/*
** Filename: flatten.c
**
** Disjunctive/Conjunctive Normal Form
*/


#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

#include "boolexpr.h"
#include "memcheck.h"
#include "share.h"
#include "util.h"


#define DUAL(kind) (BX_OP_OR + BX_OP_AND - kind)


/* Forward declarations: _distribute() recurses back into _to_dnf()/_to_cnf()
** to convert the sub-expression left over after common-literal factoring,
** and into _choose_var()/_cofactors() (defined further down, where they are
** also used by _complete_sum()) for the cofactor-based fallback below. */
static struct BoolExpr * _to_dnf(struct BoolExpr *nnf);
static struct BoolExpr * _to_cnf(struct BoolExpr *nnf);
static struct BoolExpr * _choose_var(struct BoolExpr *dnf);
static bool _cofactors(struct BoolExpr **fv0, struct BoolExpr **fv1,
                        struct BoolExpr *f, struct BoolExpr *v);


/*
** Distributing n branches of arity k is O(k^n). Beyond this many resulting
** clauses, fall back to _distribute_by_cofactor(), which is bounded by the
** number of *variables* instead -- much better when many branches share
** structure built from relatively few variables.
*/
#define DISTRIBUTE_MAX_PRODUCT ((size_t) 1 << 16)


static void
_free_arrays(size_t n, struct BX_Array **arrays)
{
    for (size_t i = 0; i < n; ++i)
        BX_Array_Del(arrays[i]);
    free(arrays);
}


/* Convert a normal-form expression to arrays of arrays form */
static struct BX_Array **
_nf2arrays(struct BoolExpr *nf)
{
    size_t length = nf->data.xs->length;
    struct BX_Array **arrays;

    arrays = malloc(length * sizeof(struct BX_Array *));

    for (size_t i = 0; i < length; ++i) {
        if (BX_IS_LIT(nf->data.xs->items[i]))
            arrays[i] = BX_Array_New(1, &nf->data.xs->items[i]);
        else
            arrays[i] = BX_Array_New(nf->data.xs->items[i]->data.xs->length,
                                     nf->data.xs->items[i]->data.xs->items);
        if (arrays[i] == NULL) {
            _free_arrays(i, arrays); // LCOV_EXCL_LINE
            return NULL;             // LCOV_EXCL_LINE
        }
    }

    return arrays;
}


/*
** Return the items common to every one of the n arrays.
**
** Commonality is exact identity (x == y): pyeda interns/shares structurally
** identical sub-expressions, so this catches both a literal shared by every
** branch and a larger shared sub-expression. An array element need not be a
** literal -- _nf2arrays() puts a branch's own children in the array, and a
** branch can be a multi-clause normal form (e.g. an AND of several OR-
** clauses) instead of a single literal or clause, whenever it doesn't
** collapse into the outer nf by same-kind flattening. So this deliberately
** does not use any per-element field like a literal's uniqid (reading that
** off a non-literal element would be type-punning garbage) or assume any
** sort order; arrays here are small (branch arity), so a plain quadratic
** scan is cheap. Caller must BX_Array_Del() the result.
*/
static struct BX_Array *
_common_lits(size_t n, struct BX_Array **arrays)
{
    struct BX_Array *common;
    struct BoolExpr **items;
    size_t count = 0;

    items = malloc(arrays[0]->length * sizeof(struct BoolExpr *));
    if (items == NULL)
        return NULL; // LCOV_EXCL_LINE

    for (size_t i = 0; i < arrays[0]->length; ++i) {
        struct BoolExpr *x = arrays[0]->items[i];
        bool in_all = true;

        for (size_t k = 1; k < n && in_all; ++k) {
            bool found = false;

            for (size_t j = 0; j < arrays[k]->length; ++j) {
                if (arrays[k]->items[j] == x) {
                    found = true;
                    break;
                }
            }
            in_all = found;
        }

        if (in_all)
            items[count++] = x;
    }

    common = _bx_array_from(count, items);
    if (common == NULL) {
        free(items); // LCOV_EXCL_LINE
        return NULL; // LCOV_EXCL_LINE
    }

    return common;
}


/*
** Return a copy of xs with every item in common removed (by identity, see
** _common_lits() above). common must be a subset of xs, which is guaranteed
** when common came from _common_lits() over an array list that includes xs.
** Caller must BX_Array_Del() the result.
*/
static struct BX_Array *
_subtract_lits(struct BX_Array *xs, struct BX_Array *common)
{
    struct BoolExpr **items;
    struct BX_Array *result;
    size_t count = 0;

    items = malloc(xs->length * sizeof(struct BoolExpr *));
    if (items == NULL)
        return NULL; // LCOV_EXCL_LINE

    for (size_t i = 0; i < xs->length; ++i) {
        struct BoolExpr *x = xs->items[i];
        bool in_common = false;

        for (size_t j = 0; j < common->length; ++j) {
            if (common->items[j] == x) {
                in_common = true;
                break;
            }
        }

        if (!in_common)
            items[count++] = x;
    }

    result = _bx_array_from(count, items);
    if (result == NULL) {
        free(items); // LCOV_EXCL_LINE
        return NULL; // LCOV_EXCL_LINE
    }

    return result;
}


/*
** Return `lit OP nf`, where OP is | if combinator == BX_OP_OR, else &,
** and nf is a constant, literal, single term/clause, or (like the output
** of _to_cnf()/_to_dnf()) an op-of-terms/clauses matching combinator (an
** AND-of-OR-clauses for combinator == BX_OP_OR, i.e. a CNF; an OR-of-AND-
** terms for combinator == BX_OP_AND, i.e. a DNF).
**
** This is linear in the size of nf: it folds lit into each existing
** term/clause instead of computing a full distribution, so it never blows
** up the way _distribute() can.
*/
static struct BoolExpr *
_lit_into(BX_Kind combinator, struct BoolExpr *lit, struct BoolExpr *nf)
{
    struct BoolExpr *absorbing = (combinator == BX_OP_OR) ? &BX_One : &BX_Zero;
    struct BoolExpr *neutral = (combinator == BX_OP_OR) ? &BX_Zero : &BX_One;
    struct BoolExpr *temp;
    struct BoolExpr *y;

    if (nf == absorbing)
        return BX_IncRef(absorbing);

    if (nf == neutral)
        return BX_IncRef(lit);

    /* nf counts as "a single clause to fold lit into directly" only when its
    ** own kind matches combinator (e.g. an OR-clause when combinator == OR).
    ** _bx_is_clause() alone isn't enough: it only checks that nf's children
    ** are literals, regardless of nf's kind, so e.g. And(~a, b) -- a 2-clause
    ** CNF whose clauses happen to be bare literals -- would wrongly satisfy
    ** it too (its kind is AND, not OR). Folding lit into that as if it were
    ** one OR-clause (Or(lit, ~a, b)) is a different, wrong function from the
    ** correct distribution (Or(lit,~a) & Or(lit,b)); the kind check below
    ** routes it to the "fold into every term" case instead. */
    if (BX_IS_LIT(nf) || (nf->kind == combinator && _bx_is_clause(nf))) {
        size_t n = BX_IS_LIT(nf) ? 1 : nf->data.xs->length;
        struct BoolExpr **xs;

        xs = malloc((n + 1) * sizeof(struct BoolExpr *));
        if (xs == NULL)
            return NULL; // LCOV_EXCL_LINE

        xs[0] = lit;
        if (BX_IS_LIT(nf))
            xs[1] = nf;
        else {
            for (size_t i = 0; i < n; ++i)
                xs[i + 1] = nf->data.xs->items[i];
        }

        temp = _bx_orandxor_new(combinator, n + 1, xs);
        free(xs);
        if (temp == NULL)
            return NULL; // LCOV_EXCL_LINE

        CHECK_NULL_1(y, _bx_simplify(temp), temp);
        BX_DecRef(temp);
        return y;
    }

    /* nf is a DUAL(combinator)-of-terms: fold lit into every term individually */
    {
        size_t n;

        /* Everything else was handled above, so nf must be an op of the dual
        ** kind here. Were it a combinator-kinded op that isn't a clause, the
        ** code below would rebuild it as its own dual -- the same class of
        ** mistake as folding an And() into an Or-clause. */
        assert(BX_IS_OP(nf) && nf->kind == DUAL(combinator));

        n = nf->data.xs->length;
        struct BoolExpr **terms;

        terms = malloc(n * sizeof(struct BoolExpr *));
        if (terms == NULL)
            return NULL; // LCOV_EXCL_LINE

        for (size_t i = 0; i < n; ++i)
            CHECK_NULL_N(terms[i], _lit_into(combinator, lit, nf->data.xs->items[i]), i, terms);

        temp = _bx_orandxor_new(DUAL(combinator), n, terms);
        _bx_free_exprs(n, terms);
        if (temp == NULL)
            return NULL; // LCOV_EXCL_LINE

        CHECK_NULL_1(y, _bx_simplify(temp), temp);
        BX_DecRef(temp);
        return y;
    }
}


/*
** Convert nf (kind == outer_kind, e.g. an OR of AND-clauses for the CNF
** case) to normal form via Shannon cofactor decomposition, instead of
** _distribute()'s full product. Distribution is exponential in the number
** of branches; this is instead bounded by the number of *variables* --
** much better when a formula has many branches built from few variables:
**
**     CNF: f == (~v | to_cnf(f|v=1)) & (v | to_cnf(f|v=0))
**     DNF: f == ( v & to_dnf(f|v=1)) | (~v & to_dnf(f|v=0))
**
** Note the DNF case is not simply the CNF case with & and | swapped: the
** literal that pairs with the v=1 cofactor is v itself there (not ~v).
*/
static struct BoolExpr *
_distribute_by_cofactor(BX_Kind kind, struct BoolExpr *nf)
{
    struct BoolExpr *v, *nv;
    struct BoolExpr *fv0, *fv1;
    struct BoolExpr *r0, *r1;
    struct BoolExpr *left, *right;
    struct BoolExpr *pair[2];
    struct BoolExpr *temp;
    struct BoolExpr *y;

    CHECK_NULL(v, _choose_var(nf));

    if (!_cofactors(&fv0, &fv1, nf, v)) {
        BX_DecRef(v); // LCOV_EXCL_LINE
        return NULL;  // LCOV_EXCL_LINE
    }

    r0 = (kind == BX_OP_OR) ? _to_cnf(fv0) : _to_dnf(fv0);
    BX_DecRef(fv0);
    if (r0 == NULL) {
        BX_DecRef(v);   // LCOV_EXCL_LINE
        BX_DecRef(fv1); // LCOV_EXCL_LINE
        return NULL;    // LCOV_EXCL_LINE
    }

    r1 = (kind == BX_OP_OR) ? _to_cnf(fv1) : _to_dnf(fv1);
    BX_DecRef(fv1);
    if (r1 == NULL) {
        BX_DecRef(v);  // LCOV_EXCL_LINE
        BX_DecRef(r0); // LCOV_EXCL_LINE
        return NULL;   // LCOV_EXCL_LINE
    }

    nv = BX_Not(v);
    if (nv == NULL) {
        BX_DecRef(v);  // LCOV_EXCL_LINE
        BX_DecRef(r0); // LCOV_EXCL_LINE
        BX_DecRef(r1); // LCOV_EXCL_LINE
        return NULL;   // LCOV_EXCL_LINE
    }

    /* _lit_into()'s combinator is always the outer kind: OR to fold a
    ** literal into a CNF's clauses, AND to fold one into a DNF's terms. */
    if (kind == BX_OP_OR) {
        left = _lit_into(kind, nv, r1);
        right = (left == NULL) ? NULL : _lit_into(kind, v, r0);
    }
    else {
        left = _lit_into(kind, v, r1);
        right = (left == NULL) ? NULL : _lit_into(kind, nv, r0);
    }

    BX_DecRef(v);
    BX_DecRef(nv);
    BX_DecRef(r0);
    BX_DecRef(r1);

    if (left == NULL || right == NULL) {
        if (left != NULL)  BX_DecRef(left);  // LCOV_EXCL_LINE
        if (right != NULL) BX_DecRef(right); // LCOV_EXCL_LINE
        return NULL;                         // LCOV_EXCL_LINE
    }

    pair[0] = left;
    pair[1] = right;
    temp = _bx_orandxor_new(DUAL(kind), 2, pair);
    BX_DecRef(left);
    BX_DecRef(right);
    if (temp == NULL)
        return NULL; // LCOV_EXCL_LINE

    CHECK_NULL_1(y, _bx_simplify(temp), temp);
    BX_DecRef(temp);

    return y;
}


/* NOTE: Return size is exponential */
static struct BoolExpr *
_distribute(BX_Kind kind, struct BoolExpr *nf)
{
    size_t length = nf->data.xs->length;
    struct BX_Array **arrays;
    struct BX_Array *product;
    struct BoolExpr *temp;
    struct BoolExpr *y;

    assert(nf->kind == kind);

    arrays = _nf2arrays(nf);
    if (arrays == NULL)
        return NULL; // LCOV_EXCL_LINE

    /*
    ** Factor out literals common to every branch before distributing:
    **
    **     (L & a) | (L & b) | (L & c) == L & (a | b | c)
    **
    ** Plain distribution is exponential in the branch count. When branches
    ** share literals (e.g. many clauses of a DNF sharing a few conditions),
    ** pulling the shared part out first can shrink the remaining product
    ** dramatically, or eliminate it entirely.
    */
    {
        struct BX_Array *common;

        CHECK_NULL(common, _common_lits(length, arrays));

        if (common->length > 0) {
            struct BoolExpr **reduced;
            struct BoolExpr *rnf;
            struct BoolExpr *rest;
            struct BoolExpr **final_xs;
            size_t fcount;

            reduced = malloc(length * sizeof(struct BoolExpr *));
            if (reduced == NULL) {
                BX_Array_Del(common);          // LCOV_EXCL_LINE
                _free_arrays(length, arrays);  // LCOV_EXCL_LINE
                return NULL;                   // LCOV_EXCL_LINE
            }

            for (size_t i = 0; i < length; ++i) {
                struct BX_Array *sub;

                sub = _subtract_lits(arrays[i], common);
                if (sub == NULL) {
                    for (size_t k = 0; k < i; ++k) // LCOV_EXCL_LINE
                        BX_DecRef(reduced[k]);     // LCOV_EXCL_LINE
                    free(reduced);                 // LCOV_EXCL_LINE
                    BX_Array_Del(common);          // LCOV_EXCL_LINE
                    _free_arrays(length, arrays);  // LCOV_EXCL_LINE
                    return NULL;                   // LCOV_EXCL_LINE
                }

                if (sub->length == 0)
                    reduced[i] = BX_IncRef(_bx_identity[DUAL(kind)]);
                else if (sub->length == 1)
                    reduced[i] = BX_IncRef(sub->items[0]);
                else
                    reduced[i] = _bx_orandxor_new(DUAL(kind), sub->length, sub->items);

                BX_Array_Del(sub);

                if (reduced[i] == NULL) {
                    for (size_t k = 0; k < i; ++k) // LCOV_EXCL_LINE
                        BX_DecRef(reduced[k]);     // LCOV_EXCL_LINE
                    free(reduced);                 // LCOV_EXCL_LINE
                    BX_Array_Del(common);          // LCOV_EXCL_LINE
                    _free_arrays(length, arrays);  // LCOV_EXCL_LINE
                    return NULL;                   // LCOV_EXCL_LINE
                }
            }

            _free_arrays(length, arrays);

            temp = _bx_orandxor_new(kind, length, reduced);
            _bx_free_exprs(length, reduced);
            if (temp == NULL) {
                BX_Array_Del(common); // LCOV_EXCL_LINE
                return NULL;          // LCOV_EXCL_LINE
            }

            CHECK_NULL_1(rnf, _bx_simplify(temp), temp);
            BX_DecRef(temp);

            if (BX_IS_ATOM(rnf) || _bx_is_clause(rnf)) {
                rest = rnf;
            }
            else {
                temp = rnf;
                rest = (kind == BX_OP_OR) ? _to_cnf(temp) : _to_dnf(temp);
                BX_DecRef(temp);
                if (rest == NULL) {
                    BX_Array_Del(common); // LCOV_EXCL_LINE
                    return NULL;          // LCOV_EXCL_LINE
                }
            }

            fcount = common->length + 1;
            final_xs = malloc(fcount * sizeof(struct BoolExpr *));
            if (final_xs == NULL) {
                BX_DecRef(rest);      // LCOV_EXCL_LINE
                BX_Array_Del(common); // LCOV_EXCL_LINE
                return NULL;          // LCOV_EXCL_LINE
            }
            for (size_t i = 0; i < common->length; ++i)
                final_xs[i] = common->items[i];
            final_xs[common->length] = rest;

            temp = _bx_orandxor_new(DUAL(kind), fcount, final_xs);
            free(final_xs);
            BX_DecRef(rest);
            BX_Array_Del(common);
            if (temp == NULL)
                return NULL; // LCOV_EXCL_LINE

            CHECK_NULL_1(y, _bx_simplify(temp), temp);
            BX_DecRef(temp);

            return y;
        }

        BX_Array_Del(common);
    }

    /*
    ** No factorable common literal: estimate the size of the full product
    ** before committing to it, and fall back to the cofactor-based
    ** decomposition above if it would be too large.
    */
    {
        size_t total = 1;
        bool too_large = false;

        for (size_t i = 0; i < length; ++i) {
            size_t alen = arrays[i]->length;

            if (alen != 0 && total > DISTRIBUTE_MAX_PRODUCT / alen) {
                too_large = true;
                break;
            }
            total *= alen;
            if (total > DISTRIBUTE_MAX_PRODUCT) {
                too_large = true;
                break;
            }
        }

        if (too_large) {
            y = _distribute_by_cofactor(kind, nf);
            _free_arrays(length, arrays);
            return y;
        }
    }

    product = BX_Product(kind, length, arrays);
    if (product == NULL) {
        _free_arrays(length, arrays); // LCOV_EXCL_LINE
        return NULL;                  // LCOV_EXCL_LINE
    }

    temp = _bx_orandxor_new(DUAL(kind), product->length, product->items);
    if (temp == NULL) {
        BX_Array_Del(product);   // LCOV_EXCL_LINE
        _free_arrays(length, arrays); // LCOV_EXCL_LINE
    }

    BX_Array_Del(product);
    _free_arrays(length, arrays);

    CHECK_NULL_1(y, _bx_simplify(temp), temp);
    BX_DecRef(temp);

    return y;
}


/*
** Return an int that shows set membership.
**
** xs <= ys: 1
** xs >= ys: 2
** xs == ys: 3
**
** NOTE: This algorithm requires the literals to be sorted.
*/

#define XS_LTE_YS (1u << 0)
#define YS_LTE_XS (1u << 1)

static unsigned int
_lits_cmp(struct BX_Array *xs, struct BX_Array *ys)
{
    size_t i = 0, j = 0;
    unsigned int ret = XS_LTE_YS | YS_LTE_XS;

    while (i < xs->length && j < ys->length) {
        struct BoolExpr *x = xs->items[i];
        struct BoolExpr *y = ys->items[j];

        assert(BX_IS_LIT(x) && BX_IS_LIT(y));

        if (x == y) {
            i += 1;
            j += 1;
        }
        else {
            long abs_x = labs(x->data.lit.uniqid);
            long abs_y = labs(y->data.lit.uniqid);

            if (abs_x < abs_y) {
                ret &= ~XS_LTE_YS;
                i += 1;
            }
            else if (abs_x > abs_y) {
                ret &= ~YS_LTE_XS;
                j += 1;
            }
            else {
                break;
            }
        }
    }

    if (i < xs->length)
        ret &= ~XS_LTE_YS;

    if (j < ys->length)
        ret &= ~YS_LTE_XS;

    return ret;
}


static struct BoolExpr *
_absorb(struct BoolExpr *nf)
{
    size_t length = nf->data.xs->length;
    bool *keep;
    struct BX_Array **arrays;
    unsigned int val;
    size_t count = 0;

    arrays = _nf2arrays(nf);
    if (arrays == NULL)
        return NULL; // LCOV_EXCL_LINE

    keep = malloc(length * sizeof(bool));
    if (keep == NULL) {
        _free_arrays(length, arrays); // LCOV_EXCL_LINE
        return NULL;                  // LCOV_EXCL_LINE
    }

    /* Keep all clauses by default */
    for (size_t i = 0; i < length; ++i)
        keep[i] = true;

    for (size_t i = 0; i < (length-1); ++i) {
        if (keep[i]) {
            for (size_t j = i+1; j < length; ++j) {
                val = _lits_cmp(arrays[i], arrays[j]);
                /* xs <= ys */
                if (val & 1) {
                    keep[j] = false;
                }
                /* xs > ys */
                else if (val & 2) {
                    keep[i] = false;
                    break;
                }
            }
        }
    }

    _free_arrays(length, arrays);

    for (size_t i = 0; i < length; ++i)
        count += (size_t) keep[i];

    if (count == length) {
        free(keep);
        return BX_IncRef(nf);
    }

    struct BoolExpr **xs;
    struct BoolExpr *temp;
    struct BoolExpr *y;

    xs = malloc(count * sizeof(struct BoolExpr *));
    if (xs == NULL) {
        free(keep);  // LCOV_EXCL_LINE
        return NULL; // LCOV_EXCL_LINE
    }

    for (size_t i = 0, index = 0; i < length; ++i) {
        if (keep[i])
            xs[index++] = nf->data.xs->items[i];
    }

    free(keep);

    temp = _bx_orandxor_new(nf->kind, count, xs);
    if (temp == NULL) {
        free(xs);    // LCOV_EXCL_LINE
        return NULL; // LCOV_EXCL_LINE
    }

    y = _bx_simplify(temp);
    BX_DecRef(temp);

    free(xs);

    return y;
}


static struct BoolExpr *
_to_dnf(struct BoolExpr *nnf)
{
    if (BX_IS_ATOM(nnf) || _bx_is_clause(nnf))
        return BX_IncRef(nnf);

    struct BoolExpr *temp;
    struct BoolExpr *ex;

    /* Convert sub-expressions to DNF */
    CHECK_NULL(temp, _bx_op_transform(nnf, _to_dnf));
    CHECK_NULL_1(ex, _bx_simplify(temp), temp);
    BX_DecRef(temp);

    /* a ; a | b ; a & b */
    if (BX_IS_ATOM(ex) || _bx_is_clause(ex))
        return ex;

    /* a | b & c */
    if (BX_IS_OR(ex)) {
        temp = ex;
        ex = _absorb(temp);
        BX_DecRef(temp);
        return ex;
    }

    /* (a | b) & (c | d) */
    temp = ex;
    CHECK_NULL_1(ex, _distribute(BX_OP_AND, temp), temp);
    BX_DecRef(temp);

    /* a ; a | b ; a & b */
    if (BX_IS_ATOM(ex) || _bx_is_clause(ex))
        return ex;

    temp = ex;
    ex = _absorb(temp);
    BX_DecRef(temp);
    return ex;
}


static struct BoolExpr *
_to_cnf(struct BoolExpr *nnf)
{
    if (BX_IS_ATOM(nnf) || _bx_is_clause(nnf))
        return BX_IncRef(nnf);

    struct BoolExpr *temp;
    struct BoolExpr *ex;

    /* Convert sub-expressions to CNF */
    CHECK_NULL(temp, _bx_op_transform(nnf, _to_cnf));
    CHECK_NULL_1(ex, _bx_simplify(temp), temp);
    BX_DecRef(temp);

    /* a ; a | b ; a & b */
    if (BX_IS_ATOM(ex) || _bx_is_clause(ex))
        return ex;

    /* a & (b | c) */
    if (BX_IS_AND(ex)) {
        temp = ex;
        ex = _absorb(temp);
        BX_DecRef(temp);
        return ex;
    }

    /* a & b | c & d */
    temp = ex;
    CHECK_NULL_1(ex, _distribute(BX_OP_OR, temp), temp);
    BX_DecRef(temp);

    /* a ; a | b ; a & b */
    if (BX_IS_ATOM(ex) || _bx_is_clause(ex))
        return ex;

    temp = ex;
    ex = _absorb(temp);
    BX_DecRef(temp);
    return ex;
}


struct BoolExpr *
BX_ToDNF(struct BoolExpr *ex)
{
    struct BoolExpr *nnf;
    struct BoolExpr *dnf;

    CHECK_NULL(nnf, _bx_to_nnf(ex));
    CHECK_NULL_1(dnf, _to_dnf(nnf), nnf);
    BX_DecRef(nnf);

    _bx_mark_flags(dnf, BX_NNF | BX_SIMPLE);

    return dnf;
}


struct BoolExpr *
BX_ToCNF(struct BoolExpr *ex)
{
    struct BoolExpr *nnf;
    struct BoolExpr *cnf;

    CHECK_NULL(nnf, _bx_to_nnf(ex));
    CHECK_NULL_1(cnf, _to_cnf(nnf), nnf);
    BX_DecRef(nnf);

    _bx_mark_flags(cnf, BX_NNF | BX_SIMPLE);

    return cnf;
}


// FIXME: Implement splitvar heuristic
static struct BoolExpr *
_choose_var(struct BoolExpr *dnf)
{
    /* dnf's first branch need not be a plain literal or clause -- it can be
    ** a multi-clause normal form itself (see _common_lits() above), so
    ** descend until an actual literal is reached. */
    struct BoolExpr *lit = dnf->data.xs->items[0];

    while (!BX_IS_LIT(lit)) {
        /* Only an operator has data.xs; a constant here would mean reading
        ** it out of the union member holding pcval. Simplified normal forms
        ** don't carry constant children, so this documents the invariant
        ** rather than handling a reachable case. */
        assert(BX_IS_OP(lit) && lit->data.xs->length > 0);
        lit = lit->data.xs->items[0];
    }

    if (BX_IS_COMP(lit))
        return BX_Not(lit);
    else
        return BX_IncRef(lit);
}


static bool
_cofactors(struct BoolExpr **fv0, struct BoolExpr **fv1, struct BoolExpr *f, struct BoolExpr *v)
{
    struct BX_Dict *v0, *v1;

    v0 = BX_Dict_New();
    if (v0 == NULL)
        return false; // LCOV_EXCL_LINE

    if (!BX_Dict_Insert(v0, v, &BX_Zero)) {
        BX_Dict_Del(v0); // LCOV_EXCL_LINE
        return false;         // LCOV_EXCL_LINE
    }

    *fv0 = BX_Restrict(f, v0);
    if (fv0 == NULL) {
        BX_Dict_Del(v0); // LCOV_EXCL_LINE
        return false;         // LCOV_EXCL_LINE
    }

    BX_Dict_Del(v0);

    v1 = BX_Dict_New();
    if (v1 == NULL)
        return false; // LCOV_EXCL_LINE

    if (!BX_Dict_Insert(v1, v, &BX_One)) {
        BX_Dict_Del(v1); // LCOV_EXCL_LINE
        return false;    // LCOV_EXCL_LINE
    }

    *fv1 = BX_Restrict(f, v1);
    if (fv1 == NULL) {
        BX_Dict_Del(v1); // LCOV_EXCL_LINE
        return false;    // LCOV_EXCL_LINE
    }

    BX_Dict_Del(v1);

    return true;
}


/* CS(f) = [x0 | CS(0, x1, ..., xn)] & [~x0 | CS(1, x1, ..., xn)] */
static struct BoolExpr *
_complete_sum(struct BoolExpr *dnf)
{
    if (BX_Depth(dnf) <= 1) {
        return BX_IncRef(dnf);
    }
    else {
        struct BoolExpr *v, *vn;
        struct BoolExpr *fv0, *fv1;
        struct BoolExpr *cs0, *cs1;
        struct BoolExpr *left, *right;
        struct BoolExpr *temp;
        struct BoolExpr *y;

        CHECK_NULL(v, _choose_var(dnf));

        if (!_cofactors(&fv0, &fv1, dnf, v)) {
            BX_DecRef(v); // LCOV_EXCL_LINE
            return NULL;  // LCOV_EXCL_LINE
        }

        CHECK_NULL_3(cs0, _complete_sum(fv0), v, fv0, fv1);
        BX_DecRef(fv0);

        CHECK_NULL_3(left, BX_OrN(2, v, cs0), v, fv1, cs0);
        BX_DecRef(v);
        BX_DecRef(cs0);

        CHECK_NULL_2(cs1, _complete_sum(fv1), fv1, left);
        BX_DecRef(fv1);

        CHECK_NULL_2(vn, BX_Not(v), left, cs1);
        CHECK_NULL_3(right, BX_OrN(2, vn, cs1), left, cs1, vn);
        BX_DecRef(cs1);
        BX_DecRef(vn);

        CHECK_NULL_2(temp, BX_AndN(2, left, right), left, right);
        BX_DecRef(left);
        BX_DecRef(right);

        CHECK_NULL_1(y, BX_ToDNF(temp), temp);
        BX_DecRef(temp);

        return y;
    }
}


struct BoolExpr *
BX_CompleteSum(struct BoolExpr *ex)
{
    struct BoolExpr *dnf;
    struct BoolExpr *sum;

    if (BX_IsDNF(ex))
        dnf = BX_IncRef(ex);
    else
        CHECK_NULL(dnf, BX_ToDNF(ex));

    CHECK_NULL_1(sum, _complete_sum(dnf), dnf);
    BX_DecRef(dnf);

    return sum;
}


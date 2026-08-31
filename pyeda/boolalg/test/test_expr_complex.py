"""
Tests for expression processing: simplify, CNF/DNF conversion,
equivalence, Tseitin encoding, and SAT solving on long/complex expressions.
"""


import random

from pyeda.boolalg.bfarray import exprvars
from pyeda.boolalg.expr import (
    ITE,
    AchillesHeel,
    And,
    Equal,
    Implies,
    Majority,
    Mux,
    NHot,
    Not,
    One,
    OneHot,
    OneHot0,
    Or,
    Xor,
    Zero,
    expr2dimacscnf,
    exprvar,
)
from pyeda.boolalg.minimization import espresso_exprs


# ---------------------------------------------------------------------------
# Variables
# ---------------------------------------------------------------------------
a, b, c, d, e = map(exprvar, "abcde")
p, q, r = exprvar("p"), exprvar("q"), exprvar("r")
V = exprvars("v", 20)


# ===========================================================================
# Simplification tests
# ===========================================================================

class TestSimplify:
    """Tests for Expression.simplify on various expression shapes."""

    def test_identity_laws(self):
        assert (a & One).simplify().equivalent(a)
        assert (a | Zero).simplify().equivalent(a)

    def test_domination_laws(self):
        assert (a | One).simplify() is One
        assert (a & Zero).simplify() is Zero

    def test_idempotent(self):
        assert (a | a).simplify().equivalent(a)
        assert (a & a).simplify().equivalent(a)

    def test_complement(self):
        assert (a | ~a).simplify() is One
        assert (a & ~a).simplify() is Zero

    def test_double_negation(self):
        assert Not(Not(a)).simplify().equivalent(a)
        assert Not(Not(Not(a))).simplify().equivalent(~a)

    def test_absorption(self):
        assert (a | (a & b)).simplify().equivalent(a)
        assert (a & (a | b)).simplify().equivalent(a)

    def test_nested_simplify(self):
        # (a & b) | (a & b & c) simplifies to a & b
        f = (a & b) | (a & b & c)
        assert f.simplify().equivalent(a & b)

    def test_deep_nesting(self):
        # Build a deeply nested expression and simplify
        ex = a
        for v in [b, c, d, e, p, q, r]:
            ex = ex & (v | ~v)
        # Each (v | ~v) == 1, so result should simplify to just a
        assert ex.simplify().equivalent(a)

    def test_simplify_xor_self(self):
        assert Xor(a, a).simplify() is Zero

    def test_simplify_large_or_with_complement_pairs(self):
        # v0 | ~v0 | v1 | ~v1 | ... -> One
        terms = []
        for i in range(10):
            terms.extend([V[i], ~V[i]])
        assert Or(*terms).simplify() is One

    def test_simplify_large_and_with_complement(self):
        # v0 & ~v0 & v1 & ... -> Zero
        assert And(V[0], ~V[0], *V[1:10]).simplify() is Zero

    def test_simplify_preserves_equivalence(self):
        """Simplification must always preserve logical equivalence."""
        f = (a | b) & (a | c) & (~a | d)
        assert f.simplify().equivalent(f)


# ===========================================================================
# CNF conversion tests
# ===========================================================================

class TestToCNF:
    """Tests for Expression.to_cnf on various expression shapes."""

    def test_literal_cnf(self):
        assert a.to_cnf() is a
        assert (~a).to_cnf().equivalent(~a)

    def test_simple_or_is_cnf(self):
        f = a | b | c
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)

    def test_simple_and_is_cnf(self):
        f = a & b & c
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)

    def test_xor_to_cnf(self):
        f = Xor(a, b)
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)

    def test_xor3_to_cnf(self):
        f = Xor(a, b, c)
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)

    def test_implies_to_cnf(self):
        f = Implies(a, b)
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)

    def test_ite_to_cnf(self):
        f = ITE(a, b, c)
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)

    def test_nested_or_and_to_cnf(self):
        # (a & b) | (c & d) => distribute to CNF
        f = (a & b) | (c & d)
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)

    def test_deeply_nested_to_cnf(self):
        # Deep nesting: ((a | b) & c) | ((d & e) | p)
        ex = ((a | b) & c) | ((d & e) | p)
        cnf = ex.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(ex)

    def test_8var_mixed_to_cnf(self):
        ex = (a & b & ~c) | (d & ~e & p) | (q & r)
        cnf = ex.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(ex)

    def test_majority5_to_cnf(self):
        f = Majority(a, b, c, d, e)
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)

    def test_onehot4_to_cnf(self):
        f = OneHot(a, b, c, d)
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)

    def test_achillesheel_to_cnf(self):
        f = AchillesHeel(a, b, c, d)
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)

    def test_cnf_of_cnf_is_identity(self):
        """Converting a CNF expression to CNF should return itself."""
        f = And(Or(a, b), Or(c, d), Or(~a, e))
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)

    def test_wide_disjunction_of_conjunctions(self):
        # (v0 & v1) | (v2 & v3) | ... | (v18 & v19) - 10 terms
        terms = [V[i] & V[i+1] for i in range(0, 20, 2)]
        f = Or(*terms)
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)

    def test_large_cnf(self):
        E0 = exprvar('E0')
        E1 = exprvar('E1')
        B0 = exprvar('B0')
        B1 = exprvar('B1')
        B3 = exprvar('B3')
        S0 = exprvar('S0')
        S1 = exprvar('S1')
        S2 = exprvar('S2')
        S3 = exprvar('S3')
        S4 = exprvar('S4')

        ex = Or(And(~E0, ~E1, S1, ~B1, B3), And(~E0, ~E1, ~B0, ~B1, B3), 
            And(~E0, ~E1, ~S0, S3, S4), And(~E0, ~E1, ~B0, ~S2, S4), 
            And(~E0, ~E1, ~B0, S3, S4), And(~E0, ~E1, ~S0, S3, B3), 
            And(~E0, ~E1, S1, ~B1, S4), And(~E0, ~E1, ~B0, ~B1, S4), 
            And(~E0, ~E1, ~B0, S3, B3), And(~E0, ~E1, ~S0, ~S2, B3), 
            And(~E0, ~E1, ~S0, ~B1, B3), And(~E0, ~E1, ~S0, ~B1, S4), 
            And(~E0, ~E1, S1, S3, B3), And(~E0, ~E1, ~S0, ~S2, S4), 
            And(~E0, ~E1, S1, S3, S4), And(~E0, ~E1, S1, ~S2, B3), 
            And(~E0, ~E1, S1, ~S2, S4), And(~E0, ~E1, ~B0, ~S2, B3))
        cnf = ex.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(ex)

    def test_cofactor_fallback_and_of_literals_branch(self):
        # Regression test for a bug in the cofactor-based distribution
        # fallback (only reached once a branch count/arity crosses
        # DISTRIBUTE_MAX_PRODUCT, hence the size of this expression): a
        # cofactor could collapse to something like And(~a, b), a 2-clause
        # CNF whose clauses happen to be bare literals. _lit_into() mistook
        # that for a single OR-clause (matching by "all children are
        # literals" alone, ignoring the node's own AND kind) and folded a
        # literal into it directly instead of distributing across its two
        # clauses, silently dropping a needed clause from the result.
        ex = Or(
            And(V[3], ~V[6], ~V[8], Or(And(~V[3], ~V[4], V[6], Or(And(~V[1], V[7]), And(~V[2], ~V[3], ~V[5]), And(V[3], ~V[5], ~V[9]))), And(~V[0], ~V[2], V[4], ~V[8], Or(V[2], V[6], And(V[5], V[7], V[8]))), And(~V[0], V[2], V[4], Or(~V[4], And(~V[1], V[3]), And(~V[0], ~V[5]))), And(V[0], V[1], V[3], V[9], Or(And(~V[4], V[6], V[8]), And(~V[4], ~V[8], V[9]))), And(V[0], ~V[4], V[5], ~V[8]))),
            And(V[0], ~V[1], V[9], Or(And(V[3], V[4], ~V[5], V[6], Or(V[3], And(V[6], V[7], ~V[9]), And(~V[5], ~V[6], ~V[9]))), And(V[3], ~V[9], Or(And(V[3], ~V[6], ~V[8]), And(~V[3], V[4], ~V[5]))), And(~V[2], ~V[3], ~V[4], Or(And(~V[1], ~V[4]), And(V[0], ~V[1], V[3]), And(V[3], ~V[8]))), And(V[2], ~V[8], Or(V[1], V[2])), And(~V[2], ~V[3], V[6], V[8]), And(V[6], ~V[7], ~V[8], Or(And(V[0], ~V[3], ~V[8]), And(~V[1], V[3], V[4]))), And(~V[4], V[6], Or(~V[5], And(V[2], ~V[4], ~V[9]))))),
            And(~V[0], V[7], ~V[8], Or(And(V[1], ~V[2], ~V[3], V[4], ~V[6], ~V[8], V[9]), And(~V[1], V[2], ~V[3], V[4], ~V[8], ~V[9]))),
            And(V[4], ~V[7], ~V[8], Or(And(V[0], V[1], ~V[4], V[5], V[7]), And(V[2], V[3], V[5], V[6], V[8]), And(V[2], V[5], ~V[6], Or(V[3], And(V[1], V[4]), And(~V[2], ~V[4], ~V[9]))), And(V[0], V[1], ~V[5], V[6], ~V[7], ~V[8]))),
            And(V[6], V[7], Or(And(~V[4], ~V[6], ~V[7], Or(~V[8], And(~V[0], ~V[4], V[5]), And(V[8], ~V[9]))), And(V[1], ~V[2], ~V[4], V[6], Or(And(~V[4], ~V[6], V[7]), And(~V[0], ~V[8]), And(~V[4], V[6], ~V[7]))), And(V[2], ~V[4], ~V[9], Or(V[3], And(V[2], ~V[5], ~V[8]))), And(~V[3], V[4], Or(And(~V[0], ~V[2], ~V[4]), And(~V[5], V[6], ~V[7]))), And(V[0], ~V[9], Or(And(V[5], ~V[8], V[9]), And(V[1], ~V[4], V[7]))), And(~V[1], V[3], ~V[4], Or(V[2], And(~V[3], V[6], V[7]), And(~V[1], V[2], V[9]))), And(~V[2], V[3], ~V[4], ~V[6]))),
            And(~V[2], ~V[5], ~V[7], Or(And(V[0], ~V[2], V[6], V[7], Or(V[0], And(~V[0], V[6], ~V[7]))), And(V[2], V[7], Or(V[1], And(~V[1], V[7], V[9]), And(V[2], ~V[3], V[6]))), And(V[0], ~V[3], Or(V[0], And(V[0], V[3], V[4]))), And(~V[4], V[7], ~V[8], ~V[9], Or(V[1], V[2], And(V[8], V[9]))), And(V[0], V[2], V[5], V[8], Or(And(~V[0], ~V[3], V[5]), And(V[0], ~V[5], ~V[7]))))),
            And(~V[2], V[6], Or(And(V[0], V[1], V[2], V[4], V[9]), And(~V[4], V[6], Or(~V[3], And(V[1], V[8], ~V[9]), And(~V[0], V[3], ~V[6]))), And(V[5], V[6], ~V[8], Or(V[7], And(~V[1], V[2], ~V[3]))), And(~V[0], ~V[2], V[3], ~V[5]), And(V[0], V[2], ~V[7], ~V[8], Or(V[0], V[4], And(V[1], ~V[7], V[8]))))),
        )
        cnf = ex.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(ex)

# ===========================================================================
# DNF conversion tests
# ===========================================================================

class TestToDNF:
    """Tests for Expression.to_dnf on various expression shapes."""

    def test_literal_dnf(self):
        assert a.to_dnf() is a

    def test_simple_and_is_dnf(self):
        f = a & b & c
        dnf = f.to_dnf()
        assert dnf.is_dnf()
        assert dnf.equivalent(f)

    def test_simple_or_is_dnf(self):
        f = a | b | c
        dnf = f.to_dnf()
        assert dnf.is_dnf()
        assert dnf.equivalent(f)

    def test_xor_to_dnf(self):
        f = Xor(a, b)
        dnf = f.to_dnf()
        assert dnf.is_dnf()
        assert dnf.equivalent(f)

    def test_xor3_to_dnf(self):
        f = Xor(a, b, c)
        dnf = f.to_dnf()
        assert dnf.is_dnf()
        assert dnf.equivalent(f)

    def test_implies_to_dnf(self):
        f = Implies(a, b)
        dnf = f.to_dnf()
        assert dnf.is_dnf()
        assert dnf.equivalent(f)

    def test_ite_to_dnf(self):
        f = ITE(a, b, c)
        dnf = f.to_dnf()
        assert dnf.is_dnf()
        assert dnf.equivalent(f)

    def test_conjunctive_to_dnf(self):
        # (a | b) & (c | d) => distribute to DNF
        f = (a | b) & (c | d)
        dnf = f.to_dnf()
        assert dnf.is_dnf()
        assert dnf.equivalent(f)

    def test_8var_mixed_to_dnf(self):
        ex = (a | b | ~c) & (d | ~e | p) & (q | r)
        dnf = ex.to_dnf()
        assert dnf.is_dnf()
        assert dnf.equivalent(ex)

    def test_majority5_to_dnf(self):
        f = Majority(a, b, c, d, e)
        dnf = f.to_dnf()
        assert dnf.is_dnf()
        assert dnf.equivalent(f)

    def test_onehot4_to_dnf(self):
        f = OneHot(a, b, c, d)
        dnf = f.to_dnf()
        assert dnf.is_dnf()
        assert dnf.equivalent(f)

    def test_dnf_of_dnf_is_identity(self):
        """Converting a DNF expression to DNF should return itself."""
        f = Or(And(a, b), And(c, d), And(~a, e))
        dnf = f.to_dnf()
        assert dnf.is_dnf()
        assert dnf.equivalent(f)

    def test_large_dnf(self):
        """AND-of-ORs mirror of TestToCNF.test_crash, targeting to_dnf's
        cofactor-based fallback (the dual of to_cnf's) rather than to_cnf's.
        """
        E0 = exprvar('E0')
        E1 = exprvar('E1')
        B0 = exprvar('B0')
        B1 = exprvar('B1')
        B3 = exprvar('B3')
        S0 = exprvar('S0')
        S1 = exprvar('S1')
        S2 = exprvar('S2')
        S3 = exprvar('S3')
        S4 = exprvar('S4')

        ex = Or(And(~E0, ~E1, S1, ~B1, B3), And(~E0, ~E1, ~B0, ~B1, B3),
            And(~E0, ~E1, ~S0, S3, S4), And(~E0, ~E1, ~B0, ~S2, S4),
            And(~E0, ~E1, ~B0, S3, S4), And(~E0, ~E1, ~S0, S3, B3),
            And(~E0, ~E1, S1, ~B1, S4), And(~E0, ~E1, ~B0, ~B1, S4),
            And(~E0, ~E1, ~B0, S3, B3), And(~E0, ~E1, ~S0, ~S2, B3),
            And(~E0, ~E1, ~S0, ~B1, B3), And(~E0, ~E1, ~S0, ~B1, S4),
            And(~E0, ~E1, S1, S3, B3), And(~E0, ~E1, ~S0, ~S2, S4),
            And(~E0, ~E1, S1, S3, S4), And(~E0, ~E1, S1, ~S2, B3),
            And(~E0, ~E1, S1, ~S2, S4), And(~E0, ~E1, ~B0, ~S2, B3))
        dual = ~ex  # De Morgan: AND of 18 5-literal OR-clauses, in NNF

        dnf = dual.to_dnf()
        assert dnf.is_dnf()
        assert dnf.equivalent(dual)


# ===========================================================================
# NNF conversion tests
# ===========================================================================

class TestToNNF:
    """Tests for to_nnf (negation normal form)."""

    def test_double_not(self):
        assert Not(Not(a)).to_nnf().equivalent(a)

    def test_demorgan_or(self):
        f = Not(a | b | c)
        nnf = f.to_nnf()
        assert nnf.equivalent(~a & ~b & ~c)

    def test_demorgan_and(self):
        f = Not(a & b & c)
        nnf = f.to_nnf()
        assert nnf.equivalent(~a | ~b | ~c)

    def test_nested_demorgan(self):
        # ~(a & (b | c))  =>  ~a | (~b & ~c)
        f = Not(a & (b | c))
        nnf = f.to_nnf()
        assert nnf.equivalent(~a | (~b & ~c))

    def test_deep_not_chain(self):
        f = Not(Not(Not(Not(a & b))))
        nnf = f.to_nnf()
        assert nnf.equivalent(a & b)

    def test_complex_nnf(self):
        f = Not((a | b) & (c | Not(d & e)))
        nnf = f.to_nnf()
        assert nnf.equivalent(f)


# ===========================================================================
# Tseitin encoding tests
# ===========================================================================

class TestTseitin:
    """Tests for Tseitin CNF encoding of complex expressions."""

    def test_simple_expression(self):
        f = a ^ b
        t = f.tseitin()
        assert t.is_cnf()
        # Tseitin encoding is equisatisfiable: every satisfying point
        # of the original should extend to satisfy the encoded form
        for point in f.satisfy_all():
            restricted = t.restrict(point)
            assert restricted.satisfy_one() is not None

    def test_deeply_nested(self):
        ex = (a ^ b) & (c | (d & (e ^ p)))
        t = ex.tseitin()
        assert t.is_cnf()
        # Check that original solutions exist in the Tseitin form
        orig_count = sum(1 for _ in ex.satisfy_all())
        assert orig_count > 0
        tseitin_count = sum(1 for _ in t.satisfy_all())
        assert tseitin_count >= orig_count

    def test_large_xor_chain(self):
        # XOR of 6 variables
        ex = Xor(a, b, c, d, e, p)
        t = ex.tseitin()
        assert t.is_cnf()

    def test_onehot_tseitin(self):
        f = OneHot(a, b, c, d)
        t = f.tseitin()
        assert t.is_cnf()


# ===========================================================================
# SAT solving on complex expressions
# ===========================================================================

class TestSatisfyComplex:
    """SAT solving on larger and more complex expressions."""

    def test_satisfiable_conjunction(self):
        f = And(*V[:10])
        soln = f.satisfy_one()
        assert soln is not None
        assert all(soln[v] == 1 for v in V[:10])

    def test_unsatisfiable_contradiction(self):
        f = And(V[0], ~V[0])
        assert f.satisfy_one() is None

    def test_large_cnf_satisfy(self):
        # Build a satisfiable CNF with many clauses
        f = And(
            Or(V[0], V[1], V[2]),
            Or(~V[0], V[3], V[4]),
            Or(~V[1], ~V[3], V[5]),
            Or(V[2], ~V[4], ~V[5]),
            Or(V[6], V[7], ~V[2]),
            Or(~V[6], V[8], V[9]),
            Or(~V[7], ~V[8], V[0]),
            Or(V[1], ~V[9], V[6]),
        )
        soln = f.satisfy_one()
        assert soln is not None
        # Verify the solution
        assert f.restrict(soln) is One

    def test_satisfy_all_count_xor3(self):
        f = Xor(V[0], V[1], V[2])
        solns = list(f.satisfy_all())
        assert len(solns) == 4

    def test_satisfy_all_onehot(self):
        f = OneHot(a, b, c, d, e)
        solns = list(f.satisfy_all())
        # OneHot(5 vars) has exactly 5 solutions
        assert len(solns) == 5
        for soln in solns:
            assert sum(soln.values()) == 1

    def test_satisfy_onehot0(self):
        f = OneHot0(a, b, c, d, e)
        solns = list(f.satisfy_all())
        # OneHot0 allows zero or one: 1 + 5 = 6 solutions
        assert len(solns) == 6

    def test_satisfy_majority_odd(self):
        # Majority(a,b,c) is true when >= 2 of 3 are true
        maj = Majority(a, b, c)
        solns = list(maj.satisfy_all())
        assert len(solns) >= 3
        for soln in solns:
            assert maj.restrict(soln) is One

    def test_satisfy_count(self):
        f = (a | b) & (c | d)
        # 4 * 4 = 16 total points, only (0,0,0,0) fails both => 9 satisfy
        assert f.satisfy_count() == 9

    def test_satisfy_implies_chain(self):
        # a => b => c => d, with a=1 forces all to 1
        f = Implies(a, b) & Implies(b, c) & Implies(c, d) & a
        soln = f.satisfy_one()
        assert soln is not None
        assert soln == {a: 1, b: 1, c: 1, d: 1}

    def test_satisfy_after_cnf_conversion(self):
        """CNF conversion must preserve equivalence."""
        ex = Xor(a, b) & (c | d)
        cnf = ex.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(ex)
        # Every solution of the original must satisfy the CNF and vice versa
        for soln in ex.satisfy_all():
            assert cnf.restrict(soln).satisfy_one() is not None


# ===========================================================================
# Round-trip CNF <-> DNF
# ===========================================================================

class TestNormalFormRoundTrip:
    """Verify that CNF and DNF conversions preserve equivalence."""

    def test_cnf_then_dnf(self):
        f = (a ^ b) | (c & d)
        cnf = f.to_cnf()
        back = cnf.to_dnf()
        assert back.is_dnf()
        assert back.equivalent(f)

    def test_dnf_then_cnf(self):
        f = (a | b) & (c | d) & (e | ~a)
        dnf = f.to_dnf()
        back = dnf.to_cnf()
        assert back.is_cnf()
        assert back.equivalent(f)

    def test_xor4_roundtrip(self):
        f = Xor(a, b, c, d)
        cnf = f.to_cnf()
        dnf = f.to_dnf()
        assert cnf.equivalent(dnf)
        assert cnf.equivalent(f)

    def test_equal3_roundtrip(self):
        f = Equal(a, b, c)
        cnf = f.to_cnf()
        dnf = f.to_dnf()
        assert cnf.equivalent(dnf)
        assert cnf.equivalent(f)

    def test_ite_roundtrip(self):
        f = ITE(a, b & c, d | e)
        cnf = f.to_cnf()
        dnf = f.to_dnf()
        assert cnf.equivalent(dnf)
        assert cnf.equivalent(f)


class TestNormalFormFuzz:
    """Property-based check of to_cnf/to_dnf over randomly nested
    expressions, with a fixed seed for determinism.

    The recursive distribution logic has enough special cases (common-factor
    extraction, the cofactor fallback) that any one fixed expression
    exercises only a slice of it, so this walks a spread of shapes instead.

    This is a general net, not a reproduction of any particular past bug:
    the expressions it builds stay well under DISTRIBUTE_MAX_PRODUCT, so it
    does not reach the cofactor fallback that
    test_cofactor_fallback_and_of_literals_branch covers. Keep that test.
    """

    NVARS = 6
    VARS = exprvars("fz", NVARS)

    @classmethod
    def _rand_clause(cls, rng, k):
        idx = rng.sample(range(cls.NVARS), k)
        return [cls.VARS[i] if rng.random() < 0.5 else ~cls.VARS[i] for i in idx]

    @classmethod
    def _rand_nested(cls, rng, depth):
        if depth == 0:
            k = rng.randint(1, 3)
            return Or(*[And(*cls._rand_clause(rng, rng.randint(1, 3)))
                        for _ in range(k)])
        branches = []
        for _ in range(rng.randint(2, 4)):
            lits = cls._rand_clause(rng, rng.randint(1, 3))
            sub = cls._rand_nested(rng, depth - 1)
            branches.append(And(*lits, sub))
        return Or(*branches)

    def test_to_cnf_to_dnf_random_nested(self):
        rng = random.Random(0)
        for _ in range(300):
            f = self._rand_nested(rng, depth=2)

            cnf = f.to_cnf()
            assert cnf.is_cnf() or cnf.is_zero() or cnf.is_one()
            assert cnf.equivalent(f)

            dnf = f.to_dnf()
            assert dnf.is_dnf() or dnf.is_zero() or dnf.is_one()
            assert dnf.equivalent(f)


# ===========================================================================
# Complex expression construction and processing
# ===========================================================================

class TestComplexExpressions:
    """Stress tests with long and complex expressions."""

    def test_long_and_chain(self):
        """AND of 20 variables: simplify, CNF, DNF."""
        f = And(*V)
        assert f.simplify().equivalent(f)
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)
        dnf = f.to_dnf()
        assert dnf.is_dnf()
        assert dnf.equivalent(f)

    def test_long_or_chain(self):
        """OR of 20 variables: simplify, CNF, DNF."""
        f = Or(*V)
        assert f.simplify().equivalent(f)
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)
        dnf = f.to_dnf()
        assert dnf.is_dnf()
        assert dnf.equivalent(f)

    def test_nested_binary_tree(self):
        """Binary tree of ANDs and ORs, 8 leaves."""
        ex = (
            ((a & b) | (c & d))
            &
            ((e | p) & (q | r))
        )
        cnf = ex.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(ex)
        dnf = ex.to_dnf()
        assert dnf.is_dnf()
        assert dnf.equivalent(ex)

    def test_achillesheel_6(self):
        """AchillesHeel with 6 variables."""
        ex = AchillesHeel(a, b, c, d, e, p)
        cnf = ex.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(ex)

    def test_mux_chain(self):
        """Chain of muxes."""
        m1 = Mux([a, b], c)   # Mux(inputs, sel)
        m2 = Mux([d, e], p)
        combined = m1 ^ m2
        cnf = combined.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(combined)
        soln = cnf.satisfy_one()
        assert soln is not None

    def test_nhot_expression(self):
        """NHot(2, ...) exactly 2 of 5 variables true."""
        f = NHot(2, a, b, c, d, e)
        solns = list(f.satisfy_all())
        # C(5,2) = 10 solutions
        assert len(solns) == 10
        for soln in solns:
            assert sum(soln.values()) == 2

    def test_mixed_operators_deep(self):
        """Mix of all operator types in a deep expression."""
        ex = And(
            Or(a, Xor(b, c)),
            Implies(d, e),
            ITE(p, q, r),
            Equal(a, b),
        )
        s = ex.simplify()
        assert s.equivalent(ex)
        cnf = ex.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(ex)

    def test_18var_nested_expression(self):
        """The 18-variable nested expression from the user's example."""
        B = exprvars("b", 18)
        f = B[0] & (
            (B[1] | (B[2] | B[3]))
            & ((B[4] | (B[5] | B[6]))
               & ((B[7] | (B[8] | B[9]))
                  & ((B[10] | (B[11] | B[12]))
                     & ((B[13] | B[14]) & (B[15] | (B[16] | B[17]))))))
        )
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)

        soln = cnf.satisfy_one()
        assert soln is not None
        assert f.restrict(soln) is One

    def test_expand_and_simplify_back(self):
        """Shannon expansion then simplification should be equivalent."""
        f = (a & b) | (c & d)
        expanded = f.expand([a, b])
        simplified = expanded.simplify()
        assert simplified.equivalent(f)

    def test_demorgan_many_levels(self):
        """Deeply nested NOTs pushed through AND/OR."""
        inner = And(a, Or(b, And(c, Or(d, e))))
        f = Not(Not(Not(inner)))
        nnf = f.to_nnf()
        assert nnf.equivalent(f)
        cnf = f.to_cnf()
        assert cnf.is_cnf()
        assert cnf.equivalent(f)


# ===========================================================================
# Espresso minimization tests
# ===========================================================================

class TestEspressoComplex:
    """Test Espresso minimization on larger expressions."""

    def test_minimize_redundant_dnf(self):
        """Redundant minterms should be removed by Espresso."""
        ex = (a & b) | (a & b & c) | (a & ~b & c) | (~a & b & c)
        ex_dnf = ex.to_dnf()
        [fm] = espresso_exprs(ex_dnf)
        assert fm.equivalent(ex)
        assert fm.size <= ex.size

    def test_minimize_8var(self):
        """Minimize an 8-variable expression with many redundant terms."""
        f = Or(
            And(a, b, c),
            And(a, b, ~c),
            And(a, ~b, c, d),
            And(~a, b, c, d),
            And(a, b, d),
        )
        [fm] = espresso_exprs(f)
        assert fm.equivalent(f)
        assert fm.size <= f.size

    def test_minimize_majority3(self):
        f = Majority(a, b, c)
        dnf = f.to_dnf()
        [fm] = espresso_exprs(dnf)
        assert fm.equivalent(f)

    def test_minimize_multiple_outputs(self):
        """Espresso with two outputs sharing inputs."""
        f1 = Or(And(a, b), And(c, d))
        f2 = Or(And(a, c), And(b, d))
        f1m, f2m = espresso_exprs(f1, f2)
        assert f1m.equivalent(f1)
        assert f2m.equivalent(f2)


# ===========================================================================
# DIMACS CNF encoding tests
# ===========================================================================

class TestDimacsCNF:
    """Tests for expr2dimacscnf on complex expressions."""

    def test_simple_cnf_encoding(self):
        f = And(Or(a, b), Or(~a, c))
        litmap, cnf = expr2dimacscnf(f)
        soln = cnf.satisfy_one()
        assert soln is not None

    def test_8var_cnf_encoding(self):
        ex = And(
            Or(a, b, c),
            Or(~a, d, e),
            Or(~b, ~d, p),
            Or(c, ~e, ~p),
            Or(q, r, ~c),
        )
        litmap, cnf = expr2dimacscnf(ex)
        soln = cnf.satisfy_one()
        assert soln is not None
        point = cnf.soln2point(soln, litmap)
        assert ex.restrict(point) is One

    def test_dimacs_unsat(self):
        f = And(Or(a, b), Or(~a, b), Or(a, ~b), Or(~a, ~b))
        litmap, cnf = expr2dimacscnf(f)
        soln = cnf.satisfy_one()
        assert soln is None

    def test_dimacs_satisfy_all(self):
        f = And(Or(a, b), Or(a, c))
        litmap, cnf = expr2dimacscnf(f)
        solns = list(cnf.satisfy_all())
        points = [cnf.soln2point(s, litmap) for s in solns]
        for point in points:
            assert f.restrict(point) is One


# ===========================================================================
# Edge cases and constants
# ===========================================================================

class TestEdgeCases:
    """Edge cases for expression processing."""

    def test_constant_simplify(self):
        assert Zero.simplify() is Zero
        assert One.simplify() is One

    def test_constant_cnf_dnf(self):
        assert Zero.to_cnf() is Zero
        assert Zero.to_dnf() is Zero
        assert One.to_cnf() is One
        assert One.to_dnf() is One

    def test_single_variable_cnf_dnf(self):
        assert a.to_cnf() is a
        assert a.to_dnf() is a
        assert (~a).to_cnf().equivalent(~a)
        assert (~a).to_dnf().equivalent(~a)

    def test_restrict_to_constant(self):
        f = a & b & c
        assert f.restrict({a: 1, b: 1, c: 1}) is One
        assert f.restrict({a: 0}) is Zero

    def test_equivalent_is_reflexive(self):
        f = Xor(a, b, c)
        assert f.equivalent(f)

    def test_equivalent_symmetry(self):
        f1 = (a | b) & c
        f2 = (c & a) | (c & b)
        assert f1.equivalent(f2)
        assert f2.equivalent(f1)

    def test_not_equivalent(self):
        assert not a.equivalent(b)
        assert not (a & b).equivalent(a | b)


# ===========================================================================
# Complete sum (all prime implicants)
# ===========================================================================

class TestCompleteSum:
    """Tests for complete_sum on larger expressions."""

    def test_complete_sum_simple(self):
        f = (a & b) | (a & c) | (b & c)
        cs = f.complete_sum()
        assert cs.is_dnf()
        assert cs.equivalent(f)

    def test_complete_sum_preserves_equivalence(self):
        f = (a & ~b & c) | (~a & b & ~c) | (a & b)
        cs = f.complete_sum()
        assert cs.equivalent(f)

    def test_complete_sum_with_negations(self):
        f = (~a & b) | (a & ~b) | (b & c)
        cs = f.complete_sum()
        assert cs.is_dnf()
        assert cs.equivalent(f)

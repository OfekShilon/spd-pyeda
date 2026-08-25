"""
Test pyeda.boolalg.reset_state and friends

Every other test module in this suite creates module-level Variable
instances at collection time, all sharing the single process-wide
uniqid counter. Calling reset_state() in this process would recycle
those uniqids out from under the rest of the suite, so each scenario
below runs in a freshly spawned child process instead, where it gets
pristine pyeda.boolalg state and cannot affect anything else.
"""


import multiprocessing as mp
import traceback

import pytest


def _worker(body, q):
    try:
        body()
    except BaseException:  # pylint: disable=broad-except
        q.put(traceback.format_exc())
    else:
        q.put(None)


def _isolated(body):
    """Run *body* to completion in a fresh child process."""
    ctx = mp.get_context("spawn")
    q = ctx.Queue()
    p = ctx.Process(target=_worker, args=(body, q))
    p.start()
    tb = q.get()
    p.join()
    if tb is not None:
        pytest.fail(tb)


def _body_clears_all_registries():
    import pyeda.boolalg as ba
    from pyeda.boolalg import bdd, boolfunc, expr, table
    from pyeda.inter import bddvar, exprvar, ttvar

    assert boolfunc.VARIABLES == {}
    assert boolfunc._UNIQIDS == {}
    assert boolfunc._COUNT == 1
    assert expr._LITS == {}
    assert expr._ASSUMPTIONS == set()
    assert bdd._VARS == {}
    assert table._VARS == {}

    exprvar("a")
    bddvar("b")
    ttvar("c")

    assert boolfunc.VARIABLES
    assert boolfunc._UNIQIDS
    assert boolfunc._COUNT == 4
    assert expr._LITS
    assert bdd._VARS
    assert table._VARS

    ba.reset_state()

    assert boolfunc.VARIABLES == {}
    assert boolfunc._UNIQIDS == {}
    assert boolfunc._COUNT == 1
    assert expr._LITS == {}
    assert bdd._VARS == {}
    assert table._VARS == {}


def _body_recycles_uniqids():
    import pyeda.boolalg as ba
    from pyeda.inter import exprvar

    a = exprvar("a")
    b = exprvar("b")
    assert (a.uniqid, b.uniqid) == (1, 2)

    ba.reset_state()

    # a fresh name gets uniqid 1 again, exactly as in a pristine process
    x = exprvar("x")
    assert x.uniqid == 1


def _body_clears_assumptions():
    from pyeda.boolalg import expr
    from pyeda.inter import exprvar

    a = exprvar("a")
    # __enter__ without a matching __exit__: e.g. an interpreter-level
    # crash inside a `with a:` block that skipped normal cleanup
    a.__enter__()
    assert expr._ASSUMPTIONS == {a}

    import pyeda.boolalg as ba
    ba.reset_state()

    assert expr._ASSUMPTIONS == set()


def _body_bdd_terminals_survive():
    """BDDZERO/BDDONE (and the BDDNODEZERO/BDDNODEONE they wrap) are
    singletons seeded once at import time. reset_state() must not
    silently replace them, or every `is BDDZERO`-style identity check
    in bdd.py would start failing."""
    import pyeda.boolalg as ba
    from pyeda.boolalg.bdd import BDDONE, BDDZERO, expr2bdd
    from pyeda.boolalg.expr import expr as _expr
    from pyeda.inter import bddvar

    bddvar("a")
    ba.reset_state()

    assert expr2bdd(_expr(0)) is BDDZERO
    assert expr2bdd(_expr(1)) is BDDONE

    b = bddvar("b")
    assert (b | ~b) is BDDONE
    assert (b & ~b) is BDDZERO


def _body_exprnode_cache_reset():
    from pyeda.boolalg import exprnode
    from pyeda.inter import exprvar

    exprvar("a")
    # must not raise, and must leave the extension in a working state
    exprnode.reset()

    x = exprvar("x")
    assert (x | ~x).simplify().is_one()


def _body_per_module_reset_functions():
    from pyeda.boolalg import bdd, boolfunc, expr, table
    from pyeda.inter import bddvar, exprvar, ttvar

    exprvar("a")
    bddvar("b")
    ttvar("c")

    bdd.reset_state()
    assert bdd._VARS == {}

    table.reset_state()
    assert table._VARS == {}

    expr.reset_state()
    assert expr._LITS == {}

    boolfunc.reset_state()
    assert boolfunc.VARIABLES == {}
    assert boolfunc._UNIQIDS == {}
    assert boolfunc._COUNT == 1


def _body_repeated_reset_cycles_stay_correct_and_bounded():
    """Simulate a long-running process reusing pyeda repeatedly: build
    and discard Boolean functions across many "runs", resetting between
    each. Uniqids and cache sizes must stay bounded, and each run must
    behave exactly like a fresh process."""
    import pyeda.boolalg as ba
    from pyeda.boolalg import bdd, boolfunc, expr, table
    from pyeda.inter import bddvar, exprvar, ttvar

    for _ in range(20):
        ex = exprvar("a")
        bd = bddvar("a")
        tt = ttvar("a")

        # the three backends must agree on uniqid within a run, exactly
        # as they would in a pristine process
        assert ex.uniqid == bd.uniqid == tt.uniqid == 1

        assert (ex | ~ex).simplify().is_one()
        assert (bd | ~bd).is_one()

        ba.reset_state()

        assert boolfunc.VARIABLES == {}
        assert boolfunc._COUNT == 1
        assert expr._LITS == {}
        assert bdd._VARS == {}
        assert table._VARS == {}


def test_reset_state_clears_all_registries():
    _isolated(_body_clears_all_registries)


def test_reset_state_recycles_uniqids():
    _isolated(_body_recycles_uniqids)


def test_reset_state_clears_assumptions():
    _isolated(_body_clears_assumptions)


def test_reset_state_bdd_terminals_survive():
    _isolated(_body_bdd_terminals_survive)


def test_exprnode_reset():
    _isolated(_body_exprnode_cache_reset)


def test_per_module_reset_functions():
    _isolated(_body_per_module_reset_functions)


def test_repeated_reset_cycles_stay_correct_and_bounded():
    _isolated(_body_repeated_reset_cycles_stay_correct_and_bounded)

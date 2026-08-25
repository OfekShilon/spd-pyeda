"""
PyEDA Boolean Algebra
"""

from pyeda.boolalg import bdd, boolfunc, expr, table


def reset_state():
    """Reset all global pyeda.boolalg registries and counters.

    ``Variable`` instances are interned and identified by a global,
    ever-increasing ``uniqid``, and the ``Expression``/``BinaryDecisionDiagram``/
    ``TruthTable`` wrappers around them are interned the same way (including
    the ``exprnode`` C extension's own literal cache). None of these
    registries are ever pruned, so a long-running process that keeps
    building and discarding Boolean functions will leak memory over time.
    Call this function between logically distinct "runs" to clear them.

    .. warning::
       This is only safe once every ``Variable``/``Expression``/
       ``BinaryDecisionDiagram``/``TruthTable`` object from the previous
       run has been discarded. Uniqids restart from 1 after the reset, so
       an object kept alive across the call can collide with an unrelated
       new object that happens to be assigned the same uniqid.
    """
    bdd.reset_state()
    table.reset_state()
    expr.reset_state()
    boolfunc.reset_state()


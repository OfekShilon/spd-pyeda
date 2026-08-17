"""
PyEDA C extension build config.

All distribution metadata lives in pyproject.toml; this file only declares the
things setuptools cannot express statically.
"""


import sys
from os.path import join as pjoin

from setuptools import setup, Extension


# Espresso extension
ESPRESSO = dict(
    define_macros=[],
    include_dirs=[
        pjoin("thirdparty", "espresso", "src"),
    ],
    sources=[
        pjoin("thirdparty", "espresso", "src", "cofactor.c"),
        pjoin("thirdparty", "espresso", "src", "cols.c"),
        pjoin("thirdparty", "espresso", "src", "compl.c"),
        pjoin("thirdparty", "espresso", "src", "contain.c"),
        pjoin("thirdparty", "espresso", "src", "cubestr.c"),
        pjoin("thirdparty", "espresso", "src", "cvrin.c"),
        pjoin("thirdparty", "espresso", "src", "cvrm.c"),
        pjoin("thirdparty", "espresso", "src", "cvrmisc.c"),
        pjoin("thirdparty", "espresso", "src", "cvrout.c"),
        pjoin("thirdparty", "espresso", "src", "dominate.c"),
        pjoin("thirdparty", "espresso", "src", "espresso.c"),
        pjoin("thirdparty", "espresso", "src", "essen.c"),
        pjoin("thirdparty", "espresso", "src", "exact.c"),
        pjoin("thirdparty", "espresso", "src", "expand.c"),
        pjoin("thirdparty", "espresso", "src", "gasp.c"),
        pjoin("thirdparty", "espresso", "src", "gimpel.c"),
        pjoin("thirdparty", "espresso", "src", "globals.c"),
        pjoin("thirdparty", "espresso", "src", "hack.c"),
        pjoin("thirdparty", "espresso", "src", "indep.c"),
        pjoin("thirdparty", "espresso", "src", "irred.c"),
        pjoin("thirdparty", "espresso", "src", "matrix.c"),
        pjoin("thirdparty", "espresso", "src", "mincov.c"),
        pjoin("thirdparty", "espresso", "src", "opo.c"),
        pjoin("thirdparty", "espresso", "src", "pair.c"),
        pjoin("thirdparty", "espresso", "src", "part.c"),
        pjoin("thirdparty", "espresso", "src", "primes.c"),
        pjoin("thirdparty", "espresso", "src", "reduce.c"),
        pjoin("thirdparty", "espresso", "src", "rows.c"),
        pjoin("thirdparty", "espresso", "src", "set.c"),
        pjoin("thirdparty", "espresso", "src", "setc.c"),
        pjoin("thirdparty", "espresso", "src", "sharp.c"),
        pjoin("thirdparty", "espresso", "src", "sminterf.c"),
        pjoin("thirdparty", "espresso", "src", "solution.c"),
        pjoin("thirdparty", "espresso", "src", "sparse.c"),
        pjoin("thirdparty", "espresso", "src", "unate.c"),
        pjoin("thirdparty", "espresso", "src", "verify.c"),
        pjoin("pyeda", "boolalg", "espressomodule.c"),
    ]
)

# exprnode C extension
EXPRNODE = dict(
    define_macros=[
        ("NDEBUG", None),
    ],
    include_dirs=[
        pjoin("extension", "boolexpr"),
    ],
    sources=[
        pjoin("extension", "boolexpr", "argset.c"),
        pjoin("extension", "boolexpr", "array.c"),
        pjoin("extension", "boolexpr", "binary.c"),
        pjoin("extension", "boolexpr", "boolexpr.c"),
        pjoin("extension", "boolexpr", "bubble.c"),
        pjoin("extension", "boolexpr", "compose.c"),
        pjoin("extension", "boolexpr", "dict.c"),
        pjoin("extension", "boolexpr", "flatten.c"),
        pjoin("extension", "boolexpr", "nnf.c"),
        pjoin("extension", "boolexpr", "product.c"),
        pjoin("extension", "boolexpr", "set.c"),
        pjoin("extension", "boolexpr", "simple.c"),
        pjoin("extension", "boolexpr", "util.c"),
        pjoin("extension", "boolexpr", "vector.c"),
        pjoin("pyeda", "boolalg", "exprnodemodule.c"),
    ],
    extra_compile_args=["--std=c99"],
)

# PicoSAT C extension
PICOSAT = dict(
    define_macros=[
        ("NDEBUG", None),
    ],
    include_dirs=[
        pjoin("thirdparty", "picosat"),
    ],
    sources=[
        pjoin("thirdparty", "picosat", "picosat.c"),
        pjoin("pyeda", "boolalg", "picosatmodule.c"),
    ],
)

if sys.platform == "win32":
    for _ext in (ESPRESSO, EXPRNODE, PICOSAT):
        _ext["extra_compile_args"] = []
    PICOSAT["define_macros"] += [
        ("NGETRUSAGE", None),
        ("inline", "__inline"),
    ]

EXT_MODULES = [
    Extension("pyeda.boolalg.espresso", **ESPRESSO),
    Extension("pyeda.boolalg.exprnode", **EXPRNODE),
    Extension("pyeda.boolalg.picosat", **PICOSAT),
]

SCRIPTS = [
    pjoin("script", "espresso"),
    pjoin("script", "picosat"),
]

setup(
    ext_modules=EXT_MODULES,
    scripts=SCRIPTS,
)

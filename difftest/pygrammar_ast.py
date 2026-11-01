"""Canonical JSON encoding of Python `ast` trees, shared by the pygrammar difftests.

Mirrors `lean/PyLean/PyGrammar/Ast.lean`:

  node        {"c": name, "l": [lineno, col, end_lineno, end_col] | null, "f": [fields]}
  seq         JSON array;  None for an absent optional field: null
  identifier  {"id": [cps]};  string {"s": [cps]};  int {"n": i}
  constant    {"k": kind, "v": value}
"""

import ast
import math
import struct


def bits(x):
    return str(struct.unpack("<Q", struct.pack("<d", x))[0])


def enc_const(v):
    if v is None:
        return {"k": "None"}
    if v is True:
        return {"k": "True"}
    if v is False:
        return {"k": "False"}
    if v is Ellipsis:
        return {"k": "Ellipsis"}
    if isinstance(v, int):
        return {"k": "int", "v": str(v)}
    if isinstance(v, float):
        return {"k": "float", "v": bits(v)}
    if isinstance(v, complex):
        return {"k": "complex", "v": [bits(v.real), bits(v.imag)]}
    if isinstance(v, str):
        return {"k": "str", "v": [ord(c) for c in v]}
    if isinstance(v, bytes):
        return {"k": "bytes", "v": list(v)}
    if isinstance(v, tuple):
        return {"k": "tuple", "v": [enc_const(x) for x in v]}
    if isinstance(v, frozenset):
        return {"k": "frozenset", "v": [enc_const(x) for x in v]}
    raise TypeError(f"not a constant: {v!r}")


def enc_cps(s):
    return [ord(c) for c in s]


ATTRS = ("lineno", "col_offset", "end_lineno", "end_col_offset")


def _enc_field(typ, v):
    """`typ` is one of identifier/int/string/constant or anything else for a node."""
    if v is None and typ != "constant":
        return None
    if isinstance(v, list):
        return [_enc_field(typ, x) for x in v]
    if typ == "identifier":
        return {"id": enc_cps(v)}
    if typ == "string":
        return {"s": enc_cps(v)}
    if typ == "int":
        return {"n": v}
    if typ == "constant":
        return enc_const(v)
    return enc(v)


def enc(node):
    """Encode an `ast.AST`. Field order and builtin types come from `_field_types`."""
    fields = []
    types = getattr(node, "_field_types", {})
    for name in node._fields:
        t = types.get(name)
        v = getattr(node, name, None)
        fields.append(_enc_field(_base(t), v))
    has_loc = "lineno" in node._attributes
    loc = [getattr(node, a, None) for a in ATTRS] if has_loc else None
    if loc is not None:
        loc = [-1 if x is None else x for x in loc]
    return {"c": type(node).__name__, "l": loc, "f": fields}


def _base(t):
    """Reduce an `_field_types` annotation to the ASDL base name."""
    import types as _t
    if isinstance(t, _t.UnionType):
        args = [a for a in t.__args__ if a is not _t.NoneType]
        return _base(args[0]) if args else "constant"
    origin = getattr(t, "__origin__", None)
    if origin is list:
        return _base(t.__args__[0])
    if t is str:
        return "string"
    if t is int:
        return "int"
    if t is object:
        return "constant"
    name = getattr(t, "__name__", "")
    if name == "_Identifier" or name == "identifier":
        return "identifier"
    return "node"


# `_field_types` calls identifiers `str` too, so the exact ASDL types come from this
# table of the identifier-typed fields in Python.asdl.
_IDENT = {("FunctionDef", "name"), ("AsyncFunctionDef", "name"), ("ClassDef", "name"),
          ("ImportFrom", "module"), ("Global", "names"), ("Nonlocal", "names"),
          ("Attribute", "attr"), ("Name", "id"), ("ExceptHandler", "name"),
          ("arg", "arg"), ("keyword", "arg"), ("alias", "name"), ("alias", "asname"),
          ("MatchMapping", "rest"), ("MatchClass", "kwd_attrs"), ("MatchStar", "name"),
          ("MatchAs", "name"), ("TypeVar", "name"), ("ParamSpec", "name"),
          ("TypeVarTuple", "name")}


def _fix_ident(node, fields):
    cls = type(node).__name__
    for i, name in enumerate(node._fields):
        if (cls, name) in _IDENT:
            f = fields[i]
            if isinstance(f, dict):
                fields[i] = {"id": f["s"]}
            elif isinstance(f, list):
                fields[i] = [{"id": x["s"]} for x in f]
    return fields


_enc = enc


def enc(node):  # noqa: F811
    r = _enc(node)
    _fix_ident(node, r["f"])
    return r

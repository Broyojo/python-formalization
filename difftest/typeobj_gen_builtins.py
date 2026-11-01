"""Generate lean/PyLean/TypeObj/BuiltinTable.lean by introspecting CPython 3.14.7.

Usage: python3 difftest/typeobj_gen_builtins.py > lean/PyLean/TypeObj/BuiltinTable.lean

For each builtin type the model needs: its size fields, base, BASETYPE flag, and the
ordered keys of `tp_dict` with the kind of each value. Lean turns this into heap cells
(`Builtins.lean`). Addresses follow `namespace B` in `Model.lean`.
"""

import builtins
import sys
import types

NOT_ITER = [iter(()), iter([]), iter("")]
CORE = [
    ("object", object), ("type", type), ("int", int), ("bool", bool), ("float", float),
    ("str", str), ("tuple", tuple), ("list", list), ("dict", dict),
    ("NoneType", type(None)), ("NotImplementedType", type(NotImplemented)),
    ("ellipsis", type(Ellipsis)), ("function", types.FunctionType),
    ("method", types.MethodType), ("builtin_function_or_method", types.BuiltinFunctionType),
    ("wrapper_descriptor", types.WrapperDescriptorType),
    ("method-wrapper", types.MethodWrapperType),
    ("method_descriptor", types.MethodDescriptorType),
    ("classmethod_descriptor", types.ClassMethodDescriptorType),
    ("member_descriptor", types.MemberDescriptorType),
    ("getset_descriptor", types.GetSetDescriptorType),
    ("property", property), ("classmethod", classmethod), ("staticmethod", staticmethod),
    ("super", super), ("mappingproxy", types.MappingProxyType),
    ("iterator", type(iter(type("S", (), {"__getitem__": lambda s, i: i})()))),
    ("list_iterator", type(iter([]))), ("tuple_iterator", type(iter(()))),
    ("str_ascii_iterator", type(iter(""))), ("cell", types.CellType),
]
EXC_FIRST = ["BaseException", "Exception", "TypeError", "AttributeError", "ValueError",
             "IndexError", "KeyError", "OverflowError", "StopIteration", "RuntimeError",
             "SystemError", "ZeroDivisionError", "NameError", "NotImplementedError",
             "RecursionError", "ArithmeticError", "LookupError", "UnboundLocalError",
             "BaseExceptionGroup", "ExceptionGroup", "DeprecationWarning", "RuntimeWarning",
             "MemoryError"]


def all_exceptions():
    seen = list(EXC_FIRST)
    pending = [getattr(builtins, n) for n in dir(builtins)
               if isinstance(getattr(builtins, n), type)
               and issubclass(getattr(builtins, n), BaseException)]
    pending = [c for c in pending if c.__name__ not in seen]
    # Bases before subclasses.
    while pending:
        for c in pending:
            if c.__base__.__name__ in seen and all(b.__name__ in seen for b in c.__bases__):
                seen.append(c.__name__)
                pending.remove(c)
                break
        else:
            sys.exit(f"cannot order {pending}")
    return [(n, getattr(builtins, n)) for n in seen]


# PyGetSetDefs with a setter, and members without Py_READONLY.
WRITABLE = {
    ("object", "__class__"), ("type", "__name__"), ("type", "__qualname__"), ("type", "__bases__"),
    ("type", "__module__"), ("type", "__abstractmethods__"), ("type", "__doc__"),
    ("type", "__annotations__"), ("type", "__annotate__"), ("type", "__type_params__"),
    ("function", "__code__"), ("function", "__defaults__"), ("function", "__kwdefaults__"),
    ("function", "__name__"), ("function", "__qualname__"), ("function", "__doc__"),
    ("function", "__module__"), ("function", "__dict__"), ("function", "__annotations__"),
    ("function", "__annotate__"), ("function", "__type_params__"),
    ("property", "__doc__"), ("property", "__name__"),
    ("BaseException", "args"), ("BaseException", "__traceback__"), ("BaseException", "__context__"),
    ("BaseException", "__cause__"), ("BaseException", "__suppress_context__"),
    ("BaseException", "__dict__"), ("classmethod", "__dict__"), ("staticmethod", "__dict__"),
    ("classmethod", "__annotations__"), ("classmethod", "__annotate__"),
    ("staticmethod", "__annotations__"), ("staticmethod", "__annotate__"),
    ("cell", "cell_contents"),
}


def kind(tname, key, v):
    if key == "__new__":
        return ".new"
    if key == "__hash__" and v is None:
        return ".noneV"
    if isinstance(v, types.WrapperDescriptorType):
        return ".w"
    if isinstance(v, types.MethodDescriptorType):
        return ".m"
    if isinstance(v, types.ClassMethodDescriptorType):
        return ".c"
    if isinstance(v, types.GetSetDescriptorType):
        return f".g {'true' if (tname, key) in WRITABLE else 'false'}"
    if isinstance(v, types.MemberDescriptorType):
        return f".mem {'true' if (tname, key) not in WRITABLE else 'false'}"
    if isinstance(v, staticmethod):
        return ".stat"
    if isinstance(v, str):
        return ".doc"
    if v is None:
        return ".noneV"
    return ".other"


def lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def emit(addr, name, t, index):
    base = t.__base__
    base_txt = "none" if base is None else f"(some {index[base]})"
    entries = ", ".join(f"({lean_str(k)}, {kind(name, k, v)})" for k, v in t.__dict__.items())
    basetype = "true" if t.__flags__ & (1 << 10) else "false"
    mod = "" if t.__module__ == "builtins" else t.__module__
    print(f'  ⟨{addr}, {lean_str(name)}, {base_txt}, {t.__basicsize__}, {t.__itemsize__}, '
          f'{t.__dictoffset__}, {t.__weakrefoffset__}, {basetype}, [{entries}]⟩,')


def main():
    rows = CORE + all_exceptions() + [("GenericAlias", types.GenericAlias), ("Union", types.UnionType)]
    index = {t: i for i, (_, t) in enumerate(rows)}
    print('import PyLean.TypeObj.Model\n')
    print('/-! Generated by `difftest/typeobj_gen_builtins.py` from CPython '
          f'{sys.version.split()[0]}. Do not edit. -/\n')
    print('namespace PyLean.TypeObj\n')
    print('''/-- The kind of a `tp_dict` value of a builtin type. -/
inductive EntryKind where
  | w | m | c | new | noneV | stat | doc | other
  | g (canSet : Bool)
  | mem (readonly : Bool)
  deriving Repr, Inhabited, DecidableEq

/-- A builtin type: address, name, `tp_base`, `tp_basicsize`, `tp_itemsize`,
`tp_dictoffset`, `tp_weaklistoffset`, `Py_TPFLAGS_BASETYPE`, and the keys of `tp_dict`. -/
structure BuiltinRow where
  addr : Addr
  name : String
  base : Option Addr
  basicsize : Nat
  itemsize : Nat
  dictoffset : Int
  weaklistoffset : Int
  baseType : Bool
  entries : List (Name × EntryKind)
''')
    print('def builtinTable : List BuiltinRow := [')
    for addr, (name, t) in enumerate(rows):
        emit(addr, name, t, index)
    print('  ]\n\nend PyLean.TypeObj')


if __name__ == "__main__":
    main()

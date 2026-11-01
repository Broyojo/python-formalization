"""Scan stdlib code objects: instruction whose handler lookup at ip differs from ip-1."""
import dis, sys, os, pathlib, types, collections, opcode

INLINING = {'CALL', 'CALL_KW', 'CALL_FUNCTION_EX', 'BINARY_OP', 'LOAD_ATTR', 'FOR_ITER', 'SEND'}

def lookup(tab, off):
    for e in tab:
        if e.start <= off < e.end:
            return (e.target, e.depth, e.lasti)
    return None

def walk(co):
    yield co
    for c in co.co_consts:
        if isinstance(c, types.CodeType):
            yield from walk(c)

hits = collections.Counter()
samples = {}
root = pathlib.Path(os.path.dirname(os.__file__))
n = 0
for p in root.rglob('*.py'):
    try:
        src = p.read_text(encoding='utf8')
        top = compile(src, str(p), 'exec')
    except Exception:
        continue
    for co in walk(top):
        tab = dis._parse_exception_table(co)
        if not tab:
            continue
        n += 1
        for ins in dis.get_instructions(co):
            if ins.opname in INLINING:
                a = lookup(tab, ins.offset)
                b = lookup(tab, ins.offset - 2)
                if a != b:
                    hits[ins.opname] += 1
                    samples.setdefault(ins.opname, []).append((str(p), co.co_name, ins.offset, a, b))
print(n, hits)
for k, v in samples.items():
    print(k, v[:6])

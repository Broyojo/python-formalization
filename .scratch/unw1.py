import dis, sys

def bad():
    yield 1
    raise ValueError("boom")

def f(mk):
    x = 'outer'
    try:
        r = [x for x in mk()]
    except ValueError:
        pass
    return x

dis.dis(f)
print(dis.code_info(f))
for _ in range(10):
    print(f(bad), end=' ')
print()
for _ in range(2000):
    v = f(bad)
print('hot', v)
dis.dis(f, adaptive=True, show_caches=False)
for ent in dis._parse_exception_table(f.__code__):
    print(ent)

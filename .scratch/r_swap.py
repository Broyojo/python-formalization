import sys, dis
DEPTH = int(sys.argv[1]) if len(sys.argv) > 1 else 13
src = "def victim():\n    n = 0\n"
ind = "    "
for i in range(DEPTH):
    src += ind + f"for i{i} in [1]:\n"
    ind += "    "
src += ind + "w = [j for j in [1]]\n"
src += ind + "n += 1\n"
src += ind + "n += 2\n"
src += "    return n\n"
ns = {}
exec(compile(src, "<v>", "exec"), ns)
victim = ns["victim"]
print('depth', DEPTH, 'swaps', sum(i.opname == 'SWAP' for i in dis.get_instructions(victim)),
      'stacksize', victim.__code__.co_stacksize)
first = victim.__code__.co_firstlineno
LINE_FROM = first + 2 + DEPTH
LINE_TO = LINE_FROM + 1
done = [False]
res = ['none']
def tracer(frame, event, arg):
    if frame.f_code is victim.__code__ and event == 'line' and frame.f_lineno == LINE_FROM and not done[0]:
        done[0] = True
        try:
            frame.f_lineno = LINE_TO
            res[0] = 'allowed'
        except ValueError as e:
            res[0] = 'ValueError: ' + str(e)
    return tracer
sys.settrace(tracer)
out = victim()
sys.settrace(None)
print('jump', res[0], 'result', out)

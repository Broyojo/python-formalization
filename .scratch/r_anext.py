class Aw:
    calls = 0
    def __await__(self):
        Aw.calls += 1
        yield 1
        yield 2
        return 'done'
class A:
    def __anext__(self): return Aw()
async def direct(): return await Aw()
async def via(): return await anext(A(), 'default')
def drive(c, limit=8):
    seen = []
    try:
        for _ in range(limit):
            seen.append(c.send(None))
    except StopIteration as e:
        return seen, e.value
    c.close()
    return seen, 'did not finish'
d = drive(direct()); dc = Aw.calls; Aw.calls = 0
v = drive(via()); vc = Aw.calls
print('direct', d, dc)
print('anext', v, vc)
if dc == 1 and vc == 8 and v == ([1]*8, 'did not finish'):
    print('REPRODUCED bytecode-anext-default-restarts-await')

class C:
    def __init__(self):
        pass
C.__abstractmethods__ = frozenset({'f'})
def mk():
    return C()
created = 0
errors = 0
for i in range(40):
    try:
        mk()
        created += 1
    except TypeError:
        errors += 1
print('created', created, 'errors', errors)
if created > 1 and errors >= 1:
    print('REPRODUCED bytecode-call-alloc-enter-init-abstract')

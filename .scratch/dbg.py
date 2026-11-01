"""Find cases that crash pydiff, then report mismatches per family."""
import sys, json, random, subprocess, collections
sys.path.insert(0, 'difftest')
import bytecode_diff as B
from common import PYDIFF, agree

n = int(sys.argv[1]); seed = int(sys.argv[2]); show = int(sys.argv[3]) if len(sys.argv) > 3 else 12
only = sys.argv[4] if len(sys.argv) > 4 else None
rng = random.Random(seed)
cases = []
while len(cases) < n:
    c = B.gen_case(rng)
    if c is None or c['fn'] == 'effect':
        continue
    if only and c.get('family') != only:
        continue
    cases.append(c)

def run(batch):
    p = subprocess.run([str(PYDIFF)], input="".join(json.dumps(c) + "\n" for c in batch), capture_output=True, text=True)
    return p.returncode, p.stdout.splitlines(), p.stderr

rc, out, err = run(cases)
if rc != 0:
    print("CRASH rc", rc, "after", len(out), err[:300])
    # first crashing case is the one after the last output line
    bad = cases[len(out)]
    print(bad['src'])
    rc2, o2, e2 = run([bad])
    print('alone rc', rc2, e2[:300])
    sys.exit(1)
tot = collections.Counter(); ok = collections.Counter(); shown = 0
hkinds = collections.Counter()
for c, line in zip(cases, out):
    lo = json.loads(line)
    py = B.run_python(c)
    fam = c['family'] + ('+q' if c['fn'] == 'quick' else '')
    tot[fam] += 1
    good = 'harness_error' not in lo and agree(py, lo)
    ok[fam] += good
    if 'harness_error' in lo:
        hkinds[lo['harness_error'][:60]] += 1
    if not good and shown < show:
        shown += 1
        print("=== MISMATCH", fam); print(c['src']); print(" py  ", py); print(" lean", lo)
print({k: f"{ok[k]}/{tot[k]}" for k in sorted(tot) if ok[k] != tot[k]})
print(sum(ok.values()), '/', sum(tot.values()))
print(hkinds.most_common(15))

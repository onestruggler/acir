#!/usr/bin/env python3
"""Check the five-wire modules in parallel, in dependency order.

A module starts only when every module of Five/ it imports, directly or
not, has been checked, so that no two Agda processes write the same
interface; the closure of the targets under imports inside Five/ is
scheduled, not only the targets.  At most JOBS run at once, and a module
is admitted only if the estimated peaks of the running ones and its own
fit the memory budget.  A heap failure (exit 251) is retried alone with
the big heap.  The whole run holds the global Agda lock (~/.agda-job.lock).

    python3 par5.py JOBS LOG [module ...]     (paths relative to the repo)

With no modules, the targets are Five/Main and Five/Soundness, which
reach every module of Five/; Main needs Four.Complete built (it is
outside Five/, so the first process that needs it builds it alone).
Settings by environment: AGDA (the agda binary), PAR5_OUT (where each
module's output goes, default /tmp/par5_out), PAR5_BUDGET_GB (11),
PAR5_HEAP / PAR5_BIG (5G / 7G), DONE (comma-separated logs of an
earlier run: their passes count as checked -- only for a rerun after
changes that touched neither those modules nor what they import).

The estimates: a D module peaks at about 1.6 GB plus 13.6 kB per byte
of source (emit5's letter-step cut keeps them near 4.5 GB, a few up to
7.9 GB), one over 230 KB gets the big heap from the start; another
module is estimated by the mean of its kind measured so far in the run.
"""
import fcntl, os, re, subprocess, sys, time

JOBS = int(sys.argv[1]); LOG = sys.argv[2]
REPO = os.environ.get('PAR5_REPO') or os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), *(['..'] * 5)))
NS = os.environ.get('PAR5_NS', 'Five')
# PAR5_NS='*': the whole development (every module of Clifford+CS)
MODPFX = 'Examples.Groups.Clifford+CS.' + ('' if NS == '*' else NS + '.')
FIVE = 'Examples/Groups/Clifford+CS/' + ('' if NS == '*' else NS + '/')
TARGETS = sys.argv[3:] or [FIVE + 'Main.agda', FIVE + 'Soundness.agda']
OUT = os.environ.get('PAR5_OUT', '/tmp/par5_out')
AGDA = os.environ.get('AGDA', 'agda')
HEAP, BIG = os.environ.get('PAR5_HEAP', '5G'), os.environ.get('PAR5_BIG', '7G')
BUDGET = float(os.environ.get('PAR5_BUDGET_GB', '11')) * 1e6     # kB
DEFAULT = 3.5e6                                                  # kB
BIGSRC = 230_000
os.makedirs(OUT, exist_ok=True)


def log(s):
    with open(LOG, 'a') as f:
        f.write(s + '\n')


def imports(path):
    src = open(os.path.join(REPO, path), encoding='utf-8').read()
    out = set()
    for m in re.findall(r'^\s*(?:open\s+)?import\s+' + re.escape(MODPFX) + r'([^\s(]+)', src, re.M):
        p = FIVE + m.replace('.', '/') + '.agda'
        if os.path.exists(os.path.join(REPO, p)):
            out.add(p)
    return out


# The closure of the targets under imports inside Five/.
deps, todo = {}, list(TARGETS)
while todo:
    p = todo.pop()
    if p in deps: continue
    deps[p] = imports(p)
    todo += list(deps[p])
order = {p: i for i, p in enumerate(TARGETS)}
mods = sorted(deps, key=lambda p: (order.get(p, -1), p))


def kind(p):
    b = p[len(FIVE):].split('/')[-2:]
    d = b[0] if len(b) == 2 else ''
    return 'R' if d == 'D' and b[1].startswith('R') else 'D' if d == 'D' else 'W' if d == 'Wins' else 'o'


def size(p): return os.path.getsize(os.path.join(REPO, p))


def heap_for(p): return BIG if size(p) > BIGSRC else HEAP


seen, force = {}, {}


def peak(p):
    if p in force: return force[p]
    if size(p) > BIGSRC: return 12e6                    # the big heap, measured near it
    if kind(p) == 'D': return 1.6e6 + 13.6 * size(p)
    xs = seen.get(kind(p))
    return sum(xs) / len(xs) if xs else DEFAULT


lock = open(os.path.expanduser(os.environ.get('PAR5_LOCK', '~/.agda-job.lock')), 'w')
fcntl.flock(lock, fcntl.LOCK_EX)
log(f'par5: {len(mods)} modules ({len(TARGETS)} targets), {JOBS} jobs, budget {BUDGET / 1e6:.1f} GB')

done, failed, running, retry = set(), set(), {}, []
cool = [0.0]
if os.environ.get('DONE'):
    for f in os.environ['DONE'].split(','):
        for line in open(f, errors='replace'):
            m = re.match(r'(\S+\.agda) exit=0 ', line)
            if m and m.group(1) in deps: done.add(m.group(1))
    log(f'par5: {len(done)} modules done in {os.environ["DONE"]}')
t_start = time.time()


def avail():
    # MemAvailable in kB: a module starts only if its estimated peak fits in
    # it with 1.5 GB to spare, so that other sessions' jobs keep their room.
    for line in open('/proc/meminfo'):
        if line.startswith('MemAvailable:'):
            return int(line.split()[1])
    return 0


def start(p, heap):
    tag = p.replace('/', '_')
    out = open(f'{OUT}/{tag}.out', 'w')
    proc = subprocess.Popen(['/usr/bin/time', '-f', 'maxrss=%MkB', 'timeout', '3600', AGDA,
                             '+RTS', f'-M{heap}', '-c', '-RTS', p],
                            cwd=REPO, stdout=out, stderr=subprocess.STDOUT)
    running[p] = (proc, time.time(), heap, out, tag)


while True:
    for p in list(running):
        proc, t0, heap, out, tag = running[p]
        rc = proc.poll()
        if rc is None: continue
        out.close(); del running[p]
        txt = open(f'{OUT}/{tag}.out', errors='replace').read()
        m = re.findall(r'maxrss=(\d+)kB', txt)
        rss = int(m[-1]) if m else 0
        log(f'{p} exit={rc} time={int(time.time() - t0)}s maxrss={rss}kB heap={heap} '
            f'elapsed={int(time.time() - t_start)}s')
        if rc == 0:
            os.sync()                        # a VM restart must not lose a checked interface
            done.add(p)
            if rss: seen.setdefault(kind(p), []).append(rss)
        elif rc == 251 and heap != BIG:
            retry.append(p); force[p] = BUDGET
        elif rc == 15:                       # killed by the memory guard: requeue, pause new starts
            cool[0] = time.time() + 120
        else:
            failed.add(p)
            log('\n'.join(l for l in txt.splitlines() if l.strip())[-3000:])
    pending = [p for p in mods if p not in done and p not in failed and p not in running]
    if not pending and not running: break
    for p in pending:
        if any(d in failed for d in deps[p]) and p not in failed:
            failed.add(p); log(f'{p} SKIPPED (a dependency failed)')
    ready = [p for p in pending if p not in failed and all(d in done for d in deps[p])]
    if retry:
        if not running and avail() > 13.5e6:
            p = retry.pop(0); start(p, BIG)
        time.sleep(2); continue
    for p in ready:
        if time.time() < cool[0]: break
        if len(running) >= JOBS: break
        # jobs started in the last two minutes have not grown yet: reserve their estimates
        young = sum(peak(q) for q, r in running.items() if time.time() - r[1] < 120)
        if peak(p) + young + 1.5e6 > avail(): continue
        if running and sum(peak(q) for q in running) + peak(p) > BUDGET: continue
        start(p, heap_for(p))
    if not running and not ready and pending and not retry:
        log('STUCK: ' + ' '.join(pending[:10])); break
    time.sleep(2)

log(f'PAR5 DONE ok={len(done)} failed={len(failed)} elapsed={int(time.time() - t_start)}s')

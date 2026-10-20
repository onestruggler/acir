#!/usr/bin/env python3
"""Check Agda modules in parallel, in dependency order (made for Five/).

A module starts only when every module of the repository it imports,
directly or not, has been checked, so that no two Agda processes write
the same interface; the closure of the targets under imports is
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

Imports are followed anywhere in the repository, not only in Five/, and a
module whose interface is up to date is not run: its interface exists, is
newer than its source and than the interface of everything it imports in
the repository, all of which are up to date in turn (modification times,
a proxy for Agda's hashes that can only err towards running a module).
A timestamp can move without the file changing (a checkout touches it):
a module Agda then finds up to date -- its output has no "Checking" line
for it -- has its interface's timestamp raised to its source's and its
imports', and the modules waiting on it are looked at again, so that a
touched file costs one load, not a recheck of everything above it.
With DRY=1 the stale modules are listed and nothing is run.

A module that has an interface is expected to be up to date, so it is
estimated by the loads measured so far (PROBE_GB before the first); and
whatever the estimates, a job starts only while the memory the system
reports available exceeds its estimate plus PAR5_RESERVE_GB (1).

The estimates: a D module peaks at about 1.6 GB plus 13.6 kB per byte
of source (emit5's letter-step cut keeps them near 4.5 GB, a few up to
7.9 GB), one over 230 KB gets the big heap from the start; another
module is estimated by the mean of its kind measured so far in the run.
"""
import fcntl, os, re, subprocess, sys, time

JOBS = int(sys.argv[1]); LOG = sys.argv[2]
REPO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), *(['..'] * 5)))
FIVE = 'Examples/Groups/Clifford+CS/Five/'
TARGETS = sys.argv[3:] or [FIVE + 'Main.agda', FIVE + 'Soundness.agda']
OUT = os.environ.get('PAR5_OUT', '/tmp/par5_out')
AGDA = os.environ.get('AGDA', 'agda')
HEAP, BIG = os.environ.get('PAR5_HEAP', '5G'), os.environ.get('PAR5_BIG', '7G')
BUDGET = float(os.environ.get('PAR5_BUDGET_GB', '11')) * 1e6     # kB
DEFAULT = 3.5e6                                                  # kB
BIGSRC = 230_000
PROBE = float(os.environ.get('PROBE_GB', '1.5')) * 1e6           # kB
RESERVE = float(os.environ.get('PAR5_RESERVE_GB', '1')) * 1e6    # kB
os.makedirs(OUT, exist_ok=True)


def log(s):
    with open(LOG, 'a') as f:
        f.write(s + '\n')


BUILD = os.path.join(REPO, '_build', '2.8.0', 'agda')


def imports(path):
    src = open(os.path.join(REPO, path), encoding='utf-8').read()
    out = set()
    for m in re.findall(r'^\s*(?:open\s+)?import\s+([A-Za-z][^\s(;]*)', src, re.M):
        p = m.replace('.', '/') + '.agda'
        if os.path.exists(os.path.join(REPO, p)):
            out.add(p)
    return out


# The closure of the targets under imports inside the repository.
deps, todo = {}, list(TARGETS)
while todo:
    p = todo.pop()
    if p in deps: continue
    deps[p] = imports(p)
    todo += list(deps[p])
order = {p: i for i, p in enumerate(TARGETS)}
mods = sorted(deps, key=lambda p: (order.get(p, -1), p))

sys.setrecursionlimit(100000)
fresh = {}


def iface(p): return os.path.join(BUILD, p[:-len('.agda')] + '.agdai')


def is_fresh(p):
    if p in running or p in failed: return False
    if p not in fresh:
        i = iface(p)
        ok = os.path.exists(i) and os.path.getmtime(i) >= os.path.getmtime(os.path.join(REPO, p))
        for d in deps[p]:
            if not ok: break
            ok = is_fresh(d) and os.path.getmtime(iface(d)) <= os.path.getmtime(i)
        fresh[p] = ok
    return fresh[p]


def modname(p): return p[:-len('.agda')].replace('/', '.')


def settle(p):
    # p's interface is up to date: make its timestamp say so.
    i = iface(p)
    ts = [os.path.getmtime(i), os.path.getmtime(os.path.join(REPO, p))]
    ts += [os.path.getmtime(iface(d)) for d in deps[p] if os.path.exists(iface(d))]
    os.utime(i, (max(ts), max(ts)))


running, failed = {}, set()
stale = [p for p in mods if not is_fresh(p)]
if os.environ.get('DRY'):
    for p in stale: print(p, os.path.getsize(os.path.join(REPO, p)))
    print(f'{len(stale)} stale of {len(mods)}')
    sys.exit(0)


def kind(p):
    if not p.startswith(FIVE): return os.path.dirname(p)
    b = p[len(FIVE):]
    return 'R' if b.startswith('D/R') else 'D' if b.startswith('D/') else 'W' if b.startswith('Wins/') else 'o'


def size(p): return os.path.getsize(os.path.join(REPO, p))


def heap_for(p): return BIG if size(p) > BIGSRC else HEAP


seen, force = {}, {}


probes = []


def available():
    for line in open('/proc/meminfo'):
        if line.startswith('MemAvailable:'): return int(line.split()[1])
    return BUDGET


def peak(p):
    if p in force: return force[p]
    if os.path.exists(iface(p)) and kind(p) != 'D':
        return max(probes) * 1.3 if probes else PROBE
    if kind(p) == 'D': return 1.6e6 + 13.6 * size(p)
    xs = seen.get(kind(p))
    return sum(xs) / len(xs) if xs else DEFAULT


lock = open(os.path.expanduser('~/.agda-job.lock'), 'w')
fcntl.flock(lock, fcntl.LOCK_EX)
log(f'par5: {len(mods)} modules ({len(TARGETS)} targets), {JOBS} jobs, budget {BUDGET / 1e6:.1f} GB')

done, retry = {p for p in mods if fresh[p]}, []
log(f'par5: {len(done)} modules up to date, {len(mods) - len(done)} to check')
if os.environ.get('DONE'):
    for f in os.environ['DONE'].split(','):
        for line in open(f, errors='replace'):
            m = re.match(r'(\S+\.agda) exit=0 ', line)
            if m and m.group(1) in deps: done.add(m.group(1))
    log(f'par5: {len(done)} modules done in {os.environ["DONE"]}')
t_start = time.time()


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
            done.add(p)
            if f'Checking {modname(p)} ' in txt:
                if rss: seen.setdefault(kind(p), []).append(rss)
            else:
                if rss: probes.append(rss)
                settle(p)
                fresh.clear()
                now = [q for q in mods if q not in done and q not in running and is_fresh(q)]
                done.update(now)
                log(f'{p} was up to date; {len(now)} more now up to date')
        elif rc == 251 and heap != BIG:
            retry.append(p); force[p] = BUDGET
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
        if not running:
            p = retry.pop(0); start(p, BIG)
        time.sleep(2); continue
    for p in ready:
        if len(running) >= JOBS: break
        if running and sum(peak(q) for q in running) + peak(p) > BUDGET: continue
        if running and available() < peak(p) + RESERVE: continue
        start(p, heap_for(p))
    if not running and not ready and pending and not retry:
        log('STUCK: ' + ' '.join(pending[:10])); break
    time.sleep(2)

log(f'PAR5 DONE ok={len(done)} failed={len(failed)} elapsed={int(time.time() - t_start)}s')

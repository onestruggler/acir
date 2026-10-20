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
module whose interface is up to date is not run.  That is decided as Agda
decides it, from the interface file and not from timestamps (a checkout
touches files it does not change): after a 24-byte header -- the source
hash, the interface hash, the interface version -- an interface is a gzip
stream that holds the module's source text, line endings normalised to LF
and preceded by its length in eight bytes, and the interface hash of every
module it imports.  So a module is up to date when its interface holds its
current source, and the current interface hash of each module it imports
in the repository, each of which is up to date in turn.  A module that is
rechecked with a new interface hash makes its importers stale; one Agda
rechecks while checking another (an "Checking" line in its output) counts
as checked.  Modules outside the repository (the standard library,
EucDomain) are taken to be up to date.
With DRY=1 the stale modules are listed and nothing is run.

Whatever the estimates, a job starts only while the memory the system
reports available exceeds its estimate plus PAR5_RESERVE_GB (1).

The estimates: a D module peaks at about 1.6 GB plus 13.6 kB per byte
of source (emit5's letter-step cut keeps them near 4.5 GB, a few up to
7.9 GB), one over 230 KB gets the big heap from the start; another
module is estimated by the mean of its kind measured so far in the run.
"""
import fcntl, os, re, subprocess, sys, time, zlib

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


def iface(p): return os.path.join(BUILD, p[:-len('.agda')] + '.agdai')


def ihash(p):
    with open(iface(p), 'rb') as f:
        return f.read(24)[8:16]


def norm(s): return s.replace(b'\r\n', b'\n').replace(b'\r', b'\n')


# What each interface records: its own source (srcok) and, for each
# import, whether the import's current interface hash (match).
hashes = {p: ihash(p) for p in mods if os.path.exists(iface(p))}
srcok, match = {}, {}
for p in mods:
    if p not in hashes:
        srcok[p], match[p] = False, {}
        continue
    try:
        body = zlib.decompressobj(47).decompress(open(iface(p), 'rb').read()[24:])
    except zlib.error:                    # being written, or truncated
        srcok[p], match[p] = False, {}
        continue
    src = norm(open(os.path.join(REPO, p), 'rb').read())
    srcok[p] = len(src).to_bytes(8, 'big') + src in body
    match[p] = {d: d in hashes and hashes[d] in body for d in deps[p]}
    del body
importers = {p: [q for q in mods if p in deps[q]] for p in mods}
fresh = {}
running, failed, done = {}, set(), set()


def is_fresh(p):
    if p in done: return True
    if p in running or p in failed: return False
    if p not in fresh:
        fresh[p] = srcok[p] and all(match[p][d] and is_fresh(d) for d in deps[p])
    return fresh[p]


def modname(p): return p[:-len('.agda')].replace('/', '.')


bypath = {modname(p): p for p in mods}


def checked(p):
    # p has a new interface: importers that recorded another hash are stale.
    new = ihash(p)
    if new != hashes.get(p):
        for q in importers[p]: match[q][p] = False
        hashes[p] = new


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


def available():
    for line in open('/proc/meminfo'):
        if line.startswith('MemAvailable:'): return int(line.split()[1])
    return BUDGET


def peak(p):
    if p in force: return force[p]
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
            names = re.findall(r'^\s*Checking (\S+) \(', txt, re.M)
            if modname(p) in names:
                if rss: seen.setdefault(kind(p), []).append(rss)
            else:
                log(f'{p} was up to date')
            for n in names:
                q = bypath.get(n)
                if q and q not in running:
                    checked(q)
                    if q != p and q not in done: log(f'{q} checked by {p}')
                    done.add(q)
            done.add(p)
            fresh.clear()
            now = [q for q in mods if q not in done and is_fresh(q)]
            done.update(now)
            if now: log(f'{len(now)} more up to date')
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

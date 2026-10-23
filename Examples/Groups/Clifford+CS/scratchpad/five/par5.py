#!/usr/bin/env python3
"""Check Agda modules in parallel, in dependency order, in batches.

    python3 par5.py JOBS LOG [module ...]     (paths relative to the repo)

The closure of the targets under imports inside the repository is
scheduled, so that no two Agda processes write the same interface: a job
starts only when every module of the repository it imports has been
checked or belongs to the job itself.  A job is a batch of up to BATCH
modules, closed under their unchecked imports, checked by one Agda
process through a generated root module that imports them (Par5Batch/ in
the repository): the interfaces they import are then read once per batch
rather than once per module, which was most of a derivation module's time
(Four/D, Five/D: 20-35 s of loading against 3-16 s of checking).  With
PAR5_BIGSRC set, a module of more source bytes runs alone, estimated at
12 GB (since the chain fix no derivation module needs it).  A batch that fails is split into
single modules, so that the others go on and the error is the module's
own; a heap failure (exit 251) of a single module is retried alone with
the big heap; a job killed by the memory guard (memguard.sh, exit 15) is
requeued after a two-minute pause.

A module is up to date, and not run, when its interface holds its current
source and the current interface hash of each import in the repository,
each up to date in turn -- Agda's own test, read off the files (an Agda
2.8 interface is a 24-byte header, source hash, interface hash, version,
and a gzip stream holding the source text, LF line endings, after its
length in eight bytes, and the hash of every import).  A recheck that
changes an interface's hash makes its importers stale; a module Agda
rechecks while checking another counts as checked.  Modules outside the
repository (the standard library, EucDomain) are taken to be up to date.
With DRY=1 the stale modules are listed and nothing is run.

Memory: at most JOBS jobs; a job starts only if the estimated peaks of the
running jobs and its own fit PAR5_BUDGET_GB, and its estimate, with those
of jobs started in the last PAR5_YOUNG seconds (90: not grown yet), fits
the memory the system reports available less PAR5_RESERVE_GB -- other
sessions share the machine.  A job's estimate is the larger of
PAR5_FLOOR_GB (1.2) plus PAR5_MEMRATE (15) times the size of the
interfaces it loads (everything its modules import in the repository)
and the peak measured for single modules of its kind, plus a little per
batch member.
Every finished job is synced to disk: a restart of the WSL VM loses
unsynced writes.

Settings by environment: PAR5_REPO (the repository, default the one this
script is in), AGDA, PAR5_OUT (each job's output, default /tmp/par5_out),
PAR5_LOCK (default ~/.agda-job.lock, held for the whole run),
PAR5_HEAP / PAR5_BIG (7G / 12G), PAR5_RTS (further RTS options, default
-c -A256m), PAR5_BUDGET_GB (11), PAR5_RESERVE_GB
(2.5), PAR5_BATCH (48; 1 checks one module per process), PAR5_MINB (16:
with many modules ready, a batch takes at least this many rather than
spreading them over the idle slots -- each batch loads its imports once,
and with the jobs bounded by memory rather than by slots that loading
was most of a from-scratch run, 3200 of 5200 s), PAR5_COSTS
(comma-separated logs of earlier runs: a module's checking time there;
unknown, 20 s; only logs of the same layout -- after repack.py a name
like Four/D/D724 is another module, and a stale cost of a heavy one ran
light modules alone, too many of them at once), PAR5_HEAVY (60: a module known to take longer runs
alone), PAR5_TARGET (40: a batch stops at that many seconds of known
time), PAR5_OVERHEAD (5: a job's fixed cost in the critical-path height
by which ready modules are taken, highest first), PAR5_LOADRATE (1.5:
seconds of loading per MB of source a module imports, in that height),
PAR5_SLACK (60: a
ready module within that many seconds of the highest height is critical;
while at most JOBS are, each runs in a job of its own with the critical
modules that wait only on it), DONE (comma-separated
logs of an earlier run whose passes count as checked).  Each module's
own time is read off --profile=modules and logged (own=…ms), so that a
run's log serves the next as PAR5_COSTS: list the newest log last, its
times win.

From scratch, the whole of Clifford+CS (1271 modules, 6 jobs within
15 GB): 1560 s with batches of at most 16 spread over the idle slots and
taken in topological order, 1367 s with PAR5_MINB 16, PAR5_BATCH 48 and
the critical path first (job time 5223 -> 3333 s, most of the saving
loading).  With the derivation modules taking their lemmas as
parameters (1483 modules, 22 GB): 1143 s; 1094 s with chain heads run
alone in a wide critical front; 960 s with the heights counting loading
(and the window libraries no longer under the completeness chain), job
time 4180 s of which 2200 s checking; 824 s with a chain head's
partners; 727 s with Four's consumers taking their lemmas as a
parameter; 618 s with -A256m (job time 2525 s); and 552 s on eight jobs
with the memory estimates from what a job loads (job time 3670 s, 7-8
jobs at a time; -A64m 614 s, -A512m 544 s).  So: python3 par5.py 8 LOG
on this machine (16 cores, 26 GB, PAR5_BUDGET_GB=22).
"""
import fcntl, os, re, subprocess, sys, time, zlib

JOBS = int(sys.argv[1]); LOG = sys.argv[2]
REPO = os.environ.get('PAR5_REPO') or os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), *(['..'] * 5)))
FIVE = 'Examples/Groups/Clifford+CS/Five/'
TARGETS = sys.argv[3:] or [FIVE + 'Main.agda', FIVE + 'Soundness.agda']
OUT = os.environ.get('PAR5_OUT', '/tmp/par5_out')
AGDA = os.environ.get('AGDA', 'agda')
HEAP, BIG = os.environ.get('PAR5_HEAP', '7G'), os.environ.get('PAR5_BIG', '12G')
# Further RTS options.  A 256 MB allocation area (GHC's default is 4 MB)
# cut the garbage collector's share of a job: a batch of twenty Four/D
# modules 13.3 → 12.1 s, four window libraries 23.0 → 20.5 s, and
# Four.ConsInst, which loads all of Four/D, 38.3 → 30.8 s (GC 15.8 →
# 2.7 s) with a lower peak (4.8 → 3.9 GB).
RTS = os.environ.get('PAR5_RTS', '-c -A256m').split()
BUDGET = float(os.environ.get('PAR5_BUDGET_GB', '11')) * 1e6     # kB
RESERVE = float(os.environ.get('PAR5_RESERVE_GB', '2.5')) * 1e6  # kB
BATCH = int(os.environ.get('PAR5_BATCH', '48'))
MINB = int(os.environ.get('PAR5_MINB', '16'))
# The fixed part of a job's estimated peak (PAR5_FLOOR_GB): 2.5 GB when a
# Four/D module loading 87 MB peaked at 2.7 GB; since the derivation
# modules take their lemmas as parameters, and with -A256m, 114 of the
# 150 jobs of a from-scratch run peak under 1.5 GB.
FLOOR = float(os.environ.get('PAR5_FLOOR_GB', '1.2')) * 1e6
# The peak per kB of interfaces loaded (PAR5_MEMRATE): measured with
# -A256m, Four/DAll 3.5 GB loading 178 MB, Four.ConsInst with
# Four.Complete 5.1 GB loading 307 MB, Five.F1 4.2 GB loading 184 MB, a
# window library 1.0 GB loading 10 MB.  A kind of module with no single
# job measured yet counts nothing beyond this (a default of 3.5 GB had been
# every batch's estimate, so that six of them filled the budget and the
# jobs started in the last 90 s held back the rest: 4.1 jobs at a time
# on average, whatever JOBS was).
MEMRATE = float(os.environ.get('PAR5_MEMRATE', '15'))
BIGSRC = int(os.environ.get('PAR5_BIGSRC', '0'))                # 0: none
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
mods = sorted(deps)
sys.setrecursionlimit(100000)

# A topological order: imports first.
topo, seen_t = [], set()


def visit(p):
    if p in seen_t: return
    seen_t.add(p)
    for d in sorted(deps[p]): visit(d)
    topo.append(p)


for p in mods: visit(p)
rank = {p: i for i, p in enumerate(topo)}


def iface(p): return os.path.join(BUILD, p[:-len('.agda')] + '.agdai')


def ihash(p):
    with open(iface(p), 'rb') as f:
        return f.read(24)[8:16]


def norm(s): return s.replace(b'\r\n', b'\n').replace(b'\r', b'\n')


# What each interface records: its own source (srcok) and, for each
# import, whether it holds the import's current interface hash (match).
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
importers = {p: [] for p in mods}
for q in mods:
    for d in deps[q]: importers[d].append(q)
fresh = {}
running, failed, done = {}, set(), set()
busy = set()                              # modules of running jobs


def is_fresh(p):
    if p in done: return True
    if p in busy or p in failed: return False
    if p not in fresh:
        fresh[p] = srcok[p] and all(match[p].get(d, False) and is_fresh(d) for d in deps[p])
    return fresh[p]


def modname(p): return p[:-len('.agda')].replace('/', '.')


bypath = {modname(p): p for p in mods}


def checked(p):
    # p has a new interface: importers that recorded another hash are stale.
    if not os.path.exists(iface(p)): return
    new = ihash(p)
    if new != hashes.get(p):
        for q in importers[p]: match[q][p] = False
        hashes[p] = new


stale = [p for p in topo if not is_fresh(p)]
if os.environ.get('DRY'):
    for p in stale: print(p, os.path.getsize(os.path.join(REPO, p)))
    print(f'{len(stale)} stale of {len(mods)}')
    sys.exit(0)


def kind(p):
    if not p.startswith(FIVE): return os.path.dirname(p)
    b = p[len(FIVE):]
    return 'R' if b.startswith('D/R') else 'D' if b.startswith('D/') else 'W' if b.startswith('Wins/') else 'o'


def size(p): return os.path.getsize(os.path.join(REPO, p))
def big(p): return BIGSRC > 0 and size(p) > BIGSRC


measured, force = {}, {}


def available():
    for line in open('/proc/meminfo'):
        if line.startswith('MemAvailable:'): return int(line.split()[1])
    return BUDGET


def peak(p):
    if p in force: return force[p]
    if big(p): return 12e6
    xs = measured.get(kind(p))
    return sum(xs) / len(xs) if xs else 0


# What a job loads: the interfaces of everything its modules import, in
# the repository.  Agda's peak grows with it -- about 2.5 GB plus 7
# times the interfaces' size on disk (a Four/D module loading 87 MB peaked
# at 2.7 GB, a Five/D one loading 231 MB at 3.5 GB, the top Four/D ones,
# which load most of Four/D, near 6 GB) -- and an estimate from measured
# modules of the same kind missed that by half and let the memory guard
# kill jobs at 40 MB available.
closure = {}


def clos(p):
    if p not in closure:
        out = set()
        for d in deps[p]:
            out.add(d); out |= clos(d)
        closure[p] = out
    return closure[p]


def loads(job):
    seen = set()
    for p in job: seen |= clos(p)
    return sum(os.path.getsize(iface(d)) for d in seen if os.path.exists(iface(d))) / 1000   # kB


def estimate(job):
    # measured: a batch of ten peaks at about its largest member (3.1-3.3 GB)
    by_kind = max(peak(p) for p in job) + 0.03e6 * (len(job) - 1)
    return min(max(by_kind, FLOOR + MEMRATE * loads(job)), 14e6)


# Checking times of earlier runs (PAR5_COSTS: comma-separated logs), in
# seconds: a module's own time where the log has it, else its wall time.
HEAVY = float(os.environ.get('PAR5_HEAVY', '60'))
YOUNG = float(os.environ.get('PAR5_YOUNG', '90'))
TARGET = float(os.environ.get('PAR5_TARGET', '40'))
SLACK = float(os.environ.get('PAR5_SLACK', '60'))
costs = {}
for f in filter(None, os.environ.get('PAR5_COSTS', '').split(',')):
    for line in open(f, errors='replace'):
        m = re.match(r'(\S+\.agda) exit=0 time=(\d+)s(?: own=(\d+)ms)?', line)
        if m: costs[m.group(1)] = int(m.group(3)) / 1000 if m.group(3) else float(m.group(2))


def cost(p):
    # unknown: 20 s, but a window library or evaluation module counts as heavy
    # (Five/Wins took 40-270 s each, and batched they ran one after another)
    if p in costs: return costs[p]
    return 3 * HEAVY if '/Wins/' in p or p.endswith('/Checks.agda') else 20.0
def alone_p(p): return p in solo or big(p) or cost(p) > HEAVY


# The critical path: a module's height is its cost, plus what a job
# spends loading it (PAR5_OVERHEAD, 5 s, plus PAR5_LOADRATE, 1.5 s per MB
# of source in the repository that it imports, directly or not), plus
# the largest height among the modules that import it.  Ready modules
# are taken highest first, so that the long chains (Four/D's 20 levels,
# Five/D's 18) start as soon as they can; in topological order they ran
# last, alone, for the final 500 s of a from-scratch run.  The loading
# term is measured (Lemma87/Four, 32 MB: 51 s beyond its own time; a
# Four/D module, 1-3 MB: about 6 s): with a fixed 5 s, the light modules
# near the end that load all of Four/D (Lemma87/Parts, Sem/S02) looked
# cheap, waited 180 s after they were ready, and then took 78 s.
OVERHEAD = float(os.environ.get('PAR5_OVERHEAD', '5'))
LOADRATE = float(os.environ.get('PAR5_LOADRATE', '1.5'))
srcmb = {p: sum(size(d) for d in clos(p) if os.path.exists(os.path.join(REPO, d))) / 1e6 for p in deps}
def own_h(p): return cost(p) + OVERHEAD + LOADRATE * srcmb[p]
rdeps = {p: set() for p in deps}
for p in deps:
    for d in deps[p]:
        if d in rdeps: rdeps[d].add(p)
height = {}
for p in reversed(topo):
    missing = [q for q in rdeps[p] if q not in height]
    if missing:   # only an import cycle leaves a dependent unvisited
        sys.exit(f'par5: import cycle through {p} and {missing[0]}')
    height[p] = own_h(p) + max((height[q] for q in rdeps[p]), default=0.0)


if os.environ.get('PAR5_HEIGHTS'):   # a file to write the heights to, then stop
    with open(os.environ['PAR5_HEIGHTS'], 'w') as f:
        for p in sorted(height, key=lambda q: -height[q]):
            f.write(f'{height[p]:8.1f} {own_h(p):7.1f} {p}\n')
    sys.exit(0)
lock = open(os.path.expanduser(os.environ.get('PAR5_LOCK', '~/.agda-job.lock')), 'w')
fcntl.flock(lock, fcntl.LOCK_EX)
log(f'par5: {len(mods)} modules ({len(TARGETS)} targets), {JOBS} jobs, batches of {BATCH}, '
    f'budget {BUDGET / 1e6:.1f} GB')
done = {p for p in mods if fresh[p]}
log(f'par5: {len(done)} modules up to date, {len(mods) - len(done)} to check')
if os.environ.get('DONE'):
    for f in os.environ['DONE'].split(','):
        for line in open(f, errors='replace'):
            m = re.match(r'(\S+\.agda) exit=0 ', line)
            if m and m.group(1) in deps: done.add(m.group(1))
    log(f'par5: {len(done)} modules done in {os.environ["DONE"]}')
t_start = time.time()
BDIR = os.path.join(REPO, 'Par5Batch')
os.makedirs(BDIR, exist_ok=True)
nbatch = [0]
solo, retry = set(), []
cool = [0.0]


def start(job, heap):
    nbatch[0] += 1
    if len(job) == 1:
        target, tag = job[0], job[0].replace('/', '_')
    else:
        name = f'B{os.getpid()}x{nbatch[0]}'
        target, tag = f'Par5Batch/{name}.agda', name
        with open(os.path.join(REPO, target), 'w', encoding='utf-8') as f:
            f.write(f'module Par5Batch.{name} where\n\n' + ''.join(f'import {modname(p)}\n' for p in job))
    out = open(f'{OUT}/{tag}.out', 'w')
    proc = subprocess.Popen(['/usr/bin/time', '-f', 'maxrss=%MkB', 'timeout', '3600', AGDA,
                             '--profile=modules', '+RTS', f'-M{heap}', *RTS, '-RTS', target],
                            cwd=REPO, stdout=out, stderr=subprocess.STDOUT)
    running[tag] = (proc, time.time(), heap, out, job, target)
    busy.update(job)


def own_times(txt):
    # --profile=modules: one line per module checked, "Name   12,345ms"
    out = {}
    for n, ms in re.findall(r'^(\S+)\s+([\d,]+)ms\s*$', txt, re.M):
        out[n] = int(ms.replace(',', ''))
    return out


def form_batch(ready_set, pending, idle):
    # The ready module on the critical path (within SLACK of the highest
    # height) runs in a job of its own, extended by the critical modules
    # that wait only on it and on each other (a chain checks in one
    # process, loading once): batched with forty others, the modules of the
    # base chain (Evaluation, MacroEval, TwoQubit, Swaps, Place, Windows ...)
    # each waited for a batch of 50-180 s, and a from-scratch run took
    # 1400 s of which they were 1000.  The others: many ready modules are
    # spread over the idle slots, at least MINB to a batch; fewer, one of
    # them and the modules that wait only on it.  A batch stops at about
    # TARGET seconds of known checking time (cost, from the own times of
    # earlier logs), and a module known to take over HEAVY seconds runs
    # alone.
    rs = [p for p in pending if p in ready_set and not alone_p(p)]
    if not rs: return []
    top = max(height[p] for p in pending if p in ready_set)
    front = sum(1 for p in pending if p in ready_set and height[p] >= top - SLACK)

    def partners(p):
        # the other ready modules that, with p, complete a critical
        # dependent of p (Windows waits on SemanticSteps and Place, both
        # ready together: neither alone headed a chain, and both waited
        # 170 s behind Four/D); None if there is none
        lim = height[p] - own_h(p) - SLACK
        for q in sorted(rdeps[p], key=lambda x: -height[x]):
            if q in done or q in busy or alone_p(q) or height[q] < lim: continue
            others = [d for d in deps[q] if d not in done and d != p]
            # a few: Four/DAll waits on 788 modules ready at once
            if len(others) <= 3 and all(d in ready_set and d not in busy and not alone_p(d) for d in others):
                return others
        return None

    def chain_after(head):
        # the critical modules that wait only on the job (each lower by
        # the work before it)
        job, spent = [head], own_h(head)
        for d in partners(head) or []:
            job.append(d)
            spent += own_h(d)
        for p in pending:
            if len(job) >= BATCH or sum(map(cost, job)) >= TARGET: break
            if p in job or p in ready_set or alone_p(p): continue
            if height[p] >= height[head] - spent - SLACK and all(d in done or d in job for d in deps[p]):
                job.append(p)
                spent += own_h(p)
        return job
    # The critical module runs in a job of its own, with the chain after
    # it, when the critical front is narrow or when a chain does continue
    # through it.  When many modules are equally critical and none heads
    # a chain (all of Four/D, whose one importer waits on all of them)
    # they are batched as the others are: one job each made a run 1960 s
    # rather than 1350.  But a chain head in a wide front had been batched
    # with 47 of them: Swaps, TopWeakening, Place, Windows and the seven
    # Lemma88/Hybrid modules, a few seconds each, each waited for a batch
    # of 50-105 s, and those two chains were the critical path of a
    # 1143 s run.
    def heads_chain(p):
        return partners(p) is not None
    if height[rs[0]] >= top - SLACK:
        if front <= JOBS:
            return chain_after(rs[0])
        for p in rs:
            if height[p] < top - SLACK: break
            if heads_chain(p):
                return chain_after(p)
    if len(rs) >= idle:
        cap, job = max(1, min(BATCH, max(MINB, -(-len(rs) // idle)))), []
        for p in rs:
            if len(job) >= cap or (job and sum(map(cost, job)) + cost(p) > TARGET): break
            job.append(p)
        return job
    job = [rs[0]]
    for p in pending:
        if len(job) >= BATCH or sum(map(cost, job)) >= TARGET: break
        if p in job or p in ready_set or alone_p(p): continue
        if all(d in done or d in job for d in deps[p]):
            job.append(p)
    return job


while True:
    for tag in list(running):
        proc, t0, heap, out, job, target = running[tag]
        rc = proc.poll()
        if rc is None: continue
        out.close(); del running[tag]; busy.difference_update(job)
        txt = open(f'{OUT}/{tag}.out', errors='replace').read()
        m = re.findall(r'maxrss=(\d+)kB', txt)
        rss = int(m[-1]) if m else 0
        own = own_times(txt)
        wall = int(time.time() - t0)
        if len(job) > 1:
            log(f'batch {tag} of {len(job)} exit={rc} time={wall}s maxrss={rss}kB heap={heap} '
                f'elapsed={int(time.time() - t_start)}s')
        if rc == 0:
            os.sync()
            names = re.findall(r'^\s*Checking (\S+) \(', txt, re.M)
            for p in job:
                log(f'{p} exit=0 time={wall if len(job) == 1 else 0}s own={own.get(modname(p), 0)}ms '
                    f'maxrss={rss}kB heap={heap}{"" if len(job) == 1 else " batch=" + tag} '
                    f'elapsed={int(time.time() - t_start)}s')
                if modname(p) in names and rss and len(job) == 1:
                    measured.setdefault(kind(p), []).append(rss)
            for n in names:
                q = bypath.get(n)
                if q and q not in busy:
                    checked(q)
                    if q not in job and q not in done: log(f'{q} checked by {tag}')
                    done.add(q)
            done.update(job)
            fresh.clear()
            now = [q for q in mods if q not in done and q not in busy and is_fresh(q)]
            done.update(now)
            if now: log(f'{len(now)} more up to date')
        elif rc in (15, 143, -15):                     # the memory guard
            log(f'{tag} killed by the memory guard: requeued')
            cool[0] = time.time() + 120
        elif len(job) > 1:
            log(f'batch {tag} failed (exit {rc}): its modules run alone')
            solo.update(job)
        elif rc == 251 and heap != BIG:
            retry.append(job[0]); force[job[0]] = BUDGET
            log(f'{job[0]} exit=251 heap={heap}: retried with {BIG}')
        else:
            p = job[0]
            failed.add(p)
            log(f'{p} exit={rc} time={wall}s maxrss={rss}kB heap={heap}')
            log('\n'.join(l for l in txt.splitlines() if l.strip())[-3000:])
        if target.startswith('Par5Batch/'):
            for f in (os.path.join(REPO, target), os.path.join(BUILD, target[:-5] + '.agdai')):
                if os.path.exists(f): os.remove(f)
    pending = sorted((p for p in topo if p not in done and p not in failed and p not in busy),
                     key=lambda p: -height[p])
    if not pending and not running: break
    for p in pending:
        if any(d in failed for d in deps[p]) and p not in failed:
            failed.add(p); log(f'{p} SKIPPED (a dependency failed)')
    pending = [p for p in pending if p not in failed]
    ready = [p for p in pending if all(d in done for d in deps[p])]
    if retry:
        if not running and available() > 13.5e6:
            p = retry.pop(0); start([p], BIG)
        time.sleep(2); continue
    # a job reaches its peak in about 20 s (the interfaces it loads): until
    # then, its estimate is not yet in the memory the system reports used
    young = sum(estimate(r[4]) for r in running.values() if time.time() - r[1] < YOUNG)
    started = True
    while started and len(running) < JOBS and time.time() >= cool[0]:
        started = False
        rs = set(ready) - busy
        alone = [p for p in ready if p in rs and (alone_p(p) or BATCH == 1)]
        jobs = [[alone[0]]] if alone else []
        if BATCH > 1:
            b = form_batch(rs, [p for p in pending if p not in busy], JOBS - len(running))
            if b: jobs.append(b)
        load = sum(estimate(r[4]) for r in running.values())
        for job in jobs:
            est = estimate(job)
            if running and load + est > BUDGET: continue
            if est + young + RESERVE > available(): continue
            start(job, BIG if any(big(p) for p in job) else HEAP)
            young += est
            started = True
            break
    if not running and not ready and pending and not retry:
        log('STUCK: ' + ' '.join(pending[:10])); break
    time.sleep(2)

log(f'PAR5 DONE ok={len(done)} failed={len(failed)} elapsed={int(time.time() - t_start)}s')

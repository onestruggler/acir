"""Time a clean build of the Lean formalization, folder by folder.

    python3 leantime.py ../../Lean leantime.json            # clean, then every unit
    python3 leantime.py ../../Lean leantime.json U1,U2,...  # re-time those units only
    LEANTIME_DRY=1 python3 leantime.py ../../Lean x.json    # print the plan only

A unit is a folder of QCert (QCert/<Folder>/...) or one root module
(QCert.lean, QCert/<Name>.lean). The tracked modules are those that git
knows, without the generator templates under gen/. Units are built one at a
time in dependency order of their imports, so every module a unit imports
from another unit is built already and counted there; each build is
`LEAN_NUM_THREADS=2 lake build <the unit's modules>`, timed by the
monotonic clock, Lake startup and artifact generation included. Before the
first unit QCert's build artifacts are removed (Mathlib and the other
packages are kept); re-timing a unit removes only its own artifacts.

The script holds the lock of Lean/check.sh for the whole run, and records
for each unit the CPU seconds that Lean processes of other projects (those
not running in this Lean directory) used while it built (`foreign_cpu_s`),
so that a time taken while something else was building can be told apart
and re-timed. With LEANTIME_IDLE=<seconds> it first waits, at most that
long, until other projects' Lean has used at most LEANTIME_IDLE_CPU
(default 3) CPU-seconds in 30 seconds; 30 allows one busy core. Results are
written to the JSON file after each unit; a re-timing keeps the record of
the first run (`run`) and adds its own (`retimes`).
"""
import fcntl, glob, json, os, platform, re, subprocess, sys, threading, time

LEAN = os.path.abspath(sys.argv[1])
OUT = sys.argv[2]
ONLY = sys.argv[3].split(',') if len(sys.argv) > 3 else None
BUILD = os.path.join(LEAN, '.lake', 'build')
ENV = dict(os.environ, LEAN_NUM_THREADS='2',
           PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])


def tracked_modules():
    out = subprocess.run(['git', '-C', LEAN, 'ls-files', 'QCert.lean', 'QCert'],
                         capture_output=True, text=True, check=True).stdout.split()
    return sorted(p for p in out if p.endswith('.lean') and '/gen/' not in p)


def unit_of(path):
    parts = path[:-len('.lean')].split('/')
    return parts[1] if len(parts) > 2 else '.'.join(parts)


def imports(path):
    found = []
    for ln in open(os.path.join(LEAN, path), encoding='utf-8'):
        if ln.startswith('import '):
            found += ln.split()[1:]
    return [m for m in found if m == 'QCert' or m.startswith('QCert.')]


def order(units, deps):
    done, seq = set(), []
    while len(seq) < len(units):
        ready = sorted(u for u in units if u not in done and deps[u] <= done)
        if not ready:
            raise SystemExit('cycle among units: '
                             + ', '.join(sorted(u for u in units if u not in done)))
        seq.append(ready[0]); done.add(ready[0])
    return seq


def remove_artifacts(mods):
    for m in mods:
        rel = m.replace('.', '/')
        for d in ('lib/lean', 'ir'):
            for f in glob.glob(os.path.join(BUILD, d, rel + '.*')):
                os.remove(f)


REAL = os.path.realpath(LEAN)
TICK = os.sysconf('SC_CLK_TCK')


def foreign_ticks():
    """CPU ticks used so far by each Lean or Lake process of another project
    (one not running in this Lean directory)."""
    out = {}
    for pid in os.listdir('/proc'):
        if not pid.isdigit():
            continue
        try:
            cmd = open(f'/proc/{pid}/cmdline', 'rb').read().replace(b'\0', b' ').decode()
            if not re.search(r'/bin/(lean|lake) ', cmd):
                continue
            if os.path.realpath(os.readlink(f'/proc/{pid}/cwd')).startswith(REAL) or LEAN in cmd:
                continue
            f = open(f'/proc/{pid}/stat').read().rsplit(')', 1)[1].split()
            out[pid] = int(f[11]) + int(f[12])  # utime + stime
        except OSError:
            continue
    return out


class Foreign:
    """CPU seconds used by other projects' Lean since the last reset."""
    def __init__(self):
        self.last = foreign_ticks(); self.used = 0

    def poll(self):
        now = foreign_ticks()
        self.used += sum(t - self.last.get(p, 0) for p, t in now.items())
        self.last = now
        return self.used / TICK


def wait_idle(limit, cpu):
    """Wait (at most `limit` seconds) until other projects' Lean used at
    most `cpu` CPU-seconds in 30 seconds; return the seconds waited."""
    t0 = time.monotonic()
    while time.monotonic() - t0 < limit:
        f = Foreign()
        time.sleep(30)
        if f.poll() <= cpu:
            break
    return round(time.monotonic() - t0)


def main():
    paths = tracked_modules()
    mod = {p: p[:-len('.lean')].replace('/', '.') for p in paths}
    units = {}
    for p in paths:
        units.setdefault(unit_of(p), []).append(mod[p])
    owner = {mod[p]: unit_of(p) for p in paths}
    deps = {u: set() for u in units}
    for p in paths:
        for m in imports(p):
            if m in owner and owner[m] != unit_of(p):
                deps[unit_of(p)].add(owner[m])
    seq = order(set(units), deps)
    todo = [u for u in seq if ONLY is None or u in ONLY]
    if os.environ.get('LEANTIME_DRY'):  # print the plan and stop
        for u in seq:
            print(f'{u:28} {len(units[u]):4} modules  after {sorted(deps[u])}')
        return

    rec = json.load(open(OUT)) if ONLY and os.path.exists(OUT) else {}
    rec.setdefault('units', {})
    rec['order'] = seq
    lock = open(os.path.expanduser('~/.qcert-build-1.lock'), 'w')
    fcntl.flock(lock, fcntl.LOCK_EX)
    rev = subprocess.run(['git', '-C', LEAN, 'rev-parse', '--short', 'HEAD'],
                         capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(['git', '-C', LEAN, 'status', '--short', '--untracked-files=no', '.'],
                           capture_output=True, text=True).stdout.split('\n')
    cpu = next((ln.split(':', 1)[1].strip() for ln in open('/proc/cpuinfo')
                if ln.startswith('model name')), platform.processor())
    mem = int(next(ln.split()[1] for ln in open('/proc/meminfo') if ln.startswith('MemTotal')))
    lean = subprocess.run(['lean', '--version'], capture_output=True, text=True, env=ENV).stdout.strip()
    info = dict(date=time.strftime('%Y-%m-%d %H:%M %z'), revision=rev,
                modified=[d.strip() for d in dirty if d.strip()], cpu=cpu,
                logical_cpus=os.cpu_count(), mem_gib=round(mem / 2**20, 1), lean=lean,
                modules=len(paths))
    if ONLY is None:
        rec['run'] = info
        for d in ('lib/lean', 'ir'):
            for f in glob.glob(os.path.join(BUILD, d, 'QCert*')):
                subprocess.run(['rm', '-rf', f], check=True)
    else:
        rec.setdefault('retimes', []).append(dict(info, units=todo))
    idle = int(os.environ.get('LEANTIME_IDLE', '0'))  # wait for an idle machine, at most this
    idle_cpu = float(os.environ.get('LEANTIME_IDLE_CPU', '3'))  # CPU-s per 30 s that count as idle
    for u in todo:
        waited = wait_idle(idle, idle_cpu) if idle else 0
        if ONLY is not None:
            remove_artifacts(units[u])
        foreign = Foreign()
        used = [0.0]
        stop = threading.Event()

        def sample():
            while not stop.wait(2):
                used[0] = foreign.poll()
        th = threading.Thread(target=sample, daemon=True); th.start()
        load0 = os.getloadavg()[0]
        t0 = time.monotonic()
        log = os.path.expanduser(os.path.join('~/leantime-logs', u + '.log'))
        os.makedirs(os.path.dirname(log), exist_ok=True)
        with open(log, 'w') as fh:
            rc = subprocess.run(['lake', 'build'] + units[u], cwd=LEAN, env=ENV,
                                stdout=fh, stderr=subprocess.STDOUT).returncode
        secs = time.monotonic() - t0
        stop.set(); th.join()
        fcpu = foreign.poll()
        failed = [m.group(0) for ln in open(log, encoding='utf-8', errors='replace')
                  if ln.startswith('✖') for m in [re.search(r'QCert[\w.]*', ln)] if m]
        rec['units'][u] = dict(seconds=round(secs, 2), rc=rc, modules=len(units[u]),
                               failed=failed, load_start=round(load0, 2),
                               foreign_cpu_s=round(fcpu, 1), waited_s=waited,
                               date=time.strftime('%Y-%m-%d %H:%M'))
        json.dump(rec, open(OUT, 'w'), indent=1)
        print(f'{u:28} {secs:9.2f} s  rc={rc}  modules={len(units[u])}  '
              f'foreign_cpu={fcpu:.1f} s  waited={waited} s  failed={failed}', flush=True)
    tot = sum(v['seconds'] for v in rec['units'].values())
    print(f'total {tot:.2f} s over {len(rec["units"])} units', flush=True)


main()

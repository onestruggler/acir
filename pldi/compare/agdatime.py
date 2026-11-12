"""Time a from-scratch typecheck of the Agda formalization, module by module.

    python3 agdatime.py ../.. agdatime.json            # clean, then every unit
    python3 agdatime.py ../.. agdatime.json U1,U2,...  # re-time those units only
    AGDATIME_DRY=1 python3 agdatime.py ../.. x.json    # print the plan only

Run in WSL.  The units are the rows of Table 1 and the shared library, as
loc.py maps them to folders; a unit's modules are its tracked .agda files.
Before the first unit the repository's interfaces (_build/) are removed;
the standard library's and EucDomain's are kept.  Each unit is checked by
one Agda process, through a root module that imports every module of the
unit, with --profile=modules: Agda reports the time it spent on each module
it checked, without its imports, and a row's time is the sum over its own
modules, wherever they were checked (a module of one row that another row
imports is checked in that row's process, and still counted in its own).
This is the measurement Table 1 has always reported (CLAUDE.md, 22 October
2026), now with every unit in a process of its own so that no heap grows
over the whole corpus.  Each process runs with +RTS -M<heap> (AGDATIME_HEAP,
default 16G).  For each unit the script also records the wall time, the
peak resident size, and the CPU seconds that Lean or Agda processes of
other projects used meanwhile (foreign_cpu_s), as leantime.py does.
"""
import glob, json, os, platform, re, subprocess, sys, threading, time

ROOT = os.path.abspath(sys.argv[1])
OUT = sys.argv[2]
ONLY = sys.argv[3].split(',') if len(sys.argv) > 3 else None
HEAP = os.environ.get('AGDATIME_HEAP', '16G')
LIBS = os.path.expanduser('~/acir-agdatime.libraries')
STDLIB = os.environ.get('AGDATIME_STDLIB', '/home/bones/agda-stdlib-2.4/standard-library.agda-lib')

# The row table of loc.py (its definitions, not its main).
here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, 'loc.py'), encoding='utf-8').read().split('def main')[0]
sys.argv = [sys.argv[0], ROOT] + sys.argv[2:]
exec(src)                                    # defines AGDA, ROWS, files, TRACKED

UNITS = ['(shared)'] + ROWS


def modname(path):
    rel = os.path.relpath(path, ROOT)[:-len('.agda')]
    return rel.replace(os.sep, '.')


def unit_modules():
    return {u: sorted(modname(f) for f in set(files(AGDA[u], '.agda'))) for u in UNITS}


REAL = os.path.realpath(ROOT)
TICK = os.sysconf('SC_CLK_TCK')


def foreign_ticks():
    """CPU ticks used so far by Lean, Lake or Agda processes of other
    projects (not running in this repository)."""
    out = {}
    for pid in os.listdir('/proc'):
        if not pid.isdigit():
            continue
        try:
            cmd = open(f'/proc/{pid}/cmdline', 'rb').read().replace(b'\0', b' ').decode()
            if not re.search(r'/(lean|lake|agda) ', cmd + ' '):
                continue
            if os.path.realpath(os.readlink(f'/proc/{pid}/cwd')).startswith(REAL) or ROOT in cmd:
                continue
            f = open(f'/proc/{pid}/stat').read().rsplit(')', 1)[1].split()
            out[pid] = int(f[11]) + int(f[12])
        except OSError:
            continue
    return out


class Foreign:
    def __init__(self):
        self.last = foreign_ticks(); self.used = 0

    def poll(self):
        now = foreign_ticks()
        self.used += sum(t - self.last.get(p, 0) for p, t in now.items())
        self.last = now
        return self.used / TICK


PROFILE = re.compile(r'^(\S+)\s+([\d,]+)ms\s*$')


def check(unit, mods):
    tag = re.sub(r'\W', '', unit) or 'shared'
    root = f'AgdaTime{tag}'
    path = os.path.join(ROOT, root + '.agda')
    with open(path, 'w', encoding='utf-8') as fh:
        fh.write(f'module {root} where\n')
        for m in mods:
            fh.write(f'import {m}\n')
    log = os.path.expanduser(os.path.join('~/agdatime-logs', tag + '.log'))
    os.makedirs(os.path.dirname(log), exist_ok=True)
    foreign = Foreign(); used = [0.0]; stop = threading.Event()

    def sample():
        while not stop.wait(2):
            used[0] = foreign.poll()
    th = threading.Thread(target=sample, daemon=True); th.start()
    t0 = time.monotonic()
    with open(log, 'w') as fh:
        rc = subprocess.run(['/usr/bin/time', '-f', 'maxrss %M KB', 'agda', f'--library-file={LIBS}',
                             '--profile=modules', root + '.agda', '+RTS', f'-M{HEAP}', '-RTS'],
                            cwd=ROOT, stdout=fh, stderr=subprocess.STDOUT).returncode
    secs = time.monotonic() - t0
    stop.set(); th.join()
    fcpu = foreign.poll()
    os.remove(path)
    for f in glob.glob(os.path.join(ROOT, '_build', '*', 'agda', root + '.agdai')):
        os.remove(f)
    prof, rss, errors = {}, None, []
    for ln in open(log, encoding='utf-8', errors='replace'):
        m = PROFILE.match(ln)
        if m and m.group(1) not in ('Total', 'Miscellaneous'):
            prof[m.group(1)] = int(m.group(2).replace(',', ''))
        elif ln.startswith('maxrss'):
            rss = int(ln.split()[1])
        elif ': error:' in ln:
            errors.append(ln.strip())
    return dict(seconds=round(secs, 2), rc=rc, max_rss_kb=rss, errors=errors[:5],
                foreign_cpu_s=round(fcpu, 1), date=time.strftime('%Y-%m-%d %H:%M')), prof


def main():
    with open(LIBS, 'w') as fh:
        fh.write(STDLIB + '\n' + os.path.join(ROOT, 'EucDomain', 'EucDomain.agda-lib') + '\n')
    mods = unit_modules()
    owner = {m: u for u, ms in mods.items() for m in ms}
    todo = [u for u in UNITS if ONLY is None or u in ONLY]
    if os.environ.get('AGDATIME_DRY'):
        for u in UNITS:
            print(f'{u:18} {len(mods[u]):5} modules')
        return
    rec = json.load(open(OUT)) if ONLY and os.path.exists(OUT) else {}
    rec.setdefault('units', {}); rec.setdefault('modules', {})
    rev = subprocess.run(['git', '-C', ROOT, 'rev-parse', '--short', 'HEAD'],
                         capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(['git', '-C', ROOT, 'status', '--short', '--untracked-files=no', '--', '*.agda'],
                           capture_output=True, text=True).stdout.split('\n')
    cpu = next((ln.split(':', 1)[1].strip() for ln in open('/proc/cpuinfo')
                if ln.startswith('model name')), platform.processor())
    mem = int(next(ln.split()[1] for ln in open('/proc/meminfo') if ln.startswith('MemTotal')))
    agda = subprocess.run(['agda', '--version'], capture_output=True, text=True).stdout.split('\n')[0]
    info = dict(date=time.strftime('%Y-%m-%d %H:%M %z'), revision=rev,
                modified=[d.strip() for d in dirty if d.strip()], cpu=cpu,
                logical_cpus=os.cpu_count(), mem_gib=round(mem / 2**20, 1), agda=agda,
                rts=f'-M{HEAP}', modules=sum(len(v) for v in mods.values()))
    if ONLY is None:
        rec['run'] = info
        subprocess.run(['rm', '-rf', os.path.join(ROOT, '_build')], check=True)
    else:
        rec.setdefault('retimes', []).append(dict(info, units=todo))
        for u in todo:          # its modules' interfaces, so that they are checked again
            for m in mods[u]:
                for f in glob.glob(os.path.join(ROOT, '_build', '*', 'agda',
                                                m.replace('.', '/') + '.agdai')):
                    os.remove(f)
    for u in todo:
        # A module that does not typecheck (a stale one that nothing
        # imports) is left out with whatever imports it, and the unit
        # is checked again; the modules checked before the failure keep
        # the times of the failed attempt.
        listed, excluded, wall = list(mods[u]), [], 0.0
        for attempt in range(20):
            res, prof = check(u, listed)
            wall += res['seconds']
            for m, ms in prof.items():
                rec['modules'][m] = dict(ms=ms, unit=owner.get(m, '(other)'), checked_in=u)
            bad = [modname(e.split(':', 1)[0]) for e in res['errors'] if e.startswith('/')]
            if res['rc'] == 0 or not bad:
                break
            drop = {b for b in bad if b in listed}
            if not drop:      # the failing module is imported by listed ones
                drop = {m for m in listed
                        if any(re.search(r'^\s*(open\s+)?import\s+' + re.escape(b) + r'(\s|$)',
                                         open(os.path.join(ROOT, m.replace('.', '/') + '.agda'),
                                              encoding='utf-8').read(), re.M) for b in bad)}
            if not drop:
                break
            excluded += sorted(drop)
            listed = [m for m in listed if m not in drop]
            print(f'{u}: leaving out {sorted(drop)}', flush=True)
        res['seconds'], res['attempts'], res['excluded'] = round(wall, 2), attempt + 1, excluded
        rec['units'][u] = res
        # A row's time: the profiled time of its own modules.
        for v in UNITS:
            own = [rec['modules'][m]['ms'] for m in mods[v] if m in rec['modules']]
            rec.setdefault('rows', {})[v] = dict(seconds=round(sum(own) / 1000, 2),
                                                 modules=len(mods[v]), profiled=len(own))
        json.dump(rec, open(OUT, 'w'), indent=1)
        print(f"{u:18} {res['seconds']:9.2f} s wall  rc={res['rc']}  rss={res['max_rss_kb']} KB  "
              f"own={rec['rows'][u]['seconds']} s ({rec['rows'][u]['profiled']}/{len(mods[u])})  "
              f"foreign_cpu={res['foreign_cpu_s']} s  errors={res['errors'][:1]}", flush=True)
        if res['rc'] != 0:
            print('stopping: the unit failed; see ~/agdatime-logs', flush=True)
            break
    tot = sum(rec['rows'][u]['seconds'] for u in ROWS)
    print(f'rows total {tot:.2f} s', flush=True)


main()

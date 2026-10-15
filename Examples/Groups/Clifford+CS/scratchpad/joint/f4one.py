# One (F4) item, with timing: python3 f4one.py K0 CS1
import sys, time, resource
import derivn, box, boxsym, boxdash, f4
derivn.QUIET = True


def parse(s):
    if s == 'I': return ('I',)
    return (s.rstrip('0123456789'), int(s[len(s.rstrip('0123456789')):]))


L = box.build({}); boxsym.build(L); boxsym.build_perms(L); boxdash.build(L)
for a, b in zip(sys.argv[1::2], sys.argv[2::2]):
    t0 = time.time()
    try:
        f4.f4(L, parse(a), parse(b)); r = 'ok'
    except Exception as e:
        r = 'FAIL ' + str(e)[:200]
    print(a, b, r, f'{time.time() - t0:.1f}s', resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024, 'MB')

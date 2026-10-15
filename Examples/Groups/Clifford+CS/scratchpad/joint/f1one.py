# One (F1) item with an alarm that prints where it is: python3 f1one.py NAME [SECONDS]
import sys, signal, traceback, time
import derivn, box, boxsym, boxdash, boxbox, f0, f1, f1rules, boxtoff, boxck, f5
derivn.QUIET = True


def alarm(sig, frame):
    print('--- alarm; current word:', flush=True)
    traceback.print_stack(frame, limit=25)
    raise TimeoutError()


L = box.build({})
f5.build(L); boxsym.build(L); boxsym.build_perms(L); boxdash.build(L); boxbox.build(L); f0.build(L)
boxtoff.build(L); boxck.build(L)
name = sys.argv[1]
secs = int(sys.argv[2]) if len(sys.argv) > 2 else 300
signal.signal(signal.SIGALRM, alarm)
signal.alarm(secs)
t0 = time.time()
for n, l, r in f1rules.items():
    if n == name:
        rule, o = name.split('@')
        ar = [a for (nn, a, _, _) in f1rules.RULES if nn == rule][0]
        idle = f1.IDLE3[int(o)] if ar == 3 else None
        try:
            f1.item(L, name, l, r, idle)
            print('ok', name, f'{time.time() - t0:.1f}s')
        except Exception as e:
            print('FAIL', name, str(e)[:400])

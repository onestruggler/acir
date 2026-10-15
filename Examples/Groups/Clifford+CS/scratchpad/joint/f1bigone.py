# One f1big item with an alarm: python3 f1bigone.py NAME SECONDS [box]
import sys, signal, traceback, time
import derivn, box, boxsym, boxdash, boxbox, f0, f1, f1big, boxtoff, boxck, f5
derivn.QUIET = True
CUR = {}


def alarm(sig, frame):
    print('--- alarm', flush=True)
    traceback.print_stack(frame, limit=30)
    d = frame.f_locals.get('d')
    while d is None and frame is not None:
        frame = frame.f_back
        d = frame.f_locals.get('d') if frame else None
    if d is not None:
        print('word', len(d.cur), derivn.show(d.cur)[:3000], flush=True)
    raise TimeoutError()


if len(sys.argv) > 3 and sys.argv[3] == 'box':
    f1big.TOFF_BOX = True
L = box.build({})
f5.build(L); boxsym.build(L); boxsym.build_perms(L); boxdash.build(L); boxbox.build(L); f0.build(L)
boxtoff.build(L); boxck.build(L)
signal.signal(signal.SIGALRM, alarm)
signal.alarm(int(sys.argv[2]))
t0 = time.time()
f1big.build(L, only=[sys.argv[1]])
print('time', f'{time.time() - t0:.0f}s')

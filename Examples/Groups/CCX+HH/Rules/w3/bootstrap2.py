"""Continue bootstrap.py from its lemmas with more targets and a larger
table.

    python3 -B bootstrap2.py limit "target" ...
"""
import sys, time, pickle
import bootstrap as B
import ptargets as TG

if __name__ == '__main__':
    limit = int(sys.argv[1])
    done = pickle.load(open('bootstrap.pkl', 'rb'))
    lemmas = [TG.gatesof(t) for t in done]
    todo = sys.argv[2:]
    t0 = time.time()
    progress = True
    while progress:
        progress = False
        for t in list(todo):
            if B.attempt(t, lemmas, limit):
                lemmas.append(TG.gatesof(t)); done.append(t); todo.remove(t)
                progress = True
                print(f'  + {t}   [{round(time.time() - t0)} s]', flush=True)
            else:
                print(f'  - {t}   [{round(time.time() - t0)} s]', flush=True)
    pickle.dump(done, open('bootstrap.pkl', 'wb'))
    print('open', todo)

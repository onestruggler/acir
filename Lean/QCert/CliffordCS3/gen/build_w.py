import pickle, sys, time
sys.setrecursionlimit(100000)
import groups3
t = time.time()
W = groups3.build(verbose=True)
print('built %.1fs' % (time.time() - t), 'eqs', len(W.T.eqs), flush=True)
with open('w3.pkl', 'wb') as f:
    pickle.dump(W, f, protocol=pickle.HIGHEST_PROTOCOL)
print('pickled %.1fs' % (time.time() - t), flush=True)

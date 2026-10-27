import pickle, os
from fig6 import *
done = {}
for fn in os.listdir('.'):
    if fn.startswith('res6_') and fn.endswith('.pkl'):
        for k, v in pickle.load(open(fn,'rb')).items():
            if v is not None: done[k] = v
print(len(done), 'proven')
pickle.dump(done, open('proven_dec.pkl','wb'))

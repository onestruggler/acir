"""Persistent store of micro relators with their derivations.
DER[rid] = (u, v, steps) for derived relators (relator = u + rev v); None for base."""
import pickle
from cbfs import Relators, CSearch
from model import LET

class Store:
    def __init__(self, rels, names, der):
        self.R = Relators()
        for r, n in zip(rels, names):
            self.R.add(r, n)
        self.der = der
    def save(self, fn):
        pickle.dump((self.R.rels, self.R.names, self.der), open(fn, "wb"))
    @staticmethod
    def load(fn):
        rels, names, der = pickle.load(open(fn, "rb"))
        return Store(rels, names, der)
    def search(self, maxlhs=10):
        return CSearch(len(LET), maxlhs, self.R)
    def add(self, u, v, steps, name):
        u = tuple(u); v = tuple(v)
        assert self.R.replay(u, steps) == v, name
        rid = self.R.add(u + tuple(reversed(v)), name)
        self.der.append((u, v, steps))
        assert len(self.der) == len(self.R.rels)
        return rid
    def find(self, name):
        return self.R.names.index(name)

"""Assembling derivations from known relators (rotation steps)."""
from model import IDX, LET

class Asm:
    def __init__(self, store, w):
        self.S = store
        self.w = tuple(w)
        self.steps = []
        self.inv = {x: store.find(f"inv_{LET[x]}") for x in range(len(LET))}
    def _do(self, st):
        self.w = self.S.R.apply(self.w, st)
        self.steps.append(st)
    def fwd(self, pos, rid):
        """replace u by v, where relator rid was derived as u -> v"""
        u, v, _ = self.S.der[rid]
        self._do((pos, rid, 0, len(u), False))
    def bwd(self, pos, rid):
        u, v, _ = self.S.der[rid]
        self._do((pos, rid, 0, len(v), True))
    def ins(self, pos, word):
        """insert word + rev word at pos (pairs of involutions)"""
        for k, x in enumerate(word):
            self._do((pos + k, self.inv[x], 0, 0, False))
    def cancel(self, pos, word):
        """remove word + rev word at pos"""
        for k in range(len(word) - 1, -1, -1):
            x = word[k]
            assert self.w[pos + k] == x and self.w[pos + k + 1] == x
            self._do((pos + k, self.inv[x], 0, 2, False))
    def sub(self, pos, steps):
        for (i, rid, rot, cut, rv) in steps:
            self._do((i + pos, rid, rot, cut, rv))

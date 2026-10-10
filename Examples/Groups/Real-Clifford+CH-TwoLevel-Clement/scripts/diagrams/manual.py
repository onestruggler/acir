"""Hand-written derivation chains: explicit steps, checked step by step."""
from deriv import check_equiv, canonical, rev, same

class Chain:
    def __init__(self, D, start):
        self.D = D
        self.cur = list(start)
        self.start = list(start)
        self.steps = []
    def perm(self, new):
        new = list(new)
        assert check_equiv(self.cur, new, self.D.m), ('bad perm', self.cur, new)
        self.steps.append(('perm', new))
        self.cur = new
        return self
    def rw(self, name, i):
        l, r = self.D.lib.byname[name]
        assert self.cur[i:i + len(l)] == l, ('bad rw', name, i, self.cur[i:i + len(l)], l)
        new = self.cur[:i] + r + self.cur[i + len(l):]
        self.steps.append(('rw', i, name, new))
        self.cur = new
        return self
    def find(self, pattern, start=0):
        n = len(pattern)
        for i in range(start, len(self.cur) - n + 1):
            if self.cur[i:i + n] == list(pattern):
                return i
        raise KeyError(pattern)
    def rw_at(self, name, start=0):
        l, r = self.D.lib.byname[name]
        return self.rw(name, self.find(l, start))
    def insert(self, word, i):
        """Insert an involution pair x x for each letter, nested: word w becomes
        w rev(w) at position i (one insertion per letter)."""
        for k, g in enumerate(word):
            nm = self.D.pair_name(g)
            self.rw('(sym⁼ %s)' % nm, i + k)
        return self
    def cancel(self):
        """Cancel equal letters separated only by letters commuting with
        them, repeatedly (a perm brings them together)."""
        from deriv import comm
        while True:
            done = True
            for i in range(len(self.cur) - 1):
                x = self.cur[i]
                for j in range(i + 1, len(self.cur)):
                    if self.cur[j] == x:
                        if j > i + 1:
                            new = self.cur[:i + 1] + [x] + self.cur[i + 1:j] + self.cur[j + 1:]
                            self.perm(new)
                        self.rw(self.D.pair_name(x), i)
                        done = False
                        break
                    if not comm(self.cur[j], x):
                        break
                if not done:
                    break
            if done:
                return self
    def finish(self, name, goal, add=True):
        goal = list(goal)
        self.perm(goal)
        assert same(self.start, goal, self.D.m)
        self.D.derived.append((name, self.start, goal, self.steps))
        if add:
            self.D.lib.add(name, self.start, goal)
        return self.steps

def pair_name(g):
    if g[0] == 'Z':
        return 'a1-%d' % g[1]
    if g[0] == 'X':
        return 'a2-%d%d' % (g[1], g[2])
    return 'a3-%d%d' % (g[1], g[2])

"""Agda for Clifford+CS.Engine, from the output of kbc runs.

Each rule a derivation needs, and each wanted equation, becomes an Eqn:
`derive L R steps refl`, the steps naming the rules they use; an axiom
becomes its Agda term.  A run may be mirrored — its targets are the
mirror images of the wanted equations, and its derivations are replayed
with the wires exchanged — or printed expanded (z ↦ C C)."""


def parse(path):
    """(rules, targets) of a kbc output: rule id ↦ (lhs, rhs, body),
    target name ↦ (lhs, rhs, steps)."""
    rules, targets = {}, {}
    for line in open(path, encoding='utf-8'):
        p = line.split()
        if not p or p[0] not in ('rule', 'target'):
            continue
        i = p.index(':')
        j = p.index('=', i)
        lhs = [x for x in p[i + 1:j] if x != '.']
        rest = p[j + 1:]
        m = next(n for n, x in enumerate(rest) if x in ('axiom', 'steps'))
        rhs = [x for x in rest[:m] if x != '.']
        tail = rest[m:]
        if tail[0] == 'axiom':
            body = ('axiom', tail[1], tail[2] == '1')
        else:
            nums = list(map(int, tail[1:]))
            body = ('steps', [tuple(nums[q:q + 3]) for q in range(0, len(nums), 3)])
        if p[0] == 'rule':
            rules[int(p[1])] = (lhs, rhs, body)
        else:
            targets[p[1]] = (lhs, rhs, body[1])
    return rules, targets


class Emitter:
    PER_LINE = 6

    def __init__(self, letter, axterm, axwords, mirror=None, expand=None):
        self.letter = letter          # letter ↦ Agda name
        self.axterm = axterm          # axiom name ↦ Agda term, an Eqn for axwords' orientation
        self.axwords = axwords        # axiom name ↦ (lhs, rhs)
        self.mir = mirror or {}       # letter ↦ its mirror image
        self.expand = expand or {}    # letter ↦ the letters it is printed as
        self.runs = {}                # tag ↦ (rules, targets, mirrored)
        self.need = set()             # (tag, rule id, mirrored)

    def load(self, tag, path, mirrored):
        rules, targets = parse(path)
        self.runs[tag] = (rules, targets, mirrored)

    def mw(self, w):
        return [self.mir.get(a, a) for a in w]

    def rule(self, key):
        tag, rid, m = key
        l, r, body = self.runs[tag][0][rid]
        return (self.mw(l), self.mw(r), body) if m else (l, r, body)

    def rname(self, key):
        tag, rid, m = key
        return '%s%s-%d' % ('m' if m else 'r', tag, rid)

    def axioms_used(self):
        return {self.rule(k)[2][1] for k in self.need if self.rule(k)[2][0] == 'axiom'}

    def visit(self, tag, steps, m):
        for (_, rid, _) in steps:
            key = (tag, rid, m)
            if key not in self.need:
                self.need.add(key)
                body = self.runs[tag][0][rid][2]
                if body[0] == 'steps':
                    self.visit(tag, body[1], m)

    def choose(self, name, lhs, rhs):
        """A run proving lhs = rhs, and whether it is mirrored."""
        for tag, (rules, targets, mirrored) in self.runs.items():
            if name in targets:
                tl, tr, st = targets[name]
                want = (self.mw(lhs), self.mw(rhs)) if mirrored else (lhs, rhs)
                if (tl, tr) == want:
                    return tag, mirrored, st
        return None

    def lst(self, w):
        if not w:
            return '[]'
        return ' ∷ '.join(self.letter[b] for a in w for b in self.expand.get(a, a)) + ' ∷ []'

    def epos(self, w, pos):
        return sum(len(self.expand.get(a, a)) for a in w[:pos])

    def chain(self, start, steps, tag, m):
        w = list(start)
        terms = []
        for (pos, rid, d) in steps:
            l, r, _ = self.rule((tag, rid, m))
            if d < 0:
                l, r = r, l
            assert w[pos:pos + len(l)] == l, (start, pos, rid, d)
            terms.append('%s %d %s' % ('rw' if d > 0 else 'rw⁻', self.epos(w, pos), self.rname((tag, rid, m))))
            w = w[:pos] + r + w[pos + len(l):]
        return w, terms

    def axiom_term(self, l, r, name, m):
        if not m:
            al, ar = self.axwords[name]
            assert (al, ar) in ((l, r), (r, l)), (name, l, r)
            return self.axterm[name] if (al, ar) == (l, r) else 'sym⁼ (%s)' % self.axterm[name]
        for n, (al, ar) in self.axwords.items():
            if (al, ar) == (l, r):
                return self.axterm[n]
            if (al, ar) == (r, l):
                return 'sym⁼ (%s)' % self.axterm[n]
        raise KeyError('no mirrored axiom for %s' % name)

    def derive_text(self, nm, L, R, terms, ind):
        if terms:
            lines = [' ∷ '.join(terms[i:i + self.PER_LINE]) for i in range(0, len(terms), self.PER_LINE)]
            steps = '(' + (' ∷\n' + ind + '     ').join(lines) + ' ∷ [])'
        else:
            steps = '[]'
        return ('%s%s : Eqn\n%s%s = derive (%s)\n%s  (%s)\n%s  %s refl\n'
                % (ind, nm, ind, nm, self.lst(L), ind, self.lst(R), ind, steps))

    def emit_rules(self):
        out = []
        for key in sorted(self.need, key=lambda k: (k[0], k[2], k[1])):
            l, r, body = self.rule(key)
            nm = self.rname(key)
            if body[0] == 'axiom':
                out.append('  %s : Eqn\n  %s = %s\n' % (nm, nm, self.axiom_term(l, r, body[1], key[2])))
            else:
                end, terms = self.chain(l, body[1], key[0], key[2])
                assert end == r
                out.append(self.derive_text(nm, l, r, terms, '  '))
        return ('private\n' + '\n'.join(out) + '\n') if out else ''

    def emit_target(self, kname, aname, L, R):
        """The definition of aname : L ≡ R, or None if no run proves it."""
        ch = self.choose(kname, L, R)
        if ch is None:
            return None
        tag, m, st = ch
        self.visit(tag, st, m)
        end, terms = self.chain(L, st, tag, m)
        assert end == R, aname
        return self.derive_text(aname, L, R, terms, '')

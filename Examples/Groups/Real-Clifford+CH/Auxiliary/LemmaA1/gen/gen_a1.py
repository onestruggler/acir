# Generate the segment-chain derivations of Lemma A.1 (Appendix A.2).
#
# A word is a string of space-separated letters: Za = (−1)[a], Xab, Hab;
# an index is one character, a letter (a variable) or a digit (a literal).
# A lemma is (name, indices, distinct pairs, lhs, rhs, steps); a step is
# (old, new, proof) or (old, new, proof, position).  The script checks
# that each old segment occurs (at the position, or first), that old and
# new denote the same matrix under a random assignment of distinct
# values, and that the chain ends at rhs; then it prints the Agda.
import math, random, sys, itertools
if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8')

R2 = math.sqrt(2)
NN = 10

def ident():
    return [[1.0 if i == j else 0.0 for j in range(NN)] for i in range(NN)]
def mul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(NN)) for j in range(NN)] for i in range(NN)]
def gen(g, env):
    M = ident()
    if g[0] == 'Z':
        a = env[g[1]]; M[a][a] = -1.0
    elif g[0] == 'X':
        a, b = env[g[1]], env[g[2]]
        M[a][a] = M[b][b] = 0.0; M[a][b] = M[b][a] = 1.0
    else:
        a, b = env[g[1]], env[g[2]]
        M[a][a] = 1 / R2; M[a][b] = 1 / R2; M[b][a] = 1 / R2; M[b][b] = -1 / R2
    return M
def sem(w, env):
    M = ident()
    for g in w: M = mul(M, gen(g, env))
    return M
def same(A, B):
    return all(abs(A[i][j] - B[i][j]) < 1e-9 for i in range(NN) for j in range(NN))

def parse(s):
    return [t for t in s.split()] if s.strip() else []

SUB = '₀₁₂₃₄₅₆₇₈₉'
def idx(c):
    return SUB[int(c)] if c.isdigit() else c
def letter(t):
    if t[0] == 'Z': return '−1 ' + idx(t[1])
    return '%s %s %s' % (t[0], idx(t[1]), idx(t[2]))
def alist(w):
    return ' ∷ '.join(letter(t) for t in w) + (' ∷ []' if w else '[]')
def aword(w):
    return ' • '.join(letter(t) for t in w) if w else 'ε'

def envs(indices):
    for _ in range(4):
        vals = random.sample(range(NN), len(indices))
        yield dict(zip(indices, vals))

def chain(name, indices, lhs, rhs, steps):
    line = parse(lhs)
    target = parse(rhs)
    allidx = sorted(set(c for t in line + target for c in t[1:]) | set(indices))
    out = []
    for st in steps:
        old, new, proof = parse(st[0]), parse(st[1]), st[2]
        pos = st[3] if len(st) > 3 else None
        if pos is None:
            pos = next((k for k in range(len(line) - len(old) + 1) if line[k:k + len(old)] == old), None)
            if pos is None:
                raise SystemExit('%s: segment %s not in %s' % (name, st[0], ' '.join(line)))
        elif line[pos:pos + len(old)] != old:
            raise SystemExit('%s: segment %s not at %d in %s' % (name, st[0], pos, ' '.join(line)))
        ids = sorted(set(c for t in old + new for c in t[1:]) | set(allidx))
        for env in envs(ids):
            if not same(sem(old, env), sem(new, env)):
                raise SystemExit('%s: unsound step %s => %s' % (name, st[0], st[1]))
        out.append('at %d %d (%s) (%s)' % (pos, len(old), alist(new), proof))
        line = line[:pos] + new + line[pos + len(old):]
    if line != target:
        raise SystemExit('%s: ends at %s, not %s' % (name, ' '.join(line), rhs))
    return out

def emit(name, sig, args, lhs, rhs, steps, comment=None):
    steps_out = chain(name, [], lhs, rhs, steps)
    s = ''
    if comment:
        s += ''.join('-- %s\n' % c for c in comment)
    s += '%s : %s\n' % (name, sig)
    s += '%s %s =\n  run {%s} {%s}\n' % (name, args, alist(parse(lhs)), alist(parse(rhs)))
    s += ''.join('    (%s ▸\n' % o for o in steps_out)
    s += '     done' + ')' * len(steps_out) + '\n\n'
    return s

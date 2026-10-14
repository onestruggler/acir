# What Lemma 8.8 asks at n = 4: every rule of P' (Auxiliary/Fragment,
# Auxiliary/Rules) decoded at N = 16, both sides as words of placed
# gadgets (dec.py), checked semantically, and printed so that the core
# identities can be read off.  pp3 is the phase gadget of the pair 3, 4;
# a prime is the flipped gadget (the inverse pair, the other rotation);
# rot/ki likewise.
import sys
from random import Random
from dec import Dec, code, layout

n = 4; N = 2 ** n
d = Dec(n)
rng = Random(1)

def nm(key):
    kind, a, flip = key
    return f"{kind}{a}" + ("'" if flip else "")

def show(keys): return ' '.join(nm(k) for k in keys) if keys else 'eps'

def check(name, lhs, rhs):
    ok = d.mat(lhs) == d.mat(rhs)
    print(f"{'ok ' if ok else 'BAD'} {name}")
    print(f"      {show(lhs)}")
    print(f"   =  {show(rhs)}")
    return ok

def pp(a, b): return d.pp(a, b)
def px(c, a, b): return d.px(c, a, b)
def dx(a, b, c, e): return d.dx(a, b, c, e)
def ki(a, b, s): return d.ki(a, b, s)

def distinct(k, avoid=()):
    while True:
        xs = rng.sample(range(N), k)
        if all(x not in avoid for x in xs): return xs

bad = 0
def rule(name, lhs, rhs):
    global bad
    if not check(name, lhs, rhs): bad += 1

# ---------------------------------------------------------------- fragment
a, b, c, e = sorted(distinct(4))
rule('pp-ord', pp(a, b) * 4, [])
rule('pp-comm', pp(a, b) + pp(c, e), pp(c, e) + pp(a, b))
rule('pp-comm (shared index)', pp(a, b) + pp(b, c), pp(b, c) + pp(a, b))
rule('pp-tele', pp(a, b) + pp(b, c), pp(a, c))
rule('pp-tele (down)', pp(c, b) + pp(b, a), pp(c, a))
a = rng.randrange(N - 1)
rule(f'px-sq a={a}', pp(a, a + 1) * 2, px(a, a, a + 1) * 2)
a = rng.randrange(N - 2)
rule(f'px-braid a={a}', px(a, a, a + 1) + px(a + 1, a + 1, a + 2) + px(a, a, a + 1),
     px(a + 1, a + 1, a + 2) + px(a, a, a + 1) + px(a + 1, a + 1, a + 2))
a = rng.randrange(N - 3); c = rng.randrange(a + 2, N)
rule(f'px-shrink1 a={a} c={c}', px(a, a, c), px(a + 1, a, a + 1) + px(a + 1, a + 1, c) + px(a, a, a + 1))
rule(f'px-shrink2 a={a} c={c}', px(c, a, c), px(a + 1, a, a + 1) + px(c, a + 1, c) + px(a, a, a + 1))
rule(f'px-shrink3 a={a} c={c}', px(a, a, c), px(c - 1, c - 1, c) + px(a, a, c - 1) + px(c, c - 1, c))
rule(f'px-shrink4 a={a} c={c}', px(c, a, c), px(c - 1, c - 1, c) + px(c - 1, a, c - 1) + px(c, c - 1, c))
a = rng.randrange(N - 1)
rule(f'px-inv a={a}', px(a, a, a + 1) + px(a + 1, a, a + 1), [])
a, b = sorted(distinct(2)); c = distinct(1, avoid=(a, b))[0]
rule(f'px-sign c={c} a={a} b={b}', px(c, a, b), pp(c, a) * 2 + px(a, a, b))
rule(f'px-sign c=b a={a} b={b}', px(b, a, b), pp(b, a) * 2 + px(a, a, b))
a = rng.randrange(N - 1); c = distinct(1, avoid=(a, a + 1))[0]
rule(f'px-conj a={a} c={c}', pp(a + 1, c) + px(a, a, a + 1), px(a, a, a + 1) + pp(a, c))
rule(f'px-conj2 a={a}', pp(a, a + 1) + px(a, a, a + 1), px(a, a, a + 1) + pp(a + 1, a))
a = rng.randrange(N - 4); b = rng.randrange(a + 2, N - 1)
rule(f'px-comm a={a} b={b}', px(a, a, a + 1) + px(b, b, b + 1), px(b, b, b + 1) + px(a, a, a + 1))
a, b = sorted(distinct(2)); c, e = sorted(distinct(2))
rule('dx-split', dx(a, b, c, e), px(a, a, b) + px(b, c, e))

# ------------------------------------------------------------------ hybrid
a, b = sorted(distinct(2)); s, t = distinct(2, avoid=(a, b))
rule(f'ki-sink a={a} b={b} s={s} t={t}', ki(a, b, s) + pp(s, t), ki(a, b, t))
x = distinct(1, avoid=(a, b, s))[0]
rule(f'ki-pp a={a} b={b} s={s} x={x}', pp(x, s) + ki(a, b, s), ki(a, b, s) + pp(x, s))
x, y = sorted(distinct(2, avoid=(a, b, s)))
rule(f'ki-px a={a} b={b} s={s} x={x} y={y}', px(s, x, y) + ki(a, b, s), ki(a, b, s) + px(s, x, y))
c, e = sorted(distinct(2, avoid=(a, b, s)))
rule(f'ki-ki a={a} b={b} c={c} e={e} s={s}', ki(a, b, s) + ki(c, e, s), ki(c, e, s) + ki(a, b, s))
j, k, l = sorted(distinct(3)); s = distinct(1, avoid=(j, k, l))[0]
rule(f'ki-swap j={j} k={k} l={l} s={s}', ki(k, l, s) + px(s, j, k), px(s, j, k) + ki(j, l, s))
rule(f"ki-swap' j={j} k={k} l={l} s={s}", ki(j, l, s) + px(s, k, l), px(s, k, l) + ki(j, k, s))
a, b = sorted(distinct(2)); s = distinct(1, avoid=(a, b))[0]
rule(f'ki-x a={a} b={b} s={s}', ki(a, b, s) + pp(b, s) * 2, px(s, a, b) + ki(a, b, s))
rule(f'ki-16 a={a} b={b} s={s}', ki(a, b, s) + pp(b, s) * 3, pp(b, s) + ki(a, b, s) + pp(b, s) + ki(a, b, s))
rule(f'ki-ii a={a} b={b} s={s}', ki(a, b, s) + pp(a, s) + pp(b, s), pp(a, s) + pp(b, s) + ki(a, b, s))
rule(f'ki-sq a={a} b={b} s={s}', ki(a, b, s) * 2 + pp(a, s) + pp(b, s), [])
j, k, l, m = sorted(distinct(4)); s = distinct(1, avoid=(j, k, l, m))[0]
rule(f'ki-yb j={j} k={k} l={l} m={m} s={s}', ki(j, k, s) + ki(l, m, s) + ki(j, l, s) + ki(k, m, s),
     ki(j, l, s) + ki(k, m, s) + ki(j, k, s) + ki(l, m, s))

# the consecutive instances, where the gadgets are bare
print('\n--- consecutive instances (bare gadgets) ---')
for a in range(N - 1):
    t, x = layout(n, a)
    print(f'pair {a:2d},{a + 1:2d}: codes {code(n, a)} {code(n, a + 1)}  target {t}  colours {x}')
print('bad:', bad)

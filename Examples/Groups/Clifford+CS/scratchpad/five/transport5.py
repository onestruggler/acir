# Transport on five wires: the controlled functor lambda^1_4 (target wire 4,
# domain wires 0 1 2 3) and, for every axiom instance of the four-wire
# theory (Syntactics' rules at every placement, the structural rules
# comm1, comm2, omega-up), the five-wire equation between the
# lambda-images of its two sides, derived from the joint paper's F-items:
#
#   * both images equal: nothing to do;
#   * images on at most four wires: one window;
#   * a commutation with a CS: the F2 item of the two gates;
#   * a rule with a CS at placement j: its F1 item renamed by a permutation
#     of the domain wires, with the borrowed wires of each doubly
#     controlled S put back in order by F0 (F0d for the inverse).
#
# Rules whose F1 item the joint run does not derive are reported as
# missing: rel-269 and rel-272 if the de-borrowing has not run; ck-tct,
# whose variant ck-tct' alone the de-borrowing derives, and lf, hyb-sq,
# hyb-yb, whose controlled versions are five-wire rules.
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(os.path.dirname(HERE), 'joint'))
import lower5 as L5
from prim5 import Prim, norm1, show, gsupp, is_box
import abel

T = 4
DOM = (0, 1, 2, 3)

# --------------------------------------------------------- generators
# a generator of Circuit 4: ('I',), ('S', w), ('K', w), ('CS', w) (wires w, w+1)
def gens_of_abel(word):
    out = []
    for g in word:
        if g[0] == 'iI': out.append(('I',))
        elif g[0] in ('S', 'K'): out.append((g[0], g[1]))
        elif g[0] == 'CS':
            a, b = sorted(g[1:]); assert b == a + 1, g; out.append(('CS', a))
        else: raise ValueError(g)
    return out

def up(gs, j):
    return [g if g[0] == 'I' else (g[0], g[1] + j) for g in gs]

def lam1(g):
    k = g[0]
    if k == 'I': return ('S', T)
    if k == 'S': return norm1(('CS', g[1], T))
    if k == 'K': return ('CK', T, g[1])
    if k == 'CS':
        x, y = g[1], g[1] + 1
        u, A = [w for w in DOM if w not in (x, y)]
        return ('SBOX', u, x, (T, y), A)
    raise ValueError(g)

def lam(gs): return [lam1(g) for g in gs]

# --------------------------------------------------------- the rules
ARITY = dict(abel.WIDTH)
RULES = {name: (ARITY[name], gens_of_abel(l), gens_of_abel(r)) for name, (l, r) in abel.RULES.items()}

def ck_tct():
    import mac5
    def gw(letters):
        out = []
        for g in letters:
            for name, s in mac5.word_of(mac5.mac_tree(g)):
                out.append(('I',) if name == 'iI' else (name, s))
        return out
    A = [('X', 0), ('CK', 0, 1), ('X', 0)]
    B = [('TOFF', 1, 2, 3), ('CS', 0, 1), ('TOFF', 1, 2, 3)]
    return gw(A + B), gw(B + A)
RULES['ck-tct'] = (4,) + ck_tct()

F1 = {name: f'F1 {name}' for name in RULES}
# The rules whose lambda-images the joint run does not derive; the
# de-borrowing (joint/deb_all.py, load5.py --deb) derives rel-269 and
# rel-272, and ck-tct' (Toff^-1 in its second Toffoli) but not ck-tct.
def missing():
    return {r for r in ('rel-269', 'rel-272', 'ck-tct') if F1[r] not in L5.JOINT}

# --------------------------------------------------------- instances
def gens_upto(m):
    """the generators of Circuit m, as wire-level tuples."""
    out = [('I',)]
    for w in range(m): out += [('S', w), ('K', w)]
    for w in range(m - 1): out.append(('CS', w))
    return out

def instances():
    """(key, lhs gens, rhs gens) for every axiom instance at width 4."""
    out = []
    for name, (k, l, r) in RULES.items():
        for j in range(0, 4 - k + 1):
            out.append((('rule', name, j), up(l, j), up(r, j)))
    for j in range(4):                      # comm1 at width 4 - j, lifted j
        m = 4 - j - 1
        for h in ('S', 'K'):
            for g in gens_upto(m):
                gg = up([g], j + 1)[0]
                out.append((('comm1', h, g, j), [gg, (h, j)], [(h, j), gg]))
    for j in range(3):                      # comm2 at width 4 - j, lifted j
        m = 4 - j - 2
        for g in gens_upto(m):
            gg = up([g], j + 2)[0]
            out.append((('comm2', g, j), [gg, ('CS', j)], [('CS', j), gg]))
    return out

# --------------------------------------------------------- derivations
def f0_rename(cur, want):
    """the F0 instance turning the letter cur into want (the borrowed wires
    exchanged): (lemma name, forward)."""
    assert cur[0] in ('SBOX', 'SBOXd') and cur[0] == want[0] and cur[2:4] == want[2:4]
    assert (cur[1], cur[4]) == (want[4], want[1])
    x, (t, y) = cur[2], cur[3]
    base = 'F0' if cur[0] == 'SBOX' else 'F0d'
    # F0: SBOX(2;0;41;3) = SBOX(3;0;41;2); rename 0->x, 1->y, 2->u, 3->A
    u, A = cur[1], cur[4]
    pi = {0: x, 1: y, 2: u, 3: A}
    return L5.instance(base, {a: b for a, b in pi.items() if a != b}), True

def align(P, k, target):
    """the letters at k .. to target by F0 steps."""
    for i, want in enumerate(target):
        cur = P.cur[k + i]
        if cur != want:
            nm, fwd = f0_rename(cur, want)
            P.L(nm, k + i, fwd)

def domain_perm(k, j):
    """a permutation of the domain wires taking 0 .. k-1 to j .. j+k-1 and
    the rest, in order, to the rest."""
    src_rest = [w for w in DOM if w >= k]
    dst = list(range(j, j + k)); dst_rest = [w for w in DOM if w not in dst]
    pi = {w: j + w for w in range(k)}
    pi.update(dict(zip(src_rest, dst_rest)))
    return {a: b for a, b in pi.items() if a != b}

def f2_name(g, h):
    """the F2 item for the generators g, h (either order)."""
    def show1(x):
        if x[0] == 'I': return 'iI'
        if x[0] == 'CS': return f'CS{x[1]}{x[1] + 1}'
        return f'{x[0]}{x[1]}'
    for a, b in ((g, h), (h, g)):
        nm = f'F2 {show1(a)}|{show1(b)}'
        if nm in L5.JOINT: return nm, (a == g)
    return None, None

def gname(g):
    if g[0] == 'I': return 'I'
    if g[0] == 'CS': return f'CS{g[1]}{g[1] + 1}'
    return f'{g[0]}{g[1]}'

def key_name(key):
    if key[0] == 'rule': return f'tr {key[1]} at {key[2]}'
    if key[0] == 'comm1': return f'tr comm1 {key[1]} {gname(key[2])} at {key[3]}'
    return f'tr comm2 {gname(key[1])} at {key[2]}'

def derive(key, lg, rg):
    lhs, rhs = lam(lg), lam(rg)
    name = key_name(key)
    if lhs == rhs: return ('refl', None)
    P = Prim(name, lhs, rhs, L5.LEMMAS)
    if len(gsupp(lhs) | gsupp(rhs)) <= 4:
        L5.lower_window(P, 0, len(lhs), rhs)
    elif key[0] == 'rule':
        _, r, j = key
        if r in missing(): return ('missing', r)
        k = RULES[r][0]; pi = domain_perm(k, j)
        f1 = L5.instance(F1[r], pi)
        l1, r1 = L5.LEMMAS[f1]
        align(P, 0, l1)
        P.L(f1, 0, True)
        # r1 back to rhs
        for i, want in enumerate(rhs):
            cur = P.cur[i]
            if cur != want:
                nm, fwd = f0_rename(cur, want); P.L(nm, i, fwd)
    else:
        g, h = (lg[0], lg[1])
        nm, fwd = f2_name(g, h)
        assert nm is not None, ('no F2 item', key)
        P.L(L5.instance(nm, {}), 0, fwd)
    P.done(); L5.PRIMS.append(P)
    return ('lemma', name)

def all_obligations():
    res = {}
    for key, l, r in instances():
        res[key] = derive(key, l, r)
    return res

# --------------------------------------------------------- Agda
AGDA_RULE = {'order-I': 'order-I', 'order-S': 'order-S', 'order-K': 'order-K', 'order-SK': 'order-SK',
             'order-CS': 'order-CS', 'comm-CS-S0': 'comm-CS-S₀', 'comm-CS-S1': 'comm-CS-S₁',
             'X-CS0': 'X-CS₀', 'X-CS1': 'X-CS₁', 'CS-K0': 'CS-K₀', 'CS-K1': 'CS-K₁',
             'comm-CS-CS': 'comm-CS↑-CS', 'rel-266': 'rel-266', 'rel-267': 'rel-267', 'rel-268': 'rel-268',
             'rel-269': 'rel-269', 'rel-272': 'rel-272', 'cx-ccz': 'cx-ccz', 'toff-ccz': 'toff-ccz',
             'ck-tct': 'ck-tct', 'lf': 'lf', 'hyb-sq': 'hyb-sq', 'hyb-yb': 'hyb-yb'}
NEW_RULES = ('lf', 'hyb-sq', 'hyb-yb')

def ups(e, j):
    for _ in range(j): e = f'cong↑ ({e})'
    return e

def gen_pats(g, m):
    """the Agda patterns of the generator g of Gen m (every lift of a scalar)."""
    if g[0] == 'I': return ['gate₀ I-gate' + ' ↥' * i for i in range(m + 1)]
    if g[0] == 'S': return ['gate₁ S-gate' + ' ↥' * g[1]]
    if g[0] == 'K': return ['gate₁ K-gate' + ' ↥' * g[1]]
    return ['gate₂ CS-gate' + ' ↥' * g[1]]

def missing_field(r, j): return f'm-{r}-{j}'

def accessors(fields):
    """an accessor for each component of the product Missing."""
    out = []
    for i, (n, t) in enumerate(fields):
        last = i == len(fields) - 1
        e = 'm'
        for _ in range(i): e = f'proj₂ ({e})' if e != 'm' else 'proj₂ m'
        if not last: e = f'proj₁ ({e})' if e != 'm' else 'proj₁ m'
        out += [f'{n} : Missing → {t}', f'{n} m = {e}', '']
    return out


def agda_module(res, modof, lemname, MOD):
    """TransportAx and its parts, as [(path relative to Five, text)].

    One function by cases took 7.5 GB: each clause computes the λ-images
    of a rule's sides and compares them with a lemma's type, and a module
    keeps all of that until it ends.  So the instances are split by their
    depth j (the number of cong↑ around them) into TransportAx/A{j}, each
    with a function for the rule instances (ax-s{j}) and for comm₁ and
    comm₂ (ax-k1-{j}, ax-k2-{j}); TransportAx dispatches."""
    NL = chr(10)
    fields = []
    parts = {}          # j -> {'s': [...], 'k1': [...], 'k2': [...], 'deps': {}}

    def part(j):
        return parts.setdefault(j, {'s': [], 'k1': [], 'k2': [], 'deps': {}})

    def body(key, j):
        kind, v = res[key]
        if kind == 'lemma':
            part(j)['deps'].setdefault(modof[v], set()).add(lemname(v)); return f'{lemname(v)} c4'
        assert kind == 'missing'
        return f'{missing_field(key[1], key[2])} ms'

    for key, l, r in instances():
        if key[0] == 'rule':
            _, name, j = key
            if res[key][0] == 'missing':
                fields.append((missing_field(name, j), f'Inst ({ups("srel " + AGDA_RULE[name], j)})'))
            part(j)['s'].append(f'ax-s{j} c4 ms {AGDA_RULE[name]} = {body(key, j)}')
        elif key[0] == 'comm1':
            _, h, g, j = key; m = 4 - j - 1
            for gp in gen_pats(g, m):
                part(j)['k1'].append(f'ax-k1-{j} c4 {h}-gate ({gp}) = {body(key, j)}')
        else:
            _, g, j = key; m = 4 - j - 2
            for gp in gen_pats(g, m):
                part(j)['k2'].append(f'ax-k2-{j} c4 CS-gate ({gp}) = {body(key, j)}')
    for name in NEW_RULES:
        fields.append((missing_field(name, 0), f'Inst (srel {AGDA_RULE[name]})'))
        part(0)['s'].append(f'ax-s0 c4 ms {AGDA_RULE[name]} = {missing_field(name, 0)} ms')

    head = lambda title, body_: f"""------------------------------------------------------------------------
-- Presentations of groups
--
-- {title}
--
{body_}
------------------------------------------------------------------------

{{-# OPTIONS --without-K --safe #-}}

"""
    out = []
    out.append(('TransportAx/Base.agda', head(
        'Transport on five wires: the statement for one axiom instance',
        '-- `Inst a`, the equation of the λ¹₄-images of the two sides of an axiom\n'
        '-- instance a of the four-wire theory, and `Missing`, those the joint\n'
        '-- run does not derive: the controlled versions of the four-wire rules\n'
        '-- ck-tct, lf, hyb-sq and hyb-yb, which are rules on five wires\n'
        '-- (Five.Rules, Five.MissingInst).  Written by\n'
        '-- `scratchpad/five/transport5.py`.') + f"""module {MOD}.TransportAx.Base where

open import Data.Product using (_×_ ; proj₁ ; proj₂)
open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import {MOD}.Chain
open import {MOD}.Transport

Inst : ∀ {{w v}} → 4 VRel, w === v → Set
Inst {{w}} {{v}} _ = ⟪ λʷ w ⟫ʷ ≈ ⟪ λʷ v ⟫ʷ

-- A product, not a record: the positivity checker normalises the types
-- of a record's fields, here the λ-images of the four-wire rules, and
-- that took more than 5 GB.
Missing : Set
Missing = {' × '.join(t for _, t in fields)}

{NL.join(accessors(fields))}
"""))
    dispatch = []
    for j in sorted(parts):
        P = parts[j]; w = 4 - j
        dep_lines = NL.join(f'open import {MOD}.D.{m} using ({" ; ".join(sorted(ns))})'
                            for m, ns in sorted(P['deps'].items()))
        defs = []
        if P['s']:
            defs += [f'ax-s{j} : Complete 4 → Missing → ∀ {{w v}} (a : {w} SRel, w === v) → Inst ({ups("srel a", j)})']
            defs += P['s'] + ['']
            dispatch.append(f'λ-ax c4 ms ({ups("srel a", j)}) = ax-s{j} c4 ms a')
        if P['k1']:
            defs += [f'ax-k1-{j} : Complete 4 → ∀ h (g : Gen {w - 1}) → Inst ({ups("comm₁ h g", j)})']
            defs += P['k1'] + ['']
            dispatch.append(f'λ-ax c4 ms ({ups("comm₁ h g", j)}) = ax-k1-{j} c4 h g')
        if P['k2']:
            defs += [f'ax-k2-{j} : Complete 4 → ∀ h (g : Gen {w - 2}) → Inst ({ups("comm₂ h g", j)})']
            defs += P['k2'] + ['']
            dispatch.append(f'λ-ax c4 ms ({ups("comm₂ h g", j)}) = ax-k2-{j} c4 h g')
        out.append((f'TransportAx/A{j}.agda', head(
            f'Transport on five wires: the axiom instances under {j} cong↑',
            f'-- The equations Inst of the instances of depth {j} (Five.TransportAx).\n'
            '-- Written by `scratchpad/five/transport5.py`.') + f"""module {MOD}.TransportAx.A{j} where

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import {MOD}.Chain
open import {MOD}.Transport
open import {MOD}.TransportAx.Base using ({' ; '.join(['Inst', 'Missing'] + [n for n, _ in fields])})
{dep_lines}

""" + NL.join(defs)))
    for j in range(4):
        dispatch.append(f'λ-ax c4 ms ({ups("ω↑=ω I-gate", j)}) = refl')
    imports = NL.join(f'open import {MOD}.TransportAx.A{j} using ('
                      + ' ; '.join(n for n, k in ((f'ax-s{j}', 's'), (f'ax-k1-{j}', 'k1'), (f'ax-k2-{j}', 'k2'))
                                   if parts[j][k]) + ')' for j in sorted(parts))
    out.append(('TransportAx.agda', head(
        'Transport on five wires: every axiom instance of the four-wire theory',
        '-- For each instance of Syntactics\' rules at every placement on four\n'
        '-- wires, and of the structural rules, the equation of the λ¹₄-images of\n'
        '-- its two sides (Five.Transport.AxOk): a window, an F2 item of the joint\n'
        '-- paper, or an F1 item renamed by a permutation of the domain wires with\n'
        '-- the borrowed wires put in order by F0; the derivations are the lemmas\n'
        '-- `lem-tr-…` of Five.D, collected by depth in TransportAx/A0-A4.  What\n'
        '-- the joint run does not derive is a field of `Missing`: the controlled\n'
        '-- versions of the four-wire rules ck-tct, lf, hyb-sq and hyb-yb, which\n'
        '-- are rules on five wires (Five.Rules, Five.MissingInst).  Written by\n'
        '-- `scratchpad/five/transport5.py`.') + f"""module {MOD}.TransportAx where

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import {MOD}.Chain
open import {MOD}.Transport
open import {MOD}.TransportAx.Base public using ({' ; '.join(['Inst', 'Missing'] + [n for n, _ in fields])})
{imports}

λ-ax : Complete 4 → Missing → AxOk
{NL.join(dispatch)}
"""))
    return out


if __name__ == '__main__':
    import collections
    names = L5.load(sys.argv[1])
    for nm in names: L5.instance(nm, {})
    res = all_obligations()
    c = collections.Counter(v[0] for v in res.values())
    print(len(res), 'instances', dict(c))
    print('missing:', sorted({v[1] for v in res.values() if v[0] == 'missing'}))

# --------------------------------------------------------- transports
def agda2(word):
    """a word of the wires 0 1 (normalised joint letters) as an Agda Circuit 2."""
    out = []
    for g in word:
        k = g[0]
        if k == 'iI': out.append('iI')
        elif k in ('S', 'K'): out.append(k if g[1] == 0 else f'({k} ↑)')
        elif k == 'CS':
            assert tuple(g[1:]) == (0, 1), g; out.append('CS')
        else: raise ValueError(g)
    return ' • '.join(out) if out else 'ε'

def tr_module(res, modof, lemname, MOD, mname, trname):
    """D/TR.agda: the lambda-images of the instances on two wires (ok₂) and
    the transports of the de-borrowing, at control wire 4 on the wires 0 1."""
    NL = chr(10)
    deps = {}
    def call(v):
        deps.setdefault(modof[v], set()).add(lemname(v)); return f'{lemname(v)} c4'
    clauses = []
    for key, l, r in instances():
        if key[0] == 'rule':
            _, name, j = key
            if RULES[name][0] + j > 2: continue
            kind, v = res[key]; assert kind == 'lemma', key
            clauses.append(f'ok₂ c4 ({ups("srel " + AGDA_RULE[name], j)}) = {call(v)}')
        elif key[0] == 'comm1':
            _, h, g, j = key
            m2 = 2 - j - 1
            if m2 < 0 or g not in gens_upto(m2): continue
            kind, v = res[key]; assert kind == 'lemma', key
            for gp in gen_pats(g, m2):
                clauses.append(f'ok₂ c4 ({ups(f"comm₁ {h}-gate ({gp})", j)}) = {call(v)}')
        else:
            _, g, j = key
            m2 = 2 - j - 2
            if m2 < 0 or g not in gens_upto(m2): continue
            kind, v = res[key]; assert kind == 'lemma', key
            for gp in gen_pats(g, m2):
                clauses.append(f'ok₂ c4 ({ups(f"comm₂ CS-gate ({gp})", j)}) = {call(v)}')
    for j in range(2):
        clauses.append(f'ok₂ c4 ({ups("ω↑=ω I-gate", j)}) = refl')
    x4 = next(n for n in modof if lemname(n) == 'lem-calc-x4x4')
    x4call = call(x4)
    trs = []
    for name, (el, er, b) in L5.TRANSPORTS.items():
        l, r = L5.AXIOMS[name]
        t = trname(name); e = 'e2-' + t[2:]
        side = lambda w: '(' + ' ∷ '.join(mname(g) for g in w) + ' ∷ [])' if w else '[]'
        trs.append(f'{t} : Ws → ⟪ {side(l)} ⟫ʷ ≈ ⟪ {side(r)} ⟫ʷ')
        body = f'transport₂ (ok₂ c4) ({e} (lit c4))'
        # lam⁰'s words, which ⟪ λʷ ?u ⟫ʷ does not determine: the two-wire
        # sides, given to lam⁰₂ at Circuit 2.
        lam0 = f'lam⁰₂ ({x4call}) ({agda2(el)}) ({agda2(er)})'
        trs.append(f'{t} c4 = ' + (body if b == 1 else f'{lam0} ({body})'))
        trs.append('')
    es = sorted({'e2-' + trname(n)[2:] for n in L5.TRANSPORTS})
    dep_lines = NL.join(f'open import {MOD}.D.{m} using ({" ; ".join(sorted(ns))})' for m, ns in sorted(deps.items()))
    return f"""------------------------------------------------------------------------
-- Presentations of groups
--
-- The transports of the de-borrowing
--
-- Each replaces λᵇ(el) by λᵇ(er) for an equation el = er on the wires
-- 0 1 of the domain (control wire 4), the de-borrowing using it at other
-- wires by renaming: Five.Transport2.transport₂ of the two-wire
-- derivation the windows record carries (WsL), given the λ-images of the
-- instances on two wires (`ok₂`, from the lemmas of Five.D).  Written by
-- `scratchpad/five/transport5.py`.
------------------------------------------------------------------------

{{-# OPTIONS --without-K --safe #-}}

module {MOD}.D.TR where

open import Data.List using (List ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import {MOD}.Chain
open import {MOD}.WinSig using (Ws ; lit ; {" ; ".join(es)})
open import {MOD}.Transport2 using (Ok₂ ; transport₂ ; lam⁰₂)
{dep_lines}

ok₂ : Ws → Ok₂
{NL.join(clauses)}

{NL.join(trs)}"""

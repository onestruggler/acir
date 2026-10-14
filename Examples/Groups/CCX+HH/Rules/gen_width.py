#!/usr/bin/env python3
"""Write Natural/WidthN and Natural/WidthN/: natural rules complete on n wires.

For CCX+HH (`HH`) and CCX+H (`H`).  The proof-producing coset
enumeration (proofs.py with natproof.py; labelled.py with natproofH.py)
gives a representative for every element of the group on n wires and,
for each representative c and letter y, a derivation
rep c ++ [y] = rep (δ c y) from the natural rules.  The modules state
those derivations, the tables and the boolean checks (the derivations
have the right sides; the representatives' matrices, given as literals,
agree with the semantics and are pairwise distinct), and
Natural/WidthN.agda instantiates Natural/Automaton, which gives
completeness on n wires.  Only facts the final table needs are written.

The output is split into modules because Agda frees the memory of an
evaluation only when its module is done: facts in chunks, the matrix
agreement in chunks, and each check in a module of its own.  Tables are
functions by clauses on the base-16 digits of an index: a long chain of
infix constructors exhausts the operator parser's memory, and Agda
accepts numeral patterns up to 20 only.

Run: python3 -B gen_width.py [HH|H] N [--check]   (N = 1 or 2; HH by default)
"""
import sys
from fractions import Fraction
from pathlib import Path

import core as C
import coreH as CH
import proofs as P
import labelled as L
import natproof as NP
import natproofH as NH

SUB = "₀₁₂₃₄₅₆₇₈₉"
FACTS_PER_MODULE = 1200
AGREE_PER_MODULE = 48
ARITY = {"X": 1, "H": 1, "CX": 2, "HH": 2, "CCX": 3}


# ---------------------------------------------------------------------
# Numbers: dyadics, and Q(√2) as pairs (a, b) meaning a + b√2

def dyadic(v):
    """A name and a literal for the canonical dyadic a / 2^k."""
    k = v.denominator.bit_length() - 1
    assert v.denominator == 1 << k
    a = v.numerator
    return ("p" if a >= 0 else "m") + f"{abs(a)}x{k}", \
        f"Dyadic' {'(+ ' + str(a) + ')' if a >= 0 else '-[1+ ' + str(-a - 1) + ' ]'} {k} _"


class Q2:
    __slots__ = ("a", "b")

    def __init__(self, a, b=0):
        self.a, self.b = Fraction(a), Fraction(b)

    def __add__(self, o):
        return Q2(self.a + o.a, self.b + o.b)

    def __mul__(self, o):
        return Q2(self.a * o.a + 2 * self.b * o.b, self.a * o.b + self.b * o.a)

    def __eq__(self, o):
        return (self.a, self.b) == (o.a, o.b)

    def __hash__(self):
        return hash((self.a, self.b))

    def __lt__(self, o):
        return (self.a, self.b) < (o.a, o.b)


def root_two(v):
    na, la = dyadic(v.a)
    nb, lb = dyadic(v.b)
    return f"r{na}y{nb}", f"RootTwo ({la}) ({lb})"


# ---------------------------------------------------------------------
# The two gate sets

class SpecHH:
    key = "HH"
    root = "Examples.Groups.CCX+HH.Natural"
    natural = Path(__file__).resolve().parents[1] / "Natural"
    sem = "Examples.Groups.CCX+HH.Semantics"
    elem, eq, eq_refl = "Dyadic", "eqD", "eqD-refl"
    elem_imports = "open import Quantum.Synthesis.Ring using (Dyadic ; Dyadic')\n"
    unfolding_import = "open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)\n"
    unfolding = "_+ᴰ_ _*ᴰ_ -ᴰ_"
    decide = "eqD ; eqD-refl"
    by_eq = "by-eq"
    names = {"X": "x", "CX": "cx", "CCX": "ccx", "HH": "hh"}
    ctors = {"X": ("gate₁", "X-gate"), "CX": ("gate₂", "CX-gate"),
             "CCX": ("gate₃", "CCX-gate"), "HH": ("gate₂", "HH-gate")}
    literal_note = "pAxK is A / 2^K and mAxK is -A / 2^K"

    @staticmethod
    def gateset(n):
        return C.GateSet(n)

    @staticmethod
    def axioms(gs):
        return NP.axioms(gs)

    @staticmethod
    def enumerate(gs, axioms):
        tc = P.ProofTC(len(gs.names), axioms)
        live = tc.run()
        final = {(c, y): tc.final(c, y) for c in live for y in range(len(gs.names))}
        return tc, live, final

    @staticmethod
    def zero():
        return Fraction(0)

    @staticmethod
    def one():
        return Fraction(1)

    @staticmethod
    def hh(sign):
        return Fraction(sign, 2)

    literal = staticmethod(dyadic)


class SpecH(SpecHH):
    key = "H"
    root = "Examples.Groups.CCX+H.Natural"
    natural = Path(__file__).resolve().parents[2] / "CCX+H" / "Natural"
    sem = "Examples.Groups.CCX+H.Presentation"
    elem, eq, eq_refl = "D", "eqD√", "eqD√-refl"
    elem_imports = ("open import Quantum.Synthesis.Ring using (Dyadic' ; RootTwo)\n"
                    "open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D)\n")
    unfolding_import = ("import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S\n"
                        "import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R\n")
    unfolding = "S.actV S.set₁ S.set₂ R._+ᴰ_ R._*ᴰ_ R.-ᴰ_"
    decide = "eqD√ ; eqD√-refl"
    by_eq = "by-eq√"
    names = {"X": "x", "CX": "cx", "CCX": "ccx", "H": "h"}
    ctors = {"X": ("gate₁", "X-gate"), "H": ("gate₁", "H-gate"),
             "CX": ("gate₂", "CX-gate"), "CCX": ("gate₃", "CCX-gate")}
    literal_note = "rAyB is A + B√2, with pAxK for A / 2^K and mAxK for -A / 2^K"

    @staticmethod
    def gateset(n):
        return CH.GateSetH(n)

    @staticmethod
    def axioms(gs):
        return NH.axioms(gs)

    @staticmethod
    def enumerate(gs, axioms):
        # Felsch's strategy: far fewer cosets, and so far fewer facts.
        tc = L.LabelledTC(len(gs.names), axioms, {})
        live = tc.run()
        final = {}
        for c in live:
            for y in range(len(gs.names)):
                d, label, f = tc.final(c, y)
                assert label == ()
                final[(c, y)] = (d, f)
        return tc, live, final

    @staticmethod
    def zero():
        return Q2(0)

    @staticmethod
    def one():
        return Q2(1)

    @staticmethod
    def hh(sign):
        return Q2(0, Fraction(sign, 2))

    literal = staticmethod(root_two)


SPECS = {"HH": SpecHH, "H": SpecH}


# ---------------------------------------------------------------------

def letter(spec, gs, g):
    base, i = C.split_name(gs.names[g])
    return spec.names[base] + SUB[i]


def lst(spec, gs, word):
    return "(" + " ∷ ".join(letter(spec, gs, g) for g in word) + " ∷ [])" if word else "[]"


def physical_matrix(spec, n, name):
    """Entry [y][x] = ⟨y|G|x⟩, wire 0 the low bit."""
    base, i = C.split_name(name)
    dim = 1 << n
    z, o = spec.zero(), spec.one()

    def perm(f):
        return [[o if y == f(x) else z for x in range(dim)] for y in range(dim)]

    def flip(t, cs=()):
        return lambda x: x ^ (1 << t) if all(x >> c & 1 for c in cs) else x

    if base == "X":
        return perm(flip(i))
    if base == "CX":
        return perm(flip(i, (i + 1,)))
    if base == "CCX":
        return perm(flip(i, (i + 1, i + 2)))
    if base == "HH":
        mask = (1 << i) | (1 << (i + 1))
        return [[spec.hh((-1) ** bin(y & x & mask).count("1")) if (y & ~mask) == (x & ~mask) else z
                 for x in range(dim)] for y in range(dim)]
    assert base == "H"
    mask = 1 << i
    return [[Q2(0, Fraction((-1) ** bin(y & x & mask).count("1"), 2)) if (y & ~mask) == (x & ~mask) else z
             for x in range(dim)] for y in range(dim)]


def word_matrix(spec, gs, word):
    """The matrix of a word: the product of its gates in written order."""
    dim = 1 << gs.n
    z, o = spec.zero(), spec.one()
    m = [[o if i == j else z for j in range(dim)] for i in range(dim)]
    for g in word:
        p = physical_matrix(spec, gs.n, gs.names[g])
        new = []
        for i in range(dim):
            row = []
            for j in range(dim):
                acc = z
                for k in range(dim):
                    acc = acc + m[i][k] * p[k][j]
                row.append(acc)
            new.append(row)
        m = new
    return m


def axiom_name(spec, gs, ax):
    key = ax.name
    if key[0] == "inv":
        return f"(inv⁼ {letter(spec, gs, key[1])})"
    if key[0] == "comm":
        return f"comm-{key[1]}-{key[2]}"
    rule, shift = key
    e = f"{rule}ᵉ"
    for _ in range(shift):
        e = f"(lift⁼ {e})"
    return e


def header(spec, n, name, description):
    full = f"{spec.root}.Width{n}" + (f".{name}" if name else "")
    lines = "\n".join("-- " + l if l else "--" for l in description.split("\n"))
    return f"""------------------------------------------------------------------------
-- Presentations of groups
--
{lines}
--
-- Generated by CCX+HH/Rules/gen_width.py; do not edit.
------------------------------------------------------------------------

{{-# OPTIONS --without-K --safe #-}}

module {full} where

"""


def digits_for(N):
    d = 1
    while 16 ** d < N:
        d += 1
    return d


def table(name, typ, items, default, digits):
    """A table as a function on ℕ, by clauses on the base-16 digits."""
    rows = [f"\n{name}′ : {'ℕ → ' * digits}{typ}\n"]
    for k, v in enumerate(items):
        ds = [(k // 16 ** (digits - 1 - j)) % 16 for j in range(digits)]
        rows.append(f"{name}′ {' '.join(map(str, ds))} = {v}\n")
    rows.append(f"{name}′ {' '.join(['_'] * digits)} = {default}\n")
    args = " ".join(f"((i / {16 ** (digits - 1 - j)}) % 16)" if j < digits - 1 else "(i % 16)"
                    for j in range(digits))
    rows.append(f"\n{name} : ℕ → {typ}\n{name} i = {name}′ {args}\n")
    return "".join(rows)


def absurd_letters(n):
    """The patterns of Gen n that are no letter: a 0-ary gate, shifted."""
    out, p = [], "(gate₀ ())"
    for _ in range(n + 1):
        out.append(p)
        p = f"({p} ↥)"
    return out


def generate(spec, n):
    """{relative path: module text}."""
    ROOT = spec.root
    gs = spec.gateset(n)
    axioms = spec.axioms(gs)
    tc, live, final = spec.enumerate(gs, axioms)
    index = {c: k for k, c in enumerate(live)}
    assert live[0] == 0 and tc.rep[0] == ()
    N = len(live)
    W = n
    letters = list(range(len(gs.names)))
    need, stack = set(), [f for _, f in final.values()]
    while stack:
        f = stack.pop()
        if f in need:
            continue
        need.add(f)
        for _, (kind, k), _ in tc.facts[f].steps:
            if kind == "fact":
                stack.append(k)
    for f in need:
        assert P.replay(tc, tc.facts[f]), f
    digits = digits_for(N)
    files = {}
    sub = f"Width{n}"
    patterns = " ; ".join(letter(spec, gs, y) for y in letters)

    # ------------------------------------------------------------------
    # Facts, in chunks; the first also has the commutations as equations.
    facts = sorted(need)
    chunks = [facts[i:i + FACTS_PER_MODULE] for i in range(0, len(facts), FACTS_PER_MODULE)]
    for k, chunk in enumerate(chunks):
        s = header(spec, n, f"Facts{k}",
                   f"Derivations from the natural rules on {n} wire{'s' if n > 1 else ''}, "
                   f"part {k + 1} of {len(chunks)}:\n"
                   f"each rewrites a representative followed by a letter.")
        s += """open import Data.List.Base using ([] ; _∷_)
import Relation.Binary.PropositionalEquality as Eq
"""
        if k == 0:
            s += """import Presentation.Base as PB
import Presentation.Properties as PP
"""
        s += f"""
open import {ROOT}.Syntactics
open import {ROOT}.Engine
open import {ROOT}.Axioms
"""
        if k > 0:
            s += f"open import {ROOT}.{sub}.Facts{k - 1} public\n"
        if k == 0:
            comms = [ax for ax in axioms if ax.name[0] == "comm"]
            if comms:
                s += """
private
  as : ∀ {m} {w v : Circuit m} →
       PP.to-list (m VRel,_===_) w Eq.≡ PP.to-list (m VRel,_===_) v → m ⊢ w ≈ v
  as {m} = PP.by-assoc (m VRel,_===_)

-- The commutations of letters on disjoint wires.
"""
            for ax in comms:
                a, b = ax.name[1], ax.name[2]
                # commₖ h g : [g ↥ᵏ] • [h] === [h] • [g ↥ᵏ], h the lower gate
                lo, hi = (a, b) if min(gs.wires[a]) < min(gs.wires[b]) else (b, a)
                blo, bhi = C.split_name(gs.names[lo]), C.split_name(gs.names[hi])
                k_ar = ARITY[blo[0]]
                h = spec.ctors[blo[0]][1]
                g = " ".join(spec.ctors[bhi[0]]) + " ↥" * (bhi[1] - k_ar)
                comm = f"PB.axiom (comm{SUB[k_ar]} {h} ({g}))"
                if ax.lhs[0] != hi:
                    comm = f"PB.sym ({comm})"
                s += (f"\ncomm-{a}-{b} : Eqn {W}\ncomm-{a}-{b} = eqn {lst(spec, gs, ax.lhs)} {lst(spec, gs, ax.rhs)}\n"
                      f"  (PB.trans (as Eq.refl) (PB.trans ({comm}) (as Eq.refl)))\n")
        for f in chunk:
            fact = tc.facts[f]
            steps = []
            for pos, (kind, key), fwd in fact.steps:
                if kind == "ax":
                    e = axiom_name(spec, gs, axioms[key])
                elif kind == "inv":
                    e = f"(inv⁼ {letter(spec, gs, key)})"
                else:
                    e = f"f{key}"
                if not fwd:
                    e = f"(sym⁼ {e})"
                steps.append(f"rw {pos} {e}")
            ss = "(" + " ∷ ".join(steps) + " ∷ [])" if steps else "[]"
            s += (f"\nf{f} : Eqn {W}\nf{f} = derive {lst(spec, gs, fact.lhs)} {lst(spec, gs, fact.rhs)}\n"
                  f"  {ss} Eq.refl\n")
        files[f"{sub}/Facts{k}.agda"] = s
    last_facts = f"{ROOT}.{sub}.Facts{len(chunks) - 1}"

    # ------------------------------------------------------------------
    # The representatives and the prefixes of them that are not, each
    # word after the first being its parent's followed by one letter.
    family = [tc.rep[c] for c in live]
    position = {w: k for k, w in enumerate(family)}
    for w in list(family):
        for j in range(len(w)):
            if w[:j] not in position:
                position[w[:j]] = len(family)
                family.append(w[:j])
    KF = len(family)
    parents = [0] + [position[w[:-1]] for w in family[1:]]
    lasts = [0] + [w[-1] for w in family[1:]]
    fdigits = digits_for(KF)

    # ------------------------------------------------------------------
    # The words, with no facts: the matrix checks need not load those
    absurd = absurd_letters(n)
    s = header(spec, n, "Words",
               f"The {KF} words: the {N} representatives, then the prefixes of\n"
               f"representatives that are not representatives themselves; each word\n"
               f"after the first is its parent's followed by its last letter.")
    s += f"""open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ ; _/_ ; _%_)

open import {ROOT}.Syntactics
open import {ROOT}.Axioms using ({patterns})
"""
    s += table("repℕ", f"List (Gen {W})", [lst(spec, gs, w) for w in family], "[]", fdigits)
    s += table("parentℕ", "ℕ", list(map(str, parents)), "0", fdigits)
    s += table("lastℕ", f"Gen {W}", [letter(spec, gs, y) for y in lasts], letter(spec, gs, 0), fdigits)
    files[f"{sub}/Words.agda"] = s

    # ------------------------------------------------------------------
    # Tables
    s = header(spec, n, "Tables",
               f"The {N} representatives, the transition table and its derivations,\n"
               f"as functions of an index.")
    s += f"""open import Data.Fin using (Fin ; zero ; suc ; toℕ ; #_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ ; _/_ ; _%_)
import Presentation.Base as PB

open import {ROOT}.Syntactics
open import {ROOT}.Engine using (Eqn ; eqn)
open import {ROOT}.Axioms using ({patterns})
open import {ROOT}.{sub}.Words public
open import {last_facts}
"""
    s += f"\nrep : Fin {N} → List (Gen {W})\nrep c = repℕ (toℕ c)\n"
    for y in letters:
        Ly = letter(spec, gs, y)
        s += table(f"δ-{Ly}", f"Fin {N}", ['# ' + str(index[final[(c, y)][0]]) for c in live],
                   "zero", digits)
        s += table(f"fact-{Ly}", f"Eqn {W}", ['f' + str(final[(c, y)][1]) for c in live],
                   "eqn [] [] PB.refl", digits)
    s += f"\nδ : Fin {N} → Gen {W} → Fin {N}\n"
    s += "".join(f"δ c {letter(spec, gs, y)} = δ-{letter(spec, gs, y)} (toℕ c)\n" for y in letters)
    s += "".join(f"δ c {a}\n" for a in absurd)
    s += f"\nfact : Fin {N} → Gen {W} → Eqn {W}\n"
    s += "".join(f"fact c {letter(spec, gs, y)} = fact-{letter(spec, gs, y)} (toℕ c)\n" for y in letters)
    s += "".join(f"fact c {a}\n" for a in absurd)
    files[f"{sub}/Tables.agda"] = s

    # ------------------------------------------------------------------
    # The sides of the table's derivations
    s = header(spec, n, "Sides", "Each derivation of the table starts from its representative followed\n"
                                 "by its letter and ends at the representative the table gives.")
    s += f"""open import Data.Bool.Base using (true ; T)
open import Data.List.Base using ([] ; _∷_ ; _++_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import {ROOT}.Syntactics
open import {ROOT}.Engine using (lhs ; rhs ; eqL ; eqL-sound)
open import {ROOT}.Axioms using ({patterns})
open import Examples.Groups.CCX+HH.Natural.Checks using (allF ; allF-sound)
open import {ROOT}.{sub}.Tables

private
  true≡ : ∀ {{b}} → T b → b ≡ true
  true≡ {{true}} _ = Eq.refl

fact-lhs : ∀ c y → lhs (fact c y) ≡ rep c ++ y ∷ []
""".replace("{{b}}", "{b}").replace("{{true}}", "{true}")
    for y in letters:
        Ly = letter(spec, gs, y)
        s += (f"fact-lhs c {Ly} = eqL-sound _ _ (true≡ (allF-sound "
              f"(λ c → eqL (lhs (fact c {Ly})) (rep c ++ {Ly} ∷ [])) tt c))\n")
    s += "".join(f"fact-lhs c {a}\n" for a in absurd)
    s += f"\nfact-rhs : ∀ c y → rhs (fact c y) ≡ rep (δ c y)\n"
    for y in letters:
        Ly = letter(spec, gs, y)
        s += (f"fact-rhs c {Ly} = eqL-sound _ _ (true≡ (allF-sound "
              f"(λ c → eqL (rhs (fact c {Ly})) (rep (δ c {Ly}))) tt c))\n")
    s += "".join(f"fact-rhs c {a}\n" for a in absurd)
    files[f"{sub}/Sides.agda"] = s

    # ------------------------------------------------------------------
    # The matrices of the representatives
    mats = [word_matrix(spec, gs, w) for w in family]
    dim = 1 << n
    values = sorted({v for m in mats for row in m for v in row})
    s = header(spec, n, "Matrices", f"The matrices of the {KF} words of Tables, as literals, listed by\n"
                                    f"columns; {spec.literal_note}.")
    s += f"""open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.Nat.Base using (ℕ ; _/_ ; _%_)
open import Data.Vec.Base using ([] ; _∷_)
{spec.elem_imports}open import Quantum.Synthesis.Matrix using (Matrix ; Matrix')

private
"""
    s += "  " + " ".join(spec.literal(v)[0] for v in values) + f" : {spec.elem}\n"
    s += "".join(f"  {spec.literal(v)[0]} = {spec.literal(v)[1]}\n" for v in values)

    def mat(m):
        cols = ["(" + " ∷ ".join(spec.literal(m[r][x])[0] for r in range(dim)) + " ∷ [])" for x in range(dim)]
        return "Matrix' (" + " ∷ ".join(cols) + " ∷ [])"
    s += table("tableℕ", f"Matrix {dim} {dim} {spec.elem}", [mat(m) for m in mats], mat(mats[0]), fdigits)
    files[f"{sub}/Matrices.agda"] = s

    # ------------------------------------------------------------------
    # The gate matrices, stored and checked once each
    s = header(spec, n, "Gates", "The matrices of the letters, as literals, each checked once.")
    s += f"""open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)
{spec.elem_imports}open import Quantum.Synthesis.Matrix using (Matrix ; Matrix')

open import {ROOT}.Syntactics
open import {ROOT}.Engine using (⟪_⟫)
open import {ROOT}.Axioms using ({patterns})
import {spec.sem} as Sem
open import Examples.Groups.CCX+HH.Decide using ({spec.by_eq})
{spec.unfolding_import}
private
"""
    gmats = {y: word_matrix(spec, gs, (y,)) for y in letters}
    gvalues = sorted({v for m in gmats.values() for row in m for v in row})
    s += "  " + " ".join(spec.literal(v)[0] for v in gvalues) + f" : {spec.elem}\n"
    s += "".join(f"  {spec.literal(v)[0]} = {spec.literal(v)[1]}\n" for v in gvalues)
    s += f"\ngateM : Gen {W} → Matrix {1 << n} {1 << n} {spec.elem}\n"
    s += "".join(f"gateM {letter(spec, gs, y)} = {mat(gmats[y])}\n" for y in letters)
    s += "".join(f"gateM {a}\n" for a in absurd)
    s += f"""
opaque
  unfolding {spec.unfolding}

  gate-ok : ∀ y → Sem.interpret ⟪ y ∷ [] ⟫ ≡ gateM y
"""
    s += "".join(f"  gate-ok {letter(spec, gs, y)} = {spec.by_eq} tt\n" for y in letters)
    s += "".join(f"  gate-ok {a}\n" for a in absurd)
    files[f"{sub}/Gates.agda"] = s

    # ------------------------------------------------------------------
    # The family of words with their stored matrices
    s = header(spec, n, "Family", f"The {KF} words of Tables with the stored matrices of Matrices.")
    s += f"""open import {ROOT}.{sub}.Words using (repℕ ; parentℕ ; lastℕ)
open import {ROOT}.{sub}.Matrices using (tableℕ)
open import {ROOT}.{sub}.Gates using (gateM)

open import {ROOT}.Prefix {KF} repℕ parentℕ lastℕ tableℕ gateM public using (ok ; module Agree)
"""
    files[f"{sub}/Family.agda"] = s

    # ------------------------------------------------------------------
    # Agreement, in chunks
    bounds = [(lo, min(AGREE_PER_MODULE, KF - lo)) for lo in range(0, KF, AGREE_PER_MODULE)]
    for k, (lo, K) in enumerate(bounds):
        s = header(spec, n, f"Agree{k}", f"The stored matrices of words {lo} to {lo + K - 1}, one gate at a time.")
        s += f"""open import Data.Bool.Base using (T)
open import Data.Nat.Base using (_+_ ; _≤_ ; _<_)
open import Data.Unit.Base using (tt)

open import Examples.Groups.CCX+HH.Natural.Checks using (allR ; allR-sound)
open import {ROOT}.{sub}.Family using (ok)
{spec.unfolding_import}
private
  opaque
    unfolding {spec.unfolding}

    check : T (allR {lo} {K} ok)
    check = tt

checked : ∀ i → {lo} ≤ i → i < {lo} + {K} → T (ok i)
checked = allR-sound {lo} {K} ok check
"""
        files[f"{sub}/Agree{k}.agda"] = s

    # ------------------------------------------------------------------
    # Distinctness
    s = header(spec, n, "Apart", f"The {N} stored matrices are pairwise distinct.")
    s += f"""open import Data.Bool.Base using (T)
open import Data.Unit.Base using (tt)

open import Examples.Groups.CCX+HH.Natural.Checks using (apartR)
open import Examples.Groups.CCX+HH.Decide using ({spec.eq})
open import {ROOT}.{sub}.Matrices using (tableℕ)

apart : T (apartR {spec.eq} {N} tableℕ)
apart = tt
"""
    files[f"{sub}/Apart.agda"] = s

    # ------------------------------------------------------------------
    # Assembly
    s = header(spec, n, "", f"The natural rules are complete on {n} wire{'s' if n > 1 else ''}.\n\n"
                            f"From a proof-producing coset enumeration: {N} representatives, and\n"
                            f"for each representative and letter a derivation from the natural\n"
                            f"rules ({len(need)} of them, each checked by Natural.Engine's `derive`).\n"
                            f"The representatives' matrices are distinct; Natural.Automaton\n"
                            f"concludes.")
    s += f"""open import Data.Bool.Base using (T)
open import Data.Fin using (zero)
open import Data.Nat.Base using (ℕ ; _≤_ ; _<_ ; z≤n)
open import Data.Nat.Properties using (<-≤-trans ; m≤m+n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import {ROOT}.Engine using (⟪_⟫)
open import Examples.Groups.CCX+HH.Natural.Checks using (module DistinctR ; join)
open import Examples.Groups.CCX+HH.Decide using ({spec.decide})
open import {ROOT}.{sub}.Tables
open import {ROOT}.{sub}.Sides
open import {ROOT}.{sub}.Matrices using (tableℕ)
open import {ROOT}.{sub}.Family using (ok ; module Agree)
open import {ROOT}.{sub}.Gates using (gate-ok)
open import {ROOT}.{sub}.Apart using (apart)
"""
    s += "".join(f"import {ROOT}.{sub}.Agree{k} as A{k}\n" for k in range(len(bounds)))
    s += f"""import {spec.sem} as Sem

private
  Ok : ℕ → Set
  Ok i = T (ok i)
"""
    for k, (lo, K) in enumerate(bounds):
        s += f"\n  checked{k} : ∀ i → 0 ≤ i → i < {lo + K} → Ok i\n"
        if k == 0:
            s += f"  checked{k} = A0.checked\n"
        else:
            s += f"  checked{k} = join Ok 0 {lo} {K} checked{k - 1} A{k}.checked\n"
    s += f"""
  module G = Agree gate-ok (λ i → checked{len(bounds) - 1} i z≤n)

  agree : ∀ i → i < {N} → Sem.interpret ⟪ repℕ i ⟫ ≡ tableℕ i
  agree i i<N = G.agree i (<-≤-trans i<N (m≤m+n {N} {KF - N}))

  module D = DistinctR {spec.eq} {spec.eq_refl} {{{N}}} (λ i → Sem.interpret ⟪ repℕ i ⟫) tableℕ agree apart

open import {ROOT}.Automaton {W} {N} rep δ zero Eq.refl fact fact-lhs fact-rhs D.distinct
  public using (complete ; nf ; nf-sound)
"""
    files[f"{sub}.agda"] = s
    return files


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    spec = SPECS[args[0]] if args[0] in SPECS else SpecHH
    n = int(args[-1])
    files = generate(spec, n)
    base = spec.natural
    if "--check" in sys.argv:
        bad = [p for p, t in files.items() if (base / p).read_text(encoding="utf-8") != t]
        if bad:
            raise SystemExit(f"differ from the generator: {bad}")
        print(f"{spec.key} Width{n}: {len(files)} modules up to date")
    else:
        (base / f"Width{n}").mkdir(exist_ok=True)
        for p, t in files.items():
            with open(base / p, "w", encoding="utf-8", newline="\n") as f:
                f.write(t)
        print(f"{spec.key} Width{n}: wrote {len(files)} modules, {sum(map(len, files.values()))} bytes")

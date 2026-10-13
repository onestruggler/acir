#!/usr/bin/env python3
"""Generate and audit the Clément-style three-wire auxiliary decoder.

The only synthesis search is Dijkstra on the 28 unordered pairs of basis
states, using X/CX conjugation of CCX.  No external circuit presentation
is used.  All 107 auxiliary generator images are checked exactly over
Z[1/sqrt(2)] using integer matrices and a shared denominator exponent.
"""

from heapq import heappop, heappush
from itertools import combinations
from pathlib import Path

N = 8


def x(t):
    return [("x", t)]


def h(t):
    return [("h", t)]


MACROS = {f"X{i}": x(i) for i in range(3)}
MACROS.update({f"H{i}": h(i) for i in range(3)})
MACROS["C10"] = [("cx", 1, 0)]
MACROS["C21"] = [("cx", 2, 1)]
MACROS["C20"] = MACROS["C21"] + MACROS["C10"] + MACROS["C21"] + MACROS["C10"]
for c, t in ((0, 1), (1, 2), (0, 2)):
    MACROS[f"C{c}{t}"] = h(c) + h(t) + MACROS[f"C{t}{c}"] + h(c) + h(t)
MACROS["CCX"] = [("ccx", 1, 2, 0)]


def permute_index(name, i):
    if name[0] == "X":
        return i ^ (1 << int(name[1]))
    c, t = int(name[1]), int(name[2])
    return i ^ (1 << t) if i & (1 << c) else i


def pair_routes():
    names = [n for n in MACROS if n.startswith("X") or (n.startswith("C") and n != "CCX")]
    best = {(6, 7): (0, ())}
    todo = [(0, (6, 7), ())]
    while todo:
        cost, pair, route = heappop(todo)
        if best[pair] != (cost, route):
            continue
        for name in names:
            nxt = tuple(sorted(permute_index(name, i) for i in pair))
            candidate = (cost + len(MACROS[name]), (name,) + route)
            if nxt not in best or candidate < best[nxt]:
                best[nxt] = candidate
                heappush(todo, (candidate[0], nxt, candidate[1]))
    assert len(best) == 28
    return {p: r for p, (_, r) in best.items()}


ROUTES = pair_routes()


def exchange(a, b):
    if a == b:
        return []
    route = [g for name in ROUTES[tuple(sorted((a, b)))] for g in MACROS[name]]
    return route + MACROS["CCX"] + route[::-1]


def sign(a):
    route = [g for t in range(3) if not a & (1 << t) for g in x(t)]
    return route + h(0) + MACROS["CCX"] + h(0) + route[::-1]


K0 = sign(0) + h(0) + h(1) + sign(0) + h(0) + h(1) + sign(0) + exchange(1, 2)


def route_targets(targets):
    current = list(range(4))
    route = []
    for wanted in targets:
        actual = current.pop(0)
        route = exchange(actual, wanted) + route
        current = [wanted if x == actual else actual if x == wanted else x for x in current]
    return route


def four(indices):
    route = route_targets(indices)
    return route + K0 + route[::-1]


def identity():
    return tuple(tuple(int(i == j) for j in range(N)) for i in range(N))


def normalize(k, a):
    while k >= 2 and all(x % 2 == 0 for row in a for x in row):
        k -= 2
        a = tuple(tuple(x // 2 for x in row) for row in a)
    return k, a


def matrix(word):
    """Product of gate matrices in written order, exactly."""
    k, a = 0, identity()
    for gate in word:
        kind, *args = gate
        if kind == "h":
            bit = 1 << args[0]
            a = tuple(tuple((row[j & ~bit] - row[j | bit]) if j & bit
                            else (row[j & ~bit] + row[j | bit])
                            for j in range(N)) for row in a)
            k += 1
        else:
            target = args[-1]
            controls = args[:-1]
            p = [j ^ (1 << target) if all(j & (1 << c) for c in controls) else j for j in range(N)]
            a = tuple(tuple(row[p[j]] for j in range(N)) for row in a)
        k, a = normalize(k, a)
    return k, a


def expected(kind, indices=()):
    a = [list(r) for r in identity()]
    if kind == "M":
        a[indices[0]][indices[0]] = -1
        return 0, tuple(tuple(r) for r in a)
    if kind == "X":
        i, j = indices
        a[i], a[j] = a[j], a[i]
        return 0, tuple(tuple(r) for r in a)
    if kind == "K":
        a = [[2 * v for v in r] for r in a]
        for i, row in enumerate(indices):
            for j, col in enumerate(indices):
                a[row][col] = (-1) ** ((i & j).bit_count() % 2)
        return 2, tuple(tuple(r) for r in a)
    if kind == "IH":
        return matrix(h(0))
    raise ValueError(kind)


def audit():
    for a in range(8):
        assert matrix(sign(a)) == expected("M", (a,)), ("M", a)
    for a, b in combinations(range(8), 2):
        assert matrix(exchange(a, b)) == expected("X", (a, b)), ("X", a, b)
    for indices in combinations(range(8), 4):
        assert matrix(four(indices)) == expected("K", indices), ("K", indices)
    assert matrix(h(0)) == expected("IH")
    # A wrong order/sign is detected: this is a real equality test.
    assert matrix(K0[:-1]) != expected("K", (0, 1, 2, 3))
    print("PASS: all 107 decoder images (8 M, 28 X, 70 K, 1 IH), exact integer arithmetic.")


HEADER = """------------------------------------------------------------------------
-- Presentations of groups
--
-- An explicit three-wire decoder for the scaled auxiliary presentation.
-- Generated by build_decoding.py; the generator also audits all 107
-- matrices exactly.  This file defines circuits, not semantic proofs.
--
-- Clément's back-and-forth method: signs, exchanges and four-level K
-- are decoded into X/CX/CCX/H circuits on the same three wires.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.ThreeQubit.Decoding where

open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Fin.Properties using (_≟_)
open import Data.List.Base using (List ; [] ; _∷_ ; map)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_<?_)
open import Relation.Nullary.Decidable using (yes ; no)
open import Notations using (₀ ; ₁ ; ₂ ; ₃)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T

reverse : ∀ {A : Set} → Word A → Word A
reverse [ g ]ʷ = [ g ]ʷ
reverse ε = ε
reverse (w • v) = reverse v • reverse w

X0 X1 X2 H0 H1 H2 C10 C21 C20 C01 C12 C02 : Circuit 3
X0 = X
X1 = X ↑
X2 = (X ↑) ↑
H0 = H
H1 = H ↑
H2 = (H ↑) ↑
C10 = CX
C21 = CX ↑
C20 = C21 • C10 • C21 • C10
C01 = H0 • H1 • C10 • H0 • H1
C12 = H1 • H2 • C21 • H1 • H2
C02 = H0 • H2 • C20 • H0 • H2

conjugate : Circuit 3 → Circuit 3 → Circuit 3
conjugate p w = p • w • reverse p

-- Table found by conjugating CCX along the orbit of the pair {6,7}.
exchange-table : ℕ → ℕ → Circuit 3
"""


TAIL = """
exchange-table _ _ = ε

realise-exchange : Fin 8 → Fin 8 → Circuit 3
realise-exchange a b with toℕ a <? toℕ b
... | yes _ = exchange-table (toℕ a) (toℕ b)
... | no _ = exchange-table (toℕ b) (toℕ a)

sign-table : ℕ → Circuit 3
"""


ENDING = """
sign-table _ = H0 • CCX • H0

realise-sign : Fin 8 → Circuit 3
realise-sign a = sign-table (toℕ a)

-- K on levels 0,1,2,3 and identity on the other four levels.
-- M0 Q M0 Q M0 is reflection in (-1,1,1,1,0,0,0,0)/2.
-- Multiplying by X_[1,2] gives K, with Q = H0 H1.
K0 : Circuit 3
K0 = sign-table 0 • H0 • H1 • sign-table 0 • H0 • H1 • sign-table 0 • exchange-table 1 2

data Atom : Set where
  sign : Fin 8 → Atom
  exchange : Fin 8 → Fin 8 → Atom
  k0 ih : Atom

realise : Atom → Circuit 3
realise (sign a) = realise-sign a
realise (exchange a b) = realise-exchange a b
realise k0 = K0
realise ih = H0

swap-index : Fin 8 → Fin 8 → Fin 8 → Fin 8
swap-index a b x with x ≟ a | x ≟ b
... | yes _ | _ = b
... | no _ | yes _ = a
... | no _ | no _ = x

-- Route the current images of the first four basis vectors to their
-- requested values.  The new exchange multiplies on the LEFT.
routing : List (Fin 8) → List (Fin 8) → Word Atom
routing [] _ = ε
routing (_ ∷ _) [] = ε
routing (x ∷ xs) (y ∷ ys) =
  routing (map (swap-index x y) xs) ys • [ exchange x y ]ʷ

route : Fin 8 → Fin 8 → Fin 8 → Fin 8 → Word Atom
route a b c d = routing (₀ ∷ ₁ ∷ ₂ ∷ ₃ ∷ []) (a ∷ b ∷ c ∷ d ∷ [])

plan : T.Genᴸ 8 → Word Atom
plan T.IH = [ ih ]ʷ
plan (T.⌊ U.M-gen a ⌋) = [ sign a ]ʷ
plan (T.⌊ U.X-gen a b p ⌋) = [ exchange a b ]ʷ
plan (T.⌊ U.K-gen a b c d p q r ⌋) =
  route a b c d • [ k0 ]ʷ • reverse (route a b c d)

d : T.Genᴸ 8 → Circuit 3
d g = (realise ʷ) (plan g)
"""


def generate():
    text = HEADER
    for (a, b), route in sorted(ROUTES.items()):
        p = " • ".join(route) if route else "ε"
        text += f"exchange-table {a} {b} = conjugate ({p}) CCX\n"
    text += TAIL
    for a in range(8):
        names = [f"X{t}" for t in range(3) if not a & (1 << t)]
        p = " • ".join(names) if names else "ε"
        text += f"sign-table {a} = conjugate ({p}) (H0 • CCX • H0)\n"
    text += ENDING
    Path(__file__).with_name("Decoding.agda").write_text(text, encoding="utf-8")


if __name__ == "__main__":
    audit()
    generate()

# The λ-calculus at control wire 4 for generators: for every pair of
# generators g, h of Circuit 4,
#   (F4) [X4, λg, X4, λh] = [λh, X4, λg, X4]
# and for every generator g
#   (F5) [g on wires 0..3] = [X4, λg, X4, λg],
# and X4 X4 = ε.  Derived from the joint paper's F4/F5 items when the
# pair has a CS (its images span five wires), by one window otherwise;
# Five/CalcAx gives them by cases on the generators (Five.Calc's
# parameters).
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lower5 as L5
from prim5 import Prim, gsupp, norm1
import transport5 as T5

X4 = ('X', 4)

# the generators of Gen 4 as Agda patterns, with their wire-level kind
def gen4():
    out = []
    for i in range(5):
        out.append(('gate₀ I-gate' + ' ↥' * i, ('I',), ('iI', i)))
    for w in range(4):
        out.append(('gate₁ S-gate' + ' ↥' * w, ('S', w), ('S', w)))
        out.append(('gate₁ K-gate' + ' ↥' * w, ('K', w), ('K', w)))
    for w in range(3):
        out.append(('gate₂ CS-gate' + ' ↥' * w, ('CS', w), ('CS', w, w + 1)))
    return out

def gname(g): return T5.gname(g)

def joint_name(g):
    """the joint paper's name of a generator (derivn.show)."""
    if g[0] == 'I': return 'iI'
    if g[0] == 'CS': return f'CS{g[1]}{g[1] + 1}'
    return f'{g[0]}{g[1]}'

def derive_f4(g, h):
    lhs = [X4, T5.lam1(g), X4, T5.lam1(h)]
    rhs = [T5.lam1(h), X4, T5.lam1(g), X4]
    name = f'calc F4 {gname(g)} {gname(h)}'
    if name in L5.LEMMAS: return name
    P = Prim(name, lhs, rhs, L5.LEMMAS)
    jn = f'F4 {joint_name(g)}^0|{joint_name(h)}^1'
    if jn in L5.JOINT:
        P.L(L5.instance(jn, {}), 0, True)
    else:
        assert len(gsupp(lhs) | gsupp(rhs)) <= 4, ('no F4 item', jn)
        L5.lower_window(P, 0, 4, rhs)
    P.done(); L5.PRIMS.append(P)
    return name

def derive_f5(g, dom):
    lhs = [norm1(dom)]
    rhs = [X4, T5.lam1(g), X4, T5.lam1(g)]
    name = f'calc F5 {gname(g)} {dom[1] if dom[0] == "iI" else ""}'.strip()
    if name in L5.LEMMAS: return name
    P = Prim(name, lhs, rhs, L5.LEMMAS)
    jn = f'F5 {joint_name(g)}'
    if g[0] == 'CS' and jn in L5.JOINT:
        nm = L5.instance(jn, {})
        P.L(nm, 0, L5.LEMMAS[nm][0] == lhs)
    else:
        assert len(gsupp(lhs) | gsupp(rhs)) <= 4, ('no F5 item', jn)
        L5.lower_window(P, 0, 1, rhs)
    P.done(); L5.PRIMS.append(P)
    return name

def derive_x4x4():
    name = 'calc x4x4'
    if name in L5.LEMMAS: return name
    P = Prim(name, [X4, X4], [], L5.LEMMAS)
    L5.lower_window(P, 0, 2, [])
    P.done(); L5.PRIMS.append(P)
    return name

def all_obligations():
    gs = gen4()
    f4 = {}
    for pg, g, _ in gs:
        for ph, h, _ in gs:
            f4[(pg, ph)] = derive_f4(g, h)
    f5 = {pg: derive_f5(g, dom) for pg, g, dom in gs}
    return f4, f5, derive_x4x4()

def agda_module(res, modof, lemname, MOD):
    f4, f5, xx = res
    deps = {}
    def use(name):
        deps.setdefault(modof[name], set()).add(lemname(name)); return f'{lemname(name)} c4'
    cl4 = [f'F4ᵍ c4 ({pg}) ({ph}) = {use(n)}' for (pg, ph), n in f4.items()]
    cl5 = [f'F5ᵍ c4 ({pg}) = {use(n)}' for pg, n in f5.items()]
    xxu = use(xx)
    NL = chr(10)
    dep_lines = NL.join(f'open import {MOD}.D.{m} using ({" ; ".join(sorted(ns))})' for m, ns in sorted(deps.items()))
    return f"""------------------------------------------------------------------------
-- Presentations of groups
--
-- The λ-calculus at control wire 4 for generators
--
-- (F4) λ⁰(g) and λ¹(h) commute, (F5) g is λ⁰(g) λ¹(g), for every pair
-- of generators of Circuit 4, and X on wire 4 squares to ε: the joint
-- paper's items when the pair has a CS, a window otherwise (the lemmas
-- `lem-calc-…` of Five.D).  `module At c4` instantiates Five.Calc.
-- Written by `scratchpad/five/calc5.py`.
------------------------------------------------------------------------

{{-# OPTIONS --without-K --safe #-}}

module {MOD}.CalcAx where

open import Data.List using (List ; [] ; _∷_)
open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import {MOD}.Chain
open import {MOD}.Lambda using (λ₁ ; λᵈ)
import {MOD}.Calc
{dep_lines}

F4ᵍ : Complete 4 → ∀ g h → ⟪ X4 ∷ λ₁ g ∷ X4 ∷ λ₁ h ∷ [] ⟫ʷ ≈ ⟪ λ₁ h ∷ X4 ∷ λ₁ g ∷ X4 ∷ [] ⟫ʷ
{NL.join(cl4)}

F5ᵍ : Complete 4 → ∀ g → ⟪ λᵈ g ∷ [] ⟫ʷ ≈ ⟪ X4 ∷ λ₁ g ∷ X4 ∷ λ₁ g ∷ [] ⟫ʷ
{NL.join(cl5)}

x4x4 : Complete 4 → ⟪ X4 ∷ X4 ∷ [] ⟫ʷ ≈ ε
x4x4 c4 = {xxu}

module At (c4 : Complete 4) = {MOD}.Calc (F4ᵍ c4) (F5ᵍ c4) (x4x4 c4)
"""

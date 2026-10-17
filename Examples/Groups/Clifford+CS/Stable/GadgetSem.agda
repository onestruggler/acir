------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding's gadgets denote their two-level blocks, at every width
--
-- Five.Facts4 gives each four-wire gadget's semantics: the two-level
-- operator of its block on the basis states 0 and e₀ (Five.Sem.TL.tl).
-- Under λ⁰ a two-level operator stays one, on the same states with the
-- top bit 0 (`ctrl⁰-tl`: the white control of an operator is its block
-- where the top wire reads 0, Semantics.Control.blk, and a two-level
-- operator read on bit vectors split at their last bit is that block),
-- so the gadget on 4 + m wires (Stable.GadgetSym.gad) denotes the block
-- on 0 and e₀ there (`gad-sem`) — the first half of the decoding's
-- semantics at every width, which Lemma 8.8 needs (Stable.HyperSem).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)

module Examples.Groups.Clifford+CS.Stable.GadgetSem
  (f4 : ∀ m → F4ᵗ m) (f5 : ∀ m → F5ᵗ m)
  (tr : ∀ m {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  (F : Facts4)
  where

open import Algebra.Bundles using (Monoid)
open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∧_)
open import Data.Bool.Properties using (∧-identityʳ ; ∧-assoc)
open import Data.Nat using (zero)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_ ; _∷ʳ_ ; initLast ; replicate)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₀ ; ₁₊ ; ₃₊)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_ ; up)
open import Examples.Groups.Clifford+CS.Semantics.Control using (blk ; ctrl⁰ ; ctrl⁰-~ ; sel)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ʷ)
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (λ⁰-sem)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqᵇ ; eqB)
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind ; blkOf ; o₄ ; e₄)
import Examples.Groups.Clifford+CS.Five.Sem.TL as TL
import Examples.Groups.Clifford+CS.Stable.GadgetSym as GadgetSym

open TL using (Blk ; tl ; tlOp)
open Facts4 F using (sem)

private
  module GS = GadgetSym f4 f5 tr F
  module R (n : ℕ) = SetoidR (Monoid.setoid (Scaled-monoid n))

------------------------------------------------------------------------
-- Bit vectors split at their last bit

private
  blk-snoc : ∀ {n} (P M : Op n) (x y : Bits n) (a b : Bool) →
             blk P M (x ∷ʳ a) (y ∷ʳ b) ≡ sel a b (P x y) (M x y)
  blk-snoc {₀}    P M []      []      a b = Eq.refl
  blk-snoc {₁₊ n} P M (u ∷ x) (v ∷ y) a b =
    blk-snoc {n} (λ s t → P (u ∷ s) (v ∷ t)) (λ s t → M (u ∷ s) (v ∷ t)) x y a b

  eqB-snoc : ∀ {n} (x p : Bits n) (a b : Bool) → eqB (x ∷ʳ a) (p ∷ʳ b) ≡ (eqB x p ∧ eqᵇ a b)
  eqB-snoc []      []      a b = ∧-identityʳ (eqᵇ a b)
  eqB-snoc (u ∷ x) (v ∷ p) a b =
    Eq.trans (Eq.cong (eqᵇ u v ∧_) (eqB-snoc x p a b)) (Eq.sym (∧-assoc (eqᵇ u v) (eqB x p) (eqᵇ a b)))

  if-same : ∀ (c : Bool) (z : 𝔽) → (if c then z else z) ≡ z
  if-same true  z = Eq.refl
  if-same false z = Eq.refl

  δb-snoc : ∀ {n} (x y : Bits n) (a b : Bool) → δb (x ∷ʳ a) (y ∷ʳ b) ≡ (if eqᵇ a b then δb x y else 0#)
  δb-snoc []          []          true  true  = Eq.refl
  δb-snoc []          []          false false = Eq.refl
  δb-snoc []          []          true  false = Eq.refl
  δb-snoc []          []          false true  = Eq.refl
  δb-snoc (true ∷ x)  (true ∷ y)  a b = δb-snoc x y a b
  δb-snoc (false ∷ x) (false ∷ y) a b = δb-snoc x y a b
  δb-snoc (true ∷ x)  (false ∷ y) a b = Eq.sym (if-same (eqᵇ a b) 0#)
  δb-snoc (false ∷ x) (true ∷ y)  a b = Eq.sym (if-same (eqᵇ a b) 0#)

  -- A two-level operator's entry, as a function of its tests.
  Ent : Blk → Bool → Bool → 𝔽 → 𝔽 → 𝔽 → 𝔽
  Ent B ep eq dp dq dx =
    if ep then Blk.a B * dp + Blk.b B * dq
    else if eq then Blk.c B * dp + Blk.d B * dq
    else γ^ Blk.k B * dx

  zero₂ : ∀ (u v : 𝔽) → u * 0# + v * 0# ≡ 0#
  zero₂ u v = Eq.trans (Eq.cong₂ _+_ (*-zeroʳ u) (*-zeroʳ v)) (+-identityʳ 0#)

  key : ∀ (B : Blk) (a b ep eq : Bool) (dp dq dx : 𝔽) →
        sel a b (Ent B ep eq dp dq dx) (γ^ Blk.k B * dx) ≡
        Ent B (ep ∧ eqᵇ a false) (eq ∧ eqᵇ a false)
              (if eqᵇ false b then dp else 0#) (if eqᵇ false b then dq else 0#) (if eqᵇ a b then dx else 0#)
  key B false false true  eq    dp dq dx = Eq.refl
  key B false false false true  dp dq dx = Eq.refl
  key B false false false false dp dq dx = Eq.refl
  key B true  true  true  true  dp dq dx = Eq.refl
  key B true  true  true  false dp dq dx = Eq.refl
  key B true  true  false true  dp dq dx = Eq.refl
  key B true  true  false false dp dq dx = Eq.refl
  key B false true  true  eq    dp dq dx = Eq.sym (zero₂ (Blk.a B) (Blk.b B))
  key B false true  false true  dp dq dx = Eq.sym (zero₂ (Blk.c B) (Blk.d B))
  key B false true  false false dp dq dx = Eq.sym (*-zeroʳ (γ^ Blk.k B))
  key B true  false true  true  dp dq dx = Eq.sym (*-zeroʳ (γ^ Blk.k B))
  key B true  false true  false dp dq dx = Eq.sym (*-zeroʳ (γ^ Blk.k B))
  key B true  false false true  dp dq dx = Eq.sym (*-zeroʳ (γ^ Blk.k B))
  key B true  false false false dp dq dx = Eq.sym (*-zeroʳ (γ^ Blk.k B))

  pt : ∀ {n} (B : Blk) (p q x y : Bits n) (a b : Bool) →
       blk (tlOp B p q) (scal (γ^ Blk.k B)) (x ∷ʳ a) (y ∷ʳ b) ≡ tlOp B (p ∷ʳ false) (q ∷ʳ false) (x ∷ʳ a) (y ∷ʳ b)
  pt B p q x y a b =
    Eq.trans (blk-snoc (tlOp B p q) (scal (γ^ Blk.k B)) x y a b)
      (Eq.trans (key B a b (eqB x p) (eqB x q) (δb p y) (δb q y) (δb x y))
        (Eq.sym (Eq.trans
          (Eq.cong₂ (λ u v → Ent B u v (δb (p ∷ʳ false) (y ∷ʳ b)) (δb (q ∷ʳ false) (y ∷ʳ b)) (δb (x ∷ʳ a) (y ∷ʳ b)))
                    (eqB-snoc x p a false) (eqB-snoc x q a false))
          (Eq.trans
            (Eq.cong₂ (λ u v → Ent B (eqB x p ∧ eqᵇ a false) (eqB x q ∧ eqᵇ a false) u v (δb (x ∷ʳ a) (y ∷ʳ b)))
                      (δb-snoc p y false b) (δb-snoc q y false b))
            (Eq.cong (λ u → Ent B (eqB x p ∧ eqᵇ a false) (eqB x q ∧ eqᵇ a false)
                                  (if eqᵇ false b then δb p y else 0#) (if eqᵇ false b then δb q y else 0#) u)
                     (δb-snoc x y a b))))))

-- The white control of a two-level operator is the two-level operator
-- on the same states with the top bit 0.
ctrl⁰-tl : ∀ {n} (B : Blk) (p q : Bits n) → ctrl⁰ (tl B p q) ~ tl B (p ∷ʳ false) (q ∷ʳ false)
ctrl⁰-tl B p q = ~-reflexive {l = Blk.k B} {Blk.k B} Eq.refl go
  where
  go : ∀ x y → blk (tlOp B p q) (scal (γ^ Blk.k B)) x y ≡ tlOp B (p ∷ʳ false) (q ∷ʳ false) x y
  go x y with initLast x | initLast y
  ... | x′ , a , Eq.refl | y′ , b , Eq.refl = pt B p q x′ y′ a b

------------------------------------------------------------------------
-- The gadgets

-- The basis states 0 and e₀ on 4 + m wires.
o e : ∀ m → Bits (₄₊ m)
o zero    = o₄
o (suc m) = o m ∷ʳ false
e zero    = e₄
e (suc m) = e m ∷ʳ false

private
  rep-snoc : ∀ k → (replicate k false ∷ʳ false) ≡ (false ∷ replicate k false)
  rep-snoc zero    = Eq.refl
  rep-snoc (suc k) = Eq.cong (false ∷_) (rep-snoc k)

-- They are the all-zero vector and the first unit vector.
o≡ : ∀ m → o m ≡ (false ∷ replicate (₃₊ m) false)
o≡ zero    = Eq.refl
o≡ (suc m) = Eq.trans (Eq.cong (_∷ʳ false) (o≡ m)) (Eq.cong (false ∷_) (rep-snoc (₃₊ m)))

e≡ : ∀ m → e m ≡ (true ∷ replicate (₃₊ m) false)
e≡ zero    = Eq.refl
e≡ (suc m) = Eq.trans (Eq.cong (_∷ʳ false) (e≡ m)) (Eq.cong (true ∷_) (rep-snoc (₃₊ m)))

-- The gadget on 4 + m wires denotes its block on 0 and e₀.
gad-sem : ∀ V m → ⟦ GS.gad V m ⟧ ~ tl (blkOf V) (o m) (e m)
gad-sem V zero    = sem V
gad-sem V (suc m) = begin
  ⟦ λ⁰ʷ (GS.gad V m) ⟧                 ≈⟨ λ⁰-sem (GS.gad V m) ⟩
  ctrl⁰ ⟦ GS.gad V m ⟧                 ≈⟨ ctrl⁰-~ {s = ⟦ GS.gad V m ⟧} {tl (blkOf V) (o m) (e m)} (gad-sem V m) ⟩
  ctrl⁰ (tl (blkOf V) (o m) (e m))     ≈⟨ ctrl⁰-tl (blkOf V) (o m) (e m) ⟩
  tl (blkOf V) (o (suc m)) (e (suc m)) ∎
  where open R (₄₊ (suc m))

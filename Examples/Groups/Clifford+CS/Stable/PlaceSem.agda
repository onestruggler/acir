------------------------------------------------------------------------
-- Presentations of groups
--
-- A placed gate denotes the gate's operator pulled back along the
-- network
--
-- The reversed network's bit map inverts the network's (`nb-revS`,
-- each letter's map being an involution), so conjugating by the two
-- permutation operators of Stable.NetSem pulls an operator back along
-- the bit map: pl σ g denotes ⟦ g ⟧ read at nb σ x, nb σ y (`pl-sem`).
-- The two letters the affine circuits place, X on wire 0 and CX₁₀, are
-- the permutation operators of their bit maps with any idle wires on
-- top (`X-sem`, `CX-sem`: one evaluation each on one and two wires, and
-- `top` for the rest, as for the exchange in NetSem).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.PlaceSem where

open import Algebra.Bundles using (Monoid)
open import Data.Bool using (Bool ; true ; false ; not ; _xor_)
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
import Data.Nat.Properties as NP
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_ ; _∷ʳ_)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Semantics.Control using (blk ; permOp ; flipL)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; X ; CX₁₀)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.PermCalc using (net ; revS)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl)
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (⟦•⟧ ; ⟦top⟧ ; topS ; topS-~ ; ∙-cong′)
open import Examples.Groups.Clifford+CS.Lambda.Checks using (check ; X-perm)
open import Examples.Groups.Clifford+CS.Stable.NetSem using (nb ; nbg ; sw01 ; net-sem ; topS-perm)
import Examples.Groups.Clifford+CS.Five.Sem.TL as TL

private
  variable
    n : ℕ

  module R (n : ℕ) = SetoidR (Monoid.setoid (Scaled-monoid n))

------------------------------------------------------------------------
-- The reversed network inverts the map

private
  nbg-invol : ∀ (g : S.Gen n) (x : Bits n) → nbg g (nbg g x) ≡ x
  nbg-invol (S.gate₀ ())
  nbg-invol (S.gate₁ ())
  nbg-invol (S.gate₂ S.σ-gate) (a ∷ b ∷ x) = Eq.refl
  nbg-invol (g S.↥) (a ∷ x) = Eq.cong (a ∷_) (nbg-invol g x)

  revS-revS : ∀ (u : Word (S.Gen n)) → revS (revS u) ≡ u
  revS-revS [ g ]ʷ  = Eq.refl
  revS-revS ε       = Eq.refl
  revS-revS (u • v) = Eq.cong₂ _•_ (revS-revS u) (revS-revS v)

nb-revS : ∀ (σ : Word (S.Gen n)) (x : Bits n) → nb (revS σ) (nb σ x) ≡ x
nb-revS [ g ]ʷ  x = nbg-invol g x
nb-revS ε       x = Eq.refl
nb-revS (u • v) x = Eq.trans (Eq.cong (nb (revS u)) (nb-revS v (nb u x))) (nb-revS u x)

nb-revS′ : ∀ (σ : Word (S.Gen n)) (x : Bits n) → nb σ (nb (revS σ) x) ≡ x
nb-revS′ σ x = Eq.subst (λ τ → nb τ (nb (revS σ) x) ≡ x) (revS-revS σ) (nb-revS (revS σ) x)

------------------------------------------------------------------------
-- A placement pulls back along the network

pl-sem : ∀ (σ : Word (S.Gen n)) (g : Circuit n) (l : ℕ) (M : Op n) → ⟦ g ⟧ ~ (l , M) →
         ⟦ pl σ g ⟧ ~ (l , λ x y → M (nb σ x) (nb σ y))
pl-sem {n} σ g l M e = begin
  ⟦ net σ • g • net (revS σ) ⟧
    ≈⟨ ⟦•⟧ (net σ) (g • net (revS σ)) ⟩
  ⟦ net σ ⟧ ∙ ⟦ g • net (revS σ) ⟧
    ≈⟨ ∙-cong′ ⟦ net σ ⟧ (0 , P) ⟦ g • net (revS σ) ⟧ ((l , M) ∙ (0 , P′)) (net-sem σ)
         (begin
            ⟦ g • net (revS σ) ⟧         ≈⟨ ⟦•⟧ g (net (revS σ)) ⟩
            ⟦ g ⟧ ∙ ⟦ net (revS σ) ⟧     ≈⟨ ∙-cong′ ⟦ g ⟧ (l , M) ⟦ net (revS σ) ⟧ (0 , P′) e (net-sem (revS σ)) ⟩
            (l , M) ∙ (0 , P′)           ∎) ⟩
  (0 , P) ∙ ((l , M) ∙ (0 , P′))
    ≈⟨ ~-reflexive {l = 0 +ℕ (l +ℕ 0)} {l} (NP.+-identityʳ l) op ⟩
  (l , λ x y → M (nb σ x) (nb σ y)) ∎
  where
  open R n
  P P′ : Op n
  P  = permOp (nb σ)
  P′ = permOp (nb (revS σ))
  op : (P ⊙ (M ⊙ P′)) ≐ (λ x y → M (nb σ x) (nb σ y))
  op x y =
    Eq.trans (Σ-δˡ (nb σ x) (λ z → (M ⊙ P′) z y))
      (Eq.trans (Σ-cong {f = λ w → M (nb σ x) w * δb (nb (revS σ) w) y} {g = λ w → M (nb σ x) w * δb w (nb σ y)}
                        (λ w → Eq.cong (M (nb σ x) w *_)
                                 (Eq.sym (TL.Bij.δ-move (nb σ) (nb (revS σ)) (nb-revS′ σ) (nb-revS σ) w y))))
                (Σ-δʳ (nb σ y) (λ w → M (nb σ x) w)))

------------------------------------------------------------------------
-- The placed letters

-- X on wire 0, and CX from wire 1 onto wire 0, as bit maps.
fl0 : Bits (₁₊ n) → Bits (₁₊ n)
fl0 (a ∷ x) = not a ∷ x

cx0 : Bits (₂₊ n) → Bits (₂₊ n)
cx0 (a ∷ b ∷ x) = (a xor b) ∷ b ∷ x

private
  fl-one : ∀ (x : Bits 1) → flipL {0} x ≡ fl0 x
  fl-one (a ∷ []) = Eq.refl

  fl-snoc : ∀ (x : Bits (₁₊ n)) (a : Bool) → fl0 (x ∷ʳ a) ≡ fl0 x ∷ʳ a
  fl-snoc (u ∷ x) a = Eq.refl

  cx-snoc : ∀ (x : Bits (₂₊ n)) (a : Bool) → cx0 (x ∷ʳ a) ≡ cx0 x ∷ʳ a
  cx-snoc (u ∷ v ∷ x) a = Eq.refl

X-sem : ∀ r → ⟦ X {r} ⟧ ~ (0 , permOp (fl0 {r}))
X-sem zero =
  ~-trans {s = ⟦ X {0} ⟧} {0 , permOp flipL} {0 , permOp fl0} X-perm
    (~-reflexive {l = 0} {0} Eq.refl (λ x y → Eq.cong (λ z → δb z y) (fl-one x)))
X-sem (suc r) = begin
  ⟦ top (X {r}) ⟧                         ≈⟨ ⟦top⟧ (X {r}) ⟩
  topS ⟦ X {r} ⟧                          ≈⟨ topS-~ {s = ⟦ X {r} ⟧} {0 , permOp fl0} (X-sem r) ⟩
  (0 , blk (permOp fl0) (permOp fl0))     ≈⟨ ~-reflexive {l = 0} {0} Eq.refl (topS-perm fl0 fl0 fl-snoc) ⟩
  (0 , permOp (fl0 {suc r}))              ∎
  where open R (₁₊ (suc r))

CX-sem : ∀ r → ⟦ CX₁₀ {r} ⟧ ~ (0 , permOp (cx0 {r}))
CX-sem zero    = check (CX₁₀ {0}) 0 (permOp cx0) Eq.refl
CX-sem (suc r) = begin
  ⟦ top (CX₁₀ {r}) ⟧                      ≈⟨ ⟦top⟧ (CX₁₀ {r}) ⟩
  topS ⟦ CX₁₀ {r} ⟧                       ≈⟨ topS-~ {s = ⟦ CX₁₀ {r} ⟧} {0 , permOp cx0} (CX-sem r) ⟩
  (0 , blk (permOp cx0) (permOp cx0))     ≈⟨ ~-reflexive {l = 0} {0} Eq.refl (topS-perm cx0 cx0 cx-snoc) ⟩
  (0 , permOp (cx0 {suc r}))              ∎
  where open R (₂₊ (suc r))

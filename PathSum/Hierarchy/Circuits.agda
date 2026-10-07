------------------------------------------------------------------------
-- Presentations of groups
--
-- Clifford circuits implement Clifford operators
--
-- "Clifford" is a syntactic class elsewhere in PathSum: circuits over
-- {H, S, CZ} (PathSum.Circuit), and circuits over {H, CNOT, R_k,
-- R_k†} of level ≤ 2 (PathSum.CRK.Circuit's level, the largest k of
-- an R_k or R_k†), which is what corollary 4.4 and the Gaussian
-- elimination of PathSum.Gauss are about.  The paper's Clifford group
-- C₂ is semantic.  Here the first is shown to lie in the second: the
-- operator ⟪ ⟦ C ⟧ ⟫ of the path-sum of every such circuit -- the
-- operator the development verifies -- is in 𝒞 2 (crk-𝒞₂,
-- clifford-𝒞₂).
--
-- The path-sum of a one-gate circuit is that gate's operator of
-- PathSum.Hierarchy.Gates (crk-gate, clifford-gate: proposition 2.10,
-- PathSum.CRK.Semantics and PathSum.CircuitSemantics), the path-sum of
-- g ∷ C is the product of those of C and of g (⟦∷⟧: definition 2.9's
-- ⟦C₁;C₂⟧ = ⟦C₂⟧ ∘ ⟦C₁⟧, PathSum.Compose.CRK and
-- PathSum.Compose.Clifford, read as a product of matrices by
-- proposition 2.7, PathSum.Compose.Matrix), and 𝒞 2 is closed under
-- products and contains I.  Each gate of level ≤ 2 is in 𝒞 2: H and
-- CNOT, R_0 = I, R_1 = Z and R_1† = Z, R_2 = S and R_2† = S†; and S
-- and CZ of the other gate set.
--
-- Level ≤ 2 cannot be weakened to level ≤ 3 with 𝒞 3: C₃ is not closed
-- under products (PathSum.Hierarchy.NotClosed: T H T has level 3 and is
-- not in C₃).  Only k = 3 is proved; for k > 3 the analogous statement
-- is not formalised.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.Circuits (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; -1ℤ; +_; -_; _*_)
open import Data.Integer.Properties using (neg-distribˡ-*)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (zero; _≤_; _∸_; _⊔_; z≤n; s≤s)
  renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

import Data.Nat.Properties as ℕ

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Compose.Matrix M₀ using (prop-2-7)
open import PathSum.Cyclotomic M₀ using (Amp; _≐_; rot-exp)
open import PathSum.Hierarchy M₀
open import PathSum.Hierarchy.Gates M₀
open import PathSum.Hierarchy.Levels M₀
open import PathSum.Hierarchy.Operator M₀
open import PathSum.Hierarchy.Pauli M₀ using (M; pow; ¼)

import PathSum.CircuitSemantics M₀ as ClS
import PathSum.Compose.Clifford M₀ as ClC
import PathSum.Compose.CRK M₀ as KC
import PathSum.CRK.Semantics M₀ as KS

-- The two gate sets.  These module applications are exported, and
-- the modules about circuits below use them rather than their own:
-- two applications of PathSum.CRK.Circuit M are two sets of names,
-- and Agda compares a circuit's path-sum under one with the same
-- path-sum under the other by computing both.

import PathSum.Circuit
import PathSum.CRK.Circuit

module Cl = PathSum.Circuit M
module K = PathSum.CRK.Circuit M

open +-*-Solver using (solve; con; :-_; _:*_; _:=_)

private
  variable
    n : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)


------------------------------------------------------------------------
-- {H, CNOT, R_k, R_k†}

-- The operator of each gate.

crkOp : K.Gate n → Op n
crkOp (K.H w)        = hadOp w
crkOp (K.CNOT c t _) = cnotOp c t
crkOp (K.R k w)      = Rs (ρ false k) w
crkOp (K.R† k w)     = Rs (ρ true k) w

-- It is the operator of the gate's path-sum (proposition 2.10).

crk-gate : (g : K.Gate n) → ⟪ K.⟦ g ∷ [] ⟧ ⟫ ≈ crkOp g
crk-gate (K.H w) = ≈-by ⟪ K.⟦ K.H w ∷ [] ⟧ ⟫ (hadOp w) refl
  (λ x z → KS.prop-2-10 (K.H w ∷ []) x z)
crk-gate (K.CNOT c t p) = ≈-by ⟪ K.⟦ K.CNOT c t p ∷ [] ⟧ ⟫ (cnotOp c t) refl
  (λ x z → KS.prop-2-10 (K.CNOT c t p ∷ []) x z)
crk-gate (K.R k w) = ≈-by ⟪ K.⟦ K.R k w ∷ [] ⟧ ⟫ (Rs (ρ false k) w) refl
  (λ x z → KS.prop-2-10 (K.R k w ∷ []) x z
           ∙ rot-exp {pow (M ∸ k) * [ z w ]ᶻ} {ρ false k * [ z w ]ᶻ}
                     (δ x z) (cong (_* [ z w ]ᶻ) (sym (ρ-def false k))))
crk-gate (K.R† k w) = ≈-by ⟪ K.⟦ K.R† k w ∷ [] ⟧ ⟫ (Rs (ρ true k) w) refl
  (λ x z → KS.prop-2-10 (K.R† k w ∷ []) x z
           ∙ rot-exp { - (pow (M ∸ k) * [ z w ]ᶻ)} {ρ true k * [ z w ]ᶻ}
                     (δ x z)
                     (trans (neg-distribˡ-* (pow (M ∸ k)) [ z w ]ᶻ)
                            (cong (_* [ z w ]ᶻ) (sym (ρ-def true k)))))

-- The empty circuit is the identity, and a gate followed by a
-- circuit is the product (definition 2.9 and proposition 2.7).

crk-[] : ⟪ K.⟦_⟧ {n} [] ⟫ ≈ I
crk-[] = ≈-by ⟪ K.⟦ [] ⟧ ⟫ I refl (λ x z → KS.prop-2-10 [] x z)

crk-∷ : (g : K.Gate n) (C : K.Circuit n) →
        ⟪ K.⟦ g ∷ C ⟧ ⟫ ≈ ⟪ K.⟦ C ⟧ ⟫ · ⟪ K.⟦ g ∷ [] ⟧ ⟫
crk-∷ g C = ≈-by ⟪ K.⟦ g ∷ C ⟧ ⟫ (⟪ K.⟦ C ⟧ ⟫ · ⟪ K.⟦ g ∷ [] ⟧ ⟫)
  (trans (KC.norm-++ (g ∷ []) C) (ℕ.+-comm (K.norm (g ∷ [])) (K.norm C)))
  (λ x z → KC.amp-⟦++⟧ (g ∷ []) C x z
           ∙ prop-2-7 K.⟦ C ⟧ K.⟦ g ∷ [] ⟧ x z)

-- The gates of level ≤ 2 are Cliffords.
--
-- (A note on the proofs: two 𝒞 2 types are compared by unfolding their
-- operators, proofs of RespectsM included, whenever they are not
-- syntactically equal -- even when they differ only by a literal 2
-- against suc (suc zero).  So every conversion below is made at the
-- level of ≈, between operators that are equal after one unfolding,
-- with 𝒞-resp's operators given explicitly.)

private
  Rσ∈𝒞 : (σ : Bool) (k : ℕ) (w : Fin n) → 1 ≤ k → 𝒞 k (Rs (ρ σ k) w)
  Rσ∈𝒞 false = R∈𝒞
  Rσ∈𝒞 true  = R†∈𝒞

  R₀ : (σ : Bool) (k : ℕ) (w : Fin n) → k ≡ 0 → Rs (ρ σ k) w ≈ I
  R₀ σ _ w refl = R₀≈I σ w

  R-small : (σ : Bool) (k : ℕ) (w : Fin n) → k ≤ 2 → 𝒞 2 (Rs (ρ σ k) w)
  R-small σ zero    w _       =
    𝒞-resp 2 {I} {Rs (ρ σ zero) w} (≈-sym (R₀ σ zero w refl)) (𝒞-I 1)
  R-small σ (suc j) w (s≤s h) =
    𝒞-mono⁺ {j = j} {k = 1} {U = Rs (ρ σ (suc j)) w} h
            (Rσ∈𝒞 σ (suc j) w (s≤s z≤n))

crk-gate-𝒞₂ : (g : K.Gate n) → K.level (g ∷ []) ≤ 2 → 𝒞 2 (crkOp g)
crk-gate-𝒞₂ (K.H w)          _ =
  𝒞-resp 2 {hadOp w} {crkOp (K.H w)} ≈-refl (had-𝒞₂ w)
crk-gate-𝒞₂ (K.CNOT c t c≢t) _ =
  𝒞-resp 2 {cnotOp c t} {crkOp (K.CNOT c t c≢t)} ≈-refl (cnot-𝒞₂ c t c≢t)
crk-gate-𝒞₂ (K.R k w)        h =
  𝒞-resp 2 {Rs (ρ false k) w} {crkOp (K.R k w)} ≈-refl
           (R-small false k w (ℕ.m⊔n≤o⇒m≤o k 0 h))
crk-gate-𝒞₂ (K.R† k w)       h =
  𝒞-resp 2 {Rs (ρ true k) w} {crkOp (K.R† k w)} ≈-refl
           (R-small true k w (ℕ.m⊔n≤o⇒m≤o k 0 h))

private
  split : (g : K.Gate n) (C : K.Circuit n) → K.level (g ∷ C) ≤ 2 →
          K.level (g ∷ []) ≤ 2 × K.level C ≤ 2
  split (K.H _)        C h = z≤n , h
  split (K.CNOT _ _ _) C h = z≤n , h
  split (K.R k _)      C h =
    ℕ.⊔-lub (ℕ.m⊔n≤o⇒m≤o k (K.level C) h) z≤n , ℕ.m⊔n≤o⇒n≤o k (K.level C) h
  split (K.R† k _)     C h =
    ℕ.⊔-lub (ℕ.m⊔n≤o⇒m≤o k (K.level C) h) z≤n , ℕ.m⊔n≤o⇒n≤o k (K.level C) h

-- Every circuit of level ≤ 2 over {H, CNOT, R_k, R_k†} implements a
-- Clifford operator.

crk-𝒞₂ : (C : K.Circuit n) → K.level C ≤ 2 → 𝒞 2 ⟪ K.⟦ C ⟧ ⟫
crk-𝒞₂ {n} []  _ =
  𝒞-resp 2 {I} {⟪ K.⟦_⟧ {n} [] ⟫} (≈-sym crk-[]) (𝒞-I 1)
crk-𝒞₂ (g ∷ C) h =
  𝒞-resp 2 {⟪ K.⟦ C ⟧ ⟫ · ⟪ K.⟦ g ∷ [] ⟧ ⟫} {⟪ K.⟦ g ∷ C ⟧ ⟫}
    (≈-sym (crk-∷ g C))
    (𝒞₂-· {U = ⟪ K.⟦ C ⟧ ⟫} {V = ⟪ K.⟦ g ∷ [] ⟧ ⟫}
          (crk-𝒞₂ C (proj₂′ (split g C h)))
          (𝒞-resp 2 {crkOp g} {⟪ K.⟦ g ∷ [] ⟧ ⟫} (≈-sym (crk-gate g))
                    (crk-gate-𝒞₂ g (proj₁′ (split g C h)))))
  where
  proj₁′ : ∀ {A B : Set} → A × B → A
  proj₁′ (a , _) = a
  proj₂′ : ∀ {A B : Set} → A × B → B
  proj₂′ (_ , b) = b


------------------------------------------------------------------------
-- {H, S, CZ}

cliffordOp : Cl.Gate n → Op n
cliffordOp (Cl.H w)    = hadOp w
cliffordOp (Cl.S w)    = Rs (ρ false 2) w
cliffordOp (Cl.CZ w v) = diagOp (czFn w v)

clifford-gate : (g : Cl.Gate n) → ⟪ Cl.⟦ g ∷ [] ⟧ ⟫ ≈ cliffordOp g
clifford-gate (Cl.H w) = ≈-by ⟪ Cl.⟦ Cl.H w ∷ [] ⟧ ⟫ (hadOp w) refl
  (λ x z → ClS.prop-2-10 (Cl.H w ∷ []) x z)
clifford-gate (Cl.S w) = ≈-by ⟪ Cl.⟦ Cl.S w ∷ [] ⟧ ⟫ (Rs (ρ false 2) w) refl
  (λ x z → ClS.prop-2-10 (Cl.S w ∷ []) x z
           ∙ rot-exp {¼ * [ z w ]ᶻ} {ρ false 2 * [ z w ]ᶻ}
                     (δ x z) (cong (_* [ z w ]ᶻ) (sym (ρ-def false 2))))
clifford-gate (Cl.CZ w v) =
  ≈-by ⟪ Cl.⟦ Cl.CZ w v ∷ [] ⟧ ⟫ (diagOp (czFn w v)) refl
    (λ x z → ClS.prop-2-10 (Cl.CZ w v ∷ []) x z)

clifford-[] : ⟪ Cl.⟦_⟧ {n} [] ⟫ ≈ I
clifford-[] = ≈-by ⟪ Cl.⟦ [] ⟧ ⟫ I refl (λ x z → ClS.prop-2-10 [] x z)

clifford-∷ : (g : Cl.Gate n) (C : Cl.Circuit n) →
             ⟪ Cl.⟦ g ∷ C ⟧ ⟫ ≈ ⟪ Cl.⟦ C ⟧ ⟫ · ⟪ Cl.⟦ g ∷ [] ⟧ ⟫
clifford-∷ g C = ≈-by ⟪ Cl.⟦ g ∷ C ⟧ ⟫ (⟪ Cl.⟦ C ⟧ ⟫ · ⟪ Cl.⟦ g ∷ [] ⟧ ⟫)
  (trans (ClC.norm-++ (g ∷ []) C) (ℕ.+-comm (Cl.norm (g ∷ [])) (Cl.norm C)))
  (λ x z → ClC.amp-⟦++⟧ (g ∷ []) C x z
           ∙ prop-2-7 Cl.⟦ C ⟧ Cl.⟦ g ∷ [] ⟧ x z)

clifford-gate-𝒞₂ : (g : Cl.Gate n) → 𝒞 2 (cliffordOp g)
clifford-gate-𝒞₂ (Cl.H w)    =
  𝒞-resp 2 {hadOp w} {cliffordOp (Cl.H w)} ≈-refl (had-𝒞₂ w)
clifford-gate-𝒞₂ (Cl.S w)    =
  𝒞-resp 2 {Rs (ρ false 2) w} {cliffordOp (Cl.S w)} ≈-refl
           (R∈𝒞 2 w (s≤s z≤n))
clifford-gate-𝒞₂ (Cl.CZ w v) =
  𝒞-resp 2 {diagOp (czFn w v)} {cliffordOp (Cl.CZ w v)} ≈-refl (cz-𝒞₂ w v)

-- Every circuit over {H, S, CZ} implements a Clifford operator.

clifford-𝒞₂ : (C : Cl.Circuit n) → 𝒞 2 ⟪ Cl.⟦ C ⟧ ⟫
clifford-𝒞₂ {n} [] =
  𝒞-resp 2 {I} {⟪ Cl.⟦_⟧ {n} [] ⟫} (≈-sym clifford-[]) (𝒞-I 1)
clifford-𝒞₂ (g ∷ C) =
  𝒞-resp 2 {⟪ Cl.⟦ C ⟧ ⟫ · ⟪ Cl.⟦ g ∷ [] ⟧ ⟫} {⟪ Cl.⟦ g ∷ C ⟧ ⟫}
    (≈-sym (clifford-∷ g C))
    (𝒞₂-· {U = ⟪ Cl.⟦ C ⟧ ⟫} {V = ⟪ Cl.⟦ g ∷ [] ⟧ ⟫}
          (clifford-𝒞₂ C)
          (𝒞-resp 2 {cliffordOp g} {⟪ Cl.⟦ g ∷ [] ⟧ ⟫} (≈-sym (clifford-gate g))
                    (clifford-gate-𝒞₂ g)))

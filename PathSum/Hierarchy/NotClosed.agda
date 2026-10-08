------------------------------------------------------------------------
-- Presentations of groups
--
-- C₃ is not closed under products: T H T
--
-- The Clifford group C₂ is a group (PathSum.Hierarchy's 𝒞₂-·), but
-- the higher levels of the hierarchy are not: T = R_3 and H are in C₃
-- (PathSum.Hierarchy.Levels), and so is T H (C₃ is closed under
-- multiplying by a Clifford on the right), but T H T is not (THT∉𝒞₃).
-- Since T H T is the circuit T ; H ; T, of level 3, the syntactic
-- class "level ≤ k" is not contained in C_k for k = 3 -- unlike
-- k = 2 (PathSum.Hierarchy.Circuits).  The paper's preliminaries say
-- "Clifford+T (C₃)" and "for k ≤ 3 the above gates suffice to generate
-- C_k"; read literally (C_k the group the gates generate), this fails
-- at k = 3, since C₃ is not a group and the Clifford+T group contains
-- T H T ∉ C₃, so "Clifford+T (C₃)" misnames C₃ -- and at k = 1 as well,
-- since H ∉ C₁ (PathSum.Hierarchy.Levels).  The charitable reading,
-- that every element of C_k is a product of the gates up to a global
-- phase, is formalised only for n = 1 and k = 2
-- (PathSum.Hierarchy.OneQubit); for n-qubit C₂ and for C₃ it is not.
--
-- The proof follows conjugates through the gates' actions on the
-- Paulis, on any wire w of n qubits and for every precision M.  With
-- V = (T H T) X (T H T)† and K = H S H†:
--
--   T X T† = ζ^(-⅛) S X                 (R_3 conjugates X to R_2)
--   V      = ζ^(-⅛) T (K Z) T†          (H X H† = Z)
--   V Z V† = T (K Z K†) T†              (T commutes with Z; Z Z Z† = Z)
--   K Z K† = H (S X S†) H† = H (ζ^(-¼) Z X) H† = ζ^(-¼) X Z
--   V Z V† = ζ^(-¼-⅛) S X Z             (T (X Z) T† = ζ^(-⅛) S X Z)
--
-- If T H T were in C₃, V would be in C₂ and V Z V† a Pauli; multiplying
-- by (X Z)† on the right, ζ^(-¼-⅛) S would be a Pauli, which it is not
-- (PathSum.Hierarchy.Levels's S∉𝒞₁: S is not a Pauli up to any phase).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.NotClosed (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _xor_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _*_)
open import Data.Integer.Properties using (*-zeroʳ; neg-distribˡ-*)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Assign using ([_]ᶻ; ≔-here)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Cyclotomic M₀ using (rot-exp)
open import PathSum.Hierarchy.Circuits M₀
open import PathSum.Hierarchy.Pauli M₀

import PathSum.Hierarchy
import PathSum.Hierarchy.Gates
import PathSum.Hierarchy.Levels
import PathSum.Hierarchy.Operator

-- The applications the statements below are written with are named, so
-- that a client can restate them with the very same names
-- (PathSum.Hierarchy.NotClosed.Hrⁿ.𝒞 M₀ and so on; see the header of
-- PathSum.Hierarchy).

module Hrⁿ = PathSum.Hierarchy M₀
module Gaⁿ = PathSum.Hierarchy.Gates M₀
module Lvⁿ = PathSum.Hierarchy.Levels M₀
module Opⁿ = PathSum.Hierarchy.Operator M₀

open Hrⁿ
open Gaⁿ
open Lvⁿ
open Opⁿ



------------------------------------------------------------------------
-- The pieces

-- T = R_3 and S = R_2 have the opaque phases ρ false 3 and ρ false 2
-- of PathSum.Hierarchy.Levels (2^(M-3) and 2^(M-2)), written so
-- throughout: an abbreviation for either would leave two spellings of
-- one exponent, and Agda compares those by unfolding the rotations.

-- A circuit whose operator is not in C₃.  Statements about a concrete
-- circuit go through this name and a name for the circuit: restating
-- ¬ 𝒞 3 ⟪ K.⟦ T ; H ; T ⟧ ⟫ in another module and comparing it with
-- the statement here took Agda 13 minutes, and Not𝒞₃ (T ; H ; T)
-- written out in both 14 (it computes the circuit's path-sum inside
-- 𝒞 3), while Not𝒞₃ C, for a variable C, and Not𝒞₃ of the circuit's
-- name compare at once.

Not𝒞₃ : {n : ℕ} → K.Circuit n → Set
Not𝒞₃ C = ¬ 𝒞 3 ⟪ K.⟦ C ⟧ ⟫

module _ {n : ℕ} (w : Fin n) where

  private
    T S H X Z : Op n
    T = Rs (ρ false 3) w
    S = Rs (ρ false 2) w
    H = hadOp w
    X = pauli (X^ w)
    Z = pauli (Z^ w)

    uT : Unitary T
    uT = diag-unitary (wireFn (ρ false 3) w)

    uH : Unitary H
    uH = had-unitary w

    e-here : eᵛ w w ≡ true
    e-here = ≔-here 0ᵛ w true

    2t : (+ 2) * (ρ false 3) ≡ (ρ false 2)
    2t = ρ-double false 1 (s≤s (s≤s (s≤s z≤n)))

    2s : (+ 2) * (ρ false 2) ≡ ½
    2s = trans (ρ-double false 0 (s≤s (s≤s z≤n))) (ρ-def false 1)

    -- T X T† = ζ^(-⅛) S X, and T Z T† = Z.

    TXT : T · X · T † ≈ (- (ρ false 3)) ◃ (S · X)
    TXT = Rs-conj-1 (ρ false 3) w (X^ w) e-here
          ⟨≈⟩ ◃-cong (- (ρ false 3))
                (·-congˡ X (Rs-exp {a = (+ 2) * (ρ false 3)} {b = ρ false 2}
                                   w 2t))

    TZT : T · Z · T † ≈ Z
    TZT = Rs-conj-0 (ρ false 3) w (Z^ w) refl

    -- T† Z T = Z: T† is the opposite phase.

    T†≈ : T † ≈ Rs (- (ρ false 3)) w
    T†≈ = diag-† (wireFn (ρ false 3) w)
          ⟨≈⟩ ≈-by (diagOp (negFn (wireFn (ρ false 3) w)))
                   (Rs (- (ρ false 3)) w) refl (λ x z →
                rot-exp { - (ρ false 3 * [ z w ]ᶻ)} {(- (ρ false 3)) * [ z w ]ᶻ}
                        (δ x z) (neg-distribˡ-* (ρ false 3) [ z w ]ᶻ))

    T†ZT : T † · Z · T † † ≈ Z
    T†ZT = conj-cong T†≈ Z ⟨≈⟩ Rs-conj-0 (- (ρ false 3)) w (Z^ w) refl

    -- S X S† = ζ^(-¼) Z X.

    SXS : S · X · S † ≈ (- (ρ false 2)) ◃ (Z · X)
    SXS = Rs-conj-1 (ρ false 2) w (X^ w) e-here
          ⟨≈⟩ ◃-cong (- (ρ false 2))
                (·-congˡ X (Rs-exp {a = (+ 2) * (ρ false 2)} {b = ½} w 2s
                            ⟨≈⟩ Rs-½ w))

    -- H X H† = Z, H Z H† = X, and H† Z H = X.

    HXH : H · X · H † ≈ Z
    HXH = intertwine⇒conj H X Z uH (had-X w)

    HZH : H · Z · H † ≈ X
    HZH = intertwine⇒conj H Z X uH (had-Z w)

    H†ZH : H † · Z · H † † ≈ X
    H†ZH = conj-cong (had-† w) Z ⟨≈⟩ HZH

    -- Z Z Z† = Z.

    ZZZ : Z · Z · Z † ≈ Z
    ZZZ = pauli-conj (Z^ w) (Z^ w)
          ⟨≈⟩ ◃-exp {e = ½ * [ ω (Z^ w) (Z^ w) ]ᶻ} {e′ = 0ℤ} Z
                    (trans (cong (λ b → ½ * [ b ]ᶻ) ωZZ) (*-zeroʳ ½))
          ⟨≈⟩ ◃-0 Z
      where
      ωZZ : ω (Z^ w) (Z^ w) ≡ false
      ωZZ = cong₂ _xor_ (dot-0ʳ (eᵛ w) 0ᵛ (λ _ → refl))
                        (dot-0ʳ (eᵛ w) 0ᵛ (λ _ → refl))

    K : Op n
    K = H · S · H †

    -- K Z K† = ζ^(-¼) X Z.

    KZK : K · Z · K † ≈ (- (ρ false 2)) ◃ (X · Z)
    KZK = conj-· (H · S) (H †) Z
          ⟨≈⟩ conj-congᴾ (H · S) H†ZH
          ⟨≈⟩ conj-· H S X
          ⟨≈⟩ conj-congᴾ H SXS
          ⟨≈⟩ conj-◃ (- (ρ false 2)) H (Z · X)
          ⟨≈⟩ ◃-cong (- (ρ false 2)) (conj-split H Z X uH ⟨≈⟩ ·-cong HZH HXH)

    -- T (X Z) T† = ζ^(-⅛) S X Z.

    TXZT : T · (X · Z) · T † ≈ (- (ρ false 3)) ◃ (S · (X · Z))
    TXZT = conj-split T X Z uT
           ⟨≈⟩ ·-cong TXT TZT
           ⟨≈⟩ ◃-·ˡ (- (ρ false 3)) (S · X) Z
           ⟨≈⟩ ◃-cong (- (ρ false 3)) (·-assoc S X Z)

    W : Op n
    W = T · H · T

    A : Op n
    A = T · (K · Z) · T †

    -- V = ζ^(-⅛) A.

    V≈ : W · X · W † ≈ (- (ρ false 3)) ◃ A
    V≈ = conj-· (T · H) T X
         ⟨≈⟩ conj-· T H (T · X · T †)
         ⟨≈⟩ conj-congᴾ T
               (conj-congᴾ H TXT
                ⟨≈⟩ conj-◃ (- (ρ false 3)) H (S · X)
                ⟨≈⟩ ◃-cong (- (ρ false 3)) (conj-split H S X uH
                                            ⟨≈⟩ ·-congʳ K HXH))
         ⟨≈⟩ conj-◃ (- (ρ false 3)) T (K · Z)

    e₀ : ℤ
    e₀ = - (ρ false 2) + - (ρ false 3)

    -- A Z A† = ζ^(-¼-⅛) S X Z.

    AZA : A · Z · A † ≈ e₀ ◃ (S · (X · Z))
    AZA = conj-· (T · (K · Z)) (T †) Z
          ⟨≈⟩ conj-congᴾ (T · (K · Z)) T†ZT
          ⟨≈⟩ conj-· T (K · Z) Z
          ⟨≈⟩ conj-congᴾ T (conj-· K Z Z ⟨≈⟩ conj-congᴾ K ZZZ ⟨≈⟩ KZK)
          ⟨≈⟩ conj-◃ (- (ρ false 2)) T (X · Z)
          ⟨≈⟩ ◃-cong (- (ρ false 2)) TXZT
          ⟨≈⟩ ◃-◃ (- (ρ false 2)) (- (ρ false 3)) (S · (X · Z))

    VZV : W · X · W † · Z · (W · X · W †) † ≈ e₀ ◃ (S · (X · Z))
    VZV = conj-cong V≈ Z ⟨≈⟩ ◃-conj (- (ρ false 3)) A Z ⟨≈⟩ AZA

    -- X Z is the Pauli P(0, e_w, e_w), so multiplying by its adjoint on
    -- the right cancels it.

    q : PauliData n
    q = X^ w ∙ᴾ Z^ w

    cancel : e₀ ◃ (S · (X · Z)) · pauli (q ⁻¹ᴾ) ≈ e₀ ◃ S
    cancel = ◃-·ˡ e₀ (S · (X · Z)) (pauli (q ⁻¹ᴾ))
             ⟨≈⟩ ◃-cong e₀
                   (·-assoc S (X · Z) (pauli (q ⁻¹ᴾ))
                    ⟨≈⟩ ·-congʳ S (·-cong (pauli-· (X^ w) (Z^ w))
                                          (≈-sym (pauli-† q))
                                   ⟨≈⟩ proj₂ (pauli-unitary q))
                    ⟨≈⟩ ·-identityʳ S)

  -- T H T is not in C₃.

  THT∉𝒞₃ : ¬ 𝒞 3 (Rs (ρ false 3) w · hadOp w · Rs (ρ false 3) w)
  THT∉𝒞₃ (_ , h) =
    S∉𝒞₁ w e₀
      (𝒞-resp 1 cancel
        (𝒞-·pauli 0 {e₀ ◃ (S · (X · Z))} (q ⁻¹ᴾ)
          (𝒞-resp 1 VZV (proj₂ (h (X^ w)) (Z^ w)))))

  -- T and T H are in C₃, and their product T H T is not.

  𝒞₃-not-closed : 𝒞 3 (Rs (ρ false 3) w · hadOp w) × 𝒞 3 (Rs (ρ false 3) w) ×
                  ¬ 𝒞 3 (Rs (ρ false 3) w · hadOp w · Rs (ρ false 3) w)
  𝒞₃-not-closed =
    𝒞-·₂ 1 {Rs (ρ false 3) w} {hadOp w} (R∈𝒞 3 w (s≤s z≤n)) (had-𝒞₂ w) ,
    R∈𝒞 3 w (s≤s z≤n) ,
    THT∉𝒞₃

  -- As a circuit: T ; H ; T has level 3, and its operator is not in C₃.
  -- (The circuit is written out in the proofs, and named, THT-circuit,
  -- only in the statement: comparing the name with the written-out
  -- circuit inside 𝒞 3 makes Agda compute both path-sums, so the proof
  -- crosses from one to the other by an equation of circuits, which
  -- compares the lists alone.)

  THT-circuit : K.Circuit n
  THT-circuit = K.R 3 w ∷ K.H w ∷ K.R 3 w ∷ []

  THT-level : K.level (K.R 3 w ∷ K.H w ∷ K.R 3 w ∷ []) ≡ 3
  THT-level = refl

  private
    -- The gates' operators, spelled as above.

    R3-gate : ⟪ K.⟦ K.R 3 w ∷ [] ⟧ ⟫ ≈ Rs (ρ false 3) w
    R3-gate = crk-gate (K.R 3 w)

    H-gate : ⟪ K.⟦ K.H w ∷ [] ⟧ ⟫ ≈ hadOp w
    H-gate = crk-gate (K.H w)

  THT-op : ⟪ K.⟦ K.R 3 w ∷ K.H w ∷ K.R 3 w ∷ [] ⟧ ⟫ ≈
           Rs (ρ false 3) w · hadOp w · Rs (ρ false 3) w
  THT-op =
    crk-∷ (K.R 3 w) (K.H w ∷ K.R 3 w ∷ [])
    ⟨≈⟩ ·-cong (crk-∷ (K.H w) (K.R 3 w ∷ []) ⟨≈⟩ ·-cong R3-gate H-gate)
               R3-gate

  -- The statement, through Not𝒞₃.

  THT-circuit-claim : Set
  THT-circuit-claim = Not𝒞₃ THT-circuit

  THT-circuit∉𝒞₃ : THT-circuit-claim
  THT-circuit∉𝒞₃ = by THT-circuit refl
    where
    by : (C : K.Circuit n) → C ≡ K.R 3 w ∷ K.H w ∷ K.R 3 w ∷ [] → Not𝒞₃ C
    by _ refl c =
      THT∉𝒞₃ (𝒞-resp 3 {⟪ K.⟦ K.R 3 w ∷ K.H w ∷ K.R 3 w ∷ [] ⟧ ⟫}
                        {Rs (ρ false 3) w · hadOp w · Rs (ρ false 3) w}
                        THT-op c)

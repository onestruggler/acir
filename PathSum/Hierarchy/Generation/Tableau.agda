------------------------------------------------------------------------
-- Presentations of groups
--
-- The tableau: how the gates of {H, S, CZ} conjugate Pauli data
--
-- Part of the generation of the n-qubit Clifford group (the plan is in
-- PathSum.Hierarchy.Generation.Scalar).  A Clifford operator is known
-- by what it does to the Paulis under conjugation; for the gates of
-- PathSum.Circuit that is an explicit, computable map act on the data
-- i^a X^x Z^z of PathSum.Hierarchy.Pauli, phases included:
--
--   H_w      swaps the bits at w, and multiplies by (-1)^(x_w z_w):
--            H X^x Z^z H = Z^x X^z there, and Z X = -X Z (actH);
--   S_w      adds x_w to z_w and to the phase: X ↦ Y = i X Z (actS);
--   CZ_(a,b) adds x_b to z_a and x_a to z_b, and multiplies by
--            (-1)^(x_a x_b) (actCZ; for a = b it is Z_a, which only
--            changes the sign).
--
-- For each gate g, g P(p) g† = P(act g p) on the operators of
-- PathSum.Hierarchy.Gates (gate-conj): for H by computing how it
-- intertwines every Pauli (PathSum.Hierarchy.Gates's had-intertwine),
-- for S and CZ from their diagonal phases, whose differences along
-- the Pauli's flip are a Pauli's phases (diag-conj-pauli; for S,
-- ¼[u] - ¼[u ⊕ x] = -¼[x] + ½[x ∧ u]).  The path-sum of the one-gate
-- circuit is that operator (PathSum.Hierarchy.Circuits's
-- clifford-gate), and the path-sum of a circuit is the product of its
-- gates' (clifford-∷, and clifford-++ here for any concatenation), so
-- a circuit acts by composing its gates' actions, first gate first:
-- the tableau semantics of circuits (actC, circuit-act):
--
--    ⟪ ⟦ C ⟧ ⟫ · P(p) · ⟪ ⟦ C ⟧ ⟫ † ≈ P(actC C p).
--
-- C†, the inverse circuit of PathSum.Adjoint, is the adjoint of C as
-- an operator (circuit-†, from PathSum.Adjoint.Conjugate).
--
-- For the synthesis, CNOT is the circuit cnotC c t = H_t CZ_(c,t) H_t,
-- whose action on the bits is CNOT's (cnot-xs-t, cnot-zs-c, ...:
-- X_c ↦ X_c X_t, Z_t ↦ Z_c Z_t), and a circuit that avoids a wire
-- keeps every Pauli's bits there (circuit-same) and leaves the Paulis
-- supported on that wire alone, phases included (circuit-fix).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.Generation.Tableau (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; _xor_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using
  (ℤ; 0ℤ; 1ℤ; -1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Properties using
  (+-identityʳ; *-distribˡ-+; +-assoc)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-self; same; same-true; same-intro)
open import PathSum.Adjoint.Conjugate M₀ using (circuit-adjoint)
open import PathSum.Compose.Matrix M₀ using (prop-2-7)
open import PathSum.Compose.Sum M₀ using (bool-iff)
open import PathSum.Cyclotomic M₀ using (Amp; _≐_)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Hierarchy.Generation.Symplectic M₀ public
open import PathSum.Hierarchy.Levels M₀ using (ρ; ρ-def; ½≡¼·2)
open import PathSum.Maslov.Arith M₀ using (½-xor)

-- The circuits, the gates and the lemmas about them that the modules
-- after this one use, re-exported from one application each (see
-- PathSum.Hierarchy.Generation.Scalar's imports).

open import PathSum.Hierarchy.Circuits M₀ public using
  (module Cl; module K; cliffordOp; clifford-gate; clifford-[];
   clifford-∷; clifford-𝒞₂; crkOp; crk-gate; crk-[]; crk-∷; crk-𝒞₂)
open import PathSum.Hierarchy.Gates M₀ public using
  (hadOp; had-unitary; had-intertwine; cnotOp; cnot-unitary; cnot-pauli;
   cnot-act; flip; flipᵀ; diagOp; czFn; wireFn; ΔFn; diag-conj-pauli;
   Rs; dot-≔)
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; ≡ᴺ-refl; ≡ᴺ-≡; ≡ᴺ-sym; ≡ᴺ-trans; ≡ᴺ-+; module ≡ᴺ-Reasoning)

import PathSum.Adjoint
import PathSum.Compose.Clifford M₀ as ClC

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

-- The inverse circuit (PathSum.Adjoint), at the precision of Cl.

module Adj = PathSum.Adjoint M

private
  variable
    n : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  -- Boolean identities, by cases.

  ∧-false : ∀ a → (a ∧ false) ≡ false
  ∧-false true  = refl
  ∧-false false = refl

  ∧-true : ∀ a → (a ∧ true) ≡ a
  ∧-true true  = refl
  ∧-true false = refl

  ∧-comm : ∀ a b → (a ∧ b) ≡ (b ∧ a)
  ∧-comm true  true  = refl
  ∧-comm true  false = refl
  ∧-comm false true  = refl
  ∧-comm false false = refl

  bits1 : ∀ a b d → (((a ∧ false) xor (b ∧ true)) xor d) ≡ (d xor b)
  bits1 true  true  true  = refl
  bits1 true  true  false = refl
  bits1 true  false true  = refl
  bits1 true  false false = refl
  bits1 false true  true  = refl
  bits1 false true  false = refl
  bits1 false false true  = refl
  bits1 false false false = refl

  bits2 : ∀ a b d → (((a ∧ true) xor (b ∧ false)) xor d) ≡ (d xor a)
  bits2 true  true  true  = refl
  bits2 true  true  false = refl
  bits2 true  false true  = refl
  bits2 true  false false = refl
  bits2 false true  true  = refl
  bits2 false true  false = refl
  bits2 false false true  = refl
  bits2 false false false = refl

  bits3 : ∀ a b d → (((a ∧ false) xor (b ∧ false)) xor d) ≡ d
  bits3 true  true  d = refl
  bits3 true  false d = refl
  bits3 false true  d = refl
  bits3 false false d = refl


------------------------------------------------------------------------
-- The action on Pauli data

-- c on the unit vector at i.

sc : Bool → Fin n → Assign n
sc c i j = c ∧ eᵛ i j

-- The Z bits CZ_(a,b) adds to a Pauli with the X bits x.

czZ : Fin n → Fin n → Assign n → Assign n
czZ a b x = sc (x b) a ⊕ᵛ sc (x a) b

actH : Fin n → PauliData n → PauliData n
actH w p = pd (ph p + (+ 2) * [ xs p w ∧ zs p w ]ᶻ)
              (xs p [ w ≔ zs p w ]) (zs p [ w ≔ xs p w ])

actS : Fin n → PauliData n → PauliData n
actS w p = pd (ph p + [ xs p w ]ᶻ) (xs p) (zs p [ w ≔ zs p w xor xs p w ])

actCZ : Fin n → Fin n → PauliData n → PauliData n
actCZ a b p = pd (ph p + (+ 2) * [ xs p a ∧ xs p b ]ᶻ) (xs p)
                 (czZ a b (xs p) ⊕ᵛ zs p)

act : Cl.Gate n → PauliData n → PauliData n
act (Cl.H w)    = actH w
act (Cl.S w)    = actS w
act (Cl.CZ a b) = actCZ a b

-- A circuit acts by its gates, first gate first.

actC : Cl.Circuit n → PauliData n → PauliData n
actC []      p = p
actC (g ∷ C) p = actC C (act g p)

actC-++ : (C D : Cl.Circuit n) (p : PauliData n) →
          actC (C ++ D) p ≡ actC D (actC C p)
actC-++ []      D p = refl
actC-++ (g ∷ C) D p = actC-++ C D (act g p)


------------------------------------------------------------------------
-- H

private
  -- Two comparisons agree when they agree pointwise.

  same-iff : (A B A′ B′ : Assign n) →
             (∀ j → A j ≡ B j → A′ j ≡ B′ j) →
             (∀ j → A′ j ≡ B′ j → A j ≡ B j) → same A B ≡ same A′ B′
  same-iff A B A′ B′ f g = bool-iff
    (λ h → same-intro A′ B′ (λ j → f j (same-true A B h j)))
    (λ h → same-intro A B (λ j → g j (same-true A′ B′ h j)))

  -- The parity, split at one wire.

  split-dot : (z y : Assign n) (w : Fin n) →
              dot z y ≡ (dot z (y [ w ≔ false ]) xor (z w ∧ y w))
  split-dot z y w = sym (xor-move (dot z y) (z w ∧ y w)
    (dot z (y [ w ≔ false ]))
    (sym (trans (dot-≔ z y w false)
                (cong (λ t → dot z y xor (z w ∧ t)) (xor-false (y w))))))

  -- Changing the left argument where the right one is 0.

  dot-≔ˡ : (z y : Assign n) (w : Fin n) (b : Bool) → y w ≡ false →
           dot (z [ w ≔ b ]) y ≡ dot z y
  dot-≔ˡ z y w b yw = trans (dot-comm (z [ w ≔ b ]) y)
    (trans (dot-≔ y z w b)
      (trans (cong (λ t → dot y z xor (t ∧ (z w xor b))) yw)
        (trans (xor-false (dot y z)) (dot-comm y z))))

  bits-H : ∀ D X Z V U →
           ((D xor (Z ∧ V)) xor ((V xor X) ∧ U)) ≡
           (((X ∧ Z) xor (D xor (X ∧ (U xor Z)))) xor (V ∧ (U xor Z)))
  bits-H true  true  true  true  true  = refl
  bits-H true  true  true  true  false = refl
  bits-H true  true  true  false true  = refl
  bits-H true  true  true  false false = refl
  bits-H true  true  false true  true  = refl
  bits-H true  true  false true  false = refl
  bits-H true  true  false false true  = refl
  bits-H true  true  false false false = refl
  bits-H true  false true  true  true  = refl
  bits-H true  false true  true  false = refl
  bits-H true  false true  false true  = refl
  bits-H true  false true  false false = refl
  bits-H true  false false true  true  = refl
  bits-H true  false false true  false = refl
  bits-H true  false false false true  = refl
  bits-H true  false false false false = refl
  bits-H false true  true  true  true  = refl
  bits-H false true  true  true  false = refl
  bits-H false true  true  false true  = refl
  bits-H false true  true  false false = refl
  bits-H false true  false true  true  = refl
  bits-H false true  false true  false = refl
  bits-H false true  false false true  = refl
  bits-H false true  false false false = refl
  bits-H false false true  true  true  = refl
  bits-H false false true  true  false = refl
  bits-H false false true  false true  = refl
  bits-H false false true  false false = refl
  bits-H false false false true  true  = refl
  bits-H false false false true  false = refl
  bits-H false false false false true  = refl
  bits-H false false false false false = refl

-- H P = P′ H for P′ the Pauli of actH: the guards agree (both say
-- v ⊕ x = u off w) and so do the phases.

had-conj : (w : Fin n) (p : PauliData n) →
           hadOp w · pauli p · hadOp w † ≈ pauli (actH w p)
had-conj {n} w p =
  intertwine⇒conj (hadOp w) (pauli p) (pauli q) (had-unitary w)
    (had-intertwine w p q G E)
  where
  q  = actH w p
  x  = xs p
  z  = zs p
  x′ = xs q

  G : ∀ v u → same ((v ⊕ᵛ x) [ w ≔ u w ]) u ≡
              same (v [ w ≔ (u ⊕ᵛ x′) w ]) (u ⊕ᵛ x′)
  G v u = same-iff ((v ⊕ᵛ x) [ w ≔ u w ]) u (v [ w ≔ (u ⊕ᵛ x′) w ])
                   (u ⊕ᵛ x′) (λ j → to j (j Fin.≟ w)) (λ j → from j (j Fin.≟ w))
    where
    to : ∀ j → Dec (j ≡ w) → ((v ⊕ᵛ x) [ w ≔ u w ]) j ≡ u j →
         (v [ w ≔ (u ⊕ᵛ x′) w ]) j ≡ (u ⊕ᵛ x′) j
    to j (yes refl) _ = ≔-here v w ((u ⊕ᵛ x′) w)
    to j (no j≢w)   h = trans (≔-there v ((u ⊕ᵛ x′) w) j≢w)
      (sym (trans (cong (u j xor_) (≔-there x (z w) j≢w))
                  (xor-move (v j) (x j) (u j)
                     (trans (sym (≔-there (v ⊕ᵛ x) (u w) j≢w)) h))))

    from : ∀ j → Dec (j ≡ w) → (v [ w ≔ (u ⊕ᵛ x′) w ]) j ≡ (u ⊕ᵛ x′) j →
           ((v ⊕ᵛ x) [ w ≔ u w ]) j ≡ u j
    from j (yes refl) _ = ≔-here (v ⊕ᵛ x) w (u w)
    from j (no j≢w)   h = trans (≔-there (v ⊕ᵛ x) (u w) j≢w)
      (xor-move (u j) (x j) (v j)
        (trans (cong (u j xor_) (sym (≔-there x (z w) j≢w)))
               (trans (sym h) (≔-there v ((u ⊕ᵛ x′) w) j≢w))))

  E : ∀ v u → same (v [ w ≔ (u ⊕ᵛ x′) w ]) (u ⊕ᵛ x′) ≡ true →
      φᴾ p v + ½ * [ (v ⊕ᵛ x) w ∧ u w ]ᶻ ≡ᴺ
      φᴾ q (u ⊕ᵛ x′) + ½ * [ v w ∧ (u ⊕ᵛ x′) w ]ᶻ
  E v u h = begin
    ¼ * ph p + ½ * [ dot z v ]ᶻ + ½ * [ (v w xor x w) ∧ u w ]ᶻ
      ≡⟨ cong (λ b → ¼ * ph p + ½ * [ b ]ᶻ + ½ * [ (v w xor x w) ∧ u w ]ᶻ)
              (split-dot z v w) ⟩
    ¼ * ph p + ½ * [ D xor (z w ∧ v w) ]ᶻ + ½ * [ (v w xor x w) ∧ u w ]ᶻ
      ≡⟨ +-assoc (¼ * ph p) (½ * [ D xor (z w ∧ v w) ]ᶻ)
                 (½ * [ (v w xor x w) ∧ u w ]ᶻ) ⟩
    ¼ * ph p + (½ * [ D xor (z w ∧ v w) ]ᶻ + ½ * [ (v w xor x w) ∧ u w ]ᶻ)
      ≡ᴺ⟨ ≡ᴺ-+ (≡ᴺ-refl {a = ¼ * ph p})
               (½-xor (D xor (z w ∧ v w)) ((v w xor x w) ∧ u w)) ⟩
    ¼ * ph p + ½ * [ (D xor (z w ∧ v w)) xor ((v w xor x w) ∧ u w) ]ᶻ
      ≡⟨ cong (λ b → ¼ * ph p + ½ * [ b ]ᶻ)
              (bits-H D (x w) (z w) (v w) (u w)) ⟩
    ¼ * ph p + ½ * [ (A xor B) xor C ]ᶻ
      ≡ᴺ⟨ ≡ᴺ-+ (≡ᴺ-refl {a = ¼ * ph p}) (≡ᴺ-sym (½-xor (A xor B) C)) ⟩
    ¼ * ph p + (½ * [ A xor B ]ᶻ + ½ * [ C ]ᶻ)
      ≡ᴺ⟨ ≡ᴺ-+ (≡ᴺ-refl {a = ¼ * ph p})
               (≡ᴺ-+ (≡ᴺ-sym (½-xor A B)) (≡ᴺ-refl {a = ½ * [ C ]ᶻ})) ⟩
    ¼ * ph p + ((½ * [ A ]ᶻ + ½ * [ B ]ᶻ) + ½ * [ C ]ᶻ)
      ≡⟨ regroup ⟩
    ¼ * (ph p + (+ 2) * [ A ]ᶻ) + ½ * [ B ]ᶻ + ½ * [ C ]ᶻ
      ≡⟨ cong₂ (λ s t → ¼ * (ph p + (+ 2) * [ A ]ᶻ) + ½ * [ s ]ᶻ +
                        ½ * [ v w ∧ t ]ᶻ)
               (sym dot-rhs) (sym yw) ⟩
    φᴾ q (u ⊕ᵛ x′) + ½ * [ v w ∧ (u ⊕ᵛ x′) w ]ᶻ ∎
    where
    open ≡ᴺ-Reasoning

    D = dot z (v [ w ≔ false ])
    A = x w ∧ z w
    B = D xor (x w ∧ (u w xor z w))
    C = v w ∧ (u w xor z w)
    y = u ⊕ᵛ x′

    pt : ∀ j → (v [ w ≔ y w ]) j ≡ y j
    pt = same-true (v [ w ≔ y w ]) y h

    yw : y w ≡ u w xor z w
    yw = cong (u w xor_) (≔-here x w (z w))

    agree-at : ∀ j → Dec (j ≡ w) → (y [ w ≔ false ]) j ≡ (v [ w ≔ false ]) j
    agree-at j (yes refl) = trans (≔-here y w false) (sym (≔-here v w false))
    agree-at j (no  j≢w)  = trans (≔-there y false j≢w)
                              (trans (sym (pt j))
                                (trans (≔-there v (y w) j≢w)
                                       (sym (≔-there v false j≢w))))

    agree : ∀ j → (y [ w ≔ false ]) j ≡ (v [ w ≔ false ]) j
    agree j = agree-at j (j Fin.≟ w)

    dot-rhs : dot (zs q) y ≡ B
    dot-rhs = trans (split-dot (zs q) y w)
      (cong₂ _xor_
        (trans (dot-≔ˡ z (y [ w ≔ false ]) w (x w) (≔-here y w false))
               (dot-cong {z = z} {z′ = z} (λ _ → refl) agree))
        (cong₂ _∧_ (≔-here z w (x w)) yw))

    quarter : ¼ * (ph p + (+ 2) * [ A ]ᶻ) ≡ ¼ * ph p + ½ * [ A ]ᶻ
    quarter = trans (*-distribˡ-+ ¼ (ph p) ((+ 2) * [ A ]ᶻ))
                    (cong (λ t → ¼ * ph p + t) (¼·2 [ A ]ᶻ))

    regroup : ¼ * ph p + ((½ * [ A ]ᶻ + ½ * [ B ]ᶻ) + ½ * [ C ]ᶻ) ≡
              ¼ * (ph p + (+ 2) * [ A ]ᶻ) + ½ * [ B ]ᶻ + ½ * [ C ]ᶻ
    regroup = trans
      (solve 4 (λ q h₁ h₂ h₃ → q :+ ((h₁ :+ h₂) :+ h₃) :=
                               (q :+ h₁) :+ h₂ :+ h₃)
               refl (¼ * ph p) (½ * [ A ]ᶻ) (½ * [ B ]ᶻ) (½ * [ C ]ᶻ))
      (cong (λ s → s + ½ * [ B ]ᶻ + ½ * [ C ]ᶻ) (sym quarter))


------------------------------------------------------------------------
-- S

-- Like CZ below, S is a diagonal whose phase differences along a
-- Pauli's flip are a Pauli's phases (PathSum.Hierarchy.Gates's
-- diag-conj-pauli): ¼[u ⊕ x] differs from ¼[u] by -¼[x] + ½[x ∧ u].
-- (Going through Rs-conj-1 and Rs-½ instead makes Agda compare two
-- spellings of the operator Rs ½ by unfolding its entries: minutes.)

private
  dot-sc : (z : Assign n) (c : Bool) (i : Fin n) → dot z (sc c i) ≡ (z i ∧ c)
  dot-sc z true  i = trans (dot-e z i) (sym (∧-true (z i)))
  dot-sc z false i = trans (dot-0ʳ z (sc false i) (λ _ → refl))
                           (sym (∧-false (z i)))

  dot-scˡ : (c : Bool) (i : Fin n) (u : Assign n) → dot (sc c i) u ≡ (c ∧ u i)
  dot-scˡ c i u = trans (dot-comm (sc c i) u)
                        (trans (dot-sc u c i) (∧-comm (u i) c))

  ∧-idem : ∀ a → (a ∧ a) ≡ a
  ∧-idem true  = refl
  ∧-idem false = refl

  -- ¼[u] - ¼[u ⊕ x] = -¼[x] + 2¼[x ∧ u], exactly.

  s-bits : ∀ u x → ¼ * [ u ]ᶻ - ¼ * [ u xor x ]ᶻ ≡
                   ¼ * (- [ x ]ᶻ) + (¼ * (+ 2)) * [ x ∧ u ]ᶻ
  s-bits false false = solve 1 (λ q → q :* con 0ℤ :- q :* con 0ℤ :=
                         q :* (:- con 0ℤ) :+ (q :* con (+ 2)) :* con 0ℤ) refl ¼
  s-bits true  false = solve 1 (λ q → q :* con 1ℤ :- q :* con 1ℤ :=
                         q :* (:- con 0ℤ) :+ (q :* con (+ 2)) :* con 0ℤ) refl ¼
  s-bits false true  = solve 1 (λ q → q :* con 0ℤ :- q :* con 1ℤ :=
                         q :* (:- con 1ℤ) :+ (q :* con (+ 2)) :* con 0ℤ) refl ¼
  s-bits true  true  = solve 1 (λ q → q :* con 1ℤ :- q :* con 0ℤ :=
                         q :* (:- con 1ℤ) :+ (q :* con (+ 2)) :* con 1ℤ) refl ¼

  s-phase : (w : Fin n) (p : PauliData n) (u : Assign n) →
            proj₁ (ΔFn (wireFn (ρ false 2) w) p) u ≡ᴺ
            ¼ * (- [ xs p w ]ᶻ) + ½ * [ dot (sc (xs p w) w) u ]ᶻ
  s-phase w p u = ≡ᴺ-≡
    (trans (cong (λ s → s * [ u w ]ᶻ - s * [ u w xor xs p w ]ᶻ) (ρ-def false 2))
      (trans (s-bits (u w) (xs p w))
        (cong₂ (λ h b → ¼ * (- [ xs p w ]ᶻ) + h * [ b ]ᶻ) (sym ½≡¼·2)
               (sym (dot-scˡ (xs p w) w u)))))

-- S leaves P alone when P does not flip its wire, and otherwise
-- multiplies it by i^(-1) Z: X ↦ Y.

S-conj : (w : Fin n) (p : PauliData n) →
         Rs (ρ false 2) w · pauli p · Rs (ρ false 2) w † ≈ pauli (actS w p)
S-conj w p =
  diag-conj-pauli (wireFn (ρ false 2) w) p (- [ xs p w ]ᶻ) (sc (xs p w) w)
                  (s-phase w p)
  ⟨≈⟩ pauli-≈ (pd (- [ xs p w ]ᶻ) 0ᵛ (sc (xs p w) w) ∙ᴾ p) (actS w p)
              ph-eq (λ _ → refl) (λ j → z-at j (j Fin.≟ w))
  where
  ph-eq : ¼ * (- [ xs p w ]ᶻ + ph p +
               (+ 2) * [ dot (sc (xs p w) w) (xs p) ]ᶻ) ≡ᴺ
          ¼ * (ph p + [ xs p w ]ᶻ)
  ph-eq = ≡ᴺ-≡ (cong (¼ *_)
    (trans (cong (λ b → - [ xs p w ]ᶻ + ph p + (+ 2) * [ b ]ᶻ)
                 (trans (dot-scˡ (xs p w) w (xs p)) (∧-idem (xs p w))))
           (solve 2 (λ t a → :- t :+ a :+ con (+ 2) :* t := a :+ t)
                  refl [ xs p w ]ᶻ (ph p))))

  z-at : ∀ j → Dec (j ≡ w) →
         (sc (xs p w) w ⊕ᵛ zs p) j ≡ (zs p [ w ≔ zs p w xor xs p w ]) j
  z-at j (yes refl) =
    trans (cong (λ e → (xs p w ∧ e) xor zs p w) (≔-here 0ᵛ w true))
      (trans (cong (_xor zs p w) (∧-true (xs p w)))
        (trans (xor-comm (xs p w) (zs p w))
               (sym (≔-here (zs p) w (zs p w xor xs p w)))))
  z-at j (no  j≢w)  =
    trans (cong (λ e → (xs p w ∧ e) xor zs p j) (≔-there 0ᵛ true j≢w))
      (trans (cong (_xor zs p j) (∧-false (xs p w)))
             (sym (≔-there (zs p) (zs p w xor xs p w) j≢w)))


------------------------------------------------------------------------
-- CZ

private
  cz-bits : ∀ ua ub xa xb →
            ((ua ∧ ub) xor ((ua xor xa) ∧ (ub xor xb))) ≡
            ((xa ∧ xb) xor ((xb ∧ ua) xor (xa ∧ ub)))
  cz-bits true  true  true  true  = refl
  cz-bits true  true  true  false = refl
  cz-bits true  true  false true  = refl
  cz-bits true  true  false false = refl
  cz-bits true  false true  true  = refl
  cz-bits true  false true  false = refl
  cz-bits true  false false true  = refl
  cz-bits true  false false false = refl
  cz-bits false true  true  true  = refl
  cz-bits false true  true  false = refl
  cz-bits false true  false true  = refl
  cz-bits false true  false false = refl
  cz-bits false false true  true  = refl
  cz-bits false false true  false = refl
  cz-bits false false false true  = refl
  cz-bits false false false false = refl

  -- The phase differences of CZ along P's flip are those of a Pauli.

  cz-phase : (a b : Fin n) (p : PauliData n) (u : Assign n) →
             ½ * [ u a ∧ u b ]ᶻ - ½ * [ (u ⊕ᵛ xs p) a ∧ (u ⊕ᵛ xs p) b ]ᶻ ≡ᴺ
             ¼ * ((+ 2) * [ xs p a ∧ xs p b ]ᶻ) +
             ½ * [ dot (czZ a b (xs p)) u ]ᶻ
  cz-phase a b p u = begin
    ½ * [ A ]ᶻ - ½ * [ B ]ᶻ
      ≡ᴺ⟨ ≡ᴺ-+ (≡ᴺ-refl {a = ½ * [ A ]ᶻ}) (neg-½ B) ⟩
    ½ * [ A ]ᶻ + ½ * [ B ]ᶻ
      ≡ᴺ⟨ ½-xor A B ⟩
    ½ * [ A xor B ]ᶻ
      ≡⟨ cong (λ c → ½ * [ c ]ᶻ) (cz-bits (u a) (u b) (xs p a) (xs p b)) ⟩
    ½ * [ (xs p a ∧ xs p b) xor C ]ᶻ
      ≡ᴺ⟨ ≡ᴺ-sym (½-xor (xs p a ∧ xs p b) C) ⟩
    ½ * [ xs p a ∧ xs p b ]ᶻ + ½ * [ C ]ᶻ
      ≡⟨ cong₂ _+_ (sym (¼·2 [ xs p a ∧ xs p b ]ᶻ))
           (cong (λ c → ½ * [ c ]ᶻ)
             (sym (trans (dot-⊕ˡ (sc (xs p b) a) (sc (xs p a) b) u)
                         (cong₂ _xor_ (dot-scˡ (xs p b) a u)
                                      (dot-scˡ (xs p a) b u))))) ⟩
    ¼ * ((+ 2) * [ xs p a ∧ xs p b ]ᶻ) +
    ½ * [ dot (czZ a b (xs p)) u ]ᶻ ∎
    where
    open ≡ᴺ-Reasoning
    A = u a ∧ u b
    B = (u a xor xs p a) ∧ (u b xor xs p b)
    C = (xs p b ∧ u a) xor (xs p a ∧ u b)

cz-conj : (a b : Fin n) (p : PauliData n) →
          diagOp (czFn a b) · pauli p · diagOp (czFn a b) † ≈
          pauli (actCZ a b p)
cz-conj a b p =
  diag-conj-pauli (czFn a b) p ((+ 2) * [ xs p a ∧ xs p b ]ᶻ)
                  (czZ a b (xs p)) (cz-phase a b p)
  ⟨≈⟩ pauli-≈ (pd ((+ 2) * [ xs p a ∧ xs p b ]ᶻ) 0ᵛ (czZ a b (xs p)) ∙ᴾ p)
              (actCZ a b p) ph-eq (λ _ → refl) (λ _ → refl)
  where
  dot-zero : dot (czZ a b (xs p)) (xs p) ≡ false
  dot-zero =
    trans (dot-⊕ˡ (sc (xs p b) a) (sc (xs p a) b) (xs p))
      (trans (cong₂ _xor_ (dot-scˡ (xs p b) a (xs p))
                          (dot-scˡ (xs p a) b (xs p)))
        (trans (cong ((xs p b ∧ xs p a) xor_) (∧-comm (xs p a) (xs p b)))
               (xor-self (xs p b ∧ xs p a))))

  ph-eq : ¼ * ((+ 2) * [ xs p a ∧ xs p b ]ᶻ + ph p +
               (+ 2) * [ dot (czZ a b (xs p)) (xs p) ]ᶻ) ≡ᴺ
          ¼ * (ph p + (+ 2) * [ xs p a ∧ xs p b ]ᶻ)
  ph-eq = ≡ᴺ-≡ (cong (¼ *_)
    (trans (cong (λ d → (+ 2) * [ xs p a ∧ xs p b ]ᶻ + ph p + (+ 2) * [ d ]ᶻ)
                 dot-zero)
           (solve 2 (λ A a → A :+ a :+ con (+ 2) :* con 0ℤ := a :+ A)
                  refl ((+ 2) * [ xs p a ∧ xs p b ]ᶻ) (ph p))))


------------------------------------------------------------------------
-- Gates and circuits

-- Each gate conjugates P(p) to P(act g p).

gate-conj : (g : Cl.Gate n) (p : PauliData n) →
            cliffordOp g · pauli p · cliffordOp g † ≈ pauli (act g p)
gate-conj (Cl.H w)    p = had-conj w p
gate-conj (Cl.S w)    p = S-conj w p
gate-conj (Cl.CZ a b) p = cz-conj a b p

-- So does the path-sum of the one-gate circuit.

gate-act : (g : Cl.Gate n) (p : PauliData n) →
           ⟪ Cl.⟦ g ∷ [] ⟧ ⟫ · pauli p · ⟪ Cl.⟦ g ∷ [] ⟧ ⟫ † ≈ pauli (act g p)
gate-act g p = conj-cong (clifford-gate g) (pauli p) ⟨≈⟩ gate-conj g p

private
  conj-I : (P : Op n) → I · P · I † ≈ P
  conj-I P = ·-congʳ (I · P) †-I ⟨≈⟩ ·-identityʳ (I · P) ⟨≈⟩ ·-identityˡ P

-- The tableau semantics of a circuit.

circuit-act : (C : Cl.Circuit n) (p : PauliData n) →
              ⟪ Cl.⟦ C ⟧ ⟫ · pauli p · ⟪ Cl.⟦ C ⟧ ⟫ † ≈ pauli (actC C p)
circuit-act []      p = conj-cong clifford-[] (pauli p) ⟨≈⟩ conj-I (pauli p)
circuit-act (g ∷ C) p =
  conj-cong (clifford-∷ g C) (pauli p)
  ⟨≈⟩ conj-· ⟪ Cl.⟦ C ⟧ ⟫ ⟪ Cl.⟦ g ∷ [] ⟧ ⟫ (pauli p)
  ⟨≈⟩ conj-congᴾ ⟪ Cl.⟦ C ⟧ ⟫ (gate-act g p)
  ⟨≈⟩ circuit-act C (act g p)

-- The path-sum of C followed by D is the product (definition 2.9 and
-- proposition 2.7).

clifford-++ : (C D : Cl.Circuit n) →
              ⟪ Cl.⟦ C ++ D ⟧ ⟫ ≈ ⟪ Cl.⟦ D ⟧ ⟫ · ⟪ Cl.⟦ C ⟧ ⟫
clifford-++ C D = ≈-by ⟪ Cl.⟦ C ++ D ⟧ ⟫ (⟪ Cl.⟦ D ⟧ ⟫ · ⟪ Cl.⟦ C ⟧ ⟫)
  (trans (ClC.norm-++ C D) (ℕ.+-comm (Cl.norm C) (Cl.norm D)))
  (λ x z → ClC.amp-⟦++⟧ C D x z ∙ prop-2-7 Cl.⟦ D ⟧ Cl.⟦ C ⟧ x z)

-- Every circuit is unitary, and its inverse circuit is its adjoint.

circuit-unitary : (C : Cl.Circuit n) → Unitary ⟪ Cl.⟦ C ⟧ ⟫
circuit-unitary C = 𝒞-unitary 1 {⟪ Cl.⟦ C ⟧ ⟫} (clifford-𝒞₂ C)

-- PathSum.Hierarchy.Circuits's clifford-𝒞₂ and clifford-[], restated
-- with this development's operators.

circuit-𝒞₂ : (C : Cl.Circuit n) → 𝒞 2 ⟪ Cl.⟦ C ⟧ ⟫
circuit-𝒞₂ C = clifford-𝒞₂ C

circuit-[] : ⟪ Cl.⟦_⟧ {n} [] ⟫ ≈ I
circuit-[] = clifford-[]

level-𝒞₂ : (C : K.Circuit n) → K.level C ≤ 2 → 𝒞 2 ⟪ K.⟦ C ⟧ ⟫
level-𝒞₂ C = crk-𝒞₂ C

circuit-† : (C : Cl.Circuit n) → ⟪ Cl.⟦ C Adj.† ⟧ ⟫ ≈ ⟪ Cl.⟦ C ⟧ ⟫ †
circuit-† C = ≈-by ⟪ Cl.⟦ C Adj.† ⟧ ⟫ (⟪ Cl.⟦ C ⟧ ⟫ †) (Adj.norm-† C)
  (λ x z → circuit-adjoint C x z)

-- Conjugating by U, then by a circuit.

after : (C : Cl.Circuit n) (U : Op n) (s r : PauliData n) →
        U · pauli s · U † ≈ pauli r →
        (⟪ Cl.⟦ C ⟧ ⟫ · U) · pauli s · (⟪ Cl.⟦ C ⟧ ⟫ · U) † ≈ pauli (actC C r)
after C U s r h =
  conj-· ⟪ Cl.⟦ C ⟧ ⟫ U (pauli s)
  ⟨≈⟩ conj-congᴾ ⟪ Cl.⟦ C ⟧ ⟫ h
  ⟨≈⟩ circuit-act C r


------------------------------------------------------------------------
-- The bits

xs-H-at : (w : Fin n) (r : PauliData n) → xs (actH w r) w ≡ zs r w
xs-H-at w r = ≔-here (xs r) w (zs r w)

zs-H-at : (w : Fin n) (r : PauliData n) → zs (actH w r) w ≡ xs r w
zs-H-at w r = ≔-here (zs r) w (xs r w)

xs-H-off : (w : Fin n) (r : PauliData n) {i : Fin n} → i ≢ w →
           xs (actH w r) i ≡ xs r i
xs-H-off w r i≢w = ≔-there (xs r) (zs r w) i≢w

zs-H-off : (w : Fin n) (r : PauliData n) {i : Fin n} → i ≢ w →
           zs (actH w r) i ≡ zs r i
zs-H-off w r i≢w = ≔-there (zs r) (xs r w) i≢w

zs-S-at : (w : Fin n) (r : PauliData n) → zs (actS w r) w ≡ zs r w xor xs r w
zs-S-at w r = ≔-here (zs r) w (zs r w xor xs r w)

zs-S-off : (w : Fin n) (r : PauliData n) {i : Fin n} → i ≢ w →
           zs (actS w r) i ≡ zs r i
zs-S-off w r i≢w = ≔-there (zs r) (zs r w xor xs r w) i≢w

zs-CZ-off : (a b : Fin n) (r : PauliData n) {i : Fin n} → i ≢ a → i ≢ b →
            zs (actCZ a b r) i ≡ zs r i
zs-CZ-off a b r {i} i≢a i≢b =
  trans (cong₂ (λ e₁ e₂ → ((xs r b ∧ e₁) xor (xs r a ∧ e₂)) xor zs r i)
               (≔-there 0ᵛ true i≢a) (≔-there 0ᵛ true i≢b))
        (bits3 (xs r b) (xs r a) (zs r i))

-- CNOT, as H_t CZ_(c,t) H_t: X_c ↦ X_c X_t and Z_t ↦ Z_c Z_t on the bits.

cnotC : Fin n → Fin n → Cl.Circuit n
cnotC c t = Cl.H t ∷ Cl.CZ c t ∷ Cl.H t ∷ []

module _ {n : ℕ} {c t : Fin n} (c≢t : c ≢ t) (r : PauliData n) where

  private
    t≢c : t ≢ c
    t≢c e = c≢t (sym e)

    r₁ = actH t r
    r₂ = actCZ c t r₁

  cnot-xs-t : xs (actC (cnotC c t) r) t ≡ xs r t xor xs r c
  cnot-xs-t = trans (≔-here (xs r₂) t (zs r₂ t))
    (trans (cong₂ (λ e₁ e₂ → ((xs r₁ t ∧ e₁) xor (xs r₁ c ∧ e₂)) xor zs r₁ t)
                  (≔-there 0ᵛ true t≢c) (≔-here 0ᵛ t true))
      (trans (cong₂ (λ a d → ((xs r₁ t ∧ false) xor (a ∧ true)) xor d)
                    (≔-there (xs r) (zs r t) c≢t) (≔-here (zs r) t (xs r t)))
             (bits1 (xs r₁ t) (xs r c) (xs r t))))

  cnot-xs-off : {j : Fin n} → j ≢ t → xs (actC (cnotC c t) r) j ≡ xs r j
  cnot-xs-off j≢t = trans (≔-there (xs r₂) (zs r₂ t) j≢t)
                          (≔-there (xs r) (zs r t) j≢t)

  cnot-zs-t : zs (actC (cnotC c t) r) t ≡ zs r t
  cnot-zs-t = trans (≔-here (zs r₂) t (xs r₂ t)) (≔-here (xs r) t (zs r t))

  cnot-zs-c : zs (actC (cnotC c t) r) c ≡ zs r c xor zs r t
  cnot-zs-c = trans (≔-there (zs r₂) (xs r₂ t) c≢t)
    (trans (cong₂ (λ e₁ e₂ → ((xs r₁ t ∧ e₁) xor (xs r₁ c ∧ e₂)) xor zs r₁ c)
                  (≔-here 0ᵛ c true) (≔-there 0ᵛ true c≢t))
      (trans (cong₂ (λ a d → ((a ∧ true) xor (xs r₁ c ∧ false)) xor d)
                    (≔-here (xs r) t (zs r t)) (≔-there (zs r) (xs r t) c≢t))
             (bits2 (zs r t) (xs r₁ c) (zs r c))))

  private
    zs-off-at : (j : Fin n) → j ≢ c → Dec (j ≡ t) →
                zs (actC (cnotC c t) r) j ≡ zs r j
    zs-off-at j j≢c (yes refl) = cnot-zs-t
    zs-off-at j j≢c (no  j≢t)  = trans (≔-there (zs r₂) (xs r₂ t) j≢t)
      (trans (cong₂ (λ e₁ e₂ → ((xs r₁ t ∧ e₁) xor (xs r₁ c ∧ e₂)) xor zs r₁ j)
                    (≔-there 0ᵛ true j≢c) (≔-there 0ᵛ true j≢t))
        (trans (bits3 (xs r₁ t) (xs r₁ c) (zs r₁ j))
               (≔-there (zs r) (xs r t) j≢t)))

  cnot-zs-off : {j : Fin n} → j ≢ c → zs (actC (cnotC c t) r) j ≡ zs r j
  cnot-zs-off {j} j≢c = zs-off-at j j≢c (j Fin.≟ t)


------------------------------------------------------------------------
-- Circuits that avoid a wire

AvoidsG : Fin n → Cl.Gate n → Set
AvoidsG i (Cl.H w)    = i ≢ w
AvoidsG i (Cl.S w)    = i ≢ w
AvoidsG i (Cl.CZ a b) = (i ≢ a) × (i ≢ b)

Avoids : Fin n → Cl.Circuit n → Set
Avoids i = All (AvoidsG i)

avoids-++ : {i : Fin n} (C D : Cl.Circuit n) → Avoids i C → Avoids i D →
            Avoids i (C ++ D)
avoids-++ []      D []       d = d
avoids-++ (g ∷ C) D (a ∷ as) d = a ∷ avoids-++ C D as d

avoids-cnot : {i c t : Fin n} → i ≢ c → i ≢ t → Avoids i (cnotC c t)
avoids-cnot i≢c i≢t = i≢t ∷ (i≢c , i≢t) ∷ i≢t ∷ []

-- The bits at an avoided wire are kept.

gate-same : (g : Cl.Gate n) {i : Fin n} → AvoidsG i g → (r : PauliData n) →
            Same-at i r (act g r)
gate-same (Cl.H w)    i≢w         r = sym (xs-H-off w r i≢w) ,
                                      sym (zs-H-off w r i≢w)
gate-same (Cl.S w)    i≢w         r = refl , sym (zs-S-off w r i≢w)
gate-same (Cl.CZ a b) (i≢a , i≢b) r = refl , sym (zs-CZ-off a b r i≢a i≢b)

circuit-same : (C : Cl.Circuit n) {i : Fin n} → Avoids i C →
               (r : PauliData n) → Same-at i r (actC C r)
circuit-same []      []       r = refl , refl
circuit-same (g ∷ C) (a ∷ as) r =
  trans (proj₁ (gate-same g a r)) (proj₁ (circuit-same C as (act g r))) ,
  trans (proj₂ (gate-same g a r)) (proj₂ (circuit-same C as (act g r)))

-- A Pauli supported on the avoided wire is left alone.

Supp : Fin n → PauliData n → Set
Supp i r = ∀ k → k ≢ i → Zero-at k r

supp-X : (i : Fin n) → Supp i (X^ i)
supp-X i k k≢i = ≔-there 0ᵛ true k≢i , refl

supp-Z : (i : Fin n) → Supp i (Z^ i)
supp-Z i k k≢i = refl , ≔-there 0ᵛ true k≢i

gate-fix : (g : Cl.Gate n) {i : Fin n} → AvoidsG i g → (r : PauliData n) →
           Supp i r → act g r ≈ᴾ r
gate-fix (Cl.H w) i≢w r s = ≈ᴾ-intro
  (≡ᴺ-≡ (cong (¼ *_) (trans (cong (λ b → ph r + (+ 2) * [ b ∧ zs r w ]ᶻ) xw)
                            (+-identityʳ (ph r)))))
  (λ k → trans (cong (λ b → (xs r [ w ≔ b ]) k) (trans zw (sym xw)))
               (≔-self (xs r) w k))
  (λ k → trans (cong (λ b → (zs r [ w ≔ b ]) k) (trans xw (sym zw)))
               (≔-self (zs r) w k))
  where
  xw = proj₁ (s w (λ e → i≢w (sym e)))
  zw = proj₂ (s w (λ e → i≢w (sym e)))
gate-fix (Cl.S w) i≢w r s = ≈ᴾ-intro
  (≡ᴺ-≡ (cong (¼ *_) (trans (cong (λ b → ph r + [ b ]ᶻ) xw)
                            (+-identityʳ (ph r)))))
  (λ _ → refl)
  (λ k → trans (cong (λ b → (zs r [ w ≔ b ]) k)
                     (trans (cong (zs r w xor_) xw) (xor-false (zs r w))))
               (≔-self (zs r) w k))
  where
  xw = proj₁ (s w (λ e → i≢w (sym e)))
gate-fix (Cl.CZ a b) (i≢a , i≢b) r s = ≈ᴾ-intro
  (≡ᴺ-≡ (cong (¼ *_) (trans (cong (λ c → ph r + (+ 2) * [ c ∧ xs r b ]ᶻ) xa)
                            (+-identityʳ (ph r)))))
  (λ _ → refl)
  (λ k → cong₂ (λ u v → ((u ∧ eᵛ a k) xor (v ∧ eᵛ b k)) xor zs r k) xb xa)
  where
  xa = proj₁ (s a (λ e → i≢a (sym e)))
  xb = proj₁ (s b (λ e → i≢b (sym e)))

circuit-fix : (C : Cl.Circuit n) {i : Fin n} → Avoids i C →
              (r : PauliData n) → Supp i r → actC C r ≈ᴾ r
circuit-fix []      []       r s = ≈ᴾ-refl
circuit-fix (g ∷ C) {i} (a ∷ as) r s =
  ≈ᴾ-trans (circuit-fix C as (act g r) s′) e
  where
  e = gate-fix g a r s
  s′ : Supp i (act g r)
  s′ k k≢i = trans (xs≈ e k) (proj₁ (s k k≢i)) ,
             trans (zs≈ e k) (proj₂ (s k k≢i))

-- So a circuit avoiding wire i keeps what U does to a Pauli on wire i.

fixes-after : (C : Cl.Circuit n) {i : Fin n} → Avoids i C → (U : Op n)
              (r : PauliData n) → Supp i r → U · pauli r · U † ≈ pauli r →
              (⟪ Cl.⟦ C ⟧ ⟫ · U) · pauli r · (⟪ Cl.⟦ C ⟧ ⟫ · U) † ≈ pauli r
fixes-after C a U r s h = after C U r r h ⟨≈⟩ ≈ᴾ⇒≈ (circuit-fix C a r s)

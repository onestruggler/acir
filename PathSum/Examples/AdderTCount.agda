------------------------------------------------------------------------
-- Presentations of groups
--
-- Example B.2: the Reed-Muller adder uses fewer T gates than two
-- Toffoli gates
--
-- Appendix B.2 of Amy's QPL 2018 paper gives a Clifford+T circuit for
-- the one-bit full adder
--
--    |x1x2x3x4⟩ ↦ |x1 (x1 ⊕ x2) (x1 ⊕ x2 ⊕ x3)
--                  (x1x2 ⊕ x1x3 ⊕ x2x3 ⊕ x4)⟩
--
-- "obtained by using the Reed-Muller decoding method of [4] to reduce
-- the number of T gates from the standard implementation using two
-- Toffoli gates".  PathSum.Examples.Adder reads that circuit off the
-- figure (AdderC, over {H, CNOT, S, T}) and proves that it implements
-- the specification (AdderC-spec).  This module makes the comparison
-- the sentence makes, counting T and T† gates in the circuits
-- themselves (PathSum.Toffoli.Netlist's tcount: the gates R 3 and
-- R† 3).
--
-- * The standard implementation, StdAdder: a Toffoli gate onto x4
--   controlled by x1 and x2, CNOT x1 → x2, a Toffoli gate onto x4
--   controlled by (the new) x2 and x3, CNOT x2 → x3; each Toffoli gate
--   is PathSum.Toffoli's seven-T circuit.  It implements the same
--   specification (StdAdder-spec): the four gates compute the
--   composite of their Boolean functions (PathSum.Classical's
--   ⟦++⟧-computes, PathSum.Toffoli.tof-computes, ⟦CNOT⟧-computes),
--   which is the specification's function at each of the 16 inputs
--   (checked by computation, adder-function).
--
-- * T counts (adder-tcounts): 7 for the paper's circuit, 14 = 2 · 7
--   for the standard one, so the Reed-Muller circuit uses half as many
--   (fewer-T).  It also uses half as many Hadamard gates, so half as
--   many path variables (adder-hadamards: 2 against 4).
--
-- That 7 is optimal, or that no other circuit does better, is not
-- claimed; the paper does not claim it either.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.AdderTCount where

open import Data.Bool.Base using (Bool; _xor_; _∧_)
open import Data.Bool.Properties using () renaming (_≟_ to _≟ᵇ_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (all?)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Nat.Base using (ℕ; _<_; _*_; s≤s; z≤n)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (toWitness)

open import PathSum.Assign using (_[_≔_]; ≔-cong)
open import PathSum.Base using (PathSum; out)
open import PathSum.Denotation 0 using (Assign; _≋_)
open import PathSum.Examples.Adder using (AdderC; Adderˢ; AdderC-spec)
open import PathSum.Examples.Base using (module CRK; Implements)
open import PathSum.Polynomial using (eval)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Decidable using (all-assignments?)
open import PathSum.Polynomial.Properties using (eval-cong)
open import PathSum.Toffoli.Netlist 0 using (tcount)

import PathSum.Classical
import PathSum.CRK.Path
import PathSum.Toffoli

private
  module CL = PathSum.Classical 0
  module CP = PathSum.CRK.Path 0
  module TF = PathSum.Toffoli 0

  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Implementing a specification, for any circuit

-- A circuit and a path-sum computing the same Boolean function are
-- equivalent (PathSum.Classical.computes-≋), stated as
-- PathSum.Examples.Base's Implements.

implements-computes : (C : CRK.Circuit n) (ζ : PathSum n k m)
                      {F : Assign n → Assign n} →
                      CP.⟦ C ⟧ CL.computes F → ζ CL.computes F →
                      Implements C ζ
implements-computes C ζ cC cζ = CL.computes-≋ CP.⟦ C ⟧ ζ cC cζ


------------------------------------------------------------------------
-- The standard implementation

a b c d : Fin 4
a = zero
b = suc zero
c = suc (suc zero)
d = suc (suc (suc zero))

-- Toffoli onto x4 by x1 and x2; x1 → x2; Toffoli onto x4 by x2 and x3;
-- x2 → x3.

Tof₁ CNOT₁ Tof₂ CNOT₂ : CP.Circuit 4
Tof₁  = TF.tof a b d (λ ()) (λ ()) (λ ())
CNOT₁ = CP.CNOT a b (λ ()) ∷ []
Tof₂  = TF.tof b c d (λ ()) (λ ()) (λ ())
CNOT₂ = CP.CNOT b c (λ ()) ∷ []

StdAdder : CP.Circuit 4
StdAdder = Tof₁ ++ (CNOT₁ ++ (Tof₂ ++ CNOT₂))

-- Its Boolean function, gate by gate.

private
  cnotᶠ : Fin 4 → Fin 4 → Assign 4 → Assign 4
  cnotᶠ s t x = x [ t ≔ x t xor x s ]

stdᶠ : Assign 4 → Assign 4
stdᶠ x = cnotᶠ b c (TF.toffoli b c d (cnotᶠ a b (TF.toffoli a b d x)))

std-computes₀ : CP.⟦ StdAdder ⟧ CL.computes stdᶠ
std-computes₀ =
  CL.⟦++⟧-computes Tof₁ (CNOT₁ ++ (Tof₂ ++ CNOT₂))
    (TF.tof-computes a b d (λ ()) (λ ()) (λ ()))
    (CL.⟦++⟧-computes CNOT₁ (Tof₂ ++ CNOT₂)
      (CL.⟦CNOT⟧-computes a b (λ ()))
      (CL.⟦++⟧-computes Tof₂ CNOT₂
        (TF.tof-computes b c d (λ ()) (λ ()) (λ ()))
        (CL.⟦CNOT⟧-computes b c (λ ()))))


------------------------------------------------------------------------
-- It is the specification's function

-- Both functions read their input through its values.

private
  upd-≗ : (t : Fin 4) {x x′ : Assign 4} {v v′ : Bool} →
          (∀ i → x i ≡ x′ i) → v ≡ v′ →
          ∀ i → (x [ t ≔ v ]) i ≡ (x′ [ t ≔ v′ ]) i
  upd-≗ t {v = v} x≗ refl = ≔-cong t v x≗

  toffoli-≗ : (s₁ s₂ t : Fin 4) {x x′ : Assign 4} → (∀ i → x i ≡ x′ i) →
              ∀ i → TF.toffoli s₁ s₂ t x i ≡ TF.toffoli s₁ s₂ t x′ i
  toffoli-≗ s₁ s₂ t x≗ =
    upd-≗ t x≗ (cong₂ _xor_ (x≗ t) (cong₂ _∧_ (x≗ s₁) (x≗ s₂)))

  cnot-≗ : (s t : Fin 4) {x x′ : Assign 4} → (∀ i → x i ≡ x′ i) →
           ∀ i → cnotᶠ s t x i ≡ cnotᶠ s t x′ i
  cnot-≗ s t x≗ = upd-≗ t x≗ (cong₂ _xor_ (x≗ t) (x≗ s))

  std-≗ : {x x′ : Assign 4} → (∀ i → x i ≡ x′ i) →
          ∀ i → stdᶠ x i ≡ stdᶠ x′ i
  std-≗ x≗ = cnot-≗ b c (toffoli-≗ b c d (cnot-≗ a b (toffoli-≗ a b d x≗)))

  spec-≗ : {x x′ : Assign 4} → (∀ i → x i ≡ x′ i) →
           ∀ w → CL.fun (out Adderˢ) x w ≡ CL.fun (out Adderˢ) x′ w
  spec-≗ {x} {x′} x≗ w =
    cong odd (eval-cong (out Adderˢ w) {x} {x′} {CL.none} {CL.none}
                        x≗ (λ ()))

  Agrees : Assign 4 → Set
  Agrees x = ∀ w → stdᶠ x w ≡ CL.fun (out Adderˢ) x w

  agrees-resp : {x x′ : Assign 4} → (∀ i → x i ≡ x′ i) →
                Agrees x → Agrees x′
  agrees-resp x≗ h w = trans (sym (std-≗ x≗ w)) (trans (h w) (spec-≗ x≗ w))

-- At each of the 16 inputs, by computation.

adder-function : ∀ (x : Assign 4) w → stdᶠ x w ≡ CL.fun (out Adderˢ) x w
adder-function = toWitness
  {a? = all-assignments? agrees-resp
          (λ x → all? (λ w → stdᶠ x w ≟ᵇ CL.fun (out Adderˢ) x w))} tt

-- Hence the standard circuit implements the specification too.

StdAdder-spec : Implements StdAdder Adderˢ
StdAdder-spec = implements-computes StdAdder Adderˢ
  (CL.computes-≗ CP.⟦ StdAdder ⟧ adder-function std-computes₀)
  (CL.classical-computes (out Adderˢ))


------------------------------------------------------------------------
-- Counting T gates

-- The paper's circuit has 7 T and T† gates; two Toffoli gates have 14.

adder-tcounts : tcount AdderC ≡ 7 × tcount StdAdder ≡ 2 * 7
adder-tcounts = refl , refl

fewer-T : tcount AdderC < tcount StdAdder
fewer-T = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))

-- Half as many Hadamard gates, so half as many path variables.

adder-hadamards : CRK.norm AdderC ≡ 2 × CRK.norm StdAdder ≡ 4
adder-hadamards = refl , refl

-- Both circuits implement the full adder, the paper's with half the
-- T gates.

reed-muller-adder :
  Implements AdderC Adderˢ × Implements StdAdder Adderˢ ×
  tcount AdderC < tcount StdAdder
reed-muller-adder = AdderC-spec , StdAdder-spec , fewer-T

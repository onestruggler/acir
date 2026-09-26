------------------------------------------------------------------------
-- Presentations of groups
--
-- The hidden shift algorithm with a symbolic shift, figure 3(b)
-- (Amy, QPL 2018, section 5.2)
--
-- In the second version of the paper's benchmark "the shift is
-- supplied symbolically via a quantum register", and the circuit is
-- verified against |0⟩|s⟩ ↦ |s⟩|s⟩.  Here the data register holds
-- n = 2m qubits and the shift register n more, the data first; the
-- circuit (SSᶜ) is figure 3(a) on the data register with each X^s
-- replaced by n CNOTs, from the i-th qubit of the shift register to
-- the i-th data qubit (cnots):
--
--    H^{⊗n};  CX;  O_f;  CX;  H^{⊗n};  O_f̃;  H^{⊗n}.
--
-- The shift register only ever controls, so the circuit acts on each
-- slice of a column with the shift register fixed at v separately
-- (Slices): the layers on the data register act on the slice as they
-- act on n qubits (PathSum.HiddenShift.Gates's applyᴬ-upper), and the
-- CNOTs shift the slice by v (applyᴬ-cnots), with no normalisation,
-- unlike X^s.  So on the slice at v the circuit is the composite
-- HS g v of PathSum.HiddenShift, for the shift v the register holds
-- (Sim-slice), and at every input
--
--    amp (|x⟩|t⟩ → |u⟩|v⟩) = [t = v] · amp_{HS g v}(|x⟩ → |u⟩)
--
-- (symbolic-shift): the circuit is Σ_t HS(g, t) ⊗ |t⟩⟨t|.  With
-- x = 0 this is the paper's specification, for every s at once:
-- |0⟩|s⟩ reaches |s⟩|s⟩ with normalised amplitude 1 and nothing else
-- (symbolic-shift-0).  As an equivalence of path-sums with the data
-- register prepared in |0⟩ (PathSum.Ancilla.Register), the circuit is
-- the specification |x_d, x_s⟩ ↦ |x_s, x_s⟩ (specSᴾ), with the shift
-- as input variables (symbolic-shift-≋, symbolic-shift-set0).  The
-- circuit has 3n Hadamards, as in table 2 (norm-SSᶜ).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Symbolic (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using (∧-assoc; ∧-identityʳ; ∧-zeroʳ)
open import Data.Fin.Base using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (ℤ; 0ℤ; _*_)
open import Data.Integer.Properties using (*-zeroˡ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.AmpLinear M₀ using (·ᴬ-linear; scale-exp)
open import PathSum.Ancilla.Register M₀ using
  (Prepared; mask; set0ᶜ; amp-input; _≋⟨_⟩₀_; ≋⟨⟩₀-set0ᶜ)
open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; _=ᵇ_; same; same-true; same-≗)
open import PathSum.AssignSum using (_∷ᵃ_)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out)
open import PathSum.CircuitSemantics M₀ using (Column; δ; δ-resp)
open import PathSum.Compose.Properties M₀ using
  (applyᴾ; applyᴾ-linear; hits-same)
open import PathSum.Compose.Sum M₀ using (if-cong; zpow-≡)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; _·ᴬ_; zpow; scale; scale-map; Respects)
open import PathSum.Denotation M₀ using
  (Assign; amp; hits; outBit; outBit-μ; amp-≗; _≋_)
open import PathSum.HiddenShift M₀ using
  (Oᴾ; shiftᴾ; mmᴾ; dualᴾ; bool-shiftᴾ; boolᴾ; HS; hs-norm; hidden-shift;
   scale-0ᴬ; Σᴮ-none; none)
open import PathSum.HiddenShift.Circuit M₀ using
  (sumᴾ; fTerms; f̃Terms; oracleᶠ; oracleᵈ; bool-f; bool-f̃)
open import PathSum.HiddenShift.Gates M₀ using
  (lift; norm-lift; applyᴬ-lift; slice-resp; upper; norm-upper;
   applyᴬ-upper; sliceʳ-resp; Signs; signed; Term; norm-oracle;
   Signs-oracle)
open import PathSum.HiddenShift.Layers M₀ using
  (hadamards; norm-hadamards; Sim; sim; sim-resp; simulates; Sim-∘; Sim-δ;
   Sim-hadamards; Sim-signs; applyᴾ-Oᴾ′)
open import PathSum.HiddenShift.Sign M₀ using (1ᴬ)
open import PathSum.HiddenShift.Walsh using
  (0ᵃ; _⊕ᵃ_; _⧺_; ⧺-↑ˡ; ⧺-↑ʳ; ⧺-split; rhalf)
open import PathSum.Polynomial using (Poly; x[_]; 0ᴾ; μ; eval; sgn)
open import PathSum.Polynomial.Product using (eval-0ᴾ)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.CRK.Adjoint M using (norm-++)
open import PathSum.CRK.Circuit M using (Gate; CNOT; Circuit; norm; ⟦_⟧)
open import PathSum.CRK.Semantics M₀ using
  (gateᴬ; applyᴬ; applyᴬ-++; applyᴬ-cong; applyᴬ-resp; gateᴬ-resp;
   prop-2-10)

private
  variable
    k l m : ℕ


------------------------------------------------------------------------
-- CNOTs from a second register

-- k target wires followed by l control wires; the i-th target is
-- controlled by the control wire ρ i.

cnots : (ρ : Fin k → Fin l) → Circuit (k ℕ+ l)
cnots {zero}      ρ = []
cnots {suc k} {l} ρ =
  CNOT (suc (k ↑ʳ ρ zero)) zero (λ ()) ∷ lift (cnots (λ i → ρ (suc i)))

norm-cnots : (ρ : Fin k → Fin l) → norm (cnots ρ) ≡ 0
norm-cnots {zero}  ρ = refl
norm-cnots {suc k} ρ = trans (norm-lift (cnots (λ i → ρ (suc i))))
                             (norm-cnots (λ i → ρ (suc i)))

-- They add the controls to the targets.

applyᴬ-cnots : (ρ : Fin k → Fin l) (ψ : Column (k ℕ+ l)) → Respects ψ →
               (u : Assign k) (v : Assign l) →
               applyᴬ (cnots ρ) ψ (u ⧺ v) ≐ ψ ((u ⊕ᵃ (λ i → v (ρ i))) ⧺ v)
applyᴬ-cnots {zero}      ρ ψ r u v i = refl
applyᴬ-cnots {suc k} {l} ρ ψ r u v i =
  trans (applyᴬ-lift (cnots ρ′) (gateᴬ-resp g r) (u zero) (tu ⧺ v) i)
    (trans (applyᴬ-cnots ρ′ (λ w → gateᴬ g ψ (u zero ∷ᵃ w))
                         (slice-resp (gateᴬ-resp g r) (u zero)) tu v i)
           (r _ _ at i))
  where
  ρ′ : Fin k → Fin l
  ρ′ j = ρ (suc j)

  tu : Assign k
  tu j = u (suc j)

  g : Gate (suc (k ℕ+ l))
  g = CNOT (suc (k ↑ʳ ρ zero)) zero (λ ())

  W : Assign (k ℕ+ l)
  W = (tu ⊕ᵃ (λ j → v (ρ′ j))) ⧺ v

  at : ∀ j → ((u zero ∷ᵃ W) [ zero ≔ u zero xor W (k ↑ʳ ρ zero) ]) j ≡
             ((u ⊕ᵃ (λ j → v (ρ j))) ⧺ v) j
  at zero    = cong (u zero xor_) (⧺-↑ʳ (tu ⊕ᵃ (λ j → v (ρ′ j))) v (ρ zero))
  at (suc j) = refl


------------------------------------------------------------------------
-- Circuits acting slice by slice

-- On every column, the entries with the second register at v are L v
-- applied to the slice at v.

record Slices (C : Circuit (k ℕ+ l)) (L : Assign l → Column k → Column k) :
              Set where
  constructor slices
  field
    on-slices  : (Φ : Column (k ℕ+ l)) → Respects Φ →
                 ∀ u v → applyᴬ C Φ (u ⧺ v) ≐ L v (λ u′ → Φ (u′ ⧺ v)) u
    slice-cong : ∀ v {ψ ψ′ : Column k} → (∀ u → ψ u ≐ ψ′ u) →
                 ∀ u → L v ψ u ≐ L v ψ′ u

open Slices public

-- Concatenation, circuits on the first register, and CNOTs around one.

Slices-++ : (C D : Circuit (k ℕ+ l)) {L L′ : Assign l → Column k → Column k} →
            Slices C L → Slices D L′ → Slices (C ++ D) (λ v ψ → L′ v (L v ψ))
Slices-++ C D {L} {L′} SC SD = slices
  (λ Φ r u v i → trans (cong (λ F → F (u ⧺ v) i) (applyᴬ-++ C D Φ))
    (trans (on-slices SD (applyᴬ C Φ) (applyᴬ-resp C r) u v i)
           (slice-cong SD v (λ u′ → on-slices SC Φ r u′ v) u i)))
  (λ v h → slice-cong SD v (slice-cong SC v h))

Slices-upper : (C : Circuit k) → Slices {k} {l} (upper l C) (λ v → applyᴬ C)
Slices-upper {l = l} C = slices
  (λ Φ r u v → applyᴬ-upper l C r u v)
  (λ v h → applyᴬ-cong C h)

-- The slice at v, shifted by v on either side of O.

shifted : ∀ {n} → Assign n → Circuit n → Column n → Column n
shifted v O ψ u = applyᴬ O (λ u′ → ψ (u′ ⊕ᵃ v)) (u ⊕ᵃ v)

private
  ⊕-resp : ∀ {n} (v : Assign n) {u u′ : Assign n} → (∀ j → u j ≡ u′ j) →
           ∀ j → (u ⊕ᵃ v) j ≡ (u′ ⊕ᵃ v) j
  ⊕-resp v h j = cong (_xor v j) (h j)

  shift-resp : ∀ {n} (v : Assign n) {ψ : Column n} → Respects ψ →
               Respects (λ u → ψ (u ⊕ᵃ v))
  shift-resp v r u u′ h = r (u ⊕ᵃ v) (u′ ⊕ᵃ v) (⊕-resp v h)

  xor-back : ∀ a b → (a xor b) xor b ≡ a
  xor-back false false = refl
  xor-back false true  = refl
  xor-back true  false = refl
  xor-back true  true  = refl

Slices-shifted : ∀ {n} (O : Circuit n) →
                 Slices (cnots {n} {n} (λ i → i) ++
                         (upper n O ++ cnots {n} {n} (λ i → i)))
                        (λ v → shifted v O)
Slices-shifted {n} O = slices
  (λ Φ r u v i →
    trans (cong (λ F → F (u ⧺ v) i) (applyᴬ-++ X (upper n O ++ X) Φ))
      (trans (cong (λ F → F (u ⧺ v) i)
                   (applyᴬ-++ (upper n O) X (applyᴬ X Φ)))
        (trans (applyᴬ-cnots (λ j → j) (applyᴬ (upper n O) (applyᴬ X Φ))
                             (applyᴬ-resp (upper n O) (applyᴬ-resp X r)) u v i)
          (trans (applyᴬ-upper n O (applyᴬ-resp X r) (u ⊕ᵃ v) v i)
                 (applyᴬ-cong O {λ u′ → applyᴬ X Φ (u′ ⧺ v)}
                              {λ u′ → Φ ((u′ ⊕ᵃ v) ⧺ v)}
                              (λ u′ → applyᴬ-cnots (λ j → j) Φ r u′ v)
                              (u ⊕ᵃ v) i)))))
  (λ v h u → applyᴬ-cong O (λ u′ → h (u′ ⊕ᵃ v)) (u ⊕ᵃ v))
  where
  X : Circuit (n ℕ+ n)
  X = cnots {n} {n} (λ i → i)

-- On a slice, the shifted oracle is the oracle of the shifted
-- exponent, with no normalisation.

Sim-slice-shifted : ∀ {n} (v : Assign n) {O : Circuit n} {b : Assign n → Bool} →
                    Signs O b → (E : Poly n 0) → (∀ z → b z ≡ boolᴾ E z) →
                    Sim (shifted v O) (Oᴾ (shiftᴾ v E)) 0
Sim-slice-shifted v {O} {b} sO E h = sim
  (λ ψ r u u′ uu → applyᴬ-resp O (shift-resp v r) (u ⊕ᵃ v) (u′ ⊕ᵃ v)
                                 (⊕-resp v uu))
  (λ ψ r u i → trans (signed sO (λ u′ → ψ (u′ ⊕ᵃ v)) (shift-resp v r)
                             (u ⊕ᵃ v) i)
    (trans (cong (sgn (b (u ⊕ᵃ v)) *_)
                 (r ((u ⊕ᵃ v) ⊕ᵃ v) u (λ j → xor-back (u j) (v j)) i))
      (trans (cong (λ t → sgn t * ψ u i)
                   (trans (h (u ⊕ᵃ v)) (sym (bool-shiftᴾ v E u))))
             (sym (applyᴾ-Oᴾ′ (shiftᴾ v E) ψ r u i)))))


------------------------------------------------------------------------
-- Figure 3(b)

-- The data register first, the shift register after it.

SSᶜ : List (Term m) → Circuit ((m ℕ+ m) ℕ+ (m ℕ+ m))
SSᶜ {m} gs =
  (((upper n (hadamards n) ++ X) ++ upper n (hadamards n)) ++
    upper n (oracleᵈ gs)) ++ upper n (hadamards n)
  where
  n : ℕ
  n = m ℕ+ m

  X : Circuit (n ℕ+ n)
  X = cnots {n} {n} (λ i → i) ++
      (upper n (oracleᶠ gs) ++ cnots {n} {n} (λ i → i))

-- What it does to the slice at v.

slice-op : List (Term m) → Assign (m ℕ+ m) → Column (m ℕ+ m) →
           Column (m ℕ+ m)
slice-op {m} gs v ψ =
  applyᴬ (hadamards (m ℕ+ m))
    (applyᴬ (oracleᵈ gs)
      (applyᴬ (hadamards (m ℕ+ m))
        (shifted v (oracleᶠ gs) (applyᴬ (hadamards (m ℕ+ m)) ψ))))

Slices-SSᶜ : (gs : List (Term m)) → Slices (SSᶜ gs) (slice-op gs)
Slices-SSᶜ {m} gs =
  Slices-++ (((A ++ X) ++ A) ++ D) A
    (Slices-++ ((A ++ X) ++ A) D
      (Slices-++ (A ++ X) A
        (Slices-++ A X (Slices-upper (hadamards n))
                       (Slices-shifted (oracleᶠ gs)))
        (Slices-upper (hadamards n)))
      (Slices-upper (oracleᵈ gs)))
    (Slices-upper (hadamards n))
  where
  n : ℕ
  n = m ℕ+ m

  A D X : Circuit (n ℕ+ n)
  A = upper n (hadamards n)
  D = upper n (oracleᵈ gs)
  X = cnots {n} {n} (λ i → i) ++
      (upper n (oracleᶠ gs) ++ cnots {n} {n} (λ i → i))

-- On the slice at v it is the composite HS g v.

Sim-slice : (gs : List (Term m)) (v : Assign (m ℕ+ m)) →
            Sim (slice-op gs v) (HS (sumᴾ gs) v) 0
Sim-slice {m} gs v =
  Sim-∘ (Sim-∘ (Sim-∘ (Sim-∘ (Sim-hadamards n)
                               (Sim-slice-shifted v (Signs-oracle (fTerms gs))
                                                  (mmᴾ (sumᴾ gs)) (bool-f gs)))
                       (Sim-hadamards n))
               (Sim-signs (Signs-oracle (f̃Terms gs)) (dualᴾ (sumᴾ gs))
                          (bool-f̃ gs)))
        (Sim-hadamards n)
  where
  n : ℕ
  n = m ℕ+ m

-- Its normalisation is 3n.

norm-SSᶜ : (gs : List (Term m)) → norm (SSᶜ gs) ≡ hs-norm (m ℕ+ m)
norm-SSᶜ {m} gs =
  trans (norm-++ (((A ++ X) ++ A) ++ D) A)
    (cong₂ _ℕ+_
      (trans (norm-++ ((A ++ X) ++ A) D)
        (cong₂ _ℕ+_
          (trans (norm-++ (A ++ X) A)
            (cong₂ _ℕ+_ (trans (norm-++ A X) (cong₂ _ℕ+_ nA nX)) nA))
          (trans (norm-upper n (oracleᵈ gs)) (norm-oracle (f̃Terms gs)))))
      nA)
  where
  n : ℕ
  n = m ℕ+ m

  A D X : Circuit (n ℕ+ n)
  A = upper n (hadamards n)
  D = upper n (oracleᵈ gs)
  X = cnots {n} {n} (λ i → i) ++
      (upper n (oracleᶠ gs) ++ cnots {n} {n} (λ i → i))

  nA : norm A ≡ n
  nA = trans (norm-upper n (hadamards n)) (norm-hadamards n)

  nX : norm X ≡ 0
  nX = trans (norm-++ (cnots {n} {n} (λ i → i))
                      (upper n (oracleᶠ gs) ++ cnots {n} {n} (λ i → i)))
    (cong₂ _ℕ+_ (norm-cnots {n} {n} (λ i → i))
      (trans (norm-++ (upper n (oracleᶠ gs)) (cnots {n} {n} (λ i → i)))
        (cong₂ _ℕ+_ (trans (norm-upper n (oracleᶠ gs))
                           (norm-oracle (fTerms gs)))
                    (norm-cnots {n} {n} (λ i → i)))))


------------------------------------------------------------------------
-- The circuit's amplitudes

-- Comparing concatenations compares the blocks.

same-⧺ : (a c : Assign k) (b d : Assign l) →
         same (a ⧺ b) (c ⧺ d) ≡ same a c ∧ same b d
same-⧺ {k = zero}  a c b d = refl
same-⧺ {k = suc k} a c b d = trans
  (cong ((a zero =ᵇ c zero) ∧_)
        (same-⧺ (λ i → a (suc i)) (λ i → c (suc i)) b d))
  (sym (∧-assoc (a zero =ᵇ c zero)
                (same (λ i → a (suc i)) (λ i → c (suc i))) (same b d)))

-- A simulating operator sends the zero column to zero.

private
  applyᴾ-0 : ∀ {n k′ m′} (ξ : PathSum n k′ m′) (z : Assign n) →
             applyᴾ ξ (λ _ → 0ᴬ) z ≐ 0ᴬ
  applyᴾ-0 ξ z i = trans (applyᴾ-linear (·ᴬ-linear 0ℤ) ξ (λ _ → 0ᴬ) z i)
                         (*-zeroˡ (applyᴾ ξ (λ _ → 0ᴬ) z i))

  Sim-0 : ∀ {n k′ m′} {L : Column n → Column n} {ξ : PathSum n k′ m′} {e : ℕ} →
          Sim L ξ e → ∀ z → L (λ _ → 0ᴬ) z ≐ 0ᴬ
  Sim-0 {ξ = ξ} {e} S z i =
    trans (simulates S (λ _ → 0ᴬ) (λ _ _ _ _ → refl) z i)
          (trans (scale-map e (applyᴾ-0 ξ z) i) (scale-0ᴬ e i))

-- The circuit is Σ_t HS(g, t) ⊗ |t⟩⟨t|: from |x⟩|t⟩ it reaches only
-- outputs |u⟩|t⟩, with HS g t's amplitude from |x⟩ to |u⟩.

symbolic-shift : (gs : List (Term m)) (x t u v : Assign (m ℕ+ m)) →
                 amp ⟦ SSᶜ gs ⟧ (x ⧺ t) (u ⧺ v) ≐
                 (if same t v then amp (HS (sumᴾ gs) v) x u else 0ᴬ)
symbolic-shift {m} gs x t u v i =
  trans (prop-2-10 (SSᶜ gs) (x ⧺ t) (u ⧺ v) i)
    (trans (on-slices (Slices-SSᶜ gs) (δ (x ⧺ t)) (δ-resp (x ⧺ t)) u v i)
           (pick (same t v) refl i))
  where
  σ : Column (m ℕ+ m)
  σ u′ = δ (x ⧺ t) (u′ ⧺ v)

  σ-guard : ∀ u′ → σ u′ ≐ (if same x u′ ∧ same t v then zpow 0ℤ else 0ᴬ)
  σ-guard u′ l = cong (λ b → (if b then zpow 0ℤ else 0ᴬ) l)
                      (same-⧺ x u′ t v)

  pick : ∀ b → same t v ≡ b →
         slice-op gs v σ u ≐ (if b then amp (HS (sumᴾ gs) v) x u else 0ᴬ)
  pick true  e l = trans
    (slice-cong (Slices-SSᶜ gs) v {σ} {δ x} (λ u′ l′ → trans (σ-guard u′ l′)
      (cong (λ b → (if b then zpow 0ℤ else 0ᴬ) l′)
            (trans (cong (same x u′ ∧_) e) (∧-identityʳ (same x u′))))) u l)
    (Sim-δ (Sim-slice gs v) x u l)
  pick false e l = trans
    (slice-cong (Slices-SSᶜ gs) v {σ} {λ _ → 0ᴬ}
                (λ u′ l′ → trans (σ-guard u′ l′)
      (cong (λ b → (if b then zpow 0ℤ else 0ᴬ) l′)
            (trans (cong (same x u′ ∧_) e) (∧-zeroʳ (same x u′))))) u l)
    (Sim-0 (Sim-slice gs v) u l)

-- The paper's specification |0⟩|s⟩ ↦ |s⟩|s⟩, for every s: the only
-- output reached is |s⟩|s⟩, with amplitude √2^K before the
-- normalisation 1/√2^K, K = 3n.

symbolic-shift-0 : (gs : List (Term m)) (s : Assign (m ℕ+ m))
                   (z : Assign ((m ℕ+ m) ℕ+ (m ℕ+ m))) →
                   amp ⟦ SSᶜ gs ⟧ (0ᵃ {m ℕ+ m} ⧺ s) z ≐
                   (if same (s ⧺ s) z then scale (norm (SSᶜ gs)) (zpow 0ℤ)
                    else 0ᴬ)
symbolic-shift-0 {m} gs s z i =
  trans (amp-≗ ⟦ SSᶜ gs ⟧ (0ᵃ {m ℕ+ m} ⧺ s) (λ j → sym (⧺-split n n z j)) i)
    (trans (symbolic-shift gs 0ᵃ s u v i)
      (trans (pick (same s v) refl i)
             (cong (λ b → (if b then scale (norm (SSᶜ gs)) (zpow 0ℤ)
                           else 0ᴬ) i)
                   (sym (trans (same-≗ {x = s ⧺ s} {x′ = s ⧺ s}
                                       {z = z} {z′ = u ⧺ v} (λ _ → refl)
                                       (λ j → sym (⧺-split n n z j)))
                               (same-⧺ s u s v))))))
  where
  n : ℕ
  n = m ℕ+ m

  u v : Assign n
  u j = z (j ↑ˡ n)
  v j = z (n ↑ʳ j)

  pick : ∀ b → same s v ≡ b →
         (if b then amp (HS (sumᴾ gs) v) 0ᵃ u else 0ᴬ) ≐
         (if same s u ∧ b then scale (norm (SSᶜ gs)) (zpow 0ℤ) else 0ᴬ)
  pick false e l = cong (λ c → (if c then scale (norm (SSᶜ gs)) (zpow 0ℤ)
                                else 0ᴬ) l)
                        (sym (∧-zeroʳ (same s u)))
  pick true  e l = trans (hidden-shift (sumᴾ gs) v u l)
    (trans (cong (λ c → (if c then scale (hs-norm n) (zpow 0ℤ) else 0ᴬ) l)
                 (trans (same-≗ {x = v} {x′ = s} {z = u} {z′ = u}
                                (λ j → sym (same-true s v e j)) (λ _ → refl))
                        (sym (∧-identityʳ (same s u)))))
           (fix (same s u ∧ true) l))
    where
    fix : ∀ c → (if c then scale (hs-norm n) (zpow 0ℤ) else 0ᴬ) ≐
                (if c then scale (norm (SSᶜ gs)) (zpow 0ℤ) else 0ᴬ)
    fix true  = scale-exp (zpow 0ℤ) (sym (norm-SSᶜ gs))
    fix false _ = refl

-- The same, as a statement named by its argument, for closed
-- instances (PathSum.HiddenShift.CircuitExample).

record SymbolicShiftSpec (gs : List (Term m)) : Set where
  constructor symbolic-shift-spec-at
  field
    column-at-0s : ∀ (s : Assign (m ℕ+ m)) z →
                   amp ⟦ SSᶜ gs ⟧ (0ᵃ {m ℕ+ m} ⧺ s) z ≐
                   (if same (s ⧺ s) z then scale (norm (SSᶜ gs)) (zpow 0ℤ)
                    else 0ᴬ)

symbolic-shift-spec : (gs : List (Term m)) → SymbolicShiftSpec gs
symbolic-shift-spec gs = symbolic-shift-spec-at (symbolic-shift-0 gs)


------------------------------------------------------------------------
-- The specification as a path-sum

-- Concatenating two functions on wires.

infixr 5 _⊹_

_⊹_ : {A : Set} → (Fin k → A) → (Fin l → A) → Fin (k ℕ+ l) → A
_⊹_ {k = zero}  f g j       = g j
_⊹_ {k = suc k} f g zero    = f zero
_⊹_ {k = suc k} f g (suc j) = ((λ i → f (suc i)) ⊹ g) j

⊹-⧺ : ∀ {n} (x : Assign n) (f : Fin k → Fin n) (g : Fin l → Fin n) →
      ∀ j → x ((f ⊹ g) j) ≡ ((λ i → x (f i)) ⧺ (λ i → x (g i))) j
⊹-⧺ {k = zero}  x f g j       = refl
⊹-⧺ {k = suc k} x f g zero    = refl
⊹-⧺ {k = suc k} x f g (suc j) = ⊹-⧺ x (λ i → f (suc i)) g j

-- |x_d, x_s⟩ ↦ |x_s, x_s⟩: the output copies the second register onto
-- both.

copy : ∀ n → Fin (n ℕ+ n) → Fin (n ℕ+ n)
copy n = (λ i → n ↑ʳ i) ⊹ (λ i → n ↑ʳ i)

specSᴾ : ∀ n → PathSum (n ℕ+ n) 0 0
specSᴾ n = ⟨ 0ᴾ , (λ w → μ x[ copy n w ]) ⟩

amp-specSᴾ : ∀ n (x z : Assign (n ℕ+ n)) →
             amp (specSᴾ n) x z ≐
             (if same (rhalf {n} x ⧺ rhalf {n} x) z then 1ᴬ else 0ᴬ)
amp-specSᴾ n x z = Σᴮ-none
  (λ y → if hits (specSᴾ n) x y z
         then zpow (eval (phase (specSᴾ n)) x y) else 0ᴬ)
  (λ y → if-cong (guard y) (zpow-≡ (eval-0ᴾ x y)))
  where
  guard : ∀ y → hits (specSᴾ n) x y z ≡ same (rhalf {n} x ⧺ rhalf {n} x) z
  guard y = trans (hits-same (specSᴾ n) x y z)
    (same-≗ {x = outBit (specSᴾ n) x y} {x′ = rhalf {n} x ⧺ rhalf {n} x}
            {z = z} {z′ = z}
            (λ w → trans (outBit-μ (specSᴾ n) x y w x[ copy n w ] refl)
                         (⊹-⧺ x (λ i → n ↑ʳ i) (λ i → n ↑ʳ i) w))
            (λ _ → refl))

-- The data register, marked for preparation in |0⟩.

dataMask : ∀ n → Fin (n ℕ+ n) → Bool
dataMask n = (λ (_ : Fin n) → true) ⧺ (λ (_ : Fin n) → false)

-- Concatenation respects pointwise equality in both blocks.

⧺-cong₂ : {a a′ : Assign k} {b b′ : Assign l} → (∀ i → a i ≡ a′ i) →
          (∀ i → b i ≡ b′ i) → ∀ j → (a ⧺ b) j ≡ (a′ ⧺ b′) j
⧺-cong₂ {k = zero}  ha hb j       = hb j
⧺-cong₂ {k = suc k} ha hb zero    = ha zero
⧺-cong₂ {k = suc k} ha hb (suc j) = ⧺-cong₂ (λ i → ha (suc i)) hb j

-- A prepared input is 0 followed by its second register.

private
  prepared-split : ∀ {n} (x : Assign (n ℕ+ n)) → Prepared (dataMask n) x →
                   ∀ j → x j ≡ (0ᵃ {n} ⧺ rhalf {n} x) j
  prepared-split {n} x p j = trans (sym (⧺-split n n x j))
    (⧺-cong₂ {a = λ i → x (i ↑ˡ n)} {a′ = 0ᵃ {n}}
             {b = rhalf {n} x} {b′ = rhalf {n} x}
             (λ i → p (i ↑ˡ n) (⧺-↑ˡ (λ (_ : Fin n) → true)
                                     (λ (_ : Fin n) → false) i))
             (λ _ → refl) j)

-- With the data register prepared in |0⟩, the circuit is the
-- specification, the shift being the input variables of the second
-- register.

symbolic-shift-≋ : (gs : List (Term m)) →
                   ⟦ SSᶜ gs ⟧ ≋⟨ dataMask (m ℕ+ m) ⟩₀ specSᴾ (m ℕ+ m)
symbolic-shift-≋ {m} gs x z p i =
  trans (amp-input ⟦ SSᶜ gs ⟧ (prepared-split {m ℕ+ m} x p) z i)
    (trans (symbolic-shift-0 gs (rhalf {m ℕ+ m} x) z i)
      (sym (trans (scale-map (norm (SSᶜ gs)) (amp-specSᴾ (m ℕ+ m) x z) i)
                  (pick (same (rhalf {m ℕ+ m} x ⧺ rhalf {m ℕ+ m} x) z) i))))
  where
  pick : ∀ b → scale (norm (SSᶜ gs)) (if b then 1ᴬ else 0ᴬ) ≐
               (if b then scale (norm (SSᶜ gs)) (zpow 0ℤ) else 0ᴬ)
  pick true  l = refl
  pick false l = scale-0ᴬ (norm (SSᶜ gs)) l

-- The path-sum of the circuit with the data register read as 0 is the
-- specification.

symbolic-shift-set0 : (gs : List (Term m)) →
                      set0ᶜ (dataMask (m ℕ+ m)) ⟦ SSᶜ gs ⟧ ≋ specSᴾ (m ℕ+ m)
symbolic-shift-set0 {m} gs = ≋⟨⟩₀-set0ᶜ (dataMask n) ⟦ SSᶜ gs ⟧ (specSᴾ n)
  (symbolic-shift-≋ gs)
  (λ x z l → trans (amp-specSᴾ n (mask (dataMask n) x) z l)
    (trans (cong (λ b → (if b then 1ᴬ else 0ᴬ) l)
                 (same-≗ {x = rhalf {n} (mask (dataMask n) x) ⧺
                              rhalf {n} (mask (dataMask n) x)}
                         {x′ = rhalf {n} x ⧺ rhalf {n} x} {z = z} {z′ = z}
                         (⧺-cong₂ (keep x) (keep x)) (λ _ → refl)))
           (sym (amp-specSᴾ n x z l))))
  where
  n : ℕ
  n = m ℕ+ m

  -- The mask leaves the second register alone.
  keep : (x : Assign (n ℕ+ n)) →
         ∀ i → mask (dataMask n) x (n ↑ʳ i) ≡ x (n ↑ʳ i)
  keep x i = cong (λ b → if b then false else x (n ↑ʳ i))
                  (⧺-↑ʳ (λ (_ : Fin n) → true) (λ (_ : Fin n) → false) i)

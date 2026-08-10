------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantic content of Proposition 2.55's `sound-ax` for the qubit
-- Clifford extension: how Pauli words behave in CMS n.
--
-- sound-ax has to check two families against the P4-action:
--
--   ConjRelʷ conj   x · y = conj x y · x   for a gate x and a Pauli
--                   generator y — conj records conjugation in CMS n;
--   RelTwist  corr  [ ū ]ᵣ = [ corr r̄ ]ₗ · [ v̄ ]ᵣ  for each symplectic
--                   relator r̄ — corr records the Pauli that lifting r̄
--                   accumulates.
--
-- This module proves the two lemmas the first family rests on, both
-- about `pauliWord` (which IS the extension's inclusion, so ⟦_⟧₀ of a
-- Pauli generator):
--
--   pauliWord-∙    pauliWord P · pauliWord Q = pauliWord (P +ₚ Q)
--   pauli-conj     x · pauliWord P = pauliWord (actg x P) · x
--
-- The second is the conjugation law itself, and its proof is the one
-- line of mathematics in the whole family: conjugating by a Clifford
-- moves the phase by ι (sform P R), and the symplectic action preserves
-- sform (Interpretation.actg-sform), so both sides collect the same
-- phase.  Nothing is computed gate by gate — no case analysis on x at
-- all — which is what keeps this clear of the cact blow-up that
-- Selinger.Soundness has to work around.
--
-- Both families are now closed:
--
--   conj-sound     the ConjRelʷ axiom, via the delogging lemma (`delog`:
--                  ⟦_⟧ of a left-embedded vecToWord P is pauliWord P) and
--                  pauli-conj at P = genToVec y, since conj x y is by
--                  definition vecToWord (actg x (genToVec y));
--   twisted-sound  the RelTwist family, for EVERY relator: axiom-sound
--                  discharges all fifteen raw axioms and twist-sound
--                  carries them through cong↑, comm₁ and comm₂.
--
-- What separates these from `sound-ax` itself is now only bookkeeping:
-- the two must be read through Proposition 2.55's ⟦_⟧ on the mixed
-- alphabet, i.e. ⟦ [ w ]ₗ ⟧ = pw w and ⟦ [ w ]ᵣ ⟧ = w.
------------------------------------------------------------------------

-- --call-by-name: the axiom-sound clauses for selinger-c14 / c15 have
-- long words in their goals, and call-by-need normalisation of cact
-- along them exhausts memory (see the note at axiom-sound). 
{-# OPTIONS --cubical-compatible --safe --call-by-name #-}

module Examples.Groups.Clifford.Qubit.ExtensionSoundness where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Zp.ModularArithmetic
open import Data.Sum using (inj₂)
open import Data.Vec using (_∷_ ; [])
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; wmap)

open import Examples.Groups.Clifford.Qubit.CliffordGroup
  using ( p-2 ; p-prime ; _≈ᶜ_ ; pauliWord ; cact-pauliWord ; sform-+ˡ
        ; ≈ᶜ-refl ; ≈ᶜ-sym ; ≈ᶜ-trans ; ∙-congᶜ )
open import Examples.Groups.Clifford.Qubit.Presentation
  using (PauliGen ; genToVec ; vecToWord ; conj ; corr ; shiftPauli)

open import Examples.Groups.Clifford.Qubit.PrimitiveRoot using (g* ; g-gen)
open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
  using (module Simplified-Relations)
open Simplified-Relations
  using (_QRel,_===_ ; srel ; cong↑ ; comm₁ ; comm₂ ; module SimBase ; M₋₁)
open SimBase
  using ( _SRel,_===_ ; order-S ; order-H ; M-power ; semi-MS ; semi-M↑CZ
        ; semi-M↓CZ ; order-CZ ; comm-CZ-S↓ ; comm-CZ-S↑
        ; selinger-c10 ; selinger-c11 ; selinger-c12 ; selinger-c13
        ; selinger-c14 ; selinger-c15 )
open import Examples.Groups.Clifford.Qubit.Selinger.Soundness
  using (sound-↑ ; comm₁-sound ; comm₂-sound ; cω↑-sound ; c14-sound ; c15-sound)
open import Examples.Groups.Clifford.Qubit.Selinger.Action
  using (cact-ω ; lift-eq ; c12-sound ; c13-sound)
open import Examples.Groups.Clifford.Qubit.CliffordGroup using (identityˡᶜ)

open PrimeModulus p-2 p-prime

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using ( Pauli ; Pauli1 ; pI ; pIₙ ; sform ; sform1 ; _+ₚ_
        ; +₁-identityˡ ; +ₚ-identityˡ )
import Examples.Groups.Symplectic.Semantics p-2 p-prime as SympSem
open SympSem.Interpretation using (actg ; actg-sform)
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic
  using ( Gen ; Circuit ; gate₁ ; gate₂ ; _↥ ; _↑ ; _↓
        ; S ; S⁻¹ ; H ; CZ ; ⊤⊥ ; ⊥⊤ )

open import Examples.Groups.SignedPauli-Qubit.SignedPauli using (Φ ; P4Carrier ; ι ; ι-+)
open import Examples.Groups.Clifford.Qubit.CliffordAction using (cact ; δ ; incl)
open import Examples.Groups.Clifford.Qubit.CliffordGroup using (incl-2)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- ℤ/4 rearrangements

private
  -- (s + a) + b ≡ s + (b + a): the two orders in which two phases can be
  -- collected onto s.
  swap-onto : (s a b : Φ) → (s + a) + b ≡ s + (b + a)
  swap-onto s a b = Eq.trans (+-assoc s a b) (Eq.cong (s +_) (+-comm a b))

------------------------------------------------------------------------
-- Pauli words multiply by adding their vectors
--
-- Conjugation by P shifts the phase by ι (sform P R) and fixes the
-- phaseless Pauli (CliffordGroup.cact-pauliWord), so composing two of
-- them adds the two shifts — and sform is additive in its first
-- argument.

pauliWord-∙ : (P Q : Pauli n) →
              (pauliWord P • pauliWord Q) ≈ᶜ pauliWord (P +ₚ Q)
pauliWord-∙ P Q (s , R) = begin
  cact (pauliWord P) (cact (pauliWord Q) (s , R))
    ≡⟨ Eq.cong (cact (pauliWord P)) (cact-pauliWord Q s R) ⟩
  cact (pauliWord P) (s + ι (sform Q R) , R)
    ≡⟨ cact-pauliWord P (s + ι (sform Q R)) R ⟩
  ((s + ι (sform Q R)) + ι (sform P R)) , R
    ≡⟨ Eq.cong (_, R) (swap-onto s (ι (sform Q R)) (ι (sform P R))) ⟩
  (s + (ι (sform P R) + ι (sform Q R))) , R
    ≡⟨ Eq.cong (λ □ → (s + □) , R) (Eq.sym (ι-+ (sform P R) (sform Q R))) ⟩
  (s + ι (sform P R + sform Q R)) , R
    ≡⟨ Eq.cong (λ □ → (s + ι □) , R) (Eq.sym (sform-+ˡ P Q R)) ⟩
  (s + ι (sform (P +ₚ Q) R)) , R
    ≡⟨ Eq.sym (cact-pauliWord (P +ₚ Q) s R) ⟩
  cact (pauliWord (P +ₚ Q)) (s , R)   ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Conjugation: a gate moves a Pauli word past itself, symplectically
--
-- This is the ConjRelʷ family's mathematical content.  Reading both
-- sides at (s , R):
--
--   x · P  :  R ↦ actg x R,  phase  s + ι (sform P R)      + δ x R
--   (x·P·x⁻¹) · x :  R ↦ actg x R,  phase  s + δ x R + ι (sform (actg x P) (actg x R))
--
-- and the two phases agree because actg x preserves sform.  No gate is
-- ever unfolded: `x` stays a variable throughout.

pauli-conj : (x : Gen n) (P : Pauli n) →
             ([ x ]ʷ • pauliWord P) ≈ᶜ (pauliWord (actg x P) • [ x ]ʷ)
pauli-conj x P (s , R) = begin
  cact [ x ]ʷ (cact (pauliWord P) (s , R))
    ≡⟨ Eq.cong (cact [ x ]ʷ) (cact-pauliWord P s R) ⟩
  cact [ x ]ʷ (s + ι (sform P R) , R)
    ≡⟨ Eq.refl ⟩
  ((s + ι (sform P R)) + δ x R) , actg x R
    ≡⟨ Eq.cong (_, actg x R) (swap-onto s (ι (sform P R)) (δ x R)) ⟩
  (s + (δ x R + ι (sform P R))) , actg x R
    ≡⟨ Eq.cong (λ □ → (s + (δ x R + ι □)) , actg x R)
               (Eq.sym (actg-sform x P R)) ⟩
  (s + (δ x R + ι (sform (actg x P) (actg x R)))) , actg x R
    ≡⟨ Eq.cong (_, actg x R)
               (Eq.sym (+-assoc s (δ x R) (ι (sform (actg x P) (actg x R))))) ⟩
  ((s + δ x R) + ι (sform (actg x P) (actg x R))) , actg x R
    ≡⟨ Eq.sym (cact-pauliWord (actg x P) (s + δ x R) (actg x R)) ⟩
  cact (pauliWord (actg x P)) (s + δ x R , actg x R)
    ≡⟨ Eq.refl ⟩
  cact (pauliWord (actg x P)) (cact [ x ]ʷ (s , R))   ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Delogging a Pauli word
--
-- The extension names Paulis twice over: as vectors (what actg acts on)
-- and as words over the Pauli generators (what conj returns).  The
-- interpretation of such a word in CMS n is the product of the
-- conjugations its letters name, and pauliWord-∙ turns that product into
-- a single conjugation — by the vector the word denotes.  So the whole
-- delogging question reduces to a computation on VECTORS: `vecOf`
-- undoes `vecToWord`.

-- The vector a Pauli word denotes.
vecOf : Word (PauliGen n) → Pauli n
vecOf [ y ]ʷ  = genToVec y
vecOf ε       = pIₙ
vecOf (w • v) = vecOf w +ₚ vecOf v

-- Its interpretation in CMS n: each letter is conjugation by its basis
-- vector.  (This is ⟦_⟧ of Proposition 2.55 restricted to left-embedded
-- words, spelled out without the extension machinery.)
pw : Word (PauliGen n) → Word (Gen n)
pw [ y ]ʷ  = pauliWord (genToVec y)
pw ε       = ε
pw (w • v) = pw w • pw v

-- sform vanishes on the identity in the left argument too (the library
-- has the right-hand version).
private
  sform1-pIˡ : (c d : ℤ ₚ) → sform1 pI (c , d) ≡ ₀
  sform1-pIˡ ₀ ₀ = auto
  sform1-pIˡ ₀ ₁ = auto
  sform1-pIˡ ₁ ₀ = auto
  sform1-pIˡ ₁ ₁ = auto

  sform-pIˡ : (R : Pauli n) → sform (pIₙ {n}) R ≡ ₀
  sform-pIˡ []             = Eq.refl
  sform-pIˡ ((c , d) ∷ Rs) =
    Eq.trans (Eq.cong₂ _+_ (sform1-pIˡ c d) (sform-pIˡ Rs)) (+-identityˡ ₀)

-- Conjugation by the identity Pauli is the identity.
pauliWord-pIₙ : (pauliWord (pIₙ {n})) ≈ᶜ ε
pauliWord-pIₙ (s , R) = Eq.trans (cact-pauliWord pIₙ s R)
  (Eq.cong (_, R) (Eq.trans (Eq.cong (λ □ → s + ι □) (sform-pIˡ R))
                            (+-identityʳ s)))

-- A Pauli word acts as conjugation by the vector it denotes.
-- (_≈ᶜ_ is a defined relation — equality of the P4-action — so its
-- endpoints are never inferable; every combinator below is applied with
-- them explicit.)
pw-vecOf : (w : Word (PauliGen n)) → pw w ≈ᶜ pauliWord (vecOf w)
pw-vecOf [ y ]ʷ  = ≈ᶜ-refl {w = pauliWord (genToVec y)}
pw-vecOf ε       = ≈ᶜ-sym {w = pauliWord pIₙ} {v = ε} pauliWord-pIₙ
pw-vecOf (w • v) =
  ≈ᶜ-trans {w = pw w • pw v}
           {v = pauliWord (vecOf w) • pauliWord (vecOf v)}
           {u = pauliWord (vecOf w +ₚ vecOf v)}
    (∙-congᶜ {w = pw w} {pauliWord (vecOf w)} {pw v} {pauliWord (vecOf v)}
             (pw-vecOf w) (pw-vecOf v))
    (pauliWord-∙ (vecOf w) (vecOf v))

------------------------------------------------------------------------
-- vecOf undoes vecToWord
--
-- A pure computation on vectors: the exponents are ℤ/2, so each wire
-- contributes X^a Z^b with a , b ∈ {0 , 1} and the four cases are
-- concrete.

private
  -- Shifting a Pauli word up one wire prepends the identity.
  vecOf-↑ : (w : Word (PauliGen (₁₊ n))) →
            vecOf (wmap inj₂ w) ≡ pI ∷ vecOf w
  vecOf-↑ [ y ]ʷ  = Eq.refl
  vecOf-↑ ε       = Eq.refl
  vecOf-↑ (w • v) =
    Eq.trans (Eq.cong₂ _+ₚ_ (vecOf-↑ w) (vecOf-↑ v))
             (Eq.cong (_∷ (vecOf w +ₚ vecOf v)) (+₁-identityˡ pI))

  -- Two identity summands in front of a tail.
  tail-pIₙ : (ps : Pauli n) → (pIₙ +ₚ pIₙ) +ₚ ps ≡ ps
  tail-pIₙ ps = Eq.trans (Eq.cong (_+ₚ ps) (+ₚ-identityˡ pIₙ)) (+ₚ-identityˡ ps)

vecOf-vecToWord : (P : Pauli n) → vecOf (vecToWord P) ≡ P
vecOf-vecToWord {₀}      []             = Eq.refl
vecOf-vecToWord {₁₊ ₀}   ((₀ , ₀) ∷ []) = auto
vecOf-vecToWord {₁₊ ₀}   ((₀ , ₁) ∷ []) = auto
vecOf-vecToWord {₁₊ ₀}   ((₁ , ₀) ∷ []) = auto
vecOf-vecToWord {₁₊ ₀}   ((₁ , ₁) ∷ []) = auto
vecOf-vecToWord {₂₊ n}   ((₀ , ₀) ∷ ps)
  rewrite vecOf-↑ (vecToWord ps) | vecOf-vecToWord ps =
  Eq.cong₂ _∷_ auto (tail-pIₙ ps)
vecOf-vecToWord {₂₊ n}   ((₀ , ₁) ∷ ps)
  rewrite vecOf-↑ (vecToWord ps) | vecOf-vecToWord ps =
  Eq.cong₂ _∷_ auto (tail-pIₙ ps)
vecOf-vecToWord {₂₊ n}   ((₁ , ₀) ∷ ps)
  rewrite vecOf-↑ (vecToWord ps) | vecOf-vecToWord ps =
  Eq.cong₂ _∷_ auto (tail-pIₙ ps)
vecOf-vecToWord {₂₊ n}   ((₁ , ₁) ∷ ps)
  rewrite vecOf-↑ (vecToWord ps) | vecOf-vecToWord ps =
  Eq.cong₂ _∷_ auto (tail-pIₙ ps)

-- The delogging lemma: a Pauli vector, read out as a word and
-- interpreted, is conjugation by that vector.
delog : (P : Pauli n) → pw (vecToWord P) ≈ᶜ pauliWord P
delog {n} P = Eq.subst (λ □ → pw (vecToWord P) ≈ᶜ pauliWord □)
                       (vecOf-vecToWord P) (pw-vecOf (vecToWord P))

------------------------------------------------------------------------
-- The conjugation family of sound-ax
--
-- conj x y is by definition vecToWord (actg x (genToVec y)), so with the
-- delogging lemma the ConjRelʷ axiom is exactly pauli-conj at
-- P = genToVec y.

conj-sound : (y : PauliGen n) (x : Gen n) →
             ([ x ]ʷ • pw [ y ]ʷ) ≈ᶜ (pw (conj x y) • [ x ]ʷ)
conj-sound y x =
  ≈ᶜ-trans {w = [ x ]ʷ • pauliWord (genToVec y)}
           {v = pauliWord (actg x (genToVec y)) • [ x ]ʷ}
           {u = pw (conj x y) • [ x ]ʷ}
    (pauli-conj x (genToVec y))
    (∙-congᶜ {w = pauliWord (actg x (genToVec y))}
             {pw (conj x y)} {[ x ]ʷ} {[ x ]ʷ}
             (≈ᶜ-sym {w = pw (vecToWord (actg x (genToVec y)))}
                     {v = pauliWord (actg x (genToVec y))}
                     (delog (actg x (genToVec y))))
             (≈ᶜ-refl {w = [ x ]ʷ}))

------------------------------------------------------------------------
-- The twisted-relator family of sound-ax, structurally
--
-- For a symplectic relator r̄ : ū === v̄ the twisted relation reads
-- [ ū ]ᵣ = [ corr r̄ ]ₗ · [ v̄ ]ᵣ, i.e. in CMS n
--
--     ū  ≈ᶜ  pw (corr r̄) · v̄.
--
-- corr is ε except at order-S, where it is Z₀, and it follows cong↑ by
-- shifting.  So the whole family reduces to the raw axioms: everything
-- structural — the wire shift and the two disjoint-wire commutations —
-- is discharged once and for all below, leaving one obligation per
-- axiom of the simplified rule set.

-- shiftPauli prepends the identity to the vector (the letter case is
-- vacuous at width 0, where there are no Pauli generators).
private
  vecOf-shift : (c : Word (PauliGen n)) → vecOf (shiftPauli c) ≡ pI ∷ vecOf c
  vecOf-shift {₀}    [ () ]ʷ
  vecOf-shift {₁₊ m} [ y ]ʷ  = Eq.refl
  vecOf-shift        ε       = Eq.refl
  vecOf-shift        (w • v) =
    Eq.trans (Eq.cong₂ _+ₚ_ (vecOf-shift w) (vecOf-shift v))
             (Eq.cong (_∷ (vecOf w +ₚ vecOf v)) (+₁-identityˡ pI))

-- Shifting a correction up a wire is shifting its conjugation.
pw-shift : (c : Word (PauliGen n)) → pw (shiftPauli c) ≈ᶜ (pw c) ↑
pw-shift {n} c = ≈ᶜ-trans {w = pw (shiftPauli c)}
                          {v = pauliWord (pI ∷ vecOf c)}
                          {u = (pw c) ↑}
  (Eq.subst (λ □ → pw (shiftPauli c) ≈ᶜ pauliWord □)
            (vecOf-shift c) (pw-vecOf (shiftPauli c)))
  (≈ᶜ-trans {w = pauliWord (pI ∷ vecOf c)}
            {v = (pauliWord (vecOf c)) ↑}
            {u = (pw c) ↑}
    (identityˡᶜ ((pauliWord (vecOf c)) ↑))
    (sound-↑ {w = pauliWord (vecOf c)} {v = pw c}
             (≈ᶜ-sym {w = pw c} {v = pauliWord (vecOf c)} (pw-vecOf c))))

------------------------------------------------------------------------
-- Discharging the axioms
--
-- Fourteen of the fifteen have correction ε, so their obligation is just
-- "the two sides act alike"; `plain` puts such a proof into the shape
-- twist-sound wants.  order-S is the one with content, and is done in
-- full below.

-- (Both endpoints explicit: _≈ᶜ_ is a defined relation.)
plain : (u v : Circuit n) → u ≈ᶜ v → u ≈ᶜ (ε • v)
plain u v e = ≈ᶜ-trans {w = u} {v = v} {u = ε • v} e
                (≈ᶜ-sym {w = ε • v} {v = v} (identityˡᶜ v))

-- order-S: S² is not the identity in the Clifford group — it is the
-- Pauli Z on wire 0, which is exactly what corr records.  Reading both
-- sides at (s , (a , b) ∷ ps):
--
--   S²           : phase  s + incl a + incl a,  head (a , (b + a) + a)
--   conj. by Z₀  : phase  s + ι (sform Z₀ _),   head (a , b)
--
-- and incl a + incl a = ι a (CliffordGroup.incl-2) while
-- sform (pZ ∷ pIₙ) ((a , b) ∷ ps) = a.  No word is ever unfolded beyond
-- the two letters of S².

private
  -- b + a + a = b, and sform against Z₀ reads off the X-exponent.
  sq : (a b : ℤ ₚ) → (b + a) + a ≡ b
  sq ₀ ₀ = auto
  sq ₀ ₁ = auto
  sq ₁ ₀ = auto
  sq ₁ ₁ = auto

  sform-Z₀ : (a b : ℤ ₚ) (ps : Pauli n) →
             sform ((₀ , ₁) ∷ pIₙ) ((a , b) ∷ ps) ≡ a
  sform-Z₀ ₀ ₀ ps = Eq.trans (Eq.cong (₀ +_) (sform-pIˡ ps)) auto
  sform-Z₀ ₀ ₁ ps = Eq.trans (Eq.cong (₀ +_) (sform-pIˡ ps)) auto
  sform-Z₀ ₁ ₀ ps = Eq.trans (Eq.cong (₁ +_) (sform-pIˡ ps)) auto
  sform-Z₀ ₁ ₁ ps = Eq.trans (Eq.cong (₁ +_) (sform-pIˡ ps)) auto

order-S-sound : (S {n} ^ 2) ≈ᶜ (pauliWord ((₀ , ₁) ∷ pIₙ) • ε)
order-S-sound (s , (a , b) ∷ ps) = begin
  ((s + incl a) + incl a) , (a , (b + a) + a) ∷ ps
    ≡⟨ Eq.cong₂ (λ x y → x , (a , y) ∷ ps)
                (Eq.trans (+-assoc s (incl a) (incl a))
                          (Eq.cong (s +_) (incl-2 a)))
                (sq a b) ⟩
  (s + ι a) , (a , b) ∷ ps
    ≡⟨ Eq.cong (λ □ → (s + ι □) , (a , b) ∷ ps) (Eq.sym (sform-Z₀ a b ps)) ⟩
  (s + ι (sform ((₀ , ₁) ∷ pIₙ) ((a , b) ∷ ps))) , (a , b) ∷ ps
    ≡⟨ Eq.sym (cact-pauliWord ((₀ , ₁) ∷ pIₙ) s ((a , b) ∷ ps)) ⟩
  cact (pauliWord ((₀ , ₁) ∷ pIₙ)) (s , (a , b) ∷ ps)   ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The scalar axioms
--
-- Five of the fourteen ε-correction axioms are about M₋₁, which at p = 2
-- is the scalar (S·H)³ = ω — the ℤ*₂-is-trivial collapse.  ω acts as the
-- identity on P4 (Action.cact-ω), on any wire (Soundness.cω↑-sound), so
-- these need no case analysis at all: both sides act as whatever is left
-- when ω is deleted.

private
  cactω : (x : P4Carrier (₁₊ n)) → cact (M₋₁ {n}) x ≡ x
  cactω = cact-ω

  cactω↑ : (x : P4Carrier (₂₊ n)) → cact ((M₋₁ {n}) ↑) x ≡ x
  cactω↑ x = Eq.trans (cω↑-sound x) (cact-ω x)

-- M-power at k = ₀ reads ε === M₋₁ (ℤ*₂ being trivial).
M-power-sound : (ε {X = Gen (₁₊ n)}) ≈ᶜ (ε • M₋₁)
M-power-sound = plain ε M₋₁ (λ x → Eq.sym (cactω x))

-- order-H: H² = M₋₁.  H² acts trivially, and so does the scalar.
order-H-sound : (H {n} ^ 2) ≈ᶜ (ε • M₋₁)
order-H-sound {n} = plain (H ^ 2) M₋₁ h²
  where
  h² : (x : P4Carrier (₁₊ n)) → cact (H ^ 2) x ≡ cact M₋₁ x
  h² (s , P@((₀ , ₀) ∷ ps)) =
    Eq.trans (lift-eq (H ^ 2) ε s P Eq.refl) (Eq.sym (cactω (s , P)))
  h² (s , P@((₀ , ₁) ∷ ps)) =
    Eq.trans (lift-eq (H ^ 2) ε s P Eq.refl) (Eq.sym (cactω (s , P)))
  h² (s , P@((₁ , ₀) ∷ ps)) =
    Eq.trans (lift-eq (H ^ 2) ε s P Eq.refl) (Eq.sym (cactω (s , P)))
  h² (s , P@((₁ , ₁) ∷ ps)) =
    Eq.trans (lift-eq (H ^ 2) ε s P Eq.refl) (Eq.sym (cactω (s , P)))

-- semi-MS: the scalar commutes with S (at p = 2 the exponent g·g is 1).
semi-MS-sound : ((M₋₁ {n}) • S) ≈ᶜ (ε • (S • M₋₁))
semi-MS-sound {n} = plain (M₋₁ • S) (S • M₋₁)
  (λ x → Eq.trans (cactω (cact S x)) (Eq.sym (Eq.cong (cact S) (cactω x))))

-- semi-M↑CZ / semi-M↓CZ: the same, one wire up and on the bottom wire
-- (at p = 2 the exponent g is 1, so CZ^g is CZ).
semi-M↑CZ-sound : (((M₋₁ {n}) ↑) • CZ) ≈ᶜ (ε • (CZ • ((M₋₁ {n}) ↑)))
semi-M↑CZ-sound {n} = plain ((M₋₁ ↑) • CZ) (CZ • (M₋₁ ↑))
  (λ x → Eq.trans (cactω↑ (cact CZ x))
                  (Eq.sym (Eq.cong (cact CZ) (cactω↑ x))))

semi-M↓CZ-sound : ((M₋₁ {₁₊ n}) • CZ) ≈ᶜ (ε • (CZ • (M₋₁ {₁₊ n})))
semi-M↓CZ-sound {n} = plain (M₋₁ • CZ) (CZ • M₋₁)
  (λ x → Eq.trans (cactω (cact CZ x))
                  (Eq.sym (Eq.cong (cact CZ) (cactω x))))

------------------------------------------------------------------------
-- The two-wire axioms
--
-- order-CZ and the two CZ/S commutations touch wires 0 and 1, so the
-- action is decided by the two head Paulis: sixteen concrete cases,
-- each closed by lift-eq (which reduces the check to phase 0) with the
-- tail ps symbolic throughout.  The words are named so that conversion
-- checking compares them, not their unfoldings.

private
  CZ² : Word (Gen (₂₊ n))
  CZ² = CZ ^ 2

  CZS↓ S↓CZ CZS↑ S↑CZ : Word (Gen (₂₊ n))
  CZS↓ = CZ • S ↓
  S↓CZ = S ↓ • CZ
  CZS↑ = CZ • S ↑
  S↑CZ = S ↑ • CZ

order-CZ-sound : (CZ {n} ^ 2) ≈ᶜ (ε • ε)
order-CZ-sound {n} = plain (CZ ^ 2) ε go
  where
  go : (x : P4Carrier (₂₊ n)) → cact CZ² x ≡ cact ε x
  go (s , P@((₀ , ₀) ∷ (₀ , ₀) ∷ ps)) = lift-eq CZ² ε s P Eq.refl
  go (s , P@((₀ , ₀) ∷ (₀ , ₁) ∷ ps)) = lift-eq CZ² ε s P Eq.refl
  go (s , P@((₀ , ₀) ∷ (₁ , ₀) ∷ ps)) = lift-eq CZ² ε s P Eq.refl
  go (s , P@((₀ , ₀) ∷ (₁ , ₁) ∷ ps)) = lift-eq CZ² ε s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₀ , ₀) ∷ ps)) = lift-eq CZ² ε s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₀ , ₁) ∷ ps)) = lift-eq CZ² ε s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₁ , ₀) ∷ ps)) = lift-eq CZ² ε s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₁ , ₁) ∷ ps)) = lift-eq CZ² ε s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₀ , ₀) ∷ ps)) = lift-eq CZ² ε s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₀ , ₁) ∷ ps)) = lift-eq CZ² ε s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₁ , ₀) ∷ ps)) = lift-eq CZ² ε s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₁ , ₁) ∷ ps)) = lift-eq CZ² ε s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₀ , ₀) ∷ ps)) = lift-eq CZ² ε s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₀ , ₁) ∷ ps)) = lift-eq CZ² ε s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₁ , ₀) ∷ ps)) = lift-eq CZ² ε s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₁ , ₁) ∷ ps)) = lift-eq CZ² ε s P Eq.refl

comm-CZ-S↓-sound : ((CZ {n}) • S ↓) ≈ᶜ (ε • (S ↓ • CZ))
comm-CZ-S↓-sound {n} = plain (CZ • S ↓) (S ↓ • CZ) go
  where
  go : (x : P4Carrier (₂₊ n)) → cact CZS↓ x ≡ cact S↓CZ x
  go (s , P@((₀ , ₀) ∷ (₀ , ₀) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl
  go (s , P@((₀ , ₀) ∷ (₀ , ₁) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl
  go (s , P@((₀ , ₀) ∷ (₁ , ₀) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl
  go (s , P@((₀ , ₀) ∷ (₁ , ₁) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₀ , ₀) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₀ , ₁) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₁ , ₀) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₁ , ₁) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₀ , ₀) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₀ , ₁) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₁ , ₀) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₁ , ₁) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₀ , ₀) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₀ , ₁) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₁ , ₀) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₁ , ₁) ∷ ps)) = lift-eq CZS↓ S↓CZ s P Eq.refl

comm-CZ-S↑-sound : ((CZ {n}) • S ↑) ≈ᶜ (ε • (S ↑ • CZ))
comm-CZ-S↑-sound {n} = plain (CZ • S ↑) (S ↑ • CZ) go
  where
  go : (x : P4Carrier (₂₊ n)) → cact CZS↑ x ≡ cact S↑CZ x
  go (s , P@((₀ , ₀) ∷ (₀ , ₀) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl
  go (s , P@((₀ , ₀) ∷ (₀ , ₁) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl
  go (s , P@((₀ , ₀) ∷ (₁ , ₀) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl
  go (s , P@((₀ , ₀) ∷ (₁ , ₁) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₀ , ₀) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₀ , ₁) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₁ , ₀) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₁ , ₁) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₀ , ₀) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₀ , ₁) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₁ , ₀) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₁ , ₁) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₀ , ₀) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₀ , ₁) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₁ , ₀) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₁ , ₁) ∷ ps)) = lift-eq CZS↑ S↑CZ s P Eq.refl

------------------------------------------------------------------------
-- The three-wire axioms: do NOT restate them here
--
-- selinger-c12 … c15 are letter-for-letter the Figure-8 relations of the
-- same names, and their P4-soundness is already proved — c12 and c13 in
-- Selinger.Action, c14 and c15 in Selinger.Soundness, each a 64-case
-- head split.  The obvious move is to wrap them with `plain`, and it is
-- a trap: doing so puts TWO differently-named copies of the same long
-- word in one goal (this module's and the private one over there), and
-- the conversion checker resolves that by unfolding cact along the word
-- with a symbolic Pauli.  Measured: 25 GB resident and still climbing
-- after 11 minutes, i.e. the blow-up documented in Selinger.Soundness's
-- header.
--
-- So these four are to be plugged in AT THE ASSEMBLY SITE, where the
-- axiom itself supplies the words and only one copy is ever in play:
--
--     axiom-sound selinger-c12 = plain _ _ c12-sound
--
-- with the underscores solved from the axiom's own indices.  The same
-- caution applies to c10 / c11, whose two sides differ between the two
-- rule sets and so need their own sixteen-case computation — write it
-- against named words, exactly as Soundness.agda does.

------------------------------------------------------------------------
-- selinger-c10
--
-- Unlike c12…c15 this one is NOT shared with Figure 8: the simplified
-- rule set writes the right-hand side with S⁻¹'s (which are S at p = 2)
-- and no ω, where Figure 8 writes SH's and a trailing ω⁻¹.  So it needs
-- its own computation — sixteen head cases, tail symbolic, lift-eq for
-- the phase, against words named locally so that conversion never
-- unfolds cact along them.

private
  L10ˢ R10ˢ : Word (Gen (₂₊ n))
  L10ˢ = CZ • H ↑ • CZ
  R10ˢ = S⁻¹ ↑ • H ↑ • S⁻¹ ↑ • CZ • H ↑ • S⁻¹ ↑ • S⁻¹ ↓

selinger-c10-sound : (L10ˢ {n}) ≈ᶜ (ε • R10ˢ)
selinger-c10-sound {n} = plain L10ˢ R10ˢ go
  where
  go : (x : P4Carrier (₂₊ n)) → cact L10ˢ x ≡ cact R10ˢ x
  go (s , P@((₀ , ₀) ∷ (₀ , ₀) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl
  go (s , P@((₀ , ₀) ∷ (₀ , ₁) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl
  go (s , P@((₀ , ₀) ∷ (₁ , ₀) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl
  go (s , P@((₀ , ₀) ∷ (₁ , ₁) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₀ , ₀) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₀ , ₁) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₁ , ₀) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₁ , ₁) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₀ , ₀) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₀ , ₁) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₁ , ₀) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₁ , ₁) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₀ , ₀) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₀ , ₁) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₁ , ₀) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₁ , ₁) ∷ ps)) = lift-eq L10ˢ R10ˢ s P Eq.refl

------------------------------------------------------------------------
-- selinger-c11, the mirror image

private
  L11ˢ R11ˢ : Word (Gen (₂₊ n))
  L11ˢ = CZ • H ↓ • CZ
  R11ˢ = S⁻¹ ↓ • H ↓ • S⁻¹ ↓ • CZ • H ↓ • S⁻¹ ↓ • S⁻¹ ↑

selinger-c11-sound : (L11ˢ {n}) ≈ᶜ (ε • R11ˢ)
selinger-c11-sound {n} = plain L11ˢ R11ˢ go
  where
  go : (x : P4Carrier (₂₊ n)) → cact L11ˢ x ≡ cact R11ˢ x
  go (s , P@((₀ , ₀) ∷ (₀ , ₀) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl
  go (s , P@((₀ , ₀) ∷ (₀ , ₁) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl
  go (s , P@((₀ , ₀) ∷ (₁ , ₀) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl
  go (s , P@((₀ , ₀) ∷ (₁ , ₁) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₀ , ₀) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₀ , ₁) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₁ , ₀) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl
  go (s , P@((₀ , ₁) ∷ (₁ , ₁) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₀ , ₀) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₀ , ₁) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₁ , ₀) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl
  go (s , P@((₁ , ₀) ∷ (₁ , ₁) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₀ , ₀) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₀ , ₁) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₁ , ₀) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl
  go (s , P@((₁ , ₁) ∷ (₁ , ₁) ∷ ps)) = lift-eq L11ˢ R11ˢ s P Eq.refl

-- The per-axiom obligation that remains: each raw axiom of the
-- simplified rule set acts as its correction demands.  (For every axiom
-- but order-S the correction is ε, so this says the two sides act
-- alike; for order-S it says S² is conjugation by Z on wire 0.)
AxiomSound : Set
AxiomSound = ∀ {n} {u v : Circuit n} (r : n SRel, u === v) →
             u ≈ᶜ (pw (corr (srel r)) • v)

-- THE ASSEMBLY, and what it costs.  Written out it is
--
--   axiom-sound : AxiomSound
--   axiom-sound (order-S {₀})    = order-S-sound    -- the width split is
--   axiom-sound (order-S {₁₊ m}) = order-S-sound    -- needed: Z₀, the
--   axiom-sound order-H          = order-H-sound    -- one non-trivial
--   axiom-sound (M-power ₀)      = M-power-sound    -- correction, is
--   axiom-sound semi-MS          = semi-MS-sound    -- defined by cases
--   axiom-sound semi-M↑CZ        = semi-M↑CZ-sound  -- on the width
--   axiom-sound semi-M↓CZ        = semi-M↓CZ-sound
--   axiom-sound order-CZ         = order-CZ-sound
--   axiom-sound comm-CZ-S↓       = comm-CZ-S↓-sound
--   axiom-sound comm-CZ-S↑       = comm-CZ-S↑-sound
--   axiom-sound selinger-c10     = selinger-c10-sound
--   axiom-sound selinger-c11     = selinger-c11-sound
--   axiom-sound selinger-c12     = plain (CZ ↑ • CZ) (CZ • CZ ↑) c12-sound
--   axiom-sound selinger-c13     =
--     plain (⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑) (⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓) c13-sound
--   axiom-sound selinger-c14     = plain ((⊤⊥ ↑ • CZ ↓) ^ 3) ε c14-sound
--   axiom-sound selinger-c15     = plain ((⊥⊤ ↓ • CZ ↑) ^ 3) ε c15-sound
--
-- Measured 2026-08-08 under an 8 GB cap:
--
--   * everything through selinger-c13 checks, in 24 s.  c12 and c13 need
--     their words written OUT — `plain _ _ c12-sound` leaves metas, since
--     _≈ᶜ_ is a defined relation and cannot determine them — but writing
--     the same expression the axiom uses costs nothing;
--   * selinger-c14 / c15 exhaust 8 GB in ~34 s whatever the body.  Their
--     words are cubes of the derived ⊤⊥ / ⊥⊤, and the blow-up is in the
--     CLAUSE'S GOAL rather than the proof — the same phenomenon
--     Soundness.agda's header records for its own axiom-sound;
--   * M-power needs a second clause: Agda asks for M-power (₁₊ k), so its
--     exponent type is not the one-element ℤ/1 that ℤ*₂ triviality would
--     suggest.  That case has to be inhabited-and-proved or shown absurd.
--
-- The fix was the module's --call-by-name flag: call-by-need
-- normalisation is what duplicates the Pauli once per letter, and under
-- call-by-name the same clauses go through.  M-power's second clause is
-- discharged by the absurd pattern — its exponent lives in ℤ/1.

axiom-sound : AxiomSound
axiom-sound (order-S {₀})    = order-S-sound
axiom-sound (order-S {₁₊ m}) = order-S-sound
axiom-sound order-H          = order-H-sound
axiom-sound (M-power ₀)      = M-power-sound
axiom-sound (M-power ₁)      = plain M₋₁ M₋₁ (λ _ → Eq.refl)
axiom-sound (M-power (₂₊ ()))
axiom-sound semi-MS          = semi-MS-sound
axiom-sound semi-M↑CZ        = semi-M↑CZ-sound
axiom-sound semi-M↓CZ        = semi-M↓CZ-sound
axiom-sound order-CZ         = order-CZ-sound
axiom-sound comm-CZ-S↓       = comm-CZ-S↓-sound
axiom-sound comm-CZ-S↑       = comm-CZ-S↑-sound
axiom-sound selinger-c10     = selinger-c10-sound
axiom-sound selinger-c11     = selinger-c11-sound
axiom-sound selinger-c12     = plain (CZ ↑ • CZ) (CZ • CZ ↑) c12-sound
axiom-sound selinger-c13     =
  plain (⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑) (⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓) c13-sound
axiom-sound selinger-c14     = plain ((⊤⊥ ↑ • CZ ↓) ^ 3) ε c14-sound
axiom-sound selinger-c15     = plain ((⊥⊤ ↓ • CZ ↑) ^ 3) ε c15-sound

-- Given that, the whole twisted family follows.
twist-sound : AxiomSound →
              ∀ {n} {u v : Circuit n} (r̄ : (n QRel,_===_) u v) →
              u ≈ᶜ (pw (corr r̄) • v)
twist-sound as (srel r)    = as r
twist-sound as (comm₁ h g) =
  ≈ᶜ-trans {w = [ g ↥ ]ʷ • [ gate₁ h ]ʷ}
           {v = [ gate₁ h ]ʷ • [ g ↥ ]ʷ}
           {u = ε • ([ gate₁ h ]ʷ • [ g ↥ ]ʷ)}
    (comm₁-sound h g)
    (≈ᶜ-sym {w = ε • ([ gate₁ h ]ʷ • [ g ↥ ]ʷ)}
            {v = [ gate₁ h ]ʷ • [ g ↥ ]ʷ}
            (identityˡᶜ ([ gate₁ h ]ʷ • [ g ↥ ]ʷ)))
twist-sound as (comm₂ h g) =
  ≈ᶜ-trans {w = [ g ↥ ↥ ]ʷ • [ gate₂ h ]ʷ}
           {v = [ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ}
           {u = ε • ([ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ)}
    (comm₂-sound h g)
    (≈ᶜ-sym {w = ε • ([ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ)}
            {v = [ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ}
            (identityˡᶜ ([ gate₂ h ]ʷ • [ g ↥ ↥ ]ʷ)))
twist-sound as (cong↑ {w = u'} {v = v'} r) =
  ≈ᶜ-trans {w = u' ↑} {v = (pw (corr r) • v') ↑}
           {u = pw (shiftPauli (corr r)) • (v' ↑)}
    (sound-↑ {w = u'} {v = pw (corr r) • v'} (twist-sound as r))
    (∙-congᶜ {w = (pw (corr r)) ↑} {pw (shiftPauli (corr r))}
             {v' ↑} {v' ↑}
             (≈ᶜ-sym {w = pw (shiftPauli (corr r))} {v = (pw (corr r)) ↑}
                     (pw-shift (corr r)))
             (≈ᶜ-refl {w = v' ↑}))

------------------------------------------------------------------------
-- sound-ax's twisted half, with no hypothesis left

twisted-sound : {n : ℕ} {u v : Circuit n} (r̄ : (n QRel,_===_) u v) →
                u ≈ᶜ (pw (corr r̄) • v)
twisted-sound = twist-sound axiom-sound

------------------------------------------------------------------------
-- Presentations of groups
--
-- Shifting a circuit shifts its denotation.
--
-- Clifford.Qupit.SemRealises reduces Realises to nineteen equations in
-- ℤ/pℤ about the phase Φ.  Three of them are the STRUCTURAL rules —
-- cong↑, comm₁, comm₂ — and all three are about a circuit that has been
-- moved up a wire.  What they need, and what nothing in the library had,
-- is the effect of that move on the Paper-V0 denotation:
--
--     ⟦ w ↑ ⟧  =  (pI ∷ P⟦ w ⟧ , lift₀ˢ S⟦ w ⟧).
--
-- The Pauli gains a trivial bottom wire and the symplectic part becomes
-- the one that fixes wire 0 — which is `lift₀ˢ`, already in
-- Symplectic.Semantics with its whole homomorphism API.
--
-- Where the work is.  Paper-V0's denotation is V1's, which is the
-- SEMIDIRECT one composed with Simplified-V1.Forward's translation h.
-- So the lemma is proved one level down, over words in the semidirect
-- alphabet, and lifted through h by `hʷ-↑` — h commutes with shifting
-- because it is defined to (h (a ↥) = (h a) ↑).
--
-- Two things make the induction go through where a gate-by-gate one
-- would not.  First, it is over the SEMIDIRECT word, not the gate: the
-- translation of S is Z^(-½) · S, whose Pauli factor is a power with a
-- symbolic exponent, so no case analysis on gates can reach it — but a
-- structural induction proved for ALL words applies to a stuck power
-- without needing to reduce it.  Second, the semidirect product built by
-- the presentation machinery multiplies with the TRANSPORTED action, so
-- every product step goes through SemiDirect.Presentation.∙-agrees to
-- get back to `ap`.
--
-- The generator cases are all definitional: `actg (g ↥) (x ∷ ps) =
-- x ∷ actg g ps` is a defining clause of the symplectic action, and
-- XZ's `⟦ g ↥ ⟧₀ = pI ∷ ⟦ g ⟧₀` of the Pauli one.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc ; zero)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford.Qupit.SemShift
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Bundles using (Group)
open import Data.Product using (_×_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Vec using (_∷_)
import Relation.Binary.PropositionalEquality as Eq

open import Word.Base using (Word ; ε ; _•_ ; _^_ ; [_]ʷ ; _ʷ)
open import Presentation.Definitions using (_IsPresentationOf_)
open import Algebra.Properties.Ring (+-*-ring p-2) using (-0#≈0# ; -‿+-comm)
open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime
  using (mult ; mult-toℕ)



open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using ( Pauli ; Pauli1 ; pI ; pZ ; pZ₀ ; pIₙ ; sform
        ; _+₁_ ; _+ₚ_ ; +₁-identityˡ ; +ₚ-identityˡ ; +ₚ-identityʳ )
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (Symplectic ; _≈ˢ_ ; εˢ ; _∘ˢ_ ; lift₀ˢ ; lift₀ˢ-ε ; lift₀ˢ-∘)
open Symplectic using (ap)
import Examples.Groups.Clifford.Qupit.Semantics p-3 p-prime as Sem


open import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Syntactics
  p-3 p-prime g* g-gen using (module SemiDirect)
import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Presentation
  p-3 p-prime g* g-gen as SDPres
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Forward
  p-3 p-prime g* g-gen as Fwd
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen as Pap
import Examples.Groups.Clifford.Qupit.Syntactics
  p-3 p-prime g* g-gen as QS
import Examples.Groups.Clifford.Qupit.SemFE p-3 p-prime g* g-gen as FE

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The semidirect denotation
--
-- The presentation's own interpretation, named so it can be inducted
-- over.  Its two components are the Pauli and the symplectic part.

⟦_⟧ˢᵈ : Word (SemiDirect.Gen n) → Pauli n × Symplectic n
⟦_⟧ˢᵈ {n} = _IsPresentationOf_.⟦_⟧ (SDPres.presentation {n})

private
  -- Multiplication in the semidirect product uses the TRANSPORTED
  -- action; ∙-agrees is what turns it back into `ap`.
  ∙ᵃᵖ : (u v : Word (SemiDirect.Gen n)) →
        ⟦ u • v ⟧ˢᵈ ≡ ( proj₁ ⟦ u ⟧ˢᵈ +ₚ ap (proj₂ ⟦ u ⟧ˢᵈ) (proj₁ ⟦ v ⟧ˢᵈ)
                      , proj₂ ⟦ u ⟧ˢᵈ ∘ˢ proj₂ ⟦ v ⟧ˢᵈ )
  ∙ᵃᵖ {n} u v = SDPres.Semidirect.∙-agrees n ⟦ u ⟧ˢᵈ ⟦ v ⟧ˢᵈ

  -- Composition respects ≈ˢ.  Written out: the endpoints of a ≈ˢ are
  -- never recovered by unification.
  ∘ˢ-cong : (S S' T T' : Symplectic n) → S ≈ˢ S' → T ≈ˢ T' →
            (S ∘ˢ T) ≈ˢ (S' ∘ˢ T')
  ∘ˢ-cong S S' T T' eS eT q = Eq.trans (Eq.cong (ap S) (eT q)) (eS (ap T' q))

------------------------------------------------------------------------
-- The shift lemma, one level down
--
-- Structural induction over the semidirect word.  A generator lands in
-- one factor or the other, and both cases are definitional; the product
-- case is the two components' laws, with lift₀ˢ threaded through.

⟦⟧ˢᵈ-↑ : (w : Word (SemiDirect.Gen n)) →
         (proj₁ ⟦ w SemiDirect.↑ ⟧ˢᵈ ≡ pI ∷ proj₁ ⟦ w ⟧ˢᵈ)
       × (proj₂ ⟦ w SemiDirect.↑ ⟧ˢᵈ ≈ˢ lift₀ˢ (proj₂ ⟦ w ⟧ˢᵈ))
-- A Pauli generator: XZ's ⟦ x ↥ ⟧₀ = pI ∷ ⟦ x ⟧₀, and the symplectic
-- part is the identity on both sides.
⟦⟧ˢᵈ-↑ [ inj₁ x ]ʷ = Eq.refl , λ { (y ∷ ps) → Eq.refl }
-- A symplectic generator: no Pauli either side, and actg's own shift
-- clause is exactly lift₀ˢ.
⟦⟧ˢᵈ-↑ [ inj₂ y ]ʷ = Eq.refl , λ { (y ∷ ps) → Eq.refl }
⟦⟧ˢᵈ-↑ ε          = Eq.refl , λ { (y ∷ ps) → Eq.refl }
⟦⟧ˢᵈ-↑ {n} (u • v) = pw , sw
  where
  Pu = proj₁ ⟦ u ⟧ˢᵈ
  Su = proj₂ ⟦ u ⟧ˢᵈ
  Pv = proj₁ ⟦ v ⟧ˢᵈ
  Sv = proj₂ ⟦ v ⟧ˢᵈ

  ihu : (proj₁ ⟦ u SemiDirect.↑ ⟧ˢᵈ ≡ pI ∷ Pu)
      × (proj₂ ⟦ u SemiDirect.↑ ⟧ˢᵈ ≈ˢ lift₀ˢ Su)
  ihu = ⟦⟧ˢᵈ-↑ u
  ihv : (proj₁ ⟦ v SemiDirect.↑ ⟧ˢᵈ ≡ pI ∷ Pv)
      × (proj₂ ⟦ v SemiDirect.↑ ⟧ˢᵈ ≈ˢ lift₀ˢ Sv)
  ihv = ⟦⟧ˢᵈ-↑ v

  -- The transported Pauli of the right factor, shifted.
  apv : ap (proj₂ ⟦ u SemiDirect.↑ ⟧ˢᵈ) (proj₁ ⟦ v SemiDirect.↑ ⟧ˢᵈ)
          ≡ pI ∷ ap Su Pv
  apv = Eq.trans (Eq.cong (ap (proj₂ ⟦ u SemiDirect.↑ ⟧ˢᵈ)) (proj₁ ihv))
                 (proj₂ ihu (pI ∷ Pv))

  pw : proj₁ ⟦ (u • v) SemiDirect.↑ ⟧ˢᵈ ≡ pI ∷ proj₁ ⟦ u • v ⟧ˢᵈ
  pw = Eq.trans (Eq.cong proj₁ (∙ᵃᵖ (u SemiDirect.↑) (v SemiDirect.↑)))
         (Eq.trans (Eq.cong₂ _+ₚ_ (proj₁ ihu) apv)
           (Eq.trans (Eq.cong (_∷ (Pu +ₚ ap Su Pv)) (+₁-identityˡ pI))
                     (Eq.cong (λ z → pI ∷ proj₁ z) (Eq.sym (∙ᵃᵖ u v)))))

  sw : proj₂ ⟦ (u • v) SemiDirect.↑ ⟧ˢᵈ ≈ˢ lift₀ˢ (proj₂ ⟦ u • v ⟧ˢᵈ)
  sw q =
    Eq.trans
      (Eq.cong (λ z → ap (proj₂ z) q) (∙ᵃᵖ (u SemiDirect.↑) (v SemiDirect.↑)))
      (Eq.trans (∘ˢ-cong (proj₂ ⟦ u SemiDirect.↑ ⟧ˢᵈ) (lift₀ˢ Su)
                         (proj₂ ⟦ v SemiDirect.↑ ⟧ˢᵈ) (lift₀ˢ Sv)
                         (proj₂ ihu) (proj₂ ihv) q)
        (Eq.trans (Eq.sym (lift₀ˢ-∘ Su Sv q))
                  (Eq.cong (λ z → ap (lift₀ˢ (proj₂ z)) q) (Eq.sym (∙ᵃᵖ u v)))))

------------------------------------------------------------------------
-- ... and the same lemma upstairs
--
-- Paper-V0's denotation is the semidirect one composed with h, and h
-- commutes with shifting by construction.

private
  -- h commutes with _↑ (Simplified-V1.Iso's lemma-h↑, which lives inside
  -- a width-parameterised module; three lines to restate).
  hʷ-↑ : (w : Word (Pap.Gen n)) →
         (Fwd.Iso.h n ʷ) (w Pap.↑) ≡ ((Fwd.Iso.h n ʷ) w) SemiDirect.↑
  hʷ-↑ [ x ]ʷ  = Eq.refl
  hʷ-↑ ε       = Eq.refl
  hʷ-↑ (u • v) = Eq.cong₂ _•_ (hʷ-↑ u) (hʷ-↑ v)

  -- Forward.Iso's module argument does not occur in h's body, but the
  -- two sides of a shift live at DIFFERENT widths, so the two instances
  -- have to be identified.  On a constructor h reduces regardless of the
  -- argument, so this is one induction on the gate.
  h-irrel : (i j : ℕ) {k : ℕ} (a : Pap.Gen k) →
            Fwd.Iso.h i a ≡ Fwd.Iso.h j a
  h-irrel i j Pap.H-gen  = Eq.refl
  h-irrel i j Pap.S-gen  = Eq.refl
  h-irrel i j Pap.CZ-gen = Eq.refl
  h-irrel i j (a Pap.↥)  = Eq.cong SemiDirect._↑ (h-irrel i j a)

  hʷ-irrel : (i j : ℕ) (w : Word (Pap.Gen n)) →
             (Fwd.Iso.h i ʷ) w ≡ (Fwd.Iso.h j ʷ) w
  hʷ-irrel i j [ a ]ʷ  = h-irrel i j a
  hʷ-irrel i j ε       = Eq.refl
  hʷ-irrel i j (u • v) = Eq.cong₂ _•_ (hʷ-irrel i j u) (hʷ-irrel i j v)

  -- ... and the shift lemma at the two widths the denotation uses.
  hʷ-↑' : (w : Word (Pap.Gen n)) →
          (Fwd.Iso.h (₁₊ n) ʷ) (w Pap.↑) ≡ ((Fwd.Iso.h n ʷ) w) SemiDirect.↑
  hʷ-↑' {n} w = Eq.trans (hʷ-irrel (₁₊ n) n (w Pap.↑)) (hʷ-↑ w)

  -- FE.Weyl takes its width as a MODULE argument, which cannot be
  -- applied prefix to a mixfix name; alias it.
  module Weylₙ (m : ℕ) where
    open FE.Weyl m public using () renaming (⟦_⟧ to den)

  -- The two denotations agree: Paper-V0's IS the semidirect one read
  -- after h.
  ⟦⟧-via-h : (w : Word (Pap.Gen n)) →
             Weylₙ.den n w ≡ ⟦ (Fwd.Iso.h n ʷ) w ⟧ˢᵈ
  ⟦⟧-via-h w = Eq.refl

-- The Pauli and symplectic parts of the rule set's denotation, with the
-- width as an ordinary implicit.
Pᵂ : QS.Circuit n → Pauli n
Pᵂ {n} w = proj₁ (Weylₙ.den n w)

Sᵂ : QS.Circuit n → Symplectic n
Sᵂ {n} w = proj₂ (Weylₙ.den n w)

-- The shift lemma for the rule set's own denotation.
⟦⟧-↑ : (w : QS.Circuit n) →
       (Pᵂ (w Pap.↑) ≡ pI ∷ Pᵂ w) × (Sᵂ (w Pap.↑) ≈ˢ lift₀ˢ (Sᵂ w))
⟦⟧-↑ {n} w = Eq.subst Motive (Eq.sym (hʷ-↑' w)) (⟦⟧ˢᵈ-↑ hw)
  where
  hw : Word (SemiDirect.Gen n)
  hw = (Fwd.Iso.h n ʷ) w

  -- The motive lives one wire up, so both widths are pinned by hand.
  Motive : Word (SemiDirect.Gen (₁₊ n)) → Set
  Motive z = (proj₁ (⟦_⟧ˢᵈ {₁₊ n} z) ≡ pI ∷ proj₁ (⟦_⟧ˢᵈ {n} hw))
           × (proj₂ (⟦_⟧ˢᵈ {₁₊ n} z) ≈ˢ lift₀ˢ (proj₂ (⟦_⟧ˢᵈ {n} hw)))



------------------------------------------------------------------------
-- Bottom-locality: the Pauli powers
--
-- The dual of the shift lemma, and what comm₁ / comm₂ need.  The
-- awkward case is S, whose translation is Z^(-½) · S: the Pauli factor
-- is a power with a symbolic exponent.  This is an induction on that
-- exponent, to be applied at the stuck `toℕ (-½)` — the same move as
-- zeroP-^ applied at p.

-- A Pauli supported on the bottom wire.
Bot₁ : Pauli (₁₊ n) → Set
Bot₁ {n} P = ∃ λ q → P ≡ q ∷ pIₙ

Bot₂ : Pauli (₂₊ n) → Set
Bot₂ {n} P = ∃ λ q → ∃ λ q' → P ≡ q ∷ q' ∷ pIₙ

-- Z ^ j sits on wire 0 and acts trivially.  The recursive call is the
-- `with` scrutinee: inside a where-block the termination checker cannot
-- see the decrease through the lifting.
Z^-bot : (j : ℕ) →
         Bot₁ (proj₁ (⟦_⟧ˢᵈ {₁₊ n} (SemiDirect.Z ^ j)))
       × (proj₂ (⟦_⟧ˢᵈ {₁₊ n} (SemiDirect.Z ^ j)) ≈ˢ εˢ)
Z^-bot zero      = (pI , Eq.refl) , λ q → Eq.refl
Z^-bot (₁₊ zero) = (pZ , Eq.refl) , λ q → Eq.refl
-- NO `with`, and no `where`: with-abstraction generalises the goal over
-- the scrutinee's type, which mentions the denotation, and that
-- comparison forces the whole chain (measured: OOM at 12 GB).  A
-- where-block instead defeats the termination checker.  Inlining the
-- recursive calls avoids both.
Z^-bot {n} (₂₊ j) =
      ( (pZ +₁ proj₁ (proj₁ (Z^-bot {n} (₁₊ j))))
      , Eq.trans (Eq.cong proj₁ (∙ᵃᵖ (SemiDirect.Z {n}) (SemiDirect.Z ^ ₁₊ j)))
          (Eq.trans (Eq.cong (pZ₀ +ₚ_) (proj₂ (proj₁ (Z^-bot {n} (₁₊ j)))))
                    (Eq.cong ((pZ +₁ proj₁ (proj₁ (Z^-bot {n} (₁₊ j)))) ∷_)
                             (+ₚ-identityˡ pIₙ))) )
    , λ q → Eq.trans
              (Eq.cong (λ z → ap (proj₂ z) q)
                       (∙ᵃᵖ (SemiDirect.Z {n}) (SemiDirect.Z ^ ₁₊ j)))
              (proj₂ (Z^-bot {n} (₁₊ j)) q)

-- A two-wire gate at the bottom: CZ is pure symplectic, so its Pauli is
-- trivial outright and its action leaves every wire above the bottom
-- two alone.  Both facts are the arithmetic of ₀ + ₀.
gate₂-bot : (h : Pap.SympGate 2) →
            Bot₂ (Pᵂ {₂₊ n} [ Pap.gate₂ h ]ʷ)
          × ((R : Pauli n) →
             ap (Sᵂ {₂₊ n} [ Pap.gate₂ h ]ʷ) (pI ∷ pI ∷ R) ≡ pI ∷ pI ∷ R)
gate₂-bot Pap.CZ-gate =
  (pI , pI , Eq.refl) ,
  λ R → Eq.cong₂ (λ y z → (₀ , y) ∷ (₀ , z) ∷ R)
                 (+-identityʳ ₀) (+-identityʳ ₀)

-- The one-wire gates, one at a time (they are split so that each can be
-- measured on its own; H is pure symplectic, S is not).
gate₁H-bot : Bot₁ (Pᵂ {₁₊ n} [ Pap.gate₁ Pap.H-gate ]ʷ)
           × ((R : Pauli n) →
              ap (Sᵂ {₁₊ n} [ Pap.gate₁ Pap.H-gate ]ʷ) (pI ∷ R) ≡ pI ∷ R)
gate₁H-bot = (pI , Eq.refl) , λ R → Eq.cong (λ z → (z , ₀) ∷ R) -0#≈0#

-- Appending the symplectic S to a bottom-supported, symplectically
-- trivial word keeps it bottom-supported and fixing everything above.
-- Quantified over the WORD together with its two properties, never over
-- an exponent: the translation of S is Z^(-½) · S, and that numeral is
-- a modular inverse — solving for it would force Bézout/Fermat.  As a
-- word variable it is only ever matched, never computed.
ZS-bot : (w : Word (SemiDirect.Gen (₁₊ n))) →
         Bot₁ (proj₁ (⟦_⟧ˢᵈ {₁₊ n} w)) →
         (proj₂ (⟦_⟧ˢᵈ {₁₊ n} w) ≈ˢ εˢ) →
         Bot₁ (proj₁ (⟦_⟧ˢᵈ {₁₊ n} (w • SemiDirect.S)))
       × ((R : Pauli n) →
          ap (proj₂ (⟦_⟧ˢᵈ {₁₊ n} (w • SemiDirect.S))) (pI ∷ R) ≡ pI ∷ R)
ZS-bot {n} w (q , eq) sy =
      ( q
      , Eq.trans (Eq.cong proj₁ (∙ᵃᵖ w SemiDirect.S))
          (Eq.trans (Eq.cong (proj₁ (⟦_⟧ˢᵈ {₁₊ n} w) +ₚ_) (sy pIₙ))
                    (Eq.trans (+ₚ-identityʳ (proj₁ (⟦_⟧ˢᵈ {₁₊ n} w))) eq)) )
    , λ R → Eq.trans
              (Eq.cong (λ z → ap (proj₂ z) (pI ∷ R)) (∙ᵃᵖ w SemiDirect.S))
              (Eq.trans (sy ((₀ , ₀ + ₀) ∷ R))
                        (Eq.cong (λ z → (₀ , z) ∷ R) (+-identityʳ ₀)))

-- The translation of S, as a Z-power times the symplectic S.  The
-- exponent is obtained by MATCHING AT THE LEVEL OF WORDS, where both
-- sides are already _•_ and _^_ applications and nothing has to be
-- evaluated.  This is the whole trick: reaching the same equation
-- through `⟦_⟧ˢᵈ` instead would go through StarInterp's Extend, which
-- pattern-matches on the word and so must decide whether Z ^ toℕ (-½)
-- is a letter, an ε or a product — forcing a modular inverse.
hS : (m k : ℕ) → ∃ λ (j : ℕ) →
     Fwd.Iso.h m (Pap.gate₁ Pap.S-gate)
       ≡ (SemiDirect.Z {k} ^ j) • SemiDirect.S {k}
hS m k = _ , Eq.refl

-- ... and the S gate, by transporting ZS-bot along that word equation.
-- `jS` is NAMED rather than left to unification: as a projection out of
-- an existential it is neutral, so the modular inverse inside it is
-- carried and never evaluated (the parameter dodge, at the level of a
-- numeral).
gate₁S-bot : Bot₁ (Pᵂ {₁₊ n} [ Pap.gate₁ Pap.S-gate ]ʷ)
           × ((R : Pauli n) →
              ap (Sᵂ {₁₊ n} [ Pap.gate₁ Pap.S-gate ]ʷ) (pI ∷ R) ≡ pI ∷ R)
gate₁S-bot {n} =
  Eq.subst Motive (Eq.sym eqS)
           (ZS-bot wS (proj₁ (Z^-bot jS)) (proj₂ (Z^-bot jS)))
  where
  jS : ℕ
  jS = proj₁ (hS (₁₊ n) n)

  wS : Word (SemiDirect.Gen (₁₊ n))
  wS = SemiDirect.Z ^ jS

  eqS : Fwd.Iso.h (₁₊ n) (Pap.gate₁ Pap.S-gate) ≡ wS • SemiDirect.S
  eqS = proj₂ (hS (₁₊ n) n)

  Motive : Word (SemiDirect.Gen (₁₊ n)) → Set
  Motive w = Bot₁ (proj₁ (⟦_⟧ˢᵈ {₁₊ n} w))
           × ((R : Pauli n) →
              ap (proj₂ (⟦_⟧ˢᵈ {₁₊ n} w)) (pI ∷ R) ≡ pI ∷ R)

-- The one-wire gates together.
gate₁-bot : (h : Pap.SympGate 1) →
            Bot₁ (Pᵂ {₁₊ n} [ Pap.gate₁ h ]ʷ)
          × ((R : Pauli n) →
             ap (Sᵂ {₁₊ n} [ Pap.gate₁ h ]ʷ) (pI ∷ R) ≡ pI ∷ R)
gate₁-bot Pap.H-gate = gate₁H-bot
gate₁-bot Pap.S-gate = gate₁S-bot

------------------------------------------------------------------------
-- A bottom-supported Pauli does not see a top-supported one
--
-- sform is a sum over wires, and at every wire one of the two arguments
-- is trivial.  These are the four shapes the commutation rules need.

sform-bot-top : (q : Pauli1) (P : Pauli n) → sform (q ∷ pIₙ) (pI ∷ P) ≡ ₀
sform-bot-top q P =
  Eq.trans (Eq.cong₂ _+_ (Sem.sform1-pIʳ q) (Sem.sform-pIˡ P)) (+-identityʳ ₀)

sform-top-bot : (P : Pauli n) (q : Pauli1) → sform (pI ∷ P) (q ∷ pIₙ) ≡ ₀
sform-top-bot P q =
  Eq.trans (Eq.cong₂ _+_ (Sem.sform1-pIˡ q) (Sem.sform-pIʳ P)) (+-identityʳ ₀)

sform-bot-top₂ : (q q' : Pauli1) (P : Pauli n) →
                 sform (q ∷ q' ∷ pIₙ) (pI ∷ pI ∷ P) ≡ ₀
sform-bot-top₂ q q' P =
  Eq.trans (Eq.cong₂ _+_ (Sem.sform1-pIʳ q) (sform-bot-top q' P))
           (+-identityʳ ₀)

sform-top-bot₂ : (P : Pauli n) (q q' : Pauli1) →
                 sform (pI ∷ pI ∷ P) (q ∷ q' ∷ pIₙ) ≡ ₀
sform-top-bot₂ P q q' =
  Eq.trans (Eq.cong₂ _+_ (Sem.sform1-pIˡ q) (sform-top-bot P q'))
           (+-identityʳ ₀)

------------------------------------------------------------------------
-- Pure-Z locality
--
-- Sharper than Bot₁, and what order-S needs: the Pauli is not merely on
-- wire 0 but has no X-part there.  Two such Paulis have sform ₀ —
-- sform1 (₀,b) (₀,b') = (-₀)·b' + ₀·b — and the shear preserves the
-- shape, since it adds the X-part to the Z-part and that is ₀.  So the
-- whole of S ^ k stays pure-Z and every cocycle term along it vanishes.

BotZ : Pauli (₁₊ n) → Set
BotZ {n} P = ∃ λ (b : ℤ ₚ) → P ≡ (₀ , b) ∷ pIₙ

-- Z ^ j is pure-Z: the same induction as Z^-bot, one component sharper.
Z^-botZ : (j : ℕ) → BotZ (proj₁ (⟦_⟧ˢᵈ {₁₊ n} (SemiDirect.Z ^ j)))
Z^-botZ zero      = ₀ , Eq.refl
Z^-botZ (₁₊ zero) = ₁ , Eq.refl
Z^-botZ {n} (₂₊ j) =
  ( ₁ + proj₁ (Z^-botZ {n} (₁₊ j))
  , Eq.trans (Eq.cong proj₁ (∙ᵃᵖ (SemiDirect.Z {n}) (SemiDirect.Z ^ ₁₊ j)))
      (Eq.trans (Eq.cong (pZ₀ +ₚ_) (proj₂ (Z^-botZ {n} (₁₊ j))))
        (Eq.trans
          (Eq.cong (λ z → (z , ₁ + proj₁ (Z^-botZ {n} (₁₊ j)))
                            ∷ (pIₙ +ₚ pIₙ))
                   (+-identityʳ ₀))
          (Eq.cong ((₀ , ₁ + proj₁ (Z^-botZ {n} (₁₊ j))) ∷_)
                   (+ₚ-identityˡ pIₙ)))) )

-- Appending the symplectic S keeps it pure-Z (the S contributes no
-- Pauli of its own; this is ZS-bot's first component, sharpened).
ZS-botZ : (w : Word (SemiDirect.Gen (₁₊ n))) →
          BotZ (proj₁ (⟦_⟧ˢᵈ {₁₊ n} w)) →
          (proj₂ (⟦_⟧ˢᵈ {₁₊ n} w) ≈ˢ εˢ) →
          BotZ (proj₁ (⟦_⟧ˢᵈ {₁₊ n} (w • SemiDirect.S)))
ZS-botZ {n} w (b , e) sy =
  ( b
  , Eq.trans (Eq.cong proj₁ (∙ᵃᵖ w SemiDirect.S))
      (Eq.trans (Eq.cong (proj₁ (⟦_⟧ˢᵈ {₁₊ n} w) +ₚ_) (sy pIₙ))
                (Eq.trans (+ₚ-identityʳ (proj₁ (⟦_⟧ˢᵈ {₁₊ n} w))) e)) )

-- ... so the S gate's own Pauli is pure-Z, by the same transport as
-- gate₁S-bot.
gate₁S-botZ : BotZ (Pᵂ {₁₊ n} [ Pap.gate₁ Pap.S-gate ]ʷ)
gate₁S-botZ {n} =
  Eq.subst MotiveZ (Eq.sym eqS) (ZS-botZ wS (Z^-botZ jS) (proj₂ (Z^-bot jS)))
  where
  jS : ℕ
  jS = proj₁ (hS (₁₊ n) n)

  wS : Word (SemiDirect.Gen (₁₊ n))
  wS = SemiDirect.Z ^ jS

  eqS : Fwd.Iso.h (₁₊ n) (Pap.gate₁ Pap.S-gate) ≡ wS • SemiDirect.S
  eqS = proj₂ (hS (₁₊ n) n)

  MotiveZ : Word (SemiDirect.Gen (₁₊ n)) → Set
  MotiveZ w = BotZ (proj₁ (⟦_⟧ˢᵈ {₁₊ n} w))

-- Two pure-Z Paulis do not see each other.
sform-Z-Z : (b b' : ℤ ₚ) (P : Pauli n) →
            sform ((₀ , b) ∷ pIₙ) ((₀ , b') ∷ P) ≡ ₀
sform-Z-Z b b' P =
  Eq.trans (Eq.cong₂ _+_ z1 (Sem.sform-pIˡ P)) (+-identityʳ ₀)
  where
  z1 : ((- ₀) * b') + (₀ * b) ≡ ₀
  z1 = Eq.trans (Eq.cong₂ _+_ (Eq.trans (Eq.cong (_* b') -0#≈0#) (*-zeroˡ b'))
                              (*-zeroˡ b))
                (+-identityʳ ₀)

-- The S gate FIXES a pure-Z Pauli.  The shear adds the X-part to the
-- Z-part, and a pure-Z has no X-part — this is the fact that makes
-- every prefix of S ^ k pure-Z, hence every cocycle term along it zero.
ZS-fixZ : (w : Word (SemiDirect.Gen (₁₊ n))) →
          (proj₂ (⟦_⟧ˢᵈ {₁₊ n} w) ≈ˢ εˢ) →
          (b : ℤ ₚ) (R : Pauli n) →
          ap (proj₂ (⟦_⟧ˢᵈ {₁₊ n} (w • SemiDirect.S))) ((₀ , b) ∷ R)
            ≡ (₀ , b) ∷ R
ZS-fixZ {n} w sy b R =
  Eq.trans (Eq.cong (λ z → ap (proj₂ z) ((₀ , b) ∷ R)) (∙ᵃᵖ w SemiDirect.S))
    (Eq.trans (sy ((₀ , b + ₀) ∷ R))
              (Eq.cong (λ z → (₀ , z) ∷ R) (+-identityʳ b)))

gate₁S-fixZ : (b : ℤ ₚ) (R : Pauli n) →
              ap (Sᵂ {₁₊ n} [ Pap.gate₁ Pap.S-gate ]ʷ) ((₀ , b) ∷ R)
                ≡ (₀ , b) ∷ R
gate₁S-fixZ {n} b R =
  Eq.subst MotiveF (Eq.sym eqS) (ZS-fixZ wS (proj₂ (Z^-bot jS)) b R)
  where
  jS : ℕ
  jS = proj₁ (hS (₁₊ n) n)

  wS : Word (SemiDirect.Gen (₁₊ n))
  wS = SemiDirect.Z ^ jS

  eqS : Fwd.Iso.h (₁₊ n) (Pap.gate₁ Pap.S-gate) ≡ wS • SemiDirect.S
  eqS = proj₂ (hS (₁₊ n) n)

  MotiveF : Word (SemiDirect.Gen (₁₊ n)) → Set
  MotiveF w = ap (proj₂ (⟦_⟧ˢᵈ {₁₊ n} w)) ((₀ , b) ∷ R) ≡ (₀ , b) ∷ R

------------------------------------------------------------------------
-- The gates' actions in full
--
-- gate₁S-fixZ above is the pure-Z case; the remaining rules — order-SH
-- most of all, the only one whose answer is not ₀ — need the action on
-- an arbitrary Pauli.  H is pure symplectic, so its action IS `actg` and
-- the fact is definitional; S goes through the same transport as before.

gate₁H-act : (a b : ℤ ₚ) (R : Pauli n) →
             ap (Sᵂ {₁₊ n} [ Pap.gate₁ Pap.H-gate ]ʷ) ((a , b) ∷ R)
               ≡ ((- b) , a) ∷ R
gate₁H-act a b R = Eq.refl

ZS-act : (w : Word (SemiDirect.Gen (₁₊ n))) →
         (proj₂ (⟦_⟧ˢᵈ {₁₊ n} w) ≈ˢ εˢ) →
         (a b : ℤ ₚ) (R : Pauli n) →
         ap (proj₂ (⟦_⟧ˢᵈ {₁₊ n} (w • SemiDirect.S))) ((a , b) ∷ R)
           ≡ (a , b + a) ∷ R
ZS-act {n} w sy a b R =
  Eq.trans (Eq.cong (λ z → ap (proj₂ z) ((a , b) ∷ R)) (∙ᵃᵖ w SemiDirect.S))
           (sy ((a , b + a) ∷ R))

gate₁S-act : (a b : ℤ ₚ) (R : Pauli n) →
             ap (Sᵂ {₁₊ n} [ Pap.gate₁ Pap.S-gate ]ʷ) ((a , b) ∷ R)
               ≡ (a , b + a) ∷ R
gate₁S-act {n} a b R =
  Eq.subst MotiveA (Eq.sym eqS) (ZS-act wS (proj₂ (Z^-bot jS)) a b R)
  where
  jS : ℕ
  jS = proj₁ (hS (₁₊ n) n)

  wS : Word (SemiDirect.Gen (₁₊ n))
  wS = SemiDirect.Z ^ jS

  eqS : Fwd.Iso.h (₁₊ n) (Pap.gate₁ Pap.S-gate) ≡ wS • SemiDirect.S
  eqS = proj₂ (hS (₁₊ n) n)

  MotiveA : Word (SemiDirect.Gen (₁₊ n)) → Set
  MotiveA w = ap (proj₂ (⟦_⟧ˢᵈ {₁₊ n} w)) ((a , b) ∷ R) ≡ (a , b + a) ∷ R

------------------------------------------------------------------------
-- The S gate's Pauli, pinned down
--
-- The five remaining rules all need the VALUE of P⟦S⟧, not just its
-- shape.  It is (₀ , -½), but -½ must never be evaluated: it is a
-- modular inverse.  Two devices keep it symbolic.
--
--   * `hS-val` matches `Z ^ toℕ ?x` rather than `Z ^ ?j`, so the meta is
--     solved at the level of ℤ/pℤ and the numeral is never formed;
--   * -½ is characterised by `x + x ≡ - ₁` rather than named, so every
--     use downstream is arithmetic in ℤ/pℤ with nothing to unfold.

-- Z ^ j has Pauli (₀ , mult j): Z^-botZ with the value kept.
Z^-val : (j : ℕ) →
         proj₁ (⟦_⟧ˢᵈ {₁₊ n} (SemiDirect.Z ^ j)) ≡ (₀ , mult j) ∷ pIₙ
Z^-val zero      = Eq.refl
Z^-val (₁₊ zero) = Eq.cong (λ z → (₀ , z) ∷ pIₙ) (Eq.sym (+-identityʳ ₁))
Z^-val {n} (₂₊ j) =
  Eq.trans (Eq.cong proj₁ (∙ᵃᵖ (SemiDirect.Z {n}) (SemiDirect.Z ^ ₁₊ j)))
    (Eq.trans (Eq.cong (pZ₀ +ₚ_) (Z^-val {n} (₁₊ j)))
      (Eq.trans (Eq.cong (λ z → (z , ₁ + mult (₁₊ j)) ∷ (pIₙ +ₚ pIₙ))
                         (+-identityʳ ₀))
                (Eq.cong ((₀ , ₁ + mult (₁₊ j)) ∷_) (+ₚ-identityˡ pIₙ))))

-- Appending the symplectic S keeps the value.
ZS-val : (w : Word (SemiDirect.Gen (₁₊ n))) (b : ℤ ₚ) →
         proj₁ (⟦_⟧ˢᵈ {₁₊ n} w) ≡ (₀ , b) ∷ pIₙ →
         (proj₂ (⟦_⟧ˢᵈ {₁₊ n} w) ≈ˢ εˢ) →
         proj₁ (⟦_⟧ˢᵈ {₁₊ n} (w • SemiDirect.S)) ≡ (₀ , b) ∷ pIₙ
ZS-val {n} w b e sy =
  Eq.trans (Eq.cong proj₁ (∙ᵃᵖ w SemiDirect.S))
    (Eq.trans (Eq.cong (proj₁ (⟦_⟧ˢᵈ {₁₊ n} w) +ₚ_) (sy pIₙ))
              (Eq.trans (+ₚ-identityʳ (proj₁ (⟦_⟧ˢᵈ {₁₊ n} w))) e))

-- NOT YET: the VALUE of P⟦S⟧, which is what all five remaining rules
-- need (order-SH above all — the only rule whose answer is not ₀; its
-- phase is -x²/2 for x the Z-exponent, and that is -⅛ exactly when
-- x = -½).  Z^-val and ZS-val above carry the value as far as it goes
-- without naming the exponent.
--
-- Both ways of naming it fail, in OPPOSITE directions:
--
--   * `∃ λ x → h (gate₁ S-gate) ≡ (Z ^ toℕ x) • S`, solved by a meta —
--     `toℕ ?x` is not solvable by matching (toℕ is not injective for the
--     unifier), so Agda normalises and unfolds Bézout.  364 s, then
--     UnequalTerms naming Data.Nat.GCD.Bézout.gcd″;
--   * `h (gate₁ S-gate) ≡ (Z ^ toℕ Cli.-1/2) • S` by `refl`, with the
--     constant written out on BOTH sides and no meta at all — worse,
--     OOM at 419 s.  `_^_` is a defined function, so conversion reduces
--     both sides to whnf before comparing, and that forces toℕ of the
--     inverse regardless.
--
-- So the meta was the thing keeping the earlier `hS` cheap: with `Z ^ ?j`
-- the unifier takes the same-head shortcut and never reduces.  That
-- shortcut is unavailable once the exponent is written.
--
-- The fix is therefore at the DEFINITION: make Simplified-V1.Syntactics'
-- `1/2` / `-1/2` abstract, exporting `₂ * 1/2 ≡ ₁` beside them, so the
-- constant is stuck everywhere and `hS`'s meta route still applies.
-- That file is imported by the whole qupit chain and some existing proof
-- may well be computing 1/2 today, so expect fallout and do it when
-- nobody else is editing Simplified-V1 or Paper-V0.

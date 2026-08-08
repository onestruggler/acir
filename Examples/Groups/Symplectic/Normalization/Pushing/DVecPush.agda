------------------------------------------------------------------------
-- Presentations of groups
--
-- Pushing single dirty gates (S, H, S↑, H↑) through a D-vector, with the
-- residual exposed as a `dir ↑` (one wire up).  S/H (wire 0) interact
-- only with the bottom D-box (aux-DS / aux-DH) and commute past the
-- lifted tail; S↑/H↑ (wire 1) descend one box and recurse.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.Pushing.DVecPush (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Vec using (Vec ; _∷_)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Lemmas4-Sym p-2 p-prime using (comm-dbox-w↑↑)
open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime using (aux-DS ; dir-of-DS ; d-of-DS)
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime using (cong↓ᵏ ; ↑↓ᵏ-comm)
open import Examples.Groups.Symplectic.BR.Three.DD-CZ-n p-2 p-prime using (d-↓ᵏ)
import Examples.Groups.Symplectic.BR.Two.D p-2 p-prime as TD

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃ ; ∃-syntax)
open import Examples.Groups.Symplectic.BR.Three.DD-CZ-n p-2 p-prime using (gen-dd-cz ; gen-dir-of ; gen-vd'-of)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Notations
open import Word.Base using (Word ; _•_ ; ε ; [_]ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

------------------------------------------------------------------------
-- H through a single D box, clean dir↑ form, widened from Two.D.lemma-D-br
-- (whose H direction has e = 0, so the emitted S^e ↓ vanishes).

Hdir : D → Word (Gen 1)
Hdir d = proj₂ (TD.dir-of d H-gen (λ ()))
Hd' : D → D
Hd' d = TD.d'-of d H-gen (λ ())

H-e≡0 : ∀ (d : D) → proj₁ (TD.dir-of d H-gen (λ ())) ≡ ₀
H-e≡0 (₀ , ₀)      = Eq.refl
H-e≡0 (₀ , ₁₊ b)   = Eq.refl
H-e≡0 (₁₊ a , ₀)   = Eq.refl
H-e≡0 (₁₊ a , ₁₊ b) = Eq.refl

module _ where
  open PB (₂ QRel,_===_) ; open PP (₂ QRel,_===_) ; open SR word-setoid
  DH2 : ∀ (d : D) → [ d ]ᵈ • H ≈ (Hdir d ↑) • [ Hd' d ]ᵈ
  DH2 d = trans (TD.lemma-D-br d H-gen (λ ()))
            (trans (cleft (refl' (Eq.cong (λ x → S^ x ↓) (H-e≡0 d)))) left-unit)

module _ {n : ℕ} where
  open PB ((₂₊ n) QRel,_===_) ; open PP ((₂₊ n) QRel,_===_) ; open SR word-setoid
  gen-DH-box : ∀ (d : D) → [_]ᵈ {n} d • H ≈ ((Hdir d ↓ᵏ n) ↑) • [_]ᵈ {n} (Hd' d)
  gen-DH-box d = trans (refl' (Eq.sym (Eq.cong₂ _•_ (d-↓ᵏ {0} d n) Eq.refl)))
                   (trans (cong↓ᵏ n _ _ (DH2 d))
                     (refl' (Eq.cong₂ _•_ (↑↓ᵏ-comm (Hdir d) n) (d-↓ᵏ {0} (Hd' d) n))))

------------------------------------------------------------------------
-- Wire-0 gates: interact with the bottom box, commute past the tail.

module _ {n : ℕ} where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

  dvec-S : ∀ (d₁ : D) (tl : Vec D n) →
    [ (d₁ ∷ tl) ]ᵛᵈ • S ≈ (dir-of-DS d₁ ↑) • [ (d-of-DS d₁ ∷ tl) ]ᵛᵈ
  dvec-S d₁ tl = begin
    ([ d₁ ]ᵈ • [ tl ]ᵛᵈ ↑) • S                              ≈⟨ assoc ⟩
    [ d₁ ]ᵈ • ([ tl ]ᵛᵈ ↑ • S)                              ≈⟨ cright (sym (lemma-comm-S-w↑ [ tl ]ᵛᵈ)) ⟩
    [ d₁ ]ᵈ • (S • [ tl ]ᵛᵈ ↑)                              ≈⟨ sym assoc ⟩
    ([ d₁ ]ᵈ • S) • [ tl ]ᵛᵈ ↑                              ≈⟨ cleft (aux-DS d₁) ⟩
    ((dir-of-DS d₁ ↑) • [ d-of-DS d₁ ]ᵈ) • [ tl ]ᵛᵈ ↑       ≈⟨ assoc ⟩
    (dir-of-DS d₁ ↑) • ([ d-of-DS d₁ ]ᵈ • [ tl ]ᵛᵈ ↑)       ∎

  dvec-H : ∀ (d₁ : D) (tl : Vec D n) →
    [ (d₁ ∷ tl) ]ᵛᵈ • H ≈ ((Hdir d₁ ↓ᵏ n) ↑) • [ (Hd' d₁ ∷ tl) ]ᵛᵈ
  dvec-H d₁ tl = begin
    ([ d₁ ]ᵈ • [ tl ]ᵛᵈ ↑) • H                              ≈⟨ assoc ⟩
    [ d₁ ]ᵈ • ([ tl ]ᵛᵈ ↑ • H)                              ≈⟨ cright (sym (lemma-comm-H-w↑ [ tl ]ᵛᵈ)) ⟩
    [ d₁ ]ᵈ • (H • [ tl ]ᵛᵈ ↑)                              ≈⟨ sym assoc ⟩
    ([ d₁ ]ᵈ • H) • [ tl ]ᵛᵈ ↑                              ≈⟨ cleft (gen-DH-box d₁) ⟩
    (((Hdir d₁ ↓ᵏ n) ↑) • [ Hd' d₁ ]ᵈ) • [ tl ]ᵛᵈ ↑        ≈⟨ assoc ⟩
    ((Hdir d₁ ↓ᵏ n) ↑) • ([ Hd' d₁ ]ᵈ • [ tl ]ᵛᵈ ↑)        ∎

------------------------------------------------------------------------
-- Wire-1 gates: g↑ combines with the lifted tail, recurse via dvec, and
-- the residual (now two wires up) commutes past the bottom box.

module _ {n : ℕ} where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid

  dvec-S↑ : ∀ (d₁ h : D) (t : Vec D n) →
    [ (d₁ ∷ h ∷ t) ]ᵛᵈ • S ↑ ≈ (dir-of-DS h ↑ ↑) • [ (d₁ ∷ d-of-DS h ∷ t) ]ᵛᵈ
  dvec-S↑ d₁ h t = begin
    ([ d₁ ]ᵈ • [ h ∷ t ]ᵛᵈ ↑) • S ↑                                        ≈⟨ assoc ⟩
    [ d₁ ]ᵈ • (([ h ∷ t ]ᵛᵈ • S) ↑)                                        ≈⟨ cright (lemma-cong↑ _ _ (dvec-S h t)) ⟩
    [ d₁ ]ᵈ • ((dir-of-DS h ↑ ↑) • [ d-of-DS h ∷ t ]ᵛᵈ ↑)                  ≈⟨ sym assoc ⟩
    ([ d₁ ]ᵈ • (dir-of-DS h ↑ ↑)) • [ d-of-DS h ∷ t ]ᵛᵈ ↑                  ≈⟨ cleft (comm-dbox-w↑↑ d₁ (dir-of-DS h)) ⟩
    ((dir-of-DS h ↑ ↑) • [ d₁ ]ᵈ) • [ d-of-DS h ∷ t ]ᵛᵈ ↑                  ≈⟨ assoc ⟩
    (dir-of-DS h ↑ ↑) • ([ d₁ ]ᵈ • [ d-of-DS h ∷ t ]ᵛᵈ ↑)                  ∎

  dvec-H↑ : ∀ (d₁ h : D) (t : Vec D n) →
    [ (d₁ ∷ h ∷ t) ]ᵛᵈ • H ↑ ≈ ((Hdir h ↓ᵏ n) ↑ ↑) • [ (d₁ ∷ Hd' h ∷ t) ]ᵛᵈ
  dvec-H↑ d₁ h t = begin
    ([ d₁ ]ᵈ • [ h ∷ t ]ᵛᵈ ↑) • H ↑                                        ≈⟨ assoc ⟩
    [ d₁ ]ᵈ • (([ h ∷ t ]ᵛᵈ • H) ↑)                                        ≈⟨ cright (lemma-cong↑ _ _ (dvec-H h t)) ⟩
    [ d₁ ]ᵈ • (((Hdir h ↓ᵏ n) ↑ ↑) • [ Hd' h ∷ t ]ᵛᵈ ↑)                    ≈⟨ sym assoc ⟩
    ([ d₁ ]ᵈ • ((Hdir h ↓ᵏ n) ↑ ↑)) • [ Hd' h ∷ t ]ᵛᵈ ↑                    ≈⟨ cleft (comm-dbox-w↑↑ d₁ (Hdir h ↓ᵏ n)) ⟩
    (((Hdir h ↓ᵏ n) ↑ ↑) • [ d₁ ]ᵈ) • [ Hd' h ∷ t ]ᵛᵈ ↑                    ≈⟨ assoc ⟩
    ((Hdir h ↓ᵏ n) ↑ ↑) • ([ d₁ ]ᵈ • [ Hd' h ∷ t ]ᵛᵈ ↑)                    ∎

------------------------------------------------------------------------
-- Push a whole Word (Gen 2) (padded to wires 0,1) through the D-vector,
-- composing the per-letter atoms; residual stays dir↑.

module _ {n : ℕ} where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid

  -- One letter of the residual word, pushed through the D-vector.  Split
  -- off from `dvec-word` so the constructor patterns (gate₁ S-gate, …) do
  -- not clash with the `[_]ʷ` bracket in the `∷`-pattern LHS.
  dvec-letter : ∀ (g : Gen 2) (vd : Vec D (₂₊ n)) →
    ∃[ dir ] ∃[ vd' ] ([ vd ]ᵛᵈ • ([ g ]ʷ ↓ᵏ (₁₊ n)) ≈ (dir ↑) • [ vd' ]ᵛᵈ)
  dvec-letter (gate₁ S-gate) (d₁ ∷ h ∷ t) =
    dir-of-DS d₁ , (d-of-DS d₁ ∷ h ∷ t) , dvec-S d₁ (h ∷ t)
  dvec-letter (gate₁ H-gate) (d₁ ∷ h ∷ t) =
    (Hdir d₁ ↓ᵏ (₁₊ n)) , (Hd' d₁ ∷ h ∷ t) , dvec-H d₁ (h ∷ t)
  dvec-letter (gate₂ CZ-gate) vd =
    gen-dir-of vd , gen-vd'-of vd , gen-dd-cz vd
  dvec-letter (gate₁ S-gate ↥) (d₁ ∷ h ∷ t) =
    (dir-of-DS h ↑) , (d₁ ∷ d-of-DS h ∷ t) , dvec-S↑ d₁ h t
  dvec-letter (gate₁ H-gate ↥) (d₁ ∷ h ∷ t) =
    ((Hdir h ↓ᵏ n) ↑) , (d₁ ∷ Hd' h ∷ t) , dvec-H↑ d₁ h t

  dvec-word : ∀ (u : Word (Gen 2)) (vd : Vec D (₂₊ n)) →
    ∃[ dir ] ∃[ vd' ] ([ vd ]ᵛᵈ • (u ↓ᵏ (₁₊ n)) ≈ (dir ↑) • [ vd' ]ᵛᵈ)
  dvec-word ε (d₁ ∷ h ∷ t) = ε , (d₁ ∷ h ∷ t) , trans right-unit (sym left-unit)
  dvec-word [ g ]ʷ vd = dvec-letter g vd
  dvec-word (u • v) vd =
    let (dir₁ , vd₁ , eq₁) = dvec-word u vd
        (dir₂ , vd₂ , eq₂) = dvec-word v vd₁
    in (dir₁ • dir₂) , vd₂ , (begin
      [ vd ]ᵛᵈ • ((u • v) ↓ᵏ (₁₊ n))            ≈⟨ sym assoc ⟩
      ([ vd ]ᵛᵈ • (u ↓ᵏ (₁₊ n))) • (v ↓ᵏ (₁₊ n)) ≈⟨ cleft eq₁ ⟩
      ((dir₁ ↑) • [ vd₁ ]ᵛᵈ) • (v ↓ᵏ (₁₊ n))     ≈⟨ assoc ⟩
      (dir₁ ↑) • ([ vd₁ ]ᵛᵈ • (v ↓ᵏ (₁₊ n)))     ≈⟨ cright eq₂ ⟩
      (dir₁ ↑) • ((dir₂ ↑) • [ vd₂ ]ᵛᵈ)          ≈⟨ sym assoc ⟩
      (dir₁ • dir₂) ↑ • [ vd₂ ]ᵛᵈ                ∎)

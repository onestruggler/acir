------------------------------------------------------------------------
-- Presentations of groups
--
-- Pushing a no-↥ Word (Gen 2) W (only wire-0 gates and CZ — the shape of
-- every L2-CZ residual) through an M column followed by a lifted B-vector:
--
--   [ m ]ᵐ • ([ vb ]ᵛᵇ ↑ • (W ↓ᵏ k)) ≈ dir ↑ • ([ m' ]ᵐ • [ vb ]ᵛᵇ ↑)
--
-- This generalises Push3 (the CZ case) to an arbitrary no-↥ residual, by
-- recursion on W: CZ atoms cross the B-vector via PushBvcz.bvec↑-cz and
-- then the M column via PushMW.push-MW (exactly Push3); wire-0 atoms
-- commute past the B-vector (lemma-comm-{H,S}-w↑) and cross the M column
-- via PushMword.push-Mʷ2 / push-Mʷ-suc.  All boxes are LM-Sym's.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.Pushing.PushMBword (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; _∷_ ; [])
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open Lemmas-Sym using (lemma-comm-H-w↑ ; lemma-comm-S-w↑)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.PushBvcz p-2 p-prime
  using (bvec↑-cz ; Wof)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMW p-2 p-prime
  using (push-MW)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMword p-2 p-prime
  using (push-Mʷ2 ; push-Mʷ-suc)
import Examples.Groups.Symplectic.BR.Two.D-w p-2 p-prime as DW
open import Examples.Groups.Symplectic.Normalization.Pushing.PushBword p-2 p-prime
  using (No-Top ; NoTopGen ; sg ; εⁿ ; _•ⁿ_)

open import Notations
open import Word.Base using (Word ; _•_ ; ε ; [_]ʷ)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

------------------------------------------------------------------------
-- No-↥ ⇒ No-top-H, and ↓ᵏ 0 is the identity on no-↥ words.

No-Top⇒No-Top-H : ∀ {W} → No-Top W → DW.No-Top-H W
No-Top⇒No-Top-H (sg {gate₁ x} _) = DW.sgⁿ (λ ())
No-Top⇒No-Top-H (sg {gate₂ x} _) = DW.sgⁿ (λ ())
No-Top⇒No-Top-H (sg {g ↥} ())
No-Top⇒No-Top-H εⁿ               = DW.εⁿ
No-Top⇒No-Top-H (ntu •ⁿ ntv)     = DW._•ⁿ_ (No-Top⇒No-Top-H ntu) (No-Top⇒No-Top-H ntv)

word-↓ᵏ0 : ∀ (W : Word (Gen 2)) → No-Top W → W ↓ᵏ 0 ≡ W
word-↓ᵏ0 ε                  εⁿ           = Eq.refl
word-↓ᵏ0 [ gate₁ x ]ʷ       _            = Eq.refl
word-↓ᵏ0 [ gate₂ x ]ʷ       _            = Eq.refl
word-↓ᵏ0 [ g ↥ ]ʷ           (sg ())
word-↓ᵏ0 (u • v)            (ntu •ⁿ ntv)  = Eq.cong₂ _•_ (word-↓ᵏ0 u ntu) (word-↓ᵏ0 v ntv)

------------------------------------------------------------------------
-- Pushing a no-↥ word through an M column (dir ↑ residual), uniform in
-- the width: width 2 uses push-Mʷ2, width ≥ 3 uses push-Mʷ-suc.

push-Mʷ : ∀ {k} (m : M (₂₊ k)) (W : Word (Gen 2)) → No-Top W →
  let open PB ((₂₊ k) QRel,_===_) in
  ∃ λ dir → ∃ λ m' → [ m ]ᵐ • (W ↓ᵏ k) ≈ dir ↑ • [ m' ]ᵐ
push-Mʷ {0} (d₀ ∷ [] , e) W nt =
  r .proj₂ .proj₁ , (r .proj₂ .proj₂ ∷ [] , e + - r .proj₁) ,
    trans (refl' (Eq.cong ([ (d₀ ∷ [] , e) ]ᵐ •_) (word-↓ᵏ0 W nt)))
          (push-Mʷ2 d₀ e W ntH)
  where
  open PB (2 QRel,_===_)
  open PP (2 QRel,_===_)
  ntH = No-Top⇒No-Top-H nt
  r   = DW.push-D-w d₀ W ntH
push-Mʷ {₁₊ k'} m W nt = push-Mʷ-suc m W

------------------------------------------------------------------------
-- The combined push.

module _ {k : ℕ} where
  open PB ((₂₊ k) QRel,_===_)
  open PP ((₂₊ k) QRel,_===_)
  open SR word-setoid

  push-MBvec-word : (W : Word (Gen 2)) → No-Top W → (m : M (₂₊ k)) (vb : Vec B k) →
    ∃ λ dir → ∃ λ m' →
      [ m ]ᵐ • ([ vb ]ᵛᵇ ↑ • (W ↓ᵏ k)) ≈ dir ↑ • ([ m' ]ᵐ • [ vb ]ᵛᵇ ↑)
  push-MBvec-word ε εⁿ m vb = ε , m , (begin
    [ m ]ᵐ • ([ vb ]ᵛᵇ ↑ • ε)   ≈⟨ cright right-unit ⟩
    [ m ]ᵐ • [ vb ]ᵛᵇ ↑         ≈⟨ sym left-unit ⟩
    ε • ([ m ]ᵐ • [ vb ]ᵛᵇ ↑)   ∎)
  push-MBvec-word [ gate₁ H-gate ]ʷ nt m vb =
    let (dir , m' , eq) = push-Mʷ m H nt
    in dir , m' , (begin
      [ m ]ᵐ • ([ vb ]ᵛᵇ ↑ • H)      ≈⟨ cright (sym (lemma-comm-H-w↑ [ vb ]ᵛᵇ)) ⟩
      [ m ]ᵐ • (H • [ vb ]ᵛᵇ ↑)      ≈⟨ sym assoc ⟩
      ([ m ]ᵐ • H) • [ vb ]ᵛᵇ ↑      ≈⟨ cleft eq ⟩
      (dir ↑ • [ m' ]ᵐ) • [ vb ]ᵛᵇ ↑ ≈⟨ assoc ⟩
      dir ↑ • ([ m' ]ᵐ • [ vb ]ᵛᵇ ↑) ∎)
  push-MBvec-word [ gate₁ S-gate ]ʷ nt m vb =
    let (dir , m' , eq) = push-Mʷ m S nt
    in dir , m' , (begin
      [ m ]ᵐ • ([ vb ]ᵛᵇ ↑ • S)      ≈⟨ cright (sym (lemma-comm-S-w↑ [ vb ]ᵛᵇ)) ⟩
      [ m ]ᵐ • (S • [ vb ]ᵛᵇ ↑)      ≈⟨ sym assoc ⟩
      ([ m ]ᵐ • S) • [ vb ]ᵛᵇ ↑      ≈⟨ cleft eq ⟩
      (dir ↑ • [ m' ]ᵐ) • [ vb ]ᵛᵇ ↑ ≈⟨ assoc ⟩
      dir ↑ • ([ m' ]ᵐ • [ vb ]ᵛᵇ ↑) ∎)
  push-MBvec-word [ gate₂ CZ-gate ]ʷ _ m vb =
    let (dir , m' , eq) = push-MW m vb
    in dir , m' , (begin
      [ m ]ᵐ • ([ vb ]ᵛᵇ ↑ • CZ)      ≈⟨ cright (bvec↑-cz vb) ⟩
      [ m ]ᵐ • (Wof vb • [ vb ]ᵛᵇ ↑)  ≈⟨ sym assoc ⟩
      ([ m ]ᵐ • Wof vb) • [ vb ]ᵛᵇ ↑  ≈⟨ cleft eq ⟩
      (dir ↑ • [ m' ]ᵐ) • [ vb ]ᵛᵇ ↑  ≈⟨ assoc ⟩
      dir ↑ • ([ m' ]ᵐ • [ vb ]ᵛᵇ ↑)  ∎)
  push-MBvec-word [ g ↥ ]ʷ (sg ()) m vb
  push-MBvec-word (u • v) (ntu •ⁿ ntv) m vb =
    let (diru , mu , equ) = push-MBvec-word u ntu m vb
        (dirv , mv , eqv) = push-MBvec-word v ntv mu vb
    in (diru • dirv) , mv , (begin
      [ m ]ᵐ • ([ vb ]ᵛᵇ ↑ • ((u ↓ᵏ k) • (v ↓ᵏ k)))   ≈⟨ cright (sym assoc) ⟩
      [ m ]ᵐ • (([ vb ]ᵛᵇ ↑ • (u ↓ᵏ k)) • (v ↓ᵏ k))   ≈⟨ sym assoc ⟩
      ([ m ]ᵐ • ([ vb ]ᵛᵇ ↑ • (u ↓ᵏ k))) • (v ↓ᵏ k)   ≈⟨ cleft equ ⟩
      (diru ↑ • ([ mu ]ᵐ • [ vb ]ᵛᵇ ↑)) • (v ↓ᵏ k)    ≈⟨ assoc ⟩
      diru ↑ • (([ mu ]ᵐ • [ vb ]ᵛᵇ ↑) • (v ↓ᵏ k))    ≈⟨ cright assoc ⟩
      diru ↑ • ([ mu ]ᵐ • ([ vb ]ᵛᵇ ↑ • (v ↓ᵏ k)))    ≈⟨ cright eqv ⟩
      diru ↑ • (dirv ↑ • ([ mv ]ᵐ • [ vb ]ᵛᵇ ↑))      ≈⟨ sym assoc ⟩
      (diru ↑ • dirv ↑) • ([ mv ]ᵐ • [ vb ]ᵛᵇ ↑)      ∎)

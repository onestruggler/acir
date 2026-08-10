------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric groups Sₙ and their normal form via coset enumeration
-- Adapted to the Circuit / Lift-Relation framework
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.Push2 (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; inspect ; module ≡-Reasoning) renaming ([_] to [_]ₑ)
import Relation.Binary.Reasoning.Setoid as SR
open import Relation.Nullary.Decidable using (yes ; no)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.NormalForm.Propositional as NFBase
open NFBase using (NormalFormInjective ; NormalForm)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Data.Sum


private variable
  n : ℕ

import Examples.Groups.Symplectic.BR.Two.ML'-Top p-2 p-prime as ML'T
import Examples.Groups.Symplectic.BR.Two.L2-CZ p-2 p-prime as LCZ2
open import Examples.Groups.Symplectic.BR.Two.D-w p-2 p-prime as TDw
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMword p-2 p-prime
  using (push-Mʷ2)
open import Examples.Groups.Symplectic.Normalization.Pushing.SectionLMBridge p-2 p-prime
  using (mbox-eq ; l'box-eq ; vbbox-eq)
import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime as LM
open import Examples.Groups.Symplectic.Normalization.Pushing.PushBword p-2 p-prime
  using (No-Top ; NoTopGen ; sg ; εⁿ ; _•ⁿ_)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMBword p-2 p-prime
  using (push-MBvec-word)
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime
  using (M-↓ᵏ ; S^-↓ᵏ ; cong↓ᵏ ; ↑↓ᵏ-comm ; ↓ᵏ-↓ᵏ-1)
open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime using (b-c=0⇒b=c)
open import Data.Fin using (toℕ ; _≟_)
open import Data.Empty using (⊥-elim)
open import Presentation.GroupLike

open import Data.Vec

------------------------------------------------------------------------
-- The L2-CZ residual is a no-↥ word (only wire-0 gates and CZ), so it is
-- a legal input to PushMBword.push-MBvec-word.  Vocabulary mirrors D-w's
-- No-Top-H set, and dir-of₂-No-Top mirrors D-w.dir-of₂-No-Top-H.

module _ where
  open PB (2 QRel,_===_)
  open Symplectic-GroupLike
  open Group-Lemmas (2 QRel,_===_) grouplike renaming (_⁻¹ to _⁻¹ʷ)

  nt-H  : No-Top H
  nt-H  = sg tt
  nt-S  : No-Top S
  nt-S  = sg tt
  nt-CZ : No-Top CZ
  nt-CZ = sg tt

  nt-^ : ∀ {w} → No-Top w → (k : ℕ) → No-Top (w ^ k)
  nt-^ nw zero      = εⁿ
  nt-^ nw (₁₊ zero) = nw
  nt-^ nw (₂₊ k)    = nw •ⁿ nt-^ nw (₁₊ k)

  nt-gen-inv : (g : Gen 2) → NoTopGen g → No-Top (proj₁ (grouplike g))
  nt-gen-inv H-gen  _ = nt-^ nt-H _
  nt-gen-inv S-gen  _ = nt-^ nt-S _
  nt-gen-inv CZ-gen _ = nt-^ nt-CZ _
  nt-gen-inv (g ↥)  ()

  nt-⁻¹ʷ : ∀ {w} → No-Top w → No-Top (w ⁻¹ʷ)
  nt-⁻¹ʷ (sg {g} ntg) = nt-gen-inv g ntg
  nt-⁻¹ʷ εⁿ           = εⁿ
  nt-⁻¹ʷ (nu •ⁿ nv)   = nt-⁻¹ʷ nv •ⁿ nt-⁻¹ʷ nu

  nt-S^  : (k : ℤ ₚ) → No-Top (S^ k)
  nt-S^  k = nt-^ nt-S (toℕ k)
  nt-CZ^ : (k : ℤ ₚ) → No-Top (CZ^ k)
  nt-CZ^ k = nt-^ nt-CZ (toℕ k)
  nt-HH  : No-Top HH
  nt-HH  = nt-^ nt-H 2
  nt-ZM  : (x : ℤ* ₚ) → No-Top (ZM x)
  nt-ZM  x = nt-S^ _ •ⁿ nt-H •ⁿ nt-S^ _ •ⁿ nt-H •ⁿ nt-S^ _ •ⁿ nt-H

  dir-of₂-No-Top : (l : L' 2 ⊎ L' 1) → No-Top (LCZ2.dir-of l)
  dir-of₂-No-Top (inj₁ (((c@₀ , d@₀) ∷ []) , ((a@₀ , b@(₁₊ _)) , nz))) with b ≟ c
  ... | yes ()
  ... | no neq = nt-CZ^ _
  dir-of₂-No-Top (inj₁ (((c@₀ , d@(₁₊ _)) ∷ []) , ((a@₀ , b@(₁₊ _)) , nz))) with b ≟ c
  ... | yes ()
  ... | no neq = nt-S^ _ •ⁿ nt-CZ^ _
  dir-of₂-No-Top (inj₁ (((c@(₁₊ _) , d) ∷ []) , ((a@₀ , b@(₁₊ _)) , nz))) with b ≟ c
  ... | yes eq = nt-⁻¹ʷ (nt-H •ⁿ nt-CZ^ (((b , λ ()) ⁻¹) .proj₁) •ⁿ nt-^ nt-H 3) •ⁿ nt-HH
  ... | no neq = nt-ZM ((b + - c , λ eq → neq (b-c=0⇒b=c b c eq)) *' ((b , λ ()) ⁻¹))
                   •ⁿ nt-H •ⁿ nt-CZ^ _ •ⁿ nt-^ nt-H _
  dir-of₂-No-Top (inj₁ (((c@₀ , d@₀) ∷ []) , ((a@(₁₊ _) , b) , nz)))          = εⁿ
  dir-of₂-No-Top (inj₁ (((c@₀ , d@(₁₊ _)) ∷ []) , ((a@(₁₊ _) , b) , nz)))     = εⁿ
  dir-of₂-No-Top (inj₁ (((c@(₁₊ _) , d) ∷ []) , ((a@(₁₊ _) , b) , nz)))       = nt-^ nt-H _ •ⁿ nt-S^ _ •ⁿ nt-H
  dir-of₂-No-Top (inj₁ (((c , d) ∷ []) , ((a@₀ , b@₀) , nzx)))                = ⊥-elim (nzx auto)
  dir-of₂-No-Top (inj₂ ([] , (a@₀ , b@(₁₊ _)) , nzx))                         = nt-CZ^ _
  dir-of₂-No-Top (inj₂ ([] , (a@(₁₊ _) , b) , nzx))                          = nt-H •ⁿ nt-CZ^ _ •ⁿ nt-^ nt-H _
  dir-of₂-No-Top (inj₂ ([] , (a@₀ , b@₀) , nzx))                             = ⊥-elim (nzx auto)

-- A-box widening: the A box is all wire-0 (M-gate, H, S powers), so ↓ᵏ
-- (padding wires on top) leaves it fixed up to the width index.
abox-↓ᵏ : ∀ {n' : ℕ} (a : A) (k : ℕ) → [_]ᵃ {n = n'} a ↓ᵏ k ≡ [_]ᵃ {n = Data.Nat._+_ n' k} a
abox-↓ᵏ ((₀ , ₀) , pr) k    = ⊥-elim (pr auto)
abox-↓ᵏ ((₀ , b₀@(₁₊ b)) , pr) k = Eq.cong₂ _•_ (M-↓ᵏ ((b₀ , λ ()) ⁻¹) k) Eq.refl
abox-↓ᵏ ((a₀@(₁₊ a) , b) , pr) k =
  Eq.cong₂ _•_ (M-↓ᵏ ((a₀ , λ ()) ⁻¹) k)
    (Eq.cong₂ _•_ Eq.refl (S^-↓ᵏ (- b * ((a₀ , λ ()) ⁻¹) .proj₁) k))

------------------------------------------------------------------------
-- Right coset action  (CZ on an ML' box; width-2 base case)
--
-- Pushing bottom CZ through an ML' (₂₊ n) box decomposes as: CZ through
-- the L' box (BR.Two.L2-CZ.lemma-dir-and-l'), whose residual is a
-- top-H-free Word (Gen 2) (D-w.dir-of₂-No-Top-H); that residual is pushed
-- through the M column (PushMword.push-Mʷ2).  Because the L' box can
-- *collapse* (its j=0 → j=1 case, l'-of ↦ inj₂), the result may land in
-- the D · ML branch of ML, so the coset lives in ML (₂₊ n), not ML'.

-- Interpret the L2-CZ output (L' 2 ⊎ L' 1) together with the updated M box
-- as an ML 2 coset: inj₁ (L' 2) stays an ML' box; inj₂ (L' 1) collapse
-- moves into the D · ML branch, its A box sitting one wire up.
coset : (L' 2 ⊎ L' 1) → M 2 → ML 2
coset (inj₁ l2)          m'              = inj₁ (m' , l2)
coset (inj₂ ([] , a2)) (d₀' ∷ [] , e'')  = inj₂ (d₀' , (([] , e'') , ([] , a2)))

module _ where
  open PB (2 QRel,_===_)
  open PP (2 QRel,_===_)
  open SR word-setoid

  -- [ m' ]ᵐ (LM-Sym) followed by the interpreted L2-CZ output is the ML
  -- coset (in Section boxes), via the Section ↔ LM-Sym box bridges.
  coset-eq : ∀ (l'' : L' 2 ⊎ L' 1) (m' : M 2) →
    LM.[ m' ]ᵐ • LCZ2.intp l'' ≈ [ coset l'' m' ]ᵐˡ
  coset-eq (inj₁ l2) m' =
    cong (refl' (Eq.sym (mbox-eq m'))) (refl' (Eq.sym (l'box-eq l2)))
  coset-eq (inj₂ ([] , a2)) (d₀' ∷ [] , e'') = begin
    LM.[ (d₀' ∷ [] , e'') ]ᵐ • (ε • LM.[ a2 ]ᵃ) ↑
      ≈⟨ cong (refl' (Eq.sym (mbox-eq (d₀' ∷ [] , e''))))
              (refl' (Eq.cong (_↑) (Eq.cong (ε •_) (Eq.sym (ML'T.abox-eq a2))))) ⟩
    [ (d₀' ∷ [] , e'') ]ᵐ • (ε • [ a2 ]ᵃ) ↑          ≈⟨ assoc ⟩
    [ d₀' ]ᵈ • ([ e'' ]ᵉ ↑ • (ε • [ a2 ]ᵃ) ↑)        ∎

-- General-width coset map: the L2-CZ output (L' 2 ⊎ L' 1) + updated M box
-- + inert upper B-vector bv' → the ML (₃₊ n) coset.  inj₁ stays an ML';
-- inj₂ collapse moves the (now bottom) D box out, leaving an ML' one wire
-- up in the D · ML branch.
coset-n : ∀ {n} → (L' 2 ⊎ L' 1) → M (₃₊ n) → Vec B (₁₊ n) → ML (₃₊ n)
coset-n (inj₁ ((b₀' ∷ []) , a')) m'             bv' = inj₁ (m' , ((b₀' ∷ bv') , a'))
coset-n (inj₂ ([] , a2))       (d₀' ∷ dr , e)   bv' = inj₂ (d₀' , inj₁ ((dr , e) , (bv' , a2)))

-- The right action of CZ on a coset: ract c CZ returns the residual
-- circuit b' and the coset c' reached, so that
-- [ c ]ᵐˡ' • [ gate₂ CZ ]ʷ ≈ b' ↑ • [ c' ]ᵐˡ (see ract-sound below).
ract : ∀ {n} -> ML' (₂₊ n) → SympGate 2 → Circuit (₁₊ n) × ML (₂₊ n)
ract {0} ((d₀ ∷ [] , e) , l) CZ-gate = dir-M , coset l'' m'
  where
  nt    = TDw.dir-of₂-No-Top-H (inj₁ l)
  pr    = TDw.push-D-w d₀ (LCZ2.dir-of (inj₁ l)) nt
  e'    = pr .proj₁
  dir-M = pr .proj₂ .proj₁
  d₀'   = pr .proj₂ .proj₂
  m'    = (d₀' ∷ [] , e + - e')
  l''   = LCZ2.l'-of (inj₁ l)
ract {₁₊ n} (m , ((b₀ ∷ bv') , a)) CZ-gate =
  proj₁ r , coset-n l'' (proj₁ (proj₂ r)) bv'
  where
  lc  = inj₁ ((b₀ ∷ []) , a)
  l'' = LCZ2.l'-of lc
  r   = push-MBvec-word (LCZ2.dir-of lc) (dir-of₂-No-Top lc) m bv'

------------------------------------------------------------------------
-- General-width core widening and coset interpretation.

module _ {n : ℕ} where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  module P2 = PB ((₂₊ n) QRel,_===_)

  -- LM-Sym A box (width 1 / 0) widened by ↓ᵏ (₁₊ n) = Section A box.
  abox-↓ᵏ-LM1 : (a : A) → LM.[_]ᵃ {n = 1} a ↓ᵏ (₁₊ n) ≡ [_]ᵃ {n = ₂₊ n} a
  abox-↓ᵏ-LM1 a = Eq.trans (Eq.cong (_↓ᵏ (₁₊ n)) (Eq.sym (ML'T.abox-eq {1} a)))
                           (abox-↓ᵏ {1} a (₁₊ n))
  abox-↓ᵏ-LM0 : (a : A) → LM.[_]ᵃ {n = 0} a ↓ᵏ (₁₊ n) ≡ [_]ᵃ {n = ₁₊ n} a
  abox-↓ᵏ-LM0 a = Eq.trans (Eq.cong (_↓ᵏ (₁₊ n)) (Eq.sym (ML'T.abox-eq {0} a)))
                           (abox-↓ᵏ {0} a (₁₊ n))

  -- L2-CZ widened to width (₃₊ n): CZ through the bottom B box · A box.
  -- (L2-CZ's single-element B-vector carries a leading ε = [ [] ]ᵛᵇ ↑.)
  core-widen : (b₀ : B) (a : A) →
    ([ b₀ ]ᵇ • [ a ]ᵃ) • CZ ≈
      (LCZ2.dir-of (inj₁ ((b₀ ∷ []) , a)) ↓ᵏ (₁₊ n)) •
      (LCZ2.intp (LCZ2.l'-of (inj₁ ((b₀ ∷ []) , a))) ↓ᵏ (₁₊ n))
  core-widen b₀ a = begin
    ([ b₀ ]ᵇ • [ a ]ᵃ) • CZ
      ≈⟨ cleft (cleft (sym left-unit)) ⟩
    ((ε • [ b₀ ]ᵇ) • [ a ]ᵃ) • CZ
      ≈⟨ refl' (Eq.cong₂ _•_ (Eq.cong₂ _•_
                 (Eq.cong₂ _•_ Eq.refl (Eq.sym (ML'T.bbox-↓ᵏ b₀ (₁₊ n))))
                 (Eq.sym (abox-↓ᵏ-LM1 a))) Eq.refl) ⟩
    ((ε • (LM.[_]ᵇ {n = 0} b₀ ↓ᵏ (₁₊ n))) • (LM.[_]ᵃ {n = 1} a ↓ᵏ (₁₊ n))) • CZ
      ≈⟨ cong↓ᵏ (₁₊ n) _ _ (LCZ2.lemma-dir-and-l' (inj₁ ((b₀ ∷ []) , a))) ⟩
    (LCZ2.dir-of (inj₁ ((b₀ ∷ []) , a)) ↓ᵏ (₁₊ n)) •
      (LCZ2.intp (LCZ2.l'-of (inj₁ ((b₀ ∷ []) , a))) ↓ᵏ (₁₊ n)) ∎

  -- Interpret [ m' ]ᵐ · (bv'↑ · widened L2-CZ output) as the ML coset.
  coset-eq-n : (l'' : L' 2 ⊎ L' 1) (m' : M (₃₊ n)) (bv' : Vec B (₁₊ n)) →
    [ m' ]ᵐ • ([ bv' ]ᵛᵇ ↑ • (LCZ2.intp l'' ↓ᵏ (₁₊ n))) ≈ [ coset-n l'' m' bv' ]ᵐˡ
  coset-eq-n (inj₁ ((b₀' ∷ []) , a')) m' bv' = begin
    [ m' ]ᵐ • ([ bv' ]ᵛᵇ ↑ • (LCZ2.intp (inj₁ ((b₀' ∷ []) , a')) ↓ᵏ (₁₊ n)))
      ≈⟨ cright (cright (refl' (Eq.cong₂ _•_
                 (Eq.cong₂ _•_ Eq.refl (ML'T.bbox-↓ᵏ b₀' (₁₊ n))) (abox-↓ᵏ-LM1 a')))) ⟩
    [ m' ]ᵐ • ([ bv' ]ᵛᵇ ↑ • ((ε • [ b₀' ]ᵇ) • [ a' ]ᵃ))  ≈⟨ cright (cright (cleft left-unit)) ⟩
    [ m' ]ᵐ • ([ bv' ]ᵛᵇ ↑ • ([ b₀' ]ᵇ • [ a' ]ᵃ))       ≈⟨ cright (sym assoc) ⟩
    [ m' ]ᵐ • (([ bv' ]ᵛᵇ ↑ • [ b₀' ]ᵇ) • [ a' ]ᵃ)       ∎
  coset-eq-n (inj₂ ([] , a2)) (d₀' ∷ dr , e) bv' = begin
    [ (d₀' ∷ dr , e) ]ᵐ • ([ bv' ]ᵛᵇ ↑ • (LCZ2.intp (inj₂ ([] , a2)) ↓ᵏ (₁₊ n)))
      ≈⟨ cright (cright (refl' (Eq.trans (↑↓ᵏ-comm (ε • LM.[_]ᵃ {n = 0} a2) (₁₊ n))
                                         (Eq.cong _↑ (Eq.cong₂ _•_ Eq.refl (abox-↓ᵏ-LM0 a2)))))) ⟩
    [ (d₀' ∷ dr , e) ]ᵐ • ([ bv' ]ᵛᵇ ↑ • (ε • [ a2 ]ᵃ) ↑)
      ≈⟨ cright (cright (lemma-cong↑ _ _ P2.left-unit)) ⟩
    [ (d₀' ∷ dr , e) ]ᵐ • ([ bv' ]ᵛᵇ ↑ • [ a2 ]ᵃ ↑)      ≈⟨ assoc ⟩
    [ d₀' ]ᵈ • ([ (dr , e) ]ᵐ ↑ • ([ bv' ]ᵛᵇ ↑ • [ a2 ]ᵃ ↑))  ∎

------------------------------------------------------------------------
-- Soundness of the coset action

-- ract-sound certifies the coset-table transition: for
-- (b' , c') = ract c b we have [ c ]ᵐˡ' • [ gate₂ b ]ʷ ≈ b' ↑ • [ c' ]ᵐˡ.
ract-sound : ∀ {n} c b →
  let
    open PB ((₂₊ n) QRel,_===_)
    (b' , c') = ract {n} c b
  in

    [ c ]ᵐˡ' • [ gate₂ b ]ʷ ≈ b' ↑ • [ c' ]ᵐˡ

ract-sound {0} ((d₀ ∷ [] , e) , l) CZ-gate = begin
  ([ (d₀ ∷ [] , e) ]ᵐ • [ l ]ˡ') • CZ
    ≈⟨ cleft (cright (refl' (l'box-eq l))) ⟩
  ([ (d₀ ∷ [] , e) ]ᵐ • LM.[ l ]ˡ') • CZ            ≈⟨ assoc ⟩
  [ (d₀ ∷ [] , e) ]ᵐ • (LM.[ l ]ˡ' • CZ)            ≈⟨ cright (LCZ2.lemma-dir-and-l' (inj₁ l)) ⟩
  [ (d₀ ∷ [] , e) ]ᵐ • (dir-L • LCZ2.intp l'')       ≈⟨ sym assoc ⟩
  ([ (d₀ ∷ [] , e) ]ᵐ • dir-L) • LCZ2.intp l''       ≈⟨ cleft (cleft (refl' (mbox-eq (d₀ ∷ [] , e)))) ⟩
  (LM.[ (d₀ ∷ [] , e) ]ᵐ • dir-L) • LCZ2.intp l''    ≈⟨ cleft (push-Mʷ2 d₀ e dir-L nt) ⟩
  (dir-M ↑ • LM.[ m' ]ᵐ) • LCZ2.intp l''             ≈⟨ assoc ⟩
  dir-M ↑ • (LM.[ m' ]ᵐ • LCZ2.intp l'')             ≈⟨ cright (coset-eq l'' m') ⟩
  dir-M ↑ • [ coset l'' m' ]ᵐˡ ∎
  where
  open PB (2 QRel,_===_)
  open PP (2 QRel,_===_)
  open SR word-setoid
  nt    = TDw.dir-of₂-No-Top-H (inj₁ l)
  dir-L = LCZ2.dir-of (inj₁ l)
  l''   = LCZ2.l'-of (inj₁ l)
  pr    = TDw.push-D-w d₀ dir-L nt
  e'    = pr .proj₁
  dir-M = pr .proj₂ .proj₁
  d₀'   = pr .proj₂ .proj₂
  m'    = (d₀' ∷ [] , e + - e')
ract-sound {₁₊ n} (m , ((b₀ ∷ bv') , a)) CZ-gate = begin
  ([ m ]ᵐ • (([ bv' ]ᵛᵇ ↑ • [ b₀ ]ᵇ) • [ a ]ᵃ)) • CZ
    ≈⟨ assoc ⟩
  [ m ]ᵐ • ((([ bv' ]ᵛᵇ ↑ • [ b₀ ]ᵇ) • [ a ]ᵃ) • CZ)     ≈⟨ cright assoc ⟩
  [ m ]ᵐ • (([ bv' ]ᵛᵇ ↑ • [ b₀ ]ᵇ) • ([ a ]ᵃ • CZ))     ≈⟨ cright assoc ⟩
  [ m ]ᵐ • ([ bv' ]ᵛᵇ ↑ • ([ b₀ ]ᵇ • ([ a ]ᵃ • CZ)))     ≈⟨ cright (cright (sym assoc)) ⟩
  [ m ]ᵐ • ([ bv' ]ᵛᵇ ↑ • (([ b₀ ]ᵇ • [ a ]ᵃ) • CZ))     ≈⟨ cright (cright (core-widen b₀ a)) ⟩
  [ m ]ᵐ • ([ bv' ]ᵛᵇ ↑ • ((LCZ2.dir-of lc ↓ᵏ (₁₊ n)) • core'))
    ≈⟨ cright (sym assoc) ⟩
  [ m ]ᵐ • (([ bv' ]ᵛᵇ ↑ • (LCZ2.dir-of lc ↓ᵏ (₁₊ n))) • core')
    ≈⟨ sym assoc ⟩
  ([ m ]ᵐ • ([ bv' ]ᵛᵇ ↑ • (LCZ2.dir-of lc ↓ᵏ (₁₊ n)))) • core'
    ≈⟨ cleft (cong (refl' (mbox-eq m)) (cong (refl' (Eq.cong (_↑) (vbbox-eq bv'))) refl)) ⟩
  (LM.[ m ]ᵐ • (LM.[ bv' ]ᵛᵇ ↑ • (LCZ2.dir-of lc ↓ᵏ (₁₊ n)))) • core'
    ≈⟨ cleft eq-r ⟩
  (dir ↑ • (LM.[ m' ]ᵐ • LM.[ bv' ]ᵛᵇ ↑)) • core'
    ≈⟨ cleft (cright (cong (refl' (Eq.sym (mbox-eq m'))) (refl' (Eq.cong (_↑) (Eq.sym (vbbox-eq bv')))))) ⟩
  (dir ↑ • ([ m' ]ᵐ • [ bv' ]ᵛᵇ ↑)) • core'              ≈⟨ assoc ⟩
  dir ↑ • (([ m' ]ᵐ • [ bv' ]ᵛᵇ ↑) • core')             ≈⟨ cright assoc ⟩
  dir ↑ • ([ m' ]ᵐ • ([ bv' ]ᵛᵇ ↑ • core'))             ≈⟨ cright (coset-eq-n l'' m' bv') ⟩
  dir ↑ • [ coset-n l'' m' bv' ]ᵐˡ ∎
  where
  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  lc    = inj₁ ((b₀ ∷ []) , a)
  l''   = LCZ2.l'-of lc
  r     = push-MBvec-word (LCZ2.dir-of lc) (dir-of₂-No-Top lc) m bv'
  dir   = proj₁ r
  m'    = proj₁ (proj₂ r)
  eq-r  = proj₂ (proj₂ r)
  core' = LCZ2.intp l'' ↓ᵏ (₁₊ n)

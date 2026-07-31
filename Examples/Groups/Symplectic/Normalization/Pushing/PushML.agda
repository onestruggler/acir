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

module Examples.Groups.Symplectic.Normalization.Pushing.PushML (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using (≡×≡⇒≡ ; Pointwise ; ≡⇒≡×≡)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; inspect ; module ≡-Reasoning) renaming ([_] to [_]ₑ)
import Relation.Binary.Reasoning.Setoid as SR
open import Relation.Nullary.Decidable using (yes ; no)

open import Word.Base
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.NormalForm.Propositional as NFBase
import Normalization.NormalForm.Setoid as SNF
open NFBase using (NormalFormInjective ; NormalForm)
import Normalization.CosetNF as CosetNF


--open import Examples.Groups.Symplectic.NewCosets p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Data.Sum


private variable
  n : ℕ


open import Data.Vec
open import Data.Nat using (s≤s ; z≤n)

open Lemmas-Sym using (lemma-comm-S-w↑ ; lemma-comm-H-w↑)
open import Examples.Groups.Symplectic.BR.Three.DD-CZ-n p-2 p-prime using (gen-dd-cz-tail)
import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ
import Examples.Groups.Symplectic.BR.Two.ML'-Top p-2 p-prime as ML'T
import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime as LM
open import Examples.Groups.Symplectic.Normalization.Pushing.DS p-2 p-prime
  using (aux-DS ; dir-of-DS ; d-of-DS)
open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush p-2 p-prime
  using (Hdir ; Hd' ; gen-DH-box)
import Examples.Groups.Symplectic.Normalization.Pushing.Push p-2 p-prime as Push
import Examples.Groups.Symplectic.Normalization.Pushing.Push2 p-2 p-prime as Push2
import Examples.Groups.Symplectic.Normalization.Pushing.Push6 p-2 p-prime as Push6
import Examples.Groups.Symplectic.BR.Two.L2-CZ p-2 p-prime as LCZ2
open import Examples.Groups.Symplectic.BR.Two.D-w p-2 p-prime as TDw
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMword p-2 p-prime
  using (push-Mʷ2)
open import Examples.Groups.Symplectic.Normalization.Pushing.SectionLMBridge p-2 p-prime
  using (mbox-eq)

------------------------------------------------------------------------
-- Right coset action
--
-- The right action of a generator on a coset: ract c g returns the
-- residual circuit b' and the coset c' reached from c by g, so that
-- [ c ]ᶜ • [ g ]ʷ ≈ b' ↑ • [ c' ]ᶜ (see ract-sound below).
--
-- The full ML box is a chain of bottom D boxes (inj₂) capped by an ML'
-- box (inj₁).  ract case-splits on the generator and the box:
--   • inj₁ (a pure ML') dispatches to the three ML'-level pushes:
--       gate₁  → Push.ract     (bottom unary S/H, BR.Two.ML'-Bot)
--       gate₂  → Push2.ract     (bottom CZ, may collapse L' into the sum)
--       g ↥    → BR.Two.ML'-Top  (a lifted gate)
--   • inj₂ (d , lm) — a bottom D box then a lifted sub-ML:
--       gate₁  → the wire-0 gate commutes past lm↑ and rewrites only d
--                 (single-gate D-box push DS / DVecPush)
--       g ↥    → structural recursion ract lm g, d commuted past the
--                 escaped direction (comm-dbox-w↑↑-S)
--       gate₂  → CZ meets the bottom two D boxes (gen-dd-cz-tail); when
--                 only one D box is exposed the L' below can collapse.

C = ML

ract : ∀ {n} -> C (₁₊ n) → Gen (₁₊ n) → Circuit n × C (₁₊ n)
-- Width 1 (no B boxes, no sum): ML 1 = ML' 1, only bottom unary gates.
ract {₀} ml (gate₁ x) = Push.ract ml x
-- inj₁: a pure ML' box.
ract {₁₊ n} (inj₁ ml') (gate₁ x) =
  let (dir , ml'') = Push.ract ml' x in dir , inj₁ ml''
ract {₁₊ n} (inj₁ ml') (gate₂ CZ-gate) = Push2.ract ml' CZ-gate
ract {₁₊ n} (inj₁ ml') (h ↥) = ML'T.dir-of ml' h , inj₁ (ML'T.ml'-of ml' h)
-- inj₂: a bottom D box then a lifted sub-ML.
ract {₁₊ n} (inj₂ (d , lm)) (gate₁ S-gate) =
  dir-of-DS d , inj₂ (d-of-DS d , lm)
ract {₁₊ n} (inj₂ (d , lm)) (gate₁ H-gate) =
  (Hdir d ↓ᵏ n) , inj₂ (Hd' d , lm)
ract {₁₊ n} (inj₂ (d , lm)) (h ↥) =
  let (gs , lm') = ract lm h in gs ↑ , inj₂ (d , lm')
-- CZ on the bottom D box: two exposed D boxes reduce to DD-CZ; a single
-- exposed D box lets the L' below collapse.
ract {₁₊ ₀} (inj₂ (d , (([] , e) , ([] , a)))) (gate₂ CZ-gate) =
  dir-M , Push2.coset l'' m'
  where
  nt    = TDw.dir-of₂-No-Top-H (inj₂ ([] , a))
  pr    = TDw.push-D-w d (LCZ2.dir-of (inj₂ ([] , a))) nt
  e'    = pr .proj₁
  dir-M = pr .proj₂ .proj₁
  d'    = pr .proj₂ .proj₂
  m'    = (d' ∷ [] , e + - e')
  l''   = LCZ2.l'-of (inj₂ ([] , a))
ract {₁₊ (₁₊ n)} (inj₂ (d , inj₁ ml')) (gate₂ CZ-gate) = Push6.ract ml' d CZ-gate
ract {₁₊ (₁₊ n)} (inj₂ (d , inj₂ (d2 , lm2))) (gate₂ CZ-gate) =
  (DDCZ.dir-of (d ∷ d2 ∷ []) ↓ᵏ n) ,
    inj₂ ( (proj₁ d , proj₂ d + - proj₁ d2)
         , inj₂ ((proj₁ d2 , proj₂ d2 + - proj₁ d) , lm2) )

------------------------------------------------------------------------
-- Soundness of the coset action

[_]ᶜ = [_]ᵐˡ

-- ract-sound certifies the coset-table transition: for
-- (b' , c') = ract c g we have [ c ]ᶜ • [ g ]ʷ ≈ b' ↑ • [ c' ]ᶜ.
ract-sound : ∀ {n} c g →
  let
    open PB ((₁₊ n) QRel,_===_)
    (b' , c') = ract {n} c g
  in

    [ c ]ᶜ • [ g ]ʷ ≈ b' ↑ • [ c' ]ᶜ

-- Width 1: the bottom unary gate is absorbed by the A/E boxes.
ract-sound {₀} ml (gate₁ x) = Push.ract-sound ml x
-- inj₁: delegate to the ML'-level pushes (definitionally [ inj₁ ml' ]ᵐˡ = [ ml' ]ᵐˡ').
ract-sound {₁₊ n} (inj₁ ml') (gate₁ x) = Push.ract-sound ml' x
ract-sound {₁₊ n} (inj₁ ml') (gate₂ CZ-gate) = Push2.ract-sound ml' CZ-gate
ract-sound {₁₊ n} (inj₁ ml') (h ↥) = ML'T.lemma-ML'-Top ml' h
-- inj₂ + bottom unary: the wire-0 gate commutes past the lifted tail and
-- rewrites only the D box (dual of BR.Two.B-Top; bridged by ML'T.dbox-eq).
ract-sound {₁₊ n} (inj₂ (d , lm)) (gate₁ S-gate) = begin
  ([ d ]ᵈ • [ lm ]ᵐˡ ↑) • S                          ≈⟨ assoc ⟩
  [ d ]ᵈ • ([ lm ]ᵐˡ ↑ • S)                          ≈⟨ cright (sym (lemma-comm-S-w↑ [ lm ]ᵐˡ)) ⟩
  [ d ]ᵈ • (S • [ lm ]ᵐˡ ↑)                          ≈⟨ sym assoc ⟩
  ([ d ]ᵈ • S) • [ lm ]ᵐˡ ↑                          ≈⟨ cleft ds-step ⟩
  ((dir-of-DS d ↑) • [ d-of-DS d ]ᵈ) • [ lm ]ᵐˡ ↑    ≈⟨ assoc ⟩
  (dir-of-DS d ↑) • ([ d-of-DS d ]ᵈ • [ lm ]ᵐˡ ↑)    ∎
  where
  open PB ((₂₊ n) QRel,_===_) ; open PP ((₂₊ n) QRel,_===_) ; open SR word-setoid
  ds-step : [ d ]ᵈ • S ≈ (dir-of-DS d ↑) • [ d-of-DS d ]ᵈ
  ds-step = trans (cleft (refl' (ML'T.dbox-eq d)))
              (trans (aux-DS d)
                (cright (refl' (Eq.sym (ML'T.dbox-eq (d-of-DS d))))))
ract-sound {₁₊ n} (inj₂ (d , lm)) (gate₁ H-gate) = begin
  ([ d ]ᵈ • [ lm ]ᵐˡ ↑) • H                             ≈⟨ assoc ⟩
  [ d ]ᵈ • ([ lm ]ᵐˡ ↑ • H)                             ≈⟨ cright (sym (lemma-comm-H-w↑ [ lm ]ᵐˡ)) ⟩
  [ d ]ᵈ • (H • [ lm ]ᵐˡ ↑)                             ≈⟨ sym assoc ⟩
  ([ d ]ᵈ • H) • [ lm ]ᵐˡ ↑                             ≈⟨ cleft dh-step ⟩
  (((Hdir d ↓ᵏ n) ↑) • [ Hd' d ]ᵈ) • [ lm ]ᵐˡ ↑        ≈⟨ assoc ⟩
  ((Hdir d ↓ᵏ n) ↑) • ([ Hd' d ]ᵈ • [ lm ]ᵐˡ ↑)        ∎
  where
  open PB ((₂₊ n) QRel,_===_) ; open PP ((₂₊ n) QRel,_===_) ; open SR word-setoid
  dh-step : [ d ]ᵈ • H ≈ ((Hdir d ↓ᵏ n) ↑) • [ Hd' d ]ᵈ
  dh-step = trans (cleft (refl' (ML'T.dbox-eq d)))
              (trans (gen-DH-box d)
                (cright (refl' (Eq.sym (ML'T.dbox-eq (Hd' d))))))
-- inj₂ + lifted gate: recurse into the sub-ML, commute the D box past the
-- doubly-lifted escaped direction.
ract-sound {₁₊ n} (inj₂ (d , lm)) (h ↥) = begin
  ([ d ]ᵈ • [ lm ]ᵐˡ ↑) • [ h ↥ ]ʷ                   ≈⟨ assoc ⟩
  [ d ]ᵈ • ([ lm ]ᵐˡ ↑ • [ h ]ʷ ↑)                   ≈⟨ cright (lemma-cong↑ _ _ (ract-sound lm h)) ⟩
  [ d ]ᵈ • (gs ↑ ↑ • [ lm' ]ᵐˡ ↑)                    ≈⟨ sym assoc ⟩
  ([ d ]ᵈ • gs ↑ ↑) • [ lm' ]ᵐˡ ↑                    ≈⟨ cleft (ML'T.comm-dbox-w↑↑-S d gs) ⟩
  (gs ↑ ↑ • [ d ]ᵈ) • [ lm' ]ᵐˡ ↑                    ≈⟨ assoc ⟩
  gs ↑ ↑ • ([ d ]ᵈ • [ lm' ]ᵐˡ ↑)                    ∎
  where
  open PB ((₂₊ n) QRel,_===_) ; open PP ((₂₊ n) QRel,_===_) ; open SR word-setoid
  gs  = proj₁ (ract lm h)
  lm' = proj₂ (ract lm h)
-- CZ on the bottom D box.
ract-sound {₁₊ ₀} (inj₂ (d , (([] , e) , ([] , a)))) (gate₂ CZ-gate) = begin
  ([ d ]ᵈ • ([ e ]ᵉ • (ε • [ a ]ᵃ)) ↑) • CZ
    ≈⟨ cleft (sym assoc) ⟩
  ([ (d ∷ [] , e) ]ᵐ • (ε • [ a ]ᵃ) ↑) • CZ
    ≈⟨ cleft (cright abridge) ⟩
  ([ (d ∷ [] , e) ]ᵐ • LCZ2.intp (inj₂ ([] , a))) • CZ            ≈⟨ assoc ⟩
  [ (d ∷ [] , e) ]ᵐ • (LCZ2.intp (inj₂ ([] , a)) • CZ)           ≈⟨ cright (LCZ2.lemma-dir-and-l' (inj₂ ([] , a))) ⟩
  [ (d ∷ [] , e) ]ᵐ • (dir-L • LCZ2.intp l'')                    ≈⟨ sym assoc ⟩
  ([ (d ∷ [] , e) ]ᵐ • dir-L) • LCZ2.intp l''                    ≈⟨ cleft (cleft (refl' (mbox-eq (d ∷ [] , e)))) ⟩
  (LM.[ (d ∷ [] , e) ]ᵐ • dir-L) • LCZ2.intp l''                 ≈⟨ cleft (push-Mʷ2 d e dir-L nt) ⟩
  (dir-M ↑ • LM.[ m' ]ᵐ) • LCZ2.intp l''                        ≈⟨ assoc ⟩
  dir-M ↑ • (LM.[ m' ]ᵐ • LCZ2.intp l'')                        ≈⟨ cright (Push2.coset-eq l'' m') ⟩
  dir-M ↑ • [ Push2.coset l'' m' ]ᵐˡ ∎
  where
  open PB (2 QRel,_===_) ; open PP (2 QRel,_===_) ; open SR word-setoid
  nt    = TDw.dir-of₂-No-Top-H (inj₂ ([] , a))
  dir-L = LCZ2.dir-of (inj₂ ([] , a))
  l''   = LCZ2.l'-of (inj₂ ([] , a))
  pr    = TDw.push-D-w d dir-L nt
  e'    = pr .proj₁
  dir-M = pr .proj₂ .proj₁
  d'    = pr .proj₂ .proj₂
  m'    = (d' ∷ [] , e + - e')
  -- Section A box (lifted) bridged to LCZ2's L' 1 interpretation.
  abridge : (ε • [ a ]ᵃ) ↑ ≈ LCZ2.intp (inj₂ ([] , a))
  abridge = refl' (Eq.cong (λ z → (ε • z) ↑) (ML'T.abox-eq a))
ract-sound {₁₊ (₁₊ n)} (inj₂ (d , inj₁ ml')) (gate₂ CZ-gate) = Push6.ract-sound ml' d CZ-gate
ract-sound {₁₊ (₁₊ n)} (inj₂ (d , inj₂ (d2 , lm2))) (gate₂ CZ-gate) = begin
  ([ d ]ᵈ • ([ d2 ]ᵈ • [ lm2 ]ᵐˡ ↑) ↑) • CZ
    ≈⟨ cleft bridge-in ⟩
  (LM[ d ]ᵈ • (LM[ d2 ]ᵈ • [ lm2 ]ᵐˡ ↑) ↑) • CZ
    ≈⟨ gen-dd-cz-tail d d2 [ lm2 ]ᵐˡ ⟩
  ((DDCZ.dir-of (d ∷ d2 ∷ []) ↓ᵏ n) ↑) • (LM[ d1' ]ᵈ • (LM[ d2' ]ᵈ • [ lm2 ]ᵐˡ ↑) ↑)
    ≈⟨ cright bridge-out ⟩
  ((DDCZ.dir-of (d ∷ d2 ∷ []) ↓ᵏ n) ↑) • ([ d1' ]ᵈ • ([ d2' ]ᵈ • [ lm2 ]ᵐˡ ↑) ↑)
  ∎
  where
  open PB ((₃₊ n) QRel,_===_) ; open PP ((₃₊ n) QRel,_===_) ; open SR word-setoid
  d1' = (proj₁ d , proj₂ d + - proj₁ d2)
  d2' = (proj₁ d2 , proj₂ d2 + - proj₁ d)
  LM[_]ᵈ = LM.[_]ᵈ
  bridge-in : [ d ]ᵈ • ([ d2 ]ᵈ • [ lm2 ]ᵐˡ ↑) ↑ ≈ LM[ d ]ᵈ • (LM[ d2 ]ᵈ • [ lm2 ]ᵐˡ ↑) ↑
  bridge-in = refl' (Eq.cong₂ (λ x y → x • ((y • [ lm2 ]ᵐˡ ↑) ↑)) (ML'T.dbox-eq d) (ML'T.dbox-eq d2))
  bridge-out : LM[ d1' ]ᵈ • (LM[ d2' ]ᵈ • [ lm2 ]ᵐˡ ↑) ↑ ≈ [ d1' ]ᵈ • ([ d2' ]ᵈ • [ lm2 ]ᵐˡ ↑) ↑
  bridge-out = refl' (Eq.cong₂ (λ x y → x • ((y • [ lm2 ]ᵐˡ ↑) ↑))
                 (Eq.sym (ML'T.dbox-eq d1')) (Eq.sym (ML'T.dbox-eq d2')))

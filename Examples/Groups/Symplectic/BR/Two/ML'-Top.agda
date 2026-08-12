{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Pushing a top gate (g ↥, for any generator g) through an ML' box, at
-- width (₂₊ n).
--
-- ML' (₂₊ n) = M (₂₊ n) × L' (₂₊ n) = (Vec D (₁₊ n) × E) × (Vec B (₁₊ n) × A),
-- so an ML' (₂₊ n) box is
--
--   [ (d₀ ∷ dr , e) ]ᵐ • [ (b₀ ∷ lr , a) ]ˡ'
--     = ([ d₀ ]ᵈ • [ (dr,e) ]ᵐ ↑) • (([ lr ]ᵛᵇ ↑ • [ b₀ ]ᵇ) • [ a ]ᵃ).
--
-- For a unary gate the idea is BD-Top's (B-Top through the bottom B box,
-- then the bottom residual through the bottom D box), with the extra
-- commuting of the parts of the box disjoint from the moving gate/residual:
--
--   * [ a ]ᵃ (wire 0) vs the top gate            : comm-abox-w↑;
--   * the ↑-lifted M/L' tails [ (dr,e) ]ᵐ ↑ and [ lr ]ᵛᵇ ↑ (wires ≥ 1)
--     vs the bottom-wire residual dir-b ↓ᵏ (₁₊ n) : comm-↓ᵏ-w↑.
--
-- The Gen-2 pushes B-Top.lemma-B-br and BD-Top.lemmaᵈ-w are lifted to
-- Gen (₂₊ n) by CongDownK.cong↓ᵏ (widening) together with the box- and
-- ↓ᵏ-composition rewrites below.
--
-- The binary gate g = gate₂ CZ is handled by escaping CZ ↑ downward
-- through the B-vector (BB-CZ-n.gen-bb-cz), then pushing that bottom
-- residual up through the M-column (PushMword.push-Mʷ-suc); the two
-- pushes are bridged from LM-Sym to Section boxes by vbbox-eq / mbox-eq.
------------------------------------------------------------------------

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Data.Vec using (Vec ; [] ; _∷_)

import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Word.Base hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Data.Nat.Primality
open import Notations

module Examples.Groups.Symplectic.BR.Two.ML'-Top (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic hiding (M)
open Lemmas-Sym
open import Data.Empty using (⊥-elim)
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime as LM
open import Examples.Groups.Symplectic.Lemmas.Lemmas4-Sym p-2 p-prime
  using (comm-abox-w↑ ; comm-bbox-w↑↑ ; comm-dbox-w↑↑)
open import Examples.Groups.Symplectic.CongDownK p-2 p-prime
import Examples.Groups.Symplectic.BR.Two.B-Top p-2 p-prime as BT
import Examples.Groups.Symplectic.BR.Two.BD-Top p-2 p-prime as BD
open import Examples.Groups.Symplectic.BR.Three.BB-CZ-n p-2 p-prime
  using (gen-bb-cz ; gen-dir-b ; gen-vb'-of)
open import Examples.Groups.Symplectic.Normalization.Pushing.PushMword p-2 p-prime
  using (push-Mʷ-suc)

-- Section's A/B/D boxes are (byte-)identical to LM-Sym's, but distinct
-- functions; these bridges (refl after splitting the argument) let us
-- reuse the LM-Sym-based B-Top / BD-Top / comm-abox-w↑ against Section's
-- boxes.
abox-eq : ∀ {n} (a : A) → [_]ᵃ {n} a ≡ LM.[_]ᵃ {n} a
abox-eq ((₀ , ₀) , pr)    = ⊥-elim (pr auto)
abox-eq ((₀ , ₁₊ b) , pr) = Eq.refl
abox-eq ((₁₊ a , b) , pr) = Eq.refl

bbox-eq : ∀ {n} (b : B) → [_]ᵇ {n} b ≡ LM.[_]ᵇ {n} b
bbox-eq (₀ , b)    = Eq.refl
bbox-eq (₁₊ a , b) = Eq.refl

dbox-eq : ∀ {n} (d : D) → [_]ᵈ {n} d ≡ LM.[_]ᵈ {n} d
dbox-eq (₀ , b)    = Eq.refl
dbox-eq (₁₊ a , b) = Eq.refl

-- The vector / M-column boxes are folds over the per-box boxes, so the
-- box-eq bridges lift through them by induction.
vbbox-eq : ∀ {n} (bv : Vec B n) → [ bv ]ᵛᵇ ≡ LM.[ bv ]ᵛᵇ
vbbox-eq []       = Eq.refl
vbbox-eq (x ∷ bv) = Eq.cong₂ _•_ (Eq.cong _↑ (vbbox-eq bv)) (bbox-eq x)

mbox-eq : ∀ {n} (m : M n) → [ m ]ᵐ ≡ LM.[ m ]ᵐ
mbox-eq {0}     _            = Eq.refl
mbox-eq {₁₊ n} ([] , e)      = Eq.refl
mbox-eq {₁₊ n} (x ∷ vd , e)  = Eq.cong₂ _•_ (dbox-eq x) (Eq.cong _↑ (mbox-eq (vd , e)))

------------------------------------------------------------------------
-- Box-widening: a Gen-2 box, widened by ↓ᵏ k, is the width-k box.

CX'^-↓ᵏ : ∀ {n} (b : ℤ ₚ) (k : ℕ) → (CX'^ {n} b) ↓ᵏ k ≡ CX'^ b
CX'^-↓ᵏ b k = Eq.cong₂ _•_ (pow-↓ᵏ H 3 k) (Eq.cong₂ _•_ (CZ^-↓ᵏ b k) Eq.refl)

S^↑-↓ᵏ : ∀ {n} (j : ℤ ₚ) (k : ℕ) → (S^ {n} j ↑) ↓ᵏ k ≡ S^ j ↑
S^↑-↓ᵏ j k = Eq.trans (↑↓ᵏ-comm (S^ j) k) (Eq.cong _↑ (S^-↓ᵏ j k))

bbox-↓ᵏ : ∀ (b : B) (k : ℕ) → (LM.[_]ᵇ {0} b ↓ᵏ k) ≡ [_]ᵇ {k} b
bbox-↓ᵏ (₀ , b) k = Eq.cong₂ _•_ Eq.refl (CX'^-↓ᵏ b k)
bbox-↓ᵏ (a@(₁₊ a-1) , b) k =
  Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_ (CX'^-↓ᵏ a k) (Eq.cong₂ _•_ Eq.refl (S^↑-↓ᵏ -b/a k)))
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹

dbox-↓ᵏ : ∀ (d : D) (k : ℕ) → (LM.[_]ᵈ {0} d ↓ᵏ k) ≡ [_]ᵈ {k} d
dbox-↓ᵏ (₀ , b) k = Eq.cong₂ _•_ Eq.refl (CZ^-↓ᵏ (- b) k)
dbox-↓ᵏ (a@(₁₊ a-1) , b) k =
  Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_ (CZ^-↓ᵏ (- a) k) (Eq.cong₂ _•_ Eq.refl (S^-↓ᵏ -b/a k)))
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  -b/a = - b * a⁻¹

------------------------------------------------------------------------
-- The width-(₂₊ n) lemmas.

module _ {n : ℕ} where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc renaming (by-passoc to sa)

  -- A bottom-wire Gen-1 word (padded to wire 0 by ↓ᵏ (₁₊ n)) commutes
  -- with any wire-≥1 lifted word.
  comm-↓ᵏ-w↑ : ∀ (u : Word (Gen 1)) (w : Word (Gen (₁₊ n))) →
    (u ↓ᵏ (₁₊ n)) • (w ↑) ≈ (w ↑) • (u ↓ᵏ (₁₊ n))
  -- comm-abox-w↑ / comm-{b,d}box-w↑↑ transported to Section's boxes.
  comm-abox-w↑-S : ∀ (a : A) (w : Word (Gen (₁₊ n))) → [ a ]ᵃ • (w ↑) ≈ (w ↑) • [ a ]ᵃ
  comm-abox-w↑-S a w =
    Eq.subst (λ z → z • (w ↑) ≈ (w ↑) • z) (Eq.sym (abox-eq a)) (comm-abox-w↑ a w)

  comm-bbox-w↑↑-S : ∀ (b : B) (w : Word (Gen n)) → [ b ]ᵇ • (w ↑ ↑) ≈ (w ↑ ↑) • [ b ]ᵇ
  comm-bbox-w↑↑-S b w =
    Eq.subst (λ z → z • (w ↑ ↑) ≈ (w ↑ ↑) • z) (Eq.sym (bbox-eq b)) (comm-bbox-w↑↑ b w)

  comm-dbox-w↑↑-S : ∀ (d : D) (w : Word (Gen n)) → [ d ]ᵈ • (w ↑ ↑) ≈ (w ↑ ↑) • [ d ]ᵈ
  comm-dbox-w↑↑-S d w =
    Eq.subst (λ z → z • (w ↑ ↑) ≈ (w ↑ ↑) • z) (Eq.sym (dbox-eq d)) (comm-dbox-w↑↑ d w)

  comm-↓ᵏ-w↑ [ gate₁ H-gate ]ʷ w = lemma-comm-H-w↑ w
  comm-↓ᵏ-w↑ [ gate₁ S-gate ]ʷ w = lemma-comm-S-w↑ w
  comm-↓ᵏ-w↑ [ gate₀ () ↥ ]ʷ w
  comm-↓ᵏ-w↑ ε             w = trans left-unit (sym right-unit)
  comm-↓ᵏ-w↑ (u • v)       w = begin
    ((u ↓ᵏ (₁₊ n)) • (v ↓ᵏ (₁₊ n))) • (w ↑)   ≈⟨ assoc ⟩
    (u ↓ᵏ (₁₊ n)) • ((v ↓ᵏ (₁₊ n)) • (w ↑))   ≈⟨ cright (comm-↓ᵏ-w↑ v w) ⟩
    (u ↓ᵏ (₁₊ n)) • ((w ↑) • (v ↓ᵏ (₁₊ n)))   ≈⟨ sym assoc ⟩
    ((u ↓ᵏ (₁₊ n)) • (w ↑)) • (v ↓ᵏ (₁₊ n))   ≈⟨ cleft (comm-↓ᵏ-w↑ u w) ⟩
    ((w ↑) • (u ↓ᵏ (₁₊ n))) • (v ↓ᵏ (₁₊ n))   ≈⟨ assoc ⟩
    (w ↑) • ((u ↓ᵏ (₁₊ n)) • (v ↓ᵏ (₁₊ n)))   ∎

  -- B-Top widened to Gen (₂₊ n).
  lemma-B-br-n : ∀ (b : B) (x₁ : SympGate 1) →
    [_]ᵇ {n} b • [ gate₁ x₁ ↥ ]ʷ ≈ (BT.dir-of b x₁ ↓ᵏ (₁₊ n)) • [_]ᵇ {n} (BT.b'-of b x₁)
  lemma-B-br-n b x₁ =
    trans (refl' (Eq.cong₂ _•_ (Eq.sym (bbox-↓ᵏ b n)) Eq.refl))
      (trans (cong↓ᵏ n _ _ (BT.lemma-B-br b x₁))
        (refl' (Eq.cong₂ _•_ (↓ᵏ-↓ᵏ-1 (BT.dir-of b x₁) n) (bbox-↓ᵏ (BT.b'-of b x₁) n))))

  -- BD-Top's word-level D push, widened to Gen (₂₊ n).
  lemmaᵈ-w-n : ∀ (d : D) (w : Word (Gen 1)) →
    [_]ᵈ {n} d • (w ↓ᵏ (₁₊ n)) ≈
      ((proj₁ (BD.pushᵈ d w) ↓ᵏ n) ↑) • [_]ᵈ {n} (proj₂ (BD.pushᵈ d w))
  lemmaᵈ-w-n d w =
    trans (refl' (Eq.cong₂ _•_ (Eq.sym (dbox-↓ᵏ d n)) (Eq.sym (↓ᵏ-↓ᵏ-1 w n))))
      (trans (cong↓ᵏ n _ _ (BD.lemmaᵈ-w d w))
        (refl' (Eq.cong₂ _•_ (↑↓ᵏ-comm (proj₁ (BD.pushᵈ d w)) n) (dbox-↓ᵏ (proj₂ (BD.pushᵈ d w)) n))))

------------------------------------------------------------------------
-- Pushing any generator through an M-column · B-vector (no trailing A).
-- This is the shape the higher-wire recursion factors through; unlike
-- ML', it recurses cleanly (a unary gate commutes past d₁ and b₁; a
-- gate₂ CZ escapes downward via gen-bb-cz + push-Mʷ-suc).

mbv-push : ∀ {k} (m : M (₁₊ k)) (bv : Vec B k) (g : Gen k) →
  Word (Gen k) × (M (₁₊ k) × Vec B k)
-- The gate₂ clause is placed first so that `mbv-push m bv (gate₂ …)`
-- reduces even when the M-column / B-vector are abstract: its first
-- pattern is a plain pair (never stuck on a `∷`), unlike the unary
-- clauses which peel a bottom box.
mbv-push (vd , e) bv (gate₂ CZ-gate) =
  let pm = push-Mʷ-suc (vd , e) (gen-dir-b bv)
  in proj₁ pm , (proj₁ (proj₂ pm) , gen-vb'-of bv)
mbv-push {₁₊ k'} (d₁ ∷ dr' , e) (b₁ ∷ bv') (gate₁ y) =
  proj₁ (BD.pushᵈ d₁ (BT.dir-of b₁ y)) ↓ᵏ k' ,
    ((proj₂ (BD.pushᵈ d₁ (BT.dir-of b₁ y)) ∷ dr' , e) , (BT.b'-of b₁ y ∷ bv'))
mbv-push (d₁ ∷ dr' , e) (b₁ ∷ bv') (h ↥) =
  let (dt , ((dvt , et) , bvt)) = mbv-push (dr' , e) bv' h
  in dt ↑ , ((d₁ ∷ dvt , et) , (b₁ ∷ bvt))

push-MBvec : ∀ {k} (m : M (₁₊ k)) (bv : Vec B k) (g : Gen k) →
  let open PB ((₁₊ k) QRel,_===_) in
  [ m ]ᵐ • [ bv ]ᵛᵇ • [ g ↥ ]ʷ ≈
    (proj₁ (mbv-push m bv g) ↑) •
      ([ proj₁ (proj₂ (mbv-push m bv g)) ]ᵐ • [ proj₂ (proj₂ (mbv-push m bv g)) ]ᵛᵇ)
push-MBvec ([] , _) bv (gate₀ ())
push-MBvec {₁₊ k'} (d₁ ∷ dr' , e) (b₁ ∷ bv') (gate₁ y) = begin
  (De • Me) • ((LRe • Be) • G)          ≈⟨ sa ((□ • □) • ((□ • □) • □)) (□ ^ 5) auto ⟩
  De • (Me • (LRe • (Be • G)))          ≈⟨ cright (cright (cright (lemma-B-br-n b₁ y))) ⟩
  De • (Me • (LRe • (db • Be')))        ≈⟨ cright (cright (sym assoc)) ⟩
  De • (Me • ((LRe • db) • Be'))        ≈⟨ cright (cright (cleft (sym (comm-↓ᵏ-w↑ dir-b LRw)))) ⟩
  De • (Me • ((db • LRe) • Be'))        ≈⟨ cright (cright assoc) ⟩
  De • (Me • (db • (LRe • Be')))        ≈⟨ cright (sym assoc) ⟩
  De • ((Me • db) • (LRe • Be'))        ≈⟨ cright (cleft (sym (comm-↓ᵏ-w↑ dir-b Mw))) ⟩
  De • ((db • Me) • (LRe • Be'))        ≈⟨ sa (□ • ((□ • □) • (□ • □))) ((□ • □) • (□ • (□ • □))) auto ⟩
  (De • db) • (Me • (LRe • Be'))        ≈⟨ cleft (lemmaᵈ-w-n d₁ dir-b) ⟩
  (Res • De') • (Me • (LRe • Be'))      ≈⟨ sa ((□ • □) • (□ • (□ • □))) (□ • ((□ • □) • (□ • □))) auto ⟩
  Res • ((De' • Me) • (LRe • Be'))      ∎
  where
  open PB ((₂₊ k') QRel,_===_) ; open PP ((₂₊ k') QRel,_===_) ; open SR word-setoid
  open Pattern-Assoc renaming (by-passoc to sa)
  De = [ d₁ ]ᵈ
  Mw = [ (dr' , e) ]ᵐ
  Me = Mw ↑
  LRw = [ bv' ]ᵛᵇ
  LRe = LRw ↑
  Be = [ b₁ ]ᵇ
  G = [ gate₁ y ↥ ]ʷ
  dir-b = BT.dir-of b₁ y
  db = dir-b ↓ᵏ (₁₊ k')
  Be' = [ BT.b'-of b₁ y ]ᵇ
  r = BD.pushᵈ d₁ dir-b
  De' = [ proj₂ r ]ᵈ
  Res = (proj₁ r ↓ᵏ k') ↑
push-MBvec {₂₊ k''} (vd , e) bv (gate₂ CZ-gate) = begin
  Mw • (Bv • G)                         ≈⟨ cright bb-step ⟩
  Mw • (db • Bv')                       ≈⟨ sym assoc ⟩
  (Mw • db) • Bv'                       ≈⟨ cleft m-step ⟩
  ((dir ↑) • Mw') • Bv'                 ≈⟨ assoc ⟩
  (dir ↑) • (Mw' • Bv')                 ∎
  where
  open PB ((₃₊ k'') QRel,_===_) ; open PP ((₃₊ k'') QRel,_===_) ; open SR word-setoid
  Mw = [ (vd , e) ]ᵐ
  Bv = [ bv ]ᵛᵇ
  G = [ gate₂ CZ-gate ↥ ]ʷ
  dir-b = gen-dir-b bv
  db = dir-b ↓ᵏ (₁₊ k'')
  Bv' = [ gen-vb'-of bv ]ᵛᵇ
  pm = push-Mʷ-suc (vd , e) dir-b
  dir = proj₁ pm
  Mw' = [ proj₁ (proj₂ pm) ]ᵐ
  -- CZ↑ through the B-vector (gen-bb-cz), bridged Section ↔ LM-Sym.
  bb-step : Bv • G ≈ db • Bv'
  bb-step = trans (cleft (refl' (vbbox-eq bv)))
              (trans (gen-bb-cz bv)
                (cright (refl' (Eq.sym (vbbox-eq (gen-vb'-of bv))))))
  -- the escaping bottom direction pushed up through the M-column
  -- (push-Mʷ-suc), bridged Section ↔ LM-Sym.
  m-step : Mw • db ≈ (dir ↑) • Mw'
  m-step = trans (cleft (refl' (mbox-eq (vd , e))))
             (trans (proj₂ (proj₂ pm))
               (cright (refl' (Eq.sym (mbox-eq (proj₁ (proj₂ pm)))))))
push-MBvec {₁₊ k'} (d₁ ∷ dr' , e) (b₁ ∷ bv') (h ↥) = begin
  (De • Me) • ((LRe • Be) • G)          ≈⟨ sa ((□ • □) • ((□ • □) • □)) (□ ^ 5) auto ⟩
  De • (Me • (LRe • (Be • G)))          ≈⟨ cright (cright (cright (comm-bbox-w↑↑-S b₁ w))) ⟩
  De • (Me • (LRe • (G • Be)))          ≈⟨ cright (cright (sym assoc)) ⟩
  De • (Me • ((LRe • G) • Be))          ≈⟨ cright (sym assoc) ⟩
  De • ((Me • (LRe • G)) • Be)          ≈⟨ cright (cleft (lemma-cong↑ _ _ (push-MBvec (dr' , e) bv' h))) ⟩
  De • ((dt↑↑ • (Me'' • LRe'')) • Be)    ≈⟨ sa (□ • ((□ • (□ • □)) • □)) ((□ • □) • ((□ • □) • □)) auto ⟩
  (De • dt↑↑) • ((Me'' • LRe'') • Be)    ≈⟨ cleft (comm-dbox-w↑↑-S d₁ dt) ⟩
  (dt↑↑ • De) • ((Me'' • LRe'') • Be)    ≈⟨ sa ((□ • □) • ((□ • □) • □)) (□ • ((□ • □) • (□ • □))) auto ⟩
  dt↑↑ • ((De • Me'') • (LRe'' • Be))    ∎
  where
  open PB ((₂₊ k') QRel,_===_) ; open PP ((₂₊ k') QRel,_===_) ; open SR word-setoid
  open Pattern-Assoc renaming (by-passoc to sa)
  De = [ d₁ ]ᵈ
  Me = [ (dr' , e) ]ᵐ ↑
  LRe = [ bv' ]ᵛᵇ ↑
  Be = [ b₁ ]ᵇ
  w = [ h ]ʷ
  G = [ h ↥ ↥ ]ʷ
  td = mbv-push (dr' , e) bv' h
  dt = proj₁ td
  dt↑↑ = dt ↑ ↑
  Me'' = [ proj₁ (proj₂ td) ]ᵐ ↑
  LRe'' = [ proj₂ (proj₂ td) ]ᵛᵇ ↑

------------------------------------------------------------------------
-- The ML' push for any generator g ↥: commute the trailing A box out,
-- push through the M·B-vector, put the A box back.

ml'-of : ∀ {n} (ml : ML' (₂₊ n)) (g : Gen (₁₊ n)) → ML' (₂₊ n)
ml'-of ((dv , e) , (bv , a)) g =
  let (dir , (m' , bv')) = mbv-push (dv , e) bv g in (m' , (bv' , a))

dir-of : ∀ {n} (ml : ML' (₂₊ n)) (g : Gen (₁₊ n)) → Word (Gen (₁₊ n))
dir-of ((dv , e) , (bv , a)) g = proj₁ (mbv-push (dv , e) bv g)

lemma-ML'-Top : ∀ {n} (ml : ML' (₂₊ n)) (g : Gen (₁₊ n)) →
  let
  open PB ((₂₊ n) QRel,_===_)
  ml' = ml'-of ml g
  dir = dir-of ml g
  in
  [ ml ]ᵐˡ' • [ g ↥ ]ʷ ≈ dir ↑ • [ ml' ]ᵐˡ'
lemma-ML'-Top {n} ((dv , e) , (bv , a)) g = begin
  (Mw • (Bv • Ae)) • G                        ≈⟨ assoc ⟩
  Mw • ((Bv • Ae) • G)                        ≈⟨ cright assoc ⟩
  Mw • (Bv • (Ae • G))                        ≈⟨ cright (cright (comm-abox-w↑-S a [ g ]ʷ)) ⟩
  Mw • (Bv • (G • Ae))                        ≈⟨ cright (sym assoc) ⟩
  Mw • ((Bv • G) • Ae)                        ≈⟨ sym assoc ⟩
  (Mw • (Bv • G)) • Ae                        ≈⟨ cleft (push-MBvec (dv , e) bv g) ⟩
  ((dir ↑) • (Mw' • Bv')) • Ae                ≈⟨ assoc ⟩
  (dir ↑) • ((Mw' • Bv') • Ae)                ≈⟨ cright assoc ⟩
  (dir ↑) • (Mw' • (Bv' • Ae))                ∎
  where
  open PB ((₂₊ n) QRel,_===_) ; open PP ((₂₊ n) QRel,_===_) ; open SR word-setoid
  Mw = [ (dv , e) ]ᵐ
  Bv = [ bv ]ᵛᵇ
  Ae = [ a ]ᵃ
  G = [ g ↥ ]ʷ
  dir = proj₁ (mbv-push (dv , e) bv g)
  Mw' = [ proj₁ (proj₂ (mbv-push (dv , e) bv g)) ]ᵐ
  Bv' = [ proj₂ (proj₂ (mbv-push (dv , e) bv g)) ]ᵛᵇ

------------------------------------------------------------------------
-- The original ML' (₂₊ n) top-gate push is the wire-1 (gate₁) instance.

lemma-ML'-Top-eg1 : ∀ {n} (d₀ : D) (dr : Vec D n) (e : E) (b₀ : B) (lr : Vec B n) (a : A)
  (x₁ : SympGate 1) →
  let
  open PB ((₂₊ n) QRel,_===_)
  r = BD.pushᵈ d₀ (BT.dir-of b₀ x₁)
  in
  ([ (d₀ ∷ dr , e) ]ᵐ • [ (b₀ ∷ lr , a) ]ˡ') • [ gate₁ x₁ ↥ ]ʷ ≈
    ((proj₁ r ↓ᵏ n) ↑) • ([ (proj₂ r ∷ dr , e) ]ᵐ • [ (BT.b'-of b₀ x₁ ∷ lr , a) ]ˡ')
lemma-ML'-Top-eg1 d₀ dr e b₀ lr a x₁ =
  lemma-ML'-Top ((d₀ ∷ dr , e) , (b₀ ∷ lr , a)) (gate₁ x₁)

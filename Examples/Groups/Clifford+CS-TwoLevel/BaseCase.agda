------------------------------------------------------------------------
-- Presentations of groups
--
-- The base case of Lemma 3.5: the basic edges out of I.
--
-- For a basic generator G, the synthesis algorithm run on G·I removes
-- G in one syllable: i_[0] gives the syllable i_[0]³, X_[α,α+1] gives
-- X_[α,α+1], and K_[0,1] gives K†_[0,1].  So the syllable cancels G
-- relationally, and the edge G out of I closes (edge-𝕀).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.Clifford+CS-TwoLevel.BaseCase {n : ℕ} where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; _<_ ; toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+CS-TwoLevel.Ring
open import Examples.Groups.Clifford+CS-TwoLevel.Scale
open import Examples.Groups.Clifford+CS-TwoLevel.Lde using (scV ; scV-! ; lde ; num ; lde-char ; Odd)
open import Examples.Groups.Clifford+CS-TwoLevel.Column
open import Examples.Groups.Clifford+CS-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics
open import Examples.Groups.Clifford+CS-TwoLevel.Pivot using (pivot ; pivot-char ; Beyond)
open import Examples.Groups.Clifford+CS-TwoLevel.Syllable
  using (syl ; syl-just ; step ; top ; Beyond-actM ; eᶻ ; eᶻ-! ; δᶻ-refl ; δᶻ-≢ ; col𝕀≡)
open import Examples.Groups.Clifford+CS-TwoLevel.Synthesis using (synth-step)
open import Examples.Groups.Clifford+CS-TwoLevel.Derived {n} using (i³-i ; X-X ; K†-K)
open import Examples.Groups.Clifford+CS-TwoLevel.Basic {n} using (IsBasic ; bX ; bK ; bi)
open import Examples.Groups.Clifford+CS-TwoLevel.Reduction {n} using (nw ; nw-cong ; Path ; sound-act ; Base)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

------------------------------------------------------------------------
-- If the syllable of G·I cancels G, the edge G out of I closes

edge-𝕀 : (G : Gen n) {p : Fin n} → pivot (actM G 𝕀) ≡ just p → syl (actM G 𝕀) • [ G ]ʷ ≈ ε →
         Path [ G ]ʷ 𝕀 ColOrth-𝕀
edge-𝕀 G pv rel = begin
  nw (actM G 𝕀) (ColOrth-actMʷ [ G ]ʷ ColOrth-𝕀) • [ G ]ʷ
    ≈⟨ cleft refl′ (synth-step (actM G 𝕀) (ColOrth-actMʷ [ G ]ʷ ColOrth-𝕀) pv) ⟩
  (nw (step (actM G 𝕀)) (ColOrth-actMʷ (syl (actM G 𝕀) • [ G ]ʷ) ColOrth-𝕀) • syl (actM G 𝕀)) • [ G ]ʷ
    ≈⟨ assoc ⟩
  nw (step (actM G 𝕀)) (ColOrth-actMʷ (syl (actM G 𝕀) • [ G ]ʷ) ColOrth-𝕀) • (syl (actM G 𝕀) • [ G ]ʷ)
    ≈⟨ cright rel ⟩
  nw (step (actM G 𝕀)) (ColOrth-actMʷ (syl (actM G 𝕀) • [ G ]ʷ) ColOrth-𝕀) • ε
    ≈⟨ right-unit ⟩
  nw (step (actM G 𝕀)) (ColOrth-actMʷ (syl (actM G 𝕀) • [ G ]ʷ) ColOrth-𝕀)
    ≈⟨ refl′ (nw-cong (sound-act rel 𝕀) (ColOrth-actMʷ (syl (actM G 𝕀) • [ G ]ʷ) ColOrth-𝕀) ColOrth-𝕀) ⟩
  nw 𝕀 ColOrth-𝕀
    ∎

------------------------------------------------------------------------
-- Columns of g·I

private
  col-gI : (g : Gen n) (c : Fin n) → col (actM g 𝕀) c ≡ actV g (scV 0 (eᶻ c))
  col-gI g c = ≡.trans (col-actM g 𝕀 c) (≡.cong (actV g) (col𝕀≡ c))

  scV-inj : ∀ k (u v : Vec Z n) → scV k u ≡ scV k v → u ≡ v
  scV-inj k u v eq = vec-ext λ x →
    sc-injective k (≡.trans (≡.sym (scV-! k u x)) (≡.trans (≡.cong (_! x) eq) (scV-! k v x)))

  e-a : (a : Fin n) → eᶻ a ! a ≡ ZR.1#
  e-a a = ≡.trans (eᶻ-! a a) (δᶻ-refl a)

  e-≢ : {a x : Fin n} → x ≢ a → eᶻ a ! x ≡ ZR.0#
  e-≢ {a} {x} x≢a = ≡.trans (eᶻ-! a x) (δᶻ-≢ x≢a)

  -- Nothing lies below index 0.
  none<0 : {x a : Fin n} → toℕ a ≡ 0 → x < a → ⊥
  none<0 {x} a0 x<a = ℕP.n≮0 (≡.subst (toℕ x ℕ.<_) a0 x<a)

  1≢0 : ZR.1# ≢ ZR.0#
  1≢0 ()

  ⅈ≢1 : ⅈᶻ ≢ ZR.1#
  ⅈ≢1 ()

------------------------------------------------------------------------
-- i_[0]: the syllable is i_[0]³

module Case-i (a : Fin n) (a0 : toℕ a ≡ 0) where

  private
    M = actM (i-gen a) 𝕀

    w : Vec Z n
    w = iᶻ a (eᶻ a)

    col≡ : col M a ≡ scV 0 w
    col≡ = ≡.trans (col-gI (i-gen a) a) (actV-i a 0 (eᶻ a))

    w-a : w ! a ≡ ⅈᶻ
    w-a = ≡.trans (set₁-a a (ⅈᶻ ZR.* (eᶻ a ! a)) (eᶻ a))
                  (≡.trans (≡.cong (ⅈᶻ ZR.*_) (e-a a)) (ZR.*-identityʳ ⅈᶻ))

    ln : lde (col M a) ≡ 0 × num (col M a) ≡ w
    ln = lde-char 0 w col≡ (inj₁ ≡.refl)

    ne : col M a ≢ col 𝕀 a
    ne eq = ⅈ≢1 (≡.trans (≡.sym w-a) (≡.trans (≡.cong (_! a) w≡e) (e-a a)))
      where
      w≡e : w ≡ eᶻ a
      w≡e = scV-inj 0 w (eᶻ a) (≡.trans (≡.sym col≡) (≡.trans eq (col𝕀≡ a)))

    pv : pivot M ≡ just a
    pv = pivot-char M ne (Beyond-actM (i-gen a) {M = 𝕀} FinP.≤-refl (λ c _ → ≡.refl))

    fo : firstOdd w ≡ just a
    fo = firstOdd-char w (≡.cong oddᶻ w-a) (λ x x<a → ⊥-elim (none<0 a0 x<a))

    syl≡ : syl M ≡ i a ^ 3
    syl≡ = ≡.trans (syl-just M pv)
             (≡.trans (≡.cong₂ (sylData a) (proj₁ ln) (proj₂ ln))
               (≡.trans (sylData-unit≡ w fo) (≡.cong (λ z → i a ^ invExp z) w-a)))

  edge : Path (i a) 𝕀 ColOrth-𝕀
  edge = edge-𝕀 (i-gen a) pv (trans (cleft refl′ syl≡) i³-i)

------------------------------------------------------------------------
-- X_[α,α+1]: the syllable is X_[α,α+1]

module Case-X (a b : Fin n) (ab : toℕ b ≡ suc (toℕ a)) where

  a<b : a < b
  a<b = ≡.subst (toℕ a ℕ.<_) (≡.sym ab) ℕP.≤-refl

  private
    a≢b : a ≢ b
    a≢b = <⇒≢ a<b

    M = actM (X-gen a b a<b) 𝕀

    w : Vec Z n
    w = Xᶻ a b (eᶻ b)

    col≡ : col M b ≡ scV 0 w
    col≡ = ≡.trans (col-gI (X-gen a b a<b) b) (actV-X a b a<b 0 (eᶻ b))

    w-a : w ! a ≡ ZR.1#
    w-a = ≡.trans (set₂-a a b (eᶻ b ! b) (eᶻ b ! a) (eᶻ b)) (e-a b)

    w-b : w ! b ≡ ZR.0#
    w-b = ≡.trans (set₂-b a b (eᶻ b ! b) (eᶻ b ! a) (eᶻ b) a≢b) (e-≢ a≢b)

    w-≢ : ∀ {x} → x ≢ a → x ≢ b → w ! x ≡ ZR.0#
    w-≢ {x} xa xb = ≡.trans (set₂-≢ a b (eᶻ b ! b) (eᶻ b ! a) (eᶻ b) xa xb) (e-≢ xb)

    ln : lde (col M b) ≡ 0 × num (col M b) ≡ w
    ln = lde-char 0 w col≡ (inj₁ ≡.refl)

    ne : col M b ≢ col 𝕀 b
    ne eq = 1≢0 (≡.trans (≡.sym (e-a b)) (≡.trans (≡.cong (_! b) (≡.sym w≡e)) w-b))
      where
      w≡e : w ≡ eᶻ b
      w≡e = scV-inj 0 w (eᶻ b) (≡.trans (≡.sym col≡) (≡.trans eq (col𝕀≡ b)))

    pv : pivot M ≡ just b
    pv = pivot-char M ne (Beyond-actM (X-gen a b a<b) {M = 𝕀} FinP.≤-refl (λ c _ → ≡.refl))

    fo : firstOdd w ≡ just a
    fo = firstOdd-char w (≡.cong oddᶻ w-a)
           (λ x x<a → ≡.cong oddᶻ (w-≢ (<⇒≢ x<a) (<⇒≢ (FinP.<-trans x<a a<b))))

    syl≡ : syl M ≡ X a b a<b • i a ^ 0
    syl≡ = ≡.trans (syl-just M pv)
             (≡.trans (≡.cong₂ (sylData b) (proj₁ ln) (proj₂ ln))
               (≡.trans (sylData-unit< w fo a<b) (≡.cong (λ z → X a b a<b • i a ^ invExp z) w-a)))

  edge : Path (X a b a<b) 𝕀 ColOrth-𝕀
  edge = edge-𝕀 (X-gen a b a<b) pv (trans (cleft refl′ syl≡) (trans (cleft right-unit) (X-X a<b)))

------------------------------------------------------------------------
-- K_[0,1]: the syllable is K†_[0,1]

module Case-K (a b : Fin n) (a0 : toℕ a ≡ 0) (b1 : toℕ b ≡ 1) where

  a<b : a < b
  a<b = ≡.subst₂ ℕ._<_ (≡.sym a0) (≡.sym b1) (ℕ.s≤s ℕ.z≤n)

  private
    a≢b : a ≢ b
    a≢b = <⇒≢ a<b

    M = actM (K-gen a b a<b) 𝕀

    w : Vec Z n
    w = Kᶻ a b (eᶻ b)

    col≡ : col M b ≡ scV 1 w
    col≡ = ≡.trans (col-gI (K-gen a b a<b) b) (actV-K a b a<b 0 (eᶻ b))

    w-a : w ! a ≡ ZR.1#
    w-a = ≡.trans (set₂-a a b (eᶻ b ! a ZR.+ eᶻ b ! b) (eᶻ b ! a ZR.- eᶻ b ! b) (Vec.map (γᶻ ZR.*_) (eᶻ b)))
                  (≡.trans (≡.cong₂ ZR._+_ (e-≢ a≢b) (e-a b)) (ZR.+-identityˡ ZR.1#))

    w-b : w ! b ≡ ZR.- ZR.1#
    w-b = ≡.trans (set₂-b a b (eᶻ b ! a ZR.+ eᶻ b ! b) (eᶻ b ! a ZR.- eᶻ b ! b) (Vec.map (γᶻ ZR.*_) (eᶻ b)) a≢b)
                  (≡.trans (≡.cong₂ ZR._-_ (e-≢ a≢b) (e-a b)) (ZR.+-identityˡ (ZR.- ZR.1#)))

    ln : lde (col M b) ≡ 1 × num (col M b) ≡ w
    ln = lde-char 1 w col≡ (inj₂ (a , ≡.cong oddᶻ w-a))

    -- Entry a of column b is γ⁻¹, not 0.
    ne : col M b ≢ col 𝕀 b
    ne eq = 1≢0 (sc-injective 1 (≡.trans chain (≡.sym (sc-0 1))))
      where
      chain : sc 1 ZR.1# ≡ DR.0#
      chain = ≡.trans (≡.cong (sc 1) (≡.sym w-a))
                (≡.trans (≡.sym (scV-! 1 w a))
                  (≡.trans (≡.cong (_! a) (≡.sym col≡))
                    (≡.trans (≡.cong (_! a) eq)
                      (≡.trans (≡.cong (_! a) (col𝕀≡ b))
                        (≡.trans (scV-! 0 (eᶻ b) a)
                          (≡.trans (≡.cong (sc 0) (e-≢ a≢b)) (sc-0 0)))))))

    pv : pivot M ≡ just b
    pv = pivot-char M ne (Beyond-actM (K-gen a b a<b) {M = 𝕀} FinP.≤-refl (λ c _ → ≡.refl))

    fo : firstOdd w ≡ just a
    fo = firstOdd-char w (≡.cong oddᶻ w-a) (λ x x<a → ⊥-elim (none<0 a0 x<a))

    -- Nothing lies strictly between 0 and 1.
    between : ∀ {x : Fin n} → a < x → x < b → ⊥
    between {x} a<x x<b = ℕP.<-irrefl ≡.refl
      (ℕP.<-≤-trans (≡.subst (ℕ._< toℕ x) a0 a<x) (ℕP.≤-pred (≡.subst (toℕ x ℕ.<_) b1 x<b)))

    nx : nextOdd a w ≡ just b
    nx = nextOdd-char w a<b (≡.cong oddᶻ w-b) (λ x a<x x<b → ⊥-elim (between a<x x<b))

    syl≡ : syl M ≡ K† a b a<b • i b ^ 0
    syl≡ = ≡.trans (syl-just M pv)
             (≡.trans (≡.cong₂ (sylData b) (proj₁ ln) (proj₂ ln))
               (≡.trans (sylData-pair {p = b} 0 w fo nx a<b)
                 (≡.cong₂ (λ u v → K† a b a<b • i b ^ qOf u v) w-a w-b)))

  edge : Path (K a b a<b) 𝕀 ColOrth-𝕀
  edge = edge-𝕀 (K-gen a b a<b) pv (trans (cleft refl′ syl≡) (trans (cleft right-unit) (K†-K a<b)))

------------------------------------------------------------------------
-- The base case

base : Base
base (X-gen a b p) (bX ab) = Case-X.edge a b ab
base (K-gen a b p) (bK a0 b1) = Case-K.edge a b a0 b1
base (i-gen a) (bi a0) = Case-i.edge a a0

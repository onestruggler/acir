------------------------------------------------------------------------
-- Presentations of groups
--
-- The base case of Lemma 3.9: the basic edges out of I.
--
-- For a basic generator G, the synthesis algorithm run on G·I removes
-- G in one syllable: ω_[0] gives the syllable ω_[0]⁷, X_[α,α+1] gives
-- X_[α,α+1], and H_[0,1] gives H_[0,1].  So the syllable cancels G
-- relationally, and the edge G out of I closes (edge-𝕀).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.Clifford+T-2qubit-TwoLevel.BaseCase {n : ℕ} where

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

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Scale
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Residue using (δ²ᶻ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Lde using (scV ; scV-! ; lde ; num ; lde-char ; Odd)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Column
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Pivot using (pivot ; pivot-char ; Beyond)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syllable
  using (syl ; syl-just ; step ; top ; Beyond-actM ; eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; col𝕀≡)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Synthesis using (synth-step)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Derived {n} using (ω⁷-ω ; X-X ; H-H)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Basic {n} using (IsBasic ; bX ; bH ; bω)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Reduction {n} using (nw ; nw-cong ; Path ; sound-act ; Base)

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
  e-a a = ≡.trans (eᶻ-! a a) (eδ-refl a)

  e-≢ : {a x : Fin n} → x ≢ a → eᶻ a ! x ≡ ZR.0#
  e-≢ {a} {x} x≢a = ≡.trans (eᶻ-! a x) (eδ-≢ x≢a)

  -- Nothing lies below index 0.
  none<0 : {x a : Fin n} → toℕ a ≡ 0 → x < a → ⊥
  none<0 {x} a0 x<a = ℕP.n≮0 (≡.subst (toℕ x ℕ.<_) a0 x<a)

  1≢0 : ZR.1# ≢ ZR.0#
  1≢0 ()

  ω≢1 : ωᶻ ≢ ZR.1#
  ω≢1 ()

  λω≢0 : λωᶻ ≢ ZR.0#
  λω≢0 ()


------------------------------------------------------------------------
-- ω_[0]: the syllable is ω_[0]⁷

module Case-ω (a : Fin n) (a0 : toℕ a ≡ 0) where

  private
    M = actM (ω-gen a) 𝕀

    w : Vec Z n
    w = ωᵛ a (eᶻ a)

    col≡ : col M a ≡ scV 0 w
    col≡ = ≡.trans (col-gI (ω-gen a) a) (actV-ω a 0 (eᶻ a))

    w-a : w ! a ≡ ωᶻ
    w-a = ≡.trans (set₁-a a (ωᶻ ZR.* (eᶻ a ! a)) (eᶻ a))
                  (≡.trans (≡.cong (ωᶻ ZR.*_) (e-a a)) (ZR.*-identityʳ ωᶻ))

    ln : lde (col M a) ≡ 0 × num (col M a) ≡ w
    ln = lde-char 0 w col≡ (inj₁ ≡.refl)

    ne : col M a ≢ col 𝕀 a
    ne eq = ω≢1 (≡.trans (≡.sym w-a) (≡.trans (≡.cong (_! a) w≡e) (e-a a)))
      where
      w≡e : w ≡ eᶻ a
      w≡e = scV-inj 0 w (eᶻ a) (≡.trans (≡.sym col≡) (≡.trans eq (col𝕀≡ a)))

    pv : pivot M ≡ just a
    pv = pivot-char M ne (Beyond-actM (ω-gen a) {M = 𝕀} FinP.≤-refl (λ c _ → ≡.refl))

    fo : firstOdd w ≡ just a
    fo = firstOdd-char w (≡.cong oddᶻ w-a) (λ x x<a → ⊥-elim (none<0 a0 x<a))

    syl≡ : syl M ≡ ω a ^ 7
    syl≡ = ≡.trans (syl-just M pv)
             (≡.trans (≡.cong₂ (sylData a) (proj₁ ln) (proj₂ ln))
               (≡.trans (sylData-unit≡ w fo) (≡.cong (λ z → ω a ^ invExp z) w-a)))

  edge : Path (ω a) 𝕀 ColOrth-𝕀
  edge = edge-𝕀 (ω-gen a) pv (trans (cleft refl′ syl≡) ω⁷-ω)

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

    syl≡ : syl M ≡ X a b a<b • ω a ^ 0
    syl≡ = ≡.trans (syl-just M pv)
             (≡.trans (≡.cong₂ (sylData b) (proj₁ ln) (proj₂ ln))
               (≡.trans (sylData-unit< w fo a<b) (≡.cong (λ z → X a b a<b • ω a ^ invExp z) w-a)))

  edge : Path (X a b a<b) 𝕀 ColOrth-𝕀
  edge = edge-𝕀 (X-gen a b a<b) pv (trans (cleft refl′ syl≡) (trans (cleft right-unit) (X-X a<b)))

------------------------------------------------------------------------
-- H_[0,1]: the syllable is H_[0,1]

module Case-H (a b : Fin n) (a0 : toℕ a ≡ 0) (b1 : toℕ b ≡ 1) where

  a<b : a < b
  a<b = ≡.subst₂ ℕ._<_ (≡.sym a0) (≡.sym b1) (ℕ.s≤s ℕ.z≤n)

  private
    a≢b : a ≢ b
    a≢b = <⇒≢ a<b

    M = actM (H-gen a b a<b) 𝕀

    w : Vec Z n
    w = Hᶻ a b (eᶻ b)

    col≡ : col M b ≡ scV 2 w
    col≡ = ≡.trans (col-gI (H-gen a b a<b) b) (actV-H a b a<b 0 (eᶻ b))

    w-a : w ! a ≡ λωᶻ
    w-a = ≡.trans (set₂-a a b (λωᶻ ZR.* (eᶻ b ! a ZR.+ eᶻ b ! b)) (λωᶻ ZR.* (eᶻ b ! a ZR.- eᶻ b ! b))
                          (Vec.map (δ²ᶻ ZR.*_) (eᶻ b)))
                  (≡.trans (≡.cong (λωᶻ ZR.*_) (≡.trans (≡.cong₂ ZR._+_ (e-≢ a≢b) (e-a b)) (ZR.+-identityˡ ZR.1#)))
                           (ZR.*-identityʳ λωᶻ))

    w-b : w ! b ≡ λωᶻ ZR.* (ZR.0# ZR.- ZR.1#)
    w-b = ≡.trans (set₂-b a b (λωᶻ ZR.* (eᶻ b ! a ZR.+ eᶻ b ! b)) (λωᶻ ZR.* (eᶻ b ! a ZR.- eᶻ b ! b))
                          (Vec.map (δ²ᶻ ZR.*_) (eᶻ b)) a≢b)
                  (≡.cong (λωᶻ ZR.*_) (≡.cong₂ ZR._-_ (e-≢ a≢b) (e-a b)))

    ln : lde (col M b) ≡ 2 × num (col M b) ≡ w
    ln = lde-char 2 w col≡ (inj₂ (a , ≡.cong oddᶻ w-a))

    -- Entry a of column b is λω / δ², not 0.
    ne : col M b ≢ col 𝕀 b
    ne eq = λω≢0 (sc-injective 2 (≡.trans chain (≡.sym (sc-0 2))))
      where
      chain : sc 2 λωᶻ ≡ DR.0#
      chain = ≡.trans (≡.cong (sc 2) (≡.sym w-a))
                (≡.trans (≡.sym (scV-! 2 w a))
                  (≡.trans (≡.cong (_! a) (≡.sym col≡))
                    (≡.trans (≡.cong (_! a) eq)
                      (≡.trans (≡.cong (_! a) (col𝕀≡ b))
                        (≡.trans (scV-! 0 (eᶻ b) a)
                          (≡.trans (≡.cong (sc 0) (e-≢ a≢b)) (sc-0 0)))))))

    pv : pivot M ≡ just b
    pv = pivot-char M ne (Beyond-actM (H-gen a b a<b) {M = 𝕀} FinP.≤-refl (λ c _ → ≡.refl))

    fo : firstOdd w ≡ just a
    fo = firstOdd-char w (≡.cong oddᶻ w-a) (λ x x<a → ⊥-elim (none<0 a0 x<a))

    -- Nothing lies strictly between 0 and 1.
    between : ∀ {x : Fin n} → a < x → x < b → ⊥
    between {x} a<x x<b = ℕP.<-irrefl ≡.refl
      (ℕP.<-≤-trans (≡.subst (ℕ._< toℕ x) a0 a<x) (ℕP.≤-pred (≡.subst (toℕ x ℕ.<_) b1 x<b)))

    nx : nextOdd a w ≡ just b
    nx = nextOdd-char w a<b (≡.cong oddᶻ w-b) (λ x a<x x<b → ⊥-elim (between a<x x<b))

    -- λω and -λω are ≡ (mod δ³), so the exponent is 0.
    syl≡ : syl M ≡ H a b a<b • ω a ^ 0
    syl≡ = ≡.trans (syl-just M pv)
             (≡.trans (≡.cong₂ (sylData b) (proj₁ ln) (proj₂ ln))
               (≡.trans (sylData-pair {p = b} 1 w fo nx a<b)
                 (≡.cong₂ (λ u v → H a b a<b • ω a ^ zOf u v) w-a w-b)))

  edge : Path (H a b a<b) 𝕀 ColOrth-𝕀
  edge = edge-𝕀 (H-gen a b a<b) pv (trans (cleft refl′ syl≡) (trans (cleft right-unit) (H-H a<b)))

------------------------------------------------------------------------
-- The base case

base : Base
base (X-gen a b p) (bX ab) = Case-X.edge a b ab
base (H-gen a b p) (bH a0 b1) = Case-H.edge a b a0 b1
base (ω-gen a) (bω a0) = Case-ω.edge a a0

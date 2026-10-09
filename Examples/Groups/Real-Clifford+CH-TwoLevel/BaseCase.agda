------------------------------------------------------------------------
-- Presentations of groups
--
-- The edges out of I (the base of the induction, Lemma A.8 at level
-- (0, 0, 0)).
--
-- Algorithm 1 run on g·I removes g in one syllable: Z_[a] gives Z_[a],
-- X_[a,b] gives X_[a,b], and H_[a,b] gives H_[0,b] (a = 0) or
-- H_[0,b] X_[0,a], which is X_[0,a] H_[a,b]: then the edge H_[a,b] out
-- of I follows from the edge X_[0,a].
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.Real-Clifford+CH-TwoLevel.BaseCase {n : ℕ} where

open import Data.Bool.Base using (false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; _<_ ; toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)
open import Quantum.Synthesis.Ring using (RootTwo)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (scV ; scV-! ; lde ; num ; lde-char ; Odd ; Minimal)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot
  using (pivot ; pivot-char ; pivot-nothing ; Beyond ; Lvl ; lvlAt ; level)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable
  using (syl ; top ; Beyond-actM ; eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; col𝕀≡)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (Z-Z ; X-X ; H-H ; flip-X)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (Path ; path-ε ; EdgesAt)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PathTools {n} using (via)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (path-normal ; syl-of ; ne-𝕀 ; ne-𝕀-at)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

  col-gI : (g : Gen n) (c : Fin n) → col (actM g 𝕀) c ≡ actV g (scV 0 (eᶻ c))
  col-gI g c = ≡.trans (col-actM g 𝕀 c) (≡.cong (actV g) (col𝕀≡ c))

  e-a : (a : Fin n) → eᶻ a ! a ≡ ZR.1#
  e-a a = ≡.trans (eᶻ-! a a) (eδ-refl a)

  e-≢ : {a x : Fin n} → x ≢ a → eᶻ a ! x ≡ ZR.0#
  e-≢ {a} {x} x≢a = ≡.trans (eᶻ-! a x) (eδ-≢ x≢a)

  -- I agrees with itself beyond any index.
  Beyond-𝕀 : (b : Fin n) → Beyond b 𝕀
  Beyond-𝕀 b c _ = ≡.refl

  -- The pivot of g·I is b, if g acts on indices ≤ b and moves e_b.
  pivot-gI : (g : Gen n) (b : Fin n) → top g Fin.≤ b → col (actM g 𝕀) b ≢ col 𝕀 b → pivot (actM g 𝕀) ≡ just b
  pivot-gI g b tg ne = pivot-char (actM g 𝕀) ne (Beyond-actM g {M = 𝕀} tg (Beyond-𝕀 b))

  -1≢1 : ZR.- ZR.1# ≢ ZR.1#
  -1≢1 ()

------------------------------------------------------------------------
-- Z_[a]: the syllable is Z_[a]

module Case-Z (a : Fin n) where
  private
    M = actM (Z-gen a) 𝕀
    w : Vec Z n
    w = Zᶻ a (eᶻ a)
    col≡ : col M a ≡ scV 0 w
    col≡ = ≡.trans (col-gI (Z-gen a) a) (actV-Z a 0 (eᶻ a))
    wa : w ! a ≡ ZR.- ZR.1#
    wa = ≡.trans (set₁-a a (ZR.- (eᶻ a ! a)) (eᶻ a)) (≡.cong ZR.-_ (e-a a))
    w≢ : ∀ {x} → x ≢ a → w ! x ≡ ZR.0#
    w≢ {x} x≢a = ≡.trans (set₁-≢ a (ZR.- (eᶻ a ! a)) (eᶻ a) x≢a) (e-≢ x≢a)
    min : Minimal 0 w
    min = inj₁ ≡.refl
    pv : pivot M ≡ just a
    pv = pivot-gI (Z-gen a) a FinP.≤-refl (ne-𝕀-at M a 0 w col≡ min a (λ e → -1≢1 (≡.trans (≡.sym wa) (≡.trans e (e-a a)))))
    fo : firstOdd w ≡ just a
    fo = firstOdd-char w (≡.cong oddᶻ wa) (λ x x<a → ≡.cong oddᶻ (w≢ (λ { ≡.refl → FinP.<-irrefl ≡.refl x<a })))
    syl≡ : syl M ≡ Zʷ a
    syl≡ = ≡.trans (syl-of M pv 0 w col≡ min) (≡.trans (sylData-unit≡ w fo) (≡.cong (λ z → Zτ a (negᶻ z)) wa))

  edge : Path [ Z-gen a ]ʷ 𝕀 ColOrth-𝕀
  edge = via (Z-gen a) 𝕀 ColOrth-𝕀 (syl M) ε (path-normal M (ColOrth-actMʷ [ Z-gen a ]ʷ ColOrth-𝕀) pv)
           (trans (cleft refl′ syl≡) Z-Z) (path-ε 𝕀 ColOrth-𝕀)

------------------------------------------------------------------------
-- X_[a,b]: the syllable is X_[a,b]

module Case-X (a b : Fin n) .(ab : a < b) where
  private
    a≢b : a ≢ b
    a≢b = <⇒≢ ab
    M = actM (X-gen a b ab) 𝕀
    w = Xᶻ a b (eᶻ b)
    col≡ : col M b ≡ scV 0 w
    col≡ = ≡.trans (col-gI (X-gen a b ab) b) (actV-X a b ab 0 (eᶻ b))
    -- w = e_a.
    w≡ : w ≡ eᶻ a
    w≡ = vec-ext λ x → dec-elim (x FinP.≟ a)
      (λ { ≡.refl → ≡.trans (set₂-a x b (eᶻ b ! b) (eᶻ b ! x) (eᶻ b)) (≡.trans (e-a b) (≡.sym (e-a x))) })
      (λ x≢a → dec-elim (x FinP.≟ b)
        (λ { ≡.refl → ≡.trans (set₂-b a x (eᶻ x ! x) (eᶻ x ! a) (eᶻ x) a≢b) (≡.trans (e-≢ a≢b) (≡.sym (e-≢ (a≢b ∘′ ≡.sym)))) })
        (λ x≢b → ≡.trans (set₂-≢ a b (eᶻ b ! b) (eᶻ b ! a) (eᶻ b) x≢a x≢b) (≡.trans (e-≢ x≢b) (≡.sym (e-≢ x≢a)))))
      where
      _∘′_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
      (f ∘′ g) x = f (g x)
    col≡′ : col M b ≡ scV 0 (eᶻ a)
    col≡′ = ≡.trans col≡ (≡.cong (scV 0) w≡)
    min : Minimal 0 (eᶻ a)
    min = inj₁ ≡.refl
    pv : pivot M ≡ just b
    pv = pivot-gI (X-gen a b ab) b FinP.≤-refl
           (ne-𝕀-at M b 0 (eᶻ a) col≡′ min b (λ e → 0≢1 (≡.trans (≡.sym (e-≢ (λ e′ → a≢b (≡.sym e′)))) (≡.trans e (e-a b)))))
      where
      0≢1 : ZR.0# ≢ ZR.1#
      0≢1 ()
    fo : firstOdd (eᶻ a) ≡ just a
    fo = firstOdd-char (eᶻ a) (≡.cong oddᶻ (e-a a)) (λ x x<a → ≡.cong oddᶻ (e-≢ (λ { ≡.refl → FinP.<-irrefl ≡.refl x<a })))
    syl≡ : syl M ≡ X a b ab • ε
    syl≡ = ≡.trans (syl-of M pv 0 (eᶻ a) col≡′ min)
             (≡.trans (sylData-unit< (eᶻ a) fo (recompute′ ab)) (≡.cong (λ z → X a b ab • Zτ a (negᶻ z)) (e-a a)))
      where
      recompute′ : .(a < b) → a < b
      recompute′ p = Relation.Nullary.Decidable.recompute (a FinP.<? b) p
        where import Relation.Nullary.Decidable

  edge : Path [ X-gen a b ab ]ʷ 𝕀 ColOrth-𝕀
  edge = via (X-gen a b ab) 𝕀 ColOrth-𝕀 (syl M) ε (path-normal M (ColOrth-actMʷ [ X-gen a b ab ]ʷ ColOrth-𝕀) pv)
           (trans (cleft trans (refl′ syl≡) right-unit) (X-X ab)) (path-ε 𝕀 ColOrth-𝕀)

------------------------------------------------------------------------
-- H_[a,b]: the syllable is H_[0,b] or H_[0,b] X_[0,a]

module Case-H (a b : Fin n) .(ab : a < b) where
  private
    ab′ : a < b
    ab′ = Relation.Nullary.Decidable.recompute (a FinP.<? b) ab
      where import Relation.Nullary.Decidable
    a≢b : a ≢ b
    a≢b = <⇒≢ ab
    M = actM (H-gen a b ab) 𝕀
    w = Hᶻ a b (eᶻ b)
    col≡ : col M b ≡ scV 1 w
    col≡ = ≡.trans (col-gI (H-gen a b ab) b) (actV-H a b ab 0 (eᶻ b))
    wa : w ! a ≡ ZR.1#
    wa = ≡.trans (set₂-a a b _ _ _) (≡.cong₂ ZR._+_ (e-≢ a≢b) (e-a b))
    wb : w ! b ≡ ZR.- ZR.1#
    wb = ≡.trans (set₂-b a b _ _ _ a≢b) (≡.cong₂ ZR._-_ (e-≢ a≢b) (e-a b))
    w≢ : ∀ {x} → x ≢ a → x ≢ b → w ! x ≡ ZR.0#
    w≢ {x} x≢a x≢b = ≡.trans (set₂-≢ a b _ _ _ x≢a x≢b)
                       (≡.trans (VecP.lookup-map x (√2ᶻ ZR.*_) (eᶻ b)) (≡.cong (√2ᶻ ZR.*_) (e-≢ x≢b)))
    min : Minimal 1 w
    min = inj₂ (a , ≡.cong oddᶻ wa)
    pv : pivot M ≡ just b
    pv = pivot-gI (H-gen a b ab) b FinP.≤-refl (ne-𝕀 M b 0 w col≡ min)
    fo : firstOdd w ≡ just a
    fo = firstOdd-char w (≡.cong oddᶻ wa) (λ x x<a → ≡.cong oddᶻ (w≢ (λ { ≡.refl → FinP.<-irrefl ≡.refl x<a })
                                                              (λ { ≡.refl → FinP.<-irrefl ≡.refl (FinP.<-trans x<a ab′) })))
    nx : nextSame a w ≡ just b
    nx = nextSame-char w ab′ (≡.cong oddᶻ wb , ≡.trans (≡.cong rbit wb) (≡.sym (≡.cong rbit wa)))
           (λ x a<x x<b (ox , _) → 1≢0 (≡.trans (≡.sym ox) (≡.cong oddᶻ (w≢ (λ { ≡.refl → FinP.<-irrefl ≡.refl a<x })
                                                                                (λ { ≡.refl → FinP.<-irrefl ≡.refl x<b })))))
      where
      1≢0 : Data.Bool.Base.true ≢ false
      1≢0 ()
        where import Data.Bool.Base
    syl≡ : syl M ≡ pairSyl a b ab
    syl≡ = ≡.trans (syl-of M pv 1 w col≡ min) (sylData-pair {p = b} 0 w fo nx ab′)

    Mo = ColOrth-actMʷ [ H-gen a b ab ]ʷ ColOrth-𝕀

  -- With the edge X_[0,a] out of I when a > 0.
  edge : (∀ (x y : Fin n) .(xy : x < y) → Path [ X-gen x y xy ]ʷ 𝕀 ColOrth-𝕀) → Path [ H-gen a b ab ]ʷ 𝕀 ColOrth-𝕀
  edge xedge = by-a (toℕ a ℕP.≟ 0)
    where
    by-a : Dec (toℕ a ≡ 0) → Path [ H-gen a b ab ]ʷ 𝕀 ColOrth-𝕀
    by-a (yes a0) =
      via (H-gen a b ab) 𝕀 ColOrth-𝕀 (syl M) ε (path-normal M Mo pv)
          (trans (cleft refl′ (≡.trans syl≡ (pairSyl-0 a b ab a0))) (H-H ab)) (path-ε 𝕀 ColOrth-𝕀)
    by-a (no a≢0) =
      via (H-gen a b ab) 𝕀 ColOrth-𝕀 (syl M) (X z a 0<a) (path-normal M Mo pv) rel (xedge z a 0<a)
      where
      pos : 0 ℕ.< toℕ a
      pos = ℕP.n≢0⇒n>0 a≢0
      z = zeroOf a
      0<a : z < a
      0<a = zeroOf-< a pos
      0<b = ℕP.<-trans 0<a ab′
      -- (c4): H_[a,b] X_[0,a] = X_[0,a] H_[0,b], so H_[0,b] X_[0,a] = X_[0,a] H_[a,b].
      c4′ : H z b 0<b • X z a 0<a ≈ X z a 0<a • H a b ab
      c4′ = flip-X 0<a (axiom (c4 0<a ab′))
      rel : syl M • H a b ab ≈ X z a 0<a
      rel = begin
        syl M • H a b ab                                       ≈⟨ cleft refl′ (≡.trans syl≡ (pairSyl-s a b ab pos)) ⟩
        (H z b 0<b • X z a 0<a) • H a b ab                     ≈⟨ cleft c4′ ⟩
        (X z a 0<a • H a b ab) • H a b ab                      ≈⟨ assoc ⟩
        X z a 0<a • (H a b ab • H a b ab)                      ≈⟨ cright H-H ab ⟩
        X z a 0<a • ε                                          ≈⟨ right-unit ⟩
        X z a 0<a                                              ∎

------------------------------------------------------------------------
-- All edges out of I, and out of every state at level (0, 0, 0)

edge-𝕀 : ∀ (g : Gen n) → Path [ g ]ʷ 𝕀 ColOrth-𝕀
edge-𝕀 (Z-gen a) = Case-Z.edge a
edge-𝕀 (X-gen a b ab) = Case-X.edge a b ab
edge-𝕀 (H-gen a b ab) = Case-H.edge a b ab (λ x y xy → Case-X.edge x y xy)

base : EdgesAt (0 , 0 , 0)
base g M o eq _ = at (pivot M) ≡.refl
  where
  at : (r : Maybe (Fin n)) → pivot M ≡ r → Path [ g ]ʷ M o
  at nothing pv = ≡.subst (λ N → ∀ .(o′ : ColOrth N) → Path [ g ]ʷ N o′)
                          (≡.sym (pivot-nothing M pv)) (λ _ → edge-𝕀 g) o
  at (just p) pv = ⊥-elim (suc≢0 (≡.cong proj₁ (≡.trans (≡.sym (≡.cong (λ x → lvlAt x M) pv)) eq)))
    where
    suc≢0 : ∀ {m} → suc m ≢ 0
    suc≢0 ()

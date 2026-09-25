------------------------------------------------------------------------
-- Presentations of groups
--
-- The Main Lemma for the basic generator G = i_[0] (Case 1 of the
-- Appendix).  With v the pivot column of s, k its least denominator
-- exponent, w = γᵏ v and j the index of the first odd entry of w:
--
-- * j > 0: the syllable of s acts above 0, and is also the syllable of
--   r = i_[0] s: a disjoint case;
-- * j = 0, k = 0: v = iᵗ e_0, and the syllable of r, after i_[0], is
--   that of s (or r = I when t = 3);
-- * j = 0, k > 0: with l the second odd entry, the syllables are
--   K†_[0,l] i_[l]ᑫ and K†_[0,l] i_[l]ᑫ′ with q′ = 1 - q, and the square
--   closes through i_[0] i_[l] X_[0,l]ᑫ by (15) or (case 1.4b).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)

module Examples.Groups.Clifford+CS-TwoLevel.CaseI {n : ℕ} where

open import Data.Bool.Base using (false ; _∧_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute ; does ; dec-true)
import Relation.Binary.Reasoning.Setoid as SR

open import Instances using (_≟_ ; DEℤ)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx ; DecEqCplx)

open import Notations using (auto)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+CS-TwoLevel.Ring
open import Examples.Groups.Clifford+CS-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (first-nothing ; count ; count-one)
open import Examples.Groups.Clifford+CS-TwoLevel.Norm using (Nℕ ; Σℕ ; Unit ; lde0 ; evenodd)
open import Examples.Groups.Clifford+CS-TwoLevel.Column
open import Examples.Groups.Clifford+CS-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Clifford+CS-TwoLevel.Pivot
  using (pivot ; pivot-just ; pivot-char ; level ; _<ₗ_)
open import Examples.Groups.Clifford+CS-TwoLevel.Syllable
  using (syl ; step ; Beyond-actM ; eᶻ ; eᶻ-! ; δᶻ-refl ; δᶻ-≢ ; col𝕀≡)
open import Examples.Groups.Clifford+CS-TwoLevel.Step using (pivot-zero> ; col-norm ; odd⇒≤)
open import Examples.Groups.Clifford+CS-TwoLevel.Levels using (odd-i ; Minimal-i ; mono-level ; Bℓ)
open import Examples.Groups.Clifford+CS-TwoLevel.Derived {n}
  using (i⁴ ; conj-^ ; K†I≈ILXK†L ; Apartʷ)
open import Examples.Groups.Clifford+CS-TwoLevel.Basic {n} using (Letters≤)
open import Examples.Groups.Clifford+CS-TwoLevel.Reduction {n} using (Square ; Below ; path-ε)
open import Examples.Groups.Clifford+CS-TwoLevel.MainTools {n}
  using (pivot-keep ; lt-step ; square-by ; square-disjoint ; square-merge ;
         square-syl ; syl-of ; level-of ; word-below-all ; above-apart)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

------------------------------------------------------------------------
-- The case

module _ (a : Fin n) (a0 : toℕ a ≡ 0) (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p) where

  private
    r = actM (i-gen a) s
    v = col s p
    W = num v

    v≡ : v ≡ scV (lde v) W
    v≡ = lde-eq v

    -- The facts that come from column-orthonormality, recomputed.
    zero> : ∀ x → p < x → W ! x ≡ ZR.0#
    zero> x px = recompute (W ! x ≟ ZR.0#) (pivot-zero> o ps x px)

    norm : Σℕ (λ x → Nℕ (W ! x)) ≡ 2 ℕ.^ lde v
    norm = recompute (Σℕ (λ x → Nℕ (W ! x)) ℕP.≟ 2 ℕ.^ lde v) (col-norm o p)

    -- Nothing lies below 0.
    none<a : ∀ {x : Fin n} → x < a → ⊥
    none<a {x} x<a = ℕP.n≮0 (≡.subst (toℕ x ℕ.<_) a0 x<a)

    a≤ : ∀ (x : Fin n) → a ≤ x
    a≤ x = ≡.subst (ℕ._≤ toℕ x) (≡.sym a0) z≤n

    -- The column of r = i_[0] s at the pivot, when the pivot is above 0.
    col-r : ∀ {K} {w : Vec Z n} → v ≡ scV K w → col r p ≡ scV K (iᶻ a w)
    col-r {K} {w} e = ≡.trans (col-actM (i-gen a) s p) (≡.trans (≡.cong (actV (i-gen a)) e) (actV-i a K w))

    lvl : level s ≡ (suc (toℕ p) , lde v , nodd W)
    lvl = level-of s ps (lde v) W v≡ (lde-min v)

  ----------------------------------------------------------------------
  -- j > 0: disjoint

  private
    disjoint : ∀ {j} → firstOdd W ≡ just j → a < j → Square (i-gen a) s o
    disjoint {j} fo a<j = square-disjoint (i-gen a) s o ps pr syl≡ apart lq
      where
      j≤p : j ≤ p
      j≤p = odd⇒≤ {p = p} {W} zero> (proj₁ (firstOdd-spec W fo))
      a<p : a < p
      a<p = ℕP.<-≤-trans a<j j≤p
      pr : pivot r ≡ just p
      pr = pivot-keep (i-gen a) s a<p ps
      -- Entry a of W is even, so i_[0] changes no odd entry.
      agree : ∀ x → Odd (iᶻ a W ! x) → iᶻ a W ! x ≡ W ! x
      agree x ox = at (x FinP.≟ a)
        where
        at : Dec (x ≡ a) → iᶻ a W ! x ≡ W ! x
        at (yes ≡.refl) = ⊥-elim (Odd⇒¬Even {W ! x} (≡.trans (≡.sym (odd-i a W x)) ox)
                                              (proj₂ (firstOdd-spec W fo) x a<j))
        at (no x≢a) = set₁-≢ a (ⅈᶻ ZR.* (W ! a)) W x≢a
      syl≡ : syl r ≡ syl s
      syl≡ = ≡.trans (syl-of r pr (lde v) (iᶻ a W) (col-r v≡) (Minimal-i a W (lde-min v)))
               (≡.trans (sylData-agree p (lde v) (iᶻ a W) W (odd-i a W) agree)
                 (≡.sym (syl-of s ps (lde v) W v≡ (lde-min v))))
      apart : Apartʷ (syl s) (i-gen a)
      apart = ≡.subst (λ u → Apartʷ u (i-gen a)) (≡.sym (syl-of s ps (lde v) W v≡ (lde-min v)))
                (above-apart (sylData p (lde v) W) (sylData-above p (lde v) W fo j≤p) a<j)
      lq : level (actM (i-gen a) (step s)) <ₗ level s
      lq = mono-level (i-gen a) tt FinP.≤-refl (step s) (lt-step s o ps)
             (≡.subst (Bℓ a <ₗ_) (≡.sym lvl) (inj₁ (s≤s a<p)))

  ----------------------------------------------------------------------
  -- j = 0, k = 0: v = iᵗ e_0, and the syllable of r, after i_[0], is
  -- that of s

  private
    scV-inj : ∀ k (u w : Vec Z n) → scV k u ≡ scV k w → u ≡ w
    scV-inj k u w eq = vec-ext λ x →
      sc-injective k (≡.trans (≡.sym (scV-! k u x)) (≡.trans (≡.cong (_! x) eq) (scV-! k w x)))
      where open import Examples.Groups.Clifford+CS-TwoLevel.Scale using (sc-injective)

    -- The pivot column is a unit at 0.
    unit-facts : firstOdd W ≡ just a → lde v ≡ 0 →
                 ∃ λ t → t ℕ.< 4 × W ! a ≡ ⅈᶻ ^ᶻ t × (∀ y → y ≢ a → W ! y ≡ ZR.0#)
    unit-facts fo k0 = go (lde0 W (≡.trans norm (≡.cong (2 ℕ.^_) k0)))
      where
      go : (∃ λ m → Unit (W ! m) × (∀ y → y ≢ m → W ! y ≡ ZR.0#)) →
           ∃ λ t → t ℕ.< 4 × W ! a ≡ ⅈᶻ ^ᶻ t × (∀ y → y ≢ a → W ! y ≡ ZR.0#)
      go (m , (t , t<4 , um) , rest) = at (m FinP.≟ a)
        where
        at : Dec (m ≡ a) → ∃ λ t → t ℕ.< 4 × W ! a ≡ ⅈᶻ ^ᶻ t × (∀ y → y ≢ a → W ! y ≡ ZR.0#)
        at (yes m≡a) = t , t<4 , ≡.subst (λ x → W ! x ≡ ⅈᶻ ^ᶻ t) m≡a um ,
                       ≡.subst (λ x → ∀ y → y ≢ x → W ! y ≡ ZR.0#) m≡a rest
        at (no m≢a) = ⊥-elim (Odd⇒¬Even {W ! a} (proj₁ (firstOdd-spec W fo))
                                          (≡.cong oddᶻ (rest a (λ e → m≢a (≡.sym e)))))

    v≡₀ : lde v ≡ 0 → v ≡ scV 0 W
    v≡₀ k0 = ≡.trans v≡ (≡.cong (λ k → scV k W) k0)

    -- The relations, with the pivot above 0.
    unit-rel< : ∀ t → t ℕ.< 4 → {q : Fin n} .(aq : a < q) →
                (X a q aq • i a ^ invExp (ⅈᶻ ZR.* (ⅈᶻ ^ᶻ t))) • i a ≈ X a q aq • i a ^ invExp (ⅈᶻ ^ᶻ t)
    unit-rel< 0 _ aq = trans assoc (trans (cright i³-i′) refl)
      where
      i³-i′ : i a ^ 3 • i a ≈ ε
      i³-i′ = trans (sym (^-+ (i a) 3 1)) i⁴
    unit-rel< 1 _ aq = by-assoc auto
    unit-rel< 2 _ aq = by-assoc auto
    unit-rel< 3 _ aq = by-assoc auto
    unit-rel< (suc (suc (suc (suc t)))) (s≤s (s≤s (s≤s (s≤s ())))) aq

    unit< : firstOdd W ≡ just a → lde v ≡ 0 → a < p → Square (i-gen a) s o
    unit< fo k0 a<p = go (unit-facts fo k0)
      where
      go : (∃ λ t → t ℕ.< 4 × W ! a ≡ ⅈᶻ ^ᶻ t × (∀ y → y ≢ a → W ! y ≡ ZR.0#)) → Square (i-gen a) s o
      go (t , t<4 , ua , rest) = square-merge (i-gen a) s o pr rel
        where
        pr : pivot r ≡ just p
        pr = pivot-keep (i-gen a) s a<p ps
        fo′ : firstOdd (iᶻ a W) ≡ just a
        fo′ = ≡.trans (firstOdd-cong (iᶻ a W) W (odd-i a W)) fo
        syl-r : syl r ≡ X a p a<p • i a ^ invExp (ⅈᶻ ZR.* (ⅈᶻ ^ᶻ t))
        syl-r = ≡.trans (syl-of r pr 0 (iᶻ a W) (col-r (v≡₀ k0)) (inj₁ ≡.refl))
                  (≡.trans (sylData-unit< (iᶻ a W) fo′ a<p)
                    (≡.cong (λ z → X a p a<p • i a ^ invExp z)
                            (≡.trans (set₁-a a (ⅈᶻ ZR.* (W ! a)) W) (≡.cong (ⅈᶻ ZR.*_) ua))))
        syl-s : syl s ≡ X a p a<p • i a ^ invExp (ⅈᶻ ^ᶻ t)
        syl-s = ≡.trans (syl-of s ps 0 W (v≡₀ k0) (inj₁ ≡.refl))
                  (≡.trans (sylData-unit< W fo a<p) (≡.cong (λ z → X a p a<p • i a ^ invExp z) ua))
        rel : syl r • i a ≈ syl s
        rel = trans (cleft refl′ syl-r) (trans (unit-rel< t t<4 a<p) (refl′ (≡.sym syl-s)))

  ----------------------------------------------------------------------
  -- j = 0, k = 0, with the pivot at 0: for t = 3, r = I and the square
  -- closes with empty paths; otherwise the syllable of r, after
  -- i_[0], is that of s

  private
    unit≡ : ∀ {q} → q ≡ p → firstOdd W ≡ just q → lde v ≡ 0 → ∀ t → t ℕ.< 4 → W ! q ≡ ⅈᶻ ^ᶻ t →
            (∀ y → y ≢ q → W ! y ≡ ZR.0#) → Square (i-gen q) s o
    unit≡ ≡.refl fo k0 t t<4 ua rest = by-t t t<4 ua
      where
      rp = actM (i-gen p) s

      col-rp : col rp p ≡ scV 0 (iᶻ p W)
      col-rp = ≡.trans (col-actM (i-gen p) s p) (≡.trans (≡.cong (actV (i-gen p)) (v≡₀ k0)) (actV-i p 0 W))

      fo′ : firstOdd (iᶻ p W) ≡ just p
      fo′ = ≡.trans (firstOdd-cong (iᶻ p W) W (odd-i p W)) fo

      syl-s : ∀ {t} → W ! p ≡ ⅈᶻ ^ᶻ t → syl s ≡ i p ^ invExp (ⅈᶻ ^ᶻ t)
      syl-s ua = ≡.trans (syl-of s ps 0 W (v≡₀ k0) (inj₁ ≡.refl))
                   (≡.trans (sylData-unit≡ W fo) (≡.cong (λ z → i p ^ invExp z) ua))

      rp-p : ∀ {t} → W ! p ≡ ⅈᶻ ^ᶻ t → iᶻ p W ! p ≡ ⅈᶻ ZR.* (ⅈᶻ ^ᶻ t)
      rp-p ua = ≡.trans (set₁-a p (ⅈᶻ ZR.* (W ! p)) W) (≡.cong (ⅈᶻ ZR.*_) ua)

      -- The pivot column of r is not that of I unless i iᵗ = 1.
      ne-of : ∀ {t} → W ! p ≡ ⅈᶻ ^ᶻ t → ⅈᶻ ZR.* (ⅈᶻ ^ᶻ t) ≢ ZR.1# → col rp p ≢ col 𝕀 p
      ne-of {t} ua bad eq = bad (≡.trans (≡.sym (rp-p {t} ua))
        (≡.trans (≡.cong (_! p) (scV-inj 0 (iᶻ p W) (eᶻ p) (≡.trans (≡.sym col-rp) (≡.trans eq (col𝕀≡ p)))))
                 (≡.trans (eᶻ-! p p) (δᶻ-refl p))))

      merge : ∀ {t} → W ! p ≡ ⅈᶻ ^ᶻ t → ⅈᶻ ZR.* (ⅈᶻ ^ᶻ t) ≢ ZR.1# →
              i p ^ invExp (ⅈᶻ ZR.* (ⅈᶻ ^ᶻ t)) • i p ≈ i p ^ invExp (ⅈᶻ ^ᶻ t) → Square (i-gen p) s o
      merge {t} ua bad rel′ = square-merge (i-gen p) s o pr rel
        where
        pr : pivot rp ≡ just p
        pr = pivot-char rp (ne-of {t} ua bad) (Beyond-actM (i-gen p) {M = s} FinP.≤-refl (proj₂ (pivot-just s ps)))
        syl-r : syl rp ≡ i p ^ invExp (ⅈᶻ ZR.* (ⅈᶻ ^ᶻ t))
        syl-r = ≡.trans (syl-of rp pr 0 (iᶻ p W) col-rp (inj₁ ≡.refl))
                  (≡.trans (sylData-unit≡ (iᶻ p W) fo′) (≡.cong (λ z → i p ^ invExp z) (rp-p {t} ua)))
        rel : syl rp • i p ≈ syl s
        rel = trans (cleft refl′ syl-r) (trans rel′ (refl′ (≡.sym (syl-s {t} ua))))

      by-t : ∀ t → t ℕ.< 4 → W ! p ≡ ⅈᶻ ^ᶻ t → Square (i-gen p) s o
      -- t = 0: v = e_p would not be a pivot column.
      by-t 0 _ ua = ⊥-elim (proj₁ (pivot-just s ps) (≡.trans (v≡₀ k0) (≡.trans (≡.cong (scV 0) W≡e) (≡.sym (col𝕀≡ p)))))
        where
        at : ∀ x → Dec (x ≡ p) → W ! x ≡ eᶻ p ! x
        at x (yes ≡.refl) = ≡.trans ua (≡.sym (≡.trans (eᶻ-! x x) (δᶻ-refl x)))
        at x (no x≢p) = ≡.trans (rest x x≢p) (≡.sym (≡.trans (eᶻ-! p x) (δᶻ-≢ x≢p)))
        W≡e : W ≡ eᶻ p
        W≡e = vec-ext λ x → at x (x FinP.≟ p)
      by-t 1 _ ua = merge {1} ua (λ ()) (by-assoc auto)
      by-t 2 _ ua = merge {2} ua (λ ()) (by-assoc auto)
      by-t 3 _ ua = square-by (i-gen p) s o ε ε (path-ε rp (ColOrth-actMʷ [ i-gen p ]ʷ o)) tt
                      (cright refl′ (≡.sym (syl-s {3} ua)))
      by-t (suc (suc (suc (suc t)))) (s≤s (s≤s (s≤s (s≤s ())))) _

  ----------------------------------------------------------------------
  -- j = 0, k > 0: the second odd entry ℓ, and q flips

  private
    pair : firstOdd W ≡ just a → ∀ {K′} → lde v ≡ suc K′ → Square (i-gen a) s o
    pair fo {K′} ks = withNext (nextOdd a W) ≡.refl
      where
      oa : Odd (W ! a)
      oa = proj₁ (firstOdd-spec W fo)

      withNext : (m : Maybe (Fin n)) → nextOdd a W ≡ m → Square (i-gen a) s o
      -- By evenodd, a is not the only odd entry.
      withNext nothing nx =
        ⊥-elim (odd1 (≡.trans (≡.sym (≡.cong oddℕ cnt)) (evenodd K′ W (≡.trans norm (≡.cong (2 ℕ.^_) ks)))))
        where
        odd1 : oddℕ 1 ≡ false → ⊥
        odd1 ()
        others : ∀ x → x ≢ a → oddᶻ (W ! x) ≡ false
        others x x≢a = at (FinP.<-cmp x a)
          where
          at : Tri (x < a) (x ≡ a) (a < x) → oddᶻ (W ! x) ≡ false
          at (tri< x<a _ _) = proj₂ (firstOdd-spec W fo) x x<a
          at (tri≈ _ x≡a _) = ⊥-elim (x≢a x≡a)
          at (tri> _ _ a<x) = ≡.trans (≡.sym (≡.cong (_∧ oddᶻ (W ! x)) (dec-true (a FinP.<? x) a<x)))
                                (first-nothing (λ y → does (a FinP.<? y) ∧ oddᶻ (W ! y)) nx x)
        cnt : count (λ x → oddᶻ (W ! x)) ≡ 1
        cnt = count-one (λ x → oddᶻ (W ! x)) a oa others
      withNext (just ℓ) nx = by-q (qOf (W ! a) (W ! ℓ)) (qOf-≤1 (W ! a) (W ! ℓ)) ≡.refl
        where
        a<ℓ : a < ℓ
        a<ℓ = proj₁ (nextOdd-spec W nx)
        ℓ≤p : ℓ ≤ p
        ℓ≤p = odd⇒≤ {p = p} {W} zero> (proj₁ (proj₂ (nextOdd-spec W nx)))
        ℓ≢a : ℓ ≢ a
        ℓ≢a e = FinP.<-irrefl (≡.sym e) a<ℓ
        pr : pivot r ≡ just p
        pr = pivot-keep (i-gen a) s (ℕP.<-≤-trans a<ℓ ℓ≤p) ps

        syl-s : syl s ≡ K† a ℓ a<ℓ • i ℓ ^ qOf (W ! a) (W ! ℓ)
        syl-s = ≡.trans (syl-of s ps (lde v) W v≡ (lde-min v))
                  (≡.trans (≡.cong (λ k → sylData p k W) ks) (sylData-pair {p = p} K′ W fo nx a<ℓ))

        q≡ : qOf (iᶻ a W ! a) (iᶻ a W ! ℓ) ≡ 1 ℕ.∸ qOf (W ! a) (W ! ℓ)
        q≡ = ≡.trans (≡.cong₂ qOf (set₁-a a (ⅈᶻ ZR.* (W ! a)) W) (set₁-≢ a (ⅈᶻ ZR.* (W ! a)) W ℓ≢a))
                     (qOf-flip (W ! a) (W ! ℓ) oa)

        syl-r : syl r ≡ K† a ℓ a<ℓ • i ℓ ^ (1 ℕ.∸ qOf (W ! a) (W ! ℓ))
        syl-r = ≡.trans (syl-of r pr (lde v) (iᶻ a W) (col-r v≡) (Minimal-i a W (lde-min v)))
                  (≡.trans (≡.cong (λ k → sylData p k (iᶻ a W)) ks)
                    (≡.trans (sylData-pair {p = p} K′ (iᶻ a W) fo′ nx′ a<ℓ)
                      (≡.cong (λ z → K† a ℓ a<ℓ • i ℓ ^ z) q≡)))
          where
          fo′ : firstOdd (iᶻ a W) ≡ just a
          fo′ = ≡.trans (firstOdd-cong (iᶻ a W) W (odd-i a W)) fo
          nx′ : nextOdd a (iᶻ a W) ≡ just ℓ
          nx′ = ≡.trans (nextOdd-cong a (iᶻ a W) W (odd-i a W)) nx

        -- (ℓ + 1 , 0 , 1) lies below the level of s.
        bℓ : Bℓ ℓ <ₗ level s
        bℓ = ≡.subst (Bℓ ℓ <ₗ_) (≡.sym lvl) (aux (ℕP.m≤n⇒m<n∨m≡n ℓ≤p))
          where
          aux : toℕ ℓ ℕ.< toℕ p ⊎ toℕ ℓ ≡ toℕ p → Bℓ ℓ <ₗ (suc (toℕ p) , lde v , nodd W)
          aux (inj₁ lt) = inj₁ (s≤s lt)
          aux (inj₂ eq) = inj₂ (≡.cong suc eq , inj₁ (≡.subst (0 ℕ.<_) (≡.sym ks) (s≤s z≤n)))

        below : (G′ : Word (Gen n)) → Letters≤ ℓ G′ → Below (level s) G′ (step s)
        below G′ h = word-below-all G′ h (step s) (lt-step s o ps) bℓ

        a≤ℓ : toℕ a ℕ.≤ toℕ ℓ
        a≤ℓ = ℕP.<⇒≤ a<ℓ

        by-q : ∀ q → q ℕ.≤ 1 → qOf (W ! a) (W ! ℓ) ≡ q → Square (i-gen a) s o
        -- q = 0: K† commutes with i_[0] i_[ℓ], by (15).
        by-q 0 _ e =
          square-syl (i-gen a) s o (K† a ℓ a<ℓ • i ℓ) (i a • i ℓ) pr
            (≡.trans syl-r (≡.cong (λ z → K† a ℓ a<ℓ • i ℓ ^ (1 ℕ.∸ z)) e))
            (below (i a • i ℓ) (a≤ℓ , ℕP.≤-refl))
            (trans rel (cright refl′ (≡.sym (≡.trans syl-s (≡.cong (λ z → K† a ℓ a<ℓ • i ℓ ^ z) e)))))
          where
          rel : (K† a ℓ a<ℓ • i ℓ) • i a ≈ (i a • i ℓ) • (K† a ℓ a<ℓ • ε)
          rel = begin
            (K† a ℓ a<ℓ • i ℓ) • i a        ≈⟨ assoc ⟩
            K† a ℓ a<ℓ • (i ℓ • i a)        ≈⟨ cright axiom (comm-ii ℓ≢a) ⟩
            K† a ℓ a<ℓ • (i a • i ℓ)        ≈⟨ conj-^ (trans (axiom (rel-15 a<ℓ)) (sym assoc)) 7 ⟩
            (i a • i ℓ) • K† a ℓ a<ℓ        ≈⟨ cright sym right-unit ⟩
            (i a • i ℓ) • (K† a ℓ a<ℓ • ε)  ∎
        -- q = 1: K†_[0,ℓ] i_[0] = i_[0] i_[ℓ] X_[0,ℓ] K†_[0,ℓ] i_[ℓ].
        by-q 1 _ e =
          square-syl (i-gen a) s o (K† a ℓ a<ℓ • ε) (i a • i ℓ • X a ℓ a<ℓ) pr
            (≡.trans syl-r (≡.cong (λ z → K† a ℓ a<ℓ • i ℓ ^ (1 ℕ.∸ z)) e))
            (below (i a • i ℓ • X a ℓ a<ℓ) (a≤ℓ , ℕP.≤-refl , ℕP.≤-refl))
            (trans rel (cright refl′ (≡.sym (≡.trans syl-s (≡.cong (λ z → K† a ℓ a<ℓ • i ℓ ^ z) e)))))
          where
          rel : (K† a ℓ a<ℓ • ε) • i a ≈ (i a • i ℓ • X a ℓ a<ℓ) • (K† a ℓ a<ℓ • i ℓ)
          rel = begin
            (K† a ℓ a<ℓ • ε) • i a                         ≈⟨ cleft right-unit ⟩
            K† a ℓ a<ℓ • i a                               ≈⟨ K†I≈ILXK†L a<ℓ ⟩
            i a • i ℓ • X a ℓ a<ℓ • K† a ℓ a<ℓ • i ℓ       ≈⟨ by-assoc auto ⟩
            (i a • i ℓ • X a ℓ a<ℓ) • (K† a ℓ a<ℓ • i ℓ)   ∎
        by-q (suc (suc _)) (s≤s ()) _

  ----------------------------------------------------------------------
  -- The case, by the first odd entry j of w and by k

  private
    -- The pivot column has an odd entry.
    some-odd : ∃ λ x → Odd (W ! x)
    some-odd = from (lde v) ≡.refl
      where
      from : ∀ k → lde v ≡ k → ∃ λ x → Odd (W ! x)
      from zero k0 = unit-at (lde0 W (≡.trans norm (≡.cong (2 ℕ.^_) k0)))
        where
        unit-at : (∃ λ m → Unit (W ! m) × (∀ y → y ≢ m → W ! y ≡ ZR.0#)) → ∃ λ x → Odd (W ! x)
        unit-at (m , (t , t<4 , um) , _) = m , ≡.subst Odd (≡.sym um) (unit-odd t t<4)
      from (suc k) ks = minimal (≡.subst (λ k → Minimal k W) ks (lde-min v))
        where
        minimal : Minimal (suc k) W → ∃ λ x → Odd (W ! x)
        minimal (inj₁ ())
        minimal (inj₂ x) = x

  caseI : Square (i-gen a) s o
  caseI = by-first (firstOdd W) ≡.refl
    where
    by-k : firstOdd W ≡ just a → ∀ k → lde v ≡ k → Square (i-gen a) s o
    by-k fo zero k0 = unit (FinP.<-cmp a p) (unit-facts fo k0)
      where
      unit : Tri (a < p) (a ≡ p) (p < a) →
             (∃ λ t → t ℕ.< 4 × W ! a ≡ ⅈᶻ ^ᶻ t × (∀ y → y ≢ a → W ! y ≡ ZR.0#)) → Square (i-gen a) s o
      unit (tri< a<p _ _) _ = unit< fo k0 a<p
      unit (tri≈ _ a≡p _) (t , t<4 , ua , rest) = unit≡ a≡p fo k0 t t<4 ua rest
      unit (tri> _ _ p<a) _ = ⊥-elim (none<a p<a)
    by-k fo (suc K′) ks = pair fo ks

    by-j : ∀ {j} → firstOdd W ≡ just j → Dec (toℕ j ≡ 0) → Square (i-gen a) s o
    by-j fo (yes j0) =
      by-k (≡.subst (λ x → firstOdd W ≡ just x) (FinP.toℕ-injective (≡.trans j0 (≡.sym a0))) fo) (lde v) ≡.refl
    by-j {j} fo (no j≢0) = disjoint fo (≡.subst (ℕ._< toℕ j) (≡.sym a0) (ℕP.n≢0⇒n>0 j≢0))

    by-first : (m : Maybe (Fin n)) → firstOdd W ≡ m → Square (i-gen a) s o
    by-first nothing fo =
      ⊥-elim (Odd⇒¬Even {W ! proj₁ some-odd} (proj₂ some-odd) (firstOdd-nothing W fo (proj₁ some-odd)))
    by-first (just j) fo = by-j fo (toℕ j ℕP.≟ 0)

------------------------------------------------------------------------
-- Presentations of groups
--
-- The Main Lemma for the basic generator G = ω_[0] (Case 2 of the
-- proof of Lemma 3.10).  With v the pivot column of s, k its least
-- δ-exponent, w = δᵏ v and j the index of the first odd entry of w:
--
-- * j > 0: the syllable of s acts above 0, and is also the syllable of
--   r = ω_[0] s: a disjoint case;
-- * j = 0, k = 0: v = ωᵗ e_0, and the syllable of r, after ω_[0], is
--   that of s (or r = I when t = 7);
-- * j = 0, k > 0: with ℓ the second odd entry, the syllables are
--   H_[0,ℓ] ω_[0]ᶻ and H_[0,ℓ] ω_[0]ᶻ′ with z′ = z - 1 (mod 4): for
--   z > 0 the syllable of r, after ω_[0], is that of s; for z = 0 the
--   square closes through ω_[0]⁴ ω_[ℓ]⁴ X_[0,ℓ].
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)

module Examples.Groups.Clifford+T-2qubit-TwoLevel.CaseW {n : ℕ} where

open import Data.Bool.Base using (false ; _∧_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Integer.Base using (+_)
import Data.Integer.Properties as ℤP
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

open import Quantum.Synthesis.Matrix using (Matrix)

open import Notations using (auto)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Lde
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Residue using (zOf-ω ; pred4)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (first-nothing ; count ; count-one)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Norm using (NA ; Σℕ ; Unit ; lde0 ; evenodd ; P)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Column
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Pivot
  using (pivot ; pivot-just ; pivot-char ; level ; _<ₗ_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syllable
  using (syl ; step ; Beyond-actM ; eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; col𝕀≡)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Step using (pivot-zero> ; col-norm ; odd⇒≤)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Levels using (odd-ω ; Minimal-ω ; mono-level ; Bℓ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Derived {n}
  using (ω⁷-ω ; Hω⁴≈ω⁴ω⁴XH ; Apartʷ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Basic {n} using (Letters≤)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Reduction {n} using (Square ; Below ; path-ε)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.MainTools {n}
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
    r = actM (ω-gen a) s
    v = col s p
    W = num v

    v≡ : v ≡ scV (lde v) W
    v≡ = lde-eq v

    -- The facts that come from column-orthonormality, recomputed.
    zero> : ∀ x → p < x → W ! x ≡ ZR.0#
    zero> x px = recompute (W ! x ≟ᶻ ZR.0#) (pivot-zero> o ps x px)

    norm : + Σℕ (λ x → NA (W ! x)) ≡ P (lde v)
    norm = recompute (+ Σℕ (λ x → NA (W ! x)) ℤP.≟ P (lde v)) (col-norm o p)

    -- Nothing lies below 0.
    none<a : ∀ {x : Fin n} → x < a → ⊥
    none<a {x} x<a = ℕP.n≮0 (≡.subst (toℕ x ℕ.<_) a0 x<a)

    -- The column of r = ω_[0] s at the pivot.
    col-r : ∀ {K} {w : Vec Z n} → v ≡ scV K w → col r p ≡ scV K (ωᵛ a w)
    col-r {K} {w} e = ≡.trans (col-actM (ω-gen a) s p) (≡.trans (≡.cong (actV (ω-gen a)) e) (actV-ω a K w))

    lvl : level s ≡ (suc (toℕ p) , lde v , nodd W)
    lvl = level-of s ps (lde v) W v≡ (lde-min v)

  ----------------------------------------------------------------------
  -- j > 0: disjoint

  private
    disjoint : ∀ {j} → firstOdd W ≡ just j → a < j → Square (ω-gen a) s o
    disjoint {j} fo a<j = square-disjoint (ω-gen a) s o ps pr syl≡ apart lq
      where
      j≤p : j ≤ p
      j≤p = odd⇒≤ {p = p} {W} zero> (proj₁ (firstOdd-spec W fo))
      a<p : a < p
      a<p = ℕP.<-≤-trans a<j j≤p
      pr : pivot r ≡ just p
      pr = pivot-keep (ω-gen a) s a<p ps
      -- Entry a of W is even, so ω_[0] changes no odd entry.
      agree : ∀ x → Odd (ωᵛ a W ! x) → ωᵛ a W ! x ≡ W ! x
      agree x ox = at (x FinP.≟ a)
        where
        at : Dec (x ≡ a) → ωᵛ a W ! x ≡ W ! x
        at (yes ≡.refl) = ⊥-elim (Odd⇒¬Even {W ! x} (≡.trans (≡.sym (odd-ω a W x)) ox)
                                              (proj₂ (firstOdd-spec W fo) x a<j))
        at (no x≢a) = set₁-≢ a (ωᶻ ZR.* (W ! a)) W x≢a
      syl≡ : syl r ≡ syl s
      syl≡ = ≡.trans (syl-of r pr (lde v) (ωᵛ a W) (col-r v≡) (Minimal-ω a W (lde-min v)))
               (≡.trans (sylData-agree p (lde v) (ωᵛ a W) W (odd-ω a W) agree)
                 (≡.sym (syl-of s ps (lde v) W v≡ (lde-min v))))
      apart : Apartʷ (syl s) (ω-gen a)
      apart = ≡.subst (λ u → Apartʷ u (ω-gen a)) (≡.sym (syl-of s ps (lde v) W v≡ (lde-min v)))
                (above-apart (sylData p (lde v) W) (sylData-above p (lde v) W fo j≤p) a<j)
      lq : level (actM (ω-gen a) (step s)) <ₗ level s
      lq = mono-level (ω-gen a) tt FinP.≤-refl (step s) (lt-step s o ps)
             (≡.subst (Bℓ a <ₗ_) (≡.sym lvl) (inj₁ (s≤s a<p)))

  ----------------------------------------------------------------------
  -- j = 0, k = 0: v = ωᵗ e_0, and the syllable of r, after ω_[0], is
  -- that of s

  private
    scV-inj : ∀ k (u w : Vec Z n) → scV k u ≡ scV k w → u ≡ w
    scV-inj k u w eq = vec-ext λ x →
      sc-injective k (≡.trans (≡.sym (scV-! k u x)) (≡.trans (≡.cong (_! x) eq) (scV-! k w x)))
      where open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Scale using (sc-injective)

    -- The pivot column is a unit at 0.
    unit-facts : firstOdd W ≡ just a → lde v ≡ 0 →
                 ∃ λ t → t ℕ.< 8 × W ! a ≡ ωᶻ ^ᶻ t × (∀ y → y ≢ a → W ! y ≡ ZR.0#)
    unit-facts fo k0 = go (lde0 W (≡.trans norm (≡.cong P k0)))
      where
      go : (∃ λ m → Unit (W ! m) × (∀ y → y ≢ m → W ! y ≡ ZR.0#)) →
           ∃ λ t → t ℕ.< 8 × W ! a ≡ ωᶻ ^ᶻ t × (∀ y → y ≢ a → W ! y ≡ ZR.0#)
      go (m , (t , t<8 , um) , rest) = at (m FinP.≟ a)
        where
        at : Dec (m ≡ a) → ∃ λ t → t ℕ.< 8 × W ! a ≡ ωᶻ ^ᶻ t × (∀ y → y ≢ a → W ! y ≡ ZR.0#)
        at (yes m≡a) = t , t<8 , ≡.subst (λ x → W ! x ≡ ωᶻ ^ᶻ t) m≡a um ,
                       ≡.subst (λ x → ∀ y → y ≢ x → W ! y ≡ ZR.0#) m≡a rest
        at (no m≢a) = ⊥-elim (Odd⇒¬Even {W ! a} (proj₁ (firstOdd-spec W fo))
                                          (≡.cong oddᶻ (rest a (λ e → m≢a (≡.sym e)))))

    v≡₀ : lde v ≡ 0 → v ≡ scV 0 W
    v≡₀ k0 = ≡.trans v≡ (≡.cong (λ k → scV k W) k0)

    -- The relations, with the pivot above 0: the exponent of the
    -- syllable of r is one less (mod 8).
    unit-rel< : ∀ t → t ℕ.< 8 → {q : Fin n} .(aq : a < q) →
                (X a q aq • ω a ^ invExp (ωᶻ ZR.* (ωᶻ ^ᶻ t))) • ω a ≈ X a q aq • ω a ^ invExp (ωᶻ ^ᶻ t)
    unit-rel< 0 _ aq = trans assoc (cright ω⁷-ω)
    unit-rel< 1 _ aq = by-assoc auto
    unit-rel< 2 _ aq = by-assoc auto
    unit-rel< 3 _ aq = by-assoc auto
    unit-rel< 4 _ aq = by-assoc auto
    unit-rel< 5 _ aq = by-assoc auto
    unit-rel< 6 _ aq = by-assoc auto
    unit-rel< 7 _ aq = by-assoc auto
    unit-rel< (suc (suc (suc (suc (suc (suc (suc (suc t)))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))) aq

    unit< : firstOdd W ≡ just a → lde v ≡ 0 → a < p → Square (ω-gen a) s o
    unit< fo k0 a<p = go (unit-facts fo k0)
      where
      go : (∃ λ t → t ℕ.< 8 × W ! a ≡ ωᶻ ^ᶻ t × (∀ y → y ≢ a → W ! y ≡ ZR.0#)) → Square (ω-gen a) s o
      go (t , t<8 , ua , rest) = square-merge (ω-gen a) s o pr rel
        where
        pr : pivot r ≡ just p
        pr = pivot-keep (ω-gen a) s a<p ps
        fo′ : firstOdd (ωᵛ a W) ≡ just a
        fo′ = ≡.trans (firstOdd-cong (ωᵛ a W) W (odd-ω a W)) fo
        syl-r : syl r ≡ X a p a<p • ω a ^ invExp (ωᶻ ZR.* (ωᶻ ^ᶻ t))
        syl-r = ≡.trans (syl-of r pr 0 (ωᵛ a W) (col-r (v≡₀ k0)) (inj₁ ≡.refl))
                  (≡.trans (sylData-unit< (ωᵛ a W) fo′ a<p)
                    (≡.cong (λ z → X a p a<p • ω a ^ invExp z)
                            (≡.trans (set₁-a a (ωᶻ ZR.* (W ! a)) W) (≡.cong (ωᶻ ZR.*_) ua))))
        syl-s : syl s ≡ X a p a<p • ω a ^ invExp (ωᶻ ^ᶻ t)
        syl-s = ≡.trans (syl-of s ps 0 W (v≡₀ k0) (inj₁ ≡.refl))
                  (≡.trans (sylData-unit< W fo a<p) (≡.cong (λ z → X a p a<p • ω a ^ invExp z) ua))
        rel : syl r • ω a ≈ syl s
        rel = trans (cleft refl′ syl-r) (trans (unit-rel< t t<8 a<p) (refl′ (≡.sym syl-s)))

  ----------------------------------------------------------------------
  -- j = 0, k = 0, with the pivot at 0: for t = 7, r = I and the square
  -- closes with empty paths; otherwise the syllable of r, after
  -- ω_[0], is that of s

  private
    unit≡ : ∀ {q} → q ≡ p → firstOdd W ≡ just q → lde v ≡ 0 → ∀ t → t ℕ.< 8 → W ! q ≡ ωᶻ ^ᶻ t →
            (∀ y → y ≢ q → W ! y ≡ ZR.0#) → Square (ω-gen q) s o
    unit≡ ≡.refl fo k0 t t<8 ua rest = by-t t t<8 ua
      where
      rp = actM (ω-gen p) s

      col-rp : col rp p ≡ scV 0 (ωᵛ p W)
      col-rp = ≡.trans (col-actM (ω-gen p) s p) (≡.trans (≡.cong (actV (ω-gen p)) (v≡₀ k0)) (actV-ω p 0 W))

      fo′ : firstOdd (ωᵛ p W) ≡ just p
      fo′ = ≡.trans (firstOdd-cong (ωᵛ p W) W (odd-ω p W)) fo

      syl-s : ∀ {t} → W ! p ≡ ωᶻ ^ᶻ t → syl s ≡ ω p ^ invExp (ωᶻ ^ᶻ t)
      syl-s ua = ≡.trans (syl-of s ps 0 W (v≡₀ k0) (inj₁ ≡.refl))
                   (≡.trans (sylData-unit≡ W fo) (≡.cong (λ z → ω p ^ invExp z) ua))

      rp-p : ∀ {t} → W ! p ≡ ωᶻ ^ᶻ t → ωᵛ p W ! p ≡ ωᶻ ZR.* (ωᶻ ^ᶻ t)
      rp-p ua = ≡.trans (set₁-a p (ωᶻ ZR.* (W ! p)) W) (≡.cong (ωᶻ ZR.*_) ua)

      -- The pivot column of r is not that of I unless ω ωᵗ = 1.
      ne-of : ∀ {t} → W ! p ≡ ωᶻ ^ᶻ t → ωᶻ ZR.* (ωᶻ ^ᶻ t) ≢ ZR.1# → col rp p ≢ col 𝕀 p
      ne-of {t} ua bad eq = bad (≡.trans (≡.sym (rp-p {t} ua))
        (≡.trans (≡.cong (_! p) (scV-inj 0 (ωᵛ p W) (eᶻ p) (≡.trans (≡.sym col-rp) (≡.trans eq (col𝕀≡ p)))))
                 (≡.trans (eᶻ-! p p) (eδ-refl p))))

      merge : ∀ {t} → W ! p ≡ ωᶻ ^ᶻ t → ωᶻ ZR.* (ωᶻ ^ᶻ t) ≢ ZR.1# →
              ω p ^ invExp (ωᶻ ZR.* (ωᶻ ^ᶻ t)) • ω p ≈ ω p ^ invExp (ωᶻ ^ᶻ t) → Square (ω-gen p) s o
      merge {t} ua bad rel′ = square-merge (ω-gen p) s o pr rel
        where
        pr : pivot rp ≡ just p
        pr = pivot-char rp (ne-of {t} ua bad) (Beyond-actM (ω-gen p) {M = s} FinP.≤-refl (proj₂ (pivot-just s ps)))
        syl-r : syl rp ≡ ω p ^ invExp (ωᶻ ZR.* (ωᶻ ^ᶻ t))
        syl-r = ≡.trans (syl-of rp pr 0 (ωᵛ p W) col-rp (inj₁ ≡.refl))
                  (≡.trans (sylData-unit≡ (ωᵛ p W) fo′) (≡.cong (λ z → ω p ^ invExp z) (rp-p {t} ua)))
        rel : syl rp • ω p ≈ syl s
        rel = trans (cleft refl′ syl-r) (trans rel′ (refl′ (≡.sym (syl-s {t} ua))))

      by-t : ∀ t → t ℕ.< 8 → W ! p ≡ ωᶻ ^ᶻ t → Square (ω-gen p) s o
      -- t = 0: v = e_p would not be a pivot column.
      by-t 0 _ ua = ⊥-elim (proj₁ (pivot-just s ps) (≡.trans (v≡₀ k0) (≡.trans (≡.cong (scV 0) W≡e) (≡.sym (col𝕀≡ p)))))
        where
        at : ∀ x → Dec (x ≡ p) → W ! x ≡ eᶻ p ! x
        at x (yes ≡.refl) = ≡.trans ua (≡.sym (≡.trans (eᶻ-! x x) (eδ-refl x)))
        at x (no x≢p) = ≡.trans (rest x x≢p) (≡.sym (≡.trans (eᶻ-! p x) (eδ-≢ x≢p)))
        W≡e : W ≡ eᶻ p
        W≡e = vec-ext λ x → at x (x FinP.≟ p)
      by-t 1 _ ua = merge {1} ua (λ ()) (by-assoc auto)
      by-t 2 _ ua = merge {2} ua (λ ()) (by-assoc auto)
      by-t 3 _ ua = merge {3} ua (λ ()) (by-assoc auto)
      by-t 4 _ ua = merge {4} ua (λ ()) (by-assoc auto)
      by-t 5 _ ua = merge {5} ua (λ ()) (by-assoc auto)
      by-t 6 _ ua = merge {6} ua (λ ()) (by-assoc auto)
      by-t 7 _ ua = square-by (ω-gen p) s o ε ε (path-ε rp (ColOrth-actMʷ [ ω-gen p ]ʷ o)) tt
                      (cright refl′ (≡.sym (syl-s {7} ua)))
      by-t (suc (suc (suc (suc (suc (suc (suc (suc t)))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))) _

  ----------------------------------------------------------------------
  -- j = 0, k > 0: the second odd entry ℓ, and z drops by one

  private
    pair : firstOdd W ≡ just a → ∀ {K′} → lde v ≡ suc K′ → Square (ω-gen a) s o
    pair fo {K′} ks = withNext (nextOdd a W) ≡.refl
      where
      oa : Odd (W ! a)
      oa = proj₁ (firstOdd-spec W fo)

      withNext : (m : Maybe (Fin n)) → nextOdd a W ≡ m → Square (ω-gen a) s o
      -- By evenodd, a is not the only odd entry.
      withNext nothing nx =
        ⊥-elim (odd1 (≡.trans (≡.sym (≡.cong oddℕ cnt)) (evenodd K′ W (≡.trans norm (≡.cong P ks)))))
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
      withNext (just ℓ) nx = by-z (zOf (W ! a) (W ! ℓ)) (zOf-< (W ! a) (W ! ℓ)) ≡.refl
        where
        a<ℓ : a < ℓ
        a<ℓ = proj₁ (nextOdd-spec W nx)
        oℓ : Odd (W ! ℓ)
        oℓ = proj₁ (proj₂ (nextOdd-spec W nx))
        ℓ≤p : ℓ ≤ p
        ℓ≤p = odd⇒≤ {p = p} {W} zero> oℓ
        ℓ≢a : ℓ ≢ a
        ℓ≢a e = FinP.<-irrefl (≡.sym e) a<ℓ
        pr : pivot r ≡ just p
        pr = pivot-keep (ω-gen a) s (ℕP.<-≤-trans a<ℓ ℓ≤p) ps

        syl-s : syl s ≡ H a ℓ a<ℓ • ω a ^ zOf (W ! a) (W ! ℓ)
        syl-s = ≡.trans (syl-of s ps (lde v) W v≡ (lde-min v))
                  (≡.trans (≡.cong (λ k → sylData p k W) ks) (sylData-pair {p = p} K′ W fo nx a<ℓ))

        z≡ : zOf (ωᵛ a W ! a) (ωᵛ a W ! ℓ) ≡ pred4 (zOf (W ! a) (W ! ℓ))
        z≡ = ≡.trans (≡.cong₂ zOf (set₁-a a (ωᶻ ZR.* (W ! a)) W) (set₁-≢ a (ωᶻ ZR.* (W ! a)) W ℓ≢a))
                     (zOf-ω (W ! a) (W ! ℓ) oa oℓ)

        syl-r : syl r ≡ H a ℓ a<ℓ • ω a ^ pred4 (zOf (W ! a) (W ! ℓ))
        syl-r = ≡.trans (syl-of r pr (lde v) (ωᵛ a W) (col-r v≡) (Minimal-ω a W (lde-min v)))
                  (≡.trans (≡.cong (λ k → sylData p k (ωᵛ a W)) ks)
                    (≡.trans (sylData-pair {p = p} K′ (ωᵛ a W) fo′ nx′ a<ℓ)
                      (≡.cong (λ z → H a ℓ a<ℓ • ω a ^ z) z≡)))
          where
          fo′ : firstOdd (ωᵛ a W) ≡ just a
          fo′ = ≡.trans (firstOdd-cong (ωᵛ a W) W (odd-ω a W)) fo
          nx′ : nextOdd a (ωᵛ a W) ≡ just ℓ
          nx′ = ≡.trans (nextOdd-cong a (ωᵛ a W) W (odd-ω a W)) nx

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

        -- z > 0: the syllable of r, after ω_[0], is that of s.
        merge : ∀ z → zOf (W ! a) (W ! ℓ) ≡ suc z →
                (H a ℓ a<ℓ • ω a ^ z) • ω a ≈ H a ℓ a<ℓ • ω a ^ suc z → Square (ω-gen a) s o
        merge z e rel′ = square-merge (ω-gen a) s o pr
          (trans (cleft refl′ (≡.trans syl-r (≡.cong (λ z → H a ℓ a<ℓ • ω a ^ pred4 z) e)))
                 (trans rel′ (refl′ (≡.sym (≡.trans syl-s (≡.cong (λ z → H a ℓ a<ℓ • ω a ^ z) e))))))

        by-z : ∀ z → z ℕ.< 4 → zOf (W ! a) (W ! ℓ) ≡ z → Square (ω-gen a) s o
        -- z = 0: H_[0,ℓ] ω_[0]⁴ = ω_[0]⁴ ω_[ℓ]⁴ X_[0,ℓ] H_[0,ℓ].
        by-z 0 _ e =
          square-syl (ω-gen a) s o (H a ℓ a<ℓ • ω a ^ 3) G′ pr
            (≡.trans syl-r (≡.cong (λ z → H a ℓ a<ℓ • ω a ^ pred4 z) e))
            (below G′ ((a≤ℓ , a≤ℓ , a≤ℓ , a≤ℓ) , (ℕP.≤-refl , ℕP.≤-refl , ℕP.≤-refl , ℕP.≤-refl) , ℕP.≤-refl))
            (trans rel (cright refl′ (≡.sym (≡.trans syl-s (≡.cong (λ z → H a ℓ a<ℓ • ω a ^ z) e)))))
          where
          G′ = ω a ^ 4 • ω ℓ ^ 4 • X a ℓ a<ℓ
          rel : (H a ℓ a<ℓ • ω a ^ 3) • ω a ≈ G′ • (H a ℓ a<ℓ • ε)
          rel = begin
            (H a ℓ a<ℓ • ω a ^ 3) • ω a            ≈⟨ by-assoc auto ⟩
            H a ℓ a<ℓ • ω a ^ 4                    ≈⟨ Hω⁴≈ω⁴ω⁴XH a<ℓ ⟩
            ω a ^ 4 • ω ℓ ^ 4 • X a ℓ a<ℓ • H a ℓ a<ℓ ≈⟨ by-assoc auto ⟩
            G′ • (H a ℓ a<ℓ • ε)                   ∎
        by-z 1 _ e = merge 0 e (by-assoc auto)
        by-z 2 _ e = merge 1 e (by-assoc auto)
        by-z 3 _ e = merge 2 e (by-assoc auto)
        by-z (suc (suc (suc (suc _)))) (s≤s (s≤s (s≤s (s≤s ())))) _

  ----------------------------------------------------------------------
  -- The case, by the first odd entry j of w and by k

  private
    -- The pivot column has an odd entry.
    some-odd : ∃ λ x → Odd (W ! x)
    some-odd = from (lde v) ≡.refl
      where
      from : ∀ k → lde v ≡ k → ∃ λ x → Odd (W ! x)
      from zero k0 = unit-at (lde0 W (≡.trans norm (≡.cong P k0)))
        where
        unit-at : (∃ λ m → Unit (W ! m) × (∀ y → y ≢ m → W ! y ≡ ZR.0#)) → ∃ λ x → Odd (W ! x)
        unit-at (m , (t , t<8 , um) , _) = m , ≡.subst Odd (≡.sym um) (unit-odd t t<8)
      from (suc k) ks = minimal (≡.subst (λ k → Minimal k W) ks (lde-min v))
        where
        minimal : Minimal (suc k) W → ∃ λ x → Odd (W ! x)
        minimal (inj₁ ())
        minimal (inj₂ x) = x

  caseW : Square (ω-gen a) s o
  caseW = by-first (firstOdd W) ≡.refl
    where
    by-k : firstOdd W ≡ just a → ∀ k → lde v ≡ k → Square (ω-gen a) s o
    by-k fo zero k0 = unit (FinP.<-cmp a p) (unit-facts fo k0)
      where
      unit : Tri (a < p) (a ≡ p) (p < a) →
             (∃ λ t → t ℕ.< 8 × W ! a ≡ ωᶻ ^ᶻ t × (∀ y → y ≢ a → W ! y ≡ ZR.0#)) → Square (ω-gen a) s o
      unit (tri< a<p _ _) _ = unit< fo k0 a<p
      unit (tri≈ _ a≡p _) (t , t<8 , ua , rest) = unit≡ a≡p fo k0 t t<8 ua rest
      unit (tri> _ _ p<a) _ = ⊥-elim (none<a p<a)
    by-k fo (suc K′) ks = pair fo ks

    by-j : ∀ {j} → firstOdd W ≡ just j → Dec (toℕ j ≡ 0) → Square (ω-gen a) s o
    by-j fo (yes j0) =
      by-k (≡.subst (λ x → firstOdd W ≡ just x) (FinP.toℕ-injective (≡.trans j0 (≡.sym a0))) fo) (lde v) ≡.refl
    by-j {j} fo (no j≢0) = disjoint fo (≡.subst (ℕ._< toℕ j) (≡.sym a0) (ℕP.n≢0⇒n>0 j≢0))

    by-first : (m : Maybe (Fin n)) → firstOdd W ≡ m → Square (ω-gen a) s o
    by-first nothing fo =
      ⊥-elim (Odd⇒¬Even {W ! proj₁ some-odd} (proj₂ some-odd) (firstOdd-nothing W fo (proj₁ some-odd)))
    by-first (just j) fo = by-j fo (toℕ j ℕP.≟ 0)

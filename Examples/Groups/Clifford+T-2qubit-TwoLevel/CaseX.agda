------------------------------------------------------------------------
-- Presentations of groups
--
-- The Main Lemma for the basic generator G = X_[α,α+1] (Cases 3–5 of
-- the proof of Lemma 3.10), β = α + 1, but for one subcase, left as
-- the hypothesis Hard (proved in CaseXM).  With p the pivot, w the
-- numerator of the pivot column and k its least δ-exponent:
--
-- * α ≥ p: retrograde, G moves the pivot to β and the normal edge from
--   G s is X_[α,β];
-- * k = 0, w a unit at m: disjoint when m ∉ {α, β} and β < p; merging
--   or through X_[m,α] when β = p; through X_[α,β] otherwise;
-- * k > 0, with j < ℓ the first odd entries: disjoint when ℓ < α,
--   j < α < β < ℓ or β < j; through X_[α,β] when ℓ = α with w_β even,
--   ℓ = β with j < α, and β < ℓ with j ∈ {α, β}; for j = α, ℓ = β,
--   through ω_[β]⁴ or through (z₁)–(z₃), by the exponent.  The subcase
--   ℓ = α with w_β odd is Hard.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)

module Examples.Groups.Clifford+T-2qubit-TwoLevel.CaseX {n : ℕ} where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.List.Relation.Unary.All using ([] ; _∷_)
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_ ; ≢-sym)
open import Relation.Nullary using (Dec ; yes ; no)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Notations using (auto)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Residue using (neg4 ; zOf-sym)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Lde
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Column
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics hiding (_!_ ; U)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Pivot using (pivot ; pivot-just ; pivot-char ; level ; _<ₗ_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syllable
  using (syl ; step ; Within-^ ; Beyond-actM ; eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; col𝕀≡)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Levels using (Bℓ ; nodd-X ; Minimal-X)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Derived {n}
  using (X-X ; ωX≈Xω ; ωX≈Xω′ ; Hω³X ; Hω²X ; Hω¹X ; conj-^ ; flip-X ; Apartʷ ; Apartʷʷ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Basic {n} using (Letters≤)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Reduction {n} using (Square ; Below ; path-ε)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.MainTools {n}
  using (lt-step ; square-by ; square-disjoint′ ; square-retro ; square-merge ; square-syl ;
         syl-of ; level-of ; word-below-all ; above-apart′ ; within-apart ; Apartʷ-^ ;
         pivot-stay ; ne-𝕀 ; ne-𝕀-at ; bℓ-below)
import Examples.Groups.Clifford+T-2qubit-TwoLevel.PivotColumn as PivotColumn

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

------------------------------------------------------------------------
-- The relations of the squares, for j < k < l

private
  -- X_[j,l] X_[k,l] = X_[j,k] X_[j,l], by (13) and (12).
  XX₁ : ∀ {j k l : Fin n} (jk : j < k) (kl : k < l) →
        X j l (FinP.<-trans jk kl) • X k l kl ≈ X j k jk • X j l (FinP.<-trans jk kl)
  XX₁ jk kl = trans (sym (axiom (swap-XX′ jk kl))) (sym (axiom (swap-XX jk kl)))

  -- H_[j,l] X_[k,l] = X_[k,l] H_[j,k], by (15); H_[k,l] X_[j,k] = X_[j,k] H_[j,l], by (14).
  HX₁ : ∀ {j k l : Fin n} (jk : j < k) (kl : k < l) → H j l (FinP.<-trans jk kl) • X k l kl ≈ X k l kl • H j k jk
  HX₁ jk kl = sym (axiom (swap-XH′ jk kl))

  HX₂ : ∀ {j k l : Fin n} (jk : j < k) (kl : k < l) → H k l kl • X j k jk ≈ X j k jk • H j l (FinP.<-trans jk kl)
  HX₂ jk kl = sym (axiom (swap-XH jk kl))

  -- ω_[j] commutes with X_[k,l].
  ωX-comm : ∀ {j k l : Fin n} (jk : j < k) (kl : k < l) → ω j • X k l kl ≈ X k l kl • ω j
  ωX-comm jk kl = axiom (comm-ωX kl (FinP.<⇒≢ jk) (FinP.<⇒≢ (FinP.<-trans jk kl)))

  -- The syllable X_[j,l] ω_[j]ᶠ, with X_[k,l].
  R-X-X : ∀ {j k l : Fin n} (jk : j < k) (kl : k < l) f →
          (X j l (FinP.<-trans jk kl) • ω j ^ f) • X k l kl ≈ X j k jk • (X j l (FinP.<-trans jk kl) • ω j ^ f)
  R-X-X {j} {k} {l} jk kl f = begin
    (X j l jl • ω j ^ f) • X k l kl       ≈⟨ assoc ⟩
    X j l jl • (ω j ^ f • X k l kl)       ≈⟨ cright conj-^ (ωX-comm jk kl) f ⟩
    X j l jl • (X k l kl • ω j ^ f)       ≈⟨ sym assoc ⟩
    (X j l jl • X k l kl) • ω j ^ f       ≈⟨ cleft XX₁ jk kl ⟩
    (X j k jk • X j l jl) • ω j ^ f       ≈⟨ assoc ⟩
    X j k jk • (X j l jl • ω j ^ f)       ∎
    where jl = FinP.<-trans jk kl

  -- The syllable X_[k,l] ω_[k]ᶠ, with X_[j,k].
  R-X-ω : ∀ {j k l : Fin n} (jk : j < k) (kl : k < l) f →
          (X k l kl • ω k ^ f) • X j k jk ≈ X j k jk • (X j l (FinP.<-trans jk kl) • ω j ^ f)
  R-X-ω {j} {k} {l} jk kl f = begin
    (X k l kl • ω k ^ f) • X j k jk       ≈⟨ assoc ⟩
    X k l kl • (ω k ^ f • X j k jk)       ≈⟨ cright conj-^ (ωX≈Xω jk) f ⟩
    X k l kl • (X j k jk • ω j ^ f)       ≈⟨ sym assoc ⟩
    (X k l kl • X j k jk) • ω j ^ f       ≈⟨ cleft sym (axiom (swap-XX jk kl)) ⟩
    (X j k jk • X j l jl) • ω j ^ f       ≈⟨ assoc ⟩
    X j k jk • (X j l jl • ω j ^ f)       ∎
    where jl = FinP.<-trans jk kl

  -- Merging.
  R-merge : ∀ {j k : Fin n} (jk : j < k) f → (X j k jk • ω j ^ f) • X j k jk ≈ ω k ^ f
  R-merge {j} {k} jk f = begin
    (X j k jk • ω j ^ f) • X j k jk       ≈⟨ assoc ⟩
    X j k jk • (ω j ^ f • X j k jk)       ≈⟨ cright conj-^ (ωX≈Xω′ jk) f ⟩
    X j k jk • (X j k jk • ω k ^ f)       ≈⟨ sym assoc ⟩
    (X j k jk • X j k jk) • ω k ^ f       ≈⟨ cleft X-X jk ⟩
    ε • ω k ^ f                           ≈⟨ left-unit ⟩
    ω k ^ f                               ∎

  -- The syllable H_[j,l] ω_[j]ᶻ, with X_[k,l].
  R-H-X : ∀ {j k l : Fin n} (jk : j < k) (kl : k < l) z →
          (H j l (FinP.<-trans jk kl) • ω j ^ z) • X k l kl ≈ X k l kl • (H j k jk • ω j ^ z)
  R-H-X {j} {k} {l} jk kl z = begin
    (H j l jl • ω j ^ z) • X k l kl       ≈⟨ assoc ⟩
    H j l jl • (ω j ^ z • X k l kl)       ≈⟨ cright conj-^ (ωX-comm jk kl) z ⟩
    H j l jl • (X k l kl • ω j ^ z)       ≈⟨ sym assoc ⟩
    (H j l jl • X k l kl) • ω j ^ z       ≈⟨ cleft HX₁ jk kl ⟩
    (X k l kl • H j k jk) • ω j ^ z       ≈⟨ assoc ⟩
    X k l kl • (H j k jk • ω j ^ z)       ∎
    where jl = FinP.<-trans jk kl

  -- The syllable H_[k,l] ω_[k]ᶻ, with X_[j,k].
  R-X-H : ∀ {j k l : Fin n} (jk : j < k) (kl : k < l) z →
          (H k l kl • ω k ^ z) • X j k jk ≈ X j k jk • (H j l (FinP.<-trans jk kl) • ω j ^ z)
  R-X-H {j} {k} {l} jk kl z = begin
    (H k l kl • ω k ^ z) • X j k jk       ≈⟨ assoc ⟩
    H k l kl • (ω k ^ z • X j k jk)       ≈⟨ cright conj-^ (ωX≈Xω jk) z ⟩
    H k l kl • (X j k jk • ω j ^ z)       ≈⟨ sym assoc ⟩
    (H k l kl • X j k jk) • ω j ^ z       ≈⟨ cleft HX₂ jk kl ⟩
    (X j k jk • H j l jl) • ω j ^ z       ≈⟨ assoc ⟩
    X j k jk • (H j l jl • ω j ^ z)       ∎
    where jl = FinP.<-trans jk kl

------------------------------------------------------------------------
-- α and β = α + 1

module Common (α β : Fin n) (αβ1 : toℕ β ≡ suc (toℕ α)) where

  αβ : α < β
  αβ = ≡.subst (suc (toℕ α) ℕ.≤_) (≡.sym αβ1) ℕP.≤-refl

  G : Gen n
  G = X-gen α β αβ

  α≢β : α ≢ β
  α≢β = FinP.<⇒≢ αβ

  -- Nothing lies between α and β.
  none-αβ : ∀ {x : Fin n} → α < x → x < β → ⊥
  none-αβ {x} αx xβ = ℕP.<-irrefl ≡.refl (ℕP.<-≤-trans xβ (≡.subst (ℕ._≤ toℕ x) (≡.sym αβ1) αx))

  β≤ : ∀ {x : Fin n} → α < x → β ≤ x
  β≤ {x} αx = ≡.subst (ℕ._≤ toℕ x) (≡.sym αβ1) αx

  ≤α : ∀ {x : Fin n} → x < β → x ≤ α
  ≤α {x} xβ = ℕP.≤-pred (≡.subst (suc (toℕ x) ℕ.≤_) αβ1 xβ)

  -- x < β and x ≢ α give x < α; α < x and x ≢ β give β < x.
  <α : ∀ {x : Fin n} → x < β → x ≢ α → x < α
  <α {x} xβ x≢α = ℕP.≤∧≢⇒< (≤α xβ) (λ e → x≢α (FinP.toℕ-injective e))

  β< : ∀ {x : Fin n} → α < x → x ≢ β → β < x
  β< {x} αx x≢β = ℕP.≤∧≢⇒< (β≤ αx) (λ e → x≢β (FinP.toℕ-injective (≡.sym e)))

  -- X_[α,β] on numerators swaps the entries α and β.
  Xᶻ-α : (U : Vec Z n) → Xᶻ α β U ! α ≡ U ! β
  Xᶻ-α U = set₂-a α β (U ! β) (U ! α) U

  Xᶻ-β : (U : Vec Z n) → Xᶻ α β U ! β ≡ U ! α
  Xᶻ-β U = set₂-b α β (U ! β) (U ! α) U α≢β

  Xᶻ-≢ : (U : Vec Z n) {x : Fin n} → x ≢ α → x ≢ β → Xᶻ α β U ! x ≡ U ! x
  Xᶻ-≢ U x≢α x≢β = set₂-≢ α β (U ! β) (U ! α) U x≢α x≢β

  Xᶻ-same : (U : Vec Z n) → U ! α ≡ U ! β → Xᶻ α β U ≡ U
  Xᶻ-same U e = vec-ext λ x → at x (x FinP.≟ α) (x FinP.≟ β)
    where
    at : ∀ x → Dec (x ≡ α) → Dec (x ≡ β) → Xᶻ α β U ! x ≡ U ! x
    at x (yes ≡.refl) _ = ≡.trans (Xᶻ-α U) (≡.sym e)
    at x (no _) (yes ≡.refl) = ≡.trans (Xᶻ-β U) e
    at x (no x≢α) (no x≢β) = Xᶻ-≢ U x≢α x≢β

  -- An entry of Xᶻ α β U is even, from the entry of U it comes from.
  even-X : (U : Vec Z n) (x : Fin n) → (x ≡ α → Even (U ! β)) → (x ≡ β → Even (U ! α)) →
           (x ≢ α → x ≢ β → Even (U ! x)) → Even (Xᶻ α β U ! x)
  even-X U x hα hβ h = at (x FinP.≟ α) (x FinP.≟ β)
    where
    at : Dec (x ≡ α) → Dec (x ≡ β) → Even (Xᶻ α β U ! x)
    at (yes x≡α) _ = ≡.subst (λ y → Even (Xᶻ α β U ! y)) (≡.sym x≡α) (≡.trans (≡.cong oddᶻ (Xᶻ-α U)) (hα x≡α))
    at (no _) (yes x≡β) = ≡.subst (λ y → Even (Xᶻ α β U ! y)) (≡.sym x≡β) (≡.trans (≡.cong oddᶻ (Xᶻ-β U)) (hβ x≡β))
    at (no x≢α) (no x≢β) = ≡.trans (≡.cong oddᶻ (Xᶻ-≢ U x≢α x≢β)) (h x≢α x≢β)

------------------------------------------------------------------------
-- k = 0 with the pivot at β

module Top (α β : Fin n) (αβ1 : toℕ β ≡ suc (toℕ α))
           (s : Matrix n n D) .(o : ColOrth s) (ps : pivot s ≡ just β) where

  open Common α β αβ1
  open PivotColumn s o ps

  private
    r = actM G s

    col-r : ∀ {K} {U : Vec Z n} → v ≡ scV K U → col r β ≡ scV K (Xᶻ α β U)
    col-r {K} {U} e = ≡.trans (col-actM G s β) (≡.trans (≡.cong (actV G) e) (actV-X α β αβ K U))

    0≢1 : ZR.0# ≢ ZR.1#
    0≢1 ()

  top0 : lde v ≡ 0 → Square G s o
  top0 k0 = go (unit k0)
    where
    v≡₀ : v ≡ scV 0 W
    v≡₀ = ≡.trans v≡ (≡.cong (λ k → scV k W) k0)

    -- The unit at α.
    at-α : ∀ {m} → m ≡ α → firstOdd W ≡ just m → ∀ t → t ℕ.< 8 → W ! m ≡ ωᶻ ^ᶻ t →
           (∀ y → y ≢ m → W ! y ≡ ZR.0#) → Square G s o
    at-α ≡.refl fo t t<8 ua rest = by-t t t<8 ua
      where
      U = Xᶻ α β W
      syl-s : ∀ {t} → W ! α ≡ ωᶻ ^ᶻ t → syl s ≡ X α β αβ • ω α ^ invExp (ωᶻ ^ᶻ t)
      syl-s ua = ≡.trans (syl-of s ps 0 W v≡₀ (inj₁ ≡.refl))
                   (≡.trans (sylData-unit< W fo αβ) (≡.cong (λ z → X α β αβ • ω α ^ invExp z) ua))
      foU : firstOdd U ≡ just β
      foU = firstOdd-char U (≡.subst Odd (≡.sym (Xᶻ-β W)) (proj₁ (firstOdd-spec W fo)))
              (λ x xβ → even-X W x (λ _ → ≡.cong oddᶻ (rest β (≢-sym α≢β))) (λ x≡β → ⊥-elim (FinP.<-irrefl x≡β xβ))
                                   (λ x≢α _ → ≡.cong oddᶻ (rest x x≢α)))
      -- The syllable of r, after G, is that of s.
      merge : ∀ {t} → W ! α ≡ ωᶻ ^ᶻ t → ωᶻ ^ᶻ t ≢ ZR.1# → Square G s o
      merge {t} ua bad = square-merge G s o pr rel
        where
        pr : pivot r ≡ just β
        pr = pivot-stay G s FinP.≤-refl ps
               (ne-𝕀-at r β 0 U (col-r v≡₀) (inj₁ ≡.refl) β
                 (λ e → bad (≡.trans (≡.sym (≡.trans (Xᶻ-β W) ua)) (≡.trans e (≡.trans (eᶻ-! β β) (eδ-refl β))))))
        syl-r : syl r ≡ ω β ^ invExp (ωᶻ ^ᶻ t)
        syl-r = ≡.trans (syl-of r pr 0 U (col-r v≡₀) (inj₁ ≡.refl))
                  (≡.trans (sylData-unit≡ U foU) (≡.cong (λ z → ω β ^ invExp z) (≡.trans (Xᶻ-β W) ua)))
        rel : syl r • X α β αβ ≈ syl s
        rel = trans (cleft refl′ syl-r)
                (trans (conj-^ (ωX≈Xω αβ) (invExp (ωᶻ ^ᶻ t))) (refl′ (≡.sym (syl-s {t} ua))))
      by-t : ∀ t → t ℕ.< 8 → W ! α ≡ ωᶻ ^ᶻ t → Square G s o
      -- t = 0: G s has the column e_β, and the square closes with empty
      -- paths.
      by-t 0 _ ua = square-by G s o ε ε (path-ε r (ColOrth-actMʷ [ G ]ʷ o)) tt
                      (trans left-unit (trans (sym right-unit) (trans (refl′ (≡.sym (syl-s {0} ua))) (sym left-unit))))
      by-t 1 _ ua = merge {1} ua (λ ())
      by-t 2 _ ua = merge {2} ua (λ ())
      by-t 3 _ ua = merge {3} ua (λ ())
      by-t 4 _ ua = merge {4} ua (λ ())
      by-t 5 _ ua = merge {5} ua (λ ())
      by-t 6 _ ua = merge {6} ua (λ ())
      by-t 7 _ ua = merge {7} ua (λ ())
      by-t (suc (suc (suc (suc (suc (suc (suc (suc t)))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))) _

    -- The unit at β.
    at-β : ∀ {m} → m ≡ β → firstOdd W ≡ just m → ∀ t → t ℕ.< 8 → W ! m ≡ ωᶻ ^ᶻ t →
           (∀ y → y ≢ m → W ! y ≡ ZR.0#) → Square G s o
    at-β ≡.refl fo t t<8 ua rest = by-t t t<8 ua
      where
      U = Xᶻ α β W
      Wα : W ! α ≡ ZR.0#
      Wα = rest α α≢β
      foU : firstOdd U ≡ just α
      foU = firstOdd-char U (≡.subst Odd (≡.sym (Xᶻ-α W)) (proj₁ (firstOdd-spec W fo)))
              (λ x xα → ≡.cong oddᶻ (≡.trans (Xᶻ-≢ W (FinP.<⇒≢ xα) (FinP.<⇒≢ (ℕP.<-trans xα αβ)))
                                            (rest x (FinP.<⇒≢ (ℕP.<-trans xα αβ)))))
      pr : pivot r ≡ just β
      pr = pivot-stay G s FinP.≤-refl ps
             (ne-𝕀-at r β 0 U (col-r v≡₀) (inj₁ ≡.refl) β
               (λ e → 0≢1 (≡.trans (≡.sym (≡.trans (Xᶻ-β W) Wα)) (≡.trans e (≡.trans (eᶻ-! β β) (eδ-refl β))))))
      merge : ∀ {t} → W ! β ≡ ωᶻ ^ᶻ t → Square G s o
      merge {t} ua = square-merge G s o pr rel
        where
        syl-r : syl r ≡ X α β αβ • ω α ^ invExp (ωᶻ ^ᶻ t)
        syl-r = ≡.trans (syl-of r pr 0 U (col-r v≡₀) (inj₁ ≡.refl))
                  (≡.trans (sylData-unit< U foU αβ) (≡.cong (λ z → X α β αβ • ω α ^ invExp z) (≡.trans (Xᶻ-α W) ua)))
        syl-s : syl s ≡ ω β ^ invExp (ωᶻ ^ᶻ t)
        syl-s = ≡.trans (syl-of s ps 0 W v≡₀ (inj₁ ≡.refl))
                  (≡.trans (sylData-unit≡ W fo) (≡.cong (λ z → ω β ^ invExp z) ua))
        rel : syl r • X α β αβ ≈ syl s
        rel = trans (cleft refl′ syl-r) (trans (R-merge αβ (invExp (ωᶻ ^ᶻ t))) (refl′ (≡.sym syl-s)))
      by-t : ∀ t → t ℕ.< 8 → W ! β ≡ ωᶻ ^ᶻ t → Square G s o
      -- t = 0: v = e_β would not be a pivot column.
      by-t 0 _ ua = ⊥-elim (proj₁ (pivot-just s ps) (≡.trans v≡₀ (≡.trans (≡.cong (scV 0) W≡e) (≡.sym (col𝕀≡ β)))))
        where
        at : ∀ x → Dec (x ≡ β) → W ! x ≡ eᶻ β ! x
        at x (yes ≡.refl) = ≡.trans ua (≡.sym (≡.trans (eᶻ-! x x) (eδ-refl x)))
        at x (no x≢β) = ≡.trans (rest x x≢β) (≡.sym (≡.trans (eᶻ-! β x) (eδ-≢ x≢β)))
        W≡e : W ≡ eᶻ β
        W≡e = vec-ext λ x → at x (x FinP.≟ β)
      by-t 1 _ ua = merge {1} ua
      by-t 2 _ ua = merge {2} ua
      by-t 3 _ ua = merge {3} ua
      by-t 4 _ ua = merge {4} ua
      by-t 5 _ ua = merge {5} ua
      by-t 6 _ ua = merge {6} ua
      by-t 7 _ ua = merge {7} ua
      by-t (suc (suc (suc (suc (suc (suc (suc (suc t)))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))) _

    go : (∃ λ m → firstOdd W ≡ just m × ∃ λ t → t ℕ.< 8 × W ! m ≡ ωᶻ ^ᶻ t × (∀ y → y ≢ m → W ! y ≡ ZR.0#)) →
         Square G s o
    go (m , fo , t , t<8 , um , rest) = by-m (FinP.<-cmp m α)
      where
      m≤β : m ≤ β
      m≤β = odd≤ (proj₁ (firstOdd-spec W fo))
      by-m : Tri (m < α) (m ≡ α) (α < m) → Square G s o
      -- m < α: the syllable stays, and the square closes through X_[m,α].
      by-m (tri< m<α _ _) = square-syl G s o (syl s) (X m α m<α) pr syl-r below rel
        where
        m<β = FinP.<-trans m<α αβ
        f = invExp (W ! m)
        col≡ : col r β ≡ col s β
        col≡ = ≡.trans (col-r v≡₀)
                 (≡.trans (≡.cong (scV 0) (Xᶻ-same W (≡.trans (rest α (λ e → FinP.<-irrefl (≡.sym e) m<α))
                                                              (≡.sym (rest β (λ e → FinP.<-irrefl (≡.sym e) m<β))))))
                          (≡.sym v≡₀))
        pr : pivot r ≡ just β
        pr = pivot-stay G s FinP.≤-refl ps (λ e → proj₁ (pivot-just s ps) (≡.trans (≡.sym col≡) e))
        syl-r : syl r ≡ syl s
        syl-r = ≡.trans (syl-of r pr 0 W (≡.trans col≡ v≡₀) (inj₁ ≡.refl)) (≡.sym (syl-of s ps 0 W v≡₀ (inj₁ ≡.refl)))
        syl-s : syl s ≡ X m β m<β • ω m ^ f
        syl-s = ≡.trans (syl-of s ps 0 W v≡₀ (inj₁ ≡.refl)) (sylData-unit< W fo m<β)
        below : Below (level s) (X m α m<α) (step s)
        below = word-below-all (X m α m<α) ℕP.≤-refl (step s) (lt-step s o ps)
                  (≡.subst (Bℓ α <ₗ_) (≡.sym lvl) (inj₁ (s≤s αβ)))
        rel : syl s • X α β αβ ≈ X m α m<α • syl s
        rel = trans (cleft refl′ syl-s) (trans (R-X-X m<α αβ f) (cright refl′ (≡.sym syl-s)))
      by-m (tri≈ _ m≡α _) = at-α m≡α fo t t<8 um rest
      by-m (tri> _ _ α<m) = at-β (FinP.≤-antisym m≤β (β≤ α<m)) fo t t<8 um rest

------------------------------------------------------------------------
-- The case

module _ (α β : Fin n) (αβ1 : toℕ β ≡ suc (toℕ α))
         (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p) where

  open Common α β αβ1
  open PivotColumn s o ps

  -- The subcase left to CaseXM: k > 0, the first two odd entries are
  -- j < α, and w_β is odd.
  Hard : Set
  Hard = ∀ {K′ j} → lde v ≡ suc K′ → firstOdd W ≡ just j → nextOdd j W ≡ just α → Odd (W ! β) →
         Square (X-gen α β αβ) s o

  private
    r = actM G s

    col-r : ∀ {K} {U : Vec Z n} → v ≡ scV K U → col r p ≡ scV K (Xᶻ α β U)
    col-r {K} {U} e = ≡.trans (col-actM G s p) (≡.trans (≡.cong (actV G) e) (actV-X α β αβ K U))

    ------------------------------------------------------------------
    -- α ≥ p: retrograde

    retro : p ≤ α → Square G s o
    retro p≤α = square-retro G s o ps pr back
      where
      p<β : p < β
      p<β = ℕP.≤-<-trans p≤α αβ
      U = Xᶻ α β (eᶻ β)
      colβ : col r β ≡ scV 0 U
      colβ = ≡.trans (col-actM G s β)
               (≡.trans (≡.cong (actV G) (≡.trans (proj₂ (pivot-just s ps) β p<β) (col𝕀≡ β)))
                        (actV-X α β αβ 0 (eᶻ β)))
      Uα : U ! α ≡ ZR.1#
      Uα = ≡.trans (Xᶻ-α (eᶻ β)) (≡.trans (eᶻ-! β β) (eδ-refl β))
      Uβ : U ! β ≡ ZR.0#
      Uβ = ≡.trans (Xᶻ-β (eᶻ β)) (≡.trans (eᶻ-! β α) (eδ-≢ α≢β))
      fo : firstOdd U ≡ just α
      fo = firstOdd-char U (≡.cong oddᶻ Uα)
             (λ x xα → ≡.cong oddᶻ (≡.trans (Xᶻ-≢ (eᶻ β) (FinP.<⇒≢ xα) (FinP.<⇒≢ (ℕP.<-trans xα αβ)))
                                          (≡.trans (eᶻ-! β x) (eδ-≢ (FinP.<⇒≢ (ℕP.<-trans xα αβ))))))
      ne : col r β ≢ col 𝕀 β
      ne = ne-𝕀-at r β 0 U colβ (inj₁ ≡.refl) β
             (λ e → 0≢1 (≡.trans (≡.sym Uβ) (≡.trans e (≡.trans (eᶻ-! β β) (eδ-refl β)))))
        where
        0≢1 : ZR.0# ≢ ZR.1#
        0≢1 ()
      pr : pivot r ≡ just β
      pr = pivot-char r ne (Beyond-actM G {M = s} FinP.≤-refl
                              (λ c β<c → proj₂ (pivot-just s ps) c (ℕP.<-trans p<β β<c)))
      syl-r : syl r ≡ X α β αβ • ε
      syl-r = ≡.trans (syl-of r pr 0 U colβ (inj₁ ≡.refl))
                (≡.trans (sylData-unit< U fo αβ) (≡.cong (λ z → X α β αβ • ω α ^ invExp z) Uα))
      back : syl r • [ G ]ʷ ≈ ε
      back = trans (cleft refl′ syl-r) (trans (cleft right-unit) (X-X αβ))

    ------------------------------------------------------------------
    -- k = 0 and β < p

    case0 : lde v ≡ 0 → β < p → Square G s o
    case0 k0 β<p = go (unit k0)
      where
      v≡₀ : v ≡ scV 0 W
      v≡₀ = ≡.trans v≡ (≡.cong (λ k → scV k W) k0)
      α<p : α < p
      α<p = ℕP.<-trans αβ β<p
      p≢α : p ≢ α
      p≢α e = FinP.<-irrefl (≡.sym e) α<p
      p≢β : p ≢ β
      p≢β e = FinP.<-irrefl (≡.sym e) β<p
      bβ : Bℓ β <ₗ level s
      bβ = ≡.subst (Bℓ β <ₗ_) (≡.sym lvl) (inj₁ (s≤s β<p))

      go : (∃ λ m → firstOdd W ≡ just m × ∃ λ t → t ℕ.< 8 × W ! m ≡ ωᶻ ^ᶻ t × (∀ y → y ≢ m → W ! y ≡ ZR.0#)) →
           Square G s o
      go (m , fo , t , t<8 , um , rest) = by-m (FinP.<-cmp m α)
        where
        om : Odd (W ! m)
        om = proj₁ (firstOdd-spec W fo)
        m≤p : m ≤ p
        m≤p = odd≤ om
        f = invExp (W ! m)
        -- The unit at neither α nor β: disjoint.
        same : m ≢ α → m ≢ β → Apartʷ (syl s) G → Square G s o
        same m≢α m≢β ap = square-disjoint′ G s o ps pr syl-r ap lv
          where
          col≡ : col r p ≡ col s p
          col≡ = ≡.trans (col-r v≡₀)
                   (≡.trans (≡.cong (scV 0) (Xᶻ-same W (≡.trans (rest α (≢-sym m≢α)) (≡.sym (rest β (≢-sym m≢β))))))
                            (≡.sym v≡₀))
          pr : pivot r ≡ just p
          pr = pivot-stay G s (ℕP.<⇒≤ β<p) ps (λ e → proj₁ (pivot-just s ps) (≡.trans (≡.sym col≡) e))
          syl-r : syl r ≡ syl s
          syl-r = ≡.trans (syl-of r pr (lde v) W (≡.trans col≡ v≡) min) (≡.sym syl≡)
          lv : level r ≡ level s
          lv = ≡.trans (level-of r pr (lde v) W (≡.trans col≡ v≡) min) (≡.sym lvl)
        -- The unit at α or β: G moves it.
        at-α : ∀ {m′} → m′ ≡ α → firstOdd W ≡ just m′ → W ! m′ ≡ ωᶻ ^ᶻ t → (∀ y → y ≢ m′ → W ! y ≡ ZR.0#) →
               Square G s o
        at-α ≡.refl fo′ ua rest′ =
          square-syl G s o (X β p β<p • ω β ^ invExp (ωᶻ ^ᶻ t)) (X α β αβ) pr syl-r
            (word-below-all (X α β αβ) ℕP.≤-refl (step s) (lt-step s o ps) bβ)
            (trans (R-X-ω αβ β<p (invExp (ωᶻ ^ᶻ t))) (cright refl′ (≡.sym syl-s)))
          where
          U = Xᶻ α β W
          foU : firstOdd U ≡ just β
          foU = firstOdd-char U (≡.subst Odd (≡.sym (Xᶻ-β W)) (proj₁ (firstOdd-spec W fo′)))
                  (λ x xβ → even-X W x (λ _ → ≡.cong oddᶻ (rest′ β (≢-sym α≢β)))
                                       (λ x≡β → ⊥-elim (FinP.<-irrefl x≡β xβ))
                                       (λ x≢α _ → ≡.cong oddᶻ (rest′ x x≢α)))
          pr : pivot r ≡ just p
          pr = pivot-stay G s (ℕP.<⇒≤ β<p) ps
                 (ne-𝕀-at r p 0 U (col-r v≡₀) (inj₁ ≡.refl) p
                   (λ e → 0≢1 (≡.trans (≡.sym (≡.trans (Xᶻ-≢ W p≢α p≢β) (rest′ p p≢α)))
                                       (≡.trans e (≡.trans (eᶻ-! p p) (eδ-refl p))))))
            where
            0≢1 : ZR.0# ≢ ZR.1#
            0≢1 ()
          syl-r : syl r ≡ X β p β<p • ω β ^ invExp (ωᶻ ^ᶻ t)
          syl-r = ≡.trans (syl-of r pr 0 U (col-r v≡₀) (inj₁ ≡.refl))
                    (≡.trans (sylData-unit< U foU β<p)
                             (≡.cong (λ z → X β p β<p • ω β ^ invExp z) (≡.trans (Xᶻ-β W) ua)))
          syl-s : syl s ≡ X α p α<p • ω α ^ invExp (ωᶻ ^ᶻ t)
          syl-s = ≡.trans (syl-of s ps 0 W v≡₀ (inj₁ ≡.refl))
                    (≡.trans (sylData-unit< W fo′ α<p) (≡.cong (λ z → X α p α<p • ω α ^ invExp z) ua))
        at-β : ∀ {m′} → m′ ≡ β → firstOdd W ≡ just m′ → W ! m′ ≡ ωᶻ ^ᶻ t → (∀ y → y ≢ m′ → W ! y ≡ ZR.0#) →
               Square G s o
        at-β ≡.refl fo′ ua rest′ =
          square-syl G s o (X α p α<p • ω α ^ invExp (ωᶻ ^ᶻ t)) (X α β αβ) pr syl-r
            (word-below-all (X α β αβ) ℕP.≤-refl (step s) (lt-step s o ps) bβ)
            (trans (flip-X αβ (R-X-ω αβ β<p (invExp (ωᶻ ^ᶻ t)))) (cright refl′ (≡.sym syl-s)))
          where
          U = Xᶻ α β W
          foU : firstOdd U ≡ just α
          foU = firstOdd-char U (≡.subst Odd (≡.sym (Xᶻ-α W)) (proj₁ (firstOdd-spec W fo′)))
                  (λ x xα → ≡.cong oddᶻ (≡.trans (Xᶻ-≢ W (FinP.<⇒≢ xα) (FinP.<⇒≢ (ℕP.<-trans xα αβ)))
                                                (rest′ x (FinP.<⇒≢ (ℕP.<-trans xα αβ)))))
          pr : pivot r ≡ just p
          pr = pivot-stay G s (ℕP.<⇒≤ β<p) ps
                 (ne-𝕀-at r p 0 U (col-r v≡₀) (inj₁ ≡.refl) p
                   (λ e → 0≢1 (≡.trans (≡.sym (≡.trans (Xᶻ-≢ W p≢α p≢β) (rest′ p p≢β)))
                                       (≡.trans e (≡.trans (eᶻ-! p p) (eδ-refl p))))))
            where
            0≢1 : ZR.0# ≢ ZR.1#
            0≢1 ()
          syl-r : syl r ≡ X α p α<p • ω α ^ invExp (ωᶻ ^ᶻ t)
          syl-r = ≡.trans (syl-of r pr 0 U (col-r v≡₀) (inj₁ ≡.refl))
                    (≡.trans (sylData-unit< U foU α<p)
                             (≡.cong (λ z → X α p α<p • ω α ^ invExp z) (≡.trans (Xᶻ-α W) ua)))
          syl-s : syl s ≡ X β p β<p • ω β ^ invExp (ωᶻ ^ᶻ t)
          syl-s = ≡.trans (syl-of s ps 0 W v≡₀ (inj₁ ≡.refl))
                    (≡.trans (sylData-unit< W fo′ β<p) (≡.cong (λ z → X β p β<p • ω β ^ invExp z) ua))

        by-m : Tri (m < α) (m ≡ α) (α < m) → Square G s o
        by-m (tri< m<α _ _) = same m≢α m≢β
            (≡.subst (λ w → Apartʷ w G) (≡.sym syl-s)
              ((m≢α ∷ m≢β ∷ []) ∷ (p≢α ∷ p≢β ∷ []) ∷ [] , Apartʷ-^ (ω m) G ((m≢α ∷ m≢β ∷ []) ∷ []) f))
          where
          m≢α = FinP.<⇒≢ m<α
          m<β = ℕP.<-trans m<α αβ
          m≢β = FinP.<⇒≢ m<β
          m<p = ℕP.<-trans m<β β<p
          syl-s : syl s ≡ X m p m<p • ω m ^ f
          syl-s = ≡.trans syl≡ (≡.trans (≡.cong (λ k → sylData p k W) k0) (sylData-unit< W fo m<p))
        by-m (tri≈ _ m≡α _) = at-α m≡α fo um rest
        by-m (tri> _ _ α<m) = by-mβ (ℕP.m≤n⇒m<n∨m≡n (β≤ α<m))
          where
          by-mβ : β < m ⊎ toℕ β ≡ toℕ m → Square G s o
          by-mβ (inj₁ β<m) =
            same (≢-sym (FinP.<⇒≢ α<m)) (≢-sym (FinP.<⇒≢ β<m))
              (≡.subst (λ w → Apartʷ w G) (≡.sym syl≡)
                (above-apart′ (sylData p (lde v) W) (sylData-above p (lde v) W fo m≤p) G (α<m ∷ β<m ∷ [])))
          by-mβ (inj₂ e) = at-β (FinP.toℕ-injective (≡.sym e)) fo um rest

    ------------------------------------------------------------------
    -- k > 0 and α < p

    case+ : ∀ {K′} → lde v ≡ suc K′ → α < p → Hard → Square G s o
    case+ {K′} ks α<p hard = at-j first
      where
      β≤p : β ≤ p
      β≤p = β≤ α<p
      v≡ₖ : v ≡ scV (suc K′) W
      v≡ₖ = ≡.trans v≡ (≡.cong (λ k → scV k W) ks)
      U = Xᶻ α β W
      colU : col r p ≡ scV (suc K′) U
      colU = col-r v≡ₖ
      minU : Minimal (suc K′) U
      minU = Minimal-X α β α≢β W (≡.subst (λ k → Minimal k W) ks min)
      pr : pivot r ≡ just p
      pr = pivot-stay G s β≤p ps (ne-𝕀 r p K′ U colU minU)
      lv : level r ≡ level s
      lv = ≡.trans (level-of r pr (suc K′) U colU minU)
             (≡.trans (≡.cong (λ m → (suc (toℕ p) , suc K′ , m)) (nodd-X α β α≢β W))
                      (≡.sym (≡.trans lvl (≡.cong (λ k → (suc (toℕ p) , k , nodd W)) ks))))
      syl-U : ∀ {j′ ℓ′} → firstOdd U ≡ just j′ → nextOdd j′ U ≡ just ℓ′ → (jℓ : j′ < ℓ′) →
              syl r ≡ H j′ ℓ′ jℓ • ω j′ ^ zOf (U ! j′) (U ! ℓ′)
      syl-U fo nx jℓ = ≡.trans (syl-of r pr (suc K′) U colU minU) (sylData-pair {p = p} K′ U fo nx jℓ)
      syl-W : ∀ {j ℓ} → firstOdd W ≡ just j → nextOdd j W ≡ just ℓ → (jℓ : j < ℓ) →
              syl s ≡ H j ℓ jℓ • ω j ^ zOf (W ! j) (W ! ℓ)
      syl-W fo nx jℓ = ≡.trans syl≡ (≡.trans (≡.cong (λ k → sylData p k W) ks) (sylData-pair {p = p} K′ W fo nx jℓ))
      bβ : Bℓ β <ₗ level s
      bβ = ≡.subst (Bℓ β <ₗ_) (≡.sym lvl) (bℓ-below (nodd W) (≡.subst (0 ℕ.<_) (≡.sym ks) (s≤s z≤n)) β≤p)
      below : (G′ : Word (Gen n)) → Letters≤ β G′ → Below (level s) G′ (step s)
      below G′ h = word-below-all G′ h (step s) (lt-step s o ps) bβ
      α≤β : toℕ α ℕ.≤ toℕ β
      α≤β = ℕP.<⇒≤ αβ

      -- G keeps the first two odd entries: disjoint.
      keep : ∀ {j ℓ} → firstOdd W ≡ just j → nextOdd j W ≡ just ℓ → U ! j ≡ W ! j → U ! ℓ ≡ W ! ℓ →
             (∀ x → x < j → Even (U ! x)) → (∀ x → j < x → x < ℓ → Even (U ! x)) →
             Apartʷ (syl s) G → Square G s o
      keep {j} {ℓ} fo nx ej eℓ blw btw ap = square-disjoint′ G s o ps pr syl-r ap lv
        where
        jℓ : j < ℓ
        jℓ = proj₁ (nextOdd-spec W nx)
        foU : firstOdd U ≡ just j
        foU = firstOdd-char U (≡.subst Odd (≡.sym ej) (proj₁ (firstOdd-spec W fo))) blw
        nxU : nextOdd j U ≡ just ℓ
        nxU = nextOdd-char U jℓ (≡.subst Odd (≡.sym eℓ) (proj₁ (proj₂ (nextOdd-spec W nx)))) btw
        syl-r : syl r ≡ syl s
        syl-r = ≡.trans (syl-U foU nxU jℓ)
                  (≡.trans (≡.cong₂ (λ x y → H j ℓ jℓ • ω j ^ zOf x y) ej eℓ) (≡.sym (syl-W fo nx jℓ)))

      -- ℓ = α, w_β even: through X_[α,β].
      evenβ : ∀ {j} → firstOdd W ≡ just j → nextOdd j W ≡ just α → Even (W ! β) → Square G s o
      evenβ {j} fo nx eβ =
        square-syl G s o (H j β jβ • ω j ^ z) (X α β αβ) pr syl-r (below (X α β αβ) ℕP.≤-refl)
          (trans (R-H-X jα αβ z) (cright refl′ (≡.sym (syl-W fo nx jα))))
        where
        jα : j < α
        jα = proj₁ (nextOdd-spec W nx)
        jβ = ℕP.<-trans jα αβ
        z = zOf (W ! j) (W ! α)
        Uj : U ! j ≡ W ! j
        Uj = Xᶻ-≢ W (FinP.<⇒≢ jα) (FinP.<⇒≢ jβ)
        foU : firstOdd U ≡ just j
        foU = firstOdd-char U (≡.subst Odd (≡.sym Uj) (proj₁ (firstOdd-spec W fo)))
                (λ x xj → ≡.subst Even (≡.sym (Xᶻ-≢ W (FinP.<⇒≢ (ℕP.<-trans xj jα)) (FinP.<⇒≢ (ℕP.<-trans xj jβ))))
                                  (proj₂ (firstOdd-spec W fo) x xj))
        nxU : nextOdd j U ≡ just β
        nxU = nextOdd-char U jβ (≡.subst Odd (≡.sym (Xᶻ-β W)) (proj₁ (proj₂ (nextOdd-spec W nx))))
                (λ x jx xβ → even-X W x (λ _ → eβ) (λ x≡β → ⊥-elim (FinP.<-irrefl x≡β xβ))
                                        (λ x≢α _ → proj₂ (proj₂ (nextOdd-spec W nx)) x jx (<α xβ x≢α)))
        syl-r : syl r ≡ H j β jβ • ω j ^ z
        syl-r = ≡.trans (syl-U foU nxU jβ) (≡.cong₂ (λ x y → H j β jβ • ω j ^ zOf x y) Uj (Xᶻ-β W))

      -- ℓ = β, j < α: through X_[α,β].
      βnext : ∀ {j} → firstOdd W ≡ just j → nextOdd j W ≡ just β → j < α → Square G s o
      βnext {j} fo nx jα =
        square-syl G s o (H j α jα • ω j ^ z) (X α β αβ) pr syl-r (below (X α β αβ) ℕP.≤-refl)
          (trans (flip-X αβ (R-H-X jα αβ z)) (cright refl′ (≡.sym (syl-W fo nx jβ))))
        where
        jβ : j < β
        jβ = proj₁ (nextOdd-spec W nx)
        z = zOf (W ! j) (W ! β)
        Uj : U ! j ≡ W ! j
        Uj = Xᶻ-≢ W (FinP.<⇒≢ jα) (FinP.<⇒≢ jβ)
        foU : firstOdd U ≡ just j
        foU = firstOdd-char U (≡.subst Odd (≡.sym Uj) (proj₁ (firstOdd-spec W fo)))
                (λ x xj → ≡.subst Even (≡.sym (Xᶻ-≢ W (FinP.<⇒≢ (ℕP.<-trans xj jα)) (FinP.<⇒≢ (ℕP.<-trans xj jβ))))
                                  (proj₂ (firstOdd-spec W fo) x xj))
        nxU : nextOdd j U ≡ just α
        nxU = nextOdd-char U jα (≡.subst Odd (≡.sym (Xᶻ-α W)) (proj₁ (proj₂ (nextOdd-spec W nx))))
                (λ x jx xα → ≡.subst Even (≡.sym (Xᶻ-≢ W (FinP.<⇒≢ xα) (FinP.<⇒≢ (ℕP.<-trans xα αβ))))
                                     (proj₂ (proj₂ (nextOdd-spec W nx)) x jx (ℕP.<-trans xα αβ)))
        syl-r : syl r ≡ H j α jα • ω j ^ z
        syl-r = ≡.trans (syl-U foU nxU jα) (≡.cong₂ (λ x y → H j α jα • ω j ^ zOf x y) Uj (Xᶻ-α W))

      -- j = α, ℓ = β: by the exponent z; the syllable of r has -z.
      pairαβ : firstOdd W ≡ just α → nextOdd α W ≡ just β → Square G s o
      pairαβ fo nx = by-z (zOf (W ! α) (W ! β)) (zOf-< (W ! α) (W ! β)) ≡.refl
        where
        oα : Odd (W ! α)
        oα = proj₁ (firstOdd-spec W fo)
        oβ : Odd (W ! β)
        oβ = proj₁ (proj₂ (nextOdd-spec W nx))
        foU : firstOdd U ≡ just α
        foU = firstOdd-char U (≡.subst Odd (≡.sym (Xᶻ-α W)) oβ)
                (λ x xα → ≡.subst Even (≡.sym (Xᶻ-≢ W (FinP.<⇒≢ xα) (FinP.<⇒≢ (ℕP.<-trans xα αβ))))
                                  (proj₂ (firstOdd-spec W fo) x xα))
        nxU : nextOdd α U ≡ just β
        nxU = nextOdd-char U αβ (≡.subst Odd (≡.sym (Xᶻ-β W)) oα)
                (λ x αx xβ → ⊥-elim (none-αβ αx xβ))
        syl-r : syl r ≡ H α β αβ • ω α ^ neg4 (zOf (W ! α) (W ! β))
        syl-r = ≡.trans (syl-U foU nxU αβ)
                  (≡.cong (λ z → H α β αβ • ω α ^ z)
                    (≡.trans (≡.cong₂ zOf (Xᶻ-α W) (Xᶻ-β W)) (zOf-sym (W ! α) (W ! β) oα oβ)))
        syl-s′ : ∀ {z} → zOf (W ! α) (W ! β) ≡ z → syl s ≡ H α β αβ • ω α ^ z
        syl-s′ e = ≡.trans (syl-W fo nx αβ) (≡.cong (λ z → H α β αβ • ω α ^ z) e)
        syl-r′ : ∀ {z} → zOf (W ! α) (W ! β) ≡ z → syl r ≡ H α β αβ • ω α ^ neg4 z
        syl-r′ e = ≡.trans syl-r (≡.cong (λ z → H α β αβ • ω α ^ neg4 z) e)
        by-z : ∀ z → z ℕ.< 4 → zOf (W ! α) (W ! β) ≡ z → Square G s o
        -- z = 0: H X = ω_[β]⁴ H, by (18).
        by-z 0 _ e =
          square-syl G s o (H α β αβ • ε) (ω β ^ 4) pr (syl-r′ e)
            (below (ω β ^ 4) (ℕP.≤-refl , ℕP.≤-refl , ℕP.≤-refl , ℕP.≤-refl))
            (trans (trans (cleft right-unit) (trans (axiom (rel-18 αβ)) (cright sym right-unit)))
                   (cright refl′ (≡.sym (syl-s′ e))))
        -- z = 1, 2, 3: by (z₁), (z₂), (z₃).
        by-z 1 _ e =
          square-syl G s o (H α β αβ • ω α ^ 3) (ω α ^ 7 • ω β ^ 3 • X α β αβ) pr (syl-r′ e)
            (below (ω α ^ 7 • ω β ^ 3 • X α β αβ)
                   ((α≤β , α≤β , α≤β , α≤β , α≤β , α≤β , α≤β) , (ℕP.≤-refl , ℕP.≤-refl , ℕP.≤-refl) , ℕP.≤-refl))
            (trans (trans assoc (trans (Hω³X αβ) (by-assoc auto))) (cright refl′ (≡.sym (syl-s′ e))))
        by-z 2 _ e =
          square-syl G s o (H α β αβ • ω α ^ 2) (ω α ^ 6 • ω β ^ 2 • X α β αβ) pr (syl-r′ e)
            (below (ω α ^ 6 • ω β ^ 2 • X α β αβ)
                   ((α≤β , α≤β , α≤β , α≤β , α≤β , α≤β) , (ℕP.≤-refl , ℕP.≤-refl) , ℕP.≤-refl))
            (trans (trans assoc (trans (Hω²X αβ) (by-assoc auto))) (cright refl′ (≡.sym (syl-s′ e))))
        by-z 3 _ e =
          square-syl G s o (H α β αβ • ω α) (ω α ^ 5 • ω β • X α β αβ) pr (syl-r′ e)
            (below (ω α ^ 5 • ω β • X α β αβ)
                   ((α≤β , α≤β , α≤β , α≤β , α≤β) , ℕP.≤-refl , ℕP.≤-refl))
            (trans (trans assoc (trans (Hω¹X αβ) (by-assoc auto))) (cright refl′ (≡.sym (syl-s′ e))))
        by-z (suc (suc (suc (suc _)))) (s≤s (s≤s (s≤s (s≤s ())))) _

      -- j = α, β < ℓ: through X_[α,β].
      αfirst : ∀ {ℓ} → firstOdd W ≡ just α → nextOdd α W ≡ just ℓ → β < ℓ → Square G s o
      αfirst {ℓ} fo nx βℓ =
        square-syl G s o (H β ℓ βℓ • ω β ^ z) (X α β αβ) pr syl-r (below (X α β αβ) ℕP.≤-refl)
          (trans (R-X-H αβ βℓ z) (cright refl′ (≡.sym (syl-W fo nx αℓ))))
        where
        αℓ : α < ℓ
        αℓ = proj₁ (nextOdd-spec W nx)
        z = zOf (W ! α) (W ! ℓ)
        ℓ≢α = ≢-sym (FinP.<⇒≢ αℓ)
        ℓ≢β = ≢-sym (FinP.<⇒≢ βℓ)
        btw = proj₂ (proj₂ (nextOdd-spec W nx))
        foU : firstOdd U ≡ just β
        foU = firstOdd-char U (≡.subst Odd (≡.sym (Xᶻ-β W)) (proj₁ (firstOdd-spec W fo)))
                (λ x xβ → even-X W x (λ _ → btw β αβ βℓ) (λ x≡β → ⊥-elim (FinP.<-irrefl x≡β xβ))
                                     (λ x≢α _ → proj₂ (firstOdd-spec W fo) x (<α xβ x≢α)))
        nxU : nextOdd β U ≡ just ℓ
        nxU = nextOdd-char U βℓ (≡.subst Odd (≡.sym (Xᶻ-≢ W ℓ≢α ℓ≢β)) (proj₁ (proj₂ (nextOdd-spec W nx))))
                (λ x βx xℓ → ≡.subst Even (≡.sym (Xᶻ-≢ W (≢-sym (FinP.<⇒≢ (ℕP.<-trans αβ βx))) (≢-sym (FinP.<⇒≢ βx))))
                                     (btw x (ℕP.<-trans αβ βx) xℓ))
        syl-r : syl r ≡ H β ℓ βℓ • ω β ^ z
        syl-r = ≡.trans (syl-U foU nxU βℓ) (≡.cong₂ (λ x y → H β ℓ βℓ • ω β ^ zOf x y) (Xᶻ-β W) (Xᶻ-≢ W ℓ≢α ℓ≢β))

      -- j = β: through X_[α,β].
      βfirst : ∀ {ℓ} → firstOdd W ≡ just β → nextOdd β W ≡ just ℓ → Square G s o
      βfirst {ℓ} fo nx =
        square-syl G s o (H α ℓ αℓ • ω α ^ z) (X α β αβ) pr syl-r (below (X α β αβ) ℕP.≤-refl)
          (trans (flip-X αβ (R-X-H αβ βℓ z)) (cright refl′ (≡.sym (syl-W fo nx βℓ))))
        where
        βℓ : β < ℓ
        βℓ = proj₁ (nextOdd-spec W nx)
        αℓ = ℕP.<-trans αβ βℓ
        z = zOf (W ! β) (W ! ℓ)
        ℓ≢α = ≢-sym (FinP.<⇒≢ αℓ)
        ℓ≢β = ≢-sym (FinP.<⇒≢ βℓ)
        blw = proj₂ (firstOdd-spec W fo)
        foU : firstOdd U ≡ just α
        foU = firstOdd-char U (≡.subst Odd (≡.sym (Xᶻ-α W)) (proj₁ (firstOdd-spec W fo)))
                (λ x xα → ≡.subst Even (≡.sym (Xᶻ-≢ W (FinP.<⇒≢ xα) (FinP.<⇒≢ (ℕP.<-trans xα αβ))))
                                  (blw x (ℕP.<-trans xα αβ)))
        nxU : nextOdd α U ≡ just ℓ
        nxU = nextOdd-char U αℓ (≡.subst Odd (≡.sym (Xᶻ-≢ W ℓ≢α ℓ≢β)) (proj₁ (proj₂ (nextOdd-spec W nx))))
                (λ x αx xℓ → even-X W x (λ x≡α → ⊥-elim (FinP.<-irrefl (≡.sym x≡α) αx)) (λ _ → blw α αβ)
                                        (λ _ x≢β → proj₂ (proj₂ (nextOdd-spec W nx)) x (β< αx x≢β) xℓ))
        syl-r : syl r ≡ H α ℓ αℓ • ω α ^ z
        syl-r = ≡.trans (syl-U foU nxU αℓ) (≡.cong₂ (λ x y → H α ℓ αℓ • ω α ^ zOf x y) (Xᶻ-α W) (Xᶻ-≢ W ℓ≢α ℓ≢β))

      at-j : (∃ λ j → firstOdd W ≡ just j) → Square G s o
      at-j (j , fo) = at-ℓ (second ks fo)
        where
        blw : ∀ x → x < j → Even (W ! x)
        blw = proj₂ (firstOdd-spec W fo)
        at-ℓ : (∃ λ ℓ → nextOdd j W ≡ just ℓ) → Square G s o
        at-ℓ (ℓ , nx) = by-ℓα (FinP.<-cmp ℓ α)
          where
          jℓ : j < ℓ
          jℓ = proj₁ (nextOdd-spec W nx)
          btw : ∀ x → j < x → x < ℓ → Even (W ! x)
          btw = proj₂ (proj₂ (nextOdd-spec W nx))
          z = zOf (W ! j) (W ! ℓ)
          syl-s : syl s ≡ H j ℓ jℓ • ω j ^ z
          syl-s = syl-W fo nx jℓ

          by-ℓα : Tri (ℓ < α) (ℓ ≡ α) (α < ℓ) → Square G s o
          -- ℓ < α: disjoint.
          by-ℓα (tri< ℓα _ _) =
            keep fo nx (Xᶻ-≢ W (FinP.<⇒≢ jα) (FinP.<⇒≢ (ℕP.<-trans jα αβ)))
                       (Xᶻ-≢ W (FinP.<⇒≢ ℓα) (FinP.<⇒≢ ℓβ))
                       (λ x xj → ≡.subst Even (≡.sym (Xᶻ-≢ W (FinP.<⇒≢ (ℕP.<-trans xj jα))
                                                           (FinP.<⇒≢ (ℕP.<-trans (ℕP.<-trans xj jα) αβ))))
                                          (blw x xj))
                       (λ x jx xℓ → ≡.subst Even (≡.sym (Xᶻ-≢ W (FinP.<⇒≢ (ℕP.<-trans xℓ ℓα))
                                                              (FinP.<⇒≢ (ℕP.<-trans xℓ ℓβ))))
                                             (btw x jx xℓ))
                       (≡.subst (λ w → Apartʷ w G) (≡.sym syl-s)
                         (within-apart (H j ℓ jℓ • ω j ^ z)
                           (FinP.≤-refl , Within-^ (ω j) (ℕP.<⇒≤ jℓ) z) G (ℓα ∷ ℓβ ∷ [])))
            where
            jα = ℕP.<-trans jℓ ℓα
            ℓβ = ℕP.<-trans ℓα αβ
          -- ℓ = α: by the parity of w_β.
          by-ℓα (tri≈ _ ℓ≡α _) = by-par (oddᶻ (W ! β)) ≡.refl
            where
            nxα : nextOdd j W ≡ just α
            nxα = ≡.subst (λ x → nextOdd j W ≡ just x) ℓ≡α nx
            by-par : (b : Bool) → oddᶻ (W ! β) ≡ b → Square G s o
            by-par true od = hard ks fo nxα od
            by-par false ev = evenβ fo nxα ev
          by-ℓα (tri> _ _ αℓ) = by-ℓβ (ℕP.m≤n⇒m<n∨m≡n (β≤ αℓ))
            where
            by-ℓβ : β < ℓ ⊎ toℕ β ≡ toℕ ℓ → Square G s o
            -- ℓ = β.
            by-ℓβ (inj₂ e) = by-jα (ℕP.m≤n⇒m<n∨m≡n (≤α jβ))
              where
              ℓ≡β : ℓ ≡ β
              ℓ≡β = FinP.toℕ-injective (≡.sym e)
              nxβ : nextOdd j W ≡ just β
              nxβ = ≡.subst (λ x → nextOdd j W ≡ just x) ℓ≡β nx
              jβ : j < β
              jβ = ≡.subst (j <_) ℓ≡β jℓ
              by-jα : j < α ⊎ toℕ j ≡ toℕ α → Square G s o
              by-jα (inj₁ jα) = βnext fo nxβ jα
              by-jα (inj₂ e′) = pairαβ (≡.subst (λ x → firstOdd W ≡ just x) j≡α fo)
                                       (≡.subst (λ x → nextOdd x W ≡ just β) j≡α nxβ)
                where
                j≡α : j ≡ α
                j≡α = FinP.toℕ-injective e′
            -- β < ℓ: by j.
            by-ℓβ (inj₁ βℓ) = by-jα (FinP.<-cmp j α)
              where
              ℓ≢α = ≢-sym (FinP.<⇒≢ αℓ)
              ℓ≢β = ≢-sym (FinP.<⇒≢ βℓ)
              by-jα : Tri (j < α) (j ≡ α) (α < j) → Square G s o
              -- j < α < β < ℓ: disjoint.
              by-jα (tri< jα _ _) =
                keep fo nx (Xᶻ-≢ W (FinP.<⇒≢ jα) (FinP.<⇒≢ jβ)) (Xᶻ-≢ W ℓ≢α ℓ≢β)
                  (λ x xj → ≡.subst Even (≡.sym (Xᶻ-≢ W (FinP.<⇒≢ (ℕP.<-trans xj jα))
                                                      (FinP.<⇒≢ (ℕP.<-trans xj jβ))))
                                     (blw x xj))
                  (λ x jx xℓ → even-X W x (λ _ → btw β jβ βℓ) (λ _ → btw α jα αℓ) (λ _ _ → btw x jx xℓ))
                  (≡.subst (λ w → Apartʷ w G) (≡.sym syl-s)
                    ((j≢α ∷ j≢β ∷ []) ∷ (ℓ≢α ∷ ℓ≢β ∷ []) ∷ [] ,
                     Apartʷ-^ (ω j) G ((j≢α ∷ j≢β ∷ []) ∷ []) z))
                where
                jβ = ℕP.<-trans jα αβ
                j≢α = FinP.<⇒≢ jα
                j≢β = FinP.<⇒≢ jβ
              by-jα (tri≈ _ j≡α _) =
                αfirst (≡.subst (λ x → firstOdd W ≡ just x) j≡α fo)
                       (≡.subst (λ x → nextOdd x W ≡ just ℓ) j≡α nx) βℓ
              by-jα (tri> _ _ αj) = by-jβ (ℕP.m≤n⇒m<n∨m≡n (β≤ αj))
                where
                by-jβ : β < j ⊎ toℕ β ≡ toℕ j → Square G s o
                -- β < j: disjoint.
                by-jβ (inj₁ βj) =
                  keep fo nx (Xᶻ-≢ W (≢-sym (FinP.<⇒≢ αj)) (≢-sym (FinP.<⇒≢ βj))) (Xᶻ-≢ W ℓ≢α ℓ≢β)
                    (λ x xj → even-X W x (λ _ → blw β βj) (λ _ → blw α αj) (λ _ _ → blw x xj))
                    (λ x jx xℓ → ≡.subst Even (≡.sym (Xᶻ-≢ W (≢-sym (FinP.<⇒≢ (ℕP.<-trans αj jx)))
                                                           (≢-sym (FinP.<⇒≢ (ℕP.<-trans βj jx)))))
                                          (btw x jx xℓ))
                    (≡.subst (λ w → Apartʷ w G) (≡.sym syl≡)
                      (above-apart′ (sylData p (lde v) W)
                        (sylData-above p (lde v) W fo (ℕP.<⇒≤ (ℕP.<-≤-trans jℓ (odd≤ (proj₁ (proj₂ (nextOdd-spec W nx)))))))
                        G (αj ∷ βj ∷ [])))
                by-jβ (inj₂ e) =
                  βfirst (≡.subst (λ x → firstOdd W ≡ just x) j≡β fo)
                         (≡.subst (λ x → nextOdd x W ≡ just ℓ) j≡β nx)
                  where
                  j≡β : j ≡ β
                  j≡β = FinP.toℕ-injective (≡.sym e)

  ----------------------------------------------------------------------
  -- The case, given Hard

  caseX : Hard → Square (X-gen α β αβ) s o
  caseX hard = by-αp (FinP.<-cmp α p)
    where
    by-αp : Tri (α < p) (α ≡ p) (p < α) → Square G s o
    by-αp (tri< α<p _ _) = by-k (lde v) ≡.refl
      where
      by-k : ∀ k → lde v ≡ k → Square G s o
      by-k (suc K′) ks = case+ ks α<p hard
      by-k zero k0 = by-βp (ℕP.m≤n⇒m<n∨m≡n (β≤ α<p))
        where
        by-βp : β < p ⊎ toℕ β ≡ toℕ p → Square G s o
        by-βp (inj₁ β<p) = case0 k0 β<p
        by-βp (inj₂ e) =
          Top.top0 α β αβ1 s o (≡.subst (λ x → pivot s ≡ just x) (≡.sym β≡p) ps)
                   (≡.subst (λ x → lde (col s x) ≡ 0) (≡.sym β≡p) k0)
          where
          β≡p : β ≡ p
          β≡p = FinP.toℕ-injective e
    by-αp (tri≈ _ α≡p _) = retro (≡.subst (_≤ α) α≡p FinP.≤-refl)
    by-αp (tri> _ _ p<α) = retro (ℕP.<⇒≤ p<α)

------------------------------------------------------------------------
-- Presentations of groups
--
-- Generators that reach above the pivot raise the level.
--
-- If s agrees with I from column d on, and g acts on indices ≤ d with
-- top index d, then g·s has pivot d: column d of g·s is g e_d, which is
-- -e_d, e_c or a column of K, and the columns beyond d are untouched.
-- So the edges out of a state s with pivot p (or s = I) by a generator
-- with top index above p go up, and the induction on levels takes them
-- from the other end.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.CCX+HH-TwoLevel.Above {n : ℕ} where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary.Decidable using (recompute)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D ; oddℤ)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (scV ; Minimal)
open import Examples.Groups.CCX+HH-TwoLevel.ColumnAction
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
open import Examples.Groups.CCX+HH-TwoLevel.Pivot
  using (pivot ; pivot-char ; pivot-just ; pivot-nothing ; Beyond ; Lvl ; level ; level-just ; lvlAt ; _<ₗ_ ; <ₗ-irrefl)
open import Examples.Groups.CCX+HH-TwoLevel.Levels using (<ₗ-trans)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable
  using (top ; Beyond-actM ; actV-e-beyond ; eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; col𝕀≡)
open import Examples.Groups.CCX+HH-TwoLevel.Reduction {n} using (_≤ₗ_)
open import Examples.Groups.CCX+HH-TwoLevel.States {n} using (ne-𝕀 ; ne-𝕀-at)

private
  e-a : (a : Fin n) → eᶻ a ! a ≡ + 1
  e-a a = ≡.trans (eᶻ-! a a) (eδ-refl a)

  e-≢ : {a x : Fin n} → x ≢ a → eᶻ a ! x ≡ + 0
  e-≢ {a} {x} x≢a = ≡.trans (eᶻ-! a x) (eδ-≢ x≢a)

  rc : ∀ {a b : Fin n} → .(a < b) → a < b
  rc {a} {b} lt = recompute (a FinP.<? b) lt

  sym≢ : {x y : Fin n} → x ≢ y → y ≢ x
  sym≢ ne e = ne (≡.sym e)

------------------------------------------------------------------------
-- A generator moves the basis vector of its top index

top-moves : (g : Gen n) (M : Matrix n n D) → col M (top g) ≡ col 𝕀 (top g) →
            col (actM g M) (top g) ≢ col 𝕀 (top g)
top-moves (M-gen d) M e = ne-𝕀-at gM d 0 w col≡ (inj₁ ≡.refl) d (λ eq → -1≢1 (≡.trans (≡.sym wd) (≡.trans eq (e-a d))))
  where
  gM = actM (M-gen d) M
  w = Mᶻ d (eᶻ d)
  col≡ : col gM d ≡ scV 0 w
  col≡ = ≡.trans (col-actM (M-gen d) M d) (≡.trans (≡.cong (actV (M-gen d)) (≡.trans e (col𝕀≡ d))) (actV-M d 0 (eᶻ d)))
  wd : w ! d ≡ -[1+ 0 ]
  wd = ≡.trans (set₁-a d (ℤ.- (eᶻ d ! d)) (eᶻ d)) (≡.cong ℤ.-_ (e-a d))
  -1≢1 : -[1+ 0 ] ≢ + 1
  -1≢1 ()
top-moves (X-gen c d p) M e = ne-𝕀-at gM d 0 w col≡ (inj₁ ≡.refl) d (λ eq → 0≢1 (≡.trans (≡.sym wd) (≡.trans eq (e-a d))))
  where
  gM = actM (X-gen c d p) M
  w = Xᶻ c d (eᶻ d)
  col≡ : col gM d ≡ scV 0 w
  col≡ = ≡.trans (col-actM (X-gen c d p) M d) (≡.trans (≡.cong (actV (X-gen c d p)) (≡.trans e (col𝕀≡ d))) (actV-X c d p 0 (eᶻ d)))
  wd : w ! d ≡ + 0
  wd = ≡.trans (set₂-b c d (eᶻ d ! d) (eᶻ d ! c) (eᶻ d) (<⇒≢ p)) (e-≢ (<⇒≢ p))
  0≢1 : + 0 ≢ + 1
  0≢1 ()
top-moves (K-gen a b c d p q r) M e = ne-𝕀 gM d 0 w col≡ (inj₂ (d , ≡.cong oddℤ wd))
  where
  open Distinct₄ (distinct₄ p q r)
  gM = actM (K-gen a b c d p q r) M
  w = Kᶻ a b c d (eᶻ d)
  col≡ : col gM d ≡ scV 1 w
  col≡ = ≡.trans (col-actM (K-gen a b c d p q r) M d)
           (≡.trans (≡.cong (actV (K-gen a b c d p q r)) (≡.trans e (col𝕀≡ d))) (actV-K a b c d p q r 0 (eᶻ d)))
  wd : w ! d ≡ + 1
  wd = ≡.trans (set₄-d (distinct₄ p q r) _ _ _ _ _)
         (≡.trans (≡.cong₂ (λ x y → rowDᶻ x y (eᶻ d ! c) (eᶻ d ! d)) (e-≢ ad) (e-≢ bd))
           (≡.trans (≡.cong₂ (λ x y → rowDᶻ (+ 0) (+ 0) x y) (e-≢ cd) (e-a d)) ≡.refl))

-- So g·M has pivot top g, if M agrees with I from top g on.
pivot-top : (g : Gen n) (M : Matrix n n D) → (∀ c → top g ≤ c → col M c ≡ col 𝕀 c) →
            pivot (actM g M) ≡ just (top g)
pivot-top g M id≥ = pivot-char (actM g M) (top-moves g M (id≥ (top g) FinP.≤-refl))
  (Beyond-actM g {M = M} FinP.≤-refl (λ c tg<c → id≥ c (ℕP.<⇒≤ tg<c)))

------------------------------------------------------------------------
-- The edges reaching above go up

private
  -- (t + 1, …) is above (p + 1, …) when p < t, and above (0, 0, 0).
  above : ∀ {t : Fin n} {L : Lvl} → (∀ {k m} → L <ₗ (suc (toℕ t) , k , m)) →
          ∀ {k m} → (suc (toℕ t) , k , m) ≤ₗ L → ⊥
  above lt (inj₁ x) = <ₗ-irrefl (<ₗ-trans x lt)
  above lt (inj₂ ≡.refl) = <ₗ-irrefl lt

-- A generator whose top index lies above the pivot p of s raises the
-- level.
up-just : (g : Gen n) (s : Matrix n n D) {p : Fin n} → pivot s ≡ just p → p < top g →
          level (actM g s) ≤ₗ level s → ⊥
up-just g s {p} pv p<t le =
  above {t = top g} lt (≡.subst (_≤ₗ level s) (level-just (actM g s) pt) le)
  where
  pt : pivot (actM g s) ≡ just (top g)
  pt = pivot-top g s (λ c tg≤c → proj₂ (pivot-just s pv) c (ℕP.<-≤-trans p<t tg≤c))
  lt : ∀ {k m} → level s <ₗ (suc (toℕ (top g)) , k , m)
  lt = ≡.subst (_<ₗ _) (≡.sym (level-just s pv)) (inj₁ (ℕ.s≤s p<t))

-- Every generator raises the level of I.
up-nothing : (g : Gen n) (s : Matrix n n D) → pivot s ≡ nothing → level (actM g s) ≤ₗ level s → ⊥
up-nothing g s pv le =
  above {t = top g} lt (≡.subst (_≤ₗ level s) (level-just (actM g s) pt) le)
  where
  s≡ : s ≡ 𝕀
  s≡ = pivot-nothing s pv
  pt : pivot (actM g s) ≡ just (top g)
  pt = pivot-top g s (λ c _ → ≡.cong (λ N → col N c) s≡)
  lt : ∀ {k m} → level s <ₗ (suc (toℕ (top g)) , k , m)
  lt = ≡.subst (_<ₗ _) (≡.sym (≡.cong (λ x → lvlAt x s) pv)) (inj₁ (ℕ.s≤s ℕ.z≤n))

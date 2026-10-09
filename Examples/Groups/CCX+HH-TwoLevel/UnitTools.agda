------------------------------------------------------------------------
-- Presentations of groups
--
-- Tools for the edges at the levels with exponent 0, and for the
-- squares that close below a pivot p.
--
-- * Unit columns: a numerator that is ±1 at m and 0 elsewhere (UV),
--   how (-1) and the adjacent X's move it, and its syllable.
-- * States that are I from column p on (AtI p), as a normal syllable
--   leaves a unit pivot column, and words whose letters act below p
--   (Under p): along such a word every state is I from p on, so lies
--   below every level with pivot p.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.CCX+HH-TwoLevel.UnitTools {n : ℕ} where

open import Data.Bool.Base using (Bool ; true ; false ; not)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D ; oddℤ)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (Odd)
open import Examples.Groups.CCX+HH-TwoLevel.Column
open import Examples.Groups.CCX+HH-TwoLevel.ColumnAction using (Mᶻ ; Xᶻ)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (pivot ; Beyond ; level-below)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable
  using (top ; Beyond-actM ; actV-e-beyond ; eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢)
open import Examples.Groups.CCX+HH-TwoLevel.Reduction {n} using (Low)

private
  ≢-sym : {a b : Fin n} → a ≢ b → b ≢ a
  ≢-sym ne e = ne (≡.sym e)

  e-a : (a : Fin n) → eᶻ a ! a ≡ + 1
  e-a a = ≡.trans (eᶻ-! a a) (eδ-refl a)

  e-≢ : {a x : Fin n} → x ≢ a → eᶻ a ! x ≡ + 0
  e-≢ {a} {x} x≢a = ≡.trans (eᶻ-! a x) (eδ-≢ x≢a)

------------------------------------------------------------------------
-- Unit columns

-- w is the unit u at m, and 0 elsewhere.
record UV (m : Fin n) (u : ℤ) (w : Vec ℤ n) : Set where
  constructor mkUV
  field
    unit : Unit1 u
    at   : w ! m ≡ u
    off  : ∀ y → y ≢ m → w ! y ≡ + 0

unit-neg : ∀ {u} → Unit1 u → Unit1 (ℤ.- u)
unit-neg (inj₁ ≡.refl) = inj₂ ≡.refl
unit-neg (inj₂ ≡.refl) = inj₁ ≡.refl

unit-negℤ : ∀ {u} → Unit1 u → negℤ (ℤ.- u) ≡ not (negℤ u)
unit-negℤ (inj₁ ≡.refl) = ≡.refl
unit-negℤ (inj₂ ≡.refl) = ≡.refl

unit≢0 : ∀ {u} → Unit1 u → u ≢ + 0
unit≢0 (inj₁ ≡.refl) ()
unit≢0 (inj₂ ≡.refl) ()

UV-first : ∀ {m u w} → UV m u w → firstOdd w ≡ just m
UV-first {m} {u} {w} (mkUV uu wm z) =
  firstOdd-char w (≡.subst Odd (≡.sym wm) (unit-odd uu))
    (λ x x<m → ≡.cong oddℤ (z x (λ { ≡.refl → FinP.<-irrefl ≡.refl x<m })))

-- (-1)_[m] negates the unit.
UV-M≡ : ∀ {m u w} → UV m u w → UV m (ℤ.- u) (Mᶻ m w)
UV-M≡ {m} {u} {w} (mkUV uu wm z) = mkUV
  (unit-neg uu)
  (≡.trans (set₁-a m (ℤ.- (w ! m)) w) (≡.cong ℤ.-_ wm))
  (λ y y≢m → ≡.trans (set₁-≢ m (ℤ.- (w ! m)) w y≢m) (z y y≢m))

-- (-1)_[c], c ≠ m, keeps it.
UV-M≢ : ∀ {m u w} (c : Fin n) → c ≢ m → UV m u w → UV m u (Mᶻ c w)
UV-M≢ {m} {u} {w} c c≢m (mkUV uu wm z) =
  mkUV uu (≡.trans (set₁-≢ c _ w (≢-sym c≢m)) wm) (λ y y≢m → at y y≢m (y FinP.≟ c))
  where
  at : ∀ y → y ≢ m → Dec (y ≡ c) → Mᶻ c w ! y ≡ + 0
  at y y≢m (yes ≡.refl) = ≡.trans (set₁-a y (ℤ.- (w ! y)) w) (≡.cong ℤ.-_ (z y y≢m))
  at y y≢m (no y≢c) = ≡.trans (set₁-≢ c _ w y≢c) (z y y≢m)

-- X_[x,y] moves a unit at x to y, at y to x, and keeps the others.
UV-X-x : ∀ {x y u w} → x ≢ y → UV x u w → UV y u (Xᶻ x y w)
UV-X-x {x} {y} {u} {w} x≢y (mkUV uu wx z) = mkUV uu
  (≡.trans (set₂-b x y (w ! y) (w ! x) w x≢y) wx)
  (λ t t≢y → at t t≢y (t FinP.≟ x))
  where
  at : ∀ t → t ≢ y → Dec (t ≡ x) → Xᶻ x y w ! t ≡ + 0
  at t t≢y (yes ≡.refl) = ≡.trans (set₂-a t y (w ! y) (w ! t) w) (z y (≢-sym x≢y))
  at t t≢y (no t≢x) = ≡.trans (set₂-≢ x y (w ! y) (w ! x) w t≢x t≢y) (z t t≢x)

UV-X-y : ∀ {x y u w} → x ≢ y → UV y u w → UV x u (Xᶻ x y w)
UV-X-y {x} {y} {u} {w} x≢y (mkUV uu wy z) = mkUV uu
  (≡.trans (set₂-a x y (w ! y) (w ! x) w) wy)
  (λ t t≢x → at t t≢x (t FinP.≟ y))
  where
  at : ∀ t → t ≢ x → Dec (t ≡ y) → Xᶻ x y w ! t ≡ + 0
  at t t≢x (yes ≡.refl) = ≡.trans (set₂-b x t (w ! t) (w ! x) w x≢y) (z x x≢y)
  at t t≢x (no t≢y) = ≡.trans (set₂-≢ x y (w ! y) (w ! x) w t≢x t≢y) (z t t≢y)

UV-X-o : ∀ {m x y u w} → x ≢ y → m ≢ x → m ≢ y → UV m u w → UV m u (Xᶻ x y w)
UV-X-o {m} {x} {y} {u} {w} x≢y m≢x m≢y (mkUV uu wm z) = mkUV uu
  (≡.trans (set₂-≢ x y (w ! y) (w ! x) w m≢x m≢y) wm)
  (λ t t≢m → at t t≢m (t FinP.≟ x) (t FinP.≟ y))
  where
  at : ∀ t → t ≢ m → Dec (t ≡ x) → Dec (t ≡ y) → Xᶻ x y w ! t ≡ + 0
  at t t≢m (yes ≡.refl) _ = ≡.trans (set₂-a t y (w ! y) (w ! t) w) (z y (≢-sym m≢y))
  at t t≢m (no t≢x) (yes ≡.refl) = ≡.trans (set₂-b x t (w ! t) (w ! x) w x≢y) (z x (≢-sym m≢x))
  at t t≢m (no t≢x) (no t≢y) = ≡.trans (set₂-≢ x y (w ! y) (w ! x) w t≢x t≢y) (z t t≢m)

-- Unless it is e_p, a unit vector differs from e_p somewhere.
UV-ne : ∀ {m u w} (p : Fin n) → UV m u w → m ≢ p ⊎ u ≡ -[1+ 0 ] → ∃ λ x → w ! x ≢ eᶻ p ! x
UV-ne {m} {u} {w} p (mkUV uu wm z) h = by (m FinP.≟ p) h
  where
  -1≢1 : -[1+ 0 ] ≢ + 1
  -1≢1 ()
  by : Dec (m ≡ p) → m ≢ p ⊎ u ≡ -[1+ 0 ] → ∃ λ x → w ! x ≢ eᶻ p ! x
  by (no m≢p) _ = m , λ e → unit≢0 uu (≡.trans (≡.sym wm) (≡.trans e (e-≢ m≢p)))
  by (yes m≡p) (inj₁ m≢p) = ⊥-elim (m≢p m≡p)
  by (yes ≡.refl) (inj₂ u≡) = m , λ e → -1≢1 (≡.trans (≡.sym u≡) (≡.trans (≡.sym wm) (≡.trans e (e-a m))))

-- The syllable of a unit column.
unitSyl< : ∀ {p m u w} → UV m u w → (lt : m < p) → sylData p 0 w ≡ X m p lt • Mτ m (negℤ u)
unitSyl< {p} {m} {u} {w} uv lt =
  ≡.trans (sylData-unit< w (UV-first uv) lt) (≡.cong (λ z → X m p lt • Mτ m (negℤ z)) (UV.at uv))

unitSyl≡ : ∀ {p u w} → UV p u w → sylData p 0 w ≡ Mτ p (negℤ u)
unitSyl≡ {p} {u} {w} uv = ≡.trans (sylData-unit≡ w (UV-first uv)) (≡.cong (λ z → Mτ p (negℤ z)) (UV.at uv))

------------------------------------------------------------------------
-- States that are I from column p on, and words acting below p

AtI : Fin n → Matrix n n D → Set
AtI p M = Beyond p M × col M p ≡ col 𝕀 p

Under : Fin n → Word (Gen n) → Set
Under p [ g ]ʷ = top g < p
Under p ε = ⊤
Under p (u • v) = Under p u × Under p v

AtI-act : (g : Gen n) {p : Fin n} {M : Matrix n n D} → top g < p → AtI p M → AtI p (actM g M)
AtI-act g {p} {M} tg (be , cp) =
  Beyond-actM g {p} {M} (ℕP.<⇒≤ tg) be ,
  ≡.trans (col-actM g M p) (≡.trans (≡.cong (actV g) cp) (actV-e-beyond g {top g} {p} FinP.≤-refl tg))

AtI-actʷ : (w : Word (Gen n)) {p : Fin n} {M : Matrix n n D} → Under p w → AtI p M → AtI p (actMʷ w M)
AtI-actʷ [ g ]ʷ {p} {M} h a = AtI-act g {p} {M} h a
AtI-actʷ ε _ a = a
AtI-actʷ (u • v) {p} {M} (hu , hv) a = AtI-actʷ u {p} {actMʷ v M} hu (AtI-actʷ v {p} {M} hv a)

-- Every letter of the word joins states below any level with pivot p.
under-below : (w : Word (Gen n)) {p : Fin n} {M : Matrix n n D} → Under p w → AtI p M →
              ∀ k m → Low (suc (toℕ p) , k , m) w M
under-below [ g ]ʷ {p} {M} h a k m =
  level-below M (proj₂ a) (proj₁ a) k m ,
  level-below (actM g M) (proj₂ (AtI-act g {p} {M} h a)) (proj₁ (AtI-act g {p} {M} h a)) k m
under-below ε _ _ k m = tt
under-below (u • v) {p} {M} (hu , hv) a k m =
  under-below v {p} {M} hv a k m , under-below u {p} {actMʷ v M} hu (AtI-actʷ v {p} {M} hv a) k m

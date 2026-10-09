------------------------------------------------------------------------
-- Presentations of groups
--
-- Correctness of Algorithm 1: for an orthogonal matrix M ≠ I, one
-- output of the algorithm lowers the level (Lemmas 3.2–3.4).
--
-- * If the pivot column v has k = lde v = 0, it is ±e_m (Norm.lde0,
--   Lemma 3.3), and the syllable (-1)_[p] or X_[m,p] (-1)_[m]^τ turns
--   it into e_p, so the pivot drops.
-- * If k > 0, the number of odd entries of 2ᵏ v is a multiple of 4
--   (Norm.nodd-mod4), so there are four odd entries a < b < c < d;
--   they are 1 + 2y (Residue.one2), and the sign of the syllable makes
--   the sum of the y's even, so that K_[a,b,c,d] makes them even
--   (Lemma A.2): the number of odd entries drops by four, or the
--   exponent drops.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Step where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; _∨_ ; _xor_ ; not ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Solver as ℤSolver
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; _%_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; dec-true ; dec-false)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH-TwoLevel.Ring
open import Examples.Groups.CCX+HH-TwoLevel.Scale
open import Examples.Groups.CCX+HH-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Search hiding (count-three)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Counting using (count-two ; count-three)
open import Examples.Groups.CCX+HH-TwoLevel.Norm using (sq ; Σℕ ; nodd-mod4 ; lde0 ; unit-norm)
open import Examples.Groups.CCX+HH-TwoLevel.Residue using (τ ; sgn ; one2 ; τ-neg)
open import Examples.Groups.CCX+HH-TwoLevel.Column
open import Examples.Groups.CCX+HH-TwoLevel.ColumnAction
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot
open import Examples.Groups.CCX+HH-TwoLevel.Syllable

private
  variable
    n : ℕ
  module ℤS = ℤSolver.+-*-Solver

------------------------------------------------------------------------
-- The numerator of the pivot column
--
-- Beyond the pivot, the columns are those of the identity, so by
-- orthogonality the pivot column vanishes there; being a unit vector,
-- its numerator has Σ wₓ² = 4ᵏ.

pivot-zero> : {M : Matrix n n D} → ColOrth M → ∀ {p} → pivot M ≡ just p →
              ∀ x → p < x → num (col M p) ! x ≡ + 0
pivot-zero> {M = M} o {p} pv x p<x = sc-injective (lde (col M p)) (begin
  sc (lde (col M p)) (num (col M p) ! x)          ≡⟨ sym (scV-! (lde (col M p)) (num (col M p)) x) ⟩
  scV (lde (col M p)) (num (col M p)) ! x         ≡⟨ cong (_! x) (sym (lde-eq (col M p))) ⟩
  col M p ! x                                     ≡⟨ col-vanish o (proj₂ (pivot-just M pv) x p<x) (λ { refl → ℕP.<-irrefl refl p<x }) ⟩
  DR.0#                                           ≡⟨ sym (sc-0 (lde (col M p))) ⟩
  sc (lde (col M p)) (+ 0)                        ∎)
  where open ≡-Reasoning

col-norm : {M : Matrix n n D} → ColOrth M → (p : Fin n) →
           Σℕ (λ x → sq (num (col M p) ! x)) ≡ 4 ℕ.^ lde (col M p)
col-norm {M = M} o p =
  unit-norm (lde (col M p)) (num (col M p))
    (subst (λ u → ⟨ u , u ⟩ ≡ DR.1#) (lde-eq (col M p)) (col-unit o p))

-- The odd entries are at indices ≤ p.
odd⇒≤ : {p : Fin n} {w : Vec ℤ n} → (∀ x → p < x → w ! x ≡ + 0) → ∀ {x} → Odd (w ! x) → x ≤ p
odd⇒≤ {p = p} {w} zero> {x} ox = tri-elim (FinP.<-cmp p x)
  (λ p<x → ⊥-elim (Odd⇒¬Even {w ! x} ox (cong oddℤ (zero> x p<x))))
  (λ { refl → FinP.≤-refl })
  (λ x<p → ℕP.<⇒≤ x<p)

------------------------------------------------------------------------
-- Doubling a numerator

scV-2map : ∀ k (W : Vec ℤ n) → scV (suc k) (Vec.map (+ 2 ℤ.*_) W) ≡ scV k W
scV-2map k W = vec-ext λ x → begin
  scV (suc k) (Vec.map (+ 2 ℤ.*_) W) ! x     ≡⟨ scV-! (suc k) (Vec.map (+ 2 ℤ.*_) W) x ⟩
  sc (suc k) (Vec.map (+ 2 ℤ.*_) W ! x)      ≡⟨ cong (sc (suc k)) (VecP.lookup-map x (+ 2 ℤ.*_) W) ⟩
  sc (suc k) (+ 2 ℤ.* (W ! x))               ≡⟨ sc-2 k (W ! x) ⟩
  sc k (W ! x)                               ≡⟨ sym (scV-! k W x) ⟩
  scV k W ! x                                ∎
  where open ≡-Reasoning

private
  cong-actVʷ : (u : Word (Gen n)) (x y : Vec D n) → x ≡ y → actVʷ u x ≡ actVʷ u y
  cong-actVʷ u x y refl = refl

  cong₄ : ∀ {A B : Set} (f : A → A → A → A → B) {x x′ y y′ z z′ t t′} →
          x ≡ x′ → y ≡ y′ → z ≡ z′ → t ≡ t′ → f x y z t ≡ f x′ y′ z′ t′
  cong₄ f refl refl refl refl = refl

------------------------------------------------------------------------
-- k = 0: the syllable restores e_p

private
  -- A vector that is 1 at m and 0 elsewhere is e_m.
  set₁-e : (m : Fin n) (w : Vec ℤ n) → (∀ y → y ≢ m → w ! y ≡ + 0) → set₁ m (+ 1) w ≡ eᶻ m
  set₁-e m w rest = vec-ext λ x → dec-elim (x FinP.≟ m)
    (λ { refl → trans (set₁-a x (+ 1) w) (sym (trans (eᶻ-! x x) (eδ-refl x))) })
    (λ x≢m → trans (set₁-≢ m (+ 1) w x≢m) (trans (rest x x≢m) (sym (trans (eᶻ-! m x) (eδ-≢ x≢m)))))

  -- Swapping it to p gives e_p.
  Xᶻ-e : (m p : Fin n) → m ≢ p → (w : Vec ℤ n) → (∀ y → y ≢ m → w ! y ≡ + 0) →
         Xᶻ m p (set₁ m (+ 1) w) ≡ eᶻ p
  Xᶻ-e m p m≢p w rest = vec-ext λ x → dec-elim (x FinP.≟ m)
    (λ { refl → begin
          Xᶻ x p u ! x         ≡⟨ set₂-a x p (u ! p) (u ! x) u ⟩
          u ! p                ≡⟨ set₁-≢ x (+ 1) w (m≢p ∘ sym) ⟩
          w ! p                ≡⟨ rest p (m≢p ∘ sym) ⟩
          + 0                  ≡⟨ sym (trans (eᶻ-! p x) (eδ-≢ m≢p)) ⟩
          eᶻ p ! x             ∎ })
    (λ x≢m → dec-elim (x FinP.≟ p)
      (λ { refl → begin
            Xᶻ m x u ! x       ≡⟨ set₂-b m x (u ! x) (u ! m) u m≢p ⟩
            u ! m              ≡⟨ set₁-a m (+ 1) w ⟩
            + 1                ≡⟨ sym (trans (eᶻ-! x x) (eδ-refl x)) ⟩
            eᶻ x ! x           ∎ })
      (λ x≢p → begin
            Xᶻ m p u ! x       ≡⟨ set₂-≢ m p (u ! p) (u ! m) u x≢m x≢p ⟩
            u ! x              ≡⟨ set₁-≢ m (+ 1) w x≢m ⟩
            w ! x              ≡⟨ rest x x≢m ⟩
            + 0                ≡⟨ sym (trans (eᶻ-! p x) (eδ-≢ x≢p)) ⟩
            eᶻ p ! x           ∎))
    where
    open ≡-Reasoning
    u = set₁ m (+ 1) w

  -- (-1)_[m]^τ makes the unit at m positive.
  Mfix : (w : Vec ℤ n) (m : Fin n) → (w ! m ≡ + 1 ⊎ w ! m ≡ -[1+ 0 ]) →
         (if negℤ (w ! m) then Mᶻ m w else w) ≡ set₁ m (+ 1) w
  Mfix w m (inj₁ e) = trans (cong (λ z → if negℤ z then Mᶻ m w else w) e)
                            (trans (sym (set₁-self m w)) (cong (λ z → set₁ m z w) e))
  Mfix w m (inj₂ e) = trans (cong (λ z → if negℤ z then Mᶻ m w else w) e) (cong (λ z → set₁ m (ℤ.- z) w) e)

  unit≢0 : ∀ {u} → (u ≡ + 1 ⊎ u ≡ -[1+ 0 ]) → u ≢ + 0
  unit≢0 (inj₁ refl) ()
  unit≢0 (inj₂ refl) ()

  Within-Mτ : ∀ {p a : Fin n} t → a ≤ p → Within p (Mτ a t)
  Within-Mτ true  a≤p = a≤p
  Within-Mτ false a≤p = tt

unit-step : ∀ {p : Fin n} (w : Vec ℤ n) → Σℕ (λ x → sq (w ! x)) ≡ 1 → (∀ x → p < x → w ! x ≡ + 0) →
            Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
unit-step {n} {p} w norm zero> = go (lde0 w norm)
  where
  open ≡-Reasoning
  go : (∃ λ m → (w ! m ≡ + 1 ⊎ w ! m ≡ -[1+ 0 ]) × (∀ y → y ≢ m → w ! y ≡ + 0)) →
       Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
  go (m , um , rest) =
    tri-elim (FinP.<-cmp m p) case< case≡ (λ p<m → ⊥-elim (unit≢0 um (zero> m p<m)))
    where
    fo : firstOdd w ≡ just m
    fo = firstOdd-char w (unit-odd um) (λ x x<m → cong oddℤ (rest x (λ { refl → ℕP.<-irrefl refl x<m })))
    t = negℤ (w ! m)
    u = if t then Mᶻ m w else w
    u≡ : u ≡ set₁ m (+ 1) w
    u≡ = Mfix w m um
    case< : m < p → Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
    case< m<p = subst (λ W → Within p W × actVʷ W (scV 0 w) ≡ scV 0 (eᶻ p)) (sym (sylData-unit< w fo m<p))
      ( (FinP.≤-refl , Within-Mτ t (ℕP.<⇒≤ m<p))
      , (begin
          actV (X-gen m p m<p) (actVʷ (Mτ m t) (scV 0 w))
            ≡⟨ cong-actVʷ (X m p m<p) _ _ (Mτ-action m t 0 w) ⟩
          actV (X-gen m p m<p) (scV 0 u)
            ≡⟨ actV-X m p m<p 0 u ⟩
          scV 0 (Xᶻ m p u)
            ≡⟨ cong (scV 0) (trans (cong (Xᶻ m p) u≡) (Xᶻ-e m p (<⇒≢ m<p) w rest)) ⟩
          scV 0 (eᶻ p) ∎))
    case≡ : m ≡ p → Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
    case≡ refl = subst (λ W → Within p W × actVʷ W (scV 0 w) ≡ scV 0 (eᶻ p)) (sym (sylData-unit≡ w fo))
      ( Within-Mτ t FinP.≤-refl
      , (begin
          actVʷ (Mτ m t) (scV 0 w)        ≡⟨ Mτ-action m t 0 w ⟩
          scV 0 u                         ≡⟨ cong (scV 0) (trans u≡ (set₁-e m w rest)) ⟩
          scV 0 (eᶻ m) ∎))

------------------------------------------------------------------------
-- k > 0: K on four odd entries ≡ 1 (mod 4) makes them even

-- (-1)_[a]^τ on numerators.
sgnAt : Fin n → Bool → Vec ℤ n → Vec ℤ n
sgnAt a t w = if t then Mᶻ a w else w

sgnAt-at : ∀ (a : Fin n) t w → sgnAt a t w ! a ≡ sgn t (w ! a)
sgnAt-at a true  w = set₁-a a (ℤ.- (w ! a)) w
sgnAt-at a false w = refl

sgnAt-off : ∀ (a : Fin n) t w {x} → x ≢ a → sgnAt a t w ! x ≡ w ! x
sgnAt-off a true  w x≢a = set₁-≢ a (ℤ.- (w ! a)) w x≢a
sgnAt-off a false w x≢a = refl

-- 1 + 2y.
o2 : ℤ → ℤ
o2 y = + 1 ℤ.+ + 2 ℤ.* y

-- With y_a + y_b + y_c + y_d = 2T: y_a.
ya-of : (yb yc yd T : ℤ) → ℤ
ya-of yb yc yd T = + 2 ℤ.* T ℤ.- yb ℤ.- yc ℤ.- yd

-- The numerator after K_[a,b,c,d] on entries uₓ = 1 + 2yₓ with an even
-- sum y_a + y_b + y_c + y_d = 2T, back at the same scale: the four
-- entries become even.
quadW : (u : Vec ℤ n) (a b c d : Fin n) (yb yc yd T : ℤ) → Vec ℤ n
quadW u a b c d yb yc yd T =
  set₄ a b c d (+ 2 ℤ.* (+ 1 ℤ.+ T)) (+ 2 ℤ.* (T ℤ.- yb ℤ.- yd))
               (+ 2 ℤ.* (T ℤ.- yc ℤ.- yd)) (+ 2 ℤ.* (T ℤ.- yb ℤ.- yc)) u

private
  open ℤS using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

  idA : ∀ yb yc yd T → rowAᶻ (o2 (ya-of yb yc yd T)) (o2 yb) (o2 yc) (o2 yd) ≡ + 2 ℤ.* (+ 2 ℤ.* (+ 1 ℤ.+ T))
  idA = ℤS.solve 4 (λ yb yc yd T →
    con (+ 1) :* (con (+ 1) :+ con (+ 2) :* (con (+ 2) :* T :- yb :- yc :- yd))
      :+ con (+ 1) :* (con (+ 1) :+ con (+ 2) :* yb)
      :+ con (+ 1) :* (con (+ 1) :+ con (+ 2) :* yc) :+ con (+ 1) :* (con (+ 1) :+ con (+ 2) :* yd)
    := con (+ 2) :* (con (+ 2) :* (con (+ 1) :+ T))) refl

  idB : ∀ yb yc yd T → rowBᶻ (o2 (ya-of yb yc yd T)) (o2 yb) (o2 yc) (o2 yd) ≡ + 2 ℤ.* (+ 2 ℤ.* (T ℤ.- yb ℤ.- yd))
  idB = ℤS.solve 4 (λ yb yc yd T →
    con (+ 1) :* (con (+ 1) :+ con (+ 2) :* (con (+ 2) :* T :- yb :- yc :- yd))
      :+ con -[1+ 0 ] :* (con (+ 1) :+ con (+ 2) :* yb)
      :+ con (+ 1) :* (con (+ 1) :+ con (+ 2) :* yc) :+ con -[1+ 0 ] :* (con (+ 1) :+ con (+ 2) :* yd)
    := con (+ 2) :* (con (+ 2) :* (T :- yb :- yd))) refl

  idC : ∀ yb yc yd T → rowCᶻ (o2 (ya-of yb yc yd T)) (o2 yb) (o2 yc) (o2 yd) ≡ + 2 ℤ.* (+ 2 ℤ.* (T ℤ.- yc ℤ.- yd))
  idC = ℤS.solve 4 (λ yb yc yd T →
    con (+ 1) :* (con (+ 1) :+ con (+ 2) :* (con (+ 2) :* T :- yb :- yc :- yd))
      :+ con (+ 1) :* (con (+ 1) :+ con (+ 2) :* yb)
      :+ con -[1+ 0 ] :* (con (+ 1) :+ con (+ 2) :* yc) :+ con -[1+ 0 ] :* (con (+ 1) :+ con (+ 2) :* yd)
    := con (+ 2) :* (con (+ 2) :* (T :- yc :- yd))) refl

  idD : ∀ yb yc yd T → rowDᶻ (o2 (ya-of yb yc yd T)) (o2 yb) (o2 yc) (o2 yd) ≡ + 2 ℤ.* (+ 2 ℤ.* (T ℤ.- yb ℤ.- yc))
  idD = ℤS.solve 4 (λ yb yc yd T →
    con (+ 1) :* (con (+ 1) :+ con (+ 2) :* (con (+ 2) :* T :- yb :- yc :- yd))
      :+ con -[1+ 0 ] :* (con (+ 1) :+ con (+ 2) :* yb)
      :+ con -[1+ 0 ] :* (con (+ 1) :+ con (+ 2) :* yc) :+ con (+ 1) :* (con (+ 1) :+ con (+ 2) :* yd)
    := con (+ 2) :* (con (+ 2) :* (T :- yb :- yc))) refl

K-quad : ∀ k (u : Vec ℤ n) (a b c d : Fin n) .(p : a < b) .(q : b < c) .(r : c < d) (yb yc yd T : ℤ) →
         u ! a ≡ o2 (ya-of yb yc yd T) → u ! b ≡ o2 yb → u ! c ≡ o2 yc → u ! d ≡ o2 yd →
         actV (K-gen a b c d p q r) (scV k u) ≡ scV k (quadW u a b c d yb yc yd T)
K-quad k u a b c d p q r yb yc yd T ea eb ec ed =
  trans (actV-K a b c d p q r k u) (trans (cong (scV (suc k)) Kq) (scV-2map k W))
  where
  open ≡-Reasoning
  W = quadW u a b c d yb yc yd T
  D₄ = distinct₄ p q r
  du = Vec.map (+ 2 ℤ.*_) u
  dW = Vec.map (+ 2 ℤ.*_) W
  ents : ∀ (f : ℤ → ℤ → ℤ → ℤ → ℤ) → f (u ! a) (u ! b) (u ! c) (u ! d) ≡ f (o2 (ya-of yb yc yd T)) (o2 yb) (o2 yc) (o2 yd)
  ents f = cong₄ f ea eb ec ed
  twice : ∀ x → + 2 ℤ.* (W ! x) ≡ dW ! x
  twice x = sym (VecP.lookup-map x (+ 2 ℤ.*_) W)
  at : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Dec (x ≡ c) → Dec (x ≡ d) → Kᶻ a b c d u ! x ≡ dW ! x
  at x (yes refl) _ _ _ =
    trans (set₄-a D₄ _ _ _ _ du) (trans (ents rowAᶻ) (trans (idA yb yc yd T)
      (trans (cong (+ 2 ℤ.*_) (sym (set₄-a D₄ _ _ _ _ u))) (twice x))))
  at x (no _) (yes refl) _ _ =
    trans (set₄-b D₄ _ _ _ _ du) (trans (ents rowBᶻ) (trans (idB yb yc yd T)
      (trans (cong (+ 2 ℤ.*_) (sym (set₄-b D₄ _ _ _ _ u))) (twice x))))
  at x (no _) (no _) (yes refl) _ =
    trans (set₄-c D₄ _ _ _ _ du) (trans (ents rowCᶻ) (trans (idC yb yc yd T)
      (trans (cong (+ 2 ℤ.*_) (sym (set₄-c D₄ _ _ _ _ u))) (twice x))))
  at x (no _) (no _) (no _) (yes refl) =
    trans (set₄-d D₄ _ _ _ _ du) (trans (ents rowDᶻ) (trans (idD yb yc yd T)
      (trans (cong (+ 2 ℤ.*_) (sym (set₄-d D₄ _ _ _ _ u))) (twice x))))
  at x (no xa) (no xb) (no xc) (no xd) =
    trans (set₄-≢ D₄ _ _ _ _ du xa xb xc xd) (trans (VecP.lookup-map x (+ 2 ℤ.*_) u)
      (trans (cong (+ 2 ℤ.*_) (sym (set₄-≢ D₄ _ _ _ _ u xa xb xc xd))) (twice x)))
  Kq : Kᶻ a b c d u ≡ dW
  Kq = vec-ext λ x → at x (x FinP.≟ a) (x FinP.≟ b) (x FinP.≟ c) (x FinP.≟ d)

------------------------------------------------------------------------
-- Turning four indices from true to false lowers a count by four

count-drop₄ : (P Q : Fin n → Bool) {a b c d : Fin n} → Distinct₄ a b c d →
              P a ≡ true → P b ≡ true → P c ≡ true → P d ≡ true →
              Q a ≡ false → Q b ≡ false → Q c ≡ false → Q d ≡ false →
              (∀ x → x ≢ a → x ≢ b → x ≢ c → x ≢ d → P x ≡ Q x) → count P ≡ 4 ℕ.+ count Q
count-drop₄ {n} P Q {a} {b} {c} {d} D₄ Pa Pb Pc Pd Qa Qb Qc Qd agree =
  trans (count-drop₂ P Pab a b ab Pa Pb Ra Rb agreePR) (cong (λ m → 2 ℕ.+ m) (count-drop₂ Pab Q c d cd Rc Rd Qc Qd agreeRQ))
  where
  open Distinct₄ D₄
  Pab : Fin n → Bool
  Pab x = if does (x FinP.≟ a) ∨ does (x FinP.≟ b) then false else P x
  if-t : ∀ {t : Bool} {x y : Bool} → t ≡ true → (if t then x else y) ≡ x
  if-t refl = refl
  if-f : ∀ {t : Bool} {x y : Bool} → t ≡ false → (if t then x else y) ≡ y
  if-f refl = refl
  off : ∀ x → x ≢ a → x ≢ b → Pab x ≡ P x
  off x xa xb = if-f (cong₂ _∨_ (dec-false (x FinP.≟ a) xa) (dec-false (x FinP.≟ b) xb))
  Ra : Pab a ≡ false
  Ra = if-t (cong (_∨ does (a FinP.≟ b)) (dec-true (a FinP.≟ a) refl))
  Rb : Pab b ≡ false
  Rb = if-t (trans (cong (does (b FinP.≟ a) ∨_) (dec-true (b FinP.≟ b) refl)) (∨-true (does (b FinP.≟ a))))
    where
    ∨-true : ∀ t → t ∨ true ≡ true
    ∨-true true  = refl
    ∨-true false = refl
  Rc : Pab c ≡ true
  Rc = trans (off c (λ e → ac (sym e)) (λ e → bc (sym e))) Pc
  Rd : Pab d ≡ true
  Rd = trans (off d (λ e → ad (sym e)) (λ e → bd (sym e))) Pd
  agreePR : ∀ x → x ≢ a → x ≢ b → P x ≡ Pab x
  agreePR x xa xb = sym (off x xa xb)
  agreeRQ : ∀ x → x ≢ c → x ≢ d → Pab x ≡ Q x
  agreeRQ x xc xd = dec-elim (x FinP.≟ a)
    (λ { refl → trans Ra (sym Qa) })
    (λ xa → dec-elim (x FinP.≟ b)
      (λ { refl → trans Rb (sym Qb) })
      (λ xb → trans (off x xa xb) (agree x xa xb xc xd)))

------------------------------------------------------------------------
-- Signs and residues

private
  sgn-odd : ∀ t x → oddℤ (sgn t x) ≡ oddℤ x
  sgn-odd true  x = oddℤ-neg x
  sgn-odd false x = refl

  τ-sgn : ∀ t x → oddℤ x ≡ true → τ (sgn t x) ≡ t xor τ x
  τ-sgn true  x o = τ-neg x o
  τ-sgn false x o = refl

  xor-twice : ∀ p q r s → ((((((p xor q) xor r) xor s) xor p) xor q) xor r) xor s ≡ false
  xor-twice true  true  true  true  = refl
  xor-twice true  true  true  false = refl
  xor-twice true  true  false true  = refl
  xor-twice true  true  false false = refl
  xor-twice true  false true  true  = refl
  xor-twice true  false true  false = refl
  xor-twice true  false false true  = refl
  xor-twice true  false false false = refl
  xor-twice false true  true  true  = refl
  xor-twice false true  true  false = refl
  xor-twice false true  false true  = refl
  xor-twice false true  false false = refl
  xor-twice false false true  true  = refl
  xor-twice false false true  false = refl
  xor-twice false false false true  = refl
  xor-twice false false false false = refl

  module ℤS′ where
    open ℤS using (_:+_ ; _:*_ ; _:-_ ; _:=_ ; con)
    -- From ya + yb + yc + yd = T + T: ya = 2T - yb - yc - yd.
    solve-sum : ∀ ya yb yc yd T → ((ya ℤ.+ yb) ℤ.+ yc) ℤ.+ yd ≡ T ℤ.+ T → ya ≡ ya-of yb yc yd T
    solve-sum ya yb yc yd T e = begin
      ya                                               ≡⟨ ℤS.solve 4 (λ ya yb yc yd → ya := (((ya :+ yb) :+ yc) :+ yd) :- yb :- yc :- yd) refl ya yb yc yd ⟩
      (((ya ℤ.+ yb) ℤ.+ yc) ℤ.+ yd) ℤ.- yb ℤ.- yc ℤ.- yd ≡⟨ cong (λ z → z ℤ.- yb ℤ.- yc ℤ.- yd) e ⟩
      (T ℤ.+ T) ℤ.- yb ℤ.- yc ℤ.- yd                   ≡⟨ ℤS.solve 4 (λ T yb yc yd → (T :+ T) :- yb :- yc :- yd := con (+ 2) :* T :- yb :- yc :- yd) refl T yb yc yd ⟩
      ya-of yb yc yd T                                 ∎
      where open ≡-Reasoning

------------------------------------------------------------------------
-- The syllable of four odd entries

private
  Goal : Fin n → ℕ → Vec ℤ n → Set
  Goal p k w = ∃ λ W′ → Within p (sylData p (suc k) w)
                      × actVʷ (sylData p (suc k) w) (scV (suc k) w) ≡ scV (suc k) W′
                      × nodd w ≡ 4 ℕ.+ nodd W′

-- The syllable, given the first four odd entries.
quad-core : ∀ {p : Fin n} k′ (w : Vec ℤ n) {a b c d : Fin n} →
            firstOdd w ≡ just a → nextOdd a w ≡ just b → nextOdd b w ≡ just c → nextOdd c w ≡ just d →
            d ≤ p → Goal p k′ w
quad-core {n} {p} k′ w {a} {b} {c} {d} fo na nb nc d≤p = W′ , within , act , cnt
  where
  open ≡-Reasoning
  a<b = proj₁ (nextOdd-spec w na)
  b<c = proj₁ (nextOdd-spec w nb)
  c<d = proj₁ (nextOdd-spec w nc)
  D₄ = distinct₄ a<b b<c c<d
  open Distinct₄ D₄
  oa = proj₁ (firstOdd-spec w fo)
  ob = proj₁ (proj₂ (nextOdd-spec w na))
  oc = proj₁ (proj₂ (nextOdd-spec w nb))
  od = proj₁ (proj₂ (nextOdd-spec w nc))
  t = σ₄ w a b c d
  u = sgnAt a t w
  sym≢ : ∀ {x y : Fin n} → x ≢ y → y ≢ x
  sym≢ ne e = ne (sym e)
  ua≡ : u ! a ≡ sgn t (w ! a)
  ua≡ = sgnAt-at a t w
  oua : oddℤ (u ! a) ≡ true
  oua = trans (cong oddℤ ua≡) (trans (sgn-odd t (w ! a)) oa)
  -- The entries as 1 + 2y.
  Ya = one2 (u ! a) oua
  Yb = one2 (w ! b) ob
  Yc = one2 (w ! c) oc
  Yd = one2 (w ! d) od
  ya = proj₁ Ya
  yb = proj₁ Yb
  yc = proj₁ Yc
  yd = proj₁ Yd
  -- The sign makes the sum of the y's even.
  par : oddℤ (((ya ℤ.+ yb) ℤ.+ yc) ℤ.+ yd) ≡ false
  par = begin
    oddℤ (((ya ℤ.+ yb) ℤ.+ yc) ℤ.+ yd)
      ≡⟨ trans (oddℤ-+ ((ya ℤ.+ yb) ℤ.+ yc) yd) (cong (_xor oddℤ yd) (trans (oddℤ-+ (ya ℤ.+ yb) yc) (cong (_xor oddℤ yc) (oddℤ-+ ya yb)))) ⟩
    ((oddℤ ya xor oddℤ yb) xor oddℤ yc) xor oddℤ yd
      ≡⟨ cong₄ (λ p q r s → ((p xor q) xor r) xor s) (proj₂ (proj₂ Ya)) (proj₂ (proj₂ Yb)) (proj₂ (proj₂ Yc)) (proj₂ (proj₂ Yd)) ⟩
    ((τ (u ! a) xor τ (w ! b)) xor τ (w ! c)) xor τ (w ! d)
      ≡⟨ cong (λ x → ((x xor τ (w ! b)) xor τ (w ! c)) xor τ (w ! d)) (trans (cong τ ua≡) (τ-sgn t (w ! a) oa)) ⟩
    (((t xor τ (w ! a)) xor τ (w ! b)) xor τ (w ! c)) xor τ (w ! d)
      ≡⟨ xor-twice (τ (w ! a)) (τ (w ! b)) (τ (w ! c)) (τ (w ! d)) ⟩
    false ∎
  H = evenℤ-half (((ya ℤ.+ yb) ℤ.+ yc) ℤ.+ yd) par
  T = proj₁ H
  ya≡ : ya ≡ ya-of yb yc yd T
  ya≡ = ℤS′.solve-sum ya yb yc yd T (proj₂ H)
  ua : u ! a ≡ o2 (ya-of yb yc yd T)
  ua = trans (proj₁ (proj₂ Ya)) (cong o2 ya≡)
  ub : u ! b ≡ o2 yb
  ub = trans (sgnAt-off a t w (sym≢ ab)) (proj₁ (proj₂ Yb))
  uc : u ! c ≡ o2 yc
  uc = trans (sgnAt-off a t w (sym≢ ac)) (proj₁ (proj₂ Yc))
  ud : u ! d ≡ o2 yd
  ud = trans (sgnAt-off a t w (sym≢ ad)) (proj₁ (proj₂ Yd))
  W′ = quadW u a b c d yb yc yd T
  syl≡ : sylData p (suc k′) w ≡ quadSyl a b c d a<b b<c c<d w
  syl≡ = sylData-quad {p = p} k′ w fo na nb nc a<b b<c c<d
  a≤p = ℕP.<⇒≤ (FinP.<-trans a<b (FinP.<-trans b<c (ℕP.<-≤-trans c<d d≤p)))
  within : Within p (sylData p (suc k′) w)
  within = subst (Within p) (sym syl≡) (d≤p , Within-Mτ t a≤p)
  K′ = suc k′
  act : actVʷ (sylData p (suc k′) w) (scV (suc k′) w) ≡ scV (suc k′) W′
  act = subst (λ S → actVʷ S (scV K′ w) ≡ scV K′ W′) (sym syl≡) (begin
    actV (K-gen a b c d a<b b<c c<d) (actVʷ (Mτ a t) (scV K′ w))
      ≡⟨ cong-actVʷ (K a b c d a<b b<c c<d) _ _ (Mτ-action a t K′ w) ⟩
    actV (K-gen a b c d a<b b<c c<d) (scV K′ u)
      ≡⟨ K-quad K′ u a b c d a<b b<c c<d yb yc yd T ua ub uc ud ⟩
    scV K′ W′ ∎)
  cnt : nodd w ≡ 4 ℕ.+ nodd W′
  cnt = count-drop₄ (λ x → oddℤ (w ! x)) (λ x → oddℤ (W′ ! x)) D₄ oa ob oc od
    (trans (cong oddℤ (set₄-a D₄ _ _ _ _ u)) (even-2* (+ 1 ℤ.+ T)))
    (trans (cong oddℤ (set₄-b D₄ _ _ _ _ u)) (even-2* (T ℤ.- yb ℤ.- yd)))
    (trans (cong oddℤ (set₄-c D₄ _ _ _ _ u)) (even-2* (T ℤ.- yc ℤ.- yd)))
    (trans (cong oddℤ (set₄-d D₄ _ _ _ _ u)) (even-2* (T ℤ.- yb ℤ.- yc)))
    (λ x xa xb xc xd → sym (cong oddℤ (trans (set₄-≢ D₄ _ _ _ _ u xa xb xc xd) (sgnAt-off a t w xa))))

------------------------------------------------------------------------
-- k > 0: four odd entries exist

private
  -- If the odd entries are exactly those given, the count is known.
  inside₂ : (w : Vec ℤ n) {a b : Fin n} → firstOdd w ≡ just a → nextOdd a w ≡ just b → nextOdd b w ≡ nothing →
            ∀ y → oddℤ (w ! y) ≡ true → y ≡ a ⊎ y ≡ b
  inside₂ w {a} {b} fo na nb y oy = tri-elim (FinP.<-cmp y a)
    (λ y<a → ⊥-elim (Odd⇒¬Even {w ! y} oy (proj₂ (firstOdd-spec w fo) y y<a)))
    inj₁
    (λ a<y → tri-elim (FinP.<-cmp y b)
      (λ y<b → ⊥-elim (Odd⇒¬Even {w ! y} oy (proj₂ (proj₂ (nextOdd-spec w na)) y a<y y<b)))
      inj₂
      (λ b<y → ⊥-elim (Odd⇒¬Even {w ! y} oy (nextOdd-nothing w nb y b<y))))

  inside₃ : (w : Vec ℤ n) {a b c : Fin n} → firstOdd w ≡ just a → nextOdd a w ≡ just b → nextOdd b w ≡ just c →
            nextOdd c w ≡ nothing → ∀ y → oddℤ (w ! y) ≡ true → y ≡ a ⊎ y ≡ b ⊎ y ≡ c
  inside₃ w {a} {b} {c} fo na nb nc y oy = tri-elim (FinP.<-cmp y a)
    (λ y<a → ⊥-elim (Odd⇒¬Even {w ! y} oy (proj₂ (firstOdd-spec w fo) y y<a)))
    inj₁
    (λ a<y → tri-elim (FinP.<-cmp y b)
      (λ y<b → ⊥-elim (Odd⇒¬Even {w ! y} oy (proj₂ (proj₂ (nextOdd-spec w na)) y a<y y<b)))
      (λ e → inj₂ (inj₁ e))
      (λ b<y → tri-elim (FinP.<-cmp y c)
        (λ y<c → ⊥-elim (Odd⇒¬Even {w ! y} oy (proj₂ (proj₂ (nextOdd-spec w nb)) y b<y y<c)))
        (λ e → inj₂ (inj₂ e))
        (λ c<y → ⊥-elim (Odd⇒¬Even {w ! y} oy (nextOdd-nothing w nc y c<y)))))

  -- The residues 1, 2 and 3 modulo 4 are not 0.
  1%4 : 1 % 4 ≢ 0
  1%4 ()
  2%4 : 2 % 4 ≢ 0
  2%4 ()
  3%4 : 3 % 4 ≢ 0
  3%4 ()

-- The first four odd entries.
record Quad (w : Vec ℤ n) : Set where
  constructor quad⟨_,_,_,_⟩
  field
    {a b c d} : Fin n
    fo : firstOdd w ≡ just a
    na : nextOdd a w ≡ just b
    nb : nextOdd b w ≡ just c
    nc : nextOdd c w ≡ just d

quad-exists : ∀ k′ (w : Vec ℤ n) → Minimal (suc k′) w → Σℕ (λ x → sq (w ! x)) ≡ 4 ℕ.^ suc k′ → Quad w
quad-exists k′ w (inj₁ ()) norm
quad-exists {n} k′ w (inj₂ (x , ox)) norm = withA (firstOdd w) refl
  where
  m4 = nodd-mod4 k′ w norm
  P : Fin n → Bool
  P y = oddℤ (w ! y)
  withA : (r : Maybe (Fin n)) → firstOdd w ≡ r → Quad w
  withA nothing fo = ⊥-elim (Odd⇒¬Even {w ! x} ox (firstOdd-nothing w fo x))
  withA (just a) fo = withB (nextOdd a w) refl
    where
    oa = proj₁ (firstOdd-spec w fo)
    withB : (r : Maybe (Fin n)) → nextOdd a w ≡ r → Quad w
    withB nothing na = ⊥-elim (1%4 (trans (cong (_% 4) (sym one)) m4))
      where
      one : count P ≡ 1
      one = count-one P a oa (λ y y≢a → dec-elim (odd? (w ! y)) (λ oy → ⊥-elim (y≢a (only y oy))) (¬Odd⇒Even {w ! y}))
        where
        only : ∀ y → Odd (w ! y) → y ≡ a
        only y oy = tri-elim (FinP.<-cmp y a)
          (λ y<a → ⊥-elim (Odd⇒¬Even {w ! y} oy (proj₂ (firstOdd-spec w fo) y y<a)))
          (λ e → e)
          (λ a<y → ⊥-elim (Odd⇒¬Even {w ! y} oy (nextOdd-nothing w na y a<y)))
    withB (just b) na = withC (nextOdd b w) refl
      where
      ab = proj₁ (nextOdd-spec w na)
      ob = proj₁ (proj₂ (nextOdd-spec w na))
      withC : (r : Maybe (Fin n)) → nextOdd b w ≡ r → Quad w
      withC nothing nb = ⊥-elim (2%4 (trans (cong (_% 4) (sym two)) m4))
        where
        two : count P ≡ 2
        two = count-two P a b (<⇒≢ ab) oa ob (inside₂ w fo na nb)
      withC (just c) nb = withD (nextOdd c w) refl
        where
        bc = proj₁ (nextOdd-spec w nb)
        oc = proj₁ (proj₂ (nextOdd-spec w nb))
        withD : (r : Maybe (Fin n)) → nextOdd c w ≡ r → Quad w
        withD nothing nc = ⊥-elim (3%4 (trans (cong (_% 4) (sym three)) m4))
          where
          three : count P ≡ 3
          three = count-three P a b c (<⇒≢ ab) (<⇒≢ (FinP.<-trans ab bc)) (<⇒≢ bc) oa ob oc (inside₃ w fo na nb nc)
        withD (just d) nc = quad⟨ fo , na , nb , nc ⟩

quad-step : ∀ {p : Fin n} k′ (w : Vec ℤ n) → Minimal (suc k′) w →
            Σℕ (λ x → sq (w ! x)) ≡ 4 ℕ.^ suc k′ →
            (∀ {x} → Odd (w ! x) → x ≤ p) → Goal p k′ w
quad-step k′ w min norm ≤p with quad-exists k′ w min norm
... | quad⟨ fo , na , nb , nc ⟩ = quad-core k′ w fo na nb nc (≤p (proj₁ (proj₂ (nextOdd-spec w nc))))

------------------------------------------------------------------------
-- One step lowers the level

private
  scV-injective : ∀ k (u v : Vec ℤ n) → scV k u ≡ scV k v → u ≡ v
  scV-injective k u v eq = vec-ext λ x →
    sc-injective k (trans (sym (scV-! k u x)) (trans (cong (_! x) eq) (scV-! k v x)))

  -- The column p after the syllable S.
  col-step : (M : Matrix n n D) (p : Fin n) (S : Word (Gen n)) (K : ℕ) (W : Vec ℤ n) →
             col M p ≡ scV K W → col (actMʷ S M) p ≡ actVʷ S (scV K W)
  col-step M p S K W eq = trans (col-actMʷ S M p) (cong-actVʷ S (col M p) (scV K W) eq)

-- The level drops, given the data of the pivot column.
lt-core : (M : Matrix n n D) (p : Fin n) (K : ℕ) (W : Vec ℤ n) →
          Beyond p M → col M p ≡ scV K W → Minimal K W → (∀ x → p < x → W ! x ≡ + 0) →
          Σℕ (λ x → sq (W ! x)) ≡ 4 ℕ.^ K →
          level (actMʷ (sylData p K W) M) <ₗ (suc (toℕ p) , K , nodd W)
lt-core M p zero W be eq min zero> norm =
  level-below (actMʷ S M) col≡ (Beyond-actMʷ S {p} {M} (proj₁ us) be) zero (nodd W)
  where
  S = sylData p zero W
  us = unit-step W norm zero>
  col≡ : col (actMʷ S M) p ≡ col 𝕀 p
  col≡ = trans (col-step M p S zero W eq) (trans (proj₂ us) (sym (col𝕀≡ p)))
lt-core M p (suc K′) W be eq min zero> norm =
  go (quad-step K′ W min norm (odd⇒≤ {p = p} {W} zero>))
  where
  S = sylData p (suc K′) W
  go : (∃ λ W′ → Within p S × actVʷ S (scV (suc K′) W) ≡ scV (suc K′) W′ × nodd W ≡ 4 ℕ.+ nodd W′) →
       level (actMʷ S M) <ₗ (suc (toℕ p) , suc K′ , nodd W)
  go (W′ , within , act , cnt) =
    decide (col (actMʷ S M) p ≟ᵛ col 𝕀 p)
    where
    be′ : Beyond p (actMʷ S M)
    be′ = Beyond-actMʷ S {p} {M} within be
    col′ : col (actMʷ S M) p ≡ scV (suc K′) W′
    col′ = trans (col-step M p S (suc K′) W eq) act
    v = col (actMʷ S M) p
    -- With the same exponent, the numerator is W′.
    same : lde v ≡ suc K′ → num v ≡ W′
    same e = scV-injective (suc K′) (num v) W′
      (trans (cong (λ k → scV k (num v)) (sym e)) (trans (sym (lde-eq v)) col′))
    lt₂ : (lde v , nodd (num v)) <₂ (suc K′ , nodd W)
    lt₂ = [ inj₁
          , (λ e → inj₂ (e , subst (λ u → nodd u ℕ.< nodd W) (sym (same e))
                                   (subst (nodd W′ ℕ.<_) (sym cnt) (ℕ.s≤s (ℕP.m≤n+m (nodd W′) 3))))) ]′
          (ℕP.m≤n⇒m<n∨m≡n (lde-≤ (suc K′) W′ col′))
    -- (A helper with its type written out, rather than dec-elim.)
    decide : Dec (col (actMʷ S M) p ≡ col 𝕀 p) → level (actMʷ S M) <ₗ (suc (toℕ p) , suc K′ , nodd W)
    decide (yes e) = level-below (actMʷ S M) e be′ (suc K′) (nodd W)
    decide (no ne) = level-same (actMʷ S M) ne be′ lt₂

step-lt : {M : Matrix n n D} → ColOrth M → ∀ {p} → pivot M ≡ just p → level (step M) <ₗ level M
step-lt {M = M} o {p} pv =
  subst₂ _<ₗ_ (cong (λ S → level (actMʷ S M)) (sym (syl-just M pv))) (sym (level-just M pv))
    (lt-core M p (lde v) (num v) (proj₂ (pivot-just M pv)) (lde-eq v) (lde-min v)
             (pivot-zero> o pv) (col-norm o p))
  where
  v = col M p

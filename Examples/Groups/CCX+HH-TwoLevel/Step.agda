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
--   with the signs, they are 1 + 4z (Residue.one4), and K_[a,b,c,d]
--   makes them even (Lemma 3.1): the number of odd entries drops by
--   four, or the exponent drops.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Step where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; _∨_ ; not ; if_then_else_)
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
open import Examples.Groups.CCX+HH-TwoLevel.Residue using (τ ; sgn ; one4)
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

  unit-odd : ∀ {u} → (u ≡ + 1 ⊎ u ≡ -[1+ 0 ]) → Odd u
  unit-odd (inj₁ refl) = refl
  unit-odd (inj₂ refl) = refl

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

-- The numerator after K_[a,b,c,d] on entries uₓ = 1 + 4zₓ, back at the
-- same scale: the four entries become even.
quadW : (u : Vec ℤ n) (a b c d : Fin n) (za zb zc zd : ℤ) → Vec ℤ n
quadW u a b c d za zb zc zd =
  set₄ a b c d (+ 2 ℤ.* (+ 1 ℤ.+ za ℤ.+ zb ℤ.+ zc ℤ.+ zd)) (+ 2 ℤ.* (za ℤ.- zb ℤ.+ zc ℤ.- zd))
               (+ 2 ℤ.* (za ℤ.+ zb ℤ.- zc ℤ.- zd)) (+ 2 ℤ.* (za ℤ.- zb ℤ.- zc ℤ.+ zd)) u

-- 1 + 4z.
o4 : ℤ → ℤ
o4 z = + 1 ℤ.+ + 4 ℤ.* z

private
  open ℤS using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

  idA : ∀ za zb zc zd → rowAᶻ (o4 za) (o4 zb) (o4 zc) (o4 zd) ≡ + 2 ℤ.* (+ 2 ℤ.* (+ 1 ℤ.+ za ℤ.+ zb ℤ.+ zc ℤ.+ zd))
  idA = ℤS.solve 4 (λ za zb zc zd →
    con (+ 1) :* (con (+ 1) :+ con (+ 4) :* za) :+ con (+ 1) :* (con (+ 1) :+ con (+ 4) :* zb)
      :+ con (+ 1) :* (con (+ 1) :+ con (+ 4) :* zc) :+ con (+ 1) :* (con (+ 1) :+ con (+ 4) :* zd)
    := con (+ 2) :* (con (+ 2) :* (con (+ 1) :+ za :+ zb :+ zc :+ zd))) refl

  idB : ∀ za zb zc zd → rowBᶻ (o4 za) (o4 zb) (o4 zc) (o4 zd) ≡ + 2 ℤ.* (+ 2 ℤ.* (za ℤ.- zb ℤ.+ zc ℤ.- zd))
  idB = ℤS.solve 4 (λ za zb zc zd →
    con (+ 1) :* (con (+ 1) :+ con (+ 4) :* za) :+ con -[1+ 0 ] :* (con (+ 1) :+ con (+ 4) :* zb)
      :+ con (+ 1) :* (con (+ 1) :+ con (+ 4) :* zc) :+ con -[1+ 0 ] :* (con (+ 1) :+ con (+ 4) :* zd)
    := con (+ 2) :* (con (+ 2) :* (za :- zb :+ zc :- zd))) refl

  idC : ∀ za zb zc zd → rowCᶻ (o4 za) (o4 zb) (o4 zc) (o4 zd) ≡ + 2 ℤ.* (+ 2 ℤ.* (za ℤ.+ zb ℤ.- zc ℤ.- zd))
  idC = ℤS.solve 4 (λ za zb zc zd →
    con (+ 1) :* (con (+ 1) :+ con (+ 4) :* za) :+ con (+ 1) :* (con (+ 1) :+ con (+ 4) :* zb)
      :+ con -[1+ 0 ] :* (con (+ 1) :+ con (+ 4) :* zc) :+ con -[1+ 0 ] :* (con (+ 1) :+ con (+ 4) :* zd)
    := con (+ 2) :* (con (+ 2) :* (za :+ zb :- zc :- zd))) refl

  idD : ∀ za zb zc zd → rowDᶻ (o4 za) (o4 zb) (o4 zc) (o4 zd) ≡ + 2 ℤ.* (+ 2 ℤ.* (za ℤ.- zb ℤ.- zc ℤ.+ zd))
  idD = ℤS.solve 4 (λ za zb zc zd →
    con (+ 1) :* (con (+ 1) :+ con (+ 4) :* za) :+ con -[1+ 0 ] :* (con (+ 1) :+ con (+ 4) :* zb)
      :+ con -[1+ 0 ] :* (con (+ 1) :+ con (+ 4) :* zc) :+ con (+ 1) :* (con (+ 1) :+ con (+ 4) :* zd)
    := con (+ 2) :* (con (+ 2) :* (za :- zb :- zc :+ zd))) refl

K-quad : ∀ k (u : Vec ℤ n) (a b c d : Fin n) .(p : a < b) .(q : b < c) .(r : c < d) (za zb zc zd : ℤ) →
         u ! a ≡ o4 za → u ! b ≡ o4 zb → u ! c ≡ o4 zc → u ! d ≡ o4 zd →
         actV (K-gen a b c d p q r) (scV k u) ≡ scV k (quadW u a b c d za zb zc zd)
K-quad k u a b c d p q r za zb zc zd ea eb ec ed =
  trans (actV-K a b c d p q r k u) (trans (cong (scV (suc k)) Kq) (scV-2map k W))
  where
  open ≡-Reasoning
  W = quadW u a b c d za zb zc zd
  D₄ = distinct₄ p q r
  du = Vec.map (+ 2 ℤ.*_) u
  dW = Vec.map (+ 2 ℤ.*_) W
  ents : ∀ (f : ℤ → ℤ → ℤ → ℤ → ℤ) → f (u ! a) (u ! b) (u ! c) (u ! d) ≡ f (o4 za) (o4 zb) (o4 zc) (o4 zd)
  ents f = cong₄ f ea eb ec ed
  twice : ∀ x → + 2 ℤ.* (W ! x) ≡ dW ! x
  twice x = sym (VecP.lookup-map x (+ 2 ℤ.*_) W)
  at : ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Dec (x ≡ c) → Dec (x ≡ d) → Kᶻ a b c d u ! x ≡ dW ! x
  at x (yes refl) _ _ _ =
    trans (set₄-a D₄ _ _ _ _ du) (trans (ents rowAᶻ) (trans (idA za zb zc zd)
      (trans (cong (+ 2 ℤ.*_) (sym (set₄-a D₄ _ _ _ _ u))) (twice x))))
  at x (no _) (yes refl) _ _ =
    trans (set₄-b D₄ _ _ _ _ du) (trans (ents rowBᶻ) (trans (idB za zb zc zd)
      (trans (cong (+ 2 ℤ.*_) (sym (set₄-b D₄ _ _ _ _ u))) (twice x))))
  at x (no _) (no _) (yes refl) _ =
    trans (set₄-c D₄ _ _ _ _ du) (trans (ents rowCᶻ) (trans (idC za zb zc zd)
      (trans (cong (+ 2 ℤ.*_) (sym (set₄-c D₄ _ _ _ _ u))) (twice x))))
  at x (no _) (no _) (no _) (yes refl) =
    trans (set₄-d D₄ _ _ _ _ du) (trans (ents rowDᶻ) (trans (idD za zb zc zd)
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
  ta = τ (w ! a)
  tb = τ (w ! b)
  tc = τ (w ! c)
  td = τ (w ! d)
  u = sgnAt a ta (sgnAt b tb (sgnAt c tc (sgnAt d td w)))
  za = proj₁ (one4 (w ! a) oa)
  zb = proj₁ (one4 (w ! b) ob)
  zc = proj₁ (one4 (w ! c) oc)
  zd = proj₁ (one4 (w ! d) od)
  sym≢ : ∀ {x y : Fin n} → x ≢ y → y ≢ x
  sym≢ ne e = ne (sym e)
  ua : u ! a ≡ o4 za
  ua = trans (sgnAt-at a ta _) (trans (cong (sgn ta) (trans (sgnAt-off b tb _ ab) (trans (sgnAt-off c tc _ ac)
         (sgnAt-off d td w ad)))) (proj₂ (one4 (w ! a) oa)))
  ub : u ! b ≡ o4 zb
  ub = trans (sgnAt-off a ta _ (sym≢ ab)) (trans (sgnAt-at b tb _) (trans (cong (sgn tb) (trans (sgnAt-off c tc _ bc)
         (sgnAt-off d td w bd))) (proj₂ (one4 (w ! b) ob))))
  uc : u ! c ≡ o4 zc
  uc = trans (sgnAt-off a ta _ (sym≢ ac)) (trans (sgnAt-off b tb _ (sym≢ bc)) (trans (sgnAt-at c tc _)
         (trans (cong (sgn tc) (sgnAt-off d td w cd)) (proj₂ (one4 (w ! c) oc)))))
  ud : u ! d ≡ o4 zd
  ud = trans (sgnAt-off a ta _ (sym≢ ad)) (trans (sgnAt-off b tb _ (sym≢ bd)) (trans (sgnAt-off c tc _ (sym≢ cd))
         (trans (sgnAt-at d td w) (proj₂ (one4 (w ! d) od)))))
  W′ = quadW u a b c d za zb zc zd
  syl≡ : sylData p (suc k′) w ≡ quadSyl a b c d a<b b<c c<d w
  syl≡ = sylData-quad {p = p} k′ w fo na nb nc a<b b<c c<d
  a≤p = ℕP.<⇒≤ (FinP.<-trans a<b (FinP.<-trans b<c (ℕP.<-≤-trans c<d d≤p)))
  b≤p = ℕP.<⇒≤ (FinP.<-trans b<c (ℕP.<-≤-trans c<d d≤p))
  c≤p = ℕP.<⇒≤ (ℕP.<-≤-trans c<d d≤p)
  within : Within p (sylData p (suc k′) w)
  within = subst (Within p) (sym syl≡)
    (d≤p , Within-Mτ ta a≤p , Within-Mτ tb b≤p , Within-Mτ tc c≤p , Within-Mτ td d≤p)
  K′ = suc k′
  act : actVʷ (sylData p (suc k′) w) (scV (suc k′) w) ≡ scV (suc k′) W′
  act = subst (λ S → actVʷ S (scV K′ w) ≡ scV K′ W′) (sym syl≡) (begin
    actV (K-gen a b c d a<b b<c c<d) (actVʷ (Mτ a ta) (actVʷ (Mτ b tb) (actVʷ (Mτ c tc) (actVʷ (Mτ d td) (scV K′ w)))))
      ≡⟨ cong-actVʷ (K a b c d a<b b<c c<d • Mτ a ta • Mτ b tb • Mτ c tc) _ _ (Mτ-action d td K′ w) ⟩
    actV (K-gen a b c d a<b b<c c<d) (actVʷ (Mτ a ta) (actVʷ (Mτ b tb) (actVʷ (Mτ c tc) (scV K′ (sgnAt d td w)))))
      ≡⟨ cong-actVʷ (K a b c d a<b b<c c<d • Mτ a ta • Mτ b tb) _ _ (Mτ-action c tc K′ _) ⟩
    actV (K-gen a b c d a<b b<c c<d) (actVʷ (Mτ a ta) (actVʷ (Mτ b tb) (scV K′ (sgnAt c tc (sgnAt d td w)))))
      ≡⟨ cong-actVʷ (K a b c d a<b b<c c<d • Mτ a ta) _ _ (Mτ-action b tb K′ _) ⟩
    actV (K-gen a b c d a<b b<c c<d) (actVʷ (Mτ a ta) (scV K′ (sgnAt b tb (sgnAt c tc (sgnAt d td w)))))
      ≡⟨ cong-actVʷ (K a b c d a<b b<c c<d) _ _ (Mτ-action a ta K′ _) ⟩
    actV (K-gen a b c d a<b b<c c<d) (scV K′ u)
      ≡⟨ K-quad K′ u a b c d a<b b<c c<d za zb zc zd ua ub uc ud ⟩
    scV K′ W′ ∎)
  even-at : ∀ y → Even (+ 2 ℤ.* y)
  even-at = even-2*
  cnt : nodd w ≡ 4 ℕ.+ nodd W′
  cnt = count-drop₄ (λ x → oddℤ (w ! x)) (λ x → oddℤ (W′ ! x)) D₄ oa ob oc od
    (trans (cong oddℤ (set₄-a D₄ _ _ _ _ u)) (even-at (+ 1 ℤ.+ za ℤ.+ zb ℤ.+ zc ℤ.+ zd)))
    (trans (cong oddℤ (set₄-b D₄ _ _ _ _ u)) (even-at (za ℤ.- zb ℤ.+ zc ℤ.- zd)))
    (trans (cong oddℤ (set₄-c D₄ _ _ _ _ u)) (even-at (za ℤ.+ zb ℤ.- zc ℤ.- zd)))
    (trans (cong oddℤ (set₄-d D₄ _ _ _ _ u)) (even-at (za ℤ.- zb ℤ.- zc ℤ.+ zd)))
    (λ x xa xb xc xd → sym (cong oddℤ (trans (set₄-≢ D₄ _ _ _ _ u xa xb xc xd)
       (trans (sgnAt-off a ta _ xa) (trans (sgnAt-off b tb _ xb) (trans (sgnAt-off c tc _ xc) (sgnAt-off d td w xd)))))))

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

quad-step : ∀ {p : Fin n} k′ (w : Vec ℤ n) → Minimal (suc k′) w →
            Σℕ (λ x → sq (w ! x)) ≡ 4 ℕ.^ suc k′ →
            (∀ {x} → Odd (w ! x) → x ≤ p) → Goal p k′ w
quad-step k′ w (inj₁ ()) norm ≤p
quad-step {n} {p} k′ w (inj₂ (x , ox)) norm ≤p = withA (firstOdd w) refl
  where
  m4 = nodd-mod4 k′ w norm
  P : Fin n → Bool
  P y = oddℤ (w ! y)
  withA : (r : Maybe (Fin n)) → firstOdd w ≡ r → Goal p k′ w
  withA nothing fo = ⊥-elim (Odd⇒¬Even {w ! x} ox (firstOdd-nothing w fo x))
  withA (just a) fo = withB (nextOdd a w) refl
    where
    oa = proj₁ (firstOdd-spec w fo)
    withB : (r : Maybe (Fin n)) → nextOdd a w ≡ r → Goal p k′ w
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
      withC : (r : Maybe (Fin n)) → nextOdd b w ≡ r → Goal p k′ w
      withC nothing nb = ⊥-elim (2%4 (trans (cong (_% 4) (sym two)) m4))
        where
        two : count P ≡ 2
        two = count-two P a b (<⇒≢ ab) oa ob (inside₂ w fo na nb)
      withC (just c) nb = withD (nextOdd c w) refl
        where
        bc = proj₁ (nextOdd-spec w nb)
        oc = proj₁ (proj₂ (nextOdd-spec w nb))
        withD : (r : Maybe (Fin n)) → nextOdd c w ≡ r → Goal p k′ w
        withD nothing nc = ⊥-elim (3%4 (trans (cong (_% 4) (sym three)) m4))
          where
          three : count P ≡ 3
          three = count-three P a b c (<⇒≢ ab) (<⇒≢ (FinP.<-trans ab bc)) (<⇒≢ bc) oa ob oc (inside₃ w fo na nb nc)
        withD (just d) nc = quad-core k′ w fo na nb nc (≤p (proj₁ (proj₂ (nextOdd-spec w nc))))

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

------------------------------------------------------------------------
-- Presentations of groups
--
-- Correctness of Algorithm 1 (Theorem 4.10): for an orthogonal matrix
-- M ≠ I, one output of the algorithm lowers the level.
--
-- * If the pivot column v has k = lde v = 0, it is ±e_m (Norm.lde0),
--   and the syllable Z_[p] or X_[m,p] Z_[m]^τ turns it into e_p, so
--   the pivot drops.
-- * If k > 0, the entries i₁ and i₂ of √2ᵏ v are odd and congruent
--   modulo 2, so H_[0,i₂] (after X_[0,i₁], which brings entry i₁ to
--   0) makes both even: the number of odd entries drops by two, or the
--   exponent drops.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.Step where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; _xor_ ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (+_ ; -[1+_])
import Data.Integer.Solver as ℤSolver
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; dec-true)

open import Quantum.Synthesis.Matrix using (Matrix)
open import Quantum.Synthesis.Ring using (RootTwo)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Scale
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Search
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Norm
  using (NA ; NB ; Σℕ ; Σℤ ; 2ᶻ ; evenodd ; lde0 ; unit-norm ; unit-normB)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable

private
  variable
    n : ℕ
  module ℤS = ℤSolver.+-*-Solver

------------------------------------------------------------------------
-- The numerator of the pivot column
--
-- Beyond the pivot, the columns are those of the identity, so by
-- orthogonality the pivot column vanishes there; being a unit vector,
-- its numerator has Σ Aₓ = 2ᵏ and Σ Bₓ = 0.

pivot-zero> : {M : Matrix n n D} → ColOrth M → ∀ {p} → pivot M ≡ just p →
              ∀ x → p < x → num (col M p) ! x ≡ ZR.0#
pivot-zero> {M = M} o {p} pv x p<x = sc-injective (lde (col M p)) (begin
  sc (lde (col M p)) (num (col M p) ! x)          ≡⟨ sym (scV-! (lde (col M p)) (num (col M p)) x) ⟩
  scV (lde (col M p)) (num (col M p)) ! x         ≡⟨ cong (_! x) (sym (lde-eq (col M p))) ⟩
  col M p ! x                                     ≡⟨ col-vanish o (proj₂ (pivot-just M pv) x p<x) (λ { refl → ℕP.<-irrefl refl p<x }) ⟩
  DR.0#                                           ≡⟨ sym (sc-0 (lde (col M p))) ⟩
  sc (lde (col M p)) ZR.0#                        ∎)
  where open ≡-Reasoning

col-norm : {M : Matrix n n D} → ColOrth M → (p : Fin n) →
           Σℕ (λ x → NA (num (col M p) ! x)) ≡ 2 ℕ.^ lde (col M p)
col-norm {M = M} o p =
  unit-norm (lde (col M p)) (num (col M p))
    (subst (λ u → ⟨ u , u ⟩ ≡ DR.1#) (lde-eq (col M p)) (col-unit o p))

col-normB : {M : Matrix n n D} → ColOrth M → (p : Fin n) →
            Σℤ (λ x → NB (num (col M p) ! x)) ≡ + 0
col-normB {M = M} o p =
  unit-normB (lde (col M p)) (num (col M p))
    (subst (λ u → ⟨ u , u ⟩ ≡ DR.1#) (lde-eq (col M p)) (col-unit o p))

-- The odd entries are at indices ≤ p.
odd⇒≤ : {p : Fin n} {w : Vec Z n} → (∀ x → p < x → w ! x ≡ ZR.0#) → ∀ {x} → Odd (w ! x) → x ≤ p
odd⇒≤ {p = p} {w} zero> {x} ox = tri-elim (FinP.<-cmp p x)
  (λ p<x → ⊥-elim (Odd⇒¬Even {w ! x} ox (cong oddᶻ (zero> x p<x))))
  (λ { refl → FinP.≤-refl })
  (λ x<p → ℕP.<⇒≤ x<p)

------------------------------------------------------------------------
-- Scaling a numerator by √2

scV-δmap : ∀ k (W : Vec Z n) → scV (suc k) (Vec.map (√2ᶻ ZR.*_) W) ≡ scV k W
scV-δmap k W = vec-ext λ x → begin
  scV (suc k) (Vec.map (√2ᶻ ZR.*_) W) ! x    ≡⟨ scV-! (suc k) (Vec.map (√2ᶻ ZR.*_) W) x ⟩
  sc (suc k) (Vec.map (√2ᶻ ZR.*_) W ! x)     ≡⟨ cong (sc (suc k)) (VecP.lookup-map x (√2ᶻ ZR.*_) W) ⟩
  sc (suc k) (√2ᶻ ZR.* (W ! x))              ≡⟨ sc-δ k (W ! x) ⟩
  sc k (W ! x)                               ≡⟨ sym (scV-! k W x) ⟩
  scV k W ! x                                ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- k = 0: the syllable restores e_p

private
  -- A vector that is 1 at m and 0 elsewhere is e_m.
  set₁-e : (m : Fin n) (w : Vec Z n) → (∀ y → y ≢ m → w ! y ≡ ZR.0#) → set₁ m ZR.1# w ≡ eᶻ m
  set₁-e m w rest = vec-ext λ x → dec-elim (x FinP.≟ m)
    (λ { refl → trans (set₁-a x ZR.1# w) (sym (trans (eᶻ-! x x) (eδ-refl x))) })
    (λ x≢m → trans (set₁-≢ m ZR.1# w x≢m) (trans (rest x x≢m) (sym (trans (eᶻ-! m x) (eδ-≢ x≢m)))))

  -- Swapping it to p gives e_p.
  Xᶻ-e : (m p : Fin n) → m ≢ p → (w : Vec Z n) → (∀ y → y ≢ m → w ! y ≡ ZR.0#) →
         Xᶻ m p (set₁ m ZR.1# w) ≡ eᶻ p
  Xᶻ-e m p m≢p w rest = vec-ext λ x → dec-elim (x FinP.≟ m)
    (λ { refl → begin
          Xᶻ x p u ! x         ≡⟨ set₂-a x p (u ! p) (u ! x) u ⟩
          u ! p                ≡⟨ set₁-≢ x ZR.1# w (m≢p ∘ sym) ⟩
          w ! p                ≡⟨ rest p (m≢p ∘ sym) ⟩
          ZR.0#                ≡⟨ sym (trans (eᶻ-! p x) (eδ-≢ m≢p)) ⟩
          eᶻ p ! x             ∎ })
    (λ x≢m → dec-elim (x FinP.≟ p)
      (λ { refl → begin
            Xᶻ m x u ! x       ≡⟨ set₂-b m x (u ! x) (u ! m) u m≢p ⟩
            u ! m              ≡⟨ set₁-a m ZR.1# w ⟩
            ZR.1#              ≡⟨ sym (trans (eᶻ-! x x) (eδ-refl x)) ⟩
            eᶻ x ! x           ∎ })
      (λ x≢p → begin
            Xᶻ m p u ! x       ≡⟨ set₂-≢ m p (u ! p) (u ! m) u x≢m x≢p ⟩
            u ! x              ≡⟨ set₁-≢ m ZR.1# w x≢m ⟩
            w ! x              ≡⟨ rest x x≢m ⟩
            ZR.0#              ≡⟨ sym (trans (eᶻ-! p x) (eδ-≢ x≢p)) ⟩
            eᶻ p ! x           ∎))
    where
    open ≡-Reasoning
    u = set₁ m ZR.1# w

  -- Z_[m]^τ makes the unit at m positive.
  Zfix : (w : Vec Z n) (m : Fin n) → (w ! m ≡ ZR.1# ⊎ w ! m ≡ ZR.- ZR.1#) →
         (if negᶻ (w ! m) then Zᶻ m w else w) ≡ set₁ m ZR.1# w
  Zfix w m (inj₁ e) = trans (cong (λ z → if negᶻ z then Zᶻ m w else w) e)
                            (trans (sym (set₁-self m w)) (cong (λ z → set₁ m z w) e))
  Zfix w m (inj₂ e) = trans (cong (λ z → if negᶻ z then Zᶻ m w else w) e) (cong (λ z → set₁ m (ZR.- z) w) e)

  unit≢0 : ∀ {u} → (u ≡ ZR.1# ⊎ u ≡ ZR.- ZR.1#) → u ≢ ZR.0#
  unit≢0 (inj₁ refl) ()
  unit≢0 (inj₂ refl) ()

  unit-odd : ∀ {u} → (u ≡ ZR.1# ⊎ u ≡ ZR.- ZR.1#) → Odd u
  unit-odd (inj₁ refl) = refl
  unit-odd (inj₂ refl) = refl

  Within-Zτ : ∀ {p a : Fin n} τ → a ≤ p → Within p (Zτ a τ)
  Within-Zτ true  a≤p = a≤p
  Within-Zτ false a≤p = tt

  cong-actVʷ : (u : Word (Gen n)) (x y : Vec D n) → x ≡ y → actVʷ u x ≡ actVʷ u y
  cong-actVʷ u x y refl = refl

unit-step : ∀ {p : Fin n} (w : Vec Z n) → Σℕ (λ x → NA (w ! x)) ≡ 1 → (∀ x → p < x → w ! x ≡ ZR.0#) →
            Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
unit-step {n} {p} w norm zero> = go (lde0 w norm)
  where
  open ≡-Reasoning
  go : (∃ λ m → (w ! m ≡ ZR.1# ⊎ w ! m ≡ ZR.- ZR.1#) × (∀ y → y ≢ m → w ! y ≡ ZR.0#)) →
       Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
  go (m , um , rest) =
    tri-elim (FinP.<-cmp m p) case< case≡ (λ p<m → ⊥-elim (unit≢0 um (zero> m p<m)))
    where
    fo : firstOdd w ≡ just m
    fo = firstOdd-char w (unit-odd um) (λ x x<m → cong oddᶻ (rest x (λ { refl → ℕP.<-irrefl refl x<m })))
    τ = negᶻ (w ! m)
    u = if τ then Zᶻ m w else w
    u≡ : u ≡ set₁ m ZR.1# w
    u≡ = Zfix w m um
    case< : m < p → Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
    case< m<p = subst (λ W → Within p W × actVʷ W (scV 0 w) ≡ scV 0 (eᶻ p)) (sym (sylData-unit< w fo m<p))
      ( (FinP.≤-refl , Within-Zτ τ (ℕP.<⇒≤ m<p))
      , (begin
          actV (X-gen m p m<p) (actVʷ (Zτ m τ) (scV 0 w))
            ≡⟨ cong-actVʷ (X m p m<p) _ _ (Zτ-action m τ 0 w) ⟩
          actV (X-gen m p m<p) (scV 0 u)
            ≡⟨ actV-X m p m<p 0 u ⟩
          scV 0 (Xᶻ m p u)
            ≡⟨ cong (scV 0) (trans (cong (Xᶻ m p) u≡) (Xᶻ-e m p (<⇒≢ m<p) w rest)) ⟩
          scV 0 (eᶻ p) ∎))
    case≡ : m ≡ p → Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
    case≡ refl = subst (λ W → Within p W × actVʷ W (scV 0 w) ≡ scV 0 (eᶻ p)) (sym (sylData-unit≡ w fo))
      ( Within-Zτ τ FinP.≤-refl
      , (begin
          actVʷ (Zτ m τ) (scV 0 w)        ≡⟨ Zτ-action m τ 0 w ⟩
          scV 0 u                         ≡⟨ cong (scV 0) (trans u≡ (set₁-e m w rest)) ⟩
          scV 0 (eᶻ m) ∎))

------------------------------------------------------------------------
-- k > 0: H on two odd entries in the same class makes them even

-- Two odd entries in the same residue class are congruent modulo 2.
same-class : ∀ x y → Odd x → Odd y → rbit x ≡ rbit y → ∃ λ z → x ≡ y ZR.+ 2ᶻ ZR.* z
same-class (RootTwo a b) (RootTwo c d) oa oc rb
  with evenℤ-half (a ℤ.- c) (trans (oddℤ-+ a (ℤ.- c)) (cong₂ _xor_ oa (trans (oddℤ-neg c) oc)))
     | evenℤ-half (b ℤ.- d) (trans (oddℤ-+ b (ℤ.- d)) (trans (cong (oddℤ b xor_) (oddℤ-neg d)) (xor-self rb)))
  where
  xor-self : ∀ {p q} → p ≡ q → p xor q ≡ false
  xor-self {true} refl = refl
  xor-self {false} refl = refl
... | s , es | t , et = RootTwo s t , cong₂ RootTwo ea eb
  where
  open ℤS using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)
  ea : a ≡ c ℤ.+ (+ 2 ℤ.* s ℤ.+ (+ 0 ℤ.* t ℤ.+ + 0 ℤ.* t))
  ea = begin
    a                                   ≡⟨ ℤS.solve 2 (λ a c → a := c :+ (a :- c)) refl a c ⟩
    c ℤ.+ (a ℤ.- c)                     ≡⟨ cong (λ u → c ℤ.+ u) es ⟩
    c ℤ.+ (s ℤ.+ s)                     ≡⟨ ℤS.solve 3 (λ c s t → c :+ (s :+ s)
                                             := c :+ (con (+ 2) :* s :+ (con (+ 0) :* t :+ con (+ 0) :* t))) refl c s t ⟩
    c ℤ.+ (+ 2 ℤ.* s ℤ.+ (+ 0 ℤ.* t ℤ.+ + 0 ℤ.* t)) ∎
    where open ≡-Reasoning
  eb : b ≡ d ℤ.+ (+ 2 ℤ.* t ℤ.+ s ℤ.* + 0)
  eb = begin
    b                                   ≡⟨ ℤS.solve 2 (λ b d → b := d :+ (b :- d)) refl b d ⟩
    d ℤ.+ (b ℤ.- d)                     ≡⟨ cong (λ u → d ℤ.+ u) et ⟩
    d ℤ.+ (t ℤ.+ t)                     ≡⟨ ℤS.solve 3 (λ d s t → d :+ (t :+ t) := d :+ (con (+ 2) :* t :+ s :* con (+ 0))) refl d s t ⟩
    d ℤ.+ (+ 2 ℤ.* t ℤ.+ s ℤ.* + 0)     ∎
    where open ≡-Reasoning

private
  open ZG using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

  -- With x = y + 2z:  x + y = √2 (√2 (y + z))  and  x − y = √2 (√2 z).
  idJ : ∀ x y z → x ≡ y ZR.+ 2ᶻ ZR.* z → x ZR.+ y ≡ √2ᶻ ZR.* (√2ᶻ ZR.* (y ZR.+ z))
  idJ x y z refl =
    ZG.solve 2 (λ y z → (y :+ con 2ᶻ :* z) :+ y := con √2ᶻ :* (con √2ᶻ :* (y :+ z))) refl y z
  idL : ∀ x y z → x ≡ y ZR.+ 2ᶻ ZR.* z → x ZR.- y ≡ √2ᶻ ZR.* (√2ᶻ ZR.* z)
  idL x y z refl =
    ZG.solve 2 (λ y z → (y :+ con 2ᶻ :* z) :- y := con √2ᶻ :* (con √2ᶻ :* z)) refl y z

  -- Multiples of √2 are even.
  even√2 : ∀ y → Even (√2ᶻ ZR.* y)
  even√2 y = δ∣⇒even (y , refl)

-- The numerator after H_[j,ℓ] on entries x_j = x_ℓ + 2z, back at the
-- same scale: entries j and ℓ become √2 (x_ℓ + z) and √2 z.
pairW : (w : Vec Z n) (j ℓ : Fin n) (z : Z) → Vec Z n
pairW w j ℓ z = set₂ j ℓ (√2ᶻ ZR.* (w ! ℓ ZR.+ z)) (√2ᶻ ZR.* z) w

H-pair : ∀ (j ℓ : Fin n) → j ≢ ℓ → (w : Vec Z n) (z : Z) → w ! j ≡ w ! ℓ ZR.+ 2ᶻ ZR.* z →
         Hᶻ j ℓ w ≡ Vec.map (√2ᶻ ZR.*_) (pairW w j ℓ z)
H-pair j ℓ j≢ℓ w z eq = vec-ext λ x → dec-elim (x FinP.≟ j)
  (λ { refl → begin
      Hᶻ x ℓ w ! x                                ≡⟨ set₂-a x ℓ (w ! x ZR.+ w ! ℓ) (w ! x ZR.- w ! ℓ) δw ⟩
      w ! x ZR.+ w ! ℓ                            ≡⟨ idJ (w ! x) (w ! ℓ) z eq ⟩
      √2ᶻ ZR.* Jv                                 ≡⟨ cong (√2ᶻ ZR.*_) (sym (set₂-a x ℓ Jv Lv w)) ⟩
      √2ᶻ ZR.* (W′ ! x)                           ≡⟨ sym (VecP.lookup-map x (√2ᶻ ZR.*_) W′) ⟩
      Vec.map (√2ᶻ ZR.*_) W′ ! x                  ∎ })
  (λ x≢j → dec-elim (x FinP.≟ ℓ)
    (λ { refl → begin
        Hᶻ j x w ! x                              ≡⟨ set₂-b j x (w ! j ZR.+ w ! x) (w ! j ZR.- w ! x) δw j≢ℓ ⟩
        w ! j ZR.- w ! x                          ≡⟨ idL (w ! j) (w ! x) z eq ⟩
        √2ᶻ ZR.* Lv                               ≡⟨ cong (√2ᶻ ZR.*_) (sym (set₂-b j x Jv Lv w j≢ℓ)) ⟩
        √2ᶻ ZR.* (W′ ! x)                         ≡⟨ sym (VecP.lookup-map x (√2ᶻ ZR.*_) W′) ⟩
        Vec.map (√2ᶻ ZR.*_) W′ ! x                ∎ })
    (λ x≢ℓ → begin
        Hᶻ j ℓ w ! x                              ≡⟨ set₂-≢ j ℓ (w ! j ZR.+ w ! ℓ) (w ! j ZR.- w ! ℓ) δw x≢j x≢ℓ ⟩
        δw ! x                                    ≡⟨ VecP.lookup-map x (√2ᶻ ZR.*_) w ⟩
        √2ᶻ ZR.* (w ! x)                          ≡⟨ cong (√2ᶻ ZR.*_) (sym (set₂-≢ j ℓ Jv Lv w x≢j x≢ℓ)) ⟩
        √2ᶻ ZR.* (W′ ! x)                         ≡⟨ sym (VecP.lookup-map x (√2ᶻ ZR.*_) W′) ⟩
        Vec.map (√2ᶻ ZR.*_) W′ ! x                ∎))
  where
  open ≡-Reasoning
  δw = Vec.map (√2ᶻ ZR.*_) w
  Jv = √2ᶻ ZR.* (w ! ℓ ZR.+ z)
  Lv = √2ᶻ ZR.* z
  W′ = pairW w j ℓ z

-- H_[j,ℓ] on a scaled column, for such entries.
H-action : ∀ k (w : Vec Z n) (j ℓ : Fin n) .(j<ℓ : j < ℓ) (z : Z) → w ! j ≡ w ! ℓ ZR.+ 2ᶻ ZR.* z →
           actV (H-gen j ℓ j<ℓ) (scV k w) ≡ scV k (pairW w j ℓ z)
H-action k w j ℓ j<ℓ z eq =
  trans (actV-H j ℓ j<ℓ k w)
        (trans (cong (scV (suc k)) (H-pair j ℓ (<⇒≢ j<ℓ) w z eq)) (scV-δmap k (pairW w j ℓ z)))

pairW-j : ∀ (w : Vec Z n) j ℓ z → Even (pairW w j ℓ z ! j)
pairW-j w j ℓ z = trans (cong oddᶻ (set₂-a j ℓ _ _ w)) (even√2 (w ! ℓ ZR.+ z))

pairW-ℓ : ∀ (w : Vec Z n) j ℓ z → j ≢ ℓ → Even (pairW w j ℓ z ! ℓ)
pairW-ℓ w j ℓ z j≢ℓ = trans (cong oddᶻ (set₂-b j ℓ _ _ w j≢ℓ)) (even√2 z)

pairW-≢ : ∀ (w : Vec Z n) j ℓ z x → x ≢ j → x ≢ ℓ → pairW w j ℓ z ! x ≡ w ! x
pairW-≢ w j ℓ z x x≢j x≢ℓ = set₂-≢ j ℓ _ _ w x≢j x≢ℓ

------------------------------------------------------------------------
-- The pair syllable

private
  Goal : Fin n → ℕ → Vec Z n → Set
  Goal p k w = ∃ λ W′ → Within p (sylData p (suc k) w)
                      × actVʷ (sylData p (suc k) w) (scV (suc k) w) ≡ scV (suc k) W′
                      × nodd w ≡ suc (suc (nodd W′))

  actVʷ-• : (u v : Word (Gen n)) (x : Vec D n) → actVʷ (u • v) x ≡ actVʷ u (actVʷ v x)
  actVʷ-• u v x = refl

-- The syllable, given i₁ (the first odd entry) and i₂ (the next one in
-- its class).
pair-core : ∀ {p : Fin n} k′ (w : Vec Z n) {i₁ i₂ : Fin n} →
            firstOdd w ≡ just i₁ → nextSame i₁ w ≡ just i₂ → i₂ ≤ p → Goal p k′ w
pair-core {n} {p} k′ w {i₁} {i₂} fo nx i₂≤p = by-i₁ i₁ refl fo nx
  where
  i₁<i₂ = proj₁ (nextSame-spec w nx)
  o₁ = proj₁ (firstOdd-spec w fo)
  sm = proj₁ (proj₂ (nextSame-spec w nx))
  zc = same-class (w ! i₁) (w ! i₂) o₁ (proj₁ sm) (sym (proj₂ sm))
  open ≡-Reasoning
  by-i₁ : ∀ j → j ≡ i₁ → firstOdd w ≡ just j → nextSame j w ≡ just i₂ → Goal p k′ w
  by-i₁ zero refl fo′ nx′ = W′ , within , act , cnt
    where
    lt = proj₁ (nextSame-spec w nx′)
    z = proj₁ zc
    W′ = pairW w zero i₂ z
    syl≡ : sylData p (suc k′) w ≡ H zero i₂ lt
    syl≡ = sylData-pair {p = p} k′ w fo′ nx′ lt
    within : Within p (sylData p (suc k′) w)
    within = subst (Within p) (sym syl≡) i₂≤p
    act : actVʷ (sylData p (suc k′) w) (scV (suc k′) w) ≡ scV (suc k′) W′
    act = subst (λ S → actVʷ S (scV (suc k′) w) ≡ scV (suc k′) W′) (sym syl≡)
                (H-action (suc k′) w zero i₂ lt z (proj₂ zc))
    cnt : nodd w ≡ suc (suc (nodd W′))
    cnt = count-drop₂ (λ x → oddᶻ (w ! x)) (λ x → oddᶻ (W′ ! x)) zero i₂ (<⇒≢ lt) o₁ (proj₁ sm)
            (pairW-j w zero i₂ z) (pairW-ℓ w zero i₂ z (<⇒≢ lt))
            (λ x x≢0 x≢i₂ → sym (cong oddᶻ (pairW-≢ w zero i₂ z x x≢0 x≢i₂)))
  by-i₁ (suc j) refl fo′ nx′ = W′ , within , act , cnt
    where
    lt = proj₁ (nextSame-spec w nx′)
    0<i₁ : 0 ℕ.< toℕ (suc j)
    0<i₁ = ℕ.s≤s ℕ.z≤n
    0<i₂ : 0 ℕ.< toℕ i₂
    0<i₂ = ℕP.<-trans 0<i₁ lt
    i₂≢0 : i₂ ≢ zero
    i₂≢0 e = <⇒≢ 0<i₂ (sym e)
    i₂≢i₁ : i₂ ≢ suc j
    i₂≢i₁ e = <⇒≢ lt (sym e)
    z = proj₁ zc
    w₁ = Xᶻ zero (suc j) w
    w₁0 : w₁ ! zero ≡ w ! suc j
    w₁0 = set₂-a zero (suc j) (w ! suc j) (w ! zero) w
    w₁i₂ : w₁ ! i₂ ≡ w ! i₂
    w₁i₂ = set₂-≢ zero (suc j) (w ! suc j) (w ! zero) w i₂≢0 i₂≢i₁
    eq₁ : w₁ ! zero ≡ w₁ ! i₂ ZR.+ 2ᶻ ZR.* z
    eq₁ = trans w₁0 (trans (proj₂ zc) (cong (ZR._+ 2ᶻ ZR.* z) (sym w₁i₂)))
    W′ = pairW w₁ zero i₂ z
    syl≡ : sylData p (suc k′) w ≡ H zero i₂ 0<i₂ • X zero (suc j) 0<i₁
    syl≡ = sylData-pair {p = p} k′ w fo′ nx′ lt
    within : Within p (sylData p (suc k′) w)
    within = subst (Within p) (sym syl≡) (i₂≤p , ℕP.<⇒≤ (ℕP.<-≤-trans lt i₂≤p))
    act : actVʷ (sylData p (suc k′) w) (scV (suc k′) w) ≡ scV (suc k′) W′
    act = subst (λ S → actVʷ S (scV (suc k′) w) ≡ scV (suc k′) W′) (sym syl≡) (begin
      actV (H-gen zero i₂ 0<i₂) (actV (X-gen zero (suc j) 0<i₁) (scV (suc k′) w))
        ≡⟨ cong-actVʷ (H zero i₂ 0<i₂) _ _ (actV-X zero (suc j) 0<i₁ (suc k′) w) ⟩
      actV (H-gen zero i₂ 0<i₂) (scV (suc k′) w₁)
        ≡⟨ H-action (suc k′) w₁ zero i₂ 0<i₂ z eq₁ ⟩
      scV (suc k′) W′ ∎)
    -- Entry 0 of w is even (i₁ is the first odd entry).
    e0 : Even (w ! zero)
    e0 = proj₂ (firstOdd-spec w fo′) zero 0<i₁
    cnt : nodd w ≡ suc (suc (nodd W′))
    cnt = count-drop₂ (λ x → oddᶻ (w ! x)) (λ x → oddᶻ (W′ ! x)) (suc j) i₂ (i₂≢i₁ ∘ sym) o₁ (proj₁ sm)
            (trans (cong oddᶻ (trans (pairW-≢ w₁ zero i₂ z (suc j) (λ ()) (i₂≢i₁ ∘ sym))
                                     (set₂-b zero (suc j) (w ! suc j) (w ! zero) w (λ ())))) e0)
            (pairW-ℓ w₁ zero i₂ z (i₂≢0 ∘ sym))
            agree
      where
      agree : ∀ x → x ≢ suc j → x ≢ i₂ → oddᶻ (w ! x) ≡ oddᶻ (W′ ! x)
      agree zero _ _ = trans e0 (sym (pairW-j w₁ zero i₂ z))
      agree (suc x) x≢i₁ x≢i₂ =
        sym (cong oddᶻ (trans (pairW-≢ w₁ zero i₂ z (suc x) (λ ()) x≢i₂)
                              (set₂-≢ zero (suc j) (w ! suc j) (w ! zero) w (λ ()) x≢i₁)))

------------------------------------------------------------------------
-- k > 0: i₁ and i₂ exist

pair-step : ∀ {p : Fin n} k′ (w : Vec Z n) → Minimal (suc k′) w →
            Σℕ (λ x → NA (w ! x)) ≡ 2 ℕ.^ suc k′ → Σℤ (λ x → NB (w ! x)) ≡ + 0 →
            (∀ {x} → Odd (w ! x) → x ≤ p) → Goal p k′ w
pair-step k′ w (inj₁ ()) norm normB ≤p
pair-step {n} {p} k′ w (inj₂ (x , ox)) norm normB ≤p = withFirst (firstOdd w) refl
  where
  withFirst : (r : Maybe (Fin n)) → firstOdd w ≡ r → Goal p k′ w
  withFirst nothing fo = ⊥-elim (Odd⇒¬Even {w ! x} ox (firstOdd-nothing w fo x))
  withFirst (just j) fo = withNext (nextSame j w) refl
    where
    oj : Odd (w ! j)
    oj = proj₁ (firstOdd-spec w fo)
    withNext : (r : Maybe (Fin n)) → nextSame j w ≡ r → Goal p k′ w
    withNext (just ℓ) nx = pair-core k′ w fo nx (≤p (proj₁ (proj₁ (proj₂ (nextSame-spec w nx)))))
    -- Otherwise j is the only odd entry in its class, but every class
    -- has an even size.
    withNext nothing nx = ⊥-elim (by-class (rbit (w ! j)) refl)
      where
      true≢false : true ≢ false
      true≢false ()
      -- No other entry is odd in the class of j.
      others : ∀ y → y ≢ j → Odd (w ! y) → rbit (w ! y) ≢ rbit (w ! j)
      others y y≢j oy rb = tri-elim (FinP.<-cmp y j)
        (λ y<j → Odd⇒¬Even {w ! y} oy (proj₂ (firstOdd-spec w fo) y y<j))
        (λ y≡j → y≢j y≡j)
        (λ j<y → nextSame-nothing w nx y j<y (oy , rb))
      -- Class 1 + √2: j is the only entry odd with rbit.
      by-class : ∀ b → rbit (w ! j) ≡ b → _
      by-class true rb = true≢false (trans (sym (cong oddℕ one)) (evenclass′))
        where
        P : Fin n → Bool
        P y = oddᶻ (w ! y) ∧ rbit (w ! y)
        Pj : P j ≡ true
        Pj = trans (cong₂ _∧_ oj rb) refl
        noP : ∀ y → y ≢ j → P y ≡ false
        noP y y≢j with oddᶻ (w ! y) in oy | rbit (w ! y) in ry
        ... | false | _ = refl
        ... | true | false = refl
        ... | true | true = ⊥-elim (others y y≢j oy (trans ry (sym rb)))
        one : count P ≡ 1
        one = count-one P j Pj noP
        evenclass′ : oddℕ (count P) ≡ false
        evenclass′ = Norm-evenclass
          where open import Examples.Groups.Real-Clifford+CH-TwoLevel.Norm using () renaming (evenclass to ec)
                Norm-evenclass = ec w normB
      -- Class 1: the odd entries other than j are all in class 1 + √2,
      -- an even number of them, so the total is odd.
      by-class false rb = true≢false (trans (sym oddsum) (evenodd k′ w norm))
        where
        P Q : Fin n → Bool
        P y = oddᶻ (w ! y)
        Q y = oddᶻ (w ! y) ∧ rbit (w ! y)
        open import Examples.Groups.Real-Clifford+CH-TwoLevel.Norm using (evenclass)
        -- count P = 1 + count Q, as j is the only odd entry outside Q.
        PQ : count P ≡ suc (count Q)
        PQ = count-drop P Q j oj (trans (cong (oddᶻ (w ! j) ∧_) rb) (∧-false (oddᶻ (w ! j)))) agree
          where
          ∧-false : ∀ b → b ∧ false ≡ false
          ∧-false true = refl
          ∧-false false = refl
          agree : ∀ y → y ≢ j → P y ≡ Q y
          agree y y≢j with oddᶻ (w ! y) in oy | rbit (w ! y) in ry
          ... | false | _ = refl
          ... | true | true = refl
          ... | true | false = ⊥-elim (others y y≢j oy (trans ry (sym rb)))
        oddsum : oddℕ (count P) ≡ true
        oddsum = trans (cong oddℕ PQ) (cong Data.Bool.Base.not (evenclass w normB))
          where import Data.Bool.Base

------------------------------------------------------------------------
-- One step lowers the level (Theorem 4.10)

-- Numerators at one scale are determined by the vector.
scV-injective : ∀ k (u v : Vec Z n) → scV k u ≡ scV k v → u ≡ v
scV-injective k u v eq = vec-ext λ x →
  sc-injective k (trans (sym (scV-! k u x)) (trans (cong (_! x) eq) (scV-! k v x)))

private
  -- The column p after the syllable S.
  col-step : (M : Matrix n n D) (p : Fin n) (S : Word (Gen n)) (K : ℕ) (W : Vec Z n) →
             col M p ≡ scV K W → col (actMʷ S M) p ≡ actVʷ S (scV K W)
  col-step M p S K W eq = trans (col-actMʷ S M p) (cong-actVʷ S (col M p) (scV K W) eq)

-- The level drops, given the data of the pivot column.
lt-core : (M : Matrix n n D) (p : Fin n) (K : ℕ) (W : Vec Z n) →
          Beyond p M → col M p ≡ scV K W → Minimal K W → (∀ x → p < x → W ! x ≡ ZR.0#) →
          Σℕ (λ x → NA (W ! x)) ≡ 2 ℕ.^ K → Σℤ (λ x → NB (W ! x)) ≡ + 0 →
          level (actMʷ (sylData p K W) M) <ₗ (suc (toℕ p) , K , nodd W)
lt-core M p zero W be eq min zero> norm normB =
  level-below (actMʷ S M) col≡ (Beyond-actMʷ S {p} {M} (proj₁ us) be) zero (nodd W)
  where
  S = sylData p zero W
  us = unit-step W norm zero>
  col≡ : col (actMʷ S M) p ≡ col 𝕀 p
  col≡ = trans (col-step M p S zero W eq) (trans (proj₂ us) (sym (col𝕀≡ p)))
lt-core M p (suc K′) W be eq min zero> norm normB =
  go (pair-step K′ W min norm normB (odd⇒≤ {p = p} {W} zero>))
  where
  S = sylData p (suc K′) W
  go : (∃ λ W′ → Within p S × actVʷ S (scV (suc K′) W) ≡ scV (suc K′) W′ × nodd W ≡ suc (suc (nodd W′))) →
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
                                   (subst (nodd W′ ℕ.<_) (sym cnt) (ℕ.s≤s (ℕP.n≤1+n (nodd W′)))))) ]′
          (ℕP.m≤n⇒m<n∨m≡n (lde-≤ (suc K′) W′ col′))
    -- (A helper with its type written out, rather than dec-elim.)
    decide : Dec (col (actMʷ S M) p ≡ col 𝕀 p) → level (actMʷ S M) <ₗ (suc (toℕ p) , suc K′ , nodd W)
    decide (yes e) = level-below (actMʷ S M) e be′ (suc K′) (nodd W)
    decide (no ne) = level-same (actMʷ S M) ne be′ lt₂

step-lt : {M : Matrix n n D} → ColOrth M → ∀ {p} → pivot M ≡ just p → level (step M) <ₗ level M
step-lt {M = M} o {p} pv =
  subst₂ _<ₗ_ (cong (λ S → level (actMʷ S M)) (sym (syl-just M pv))) (sym (level-just M pv))
    (lt-core M p (lde v) (num v) (proj₂ (pivot-just M pv)) (lde-eq v) (lde-min v)
             (pivot-zero> o pv) (col-norm o p) (col-normB o p))
  where
  v = col M p

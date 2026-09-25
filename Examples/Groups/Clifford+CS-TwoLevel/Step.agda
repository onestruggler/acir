------------------------------------------------------------------------
-- Presentations of groups
--
-- Termination of the exact synthesis algorithm (Theorem 2.9): for a
-- column-orthonormal matrix M ≠ I, one step lowers the level.
--
-- * If the pivot column v has k = lde v = 0, it is a unit times a
--   standard basis vector e_m (Corollary 2.3), and the syllable turns
--   it into e_p, so the pivot drops.
-- * If k > 0, the syllable K†_[j,ℓ] i_[ℓ]ᑫ makes the entries j and ℓ
--   of γᵏ v even (Lemma 2.6: the row operation), so the number of odd
--   entries drops by two, or the exponent drops.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.Step where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base using (+_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does)

open import Quantum.Synthesis.Matrix using (Matrix)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
open import Examples.Groups.Clifford+CS-TwoLevel.Ring
open import Examples.Groups.Clifford+CS-TwoLevel.Scale
open import Examples.Groups.Clifford+CS-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Search
open import Examples.Groups.Clifford+CS-TwoLevel.Norm
  using (Nℕ ; Σℕ ; Unit ; evenodd ; lde0 ; unit-norm)
open import Examples.Groups.Clifford+CS-TwoLevel.Column
open import Examples.Groups.Clifford+CS-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Clifford+CS-TwoLevel.Pivot
open import Examples.Groups.Clifford+CS-TwoLevel.Syllable

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The data of a pivot column

record PivotData (M : Matrix n n D) (p : Fin n) : Set where
  field
    nonId  : col M p ≢ col 𝕀 p
    beyond : Beyond p M
    k      : ℕ
    w      : Vec Z n
    col≡   : col M p ≡ scV k w
    min    : Minimal k w
    zero>  : ∀ x → p < x → w ! x ≡ ZR.0#
    norm   : Σℕ (λ x → Nℕ (w ! x)) ≡ 2 ℕ.^ k
    k≡     : k ≡ lde (col M p)
    w≡     : w ≡ num (col M p)

pivotData : {M : Matrix n n D} → ColOrth M → ∀ {p} → pivot M ≡ just p → PivotData M p
pivotData {M = M} o {p} pv = record
  { nonId = proj₁ pj ; beyond = proj₂ pj ; k = lde v ; w = num v
  ; col≡ = lde-eq v ; min = lde-min v ; zero> = zero> ; norm = norm ; k≡ = refl ; w≡ = refl }
  where
  pj = pivot-just M pv
  v = col M p
  zero> : ∀ x → p < x → num v ! x ≡ ZR.0#
  zero> x p<x = sc-injective (lde v) (begin
    sc (lde v) (num v ! x)          ≡⟨ sym (scV-! (lde v) (num v) x) ⟩
    scV (lde v) (num v) ! x         ≡⟨ cong (_! x) (sym (lde-eq v)) ⟩
    v ! x                           ≡⟨ col-vanish o (proj₂ pj x p<x) (λ { refl → ℕP.<-irrefl refl p<x }) ⟩
    DR.0#                           ≡⟨ sym (sc-0 (lde v)) ⟩
    sc (lde v) ZR.0#                ∎)
    where open ≡-Reasoning
  norm : Σℕ (λ x → Nℕ (num v ! x)) ≡ 2 ℕ.^ lde v
  norm = unit-norm (lde v) (num v) (subst (λ u → ⟨ u , u ⟩ ≡ DR.1#) (lde-eq v) (col-unit o p))

module _ {M : Matrix n n D} {p : Fin n} (P : PivotData M p) where
  open PivotData P

  -- The nonzero, and so the odd, entries are at indices ≤ p.
  odd⇒≤ : ∀ {x} → Odd (w ! x) → x ≤ p
  odd⇒≤ {x} ox = tri-elim (FinP.<-cmp p x)
    (λ p<x → ⊥-elim (Odd⇒¬Even {w ! x} ox (cong oddᶻ (zero> x p<x))))
    (λ { refl → FinP.≤-refl })
    (λ x<p → ℕP.<⇒≤ x<p)

------------------------------------------------------------------------
-- Scaling a numerator by γ

scV-γmap : ∀ k (W : Vec Z n) → scV (suc k) (Vec.map (γᶻ ZR.*_) W) ≡ scV k W
scV-γmap k W = vec-ext λ x → begin
  scV (suc k) (Vec.map (γᶻ ZR.*_) W) ! x    ≡⟨ scV-! (suc k) (Vec.map (γᶻ ZR.*_) W) x ⟩
  sc (suc k) (Vec.map (γᶻ ZR.*_) W ! x)     ≡⟨ cong (sc (suc k)) (VecP.lookup-map x (γᶻ ZR.*_) W) ⟩
  sc (suc k) (γᶻ ZR.* (W ! x))              ≡⟨ sc-γ k (W ! x) ⟩
  sc k (W ! x)                              ≡⟨ sym (scV-! k W x) ⟩
  scV k W ! x                               ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- k = 0: the syllable restores e_p

private
  unit≢0 : ∀ t → t ℕ.< 4 → ⅈᶻ ^ᶻ t ≢ ZR.0#
  unit≢0 0 _ ()
  unit≢0 1 _ ()
  unit≢0 2 _ ()
  unit≢0 3 _ ()
  unit≢0 (suc (suc (suc (suc t)))) (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ())))) _

  -- A vector that is 1 at m and 0 elsewhere is e_m.
  set₁-e : (m : Fin n) (w : Vec Z n) → (∀ y → y ≢ m → w ! y ≡ ZR.0#) → set₁ m ZR.1# w ≡ eᶻ m
  set₁-e m w rest = vec-ext λ x → dec-elim (x FinP.≟ m)
    (λ { refl → trans (set₁-a x ZR.1# w) (sym (trans (eᶻ-! x x) (δᶻ-refl x))) })
    (λ x≢m → trans (set₁-≢ m ZR.1# w x≢m) (trans (rest x x≢m) (sym (trans (eᶻ-! m x) (δᶻ-≢ x≢m)))))

  -- Swapping it to p gives e_p.
  Xᶻ-e : (m p : Fin n) → m ≢ p → (w : Vec Z n) → (∀ y → y ≢ m → w ! y ≡ ZR.0#) →
         Xᶻ m p (set₁ m ZR.1# w) ≡ eᶻ p
  Xᶻ-e m p m≢p w rest = vec-ext λ x → dec-elim (x FinP.≟ m)
    (λ { refl → begin
          Xᶻ x p u ! x         ≡⟨ set₂-a x p (u ! p) (u ! x) u ⟩
          u ! p                ≡⟨ set₁-≢ x ZR.1# w (m≢p ∘ sym) ⟩
          w ! p                ≡⟨ rest p (m≢p ∘ sym) ⟩
          ZR.0#                ≡⟨ sym (trans (eᶻ-! p x) (δᶻ-≢ m≢p)) ⟩
          eᶻ p ! x             ∎ })
    (λ x≢m → dec-elim (x FinP.≟ p)
      (λ { refl → begin
            Xᶻ m x u ! x       ≡⟨ set₂-b m x (u ! x) (u ! m) u m≢p ⟩
            u ! m              ≡⟨ set₁-a m ZR.1# w ⟩
            ZR.1#              ≡⟨ sym (trans (eᶻ-! x x) (δᶻ-refl x)) ⟩
            eᶻ x ! x           ∎ })
      (λ x≢p → begin
            Xᶻ m p u ! x       ≡⟨ set₂-≢ m p (u ! p) (u ! m) u x≢m x≢p ⟩
            u ! x              ≡⟨ set₁-≢ m ZR.1# w x≢m ⟩
            w ! x              ≡⟨ rest x x≢m ⟩
            ZR.0#              ≡⟨ sym (trans (eᶻ-! p x) (δᶻ-≢ x≢p)) ⟩
            eᶻ p ! x           ∎))
    where
    open ≡-Reasoning
    u = set₁ m ZR.1# w

unit-step : ∀ {p : Fin n} (w : Vec Z n) → Σℕ (λ x → Nℕ (w ! x)) ≡ 1 → (∀ x → p < x → w ! x ≡ ZR.0#) →
            Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
unit-step {n} {p} w norm zero> = go (lde0 w norm)
  where
  open ≡-Reasoning
  go : (∃ λ m → Unit (w ! m) × (∀ y → y ≢ m → w ! y ≡ ZR.0#)) →
       Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
  go (m , (t , t<4 , um) , rest) =
    tri-elim (FinP.<-cmp m p) case< case≡ (λ p<m → ⊥-elim (unit≢0 t t<4 (trans (sym um) (zero> m p<m))))
    where
    om : Odd (w ! m)
    om = subst Odd (sym um) (unit-odd t t<4)
    fo : firstOdd w ≡ just m
    fo = firstOdd-char w om (λ x x<m → cong oddᶻ (rest x (λ { refl → ℕP.<-irrefl refl x<m })))
    e = invExp (w ! m)
    unitE : (ⅈᶻ ^ᶻ e) ZR.* (w ! m) ≡ ZR.1#
    unitE = subst (λ u → (ⅈᶻ ^ᶻ invExp u) ZR.* u ≡ ZR.1#) (sym um) (invExp-unit t t<4)
    w₁ = set₁ m ((ⅈᶻ ^ᶻ e) ZR.* (w ! m)) w
    w₁≡ : w₁ ≡ set₁ m ZR.1# w
    w₁≡ = cong (λ z → set₁ m z w) unitE
    case< : m < p → Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
    case< m<p = subst (λ W → Within p W × actVʷ W (scV 0 w) ≡ scV 0 (eᶻ p)) (sym (sylData-unit< w fo m<p))
      ( (FinP.≤-refl , Within-^ (i m) (ℕP.<⇒≤ m<p) e)
      , (begin
          actV (X-gen m p m<p) (actVʷ (i m ^ e) (scV 0 w))
            ≡⟨ cong (actV (X-gen m p m<p)) (i^-action m e 0 w) ⟩
          actV (X-gen m p m<p) (scV 0 w₁)
            ≡⟨ actV-X m p m<p 0 w₁ ⟩
          scV 0 (Xᶻ m p w₁)
            ≡⟨ cong (scV 0) (trans (cong (Xᶻ m p) w₁≡) (Xᶻ-e m p (<⇒≢ m<p) w rest)) ⟩
          scV 0 (eᶻ p) ∎))
    case≡ : m ≡ p → Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
    case≡ refl = subst (λ W → Within p W × actVʷ W (scV 0 w) ≡ scV 0 (eᶻ p)) (sym (sylData-unit≡ w fo))
      ( Within-^ (i m) FinP.≤-refl e
      , (begin
          actVʷ (i m ^ e) (scV 0 w)       ≡⟨ i^-action m e 0 w ⟩
          scV 0 w₁                        ≡⟨ cong (scV 0) (trans w₁≡ (set₁-e m w rest)) ⟩
          scV 0 (eᶻ m) ∎))

------------------------------------------------------------------------
-- k > 0: the syllable makes the entries j and ℓ even

private
  module ZS′ = ZS
  open ZS′ using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_)

  two* : ∀ c → 2ᶻ ZR.* c ≡ c ZR.+ c
  two* (Quantum.Synthesis.Ring.Cplx c₁ c₂) = cong₂ Quantum.Synthesis.Ring.Cplx
    (ℤS.solve 2 (λ x y → ℤS.con (+ 2) ℤS.:* x ℤS.:+ ℤS.:- (ℤS.con (+ 0) ℤS.:* y) ℤS.:= x ℤS.:+ x) refl c₁ c₂)
    (ℤS.solve 2 (λ x y → ℤS.con (+ 2) ℤS.:* y ℤS.:+ ℤS.con (+ 0) ℤS.:* x ℤS.:= y ℤS.:+ y) refl c₁ c₂)
    where
    import Data.Integer.Solver as ℤSolver
    module ℤS = ℤSolver.+-*-Solver

  ⅈ+ⅈ : ⅈᶻ ZR.+ ⅈᶻ ≡ γᶻ ZR.* γᶻ
  ⅈ+ⅈ = refl

  -- With a − d = 2c:  i(a + d) = γ(γ(d + c))  and  i(a − d) = γ(γ c).
  idJ : ∀ a d c → a ZR.- d ≡ 2ᶻ ZR.* c → ⅈᶻ ZR.* (a ZR.+ d) ≡ γᶻ ZR.* (γᶻ ZR.* (d ZR.+ c))
  idJ a d c eq = begin
    ⅈᶻ ZR.* (a ZR.+ d)                          ≡⟨ cong (λ z → ⅈᶻ ZR.* (z ZR.+ d)) a≡ ⟩
    ⅈᶻ ZR.* (((c ZR.+ c) ZR.+ d) ZR.+ d)         ≡⟨ ZS.solve 3 (λ ι c d → ι :* (((c :+ c) :+ d) :+ d) := (ι :+ ι) :* (d :+ c)) refl ⅈᶻ c d ⟩
    (ⅈᶻ ZR.+ ⅈᶻ) ZR.* (d ZR.+ c)                ≡⟨ cong (ZR._* (d ZR.+ c)) ⅈ+ⅈ ⟩
    (γᶻ ZR.* γᶻ) ZR.* (d ZR.+ c)                ≡⟨ ZR.*-assoc γᶻ γᶻ (d ZR.+ c) ⟩
    γᶻ ZR.* (γᶻ ZR.* (d ZR.+ c))                ∎
    where
    open ≡-Reasoning
    a≡ : a ≡ (c ZR.+ c) ZR.+ d
    a≡ = begin
      a                           ≡⟨ ZS.solve 2 (λ a d → a := (a :- d) :+ d) refl a d ⟩
      (a ZR.- d) ZR.+ d           ≡⟨ cong (ZR._+ d) (trans eq (two* c)) ⟩
      (c ZR.+ c) ZR.+ d           ∎

  idL : ∀ a d c → a ZR.- d ≡ 2ᶻ ZR.* c → ⅈᶻ ZR.* (a ZR.- d) ≡ γᶻ ZR.* (γᶻ ZR.* c)
  idL a d c eq = begin
    ⅈᶻ ZR.* (a ZR.- d)          ≡⟨ cong (ⅈᶻ ZR.*_) (trans eq (two* c)) ⟩
    ⅈᶻ ZR.* (c ZR.+ c)          ≡⟨ ZS.solve 2 (λ ι c → ι :* (c :+ c) := (ι :+ ι) :* c) refl ⅈᶻ c ⟩
    (ⅈᶻ ZR.+ ⅈᶻ) ZR.* c         ≡⟨ cong (ZR._* c) ⅈ+ⅈ ⟩
    (γᶻ ZR.* γᶻ) ZR.* c         ≡⟨ ZR.*-assoc γᶻ γᶻ c ⟩
    γᶻ ZR.* (γᶻ ZR.* c)         ∎
    where open ≡-Reasoning

  γ*-even : ∀ y → Even (γᶻ ZR.* y)
  γ*-even y = γ∣⇒even (y , refl)

-- The numerator after the row operation K†_[j,ℓ] i_[ℓ]ᑫ, at scale k + 1,
-- is γ times W′ = w with entries j and ℓ replaced by the even
-- numbers γ(d + c) and γc.
W-eq : ∀ (j ℓ : Fin n) → j ≢ ℓ → (w : Vec Z n) (d c : Z) → w ! j ZR.- d ≡ 2ᶻ ZR.* c →
       iᶻ j (iᶻ ℓ (Kᶻ j ℓ (set₁ ℓ d w))) ≡ Vec.map (γᶻ ZR.*_) (set₂ j ℓ (γᶻ ZR.* (d ZR.+ c)) (γᶻ ZR.* c) w)
W-eq j ℓ j≢ℓ w d c eq = vec-ext λ x → dec-elim (x FinP.≟ j)
  (λ { refl → begin
      iᶻ x (iᶻ ℓ K₁) ! x              ≡⟨ set₁-a x (ⅈᶻ ZR.* (iᶻ ℓ K₁ ! x)) (iᶻ ℓ K₁) ⟩
      ⅈᶻ ZR.* (iᶻ ℓ K₁ ! x)           ≡⟨ cong (ⅈᶻ ZR.*_) (set₁-≢ ℓ (ⅈᶻ ZR.* (K₁ ! ℓ)) K₁ j≢ℓ) ⟩
      ⅈᶻ ZR.* (K₁ ! x)                ≡⟨ cong (ⅈᶻ ZR.*_) (set₂-a x ℓ (w₁ ! x ZR.+ w₁ ! ℓ) (w₁ ! x ZR.- w₁ ! ℓ) γw₁) ⟩
      ⅈᶻ ZR.* (w₁ ! x ZR.+ w₁ ! ℓ)    ≡⟨ cong₂ (λ s t → ⅈᶻ ZR.* (s ZR.+ t)) (set₁-≢ ℓ d w j≢ℓ) (set₁-a ℓ d w) ⟩
      ⅈᶻ ZR.* (w ! x ZR.+ d)          ≡⟨ idJ (w ! x) d c eq ⟩
      γᶻ ZR.* (γᶻ ZR.* (d ZR.+ c))    ≡⟨ cong (γᶻ ZR.*_) (sym (set₂-a x ℓ (γᶻ ZR.* (d ZR.+ c)) (γᶻ ZR.* c) w)) ⟩
      γᶻ ZR.* (W′ ! x)                ≡⟨ sym (VecP.lookup-map x (γᶻ ZR.*_) W′) ⟩
      Vec.map (γᶻ ZR.*_) W′ ! x       ∎ })
  (λ x≢j → dec-elim (x FinP.≟ ℓ)
    (λ { refl → begin
        iᶻ j (iᶻ x K₁) ! x            ≡⟨ set₁-≢ j (ⅈᶻ ZR.* (iᶻ x K₁ ! j)) (iᶻ x K₁) x≢j ⟩
        iᶻ x K₁ ! x                   ≡⟨ set₁-a x (ⅈᶻ ZR.* (K₁ ! x)) K₁ ⟩
        ⅈᶻ ZR.* (K₁ ! x)              ≡⟨ cong (ⅈᶻ ZR.*_) (set₂-b j x (w₁ ! j ZR.+ w₁ ! x) (w₁ ! j ZR.- w₁ ! x) γw₁ j≢ℓ) ⟩
        ⅈᶻ ZR.* (w₁ ! j ZR.- w₁ ! x)  ≡⟨ cong₂ (λ s t → ⅈᶻ ZR.* (s ZR.- t)) (set₁-≢ x d w j≢ℓ) (set₁-a x d w) ⟩
        ⅈᶻ ZR.* (w ! j ZR.- d)        ≡⟨ idL (w ! j) d c eq ⟩
        γᶻ ZR.* (γᶻ ZR.* c)           ≡⟨ cong (γᶻ ZR.*_) (sym (set₂-b j x (γᶻ ZR.* (d ZR.+ c)) (γᶻ ZR.* c) w j≢ℓ)) ⟩
        γᶻ ZR.* (W′ ! x)              ≡⟨ sym (VecP.lookup-map x (γᶻ ZR.*_) W′) ⟩
        Vec.map (γᶻ ZR.*_) W′ ! x     ∎ })
    (λ x≢ℓ → begin
        iᶻ j (iᶻ ℓ K₁) ! x            ≡⟨ set₁-≢ j (ⅈᶻ ZR.* (iᶻ ℓ K₁ ! j)) (iᶻ ℓ K₁) x≢j ⟩
        iᶻ ℓ K₁ ! x                   ≡⟨ set₁-≢ ℓ (ⅈᶻ ZR.* (K₁ ! ℓ)) K₁ x≢ℓ ⟩
        K₁ ! x                        ≡⟨ set₂-≢ j ℓ (w₁ ! j ZR.+ w₁ ! ℓ) (w₁ ! j ZR.- w₁ ! ℓ) γw₁ x≢j x≢ℓ ⟩
        γw₁ ! x                       ≡⟨ VecP.lookup-map x (γᶻ ZR.*_) w₁ ⟩
        γᶻ ZR.* (w₁ ! x)              ≡⟨ cong (γᶻ ZR.*_) (trans (set₁-≢ ℓ d w x≢ℓ) (sym (set₂-≢ j ℓ (γᶻ ZR.* (d ZR.+ c)) (γᶻ ZR.* c) w x≢j x≢ℓ))) ⟩
        γᶻ ZR.* (W′ ! x)              ≡⟨ sym (VecP.lookup-map x (γᶻ ZR.*_) W′) ⟩
        Vec.map (γᶻ ZR.*_) W′ ! x     ∎))
  where
  open ≡-Reasoning
  w₁ = set₁ ℓ d w
  γw₁ = Vec.map (γᶻ ZR.*_) w₁
  K₁ = Kᶻ j ℓ w₁
  W′ = set₂ j ℓ (γᶻ ZR.* (d ZR.+ c)) (γᶻ ZR.* c) w

-- The row operation, given the first two odd entries j < ℓ.
pair-core : ∀ {p : Fin n} k′ (w : Vec Z n) {j ℓ : Fin n} →
            firstOdd w ≡ just j → nextOdd j w ≡ just ℓ → (j<ℓ : j < ℓ) →
            Odd (w ! j) → Odd (w ! ℓ) → ℓ ≤ p →
            ∃ λ W′ → Within p (sylData p (suc k′) w)
                   × actVʷ (sylData p (suc k′) w) (scV (suc k′) w) ≡ scV (suc k′) W′
                   × nodd w ≡ suc (suc (nodd W′))
pair-core {n} {p} k′ w {j} {ℓ} fo no j<ℓ oj oℓ ℓ≤p =
  W′ ,
  subst (λ W → Within p W × actVʷ W (scV (suc k′) w) ≡ scV (suc k′) W′) (sym (sylData-pair k′ w fo no j<ℓ))
    ( (Within-^ (K j ℓ j<ℓ) ℓ≤p 7 , Within-^ (i ℓ) ℓ≤p q)
    , action ) ,
  count-drop₂ (λ x → oddᶻ (w ! x)) (λ x → oddᶻ (W′ ! x)) j ℓ j≢ℓ oj oℓ
    (trans (cong oddᶻ (set₂-a j ℓ (γᶻ ZR.* (d ZR.+ c)) (γᶻ ZR.* c) w)) (γ*-even (d ZR.+ c)))
    (trans (cong oddᶻ (set₂-b j ℓ (γᶻ ZR.* (d ZR.+ c)) (γᶻ ZR.* c) w j≢ℓ)) (γ*-even c))
    (λ x x≢j x≢ℓ → sym (cong oddᶻ (set₂-≢ j ℓ (γᶻ ZR.* (d ZR.+ c)) (γᶻ ZR.* c) w x≢j x≢ℓ)))
  where
  open ≡-Reasoning
  j≢ℓ = <⇒≢ j<ℓ
  q = qOf (w ! j) (w ! ℓ)
  d = (ⅈᶻ ^ᶻ q) ZR.* (w ! ℓ)
  c = proj₁ (qOf-spec (w ! j) (w ! ℓ) oj oℓ)
  eqc : w ! j ZR.- d ≡ 2ᶻ ZR.* c
  eqc = proj₂ (qOf-spec (w ! j) (w ! ℓ) oj oℓ)
  W′ = set₂ j ℓ (γᶻ ZR.* (d ZR.+ c)) (γᶻ ZR.* c) w
  w₁ = set₁ ℓ d w
  k = suc k′
  action : actVʷ (K† j ℓ j<ℓ) (actVʷ (i ℓ ^ q) (scV k w)) ≡ scV k W′
  action = begin
    actVʷ (K† j ℓ j<ℓ) (actVʷ (i ℓ ^ q) (scV k w))
      ≡⟨ cong (actVʷ (K† j ℓ j<ℓ)) (i^-action ℓ q k w) ⟩
    actVʷ (K† j ℓ j<ℓ) (scV k w₁)
      ≡⟨ K†-action j ℓ j<ℓ (scV k w₁) ⟩
    actV (i-gen j) (actV (i-gen ℓ) (actV (K-gen j ℓ j<ℓ) (scV k w₁)))
      ≡⟨ cong (λ u → actV (i-gen j) (actV (i-gen ℓ) u)) (actV-K j ℓ j<ℓ k w₁) ⟩
    actV (i-gen j) (actV (i-gen ℓ) (scV (suc k) (Kᶻ j ℓ w₁)))
      ≡⟨ cong (actV (i-gen j)) (actV-i ℓ (suc k) (Kᶻ j ℓ w₁)) ⟩
    actV (i-gen j) (scV (suc k) (iᶻ ℓ (Kᶻ j ℓ w₁)))
      ≡⟨ actV-i j (suc k) (iᶻ ℓ (Kᶻ j ℓ w₁)) ⟩
    scV (suc k) (iᶻ j (iᶻ ℓ (Kᶻ j ℓ w₁)))
      ≡⟨ cong (scV (suc k)) (W-eq j ℓ j≢ℓ w d c eqc) ⟩
    scV (suc k) (Vec.map (γᶻ ZR.*_) W′)
      ≡⟨ scV-γmap k W′ ⟩
    scV k W′ ∎

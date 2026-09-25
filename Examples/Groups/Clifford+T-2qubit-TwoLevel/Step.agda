------------------------------------------------------------------------
-- Presentations of groups
--
-- Termination of the exact synthesis algorithm (Theorem 2.16): for a
-- column-orthonormal matrix M ≠ I, one step lowers the level.
--
-- * If the pivot column v has k = lde v = 0, it is a unit times a
--   standard basis vector e_m (Lemma 2.12), and the syllable turns it
--   into e_p, so the pivot drops.
-- * If k > 0, the syllable H_[j,ℓ] ω_[j]ᶻ makes the entries j and ℓ
--   of δᵏ v even (Lemma 2.13: the row operation), so the number of
--   odd entries drops by two, or the exponent drops.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Step where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; _xor_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Integer.Base using (+_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂ ; [_,_]′)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as VecP
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; dec-true)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Scale
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Residue using (δ²ᶻ ; δ³ᶻ ; g2 ; _∣_ ; _,_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Search
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Norm
  using (NA ; Σℕ ; Unit ; evenodd ; lde0 ; unit-norm ; P)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Column
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Pivot
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syllable

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The numerator of the pivot column
--
-- Beyond the pivot, the columns are those of the identity, so by
-- orthogonality the pivot column vanishes there; being a unit vector,
-- its numerator has Σ Aₓ = Pₖ.

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
           + Σℕ (λ x → NA (num (col M p) ! x)) ≡ P (lde (col M p))
col-norm {M = M} o p =
  unit-norm (lde (col M p)) (num (col M p))
    (subst (λ u → ⟨ u , u ⟩ ≡ DR.1#) (lde-eq (col M p)) (col-unit o p))

-- The odd entries are at indices ≤ p.
odd⇒≤ : {p : Fin n} {w : Vec Z n} → (∀ x → p < x → w ! x ≡ ZR.0#) → ∀ {x} → Odd (w ! x) → x ≤ p
odd⇒≤ {p = p} {w} zero> {x} ox = tri-elim (FinP.<-cmp p x)
  (λ p<x → ⊥-elim (Odd⇒¬Even {w ! x} ox (cong oddᶻ (zero> x p<x))))
  (λ { refl → FinP.≤-refl })
  (λ x<p → ℕP.<⇒≤ x<p)

------------------------------------------------------------------------
-- Scaling a numerator by δ²

scV-δ²map : ∀ k (W : Vec Z n) → scV (suc (suc k)) (Vec.map (δ²ᶻ ZR.*_) W) ≡ scV k W
scV-δ²map k W = vec-ext λ x → begin
  scV (suc (suc k)) (Vec.map (δ²ᶻ ZR.*_) W) ! x    ≡⟨ scV-! (suc (suc k)) (Vec.map (δ²ᶻ ZR.*_) W) x ⟩
  sc (suc (suc k)) (Vec.map (δ²ᶻ ZR.*_) W ! x)     ≡⟨ cong (sc (suc (suc k))) (VecP.lookup-map x (δ²ᶻ ZR.*_) W) ⟩
  sc (suc (suc k)) (δ²ᶻ ZR.* (W ! x))              ≡⟨ sc-δ² k (W ! x) ⟩
  sc k (W ! x)                                     ≡⟨ sym (scV-! k W x) ⟩
  scV k W ! x                                      ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- k = 0: the syllable restores e_p

private
  unit≢0 : ∀ t → t ℕ.< 8 → ωᶻ ^ᶻ t ≢ ZR.0#
  unit≢0 0 _ ()
  unit≢0 1 _ ()
  unit≢0 2 _ ()
  unit≢0 3 _ ()
  unit≢0 4 _ ()
  unit≢0 5 _ ()
  unit≢0 6 _ ()
  unit≢0 7 _ ()
  unit≢0 (suc (suc (suc (suc (suc (suc (suc (suc t)))))))) (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ())))))))) _
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

unit-step : ∀ {p : Fin n} (w : Vec Z n) → + Σℕ (λ x → NA (w ! x)) ≡ + 1 → (∀ x → p < x → w ! x ≡ ZR.0#) →
            Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
unit-step {n} {p} w norm zero> = go (lde0 w norm)
  where
  open ≡-Reasoning
  go : (∃ λ m → Unit (w ! m) × (∀ y → y ≢ m → w ! y ≡ ZR.0#)) →
       Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
  go (m , (t , t<8 , um) , rest) =
    tri-elim (FinP.<-cmp m p) case< case≡ (λ p<m → ⊥-elim (unit≢0 t t<8 (trans (sym um) (zero> m p<m))))
    where
    om : Odd (w ! m)
    om = subst Odd (sym um) (unit-odd t t<8)
    fo : firstOdd w ≡ just m
    fo = firstOdd-char w om (λ x x<m → cong oddᶻ (rest x (λ { refl → ℕP.<-irrefl refl x<m })))
    e = invExp (w ! m)
    unitE : (ωᶻ ^ᶻ e) ZR.* (w ! m) ≡ ZR.1#
    unitE = subst (λ u → (ωᶻ ^ᶻ invExp u) ZR.* u ≡ ZR.1#) (sym um) (invExp-unit t t<8)
    w₁ = set₁ m ((ωᶻ ^ᶻ e) ZR.* (w ! m)) w
    w₁≡ : w₁ ≡ set₁ m ZR.1# w
    w₁≡ = cong (λ z → set₁ m z w) unitE
    case< : m < p → Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
    case< m<p = subst (λ W → Within p W × actVʷ W (scV 0 w) ≡ scV 0 (eᶻ p)) (sym (sylData-unit< w fo m<p))
      ( (FinP.≤-refl , Within-^ (ω m) (ℕP.<⇒≤ m<p) e)
      , (begin
          actV (X-gen m p m<p) (actVʷ (ω m ^ e) (scV 0 w))
            ≡⟨ cong (actV (X-gen m p m<p)) (ω^-action m e 0 w) ⟩
          actV (X-gen m p m<p) (scV 0 w₁)
            ≡⟨ actV-X m p m<p 0 w₁ ⟩
          scV 0 (Xᶻ m p w₁)
            ≡⟨ cong (scV 0) (trans (cong (Xᶻ m p) w₁≡) (Xᶻ-e m p (<⇒≢ m<p) w rest)) ⟩
          scV 0 (eᶻ p) ∎))
    case≡ : m ≡ p → Within p (sylData p 0 w) × actVʷ (sylData p 0 w) (scV 0 w) ≡ scV 0 (eᶻ p)
    case≡ refl = subst (λ W → Within p W × actVʷ W (scV 0 w) ≡ scV 0 (eᶻ p)) (sym (sylData-unit≡ w fo))
      ( Within-^ (ω m) FinP.≤-refl e
      , (begin
          actVʷ (ω m ^ e) (scV 0 w)       ≡⟨ ω^-action m e 0 w ⟩
          scV 0 w₁                        ≡⟨ cong (scV 0) (trans w₁≡ (set₁-e m w rest)) ⟩
          scV 0 (eᶻ m) ∎))

------------------------------------------------------------------------
-- k > 0: the syllable makes the entries j and ℓ even

private
  open ZG using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

  -- With a = d + δ³ c:  λω (a + d) = δ² (λω (g₂ d + δ c))  and
  -- λω (a − d) = δ² (λω (δ c)), where g₂ = 2 / δ².
  idJ : ∀ a d c → a ≡ d ZR.+ δ³ᶻ ZR.* c → λωᶻ ZR.* (a ZR.+ d) ≡ δ²ᶻ ZR.* (λωᶻ ZR.* (g2 ZR.* d ZR.+ δᶻ ZR.* c))
  idJ a d c refl =
    ZG.solve 2 (λ d c → con λωᶻ :* ((d :+ con δ³ᶻ :* c) :+ d) := con δ²ᶻ :* (con λωᶻ :* (con g2 :* d :+ con δᶻ :* c)))
               refl d c

  idL : ∀ a d c → a ≡ d ZR.+ δ³ᶻ ZR.* c → λωᶻ ZR.* (a ZR.- d) ≡ δ²ᶻ ZR.* (λωᶻ ZR.* (δᶻ ZR.* c))
  idL a d c refl =
    ZG.solve 2 (λ d c → con λωᶻ :* ((d :+ con δ³ᶻ :* c) :- d) := con δ²ᶻ :* (con λωᶻ :* (con δᶻ :* c)))
               refl d c

  -- The new entries are even.
  evenJ : ∀ d c → Even (λωᶻ ZR.* (g2 ZR.* d ZR.+ δᶻ ZR.* c))
  evenJ d c = trans (oddᶻ-* λωᶻ (g2 ZR.* d ZR.+ δᶻ ZR.* c))
                    (cong (true ∧_) (trans (oddᶻ-+ (g2 ZR.* d) (δᶻ ZR.* c))
                      (cong₂ _xor_ (oddᶻ-* g2 d) (oddᶻ-* δᶻ c))))

  evenL : ∀ c → Even (λωᶻ ZR.* (δᶻ ZR.* c))
  evenL c = trans (oddᶻ-* λωᶻ (δᶻ ZR.* c)) (cong (true ∧_) (oddᶻ-* δᶻ c))

-- The numerator after the row operation H_[j,ℓ] ω_[j]ᶻ, at scale k + 2,
-- is δ² times W′ = w with entries j and ℓ replaced by the even numbers
-- λω (g₂ d + δ c) and λω δ c, where ωᶻ w_j = d + δ³ c.
W-eq : ∀ (j ℓ : Fin n) → j ≢ ℓ → (w : Vec Z n) (a c : Z) → a ≡ w ! ℓ ZR.+ δ³ᶻ ZR.* c →
       Hᶻ j ℓ (set₁ j a w) ≡
       Vec.map (δ²ᶻ ZR.*_) (set₂ j ℓ (λωᶻ ZR.* (g2 ZR.* (w ! ℓ) ZR.+ δᶻ ZR.* c)) (λωᶻ ZR.* (δᶻ ZR.* c)) w)
W-eq j ℓ j≢ℓ w a c eq = vec-ext λ x → dec-elim (x FinP.≟ j)
  (λ { refl → begin
      Hᶻ x ℓ w₁ ! x                                       ≡⟨ set₂-a x ℓ (λωᶻ ZR.* (w₁ ! x ZR.+ w₁ ! ℓ)) (λωᶻ ZR.* (w₁ ! x ZR.- w₁ ! ℓ)) δw₁ ⟩
      λωᶻ ZR.* (w₁ ! x ZR.+ w₁ ! ℓ)                       ≡⟨ cong₂ (λ s t → λωᶻ ZR.* (s ZR.+ t)) (set₁-a x a w) (set₁-≢ x a w (j≢ℓ ∘ sym)) ⟩
      λωᶻ ZR.* (a ZR.+ w ! ℓ)                             ≡⟨ idJ a (w ! ℓ) c eq ⟩
      δ²ᶻ ZR.* Jv                                         ≡⟨ cong (δ²ᶻ ZR.*_) (sym (set₂-a x ℓ Jv Lv w)) ⟩
      δ²ᶻ ZR.* (W′ ! x)                                   ≡⟨ sym (VecP.lookup-map x (δ²ᶻ ZR.*_) W′) ⟩
      Vec.map (δ²ᶻ ZR.*_) W′ ! x                          ∎ })
  (λ x≢j → dec-elim (x FinP.≟ ℓ)
    (λ { refl → begin
        Hᶻ j x w₁ ! x                                     ≡⟨ set₂-b j x (λωᶻ ZR.* (w₁ ! j ZR.+ w₁ ! x)) (λωᶻ ZR.* (w₁ ! j ZR.- w₁ ! x)) δw₁ j≢ℓ ⟩
        λωᶻ ZR.* (w₁ ! j ZR.- w₁ ! x)                     ≡⟨ cong₂ (λ s t → λωᶻ ZR.* (s ZR.- t)) (set₁-a j a w) (set₁-≢ j a w x≢j) ⟩
        λωᶻ ZR.* (a ZR.- w ! x)                           ≡⟨ idL a (w ! x) c eq ⟩
        δ²ᶻ ZR.* Lv                                       ≡⟨ cong (δ²ᶻ ZR.*_) (sym (set₂-b j x Jv Lv w j≢ℓ)) ⟩
        δ²ᶻ ZR.* (W′ ! x)                                 ≡⟨ sym (VecP.lookup-map x (δ²ᶻ ZR.*_) W′) ⟩
        Vec.map (δ²ᶻ ZR.*_) W′ ! x                        ∎ })
    (λ x≢ℓ → begin
        Hᶻ j ℓ w₁ ! x                                     ≡⟨ set₂-≢ j ℓ (λωᶻ ZR.* (w₁ ! j ZR.+ w₁ ! ℓ)) (λωᶻ ZR.* (w₁ ! j ZR.- w₁ ! ℓ)) δw₁ x≢j x≢ℓ ⟩
        δw₁ ! x                                           ≡⟨ VecP.lookup-map x (δ²ᶻ ZR.*_) w₁ ⟩
        δ²ᶻ ZR.* (w₁ ! x)                                 ≡⟨ cong (δ²ᶻ ZR.*_) (trans (set₁-≢ j a w x≢j) (sym (set₂-≢ j ℓ Jv Lv w x≢j x≢ℓ))) ⟩
        δ²ᶻ ZR.* (W′ ! x)                                 ≡⟨ sym (VecP.lookup-map x (δ²ᶻ ZR.*_) W′) ⟩
        Vec.map (δ²ᶻ ZR.*_) W′ ! x                        ∎))
  where
  open ≡-Reasoning
  w₁ = set₁ j a w
  δw₁ = Vec.map (δ²ᶻ ZR.*_) w₁
  Jv = λωᶻ ZR.* (g2 ZR.* (w ! ℓ) ZR.+ δᶻ ZR.* c)
  Lv = λωᶻ ZR.* (δᶻ ZR.* c)
  W′ = set₂ j ℓ Jv Lv w

-- The numerator after the row operation, for c with
-- ωᶻ w_j − w_ℓ = δ³ c.
pairW : (w : Vec Z n) (j ℓ : Fin n) (c : Z) → Vec Z n
pairW w j ℓ c = set₂ j ℓ (λωᶻ ZR.* (g2 ZR.* (w ! ℓ) ZR.+ δᶻ ZR.* c)) (λωᶻ ZR.* (δᶻ ZR.* c)) w

-- The numerator after ω_[a]ᵉ.
ωset : Fin n → ℕ → Vec Z n → Vec Z n
ωset a e w = set₁ a ((ωᶻ ^ᶻ e) ZR.* (w ! a)) w

private
  actVʷ-• : (u v : Word (Gen n)) (x : Vec D n) → actVʷ (u • v) x ≡ actVʷ u (actVʷ v x)
  actVʷ-• u v x = refl

  -- Congruence with explicit endpoints.
  cong-actVʷ : (u : Word (Gen n)) (x y : Vec D n) → x ≡ y → actVʷ u x ≡ actVʷ u y
  cong-actVʷ u x y refl = refl

  -- ωᶻ w_j = w_ℓ + δ³ c.
  shift : ∀ a d c → a ZR.- d ≡ δ³ᶻ ZR.* c → a ≡ d ZR.+ δ³ᶻ ZR.* c
  shift a d c eq = trans (ZG.solve 2 (λ a d → a := d :+ (a :- d)) refl a d) (cong (d ZR.+_) eq)

pair-action : ∀ k (w : Vec Z n) (j ℓ : Fin n) (j<ℓ : j < ℓ) (z : ℕ) (c : Z) →
              (ωᶻ ^ᶻ z) ZR.* (w ! j) ZR.- w ! ℓ ≡ δ³ᶻ ZR.* c →
              actVʷ (H j ℓ j<ℓ • ω j ^ z) (scV k w) ≡ scV k (pairW w j ℓ c)
pair-action k w j ℓ j<ℓ z c eq = begin
  actVʷ (H j ℓ j<ℓ • ω j ^ z) (scV k w)
    ≡⟨ actVʷ-• (H j ℓ j<ℓ) (ω j ^ z) (scV k w) ⟩
  actV (H-gen j ℓ j<ℓ) (actVʷ (ω j ^ z) (scV k w))
    ≡⟨ cong-actVʷ (H j ℓ j<ℓ) (actVʷ (ω j ^ z) (scV k w)) (scV k (ωset j z w)) (ω^-action j z k w) ⟩
  actV (H-gen j ℓ j<ℓ) (scV k (ωset j z w))
    ≡⟨ actV-H j ℓ j<ℓ k (ωset j z w) ⟩
  scV (suc (suc k)) (Hᶻ j ℓ (ωset j z w))
    ≡⟨ cong (scV (suc (suc k))) (W-eq j ℓ (<⇒≢ j<ℓ) w ((ωᶻ ^ᶻ z) ZR.* (w ! j)) c
                                     (shift ((ωᶻ ^ᶻ z) ZR.* (w ! j)) (w ! ℓ) c eq)) ⟩
  scV (suc (suc k)) (Vec.map (δ²ᶻ ZR.*_) (pairW w j ℓ c))
    ≡⟨ scV-δ²map k (pairW w j ℓ c) ⟩
  scV k (pairW w j ℓ c) ∎
  where open ≡-Reasoning

-- The entries j and ℓ become even, the others keep their parity.
pair-count : (w : Vec Z n) (j ℓ : Fin n) → j ≢ ℓ → (c : Z) →
             Odd (w ! j) → Odd (w ! ℓ) → nodd w ≡ suc (suc (nodd (pairW w j ℓ c)))
pair-count w j ℓ j≢ℓ c oj oℓ =
  count-drop₂ (λ x → oddᶻ (w ! x)) (λ x → oddᶻ (pairW w j ℓ c ! x)) j ℓ j≢ℓ oj oℓ
    (trans (cong oddᶻ (set₂-a j ℓ Jv Lv w)) (evenJ (w ! ℓ) c))
    (trans (cong oddᶻ (set₂-b j ℓ Jv Lv w j≢ℓ)) (evenL c))
    (λ x x≢j x≢ℓ → sym (cong oddᶻ (set₂-≢ j ℓ Jv Lv w x≢j x≢ℓ)))
  where
  Jv = λωᶻ ZR.* (g2 ZR.* (w ! ℓ) ZR.+ δᶻ ZR.* c)
  Lv = λωᶻ ZR.* (δᶻ ZR.* c)

-- The row operation, given the first two odd entries j < ℓ.
pair-core : ∀ {p : Fin n} k′ (w : Vec Z n) {j ℓ : Fin n} →
            firstOdd w ≡ just j → nextOdd j w ≡ just ℓ → (j<ℓ : j < ℓ) →
            Odd (w ! j) → Odd (w ! ℓ) → ℓ ≤ p →
            ∃ λ W′ → Within p (sylData p (suc k′) w)
                   × actVʷ (sylData p (suc k′) w) (scV (suc k′) w) ≡ scV (suc k′) W′
                   × nodd w ≡ suc (suc (nodd W′))
pair-core {n} {p} k′ w {j} {ℓ} fo nx j<ℓ oj oℓ ℓ≤p = go (zOf-spec (w ! j) (w ! ℓ) oj oℓ)
  where
  go : δ³ᶻ ∣ ((ωᶻ ^ᶻ zOf (w ! j) (w ! ℓ)) ZR.* (w ! j) ZR.- w ! ℓ) →
       ∃ λ W′ → Within p (sylData p (suc k′) w)
              × actVʷ (sylData p (suc k′) w) (scV (suc k′) w) ≡ scV (suc k′) W′
              × nodd w ≡ suc (suc (nodd W′))
  go (c , eqc) = W′ , within , act , pair-count w j ℓ (<⇒≢ j<ℓ) c oj oℓ
    where
    z = zOf (w ! j) (w ! ℓ)
    W′ = pairW w j ℓ c
    syl≡ : sylData p (suc k′) w ≡ H j ℓ j<ℓ • ω j ^ zOf (w ! j) (w ! ℓ)
    syl≡ = sylData-pair {p = p} k′ w fo nx j<ℓ
    within : Within p (sylData p (suc k′) w)
    within = subst (Within p) (sym syl≡) (ℓ≤p , Within-^ (ω j) (ℕP.<⇒≤ (ℕP.<-≤-trans j<ℓ ℓ≤p)) z)
    act : actVʷ (sylData p (suc k′) w) (scV (suc k′) w) ≡ scV (suc k′) W′
    act = subst (λ W → actVʷ W (scV (suc k′) w) ≡ scV (suc k′) W′) (sym syl≡)
                (pair-action (suc k′) w j ℓ j<ℓ z c eqc)

------------------------------------------------------------------------
-- k > 0: the first two odd entries exist

pair-step : ∀ {p : Fin n} k′ (w : Vec Z n) → Minimal (suc k′) w →
            + Σℕ (λ x → NA (w ! x)) ≡ P (suc k′) → (∀ {x} → Odd (w ! x) → x ≤ p) →
            ∃ λ W′ → Within p (sylData p (suc k′) w)
                   × actVʷ (sylData p (suc k′) w) (scV (suc k′) w) ≡ scV (suc k′) W′
                   × nodd w ≡ suc (suc (nodd W′))
pair-step k′ w (inj₁ ()) norm ≤p
pair-step {n} {p} k′ w (inj₂ (x , ox)) norm ≤p = withFirst (firstOdd w) refl
  where
  Goal : Set
  Goal = ∃ λ W′ → Within p (sylData p (suc k′) w)
                × actVʷ (sylData p (suc k′) w) (scV (suc k′) w) ≡ scV (suc k′) W′
                × nodd w ≡ suc (suc (nodd W′))

  withFirst : (r : Maybe (Fin n)) → firstOdd w ≡ r → Goal
  withFirst nothing fo = ⊥-elim (Odd⇒¬Even {w ! x} ox (firstOdd-nothing w fo x))
  withFirst (just j) fo = withNext (nextOdd j w) refl
    where
    oj : Odd (w ! j)
    oj = proj₁ (firstOdd-spec w fo)

    withNext : (r : Maybe (Fin n)) → nextOdd j w ≡ r → Goal
    withNext (just ℓ) nx =
      pair-core k′ w fo nx (proj₁ (nextOdd-spec w nx)) oj (proj₁ (proj₂ (nextOdd-spec w nx)))
        (≤p (proj₁ (proj₂ (nextOdd-spec w nx))))
    -- Otherwise j is the only odd entry, but their number is even.
    withNext nothing nx = ⊥-elim (true≢false (trans (sym (cong oddℕ one)) (evenodd k′ w norm)))
      where
      true≢false : true ≢ false
      true≢false ()
      others : ∀ y → y ≢ j → oddᶻ (w ! y) ≡ false
      others y y≢j = tri-elim (FinP.<-cmp y j)
        (λ y<j → proj₂ (firstOdd-spec w fo) y y<j)
        (λ y≡j → ⊥-elim (y≢j y≡j))
        (λ j<y → trans (cong (_∧ oddᶻ (w ! y)) (sym (dec-true (j FinP.<? y) j<y)))
                       (first-nothing (λ z → does (j FinP.<? z) ∧ oddᶻ (w ! z)) nx y))
      one : nodd w ≡ 1
      one = count-one (λ y → oddᶻ (w ! y)) j oj others

------------------------------------------------------------------------
-- One step lowers the level (the proof of Theorem 2.9)

private
  scV-injective : ∀ k (u v : Vec Z n) → scV k u ≡ scV k v → u ≡ v
  scV-injective k u v eq = vec-ext λ x →
    sc-injective k (trans (sym (scV-! k u x)) (trans (cong (_! x) eq) (scV-! k v x)))

  -- The column p after the syllable S.
  col-step : (M : Matrix n n D) (p : Fin n) (S : Word (Gen n)) (K : ℕ) (W : Vec Z n) →
             col M p ≡ scV K W → col (actMʷ S M) p ≡ actVʷ S (scV K W)
  col-step M p S K W eq = trans (col-actMʷ S M p) (cong-actVʷ S (col M p) (scV K W) eq)

-- The level drops, given the data of the pivot column.
lt-core : (M : Matrix n n D) (p : Fin n) (K : ℕ) (W : Vec Z n) →
          Beyond p M → col M p ≡ scV K W → Minimal K W → (∀ x → p < x → W ! x ≡ ZR.0#) →
          + Σℕ (λ x → NA (W ! x)) ≡ P K →
          level (actMʷ (sylData p K W) M) <ₗ (suc (toℕ p) , K , nodd W)
lt-core M p zero W be eq min zero> norm =
  level-below (actMʷ S M) col≡ (Beyond-actMʷ S {p} {M} (proj₁ us) be) zero (nodd W)
  where
  S = sylData p zero W
  us = unit-step W norm zero>
  col≡ : col (actMʷ S M) p ≡ col 𝕀 p
  col≡ = trans (col-step M p S zero W eq) (trans (proj₂ us) (sym (col𝕀≡ p)))
lt-core M p (suc K′) W be eq min zero> norm = go (pair-step K′ W min norm (odd⇒≤ {p = p} {W} zero>))
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
             (pivot-zero> o pv) (col-norm o p))
  where
  v = col M p

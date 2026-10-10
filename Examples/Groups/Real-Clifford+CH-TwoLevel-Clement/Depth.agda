------------------------------------------------------------------------
-- Presentations of groups
--
-- Depths and classes of entries, decided, and counts.
--
-- An entry z is of depth δ and class b when z = √2^δ y with y odd of
-- class b (cls? δ z ≡ just b); deep? δ z says it is of depth δ.  The
-- pairing recursion of Hard counts the entries of depths 1 and 2.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Depth where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; not ; if_then_else_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
import Data.Fin.Properties as FinP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; ∃₂ ; _×_ ; _,_ ; proj₁)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes ; no)

open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count ; count-cong ; count-drop ; first ; first-just ; first-nothing)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (Z ; module ZR ; module ZG ; √2ᶻ ; _^ᶻ_ ; oddᶻ ; rbit ; oddᶻ-*)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Forms using (halfZ ; halfZ-sound ; halfZ-odd)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Tree using (caseM ; _==_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.TreeFacts using (halfZ-√2 ; t≢f)

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- Halving δ times

halfZⁿ : ℕ → Z → Maybe Z
halfZⁿ zero z = just z
halfZⁿ (suc δ) z = caseM (halfZ z) nothing (halfZⁿ δ)

halfZⁿ-sound : ∀ δ z {y} → halfZⁿ δ z ≡ just y → z ≡ (√2ᶻ ^ᶻ δ) ZR.* y
halfZⁿ-sound zero z refl = sym (ZR.*-identityˡ z)
halfZⁿ-sound (suc δ) z {y} e = go (halfZ z) refl e
  where
  go : ∀ m → halfZ z ≡ m → caseM m nothing (halfZⁿ δ) ≡ just y → z ≡ (√2ᶻ ^ᶻ suc δ) ZR.* y
  go (just w) h e′ = trans (halfZ-sound z h) (trans (cong (√2ᶻ ZR.*_) (halfZⁿ-sound δ w e′)) (sym (ZR.*-assoc √2ᶻ (√2ᶻ ^ᶻ δ) y)))
  go nothing h ()

halfZⁿ-pow : ∀ δ y → halfZⁿ δ ((√2ᶻ ^ᶻ δ) ZR.* y) ≡ just y
halfZⁿ-pow zero y = cong just (ZR.*-identityˡ y)
halfZⁿ-pow (suc δ) y =
  trans (cong (λ z → caseM (halfZ z) nothing (halfZⁿ δ)) (ZR.*-assoc √2ᶻ (√2ᶻ ^ᶻ δ) y))
    (trans (cong (λ m → caseM m nothing (halfZⁿ δ)) (halfZ-√2 ((√2ᶻ ^ᶻ δ) ZR.* y))) (halfZⁿ-pow δ y))

------------------------------------------------------------------------
-- Classes at a depth

cls? : ℕ → Z → Maybe Bool
cls? δ z = caseM (halfZⁿ δ z) nothing λ y → if oddᶻ y then just (rbit y) else nothing

deep? : ℕ → Z → Bool
deep? δ z = caseM (cls? δ z) false (λ _ → true)

private
  cls-of : ∀ y → oddᶻ y ≡ true → (if oddᶻ y then just (rbit y) else nothing) ≡ just (rbit y)
  cls-of y o = cong (λ b → if b then just (rbit y) else nothing) o

  cls-even : ∀ y → oddᶻ y ≡ false → (if oddᶻ y then just (rbit y) else nothing) ≡ nothing
  cls-even y o = cong (λ b → if b then just (rbit y) else nothing) o

cls?-complete : ∀ δ z y → z ≡ (√2ᶻ ^ᶻ δ) ZR.* y → oddᶻ y ≡ true → cls? δ z ≡ just (rbit y)
cls?-complete δ z y refl o = trans (cong (λ m → caseM m nothing λ y → if oddᶻ y then just (rbit y) else nothing) (halfZⁿ-pow δ y)) (cls-of y o)

cls?-sound : ∀ δ z b → cls? δ z ≡ just b → ∃ λ y → z ≡ (√2ᶻ ^ᶻ δ) ZR.* y × oddᶻ y ≡ true × rbit y ≡ b
cls?-sound δ z b e = go (halfZⁿ δ z) refl e
  where
  go : ∀ m → halfZⁿ δ z ≡ m → caseM m nothing (λ y → if oddᶻ y then just (rbit y) else nothing) ≡ just b →
       ∃ λ y → z ≡ (√2ᶻ ^ᶻ δ) ZR.* y × oddᶻ y ≡ true × rbit y ≡ b
  go (just y) h e′ = y , halfZⁿ-sound δ z h , odd , just-inj (trans (sym (cls-of y odd)) e′)
    where
    nj : nothing ≢ just b
    nj ()
    by : ∀ c → oddᶻ y ≡ c → oddᶻ y ≡ true
    by true e = e
    by false e = ⊥-elim (nj (trans (sym (cls-even y e)) e′))
    odd : oddᶻ y ≡ true
    odd = by (oddᶻ y) refl
    just-inj : ∀ {a c : Bool} → just a ≡ just c → a ≡ c
    just-inj refl = refl
  go nothing h ()

-- An entry √2^(δ+1) y is not of depth δ.
cls?-deeper : ∀ δ y → cls? δ ((√2ᶻ ^ᶻ suc δ) ZR.* y) ≡ nothing
cls?-deeper δ y =
  trans (cong (cls? δ) (sym (trans (cong ((√2ᶻ ^ᶻ δ) ZR.*_) refl) (ZG.solve 2 (λ c y → c :* (con √2ᶻ :* y) := (con √2ᶻ :* c) :* y) refl (√2ᶻ ^ᶻ δ) y))))
    (trans (cong (λ m → caseM m nothing λ y → if oddᶻ y then just (rbit y) else nothing) (halfZⁿ-pow δ (√2ᶻ ZR.* y)))
      (cls-even (√2ᶻ ZR.* y) (oddᶻ-* √2ᶻ y)))
  where open ZG using (_:*_ ; _:=_ ; con)

deep?-cls : ∀ δ z b → cls? δ z ≡ just b → deep? δ z ≡ true
deep?-cls δ z b e = cong (λ m → caseM m false (λ _ → true)) e

deep?-nothing : ∀ δ z → cls? δ z ≡ nothing → deep? δ z ≡ false
deep?-nothing δ z e = cong (λ m → caseM m false (λ _ → true)) e

------------------------------------------------------------------------
-- Counting

ind : Bool → ℕ
ind b = if b then 1 else 0

-- Changing one index of a predicate.
count-replace : ∀ (P Q : Fin k → Bool) (a : Fin k) → (∀ x → x ≢ a → P x ≡ Q x) →
                count P ℕ.+ ind (Q a) ≡ count Q ℕ.+ ind (P a)
count-replace P Q a agree = by (P a) (Q a) refl refl
  where
  same : P a ≡ Q a → ∀ x → P x ≡ Q x
  same e x with x FinP.≟ a
  ... | yes refl = e
  ... | no x≢a = agree x x≢a
  by : ∀ pa qa → P a ≡ pa → Q a ≡ qa → count P ℕ.+ ind qa ≡ count Q ℕ.+ ind pa
  by true true ep eq = cong (ℕ._+ 1) (count-cong P Q (same (trans ep (sym eq))))
  by false false ep eq = cong (ℕ._+ 0) (count-cong P Q (same (trans ep (sym eq))))
  by true false ep eq = trans (ℕP.+-identityʳ (count P)) (trans (count-drop P Q a ep eq agree) (ℕP.+-comm 1 (count Q)))
  by false true ep eq = trans (ℕP.+-comm (count P) 1) (trans (sym (count-drop Q P a eq ep (λ x x≢a → sym (agree x x≢a))))
                                                         (sym (ℕP.+-identityʳ (count Q))))

-- Two indices where P holds, or none such.
two? : ∀ (P : Fin k → Bool) → (∃₂ λ u v → u ≢ v × P u ≡ true × P v ≡ true) ⊎ (∀ u v → u ≢ v → P u ≡ true → P v ≡ true → ⊥)
two? P = at (first P) refl
  where
  at : ∀ m → first P ≡ m → (∃₂ λ u v → u ≢ v × P u ≡ true × P v ≡ true) ⊎ (∀ u v → u ≢ v → P u ≡ true → P v ≡ true → ⊥)
  at nothing f = inj₂ λ u v _ pu _ → t≢f (trans (sym pu) (first-nothing P f u))
  at (just u) f = at′ (first (λ x → P x ∧ not (x == u))) refl
    where
    pu : P u ≡ true
    pu = proj₁ (first-just P f)
    at′ : ∀ m → first (λ x → P x ∧ not (x == u)) ≡ m →
          (∃₂ λ u v → u ≢ v × P u ≡ true × P v ≡ true) ⊎ (∀ u v → u ≢ v → P u ≡ true → P v ≡ true → ⊥)
    at′ (just v) f′ = inj₁ (u , v , (λ e → t≢f (trans (sym (∧-r′ (proj₁ (first-just _ f′)))) (cong not (≡u e)))) , pu , ∧-l′ (proj₁ (first-just _ f′)))
      where
      ∧-l′ : ∀ {a b} → a ∧ b ≡ true → a ≡ true
      ∧-l′ {true} _ = refl
      ∧-r′ : ∀ {a b} → a ∧ b ≡ true → b ≡ true
      ∧-r′ {true} e = e
      ≡u : u ≡ v → (v == u) ≡ true
      ≡u refl with u FinP.≟ u
      ... | yes _ = refl
      ... | no ¬p = ⊥-elim (¬p refl)
    at′ nothing f′ = inj₂ λ x y x≢y px py → one x y x≢y px py
      where
      none : ∀ x → P x ≡ true → x ≡ u
      none x px with x FinP.≟ u
      ... | yes e = e
      ... | no x≢u = ⊥-elim (t≢f (trans (sym (both px x≢u)) (first-nothing _ f′ x)))
        where
        both : P x ≡ true → x ≢ u → (P x ∧ not (x == u)) ≡ true
        both e ne with x FinP.≟ u
        ... | yes p = ⊥-elim (ne p)
        ... | no _ = trans (cong (_∧ true) e) refl
      one : ∀ x y → x ≢ y → P x ≡ true → P y ≡ true → ⊥
      one x y x≢y px py = x≢y (trans (none x px) (sym (none y py)))

-- Changing a predicate at two indices raises its count by at most 2.
count-le-2 : ∀ (P Q : Fin k → Bool) u v → (∀ x → x ≢ u → x ≢ v → Q x ≡ P x) → count Q ℕ.≤ count P ℕ.+ 2
count-le-2 P Q u v agree =
  ℕP.≤-trans (step Q R u agreeQR) (ℕP.≤-trans (ℕP.+-monoˡ-≤ 1 (step R P v agreeRP)) (ℕP.≤-reflexive (ℕP.+-assoc (count P) 1 1)))
  where
  R : Fin _ → Bool
  R x = if x == u then P x else Q x
  agreeQR : ∀ x → x ≢ u → Q x ≡ R x
  agreeQR x x≢u = sym (cong (λ b → if b then P x else Q x) (fu x≢u))
    where
    fu : x ≢ u → (x == u) ≡ false
    fu ne with x FinP.≟ u
    ... | yes p = ⊥-elim (ne p)
    ... | no _ = refl
  agreeRP : ∀ x → x ≢ v → R x ≡ P x
  agreeRP x x≢v with x FinP.≟ u
  ... | yes _ = refl
  ... | no x≢u = agree x x≢u x≢v
  step : ∀ (A B : Fin _ → Bool) a → (∀ x → x ≢ a → A x ≡ B x) → count A ℕ.≤ count B ℕ.+ 1
  step A B a ag = ℕP.≤-trans (ℕP.m≤m+n (count A) (ind (B a)))
                    (ℕP.≤-trans (ℕP.≤-reflexive (count-replace A B a ag)) (ℕP.+-monoʳ-≤ (count B) (ind≤1 (A a))))
    where
    ind≤1 : ∀ b → ind b ℕ.≤ 1
    ind≤1 true = ℕP.≤-refl
    ind≤1 false = ℕ.z≤n

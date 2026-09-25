------------------------------------------------------------------------
-- Presentations of groups
--
-- The syllables of the exact synthesis algorithm (Algorithm 2.10), as
-- a function of the data of the pivot column: its index p, its least
-- denominator exponent k and its numerator w ∈ ℤ[i]ⁿ.
--
-- * k = 0: w has a single nonzero entry, a unit u at index m
--   (Corollary 2.3), and the syllable is i_[m]ᵉ followed by X_[m,p]
--   (if m < p), where iᵉ u = 1;
-- * k > 0: with j < ℓ the first two odd entries of w (Lemma 2.5) and
--   q ∈ {0,1} such that w_j ≡ iᑫ w_ℓ (mod 2), the syllable is
--   i_[ℓ]ᑫ followed by K†_[j,ℓ] (Lemma 2.6).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.Column where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _xor_ ; if_then_else_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _<_)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; dec-yes ; dec-no ; dec-true ; dec-false)
import Data.Integer.Solver as ℤSolver

open import Quantum.Synthesis.Ring using (Cplx)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
open import Examples.Groups.Clifford+CS-TwoLevel.Ring
open import Examples.Groups.Clifford+CS-TwoLevel.Lde using (_!_ ; Odd ; Even)
open import Examples.Groups.Clifford+CS-TwoLevel.Search
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics

private
  variable
    n : ℕ
  module ℤS = ℤSolver.+-*-Solver

------------------------------------------------------------------------
-- Odd entries

-- The number of odd entries.
nodd : Vec Z n → ℕ
nodd w = count (λ x → oddᶻ (w ! x))

-- The first odd entry.
firstOdd : Vec Z n → Maybe (Fin n)
firstOdd w = first (λ x → oddᶻ (w ! x))

-- The first odd entry after j.
nextOdd : Fin n → Vec Z n → Maybe (Fin n)
nextOdd j w = first (λ x → does (j FinP.<? x) ∧ oddᶻ (w ! x))

------------------------------------------------------------------------
-- Units and the exponent that normalises them

-- invExp u = e with iᵉ u = 1, for u ∈ {1, i, -1, -i}.
invExp : Z → ℕ
invExp (Cplx (+ 1) (+ 0)) = 0
invExp (Cplx (+ 0) (+ 1)) = 3
invExp (Cplx -[1+ 0 ] (+ 0)) = 2
invExp (Cplx (+ 0) -[1+ 0 ]) = 1
invExp _ = 0

invExp-unit : ∀ t → t ℕ.< 4 → (ⅈᶻ ^ᶻ invExp (ⅈᶻ ^ᶻ t)) ZR.* (ⅈᶻ ^ᶻ t) ≡ ZR.1#
invExp-unit 0 _ = refl
invExp-unit 1 _ = refl
invExp-unit 2 _ = refl
invExp-unit 3 _ = refl
invExp-unit (suc (suc (suc (suc t)))) (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ()))))

invExp-< : ∀ t → t ℕ.< 4 → invExp (ⅈᶻ ^ᶻ t) ℕ.< 4
invExp-< 0 _ = ℕ.s≤s ℕ.z≤n
invExp-< 1 _ = ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))
invExp-< 2 _ = ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))
invExp-< 3 _ = ℕ.s≤s (ℕ.s≤s ℕ.z≤n)
invExp-< (suc (suc (suc (suc t)))) (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ()))))

-- The only unit u with invExp u = 0 is 1.
invExp-0 : ∀ t → t ℕ.< 4 → invExp (ⅈᶻ ^ᶻ t) ≡ 0 → ⅈᶻ ^ᶻ t ≡ ZR.1#
invExp-0 0 _ _ = refl
invExp-0 1 _ ()
invExp-0 2 _ ()
invExp-0 3 _ ()
invExp-0 (suc (suc (suc (suc t)))) (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ())))) _

-- Units are odd.
unit-odd : ∀ t → t ℕ.< 4 → Odd (ⅈᶻ ^ᶻ t)
unit-odd 0 _ = refl
unit-odd 1 _ = refl
unit-odd 2 _ = refl
unit-odd 3 _ = refl
unit-odd (suc (suc (suc (suc t)))) (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ()))))

------------------------------------------------------------------------
-- Residues modulo 2 of odd Gaussian integers
--
-- An odd a + bi has exactly one of a, b odd, so it is ≡ 1 or ≡ i
-- (mod 2) according to the parity of a (Lemma 2.2).  Two odd numbers
-- u, v satisfy u ≡ iᑫ v (mod 2) for q = qOf u v.

private
  re im : Z → ℤ
  re (Cplx a _) = a
  im (Cplx _ b) = b

qOf : Z → Z → ℕ
qOf u v = if oddℤ (re u) xor oddℤ (re v) then 1 else 0

qOf-≤1 : ∀ u v → qOf u v ℕ.≤ 1
qOf-≤1 u v with oddℤ (re u) xor oddℤ (re v)
... | true  = ℕ.s≤s ℕ.z≤n
... | false = ℕ.z≤n

private
  -- A Gaussian integer with both components even is divisible by 2.
  2∣-intro : ∀ a b → oddℤ a ≡ false → oddℤ b ≡ false → 2∣ Cplx a b
  2∣-intro a b ea eb with evenℤ-half a ea | evenℤ-half b eb
  ... | a′ , refl | b′ , refl = Cplx a′ b′ , cong₂ Cplx (lemA a′ b′) (lemB a′ b′)
    where
    open ℤS using (_:+_ ; _:*_ ; :-_ ; _:=_ ; con)
    lemA : ∀ x y → x ℤ.+ x ≡ + 2 ℤ.* x ℤ.+ ℤ.- (+ 0 ℤ.* y)
    lemA = ℤS.solve 2 (λ x y → x :+ x := con (+ 2) :* x :+ :- (con (+ 0) :* y)) refl
    lemB : ∀ x y → y ℤ.+ y ≡ + 2 ℤ.* y ℤ.+ + 0 ℤ.* x
    lemB = ℤS.solve 2 (λ x y → y :+ y := con (+ 2) :* y :+ con (+ 0) :* x) refl

  -- i v, componentwise.
  ⅈ*≡ : ∀ c d → ⅈᶻ ZR.* Cplx c d ≡ Cplx (ℤ.- d) c
  ⅈ*≡ c d = cong₂ Cplx
    (ℤS.solve 2 (λ c d → con (+ 0) :* c :+ :- (con (+ 1) :* d) := :- d) refl c d)
    (ℤS.solve 2 (λ c d → con (+ 0) :* d :+ con (+ 1) :* c := c) refl c d)
    where open ℤS using (_:+_ ; _:*_ ; :-_ ; _:=_ ; con)

  xor-lemma₀ : ∀ oa ob oc od → oa xor ob ≡ true → oc xor od ≡ true → oa xor oc ≡ false →
               ob xor od ≡ false
  xor-lemma₀ true  false true  false _ _ _ = refl
  xor-lemma₀ false true  false true  _ _ _ = refl
  xor-lemma₀ true  true  _ _ () _ _
  xor-lemma₀ false false _ _ () _ _
  xor-lemma₀ _ _ true  true  _ () _
  xor-lemma₀ _ _ false false _ () _
  xor-lemma₀ true  false false true  _ _ ()
  xor-lemma₀ false true  true  false _ _ ()

  xor-lemma₁ : ∀ oa ob oc od → oa xor ob ≡ true → oc xor od ≡ true → oa xor oc ≡ true →
               (oa xor od ≡ false) × (ob xor oc ≡ false)
  xor-lemma₁ true  false false true  _ _ _ = refl , refl
  xor-lemma₁ false true  true  false _ _ _ = refl , refl
  xor-lemma₁ true  true  _ _ () _ _
  xor-lemma₁ false false _ _ () _ _
  xor-lemma₁ _ _ true  true  _ () _
  xor-lemma₁ _ _ false false _ () _
  xor-lemma₁ true  false true  false _ _ ()
  xor-lemma₁ false true  false true  _ _ ()

  odd-sub : ∀ x y → oddℤ (x ℤ.+ ℤ.- y) ≡ oddℤ x xor oddℤ y
  odd-sub x y = trans (oddℤ-+ x (ℤ.- y)) (cong (oddℤ x xor_) (oddℤ-neg y))

-- u ≡ i^(qOf u v) v (mod 2) for odd u and v.
qOf-spec : ∀ u v → Odd u → Odd v → 2∣ (u ZR.- (ⅈᶻ ^ᶻ qOf u v) ZR.* v)
qOf-spec (Cplx a b) (Cplx c d) ou ov
  with oddℤ a xor oddℤ c in eac
... | false = subst (λ z → 2∣ (Cplx a b ZR.- z)) (sym (ZR.*-identityˡ (Cplx c d)))
               (2∣-intro (a ℤ.+ ℤ.- c) (b ℤ.+ ℤ.- d)
                 (trans (odd-sub a c) eac)
                 (trans (odd-sub b d)
                   (xor-lemma₀ (oddℤ a) (oddℤ b) (oddℤ c) (oddℤ d)
                     (trans (sym (oddℤ-+ a b)) ou) (trans (sym (oddℤ-+ c d)) ov) eac)))
... | true = subst (λ z → 2∣ (Cplx a b ZR.- z)) (sym (trans (cong (ZR._* Cplx c d) (ZR.*-identityʳ ⅈᶻ)) (ⅈ*≡ c d)))
               (2∣-intro (a ℤ.+ ℤ.- (ℤ.- d)) (b ℤ.+ ℤ.- c)
                 (trans (odd-sub a (ℤ.- d)) (trans (cong (oddℤ a xor_) (oddℤ-neg d)) (proj₁ facts)))
                 (trans (odd-sub b c) (proj₂ facts)))
  where
  facts = xor-lemma₁ (oddℤ a) (oddℤ b) (oddℤ c) (oddℤ d)
            (trans (sym (oddℤ-+ a b)) ou) (trans (sym (oddℤ-+ c d)) ov) eac

------------------------------------------------------------------------
-- The syllable of a pivot column

-- k = 0: the unit at index m (if found), with invExp e.
unitSyl : (p m : Fin n) → ℕ → Dec (m < p) → Word (Gen n)
unitSyl p m e (yes m<p) = X m p m<p • i m ^ e
unitSyl p m e (no  _)   = i p ^ e

-- k > 0: the first two odd entries j < ℓ.
pairSyl : (w : Vec Z n) (j ℓ : Fin n) → Dec (j < ℓ) → Word (Gen n)
pairSyl w j ℓ (yes j<ℓ) = K† j ℓ j<ℓ • i ℓ ^ qOf (w ! j) (w ! ℓ)
pairSyl w j ℓ (no  _)   = ε

private
  unitStep : Fin n → Vec Z n → Maybe (Fin n) → Word (Gen n)
  unitStep p w (just m) = unitSyl p m (invExp (w ! m)) (m FinP.<? p)
  unitStep p w nothing  = ε

  pairStep₂ : Vec Z n → Fin n → Maybe (Fin n) → Word (Gen n)
  pairStep₂ w j (just ℓ) = pairSyl w j ℓ (j FinP.<? ℓ)
  pairStep₂ w j nothing  = ε

  pairStep : Vec Z n → Maybe (Fin n) → Word (Gen n)
  pairStep w (just j) = pairStep₂ w j (nextOdd j w)
  pairStep w nothing  = ε

sylData : Fin n → ℕ → Vec Z n → Word (Gen n)
sylData p zero    w = unitStep p w (firstOdd w)
sylData p (suc k) w = pairStep w (firstOdd w)

-- The syllable, from the facts that determine it.
sylData-unit< : ∀ {p m : Fin n} (w : Vec Z n) → firstOdd w ≡ just m → (m<p : m < p) →
                sylData p 0 w ≡ X m p m<p • i m ^ invExp (w ! m)
sylData-unit< {p = p} {m} w fo m<p rewrite fo with m FinP.<? p
... | yes _ = refl
... | no ¬m<p = ⊥-elim (¬m<p m<p)

sylData-unit≡ : ∀ {p : Fin n} (w : Vec Z n) → firstOdd w ≡ just p →
                sylData p 0 w ≡ i p ^ invExp (w ! p)
sylData-unit≡ {p = p} w fo rewrite fo with p FinP.<? p
... | yes p<p = ⊥-elim (FinP.<-irrefl refl p<p)
... | no _ = refl

sylData-pair : ∀ {p j ℓ : Fin n} k (w : Vec Z n) → firstOdd w ≡ just j → nextOdd j w ≡ just ℓ →
               (j<ℓ : j < ℓ) → sylData p (suc k) w ≡ K† j ℓ j<ℓ • i ℓ ^ qOf (w ! j) (w ! ℓ)
sylData-pair {j = j} {ℓ} k w fo nx j<ℓ rewrite fo | nx with j FinP.<? ℓ
... | yes _ = refl
... | no ¬j<ℓ = ⊥-elim (¬j<ℓ j<ℓ)

------------------------------------------------------------------------
-- Characterising the first odd entries

firstOdd-char : ∀ (w : Vec Z n) {j} → Odd (w ! j) → (∀ x → x < j → Even (w ! x)) → firstOdd w ≡ just j
firstOdd-char w oj below = first-char (λ x → oddᶻ (w ! x)) oj below

nextOdd-char : ∀ (w : Vec Z n) {j ℓ} → j < ℓ → Odd (w ! ℓ) →
               (∀ x → j < x → x < ℓ → Even (w ! x)) → nextOdd j w ≡ just ℓ
nextOdd-char w {j} {ℓ} j<ℓ oℓ between =
  first-char (λ x → does (j FinP.<? x) ∧ oddᶻ (w ! x))
    (trans (cong (_∧ oddᶻ (w ! ℓ)) (dec-true (j FinP.<? ℓ) j<ℓ)) oℓ) below
  where
  below : ∀ x → x < ℓ → does (j FinP.<? x) ∧ oddᶻ (w ! x) ≡ false
  below x x<ℓ = aux (j FinP.<? x)
    where
    aux : (d : Dec (j < x)) → does d ∧ oddᶻ (w ! x) ≡ false
    aux (yes j<x) = between x j<x x<ℓ
    aux (no  _)   = refl

firstOdd-spec : ∀ (w : Vec Z n) {j} → firstOdd w ≡ just j → Odd (w ! j) × (∀ x → x < j → Even (w ! x))
firstOdd-spec w eq = first-just (λ x → oddᶻ (w ! x)) eq

firstOdd-nothing : ∀ (w : Vec Z n) → firstOdd w ≡ nothing → ∀ x → Even (w ! x)
firstOdd-nothing w eq = first-nothing (λ x → oddᶻ (w ! x)) eq

nextOdd-spec : ∀ (w : Vec Z n) {j ℓ} → nextOdd j w ≡ just ℓ →
               j < ℓ × Odd (w ! ℓ) × (∀ x → j < x → x < ℓ → Even (w ! x))
nextOdd-spec w {j} {ℓ} eq with first-just (λ x → does (j FinP.<? x) ∧ oddᶻ (w ! x)) eq
... | Pℓ , below = proj₁ (split ℓ (j FinP.<? ℓ) Pℓ) , proj₂ (split ℓ (j FinP.<? ℓ) Pℓ) , between
  where
  split : ∀ x (d : Dec (j < x)) → does d ∧ oddᶻ (w ! x) ≡ true → j < x × Odd (w ! x)
  split x (yes j<x) P = j<x , P
  split x (no  _)   ()
  between : ∀ x → j < x → x < ℓ → Even (w ! x)
  between x j<x x<ℓ = aux (j FinP.<? x) (below x x<ℓ)
    where
    aux : (d : Dec (j < x)) → does d ∧ oddᶻ (w ! x) ≡ false → Even (w ! x)
    aux (yes _) e = e
    aux (no ¬j<x) _ = ⊥-elim (¬j<x j<x)

------------------------------------------------------------------------
-- The syllable depends only on the parities and the odd entries

firstOdd-cong : (w w′ : Vec Z n) → (∀ x → oddᶻ (w ! x) ≡ oddᶻ (w′ ! x)) → firstOdd w ≡ firstOdd w′
firstOdd-cong w w′ par = first-cong (λ x → oddᶻ (w ! x)) (λ x → oddᶻ (w′ ! x)) par

nextOdd-cong : (j : Fin n) (w w′ : Vec Z n) → (∀ x → oddᶻ (w ! x) ≡ oddᶻ (w′ ! x)) → nextOdd j w ≡ nextOdd j w′
nextOdd-cong j w w′ par =
  first-cong (λ x → does (j FinP.<? x) ∧ oddᶻ (w ! x)) (λ x → does (j FinP.<? x) ∧ oddᶻ (w′ ! x))
             (λ x → cong (does (j FinP.<? x) ∧_) (par x))

sylData-agree : (p : Fin n) (k : ℕ) (w w′ : Vec Z n) →
                (∀ x → oddᶻ (w ! x) ≡ oddᶻ (w′ ! x)) → (∀ x → Odd (w ! x) → w ! x ≡ w′ ! x) →
                sylData p k w ≡ sylData p k w′
sylData-agree p zero w w′ par agree =
  trans (unit (firstOdd w) refl) (cong (unitStep p w′) (firstOdd-cong w w′ par))
  where
  unit : (r : Maybe (Fin _)) → firstOdd w ≡ r → unitStep p w r ≡ unitStep p w′ r
  unit nothing _ = refl
  unit (just m) e = cong (λ z → unitSyl p m (invExp z) (m FinP.<? p)) (agree m (proj₁ (firstOdd-spec w e)))
sylData-agree p (suc k) w w′ par agree =
  trans (pair (firstOdd w) refl) (cong (pairStep w′) (firstOdd-cong w w′ par))
  where
  syl-agree : ∀ j ℓ → w ! j ≡ w′ ! j → w ! ℓ ≡ w′ ! ℓ → (d : Dec (j < ℓ)) → pairSyl w j ℓ d ≡ pairSyl w′ j ℓ d
  syl-agree j ℓ ej eℓ (yes j<ℓ) = cong₂ (λ a b → K† j ℓ j<ℓ • i ℓ ^ qOf a b) ej eℓ
  syl-agree j ℓ ej eℓ (no _) = refl
  pair : (r : Maybe (Fin _)) → firstOdd w ≡ r → pairStep w r ≡ pairStep w′ r
  pair nothing _ = refl
  pair (just j) e = trans (two (nextOdd j w) refl) (cong (pairStep₂ w′ j) (nextOdd-cong j w w′ par))
    where
    oj : Odd (w ! j)
    oj = proj₁ (firstOdd-spec w e)
    two : (r : Maybe (Fin _)) → nextOdd j w ≡ r → pairStep₂ w j r ≡ pairStep₂ w′ j r
    two nothing _ = refl
    two (just ℓ) e′ = syl-agree j ℓ (agree j oj) (agree ℓ (proj₁ (proj₂ (nextOdd-spec w e′)))) (j FinP.<? ℓ)

------------------------------------------------------------------------
-- The syllable acts at or above the first odd entry

-- Every letter acts on indices ≥ j.
Above : Fin n → Word (Gen n) → Set
Above j [ X-gen a b _ ]ʷ = j Fin.≤ a
Above j [ K-gen a b _ ]ʷ = j Fin.≤ a
Above j [ i-gen a ]ʷ = j Fin.≤ a
Above j ε = ⊤
Above j (u • v) = Above j u × Above j v

Above-^ : ∀ {j : Fin n} (w : Word (Gen n)) → Above j w → ∀ e → Above j (w ^ e)
Above-^ w h zero = tt
Above-^ w h (suc zero) = h
Above-^ w h (suc (suc e)) = h , Above-^ w h (suc e)

sylData-above : (p : Fin n) (k : ℕ) (w : Vec Z n) {j : Fin n} → firstOdd w ≡ just j → j Fin.≤ p →
                Above j (sylData p k w)
sylData-above p zero w {j} fo j≤p = subst (λ r → Above j (unitStep p w r)) (sym fo) (unit (j FinP.<? p))
  where
  unit : (d : Dec (j < p)) → Above j (unitSyl p j (invExp (w ! j)) d)
  unit (yes j<p) = FinP.≤-refl , Above-^ (i j) FinP.≤-refl (invExp (w ! j))
  unit (no ¬j<p) = Above-^ (i p) j≤p (invExp (w ! j))
sylData-above p (suc k) w {j} fo j≤p = subst (λ r → Above j (pairStep w r)) (sym fo) (two (nextOdd j w) refl)
  where
  two : (r : Maybe (Fin _)) → nextOdd j w ≡ r → Above j (pairStep₂ w j r)
  two nothing _ = tt
  two (just ℓ) e = syl (j FinP.<? ℓ)
    where
    syl : (d : Dec (j < ℓ)) → Above j (pairSyl w j ℓ d)
    syl (yes j<ℓ) = Above-^ (K j ℓ j<ℓ) FinP.≤-refl 7 , Above-^ (i ℓ) (ℕP.<⇒≤ j<ℓ) (qOf (w ! j) (w ! ℓ))
    syl (no _) = tt

------------------------------------------------------------------------
-- Multiplying an odd entry by i flips the exponent q

qOf-flip : ∀ u v → Odd u → qOf (ⅈᶻ ZR.* u) v ≡ 1 ℕ.∸ qOf u v
qOf-flip (Cplx a b) v ou = flip (oddℤ a) (oddℤ b) (oddℤ (re v)) refl refl (trans (sym (oddℤ-+ a b)) ou) re-iu
  where
  -- re (i u) = - b, whose parity is that of b.
  re-iu : oddℤ (re (ⅈᶻ ZR.* Cplx a b)) ≡ oddℤ b
  re-iu = trans (cong oddℤ (ℤS.solve 2 (λ x y → con (+ 0) :* x :+ :- (con (+ 1) :* y) := :- y) refl a b))
                (oddℤ-neg b)
    where open ℤS using (_:+_ ; _:*_ ; :-_ ; _:=_ ; con)
  flip : ∀ oa ob ov → oddℤ a ≡ oa → oddℤ b ≡ ob → oa xor ob ≡ true → oddℤ (re (ⅈᶻ ZR.* Cplx a b)) ≡ ob →
         (if oddℤ (re (ⅈᶻ ZR.* Cplx a b)) xor ov then 1 else 0) ≡ 1 ℕ.∸ (if oa xor ov then 1 else 0)
  flip true false true ea eb _ r = cong (λ c → if c xor true then 1 else 0) r
  flip true false false ea eb _ r = cong (λ c → if c xor false then 1 else 0) r
  flip false true true ea eb _ r = cong (λ c → if c xor true then 1 else 0) r
  flip false true false ea eb _ r = cong (λ c → if c xor false then 1 else 0) r
  flip true true ov ea eb () r
  flip false false ov ea eb () r

------------------------------------------------------------------------
-- The exponent q of sums and differences

private
  xor-self : ∀ x → x xor x ≡ false
  xor-self true  = refl
  xor-self false = refl

  xor-xor : ∀ x y z → (x xor y) xor (x xor z) ≡ y xor z
  xor-xor false y z = refl
  xor-xor true true z = refl
  xor-xor true false true = refl
  xor-xor true false false = refl

  xor-comm′ : ∀ x y → x xor y ≡ y xor x
  xor-comm′ true  true  = refl
  xor-comm′ true  false = refl
  xor-comm′ false true  = refl
  xor-comm′ false false = refl

qOf-sym : ∀ u v → qOf u v ≡ qOf v u
qOf-sym u v = cong (λ z → if z then 1 else 0) (xor-comm′ (oddℤ (re u)) (oddℤ (re v)))

-- u + v ≡ u - v (mod 2).
qOf-+- : ∀ u v → qOf (u ZR.+ v) (u ZR.- v) ≡ 0
qOf-+- (Cplx a b) (Cplx c d) =
  cong (λ z → if z then 1 else 0)
    (trans (cong₂ _xor_ (oddℤ-+ a c) (odd-sub a c)) (xor-self (oddℤ a xor oddℤ c)))

-- d + v ≡ i (d + i v) (mod 2) for odd v.
qOf-shift : ∀ d v → Odd v → qOf (d ZR.+ v) (d ZR.+ ⅈᶻ ZR.* v) ≡ 1
qOf-shift (Cplx a b) (Cplx e f) ov =
  trans (cong (λ z → qOf (Cplx a b ZR.+ Cplx e f) (Cplx a b ZR.+ z)) (ⅈ*≡ e f))
    (cong (λ z → if z then 1 else 0)
      (trans (cong₂ _xor_ (oddℤ-+ a e) (odd-sub a f))
        (trans (xor-xor (oddℤ a) (oddℤ e) (oddℤ f)) (trans (sym (oddℤ-+ e f)) ov))))

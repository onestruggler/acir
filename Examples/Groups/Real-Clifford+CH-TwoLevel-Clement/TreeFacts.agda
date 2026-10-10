------------------------------------------------------------------------
-- Presentations of groups
--
-- What the Boolean tests of Tree say: on indices (equality, distinct
-- and onto vectors), on forms (composition, division by powers of √2,
-- the parities of the numbers of odd values), and on ℤ[√2] (the forms
-- of new entries).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.TreeFacts where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; not ; _xor_ ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Decidable using (does)

open import Quantum.Synthesis.Ring using (RootTwo)
open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (oddℕ ; oddℕ-+)
import Examples.Groups.Clifford+CS-TwoLevel.Ring
open import Examples.Groups.Clifford+CS-TwoLevel.Vector using (_!_)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count ; count-drop₂)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (Z ; module ZR ; module ZG ; √2ᶻ ; _^ᶻ_ ; oddᶻ ; rbit ; oddᶻ-+ ; rbit-+ ; _≟ᶻ_ ; √2*≡ ; even⇒δ∣)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Forms
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Subst
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Check
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Tree

open ZG using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

private
  variable
    m r : ℕ

------------------------------------------------------------------------
-- Booleans

∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
∧-l {true} _ = refl

∧-r : ∀ {a b} → a ∧ b ≡ true → b ≡ true
∧-r {true} e = e

not-t : ∀ {a} → not a ≡ true → a ≡ false
not-t {false} _ = refl

t≢f : true ≢ false
t≢f ()

------------------------------------------------------------------------
-- Indices

==-sound : ∀ {i j : Fin m} → (i == j) ≡ true → i ≡ j
==-sound {i = i} {j} e with i FinP.≟ j
... | yes p = p

==-false : ∀ {i j : Fin m} → (i == j) ≡ false → i ≢ j
==-false {i = i} {j} e with i FinP.≟ j
==-false {i = i} {j} () | yes _
... | no ¬p = ¬p

avoid-sound : ∀ (a : Fin m) Q → avoid a Q ≡ true → All (_≢ a) Q
avoid-sound a [] _ = []
avoid-sound a (q ∷ Q) e = ==-false (not-t (∧-l e)) ∷ avoid-sound a Q (∧-r e)

notInV-sound : ∀ {k} (i : Fin m) (v : Vec (Fin m) k) → notInV i v ≡ true → ∀ l → Vec.lookup v l ≢ i
notInV-sound i (j ∷ v) e zero = ==-false (not-t (∧-l e))
notInV-sound i (j ∷ v) e (suc l) = notInV-sound i v (∧-r e) l

distinctV-sound : ∀ {k} (v : Vec (Fin m) k) → distinctV v ≡ true → ∀ {i j} → Vec.lookup v i ≡ Vec.lookup v j → i ≡ j
distinctV-sound (x ∷ v) e {zero} {zero} _ = refl
distinctV-sound (x ∷ v) e {zero} {suc j} eq = ⊥-elim (notInV-sound x v (∧-l e) j (sym eq))
distinctV-sound (x ∷ v) e {suc i} {zero} eq = ⊥-elim (notInV-sound x v (∧-l e) i eq)
distinctV-sound (x ∷ v) e {suc i} {suc j} eq = cong suc (distinctV-sound v (∧-r e) eq)

anyV-sound : ∀ {k} (j : Fin m) (v : Vec (Fin m) k) → anyV j v ≡ true → ∃ λ i → Vec.lookup v i ≡ j
anyV-sound j (x ∷ v) e with x == j in xj
... | true = zero , ==-sound xj
... | false = let (i , p) = anyV-sound j v e in suc i , p

allFin-sound : ∀ {k} (P : Fin k → Bool) → allFin P ≡ true → ∀ j → P j ≡ true
allFin-sound {suc k} P e zero = ∧-l e
allFin-sound {suc k} P e (suc j) = allFin-sound (λ j → P (suc j)) (∧-r e) j

ontoV-sound : ∀ (π : Vec (Fin m) m) → ontoV π ≡ true → ∀ j → ∃ λ i → Vec.lookup π i ≡ j
ontoV-sound π e j = anyV-sound j π (allFin-sound (λ j → anyV j π) e j)

------------------------------------------------------------------------
-- Equality of forms and tags

eqZ-sound : ∀ {x y : Z} → eqZ x y ≡ true → x ≡ y
eqZ-sound {x} {y} e with x ≟ᶻ y
... | yes p = p

eqV-sound : ∀ {k} (xs ys : Vec Z k) → eqV xs ys ≡ true → xs ≡ ys
eqV-sound [] [] _ = refl
eqV-sound (x ∷ xs) (y ∷ ys) e = cong₂ _∷_ (eqZ-sound (∧-l e)) (eqV-sound xs ys (∧-r e))

eqF-sound : ∀ (f g : Form r) → eqF f g ≡ true → f ≡ g
eqF-sound (form k cs) (form l ds) e = cong₂ form (eqZ-sound (∧-l e)) (eqV-sound cs ds (∧-r e))

eqFs-sound : ∀ {k} (fs gs : Vec (Form r) k) → eqFs fs gs ≡ true → fs ≡ gs
eqFs-sound [] [] _ = refl
eqFs-sound (f ∷ fs) (g ∷ gs) e = cong₂ _∷_ (eqF-sound f g (∧-l e)) (eqFs-sound fs gs (∧-r e))

eqMN-sound : ∀ x y → eqMN x y ≡ true → x ≡ y
eqMN-sound nothing nothing _ = refl
eqMN-sound (just a) (just b) e = cong just (ℕP.≡ᵇ⇒≡ a b (subst T (sym e) _))
  where open import Data.Bool.Base using (T)
eqMN-sound nothing (just _) ()
eqMN-sound (just _) nothing ()

eqTags-sound : ∀ {k} (xs ys : Vec (Maybe ℕ) k) → eqTags xs ys ≡ true → xs ≡ ys
eqTags-sound [] [] _ = refl
eqTags-sound (x ∷ xs) (y ∷ ys) e = cong₂ _∷_ (eqMN-sound x y (∧-l e)) (eqTags-sound xs ys (∧-r e))

------------------------------------------------------------------------
-- Forms

-- Zero and sums.
dot-zero : ∀ (ρ : Vec Z r) → dot (Vec.replicate r ZR.0#) ρ ≡ ZR.0#
dot-zero [] = refl
dot-zero (x ∷ ρ) = trans (cong (ZR.0# ZR.* x ZR.+_) (dot-zero ρ)) (ZG.solve 1 (λ x → con ZR.0# :* x :+ con ZR.0# := con ZR.0#) refl x)

⟦zeroF⟧ : ∀ (ρ : Vec Z r) → ⟦ zeroF ⟧ ρ ≡ ZR.0#
⟦zeroF⟧ ρ = trans (cong (ZR.0# ZR.+_) (dot-zero ρ)) (ZG.solve 0 (con ZR.0# :+ con ZR.0# := con ZR.0#) refl)

sumZ : Vec Z m → Z
sumZ [] = ZR.0#
sumZ (x ∷ xs) = x ZR.+ sumZ xs

⟦sumF⟧ : ∀ (fs : Vec (Form r) m) ρ → ⟦ sumF fs ⟧ ρ ≡ sumZ (⟦ fs ⟧ᵛ ρ)
⟦sumF⟧ [] ρ = ⟦zeroF⟧ ρ
⟦sumF⟧ (f ∷ fs) ρ = trans (⟦⊕⟧ f (sumF fs) ρ) (cong (⟦ f ⟧ ρ ZR.+_) (⟦sumF⟧ fs ρ))

-- Composition.
⟦combF⟧ : ∀ {k} (cs : Vec Z k) (τ : Vec (Form r) k) ρ → ⟦ combF cs τ ⟧ ρ ≡ dot cs (⟦ τ ⟧ᵛ ρ)
⟦combF⟧ [] [] ρ = ⟦zeroF⟧ ρ
⟦combF⟧ (c ∷ cs) (t ∷ τ) ρ =
  trans (⟦⊕⟧ (c ⊛ t) (combF cs τ) ρ) (cong₂ ZR._+_ (⟦⊛⟧ c t ρ) (⟦combF⟧ cs τ ρ))

⟦compF⟧ : ∀ {r′} (f : Form r′) (τ : Vec (Form r) r′) ρ → ⟦ compF f τ ⟧ ρ ≡ ⟦ f ⟧ (⟦ τ ⟧ᵛ ρ)
⟦compF⟧ (form k cs) τ ρ =
  trans (⟦⊕⟧ (form k (Vec.replicate _ ZR.0#)) (combF cs τ) ρ)
    (cong₂ ZR._+_ (trans (cong (k ZR.+_) (dot-zero ρ)) (ZG.solve 1 (λ k → k :+ con ZR.0# := k) refl k)) (⟦combF⟧ cs τ ρ))

-- Division by powers of √2.
halfFⁿ-sound : ∀ δ (f : Form r) {g} → halfFⁿ δ f ≡ just g → ∀ ρ → ⟦ f ⟧ ρ ≡ (√2ᶻ ^ᶻ δ) ZR.* ⟦ g ⟧ ρ
halfFⁿ-sound zero f refl ρ = sym (ZR.*-identityˡ (⟦ f ⟧ ρ))
halfFⁿ-sound (suc δ) f e ρ with halfF f in h
halfFⁿ-sound (suc δ) f {g} e ρ | just g′ =
  trans (halfF-sound f h ρ)
    (trans (cong (√2ᶻ ZR.*_) (halfFⁿ-sound δ g′ e ρ)) (sym (ZR.*-assoc √2ᶻ (√2ᶻ ^ᶻ δ) (⟦ g ⟧ ρ))))
halfFⁿ-sound (suc δ) f () ρ | nothing

halfVⁿ-sound : ∀ δ (fs : Vec (Form r) m) {gs} → halfVⁿ δ fs ≡ just gs → ∀ ρ i →
               ⟦ fs ! i ⟧ ρ ≡ (√2ᶻ ^ᶻ δ) ZR.* ⟦ gs ! i ⟧ ρ
halfVⁿ-sound δ (f ∷ fs) e ρ i with halfFⁿ δ f in hf | halfVⁿ δ fs in hfs
halfVⁿ-sound δ (f ∷ fs) refl ρ zero | just g | just gs = halfFⁿ-sound δ f hf ρ
halfVⁿ-sound δ (f ∷ fs) refl ρ (suc i) | just g | just gs = halfVⁿ-sound δ fs hfs ρ i
halfVⁿ-sound δ (f ∷ fs) () ρ i | just g | nothing
halfVⁿ-sound δ (f ∷ fs) () ρ i | nothing | _

------------------------------------------------------------------------
-- Counting odd values

private
  ind : Bool → ℕ
  ind b = if b then 1 else 0

  odd-ind : ∀ b → oddℕ (ind b) ≡ b
  odd-ind true = refl
  odd-ind false = refl

  oddℕ-ind+ : ∀ b n → oddℕ (ind b ℕ.+ n) ≡ b xor oddℕ n
  oddℕ-ind+ b n = trans (oddℕ-+ (ind b) n) (cong (_xor oddℕ n) (odd-ind b))

-- The count over a vector is the count over its indices.
countV-count : ∀ (P : Z → Bool) (e : Vec Z m) → countV P e ≡ count (λ i → P (e ! i))
countV-count P [] = refl
countV-count P (x ∷ e) = cong (ind (P x) ℕ.+_) (countV-count P e)

noddV-countV : ∀ (e : Vec Z m) → noddV e ≡ countV oddᶻ e
noddV-countV [] = refl
noddV-countV (x ∷ e) = cong (ind (oddᶻ x) ℕ.+_) (noddV-countV e)

-- The parity of the number of odd values is that of their sum.
odd-count-sum : ∀ (e : Vec Z m) → oddℕ (countV oddᶻ e) ≡ oddᶻ (sumZ e)
odd-count-sum [] = refl
odd-count-sum (x ∷ e) =
  trans (oddℕ-ind+ (oddᶻ x) (countV oddᶻ e)) (trans (cong (oddᶻ x xor_) (odd-count-sum e)) (sym (oddᶻ-+ x (sumZ e))))

-- When every form is odd or even, the parity of the number of odd
-- values of class 1 is the class of the sum of the odd forms.
odd-count-cls : ∀ (fs : Vec (Form r) m) {c} → noddF fs ≡ just c → ∀ ρ →
                oddℕ (countV (λ z → oddᶻ z ∧ rbit z) (⟦ fs ⟧ᵛ ρ)) ≡ rbit (⟦ oddSumF fs ⟧ ρ)
odd-count-cls [] refl ρ = sym (cong rbit (⟦zeroF⟧ ρ))
odd-count-cls (f ∷ fs) eq ρ with noddF fs in e
odd-count-cls (f ∷ fs) () ρ | nothing
odd-count-cls (f ∷ fs) eq ρ | just c with oddF f in o
... | true =
  trans (oddℕ-ind+ (oddᶻ (⟦ f ⟧ ρ) ∧ rbit (⟦ f ⟧ ρ)) _)
    (trans (cong₂ _xor_ (cong (_∧ rbit (⟦ f ⟧ ρ)) (oddF-sound f o ρ)) (odd-count-cls fs e ρ))
      (trans (sym (rbit-+ (⟦ f ⟧ ρ) (⟦ oddSumF fs ⟧ ρ))) (cong rbit (sym (⟦⊕⟧ f (oddSumF fs) ρ)))))
... | false with evenF f in ev
...   | true = trans (oddℕ-ind+ (oddᶻ (⟦ f ⟧ ρ) ∧ rbit (⟦ f ⟧ ρ)) _)
                 (trans (cong (λ b → (b ∧ rbit (⟦ f ⟧ ρ)) xor oddℕ (countV (λ z → oddᶻ z ∧ rbit z) (⟦ fs ⟧ᵛ ρ))) (evenF-sound f ev ρ))
                        (odd-count-cls fs e ρ))
odd-count-cls (f ∷ fs) () ρ | just c | false | false

-- Class 0 is the rest.
odd-count-cls0 : ∀ (e : Vec Z m) →
                 oddℕ (countV (λ z → oddᶻ z ∧ not (rbit z)) e) ≡ oddℕ (countV oddᶻ e) xor oddℕ (countV (λ z → oddᶻ z ∧ rbit z) e)
odd-count-cls0 [] = refl
odd-count-cls0 (x ∷ e) =
  trans (oddℕ-ind+ (oddᶻ x ∧ not (rbit x)) _)
    (trans (cong ((oddᶻ x ∧ not (rbit x)) xor_) (odd-count-cls0 e))
      (trans (step (oddᶻ x) (rbit x) (oddℕ (countV oddᶻ e)) (oddℕ (countV (λ z → oddᶻ z ∧ rbit z) e)))
        (sym (cong₂ _xor_ (oddℕ-ind+ (oddᶻ x) _) (oddℕ-ind+ (oddᶻ x ∧ rbit x) _)))))
  where
  step : ∀ o c a b → (o ∧ not c) xor (a xor b) ≡ (o xor a) xor ((o ∧ c) xor b)
  step false false a b = refl
  step false true a b = refl
  step true false false false = refl
  step true false false true = refl
  step true false true false = refl
  step true false true true = refl
  step true true false false = refl
  step true true false true = refl
  step true true true false = refl
  step true true true true = refl

-- Two disjoint pairs with odd sums: at least two odd values.
private
  one-odd : ∀ x y → oddᶻ (x ZR.+ y) ≡ true → oddᶻ x ≡ true ⊎ oddᶻ y ≡ true
  one-odd x y e with oddᶻ x in ox | oddᶻ y in oy
  ... | true | _ = inj₁ refl
  ... | false | true = inj₂ refl
  ... | false | false = ⊥-elim (t≢f (trans (sym e) (trans (oddᶻ-+ x y) (cong₂ _xor_ ox oy))))

  odd-of : ∀ (gs : Vec (Form r) m) (a b : Fin m) ρ → oddF (gs ! a ⊕ gs ! b) ≡ true →
           ∃ λ i → (i ≡ a ⊎ i ≡ b) × oddᶻ ((⟦ gs ⟧ᵛ ρ) ! i) ≡ true
  odd-of gs a b ρ e = pick (one-odd (⟦ gs ! a ⟧ ρ) (⟦ gs ! b ⟧ ρ)
                             (trans (sym (cong oddᶻ (⟦⊕⟧ (gs ! a) (gs ! b) ρ))) (oddF-sound (gs ! a ⊕ gs ! b) e ρ)))
    where
    pick : oddᶻ (⟦ gs ! a ⟧ ρ) ≡ true ⊎ oddᶻ (⟦ gs ! b ⟧ ρ) ≡ true →
           ∃ λ i → (i ≡ a ⊎ i ≡ b) × oddᶻ ((⟦ gs ⟧ᵛ ρ) ! i) ≡ true
    pick (inj₁ oa) = a , inj₁ refl , trans (cong oddᶻ (⟦⟧ᵛ-! gs ρ a)) oa
    pick (inj₂ ob) = b , inj₂ refl , trans (cong oddᶻ (⟦⟧ᵛ-! gs ρ b)) ob

  two-count : ∀ (P : Fin m → Bool) i j → i ≢ j → P i ≡ true → P j ≡ true → 2 ℕ.≤ count P
  two-count P i j i≢j Pi Pj =
    subst (2 ℕ.≤_) (sym (count-drop₂ P Q i j i≢j Pi Pj Qi Qj agree)) (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))
    where
    Q : Fin _ → Bool
    Q x = if does (x FinP.≟ i) then false else if does (x FinP.≟ j) then false else P x
    Qi : Q i ≡ false
    Qi with i FinP.≟ i
    ... | yes _ = refl
    ... | no ¬p = ⊥-elim (¬p refl)
    Qj : Q j ≡ false
    Qj with j FinP.≟ i
    ... | yes p = ⊥-elim (i≢j (sym p))
    ... | no _ with j FinP.≟ j
    ...   | yes _ = refl
    ...   | no ¬p = ⊥-elim (¬p refl)
    agree : ∀ x → x ≢ i → x ≢ j → P x ≡ Q x
    agree x xi xj with x FinP.≟ i
    ... | yes p = ⊥-elim (xi p)
    ... | no _ with x FinP.≟ j
    ...   | yes p = ⊥-elim (xj p)
    ...   | no _ = refl

certOK-sound : ∀ (gs : Vec (Form r) m) a b c d → certOK gs a b c d ≡ true → ∀ ρ → 2 ℕ.≤ countV oddᶻ (⟦ gs ⟧ᵛ ρ)
certOK-sound gs a b c d e ρ = go (odd-of gs a b ρ (∧-l {A} (∧-r {D} e))) (odd-of gs c d ρ (∧-r {A} (∧-r {D} e)))
  where
  D = distinctV (a ∷ b ∷ c ∷ d ∷ [])
  A = oddF (gs ! a ⊕ gs ! b)
  vs = ⟦ gs ⟧ᵛ ρ
  inj4 = distinctV-sound (a ∷ b ∷ c ∷ d ∷ []) (∧-l {D} e)
  ac : a ≢ c
  ac p with inj4 {zero} {suc (suc zero)} p
  ... | ()
  ad : a ≢ d
  ad p with inj4 {zero} {suc (suc (suc zero))} p
  ... | ()
  bc : b ≢ c
  bc p with inj4 {suc zero} {suc (suc zero)} p
  ... | ()
  bd : b ≢ d
  bd p with inj4 {suc zero} {suc (suc (suc zero))} p
  ... | ()
  sep : ∀ {i j} → (i ≡ a ⊎ i ≡ b) → (j ≡ c ⊎ j ≡ d) → i ≢ j
  sep (inj₁ refl) (inj₁ refl) p = ac p
  sep (inj₁ refl) (inj₂ refl) p = ad p
  sep (inj₂ refl) (inj₁ refl) p = bc p
  sep (inj₂ refl) (inj₂ refl) p = bd p
  go : (∃ λ i → (i ≡ a ⊎ i ≡ b) × oddᶻ (vs ! i) ≡ true) → (∃ λ j → (j ≡ c ⊎ j ≡ d) × oddᶻ (vs ! j) ≡ true) →
       2 ℕ.≤ countV oddᶻ vs
  go (i , ei , oi) (j , ej , oj) =
    subst (2 ℕ.≤_) (sym (countV-count oddᶻ vs)) (two-count (λ x → oddᶻ (vs ! x)) i j (sep ei ej) oi oj)

------------------------------------------------------------------------
-- ℤ[√2]

-- An odd element is 1 + √2 u.
odd-decomp : ∀ y → oddᶻ y ≡ true → ∃ λ u → y ≡ ZR.1# ZR.+ √2ᶻ ZR.* u
odd-decomp y o = from (even⇒δ∣ (y ZR.- ZR.1#) (trans (oddᶻ-+ y (ZR.- ZR.1#)) (cong (_xor true) o)))
  where
  from : (∃ λ u → y ZR.- ZR.1# ≡ √2ᶻ ZR.* u) → ∃ λ u → y ≡ ZR.1# ZR.+ √2ᶻ ZR.* u
  from (u , eu) = u , trans (ZG.solve 1 (λ y → y := con ZR.1# :+ (y :- con ZR.1#)) refl y) (cong (ZR.1# ZR.+_) eu)

private
  rbit-√2 : ∀ u → rbit (√2ᶻ ZR.* u) ≡ oddᶻ u
  rbit-√2 (RootTwo p q) = cong rbit (√2*≡ p q)

  rbit-√2b : ∀ b → rbit (ZR.- (√2ᶻ ZR.* bitᶻ b)) ≡ b
  rbit-√2b true = refl
  rbit-√2b false = refl

  xor-self : ∀ b → b xor b ≡ false
  xor-self true = refl
  xor-self false = refl

-- An odd element of class b is 1 + √2 b + 2 v.
cls-decomp : ∀ y b → oddᶻ y ≡ true → rbit y ≡ b →
             ∃ λ v → y ≡ ZR.1# ZR.+ √2ᶻ ZR.* bitᶻ b ZR.+ (ZR.1# ZR.+ ZR.1#) ZR.* v
cls-decomp y b o c = go (odd-decomp y o)
  where
  go : (∃ λ u → y ≡ ZR.1# ZR.+ √2ᶻ ZR.* u) → ∃ λ v → y ≡ ZR.1# ZR.+ √2ᶻ ZR.* bitᶻ b ZR.+ (ZR.1# ZR.+ ZR.1#) ZR.* v
  go (u , eu) = fin (even⇒δ∣ (u ZR.- bitᶻ b) ue)
    where
    rbit-u : rbit (√2ᶻ ZR.* u) ≡ b
    rbit-u = trans (sym (trans (cong rbit eu) (rbit-+ ZR.1# (√2ᶻ ZR.* u)))) c
    eq1 : √2ᶻ ZR.* (u ZR.- bitᶻ b) ≡ √2ᶻ ZR.* u ZR.+ ZR.- (√2ᶻ ZR.* bitᶻ b)
    eq1 = ZG.solve 2 (λ u c → con √2ᶻ :* (u :- c) := con √2ᶻ :* u :+ :- (con √2ᶻ :* c)) refl u (bitᶻ b)
    ue : oddᶻ (u ZR.- bitᶻ b) ≡ false
    ue = trans (sym (rbit-√2 (u ZR.- bitᶻ b)))
           (trans (cong rbit eq1)
             (trans (rbit-+ (√2ᶻ ZR.* u) (ZR.- (√2ᶻ ZR.* bitᶻ b))) (trans (cong₂ _xor_ rbit-u (rbit-√2b b)) (xor-self b))))
    fin : (∃ λ v → u ZR.- bitᶻ b ≡ √2ᶻ ZR.* v) → ∃ λ v → y ≡ ZR.1# ZR.+ √2ᶻ ZR.* bitᶻ b ZR.+ (ZR.1# ZR.+ ZR.1#) ZR.* v
    fin (v , ev) = v , trans eu (trans (cong (λ t → ZR.1# ZR.+ √2ᶻ ZR.* t) (ZG.solve 2 (λ u c → u := c :+ (u :- c)) refl u (bitᶻ b)))
                              (trans (cong (λ t → ZR.1# ZR.+ √2ᶻ ZR.* (bitᶻ b ZR.+ t)) ev)
                                (ZG.solve 2 (λ c v → con ZR.1# :+ con √2ᶻ :* (c :+ con √2ᶻ :* v)
                                                    := con ZR.1# :+ con √2ᶻ :* c :+ (con ZR.1# :+ con ZR.1#) :* v) refl (bitᶻ b) v)))

-- √2^δ times an odd element is not 0.
private
  rt-a : ∀ {a b c d : ℤ} → RootTwo a b ≡ RootTwo c d → a ≡ c
  rt-a refl = refl

  rt-b : ∀ {a b c d : ℤ} → RootTwo a b ≡ RootTwo c d → b ≡ d
  rt-b refl = refl

  double0 : ∀ q → q ℤ.+ q ≡ + 0 → q ≡ + 0
  double0 (+ zero) _ = refl
  double0 (+ suc q) ()
  double0 -[1+ q ] ()

√2-cancel : ∀ w → √2ᶻ ZR.* w ≡ ZR.0# → w ≡ ZR.0#
√2-cancel (RootTwo p q) e = cong₂ RootTwo (rt-b p0) (double0 q (rt-a p0))
  where
  p0 = trans (sym (√2*≡ p q)) e

√2-inj : ∀ a b → √2ᶻ ZR.* a ≡ √2ᶻ ZR.* b → a ≡ b
√2-inj a b e = trans (ZG.solve 2 (λ a b → a := b :+ (a :- b)) refl a b)
                 (trans (cong (b ZR.+_) (√2-cancel (a ZR.- b) (trans (ZG.solve 2 (λ a b → con √2ᶻ :* (a :- b) := con √2ᶻ :* a :- con √2ᶻ :* b) refl a b)
                                                                  (trans (cong (ZR._- (√2ᶻ ZR.* b)) e) (ZG.solve 1 (λ t → t :- t := con ZR.0#) refl (√2ᶻ ZR.* b))))))
                   (ZG.solve 1 (λ b → b :+ con ZR.0# := b) refl b))

pow-cancel : ∀ δ y y′ → (√2ᶻ ^ᶻ δ) ZR.* y ≡ (√2ᶻ ^ᶻ δ) ZR.* y′ → y ≡ y′
pow-cancel zero y y′ e = trans (sym (ZR.*-identityˡ y)) (trans e (ZR.*-identityˡ y′))
pow-cancel (suc δ) y y′ e =
  pow-cancel δ y y′ (√2-inj _ _ (trans (sym (ZR.*-assoc √2ᶻ (√2ᶻ ^ᶻ δ) y)) (trans e (ZR.*-assoc √2ᶻ (√2ᶻ ^ᶻ δ) y′))))

pow-odd-≢0 : ∀ δ y → oddᶻ y ≡ true → (√2ᶻ ^ᶻ δ) ZR.* y ≢ ZR.0#
pow-odd-≢0 zero y o e = t≢f (trans (sym o) (cong oddᶻ (trans (sym (ZR.*-identityˡ y)) e)))
pow-odd-≢0 (suc δ) y o e = pow-odd-≢0 δ y o (√2-cancel ((√2ᶻ ^ᶻ δ) ZR.* y) (trans (sym (ZR.*-assoc √2ᶻ (√2ᶻ ^ᶻ δ) y)) e))

-- The new entries' forms.
⟦newF⟧ : ∀ δ b v (ρ : Vec Z r) →
         ⟦ newF δ (just b) ⟧ (v ∷ ρ) ≡ (√2ᶻ ^ᶻ δ) ZR.* (ZR.1# ZR.+ √2ᶻ ZR.* bitᶻ b ZR.+ (ZR.1# ZR.+ ZR.1#) ZR.* v)
⟦newF⟧ δ b v ρ = trans (⟦⊛⟧ (√2ᶻ ^ᶻ δ) (form (ZR.1# ZR.+ √2ᶻ ZR.* bitᶻ b) ((ZR.1# ZR.+ ZR.1#) ∷ Vec.replicate _ ZR.0#)) (v ∷ ρ)) (cong ((√2ᶻ ^ᶻ δ) ZR.*_)
  (trans (cong (λ t → ZR.1# ZR.+ √2ᶻ ZR.* bitᶻ b ZR.+ ((ZR.1# ZR.+ ZR.1#) ZR.* v ZR.+ t)) (dot-zero ρ))
    (ZG.solve 2 (λ k t → k :+ (t :+ con ZR.0#) := k :+ t) refl (ZR.1# ZR.+ √2ᶻ ZR.* bitᶻ b) ((ZR.1# ZR.+ ZR.1#) ZR.* v))))

⟦newF₀⟧ : ∀ δ v (ρ : Vec Z r) → ⟦ newF δ nothing ⟧ (v ∷ ρ) ≡ (√2ᶻ ^ᶻ δ) ZR.* (ZR.1# ZR.+ √2ᶻ ZR.* v)
⟦newF₀⟧ δ v ρ = trans (⟦⊛⟧ (√2ᶻ ^ᶻ δ) (form ZR.1# (√2ᶻ ∷ Vec.replicate _ ZR.0#)) (v ∷ ρ)) (cong ((√2ᶻ ^ᶻ δ) ZR.*_)
  (trans (cong (λ t → ZR.1# ZR.+ (√2ᶻ ZR.* v ZR.+ t)) (dot-zero ρ))
    (ZG.solve 1 (λ t → con ZR.1# :+ (t :+ con ZR.0#) := con ZR.1# :+ t) refl (√2ᶻ ZR.* v))))

-- Halving √2 times an element.
halfZ-√2 : ∀ y → halfZ (√2ᶻ ZR.* y) ≡ just y
halfZ-√2 y = go (halfZ-even (√2ᶻ ZR.* y) (oddᶻ-*′ y))
  where
  oddᶻ-*′ : ∀ y → oddᶻ (√2ᶻ ZR.* y) ≡ false
  oddᶻ-*′ (RootTwo p q) = cong oddᶻ (√2*≡ p q) ∙ oddℤ-double′ q
    where
    _∙_ = trans
    oddℤ-double′ : ∀ q → oddᶻ (RootTwo (q ℤ.+ q) p) ≡ false
    oddℤ-double′ q = Examples.Groups.Clifford+CS-TwoLevel.Ring.oddℤ-double q
  go : (∃ λ y′ → halfZ (√2ᶻ ZR.* y) ≡ just y′) → halfZ (√2ᶻ ZR.* y) ≡ just y
  go (y′ , h) = trans h (cong just (sym (√2-inj y y′ (halfZ-sound (√2ᶻ ZR.* y) h))))

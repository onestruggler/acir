------------------------------------------------------------------------
-- Presentations of groups
--
-- Linear forms over ℤ[√2]: a constant and a coefficient for each of r
-- variables.  The column computations along a route are done on forms,
-- coefficient by coefficient, so that one computation covers every
-- value of the variables (Route).
--
-- * halfF: a form all of whose coefficients √2 divides, divided by √2;
-- * evenF, oddF: every value is even, odd (the rational part of every
--   coefficient but the constant is even);
-- * clsF: the residue class of an odd form, when 2 divides every
--   coefficient but the constant.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Forms where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; _xor_ ; not)
open import Data.Integer.Base as ℤ using (ℤ)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (∃ ; _,_ ; proj₁ ; proj₂)
open import Data.Empty using (⊥-elim)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality

open import Quantum.Synthesis.Ring using (RootTwo)
open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (oddℤ ; oddℤ-+ ; oddℤ-* ; evenℤ-half)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (Z ; module ZR ; module ZG ; √2ᶻ ; oddᶻ ; rbit ; oddᶻ-+ ; oddᶻ-* ; rbit-+ ; √2*≡)

private
  variable
    r : ℕ

open ZG using (_:+_ ; _:*_ ; :-_ ; _:=_ ; con)

------------------------------------------------------------------------
-- Forms and their values

record Form (r : ℕ) : Set where
  constructor form
  field
    k₀ : Z
    co : Vec Z r

open Form public

dot : Vec Z r → Vec Z r → Z
dot [] [] = ZR.0#
dot (c ∷ cs) (x ∷ xs) = c ZR.* x ZR.+ dot cs xs

⟦_⟧ : Form r → Vec Z r → Z
⟦ form k cs ⟧ ρ = k ZR.+ dot cs ρ

------------------------------------------------------------------------
-- Sums and negation

infixl 6 _⊕_ _⊖_

_⊕_ : Form r → Form r → Form r
form k cs ⊕ form l ds = form (k ZR.+ l) (Vec.zipWith ZR._+_ cs ds)

⊝ : Form r → Form r
⊝ (form k cs) = form (ZR.- k) (Vec.map ZR.-_ cs)

_⊖_ : Form r → Form r → Form r
f ⊖ g = f ⊕ ⊝ g

private
  dot-+ : (cs ds ρ : Vec Z r) → dot (Vec.zipWith ZR._+_ cs ds) ρ ≡ dot cs ρ ZR.+ dot ds ρ
  dot-+ [] [] [] = refl
  dot-+ (c ∷ cs) (d ∷ ds) (x ∷ ρ) =
    trans (cong ((c ZR.+ d) ZR.* x ZR.+_) (dot-+ cs ds ρ))
      (ZG.solve 5 (λ c d x s t → (c :+ d) :* x :+ (s :+ t) := (c :* x :+ s) :+ (d :* x :+ t))
        refl c d x (dot cs ρ) (dot ds ρ))

  dot-neg : (cs ρ : Vec Z r) → dot (Vec.map ZR.-_ cs) ρ ≡ ZR.- dot cs ρ
  dot-neg [] [] = refl
  dot-neg (c ∷ cs) (x ∷ ρ) =
    trans (cong ((ZR.- c) ZR.* x ZR.+_) (dot-neg cs ρ))
      (ZG.solve 3 (λ c x s → (:- c) :* x :+ (:- s) := :- (c :* x :+ s)) refl c x (dot cs ρ))

⟦⊕⟧ : ∀ (f g : Form r) ρ → ⟦ f ⊕ g ⟧ ρ ≡ ⟦ f ⟧ ρ ZR.+ ⟦ g ⟧ ρ
⟦⊕⟧ (form k cs) (form l ds) ρ =
  trans (cong ((k ZR.+ l) ZR.+_) (dot-+ cs ds ρ))
    (ZG.solve 4 (λ k l s t → (k :+ l) :+ (s :+ t) := (k :+ s) :+ (l :+ t)) refl k l (dot cs ρ) (dot ds ρ))

⟦⊝⟧ : ∀ (f : Form r) ρ → ⟦ ⊝ f ⟧ ρ ≡ ZR.- ⟦ f ⟧ ρ
⟦⊝⟧ (form k cs) ρ =
  trans (cong ((ZR.- k) ZR.+_) (dot-neg cs ρ)) (ZG.solve 2 (λ k s → (:- k) :+ (:- s) := :- (k :+ s)) refl k (dot cs ρ))

⟦⊖⟧ : ∀ (f g : Form r) ρ → ⟦ f ⊖ g ⟧ ρ ≡ ⟦ f ⟧ ρ ZR.- ⟦ g ⟧ ρ
⟦⊖⟧ f g ρ = trans (⟦⊕⟧ f (⊝ g) ρ) (cong (⟦ f ⟧ ρ ZR.+_) (⟦⊝⟧ g ρ))

------------------------------------------------------------------------
-- Division by √2

-- x / √2, when the rational part of x is even.
private
  halfZ′ : (a b : ℤ) (o : Bool) → oddℤ a ≡ o → Maybe Z
  halfZ′ a b true _ = nothing
  halfZ′ a b false e = just (RootTwo b (proj₁ (evenℤ-half a e)))

  halfZ′-sound : (a b : ℤ) (o : Bool) (e : oddℤ a ≡ o) {y : Z} → halfZ′ a b o e ≡ just y → RootTwo a b ≡ √2ᶻ ZR.* y
  halfZ′-sound a b true _ ()
  halfZ′-sound a b false e refl =
    trans (cong (λ x → RootTwo x b) (proj₂ (evenℤ-half a e))) (sym (√2*≡ b (proj₁ (evenℤ-half a e))))

halfZ : Z → Maybe Z
halfZ (RootTwo a b) = halfZ′ a b (oddℤ a) refl

halfZ-sound : ∀ x {y} → halfZ x ≡ just y → x ≡ √2ᶻ ZR.* y
halfZ-sound (RootTwo a b) = halfZ′-sound a b (oddℤ a) refl

-- An odd element does not halve.
halfZ-odd : ∀ x → oddᶻ x ≡ true → halfZ x ≡ nothing
halfZ-odd (RootTwo a b) e = go (oddℤ a) refl e
  where
  go : ∀ o (eo : oddℤ a ≡ o) → oddℤ a ≡ true → halfZ′ a b o eo ≡ nothing
  go true eo _ = refl
  go false eo e′ = ⊥-elim (t≢f (trans (sym e′) eo))
    where
    t≢f : true ≢ false
    t≢f ()

-- An even element halves.
halfZ-even : ∀ x → oddᶻ x ≡ false → ∃ λ y → halfZ x ≡ just y
halfZ-even (RootTwo a b) e = go (oddℤ a) refl e
  where
  go : ∀ o (eo : oddℤ a ≡ o) → oddℤ a ≡ false → ∃ λ y → halfZ′ a b o eo ≡ just y
  go false eo _ = _ , refl
  go true eo e′ = ⊥-elim (t≢f (trans (sym eo) e′))
    where
    t≢f : true ≢ false
    t≢f ()

halfV : Vec Z r → Maybe (Vec Z r)
halfV [] = just []
halfV (c ∷ cs) with halfZ c | halfV cs
... | just d | just ds = just (d ∷ ds)
... | _ | _ = nothing

halfF : Form r → Maybe (Form r)
halfF (form k cs) with halfZ k | halfV cs
... | just l | just ds = just (form l ds)
... | _ | _ = nothing

private
  halfV-sound : (cs : Vec Z r) {ds : Vec Z r} → halfV cs ≡ just ds → ∀ ρ → dot cs ρ ≡ √2ᶻ ZR.* dot ds ρ
  halfV-sound [] refl [] = refl
  halfV-sound (c ∷ cs) eq (x ∷ ρ) with halfZ c in hc | halfV cs in hcs
  halfV-sound (c ∷ cs) refl (x ∷ ρ) | just d | just ds =
    trans (cong₂ (λ u v → u ZR.* x ZR.+ v) (halfZ-sound c hc) (halfV-sound cs hcs ρ))
      (ZG.solve 3 (λ d x t → con √2ᶻ :* d :* x :+ con √2ᶻ :* t := con √2ᶻ :* (d :* x :+ t))
        refl d x (dot ds ρ))
  halfV-sound (c ∷ cs) () (x ∷ ρ) | just d | nothing
  halfV-sound (c ∷ cs) () (x ∷ ρ) | nothing | _

halfF-sound : (f : Form r) {g : Form r} → halfF f ≡ just g → ∀ ρ → ⟦ f ⟧ ρ ≡ √2ᶻ ZR.* ⟦ g ⟧ ρ
halfF-sound (form k cs) eq ρ with halfZ k in hk | halfV cs in hcs
halfF-sound (form k cs) refl ρ | just l | just ds =
  trans (cong₂ ZR._+_ (halfZ-sound k hk) (halfV-sound cs hcs ρ))
    (ZG.solve 2 (λ l t → con √2ᶻ :* l :+ con √2ᶻ :* t := con √2ᶻ :* (l :+ t)) refl l (dot ds ρ))
halfF-sound (form k cs) () ρ | just l | nothing
halfF-sound (form k cs) () ρ | nothing | _

------------------------------------------------------------------------
-- Parities

-- 2 divides x (both parts even).
twoZ : Z → Bool
twoZ (RootTwo a b) = not (oddℤ a) ∧ not (oddℤ b)

evenV : Vec Z r → Bool
evenV [] = true
evenV (c ∷ cs) = not (oddᶻ c) ∧ evenV cs

twoV : Vec Z r → Bool
twoV [] = true
twoV (c ∷ cs) = twoZ c ∧ twoV cs

-- Every value even; every value odd.
evenF : Form r → Bool
evenF (form k cs) = not (oddᶻ k) ∧ evenV cs

oddF : Form r → Bool
oddF (form k cs) = oddᶻ k ∧ evenV cs

-- The residue class of every value, when 2 divides the coefficients.
clsF : Form r → Maybe Bool
clsF (form k cs) with twoV cs
... | true = just (rbit k)
... | false = nothing

private
  ∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧-l {true} _ = refl
  ∧-l {false} ()

  ∧-r : ∀ {a b} → a ∧ b ≡ true → b ≡ true
  ∧-r {true} {true} _ = refl
  ∧-r {true} {false} ()
  ∧-r {false} ()

  not-true : ∀ {a} → not a ≡ true → a ≡ false
  not-true {false} _ = refl
  not-true {true} ()

  xor-false : ∀ b → b xor false ≡ b
  xor-false true = refl
  xor-false false = refl

  odd-dot : (cs ρ : Vec Z r) → evenV cs ≡ true → oddᶻ (dot cs ρ) ≡ false
  odd-dot [] [] _ = refl
  odd-dot (c ∷ cs) (x ∷ ρ) e =
    trans (oddᶻ-+ (c ZR.* x) (dot cs ρ))
      (cong₂ _xor_ (trans (oddᶻ-* c x) (cong (_∧ oddᶻ x) (not-true (∧-l {not (oddᶻ c)} {evenV cs} e))))
                   (odd-dot cs ρ (∧-r {not (oddᶻ c)} {evenV cs} e)))

  rbit-two : ∀ c x → twoZ c ≡ true → rbit (c ZR.* x) ≡ false
  rbit-two (RootTwo a b) (RootTwo s t) e =
    trans (oddℤ-+ (a ℤ.* t) (s ℤ.* b))
      (cong₂ _xor_ (trans (oddℤ-* a t) (cong (_∧ oddℤ t) (not-true (∧-l {not (oddℤ a)} {not (oddℤ b)} e))))
                   (trans (oddℤ-* s b) (trans (cong (oddℤ s ∧_) (not-true (∧-r {not (oddℤ a)} {not (oddℤ b)} e))) (∧-false (oddℤ s)))))
    where
    ∧-false : ∀ b → b ∧ false ≡ false
    ∧-false true = refl
    ∧-false false = refl

  rbit-dot : (cs ρ : Vec Z r) → twoV cs ≡ true → rbit (dot cs ρ) ≡ false
  rbit-dot [] [] _ = refl
  rbit-dot (c ∷ cs) (x ∷ ρ) e =
    trans (rbit-+ (c ZR.* x) (dot cs ρ))
      (cong₂ _xor_ (rbit-two c x (∧-l {twoZ c} {twoV cs} e)) (rbit-dot cs ρ (∧-r {twoZ c} {twoV cs} e)))

evenF-sound : (f : Form r) → evenF f ≡ true → ∀ ρ → oddᶻ (⟦ f ⟧ ρ) ≡ false
evenF-sound (form k cs) e ρ =
  trans (oddᶻ-+ k (dot cs ρ))
    (cong₂ _xor_ (not-true (∧-l {not (oddᶻ k)} {evenV cs} e)) (odd-dot cs ρ (∧-r {not (oddᶻ k)} {evenV cs} e)))

oddF-sound : (f : Form r) → oddF f ≡ true → ∀ ρ → oddᶻ (⟦ f ⟧ ρ) ≡ true
oddF-sound (form k cs) e ρ =
  trans (oddᶻ-+ k (dot cs ρ))
    (trans (cong₂ _xor_ (∧-l {oddᶻ k} {evenV cs} e) (odd-dot cs ρ (∧-r {oddᶻ k} {evenV cs} e))) refl)

clsF-sound : (f : Form r) {b : Bool} → clsF f ≡ just b → ∀ ρ → rbit (⟦ f ⟧ ρ) ≡ b
clsF-sound (form k cs) eq ρ with twoV cs in t
clsF-sound (form k cs) refl ρ | true = trans (rbit-+ k (dot cs ρ)) (trans (cong (rbit k xor_) (rbit-dot cs ρ t)) (xor-false (rbit k)))
clsF-sound (form k cs) () ρ | false

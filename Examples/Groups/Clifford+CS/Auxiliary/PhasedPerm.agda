------------------------------------------------------------------------
-- Presentations of groups
--
-- Phased permutations, a model of the K-free fragment
--
-- Every letter of P′ but the K one denotes a *phased permutation* of
-- the N basis indices: a permutation together with a power of i on
-- each index.  Reading a word that way is a monoid homomorphism, and
-- the rules of `Fragment` hold in it, so its congruence is interpreted
-- here.  That is what will make the normal form unique: two normal
-- forms with the same semantics have the same phased permutation, and
-- a normal form is recoverable from it.
--
-- The whole of the P′ theory is *not* interpreted here, and cannot
-- be: a K pair squared is a phase word, which no phased-permutation
-- reading of a K letter makes true.
--
-- After `SignedPerm` of Real-Clifford+CH, with the ℤ/4 phases `Ph` for
-- the Boolean signs; the letter and permutation machinery is carried
-- over unchanged, and only the phase arithmetic is new.  The rules
-- about phase pairs alone are proved pointwise, by case analysis on
-- where the index sits; the rules with a letter in them go through
-- `prod-L` and `conj-L`, as Clément's do.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm (N : ℕ) where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (suc ; _<_)
open import Data.Nat.Properties using (n≮n ; <-trans ; n<1+n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx ; kk)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment

private
  W : Set
  W = Word (GenP N)

------------------------------------------------------------------------
-- The phases: ℤ/4, as its own data type
--
-- Everything is decided by cases, so every lemma is a table of refl
-- clauses and the conversion checker never normalises an open sum.

data Ph : Set where
  p0 p1 p2 p3 : Ph

infixl 6 _+ᵖ_
_+ᵖ_ : Ph → Ph → Ph
p0 +ᵖ y  = y
p1 +ᵖ p0 = p1
p1 +ᵖ p1 = p2
p1 +ᵖ p2 = p3
p1 +ᵖ p3 = p0
p2 +ᵖ p0 = p2
p2 +ᵖ p1 = p3
p2 +ᵖ p2 = p0
p2 +ᵖ p3 = p1
p3 +ᵖ p0 = p3
p3 +ᵖ p1 = p0
p3 +ᵖ p2 = p1
p3 +ᵖ p3 = p2

+ᵖ-idʳ : ∀ x → x +ᵖ p0 ≡ x
+ᵖ-idʳ p0 = Eq.refl
+ᵖ-idʳ p1 = Eq.refl
+ᵖ-idʳ p2 = Eq.refl
+ᵖ-idʳ p3 = Eq.refl

+ᵖ-comm : ∀ x y → x +ᵖ y ≡ y +ᵖ x
+ᵖ-comm p0 y  = Eq.sym (+ᵖ-idʳ y)
+ᵖ-comm p1 p0 = Eq.refl
+ᵖ-comm p1 p1 = Eq.refl
+ᵖ-comm p1 p2 = Eq.refl
+ᵖ-comm p1 p3 = Eq.refl
+ᵖ-comm p2 p0 = Eq.refl
+ᵖ-comm p2 p1 = Eq.refl
+ᵖ-comm p2 p2 = Eq.refl
+ᵖ-comm p2 p3 = Eq.refl
+ᵖ-comm p3 p0 = Eq.refl
+ᵖ-comm p3 p1 = Eq.refl
+ᵖ-comm p3 p2 = Eq.refl
+ᵖ-comm p3 p3 = Eq.refl

+ᵖ-assoc : ∀ x y z → (x +ᵖ y) +ᵖ z ≡ x +ᵖ (y +ᵖ z)
+ᵖ-assoc p0 y z = Eq.refl
+ᵖ-assoc p1 p0 z = Eq.refl
+ᵖ-assoc p1 p1 p0 = Eq.refl
+ᵖ-assoc p1 p1 p1 = Eq.refl
+ᵖ-assoc p1 p1 p2 = Eq.refl
+ᵖ-assoc p1 p1 p3 = Eq.refl
+ᵖ-assoc p1 p2 p0 = Eq.refl
+ᵖ-assoc p1 p2 p1 = Eq.refl
+ᵖ-assoc p1 p2 p2 = Eq.refl
+ᵖ-assoc p1 p2 p3 = Eq.refl
+ᵖ-assoc p1 p3 p0 = Eq.refl
+ᵖ-assoc p1 p3 p1 = Eq.refl
+ᵖ-assoc p1 p3 p2 = Eq.refl
+ᵖ-assoc p1 p3 p3 = Eq.refl
+ᵖ-assoc p2 p0 z = Eq.refl
+ᵖ-assoc p2 p1 p0 = Eq.refl
+ᵖ-assoc p2 p1 p1 = Eq.refl
+ᵖ-assoc p2 p1 p2 = Eq.refl
+ᵖ-assoc p2 p1 p3 = Eq.refl
+ᵖ-assoc p2 p2 p0 = Eq.refl
+ᵖ-assoc p2 p2 p1 = Eq.refl
+ᵖ-assoc p2 p2 p2 = Eq.refl
+ᵖ-assoc p2 p2 p3 = Eq.refl
+ᵖ-assoc p2 p3 p0 = Eq.refl
+ᵖ-assoc p2 p3 p1 = Eq.refl
+ᵖ-assoc p2 p3 p2 = Eq.refl
+ᵖ-assoc p2 p3 p3 = Eq.refl
+ᵖ-assoc p3 p0 z = Eq.refl
+ᵖ-assoc p3 p1 p0 = Eq.refl
+ᵖ-assoc p3 p1 p1 = Eq.refl
+ᵖ-assoc p3 p1 p2 = Eq.refl
+ᵖ-assoc p3 p1 p3 = Eq.refl
+ᵖ-assoc p3 p2 p0 = Eq.refl
+ᵖ-assoc p3 p2 p1 = Eq.refl
+ᵖ-assoc p3 p2 p2 = Eq.refl
+ᵖ-assoc p3 p2 p3 = Eq.refl
+ᵖ-assoc p3 p3 p0 = Eq.refl
+ᵖ-assoc p3 p3 p1 = Eq.refl
+ᵖ-assoc p3 p3 p2 = Eq.refl
+ᵖ-assoc p3 p3 p3 = Eq.refl

-- Four of anything vanish.
+ᵖ-4 : ∀ x → x +ᵖ (x +ᵖ (x +ᵖ x)) ≡ p0
+ᵖ-4 p0 = Eq.refl
+ᵖ-4 p1 = Eq.refl
+ᵖ-4 p2 = Eq.refl
+ᵖ-4 p3 = Eq.refl

-- A vanishing sum vanishes the other way round.
+ᵖ-flip0 : ∀ x y → x +ᵖ y ≡ p0 → y +ᵖ x ≡ p0
+ᵖ-flip0 x y e = Eq.trans (+ᵖ-comm y x) e

------------------------------------------------------------------------
-- Phased permutations

record PP : Set where
  constructor pp[_,_]
  field
    ph  : Fin N → Ph
    prm : Fin N → Fin N

open PP public

-- Pointwise equality of both components.
infix 4 _≐_
record _≐_ (f g : PP) : Set where
  constructor eqv
  field
    ph≡  : ∀ i → ph f i ≡ ph g i
    prm≡ : ∀ i → prm f i ≡ prm g i

open _≐_ public

idPP : PP
idPP = pp[ (λ _ → p0) , (λ i → i) ]

-- Composition, the left factor acting first.
infixr 7 _⊙_
_⊙_ : PP → PP → PP
f ⊙ g = pp[ (λ i → ph f i +ᵖ ph g (prm f i)) , (λ i → prm g (prm f i)) ]

≐-refl : ∀ {f} → f ≐ f
≐-refl = eqv (λ _ → Eq.refl) (λ _ → Eq.refl)

≐-sym : ∀ {f g} → f ≐ g → g ≐ f
≐-sym e = eqv (λ i → Eq.sym (ph≡ e i)) (λ i → Eq.sym (prm≡ e i))

≐-trans : ∀ {f g h} → f ≐ g → g ≐ h → f ≐ h
≐-trans e e′ = eqv (λ i → Eq.trans (ph≡ e i) (ph≡ e′ i))
                   (λ i → Eq.trans (prm≡ e i) (prm≡ e′ i))

≐-isEquivalence : IsEquivalence _≐_
≐-isEquivalence = record { refl = ≐-refl ; sym = ≐-sym ; trans = ≐-trans }

PP-setoid : Setoid _ _
PP-setoid = record { Carrier = PP ; _≈_ = _≐_ ; isEquivalence = ≐-isEquivalence }

open import Relation.Binary.Reasoning.Setoid PP-setoid public

⊙-cong : ∀ {f f′ g g′} → f ≐ f′ → g ≐ g′ → f ⊙ g ≐ f′ ⊙ g′
⊙-cong {f} {f′} {g} {g′} e e′ = eqv s p
  where
  s : ∀ i → ph f i +ᵖ ph g (prm f i) ≡ ph f′ i +ᵖ ph g′ (prm f′ i)
  s i = Eq.cong₂ _+ᵖ_ (ph≡ e i)
                      (Eq.trans (ph≡ e′ (prm f i))
                                (Eq.cong (ph g′) (prm≡ e i)))

  p : ∀ i → prm g (prm f i) ≡ prm g′ (prm f′ i)
  p i = Eq.trans (prm≡ e′ (prm f i)) (Eq.cong (prm g′) (prm≡ e i))

⊙-assoc : ∀ (f g h : PP) → (f ⊙ g) ⊙ h ≐ f ⊙ (g ⊙ h)
⊙-assoc f g h =
  eqv (λ i → +ᵖ-assoc (ph f i) (ph g (prm f i)) (ph h (prm g (prm f i))))
      (λ _ → Eq.refl)

⊙-idˡ : ∀ (f : PP) → idPP ⊙ f ≐ f
⊙-idˡ f = eqv (λ _ → Eq.refl) (λ _ → Eq.refl)

⊙-idʳ : ∀ (f : PP) → f ⊙ idPP ≐ f
⊙-idʳ f = eqv (λ i → +ᵖ-idʳ (ph f i)) (λ _ → Eq.refl)

------------------------------------------------------------------------
-- The atoms: a phase on one index, and a transposition

-- Whether an index is the one carrying the phase.
δ : Fin N → Fin N → Bool
δ c i with i ≟ c
... | yes _ = true
... | no  _ = false

δ-here : ∀ (c : Fin N) → δ c c ≡ true
δ-here c with c ≟ c
... | yes _  = Eq.refl
... | no  ne = ⊥-elim (ne Eq.refl)

δ-≢ : ∀ (c i : Fin N) → i ≢ c → δ c i ≡ false
δ-≢ c i ne with i ≟ c
... | yes e = ⊥-elim (ne e)
... | no  _ = Eq.refl

-- The phase where the test holds.
phif : Bool → Ph → Ph
phif true  k = k
phif false k = p0

swapF : Fin N → Fin N → Fin N → Fin N
swapF a b i with i ≟ a
... | yes _ = b
... | no  _ with i ≟ b
...         | yes _ = a
...         | no  _ = i

PH : Fin N → Ph → PP
PH c k = pp[ (λ i → phif (δ c i) k) , (λ i → i) ]

SWP : Fin N → Fin N → PP
SWP a b = pp[ (λ _ → p0) , swapF a b ]

------------------------------------------------------------------------
-- How a transposition acts

swapF-a : ∀ (a b : Fin N) → swapF a b a ≡ b
swapF-a a b with a ≟ a
... | yes _  = Eq.refl
... | no  ne = ⊥-elim (ne Eq.refl)

swapF-b : ∀ (a b : Fin N) → swapF a b b ≡ a
swapF-b a b with b ≟ a
... | yes e = e
... | no  _ with b ≟ b
...         | yes _  = Eq.refl
...         | no  ne = ⊥-elim (ne Eq.refl)

swapF-o : ∀ (a b i : Fin N) → i ≢ a → i ≢ b → swapF a b i ≡ i
swapF-o a b i ia ib with i ≟ a
... | yes e = ⊥-elim (ia e)
... | no  _ with i ≟ b
...         | yes e = ⊥-elim (ib e)
...         | no  _ = Eq.refl

swapF-invol : ∀ (a b i : Fin N) → swapF a b (swapF a b i) ≡ i
swapF-invol a b i with i ≟ a
... | yes Eq.refl = swapF-b a b
... | no  ia with i ≟ b
...          | yes Eq.refl = swapF-a a b
...          | no  ib = swapF-o a b i ia ib

swapF-inj : ∀ (a b : Fin N) {i j : Fin N} → swapF a b i ≡ swapF a b j → i ≡ j
swapF-inj a b {i} {j} e =
  Eq.trans (Eq.sym (swapF-invol a b i))
           (Eq.trans (Eq.cong (swapF a b) e) (swapF-invol a b j))

-- Deciding in a helper rather than with a `with`: a `with` here would
-- rewrite the goal into the shape of `swapF`'s own case split, and the
-- characterisations above would no longer apply to it.
swapF-sym : ∀ (a b i : Fin N) → swapF a b i ≡ swapF b a i
swapF-sym a b i = go (i ≟ a) (i ≟ b)
  where
  go : Dec (i ≡ a) → Dec (i ≡ b) → swapF a b i ≡ swapF b a i
  go (yes Eq.refl) _ = Eq.trans (swapF-a i b) (Eq.sym (swapF-b b i))
  go (no ia) (yes Eq.refl) = Eq.trans (swapF-b a i) (Eq.sym (swapF-a i a))
  go (no ia) (no ib) =
    Eq.trans (swapF-o a b i ia ib) (Eq.sym (swapF-o b a i ib ia))

swapF-same : ∀ (a i : Fin N) → swapF a a i ≡ i
swapF-same a i with i ≟ a
... | yes e = Eq.sym e
... | no  ia with i ≟ a
...          | yes e = ⊥-elim (ia e)
...          | no  _ = Eq.refl

private
  δ-swap : ∀ (a b c i : Fin N) → δ (swapF a b c) (swapF a b i) ≡ δ c i
  δ-swap a b c i = go (i ≟ c)
    where
    go : Dec (i ≡ c) → δ (swapF a b c) (swapF a b i) ≡ δ c i
    go (yes Eq.refl) = Eq.trans (δ-here (swapF a b i)) (Eq.sym (δ-here i))
    go (no  ne) =
      Eq.trans (δ-≢ (swapF a b c) (swapF a b i) (λ e → ne (swapF-inj a b e)))
               (Eq.sym (δ-≢ c i ne))

------------------------------------------------------------------------
-- The algebra of the atoms

PH-id : ∀ (c : Fin N) → PH c p0 ≐ idPP
PH-id c = eqv s (λ _ → Eq.refl)
  where
  s : ∀ i → phif (δ c i) p0 ≡ p0
  s i with δ c i
  ... | true  = Eq.refl
  ... | false = Eq.refl

PH-fuse : ∀ (c : Fin N) (k l : Ph) → PH c k ⊙ PH c l ≐ PH c (k +ᵖ l)
PH-fuse c k l = eqv s (λ _ → Eq.refl)
  where
  s : ∀ i → phif (δ c i) k +ᵖ phif (δ c i) l ≡ phif (δ c i) (k +ᵖ l)
  s i with δ c i
  ... | true  = Eq.refl
  ... | false = Eq.refl

PH-comm : ∀ (c d : Fin N) (k l : Ph) → PH c k ⊙ PH d l ≐ PH d l ⊙ PH c k
PH-comm c d k l =
  eqv (λ i → +ᵖ-comm (phif (δ c i) k) (phif (δ d i) l)) (λ _ → Eq.refl)

SWP-invol : ∀ (a b : Fin N) → SWP a b ⊙ SWP a b ≐ idPP
SWP-invol a b = eqv (λ _ → Eq.refl) (swapF-invol a b)

SWP-sym : ∀ (a b : Fin N) → SWP a b ≐ SWP b a
SWP-sym a b = eqv (λ _ → Eq.refl) (swapF-sym a b)

SWP-same : ∀ (a : Fin N) → SWP a a ≐ idPP
SWP-same a = eqv (λ _ → Eq.refl) (swapF-same a)

-- A phase passes a transposition, its index transposed with it.
PH-SWP : ∀ (c : Fin N) (k : Ph) (a b : Fin N) →
         PH c k ⊙ SWP a b ≐ SWP a b ⊙ PH (swapF a b c) k
PH-SWP c k a b =
  eqv (λ i → Eq.trans (+ᵖ-idʳ (phif (δ c i) k))
                      (Eq.cong (λ z → phif z k) (Eq.sym (δ-swap a b c i))))
      (λ _ → Eq.refl)

SWP-PH : ∀ (a b c : Fin N) (k : Ph) →
         SWP a b ⊙ PH c k ≐ PH (swapF a b c) k ⊙ SWP a b
SWP-PH a b c k = eqv s (λ _ → Eq.refl)
  where
  s : ∀ i → p0 +ᵖ phif (δ c (swapF a b i)) k ≡ phif (δ (swapF a b c) i) k +ᵖ p0
  s i = Eq.trans step (Eq.sym (+ᵖ-idʳ (phif (δ (swapF a b c) i) k)))
    where
    step : phif (δ c (swapF a b i)) k ≡ phif (δ (swapF a b c) i) k
    step = Eq.cong (λ z → phif z k)
             (Eq.trans (Eq.cong (λ z → δ z (swapF a b i))
                                (Eq.sym (swapF-invol a b c)))
                       (δ-swap a b (swapF a b c) i))

-- Conjugating a transposition transposes its indices.
SWP-conj : ∀ (a b c d : Fin N) →
           SWP a b ⊙ SWP c d ⊙ SWP a b ≐ SWP (swapF a b c) (swapF a b d)
SWP-conj a b c d = eqv (λ _ → Eq.refl) p
  where
  t = swapF a b

  p : ∀ i → t (swapF c d (t i)) ≡ swapF (t c) (t d) i
  p i = go (t i ≟ c) (t i ≟ d)
    where
    tt : ∀ (x : Fin N) {y : Fin N} → t x ≡ y → x ≡ t y
    tt x e = Eq.trans (Eq.sym (swapF-invol a b x)) (Eq.cong t e)

    go : Dec (t i ≡ c) → Dec (t i ≡ d) → t (swapF c d (t i)) ≡ swapF (t c) (t d) i
    go (yes e) _ =
      Eq.trans (Eq.cong t (Eq.trans (Eq.cong (swapF c d) e) (swapF-a c d)))
               (Eq.sym (Eq.trans (Eq.cong (swapF (t c) (t d)) (tt i e))
                                 (swapF-a (t c) (t d))))
    go (no nc) (yes e) =
      Eq.trans (Eq.cong t (Eq.trans (Eq.cong (swapF c d) e) (swapF-b c d)))
               (Eq.sym (Eq.trans (Eq.cong (swapF (t c) (t d)) (tt i e))
                                 (swapF-b (t c) (t d))))
    go (no nc) (no nd) =
      Eq.trans (Eq.cong t (swapF-o c d (t i) nc nd))
               (Eq.trans (swapF-invol a b i)
                         (Eq.sym (swapF-o (t c) (t d) i
                                    (λ e → nc (Eq.trans (Eq.cong t e) (swapF-invol a b c)))
                                    (λ e → nd (Eq.trans (Eq.cong t e) (swapF-invol a b d))))))

------------------------------------------------------------------------
-- Rewriting inside a product

≡⇒≐ : ∀ {f g : PP} → f ≡ g → f ≐ g
≡⇒≐ Eq.refl = ≐-refl

ph≡≐ : ∀ {x y : Fin N} {k : Ph} → x ≡ y → PH x k ≐ PH y k
ph≡≐ Eq.refl = ≐-refl

swp≡ : ∀ {a b c d : Fin N} → a ≡ c → b ≡ d → SWP a b ≐ SWP c d
swp≡ Eq.refl Eq.refl = ≐-refl

-- One factor hops over the next, both possibly changing.  Every
-- factor is explicit: `_⊙_` computes to a record literal, so a meta
-- `f ⊙ g` is never a unification pattern and nothing would be solved.
hop : ∀ (f g f′ g′ h : PP) → f ⊙ g ≐ g′ ⊙ f′ → f ⊙ (g ⊙ h) ≐ g′ ⊙ (f′ ⊙ h)
hop f g f′ g′ h e =
  ≐-trans (≐-sym (⊙-assoc f g h))
          (≐-trans (⊙-cong e (≐-refl {h})) (⊙-assoc g′ f′ h))

-- Two factors fuse into one.
fuse : ∀ (f g k h : PP) → f ⊙ g ≐ k → f ⊙ (g ⊙ h) ≐ k ⊙ h
fuse f g k h e = ≐-trans (≐-sym (⊙-assoc f g h)) (⊙-cong e (≐-refl {h}))

-- And they may fuse to nothing.
drop : ∀ (f g h : PP) → f ⊙ g ≐ idPP → f ⊙ (g ⊙ h) ≐ h
drop f g h e = ≐-trans (fuse f g idPP h e) (⊙-idˡ h)

------------------------------------------------------------------------
-- The reading of a word
--
-- A phase pair is two phase atoms, a letter is a sign times a
-- transposition; a K letter is read as the identity, which is harmless
-- because no rule of the fragment mentions one.

L : Fin N → Fin N → Fin N → PP
L c a b = PH c p2 ⊙ SWP a b

-- The phase pair.
P₂ : Fin N → Fin N → PP
P₂ a b = PH a p1 ⊙ PH b p3

spg : GenP N → PP
spg (pp a b)         = P₂ a b
spg (px c a b _)     = L c a b
spg (dx a b c d _ _) = SWP a b ⊙ SWP c d
spg (kk a b c d _ _) = idPP

sp : W → PP
sp [ g ]ʷ  = spg g
sp ε       = idPP
sp (u • v) = sp u ⊙ sp v

------------------------------------------------------------------------
-- Products of letters
--
-- Two facts do most of the work: the product of two letters, and a
-- letter conjugated by a letter.  Moving a phase past a transposition
-- transposes its index, and conjugating a transposition transposes
-- both of its indices, so both results are read off `swapF`.

prod-L : ∀ (c a b d p q : Fin N) →
         L c a b ⊙ L d p q ≐
         PH c p2 ⊙ (PH (swapF a b d) p2 ⊙ (SWP a b ⊙ SWP p q))
prod-L c a b d p q =
  ≐-trans (⊙-assoc (PH c p2) (SWP a b) (PH d p2 ⊙ SWP p q))
          (⊙-cong (≐-refl {PH c p2})
                  (hop (SWP a b) (PH d p2) (SWP a b) (PH (swapF a b d) p2) (SWP p q)
                       (SWP-PH a b d p2)))

conj-L : ∀ (x a b y p q z : Fin N) →
         L x a b ⊙ (L y p q ⊙ L z a b) ≐
         PH x p2 ⊙ (PH (swapF a b y) p2
                   ⊙ (PH (swapF a b (swapF p q z)) p2
                     ⊙ SWP (swapF a b p) (swapF a b q)))
conj-L x a b y p q z = begin
  L x a b ⊙ (L y p q ⊙ L z a b)
    ≈⟨ ⊙-cong (≐-refl {L x a b}) (prod-L y p q z a b) ⟩
  (PH x p2 ⊙ SWP a b) ⊙ (PH y p2 ⊙ (PH (swapF p q z) p2 ⊙ (SWP p q ⊙ SWP a b)))
    ≈⟨ ⊙-assoc (PH x p2) (SWP a b)
               (PH y p2 ⊙ (PH (swapF p q z) p2 ⊙ (SWP p q ⊙ SWP a b))) ⟩
  PH x p2 ⊙ (SWP a b ⊙ (PH y p2 ⊙ (PH (swapF p q z) p2 ⊙ (SWP p q ⊙ SWP a b))))
    ≈⟨ ⊙-cong (≐-refl {PH x p2})
              (hop (SWP a b) (PH y p2) (SWP a b) (PH (swapF a b y) p2)
                   (PH (swapF p q z) p2 ⊙ (SWP p q ⊙ SWP a b))
                   (SWP-PH a b y p2)) ⟩
  PH x p2 ⊙ (PH (swapF a b y) p2 ⊙ (SWP a b ⊙ (PH (swapF p q z) p2 ⊙ (SWP p q ⊙ SWP a b))))
    ≈⟨ ⊙-cong (≐-refl {PH x p2})
              (⊙-cong (≐-refl {PH (swapF a b y) p2})
                      (hop (SWP a b) (PH (swapF p q z) p2) (SWP a b)
                           (PH (swapF a b (swapF p q z)) p2) (SWP p q ⊙ SWP a b)
                           (SWP-PH a b (swapF p q z) p2))) ⟩
  PH x p2 ⊙ (PH (swapF a b y) p2 ⊙ (PH (swapF a b (swapF p q z)) p2
          ⊙ (SWP a b ⊙ (SWP p q ⊙ SWP a b))))
    ≈⟨ ⊙-cong (≐-refl {PH x p2})
              (⊙-cong (≐-refl {PH (swapF a b y) p2})
                      (⊙-cong (≐-refl {PH (swapF a b (swapF p q z)) p2})
                              (SWP-conj a b p q))) ⟩
  PH x p2 ⊙ (PH (swapF a b y) p2 ⊙ (PH (swapF a b (swapF p q z)) p2
          ⊙ SWP (swapF a b p) (swapF a b q))) ∎

-- Transpositions on disjoint pairs commute.
SWP-comm : ∀ (a b p q : Fin N) → p ≢ a → p ≢ b → q ≢ a → q ≢ b →
           SWP a b ⊙ SWP p q ≐ SWP p q ⊙ SWP a b
SWP-comm a b p q pa pb qa qb = begin
  SWP a b ⊙ SWP p q
    ≈⟨ ≐-sym (⊙-idʳ (SWP a b ⊙ SWP p q)) ⟩
  (SWP a b ⊙ SWP p q) ⊙ idPP
    ≈⟨ ⊙-cong (≐-refl {SWP a b ⊙ SWP p q}) (≐-sym (SWP-invol a b)) ⟩
  (SWP a b ⊙ SWP p q) ⊙ (SWP a b ⊙ SWP a b)
    ≈⟨ ≐-sym (⊙-assoc (SWP a b ⊙ SWP p q) (SWP a b) (SWP a b)) ⟩
  ((SWP a b ⊙ SWP p q) ⊙ SWP a b) ⊙ SWP a b
    ≈⟨ ⊙-cong (⊙-assoc (SWP a b) (SWP p q) (SWP a b)) (≐-refl {SWP a b}) ⟩
  (SWP a b ⊙ (SWP p q ⊙ SWP a b)) ⊙ SWP a b
    ≈⟨ ⊙-cong (SWP-conj a b p q) (≐-refl {SWP a b}) ⟩
  SWP (swapF a b p) (swapF a b q) ⊙ SWP a b
    ≈⟨ ⊙-cong (swp≡ (swapF-o a b p pa pb) (swapF-o a b q qa qb)) (≐-refl {SWP a b}) ⟩
  SWP p q ⊙ SWP a b ∎

------------------------------------------------------------------------
-- Distinctness from the side conditions

private
  <≢ : ∀ {x y : Fin N} → toℕ x < toℕ y → x ≢ y
  <≢ {x} lt e = n≮n (toℕ x) (Eq.subst (toℕ x <_) (Eq.sym (Eq.cong toℕ e)) lt)

  ≢sym : ∀ {x y : Fin N} → x ≢ y → y ≢ x
  ≢sym ne e = ne (Eq.sym e)

  Succ<ℕ : ∀ {a a′ : Fin N} → Succ a a′ → toℕ a < toℕ a′
  Succ<ℕ = s<

  Succ≢ : ∀ {a a′ : Fin N} → Succ a a′ → a ≢ a′
  Succ≢ s = <≢ (s< s)

------------------------------------------------------------------------
-- Soundness
--
-- The rules about phase pairs alone are proved pointwise: the pair's
-- phase function is a sum of two `phif`s, so a case split on the δs
-- closes each index.  The rules with a letter in them are computed to
-- canonical form — the phases first, then the transpositions — by
-- `prod-L` and `conj-L`, and the index each phase ends up on is read
-- off `swapF`, exactly as in `SignedPerm`.

private
  ph2-hop : ∀ (x y : Fin N) (h : PP) →
            PH x p2 ⊙ (PH y p2 ⊙ h) ≐ PH y p2 ⊙ (PH x p2 ⊙ h)
  ph2-hop x y h = hop (PH x p2) (PH y p2) (PH x p2) (PH y p2) h (PH-comm x y p2 p2)

  ph2-drop : ∀ (x : Fin N) (h : PP) → PH x p2 ⊙ (PH x p2 ⊙ h) ≐ h
  ph2-drop x h = drop (PH x p2) (PH x p2) h
                      (≐-trans (PH-fuse x p2 p2) (PH-id x))

  -- What the braid and the shrinking rules come down to: an outer
  -- phase repeated around the one that survives.
  ph2-sandwich : ∀ (x y : Fin N) (h : PP) →
                 PH x p2 ⊙ (PH y p2 ⊙ (PH x p2 ⊙ h)) ≐ PH y p2 ⊙ h
  ph2-sandwich x y h =
    ≐-trans (ph2-hop x y (PH x p2 ⊙ h))
            (⊙-cong (≐-refl {PH y p2}) (ph2-drop x h))

  -- The pointwise helpers for the phase-pair rules.
  tele-ph : ∀ (x y z : Bool) →
            (phif x p1 +ᵖ phif y p3) +ᵖ (phif y p1 +ᵖ phif z p3)
            ≡ phif x p1 +ᵖ phif z p3
  tele-ph true  true  true  = Eq.refl
  tele-ph true  true  false = Eq.refl
  tele-ph true  false true  = Eq.refl
  tele-ph true  false false = Eq.refl
  tele-ph false true  true  = Eq.refl
  tele-ph false true  false = Eq.refl
  tele-ph false false true  = Eq.refl
  tele-ph false false false = Eq.refl

  sq-ph : ∀ (x y : Bool) →
          (phif x p1 +ᵖ phif y p3) +ᵖ (phif x p1 +ᵖ phif y p3)
          ≡ phif x p2 +ᵖ phif y p2
  sq-ph true  true  = Eq.refl
  sq-ph true  false = Eq.refl
  sq-ph false true  = Eq.refl
  sq-ph false false = Eq.refl

sound-ax : ∀ {u v : W} → N F, u === v → sp u ≐ sp v
-- The pair on one index vanishes.
sound-ax (pp-id a) = eqv s (λ _ → Eq.refl)
  where
  s : ∀ i → phif (δ a i) p1 +ᵖ phif (δ a i) p3 ≡ p0
  s i with δ a i
  ... | true  = Eq.refl
  ... | false = Eq.refl
-- A pair has order four.
sound-ax (pp-ord a b) = eqv s (λ _ → Eq.refl)
  where
  s : ∀ i → let φ = phif (δ a i) p1 +ᵖ phif (δ b i) p3 in
            φ +ᵖ (φ +ᵖ (φ +ᵖ φ)) ≡ p0
  s i = +ᵖ-4 (phif (δ a i) p1 +ᵖ phif (δ b i) p3)
-- Pairs commute.
sound-ax (pp-comm a b c d) =
  eqv (λ i → +ᵖ-comm (phif (δ a i) p1 +ᵖ phif (δ b i) p3)
                     (phif (δ c i) p1 +ᵖ phif (δ d i) p3))
      (λ _ → Eq.refl)
-- Pairs telescope.
sound-ax (pp-tele a b c) =
  eqv (λ i → tele-ph (δ a i) (δ b i) (δ c i)) (λ _ → Eq.refl)
-- A letter squared is the −1−1 pair of its indices.
sound-ax (px-sq a a′ s) = ≐-trans lhs (≐-sym rhs)
  where
  aa′ = Succ≢ s

  lhs : P₂ a a′ ⊙ P₂ a a′ ≐ PH a p2 ⊙ (PH a′ p2 ⊙ idPP)
  lhs = eqv sg (λ _ → Eq.refl)
    where
    sg : ∀ i → (phif (δ a i) p1 +ᵖ phif (δ a′ i) p3)
               +ᵖ (phif (δ a i) p1 +ᵖ phif (δ a′ i) p3)
               ≡ phif (δ a i) p2 +ᵖ (phif (δ a′ i) p2 +ᵖ p0)
    sg i = Eq.trans (sq-ph (δ a i) (δ a′ i))
                    (Eq.cong (phif (δ a i) p2 +ᵖ_)
                             (Eq.sym (+ᵖ-idʳ (phif (δ a′ i) p2))))

  rhs : L a a a′ ⊙ L a a a′ ≐ PH a p2 ⊙ (PH a′ p2 ⊙ idPP)
  rhs = begin
    L a a a′ ⊙ L a a a′
      ≈⟨ prod-L a a a′ a a a′ ⟩
    PH a p2 ⊙ (PH (swapF a a′ a) p2 ⊙ (SWP a a′ ⊙ SWP a a′))
      ≈⟨ ⊙-cong (≐-refl {PH a p2})
                (⊙-cong (ph≡≐ (swapF-a a a′)) (SWP-invol a a′)) ⟩
    PH a p2 ⊙ (PH a′ p2 ⊙ idPP) ∎
-- The braid, both sides the letter on the outer pair.
sound-ax (px-braid a a′ a″ s s′) = ≐-trans lhs (≐-sym rhs)
  where
  aa′  = Succ≢ s
  a′a″ = Succ≢ s′
  aa″  = <≢ (<-trans (s< s) (s< s′))

  lhs : L a a a′ ⊙ (L a′ a′ a″ ⊙ L a a a′) ≐ PH a′ p2 ⊙ SWP a a″
  lhs = begin
    L a a a′ ⊙ (L a′ a′ a″ ⊙ L a a a′)
      ≈⟨ conj-L a a a′ a′ a′ a″ a ⟩
    PH a p2 ⊙ (PH (swapF a a′ a′) p2
              ⊙ (PH (swapF a a′ (swapF a′ a″ a)) p2
                ⊙ SWP (swapF a a′ a′) (swapF a a′ a″)))
      ≈⟨ ⊙-cong (≐-refl {PH a p2})
                (⊙-cong (ph≡≐ (swapF-b a a′))
                        (⊙-cong (ph≡≐ (Eq.trans (Eq.cong (swapF a a′)
                                                  (swapF-o a′ a″ a aa′ aa″))
                                                (swapF-a a a′)))
                                (swp≡ (swapF-b a a′)
                                      (swapF-o a a′ a″ (≢sym aa″) (≢sym a′a″))))) ⟩
    PH a p2 ⊙ (PH a p2 ⊙ (PH a′ p2 ⊙ SWP a a″))
      ≈⟨ ph2-drop a (PH a′ p2 ⊙ SWP a a″) ⟩
    PH a′ p2 ⊙ SWP a a″ ∎

  rhs : L a′ a′ a″ ⊙ (L a a a′ ⊙ L a′ a′ a″) ≐ PH a′ p2 ⊙ SWP a a″
  rhs = begin
    L a′ a′ a″ ⊙ (L a a a′ ⊙ L a′ a′ a″)
      ≈⟨ conj-L a′ a′ a″ a a a′ a′ ⟩
    PH a′ p2 ⊙ (PH (swapF a′ a″ a) p2
               ⊙ (PH (swapF a′ a″ (swapF a a′ a′)) p2
                 ⊙ SWP (swapF a′ a″ a) (swapF a′ a″ a′)))
      ≈⟨ ⊙-cong (≐-refl {PH a′ p2})
                (⊙-cong (ph≡≐ (swapF-o a′ a″ a aa′ aa″))
                        (⊙-cong (ph≡≐ (Eq.trans (Eq.cong (swapF a′ a″) (swapF-b a a′))
                                                (swapF-o a′ a″ a aa′ aa″)))
                                (swp≡ (swapF-o a′ a″ a aa′ aa″) (swapF-a a′ a″)))) ⟩
    PH a′ p2 ⊙ (PH a p2 ⊙ (PH a p2 ⊙ SWP a a″))
      ≈⟨ ⊙-cong (≐-refl {PH a′ p2}) (ph2-drop a (SWP a a″)) ⟩
    PH a′ p2 ⊙ SWP a a″ ∎
-- (shrink₁), (shrink₂): the lower index moves up.
sound-ax (px-shrink₁ a a′ c s lt) = ≐-sym (begin
  L a′ a a′ ⊙ (L a′ a′ c ⊙ L a a a′)
    ≈⟨ conj-L a′ a a′ a′ a′ c a ⟩
  PH a′ p2 ⊙ (PH (swapF a a′ a′) p2
             ⊙ (PH (swapF a a′ (swapF a′ c a)) p2
               ⊙ SWP (swapF a a′ a′) (swapF a a′ c)))
    ≈⟨ ⊙-cong (≐-refl {PH a′ p2})
              (⊙-cong (ph≡≐ (swapF-b a a′))
                      (⊙-cong (ph≡≐ (Eq.trans (Eq.cong (swapF a a′)
                                                (swapF-o a′ c a aa′ ac))
                                              (swapF-a a a′)))
                              (swp≡ (swapF-b a a′)
                                    (swapF-o a a′ c (≢sym ac) (≢sym a′c))))) ⟩
  PH a′ p2 ⊙ (PH a p2 ⊙ (PH a′ p2 ⊙ SWP a c))
    ≈⟨ ph2-sandwich a′ a (SWP a c) ⟩
  PH a p2 ⊙ SWP a c ∎)
  where
  aa′ = Succ≢ s
  a′c = <≢ lt
  ac  = <≢ (<-trans (s< s) lt)
sound-ax (px-shrink₂ a a′ c s lt) = ≐-sym (begin
  L a′ a a′ ⊙ (L c a′ c ⊙ L a a a′)
    ≈⟨ conj-L a′ a a′ c a′ c a ⟩
  PH a′ p2 ⊙ (PH (swapF a a′ c) p2
             ⊙ (PH (swapF a a′ (swapF a′ c a)) p2
               ⊙ SWP (swapF a a′ a′) (swapF a a′ c)))
    ≈⟨ ⊙-cong (≐-refl {PH a′ p2})
              (⊙-cong (ph≡≐ (swapF-o a a′ c (≢sym ac) (≢sym a′c)))
                      (⊙-cong (ph≡≐ (Eq.trans (Eq.cong (swapF a a′)
                                                (swapF-o a′ c a aa′ ac))
                                              (swapF-a a a′)))
                              (swp≡ (swapF-b a a′)
                                    (swapF-o a a′ c (≢sym ac) (≢sym a′c))))) ⟩
  PH a′ p2 ⊙ (PH c p2 ⊙ (PH a′ p2 ⊙ SWP a c))
    ≈⟨ ph2-sandwich a′ c (SWP a c) ⟩
  PH c p2 ⊙ SWP a c ∎)
  where
  aa′ = Succ≢ s
  a′c = <≢ lt
  ac  = <≢ (<-trans (s< s) lt)
-- (shrink₃), (shrink₄): the upper index moves down.
sound-ax (px-shrink₃ a c′ c s lt) = ≐-sym (begin
  L c′ c′ c ⊙ (L a a c′ ⊙ L c c′ c)
    ≈⟨ conj-L c′ c′ c a a c′ c ⟩
  PH c′ p2 ⊙ (PH (swapF c′ c a) p2
             ⊙ (PH (swapF c′ c (swapF a c′ c)) p2
               ⊙ SWP (swapF c′ c a) (swapF c′ c c′)))
    ≈⟨ ⊙-cong (≐-refl {PH c′ p2})
              (⊙-cong (ph≡≐ (swapF-o c′ c a ac′ ac))
                      (⊙-cong (ph≡≐ (Eq.trans (Eq.cong (swapF c′ c)
                                                (swapF-o a c′ c (≢sym ac) (≢sym c′c)))
                                              (swapF-b c′ c)))
                              (swp≡ (swapF-o c′ c a ac′ ac) (swapF-a c′ c)))) ⟩
  PH c′ p2 ⊙ (PH a p2 ⊙ (PH c′ p2 ⊙ SWP a c))
    ≈⟨ ph2-sandwich c′ a (SWP a c) ⟩
  PH a p2 ⊙ SWP a c ∎)
  where
  c′c = Succ≢ s
  ac  = <≢ (<-trans lt (s< s))
  ac′ = <≢ lt
sound-ax (px-shrink₄ a c′ c s lt) = ≐-sym (begin
  L c′ c′ c ⊙ (L c′ a c′ ⊙ L c c′ c)
    ≈⟨ conj-L c′ c′ c c′ a c′ c ⟩
  PH c′ p2 ⊙ (PH (swapF c′ c c′) p2
             ⊙ (PH (swapF c′ c (swapF a c′ c)) p2
               ⊙ SWP (swapF c′ c a) (swapF c′ c c′)))
    ≈⟨ ⊙-cong (≐-refl {PH c′ p2})
              (⊙-cong (ph≡≐ (swapF-a c′ c))
                      (⊙-cong (ph≡≐ (Eq.trans (Eq.cong (swapF c′ c)
                                                (swapF-o a c′ c (≢sym ac) (≢sym c′c)))
                                              (swapF-b c′ c)))
                              (swp≡ (swapF-o c′ c a ac′ ac) (swapF-a c′ c)))) ⟩
  PH c′ p2 ⊙ (PH c p2 ⊙ (PH c′ p2 ⊙ SWP a c))
    ≈⟨ ph2-sandwich c′ c (SWP a c) ⟩
  PH c p2 ⊙ SWP a c ∎)
  where
  c′c = Succ≢ s
  ac  = <≢ (<-trans lt (s< s))
  ac′ = <≢ lt
-- The two phase choices on a consecutive pair are inverse.
sound-ax (px-inv a a′ s) = begin
  L a a a′ ⊙ L a′ a a′
    ≈⟨ prod-L a a a′ a′ a a′ ⟩
  PH a p2 ⊙ (PH (swapF a a′ a′) p2 ⊙ (SWP a a′ ⊙ SWP a a′))
    ≈⟨ ⊙-cong (≐-refl {PH a p2})
              (⊙-cong (ph≡≐ (swapF-b a a′)) (SWP-invol a a′)) ⟩
  PH a p2 ⊙ (PH a p2 ⊙ idPP)
    ≈⟨ ph2-drop a idPP ⟩
  idPP ∎
-- The sign moves to the lower index at the cost of a −1−1 pair.
sound-ax (px-sign c a b ab) = ≐-sym (begin
  P₂ c a ⊙ (P₂ c a ⊙ L a a b)
    ≈⟨ fuse (P₂ c a) (P₂ c a) (PH c p2 ⊙ PH a p2) (L a a b) pair² ⟩
  (PH c p2 ⊙ PH a p2) ⊙ L a a b
    ≈⟨ ⊙-assoc (PH c p2) (PH a p2) (L a a b) ⟩
  PH c p2 ⊙ (PH a p2 ⊙ (PH a p2 ⊙ SWP a b))
    ≈⟨ ⊙-cong (≐-refl {PH c p2}) (ph2-drop a (SWP a b)) ⟩
  PH c p2 ⊙ SWP a b ∎)
  where
  pair² : P₂ c a ⊙ P₂ c a ≐ PH c p2 ⊙ PH a p2
  pair² = eqv (λ i → sq-ph (δ c i) (δ a i)) (λ _ → Eq.refl)
-- A phase pair crosses a letter, its indices transposed.
sound-ax (px-conj a a′ c s ca ca′) = ≐-trans lhs (≐-sym rhs)
  where
  aa′ = Succ≢ s

  -- Both sides: the phase p1 lands on a (resp. a′), p3 stays on c.
  lhs : P₂ a′ c ⊙ L a a a′ ≐
        PH a′ p1 ⊙ (PH c p3 ⊙ (PH a p2 ⊙ SWP a a′))
  lhs = ⊙-assoc (PH a′ p1) (PH c p3) (L a a a′)

  rhs : L a a a′ ⊙ P₂ a c ≐
        PH a′ p1 ⊙ (PH c p3 ⊙ (PH a p2 ⊙ SWP a a′))
  rhs = begin
    L a a a′ ⊙ P₂ a c
      ≈⟨ ⊙-assoc (PH a p2) (SWP a a′) (P₂ a c) ⟩
    PH a p2 ⊙ (SWP a a′ ⊙ (PH a p1 ⊙ PH c p3))
      ≈⟨ ⊙-cong (≐-refl {PH a p2})
                (hop (SWP a a′) (PH a p1) (SWP a a′) (PH (swapF a a′ a) p1)
                     (PH c p3) (SWP-PH a a′ a p1)) ⟩
    PH a p2 ⊙ (PH (swapF a a′ a) p1 ⊙ (SWP a a′ ⊙ PH c p3))
      ≈⟨ ⊙-cong (≐-refl {PH a p2})
                (⊙-cong (ph≡≐ (swapF-a a a′))
                        (≐-trans (SWP-PH a a′ c p3)
                                 (⊙-cong (ph≡≐ (swapF-o a a′ c ca ca′))
                                         (≐-refl {SWP a a′})))) ⟩
    PH a p2 ⊙ (PH a′ p1 ⊙ (PH c p3 ⊙ SWP a a′))
      ≈⟨ hop (PH a p2) (PH a′ p1) (PH a p2) (PH a′ p1) (PH c p3 ⊙ SWP a a′)
             (PH-comm a a′ p2 p1) ⟩
    PH a′ p1 ⊙ (PH a p2 ⊙ (PH c p3 ⊙ SWP a a′))
      ≈⟨ ⊙-cong (≐-refl {PH a′ p1})
                (hop (PH a p2) (PH c p3) (PH a p2) (PH c p3) (SWP a a′)
                     (PH-comm a c p2 p3)) ⟩
    PH a′ p1 ⊙ (PH c p3 ⊙ (PH a p2 ⊙ SWP a a′)) ∎
-- The within-pair phase pair crosses its own letter: both sides are
-- the same sum once the two δ-swap identities rewrite the pair's
-- phases, and what is left is commutativity.
sound-ax (px-conj₂ a a′ s) = eqv sg (λ _ → Eq.refl)
  where
  σ = swapF a a′

  -- The pair's phases read through σ are its phases here.
  δσa : ∀ i → δ a′ (σ i) ≡ δ a i
  δσa i = Eq.trans (Eq.cong (λ z → δ z (σ i)) (Eq.sym (swapF-a a a′)))
                   (δ-swap a a′ a i)

  δσa′ : ∀ i → δ a (σ i) ≡ δ a′ i
  δσa′ i = Eq.trans (Eq.cong (λ z → δ z (σ i)) (Eq.sym (swapF-b a a′)))
                    (δ-swap a a′ a′ i)

  sg : ∀ i → (phif (δ a i) p1 +ᵖ phif (δ a′ i) p3) +ᵖ (phif (δ a i) p2 +ᵖ p0)
             ≡ (phif (δ a i) p2 +ᵖ p0)
               +ᵖ (phif (δ a′ (σ i)) p1 +ᵖ phif (δ a (σ i)) p3)
  sg i = Eq.trans
    (+ᵖ-comm (phif (δ a i) p1 +ᵖ phif (δ a′ i) p3) (phif (δ a i) p2 +ᵖ p0))
    (Eq.cong ((phif (δ a i) p2 +ᵖ p0) +ᵖ_)
      (Eq.sym (Eq.cong₂ (λ x y → phif x p1 +ᵖ phif y p3) (δσa i) (δσa′ i))))
-- Letters on disjoint consecutive pairs commute.
sound-ax (px-comm a a′ b b′ s s′ lt) = ≐-trans lhs (≐-sym rhs)
  where
  aa′  = Succ≢ s
  bb′  = Succ≢ s′
  a<b  = <-trans (s< s) lt
  a<b′ = <-trans a<b (s< s′)
  a′<b′ = <-trans lt (s< s′)

  lhs : L a a a′ ⊙ L b b b′ ≐ PH a p2 ⊙ (PH b p2 ⊙ (SWP a a′ ⊙ SWP b b′))
  lhs = begin
    L a a a′ ⊙ L b b b′
      ≈⟨ prod-L a a a′ b b b′ ⟩
    PH a p2 ⊙ (PH (swapF a a′ b) p2 ⊙ (SWP a a′ ⊙ SWP b b′))
      ≈⟨ ⊙-cong (≐-refl {PH a p2})
                (⊙-cong (ph≡≐ (swapF-o a a′ b (≢sym (<≢ a<b)) (≢sym (<≢ lt))))
                        (≐-refl {SWP a a′ ⊙ SWP b b′})) ⟩
    PH a p2 ⊙ (PH b p2 ⊙ (SWP a a′ ⊙ SWP b b′)) ∎

  rhs : L b b b′ ⊙ L a a a′ ≐ PH a p2 ⊙ (PH b p2 ⊙ (SWP a a′ ⊙ SWP b b′))
  rhs = begin
    L b b b′ ⊙ L a a a′
      ≈⟨ prod-L b b b′ a a a′ ⟩
    PH b p2 ⊙ (PH (swapF b b′ a) p2 ⊙ (SWP b b′ ⊙ SWP a a′))
      ≈⟨ ⊙-cong (≐-refl {PH b p2})
                (⊙-cong (ph≡≐ (swapF-o b b′ a (<≢ a<b) (<≢ a<b′)))
                        (SWP-comm b b′ a a′ (<≢ a<b) (<≢ a<b′)
                                  (<≢ lt) (<≢ a′<b′))) ⟩
    PH b p2 ⊙ (PH a p2 ⊙ (SWP a a′ ⊙ SWP b b′))
      ≈⟨ ph2-hop b a (SWP a a′ ⊙ SWP b b′) ⟩
    PH a p2 ⊙ (PH b p2 ⊙ (SWP a a′ ⊙ SWP b b′)) ∎
-- A double exchange is two letters, the signs cancelling.
sound-ax (dx-split a b c d ab cd) = ≐-sym (begin
  L a a b ⊙ L b c d
    ≈⟨ prod-L a a b b c d ⟩
  PH a p2 ⊙ (PH (swapF a b b) p2 ⊙ (SWP a b ⊙ SWP c d))
    ≈⟨ ⊙-cong (≐-refl {PH a p2})
              (⊙-cong (ph≡≐ (swapF-b a b)) (≐-refl {SWP a b ⊙ SWP c d})) ⟩
  PH a p2 ⊙ (PH a p2 ⊙ (SWP a b ⊙ SWP c d))
    ≈⟨ ph2-drop a (SWP a b ⊙ SWP c d) ⟩
  SWP a b ⊙ SWP c d ∎)

-- And so the whole congruence of the fragment is interpreted.
sound : ∀ {u v : W} → PB._≈_ (N F,_===_) u v → sp u ≐ sp v
sound PB.refl                 = ≐-refl
sound (PB.sym e)              = ≐-sym (sound e)
sound (PB.trans e e′)         = ≐-trans (sound e) (sound e′)
sound (PB.cong e e′)          = ⊙-cong (sound e) (sound e′)
sound (PB.assoc {w} {v} {u})  = ⊙-assoc (sp w) (sp v) (sp u)
sound (PB.left-unit {w})      = ⊙-idˡ (sp w)
sound (PB.right-unit {w})     = ⊙-idʳ (sp w)
sound (PB.axiom a)            = sound-ax a

------------------------------------------------------------------------
-- A phased permutation permutes
--
-- `PP` stores the permutation as a bare function; that it really is a
-- bijection is this lemma, proved letter by letter.  Only injectivity
-- is ever wanted, and on a finite type it is enough.

Inj : PP → Set
Inj f = ∀ {i j : Fin N} → prm f i ≡ prm f j → i ≡ j

idPP-inj : Inj idPP
idPP-inj e = e

PH-inj : ∀ (c : Fin N) (k : Ph) → Inj (PH c k)
PH-inj c k e = e

SWP-inj : ∀ (a b : Fin N) → Inj (SWP a b)
SWP-inj a b e = swapF-inj a b e

⊙-inj : ∀ (f g : PP) → Inj f → Inj g → Inj (f ⊙ g)
⊙-inj f g fi gi e = fi (gi e)

spg-inj : ∀ (g : GenP N) → Inj (spg g)
spg-inj (pp a b)         = ⊙-inj (PH a p1) (PH b p3) (PH-inj a p1) (PH-inj b p3)
spg-inj (px c a b _)     = ⊙-inj (PH c p2) (SWP a b) (PH-inj c p2) (SWP-inj a b)
spg-inj (dx a b c d _ _) = ⊙-inj (SWP a b) (SWP c d) (SWP-inj a b) (SWP-inj c d)
spg-inj (kk a b c d _ _) = idPP-inj

sp-inj : ∀ (w : W) → Inj (sp w)
sp-inj [ g ]ʷ  = spg-inj g
sp-inj ε       = idPP-inj
sp-inj (u • v) = ⊙-inj (sp u) (sp v) (sp-inj u) (sp-inj v)

-- A one-sided inverse is a two-sided one, without any counting: `g`
-- is injective, so from `g ∘ f = id` one gets `f ∘ g = id` by
-- cancelling a `g`, and the phases then follow at the transported
-- index.
⊙-inverse : ∀ (f g : PP) → Inj g → f ⊙ g ≐ idPP → g ⊙ f ≐ idPP
⊙-inverse f g gi e = eqv s p
  where
  p : ∀ i → prm f (prm g i) ≡ i
  p i = gi (prm≡ e (prm g i))

  s : ∀ i → ph g i +ᵖ ph f (prm g i) ≡ p0
  s i = +ᵖ-flip0 (ph f (prm g i)) (ph g i)
          (Eq.trans (Eq.cong (λ z → ph f (prm g i) +ᵖ ph g z) (Eq.sym (p i)))
                    (ph≡ e (prm g i)))

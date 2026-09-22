------------------------------------------------------------------------
-- Presentations of groups
--
-- Signed permutations, a model of the Hadamard-free fragment
--
-- Every letter of P but the Hadamard one denotes a signed permutation
-- of the 2ⁿ basis indices: a permutation together with a sign on each
-- index.  Reading a word that way is a monoid homomorphism, and
-- Equations (20)–(34) hold in it, so the congruence of `Figure8Free`
-- is interpreted here.  That is what makes the normal form of Lemma
-- A.4 *unique*: two normal forms with the same semantics have the same
-- signed permutation, and a normal form is recoverable from it.
--
-- The whole of Figure 8 is *not* interpreted here, and cannot be:
-- (41) says a Hadamard pair squared is the identity, which no signed
-- permutation reading of a Hadamard letter makes true.
--
-- A signed permutation is stored as its two components rather than as
-- one map to `Bool × Fin N`, because the permutation halves compose on
-- their own and almost every lemma is about them alone.  Words are
-- folded left to right; the other convention also models the rules
-- (checked in `scratchpad/tSP.py` at N = 8), so nothing turns on it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; _xor_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (_≟_ ; toℕ-injective)
open import Data.Nat using (suc ; _<_ ; _≤_) renaming (_^_ to _^ℕ_)
open import Data.Nat.Properties using (n≮n ; <-trans ; n<1+n ; ≤-refl ; ≤-pred)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ)

open import Notations using (₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8Free
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
  using (GenP ; −1−1 ; −1X ; XX ; HH)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zz ; zx ; xx)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  W : Set
  W = Word (GenP (₃₊ m))

------------------------------------------------------------------------
-- Booleans
--
-- The four facts about exclusive or that the signs need, proved here
-- rather than imported so that nothing depends on a library name.

private
  xor-self : ∀ (x : Bool) → x xor x ≡ false
  xor-self false = Eq.refl
  xor-self true  = Eq.refl

  xor-idʳ : ∀ (x : Bool) → x xor false ≡ x
  xor-idʳ false = Eq.refl
  xor-idʳ true  = Eq.refl

  xor-comm : ∀ (x y : Bool) → x xor y ≡ y xor x
  xor-comm false false = Eq.refl
  xor-comm false true  = Eq.refl
  xor-comm true  false = Eq.refl
  xor-comm true  true  = Eq.refl

  xor-assoc : ∀ (x y z : Bool) → (x xor y) xor z ≡ x xor (y xor z)
  xor-assoc false y z = Eq.refl
  xor-assoc true  false z = Eq.refl
  xor-assoc true  true  false = Eq.refl
  xor-assoc true  true  true  = Eq.refl

------------------------------------------------------------------------
-- Signed permutations

record SP : Set where
  constructor sp[_,_]
  field
    sgn : Fin N → Bool
    prm : Fin N → Fin N

open SP public

-- Pointwise equality of both components.
infix 4 _≐_
record _≐_ (f g : SP) : Set where
  constructor eqv
  field
    sgn≡ : ∀ i → sgn f i ≡ sgn g i
    prm≡ : ∀ i → prm f i ≡ prm g i

open _≐_ public

idSP : SP
idSP = sp[ (λ _ → false) , (λ i → i) ]

-- Composition, the left factor acting first.
infixr 7 _⊙_
_⊙_ : SP → SP → SP
f ⊙ g = sp[ (λ i → sgn f i xor sgn g (prm f i)) , (λ i → prm g (prm f i)) ]

≐-refl : ∀ {f} → f ≐ f
≐-refl = eqv (λ _ → Eq.refl) (λ _ → Eq.refl)

≐-sym : ∀ {f g} → f ≐ g → g ≐ f
≐-sym e = eqv (λ i → Eq.sym (sgn≡ e i)) (λ i → Eq.sym (prm≡ e i))

≐-trans : ∀ {f g h} → f ≐ g → g ≐ h → f ≐ h
≐-trans e e′ = eqv (λ i → Eq.trans (sgn≡ e i) (sgn≡ e′ i))
                   (λ i → Eq.trans (prm≡ e i) (prm≡ e′ i))

≐-isEquivalence : IsEquivalence _≐_
≐-isEquivalence = record { refl = ≐-refl ; sym = ≐-sym ; trans = ≐-trans }

SP-setoid : Setoid _ _
SP-setoid = record { Carrier = SP ; _≈_ = _≐_ ; isEquivalence = ≐-isEquivalence }

open import Relation.Binary.Reasoning.Setoid SP-setoid public

⊙-cong : ∀ {f f′ g g′} → f ≐ f′ → g ≐ g′ → f ⊙ g ≐ f′ ⊙ g′
⊙-cong {f} {f′} {g} {g′} e e′ = eqv s p
  where
  s : ∀ i → sgn f i xor sgn g (prm f i) ≡ sgn f′ i xor sgn g′ (prm f′ i)
  s i = Eq.cong₂ _xor_ (sgn≡ e i)
                       (Eq.trans (sgn≡ e′ (prm f i))
                                 (Eq.cong (sgn g′) (prm≡ e i)))

  p : ∀ i → prm g (prm f i) ≡ prm g′ (prm f′ i)
  p i = Eq.trans (prm≡ e′ (prm f i)) (Eq.cong (prm g′) (prm≡ e i))

⊙-assoc : ∀ (f g h : SP) → (f ⊙ g) ⊙ h ≐ f ⊙ (g ⊙ h)
⊙-assoc f g h =
  eqv (λ i → xor-assoc (sgn f i) (sgn g (prm f i)) (sgn h (prm g (prm f i))))
      (λ _ → Eq.refl)

⊙-idˡ : ∀ (f : SP) → idSP ⊙ f ≐ f
⊙-idˡ f = eqv (λ _ → Eq.refl) (λ _ → Eq.refl)

⊙-idʳ : ∀ (f : SP) → f ⊙ idSP ≐ f
⊙-idʳ f = eqv (λ i → xor-idʳ (sgn f i)) (λ _ → Eq.refl)

------------------------------------------------------------------------
-- The atoms: a sign on one index, and a transposition

private
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

swapF : Fin N → Fin N → Fin N → Fin N
swapF a b i with i ≟ a
... | yes _ = b
... | no  _ with i ≟ b
...         | yes _ = a
...         | no  _ = i

NEG : Fin N → SP
NEG c = sp[ δ c , (λ i → i) ]

SWP : Fin N → Fin N → SP
SWP a b = sp[ (λ _ → false) , swapF a b ]

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

NEG-invol : ∀ (c : Fin N) → NEG c ⊙ NEG c ≐ idSP
NEG-invol c = eqv (λ i → xor-self (δ c i)) (λ _ → Eq.refl)

NEG-comm : ∀ (c d : Fin N) → NEG c ⊙ NEG d ≐ NEG d ⊙ NEG c
NEG-comm c d = eqv (λ i → xor-comm (δ c i) (δ d i)) (λ _ → Eq.refl)

SWP-invol : ∀ (a b : Fin N) → SWP a b ⊙ SWP a b ≐ idSP
SWP-invol a b = eqv (λ _ → Eq.refl) (swapF-invol a b)

SWP-sym : ∀ (a b : Fin N) → SWP a b ≐ SWP b a
SWP-sym a b = eqv (λ _ → Eq.refl) (swapF-sym a b)

SWP-same : ∀ (a : Fin N) → SWP a a ≐ idSP
SWP-same a = eqv (λ _ → Eq.refl) (swapF-same a)

-- A sign passes a transposition, its index transposed with it.
NEG-SWP : ∀ (c a b : Fin N) → NEG c ⊙ SWP a b ≐ SWP a b ⊙ NEG (swapF a b c)
NEG-SWP c a b =
  eqv (λ i → Eq.trans (xor-idʳ (δ c i)) (Eq.sym (δ-swap a b c i)))
      (λ _ → Eq.refl)

SWP-NEG : ∀ (a b c : Fin N) → SWP a b ⊙ NEG c ≐ NEG (swapF a b c) ⊙ SWP a b
SWP-NEG a b c = eqv s (λ _ → Eq.refl)
  where
  s : ∀ i → false xor δ c (swapF a b i) ≡ δ (swapF a b c) i xor false
  s i = Eq.trans step (Eq.sym (xor-idʳ (δ (swapF a b c) i)))
    where
    step : δ c (swapF a b i) ≡ δ (swapF a b c) i
    step = Eq.trans (Eq.cong (λ z → δ z (swapF a b i))
                             (Eq.sym (swapF-invol a b c)))
                    (δ-swap a b (swapF a b c) i)

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
--
-- Every rule of the fragment is a product of letters, so what the
-- proofs need is to move one factor past the next and to fuse two
-- into one, both under a right-nested product.

≡⇒≐ : ∀ {f g : SP} → f ≡ g → f ≐ g
≡⇒≐ Eq.refl = ≐-refl

neg≡ : ∀ {x y : Fin N} → x ≡ y → NEG x ≐ NEG y
neg≡ Eq.refl = ≐-refl

swp≡ : ∀ {a b c d : Fin N} → a ≡ c → b ≡ d → SWP a b ≐ SWP c d
swp≡ Eq.refl Eq.refl = ≐-refl

-- One factor hops over the next, both possibly changing.  Every
-- factor is explicit: `_⊙_` computes to a record literal, so a meta
-- `f ⊙ g` is never a unification pattern and nothing would be solved.
hop : ∀ (f g f′ g′ h : SP) → f ⊙ g ≐ g′ ⊙ f′ → f ⊙ (g ⊙ h) ≐ g′ ⊙ (f′ ⊙ h)
hop f g f′ g′ h e =
  ≐-trans (≐-sym (⊙-assoc f g h))
          (≐-trans (⊙-cong e (≐-refl {h})) (⊙-assoc g′ f′ h))

-- Two factors fuse into one.
fuse : ∀ (f g k h : SP) → f ⊙ g ≐ k → f ⊙ (g ⊙ h) ≐ k ⊙ h
fuse f g k h e = ≐-trans (≐-sym (⊙-assoc f g h)) (⊙-cong e (≐-refl {h}))

-- And they may fuse to nothing.
drop : ∀ (f g h : SP) → f ⊙ g ≐ idSP → f ⊙ (g ⊙ h) ≐ h
drop f g h e = ≐-trans (fuse f g idSP h e) (⊙-idˡ h)

------------------------------------------------------------------------
-- The reading of a word
--
-- A letter of P is a sign times a transposition; a Hadamard letter is
-- read as the identity, which is harmless because no rule of the
-- fragment mentions one.

L : Fin N → Fin N → Fin N → SP
L c a b = NEG c ⊙ SWP a b

spg : GenP (₃₊ m) → SP
spg (−1−1 a b)       = NEG a ⊙ NEG b
spg (−1X c a b _)    = L c a b
spg (XX a b c d _ _) = SWP a b ⊙ SWP c d
spg (HH a b c d _ _) = idSP

sp : W → SP
sp [ g ]ʷ  = spg g
sp ε       = idSP
sp (u • v) = sp u ⊙ sp v

-- The deciding wrappers, on indices known to differ.
sp-zx : ∀ (c a b : Fin N) → a ≢ b → sp (zx c a b) ≐ L c a b
sp-zx c a b ne with a ≟ b
... | yes e = ⊥-elim (ne e)
... | no  _ = ≐-refl

sp-xx : ∀ (a b c d : Fin N) → a ≢ b → c ≢ d →
        sp (xx a b c d) ≐ SWP a b ⊙ SWP c d
sp-xx a b c d ab cd with a ≟ b | c ≟ d
... | yes e | _     = ⊥-elim (ab e)
... | no  _ | yes e = ⊥-elim (cd e)
... | no  _ | no  _ = ≐-refl

------------------------------------------------------------------------
-- Products of letters
--
-- Two facts do most of the work: the product of two letters, and a
-- letter conjugated by a letter.  Moving a sign past a transposition
-- transposes its index, and conjugating a transposition transposes
-- both of its indices, so both results are read off `swapF`.

prod-L : ∀ (c a b d p q : Fin N) →
         L c a b ⊙ L d p q ≐
         NEG c ⊙ (NEG (swapF a b d) ⊙ (SWP a b ⊙ SWP p q))
prod-L c a b d p q =
  ≐-trans (⊙-assoc (NEG c) (SWP a b) (NEG d ⊙ SWP p q))
          (⊙-cong (≐-refl {NEG c})
                  (hop (SWP a b) (NEG d) (SWP a b) (NEG (swapF a b d)) (SWP p q)
                       (SWP-NEG a b d)))

conj-L : ∀ (x a b y p q z : Fin N) →
         L x a b ⊙ (L y p q ⊙ L z a b) ≐
         NEG x ⊙ (NEG (swapF a b y)
                 ⊙ (NEG (swapF a b (swapF p q z))
                   ⊙ SWP (swapF a b p) (swapF a b q)))
conj-L x a b y p q z = begin
  L x a b ⊙ (L y p q ⊙ L z a b)
    ≈⟨ ⊙-cong (≐-refl {L x a b}) (prod-L y p q z a b) ⟩
  (NEG x ⊙ SWP a b) ⊙ (NEG y ⊙ (NEG (swapF p q z) ⊙ (SWP p q ⊙ SWP a b)))
    ≈⟨ ⊙-assoc (NEG x) (SWP a b)
               (NEG y ⊙ (NEG (swapF p q z) ⊙ (SWP p q ⊙ SWP a b))) ⟩
  NEG x ⊙ (SWP a b ⊙ (NEG y ⊙ (NEG (swapF p q z) ⊙ (SWP p q ⊙ SWP a b))))
    ≈⟨ ⊙-cong (≐-refl {NEG x})
              (hop (SWP a b) (NEG y) (SWP a b) (NEG (swapF a b y))
                   (NEG (swapF p q z) ⊙ (SWP p q ⊙ SWP a b))
                   (SWP-NEG a b y)) ⟩
  NEG x ⊙ (NEG (swapF a b y) ⊙ (SWP a b ⊙ (NEG (swapF p q z) ⊙ (SWP p q ⊙ SWP a b))))
    ≈⟨ ⊙-cong (≐-refl {NEG x})
              (⊙-cong (≐-refl {NEG (swapF a b y)})
                      (hop (SWP a b) (NEG (swapF p q z)) (SWP a b)
                           (NEG (swapF a b (swapF p q z))) (SWP p q ⊙ SWP a b)
                           (SWP-NEG a b (swapF p q z)))) ⟩
  NEG x ⊙ (NEG (swapF a b y) ⊙ (NEG (swapF a b (swapF p q z))
          ⊙ (SWP a b ⊙ (SWP p q ⊙ SWP a b))))
    ≈⟨ ⊙-cong (≐-refl {NEG x})
              (⊙-cong (≐-refl {NEG (swapF a b y)})
                      (⊙-cong (≐-refl {NEG (swapF a b (swapF p q z))})
                              (SWP-conj a b p q))) ⟩
  NEG x ⊙ (NEG (swapF a b y) ⊙ (NEG (swapF a b (swapF p q z))
          ⊙ SWP (swapF a b p) (swapF a b q))) ∎

-- Transpositions on disjoint pairs commute.
SWP-comm : ∀ (a b p q : Fin N) → p ≢ a → p ≢ b → q ≢ a → q ≢ b →
           SWP a b ⊙ SWP p q ≐ SWP p q ⊙ SWP a b
SWP-comm a b p q pa pb qa qb = begin
  SWP a b ⊙ SWP p q
    ≈⟨ ≐-sym (⊙-idʳ (SWP a b ⊙ SWP p q)) ⟩
  (SWP a b ⊙ SWP p q) ⊙ idSP
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

  Succ< : ∀ {a a′ : Fin N} → Succ a a′ → toℕ a < toℕ a′
  Succ< {a} s = Eq.subst (suc (toℕ a) ≤_) (Eq.sym s) ≤-refl

  Succ≢ : ∀ {a a′ : Fin N} → Succ a a′ → a ≢ a′
  Succ≢ s = <≢ (Succ< s)

------------------------------------------------------------------------
-- Soundness
--
-- Each rule is computed to canonical form — the signs first, then the
-- transpositions — by `prod-L` and `conj-L`, and the index each sign
-- ends up on is read off `swapF`.  The parity and ordering side
-- conditions of (25)–(28) play no part: all those rules need is that
-- their indices are distinct, which is why one lemma covers the four
-- of them and the braid (24) as well.

private
  neg-hop : ∀ (x y : Fin N) (h : SP) → NEG x ⊙ (NEG y ⊙ h) ≐ NEG y ⊙ (NEG x ⊙ h)
  neg-hop x y h = hop (NEG x) (NEG y) (NEG x) (NEG y) h (NEG-comm x y)

  neg-drop : ∀ (x : Fin N) (h : SP) → NEG x ⊙ (NEG x ⊙ h) ≐ h
  neg-drop x h = drop (NEG x) (NEG x) h (NEG-invol x)

  -- What (24)–(28) all come down to: an outer sign repeated around the
  -- one that survives.
  neg-sandwich : ∀ (x y : Fin N) (h : SP) →
                 NEG x ⊙ (NEG y ⊙ (NEG x ⊙ h)) ≐ NEG y ⊙ h
  neg-sandwich x y h =
    ≐-trans (neg-hop x y (NEG x ⊙ h))
            (⊙-cong (≐-refl {NEG y}) (neg-drop x h))

sound-ax : ∀ {u v : W} → m PF, u === v → sp u ≐ sp v
-- (20)–(22): the signs, where every permutation is the identity.
sound-ax (r20 a) = NEG-invol a
sound-ax (r21 a b) = NEG-comm a b
sound-ax (r22 a b c) = begin
  (NEG a ⊙ NEG b) ⊙ (NEG b ⊙ NEG c)
    ≈⟨ ⊙-assoc (NEG a) (NEG b) (NEG b ⊙ NEG c) ⟩
  NEG a ⊙ (NEG b ⊙ (NEG b ⊙ NEG c))
    ≈⟨ ⊙-cong (≐-refl {NEG a}) (neg-drop b (NEG c)) ⟩
  NEG a ⊙ NEG c ∎
-- (23): a letter squared is the sign pair of its indices.
sound-ax (r23 a a′ s) = ≐-sym (begin
  sp (zx a a a′) ⊙ sp (zx a a a′)
    ≈⟨ ⊙-cong (sp-zx a a a′ aa′) (sp-zx a a a′ aa′) ⟩
  L a a a′ ⊙ L a a a′
    ≈⟨ prod-L a a a′ a a a′ ⟩
  NEG a ⊙ (NEG (swapF a a′ a) ⊙ (SWP a a′ ⊙ SWP a a′))
    ≈⟨ ⊙-cong (≐-refl {NEG a})
              (⊙-cong (neg≡ (swapF-a a a′)) (SWP-invol a a′)) ⟩
  NEG a ⊙ (NEG a′ ⊙ idSP)
    ≈⟨ ⊙-cong (≐-refl {NEG a}) (⊙-idʳ (NEG a′)) ⟩
  NEG a ⊙ NEG a′ ∎)
  where aa′ = Succ≢ s
-- (24): the braid, both sides the letter on the outer pair.
sound-ax (r24 a a′ a″ s s′) = ≐-trans lhs (≐-sym rhs)
  where
  aa′  = Succ≢ s
  a′a″ = Succ≢ s′
  aa″  = <≢ (<-trans (Succ< s) (Succ< s′))

  lhs : sp (zx a a a′) ⊙ (sp (zx a′ a′ a″) ⊙ sp (zx a a a′)) ≐ NEG a′ ⊙ SWP a a″
  lhs = begin
    sp (zx a a a′) ⊙ (sp (zx a′ a′ a″) ⊙ sp (zx a a a′))
      ≈⟨ ⊙-cong (sp-zx a a a′ aa′)
                (⊙-cong (sp-zx a′ a′ a″ a′a″) (sp-zx a a a′ aa′)) ⟩
    L a a a′ ⊙ (L a′ a′ a″ ⊙ L a a a′)
      ≈⟨ conj-L a a a′ a′ a′ a″ a ⟩
    NEG a ⊙ (NEG (swapF a a′ a′)
            ⊙ (NEG (swapF a a′ (swapF a′ a″ a)) ⊙ SWP (swapF a a′ a′) (swapF a a′ a″)))
      ≈⟨ ⊙-cong (≐-refl {NEG a})
                (⊙-cong (neg≡ (swapF-b a a′))
                        (⊙-cong (neg≡ (Eq.trans (Eq.cong (swapF a a′)
                                                  (swapF-o a′ a″ a aa′ aa″))
                                                (swapF-a a a′)))
                                (swp≡ (swapF-b a a′)
                                      (swapF-o a a′ a″ (≢sym aa″) (≢sym a′a″))))) ⟩
    NEG a ⊙ (NEG a ⊙ (NEG a′ ⊙ SWP a a″))
      ≈⟨ neg-drop a (NEG a′ ⊙ SWP a a″) ⟩
    NEG a′ ⊙ SWP a a″ ∎

  rhs : sp (zx a′ a′ a″) ⊙ (sp (zx a a a′) ⊙ sp (zx a′ a′ a″)) ≐ NEG a′ ⊙ SWP a a″
  rhs = begin
    sp (zx a′ a′ a″) ⊙ (sp (zx a a a′) ⊙ sp (zx a′ a′ a″))
      ≈⟨ ⊙-cong (sp-zx a′ a′ a″ a′a″)
                (⊙-cong (sp-zx a a a′ aa′) (sp-zx a′ a′ a″ a′a″)) ⟩
    L a′ a′ a″ ⊙ (L a a a′ ⊙ L a′ a′ a″)
      ≈⟨ conj-L a′ a′ a″ a a a′ a′ ⟩
    NEG a′ ⊙ (NEG (swapF a′ a″ a)
             ⊙ (NEG (swapF a′ a″ (swapF a a′ a′)) ⊙ SWP (swapF a′ a″ a) (swapF a′ a″ a′)))
      ≈⟨ ⊙-cong (≐-refl {NEG a′})
                (⊙-cong (neg≡ (swapF-o a′ a″ a aa′ aa″))
                        (⊙-cong (neg≡ (Eq.trans (Eq.cong (swapF a′ a″) (swapF-b a a′))
                                                (swapF-o a′ a″ a aa′ aa″)))
                                (swp≡ (swapF-o a′ a″ a aa′ aa″) (swapF-a a′ a″)))) ⟩
    NEG a′ ⊙ (NEG a ⊙ (NEG a ⊙ SWP a a″))
      ≈⟨ ⊙-cong (≐-refl {NEG a′}) (neg-drop a (SWP a a″)) ⟩
    NEG a′ ⊙ SWP a a″ ∎
-- (25), (26): the lower index moves up.
sound-ax (r25 a a′ c s lt p) = ≐-sym (begin
  sp (zx a′ a a′) ⊙ (sp (zx a′ a′ c) ⊙ sp (zx a a a′))
    ≈⟨ ⊙-cong (sp-zx a′ a a′ aa′) (⊙-cong (sp-zx a′ a′ c a′c) (sp-zx a a a′ aa′)) ⟩
  L a′ a a′ ⊙ (L a′ a′ c ⊙ L a a a′)
    ≈⟨ conj-L a′ a a′ a′ a′ c a ⟩
  NEG a′ ⊙ (NEG (swapF a a′ a′)
           ⊙ (NEG (swapF a a′ (swapF a′ c a)) ⊙ SWP (swapF a a′ a′) (swapF a a′ c)))
    ≈⟨ ⊙-cong (≐-refl {NEG a′})
              (⊙-cong (neg≡ (swapF-b a a′))
                      (⊙-cong (neg≡ (Eq.trans (Eq.cong (swapF a a′)
                                                (swapF-o a′ c a aa′ ac))
                                              (swapF-a a a′)))
                              (swp≡ (swapF-b a a′)
                                    (swapF-o a a′ c (≢sym ac) (≢sym a′c))))) ⟩
  NEG a′ ⊙ (NEG a ⊙ (NEG a′ ⊙ SWP a c))
    ≈⟨ neg-sandwich a′ a (SWP a c) ⟩
  NEG a ⊙ SWP a c
    ≈⟨ ≐-sym (sp-zx a a c ac) ⟩
  sp (zx a a c) ∎)
  where
  aa′ = Succ≢ s
  a′c = <≢ lt
  ac  = <≢ (<-trans (Succ< s) lt)
sound-ax (r26 a a′ c s lt p) = ≐-sym (begin
  sp (zx a′ a a′) ⊙ (sp (zx c a′ c) ⊙ sp (zx a a a′))
    ≈⟨ ⊙-cong (sp-zx a′ a a′ aa′) (⊙-cong (sp-zx c a′ c a′c) (sp-zx a a a′ aa′)) ⟩
  L a′ a a′ ⊙ (L c a′ c ⊙ L a a a′)
    ≈⟨ conj-L a′ a a′ c a′ c a ⟩
  NEG a′ ⊙ (NEG (swapF a a′ c)
           ⊙ (NEG (swapF a a′ (swapF a′ c a)) ⊙ SWP (swapF a a′ a′) (swapF a a′ c)))
    ≈⟨ ⊙-cong (≐-refl {NEG a′})
              (⊙-cong (neg≡ (swapF-o a a′ c (≢sym ac) (≢sym a′c)))
                      (⊙-cong (neg≡ (Eq.trans (Eq.cong (swapF a a′)
                                                (swapF-o a′ c a aa′ ac))
                                              (swapF-a a a′)))
                              (swp≡ (swapF-b a a′)
                                    (swapF-o a a′ c (≢sym ac) (≢sym a′c))))) ⟩
  NEG a′ ⊙ (NEG c ⊙ (NEG a′ ⊙ SWP a c))
    ≈⟨ neg-sandwich a′ c (SWP a c) ⟩
  NEG c ⊙ SWP a c
    ≈⟨ ≐-sym (sp-zx c a c ac) ⟩
  sp (zx c a c) ∎)
  where
  aa′ = Succ≢ s
  a′c = <≢ lt
  ac  = <≢ (<-trans (Succ< s) lt)
-- (27), (28): the upper index moves down.
sound-ax (r27 a c′ c s lt p) = ≐-sym (begin
  sp (zx c′ c′ c) ⊙ (sp (zx a a c′) ⊙ sp (zx c c′ c))
    ≈⟨ ⊙-cong (sp-zx c′ c′ c c′c) (⊙-cong (sp-zx a a c′ ac′) (sp-zx c c′ c c′c)) ⟩
  L c′ c′ c ⊙ (L a a c′ ⊙ L c c′ c)
    ≈⟨ conj-L c′ c′ c a a c′ c ⟩
  NEG c′ ⊙ (NEG (swapF c′ c a)
           ⊙ (NEG (swapF c′ c (swapF a c′ c)) ⊙ SWP (swapF c′ c a) (swapF c′ c c′)))
    ≈⟨ ⊙-cong (≐-refl {NEG c′})
              (⊙-cong (neg≡ (swapF-o c′ c a ac′ ac))
                      (⊙-cong (neg≡ (Eq.trans (Eq.cong (swapF c′ c)
                                                (swapF-o a c′ c (≢sym ac) (≢sym c′c)))
                                              (swapF-b c′ c)))
                              (swp≡ (swapF-o c′ c a ac′ ac) (swapF-a c′ c)))) ⟩
  NEG c′ ⊙ (NEG a ⊙ (NEG c′ ⊙ SWP a c))
    ≈⟨ neg-sandwich c′ a (SWP a c) ⟩
  NEG a ⊙ SWP a c
    ≈⟨ ≐-sym (sp-zx a a c ac) ⟩
  sp (zx a a c) ∎)
  where
  c′c = Succ≢ s
  ac  = <≢ (<-trans (n<1+n (toℕ a)) lt)
  ac′ = <≢ (≤-pred (Eq.subst (suc (toℕ a) <_) s lt))
sound-ax (r28 a c′ c s lt p) = ≐-sym (begin
  sp (zx c′ c′ c) ⊙ (sp (zx c′ a c′) ⊙ sp (zx c c′ c))
    ≈⟨ ⊙-cong (sp-zx c′ c′ c c′c) (⊙-cong (sp-zx c′ a c′ ac′) (sp-zx c c′ c c′c)) ⟩
  L c′ c′ c ⊙ (L c′ a c′ ⊙ L c c′ c)
    ≈⟨ conj-L c′ c′ c c′ a c′ c ⟩
  NEG c′ ⊙ (NEG (swapF c′ c c′)
           ⊙ (NEG (swapF c′ c (swapF a c′ c)) ⊙ SWP (swapF c′ c a) (swapF c′ c c′)))
    ≈⟨ ⊙-cong (≐-refl {NEG c′})
              (⊙-cong (neg≡ (swapF-a c′ c))
                      (⊙-cong (neg≡ (Eq.trans (Eq.cong (swapF c′ c)
                                                (swapF-o a c′ c (≢sym ac) (≢sym c′c)))
                                              (swapF-b c′ c)))
                              (swp≡ (swapF-o c′ c a ac′ ac) (swapF-a c′ c)))) ⟩
  NEG c′ ⊙ (NEG c ⊙ (NEG c′ ⊙ SWP a c))
    ≈⟨ neg-sandwich c′ c (SWP a c) ⟩
  NEG c ⊙ SWP a c
    ≈⟨ ≐-sym (sp-zx c a c ac) ⟩
  sp (zx c a c) ∎)
  where
  c′c = Succ≢ s
  ac  = <≢ (<-trans (n<1+n (toℕ a)) lt)
  ac′ = <≢ (≤-pred (Eq.subst (suc (toℕ a) <_) s lt))
-- (29): the two sign choices on a consecutive pair are inverse.
sound-ax (r29 a a′ s) = begin
  sp (zx a a a′) ⊙ sp (zx a′ a a′)
    ≈⟨ ⊙-cong (sp-zx a a a′ aa′) (sp-zx a′ a a′ aa′) ⟩
  L a a a′ ⊙ L a′ a a′
    ≈⟨ prod-L a a a′ a′ a a′ ⟩
  NEG a ⊙ (NEG (swapF a a′ a′) ⊙ (SWP a a′ ⊙ SWP a a′))
    ≈⟨ ⊙-cong (≐-refl {NEG a})
              (⊙-cong (neg≡ (swapF-b a a′)) (SWP-invol a a′)) ⟩
  NEG a ⊙ (NEG a ⊙ idSP)
    ≈⟨ neg-drop a idSP ⟩
  idSP ∎
  where aa′ = Succ≢ s
-- (30): a sign on neither index splits off.
sound-ax (r30 c a b ab ca cb) = ≐-sym (begin
  (NEG c ⊙ NEG a) ⊙ sp (zx a a b)
    ≈⟨ ⊙-cong (≐-refl {NEG c ⊙ NEG a}) (sp-zx a a b ab) ⟩
  (NEG c ⊙ NEG a) ⊙ (NEG a ⊙ SWP a b)
    ≈⟨ ⊙-assoc (NEG c) (NEG a) (NEG a ⊙ SWP a b) ⟩
  NEG c ⊙ (NEG a ⊙ (NEG a ⊙ SWP a b))
    ≈⟨ ⊙-cong (≐-refl {NEG c}) (neg-drop a (SWP a b)) ⟩
  NEG c ⊙ SWP a b
    ≈⟨ ≐-sym (sp-zx c a b ab) ⟩
  sp (zx c a b) ∎)
-- (31): a sign crosses a letter, its index transposed.
sound-ax (r31 a a′ c s ca ca′) = ≐-trans lhs (≐-sym rhs)
  where
  aa′ = Succ≢ s

  lhs : (NEG a′ ⊙ NEG c) ⊙ sp (zx a a a′) ≐ NEG a ⊙ (NEG a′ ⊙ (NEG c ⊙ SWP a a′))
  lhs = begin
    (NEG a′ ⊙ NEG c) ⊙ sp (zx a a a′)
      ≈⟨ ⊙-cong (≐-refl {NEG a′ ⊙ NEG c}) (sp-zx a a a′ aa′) ⟩
    (NEG a′ ⊙ NEG c) ⊙ (NEG a ⊙ SWP a a′)
      ≈⟨ ⊙-assoc (NEG a′) (NEG c) (NEG a ⊙ SWP a a′) ⟩
    NEG a′ ⊙ (NEG c ⊙ (NEG a ⊙ SWP a a′))
      ≈⟨ ⊙-cong (≐-refl {NEG a′}) (neg-hop c a (SWP a a′)) ⟩
    NEG a′ ⊙ (NEG a ⊙ (NEG c ⊙ SWP a a′))
      ≈⟨ neg-hop a′ a (NEG c ⊙ SWP a a′) ⟩
    NEG a ⊙ (NEG a′ ⊙ (NEG c ⊙ SWP a a′)) ∎

  rhs : sp (zx a a a′) ⊙ (NEG a ⊙ NEG c) ≐ NEG a ⊙ (NEG a′ ⊙ (NEG c ⊙ SWP a a′))
  rhs = begin
    sp (zx a a a′) ⊙ (NEG a ⊙ NEG c)
      ≈⟨ ⊙-cong (sp-zx a a a′ aa′) (≐-refl {NEG a ⊙ NEG c}) ⟩
    (NEG a ⊙ SWP a a′) ⊙ (NEG a ⊙ NEG c)
      ≈⟨ ⊙-assoc (NEG a) (SWP a a′) (NEG a ⊙ NEG c) ⟩
    NEG a ⊙ (SWP a a′ ⊙ (NEG a ⊙ NEG c))
      ≈⟨ ⊙-cong (≐-refl {NEG a})
                (hop (SWP a a′) (NEG a) (SWP a a′) (NEG (swapF a a′ a)) (NEG c)
                     (SWP-NEG a a′ a)) ⟩
    NEG a ⊙ (NEG (swapF a a′ a) ⊙ (SWP a a′ ⊙ NEG c))
      ≈⟨ ⊙-cong (≐-refl {NEG a})
                (⊙-cong (neg≡ (swapF-a a a′))
                        (≐-trans (SWP-NEG a a′ c)
                                 (⊙-cong (neg≡ (swapF-o a a′ c ca ca′))
                                         (≐-refl {SWP a a′})))) ⟩
    NEG a ⊙ (NEG a′ ⊙ (NEG c ⊙ SWP a a′)) ∎
-- (32): letters on disjoint consecutive pairs commute.
sound-ax (r32 a a′ b b′ s s′ lt) = ≐-trans lhs (≐-sym rhs)
  where
  aa′  = Succ≢ s
  bb′  = Succ≢ s′
  a′<b = lt
  a<b  = <-trans (Succ< s) lt
  a<b′ = <-trans a<b (Succ< s′)
  a′<b′ = <-trans lt (Succ< s′)

  lhs : sp (zx a a a′) ⊙ sp (zx b b b′) ≐ NEG a ⊙ (NEG b ⊙ (SWP a a′ ⊙ SWP b b′))
  lhs = begin
    sp (zx a a a′) ⊙ sp (zx b b b′)
      ≈⟨ ⊙-cong (sp-zx a a a′ aa′) (sp-zx b b b′ bb′) ⟩
    L a a a′ ⊙ L b b b′
      ≈⟨ prod-L a a a′ b b b′ ⟩
    NEG a ⊙ (NEG (swapF a a′ b) ⊙ (SWP a a′ ⊙ SWP b b′))
      ≈⟨ ⊙-cong (≐-refl {NEG a})
                (⊙-cong (neg≡ (swapF-o a a′ b (≢sym (<≢ a<b)) (≢sym (<≢ a′<b))))
                        (≐-refl {SWP a a′ ⊙ SWP b b′})) ⟩
    NEG a ⊙ (NEG b ⊙ (SWP a a′ ⊙ SWP b b′)) ∎

  rhs : sp (zx b b b′) ⊙ sp (zx a a a′) ≐ NEG a ⊙ (NEG b ⊙ (SWP a a′ ⊙ SWP b b′))
  rhs = begin
    sp (zx b b b′) ⊙ sp (zx a a a′)
      ≈⟨ ⊙-cong (sp-zx b b b′ bb′) (sp-zx a a a′ aa′) ⟩
    L b b b′ ⊙ L a a a′
      ≈⟨ prod-L b b b′ a a a′ ⟩
    NEG b ⊙ (NEG (swapF b b′ a) ⊙ (SWP b b′ ⊙ SWP a a′))
      ≈⟨ ⊙-cong (≐-refl {NEG b})
                (⊙-cong (neg≡ (swapF-o b b′ a (<≢ a<b) (<≢ a<b′)))
                        (SWP-comm b b′ a a′ (<≢ a<b) (<≢ a<b′)
                                  (<≢ a′<b) (<≢ a′<b′))) ⟩
    NEG b ⊙ (NEG a ⊙ (SWP a a′ ⊙ SWP b b′))
      ≈⟨ neg-hop b a (SWP a a′ ⊙ SWP b b′) ⟩
    NEG a ⊙ (NEG b ⊙ (SWP a a′ ⊙ SWP b b′)) ∎
-- (33): a transposition does not care which way round it is written.
sound-ax (r33 b a) = go (a ≟ b)
  where
  go : Dec (a ≡ b) → sp (zx b a b) ≐ sp (zx b b a)
  go (yes Eq.refl) = ≐-refl
  go (no ne) =
    ≐-trans (sp-zx b a b ne)
            (≐-trans (⊙-cong (≐-refl {NEG b}) (SWP-sym a b))
                     (≐-sym (sp-zx b b a (≢sym ne))))
-- (34): a double exchange is two letters, the signs cancelling.
sound-ax (r34 a b c d ab cd) = ≐-sym (begin
  sp (zx a a b) ⊙ sp (zx b c d)
    ≈⟨ ⊙-cong (sp-zx a a b ab) (sp-zx b c d cd) ⟩
  L a a b ⊙ L b c d
    ≈⟨ prod-L a a b b c d ⟩
  NEG a ⊙ (NEG (swapF a b b) ⊙ (SWP a b ⊙ SWP c d))
    ≈⟨ ⊙-cong (≐-refl {NEG a})
              (⊙-cong (neg≡ (swapF-b a b)) (≐-refl {SWP a b ⊙ SWP c d})) ⟩
  NEG a ⊙ (NEG a ⊙ (SWP a b ⊙ SWP c d))
    ≈⟨ neg-drop a (SWP a b ⊙ SWP c d) ⟩
  SWP a b ⊙ SWP c d
    ≈⟨ ≐-sym (sp-xx a b c d ab cd) ⟩
  sp (xx a b c d) ∎)

-- And so the whole congruence of the fragment is interpreted.
sound : ∀ {u v : W} → PB._≈_ (m PF,_===_) u v → sp u ≐ sp v
sound PB.refl                 = ≐-refl
sound (PB.sym e)              = ≐-sym (sound e)
sound (PB.trans e e′)         = ≐-trans (sound e) (sound e′)
sound (PB.cong e e′)          = ⊙-cong (sound e) (sound e′)
sound (PB.assoc {w} {v} {u})  = ⊙-assoc (sp w) (sp v) (sp u)
sound (PB.left-unit {w})      = ⊙-idˡ (sp w)
sound (PB.right-unit {w})     = ⊙-idʳ (sp w)
sound (PB.axiom a)            = sound-ax a

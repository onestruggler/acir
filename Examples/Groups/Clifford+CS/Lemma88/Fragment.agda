------------------------------------------------------------------------
-- Presentations of groups
--
-- The K-free rules of P′ from the facts about consecutive letters
--
-- The decoding (Lemma88.Chains) writes every letter of P′ as a word in
-- the letters on consecutive indices.  Given a presentation Γ and the
-- facts `Facts` about those letters on N indices — the phase pairs
-- commute, have order four and are inverted by their flips, the two
-- rotations are inverse, a phase pair squared is a rotation squared,
-- the conjugations px-conj₂ on one pair and px-conj on two adjacent
-- pairs, far letters commute, and the braid — every rule of the
-- K-free fragment (Auxiliary.Fragment) decodes to an equation in Γ.
-- This is the generic half of Lemma 8.8; the facts are what is left to
-- prove at each width.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc ; _<_ ; _≤_)
open import Data.Sum using (_⊎_)
open import Word.Base using (Word ; WRel ; ε ; _•_)

import Presentation.Base as PB

module Examples.Groups.Clifford+CS.Lemma88.Fragment
  {X : Set} (Γ : WRel X) (N : ℕ)
  (p p′ l h k : ℕ → Word X) where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (zero ; _+_ ; _∸_ ; _<ᵇ_ ; _≡ᵇ_ ; z≤n ; s≤s)
open import Data.Nat.Properties as NP using ()
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using ([_]ʷ ; _ʷ ; _^_)

open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Relation.Nullary.Decidable using (recompute ; yes ; no)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)

open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (_F,_===_)
open import Examples.Groups.Clifford+CS.Lemma88.Chains p p′ l h k

open _F,_===_

open PB Γ using (_≈_)

------------------------------------------------------------------------
-- The facts

record Facts : Set where
  field
    p-inv   : ∀ {i} → suc i < N → p i • p′ i ≈ ε
    p′-inv  : ∀ {i} → suc i < N → p′ i • p i ≈ ε
    p-ord   : ∀ {i} → suc i < N → p i ^ 4 ≈ ε
    p-comm  : ∀ {i j} → suc i < N → suc j < N → p i • p j ≈ p j • p i
    sq      : ∀ {i} → suc i < N → p i • p i ≈ l i • l i
    l-inv   : ∀ {i} → suc i < N → l i • h i ≈ ε
    h-inv   : ∀ {i} → suc i < N → h i • l i ≈ ε
    conj₂   : ∀ {i} → suc i < N → p i • l i ≈ l i • p′ i
    conj-up : ∀ {i} → suc (suc i) < N → p (suc i) • l i ≈ l i • p i • p (suc i)
    conj-dn : ∀ {i} → suc (suc i) < N → p′ i • p′ (suc i) • l (suc i) ≈ l (suc i) • p′ i
    far-pl  : ∀ {i j} → suc i < N → suc j < N → suc (suc i) ≤ j ⊎ suc (suc j) ≤ i →
              p i • l j ≈ l j • p i
    far-ll  : ∀ {i j} → suc j < N → suc (suc i) ≤ j → l i • l j ≈ l j • l i
    braid   : ∀ {i} → suc (suc i) < N → l i • l (suc i) • l i ≈ l (suc i) • l i • l (suc i)

module Proofs (F : Facts) where

  open Facts F
  open Tools Γ hiding (_≈_)

  private
    variable
      x y z w x′ : Word X

  ----------------------------------------------------------------------
  -- Booleans and arithmetic

  lt-true : ∀ {m n} → m < n → (m <ᵇ n) ≡ true
  lt-true {zero}  {suc n} _         = Eq.refl
  lt-true {suc m} {suc n} (s≤s le) = lt-true le

  lt-false : ∀ {m n} → n ≤ m → (m <ᵇ n) ≡ false
  lt-false {zero}  {zero}  z≤n      = Eq.refl
  lt-false {suc m} {zero}  z≤n      = Eq.refl
  lt-false {suc m} {suc n} (s≤s le) = lt-false le

  eq-true : ∀ n → (n ≡ᵇ n) ≡ true
  eq-true zero    = Eq.refl
  eq-true (suc n) = eq-true n

  eq-false : ∀ {m n} → m ≢ n → (m ≡ᵇ n) ≡ false
  eq-false {zero}  {zero}  ne = ⊥-elim (ne Eq.refl)
  eq-false {zero}  {suc n} ne = Eq.refl
  eq-false {suc m} {zero}  ne = Eq.refl
  eq-false {suc m} {suc n} ne = eq-false (λ e → ne (Eq.cong suc e))

  -- The first pair of a valid chain is valid.
  vhead : ∀ a e → a + suc e < N → suc a < N
  vhead a e v = NP.≤-trans (s≤s (NP.≤-trans (s≤s (NP.m≤m+n a e)) (NP.≤-reflexive (Eq.sym (NP.+-suc a e))))) v

  ----------------------------------------------------------------------
  -- Words: commutation, inverses

  Comm : Word X → Word X → Set
  Comm x y = x • y ≈ y • x

  comm-sym : Comm x y → Comm y x
  comm-sym = sym

  comm-ε : Comm ε x
  comm-ε = trans left-unit (sym right-unit)

  comm-• : Comm x z → Comm y z → Comm (x • y) z
  comm-• {x} {z} {y} cx cy = begin
    (x • y) • z  ≈⟨ assoc ⟩
    x • (y • z)  ≈⟨ back x cy ⟩
    x • (z • y)  ≈⟨ sym assoc ⟩
    (x • z) • y  ≈⟨ front y cx ⟩
    (z • x) • y  ≈⟨ assoc ⟩
    z • (x • y)  ∎

  comm-•ʳ : Comm z x → Comm z y → Comm z (x • y)
  comm-•ʳ cx cy = comm-sym (comm-• (comm-sym cx) (comm-sym cy))

  -- An inverse commutes with what commutes with the element.
  comm-inv : x • x′ ≈ ε → x′ • x ≈ ε → Comm x z → Comm x′ z
  comm-inv {x} {x′} {z} r l c = begin
    x′ • z               ≈⟨ sym right-unit ⟩
    (x′ • z) • ε         ≈⟨ back (x′ • z) (sym r) ⟩
    (x′ • z) • (x • x′)  ≈⟨ assoc ⟩
    x′ • (z • (x • x′))  ≈⟨ back x′ (sym assoc) ⟩
    x′ • ((z • x) • x′)  ≈⟨ back x′ (front x′ (sym c)) ⟩
    x′ • ((x • z) • x′)  ≈⟨ back x′ assoc ⟩
    x′ • (x • (z • x′))  ≈⟨ sym assoc ⟩
    (x′ • x) • (z • x′)  ≈⟨ front (z • x′) l ⟩
    ε • (z • x′)         ≈⟨ left-unit ⟩
    z • x′               ∎

  -- A right inverse is a left inverse's twin.
  inv-unique : x • y ≈ ε → w • x ≈ ε → y ≈ w
  inv-unique {x} {y} {w} r l = begin
    y              ≈⟨ sym left-unit ⟩
    ε • y          ≈⟨ front y (sym l) ⟩
    (w • x) • y    ≈⟨ assoc ⟩
    w • (x • y)    ≈⟨ back w r ⟩
    w • ε          ≈⟨ right-unit ⟩
    w              ∎

  ----------------------------------------------------------------------
  -- The phase pairs

  -- Everything here commutes with every valid phase pair.
  AllP : Word X → Set
  AllP z = ∀ {j} → suc j < N → Comm (p j) z

  allP′ : AllP z → ∀ {j} → suc j < N → Comm (p′ j) z
  allP′ a v = comm-inv (p-inv v) (p′-inv v) (a v)

  -- A chain whose indices are valid commutes with what all phase pairs do.
  up-comm : ∀ a e → a + e < N → AllP z → Comm (pp-up a e) z
  up-comm a zero    v A = comm-ε
  up-comm a (suc e) v A =
    comm-• (A (vhead a e v))
           (up-comm (suc a) e (Eq.subst (_< N) (NP.+-suc a e) v) A)

  dn-comm : ∀ a e → a + e < N → AllP z → Comm (pp-dn a e) z
  dn-comm a zero    v A = comm-ε
  dn-comm a (suc e) v A =
    comm-• (allP′ A (vhead a e v))
           (dn-comm (suc a) e (Eq.subst (_< N) (NP.+-suc a e) v) A)

  allP-p : ∀ {i} → suc i < N → AllP (p i)
  allP-p v w = p-comm w v

  allP-p′ : ∀ {i} → suc i < N → AllP (p′ i)
  allP-p′ v w = comm-sym (comm-inv (p-inv v) (p′-inv v) (p-comm v w))

  allP-• : AllP x → AllP y → AllP (x • y)
  allP-• A B w = comm-•ʳ (A w) (B w)

  allP-up : ∀ a e → a + e < N → AllP (pp-up a e)
  allP-up a e v w = comm-sym (up-comm a e v (allP-p w))

  allP-dn : ∀ a e → a + e < N → AllP (pp-dn a e)
  allP-dn a e v w = comm-sym (dn-comm a e v (allP-p w))

  -- Splitting a chain.
  up-+ : ∀ a e f → pp-up a (e + f) ≈ pp-up a e • pp-up (a + e) f
  up-+ a zero f rewrite NP.+-identityʳ a = sym left-unit
  up-+ a (suc e) f = begin
    p a • pp-up (suc a) (e + f)                       ≈⟨ back (p a) (up-+ (suc a) e f) ⟩
    p a • (pp-up (suc a) e • pp-up (suc a + e) f)     ≈⟨ sym assoc ⟩
    (p a • pp-up (suc a) e) • pp-up (suc a + e) f     ≡⟨ Eq.cong (λ t → (p a • pp-up (suc a) e) • pp-up t f) (Eq.sym (NP.+-suc a e)) ⟩
    (p a • pp-up (suc a) e) • pp-up (a + suc e) f     ∎

  dn-+ : ∀ a e f → pp-dn a (e + f) ≈ pp-dn a e • pp-dn (a + e) f
  dn-+ a zero f rewrite NP.+-identityʳ a = sym left-unit
  dn-+ a (suc e) f = begin
    p′ a • pp-dn (suc a) (e + f)                      ≈⟨ back (p′ a) (dn-+ (suc a) e f) ⟩
    p′ a • (pp-dn (suc a) e • pp-dn (suc a + e) f)    ≈⟨ sym assoc ⟩
    (p′ a • pp-dn (suc a) e) • pp-dn (suc a + e) f    ≡⟨ Eq.cong (λ t → (p′ a • pp-dn (suc a) e) • pp-dn t f) (Eq.sym (NP.+-suc a e)) ⟩
    (p′ a • pp-dn (suc a) e) • pp-dn (a + suc e) f    ∎

  -- A chain and its inverse cancel, in either order.
  up-dn : ∀ a e → a + e < N → pp-up a e • pp-dn a e ≈ ε
  up-dn a zero v = left-unit
  up-dn a (suc e) v = begin
    (p a • U) • (p′ a • D)    ≈⟨ assoc ⟩
    p a • (U • (p′ a • D))    ≈⟨ back (p a) (sym assoc) ⟩
    p a • ((U • p′ a) • D)    ≈⟨ back (p a) (front D (up-comm (suc a) e v′ (allP-p′ va))) ⟩
    p a • ((p′ a • U) • D)    ≈⟨ back (p a) assoc ⟩
    p a • (p′ a • (U • D))    ≈⟨ sym assoc ⟩
    (p a • p′ a) • (U • D)    ≈⟨ cong (p-inv va) (up-dn (suc a) e v′) ⟩
    ε • ε                     ≈⟨ left-unit ⟩
    ε                         ∎
    where
      U = pp-up (suc a) e
      D = pp-dn (suc a) e
      va = vhead a e v
      v′ = Eq.subst (_< N) (NP.+-suc a e) v

  dn-up : ∀ a e → a + e < N → pp-dn a e • pp-up a e ≈ ε
  dn-up a zero v = left-unit
  dn-up a (suc e) v = begin
    (p′ a • D) • (p a • U)    ≈⟨ assoc ⟩
    p′ a • (D • (p a • U))    ≈⟨ back (p′ a) (sym assoc) ⟩
    p′ a • ((D • p a) • U)    ≈⟨ back (p′ a) (front U (dn-comm (suc a) e v′ (allP-p va))) ⟩
    p′ a • ((p a • D) • U)    ≈⟨ back (p′ a) assoc ⟩
    p′ a • (p a • (D • U))    ≈⟨ sym assoc ⟩
    (p′ a • p a) • (D • U)    ≈⟨ cong (p′-inv va) (dn-up (suc a) e v′) ⟩
    ε • ε                     ≈⟨ left-unit ⟩
    ε                         ∎
    where
      U = pp-up (suc a) e
      D = pp-dn (suc a) e
      va = vhead a e v
      v′ = Eq.subst (_< N) (NP.+-suc a e) v

  -- The two readings of dPP.
  dPP-up : ∀ {a b} → a ≤ b → dPP a b ≡ pp-up a (b ∸ a)
  dPP-up {a} {b} le with NP.m≤n⇒m<n∨m≡n le
  ... | inj₁ lt rewrite lt-true lt = Eq.refl
  ... | inj₂ Eq.refl rewrite lt-false (NP.≤-refl {a}) | NP.n∸n≡0 a = Eq.refl

  dPP-dn : ∀ {a b} → b ≤ a → dPP a b ≡ pp-dn b (a ∸ b)
  dPP-dn {a} {b} le rewrite lt-false le = Eq.refl

  ----------------------------------------------------------------------
  -- Arithmetic of the chains

  sA∸A : ∀ a → suc a ∸ a ≡ 1
  sA∸A zero    = Eq.refl
  sA∸A (suc a) = sA∸A a

  ∸-suc : ∀ {a c} → a < c → c ∸ a ≡ suc (c ∸ suc a)
  ∸-suc {zero}  {suc c} _        = Eq.refl
  ∸-suc {suc a} {suc c} (s≤s lt) = ∸-suc lt

  split∸ : ∀ {a b c} → a ≤ b → b ≤ c → (b ∸ a) + (c ∸ b) ≡ c ∸ a
  split∸ {a} {b} {c} ab bc = Eq.trans (Eq.sym (NP.m+n∸m≡n a _)) (Eq.cong (_∸ a) e)
    where
      e : a + ((b ∸ a) + (c ∸ b)) ≡ c
      e = Eq.trans (Eq.sym (NP.+-assoc a (b ∸ a) (c ∸ b)))
            (Eq.trans (Eq.cong (_+ (c ∸ b)) (NP.m+[n∸m]≡n ab)) (NP.m+[n∸m]≡n bc))

  -- The chain between two valid indices is valid.
  vch : ∀ {a b} → a ≤ b → b < N → a + (b ∸ a) < N
  vch ab bN = Eq.subst (_< N) (Eq.sym (NP.m+[n∸m]≡n ab)) bN

  T1 : ∀ {a b c} → a ≤ b → b ≤ c → pp-up a (b ∸ a) • pp-up b (c ∸ b) ≈ pp-up a (c ∸ a)
  T1 {a} {b} {c} ab bc =
    Eq.subst₂ (λ u v → pp-up a (b ∸ a) • pp-up u (c ∸ b) ≈ pp-up a v)
      (NP.m+[n∸m]≡n ab) (split∸ ab bc) (sym (up-+ a (b ∸ a) (c ∸ b)))

  D1 : ∀ {a b c} → a ≤ b → b ≤ c → pp-dn a (b ∸ a) • pp-dn b (c ∸ b) ≈ pp-dn a (c ∸ a)
  D1 {a} {b} {c} ab bc =
    Eq.subst₂ (λ u v → pp-dn a (b ∸ a) • pp-dn u (c ∸ b) ≈ pp-dn a v)
      (NP.m+[n∸m]≡n ab) (split∸ ab bc) (sym (dn-+ a (b ∸ a) (c ∸ b)))

  ----------------------------------------------------------------------
  -- pp-tele

  tele₂ : ∀ {a b c} → b < N → a ≤ c → c ≤ b →
          pp-up a (b ∸ a) • pp-dn c (b ∸ c) ≈ pp-up a (c ∸ a)
  tele₂ {a} {b} {c} bN ac cb = begin
    pp-up a (b ∸ a) • pp-dn c (b ∸ c)                       ≈⟨ front _ (sym (T1 ac cb)) ⟩
    (pp-up a (c ∸ a) • pp-up c (b ∸ c)) • pp-dn c (b ∸ c)   ≈⟨ assoc ⟩
    pp-up a (c ∸ a) • (pp-up c (b ∸ c) • pp-dn c (b ∸ c))   ≈⟨ back _ (up-dn c (b ∸ c) (vch cb bN)) ⟩
    pp-up a (c ∸ a) • ε                                     ≈⟨ right-unit ⟩
    pp-up a (c ∸ a)                                         ∎

  tele₃ : ∀ {a b c} → a < N → b < N → c ≤ a → a ≤ b →
          pp-up a (b ∸ a) • pp-dn c (b ∸ c) ≈ pp-dn c (a ∸ c)
  tele₃ {a} {b} {c} aN bN ca ab = begin
    U • pp-dn c (b ∸ c)        ≈⟨ back U (sym (D1 ca ab)) ⟩
    U • (D′ • D″)              ≈⟨ sym assoc ⟩
    (U • D′) • D″              ≈⟨ front D″ (up-comm a (b ∸ a) (vch ab bN) (allP-dn c (a ∸ c) (vch ca aN))) ⟩
    (D′ • U) • D″              ≈⟨ assoc ⟩
    D′ • (U • D″)              ≈⟨ back D′ (up-dn a (b ∸ a) (vch ab bN)) ⟩
    D′ • ε                     ≈⟨ right-unit ⟩
    D′                         ∎
    where
      U = pp-up a (b ∸ a); D′ = pp-dn c (a ∸ c); D″ = pp-dn a (b ∸ a)

  tele₄ : ∀ {a b c} → a < N → b ≤ a → a ≤ c →
          pp-dn b (a ∸ b) • pp-up b (c ∸ b) ≈ pp-up a (c ∸ a)
  tele₄ {a} {b} {c} aN ba ac = begin
    D • pp-up b (c ∸ b)        ≈⟨ back D (sym (T1 ba ac)) ⟩
    D • (U′ • U″)              ≈⟨ sym assoc ⟩
    (D • U′) • U″              ≈⟨ front U″ (dn-up b (a ∸ b) (vch ba aN)) ⟩
    ε • U″                     ≈⟨ left-unit ⟩
    U″                         ∎
    where
      D = pp-dn b (a ∸ b); U′ = pp-up b (a ∸ b); U″ = pp-up a (c ∸ a)

  tele₅ : ∀ {a b c} → a < N → c < N → b ≤ c → c ≤ a →
          pp-dn b (a ∸ b) • pp-up b (c ∸ b) ≈ pp-dn c (a ∸ c)
  tele₅ {a} {b} {c} aN cN bc ca = begin
    pp-dn b (a ∸ b) • U        ≈⟨ front U (sym (D1 bc ca)) ⟩
    (D′ • D″) • U              ≈⟨ assoc ⟩
    D′ • (D″ • U)              ≈⟨ back D′ (dn-comm c (a ∸ c) (vch ca aN) (allP-up b (c ∸ b) (vch bc cN))) ⟩
    D′ • (U • D″)              ≈⟨ sym assoc ⟩
    (D′ • U) • D″              ≈⟨ front D″ (dn-up b (c ∸ b) (vch bc cN)) ⟩
    ε • D″                     ≈⟨ left-unit ⟩
    D″                         ∎
    where
      U = pp-up b (c ∸ b); D′ = pp-dn b (c ∸ b); D″ = pp-dn c (a ∸ c)

  tele₆ : ∀ {a b c} → a < N → b < N → c ≤ b → b ≤ a →
          pp-dn b (a ∸ b) • pp-dn c (b ∸ c) ≈ pp-dn c (a ∸ c)
  tele₆ {a} {b} {c} aN bN cb ba = begin
    pp-dn b (a ∸ b) • pp-dn c (b ∸ c)   ≈⟨ dn-comm b (a ∸ b) (vch ba aN) (allP-dn c (b ∸ c) (vch cb bN)) ⟩
    pp-dn c (b ∸ c) • pp-dn b (a ∸ b)   ≈⟨ D1 cb ba ⟩
    pp-dn c (a ∸ c)                     ∎

  tele : ∀ {a b c} → a < N → b < N → c < N → dPP a b • dPP b c ≈ dPP a c
  tele {a} {b} {c} aN bN cN with NP.≤-total a b | NP.≤-total b c
  ... | inj₁ ab | inj₁ bc
    rewrite dPP-up ab | dPP-up bc | dPP-up (NP.≤-trans ab bc) = T1 ab bc
  ... | inj₁ ab | inj₂ cb with NP.≤-total a c
  ...   | inj₁ ac rewrite dPP-up ab | dPP-dn cb | dPP-up ac = tele₂ bN ac cb
  ...   | inj₂ ca rewrite dPP-up ab | dPP-dn cb | dPP-dn ca = tele₃ aN bN ca ab
  tele {a} {b} {c} aN bN cN | inj₂ ba | inj₁ bc with NP.≤-total a c
  ...   | inj₁ ac rewrite dPP-dn ba | dPP-up bc | dPP-up ac = tele₄ aN ba ac
  ...   | inj₂ ca rewrite dPP-dn ba | dPP-up bc | dPP-dn ca = tele₅ aN cN bc ca
  tele {a} {b} {c} aN bN cN | inj₂ ba | inj₂ cb
    rewrite dPP-dn ba | dPP-dn cb | dPP-dn (NP.≤-trans cb ba) = tele₆ aN bN cb ba

  ----------------------------------------------------------------------
  -- pp-id, pp-comm

  pp-self : ∀ a → dPP a a ≈ ε
  pp-self a rewrite dPP-dn (NP.≤-refl {a}) | NP.n∸n≡0 a = refl

  dPP-comm : ∀ {a b} → a < N → b < N → AllP z → Comm (dPP a b) z
  dPP-comm {_} {a} {b} aN bN A with NP.≤-total a b
  ... | inj₁ ab rewrite dPP-up ab = up-comm a (b ∸ a) (vch ab bN) A
  ... | inj₂ ba rewrite dPP-dn ba = dn-comm b (a ∸ b) (vch ba aN) A

  allP-dPP : ∀ {a b} → a < N → b < N → AllP (dPP a b)
  allP-dPP aN bN w = comm-sym (dPP-comm aN bN (allP-p w))

  ----------------------------------------------------------------------
  -- pp-ord

  sq-• : Comm x y → (x • y) • (x • y) ≈ (x • x) • (y • y)
  sq-• {x} {y} c = begin
    (x • y) • (x • y)    ≈⟨ assoc ⟩
    x • (y • (x • y))    ≈⟨ back x (sym assoc) ⟩
    x • ((y • x) • y)    ≈⟨ back x (front y (sym c)) ⟩
    x • ((x • y) • y)    ≈⟨ back x assoc ⟩
    x • (x • (y • y))    ≈⟨ sym assoc ⟩
    (x • x) • (y • y)    ∎

  ord-• : Comm x y → x ^ 4 ≈ ε → y ^ 4 ≈ ε → (x • y) ^ 4 ≈ ε
  ord-• {x} {y} c ox oy = begin
    (x • y) • ((x • y) • ((x • y) • (x • y)))           ≈⟨ sym assoc ⟩
    ((x • y) • (x • y)) • ((x • y) • (x • y))           ≈⟨ cong (sq-• c) (sq-• c) ⟩
    ((x • x) • (y • y)) • ((x • x) • (y • y))           ≈⟨ sq-• cc ⟩
    ((x • x) • (x • x)) • ((y • y) • (y • y))           ≈⟨ cong assoc assoc ⟩
    (x • (x • (x • x))) • (y • (y • (y • y)))           ≈⟨ cong ox oy ⟩
    ε • ε                                               ≈⟨ left-unit ⟩
    ε                                                   ∎
    where
      cy : Comm x (y • y)
      cy = comm-•ʳ c c
      cc : Comm (x • x) (y • y)
      cc = comm-• cy cy

  ord-inv : x ^ 4 ≈ ε → x • x′ ≈ ε → x′ • x ≈ ε → x′ ^ 4 ≈ ε
  ord-inv {x} {x′} ox r l = begin
    x′ • (x′ • (x′ • x′))                           ≈⟨ sym assoc ⟩
    (x′ • x′) • (x′ • x′)                           ≈⟨ sym right-unit ⟩
    ((x′ • x′) • (x′ • x′)) • ε                     ≈⟨ back _ (sym ox) ⟩
    ((x′ • x′) • (x′ • x′)) • (x • (x • (x • x)))   ≈⟨ back _ (sym assoc) ⟩
    ((x′ • x′) • (x′ • x′)) • ((x • x) • (x • x))   ≈⟨ assoc ⟩
    (x′ • x′) • ((x′ • x′) • ((x • x) • (x • x)))   ≈⟨ back _ (sym assoc) ⟩
    (x′ • x′) • (((x′ • x′) • (x • x)) • (x • x))   ≈⟨ back _ (front _ c2) ⟩
    (x′ • x′) • (ε • (x • x))                       ≈⟨ back _ left-unit ⟩
    (x′ • x′) • (x • x)                             ≈⟨ c2 ⟩
    ε                                               ∎
    where
      c2 : (x′ • x′) • (x • x) ≈ ε
      c2 = begin
        (x′ • x′) • (x • x)    ≈⟨ assoc ⟩
        x′ • (x′ • (x • x))    ≈⟨ back x′ (sym assoc) ⟩
        x′ • ((x′ • x) • x)    ≈⟨ back x′ (front x l) ⟩
        x′ • (ε • x)           ≈⟨ back x′ left-unit ⟩
        x′ • x                 ≈⟨ l ⟩
        ε                      ∎

  ord-ε : ε ^ 4 ≈ ε
  ord-ε = trans left-unit (trans left-unit left-unit)

  up-ord : ∀ a e → a + e < N → pp-up a e ^ 4 ≈ ε
  up-ord a zero    v = ord-ε
  up-ord a (suc e) v =
    ord-• (comm-sym (up-comm (suc a) e v′ (allP-p (vhead a e v)))) (p-ord (vhead a e v))
          (up-ord (suc a) e v′)
    where v′ = Eq.subst (_< N) (NP.+-suc a e) v

  dn-ord : ∀ a e → a + e < N → pp-dn a e ^ 4 ≈ ε
  dn-ord a zero    v = ord-ε
  dn-ord a (suc e) v =
    ord-• (comm-sym (dn-comm (suc a) e v′ (allP-p′ (vhead a e v))))
          (ord-inv (p-ord (vhead a e v)) (p-inv (vhead a e v)) (p′-inv (vhead a e v)))
          (dn-ord (suc a) e v′)
    where v′ = Eq.subst (_< N) (NP.+-suc a e) v

  pp-ord′ : ∀ {a b} → a < N → b < N → dPP a b ^ 4 ≈ ε
  pp-ord′ {a} {b} aN bN with NP.≤-total a b
  ... | inj₁ ab rewrite dPP-up ab = up-ord a (b ∸ a) (vch ab bN)
  ... | inj₂ ba rewrite dPP-dn ba = dn-ord b (a ∸ b) (vch ba aN)

  ----------------------------------------------------------------------
  -- Far letters

  -- A chain commutes with z when every letter in its range does.
  up-commR : ∀ a e → (∀ {j} → a ≤ j → j < a + e → Comm (p j) z) → Comm (pp-up a e) z
  up-commR a zero    A = comm-ε
  up-commR a (suc e) A =
    comm-• (A NP.≤-refl (Eq.subst (a <_) (Eq.sym (NP.+-suc a e)) (s≤s (NP.m≤m+n a e))))
           (up-commR (suc a) e (λ {j} le lt → A (NP.<⇒≤ le) (Eq.subst (λ u → j < u) (Eq.sym (NP.+-suc a e)) lt)))

  dn-commR : ∀ a e → (∀ {j} → a ≤ j → j < a + e → Comm (p′ j) z) → Comm (pp-dn a e) z
  dn-commR a zero    A = comm-ε
  dn-commR a (suc e) A =
    comm-• (A NP.≤-refl (Eq.subst (a <_) (Eq.sym (NP.+-suc a e)) (s≤s (NP.m≤m+n a e))))
           (dn-commR (suc a) e (λ {j} le lt → A (NP.<⇒≤ le) (Eq.subst (λ u → j < u) (Eq.sym (NP.+-suc a e)) lt)))

  -- valid indices below a valid bound
  vb : ∀ {j m} → j < m → m < N → suc j < N
  vb jm mN = NP.≤-<-trans jm mN

  far-p′l : ∀ {i j} → suc i < N → suc j < N → suc (suc i) ≤ j ⊎ suc (suc j) ≤ i →
            Comm (p′ i) (l j)
  far-p′l vi vj f = comm-inv (p-inv vi) (p′-inv vi) (far-pl vi vj f)

  far-ph : ∀ {i j} → suc i < N → suc j < N → suc (suc i) ≤ j ⊎ suc (suc j) ≤ i →
           Comm (p i) (h j)
  far-ph vi vj f = comm-sym (comm-inv (l-inv vj) (h-inv vj) (comm-sym (far-pl vi vj f)))

  far-hl : ∀ {i j} → suc j < N → suc (suc i) ≤ j → Comm (h i) (l j)
  far-hl {i} vj le = comm-inv (l-inv vi) (h-inv vi) (far-ll vj le)
    where vi = NP.<-trans (s≤s (NP.≤-trans (NP.n≤1+n _) le)) vj

  far-lh : ∀ {i j} → suc j < N → suc (suc i) ≤ j → Comm (l j) (h i)
  far-lh vj le = comm-sym (far-hl vj le)

  far-hl′ : ∀ {i j} → suc j < N → suc (suc i) ≤ j → Comm (h j) (l i)
  far-hl′ vj le = comm-inv (l-inv vj) (h-inv vj) (comm-sym (far-ll vj le))

  ----------------------------------------------------------------------
  -- Conjugation by a rotation

  cj : ℕ → Word X → Word X
  cj a w = h a • w • l a

  cj-• : ∀ {a} → suc a < N → cj a (x • y) ≈ cj a x • cj a y
  cj-• {x} {y} {a} v = sym (begin
    (h a • x • l a) • (h a • y • l a)    ≈⟨ assoc ⟩
    h a • ((x • l a) • (h a • y • l a))  ≈⟨ back (h a) assoc ⟩
    h a • (x • (l a • (h a • y • l a)))  ≈⟨ back (h a) (back x (sym assoc)) ⟩
    h a • (x • ((l a • h a) • (y • l a)))  ≈⟨ back (h a) (back x (front _ (l-inv v))) ⟩
    h a • (x • (ε • (y • l a)))          ≈⟨ back (h a) (back x left-unit) ⟩
    h a • (x • (y • l a))                ≈⟨ back (h a) (sym assoc) ⟩
    h a • ((x • y) • l a)                ∎)

  cj-ε : ∀ {a} → suc a < N → cj a ε ≈ ε
  cj-ε {a} v = trans (back (h a) left-unit) (h-inv v)

  cj-far : ∀ {a} → suc a < N → Comm x (l a) → cj a x ≈ x
  cj-far {x} {a} v c = begin
    h a • (x • l a)    ≈⟨ back (h a) c ⟩
    h a • (l a • x)    ≈⟨ sym assoc ⟩
    (h a • l a) • x    ≈⟨ front x (h-inv v) ⟩
    ε • x              ≈⟨ left-unit ⟩
    x                  ∎

  to-cj : ∀ {a} → suc a < N → x • l a ≈ l a • y → cj a x ≈ y
  to-cj {x} {y} {a} v e = begin
    h a • (x • l a)    ≈⟨ back (h a) e ⟩
    h a • (l a • y)    ≈⟨ sym assoc ⟩
    (h a • l a) • y    ≈⟨ front y (h-inv v) ⟩
    ε • y              ≈⟨ left-unit ⟩
    y                  ∎

  from-cj : ∀ {a} → suc a < N → cj a x ≈ y → x • l a ≈ l a • y
  from-cj {x} {y} {a} v e = begin
    x • l a                    ≈⟨ sym left-unit ⟩
    ε • (x • l a)              ≈⟨ front _ (sym (l-inv v)) ⟩
    (l a • h a) • (x • l a)    ≈⟨ assoc ⟩
    l a • (h a • (x • l a))    ≈⟨ back (l a) e ⟩
    l a • y                    ∎

  cj-inv : ∀ {a} → suc a < N → x • y ≈ ε → cj a x • cj a y ≈ ε
  cj-inv {x} {y} {a} v e = trans (sym (cj-• v)) (trans (back (h a) (front (l a) e)) (cj-ε v))

  cj-p : ∀ {a} → suc (suc a) < N → cj a (p (suc a)) ≈ p a • p (suc a)
  cj-p v = to-cj (NP.<-trans (NP.n<1+n _) v) (conj-up v)

  cj-p′ : ∀ {a} → suc (suc a) < N → cj a (p′ (suc a)) ≈ p′ a • p′ (suc a)
  cj-p′ {a} v = inv-unique r l′
    where
      va = NP.<-trans (NP.n<1+n _) v
      r : cj a (p (suc a)) • cj a (p′ (suc a)) ≈ ε
      r = cj-inv va (p-inv v)
      l′ : (p′ a • p′ (suc a)) • cj a (p (suc a)) ≈ ε
      l′ = begin
        (p′ a • p′ (suc a)) • cj a (p (suc a))      ≈⟨ back _ (cj-p v) ⟩
        (p′ a • p′ (suc a)) • (p a • p (suc a))     ≈⟨ assoc ⟩
        p′ a • (p′ (suc a) • (p a • p (suc a)))     ≈⟨ back (p′ a) (sym assoc) ⟩
        p′ a • ((p′ (suc a) • p a) • p (suc a))     ≈⟨ back (p′ a) (front _ (comm-sym (allP-p′ v va))) ⟩
        p′ a • ((p a • p′ (suc a)) • p (suc a))     ≈⟨ back (p′ a) assoc ⟩
        p′ a • (p a • (p′ (suc a) • p (suc a)))     ≈⟨ back (p′ a) (back (p a) (p′-inv v)) ⟩
        p′ a • (p a • ε)                            ≈⟨ back (p′ a) right-unit ⟩
        p′ a • p a                                  ≈⟨ p′-inv va ⟩
        ε                                           ∎

  -- Chains above a + 1 pass the rotation on a.
  above : ∀ {a} f → suc a < N → suc (suc a) + f < N →
          (∀ {j} → suc (suc a) ≤ j → j < suc (suc a) + f → Comm (p j) (l a))
  above {a} f va v le lt =
    far-pl (vb lt v) va (inj₂ le)

  above′ : ∀ {a} f → suc a < N → suc (suc a) + f < N →
           (∀ {j} → suc (suc a) ≤ j → j < suc (suc a) + f → Comm (p′ j) (l a))
  above′ {a} f va v le lt = far-p′l (vb lt v) va (inj₂ le)

  cj-up : ∀ {a} f → suc a + suc f < N → cj a (pp-up (suc a) (suc f)) ≈ pp-up a (suc (suc f))
  cj-up {a} f v = begin
    cj a (p (suc a) • U)          ≈⟨ cj-• va ⟩
    cj a (p (suc a)) • cj a U     ≈⟨ cong (cj-p v2) (cj-far va (up-commR (suc (suc a)) f (above f va v′))) ⟩
    (p a • p (suc a)) • U         ≈⟨ assoc ⟩
    p a • (p (suc a) • U)         ∎
    where
      U = pp-up (suc (suc a)) f
      v′ = Eq.subst (_< N) (NP.+-suc (suc a) f) v
      v2 = NP.≤-trans (s≤s (s≤s (s≤s (NP.m≤m+n a f)))) v′
      va = NP.<-trans (NP.n<1+n _) v2

  cj-dn : ∀ {a} f → suc a + suc f < N → cj a (pp-dn (suc a) (suc f)) ≈ pp-dn a (suc (suc f))
  cj-dn {a} f v = begin
    cj a (p′ (suc a) • D)         ≈⟨ cj-• va ⟩
    cj a (p′ (suc a)) • cj a D    ≈⟨ cong (cj-p′ v2) (cj-far va (dn-commR (suc (suc a)) f (above′ f va v′))) ⟩
    (p′ a • p′ (suc a)) • D       ≈⟨ assoc ⟩
    p′ a • (p′ (suc a) • D)       ∎
    where
      D = pp-dn (suc (suc a)) f
      v′ = Eq.subst (_< N) (NP.+-suc (suc a) f) v
      v2 = NP.≤-trans (s≤s (s≤s (s≤s (NP.m≤m+n a f)))) v′
      va = NP.<-trans (NP.n<1+n _) v2

  ----------------------------------------------------------------------
  -- The signed exchanges

  lo-hi : ∀ a e → a + e < N → dLo a e • dHi a e ≈ ε
  hi-lo : ∀ a e → a + e < N → dHi a e • dLo a e ≈ ε
  lo-hi a zero v                = left-unit
  lo-hi a (suc zero) v          = l-inv (vhead a zero v)
  lo-hi a (suc (suc e)) v       =
    cj-inv (vhead a (suc e) v) (lo-hi (suc a) (suc e) (Eq.subst (_< N) (NP.+-suc a (suc e)) v))
  hi-lo a zero v                = left-unit
  hi-lo a (suc zero) v          = h-inv (vhead a zero v)
  hi-lo a (suc (suc e)) v       =
    cj-inv (vhead a (suc e) v) (hi-lo (suc a) (suc e) (Eq.subst (_< N) (NP.+-suc a (suc e)) v))

  -- From the braid.
  B1 : ∀ {a} → suc (suc a) < N → h a • l (suc a) • l a ≈ l (suc a) • l a • h (suc a)
  B1 {a} v = begin
    h a • (lb • la)                       ≈⟨ back (h a) (sym right-unit) ⟩
    h a • ((lb • la) • ε)                 ≈⟨ back (h a) (back _ (sym (l-inv v))) ⟩
    h a • ((lb • la) • (lb • h b))        ≈⟨ back (h a) (sym assoc) ⟩
    h a • (((lb • la) • lb) • h b)        ≈⟨ back (h a) (front (h b) assoc) ⟩
    h a • ((lb • (la • lb)) • h b)        ≈⟨ back (h a) (front (h b) (sym (braid v))) ⟩
    h a • ((la • (lb • la)) • h b)        ≈⟨ back (h a) assoc ⟩
    h a • (la • ((lb • la) • h b))        ≈⟨ sym assoc ⟩
    (h a • la) • ((lb • la) • h b)        ≈⟨ front _ (h-inv va) ⟩
    ε • ((lb • la) • h b)                 ≈⟨ left-unit ⟩
    (lb • la) • h b                       ≈⟨ assoc ⟩
    lb • (la • h b)                       ∎
    where
      b = suc a; la = l a; lb = l b
      va = NP.<-trans (NP.n<1+n _) v

  lo-shrink : ∀ a e → a + suc (suc e) < N →
              dLo a (suc (suc e)) ≈ l (a + suc e) • dLo a (suc e) • h (a + suc e)
  lo-shrink a zero v rewrite NP.+-suc a zero | NP.+-identityʳ a =
    B1 (Eq.subst (_< N) (Eq.trans (NP.+-suc a 1) (Eq.cong suc (Eq.trans (NP.+-suc a 0) (Eq.cong suc (NP.+-identityʳ a))))) v)
  lo-shrink a (suc e) v = begin
    h a • (dLo (suc a) (suc (suc e)) • l a)                    ≈⟨ back (h a) (front (l a) (lo-shrink (suc a) e v₁)) ⟩
    h a • ((l t • (L • h t)) • l a)                           ≈⟨ back (h a) assoc ⟩
    h a • (l t • ((L • h t) • l a))                           ≈⟨ sym assoc ⟩
    (h a • l t) • ((L • h t) • l a)                           ≈⟨ front _ (comm-sym (far-lh vt le)) ⟩
    (l t • h a) • ((L • h t) • l a)                           ≈⟨ assoc ⟩
    l t • (h a • ((L • h t) • l a))                           ≈⟨ back (l t) (back (h a) assoc) ⟩
    l t • (h a • (L • (h t • l a)))                           ≈⟨ back (l t) (back (h a) (back L (far-hl′ vt le))) ⟩
    l t • (h a • (L • (l a • h t)))                           ≈⟨ back (l t) (back (h a) (sym assoc)) ⟩
    l t • (h a • ((L • l a) • h t))                           ≈⟨ back (l t) (sym assoc) ⟩
    l t • ((h a • (L • l a)) • h t)                           ≡⟨ Eq.cong (λ u → l u • ((h a • (L • l a)) • h u)) tq ⟩
    l (a + suc (suc e)) • ((h a • (L • l a)) • h (a + suc (suc e)))   ∎
    where
      t = suc a + suc e
      L = dLo (suc a) (suc e)
      tq : t ≡ a + suc (suc e)
      tq = Eq.sym (NP.+-suc a (suc e))
      v₁ : suc a + suc (suc e) < N
      v₁ = Eq.subst (_< N) (NP.+-suc a (suc (suc e))) v
      vt : suc t < N
      vt = Eq.subst (_< N) (Eq.trans (NP.+-suc a (suc (suc e))) (Eq.cong suc (NP.+-suc a (suc e)))) v
      le : suc (suc a) ≤ t
      le = s≤s (NP.≤-trans (s≤s (NP.m≤m+n a e)) (NP.≤-reflexive (Eq.sym (NP.+-suc a e))))

  hi-shrink : ∀ a e → a + suc (suc e) < N →
              dHi a (suc (suc e)) ≈ l (a + suc e) • dHi a (suc e) • h (a + suc e)
  hi-shrink a e v = inv-unique (lo-hi a (suc (suc e)) v) (trans (back _ (lo-shrink a e v)) inv′)
    where
      t = a + suc e
      vt : suc t < N
      vt = NP.≤-<-trans (NP.≤-reflexive (Eq.sym (NP.+-suc a (suc e)))) v
      H = dHi a (suc e); L = dLo a (suc e)
      vh : a + suc e < N
      vh = NP.<-trans (NP.≤-reflexive (Eq.sym (NP.+-suc a (suc e)))) v
      inv′ : (l t • H • h t) • (l t • L • h t) ≈ ε
      inv′ = begin
        (l t • H • h t) • (l t • L • h t)      ≈⟨ assoc ⟩
        l t • ((H • h t) • (l t • L • h t))    ≈⟨ back (l t) assoc ⟩
        l t • (H • (h t • (l t • L • h t)))    ≈⟨ back (l t) (back H (sym assoc)) ⟩
        l t • (H • ((h t • l t) • (L • h t)))  ≈⟨ back (l t) (back H (front _ (h-inv vt))) ⟩
        l t • (H • (ε • (L • h t)))            ≈⟨ back (l t) (back H left-unit) ⟩
        l t • (H • (L • h t))                  ≈⟨ back (l t) (sym assoc) ⟩
        l t • ((H • L) • h t)                  ≈⟨ back (l t) (front (h t) (hi-lo a (suc e) vh)) ⟩
        l t • (ε • h t)                        ≈⟨ back (l t) left-unit ⟩
        l t • h t                              ≈⟨ l-inv vt ⟩
        ε                                      ∎

  -- The sign on the upper index: two phase pairs and the lower sign.
  hi-sign : ∀ a e → a + suc e < N →
            dHi a (suc e) ≈ pp-dn a (suc e) • pp-dn a (suc e) • dLo a (suc e)
  hi-sign a zero v = begin
    h a                                     ≈⟨ sym left-unit ⟩
    ε • h a                                 ≈⟨ front _ (sym c4) ⟩
    ((p′ a • p′ a) • (p a • p a)) • h a     ≈⟨ assoc ⟩
    (p′ a • p′ a) • ((p a • p a) • h a)     ≈⟨ back _ (front _ (sq va)) ⟩
    (p′ a • p′ a) • ((l a • l a) • h a)     ≈⟨ back _ assoc ⟩
    (p′ a • p′ a) • (l a • (l a • h a))     ≈⟨ back _ (back (l a) (l-inv va)) ⟩
    (p′ a • p′ a) • (l a • ε)               ≈⟨ back _ right-unit ⟩
    (p′ a • p′ a) • l a                     ≈⟨ assoc ⟩
    p′ a • (p′ a • l a)                     ≈⟨ sym (cong right-unit (front (l a) right-unit)) ⟩
    (p′ a • ε) • ((p′ a • ε) • l a)         ∎
    where
      va = vhead a zero v
      c4 : (p′ a • p′ a) • (p a • p a) ≈ ε
      c4 = begin
        (p′ a • p′ a) • (p a • p a)    ≈⟨ assoc ⟩
        p′ a • (p′ a • (p a • p a))    ≈⟨ back (p′ a) (sym assoc) ⟩
        p′ a • ((p′ a • p a) • p a)    ≈⟨ back (p′ a) (front (p a) (p′-inv va)) ⟩
        p′ a • (ε • p a)               ≈⟨ back (p′ a) left-unit ⟩
        p′ a • p a                     ≈⟨ p′-inv va ⟩
        ε                              ∎
  hi-sign a (suc e) v = begin
    cj a (dHi (suc a) (suc e))                 ≈⟨ back (h a) (front (l a) (hi-sign (suc a) e v₁)) ⟩
    cj a (D • D • L)                           ≈⟨ cj-• va ⟩
    cj a D • cj a (D • L)                      ≈⟨ back _ (cj-• va) ⟩
    cj a D • cj a D • cj a L                   ≈⟨ cong (cj-dn e v₁) (front _ (cj-dn e v₁)) ⟩
    pp-dn a (suc (suc e)) • pp-dn a (suc (suc e)) • dLo a (suc (suc e))   ∎
    where
      D = pp-dn (suc a) (suc e); L = dLo (suc a) (suc e)
      v₁ : suc a + suc e < N
      v₁ = Eq.subst (_< N) (NP.+-suc a (suc e)) v
      va = vhead a (suc e) v

  ----------------------------------------------------------------------
  -- The letters on one pair, read off the decoding

  pp1 : ∀ a → dPP a (suc a) ≡ p a • ε
  pp1 a rewrite lt-true (NP.n<1+n a) | sA∸A a = Eq.refl

  pp1′ : ∀ a → dPP (suc a) a ≡ p′ a • ε
  pp1′ a rewrite lt-false (NP.n≤1+n a) | sA∸A a = Eq.refl

  lo1 : ∀ a → dPX a a (suc a) ≡ l a
  lo1 a rewrite eq-true a | sA∸A a = Eq.refl

  hi1 : ∀ a → dPX (suc a) a (suc a) ≡ h a
  hi1 a rewrite eq-false {suc a} {a} (λ e → NP.<⇒≢ (NP.n<1+n a) (Eq.sym e)) | eq-true (suc a) | sA∸A a = Eq.refl

  loC : ∀ a c → dPX a a c ≡ dLo a (c ∸ a)
  loC a c rewrite eq-true a = Eq.refl

  hiC : ∀ {a c} → a < c → dPX c a c ≡ dHi a (c ∸ a)
  hiC {a} {c} lt rewrite eq-false {c} {a} (λ e → NP.<⇒≢ lt (Eq.sym e)) | eq-true c = Eq.refl

  s∸ : ∀ {a c} → a ≤ c → suc c ∸ a ≡ suc (c ∸ a)
  s∸ {zero}  {c}     _        = Eq.refl
  s∸ {suc a} {suc c} (s≤s le) = s∸ le

  -- A + suc (C ∸ suc A) is C, for A < C.
  back∸ : ∀ {a c} → a < c → a + suc (c ∸ suc a) ≡ c
  back∸ {a} {c} lt = Eq.trans (Eq.cong (a +_) (Eq.sym (∸-suc lt))) (NP.m+[n∸m]≡n (NP.<⇒≤ lt))

  ----------------------------------------------------------------------
  -- The rules on natural numbers

  px-sq′ : ∀ a → suc a < N → dPP a (suc a) • dPP a (suc a) ≈ dPX a a (suc a) • dPX a a (suc a)
  px-sq′ a v rewrite pp1 a | lo1 a = trans (cong right-unit right-unit) (sq v)

  px-braid′ : ∀ a → suc (suc a) < N →
              dPX a a (suc a) • dPX (suc a) (suc a) (suc (suc a)) • dPX a a (suc a)
              ≈ dPX (suc a) (suc a) (suc (suc a)) • dPX a a (suc a) • dPX (suc a) (suc a) (suc (suc a))
  px-braid′ a v rewrite lo1 a | lo1 (suc a) = braid v

  shrink₁′ : ∀ a c → suc a < c →
             dPX a a c ≈ dPX (suc a) a (suc a) • dPX (suc a) (suc a) c • dPX a a (suc a)
  shrink₁′ a c lt rewrite loC a c | loC (suc a) c | hi1 a | lo1 a
                        | ∸-suc (NP.<-trans (NP.n<1+n a) lt) | ∸-suc lt = refl

  shrink₂′ : ∀ a c → suc a < c →
             dPX c a c ≈ dPX (suc a) a (suc a) • dPX c (suc a) c • dPX a a (suc a)
  shrink₂′ a c lt rewrite hiC (NP.<-trans (NP.n<1+n a) lt) | hiC lt | hi1 a | lo1 a
                        | ∸-suc (NP.<-trans (NP.n<1+n a) lt) | ∸-suc lt = refl

  shrink₃′ : ∀ a c′ → a < c′ → suc c′ < N →
             dPX a a (suc c′) ≈ dPX c′ c′ (suc c′) • dPX a a c′ • dPX (suc c′) c′ (suc c′)
  shrink₃′ a c′ lt v rewrite loC a (suc c′) | loC a c′ | lo1 c′ | hi1 c′
                           | s∸ (NP.<⇒≤ lt) | ∸-suc lt =
    Eq.subst (λ u → dLo a (suc (suc (c′ ∸ suc a))) ≈ l u • dLo a (suc (c′ ∸ suc a)) • h u)
             (back∸ lt) (lo-shrink a (c′ ∸ suc a) v′)
    where
      v′ : a + suc (suc (c′ ∸ suc a)) < N
      v′ = Eq.subst (_< N) (Eq.sym (Eq.trans (NP.+-suc a (suc (c′ ∸ suc a))) (Eq.cong suc (back∸ lt)))) v

  shrink₄′ : ∀ a c′ → a < c′ → suc c′ < N →
             dPX (suc c′) a (suc c′) ≈ dPX c′ c′ (suc c′) • dPX c′ a c′ • dPX (suc c′) c′ (suc c′)
  shrink₄′ a c′ lt v rewrite hiC (NP.<-trans lt (NP.n<1+n c′)) | hiC lt | lo1 c′ | hi1 c′
                           | s∸ (NP.<⇒≤ lt) | ∸-suc lt =
    Eq.subst (λ u → dHi a (suc (suc (c′ ∸ suc a))) ≈ l u • dHi a (suc (c′ ∸ suc a)) • h u)
             (back∸ lt) (hi-shrink a (c′ ∸ suc a) v′)
    where
      v′ : a + suc (suc (c′ ∸ suc a)) < N
      v′ = Eq.subst (_< N) (Eq.sym (Eq.trans (NP.+-suc a (suc (c′ ∸ suc a))) (Eq.cong suc (back∸ lt)))) v

  px-inv′ : ∀ a → suc a < N → dPX a a (suc a) • dPX (suc a) a (suc a) ≈ ε
  px-inv′ a v rewrite lo1 a | hi1 a = l-inv v

  px-sign′ : ∀ c a b → a < b → b < N →
             dPX c a b ≈ dPP c a • dPP c a • dPX a a b
  px-sign′ c a b lt bN with c Data.Nat.≟ a
  ... | yes Eq.refl = sym (trans (cong (pp-self c) (front _ (pp-self c))) (trans left-unit left-unit))
  ... | no c≢a with c Data.Nat.≟ b
  ...   | yes Eq.refl rewrite hiC lt | dPP-dn (NP.<⇒≤ lt) | loC a c | ∸-suc lt =
          hi-sign a (c ∸ suc a) (Eq.subst (_< N) (Eq.sym (back∸ lt)) bN)
  ...   | no c≢b rewrite eq-false c≢a | eq-false c≢b | loC a b = refl

  -- px-conj, the pair c above the letter.
  conj-above : ∀ a c → suc a < c → c < N → dPP (suc a) c • l a ≈ l a • dPP a c
  conj-above a c lt cN rewrite dPP-up (NP.<⇒≤ lt) | dPP-up (NP.<⇒≤ (NP.<-trans (NP.n<1+n a) lt))
                             | ∸-suc lt | ∸-suc (NP.<-trans (NP.n<1+n a) lt) | ∸-suc lt =
    from-cj (NP.≤-<-trans (NP.<⇒≤ lt) cN) (cj-up (c ∸ suc (suc a))
      (Eq.subst (_< N) (Eq.sym (back∸ lt)) cN))

  -- px-conj, the pair c below the letter.
  dn-snoc : ∀ a e → pp-dn a (suc e) ≈ pp-dn a e • (p′ (a + e) • ε)
  dn-snoc a e = Eq.subst (λ u → pp-dn a u ≈ pp-dn a e • (p′ (a + e) • ε)) (NP.+-comm e 1) (dn-+ a e 1)

  conj-below : ∀ c g → suc (suc (c + g)) < N →
               pp-dn c (suc (suc g)) • l (suc (c + g)) ≈ l (suc (c + g)) • pp-dn c (suc g)
  conj-below c g v = begin
    pp-dn c (suc (suc g)) • l j                                ≈⟨ front _ (dn-snoc c (suc g)) ⟩
    (pp-dn c (suc g) • (p′ (c + suc g) • ε)) • l j             ≡⟨ Eq.cong (λ u → (pp-dn c (suc g) • (p′ u • ε)) • l j) (NP.+-suc c g) ⟩
    (pp-dn c (suc g) • (p′ j • ε)) • l j                       ≈⟨ front _ (front _ (dn-snoc c g)) ⟩
    ((G • (p′ i • ε)) • (p′ j • ε)) • l j                      ≈⟨ front _ (cong (back G right-unit) right-unit) ⟩
    ((G • p′ i) • p′ j) • l j                                  ≈⟨ trans assoc (trans assoc (back G (back (p′ i) (sym (conj-dn′))))) ⟩
    G • (p′ i • (p′ j • l j))                                  ≈⟨ back G (conj-dn v) ⟩
    G • (l j • p′ i)                                           ≈⟨ sym assoc ⟩
    (G • l j) • p′ i                                           ≈⟨ front _ (dn-commR c g far) ⟩
    (l j • G) • p′ i                                           ≈⟨ assoc ⟩
    l j • (G • p′ i)                                           ≈⟨ back (l j) (back G (sym right-unit)) ⟩
    l j • (G • (p′ i • ε))                                     ≈⟨ back (l j) (sym (dn-snoc c g)) ⟩
    l j • pp-dn c (suc g)                                      ∎
    where
      i = c + g; j = suc (c + g)
      G = pp-dn c g
      conj-dn′ : p′ j • l j ≈ p′ j • l j
      conj-dn′ = refl
      vj : suc j < N
      vj = v
      far : ∀ {m} → c ≤ m → m < c + g → Comm (p′ m) (l j)
      far {m} _ lt = far-p′l (NP.<-trans (s≤s lt) (NP.<-trans (NP.n<1+n _) v)) vj
                       (inj₁ (s≤s lt))

  px-conj′ : ∀ a c → c ≢ a → c ≢ suc a → c < N → suc a < N →
             dPP (suc a) c • dPX a a (suc a) ≈ dPX a a (suc a) • dPP a c
  px-conj′ a c ca csa cN vN rewrite lo1 a with NP.<-cmp c a
  ... | tri≈ _ e _ = ⊥-elim (ca e)
  ... | tri> _ _ gt = conj-above a c (NP.≤∧≢⇒< gt (λ e → csa (Eq.sym e))) cN
  ... | tri< lt _ _ =
    Eq.subst₂ (λ u w → dPP (suc u) c • l u ≈ l u • dPP u c) ea ea
      (Eq.subst (λ x → x) (Eq.cong₂ (λ L R → L ≈ R) (Eq.sym lhs) (Eq.sym rhs)) (conj-below c g v))
    where
      g = a ∸ suc c
      ea : suc (c + g) ≡ a
      ea = Eq.trans (Eq.sym (NP.+-suc c g)) (back∸ lt)
      v : suc (suc (c + g)) < N
      v = Eq.subst (λ u → suc u < N) (Eq.sym ea) vN
      lhs : dPP (suc (suc (c + g))) c • l (suc (c + g)) ≡ pp-dn c (suc (suc g)) • l (suc (c + g))
      lhs rewrite dPP-dn {suc (suc (c + g))} {c} (NP.≤-trans (NP.m≤m+n c g) (NP.≤-trans (NP.n≤1+n _) (NP.n≤1+n _)))
                | s∸ {c} {suc (c + g)} (NP.≤-trans (NP.m≤m+n c g) (NP.n≤1+n _))
                | s∸ {c} {c + g} (NP.m≤m+n c g) | NP.m+n∸m≡n c g = Eq.refl
      rhs : l (suc (c + g)) • dPP (suc (c + g)) c ≡ l (suc (c + g)) • pp-dn c (suc g)
      rhs rewrite dPP-dn {suc (c + g)} {c} (NP.≤-trans (NP.m≤m+n c g) (NP.n≤1+n _))
                | s∸ {c} {c + g} (NP.m≤m+n c g) | NP.m+n∸m≡n c g = Eq.refl

  px-conj₂′ : ∀ a → suc a < N → dPP a (suc a) • dPX a a (suc a) ≈ dPX a a (suc a) • dPP (suc a) a
  px-conj₂′ a v rewrite pp1 a | pp1′ a | lo1 a =
    trans (front _ right-unit) (trans (conj₂ v) (back _ (sym right-unit)))

  px-comm′ : ∀ a b → suc a < b → suc b < N →
             dPX a a (suc a) • dPX b b (suc b) ≈ dPX b b (suc b) • dPX a a (suc a)
  px-comm′ a b lt v rewrite lo1 a | lo1 b = far-ll v lt

  ----------------------------------------------------------------------
  -- The rules of the fragment decode to equations

  fragment : ∀ {u w} → N F, u === w → (d ʷ) u ≈ (d ʷ) w
  fragment (pp-id a)          = pp-self (toℕ a)
  fragment (pp-ord a b)       = pp-ord′ (toℕ<n a) (toℕ<n b)
  fragment (pp-comm a b c e)  = dPP-comm (toℕ<n a) (toℕ<n b) (allP-dPP (toℕ<n c) (toℕ<n e))
  fragment (pp-tele a b c)    = tele (toℕ<n a) (toℕ<n b) (toℕ<n c)
  fragment (px-sq a a′ s) =
    Eq.subst (λ u → dPP A u • dPP A u ≈ dPX A A u • dPX A A u) (Eq.sym s)
             (px-sq′ A (Eq.subst (_< N) s (toℕ<n a′)))
    where A = toℕ a
  fragment (px-braid a a′ a″ s s′) =
    Eq.subst₂ (λ u v → dPX A A u • dPX u u v • dPX A A u ≈ dPX u u v • dPX A A u • dPX u u v)
              (Eq.sym s) (Eq.sym s″) (px-braid′ A (Eq.subst (_< N) s″ (toℕ<n a″)))
    where
      A = toℕ a
      s″ : toℕ a″ ≡ suc (suc A)
      s″ = Eq.trans s′ (Eq.cong suc s)
  fragment (px-shrink₁ a a′ c s lt) =
    Eq.subst (λ u → dPX A A C ≈ dPX u A u • dPX u u C • dPX A A u) (Eq.sym s)
             (shrink₁′ A C (Eq.subst (_< C) s lt))
    where A = toℕ a; C = toℕ c
  fragment (px-shrink₂ a a′ c s lt) =
    Eq.subst (λ u → dPX C A C ≈ dPX u A u • dPX C u C • dPX A A u) (Eq.sym s)
             (shrink₂′ A C (Eq.subst (_< C) s lt))
    where A = toℕ a; C = toℕ c
  fragment (px-shrink₃ a c′ c s lt) =
    Eq.subst (λ u → dPX A A u ≈ dPX C′ C′ u • dPX A A C′ • dPX u C′ u) (Eq.sym s)
             (shrink₃′ A C′ lt (Eq.subst (_< N) s (toℕ<n c)))
    where A = toℕ a; C′ = toℕ c′
  fragment (px-shrink₄ a c′ c s lt) =
    Eq.subst (λ u → dPX u A u ≈ dPX C′ C′ u • dPX C′ A C′ • dPX u C′ u) (Eq.sym s)
             (shrink₄′ A C′ lt (Eq.subst (_< N) s (toℕ<n c)))
    where A = toℕ a; C′ = toℕ c′
  fragment (px-inv a a′ s) =
    Eq.subst (λ u → dPX A A u • dPX u A u ≈ ε) (Eq.sym s)
             (px-inv′ A (Eq.subst (_< N) s (toℕ<n a′)))
    where A = toℕ a
  fragment (px-sign c a b ab) =
    px-sign′ (toℕ c) (toℕ a) (toℕ b) (recompute (toℕ a NP.<? toℕ b) ab) (toℕ<n b)
  fragment (px-conj a a′ c s ca ca′) =
    Eq.subst (λ u → dPP u C • dPX A A u ≈ dPX A A u • dPP A C) (Eq.sym s)
      (px-conj′ A C (λ e → ca (Data.Fin.Properties.toℕ-injective e))
                (λ e → ca′ (Data.Fin.Properties.toℕ-injective (Eq.trans e (Eq.sym s))))
                (toℕ<n c) (Eq.subst (_< N) s (toℕ<n a′)))
    where A = toℕ a; C = toℕ c
  fragment (px-conj₂ a a′ s) =
    Eq.subst (λ u → dPP A u • dPX A A u ≈ dPX A A u • dPP u A) (Eq.sym s)
             (px-conj₂′ A (Eq.subst (_< N) s (toℕ<n a′)))
    where A = toℕ a
  fragment (px-comm a a′ b b′ s s′ lt) =
    Eq.subst₂ (λ u v → dPX A A u • dPX B B v ≈ dPX B B v • dPX A A u) (Eq.sym s) (Eq.sym s′)
              (px-comm′ A B (Eq.subst (_< B) s lt) (Eq.subst (_< N) s′ (toℕ<n b′)))
    where A = toℕ a; B = toℕ b
  fragment (dx-split a b c e ab ce) = refl

------------------------------------------------------------------------
-- Presentations of groups
--
-- The two-level derivations of the P′ rules
--
-- Each lemma is one rule of `Rules` read through `asG`: its sides as
-- words over the two-level generators, equal by Bian and Selinger's
-- relations.  In order: the phase-pair rules — pure phase algebra,
-- the phases commuting totally and i⁴ vanishing; the exchange letters;
-- the braid and the shrinking rules; and the hybrid letters, whose
-- rules are two-level relations read at a sink, all through one lemma
-- (`frame`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Auxiliary.SoundLemmas (N : ℕ) where

open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (_<?_)
open import Data.Nat using (_+_)
open import Data.Product using (_×_ ; _,_)
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary.Decidable using (recompute)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _^_)

import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open TL using (i ; X ; K)

open import Examples.Groups.Clifford+CS.Auxiliary.SoundBase N
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm N
  using (swapF ; swapF-a ; swapF-b ; swapF-o)

private
  WT : Set
  WT = Word (TL.Gen N)

  _<F_ : Fin N → Fin N → Set
  _<F_ = Data.Fin._<_
    where import Data.Fin

------------------------------------------------------------------------
-- The phase pairs

sd-pp-id : ∀ (a : Fin N) → i a • i a ^ 3 ≈ ε
sd-pp-id a = i⁴ a

sd-pp-ord : ∀ (a b : Fin N) → (i a • i b ^ 3) ^ 4 ≈ ε
sd-pp-ord a b = begin
  (i a • i b ^ 3) ^ 4
    ≈⟨ ^-• (i a) (i b ^ 3) 4 (ipow-comm a b 1 3) ⟩
  i a ^ 4 • (i b ^ 3) ^ 4
    ≈⟨ front _ (i⁴ a) ⟩
  ε • (i b ^ 3) ^ 4
    ≈⟨ left-unit ⟩
  (i b ^ 3) ^ 4
    ≈⟨ ^^ (i b) 3 4 ⟩
  i b ^ 12
    ≈⟨ sym (^^ (i b) 4 3) ⟩
  (i b ^ 4) ^ 3
    ≈⟨ ^-cong (i b ^ 4) ε 3 (i⁴ b) ⟩
  ε ^ 3
    ≈⟨ ε^k=ε 3 ⟩
  ε ∎

sd-pp-comm : ∀ (a b c d : Fin N) →
             (i a • i b ^ 3) • (i c • i d ^ 3)
             ≈ (i c • i d ^ 3) • (i a • i b ^ 3)
sd-pp-comm a b c d =
  comm-pair (i a) (i b ^ 3) (i c) (i d ^ 3)
            (ipow-comm a c 1 1) (ipow-comm a d 1 3)
            (ipow-comm b c 3 1) (ipow-comm b d 3 3)

sd-pp-tele : ∀ (a b c : Fin N) →
             (i a • i b ^ 3) • (i b • i c ^ 3) ≈ i a • i c ^ 3
sd-pp-tele a b c = begin
  (i a • i b ^ 3) • (i b • i c ^ 3)
    ≈⟨ assoc ⟩
  i a • (i b ^ 3 • (i b • i c ^ 3))
    ≈⟨ back (i a) (sym assoc) ⟩
  i a • ((i b ^ 3 • i b) • i c ^ 3)
    ≈⟨ back (i a) (front _ (sym (^-+ (i b) 3 1))) ⟩
  i a • (i b ^ 4 • i c ^ 3)
    ≈⟨ back (i a) (front _ (i⁴ b)) ⟩
  i a • (ε • i c ^ 3)
    ≈⟨ back (i a) left-unit ⟩
  i a • i c ^ 3 ∎

------------------------------------------------------------------------
-- The exchange letters
--
-- Each proof brings the phases to the front — a phase crosses an
-- exchange with its index transposed — fuses them mod four, and leaves
-- an exchange word that one swap relation and an involution settle.

private
  <⇒≢ : ∀ {x y : Fin N} → x <F y → x ≢ y
  <⇒≢ {x} lt e =
    n≮n (toℕ x) (Eq.subst (λ z → Data.Nat._<_ (toℕ x) z)
                          (Eq.cong toℕ (Eq.sym e)) lt)
    where
    import Data.Nat
    open import Data.Nat.Properties using (n≮n)

  ≢sym : ∀ {x y : Fin N} → x ≢ y → y ≢ x
  ≢sym ne e = ne (Eq.sym e)

  -- The canonical form of a phase pair squared.
  pp²-can : ∀ (x y : Fin N) →
            (i x • i y ^ 3) • (i x • i y ^ 3) ≈ i x ^ 2 • i y ^ 2
  pp²-can x y = begin
    (i x • i y ^ 3) • (i x • i y ^ 3)
      ≈⟨ by-assoc Eq.refl ⟩
    i x • ((i y ^ 3 • i x) • i y ^ 3)
      ≈⟨ back (i x) (front _ (ipow-comm y x 3 1)) ⟩
    i x • ((i x • i y ^ 3) • i y ^ 3)
      ≈⟨ by-assoc Eq.refl ⟩
    (i x • i x) • (i y ^ 3 • i y ^ 3)
      ≈⟨ back _ (trans (sym (^-+ (i y) 3 3)) (i-mod4 y 2)) ⟩
    (i x • i x) • i y ^ 2 ∎

sd-px-sq : ∀ (a a′ : Fin N) .(p : a <F a′) →
           (i a • i a′ ^ 3) • (i a • i a′ ^ 3)
           ≈ (i a • (i a • X a a′ p)) • (i a • (i a • X a a′ p))
sd-px-sq a a′ p = trans (pp²-can a a′) (sym rhs)
  where
  Xp = X a a′ p

  rhs : (i a • (i a • Xp)) • (i a • (i a • Xp)) ≈ i a ^ 2 • i a′ ^ 2
  rhs = begin
    (i a • (i a • Xp)) • (i a • (i a • Xp))
      ≈⟨ by-assoc Eq.refl ⟩
    (i a • i a) • ((Xp • (i a • i a)) • Xp)
      ≈⟨ back _ (front Xp (crossʳ-pow-at a a′ p 2 (swapF-a a a′))) ⟩
    (i a • i a) • ((i a′ ^ 2 • Xp) • Xp)
      ≈⟨ back _ assoc ⟩
    (i a • i a) • (i a′ ^ 2 • (Xp • Xp))
      ≈⟨ back _ (back _ (X² a a′ p)) ⟩
    (i a • i a) • (i a′ ^ 2 • ε)
      ≈⟨ back _ right-unit ⟩
    (i a • i a) • i a′ ^ 2 ∎

sd-px-inv : ∀ (a a′ : Fin N) .(p : a <F a′) →
            (i a • (i a • X a a′ p)) • (i a′ • (i a′ • X a a′ p)) ≈ ε
sd-px-inv a a′ p = begin
  (i a • (i a • Xp)) • (i a′ • (i a′ • Xp))
    ≈⟨ by-assoc Eq.refl ⟩
  (i a • i a) • ((Xp • (i a′ • i a′)) • Xp)
    ≈⟨ back _ (front Xp (crossʳ-pow-at a a′ p 2 (swapF-b a a′))) ⟩
  (i a • i a) • ((i a ^ 2 • Xp) • Xp)
    ≈⟨ back _ assoc ⟩
  (i a • i a) • (i a ^ 2 • (Xp • Xp))
    ≈⟨ back _ (back _ (X² a a′ p)) ⟩
  (i a • i a) • (i a ^ 2 • ε)
    ≈⟨ back _ right-unit ⟩
  (i a • i a) • (i a • i a)
    ≈⟨ by-assoc Eq.refl ⟩
  i a • (i a • (i a • i a))
    ≈⟨ i⁴ a ⟩
  ε ∎
  where
  Xp = X a a′ p

sd-px-sign : ∀ (c a b : Fin N) .(p : a <F b) →
             i c • (i c • X a b p)
             ≈ ((i c • i a ^ 3) • (i c • i a ^ 3)) • (i a • (i a • X a b p))
sd-px-sign c a b p = sym (begin
  ((i c • i a ^ 3) • (i c • i a ^ 3)) • (i a • (i a • Xp))
    ≈⟨ front _ (pp²-can c a) ⟩
  (i c ^ 2 • i a ^ 2) • (i a • (i a • Xp))
    ≈⟨ by-assoc Eq.refl ⟩
  i c ^ 2 • ((i a ^ 2 • (i a • i a)) • Xp)
    ≈⟨ back _ (front Xp (trans (sym (^-+ (i a) 2 2)) (i-mod4 a 0))) ⟩
  i c ^ 2 • (ε • Xp)
    ≈⟨ back _ left-unit ⟩
  i c ^ 2 • Xp
    ≈⟨ assoc ⟩
  i c • (i c • Xp) ∎)
  where
  Xp = X a b p

sd-px-conj : ∀ (a a′ c : Fin N) .(p : a <F a′) → c ≢ a → c ≢ a′ →
             (i a′ • i c ^ 3) • (i a • (i a • X a a′ p))
             ≈ (i a • (i a • X a a′ p)) • (i a • i c ^ 3)
sd-px-conj a a′ c p ca ca′ = trans lhs (sym rhs)
  where
  Xp = X a a′ p
  R  = i c ^ 3 • Xp

  lhs : (i a′ • i c ^ 3) • (i a • (i a • Xp))
        ≈ (i a • i a) • (i a′ • (i c ^ 3 • Xp))
  lhs = begin
    (i a′ • i c ^ 3) • (i a • (i a • Xp))
      ≈⟨ by-assoc Eq.refl ⟩
    i a′ • ((i c ^ 3 • (i a • i a)) • Xp)
      ≈⟨ back _ (front Xp (ipow-comm c a 3 2)) ⟩
    i a′ • (((i a • i a) • i c ^ 3) • Xp)
      ≈⟨ by-assoc Eq.refl ⟩
    (i a′ • (i a • i a)) • (i c ^ 3 • Xp)
      ≈⟨ front R (ipow-comm a′ a 1 2) ⟩
    ((i a • i a) • i a′) • (i c ^ 3 • Xp)
      ≈⟨ assoc ⟩
    (i a • i a) • (i a′ • (i c ^ 3 • Xp)) ∎

  rhs : (i a • (i a • Xp)) • (i a • i c ^ 3)
        ≈ (i a • i a) • (i a′ • (i c ^ 3 • Xp))
  rhs = begin
    (i a • (i a • Xp)) • (i a • i c ^ 3)
      ≈⟨ by-assoc Eq.refl ⟩
    (i a • i a) • ((Xp • i a) • i c ^ 3)
      ≈⟨ back _ (front _ (crossʳ-at a a′ p (swapF-a a a′))) ⟩
    (i a • i a) • ((i a′ • Xp) • i c ^ 3)
      ≈⟨ back _ assoc ⟩
    (i a • i a) • (i a′ • (Xp • i c ^ 3))
      ≈⟨ back _ (back _ (crossʳ-pow-at a a′ p 3 (swapF-o a a′ c ca ca′))) ⟩
    (i a • i a) • (i a′ • (i c ^ 3 • Xp)) ∎

sd-px-conj₂ : ∀ (a a′ : Fin N) .(p : a <F a′) →
              (i a • i a′ ^ 3) • (i a • (i a • X a a′ p))
              ≈ (i a • (i a • X a a′ p)) • (i a′ • i a ^ 3)
sd-px-conj₂ a a′ p = trans lhs (sym rhs)
  where
  Xp = X a a′ p

  lhs : (i a • i a′ ^ 3) • (i a • (i a • Xp))
        ≈ (i a • (i a • i a)) • (i a′ ^ 3 • Xp)
  lhs = begin
    (i a • i a′ ^ 3) • (i a • (i a • Xp))
      ≈⟨ by-assoc Eq.refl ⟩
    i a • ((i a′ ^ 3 • (i a • i a)) • Xp)
      ≈⟨ back _ (front Xp (ipow-comm a′ a 3 2)) ⟩
    i a • (((i a • i a) • i a′ ^ 3) • Xp)
      ≈⟨ by-assoc Eq.refl ⟩
    (i a • (i a • i a)) • (i a′ ^ 3 • Xp) ∎

  rhs : (i a • (i a • Xp)) • (i a′ • i a ^ 3)
        ≈ (i a • (i a • i a)) • (i a′ ^ 3 • Xp)
  rhs = begin
    (i a • (i a • Xp)) • (i a′ • i a ^ 3)
      ≈⟨ by-assoc Eq.refl ⟩
    (i a • i a) • ((Xp • i a′) • i a ^ 3)
      ≈⟨ back _ (front _ (crossʳ-at a a′ p (swapF-b a a′))) ⟩
    (i a • i a) • ((i a • Xp) • i a ^ 3)
      ≈⟨ back _ assoc ⟩
    (i a • i a) • (i a • (Xp • i a ^ 3))
      ≈⟨ back _ (back _ (crossʳ-pow-at a a′ p 3 (swapF-a a a′))) ⟩
    (i a • i a) • (i a • (i a′ ^ 3 • Xp))
      ≈⟨ by-assoc Eq.refl ⟩
    (i a • (i a • i a)) • (i a′ ^ 3 • Xp) ∎

sd-dx-split : ∀ (a b c d : Fin N) .(ab : a <F b) .(cd : c <F d) →
              X a b ab • X c d cd
              ≈ (i a • (i a • X a b ab)) • (i b • (i b • X c d cd))
sd-dx-split a b c d ab cd = sym (begin
  (i a • (i a • Xab)) • (i b • (i b • Xcd))
    ≈⟨ by-assoc Eq.refl ⟩
  (i a • i a) • ((Xab • (i b • i b)) • Xcd)
    ≈⟨ back _ (front Xcd (crossʳ-pow-at a b ab 2 (swapF-b a b))) ⟩
  (i a • i a) • ((i a ^ 2 • Xab) • Xcd)
    ≈⟨ by-assoc Eq.refl ⟩
  ((i a • i a) • (i a • i a)) • (Xab • Xcd)
    ≈⟨ front _ (trans (by-assoc Eq.refl) (i⁴ a)) ⟩
  ε • (Xab • Xcd)
    ≈⟨ left-unit ⟩
  Xab • Xcd ∎)
  where
  Xab = X a b ab
  Xcd = X c d cd

sd-px-comm : ∀ (a a′ b b′ : Fin N) .(p : a <F a′) .(q : b <F b′) →
             a ≢ b → a ≢ b′ → a′ ≢ b → a′ ≢ b′ →
             (i a • (i a • X a a′ p)) • (i b • (i b • X b b′ q))
             ≈ (i b • (i b • X b b′ q)) • (i a • (i a • X a a′ p))
sd-px-comm a a′ b b′ p q ab ab′ a′b a′b′ = begin
  (i a • (i a • X₁)) • (i b • (i b • X₂))
    ≈⟨ by-assoc Eq.refl ⟩
  ((i a • i a) • X₁) • ((i b • i b) • X₂)
    ≈⟨ comm-pair (i a • i a) X₁ (i b • i b) X₂ ux uy vx vy ⟩
  ((i b • i b) • X₂) • ((i a • i a) • X₁)
    ≈⟨ by-assoc Eq.refl ⟩
  (i b • (i b • X₂)) • (i a • (i a • X₁)) ∎
  where
  X₁ = X a a′ p
  X₂ = X b b′ q

  ux : (i a • i a) • (i b • i b) ≈ (i b • i b) • (i a • i a)
  ux = ipow-comm a b 2 2

  uy : (i a • i a) • X₂ ≈ X₂ • (i a • i a)
  uy = cross-pow-at b b′ q 2 (swapF-o b b′ a ab ab′)

  vx : X₁ • (i b • i b) ≈ (i b • i b) • X₁
  vx = crossʳ-pow-at a a′ p 2 (swapF-o a a′ b (≢sym ab) (≢sym a′b))

  vy : X₁ • X₂ ≈ X₂ • X₁
  vy = axiom (TL.comm-XX p q ab ab′ a′b a′b′)

------------------------------------------------------------------------
-- The braid and the shrinking rules
--
-- Each proof crosses the phases to the front, where the pattern
-- x² y² x² fuses to y² (`φ-aba`), and settles the three exchanges by
-- one swap relation and an involution (`xcoreL`, `xcoreR`, `xcoreU`).

private
  <F-trans : ∀ {x y z : Fin N} → x <F y → y <F z → x <F z
  <F-trans = Data.Nat.Properties.<-trans
    where import Data.Nat.Properties

  -- x² y² x² is y².
  φ-aba : ∀ (x y : Fin N) (core : WT) →
          (i x • i x) • ((i y • i y) • ((i x • i x) • core))
          ≈ (i y • i y) • core
  φ-aba x y core = begin
    (i x • i x) • ((i y • i y) • ((i x • i x) • core))
      ≈⟨ by-assoc Eq.refl ⟩
    ((i x • i x) • (i y • i y)) • ((i x • i x) • core)
      ≈⟨ front _ (ipow-comm x y 2 2) ⟩
    ((i y • i y) • (i x • i x)) • ((i x • i x) • core)
      ≈⟨ by-assoc Eq.refl ⟩
    (i y • i y) • (((i x • i x) • (i x • i x)) • core)
      ≈⟨ back _ (front core (trans (by-assoc Eq.refl) (i⁴ x))) ⟩
    (i y • i y) • (ε • core)
      ≈⟨ back _ left-unit ⟩
    (i y • i y) • core ∎

  -- The three-exchange cores.
  xcoreL : ∀ (a a′ c : Fin N) (p : a <F a′) (q : a′ <F c) →
           X a a′ p • (X a′ c q • X a a′ p) ≈ X a c (<F-trans p q)
  xcoreL a a′ c p q =
    trans (back (X a a′ p) (axiom (TL.swap-XX p q)))
          (cancelˡ⁻ _ (X² a a′ p))

  xcoreR : ∀ (a a′ c : Fin N) (p : a <F a′) (q : a′ <F c) →
           X a′ c q • (X a a′ p • X a′ c q) ≈ X a c (<F-trans p q)
  xcoreR a a′ c p q =
    trans (back (X a′ c q) (sym (conj-flip (X² a′ c q) (axiom (TL.swap-XX′ p q)))))
          (cancelˡ⁻ _ (X² a′ c q))

  xcoreU : ∀ (a c′ c : Fin N) (p : a <F c′) (q : c′ <F c) →
           X c′ c q • (X a c′ p • X c′ c q) ≈ X a c (<F-trans p q)
  xcoreU a c′ c p q =
    trans (back (X c′ c q) (sym (conj-flip (X² c′ c q) (axiom (TL.swap-XX′ p q)))))
          (cancelˡ⁻ _ (X² c′ c q))

sd-px-braid : ∀ (a a′ a″ : Fin N) (p : a <F a′) (q : a′ <F a″) →
              (i a • (i a • X a a′ p))
              • ((i a′ • (i a′ • X a′ a″ q)) • (i a • (i a • X a a′ p)))
              ≈ (i a′ • (i a′ • X a′ a″ q))
                • ((i a • (i a • X a a′ p)) • (i a′ • (i a′ • X a′ a″ q)))
sd-px-braid a a′ a″ p q = trans lhs (sym rhs)
  where
  X₁ = X a a′ p
  X₂ = X a′ a″ q

  a∉₂ : X₂ • (i a • i a) ≈ (i a • i a) • X₂
  a∉₂ = crossʳ-pow-at a′ a″ q 2
          (swapF-o a′ a″ a (<⇒≢ p) (<⇒≢ (<F-trans p q)))

  lhs : (i a • (i a • X₁)) • ((i a′ • (i a′ • X₂)) • (i a • (i a • X₁)))
        ≈ (i a′ • i a′) • X a a″ (<F-trans p q)
  lhs = begin
    (i a • (i a • X₁)) • ((i a′ • (i a′ • X₂)) • (i a • (i a • X₁)))
      ≈⟨ by-assoc Eq.refl ⟩
    (i a • i a) • (X₁ • ((i a′ • i a′) • ((X₂ • (i a • i a)) • X₁)))
      ≈⟨ back _ (back X₁ (back _ (front X₁ a∉₂))) ⟩
    (i a • i a) • (X₁ • ((i a′ • i a′) • (((i a • i a) • X₂) • X₁)))
      ≈⟨ by-assoc Eq.refl ⟩
    (i a • i a) • ((X₁ • (i a′ • i a′)) • ((i a • i a) • (X₂ • X₁)))
      ≈⟨ back _ (front _ (crossʳ-pow-at a a′ p 2 (swapF-b a a′))) ⟩
    (i a • i a) • (((i a • i a) • X₁) • ((i a • i a) • (X₂ • X₁)))
      ≈⟨ by-assoc Eq.refl ⟩
    (i a • i a) • ((i a • i a) • ((X₁ • (i a • i a)) • (X₂ • X₁)))
      ≈⟨ back _ (back _ (front _ (crossʳ-pow-at a a′ p 2 (swapF-a a a′)))) ⟩
    (i a • i a) • ((i a • i a) • (((i a′ • i a′) • X₁) • (X₂ • X₁)))
      ≈⟨ by-assoc Eq.refl ⟩
    ((i a • i a) • (i a • i a)) • ((i a′ • i a′) • (X₁ • (X₂ • X₁)))
      ≈⟨ front _ (trans (by-assoc Eq.refl) (i⁴ a)) ⟩
    ε • ((i a′ • i a′) • (X₁ • (X₂ • X₁)))
      ≈⟨ left-unit ⟩
    (i a′ • i a′) • (X₁ • (X₂ • X₁))
      ≈⟨ back _ (xcoreL a a′ a″ p q) ⟩
    (i a′ • i a′) • X a a″ (<F-trans p q) ∎

  rhs : (i a′ • (i a′ • X₂)) • ((i a • (i a • X₁)) • (i a′ • (i a′ • X₂)))
        ≈ (i a′ • i a′) • X a a″ (<F-trans p q)
  rhs = begin
    (i a′ • (i a′ • X₂)) • ((i a • (i a • X₁)) • (i a′ • (i a′ • X₂)))
      ≈⟨ by-assoc Eq.refl ⟩
    (i a′ • i a′) • (X₂ • ((i a • i a) • ((X₁ • (i a′ • i a′)) • X₂)))
      ≈⟨ back _ (back X₂ (back _ (front X₂
           (crossʳ-pow-at a a′ p 2 (swapF-b a a′))))) ⟩
    (i a′ • i a′) • (X₂ • ((i a • i a) • (((i a • i a) • X₁) • X₂)))
      ≈⟨ by-assoc Eq.refl ⟩
    (i a′ • i a′) • ((X₂ • (i a • i a)) • ((i a • i a) • (X₁ • X₂)))
      ≈⟨ back _ (front _ a∉₂) ⟩
    (i a′ • i a′) • (((i a • i a) • X₂) • ((i a • i a) • (X₁ • X₂)))
      ≈⟨ by-assoc Eq.refl ⟩
    (i a′ • i a′) • ((i a • i a) • ((X₂ • (i a • i a)) • (X₁ • X₂)))
      ≈⟨ back _ (back _ (front _ a∉₂)) ⟩
    (i a′ • i a′) • ((i a • i a) • (((i a • i a) • X₂) • (X₁ • X₂)))
      ≈⟨ by-assoc Eq.refl ⟩
    (i a′ • i a′) • (((i a • i a) • (i a • i a)) • (X₂ • (X₁ • X₂)))
      ≈⟨ back _ (front _ (trans (by-assoc Eq.refl) (i⁴ a))) ⟩
    (i a′ • i a′) • (ε • (X₂ • (X₁ • X₂)))
      ≈⟨ back _ left-unit ⟩
    (i a′ • i a′) • (X₂ • (X₁ • X₂))
      ≈⟨ back _ (xcoreR a a′ a″ p q) ⟩
    (i a′ • i a′) • X a a″ (<F-trans p q) ∎

------------------------------------------------------------------------
-- The shrinking rules

sd-px-shrink₁ : ∀ (a a′ c : Fin N) (p : a <F a′) (lt : a′ <F c) →
                i a • (i a • X a c (<F-trans p lt))
                ≈ (i a′ • (i a′ • X a a′ p))
                  • ((i a′ • (i a′ • X a′ c lt)) • (i a • (i a • X a a′ p)))
sd-px-shrink₁ a a′ c p lt = sym (begin
  (i a′ • (i a′ • X₁)) • ((i a′ • (i a′ • X₂)) • (i a • (i a • X₁)))
    ≈⟨ by-assoc Eq.refl ⟩
  (i a′ • i a′) • (X₁ • ((i a′ • i a′) • ((X₂ • (i a • i a)) • X₁)))
    ≈⟨ back _ (back X₁ (back _ (front X₁ a∉₂))) ⟩
  (i a′ • i a′) • (X₁ • ((i a′ • i a′) • (((i a • i a) • X₂) • X₁)))
    ≈⟨ by-assoc Eq.refl ⟩
  (i a′ • i a′) • ((X₁ • (i a′ • i a′)) • ((i a • i a) • (X₂ • X₁)))
    ≈⟨ back _ (front _ (crossʳ-pow-at a a′ p 2 (swapF-b a a′))) ⟩
  (i a′ • i a′) • (((i a • i a) • X₁) • ((i a • i a) • (X₂ • X₁)))
    ≈⟨ by-assoc Eq.refl ⟩
  (i a′ • i a′) • ((i a • i a) • ((X₁ • (i a • i a)) • (X₂ • X₁)))
    ≈⟨ back _ (back _ (front _ (crossʳ-pow-at a a′ p 2 (swapF-a a a′)))) ⟩
  (i a′ • i a′) • ((i a • i a) • (((i a′ • i a′) • X₁) • (X₂ • X₁)))
    ≈⟨ back _ (back _ assoc) ⟩
  (i a′ • i a′) • ((i a • i a) • ((i a′ • i a′) • (X₁ • (X₂ • X₁))))
    ≈⟨ φ-aba a′ a (X₁ • (X₂ • X₁)) ⟩
  (i a • i a) • (X₁ • (X₂ • X₁))
    ≈⟨ back _ (xcoreL a a′ c p lt) ⟩
  (i a • i a) • X a c (<F-trans p lt)
    ≈⟨ assoc ⟩
  i a • (i a • X a c (<F-trans p lt)) ∎)
  where
  X₁ = X a a′ p
  X₂ = X a′ c lt

  a∉₂ : X₂ • (i a • i a) ≈ (i a • i a) • X₂
  a∉₂ = crossʳ-pow-at a′ c lt 2
          (swapF-o a′ c a (<⇒≢ p) (<⇒≢ (<F-trans p lt)))

sd-px-shrink₂ : ∀ (a a′ c : Fin N) (p : a <F a′) (lt : a′ <F c) →
                i c • (i c • X a c (<F-trans p lt))
                ≈ (i a′ • (i a′ • X a a′ p))
                  • ((i c • (i c • X a′ c lt)) • (i a • (i a • X a a′ p)))
sd-px-shrink₂ a a′ c p lt = sym (begin
  (i a′ • (i a′ • X₁)) • ((i c • (i c • X₂)) • (i a • (i a • X₁)))
    ≈⟨ by-assoc Eq.refl ⟩
  (i a′ • i a′) • (X₁ • ((i c • i c) • ((X₂ • (i a • i a)) • X₁)))
    ≈⟨ back _ (back X₁ (back _ (front X₁ a∉₂))) ⟩
  (i a′ • i a′) • (X₁ • ((i c • i c) • (((i a • i a) • X₂) • X₁)))
    ≈⟨ by-assoc Eq.refl ⟩
  (i a′ • i a′) • ((X₁ • (i c • i c)) • ((i a • i a) • (X₂ • X₁)))
    ≈⟨ back _ (front _ (crossʳ-pow-at a a′ p 2
         (swapF-o a a′ c (≢sym (<⇒≢ (<F-trans p lt))) (≢sym (<⇒≢ lt))))) ⟩
  (i a′ • i a′) • (((i c • i c) • X₁) • ((i a • i a) • (X₂ • X₁)))
    ≈⟨ by-assoc Eq.refl ⟩
  (i a′ • i a′) • ((i c • i c) • ((X₁ • (i a • i a)) • (X₂ • X₁)))
    ≈⟨ back _ (back _ (front _ (crossʳ-pow-at a a′ p 2 (swapF-a a a′)))) ⟩
  (i a′ • i a′) • ((i c • i c) • (((i a′ • i a′) • X₁) • (X₂ • X₁)))
    ≈⟨ back _ (back _ assoc) ⟩
  (i a′ • i a′) • ((i c • i c) • ((i a′ • i a′) • (X₁ • (X₂ • X₁))))
    ≈⟨ φ-aba a′ c (X₁ • (X₂ • X₁)) ⟩
  (i c • i c) • (X₁ • (X₂ • X₁))
    ≈⟨ back _ (xcoreL a a′ c p lt) ⟩
  (i c • i c) • X a c (<F-trans p lt)
    ≈⟨ assoc ⟩
  i c • (i c • X a c (<F-trans p lt)) ∎)
  where
  X₁ = X a a′ p
  X₂ = X a′ c lt

  a∉₂ : X₂ • (i a • i a) ≈ (i a • i a) • X₂
  a∉₂ = crossʳ-pow-at a′ c lt 2
          (swapF-o a′ c a (<⇒≢ p) (<⇒≢ (<F-trans p lt)))

sd-px-shrink₃ : ∀ (a c′ c : Fin N) (lt : a <F c′) (q : c′ <F c) →
                i a • (i a • X a c (<F-trans lt q))
                ≈ (i c′ • (i c′ • X c′ c q))
                  • ((i a • (i a • X a c′ lt)) • (i c • (i c • X c′ c q)))
sd-px-shrink₃ a c′ c lt q = sym (begin
  (i c′ • (i c′ • Y₁)) • ((i a • (i a • Y₂)) • (i c • (i c • Y₁)))
    ≈⟨ by-assoc Eq.refl ⟩
  (i c′ • i c′) • (Y₁ • ((i a • i a) • ((Y₂ • (i c • i c)) • Y₁)))
    ≈⟨ back _ (back Y₁ (back _ (front Y₁ c∉₂))) ⟩
  (i c′ • i c′) • (Y₁ • ((i a • i a) • (((i c • i c) • Y₂) • Y₁)))
    ≈⟨ by-assoc Eq.refl ⟩
  (i c′ • i c′) • ((Y₁ • (i a • i a)) • ((i c • i c) • (Y₂ • Y₁)))
    ≈⟨ back _ (front _ (crossʳ-pow-at c′ c q 2
         (swapF-o c′ c a (<⇒≢ lt) (<⇒≢ (<F-trans lt q))))) ⟩
  (i c′ • i c′) • (((i a • i a) • Y₁) • ((i c • i c) • (Y₂ • Y₁)))
    ≈⟨ by-assoc Eq.refl ⟩
  (i c′ • i c′) • ((i a • i a) • ((Y₁ • (i c • i c)) • (Y₂ • Y₁)))
    ≈⟨ back _ (back _ (front _ (crossʳ-pow-at c′ c q 2 (swapF-b c′ c)))) ⟩
  (i c′ • i c′) • ((i a • i a) • (((i c′ • i c′) • Y₁) • (Y₂ • Y₁)))
    ≈⟨ back _ (back _ assoc) ⟩
  (i c′ • i c′) • ((i a • i a) • ((i c′ • i c′) • (Y₁ • (Y₂ • Y₁))))
    ≈⟨ φ-aba c′ a (Y₁ • (Y₂ • Y₁)) ⟩
  (i a • i a) • (Y₁ • (Y₂ • Y₁))
    ≈⟨ back _ (xcoreU a c′ c lt q) ⟩
  (i a • i a) • X a c (<F-trans lt q)
    ≈⟨ assoc ⟩
  i a • (i a • X a c (<F-trans lt q)) ∎)
  where
  Y₁ = X c′ c q
  Y₂ = X a c′ lt

  c∉₂ : Y₂ • (i c • i c) ≈ (i c • i c) • Y₂
  c∉₂ = crossʳ-pow-at a c′ lt 2
          (swapF-o a c′ c (≢sym (<⇒≢ (<F-trans lt q))) (≢sym (<⇒≢ q)))

sd-px-shrink₄ : ∀ (a c′ c : Fin N) (lt : a <F c′) (q : c′ <F c) →
                i c • (i c • X a c (<F-trans lt q))
                ≈ (i c′ • (i c′ • X c′ c q))
                  • ((i c′ • (i c′ • X a c′ lt)) • (i c • (i c • X c′ c q)))
sd-px-shrink₄ a c′ c lt q = sym (begin
  (i c′ • (i c′ • Y₁)) • ((i c′ • (i c′ • Y₂)) • (i c • (i c • Y₁)))
    ≈⟨ by-assoc Eq.refl ⟩
  (i c′ • i c′) • (Y₁ • ((i c′ • i c′) • ((Y₂ • (i c • i c)) • Y₁)))
    ≈⟨ back _ (back Y₁ (back _ (front Y₁ c∉₂))) ⟩
  (i c′ • i c′) • (Y₁ • ((i c′ • i c′) • (((i c • i c) • Y₂) • Y₁)))
    ≈⟨ by-assoc Eq.refl ⟩
  (i c′ • i c′) • ((Y₁ • (i c′ • i c′)) • ((i c • i c) • (Y₂ • Y₁)))
    ≈⟨ back _ (front _ (crossʳ-pow-at c′ c q 2 (swapF-a c′ c))) ⟩
  (i c′ • i c′) • (((i c • i c) • Y₁) • ((i c • i c) • (Y₂ • Y₁)))
    ≈⟨ by-assoc Eq.refl ⟩
  (i c′ • i c′) • ((i c • i c) • ((Y₁ • (i c • i c)) • (Y₂ • Y₁)))
    ≈⟨ back _ (back _ (front _ (crossʳ-pow-at c′ c q 2 (swapF-b c′ c)))) ⟩
  (i c′ • i c′) • ((i c • i c) • (((i c′ • i c′) • Y₁) • (Y₂ • Y₁)))
    ≈⟨ back _ (back _ assoc) ⟩
  (i c′ • i c′) • ((i c • i c) • ((i c′ • i c′) • (Y₁ • (Y₂ • Y₁))))
    ≈⟨ φ-aba c′ c (Y₁ • (Y₂ • Y₁)) ⟩
  (i c • i c) • (Y₁ • (Y₂ • Y₁))
    ≈⟨ back _ (xcoreU a c′ c lt q) ⟩
  (i c • i c) • X a c (<F-trans lt q)
    ≈⟨ assoc ⟩
  i c • (i c • X a c (<F-trans lt q)) ∎)
  where
  Y₁ = X c′ c q
  Y₂ = X a c′ lt

  c∉₂ : Y₂ • (i c • i c) ≈ (i c • i c) • Y₂
  c∉₂ = crossʳ-pow-at a c′ lt 2
          (swapF-o a c′ c (≢sym (<⇒≢ (<F-trans lt q))) (≢sym (<⇒≢ q)))

------------------------------------------------------------------------
-- The hybrid letters
--
-- Every rule of the hybrid letter but the sink move is a two-level
-- relation read through the embedding Φ_s at a sink s off its indices
-- — i_[a] ↦ i_[a] i_[s]³, X ↦ i_[s]² X, K ↦ K i_[s]³ — and Φ_s(u) is
-- u followed by a power of i_[s] (`slide`), i_[s] passing everything u
-- touches.  So a relation u = t gives Φ_s(u) = Φ_s(t) as soon as the
-- two powers agree mod 4 (`frame`), and each rule is one line.

private
  comm-two : ∀ (W x y : WT) → W • x ≈ x • W → W • y ≈ y • W →
             W • (x • y) ≈ (x • y) • W
  comm-two W x y wx wy = begin
    W • (x • y)    ≈⟨ sym assoc ⟩
    (W • x) • y    ≈⟨ front y wx ⟩
    (x • W) • y    ≈⟨ assoc ⟩
    x • (W • y)    ≈⟨ back x wy ⟩
    x • (y • W)    ≈⟨ sym assoc ⟩
    (x • y) • W ∎

  rec< : ∀ {x y : Fin N} → .(x <F y) → x <F y
  rec< {x} {y} p = recompute (x <? y) p

  -- The embedding at the sink s.
  Φs : Fin N → TL.Gen N → WT
  Φs s (TL.i-gen a)     = i a • i s ^ 3
  Φs s (TL.X-gen a b p) = i s • (i s • X a b p)
  Φs s (TL.K-gen a b p) = K a b p • i s ^ 3

  Φsʷ : Fin N → WT → WT
  Φsʷ s [ y ]ʷ  = Φs s y
  Φsʷ s ε       = ε
  Φsʷ s (u • v) = Φsʷ s u • Φsʷ s v

  -- What the sink costs.
  ex : TL.Gen N → ℕ
  ex (TL.i-gen _)     = 3
  ex (TL.X-gen _ _ _) = 2
  ex (TL.K-gen _ _ _) = 3

  exʷ : WT → ℕ
  exʷ [ y ]ʷ  = ex y
  exʷ ε       = 0
  exʷ (u • v) = exʷ u + exʷ v

  -- The sink is off a generator's indices; a phase never minds.
  Off : Fin N → TL.Gen N → Set
  Off s (TL.i-gen _)     = ⊤
  Off s (TL.X-gen a b _) = s ≢ a × s ≢ b
  Off s (TL.K-gen a b _) = s ≢ a × s ≢ b

  Offʷ : Fin N → WT → Set
  Offʷ s [ y ]ʷ  = Off s y
  Offʷ s ε       = ⊤
  Offʷ s (u • v) = Offʷ s u × Offʷ s v

  -- i_[s] passes what is off it.
  s-pass : ∀ (s : Fin N) (u : WT) → Offʷ s u → i s • u ≈ u • i s
  s-pass s [ TL.i-gen a ]ʷ     _         = icomm s a
  s-pass s [ TL.X-gen a b p ]ʷ (sa , sb) = axiom (TL.comm-iX p sa sb)
  s-pass s [ TL.K-gen a b p ]ʷ (sa , sb) = axiom (TL.comm-iK p sa sb)
  s-pass s ε                   _         = trans right-unit (sym left-unit)
  s-pass s (u • v)             (ou , ov) =
    comm-two (i s) u v (s-pass s u ou) (s-pass s v ov)

  s-pow : ∀ (s : Fin N) (u : WT) → Offʷ s u → ∀ k → i s ^ k • u ≈ u • i s ^ k
  s-pow s u o k = sym (pass-pow (sym (s-pass s u o)) k)

  -- Φ_s(u) is u followed by its cost.
  slide : ∀ (s : Fin N) (u : WT) → Offʷ s u → Φsʷ s u ≈ u • i s ^ exʷ u
  slide s [ TL.i-gen a ]ʷ     _ = refl
  slide s [ TL.X-gen a b p ]ʷ o =
    trans (by-assoc Eq.refl) (s-pow s [ TL.X-gen a b p ]ʷ o 2)
  slide s [ TL.K-gen a b p ]ʷ _ = refl
  slide s ε                   _ = sym left-unit
  slide s (u • v)       (ou , ov) = begin
    Φsʷ s u • Φsʷ s v
      ≈⟨ cong (slide s u ou) (slide s v ov) ⟩
    (u • i s ^ m) • (v • i s ^ n)
      ≈⟨ assoc ⟩
    u • (i s ^ m • (v • i s ^ n))
      ≈⟨ back u (sym assoc) ⟩
    u • ((i s ^ m • v) • i s ^ n)
      ≈⟨ back u (front _ (s-pow s v ov m)) ⟩
    u • ((v • i s ^ m) • i s ^ n)
      ≈⟨ back u assoc ⟩
    u • (v • (i s ^ m • i s ^ n))
      ≈⟨ back u (back v (sym (^-+ (i s) m n))) ⟩
    u • (v • i s ^ (m + n))
      ≈⟨ sym assoc ⟩
    (u • v) • i s ^ (m + n) ∎
    where
    m = exʷ u
    n = exʷ v

  -- A relation off the sink holds through it.
  frame : ∀ (s : Fin N) {u t : WT} → u ≈ t → Offʷ s u → Offʷ s t →
          i s ^ exʷ u ≈ i s ^ exʷ t → Φsʷ s u ≈ Φsʷ s t
  frame s {u} {t} e ou ot ext =
    trans (slide s u ou) (trans (cong e ext) (sym (slide s t ot)))

-- The sink moves along a phase pair.
sd-ki-sink : ∀ (a b s t : Fin N) .(ab : a <F b) →
             (K a b ab • i s ^ 3) • (i s • i t ^ 3) ≈ K a b ab • i t ^ 3
sd-ki-sink a b s t ab = begin
  (K a b ab • i s ^ 3) • (i s • i t ^ 3)
    ≈⟨ by-assoc Eq.refl ⟩
  K a b ab • (i s ^ 4 • i t ^ 3)
    ≈⟨ back _ (front _ (i⁴ s)) ⟩
  K a b ab • (ε • i t ^ 3)
    ≈⟨ back _ left-unit ⟩
  K a b ab • i t ^ 3 ∎

sd-ki-pp : ∀ (a b s x : Fin N) .(ab : a <F b) →
           x ≢ a → x ≢ b → s ≢ a → s ≢ b →
           (i x • i s ^ 3) • (K a b ab • i s ^ 3)
           ≈ (K a b ab • i s ^ 3) • (i x • i s ^ 3)
sd-ki-pp a b s x ab xa xb sa sb =
  frame s (axiom (TL.comm-iK ab xa xb)) (tt , (sa , sb)) ((sa , sb) , tt) refl

sd-ki-px : ∀ (a b s x y : Fin N) .(ab : a <F b) .(xy : x <F y) →
           x ≢ a → x ≢ b → y ≢ a → y ≢ b → s ≢ a → s ≢ b → s ≢ x → s ≢ y →
           (i s • (i s • X x y xy)) • (K a b ab • i s ^ 3)
           ≈ (K a b ab • i s ^ 3) • (i s • (i s • X x y xy))
sd-ki-px a b s x y ab xy xa xb ya yb sa sb sx sy =
  frame s (axiom (TL.comm-XK xy ab xa xb ya yb))
        ((sx , sy) , (sa , sb)) ((sa , sb) , (sx , sy)) refl

sd-ki-ki : ∀ (a b c d s : Fin N) .(ab : a <F b) .(cd : c <F d) →
           c ≢ a → c ≢ b → d ≢ a → d ≢ b →
           s ≢ a → s ≢ b → s ≢ c → s ≢ d →
           (K a b ab • i s ^ 3) • (K c d cd • i s ^ 3)
           ≈ (K c d cd • i s ^ 3) • (K a b ab • i s ^ 3)
sd-ki-ki a b c d s ab cd ca cb da db sa sb sc sd =
  frame s (axiom (TL.comm-KK ab cd (≢sym ca) (≢sym da) (≢sym cb) (≢sym db)))
        ((sa , sb) , (sc , sd)) ((sc , sd) , (sa , sb)) refl

sd-ki-swap : ∀ (j k l s : Fin N) .(p : j <F k) .(q : k <F l) →
             s ≢ j → s ≢ k → s ≢ l →
             (K k l q • i s ^ 3) • (i s • (i s • X j k p))
             ≈ (i s • (i s • X j k p)) • (K j l (<F-trans (rec< p) (rec< q)) • i s ^ 3)
sd-ki-swap j k l s p q sj sk sl =
  frame s (axiom (TL.swap-KX (rec< p) (rec< q)))
        ((sk , sl) , (sj , sk)) ((sj , sk) , (sj , sl)) refl

sd-ki-swap′ : ∀ (j k l s : Fin N) .(p : j <F k) .(q : k <F l) →
              s ≢ j → s ≢ k → s ≢ l →
              (K j l (<F-trans (rec< p) (rec< q)) • i s ^ 3) • (i s • (i s • X k l q))
              ≈ (i s • (i s • X k l q)) • (K j k p • i s ^ 3)
sd-ki-swap′ j k l s p q sj sk sl =
  frame s (axiom (TL.swap-KX′ (rec< p) (rec< q)))
        ((sj , sl) , (sk , sl)) ((sk , sl) , (sj , sk)) refl

sd-ki-x : ∀ (a b s : Fin N) .(ab : a <F b) → s ≢ a → s ≢ b →
          (K a b ab • i s ^ 3) • ((i b • i s ^ 3) • (i b • i s ^ 3))
          ≈ (i s • (i s • X a b ab)) • (K a b ab • i s ^ 3)
sd-ki-x a b s ab sa sb =
  frame s (axiom (TL.rel-13 ab)) ((sa , sb) , (tt , tt)) ((sa , sb) , (sa , sb))
        (i-mod4 s 5)

sd-ki-16 : ∀ (a b s : Fin N) .(ab : a <F b) → s ≢ a → s ≢ b →
           (K a b ab • i s ^ 3)
           • ((i b • i s ^ 3) • ((i b • i s ^ 3) • (i b • i s ^ 3)))
           ≈ (i b • i s ^ 3)
             • ((K a b ab • i s ^ 3) • ((i b • i s ^ 3) • (K a b ab • i s ^ 3)))
sd-ki-16 a b s ab sa sb =
  frame s (axiom (TL.rel-14 ab)) ((sa , sb) , (tt , (tt , tt)))
        (tt , ((sa , sb) , (tt , (sa , sb)))) refl

sd-ki-ii : ∀ (a b s : Fin N) .(ab : a <F b) → s ≢ a → s ≢ b →
           (K a b ab • i s ^ 3) • ((i a • i s ^ 3) • (i b • i s ^ 3))
           ≈ (i a • i s ^ 3) • ((i b • i s ^ 3) • (K a b ab • i s ^ 3))
sd-ki-ii a b s ab sa sb =
  frame s (axiom (TL.rel-15 ab)) ((sa , sb) , (tt , tt)) (tt , (tt , (sa , sb))) refl

sd-ki-sq : ∀ (a b s : Fin N) .(ab : a <F b) → s ≢ a → s ≢ b →
           ((K a b ab • i s ^ 3) • (K a b ab • i s ^ 3))
           • ((i a • i s ^ 3) • (i b • i s ^ 3)) ≈ ε
sd-ki-sq a b s ab sa sb =
  frame s (axiom (TL.rel-16 ab)) (((sa , sb) , (sa , sb)) , (tt , tt)) tt
        (trans (i-mod4 s 8) (trans (i-mod4 s 4) (i-mod4 s 0)))

sd-ki-yb : ∀ (j k l m s : Fin N)
             .(jk : j <F k) .(lm : l <F m) .(jl : j <F l) .(km : k <F m) →
           k ≢ l → s ≢ j → s ≢ k → s ≢ l → s ≢ m →
           (K j k jk • i s ^ 3)
           • ((K l m lm • i s ^ 3) • ((K j l jl • i s ^ 3) • (K k m km • i s ^ 3)))
           ≈ (K j l jl • i s ^ 3)
             • ((K k m km • i s ^ 3) • ((K j k jk • i s ^ 3) • (K l m lm • i s ^ 3)))
sd-ki-yb j k l m s jk lm jl km kl sj sk sl sm =
  frame s (axiom (TL.rel-17 jk lm jl km kl))
        ((sj , sk) , ((sl , sm) , ((sj , sl) , (sk , sm))))
        ((sj , sl) , ((sk , sm) , ((sj , sk) , (sl , sm)))) refl

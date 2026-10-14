------------------------------------------------------------------------
-- Presentations of groups
--
-- The two-level derivations of the P′ rules
--
-- Each lemma is one rule of `Rules` read through `asG`: its sides as
-- words over the two-level generators, equal by Bian and Selinger's
-- relations.  In order: the phase-pair rules — pure phase algebra,
-- the phases commuting totally and i⁴ vanishing; the two
-- unconditional K rules, whose proofs are the cancellations through
-- relations (17) and (18) that make them need no disjointness; the
-- exchange letters; the braid and the shrinking rules; the K pairs
-- against disjoint letters; and the K pairs' own algebra — the square
-- (18), the exchange (15), conjugation by the pair's exchange ((15)
-- read both ways), renaming by the swap relations of K against X, and
-- (19) bridged.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Auxiliary.SoundLemmas (N : ℕ) where

open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (_<?_)
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
-- The unconditional K rules

sd-kk-inv : ∀ (a b c d : Fin N) .(ab : a <F b) .(cd : c <F d) →
            (K a b ab • (K c d cd • (i c • i d)))
            • (K c d cd • (K a b ab • (i a • i b))) ≈ ε
sd-kk-inv a b c d ab cd = begin
  (K a b ab • (K c d cd • (i c • i d)))
  • (K c d cd • (K a b ab • (i a • i b)))
    ≈⟨ by-assoc Eq.refl ⟩
  K a b ab • (K c d cd • (((i c • i d) • K c d cd) • (K a b ab • (i a • i b))))
    ≈⟨ back _ (back _ (front _ (iiK c d cd))) ⟩
  K a b ab • (K c d cd • ((K c d cd • (i c • i d)) • (K a b ab • (i a • i b))))
    ≈⟨ by-assoc Eq.refl ⟩
  K a b ab • ((K c d cd • (K c d cd • (i c • i d))) • (K a b ab • (i a • i b)))
    ≈⟨ back _ (front _ (K²ii c d cd)) ⟩
  K a b ab • (ε • (K a b ab • (i a • i b)))
    ≈⟨ back _ left-unit ⟩
  K a b ab • (K a b ab • (i a • i b))
    ≈⟨ K²ii a b ab ⟩
  ε ∎

sd-kk-bridge : ∀ (a b c d e f : Fin N)
                 .(ab : a <F b) .(cd : c <F d) .(ef : e <F f) →
               K a b ab • (K c d cd • (i c • i d))
               ≈ (K a b ab • (K e f ef • (i e • i f)))
                 • (K e f ef • (K c d cd • (i c • i d)))
sd-kk-bridge a b c d e f ab cd ef = sym (begin
  (K a b ab • (K e f ef • (i e • i f)))
  • (K e f ef • (K c d cd • (i c • i d)))
    ≈⟨ by-assoc Eq.refl ⟩
  K a b ab • (K e f ef • (((i e • i f) • K e f ef) • (K c d cd • (i c • i d))))
    ≈⟨ back _ (back _ (front _ (iiK e f ef))) ⟩
  K a b ab • (K e f ef • ((K e f ef • (i e • i f)) • (K c d cd • (i c • i d))))
    ≈⟨ by-assoc Eq.refl ⟩
  K a b ab • ((K e f ef • (K e f ef • (i e • i f))) • (K c d cd • (i c • i d)))
    ≈⟨ back _ (front _ (K²ii e f ef)) ⟩
  K a b ab • (ε • (K c d cd • (i c • i d)))
    ≈⟨ back _ left-unit ⟩
  K a b ab • (K c d cd • (i c • i d)) ∎)

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
-- The K pairs against disjoint letters
--
-- A K-pair image is four factors; against a disjoint letter each
-- factor commutes by its own axiom, and `comm-two`/`comm-quad` stitch
-- the factors back together.  The phases of the first pair's own
-- indices pass as one through relation (17), and the mixed balanced
-- pairs reduce to that by the phase algebra.

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

  comm-quad : ∀ (u v x y L : WT) →
              u • L ≈ L • u → v • L ≈ L • v → x • L ≈ L • x → y • L ≈ L • y →
              (u • (v • (x • y))) • L ≈ L • (u • (v • (x • y)))
  comm-quad u v x y L uL vL xL yL = begin
    (u • (v • (x • y))) • L    ≈⟨ assoc ⟩
    u • ((v • (x • y)) • L)    ≈⟨ back u assoc ⟩
    u • (v • ((x • y) • L))
      ≈⟨ back u (back v (sym (comm-two L x y (sym xL) (sym yL)))) ⟩
    u • (v • (L • (x • y)))    ≈⟨ back u (sym assoc) ⟩
    u • ((v • L) • (x • y))    ≈⟨ back u (front _ vL) ⟩
    u • ((L • v) • (x • y))    ≈⟨ back u assoc ⟩
    u • (L • (v • (x • y)))    ≈⟨ sym assoc ⟩
    (u • L) • (v • (x • y))    ≈⟨ front _ uL ⟩
    (L • u) • (v • (x • y))    ≈⟨ assoc ⟩
    L • (u • (v • (x • y))) ∎

  -- A phase at an index off both pairs passes the K-pair image.
  i-pass : ∀ (a b c d x : Fin N) .(ab : a <F b) .(cd : c <F d) →
           x ≢ a → x ≢ b → x ≢ c → x ≢ d →
           (K a b ab • (K c d cd • (i c • i d))) • i x
           ≈ i x • (K a b ab • (K c d cd • (i c • i d)))
  i-pass a b c d x ab cd xa xb xc xd =
    comm-quad (K a b ab) (K c d cd) (i c) (i d) (i x)
      (sym (axiom (TL.comm-iK ab xa xb)))
      (sym (axiom (TL.comm-iK cd xc xd)))
      (icomm c x) (icomm d x)

  i-pass-pow : ∀ (a b c d x : Fin N) .(ab : a <F b) .(cd : c <F d) →
               x ≢ a → x ≢ b → x ≢ c → x ≢ d → ∀ (n : ℕ) →
               (K a b ab • (K c d cd • (i c • i d))) • i x ^ n
               ≈ i x ^ n • (K a b ab • (K c d cd • (i c • i d)))
  i-pass-pow a b c d x ab cd xa xb xc xd n =
    pass-pow (i-pass a b c d x ab cd xa xb xc xd) n

  -- The first pair's own phases pass as one, relation (17).
  pair-pass : ∀ (a b c d : Fin N) .(ab : a <F b) .(cd : c <F d) →
              c ≢ a → c ≢ b → d ≢ a → d ≢ b →
              (K a b ab • (K c d cd • (i c • i d))) • (i a • i b)
              ≈ (i a • i b) • (K a b ab • (K c d cd • (i c • i d)))
  pair-pass a b c d ab cd ca cb da db =
    comm-quad (K a b ab) (K c d cd) (i c) (i d) (i a • i b)
      (sym (iiK a b ab))
      (comm-two (K c d cd) (i a) (i b)
        (sym (axiom (TL.comm-iK cd (≢sym ca) (≢sym da))))
        (sym (axiom (TL.comm-iK cd (≢sym cb) (≢sym db)))))
      (comm-two (i c) (i a) (i b) (icomm c a) (icomm c b))
      (comm-two (i d) (i a) (i b) (icomm d a) (icomm d b))

  -- The canonical form of a balanced pair squared.
  pair²-can : ∀ (x y : Fin N) →
              (i x • i y) • (i x • i y) ≈ i x ^ 2 • i y ^ 2
  pair²-can x y = begin
    (i x • i y) • (i x • i y)
      ≈⟨ by-assoc Eq.refl ⟩
    i x • ((i y • i x) • i y)
      ≈⟨ back (i x) (front _ (icomm y x)) ⟩
    i x • ((i x • i y) • i y)
      ≈⟨ by-assoc Eq.refl ⟩
    (i x • i x) • (i y • i y) ∎

sd-kk-pp : ∀ (a b c d x y : Fin N) .(ab : a <F b) .(cd : c <F d) →
           x ≢ a → x ≢ b → x ≢ c → x ≢ d → y ≢ a → y ≢ b → y ≢ c → y ≢ d →
           (K a b ab • (K c d cd • (i c • i d))) • (i x • i y ^ 3)
           ≈ (i x • i y ^ 3) • (K a b ab • (K c d cd • (i c • i d)))
sd-kk-pp a b c d x y ab cd xa xb xc xd ya yb yc yd =
  comm-two W (i x) (i y ^ 3)
    (i-pass a b c d x ab cd xa xb xc xd)
    (i-pass-pow a b c d y ab cd ya yb yc yd 3)
  where
  W = K a b ab • (K c d cd • (i c • i d))

sd-kk-px : ∀ (a b c d s x y : Fin N) .(ab : a <F b) .(cd : c <F d)
             .(xy : x <F y) →
           s ≢ a → s ≢ b → s ≢ c → s ≢ d →
           x ≢ a → x ≢ b → x ≢ c → x ≢ d → y ≢ a → y ≢ b → y ≢ c → y ≢ d →
           (K a b ab • (K c d cd • (i c • i d))) • (i s • (i s • X x y xy))
           ≈ (i s • (i s • X x y xy)) • (K a b ab • (K c d cd • (i c • i d)))
sd-kk-px a b c d s x y ab cd xy sa sb sc sd xa xb xc xd ya yb yc yd =
  comm-two W (i s) (i s • X x y xy)
    (i-pass a b c d s ab cd sa sb sc sd)
    (comm-two W (i s) (X x y xy)
      (i-pass a b c d s ab cd sa sb sc sd)
      X-pass)
  where
  W = K a b ab • (K c d cd • (i c • i d))

  X-pass : W • X x y xy ≈ X x y xy • W
  X-pass =
    comm-quad (K a b ab) (K c d cd) (i c) (i d) (X x y xy)
      (sym (axiom (TL.comm-XK xy ab xa xb ya yb)))
      (sym (axiom (TL.comm-XK xy cd xc xd yc yd)))
      (cross-at x y xy (swapF-o x y c (≢sym xc) (≢sym yc)))
      (cross-at x y xy (swapF-o x y d (≢sym xd) (≢sym yd)))

sd-kk-kk : ∀ (a b c d e f g h : Fin N)
             .(ab : a <F b) .(cd : c <F d) .(ef : e <F f) .(gh : g <F h) →
           e ≢ a → e ≢ b → e ≢ c → e ≢ d → f ≢ a → f ≢ b → f ≢ c → f ≢ d →
           g ≢ a → g ≢ b → g ≢ c → g ≢ d → h ≢ a → h ≢ b → h ≢ c → h ≢ d →
           (K a b ab • (K c d cd • (i c • i d)))
           • (K e f ef • (K g h gh • (i g • i h)))
           ≈ (K e f ef • (K g h gh • (i g • i h)))
             • (K a b ab • (K c d cd • (i c • i d)))
sd-kk-kk a b c d e f g h ab cd ef gh
         ea eb ec ed fa fb fc fd ga gb gc gd ha hb hc hd =
  sym (comm-quad (K e f ef) (K g h gh) (i g) (i h) W
        (sym Kef-pass) (sym Kgh-pass)
        (sym (i-pass a b c d g ab cd ga gb gc gd))
        (sym (i-pass a b c d h ab cd ha hb hc hd)))
  where
  W = K a b ab • (K c d cd • (i c • i d))

  Kef-pass : W • K e f ef ≈ K e f ef • W
  Kef-pass =
    comm-quad (K a b ab) (K c d cd) (i c) (i d) (K e f ef)
      (axiom (TL.comm-KK ab ef (≢sym ea) (≢sym fa) (≢sym eb) (≢sym fb)))
      (axiom (TL.comm-KK cd ef (≢sym ec) (≢sym fc) (≢sym ed) (≢sym fd)))
      (axiom (TL.comm-iK ef (≢sym ec) (≢sym fc)))
      (axiom (TL.comm-iK ef (≢sym ed) (≢sym fd)))

  Kgh-pass : W • K g h gh ≈ K g h gh • W
  Kgh-pass =
    comm-quad (K a b ab) (K c d cd) (i c) (i d) (K g h gh)
      (axiom (TL.comm-KK ab gh (≢sym ga) (≢sym ha) (≢sym gb) (≢sym hb)))
      (axiom (TL.comm-KK cd gh (≢sym gc) (≢sym hc) (≢sym gd) (≢sym hd)))
      (axiom (TL.comm-iK gh (≢sym gc) (≢sym hc)))
      (axiom (TL.comm-iK gh (≢sym gd) (≢sym hd)))

sd-kk-mm : ∀ (a b c d : Fin N) .(ab : a <F b) .(cd : c <F d) →
           c ≢ a → c ≢ b → d ≢ a → d ≢ b →
           ((i a • i b ^ 3) • (i a • i b ^ 3))
           • (K a b ab • (K c d cd • (i c • i d)))
           ≈ (K a b ab • (K c d cd • (i c • i d)))
             • ((i a • i b ^ 3) • (i a • i b ^ 3))
sd-kk-mm a b c d ab cd ca cb da db = begin
  ((i a • i b ^ 3) • (i a • i b ^ 3)) • W
    ≈⟨ front W (trans (pp²-can a b) (sym (pair²-can a b))) ⟩
  ((i a • i b) • (i a • i b)) • W
    ≈⟨ assoc ⟩
  (i a • i b) • ((i a • i b) • W)
    ≈⟨ back _ (sym (pair-pass a b c d ab cd ca cb da db)) ⟩
  (i a • i b) • (W • (i a • i b))
    ≈⟨ sym assoc ⟩
  ((i a • i b) • W) • (i a • i b)
    ≈⟨ front _ (sym (pair-pass a b c d ab cd ca cb da db)) ⟩
  (W • (i a • i b)) • (i a • i b)
    ≈⟨ assoc ⟩
  W • ((i a • i b) • (i a • i b))
    ≈⟨ back W (trans (pair²-can a b) (sym (pp²-can a b))) ⟩
  W • ((i a • i b ^ 3) • (i a • i b ^ 3)) ∎
  where
  W = K a b ab • (K c d cd • (i c • i d))

sd-kk-ii : ∀ (a b c d e : Fin N) .(ab : a <F b) .(cd : c <F d) →
           c ≢ a → c ≢ b → d ≢ a → d ≢ b →
           e ≢ a → e ≢ b → e ≢ c → e ≢ d →
           ((i a • i e ^ 3) • (i b • i e ^ 3))
           • (K a b ab • (K c d cd • (i c • i d)))
           ≈ (K a b ab • (K c d cd • (i c • i d)))
             • ((i a • i e ^ 3) • (i b • i e ^ 3))
sd-kk-ii a b c d e ab cd ca cb da db ea eb ec ed = begin
  ((i a • i e ^ 3) • (i b • i e ^ 3)) • W
    ≈⟨ front W mix-can ⟩
  ((i a • i b) • i e ^ 2) • W
    ≈⟨ assoc ⟩
  (i a • i b) • (i e ^ 2 • W)
    ≈⟨ back _ (sym (i-pass-pow a b c d e ab cd ea eb ec ed 2)) ⟩
  (i a • i b) • (W • i e ^ 2)
    ≈⟨ sym assoc ⟩
  ((i a • i b) • W) • i e ^ 2
    ≈⟨ front _ (sym (pair-pass a b c d ab cd ca cb da db)) ⟩
  (W • (i a • i b)) • i e ^ 2
    ≈⟨ assoc ⟩
  W • ((i a • i b) • i e ^ 2)
    ≈⟨ back W (sym mix-can) ⟩
  W • ((i a • i e ^ 3) • (i b • i e ^ 3)) ∎
  where
  W = K a b ab • (K c d cd • (i c • i d))

  mix-can : (i a • i e ^ 3) • (i b • i e ^ 3) ≈ (i a • i b) • i e ^ 2
  mix-can = begin
    (i a • i e ^ 3) • (i b • i e ^ 3)
      ≈⟨ by-assoc Eq.refl ⟩
    i a • ((i e ^ 3 • i b) • i e ^ 3)
      ≈⟨ back (i a) (front _ (ipow-comm e b 3 1)) ⟩
    i a • ((i b • i e ^ 3) • i e ^ 3)
      ≈⟨ by-assoc Eq.refl ⟩
    (i a • i b) • (i e ^ 3 • i e ^ 3)
      ≈⟨ back _ (trans (sym (^-+ (i e) 3 3)) (i-mod4 e 2)) ⟩
    (i a • i b) • i e ^ 2 ∎

------------------------------------------------------------------------
-- The K pairs' own algebra
--
-- The square is relation (18) on each factor, the factors passing
-- each other; the exchange rule is relation (15), Z on the second
-- index becoming the pair's exchange; conjugation by that exchange is
-- (15) used twice, once read backwards as K X = Z K (`KX`, by
-- inverting both sides); the renaming is the two swap relations of K
-- against X, one per exchange of the double exchange; and in the
-- bridged (19) the fresh factors collect at the end, where both sides
-- leave them in the same order.

private
  rec< : ∀ {x y : Fin N} → .(x <F y) → x <F y
  rec< {x} {y} p = recompute (x <? y) p

  -- What passes the second factor K c d • i c • i d.
  iV : ∀ (z c d : Fin N) .(cd : c <F d) → z ≢ c → z ≢ d →
       i z • (K c d cd • (i c • i d)) ≈ (K c d cd • (i c • i d)) • i z
  iV z c d cd zc zd =
    comm-two (i z) (K c d cd) (i c • i d)
      (axiom (TL.comm-iK cd zc zd))
      (comm-two (i z) (i c) (i d) (icomm z c) (icomm z d))

  KV : ∀ (x y c d : Fin N) .(xy : x <F y) .(cd : c <F d) →
       x ≢ c → x ≢ d → y ≢ c → y ≢ d →
       K x y xy • (K c d cd • (i c • i d))
       ≈ (K c d cd • (i c • i d)) • K x y xy
  KV x y c d xy cd xc xd yc yd =
    comm-two (K x y xy) (K c d cd) (i c • i d)
      (axiom (TL.comm-KK xy cd xc xd yc yd))
      (comm-two (K x y xy) (i c) (i d)
        (sym (axiom (TL.comm-iK xy (≢sym xc) (≢sym yc))))
        (sym (axiom (TL.comm-iK xy (≢sym xd) (≢sym yd)))))

  XV : ∀ (x y c d : Fin N) .(xy : x <F y) .(cd : c <F d) →
       x ≢ c → x ≢ d → y ≢ c → y ≢ d →
       X x y xy • (K c d cd • (i c • i d))
       ≈ (K c d cd • (i c • i d)) • X x y xy
  XV x y c d xy cd xc xd yc yd =
    comm-two (X x y xy) (K c d cd) (i c • i d)
      (axiom (TL.comm-XK xy cd xc xd yc yd))
      (comm-two (X x y xy) (i c) (i d)
        (sym (cross-at x y xy (swapF-o x y c (≢sym xc) (≢sym yc))))
        (sym (cross-at x y xy (swapF-o x y d (≢sym xd) (≢sym yd)))))

  -- The phase pair of a K's indices and its inverse, both ways round.
  ii-inv : ∀ (x y : Fin N) → (i x • i y) • (i x ^ 3 • i y ^ 3) ≈ ε
  ii-inv x y = begin
    (i x • i y) • (i x ^ 3 • i y ^ 3)
      ≈⟨ by-assoc Eq.refl ⟩
    i x • ((i y • i x ^ 3) • i y ^ 3)
      ≈⟨ back (i x) (front (i y ^ 3) (ipow-comm y x 1 3)) ⟩
    i x • ((i x ^ 3 • i y) • i y ^ 3)
      ≈⟨ by-assoc Eq.refl ⟩
    i x ^ 4 • i y ^ 4
      ≈⟨ cong (i⁴ x) (i⁴ y) ⟩
    ε • ε
      ≈⟨ left-unit ⟩
    ε ∎

  ii-inv′ : ∀ (x y : Fin N) → (i x ^ 3 • i y ^ 3) • (i x • i y) ≈ ε
  ii-inv′ x y = begin
    (i x ^ 3 • i y ^ 3) • (i x • i y)
      ≈⟨ by-assoc Eq.refl ⟩
    i x ^ 3 • ((i y ^ 3 • i x) • i y)
      ≈⟨ back (i x ^ 3) (front (i y) (ipow-comm y x 3 1)) ⟩
    i x ^ 3 • ((i x • i y ^ 3) • i y)
      ≈⟨ by-assoc Eq.refl ⟩
    i x ^ 4 • i y ^ 4
      ≈⟨ cong (i⁴ x) (i⁴ y) ⟩
    ε • ε
      ≈⟨ left-unit ⟩
    ε ∎

  -- The pair cancels on the right.
  cancel-ii : ∀ (x y : Fin N) {u v : WT} →
              u • (i x • i y) ≈ v • (i x • i y) → u ≈ v
  cancel-ii x y {u} {v} e = begin
    u                                          ≈⟨ sym right-unit ⟩
    u • ε                                      ≈⟨ back u (sym (ii-inv x y)) ⟩
    u • ((i x • i y) • (i x ^ 3 • i y ^ 3))    ≈⟨ sym assoc ⟩
    (u • (i x • i y)) • (i x ^ 3 • i y ^ 3)    ≈⟨ front _ e ⟩
    (v • (i x • i y)) • (i x ^ 3 • i y ^ 3)    ≈⟨ assoc ⟩
    v • ((i x • i y) • (i x ^ 3 • i y ^ 3))    ≈⟨ back v (ii-inv x y) ⟩
    v • ε                                      ≈⟨ right-unit ⟩
    v ∎

  -- Relation (18) solved for the square.
  K² : ∀ (x y : Fin N) .(xy : x <F y) →
       K x y xy • K x y xy ≈ i x ^ 3 • i y ^ 3
  K² x y xy = cancel-ii x y (begin
    (Kxy • Kxy) • (i x • i y)            ≈⟨ assoc ⟩
    Kxy • (Kxy • (i x • i y))            ≈⟨ K²ii x y xy ⟩
    ε                                    ≈⟨ sym (ii-inv′ x y) ⟩
    (i x ^ 3 • i y ^ 3) • (i x • i y) ∎)
    where
    Kxy = K x y xy

  -- The second factor squares to the pair's phases.
  V² : ∀ (c d : Fin N) .(cd : c <F d) →
       (K c d cd • (i c • i d)) • (K c d cd • (i c • i d)) ≈ i c • i d
  V² c d cd = begin
    (Kcd • P) • (Kcd • P)    ≈⟨ by-assoc Eq.refl ⟩
    Kcd • ((P • Kcd) • P)    ≈⟨ back Kcd (front P (iiK c d cd)) ⟩
    Kcd • ((Kcd • P) • P)    ≈⟨ by-assoc Eq.refl ⟩
    (Kcd • (Kcd • P)) • P    ≈⟨ front P (K²ii c d cd) ⟩
    ε • P                    ≈⟨ left-unit ⟩
    P ∎
    where
    Kcd = K c d cd
    P = i c • i d

  -- Relation (15) read backwards: K X = Z K.  Inverted, (15) says
  -- K⁻¹ X = Z K⁻¹, and K⁻¹ is K times the pair's phases, which pass X.
  KX : ∀ (x y : Fin N) .(xy : x <F y) →
       K x y xy • X x y xy ≈ i y ^ 2 • K x y xy
  KX x y xy = cancel-ii x y (begin
    (Kxy • Xxy) • P
      ≈⟨ assoc ⟩
    Kxy • (Xxy • P)
      ≈⟨ back Kxy (sym PX) ⟩
    Kxy • (P • Xxy)
      ≈⟨ sym right-unit ⟩
    (Kxy • (P • Xxy)) • ε
      ≈⟨ back _ (sym (K²ii x y xy)) ⟩
    (Kxy • (P • Xxy)) • (Kxy • (Kxy • P))
      ≈⟨ by-assoc Eq.refl ⟩
    (Kxy • P) • ((Xxy • Kxy) • (Kxy • P))
      ≈⟨ back _ (front _ (sym (axiom (TL.rel-13 xy)))) ⟩
    (Kxy • P) • ((Kxy • i y ^ 2) • (Kxy • P))
      ≈⟨ by-assoc Eq.refl ⟩
    Kxy • ((P • Kxy) • (i y ^ 2 • (Kxy • P)))
      ≈⟨ back Kxy (front _ (iiK x y xy)) ⟩
    Kxy • ((Kxy • P) • (i y ^ 2 • (Kxy • P)))
      ≈⟨ by-assoc Eq.refl ⟩
    (Kxy • (Kxy • P)) • (i y ^ 2 • (Kxy • P))
      ≈⟨ front _ (K²ii x y xy) ⟩
    ε • (i y ^ 2 • (Kxy • P))
      ≈⟨ left-unit ⟩
    i y ^ 2 • (Kxy • P)
      ≈⟨ sym assoc ⟩
    (i y ^ 2 • Kxy) • P ∎)
    where
    Kxy = K x y xy
    Xxy = X x y xy
    P = i x • i y

    PX : P • Xxy ≈ Xxy • P
    PX = begin
      (i x • i y) • Xxy    ≈⟨ assoc ⟩
      i x • (i y • Xxy)    ≈⟨ back (i x) (cross-at x y xy (swapF-b x y)) ⟩
      i x • (Xxy • i x)    ≈⟨ sym assoc ⟩
      (i x • Xxy) • i x    ≈⟨ front (i x) (cross-at x y xy (swapF-a x y)) ⟩
      (Xxy • i y) • i x    ≈⟨ assoc ⟩
      Xxy • (i y • i x)    ≈⟨ back Xxy (icomm y x) ⟩
      Xxy • (i x • i y) ∎

sd-kk-sq : ∀ (a b c d : Fin N) .(ab : a <F b) .(cd : c <F d) →
           c ≢ a → c ≢ b → d ≢ a → d ≢ b →
           (K a b ab • (K c d cd • (i c • i d)))
           • (K a b ab • (K c d cd • (i c • i d)))
           ≈ (i c • i a ^ 3) • (i d • i b ^ 3)
sd-kk-sq a b c d ab cd ca cb da db = begin
  (Kab • V) • (Kab • V)
    ≈⟨ by-assoc Eq.refl ⟩
  Kab • ((V • Kab) • V)
    ≈⟨ back Kab (front V (sym (KV a b c d ab cd
                                 (≢sym ca) (≢sym da) (≢sym cb) (≢sym db)))) ⟩
  Kab • ((Kab • V) • V)
    ≈⟨ by-assoc Eq.refl ⟩
  (Kab • Kab) • (V • V)
    ≈⟨ cong (K² a b ab) (V² c d cd) ⟩
  (i a ^ 3 • i b ^ 3) • (i c • i d)
    ≈⟨ by-assoc Eq.refl ⟩
  i a ^ 3 • ((i b ^ 3 • i c) • i d)
    ≈⟨ back (i a ^ 3) (front (i d) (ipow-comm b c 3 1)) ⟩
  i a ^ 3 • ((i c • i b ^ 3) • i d)
    ≈⟨ by-assoc Eq.refl ⟩
  (i a ^ 3 • i c) • (i b ^ 3 • i d)
    ≈⟨ cong (ipow-comm a c 3 1) (ipow-comm b d 3 1) ⟩
  (i c • i a ^ 3) • (i d • i b ^ 3) ∎
  where
  Kab = K a b ab
  V = K c d cd • (i c • i d)

sd-kk-x : ∀ (a b c d e : Fin N) .(ab : a <F b) .(cd : c <F d) →
          c ≢ a → c ≢ b → d ≢ a → d ≢ b →
          e ≢ a → e ≢ b → e ≢ c → e ≢ d →
          (K a b ab • (K c d cd • (i c • i d)))
          • ((i b • i e ^ 3) • (i b • i e ^ 3))
          ≈ (i e • (i e • X a b ab)) • (K a b ab • (K c d cd • (i c • i d)))
sd-kk-x a b c d e ab cd ca cb da db ea eb ec ed = begin
  (Kab • V) • ((i b • i e ^ 3) • (i b • i e ^ 3))
    ≈⟨ back _ (pp²-can b e) ⟩
  (Kab • V) • (i b ^ 2 • i e ^ 2)
    ≈⟨ by-assoc Eq.refl ⟩
  Kab • ((V • i b ^ 2) • i e ^ 2)
    ≈⟨ back Kab (front _ (pass-pow (sym (iV b c d cd (≢sym cb) (≢sym db))) 2)) ⟩
  Kab • ((i b ^ 2 • V) • i e ^ 2)
    ≈⟨ by-assoc Eq.refl ⟩
  ((Kab • i b ^ 2) • V) • i e ^ 2
    ≈⟨ front _ (front V (axiom (TL.rel-13 ab))) ⟩
  ((Xab • Kab) • V) • i e ^ 2
    ≈⟨ by-assoc Eq.refl ⟩
  Xab • (W • i e ^ 2)
    ≈⟨ back Xab (i-pass-pow a b c d e ab cd ea eb ec ed 2) ⟩
  Xab • (i e ^ 2 • W)
    ≈⟨ sym assoc ⟩
  (Xab • i e ^ 2) • W
    ≈⟨ front W (crossʳ-pow-at a b ab 2 (swapF-o a b e ea eb)) ⟩
  (i e ^ 2 • Xab) • W
    ≈⟨ front W assoc ⟩
  (i e • (i e • Xab)) • W ∎
  where
  Kab = K a b ab
  Xab = X a b ab
  V = K c d cd • (i c • i d)
  W = Kab • V

sd-kk-conj : ∀ (a b c d : Fin N) .(ab : a <F b) .(cd : c <F d) →
             c ≢ a → c ≢ b → d ≢ a → d ≢ b →
             (i b • (i b • X a b ab))
             • ((K a b ab • (K c d cd • (i c • i d)))
                • (i a • (i a • X a b ab)))
             ≈ ((i a • i b ^ 3) • (i a • i b ^ 3))
               • (K a b ab • (K c d cd • (i c • i d)))
sd-kk-conj a b c d ab cd ca cb da db = begin
  (i b • (i b • Xab)) • ((Kab • V) • (i a • (i a • Xab)))
    ≈⟨ by-assoc Eq.refl ⟩
  (i b ^ 2 • Xab) • (Kab • (V • (i a ^ 2 • Xab)))
    ≈⟨ back _ (back Kab (comm-two V (i a ^ 2) Xab Va² VX)) ⟩
  (i b ^ 2 • Xab) • (Kab • ((i a ^ 2 • Xab) • V))
    ≈⟨ by-assoc Eq.refl ⟩
  i b ^ 2 • (Xab • (Kab • ((i a ^ 2 • Xab) • V)))
    ≈⟨ back _ (back Xab (back Kab (front V
         (cross-pow-at a b ab 2 (swapF-a a b))))) ⟩
  i b ^ 2 • (Xab • (Kab • ((Xab • i b ^ 2) • V)))
    ≈⟨ by-assoc Eq.refl ⟩
  i b ^ 2 • (Xab • ((Kab • Xab) • (i b ^ 2 • V)))
    ≈⟨ back _ (back Xab (front _ (KX a b ab))) ⟩
  i b ^ 2 • (Xab • ((i b ^ 2 • Kab) • (i b ^ 2 • V)))
    ≈⟨ by-assoc Eq.refl ⟩
  i b ^ 2 • ((Xab • i b ^ 2) • (Kab • (i b ^ 2 • V)))
    ≈⟨ back _ (front _ (crossʳ-pow-at a b ab 2 (swapF-b a b))) ⟩
  i b ^ 2 • ((i a ^ 2 • Xab) • (Kab • (i b ^ 2 • V)))
    ≈⟨ by-assoc Eq.refl ⟩
  (i b ^ 2 • i a ^ 2) • ((Xab • Kab) • (i b ^ 2 • V))
    ≈⟨ back _ (front _ (sym (axiom (TL.rel-13 ab)))) ⟩
  (i b ^ 2 • i a ^ 2) • ((Kab • i b ^ 2) • (i b ^ 2 • V))
    ≈⟨ by-assoc Eq.refl ⟩
  (i b ^ 2 • i a ^ 2) • (Kab • ((i b ^ 2 • i b ^ 2) • V))
    ≈⟨ back _ (back Kab (front V (trans (by-assoc Eq.refl) (i⁴ b)))) ⟩
  (i b ^ 2 • i a ^ 2) • (Kab • (ε • V))
    ≈⟨ back _ (back Kab left-unit) ⟩
  (i b ^ 2 • i a ^ 2) • (Kab • V)
    ≈⟨ front _ (trans (ipow-comm b a 2 2) (sym (pp²-can a b))) ⟩
  ((i a • i b ^ 3) • (i a • i b ^ 3)) • (Kab • V) ∎
  where
  Kab = K a b ab
  Xab = X a b ab
  V = K c d cd • (i c • i d)

  Va² : V • i a ^ 2 ≈ i a ^ 2 • V
  Va² = pass-pow (sym (iV a c d cd (≢sym ca) (≢sym da))) 2

  VX : V • Xab ≈ Xab • V
  VX = sym (XV a b c d ab cd (≢sym ca) (≢sym da) (≢sym cb) (≢sym db))

sd-kk-ren : ∀ (a b c d e f : Fin N) .(ab : a <F b) .(cd : c <F d)
              .(ae : a <F e) .(bf : b <F f) .(ef : e <F f) →
            c ≢ a → c ≢ b → c ≢ e → c ≢ f → d ≢ a → d ≢ b → d ≢ e → d ≢ f →
            e ≢ a → e ≢ b → f ≢ a → f ≢ b →
            (X a e ae • X b f bf)
            • ((K a b ab • (K c d cd • (i c • i d))) • (X a e ae • X b f bf))
            ≈ K e f ef • (K c d cd • (i c • i d))
sd-kk-ren a b c d e f ab cd ae bf ef ca cb ce cf da db de df ea eb fa fb =
  begin
  D • ((Kab • V) • D)
    ≈⟨ by-assoc Eq.refl ⟩
  D • (Kab • (V • D))
    ≈⟨ back D (back Kab (sym DV)) ⟩
  D • (Kab • (D • V))
    ≈⟨ by-assoc Eq.refl ⟩
  (D • (Kab • D)) • V
    ≈⟨ front V core ⟩
  Kef • V ∎
  where
  ab′ = rec< ab
  ae′ = rec< ae
  bf′ = rec< bf
  ef′ = rec< ef

  Xae = X a e ae
  Xbf = X b f bf
  D = Xae • Xbf
  Kab = K a b ab
  Kaf = K a f (<F-trans ab′ bf′)
  Kef = K e f ef
  V = K c d cd • (i c • i d)

  DV : D • V ≈ V • D
  DV = sym (comm-two V Xae Xbf
         (sym (XV a e c d ae cd (≢sym ca) (≢sym da) (≢sym ce) (≢sym de)))
         (sym (XV b f c d bf cd (≢sym cb) (≢sym db) (≢sym cf) (≢sym df))))

  XX : Xae • Xbf ≈ Xbf • Xae
  XX = axiom (TL.comm-XX ae bf (<⇒≢ ab′) (<⇒≢ (<F-trans ab′ bf′))
                         eb (<⇒≢ ef′))

  -- X_bf renames b to f: K_ab becomes K_af (swap-KX′) ...
  c₁ : Xbf • (Kab • Xbf) ≈ Kaf
  c₁ = begin
    Xbf • (Kab • Xbf)    ≈⟨ sym assoc ⟩
    (Xbf • Kab) • Xbf    ≈⟨ front Xbf (sym (axiom (TL.swap-KX′ ab′ bf′))) ⟩
    (Kaf • Xbf) • Xbf    ≈⟨ assoc ⟩
    Kaf • (Xbf • Xbf)    ≈⟨ back Kaf (X² b f bf) ⟩
    Kaf • ε              ≈⟨ right-unit ⟩
    Kaf ∎

  -- ... and X_ae renames a to e: K_af becomes K_ef (swap-KX).
  c₂ : Xae • (Kaf • Xae) ≈ Kef
  c₂ = begin
    Xae • (Kaf • Xae)    ≈⟨ sym assoc ⟩
    (Xae • Kaf) • Xae    ≈⟨ front Xae (sym (axiom (TL.swap-KX ae′ ef′))) ⟩
    (Kef • Xae) • Xae    ≈⟨ assoc ⟩
    Kef • (Xae • Xae)    ≈⟨ back Kef (X² a e ae) ⟩
    Kef • ε              ≈⟨ right-unit ⟩
    Kef ∎

  core : D • (Kab • D) ≈ Kef
  core = begin
    (Xae • Xbf) • (Kab • (Xae • Xbf))
      ≈⟨ back _ (back Kab XX) ⟩
    (Xae • Xbf) • (Kab • (Xbf • Xae))
      ≈⟨ by-assoc Eq.refl ⟩
    Xae • ((Xbf • (Kab • Xbf)) • Xae)
      ≈⟨ back Xae (front Xae c₁) ⟩
    Xae • (Kaf • Xae)
      ≈⟨ c₂ ⟩
    Kef ∎

-- The bridged (19): each side is a K-word followed by the fresh
-- factors V₁ V₂ V₁ V₂, the K-words being the two sides of (19).
private
  module Collect (e f g h : Fin N) .(ef : e <F f) .(gh : g <F h) where

    V₁ V₂ : WT
    V₁ = K e f ef • (i e • i f)
    V₂ = K g h gh • (i g • i h)

    collect : ∀ (A B C D : TL.Gen N) →
              V₁ • [ B ]ʷ ≈ [ B ]ʷ • V₁ → V₁ • [ C ]ʷ ≈ [ C ]ʷ • V₁ →
              V₁ • [ D ]ʷ ≈ [ D ]ʷ • V₁ →
              V₂ • [ C ]ʷ ≈ [ C ]ʷ • V₂ → V₂ • [ D ]ʷ ≈ [ D ]ʷ • V₂ →
              ([ A ]ʷ • V₁)
              • (([ B ]ʷ • V₂) • (([ C ]ʷ • V₁) • ([ D ]ʷ • V₂)))
              ≈ ([ A ]ʷ • ([ B ]ʷ • ([ C ]ʷ • [ D ]ʷ)))
                • (V₁ • (V₂ • (V₁ • V₂)))
    collect A B C D VB VC VD WC WD = begin
      (wa • V₁) • ((wb • V₂) • ((wc • V₁) • (wd • V₂)))
        ≈⟨ by-assoc Eq.refl ⟩
      wa • ((V₁ • wb) • (V₂ • (wc • (V₁ • (wd • V₂)))))
        ≈⟨ back wa (front _ VB) ⟩
      wa • ((wb • V₁) • (V₂ • (wc • (V₁ • (wd • V₂)))))
        ≈⟨ by-assoc Eq.refl ⟩
      wa • (wb • (((V₁ • V₂) • wc) • (V₁ • (wd • V₂))))
        ≈⟨ back wa (back wb (front _
             (sym (comm-two wc V₁ V₂ (sym VC) (sym WC))))) ⟩
      wa • (wb • ((wc • (V₁ • V₂)) • (V₁ • (wd • V₂))))
        ≈⟨ by-assoc Eq.refl ⟩
      wa • (wb • (wc • (((V₁ • (V₂ • V₁)) • wd) • V₂)))
        ≈⟨ back wa (back wb (back wc (front V₂
             (sym (comm-two wd V₁ (V₂ • V₁) (sym VD)
                    (comm-two wd V₂ V₁ (sym WD) (sym VD))))))) ⟩
      wa • (wb • (wc • ((wd • (V₁ • (V₂ • V₁))) • V₂)))
        ≈⟨ by-assoc Eq.refl ⟩
      (wa • (wb • (wc • wd))) • (V₁ • (V₂ • (V₁ • V₂))) ∎
      where
      wa = [ A ]ʷ
      wb = [ B ]ʷ
      wc = [ C ]ʷ
      wd = [ D ]ʷ

sd-kk-yb : ∀ (a b c d e f g h : Fin N)
             .(ab : a <F b) .(cd : c <F d) .(ac : a <F c) .(bd : b <F d)
             .(ef : e <F f) .(gh : g <F h) →
           b ≢ c →
           e ≢ a → e ≢ b → e ≢ c → e ≢ d → f ≢ a → f ≢ b → f ≢ c → f ≢ d →
           g ≢ a → g ≢ b → g ≢ c → g ≢ d → h ≢ a → h ≢ b → h ≢ c → h ≢ d →
           g ≢ e → g ≢ f → h ≢ e → h ≢ f →
           (K a b ab • (K e f ef • (i e • i f)))
           • ((K c d cd • (K g h gh • (i g • i h)))
              • ((K a c ac • (K e f ef • (i e • i f)))
                 • (K b d bd • (K g h gh • (i g • i h)))))
           ≈ (K a c ac • (K e f ef • (i e • i f)))
             • ((K b d bd • (K g h gh • (i g • i h)))
                • ((K a b ab • (K e f ef • (i e • i f)))
                   • (K c d cd • (K g h gh • (i g • i h)))))
sd-kk-yb a b c d e f g h ab cd ac bd ef gh bc
         ea eb ec ed fa fb fc fd ga gb gc gd ha hb hc hd ge gf he hf =
  trans (collect (TL.K-gen a b ab) (TL.K-gen c d cd)
                 (TL.K-gen a c ac) (TL.K-gen b d bd)
                 (Pe c d cd ec fc ed fd) (Pe a c ac ea fa ec fc)
                 (Pe b d bd eb fb ed fd)
                 (Pg a c ac ga ha gc hc) (Pg b d bd gb hb gd hd))
  (trans (front _ (axiom (TL.rel-17 ab cd ac bd bc)))
  (sym (collect (TL.K-gen a c ac) (TL.K-gen b d bd)
                (TL.K-gen a b ab) (TL.K-gen c d cd)
                (Pe b d bd eb fb ed fd) (Pe a b ab ea fa eb fb)
                (Pe c d cd ec fc ed fd)
                (Pg a b ab ga ha gb hb) (Pg c d cd gc hc gd hd))))
  where
  open Collect e f g h ef gh

  Pe : ∀ (x y : Fin N) .(xy : x <F y) → e ≢ x → f ≢ x → e ≢ y → f ≢ y →
       V₁ • K x y xy ≈ K x y xy • V₁
  Pe x y xy ex fx ey fy =
    sym (KV x y e f xy ef (≢sym ex) (≢sym fx) (≢sym ey) (≢sym fy))

  Pg : ∀ (x y : Fin N) .(xy : x <F y) → g ≢ x → h ≢ x → g ≢ y → h ≢ y →
       V₂ • K x y xy ≈ K x y xy • V₂
  Pg x y xy gx hx gy hy =
    sym (KV x y g h xy gh (≢sym gx) (≢sym hx) (≢sym gy) (≢sym hy))

------------------------------------------------------------------------
-- The braid: relation (16)
--
-- On a pair, K i_[a] K = i_[b] K i_[b]: relation (16), K i_b³ =
-- i_b K i_b K, closed by a K⁻¹ = K i_a i_b on the right ((18)), the
-- pair's phases passing K ((17)).  The second factor K⁻¹ satisfies the
-- inverse statement, which is (16) multiplied by i_b³ on the left.

private
  -- i_y³ i_x i_y and i_x i_y i_y³ are i_x.
  ph-x : ∀ (x y : Fin N) → i y ^ 3 • (i x • i y) ≈ i x
  ph-x x y = begin
    i y ^ 3 • (i x • i y)    ≈⟨ by-assoc Eq.refl ⟩
    (i y ^ 3 • i x) • i y    ≈⟨ front (i y) (ipow-comm y x 3 1) ⟩
    (i x • i y ^ 3) • i y    ≈⟨ by-assoc Eq.refl ⟩
    i x • i y ^ 4            ≈⟨ back (i x) (i⁴ y) ⟩
    i x • ε                  ≈⟨ right-unit ⟩
    i x ∎

  ph-x′ : ∀ (x y : Fin N) → (i x • i y) • i y ^ 3 ≈ i x
  ph-x′ x y = begin
    (i x • i y) • i y ^ 3    ≈⟨ by-assoc Eq.refl ⟩
    i x • i y ^ 4            ≈⟨ back (i x) (i⁴ y) ⟩
    i x • ε                  ≈⟨ right-unit ⟩
    i x ∎

  ph-y : ∀ (x y : Fin N) → (i x • i y) • i x ^ 3 ≈ i y
  ph-y x y = begin
    (i x • i y) • i x ^ 3    ≈⟨ by-assoc Eq.refl ⟩
    i x • (i y • i x ^ 3)    ≈⟨ back (i x) (ipow-comm y x 1 3) ⟩
    i x • (i x ^ 3 • i y)    ≈⟨ by-assoc Eq.refl ⟩
    i x ^ 4 • i y            ≈⟨ front (i y) (i⁴ x) ⟩
    ε • i y                  ≈⟨ left-unit ⟩
    i y ∎

  -- K i_x K = i_y K i_y.
  KiK : ∀ (x y : Fin N) .(xy : x <F y) →
        K x y xy • (i x • K x y xy) ≈ i y • (K x y xy • i y)
  KiK x y xy = sym (begin
    i y • (Kxy • i y)
      ≈⟨ sym right-unit ⟩
    (i y • (Kxy • i y)) • ε
      ≈⟨ back _ (sym (K²ii x y xy)) ⟩
    (i y • (Kxy • i y)) • (Kxy • (Kxy • P))
      ≈⟨ by-assoc Eq.refl ⟩
    (i y • (Kxy • (i y • Kxy))) • (Kxy • P)
      ≈⟨ front _ (sym (axiom (TL.rel-14 xy))) ⟩
    (Kxy • i y ^ 3) • (Kxy • P)
      ≈⟨ back _ (sym (iiK x y xy)) ⟩
    (Kxy • i y ^ 3) • (P • Kxy)
      ≈⟨ by-assoc Eq.refl ⟩
    Kxy • ((i y ^ 3 • P) • Kxy)
      ≈⟨ back Kxy (front Kxy (ph-x x y)) ⟩
    Kxy • (i x • Kxy) ∎)
    where
    Kxy = K x y xy
    P = i x • i y

  -- (16) multiplied by i_y³: K i_y K = i_y³ K i_y³.
  KiK′ : ∀ (x y : Fin N) .(xy : x <F y) →
         K x y xy • (i y • K x y xy) ≈ i y ^ 3 • (K x y xy • i y ^ 3)
  KiK′ x y xy = begin
    Kxy • (i y • Kxy)
      ≈⟨ sym left-unit ⟩
    ε • (Kxy • (i y • Kxy))
      ≈⟨ front _ (sym (trans (by-assoc Eq.refl) (i⁴ y))) ⟩
    (i y ^ 3 • i y) • (Kxy • (i y • Kxy))
      ≈⟨ assoc ⟩
    i y ^ 3 • (i y • (Kxy • (i y • Kxy)))
      ≈⟨ back _ (sym (axiom (TL.rel-14 xy))) ⟩
    i y ^ 3 • (Kxy • i y ^ 3) ∎
    where
    Kxy = K x y xy

  -- The inverse statement for K⁻¹ = K i_x i_y.
  KiK⁻ : ∀ (x y : Fin N) .(xy : x <F y) →
         (K x y xy • (i x • i y)) • (i x ^ 3 • (K x y xy • (i x • i y)))
         ≈ i y ^ 3 • ((K x y xy • (i x • i y)) • i y ^ 3)
  KiK⁻ x y xy = trans lhs (sym rhs)
    where
    Kxy = K x y xy
    P = i x • i y

    lhs : (Kxy • P) • (i x ^ 3 • (Kxy • P)) ≈ i y ^ 3 • (Kxy • i x)
    lhs = begin
      (Kxy • P) • (i x ^ 3 • (Kxy • P))
        ≈⟨ by-assoc Eq.refl ⟩
      Kxy • ((P • i x ^ 3) • (Kxy • P))
        ≈⟨ back Kxy (front _ (ph-y x y)) ⟩
      Kxy • (i y • (Kxy • P))
        ≈⟨ by-assoc Eq.refl ⟩
      (Kxy • (i y • Kxy)) • P
        ≈⟨ front P (KiK′ x y xy) ⟩
      (i y ^ 3 • (Kxy • i y ^ 3)) • P
        ≈⟨ by-assoc Eq.refl ⟩
      i y ^ 3 • (Kxy • (i y ^ 3 • P))
        ≈⟨ back _ (back Kxy (ph-x x y)) ⟩
      i y ^ 3 • (Kxy • i x) ∎

    rhs : i y ^ 3 • ((Kxy • P) • i y ^ 3) ≈ i y ^ 3 • (Kxy • i x)
    rhs = begin
      i y ^ 3 • ((Kxy • P) • i y ^ 3)
        ≈⟨ back _ assoc ⟩
      i y ^ 3 • (Kxy • (P • i y ^ 3))
        ≈⟨ back _ (back Kxy (ph-x′ x y)) ⟩
      i y ^ 3 • (Kxy • i x) ∎

sd-kk-braid : ∀ (a b c d : Fin N) .(ab : a <F b) .(cd : c <F d) →
              c ≢ a → c ≢ b → d ≢ a → d ≢ b →
              (K a b ab • (K c d cd • (i c • i d)))
              • ((i a • i c ^ 3) • (K a b ab • (K c d cd • (i c • i d))))
              ≈ (i b • i d ^ 3)
                • ((K a b ab • (K c d cd • (i c • i d))) • (i b • i d ^ 3))
sd-kk-braid a b c d ab cd ca cb da db = begin
  (Kab • V) • ((i a • i c ^ 3) • (Kab • V))
    ≈⟨ by-assoc Eq.refl ⟩
  Kab • ((V • i a) • ((i c ^ 3 • Kab) • V))
    ≈⟨ back Kab (cong (sym (iV a c d cd (≢sym ca) (≢sym da))) (front V c³K)) ⟩
  Kab • ((i a • V) • ((Kab • i c ^ 3) • V))
    ≈⟨ by-assoc Eq.refl ⟩
  Kab • (i a • ((V • Kab) • (i c ^ 3 • V)))
    ≈⟨ back Kab (back (i a) (front _ (sym (KV a b c d ab cd
                              (≢sym ca) (≢sym da) (≢sym cb) (≢sym db))))) ⟩
  Kab • (i a • ((Kab • V) • (i c ^ 3 • V)))
    ≈⟨ by-assoc Eq.refl ⟩
  (Kab • (i a • Kab)) • (V • (i c ^ 3 • V))
    ≈⟨ cong (KiK a b ab) (KiK⁻ c d cd) ⟩
  (i b • (Kab • i b)) • (i d ^ 3 • (V • i d ^ 3))
    ≈⟨ by-assoc Eq.refl ⟩
  i b • (((Kab • i b) • i d ^ 3) • (V • i d ^ 3))
    ≈⟨ back (i b) (front _ (sym (comm-two (i d ^ 3) Kab (i b) d³K
                                          (ipow-comm d b 3 1)))) ⟩
  i b • ((i d ^ 3 • (Kab • i b)) • (V • i d ^ 3))
    ≈⟨ by-assoc Eq.refl ⟩
  (i b • i d ^ 3) • (Kab • ((i b • V) • i d ^ 3))
    ≈⟨ back _ (back Kab (front _ (iV b c d cd (≢sym cb) (≢sym db)))) ⟩
  (i b • i d ^ 3) • (Kab • ((V • i b) • i d ^ 3))
    ≈⟨ by-assoc Eq.refl ⟩
  (i b • i d ^ 3) • ((Kab • V) • (i b • i d ^ 3)) ∎
  where
  Kab = K a b ab
  V = K c d cd • (i c • i d)

  c³K : i c ^ 3 • Kab ≈ Kab • i c ^ 3
  c³K = sym (pass-pow (sym (axiom (TL.comm-iK ab ca cb))) 3)

  d³K : i d ^ 3 • Kab ≈ Kab • i d ^ 3
  d³K = sym (pass-pow (sym (axiom (TL.comm-iK ab da db))) 3)

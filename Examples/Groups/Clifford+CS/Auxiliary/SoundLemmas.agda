------------------------------------------------------------------------
-- Presentations of groups
--
-- The two-level derivations of the P′ rules, first part
--
-- Each lemma is one rule of `Rules` read through `asG`: its sides as
-- words over the two-level generators, equal by Bian and Selinger's
-- relations.  This part has the phase-pair rules — pure phase algebra,
-- the phases commuting totally and i⁴ vanishing — and the two
-- unconditional K rules, whose proofs are the cancellations through
-- relations (17) and (18) that make them need no disjointness.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Auxiliary.SoundLemmas (N : ℕ) where

open import Data.Fin using (Fin ; toℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
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

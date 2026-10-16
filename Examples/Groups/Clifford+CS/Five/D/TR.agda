------------------------------------------------------------------------
-- Presentations of groups
--
-- The transports of the de-borrowing
--
-- Each replaces λᵇ(el) by λᵇ(er) for an equation el = er on the wires
-- 0 1 of the domain (control wire 4), the de-borrowing using it at other
-- wires by renaming: Five.Transport2.transport₂ of the two-wire
-- derivation the windows record carries (WsL), given the λ-images of the
-- instances on two wires (`ok₂`, from the lemmas of Five.D).  Written by
-- `scratchpad/five/transport5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.TR where

open import Data.List using (List ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; e2-01 ; e2-02 ; e2-03 ; e2-04 ; e2-05 ; e2-06 ; e2-07 ; e2-08 ; e2-09 ; e2-10 ; e2-11 ; e2-12 ; e2-13 ; e2-14 ; e2-15 ; e2-16 ; e2-17 ; e2-18 ; e2-19)
open import Examples.Groups.Clifford+CS.Five.Transport2 using (Ok₂ ; transport₂ ; lam⁰₂)
open import Examples.Groups.Clifford+CS.Five.D.TRL using (lem-calc-x4x4 ; lem-tr-CS-K0-at-0 ; lem-tr-CS-K1-at-0 ; lem-tr-X-CS0-at-0 ; lem-tr-X-CS1-at-0 ; lem-tr-comm-CS-S0-at-0 ; lem-tr-comm-CS-S1-at-0 ; lem-tr-comm1-K-I-at-0 ; lem-tr-comm1-K-I-at-1 ; lem-tr-comm1-K-K0-at-0 ; lem-tr-comm1-K-S0-at-0 ; lem-tr-comm1-S-I-at-0 ; lem-tr-comm1-S-I-at-1 ; lem-tr-comm1-S-K0-at-0 ; lem-tr-comm1-S-S0-at-0 ; lem-tr-comm2-I-at-0 ; lem-tr-order-CS-at-0 ; lem-tr-order-I-at-0 ; lem-tr-order-I-at-1 ; lem-tr-order-I-at-2 ; lem-tr-order-K-at-0 ; lem-tr-order-K-at-1 ; lem-tr-order-S-at-0 ; lem-tr-order-S-at-1 ; lem-tr-order-SK-at-0 ; lem-tr-order-SK-at-1)

ok₂ : Ws → Ok₂
ok₂ c4 (srel order-I) = lem-tr-order-I-at-0 c4
ok₂ c4 (cong↑ (srel order-I)) = lem-tr-order-I-at-1 c4
ok₂ c4 (cong↑ (cong↑ (srel order-I))) = lem-tr-order-I-at-2 c4
ok₂ c4 (srel order-S) = lem-tr-order-S-at-0 c4
ok₂ c4 (cong↑ (srel order-S)) = lem-tr-order-S-at-1 c4
ok₂ c4 (srel order-K) = lem-tr-order-K-at-0 c4
ok₂ c4 (cong↑ (srel order-K)) = lem-tr-order-K-at-1 c4
ok₂ c4 (srel order-SK) = lem-tr-order-SK-at-0 c4
ok₂ c4 (cong↑ (srel order-SK)) = lem-tr-order-SK-at-1 c4
ok₂ c4 (srel order-CS) = lem-tr-order-CS-at-0 c4
ok₂ c4 (srel comm-CS-S₀) = lem-tr-comm-CS-S0-at-0 c4
ok₂ c4 (srel comm-CS-S₁) = lem-tr-comm-CS-S1-at-0 c4
ok₂ c4 (srel X-CS₀) = lem-tr-X-CS0-at-0 c4
ok₂ c4 (srel X-CS₁) = lem-tr-X-CS1-at-0 c4
ok₂ c4 (srel CS-K₀) = lem-tr-CS-K0-at-0 c4
ok₂ c4 (srel CS-K₁) = lem-tr-CS-K1-at-0 c4
ok₂ c4 (comm₁ S-gate (gate₀ I-gate)) = lem-tr-comm1-S-I-at-0 c4
ok₂ c4 (comm₁ S-gate (gate₀ I-gate ↥)) = lem-tr-comm1-S-I-at-0 c4
ok₂ c4 (comm₁ S-gate (gate₁ S-gate)) = lem-tr-comm1-S-S0-at-0 c4
ok₂ c4 (comm₁ S-gate (gate₁ K-gate)) = lem-tr-comm1-S-K0-at-0 c4
ok₂ c4 (comm₁ K-gate (gate₀ I-gate)) = lem-tr-comm1-K-I-at-0 c4
ok₂ c4 (comm₁ K-gate (gate₀ I-gate ↥)) = lem-tr-comm1-K-I-at-0 c4
ok₂ c4 (comm₁ K-gate (gate₁ S-gate)) = lem-tr-comm1-K-S0-at-0 c4
ok₂ c4 (comm₁ K-gate (gate₁ K-gate)) = lem-tr-comm1-K-K0-at-0 c4
ok₂ c4 (cong↑ (comm₁ S-gate (gate₀ I-gate))) = lem-tr-comm1-S-I-at-1 c4
ok₂ c4 (cong↑ (comm₁ K-gate (gate₀ I-gate))) = lem-tr-comm1-K-I-at-1 c4
ok₂ c4 (comm₂ CS-gate (gate₀ I-gate)) = lem-tr-comm2-I-at-0 c4
ok₂ c4 (ω↑=ω I-gate) = refl
ok₂ c4 (cong↑ (ω↑=ω I-gate)) = refl

tr01 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
tr01 c4 = lam⁰₂ (lem-calc-x4x4 c4) (CS • CS • CS • CS • CS • CS • S • iI • S • S • S • CS • (K ↑) • CS • (K ↑) • CS • iI • S • S • S • CS • (K ↑) • CS • (K ↑) • CS • CS • CS) (ε) (transport₂ (ok₂ c4) (e2-01 (lit c4)))

tr02 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
tr02 c4 = lam⁰₂ (lem-calc-x4x4 c4) (CS • CS • CS • CS • CS • CS • (S ↑) • iI • (S ↑) • (S ↑) • (S ↑) • CS • K • CS • K • CS • iI • (S ↑) • (S ↑) • (S ↑) • CS • K • CS • K • CS • CS • CS) (ε) (transport₂ (ok₂ c4) (e2-02 (lit c4)))

tr03 : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
tr03 c4 = transport₂ (ok₂ c4) (e2-03 (lit c4))

tr04 : Ws → ⟪ (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ
tr04 c4 = transport₂ (ok₂ c4) (e2-04 (lit c4))

tr05 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
tr05 c4 = lam⁰₂ (lem-calc-x4x4 c4) (S • iI • S • S • S • CS • (K ↑) • CS • (K ↑) • CS • iI • S • S • S • CS • (K ↑) • CS • (K ↑) • CS) (ε) (transport₂ (ok₂ c4) (e2-05 (lit c4)))

tr06 : Ws → ⟪ (X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
tr06 c4 = lam⁰₂ (lem-calc-x4x4 c4) ((S ↑) • iI • (S ↑) • (S ↑) • (S ↑) • CS • K • CS • K • CS • iI • (S ↑) • (S ↑) • (S ↑) • CS • K • CS • K • CS) (ε) (transport₂ (ok₂ c4) (e2-06 (lit c4)))

tr07 : Ws → ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
tr07 c4 = transport₂ (ok₂ c4) (e2-07 (lit c4))

tr08 : Ws → ⟪ [] ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
tr08 c4 = transport₂ (ok₂ c4) (e2-08 (lit c4))

tr09 : Ws → ⟪ (Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS14 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CK40 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ
tr09 c4 = transport₂ (ok₂ c4) (e2-09 (lit c4))

tr10 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
tr10 c4 = lam⁰₂ (lem-calc-x4x4 c4) (iI • K • K) (ε) (transport₂ (ok₂ c4) (e2-10 (lit c4)))

tr11 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
tr11 c4 = lam⁰₂ (lem-calc-x4x4 c4) (CS • CS • CS • CS) (ε) (transport₂ (ok₂ c4) (e2-11 (lit c4)))

tr12 : Ws → ⟪ (X4 ∷ S4 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
tr12 c4 = lam⁰₂ (lem-calc-x4x4 c4) (iI • iI • iI • iI) (ε) (transport₂ (ok₂ c4) (e2-12 (lit c4)))

tr13 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
tr13 c4 = lam⁰₂ (lem-calc-x4x4 c4) (K • iI • K) (ε) (transport₂ (ok₂ c4) (e2-13 (lit c4)))

tr14 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
tr14 c4 = lam⁰₂ (lem-calc-x4x4 c4) (S • S • S • S) (ε) (transport₂ (ok₂ c4) (e2-14 (lit c4)))

tr15 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
tr15 c4 = lam⁰₂ (lem-calc-x4x4 c4) (K • K • iI) (ε) (transport₂ (ok₂ c4) (e2-15 (lit c4)))

tr16 : Ws → ⟪ (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
tr16 c4 = lam⁰₂ (lem-calc-x4x4 c4) (S • iI • S • S • S • CS • (K ↑) • CS • (K ↑) • CS • CS • CS • CS • S • iI • S • S • S • CS • (K ↑) • CS • (K ↑) • CS • iI • S • S • S • CS • (K ↑) • CS • (K ↑) • CS • CS • iI • S • S • S • CS • (K ↑) • CS • (K ↑) • CS) (ε) (transport₂ (ok₂ c4) (e2-16 (lit c4)))

tr17 : Ws → ⟪ (S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ []) ⟫ʷ
tr17 c4 = transport₂ (ok₂ c4) (e2-17 (lit c4))

tr18 : Ws → ⟪ [] ⟫ʷ ≈ ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ
tr18 c4 = transport₂ (ok₂ c4) (e2-18 (lit c4))

tr19 : Ws → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS14 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
tr19 c4 = transport₂ (ok₂ c4) (e2-19 (lit c4))

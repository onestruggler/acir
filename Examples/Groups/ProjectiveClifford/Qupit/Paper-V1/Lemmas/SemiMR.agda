{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- semi-MR follows from the other four one-wire rules.
--
-- Paper-V1 has five one-wire axioms: order-S, order-H, M-power, semi-MR
-- and comm-HHSHHS.  This module derives semi-MR from the other four, for
-- every odd prime p and every primitive root g, over any relation that
-- has them.  Reduced instantiates it at the rule set without semi-MR.
--
-- The argument is Steinberg's, run in the R-spelling of the multiplier,
-- where R = S • Z^½ is the Pauli-free phase gate.  Write
--
--     m        = H • H                              (= M₋₁)
--     y t      = H • R^t • H³                       (R^t conjugated by H)
--     MR u v   = R^u • H • R^v • H • R^u • H        (XM x at u = x⁻¹, v = x)
--     w u v    = R^u • y v • R^u
--
-- m is central in what H and R generate, and MR u v is w u v • H • m.
-- For a unit x, with v = x and u = x⁻¹:
--
--   1. (R^u • y v)³ ≈ m             from XM x • M x ≈ ε (M-power)
--   2. w u v • m ≈ w (-u) (-v)      from XM x • m ≈ XM (-x)
--                                   (order-H, M-power)
--   3. w u v ≈ y v • R^u • y v      1 at -x, then 2: the braid relation
--   4. w u v • y v ≈ R^u • w u v    3, regrouped
--   5. XM x • R^(v·v) ≈ R • XM x    4 is R^v ↦ R^u across w u v • H;
--                                   iterate it toℕ v times
--
-- At x = g, 5 is semi-MR in Paper-V0's R-spelling, and Shared's
-- SemiMR.R⇒S turns that into Paper-V1's S-spelling of the axiom.  No
-- step distinguishes p = 3.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _-_)

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat


module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.SemiMR
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen
open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime using (toℕ-+)

-- The words only, as in OneWire.
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen

open Clifford-Relations
  using ( Z ; X ; Z⁻¹ ; X⁻¹ ; Z^ ; X^ ; R ; R^ ; SHS' ; SHS ; M ; XM
        ; XM≡M⁻¹ ; M₁ ; M₋₁ ; XM₋₁ ; XM₋₁≡M₋₁ ; XMg ; XMg^ )

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.OneWire
  p-3 p-prime g* g-gen
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.GroupLike
  p-3 p-prime g* g-gen
  using (lemma-pow-mod ; lemma-Induction)
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.XZ
  p-3 p-prime g* g-gen

import Examples.Groups.ProjectiveClifford.Qupit.Shared.PauliBase
  p-3 p-prime g* g-gen as Shared
open Shared using (aux-half+half ; neg-mul)

------------------------------------------------------------------------
-- The derivation
--
-- The parameters are One-Wire-Group's: the four rules, and a grouplike
-- witness for the cancellations in steps 2 and 3.

module SemiMR
  (n : ℕ)
  (Γ : WRel (Gen (₁₊ n)))
  (order-S     : let open PB Γ in S ^ p ≈ ε)
  (order-H     : let open PB Γ in H ^ 2 ≈ XM₋₁)
  (M-power     : let open PB Γ in ∀ k → XMg^ k ≈ XM (g^ k))
  (comm-HHSHHS : let open PB Γ in
                 H • H • S • H • H • S ≈ S • H • H • S • H • H)
  (grouplike   : Grouplike Γ)
  where

  open PB Γ hiding (_===_)
  open PP Γ
  open SR word-setoid
  open Pattern-Assoc
  open Group-Lemmas Γ grouplike using (•-cancelʳ)
  open One-Wire n Γ order-S order-H M-power comm-HHSHHS
  open One-Wire-Group n Γ order-S order-H M-power comm-HHSHHS grouplike

  H³H : H ^ 3 • H ≈ ε
  H³H = trans (sym (^-+ H 3 1)) lemma-order-H

  ------------------------------------------------------------------------
  -- R has order p, so its powers add and multiply in ℤₚ
  --
  -- Paper-V0's One-Wire.lemma-order-R, and SB's Z^-+ and Z^-* with R for
  -- Z.

  lemma-order-R : R ^ p ≈ ε
  lemma-order-R = begin
    (S • Z^ 1/2) ^ p
      ≈⟨ ^-cong (S • Z^ 1/2) (Z^ 1/2 • S) p
                (comm⇒pow-comm 1 (toℕ 1/2) (sym lemma-comm-Z-S)) ⟩
    (Z^ 1/2 • S) ^ p
      ≈⟨ ^-• (Z^ 1/2) S p (comm⇒pow-comm (toℕ 1/2) 1 lemma-comm-Z-S) ⟩
    Z^ 1/2 ^ p • S ^ p
      ≈⟨ cright order-S ⟩
    Z^ 1/2 ^ p • ε
      ≈⟨ right-unit ⟩
    Z^ 1/2 ^ p
      ≈⟨ lemma-order-w^k Z p (toℕ 1/2) lemma-order-Z ⟩
    ε ∎

  R^-+ : ∀ s t → R^ s • R^ t ≈ R^ (s + t)
  R^-+ s t = begin
    R ^ toℕ s • R ^ toℕ t             ≈⟨ sym (^-+ R (toℕ s) (toℕ t)) ⟩
    R ^ (toℕ s Nat.+ toℕ t)           ≈⟨ lemma-pow-mod lemma-order-R (toℕ s Nat.+ toℕ t) ⟩
    R ^ ((toℕ s Nat.+ toℕ t) Nat.% p) ≈⟨ refl' (Eq.cong (R ^_) (Eq.sym (toℕ-+ s t))) ⟩
    R ^ toℕ (s + t) ∎

  R^-* : ∀ s t → (R^ s) ^ toℕ t ≈ R^ (s * t)
  R^-* s t = begin
    (R ^ toℕ s) ^ toℕ t               ≈⟨ ^^ R (toℕ s) (toℕ t) ⟩
    R ^ (toℕ s Nat.* toℕ t)           ≈⟨ lemma-pow-mod lemma-order-R (toℕ s Nat.* toℕ t) ⟩
    R ^ ((toℕ s Nat.* toℕ t) Nat.% p) ≈⟨ refl' (Eq.cong (R ^_) (lemma-toℕ-% s t)) ⟩
    R ^ toℕ (s * t) ∎

  R^-inv : ∀ t → R^ (- t) • R^ t ≈ ε
  R^-inv t = trans (R^-+ (- t) t) (refl' (Eq.cong (λ z → R^ z) (+-inverseˡ t)))

  ------------------------------------------------------------------------
  -- m = H • H commutes with R
  --
  -- Conjugating by m sends S to Z • S (the definition of Z) and Z to
  -- Z⁻¹ (lemma-HH-Z), so it sends R = S • Z^½ to Z • S • Z^-½, which is
  -- S • Z^½ again because Z and S commute and 1 - ½ = ½.  Over S alone m
  -- does not commute with the phase gate; over R it does, which is what
  -- makes the R-spelling the one to argue in.

  HH-HH : HH • HH ≈ ε
  HH-HH = begin
    HH • HH  ≈⟨ by-assoc auto ⟩
    H ^ 4    ≈⟨ lemma-order-H ⟩
    ε ∎

  HH-S-HH : HH • (S • HH) ≈ Z • S
  HH-S-HH = sym (begin
    (H • H • S • H • H • S⁻¹) • S
      ≈⟨ by-passoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2) auto ⟩
    (H • H • S • H • H) • (S⁻¹ • S)
      ≈⟨ cright S⁻¹S ⟩
    (H • H • S • H • H) • ε
      ≈⟨ right-unit ⟩
    H • H • S • H • H
      ≈⟨ by-assoc auto ⟩
    HH • (S • HH) ∎)

  HH-Z^ : ∀ k → HH • Z^ k ≈ Z^ (- k) • HH
  HH-Z^ k = begin
    HH • Z ^ toℕ k
      ≈⟨ lemma-Induction lemma-HH-Z (toℕ k) ⟩
    (Z^ (- ₁)) ^ toℕ k • HH
      ≈⟨ cleft SB.Z^-* (- ₁) k ⟩
    Z^ ((- ₁) * k) • HH
      ≈⟨ refl' (Eq.cong (λ z → Z^ z • HH) (neg-mul k)) ⟩
    Z^ (- k) • HH ∎

  HH-R : HH • R ≈ R • HH
  HH-R = begin
    HH • (S • Z^ 1/2)
      ≈⟨ cright cright sym left-unit ⟩
    HH • (S • (ε • Z^ 1/2))
      ≈⟨ cright cright cleft sym HH-HH ⟩
    HH • (S • ((HH • HH) • Z^ 1/2))
      ≈⟨ by-passoc (□ • (□ • ((□ • □) • □))) ((□ • (□ • □)) • (□ • □)) auto ⟩
    (HH • (S • HH)) • (HH • Z^ 1/2)
      ≈⟨ cong HH-S-HH (HH-Z^ 1/2) ⟩
    (Z • S) • (Z^ (- 1/2) • HH)
      ≈⟨ cleft lemma-comm-Z-S ⟩
    (S • Z) • (Z^ (- 1/2) • HH)
      ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • ((□ • □) • □)) auto ⟩
    S • ((Z • Z^ (- 1/2)) • HH)
      ≈⟨ cright cleft SB.Z^-+ ₁ (- 1/2) ⟩
    S • (Z^ (₁ + - 1/2) • HH)
      ≈⟨ cright cleft refl' (Eq.cong (λ z → Z^ z) half) ⟩
    S • (Z^ 1/2 • HH)
      ≈⟨ sym assoc ⟩
    (S • Z^ 1/2) • HH ∎
    where
    -- 1 - ½ is ½, since ½ + ½ is 1.
    half : ₁ + - 1/2 ≡ 1/2
    half = Eq.trans (Eq.cong (_+ - 1/2) (Eq.sym aux-half+half))
             (Eq.trans (+-assoc 1/2 1/2 (- 1/2))
               (Eq.trans (Eq.cong (1/2 +_) (+-inverseʳ 1/2)) (+-identityʳ 1/2)))

  HH-R^ : ∀ k → HH • R ^ k ≈ R ^ k • HH
  HH-R^ k = comm⇒pow-comm 1 k HH-R

  ------------------------------------------------------------------------
  -- R^t conjugated by H
  --
  -- y t is H • R^t • H⁻¹, with H⁻¹ spelled H ^ 3.  It turns an H on the
  -- left of R^t into one on the right (H-R^), and absorbs the H on both
  -- sides up to an m (H-R^-H) — which is how the blocks of MR become
  -- R-and-y words.

  y : ℤ ₚ → Word (Gen (₁₊ n))
  y t = H • (R^ t • H ^ 3)

  H-R^ : ∀ t → H • R^ t ≈ y t • H
  H-R^ t = sym (begin
    (H • (R^ t • H ^ 3)) • H
      ≈⟨ by-passoc ((□ • (□ • □)) • □) (□ • (□ • (□ • □))) auto ⟩
    H • (R^ t • (H ^ 3 • H))
      ≈⟨ cright cright H³H ⟩
    H • (R^ t • ε)
      ≈⟨ cright right-unit ⟩
    H • R^ t ∎)

  H-R^-H : ∀ t → H • (R^ t • H) ≈ y t • HH
  H-R^-H t = sym (begin
    (H • (R^ t • H ^ 3)) • HH
      ≈⟨ by-passoc ((□ • (□ • □ ^ 3)) • □ ^ 2) (□ • (□ • ((□ ^ 3 • □) • □))) auto ⟩
    H • (R^ t • ((H ^ 3 • H) • H))
      ≈⟨ cright cright cleft H³H ⟩
    H • (R^ t • (ε • H))
      ≈⟨ cright cright left-unit ⟩
    H • (R^ t • H) ∎)

  HH-y : ∀ t → HH • y t ≈ y t • HH
  HH-y t = begin
    HH • (H • (R^ t • H ^ 3))
      ≈⟨ by-passoc (□ ^ 2 • (□ • (□ • □))) (□ • ((□ ^ 2 • □) • □)) auto ⟩
    H • ((HH • R^ t) • H ^ 3)
      ≈⟨ cright cleft HH-R^ (toℕ t) ⟩
    H • ((R^ t • HH) • H ^ 3)
      ≈⟨ by-passoc (□ • ((□ • □ ^ 2) • □ ^ 3)) ((□ • (□ • □ ^ 3)) • □ ^ 2) auto ⟩
    (H • (R^ t • H ^ 3)) • HH ∎

  y-inv : ∀ t → y (- t) • y t ≈ ε
  y-inv t = begin
    (H • (R^ (- t) • H ^ 3)) • (H • (R^ t • H ^ 3))
      ≈⟨ by-passoc ((□ • (□ • □)) • (□ • (□ • □)))
                   (□ • (□ • ((□ • □) • (□ • □)))) auto ⟩
    H • (R^ (- t) • ((H ^ 3 • H) • (R^ t • H ^ 3)))
      ≈⟨ cright cright cleft H³H ⟩
    H • (R^ (- t) • (ε • (R^ t • H ^ 3)))
      ≈⟨ cright cright left-unit ⟩
    H • (R^ (- t) • (R^ t • H ^ 3))
      ≈⟨ cright sym assoc ⟩
    H • ((R^ (- t) • R^ t) • H ^ 3)
      ≈⟨ cright cleft R^-inv t ⟩
    H • (ε • H ^ 3)
      ≈⟨ cright left-unit ⟩
    H • H ^ 3
      ≈⟨ lemma-order-H ⟩
    ε ∎

  -- m commutes with the words of the braid relation, y s • R^t • y s.
  HH-V : ∀ s t → HH • (y s • (R^ t • y s)) ≈ (y s • (R^ t • y s)) • HH
  HH-V s t = begin
    HH • (y s • (R^ t • y s))   ≈⟨ sym assoc ⟩
    (HH • y s) • (R^ t • y s)   ≈⟨ cleft HH-y s ⟩
    (y s • HH) • (R^ t • y s)   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • ((□ • □) • □)) auto ⟩
    y s • ((HH • R^ t) • y s)   ≈⟨ cright cleft HH-R^ (toℕ t) ⟩
    y s • ((R^ t • HH) • y s)   ≈⟨ cright assoc ⟩
    y s • (R^ t • (HH • y s))   ≈⟨ cright cright HH-y s ⟩
    y s • (R^ t • (y s • HH))   ≈⟨ by-passoc (□ • (□ • (□ • □))) ((□ • (□ • □)) • □) auto ⟩
    (y s • (R^ t • y s)) • HH ∎

  -- …and they invert at negated exponents.
  V-inv : ∀ s t → (y (- s) • (R^ (- t) • y (- s))) • (y s • (R^ t • y s)) ≈ ε
  V-inv s t = begin
    (y (- s) • (R^ (- t) • y (- s))) • (y s • (R^ t • y s))
      ≈⟨ by-passoc ((□ • (□ • □)) • (□ • (□ • □)))
                   (□ • (□ • ((□ • □) • (□ • □)))) auto ⟩
    y (- s) • (R^ (- t) • ((y (- s) • y s) • (R^ t • y s)))
      ≈⟨ cright cright cleft y-inv s ⟩
    y (- s) • (R^ (- t) • (ε • (R^ t • y s)))
      ≈⟨ cright cright left-unit ⟩
    y (- s) • (R^ (- t) • (R^ t • y s))
      ≈⟨ cright sym assoc ⟩
    y (- s) • ((R^ (- t) • R^ t) • y s)
      ≈⟨ cright cleft R^-inv t ⟩
    y (- s) • (ε • y s)
      ≈⟨ cright left-unit ⟩
    y (- s) • y s
      ≈⟨ y-inv s ⟩
    ε ∎

  ------------------------------------------------------------------------
  -- The multiplier's R-word, through y
  --
  -- MR u v is XM x at (u, v) = (x⁻¹, x) — XM-bridge — and M x at
  -- (u, v) = (x, x⁻¹) — Bridge.bridge.

  MR : ℤ ₚ → ℤ ₚ → Word (Gen (₁₊ n))
  MR u v = R^ u • (H • (R^ v • (H • (R^ u • H))))

  w : ℤ ₚ → ℤ ₚ → Word (Gen (₁₊ n))
  w u v = R^ u • (y v • R^ u)

  MR-w : ∀ u v → MR u v ≈ (w u v • H) • HH
  MR-w u v = begin
    R^ u • (H • (R^ v • (H • (R^ u • H))))
      ≈⟨ by-passoc (□ • (□ • (□ • (□ • (□ • □)))))
                   (□ • ((□ • (□ • □)) • (□ • □))) auto ⟩
    R^ u • ((H • (R^ v • H)) • (R^ u • H))
      ≈⟨ cright cleft H-R^-H v ⟩
    R^ u • ((y v • HH) • (R^ u • H))
      ≈⟨ by-passoc (□ • ((□ • □) • (□ • □))) (□ • (□ • ((□ • □) • □))) auto ⟩
    R^ u • (y v • ((HH • R^ u) • H))
      ≈⟨ cright cright cleft HH-R^ (toℕ u) ⟩
    R^ u • (y v • ((R^ u • HH) • H))
      ≈⟨ by-passoc (□ • (□ • ((□ • □ ^ 2) • □))) (((□ • (□ • □)) • □) • □ ^ 2) auto ⟩
    ((R^ u • (y v • R^ u)) • H) • HH ∎

  ------------------------------------------------------------------------
  -- Step 1: (R^u • y v)³ ≈ m, from MR u v • MR v u ≈ ε
  --
  -- MR u v • MR v u is three blocks R^u • H • R^v • H; each block is
  -- R^u • y v • m, and the m's commute out and collect to m³ = m.

  cube : ∀ u v → MR u v • MR v u ≈ ε → w u v • (y v • (R^ u • y v)) ≈ HH
  cube u v eq = begin
    w u v • (y v • (R^ u • y v))
      ≈⟨ by-passoc ((□ • (□ • □)) • (□ • (□ • □))) (□ • (□ • (□ • (□ • (□ • □))))) auto ⟩
    T
      ≈⟨ sym right-unit ⟩
    T • ε
      ≈⟨ cright sym HH-HH ⟩
    T • (HH • HH)
      ≈⟨ sym assoc ⟩
    (T • HH) • HH
      ≈⟨ cleft T-HH ⟩
    ε • HH
      ≈⟨ left-unit ⟩
    HH ∎
    where
    Q : Word (Gen (₁₊ n))
    Q = R^ u • y v

    T : Word (Gen (₁₊ n))
    T = R^ u • (y v • (R^ u • (y v • (R^ u • y v))))

    block : R^ u • (H • (R^ v • H)) ≈ Q • HH
    block = trans (cright H-R^-H v) (sym assoc)

    HH-Q : HH • Q ≈ Q • HH
    HH-Q = begin
      HH • (R^ u • y v)   ≈⟨ sym assoc ⟩
      (HH • R^ u) • y v   ≈⟨ cleft HH-R^ (toℕ u) ⟩
      (R^ u • HH) • y v   ≈⟨ assoc ⟩
      R^ u • (HH • y v)   ≈⟨ cright HH-y v ⟩
      R^ u • (y v • HH)   ≈⟨ sym assoc ⟩
      (R^ u • y v) • HH ∎

    T-HH : T • HH ≈ ε
    T-HH = begin
      T • HH
        ≈⟨ by-passoc ((□ • (□ • (□ • (□ • (□ • □))))) • □)
                     ((□ • □) • ((□ • □) • ((□ • □) • □))) auto ⟩
      Q • (Q • (Q • HH))
        ≈⟨ cright cright cleft sym left-unit ⟩
      Q • (Q • ((ε • Q) • HH))
        ≈⟨ cright cright cleft cleft sym HH-HH ⟩
      Q • (Q • (((HH • HH) • Q) • HH))
        ≈⟨ by-passoc ((□ • □) • ((□ • □) • (((□ • □) • (□ • □)) • □)))
                     ((□ • □) • (((□ • □) • □) • (□ • ((□ • □) • □)))) auto ⟩
      Q • ((Q • HH) • (HH • (Q • HH)))
        ≈⟨ cright cleft sym HH-Q ⟩
      Q • ((HH • Q) • (HH • (Q • HH)))
        ≈⟨ by-passoc ((□ • □) • ((□ • (□ • □)) • (□ • ((□ • □) • □))))
                     (((□ • □) • □) • (((□ • □) • □) • ((□ • □) • □))) auto ⟩
      (Q • HH) • ((Q • HH) • (Q • HH))
        ≈⟨ sym (cong block (cong block block)) ⟩
      (R^ u • (H • (R^ v • H)))
        • ((R^ u • (H • (R^ v • H))) • (R^ u • (H • (R^ v • H))))
        ≈⟨ by-passoc ((□ • (□ • (□ • □))) • ((□ • (□ • (□ • □))) • (□ • (□ • (□ • □)))))
                     ((□ • (□ • (□ • (□ • (□ • □))))) • (□ • (□ • (□ • (□ • (□ • □)))))) auto ⟩
      MR u v • MR v u
        ≈⟨ eq ⟩
      ε ∎

  -- M-power, in the two forms the braid relation needs.  XM x is M at
  -- x⁻¹, so it inverts M x …
  XM-M : ∀ (x : ℤ* ₚ) → XM x • M x ≈ ε
  XM-M x = begin
    XM x • M x
      ≡⟨ Eq.cong (_• M x) (XM≡M⁻¹ x) ⟩
    M (x ⁻¹) • M x
      ≈⟨ lemma-M-mul (x ⁻¹) x ⟩
    M (x ⁻¹ *' x)
      ≡⟨ aux-M≡M (x ⁻¹ *' x) (₁ , λ ()) x⁻¹x≡1 ⟩
    M (₁ , λ ())
      ≈⟨ lemma-M1 ⟩
    ε ∎
    where
    x⁻¹x≡1 : (x ⁻¹ *' x) .proj₁ ≡ ₁
    x⁻¹x≡1 = lemma-⁻¹ˡ (x .proj₁) {{nztoℕ {y = x .proj₁} {neq0 = x .proj₂}}}

  -- … and multiplying it by m, which is XM₋₁ (order-H), negates the unit.
  XM-neg : ∀ (x : ℤ* ₚ) → XM x • HH ≈ XM (-' x)
  XM-neg x = begin
    XM x • H ^ 2
      ≈⟨ cright order-H' ⟩
    XM x • M₋₁
      ≡⟨ Eq.cong (_• M₋₁) (XM≡M⁻¹ x) ⟩
    M (x ⁻¹) • M -'₁
      ≈⟨ lemma-M-mul (x ⁻¹) -'₁ ⟩
    M (x ⁻¹ *' -'₁)
      ≡⟨ aux-M≡M (x ⁻¹ *' -'₁) ((-' x) ⁻¹) neg ⟩
    M ((-' x) ⁻¹)
      ≡⟨ Eq.sym (XM≡M⁻¹ (-' x)) ⟩
    XM (-' x) ∎
    where
    -- x⁻¹ · (-1) is -(x⁻¹), which is (-x)⁻¹.
    neg : (x ⁻¹ *' -'₁) .proj₁ ≡ ((-' x) ⁻¹) .proj₁
    neg = Eq.trans (*-comm ((x ⁻¹) .proj₁) (- ₁))
            (Eq.trans (neg-mul ((x ⁻¹) .proj₁)) (Eq.sym (inv-neg-comm x)))

  -- Step 1, at a unit.
  step1 : ∀ (x : ℤ* ₚ) →
          w ((x ⁻¹) .proj₁) (x .proj₁)
            • (y (x .proj₁) • (R^ ((x ⁻¹) .proj₁) • y (x .proj₁)))
          ≈ HH
  step1 x = cube ((x ⁻¹) .proj₁) (x .proj₁)
                 (trans (cong (XM-bridge x) (Bridge.bridge x)) (XM-M x))

  ------------------------------------------------------------------------
  -- Step 2: w u v • m ≈ w (-u) (-v), from MR u v • m ≈ MR (-u) (-v)
  --
  -- Both sides are w • H • m, so cancelling the m and then the H leaves
  -- the w's, with the m from the left moved past the H.

  step2' : ∀ u v u' v' → MR u v • HH ≈ MR u' v' → w u v • HH ≈ w u' v'
  step2' u v u' v' eq = •-cancelʳ {h = H} (•-cancelʳ {h = HH} (begin
    ((w u v • HH) • H) • HH
      ≈⟨ by-passoc (((□ • □ ^ 2) • □) • □ ^ 2) (((□ • □) • □ ^ 2) • □ ^ 2) auto ⟩
    ((w u v • H) • HH) • HH
      ≈⟨ cleft sym (MR-w u v) ⟩
    MR u v • HH
      ≈⟨ eq ⟩
    MR u' v'
      ≈⟨ MR-w u' v' ⟩
    (w u' v' • H) • HH ∎))

  step2 : ∀ (x : ℤ* ₚ) →
          w ((x ⁻¹) .proj₁) (x .proj₁) • HH
          ≈ w (((-' x) ⁻¹) .proj₁) ((-' x) .proj₁)
  step2 x = step2' ((x ⁻¹) .proj₁) (x .proj₁) (((-' x) ⁻¹) .proj₁) ((-' x) .proj₁)
    (begin
      MR ((x ⁻¹) .proj₁) (x .proj₁) • HH                ≈⟨ cleft XM-bridge x ⟩
      XM x • HH                                         ≈⟨ XM-neg x ⟩
      XM (-' x)                                         ≈⟨ sym (XM-bridge (-' x)) ⟩
      MR (((-' x) ⁻¹) .proj₁) ((-' x) .proj₁) ∎)

  ------------------------------------------------------------------------
  -- Step 3: the braid relation w u v ≈ y v • R^u • y v
  --
  -- Step 1 at -x says w (-u) (-v) is m times the inverse of
  -- y (-v) • R^-u • y (-v), and that inverse is y v • R^u • y v; step 2
  -- says w (-u) (-v) is w u v times m.  Cancelling m gives the relation.

  braid' : ∀ u v u' v' →
           w u v • HH ≈ w u' v' →
           w u' v' • (y v' • (R^ u' • y v')) ≈ HH →
           (y v' • (R^ u' • y v')) • (y v • (R^ u • y v)) ≈ ε →
           w u v ≈ y v • (R^ u • y v)
  braid' u v u' v' e2 e1 inv = begin
    w u v              ≈⟨ sym right-unit ⟩
    w u v • ε          ≈⟨ cright sym inv ⟩
    w u v • (V • V')   ≈⟨ sym assoc ⟩
    (w u v • V) • V'   ≈⟨ cleft wV ⟩
    ε • V'             ≈⟨ left-unit ⟩
    V' ∎
    where
    V : Word (Gen (₁₊ n))
    V = y v' • (R^ u' • y v')

    V' : Word (Gen (₁₊ n))
    V' = y v • (R^ u • y v)

    wV : w u v • V ≈ ε
    wV = •-cancelʳ {h = HH} (begin
      (w u v • V) • HH   ≈⟨ assoc ⟩
      w u v • (V • HH)   ≈⟨ cright sym (HH-V v' u') ⟩
      w u v • (HH • V)   ≈⟨ sym assoc ⟩
      (w u v • HH) • V   ≈⟨ cleft e2 ⟩
      w u' v' • V        ≈⟨ e1 ⟩
      HH                 ≈⟨ sym left-unit ⟩
      ε • HH ∎)

  braid : ∀ (x : ℤ* ₚ) →
          w ((x ⁻¹) .proj₁) (x .proj₁)
          ≈ y (x .proj₁) • (R^ ((x ⁻¹) .proj₁) • y (x .proj₁))
  braid x = braid' u v (((-' x) ⁻¹) .proj₁) (- v) (step2 x) (step1 (-' x)) inv
    where
    v = x .proj₁
    u = (x ⁻¹) .proj₁

    -- (-x)⁻¹ is -(x⁻¹): the second exponent is negated as well.
    inv : (y (- v) • (R^ (((-' x) ⁻¹) .proj₁) • y (- v))) • (y v • (R^ u • y v)) ≈ ε
    inv = trans (cleft cright cleft refl' (Eq.cong (λ z → R^ z) (inv-neg-comm x)))
                (V-inv v u)

  ------------------------------------------------------------------------
  -- Steps 4 and 5: conjugation by the multiplier squares R's exponent
  --
  -- The braid relation regroups to w u v • y v ≈ R^u • w u v, which says
  -- that w u v • H carries R^v to R^u.  Iterating, it carries
  -- R^(v·v) = (R^v)^v to (R^u)^v = R^(u·v) = R; and MR u v is w u v • H
  -- times m, which commutes with R.

  semi' : ∀ u v → u * v ≡ ₁ → w u v ≈ y v • (R^ u • y v) →
          MR u v • R^ (v * v) ≈ R • MR u v
  semi' u v uv≡1 br = begin
    MR u v • R^ (v * v)
      ≈⟨ cleft MR-w u v ⟩
    ((w u v • H) • HH) • R^ (v * v)
      ≈⟨ assoc ⟩
    (w u v • H) • (HH • R^ (v * v))
      ≈⟨ cright HH-R^ (toℕ (v * v)) ⟩
    (w u v • H) • (R^ (v * v) • HH)
      ≈⟨ sym assoc ⟩
    ((w u v • H) • R^ (v * v)) • HH
      ≈⟨ cleft U-R ⟩
    (R • (w u v • H)) • HH
      ≈⟨ assoc ⟩
    R • ((w u v • H) • HH)
      ≈⟨ cright sym (MR-w u v) ⟩
    R • MR u v ∎
    where
    -- Step 4.
    wy : w u v • y v ≈ R^ u • w u v
    wy = begin
      (R^ u • (y v • R^ u)) • y v   ≈⟨ by-passoc ((□ • (□ • □)) • □) (□ • (□ • (□ • □))) auto ⟩
      R^ u • (y v • (R^ u • y v))   ≈⟨ cright sym br ⟩
      R^ u • w u v ∎

    UR : (w u v • H) • R^ v ≈ R^ u • (w u v • H)
    UR = begin
      (w u v • H) • R^ v    ≈⟨ assoc ⟩
      w u v • (H • R^ v)    ≈⟨ cright H-R^ v ⟩
      w u v • (y v • H)     ≈⟨ sym assoc ⟩
      (w u v • y v) • H     ≈⟨ cleft wy ⟩
      (R^ u • w u v) • H    ≈⟨ assoc ⟩
      R^ u • (w u v • H) ∎

    -- Step 5: UR iterated toℕ v times.
    U-R : (w u v • H) • R^ (v * v) ≈ R • (w u v • H)
    U-R = begin
      (w u v • H) • R^ (v * v)
        ≈⟨ cright sym (R^-* v v) ⟩
      (w u v • H) • (R^ v) ^ toℕ v
        ≈⟨ lemma-Induction UR (toℕ v) ⟩
      (R^ u) ^ toℕ v • (w u v • H)
        ≈⟨ cleft R^-* u v ⟩
      R^ (u * v) • (w u v • H)
        ≈⟨ cleft refl' (Eq.cong (λ z → R^ z) uv≡1) ⟩
      R • (w u v • H) ∎

  -- At a unit: conjugation by XM x sends R to R^(x²).
  semi : ∀ (x : ℤ* ₚ) → XM x • R^ (x .proj₁ * x .proj₁) ≈ R • XM x
  semi x = begin
    XM x • R^ (v * v)    ≈⟨ cleft sym (XM-bridge x) ⟩
    MR u v • R^ (v * v)  ≈⟨ semi' u v uv≡1 (braid x) ⟩
    R • MR u v           ≈⟨ cright XM-bridge x ⟩
    R • XM x ∎
    where
    v = x .proj₁
    u = (x ⁻¹) .proj₁

    uv≡1 : u * v ≡ ₁
    uv≡1 = lemma-⁻¹ˡ v {{nztoℕ {y = v} {neq0 = x .proj₂}}}

  ------------------------------------------------------------------------
  -- semi-MR
  --
  -- At x = g, semi is Paper-V0's spelling of the rule; SB.SemiMR.R⇒S
  -- turns it into Paper-V1's, which is the statement of the axiom
  -- verbatim.

  lemma-semi-MR-R : XMg {n} • R^ (g * g) ≈ R • XMg
  lemma-semi-MR-R = semi g′

  lemma-semi-MR : XMg {n} • S^ (g * g) • Z^ ((g * g + - g) * 1/2) ≈ S • XMg
  lemma-semi-MR = SB.SemiMR.R⇒S g′ lemma-semi-MR-R

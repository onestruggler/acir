{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The Ex-conjugation algebra of the Paper-V0 rules.
--
-- Paper-V0 axiomatises the swap directly: order-Ex says Ex is an
-- involution, and semi-Ex-S↑ / semi-Ex-H↑ say conjugating by it carries
-- a gate on the upper wire down to the lower one,
--
--     Ex • S ↑ === S • Ex        Ex • H ↑ === H • Ex.
--
-- Everything below is the bookkeeping that turns those three axioms into
-- a usable calculus: the opposite direction (a lower-wire gate goes up),
-- the two-sided conjugation forms, and the extension of all of it from
-- single gates to powers and to whole words.  These are the steps that
-- the corresponding symplectic lemmas get for free from Ex's definition
-- as a CZ/H word — a route that is NOT available here, since the
-- symplectic proofs of lemma-comm-Ex-H' and lemma-comm-Ex-H↑' run
-- through lemma-eqn16 / lemma-eqn17 / lemma-CZH↓CZCZ, i.e. through the
-- CZ-H-CZ relations c10 and c11 that Paper-V0 does not have.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; setoid ; module ≡-Reasoning)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Nat.DivMod
import Data.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Fin.Properties using (toℕ-inject₁ ; toℕ-fromℕ<)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen

open Clifford-Relations
open Lemmas-Clifford
  using (lemma-↑^ ; lemma-Induction ; lemma-Inductionˡ
        ; lemma-comm-S-w↑ ; lemma-comm-H-w↑ ; lemma-comm-Z-w↑
        ; lemma-comm-CZ-w↑)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Multiplier arithmetic on one wire
--
-- Paper-V0 and Simplified-V1 have the SAME six one-wire axioms —
-- order-S, order-H, M-power, semi-MR, order-SH, comm-HHSHHS — so every
-- one-wire lemma of Simplified-V1.Lemmas.Lemmas1 holds here by the same
-- proof.  The ones below are ported verbatim from there, because the
-- proof terms are tied to a particular relation and cannot be reused
-- across the two.
--
-- lemma-M-mul is what the three-wire derivations need: M ½ • M 2 is
-- M 1 is ε, and inserting that resolution of the identity is the step
-- that lets R¹⁴/R¹⁵ rescale a CZ exponent.

module One-Wire (n : ℕ) where

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)

  aux-M≡M : ∀ y y' -> y .proj₁ ≡ y' .proj₁ -> M {n = n} y ≡ M y'
  aux-M≡M y y' eq = begin
    M y ≡⟨ auto ⟩
    R^ x • H • R^ x⁻¹ • H • R^ x • H ≡⟨ Eq.cong₂ (\ xx yy -> R^ xx • H • R^ yy • H • R^ x • H) eq aux-eq ⟩
    R^ x' • H • R^ x'⁻¹ • H • R^ x • H ≡⟨ Eq.cong (\ xx -> R^ x' • H • R^ x'⁻¹ • H • R^ xx • H) eq ⟩
    R^ x' • H • R^ x'⁻¹ • H • R^ x' • H ≡⟨ auto ⟩
    M y' ∎
    where
    open ≡-Reasoning
    x = y .proj₁
    x⁻¹ = ((y ⁻¹) .proj₁ )
    x' = y' .proj₁
    x'⁻¹ = ((y' ⁻¹) .proj₁ )
    aux-eq : x⁻¹ ≡ x'⁻¹
    aux-eq  = begin
      x⁻¹ ≡⟨  Eq.sym  (*-identityʳ x⁻¹) ⟩
      x⁻¹ * ₁ ≡⟨ Eq.cong (x⁻¹ *_) (Eq.sym (lemma-⁻¹ʳ x' {{nztoℕ {y = x'} {neq0 = y' .proj₂} }})) ⟩
      x⁻¹ * (x' * x'⁻¹) ≡⟨ Eq.sym (*-assoc x⁻¹ x' x'⁻¹) ⟩
      (x⁻¹ * x') * x'⁻¹ ≡⟨ Eq.cong (\ xx -> (x⁻¹ * xx) * x'⁻¹) (Eq.sym eq) ⟩
      (x⁻¹ * x) * x'⁻¹ ≡⟨ Eq.cong (_* x'⁻¹) (lemma-⁻¹ˡ x {{nztoℕ {y = x} {neq0 = y .proj₂} }}) ⟩
      ₁ * x'⁻¹ ≡⟨ *-identityˡ x'⁻¹ ⟩
      x'⁻¹ ∎

  lemma-M1 : M (₁ , λ ()) ≈ ε
  lemma-M1 = begin
    M (₁ , λ ()) ≡⟨ aux-M≡M ((₁ , λ ())) (g^ ₀) auto ⟩
    M (g^ ₀) ≈⟨ sym (axiom (M-power ₀)) ⟩
    Mg^ ₀ ≈⟨ refl ⟩
    ε ∎
    where
    open SR word-setoid

  lemma-Mg^p-1=ε : Mg ^ p-1 ≈ ε
  lemma-Mg^p-1=ε = begin
    Mg ^ p-1 ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-fromℕ< (NP.n<1+n p-1))) ⟩
    Mg^ (fromℕ< (NP.n<1+n p-1)) ≈⟨ axiom (M-power (₂₊ (fromℕ< _))) ⟩
    M (g^ p-1') ≡⟨ aux-M≡M (g^ p-1') ((g ^′ p-1 , lemma-g^′k≠0 p-1)) (Eq.cong (g ^′_) (toℕ-fromℕ< (NP.n<1+n p-1))) ⟩
    M (g ^′ p-1 , lemma-g^′k≠0 p-1) ≡⟨ aux-M≡M ((g ^′ p-1 , lemma-g^′k≠0 p-1)) (1ₚ , λ ()) Fermat's-little-theorem' ⟩
    M (1ₚ , λ ()) ≈⟨ sym (axiom (M-power ₀)) ⟩
    ε ∎
    where
    open SR word-setoid
    p-1' = fromℕ< (NP.n<1+n p-1)

  aux-Mg^[kp-1] : ∀ k -> Mg ^ (k Nat.* p-1) ≈ ε
  aux-Mg^[kp-1] k = begin
    Mg ^ (k Nat.* p-1) ≈⟨ refl' (Eq.cong (Mg ^_) (NP.*-comm k p-1)) ⟩
    Mg ^ (p-1 Nat.* k) ≈⟨ sym (^^ Mg p-1 k) ⟩
    (Mg ^ p-1) ^ k ≈⟨ ^-cong (Mg ^ p-1) ε k lemma-Mg^p-1=ε ⟩
    ε ^ k ≈⟨ ε^k=ε k ⟩
    ε ∎
    where
    open SR word-setoid

  lemma-M-mul : ∀ x y -> M x • M y ≈ M (x *' y)
  lemma-M-mul x y = begin
    M x • M y ≈⟨ cong (refl' (aux-M≡M x (g^ k) eqk)) (refl' (aux-M≡M y (g^ l) eql)) ⟩
    M (g^ k) • M (g^ l) ≈⟨ cong (sym (axiom (M-power k))) (sym (axiom (M-power l))) ⟩
    Mg ^ toℕ k • Mg ^ toℕ l ≈⟨ sym (^-+ Mg (toℕ k) (toℕ l)) ⟩
    Mg ^ [k+l] ≡⟨ Eq.cong (Mg ^_) (m≡m%n+[m/n]*n [k+l] p-1) ⟩
    Mg ^ ([k+l]%p-1 Nat.+ [k+l]/p-1 Nat.* p-1) ≈⟨ ^-+ Mg [k+l]%p-1 (([k+l]/p-1 Nat.* p-1)) ⟩
    Mg ^ [k+l]%p-1 • Mg ^ ([k+l]/p-1 Nat.* p-1) ≈⟨ (cright trans refl (aux-Mg^[kp-1] [k+l]/p-1)) ⟩
    Mg ^ [k+l]%p-1 • ε ≈⟨ right-unit ⟩
    Mg ^ [k+l]%p-1 ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-fromℕ< (m%n<n [k+l] p-1))) ⟩
    Mg ^ toℕ ( (fromℕ< (m%n<n [k+l] p-1))) ≡⟨ Eq.cong (Mg ^_) (Eq.sym (toℕ-inject₁ ((fromℕ< (m%n<n [k+l] p-1))))) ⟩
    Mg ^ toℕ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≈⟨ refl ⟩
    Mg^ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≈⟨ axiom (M-power (inject₁ (fromℕ< (m%n<n [k+l] p-1)))) ⟩
    M (g^ (inject₁ (fromℕ< (m%n<n [k+l] p-1)))) ≡⟨ aux-M≡M (g^ (inject₁ (fromℕ< (m%n<n [k+l] p-1)))) (g^′ [k+l]) aux-2 ⟩
    M (g^′ [k+l]) ≡⟨ aux-M≡M (g^′ [k+l]) (g^′ toℕ k *' g^′ toℕ l) aux-1 ⟩
    M (g^′ toℕ k *' g^′ toℕ l) ≡⟨ aux-M≡M (g^′ toℕ k *' g^′ toℕ l) (x *' y) aux-0 ⟩
    M (x *' y) ∎
    where
    k = inject₁ (g-gen x .proj₁)
    l = inject₁ (g-gen y .proj₁)
    eqk : x .proj₁ ≡ (g^ k) .proj₁
    eqk = Eq.sym (lemma-log-inject x)
    eql : y .proj₁ ≡ (g^ l) .proj₁
    eql = Eq.sym (lemma-log-inject y)

    [k+l] = toℕ k Nat.+ toℕ l
    [k+l]%p-1 = [k+l] Nat.% p-1
    [k+l]/p-1 = [k+l] Nat./ p-1

    aux-0 : ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁ ≡ (x *' y) .proj₁
    aux-0 = begin
      ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁ ≡⟨ auto ⟩
      (g^′ toℕ k) .proj₁ * (g^′ toℕ l) .proj₁ ≡⟨ Eq.cong₂ (\ xx yy -> (xx * yy) ) (lemma-log-inject x) (lemma-log-inject y) ⟩
      x .proj₁ * y .proj₁ ≡⟨ auto ⟩
      (x *' y) .proj₁ ∎
      where
      open ≡-Reasoning

    aux-1 : (g^′ [k+l]) .proj₁ ≡ ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁
    aux-1 = begin
      (g^′ [k+l]) .proj₁ ≡⟨ auto ⟩
      (g ^′ [k+l]) ≡⟨ Eq.sym (+-^′-distribʳ g (toℕ k) (toℕ l)) ⟩
      ((g ^′ toℕ k) * (g ^′ toℕ l)) ≡⟨ auto ⟩
      ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁ ∎
      where
      open ≡-Reasoning

    aux-2 : g ^′ toℕ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≡ g ^′ (toℕ k Nat.+ toℕ l)
    aux-2 = begin
      g ^′ toℕ (inject₁ (fromℕ< (m%n<n [k+l] p-1))) ≡⟨ Eq.cong (g ^′_) (toℕ-inject₁ ((fromℕ< (m%n<n [k+l] p-1)))) ⟩
      g ^′ toℕ ( (fromℕ< (m%n<n [k+l] p-1))) ≡⟨ Eq.cong (g ^′_) (toℕ-fromℕ< ((m%n<n [k+l] p-1))) ⟩
      g ^′ [k+l]%p-1 ≡⟨ Eq.sym (aux-g^′-% [k+l]) ⟩
      g ^′ (toℕ k Nat.+ toℕ l) ∎
      where
      open ≡-Reasoning

    -- Opened last, as in Simplified-V1: an `open` in a where-block is
    -- scoped from its own position onward, so putting the setoid
    -- reasoning here keeps `begin_` unambiguous inside the aux-blocks
    -- above, which use ≡-Reasoning instead.
    open SR word-setoid

  ------------------------------------------------------------------------
  -- The resolution of the identity that Lemma 9 inserts
  --
  -- M ½ • M 2 is M (½·2) is M 1 is ε.  Inserting this in the middle of a
  -- word is the unlabelled step of the progress report's Lemma 9: once
  -- the two multipliers are there, semi-M↑CZ / semi-M↓CZ push them
  -- outwards and rescale the exponent of every CZ they pass, which is
  -- what makes the C18 corrections cancel.

  -- The modulus of a bare ₂ is not inferable inside the instance
  -- argument below, so it is pinned down once here.
  2ₚ : ℤ ₚ
  2ₚ = ₂

  ₂* : ℤ* ₚ
  ₂* = (2ₚ , λ ())

  -- H has order 4: order-H makes H² the multiplier by -1, and squaring
  -- that multiplies by 1.
  lemma-M₋₁^2 : M₋₁ ^ 2 ≈ ε
  lemma-M₋₁^2 = begin
    M₋₁ ^ 2 ≈⟨ lemma-M-mul -'₁ -'₁ ⟩
    M (-'₁ *' -'₁) ≡⟨ aux-M≡M (-'₁ *' -'₁) (₁ , (λ ())) aux-0 ⟩
    M₁ ≈⟨ lemma-M1 ⟩
    ε ∎
    where
    open import Algebra.Properties.Ring (+-*-ring p-2)

    aux-0 : (-'₁ *' -'₁) .proj₁ ≡ ₁
    aux-0 = begin
      (- ₁ * - ₁) ≡⟨ -1*x≈-x (- ₁) ⟩
      (- - ₁) ≡⟨ -‿involutive ₁ ⟩
      ₁ ∎
      where
      open ≡-Reasoning
    open SR word-setoid

  -- Stated here rather than used as `axiom order-S` at the point of use:
  -- callers need it at width ₁₊ n to feed lemma-cong↑, and `axiom` is
  -- pinned to the ambient width by the open.
  lemma-order-S : S ^ p ≈ ε
  lemma-order-S = axiom order-S

  lemma-order-H : H ^ 4 ≈ ε
  lemma-order-H = begin
    H ^ 4 ≈⟨ sym assoc ⟩
    HH ^ 2 ≈⟨ cong (axiom order-H) (axiom order-H) ⟩
    M₋₁ ^ 2 ≈⟨ lemma-M₋₁^2 ⟩
    ε ∎
    where
    open SR word-setoid

  lemma-M½·M₂ : M (₂* ⁻¹) • M ₂* ≈ ε
  lemma-M½·M₂ = begin
    M (₂* ⁻¹) • M ₂*   ≈⟨ lemma-M-mul (₂* ⁻¹) ₂* ⟩
    M ((₂* ⁻¹) *' ₂*)  ≡⟨ aux-M≡M ((₂* ⁻¹) *' ₂*) (₁ , λ ()) aux ⟩
    M (₁ , λ ())       ≈⟨ lemma-M1 ⟩
    ε ∎
    where
    aux : ((₂* ⁻¹) *' ₂*) .proj₁ ≡ ₁
    aux = lemma-⁻¹ˡ 2ₚ {{nztoℕ {y = 2ₚ} {neq0 = λ ()} }}
    open SR word-setoid

  ------------------------------------------------------------------------
  -- The multiplier by -1 as a power of the generating multiplier
  --
  -- Stated here, at one wire, rather than where it is used: the callers
  -- need it at two different widths — as it stands for the wire-0
  -- multiplier, and lifted through lemma-cong↑ for the wire-1 one — and
  -- `axiom` is fixed to the ambient width by the open, so it cannot
  -- produce the lower-width statement from inside a two-wire module.

  k₋ : ℤ ₚ
  k₋ = inject₁ (g-gen -'₁ .proj₁)

  j₋ : ℕ
  j₋ = toℕ k₋

  e₋ : (g^ k₋) .proj₁ ≡ -'₁ .proj₁
  e₋ = lemma-log-inject -'₁

  lemma-M₋₁-pow : Mg ^ j₋ ≈ M₋₁
  lemma-M₋₁-pow = begin
    Mg ^ j₋    ≈⟨ axiom (M-power k₋) ⟩
    M (g^ k₋)  ≡⟨ aux-M≡M (g^ k₋) -'₁ e₋ ⟩
    M₋₁ ∎
    where open SR word-setoid

  ------------------------------------------------------------------------
  -- Moving S through the H-H-S-H-H block, and Z as a power
  --
  -- Ported from Simplified-V1.Lemmas: both are one-wire facts over
  -- comm-HHSHHS and order-H, which Paper-V0 shares verbatim.  They are
  -- what the HH-conjugation of the Paulis is built from.

  lemma-comm-SHHS^kHH :
    ∀ k → S • H • H • S ^ k • H • H ≈ (H • H • S ^ k • H • H) • S
  lemma-comm-SHHS^kHH k@0 = begin
    S • H • H • ε • H • H      ≈⟨ by-assoc auto ⟩
    S • H • H • H • H          ≈⟨ cright lemma-order-H ⟩
    S • ε                      ≈⟨ trans right-unit (sym left-unit) ⟩
    ε • S                      ≈⟨ cleft sym lemma-order-H ⟩
    (H • H • H • H) • S        ≈⟨ by-assoc auto ⟩
    (H • H • ε • H • H) • S ∎
    where
    open SR word-setoid
    open Pattern-Assoc
  lemma-comm-SHHS^kHH k@1 = sym (by-assoc-and (axiom comm-HHSHHS) auto auto)
  lemma-comm-SHHS^kHH k@(₁₊ k'@(₁₊ k'')) = begin
    S • H • H • S ^ k • H • H
      ≈⟨ refl ⟩
    S • H • H • (S • S ^ k') • H • H
      ≈⟨ cright cright cright cleft cright sym left-unit ⟩
    S • H • H • (S • ε • S ^ k') • H • H
      ≈⟨ cright cright cright cleft cright cleft sym lemma-order-H ⟩
    S • H • H • (S • (H • H • H • H) • S ^ k') • H • H
      ≈⟨ by-passoc (□ • □ • □ • (□ • □ ^ 4 • □) • □ ^ 2) (□ ^ 6 • □ ^ 5) auto ⟩
    (S • H • H • S • H • H) • H • H • S ^ k' • H • H
      ≈⟨ cleft sym (axiom comm-HHSHHS) ⟩
    (H • H • S • H • H • S) • H • H • S ^ k' • H • H
      ≈⟨ by-passoc (□ ^ 6 • □ ^ 5) (□ ^ 5 • □ ^ 6) auto ⟩
    (H • H • S • H • H) • S • H • H • S ^ k' • H • H
      ≈⟨ cright lemma-comm-SHHS^kHH k' ⟩
    (H • H • S • H • H) • (H • H • S ^ k' • H • H) • S
      ≈⟨ by-passoc (□ ^ 5 • □ ^ 5 • □) (□ ^ 7 • □ ^ 4) auto ⟩
    (H • H • S • H • H • H • H) • S ^ k' • H • H • S
      ≈⟨ cleft (cright cright trans (cright lemma-order-H) right-unit) ⟩
    (H • H • S) • S ^ k' • H • H • S
      ≈⟨ by-passoc (□ ^ 3 • □ ^ 4) (□ • □ • □ ^ 2 • □ ^ 3) auto ⟩
    H • H • (S • S ^ k') • H • H • S
      ≈⟨ by-passoc (□ ^ 6) (□ ^ 5 • □) auto ⟩
    (H • H • S ^ k • H • H) • S ∎
    where
    open SR word-setoid
    open Pattern-Assoc

  lemma-Z^k-ℕ : ∀ k → Z ^ k ≈ H • H • S ^ k • H • H • S⁻¹ ^ k
  lemma-Z^k-ℕ k@0 = sym (by-assoc-and lemma-order-H auto auto)
  lemma-Z^k-ℕ k@1 = refl
  lemma-Z^k-ℕ k@(₁₊ k'@(₁₊ k'')) = begin
    Z • Z ^ k'
      ≈⟨ cright lemma-Z^k-ℕ k' ⟩
    Z • H • H • S ^ k' • H • H • S⁻¹ ^ k'
      ≈⟨ refl ⟩
    (H • H • S • H • H • S⁻¹) • H • H • S ^ k' • H • H • S⁻¹ ^ k'
      ≈⟨ by-passoc (□ ^ 6 • □ ^ 6) (□ ^ 5 • □ ^ 6 • □) auto ⟩
    (H • H • S • H • H) • (S⁻¹ • H • H • S ^ k' • H • H) • S⁻¹ ^ k'
      ≈⟨ cright cleft comm⇒pow-comm p-1 1 (lemma-comm-SHHS^kHH k') ⟩
    (H • H • S • H • H) • ((H • H • S ^ k' • H • H) • S⁻¹) • S⁻¹ ^ k'
      ≈⟨ by-passoc (□ ^ 5 • (□ ^ 5 • □) • □) (□ ^ 7 • □ ^ 3 • □ ^ 2) auto ⟩
    (H • H • S • H • H • H • H) • (S ^ k' • H • H) • S⁻¹ • S⁻¹ ^ k'
      ≈⟨ cleft (cright cright trans (cright lemma-order-H) right-unit) ⟩
    (H • H • S) • (S ^ k' • H • H) • S⁻¹ ^ ₁₊ k'
      ≈⟨ by-passoc (□ ^ 3 • □ ^ 3 • □) (□ ^ 2 • □ ^ 2 • □ ^ 3) auto ⟩
    (H • H) • (S • S ^ k') • H • H • S⁻¹ ^ ₁₊ k'
      ≈⟨ refl ⟩
    (H • H) • S ^ ₁₊ k' • H • H • S⁻¹ ^ ₁₊ k'
      ≈⟨ assoc ⟩
    H • H • S ^ k • H • H • S⁻¹ ^ k ∎
    where
    open SR word-setoid
    open Pattern-Assoc

  lemma-X^k-ℕ : ∀ k → X ^ k ≈ H • S ^ k • H • H • S⁻¹ ^ k • H
  lemma-X^k-ℕ k@0 = sym (by-assoc-and lemma-order-H auto auto)
  lemma-X^k-ℕ k@1 = refl
  lemma-X^k-ℕ k@(₁₊ k'@(₁₊ k'')) = begin
    X • X ^ k'
      ≈⟨ cright lemma-X^k-ℕ k' ⟩
    X • H • S ^ k' • H • H • S⁻¹ ^ k' • H
      ≈⟨ refl ⟩
    (H • S • H • H • S⁻¹ • H) • H • S ^ k' • H • H • S⁻¹ ^ k' • H
      ≈⟨ by-passoc (□ ^ 6 • □ ^ 6) (□ ^ 4 • □ ^ 6 • □ ^ 2) auto ⟩
    (H • S • H • H) • (S⁻¹ • H • H • S ^ k' • H • H) • S⁻¹ ^ k' • H
      ≈⟨ cright cleft comm⇒pow-comm p-1 1 (lemma-comm-SHHS^kHH k') ⟩
    (H • S • H • H) • ((H • H • S ^ k' • H • H) • S⁻¹) • S⁻¹ ^ k' • H
      ≈⟨ by-passoc (□ ^ 4 • (□ ^ 5 • □) • □ ^ 2) (□ ^ 6 • □ ^ 3 • □ ^ 2 • □) auto ⟩
    (H • S • H • H • H • H) • (S ^ k' • H • H) • (S⁻¹ • S⁻¹ ^ k') • H
      ≈⟨ cleft (cright trans (cright lemma-order-H) right-unit) ⟩
    (H • S) • (S ^ k' • H • H) • S⁻¹ ^ k • H
      ≈⟨ by-passoc (□ ^ 2 • □ ^ 3 • □ ^ 2) (□ • □ ^ 2 • □ ^ 4) auto ⟩
    H • (S • S ^ k') • H • H • S⁻¹ ^ k • H
      ≈⟨ refl ⟩
    H • S ^ k • H • H • S⁻¹ ^ k • H ∎
    where
    open SR word-setoid
    open Pattern-Assoc

  ------------------------------------------------------------------------
  -- The Paulis have order p, and Z commutes with S
  --
  -- Ported from Simplified-V1.Lemmas, on the same grounds as the lemmas
  -- above: these are one-wire facts over order-S, order-H and
  -- comm-HHSHHS, which the two rule sets share.  lemma-order-Z is what
  -- lets a Pauli exponent be completed to a full p-th power, and
  -- lemma-comm-Z-S is what takes R = S • Z ^ ½ apart and puts it back
  -- together — the S-versus-R bookkeeping c10 runs on.

  lemma-order-w^k : ∀ (w : Word (Gen (₁₊ n))) o k → w ^ o ≈ ε → (w ^ k) ^ o ≈ ε
  lemma-order-w^k w o k eq = begin
    (w ^ k) ^ o  ≈⟨ ^^' w k o ⟩
    (w ^ o) ^ k  ≈⟨ ^-cong (w ^ o) ε k eq ⟩
    ε ^ k        ≈⟨ ε^k=ε k ⟩
    ε ∎
    where open SR word-setoid

  lemma-order-Z : Z ^ p ≈ ε
  lemma-order-Z = begin
    Z ^ p
      ≈⟨ lemma-Z^k-ℕ p ⟩
    H • H • S ^ p • H • H • S⁻¹ ^ p
      ≈⟨ cright cright cong (axiom order-S)
                            (cright cright lemma-order-w^k S p p-1 (axiom order-S)) ⟩
    H • H • ε • H • H • ε
      ≈⟨ by-assoc auto ⟩
    H • H • H • H
      ≈⟨ lemma-order-H ⟩
    ε ∎
    where open SR word-setoid

  lemma-order-X : X ^ p ≈ ε
  lemma-order-X = begin
    X ^ p
      ≈⟨ lemma-X^k-ℕ p ⟩
    H • S ^ p • H • H • S⁻¹ ^ p • H
      ≈⟨ cright cong (axiom order-S)
                     (cright cright cleft lemma-order-w^k S p p-1 (axiom order-S)) ⟩
    H • ε • H • H • ε • H
      ≈⟨ by-assoc auto ⟩
    H • H • H • H
      ≈⟨ lemma-order-H ⟩
    ε ∎
    where open SR word-setoid

  lemma-comm-Z-S : Z • S ≈ S • Z
  lemma-comm-Z-S = begin
    (H • H • S • H • H • S⁻¹) • S
      ≈⟨ by-passoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2) auto ⟩
    (H • H • S • H • H) • S⁻¹ • S
      ≈⟨ cright comm⇒pow-comm p-1 1 refl ⟩
    (H • H • S • H • H) • S • S⁻¹
      ≈⟨ sym (by-passoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2) auto) ⟩
    (H • H • S • H • H • S) • S⁻¹
      ≈⟨ cleft axiom comm-HHSHHS ⟩
    (S • H • H • S • H • H) • S⁻¹
      ≈⟨ by-passoc (□ ^ 6 • □) (□ • □ ^ 6) auto ⟩
    S • (H • H • S • H • H • S⁻¹) ∎
    where
    open SR word-setoid
    open Pattern-Assoc

  lemma-order-R : R ^ p ≈ ε
  lemma-order-R = begin
    (S • Z^ 1/2) ^ p
      ≈⟨ ^-cong (S • Z^ 1/2) (Z^ 1/2 • S) p
                (comm⇒pow-comm 1 (toℕ 1/2) (sym lemma-comm-Z-S)) ⟩
    (Z^ 1/2 • S) ^ p
      ≈⟨ ^-• (Z^ 1/2) S p (comm⇒pow-comm (toℕ 1/2) 1 lemma-comm-Z-S) ⟩
    Z^ 1/2 ^ p • S ^ p
      ≈⟨ cright axiom order-S ⟩
    Z^ 1/2 ^ p • ε
      ≈⟨ right-unit ⟩
    Z^ 1/2 ^ p
      ≈⟨ lemma-order-w^k Z p (toℕ 1/2) lemma-order-Z ⟩
    ε ∎
    where open SR word-setoid

  ------------------------------------------------------------------------
  -- Pauli conjugation by H
  --
  -- Z and X are derived words in H and S (see Syntactics):
  --
  --     Z = H • H • S • H • H • S ⁻¹        X = H • S • H • H • S ⁻¹ • H
  --
  -- chosen so that H • X and Z • H are literally the same letter
  -- sequence.  The conjugation is therefore pure associativity, and the
  -- power version follows by induction on the exponent.
  --
  -- Groundwork for c10: moving a Pauli across XC = H ↑ ^ 3 • CZ • H ↑
  -- means moving it across the two H ↑, which is this, and across CZ,
  -- which is rel-X↑-CZ.

  conj-H-X : H • X ≈ Z • H
  conj-H-X = by-assoc auto

  conj-H-X^k : ∀ k → H • X ^ k ≈ Z ^ k • H
  conj-H-X^k ₀ = trans right-unit (sym left-unit)
  conj-H-X^k ₁ = conj-H-X
  conj-H-X^k (₂₊ k) = begin
    H • (X • X ^ ₁₊ k)  ≈⟨ sym assoc ⟩
    (H • X) • X ^ ₁₊ k  ≈⟨ cleft conj-H-X ⟩
    (Z • H) • X ^ ₁₊ k  ≈⟨ assoc ⟩
    Z • (H • X ^ ₁₊ k)  ≈⟨ cright conj-H-X^k (₁₊ k) ⟩
    Z • (Z ^ ₁₊ k • H)  ≈⟨ sym assoc ⟩
    (Z • Z ^ ₁₊ k) • H ∎
    where open SR word-setoid

  ------------------------------------------------------------------------
  -- The multiplier by -1, spelled out in R and H
  --
  -- M is *defined* as R ^ x • H • R ^ x⁻¹ • H • R ^ x • H, so M₋₁ unfolds
  -- definitionally once both exponents are identified with p-1: the first
  -- by lemma-toℕ-1ₚ, the second because -1 is its own inverse, which is
  -- aux-₁⁻¹ in ForStdlib.  order-H then says the whole word is H ^ 2.
  --
  -- This is the Euler decomposition c10 turns on: cancelling the trailing
  -- H gives R ⁻¹ H R ⁻¹ H R ⁻¹ ≈ H, and hence R ⁻¹ H R ⁻¹ ≈ H R H ⁻¹,
  -- which is what rewrites c10's right-hand side.

  lemma-M₋₁-R : R ^ p-1 • (H • (R ^ p-1 • (H • (R ^ p-1 • H)))) ≈ H ^ 2
  lemma-M₋₁-R = begin
    R ^ p-1 • (H • (R ^ p-1 • (H • (R ^ p-1 • H))))
      ≡⟨ Eq.sym (Eq.cong₂ (λ a b → R ^ a • (H • (R ^ b • (H • (R ^ a • H)))))
                          lemma-toℕ-1ₚ
                          (Eq.trans (Eq.cong toℕ aux-₁⁻¹) lemma-toℕ-1ₚ)) ⟩
    M₋₁
      ≈⟨ sym (axiom order-H) ⟩
    H ^ 2 ∎
    where open SR word-setoid

------------------------------------------------------------------------
-- Group-likeness
--
-- Every generator has a left inverse, from the three order axioms.  The
-- same construction as Simplified-V1.Lemmas.Clifford-GroupLike, and for
-- the same reason: the axioms it uses are shared.  Iso.agda gets its
-- witness by transporting V1's along g-well-defined, which is fine there
-- but unusable here — the chains below need right-cancellation, and
-- deriving it from the transported witness would be circular.

module Paper-GroupLike where

  grouplike : Grouplike (n QRel,_===_)
  grouplike {₁₊ n} H-gen = H ^ 3 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : H ^ 3 • H ≈ ε
    claim = begin
      H ^ 3 • H ≈⟨ by-assoc auto ⟩
      H ^ 4     ≈⟨ One-Wire.lemma-order-H n ⟩
      ε ∎
  grouplike {₁₊ n} S-gen = S ^ p-1 , claim
    where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid
    claim : S ^ p-1 • S ≈ ε
    claim = begin
      S ^ p-1 • S       ≈⟨ sym (^-+ S p-1 1) ⟩
      S ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (S ^_) (NP.+-comm p-1 1) ⟩
      S ^ p             ≈⟨ axiom order-S ⟩
      ε ∎
  grouplike {₂₊ n} CZ-gen = CZ ^ p-1 , claim
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    claim : CZ ^ p-1 • CZ ≈ ε
    claim = begin
      CZ ^ p-1 • CZ       ≈⟨ sym (^-+ CZ p-1 1) ⟩
      CZ ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (CZ ^_) (NP.+-comm p-1 1) ⟩
      CZ ^ p              ≈⟨ axiom order-CZ ⟩
      ε ∎
  -- Width ₁₊ n rather than ₂₊ n: gate₀ makes Gen 0 inhabited, so a shift
  -- can appear on one wire too.  The witness is width-generic.
  grouplike {₁₊ n} (g ↥) with grouplike g
  ... | ig , prf = (ig ↑) , lemma-cong↑ (ig • [ g ]ʷ) ε prf

------------------------------------------------------------------------
-- Powers of a word of order p depend only on the exponent mod p
--
-- Stated at an arbitrary width, since the multiplier rescalings produce
-- natural-number exponents at both two and three wires.

lemma-pow-mod : ∀ {n} {w : Word (Gen n)} →
                let open PB (n QRel,_===_) using (_≈_) in
                w ^ p ≈ ε → ∀ m → w ^ m ≈ w ^ (m Nat.% p)
lemma-pow-mod {n} {w} op m = begin
  w ^ m
    ≡⟨ Eq.cong (w ^_) (m≡m%n+[m/n]*n m p) ⟩
  w ^ (m Nat.% p Nat.+ (m Nat./ p) Nat.* p)
    ≈⟨ ^-+ w (m Nat.% p) ((m Nat./ p) Nat.* p) ⟩
  w ^ (m Nat.% p) • w ^ ((m Nat./ p) Nat.* p)
    ≈⟨ cright aux ⟩
  w ^ (m Nat.% p) • ε
    ≈⟨ right-unit ⟩
  w ^ (m Nat.% p) ∎
  where
  open PB (n QRel,_===_)
  open PP (n QRel,_===_)
  open SR word-setoid
  aux : w ^ ((m Nat./ p) Nat.* p) ≈ ε
  aux = begin
    w ^ ((m Nat./ p) Nat.* p)  ≈⟨ refl' (Eq.cong (w ^_) (NP.*-comm (m Nat./ p) p)) ⟩
    w ^ (p Nat.* (m Nat./ p))  ≈⟨ sym (^^ w p (m Nat./ p)) ⟩
    (w ^ p) ^ (m Nat./ p)      ≈⟨ ^-cong (w ^ p) ε (m Nat./ p) op ⟩
    ε ^ (m Nat./ p)            ≈⟨ ε^k=ε (m Nat./ p) ⟩
    ε ∎

------------------------------------------------------------------------
-- Pauli conjugation by H ^ 2, and the second direction of conj-H
--
-- These need right cancellation and the basis-change tactic, so they
-- cannot live in One-Wire: Paper-GroupLike is declared after it, so no
-- Group-Lemmas instance is in scope there.  Ported verbatim from
-- Simplified-V1.LemmasXZ, on the same grounds as the One-Wire ports —
-- the one-wire axioms are shared, so the proof terms transfer unchanged.
--
-- conj-H-Z is the direction conj-H-X does not give.  Together they say
-- how a Pauli crosses either H in XC = H ↑ ^ 3 • CZ • H ↑, which with
-- lemma-CZ-X↑ᵏ for the middle CZ is the whole Pauli-vs-XC rule.

module One-Wire-Group (n : ℕ) where

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
  open Pattern-Assoc
  open One-Wire n
  open Group-Lemmas ((₁₊ n) QRel,_===_) (Paper-GroupLike.grouplike {₁₊ n})
    using (•-cancelʳ ; •-cancelˡ)
  open Basis-Change _ ((₁₊ n) QRel,_===_) (Paper-GroupLike.grouplike {₁₊ n})

  aux-S⁻¹⁻¹ : S⁻¹ ^ p-1 ≈ S
  aux-S⁻¹⁻¹ = •-cancelʳ {h = S⁻¹} aux00
    where
    aux00 : S⁻¹ ^ p-1 • S⁻¹ ≈ S • S⁻¹
    aux00 = begin
      S⁻¹ ^ p-1 • S⁻¹    ≈⟨ comm⇒pow-comm p-1 1 refl ⟩
      S⁻¹ • S⁻¹ ^ p-1    ≈⟨ refl ⟩
      S⁻¹ ^ p            ≈⟨ ^^ S p-1 p ⟩
      S ^ (p-1 Nat.* p)  ≡⟨ Eq.cong (S ^_) (NP.*-comm p-1 p) ⟩
      S ^ (p Nat.* p-1)  ≈⟨ sym (^^ S p p-1) ⟩
      (S ^ p) ^ p-1      ≈⟨ ^-cong (S ^ p) ε p-1 (axiom order-S) ⟩
      ε ^ p-1            ≈⟨ ε^k=ε (₁₊ p-2) ⟩
      ε                  ≈⟨ sym (axiom order-S) ⟩
      S • S⁻¹ ∎

  lemma-HH-Z : HH • Z ≈ Z^ (- ₁) • HH
  lemma-HH-Z = begin
    HH • H • H • S • H • H • S⁻¹
      ≈⟨ by-passoc (□ ^ 2 • □ ^ 6) (□ • □ • □ ^ 5 • □) auto ⟩
    H • H • (H • H • S • H • H) • S⁻¹
      ≈⟨ cright cright sym (comm⇒pow-comm p-1 1 (lemma-comm-SHHS^kHH 1)) ⟩
    H • H • S⁻¹ • (H • H • S • H • H)
      ≈⟨ by-passoc (□ ^ 8) (□ ^ 6 • □ ^ 2) auto ⟩
    (H • H • S⁻¹ • H • H • S) • H • H
      ≈⟨ cleft (cright cright cong (refl' (Eq.cong (S ^_) (Eq.sym lemma-toℕ-1ₚ)))
                                   (cright cright sym aux-S⁻¹⁻¹)) ⟩
    (H • H • S ^ (toℕ (- 1ₚ)) • H • H • S⁻¹ ^ p-1) • HH
      ≈⟨ cleft cright cright cright cright cright
           refl' (Eq.cong (S⁻¹ ^_) (Eq.sym lemma-toℕ-1ₚ)) ⟩
    (H • H • S ^ (toℕ (- 1ₚ)) • H • H • S⁻¹ ^ (toℕ (- 1ₚ))) • HH
      ≈⟨ cleft sym (lemma-Z^k-ℕ (toℕ (- 1ₚ))) ⟩
    Z^ (- ₁) • HH ∎

  lemma-HH-X : HH • X ≈ X^ (- ₁) • HH
  lemma-HH-X = bbc H ε claim
    where
    claim : H • (HH • X) • ε ≈ H • (X^ (- ₁) • HH) • ε
    claim = begin
      H • (HH • X) • ε     ≈⟨ cong refl right-unit ⟩
      H • (HH • X)         ≈⟨ by-passoc (□ • □ ^ 2 • □) (□ ^ 2 • □ ^ 2) auto ⟩
      HH • H • X           ≈⟨ cright conj-H-X ⟩
      HH • Z • H           ≈⟨ sym assoc ⟩
      (HH • Z) • H         ≈⟨ cleft lemma-HH-Z ⟩
      (Z^ (- ₁) • HH) • H  ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 2 • □ ^ 2) auto ⟩
      (Z^ (- ₁) • H) • HH  ≈⟨ cleft sym (conj-H-X^k (toℕ (- ₁))) ⟩
      (H • X^ (- ₁)) • HH  ≈⟨ assoc ⟩
      H • (X^ (- ₁) • HH)  ≈⟨ sym (cong refl right-unit) ⟩
      H • (X^ (- ₁) • HH) • ε ∎

  conj-H-Z : H • Z ≈ X^ (- ₁) • H
  conj-H-Z = bbc (H ^ 3) H claim
    where
    claim : H ^ 3 • (H • Z) • H ≈ H ^ 3 • (X^ (- ₁) • H) • H
    claim = begin
      H ^ 3 • (H • Z) • H  ≈⟨ by-assoc auto ⟩
      (H ^ 4) • Z • H      ≈⟨ trans (cleft lemma-order-H) left-unit ⟩
      Z • H                ≈⟨ sym conj-H-X ⟩
      H • X                ≈⟨ cleft (sym (trans (cright lemma-order-H) right-unit)) ⟩
      H ^ 5 • X            ≈⟨ by-passoc (□ ^ 5 • □) (□ ^ 3 • □ ^ 2 • □) auto ⟩
      H ^ 3 • HH • X       ≈⟨ cright lemma-HH-X ⟩
      H ^ 3 • X^ (- ₁) • H • H
        ≈⟨ by-passoc (□ ^ 4) (□ • □ ^ 2 • □) auto ⟩
      H ^ 3 • (X^ (- ₁) • H) • H ∎

  ------------------------------------------------------------------------
  -- The two conjugations by H that the Pauli-versus-XC rule crosses on
  --
  -- XC is H ↑ ^ 3 • CZ • H ↑, so a Z on the target wire meets first an
  -- H ↑ ^ 3 and then, past the CZ, another one.  Both crossings are
  -- read off conj-H-X — no inverse Pauli appears, which is what keeps
  -- the exponent bookkeeping in ℕ:
  --
  --     Z ≈ H • X • H ^ 3        X • H ^ 3 ≈ H ^ 3 • Z.

  lemma-Z-conj : Z ≈ H • (X • H ^ 3)
  lemma-Z-conj = •-cancelʳ {h = H} (begin
    Z • H                  ≈⟨ sym conj-H-X ⟩
    H • X                  ≈⟨ cright sym right-unit ⟩
    H • (X • ε)            ≈⟨ cright cright sym lemma-order-H ⟩
    H • (X • H ^ 4)        ≈⟨ cright cright ^-+ H 3 1 ⟩
    H • (X • (H ^ 3 • H))  ≈⟨ cright sym assoc ⟩
    H • ((X • H ^ 3) • H)  ≈⟨ sym assoc ⟩
    (H • (X • H ^ 3)) • H ∎)

  lemma-X-H³ : X • H ^ 3 ≈ H ^ 3 • Z
  lemma-X-H³ = •-cancelˡ {g = H} (begin
    H • (X • H ^ 3)  ≈⟨ sym assoc ⟩
    (H • X) • H ^ 3  ≈⟨ cleft conj-H-X ⟩
    (Z • H) • H ^ 3  ≈⟨ assoc ⟩
    Z • H ^ 4        ≈⟨ cright lemma-order-H ⟩
    Z • ε            ≈⟨ right-unit ⟩
    Z                ≈⟨ sym left-unit ⟩
    ε • Z            ≈⟨ cleft sym lemma-order-H ⟩
    H ^ 4 • Z        ≈⟨ assoc ⟩
    H • (H ^ 3 • Z) ∎)

  conj-H-Z^k : ∀ k → H • Z ^ k ≈ (X^ (- ₁)) ^ k • H
  conj-H-Z^k ₀ = trans right-unit (sym left-unit)
  conj-H-Z^k ₁ = conj-H-Z
  conj-H-Z^k (₂₊ k) = begin
    H • (Z • Z ^ ₁₊ k)
      ≈⟨ sym assoc ⟩
    (H • Z) • Z ^ ₁₊ k
      ≈⟨ cleft conj-H-Z ⟩
    (X^ (- ₁) • H) • Z ^ ₁₊ k
      ≈⟨ assoc ⟩
    X^ (- ₁) • (H • Z ^ ₁₊ k)
      ≈⟨ cright conj-H-Z^k (₁₊ k) ⟩
    X^ (- ₁) • ((X^ (- ₁)) ^ ₁₊ k • H)
      ≈⟨ sym assoc ⟩
    (X^ (- ₁) • (X^ (- ₁)) ^ ₁₊ k) • H ∎

module Ex-Conjugation (n : ℕ) where

  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

  open Group-Lemmas ((₂₊ n) QRel,_===_) (Paper-GroupLike.grouplike {₂₊ n})
    using (•-cancelʳ ; •-cancelˡ)

  -- The relation one wire down, for the arguments of lemma-cong↑.
  private module PB₁ = PB ((₁₊ n) QRel,_===_)

  -- order-Ex with the power unfolded: Ex ^ 2 is Ex • (Ex ^ 1) is
  -- Ex • Ex definitionally, so this is the axiom itself.
  lemma-Ex-Ex : Ex • Ex ≈ ε
  lemma-Ex-Ex = axiom order-Ex

  -- Cancelling a trailing Ex • Ex.
  lemma-cancel-Ex : ∀ {w} → w • Ex • Ex ≈ w
  lemma-cancel-Ex {w} = begin
    w • Ex • Ex ≈⟨ cright lemma-Ex-Ex ⟩
    w • ε       ≈⟨ right-unit ⟩
    w ∎

  ------------------------------------------------------------------------
  -- The two axioms, and their opposites
  --
  -- Conjugating by an involution is symmetric: from Ex • H ↑ ≈ H • Ex we
  -- get Ex • H ≈ H ↑ • Ex by inserting Ex • Ex on the right, pushing the
  -- axiom through backwards, and cancelling the pair on the left.

  lemma-Ex-H↑ : Ex • H ↑ ≈ H • Ex
  lemma-Ex-H↑ = axiom semi-Ex-H↑

  lemma-Ex-S↑ : Ex • S ↑ ≈ S • Ex
  lemma-Ex-S↑ = axiom semi-Ex-S↑

  lemma-Ex-H : Ex • H ≈ H ↑ • Ex
  lemma-Ex-H = begin
    Ex • H                 ≈⟨ sym lemma-cancel-Ex ⟩
    (Ex • H) • Ex • Ex     ≈⟨ by-assoc auto ⟩
    Ex • (H • Ex) • Ex     ≈⟨ cright cleft sym lemma-Ex-H↑ ⟩
    Ex • (Ex • H ↑) • Ex   ≈⟨ by-assoc auto ⟩
    (Ex • Ex) • H ↑ • Ex   ≈⟨ cleft lemma-Ex-Ex ⟩
    ε • H ↑ • Ex           ≈⟨ left-unit ⟩
    H ↑ • Ex ∎

  lemma-Ex-S : Ex • S ≈ S ↑ • Ex
  lemma-Ex-S = begin
    Ex • S                 ≈⟨ sym lemma-cancel-Ex ⟩
    (Ex • S) • Ex • Ex     ≈⟨ by-assoc auto ⟩
    Ex • (S • Ex) • Ex     ≈⟨ cright cleft sym lemma-Ex-S↑ ⟩
    Ex • (Ex • S ↑) • Ex   ≈⟨ by-assoc auto ⟩
    (Ex • Ex) • S ↑ • Ex   ≈⟨ cleft lemma-Ex-Ex ⟩
    ε • S ↑ • Ex           ≈⟨ left-unit ⟩
    S ↑ • Ex ∎

  ------------------------------------------------------------------------
  -- Two-sided conjugation
  --
  -- The form the later derivations actually use: Ex • g • Ex is g with
  -- its wire flipped.

  lemma-conj-Ex-H↑ : Ex • H ↑ • Ex ≈ H
  lemma-conj-Ex-H↑ = begin
    Ex • H ↑ • Ex   ≈⟨ sym assoc ⟩
    (Ex • H ↑) • Ex ≈⟨ cleft lemma-Ex-H↑ ⟩
    (H • Ex) • Ex   ≈⟨ assoc ⟩
    H • Ex • Ex     ≈⟨ lemma-cancel-Ex ⟩
    H ∎

  lemma-conj-Ex-S↑ : Ex • S ↑ • Ex ≈ S
  lemma-conj-Ex-S↑ = begin
    Ex • S ↑ • Ex   ≈⟨ sym assoc ⟩
    (Ex • S ↑) • Ex ≈⟨ cleft lemma-Ex-S↑ ⟩
    (S • Ex) • Ex   ≈⟨ assoc ⟩
    S • Ex • Ex     ≈⟨ lemma-cancel-Ex ⟩
    S ∎

  lemma-conj-Ex-H : Ex • H • Ex ≈ H ↑
  lemma-conj-Ex-H = begin
    Ex • H • Ex     ≈⟨ sym assoc ⟩
    (Ex • H) • Ex   ≈⟨ cleft lemma-Ex-H ⟩
    (H ↑ • Ex) • Ex ≈⟨ assoc ⟩
    H ↑ • Ex • Ex   ≈⟨ lemma-cancel-Ex ⟩
    H ↑ ∎

  lemma-conj-Ex-S : Ex • S • Ex ≈ S ↑
  lemma-conj-Ex-S = begin
    Ex • S • Ex     ≈⟨ sym assoc ⟩
    (Ex • S) • Ex   ≈⟨ cleft lemma-Ex-S ⟩
    (S ↑ • Ex) • Ex ≈⟨ assoc ⟩
    S ↑ • Ex • Ex   ≈⟨ lemma-cancel-Ex ⟩
    S ↑ ∎

  ------------------------------------------------------------------------
  -- Powers
  --
  -- Conjugation is a homomorphism, so it passes through a power one
  -- factor at a time.

  lemma-Ex-Hᵏ : ∀ k → Ex • H ^ k ≈ (H ↑) ^ k • Ex
  lemma-Ex-Hᵏ ₀ = trans right-unit (sym left-unit)
  lemma-Ex-Hᵏ ₁ = lemma-Ex-H
  lemma-Ex-Hᵏ (₂₊ k) = begin
    Ex • H ^ ₂₊ k            ≈⟨ sym assoc ⟩
    (Ex • H) • H ^ ₁₊ k      ≈⟨ cleft lemma-Ex-H ⟩
    (H ↑ • Ex) • H ^ ₁₊ k    ≈⟨ assoc ⟩
    H ↑ • Ex • H ^ ₁₊ k      ≈⟨ cright lemma-Ex-Hᵏ (₁₊ k) ⟩
    H ↑ • (H ↑) ^ ₁₊ k • Ex  ≈⟨ sym assoc ⟩
    (H ↑) ^ ₂₊ k • Ex ∎

  lemma-Ex-Sᵏ : ∀ k → Ex • S ^ k ≈ (S ↑) ^ k • Ex
  lemma-Ex-Sᵏ ₀ = trans right-unit (sym left-unit)
  lemma-Ex-Sᵏ ₁ = lemma-Ex-S
  lemma-Ex-Sᵏ (₂₊ k) = begin
    Ex • S ^ ₂₊ k            ≈⟨ sym assoc ⟩
    (Ex • S) • S ^ ₁₊ k      ≈⟨ cleft lemma-Ex-S ⟩
    (S ↑ • Ex) • S ^ ₁₊ k    ≈⟨ assoc ⟩
    S ↑ • Ex • S ^ ₁₊ k      ≈⟨ cright lemma-Ex-Sᵏ (₁₊ k) ⟩
    S ↑ • (S ↑) ^ ₁₊ k • Ex  ≈⟨ sym assoc ⟩
    (S ↑) ^ ₂₊ k • Ex ∎

  lemma-Ex-Hᵏ↑ : ∀ k → Ex • (H ↑) ^ k ≈ H ^ k • Ex
  lemma-Ex-Hᵏ↑ ₀ = trans right-unit (sym left-unit)
  lemma-Ex-Hᵏ↑ ₁ = lemma-Ex-H↑
  lemma-Ex-Hᵏ↑ (₂₊ k) = begin
    Ex • (H ↑) ^ ₂₊ k          ≈⟨ sym assoc ⟩
    (Ex • H ↑) • (H ↑) ^ ₁₊ k  ≈⟨ cleft lemma-Ex-H↑ ⟩
    (H • Ex) • (H ↑) ^ ₁₊ k    ≈⟨ assoc ⟩
    H • Ex • (H ↑) ^ ₁₊ k      ≈⟨ cright lemma-Ex-Hᵏ↑ (₁₊ k) ⟩
    H • H ^ ₁₊ k • Ex          ≈⟨ sym assoc ⟩
    H ^ ₂₊ k • Ex ∎

  lemma-Ex-Sᵏ↑ : ∀ k → Ex • (S ↑) ^ k ≈ S ^ k • Ex
  lemma-Ex-Sᵏ↑ ₀ = trans right-unit (sym left-unit)
  lemma-Ex-Sᵏ↑ ₁ = lemma-Ex-S↑
  lemma-Ex-Sᵏ↑ (₂₊ k) = begin
    Ex • (S ↑) ^ ₂₊ k          ≈⟨ sym assoc ⟩
    (Ex • S ↑) • (S ↑) ^ ₁₊ k  ≈⟨ cleft lemma-Ex-S↑ ⟩
    (S • Ex) • (S ↑) ^ ₁₊ k    ≈⟨ assoc ⟩
    S • Ex • (S ↑) ^ ₁₊ k      ≈⟨ cright lemma-Ex-Sᵏ↑ (₁₊ k) ⟩
    S • S ^ ₁₊ k • Ex          ≈⟨ sym assoc ⟩
    S ^ ₂₊ k • Ex ∎

  ------------------------------------------------------------------------
  -- Conjugation is a monoid homomorphism
  --
  -- Stated as "Ex • u ≈ u' • Ex", the form the chains below compose in.
  -- These two are what lift the gate-level axioms to the derived words Z,
  -- R, M and Mg, which are just products and powers of S and H.

  lemma-Ex-• : ∀ {u u' v v'} → Ex • u ≈ u' • Ex → Ex • v ≈ v' • Ex →
               Ex • (u • v) ≈ (u' • v') • Ex
  lemma-Ex-• {u} {u'} {v} {v'} eu ev = begin
    Ex • (u • v)   ≈⟨ sym assoc ⟩
    (Ex • u) • v   ≈⟨ cleft eu ⟩
    (u' • Ex) • v  ≈⟨ assoc ⟩
    u' • Ex • v    ≈⟨ cright ev ⟩
    u' • v' • Ex   ≈⟨ sym assoc ⟩
    (u' • v') • Ex ∎

  lemma-Ex-pow : ∀ {u u'} → Ex • u ≈ u' • Ex → ∀ k → Ex • u ^ k ≈ u' ^ k • Ex
  lemma-Ex-pow e ₀      = trans right-unit (sym left-unit)
  lemma-Ex-pow e ₁      = e
  lemma-Ex-pow e (₂₊ k) = lemma-Ex-• e (lemma-Ex-pow e (₁₊ k))

  ------------------------------------------------------------------------
  -- CZ is symmetric in its two wires, so the swap leaves it alone
  --
  -- This is Lemma 2 of ProgressReport14, which shows the swap-vs-CZ
  -- commutation (its C12) is derivable and need not be an axiom.  The
  -- argument turns on the two ways of writing the swap.  Write A = H • H↑
  -- for the Hadamard on both wires.  A commutes with Ex, because Ex
  -- carries each Hadamard to the other wire (Lemma 1 = lemma-Ex-H, itself
  -- just semi-Ex-H↑ conjugated) and the two Hadamards commute with each
  -- other; cancelling one A then rewrites
  --
  --     Ex = CZ • A • CZ • A • CZ • A      (the definition here)
  --     Ex = A • CZ • A • CZ • A • CZ      (the report's D4)
  --
  -- and with both in hand the commutation is pure associativity: the CZ
  -- at the right end of the first form is the CZ at the left end of the
  -- second.

  lemma-Ex-A : Ex • (H • H ↑) ≈ (H • H ↑) • Ex
  lemma-Ex-A = begin
    Ex • (H • H ↑)  ≈⟨ sym assoc ⟩
    (Ex • H) • H ↑  ≈⟨ cleft lemma-Ex-H ⟩
    (H ↑ • Ex) • H ↑ ≈⟨ assoc ⟩
    H ↑ • (Ex • H ↑) ≈⟨ cright lemma-Ex-H↑ ⟩
    H ↑ • (H • Ex)  ≈⟨ sym assoc ⟩
    (H ↑ • H) • Ex  ≈⟨ cleft axiom comm-H ⟩
    (H • H ↑) • Ex ∎

  -- The report's D4: the same swap with the Hadamards leading.
  lemma-D4 : Ex ≈ (H • H ↑) • CZ • ((H • H ↑) • CZ • ((H • H ↑) • CZ))
  lemma-D4 = •-cancelʳ {h = H • H ↑} (begin
    Ex • (H • H ↑)
      ≈⟨ lemma-Ex-A ⟩
    (H • H ↑) • Ex
      ≈⟨ by-assoc auto ⟩
    ((H • H ↑) • CZ • ((H • H ↑) • CZ • ((H • H ↑) • CZ))) • (H • H ↑) ∎)

  lemma-Ex-CZ : Ex • CZ ≈ CZ • Ex
  lemma-Ex-CZ = begin
    Ex • CZ
      ≈⟨ by-assoc auto ⟩
    CZ • ((H • H ↑) • CZ • ((H • H ↑) • CZ • ((H • H ↑) • CZ)))
      ≈⟨ cright sym lemma-D4 ⟩
    CZ • Ex ∎

  lemma-Ex-CZᵏ : ∀ k → Ex • CZ ^ k ≈ CZ ^ k • Ex
  lemma-Ex-CZᵏ = lemma-Ex-pow lemma-Ex-CZ

  lemma-conj-Ex-CZ : Ex • CZ • Ex ≈ CZ
  lemma-conj-Ex-CZ = begin
    Ex • CZ • Ex    ≈⟨ sym assoc ⟩
    (Ex • CZ) • Ex  ≈⟨ cleft lemma-Ex-CZ ⟩
    (CZ • Ex) • Ex  ≈⟨ assoc ⟩
    CZ • Ex • Ex    ≈⟨ lemma-cancel-Ex ⟩
    CZ ∎

  ------------------------------------------------------------------------
  -- The derived one-wire words, carried from the upper wire to the lower
  --
  -- Each is a product of powers of S and H, so it is assembled from the
  -- two axioms by lemma-Ex-• and lemma-Ex-pow.  The `refl'` steps are
  -- the shift commuting with a power — definitional for a literal
  -- exponent, but p-1 and toℕ k are symbolic, so lemma-↑^ is needed.

  lemma-Ex-S⁻¹↑ : Ex • S⁻¹ ↑ ≈ S⁻¹ • Ex
  lemma-Ex-S⁻¹↑ = begin
    Ex • S⁻¹ ↑          ≈⟨ refl' (Eq.cong (Ex •_) (lemma-↑^ p-1 S)) ⟩
    Ex • (S ↑) ^ p-1    ≈⟨ lemma-Ex-Sᵏ↑ p-1 ⟩
    S⁻¹ • Ex ∎

  lemma-Ex-Z↑ : Ex • Z ↑ ≈ Z • Ex
  lemma-Ex-Z↑ =
    lemma-Ex-• lemma-Ex-H↑
      (lemma-Ex-• lemma-Ex-H↑
        (lemma-Ex-• lemma-Ex-S↑
          (lemma-Ex-• lemma-Ex-H↑
            (lemma-Ex-• lemma-Ex-H↑ lemma-Ex-S⁻¹↑))))

  lemma-Ex-Z^↑ : ∀ k → Ex • (Z^ k) ↑ ≈ Z^ k • Ex
  lemma-Ex-Z^↑ k = begin
    Ex • (Z ^ toℕ k) ↑       ≈⟨ refl' (Eq.cong (Ex •_) (lemma-↑^ (toℕ k) Z)) ⟩
    Ex • (Z ↑) ^ toℕ k       ≈⟨ lemma-Ex-pow lemma-Ex-Z↑ (toℕ k) ⟩
    Z ^ toℕ k • Ex ∎

  lemma-Ex-R↑ : Ex • R ↑ ≈ R • Ex
  lemma-Ex-R↑ = lemma-Ex-• lemma-Ex-S↑ (lemma-Ex-Z^↑ 1/2)

  lemma-Ex-R^↑ : ∀ k → Ex • (R^ k) ↑ ≈ R^ k • Ex
  lemma-Ex-R^↑ k = begin
    Ex • (R ^ toℕ k) ↑       ≈⟨ refl' (Eq.cong (Ex •_) (lemma-↑^ (toℕ k) R)) ⟩
    Ex • (R ↑) ^ toℕ k       ≈⟨ lemma-Ex-pow lemma-Ex-R↑ (toℕ k) ⟩
    R ^ toℕ k • Ex ∎

  lemma-Ex-M↑ : ∀ (x' : ℤ* ₚ) → Ex • M x' ↑ ≈ M x' • Ex
  lemma-Ex-M↑ x' =
    lemma-Ex-• (lemma-Ex-R^↑ x)
      (lemma-Ex-• lemma-Ex-H↑
        (lemma-Ex-• (lemma-Ex-R^↑ x⁻¹)
          (lemma-Ex-• lemma-Ex-H↑
            (lemma-Ex-• (lemma-Ex-R^↑ x) lemma-Ex-H↑))))
    where
    x   = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁)

  lemma-Ex-Mg↑ : Ex • Mg ↑ ≈ Mg • Ex
  lemma-Ex-Mg↑ = lemma-Ex-M↑ g′

  -- …and the same three, in the other direction: a lower-wire word goes
  -- up.  c11 is c10 conjugated by the swap, and these are the factors of
  -- c10 that travel that way.

  lemma-Ex-S⁻¹ : Ex • S⁻¹ ≈ S⁻¹ ↑ • Ex
  lemma-Ex-S⁻¹ = begin
    Ex • S ^ p-1      ≈⟨ lemma-Ex-Sᵏ p-1 ⟩
    (S ↑) ^ p-1 • Ex  ≈⟨ refl' (Eq.cong (_• Ex) (Eq.sym (lemma-↑^ p-1 S))) ⟩
    S⁻¹ ↑ • Ex ∎

  lemma-Ex-Z : Ex • Z ≈ Z ↑ • Ex
  lemma-Ex-Z =
    lemma-Ex-• lemma-Ex-H
      (lemma-Ex-• lemma-Ex-H
        (lemma-Ex-• lemma-Ex-S
          (lemma-Ex-• lemma-Ex-H
            (lemma-Ex-• lemma-Ex-H lemma-Ex-S⁻¹))))

  lemma-Ex-Z^ : ∀ k → Ex • Z^ k ≈ (Z^ k) ↑ • Ex
  lemma-Ex-Z^ k = begin
    Ex • Z ^ toℕ k      ≈⟨ lemma-Ex-pow lemma-Ex-Z (toℕ k) ⟩
    (Z ↑) ^ toℕ k • Ex  ≈⟨ refl' (Eq.cong (_• Ex) (Eq.sym (lemma-↑^ (toℕ k) Z))) ⟩
    (Z ^ toℕ k) ↑ • Ex ∎

  lemma-Ex-R : Ex • R ≈ R ↑ • Ex
  lemma-Ex-R = lemma-Ex-• lemma-Ex-S (lemma-Ex-Z^ 1/2)

  ------------------------------------------------------------------------
  -- The controlled-X and its mirror
  --
  -- CX = H ↓ ^ 3 • CZ • H ↓ conjugates CZ by an H on wire 0, so its
  -- target is wire 0 and its control wire 1; XC = H ↑ ^ 3 • CZ • H ↑ is
  -- the same with the wires exchanged.  Conjugating by the swap therefore
  -- exchanges the two, and since CZ is symmetric the proof is just the
  -- homomorphism applied to the three factors.

  lemma-Ex-CX : Ex • CX ≈ XC • Ex
  lemma-Ex-CX = lemma-Ex-• (lemma-Ex-Hᵏ 3) (lemma-Ex-• lemma-Ex-CZ lemma-Ex-H)

  lemma-Ex-XC : Ex • XC ≈ CX • Ex
  lemma-Ex-XC = lemma-Ex-• (lemma-Ex-Hᵏ↑ 3) (lemma-Ex-• lemma-Ex-CZ lemma-Ex-H↑)

  lemma-conj-Ex-CX : Ex • CX • Ex ≈ XC
  lemma-conj-Ex-CX = begin
    Ex • CX • Ex    ≈⟨ sym assoc ⟩
    (Ex • CX) • Ex  ≈⟨ cleft lemma-Ex-CX ⟩
    (XC • Ex) • Ex  ≈⟨ assoc ⟩
    XC • Ex • Ex    ≈⟨ lemma-cancel-Ex ⟩
    XC ∎

  lemma-conj-Ex-XC : Ex • XC • Ex ≈ CX
  lemma-conj-Ex-XC = begin
    Ex • XC • Ex    ≈⟨ sym assoc ⟩
    (Ex • XC) • Ex  ≈⟨ cleft lemma-Ex-XC ⟩
    (CX • Ex) • Ex  ≈⟨ assoc ⟩
    CX • Ex • Ex    ≈⟨ lemma-cancel-Ex ⟩
    CX ∎

  -- …and on to powers, which is the form blake-c12 needs (it writes
  -- CX ^ p-1 for the inverse).
  lemma-Ex-CXᵏ : ∀ k → Ex • CX ^ k ≈ XC ^ k • Ex
  lemma-Ex-CXᵏ = lemma-Ex-pow lemma-Ex-CX

  lemma-Ex-XCᵏ : ∀ k → Ex • XC ^ k ≈ CX ^ k • Ex
  lemma-Ex-XCᵏ = lemma-Ex-pow lemma-Ex-XC

  ------------------------------------------------------------------------
  -- The half-swaps, and ⊤⊥ / ⊥⊤
  --
  -- ₕ|ₕ = H ↓ • CZ • H ↓ and ʰ|ʰ = H ↑ • CZ • H ↑ are the same word on
  -- the two wires, so the swap exchanges them; ⊥⊤ = ₕ|ₕ • ʰ|ʰ and
  -- ⊤⊥ = ʰ|ʰ • ₕ|ₕ are their two orders, so the swap exchanges those
  -- too.  Selinger's c13, c14 and c15 are all stated over ⊤⊥ / ⊥⊤, and
  -- c14 and c15 are mirror images of one another.

  lemma-Ex-ₕ|ₕ : Ex • ₕ|ₕ ≈ ʰ|ʰ • Ex
  lemma-Ex-ₕ|ₕ = lemma-Ex-• lemma-Ex-H (lemma-Ex-• lemma-Ex-CZ lemma-Ex-H)

  lemma-Ex-ʰ|ʰ : Ex • ʰ|ʰ ≈ ₕ|ₕ • Ex
  lemma-Ex-ʰ|ʰ = lemma-Ex-• lemma-Ex-H↑ (lemma-Ex-• lemma-Ex-CZ lemma-Ex-H↑)

  lemma-Ex-⊥⊤ : Ex • ⊥⊤ ≈ ⊤⊥ • Ex
  lemma-Ex-⊥⊤ = lemma-Ex-• lemma-Ex-ₕ|ₕ lemma-Ex-ʰ|ʰ

  lemma-Ex-⊤⊥ : Ex • ⊤⊥ ≈ ⊥⊤ • Ex
  lemma-Ex-⊤⊥ = lemma-Ex-• lemma-Ex-ʰ|ʰ lemma-Ex-ₕ|ₕ

  lemma-conj-Ex-⊥⊤ : Ex • ⊥⊤ • Ex ≈ ⊤⊥
  lemma-conj-Ex-⊥⊤ = begin
    Ex • ⊥⊤ • Ex    ≈⟨ sym assoc ⟩
    (Ex • ⊥⊤) • Ex  ≈⟨ cleft lemma-Ex-⊥⊤ ⟩
    (⊤⊥ • Ex) • Ex  ≈⟨ assoc ⟩
    ⊤⊥ • Ex • Ex    ≈⟨ lemma-cancel-Ex ⟩
    ⊤⊥ ∎

  lemma-conj-Ex-⊤⊥ : Ex • ⊤⊥ • Ex ≈ ⊥⊤
  lemma-conj-Ex-⊤⊥ = begin
    Ex • ⊤⊥ • Ex    ≈⟨ sym assoc ⟩
    (Ex • ⊤⊥) • Ex  ≈⟨ cleft lemma-Ex-⊤⊥ ⟩
    (⊥⊤ • Ex) • Ex  ≈⟨ assoc ⟩
    ⊥⊤ • Ex • Ex    ≈⟨ lemma-cancel-Ex ⟩
    ⊥⊤ ∎

  ------------------------------------------------------------------------
  -- Three half-swaps make the swap
  --
  --     ₕ|ₕ • ʰ|ʰ • ₕ|ₕ  ≈  H • Ex • (H ↑) ^ 3
  --
  -- the classical "SWAP is three CNOTs", in the form the two rule sets
  -- actually write.  Both sides are the same nine letters
  -- H CZ H H↑ CZ H H↑ CZ H once the H's are sorted: on the left the
  -- adjacent H↑ • H is flipped by the structural comm-H, and on the right
  -- Ex's trailing H↑ absorbs the (H ↑) ^ 3 into (H ↑) ^ 4 ≈ ε.
  --
  -- This is the dictionary c13, c14 and c15 need, since those are stated
  -- over ⊤⊥ / ⊥⊤ while Paper-V0's own three-wire axioms are stated over
  -- Ex.

  lemma-order-H↑ : (H ↑) ^ 4 ≈ ε
  lemma-order-H↑ = lemma-cong↑ _ _ (One-Wire.lemma-order-H n)

  lemma-half-swaps : ₕ|ₕ • ʰ|ʰ • ₕ|ₕ ≈ H • Ex • (H ↑) ^ 3
  lemma-half-swaps = begin
    ₕ|ₕ • ʰ|ʰ • ₕ|ₕ
      ≈⟨ by-assoc auto ⟩
    (H • CZ • H • H ↑ • CZ) • (H ↑ • H) • CZ • H
      ≈⟨ cright cleft axiom comm-H ⟩
    (H • CZ • H • H ↑ • CZ) • (H • H ↑) • CZ • H
      ≈⟨ sym right-unit ⟩
    ((H • CZ • H • H ↑ • CZ) • (H • H ↑) • CZ • H) • ε
      ≈⟨ cright sym lemma-order-H↑ ⟩
    ((H • CZ • H • H ↑ • CZ) • (H • H ↑) • CZ • H) • (H ↑) ^ 4
      ≈⟨ by-assoc auto ⟩
    H • Ex • (H ↑) ^ 3 ∎

  ------------------------------------------------------------------------
  -- A half-swap times a swap has order 3
  --
  -- Ex carries ₕ|ₕ to ʰ|ʰ, so ⊥⊤ = ₕ|ₕ • ʰ|ʰ is (ₕ|ₕ • Ex) squared, and
  -- ⊤⊥ is the same element conjugated.  Cubing that element is
  -- ⊥⊤ • ₕ|ₕ • Ex, which lemma-half-swaps rewrites to H • Ex • (H ↑)³ • Ex;
  -- the two swaps then cancel and H ⁴ is ε.
  --
  -- Both c14 and c15 assert that an element cubes to ε, and Paper-V0's
  -- axioms supply exactly two such elements: this one and the 3-cycle of
  -- lemma-σ³.

  lemma-ʰ|ʰ-conj : Ex • (ₕ|ₕ • Ex) ≈ ʰ|ʰ
  lemma-ʰ|ʰ-conj = begin
    Ex • (ₕ|ₕ • Ex)  ≈⟨ sym assoc ⟩
    (Ex • ₕ|ₕ) • Ex  ≈⟨ cleft lemma-Ex-ₕ|ₕ ⟩
    (ʰ|ʰ • Ex) • Ex  ≈⟨ assoc ⟩
    ʰ|ʰ • (Ex • Ex)  ≈⟨ cright lemma-Ex-Ex ⟩
    ʰ|ʰ • ε          ≈⟨ right-unit ⟩
    ʰ|ʰ ∎

  lemma-⊥⊤-square : ⊥⊤ ≈ (ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)
  lemma-⊥⊤-square = begin
    ₕ|ₕ • ʰ|ʰ                    ≈⟨ cright sym lemma-ʰ|ʰ-conj ⟩
    ₕ|ₕ • (Ex • (ₕ|ₕ • Ex))      ≈⟨ sym assoc ⟩
    (ₕ|ₕ • Ex) • (ₕ|ₕ • Ex) ∎

  lemma-half-swap-cube : ((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • (ₕ|ₕ • Ex) ≈ ε
  lemma-half-swap-cube = begin
    ((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • (ₕ|ₕ • Ex)
      ≈⟨ cleft sym lemma-⊥⊤-square ⟩
    ⊥⊤ • (ₕ|ₕ • Ex)
      ≈⟨ by-assoc auto ⟩
    (ₕ|ₕ • ʰ|ʰ • ₕ|ₕ) • Ex
      ≈⟨ cleft lemma-half-swaps ⟩
    (H • Ex • (H ↑) ^ 3) • Ex
      ≈⟨ by-assoc auto ⟩
    H • Ex • ((H ↑) ^ 3 • Ex)
      ≈⟨ cright cright sym (lemma-Ex-Hᵏ 3) ⟩
    H • Ex • (Ex • H ^ 3)
      ≈⟨ by-assoc auto ⟩
    H • (Ex • Ex) • H ^ 3
      ≈⟨ cright cleft lemma-Ex-Ex ⟩
    H • ε • H ^ 3
      ≈⟨ cright left-unit ⟩
    H • H ^ 3
      ≈⟨ by-assoc auto ⟩
    H ^ 4
      ≈⟨ One-Wire.lemma-order-H (₁₊ n) ⟩
    ε ∎

  -- The same on the other side.  ⊤⊥ is what c14 is stated over, and it is
  -- the square of Ex • ₕ|ₕ, which is the previous element conjugated by
  -- the swap — so its cube is ε for the same reason, with no second
  -- appeal to lemma-half-swaps.

  lemma-UUₕ|ₕ : ((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • ₕ|ₕ ≈ Ex
  lemma-UUₕ|ₕ = begin
    ((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • ₕ|ₕ
      ≈⟨ sym right-unit ⟩
    (((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • ₕ|ₕ) • ε
      ≈⟨ cright sym lemma-Ex-Ex ⟩
    (((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • ₕ|ₕ) • (Ex • Ex)
      ≈⟨ by-assoc auto ⟩
    (((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • (ₕ|ₕ • Ex)) • Ex
      ≈⟨ cleft lemma-half-swap-cube ⟩
    ε • Ex
      ≈⟨ left-unit ⟩
    Ex ∎

  lemma-⊤⊥-square : ⊤⊥ ≈ (Ex • ₕ|ₕ) • (Ex • ₕ|ₕ)
  lemma-⊤⊥-square = begin
    ʰ|ʰ • ₕ|ₕ                        ≈⟨ cleft sym lemma-ʰ|ʰ-conj ⟩
    (Ex • (ₕ|ₕ • Ex)) • ₕ|ₕ          ≈⟨ by-assoc auto ⟩
    (Ex • ₕ|ₕ) • (Ex • ₕ|ₕ) ∎

  lemma-⊤⊥-cube : ((Ex • ₕ|ₕ) • (Ex • ₕ|ₕ)) • (Ex • ₕ|ₕ) ≈ ε
  lemma-⊤⊥-cube = begin
    ((Ex • ₕ|ₕ) • (Ex • ₕ|ₕ)) • (Ex • ₕ|ₕ)
      ≈⟨ by-assoc auto ⟩
    Ex • (((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • ₕ|ₕ)
      ≈⟨ cright lemma-UUₕ|ₕ ⟩
    Ex • Ex
      ≈⟨ lemma-Ex-Ex ⟩
    ε ∎

  lemma-conj-Ex-Mg↑ : Ex • Mg ↑ • Ex ≈ Mg
  lemma-conj-Ex-Mg↑ = begin
    Ex • Mg ↑ • Ex   ≈⟨ sym assoc ⟩
    (Ex • Mg ↑) • Ex ≈⟨ cleft lemma-Ex-Mg↑ ⟩
    (Mg • Ex) • Ex   ≈⟨ assoc ⟩
    Mg • Ex • Ex     ≈⟨ lemma-cancel-Ex ⟩
    Mg ∎

  ------------------------------------------------------------------------
  -- The ↓-rules, obtained by conjugating the ↑-rules
  --
  -- This is what the new comm-Ex-CZ axiom buys.  Each proof is the same
  -- three moves: replace the lower-wire word by its Ex-conjugate, push
  -- the CZ through both copies of Ex, and apply the ↑-rule in the middle.

  lemma-comm-CZ-S : CZ • S ≈ S • CZ
  lemma-comm-CZ-S = begin
    CZ • S                ≈⟨ cright sym lemma-conj-Ex-S↑ ⟩
    CZ • (Ex • S ↑ • Ex)  ≈⟨ by-assoc auto ⟩
    (CZ • Ex) • S ↑ • Ex  ≈⟨ cleft sym lemma-Ex-CZ ⟩
    (Ex • CZ) • S ↑ • Ex  ≈⟨ by-assoc auto ⟩
    Ex • (CZ • S ↑) • Ex  ≈⟨ cright cleft axiom comm-CZ-S↑ ⟩
    Ex • (S ↑ • CZ) • Ex  ≈⟨ by-assoc auto ⟩
    (Ex • S ↑) • CZ • Ex  ≈⟨ cright sym lemma-Ex-CZ ⟩
    (Ex • S ↑) • Ex • CZ  ≈⟨ by-assoc auto ⟩
    (Ex • S ↑ • Ex) • CZ  ≈⟨ cleft lemma-conj-Ex-S↑ ⟩
    S • CZ ∎

  -- Every re-bracketing here is an explicit assoc rather than by-assoc:
  -- the tactic compares to-list, and to-list is stuck on CZ^ g = CZ ^ toℕ g,
  -- whose exponent is symbolic.
  lemma-semi-Mg-CZ : Mg • CZ ≈ CZ^ g • Mg
  lemma-semi-Mg-CZ = begin
    Mg • CZ                       ≈⟨ cleft sym lemma-conj-Ex-Mg↑ ⟩
    (Ex • (Mg ↑ • Ex)) • CZ       ≈⟨ assoc ⟩
    Ex • ((Mg ↑ • Ex) • CZ)       ≈⟨ cright assoc ⟩
    Ex • (Mg ↑ • (Ex • CZ))       ≈⟨ cright cright lemma-Ex-CZ ⟩
    Ex • (Mg ↑ • (CZ • Ex))       ≈⟨ cright sym assoc ⟩
    Ex • ((Mg ↑ • CZ) • Ex)       ≈⟨ cright cleft axiom semi-M↑CZ ⟩
    Ex • ((CZ^ g • Mg ↑) • Ex)    ≈⟨ cright assoc ⟩
    Ex • (CZ^ g • (Mg ↑ • Ex))    ≈⟨ sym assoc ⟩
    (Ex • CZ^ g) • (Mg ↑ • Ex)    ≈⟨ cleft lemma-Ex-CZᵏ (toℕ g) ⟩
    (CZ^ g • Ex) • (Mg ↑ • Ex)    ≈⟨ assoc ⟩
    CZ^ g • (Ex • (Mg ↑ • Ex))    ≈⟨ cright lemma-conj-Ex-Mg↑ ⟩
    CZ^ g • Mg ∎

  ------------------------------------------------------------------------
  -- Pushing the multiplier past a CZ power rescales the exponent
  --
  -- Iterating the rule over the power multiplies the exponent by g.  The
  -- product is taken in ℕ, so lemma-pow-mod brings it back into range and
  -- lemma-toℕ-% identifies it with the product in ℤ/pℤ.

  lemma-Mg-CZ^ : ∀ (a : ℤ ₚ) → Mg • CZ^ a ≈ CZ^ (g * a) • Mg
  lemma-Mg-CZ^ a = begin
    Mg • CZ ^ toℕ a
      ≈⟨ lemma-Induction lemma-semi-Mg-CZ (toℕ a) ⟩
    (CZ ^ toℕ g) ^ toℕ a • Mg
      ≈⟨ cleft (^^ CZ (toℕ g) (toℕ a)) ⟩
    CZ ^ (toℕ g Nat.* toℕ a) • Mg
      ≈⟨ cleft (lemma-pow-mod (axiom order-CZ) (toℕ g Nat.* toℕ a)) ⟩
    CZ ^ ((toℕ g Nat.* toℕ a) Nat.% p) • Mg
      ≈⟨ cleft refl' (Eq.cong (CZ ^_) (lemma-toℕ-% g a)) ⟩
    CZ ^ toℕ (g * a) • Mg ∎

  -- Mg ^ j rescales by g ^′ j.  The induction costs only associativity,
  -- since x ^′ (suc k) is x * (x ^′ k) definitionally; the ₀/₁/₂₊ split
  -- is forced by w ^ 1 being w rather than w • w ^ 0.
  lemma-Mgᵏ-CZ : ∀ j → Mg ^ j • CZ ≈ CZ ^ toℕ (g ^′ j) • Mg ^ j
  lemma-Mgᵏ-CZ ₀ = begin
    ε • CZ  ≈⟨ left-unit ⟩
    CZ      ≈⟨ sym right-unit ⟩
    CZ • ε ∎
  lemma-Mgᵏ-CZ ₁ = begin
    Mg • CZ                ≈⟨ lemma-semi-Mg-CZ ⟩
    CZ ^ toℕ g • Mg
      ≡⟨ Eq.cong (λ z → CZ ^ toℕ z • Mg) (Eq.sym (lemma-x^′1=x g)) ⟩
    CZ ^ toℕ (g ^′ 1) • Mg ∎
  lemma-Mgᵏ-CZ (₂₊ j) = begin
    (Mg • Mg ^ ₁₊ j) • CZ
      ≈⟨ assoc ⟩
    Mg • (Mg ^ ₁₊ j • CZ)
      ≈⟨ cright lemma-Mgᵏ-CZ (₁₊ j) ⟩
    Mg • (CZ ^ toℕ (g ^′ ₁₊ j) • Mg ^ ₁₊ j)
      ≈⟨ sym assoc ⟩
    (Mg • CZ ^ toℕ (g ^′ ₁₊ j)) • Mg ^ ₁₊ j
      ≈⟨ cleft lemma-Mg-CZ^ (g ^′ ₁₊ j) ⟩
    (CZ ^ toℕ (g * (g ^′ ₁₊ j)) • Mg) • Mg ^ ₁₊ j
      ≈⟨ assoc ⟩
    CZ ^ toℕ (g * (g ^′ ₁₊ j)) • (Mg • Mg ^ ₁₊ j) ∎

  ------------------------------------------------------------------------
  -- The same chain one wire up
  --
  -- semi-M↑CZ is an axiom, so the wire-1 multiplier needs no derivation
  -- for its base case; from there the induction is word-for-word the
  -- wire-0 one.  A multiplier on either wire of a CZ rescales it by the
  -- same factor, which is what makes c14's cancellation work.

  lemma-Mg↑-CZ^ : ∀ (a : ℤ ₚ) → Mg ↑ • CZ^ a ≈ CZ^ (g * a) • Mg ↑
  lemma-Mg↑-CZ^ a = begin
    Mg ↑ • CZ ^ toℕ a
      ≈⟨ lemma-Induction (axiom semi-M↑CZ) (toℕ a) ⟩
    (CZ ^ toℕ g) ^ toℕ a • Mg ↑
      ≈⟨ cleft (^^ CZ (toℕ g) (toℕ a)) ⟩
    CZ ^ (toℕ g Nat.* toℕ a) • Mg ↑
      ≈⟨ cleft (lemma-pow-mod (axiom order-CZ) (toℕ g Nat.* toℕ a)) ⟩
    CZ ^ ((toℕ g Nat.* toℕ a) Nat.% p) • Mg ↑
      ≈⟨ cleft refl' (Eq.cong (CZ ^_) (lemma-toℕ-% g a)) ⟩
    CZ ^ toℕ (g * a) • Mg ↑ ∎

  lemma-Mgᵏ↑-CZ : ∀ j → (Mg ↑) ^ j • CZ ≈ CZ ^ toℕ (g ^′ j) • (Mg ↑) ^ j
  lemma-Mgᵏ↑-CZ ₀ = begin
    ε • CZ  ≈⟨ left-unit ⟩
    CZ      ≈⟨ sym right-unit ⟩
    CZ • ε ∎
  lemma-Mgᵏ↑-CZ ₁ = begin
    Mg ↑ • CZ            ≈⟨ axiom semi-M↑CZ ⟩
    CZ ^ toℕ g • Mg ↑
      ≡⟨ Eq.cong (λ z → CZ ^ toℕ z • Mg ↑) (Eq.sym (lemma-x^′1=x g)) ⟩
    CZ ^ toℕ (g ^′ 1) • Mg ↑ ∎
  lemma-Mgᵏ↑-CZ (₂₊ j) = begin
    (Mg ↑ • (Mg ↑) ^ ₁₊ j) • CZ
      ≈⟨ assoc ⟩
    Mg ↑ • ((Mg ↑) ^ ₁₊ j • CZ)
      ≈⟨ cright lemma-Mgᵏ↑-CZ (₁₊ j) ⟩
    Mg ↑ • (CZ ^ toℕ (g ^′ ₁₊ j) • (Mg ↑) ^ ₁₊ j)
      ≈⟨ sym assoc ⟩
    (Mg ↑ • CZ ^ toℕ (g ^′ ₁₊ j)) • (Mg ↑) ^ ₁₊ j
      ≈⟨ cleft lemma-Mg↑-CZ^ (g ^′ ₁₊ j) ⟩
    (CZ ^ toℕ (g * (g ^′ ₁₊ j)) • Mg ↑) • (Mg ↑) ^ ₁₊ j
      ≈⟨ assoc ⟩
    CZ ^ toℕ (g * (g ^′ ₁₊ j)) • (Mg ↑ • (Mg ↑) ^ ₁₊ j) ∎

  ------------------------------------------------------------------------
  -- (moved below, after the multiplier lemmas it depends on)

  private
    -- The power of g that is -1, and M₋₁ as that power of Mg, taken from
    -- One-Wire at both widths: as it stands for the wire-0 multiplier,
    -- and lifted for the wire-1 one.
    j₋ : ℕ
    j₋ = One-Wire.j₋ n

    e₋ : (g^ (One-Wire.k₋ n)) .proj₁ ≡ -'₁ .proj₁
    e₋ = One-Wire.e₋ n

    Mg^j₋≈M₋₁ : Mg ^ j₋ ≈ M₋₁
    Mg^j₋≈M₋₁ = One-Wire.lemma-M₋₁-pow (₁₊ n)

    lemma-M₋₁-CZ : M₋₁ • CZ ≈ CZ ^ toℕ (-'₁ .proj₁) • M₋₁
    lemma-M₋₁-CZ = begin
      M₋₁ • CZ                        ≈⟨ cleft sym Mg^j₋≈M₋₁ ⟩
      Mg ^ j₋ • CZ                    ≈⟨ lemma-Mgᵏ-CZ j₋ ⟩
      CZ ^ toℕ (g ^′ j₋) • Mg ^ j₋    ≡⟨ Eq.cong (λ z → CZ ^ toℕ z • Mg ^ j₋) e₋ ⟩
      CZ ^ toℕ (-'₁ .proj₁) • Mg ^ j₋ ≈⟨ cright Mg^j₋≈M₋₁ ⟩
      CZ ^ toℕ (-'₁ .proj₁) • M₋₁ ∎

    -- The same, one wire up.  M-power and aux-M≡M are one-wire facts, so
    -- the ↑ version is the ↓ one lifted, modulo (Mg ^ j) ↑ ≡ (Mg ↑) ^ j.
    Mg↑^j₋≈M₋₁↑ : (Mg ↑) ^ j₋ ≈ M₋₁ ↑
    Mg↑^j₋≈M₋₁↑ = begin
      (Mg ↑) ^ j₋  ≡⟨ Eq.sym (lemma-↑^ j₋ Mg) ⟩
      (Mg ^ j₋) ↑  ≈⟨ lemma-cong↑ _ _ (One-Wire.lemma-M₋₁-pow n) ⟩
      M₋₁ ↑ ∎

  -- Exposed rather than private: Three-Wire needs this one for c14.
  lemma-M₋₁↑-CZ : M₋₁ ↑ • CZ ≈ CZ ^ toℕ (-'₁ .proj₁) • M₋₁ ↑
  lemma-M₋₁↑-CZ = begin
    M₋₁ ↑ • CZ                       ≈⟨ cleft sym Mg↑^j₋≈M₋₁↑ ⟩
    (Mg ↑) ^ j₋ • CZ                 ≈⟨ lemma-Mgᵏ↑-CZ j₋ ⟩
    CZ ^ toℕ (g ^′ j₋) • (Mg ↑) ^ j₋
      ≡⟨ Eq.cong (λ z → CZ ^ toℕ z • (Mg ↑) ^ j₋) e₋ ⟩
    CZ ^ toℕ (-'₁ .proj₁) • (Mg ↑) ^ j₋ ≈⟨ cright Mg↑^j₋≈M₋₁↑ ⟩
    CZ ^ toℕ (-'₁ .proj₁) • M₋₁ ↑ ∎

  -- CZ • CZ⁻¹ is CZ ^ p.  Exposed rather than private: Three-Wire needs
  -- it for c14, where the same cancellation closes the chain.
  lemma-CZ-CZ₋₁ : CZ • CZ ^ toℕ (-'₁ .proj₁) ≈ ε
  lemma-CZ-CZ₋₁ = begin
    CZ • CZ ^ toℕ (-'₁ .proj₁)
      ≡⟨ Eq.cong (λ m → CZ • CZ ^ m) lemma-toℕ-1ₚ ⟩
    CZ • CZ ^ p-1        ≈⟨ sym (^-+ CZ 1 p-1) ⟩
    CZ ^ (1 Nat.+ p-1)   ≈⟨ axiom order-CZ ⟩
    ε ∎

  lemma-ₕ|ₕ-invol : ₕ|ₕ • ₕ|ₕ ≈ ε
  lemma-ₕ|ₕ-invol = begin
    (H • CZ • H) • (H • CZ • H)
      ≈⟨ by-assoc auto ⟩
    H • CZ • (H ^ 2 • (CZ • H))
      ≈⟨ cright cright cleft axiom order-H ⟩
    H • CZ • (M₋₁ • (CZ • H))
      ≈⟨ cright cright sym assoc ⟩
    H • CZ • ((M₋₁ • CZ) • H)
      ≈⟨ cright cright cleft lemma-M₋₁-CZ ⟩
    H • CZ • ((CZ ^ toℕ (-'₁ .proj₁) • M₋₁) • H)
      -- explicit assoc, not by-assoc: to-list is stuck on the symbolic
      -- exponent of CZ ^ toℕ (-'₁ .proj₁)
      ≈⟨ cright cright assoc ⟩
    H • CZ • (CZ ^ toℕ (-'₁ .proj₁) • (M₋₁ • H))
      ≈⟨ cright sym assoc ⟩
    H • ((CZ • CZ ^ toℕ (-'₁ .proj₁)) • (M₋₁ • H))
      ≈⟨ cright cleft lemma-CZ-CZ₋₁ ⟩
    H • (ε • (M₋₁ • H))
      ≈⟨ cright left-unit ⟩
    H • (M₋₁ • H)
      ≈⟨ cright cleft sym (axiom order-H) ⟩
    H • (H ^ 2 • H)
      ≈⟨ by-assoc auto ⟩
    H ^ 4
      ≈⟨ One-Wire.lemma-order-H (₁₊ n) ⟩
    ε ∎

  lemma-ʰ|ʰ-invol : ʰ|ʰ • ʰ|ʰ ≈ ε
  lemma-ʰ|ʰ-invol = begin
    ʰ|ʰ • ʰ|ʰ
      ≈⟨ cong (sym lemma-ʰ|ʰ-conj) (sym lemma-ʰ|ʰ-conj) ⟩
    (Ex • (ₕ|ₕ • Ex)) • (Ex • (ₕ|ₕ • Ex))
      ≈⟨ by-assoc auto ⟩
    Ex • (ₕ|ₕ • ((Ex • Ex) • (ₕ|ₕ • Ex)))
      ≈⟨ cright cright cleft lemma-Ex-Ex ⟩
    Ex • (ₕ|ₕ • (ε • (ₕ|ₕ • Ex)))
      ≈⟨ cright cright left-unit ⟩
    Ex • (ₕ|ₕ • (ₕ|ₕ • Ex))
      ≈⟨ cright sym assoc ⟩
    Ex • ((ₕ|ₕ • ₕ|ₕ) • Ex)
      ≈⟨ cright cleft lemma-ₕ|ₕ-invol ⟩
    Ex • (ε • Ex)
      ≈⟨ cright left-unit ⟩
    Ex • Ex
      ≈⟨ lemma-Ex-Ex ⟩
    ε ∎

  -- ⊥⊤ and ⊤⊥ are the two products of the same pair of involutions.
  lemma-⊥⊤-⊤⊥ : ⊥⊤ • ⊤⊥ ≈ ε
  lemma-⊥⊤-⊤⊥ = begin
    (ₕ|ₕ • ʰ|ʰ) • (ʰ|ʰ • ₕ|ₕ)
      ≈⟨ by-assoc auto ⟩
    ₕ|ₕ • ((ʰ|ʰ • ʰ|ʰ) • ₕ|ₕ)
      ≈⟨ cright cleft lemma-ʰ|ʰ-invol ⟩
    ₕ|ₕ • (ε • ₕ|ₕ)
      ≈⟨ cright left-unit ⟩
    ₕ|ₕ • ₕ|ₕ
      ≈⟨ lemma-ₕ|ₕ-invol ⟩
    ε ∎

  -- With both involutions in hand the two half-swap words collapse to a
  -- single half-swap times a swap: ⊥⊤ • (Ex • ₕ|ₕ) is ₕ|ₕ • ₕ|ₕ after the
  -- two swaps cancel, and likewise on the other side.  These are the
  -- forms c13 is proved in.
  lemma-⊥⊤-simple : ⊥⊤ ≈ Ex • ₕ|ₕ
  lemma-⊥⊤-simple = •-cancelˡ {g = ₕ|ₕ • Ex} (begin
    (ₕ|ₕ • Ex) • ⊥⊤
      ≈⟨ cright lemma-⊥⊤-square ⟩
    (ₕ|ₕ • Ex) • ((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex))
      ≈⟨ sym assoc ⟩
    ((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • (ₕ|ₕ • Ex)
      ≈⟨ lemma-half-swap-cube ⟩
    ε
      ≈⟨ sym lemma-ₕ|ₕ-invol ⟩
    ₕ|ₕ • ₕ|ₕ
      ≈⟨ by-assoc auto ⟩
    ₕ|ₕ • (ε • ₕ|ₕ)
      ≈⟨ cright cleft sym lemma-Ex-Ex ⟩
    ₕ|ₕ • ((Ex • Ex) • ₕ|ₕ)
      ≈⟨ by-assoc auto ⟩
    (ₕ|ₕ • Ex) • (Ex • ₕ|ₕ) ∎)

  lemma-⊤⊥-⊥⊤ : ⊤⊥ • ⊥⊤ ≈ ε
  lemma-⊤⊥-⊥⊤ = begin
    (ʰ|ʰ • ₕ|ₕ) • (ₕ|ₕ • ʰ|ʰ)
      ≈⟨ by-assoc auto ⟩
    ʰ|ʰ • ((ₕ|ₕ • ₕ|ₕ) • ʰ|ʰ)
      ≈⟨ cright cleft lemma-ₕ|ₕ-invol ⟩
    ʰ|ʰ • (ε • ʰ|ʰ)
      ≈⟨ cright left-unit ⟩
    ʰ|ʰ • ʰ|ʰ
      ≈⟨ lemma-ʰ|ʰ-invol ⟩
    ε ∎

  ------------------------------------------------------------------------
  -- The half-swap is a multiplier times a CX
  --
  -- CX is H ^ 3 • CZ • H by definition, so M₋₁ • CX is H ^ 5 • CZ • H,
  -- and H ^ 4 ≈ ε leaves H • CZ • H, which is ₕ|ₕ.  Purely syntactic —
  -- it needs only the definition of CX, order-H and lemma-M₋₁^2.
  --
  -- This is the bridge to C18: C18 tells us how CX ↑ moves across a CZ,
  -- and this lemma turns that into a statement about the half-swap, which
  -- is what c14 is stated over.

  lemma-ₕ|ₕ-CX : M₋₁ • CX ≈ ₕ|ₕ
  lemma-ₕ|ₕ-CX = begin
    M₋₁ • CX
      ≈⟨ cleft sym (axiom order-H) ⟩
    H ^ 2 • CX
      ≈⟨ by-assoc auto ⟩
    (H ^ 4 • H) • (CZ • H)
      ≈⟨ cleft cleft One-Wire.lemma-order-H (₁₊ n) ⟩
    (ε • H) • (CZ • H)
      ≈⟨ cleft left-unit ⟩
    H • (CZ • H) ∎

  lemma-⊤⊥-simple : ⊤⊥ ≈ ₕ|ₕ • Ex
  lemma-⊤⊥-simple = •-cancelʳ {h = ⊥⊤} (begin
    ⊤⊥ • ⊥⊤                  ≈⟨ lemma-⊤⊥-⊥⊤ ⟩
    ε                        ≈⟨ sym lemma-ₕ|ₕ-invol ⟩
    ₕ|ₕ • ₕ|ₕ                ≈⟨ by-assoc auto ⟩
    ₕ|ₕ • (ε • ₕ|ₕ)          ≈⟨ cright cleft sym lemma-Ex-Ex ⟩
    ₕ|ₕ • ((Ex • Ex) • ₕ|ₕ)  ≈⟨ by-assoc auto ⟩
    (ₕ|ₕ • Ex) • (Ex • ₕ|ₕ)  ≈⟨ cright sym lemma-⊥⊤-simple ⟩
    (ₕ|ₕ • Ex) • ⊥⊤ ∎)

  -- The cube, stated over ⊤⊥ itself rather than over ₕ|ₕ • Ex.
  ------------------------------------------------------------------------
  -- CZ against H ↑
  --
  -- XC is H ↑ ^ 3 • CZ • H ↑ by definition, so H ↑ • XC is CZ • H ↑ once
  -- H ↑ ^ 4 ≈ ε closes the loop.  This is what peels a leading H ↑ off
  -- both sides of c10, leaving the reduced core
  --
  --     XC • CZ ≈ R ↑ • XC • R ↑ ⁻¹ • R ↓ ⁻¹.
  --
  -- (The swap-dual of CX that the core then needs is already available:
  -- lemma-conj-Ex-CX turns blake-c12 into its XC form.)

  ------------------------------------------------------------------------
  -- A power of the upper X across CZ
  --
  -- rel-X↑-CZ moves one X ↑ across CZ at the cost of a Z on wire 0.
  -- Iterating collects one Z per crossing; the Z's slide back past the
  -- remaining X ↑ because they sit on different wires (lemma-comm-Z-w↑),
  -- so the corrections gather into a single power.

  lemma-CZ-X↑ᵏ : ∀ m → CZ • (X ↑) ^ m ≈ (X ↑) ^ m • ((Z ↓) ^ m • CZ)
  lemma-CZ-X↑ᵏ ₀ = begin
    CZ • ε              ≈⟨ right-unit ⟩
    CZ                  ≈⟨ sym left-unit ⟩
    ε • CZ              ≈⟨ sym left-unit ⟩
    ε • (ε • CZ) ∎
  lemma-CZ-X↑ᵏ ₁ = axiom rel-X↑-CZ
  lemma-CZ-X↑ᵏ (₂₊ k) = begin
    CZ • (X ↑ • (X ↑) ^ ₁₊ k)
      ≈⟨ sym assoc ⟩
    (CZ • X ↑) • (X ↑) ^ ₁₊ k
      ≈⟨ cleft axiom rel-X↑-CZ ⟩
    (X ↑ • (Z ↓ • CZ)) • (X ↑) ^ ₁₊ k
      ≈⟨ assoc ⟩
    X ↑ • ((Z ↓ • CZ) • (X ↑) ^ ₁₊ k)
      ≈⟨ cright assoc ⟩
    X ↑ • (Z ↓ • (CZ • (X ↑) ^ ₁₊ k))
      ≈⟨ cright cright lemma-CZ-X↑ᵏ (₁₊ k) ⟩
    X ↑ • (Z ↓ • ((X ↑) ^ ₁₊ k • ((Z ↓) ^ ₁₊ k • CZ)))
      ≈⟨ cright sym assoc ⟩
    X ↑ • ((Z ↓ • (X ↑) ^ ₁₊ k) • ((Z ↓) ^ ₁₊ k • CZ))
      ≈⟨ cright cleft slide ⟩
    X ↑ • (((X ↑) ^ ₁₊ k • Z ↓) • ((Z ↓) ^ ₁₊ k • CZ))
      ≈⟨ cright assoc ⟩
    X ↑ • ((X ↑) ^ ₁₊ k • (Z ↓ • ((Z ↓) ^ ₁₊ k • CZ)))
      ≈⟨ sym assoc ⟩
    (X ↑ • (X ↑) ^ ₁₊ k) • (Z ↓ • ((Z ↓) ^ ₁₊ k • CZ))
      ≈⟨ cright sym assoc ⟩
    (X ↑ • (X ↑) ^ ₁₊ k) • ((Z ↓ • (Z ↓) ^ ₁₊ k) • CZ) ∎
    where
    slide : Z ↓ • (X ↑) ^ ₁₊ k ≈ (X ↑) ^ ₁₊ k • Z ↓
    slide = begin
      Z ↓ • (X ↑) ^ ₁₊ k  ≡⟨ Eq.cong (λ w → Z ↓ • w) (Eq.sym (lemma-↑^ (₁₊ k) X)) ⟩
      Z ↓ • (X ^ ₁₊ k) ↑  ≈⟨ lemma-comm-Z-w↑ (X ^ ₁₊ k) ⟩
      (X ^ ₁₊ k) ↑ • Z ↓  ≡⟨ Eq.cong (λ w → w • Z ↓) (lemma-↑^ (₁₊ k) X) ⟩
      (X ↑) ^ ₁₊ k • Z ↓ ∎

  lemma-CZ-H↑ : CZ • H ↑ ≈ H ↑ • XC
  lemma-CZ-H↑ = begin
    CZ • H ↑
      ≈⟨ cleft sym left-unit ⟩
    (ε • CZ) • H ↑
      ≈⟨ cleft cleft sym lemma-order-H↑ ⟩
    ((H ↑) ^ 4 • CZ) • H ↑
      ≈⟨ by-assoc auto ⟩
    H ↑ • ((H ↑) ^ 3 • (CZ • H ↑)) ∎

  ------------------------------------------------------------------------
  -- The swap-dual of blake-c12
  --
  -- Conjugating blake-c12 by Ex exchanges CX with XC and the two wires'
  -- phase gates, and fixes CZ.  Every step is an instance of the
  -- Ex-conjugation homomorphism lemma-Ex-• and its power version
  -- lemma-Ex-pow, so the proof is just those applied factor by factor.
  --
  -- This is the form c10's reduced core needs: it is the XC statement
  -- from which the commutator [XC , S ↑] ≈ CZ • S falls out.

  lemma-Ex-blake :
    S ^ p-1 • ((S ↑) ^ p-1 • (XC ^ p-1 • (S ↑ • XC))) ≈ CZ
  lemma-Ex-blake = •-cancelʳ {h = Ex} (begin
    (S ^ p-1 • ((S ↑) ^ p-1 • (XC ^ p-1 • (S ↑ • XC)))) • Ex
      ≈⟨ sym hom ⟩
    Ex • ((S ↑) ^ p-1 • (S ^ p-1 • (CX ^ p-1 • (S • CX))))
      ≈⟨ cright blake ⟩
    Ex • CZ
      ≈⟨ lemma-Ex-CZ ⟩
    CZ • Ex ∎)
    where
    hom : Ex • ((S ↑) ^ p-1 • (S ^ p-1 • (CX ^ p-1 • (S • CX))))
        ≈ (S ^ p-1 • ((S ↑) ^ p-1 • (XC ^ p-1 • (S ↑ • XC)))) • Ex
    hom = lemma-Ex-• (lemma-Ex-pow lemma-Ex-S↑ p-1)
            (lemma-Ex-• (lemma-Ex-pow lemma-Ex-S p-1)
              (lemma-Ex-• (lemma-Ex-pow lemma-Ex-CX p-1)
                (lemma-Ex-• lemma-Ex-S lemma-Ex-CX)))

    blake : (S ↑) ^ p-1 • (S ^ p-1 • (CX ^ p-1 • (S • CX))) ≈ CZ
    blake = begin
      (S ↑) ^ p-1 • (S ^ p-1 • (CX ^ p-1 • (S • CX)))
        ≡⟨ Eq.cong (λ w → w • (S ^ p-1 • (CX ^ p-1 • (S • CX))))
                   (Eq.sym (lemma-↑^ p-1 S)) ⟩
      (S ^ p-1) ↑ • (S ^ p-1 • (CX ^ p-1 • (S • CX)))
        ≈⟨ axiom blake-c12 ⟩
      CZ ∎

  ------------------------------------------------------------------------
  -- The commutator of XC with the upper phase gate
  --
  -- Multiplying lemma-Ex-blake on the left by S ↑ • S completes both of
  -- its leading powers to a full p-th power, and order-S kills them.
  -- What is left is the conjugation rule c10's reduced core is built
  -- from.  (The axiom is stated in Word order, so the powers lead and
  -- the cancellation is on the left.)

  private
    lemma-S-Sᵖ⁻¹ : S • S ^ p-1 ≈ ε
    lemma-S-Sᵖ⁻¹ = begin
      S • S ^ p-1        ≈⟨ sym (^-+ S 1 p-1) ⟩
      S ^ (1 Nat.+ p-1)  ≈⟨ axiom order-S ⟩
      ε ∎

    lemma-S↑-S↑ᵖ⁻¹ : S ↑ • (S ↑) ^ p-1 ≈ ε
    lemma-S↑-S↑ᵖ⁻¹ = begin
      S ↑ • (S ↑) ^ p-1      ≈⟨ sym (^-+ (S ↑) 1 p-1) ⟩
      (S ↑) ^ (1 Nat.+ p-1)  ≡⟨ Eq.sym (lemma-↑^ p S) ⟩
      (S ^ p) ↑              ≈⟨ lemma-cong↑ _ _ (One-Wire.lemma-order-S n) ⟩
      ε ∎

  lemma-comm-XC-S↑ : XC ^ p-1 • (S ↑ • XC) ≈ S ↑ • (S • CZ)
  lemma-comm-XC-S↑ = begin
    XC ^ p-1 • (S ↑ • XC)
      ≈⟨ sym left-unit ⟩
    ε • (XC ^ p-1 • (S ↑ • XC))
      ≈⟨ cleft sym lemma-S↑-S↑ᵖ⁻¹ ⟩
    (S ↑ • (S ↑) ^ p-1) • (XC ^ p-1 • (S ↑ • XC))
      -- explicit assoc: the powers are symbolic, so to-list is stuck
      ≈⟨ assoc ⟩
    S ↑ • ((S ↑) ^ p-1 • (XC ^ p-1 • (S ↑ • XC)))
      ≈⟨ cright sym left-unit ⟩
    S ↑ • (ε • ((S ↑) ^ p-1 • (XC ^ p-1 • (S ↑ • XC))))
      ≈⟨ cright cleft sym lemma-S-Sᵖ⁻¹ ⟩
    S ↑ • ((S • S ^ p-1) • ((S ↑) ^ p-1 • (XC ^ p-1 • (S ↑ • XC))))
      ≈⟨ cright assoc ⟩
    S ↑ • (S • (S ^ p-1 • ((S ↑) ^ p-1 • (XC ^ p-1 • (S ↑ • XC)))))
      ≈⟨ cright cright lemma-Ex-blake ⟩
    S ↑ • (S • CZ) ∎

  ------------------------------------------------------------------------
  -- Z commutes with CZ
  --
  -- CZ is diagonal, so a Z on either wire passes it — but that is not a
  -- structural rule, and Paper-V0 has no axiom for it.  It comes from the
  -- multiplier instead: order-H makes H ^ 2 the multiplier by −1,
  -- lemma-M₋₁-CZ says that multiplier inverts the CZ it passes, and Z is
  -- H ^ 2 • S • H ^ 2 • S ⁻¹ — two multipliers, so the two rescalings
  -- cancel, and the S's pass by lemma-comm-CZ-S.
  --
  -- Simplified-V1 gets the same fact (LemmasCZ.lemma-comm-Z↑-CZ) through
  -- an eight-lemma chain over the H • H • S • H • H block; going through
  -- M₋₁ directly is shorter and needs nothing V1-only.

  private
    e₁ : ℕ
    e₁ = toℕ (-'₁ .proj₁)

    M₋₁M₋₁ : M₋₁ • M₋₁ ≈ ε
    M₋₁M₋₁ = One-Wire.lemma-M₋₁^2 (₁₊ n)

    -- lemma-M₋₁-CZ read from the other side, by conjugating with M₋₁.
    lemma-CZ-M₋₁ : CZ • M₋₁ ≈ M₋₁ • CZ ^ e₁
    lemma-CZ-M₋₁ = begin
      CZ • M₋₁
        ≈⟨ cleft sym left-unit ⟩
      (ε • CZ) • M₋₁
        ≈⟨ cleft cleft sym M₋₁M₋₁ ⟩
      ((M₋₁ • M₋₁) • CZ) • M₋₁
        ≈⟨ cleft assoc ⟩
      (M₋₁ • (M₋₁ • CZ)) • M₋₁
        ≈⟨ cleft cright lemma-M₋₁-CZ ⟩
      (M₋₁ • (CZ ^ e₁ • M₋₁)) • M₋₁
        ≈⟨ cleft sym assoc ⟩
      ((M₋₁ • CZ ^ e₁) • M₋₁) • M₋₁
        ≈⟨ assoc ⟩
      (M₋₁ • CZ ^ e₁) • (M₋₁ • M₋₁)
        ≈⟨ cright M₋₁M₋₁ ⟩
      (M₋₁ • CZ ^ e₁) • ε
        ≈⟨ right-unit ⟩
      M₋₁ • CZ ^ e₁ ∎

    Z-split : Z ≈ M₋₁ • (S • (M₋₁ • S⁻¹))
    Z-split = begin
      H • (H • (S • (H • (H • S⁻¹))))
        ≈⟨ sym assoc ⟩
      (H • H) • (S • (H • (H • S⁻¹)))
        ≈⟨ cright cright sym assoc ⟩
      (H • H) • (S • ((H • H) • S⁻¹))
        ≈⟨ cong (axiom order-H) (cright cleft axiom order-H) ⟩
      M₋₁ • (S • (M₋₁ • S⁻¹)) ∎

  lemma-comm-CZ-Z : CZ • Z ≈ Z • CZ
  lemma-comm-CZ-Z = begin
    CZ • Z
      ≈⟨ cright Z-split ⟩
    CZ • (M₋₁ • (S • (M₋₁ • S⁻¹)))
      ≈⟨ sym assoc ⟩
    (CZ • M₋₁) • (S • (M₋₁ • S⁻¹))
      ≈⟨ cleft lemma-CZ-M₋₁ ⟩
    (M₋₁ • CZ ^ e₁) • (S • (M₋₁ • S⁻¹))
      ≈⟨ assoc ⟩
    M₋₁ • (CZ ^ e₁ • (S • (M₋₁ • S⁻¹)))
      ≈⟨ cright sym assoc ⟩
    M₋₁ • ((CZ ^ e₁ • S) • (M₋₁ • S⁻¹))
      ≈⟨ cright cleft comm⇒pow-comm e₁ 1 lemma-comm-CZ-S ⟩
    M₋₁ • ((S • CZ ^ e₁) • (M₋₁ • S⁻¹))
      ≈⟨ cright assoc ⟩
    M₋₁ • (S • (CZ ^ e₁ • (M₋₁ • S⁻¹)))
      ≈⟨ cright cright sym assoc ⟩
    M₋₁ • (S • ((CZ ^ e₁ • M₋₁) • S⁻¹))
      ≈⟨ cright cright cleft sym lemma-M₋₁-CZ ⟩
    M₋₁ • (S • ((M₋₁ • CZ) • S⁻¹))
      ≈⟨ cright cright assoc ⟩
    M₋₁ • (S • (M₋₁ • (CZ • S⁻¹)))
      ≈⟨ cright cright cright comm⇒pow-comm 1 p-1 lemma-comm-CZ-S ⟩
    M₋₁ • (S • (M₋₁ • (S⁻¹ • CZ)))
      ≈⟨ cright cright sym assoc ⟩
    M₋₁ • (S • ((M₋₁ • S⁻¹) • CZ))
      ≈⟨ cright sym assoc ⟩
    M₋₁ • ((S • (M₋₁ • S⁻¹)) • CZ)
      ≈⟨ sym assoc ⟩
    (M₋₁ • (S • (M₋₁ • S⁻¹))) • CZ
      ≈⟨ cleft sym Z-split ⟩
    Z • CZ ∎

  private
    -- The swap carries the wire-1 Z down to wire 0, so the ↑ version is
    -- the ↓ one conjugated — cheaper than repeating the multiplier chain.
    Z↑-conj : Z ↑ ≈ Ex • (Z • Ex)
    Z↑-conj = begin
      Z ↑              ≈⟨ sym left-unit ⟩
      ε • Z ↑          ≈⟨ cleft sym lemma-Ex-Ex ⟩
      (Ex • Ex) • Z ↑  ≈⟨ assoc ⟩
      Ex • (Ex • Z ↑)  ≈⟨ cright lemma-Ex-Z↑ ⟩
      Ex • (Z • Ex) ∎

  lemma-comm-CZ-Z↑ : CZ • Z ↑ ≈ Z ↑ • CZ
  lemma-comm-CZ-Z↑ = begin
    CZ • Z ↑              ≈⟨ cright Z↑-conj ⟩
    CZ • (Ex • (Z • Ex))  ≈⟨ sym assoc ⟩
    (CZ • Ex) • (Z • Ex)  ≈⟨ cleft sym lemma-Ex-CZ ⟩
    (Ex • CZ) • (Z • Ex)  ≈⟨ assoc ⟩
    Ex • (CZ • (Z • Ex))  ≈⟨ cright sym assoc ⟩
    Ex • ((CZ • Z) • Ex)  ≈⟨ cright cleft lemma-comm-CZ-Z ⟩
    Ex • ((Z • CZ) • Ex)  ≈⟨ cright assoc ⟩
    Ex • (Z • (CZ • Ex))  ≈⟨ cright cright sym lemma-Ex-CZ ⟩
    Ex • (Z • (Ex • CZ))  ≈⟨ cright sym assoc ⟩
    Ex • ((Z • Ex) • CZ)  ≈⟨ sym assoc ⟩
    (Ex • (Z • Ex)) • CZ  ≈⟨ cleft sym Z↑-conj ⟩
    Z ↑ • CZ ∎

  ------------------------------------------------------------------------
  -- A Pauli across a power of CZ
  --
  -- rel-X↑-CZ iterated in the CZ exponent.  The Z's the crossings emit
  -- gather into a single power, since they pass the CZ's still to come.

  -- (_↓ is the identity on circuits — it only pins a wire count — so the
  -- Z ↓ the axiom emits *is* the wire-0 Z, with no conversion needed.)
  lemma-CZᵏ-X↑ : ∀ j → CZ ^ j • X ↑ ≈ X ↑ • (Z ^ j • CZ ^ j)
  lemma-CZᵏ-X↑ ₀ = begin
    ε • X ↑        ≈⟨ left-unit ⟩
    X ↑            ≈⟨ sym right-unit ⟩
    X ↑ • ε        ≈⟨ cright sym left-unit ⟩
    X ↑ • (ε • ε) ∎
  lemma-CZᵏ-X↑ ₁ = axiom rel-X↑-CZ
  lemma-CZᵏ-X↑ (₂₊ j) = begin
    (CZ • CZ ^ ₁₊ j) • X ↑
      ≈⟨ assoc ⟩
    CZ • (CZ ^ ₁₊ j • X ↑)
      ≈⟨ cright lemma-CZᵏ-X↑ (₁₊ j) ⟩
    CZ • (X ↑ • (Z ^ ₁₊ j • CZ ^ ₁₊ j))
      ≈⟨ sym assoc ⟩
    (CZ • X ↑) • (Z ^ ₁₊ j • CZ ^ ₁₊ j)
      ≈⟨ cleft lemma-CZᵏ-X↑ 1 ⟩
    (X ↑ • (Z • CZ)) • (Z ^ ₁₊ j • CZ ^ ₁₊ j)
      ≈⟨ assoc ⟩
    X ↑ • ((Z • CZ) • (Z ^ ₁₊ j • CZ ^ ₁₊ j))
      ≈⟨ cright assoc ⟩
    X ↑ • (Z • (CZ • (Z ^ ₁₊ j • CZ ^ ₁₊ j)))
      ≈⟨ cright cright sym assoc ⟩
    X ↑ • (Z • ((CZ • Z ^ ₁₊ j) • CZ ^ ₁₊ j))
      ≈⟨ cright cright cleft comm⇒pow-comm 1 (₁₊ j) lemma-comm-CZ-Z ⟩
    X ↑ • (Z • ((Z ^ ₁₊ j • CZ) • CZ ^ ₁₊ j))
      ≈⟨ cright cright assoc ⟩
    X ↑ • (Z • (Z ^ ₁₊ j • (CZ • CZ ^ ₁₊ j)))
      ≈⟨ cright sym assoc ⟩
    X ↑ • ((Z • Z ^ ₁₊ j) • (CZ • CZ ^ ₁₊ j)) ∎

  private
    Zᵖ : Z ^ p-1 • Z ≈ ε
    Zᵖ = begin
      Z ^ p-1 • Z        ≈⟨ sym (^-+ Z p-1 1) ⟩
      Z ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (Z ^_) (NP.+-comm p-1 1) ⟩
      Z ^ p              ≈⟨ One-Wire.lemma-order-Z (₁₊ n) ⟩
      ε ∎

  -- The same crossing read the other way at the exponent p-1: the p-1
  -- Z's the crossings emit complete to a full p-th power against the one
  -- carried in, so exactly one Z is left over.
  lemma-X↑-CZᵖ⁻¹ : X ↑ • CZ ^ p-1 ≈ CZ ^ p-1 • (X ↑ • Z)
  lemma-X↑-CZᵖ⁻¹ = sym (begin
    CZ ^ p-1 • (X ↑ • Z)
      ≈⟨ sym assoc ⟩
    (CZ ^ p-1 • X ↑) • Z
      ≈⟨ cleft lemma-CZᵏ-X↑ p-1 ⟩
    (X ↑ • (Z ^ p-1 • CZ ^ p-1)) • Z
      ≈⟨ assoc ⟩
    X ↑ • ((Z ^ p-1 • CZ ^ p-1) • Z)
      ≈⟨ cright assoc ⟩
    X ↑ • (Z ^ p-1 • (CZ ^ p-1 • Z))
      ≈⟨ cright cright comm⇒pow-comm p-1 1 lemma-comm-CZ-Z ⟩
    X ↑ • (Z ^ p-1 • (Z • CZ ^ p-1))
      ≈⟨ cright sym assoc ⟩
    X ↑ • ((Z ^ p-1 • Z) • CZ ^ p-1)
      ≈⟨ cright cleft Zᵖ ⟩
    X ↑ • (ε • CZ ^ p-1)
      ≈⟨ cright left-unit ⟩
    X ↑ • CZ ^ p-1 ∎)

  ------------------------------------------------------------------------
  -- The Pauli-versus-XC rule
  --
  -- XC = H ↑ ^ 3 • CZ • H ↑ has its control on wire 0 and its target on
  -- wire 1, so it conjugates a Z on wire 1 to Z ↑ • Z.  Every crossing is
  -- now available: lemma-Z-conj and lemma-X-H³ take the Pauli across the
  -- two H ↑ factors, and lemma-X↑-CZᵖ⁻¹ takes it across the CZ between
  -- them.  Nothing here has a negative exponent — the H-crossings were
  -- chosen in the directions that emit positive powers.
  --
  -- This is exactly the gap between the S-spelling of the commutator,
  -- which blake-c12 gives, and the R-spelling that c10 is stated in:
  -- R = S • Z ^ ½, so the two differ by this Pauli and by nothing else.

  private
    H↑³H↑ : (H ↑) ^ 3 • H ↑ ≈ ε
    H↑³H↑ = begin
      (H ↑) ^ 3 • H ↑  ≈⟨ sym (^-+ (H ↑) 3 1) ⟩
      (H ↑) ^ 4        ≈⟨ lemma-order-H↑ ⟩
      ε ∎

    H↑⁶ : (H ↑) ^ 3 • (H ↑) ^ 3 ≈ M₋₁ ↑
    H↑⁶ = begin
      (H ↑) ^ 3 • (H ↑) ^ 3  ≈⟨ sym (^-+ (H ↑) 3 3) ⟩
      (H ↑) ^ 6              ≈⟨ ^-+ (H ↑) 4 2 ⟩
      (H ↑) ^ 4 • (H ↑) ^ 2  ≈⟨ cleft lemma-order-H↑ ⟩
      ε • (H ↑) ^ 2          ≈⟨ left-unit ⟩
      (H ↑) ^ 2              ≈⟨ lemma-cong↑ _ _ (PB₁.axiom order-H) ⟩
      M₋₁ ↑ ∎

    M₋₁↑H↑ : M₋₁ ↑ • H ↑ ≈ (H ↑) ^ 3
    M₋₁↑H↑ = begin
      M₋₁ ↑ • H ↑      ≈⟨ cleft sym (lemma-cong↑ _ _ (PB₁.axiom order-H)) ⟩
      (H ↑) ^ 2 • H ↑  ≈⟨ sym (^-+ (H ↑) 2 1) ⟩
      (H ↑) ^ 3 ∎

    lemma-M₋₁↑-CZ' : M₋₁ ↑ • CZ ≈ CZ ^ p-1 • M₋₁ ↑
    lemma-M₋₁↑-CZ' = begin
      M₋₁ ↑ • CZ       ≈⟨ lemma-M₋₁↑-CZ ⟩
      CZ ^ e₁ • M₋₁ ↑  ≡⟨ Eq.cong (λ m → CZ ^ m • M₋₁ ↑) lemma-toℕ-1ₚ ⟩
      CZ ^ p-1 • M₋₁ ↑ ∎

  -- XC read from the other side.  The two spellings of the conjugation
  -- differ by an H ↑ ^ 2, which is the multiplier by −1 and inverts the
  -- CZ it passes.
  lemma-XC-flip : H ↑ • (CZ ^ p-1 • (H ↑) ^ 3) ≈ XC
  lemma-XC-flip = •-cancelˡ {g = (H ↑) ^ 3} (begin
    (H ↑) ^ 3 • (H ↑ • (CZ ^ p-1 • (H ↑) ^ 3))
      ≈⟨ sym assoc ⟩
    ((H ↑) ^ 3 • H ↑) • (CZ ^ p-1 • (H ↑) ^ 3)
      ≈⟨ cleft H↑³H↑ ⟩
    ε • (CZ ^ p-1 • (H ↑) ^ 3)
      ≈⟨ left-unit ⟩
    CZ ^ p-1 • (H ↑) ^ 3
      ≈⟨ cright sym M₋₁↑H↑ ⟩
    CZ ^ p-1 • (M₋₁ ↑ • H ↑)
      ≈⟨ sym assoc ⟩
    (CZ ^ p-1 • M₋₁ ↑) • H ↑
      ≈⟨ cleft sym lemma-M₋₁↑-CZ' ⟩
    (M₋₁ ↑ • CZ) • H ↑
      ≈⟨ cleft cleft sym H↑⁶ ⟩
    (((H ↑) ^ 3 • (H ↑) ^ 3) • CZ) • H ↑
      ≈⟨ cleft assoc ⟩
    ((H ↑) ^ 3 • ((H ↑) ^ 3 • CZ)) • H ↑
      ≈⟨ assoc ⟩
    (H ↑) ^ 3 • (((H ↑) ^ 3 • CZ) • H ↑)
      ≈⟨ cright assoc ⟩
    (H ↑) ^ 3 • ((H ↑) ^ 3 • (CZ • H ↑)) ∎)

  lemma-conj-XC-Z↑ : Z ↑ • XC ≈ XC • (Z ↑ • Z)
  lemma-conj-XC-Z↑ = begin
    Z ↑ • XC
      ≈⟨ cleft (lemma-cong↑ _ _ (One-Wire-Group.lemma-Z-conj n)) ⟩
    (H ↑ • (X ↑ • (H ↑) ^ 3)) • ((H ↑) ^ 3 • (CZ • H ↑))
      ≈⟨ assoc ⟩
    H ↑ • ((X ↑ • (H ↑) ^ 3) • ((H ↑) ^ 3 • (CZ • H ↑)))
      ≈⟨ cright assoc ⟩
    H ↑ • (X ↑ • ((H ↑) ^ 3 • ((H ↑) ^ 3 • (CZ • H ↑))))
      ≈⟨ cright cright sym assoc ⟩
    H ↑ • (X ↑ • (((H ↑) ^ 3 • (H ↑) ^ 3) • (CZ • H ↑)))
      ≈⟨ cright cright cleft H↑⁶ ⟩
    H ↑ • (X ↑ • (M₋₁ ↑ • (CZ • H ↑)))
      ≈⟨ cright cright sym assoc ⟩
    H ↑ • (X ↑ • ((M₋₁ ↑ • CZ) • H ↑))
      ≈⟨ cright cright cleft lemma-M₋₁↑-CZ' ⟩
    H ↑ • (X ↑ • ((CZ ^ p-1 • M₋₁ ↑) • H ↑))
      ≈⟨ cright cright assoc ⟩
    H ↑ • (X ↑ • (CZ ^ p-1 • (M₋₁ ↑ • H ↑)))
      ≈⟨ cright cright cright M₋₁↑H↑ ⟩
    H ↑ • (X ↑ • (CZ ^ p-1 • (H ↑) ^ 3))
      ≈⟨ cright sym assoc ⟩
    H ↑ • ((X ↑ • CZ ^ p-1) • (H ↑) ^ 3)
      ≈⟨ cright cleft lemma-X↑-CZᵖ⁻¹ ⟩
    H ↑ • ((CZ ^ p-1 • (X ↑ • Z)) • (H ↑) ^ 3)
      ≈⟨ cright assoc ⟩
    H ↑ • (CZ ^ p-1 • ((X ↑ • Z) • (H ↑) ^ 3))
      ≈⟨ cright cright assoc ⟩
    H ↑ • (CZ ^ p-1 • (X ↑ • (Z • (H ↑) ^ 3)))
      ≈⟨ cright cright cright lemma-comm-Z-w↑ (H ^ 3) ⟩
    H ↑ • (CZ ^ p-1 • (X ↑ • ((H ↑) ^ 3 • Z)))
      ≈⟨ cright cright sym assoc ⟩
    H ↑ • (CZ ^ p-1 • ((X ↑ • (H ↑) ^ 3) • Z))
      ≈⟨ cright cright cleft (lemma-cong↑ _ _ (One-Wire-Group.lemma-X-H³ n)) ⟩
    H ↑ • (CZ ^ p-1 • (((H ↑) ^ 3 • Z ↑) • Z))
      ≈⟨ cright cright assoc ⟩
    H ↑ • (CZ ^ p-1 • ((H ↑) ^ 3 • (Z ↑ • Z)))
      ≈⟨ cright sym assoc ⟩
    H ↑ • ((CZ ^ p-1 • (H ↑) ^ 3) • (Z ↑ • Z))
      ≈⟨ sym assoc ⟩
    (H ↑ • (CZ ^ p-1 • (H ↑) ^ 3)) • (Z ↑ • Z)
      ≈⟨ cleft lemma-XC-flip ⟩
    XC • (Z ↑ • Z) ∎

  lemma-conj-XC-Z↑ᵏ : ∀ k → (Z ↑) ^ k • XC ≈ XC • ((Z ↑) ^ k • Z ^ k)
  lemma-conj-XC-Z↑ᵏ k = begin
    (Z ↑) ^ k • XC
      ≈⟨ lemma-Inductionˡ lemma-conj-XC-Z↑ k ⟩
    XC • (Z ↑ • Z) ^ k
      ≈⟨ cright ^-• (Z ↑) Z k (sym (lemma-comm-Z-w↑ Z)) ⟩
    XC • ((Z ↑) ^ k • Z ^ k) ∎

  ------------------------------------------------------------------------
  -- The commutator of XC with the upper R
  --
  -- lemma-comm-XC-S↑ is stated with the p-1 power in front, because
  -- blake-c12 is; flipping it needs XC ^ p ≈ ε, which holds because XC is
  -- a CZ conjugated by H ↑.  Substituting R = S • Z ^ ½ then splits the
  -- conjugation into the S part, which is that commutator, and the Pauli
  -- part, which is lemma-conj-XC-Z↑ᵏ.

  private
    h : ℕ
    h = toℕ 1/2

    lemma-XCᵏ : ∀ k → XC ^ k ≈ (H ↑) ^ 3 • (CZ ^ k • H ↑)
    lemma-XCᵏ ₀ = begin
      ε                      ≈⟨ sym H↑³H↑ ⟩
      (H ↑) ^ 3 • H ↑        ≈⟨ cright sym left-unit ⟩
      (H ↑) ^ 3 • (ε • H ↑) ∎
    lemma-XCᵏ ₁ = refl
    lemma-XCᵏ (₂₊ k) = begin
      XC • XC ^ ₁₊ k
        ≈⟨ cright lemma-XCᵏ (₁₊ k) ⟩
      ((H ↑) ^ 3 • (CZ • H ↑)) • ((H ↑) ^ 3 • (CZ ^ ₁₊ k • H ↑))
        ≈⟨ assoc ⟩
      (H ↑) ^ 3 • ((CZ • H ↑) • ((H ↑) ^ 3 • (CZ ^ ₁₊ k • H ↑)))
        ≈⟨ cright assoc ⟩
      (H ↑) ^ 3 • (CZ • (H ↑ • ((H ↑) ^ 3 • (CZ ^ ₁₊ k • H ↑))))
        ≈⟨ cright cright sym assoc ⟩
      (H ↑) ^ 3 • (CZ • ((H ↑ • (H ↑) ^ 3) • (CZ ^ ₁₊ k • H ↑)))
        ≈⟨ cright cright cleft lemma-order-H↑ ⟩
      (H ↑) ^ 3 • (CZ • (ε • (CZ ^ ₁₊ k • H ↑)))
        ≈⟨ cright cright left-unit ⟩
      (H ↑) ^ 3 • (CZ • (CZ ^ ₁₊ k • H ↑))
        ≈⟨ cright sym assoc ⟩
      (H ↑) ^ 3 • ((CZ • CZ ^ ₁₊ k) • H ↑) ∎

    lemma-order-XC : XC ^ p ≈ ε
    lemma-order-XC = begin
      XC ^ p                      ≈⟨ lemma-XCᵏ p ⟩
      (H ↑) ^ 3 • (CZ ^ p • H ↑)  ≈⟨ cright cleft axiom order-CZ ⟩
      (H ↑) ^ 3 • (ε • H ↑)       ≈⟨ cright left-unit ⟩
      (H ↑) ^ 3 • H ↑             ≈⟨ H↑³H↑ ⟩
      ε ∎

    XCᵖ⁻¹XC : XC ^ p-1 • XC ≈ ε
    XCᵖ⁻¹XC = begin
      XC ^ p-1 • XC       ≈⟨ sym (^-+ XC p-1 1) ⟩
      XC ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (XC ^_) (NP.+-comm p-1 1) ⟩
      XC ^ p              ≈⟨ lemma-order-XC ⟩
      ε ∎

    S-Z↑ʰ : S • (Z ↑) ^ h ≈ (Z ↑) ^ h • S
    S-Z↑ʰ = begin
      S • (Z ↑) ^ h  ≡⟨ Eq.cong (S •_) (Eq.sym (lemma-↑^ h Z)) ⟩
      S • (Z ^ h) ↑  ≈⟨ lemma-comm-S-w↑ (Z ^ h) ⟩
      (Z ^ h) ↑ • S  ≡⟨ Eq.cong (_• S) (lemma-↑^ h Z) ⟩
      (Z ↑) ^ h • S ∎

  lemma-comm-XC-S↑' : S ↑ • XC ≈ XC • (S ↑ • (S • CZ))
  lemma-comm-XC-S↑' = •-cancelˡ {g = XC ^ p-1} (begin
    XC ^ p-1 • (S ↑ • XC)
      ≈⟨ lemma-comm-XC-S↑ ⟩
    S ↑ • (S • CZ)
      ≈⟨ sym left-unit ⟩
    ε • (S ↑ • (S • CZ))
      ≈⟨ cleft sym XCᵖ⁻¹XC ⟩
    (XC ^ p-1 • XC) • (S ↑ • (S • CZ))
      ≈⟨ assoc ⟩
    XC ^ p-1 • (XC • (S ↑ • (S • CZ))) ∎)

  lemma-comm-XC-R↑ : R ↑ • XC ≈ XC • (R ↑ • (R • CZ))
  lemma-comm-XC-R↑ = begin
    R ↑ • XC
      ≡⟨ Eq.cong (λ w → (S ↑ • w) • XC) (lemma-↑^ h Z) ⟩
    (S ↑ • (Z ↑) ^ h) • XC
      ≈⟨ assoc ⟩
    S ↑ • ((Z ↑) ^ h • XC)
      ≈⟨ cright lemma-conj-XC-Z↑ᵏ h ⟩
    S ↑ • (XC • ((Z ↑) ^ h • Z ^ h))
      ≈⟨ sym assoc ⟩
    (S ↑ • XC) • ((Z ↑) ^ h • Z ^ h)
      ≈⟨ cleft lemma-comm-XC-S↑' ⟩
    (XC • (S ↑ • (S • CZ))) • ((Z ↑) ^ h • Z ^ h)
      ≈⟨ assoc ⟩
    XC • ((S ↑ • (S • CZ)) • ((Z ↑) ^ h • Z ^ h))
      ≈⟨ cright rearrange ⟩
    XC • ((S ↑ • (Z ↑) ^ h) • ((S • Z ^ h) • CZ))
      ≡⟨ Eq.sym (Eq.cong (λ w → XC • ((S ↑ • w) • ((S • Z ^ h) • CZ))) (lemma-↑^ h Z)) ⟩
    XC • (R ↑ • (R • CZ)) ∎
    where
    rearrange : (S ↑ • (S • CZ)) • ((Z ↑) ^ h • Z ^ h)
              ≈ (S ↑ • (Z ↑) ^ h) • ((S • Z ^ h) • CZ)
    rearrange = begin
      (S ↑ • (S • CZ)) • ((Z ↑) ^ h • Z ^ h)
        ≈⟨ assoc ⟩
      S ↑ • ((S • CZ) • ((Z ↑) ^ h • Z ^ h))
        ≈⟨ cright assoc ⟩
      S ↑ • (S • (CZ • ((Z ↑) ^ h • Z ^ h)))
        ≈⟨ cright cright sym assoc ⟩
      S ↑ • (S • ((CZ • (Z ↑) ^ h) • Z ^ h))
        ≈⟨ cright cright cleft comm⇒pow-comm 1 h lemma-comm-CZ-Z↑ ⟩
      S ↑ • (S • (((Z ↑) ^ h • CZ) • Z ^ h))
        ≈⟨ cright cright assoc ⟩
      S ↑ • (S • ((Z ↑) ^ h • (CZ • Z ^ h)))
        ≈⟨ cright cright cright comm⇒pow-comm 1 h lemma-comm-CZ-Z ⟩
      S ↑ • (S • ((Z ↑) ^ h • (Z ^ h • CZ)))
        ≈⟨ cright sym assoc ⟩
      S ↑ • ((S • (Z ↑) ^ h) • (Z ^ h • CZ))
        ≈⟨ cright cleft S-Z↑ʰ ⟩
      S ↑ • (((Z ↑) ^ h • S) • (Z ^ h • CZ))
        ≈⟨ cright assoc ⟩
      S ↑ • ((Z ↑) ^ h • (S • (Z ^ h • CZ)))
        ≈⟨ cright cright sym assoc ⟩
      S ↑ • ((Z ↑) ^ h • ((S • Z ^ h) • CZ))
        ≈⟨ sym assoc ⟩
      (S ↑ • (Z ↑) ^ h) • ((S • Z ^ h) • CZ) ∎

  ------------------------------------------------------------------------
  -- Selinger's c10
  --
  -- Both sides shed a leading H ↑ — the left by lemma-CZ-H↑, the right
  -- because R ↑ ⁻¹ • H ↑ • R ↑ ⁻¹ is H ↑ • R ↑ • H ↑ ⁻¹ by the Euler
  -- decomposition of the multiplier by −1 (lemma-M₋₁-R).  What is left is
  --
  --     XC • CZ ≈ R ↑ • XC • R ↑ ⁻¹ • R ↓ ⁻¹,
  --
  -- i.e. the conjugation rule lemma-comm-XC-R↑, with the CZ it emits
  -- surviving and the two R's cancelling the two inverse powers.

  private
    A₋ : Word (Gen (₂₊ n))
    A₋ = (R ↑) ^ p-1

    lemma-comm-CZ-R : CZ • R ≈ R • CZ
    lemma-comm-CZ-R = begin
      CZ • (S • Z ^ h)  ≈⟨ sym assoc ⟩
      (CZ • S) • Z ^ h  ≈⟨ cleft lemma-comm-CZ-S ⟩
      (S • CZ) • Z ^ h  ≈⟨ assoc ⟩
      S • (CZ • Z ^ h)  ≈⟨ cright comm⇒pow-comm 1 h lemma-comm-CZ-Z ⟩
      S • (Z ^ h • CZ)  ≈⟨ sym assoc ⟩
      (S • Z ^ h) • CZ ∎

    lemma-comm-CZ-R↑ : CZ • R ↑ ≈ R ↑ • CZ
    lemma-comm-CZ-R↑ = begin
      CZ • R ↑
        ≡⟨ Eq.cong (λ w → CZ • (S ↑ • w)) (lemma-↑^ h Z) ⟩
      CZ • (S ↑ • (Z ↑) ^ h)
        ≈⟨ sym assoc ⟩
      (CZ • S ↑) • (Z ↑) ^ h
        ≈⟨ cleft axiom comm-CZ-S↑ ⟩
      (S ↑ • CZ) • (Z ↑) ^ h
        ≈⟨ assoc ⟩
      S ↑ • (CZ • (Z ↑) ^ h)
        ≈⟨ cright comm⇒pow-comm 1 h lemma-comm-CZ-Z↑ ⟩
      S ↑ • ((Z ↑) ^ h • CZ)
        ≈⟨ sym assoc ⟩
      (S ↑ • (Z ↑) ^ h) • CZ
        ≡⟨ Eq.sym (Eq.cong (λ w → (S ↑ • w) • CZ) (lemma-↑^ h Z)) ⟩
      R ↑ • CZ ∎

    lemma-comm-R-w↑ : ∀ (w : Word (Gen (₁₊ n))) → R • w ↑ ≈ w ↑ • R
    lemma-comm-R-w↑ w = begin
      (S • Z ^ h) • w ↑  ≈⟨ assoc ⟩
      S • (Z ^ h • w ↑)  ≈⟨ cright lemma-Inductionˡ (lemma-comm-Z-w↑ w) h ⟩
      S • (w ↑ • Z ^ h)  ≈⟨ sym assoc ⟩
      (S • w ↑) • Z ^ h  ≈⟨ cleft lemma-comm-S-w↑ w ⟩
      (w ↑ • S) • Z ^ h  ≈⟨ assoc ⟩
      w ↑ • (S • Z ^ h) ∎

    R-A₋ : R • A₋ ≈ A₋ • R
    R-A₋ = begin
      R • A₋           ≡⟨ Eq.cong (R •_) (Eq.sym (lemma-↑^ p-1 R)) ⟩
      R • (R ^ p-1) ↑  ≈⟨ lemma-comm-R-w↑ (R ^ p-1) ⟩
      (R ^ p-1) ↑ • R  ≡⟨ Eq.cong (_• R) (lemma-↑^ p-1 R) ⟩
      A₋ • R ∎

    R↑-A₋ : R ↑ • A₋ ≈ ε
    R↑-A₋ = begin
      R ↑ • (R ↑) ^ p-1      ≈⟨ sym (^-+ (R ↑) 1 p-1) ⟩
      (R ↑) ^ (1 Nat.+ p-1)  ≡⟨ Eq.sym (lemma-↑^ p R) ⟩
      (R ^ p) ↑              ≈⟨ lemma-cong↑ _ _ (One-Wire.lemma-order-R n) ⟩
      ε ∎

    R-Rᵖ⁻¹ : R • R ^ p-1 ≈ ε
    R-Rᵖ⁻¹ = begin
      R • R ^ p-1        ≈⟨ sym (^-+ R 1 p-1) ⟩
      R ^ (1 Nat.+ p-1)  ≈⟨ One-Wire.lemma-order-R (₁₊ n) ⟩
      ε ∎

    euler↑ : A₋ • (H ↑ • (A₋ • (H ↑ • (A₋ • H ↑)))) ≈ (H ↑) ^ 2
    euler↑ = begin
      A₋ • (H ↑ • (A₋ • (H ↑ • (A₋ • H ↑))))
        ≡⟨ Eq.sym (Eq.cong (λ w → w • (H ↑ • (w • (H ↑ • (w • H ↑)))))
                           (lemma-↑^ p-1 R)) ⟩
      (R ^ p-1) ↑ • (H ↑ • ((R ^ p-1) ↑ • (H ↑ • ((R ^ p-1) ↑ • H ↑))))
        ≈⟨ lemma-cong↑ _ _ (One-Wire.lemma-M₋₁-R n) ⟩
      (H ↑) ^ 2 ∎

    -- The Euler decomposition, rearranged: conjugating H ↑ by R ↑ ⁻¹ the
    -- one way is conjugating R ↑ by H ↑ the other.
    lemma-ABA : A₋ • (H ↑ • A₋) ≈ H ↑ • (R ↑ • (H ↑) ^ 3)
    lemma-ABA = •-cancelʳ {h = H ↑ • (A₋ • H ↑)} (trans left-half (sym right-half))
      where
      -- Both sides, multiplied by H ↑ • (A₋ • H ↑), come to H ↑ ^ 2:
      -- the left by the Euler decomposition itself, the right because
      -- the two H ↑ powers and the two R ↑ powers each cancel.
      left-half : (A₋ • (H ↑ • A₋)) • (H ↑ • (A₋ • H ↑)) ≈ (H ↑) ^ 2
      left-half = begin
        (A₋ • (H ↑ • A₋)) • (H ↑ • (A₋ • H ↑))
          ≈⟨ assoc ⟩
        A₋ • ((H ↑ • A₋) • (H ↑ • (A₋ • H ↑)))
          ≈⟨ cright assoc ⟩
        A₋ • (H ↑ • (A₋ • (H ↑ • (A₋ • H ↑))))
          ≈⟨ euler↑ ⟩
        (H ↑) ^ 2 ∎

      right-half : (H ↑ • (R ↑ • (H ↑) ^ 3)) • (H ↑ • (A₋ • H ↑)) ≈ (H ↑) ^ 2
      right-half = begin
        (H ↑ • (R ↑ • (H ↑) ^ 3)) • (H ↑ • (A₋ • H ↑))
          ≈⟨ assoc ⟩
        H ↑ • ((R ↑ • (H ↑) ^ 3) • (H ↑ • (A₋ • H ↑)))
          ≈⟨ cright assoc ⟩
        H ↑ • (R ↑ • ((H ↑) ^ 3 • (H ↑ • (A₋ • H ↑))))
          ≈⟨ cright cright sym assoc ⟩
        H ↑ • (R ↑ • (((H ↑) ^ 3 • H ↑) • (A₋ • H ↑)))
          ≈⟨ cright cright cleft H↑³H↑ ⟩
        H ↑ • (R ↑ • (ε • (A₋ • H ↑)))
          ≈⟨ cright cright left-unit ⟩
        H ↑ • (R ↑ • (A₋ • H ↑))
          ≈⟨ cright sym assoc ⟩
        H ↑ • ((R ↑ • A₋) • H ↑)
          ≈⟨ cright cleft R↑-A₋ ⟩
        H ↑ • (ε • H ↑)
          ≈⟨ cright left-unit ⟩
        H ↑ • H ↑ ∎

  lemma-selinger-c10 :
    CZ • H ↑ • CZ ≈ R ↑ ^ p-1 • H ↑ • R ↑ ^ p-1 • CZ • H ↑ • R ↑ ^ p-1 • R ↓ ^ p-1
  lemma-selinger-c10 = sym (begin
    A₋ • (H ↑ • (A₋ • (CZ • (H ↑ • (A₋ • R ^ p-1)))))
      ≈⟨ cright sym assoc ⟩
    A₋ • ((H ↑ • A₋) • (CZ • (H ↑ • (A₋ • R ^ p-1))))
      ≈⟨ sym assoc ⟩
    (A₋ • (H ↑ • A₋)) • (CZ • (H ↑ • (A₋ • R ^ p-1)))
      ≈⟨ cleft lemma-ABA ⟩
    (H ↑ • (R ↑ • (H ↑) ^ 3)) • (CZ • (H ↑ • (A₋ • R ^ p-1)))
      ≈⟨ assoc ⟩
    H ↑ • ((R ↑ • (H ↑) ^ 3) • (CZ • (H ↑ • (A₋ • R ^ p-1))))
      ≈⟨ cright assoc ⟩
    H ↑ • (R ↑ • ((H ↑) ^ 3 • (CZ • (H ↑ • (A₋ • R ^ p-1)))))
      ≈⟨ cright cright cright sym assoc ⟩
    H ↑ • (R ↑ • ((H ↑) ^ 3 • ((CZ • H ↑) • (A₋ • R ^ p-1))))
      ≈⟨ cright cright sym assoc ⟩
    H ↑ • (R ↑ • (((H ↑) ^ 3 • (CZ • H ↑)) • (A₋ • R ^ p-1)))
      ≈⟨ cright sym assoc ⟩
    H ↑ • ((R ↑ • XC) • (A₋ • R ^ p-1))
      ≈⟨ cright cleft lemma-comm-XC-R↑ ⟩
    H ↑ • ((XC • (R ↑ • (R • CZ))) • (A₋ • R ^ p-1))
      ≈⟨ cright assoc ⟩
    H ↑ • (XC • ((R ↑ • (R • CZ)) • (A₋ • R ^ p-1)))
      ≈⟨ cright cright collapse ⟩
    H ↑ • (XC • CZ)
      ≈⟨ sym assoc ⟩
    (H ↑ • XC) • CZ
      ≈⟨ cleft sym lemma-CZ-H↑ ⟩
    (CZ • H ↑) • CZ
      ≈⟨ assoc ⟩
    CZ • (H ↑ • CZ) ∎)
    where
    collapse : (R ↑ • (R • CZ)) • (A₋ • R ^ p-1) ≈ CZ
    collapse = begin
      (R ↑ • (R • CZ)) • (A₋ • R ^ p-1)
        ≈⟨ assoc ⟩
      R ↑ • ((R • CZ) • (A₋ • R ^ p-1))
        ≈⟨ cright assoc ⟩
      R ↑ • (R • (CZ • (A₋ • R ^ p-1)))
        ≈⟨ cright cright sym assoc ⟩
      R ↑ • (R • ((CZ • A₋) • R ^ p-1))
        ≈⟨ cright cright cleft comm⇒pow-comm 1 p-1 lemma-comm-CZ-R↑ ⟩
      R ↑ • (R • ((A₋ • CZ) • R ^ p-1))
        ≈⟨ cright cright assoc ⟩
      R ↑ • (R • (A₋ • (CZ • R ^ p-1)))
        ≈⟨ cright cright cright comm⇒pow-comm 1 p-1 lemma-comm-CZ-R ⟩
      R ↑ • (R • (A₋ • (R ^ p-1 • CZ)))
        ≈⟨ cright sym assoc ⟩
      R ↑ • ((R • A₋) • (R ^ p-1 • CZ))
        ≈⟨ cright cleft R-A₋ ⟩
      R ↑ • ((A₋ • R) • (R ^ p-1 • CZ))
        ≈⟨ cright assoc ⟩
      R ↑ • (A₋ • (R • (R ^ p-1 • CZ)))
        ≈⟨ sym assoc ⟩
      (R ↑ • A₋) • (R • (R ^ p-1 • CZ))
        ≈⟨ cleft R↑-A₋ ⟩
      ε • (R • (R ^ p-1 • CZ))
        ≈⟨ left-unit ⟩
      R • (R ^ p-1 • CZ)
        ≈⟨ sym assoc ⟩
      (R • R ^ p-1) • CZ
        ≈⟨ cleft R-Rᵖ⁻¹ ⟩
      ε • CZ
        ≈⟨ left-unit ⟩
      CZ ∎

  ------------------------------------------------------------------------
  -- Selinger's c11, by conjugating c10 with the swap
  --
  -- Ex exchanges the two wires and fixes CZ, so it carries each factor of
  -- c10 to the corresponding factor of c11.  Nothing is reproved here:
  -- the statement is transported, factor by factor, by lemma-Ex-•.

  private
    transport-Ex : ∀ {u u' v v'} →
                   Ex • u ≈ u' • Ex → Ex • v ≈ v' • Ex → u ≈ v → u' ≈ v'
    transport-Ex {u} {u'} {v} {v'} eu ev eq = begin
      u'              ≈⟨ sym lemma-cancel-Ex ⟩
      u' • Ex • Ex    ≈⟨ sym assoc ⟩
      (u' • Ex) • Ex  ≈⟨ cleft sym eu ⟩
      (Ex • u) • Ex   ≈⟨ cleft cright eq ⟩
      (Ex • v) • Ex   ≈⟨ cleft ev ⟩
      (v' • Ex) • Ex  ≈⟨ assoc ⟩
      v' • Ex • Ex    ≈⟨ lemma-cancel-Ex ⟩
      v' ∎

  lemma-selinger-c11 :
    CZ • H ↓ • CZ ≈ R ↓ ^ p-1 • H ↓ • R ↓ ^ p-1 • CZ • H ↓ • R ↓ ^ p-1 • R ↑ ^ p-1
  lemma-selinger-c11 = transport-Ex lhs rhs lemma-selinger-c10
    where
    lhs : Ex • (CZ • (H ↑ • CZ)) ≈ (CZ • (H • CZ)) • Ex
    lhs = lemma-Ex-• lemma-Ex-CZ (lemma-Ex-• lemma-Ex-H↑ lemma-Ex-CZ)

    rhs : Ex • (A₋ • (H ↑ • (A₋ • (CZ • (H ↑ • (A₋ • R ^ p-1))))))
        ≈ (R ^ p-1 • (H • (R ^ p-1 • (CZ • (H • (R ^ p-1 • A₋)))))) • Ex
    rhs = lemma-Ex-• (lemma-Ex-pow lemma-Ex-R↑ p-1)
            (lemma-Ex-• lemma-Ex-H↑
              (lemma-Ex-• (lemma-Ex-pow lemma-Ex-R↑ p-1)
                (lemma-Ex-• lemma-Ex-CZ
                  (lemma-Ex-• lemma-Ex-H↑
                    (lemma-Ex-• (lemma-Ex-pow lemma-Ex-R↑ p-1)
                                (lemma-Ex-pow lemma-Ex-R p-1))))))

  lemma-⊤⊥-cube3 : (⊤⊥ • ⊤⊥) • ⊤⊥ ≈ ε
  lemma-⊤⊥-cube3 = begin
    (⊤⊥ • ⊤⊥) • ⊤⊥
      ≈⟨ cong (cong lemma-⊤⊥-simple lemma-⊤⊥-simple) lemma-⊤⊥-simple ⟩
    ((ₕ|ₕ • Ex) • (ₕ|ₕ • Ex)) • (ₕ|ₕ • Ex)
      ≈⟨ lemma-half-swap-cube ⟩
    ε ∎


------------------------------------------------------------------------
-- The two Simplified-V1 axioms that Paper-V0 lacked
--
-- Both are the ↑-rule conjugated by the swap.  The ↓ that Simplified-V1
-- writes on them needs no stepping over: _↓ is the identity function on
-- circuits (Circuit.Base), a wire-count annotation and nothing more, so
-- Mg ↓ and Mg are the same term.  (A `Down-Identity` module used to sit
-- here proving that ↓ commutes with the derived words; every one of its
-- equations was refl, and it is gone.)

module Down-Rules (n : ℕ) where

  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Ex-Conjugation n

  lemma-comm-CZ-S↓ : CZ • S ↓ ≈ S ↓ • CZ
  lemma-comm-CZ-S↓ = lemma-comm-CZ-S

  lemma-semi-M↓CZ : Mg ↓ • CZ ≈ CZ^ g • Mg ↓
  lemma-semi-M↓CZ = lemma-semi-Mg-CZ

------------------------------------------------------------------------
-- The remote CZ, at three wires
--
-- CZ02 is *defined* as Ex • CZ ↑ • Ex — the CZ on wires 1-2 carried onto
-- wires 0-2 by the swap of wires 0-1 — so conjugation facts about it are
-- definitional, and its order follows from the order of CZ.
--
-- This is the correction term of the paper's C18
-- (semi-CX↑-CZ↓ : CX ↑ • CZ ↓ === CZ ↓ • CZ02 • CX ↑): CX ↑ retargets
-- wire 1, which is what a CZ on wires 0-1 reads, so pushing that CZ
-- through picks up a CZ on wires 0-2.  Deriving selinger-c12 turns on
-- those corrections cancelling, and they cancel because CX ↑ occurs in
-- the C6-expansion of a CZ with total exponent 1 + (p-1) = p, leaving
-- CZ02 ^ p ≈ ε.

module Three-Wire (n : ℕ) where

  open PB ((₃₊ n) QRel,_===_)
  open PP ((₃₊ n) QRel,_===_)
  open SR word-setoid
  open Ex-Conjugation (₁₊ n)

  -- The relation one wire down, for the arguments of lemma-cong↑.
  private module PB₂ = PB ((₂₊ n) QRel,_===_)

  open Group-Lemmas ((₃₊ n) QRel,_===_) (Paper-GroupLike.grouplike {₃₊ n})
    using (•-cancelʳ ; •-cancelˡ)

  -- CZ on the upper pair has order p, inherited from order-CZ one wire
  -- down.  (ε ↑ is ε definitionally, so the shift leaves no residue.)
  lemma-order-CZ↑ : (CZ ↑) ^ p ≈ ε
  lemma-order-CZ↑ = begin
    (CZ ↑) ^ p  ≈⟨ refl' (Eq.sym (lemma-↑^ p CZ)) ⟩
    (CZ ^ p) ↑  ≈⟨ lemma-cong↑ _ _ (PB₂.axiom order-CZ) ⟩
    ε ∎

  -- Conjugation commutes with powers.  Stated over an arbitrary u so it
  -- serves CZ02 and anything else conjugated by the swap.
  lemma-conj-pow : ∀ (u : Word (Gen (₃₊ n))) k →
                   (Ex • (u • Ex)) ^ k ≈ Ex • (u ^ k • Ex)
  lemma-conj-pow u ₀ = begin
    ε              ≈⟨ sym lemma-Ex-Ex ⟩
    Ex • Ex        ≈⟨ cright sym left-unit ⟩
    Ex • (ε • Ex) ∎
  lemma-conj-pow u ₁ = refl
  lemma-conj-pow u (₂₊ k) = begin
    (Ex • (u • Ex)) • (Ex • (u • Ex)) ^ ₁₊ k
      ≈⟨ cright lemma-conj-pow u (₁₊ k) ⟩
    (Ex • (u • Ex)) • (Ex • (u ^ ₁₊ k • Ex))
      ≈⟨ assoc ⟩
    Ex • ((u • Ex) • (Ex • (u ^ ₁₊ k • Ex)))
      ≈⟨ cright assoc ⟩
    Ex • (u • (Ex • (Ex • (u ^ ₁₊ k • Ex))))
      ≈⟨ cright cright sym assoc ⟩
    Ex • (u • ((Ex • Ex) • (u ^ ₁₊ k • Ex)))
      ≈⟨ cright cright cleft lemma-Ex-Ex ⟩
    Ex • (u • (ε • (u ^ ₁₊ k • Ex)))
      ≈⟨ cright cright left-unit ⟩
    Ex • (u • (u ^ ₁₊ k • Ex))
      ≈⟨ cright sym assoc ⟩
    Ex • ((u • u ^ ₁₊ k) • Ex) ∎

  -- The remote CZ has order p as well: p copies of it are p copies of
  -- CZ ↑ with the two swaps cancelling.
  lemma-order-CZ02 : CZ02 ^ p ≈ ε
  lemma-order-CZ02 = begin
    CZ02 ^ p                ≈⟨ lemma-conj-pow (CZ ↑) p ⟩
    Ex • ((CZ ↑) ^ p • Ex)  ≈⟨ cright cleft lemma-order-CZ↑ ⟩
    Ex • (ε • Ex)           ≈⟨ cright left-unit ⟩
    Ex • Ex                 ≈⟨ lemma-Ex-Ex ⟩
    ε ∎

  ------------------------------------------------------------------------
  -- The multiplier commutes with anything on the wires above it
  --
  -- Mg is a product of powers of S, H and Z on wire 0, and each of those
  -- commutes with a shifted word; the two combinators below lift that
  -- through the products and powers Mg is built from.  Taking w = CX
  -- gives what the rescaled C18 needs.

  private
    comm-• : ∀ {u v} {w : Word (Gen (₂₊ n))} →
             u • w ↑ ≈ w ↑ • u → v • w ↑ ≈ w ↑ • v →
             (u • v) • w ↑ ≈ w ↑ • (u • v)
    comm-• {u} {v} {w} cu cv = begin
      (u • v) • w ↑  ≈⟨ assoc ⟩
      u • (v • w ↑)  ≈⟨ cright cv ⟩
      u • (w ↑ • v)  ≈⟨ sym assoc ⟩
      (u • w ↑) • v  ≈⟨ cleft cu ⟩
      (w ↑ • u) • v  ≈⟨ assoc ⟩
      w ↑ • (u • v) ∎

    comm-pow : ∀ {u} {w : Word (Gen (₂₊ n))} →
               u • w ↑ ≈ w ↑ • u → ∀ k → u ^ k • w ↑ ≈ w ↑ • u ^ k
    comm-pow cu ₀      = trans left-unit (sym right-unit)
    comm-pow cu ₁      = cu
    comm-pow cu (₂₊ k) = comm-• cu (comm-pow cu (₁₊ k))

  lemma-Mg-w↑ : ∀ (w : Word (Gen (₂₊ n))) → Mg • w ↑ ≈ w ↑ • Mg
  lemma-Mg-w↑ w =
    comm-• cR^ (comm-• cH (comm-• cR^' (comm-• cH (comm-• cR^ cH))))
    where
    cH = lemma-comm-H-w↑ w
    cZ^ = comm-pow (lemma-comm-Z-w↑ w) (toℕ 1/2)
    cR  = comm-• (lemma-comm-S-w↑ w) cZ^
    cR^ = comm-pow cR (toℕ g)
    cR^' = comm-pow cR (toℕ ((g′ ⁻¹) .proj₁))

  lemma-Mg-CX↑ : Mg • CX ↑ ≈ CX ↑ • Mg
  lemma-Mg-CX↑ = lemma-Mg-w↑ CX

  ------------------------------------------------------------------------
  -- The multiplier on wire 0 rescales the remote CZ too
  --
  -- CZ02 is Ex • CZ ↑ • Ex, so the multiplier passes onto the upper wire
  -- with the swap, rescales there against CZ ↑, and comes back; the
  -- power is carried through the swap by lemma-conj-pow.

  private
    -- semi-M↓CZ one wire up: Mg on wire 1 against CZ on wires 1-2.
    -- The instance one wire down, so that cong↑ lands at this width.
    semi↑ : Mg ↑ • CZ ↑ ≈ (CZ ↑) ^ toℕ g • Mg ↑
    semi↑ = trans (lemma-cong↑ _ _ (Ex-Conjugation.lemma-semi-Mg-CZ n))
                  (refl' (Eq.cong (_• Mg ↑) (lemma-↑^ (toℕ g) CZ)))

    -- The swap carries the multiplier from wire 1 down to wire 0.
    mg↑Ex : Mg ↑ • Ex ≈ Ex • Mg
    mg↑Ex = begin
      Mg ↑ • Ex               ≈⟨ sym left-unit ⟩
      ε • (Mg ↑ • Ex)         ≈⟨ cleft sym lemma-Ex-Ex ⟩
      (Ex • Ex) • (Mg ↑ • Ex) ≈⟨ assoc ⟩
      Ex • (Ex • (Mg ↑ • Ex)) ≈⟨ cright lemma-conj-Ex-Mg↑ ⟩
      Ex • Mg ∎

  lemma-Mg-CZ02 : Mg • CZ02 ≈ CZ02 ^ toℕ g • Mg
  lemma-Mg-CZ02 = begin
    Mg • (Ex • (CZ ↑ • Ex))
      ≈⟨ sym assoc ⟩
    (Mg • Ex) • (CZ ↑ • Ex)
      ≈⟨ cleft sym lemma-Ex-Mg↑ ⟩
    (Ex • Mg ↑) • (CZ ↑ • Ex)
      ≈⟨ assoc ⟩
    Ex • (Mg ↑ • (CZ ↑ • Ex))
      ≈⟨ cright sym assoc ⟩
    Ex • ((Mg ↑ • CZ ↑) • Ex)
      ≈⟨ cright cleft semi↑ ⟩
    Ex • (((CZ ↑) ^ toℕ g • Mg ↑) • Ex)
      ≈⟨ cright assoc ⟩
    Ex • ((CZ ↑) ^ toℕ g • (Mg ↑ • Ex))
      ≈⟨ cright cright mg↑Ex ⟩
    Ex • ((CZ ↑) ^ toℕ g • (Ex • Mg))
      ≈⟨ cright sym assoc ⟩
    Ex • (((CZ ↑) ^ toℕ g • Ex) • Mg)
      ≈⟨ sym assoc ⟩
    (Ex • ((CZ ↑) ^ toℕ g • Ex)) • Mg
      ≈⟨ cleft sym (lemma-conj-pow (CZ ↑) (toℕ g)) ⟩
    CZ02 ^ toℕ g • Mg ∎

  ------------------------------------------------------------------------
  -- Iterating the multiplier: from the fixed generator to any unit
  --
  -- Mg ^ j rescales by g ^′ j.  The induction costs only associativity,
  -- because x ^′ (suc k) is x * (x ^′ k) definitionally; the ₀/₁/₂₊ split
  -- is forced by w ^ 1 being w rather than w • w ^ 0.

  ------------------------------------------------------------------------
  -- The transposition of wires 0 and 2
  --
  -- Ex swaps wires 0-1 and Ex ↑ swaps 1-2, so Ex • Ex ↑ • Ex transposes
  -- 0 and 2.  It carries CZ (wires 0-1) to CZ ↑ (wires 1-2), which is the
  -- transport between the progress report's form of C15 —
  -- CZ₁₂ • CZ₀₂ = CZ₀₂ • CZ₁₂, stated "up to qubit wire permutation" —
  -- and selinger-c12 as Simplified-V1 states it.  It is also the mirror
  -- that exchanges c14 and c15, since it swaps ⊤⊥ ↑ with ⊥⊤ as well.
  --
  -- Note Ex ↓ is Ex definitionally: _↓ maps every gate to itself and Ex
  -- is a word of gate letters with no symbolic power, so cz-slide can be
  -- used against Ex directly.

  ------------------------------------------------------------------------
  -- Iterating C18
  --
  -- Each CZ pushed leftwards through CX ↑ leaves a CZ02 behind, so a
  -- power of CZ leaves the alternating product (CZ • CZ02) ^ k.  No
  -- commutation between CZ and CZ02 is assumed — the two stay
  -- interleaved, which is the whole point: comparing this against the
  -- multiplier-rescaled form of the same word is what proves they
  -- commute.

  -- C18 read with CX ↑ on the left of the CZ.  The axiom as stated emits
  -- its CZ02 on the far left when a CZ crosses CX ↑ leftwards; read the
  -- other way it emits CZ02 ⁻¹, and it is that form the iteration needs,
  -- because the emitted factor lands outside CX ↑ and so does not block
  -- the next step.  (The axiom used to be stated in circuit order, which
  -- is the reverse of Word order; this is the same relation read the
  -- right way round.)

  private
    CZ02⁻ : Word (Gen (₃₊ n))
    CZ02⁻ = CZ02 ^ p-1

    lemma-CZ02-CZ02⁻ : CZ02 • CZ02⁻ ≈ ε
    lemma-CZ02-CZ02⁻ = begin
      CZ02 • CZ02 ^ p-1     ≈⟨ sym (^-+ CZ02 1 p-1) ⟩
      CZ02 ^ (1 Nat.+ p-1)  ≈⟨ lemma-order-CZ02 ⟩
      ε ∎

  lemma-C18' : CX ↑ • CZ ≈ (CZ02⁻ • CZ) • CX ↑
  lemma-C18' = •-cancelˡ {g = CZ02} (begin
    CZ02 • (CX ↑ • CZ)
      ≈⟨ sym (axiom semi-CX↑-CZ↓) ⟩
    CZ • CX ↑
      ≈⟨ cleft sym left-unit ⟩
    (ε • CZ) • CX ↑
      ≈⟨ cleft cleft sym lemma-CZ02-CZ02⁻ ⟩
    ((CZ02 • CZ02⁻) • CZ) • CX ↑
      ≈⟨ cleft assoc ⟩
    (CZ02 • (CZ02⁻ • CZ)) • CX ↑
      ≈⟨ assoc ⟩
    CZ02 • ((CZ02⁻ • CZ) • CX ↑) ∎)

  lemma-C18ᵏ : ∀ k → CX ↑ • CZ ^ k ≈ (CZ02⁻ • CZ) ^ k • CX ↑
  lemma-C18ᵏ ₀ = trans right-unit (sym left-unit)
  lemma-C18ᵏ ₁ = lemma-C18'
  lemma-C18ᵏ (₂₊ k) = begin
    CX ↑ • (CZ • CZ ^ ₁₊ k)
      ≈⟨ sym assoc ⟩
    (CX ↑ • CZ) • CZ ^ ₁₊ k
      ≈⟨ cleft lemma-C18' ⟩
    ((CZ02⁻ • CZ) • CX ↑) • CZ ^ ₁₊ k
      ≈⟨ assoc ⟩
    (CZ02⁻ • CZ) • (CX ↑ • CZ ^ ₁₊ k)
      ≈⟨ cright lemma-C18ᵏ (₁₊ k) ⟩
    (CZ02⁻ • CZ) • ((CZ02⁻ • CZ) ^ ₁₊ k • CX ↑)
      ≈⟨ sym assoc ⟩
    ((CZ02⁻ • CZ) • (CZ02⁻ • CZ) ^ ₁₊ k) • CX ↑ ∎

  ------------------------------------------------------------------------
  -- The alternating product has order p as well
  --
  -- CX ↑ • CZ ^ p is CX ↑ on the nose, so lemma-C18ᵏ at p says
  -- (CZ02 ⁻¹ • CZ) ^ p • CX ↑ is too, and CX ↑ cancels on the right.

  lemma-order-CZ·CZ02 : (CZ02⁻ • CZ) ^ p ≈ ε
  lemma-order-CZ·CZ02 = •-cancelʳ {h = CX ↑} (begin
    (CZ02⁻ • CZ) ^ p • CX ↑ ≈⟨ sym (lemma-C18ᵏ p) ⟩
    CX ↑ • CZ ^ p           ≈⟨ cright axiom order-CZ ⟩
    CX ↑ • ε                ≈⟨ right-unit ⟩
    CX ↑                    ≈⟨ sym left-unit ⟩
    ε • CX ↑ ∎)

  ------------------------------------------------------------------------
  -- The rescaled C18, and the exponent identity it forces
  --
  -- Conjugating C18 by Mg ^ j — which commutes with CX ↑ and rescales
  -- both CZ and CZ02 by g ^′ j — gives (A).  Comparing it against the
  -- interleaved form (B) of lemma-C18ᵏ at the same exponent, and
  -- cancelling CX ↑, leaves (C): the two CZs distribute over that power.

  lemma-Mg-CZ02^ : ∀ (a : ℤ ₚ) → Mg • CZ02 ^ toℕ a ≈ CZ02 ^ toℕ (g * a) • Mg
  lemma-Mg-CZ02^ a = begin
    Mg • CZ02 ^ toℕ a
      ≈⟨ lemma-Induction lemma-Mg-CZ02 (toℕ a) ⟩
    (CZ02 ^ toℕ g) ^ toℕ a • Mg
      ≈⟨ cleft (^^ CZ02 (toℕ g) (toℕ a)) ⟩
    CZ02 ^ (toℕ g Nat.* toℕ a) • Mg
      ≈⟨ cleft (lemma-pow-mod lemma-order-CZ02 (toℕ g Nat.* toℕ a)) ⟩
    CZ02 ^ ((toℕ g Nat.* toℕ a) Nat.% p) • Mg
      ≈⟨ cleft refl' (Eq.cong (CZ02 ^_) (lemma-toℕ-% g a)) ⟩
    CZ02 ^ toℕ (g * a) • Mg ∎

  lemma-Mgᵏ-CZ02 : ∀ j → Mg ^ j • CZ02 ≈ CZ02 ^ toℕ (g ^′ j) • Mg ^ j
  lemma-Mgᵏ-CZ02 ₀ = begin
    ε • CZ02  ≈⟨ left-unit ⟩
    CZ02      ≈⟨ sym right-unit ⟩
    CZ02 • ε ∎
  lemma-Mgᵏ-CZ02 ₁ = begin
    Mg • CZ02             ≈⟨ lemma-Mg-CZ02 ⟩
    CZ02 ^ toℕ g • Mg
      ≡⟨ Eq.cong (λ z → CZ02 ^ toℕ z • Mg) (Eq.sym (lemma-x^′1=x g)) ⟩
    CZ02 ^ toℕ (g ^′ 1) • Mg ∎
  lemma-Mgᵏ-CZ02 (₂₊ j) = begin
    (Mg • Mg ^ ₁₊ j) • CZ02
      ≈⟨ assoc ⟩
    Mg • (Mg ^ ₁₊ j • CZ02)
      ≈⟨ cright lemma-Mgᵏ-CZ02 (₁₊ j) ⟩
    Mg • (CZ02 ^ toℕ (g ^′ ₁₊ j) • Mg ^ ₁₊ j)
      ≈⟨ sym assoc ⟩
    (Mg • CZ02 ^ toℕ (g ^′ ₁₊ j)) • Mg ^ ₁₊ j
      ≈⟨ cleft lemma-Mg-CZ02^ (g ^′ ₁₊ j) ⟩
    (CZ02 ^ toℕ (g * (g ^′ ₁₊ j)) • Mg) • Mg ^ ₁₊ j
      ≈⟨ assoc ⟩
    CZ02 ^ toℕ (g * (g ^′ ₁₊ j)) • (Mg • Mg ^ ₁₊ j) ∎

  lemma-Mgᵏ-CX↑ : ∀ j → Mg ^ j • CX ↑ ≈ CX ↑ • Mg ^ j
  lemma-Mgᵏ-CX↑ = comm-pow lemma-Mg-CX↑

  -- (A): C18 with every CZ exponent rescaled by g ^′ j.  The multiplier
  -- rescales the emitted CZ02 ⁻¹ too, so its exponent picks up the same
  -- factor: CZ02 ^ (p-1) becomes CZ02 ^ ((p-1) * e).
  lemma-A : ∀ j → let e = toℕ (g ^′ j) in
            CX ↑ • CZ ^ e ≈ (CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • CX ↑
  lemma-A j = •-cancelʳ {h = Mg ^ j} (begin
    (CX ↑ • CZ ^ e) • Mg ^ j
      ≈⟨ assoc ⟩
    CX ↑ • (CZ ^ e • Mg ^ j)
      ≈⟨ cright sym (lemma-Mgᵏ-CZ j) ⟩
    CX ↑ • (Mg ^ j • CZ)
      ≈⟨ sym assoc ⟩
    (CX ↑ • Mg ^ j) • CZ
      ≈⟨ cleft sym (lemma-Mgᵏ-CX↑ j) ⟩
    (Mg ^ j • CX ↑) • CZ
      ≈⟨ assoc ⟩
    Mg ^ j • (CX ↑ • CZ)
      ≈⟨ cright lemma-C18' ⟩
    Mg ^ j • ((CZ02⁻ • CZ) • CX ↑)
      ≈⟨ sym assoc ⟩
    (Mg ^ j • (CZ02⁻ • CZ)) • CX ↑
      ≈⟨ cleft sym assoc ⟩
    ((Mg ^ j • CZ02⁻) • CZ) • CX ↑
      ≈⟨ cleft cleft rescale ⟩
    ((CZ02 ^ (p-1 Nat.* e) • Mg ^ j) • CZ) • CX ↑
      ≈⟨ cleft assoc ⟩
    (CZ02 ^ (p-1 Nat.* e) • (Mg ^ j • CZ)) • CX ↑
      ≈⟨ cleft cright (lemma-Mgᵏ-CZ j) ⟩
    (CZ02 ^ (p-1 Nat.* e) • (CZ ^ e • Mg ^ j)) • CX ↑
      ≈⟨ cleft sym assoc ⟩
    ((CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • Mg ^ j) • CX ↑
      ≈⟨ assoc ⟩
    (CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • (Mg ^ j • CX ↑)
      ≈⟨ cright (lemma-Mgᵏ-CX↑ j) ⟩
    (CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • (CX ↑ • Mg ^ j)
      ≈⟨ sym assoc ⟩
    ((CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • CX ↑) • Mg ^ j ∎)
    where
    e = toℕ (g ^′ j)
    rescale : Mg ^ j • CZ02⁻ ≈ CZ02 ^ (p-1 Nat.* e) • Mg ^ j
    rescale = begin
      Mg ^ j • CZ02 ^ p-1
        ≈⟨ lemma-Induction (lemma-Mgᵏ-CZ02 j) p-1 ⟩
      (CZ02 ^ e) ^ p-1 • Mg ^ j
        ≈⟨ cleft (^^ CZ02 e p-1) ⟩
      CZ02 ^ (e Nat.* p-1) • Mg ^ j
        ≡⟨ Eq.cong (λ m → CZ02 ^ m • Mg ^ j) (NP.*-comm e p-1) ⟩
      CZ02 ^ (p-1 Nat.* e) • Mg ^ j ∎

  -- (C): the two CZs distribute over the rescaled power.
  lemma-C : ∀ j → let e = toℕ (g ^′ j) in
            (CZ02⁻ • CZ) ^ e ≈ CZ02 ^ (p-1 Nat.* e) • CZ ^ e
  lemma-C j = •-cancelʳ {h = CX ↑} (begin
    (CZ02⁻ • CZ) ^ e • CX ↑                 ≈⟨ sym (lemma-C18ᵏ e) ⟩
    CX ↑ • CZ ^ e                           ≈⟨ lemma-A j ⟩
    (CZ02 ^ (p-1 Nat.* e) • CZ ^ e) • CX ↑ ∎)
    where e = toℕ (g ^′ j)

  ------------------------------------------------------------------------
  -- The two CZs sharing a wire commute
  --
  -- This is the progress report's C15, its Lemma 9.  Since g generates
  -- the units, some power of it is 2, and (C) at that exponent reads
  --
  --     (CZ • CZ02) • (CZ • CZ02)  ≈  (CZ • CZ) • (CZ02 • CZ02)
  --
  -- Cancelling a CZ on the left and a CZ02 on the right is the whole of
  -- the rest.  Nothing here is circular: the multiplier rescaling is an
  -- input from outside the CZ/CZ02 family, which is exactly why the
  -- report inserts M₂ • M½.

  private
    ₂ᵤ : ℤ* ₚ
    ₂ᵤ = (2ₚ , λ ())
      where
      2ₚ : ℤ ₚ
      2ₚ = ₂

    -- The power of g that is 2.
    j₂ : ℕ
    j₂ = toℕ (g-gen ₂ᵤ .proj₁)

    e₂ : toℕ (g ^′ j₂) ≡ 2
    e₂ = Eq.cong toℕ (Eq.sym (g-gen ₂ᵤ .proj₂))

    -- (C) with the exponent evaluated.
    lemma-C₂ : (CZ02⁻ • CZ) • (CZ02⁻ • CZ) ≈ (CZ02⁻ • CZ02⁻) • (CZ • CZ)
    lemma-C₂ = begin
      (CZ02⁻ • CZ) • (CZ02⁻ • CZ)
        ≡⟨ Eq.cong ((CZ02⁻ • CZ) ^_) (Eq.sym e₂) ⟩
      (CZ02⁻ • CZ) ^ toℕ (g ^′ j₂)
        ≈⟨ lemma-C j₂ ⟩
      CZ02 ^ (p-1 Nat.* toℕ (g ^′ j₂)) • CZ ^ toℕ (g ^′ j₂)
        ≡⟨ Eq.cong₂ (λ a b → CZ02 ^ (p-1 Nat.* a) • CZ ^ b) e₂ e₂ ⟩
      CZ02 ^ (p-1 Nat.* 2) • (CZ • CZ)
        ≈⟨ cleft sym (^^ CZ02 p-1 2) ⟩
      (CZ02⁻ • CZ02⁻) • (CZ • CZ) ∎

    -- Cancelling one CZ02 ⁻¹ on the left and one CZ on the right.  All
    -- explicit assoc: CZ02 ⁻¹ is a symbolic power, so to-list is stuck.
    lemma-comm-CZ-CZ02⁻ : CZ • CZ02⁻ ≈ CZ02⁻ • CZ
    lemma-comm-CZ-CZ02⁻ =
      •-cancelˡ {g = CZ02⁻} (•-cancelʳ {h = CZ} (begin
        (CZ02⁻ • (CZ • CZ02⁻)) • CZ
          ≈⟨ cleft sym assoc ⟩
        ((CZ02⁻ • CZ) • CZ02⁻) • CZ
          ≈⟨ assoc ⟩
        (CZ02⁻ • CZ) • (CZ02⁻ • CZ)
          ≈⟨ lemma-C₂ ⟩
        (CZ02⁻ • CZ02⁻) • (CZ • CZ)
          ≈⟨ assoc ⟩
        CZ02⁻ • (CZ02⁻ • (CZ • CZ))
          ≈⟨ cright sym assoc ⟩
        CZ02⁻ • ((CZ02⁻ • CZ) • CZ)
          ≈⟨ sym assoc ⟩
        (CZ02⁻ • (CZ02⁻ • CZ)) • CZ ∎))

    lemma-CZ02⁻-CZ02 : CZ02⁻ • CZ02 ≈ ε
    lemma-CZ02⁻-CZ02 = begin
      CZ02 ^ p-1 • CZ02
        ≈⟨ sym (^-+ CZ02 p-1 1) ⟩
      CZ02 ^ (p-1 Nat.+ 1)
        ≡⟨ Eq.cong (CZ02 ^_) (NP.+-comm p-1 1) ⟩
      CZ02 ^ (1 Nat.+ p-1)
        ≈⟨ lemma-order-CZ02 ⟩
      ε ∎

  -- CZ commutes with CZ02 ⁻¹, hence with CZ02.
  lemma-comm-CZ-CZ02 : CZ • CZ02 ≈ CZ02 • CZ
  lemma-comm-CZ-CZ02 = begin
    CZ • CZ02
      ≈⟨ cleft sym left-unit ⟩
    (ε • CZ) • CZ02
      ≈⟨ cleft cleft sym lemma-CZ02-CZ02⁻ ⟩
    ((CZ02 • CZ02⁻) • CZ) • CZ02
      ≈⟨ cleft assoc ⟩
    (CZ02 • (CZ02⁻ • CZ)) • CZ02
      ≈⟨ cleft cright sym lemma-comm-CZ-CZ02⁻ ⟩
    (CZ02 • (CZ • CZ02⁻)) • CZ02
      ≈⟨ cleft sym assoc ⟩
    ((CZ02 • CZ) • CZ02⁻) • CZ02
      ≈⟨ assoc ⟩
    (CZ02 • CZ) • (CZ02⁻ • CZ02)
      ≈⟨ cright lemma-CZ02⁻-CZ02 ⟩
    (CZ02 • CZ) • ε
      ≈⟨ right-unit ⟩
    CZ02 • CZ ∎

  T : Word (Gen (₃₊ n))
  T = Ex • Ex ↑ • Ex

  lemma-Ex↑-Ex↑ : Ex ↑ • Ex ↑ ≈ ε
  lemma-Ex↑-Ex↑ = lemma-cong↑ _ _ (PB₂.axiom order-Ex)

  ------------------------------------------------------------------------
  -- The swaps generate S₃
  --
  -- order-Ex makes each swap an involution and yang-baxter is the braid
  -- relation, so the 3-cycle σ = Ex • Ex ↑ has order 3.  Both c14 and c15
  -- assert that some element cubes to ε, so this is the shape they have
  -- to be matched against.

  lemma-σ³ : ((Ex • Ex ↑) • (Ex • Ex ↑)) • (Ex • Ex ↑) ≈ ε
  lemma-σ³ = begin
    ((Ex • Ex ↑) • (Ex • Ex ↑)) • (Ex • Ex ↑)
      ≈⟨ by-assoc auto ⟩
    Ex • (Ex ↑ • Ex • Ex ↑) • (Ex • Ex ↑)
      ≈⟨ cright cleft axiom yang-baxter ⟩
    Ex • (Ex ↓ • Ex ↑ • Ex ↓) • (Ex • Ex ↑)
      ≈⟨ by-assoc auto ⟩
    (Ex • Ex) • Ex ↑ • (Ex • Ex) • Ex ↑
      ≈⟨ cleft lemma-Ex-Ex ⟩
    ε • Ex ↑ • (Ex • Ex) • Ex ↑
      ≈⟨ left-unit ⟩
    Ex ↑ • (Ex • Ex) • Ex ↑
      ≈⟨ cright cleft lemma-Ex-Ex ⟩
    Ex ↑ • ε • Ex ↑
      ≈⟨ cright left-unit ⟩
    Ex ↑ • Ex ↑
      ≈⟨ lemma-Ex↑-Ex↑ ⟩
    ε ∎

  lemma-T-T : T • T ≈ ε
  lemma-T-T = begin
    (Ex • Ex ↑ • Ex) • (Ex • Ex ↑ • Ex)  ≈⟨ by-assoc auto ⟩
    (Ex • Ex ↑) • (Ex • Ex) • (Ex ↑ • Ex) ≈⟨ cright cleft lemma-Ex-Ex ⟩
    (Ex • Ex ↑) • ε • (Ex ↑ • Ex)         ≈⟨ cright left-unit ⟩
    (Ex • Ex ↑) • (Ex ↑ • Ex)             ≈⟨ by-assoc auto ⟩
    Ex • (Ex ↑ • Ex ↑) • Ex               ≈⟨ cright cleft lemma-Ex↑-Ex↑ ⟩
    Ex • ε • Ex                           ≈⟨ cright left-unit ⟩
    Ex • Ex                               ≈⟨ lemma-Ex-Ex ⟩
    ε ∎

  lemma-T-CZ : T • CZ • T ≈ CZ ↑
  lemma-T-CZ = begin
    (Ex • Ex ↑ • Ex) • CZ • (Ex • Ex ↑ • Ex)
      ≈⟨ by-assoc auto ⟩
    (Ex • Ex ↑) • (Ex • CZ) • (Ex • Ex ↑ • Ex)
      ≈⟨ cright cleft lemma-Ex-CZ ⟩
    (Ex • Ex ↑) • (CZ • Ex) • (Ex • Ex ↑ • Ex)
      ≈⟨ by-assoc auto ⟩
    (Ex ↓ • Ex ↑ • CZ) • (Ex • Ex) • (Ex ↑ • Ex)
      ≈⟨ cleft axiom cz-slide ⟩
    (CZ ↑ • Ex ↓ • Ex ↑) • (Ex • Ex) • (Ex ↑ • Ex)
      ≈⟨ cright cleft lemma-Ex-Ex ⟩
    (CZ ↑ • Ex ↓ • Ex ↑) • ε • (Ex ↑ • Ex)
      ≈⟨ cright left-unit ⟩
    (CZ ↑ • Ex ↓ • Ex ↑) • (Ex ↑ • Ex)
      ≈⟨ by-assoc auto ⟩
    CZ ↑ • Ex • (Ex ↑ • Ex ↑) • Ex
      ≈⟨ cright cright cleft lemma-Ex↑-Ex↑ ⟩
    CZ ↑ • Ex • ε • Ex
      ≈⟨ cright cright left-unit ⟩
    CZ ↑ • Ex • Ex
      ≈⟨ cright lemma-Ex-Ex ⟩
    CZ ↑ • ε
      ≈⟨ right-unit ⟩
    CZ ↑ ∎

  ------------------------------------------------------------------------
  -- selinger-c12, by moving the commutation onto the other pair
  --
  -- Simplified-V1 states c12 over the CZs sharing wire 1, whereas
  -- lemma-comm-CZ-CZ02 has the pair sharing wire 0.  The 3-cycle
  -- σ = Ex • Ex ↑ carries one to the other: cz-slide IS the statement
  -- that σ conjugates CZ to CZ ↑, and the companion fact — that it
  -- conjugates CZ02 back to CZ — follows once CZ02 is rewritten with the
  -- other swap, which is again cz-slide.

  private
    -- CZ02 through the upper swap rather than the lower one.
    lemma-CZ02' : Ex ↑ • (CZ • Ex ↑) ≈ CZ02
    lemma-CZ02' = •-cancelˡ {g = Ex} (begin
      Ex • (Ex ↑ • (CZ • Ex ↑))   ≈⟨ by-assoc auto ⟩
      (Ex ↓ • Ex ↑ • CZ) • Ex ↑   ≈⟨ cleft axiom cz-slide ⟩
      (CZ ↑ • Ex ↓ • Ex ↑) • Ex ↑ ≈⟨ by-assoc auto ⟩
      (CZ ↑ • Ex) • (Ex ↑ • Ex ↑) ≈⟨ cright lemma-Ex↑-Ex↑ ⟩
      (CZ ↑ • Ex) • ε             ≈⟨ right-unit ⟩
      CZ ↑ • Ex                   ≈⟨ sym left-unit ⟩
      ε • (CZ ↑ • Ex)             ≈⟨ cleft sym lemma-Ex-Ex ⟩
      (Ex • Ex) • (CZ ↑ • Ex)     ≈⟨ assoc ⟩
      Ex • (Ex • (CZ ↑ • Ex)) ∎)

    -- The 3-cycle sends the remote CZ back to the lower pair.
    lemma-σ-CZ02 : (Ex • Ex ↑) • CZ02 ≈ CZ • (Ex • Ex ↑)
    lemma-σ-CZ02 = begin
      (Ex • Ex ↑) • CZ02
        ≈⟨ cright sym lemma-CZ02' ⟩
      (Ex • Ex ↑) • (Ex ↑ • (CZ • Ex ↑))
        ≈⟨ by-assoc auto ⟩
      Ex • ((Ex ↑ • Ex ↑) • (CZ • Ex ↑))
        ≈⟨ cright cleft lemma-Ex↑-Ex↑ ⟩
      Ex • (ε • (CZ • Ex ↑))
        ≈⟨ cright left-unit ⟩
      Ex • (CZ • Ex ↑)
        ≈⟨ sym assoc ⟩
      (Ex • CZ) • Ex ↑
        ≈⟨ cleft lemma-Ex-CZ ⟩
      (CZ • Ex) • Ex ↑
        ≈⟨ assoc ⟩
      CZ • (Ex • Ex ↑) ∎

    aux-left : (Ex • Ex ↑) • (CZ • CZ02) ≈ (CZ ↑ • CZ) • (Ex • Ex ↑)
    aux-left = begin
      (Ex • Ex ↑) • (CZ • CZ02)     ≈⟨ sym assoc ⟩
      ((Ex • Ex ↑) • CZ) • CZ02     ≈⟨ cleft by-assoc auto ⟩
      (Ex ↓ • Ex ↑ • CZ) • CZ02     ≈⟨ cleft axiom cz-slide ⟩
      (CZ ↑ • Ex ↓ • Ex ↑) • CZ02   ≈⟨ cleft by-assoc auto ⟩
      (CZ ↑ • (Ex • Ex ↑)) • CZ02   ≈⟨ assoc ⟩
      CZ ↑ • ((Ex • Ex ↑) • CZ02)   ≈⟨ cright lemma-σ-CZ02 ⟩
      CZ ↑ • (CZ • (Ex • Ex ↑))     ≈⟨ sym assoc ⟩
      (CZ ↑ • CZ) • (Ex • Ex ↑) ∎

    aux-right : (Ex • Ex ↑) • (CZ02 • CZ) ≈ (CZ • CZ ↑) • (Ex • Ex ↑)
    aux-right = begin
      (Ex • Ex ↑) • (CZ02 • CZ)     ≈⟨ sym assoc ⟩
      ((Ex • Ex ↑) • CZ02) • CZ     ≈⟨ cleft lemma-σ-CZ02 ⟩
      (CZ • (Ex • Ex ↑)) • CZ       ≈⟨ assoc ⟩
      CZ • ((Ex • Ex ↑) • CZ)       ≈⟨ cright by-assoc auto ⟩
      CZ • (Ex ↓ • Ex ↑ • CZ)       ≈⟨ cright axiom cz-slide ⟩
      CZ • (CZ ↑ • Ex ↓ • Ex ↑)     ≈⟨ cright by-assoc auto ⟩
      CZ • (CZ ↑ • (Ex • Ex ↑))     ≈⟨ sym assoc ⟩
      (CZ • CZ ↑) • (Ex • Ex ↑) ∎

  lemma-selinger-c12 : CZ ↑ • CZ ≈ CZ • CZ ↑
  lemma-selinger-c12 = •-cancelʳ {h = Ex • Ex ↑} (begin
    (CZ ↑ • CZ) • (Ex • Ex ↑)   ≈⟨ sym aux-left ⟩
    (Ex • Ex ↑) • (CZ • CZ02)   ≈⟨ cright lemma-comm-CZ-CZ02 ⟩
    (Ex • Ex ↑) • (CZ02 • CZ)   ≈⟨ aux-right ⟩
    (CZ • CZ ↑) • (Ex • Ex ↑) ∎)

  ------------------------------------------------------------------------
  -- The third commuting pair, by conjugating c12 with the 3-cycle
  --
  -- σ = Ex • Ex ↑ conjugates CZ to CZ ↑ (that is cz-slide) and CZ02 back
  -- to CZ (lemma-σ-CZ02).  Since σ ³ ≈ ε, the missing third leg follows:
  -- σ carries CZ ↑ to CZ02, because two steps forward is one step back.
  -- Conjugating c12 by σ then turns "CZ ↑ against CZ" into "CZ02 against
  -- CZ ↑", the pair the other half of c13 needs.

  private
    lemma-σ-CZ : (Ex • Ex ↑) • CZ ≈ CZ ↑ • (Ex • Ex ↑)
    lemma-σ-CZ = begin
      (Ex • Ex ↑) • CZ    ≈⟨ by-assoc auto ⟩
      Ex ↓ • Ex ↑ • CZ    ≈⟨ axiom cz-slide ⟩
      CZ ↑ • Ex ↓ • Ex ↑  ≈⟨ by-assoc auto ⟩
      CZ ↑ • (Ex • Ex ↑) ∎

    lemma-σ-CZ↑ : (Ex • Ex ↑) • CZ ↑ ≈ CZ02 • (Ex • Ex ↑)
    lemma-σ-CZ↑ =
      •-cancelʳ {h = (Ex • Ex ↑) • (Ex • Ex ↑)} (begin
        ((Ex • Ex ↑) • CZ ↑) • ((Ex • Ex ↑) • (Ex • Ex ↑))
          ≈⟨ by-assoc auto ⟩
        (Ex • Ex ↑) • (((CZ ↑ • (Ex • Ex ↑))) • (Ex • Ex ↑))
          ≈⟨ cright cleft sym lemma-σ-CZ ⟩
        (Ex • Ex ↑) • (((Ex • Ex ↑) • CZ) • (Ex • Ex ↑))
          ≈⟨ cright assoc ⟩
        (Ex • Ex ↑) • ((Ex • Ex ↑) • (CZ • (Ex • Ex ↑)))
          ≈⟨ cright cright sym lemma-σ-CZ02 ⟩
        (Ex • Ex ↑) • ((Ex • Ex ↑) • ((Ex • Ex ↑) • CZ02))
          ≈⟨ by-assoc auto ⟩
        (((Ex • Ex ↑) • (Ex • Ex ↑)) • (Ex • Ex ↑)) • CZ02
          ≈⟨ cleft lemma-σ³ ⟩
        ε • CZ02
          ≈⟨ left-unit ⟩
        CZ02
          ≈⟨ sym right-unit ⟩
        CZ02 • ε
          ≈⟨ cright sym lemma-σ³ ⟩
        CZ02 • (((Ex • Ex ↑) • (Ex • Ex ↑)) • (Ex • Ex ↑))
          ≈⟨ by-assoc auto ⟩
        (CZ02 • (Ex • Ex ↑)) • ((Ex • Ex ↑) • (Ex • Ex ↑)) ∎)

  lemma-comm-CZ↑-CZ02 : CZ ↑ • CZ02 ≈ CZ02 • CZ ↑
  lemma-comm-CZ↑-CZ02 = •-cancelʳ {h = Ex • Ex ↑} (begin
    (CZ ↑ • CZ02) • (Ex • Ex ↑)
      ≈⟨ assoc ⟩
    CZ ↑ • (CZ02 • (Ex • Ex ↑))
      ≈⟨ cright sym lemma-σ-CZ↑ ⟩
    CZ ↑ • ((Ex • Ex ↑) • CZ ↑)
      ≈⟨ sym assoc ⟩
    (CZ ↑ • (Ex • Ex ↑)) • CZ ↑
      ≈⟨ cleft sym lemma-σ-CZ ⟩
    ((Ex • Ex ↑) • CZ) • CZ ↑
      ≈⟨ assoc ⟩
    (Ex • Ex ↑) • (CZ • CZ ↑)
      ≈⟨ cright sym lemma-selinger-c12 ⟩
    (Ex • Ex ↑) • (CZ ↑ • CZ)
      ≈⟨ sym assoc ⟩
    ((Ex • Ex ↑) • CZ ↑) • CZ
      ≈⟨ cleft lemma-σ-CZ↑ ⟩
    (CZ02 • (Ex • Ex ↑)) • CZ
      ≈⟨ assoc ⟩
    CZ02 • ((Ex • Ex ↑) • CZ)
      ≈⟨ cright lemma-σ-CZ ⟩
    CZ02 • (CZ ↑ • (Ex • Ex ↑))
      ≈⟨ sym assoc ⟩
    (CZ02 • CZ ↑) • (Ex • Ex ↑) ∎)

  ------------------------------------------------------------------------
  -- The lower half-swap commutes with the upper CZ
  --
  -- ₕ|ₕ is H • CZ • H, all on wires 0 and 1.  The H commutes with CZ ↑
  -- structurally — it is a one-wire gate against a gate shifted off wire
  -- 0 — and the two CZs commute by c12, which is now available.  This is
  -- what makes c13 collapse.

  lemma-comm-ₕ|ₕ-CZ↑ : ₕ|ₕ • CZ ↑ ≈ CZ ↑ • ₕ|ₕ
  lemma-comm-ₕ|ₕ-CZ↑ = begin
    (H • CZ • H) • CZ ↑
      ≈⟨ by-assoc auto ⟩
    H • (CZ • (H • CZ ↑))
      ≈⟨ cright cright sym (axiom comm-H) ⟩
    H • (CZ • (CZ ↑ • H))
      ≈⟨ cright sym assoc ⟩
    H • ((CZ • CZ ↑) • H)
      ≈⟨ cright cleft sym lemma-selinger-c12 ⟩
    H • ((CZ ↑ • CZ) • H)
      ≈⟨ by-assoc auto ⟩
    (H • CZ ↑) • (CZ • H)
      ≈⟨ cleft sym (axiom comm-H) ⟩
    (CZ ↑ • H) • (CZ • H)
      ≈⟨ by-assoc auto ⟩
    CZ ↑ • (H • CZ • H) ∎

  ------------------------------------------------------------------------
  -- Half of c13: conjugating the upper CZ by the half-swaps gives CZ02
  --
  -- With ⊥⊤ = Ex • ₕ|ₕ and ⊤⊥ = ₕ|ₕ • Ex, the word ⊥⊤ • CZ ↑ • ⊤⊥ is
  -- Ex • (ₕ|ₕ • CZ ↑ • ₕ|ₕ) • Ex; the previous lemma moves CZ ↑ out
  -- through one ₕ|ₕ, the involution kills the pair, and what is left is
  -- Ex • CZ ↑ • Ex, which is CZ02 by definition.
  --
  -- Semantically both sides of c13 are CZ02 — that is how this shape was
  -- found — so the other half is the same statement about the upper pair.

  ------------------------------------------------------------------------
  -- The upper half-swap commutes with CZ02
  --
  -- The mirror of lemma-comm-ₕ|ₕ-CZ↑, one wire up.  ₕ|ₕ ↑ is
  -- H ↑ • CZ ↑ • H ↑; the two CZs commute by the lemma above, and H ↑
  -- against CZ02 is a conjugation: writing CZ02 as Ex ↑ • CZ • Ex ↑, the
  -- swap carries H ↑ to H ↑ ↑, which clears CZ structurally, and the
  -- second swap carries it back.

  private
    ex↑-H↑↑ : Ex ↑ • H ↑ ↑ ≈ H ↑ • Ex ↑
    ex↑-H↑↑ = lemma-cong↑ _ _ (Ex-Conjugation.lemma-Ex-H↑ n)

    ex↑-H↑ : Ex ↑ • H ↑ ≈ H ↑ ↑ • Ex ↑
    ex↑-H↑ = lemma-cong↑ _ _ (Ex-Conjugation.lemma-Ex-H n)

  lemma-comm-H↑-CZ02 : H ↑ • CZ02 ≈ CZ02 • H ↑
  lemma-comm-H↑-CZ02 = begin
    H ↑ • CZ02
      ≈⟨ cright sym lemma-CZ02' ⟩
    H ↑ • (Ex ↑ • (CZ • Ex ↑))
      ≈⟨ sym assoc ⟩
    (H ↑ • Ex ↑) • (CZ • Ex ↑)
      ≈⟨ cleft sym ex↑-H↑↑ ⟩
    (Ex ↑ • H ↑ ↑) • (CZ • Ex ↑)
      ≈⟨ by-assoc auto ⟩
    Ex ↑ • ((H ↑ ↑ • CZ) • Ex ↑)
      ≈⟨ cright cleft axiom comm-CZ ⟩
    Ex ↑ • ((CZ • H ↑ ↑) • Ex ↑)
      ≈⟨ cright assoc ⟩
    Ex ↑ • (CZ • (H ↑ ↑ • Ex ↑))
      ≈⟨ cright cright sym ex↑-H↑ ⟩
    Ex ↑ • (CZ • (Ex ↑ • H ↑))
      ≈⟨ by-assoc auto ⟩
    (Ex ↑ • (CZ • Ex ↑)) • H ↑
      ≈⟨ cleft lemma-CZ02' ⟩
    CZ02 • H ↑ ∎

  lemma-comm-ₕ|ₕ↑-CZ02 :
    (H ↑ • CZ ↑ • H ↑) • CZ02 ≈ CZ02 • (H ↑ • CZ ↑ • H ↑)
  lemma-comm-ₕ|ₕ↑-CZ02 = begin
    (H ↑ • CZ ↑ • H ↑) • CZ02
      ≈⟨ by-assoc auto ⟩
    H ↑ • (CZ ↑ • (H ↑ • CZ02))
      ≈⟨ cright cright lemma-comm-H↑-CZ02 ⟩
    H ↑ • (CZ ↑ • (CZ02 • H ↑))
      ≈⟨ cright sym assoc ⟩
    H ↑ • ((CZ ↑ • CZ02) • H ↑)
      ≈⟨ cright cleft lemma-comm-CZ↑-CZ02 ⟩
    H ↑ • ((CZ02 • CZ ↑) • H ↑)
      ≈⟨ sym assoc ⟩
    (H ↑ • (CZ02 • CZ ↑)) • H ↑
      ≈⟨ cleft sym assoc ⟩
    ((H ↑ • CZ02) • CZ ↑) • H ↑
      ≈⟨ cleft cleft lemma-comm-H↑-CZ02 ⟩
    ((CZ02 • H ↑) • CZ ↑) • H ↑
      ≈⟨ by-assoc auto ⟩
    CZ02 • (H ↑ • CZ ↑ • H ↑) ∎

  lemma-c13-right : ⊥⊤ • (CZ ↑ • ⊤⊥) ≈ CZ02
  lemma-c13-right = begin
    ⊥⊤ • (CZ ↑ • ⊤⊥)
      ≈⟨ cleft lemma-⊥⊤-simple ⟩
    (Ex • ₕ|ₕ) • (CZ ↑ • ⊤⊥)
      ≈⟨ cright cright lemma-⊤⊥-simple ⟩
    (Ex • ₕ|ₕ) • (CZ ↑ • (ₕ|ₕ • Ex))
      ≈⟨ by-assoc auto ⟩
    Ex • (((ₕ|ₕ • CZ ↑) • ₕ|ₕ) • Ex)
      ≈⟨ cright cleft cleft lemma-comm-ₕ|ₕ-CZ↑ ⟩
    Ex • (((CZ ↑ • ₕ|ₕ) • ₕ|ₕ) • Ex)
      ≈⟨ cright cleft assoc ⟩
    Ex • ((CZ ↑ • (ₕ|ₕ • ₕ|ₕ)) • Ex)
      ≈⟨ cright cleft cright lemma-ₕ|ₕ-invol ⟩
    Ex • ((CZ ↑ • ε) • Ex)
      ≈⟨ cright cleft right-unit ⟩
    Ex • (CZ ↑ • Ex) ∎

  ------------------------------------------------------------------------
  -- The other half of c13, and c13 itself
  --
  -- One wire up, with lemma-comm-ₕ|ₕ↑-CZ02 in place of lemma-comm-ₕ|ₕ-CZ↑
  -- and lemma-CZ02' in place of the definition of CZ02.  Both sides of
  -- c13 are CZ02, so the rule is the two halves glued.

  lemma-c13-left : ⊤⊥ {n} ↑ • (CZ • ⊥⊤ {n} ↑) ≈ CZ02
  lemma-c13-left = begin
    ⊤⊥ {n} ↑ • (CZ • ⊥⊤ {n} ↑)
      ≈⟨ cleft (lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊤⊥-simple n)) ⟩
    ((H ↑ • CZ ↑ • H ↑) • Ex ↑) • (CZ • ⊥⊤ {n} ↑)
      ≈⟨ cright cright (lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊥⊤-simple n)) ⟩
    ((H ↑ • CZ ↑ • H ↑) • Ex ↑) • (CZ • (Ex ↑ • (H ↑ • CZ ↑ • H ↑)))
      ≈⟨ by-assoc auto ⟩
    (H ↑ • CZ ↑ • H ↑) • ((Ex ↑ • (CZ • Ex ↑)) • (H ↑ • CZ ↑ • H ↑))
      ≈⟨ cright cleft lemma-CZ02' ⟩
    (H ↑ • CZ ↑ • H ↑) • (CZ02 • (H ↑ • CZ ↑ • H ↑))
      ≈⟨ sym assoc ⟩
    ((H ↑ • CZ ↑ • H ↑) • CZ02) • (H ↑ • CZ ↑ • H ↑)
      ≈⟨ cleft lemma-comm-ₕ|ₕ↑-CZ02 ⟩
    (CZ02 • (H ↑ • CZ ↑ • H ↑)) • (H ↑ • CZ ↑ • H ↑)
      ≈⟨ assoc ⟩
    CZ02 • ((H ↑ • CZ ↑ • H ↑) • (H ↑ • CZ ↑ • H ↑))
      ≈⟨ cright (lemma-cong↑ _ _ (Ex-Conjugation.lemma-ₕ|ₕ-invol n)) ⟩
    CZ02 • ε
      ≈⟨ right-unit ⟩
    CZ02 ∎

  lemma-selinger-c13 :
    ⊤⊥ {n} ↑ • CZ ↓ • ⊥⊤ {n} ↑ ≈ ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
  lemma-selinger-c13 = trans lemma-c13-left (sym lemma-c13-right)

  ------------------------------------------------------------------------
  -- c13 as a commutation rule
  --
  -- Since ⊥⊤ ↑ inverts ⊤⊥ ↑, the conjugation form of c13 is equivalently
  -- a rule for moving ⊤⊥ ↑ across a CZ, which turns it from CZ into
  -- CZ02.  This is the form c14 uses: its element ⊤⊥ ↑ • CZ becomes
  -- CZ02 • ⊤⊥ ↑, so cubing it is a question about how ⊤⊥ ↑ moves across
  -- CZ02 — the one step c14 still lacks.

  ------------------------------------------------------------------------
  -- The identity c14 turns on
  --
  --     CZ • ₕ|ₕ ↑ • CZ • ₕ|ₕ ↑ ≈ CZ02
  --
  -- i.e. conjugating CZ by the upper half-swap gives CZ⁻¹ • CZ02.  This
  -- is where C18 enters, and it is the only place in the c13/c14 story
  -- that needs an axiom beyond what c13 used.
  --
  -- The half-swap is M₋₁ • CX (lemma-ₕ|ₕ-CX), so C18 applies directly:
  -- it moves CX ↑ across the CZ at the cost of a CZ02.  The two CX ↑ that
  -- are left sandwich a multiplier, and that sandwich collapses back to
  -- the multiplier because the half-swap is an involution.  What remains
  -- is a multiplier passing two CZs, rescaling one of them to its inverse
  -- and commuting with the other.

  private
    -- The multiplier on wire 1 commutes with CZ02, which lives on wires
    -- 0 and 2.  Syntactically: write CZ02 with the upper swap, which
    -- carries the multiplier to wire 2, where it clears CZ by the
    -- word-level structural rule, and carry it back.
    ex↑-M↑↑ : Ex ↑ • (M₋₁ {n}) ↑ ↑ ≈ M₋₁ ↑ • Ex ↑
    ex↑-M↑↑ = lemma-cong↑ _ _ (Ex-Conjugation.lemma-Ex-M↑ n -'₁)

    M↑↑-ex↑ : (M₋₁ {n}) ↑ ↑ • Ex ↑ ≈ Ex ↑ • M₋₁ ↑
    M↑↑-ex↑ = begin
      (M₋₁ {n}) ↑ ↑ • Ex ↑
        ≈⟨ sym left-unit ⟩
      ε • ((M₋₁ {n}) ↑ ↑ • Ex ↑)
        ≈⟨ cleft sym lemma-Ex↑-Ex↑ ⟩
      (Ex ↑ • Ex ↑) • ((M₋₁ {n}) ↑ ↑ • Ex ↑)
        -- explicit assoc throughout this section: M₋₁ carries a symbolic
        -- power, so to-list is stuck and by-assoc cannot re-bracket it
        ≈⟨ assoc ⟩
      Ex ↑ • (Ex ↑ • ((M₋₁ {n}) ↑ ↑ • Ex ↑))
        ≈⟨ cright sym assoc ⟩
      Ex ↑ • ((Ex ↑ • (M₋₁ {n}) ↑ ↑) • Ex ↑)
        ≈⟨ cright cleft ex↑-M↑↑ ⟩
      Ex ↑ • ((M₋₁ ↑ • Ex ↑) • Ex ↑)
        ≈⟨ cright assoc ⟩
      Ex ↑ • (M₋₁ ↑ • (Ex ↑ • Ex ↑))
        ≈⟨ cright cright lemma-Ex↑-Ex↑ ⟩
      Ex ↑ • (M₋₁ ↑ • ε)
        ≈⟨ cright right-unit ⟩
      Ex ↑ • M₋₁ ↑ ∎

    lemma-M₋₁↑-CZ02 : M₋₁ ↑ • CZ02 ≈ CZ02 • M₋₁ ↑
    lemma-M₋₁↑-CZ02 = begin
      M₋₁ ↑ • CZ02
        ≈⟨ cright sym lemma-CZ02' ⟩
      M₋₁ ↑ • (Ex ↑ • (CZ • Ex ↑))
        ≈⟨ sym assoc ⟩
      (M₋₁ ↑ • Ex ↑) • (CZ • Ex ↑)
        ≈⟨ cleft sym ex↑-M↑↑ ⟩
      (Ex ↑ • (M₋₁ {n}) ↑ ↑) • (CZ • Ex ↑)
        ≈⟨ assoc ⟩
      Ex ↑ • ((M₋₁ {n}) ↑ ↑ • (CZ • Ex ↑))
        ≈⟨ cright sym assoc ⟩
      Ex ↑ • (((M₋₁ {n}) ↑ ↑ • CZ) • Ex ↑)
        ≈⟨ cright cleft sym (lemma-comm-CZ-w↑ (M₋₁ {n})) ⟩
      Ex ↑ • ((CZ • (M₋₁ {n}) ↑ ↑) • Ex ↑)
        ≈⟨ cright assoc ⟩
      Ex ↑ • (CZ • ((M₋₁ {n}) ↑ ↑ • Ex ↑))
        ≈⟨ cright cright M↑↑-ex↑ ⟩
      Ex ↑ • (CZ • (Ex ↑ • M₋₁ ↑))
        ≈⟨ cright sym assoc ⟩
      Ex ↑ • ((CZ • Ex ↑) • M₋₁ ↑)
        ≈⟨ sym assoc ⟩
      (Ex ↑ • (CZ • Ex ↑)) • M₋₁ ↑
        ≈⟨ cleft lemma-CZ02' ⟩
      CZ02 • M₋₁ ↑ ∎

    -- The half-swap is an involution, and it is M₋₁ ↑ • CX ↑, so the two
    -- CX ↑ sandwiching a multiplier collapse back to that multiplier.
    ₕ|ₕ↑-CX : M₋₁ ↑ • CX ↑ ≈ ₕ|ₕ ↑
    ₕ|ₕ↑-CX = lemma-cong↑ _ _ (Ex-Conjugation.lemma-ₕ|ₕ-CX n)

    M₋₁↑-invol : M₋₁ ↑ • M₋₁ ↑ ≈ ε
    M₋₁↑-invol = lemma-cong↑ _ _ (One-Wire.lemma-M₋₁^2 (₁₊ n))

    lemma-CX↑-M₋₁↑ : CX ↑ • (M₋₁ ↑ • CX ↑) ≈ M₋₁ ↑
    lemma-CX↑-M₋₁↑ = •-cancelˡ {g = M₋₁ ↑} (begin
      M₋₁ ↑ • (CX ↑ • (M₋₁ ↑ • CX ↑))
        ≈⟨ sym assoc ⟩
      (M₋₁ ↑ • CX ↑) • (M₋₁ ↑ • CX ↑)
        ≈⟨ cong ₕ|ₕ↑-CX ₕ|ₕ↑-CX ⟩
      ₕ|ₕ ↑ • ₕ|ₕ ↑
        ≈⟨ lemma-cong↑ _ _ (Ex-Conjugation.lemma-ₕ|ₕ-invol n) ⟩
      ε
        ≈⟨ sym M₋₁↑-invol ⟩
      M₋₁ ↑ • M₋₁ ↑ ∎)

  -- Conjugating CZ by the upper half-swap gives the inverse of CZ • CZ02.
  -- Stated inverse-free, that is this.
  lemma-c14-key : CZ • (CZ02 • (ₕ|ₕ ↑ • (CZ • ₕ|ₕ ↑))) ≈ ε
  lemma-c14-key = begin
    CZ • (CZ02 • (ₕ|ₕ ↑ • (CZ • ₕ|ₕ ↑)))
      ≈⟨ cright cright cong (sym ₕ|ₕ↑-CX) (cright sym ₕ|ₕ↑-CX) ⟩
    CZ • (CZ02 • ((M₋₁ ↑ • CX ↑) • (CZ • (M₋₁ ↑ • CX ↑))))
      -- explicit assoc, not by-assoc: M₋₁'s symbolic power blocks to-list
      ≈⟨ cright sym assoc ⟩
    CZ • ((CZ02 • (M₋₁ ↑ • CX ↑)) • (CZ • (M₋₁ ↑ • CX ↑)))
      ≈⟨ cright cleft sym assoc ⟩
    CZ • (((CZ02 • M₋₁ ↑) • CX ↑) • (CZ • (M₋₁ ↑ • CX ↑)))
      ≈⟨ cright cleft cleft sym lemma-M₋₁↑-CZ02 ⟩
    CZ • (((M₋₁ ↑ • CZ02) • CX ↑) • (CZ • (M₋₁ ↑ • CX ↑)))
      ≈⟨ cright cleft assoc ⟩
    CZ • ((M₋₁ ↑ • (CZ02 • CX ↑)) • (CZ • (M₋₁ ↑ • CX ↑)))
      ≈⟨ cright assoc ⟩
    CZ • (M₋₁ ↑ • ((CZ02 • CX ↑) • (CZ • (M₋₁ ↑ • CX ↑))))
      ≈⟨ cright cright sym assoc ⟩
    CZ • (M₋₁ ↑ • (((CZ02 • CX ↑) • CZ) • (M₋₁ ↑ • CX ↑)))
      ≈⟨ cright cright cleft assoc ⟩
    CZ • (M₋₁ ↑ • ((CZ02 • (CX ↑ • CZ)) • (M₋₁ ↑ • CX ↑)))
      -- the axiom, right to left
      ≈⟨ cright cright cleft sym (axiom semi-CX↑-CZ↓) ⟩
    CZ • (M₋₁ ↑ • ((CZ • CX ↑) • (M₋₁ ↑ • CX ↑)))
      ≈⟨ cright cright assoc ⟩
    CZ • (M₋₁ ↑ • (CZ • (CX ↑ • (M₋₁ ↑ • CX ↑))))
      ≈⟨ cright cright cright lemma-CX↑-M₋₁↑ ⟩
    CZ • (M₋₁ ↑ • (CZ • M₋₁ ↑))
      ≈⟨ cright sym assoc ⟩
    CZ • ((M₋₁ ↑ • CZ) • M₋₁ ↑)
      ≈⟨ cright cleft lemma-M₋₁↑-CZ ⟩
    CZ • ((CZ ^ toℕ (-'₁ .proj₁) • M₋₁ ↑) • M₋₁ ↑)
      ≈⟨ cright assoc ⟩
    CZ • (CZ ^ toℕ (-'₁ .proj₁) • (M₋₁ ↑ • M₋₁ ↑))
      ≈⟨ cright cright M₋₁↑-invol ⟩
    CZ • (CZ ^ toℕ (-'₁ .proj₁) • ε)
      ≈⟨ cright right-unit ⟩
    CZ • CZ ^ toℕ (-'₁ .proj₁)
      ≈⟨ lemma-CZ-CZ₋₁ ⟩
    ε ∎

  lemma-⊤⊥↑-CZ : ⊤⊥ {n} ↑ • CZ ≈ CZ02 • ⊤⊥ {n} ↑
  lemma-⊤⊥↑-CZ = begin
    ⊤⊥ {n} ↑ • CZ
      ≈⟨ sym right-unit ⟩
    (⊤⊥ {n} ↑ • CZ) • ε
      ≈⟨ cright sym (lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊥⊤-⊤⊥ n)) ⟩
    (⊤⊥ {n} ↑ • CZ) • (⊥⊤ {n} ↑ • ⊤⊥ {n} ↑)
      ≈⟨ by-assoc auto ⟩
    (⊤⊥ {n} ↑ • (CZ • ⊥⊤ {n} ↑)) • ⊤⊥ {n} ↑
      ≈⟨ cleft lemma-c13-left ⟩
    CZ02 • ⊤⊥ {n} ↑ ∎

  ------------------------------------------------------------------------
  -- c14
  --
  -- Write A for ⊤⊥ ↑.  Conjugation by A sends CZ to CZ02 (that is c13,
  -- as lemma-⊤⊥↑-CZ) and CZ02 to the inverse of CZ • CZ02 (that is
  -- lemma-c14-key).  A has order 3, so cubing A • CZ telescopes: pushing
  -- the three A's rightwards leaves CZ02 • (CZ • CZ02)⁻¹ • CZ, which is ε.
  --
  -- The inverses are real words here — CZ ⁻¹ is CZ ^ p-1 — so this section
  -- uses explicit assoc throughout, to-list being stuck on them.

  private
    CZ⁻ : Word (Gen (₃₊ n))
    CZ⁻ = CZ ^ p-1

    lemma-CZ-CZ⁻ : CZ • CZ⁻ ≈ ε
    lemma-CZ-CZ⁻ = begin
      CZ • CZ ^ p-1       ≈⟨ sym (^-+ CZ 1 p-1) ⟩
      CZ ^ (1 Nat.+ p-1)  ≈⟨ axiom order-CZ ⟩
      ε ∎

    lemma-CZ⁻-CZ : CZ⁻ • CZ ≈ ε
    lemma-CZ⁻-CZ = begin
      CZ ^ p-1 • CZ       ≈⟨ sym (^-+ CZ p-1 1) ⟩
      CZ ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (CZ ^_) (NP.+-comm p-1 1) ⟩
      CZ ^ (1 Nat.+ p-1)  ≈⟨ axiom order-CZ ⟩
      ε ∎

    -- lemma-c14-key with one half-swap cancelled off the right.
    key' : CZ • (CZ02 • (ₕ|ₕ ↑ • CZ)) ≈ ₕ|ₕ ↑
    key' = •-cancelʳ {h = ₕ|ₕ ↑} (begin
      (CZ • (CZ02 • (ₕ|ₕ ↑ • CZ))) • ₕ|ₕ ↑
        ≈⟨ assoc ⟩
      CZ • ((CZ02 • (ₕ|ₕ ↑ • CZ)) • ₕ|ₕ ↑)
        ≈⟨ cright assoc ⟩
      CZ • (CZ02 • ((ₕ|ₕ ↑ • CZ) • ₕ|ₕ ↑))
        ≈⟨ cright cright assoc ⟩
      CZ • (CZ02 • (ₕ|ₕ ↑ • (CZ • ₕ|ₕ ↑)))
        ≈⟨ lemma-c14-key ⟩
      ε
        ≈⟨ sym (lemma-cong↑ _ _ (Ex-Conjugation.lemma-ₕ|ₕ-invol n)) ⟩
      ₕ|ₕ ↑ • ₕ|ₕ ↑ ∎)

    -- Ex ↑ carries CZ02 to CZ, since CZ02 is Ex ↑ • CZ • Ex ↑.
    ex↑-CZ02 : Ex ↑ • CZ02 ≈ CZ • Ex ↑
    ex↑-CZ02 = begin
      Ex ↑ • CZ02
        ≈⟨ cright sym lemma-CZ02' ⟩
      Ex ↑ • (Ex ↑ • (CZ • Ex ↑))
        ≈⟨ sym assoc ⟩
      (Ex ↑ • Ex ↑) • (CZ • Ex ↑)
        ≈⟨ cleft lemma-Ex↑-Ex↑ ⟩
      ε • (CZ • Ex ↑)
        ≈⟨ left-unit ⟩
      CZ • Ex ↑ ∎

    ⊤⊥↑-split : ⊤⊥ {n} ↑ ≈ ₕ|ₕ ↑ • Ex ↑
    ⊤⊥↑-split = lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊤⊥-simple n)

  -- Conjugation by ⊤⊥ ↑ sends CZ02 to the inverse of CZ • CZ02.
  lemma-⊤⊥↑-CZ02 : CZ • (CZ02 • (⊤⊥ {n} ↑ • CZ02)) ≈ ⊤⊥ {n} ↑
  lemma-⊤⊥↑-CZ02 = begin
    CZ • (CZ02 • (⊤⊥ {n} ↑ • CZ02))
      ≈⟨ cright cright cleft ⊤⊥↑-split ⟩
    CZ • (CZ02 • ((ₕ|ₕ ↑ • Ex ↑) • CZ02))
      ≈⟨ cright cright assoc ⟩
    CZ • (CZ02 • (ₕ|ₕ ↑ • (Ex ↑ • CZ02)))
      ≈⟨ cright cright cright ex↑-CZ02 ⟩
    CZ • (CZ02 • (ₕ|ₕ ↑ • (CZ • Ex ↑)))
      ≈⟨ cright cright sym assoc ⟩
    CZ • (CZ02 • ((ₕ|ₕ ↑ • CZ) • Ex ↑))
      ≈⟨ cright sym assoc ⟩
    CZ • ((CZ02 • (ₕ|ₕ ↑ • CZ)) • Ex ↑)
      ≈⟨ sym assoc ⟩
    (CZ • (CZ02 • (ₕ|ₕ ↑ • CZ))) • Ex ↑
      ≈⟨ cleft key' ⟩
    ₕ|ₕ ↑ • Ex ↑
      ≈⟨ sym ⊤⊥↑-split ⟩
    ⊤⊥ {n} ↑ ∎

  private
    -- The three ways ⊤⊥ ↑ moves across the two CZs and their inverses.
    A·CZ02 : ⊤⊥ {n} ↑ • CZ02 ≈ (CZ02⁻ • CZ⁻) • ⊤⊥ {n} ↑
    A·CZ02 = begin
      ⊤⊥ {n} ↑ • CZ02
        ≈⟨ sym left-unit ⟩
      ε • (⊤⊥ {n} ↑ • CZ02)
        ≈⟨ cleft sym lemma-CZ02⁻-CZ02 ⟩
      (CZ02⁻ • CZ02) • (⊤⊥ {n} ↑ • CZ02)
        ≈⟨ cleft cright sym left-unit ⟩
      (CZ02⁻ • (ε • CZ02)) • (⊤⊥ {n} ↑ • CZ02)
        ≈⟨ cleft cright cleft sym lemma-CZ⁻-CZ ⟩
      (CZ02⁻ • ((CZ⁻ • CZ) • CZ02)) • (⊤⊥ {n} ↑ • CZ02)
        ≈⟨ cleft cright assoc ⟩
      (CZ02⁻ • (CZ⁻ • (CZ • CZ02))) • (⊤⊥ {n} ↑ • CZ02)
        ≈⟨ cleft sym assoc ⟩
      ((CZ02⁻ • CZ⁻) • (CZ • CZ02)) • (⊤⊥ {n} ↑ • CZ02)
        ≈⟨ assoc ⟩
      (CZ02⁻ • CZ⁻) • ((CZ • CZ02) • (⊤⊥ {n} ↑ • CZ02))
        ≈⟨ cright assoc ⟩
      (CZ02⁻ • CZ⁻) • (CZ • (CZ02 • (⊤⊥ {n} ↑ • CZ02)))
        ≈⟨ cright lemma-⊤⊥↑-CZ02 ⟩
      (CZ02⁻ • CZ⁻) • ⊤⊥ {n} ↑ ∎

    -- Right-multiplying lemma-⊤⊥↑-CZ02 by CZ02 ⁻¹.
    A·CZ02⁻ : ⊤⊥ {n} ↑ • CZ02⁻ ≈ (CZ • CZ02) • ⊤⊥ {n} ↑
    A·CZ02⁻ = begin
      ⊤⊥ {n} ↑ • CZ02⁻
        ≈⟨ cleft sym lemma-⊤⊥↑-CZ02 ⟩
      (CZ • (CZ02 • (⊤⊥ {n} ↑ • CZ02))) • CZ02⁻
        ≈⟨ assoc ⟩
      CZ • ((CZ02 • (⊤⊥ {n} ↑ • CZ02)) • CZ02⁻)
        ≈⟨ cright assoc ⟩
      CZ • (CZ02 • ((⊤⊥ {n} ↑ • CZ02) • CZ02⁻))
        ≈⟨ cright cright assoc ⟩
      CZ • (CZ02 • (⊤⊥ {n} ↑ • (CZ02 • CZ02⁻)))
        ≈⟨ cright cright cright lemma-CZ02-CZ02⁻ ⟩
      CZ • (CZ02 • (⊤⊥ {n} ↑ • ε))
        ≈⟨ cright cright right-unit ⟩
      CZ • (CZ02 • ⊤⊥ {n} ↑)
        ≈⟨ sym assoc ⟩
      (CZ • CZ02) • ⊤⊥ {n} ↑ ∎

    -- c13 iterated: A moves across CZ ⁻¹ turning it into CZ02 ⁻¹.
    A·CZ⁻ : ⊤⊥ {n} ↑ • CZ⁻ ≈ CZ02⁻ • ⊤⊥ {n} ↑
    A·CZ⁻ = lemma-Induction lemma-⊤⊥↑-CZ p-1

    tb : Word (Gen (₃₊ n))
    tb = ⊤⊥ {n} ↑

    tb³ : (tb • tb) • tb ≈ ε
    tb³ = lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊤⊥-cube3 n)

    -- The collapse.  Each A meeting a CZ02 on its right emits
    -- CZ02 ⁻¹ • CZ ⁻¹ and moves past it; the emitted factors cancel
    -- against the CZ02 and CZ already standing to the left, and after
    -- three such moves only the cube of A is left.
    cube-collapse : (CZ02 • tb) • ((CZ02 • tb) • (CZ02 • tb)) ≈ ε
    cube-collapse = begin
      (CZ02 • tb) • ((CZ02 • tb) • (CZ02 • tb))
        ≈⟨ assoc ⟩
      CZ02 • (tb • ((CZ02 • tb) • (CZ02 • tb)))
        ≈⟨ cright sym assoc ⟩
      CZ02 • ((tb • (CZ02 • tb)) • (CZ02 • tb))
        ≈⟨ cright cleft sym assoc ⟩
      CZ02 • (((tb • CZ02) • tb) • (CZ02 • tb))
        ≈⟨ cright cleft cleft A·CZ02 ⟩
      CZ02 • ((((CZ02⁻ • CZ⁻) • tb) • tb) • (CZ02 • tb))
        ≈⟨ cright cleft assoc ⟩
      CZ02 • (((CZ02⁻ • CZ⁻) • (tb • tb)) • (CZ02 • tb))
        ≈⟨ cright assoc ⟩
      CZ02 • ((CZ02⁻ • CZ⁻) • ((tb • tb) • (CZ02 • tb)))
        ≈⟨ cright assoc ⟩
      CZ02 • (CZ02⁻ • (CZ⁻ • ((tb • tb) • (CZ02 • tb))))
        ≈⟨ sym assoc ⟩
      (CZ02 • CZ02⁻) • (CZ⁻ • ((tb • tb) • (CZ02 • tb)))
        ≈⟨ cleft lemma-CZ02-CZ02⁻ ⟩
      ε • (CZ⁻ • ((tb • tb) • (CZ02 • tb)))
        ≈⟨ left-unit ⟩
      CZ⁻ • ((tb • tb) • (CZ02 • tb))
        ≈⟨ cright assoc ⟩
      CZ⁻ • (tb • (tb • (CZ02 • tb)))
        ≈⟨ cright cright sym assoc ⟩
      CZ⁻ • (tb • ((tb • CZ02) • tb))
        ≈⟨ cright cright cleft A·CZ02 ⟩
      CZ⁻ • (tb • (((CZ02⁻ • CZ⁻) • tb) • tb))
        ≈⟨ cright cright cleft assoc ⟩
      CZ⁻ • (tb • ((CZ02⁻ • (CZ⁻ • tb)) • tb))
        ≈⟨ cright cright assoc ⟩
      CZ⁻ • (tb • (CZ02⁻ • ((CZ⁻ • tb) • tb)))
        ≈⟨ cright sym assoc ⟩
      CZ⁻ • ((tb • CZ02⁻) • ((CZ⁻ • tb) • tb))
        ≈⟨ cright cleft A·CZ02⁻ ⟩
      CZ⁻ • (((CZ • CZ02) • tb) • ((CZ⁻ • tb) • tb))
        ≈⟨ cright assoc ⟩
      CZ⁻ • ((CZ • CZ02) • (tb • ((CZ⁻ • tb) • tb)))
        ≈⟨ cright assoc ⟩
      CZ⁻ • (CZ • (CZ02 • (tb • ((CZ⁻ • tb) • tb))))
        ≈⟨ sym assoc ⟩
      (CZ⁻ • CZ) • (CZ02 • (tb • ((CZ⁻ • tb) • tb)))
        ≈⟨ cleft lemma-CZ⁻-CZ ⟩
      ε • (CZ02 • (tb • ((CZ⁻ • tb) • tb)))
        ≈⟨ left-unit ⟩
      CZ02 • (tb • ((CZ⁻ • tb) • tb))
        ≈⟨ cright cright assoc ⟩
      CZ02 • (tb • (CZ⁻ • (tb • tb)))
        ≈⟨ cright sym assoc ⟩
      CZ02 • ((tb • CZ⁻) • (tb • tb))
        ≈⟨ cright cleft A·CZ⁻ ⟩
      CZ02 • ((CZ02⁻ • tb) • (tb • tb))
        ≈⟨ cright assoc ⟩
      CZ02 • (CZ02⁻ • (tb • (tb • tb)))
        ≈⟨ sym assoc ⟩
      (CZ02 • CZ02⁻) • (tb • (tb • tb))
        ≈⟨ cleft lemma-CZ02-CZ02⁻ ⟩
      ε • (tb • (tb • tb))
        ≈⟨ left-unit ⟩
      tb • (tb • tb)
        ≈⟨ sym assoc ⟩
      (tb • tb) • tb
        ≈⟨ tb³ ⟩
      ε ∎

  lemma-selinger-c14 : (⊤⊥ {n} ↑ • CZ ↓) ^ 3 ≈ ε
  lemma-selinger-c14 = begin
    (tb • CZ) • ((tb • CZ) • (tb • CZ))
      ≈⟨ cong lemma-⊤⊥↑-CZ (cong lemma-⊤⊥↑-CZ lemma-⊤⊥↑-CZ) ⟩
    (CZ02 • tb) • ((CZ02 • tb) • (CZ02 • tb))
      ≈⟨ cube-collapse ⟩
    ε ∎

  ------------------------------------------------------------------------
  -- c15, by transporting c14 along the transposition of wires 0 and 2
  --
  -- T = Ex • Ex ↑ • Ex exchanges wires 0 and 2 and fixes wire 1.  So it
  -- fixes H ↑, exchanges CZ with CZ ↑ (lemma-T-CZ) and exchanges the two
  -- swaps, hence carries ⊤⊥ ↑ to ⊥⊤ — which turns c14's element into
  -- c15's.  Since T is an involution, conjugating a cube is the cube of
  -- the conjugate, so c15 is c14 read through T.

  private
    -- Conjugation by T merges: it is a homomorphism, T • T being ε.
    merge : ∀ {X Y} → (T • (X • T)) • (T • (Y • T)) ≈ T • ((X • Y) • T)
    merge {X} {Y} = begin
      (T • (X • T)) • (T • (Y • T))
        ≈⟨ assoc ⟩
      T • ((X • T) • (T • (Y • T)))
        ≈⟨ cright assoc ⟩
      T • (X • (T • (T • (Y • T))))
        ≈⟨ cright cright sym assoc ⟩
      T • (X • ((T • T) • (Y • T)))
        ≈⟨ cright cright cleft lemma-T-T ⟩
      T • (X • (ε • (Y • T)))
        ≈⟨ cright cright left-unit ⟩
      T • (X • (Y • T))
        ≈⟨ cright sym assoc ⟩
      T • ((X • Y) • T) ∎

    -- T fixes wire 1, so it commutes with H ↑.
    lemma-T-H↑ : T • H ↑ ≈ H ↑ • T
    lemma-T-H↑ = begin
      (Ex • Ex ↑ • Ex) • H ↑
        ≈⟨ by-assoc auto ⟩
      Ex • (Ex ↑ • (Ex • H ↑))
        ≈⟨ cright cright lemma-Ex-H↑ ⟩
      Ex • (Ex ↑ • (H • Ex))
        ≈⟨ cright sym assoc ⟩
      Ex • ((Ex ↑ • H) • Ex)
        ≈⟨ cright cleft sym (lemma-comm-H-w↑ Ex) ⟩
      Ex • ((H • Ex ↑) • Ex)
        ≈⟨ by-assoc auto ⟩
      (Ex • H) • (Ex ↑ • Ex)
        ≈⟨ cleft lemma-Ex-H ⟩
      (H ↑ • Ex) • (Ex ↑ • Ex)
        ≈⟨ by-assoc auto ⟩
      H ↑ • (Ex • Ex ↑ • Ex) ∎

    lemma-T-CZ↑ : T • (CZ ↑ • T) ≈ CZ
    lemma-T-CZ↑ = begin
      T • (CZ ↑ • T)
        ≈⟨ cright cleft sym lemma-T-CZ ⟩
      T • ((T • (CZ • T)) • T)
        ≈⟨ cright assoc ⟩
      T • (T • ((CZ • T) • T))
        ≈⟨ sym assoc ⟩
      (T • T) • ((CZ • T) • T)
        ≈⟨ cleft lemma-T-T ⟩
      ε • ((CZ • T) • T)
        ≈⟨ left-unit ⟩
      (CZ • T) • T
        ≈⟨ assoc ⟩
      CZ • (T • T)
        ≈⟨ cright lemma-T-T ⟩
      CZ • ε
        ≈⟨ right-unit ⟩
      CZ ∎

    -- yang-baxter gives the other spelling of T, and the two swaps then
    -- cancel in pairs.
    lemma-T-Ex↑ : T • (Ex ↑ • T) ≈ Ex
    lemma-T-Ex↑ = begin
      T • (Ex ↑ • T)
        ≈⟨ cleft sym (axiom yang-baxter) ⟩
      (Ex ↑ • Ex ↓ • Ex ↑) • (Ex ↑ • T)
        ≈⟨ by-assoc auto ⟩
      Ex ↑ • (Ex • ((Ex ↑ • Ex ↑) • T))
        ≈⟨ cright cright cleft lemma-Ex↑-Ex↑ ⟩
      Ex ↑ • (Ex • (ε • T))
        ≈⟨ cright cright left-unit ⟩
      Ex ↑ • (Ex • T)
        ≈⟨ by-assoc auto ⟩
      Ex ↑ • ((Ex • Ex) • (Ex ↑ • Ex))
        ≈⟨ cright cleft lemma-Ex-Ex ⟩
      Ex ↑ • (ε • (Ex ↑ • Ex))
        ≈⟨ cright left-unit ⟩
      Ex ↑ • (Ex ↑ • Ex)
        ≈⟨ sym assoc ⟩
      (Ex ↑ • Ex ↑) • Ex
        ≈⟨ cleft lemma-Ex↑-Ex↑ ⟩
      ε • Ex
        ≈⟨ left-unit ⟩
      Ex ∎

    lemma-T-ₕ|ₕ↑ : T • ((H ↑ • CZ ↑ • H ↑) • T) ≈ ʰ|ʰ
    lemma-T-ₕ|ₕ↑ = begin
      T • ((H ↑ • CZ ↑ • H ↑) • T)
        ≈⟨ cright cleft sym assoc ⟩
      T • (((H ↑ • CZ ↑) • H ↑) • T)
        ≈⟨ cright assoc ⟩
      T • ((H ↑ • CZ ↑) • (H ↑ • T))
        ≈⟨ cright cright sym lemma-T-H↑ ⟩
      T • ((H ↑ • CZ ↑) • (T • H ↑))
        ≈⟨ cright assoc ⟩
      T • (H ↑ • (CZ ↑ • (T • H ↑)))
        ≈⟨ sym assoc ⟩
      (T • H ↑) • (CZ ↑ • (T • H ↑))
        ≈⟨ cleft lemma-T-H↑ ⟩
      (H ↑ • T) • (CZ ↑ • (T • H ↑))
        ≈⟨ assoc ⟩
      H ↑ • (T • (CZ ↑ • (T • H ↑)))
        ≈⟨ cright cright sym assoc ⟩
      H ↑ • (T • ((CZ ↑ • T) • H ↑))
        ≈⟨ cright sym assoc ⟩
      H ↑ • ((T • (CZ ↑ • T)) • H ↑)
        ≈⟨ cright cleft lemma-T-CZ↑ ⟩
      H ↑ • (CZ • H ↑) ∎

    lemma-T-⊤⊥↑ : T • (⊤⊥ {n} ↑ • T) ≈ ⊥⊤
    lemma-T-⊤⊥↑ = begin
      T • (⊤⊥ {n} ↑ • T)
        ≈⟨ cright cleft ⊤⊥↑-split ⟩
      T • ((ₕ|ₕ ↑ • Ex ↑) • T)
        ≈⟨ sym merge ⟩
      (T • (ₕ|ₕ ↑ • T)) • (T • (Ex ↑ • T))
        ≈⟨ cong lemma-T-ₕ|ₕ↑ lemma-T-Ex↑ ⟩
      ʰ|ʰ • Ex
        ≈⟨ cleft sym lemma-ʰ|ʰ-conj ⟩
      (Ex • (ₕ|ₕ • Ex)) • Ex
        ≈⟨ assoc ⟩
      Ex • ((ₕ|ₕ • Ex) • Ex)
        ≈⟨ cright assoc ⟩
      Ex • (ₕ|ₕ • (Ex • Ex))
        ≈⟨ cright cright lemma-Ex-Ex ⟩
      Ex • (ₕ|ₕ • ε)
        ≈⟨ cright right-unit ⟩
      Ex • ₕ|ₕ
        ≈⟨ sym lemma-⊥⊤-simple ⟩
      ⊥⊤ ∎

  lemma-selinger-c15 : (⊥⊤ ↓ • CZ ↑) ^ 3 ≈ ε
  lemma-selinger-c15 = begin
    (⊥⊤ • CZ ↑) • ((⊥⊤ • CZ ↑) • (⊥⊤ • CZ ↑))
      ≈⟨ cong conj (cong conj conj) ⟩
    (T • ((tb • CZ) • T)) • ((T • ((tb • CZ) • T)) • (T • ((tb • CZ) • T)))
      ≈⟨ cright merge ⟩
    (T • ((tb • CZ) • T)) • (T • (((tb • CZ) • (tb • CZ)) • T))
      ≈⟨ merge ⟩
    T • (((tb • CZ) • ((tb • CZ) • (tb • CZ))) • T)
      ≈⟨ cright cleft lemma-selinger-c14 ⟩
    T • (ε • T)
      ≈⟨ cright left-unit ⟩
    T • T
      ≈⟨ lemma-T-T ⟩
    ε ∎
    where
    conj : ⊥⊤ • CZ ↑ ≈ T • ((tb • CZ) • T)
    conj = begin
      ⊥⊤ • CZ ↑
        ≈⟨ cong (sym lemma-T-⊤⊥↑) (sym lemma-T-CZ) ⟩
      (T • (tb • T)) • (T • (CZ • T))
        ≈⟨ merge ⟩
      T • ((tb • CZ) • T) ∎

  lemma-⊥⊤↑-CZ02 : ⊥⊤ {n} ↑ • CZ02 ≈ CZ • ⊥⊤ {n} ↑
  lemma-⊥⊤↑-CZ02 = •-cancelˡ {g = ⊤⊥ {n} ↑} (begin
    ⊤⊥ {n} ↑ • (⊥⊤ {n} ↑ • CZ02)
      ≈⟨ sym assoc ⟩
    (⊤⊥ {n} ↑ • ⊥⊤ {n} ↑) • CZ02
      ≈⟨ cleft (lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊤⊥-⊥⊤ n)) ⟩
    ε • CZ02
      ≈⟨ left-unit ⟩
    CZ02
      ≈⟨ sym right-unit ⟩
    CZ02 • ε
      ≈⟨ cright sym (lemma-cong↑ _ _ (Ex-Conjugation.lemma-⊤⊥-⊥⊤ n)) ⟩
    CZ02 • (⊤⊥ {n} ↑ • ⊥⊤ {n} ↑)
      ≈⟨ sym assoc ⟩
    (CZ02 • ⊤⊥ {n} ↑) • ⊥⊤ {n} ↑
      ≈⟨ cleft sym lemma-⊤⊥↑-CZ ⟩
    (⊤⊥ {n} ↑ • CZ) • ⊥⊤ {n} ↑
      ≈⟨ assoc ⟩
    ⊤⊥ {n} ↑ • (CZ • ⊥⊤ {n} ↑) ∎)

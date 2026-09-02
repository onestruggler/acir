{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- Multiplier arithmetic on one wire: the six one-wire axioms and what
-- they give.  Split out of the former monolithic Lemmas.agda; see
-- Lemmas.agda for the layering.
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
open import Data.Fin.Properties using (toℕ-inject₁ ; toℕ-fromℕ< ; toℕ-injective)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat


module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.OneWire
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen

open Clifford-Relations
open Lemmas-Clifford
  using (lemma-↑^ ; lemma-Induction ; lemma-Inductionˡ
        ; lemma-comm-S-w↑ ; lemma-comm-H-w↑ ; lemma-comm-Hᵏ-w↑
        ; lemma-comm-Z-w↑ ; lemma-comm-X-w↑ ; lemma-comm-CZ-w↑)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Multiplier arithmetic on one wire
--
-- Paper-V1 has five one-wire axioms — order-S, order-H, M-power,
-- semi-MR, comm-HHSHHS — where Simplified-V1 has those and order-SH.
-- The missing one is not a loss: lemma-order-SH below derives it, and
-- with it in hand every one-wire lemma of Simplified-V1.Lemmas.Lemmas1
-- holds here by the same proof.  The ones below are ported verbatim from
-- there, because the proof terms are tied to a particular relation and
-- cannot be reused across the two.
--
-- lemma-M-mul is what the three-wire derivations need: M ½ • M 2 is
-- M 1 is ε, and inserting that resolution of the identity is the step
-- that lets R¹⁴/R¹⁵ rescale a CZ exponent.

module One-Wire (n : ℕ) where

  open PB ((₁₊ n) QRel,_===_) hiding (_===_)
  open PP ((₁₊ n) QRel,_===_)

  -- M y mentions y only through the two field values x and x⁻¹, so the
  -- congruence is one cong₂ over the shape once both are identified:
  -- x by the hypothesis, x⁻¹ by aux-eq below.  (Over the old RHR
  -- spelling this was a ≡-Reasoning chain; the SHS spelling repeats each
  -- exponent, so naming the shape is shorter than rewriting in place.)
  aux-M≡M : ∀ y y' -> y .proj₁ ≡ y' .proj₁ -> M {n = n} y ≡ M y'
  aux-M≡M y y' eq = Eq.cong₂ SHS' aux-eq eq
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

  ------------------------------------------------------------------------
  -- From the XMg axioms to the Mg forms
  --
  -- The multiplier axioms are stated over XMg = XM g′, and XM y is M at
  -- the INVERSE unit (Syntactics.XM≡M⁻¹).  So M-power reads
  --
  --     XMg ^ toℕ k ≈ M ((g^ k) ⁻¹),
  --
  -- which is the Mg power law run at g ⁻¹ — a primitive root as well, so
  -- no strength is lost, but the Mg forms have to be recovered before
  -- anything downstream can use them.  That recovery is this section.
  --
  -- lemma-M-mul never needed more than "every M x is a power of the
  -- generator", so it is proved from the XMg form directly (lemma-M-log);
  -- the Mg power law then follows from it by induction, and the two
  -- semi-rules by cancellation, once Mg and XMg are known to be mutually
  -- inverse.

  -- The inverse of a unit depends only on its value.  This is exactly
  -- aux-M≡M's own side condition, named so the XM side can reuse it.
  aux-inv≡ : ∀ (y y' : ℤ* ₚ) -> y .proj₁ ≡ y' .proj₁
           -> (y ⁻¹) .proj₁ ≡ (y' ⁻¹) .proj₁
  aux-inv≡ y y' eq = begin
    x⁻¹ ≡⟨  Eq.sym  (*-identityʳ x⁻¹) ⟩
    x⁻¹ * ₁ ≡⟨ Eq.cong (x⁻¹ *_) (Eq.sym (lemma-⁻¹ʳ x' {{nztoℕ {y = x'} {neq0 = y' .proj₂} }})) ⟩
    x⁻¹ * (x' * x'⁻¹) ≡⟨ Eq.sym (*-assoc x⁻¹ x' x'⁻¹) ⟩
    (x⁻¹ * x') * x'⁻¹ ≡⟨ Eq.cong (\ xx -> (x⁻¹ * xx) * x'⁻¹) (Eq.sym eq) ⟩
    (x⁻¹ * x) * x'⁻¹ ≡⟨ Eq.cong (_* x'⁻¹) (lemma-⁻¹ˡ x {{nztoℕ {y = x} {neq0 = y .proj₂} }}) ⟩
    ₁ * x'⁻¹ ≡⟨ *-identityˡ x'⁻¹ ⟩
    x'⁻¹ ∎
    where
    open ≡-Reasoning
    x = y .proj₁
    x⁻¹ = ((y ⁻¹) .proj₁ )
    x' = y' .proj₁
    x'⁻¹ = ((y' ⁻¹) .proj₁ )

  -- The axiom with the bridge applied: a power of XMg is an M.
  lemma-XMg^ : ∀ (k : ℤ ₚ) -> XMg {n} ^ toℕ k ≈ M ((g^ k) ⁻¹)
  lemma-XMg^ k = begin
    XMg ^ toℕ k    ≈⟨ axiom (M-power k) ⟩
    XM (g^ k)      ≡⟨ XM≡M⁻¹ (g^ k) ⟩
    M ((g^ k) ⁻¹) ∎
    where
    open SR word-setoid

  -- The modulus of a bare ₁ is not inferable inside the instance argument
  -- below (cf. 2ₚ further down), so it is pinned down here.
  1ₚ' : ℤ ₚ
  1ₚ' = ₁

  -- 1 is its own inverse.
  aux-1⁻¹ : (((₁ , λ ())) ⁻¹) .proj₁ ≡ ₁
  aux-1⁻¹ = begin
    ((₁ , λ ()) ⁻¹) .proj₁
      ≡⟨ Eq.sym (*-identityˡ ((((₁ , λ ())) ⁻¹) .proj₁)) ⟩
    ₁ * ((₁ , λ ()) ⁻¹) .proj₁
      ≡⟨ lemma-⁻¹ʳ 1ₚ' {{nztoℕ {y = 1ₚ'} {neq0 = λ ()}}} ⟩
    ₁ ∎
    where open ≡-Reasoning

  lemma-M1 : M (₁ , λ ()) ≈ ε
  lemma-M1 = begin
    M (₁ , λ ()) ≡⟨ aux-M≡M ((₁ , λ ())) ((g^ ₀) ⁻¹) (Eq.sym aux) ⟩
    M ((g^ ₀) ⁻¹) ≈⟨ sym (lemma-XMg^ ₀) ⟩
    XMg ^ 0 ≈⟨ refl ⟩
    ε ∎
    where
    -- g ^ 0 is 1, and 1 is its own inverse.
    aux : ((g^ ₀) ⁻¹) .proj₁ ≡ ₁
    aux = Eq.trans (aux-inv≡ (g^ ₀) (₁ , λ ()) auto) aux-1⁻¹

    open SR word-setoid

  -- M₁ unfolded.  At x = 1 both of the shape's exponents are
  -- (1 - 1)·½ = 0, so the Pauli prefix vanishes outright and what is left
  -- is S • H three times over.  (Contrast lemma-M₋₁-unfold in Lemmas.XZ,
  -- where at -1 the prefix collapses to Z⁻¹ • X rather than to nothing.)
  lemma-M1-unfold : M₁ {n} ≈ (S • H) ^ 3
  lemma-M1-unfold = begin
    M₁
      ≡⟨ Eq.cong (λ z → SHS' z 1ₚ') aux-1⁻¹ ⟩
    Z^ ((₁ + - ₁) * 1/2) • X^ ((₁ + - ₁) * 1/2) • S • H • S • H • S • H
      ≡⟨ Eq.cong (λ u → Z^ u • X^ u • S • H • S • H • S • H) zz ⟩
    ε • ε • S • H • S • H • S • H
      ≈⟨ left-unit ⟩
    ε • S • H • S • H • S • H
      ≈⟨ left-unit ⟩
    S • H • S • H • S • H
      ≈⟨ by-assoc auto ⟩
    (S • H) ^ 3 ∎
    where
    open SR word-setoid

    -- (1 + -1)·½ is 0·½ is 0.
    zz : (₁ + - ₁) * 1/2 ≡ ₀
    zz = Eq.trans (Eq.cong (_* 1/2) (+-inverseʳ ₁)) (*-zeroˡ 1/2)

  -- …and hence (S • H) ^ 3 ≈ ε.  Figure 1 states this as an axiom and
  -- Paper-V0 keeps it as one, but Paper-V1 does not need it: M-power at
  -- k = 0 already gives M₁ ≈ ε (lemma-M1 above), and under the SHS'
  -- spelling M₁ *is* (S • H) ^ 3.  Under Paper-V0's R-spelling the two
  -- are different words — M₁ is (R • H) ^ 3 there — which is why the
  -- axiom survives on that side.
  --
  -- This is what Shared.PauliBase.Calculus takes as order-SH', and it is
  -- the only place the fact is used in the whole development.
  lemma-order-SH : (S • H) ^ 3 ≈ ε
  lemma-order-SH = trans (sym lemma-M1-unfold) lemma-M1
    where
    open SR word-setoid

  -- g ^ (p-1) is 1 (Fermat), so it and its inverse are both trivial.
  aux-g^p-1 : (g^ (fromℕ< (NP.n<1+n p-1))) .proj₁ ≡ ₁
  aux-g^p-1 = begin
    (g^ (fromℕ< (NP.n<1+n p-1))) .proj₁
      ≡⟨ Eq.cong (g ^′_) (toℕ-fromℕ< (NP.n<1+n p-1)) ⟩
    g ^′ p-1  ≡⟨ Fermat's-little-theorem' ⟩
    ₁ ∎
    where open ≡-Reasoning

  lemma-XMg^p-1=ε : XMg {n} ^ p-1 ≈ ε
  lemma-XMg^p-1=ε = begin
    XMg ^ p-1
      ≡⟨ Eq.cong (XMg ^_) (Eq.sym (toℕ-fromℕ< (NP.n<1+n p-1))) ⟩
    XMg ^ toℕ p-1'
      ≈⟨ lemma-XMg^ p-1' ⟩
    M ((g^ p-1') ⁻¹)
      ≡⟨ aux-M≡M ((g^ p-1') ⁻¹) (₁ , λ ())
                 (Eq.trans (aux-inv≡ (g^ p-1') (₁ , λ ()) aux-g^p-1) aux-1⁻¹) ⟩
    M (₁ , λ ())
      ≈⟨ lemma-M1 ⟩
    ε ∎
    where
    p-1' = fromℕ< (NP.n<1+n p-1)
    open SR word-setoid

  aux-XMg^[kp-1] : ∀ k -> XMg {n} ^ (k Nat.* p-1) ≈ ε
  aux-XMg^[kp-1] k = begin
    XMg ^ (k Nat.* p-1) ≈⟨ refl' (Eq.cong (XMg ^_) (NP.*-comm k p-1)) ⟩
    XMg ^ (p-1 Nat.* k) ≈⟨ sym (^^ XMg p-1 k) ⟩
    (XMg ^ p-1) ^ k ≈⟨ ^-cong (XMg ^ p-1) ε k lemma-XMg^p-1=ε ⟩
    ε ^ k ≈⟨ ε^k=ε k ⟩
    ε ∎
    where
    open SR word-setoid

  -- Inversion is multiplicative.  Not in ForStdlib, and the XM side of
  -- lemma-M-mul needs it: the discrete logs there are taken of inverses.
  aux-mul-inv : ∀ (x y : ℤ* ₚ)
              -> ((x *' y) ⁻¹) .proj₁ ≡ (x ⁻¹) .proj₁ * (y ⁻¹) .proj₁
  aux-mul-inv x y = begin
    a                    ≡⟨ Eq.sym (*-identityʳ a) ⟩
    a * ₁                ≡⟨ Eq.cong (a *_) (Eq.sym claim) ⟩
    a * ((xv * yv) * (u * v))
      ≡⟨ Eq.sym (*-assoc a (xv * yv) (u * v)) ⟩
    (a * (xv * yv)) * (u * v)
      ≡⟨ Eq.cong (_* (u * v)) (lemma-⁻¹ˡ (xv * yv) {{nztoℕ {y = xv * yv} {neq0 = (x *' y) .proj₂} }}) ⟩
    ₁ * (u * v)          ≡⟨ *-identityˡ (u * v) ⟩
    u * v ∎
    where
    open ≡-Reasoning
    xv = x .proj₁
    yv = y .proj₁
    u = (x ⁻¹) .proj₁
    v = (y ⁻¹) .proj₁
    a = ((x *' y) ⁻¹) .proj₁

    claim : (xv * yv) * (u * v) ≡ ₁
    claim = begin
      (xv * yv) * (u * v)  ≡⟨ *-assoc xv yv (u * v) ⟩
      xv * (yv * (u * v))  ≡⟨ Eq.cong (xv *_) (Eq.sym (*-assoc yv u v)) ⟩
      xv * ((yv * u) * v)  ≡⟨ Eq.cong (\ w -> xv * (w * v)) (*-comm yv u) ⟩
      xv * ((u * yv) * v)  ≡⟨ Eq.cong (xv *_) (*-assoc u yv v) ⟩
      xv * (u * (yv * v))
        ≡⟨ Eq.cong (\ w -> xv * (u * w)) (lemma-⁻¹ʳ yv {{nztoℕ {y = yv} {neq0 = y .proj₂} }}) ⟩
      xv * (u * ₁)         ≡⟨ Eq.cong (xv *_) (*-identityʳ u) ⟩
      xv * u               ≡⟨ lemma-⁻¹ʳ xv {{nztoℕ {y = xv} {neq0 = x .proj₂} }} ⟩
      ₁ ∎

  -- Every M is a power of XMg: the axiom says XMg ^ n is M at the inverse
  -- of g ^ n, so take the discrete log of x ⁻¹ rather than of x.
  lemma-M-log : ∀ (x : ℤ* ₚ)
              -> M {n = n} x ≈ XMg ^ toℕ (inject₁ (g-gen (x ⁻¹) .proj₁))
  lemma-M-log x = begin
    M x               ≡⟨ aux-M≡M x ((g^ k) ⁻¹) (Eq.sym eqk) ⟩
    M ((g^ k) ⁻¹)     ≈⟨ sym (lemma-XMg^ k) ⟩
    XMg ^ toℕ k ∎
    where
    k = inject₁ (g-gen (x ⁻¹) .proj₁)

    -- ((g ^ k) ⁻¹) is x, because g ^ k is x ⁻¹ and inversion is involutive.
    eqk : ((g^ k) ⁻¹) .proj₁ ≡ x .proj₁
    eqk = Eq.trans (aux-inv≡ (g^ k) (x ⁻¹) (lemma-log-inject (x ⁻¹)))
                   (inv-involutive x)

    open SR word-setoid

  lemma-M-mul : ∀ x y -> M x • M y ≈ M (x *' y)
  lemma-M-mul x y = begin
    M x • M y ≈⟨ cong (lemma-M-log x) (lemma-M-log y) ⟩
    XMg ^ toℕ k • XMg ^ toℕ l ≈⟨ sym (^-+ XMg (toℕ k) (toℕ l)) ⟩
    XMg ^ [k+l] ≡⟨ Eq.cong (XMg ^_) (m≡m%n+[m/n]*n [k+l] p-1) ⟩
    XMg ^ ([k+l]%p-1 Nat.+ [k+l]/p-1 Nat.* p-1) ≈⟨ ^-+ XMg [k+l]%p-1 (([k+l]/p-1 Nat.* p-1)) ⟩
    XMg ^ [k+l]%p-1 • XMg ^ ([k+l]/p-1 Nat.* p-1) ≈⟨ (cright trans refl (aux-XMg^[kp-1] [k+l]/p-1)) ⟩
    XMg ^ [k+l]%p-1 • ε ≈⟨ right-unit ⟩
    XMg ^ [k+l]%p-1 ≡⟨ Eq.cong (XMg ^_) (Eq.sym (toℕ-fromℕ< (m%n<n [k+l] p-1))) ⟩
    XMg ^ toℕ ( (fromℕ< (m%n<n [k+l] p-1))) ≡⟨ Eq.cong (XMg ^_) (Eq.sym (toℕ-inject₁ ((fromℕ< (m%n<n [k+l] p-1))))) ⟩
    XMg ^ toℕ c ≈⟨ lemma-XMg^ c ⟩
    M ((g^ c) ⁻¹) ≡⟨ aux-M≡M ((g^ c) ⁻¹) (x *' y) aux-3 ⟩
    M (x *' y) ∎
    where
    -- The logs are of the INVERSES, which is what the XMg form gives.
    k = inject₁ (g-gen (x ⁻¹) .proj₁)
    l = inject₁ (g-gen (y ⁻¹) .proj₁)

    [k+l] = toℕ k Nat.+ toℕ l
    [k+l]%p-1 = [k+l] Nat.% p-1
    [k+l]/p-1 = [k+l] Nat./ p-1

    c = inject₁ (fromℕ< (m%n<n [k+l] p-1))

    aux-0 : ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁ ≡ ((x *' y) ⁻¹) .proj₁
    aux-0 = begin
      ((g^′ toℕ k) *' (g^′ toℕ l)) .proj₁ ≡⟨ auto ⟩
      (g^′ toℕ k) .proj₁ * (g^′ toℕ l) .proj₁ ≡⟨ Eq.cong₂ (\ xx yy -> (xx * yy) ) (lemma-log-inject (x ⁻¹)) (lemma-log-inject (y ⁻¹)) ⟩
      (x ⁻¹) .proj₁ * (y ⁻¹) .proj₁ ≡⟨ Eq.sym (aux-mul-inv x y) ⟩
      ((x *' y) ⁻¹) .proj₁ ∎
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

    -- g ^ c is the inverse of x · y, so its own inverse is x · y.
    aux-3 : ((g^ c) ⁻¹) .proj₁ ≡ (x *' y) .proj₁
    aux-3 = Eq.trans (aux-inv≡ (g^ c) ((x *' y) ⁻¹)
                               (Eq.trans aux-2 (Eq.trans aux-1 aux-0)))
                     (inv-involutive (x *' y))

    -- Opened last, as in Simplified-V1: an `open` in a where-block is
    -- scoped from its own position onward, so putting the setoid
    -- reasoning here keeps `begin_` unambiguous inside the aux-blocks
    -- above, which use ≡-Reasoning instead.
    open SR word-setoid

  ------------------------------------------------------------------------
  -- The Mg forms of the three axioms
  --
  -- With lemma-M-mul in hand the rest is short.  The power law is an
  -- induction on the exponent, and XMg is Mg's inverse — M g′ • M (g′ ⁻¹)
  -- is M ₁ is ε — so the two semi-rules come back by cancelling XMg off
  -- both sides of the axiom.

  -- The power law over ℕ; lemma-M-power is this at an exponent from ℤ ₚ.
  lemma-Mgⁿ : ∀ (m : ℕ) -> Mg {n} ^ m ≈ M (g^′ m)
  lemma-Mgⁿ ₀ = begin
    ε                ≈⟨ sym lemma-M1 ⟩
    M (₁ , λ ())     ≡⟨ aux-M≡M (₁ , λ ()) (g^′ 0) auto ⟩
    M (g^′ 0) ∎
    where open SR word-setoid
  lemma-Mgⁿ ₁ = refl' (aux-M≡M g′ (g^′ 1) (Eq.sym (*-identityʳ g)))
  lemma-Mgⁿ (₂₊ m) = begin
    Mg • Mg ^ ₁₊ m          ≈⟨ cright lemma-Mgⁿ (₁₊ m) ⟩
    M g′ • M (g^′ ₁₊ m)     ≈⟨ lemma-M-mul g′ (g^′ ₁₊ m) ⟩
    M (g′ *' g^′ ₁₊ m)      ≡⟨ aux-M≡M (g′ *' g^′ ₁₊ m) (g^′ ₂₊ m) auto ⟩
    M (g^′ ₂₊ m) ∎
    where open SR word-setoid

  lemma-M-power : ∀ (k : ℤ ₚ) -> Mg^ k ≈ M (g^ k)
  lemma-M-power k = begin
    Mg ^ toℕ k     ≈⟨ lemma-Mgⁿ (toℕ k) ⟩
    M (g^′ toℕ k)  ≡⟨ aux-M≡M (g^′ toℕ k) (g^ k) auto ⟩
    M (g^ k) ∎
    where open SR word-setoid

  -- Mg and XMg are mutually inverse.
  lemma-Mg-XMg : Mg {n} • XMg ≈ ε
  lemma-Mg-XMg = begin
    Mg • XMg            ≡⟨ Eq.cong (Mg •_) (XM≡M⁻¹ g′) ⟩
    M g′ • M (g′ ⁻¹)    ≈⟨ lemma-M-mul g′ (g′ ⁻¹) ⟩
    M (g′ *' (g′ ⁻¹))   ≡⟨ aux-M≡M (g′ *' (g′ ⁻¹)) (₁ , λ ())
                                   (lemma-⁻¹ʳ g {{nztoℕ {y = g} {neq0 = g≠0} }}) ⟩
    M (₁ , λ ())        ≈⟨ lemma-M1 ⟩
    ε ∎
    where open SR word-setoid

  lemma-XMg-Mg : XMg {n} • Mg ≈ ε
  lemma-XMg-Mg = begin
    XMg • Mg            ≡⟨ Eq.cong (_• Mg) (XM≡M⁻¹ g′) ⟩
    M (g′ ⁻¹) • M g′    ≈⟨ lemma-M-mul (g′ ⁻¹) g′ ⟩
    M ((g′ ⁻¹) *' g′)   ≡⟨ aux-M≡M ((g′ ⁻¹) *' g′) (₁ , λ ())
                                   (lemma-⁻¹ˡ g {{nztoℕ {y = g} {neq0 = g≠0} }}) ⟩
    M (₁ , λ ())        ≈⟨ lemma-M1 ⟩
    ε ∎
    where open SR word-setoid

  -- semi-MR, back in the Mg spelling.  The axiom says conjugating by XMg
  -- takes R ^ (g·g) to R; cancelling XMg on both sides turns that into
  -- "conjugating by Mg takes R to R ^ (g·g)", which is the original rule.
  lemma-semi-MR : Mg {n} • R ≈ R^ (g * g) • Mg
  lemma-semi-MR = begin
    Mg • R
      ≈⟨ sym right-unit ⟩
    (Mg • R) • ε
      ≈⟨ cright sym lemma-XMg-Mg ⟩
    (Mg • R) • (XMg • Mg)
      ≈⟨ assoc ⟩
    Mg • (R • (XMg • Mg))
      ≈⟨ cright sym assoc ⟩
    Mg • ((R • XMg) • Mg)
      ≈⟨ cright cleft sym (axiom semi-MR) ⟩
    Mg • ((XMg • R^ (g * g)) • Mg)
      ≈⟨ cright assoc ⟩
    Mg • (XMg • (R^ (g * g) • Mg))
      ≈⟨ sym assoc ⟩
    (Mg • XMg) • (R^ (g * g) • Mg)
      ≈⟨ cleft lemma-Mg-XMg ⟩
    ε • (R^ (g * g) • Mg)
      ≈⟨ left-unit ⟩
    R^ (g * g) • Mg ∎
    where open SR word-setoid

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
    Mg ^ j₋    ≈⟨ lemma-M-power k₋ ⟩
    M (g^ k₋)  ≡⟨ aux-M≡M (g^ k₋) -'₁ e₋ ⟩
    M₋₁ ∎
    where open SR word-setoid

  ------------------------------------------------------------------------
  -- Moving S through the H-H-S-H-H block, and Z as a power
  --
  -- Ported from Simplified-V1.Lemmas: both are one-wire facts over
  -- comm-HHSHHS and order-H, which Paper-V1 shares verbatim.  They are
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

  -- The multiplier by −1 conjugates S into S • Z.
  --
  -- This is Z's own definition, Z = H ² • S • H ² • S ⁻¹, read as a
  -- statement about M₋₁ • S • M₋₁ — the S ⁻¹ cancels and what is left is
  -- Z • S.  Ex-Conjugation needs it one wire up: it is the reason the
  -- wire-1 multiplier drops a Z ↑ when it flips blake-c12, and that Z ↑
  -- is the one in rel-X↓-CZ (see Ex-Conjugation.lemma-rel-X↓-CZ).
  lemma-M₋₁-S : M₋₁ • S ≈ (S • Z) • M₋₁
  lemma-M₋₁-S = begin
    M₋₁ • S
      ≈⟨ sym right-unit ⟩
    (M₋₁ • S) • ε
      ≈⟨ cright sym lemma-M₋₁^2 ⟩
    (M₋₁ • S) • (M₋₁ • M₋₁)
      ≈⟨ sym assoc ⟩
    ((M₋₁ • S) • M₋₁) • M₋₁
      ≈⟨ cleft assoc ⟩
    (M₋₁ • (S • M₋₁)) • M₋₁
      ≈⟨ cleft lemma-ZS ⟩
    (Z • S) • M₋₁
      ≈⟨ cleft lemma-comm-Z-S ⟩
    (S • Z) • M₋₁ ∎
    where
    open SR word-setoid

    S⁻¹S : S⁻¹ • S ≈ ε
    S⁻¹S = begin
      S ^ p-1 • S        ≈⟨ sym (^-+ S p-1 1) ⟩
      S ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (S ^_) (NP.+-comm p-1 1) ⟩
      S ^ p              ≈⟨ lemma-order-S ⟩
      ε ∎

    Z-split : Z ≈ M₋₁ • (S • (M₋₁ • S⁻¹))
    Z-split = begin
      H • (H • (S • (H • (H • S⁻¹))))
        ≈⟨ sym assoc ⟩
      (H • H) • (S • (H • (H • S⁻¹)))
        ≈⟨ cright cright sym assoc ⟩
      (H • H) • (S • ((H • H) • S⁻¹))
        ≈⟨ cong (axiom order-H) (cright cleft axiom order-H) ⟩
      M₋₁ • (S • (M₋₁ • S⁻¹)) ∎

    lemma-ZS : M₋₁ • (S • M₋₁) ≈ Z • S
    lemma-ZS = sym (begin
      Z • S
        ≈⟨ cleft Z-split ⟩
      (M₋₁ • (S • (M₋₁ • S⁻¹))) • S
        ≈⟨ assoc ⟩
      M₋₁ • ((S • (M₋₁ • S⁻¹)) • S)
        ≈⟨ cright assoc ⟩
      M₋₁ • (S • ((M₋₁ • S⁻¹) • S))
        ≈⟨ cright cright assoc ⟩
      M₋₁ • (S • (M₋₁ • (S⁻¹ • S)))
        ≈⟨ cright cright cright S⁻¹S ⟩
      M₋₁ • (S • (M₋₁ • ε))
        ≈⟨ cright cright right-unit ⟩
      M₋₁ • (S • M₋₁) ∎)

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
  -- which is lemma-rel-X↑-CZ.

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
  -- (lemma-M₋₁-R has moved to Lemmas.XZ.  Under the old RHR spelling it
  -- was immediate — M₋₁ *was* that R-word, so order-H closed it — but
  -- with the SHS' spelling M₋₁ is an S-word with a Pauli prefix, so the
  -- two spellings have to be reconciled, and that needs the Pauli
  -- calculus.  Its one client, ExConjC, imports XZ anyway.)


{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The one-wire layer of the Paper-V0 calculus, over any relation.
--
-- Paper-V0 spells the multiplier over R = S • Z ^ ½, and these are its
-- one-wire facts: the multiplier arithmetic, the Paulis and their
-- conjugation by H, and group-likeness.  Each module takes a relation and
-- the Paper-V0 rules it uses, each stated as Paper-V0's axiom, as an
-- equation in that relation.  Paper-V0.Lemmas instantiates them at
-- Paper-V0's own rules; any relation that proves those rules can do the
-- same.
--
--   One-Wire         multiplier arithmetic, the Paulis' orders, Z • S,
--                    the Euler decomposition of M₋₁: from order-S,
--                    order-H, M-power and comm-HHSHHS (One-Wire-Rules)
--   One-Wire-MR      semi-MR back in the Mg spelling: the one module that
--                    takes semi-MR, which nothing else in the calculus
--                    uses
--   Paper-GroupLike  group-likeness, for a whole family of relations
--   One-Wire-Group   Pauli conjugation by H and H ^ 2, which needs
--                    cancellation
--
-- Paper-V0's sixth one-wire rule, order-SH, is used by none of them.
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

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas.OneWire
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

-- The words only: the relation is a parameter of every module below.
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen

open Clifford-Relations
  using ( Z ; X ; Z⁻¹ ; X⁻¹ ; Z^ ; X^ ; R ; R^ ; RHR ; M ; XM ; XM≡M⁻¹
        ; M₁ ; M₋₁ ; Mg ; Mg^ ; XMg ; XMg^ )

------------------------------------------------------------------------
-- Word lemmas at an arbitrary relation
--
-- These mention no rule at all, so they are stated once for any Γ.  The
-- two induction lemmas are copies of Syntactics.Lemmas-Clifford's, which
-- are stated over Paper-V0's relation and so cannot serve another.

module _ {A : Set} {Γ : WRel A} where

  open PB Γ
  open PP Γ
  open SR word-setoid

  -- Powers of a word of order p depend only on the exponent mod p.
  lemma-pow-mod : ∀ {w : Word A} → w ^ p ≈ ε → ∀ m → w ^ m ≈ w ^ (m Nat.% p)
  lemma-pow-mod {w} op m = begin
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
    aux : w ^ ((m Nat./ p) Nat.* p) ≈ ε
    aux = begin
      w ^ ((m Nat./ p) Nat.* p)  ≈⟨ refl' (Eq.cong (w ^_) (NP.*-comm (m Nat./ p) p)) ⟩
      w ^ (p Nat.* (m Nat./ p))  ≈⟨ sym (^^ w p (m Nat./ p)) ⟩
      (w ^ p) ^ (m Nat./ p)      ≈⟨ ^-cong (w ^ p) ε (m Nat./ p) op ⟩
      ε ^ (m Nat./ p)            ≈⟨ ε^k=ε (m Nat./ p) ⟩
      ε ∎

  -- A word that moves past v by turning it into v' moves past any power
  -- of v the same way …
  lemma-Induction : ∀ {w v v'} → w • v ≈ v' • w → ∀ k → w • v ^ k ≈ v' ^ k • w
  lemma-Induction eq 0 = trans right-unit (sym left-unit)
  lemma-Induction eq 1 = eq
  lemma-Induction {w} {v} {v'} eq k@(₂₊ k') = begin
    w • v ^ k                 ≈⟨ sym assoc ⟩
    (w • v) • v ^ (₁₊ k')     ≈⟨ cleft eq ⟩
    (v' • w) • v ^ (₁₊ k')    ≈⟨ assoc ⟩
    v' • w • v ^ (₁₊ k')      ≈⟨ cright lemma-Induction eq (₁₊ k') ⟩
    v' • v' ^ (₁₊ k') • w     ≈⟨ sym assoc ⟩
    v' ^ k • w ∎

  -- … and the mirror image, a power of w moving past v.
  lemma-Inductionˡ : ∀ {w w' v} → w • v ≈ v • w' → ∀ k → w ^ k • v ≈ v • w' ^ k
  lemma-Inductionˡ eq 0 = trans left-unit (sym right-unit)
  lemma-Inductionˡ eq 1 = eq
  lemma-Inductionˡ {w} {w'} {v} eq k@(₁₊ k'@(₁₊ k'')) = begin
    w ^ k • v                 ≈⟨ assoc ⟩
    w • w ^ k' • v            ≈⟨ cright lemma-Inductionˡ eq k' ⟩
    w • v • w' ^ k'           ≈⟨ sym assoc ⟩
    (w • v) • w' ^ k'         ≈⟨ cleft eq ⟩
    (v • w') • w' ^ k'        ≈⟨ assoc ⟩
    v • w' ^ k ∎

------------------------------------------------------------------------
-- The one-wire rules, as a record
--
-- Every module of the calculus takes its rules bundled in a record rather
-- than as separate module parameters.  Agda abstracts each definition in
-- a module over the module's whole telescope, and a dozen rule
-- parameters made the two- and three-wire layers cost twice what they
-- cost over a fixed relation; with one record parameter the telescope
-- stays short.
--
-- The multiplier by -1, M₋₁, is a parameter of the record rather than
-- part of a field's type: Agda normalises the field types of a record it
-- is declaring (its forcing analysis does), and M₋₁ is a closed word
-- over the Bézout inverse of -1, whose normal form exhausts the heap.
-- One-Wire-Rules fixes the parameter at M₋₁, so clients never see it.

record One-Wire-Rules-At {n : ℕ} (Γ : WRel (Gen (₁₊ n)))
                         (m₋₁ : Word (Gen (₁₊ n))) : Set where
  field
    order-S     : let open PB Γ in S ^ p ≈ ε
    order-H     : let open PB Γ in H ^ 2 ≈ m₋₁
    M-power     : let open PB Γ in ∀ k → XMg^ k ≈ XM (g^ k)
    comm-HHSHHS : let open PB Γ in
                  H • H • S • H • H • S ≈ S • H • H • S • H • H

One-Wire-Rules : ∀ {n} → WRel (Gen (₁₊ n)) → Set
One-Wire-Rules Γ = One-Wire-Rules-At Γ M₋₁

------------------------------------------------------------------------
-- Multiplier arithmetic on one wire
--
-- Paper-V0 and Simplified-V1 have the SAME six one-wire axioms —
-- order-S, order-H, M-power, semi-MR, order-SH, comm-HHSHHS — so every
-- one-wire lemma of Simplified-V1.Lemmas.Lemmas1 holds here by the same
-- proof, and the ones below were ported from there.  They are stated
-- over any relation Γ with four of those rules (One-Wire-Rules); none
-- uses semi-MR or order-SH.
--
-- lemma-M-mul is what the three-wire derivations need: M ½ • M 2 is
-- M 1 is ε, and inserting that resolution of the identity is the step
-- that lets R¹⁴/R¹⁵ rescale a CZ exponent.

module One-Wire (n : ℕ) (Γ : WRel (Gen (₁₊ n))) (rules : One-Wire-Rules Γ) where

  open One-Wire-Rules-At rules

  open PB Γ hiding (_===_)
  open PP Γ

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
    XMg ^ toℕ k    ≈⟨ M-power k ⟩
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

  -- The rule under a lemma's name, so that callers one wire up can feed
  -- it to lemma-cong↑ as One-Wire.lemma-order-S n.
  lemma-order-S : S ^ p ≈ ε
  lemma-order-S = order-S

  lemma-order-H : H ^ 4 ≈ ε
  lemma-order-H = begin
    H ^ 4 ≈⟨ sym assoc ⟩
    HH ^ 2 ≈⟨ cong (order-H) (order-H) ⟩
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
  -- multiplier, and lifted through lemma-cong↑ for the wire-1 one.

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
  lemma-comm-SHHS^kHH k@1 = sym (by-assoc-and (comm-HHSHHS) auto auto)
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
      ≈⟨ cleft sym (comm-HHSHHS) ⟩
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
      ≈⟨ cright cright cong (order-S)
                            (cright cright lemma-order-w^k S p p-1 (order-S)) ⟩
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
      ≈⟨ cright cong (order-S)
                     (cright cright cleft lemma-order-w^k S p p-1 (order-S)) ⟩
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
      ≈⟨ cleft comm-HHSHHS ⟩
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
        ≈⟨ cong (order-H) (cright cleft order-H) ⟩
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
      ≈⟨ cright order-S ⟩
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
      ≈⟨ sym (order-H) ⟩
    H ^ 2 ∎
    where open SR word-setoid
------------------------------------------------------------------------
-- semi-MR, in the Mg spelling
--
-- The one-wire calculus never uses semi-MR; Paper-V0.Iso does, through
-- this one lemma, to prove Simplified-V1's form of the rule.  So it is
-- kept apart, and only this module takes the rule.

module One-Wire-MR
  (n : ℕ)
  (Γ : WRel (Gen (₁₊ n)))
  (rules   : One-Wire-Rules Γ)
  (semi-MR : let open PB Γ in XMg • R^ (g * g) ≈ R • XMg)
  where

  open PB Γ hiding (_===_)
  open PP Γ
  open One-Wire n Γ rules using (lemma-Mg-XMg ; lemma-XMg-Mg)

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
      ≈⟨ cright cleft sym (semi-MR) ⟩
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
-- Group-likeness
--
-- Every generator has a left inverse, from the three order axioms.  The
-- same construction as Simplified-V1.Lemmas.Clifford-GroupLike, and for
-- the same reason: the axioms it uses are shared.  Iso.agda gets its
-- witness by transporting V1's along g-well-defined, which is fine there
-- but unusable here — the chains below need right-cancellation, and
-- deriving it from the transported witness would be circular.
--
-- Unlike the one-wire modules this one needs the whole family of
-- relations, one per width: a shifted generator takes its inverse from
-- the width below, and the shift has to carry the equation up.  So it
-- takes the family Γ, the one-wire rules at every width, order-CZ, and
-- congruence under the shift, which a Circuit.Base.Lift-Relation
-- provides as lemma-cong↑.

module Paper-GroupLike
  (Γ : (n : ℕ) → WRel (Gen n))
  (one-wire    : ∀ {n} → One-Wire-Rules (Γ (₁₊ n)))
  (order-CZ    : ∀ {n} → let open PB (Γ (₂₊ n)) in CZ ^ p ≈ ε)
  (lemma-cong↑ : ∀ {n} (w v : Word (Gen n)) →
                 PB._≈_ (Γ n) w v → PB._≈_ (Γ (₁₊ n)) (w ↑) (v ↑))
  where

  grouplike : ∀ {n} → Grouplike (Γ n)
  grouplike {₁₊ n} H-gen = H ^ 3 , claim
    where
    open PB (Γ (₁₊ n))
    open PP (Γ (₁₊ n))
    open SR word-setoid
    claim : H ^ 3 • H ≈ ε
    claim = begin
      H ^ 3 • H ≈⟨ by-assoc auto ⟩
      H ^ 4     ≈⟨ One-Wire.lemma-order-H n (Γ (₁₊ n)) one-wire ⟩
      ε ∎
  grouplike {₁₊ n} S-gen = S ^ p-1 , claim
    where
    open PB (Γ (₁₊ n))
    open PP (Γ (₁₊ n))
    open SR word-setoid
    claim : S ^ p-1 • S ≈ ε
    claim = begin
      S ^ p-1 • S       ≈⟨ sym (^-+ S p-1 1) ⟩
      S ^ (p-1 Nat.+ 1) ≡⟨ Eq.cong (S ^_) (NP.+-comm p-1 1) ⟩
      S ^ p             ≈⟨ One-Wire-Rules-At.order-S one-wire ⟩
      ε ∎
  grouplike {₂₊ n} CZ-gen = CZ ^ p-1 , claim
    where
    open PB (Γ (₂₊ n))
    open PP (Γ (₂₊ n))
    open SR word-setoid
    claim : CZ ^ p-1 • CZ ≈ ε
    claim = begin
      CZ ^ p-1 • CZ       ≈⟨ sym (^-+ CZ p-1 1) ⟩
      CZ ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (CZ ^_) (NP.+-comm p-1 1) ⟩
      CZ ^ p              ≈⟨ order-CZ ⟩
      ε ∎
  -- Width ₁₊ n rather than ₂₊ n: gate₀ makes Gen 0 inhabited, so a shift
  -- can appear on one wire too.  The witness is width-generic.
  grouplike {₁₊ n} (g ↥) with grouplike g
  ... | ig , prf = (ig ↑) , lemma-cong↑ (ig • [ g ]ʷ) ε prf

------------------------------------------------------------------------
-- Pauli conjugation by H ^ 2, and the second direction of conj-H
--
-- These need right cancellation and the basis-change tactic, so they
-- cannot live in One-Wire, which Paper-GroupLike itself uses.  Ported
-- from Simplified-V1.LemmasXZ, on the same grounds as the One-Wire ports.
--
-- conj-H-Z is the direction conj-H-X does not give.  Together they say
-- how a Pauli crosses either H in XC = H ↑ ^ 3 • CZ • H ↑, which with
-- lemma-CZ-X↑ᵏ for the middle CZ is the whole Pauli-vs-XC rule.
--
-- It takes the group-likeness witness as a parameter, as Paper-V1's
-- XZ.One-Wire-Group does: Paper-GroupLike builds it from the family.

module One-Wire-Group
  (n : ℕ)
  (Γ : WRel (Gen (₁₊ n)))
  (rules : One-Wire-Rules Γ)
  (gl    : Grouplike Γ)
  where

  open PB Γ hiding (_===_)
  open PP Γ
  open SR word-setoid
  open Pattern-Assoc
  open One-Wire-Rules-At rules
  open One-Wire n Γ rules
  open Group-Lemmas Γ gl
    using (•-cancelʳ ; •-cancelˡ)
  open Basis-Change _ Γ gl

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
      (S ^ p) ^ p-1      ≈⟨ ^-cong (S ^ p) ε p-1 (order-S) ⟩
      ε ^ p-1            ≈⟨ ε^k=ε (₁₊ p-2) ⟩
      ε                  ≈⟨ sym (order-S) ⟩
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

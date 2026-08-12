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
  using (lemma-↑^ ; lemma-↓^ ; lemma-Induction
        ; lemma-comm-S-w↑ ; lemma-comm-H-w↑ ; lemma-comm-Z-w↑)

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
-- Ex is its own inverse

module Ex-Conjugation (n : ℕ) where

  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid

  open Group-Lemmas ((₂₊ n) QRel,_===_) (Paper-GroupLike.grouplike {₂₊ n})
    using (•-cancelʳ)

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

------------------------------------------------------------------------
-- The shift down is the identity on the one-wire words
--
-- _↓ maps every gate to itself, so it is definitionally the identity on
-- a word built from gate letters — but it is stuck on a power with a
-- symbolic exponent, which is what these propositional equations step
-- over.  They are needed because Simplified-V1 states semi-M↓CZ over
-- Mg ↓ rather than Mg.

module Down-Identity where

  lemma-S⁻¹↓ : (S⁻¹ {n}) ↓ ≡ S⁻¹
  lemma-S⁻¹↓ = lemma-↓^ p-1 S

  lemma-Z↓ : (Z {n}) ↓ ≡ Z
  lemma-Z↓ = Eq.cong (λ w → H • H • S • H • H • w) lemma-S⁻¹↓

  lemma-Z^↓ : ∀ k → (Z^ k {n}) ↓ ≡ Z^ k
  lemma-Z^↓ k =
    Eq.trans (lemma-↓^ (toℕ k) Z) (Eq.cong (_^ toℕ k) lemma-Z↓)

  lemma-R↓ : (R {n}) ↓ ≡ R
  lemma-R↓ = Eq.cong (S •_) (lemma-Z^↓ 1/2)

  lemma-R^↓ : ∀ k → (R^ {n} k) ↓ ≡ R^ k
  lemma-R^↓ k =
    Eq.trans (lemma-↓^ (toℕ k) R) (Eq.cong (_^ toℕ k) lemma-R↓)

  lemma-M↓ : ∀ (x' : ℤ* ₚ) → (M {n} x') ↓ ≡ M x'
  lemma-M↓ x' = Eq.cong₂ (λ a b → a • H • b • H • a • H)
                         (lemma-R^↓ x) (lemma-R^↓ x⁻¹)
    where
    x   = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁)

  lemma-Mg↓ : (Mg {n}) ↓ ≡ Mg
  lemma-Mg↓ = lemma-M↓ g′

------------------------------------------------------------------------
-- The two Simplified-V1 axioms that Paper-V0 lacked
--
-- Both are now consequences of comm-Ex-CZ: the ↑-rule conjugated by the
-- swap, with the ↓ on the outside stepped over by Down-Identity.

module Down-Rules (n : ℕ) where

  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
  open Ex-Conjugation n
  open Down-Identity

  lemma-comm-CZ-S↓ : CZ • S ↓ ≈ S ↓ • CZ
  lemma-comm-CZ-S↓ = lemma-comm-CZ-S

  lemma-semi-M↓CZ : Mg ↓ • CZ ≈ CZ^ g • Mg ↓
  lemma-semi-M↓CZ = begin
    Mg ↓ • CZ     ≈⟨ refl' (Eq.cong (_• CZ) lemma-Mg↓) ⟩
    Mg • CZ       ≈⟨ lemma-semi-Mg-CZ ⟩
    CZ^ g • Mg    ≈⟨ refl' (Eq.cong (CZ^ g •_) (Eq.sym lemma-Mg↓)) ⟩
    CZ^ g • Mg ↓ ∎

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

  lemma-C18ᵏ : ∀ k → CX ↑ • CZ ^ k ≈ (CZ • CZ02) ^ k • CX ↑
  lemma-C18ᵏ ₀ = trans right-unit (sym left-unit)
  lemma-C18ᵏ ₁ = trans (axiom semi-CX↑-CZ↓) (sym assoc)
  lemma-C18ᵏ (₂₊ k) = begin
    CX ↑ • (CZ • CZ ^ ₁₊ k)
      ≈⟨ sym assoc ⟩
    (CX ↑ • CZ) • CZ ^ ₁₊ k
      ≈⟨ cleft axiom semi-CX↑-CZ↓ ⟩
    (CZ • (CZ02 • CX ↑)) • CZ ^ ₁₊ k
      ≈⟨ assoc ⟩
    CZ • ((CZ02 • CX ↑) • CZ ^ ₁₊ k)
      ≈⟨ cright assoc ⟩
    CZ • (CZ02 • (CX ↑ • CZ ^ ₁₊ k))
      ≈⟨ cright cright lemma-C18ᵏ (₁₊ k) ⟩
    CZ • (CZ02 • ((CZ • CZ02) ^ ₁₊ k • CX ↑))
      ≈⟨ cright sym assoc ⟩
    CZ • ((CZ02 • (CZ • CZ02) ^ ₁₊ k) • CX ↑)
      ≈⟨ sym assoc ⟩
    (CZ • (CZ02 • (CZ • CZ02) ^ ₁₊ k)) • CX ↑
      ≈⟨ cleft sym assoc ⟩
    ((CZ • CZ02) • (CZ • CZ02) ^ ₁₊ k) • CX ↑ ∎

  ------------------------------------------------------------------------
  -- The alternating product has order p as well
  --
  -- CX ↑ • CZ ^ p is CX ↑ on the nose, so lemma-C18ᵏ at p says
  -- (CZ • CZ02) ^ p • CX ↑ is too, and CX ↑ cancels on the right.

  lemma-order-CZ·CZ02 : (CZ • CZ02) ^ p ≈ ε
  lemma-order-CZ·CZ02 = •-cancelʳ {h = CX ↑} (begin
    (CZ • CZ02) ^ p • CX ↑  ≈⟨ sym (lemma-C18ᵏ p) ⟩
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

  -- (A): C18 with every CZ exponent rescaled by g ^′ j.
  lemma-A : ∀ j → let e = toℕ (g ^′ j) in
            CX ↑ • CZ ^ e ≈ (CZ ^ e • CZ02 ^ e) • CX ↑
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
      ≈⟨ cright axiom semi-CX↑-CZ↓ ⟩
    Mg ^ j • (CZ • (CZ02 • CX ↑))
      ≈⟨ sym assoc ⟩
    (Mg ^ j • CZ) • (CZ02 • CX ↑)
      ≈⟨ cleft (lemma-Mgᵏ-CZ j) ⟩
    (CZ ^ e • Mg ^ j) • (CZ02 • CX ↑)
      ≈⟨ assoc ⟩
    CZ ^ e • (Mg ^ j • (CZ02 • CX ↑))
      ≈⟨ cright sym assoc ⟩
    CZ ^ e • ((Mg ^ j • CZ02) • CX ↑)
      ≈⟨ cright cleft (lemma-Mgᵏ-CZ02 j) ⟩
    CZ ^ e • ((CZ02 ^ e • Mg ^ j) • CX ↑)
      ≈⟨ cright assoc ⟩
    CZ ^ e • (CZ02 ^ e • (Mg ^ j • CX ↑))
      ≈⟨ cright cright (lemma-Mgᵏ-CX↑ j) ⟩
    CZ ^ e • (CZ02 ^ e • (CX ↑ • Mg ^ j))
      ≈⟨ cright sym assoc ⟩
    CZ ^ e • ((CZ02 ^ e • CX ↑) • Mg ^ j)
      ≈⟨ sym assoc ⟩
    (CZ ^ e • (CZ02 ^ e • CX ↑)) • Mg ^ j
      ≈⟨ cleft sym assoc ⟩
    ((CZ ^ e • CZ02 ^ e) • CX ↑) • Mg ^ j ∎)
    where e = toℕ (g ^′ j)

  -- (C): the two CZs distribute over the rescaled power.
  lemma-C : ∀ j → let e = toℕ (g ^′ j) in
            (CZ • CZ02) ^ e ≈ CZ ^ e • CZ02 ^ e
  lemma-C j = •-cancelʳ {h = CX ↑} (begin
    (CZ • CZ02) ^ e • CX ↑     ≈⟨ sym (lemma-C18ᵏ e) ⟩
    CX ↑ • CZ ^ e              ≈⟨ lemma-A j ⟩
    (CZ ^ e • CZ02 ^ e) • CX ↑ ∎)
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
    lemma-C₂ : (CZ • CZ02) • (CZ • CZ02) ≈ (CZ • CZ) • (CZ02 • CZ02)
    lemma-C₂ = begin
      (CZ • CZ02) • (CZ • CZ02)
        ≡⟨ Eq.cong ((CZ • CZ02) ^_) (Eq.sym e₂) ⟩
      (CZ • CZ02) ^ toℕ (g ^′ j₂)
        ≈⟨ lemma-C j₂ ⟩
      CZ ^ toℕ (g ^′ j₂) • CZ02 ^ toℕ (g ^′ j₂)
        ≡⟨ Eq.cong₂ (λ a b → CZ ^ a • CZ02 ^ b) e₂ e₂ ⟩
      (CZ • CZ) • (CZ02 • CZ02) ∎

  lemma-comm-CZ-CZ02 : CZ • CZ02 ≈ CZ02 • CZ
  lemma-comm-CZ-CZ02 =
    sym (•-cancelʳ {h = CZ02} (•-cancelˡ {g = CZ} (begin
      CZ • ((CZ02 • CZ) • CZ02)  ≈⟨ by-assoc auto ⟩
      (CZ • CZ02) • (CZ • CZ02)  ≈⟨ lemma-C₂ ⟩
      (CZ • CZ) • (CZ02 • CZ02)  ≈⟨ by-assoc auto ⟩
      CZ • ((CZ • CZ02) • CZ02) ∎)))

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

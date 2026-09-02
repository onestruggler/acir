{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- Pauli conjugation past H and past S: the calculus that moves an X or a
-- Z through a Clifford generator, and the ℤₚ half-exponent arithmetic it
-- needs.  This is where X • Z ≈ Z • X is established.
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


module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.XZ
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen
open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime using (toℕ-+)

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

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.OneWire p-3 p-prime g* g-gen
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.GroupLike p-3 p-prime g* g-gen

import Examples.Groups.ProjectiveClifford.Qupit.Shared.PauliBase
  p-3 p-prime g* g-gen as Shared

------------------------------------------------------------------------
-- Pauli conjugation by H ^ 2, and the second direction of conj-H
--
-- These need right cancellation and the basis-change tactic, so they
-- cannot live in One-Wire: Paper-GroupLike is declared after it, so no
-- Group-Lemmas instance is in scope there.  Ported verbatim from
-- Simplified-V1.LemmasXZ, on the same grounds as the One-Wire ports —
-- the one-wire axioms are shared, so the proof terms transfer unchanged.
--
-- conj-H-Z is the direction conj-H-X does not give.  Both are needed to
-- carry a Pauli through the H's the bridge's blocks are built from.

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


  ------------------------------------------------------------------------
  -- Moving a Pauli past S
  --
  -- Ported from Simplified-V1.LemmasXZ.  Those proof terms are tied to
  -- that relation and cannot be reused across the two, but Paper-V1 has
  -- every fact they rest on — order-S, order-H, comm-HHSHHS, and
  -- (S • H) ^ 3 ≈ ε, an axiom there but a theorem here — so the
  -- arguments go through unchanged.  The one step
  -- Simplified-V1 discharges with its Sim-Rewriting tactic (rewriting a
  -- lone H into H ^ 5) is done by hand below, since Paper-V1 has no
  -- rewriting layer.
  --
  -- conj-H-X and conj-H-Z already move a Pauli past H; these are the
  -- missing halves, moving one past S.  Together they are what turns the
  -- R-spelling of a multiplier into the S-spelling with the Paulis
  -- collected in front — see lemma-M₋₁-R.

  -- The shared calculus, at this relation.  order-H enters only as
  -- H ^ 4 ≈ ε, which is the point past which Paper-V0's and Paper-V1's
  -- spellings of the multiplier stop mattering.
  -- order-SH' is NOT an axiom here: it is One-Wire's lemma-order-SH,
  -- derived from M-power at k = 0.  This is the only place in the
  -- development that needs (S • H) ^ 3 ≈ ε at all.
  module SC = Shared.Calculus n ((₁₊ n) QRel,_===_)
                (Paper-GroupLike.grouplike {₁₊ n})
                (axiom order-S) lemma-order-H lemma-order-SH

  S⁻¹S : S⁻¹ • S ≈ ε
  S⁻¹S = SC.S⁻¹S

  H≈H⁵ : H ≈ H ^ 5
  H≈H⁵ = SC.H≈H⁵

  lemma-SHSH : S • H • S • H ≈ H ^ 3 • S⁻¹
  lemma-SHSH = SC.lemma-SHSH

  lemma-HSH : H • S • H ≈ S⁻¹ • H ^ 3 • S⁻¹
  lemma-HSH = SC.lemma-HSH

  -- Moving a single X rightward past S costs a Z.  The one step
  -- Simplified-V1 does with `rewrite-sim 100 auto` is the H≈H⁵ below.
  lemma-SX : S • X ≈ X • Z • S
  lemma-SX = begin
    S • H • S • H • H • S⁻¹ • H
      ≈⟨ by-passoc (□ ^ 7) (□ ^ 4 • □ ^ 3) auto ⟩
    (S • H • S • H) • H • S⁻¹ • H
      ≈⟨ cleft lemma-SHSH ⟩
    (H ^ 3 • S⁻¹) • H • S⁻¹ • H
      ≈⟨ cright cleft H≈H⁵ ⟩
    (H ^ 3 • S⁻¹) • H ^ 5 • S⁻¹ • H
      ≈⟨ sym (by-passoc (□ ^ 5 • □ • □ ^ 3 • □ ^ 2) ((□ ^ 3 • □) • □ ^ 5 • □ ^ 2) auto) ⟩
    (H • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H)
      ≈⟨ cleft (cright sym left-unit) ⟩
    (H • ε • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H)
      ≈⟨ cleft cright cleft sym (axiom order-S) ⟩
    (H • (S • S⁻¹) • H • H • S⁻¹ • H) • (H • H ^ 3 • S⁻¹ • H)
      ≈⟨ by-passoc ((□ • □ ^ 2 • □ ^ 4) • □ ^ 4) (□ ^ 2 • □ ^ 6 • □ ^ 3) auto ⟩
    (H • S) • (S⁻¹ • H • H • S⁻¹ • H • H) • H ^ 3 • S⁻¹ • H
      ≈⟨ cright cleft comm⇒pow-comm p-1 1 (lemma-comm-SHHS^kHH p-1) ⟩
    (H • S) • ((H • H • S⁻¹ • H • H) • S⁻¹) • H ^ 3 • S⁻¹ • H
      ≈⟨ by-passoc (□ ^ 2 • (□ ^ 5 • □) • □ ^ 3) (□ ^ 6 • □ • □ ^ 3 • □) auto ⟩
    (H • S • H • H • S⁻¹ • H) • H • (S⁻¹ • H ^ 3 • S⁻¹) • H
      ≈⟨ cright cright cleft sym lemma-HSH ⟩
    (H • S • H • H • S⁻¹ • H) • H • (H • S • H) • H
      ≈⟨ by-passoc (□ ^ 6 • □ • □ ^ 3 • □) (□ ^ 6 • □ ^ 5) auto ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H)
      ≈⟨ cright sym right-unit ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) • ε
      ≈⟨ cright cright sym (axiom order-S) ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) • S • S⁻¹
      ≈⟨ cright cright comm⇒pow-comm 1 p-1 refl ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H) • S⁻¹ • S
      ≈⟨ cright by-passoc (□ ^ 5 • □ ^ 2) (□ ^ 6 • □) auto ⟩
    (H • S • H • H • S⁻¹ • H) • (H • H • S • H • H • S⁻¹) • S ∎

  conj-S-X : S • X ≈ (X • Z) • S
  conj-S-X = trans lemma-SX (sym assoc)


  comm-Z^k-S : ∀ k -> Z ^ k • S ≈ S • Z ^ k
  comm-Z^k-S k = lemma-Inductionˡ lemma-comm-Z-S k

  -- …and the mirror: moving a single X rightward past S costs a Z⁻¹.
  lemma-XS : X • S ≈ S • X • Z⁻¹
  lemma-XS = sym (begin
    S • X • Z⁻¹          ≈⟨ sym assoc ⟩
    (S • X) • Z⁻¹        ≈⟨ cleft conj-S-X ⟩
    ((X • Z) • S) • Z⁻¹  ≈⟨ assoc ⟩
    (X • Z) • S • Z⁻¹    ≈⟨ cright sym (comm-Z^k-S p-1) ⟩
    (X • Z) • Z⁻¹ • S    ≈⟨ by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
    X • (Z • Z⁻¹) • S    ≈⟨ cright cleft lemma-order-Z ⟩
    X • ε • S            ≈⟨ cright left-unit ⟩
    X • S ∎)

  aux-X^-₁ : X^ (- ₁) ≈ X⁻¹
  aux-X^-₁ = refl' (Eq.cong (X ^_)
               (Eq.trans (Eq.cong toℕ (Eq.sym p-1=-1ₚ)) lemma-toℕ-ₚ₋₁))

  aux-X-X⁻¹ : X • X⁻¹ ≈ ε
  aux-X-X⁻¹ = lemma-order-X

  aux-Z⁻¹-Z : Z⁻¹ • Z ≈ ε
  aux-Z⁻¹-Z = begin
    Z⁻¹ • Z  ≈⟨ comm⇒pow-comm p-1 1 refl ⟩
    Z • Z⁻¹  ≈⟨ lemma-order-Z ⟩
    ε ∎

  -- Conjugation by H sends X to Z and Z to X⁻¹, so it sends X to Z⁻¹ the
  -- other way round: the companion of conj-H-X / conj-H-Z that moves a
  -- Pauli rightward through H.
  lemma-XH : X • H ≈ H • Z⁻¹
  lemma-XH = bbc ε Z claim
    where
    claim : ε • (X • H) • Z ≈ ε • (H • Z⁻¹) • Z
    claim = begin
      ε • (X • H) • Z     ≈⟨ left-unit ⟩
      (X • H) • Z         ≈⟨ assoc ⟩
      X • (H • Z)         ≈⟨ cright conj-H-Z ⟩
      X • (X^ (- ₁) • H)  ≈⟨ cright cleft aux-X^-₁ ⟩
      X • (X⁻¹ • H)       ≈⟨ sym assoc ⟩
      (X • X⁻¹) • H       ≈⟨ cleft aux-X-X⁻¹ ⟩
      ε • H               ≈⟨ left-unit ⟩
      H                   ≈⟨ sym right-unit ⟩
      H • ε               ≈⟨ cright sym aux-Z⁻¹-Z ⟩
      H • Z⁻¹ • Z         ≈⟨ sym assoc ⟩
      (H • Z⁻¹) • Z       ≈⟨ sym left-unit ⟩
      ε • (H • Z⁻¹) • Z ∎

  conj-X^k-H : ∀ k -> X ^ k • H ≈ H • Z⁻¹ ^ k
  conj-X^k-H k = lemma-Inductionˡ lemma-XH k

  ------------------------------------------------------------------------
  -- X and Z commute
  --
  -- The mod-scalar version of the argument on p.9 of supplement-July29,
  -- which proves Z X Z⁻¹ X⁻¹ = ω⁻¹.  Projectively ω⁻¹ is the identity,
  -- and both ingredients survive:
  --
  --   * order-H read as an equation for a Pauli.  Paper-V1's M₋₁ is
  --     Z⁻¹ • X • (S⁻¹ • H) ^ 3, so H ^ 2 ≈ M₋₁ solves for Z⁻¹ • X —
  --     the paper's step "X Z⁻¹ = S H⁻¹ S H⁻¹ S H · scalars".
  --   * (S • H) ^ 3 ≈ ε, which is where the paper's (H S) ^ 3 = scalar
  --     becomes an equation outright, killing the residue.  Paper-V0
  --     takes that as an axiom; here it is One-Wire's lemma-order-SH.
  --
  -- Simplified-V1.LemmasXZ derives this instead by comparing (S • H) ^ 3
  -- with (R • H) ^ 3.  That route is not available here: it needs
  -- (R • H) ^ 3 ≈ ε, which came from M ₁ being the R-spelling, and the
  -- SHS' spelling makes M ₁ the S-spelling instead.  So this replaces
  -- that derivation rather than porting it.

  -- The half-exponent arithmetic this needs — ½ + ½ ≡ ₁, two halves of x
  -- make x, and negation is involutive — mentions no relation at all, so
  -- it is Shared.PauliBase's, at that file's top level.  The two facts
  -- below are the only ones specific to the exponents M₋₁ produces.
  open Shared using (aux-half-half ; neg-involutive ; neg-* ; neg0)

  -- The two exponents M₋₁'s Pauli prefix collapses to: at x = -1 the
  -- shape's Z-exponent is (-1-1)·½ = -1 and its X-exponent is
  -- (1-(-1))·½ = 1.  Both are ℤₚ ring facts on top of aux-half-half; not
  -- refl, since 1/2 is a Bézout witness and does not reduce.  These are
  -- ≡-chains, but `begin` here would clash with the setoid reasoning this
  -- module already has open, so they are spelled with Eq.trans.

  -- (-₁ + -₁)·½ ≡ ½·(-₁ + -₁) ≡ ½·(-₁) + ½·(-₁) ≡ -₁
  aux-e₁ : (- ₁ + - ₁) * 1/2 ≡ - ₁
  aux-e₁ =
    Eq.trans (*-comm (- ₁ + - ₁) 1/2)
      (Eq.trans (*-distribˡ-+ 1/2 (- ₁) (- ₁)) (aux-half-half (- ₁)))

  -- (₁ + -(-₁))·½ ≡ (₁+₁)·½ ≡ ½·(₁+₁) ≡ ½·₁ + ½·₁ ≡ ₁
  aux-e₂ : (₁ + - (- ₁)) * 1/2 ≡ ₁
  aux-e₂ =
    Eq.trans (Eq.cong (λ z → (₁ + z) * 1/2) (neg-involutive ₁))
      (Eq.trans (*-comm (₁ + ₁) 1/2)
        (Eq.trans (*-distribˡ-+ 1/2 ₁ ₁) (aux-half-half ₁)))

  -- M₋₁ unfolded — the paper's (T1) reading of it.  At x = -1 both of
  -- the shape's exponents are -1, so aux-e₁/aux-e₂ collapse the Pauli
  -- prefix to Z⁻¹ • X and what is left is (S⁻¹ • H) three times over.
  lemma-M₋₁-unfold : M₋₁ ≈ Z⁻¹ • X • S⁻¹ • H • S⁻¹ • H • S⁻¹ • H
  lemma-M₋₁-unfold = begin
    M₋₁
      ≡⟨ Eq.cong (λ a → SHS' a (- ₁)) aux-₁⁻¹ ⟩
    SHS' (- ₁) (- ₁)
      ≡⟨ Eq.cong₂ (λ e₁ e₂ → Z^ e₁ • X^ e₂
                             • S^ (- ₁) • H • S^ (- ₁) • H • S^ (- ₁) • H)
                  aux-e₁ aux-e₂ ⟩
    Z^ (- ₁) • X^ ₁ • S^ (- ₁) • H • S^ (- ₁) • H • S^ (- ₁) • H
      ≡⟨ Eq.cong (λ m → Z ^ m • X^ ₁ • S ^ m • H • S ^ m • H • S ^ m • H)
                 lemma-toℕ-1ₚ ⟩
    Z⁻¹ • X • S⁻¹ • H • S⁻¹ • H • S⁻¹ • H ∎

  private
    H³H : H ^ 3 • H ≈ ε
    H³H = trans (sym (^-+ H 3 1)) lemma-order-H

  -- The paper's "X Z⁻¹ = S H⁻¹ S H⁻¹ S H · scalars", in the form order-H
  -- gives it here: cancel the body of M₋₁ off the right of H ^ 2 and the
  -- Pauli prefix is what is left.  The right-hand side is H⁵ S H³ S H³ S
  -- with H⁵ already reduced to H.
  lemma-Z⁻¹X : Z⁻¹ • X ≈ H • S • H ^ 3 • S • H ^ 3 • S
  lemma-Z⁻¹X = •-cancelʳ {h = S⁻¹ • H • S⁻¹ • H • S⁻¹ • H} (begin
    (Z⁻¹ • X) • (S⁻¹ • H • S⁻¹ • H • S⁻¹ • H)
      ≈⟨ by-passoc (□ ^ 2 • □ ^ 6) (□ ^ 8) auto ⟩
    Z⁻¹ • X • S⁻¹ • H • S⁻¹ • H • S⁻¹ • H
      ≈⟨ sym lemma-M₋₁-unfold ⟩
    M₋₁
      ≈⟨ sym order-H' ⟩
    H ^ 2
      ≈⟨ sym rhs ⟩
    (H • S • H ^ 3 • S • H ^ 3 • S) • (S⁻¹ • H • S⁻¹ • H • S⁻¹ • H) ∎)
    where
    rhs : (H • S • H ^ 3 • S • H ^ 3 • S) • (S⁻¹ • H • S⁻¹ • H • S⁻¹ • H)
          ≈ H ^ 2
    rhs = begin
      (H • S • H ^ 3 • S • H ^ 3 • S) • (S⁻¹ • H • S⁻¹ • H • S⁻¹ • H)
        ≈⟨ by-passoc (□ ^ 6 • □ ^ 6) (□ ^ 5 • □ ^ 2 • □ ^ 5) auto ⟩
      (H • S • H ^ 3 • S • H ^ 3) • (S • S⁻¹) • (H • S⁻¹ • H • S⁻¹ • H)
        ≈⟨ cright cleft axiom order-S ⟩
      (H • S • H ^ 3 • S • H ^ 3) • ε • (H • S⁻¹ • H • S⁻¹ • H)
        ≈⟨ cright left-unit ⟩
      (H • S • H ^ 3 • S • H ^ 3) • (H • S⁻¹ • H • S⁻¹ • H)
        ≈⟨ by-passoc (□ ^ 5 • □ ^ 5) (□ ^ 4 • □ ^ 2 • □ ^ 4) auto ⟩
      (H • S • H ^ 3 • S) • (H ^ 3 • H) • (S⁻¹ • H • S⁻¹ • H)
        ≈⟨ cright cleft H³H ⟩
      (H • S • H ^ 3 • S) • ε • (S⁻¹ • H • S⁻¹ • H)
        ≈⟨ cright left-unit ⟩
      (H • S • H ^ 3 • S) • (S⁻¹ • H • S⁻¹ • H)
        ≈⟨ by-passoc (□ ^ 4 • □ ^ 4) (□ ^ 3 • □ ^ 2 • □ ^ 3) auto ⟩
      (H • S • H ^ 3) • (S • S⁻¹) • (H • S⁻¹ • H)
        ≈⟨ cright cleft axiom order-S ⟩
      (H • S • H ^ 3) • ε • (H • S⁻¹ • H)
        ≈⟨ cright left-unit ⟩
      (H • S • H ^ 3) • (H • S⁻¹ • H)
        ≈⟨ by-passoc (□ ^ 3 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
      (H • S) • (H ^ 3 • H) • (S⁻¹ • H)
        ≈⟨ cright cleft H³H ⟩
      (H • S) • ε • (S⁻¹ • H)
        ≈⟨ cright left-unit ⟩
      (H • S) • (S⁻¹ • H)
        ≈⟨ by-passoc (□ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □) auto ⟩
      H • (S • S⁻¹) • H
        ≈⟨ cright cleft axiom order-S ⟩
      H • ε • H
        ≈⟨ cright left-unit ⟩
      H • H ∎

  ------------------------------------------------------------------------
  -- X and Z commute, continued: the collapse
  --
  -- W is the S,H word lemma-Z⁻¹X produces, and A is X⁻¹ written out as
  -- one — X is H • S • H² • S⁻¹ • H, so its inverse is H³ • S • H² •
  -- S⁻¹ • H³.  Spelling A out rather than using X ^ p-1 keeps every step
  -- below a finite word computation.
  --
  -- The paper collapses its commutator to H (HS)³ H⁻¹; here the same
  -- cancellations reduce A • (W • Z) to H⁴ S H⁴ S⁻¹, which is ε.  The
  -- two non-trivial rewrites are lemma-SHSH (for the S H S H that
  -- appears once H³ is split as H • H²) and comm-HHSHHS.

  -- Every word below is written as a flat chain of single generators.
  -- by-passoc's □ matches one factor of the •-tree, so H ^ 3 is □ ^ 3
  -- and sits as a *subtree*; keeping the chains flat is what lets the
  -- patterns stay plain □ ^ n.  (by-assoc is no use here: S⁻¹ is S ^ p-1
  -- with p symbolic, so its to-list is stuck, and comparing across a
  -- group boundary would need associativity of _++_ on a stuck list.)
  private
    W : Word (Gen (₁₊ n))
    W = H • S • H • H • H • S • H • H • H • S

    A : Word (Gen (₁₊ n))
    A = H • H • H • S • H • H • S⁻¹ • H • H • H

    H⁵≈H : H • H • H • H • H ≈ H
    H⁵≈H = sym H≈H⁵

    H⁶≈H² : H ^ 6 ≈ H ^ 2
    H⁶≈H² = begin
      H ^ 6          ≈⟨ ^-+ H 4 2 ⟩
      H ^ 4 • H ^ 2  ≈⟨ cleft lemma-order-H ⟩
      ε • H ^ 2      ≈⟨ left-unit ⟩
      H ^ 2 ∎

    -- lemma-SHSH with its right-hand side flattened.
    SHSH' : S • H • S • H ≈ H • H • H • S⁻¹
    SHSH' = trans lemma-SHSH (by-passoc (□ ^ 3 • □) (□ ^ 4) auto)

    -- lemma-Z⁻¹X with its right-hand side flattened.
    Z⁻¹X' : Z⁻¹ • X ≈ W
    Z⁻¹X' = trans lemma-Z⁻¹X
              (by-passoc (□ • □ • □ ^ 3 • □ • □ ^ 3 • □) (□ ^ 10) auto)

  -- A • X ≈ ε: A really is an inverse for X.
  private
    aux-AX : A • X ≈ ε
    aux-AX = begin
      A • X
        ≈⟨ by-passoc (□ ^ 10 • □ ^ 6) (□ ^ 7 • □ ^ 4 • □ ^ 5) auto ⟩
      (H • H • H • S • H • H • S⁻¹) • (H • H • H • H) • (S • H • H • S⁻¹ • H)
        ≈⟨ cright cleft lemma-order-H ⟩
      (H • H • H • S • H • H • S⁻¹) • ε • (S • H • H • S⁻¹ • H)
        ≈⟨ cright left-unit ⟩
      (H • H • H • S • H • H • S⁻¹) • (S • H • H • S⁻¹ • H)
        ≈⟨ by-passoc (□ ^ 7 • □ ^ 5) (□ ^ 6 • □ ^ 2 • □ ^ 4) auto ⟩
      (H • H • H • S • H • H) • (S⁻¹ • S) • (H • H • S⁻¹ • H)
        ≈⟨ cright cleft S⁻¹S ⟩
      (H • H • H • S • H • H) • ε • (H • H • S⁻¹ • H)
        ≈⟨ cright left-unit ⟩
      (H • H • H • S • H • H) • (H • H • S⁻¹ • H)
        ≈⟨ by-passoc (□ ^ 6 • □ ^ 4) (□ ^ 4 • □ ^ 4 • □ ^ 2) auto ⟩
      (H • H • H • S) • (H • H • H • H) • (S⁻¹ • H)
        ≈⟨ cright cleft lemma-order-H ⟩
      (H • H • H • S) • ε • (S⁻¹ • H)
        ≈⟨ cright left-unit ⟩
      (H • H • H • S) • (S⁻¹ • H)
        ≈⟨ by-passoc (□ ^ 4 • □ ^ 2) (□ ^ 3 • □ ^ 2 • □) auto ⟩
      (H • H • H) • (S • S⁻¹) • H
        ≈⟨ cright cleft axiom order-S ⟩
      (H • H • H) • ε • H
        ≈⟨ cright left-unit ⟩
      (H • H • H) • H
        ≈⟨ by-passoc (□ ^ 3 • □) (□ ^ 4) auto ⟩
      H • H • H • H
        ≈⟨ lemma-order-H ⟩
      ε ∎

    -- …and the same for W • Z, which is the whole content.
    aux-AWZ : A • (W • Z) ≈ ε
    aux-AWZ = begin
      A • (W • Z)
        ≈⟨ by-passoc (□ ^ 10 • □ ^ 10 • □ ^ 6) (□ ^ 7 • □ ^ 4 • □ ^ 15) auto ⟩
      (H • H • H • S • H • H • S⁻¹) • (H • H • H • H)
        • (S • H • H • H • S • H • H • H • S • H • H • S • H • H • S⁻¹)
        ≈⟨ cright cleft lemma-order-H ⟩
      (H • H • H • S • H • H • S⁻¹) • ε
        • (S • H • H • H • S • H • H • H • S • H • H • S • H • H • S⁻¹)
        ≈⟨ cright left-unit ⟩
      (H • H • H • S • H • H • S⁻¹)
        • (S • H • H • H • S • H • H • H • S • H • H • S • H • H • S⁻¹)
        ≈⟨ by-passoc (□ ^ 7 • □ ^ 15) (□ ^ 6 • □ ^ 2 • □ ^ 14) auto ⟩
      (H • H • H • S • H • H) • (S⁻¹ • S)
        • (H • H • H • S • H • H • H • S • H • H • S • H • H • S⁻¹)
        ≈⟨ cright cleft S⁻¹S ⟩
      (H • H • H • S • H • H) • ε
        • (H • H • H • S • H • H • H • S • H • H • S • H • H • S⁻¹)
        ≈⟨ cright left-unit ⟩
      (H • H • H • S • H • H)
        • (H • H • H • S • H • H • H • S • H • H • S • H • H • S⁻¹)
        ≈⟨ by-passoc (□ ^ 6 • □ ^ 14) (□ ^ 4 • □ ^ 5 • □ ^ 11) auto ⟩
      (H • H • H • S) • (H • H • H • H • H)
        • (S • H • H • H • S • H • H • S • H • H • S⁻¹)
        ≈⟨ cright cleft H⁵≈H ⟩
      (H • H • H • S) • H • (S • H • H • H • S • H • H • S • H • H • S⁻¹)
        ≈⟨ by-passoc (□ ^ 4 • □ • □ ^ 11) (□ ^ 3 • □ ^ 4 • □ ^ 9) auto ⟩
      (H • H • H) • (S • H • S • H) • (H • H • S • H • H • S • H • H • S⁻¹)
        ≈⟨ cright cleft SHSH' ⟩
      (H • H • H) • (H • H • H • S⁻¹) • (H • H • S • H • H • S • H • H • S⁻¹)
        ≈⟨ by-passoc (□ ^ 3 • □ ^ 4 • □ ^ 9) (□ ^ 6 • □ ^ 10) auto ⟩
      H ^ 6 • (S⁻¹ • H • H • S • H • H • S • H • H • S⁻¹)
        ≈⟨ cleft H⁶≈H² ⟩
      H ^ 2 • (S⁻¹ • H • H • S • H • H • S • H • H • S⁻¹)
        ≈⟨ by-passoc (□ ^ 2 • □ ^ 10) (□ ^ 3 • □ ^ 6 • □ ^ 3) auto ⟩
      (H • H • S⁻¹) • (H • H • S • H • H • S) • (H • H • S⁻¹)
        ≈⟨ cright cleft axiom comm-HHSHHS ⟩
      (H • H • S⁻¹) • (S • H • H • S • H • H) • (H • H • S⁻¹)
        ≈⟨ by-passoc (□ ^ 3 • □ ^ 6 • □ ^ 3) (□ ^ 2 • □ ^ 2 • □ ^ 8) auto ⟩
      (H • H) • (S⁻¹ • S) • (H • H • S • H • H • H • H • S⁻¹)
        ≈⟨ cright cleft S⁻¹S ⟩
      (H • H) • ε • (H • H • S • H • H • H • H • S⁻¹)
        ≈⟨ cright left-unit ⟩
      (H • H) • (H • H • S • H • H • H • H • S⁻¹)
        ≈⟨ by-passoc (□ ^ 2 • □ ^ 8) (□ ^ 4 • □ ^ 6) auto ⟩
      (H • H • H • H) • (S • H • H • H • H • S⁻¹)
        ≈⟨ cleft lemma-order-H ⟩
      ε • (S • H • H • H • H • S⁻¹)
        ≈⟨ left-unit ⟩
      S • H • H • H • H • S⁻¹
        ≈⟨ by-passoc (□ ^ 6) (□ • □ ^ 4 • □) auto ⟩
      S • (H • H • H • H) • S⁻¹
        ≈⟨ cright cleft lemma-order-H ⟩
      S • ε • S⁻¹
        ≈⟨ cright left-unit ⟩
      S • S⁻¹
        ≈⟨ axiom order-S ⟩
      ε ∎

  -- W • Z ≈ X, by cancelling A off the left of both.
  lemma-WZ : W • Z ≈ X
  lemma-WZ = •-cancelˡ {g = A} (trans aux-AWZ (sym aux-AX))

  -- X ≈ Z • W, the other reading of lemma-Z⁻¹X.
  lemma-X≈ZW : X ≈ Z • W
  lemma-X≈ZW = begin
    X                ≈⟨ sym left-unit ⟩
    ε • X            ≈⟨ cleft sym lemma-order-Z ⟩
    (Z • Z⁻¹) • X    ≈⟨ assoc ⟩
    Z • (Z⁻¹ • X)    ≈⟨ cright Z⁻¹X' ⟩
    Z • W ∎

  -- …and so X and Z commute: both X • Z and Z • X are Z • (W • Z).
  lemma-comm-X-Z : X • Z ≈ Z • X
  lemma-comm-X-Z = begin
    X • Z          ≈⟨ cleft lemma-X≈ZW ⟩
    (Z • W) • Z    ≈⟨ assoc ⟩
    Z • (W • Z)    ≈⟨ cright lemma-WZ ⟩
    Z • X ∎


  ------------------------------------------------------------------------
  -- The shared bridge calculus
  --
  -- Everything from here to the bridge itself is relation-agnostic: it
  -- needs only the one-wire axioms and the commutation just proved.  So
  -- it is stated once, in Shared.PauliBase, and instantiated here;
  -- Simplified-V1 instantiates the same module at its own relation, and
  -- Paper-V1.Iso instantiates it a third time to carry the bridge across.
  --
  -- lemma-comm-X-Z is the one hypothesis whose proof genuinely differs
  -- between the two spellings of the multiplier, which is why it is
  -- proved above rather than assumed there.
  module SB = Shared.BridgeCalc n ((₁₊ n) QRel,_===_)
                lemma-order-X lemma-order-Z lemma-comm-Z-S lemma-comm-X-Z
                conj-H-X^k conj-X^k-H lemma-XS
                (λ w → lemma-pow-mod {₁₊ n} {w})
                lemma-Induction lemma-Inductionˡ

  ------------------------------------------------------------------------
  -- Consequences: moving Pauli powers past S⁻¹, and splitting R
  --
  -- Now that X and Z commute an (X • Z⁻¹)-power splits, which is what
  -- makes the exponent bookkeeping below finite.  These are the pieces
  -- lemma-M₋₁-R needs: R is S • Z^½, so an R-power is an S-power with a
  -- Z-power alongside, and reconciling the R-spelling of the multiplier
  -- with the S-spelling is a matter of moving those Z's out.


  ------------------------------------------------------------------------
  -- Pauli powers with ℤₚ exponents
  --
  -- The block laws above take ℕ exponents, but the exponents that turn
  -- up are ℤₚ elements (½, -1, …), and combining two of them is where
  -- the mod-p reduction has to happen.  SB does it once, which is what
  -- keeps the collapse below arithmetic-free: X^ a • X^ b is X^ (a + b)
  -- on the nose, with the wraparound absorbed there.


  open Shared using (neg-mul ; neg-* ; neg-+)


  ------------------------------------------------------------------------
  -- The same, at an arbitrary S-power
  --
  -- lemma-M₋₁-R only needed the block S⁻¹ • H, three times over, because
  -- at -1 all three exponents coincide.  The general bridge between the
  -- R- and S-spellings of the multiplier has blocks S^x • H, S^x⁻¹ • H,
  -- S^x • H, so the laws have to be stated at an arbitrary exponent.
  --
  -- All of it is SB's.  The types are restated rather than the names just
  -- opened, so that this file still records the interface the rest of
  -- Paper-V1 uses — and so that the restatement checks, by conversion,
  -- that Shared's spelling of each word is Paper-V1's.


  ------------------------------------------------------------------------
  -- The bridge between the two spellings of the multiplier
  --
  -- Paper-V0 writes M x as RHR x x⁻¹, an R-word; Paper-V1 writes it as
  -- SHS' x⁻¹ x, an S-word with a Pauli prefix.  They are the same word.
  --
  -- The proof is SB's, and states its right-hand side as that S-word
  -- written out.  Restating it against M x is what records that Paper-V1's
  -- multiplier really is that word: the two are equal by unfolding M and
  -- SHS', so the restatement needs no proof of its own.

  module Bridge (x : ℤ* ₚ) where

    private
      module B = SB.Bridge x

    -- Paper-V0's R-word for the multiplier is Paper-V1's S-word.
    bridge : R^ (x .proj₁)
             • (H • (R^ ((x ⁻¹) .proj₁) • (H • (R^ (x .proj₁) • H))))
             ≈ M x
    bridge = B.bridge

  -- The same for XM, which is the form the axioms are stated over: XM x
  -- is M (x ⁻¹) on both sides, so this is the bridge at x ⁻¹ with the
  -- middle exponent identified by inv-involutive.
  XM-bridge : ∀ (x : ℤ* ₚ) →
    R^ ((x ⁻¹) .proj₁) • (H • (R^ (x .proj₁) • (H • (R^ ((x ⁻¹) .proj₁) • H))))
    ≈ XM x
  XM-bridge x = begin
    R^ ((x ⁻¹) .proj₁) • (H • (R^ (x .proj₁) • (H • (R^ ((x ⁻¹) .proj₁) • H))))
      ≈⟨ refl' (Eq.cong
                  (λ z → R^ ((x ⁻¹) .proj₁)
                         • (H • (R^ z • (H • (R^ ((x ⁻¹) .proj₁) • H)))))
                  (Eq.sym (inv-involutive x))) ⟩
    R^ ((x ⁻¹) .proj₁)
      • (H • (R^ (((x ⁻¹) ⁻¹) .proj₁) • (H • (R^ ((x ⁻¹) .proj₁) • H))))
      ≈⟨ Bridge.bridge (x ⁻¹) ⟩
    M (x ⁻¹)
      ≈⟨ refl' (Eq.sym (XM≡M⁻¹ x)) ⟩
    XM x ∎

  ------------------------------------------------------------------------
  -- A Z-power crossing the multiplier
  --
  -- SB.Z-blocks does the three S-blocks; all that is left is the Pauli
  -- prefix SHS' carries in front of them, and a Z commutes with that
  -- outright — with its Z-part trivially, with its X-part by
  -- lemma-comm-X-Z.  So conjugating by XM x sends Z to Z^x.
  --
  -- This is what semi-MR needs: the axiom is stated with a Z on one side
  -- of the multiplier and none on the other, so the two spellings of it
  -- differ by exactly one application of this.
  Z-XM : ∀ (x : ℤ* ₚ) (k : ℤ ₚ) → Z^ k • XM x ≈ XM x • Z^ ((x .proj₁) * k)
  Z-XM x = SB.MulZ.Z-W x

  ------------------------------------------------------------------------
  -- semi-MR, back in the R-spelling
  --
  -- Paper-V1 states semi-MR over S, with the Pauli that the change of
  -- spelling leaves behind written out on the left.  Paper-V0 states it
  -- over R.  The two are the same rule: R^(g·g) splits as S^(g·g) • Z^(½g²),
  -- and the Z^½ that R contributes on the right crosses the multiplier by
  -- Z-XM, picking up the factor g.  What is left over on each side is
  -- Z^(½g), and cancelling it is the difference between the two
  -- statements.
  lemma-semi-MR-R : XMg {n} • R^ (g * g) ≈ R • XMg
  lemma-semi-MR-R = SB.SemiMR.S⇒R g′ (axiom semi-MR)


  ------------------------------------------------------------------------
  -- The multiplier by -1, spelled out in R and H
  --
  -- Moved here from One-Wire.  Under Paper-V0's RHR spelling this was
  -- immediate — M₋₁ *was* the R-word below, so order-H closed it — but
  -- Paper-V1 spells M₋₁ over SHS', so the two spellings have to be
  -- reconciled.  That reconciliation is the bridge, and this is nothing
  -- but the bridge at x = -1: M₋₁ is by definition M -'₁, so all that is
  -- needed is to recognise the shape.  Two facts do it, both ForStdlib's:
  -- lemma-toℕ-1ₚ (toℕ (-₁) is p-1, which turns the ℕ-indexed powers into
  -- ℤₚ-indexed ones) and aux-₁⁻¹ (-₁ is its own inverse, which collapses
  -- the middle exponent onto the outer two).  order-H then closes it.
  --
  -- This used to be proved directly, by a -1-specific copy of the block
  -- calculus — three copies of S⁻¹ • H rather than S^a • H, S^b • H,
  -- S^a • H.  That copy is gone: the general bridge subsumes it.
  --
  -- It is also the Euler decomposition of the multiplier by -1:
  -- cancelling the trailing H gives R ⁻¹ H R ⁻¹ H R ⁻¹ ≈ H, and hence
  -- R ⁻¹ H R ⁻¹ ≈ H R H ⁻¹.  Paper-V0's derivation of Selinger's c10
  -- turns on that reading; Paper-V1 needs only order-H here.

  lemma-M₋₁-R : R ^ p-1 • (H • (R ^ p-1 • (H • (R ^ p-1 • H)))) ≈ H ^ 2
  lemma-M₋₁-R = begin
    R ^ p-1 • (H • (R ^ p-1 • (H • (R ^ p-1 • H))))
      ≈⟨ refl' (Eq.cong (λ u → R ^ u • (H • (R ^ p-1 • (H • (R ^ u • H)))))
                        (Eq.sym lemma-toℕ-1ₚ)) ⟩
    R^ -₁ • (H • (R ^ p-1 • (H • (R^ -₁ • H))))
      ≈⟨ refl' (Eq.cong (λ v → R^ -₁ • (H • (R ^ v • (H • (R^ -₁ • H))))) mid) ⟩
    R^ -₁ • (H • (R^ ((-'₁ ⁻¹) .proj₁) • (H • (R^ -₁ • H))))
      ≈⟨ Bridge.bridge -'₁ ⟩
    M₋₁
      ≈⟨ sym order-H' ⟩
    H ^ 2 ∎
    where
    -₁ : ℤ ₚ
    -₁ = -'₁ .proj₁

    -- p-1 is toℕ of the middle exponent as well, since -₁ inverts itself.
    mid : p-1 ≡ toℕ ((-'₁ ⁻¹) .proj₁)
    mid = Eq.trans (Eq.sym lemma-toℕ-1ₚ) (Eq.cong toℕ (Eq.sym aux-₁⁻¹))


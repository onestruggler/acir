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

  conj-S-X^k : ∀ k -> S • X ^ k ≈ (X • Z) ^ k • S
  conj-S-X^k k = lemma-Induction conj-S-X k

  conj-S^l-X : ∀ l -> S ^ l • X ≈ X • Z ^ l • S ^ l
  conj-S^l-X l = begin
    S ^ l • X          ≈⟨ lemma-Inductionˡ lemma-SX l ⟩
    X • (Z • S) ^ l    ≈⟨ cright ^-• Z S l lemma-comm-Z-S ⟩
    X • Z ^ l • S ^ l ∎

  -- Z-powers commute with S outright.
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

  -- …and so an X-power costs a Z⁻¹-power.
  conj-X^k-S : ∀ k -> X ^ k • S ≈ S • (X • Z⁻¹) ^ k
  conj-X^k-S k = lemma-Inductionˡ lemma-XS k

  -- X^(-1) spelled as a Z-power exponent is X⁻¹: toℕ (- ₁) is p-1.
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

  -- (2ₚ comes from One-Wire, opened above.)
  aux-half*2 : 1/2 * 2ₚ ≡ ₁
  aux-half*2 = lemma-⁻¹ˡ 2ₚ {{nztoℕ {y = 2ₚ} {neq0 = λ ()}}}

  -- The two exponents M₋₁'s Pauli prefix collapses to: at x = -1 the
  -- shape's Z-exponent is (-1-1)·½ = -1 and its X-exponent is
  -- (1-(-1))·½ = 1.  Both are ℤₚ ring facts on top of aux-half*2; not
  -- refl, since 1/2 is a Bézout witness and does not reduce.  The chain
  -- for the first is
  --
  --   (-₁ + -₁) * ½ ≡ (-(₁ + ₁)) * ½     -‿distrib-+
  --                 ≡ -((₁ + ₁) * ½)     sym -‿distribˡ-*
  --                 ≡ -(2ₚ * ½)          ₁ + ₁ ≡ 2ₚ
  --                 ≡ -(½ * 2ₚ)          *-comm
  --                 ≡ -₁                 aux-half*2
  --
  -- and the second is the same with the signs the other way up.  The
  -- ring is ForStdlib.Data.Fin.Mod.Properties.+-*-ring p-2, so these
  -- come from Algebra.Properties.Ring at that instance.
  private
    2<p : 2 Nat.< p
    2<p = s≤s (s≤s (s≤s z≤n))

    -- ForStdlib's toℕ-+, inlined: it lives in Mod.Prime.Properties,

    1+1≡2 : ₁ + ₁ ≡ 2ₚ
    1+1≡2 = toℕ-injective (Eq.trans (toℕ-+ ₁ ₁) (m<n⇒m%n≡m 2<p))

  -- These are ≡-chains, but `begin` here would clash with the setoid
  -- reasoning this module already has open, so they are spelled with
  -- Eq.trans.  Read each as the chain named in its comment.

  -- ½ + ½ ≡ ½·₁ + ½·₁ ≡ ½·(₁+₁) ≡ ½·2ₚ ≡ ₁
  aux-half+half : 1/2 + 1/2 ≡ ₁
  aux-half+half =
    Eq.trans (Eq.sym (Eq.cong₂ _+_ (*-identityʳ 1/2) (*-identityʳ 1/2)))
      (Eq.trans (Eq.sym (*-distribˡ-+ 1/2 ₁ ₁))
        (Eq.trans (Eq.cong (1/2 *_) 1+1≡2) aux-half*2))

  -- Two halves of x make x:  ½x + ½x ≡ (½+½)·x ≡ ₁·x ≡ x
  aux-half-half : ∀ (x : ℤ ₚ) → 1/2 * x + 1/2 * x ≡ x
  aux-half-half x =
    Eq.trans (Eq.sym (*-distribʳ-+ x 1/2 1/2))
      (Eq.trans (Eq.cong (_* x) aux-half+half) (*-identityˡ x))

  -- -(-x) ≡ -(-x) + 0 ≡ -(-x) + (-x + x) ≡ (-(-x) + -x) + x ≡ 0 + x ≡ x
  neg-involutive : ∀ (x : ℤ ₚ) → - (- x) ≡ x
  neg-involutive x =
    Shared.neg-involutive x

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
      ≈⟨ sym (axiom order-H) ⟩
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

  comm-X-Z^k : ∀ k -> X • Z ^ k ≈ Z ^ k • X
  comm-X-Z^k k = lemma-Induction lemma-comm-X-Z k

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

  split-XZ⁻¹^k : ∀ k -> (X • Z⁻¹) ^ k ≈ X ^ k • Z⁻¹ ^ k
  split-XZ⁻¹^k k = ^-• X Z⁻¹ k (comm-X-Z^k p-1)

  -- Z-powers commute with S⁻¹ as well as with S.
  comm-Z^k-S⁻¹ : ∀ k -> Z ^ k • S⁻¹ ≈ S⁻¹ • Z ^ k
  comm-Z^k-S⁻¹ k = comm⇒pow-comm k p-1 lemma-comm-Z-S

  -- Moving a single X right past S⁻¹ costs a Z⁻¹ …
  conj-S⁻¹-X : S⁻¹ • X ≈ (X • Z⁻¹) • S⁻¹
  conj-S⁻¹-X = trans (conj-S^l-X p-1) (sym assoc)

  -- … and so an X-power costs a Z⁻¹-power.
  conj-S⁻¹-X^k : ∀ k -> S⁻¹ • X ^ k ≈ (X • Z⁻¹) ^ k • S⁻¹
  conj-S⁻¹-X^k k = lemma-Induction conj-S⁻¹-X k

  -- R = S • Z^½, and the two factors commute, so an R-power splits.
  R-split : ∀ k -> R ^ k ≈ S ^ k • (Z^ 1/2) ^ k
  R-split = SB.R-split


  -- Moving X rightward past S, with the X kept on the right: X S X⁻¹ is
  -- S • Z⁻¹, which needs X and Z to commute (lemma-XS leaves the Z⁻¹ on
  -- the far side of the X).
  conj-X-S : X • S ≈ (S • Z⁻¹) • X
  conj-X-S = SB.conj-X-S

  conj-X-S^l : ∀ l -> X • S ^ l ≈ (S • Z⁻¹) ^ l • X
  conj-X-S^l = SB.conj-X-S^l


  ------------------------------------------------------------------------
  -- Pauli powers with ℤₚ exponents
  --
  -- The block laws above take ℕ exponents, but the exponents that turn
  -- up are ℤₚ elements (½, -1, …), and combining two of them is where
  -- the mod-p reduction has to happen.  SB does it once, which is what
  -- keeps the collapse below arithmetic-free: X^ a • X^ b is X^ (a + b)
  -- on the nose, with the wraparound absorbed there.

  X^-+ : ∀ a b -> X^ a • X^ b ≈ X^ (a + b)
  X^-+ = SB.X^-+

  comm-X^k-Z^l : ∀ k l -> X ^ k • Z ^ l ≈ Z ^ l • X ^ k
  comm-X^k-Z^l = SB.comm-X^k-Z^l

  -- The ℤₚ negation facts the bookkeeping needs: (-₁)·k is -k, and
  -- negation passes through both operations.  These mention no relation
  -- at all, so they sit at the top level of Shared.PauliBase.
  open Shared using (neg-mul ; neg-* ; neg-+)

  -- A Z⁻¹-power at a ℤₚ exponent is a Z-power at the negated one.
  Z⁻¹^ : ∀ (k : ℤ ₚ) → Z⁻¹ ^ toℕ k ≈ Z^ (- k)
  Z⁻¹^ = SB.Z⁻¹^


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

  Z^-* : ∀ a b -> (Z^ a) ^ toℕ b ≈ Z^ (a * b)
  Z^-* = SB.Z^-*

  -- Moving a single X past an S-power costs a Z-power …
  X-S^ : ∀ m -> X • S^ m ≈ S^ m • (X • Z^ (- m))
  X-S^ = SB.X-S^

  -- … and an X-power costs a Z-power at the product of the exponents.
  X^-S^ : ∀ k m -> X^ k • S^ m ≈ S^ m • (X^ k • Z^ (- (k * m)))
  X^-S^ = SB.X^-S^

  -- A whole Pauli crossing one block S^m • H: P-B at an arbitrary m.
  P-Bm : ∀ m α β -> (X^ α • Z^ β) • (S^ m • H)
                    ≈ (S^ m • H) • (X^ (β + - (α * m)) • Z^ (- α))
  P-Bm = SB.P-Bm

  -- Absorbing a trailing X-power into the Pauli in front (Pu, general).
  Pu' : ∀ γ δ η -> (X^ γ • Z^ δ) • X^ η ≈ X^ (γ + η) • Z^ δ
  Pu' = SB.Pu'

  -- One R-power with its H is one block with an X-power on the right —
  -- RH, at an arbitrary exponent.
  R^-H : ∀ c -> R^ c • H ≈ (S^ c • H) • X^ (1/2 * c)
  R^-H = SB.R^-H

  -- One block of the general collapse, matching `step` but with the
  -- block's own exponent m rather than -₁ throughout.
  stepm : ∀ w m α β -> (w • (X^ α • Z^ β)) • ((S^ m • H) • X^ (1/2 * m))
          ≈ (w • (S^ m • H))
            • (X^ ((β + - (α * m)) + (1/2 * m)) • Z^ (- α))
  stepm = SB.stepm

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
  -- This is the Euler decomposition c10 turns on: cancelling the trailing
  -- H gives R ⁻¹ H R ⁻¹ H R ⁻¹ ≈ H, and hence R ⁻¹ H R ⁻¹ ≈ H R H ⁻¹,
  -- which is what rewrites c10's right-hand side.

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
      ≈⟨ sym (axiom order-H) ⟩
    H ^ 2 ∎
    where
    -₁ : ℤ ₚ
    -₁ = -'₁ .proj₁

    -- p-1 is toℕ of the middle exponent as well, since -₁ inverts itself.
    mid : p-1 ≡ toℕ ((-'₁ ⁻¹) .proj₁)
    mid = Eq.trans (Eq.sym lemma-toℕ-1ₚ) (Eq.cong toℕ (Eq.sym aux-₁⁻¹))


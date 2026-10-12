{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The two-wire layer of the Paper-V0 calculus, over any family of
-- relations: the Ex-conjugation algebra, and from it Simplified-V1's
-- two-wire rules.
--
-- Paper-V0 axiomatises the swap directly: order-Ex says Ex is an
-- involution, and semi-Ex-S↑ / semi-Ex-H↑ say conjugating by it carries
-- a gate on the upper wire down to the lower one,
--
--     Ex • S ↑ === S • Ex        Ex • H ↑ === H • Ex.
--
-- Ex-Conjugation is the bookkeeping that turns those three axioms into a
-- usable calculus: the opposite direction (a lower-wire gate goes up),
-- the two-sided conjugation forms, and the extension of all of it from
-- single gates to powers and to whole words.  These are the steps that
-- the corresponding symplectic lemmas get for free from Ex's definition
-- as a CZ/H word — a route that is NOT available here, since the
-- symplectic proofs of lemma-comm-Ex-H' and lemma-comm-Ex-H↑' run
-- through lemma-eqn16 / lemma-eqn17 / lemma-CZH↓CZCZ, i.e. through the
-- CZ-H-CZ relations c10 and c11 that Paper-V0 does not have.  On top of
-- it come c10 and c11, and the two Pauli-versus-CZ rules.
--
-- Two-Wire-Calculus takes the family of relations and a Two-Wire-Rules
-- record: the four one-wire rules One-Wire takes, Paper-V0's seven
-- two-wire rules, and the two structural rules a
-- Circuit.Base.Lift-Relation provides: a gate on wire 0 commutes with
-- anything shifted up (comm₁), and equations lift under the shift
-- (lemma-cong↑).  Paper-V0.Lemmas instantiates it at Paper-V0.
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

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas.TwoWire
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

-- The words only, as in OneWire.
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen

open Clifford-Relations
  using ( Z ; X ; Z⁻¹ ; X⁻¹ ; Z^ ; X^ ; R ; R^ ; RHR ; M ; XM ; XM≡M⁻¹
        ; M₁ ; M₋₁ ; Mg ; Mg^ ; XMg ; XMg^ )
-- _↑ commuting with a power; relation-free, so Paper-V0's serves.
open Lemmas-Clifford using (lemma-↑^)

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Lemmas.OneWire
  p-3 p-prime g* g-gen as OW
open OW using (lemma-pow-mod ; lemma-Induction ; lemma-Inductionˡ)

------------------------------------------------------------------------
-- The rules
--
-- A record, for the reasons OneWire gives (M₋₁ again a parameter, fixed
-- by Two-Wire-Rules): each rule is stated as Paper-V0's axiom, as an
-- equation in the relation at the width the axiom has.

record Two-Wire-Rules-At (Γ : (n : ℕ) → WRel (Gen n))
                         (m₋₁ : ∀ {n} → Word (Gen (₁₊ n))) : Set where
  field
    order-S     : ∀ {n} → let open PB (Γ (₁₊ n)) in S ^ p ≈ ε
    order-H     : ∀ {n} → let open PB (Γ (₁₊ n)) in H ^ 2 ≈ m₋₁
    M-power     : ∀ {n} → let open PB (Γ (₁₊ n)) in ∀ k → XMg^ k ≈ XM (g^ k)
    comm-HHSHHS : ∀ {n} → let open PB (Γ (₁₊ n)) in
                   H • H • S • H • H • S ≈ S • H • H • S • H • H
    order-CZ    : ∀ {n} → let open PB (Γ (₂₊ n)) in CZ ^ p ≈ ε
    order-Ex    : ∀ {n} → let open PB (Γ (₂₊ n)) in Ex ^ 2 ≈ ε
    comm-CZ-S↑  : ∀ {n} → let open PB (Γ (₂₊ n)) in CZ • S ↑ ≈ S ↑ • CZ
    semi-M↑CZ   : ∀ {n} → let open PB (Γ (₂₊ n)) in XMg ↑ • CZ^ g ≈ CZ • XMg ↑
    semi-Ex-S↑  : ∀ {n} → let open PB (Γ (₂₊ n)) in Ex • S ↑ ≈ S ↓ • Ex
    semi-Ex-H↑  : ∀ {n} → let open PB (Γ (₂₊ n)) in Ex • H ↑ ≈ H ↓ • Ex
    blake-c12   : ∀ {n} → let open PB (Γ (₂₊ n)) in
                   (S ^ p-1) ↑ • (S ^ p-1) ↓ • CX ^ p-1 • S ↓ • CX ≈ CZ
    comm₁       : ∀ {n} (h : SympGate 1) (x : Gen (₁₊ n)) →
                   let open PB (Γ (₂₊ n)) in
                   [ x ↥ ]ʷ • [ gate₁ h ]ʷ ≈ [ gate₁ h ]ʷ • [ x ↥ ]ʷ
    lemma-cong↑ : ∀ {n} (w v : Word (Gen n)) →
                   PB._≈_ (Γ n) w v → PB._≈_ (Γ (₁₊ n)) (w ↑) (v ↑)

  -- The one-wire rules at one width, as One-Wire takes them.
  one-wire : ∀ {n} → OW.One-Wire-Rules-At (Γ (₁₊ n)) m₋₁
  one-wire = record
    { order-S = order-S ; order-H = order-H ; M-power = M-power
    ; comm-HHSHHS = comm-HHSHHS }

Two-Wire-Rules : ((n : ℕ) → WRel (Gen n)) → Set
Two-Wire-Rules Γ = Two-Wire-Rules-At Γ M₋₁

module Two-Wire-Calculus
  (Γ     : (n : ℕ) → WRel (Gen n))
  (rules : Two-Wire-Rules Γ)
  where

  open Two-Wire-Rules-At rules

  ------------------------------------------------------------------------
  -- The one-wire layer, at every width

  module One-Wire (n : ℕ) = OW.One-Wire n (Γ (₁₊ n)) one-wire

  module Paper-GroupLike = OW.Paper-GroupLike Γ one-wire order-CZ lemma-cong↑

  module One-Wire-Group (n : ℕ) =
    OW.One-Wire-Group n (Γ (₁₊ n)) one-wire (Paper-GroupLike.grouplike {₁₊ n})

  ------------------------------------------------------------------------
  -- The structural commutations
  --
  -- A gate on wire 0 commutes with any word shifted off it.  These are
  -- Syntactics.Lemmas-Clifford's, which are stated over Paper-V0's
  -- relation, restated over Γ from comm₁.

  comm-H : ∀ {n} {x : Gen (₁₊ n)} →
           PB._≈_ (Γ (₂₊ n)) ([ x ↥ ]ʷ • H) (H • [ x ↥ ]ʷ)
  comm-H {x = x} = comm₁ H-gate x

  comm-S : ∀ {n} {x : Gen (₁₊ n)} →
           PB._≈_ (Γ (₂₊ n)) ([ x ↥ ]ʷ • S) (S • [ x ↥ ]ʷ)
  comm-S {x = x} = comm₁ S-gate x

  lemma-comm-S-w↑ : ∀ {n} w → let open PB (Γ (₂₊ n)) in
    
    S • w ↑ ≈ w ↑ • S
    
  lemma-comm-S-w↑ {n} [ x ]ʷ = sym (comm-S)
    where
    open PB (Γ (₂₊ n))
  lemma-comm-S-w↑ {n} ε = trans right-unit (sym left-unit)
    where
    open PB (Γ (₂₊ n))
  lemma-comm-S-w↑ {n} (w • w₁) = begin
    S • ((w • w₁) ↑) ≈⟨ refl ⟩
    S • (w ↑ • w₁ ↑) ≈⟨ sym assoc ⟩
    (S • w ↑) • w₁ ↑ ≈⟨ cong (lemma-comm-S-w↑ w) refl ⟩
    (w ↑ • S) • w₁ ↑ ≈⟨ assoc ⟩
    w ↑ • S • w₁ ↑ ≈⟨ cong refl (lemma-comm-S-w↑ w₁) ⟩
    w ↑ • w₁ ↑ • S ≈⟨ sym assoc ⟩
    ((w • w₁) ↑) • S ∎
    where
    open PB (Γ (₂₊ n))
    open PP (Γ (₂₊ n))
    open SR word-setoid

  lemma-comm-Sᵏ-w↑ : ∀ {n} k w → let open PB (Γ (₂₊ n)) in
    
    S ^ k • w ↑ ≈ w ↑ • S ^ k
    
  lemma-comm-Sᵏ-w↑ {n} ₀ w = trans left-unit (sym right-unit)
    where
    open PB (Γ (₂₊ n))
  lemma-comm-Sᵏ-w↑ {n} ₁ w = lemma-comm-S-w↑ w
    where
    open PB (Γ (₂₊ n))
  lemma-comm-Sᵏ-w↑ {n} (₂₊ k) w = begin
    (S • S ^ ₁₊ k) • (w ↑) ≈⟨ assoc ⟩
    S • S ^ ₁₊ k • (w ↑) ≈⟨ cong refl (lemma-comm-Sᵏ-w↑ (₁₊ k) w) ⟩
    S • (w ↑) • S ^ ₁₊ k ≈⟨ sym assoc ⟩
    (S • w ↑) • S ^ ₁₊ k ≈⟨ cong (lemma-comm-S-w↑ w) refl ⟩
    (w ↑ • S) • S ^ ₁₊ k ≈⟨ assoc ⟩
    (w ↑) • S • S ^ ₁₊ k ∎
    where
    open PB (Γ (₂₊ n))
    open PP (Γ (₂₊ n))
    open SR word-setoid


  lemma-comm-H-w↑ : ∀ {n} w → let open PB (Γ (₂₊ n)) in
    
    H • w ↑ ≈ w ↑ • H
    
  lemma-comm-H-w↑ {n} [ x ]ʷ = sym (comm-H)
    where
    open PB (Γ (₂₊ n))
  lemma-comm-H-w↑ {n} ε = trans right-unit (sym left-unit)
    where
    open PB (Γ (₂₊ n))
  lemma-comm-H-w↑ {n} (w • w₁) = begin
    H • ((w • w₁) ↑) ≈⟨ refl ⟩
    H • (w ↑ • w₁ ↑) ≈⟨ sym assoc ⟩
    (H • w ↑) • w₁ ↑ ≈⟨ cong (lemma-comm-H-w↑ w) refl ⟩
    (w ↑ • H) • w₁ ↑ ≈⟨ assoc ⟩
    w ↑ • H • w₁ ↑ ≈⟨ cong refl (lemma-comm-H-w↑ w₁) ⟩
    w ↑ • w₁ ↑ • H ≈⟨ sym assoc ⟩
    ((w • w₁) ↑) • H ∎
    where
    open PB (Γ (₂₊ n))
    open PP (Γ (₂₊ n))
    open SR word-setoid



  lemma-comm-Hᵏ-w↑ : ∀ {n} k w → let open PB (Γ (₂₊ n)) in
    
    H ^ k • w ↑ ≈ w ↑ • H ^ k
    
  lemma-comm-Hᵏ-w↑ {n} ₀ w = trans left-unit (sym right-unit)
    where
    open PB (Γ (₂₊ n))
  lemma-comm-Hᵏ-w↑ {n} ₁ w = lemma-comm-H-w↑ w
    where
    open PB (Γ (₂₊ n))
  lemma-comm-Hᵏ-w↑ {n} (₂₊ k) w = begin
    (H • H ^ ₁₊ k) • (w ↑) ≈⟨ assoc ⟩
    H • H ^ ₁₊ k • (w ↑) ≈⟨ cong refl (lemma-comm-Hᵏ-w↑ (₁₊ k) w) ⟩
    H • (w ↑) • H ^ ₁₊ k ≈⟨ sym assoc ⟩
    (H • w ↑) • H ^ ₁₊ k ≈⟨ cong (lemma-comm-H-w↑ w) refl ⟩
    (w ↑ • H) • H ^ ₁₊ k ≈⟨ assoc ⟩
    (w ↑) • H • H ^ ₁₊ k ∎
    where
    open PB (Γ (₂₊ n))
    open PP (Γ (₂₊ n))
    open SR word-setoid


  lemma-comm-Z-w↑ : ∀ {n} w → let open PB (Γ (₂₊ n)) in
    
    Z • w ↑ ≈ w ↑ • Z
    
  lemma-comm-Z-w↑ {n} w = begin
    (H • H • S • H • H • S⁻¹) • w ↑ ≈⟨ by-assoc auto ⟩
    (H • H • S • H • H) • S⁻¹ • w ↑ ≈⟨ (cright lemma-comm-Sᵏ-w↑ p-1 w) ⟩
    (H • H • S • H • H) • w ↑ • S⁻¹ ≈⟨ by-assoc auto ⟩
    (H • H • S) • (H ^ 2 • w ↑) • S⁻¹ ≈⟨ (cright cleft lemma-comm-Hᵏ-w↑ 2 w) ⟩
    (H • H • S) • (w ↑ • H ^ 2) • S⁻¹ ≈⟨ by-passoc (□ ^ 3 • □ ^ 2 • □) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
    H ^ 2 • (S • w ↑) • H ^ 2 • S⁻¹ ≈⟨ (cright cleft lemma-comm-Sᵏ-w↑ 1 w) ⟩
    H ^ 2 • (w ↑ • S) • H ^ 2 • S⁻¹ ≈⟨ trans (by-assoc auto) assoc ⟩
    (H ^ 2 • w ↑) • S • H ^ 2 • S⁻¹ ≈⟨ (cleft lemma-comm-Hᵏ-w↑ 2 w) ⟩
    (w ↑ • H ^ 2) • S • H ^ 2 • S⁻¹ ≈⟨ by-passoc (□ ^ 3 • □ • □ ^ 2 • □) (□ • □ ^ 6 ) auto ⟩
    w ↑ • Z ∎
    where
    open PB (Γ (₂₊ n))
    open PP (Γ (₂₊ n))
    open SR word-setoid
    open Pattern-Assoc


  lemma-comm-X-w↑ : ∀ {n} w → let open PB (Γ (₂₊ n)) in
    
    X • w ↑ ≈ w ↑ • X
    
  lemma-comm-X-w↑ {n} w = begin
    (H • S • H • H • S⁻¹ • H) • w ↑ ≈⟨ by-passoc (□ ^ 6 • □) (□ ^ 5 • □ ^ 2) auto ⟩
    (H • S • H • H • S⁻¹) • H • w ↑ ≈⟨ (cright lemma-comm-Hᵏ-w↑ 1 w) ⟩
    (H • S • H • H • S⁻¹) • w ↑ • H ≈⟨ by-passoc (□ ^ 5 • □ ^ 2) (□ ^ 4 • □ ^ 2 • □) auto ⟩
    (H • S • H • H) • (S⁻¹ • w ↑) • H ≈⟨ (cright cleft lemma-comm-Sᵏ-w↑ p-1 w) ⟩
    (H • S • H • H) • (w ↑ • S⁻¹) • H ≈⟨ by-passoc (□ ^ 4 • □ ^ 2 • □) (□ ^ 2 • (□ ^ 2 • □) • □ ^ 2) auto ⟩
    (H • S) • (H ^ 2 • w ↑) • S⁻¹ • H ≈⟨ (cright cleft lemma-comm-Hᵏ-w↑ 2 w) ⟩
    (H • S) • (w ↑ • H ^ 2) • S⁻¹ • H ≈⟨ by-passoc (□ ^ 2 • □ ^ 2 • □ ^ 2) (□ • □ ^ 2 • □ • □ ^ 2) auto ⟩
    H • (S • w ↑) • H ^ 2 • S⁻¹ • H ≈⟨ (cright cleft lemma-comm-Sᵏ-w↑ 1 w) ⟩
    H • (w ↑ • S) • H ^ 2 • S⁻¹ • H ≈⟨ trans (by-assoc auto) assoc ⟩
    (H • w ↑) • S • H ^ 2 • S⁻¹ • H ≈⟨ (cleft lemma-comm-Hᵏ-w↑ 1 w) ⟩
    (w ↑ • H) • S • H ^ 2 • S⁻¹ • H ≈⟨ by-passoc (□ ^ 2 • □ • □ ^ 2 • □ ^ 2) (□ • □ ^ 6) auto ⟩
    w ↑ • X ∎
    where
    open PB (Γ (₂₊ n))
    open PP (Γ (₂₊ n))
    open SR word-setoid
    open Pattern-Assoc



  module Ex-Conjugation (n : ℕ) where

    open PB (Γ (₂₊ n))
    open PP (Γ (₂₊ n))
    open SR word-setoid

    open Group-Lemmas (Γ (₂₊ n)) (Paper-GroupLike.grouplike {₂₊ n})
      using (•-cancelʳ ; •-cancelˡ)


    -- semi-M↑CZ, back in the Mg spelling.  Like semi-MR one wire down, the
    -- axiom is stated over XMg = Mg ⁻¹ and says conjugation by it takes
    -- CZ ^ g to CZ; inserting XMg ↑ • Mg ↑ = ε and cancelling turns that
    -- into the original rule.  The two inverse facts are the one-wire ones
    -- lifted, since Mg and XMg both live on wire 1 here.
    private
      Mg↑XMg↑ : Mg ↑ • XMg ↑ ≈ ε
      Mg↑XMg↑ = lemma-cong↑ _ _ (One-Wire.lemma-Mg-XMg n)

      XMg↑Mg↑ : XMg ↑ • Mg ↑ ≈ ε
      XMg↑Mg↑ = lemma-cong↑ _ _ (One-Wire.lemma-XMg-Mg n)

    lemma-semi-M↑CZ : Mg ↑ • CZ ≈ CZ^ g • Mg ↑
    lemma-semi-M↑CZ = begin
      Mg ↑ • CZ
        ≈⟨ sym right-unit ⟩
      (Mg ↑ • CZ) • ε
        ≈⟨ cright sym XMg↑Mg↑ ⟩
      (Mg ↑ • CZ) • (XMg ↑ • Mg ↑)
        ≈⟨ assoc ⟩
      Mg ↑ • (CZ • (XMg ↑ • Mg ↑))
        ≈⟨ cright sym assoc ⟩
      Mg ↑ • ((CZ • XMg ↑) • Mg ↑)
        ≈⟨ cright cleft sym (semi-M↑CZ) ⟩
      Mg ↑ • ((XMg ↑ • CZ^ g) • Mg ↑)
        ≈⟨ cright assoc ⟩
      Mg ↑ • (XMg ↑ • (CZ^ g • Mg ↑))
        ≈⟨ sym assoc ⟩
      (Mg ↑ • XMg ↑) • (CZ^ g • Mg ↑)
        ≈⟨ cleft Mg↑XMg↑ ⟩
      ε • (CZ^ g • Mg ↑)
        ≈⟨ left-unit ⟩
      CZ^ g • Mg ↑ ∎

    -- order-Ex with the power unfolded: Ex ^ 2 is Ex • (Ex ^ 1) is
    -- Ex • Ex definitionally, so this is the axiom itself.
    lemma-Ex-Ex : Ex • Ex ≈ ε
    lemma-Ex-Ex = order-Ex

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
    lemma-Ex-H↑ = semi-Ex-H↑

    lemma-Ex-S↑ : Ex • S ↑ ≈ S • Ex
    lemma-Ex-S↑ = semi-Ex-S↑

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
      (H ↑ • H) • Ex  ≈⟨ cleft comm-H ⟩
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

    -- The other Pauli, both ways.  X = H • S • H • H • S ⁻¹ • H, so these
    -- are the same six factors as for Z in a different order.

    lemma-Ex-X : Ex • X ≈ X ↑ • Ex
    lemma-Ex-X =
      lemma-Ex-• lemma-Ex-H
        (lemma-Ex-• lemma-Ex-S
          (lemma-Ex-• lemma-Ex-H
            (lemma-Ex-• lemma-Ex-H
              (lemma-Ex-• lemma-Ex-S⁻¹ lemma-Ex-H))))

    lemma-Ex-X↑ : Ex • X ↑ ≈ X • Ex
    lemma-Ex-X↑ =
      lemma-Ex-• lemma-Ex-H↑
        (lemma-Ex-• lemma-Ex-S↑
          (lemma-Ex-• lemma-Ex-H↑
            (lemma-Ex-• lemma-Ex-H↑
              (lemma-Ex-• lemma-Ex-S⁻¹↑ lemma-Ex-H↑))))

    ------------------------------------------------------------------------
    -- Transporting a whole relation along the swap
    --
    -- Ex is an involution, so a relation between two words is equivalent to
    -- the relation between their conjugates.  This is used twice: here for
    -- the upper Pauli rule, and much later to turn c10 into c11.

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

    -- (The two Pauli-versus-CZ rules are proved much further down, once the
    -- multiplier calculus and blake-c12 are both available: see
    -- lemma-rel-X↓-CZ and lemma-rel-X↑-CZ.  transport-Ex is declared here
    -- because it is what carries the lower rule to the upper one, and
    -- because c10 needs it too.)

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
        ≈⟨ cright cleft comm-H ⟩
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
      Ex • (CZ • S ↑) • Ex  ≈⟨ cright cleft comm-CZ-S↑ ⟩
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
      Ex • ((Mg ↑ • CZ) • Ex)       ≈⟨ cright cleft lemma-semi-M↑CZ ⟩
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
        ≈⟨ cleft (lemma-pow-mod (order-CZ) (toℕ g Nat.* toℕ a)) ⟩
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
        ≈⟨ lemma-Induction lemma-semi-M↑CZ (toℕ a) ⟩
      (CZ ^ toℕ g) ^ toℕ a • Mg ↑
        ≈⟨ cleft (^^ CZ (toℕ g) (toℕ a)) ⟩
      CZ ^ (toℕ g Nat.* toℕ a) • Mg ↑
        ≈⟨ cleft (lemma-pow-mod (order-CZ) (toℕ g Nat.* toℕ a)) ⟩
      CZ ^ ((toℕ g Nat.* toℕ a) Nat.% p) • Mg ↑
        ≈⟨ cleft refl' (Eq.cong (CZ ^_) (lemma-toℕ-% g a)) ⟩
      CZ ^ toℕ (g * a) • Mg ↑ ∎

    lemma-Mgᵏ↑-CZ : ∀ j → (Mg ↑) ^ j • CZ ≈ CZ ^ toℕ (g ^′ j) • (Mg ↑) ^ j
    lemma-Mgᵏ↑-CZ ₀ = begin
      ε • CZ  ≈⟨ left-unit ⟩
      CZ      ≈⟨ sym right-unit ⟩
      CZ • ε ∎
    lemma-Mgᵏ↑-CZ ₁ = begin
      Mg ↑ • CZ            ≈⟨ lemma-semi-M↑CZ ⟩
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
      CZ ^ (1 Nat.+ p-1)   ≈⟨ order-CZ ⟩
      ε ∎

    lemma-ₕ|ₕ-invol : ₕ|ₕ • ₕ|ₕ ≈ ε
    lemma-ₕ|ₕ-invol = begin
      (H • CZ • H) • (H • CZ • H)
        ≈⟨ by-assoc auto ⟩
      H • CZ • (H ^ 2 • (CZ • H))
        ≈⟨ cright cright cleft order-H ⟩
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
        ≈⟨ cright cleft sym (order-H) ⟩
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
        ≈⟨ cleft sym (order-H) ⟩
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
          ≈⟨ blake-c12 ⟩
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
        S ^ (1 Nat.+ p-1)  ≈⟨ order-S ⟩
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

    -- The exponent CZ picks up when the multiplier by −1 crosses it, i.e.
    -- p − 1 (lemma-toℕ-1ₚ).  Exposed alongside lemma-CZ-M₋₁ below.
    e₁ : ℕ
    e₁ = toℕ (-'₁ .proj₁)

    private
      M₋₁M₋₁ : M₋₁ • M₋₁ ≈ ε
      M₋₁M₋₁ = One-Wire.lemma-M₋₁^2 (₁₊ n)

    -- lemma-M₋₁-CZ read from the other side, by conjugating with M₋₁.
    -- Exposed rather than private: Redundancy needs it to see that the
    -- square of the missing CZ-versus-H crossing is forced.
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

    -- Z is two multipliers and two phase gates.  Exposed for the same
    -- reason as lemma-CZ-M₋₁.
    Z-split : Z ≈ M₋₁ • (S • (M₋₁ • S⁻¹))
    Z-split = begin
      H • (H • (S • (H • (H • S⁻¹))))
        ≈⟨ sym assoc ⟩
      (H • H) • (S • (H • (H • S⁻¹)))
        ≈⟨ cright cright sym assoc ⟩
      (H • H) • (S • ((H • H) • S⁻¹))
        ≈⟨ cong (order-H) (cright cleft order-H) ⟩
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
    -- The Pauli-versus-CZ rules
    --
    -- Figure 1 states both of these as axioms.  Neither is one here: the
    -- swap derives each from the other, and the survivor is derived below
    -- from blake-c12 and the multiplier calculus.
    --
    -- The rule says what CZ costs when it crosses X.  Read it as
    --
    --     X • CZ ≈ (X • CZ • X ⁻¹) • X
    --
    -- and push the two-wire gate LEFTWARDS through X's six letters, so that
    -- the letters cross it rightwards — which is the direction blake-c12 is
    -- stated in.  (Pushing rightwards instead makes the unknown CZ • H • CZ ⁻¹,
    -- which is Simplified-V1's c11, and Paper-V0 gets c10/c11 out of THIS
    -- rule; that route is circular.)  Each letter conjugates whatever
    -- two-wire word has accumulated, and the accumulated word never leaves
    --
    --     { CZ ^ a , CX ^ b , S ↑ }
    --
    -- because of three facts:
    --
    --   * H conjugates CZ to CX ⁻¹ and CX to CZ.  Both are immediate from
    --     CX = H ³ • CZ • H and H ⁴ ≈ ε; the only "dirt" is the multiplier
    --     H ² = M₋₁, which inverts the CZ it passes (lemma-M₋₁-CZ).
    --
    --   * S conjugates CX to CX • S ↑ • CZ.  This IS blake-c12, rearranged
    --     (blake-A) — the axiom is exactly a statement about S crossing CX
    --     with everything moved to one side.
    --
    --   * S ↑ is on the other wire from every letter of X, so the letters
    --     pass it for free.  That is why no rule for H ↑ against CX is ever
    --     needed, and it is what keeps the calculation finite.
    --
    -- Six crossings later the accumulated word is
    --
    --     D₀ = S ↑ • CX • CZ • S ↑ • CX ⁻¹
    --
    -- and the rule is D₀ ≈ Z ↑ ⁻¹ • CZ.  Collapsing D₀ needs blake once
    -- more, read the other way round: what S does to CX ⁻¹ rather than to
    -- CX.  That is blake-c12 conjugated by the multiplier by −1 on wire 1,
    -- which sends CX to CX ⁻¹, CZ to CZ ⁻¹, fixes S, and sends S ↑ to
    -- S ↑ • Z ↑ (One-Wire.lemma-M₋₁-S, i.e. Z's definition read backwards).
    -- The stray Z ↑ that this introduces IS the Z ↑ of the rule.

    private
      module Derive where

        module CL = One-Wire (₁₊ n)

        ------------------------------------------------------------------
        -- Two combinators
        --
        -- Everything here is of the form "a crosses u, leaving u′ behind".
        -- crossW composes such facts in the thing being crossed, slide in
        -- the thing doing the crossing; between them the whole chain is
        -- built with no associativity bookkeeping at the call sites.

        crossW : ∀ {a u u' v v'} → a • u ≈ u' • a → a • v ≈ v' • a
               → a • (u • v) ≈ (u' • v') • a
        crossW {a} {u} {u'} {v} {v'} eu ev = begin
          a • (u • v)    ≈⟨ sym assoc ⟩
          (a • u) • v    ≈⟨ cleft eu ⟩
          (u' • a) • v   ≈⟨ assoc ⟩
          u' • (a • v)   ≈⟨ cright ev ⟩
          u' • (v' • a)  ≈⟨ sym assoc ⟩
          (u' • v') • a ∎

        slide : ∀ {l V D D' D''} → V • D ≈ D' • V → l • D' ≈ D'' • l
              → (l • V) • D ≈ D'' • (l • V)
        slide {l} {V} {D} {D'} {D''} eV el = begin
          (l • V) • D    ≈⟨ assoc ⟩
          l • (V • D)    ≈⟨ cright eV ⟩
          l • (D' • V)   ≈⟨ sym assoc ⟩
          (l • D') • V   ≈⟨ cleft el ⟩
          (D'' • l) • V  ≈⟨ assoc ⟩
          D'' • (l • V) ∎

        pull : ∀ {a u v} → a • u ≈ u • a → a • (u • v) ≈ u • (a • v)
        pull e = trans (sym assoc) (trans (cleft e) assoc)

        ------------------------------------------------------------------
        -- Orders and inverses used throughout

        H⁴ : H ^ 4 ≈ ε
        H⁴ = CL.lemma-order-H

        H³H : H ^ 3 • H ≈ ε
        H³H = begin
          H ^ 3 • H  ≈⟨ sym (^-+ H 3 1) ⟩
          H ^ 4      ≈⟨ H⁴ ⟩
          ε ∎

        -- H ⁵ is H, so a multiplier absorbed into an H ³ leaves one H.
        H²H³ : M₋₁ • H ^ 3 ≈ H
        H²H³ = begin
          M₋₁ • H ^ 3    ≈⟨ cleft sym (order-H) ⟩
          H ^ 2 • H ^ 3  ≈⟨ sym (^-+ H 2 3) ⟩
          H ^ 5          ≈⟨ cright H⁴ ⟩
          H • ε          ≈⟨ right-unit ⟩
          H ∎

        H³H² : H ^ 3 • M₋₁ ≈ H
        H³H² = begin
          H ^ 3 • M₋₁    ≈⟨ cright sym (order-H) ⟩
          H ^ 3 • H ^ 2  ≈⟨ sym (^-+ H 3 2) ⟩
          H ^ 5          ≈⟨ cright H⁴ ⟩
          H • ε          ≈⟨ right-unit ⟩
          H ∎

        -- H ⁶ is the multiplier by −1 again.
        H³H³ : H ^ 3 • H ^ 3 ≈ M₋₁
        H³H³ = begin
          H ^ 3 • H ^ 3  ≈⟨ sym (^-+ H 3 3) ⟩
          H ^ 6          ≈⟨ ^-+ H 4 2 ⟩
          H ^ 4 • H ^ 2  ≈⟨ cleft H⁴ ⟩
          ε • H ^ 2      ≈⟨ left-unit ⟩
          H ^ 2          ≈⟨ order-H ⟩
          M₋₁ ∎

        CZ⁻CZ : CZ ^ p-1 • CZ ≈ ε
        CZ⁻CZ = begin
          CZ ^ p-1 • CZ       ≈⟨ sym (^-+ CZ p-1 1) ⟩
          CZ ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (CZ ^_) (NP.+-comm p-1 1) ⟩
          CZ ^ p              ≈⟨ order-CZ ⟩
          ε ∎

        S⁻S : S ^ p-1 • S ≈ ε
        S⁻S = begin
          S ^ p-1 • S        ≈⟨ sym (^-+ S p-1 1) ⟩
          S ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (S ^_) (NP.+-comm p-1 1) ⟩
          S ^ p              ≈⟨ CL.lemma-order-S ⟩
          ε ∎

        SS⁻ : S • S ^ p-1 ≈ ε
        SS⁻ = CL.lemma-order-S

        order-S↑ : S ↑ ^ p ≈ ε
        order-S↑ = begin
          S ↑ ^ p    ≡⟨ Eq.sym (lemma-↑^ p S) ⟩
          (S ^ p) ↑  ≈⟨ lemma-cong↑ _ _ (One-Wire.lemma-order-S n) ⟩
          ε ∎

        S↑⁻S↑ : S ↑ ^ p-1 • S ↑ ≈ ε
        S↑⁻S↑ = begin
          S ↑ ^ p-1 • S ↑      ≈⟨ sym (^-+ (S ↑) p-1 1) ⟩
          S ↑ ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (S ↑ ^_) (NP.+-comm p-1 1) ⟩
          S ↑ ^ p              ≈⟨ order-S↑ ⟩
          ε ∎

        S↑S↑⁻ : S ↑ • S ↑ ^ p-1 ≈ ε
        S↑S↑⁻ = order-S↑

        Z↑Z↑⁻ : Z ↑ • Z ↑ ^ p-1 ≈ ε
        Z↑Z↑⁻ = begin
          Z ↑ ^ p    ≡⟨ Eq.sym (lemma-↑^ p Z) ⟩
          (Z ^ p) ↑  ≈⟨ lemma-cong↑ _ _ (One-Wire.lemma-order-Z n) ⟩
          ε ∎

        CZᵉ : CZ ^ toℕ (-'₁ .proj₁) ≈ CZ ^ p-1
        CZᵉ = refl' (Eq.cong (CZ ^_) lemma-toℕ-1ₚ)

        M-CZ : M₋₁ • CZ ≈ CZ ^ p-1 • M₋₁
        M-CZ = trans lemma-M₋₁-CZ (cleft CZᵉ)

        ------------------------------------------------------------------
        -- The CZ / CX quartet
        --
        -- CX is CZ conjugated by an H on wire 0, so conjugating by H again
        -- must come back to CZ — with a sign, because H ² is the multiplier
        -- by −1 and that inverts the CZ it passes.  Naming CX ⁻¹ as a word,
        -- the same conjugation with the H's swapped, keeps every exponent
        -- positive.

        CX⁻ : Word (Gen (₂₊ n))
        CX⁻ = H • (CZ • H ^ 3)

        cH-CX : H • CX ≈ CZ • H
        cH-CX = begin
          H • (H ^ 3 • (CZ • H))   ≈⟨ sym assoc ⟩
          (H • H ^ 3) • (CZ • H)   ≈⟨ cleft H⁴ ⟩
          ε • (CZ • H)             ≈⟨ left-unit ⟩
          CZ • H ∎

        cH-CZ : H • CZ ≈ CX⁻ • H
        cH-CZ = sym (begin
          (H • (CZ • H ^ 3)) • H   ≈⟨ assoc ⟩
          H • ((CZ • H ^ 3) • H)   ≈⟨ cright assoc ⟩
          H • (CZ • (H ^ 3 • H))   ≈⟨ cright cright H³H ⟩
          H • (CZ • ε)             ≈⟨ cright right-unit ⟩
          H • CZ ∎)

        cH-CX⁻ : H • CX⁻ ≈ CZ ^ p-1 • H
        cH-CX⁻ = begin
          H • (H • (CZ • H ^ 3))
            ≈⟨ sym assoc ⟩
          (H • H) • (CZ • H ^ 3)
            ≈⟨ cleft order-H ⟩
          M₋₁ • (CZ • H ^ 3)
            ≈⟨ sym assoc ⟩
          (M₋₁ • CZ) • H ^ 3
            ≈⟨ cleft M-CZ ⟩
          (CZ ^ p-1 • M₋₁) • H ^ 3
            ≈⟨ assoc ⟩
          CZ ^ p-1 • (M₋₁ • H ^ 3)
            ≈⟨ cright H²H³ ⟩
          CZ ^ p-1 • H ∎

        cH-CZ⁻ : H • CZ ^ p-1 ≈ CX • H
        cH-CZ⁻ = sym (begin
          (H ^ 3 • (CZ • H)) • H
            ≈⟨ assoc ⟩
          H ^ 3 • ((CZ • H) • H)
            ≈⟨ cright assoc ⟩
          H ^ 3 • (CZ • (H • H))
            ≈⟨ cright cright order-H ⟩
          H ^ 3 • (CZ • M₋₁)
            ≈⟨ cright lemma-CZ-M₋₁ ⟩
          H ^ 3 • (M₋₁ • CZ ^ e₁)
            ≈⟨ cright cright CZᵉ ⟩
          H ^ 3 • (M₋₁ • CZ ^ p-1)
            ≈⟨ sym assoc ⟩
          (H ^ 3 • M₋₁) • CZ ^ p-1
            ≈⟨ cleft H³H² ⟩
          H • CZ ^ p-1 ∎)

        -- CX ⁻ really is the inverse: conjugating by H is injective, and it
        -- sends both CX ^ (p-1) and CX ⁻ to CZ ^ (p-1).
        CX⁻≈ : CX ^ p-1 ≈ CX⁻
        CX⁻≈ = •-cancelˡ {g = H} (begin
          H • CX ^ p-1   ≈⟨ lemma-Induction cH-CX p-1 ⟩
          CZ ^ p-1 • H   ≈⟨ sym cH-CX⁻ ⟩
          H • CX⁻ ∎)

        CX-CX⁻ : CX • CX⁻ ≈ ε
        CX-CX⁻ = begin
          (H ^ 3 • (CZ • H)) • (H • (CZ • H ^ 3))
            ≈⟨ assoc ⟩
          H ^ 3 • ((CZ • H) • (H • (CZ • H ^ 3)))
            ≈⟨ cright assoc ⟩
          H ^ 3 • (CZ • (H • (H • (CZ • H ^ 3))))
            ≈⟨ cright cright cH-CX⁻ ⟩
          H ^ 3 • (CZ • (CZ ^ p-1 • H))
            ≈⟨ cright sym assoc ⟩
          H ^ 3 • ((CZ • CZ ^ p-1) • H)
            ≈⟨ cright cleft (order-CZ) ⟩
          H ^ 3 • (ε • H)
            ≈⟨ cright left-unit ⟩
          H ^ 3 • H
            ≈⟨ H³H ⟩
          ε ∎

        CX⁻-CX : CX⁻ • CX ≈ ε
        CX⁻-CX = begin
          (H • (CZ • H ^ 3)) • (H ^ 3 • (CZ • H))
            ≈⟨ assoc ⟩
          H • ((CZ • H ^ 3) • (H ^ 3 • (CZ • H)))
            ≈⟨ cright assoc ⟩
          H • (CZ • (H ^ 3 • (H ^ 3 • (CZ • H))))
            ≈⟨ cright cright sym assoc ⟩
          H • (CZ • ((H ^ 3 • H ^ 3) • (CZ • H)))
            ≈⟨ cright cright cleft H³H³ ⟩
          H • (CZ • (M₋₁ • (CZ • H)))
            ≈⟨ cright cright sym assoc ⟩
          H • (CZ • ((M₋₁ • CZ) • H))
            ≈⟨ cright cright cleft M-CZ ⟩
          H • (CZ • ((CZ ^ p-1 • M₋₁) • H))
            ≈⟨ cright cright assoc ⟩
          H • (CZ • (CZ ^ p-1 • (M₋₁ • H)))
            ≈⟨ cright sym assoc ⟩
          H • ((CZ • CZ ^ p-1) • (M₋₁ • H))
            ≈⟨ cright cleft (order-CZ) ⟩
          H • (ε • (M₋₁ • H))
            ≈⟨ cright left-unit ⟩
          H • (M₋₁ • H)
            ≈⟨ sym assoc ⟩
          (H • M₋₁) • H
            ≈⟨ cleft cright sym (order-H) ⟩
          H ^ 3 • H
            ≈⟨ H³H ⟩
          ε ∎

        ------------------------------------------------------------------
        -- blake-c12 as a crossing rule
        --
        -- The axiom is exactly "what S costs when it crosses CX", written
        -- with everything moved to one side.  Moving it back is pure
        -- cancellation.

        blake₀ : S ↑ ^ p-1 • (S ^ p-1 • (CX⁻ • (S • CX))) ≈ CZ
        blake₀ = begin
          S ↑ ^ p-1 • (S ^ p-1 • (CX⁻ • (S • CX)))
            ≈⟨ cright cright cleft sym CX⁻≈ ⟩
          S ↑ ^ p-1 • (S ^ p-1 • (CX ^ p-1 • (S • CX)))
            ≡⟨ Eq.cong (λ w → w • (S ^ p-1 • (CX ^ p-1 • (S • CX))))
                       (Eq.sym (lemma-↑^ p-1 S)) ⟩
          (S ^ p-1) ↑ • (S ^ p-1 • (CX ^ p-1 • (S • CX)))
            ≈⟨ blake-c12 ⟩
          CZ ∎

        blake-A : CX⁻ • (S • CX) ≈ S • (S ↑ • CZ)
        blake-A = •-cancelˡ {g = S ↑ ^ p-1 • S ^ p-1} (begin
          (S ↑ ^ p-1 • S ^ p-1) • (CX⁻ • (S • CX))
            ≈⟨ assoc ⟩
          S ↑ ^ p-1 • (S ^ p-1 • (CX⁻ • (S • CX)))
            ≈⟨ blake₀ ⟩
          CZ
            ≈⟨ sym left-unit ⟩
          ε • CZ
            ≈⟨ cleft sym S↑⁻S↑ ⟩
          (S ↑ ^ p-1 • S ↑) • CZ
            ≈⟨ assoc ⟩
          S ↑ ^ p-1 • (S ↑ • CZ)
            ≈⟨ cright sym left-unit ⟩
          S ↑ ^ p-1 • (ε • (S ↑ • CZ))
            ≈⟨ cright cleft sym S⁻S ⟩
          S ↑ ^ p-1 • ((S ^ p-1 • S) • (S ↑ • CZ))
            ≈⟨ cright assoc ⟩
          S ↑ ^ p-1 • (S ^ p-1 • (S • (S ↑ • CZ)))
            ≈⟨ sym assoc ⟩
          (S ↑ ^ p-1 • S ^ p-1) • (S • (S ↑ • CZ)) ∎)

        -- What S costs crossing CX: it leaves an S ↑ and a CZ behind.
        cS-CX : S • CX ≈ (CX • (S ↑ • CZ)) • S
        cS-CX = begin
          S • CX
            ≈⟨ sym left-unit ⟩
          ε • (S • CX)
            ≈⟨ cleft sym CX-CX⁻ ⟩
          (CX • CX⁻) • (S • CX)
            ≈⟨ assoc ⟩
          CX • (CX⁻ • (S • CX))
            ≈⟨ cright blake-A ⟩
          CX • (S • (S ↑ • CZ))
            ≈⟨ cright sym assoc ⟩
          CX • ((S • S ↑) • CZ)
            ≈⟨ cright cleft lemma-comm-S-w↑ S ⟩
          CX • ((S ↑ • S) • CZ)
            ≈⟨ cright assoc ⟩
          CX • (S ↑ • (S • CZ))
            ≈⟨ cright cright sym lemma-comm-CZ-S ⟩
          CX • (S ↑ • (CZ • S))
            ≈⟨ cright sym assoc ⟩
          CX • ((S ↑ • CZ) • S)
            ≈⟨ sym assoc ⟩
          (CX • (S ↑ • CZ)) • S ∎

        -- The same for S ⁻¹ crossing CX ⁻, which is what X's fifth letter
        -- needs: blake-A with the CX moved to the other side, then flipped.
        blake-B : CX⁻ • S ≈ S • (S ↑ • (CZ • CX⁻))
        blake-B = begin
          CX⁻ • S
            ≈⟨ sym right-unit ⟩
          (CX⁻ • S) • ε
            ≈⟨ cright sym CX-CX⁻ ⟩
          (CX⁻ • S) • (CX • CX⁻)
            ≈⟨ assoc ⟩
          CX⁻ • (S • (CX • CX⁻))
            ≈⟨ cright sym assoc ⟩
          CX⁻ • ((S • CX) • CX⁻)
            ≈⟨ sym assoc ⟩
          (CX⁻ • (S • CX)) • CX⁻
            ≈⟨ cleft blake-A ⟩
          (S • (S ↑ • CZ)) • CX⁻
            ≈⟨ assoc ⟩
          S • ((S ↑ • CZ) • CX⁻)
            ≈⟨ cright assoc ⟩
          S • (S ↑ • (CZ • CX⁻)) ∎

        cS⁻-CX⁻ : S ^ p-1 • CX⁻ ≈ (S ↑ • (CZ • CX⁻)) • S ^ p-1
        cS⁻-CX⁻ = •-cancelˡ {g = S} (begin
          S • (S ^ p-1 • CX⁻)
            ≈⟨ sym assoc ⟩
          (S • S ^ p-1) • CX⁻
            ≈⟨ cleft SS⁻ ⟩
          ε • CX⁻
            ≈⟨ left-unit ⟩
          CX⁻
            ≈⟨ sym right-unit ⟩
          CX⁻ • ε
            ≈⟨ cright sym SS⁻ ⟩
          CX⁻ • (S • S ^ p-1)
            ≈⟨ sym assoc ⟩
          (CX⁻ • S) • S ^ p-1
            ≈⟨ cleft blake-B ⟩
          (S • (S ↑ • (CZ • CX⁻))) • S ^ p-1
            ≈⟨ assoc ⟩
          S • ((S ↑ • (CZ • CX⁻)) • S ^ p-1) ∎)

        ------------------------------------------------------------------
        -- blake read the other way, by the multiplier on wire 1
        --
        -- Conjugating by M₋₁ ↑ swaps CX with CX ⁻ and CZ with CZ ⁻¹, fixes
        -- S (other wire) and sends S ↑ to S ↑ • Z ↑.  Applying it to blake-A
        -- gives what S does to CX ⁻ — and the Z ↑ it drops is the Z ↑ the
        -- rule is about.

        mu-S : M₋₁ ↑ • S ≈ S • M₋₁ ↑
        mu-S = sym (lemma-comm-S-w↑ M₋₁)

        mu-H : M₋₁ ↑ • H ≈ H • M₋₁ ↑
        mu-H = sym (lemma-comm-H-w↑ M₋₁)

        mu-H³ : M₋₁ ↑ • H ^ 3 ≈ H ^ 3 • M₋₁ ↑
        mu-H³ = sym (lemma-comm-Hᵏ-w↑ 3 M₋₁)

        mu-CZ : M₋₁ ↑ • CZ ≈ CZ ^ p-1 • M₋₁ ↑
        mu-CZ = trans lemma-M₋₁↑-CZ (cleft CZᵉ)

        mu-S↑ : M₋₁ ↑ • S ↑ ≈ (S ↑ • Z ↑) • M₋₁ ↑
        mu-S↑ = lemma-cong↑ _ _ (One-Wire.lemma-M₋₁-S n)

        mu-CX : M₋₁ ↑ • CX ≈ CX⁻ • M₋₁ ↑
        mu-CX = begin
          M₋₁ ↑ • (H ^ 3 • (CZ • H))
            ≈⟨ crossW mu-H³ (crossW mu-CZ mu-H) ⟩
          (H ^ 3 • (CZ ^ p-1 • H)) • M₋₁ ↑
            ≈⟨ cleft cright sym cH-CX⁻ ⟩
          (H ^ 3 • (H • CX⁻)) • M₋₁ ↑
            ≈⟨ cleft sym assoc ⟩
          ((H ^ 3 • H) • CX⁻) • M₋₁ ↑
            ≈⟨ cleft cleft H³H ⟩
          (ε • CX⁻) • M₋₁ ↑
            ≈⟨ cleft left-unit ⟩
          CX⁻ • M₋₁ ↑ ∎

        mu-CX⁻ : M₋₁ ↑ • CX⁻ ≈ CX • M₋₁ ↑
        mu-CX⁻ = begin
          M₋₁ ↑ • (H • (CZ • H ^ 3))
            ≈⟨ crossW mu-H (crossW mu-CZ mu-H³) ⟩
          (H • (CZ ^ p-1 • H ^ 3)) • M₋₁ ↑
            ≈⟨ cleft sym assoc ⟩
          ((H • CZ ^ p-1) • H ^ 3) • M₋₁ ↑
            ≈⟨ cleft cleft cH-CZ⁻ ⟩
          ((CX • H) • H ^ 3) • M₋₁ ↑
            ≈⟨ cleft assoc ⟩
          (CX • (H • H ^ 3)) • M₋₁ ↑
            ≈⟨ cleft cright H⁴ ⟩
          (CX • ε) • M₋₁ ↑
            ≈⟨ cleft right-unit ⟩
          CX • M₋₁ ↑ ∎

        blake-flip : CX • (S • CX⁻) ≈ S • (S ↑ • (Z ↑ • CZ ^ p-1))
        blake-flip = •-cancelʳ {h = M₋₁ ↑} (begin
          (CX • (S • CX⁻)) • M₋₁ ↑
            ≈⟨ sym (crossW mu-CX⁻ (crossW mu-S mu-CX)) ⟩
          M₋₁ ↑ • (CX⁻ • (S • CX))
            ≈⟨ cright blake-A ⟩
          M₋₁ ↑ • (S • (S ↑ • CZ))
            ≈⟨ crossW mu-S (crossW mu-S↑ mu-CZ) ⟩
          (S • ((S ↑ • Z ↑) • CZ ^ p-1)) • M₋₁ ↑
            ≈⟨ cleft cright assoc ⟩
          (S • (S ↑ • (Z ↑ • CZ ^ p-1))) • M₋₁ ↑ ∎)

        -- …and the same with S ⁻¹, which is the form the collapse needs.
        -- Both sides are inverse to CX • (S • CX ⁻), and inverses are
        -- unique.  Note the order chosen on the right: the four
        -- cancellations are already nested one inside the next, so nothing
        -- has to be commuted.
        blake-flip⁻ : CX • (S ^ p-1 • CX⁻)
                    ≈ CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1))
        blake-flip⁻ = •-cancelˡ {g = CX • (S • CX⁻)} (trans left right)
          where
          left : (CX • (S • CX⁻)) • (CX • (S ^ p-1 • CX⁻)) ≈ ε
          left = begin
            (CX • (S • CX⁻)) • (CX • (S ^ p-1 • CX⁻))
              ≈⟨ assoc ⟩
            CX • ((S • CX⁻) • (CX • (S ^ p-1 • CX⁻)))
              ≈⟨ cright assoc ⟩
            CX • (S • (CX⁻ • (CX • (S ^ p-1 • CX⁻))))
              ≈⟨ cright cright sym assoc ⟩
            CX • (S • ((CX⁻ • CX) • (S ^ p-1 • CX⁻)))
              ≈⟨ cright cright cleft CX⁻-CX ⟩
            CX • (S • (ε • (S ^ p-1 • CX⁻)))
              ≈⟨ cright cright left-unit ⟩
            CX • (S • (S ^ p-1 • CX⁻))
              ≈⟨ cright sym assoc ⟩
            CX • ((S • S ^ p-1) • CX⁻)
              ≈⟨ cright cleft SS⁻ ⟩
            CX • (ε • CX⁻)
              ≈⟨ cright left-unit ⟩
            CX • CX⁻
              ≈⟨ CX-CX⁻ ⟩
            ε ∎

          right : ε ≈ (CX • (S • CX⁻))
                    • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))
          right = sym (begin
            (CX • (S • CX⁻)) • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))
              ≈⟨ cleft blake-flip ⟩
            (S • (S ↑ • (Z ↑ • CZ ^ p-1)))
              • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))
              ≈⟨ assoc ⟩
            S • ((S ↑ • (Z ↑ • CZ ^ p-1))
                   • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1))))
              ≈⟨ cright assoc ⟩
            S • (S ↑ • ((Z ↑ • CZ ^ p-1)
                   • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))))
              ≈⟨ cright cright assoc ⟩
            S • (S ↑ • (Z ↑ • (CZ ^ p-1
                   • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1))))))
              ≈⟨ cright cright cright sym assoc ⟩
            S • (S ↑ • (Z ↑ • ((CZ ^ p-1 • CZ)
                   • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))))
              ≈⟨ cright cright cright cleft CZ⁻CZ ⟩
            S • (S ↑ • (Z ↑ • (ε • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))))
              ≈⟨ cright cright cright left-unit ⟩
            S • (S ↑ • (Z ↑ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1))))
              ≈⟨ cright cright sym assoc ⟩
            S • (S ↑ • ((Z ↑ • Z ↑ ^ p-1) • (S ↑ ^ p-1 • S ^ p-1)))
              ≈⟨ cright cright cleft Z↑Z↑⁻ ⟩
            S • (S ↑ • (ε • (S ↑ ^ p-1 • S ^ p-1)))
              ≈⟨ cright cright left-unit ⟩
            S • (S ↑ • (S ↑ ^ p-1 • S ^ p-1))
              ≈⟨ cright sym assoc ⟩
            S • ((S ↑ • S ↑ ^ p-1) • S ^ p-1)
              ≈⟨ cright cleft S↑S↑⁻ ⟩
            S • (ε • S ^ p-1)
              ≈⟨ cright left-unit ⟩
            S • S ^ p-1
              ≈⟨ SS⁻ ⟩
            ε ∎)

        ------------------------------------------------------------------
        -- The six crossings
        --
        -- X = H • S • H • H • S ⁻¹ • H, read right to left.  Each letter
        -- conjugates the accumulated two-wire word; S ↑ is inert because
        -- every letter of X is on wire 0.

        cH-S↑ : H • S ↑ ≈ S ↑ • H
        cH-S↑ = lemma-comm-H-w↑ S

        cS-S↑ : S • S ↑ ≈ S ↑ • S
        cS-S↑ = lemma-comm-S-w↑ S

        cS-CZ⁻ : S • CZ ^ p-1 ≈ CZ ^ p-1 • S
        cS-CZ⁻ = comm⇒pow-comm 1 p-1 (sym lemma-comm-CZ-S)

        c₁ : H • CZ ≈ CX⁻ • H
        c₁ = cH-CZ

        c₂ : S ^ p-1 • CX⁻ ≈ (S ↑ • (CZ • CX⁻)) • S ^ p-1
        c₂ = cS⁻-CX⁻

        c₃ : H • (S ↑ • (CZ • CX⁻)) ≈ (S ↑ • (CX⁻ • CZ ^ p-1)) • H
        c₃ = crossW cH-S↑ (crossW cH-CZ cH-CX⁻)

        c₄ : H • (S ↑ • (CX⁻ • CZ ^ p-1)) ≈ (S ↑ • (CZ ^ p-1 • CX)) • H
        c₄ = crossW cH-S↑ (crossW cH-CX⁻ cH-CZ⁻)

        c₅ : S • (S ↑ • (CZ ^ p-1 • CX))
           ≈ (S ↑ • (CZ ^ p-1 • (CX • (S ↑ • CZ)))) • S
        c₅ = crossW cS-S↑ (crossW cS-CZ⁻ cS-CX)

        c₆ : H • (S ↑ • (CZ ^ p-1 • (CX • (S ↑ • CZ))))
           ≈ (S ↑ • (CX • (CZ • (S ↑ • CX⁻)))) • H
        c₆ = crossW cH-S↑ (crossW cH-CZ⁻ (crossW cH-CX (crossW cH-S↑ cH-CZ)))

        -- What X conjugates CZ into.
        D₀ : Word (Gen (₂₊ n))
        D₀ = S ↑ • (CX • (CZ • (S ↑ • CX⁻)))

        lemma-chain : X • CZ ≈ D₀ • X
        lemma-chain = slide (slide (slide (slide (slide c₁ c₂) c₃) c₄) c₅) c₆

        ------------------------------------------------------------------
        -- …and D₀ collapses
        --
        -- Fold CX • S ↑ • CZ back into S • CX • S ⁻¹ (blake, cS-CX),
        -- leaving CX • S ⁻¹ • CX ⁻ — which is blake-flip⁻.  Everything then
        -- cancels except the Z ↑ ⁻¹ the flip introduced.

        W : Word (Gen (₂₊ n))
        W = S ↑ • S

        W-CZ : W • CZ ≈ CZ • W
        W-CZ = slide (sym lemma-comm-CZ-S) (sym (comm-CZ-S↑))

        comm-S↑-Z↑ : S ↑ • Z ↑ ^ p-1 ≈ Z ↑ ^ p-1 • S ↑
        comm-S↑-Z↑ = comm⇒pow-comm 1 p-1
          (sym (lemma-cong↑ _ _ (One-Wire.lemma-comm-Z-S n)))

        comm-S-Z↑ : S • Z ↑ ^ p-1 ≈ Z ↑ ^ p-1 • S
        comm-S-Z↑ = comm⇒pow-comm 1 p-1 (lemma-comm-S-w↑ Z)

        W-Z↑ : W • Z ↑ ^ p-1 ≈ Z ↑ ^ p-1 • W
        W-Z↑ = slide comm-S-Z↑ comm-S↑-Z↑

        W-kill : W • (S ↑ ^ p-1 • S ^ p-1) ≈ ε
        W-kill = begin
          (S ↑ • S) • (S ↑ ^ p-1 • S ^ p-1)
            ≈⟨ assoc ⟩
          S ↑ • (S • (S ↑ ^ p-1 • S ^ p-1))
            ≈⟨ cright sym assoc ⟩
          S ↑ • ((S • S ↑ ^ p-1) • S ^ p-1)
            ≈⟨ cright cleft comm⇒pow-comm 1 p-1 (lemma-comm-S-w↑ S) ⟩
          S ↑ • ((S ↑ ^ p-1 • S) • S ^ p-1)
            ≈⟨ cright assoc ⟩
          S ↑ • (S ↑ ^ p-1 • (S • S ^ p-1))
            ≈⟨ cright cright SS⁻ ⟩
          S ↑ • (S ↑ ^ p-1 • ε)
            ≈⟨ cright right-unit ⟩
          S ↑ • S ↑ ^ p-1
            ≈⟨ S↑S↑⁻ ⟩
          ε ∎

        lemma-D₀ : D₀ ≈ Z ↑ ^ p-1 • CZ
        lemma-D₀ = begin
          S ↑ • (CX • (CZ • (S ↑ • CX⁻)))
            ≈⟨ cright cright sym assoc ⟩
          S ↑ • (CX • ((CZ • S ↑) • CX⁻))
            ≈⟨ cright cright cleft (comm-CZ-S↑) ⟩
          S ↑ • (CX • ((S ↑ • CZ) • CX⁻))
            ≈⟨ cright sym assoc ⟩
          S ↑ • ((CX • (S ↑ • CZ)) • CX⁻)
            ≈⟨ cright cleft sym unfold ⟩
          S ↑ • ((S • (CX • S ^ p-1)) • CX⁻)
            ≈⟨ cright assoc ⟩
          S ↑ • (S • ((CX • S ^ p-1) • CX⁻))
            ≈⟨ cright cright assoc ⟩
          S ↑ • (S • (CX • (S ^ p-1 • CX⁻)))
            ≈⟨ cright cright blake-flip⁻ ⟩
          S ↑ • (S • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1))))
            ≈⟨ sym assoc ⟩
          W • (CZ • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))
            ≈⟨ pull W-CZ ⟩
          CZ • (W • (Z ↑ ^ p-1 • (S ↑ ^ p-1 • S ^ p-1)))
            ≈⟨ cright pull W-Z↑ ⟩
          CZ • (Z ↑ ^ p-1 • (W • (S ↑ ^ p-1 • S ^ p-1)))
            ≈⟨ cright cright W-kill ⟩
          CZ • (Z ↑ ^ p-1 • ε)
            ≈⟨ cright right-unit ⟩
          CZ • Z ↑ ^ p-1
            ≈⟨ comm⇒pow-comm 1 p-1 lemma-comm-CZ-Z↑ ⟩
          Z ↑ ^ p-1 • CZ ∎
          where
          -- cS-CX with the trailing S moved across: S • CX • S ⁻¹.
          unfold : S • (CX • S ^ p-1) ≈ CX • (S ↑ • CZ)
          unfold = begin
            S • (CX • S ^ p-1)
              ≈⟨ sym assoc ⟩
            (S • CX) • S ^ p-1
              ≈⟨ cleft cS-CX ⟩
            ((CX • (S ↑ • CZ)) • S) • S ^ p-1
              ≈⟨ assoc ⟩
            (CX • (S ↑ • CZ)) • (S • S ^ p-1)
              ≈⟨ cright SS⁻ ⟩
            (CX • (S ↑ • CZ)) • ε
              ≈⟨ right-unit ⟩
            CX • (S ↑ • CZ) ∎

        lemma-rel-X↓-CZ : CZ • X ↓ ≈ X ↓ • (Z ↑ • CZ)
        lemma-rel-X↓-CZ = sym (begin
          X • (Z ↑ • CZ)
            ≈⟨ sym assoc ⟩
          (X • Z ↑) • CZ
            ≈⟨ cleft (lemma-comm-X-w↑ Z) ⟩
          (Z ↑ • X) • CZ
            ≈⟨ assoc ⟩
          Z ↑ • (X • CZ)
            ≈⟨ cright lemma-chain ⟩
          Z ↑ • (D₀ • X)
            ≈⟨ cright cleft lemma-D₀ ⟩
          Z ↑ • ((Z ↑ ^ p-1 • CZ) • X)
            ≈⟨ sym assoc ⟩
          (Z ↑ • (Z ↑ ^ p-1 • CZ)) • X
            ≈⟨ cleft sym assoc ⟩
          ((Z ↑ • Z ↑ ^ p-1) • CZ) • X
            ≈⟨ cleft cleft Z↑Z↑⁻ ⟩
          (ε • CZ) • X
            ≈⟨ cleft left-unit ⟩
          CZ • X ∎)

    -- The lower rule, exactly as Figure 1 states it — but a theorem.
    lemma-rel-X↓-CZ : CZ • X ↓ ≈ X ↓ • (Z ↑ • CZ)
    lemma-rel-X↓-CZ = Derive.lemma-rel-X↓-CZ

    -- …and the upper one, which is the lower one conjugated by the swap.
    -- Ex fixes CZ (lemma-Ex-CZ) and exchanges the wires, so transporting
    -- CZ • X ↓ ≈ X ↓ • Z ↑ • CZ across it gives CZ • X ↑ ≈ X ↑ • Z ↓ • CZ.
    lemma-rel-X↑-CZ : CZ • X ↑ ≈ X ↑ • (Z • CZ)
    lemma-rel-X↑-CZ = transport-Ex lhs rhs lemma-rel-X↓-CZ
      where
      lhs : Ex • (CZ • X) ≈ (CZ • X ↑) • Ex
      lhs = lemma-Ex-• lemma-Ex-CZ lemma-Ex-X

      rhs : Ex • (X • (Z ↑ • CZ)) ≈ (X ↑ • (Z • CZ)) • Ex
      rhs = lemma-Ex-• lemma-Ex-X (lemma-Ex-• lemma-Ex-Z↑ lemma-Ex-CZ)

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
    lemma-CZ-X↑ᵏ ₁ = lemma-rel-X↑-CZ
    lemma-CZ-X↑ᵏ (₂₊ k) = begin
      CZ • (X ↑ • (X ↑) ^ ₁₊ k)
        ≈⟨ sym assoc ⟩
      (CZ • X ↑) • (X ↑) ^ ₁₊ k
        ≈⟨ cleft lemma-rel-X↑-CZ ⟩
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
    lemma-CZᵏ-X↑ ₁ = lemma-rel-X↑-CZ
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
        (H ↑) ^ 2              ≈⟨ lemma-cong↑ _ _ (order-H) ⟩
        M₋₁ ↑ ∎

      M₋₁↑H↑ : M₋₁ ↑ • H ↑ ≈ (H ↑) ^ 3
      M₋₁↑H↑ = begin
        M₋₁ ↑ • H ↑      ≈⟨ cleft sym (lemma-cong↑ _ _ (order-H)) ⟩
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
        (H ↑) ^ 3 • (CZ ^ p • H ↑)  ≈⟨ cright cleft order-CZ ⟩
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
          ≈⟨ cleft comm-CZ-S↑ ⟩
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
    -- (transport-Ex itself is declared much earlier, since rel-X↑-CZ is
    -- transported the same way and is needed long before this.)

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
    -- The swap from half-swaps, and from CX-type gates
    --
    -- Three half-swaps make the swap in either order, and moving the
    -- multipliers out of them writes it with CX-type gates and the
    -- multiplier by −1 alone:
    --
    --     Ex ≈ CX • XC' • CX • M₋₁,
    --
    -- where XC' = H ↑ • CZ • H ↑ ^ 3 is the inverse of XC.  ThreeWire lifts
    -- all three to wires 1-2, where they are what derives cz-slide.  The
    -- inverse of CX that Derive works with, CX' = H • CZ • H ^ 3, is
    -- exported with its inverse laws for the same reason.

    open Pattern-Assoc using (by-passoc ; □)

    lemma-CX-CX' : CX • CX' ≈ ε
    lemma-CX-CX' = Derive.CX-CX⁻

    lemma-CX'-CX : CX' • CX ≈ ε
    lemma-CX'-CX = Derive.CX⁻-CX

    lemma-Ex-hhh : Ex ≈ ₕ|ₕ • (ʰ|ʰ • ₕ|ₕ)
    lemma-Ex-hhh = sym (begin
      ₕ|ₕ • (ʰ|ʰ • ₕ|ₕ)   ≈⟨ sym assoc ⟩
      (ₕ|ₕ • ʰ|ʰ) • ₕ|ₕ   ≈⟨ cleft lemma-⊥⊤-simple ⟩
      (Ex • ₕ|ₕ) • ₕ|ₕ    ≈⟨ assoc ⟩
      Ex • (ₕ|ₕ • ₕ|ₕ)    ≈⟨ cright lemma-ₕ|ₕ-invol ⟩
      Ex • ε              ≈⟨ right-unit ⟩
      Ex ∎)

    lemma-Ex-hhh' : Ex ≈ ʰ|ʰ • (ₕ|ₕ • ʰ|ʰ)
    lemma-Ex-hhh' = sym (begin
      ʰ|ʰ • (ₕ|ₕ • ʰ|ʰ)   ≈⟨ sym assoc ⟩
      (ʰ|ʰ • ₕ|ₕ) • ʰ|ʰ   ≈⟨ cleft lemma-⊤⊥-simple ⟩
      (ₕ|ₕ • Ex) • ʰ|ʰ    ≈⟨ assoc ⟩
      ₕ|ₕ • (Ex • ʰ|ʰ)    ≈⟨ cright lemma-Ex-ʰ|ʰ ⟩
      ₕ|ₕ • (ₕ|ₕ • Ex)    ≈⟨ sym assoc ⟩
      (ₕ|ₕ • ₕ|ₕ) • Ex    ≈⟨ cleft lemma-ₕ|ₕ-invol ⟩
      ε • Ex              ≈⟨ left-unit ⟩
      Ex ∎)

    private
      H⁴' : H ^ 4 ≈ ε
      H⁴' = One-Wire.lemma-order-H (₁₊ n)

      H↑²≈M↑ : (H ↑) ^ 2 ≈ M₋₁ ↑
      H↑²≈M↑ = lemma-cong↑ _ _ order-H

      -- The half-swaps with their multipliers split off.
      ₕ|ₕ-CX' : ₕ|ₕ ≈ CX' • M₋₁
      ₕ|ₕ-CX' = sym (begin
        (H • (CZ • H ^ 3)) • M₋₁      ≈⟨ cright sym order-H ⟩
        (H • (CZ • H ^ 3)) • H ^ 2    ≈⟨ by-assoc auto ⟩
        H • (CZ • (H ^ 4 • H))        ≈⟨ cright cright cleft H⁴' ⟩
        H • (CZ • (ε • H))            ≈⟨ cright cright left-unit ⟩
        H • (CZ • H) ∎)

      M↑-XC : M₋₁ ↑ • XC ≈ ʰ|ʰ
      M↑-XC = begin
        M₋₁ ↑ • ((H ↑) ^ 3 • (CZ • H ↑))      ≈⟨ cleft sym H↑²≈M↑ ⟩
        (H ↑) ^ 2 • ((H ↑) ^ 3 • (CZ • H ↑))  ≈⟨ by-assoc auto ⟩
        ((H ↑) ^ 4 • H ↑) • (CZ • H ↑)        ≈⟨ cleft cleft lemma-order-H↑ ⟩
        (ε • H ↑) • (CZ • H ↑)                ≈⟨ cleft left-unit ⟩
        H ↑ • (CZ • H ↑) ∎

      ʰ|ʰ-XC' : ʰ|ʰ ≈ XC' • M₋₁ ↑
      ʰ|ʰ-XC' = sym (begin
        (H ↑ • (CZ • (H ↑) ^ 3)) • M₋₁ ↑     ≈⟨ cright sym H↑²≈M↑ ⟩
        (H ↑ • (CZ • (H ↑) ^ 3)) • (H ↑) ^ 2 ≈⟨ by-assoc auto ⟩
        H ↑ • (CZ • ((H ↑) ^ 4 • H ↑))       ≈⟨ cright cright cleft lemma-order-H↑ ⟩
        H ↑ • (CZ • (ε • H ↑))               ≈⟨ cright cright left-unit ⟩
        H ↑ • (CZ • H ↑) ∎)

      M-M : M₋₁ • M₋₁ ≈ ε
      M-M = One-Wire.lemma-M₋₁^2 (₁₊ n)

      M-M↑ : M₋₁ • M₋₁ ↑ ≈ M₋₁ ↑ • M₋₁
      M-M↑ = begin
        M₋₁ • M₋₁ ↑      ≈⟨ cleft sym order-H ⟩
        H ^ 2 • M₋₁ ↑    ≈⟨ lemma-comm-Hᵏ-w↑ 2 M₋₁ ⟩
        M₋₁ ↑ • H ^ 2    ≈⟨ cright order-H ⟩
        M₋₁ ↑ • M₋₁ ∎

      -- The swap with the multiplier by −1 on wire 0 brought to the
      -- front: the half-swaps split as M₋₁ • CX, M₋₁ ↑ • XC and CX' • M₋₁,
      -- and the wire-1 multiplier then crosses XC and CX' rightwards.
      Ex-M-front : Ex ≈ M₋₁ • (CX • (XC' • (CX • (M₋₁ ↑ • M₋₁))))
      Ex-M-front = begin
        Ex
          ≈⟨ lemma-Ex-hhh ⟩
        ₕ|ₕ • (ʰ|ʰ • ₕ|ₕ)
          ≈⟨ cong (sym lemma-ₕ|ₕ-CX) (cong (sym M↑-XC) ₕ|ₕ-CX') ⟩
        (M₋₁ • CX) • ((M₋₁ ↑ • XC) • (CX' • M₋₁))
          ≈⟨ by-passoc ((□ • □) • ((□ • □) • (□ • □)))
                       (□ • (□ • ((□ • □) • (□ • □)))) auto ⟩
        M₋₁ • (CX • ((M₋₁ ↑ • XC) • (CX' • M₋₁)))
          ≈⟨ cright cright cleft (trans M↑-XC ʰ|ʰ-XC') ⟩
        M₋₁ • (CX • ((XC' • M₋₁ ↑) • (CX' • M₋₁)))
          ≈⟨ cright cright by-passoc ((□ • □) • (□ • □)) (□ • ((□ • □) • □)) auto ⟩
        M₋₁ • (CX • (XC' • ((M₋₁ ↑ • CX') • M₋₁)))
          ≈⟨ cright cright cright cleft Derive.mu-CX⁻ ⟩
        M₋₁ • (CX • (XC' • ((CX • M₋₁ ↑) • M₋₁)))
          ≈⟨ cright cright cright assoc ⟩
        M₋₁ • (CX • (XC' • (CX • (M₋₁ ↑ • M₋₁)))) ∎

    lemma-Ex-CX-XC : Ex ≈ CX • (XC' • (CX • M₋₁))
    lemma-Ex-CX-XC = •-cancelʳ {h = M₋₁ ↑} (begin
      Ex • M₋₁ ↑
        ≈⟨ lemma-Ex-M↑ -'₁ ⟩
      M₋₁ • Ex
        ≈⟨ cright Ex-M-front ⟩
      M₋₁ • (M₋₁ • (CX • (XC' • (CX • (M₋₁ ↑ • M₋₁)))))
        ≈⟨ sym assoc ⟩
      (M₋₁ • M₋₁) • (CX • (XC' • (CX • (M₋₁ ↑ • M₋₁))))
        ≈⟨ cleft M-M ⟩
      ε • (CX • (XC' • (CX • (M₋₁ ↑ • M₋₁))))
        ≈⟨ left-unit ⟩
      CX • (XC' • (CX • (M₋₁ ↑ • M₋₁)))
        ≈⟨ cright cright cright sym M-M↑ ⟩
      CX • (XC' • (CX • (M₋₁ • M₋₁ ↑)))
        ≈⟨ by-passoc (□ • (□ • (□ • (□ • □)))) ((□ • (□ • (□ • □))) • □) auto ⟩
      (CX • (XC' • (CX • M₋₁))) • M₋₁ ↑ ∎)


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

    open PB (Γ (₂₊ n))
    open PP (Γ (₂₊ n))
    open SR word-setoid
    open Ex-Conjugation n

    lemma-comm-CZ-S↓ : CZ • S ↓ ≈ S ↓ • CZ
    lemma-comm-CZ-S↓ = lemma-comm-CZ-S

    lemma-semi-M↓CZ : Mg ↓ • CZ ≈ CZ^ g • Mg ↓
    lemma-semi-M↓CZ = lemma-semi-Mg-CZ

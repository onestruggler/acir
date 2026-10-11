{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- Group-likeness of any relation with the Paper-V1 order rules, and
-- powers modulo p.
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


module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.GroupLike
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

-- The words only, as in OneWire.
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen

open Clifford-Relations
  using ( Z ; X ; Z⁻¹ ; X⁻¹ ; Z^ ; X^ ; R ; R^ ; SHS' ; SHS ; M ; XM
        ; XM≡M⁻¹ ; M₁ ; M₋₁ ; XM₋₁ ; XM₋₁≡M₋₁ ; XMg ; XMg^ )

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.OneWire p-3 p-prime g* g-gen

------------------------------------------------------------------------
-- Group-likeness
--
-- Every generator has a left inverse, from the three order rules.  The
-- same construction as Simplified-V1.Lemmas.Clifford-GroupLike, and for
-- the same reason: the rules it uses are shared.  Iso.agda gets its
-- witness by transporting V1's along g-well-defined, which is fine there
-- but unusable for the lemma layer — XZ's chains need right-cancellation,
-- and deriving it from the transported witness would be circular.
--
-- Unlike the one-wire modules this one needs the whole family of
-- relations, one per width: a shifted generator takes its inverse from
-- the width below, and the shift has to carry the equation up.  So it
-- takes the family Γ; the four one-wire rules at every width, which is
-- what One-Wire.lemma-order-H takes (H ^ 4 ≈ ε needs M-power as well as
-- order-H); order-CZ; and congruence under the shift, which a
-- Circuit.Base.Lift-Relation provides as lemma-cong↑.

module Paper-GroupLike
  (Γ : (n : ℕ) → WRel (Gen n))
  (order-S     : ∀ {n} → let open PB (Γ (₁₊ n)) in S ^ p ≈ ε)
  (order-H     : ∀ {n} → let open PB (Γ (₁₊ n)) in H ^ 2 ≈ XM₋₁)
  (M-power     : ∀ {n} → let open PB (Γ (₁₊ n)) in ∀ k → XMg^ k ≈ XM (g^ k))
  (comm-HHSHHS : ∀ {n} → let open PB (Γ (₁₊ n)) in
                 H • H • S • H • H • S ≈ S • H • H • S • H • H)
  (order-CZ    : ∀ {n} → let open PB (Γ (₂₊ n)) in CZ ^ p ≈ ε)
  (cong↑       : ∀ {n} (w v : Word (Gen n)) →
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
      H ^ 4     ≈⟨ One-Wire.lemma-order-H n (Γ (₁₊ n))
                     order-S order-H M-power comm-HHSHHS ⟩
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
      S ^ p             ≈⟨ order-S ⟩
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
  ... | ig , prf = (ig ↑) , cong↑ (ig • [ g ]ʷ) ε prf

------------------------------------------------------------------------
-- Word lemmas at an arbitrary relation
--
-- These mention no rule at all, so they are stated once for any Γ.  The
-- two induction lemmas are copies of Syntactics.Lemmas-Clifford's, which
-- are stated over Paper-V1's relation and so cannot serve another.

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

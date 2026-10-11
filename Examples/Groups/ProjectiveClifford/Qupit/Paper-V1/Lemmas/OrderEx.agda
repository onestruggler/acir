{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- order-Ex follows from the other two-wire rules.
--
-- Paper-V1 states Ex ^ 2 = ε as an axiom.  This module derives it, at
-- every width, for every odd prime p and every primitive root g, over
-- any relation family that has the four one-wire rules (order-S,
-- order-H, M-power, comm-HHSHHS) and the two-wire rules order-CZ,
-- comm-CZ-S↑, semi-M↑CZ, semi-Ex-S↑, semi-Ex-H↑ and blake-c12, together
-- with the structural ones (a gate at the bottom passes anything shifted
-- up, and equations lift under _↑).  Neither semi-MR nor any three-wire
-- rule is used.  Reduced instantiates it at the rule set without
-- order-Ex.
--
-- The argument, uniform in p (p = 3 included) and in g.  Write c = CZ,
-- m₀ = H • H, m₁ = m₀ ↑, A = H • H ↑ and R = S • Z ^ ½.
-- Ex is c • A three times over, and the key object is
--
--     D = m₀ • c • m₀ • c                          ( = (M₋₁ • CZ) ²).
--
--   F-a  m₁ • c ≈ c⁻¹ • m₁           semi-M↑CZ at -1, via M-power
--   F-b  Ex ≈ ₕ|ₕ • ʰ|ʰ • ₕ|ₕ          semi-Ex-H↑
--   F-c  Ex • u ↑ ≈ u • Ex           semi-Ex-S↑, semi-Ex-H↑, for u ∈ ⟨H,S⟩
--   F-d  c • S ≈ S • c, c • Z ≈ Z • c, read off F-c through
--        (c • A) • Ex ≈ Ex • (c • A), which is associativity
--   F-e  XC • R ↑ • XC⁻¹ ≈ CX • R • CX⁻¹     F-c a second time, with F-b
--   D1   D commutes with S           F-d
--   D2   D commutes with H           blake-c12
--   D4–6 D commutes with T ↑ = H⁻¹ ↑ • R ↑ • H ↑, from two readings
--        of Ex • R ↑ • Ex⁻¹ ≈ R: F-c directly, and through
--        Ex • A ≈ W • D⁻¹ with W = c • A • c • A⁻¹ • c, using F-e and D2
--   D7   so D commutes with H ↑ = T ↑ • R ↑ • T ↑, hence with m₁, which
--        inverts it (F-a): D • D ≈ ε.  With D ^ p ≈ ε, D ≈ ε.
--   D8   m₀ • c • m₀ ≈ c⁻¹, so ₕ|ₕ • ₕ|ₕ ≈ ε
--   D9   Ex • Ex ≈ ₕ|ₕ • ʰ|ʰ • ₕ|ₕ • ₕ|ₕ • ʰ|ʰ • ₕ|ₕ ≈ ε
--
-- Every step is a conjugation equation a • u ≈ u' • a, composed by the
-- small calculus in Conjugation below, so no inverse word is ever
-- written for the long two-wire words.  The steps F-e to D7 mention R
-- only through six of its properties, so they are stated over an
-- abstract ρ (Two-Wire.Core) and instantiated at R once: R unfolds to a
-- Pauli power at the Bézout witness ½, and keeping it abstract there
-- keeps ½ out of those conversion checks.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_,_ ; proj₁ ; ∃)
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


module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.OrderEx
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
  using (Z ; Z⁻¹ ; R ; R^ ; SHS' ; M ; XM ; M₋₁ ; XM₋₁ ; XMg ; XMg^)
-- _↑ commuting with a power; relation-free, so Paper-V1's serves.
open Lemmas-Clifford using (lemma-↑^)

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.OneWire
  p-3 p-prime g* g-gen as OWm
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.GroupLike
  p-3 p-prime g* g-gen as GLm
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.XZ
  p-3 p-prime g* g-gen as XZm
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.SemiMR
  p-3 p-prime g* g-gen as SMm
import Examples.Groups.ProjectiveClifford.Qupit.Shared.PauliBase
  p-3 p-prime g* g-gen as Shared

------------------------------------------------------------------------
-- Conjugation equations
--
-- Conj a u u' says that conjugating by a carries u to u', in the form
-- a • u ≈ u' • a, which needs no inverse word.  They compose (conj-∘),
-- respect products and powers of what is carried (conj-•, conj-^), and
-- cancel (conj-cancelʳ, conj-cancelˡ, conj-unique), and that is all the
-- group theory the derivation uses.

module Conjugation {G : Set} (Δ : WRel G) (gl : Grouplike Δ) where

  open PB Δ hiding (_===_)
  open PP Δ
  open SR word-setoid
  open Pattern-Assoc
  open Group-Lemmas Δ gl using (•-cancelˡ ; •-cancelʳ)

  Conj : Word G → Word G → Word G → Set
  Conj a u u' = a • u ≈ u' • a

  -- First a, then b.
  conj-∘ : ∀ {a b u u' u''} → Conj a u u' → Conj b u' u'' → Conj (b • a) u u''
  conj-∘ {a} {b} {u} {u'} {u''} e f = begin
    (b • a) • u    ≈⟨ assoc ⟩
    b • (a • u)    ≈⟨ cright e ⟩
    b • (u' • a)   ≈⟨ sym assoc ⟩
    (b • u') • a   ≈⟨ cleft f ⟩
    (u'' • b) • a  ≈⟨ assoc ⟩
    u'' • (b • a) ∎

  conj-• : ∀ {a u u' v v'} → Conj a u u' → Conj a v v' → Conj a (u • v) (u' • v')
  conj-• {a} {u} {u'} {v} {v'} e f = begin
    a • (u • v)    ≈⟨ sym assoc ⟩
    (a • u) • v    ≈⟨ cleft e ⟩
    (u' • a) • v   ≈⟨ assoc ⟩
    u' • (a • v)   ≈⟨ cright f ⟩
    u' • (v' • a)  ≈⟨ sym assoc ⟩
    (u' • v') • a ∎

  conj-ε : ∀ {a} → Conj a ε ε
  conj-ε = trans right-unit (sym left-unit)

  conj-^ : ∀ {a u u'} → Conj a u u' → ∀ k → Conj a (u ^ k) (u' ^ k)
  conj-^ e ₀ = conj-ε
  conj-^ e ₁ = e
  conj-^ e (₂₊ k) = conj-• e (conj-^ e (₁₊ k))

  -- A power of something that fixes u fixes u.
  conj-^ˡ : ∀ {a u} → Conj a u u → ∀ k → Conj (a ^ k) u u
  conj-^ˡ e ₀ = trans left-unit (sym right-unit)
  conj-^ˡ e ₁ = e
  conj-^ˡ e (₂₊ k) = conj-∘ (conj-^ˡ e (₁₊ k)) e

  conj-congˡ : ∀ {a a' u u'} → a ≈ a' → Conj a u u' → Conj a' u u'
  conj-congˡ eq e = trans (cleft sym eq) (trans e (cright eq))

  conj-cong : ∀ {a u u' v v'} → u ≈ v → u' ≈ v' → Conj a u u' → Conj a v v'
  conj-cong eu eu' e = trans (cright sym eu) (trans e (cleft eu'))

  conj-unique : ∀ {a u u' u''} → Conj a u u' → Conj a u u'' → u' ≈ u''
  conj-unique e f = •-cancelʳ (trans (sym e) f)

  -- A commutation read the other way round.
  comm-sym : ∀ {a u} → Conj a u u → Conj u a a
  comm-sym e = sym e

  -- Inverting the conjugator …
  conj-inv : ∀ {a b u u'} → b • a ≈ ε → a • b ≈ ε → Conj a u u' → Conj b u' u
  conj-inv {a} {b} {u} {u'} ba ab e = begin
    b • u'               ≈⟨ sym right-unit ⟩
    (b • u') • ε         ≈⟨ cright sym ab ⟩
    (b • u') • (a • b)   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) auto ⟩
    b • (u' • a) • b     ≈⟨ cright cleft sym e ⟩
    b • (a • u) • b      ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) auto ⟩
    (b • a) • (u • b)    ≈⟨ cleft ba ⟩
    ε • (u • b)          ≈⟨ left-unit ⟩
    u • b ∎

  -- … and the word it carries.
  conj-inv-u : ∀ {a u u' v v'} → u • v ≈ ε → v' • u' ≈ ε → Conj a u u' → Conj a v v'
  conj-inv-u {a} {u} {u'} {v} {v'} uv vu e = begin
    a • v                  ≈⟨ sym left-unit ⟩
    ε • (a • v)            ≈⟨ cleft sym vu ⟩
    (v' • u') • (a • v)    ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) auto ⟩
    v' • (u' • a) • v      ≈⟨ cright cleft sym e ⟩
    v' • (a • u) • v       ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) auto ⟩
    (v' • a) • (u • v)     ≈⟨ cright uv ⟩
    (v' • a) • ε           ≈⟨ right-unit ⟩
    v' • a ∎

  -- The literal conjugate, read from either end.
  conj-lit : ∀ {a a' u} → a' • a ≈ ε → Conj a u (a • (u • a'))
  conj-lit {a} {a'} {u} e = begin
    a • u                  ≈⟨ sym right-unit ⟩
    (a • u) • ε            ≈⟨ cright sym e ⟩
    (a • u) • (a' • a)     ≈⟨ by-passoc ((□ • □) • (□ • □)) ((□ • (□ • □)) • □) auto ⟩
    (a • (u • a')) • a ∎

  conj-lit' : ∀ {a a' u} → a • a' ≈ ε → Conj a (a' • (u • a)) u
  conj-lit' {a} {a'} {u} e = begin
    a • (a' • (u • a))     ≈⟨ sym assoc ⟩
    (a • a') • (u • a)     ≈⟨ cleft e ⟩
    ε • (u • a)            ≈⟨ left-unit ⟩
    u • a ∎

  -- Cancelling a factor of a composite conjugator whose action is known.
  conj-cancelʳ : ∀ {a b u u' u''} → Conj (b • a) u u'' → Conj a u u' → Conj b u' u''
  conj-cancelʳ {a} {b} {u} {u'} {u''} e f = •-cancelʳ {h = a} (begin
    (b • u') • a     ≈⟨ assoc ⟩
    b • (u' • a)     ≈⟨ cright sym f ⟩
    b • (a • u)      ≈⟨ sym assoc ⟩
    (b • a) • u      ≈⟨ e ⟩
    u'' • (b • a)    ≈⟨ sym assoc ⟩
    (u'' • b) • a ∎)

  conj-cancelˡ : ∀ {a b u u' u''} → Conj (b • a) u u'' → Conj b u' u'' → Conj a u u'
  conj-cancelˡ {a} {b} {u} {u'} {u''} e f = •-cancelˡ {g = b} (begin
    b • (a • u)      ≈⟨ sym assoc ⟩
    (b • a) • u      ≈⟨ e ⟩
    u'' • (b • a)    ≈⟨ sym assoc ⟩
    (u'' • b) • a    ≈⟨ cleft sym f ⟩
    (b • u') • a     ≈⟨ assoc ⟩
    b • (u' • a) ∎)

  -- Inverse pairs.
  cancel-• : ∀ {a a' w} → a' • a ≈ ε → a' • (a • w) ≈ w
  cancel-• e = trans (sym assoc) (trans (cleft e) left-unit)

  tele : ∀ {w x x' w'} → x • x' ≈ ε → w • w' ≈ ε → (w • x) • (x' • w') ≈ ε
  tele {w} {x} {x'} {w'} xx' ww' = begin
    (w • x) • (x' • w')   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • ((□ • □) • □)) auto ⟩
    w • ((x • x') • w')   ≈⟨ cright trans (cleft xx') left-unit ⟩
    w • w'                ≈⟨ ww' ⟩
    ε ∎

  -- Conjugates of an inverse pair are an inverse pair.
  sandwich-inv : ∀ {a a' u u'} → a • a' ≈ ε → a' • a ≈ ε → u • u' ≈ ε →
                 (a' • (u • a)) • (a' • (u' • a)) ≈ ε
  sandwich-inv {a} {a'} {u} {u'} aa' a'a uu' = begin
    (a' • (u • a)) • (a' • (u' • a))
      ≈⟨ by-passoc ((□ • (□ • □)) • (□ • (□ • □))) (□ • (□ • ((□ • □) • (□ • □)))) auto ⟩
    a' • (u • ((a • a') • (u' • a)))
      ≈⟨ cright cright trans (cleft aa') left-unit ⟩
    a' • (u • (u' • a))
      ≈⟨ cright cancel-• uu' ⟩
    a' • a
      ≈⟨ a'a ⟩
    ε ∎

------------------------------------------------------------------------
-- One-wire facts the two-wire argument uses
--
-- Over the same parameters as One-Wire-Group, so that Two-Wire can
-- instantiate it twice: at the bottom wire as it stands, and one wire
-- down, to be lifted to the top wire.

module One-Wire-Extra
  (n : ℕ)
  (Γ : WRel (Gen (₁₊ n)))
  (order-S     : let open PB Γ in S ^ p ≈ ε)
  (order-H     : let open PB Γ in H ^ 2 ≈ XM₋₁)
  (M-power     : let open PB Γ in ∀ k → XMg^ k ≈ XM (g^ k))
  (comm-HHSHHS : let open PB Γ in
                 H • H • S • H • H • S ≈ S • H • H • S • H • H)
  (gl          : Grouplike Γ)
  where

  open PB Γ hiding (_===_)
  open PP Γ
  open SR word-setoid
  open Pattern-Assoc
  open Conjugation Γ gl

  private
    module O = OWm.One-Wire n Γ order-S order-H M-power comm-HHSHHS
    module G = XZm.One-Wire-Group n Γ order-S order-H M-power comm-HHSHHS gl
    module Sm = SMm.SemiMR n Γ order-S order-H M-power comm-HHSHHS gl

  -- H⁻¹ = H ^ 3 really is the inverse of H.
  H⁴ : H ^ 4 ≈ ε
  H⁴ = O.lemma-order-H

  H-H⁻¹ : H • H⁻¹ ≈ ε
  H-H⁻¹ = H⁴

  H⁻¹-H : H⁻¹ • H ≈ ε
  H⁻¹-H = trans (by-assoc auto) H⁴

  HH-HH : HH • HH ≈ ε
  HH-HH = trans (by-assoc auto) H⁴

  H⁻¹H⁻¹ : H⁻¹ • H⁻¹ ≈ HH
  H⁻¹H⁻¹ = begin
    H⁻¹ • H⁻¹       ≈⟨ by-assoc auto ⟩
    H ^ 4 • HH      ≈⟨ cleft H⁴ ⟩
    ε • HH          ≈⟨ left-unit ⟩
    HH ∎

  HH-H⁻¹ : HH • H⁻¹ ≈ H
  HH-H⁻¹ = begin
    HH • H⁻¹        ≈⟨ by-assoc auto ⟩
    H ^ 4 • H       ≈⟨ cleft H⁴ ⟩
    ε • H           ≈⟨ left-unit ⟩
    H ∎

  HH-H : Conj HH H H
  HH-H = by-assoc auto

  HH-H⁻¹' : Conj HH H⁻¹ H⁻¹
  HH-H⁻¹' = by-assoc auto

  S-S⁻¹ : S • S⁻¹ ≈ ε
  S-S⁻¹ = order-S

  S⁻¹-S : S⁻¹ • S ≈ ε
  S⁻¹-S = trans (comm⇒pow-comm p-1 1 refl) order-S

  -- Conjugating by H, read backwards.
  conj-H-lit : ∀ {u} → Conj H (H⁻¹ • (u • H)) u
  conj-H-lit = conj-lit' H-H⁻¹

  -- H⁻¹ carries the H-conjugate of u to its m-conjugate.
  H⁻¹-conj : ∀ u → Conj H⁻¹ (H⁻¹ • (u • H)) (HH • (u • HH))
  H⁻¹-conj u = begin
    H⁻¹ • (H⁻¹ • (u • H))     ≈⟨ sym assoc ⟩
    (H⁻¹ • H⁻¹) • (u • H)     ≈⟨ cleft H⁻¹H⁻¹ ⟩
    HH • (u • H)              ≈⟨ cright cright sym HH-H⁻¹ ⟩
    HH • (u • (HH • H⁻¹))     ≈⟨ by-passoc (□ • (□ • (□ • □))) ((□ • (□ • □)) • □) auto ⟩
    (HH • (u • HH)) • H⁻¹ ∎

  -- Conjugating by m = H • H sends S to Z • S (the definition of Z) and
  -- Z to Z⁻¹, so it sends Z • S back to S.
  HH-S : Conj HH S (Z • S)
  HH-S = begin
    HH • S                  ≈⟨ sym right-unit ⟩
    (HH • S) • ε            ≈⟨ cright sym HH-HH ⟩
    (HH • S) • (HH • HH)    ≈⟨ by-passoc ((□ • □) • (□ • □)) ((□ • (□ • □)) • □) auto ⟩
    (HH • (S • HH)) • HH    ≈⟨ cleft Sm.HH-S-HH ⟩
    (Z • S) • HH ∎

  HH-ZS : Conj HH (Z • S) S
  HH-ZS = conj-cong refl collapse (conj-• HH-Z HH-S)
    where
    HH-Z : Conj HH Z Z⁻¹
    HH-Z = trans G.lemma-HH-Z (cleft refl' (Eq.cong (Z ^_) lemma-toℕ-1ₚ))

    collapse : Z⁻¹ • (Z • S) ≈ S
    collapse = cancel-• G.aux-Z⁻¹-Z

  -- m commutes with R (SemiMR's L0c).
  HH-R : Conj HH R R
  HH-R = Sm.HH-R

  -- (R • H) ³ is the multiplier at 1 in Paper-V0's spelling, which is ε.
  RH³ : R • (H • (R • (H • (R • H)))) ≈ ε
  RH³ = begin
    R • (H • (R • (H • (R • H))))
      ≡⟨ Eq.cong (λ z → R • (H • (R^ z • (H • (R • H))))) (Eq.sym O.aux-1⁻¹) ⟩
    R^ ₁ • (H • (R^ (((₁ , λ ()) ⁻¹) .proj₁) • (H • (R^ ₁ • H))))
      ≈⟨ G.Bridge.bridge (₁ , λ ()) ⟩
    M (₁ , λ ())
      ≈⟨ O.lemma-M1 ⟩
    ε ∎

  -- The SL₂ identity H = T • R • T with T = H⁻¹ • R • H: m is central in
  -- what H and R generate, so T • R • T is H⁻¹ • m • (R • H) ³ = H.
  SL₂ : H ≈ (H⁻¹ • (R • H)) • (R • (H⁻¹ • (R • H)))
  SL₂ = sym (begin
    (H⁻¹ • (R • H)) • (R • (H⁻¹ • (R • H)))
      ≈⟨ by-passoc ((□ • (□ • □)) • (□ • (□ • (□ • □))))
                   (□ • ((□ • (□ • □)) • (□ • (□ • □)))) auto ⟩
    H⁻¹ • ((R • (H • R)) • (H⁻¹ • (R • H)))
      ≈⟨ cright cright cleft by-assoc auto ⟩
    H⁻¹ • ((R • (H • R)) • ((HH • H) • (R • H)))
      ≈⟨ cright by-passoc ((□ • (□ • □)) • ((□ • □) • (□ • □)))
                          (((□ • (□ • □)) • □) • (□ • (□ • □))) auto ⟩
    H⁻¹ • (((R • (H • R)) • HH) • (H • (R • H)))
      ≈⟨ cright cleft sym (conj-• HH-R (conj-• HH-H HH-R)) ⟩
    H⁻¹ • ((HH • (R • (H • R))) • (H • (R • H)))
      ≈⟨ by-passoc (□ • ((□ • (□ • (□ • □))) • (□ • (□ • □))))
                   ((□ • □) • (□ • (□ • (□ • (□ • (□ • □)))))) auto ⟩
    (H⁻¹ • HH) • (R • (H • (R • (H • (R • H)))))
      ≈⟨ cright RH³ ⟩
    (H⁻¹ • HH) • ε
      ≈⟨ right-unit ⟩
    H⁻¹ • HH
      ≈⟨ trans (by-assoc auto) HH-H⁻¹ ⟩
    H ∎)

  -- (S • H) ³ = ε solved for H.
  SH-inv : H ≈ S⁻¹ • (H⁻¹ • (S⁻¹ • (H⁻¹ • S⁻¹)))
  SH-inv = sym (begin
    S⁻¹ • (H⁻¹ • (S⁻¹ • (H⁻¹ • S⁻¹)))
      ≈⟨ sym right-unit ⟩
    (S⁻¹ • (H⁻¹ • (S⁻¹ • (H⁻¹ • S⁻¹)))) • ε
      ≈⟨ cright sym SH³ ⟩
    (S⁻¹ • (H⁻¹ • (S⁻¹ • (H⁻¹ • S⁻¹)))) • (S • (H • (S • (H • (S • H)))))
      ≈⟨ by-passoc (□ ^ 5 • □ ^ 6) (□ ^ 11) auto ⟩
    S⁻¹ • (H⁻¹ • (S⁻¹ • (H⁻¹ • (S⁻¹ • (S • (H • (S • (H • (S • H)))))))))
      ≈⟨ cright cright cright cright cancel-• S⁻¹-S ⟩
    S⁻¹ • (H⁻¹ • (S⁻¹ • (H⁻¹ • (H • (S • (H • (S • H)))))))
      ≈⟨ cright cright cright cancel-• H⁻¹-H ⟩
    S⁻¹ • (H⁻¹ • (S⁻¹ • (S • (H • (S • H)))))
      ≈⟨ cright cright cancel-• S⁻¹-S ⟩
    S⁻¹ • (H⁻¹ • (H • (S • H)))
      ≈⟨ cright cancel-• H⁻¹-H ⟩
    S⁻¹ • (S • H)
      ≈⟨ cancel-• S⁻¹-S ⟩
    H ∎)
    where
    SH³ : S • (H • (S • (H • (S • H)))) ≈ ε
    SH³ = trans (by-assoc auto) O.lemma-order-SH

------------------------------------------------------------------------
-- The derivation
--
-- The family Γ and the rules the derivation uses, each stated exactly as
-- Paper-V1's axiom, as an equation in Γ.  comm₁ and cong↑ are the
-- structural rules every Circuit.Base.Lift-Relation provides.

module Order-Ex
  (Γ : (n : ℕ) → WRel (Gen n))
  (order-S     : ∀ {n} → let open PB (Γ (₁₊ n)) in S ^ p ≈ ε)
  (order-H     : ∀ {n} → let open PB (Γ (₁₊ n)) in H ^ 2 ≈ XM₋₁)
  (M-power     : ∀ {n} → let open PB (Γ (₁₊ n)) in ∀ k → XMg^ k ≈ XM (g^ k))
  (comm-HHSHHS : ∀ {n} → let open PB (Γ (₁₊ n)) in
                 H • H • S • H • H • S ≈ S • H • H • S • H • H)
  (order-CZ    : ∀ {n} → let open PB (Γ (₂₊ n)) in CZ ^ p ≈ ε)
  (comm-CZ-S↑  : ∀ {n} → let open PB (Γ (₂₊ n)) in CZ • S ↑ ≈ S ↑ • CZ)
  (semi-M↑CZ   : ∀ {n} → let open PB (Γ (₂₊ n)) in XMg ↑ • CZ^ g ≈ CZ • XMg ↑)
  (semi-Ex-S↑  : ∀ {n} → let open PB (Γ (₂₊ n)) in Ex • S ↑ ≈ S ↓ • Ex)
  (semi-Ex-H↑  : ∀ {n} → let open PB (Γ (₂₊ n)) in Ex • H ↑ ≈ H ↓ • Ex)
  (blake-c12   : ∀ {n} → let open PB (Γ (₂₊ n)) in
                 (S ^ p-1) ↑ • (S ^ p-1) ↓ • CX ^ p-1 • S ↓ • CX ≈ CZ)
  (comm₁       : ∀ {n} (h : SympGate 1) (x : Gen (₁₊ n)) →
                 let open PB (Γ (₂₊ n)) in
                 [ x ↥ ]ʷ • [ gate₁ h ]ʷ ≈ [ gate₁ h ]ʷ • [ x ↥ ]ʷ)
  (cong↑       : ∀ {n} (w v : Word (Gen n)) →
                 PB._≈_ (Γ n) w v → PB._≈_ (Γ (₁₊ n)) (w ↑) (v ↑))
  where

  -- Group-likeness, from the order rules, as for Paper-V1.
  gl : ∀ {n} → Grouplike (Γ n)
  gl = GLm.Paper-GroupLike.grouplike Γ
         order-S order-H M-power comm-HHSHHS order-CZ cong↑

  module Two-Wire (n : ℕ) where

    open PB (Γ (₂₊ n)) hiding (_===_)
    open PP (Γ (₂₊ n))
    open SR word-setoid
    open Pattern-Assoc
    open Group-Lemmas (Γ (₂₊ n)) (gl {₂₊ n}) using (•-cancelˡ ; •-cancelʳ)
    open Conjugation (Γ (₂₊ n)) (gl {₂₊ n})

    private
      -- The bottom wire, as it stands …
      module E₀ = One-Wire-Extra (₁₊ n) (Γ (₂₊ n))
                    order-S order-H M-power comm-HHSHHS (gl {₂₊ n})
      module O₀ = OWm.One-Wire (₁₊ n) (Γ (₂₊ n))
                    order-S order-H M-power comm-HHSHHS
      -- … and one wire down, to be lifted to the top wire.
      module E₁ = One-Wire-Extra n (Γ (₁₊ n))
                    order-S order-H M-power comm-HHSHHS (gl {₁₊ n})
      module O₁ = OWm.One-Wire n (Γ (₁₊ n))
                    order-S order-H M-power comm-HHSHHS

      lift↑ : ∀ {w v : Word (Gen (₁₊ n))} → PB._≈_ (Γ (₁₊ n)) w v → w ↑ ≈ v ↑
      lift↑ {w} {v} = cong↑ w v

    ----------------------------------------------------------------------
    -- The two wires commute

    ↑-gate : ∀ (h : SympGate 1) (w : Word (Gen (₁₊ n))) →
             Conj (w ↑) [ gate₁ h ]ʷ [ gate₁ h ]ʷ
    ↑-gate h [ x ]ʷ = comm₁ h x
    ↑-gate h ε = trans left-unit (sym right-unit)
    ↑-gate h (u • t) = conj-∘ (↑-gate h t) (↑-gate h u)

    ↑H : ∀ w → Conj (w ↑) H H
    ↑H = ↑-gate H-gate

    ↑S : ∀ w → Conj (w ↑) S S
    ↑S = ↑-gate S-gate

    -- Anything that fixes H and S fixes the words built from them.
    module Fix {w : Word (Gen (₂₊ n))} (wH : Conj w H H) (wS : Conj w S S) where

      wH⁻¹ : Conj w H⁻¹ H⁻¹
      wH⁻¹ = conj-^ wH 3

      wHH : Conj w HH HH
      wHH = conj-^ wH 2

      wS⁻¹ : Conj w S⁻¹ S⁻¹
      wS⁻¹ = conj-^ wS p-1

      wZ : Conj w Z Z
      wZ = conj-• wH (conj-• wH (conj-• wS (conj-• wH (conj-• wH wS⁻¹))))

      wR : Conj w R R
      wR = conj-• wS (conj-^ wZ (toℕ 1/2))

    m₁-HH : Conj (HH ↑) HH HH
    m₁-HH = conj-^ (↑H HH) 2

    ----------------------------------------------------------------------
    -- Inverse pairs

    CZ-CZ⁻¹ : CZ • CZ⁻¹ ≈ ε
    CZ-CZ⁻¹ = order-CZ

    CZ⁻¹-CZ : CZ⁻¹ • CZ ≈ ε
    CZ⁻¹-CZ = trans (comm⇒pow-comm p-1 1 refl) order-CZ

    H↑⁴ : (H ↑) ^ 4 ≈ ε
    H↑⁴ = lift↑ E₁.H⁴

    H↑-H⁻¹↑ : H ↑ • H⁻¹ ↑ ≈ ε
    H↑-H⁻¹↑ = lift↑ E₁.H-H⁻¹

    m₁m₁ : HH ↑ • HH ↑ ≈ ε
    m₁m₁ = lift↑ E₁.HH-HH

    ----------------------------------------------------------------------
    -- F-a: the multiplier by -1 on the top wire inverts CZ
    --
    -- semi-M↑CZ says XMg ↑ carries CZ ^ g to CZ; iterating, XMg ↑ ^ j
    -- carries CZ ^ (g ^ j · a) to CZ ^ a.  At the j with g ^ j = -1 and
    -- a = -1 that is m₁ • CZ ≈ CZ⁻¹ • m₁, since XMg ^ j is XM₋₁ (M-power)
    -- and H ^ 2 is XM₋₁ (order-H).

    private
      Mg↑ : Word (Gen (₂₊ n))
      Mg↑ = XMg ↑

      k₋ : ℤ ₚ
      k₋ = inject₁ (log -'₁)

      e₋ : g ^′ toℕ k₋ ≡ - ₁
      e₋ = lemma-log-inject -'₁

      step : ∀ a → Mg↑ • CZ^ (g * a) ≈ CZ^ a • Mg↑
      step a = trans (cright sym aux) (GLm.lemma-Induction semi-M↑CZ (toℕ a))
        where
        aux : (CZ^ g) ^ toℕ a ≈ CZ^ (g * a)
        aux = begin
          (CZ ^ toℕ g) ^ toℕ a                ≈⟨ ^^ CZ (toℕ g) (toℕ a) ⟩
          CZ ^ (toℕ g Nat.* toℕ a)            ≈⟨ GLm.lemma-pow-mod order-CZ (toℕ g Nat.* toℕ a) ⟩
          CZ ^ ((toℕ g Nat.* toℕ a) Nat.% p)  ≡⟨ Eq.cong (CZ ^_) (lemma-toℕ-% g a) ⟩
          CZ ^ toℕ (g * a) ∎

      iter : ∀ j a → Mg↑ ^ j • CZ^ ((g ^′ j) * a) ≈ CZ^ a • Mg↑ ^ j
      iter ₀ a = begin
        ε • CZ^ (₁ * a)   ≈⟨ left-unit ⟩
        CZ^ (₁ * a)       ≡⟨ Eq.cong (λ z → CZ^ z) (*-identityˡ a) ⟩
        CZ^ a             ≈⟨ sym right-unit ⟩
        CZ^ a • ε ∎
      iter ₁ a = begin
        Mg↑ • CZ^ ((g * ₁) * a)  ≡⟨ Eq.cong (λ z → Mg↑ • CZ^ (z * a)) (*-identityʳ g) ⟩
        Mg↑ • CZ^ (g * a)        ≈⟨ step a ⟩
        CZ^ a • Mg↑ ∎
      iter (₂₊ j) a = begin
        (Mg↑ • Mg↑ ^ ₁₊ j) • CZ^ ((g * (g ^′ ₁₊ j)) * a)
          ≡⟨ Eq.cong (λ z → (Mg↑ • Mg↑ ^ ₁₊ j) • CZ^ z) ring ⟩
        (Mg↑ • Mg↑ ^ ₁₊ j) • CZ^ ((g ^′ ₁₊ j) * (g * a))
          ≈⟨ assoc ⟩
        Mg↑ • (Mg↑ ^ ₁₊ j • CZ^ ((g ^′ ₁₊ j) * (g * a)))
          ≈⟨ cright iter (₁₊ j) (g * a) ⟩
        Mg↑ • (CZ^ (g * a) • Mg↑ ^ ₁₊ j)
          ≈⟨ sym assoc ⟩
        (Mg↑ • CZ^ (g * a)) • Mg↑ ^ ₁₊ j
          ≈⟨ cleft step a ⟩
        (CZ^ a • Mg↑) • Mg↑ ^ ₁₊ j
          ≈⟨ assoc ⟩
        CZ^ a • (Mg↑ • Mg↑ ^ ₁₊ j) ∎
        where
        ring : (g * (g ^′ ₁₊ j)) * a ≡ (g ^′ ₁₊ j) * (g * a)
        ring = Eq.trans (Eq.cong (_* a) (*-comm g (g ^′ ₁₊ j)))
                        (*-assoc (g ^′ ₁₊ j) g a)

      m≈ : Mg↑ ^ toℕ k₋ ≈ HH ↑
      m≈ = begin
        (XMg ↑) ^ toℕ k₋    ≡⟨ Eq.sym (lemma-↑^ (toℕ k₋) XMg) ⟩
        (XMg ^ toℕ k₋) ↑    ≈⟨ lift↑ (M-power k₋) ⟩
        XM (g^ k₋) ↑        ≡⟨ Eq.cong _↑ xm ⟩
        XM₋₁ ↑              ≈⟨ lift↑ (PB.sym order-H) ⟩
        HH ↑ ∎
        where
        e₋' : (g^ k₋) .proj₁ ≡ -'₁ .proj₁
        e₋' = lemma-log-inject -'₁

        -- XM y mentions y through its value and its inverse's only.
        xm : XM {n} (g^ k₋) ≡ XM₋₁
        xm = Eq.cong₂ (λ a b → SHS' {n} a b) e₋' (O₁.aux-inv≡ (g^ k₋) -'₁ e₋')

    m₁-CZ : Conj (HH ↑) CZ CZ⁻¹
    m₁-CZ = begin
      HH ↑ • CZ
        ≈⟨ cleft sym m≈ ⟩
      Mg↑ ^ toℕ k₋ • CZ
        ≡⟨ Eq.cong (λ z → Mg↑ ^ toℕ k₋ • CZ^ z) (Eq.sym one) ⟩
      Mg↑ ^ toℕ k₋ • CZ^ ((g ^′ toℕ k₋) * (- ₁))
        ≈⟨ iter (toℕ k₋) (- ₁) ⟩
      CZ^ (- ₁) • Mg↑ ^ toℕ k₋
        ≈⟨ cong (refl' (Eq.cong (CZ ^_) lemma-toℕ-1ₚ)) m≈ ⟩
      CZ⁻¹ • HH ↑ ∎
      where
      one : (g ^′ toℕ k₋) * (- ₁) ≡ ₁
      one = Eq.trans (Eq.cong (_* (- ₁)) e₋) aux-₁²

    m₁-CZ⁻¹ : Conj (HH ↑) CZ⁻¹ CZ
    m₁-CZ⁻¹ = conj-inv m₁m₁ m₁m₁ m₁-CZ

    -- The same with the multiplier spelled as Paper-V0 spells it.
    lemma-M₋₁↑-CZ : M₋₁ ↑ • CZ ≈ CZ⁻¹ • M₋₁ ↑
    lemma-M₋₁↑-CZ = conj-congˡ (lift↑ O₁.order-H') m₁-CZ

    ----------------------------------------------------------------------
    -- CZ against the top-wire S, Z and R

    S↑-CZ : Conj (S ↑) CZ CZ
    S↑-CZ = comm-sym comm-CZ-S↑

    S⁻¹↑-CZ : Conj (S⁻¹ ↑) CZ CZ
    S⁻¹↑-CZ = conj-congˡ (refl' (Eq.sym (lemma-↑^ p-1 S))) (conj-^ˡ S↑-CZ p-1)

    -- Z ↑ is m₁ • S ↑ • m₁ • S⁻¹ ↑, and m₁ inverts CZ twice.
    Z↑-CZ : Conj (Z ↑) CZ CZ
    Z↑-CZ = conj-congˡ
      (by-passoc ((□ • □) • (□ • ((□ • □) • □))) (□ • (□ • (□ • (□ • (□ • □))))) auto)
      (conj-∘ (conj-∘ (conj-∘ S⁻¹↑-CZ m₁-CZ) (conj-^ S↑-CZ p-1)) m₁-CZ⁻¹)

    R↑-CZ : Conj (R ↑) CZ CZ
    R↑-CZ = conj-∘ (conj-congˡ (refl' (Eq.sym (lemma-↑^ (toℕ 1/2) Z))) (conj-^ˡ Z↑-CZ (toℕ 1/2)))
                   S↑-CZ

    ----------------------------------------------------------------------
    -- F-c: the swap carries the top wire to the bottom one

    -- The lifted word is explicit: it cannot be read back off u ↑.
    ex-^ : ∀ (u : Word (Gen (₁₊ n))) {u'} → Conj Ex (u ↑) u' →
           ∀ k → Conj Ex ((u ^ k) ↑) (u' ^ k)
    ex-^ u e k = trans (cright refl' (lemma-↑^ k u)) (conj-^ e k)

    ex-H : Conj Ex (H ↑) H
    ex-H = semi-Ex-H↑

    ex-S : Conj Ex (S ↑) S
    ex-S = semi-Ex-S↑

    ex-H⁻¹ : Conj Ex (H⁻¹ ↑) H⁻¹
    ex-H⁻¹ = conj-^ ex-H 3

    ex-S⁻¹ : Conj Ex (S⁻¹ ↑) S⁻¹
    ex-S⁻¹ = ex-^ S ex-S p-1

    ex-Z : Conj Ex (Z ↑) Z
    ex-Z = conj-• ex-H (conj-• ex-H (conj-• ex-S (conj-• ex-H (conj-• ex-H ex-S⁻¹))))

    ex-R : Conj Ex (R ↑) R
    ex-R = conj-• ex-S (ex-^ Z ex-Z (toℕ 1/2))

    ----------------------------------------------------------------------
    -- F-d: CZ commutes with a bottom-wire u whenever it commutes with u ↑
    --
    -- Ex is (CZ • A) cubed, so CZ • A commutes with it outright; reading
    -- Ex • u ↑ ≈ u • Ex through that, with u ↑ = A • v ↑ • A⁻¹ and
    -- u = A • v • A⁻¹ for v = H⁻¹ • u • H, leaves CZ • u ≈ u • CZ.

    A Ai : Word (Gen (₂₊ n))
    A = H • H ↑
    Ai = H⁻¹ • H⁻¹ ↑

    CZA-Ex : Conj (CZ • A) Ex Ex
    CZA-Ex = by-assoc auto

    F-d : ∀ {u₁ v₁ : Word (Gen (₁₊ n))} {u v} →
          Conj Ex (v₁ ↑) v → Conj Ex (u₁ ↑) u →
          Conj A (v₁ ↑) (u₁ ↑) → Conj A v u →
          Conj CZ (u₁ ↑) (u₁ ↑) → Conj CZ u u
    F-d exv exu A↑ A₀ cu↑ =
      conj-cancelʳ (conj-congˡ (trans (sym CZA-Ex) assoc) (conj-∘ (conj-∘ A↑ cu↑) exu))
                   (conj-∘ exv A₀)

    F-d' : (u : ∀ {k} → Word (Gen (₁₊ k))) →
           Conj Ex (u ↑) u → (∀ w → Conj (w ↑) u u) → Conj CZ (u ↑) (u ↑) →
           Conj CZ u u
    F-d' u exu cross cu↑ =
      F-d {u₁ = u} {v₁ = H⁻¹ • (u • H)} {u = u} {v = H⁻¹ • (u • H)}
          (conj-• ex-H⁻¹ (conj-• exu ex-H)) exu
          (conj-∘ (lift↑ (E₁.conj-H-lit {u = u})) (comm-sym (↑H u)))
          (conj-∘ (conj-• (conj-^ (↑H H) 3) (conj-• (cross H) (↑H H)))
                  (E₀.conj-H-lit {u = u}))
          cu↑

    lemma-comm-CZ-S↓ : Conj CZ S S
    lemma-comm-CZ-S↓ = F-d' S ex-S ↑S comm-CZ-S↑

    CZ-S : Conj CZ S S
    CZ-S = lemma-comm-CZ-S↓

    CZ-Z : Conj CZ Z Z
    CZ-Z = F-d' Z ex-Z (λ w → Fix.wZ (↑H w) (↑S w)) (comm-sym Z↑-CZ)

    ----------------------------------------------------------------------
    -- F-b: three half-swaps make the swap

    half-swaps : ₕ|ₕ • ʰ|ʰ • ₕ|ₕ ≈ H • Ex • (H ↑) ^ 3
    half-swaps = begin
      ₕ|ₕ • ʰ|ʰ • ₕ|ₕ
        ≈⟨ by-assoc auto ⟩
      (H • CZ • H • H ↑ • CZ) • (H ↑ • H) • CZ • H
        ≈⟨ cright cleft ↑H H ⟩
      (H • CZ • H • H ↑ • CZ) • (H • H ↑) • CZ • H
        ≈⟨ sym right-unit ⟩
      ((H • CZ • H • H ↑ • CZ) • (H • H ↑) • CZ • H) • ε
        ≈⟨ cright sym H↑⁴ ⟩
      ((H • CZ • H • H ↑ • CZ) • (H • H ↑) • CZ • H) • (H ↑) ^ 4
        ≈⟨ by-assoc auto ⟩
      H • Ex • (H ↑) ^ 3 ∎

    lemma-Ex-hhh : Ex ≈ ₕ|ₕ • ʰ|ʰ • ₕ|ₕ
    lemma-Ex-hhh = sym (begin
      ₕ|ₕ • ʰ|ʰ • ₕ|ₕ        ≈⟨ half-swaps ⟩
      H • Ex • (H ↑) ^ 3     ≈⟨ cright conj-^ ex-H 3 ⟩
      H • H ^ 3 • Ex         ≈⟨ sym assoc ⟩
      (H • H ^ 3) • Ex       ≈⟨ cleft E₀.H⁴ ⟩
      ε • Ex                 ≈⟨ left-unit ⟩
      Ex ∎)

    ----------------------------------------------------------------------
    -- D1: D = m₀ • CZ • m₀ • CZ commutes with S

    Y Yi D Di : Word (Gen (₂₊ n))
    Y = HH • (CZ • HH)
    Yi = HH • (CZ⁻¹ • HH)
    D = HH • (CZ • (HH • CZ))
    Di = CZ⁻¹ • Yi

    D≈ : D ≈ Y • CZ
    D≈ = by-assoc auto

    Y≈ : Y ≈ D • CZ⁻¹
    Y≈ = sym (trans (cleft D≈) (trans assoc (trans (cright CZ-CZ⁻¹) right-unit)))

    D-S : Conj D S S
    D-S = conj-∘ (conj-∘ (conj-∘ CZ-S E₀.HH-S) (conj-• CZ-Z CZ-S)) E₀.HH-ZS

    ----------------------------------------------------------------------
    -- blake-c12, read as conjugations

    CXi XCi : Word (Gen (₂₊ n))
    CXi = H⁻¹ • (CZ⁻¹ • H)
    XCi = H⁻¹ ↑ • (CZ⁻¹ • H ↑)

    CX-CXi : CX • CXi ≈ ε
    CX-CXi = sandwich-inv E₀.H-H⁻¹ E₀.H⁻¹-H CZ-CZ⁻¹

    CXi-CX : CXi • CX ≈ ε
    CXi-CX = sandwich-inv E₀.H-H⁻¹ E₀.H⁻¹-H CZ⁻¹-CZ

    XC-XCi : XC • XCi ≈ ε
    XC-XCi = sandwich-inv (lift↑ E₁.H-H⁻¹) (lift↑ E₁.H⁻¹-H) CZ-CZ⁻¹

    H⁻¹-CZ : Conj H⁻¹ CZ CX
    H⁻¹-CZ = conj-lit E₀.H-H⁻¹

    H⁻¹-CZ⁻¹ : Conj H⁻¹ CZ⁻¹ CXi
    H⁻¹-CZ⁻¹ = conj-lit E₀.H-H⁻¹

    CX^p-1 : CX ^ p-1 ≈ CXi
    CX^p-1 = conj-unique (conj-^ H⁻¹-CZ p-1) H⁻¹-CZ⁻¹

    S↑-S⁻¹↑ : S ↑ • S⁻¹ ↑ ≈ ε
    S↑-S⁻¹↑ = lift↑ E₁.S-S⁻¹

    S⁻¹↑-S↑ : S⁻¹ ↑ • S ↑ ≈ ε
    S⁻¹↑-S↑ = lift↑ E₁.S⁻¹-S

    blake : S⁻¹ ↑ • (S⁻¹ • (CX ^ p-1 • (S • CX))) ≈ CZ
    blake = blake-c12

    -- CX⁻¹ • S • CX ≈ S • S ↑ • CZ, with the CX⁻¹ moved across.
    B0 : Conj CXi S (S • (S ↑ • CZ))
    B0 = begin
      CXi • S                          ≈⟨ sym right-unit ⟩
      (CXi • S) • ε                    ≈⟨ cright sym CX-CXi ⟩
      (CXi • S) • (CX • CXi)           ≈⟨ by-passoc ((□ • □) • (□ • □)) ((□ • (□ • □)) • □) auto ⟩
      (CXi • (S • CX)) • CXi           ≈⟨ cleft cleft sym CX^p-1 ⟩
      (CX ^ p-1 • (S • CX)) • CXi      ≈⟨ cleft unblake ⟩
      (S • (S ↑ • CZ)) • CXi ∎
      where
      unblake : CX ^ p-1 • (S • CX) ≈ S • (S ↑ • CZ)
      unblake = sym (begin
        S • (S ↑ • CZ)                                       ≈⟨ cright cright sym blake ⟩
        S • (S ↑ • (S⁻¹ ↑ • (S⁻¹ • (CX ^ p-1 • (S • CX)))))  ≈⟨ cright cancel-• S↑-S⁻¹↑ ⟩
        S • (S⁻¹ • (CX ^ p-1 • (S • CX)))                    ≈⟨ cancel-• E₀.S-S⁻¹ ⟩
        CX ^ p-1 • (S • CX) ∎)

    -- … and with S inverted.
    B0⁻ : Conj CXi S⁻¹ (CZ⁻¹ • (S⁻¹ ↑ • S⁻¹))
    B0⁻ = conj-inv-u E₀.S-S⁻¹ inv B0
      where
      inv : (CZ⁻¹ • (S⁻¹ ↑ • S⁻¹)) • (S • (S ↑ • CZ)) ≈ ε
      inv = begin
        (CZ⁻¹ • (S⁻¹ ↑ • S⁻¹)) • (S • (S ↑ • CZ))
          ≈⟨ by-passoc ((□ • (□ • □)) • (□ • (□ • □))) (□ • (□ • (□ • (□ • (□ • □))))) auto ⟩
        CZ⁻¹ • (S⁻¹ ↑ • (S⁻¹ • (S • (S ↑ • CZ))))
          ≈⟨ cright cright cancel-• E₀.S⁻¹-S ⟩
        CZ⁻¹ • (S⁻¹ ↑ • (S ↑ • CZ))
          ≈⟨ cright cancel-• S⁻¹↑-S↑ ⟩
        CZ⁻¹ • CZ
          ≈⟨ CZ⁻¹-CZ ⟩
        ε ∎

    CZ⁻¹-S⁻¹ : Conj CZ⁻¹ S⁻¹ S⁻¹
    CZ⁻¹-S⁻¹ = conj-^ (conj-^ˡ CZ-S p-1) p-1

    S⁻¹↑-S⁻¹ : Conj (S⁻¹ ↑) S⁻¹ S⁻¹
    S⁻¹↑-S⁻¹ = conj-^ (↑S S⁻¹) p-1

    S⁻¹↑-CXi : Conj (S⁻¹ ↑) CXi CXi
    S⁻¹↑-CXi = conj-• (conj-^ (↑H S⁻¹) 3) (conj-• (conj-^ S⁻¹↑-CZ p-1) (↑H S⁻¹))

    -- S⁻¹ • CZ⁻¹ • CX⁻¹ • S⁻¹ ↑ • S ≈ CX⁻¹: the blake rule once more.
    E3 : S⁻¹ • (CZ⁻¹ • (CXi • S⁻¹ ↑)) ≈ CXi • S⁻¹
    E3 = sym (begin
      CXi • S⁻¹                          ≈⟨ B0⁻ ⟩
      (CZ⁻¹ • (S⁻¹ ↑ • S⁻¹)) • CXi       ≈⟨ cleft cright S⁻¹↑-S⁻¹ ⟩
      (CZ⁻¹ • (S⁻¹ • S⁻¹ ↑)) • CXi       ≈⟨ cleft sym assoc ⟩
      ((CZ⁻¹ • S⁻¹) • S⁻¹ ↑) • CXi       ≈⟨ cleft cleft CZ⁻¹-S⁻¹ ⟩
      ((S⁻¹ • CZ⁻¹) • S⁻¹ ↑) • CXi       ≈⟨ by-passoc (((□ • □) • □) • □) (□ • (□ • (□ • □))) auto ⟩
      S⁻¹ • (CZ⁻¹ • (S⁻¹ ↑ • CXi))       ≈⟨ cright cright S⁻¹↑-CXi ⟩
      S⁻¹ • (CZ⁻¹ • (CXi • S⁻¹ ↑)) ∎)

    -- S⁻¹ • CX • S ≈ CX • CZ⁻¹ • S⁻¹ ↑.
    B2 : Conj S⁻¹ CX (CX • (CZ⁻¹ • S⁻¹ ↑))
    B2 = begin
      S⁻¹ • CX                         ≈⟨ sym (conj-inv CX-CXi CXi-CX B0⁻) ⟩
      CX • (CZ⁻¹ • (S⁻¹ ↑ • S⁻¹))      ≈⟨ by-passoc (□ • (□ • (□ • □))) ((□ • (□ • □)) • □) auto ⟩
      (CX • (CZ⁻¹ • S⁻¹ ↑)) • S⁻¹ ∎

    ----------------------------------------------------------------------
    -- D2: D commutes with H
    --
    -- Conjugating CZ by H two ways.  Directly it gives H⁻¹ • Y • H; via
    -- H = S⁻¹ • H⁻¹ • S⁻¹ • H⁻¹ • S⁻¹ (order-SH) and blake-c12 it gives
    -- S⁻¹ • Y • CX⁻¹ • S⁻¹ ↑ • S.  Writing Y = D • CZ⁻¹ on both sides
    -- and cancelling a CX⁻¹ leaves H⁻¹ • D • H ≈ D, given D1.

    E1 : Conj H CZ (H⁻¹ • (Y • H))
    E1 = sym (begin
      (H⁻¹ • (Y • H)) • H                ≈⟨ by-assoc auto ⟩
      H ^ 4 • (H • (CZ • H ^ 4))         ≈⟨ cong E₀.H⁴ (cright cright E₀.H⁴) ⟩
      ε • (H • (CZ • ε))                 ≈⟨ trans left-unit (cright right-unit) ⟩
      H • CZ ∎)

    S⁻¹-CZ : Conj S⁻¹ CZ CZ
    S⁻¹-CZ = conj-^ˡ (comm-sym CZ-S) p-1

    H⁻¹-S⁻¹↑ : Conj H⁻¹ (S⁻¹ ↑) (S⁻¹ ↑)
    H⁻¹-S⁻¹↑ = comm-sym (conj-^ (↑H S⁻¹) 3)

    E2 : Conj (H⁻¹ • (S⁻¹ • (H⁻¹ • S⁻¹))) CZ (Y • (CXi • S⁻¹ ↑))
    E2 = conj-∘ (conj-∘ (conj-∘ S⁻¹-CZ H⁻¹-CZ) B2)
                (conj-• (E₀.H⁻¹-conj CZ) (conj-• H⁻¹-CZ⁻¹ H⁻¹-S⁻¹↑))

    E4 : Conj S⁻¹ (Y • (CXi • S⁻¹ ↑)) (H⁻¹ • (Y • H))
    E4 = conj-cancelʳ (conj-congˡ E₀.SH-inv E1) E2

    D-S⁻¹ : Conj D S⁻¹ S⁻¹
    D-S⁻¹ = conj-^ D-S p-1

    D-H : Conj H D D
    D-H = conj-cong (sym core) refl (conj-lit' E₀.H-H⁻¹)
      where
      lhs : S⁻¹ • (Y • (CXi • S⁻¹ ↑)) ≈ D • (CXi • S⁻¹)
      lhs = begin
        S⁻¹ • (Y • (CXi • S⁻¹ ↑))             ≈⟨ cright cleft Y≈ ⟩
        S⁻¹ • ((D • CZ⁻¹) • (CXi • S⁻¹ ↑))    ≈⟨ by-passoc (□ • ((□ • □) • (□ • □))) ((□ • □) • (□ • (□ • □))) auto ⟩
        (S⁻¹ • D) • (CZ⁻¹ • (CXi • S⁻¹ ↑))    ≈⟨ cleft sym D-S⁻¹ ⟩
        (D • S⁻¹) • (CZ⁻¹ • (CXi • S⁻¹ ↑))    ≈⟨ assoc ⟩
        D • (S⁻¹ • (CZ⁻¹ • (CXi • S⁻¹ ↑)))    ≈⟨ cright E3 ⟩
        D • (CXi • S⁻¹) ∎

      rhs : (H⁻¹ • (Y • H)) • S⁻¹ ≈ (H⁻¹ • (D • H)) • (CXi • S⁻¹)
      rhs = begin
        (H⁻¹ • (Y • H)) • S⁻¹                          ≈⟨ cleft cright cleft Y≈ ⟩
        (H⁻¹ • ((D • CZ⁻¹) • H)) • S⁻¹                 ≈⟨ cleft cright cleft cright sym left-unit ⟩
        (H⁻¹ • ((D • (ε • CZ⁻¹)) • H)) • S⁻¹           ≈⟨ cleft cright cleft cright cleft sym E₀.H-H⁻¹ ⟩
        (H⁻¹ • ((D • ((H • H⁻¹) • CZ⁻¹)) • H)) • S⁻¹
          ≈⟨ by-passoc ((□ • ((□ • ((□ • □) • □)) • □)) • □) ((□ • (□ • □)) • ((□ • (□ • □)) • □)) auto ⟩
        (H⁻¹ • (D • H)) • ((H⁻¹ • (CZ⁻¹ • H)) • S⁻¹) ∎

      core : D ≈ H⁻¹ • (D • H)
      core = •-cancelʳ {h = CXi • S⁻¹} (trans (sym lhs) (trans E4 rhs))

    D-H' : Conj D H H
    D-H' = comm-sym D-H

    module DF = Fix D-H' D-S

    ----------------------------------------------------------------------
    -- Consequences of D1 and D2

    HH-D : Conj HH D D
    HH-D = comm-sym DF.wHH

    HHCZ-D : Conj (HH • CZ) D D
    HHCZ-D = by-assoc auto

    CZ-D : Conj CZ D D
    CZ-D = conj-cancelˡ HHCZ-D HH-D

    Y-CZ : Conj Y CZ CZ
    Y-CZ = •-cancelʳ {h = CZ} (begin
      (Y • CZ) • CZ    ≈⟨ cleft sym D≈ ⟩
      D • CZ           ≈⟨ sym CZ-D ⟩
      CZ • D           ≈⟨ cright D≈ ⟩
      CZ • (Y • CZ)    ≈⟨ sym assoc ⟩
      (CZ • Y) • CZ ∎)

    Y-Yi : Y • Yi ≈ ε
    Y-Yi = sandwich-inv E₀.HH-HH E₀.HH-HH CZ-CZ⁻¹

    Yi-Y : Yi • Y ≈ ε
    Yi-Y = sandwich-inv E₀.HH-HH E₀.HH-HH CZ⁻¹-CZ

    D-Di : D • Di ≈ ε
    D-Di = trans (cleft D≈) (tele CZ-CZ⁻¹ Y-Yi)

    Di-D : Di • D ≈ ε
    Di-D = trans (cright D≈) (tele Yi-Y CZ⁻¹-CZ)

    CZY≈D : CZ • Y ≈ D
    CZY≈D = begin
      CZ • Y                     ≈⟨ sym left-unit ⟩
      ε • (CZ • Y)               ≈⟨ cleft sym E₀.HH-HH ⟩
      (HH • HH) • (CZ • Y)       ≈⟨ by-assoc auto ⟩
      HH • (D • HH)              ≈⟨ cright sym HH-D ⟩
      HH • (HH • D)              ≈⟨ cancel-• E₀.HH-HH ⟩
      D ∎

    D-Yi : D • Yi ≈ CZ
    D-Yi = trans (cleft sym CZY≈D) (trans assoc (trans (cright Y-Yi) right-unit))

    -- D3: m₁ inverts D.
    Yi-CZ⁻¹ : Conj Yi CZ⁻¹ CZ⁻¹
    Yi-CZ⁻¹ = conj-^ (conj-inv Yi-Y Y-Yi Y-CZ) p-1

    m₁-D : Conj (HH ↑) D Di
    m₁-D = conj-cong refl tail (conj-• m₁-HH (conj-• m₁-CZ (conj-• m₁-HH m₁-CZ)))
      where
      tail : HH • (CZ⁻¹ • (HH • CZ⁻¹)) ≈ Di
      tail = begin
        HH • (CZ⁻¹ • (HH • CZ⁻¹))   ≈⟨ by-passoc (□ • (□ • (□ • □))) ((□ • (□ • □)) • □) auto ⟩
        (HH • (CZ⁻¹ • HH)) • CZ⁻¹   ≈⟨ Yi-CZ⁻¹ ⟩
        CZ⁻¹ • Yi ∎

    -- D ^ p ≈ ε: Y and CZ commute and both have order p.
    Yᵖ : Y ^ p ≈ ε
    Yᵖ = •-cancelʳ {h = HH} (begin
      Y ^ p • HH       ≈⟨ sym (conj-^ HH-CZ-Y p) ⟩
      HH • CZ ^ p      ≈⟨ cright order-CZ ⟩
      HH • ε           ≈⟨ right-unit ⟩
      HH               ≈⟨ sym left-unit ⟩
      ε • HH ∎)
      where
      HH-CZ-Y : Conj HH CZ Y
      HH-CZ-Y = begin
        HH • CZ                ≈⟨ sym right-unit ⟩
        (HH • CZ) • ε          ≈⟨ cright sym E₀.HH-HH ⟩
        (HH • CZ) • (HH • HH)  ≈⟨ by-assoc auto ⟩
        Y • HH ∎

    Dᵖ : D ^ p ≈ ε
    Dᵖ = begin
      D ^ p             ≈⟨ ^-cong D (Y • CZ) p D≈ ⟩
      (Y • CZ) ^ p      ≈⟨ ^-• Y CZ p Y-CZ ⟩
      Y ^ p • CZ ^ p    ≈⟨ cong Yᵖ order-CZ ⟩
      ε • ε             ≈⟨ left-unit ⟩
      ε ∎

    -- D ^ 2 ≈ ε and D ^ p ≈ ε with p odd force D ≈ ε: D is D ^ (2 · ½)
    -- once the exponent is reduced mod p.
    D²⇒ε : D • D ≈ ε → D ≈ ε
    D²⇒ε DD = begin
      D                                       ≡⟨ Eq.cong (D ^_) (Eq.sym (Eq.cong toℕ two)) ⟩
      D ^ toℕ (Shared.2ₚ * Shared.1/2)        ≡⟨ Eq.cong (D ^_) (Eq.sym (lemma-toℕ-% Shared.2ₚ Shared.1/2)) ⟩
      D ^ ((2 Nat.* toℕ Shared.1/2) Nat.% p)  ≈⟨ sym (GLm.lemma-pow-mod Dᵖ (2 Nat.* toℕ Shared.1/2)) ⟩
      D ^ (2 Nat.* toℕ Shared.1/2)            ≈⟨ sym (^^ D 2 (toℕ Shared.1/2)) ⟩
      (D ^ 2) ^ toℕ Shared.1/2                ≈⟨ ^-cong (D ^ 2) ε (toℕ Shared.1/2) DD ⟩
      ε ^ toℕ Shared.1/2                      ≈⟨ ε^k=ε (toℕ Shared.1/2) ⟩
      ε ∎
      where
      two : Shared.2ₚ * Shared.1/2 ≡ ₁
      two = Eq.trans (*-comm Shared.2ₚ Shared.1/2) Shared.aux-half*2

    ----------------------------------------------------------------------
    -- D4: Ex • A ≈ W • D⁻¹, with W the Weyl word of the root e₀ + e₁

    W : Word (Gen (₂₊ n))
    W = CZ • (A • (CZ • (Ai • CZ)))

    A-A : A • A ≈ HH • HH ↑
    A-A = begin
      (H • H ↑) • (H • H ↑)   ≈⟨ by-assoc auto ⟩
      H • ((H ↑ • H) • H ↑)   ≈⟨ cright cleft ↑H H ⟩
      H • ((H • H ↑) • H ↑)   ≈⟨ by-assoc auto ⟩
      HH • HH ↑ ∎

    Ai-A : Ai • A ≈ ε
    Ai-A = begin
      (H⁻¹ • H⁻¹ ↑) • (H • H ↑)    ≈⟨ by-assoc auto ⟩
      H⁻¹ • ((H⁻¹ ↑ • H) • H ↑)    ≈⟨ cright cleft ↑H H⁻¹ ⟩
      H⁻¹ • ((H • H⁻¹ ↑) • H ↑)    ≈⟨ by-assoc auto ⟩
      (H⁻¹ • H) • (H⁻¹ ↑ • H ↑)    ≈⟨ cong E₀.H⁻¹-H (lift↑ E₁.H⁻¹-H) ⟩
      ε • ε                        ≈⟨ left-unit ⟩
      ε ∎

    m₁CZm₁ : HH ↑ • (CZ • HH ↑) ≈ CZ⁻¹
    m₁CZm₁ = trans (sym assoc) (trans (cleft m₁-CZ) (trans assoc (trans (cright m₁m₁) right-unit)))

    AcAA : A • (CZ • (A • A)) ≈ Ai • Yi
    AcAA = begin
      A • (CZ • (A • A))                         ≈⟨ sym (cancel-• Ai-A) ⟩
      Ai • (A • (A • (CZ • (A • A))))            ≈⟨ cright by-passoc (□ • (□ • (□ • □))) ((□ • □) • (□ • □)) auto ⟩
      Ai • ((A • A) • (CZ • (A • A)))            ≈⟨ cright cong A-A (cright A-A) ⟩
      Ai • ((HH • HH ↑) • (CZ • (HH • HH ↑)))    ≈⟨ cright mid ⟩
      Ai • Yi ∎
      where
      mid : (HH • HH ↑) • (CZ • (HH • HH ↑)) ≈ Yi
      mid = begin
        (HH • HH ↑) • (CZ • (HH • HH ↑))       ≈⟨ cright cright sym m₁-HH ⟩
        (HH • HH ↑) • (CZ • (HH ↑ • HH))       ≈⟨ by-passoc ((□ • □) • (□ • (□ • □))) (□ • ((□ • (□ • □)) • □)) auto ⟩
        HH • ((HH ↑ • (CZ • HH ↑)) • HH)       ≈⟨ cright cleft m₁CZm₁ ⟩
        HH • (CZ⁻¹ • HH) ∎

    D4 : Ex • A ≈ W • Di
    D4 = begin
      Ex • A                                        ≈⟨ by-assoc auto ⟩
      CZ • (A • (CZ • (A • (CZ • (A • A)))))        ≈⟨ cright cright cright AcAA ⟩
      CZ • (A • (CZ • (Ai • Yi)))                   ≈⟨ cright cright cright cright sym (cancel-• CZ-CZ⁻¹) ⟩
      CZ • (A • (CZ • (Ai • (CZ • (CZ⁻¹ • Yi)))))   ≈⟨ by-passoc (□ • (□ • (□ • (□ • (□ • □))))) ((□ • (□ • (□ • (□ • □)))) • □) auto ⟩
      W • Di ∎

    ----------------------------------------------------------------------
    -- Ingredients of D5 that do not mention R

    m₁-CX : Conj (HH ↑) CX CXi
    m₁-CX = conj-• (conj-^ (↑H HH) 3) (conj-• m₁-CZ (↑H HH))

    m₁-CXi : Conj (HH ↑) CXi CX
    m₁-CXi = conj-• (conj-^ (↑H HH) 3) (conj-• m₁-CZ⁻¹ (↑H HH))

    m₁-XCi : Conj (HH ↑) XCi XC
    m₁-XCi = conj-• (lift↑ E₁.HH-H⁻¹') (conj-• m₁-CZ⁻¹ (lift↑ E₁.HH-H))

    m₁-XC : Conj (HH ↑) XC XCi
    m₁-XC = conj-• (lift↑ E₁.HH-H⁻¹') (conj-• m₁-CZ (lift↑ E₁.HH-H))

    -- CZ is m₁ • CZ⁻¹ • m₁, which is the H⁻¹ ↑-conjugate of XC⁻¹.
    CZ≈ : CZ ≈ H⁻¹ ↑ • (XCi • H ↑)
    CZ≈ = sym (begin
      H⁻¹ ↑ • ((H⁻¹ ↑ • (CZ⁻¹ • H ↑)) • H ↑)    ≈⟨ by-passoc (□ • ((□ • (□ • □)) • □)) ((□ • □) • (□ • (□ • □))) auto ⟩
      (H⁻¹ ↑ • H⁻¹ ↑) • (CZ⁻¹ • (H ↑ • H ↑))     ≈⟨ cleft lift↑ E₁.H⁻¹H⁻¹ ⟩
      HH ↑ • (CZ⁻¹ • HH ↑)                        ≈⟨ sym assoc ⟩
      (HH ↑ • CZ⁻¹) • HH ↑                        ≈⟨ cleft m₁-CZ⁻¹ ⟩
      (CZ • HH ↑) • HH ↑                          ≈⟨ assoc ⟩
      CZ • (HH ↑ • HH ↑)                          ≈⟨ cright m₁m₁ ⟩
      CZ • ε                                      ≈⟨ right-unit ⟩
      CZ ∎)

    ----------------------------------------------------------------------
    -- D4–D7 over an abstract ρ
    --
    -- What the argument needs of R: it is built from H and S, m commutes
    -- with it on both wires, H = T • ρ • T with T = H⁻¹ • ρ • H, the swap
    -- carries ρ ↑ to ρ, and CZ commutes with ρ ↑.

    module Core
      (ρ      : ∀ {k} → Word (Gen (₁₊ k)))
      (ρ-gen  : ∀ {w : Word (Gen (₂₊ n))} → Conj w H H → Conj w S S → Conj w ρ ρ)
      (ρ-HH₀  : Conj HH ρ ρ)
      (ρ-HH₁  : PB._≈_ (Γ (₁₊ n)) (HH • ρ) (ρ • HH))
      (ρ-SL₂  : PB._≈_ (Γ (₁₊ n)) H ((H⁻¹ • (ρ • H)) • (ρ • (H⁻¹ • (ρ • H)))))
      (ρ-Ex   : Conj Ex (ρ ↑) ρ)
      (ρ-CZ↑  : Conj CZ (ρ ↑) (ρ ↑))
      where

      T : ∀ {k} → Word (Gen (₁₊ k))
      T = H⁻¹ • (ρ • H)

      ρ-cross : ∀ w → Conj (w ↑) ρ ρ
      ρ-cross w = ρ-gen (↑H w) (↑S w)

      T-cross : ∀ w → Conj (w ↑) T T
      T-cross w = conj-• (conj-^ (↑H w) 3) (conj-• (ρ-cross w) (↑H w))

      -- F-d at ρ.
      ρ-CZ : Conj CZ ρ ρ
      ρ-CZ = F-d' ρ ρ-Ex ρ-cross ρ-CZ↑

      Hρ↑ : Conj H (ρ ↑) (ρ ↑)
      Hρ↑ = comm-sym (↑H ρ)

      H↑-T↑ : Conj (H ↑) (T ↑) (ρ ↑)
      H↑-T↑ = lift↑ (E₁.conj-H-lit {u = ρ})

      --------------------------------------------------------------------
      -- F-e: XC • ρ ↑ • XC⁻¹ ≈ CX • ρ • CX⁻¹
      --
      -- Ex carries ρ ↑ to ρ (F-c); Ex = ₕ|ₕ • ʰ|ʰ • ₕ|ₕ (F-b) and ₕ|ₕ
      -- fixes ρ ↑, so ₕ|ₕ • ʰ|ʰ carries ρ ↑ to ρ.  That word is
      -- m₀ • CX • m₁ • XC, and m₀ • CX • m₁ carries CX • ρ • CX⁻¹ to ρ.

      hh-ρ↑ : Conj ₕ|ₕ (ρ ↑) (ρ ↑)
      hh-ρ↑ = conj-∘ (conj-∘ Hρ↑ ρ-CZ↑) Hρ↑

      hhhh : Conj (ₕ|ₕ • ʰ|ʰ) (ρ ↑) ρ
      hhhh = conj-cancelʳ (conj-congˡ (trans lemma-Ex-hhh (sym assoc)) ρ-Ex) hh-ρ↑

      hhhh≈ : ₕ|ₕ • ʰ|ʰ ≈ (HH • (CX • HH ↑)) • XC
      hhhh≈ = sym (begin
        (HH • (CX • HH ↑)) • XC
          ≈⟨ by-assoc auto ⟩
        H ^ 4 • (H • (CZ • (H • ((H ↑) ^ 4 • (H ↑ • (CZ • H ↑))))))
          ≈⟨ cong E₀.H⁴ (cright cright cright cleft H↑⁴) ⟩
        ε • (H • (CZ • (H • (ε • (H ↑ • (CZ • H ↑))))))
          ≈⟨ by-assoc auto ⟩
        ₕ|ₕ • ʰ|ʰ ∎)

      F-e : Conj XC (ρ ↑) (CX • (ρ • CXi))
      F-e = conj-cancelˡ (conj-congˡ hhhh≈ hhhh) b-conj
        where
        b-conj : Conj (HH • (CX • HH ↑)) (CX • (ρ • CXi)) ρ
        b-conj = conj-∘ (conj-∘ (conj-• m₁-CX (conj-• (ρ-cross HH) m₁-CXi))
                                (conj-lit' CX-CXi))
                        ρ-HH₀

      F-e′ : XC • (ρ ↑ • XCi) ≈ CX • (ρ • CXi)
      F-e′ = begin
        XC • (ρ ↑ • XCi)                       ≈⟨ sym assoc ⟩
        (XC • ρ ↑) • XCi                       ≈⟨ cleft F-e ⟩
        ((CX • (ρ • CXi)) • XC) • XCi          ≈⟨ assoc ⟩
        (CX • (ρ • CXi)) • (XC • XCi)          ≈⟨ cright XC-XCi ⟩
        (CX • (ρ • CXi)) • ε                   ≈⟨ right-unit ⟩
        CX • (ρ • CXi) ∎

      --------------------------------------------------------------------
      -- D5: W carries T ↑ to ρ
      --
      -- Term by term: CZ carries T ↑ to P₁ = H⁻¹ ↑ • V • H ↑ with
      -- V = XC⁻¹ • ρ ↑ • XC; A⁻¹ carries that to Y • T • Y⁻¹ (F-e, m₁
      -- conjugated); CZ carries that to T (CZ • Y is D, which fixes T by
      -- D1–D2); A carries T to ρ; and CZ fixes ρ.

      V P₁ P₂ : Word (Gen (₂₊ n))
      V = XCi • (ρ ↑ • XC)
      P₁ = H⁻¹ ↑ • (V • H ↑)
      P₂ = Y • (T • Yi)

      s1 : Conj CZ (T ↑) P₁
      s1 = conj-congˡ (sym CZ≈)
             (conj-∘ (conj-∘ H↑-T↑ (conj-lit XC-XCi)) (conj-lit H↑-H⁻¹↑))

      mVm : HH ↑ • (V • HH ↑) ≈ CX • (ρ • CXi)
      mVm = begin
        HH ↑ • (V • HH ↑)                         ≈⟨ sym assoc ⟩
        (HH ↑ • V) • HH ↑                         ≈⟨ cleft conj-• m₁-XCi (conj-• (lift↑ ρ-HH₁) m₁-XC) ⟩
        ((XC • (ρ ↑ • XCi)) • HH ↑) • HH ↑        ≈⟨ assoc ⟩
        (XC • (ρ ↑ • XCi)) • (HH ↑ • HH ↑)        ≈⟨ cright m₁m₁ ⟩
        (XC • (ρ ↑ • XCi)) • ε                    ≈⟨ right-unit ⟩
        XC • (ρ ↑ • XCi)                          ≈⟨ F-e′ ⟩
        CX • (ρ • CXi) ∎

      s2 : Conj Ai P₁ P₂
      s2 = conj-∘ H⁻¹↑-P₁
             (conj-• (E₀.H⁻¹-conj CZ) (conj-• (conj-lit E₀.H-H⁻¹) (E₀.H⁻¹-conj CZ⁻¹)))
        where
        H⁻¹↑-P₁ : Conj (H⁻¹ ↑) P₁ (CX • (ρ • CXi))
        H⁻¹↑-P₁ = begin
          H⁻¹ ↑ • (H⁻¹ ↑ • (V • H ↑))              ≈⟨ sym assoc ⟩
          (H⁻¹ ↑ • H⁻¹ ↑) • (V • H ↑)              ≈⟨ cleft lift↑ E₁.H⁻¹H⁻¹ ⟩
          HH ↑ • (V • H ↑)                         ≈⟨ cright cright sym (cancel-• m₁m₁) ⟩
          HH ↑ • (V • (HH ↑ • (HH ↑ • H ↑)))       ≈⟨ by-passoc (□ • (□ • (□ • □))) ((□ • (□ • □)) • □) auto ⟩
          (HH ↑ • (V • HH ↑)) • (HH ↑ • H ↑)       ≈⟨ cong mVm (by-assoc auto) ⟩
          (CX • (ρ • CXi)) • H⁻¹ ↑ ∎

      D-T : Conj D T T
      D-T = conj-• DF.wH⁻¹ (conj-• (ρ-gen D-H' D-S) D-H')

      s3 : Conj CZ P₂ T
      s3 = begin
        CZ • (Y • (T • Yi))      ≈⟨ sym assoc ⟩
        (CZ • Y) • (T • Yi)      ≈⟨ cleft CZY≈D ⟩
        D • (T • Yi)             ≈⟨ sym assoc ⟩
        (D • T) • Yi             ≈⟨ cleft D-T ⟩
        (T • D) • Yi             ≈⟨ assoc ⟩
        T • (D • Yi)             ≈⟨ cright D-Yi ⟩
        T • CZ ∎

      s4 : Conj A T ρ
      s4 = conj-∘ (T-cross H) E₀.conj-H-lit

      D5 : Conj W (T ↑) ρ
      D5 = conj-∘ (conj-∘ (conj-∘ (conj-∘ s1 s2) s3) s4) ρ-CZ

      --------------------------------------------------------------------
      -- D6: D commutes with T ↑
      --
      -- Ex • A carries T ↑ to ρ by F-c, and Ex • A is W • D⁻¹ (D4).

      D-T↑ : Conj D (T ↑) (T ↑)
      D-T↑ = conj-inv D-Di Di-D Di-T↑
        where
        Di-T↑ : Conj Di (T ↑) (T ↑)
        Di-T↑ = conj-cancelˡ (conj-congˡ D4 (conj-∘ (conj-∘ H↑-T↑ Hρ↑) ρ-Ex)) D5

      --------------------------------------------------------------------
      -- D7: so D commutes with H ↑ = T ↑ • ρ ↑ • T ↑, hence with m₁, which
      -- inverts it; D ^ 2 ≈ ε, and with D ^ p ≈ ε, D ≈ ε.

      D-ρ↑ : Conj D (ρ ↑) (ρ ↑)
      D-ρ↑ = comm-sym (conj-• ρ↑HH (conj-• ρ↑CZ (conj-• ρ↑HH ρ↑CZ)))
        where
        ρ↑HH : Conj (ρ ↑) HH HH
        ρ↑HH = conj-^ (↑H ρ) 2

        ρ↑CZ : Conj (ρ ↑) CZ CZ
        ρ↑CZ = comm-sym ρ-CZ↑

      D-H↑ : Conj D (H ↑) (H ↑)
      D-H↑ = conj-cong (sym SL₂↑) (sym SL₂↑) (conj-• D-T↑ (conj-• D-ρ↑ D-T↑))
        where
        SL₂↑ : H ↑ ≈ T ↑ • (ρ ↑ • T ↑)
        SL₂↑ = lift↑ ρ-SL₂

      D≈ε : D ≈ ε
      D≈ε = D²⇒ε (trans (cright D≈Di) D-Di)
        where
        D≈Di : D ≈ Di
        D≈Di = conj-unique (comm-sym (conj-• D-H↑ D-H↑)) m₁-D

    private
      module C = Core R (λ wH wS → Fix.wR wH wS) E₀.HH-R E₁.HH-R E₁.SL₂ ex-R
                   (comm-sym R↑-CZ)

    ----------------------------------------------------------------------
    -- D8: N, and the half-swap is an involution

    D≈ε : D ≈ ε
    D≈ε = C.D≈ε

    -- M₋₁ • CZ • M₋₁ ≈ CZ⁻¹: the bottom-wire twin of F-a.
    lemma-N : M₋₁ • (CZ • M₋₁) ≈ CZ⁻¹
    lemma-N = begin
      M₋₁ • (CZ • M₋₁)    ≈⟨ cong (sym O₀.order-H') (cright sym O₀.order-H') ⟩
      Y                   ≈⟨ Y≈ ⟩
      D • CZ⁻¹            ≈⟨ cleft D≈ε ⟩
      ε • CZ⁻¹            ≈⟨ left-unit ⟩
      CZ⁻¹ ∎

    lemma-ₕ|ₕ² : ₕ|ₕ • ₕ|ₕ ≈ ε
    lemma-ₕ|ₕ² = begin
      ₕ|ₕ • ₕ|ₕ                       ≈⟨ by-assoc auto ⟩
      H • ((CZ • (HH • CZ)) • H)      ≈⟨ cright cleft c-m-c ⟩
      H • (HH • H)                    ≈⟨ by-assoc auto ⟩
      H ^ 4                           ≈⟨ E₀.H⁴ ⟩
      ε ∎
      where
      c-m-c : CZ • (HH • CZ) ≈ HH
      c-m-c = begin
        CZ • (HH • CZ)                 ≈⟨ sym (cancel-• E₀.HH-HH) ⟩
        HH • (HH • (CZ • (HH • CZ)))   ≈⟨ cright D≈ε ⟩
        HH • ε                         ≈⟨ right-unit ⟩
        HH ∎

    lemma-ʰ|ʰ² : ʰ|ʰ • ʰ|ʰ ≈ ε
    lemma-ʰ|ʰ² = begin
      ʰ|ʰ • ʰ|ʰ                            ≈⟨ by-assoc auto ⟩
      H ↑ • ((CZ • (HH ↑ • CZ)) • H ↑)     ≈⟨ cright cleft c-m-c ⟩
      H ↑ • (HH ↑ • H ↑)                   ≈⟨ by-assoc auto ⟩
      (H ↑) ^ 4                            ≈⟨ H↑⁴ ⟩
      ε ∎
      where
      c-m-c : CZ • (HH ↑ • CZ) ≈ HH ↑
      c-m-c = begin
        CZ • (HH ↑ • CZ)            ≈⟨ cright m₁-CZ ⟩
        CZ • (CZ⁻¹ • HH ↑)          ≈⟨ cancel-• CZ-CZ⁻¹ ⟩
        HH ↑ ∎

    ----------------------------------------------------------------------
    -- D9: order-Ex

    lemma-Ex-Ex : Ex • Ex ≈ ε
    lemma-Ex-Ex = begin
      Ex • Ex
        ≈⟨ cong lemma-Ex-hhh lemma-Ex-hhh ⟩
      (ₕ|ₕ • (ʰ|ʰ • ₕ|ₕ)) • (ₕ|ₕ • (ʰ|ʰ • ₕ|ₕ))
        ≈⟨ by-passoc ((□ • (□ • □)) • (□ • (□ • □))) (□ • (□ • (□ • (□ • (□ • □))))) auto ⟩
      ₕ|ₕ • (ʰ|ʰ • (ₕ|ₕ • (ₕ|ₕ • (ʰ|ʰ • ₕ|ₕ))))
        ≈⟨ cright cright cancel-• lemma-ₕ|ₕ² ⟩
      ₕ|ₕ • (ʰ|ʰ • (ʰ|ʰ • ₕ|ₕ))
        ≈⟨ cright cancel-• lemma-ʰ|ʰ² ⟩
      ₕ|ₕ • ₕ|ₕ
        ≈⟨ lemma-ₕ|ₕ² ⟩
      ε ∎

    lemma-order-Ex : Ex ^ 2 ≈ ε
    lemma-order-Ex = lemma-Ex-Ex

------------------------------------------------------------------------
-- Presentations of groups
--
-- Realises, reduced to arithmetic in ℤ/pℤ.
--
-- Clifford.Qupit.Presentation proves that the exact rule set presents
-- the presented central extension, on one hypothesis:
--
--     Realises  —  ∀ r : u === v,  scal u ≈ corr r • scal v,
--
-- where `scal` is the SCALAR WORD a circuit picks up when it is read in
-- the total group with every gate lifted trivially, and `corr` is the
-- power of ω the Paper-V0 relator is supposed to carry.  As stated that
-- is a statement about words over ω modulo ωᵖ = 1, mixed up with the
-- cocycle machinery of CocycleGen.  This file strips all of that away.
--
-- With the cocycle taken from SemFE — the Weyl cocycle ½·sform pulled
-- back along Paper-V0's presentation — the scalar a circuit picks up is
-- ω to a power that can be written down:
--
--     Φ ε       = 0
--     Φ [ a ]ʷ  = 0
--     Φ (u • v) = Φ u + Φ v + ½·sform P⟦u⟧ (ap S⟦u⟧ P⟦v⟧)
--
-- — an element of ℤ/pℤ, not a word — and `scal w ≈ ω ^ Φ w` (scal≈).
-- Realises then follows from
--
--     Φ-Corr  —  ∀ r : u === v,  Φ u ≡ corrℤ r + Φ v      (in ℤ/pℤ)
--
-- with corrℤ the exponent corr names: (p²-1)/8 mod p for order-SH and 0
-- for everything else.  That is the whole remaining content, and it is
-- now finite and elementary: nineteen equations in ℤ/pℤ, one per rule.
--
-- Φ has a closed form worth knowing when discharging them.  Writing a
-- circuit as a₁ ⋯ a_m and Qᵢ for the i-th gate's Pauli conjugated to the
-- front — Qᵢ = (S⟦a₁⟧ ∘ ⋯ ∘ S⟦a_{i-1}⟧) P⟦aᵢ⟧ — the twisted product
-- accumulates
--
--     Φ = ½ Σ_{i<j} sform Qᵢ Qⱼ,
--
-- so only gates with a NON-TRIVIAL Pauli part contribute.  Of the three
-- generators only S has one: Simplified-V1.Forward's translation sends
-- H and CZ to pure symplectic words and S to Z^(-½) · S, so P⟦S⟧ is the
-- Pauli (0 , -½) on wire 0 and P⟦H⟧ = P⟦CZ⟧ = 0.  Every rule written
-- without S therefore has Φ = 0 on both sides, and `zeroP-both` settles
-- it in one line.  Six of the sixteen go that way, and they are done
-- below: order-CZ, order-Ex, semi-Ex-H↑ (Rules₂) and yang-baxter,
-- cz-slide, semi-CX↑-CZ↓ (Rules₃).
--
-- The structural rules are NOT among them, though Ex and CX are written
-- over CZ and H alone.  comm₁ and comm₂ quantify over an ARBITRARY 1-
-- or 2-ary gate, S included, so their Pauli-freeness is false as
-- stated; what makes them hold is that the two sides act on disjoint
-- wires, and sform of disjointly supported Paulis vanishes.  That, and
-- cong↑, wait on shift lemmas for the Paper-V0 denotation — how the
-- Pauli and symplectic parts of ⟦ w ↑ ⟧ relate to those of ⟦ w ⟧ —
-- which nothing in the library has yet.
--
-- The remaining ten base rules all mention S and are the real
-- computation: order-S, order-H, M-power (∀ k), semi-MR, order-SH,
-- comm-HHSHHS, comm-CZ-S↑, semi-M↑CZ, semi-Ex-S↑, blake-c12.
--
-- The one rule that must NOT come out zero is order-SH, and it does not.
-- With ap H (x,z) = (-z,x) and ap S (x,z) = (x,x+z), the six letters of
-- (S • H)³ contribute
--
--     ·H  0                             ·S  ½·sform (0,-½) (½,½) = -⅛
--     ·H  0                             ·S  ½·sform (½,0) (-½,0) =  0
--     ·H  0
--
-- for a total of -⅛, which is (p² - 1)/8 mod p — exactly the exponent
-- Syntactics.corr assigns it.  So Φ-Corr is true, and the convention
-- fixed by δ_p is the one this section reproduces.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford.Qupit.SemRealises
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Data.Empty using (⊥)
open import Data.Fin using (fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat using (zero)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Product using (_×_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
import Relation.Binary.PropositionalEquality as Eq

open import Data.Vec using (_∷_)

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; pI ; pIₙ ; _+ₚ_ ; +ₚ-identityˡ ; +ₚ-identityʳ ; sform)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (Symplectic)
open Symplectic using (ap)

open import Word.Base using (Word ; ε ; _•_ ; _^_ ; [_]ʷ)
import Presentation.Base as PB

import Examples.Groups.Cyclic.Scalars as Sc
module Sp = Sc p-2

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen as Pap
import Examples.Groups.Clifford.Qupit.Syntactics
  p-3 p-prime g* g-gen as QS
import Examples.Groups.Clifford.Qupit.Semantics p-3 p-prime as Sem
import Examples.Groups.Clifford.Qupit.SemGeneratorData
  p-3 p-prime g* g-gen as SGD
import Examples.Groups.Clifford.Qupit.SemFE p-3 p-prime g* g-gen as FE
import Examples.Groups.Clifford.Qupit.SemShift p-3 p-prime g* g-gen as SH

module PE = Sem.Presented-Extension g* g-gen
module KB = PB QS.Scalar-relation

------------------------------------------------------------------------
-- ω to a natural power, as the transport of a residue
--
-- emb is the transport ℤ/pℤ → words over ω; a natural exponent reaches
-- it through its residue, since ω has order p.

modp : ℕ → ℤ ₚ
modp k = fromℕ< (m%n<n k p)

ω^-emb : ∀ k → KB._≈_ (QS.ω ^ k) (Sp.emb (modp k))
ω^-emb k =
  KB.trans (Sp.T^-% k)
           (KB.refl' (Eq.cong (QS.ω ^_) (Eq.sym (toℕ-fromℕ< (m%n<n k p)))))

------------------------------------------------------------------------
-- The correction, as an exponent
--
-- corrℤ mirrors Syntactics.corr clause for clause; corr-emb is that
-- mirroring, checked.  Every rule but order-SH lifts exactly, and there
-- both sides are ε on the nose (emb ₀ is ω ^ 0).

private
  variable
    m n : ℕ

srel-corrℤ : ∀ {u v} → QS.CB._SRel,_===_ m u v → ℤ ₚ
srel-corrℤ QS.CB.order-SH = modp QS.sh-exponent
srel-corrℤ _              = ₀

corrℤ : ∀ {u v} → QS.CR._QRel,_===_ m u v → ℤ ₚ
corrℤ (QS.CR.srel r)    = srel-corrℤ r
corrℤ (QS.CR.cong↑ r)   = corrℤ r
corrℤ (QS.CR.comm₁ h x) = ₀
corrℤ (QS.CR.comm₂ h x) = ₀

private
  srel-emb : ∀ {u v} (r : QS.CB._SRel,_===_ m u v) →
             KB._≈_ (QS.srel-corr r) (Sp.emb (srel-corrℤ r))
  srel-emb QS.CB.order-SH     = ω^-emb QS.sh-exponent
  srel-emb QS.CB.order-S      = KB.refl
  srel-emb QS.CB.order-H      = KB.refl
  srel-emb (QS.CB.M-power k)  = KB.refl
  srel-emb QS.CB.semi-MR      = KB.refl
  srel-emb QS.CB.comm-HHSHHS  = KB.refl
  srel-emb QS.CB.order-CZ     = KB.refl
  srel-emb QS.CB.order-Ex     = KB.refl
  srel-emb QS.CB.comm-CZ-S↑   = KB.refl
  srel-emb QS.CB.semi-M↑CZ    = KB.refl
  srel-emb QS.CB.semi-Ex-S↑   = KB.refl
  srel-emb QS.CB.semi-Ex-H↑   = KB.refl
  srel-emb QS.CB.blake-c12    = KB.refl
  srel-emb QS.CB.yang-baxter  = KB.refl
  srel-emb QS.CB.cz-slide     = KB.refl
  srel-emb QS.CB.semi-CX↑-CZ↓ = KB.refl

corr-emb : ∀ {u v} (r : QS.CR._QRel,_===_ m u v) →
           KB._≈_ (QS.corr r) (Sp.emb (corrℤ r))
corr-emb (QS.CR.srel r)    = srel-emb r
corr-emb (QS.CR.cong↑ r)   = corr-emb r
corr-emb (QS.CR.comm₁ h x) = KB.refl
corr-emb (QS.CR.comm₂ h x) = KB.refl

------------------------------------------------------------------------
-- The phase of a circuit
--
-- The exponent the twisted product accumulates: nothing for a single
-- gate, and one application of the pulled-back Weyl cocycle per
-- concatenation.

module Width (n : ℕ) where

  private
    gd : PE.GeneratorData n
    gd = FE.generator-data n

    module W  = FE.Weyl n
    module Ev = PE.Evaluation n (PE.γᶜ n gd)

  private
    -- A circuit's gate part is the circuit itself: the second component
    -- never sees the cocycle.
    gate : (w : QS.Circuit n) → proj₂ Ev.⟦ w ⟧ ≡ w
    gate [ a ]ʷ  = Eq.refl
    gate ε       = Eq.refl
    gate (u • v) = Eq.cong₂ _•_ (gate u) (gate v)

    agree : ∀ u v → KB._≈_ (PE.CGn.f n (PE.φ n) (PE.GeneratorData.G gd) u v)
                           (Sp.emb (W.fa u v))
    agree = SGD.From-FactorSet.agree n W.factorSet

  --------------------------------------------------------------------
  -- Circuits with no Pauli
  --
  -- Of the three generators only S has a Pauli part, so a rule written
  -- without S has Φ = 0 on both sides.  `ZeroP` is that hypothesis, one
  -- clause per letter.  It stays TRANSPARENT: deciding it for a concrete
  -- circuit is exactly what each S-free rule does, one `refl` per gate.

  P⟦_⟧ : QS.Circuit n → Pauli n
  P⟦ w ⟧ = proj₁ W.⟦ w ⟧

  S⟦_⟧ : QS.Circuit n → Symplectic n
  S⟦ w ⟧ = proj₂ W.⟦ w ⟧

  ZeroP : QS.Circuit n → Set
  ZeroP [ a ]ʷ  = P⟦ [ a ]ʷ ⟧ ≡ pIₙ
  ZeroP ε       = ⊤
  ZeroP (u • v) = ZeroP u × ZeroP v

  -- The cocycle between two circuits vanishes as soon as EITHER of them
  -- is Pauli-free — on the left because sform does, on the right because
  -- a symplectic map fixes the trivial Pauli first.  This is weaker than
  -- asking both sides of a rule to be S-free, and it is what carries the
  -- rules where the S-part sits as one block with Pauli-free material
  -- around it.
  fa-zeroˡ : (u v : QS.Circuit n) → P⟦ u ⟧ ≡ pIₙ → W.fa u v ≡ ₀
  fa-zeroˡ u v e =
    Eq.trans (Eq.cong (Sem.1/2 *_)
               (Eq.trans (Eq.cong (λ z → sform z (ap S⟦ u ⟧ P⟦ v ⟧)) e)
                         (Sem.sform-pIˡ (ap S⟦ u ⟧ P⟦ v ⟧))))
             (*-zeroʳ Sem.1/2)

  fa-zeroʳ : (u v : QS.Circuit n) → P⟦ v ⟧ ≡ pIₙ → W.fa u v ≡ ₀
  fa-zeroʳ u v e =
    Eq.trans (Eq.cong (Sem.1/2 *_)
               (Eq.trans (Eq.cong (λ z → sform P⟦ u ⟧ (ap S⟦ u ⟧ z)) e)
                 (Eq.trans (Eq.cong (sform P⟦ u ⟧) (Sem.ap-ε S⟦ u ⟧))
                           (Sem.sform-pIʳ P⟦ u ⟧))))
             (*-zeroʳ Sem.1/2)

  -- The Pauli part of a concatenation, and its two consequences: a
  -- Pauli-free right factor leaves it alone, and it is congruent in that
  -- factor.  With `fa-congʳ` these let two words be shown to carry the
  -- SAME cocycle term without either term being evaluated.
  P-∙ : (u v : QS.Circuit n) → P⟦ u • v ⟧ ≡ P⟦ u ⟧ +ₚ ap S⟦ u ⟧ P⟦ v ⟧
  P-∙ u v = proj₁ (W.⟦⟧-∙ u v)

  P-•-freeʳ : (u v : QS.Circuit n) → P⟦ v ⟧ ≡ pIₙ → P⟦ u • v ⟧ ≡ P⟦ u ⟧
  P-•-freeʳ u v e =
    Eq.trans (P-∙ u v)
      (Eq.trans (Eq.cong (λ z → P⟦ u ⟧ +ₚ ap S⟦ u ⟧ z) e)
        (Eq.trans (Eq.cong (P⟦ u ⟧ +ₚ_) (Sem.ap-ε S⟦ u ⟧))
                  (+ₚ-identityʳ P⟦ u ⟧)))

  P-•-congʳ : (u v v' : QS.Circuit n) → P⟦ v ⟧ ≡ P⟦ v' ⟧ →
              P⟦ u • v ⟧ ≡ P⟦ u • v' ⟧
  P-•-congʳ u v v' e =
    Eq.trans (P-∙ u v)
      (Eq.trans (Eq.cong (λ z → P⟦ u ⟧ +ₚ ap S⟦ u ⟧ z) e) (Eq.sym (P-∙ u v')))

  fa-congʳ : (u v v' : QS.Circuit n) → P⟦ v ⟧ ≡ P⟦ v' ⟧ →
             W.fa u v ≡ W.fa u v'
  fa-congʳ u v v' e = Eq.cong (λ z → Sem.1/2 * sform P⟦ u ⟧ (ap S⟦ u ⟧ z)) e

  -- A power of a Pauli-free circuit is Pauli-free.  The word is taken
  -- EXPLICITLY: `ZeroP` computes, so unifying a reduced `ZeroP w` goal
  -- never recovers w.
  zeroP-^ : (w : QS.Circuit n) → ZeroP w → ∀ k → ZeroP (w ^ k)
  zeroP-^ w z zero      = tt
  zeroP-^ w z (₁₊ zero) = z
  zeroP-^ w z (₂₊ k)    = z , zeroP-^ w z (₁₊ k)

  --------------------------------------------------------------------
  -- The phase itself, and everything that has to see through it
  --
  -- ABSTRACT, and this matters.  Φ recurses through the Weyl cocycle,
  -- so on a CONCRETE circuit it unfolds into one application of the
  -- whole Paper-V0 → V1 → semidirect denotation chain per
  -- concatenation.  Left transparent, merely *stating* an equation
  -- about Φ (Ex ^ 2) makes Agda normalise eighteen letters' worth of
  -- that, and 12 GB is not enough (measured).  Sealed here together
  -- with the three lemmas that need to see through it, and re-exported
  -- by its own defining equations, every proof downstream unfolds it
  -- exactly where it means to and nowhere else.
  --
  --   scal≈       the scalar a circuit picks up is ω ^ Φ;
  --   zeroP       a Pauli-free circuit has trivial Pauli and Φ = 0 —
  --               the accumulated Pauli stays trivial because a
  --               symplectic map fixes it (ap-ε), and the cocycle
  --               contributes nothing because sform vanishes there;
  --   zeroP-both  hence the Φ-Corr equation for any S-free rule.

  abstract

    Φ : QS.Circuit n → ℤ ₚ
    Φ [ a ]ʷ  = ₀
    Φ ε       = ₀
    Φ (u • v) = (Φ u + Φ v) + W.fa u v

    -- Its defining equations, as lemmas.
    Φ-gate : (a : QS.Gen n) → Φ [ a ]ʷ ≡ ₀
    Φ-gate a = Eq.refl

    Φ-ε : Φ ε ≡ ₀
    Φ-ε = Eq.refl

    Φ-• : (u v : QS.Circuit n) → Φ (u • v) ≡ (Φ u + Φ v) + W.fa u v
    Φ-• u v = Eq.refl

    scal≈ : (w : QS.Circuit n) → KB._≈_ (Ev.scal w) (Sp.emb (Φ w))
    scal≈ [ a ]ʷ  = KB.refl
    scal≈ ε       = KB.refl
    scal≈ (u • v) =
      KB.trans (KB.cong (KB.cong (scal≈ u) (scal≈ v)) step)
        (KB.trans (KB.cong (KB.sym (Sp.emb-∙ (Φ u) (Φ v))) KB.refl)
                  (KB.sym (Sp.emb-∙ (Φ u + Φ v) (W.fa u v))))
      where
      -- The cocycle is applied to the circuits themselves, `gate`
      -- having identified the second components.
      step : KB._≈_ (PE.CGn.f n (PE.φ n) (PE.GeneratorData.G gd)
                       (proj₂ Ev.⟦ u ⟧) (proj₂ Ev.⟦ v ⟧))
                    (Sp.emb (W.fa u v))
      step = Eq.subst₂
               (λ z₁ z₂ →
                  KB._≈_ (PE.CGn.f n (PE.φ n) (PE.GeneratorData.G gd) z₁ z₂)
                         (Sp.emb (W.fa u v)))
               (Eq.sym (gate u)) (Eq.sym (gate v)) (agree u v)

    zeroP : (w : QS.Circuit n) → ZeroP w → (P⟦ w ⟧ ≡ pIₙ) × (Φ w ≡ ₀)
    zeroP [ a ]ʷ  z        = z , Eq.refl
    zeroP ε       _        = Eq.refl , Eq.refl
    zeroP (u • v) (zu , zv) = pw , φw
      where
      -- Inside `abstract` a where-binding needs its type written out.
      ihu : (P⟦ u ⟧ ≡ pIₙ) × (Φ u ≡ ₀)
      ihu = zeroP u zu
      ihv : (P⟦ v ⟧ ≡ pIₙ) × (Φ v ≡ ₀)
      ihv = zeroP v zv

      -- The right factor's Pauli, transported by the left factor, is
      -- still trivial.
      apv : ap S⟦ u ⟧ P⟦ v ⟧ ≡ pIₙ
      apv = Eq.trans (Eq.cong (ap S⟦ u ⟧) (proj₁ ihv)) (Sem.ap-ε S⟦ u ⟧)

      pw : P⟦ u • v ⟧ ≡ pIₙ
      pw = Eq.trans (proj₁ (W.⟦⟧-∙ u v))
             (Eq.trans (Eq.cong₂ _+ₚ_ (proj₁ ihu) apv) (+ₚ-identityˡ pIₙ))

      -- ... so the cocycle term is ½ · sform pIₙ pIₙ.
      fa0 : W.fa u v ≡ ₀
      fa0 = Eq.trans
              (Eq.cong (Sem.1/2 *_)
                (Eq.trans (Eq.cong₂ sform (proj₁ ihu) apv)
                          (Sem.sform-pIˡ (pIₙ {n}))))
              (*-zeroʳ Sem.1/2)

      φw : Φ (u • v) ≡ ₀
      φw = Eq.trans (Eq.cong₂ _+_ (Eq.cong₂ _+_ (proj₂ ihu) (proj₂ ihv)) fa0)
             (Eq.trans (+-identityʳ (₀ + ₀)) (+-identityʳ ₀))

    zeroP-Φ : (w : QS.Circuit n) → ZeroP w → Φ w ≡ ₀
    zeroP-Φ w z = proj₂ (zeroP w z)

      -- Two sides that each have vanishing phase satisfy the Φ-Corr
    -- equation of an uncorrected rule.  Only the equations are used, so
    -- this needs nothing of Φ itself.
    Φ-both-zero : (u v : QS.Circuit n) → Φ u ≡ ₀ → Φ v ≡ ₀ → Φ u ≡ ₀ + Φ v
    Φ-both-zero u v eu ev =
      Eq.trans eu (Eq.sym (Eq.trans (Eq.cong (₀ +_) ev) (+-identityʳ ₀)))

    -- ... and more generally: the two sides need only agree, not vanish.
    -- This is what settles a rule whose S-part is the same block on both
    -- sides, whatever phase that block carries.
    Φ-both-eq : (u v : QS.Circuit n) (x : ℤ ₚ) →
                Φ u ≡ x → Φ v ≡ x → Φ u ≡ ₀ + Φ v
    Φ-both-eq u v x eu ev =
      Eq.trans eu (Eq.trans (Eq.sym ev) (Eq.sym (+-identityˡ (Φ v))))

  -- A rule both of whose sides are Pauli-free carries no correction:
    -- this is the Φ-Corr equation for every S-free rule, since corrℤ is
    -- ₀ on all of them.
    zeroP-both : (u v : QS.Circuit n) → ZeroP u → ZeroP v → Φ u ≡ ₀ + Φ v
    zeroP-both u v zu zv =
      Eq.trans (zeroP-Φ u zu)
        (Eq.sym (Eq.trans (Eq.cong (₀ +_) (zeroP-Φ v zv)) (+-identityʳ ₀)))

  -- Concatenation is additive on phases wherever the cocycle vanishes.
  Φ-•-zero : (u v : QS.Circuit n) → W.fa u v ≡ ₀ → Φ (u • v) ≡ Φ u + Φ v
  Φ-•-zero u v e =
    Eq.trans (Φ-• u v)
      (Eq.trans (Eq.cong ((Φ u + Φ v) +_) e) (+-identityʳ (Φ u + Φ v)))

  -- ... and a Pauli-free factor contributes nothing at all.
  Φ-•-freeˡ : (u v : QS.Circuit n) → P⟦ u ⟧ ≡ pIₙ → Φ u ≡ ₀ →
              Φ (u • v) ≡ Φ v
  Φ-•-freeˡ u v pe φe =
    Eq.trans (Φ-•-zero u v (fa-zeroˡ u v pe))
             (Eq.trans (Eq.cong (_+ Φ v) φe) (+-identityˡ (Φ v)))

  Φ-•-freeʳ : (u v : QS.Circuit n) → P⟦ v ⟧ ≡ pIₙ → Φ v ≡ ₀ →
              Φ (u • v) ≡ Φ u
  Φ-•-freeʳ u v pe φe =
    Eq.trans (Φ-•-zero u v (fa-zeroʳ u v pe))
             (Eq.trans (Eq.cong (Φ u +_) φe) (+-identityʳ (Φ u)))

  -- Two circuits with equal Pauli parts and equal phases carry the same
  -- phase after any common left factor.
  Φ-•-congʳ : (u v v' : QS.Circuit n) → P⟦ v ⟧ ≡ P⟦ v' ⟧ → Φ v ≡ Φ v' →
              Φ (u • v) ≡ Φ (u • v')
  Φ-•-congʳ u v v' pe φe =
    Eq.trans (Φ-• u v)
      (Eq.trans (Eq.cong₂ _+_ (Eq.cong (Φ u +_) φe) (fa-congʳ u v v' pe))
                (Eq.sym (Φ-• u v')))

  --------------------------------------------------------------------
  -- What is left
  --
  -- Nineteen equations in ℤ/pℤ — the sixteen Paper-V0 rules and the
  -- three structural ones — with no words, no cocycle and no extension
  -- in sight.

  Φ-Corr : Set
  Φ-Corr = ∀ {u v} (r : QS.CR._QRel,_===_ n u v) → Φ u ≡ corrℤ r + Φ v

  --------------------------------------------------------------------
  -- ... and it suffices

  realises : Φ-Corr → PE.Realises n gd
  realises hyp {u} {v} r =
    KB.trans (scal≈ u)
      (KB.trans (Sp.emb-cong (hyp r))
        (KB.trans (Sp.emb-∙ (corrℤ r) (Φ v))
          (KB.cong (KB.sym (corr-emb r)) (KB.sym (scal≈ v)))))

------------------------------------------------------------------------
-- The six S-free rules, discharged
--
-- H and CZ translate to pure symplectic words (Simplified-V1.Forward's
-- h H-gen = H, h CZ-gen = CZ), so their Pauli parts are trivial ON THE
-- NOSE — the whole denotation chain, Paper-V0 through V1 through the
-- semidirect presentation, computes on a generator.  Shifted gates are
-- no different: a shifted pure-symplectic letter is still a right
-- summand, so its Pauli is still the unit.
--
-- Ex, CX and CZ02 are written over CZ and H alone
--
--     Ex   = CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑
--     CX   = H ↓ ^ 3 • CZ • H ↓
--     CZ02 = Ex • CZ ↑ • Ex
--
-- so every rule stated without S has both sides Pauli-free, and each is
-- one application of zeroP-both.  Six of the sixteen fall to this.

-- One-wire rules.  comm-HHSHHS moves an S past H • H on both sides: the
-- H's carry no Pauli, so the S-block is the SAME on the two sides and
-- the rule closes without its phase — which is NOT zero — being
-- computed.  This is the first rule that needs the Pauli-part algebra
-- rather than just the free-factor combinators.

module Rules₁ (m : ℕ) where

  open Width (₁₊ m)

  zeroP-H : ZeroP (Pap.H {m})
  zeroP-H = Eq.refl

  private
    P-HH : P⟦ Pap.H {m} • Pap.H ⟧ ≡ pIₙ
    P-HH = proj₁ (zeroP (Pap.H {m} • Pap.H) (zeroP-H , zeroP-H))

    Φ-HH : Φ (Pap.H {m} • Pap.H) ≡ ₀
    Φ-HH = proj₂ (zeroP (Pap.H {m} • Pap.H) (zeroP-H , zeroP-H))

    -- The two blocks the S is wrapped around.
    A : QS.Circuit (₁₊ m)
    A = Pap.H • Pap.H • Pap.S

    B : QS.Circuit (₁₊ m)
    B = Pap.H • Pap.H • Pap.S • Pap.H • Pap.H

    -- Appending H • H changes no Pauli, so A and B have the same one.
    P-S-HH : P⟦ Pap.S {m} • (Pap.H • Pap.H) ⟧ ≡ P⟦ Pap.S {m} ⟧
    P-S-HH = P-•-freeʳ Pap.S (Pap.H • Pap.H) P-HH

    P-A≡B : P⟦ A ⟧ ≡ P⟦ B ⟧
    P-A≡B =
      P-•-congʳ Pap.H (Pap.H • Pap.S) (Pap.H • (Pap.S • (Pap.H • Pap.H)))
        (P-•-congʳ Pap.H Pap.S (Pap.S • (Pap.H • Pap.H)) (Eq.sym P-S-HH))

    Φ-A : Φ A ≡ ₀
    Φ-A = Eq.trans (Φ-•-freeˡ Pap.H (Pap.H • Pap.S) zeroP-H (Φ-gate _))
            (Eq.trans (Φ-•-freeˡ Pap.H Pap.S zeroP-H (Φ-gate _)) (Φ-gate _))

    Φ-B : Φ B ≡ ₀
    Φ-B = Eq.trans (Φ-•-freeˡ Pap.H _ zeroP-H (Φ-gate _))
            (Eq.trans (Φ-•-freeˡ Pap.H _ zeroP-H (Φ-gate _))
              (Eq.trans (Φ-•-freeʳ Pap.S (Pap.H • Pap.H) P-HH Φ-HH)
                        (Φ-gate _)))


  ------------------------------------------------------------------
  -- order-S : the powers of S carry no phase
  --
  -- S's Pauli is a pure Z (SemShift.gate₁S-botZ) and S FIXES a pure Z
  -- (gate₁S-fixZ), so every prefix of S ^ k stays pure-Z; two pure-Z
  -- Paulis have sform ₀, so every cocycle term along the power vanishes.
  --
  -- The induction is stated over a VARIABLE circuit `s` with those two
  -- facts as hypotheses, and applied to S exactly once.  Writing it
  -- directly about Pap.S instead costs 8 GB: `P⟦ Pap.S ⟧` normalises to
  -- ⟦ Z^(-½) · S ⟧ˢᵈ, where StarInterp's Extend must match on
  -- Z ^ toℕ (-½) and so forces a modular inverse.  As a variable, s is
  -- stuck and nothing is ever unfolded.

  private
    pow-step : (s : QS.Circuit (₁₊ m)) →
               SH.BotZ (P⟦ s ⟧) →
               ((b : ℤ ₚ) (R : Pauli m) →
                ap S⟦ s ⟧ ((₀ , b) ∷ R) ≡ (₀ , b) ∷ R) →
               Φ s ≡ ₀ →
               (k : ℕ) →
               SH.BotZ (P⟦ s ^ ₁₊ k ⟧) × (Φ (s ^ ₁₊ k) ≡ ₀) →
               SH.BotZ (P⟦ s ^ ₂₊ k ⟧) × (Φ (s ^ ₂₊ k) ≡ ₀)
    pow-step s (bS , eS) fix φs k ((b' , e') , φ') = bot , phi
      where
      -- The tail's Pauli is pure-Z, so s leaves it alone.
      apstep : ap S⟦ s ⟧ P⟦ s ^ ₁₊ k ⟧ ≡ (₀ , b') ∷ pIₙ
      apstep = Eq.trans (Eq.cong (ap S⟦ s ⟧) e') (fix b' pIₙ)

      bot : SH.BotZ (P⟦ s ^ ₂₊ k ⟧)
      bot = (bS + b') ,
        Eq.trans (P-∙ s (s ^ ₁₊ k))
          (Eq.trans (Eq.cong₂ _+ₚ_ eS apstep)
            (Eq.trans (Eq.cong (λ z → (z , bS + b') ∷ (pIₙ +ₚ pIₙ))
                               (+-identityʳ ₀))
                      (Eq.cong ((₀ , bS + b') ∷_) (+ₚ-identityˡ pIₙ))))

      phi : Φ (s ^ ₂₊ k) ≡ ₀
      phi =
        Eq.trans (Φ-•-zero s (s ^ ₁₊ k)
                   (Eq.trans (Eq.cong (Sem.1/2 *_)
                               (Eq.trans (Eq.cong₂ sform eS apstep)
                                         (SH.sform-Z-Z bS b' (pIₙ {m}))))
                             (*-zeroʳ Sem.1/2)))
                 (Eq.trans (Eq.cong₂ _+_ φs φ') (+-identityʳ ₀))

    pow-botZ : (s : QS.Circuit (₁₊ m)) →
               SH.BotZ (P⟦ s ⟧) →
               ((b : ℤ ₚ) (R : Pauli m) →
                ap S⟦ s ⟧ ((₀ , b) ∷ R) ≡ (₀ , b) ∷ R) →
               Φ s ≡ ₀ →
               (k : ℕ) → SH.BotZ (P⟦ s ^ k ⟧) × (Φ (s ^ k) ≡ ₀)
    pow-botZ s bz fix φs zero      = (₀ , Eq.refl) , Φ-ε
    pow-botZ s bz fix φs (₁₊ zero) = bz , φs
    pow-botZ s bz fix φs (₂₊ k)    =
      pow-step s bz fix φs k (pow-botZ s bz fix φs (₁₊ k))

  order-S-Φ :
    Φ (Pap.S {m} ^ p) ≡ corrℤ (QS.CR.srel (QS.CB.order-S {m})) + Φ ε
  order-S-Φ =
    Φ-both-zero (Pap.S ^ p) ε
      (proj₂ (pow-botZ Pap.S SH.gate₁S-botZ SH.gate₁S-fixZ (Φ-gate _) p))
      Φ-ε

  comm-HHSHHS-Φ :
    Φ (Pap.H • Pap.H • Pap.S • Pap.H • Pap.H • Pap.S)
      ≡ corrℤ (QS.CR.srel (QS.CB.comm-HHSHHS {m}))
        + Φ (Pap.S • Pap.H • Pap.H • Pap.S • Pap.H • Pap.H)
  comm-HHSHHS-Φ =
    Φ-both-eq (Pap.H • Pap.H • Pap.S • Pap.H • Pap.H • Pap.S)
              (Pap.S • Pap.H • Pap.H • Pap.S • Pap.H • Pap.H)
              (Φ (Pap.S {m} • A)) lhs rhs
    where
    lhs : Φ (Pap.H • Pap.H • Pap.S • Pap.H • Pap.H • Pap.S)
            ≡ Φ (Pap.S {m} • A)
    lhs = Eq.trans (Φ-•-freeˡ Pap.H _ zeroP-H (Φ-gate _))
                   (Φ-•-freeˡ Pap.H _ zeroP-H (Φ-gate _))

    rhs : Φ (Pap.S • Pap.H • Pap.H • Pap.S • Pap.H • Pap.H)
            ≡ Φ (Pap.S {m} • A)
    rhs = Eq.sym (Φ-•-congʳ Pap.S A B P-A≡B (Eq.trans Φ-A (Eq.sym Φ-B)))

module Rules₂ (m : ℕ) where

  open Width (₂₊ m)

  zeroP-CZ : ZeroP Pap.CZ
  zeroP-CZ = Eq.refl

  zeroP-H↓ : ZeroP (Pap.H Pap.↓)
  zeroP-H↓ = Eq.refl

  zeroP-H↑ : ZeroP (Pap.H Pap.↑)
  zeroP-H↑ = Eq.refl

  order-CZ-Φ : Φ (Pap.CZ ^ p) ≡ corrℤ (QS.CR.srel (QS.CB.order-CZ {m})) + Φ ε
  order-CZ-Φ = zeroP-both (Pap.CZ ^ p) ε (zeroP-^ Pap.CZ zeroP-CZ p) tt

  zeroP-Ex : ZeroP (Pap.Ex {m})
  zeroP-Ex = zeroP-CZ , zeroP-H↓ , zeroP-H↑
           , zeroP-CZ , zeroP-H↓ , zeroP-H↑
           , zeroP-CZ , zeroP-H↓ , zeroP-H↑

  order-Ex-Φ : Φ (Pap.Ex ^ 2) ≡ corrℤ (QS.CR.srel (QS.CB.order-Ex {m})) + Φ ε
  order-Ex-Φ = zeroP-both (Pap.Ex ^ 2) ε (zeroP-^ (Pap.Ex {m}) zeroP-Ex 2) tt

  semi-Ex-H↑-Φ :
    Φ (Pap.Ex • Pap.H Pap.↑)
      ≡ corrℤ (QS.CR.srel (QS.CB.semi-Ex-H↑ {m})) + Φ (Pap.H Pap.↓ • Pap.Ex)
  semi-Ex-H↑-Φ =
    zeroP-both (Pap.Ex • Pap.H Pap.↑) (Pap.H Pap.↓ • Pap.Ex)
               (zeroP-Ex , zeroP-H↑) (zeroP-H↓ , zeroP-Ex)

  ------------------------------------------------------------------
  -- Two rules that DO mention S
  --
  -- Neither needs the ½·sform of an S computed.  In each the S-part is a
  -- single letter sitting next to Pauli-free material, so `fa` vanishes
  -- for want of a Pauli on one side, and the letter contributes no
  -- phase of its own.

  private
    P-Ex : P⟦ Pap.Ex {m} ⟧ ≡ pIₙ
    P-Ex = proj₁ (zeroP (Pap.Ex {m}) zeroP-Ex)

    Φ-Ex : Φ (Pap.Ex {m}) ≡ ₀
    Φ-Ex = zeroP-Φ (Pap.Ex {m}) zeroP-Ex

  comm-CZ-S↑-Φ :
    Φ (Pap.CZ • Pap.S Pap.↑)
      ≡ corrℤ (QS.CR.srel (QS.CB.comm-CZ-S↑ {m})) + Φ (Pap.S Pap.↑ • Pap.CZ)
  comm-CZ-S↑-Φ =
    Φ-both-zero (Pap.CZ • Pap.S Pap.↑) (Pap.S Pap.↑ • Pap.CZ)
      (Eq.trans (Φ-•-freeˡ Pap.CZ (Pap.S Pap.↑) zeroP-CZ (Φ-gate _))
                (Φ-gate _))
      (Eq.trans (Φ-•-freeʳ (Pap.S Pap.↑) Pap.CZ zeroP-CZ (Φ-gate _))
                (Φ-gate _))

  semi-Ex-S↑-Φ :
    Φ (Pap.Ex • Pap.S Pap.↑)
      ≡ corrℤ (QS.CR.srel (QS.CB.semi-Ex-S↑ {m})) + Φ (Pap.S Pap.↓ • Pap.Ex)
  semi-Ex-S↑-Φ =
    Φ-both-zero (Pap.Ex • Pap.S Pap.↑) (Pap.S Pap.↓ • Pap.Ex)
      (Eq.trans (Φ-•-freeˡ (Pap.Ex {m}) (Pap.S Pap.↑) P-Ex Φ-Ex) (Φ-gate _))
      (Eq.trans (Φ-•-freeʳ (Pap.S Pap.↓) (Pap.Ex {m}) P-Ex Φ-Ex) (Φ-gate _))

  ------------------------------------------------------------------
  -- ... and one whose S-part is not even a single letter
  --
  -- semi-M↑CZ moves the multiplier word XMg past a CZ-power.  Whatever
  -- phase XMg ↑ carries — and it is not zero — it is the SAME block on
  -- both sides, and everything else is Pauli-free, so the two sides
  -- agree without that phase ever being computed.

  private
    zeroP-CZ^g : ZeroP (Pap.CZ^ {m} g)
    zeroP-CZ^g = zeroP-^ Pap.CZ zeroP-CZ (toℕ g)

    P-CZ^g : P⟦ Pap.CZ^ {m} g ⟧ ≡ pIₙ
    P-CZ^g = proj₁ (zeroP (Pap.CZ^ {m} g) zeroP-CZ^g)

    Φ-CZ^g : Φ (Pap.CZ^ {m} g) ≡ ₀
    Φ-CZ^g = proj₂ (zeroP (Pap.CZ^ {m} g) zeroP-CZ^g)

  semi-M↑CZ-Φ :
    Φ (QS.CR.XMg Pap.↑ • Pap.CZ^ g)
      ≡ corrℤ (QS.CR.srel (QS.CB.semi-M↑CZ {m}))
        + Φ (Pap.CZ • QS.CR.XMg Pap.↑)
  semi-M↑CZ-Φ =
    Φ-both-eq (QS.CR.XMg Pap.↑ • Pap.CZ^ g) (Pap.CZ • QS.CR.XMg Pap.↑)
              (Φ (QS.CR.XMg {m} Pap.↑))
      (Φ-•-freeʳ (QS.CR.XMg Pap.↑) (Pap.CZ^ g) P-CZ^g Φ-CZ^g)
      (Φ-•-freeˡ Pap.CZ (QS.CR.XMg Pap.↑) zeroP-CZ (Φ-gate _))

-- The three-wire rules.  Note Rules₂ (₁₊ m) opens the SAME Width — it
-- is Width (₂₊ (₁₊ m)) = Width (₃₊ m) — so its Ex is reusable here as
-- the unshifted one.  Every `ZeroP` proof names its gate: `ZeroP`
-- computes, so a bare `refl` would leave the gate an unsolved meta.

module Rules₃ (m : ℕ) where

  open Width (₃₊ m)

  private
    module R₂ = Rules₂ (₁₊ m)

  -- The single letters, each still Pauli-free after shifting.
  zeroP-CZ : ZeroP (Pap.CZ {₁₊ m})
  zeroP-CZ = Eq.refl

  zeroP-CZ↑ : ZeroP (Pap.CZ Pap.↑)
  zeroP-CZ↑ = Eq.refl

  zeroP-H↓↑ : ZeroP ((Pap.H Pap.↓) Pap.↑)
  zeroP-H↓↑ = Eq.refl

  zeroP-H↑↑ : ZeroP ((Pap.H Pap.↑) Pap.↑)
  zeroP-H↑↑ = Eq.refl

  -- Ex on the bottom two wires is Rules₂'s; shifted it is the same nine
  -- letters, each one wire up.
  zeroP-Ex↓ : ZeroP (Pap.Ex Pap.↓)
  zeroP-Ex↓ = R₂.zeroP-Ex

  zeroP-Ex↑ : ZeroP (Pap.Ex Pap.↑)
  zeroP-Ex↑ = zeroP-CZ↑ , zeroP-H↓↑ , zeroP-H↑↑
            , zeroP-CZ↑ , zeroP-H↓↑ , zeroP-H↑↑
            , zeroP-CZ↑ , zeroP-H↓↑ , zeroP-H↑↑

  zeroP-CX↑ : ZeroP (Pap.CX Pap.↑)
  zeroP-CX↑ = zeroP-^ ((Pap.H Pap.↓) Pap.↑) zeroP-H↓↑ 3
            , zeroP-CZ↑ , zeroP-H↓↑

  zeroP-CZ02 : ZeroP (Pap.CZ02 {m})
  zeroP-CZ02 = zeroP-Ex↓ , zeroP-CZ↑ , zeroP-Ex↓

  yang-baxter-Φ :
    Φ (Pap.Ex Pap.↑ • Pap.Ex Pap.↓ • Pap.Ex Pap.↑)
      ≡ corrℤ (QS.CR.srel (QS.CB.yang-baxter {m}))
        + Φ (Pap.Ex Pap.↓ • Pap.Ex Pap.↑ • Pap.Ex Pap.↓)
  yang-baxter-Φ =
    zeroP-both (Pap.Ex Pap.↑ • Pap.Ex Pap.↓ • Pap.Ex Pap.↑)
               (Pap.Ex Pap.↓ • Pap.Ex Pap.↑ • Pap.Ex Pap.↓)
               (zeroP-Ex↑ , zeroP-Ex↓ , zeroP-Ex↑)
               (zeroP-Ex↓ , zeroP-Ex↑ , zeroP-Ex↓)

  cz-slide-Φ :
    Φ (Pap.Ex Pap.↓ • Pap.Ex Pap.↑ • Pap.CZ {₁₊ m})
      ≡ corrℤ (QS.CR.srel (QS.CB.cz-slide {m}))
        + Φ (Pap.CZ Pap.↑ • Pap.Ex Pap.↓ • Pap.Ex Pap.↑)
  cz-slide-Φ =
    zeroP-both (Pap.Ex Pap.↓ • Pap.Ex Pap.↑ • Pap.CZ {₁₊ m})
               (Pap.CZ Pap.↑ • Pap.Ex Pap.↓ • Pap.Ex Pap.↑)
               (zeroP-Ex↓ , zeroP-Ex↑ , zeroP-CZ)
               (zeroP-CZ↑ , zeroP-Ex↓ , zeroP-Ex↑)

  semi-CX↑-CZ↓-Φ :
    Φ (Pap.CZ {₁₊ m} Pap.↓ • Pap.CX Pap.↑)
      ≡ corrℤ (QS.CR.srel (QS.CB.semi-CX↑-CZ↓ {m}))
        + Φ (Pap.CZ02 • Pap.CX Pap.↑ • Pap.CZ {₁₊ m} Pap.↓)
  semi-CX↑-CZ↓-Φ =
    zeroP-both (Pap.CZ {₁₊ m} Pap.↓ • Pap.CX Pap.↑)
               (Pap.CZ02 • Pap.CX Pap.↑ • Pap.CZ {₁₊ m} Pap.↓)
               (zeroP-CZ , zeroP-CX↑)
               (zeroP-CZ02 , zeroP-CX↑ , zeroP-CZ)

------------------------------------------------------------------------
-- cong↑ : shifting a circuit does not change its phase
--
-- The cocycle term is ½·sform of two Paulis that have both gained a
-- trivial bottom wire, and sform ignores a wire where both arguments
-- are trivial.  So the whole recursion goes through unchanged.

fa-↑ : (u v : QS.Circuit n) →
       FE.Weyl.fa (₁₊ n) (u Pap.↑) (v Pap.↑) ≡ FE.Weyl.fa n u v
fa-↑ {n} u v = Eq.cong (Sem.1/2 *_) inner
  where
  -- The right Pauli, shifted and then transported by the shifted
  -- symplectic part, is the transported one with a trivial wire added.
  step : ap (SH.Sᵂ (u Pap.↑)) (SH.Pᵂ (v Pap.↑))
           ≡ pI ∷ ap (SH.Sᵂ u) (SH.Pᵂ v)
  step = Eq.trans (Eq.cong (ap (SH.Sᵂ (u Pap.↑))) (proj₁ (SH.⟦⟧-↑ v)))
                  (proj₂ (SH.⟦⟧-↑ u) (pI ∷ SH.Pᵂ v))

  inner : sform (SH.Pᵂ (u Pap.↑)) (ap (SH.Sᵂ (u Pap.↑)) (SH.Pᵂ (v Pap.↑)))
            ≡ sform (SH.Pᵂ u) (ap (SH.Sᵂ u) (SH.Pᵂ v))
  inner =
    Eq.trans (Eq.cong₂ sform (proj₁ (SH.⟦⟧-↑ u)) step)
      (Eq.trans (Eq.cong (_+ sform (SH.Pᵂ u) (ap (SH.Sᵂ u) (SH.Pᵂ v)))
                         (Sem.sform1-pIˡ pI))
                (+-identityˡ (sform (SH.Pᵂ u) (ap (SH.Sᵂ u) (SH.Pᵂ v)))))

Φ-↑ : (w : QS.Circuit n) → Width.Φ (₁₊ n) (w Pap.↑) ≡ Width.Φ n w
Φ-↑ {n} [ a ]ʷ =
  Eq.trans (Width.Φ-gate (₁₊ n) _) (Eq.sym (Width.Φ-gate n a))
Φ-↑ {n} ε = Eq.trans (Width.Φ-ε (₁₊ n)) (Eq.sym (Width.Φ-ε n))
Φ-↑ {n} (u • v) =
  Eq.trans (Width.Φ-• (₁₊ n) (u Pap.↑) (v Pap.↑))
    (Eq.trans (Eq.cong₂ _+_ (Eq.cong₂ _+_ (Φ-↑ u) (Φ-↑ v)) (fa-↑ u v))
              (Eq.sym (Width.Φ-• n u v)))

------------------------------------------------------------------------
-- comm₁ : a bottom gate commutes with a shifted one
--
-- Both cocycle terms vanish, and for the same reason read in the two
-- orders: the shifted circuit's Pauli lives above wire 0 (SemShift's
-- shift lemma) and the bottom gate's lives on it (bottom-locality), so
-- sform pairs a trivial side against a non-trivial one at every wire.
-- The symplectic parts cooperate: a shifted map fixes wire 0, a bottom
-- gate fixes everything above it.

private
  comm₁-fa₁ : (h : Pap.SympGate 1) (g : QS.Gen n) →
              FE.Weyl.fa (₁₊ n) ([ g ]ʷ Pap.↑) [ Pap.gate₁ h ]ʷ ≡ ₀
  comm₁-fa₁ {n} h g =
    Eq.trans (Eq.cong (Sem.1/2 *_) inner) (*-zeroʳ Sem.1/2)
    where
    q : Pauli1
    q = proj₁ (proj₁ (SH.gate₁-bot h))

    -- The bottom gate's Pauli, transported by the shifted circuit,
    -- stays on wire 0: the shift acts as the identity there.
    step : ap (SH.Sᵂ ([ g ]ʷ Pap.↑)) (SH.Pᵂ {₁₊ n} [ Pap.gate₁ h ]ʷ)
             ≡ q ∷ pIₙ
    step = Eq.trans (Eq.cong (ap (SH.Sᵂ ([ g ]ʷ Pap.↑)))
                             (proj₂ (proj₁ (SH.gate₁-bot h))))
             (Eq.trans (proj₂ (SH.⟦⟧-↑ [ g ]ʷ) (q ∷ pIₙ))
                       (Eq.cong (q ∷_) (Sem.ap-ε (SH.Sᵂ [ g ]ʷ))))

    inner : sform (SH.Pᵂ ([ g ]ʷ Pap.↑))
                  (ap (SH.Sᵂ ([ g ]ʷ Pap.↑)) (SH.Pᵂ {₁₊ n} [ Pap.gate₁ h ]ʷ))
              ≡ ₀
    inner = Eq.trans (Eq.cong₂ sform (proj₁ (SH.⟦⟧-↑ [ g ]ʷ)) step)
                     (SH.sform-top-bot (SH.Pᵂ [ g ]ʷ) q)

  comm₁-fa₂ : (h : Pap.SympGate 1) (g : QS.Gen n) →
              FE.Weyl.fa (₁₊ n) [ Pap.gate₁ h ]ʷ ([ g ]ʷ Pap.↑) ≡ ₀
  comm₁-fa₂ {n} h g =
    Eq.trans (Eq.cong (Sem.1/2 *_) inner) (*-zeroʳ Sem.1/2)
    where
    q : Pauli1
    q = proj₁ (proj₁ (SH.gate₁-bot h))

    -- The shifted circuit's Pauli, transported by the bottom gate,
    -- stays above wire 0.
    step : ap (SH.Sᵂ {₁₊ n} [ Pap.gate₁ h ]ʷ) (SH.Pᵂ ([ g ]ʷ Pap.↑))
             ≡ pI ∷ SH.Pᵂ [ g ]ʷ
    step = Eq.trans (Eq.cong (ap (SH.Sᵂ {₁₊ n} [ Pap.gate₁ h ]ʷ))
                             (proj₁ (SH.⟦⟧-↑ [ g ]ʷ)))
                    (proj₂ (SH.gate₁-bot h) (SH.Pᵂ [ g ]ʷ))

    inner : sform (SH.Pᵂ {₁₊ n} [ Pap.gate₁ h ]ʷ)
                  (ap (SH.Sᵂ {₁₊ n} [ Pap.gate₁ h ]ʷ) (SH.Pᵂ ([ g ]ʷ Pap.↑)))
              ≡ ₀
    inner = Eq.trans (Eq.cong₂ sform (proj₂ (proj₁ (SH.gate₁-bot h))) step)
                     (SH.sform-bot-top q (SH.Pᵂ [ g ]ʷ))

  -- ... so each side's phase is zero, and the rule carries no
  -- correction.
  comm₁-Φ : (h : Pap.SympGate 1) (g : QS.Gen n) →
            Width.Φ (₁₊ n) ([ g ]ʷ Pap.↑ • [ Pap.gate₁ h ]ʷ)
              ≡ ₀ + Width.Φ (₁₊ n) ([ Pap.gate₁ h ]ʷ • [ g ]ʷ Pap.↑)
  comm₁-Φ {n} h g =
    Width.Φ-both-zero (₁₊ n) _ _
      (Eq.trans (Width.Φ-• (₁₊ n) ([ g ]ʷ Pap.↑) [ Pap.gate₁ h ]ʷ)
        (Eq.trans (Eq.cong₂ _+_
                    (Eq.cong₂ _+_ (Width.Φ-gate (₁₊ n) _)
                                  (Width.Φ-gate (₁₊ n) (Pap.gate₁ h)))
                    (comm₁-fa₁ h g))
                  (Eq.trans (+-identityʳ (₀ + ₀)) (+-identityʳ ₀))))
      (Eq.trans (Width.Φ-• (₁₊ n) [ Pap.gate₁ h ]ʷ ([ g ]ʷ Pap.↑))
        (Eq.trans (Eq.cong₂ _+_
                    (Eq.cong₂ _+_ (Width.Φ-gate (₁₊ n) (Pap.gate₁ h))
                                  (Width.Φ-gate (₁₊ n) _))
                    (comm₁-fa₂ h g))
                  (Eq.trans (+-identityʳ (₀ + ₀)) (+-identityʳ ₀))))

------------------------------------------------------------------------
-- comm₂ : the same, two wires down
--
-- Identical in shape; the shift lemma is applied twice and the bottom
-- gate is the two-wire one.

private
  comm₂-fa₁ : (h : Pap.SympGate 2) (g : QS.Gen n) →
              FE.Weyl.fa (₂₊ n) (([ g ]ʷ Pap.↑) Pap.↑) [ Pap.gate₂ h ]ʷ ≡ ₀
  comm₂-fa₁ {n} h g =
    Eq.trans (Eq.cong (Sem.1/2 *_) inner) (*-zeroʳ Sem.1/2)
    where
    q  = proj₁ (proj₁ (SH.gate₂-bot h))
    q' = proj₁ (proj₂ (proj₁ (SH.gate₂-bot h)))

    P↑↑ : SH.Pᵂ (([ g ]ʷ Pap.↑) Pap.↑) ≡ pI ∷ pI ∷ SH.Pᵂ [ g ]ʷ
    P↑↑ = Eq.trans (proj₁ (SH.⟦⟧-↑ ([ g ]ʷ Pap.↑)))
                   (Eq.cong (pI ∷_) (proj₁ (SH.⟦⟧-↑ [ g ]ʷ)))

    step : ap (SH.Sᵂ (([ g ]ʷ Pap.↑) Pap.↑))
              (SH.Pᵂ {₂₊ n} [ Pap.gate₂ h ]ʷ)
             ≡ q ∷ q' ∷ pIₙ
    step = Eq.trans (Eq.cong (ap (SH.Sᵂ (([ g ]ʷ Pap.↑) Pap.↑)))
                             (proj₂ (proj₂ (proj₁ (SH.gate₂-bot h)))))
             (Eq.trans (proj₂ (SH.⟦⟧-↑ ([ g ]ʷ Pap.↑)) (q ∷ q' ∷ pIₙ))
               (Eq.trans (Eq.cong (q ∷_)
                                  (proj₂ (SH.⟦⟧-↑ [ g ]ʷ) (q' ∷ pIₙ)))
                         (Eq.cong (λ z → q ∷ q' ∷ z)
                                  (Sem.ap-ε (SH.Sᵂ [ g ]ʷ)))))

    inner : sform (SH.Pᵂ (([ g ]ʷ Pap.↑) Pap.↑))
                  (ap (SH.Sᵂ (([ g ]ʷ Pap.↑) Pap.↑))
                      (SH.Pᵂ {₂₊ n} [ Pap.gate₂ h ]ʷ))
              ≡ ₀
    inner = Eq.trans (Eq.cong₂ sform P↑↑ step)
                     (SH.sform-top-bot₂ (SH.Pᵂ [ g ]ʷ) q q')

  comm₂-fa₂ : (h : Pap.SympGate 2) (g : QS.Gen n) →
              FE.Weyl.fa (₂₊ n) [ Pap.gate₂ h ]ʷ (([ g ]ʷ Pap.↑) Pap.↑) ≡ ₀
  comm₂-fa₂ {n} h g =
    Eq.trans (Eq.cong (Sem.1/2 *_) inner) (*-zeroʳ Sem.1/2)
    where
    q  = proj₁ (proj₁ (SH.gate₂-bot h))
    q' = proj₁ (proj₂ (proj₁ (SH.gate₂-bot h)))

    P↑↑ : SH.Pᵂ (([ g ]ʷ Pap.↑) Pap.↑) ≡ pI ∷ pI ∷ SH.Pᵂ [ g ]ʷ
    P↑↑ = Eq.trans (proj₁ (SH.⟦⟧-↑ ([ g ]ʷ Pap.↑)))
                   (Eq.cong (pI ∷_) (proj₁ (SH.⟦⟧-↑ [ g ]ʷ)))

    step : ap (SH.Sᵂ {₂₊ n} [ Pap.gate₂ h ]ʷ)
              (SH.Pᵂ (([ g ]ʷ Pap.↑) Pap.↑))
             ≡ pI ∷ pI ∷ SH.Pᵂ [ g ]ʷ
    step = Eq.trans (Eq.cong (ap (SH.Sᵂ {₂₊ n} [ Pap.gate₂ h ]ʷ)) P↑↑)
                    (proj₂ (SH.gate₂-bot h) (SH.Pᵂ [ g ]ʷ))

    inner : sform (SH.Pᵂ {₂₊ n} [ Pap.gate₂ h ]ʷ)
                  (ap (SH.Sᵂ {₂₊ n} [ Pap.gate₂ h ]ʷ)
                      (SH.Pᵂ (([ g ]ʷ Pap.↑) Pap.↑)))
              ≡ ₀
    inner = Eq.trans
              (Eq.cong₂ sform (proj₂ (proj₂ (proj₁ (SH.gate₂-bot h)))) step)
              (SH.sform-bot-top₂ q q' (SH.Pᵂ [ g ]ʷ))

  comm₂-Φ : (h : Pap.SympGate 2) (g : QS.Gen n) →
            Width.Φ (₂₊ n) (([ g ]ʷ Pap.↑) Pap.↑ • [ Pap.gate₂ h ]ʷ)
              ≡ ₀ + Width.Φ (₂₊ n) ([ Pap.gate₂ h ]ʷ • ([ g ]ʷ Pap.↑) Pap.↑)
  comm₂-Φ {n} h g =
    Width.Φ-both-zero (₂₊ n) _ _
      (Eq.trans (Width.Φ-• (₂₊ n) (([ g ]ʷ Pap.↑) Pap.↑) [ Pap.gate₂ h ]ʷ)
        (Eq.trans (Eq.cong₂ _+_
                    (Eq.cong₂ _+_ (Width.Φ-gate (₂₊ n) _)
                                  (Width.Φ-gate (₂₊ n) (Pap.gate₂ h)))
                    (comm₂-fa₁ h g))
                  (Eq.trans (+-identityʳ (₀ + ₀)) (+-identityʳ ₀))))
      (Eq.trans (Width.Φ-• (₂₊ n) [ Pap.gate₂ h ]ʷ (([ g ]ʷ Pap.↑) Pap.↑))
        (Eq.trans (Eq.cong₂ _+_
                    (Eq.cong₂ _+_ (Width.Φ-gate (₂₊ n) (Pap.gate₂ h))
                                  (Width.Φ-gate (₂₊ n) _))
                    (comm₂-fa₂ h g))
                  (Eq.trans (+-identityʳ (₀ + ₀)) (+-identityʳ ₀))))

------------------------------------------------------------------------
-- What is left, after cong↑
--
-- Φ-Corr is an induction over the RELATION, not a list of independent
-- equations: its cong↑ case needs the statement one wire down.  Peeling
-- that case off with Φ-↑ leaves the sixteen base rules and the two
-- commutation rules, at every width.
--
-- The commutation cases are isolated by `IsComm` rather than by naming
-- the gate type, which is a module parameter of the circuit framework.

IsComm : ∀ {u v} → QS.CR._QRel,_===_ m u v → Set
IsComm (QS.CR.srel _)    = ⊥
IsComm (QS.CR.cong↑ _)   = ⊥
IsComm (QS.CR.comm₁ h g) = ⊤
IsComm (QS.CR.comm₂ h g) = ⊤

-- The sixteen, at every width.
SRel-Φ : Set
SRel-Φ = ∀ {n} {u v : QS.Circuit n} (r : QS.CB._SRel,_===_ n u v) →
         Width.Φ n u ≡ srel-corrℤ r + Width.Φ n v

-- ... and the two commutation rules, which carry no correction.
Comm-Φ : Set
Comm-Φ = ∀ {n} {u v : QS.Circuit n} (r : QS.CR._QRel,_===_ n u v) →
         IsComm r → Width.Φ n u ≡ ₀ + Width.Φ n v

-- ... and Comm-Φ is now a theorem: the two commutation rules are
-- comm₁-Φ and comm₂-Φ, and the other two constructors are ruled out by
-- IsComm.
comm-Φ : Comm-Φ
comm-Φ (QS.CR.srel _)     ()
comm-Φ (QS.CR.cong↑ _)    ()
comm-Φ (QS.CR.comm₁ h g)  _ = comm₁-Φ h g
comm-Φ (QS.CR.comm₂ h g)  _ = comm₂-Φ h g

Φ-Corr-from : SRel-Φ → Comm-Φ → ∀ n → Width.Φ-Corr n
Φ-Corr-from sr cm n (QS.CR.srel r)    = sr r
Φ-Corr-from sr cm n (QS.CR.comm₁ h g) = cm (QS.CR.comm₁ h g) tt
Φ-Corr-from sr cm n (QS.CR.comm₂ h g) = cm (QS.CR.comm₂ h g) tt
Φ-Corr-from sr cm (₁₊ n) (QS.CR.cong↑ {w = u} {v = v} r) =
  Eq.trans (Φ-↑ u)
    (Eq.trans (Φ-Corr-from sr cm n r)
              (Eq.cong (corrℤ r +_) (Eq.sym (Φ-↑ v))))

------------------------------------------------------------------------
-- The reduction
--
-- Realises for SemFE's generator data — the last hypothesis of
-- Clifford.Qupit.Presentation — follows from Φ-Corr at that width.

realises : ∀ (n : ℕ) → Width.Φ-Corr n → PE.Realises n (FE.generator-data n)
realises = Width.realises

-- ... and Φ-Corr, at every width, from the eighteen remaining equations.
realises-from : SRel-Φ → Comm-Φ →
                ∀ n → PE.Realises n (FE.generator-data n)
realises-from sr cm n = realises n (Φ-Corr-from sr cm n)

-- With cong↑, comm₁ and comm₂ all discharged, the SIXTEEN Paper-V0
-- rules are the whole of what is left.
Φ-Corr-srel : SRel-Φ → ∀ n → Width.Φ-Corr n
Φ-Corr-srel sr = Φ-Corr-from sr comm-Φ

realises-srel : SRel-Φ → ∀ n → PE.Realises n (FE.generator-data n)
realises-srel sr n = realises n (Φ-Corr-srel sr n)


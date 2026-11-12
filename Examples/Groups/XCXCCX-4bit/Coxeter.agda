------------------------------------------------------------------------
-- Presentations of groups
--
-- Permutations of N basis states as circuits, and the frame lemma
--
-- Examples.Groups.Symmetric.CoxeterFrames for any number N of states
-- (it fixes N = 8).  A Coxeter word is a circuit of the presentation of
-- S_N (Examples.Groups.Symmetric), whose wires are read here as basis
-- states: its generator on d, d + 1 is the transposition of the states
-- d, d + 1, which a circuit T d over any alphabet realises (Circuits T).
-- Given the Coxeter relations for the circuits T d (Coxeter), two
-- Coxeter words with the same permutation have equivalent circuits
-- (perm-complete), and a circuit that the T i with i ≥ j commute with,
-- conjugated by a Coxeter word, depends only on where the word sends
-- the states below j (frame≈).  The width-independent part (actions,
-- inverses, cycles, frames) is CoxeterFrames' own.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.XCXCCX-4bit.Coxeter (N : ℕ) where

open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Fin.Permutation as P using (_⟨$⟩ʳ_ ; inverseʳ)
open import Data.Nat.Base using (zero ; suc ; _+_ ; _≤_ ; _<_ ; z≤n ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Definitions using (_IsPresentationOf_)
open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
import Relation.Binary.Reasoning.Setoid as SR

import Examples.Groups.Symmetric.Syntactics as Sym
import Examples.Groups.Symmetric.Semantics as SymSem
import Examples.Groups.Symmetric.Interpretation as SymI
import Examples.Groups.Symmetric.Presentation as SymP
import Examples.Groups.Symmetric.Surjectivity as SymS
open Sym using (gate₀ ; gate₁ ; gate₂ ; _↥ ; σ-gate ; _VRel,_===_ ; srel ; cong↑ ; comm₁ ; comm₂ ; ω↑=ω)

open import Examples.Groups.Symmetric.CoxeterFrames public
  using ( SG ; tr ; tr-≥ ; tr-≤ ; inv ; actₙ ; act-• ; ˡ⇒ʳ ; act-inv ; inv-inv ; act-inv′
        ; liftN ; liftN-cong ; stripN ; liftW ; strip-ok ; ⟦liftW⟧
        ; act-↑-0 ; act-↑-suc ; cyc ; cyc-0 ; cyc-suc
        ; Avoid ; Distinct ; outs ; frame ; _‼_ ; frame-act )

private
  variable
    n : ℕ

-- Words of S_N's circuit presentation.
CW : Set
CW = Word (SG N)

act : CW → Fin N → Fin N
act = actₙ

private
  -- o + (c + m) ≤ N gives c + o ≤ N.
  bound : ∀ o m c → o + (c + m) ≤ N → c + o ≤ N
  bound o m c p =
    ℕP.≤-trans (ℕP.≤-reflexive (ℕP.+-comm c o)) (ℕP.≤-trans (ℕP.+-monoʳ-≤ o (ℕP.m≤m+n c m)) p)

  ss : ∀ o n → o + suc (suc n) ≡ suc (suc (o + n))
  ss o n = Eq.trans (ℕP.+-suc o (suc n)) (Eq.cong suc (ℕP.+-suc o n))

------------------------------------------------------------------------
-- Coxeter words as circuits

module Circuits {A : Set} (T : ℕ → Word A) where

  -- A Coxeter word read as a circuit, its states shifted up by o.
  Pc : ℕ → Word (SG n) → Word A
  Pc o [ g ]ʷ   = T (tr o g)
  Pc o ε       = ε
  Pc o (u • v) = Pc o u • Pc o v

  Pc-↑ : (o : ℕ) (w : Word (SG n)) → Pc o (w Sym.↑) ≡ Pc (suc o) w
  Pc-↑ o [ g ]ʷ   = Eq.refl
  Pc-↑ o ε       = Eq.refl
  Pc-↑ o (u • v) = Eq.cong₂ _•_ (Pc-↑ o u) (Pc-↑ o v)

  Pc-liftW : (j : ℕ) {m : ℕ} (o : ℕ) (w : Word (SG m)) → Pc o (liftW j w) ≡ Pc (j + o) w
  Pc-liftW zero    o w = Eq.refl
  Pc-liftW (suc j) o w = Eq.trans (Pc-↑ o (liftW j w)) (Eq.trans (Pc-liftW j (suc o) w)
    (Eq.cong (λ z → Pc z w) (ℕP.+-suc j o)))

  -- The Coxeter relations for the circuits T d, d + 1 < N.
  module _ (Γ : WRel A) where

    open PB Γ

    record Coxeter : Set where
      field
        order : ∀ i → 2 + i ≤ N → T i • T i ≈ ε
        braid : ∀ i → 3 + i ≤ N → T i • T (suc i) • T i ≈ T (suc i) • T i • T (suc i)
        far   : ∀ i j → 2 + i ≤ j → 2 + j ≤ N → T i • T j ≈ T j • T i

  module Transfer {Γ : WRel A} (cox : Coxeter Γ) where

    open PB Γ
    open Coxeter cox

    -- The relations of S_N's circuit presentation hold for the circuits.
    Pc-ax : ∀ {n w v} (o : ℕ) → o + n ≤ N → n VRel, w === v → Pc o w ≈ Pc o v
    Pc-ax {suc (suc m)} o b (srel Sym.order) = order o (bound o m 2 b)
    Pc-ax {suc (suc (suc m))} o b (srel Sym.yang-baxter) = braid o (bound o m 3 b)
    Pc-ax {suc n} {w = w} {v} o b (cong↑ {w = w′} {v = v′} a) =
      Eq.subst₂ _≈_ (Eq.sym (Pc-↑ o w′)) (Eq.sym (Pc-↑ o v′))
        (Pc-ax (suc o) (Eq.subst (_≤ N) (ℕP.+-suc o n) b) a)
    Pc-ax o b (comm₁ () g)
    Pc-ax {suc (suc n)} o b (comm₂ σ-gate g) = sym (far o j lo hi)
      where
      j = tr (suc (suc o)) g
      lo : 2 + o ≤ j
      lo = tr-≥ (suc (suc o)) g
      hi : 2 + j ≤ N
      hi = ℕP.≤-trans (tr-≤ (suc (suc o)) g) (Eq.subst (_≤ N) (ss o n) b)
    Pc-ax o b (ω↑=ω ())

    Pc-cong : ∀ {n} {w v : Word (SG n)} (o : ℕ) → o + n ≤ N → PB._≈_ (n VRel,_===_) w v → Pc o w ≈ Pc o v
    Pc-cong o b PB.refl        = refl
    Pc-cong o b (PB.sym h)     = sym (Pc-cong o b h)
    Pc-cong o b (PB.trans h g) = trans (Pc-cong o b h) (Pc-cong o b g)
    Pc-cong o b (PB.cong h g)  = cong (Pc-cong o b h) (Pc-cong o b g)
    Pc-cong o b PB.assoc       = assoc
    Pc-cong o b PB.left-unit   = left-unit
    Pc-cong o b PB.right-unit  = right-unit
    Pc-cong o b (PB.axiom a)   = Pc-ax o b a

  ----------------------------------------------------------------------
  -- Completeness for permutations, inverses, frames and stabilisers

  module Complete {Γ : WRel A} (cox : Coxeter Γ) where

    open Transfer cox public
    open PB Γ
    open Coxeter cox
    open SR (PP.word-setoid Γ)

    -- Two Coxeter words with the same permutation are equal circuits.
    perm-complete′ : {n : ℕ} → n ≤ N → (p q : Word (SG n)) →
                     (∀ i → SymI.⟦ p ⟧ ⟨$⟩ʳ i ≡ SymI.⟦ q ⟧ ⟨$⟩ʳ i) → Pc 0 p ≈ Pc 0 q
    perm-complete′ {n} b p q h = Pc-cong 0 b (IsGroupIsomorphism.injective iso {p} {q} h)
      where
      open _IsPresentationOf_ (SymP.presentation {n}) using (iso ; module GL)
      open GroupMorphisms (Group.rawGroup GL.•-ε-group) (Group.rawGroup (SymSem.Permutation′-group n))
        using (module IsGroupIsomorphism)

    perm-complete : (p q : CW) → (∀ x → act p x ≡ act q x) → Pc 0 p ≈ Pc 0 q
    perm-complete p q h = perm-complete′ ℕP.≤-refl p q (ˡ⇒ʳ SymI.⟦ p ⟧ SymI.⟦ q ⟧ h)

    -- A Coxeter word followed by its inverse.
    Pc-inv : ∀ {n} (o : ℕ) → o + n ≤ N → (p : Word (SG n)) → Pc o p • Pc o (inv p) ≈ ε
    Pc-inv o b [ g ]ʷ = order (tr o g) (ℕP.≤-trans (tr-≤ o g) b)
    Pc-inv o b ε       = left-unit
    Pc-inv o b (u • v) = begin
      (Pc o u • Pc o v) • (Pc o (inv v) • Pc o (inv u))   ≈⟨ assoc ⟩
      Pc o u • (Pc o v • (Pc o (inv v) • Pc o (inv u)))   ≈⟨ cong refl (sym assoc) ⟩
      Pc o u • ((Pc o v • Pc o (inv v)) • Pc o (inv u))   ≈⟨ cong refl (trans (cong (Pc-inv o b v) refl) left-unit) ⟩
      Pc o u • Pc o (inv u)                               ≈⟨ Pc-inv o b u ⟩
      ε                                                   ∎

    Pc-inv′ : ∀ {n} (o : ℕ) → o + n ≤ N → (p : Word (SG n)) → Pc o (inv p) • Pc o p ≈ ε
    Pc-inv′ o b p = Eq.subst (λ q → Pc o (inv p) • Pc o q ≈ ε) (inv-inv p) (Pc-inv o b (inv p))

    -- A circuit conjugated by a Coxeter word.
    Fr : Word A → CW → Word A
    Fr b p = Pc 0 p • b • Pc 0 (inv p)

    Fr-conj : (b : Word A) (r p : CW) → Pc 0 r • Fr b p • Pc 0 (inv r) ≈ Fr b (r • p)
    Fr-conj b r p = begin
      Pc 0 r • ((Pc 0 p • (b • Pc 0 (inv p))) • Pc 0 (inv r))   ≈⟨ cong refl assoc ⟩
      Pc 0 r • (Pc 0 p • ((b • Pc 0 (inv p)) • Pc 0 (inv r)))   ≈⟨ sym assoc ⟩
      (Pc 0 r • Pc 0 p) • ((b • Pc 0 (inv p)) • Pc 0 (inv r))   ≈⟨ cong refl assoc ⟩
      (Pc 0 r • Pc 0 p) • (b • (Pc 0 (inv p) • Pc 0 (inv r)))   ∎

    -- Circuits that every T i with i ≥ j commutes with.
    Comm≥ : ℕ → Word A → Set
    Comm≥ j b = ∀ i → j ≤ i → 2 + i ≤ N → T i • b ≈ b • T i

    comm-word : ∀ {j m} (b : Word A) → Comm≥ j b → j + m ≤ N → (w : Word (SG m)) → Pc j w • b ≈ b • Pc j w
    comm-word {j} b cb bd [ g ]ʷ = cb (tr j g) (tr-≥ j g) (ℕP.≤-trans (tr-≤ j g) bd)
    comm-word b cb bd ε = trans left-unit (sym right-unit)
    comm-word {j} b cb bd (u • v) = begin
      (Pc j u • Pc j v) • b   ≈⟨ assoc ⟩
      Pc j u • (Pc j v • b)   ≈⟨ cong refl (comm-word b cb bd v) ⟩
      Pc j u • (b • Pc j v)   ≈⟨ sym assoc ⟩
      (Pc j u • b) • Pc j v   ≈⟨ cong (comm-word b cb bd u) refl ⟩
      (b • Pc j u) • Pc j v   ≈⟨ assoc ⟩
      b • (Pc j u • Pc j v)   ∎

    -- A Coxeter word fixing the states below j commutes with b.
    stab : (j m : ℕ) → j + m ≤ N → (b : Word A) → Comm≥ j b → (r : Word (SG (j + m))) →
           (∀ x → toℕ x < j → actₙ r x ≡ x) → Pc 0 r • b ≈ b • Pc 0 r
    stab j m bd b cb r fix = begin
      Pc 0 r • b                     ≈⟨ cong r≈ refl ⟩
      Pc 0 (liftW j w′) • b          ≡⟨ Eq.cong (_• b) lw ⟩
      Pc j w′ • b                    ≈⟨ comm-word b cb bd w′ ⟩
      b • Pc j w′                    ≡⟨ Eq.cong (b •_) (Eq.sym lw) ⟩
      b • Pc 0 (liftW j w′)          ≈⟨ cong refl (sym r≈) ⟩
      b • Pc 0 r                     ∎
      where
      π = SymI.⟦ r ⟧
      fixʳ : ∀ x → toℕ x < j → π ⟨$⟩ʳ x ≡ x
      fixʳ x lt = Eq.trans (Eq.cong (π ⟨$⟩ʳ_) (Eq.sym (fix x lt))) (inverseʳ π)
      gw = SymS.go m (stripN j π)
      w′ = proj₁ gw
      lw : Pc 0 (liftW j w′) ≡ Pc j w′
      lw = Eq.trans (Pc-liftW j 0 w′) (Eq.cong (λ z → Pc z w′) (ℕP.+-identityʳ j))
      r≈ : Pc 0 r ≈ Pc 0 (liftW j w′)
      r≈ = perm-complete′ bd r (liftW j w′) λ i → Eq.sym (Eq.trans (⟦liftW⟧ j w′ i)
             (Eq.trans (liftN-cong j SymI.⟦ w′ ⟧ (stripN j π) (proj₂ gw) i) (strip-ok j π fixʳ i)))

    -- Frames: b conjugated by two Coxeter words that agree below j.
    frame≈ : (j m : ℕ) → j + m ≤ N → (b : Word A) → Comm≥ j b → (p q : Word (SG (j + m))) →
            (∀ x → toℕ x < j → actₙ p x ≡ actₙ q x) →
            Pc 0 p • b • Pc 0 (inv p) ≈ Pc 0 q • b • Pc 0 (inv q)
    frame≈ j m bd b cb p q h = begin
      Pc 0 p • b • Pc 0 (inv p)                                    ≈⟨ cong p≈ refl ⟩
      (Pc 0 q • Pc 0 r) • b • Pc 0 (inv p)                         ≈⟨ assoc ⟩
      Pc 0 q • (Pc 0 r • b • Pc 0 (inv p))                         ≈⟨ cong refl (sym assoc) ⟩
      Pc 0 q • ((Pc 0 r • b) • Pc 0 (inv p))                       ≈⟨ cong refl (cong (stab j m bd b cb r fix) refl) ⟩
      Pc 0 q • ((b • Pc 0 r) • Pc 0 (inv p))                       ≈⟨ cong refl assoc ⟩
      Pc 0 q • (b • (Pc 0 r • Pc 0 (inv p)))                       ≈⟨ cong refl (cong refl ip) ⟩
      Pc 0 q • b • Pc 0 (inv q)                                    ∎
      where
      r = inv q • p
      fix : ∀ x → toℕ x < j → actₙ r x ≡ x
      fix x lt = Eq.trans (Eq.cong (actₙ (inv q)) (h x lt)) (act-inv q x)
      p≈ : Pc 0 p ≈ Pc 0 q • Pc 0 r
      p≈ = begin
        Pc 0 p                                ≈⟨ sym left-unit ⟩
        ε • Pc 0 p                            ≈⟨ cong (sym (Pc-inv 0 bd q)) refl ⟩
        (Pc 0 q • Pc 0 (inv q)) • Pc 0 p      ≈⟨ assoc ⟩
        Pc 0 q • (Pc 0 (inv q) • Pc 0 p)      ∎
      ip : Pc 0 r • Pc 0 (inv p) ≈ Pc 0 (inv q)
      ip = begin
        (Pc 0 (inv q) • Pc 0 p) • Pc 0 (inv p)    ≈⟨ assoc ⟩
        Pc 0 (inv q) • (Pc 0 p • Pc 0 (inv p))    ≈⟨ cong refl (Pc-inv 0 bd p) ⟩
        Pc 0 (inv q) • ε                          ≈⟨ right-unit ⟩
        Pc 0 (inv q)                              ∎

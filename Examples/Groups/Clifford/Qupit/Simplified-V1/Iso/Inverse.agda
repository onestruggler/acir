{-# OPTIONS --safe --cubical-compatible #-}

open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; setoid) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_,_ ; proj₁ ; ∃)

open import Data.Nat hiding (_^_ ; _*_ ; _+_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _≤_)
open import Data.Bool hiding (_≤_)
open import Data.List hiding ([_])

open import Data.Maybe
open import Data.Sum using (inj₁ ; inj₂ ; [_,_])
open import Data.Unit using (tt)

open import Word.Base as WB hiding (wfoldl)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_)
open import Presentation.Tactic.Rewriting hiding ([_])

open import Data.Fin.Properties using (toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Data.Nat.Primality

open import Zp.ModularArithmetic
open import Zp.Fermats-little-theorem


module Examples.Groups.Clifford.Qupit.Simplified-V1.Iso.Inverse
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open import Examples.Groups.Clifford.Qupit.SemiDirect.Syntactics p-3 p-prime g* g-gen
open import Examples.Groups.Clifford.Qupit.Simplified-V1.Iso.Forward p-3 p-prime g* g-gen
open import Examples.Groups.Clifford.Qupit.Simplified-V1.LemmasCZ p-3 p-prime g* g-gen hiding (module CL ; module CLb)

import Examples.Groups.Symplectic.Simplified.Lemmas p-2 p-prime g* g-gen as NSimL
import Examples.Groups.Pauli.Presentation-Alt p-2 p-prime as XZ


module Iso-Inverse-Direction (n : ℕ) where

  open import Examples.Groups.Clifford.Qupit.Simplified-V1.Syntactics
    p-3 p-prime g* g-gen as Cli
  open import Examples.Groups.Clifford.Qupit.Simplified-V1.Lemmas
    p-3 p-prime g* g-gen
    using (module Lemmas1)
  open import Examples.Groups.Clifford.Qupit.Simplified-V1.LemmasXZ
    p-3 p-prime g* g-gen
    using (module Lemmas1b)

  open Clifford-Relations
  open Iso n

  lemma-h↑ : ∀ {m} (w : Word (Cli.Gen m)) -> (h ʷ) (w ↑) ≡ ((h ʷ) w) SemiDirect.↑
  lemma-h↑ [ x ]ʷ = Eq.refl
  lemma-h↑ ε = Eq.refl
  lemma-h↑ (u • v) = Eq.cong₂ _•_ (lemma-h↑ u) (lemma-h↑ v)

  lemma-w↑H : ∀ {m} (w : Word (SemiDirect.Gen (₁₊ m))) →
    let open PB (SemiDirect._QRel,_===_ (₂₊ m)) using (_≈_) in
    (w SemiDirect.↑) • SemiDirect.H ≈ SemiDirect.H • (w SemiDirect.↑)
  lemma-w↑H [ inj₁ xz ]ʷ = PB.sym (PB.axiom (mid (comm (xz XZ.↥) Sym.H-gen)))
  lemma-w↑H [ inj₂ sm ]ʷ = PB.axiom (right (Sim.comm₁ Sym.H-gate _))
  lemma-w↑H ε = PB.trans PB.left-unit (PB.sym PB.right-unit)
  lemma-w↑H (u • v) = PB.trans PB.assoc (PB.trans (PB.cong PB.refl (lemma-w↑H v)) (PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong (lemma-w↑H u) PB.refl) PB.assoc)))

  lemma-w↑↑CZ : ∀ {m} (w : Word (SemiDirect.Gen (₁₊ m))) →
    let open PB (SemiDirect._QRel,_===_ (₃₊ m)) using (_≈_) in
    (w SemiDirect.↑ SemiDirect.↑) • SemiDirect.CZ ≈ SemiDirect.CZ • (w SemiDirect.↑ SemiDirect.↑)
  lemma-w↑↑CZ [ inj₁ xz ]ʷ = PB.sym (PB.axiom (mid (comm (xz XZ.↥ XZ.↥) Sym.CZ-gen)))
  lemma-w↑↑CZ [ inj₂ sm ]ʷ = PB.axiom (right (Sim.comm₂ Sym.CZ-gate _))
  lemma-w↑↑CZ ε = PB.trans PB.left-unit (PB.sym PB.right-unit)
  lemma-w↑↑CZ (u • v) = PB.trans PB.assoc (PB.trans (PB.cong PB.refl (lemma-w↑↑CZ v)) (PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong (lemma-w↑↑CZ u) PB.refl) PB.assoc)))

  lemma-w↑S : ∀ {m} (w : Word (SemiDirect.Gen (₁₊ m))) →
    let open PB (SemiDirect._QRel,_===_ (₂₊ m)) using (_≈_) in
    (w SemiDirect.↑) • SemiDirect.S ≈ SemiDirect.S • (w SemiDirect.↑)
  lemma-w↑S [ inj₁ xz ]ʷ = PB.sym (PB.axiom (mid (comm (xz XZ.↥) Sym.S-gen)))
  lemma-w↑S [ inj₂ sm ]ʷ = PB.axiom (right (Sim.comm₁ Sym.S-gate _))
  lemma-w↑S ε = PB.trans PB.left-unit (PB.sym PB.right-unit)
  lemma-w↑S (u • v) = PB.trans PB.assoc (PB.trans (PB.cong PB.refl (lemma-w↑S v)) (PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong (lemma-w↑S u) PB.refl) PB.assoc)))

  lemma-w↑Z : ∀ {m} (w : Word (SemiDirect.Gen (₁₊ m))) →
    let open PB (SemiDirect._QRel,_===_ (₂₊ m)) using (_≈_) in
    (w SemiDirect.↑) • SemiDirect.Z ≈ SemiDirect.Z • (w SemiDirect.↑)
  lemma-w↑Z [ inj₁ xz ]ʷ = PB.axiom (left XZ.comm-Z)
  lemma-w↑Z [ inj₂ sm ]ʷ = PB.axiom (mid (comm XZ.Z-gen (sm Sym.↥)))
  lemma-w↑Z ε = PB.trans PB.left-unit (PB.sym PB.right-unit)
  lemma-w↑Z (u • v) = PB.trans PB.assoc (PB.trans (PB.cong PB.refl (lemma-w↑Z v)) (PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong (lemma-w↑Z u) PB.refl) PB.assoc)))

  lemma-w↑Zk : ∀ {m} (w : Word (SemiDirect.Gen (₁₊ m))) (k : ℕ) →
    let open PB (SemiDirect._QRel,_===_ (₂₊ m)) using (_≈_) in
    (w SemiDirect.↑) • (SemiDirect.Z ^ k) ≈ (SemiDirect.Z ^ k) • (w SemiDirect.↑)
  lemma-w↑Zk w 0 = PB.trans PB.right-unit (PB.sym PB.left-unit)
  lemma-w↑Zk w 1 = lemma-w↑Z w
  lemma-w↑Zk w (₂₊ k) = PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong (lemma-w↑Z w) PB.refl) (PB.trans PB.assoc (PB.trans (PB.cong PB.refl (lemma-w↑Zk w (₁₊ k))) (PB.sym PB.assoc))))

  lemma-CZ-Zk : ∀ {m} (k : ℕ) →
    let open PB (SemiDirect._QRel,_===_ (₂₊ m)) using (_≈_) in
    SemiDirect.CZ • (SemiDirect.Z ^ k) ≈ (SemiDirect.Z ^ k) • SemiDirect.CZ
  lemma-CZ-Zk 0 = PB.trans PB.right-unit (PB.sym PB.left-unit)
  lemma-CZ-Zk 1 = PB.axiom (mid (comm XZ.Z-gen Sym.CZ-gen))
  lemma-CZ-Zk (₂₊ k) = PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong (lemma-CZ-Zk 1) PB.refl) (PB.trans PB.assoc (PB.trans (PB.cong PB.refl (lemma-CZ-Zk (₁₊ k))) (PB.sym PB.assoc))))

  lemma-CZ-Z↑k : ∀ {m} (k : ℕ) →
    let open PB (SemiDirect._QRel,_===_ (₂₊ m)) using (_≈_) in
    SemiDirect.CZ • ((SemiDirect.Z ^ k) SemiDirect.↑) ≈ ((SemiDirect.Z ^ k) SemiDirect.↑) • SemiDirect.CZ
  lemma-CZ-Z↑k 0 = PB.trans PB.right-unit (PB.sym PB.left-unit)
  lemma-CZ-Z↑k 1 = PB.axiom (mid (comm (XZ.Z-gen XZ.↥) Sym.CZ-gen))
  lemma-CZ-Z↑k (₂₊ k) = PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong (lemma-CZ-Z↑k 1) PB.refl) (PB.trans PB.assoc (PB.trans (PB.cong PB.refl (lemma-CZ-Z↑k (₁₊ k))) (PB.sym PB.assoc))))

  -- The metaplectic correspondence: h maps Clifford's Mg to the Sim Mg.
  -- This is the single foundational obligation that the semi-M*/order-H/etc. cases reduce to.
  -- Building blocks for the metaplectic foundation h-Z : (h ʷ) Clifford.Z ≈ SemiDirect.Z.
  lemma-HX : ∀ {m} → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in SemiDirect.H • SemiDirect.X ≈ SemiDirect.Z • SemiDirect.H
  lemma-HX = PB.axiom (mid (comm XZ.X-gen Sym.H-gen))

  lemma-HZ : ∀ {m} → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in SemiDirect.H • SemiDirect.Z ≈ SemiDirect.X ^ p-1 • SemiDirect.H
  lemma-HZ {m} = begin
      SemiDirect.H • SemiDirect.Z       ≈⟨ axiom (mid (comm XZ.Z-gen Sym.H-gen)) ⟩
      [ XZ.X ^ p-1 ]ₗ • SemiDirect.H    ≡⟨ Eq.cong (_• SemiDirect.H) (SemiDirect.lemma-[]ₗ^k XZ.X p-1) ⟩
      SemiDirect.X ^ p-1 • SemiDirect.H ∎
    where
    open PB (SemiDirect._QRel,_===_ (₁₊ m))
    open PP (SemiDirect._QRel,_===_ (₁₊ m))
    open SR word-setoid

  lemma-HX^k : ∀ {m} (k : ℕ) → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in SemiDirect.H • SemiDirect.X ^ k ≈ SemiDirect.Z ^ k • SemiDirect.H
  lemma-HX^k 0 = PB.trans PB.right-unit (PB.sym PB.left-unit)
  lemma-HX^k 1 = lemma-HX
  lemma-HX^k (₂₊ k) = PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong lemma-HX PB.refl) (PB.trans PB.assoc (PB.trans (PB.cong PB.refl (lemma-HX^k (₁₊ k))) (PB.sym PB.assoc))))

  cSX : ∀ {m} → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in SemiDirect.S • SemiDirect.X ≈ (SemiDirect.X • SemiDirect.Z) • SemiDirect.S
  cSX = PB.axiom (mid (comm XZ.X-gen Sym.S-gen))

  lemma-SX^k : ∀ {m} (j : ℕ) → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in SemiDirect.S • SemiDirect.X ^ j ≈ (SemiDirect.X • SemiDirect.Z) ^ j • SemiDirect.S
  lemma-SX^k 0 = PB.trans PB.right-unit (PB.sym PB.left-unit)
  lemma-SX^k 1 = cSX
  lemma-SX^k (₂₊ j) = PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong cSX PB.refl) (PB.trans PB.assoc (PB.trans (PB.cong PB.refl (lemma-SX^k (₁₊ j))) (PB.sym PB.assoc))))

  lemma-HZ^k : ∀ {m} (j : ℕ) → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in SemiDirect.H • SemiDirect.Z ^ j ≈ (SemiDirect.X ^ p-1) ^ j • SemiDirect.H
  lemma-HZ^k 0 = PB.trans PB.right-unit (PB.sym PB.left-unit)
  lemma-HZ^k 1 = lemma-HZ
  lemma-HZ^k (₂₊ j) = PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong lemma-HZ PB.refl) (PB.trans PB.assoc (PB.trans (PB.cong PB.refl (lemma-HZ^k (₁₊ j))) (PB.sym PB.assoc))))

  lemma-HH-Z : ∀ {m} → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in SemiDirect.H • SemiDirect.H • SemiDirect.Z ≈ SemiDirect.Z ^ p-1 • (SemiDirect.H • SemiDirect.H)
  lemma-HH-Z = PB.trans (PB.cong PB.refl lemma-HZ) (PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong (lemma-HX^k p-1) PB.refl) PB.assoc))

  lemma-HH-S : ∀ {m} → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in SemiDirect.H • SemiDirect.H • SemiDirect.S ≈ SemiDirect.S • SemiDirect.H • SemiDirect.H
  lemma-HH-S {m} = rights lemma-comm-HHS
    where
    open LeftRightCongruence (XZ._QRel,_===_ (₁₊ m)) (Sim._QRel,_===_ (₁₊ m)) (ConjRelʷ SemiDirect.conj)
    open NSimL.Lemmas1b m

  lemma-H⁴ : ∀ {m} → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in SemiDirect.H ^ 4 ≈ ε
  lemma-H⁴ {m} = begin
      SemiDirect.H ^ 4   ≡⟨ Eq.sym (SemiDirect.lemma-[]ᵣ^k Sym.H 4) ⟩
      [ Sym.H ^ 4 ]ᵣ     ≈⟨ rights lemma-order-H ⟩
      ε ∎
    where
    open PB (SemiDirect._QRel,_===_ (₁₊ m))
    open PP (SemiDirect._QRel,_===_ (₁₊ m))
    open SR word-setoid
    open LeftRightCongruence (XZ._QRel,_===_ (₁₊ m)) (Sim._QRel,_===_ (₁₊ m)) (ConjRelʷ SemiDirect.conj)
    open NSimL.Lemmas1 m

  lemma-HH-Z^k : ∀ {m} (k : ℕ) → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in (SemiDirect.H • SemiDirect.H) • SemiDirect.Z ^ k ≈ (SemiDirect.Z ^ p-1) ^ k • (SemiDirect.H • SemiDirect.H)
  lemma-HH-Z^k 0 = PB.trans PB.right-unit (PB.sym PB.left-unit)
  lemma-HH-Z^k 1 = PB.trans PB.assoc lemma-HH-Z
  lemma-HH-Z^k (₂₊ k) = PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong (lemma-HH-Z^k 1) PB.refl) (PB.trans PB.assoc (PB.trans (PB.cong PB.refl (lemma-HH-Z^k (₁₊ k))) (PB.sym PB.assoc))))

  h-Z : ∀ {m} → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in (h ʷ) (Z {m}) ≈ SemiDirect.Z
  h-Z {m} = begin
      (h ʷ) (Z {m})
        ≡⟨ Eq.cong (λ w → SemiDirect.H • SemiDirect.H • (SemiDirect.Z ^ k • SemiDirect.S) • SemiDirect.H • SemiDirect.H • w) (lemma-fʷ-w^n {f = h} {w = S} (p-1)) ⟩
      SemiDirect.H • SemiDirect.H • (SemiDirect.Z ^ k • SemiDirect.S) • SemiDirect.H • SemiDirect.H • (SemiDirect.Z ^ k • SemiDirect.S) ^ (p-1)
        ≈⟨ mid-chain ⟩
      SemiDirect.Z ∎
    where
    open PB (SemiDirect._QRel,_===_ (₁₊ m))
    open PP (SemiDirect._QRel,_===_ (₁₊ m))
    open SR word-setoid
    open Pattern-Assoc
    open import Algebra.Properties.Ring (+-*-ring p-2)
    open import Data.Nat.DivMod using (_%_ ; _/_ ; m≡m%n+[m/n]*n ; %-distribˡ-* ; m<n⇒m%n≡m)
    open import Data.Fin.Properties using (toℕ<n)
    k = toℕ Cli.-1/2
    zp : SemiDirect.Z ^ p ≈ ε
    zp = trans (refl' (Eq.sym (SemiDirect.lemma-[]ₗ^k XZ.Z p))) (axiom (left XZ.order-Z))
    sp : SemiDirect.S ^ p ≈ ε
    sp = trans (refl' (Eq.sym (SemiDirect.lemma-[]ᵣ^k Sym.S p))) (axiom (right (Sim.srel Sim.order-S)))
    sp' : SemiDirect.S • SemiDirect.S ^ (p-1) ≈ ε
    sp' = trans (sym (^-+ SemiDirect.S 1 (p-1))) sp
    H⁴' : (SemiDirect.H • SemiDirect.H) • (SemiDirect.H • SemiDirect.H) ≈ ε
    H⁴' = trans (by-assoc Eq.refl) lemma-H⁴
    cZS : SemiDirect.Z ^ k • SemiDirect.S ≈ SemiDirect.S • SemiDirect.Z ^ k
    cZS = comm⇒pow-comm k 1 (sym (axiom (mid (comm XZ.Z-gen Sym.S-gen))))
    cSZkp : SemiDirect.S • SemiDirect.Z ^ (k Nat.* (p-1)) ≈ SemiDirect.Z ^ (k Nat.* (p-1)) • SemiDirect.S
    cSZkp = comm⇒pow-comm 1 (k Nat.* (p-1)) (axiom (mid (comm XZ.Z-gen Sym.S-gen)))
    expandB : (SemiDirect.Z ^ k • SemiDirect.S) ^ (p-1) ≈ SemiDirect.Z ^ (k Nat.* (p-1)) • SemiDirect.S ^ (p-1)
    expandB = trans (^-• (SemiDirect.Z ^ k) SemiDirect.S (p-1) cZS) (cleft (^^ SemiDirect.Z k (p-1)))
    Zmod : ∀ a → SemiDirect.Z ^ a ≈ SemiDirect.Z ^ (a % p)
    Zmod a = begin
      SemiDirect.Z ^ a                                              ≡⟨ Eq.cong (SemiDirect.Z ^_) (m≡m%n+[m/n]*n a p) ⟩
      SemiDirect.Z ^ (a % p Nat.+ a / p Nat.* p)                    ≈⟨ ^-+ SemiDirect.Z (a % p) (a / p Nat.* p) ⟩
      SemiDirect.Z ^ (a % p) • SemiDirect.Z ^ (a / p Nat.* p)       ≈⟨ cright (refl' (Eq.cong (SemiDirect.Z ^_) (NP.*-comm (a / p) p))) ⟩
      SemiDirect.Z ^ (a % p) • SemiDirect.Z ^ (p Nat.* (a / p))     ≈⟨ cright (sym (^^ SemiDirect.Z p (a / p))) ⟩
      SemiDirect.Z ^ (a % p) • (SemiDirect.Z ^ p) ^ (a / p)         ≈⟨ cright (^-cong (SemiDirect.Z ^ p) ε (a / p) zp) ⟩
      SemiDirect.Z ^ (a % p) • ε ^ (a / p)                          ≈⟨ cright (ε^k=ε (a / p)) ⟩
      SemiDirect.Z ^ (a % p) • ε                                    ≈⟨ right-unit ⟩
      SemiDirect.Z ^ (a % p) ∎
    2x=x+x : ∀ x → 2 Nat.* x ≡ x Nat.+ x
    2x=x+x x = Eq.cong (x Nat.+_) (NP.+-identityʳ x)
    negneg : (- 1ₚ) * (- 1ₚ) ≡ 1ₚ
    negneg = Eq.trans (Eq.sym (-‿distribˡ-* ₁ (- ₁))) (Eq.trans (Eq.sym (Eq.cong -_ (-‿distribʳ-* ₁ ₁))) (-‿involutive 1ₚ))
    -- A bare ₂ leaves its modulus ambiguous in the two positions below
    -- (an instance argument and under toℕ), so pin it once here.
    2ₚ : ℤ ₚ
    2ₚ = ₂
    idneg : ₂ * Cli.-1/2 ≡ - 1ₚ
    idneg = Eq.trans (*-comm ₂ Cli.-1/2) (Eq.trans (Eq.sym (-‿distribˡ-* inv2 ₂)) (Eq.cong -_ (lemma-⁻¹ˡ ₂ {{nztoℕ {y = 2ₚ} {neq0 = λ ()}}})))
      where inv2 = ((₂ , λ ()) ⁻¹) .proj₁
    toℕ-*3 : ∀ (a b c : ℤ ₚ) → (toℕ a Nat.* toℕ b Nat.* toℕ c) % p ≡ toℕ (a * b * c)
    toℕ-*3 a b c = Eq.trans (%-distribˡ-* (toℕ a Nat.* toℕ b) (toℕ c) p)
                  (Eq.trans (Eq.cong (λ z → (z Nat.* (toℕ c % p)) % p) (lemma-toℕ-% a b))
                  (Eq.trans (Eq.cong (λ z → (toℕ (a * b) Nat.* z) % p) (m<n⇒m%n≡m (toℕ<n c)))
                            (lemma-toℕ-% (a * b) c)))
    e≡prod : (p-1) Nat.* k Nat.+ k Nat.* (p-1) ≡ toℕ 2ₚ Nat.* toℕ Cli.-1/2 Nat.* toℕ (- 1ₚ)
    e≡prod = Eq.trans (Eq.cong (Nat._+ k Nat.* (p-1)) (NP.*-comm (p-1) k))
            (Eq.trans (Eq.sym (2x=x+x (k Nat.* (p-1))))
            (Eq.trans (Eq.sym (NP.*-assoc 2 k (p-1)))
                      (Eq.cong ((2 Nat.* k) Nat.*_) (Eq.sym lemma-toℕ-1ₚ))))
    prod≡1ₚ : ₂ * Cli.-1/2 * (- 1ₚ) ≡ 1ₚ
    prod≡1ₚ = Eq.trans (Eq.cong (λ z → z * (- 1ₚ)) idneg) negneg
    arith : ((p-1) Nat.* k Nat.+ k Nat.* (p-1)) % p ≡ 1
    arith = Eq.trans (Eq.cong (_% p) e≡prod)
           (Eq.trans (toℕ-*3 ₂ Cli.-1/2 (- 1ₚ))
                     (Eq.cong toℕ prod≡1ₚ))
    finalZ : (SemiDirect.Z ^ p-1) ^ k • SemiDirect.Z ^ (k Nat.* (p-1)) ≈ SemiDirect.Z
    finalZ = begin
      (SemiDirect.Z ^ p-1) ^ k • SemiDirect.Z ^ (k Nat.* (p-1))
        ≈⟨ cleft (^^ SemiDirect.Z p-1 k) ⟩
      SemiDirect.Z ^ (p-1 Nat.* k) • SemiDirect.Z ^ (k Nat.* (p-1))
        ≈⟨ sym (^-+ SemiDirect.Z (p-1 Nat.* k) (k Nat.* (p-1))) ⟩
      SemiDirect.Z ^ (p-1 Nat.* k Nat.+ k Nat.* (p-1))
        ≈⟨ Zmod (p-1 Nat.* k Nat.+ k Nat.* (p-1)) ⟩
      SemiDirect.Z ^ ((p-1 Nat.* k Nat.+ k Nat.* (p-1)) % p)
        ≡⟨ Eq.cong (SemiDirect.Z ^_) arith ⟩
      SemiDirect.Z ∎
    mid-chain : SemiDirect.H • SemiDirect.H • (SemiDirect.Z ^ k • SemiDirect.S) • SemiDirect.H • SemiDirect.H • (SemiDirect.Z ^ k • SemiDirect.S) ^ (p-1) ≈ SemiDirect.Z
    mid-chain = begin
      SemiDirect.H • SemiDirect.H • (SemiDirect.Z ^ k • SemiDirect.S) • SemiDirect.H • SemiDirect.H • (SemiDirect.Z ^ k • SemiDirect.S) ^ (p-1)
        ≈⟨ by-passoc (□ • (□ • ((□ • □) • (□ • (□ • □)))))
                         (((□ • □) • □) • (□ • ((□ • □) • □))) Eq.refl ⟩
      ((SemiDirect.H • SemiDirect.H) • SemiDirect.Z ^ k) • (SemiDirect.S • ((SemiDirect.H • SemiDirect.H) • (SemiDirect.Z ^ k • SemiDirect.S) ^ (p-1)))
        ≈⟨ cleft (lemma-HH-Z^k k) ⟩
      ((SemiDirect.Z ^ p-1) ^ k • (SemiDirect.H • SemiDirect.H)) • (SemiDirect.S • ((SemiDirect.H • SemiDirect.H) • (SemiDirect.Z ^ k • SemiDirect.S) ^ (p-1)))
        ≈⟨ by-passoc ((□ • (□ • □)) • (□ • ((□ • □) • □)))
                         (□ • (((□ • □) • □) • ((□ • □) • □))) Eq.refl ⟩
      (SemiDirect.Z ^ p-1) ^ k • (((SemiDirect.H • SemiDirect.H) • SemiDirect.S) • ((SemiDirect.H • SemiDirect.H) • (SemiDirect.Z ^ k • SemiDirect.S) ^ (p-1)))
        ≈⟨ cright (cleft (trans assoc lemma-HH-S)) ⟩
      (SemiDirect.Z ^ p-1) ^ k • ((SemiDirect.S • (SemiDirect.H • SemiDirect.H)) • ((SemiDirect.H • SemiDirect.H) • (SemiDirect.Z ^ k • SemiDirect.S) ^ (p-1)))
        ≈⟨ cright (by-passoc ((□ • (□ • □)) • ((□ • □) • □))
                                (□ • (((□ • □) • (□ • □)) • □)) Eq.refl) ⟩
      (SemiDirect.Z ^ p-1) ^ k • (SemiDirect.S • (((SemiDirect.H • SemiDirect.H) • (SemiDirect.H • SemiDirect.H)) • (SemiDirect.Z ^ k • SemiDirect.S) ^ (p-1)))
        ≈⟨ cright (cright (cleft H⁴')) ⟩
      (SemiDirect.Z ^ p-1) ^ k • (SemiDirect.S • (ε • (SemiDirect.Z ^ k • SemiDirect.S) ^ (p-1)))
        ≈⟨ cright (cright left-unit) ⟩
      (SemiDirect.Z ^ p-1) ^ k • (SemiDirect.S • (SemiDirect.Z ^ k • SemiDirect.S) ^ (p-1))
        ≈⟨ cright (cright expandB) ⟩
      (SemiDirect.Z ^ p-1) ^ k • (SemiDirect.S • (SemiDirect.Z ^ (k Nat.* (p-1)) • SemiDirect.S ^ (p-1)))
        ≈⟨ cright (sym assoc) ⟩
      (SemiDirect.Z ^ p-1) ^ k • ((SemiDirect.S • SemiDirect.Z ^ (k Nat.* (p-1))) • SemiDirect.S ^ (p-1))
        ≈⟨ cright (cleft cSZkp) ⟩
      (SemiDirect.Z ^ p-1) ^ k • ((SemiDirect.Z ^ (k Nat.* (p-1)) • SemiDirect.S) • SemiDirect.S ^ (p-1))
        ≈⟨ cright assoc ⟩
      (SemiDirect.Z ^ p-1) ^ k • (SemiDirect.Z ^ (k Nat.* (p-1)) • (SemiDirect.S • SemiDirect.S ^ (p-1)))
        ≈⟨ cright (cright sp') ⟩
      (SemiDirect.Z ^ p-1) ^ k • (SemiDirect.Z ^ (k Nat.* (p-1)) • ε)
        ≈⟨ cright right-unit ⟩
      (SemiDirect.Z ^ p-1) ^ k • SemiDirect.Z ^ (k Nat.* (p-1))
        ≈⟨ finalZ ⟩
      SemiDirect.Z ∎

  -- h-Mg reduces to h-R : (h*) Clifford.R ≈ S, which reduces to
  --   h-Z : (h*) Clifford.Z ≈ SemiDirect.Z.
  -- h-Z assembly (using the 7 lemmas above), with k = toℕ -1/2:
  --   (h*)Z = HH·Zᵏ·S·HH·(Zᵏ·S)^{p-1}
  --     ≈ Z^{(p-1)k}·HH·S·HH·(Zᵏ·S)^{p-1}      (lemma-HH-Z^k)
  --     ≈ Z^{(p-1)k}·S·(HH·HH)·(Zᵏ·S)^{p-1}     (lemma-HH-S)
  --     ≈ Z^{(p-1)k}·S·(Zᵏ·S)^{p-1}              (lemma-H⁴, HH·HH = H⁴ ≈ ε)
  --     ≈ Z^{(p-1)k}·S·Z^{k(p-1)}·S^{p-1}        (^-•)
  --     ≈ Z^{(p-1)k}·Z^{k(p-1)}·S^p              (Z,S commute; order-S: S^p ≈ ε)
  --     ≈ Z^{2k(p-1)} ≈ Z                        (^-+;  2k(p-1) ≡ 1 mod p  -- remaining ℤ_p arithmetic)
  hs : ∀ {m} → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in (h ʷ) (R {m}) ≈ SemiDirect.S
  hs {m} = begin
      (h ʷ) (R {m})
        ≈⟨ cright hz12 ⟩
      (SemiDirect.Z ^ k • SemiDirect.S) • SemiDirect.Z ^ (toℕ Cli.1/2)
        ≈⟨ assoc ⟩
      SemiDirect.Z ^ k • (SemiDirect.S • SemiDirect.Z ^ (toℕ Cli.1/2))
        ≈⟨ cright cZS12 ⟩
      SemiDirect.Z ^ k • (SemiDirect.Z ^ (toℕ Cli.1/2) • SemiDirect.S)
        ≈⟨ sym assoc ⟩
      (SemiDirect.Z ^ k • SemiDirect.Z ^ (toℕ Cli.1/2)) • SemiDirect.S
        ≈⟨ cleft zk12 ⟩
      ε • SemiDirect.S
        ≈⟨ left-unit ⟩
      SemiDirect.S ∎
    where
    open PB (SemiDirect._QRel,_===_ (₁₊ m))
    open PP (SemiDirect._QRel,_===_ (₁₊ m))
    open SR word-setoid
    open import Data.Nat.DivMod using (_%_ ; _/_ ; m≡m%n+[m/n]*n ; m%n<n)
    open import Data.Fin.Properties using (toℕ-fromℕ<)
    k = toℕ Cli.-1/2
    hz12 : (h ʷ) (Z {m} ^ toℕ Cli.1/2) ≈ SemiDirect.Z ^ (toℕ Cli.1/2)
    hz12 = trans (refl' (lemma-fʷ-w^n {f = h} {w = Z {m}} (toℕ Cli.1/2))) (^-cong ((h ʷ) (Z {m})) SemiDirect.Z (toℕ Cli.1/2) h-Z)
    cZS12 : SemiDirect.S • SemiDirect.Z ^ (toℕ Cli.1/2) ≈ SemiDirect.Z ^ (toℕ Cli.1/2) • SemiDirect.S
    cZS12 = comm⇒pow-comm 1 (toℕ Cli.1/2) (axiom (mid (comm XZ.Z-gen Sym.S-gen)))
    zp : SemiDirect.Z ^ p ≈ ε
    zp = trans (refl' (Eq.sym (SemiDirect.lemma-[]ₗ^k XZ.Z p))) (axiom (left XZ.order-Z))
    Zmod : ∀ a → SemiDirect.Z ^ a ≈ SemiDirect.Z ^ (a % p)
    Zmod a = begin
      SemiDirect.Z ^ a                                              ≡⟨ Eq.cong (SemiDirect.Z ^_) (m≡m%n+[m/n]*n a p) ⟩
      SemiDirect.Z ^ (a % p Nat.+ a / p Nat.* p)                    ≈⟨ ^-+ SemiDirect.Z (a % p) (a / p Nat.* p) ⟩
      SemiDirect.Z ^ (a % p) • SemiDirect.Z ^ (a / p Nat.* p)       ≈⟨ cright (refl' (Eq.cong (SemiDirect.Z ^_) (NP.*-comm (a / p) p))) ⟩
      SemiDirect.Z ^ (a % p) • SemiDirect.Z ^ (p Nat.* (a / p))     ≈⟨ cright (sym (^^ SemiDirect.Z p (a / p))) ⟩
      SemiDirect.Z ^ (a % p) • (SemiDirect.Z ^ p) ^ (a / p)         ≈⟨ cright (^-cong (SemiDirect.Z ^ p) ε (a / p) zp) ⟩
      SemiDirect.Z ^ (a % p) • ε ^ (a / p)                          ≈⟨ cright (ε^k=ε (a / p)) ⟩
      SemiDirect.Z ^ (a % p) • ε                                    ≈⟨ right-unit ⟩
      SemiDirect.Z ^ (a % p) ∎
    toℕ-+ : ∀ (a b : ℤ ₚ) → (toℕ a Nat.+ toℕ b) % p ≡ toℕ (a + b)
    toℕ-+ a b = Eq.sym (toℕ-fromℕ< (m%n<n (toℕ a Nat.+ toℕ b) p))
    arith0 : (k Nat.+ toℕ Cli.1/2) % p ≡ 0
    arith0 = Eq.trans (toℕ-+ Cli.-1/2 Cli.1/2) (Eq.cong toℕ (+-inverseˡ Cli.1/2))
    zk12 : SemiDirect.Z ^ k • SemiDirect.Z ^ (toℕ Cli.1/2) ≈ ε
    zk12 = begin
      SemiDirect.Z ^ k • SemiDirect.Z ^ (toℕ Cli.1/2)  ≈⟨ sym (^-+ SemiDirect.Z k (toℕ Cli.1/2)) ⟩
      SemiDirect.Z ^ (k Nat.+ toℕ Cli.1/2)             ≈⟨ Zmod (k Nat.+ toℕ Cli.1/2) ⟩
      SemiDirect.Z ^ ((k Nat.+ toℕ Cli.1/2) % p)       ≡⟨ Eq.cong (SemiDirect.Z ^_) arith0 ⟩
      ε ∎

  hs-pow : ∀ {m} k → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in (h ʷ) (R {m} ^ k) ≈ SemiDirect.S ^ k
  hs-pow {m} k = trans (refl' (lemma-fʷ-w^n {f = h} {w = R {m}} k)) (^-cong ((h ʷ) (R {m})) SemiDirect.S k (hs {m}))
    where
    open PB (SemiDirect._QRel,_===_ (₁₊ m))
    open PP (SemiDirect._QRel,_===_ (₁₊ m))

  h-M : ∀ {m} (x : ℤ* ₚ) → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in (h ʷ) (M {m} x) ≈ [ Sym.M {m} x ]ᵣ
  h-M {m} x = begin
      (h ʷ) (M x)
        ≈⟨ cong (hs-pow (toℕ x₁)) (cong refl (cong (hs-pow (toℕ x₂)) (cong refl (cong (hs-pow (toℕ x₁)) refl)))) ⟩
      SemiDirect.S ^ toℕ x₁ • SemiDirect.H • SemiDirect.S ^ toℕ x₂ • SemiDirect.H • SemiDirect.S ^ toℕ x₁ • SemiDirect.H
        ≡⟨ Eq.cong₂ _•_ (Eq.sym (SemiDirect.lemma-[]ᵣ^k Sym.S (toℕ x₁)))
                 (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_ (Eq.sym (SemiDirect.lemma-[]ᵣ^k Sym.S (toℕ x₂)))
                 (Eq.cong₂ _•_ Eq.refl (Eq.cong₂ _•_ (Eq.sym (SemiDirect.lemma-[]ᵣ^k Sym.S (toℕ x₁))) Eq.refl)))) ⟩
      [ Sym.M x ]ᵣ ∎
    where
    open PB (SemiDirect._QRel,_===_ (₁₊ m))
    open PP (SemiDirect._QRel,_===_ (₁₊ m))
    open SR word-setoid
    x₁ = x .proj₁
    x₂ = (x ⁻¹) .proj₁

  h-Mg : ∀ {m} → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in (h ʷ) (Mg {m}) ≈ [ Sim.Mg {m} ]ᵣ
  h-Mg {m} = h-M {m} g*

  h-Mg↑ : ∀ {m} → let open PB (SemiDirect._QRel,_===_ (₂₊ m)) using (_≈_) in ((h ʷ) (Mg {m})) SemiDirect.↑ ≈ ([ Sim.Mg {m} ]ᵣ) SemiDirect.↑
  h-Mg↑ {m} = SemiDirect.lemma-cong↑ {₁₊ m} _ _ (h-Mg {m})

  h-X : ∀ {m} → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in (h ʷ) (X {m}) ≈ SemiDirect.X
  h-X {m} = begin
      (h ʷ) (X {m})
        ≈⟨ sym left-unit ⟩
      ε • (h ʷ) (X {m})
        ≈⟨ cleft (sym H4ε) ⟩
      (SemiDirect.H • SemiDirect.H • SemiDirect.H • SemiDirect.H) • (h ʷ) (X {m})
        ≈⟨ by-passoc ((□ • □ • □ • □) • □) ((□ • □ • □) • (□ • □)) Eq.refl ⟩
      (SemiDirect.H • SemiDirect.H • SemiDirect.H) • (SemiDirect.H • (h ʷ) (X {m}))
        ≈⟨ cright lemmaHX' ⟩
      (SemiDirect.H • SemiDirect.H • SemiDirect.H) • ((h ʷ) (Z {m}) • SemiDirect.H)
        ≈⟨ cright (cleft (h-Z {m})) ⟩
      (SemiDirect.H • SemiDirect.H • SemiDirect.H) • (SemiDirect.Z • SemiDirect.H)
        ≈⟨ cright (sym lemma-HX) ⟩
      (SemiDirect.H • SemiDirect.H • SemiDirect.H) • (SemiDirect.H • SemiDirect.X)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □)) ((□ • □ • □ • □) • □) Eq.refl ⟩
      (SemiDirect.H • SemiDirect.H • SemiDirect.H • SemiDirect.H) • SemiDirect.X
        ≈⟨ cleft H4ε ⟩
      ε • SemiDirect.X
        ≈⟨ left-unit ⟩
      SemiDirect.X ∎
    where
    open PB (SemiDirect._QRel,_===_ (₁₊ m))
    open PP (SemiDirect._QRel,_===_ (₁₊ m))
    open SR word-setoid
    open Pattern-Assoc
    H4ε : SemiDirect.H • SemiDirect.H • SemiDirect.H • SemiDirect.H ≈ ε
    H4ε = trans (by-assoc Eq.refl) lemma-H⁴
    lemmaHX' : SemiDirect.H • (h ʷ) (X {m}) ≈ (h ʷ) (Z {m}) • SemiDirect.H
    lemmaHX' = by-passoc (□ • (□ • (□ • (□ • (□ • (□ • □)))))) ((□ • (□ • (□ • (□ • (□ • □))))) • □) Eq.refl

  ↑pow : ∀ {m} (w : Word (SemiDirect.Gen (₁₊ m))) (k : ℕ) → (w ^ k) SemiDirect.↑ ≡ (w SemiDirect.↑) ^ k
  ↑pow w 0 = Eq.refl
  ↑pow w 1 = Eq.refl
  ↑pow w (₂₊ k) = Eq.cong₂ _•_ Eq.refl (↑pow w (₁₊ k))

  hs↑ : ∀ {m} → let open PB (SemiDirect._QRel,_===_ (₂₊ m)) using (_≈_) in (h ʷ) (R {m} ↑) ≈ SemiDirect.S SemiDirect.↑
  hs↑ {m} = trans (refl' (lemma-h↑ (R {m}))) (SemiDirect.lemma-cong↑ {₁₊ m} _ _ (hs {m}))
    where
    open PB (SemiDirect._QRel,_===_ (₂₊ m))

  hs↑pow : ∀ {m} → let open PB (SemiDirect._QRel,_===_ (₂₊ m)) using (_≈_) in (h ʷ) ((R {m} ↑) ^ p-1) ≈ (SemiDirect.S SemiDirect.↑) ^ p-1
  hs↑pow {m} = trans (refl' (lemma-fʷ-w^n {f = h} {w = R {m} ↑} p-1)) (^-cong ((h ʷ) (R {m} ↑)) (SemiDirect.S SemiDirect.↑) p-1 (hs↑ {m}))
    where
    open PB (SemiDirect._QRel,_===_ (₂₊ m))
    open PP (SemiDirect._QRel,_===_ (₂₊ m))

  conv↓ : ∀ {m} → let open PB (SemiDirect._QRel,_===_ (₁₊ m)) using (_≈_) in [ Sym.S⁻¹ {m} ]ᵣ ≈ (h ʷ) (R {m} ^ p-1)
  conv↓ {m} = trans (refl' (SemiDirect.lemma-[]ᵣ^k (Sym.S {m}) p-1)) (sym (hs-pow {m} p-1))
    where
    open PB (SemiDirect._QRel,_===_ (₁₊ m))

  conv↑ : ∀ {m} → let open PB (SemiDirect._QRel,_===_ (₂₊ m)) using (_≈_) in [ Sym.S⁻¹ {m} Sym.↑ ]ᵣ ≈ (h ʷ) ((R {m} ↑) ^ p-1)
  conv↑ {m} = trans (refl' eq≡) (sym (hs↑pow {m}))
    where
    open PB (SemiDirect._QRel,_===_ (₂₊ m))
    eq≡ : [ Sym.S⁻¹ {m} Sym.↑ ]ᵣ ≡ (SemiDirect.S SemiDirect.↑) ^ p-1
    eq≡ = Eq.trans (Eq.sym (SemiDirect.lemma-[]ᵣ-↑ (Sym.S⁻¹ {m}))) (Eq.trans (Eq.cong (λ z → z SemiDirect.↑) (SemiDirect.lemma-[]ᵣ^k (Sym.S {m}) p-1)) (↑pow (SemiDirect.S {m}) p-1))


  h-well-defined : ∀ {n w v} ->
    let
      open PB (n SemiDirect.QRel,_===_) renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
      open PB (n Clifford.QRel,_===_) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_ ; cleft_ to cleft₂_ ; cright_ to cright₂_) using ()
    in
    w ===₂ v -> (h ʷ) w ≈₁ (h ʷ) v

  h-well-defined {₁₊ n} order-S = begin
    (h ʷ) (S ^ p)                              ≡⟨ lemma-fʷ-w^n {f = h} {w = S} p ⟩
    (h ʷ) S ^ p                                ≈⟨ ^-• (SemiDirect.Z ^ k) SemiDirect.S p commZS ⟩
    (SemiDirect.Z ^ k) ^ p • SemiDirect.S ^ p  ≈⟨ cong zk^p sp ⟩
    ε • ε                                      ≈⟨ left-unit ⟩
    ε ∎
    where
    open PB (SemiDirect._QRel,_===_ (₁₊ n))
    open PP (SemiDirect._QRel,_===_ (₁₊ n))
    open SR word-setoid
    k : ℕ
    k = toℕ Cli.-1/2
    commZS : (SemiDirect.Z ^ k) • SemiDirect.S ≈ SemiDirect.S • (SemiDirect.Z ^ k)
    commZS = comm⇒pow-comm k 1 (sym (axiom (mid (comm XZ.Z-gen Sym.S-gen))))
    zp : SemiDirect.Z ^ p ≈ ε
    zp = begin
      SemiDirect.Z ^ p  ≡⟨ Eq.sym (SemiDirect.lemma-[]ₗ^k XZ.Z p) ⟩
      [ XZ.Z ^ p ]ₗ     ≈⟨ axiom (left XZ.order-Z) ⟩
      ε ∎
    sp : SemiDirect.S ^ p ≈ ε
    sp = begin
      SemiDirect.S ^ p  ≡⟨ Eq.sym (SemiDirect.lemma-[]ᵣ^k Sym.S p) ⟩
      [ Sym.S ^ p ]ᵣ    ≈⟨ axiom (right (Sim.srel Sim.order-S)) ⟩
      ε ∎
    zk^p : (SemiDirect.Z ^ k) ^ p ≈ ε
    zk^p = begin
      (SemiDirect.Z ^ k) ^ p        ≈⟨ ^^ SemiDirect.Z k p ⟩
      SemiDirect.Z ^ (k Nat.* p)    ≡⟨ Eq.cong (SemiDirect.Z ^_) (NP.*-comm k p) ⟩
      SemiDirect.Z ^ (p Nat.* k)    ≈⟨ sym (^^ SemiDirect.Z p k) ⟩
      (SemiDirect.Z ^ p) ^ k        ≈⟨ ^-cong (SemiDirect.Z ^ p) ε k zp ⟩
      ε ^ k                         ≈⟨ ε^k=ε k ⟩
      ε ∎
  h-well-defined {₁₊ n} order-H = begin
    (h ʷ) (H ^ 2)            ≡⟨ lemma-fʷ-w^n {f = h} {w = H} 2 ⟩
    (h ʷ) H ^ 2              ≡⟨ Eq.sym (SemiDirect.lemma-[]ᵣ^k Sym.H 2) ⟩
    [ Sym.H ^ 2 ]ᵣ          ≈⟨ axiom (right (Sim.srel Sim.order-H)) ⟩
    [ Sim.M₋₁ {n} ]ᵣ        ≈⟨ sym (h-M {n} -'₁) ⟩
    (h ʷ) (M -'₁) ∎
    where
    open PB (SemiDirect._QRel,_===_ (₁₊ n))
    open PP (SemiDirect._QRel,_===_ (₁₊ n))
    open SR word-setoid
  h-well-defined {₁₊ n} (M-power k) = begin
    (h ʷ) (Mg^ k)                       ≡⟨ lemma-fʷ-w^n {f = h} {w = Mg {n}} (toℕ k) ⟩
    (h ʷ) (Mg {n}) ^ toℕ k              ≈⟨ ^-cong ((h ʷ) (Mg {n})) ([ Sim.Mg {n} ]ᵣ) (toℕ k) (h-Mg {n}) ⟩
    [ Sim.Mg {n} ]ᵣ ^ toℕ k            ≡⟨ Eq.sym (SemiDirect.lemma-[]ᵣ^k (Sim.Mg {n}) (toℕ k)) ⟩
    [ Sim.Mg {n} ^ toℕ k ]ᵣ            ≈⟨ axiom (right (Sim.srel (Sim.M-power k))) ⟩
    [ Sym.M (g^ k) ]ᵣ                  ≈⟨ sym (h-M {n} (g^ k)) ⟩
    (h ʷ) (M (g^ k)) ∎
    where
    open PB (SemiDirect._QRel,_===_ (₁₊ n))
    open PP (SemiDirect._QRel,_===_ (₁₊ n))
    open SR word-setoid
    open Primitive-Root-Modp' g* g-gen
  h-well-defined {₁₊ n} semi-MR = begin
    (h ʷ) (Mg • R)
      ≈⟨ cong (h-Mg {n}) (hs {n}) ⟩
    [ Sim.Mg {n} ]ᵣ • [ Sym.S ]ᵣ
      ≈⟨ axiom (right (Sim.srel Sim.semi-MS)) ⟩
    [ Sym.S ^ toℕ (g * g) ]ᵣ • [ Sim.Mg {n} ]ᵣ
      ≈⟨ cong (trans (refl' (SemiDirect.lemma-[]ᵣ^k Sym.S (toℕ (g * g)))) (sym (hs-pow (toℕ (g * g))))) (sym (h-Mg {n})) ⟩
    (h ʷ) (R^ (g * g) • Mg) ∎
    where
    open PB (SemiDirect._QRel,_===_ (₁₊ n))
    open PP (SemiDirect._QRel,_===_ (₁₊ n))
    open SR word-setoid
  h-well-defined {₁₊ m} order-SH = begin
      (h ʷ) ((S • H) ^ 3)
        ≡⟨ lemma-fʷ-w^n {f = h} {w = S • H} 3 ⟩
      (h ʷ) (S • H) ^ 3
        ≈⟨ ^-cong ((h ʷ) (S • H)) (Zk • u) 3 assoc ⟩
      (Zk • u) ^ 3
        ≈⟨ by-passoc ((□ • □) • ((□ • □) • (□ • □))) (□ • (□ • (□ • (□ • (□ • □))))) Eq.refl ⟩
      Zk • (u • (Zk • (u • (Zk • u))))
        ≈⟨ cright (sym assoc) ⟩
      Zk • ((u • Zk) • (u • (Zk • u)))
        ≈⟨ cright (cleft Rk) ⟩
      Zk • ((Q₁ • u) • (u • (Zk • u)))
        ≈⟨ cright assoc ⟩
      Zk • (Q₁ • (u • (u • (Zk • u))))
        ≈⟨ cright (cright (cright (sym assoc))) ⟩
      Zk • (Q₁ • (u • ((u • Zk) • u)))
        ≈⟨ cright (cright (cright (cleft Rk))) ⟩
      Zk • (Q₁ • (u • ((Q₁ • u) • u)))
        ≈⟨ cright (cright (by-passoc (□ • ((□ • □) • □)) ((□ • □) • (□ • □)) Eq.refl)) ⟩
      Zk • (Q₁ • ((u • Q₁) • (u • u)))
        ≈⟨ cright (cright (cleft R2)) ⟩
      Zk • (Q₁ • ((Q₂ • u) • (u • u)))
        ≈⟨ cright (cright assoc) ⟩
      Zk • (Q₁ • (Q₂ • (u • (u • u))))
        ≈⟨ cright (cright (cright u3)) ⟩
      Zk • (Q₁ • (Q₂ • ε))
        ≈⟨ cright (cright right-unit) ⟩
      Zk • (Q₁ • Q₂)
        ≈⟨ finalP ⟩
      ε ∎
    where
    open PB (SemiDirect._QRel,_===_ (₁₊ m))
    open PP (SemiDirect._QRel,_===_ (₁₊ m))
    open SR word-setoid
    open Pattern-Assoc
    open LeftRightCongruence (XZ._QRel,_===_ (₁₊ m)) (Sim._QRel,_===_ (₁₊ m)) (ConjRelʷ SemiDirect.conj)
    open NSimL.Lemmas1 m
    k = toℕ Cli.-1/2
    a = (p-1) Nat.* k
    b = (p-1) Nat.* a
    u  = SemiDirect.S • SemiDirect.H
    Zk = SemiDirect.Z ^ k
    Q₁ = SemiDirect.X ^ a • SemiDirect.Z ^ a
    Q₂ = SemiDirect.X ^ b
    zp : SemiDirect.Z ^ p ≈ ε
    zp = trans (refl' (Eq.sym (SemiDirect.lemma-[]ₗ^k XZ.Z p))) (axiom (left XZ.order-Z))
    xp : SemiDirect.X ^ p ≈ ε
    xp = trans (refl' (Eq.sym (SemiDirect.lemma-[]ₗ^k XZ.X p))) (axiom (left XZ.order-X))
    commXZ : SemiDirect.X • SemiDirect.Z ≈ SemiDirect.Z • SemiDirect.X
    commXZ = sym (axiom (left XZ.comm-Z-X))
    zpn : ∀ n → SemiDirect.Z ^ (p Nat.* n) ≈ ε
    zpn n = trans (sym (^^ SemiDirect.Z p n)) (trans (^-cong (SemiDirect.Z ^ p) ε n zp) (ε^k=ε n))
    xpn : ∀ n → SemiDirect.X ^ (p Nat.* n) ≈ ε
    xpn n = trans (sym (^^ SemiDirect.X p n)) (trans (^-cong (SemiDirect.X ^ p) ε n xp) (ε^k=ε n))
    Rgen : ∀ j → u • SemiDirect.Z ^ j ≈ (SemiDirect.X ^ ((p-1) Nat.* j) • SemiDirect.Z ^ ((p-1) Nat.* j)) • u
    Rgen j = begin
      u • SemiDirect.Z ^ j
        ≈⟨ assoc ⟩
      SemiDirect.S • (SemiDirect.H • SemiDirect.Z ^ j)
        ≈⟨ cright (trans (lemma-HZ^k j) (cleft (^^ SemiDirect.X (p-1) j))) ⟩
      SemiDirect.S • (SemiDirect.X ^ ((p-1) Nat.* j) • SemiDirect.H)
        ≈⟨ sym assoc ⟩
      (SemiDirect.S • SemiDirect.X ^ ((p-1) Nat.* j)) • SemiDirect.H
        ≈⟨ cleft (trans (lemma-SX^k ((p-1) Nat.* j)) (cleft (^-• SemiDirect.X SemiDirect.Z ((p-1) Nat.* j) commXZ))) ⟩
      ((SemiDirect.X ^ ((p-1) Nat.* j) • SemiDirect.Z ^ ((p-1) Nat.* j)) • SemiDirect.S) • SemiDirect.H
        ≈⟨ assoc ⟩
      (SemiDirect.X ^ ((p-1) Nat.* j) • SemiDirect.Z ^ ((p-1) Nat.* j)) • u ∎
    Rk : u • Zk ≈ Q₁ • u
    Rk = Rgen k
    uXa : u • SemiDirect.X ^ a ≈ SemiDirect.Z ^ a • u
    uXa = begin
      u • SemiDirect.X ^ a
        ≈⟨ assoc ⟩
      SemiDirect.S • (SemiDirect.H • SemiDirect.X ^ a)
        ≈⟨ cright (lemma-HX^k a) ⟩
      SemiDirect.S • (SemiDirect.Z ^ a • SemiDirect.H)
        ≈⟨ sym assoc ⟩
      (SemiDirect.S • SemiDirect.Z ^ a) • SemiDirect.H
        ≈⟨ cleft (comm⇒pow-comm 1 a (axiom (mid (comm XZ.Z-gen Sym.S-gen)))) ⟩
      (SemiDirect.Z ^ a • SemiDirect.S) • SemiDirect.H
        ≈⟨ assoc ⟩
      SemiDirect.Z ^ a • u ∎
    R2 : u • Q₁ ≈ Q₂ • u
    R2 = begin
      u • (SemiDirect.X ^ a • SemiDirect.Z ^ a)
        ≈⟨ sym assoc ⟩
      (u • SemiDirect.X ^ a) • SemiDirect.Z ^ a
        ≈⟨ cleft uXa ⟩
      (SemiDirect.Z ^ a • u) • SemiDirect.Z ^ a
        ≈⟨ assoc ⟩
      SemiDirect.Z ^ a • (u • SemiDirect.Z ^ a)
        ≈⟨ cright (Rgen a) ⟩
      SemiDirect.Z ^ a • ((SemiDirect.X ^ b • SemiDirect.Z ^ b) • u)
        ≈⟨ sym assoc ⟩
      (SemiDirect.Z ^ a • (SemiDirect.X ^ b • SemiDirect.Z ^ b)) • u
        ≈⟨ cleft collapse ⟩
      SemiDirect.X ^ b • u ∎
      where
      collapse : SemiDirect.Z ^ a • (SemiDirect.X ^ b • SemiDirect.Z ^ b) ≈ SemiDirect.X ^ b
      collapse = begin
        SemiDirect.Z ^ a • (SemiDirect.X ^ b • SemiDirect.Z ^ b)
          ≈⟨ sym assoc ⟩
        (SemiDirect.Z ^ a • SemiDirect.X ^ b) • SemiDirect.Z ^ b
          ≈⟨ cleft (comm⇒pow-comm a b (axiom (left XZ.comm-Z-X))) ⟩
        (SemiDirect.X ^ b • SemiDirect.Z ^ a) • SemiDirect.Z ^ b
          ≈⟨ assoc ⟩
        SemiDirect.X ^ b • (SemiDirect.Z ^ a • SemiDirect.Z ^ b)
          ≈⟨ cright (sym (^-+ SemiDirect.Z a b)) ⟩
        SemiDirect.X ^ b • SemiDirect.Z ^ (a Nat.+ b)
          ≈⟨ cright (zpn a) ⟩
        SemiDirect.X ^ b • ε
          ≈⟨ right-unit ⟩
        SemiDirect.X ^ b ∎
    u3 : (SemiDirect.S • SemiDirect.H) ^ 3 ≈ ε
    u3 = begin
      (SemiDirect.S • SemiDirect.H) ^ 3
        ≡⟨ Eq.sym (SemiDirect.lemma-[]ᵣ^k (Sym.S • Sym.H) 3) ⟩
      [ (Sym.S • Sym.H) ^ 3 ]ᵣ
        ≈⟨ rights lemma-order-SH ⟩
      ε ∎
    finalP : Zk • (Q₁ • Q₂) ≈ ε
    finalP = begin
      SemiDirect.Z ^ k • ((SemiDirect.X ^ a • SemiDirect.Z ^ a) • SemiDirect.X ^ b)
        ≈⟨ cright assoc ⟩
      SemiDirect.Z ^ k • (SemiDirect.X ^ a • (SemiDirect.Z ^ a • SemiDirect.X ^ b))
        ≈⟨ cright (cright (comm⇒pow-comm a b (axiom (left XZ.comm-Z-X)))) ⟩
      SemiDirect.Z ^ k • (SemiDirect.X ^ a • (SemiDirect.X ^ b • SemiDirect.Z ^ a))
        ≈⟨ cright (sym assoc) ⟩
      SemiDirect.Z ^ k • ((SemiDirect.X ^ a • SemiDirect.X ^ b) • SemiDirect.Z ^ a)
        ≈⟨ cright (cleft (sym (^-+ SemiDirect.X a b))) ⟩
      SemiDirect.Z ^ k • (SemiDirect.X ^ (a Nat.+ b) • SemiDirect.Z ^ a)
        ≈⟨ sym assoc ⟩
      (SemiDirect.Z ^ k • SemiDirect.X ^ (a Nat.+ b)) • SemiDirect.Z ^ a
        ≈⟨ cleft (comm⇒pow-comm k (a Nat.+ b) (axiom (left XZ.comm-Z-X))) ⟩
      (SemiDirect.X ^ (a Nat.+ b) • SemiDirect.Z ^ k) • SemiDirect.Z ^ a
        ≈⟨ assoc ⟩
      SemiDirect.X ^ (a Nat.+ b) • (SemiDirect.Z ^ k • SemiDirect.Z ^ a)
        ≈⟨ cright (sym (^-+ SemiDirect.Z k a)) ⟩
      SemiDirect.X ^ (a Nat.+ b) • SemiDirect.Z ^ (k Nat.+ a)
        ≈⟨ cong (xpn a) (zpn k) ⟩
      ε • ε
        ≈⟨ left-unit ⟩
      ε ∎
  h-well-defined {₁₊ m} comm-HHSHHS = trans lhs (sym rhs)
    where
    open PB (SemiDirect._QRel,_===_ (₁₊ m))
    open PP (SemiDirect._QRel,_===_ (₁₊ m))
    open SR word-setoid
    open Pattern-Assoc
    k : ℕ
    k = toℕ Cli.-1/2
    cZS : SemiDirect.Z ^ k • SemiDirect.S ≈ SemiDirect.S • SemiDirect.Z ^ k
    cZS = comm⇒pow-comm k 1 (sym (axiom (mid (comm XZ.Z-gen Sym.S-gen))))
    cSZ : SemiDirect.S • SemiDirect.Z ^ k ≈ SemiDirect.Z ^ k • SemiDirect.S
    cSZ = sym cZS
    cQS : (SemiDirect.Z ^ p-1) ^ k • SemiDirect.S ≈ SemiDirect.S • (SemiDirect.Z ^ p-1) ^ k
    cQS = comm⇒pow-comm k 1 (comm⇒pow-comm p-1 1 (sym (axiom (mid (comm XZ.Z-gen Sym.S-gen)))))
    cSQ : SemiDirect.S • (SemiDirect.Z ^ p-1) ^ k ≈ (SemiDirect.Z ^ p-1) ^ k • SemiDirect.S
    cSQ = sym cQS
    zp : SemiDirect.Z ^ p ≈ ε
    zp = trans (refl' (Eq.sym (SemiDirect.lemma-[]ₗ^k XZ.Z p))) (axiom (left XZ.order-Z))
    H⁴' : (SemiDirect.H • SemiDirect.H) • (SemiDirect.H • SemiDirect.H) ≈ ε
    H⁴' = trans (by-assoc Eq.refl) lemma-H⁴
    ZZ : (SemiDirect.Z ^ p-1) ^ k • SemiDirect.Z ^ k ≈ ε
    ZZ = begin
      (SemiDirect.Z ^ p-1) ^ k • SemiDirect.Z ^ k  ≈⟨ cleft (^^ SemiDirect.Z p-1 k) ⟩
      SemiDirect.Z ^ (p-1 Nat.* k) • SemiDirect.Z ^ k  ≈⟨ sym (^-+ SemiDirect.Z (p-1 Nat.* k) k) ⟩
      SemiDirect.Z ^ (p-1 Nat.* k Nat.+ k)  ≡⟨ Eq.cong (SemiDirect.Z ^_) (NP.+-comm (p-1 Nat.* k) k) ⟩
      SemiDirect.Z ^ (k Nat.+ p-1 Nat.* k)  ≈⟨ sym (^^ SemiDirect.Z p k) ⟩
      (SemiDirect.Z ^ p) ^ k  ≈⟨ ^-cong (SemiDirect.Z ^ p) ε k zp ⟩
      ε ^ k  ≈⟨ ε^k=ε k ⟩
      ε ∎
    ZZ' : SemiDirect.Z ^ k • (SemiDirect.Z ^ p-1) ^ k ≈ ε
    ZZ' = begin
      SemiDirect.Z ^ k • (SemiDirect.Z ^ p-1) ^ k  ≈⟨ cright (^^ SemiDirect.Z p-1 k) ⟩
      SemiDirect.Z ^ k • SemiDirect.Z ^ (p-1 Nat.* k)  ≈⟨ sym (^-+ SemiDirect.Z k (p-1 Nat.* k)) ⟩
      SemiDirect.Z ^ (k Nat.+ p-1 Nat.* k)  ≈⟨ sym (^^ SemiDirect.Z p k) ⟩
      (SemiDirect.Z ^ p) ^ k  ≈⟨ ^-cong (SemiDirect.Z ^ p) ε k zp ⟩
      ε ^ k  ≈⟨ ε^k=ε k ⟩
      ε ∎
    lhs : (h ʷ) (H • H • S • H • H • S) ≈ SemiDirect.S • SemiDirect.S
    lhs = begin
      (h ʷ) (H • H • S • H • H • S)
        ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □ • (□ • □))
                         (((□ • □) • □) • □ • ((□ • □) • (□ • □))) Eq.refl ⟩
      ((SemiDirect.H • SemiDirect.H) • SemiDirect.Z ^ k) • (SemiDirect.S • ((SemiDirect.H • SemiDirect.H) • (SemiDirect.Z ^ k • SemiDirect.S)))
        ≈⟨ cleft (lemma-HH-Z^k k) ⟩
      ((SemiDirect.Z ^ p-1) ^ k • (SemiDirect.H • SemiDirect.H)) • (SemiDirect.S • ((SemiDirect.H • SemiDirect.H) • (SemiDirect.Z ^ k • SemiDirect.S)))
        ≈⟨ by-passoc ((□ • (□ • □)) • (□ • ((□ • □) • (□ • □))))
                         (□ • (((□ • □) • □) • ((□ • □) • (□ • □)))) Eq.refl ⟩
      (SemiDirect.Z ^ p-1) ^ k • (((SemiDirect.H • SemiDirect.H) • SemiDirect.S) • ((SemiDirect.H • SemiDirect.H) • (SemiDirect.Z ^ k • SemiDirect.S)))
        ≈⟨ cright (cleft (trans assoc lemma-HH-S)) ⟩
      (SemiDirect.Z ^ p-1) ^ k • ((SemiDirect.S • (SemiDirect.H • SemiDirect.H)) • ((SemiDirect.H • SemiDirect.H) • (SemiDirect.Z ^ k • SemiDirect.S)))
        ≈⟨ cright (by-passoc ((□ • (□ • □)) • ((□ • □) • (□ • □)))
                                (□ • (((□ • □) • (□ • □)) • (□ • □))) Eq.refl) ⟩
      (SemiDirect.Z ^ p-1) ^ k • (SemiDirect.S • (((SemiDirect.H • SemiDirect.H) • (SemiDirect.H • SemiDirect.H)) • (SemiDirect.Z ^ k • SemiDirect.S)))
        ≈⟨ cright (cright (cleft H⁴')) ⟩
      (SemiDirect.Z ^ p-1) ^ k • (SemiDirect.S • (ε • (SemiDirect.Z ^ k • SemiDirect.S)))
        ≈⟨ cright (cright left-unit) ⟩
      (SemiDirect.Z ^ p-1) ^ k • (SemiDirect.S • (SemiDirect.Z ^ k • SemiDirect.S))
        ≈⟨ cright (sym assoc) ⟩
      (SemiDirect.Z ^ p-1) ^ k • ((SemiDirect.S • SemiDirect.Z ^ k) • SemiDirect.S)
        ≈⟨ cright (cleft cSZ) ⟩
      (SemiDirect.Z ^ p-1) ^ k • ((SemiDirect.Z ^ k • SemiDirect.S) • SemiDirect.S)
        ≈⟨ by-passoc (□ • ((□ • □) • □)) ((□ • □) • (□ • □)) Eq.refl ⟩
      ((SemiDirect.Z ^ p-1) ^ k • SemiDirect.Z ^ k) • (SemiDirect.S • SemiDirect.S)
        ≈⟨ cleft ZZ ⟩
      ε • (SemiDirect.S • SemiDirect.S)
        ≈⟨ left-unit ⟩
      SemiDirect.S • SemiDirect.S ∎
    rhs : (h ʷ) (S • H • H • S • H • H) ≈ SemiDirect.S • SemiDirect.S
    rhs = begin
      (h ʷ) (S • H • H • S • H • H)
        ≈⟨ by-passoc ((□ • □) • □ • □ • (□ • □) • □ • □)
                         (□ • (□ • (((□ • □) • □) • (□ • (□ • □))))) Eq.refl ⟩
      SemiDirect.Z ^ k • (SemiDirect.S • (((SemiDirect.H • SemiDirect.H) • SemiDirect.Z ^ k) • (SemiDirect.S • (SemiDirect.H • SemiDirect.H))))
        ≈⟨ cright (cright (cleft (lemma-HH-Z^k k))) ⟩
      SemiDirect.Z ^ k • (SemiDirect.S • (((SemiDirect.Z ^ p-1) ^ k • (SemiDirect.H • SemiDirect.H)) • (SemiDirect.S • (SemiDirect.H • SemiDirect.H))))
        ≈⟨ cright (cright (by-passoc ((□ • (□ • □)) • (□ • (□ • □)))
                                         (□ • (((□ • □) • □) • (□ • □))) Eq.refl)) ⟩
      SemiDirect.Z ^ k • (SemiDirect.S • ((SemiDirect.Z ^ p-1) ^ k • (((SemiDirect.H • SemiDirect.H) • SemiDirect.S) • (SemiDirect.H • SemiDirect.H))))
        ≈⟨ cright (cright (cright (cleft (trans assoc lemma-HH-S)))) ⟩
      SemiDirect.Z ^ k • (SemiDirect.S • ((SemiDirect.Z ^ p-1) ^ k • (((SemiDirect.S • (SemiDirect.H • SemiDirect.H)) • (SemiDirect.H • SemiDirect.H)))))
        ≈⟨ cright (cright (cright (by-passoc ((□ • (□ • □)) • (□ • □))
                                                (□ • ((□ • □) • (□ • □))) Eq.refl))) ⟩
      SemiDirect.Z ^ k • (SemiDirect.S • ((SemiDirect.Z ^ p-1) ^ k • (SemiDirect.S • ((SemiDirect.H • SemiDirect.H) • (SemiDirect.H • SemiDirect.H)))))
        ≈⟨ cright (cright (cright (cright H⁴'))) ⟩
      SemiDirect.Z ^ k • (SemiDirect.S • ((SemiDirect.Z ^ p-1) ^ k • (SemiDirect.S • ε)))
        ≈⟨ cright (cright (cright right-unit)) ⟩
      SemiDirect.Z ^ k • (SemiDirect.S • ((SemiDirect.Z ^ p-1) ^ k • SemiDirect.S))
        ≈⟨ cright (sym assoc) ⟩
      SemiDirect.Z ^ k • ((SemiDirect.S • (SemiDirect.Z ^ p-1) ^ k) • SemiDirect.S)
        ≈⟨ cright (cleft cSQ) ⟩
      SemiDirect.Z ^ k • (((SemiDirect.Z ^ p-1) ^ k • SemiDirect.S) • SemiDirect.S)
        ≈⟨ by-passoc (□ • ((□ • □) • □)) ((□ • □) • (□ • □)) Eq.refl ⟩
      (SemiDirect.Z ^ k • (SemiDirect.Z ^ p-1) ^ k) • (SemiDirect.S • SemiDirect.S)
        ≈⟨ cleft ZZ' ⟩
      ε • (SemiDirect.S • SemiDirect.S)
        ≈⟨ left-unit ⟩
      SemiDirect.S • SemiDirect.S ∎
  h-well-defined {₁₊ n} comm-X-Z = begin
    (h ʷ) (X • Z)                  ≈⟨ cong (h-X {n}) (h-Z {n}) ⟩
    SemiDirect.X • SemiDirect.Z    ≈⟨ sym (axiom (left XZ.comm-Z-X)) ⟩
    SemiDirect.Z • SemiDirect.X    ≈⟨ sym (cong (h-Z {n}) (h-X {n})) ⟩
    (h ʷ) (Z • X) ∎
    where
    open PB (SemiDirect._QRel,_===_ (₁₊ n))
    open PP (SemiDirect._QRel,_===_ (₁₊ n))
    open SR word-setoid
  h-well-defined {₂₊ n} semi-M↑CZ rewrite lemma-h↑ (Mg {n}) = begin
      ((h ʷ) (Mg {n})) SemiDirect.↑ • SemiDirect.CZ                       ≈⟨ cong (h-Mg↑ {n}) refl ⟩
      ([ Sim.Mg {n} ]ᵣ) SemiDirect.↑ • SemiDirect.CZ                   ≈⟨ bareM ⟩
      SemiDirect.CZ ^ (toℕ g) • ([ Sim.Mg {n} ]ᵣ) SemiDirect.↑        ≈⟨ cong refl (sym (h-Mg↑ {n})) ⟩
      SemiDirect.CZ ^ (toℕ g) • ((h ʷ) (Mg {n})) SemiDirect.↑        ≡⟨ Eq.cong (_• ((h ʷ) (Mg {n})) SemiDirect.↑) (Eq.sym (lemma-fʷ-w^n {f = h} {w = CZ} (toℕ g))) ⟩
      (h ʷ) (CZ^ g) • ((h ʷ) (Mg {n})) SemiDirect.↑ ∎
    where
    open PB (SemiDirect._QRel,_===_ (₂₊ n))
    open PP (SemiDirect._QRel,_===_ (₂₊ n))
    open SR word-setoid
    bareM : ([ Sim.Mg {n} ]ᵣ) SemiDirect.↑ • SemiDirect.CZ ≈ SemiDirect.CZ ^ (toℕ g) • ([ Sim.Mg {n} ]ᵣ) SemiDirect.↑
    bareM = begin
      ([ Sim.Mg {n} ]ᵣ) SemiDirect.↑ • SemiDirect.CZ           ≡⟨ Eq.cong (_• SemiDirect.CZ) (SemiDirect.lemma-[]ᵣ-↑ (Sim.Mg {n})) ⟩
      [ Sim.Mg {n} Sym.↑ ]ᵣ • SemiDirect.CZ                    ≈⟨ axiom (right (Sim.srel Sim.semi-M↑CZ)) ⟩
      [ Sym.CZ ^ toℕ g ]ᵣ • [ Sim.Mg {n} Sym.↑ ]ᵣ             ≡⟨ Eq.cong₂ _•_ (SemiDirect.lemma-[]ᵣ^k Sym.CZ (toℕ g)) (Eq.sym (SemiDirect.lemma-[]ᵣ-↑ (Sim.Mg {n}))) ⟩
      SemiDirect.CZ ^ (toℕ g) • ([ Sim.Mg {n} ]ᵣ) SemiDirect.↑ ∎
  h-well-defined {₂₊ n} semi-M↓CZ = begin
      (h ʷ) (Mg {₁₊ n}) • SemiDirect.CZ              ≈⟨ cong (h-Mg {₁₊ n}) refl ⟩
      [ Sim.Mg {₁₊ n} ]ᵣ • SemiDirect.CZ            ≈⟨ bareM↓ ⟩
      SemiDirect.CZ ^ (toℕ g) • [ Sim.Mg {₁₊ n} ]ᵣ  ≈⟨ cong refl (sym (h-Mg {₁₊ n})) ⟩
      SemiDirect.CZ ^ (toℕ g) • (h ʷ) (Mg {₁₊ n})   ≡⟨ Eq.cong (_• (h ʷ) (Mg {₁₊ n})) (Eq.sym (lemma-fʷ-w^n {f = h} {w = CZ} (toℕ g))) ⟩
      (h ʷ) (CZ^ g) • (h ʷ) (Mg {₁₊ n}) ∎
    where
    open PB (SemiDirect._QRel,_===_ (₂₊ n))
    open PP (SemiDirect._QRel,_===_ (₂₊ n))
    open SR word-setoid
    bareM↓ : [ Sim.Mg {₁₊ n} ]ᵣ • SemiDirect.CZ ≈ SemiDirect.CZ ^ (toℕ g) • [ Sim.Mg {₁₊ n} ]ᵣ
    bareM↓ = begin
      [ Sim.Mg {₁₊ n} ]ᵣ • SemiDirect.CZ            ≈⟨ axiom (right (Sim.srel Sim.semi-M↓CZ)) ⟩
      [ Sym.CZ ^ toℕ g ]ᵣ • [ Sim.Mg {₁₊ n} ]ᵣ      ≡⟨ Eq.cong (_• [ Sim.Mg {₁₊ n} ]ᵣ) (SemiDirect.lemma-[]ᵣ^k Sym.CZ (toℕ g)) ⟩
      SemiDirect.CZ ^ (toℕ g) • [ Sim.Mg {₁₊ n} ]ᵣ ∎
  h-well-defined {₂₊ n} rel-X↑-CZ = begin
    (h ʷ) (CZ • (X ↑))
      ≈⟨ cong refl h-X↑ ⟩
    SemiDirect.CZ • (SemiDirect.X SemiDirect.↑)
      ≈⟨ axiom (mid (comm (XZ.X-gen XZ.↥) Sym.CZ-gen)) ⟩
    (SemiDirect.X SemiDirect.↑ • SemiDirect.Z) • SemiDirect.CZ
      ≈⟨ assoc ⟩
    SemiDirect.X SemiDirect.↑ • (SemiDirect.Z • SemiDirect.CZ)
      ≈⟨ sym (cong h-X↑ (cong (h-Z {₁₊ n}) refl)) ⟩
    (h ʷ) ((X ↑) • (Z ↓) • CZ) ∎
    where
    open PB (SemiDirect._QRel,_===_ (₂₊ n))
    open PP (SemiDirect._QRel,_===_ (₂₊ n))
    open SR word-setoid
    h-X↑ : (h ʷ) (X {n} ↑) ≈ SemiDirect.X SemiDirect.↑
    h-X↑ = trans (refl' (lemma-h↑ (X {n}))) (SemiDirect.lemma-cong↑ {₁₊ n} _ _ (h-X {n}))
  h-well-defined {₂₊ n} rel-X↓-CZ = begin
    (h ʷ) (CZ • (X ↓))
      ≈⟨ cong refl (h-X {₁₊ n}) ⟩
    SemiDirect.CZ • SemiDirect.X
      ≈⟨ axiom (mid (comm XZ.X-gen Sym.CZ-gen)) ⟩
    (SemiDirect.X • SemiDirect.Z SemiDirect.↑) • SemiDirect.CZ
      ≈⟨ assoc ⟩
    SemiDirect.X • (SemiDirect.Z SemiDirect.↑ • SemiDirect.CZ)
      ≈⟨ sym (cong (h-X {₁₊ n}) (cong h-Z↑ refl)) ⟩
    (h ʷ) ((X ↓) • (Z ↑) • CZ) ∎
    where
    open PB (SemiDirect._QRel,_===_ (₂₊ n))
    open PP (SemiDirect._QRel,_===_ (₂₊ n))
    open SR word-setoid
    h-Z↑ : (h ʷ) (Z {n} ↑) ≈ SemiDirect.Z SemiDirect.↑
    h-Z↑ = trans (refl' (lemma-h↑ (Z {n}))) (SemiDirect.lemma-cong↑ {₁₊ n} _ _ (h-Z {n}))
  h-well-defined order-CZ = begin
    (h ʷ) (CZ ^ p)   ≡⟨ lemma-fʷ-w^n {f = h} {w = CZ} p ⟩
    (h ʷ) CZ ^ p     ≡⟨ Eq.sym (SemiDirect.lemma-[]ᵣ^k Sym.CZ p) ⟩
    [ Sym.CZ ^ p ]ᵣ  ≈⟨ PB.axiom (right (Sim.srel Sim.order-CZ)) ⟩
    ε ∎
    where open SR (PP.word-setoid (SemiDirect._QRel,_===_ _))
  h-well-defined comm-CZ-S↓ = PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong (lemma-CZ-Zk _) PB.refl) (PB.trans PB.assoc (PB.trans (PB.cong PB.refl (PB.axiom (right (Sim.srel Sim.comm-CZ-S↓)))) (PB.sym PB.assoc))))
  -- (h ʷ) (S ↑) and ((h ʷ) S) ↑ are already definitionally equal here, so the
  -- old `rewrite lemma-h↑ S` was a no-op — and one --without-K rejects, since
  -- it would match refl on a reflexive equation.
  h-well-defined comm-CZ-S↑ = PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong (lemma-CZ-Z↑k _) PB.refl) (PB.trans PB.assoc (PB.trans (PB.cong PB.refl (PB.axiom (right (Sim.srel Sim.comm-CZ-S↑)))) (PB.sym PB.assoc))))
  h-well-defined {₂₊ n} selinger-c10 = begin
      (h ʷ) (CZ • (H ↑) • CZ)
        ≈⟨ axiom (right (Sim.srel Sim.selinger-c10)) ⟩
      [ Sym.S⁻¹ Sym.↑ ]ᵣ • [ Sym.H Sym.↑ ]ᵣ • [ Sym.S⁻¹ Sym.↑ ]ᵣ • [ Sym.CZ ]ᵣ • [ Sym.H Sym.↑ ]ᵣ • [ Sym.S⁻¹ Sym.↑ ]ᵣ • [ Sym.S⁻¹ ]ᵣ
        ≈⟨ cong (conv↑ {n}) (cong refl (cong (conv↑ {n}) (cong refl (cong refl (cong (conv↑ {n}) (conv↓ {₁₊ n})))))) ⟩
      (h ʷ) ((R ↑) ^ p-1 • (H ↑) • (R ↑) ^ p-1 • CZ • (H ↑) • (R ↑) ^ p-1 • (R ↓) ^ p-1) ∎
    where
    open PB (SemiDirect._QRel,_===_ (₂₊ n))
    open PP (SemiDirect._QRel,_===_ (₂₊ n))
    open SR word-setoid
  h-well-defined {₂₊ n} selinger-c11 = begin
      (h ʷ) (CZ • (H ↓) • CZ)
        ≈⟨ axiom (right (Sim.srel Sim.selinger-c11)) ⟩
      [ Sym.S⁻¹ ]ᵣ • [ Sym.H ]ᵣ • [ Sym.S⁻¹ ]ᵣ • [ Sym.CZ ]ᵣ • [ Sym.H ]ᵣ • [ Sym.S⁻¹ ]ᵣ • [ Sym.S⁻¹ Sym.↑ ]ᵣ
        ≈⟨ cong (conv↓ {₁₊ n}) (cong refl (cong (conv↓ {₁₊ n}) (cong refl (cong refl (cong (conv↓ {₁₊ n}) (conv↑ {n})))))) ⟩
      (h ʷ) ((R ↓) ^ p-1 • (H ↓) • (R ↓) ^ p-1 • CZ • (H ↓) • (R ↓) ^ p-1 • (R ↑) ^ p-1) ∎
    where
    open PB (SemiDirect._QRel,_===_ (₂₊ n))
    open PP (SemiDirect._QRel,_===_ (₂₊ n))
    open SR word-setoid
  h-well-defined {₃₊ n} selinger-c12 rewrite lemma-h↑ (CZ {n}) = begin
      SemiDirect.CZ {n} SemiDirect.↑ • SemiDirect.CZ     ≡⟨ Eq.cong (_• SemiDirect.CZ) (SemiDirect.lemma-[]ᵣ-↑ (Sym.CZ {n})) ⟩
      [ Sym.CZ {n} Sym.↑ ]ᵣ • SemiDirect.CZ              ≈⟨ axiom (right (Sim.srel Sim.selinger-c12)) ⟩
      SemiDirect.CZ • [ Sym.CZ {n} Sym.↑ ]ᵣ             ≡⟨ Eq.cong (SemiDirect.CZ •_) (Eq.sym (SemiDirect.lemma-[]ᵣ-↑ (Sym.CZ {n}))) ⟩
      SemiDirect.CZ • SemiDirect.CZ {n} SemiDirect.↑ ∎
    where
    open PB (SemiDirect._QRel,_===_ (₃₊ n))
    open PP (SemiDirect._QRel,_===_ (₃₊ n))
    open SR word-setoid
  h-well-defined {n} {w} {v} selinger-c13 = PB.axiom (right (Sim.srel Sim.selinger-c13))
  h-well-defined {n} {w} {v} selinger-c14 = PB.axiom (right (Sim.srel Sim.selinger-c14))
  h-well-defined {n} {w} {v} selinger-c15 = PB.axiom (right (Sim.srel Sim.selinger-c15))
  -- comm-H/comm-S/comm-CZ are framework instances now, so these match
  -- through comm₁/comm₂ rather than on a constructor of their own.
  h-well-defined {₂₊ n} (comm₁ H-gate x) = lemma-w↑H (h x)
  h-well-defined {₂₊ n} (comm₁ S-gate x) = PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong (lemma-w↑Zk (h x) _) PB.refl) (PB.trans PB.assoc (PB.trans (PB.cong PB.refl (lemma-w↑S (h x))) (PB.sym PB.assoc))))
  h-well-defined {₃₊ n} (comm₂ CZ-gate x) = lemma-w↑↑CZ (h x)
  h-well-defined (cong↑ {n'} {w'} {v'} eq) rewrite lemma-h↑ w' | lemma-h↑ v' = SemiDirect.lemma-cong↑ _ _ (h-well-defined eq)

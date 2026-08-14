{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; setoid ; module ≡-Reasoning ; _≢_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_,_ ; proj₁ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Fin hiding (_+_ ; _-_)

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Circuit.Base
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Data.Nat.Primality
open import Data.Nat.GCD
open Bézout
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where


open Primitive-Root-Modp' g* g-gen

module Symplectic-Simplified where

open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen as NSim
-- This development takes from Symplectic only the *generator layer* — the
-- gate set Gen and the derived words (S, H, CZ, M, S^, ⊤⊥, …), which the
-- original and the simplified presentations share.  Everything about the
-- relation comes from Simplified instead, so the whole relation layer of
-- Symplectic is hidden here: its axioms (which are also exported as
-- top-level aliases, and would clash with the Clifford relation's
-- constructors below), the structural rules, and the raw relation itself.
-- Reach for the symplectic version as NSim.Symplectic.… if ever needed.
open Symplectic hiding
  ( _QRel,_===_ ; M ; M₁ ; XM ; ZM ; module Base
  ; order-S ; order-H ; order-SH
  ; semi-M↑CZ ; semi-M↓CZ ; order-CZ
  ; comm-CZ-S↓ ; comm-CZ-S↑
  ; selinger-c10 ; selinger-c11 ; selinger-c12
  ; selinger-c13 ; selinger-c14 ; selinger-c15
  ; comm-H ; comm-S ; comm-CZ ; comm-HHS
  ; M-mul ; semi-MS
  ; srel ; cong↑ ; comm₁ ; comm₂ ; lemma-cong↑ ) public

1/2 = ((₂ , λ ()) ⁻¹) .proj₁

-1/2 = - ((₂ , λ ()) ⁻¹) .proj₁


module Clifford-Relations where

  private variable
    n : ℕ
    k : ℤ ₚ

  Z : ∀ {n} -> Word (Gen (₁₊ n))
  Z = H • H • S • H • H • S⁻¹
  
  X : ∀ {n} -> Word (Gen (₁₊ n))
  X = H • S • H • H • S⁻¹ • H

  Z⁻¹ : ∀ {n} -> Word (Gen (₁₊ n))
  Z⁻¹ = Z ^ p-1

  X⁻¹ : ∀ {n} -> Word (Gen (₁₊ n))
  X⁻¹ = X ^ p-1


  Z^ : ℤ ₚ ->  ∀ {n} -> Word (Gen (₁₊ n))
  Z^ k = Z ^ toℕ k

  X^ : ℤ ₚ ->  ∀ {n} -> Word (Gen (₁₊ n))
  X^ k = X ^ toℕ k

  R : ∀ {n} -> Word (Gen (₁₊ n))
  R = S • Z^ 1/2
  R^ : ∀ {n} ->  ℤ ₚ ->  Word (Gen (₁₊ n))
  R^ k = R ^ toℕ k

  -- The shape both multiplier words have, over R rather than S: this is
  -- Gates' SHS with S^ replaced by R^, which is what makes the identity
  -- on words a morphism to Simplified-V1 (V1 states everything over
  -- R = S • Z^½).  M and XM are the two ways of filling it from a unit
  -- and its inverse, exactly as Gates' ZM and XM are.
  RHR : ∀ {n} -> ℤ ₚ -> ℤ ₚ -> Word (Gen (₁₊ n))
  RHR a b = R^ a • H • R^ b • H • R^ a • H

  M : ∀ {n} -> ℤ* ₚ -> Word (Gen (₁₊ n))
  M x' = RHR x x⁻¹
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

  XM : ∀ {n} -> ℤ* ₚ -> Word (Gen (₁₊ n))
  XM x' = RHR x⁻¹ x
    where
    x = x' .proj₁
    x⁻¹ = ((x' ⁻¹) .proj₁ )

  -- The two fillings are exchanged by inversion.  This is the R-spelled
  -- copy of Gates' XM≡ZM⁻¹, with the same one-line proof: over RHR it is
  -- one congruence in the second exponent, since (x ⁻¹) ⁻¹ is x.  It is
  -- the bridge between the axioms, which are stated over XMg, and the
  -- Mg forms that everything downstream is written in.
  XM≡M⁻¹ : ∀ {n} (x : ℤ* ₚ) → XM {n} x ≡ M (x ⁻¹)
  XM≡M⁻¹ x = Eq.cong (RHR ((x ⁻¹) .proj₁)) (Eq.sym (inv-involutive x))

  M₁ : ∀ {n} -> Word (Gen (₁₊ n))
  M₁ = M (₁ , λ ())

  M₋₁ : ∀ {n} -> Word (Gen (₁₊ n))
  M₋₁ = M -'₁

  Mg :  ∀ {n} -> Word (Gen (₁₊ n))
  Mg = M g′

  Mg^ : ℤ ₚ ->  ∀ {n} -> Word (Gen (₁₊ n))
  Mg^ k = Mg ^ toℕ k

  XMg :  ∀ {n} -> Word (Gen (₁₊ n))
  XMg = XM g′

  XMg^ : ℤ ₚ ->  ∀ {n} -> Word (Gen (₁₊ n))
  XMg^ k = XMg ^ toℕ k


  -- Group-specific axioms only.  The structural rules — congruence
  -- under _↑, and a gate at the bottom commuting with anything shifted
  -- up past it — are not repeated here: they are the same for every
  -- circuit presentation and come from Lift-Relation below.
  --
  -- X • Z === Z • X is NOT among them: it is derivable from order-SH
  -- and M-power (which make both (S • H) ^ 3 and (R • H) ^ 3 trivial,
  -- for the two elements S and R = S • Z^½ that differ by one Pauli).
  -- See Lemmas1b.lemma-comm-X-Z in LemmasXZ.
  module Base where
    infix 4 _SRel,_===_
    data _SRel,_===_ : (n : ℕ) → WRel (Gen n) where

      order-S :      (₁₊ n) SRel,  S ^ p === ε
      order-H :      (₁₊ n) SRel,  H ^ 2 === M₋₁
      M-power : ∀ k → (₁₊ n) SRel,  XMg^ k === XM (g^ k)
      semi-MR :      (₁₊ n) SRel,  XMg • R^ (g * g) === R • XMg
      order-SH :     (₁₊ n) SRel,  (S • H) ^ 3 === ε
      comm-HHSHHS :  (₁₊ n) SRel,  H • H • S • H • H • S === S • H • H • S • H • H

      order-CZ :     (₂₊ n) SRel,  CZ ^ p === ε
      order-Ex :     (₂₊ n) SRel,  Ex ^ 2 === ε
      comm-CZ-S↑ :   (₂₊ n) SRel,  CZ • S ↑ === S ↑ • CZ
      semi-M↑CZ :    (₂₊ n) SRel,  XMg ↑ • CZ^ g === CZ • XMg ↑
      semi-Ex-S↑ :   (₂₊ n) SRel,  Ex • S ↑ === S ↓ • Ex
      semi-Ex-H↑ :   (₂₊ n) SRel,  Ex • H ↑ === H ↓ • Ex
      blake-c12 :    (₂₊ n) SRel,  (S ^ p-1) ↑ • (S ^ p-1) ↓ • CX ^ p-1 • S ↓ • CX === CZ

      yang-baxter :  (₃₊ n) SRel,  Ex ↑ • Ex ↓ • Ex ↑ === Ex ↓ • Ex ↑ • Ex ↓
      cz-slide :     (₃₊ n) SRel,  Ex ↓ • Ex ↑ • CZ === CZ ↑ • Ex ↓ • Ex ↑
      semi-CX↑-CZ↓ : (₃₊ n) SRel,  CZ ↓ • CX ↑ === CZ02 • CX ↑ • CZ ↓

  -- Full relation: the axioms above plus the structural rules.
      -- The swap commuting with CZ is NOT an axiom: it is Lemma 2 of
      -- ProgressReport14, derived in Paper-V0.Lemmas as lemma-Ex-CZ from
      -- semi-Ex-H↑ and the two ways of writing the swap.  Figure 1 has no
      -- two-wire rule for it, and none is needed.

      -- NEITHER Pauli-versus-CZ rule is an axiom.  Figure 1 states both,
      -- but the swap derives either from the other, and the survivor is
      -- a consequence of blake-c12 and the multiplier calculus: see
      -- Paper-V0.Lemmas.Ex-Conjugation.lemma-rel-X↓-CZ (and its mirror
      -- lemma-rel-X↑-CZ).  A deliberate departure from Figure 1, and the
      -- second one after rel-X↑-CZ went: 16 group-specific axioms remain.
  
  private module SC = Circuit.Base SympGate
  private module LR = SC.Lift-Relation Base._SRel,_===_

  infix 4 _QRel,_===_
  _QRel,_===_ : (n : ℕ) → WRel (Gen n)
  _QRel,_===_ = LR._VRel,_===_

  -- Structural rules, exported directly.  lemma-cong↑ is now the
  -- framework's, so the copy that used to live in Lemmas-Clifford is gone.
  open LR public using (srel ; cong↑ ; comm₁ ; comm₂ ; lemma-cong↑)

  -- Every axiom keeps the name it had before the split, as a pattern
  -- synonym rather than a definition, so that call sites in BOTH
  -- expression and pattern position go on working untouched.
  -- Each binds {n} explicitly, so that the old spellings `order-H` and
  -- `order-H {n = n}` both still elaborate.
  pattern order-S = srel (Base.order-S)
  pattern order-H = srel (Base.order-H)
  pattern M-power k = srel (Base.M-power k)
  pattern semi-MR = srel (Base.semi-MR)
  pattern order-SH = srel (Base.order-SH)
  pattern comm-HHSHHS = srel (Base.comm-HHSHHS)

  pattern order-CZ = srel (Base.order-CZ)
  pattern order-Ex = srel (Base.order-Ex)
  pattern comm-CZ-S↑ = srel (Base.comm-CZ-S↑)
  pattern semi-M↑CZ = srel (Base.semi-M↑CZ)

  pattern semi-Ex-S↑ = srel (Base.semi-Ex-S↑)
  pattern semi-Ex-H↑ = srel (Base.semi-Ex-H↑)

  pattern blake-c12 = srel (Base.blake-c12)

  pattern yang-baxter = srel (Base.yang-baxter)
  pattern cz-slide = srel (Base.cz-slide)
  pattern semi-CX↑-CZ↓ = srel (Base.semi-CX↑-CZ↓)

  -- The three structural commutations that used to be axioms are
  -- instances of comm₁/comm₂ now.  These are definitions, not pattern
  -- synonyms: as a synonym the implicit x is inserted as a meta that the
  -- goal does not always pin down, and expression-position uses (of
  -- which there are many, mostly in the commute tables) then fail to
  -- elaborate.  Pattern-position uses match on comm₁/comm₂ directly.
  comm-H : ∀ {n} {x : Gen (₁₊ n)} → (₂₊ n) QRel, [ x ↥ ]ʷ • H === H • [ x ↥ ]ʷ
  comm-H {x = x} = comm₁ H-gate x

  comm-S : ∀ {n} {x : Gen (₁₊ n)} → (₂₊ n) QRel, [ x ↥ ]ʷ • S === S • [ x ↥ ]ʷ
  comm-S {x = x} = comm₁ S-gate x

  comm-CZ : ∀ {n} {x : Gen (₁₊ n)} → (₃₊ n) QRel, [ x ↥ ↥ ]ʷ • CZ === CZ • [ x ↥ ↥ ]ʷ
  comm-CZ {x = x} = comm₂ CZ-gate x


module Lemmas-Clifford where

  open Clifford-Relations
  
  -- lemma-cong↑ comes from Circuit.Base.Lift-Relation now, re-exported
  -- by Clifford-Relations; the hand-written copy that stood here was
  -- the same induction and has been dropped.

  lemma-^-↑ : ∀ {n} (w : Word (Gen n)) k → w ↑ ^ k ≡ (w ^ k) ↑
  lemma-^-↑ w ₀ = auto
  lemma-^-↑ w ₁ = auto
  lemma-^-↑ w (₂₊ k) = begin
    (w ↑) • (w ↑) ^ ₁₊ k ≡⟨ Eq.cong ((w ↑) •_) (lemma-^-↑ w (₁₊ k)) ⟩
    (w ↑) • (w ^ ₁₊ k) ↑ ≡⟨ auto ⟩
    ((w • w ^ ₁₊ k) ↑) ∎
    where open ≡-Reasoning


  lemma-cong↓-S^ : ∀ {n} k -> let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ^ k) ↓ ≈↓ S ^ k
  lemma-cong↓-S^ {n} ₀ = PB.refl
  lemma-cong↓-S^ {n} ₁ = PB.refl
  lemma-cong↓-S^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S^ {n} (₁₊ k))

  lemma-cong↑-S^ : ∀ {n} k -> let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↑_) using () in
    (S ^ k) ↑ ≈↑ S ↑ ^ k
  lemma-cong↑-S^ {n} ₀ = PB.refl
  lemma-cong↑-S^ {n} ₁ = PB.refl
  lemma-cong↑-S^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↑-S^ {n} (₁₊ k))


  lemma-cong↓-S↓^ : ∀ {n} k -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ↓ ^ k) ↓ ≈↓ S ↓ ^ k
  lemma-cong↓-S↓^ {n} ₀ = PB.refl
  lemma-cong↓-S↓^ {n} ₁ = PB.refl
  lemma-cong↓-S↓^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S↓^ {n} (₁₊ k))

  lemma-cong↓-S↑^ : ∀ {n} k -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    ((S ↑) ^ k) ↓ ≈↓ (S ↑) ^ k
  lemma-cong↓-S↑^ {n} ₀ = PB.refl
  lemma-cong↓-S↑^ {n} ₁ = PB.refl
  lemma-cong↓-S↑^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S↑^ {n} (₁₊ k))


  lemma-cong↓-S^↓ : ∀ {n} k -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ^ k) ↓ ↓ ≈↓ (S ^ k) ↓
  lemma-cong↓-S^↓ {n} ₀ = PB.refl
  lemma-cong↓-S^↓ {n} ₁ = PB.refl
  lemma-cong↓-S^↓ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S^↓ {n} (₁₊ k))

  lemma-cong↓-S^↑ : ∀ {n} k -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (S ^ k) ↑ ↓ ≈↓ (S ^ k) ↑
  lemma-cong↓-S^↑ {n} ₀ = PB.refl
  lemma-cong↓-S^↑ {n} ₁ = PB.refl
  lemma-cong↓-S^↑ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-S^↑ {n} (₁₊ k))

  lemma-cong↓-H^ : ∀ {n} k -> let open PB ((₂₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (H ^ k) ↓ ≈↓ H ^ k
  lemma-cong↓-H^ {n} ₀ = PB.refl
  lemma-cong↓-H^ {n} ₁ = PB.refl
  lemma-cong↓-H^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-H^ {n} (₁₊ k))

  lemma-cong↓-CZ^ : ∀ {n} k -> let open PB ((₃₊ n) QRel,_===_) renaming (_≈_ to _≈↓_) using () in
    (CZ ^ k) ↓ ≈↓ CZ ^ k
  lemma-cong↓-CZ^ {n} ₀ = PB.refl
  lemma-cong↓-CZ^ {n} ₁ = PB.refl
  lemma-cong↓-CZ^ {n} (₂₊ k) = PB.cong PB.refl (lemma-cong↓-CZ^ {n} (₁₊ k))

  lemma-↑↓ : ∀ {n} (w : Word (Gen n)) → w ↑ ↓ ≡ w ↓ ↑
  lemma-↑↓ [ x ]ʷ = auto
  lemma-↑↓ ε = auto
  lemma-↑↓ (w • w₁) = Eq.cong₂ _•_ (lemma-↑↓ w) (lemma-↑↓ w₁)

  lemma-↑^ : ∀ {n} k (w : Word (Gen n)) → (w ^ k) ↑ ≡ w ↑ ^ k
  lemma-↑^ {n} ₀ w = auto
  lemma-↑^ {n} ₁ w = auto
  lemma-↑^ {n} (₂₊ k) w = Eq.cong₂ _•_ auto (lemma-↑^ {n} (₁₊ k) w)


  -- (There was a lemma-↓^ here, the same statement for _↓.  It is not
  -- needed: _↓ is the identity function on circuits, so (w ^ k) ↓ and
  -- w ↓ ^ k are the same term and nothing has to be stepped over.)

  lemma-comm-S-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    S • w ↑ ≈ w ↑ • S
    
  lemma-comm-S-w↑ {n} [ x ]ʷ = sym (axiom comm-S)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-S-w↑ {n} ε = trans right-unit (sym left-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-S-w↑ {n} (w • w₁) = begin
    S • ((w • w₁) ↑) ≈⟨ refl ⟩
    S • (w ↑ • w₁ ↑) ≈⟨ sym assoc ⟩
    (S • w ↑) • w₁ ↑ ≈⟨ cong (lemma-comm-S-w↑ w) refl ⟩
    (w ↑ • S) • w₁ ↑ ≈⟨ assoc ⟩
    w ↑ • S • w₁ ↑ ≈⟨ cong refl (lemma-comm-S-w↑ w₁) ⟩
    w ↑ • w₁ ↑ • S ≈⟨ sym assoc ⟩
    ((w • w₁) ↑) • S ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid

  lemma-comm-Sᵏ-w↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in
    
    S ^ k • w ↑ ≈ w ↑ • S ^ k
    
  lemma-comm-Sᵏ-w↑ {n} ₀ w = trans left-unit (sym right-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Sᵏ-w↑ {n} ₁ w = lemma-comm-S-w↑ w
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Sᵏ-w↑ {n} (₂₊ k) w = begin
    (S • S ^ ₁₊ k) • (w ↑) ≈⟨ assoc ⟩
    S • S ^ ₁₊ k • (w ↑) ≈⟨ cong refl (lemma-comm-Sᵏ-w↑ (₁₊ k) w) ⟩
    S • (w ↑) • S ^ ₁₊ k ≈⟨ sym assoc ⟩
    (S • w ↑) • S ^ ₁₊ k ≈⟨ cong (lemma-comm-S-w↑ w) refl ⟩
    (w ↑ • S) • S ^ ₁₊ k ≈⟨ assoc ⟩
    (w ↑) • S • S ^ ₁₊ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


  lemma-comm-H-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
    H • w ↑ ≈ w ↑ • H
    
  lemma-comm-H-w↑ {n} [ x ]ʷ = sym (axiom comm-H)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-H-w↑ {n} ε = trans right-unit (sym left-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-H-w↑ {n} (w • w₁) = begin
    H • ((w • w₁) ↑) ≈⟨ refl ⟩
    H • (w ↑ • w₁ ↑) ≈⟨ sym assoc ⟩
    (H • w ↑) • w₁ ↑ ≈⟨ cong (lemma-comm-H-w↑ w) refl ⟩
    (w ↑ • H) • w₁ ↑ ≈⟨ assoc ⟩
    w ↑ • H • w₁ ↑ ≈⟨ cong refl (lemma-comm-H-w↑ w₁) ⟩
    w ↑ • w₁ ↑ • H ≈⟨ sym assoc ⟩
    ((w • w₁) ↑) • H ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid



  lemma-comm-Hᵏ-w↑ : ∀ {n} k w → let open PB ((₂₊ n) QRel,_===_) in
    
    H ^ k • w ↑ ≈ w ↑ • H ^ k
    
  lemma-comm-Hᵏ-w↑ {n} ₀ w = trans left-unit (sym right-unit)
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Hᵏ-w↑ {n} ₁ w = lemma-comm-H-w↑ w
    where
    open PB ((₂₊ n) QRel,_===_)
  lemma-comm-Hᵏ-w↑ {n} (₂₊ k) w = begin
    (H • H ^ ₁₊ k) • (w ↑) ≈⟨ assoc ⟩
    H • H ^ ₁₊ k • (w ↑) ≈⟨ cong refl (lemma-comm-Hᵏ-w↑ (₁₊ k) w) ⟩
    H • (w ↑) • H ^ ₁₊ k ≈⟨ sym assoc ⟩
    (H • w ↑) • H ^ ₁₊ k ≈⟨ cong (lemma-comm-H-w↑ w) refl ⟩
    (w ↑ • H) • H ^ ₁₊ k ≈⟨ assoc ⟩
    (w ↑) • H • H ^ ₁₊ k ∎
    where
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid


  lemma-comm-Z-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
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
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc


  lemma-comm-X-w↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in
    
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
    open PB ((₂₊ n) QRel,_===_)
    open PP ((₂₊ n) QRel,_===_)
    open SR word-setoid
    open Pattern-Assoc



  lemma-comm-CZ-w↑ : ∀ {n} w → let open PB ((₃₊ n) QRel,_===_) in
    
    CZ • w ↑ ↑ ≈ w ↑ ↑ • CZ
    
  lemma-comm-CZ-w↑ {n} [ x ]ʷ = sym (axiom comm-CZ)
    where
    open PB ((₃₊ n) QRel,_===_)
  lemma-comm-CZ-w↑ {n} ε = trans right-unit (sym left-unit)
    where
    open PB ((₃₊ n) QRel,_===_)
  lemma-comm-CZ-w↑ {n} (w • w₁) = begin
    CZ • ((w • w₁) ↑ ↑) ≈⟨ refl ⟩
    CZ • (w ↑ ↑ • w₁ ↑ ↑) ≈⟨ sym assoc ⟩
    (CZ • w ↑ ↑) • w₁ ↑ ↑ ≈⟨ cong (lemma-comm-CZ-w↑ w) refl ⟩
    (w ↑ ↑ • CZ) • w₁ ↑ ↑ ≈⟨ assoc ⟩
    w ↑ ↑ • CZ • w₁ ↑ ↑ ≈⟨ cong refl (lemma-comm-CZ-w↑ w₁) ⟩
    w ↑ ↑ • w₁ ↑ ↑ • CZ ≈⟨ sym assoc ⟩
    ((w • w₁) ↑ ↑) • CZ ∎
    where
    open PB ((₃₊ n) QRel,_===_)
    open PP ((₃₊ n) QRel,_===_)
    open SR word-setoid

  aux-MM : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) in ∀ {x y : ℤ ₚ} (nzx : x ≢ ₀) (nzy : y ≢ ₀) -> x ≡ y -> M (x , nzx) ≈ M (y , nzy)
  aux-MM {n} {x} {y} nz1 nz2 eq rewrite eq = refl
    where
    open PB ((₁₊ n) QRel,_===_)



  lemma-Induction : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) in ∀ {w v v'} -> w • v ≈ v' • w -> ∀ k -> w • v ^ k ≈ v' ^ k • w
  lemma-Induction {n} {w} {v} {v'} eq k@0 = trans right-unit (sym left-unit)
    where open PB ((₁₊ n) QRel,_===_)
  lemma-Induction {n} {w} {v} {v'} eq k@1 = eq
  lemma-Induction {n} {w} {v} {v'} eq k@(₂₊ k') = begin
    w • v ^ k ≈⟨ sym assoc ⟩
    (w • v) • v ^ (₁₊ k') ≈⟨ (cleft eq) ⟩
    (v' • w) • v ^ (₁₊ k') ≈⟨ assoc ⟩
    v' • w • v ^ (₁₊ k') ≈⟨ (cright lemma-Induction eq (₁₊ k')) ⟩
    v' • v' ^ (₁₊ k') • w ≈⟨ sym assoc ⟩
    v' ^ k • w ∎
    where
    open PP ((₁₊ n) QRel,_===_)
    open PB ((₁₊ n) QRel,_===_)
    open SR word-setoid


  lemma-Inductionˡ : ∀ {n} -> let open PB ((₁₊ n) QRel,_===_) in ∀ {w w' v} -> w • v ≈ v • w' -> ∀ k -> w ^ k • v ≈ v • w' ^ k
  lemma-Inductionˡ {n} {w} {w'} {v} eq k@0 = trans left-unit (sym right-unit)
    where open PB ((₁₊ n) QRel,_===_)
  lemma-Inductionˡ {n} {w} {w'} {v} eq k@1 = eq
  lemma-Inductionˡ {n} {w} {w'} {v} eq k@(₁₊ k'@(₁₊ k'')) = begin
    w ^ k • v ≈⟨ assoc ⟩
    w • w ^ k' • v ≈⟨ (cright lemma-Inductionˡ eq k') ⟩
    w • v • w' ^ k' ≈⟨ sym assoc ⟩
    (w • v) • w' ^ k' ≈⟨ (cleft eq) ⟩
    (v • w') • w' ^ k' ≈⟨ assoc ⟩
    v • w' ^ k ∎
    where
    open PP ((₁₊ n) QRel,_===_)
    open PB ((₁₊ n) QRel,_===_)
    open SR word-setoid



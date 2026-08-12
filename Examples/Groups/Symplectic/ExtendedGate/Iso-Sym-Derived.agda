{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq


open import Function using (_∘_)

open import Data.Product using (_,_ ; proj₁)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe
open import Data.Sum using ([_,_])

open import Word.Base as WB hiding (wfoldl)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)


open import Data.Fin using (toℕ ; fromℕ)
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality



module Examples.Groups.Symplectic.ExtendedGate.Iso-Sym-Derived (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where




private
  variable
    n : ℕ


open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime as SD
open import Examples.Groups.Symplectic.ExtendedGate.Lemmas-2Qupit p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.NF1 p-2 p-prime
open Lemmas-2Q 2
open Symplectic-Derived-Gen
open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Properties p-2 p-prime
open Normal-Form1

module Sym  = Symplectic
module Sym'  = Lemmas-Sym
module SymDerived  = Symplectic-Derived-Gen
open Symplectic renaming (Gen to Gen₁ ; _QRel,_===_ to _QRel,_===₁_) using ()
open SymDerived renaming (Gen to Gen₂ ; _QRel,_===_ to _QRel,_===₂_) using ()
open Symplectic-GroupLike renaming (grouplike to grouplike₁) using ()
open Symplectic-Derived-GroupLike renaming (grouplike to grouplike₂) using ()


f : Sym.Gen n → SymDerived.Gen n
f {₁₊ n} Sym.H-gen = gate₁ (SymDerived.H-gen ₁)
f {₁₊ n} Sym.S-gen = gate₁ (SymDerived.S-gen ₁)
f {₂₊ n} Sym.CZ-gen = gate₂ (SymDerived.CZ-gen ₁)
f {₁₊ n} (x Sym.↥) = (f x) SymDerived.↥

g : SymDerived.Gen n → Word (Sym.Gen n)
g {₁₊ n} (gate₁ (SymDerived.H-gen k)) = Sym.H ^ toℕ k
g {₁₊ n} (gate₁ (SymDerived.S-gen k)) = Sym.S ^ toℕ k
g {₂₊ n} (gate₂ (SymDerived.CZ-gen k)) = Sym.CZ ^ toℕ k
g {₁₊ n} (x SymDerived.↥) = (g x) Sym.↑



-- open PB Sym._===_ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
-- open PB SymDerived._===_ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()

-- open import Presentation.Morphism _===₁_ _===₂_
-- open GroupMorphs grouplike₁ grouplike₂


-- open PP Sym._===_ renaming (by-assoc-and to by-assoc-and₁ ; word-setoid to ws₁)
-- open PP SymDerived._===_ renaming (by-assoc-and to by-assoc-and₂ ; word-setoid to ws₂ ; by-assoc to by-assoc₂) using ()

-- open PB hiding (_===_)
-- open SymDerived hiding (p)

f* : Word (Gen₁ n) → Word (Gen₂ n)
f* {n} = wmap (f {n})

f' : (Gen₁ n) → Word (Gen₂ n)
f' = [_]ʷ ∘ f

f'* : Word (Gen₁ n) → Word (Gen₂ n)
f'* = f' WB.ʷ

-- (([_]ʷ ∘ f) ʷ) fuses with wmap f : f'* agrees with f* = wmap f.
lemma-* : ∀ {X Y : Set} {f : X → Y} (w : Word X) → (([_]ʷ ∘ f) WB.ʷ) w ≡ wmap f w
lemma-* [ x ]ʷ    = Eq.refl
lemma-* ε         = Eq.refl
lemma-* (w • w₁)  = Eq.cong₂ _•_ (lemma-* w) (lemma-* w₁)

open PB

lemma-f'*-^ : ∀ k w v →
  let open PB ((₁₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) in
  f'* w ≈₂ v → f'* (w ^ k) ≈₂ v ^ k
lemma-f'*-^ ₀ w v eq = refl
lemma-f'*-^ ₁ w v eq = eq
lemma-f'*-^ (₂₊ k) w v eq = cong eq (lemma-f'*-^ (₁₊ k) w v eq)

lemma-f'*-^↑ : ∀ k w v →
  let open PB ((₂₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) in
  f'* (w Sym.↑) ≈₂ v ↑ → f'* ((w ^ k) Sym.↑) ≈₂ (v ^ k) ↑
lemma-f'*-^↑ {n} ₀ w v eq = refl
lemma-f'*-^↑ {n} ₁ w v eq = eq
lemma-f'*-^↑ {n} (₂₊ k) w v eq = cong eq (lemma-f'*-^↑ {n} (₁₊ k) w v eq)

lemma-f'*-^↓ : ∀ k w v →
  let open PB ((₂₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) in
  f'* (w Sym.↓) ≈₂ v ↓ → f'* ((w ^ k) Sym.↓) ≈₂ (v ^ k) ↓
lemma-f'*-^↓ {n} ₀ w v eq = refl
lemma-f'*-^↓ {n} ₁ w v eq = eq
lemma-f'*-^↓ {n} (₂₊ k) w v eq = cong eq (lemma-f'*-^↓ {n} (₁₊ k) w v eq)

lemma-f* : ∀ k → let open PB ((₁₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) in f* (Sym.S ^ k) ≈₂ SymDerived.S ^ k
lemma-f* ₀ = refl
lemma-f* ₁ = refl
lemma-f* (₂₊ k) = cong refl (lemma-f* (₁₊ k))

lemma-f*-CZ : ∀ k → let open PB ((₂₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) in f* (Sym.CZ ^ k) ≈₂ SymDerived.CZ ^ k
lemma-f*-CZ ₀ = refl
lemma-f*-CZ ₁ = refl
lemma-f*-CZ (₂₊ k) = cong refl (lemma-f*-CZ (₁₊ k))

lemma-f'*-CZ : ∀ k → let open PB ((₂₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) in f'* (Sym.CZ ^ k) ≈₂ SymDerived.CZ ^ k
lemma-f'*-CZ ₀ = refl
lemma-f'*-CZ ₁ = refl
lemma-f'*-CZ (₂₊ k) = cong refl (lemma-f'*-CZ (₁₊ k))


lemma-f'* : ∀ k → let open PB ((₁₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) in f'* (Sym.S ^ k) ≈₂ SymDerived.S ^ k
lemma-f'* ₀ = refl
lemma-f'* ₁ = refl
lemma-f'* (₂₊ k) = cong refl (lemma-f'* (₁₊ k))


lemma-f'*-H : ∀ k → let open PB ((₁₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) in f'* (Sym.H ^ k) ≈₂ SymDerived.H ^ k
lemma-f'*-H ₀ = refl
lemma-f'*-H ₁ = refl
lemma-f'*-H (₂₊ k) = cong refl (lemma-f'*-H (₁₊ k))


lemma-f'*-M : ∀ x → let open PB ((₁₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) in f'* (Sym.M x) ≈₂ SymDerived.M x
lemma-f'*-M {n} x' = begin
  f'* (Sym.M x') ≈⟨ refl ⟩
  f'* (Sym.S^ x • Sym.H • Sym.S^ x⁻¹ • Sym.H • Sym.S^ x • Sym.H) ≈⟨ refl ⟩
  f'* (Sym.S^ x) • f'* Sym.H • f'* (Sym.S^ x⁻¹) • f'* Sym.H • f'* (Sym.S^ x) • f'* (Sym.H) ≈⟨ cong (lemma-f'* (toℕ x)) (cong refl (cong (lemma-f'* (toℕ x⁻¹)) (cong refl (cong (lemma-f'* (toℕ x)) refl)))) ⟩
  (S ^ toℕ x) • H • (S ^ toℕ x⁻¹) • H • (S ^ toℕ x) • (H) ≈⟨ cong (sym (axiom (srel (derived-S x)))) (cong refl (cong (sym (axiom (srel (derived-S x⁻¹)))) (cong refl (sym (cong (axiom (srel (derived-S x))) refl))))) ⟩
  (S^ x) • H • (S^ x⁻¹) • H • (S^ x) • (H) ≈⟨ refl ⟩
  M x' ∎
  where
  open PB ((₁₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) using ()
  open PP ((₁₊ n) QRel,_===₂_)
  open SR word-setoid
  x = x' .proj₁
  x⁻¹ = ((x' ⁻¹) .proj₁ )

lemma-f'*-↑ : ∀ w → let open PB ((₁₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) in f'* {₁₊ n} (w Sym.↑) ≈₂ f'* w ↑
lemma-f'*-↑ {n} [ x ]ʷ = refl
lemma-f'*-↑ {n} ε = refl
lemma-f'*-↑ {n} (w • w₁) = cong (lemma-f'*-↑ w) (lemma-f'*-↑ w₁)

lemma-f'*-M↑ : ∀ x → let open PB ((₂₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) in f'* {₂₊ n} (Sym.M x Sym.↑) ≈₂ SymDerived.M x ↑
lemma-f'*-M↑ {n} x' = begin
  f'* (Sym.M x' Sym.↑) ≈⟨ lemma-f'*-↑ (Sym.M x') ⟩
  (f'* (Sym.M x')) ↑ ≈⟨ lemma-cong↑ _ _ (lemma-f'*-M x') ⟩
  M x' ↑ ≈⟨ _≈₂_.refl ⟩
  SymDerived.M x' ↑ ∎
  where
  open PB ((₂₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) using ()
  open PP ((₂₊ n) QRel,_===₂_)
  open SR word-setoid
  x = x' .proj₁
  x⁻¹ = ((x' ⁻¹) .proj₁ )

f-well-defined :
  let open PB ((n) QRel,_===₁_) renaming (_===_ to _===₁_) in
  let open PB ((n) QRel,_===₂_) renaming (_≈_ to _≈₂_) in
  ∀ {w v} → w ===₁ v → f'* w ≈₂ f'* v
f-well-defined {₁₊ n} (Sym.srel Sym.Base.order-S) = begin
  f'* (Sym.S • Sym.S ^ ₁₊ p-2) ≡⟨ lemma-* ([ Sym.S-gen ]ʷ • Sym.S ^ ₁₊ p-2) ⟩
  (wmap f) (Sym.S • Sym.S ^ ₁₊ p-2) ≈⟨ lemma-f* (₂₊ p-2) ⟩
  SymDerived.S ^ p ≈⟨ axiom (srel order-S) ⟩
  f'* ε ∎
  where
  open PB ((₁₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) using ()
  open PP ((₁₊ n) QRel,_===₂_)
  open SR word-setoid

f-well-defined {n} (Sym.srel Sym.Base.order-H) = axiom (srel order-H)
f-well-defined {n} (Sym.srel Sym.Base.order-SH) = axiom (srel order-SH)
f-well-defined {n} (Sym.srel Sym.Base.comm-HHS) = axiom (srel comm-HHS)
f-well-defined {₁₊ n} (Sym.srel (Sym.Base.M-mul x y)) = begin
  f'* (Sym.M x • Sym.M y) ≈⟨ refl ⟩
  f'* (Sym.M x) • f'* (Sym.M y) ≈⟨ cong (lemma-f'*-M x) (lemma-f'*-M y) ⟩
  (SymDerived.M x) • (SymDerived.M y) ≈⟨ axiom (srel (M-mul x y)) ⟩
  (SymDerived.M (x *' y)) ≈⟨ sym (lemma-f'*-M (x *' y)) ⟩
  f'* (Sym.M (x *' y)) ∎
  where
  open PB ((₁₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) using ()
  open PP ((₁₊ n) QRel,_===₂_)
  open SR word-setoid
f-well-defined {₁₊ n} (Sym.srel (Sym.Base.semi-MS (x , nz))) = begin
  f'* (Sym.M (x , nz) • Sym.S) ≈⟨ cong (lemma-f'*-M (x , nz)) (lemma-f'* ₁) ⟩
  (M (x , nz) • S) ≈⟨ axiom (srel (semi-MS (x , nz))) ⟩
  (S^ (x * x) • M (x , nz)) ≈⟨ cong (axiom (srel (derived-S (x * x)))) refl ⟩
  (S ^ toℕ (x * x) • M (x , nz)) ≈⟨ cong (sym (lemma-f'* (toℕ (x * x)))) (sym (lemma-f'*-M (x , nz))) ⟩
  f'* (Sym.S^ (x * x) • Sym.M (x , nz)) ∎
  where
  open PB ((₁₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) using ()
  open PP ((₁₊ n) QRel,_===₂_)
  open SR word-setoid

f-well-defined {₂₊ n} (Sym.srel (Sym.Base.semi-M↑CZ x)) = begin
  f'* ((Sym.M x Sym.↑) • Sym.CZ) ≡⟨ Eq.cong₂ _•_ Eq.refl (lemma-* {f = f} Sym.CZ) ⟩
  f'* ((Sym.M x Sym.↑)) • (wmap f Sym.CZ) ≈⟨ cong (lemma-f'*-M↑  x) (lemma-f*-CZ ₁) ⟩
  (SymDerived.M x SymDerived.↑) • (SymDerived.CZ) ≈⟨ _≈₂_.axiom (srel (semi-M↑CZ x)) ⟩
  (SymDerived.CZ^ (x SymDerived.^1)) • (SymDerived.M x SymDerived.↑) ≈⟨ sym (cong (_≈₂_.trans (lemma-f*-CZ (toℕ (x .proj₁)))
                                                                                    (_≈₂_.sym
                                                                                     (_≈₂_.axiom (srel (derived-CZ (x SymDerived.^1)))))) (lemma-f'*-M↑ x)) ⟩
  (wmap f) (Sym.CZ^ (x Sym.^1)) • f'* ((Sym.M x Sym.↑)) ≡⟨ Eq.sym (Eq.cong₂ _•_  (lemma-* {f = f} (Sym.CZ^ (x Sym.^1))) auto) ⟩
  f'* (Sym.CZ^ (x Sym.^1) • Sym.M x Sym.↑) ≈⟨ _≈₂_.refl ⟩
  (f'* (Sym.CZ^ (x Sym.^1) • (Sym.M x Sym.↑))) ∎
  where
  open PB ((₂₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) using ()
  open PP ((₂₊ n) QRel,_===₂_)
  open SR word-setoid
  
f-well-defined {₂₊ n} (Sym.srel (Sym.Base.semi-M↓CZ x)) = begin
  f'* ((Sym.M x Sym.↓) • Sym.CZ) ≡⟨ Eq.cong₂ _•_ Eq.refl (lemma-* {f = f} Sym.CZ) ⟩
  f'* ((Sym.M x Sym.↓)) • (wmap f Sym.CZ) ≈⟨ cong (lemma-f'*-M x) (lemma-f*-CZ ₁) ⟩
  (SymDerived.M x SymDerived.↓) • (SymDerived.CZ) ≈⟨ _≈₂_.axiom (srel (semi-M↓CZ x)) ⟩
  (SymDerived.CZ^ (x SymDerived.^1)) • (SymDerived.M x SymDerived.↓) ≈⟨ sym (cong (_≈₂_.trans (lemma-f*-CZ (toℕ (x .proj₁)))
                                                                                    (_≈₂_.sym
                                                                                     (_≈₂_.axiom (srel (derived-CZ (x SymDerived.^1)))))) (lemma-f'*-M x)) ⟩
  (wmap f) (Sym.CZ^ (x Sym.^1)) • f'* ((Sym.M x Sym.↓)) ≡⟨ Eq.sym (Eq.cong₂ _•_  (lemma-* {f = f} (Sym.CZ^ (x Sym.^1))) auto) ⟩
  f'* (Sym.CZ^ (x Sym.^1) • Sym.M x Sym.↓) ≈⟨ _≈₂_.refl ⟩
  (f'* (Sym.CZ^ (x Sym.^1) • (Sym.M x Sym.↓))) ∎
  where
  open PB ((₂₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) using ()
  open PP ((₂₊ n) QRel,_===₂_)
  open SR word-setoid

f-well-defined {₂₊ n} (Sym.srel Sym.Base.order-CZ) = begin
  f'* (Sym.CZ • Sym.CZ ^ ₁₊ p-2) ≡⟨ lemma-* ([ Sym.CZ-gen ]ʷ • Sym.CZ ^ ₁₊ p-2) ⟩
  (wmap f) (Sym.CZ • Sym.CZ ^ ₁₊ p-2) ≈⟨ lemma-f*-CZ (₂₊ p-2) ⟩
  SymDerived.CZ ^ p ≈⟨ axiom (srel order-CZ) ⟩
  f'* ε ∎
  where
  open PB ((₂₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) using ()
  open PP ((₂₊ n) QRel,_===₂_)
  open SR word-setoid
  
f-well-defined (Sym.srel Sym.Base.comm-CZ-S↓) = axiom (srel comm-CZ-S↓)
f-well-defined (Sym.srel Sym.Base.comm-CZ-S↑) = axiom (srel comm-CZ-S↑)
f-well-defined {₂₊ n} (Sym.srel Sym.Base.selinger-c10) = begin
  f'* (Sym.CZ • (Sym.H Sym.↑) • Sym.CZ) ≈⟨ _≈₂_.refl ⟩
  (CZ • (H ↑) • CZ) ≈⟨ _≈₂_.axiom (srel selinger-c10) ⟩
  (((S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑) •  CZ • (H ↑) • (S⁻¹ ↑) • (S⁻¹ ↓))) ≈⟨ sym (cong (lemma-f'*-^↑ p-1 Sym.S SymDerived.S _≈₂_.refl) (cong _≈₂_.refl (cong (lemma-f'*-^↑ p-1 Sym.S SymDerived.S _≈₂_.refl) (cong _≈₂_.refl (cong _≈₂_.refl (cong (lemma-f'*-^↑ p-1 Sym.S SymDerived.S _≈₂_.refl) (lemma-f'*-^↓ p-1 Sym.S SymDerived.S _≈₂_.refl))))))) ⟩
  (f'* ((Sym.S⁻¹ Sym.↑) • (Sym.H Sym.↑) • (Sym.S⁻¹ Sym.↑) •  Sym.CZ • (Sym.H Sym.↑) • (Sym.S⁻¹ Sym.↑) • (Sym.S⁻¹ Sym.↓))) ∎
  where
  open PB ((₂₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) using ()
  open PP ((₂₊ n) QRel,_===₂_)
  open SR word-setoid
f-well-defined {₂₊ n} (Sym.srel Sym.Base.selinger-c11) = begin
  f'* (Sym.CZ • (Sym.H Sym.↓) • Sym.CZ) ≈⟨ _≈₂_.refl ⟩
  (CZ • (H ↓) • CZ) ≈⟨ _≈₂_.axiom (srel selinger-c11) ⟩
  (((S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓) •  CZ • (H ↓) • (S⁻¹ ↓) • (S⁻¹ ↑))) ≈⟨ sym (cong (lemma-f'*-^↓ p-1 Sym.S SymDerived.S _≈₂_.refl) (cong _≈₂_.refl (cong (lemma-f'*-^↓ p-1 Sym.S SymDerived.S _≈₂_.refl) (cong _≈₂_.refl (cong _≈₂_.refl (cong (lemma-f'*-^↓ p-1 Sym.S SymDerived.S _≈₂_.refl) (lemma-f'*-^↑ p-1 Sym.S SymDerived.S _≈₂_.refl))))))) ⟩
  (f'* ((Sym.S⁻¹ Sym.↓) • (Sym.H Sym.↓) • (Sym.S⁻¹ Sym.↓) •  Sym.CZ • (Sym.H Sym.↓) • (Sym.S⁻¹ Sym.↓) • (Sym.S⁻¹ Sym.↑))) ∎
  where
  open PB ((₂₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) using ()
  open PP ((₂₊ n) QRel,_===₂_)
  open SR word-setoid
f-well-defined (Sym.srel Sym.Base.selinger-c12) = axiom (srel selinger-c12)
f-well-defined (Sym.srel Sym.Base.selinger-c13) = axiom (srel selinger-c13)
f-well-defined (Sym.srel Sym.Base.selinger-c14) = axiom (srel selinger-c14)
f-well-defined (Sym.srel Sym.Base.selinger-c15) = axiom (srel selinger-c15)
f-well-defined {(₂₊ n)} (Sym.comm₁ Sym.H-gate g) = begin
  f'* ([ g Sym.↥ ]ʷ • Sym.H) ≈⟨ refl₂ ⟩
  f'* ([ g ]ʷ) SymDerived.↑ • SymDerived.H ≈⟨ sym₂ (lemma-comm-H-w↑ (f'* ([ g ]ʷ))) ⟩
  SymDerived.H • f'* ([ g ]ʷ) SymDerived.↑ ≈⟨ refl₂ ⟩
  f'* (Sym.H • [ g Sym.↥ ]ʷ) ∎
  where
  open PB ((₂₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_ ; refl to refl₂ ; cong to cong₂ ; sym to sym₂ ; axiom to axiom₂)
  open PP ((₂₊ n) QRel,_===₂_)
  open SR word-setoid
f-well-defined {(₂₊ n)} (Sym.comm₁ Sym.S-gate g) = begin
  f'* ([ g Sym.↥ ]ʷ • Sym.S) ≈⟨ refl₂ ⟩
  f'* ([ g ]ʷ) SymDerived.↑ • SymDerived.S ≈⟨ sym₂ (lemma-comm-S-w↑ (f'* ([ g ]ʷ))) ⟩
  SymDerived.S • f'* ([ g ]ʷ) SymDerived.↑ ≈⟨ refl₂ ⟩
  f'* (Sym.S • [ g Sym.↥ ]ʷ) ∎
  where
  open PB ((₂₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_ ; refl to refl₂ ; cong to cong₂ ; sym to sym₂ ; axiom to axiom₂)
  open PP ((₂₊ n) QRel,_===₂_)
  open SR word-setoid
f-well-defined {(₃₊ n)} (Sym.comm₂ Sym.CZ-gate g) = begin
  f'* ([ g Sym.↥ Sym.↥ ]ʷ • Sym.CZ) ≈⟨ refl₂ ⟩
  f'* ([ g ]ʷ) SymDerived.↑ SymDerived.↑ • SymDerived.CZ ≈⟨ sym₂ (lemma-comm-CZ-w↑ (f'* ([ g ]ʷ))) ⟩
  SymDerived.CZ • f'* ([ g ]ʷ) SymDerived.↑ SymDerived.↑ ≈⟨ refl₂ ⟩
  f'* (Sym.CZ • [ g Sym.↥ Sym.↥ ]ʷ) ∎
  where
  open PB ((₃₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_ ; refl to refl₂ ; cong to cong₂ ; sym to sym₂ ; axiom to axiom₂)
  open PP ((₃₊ n) QRel,_===₂_)
  open SR word-setoid
f-well-defined {₁₊ n} (Sym.cong↑ {w = w} {v = v} x) = begin
  f'* (w Sym.↑) ≈⟨ lemma-f'*-↑ w ⟩
  f'* w ↑ ≈⟨ lemma-cong↑ _ _ (f-well-defined x) ⟩
  f'* v ↑ ≈⟨ sym (lemma-f'*-↑ v) ⟩
  (f'* (v Sym.↑)) ∎
  where
  open PB ((₁₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) using ()
  open PP ((₁₊ n) QRel,_===₂_)
  open SR word-setoid


g* : Word (Gen₂ n) → Word (Gen₁ n)
g* {n} = g WB.ʷ

lemma-g* : let open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_) in
  ∀ k → g* (S ^ k) ≈₁ Sym.S ^ k
lemma-g* ₀ = refl
lemma-g* ₁ = refl
lemma-g* (₂₊ k) = cong refl (lemma-g* (₁₊ k))

lemma-g*-CZ : let open PB ((₂₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_) in
  ∀ k → g* (CZ ^ k) ≈₁ Sym.CZ ^ k
lemma-g*-CZ ₀ = refl
lemma-g*-CZ ₁ = refl
lemma-g*-CZ (₂₊ k) = cong refl (lemma-g*-CZ (₁₊ k))


lemma-g*-H : let open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_) in ∀ k → g* (H ^ k) ≈₁ Sym.H ^ k
lemma-g*-H ₀ = refl
lemma-g*-H ₁ = refl
lemma-g*-H (₂₊ k) = cong refl (lemma-g*-H (₁₊ k))

lemma-g*'-H : let open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_) in ∀ k → g* (H^ k) ≈₁ Sym.H ^ toℕ k
lemma-g*'-H ₀ = refl
lemma-g*'-H ₁ = refl
lemma-g*'-H ₂ = refl
lemma-g*'-H ₃ = refl

lemma-g*-↑ : ∀ w → let open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_) in g* {₁₊ n} (w SymDerived.↑) ≈₁ g* w Sym.↑
lemma-g*-↑ {n} [ x ]ʷ = refl
lemma-g*-↑ {n} ε = refl
lemma-g*-↑ {n} (w • w₁) = cong (lemma-g*-↑ w) (lemma-g*-↑ w₁)


-- CZ ^ k commutes with a doubly-shifted word (power version of Sym'.lemma-comm-CZ-w↑).
lemma-comm-CZᵏ-w↑↑ : ∀ {m} k (w : Word (Sym.Gen (₁₊ m))) →
  let open PB ((₃₊ m) QRel,_===₁_) renaming (_≈_ to _≈₁_) in
  Sym.CZ ^ k • w Sym.↑ Sym.↑ ≈₁ w Sym.↑ Sym.↑ • Sym.CZ ^ k
lemma-comm-CZᵏ-w↑↑ {m} ₀ w = trans left-unit (sym right-unit)
lemma-comm-CZᵏ-w↑↑ {m} ₁ w = Sym'.lemma-comm-CZ-w↑ w
lemma-comm-CZᵏ-w↑↑ {m} (₂₊ k) w = begin
  (Sym.CZ • Sym.CZ ^ ₁₊ k) • (w Sym.↑ Sym.↑) ≈⟨ assoc ⟩
  Sym.CZ • Sym.CZ ^ ₁₊ k • (w Sym.↑ Sym.↑) ≈⟨ cong refl (lemma-comm-CZᵏ-w↑↑ (₁₊ k) w) ⟩
  Sym.CZ • (w Sym.↑ Sym.↑) • Sym.CZ ^ ₁₊ k ≈⟨ sym assoc ⟩
  (Sym.CZ • w Sym.↑ Sym.↑) • Sym.CZ ^ ₁₊ k ≈⟨ cong (Sym'.lemma-comm-CZ-w↑ w) refl ⟩
  (w Sym.↑ Sym.↑ • Sym.CZ) • Sym.CZ ^ ₁₊ k ≈⟨ assoc ⟩
  (w Sym.↑ Sym.↑) • Sym.CZ • Sym.CZ ^ ₁₊ k ∎
  where
  open PP ((₃₊ m) QRel,_===₁_)
  open SR word-setoid


lemma-g*-M : let open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_) in ∀ x → g* (M x) ≈₁ Sym.M x
lemma-g*-M {n} x' = begin
  g* (M x') ≈⟨ refl₁ ⟩
  g* (S^ x • H • S^ x⁻¹ • H • S^ x • H) ≈⟨ refl₁ ⟩
  g* (S^ x) • g* H • g* (S^ x⁻¹) • g* H • g* (S^ x) • g* (H) ≈⟨ cong₁ (sym₁ ( lemma-g* (toℕ x))) (cong₁ refl₁ (cong₁ (sym₁ ( lemma-g* (toℕ x⁻¹))) (cong₁ refl₁ (sym₁ (cong₁ ( lemma-g* (toℕ x)) refl₁))))) ⟩
  g* (S ^ toℕ x) • g* H • g* (S ^ toℕ x⁻¹) • g* H • g* (S ^ toℕ x) • g* (H) ≈⟨ cong₁ (lemma-g* (toℕ x)) (cong₁ refl₁ (cong₁ (lemma-g* (toℕ x⁻¹)) (cong₁ refl₁ (cong₁ (lemma-g* (toℕ x)) refl₁)))) ⟩
  (Sym.S ^ toℕ x) • Sym.H • (Sym.S ^ toℕ x⁻¹) • Sym.H • (Sym.S ^ toℕ x) • (Sym.H) ≈⟨ refl₁ ⟩
  (Sym.S^ x) • Sym.H • (Sym.S^ x⁻¹) • Sym.H • (Sym.S^ x) • (Sym.H) ≈⟨ refl₁ ⟩
  Sym.M x' ∎
  where
  open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁)
  open PP ((₁₊ n) QRel,_===₁_)
  open SR word-setoid
  x = x' .proj₁
  x⁻¹ = ((x' ⁻¹) .proj₁ )


g-well-defined :
  let open PB (( n) QRel,_===₁_) renaming (_≈_ to _≈₁_) in
  let open PB ((n) QRel,_===₂_) renaming (_≈_ to _≈₂_ ; _===_ to _===₂_) in
  ∀ {w v} → w ===₂ v → g* w ≈₁ g* v
g-well-defined {₁₊ n} (srel order-S) = begin
  g* (S • S ^ ₁₊ p-2) ≈⟨ lemma-g* p ⟩
  (Sym.S ^ p) ≈⟨ axiom₁ (Sym.srel Sym.Base.order-S) ⟩
  g* ε ∎
  where
  open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; axiom to axiom₁)
  open PP ((₁₊ n) QRel,_===₁_)
  open SR word-setoid

g-well-defined (srel order-H) = axiom (Sym.srel Sym.Base.order-H)
g-well-defined (srel order-SH) = axiom (Sym.srel Sym.Base.order-SH)
g-well-defined (srel comm-HHS) = axiom (Sym.srel Sym.Base.comm-HHS)

g-well-defined {₁₊ n} (srel (M-mul x y)) = begin
  g* (M x • M y) ≈⟨ refl ⟩
  g* (M x) • g* (M y) ≈⟨ cong (lemma-g*-M x) (lemma-g*-M y) ⟩
  (Sym.M x) • (Sym.M y) ≈⟨ axiom (Sym.M-mul x y) ⟩
  (Sym.M (x *' y)) ≈⟨ sym (lemma-g*-M (x *' y)) ⟩
  g* (M (x *' y)) ∎
  where
  open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; axiom to axiom₁)
  open PP ((₁₊ n) QRel,_===₁_)
  open SR word-setoid


g-well-defined {₁₊ n} (srel (semi-MS (x , nz))) = begin
  g* (M (x , nz) • S) ≈⟨ cong (lemma-g*-M (x , nz)) (lemma-g* ₁) ⟩
  (Sym.M (x , nz) • Sym.S) ≈⟨ axiom (Sym.srel (Sym.Base.semi-MS (x , nz))) ⟩
  (Sym.S^ (x * x) • Sym.M (x , nz)) ≈⟨ cong (refl) refl ⟩
  (Sym.S ^ toℕ (x * x) • Sym.M (x , nz)) ≈⟨ cong (sym (lemma-g* (toℕ (x * x)))) (sym (lemma-g*-M (x , nz))) ⟩
  g* (S ^ toℕ (x * x) • M (x , nz)) ≈⟨ cong (sym (g-well-defined (srel (derived-S (fromℕ< _))))) refl ⟩
  g* (S^ (x * x) • M (x , nz)) ∎
  where
  open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; axiom to axiom₁)
  open PP ((₁₊ n) QRel,_===₁_)
  open SR word-setoid

g-well-defined {₁₊ n} (srel (derived-S k)) = begin
  g* [ gate₁ (S-gen k) ]ʷ ≈⟨ refl ⟩
  Sym.S ^ toℕ k ≈⟨ sym (lemma-g* (toℕ k)) ⟩
  g* (S ^ toℕ k) ∎
  where
  open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; axiom to axiom₁)
  open PP ((₁₊ n) QRel,_===₁_)
  open SR word-setoid


g-well-defined {₁₊ n} (srel (derived-H k)) = begin
  g* [ gate₁ (H-gen k) ]ʷ ≈⟨ lemma-g*'-H k ⟩
  Sym.H ^ toℕ k ≈⟨ sym (lemma-g*-H (toℕ k)) ⟩
  g* (H ^ toℕ k) ∎
  where
  open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; axiom to axiom₁)
  open PP ((₁₊ n) QRel,_===₁_)
  open SR word-setoid



g-well-defined {₁₊ n} (srel (semi-M↑CZ x)) = begin
  g* ((SymDerived.M x SymDerived.↑) • SymDerived.CZ) ≈⟨ cong refl₁ refl₁ ⟩
  ((Sym.M x Sym.↑) • Sym.CZ) ≈⟨ axiom₁ (Sym.semi-M↑CZ x) ⟩
  Sym.CZ^ (x Sym.^1) • (Sym.M x Sym.↑)  ≈⟨ refl₁ ⟩
  g* (SymDerived.CZ^ (x SymDerived.^1) • (SymDerived.M x SymDerived.↑)) ∎
  where
  open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; axiom to axiom₁)
  open PP ((₁₊ n) QRel,_===₁_)
  open SR word-setoid
g-well-defined {₁₊ n} (srel (semi-M↓CZ x)) = begin
  g* ((SymDerived.M x SymDerived.↓) • SymDerived.CZ) ≈⟨ cong (refl) refl₁ ⟩
  ((Sym.M x Sym.↓) • Sym.CZ) ≈⟨ axiom₁ (Sym.semi-M↓CZ x) ⟩
  Sym.CZ^ (x Sym.^1) • (Sym.M x Sym.↓)  ≈⟨ cong refl₁ (sym (refl)) ⟩
  g* (SymDerived.CZ^ (x SymDerived.^1) • (SymDerived.M x SymDerived.↓)) ∎
  where
  open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; axiom to axiom₁)
  open PP ((₁₊ n) QRel,_===₁_)
  open SR word-setoid
g-well-defined {₁₊ n} (srel order-CZ) = begin
  g* (CZ • CZ ^ ₁₊ p-2) ≈⟨ lemma-g*-CZ p ⟩
  (Sym.CZ ^ p) ≈⟨ axiom₁ (Sym.srel Sym.Base.order-CZ) ⟩
  g* ε ∎
  where
  open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; axiom to axiom₁)
  open PP ((₁₊ n) QRel,_===₁_)
  open SR word-setoid
g-well-defined {n} (srel comm-CZ-S↓) = axiom Sym.comm-CZ-S↓
g-well-defined {n} (srel comm-CZ-S↑) = axiom Sym.comm-CZ-S↑
g-well-defined {₁₊ n} (srel selinger-c10) = begin
  g* (CZ • H ↑ • CZ) ≈⟨ refl₁ ⟩
  (Sym.CZ • Sym.H Sym.↑ • Sym.CZ) ≈⟨ axiom₁ Sym.selinger-c10 ⟩
  (Sym.S⁻¹ Sym.↑) • (Sym.H Sym.↑) • (Sym.S⁻¹ Sym.↑) • Sym.CZ • (Sym.H Sym.↑) • (Sym.S⁻¹ Sym.↑) • (Sym.S⁻¹ Sym.↓) ≈⟨ sym (cong ( Sym.lemma-cong↑ _ _ (lemma-g* p-1)) (cong refl₁ (cong (Sym.lemma-cong↑ _ _ (lemma-g* p-1)) (cong refl₁ (cong refl₁ (cong (Sym.lemma-cong↑ _ _ (lemma-g* p-1)) ((lemma-g* p-1)))))))) ⟩
  (g* S⁻¹ Sym.↑) • (Sym.H Sym.↑) • (g* S⁻¹ Sym.↑) • Sym.CZ • (Sym.H Sym.↑) • (g* S⁻¹ Sym.↑) • (g* S⁻¹ Sym.↓) ≈⟨ sym (cong (lemma-g*-↑ S⁻¹) (cong refl₁ (cong (lemma-g*-↑ S⁻¹) (cong refl₁ (cong refl₁ (cong (lemma-g*-↑ S⁻¹) (refl))))))) ⟩
  g* ((S⁻¹ ↑) • (H ↑) • (S⁻¹ ↑) • CZ • (H ↑) • (S⁻¹ ↑) • (S⁻¹ ↓)) ∎
  where
  open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; axiom to axiom₁) using ()
  open PP ((₁₊ n) QRel,_===₁_)
  open SR word-setoid
g-well-defined {₁₊ n} (srel selinger-c11) = begin
  g* (CZ • H ↓ • CZ) ≈⟨ refl₁ ⟩
  (Sym.CZ • Sym.H Sym.↓ • Sym.CZ) ≈⟨ axiom₁ Sym.selinger-c11 ⟩
  (Sym.S⁻¹ Sym.↓) • (Sym.H Sym.↓) • (Sym.S⁻¹ Sym.↓) • Sym.CZ • (Sym.H Sym.↓) • (Sym.S⁻¹ Sym.↓) • (Sym.S⁻¹ Sym.↑) ≈⟨ sym (cong ( (lemma-g* p-1)) (cong refl₁ (cong ((lemma-g* p-1)) (cong refl₁ (cong refl₁ (cong ((lemma-g* p-1)) (Sym.lemma-cong↑ _ _ (lemma-g* p-1)))))))) ⟩
  (g* S⁻¹ Sym.↓) • (Sym.H Sym.↓) • (g* S⁻¹ Sym.↓) • Sym.CZ • (Sym.H Sym.↓) • (g* S⁻¹ Sym.↓) • (g* S⁻¹ Sym.↑) ≈⟨ cong refl₁ (cong refl₁ (cong refl₁ (cong refl₁ (cong refl₁ (cong refl₁ (sym (lemma-g*-↑ S⁻¹))))))) ⟩
  g* ((S⁻¹ ↓) • (H ↓) • (S⁻¹ ↓) • CZ • (H ↓) • (S⁻¹ ↓) • (S⁻¹ ↑)) ∎
  where
  open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; axiom to axiom₁) using ()
  open PP ((₁₊ n) QRel,_===₁_)
  open SR word-setoid
g-well-defined {n} (srel selinger-c12) = axiom Sym.selinger-c12
g-well-defined {n} (srel selinger-c13) = axiom Sym.selinger-c13
g-well-defined {n} (srel selinger-c14) = axiom Sym.selinger-c14
g-well-defined {n} (srel selinger-c15) = axiom Sym.selinger-c15
g-well-defined {(₂₊ n)} (comm₁ (H-gen k) g₁) = begin
  g* ([ g₁ Gen₂.↥ ]ʷ • [ gate₁ (H-gen k) ]ʷ) ≈⟨ refl₁ ⟩
  g* ([ g₁ ]ʷ) Sym.↑ • Sym.H ^ toℕ k ≈⟨ sym₁ (Sym'.lemma-comm-Hᵏ-w↑ (toℕ k) (g g₁)) ⟩
  Sym.H ^ toℕ k • g* ([ g₁ ]ʷ) Sym.↑ ≈⟨ refl₁ ⟩
  g* ([ gate₁ (H-gen k) ]ʷ • [ g₁ Gen₂.↥ ]ʷ) ∎
  where
  open PB ((₂₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; axiom to axiom₁)
  open PP ((₂₊ n) QRel,_===₁_)
  open SR word-setoid
g-well-defined {(₂₊ n)} (comm₁ (S-gen k) g₁) = begin
  g* ([ g₁ Gen₂.↥ ]ʷ • [ gate₁ (S-gen k) ]ʷ) ≈⟨ refl₁ ⟩
  g* ([ g₁ ]ʷ) Sym.↑ • Sym.S ^ toℕ k ≈⟨ sym₁ (Sym'.lemma-comm-Sᵏ-w↑ (toℕ k) (g g₁)) ⟩
  Sym.S ^ toℕ k • g* ([ g₁ ]ʷ) Sym.↑ ≈⟨ refl₁ ⟩
  g* ([ gate₁ (S-gen k) ]ʷ • [ g₁ Gen₂.↥ ]ʷ) ∎
  where
  open PB ((₂₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; axiom to axiom₁)
  open PP ((₂₊ n) QRel,_===₁_)
  open SR word-setoid
g-well-defined {(₃₊ n)} (comm₂ (CZ-gen k) g₁) = begin
  g* ([ g₁ Gen₂.↥ Gen₂.↥ ]ʷ • [ gate₂ (CZ-gen k) ]ʷ) ≈⟨ refl₁ ⟩
  g* ([ g₁ ]ʷ) Sym.↑ Sym.↑ • Sym.CZ ^ toℕ k ≈⟨ sym₁ (lemma-comm-CZᵏ-w↑↑ (toℕ k) (g g₁)) ⟩
  Sym.CZ ^ toℕ k • g* ([ g₁ ]ʷ) Sym.↑ Sym.↑ ≈⟨ refl₁ ⟩
  g* ([ gate₂ (CZ-gen k) ]ʷ • [ g₁ Gen₂.↥ Gen₂.↥ ]ʷ) ∎
  where
  open PB ((₃₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; axiom to axiom₁)
  open PP ((₃₊ n) QRel,_===₁_)
  open SR word-setoid
g-well-defined {₁₊ n} (srel (derived-CZ k)) = begin
  g* [ gate₂ (CZ-gen k) ]ʷ ≈⟨ refl₁ ⟩
  Sym.CZ ^ toℕ k ≈⟨ sym (lemma-g*-CZ (toℕ k) ) ⟩
  g* (CZ ^ toℕ k) ∎
  where
  open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; axiom to axiom₁)
  open PP ((₁₊ n) QRel,_===₁_)
  open SR word-setoid

g-well-defined {(₁₊ n)} (cong↑ {w = w} {v = v} x) = begin
  g* (w SymDerived.↑) ≈⟨ lemma-g*-↑ w ⟩
  g* w Sym.↑ ≈⟨ Sym.lemma-cong↑ _ _ (g-well-defined x) ⟩
  g* v Sym.↑ ≈⟨ sym (lemma-g*-↑ v) ⟩
  g* (v SymDerived.↑) ∎
  where
  open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_ ; refl to refl₁ ; cong to cong₁ ; sym to sym₁ ; axiom to axiom₁)
  open PP ((₁₊ n) QRel,_===₁_)
  open SR word-setoid


f-left-inv-gen : let open PB ((n) QRel,_===₂_) renaming (_≈_ to _≈₂_) in
  ∀ x → [ x ]ʷ ≈₂ (f'*) (g x)
f-left-inv-gen {₁₊ n} (gate₁ (SymDerived.H-gen k)) = begin
  [ gate₁ (H-gen k) ]ʷ ≈⟨ axiom (srel (derived-H k)) ⟩
  H ^ toℕ k ≈⟨ sym (lemma-f'*-H (toℕ k)) ⟩
  f'* (Sym.H ^ toℕ k) ∎
  where
  open PB ((₁₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) using ()
  open PP ((₁₊ n) QRel,_===₂_)
  open SR word-setoid
f-left-inv-gen {₁₊ n} (gate₁ (SymDerived.S-gen k)) = begin
  [ gate₁ (S-gen k) ]ʷ ≈⟨ axiom (srel (derived-S k)) ⟩
  S ^ toℕ k ≈⟨ sym (lemma-f'* (toℕ k)) ⟩
  f'* (Sym.S ^ toℕ k) ∎
  where
  open PB ((₁₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) using ()
  open PP ((₁₊ n) QRel,_===₂_)
  open SR word-setoid

f-left-inv-gen {₁₊ n} (gate₂ (SymDerived.CZ-gen k)) = begin
  [ gate₂ (CZ-gen k) ]ʷ ≈⟨ axiom (srel (derived-CZ k)) ⟩
  CZ ^ toℕ k ≈⟨ sym (lemma-f'*-CZ (toℕ k)) ⟩
  f'* (Sym.CZ ^ toℕ k) ∎
  where
  open PB ((₁₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) using ()
  open PP ((₁₊ n) QRel,_===₂_)
  open SR word-setoid
f-left-inv-gen {(₁₊ n)} (x SymDerived.↥) = begin
  [ x Gen₂.↥ ]ʷ ≈⟨ lemma-cong↑ _ _ (f-left-inv-gen x) ⟩
  f'* (g x) ↑ ≈⟨ sym (lemma-f'*-↑ (g x)) ⟩
  f'* ((g x) Sym.↑) ∎
  where
  open PB ((₁₊ n) QRel,_===₂_) renaming (_≈_ to _≈₂_) using ()
  open PP ((₁₊ n) QRel,_===₂_)
  open SR word-setoid


g-left-inv-gen : let open PB ((n) QRel,_===₁_) renaming (_≈_ to _≈₁_) in
  ∀ x → [ x ]ʷ ≈₁ (g*) (f' x)
g-left-inv-gen Sym.S-gen = refl
g-left-inv-gen Sym.H-gen = refl
g-left-inv-gen Sym.CZ-gen = refl
g-left-inv-gen {(₁₊ n)} (x Sym.↥) = begin
  [ x Gen₁.↥ ]ʷ ≈⟨ Sym.lemma-cong↑ _ _ (g-left-inv-gen x) ⟩
  g* (f'* [ x ]ʷ) Sym.↑ ≈⟨ _≈₁_.refl ⟩
  g* (f'* [ x ]ʷ ↑) ≈⟨ _≈₁_.refl ⟩
  g* (f' (x Gen₁.↥)) ∎
  where
  open PB ((₁₊ n) QRel,_===₁_) renaming (_≈_ to _≈₁_) using ()
  open PP ((₁₊ n) QRel,_===₁_)
  open SR word-setoid


open import Algebra.Morphism.Structures using (module GroupMorphisms)

open GroupMorphisms

module G1 {n} = Group-Lemmas ((n) QRel,_===₁_) (grouplike₁ {n})
module G2 {n} = Group-Lemmas ((n) QRel,_===₂_) (grouplike₂ {n})

-- The Sym ≅ SymDerived group isomorphism (formerly Theorem-Sym-iso-SymDerived)
-- now lives in Examples.Groups.Symplectic.Sim-Ext-Sym as Theorem-Sym-iso-Ext.

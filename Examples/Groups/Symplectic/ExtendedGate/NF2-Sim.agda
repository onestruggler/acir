{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --termination-depth=2 #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; module ≡-Reasoning)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR


open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
import Data.Nat as Nat
open import Data.Nat.DivMod using (m%n<n ; m<n⇒m%n≡m)
open import Data.Vec hiding ([_])
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Fin.Properties using (fromℕ<-cong ; fromℕ<-toℕ ; toℕ-fromℕ< ; toℕ<n)

open import Word.Base as WB hiding (wfoldl)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Notations


open import Data.Fin using (toℕ)
open import Data.Nat.Primality
open import Zp.Fermats-little-theorem
open import Zp.ModularArithmetic

module Examples.Groups.Symplectic.ExtendedGate.NF2-Sim
  (p-2 : ℕ)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime hiding (act))
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where
open Primitive-Root-Modp' g* g-gen






open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime as ND
open import Examples.Groups.Symplectic.ExtendedGate.Lemmas-2Qupit p-2 p-prime
open import Examples.Groups.Symplectic.Cosets p-2 p-prime
open Lemmas-2Q 2 hiding (lemma-CZ^k-%)
open Symplectic
open import Examples.Groups.Symplectic.ExtendedGate.NF1 p-2 p-prime
open Normal-Form1 renaming (⟦_⟧₁ to ⟦_⟧₁' ; ⟦_⟧ₘ₊ to ⟦_⟧ₘ₊') using ()
open import Examples.Groups.Symplectic.ExtendedGate.NF1-Sim p-2 p-prime g* g-gen
open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Properties p-2 p-prime renaming (act to dact)

------------------------------------------------------------------------
-- The action on Simplified circuits, via the Sim ≅ Derived isomorphism
--
-- (formerly Examples.Groups.Symplectic.ExtendedGate.Semantics.Action.Action-Sym)
------------------------------------------------------------------------

open import Examples.Groups.Symplectic.ExtendedGate.Iso-Sym-Derived p-2 p-prime using (f'*)

private
  variable
    n : ℕ

open ND.Symplectic-Derived-Gen renaming (Gen to Gen₃ ; _QRel,_===_ to _QRel,_===₃_) using ()

module D = ND.Symplectic-Derived-Gen

der : Word (Gen n) -> Word (Gen₃ n)
der {n} = f'* {n}

act : ∀ {n} → Word (Gen n) → Pauli n → Pauli n
act {n} w ps = dact (der w) ps


lemma-der' : let open PB ((₁₊ n) QRel,_===₃_) in
  ∀ k -> der (S ^ k) ≈ D.S ^ k
lemma-der' ₀ = PB.refl
lemma-der' ₁ = PB.refl
lemma-der' (₂₊ k) = PB.cong PB.refl (lemma-der' (₁₊ k))


lemma-der'' : ∀ k ->
  let
  open PB ((₁₊ n) QRel,_===₃_)
  k' = fromℕ< (m%n<n k p)
  in
  der (S ^ k) ≈ D.S^ k'
lemma-der'' {n} k = begin
  der (S ^ k) ≈⟨ lemma-der' k ⟩
  D.S ^ k ≈⟨ lemma-S^k-% k ⟩
  D.S ^ (k Nat.% p) ≈⟨ refl' (Eq.cong (D.S ^_) (Eq.sym ( toℕ-fromℕ< (m%n<n k p)))) ⟩
  D.S ^ toℕ k' ≈⟨ sym (axiom (D.srel (D.derived-S k'))) ⟩
  D.S^ k' ∎
  where
  open PB ((₁₊ n) QRel,_===₃_)
  open PP ((₁₊ n) QRel,_===₃_)
  open SR word-setoid
  k' = fromℕ< (m%n<n k p)
  open ND.Lemmas0 n

lemma-der : let open PB ((₁₊ n) QRel,_===₃_) in
  ∀ k -> der (S^ k) ≈ D.S^ k
lemma-der {n} k = begin
  der (S^ k) ≈⟨ refl ⟩
  der (S ^ toℕ k) ≈⟨ lemma-der'' (toℕ k) ⟩
  D.S^ k' ≈⟨ refl' (Eq.cong D.S^ (fromℕ<-cong (toℕ k Nat.% p) (toℕ k) (m<n⇒m%n≡m (toℕ<n k)) (m%n<n (toℕ k) p) (toℕ<n k))) ⟩
  D.S^ k'' ≈⟨ refl' (Eq.cong D.S^ (fromℕ<-toℕ k (toℕ<n k))) ⟩
  D.S^ k ∎
  where
  open PB ((₁₊ n) QRel,_===₃_)
  open PP ((₁₊ n) QRel,_===₃_)
  open SR word-setoid
  k'' : ℤ ₚ
  k'' = fromℕ< (toℕ<n k)
  k' = fromℕ< (m%n<n (toℕ k) p)
  open ND.Lemmas0 n




lemma-derH : ∀ k ->
  let
  open PB ((₁₊ n) QRel,_===₃_)
  in
  der (H^ k) ≈ D.H^ k
lemma-derH {n} ₀ = PB.sym (PB.axiom (D.srel (D.derived-H ₀)))
lemma-derH {n} ₁ = PB.refl
lemma-derH {n} ₂ = PB.sym (PB.axiom (D.srel (D.derived-H ₂)))
lemma-derH {n} ₃ = PB.sym (PB.axiom (D.srel (D.derived-H ₃)))



lemma-derM : let open PB ((₁₊ n) QRel,_===₃_) in
  ∀ k -> der (M k) ≈ D.M k
lemma-derM {n} k*@(k , nz) = cong (lemma-der k) (cong (lemma-derH ₁) (cong (lemma-der k⁻¹) (cong (lemma-derH ₁) (cong (lemma-der k) refl))))
  where
  open PB ((₁₊ n) QRel,_===₃_)
  open PP ((₁₊ n) QRel,_===₃_)
  open SR word-setoid
  k⁻¹ = (k* ⁻¹) .proj₁


lemma-derCZ' : let open PB ((₂₊ n) QRel,_===₃_) in
  ∀ k -> der (CZ ^ k) ≈ D.CZ ^ k
lemma-derCZ' ₀ = PB.refl
lemma-derCZ' ₁ = PB.refl
lemma-derCZ' (₂₊ k) = PB.cong PB.refl (lemma-derCZ' (₁₊ k))


lemma-derCZ'' : ∀ k ->
  let
  open PB ((₂₊ n) QRel,_===₃_)
  k' = fromℕ< (m%n<n k p)
  in
  der (CZ ^ k) ≈ D.CZ^ k'
lemma-derCZ'' {n} k = begin
  der (CZ ^ k) ≈⟨ lemma-derCZ' k ⟩
  D.CZ ^ k ≈⟨ lemma-CZ^k-% k ⟩
  D.CZ ^ (k Nat.% p) ≈⟨ refl' (Eq.cong (D.CZ ^_) (Eq.sym ( toℕ-fromℕ< (m%n<n k p)))) ⟩
  D.CZ ^ toℕ k' ≈⟨ sym (axiom (D.srel (D.derived-CZ k'))) ⟩
  D.CZ^ k' ∎
  where
  open PB ((₂₊ n) QRel,_===₃_)
  open PP ((₂₊ n) QRel,_===₃_)
  open SR word-setoid
  k' = fromℕ< (m%n<n k p)
  open ND.Lemmas-1 n

lemma-derCZ : let open PB ((₂₊ n) QRel,_===₃_) in
  ∀ k -> der (CZ^ k) ≈ D.CZ^ k
lemma-derCZ {n} k = begin
  der (CZ^ k) ≈⟨ refl ⟩
  der (CZ ^ toℕ k) ≈⟨ lemma-derCZ'' (toℕ k) ⟩
  D.CZ^ k' ≈⟨ refl' (Eq.cong D.CZ^ (fromℕ<-cong (toℕ k Nat.% p) (toℕ k) (m<n⇒m%n≡m (toℕ<n k)) (m%n<n (toℕ k) p) (toℕ<n k))) ⟩
  D.CZ^ k'' ≈⟨ refl' (Eq.cong D.CZ^ (fromℕ<-toℕ k (toℕ<n k))) ⟩
  D.CZ^ k ∎
  where
  open PB ((₂₊ n) QRel,_===₃_)
  open PP ((₂₊ n) QRel,_===₃_)
  open SR word-setoid
  k'' : ℤ ₚ
  k'' = fromℕ< (toℕ<n k)
  k' = fromℕ< (m%n<n (toℕ k) p)
  open ND.Lemmas0 n

module LM2 where


  ⟦_⟧ₚ : Postfix -> Word (Gen (₂₊ n))
  ⟦ s , mc2 , mc1 ⟧ₚ = S^ s • (H^ ₃ • CZ • H) • ⟦ mc2 ⟧ₘ₊ ↑ • ⟦ mc1 ⟧ₘ₊
  
  ⟦_⟧₂ : Cosets2 -> Word (Gen (₂₊ n))
  ⟦ case-||ₐ k p ⟧₂ = CZ^ k • ⟦ p ⟧ₚ
  ⟦ case-|| (k , _) l p ⟧₂ = CZ^ k • H^ ₃ ↑ • S^ l ↑ • ⟦ p ⟧ₚ
  ⟦ case-Ex-| nf1 mc ⟧₂ = Ex • CZ • ⟦ nf1 ⟧₁ ↑ • ⟦ mc ⟧ₘ₊
  ⟦ case-| mc nf1 ⟧₂ = CZ • ⟦ mc ⟧ₘ₊ ↑ • ⟦ nf1 ⟧₁
  ⟦ case-nf1 nf1 ⟧₂ = ⟦ nf1 ⟧₁
  ⟦ case-Ex-nf1 nf1 ⟧₂ = Ex • ⟦ nf1 ⟧₁ ↑


  module Sym  = Symplectic
  module Sym'  = Lemmas-Sym
  module SymDerived  = ND.Symplectic-Derived-Gen

  open Symplectic renaming (Gen to Gen₁ ; _QRel,_===_ to _QRel,_===₁_) using ()
  Gen₂ = Gen₁
  open Simplified-Relations renaming (_QRel,_===_ to _QRel,_===₂_) using ()

  open Symplectic-GroupLike renaming (grouplike to grouplike₁) using ()
  open Symplectic-Sim-GroupLike renaming (grouplike to grouplike₂) using ()
  open ND.Symplectic-Derived-GroupLike renaming (grouplike to grouplike₃) using ()


  open import Algebra.Bundles using (Group)
  open import Algebra.Morphism.Structures using (module GroupMorphisms)

  open GroupMorphisms

  import Examples.Groups.Symplectic.ExtendedGate.NF2 p-2 p-prime as LM2T 
  module LM2P = LM2T.LM2
  open LM2P renaming (⟦_⟧₂ to ⟦_⟧₂' ; ⟦_⟧ₚ to ⟦_⟧ₚ') using ()



  sim-of-der : ∀ {n} -> Word (Gen₂ n) -> Word (Gen₃ n)
  sim-of-der {n} = λ z → ε



  der-of-sim : ∀ {n} -> Word (Gen₂ n) -> Word (Gen₃ n)
  der-of-sim {n} = der

  lemma-der-↑ : ∀ w -> let open PB ((₁₊ n) QRel,_===₃_) in
    (der {₁₊ n} (w ↑)) ≈ (der {n} w) D.↑
  lemma-der-↑ w@([ H-gen ]ʷ) = PB.refl
  lemma-der-↑ [ S-gen ]ʷ = PB.refl
  lemma-der-↑ [ CZ-gen ]ʷ = PB.refl
  lemma-der-↑ [ x ↥ ]ʷ = PB.refl
  lemma-der-↑ ε = PB.refl
  lemma-der-↑ (w • w₁) = PB.cong (lemma-der-↑ w) (lemma-der-↑ w₁)

  lemma-der-MC : let open PB ((₁₊ n) QRel,_===₃_) in
    ∀ mc -> der ⟦ mc ⟧ₘ₊ ≈ ⟦ mc ⟧ₘ₊'
  lemma-der-MC {n} (m , c@ε) = cong (lemma-derM m) refl
    where
    open PB ((₁₊ n) QRel,_===₃_)
  lemma-der-MC {n} (m , c@(HS^ k)) = cong (lemma-derM m) ((cong refl (lemma-der k)))
    where
    open PB ((₁₊ n) QRel,_===₃_)


  lemma-der-NF1 : let open PB ((₁₊ n) QRel,_===₃_) in
    ∀ nf1 -> der ⟦ nf1 ⟧₁ ≈ ⟦ nf1 ⟧₁'
  lemma-der-NF1 {n} nf1@(s , m , ε) = begin
    der ⟦ nf1 ⟧₁ ≈⟨ cong (lemma-der s) (cong (lemma-derM m) refl) ⟩
    ⟦ nf1 ⟧₁' ∎
    where
    open PB ((₁₊ n) QRel,_===₃_)
    open PP ((₁₊ n) QRel,_===₃_)
    open SR word-setoid

  lemma-der-NF1 {n} nf1@(s , m , HS^ k) = begin
    der ⟦ nf1 ⟧₁ ≈⟨ cong (lemma-der s) (cong (lemma-derM m) (cong refl (lemma-der k))) ⟩
    ⟦ nf1 ⟧₁' ∎
    where
    open PB ((₁₊ n) QRel,_===₃_)
    open PP ((₁₊ n) QRel,_===₃_)
    open SR word-setoid

  lemma-der-Ex : let open PB ((₂₊ n) QRel,_===₃_) in
    der Ex ≈ D.Ex
  lemma-der-Ex {n} = cong (lemma-derCZ ₁) (cright (cright cong (lemma-derCZ ₁) (cright cright cong (lemma-derCZ ₁) refl)))
    where
    open PB ((₂₊ n) QRel,_===₃_)

  lemma-der-Postfix : let open PB ((₂₊ n) QRel,_===₃_) in
    ∀ pf -> der ⟦ pf ⟧ₚ ≈ ⟦ pf ⟧ₚ'
  lemma-der-Postfix {n} pf@(s , mc2 , mc1) = cong (lemma-der s) (cong (cong (sym (axiom (SymDerived.srel (SymDerived.derived-H ₃)))) refl) (cong (trans (lemma-der-↑ ⟦ mc2 ⟧ₘ₊) (D.lemma-cong↑ _ _ (lemma-der-MC mc2))) (lemma-der-MC mc1)))
    where
    open PB ((₂₊ n) QRel,_===₃_)


  lemma-der-of-sim : let open PB ((₂₊ n) QRel,_===₃_) in
  
    ∀ lm -> der-of-sim ⟦ lm ⟧₂ ≈ ⟦ lm ⟧₂'
    
  lemma-der-of-sim {n} (case-||ₐ x x₁) = cong (lemma-derCZ x) (lemma-der-Postfix x₁)
    where
    open PB ((₂₊ n) QRel,_===₃_)
  lemma-der-of-sim {n} (case-|| x x₁ x₂) = cong (lemma-derCZ (x .proj₁)) (cong (sym (axiom (SymDerived.cong↑ (SymDerived.srel (SymDerived.derived-H ₃))))) (cong ((trans (lemma-der-↑ (S^ x₁)) (D.lemma-cong↑ _ _ (lemma-der (x₁))))) (lemma-der-Postfix x₂)))
    where
    open PB ((₂₊ n) QRel,_===₃_)
  lemma-der-of-sim {n} (case-Ex-| x x₁) = cong refl (cright cong (trans (lemma-der-↑ ⟦ x ⟧₁) (D.lemma-cong↑ _ _ (lemma-der-NF1 x))) (lemma-der-MC x₁))
    where
    open PB ((₂₊ n) QRel,_===₃_)
  lemma-der-of-sim {n} (case-| x x₁) = cong refl (cong (trans (lemma-der-↑ ⟦ x ⟧ₘ₊) (D.lemma-cong↑ _ _ (lemma-der-MC x))) (lemma-der-NF1 x₁))
    where
    open PB ((₂₊ n) QRel,_===₃_)
  lemma-der-of-sim {n} (case-nf1 (s , m , c)) = lemma-der-NF1 (s , m , c)
  
  lemma-der-of-sim {n} (case-Ex-nf1 x) = cong lemma-der-Ex (trans (lemma-der-↑ ⟦ x ⟧₁) (D.lemma-cong↑ _ _ (lemma-der-NF1 x)))
    where
    open PB ((₂₊ n) QRel,_===₃_)


  open import Examples.Groups.Symplectic.ExtendedGate.Soundness p-2 p-prime

  Theorem-LM2 :

    ∀ (ps qs : Pauli 2) (t : Pauli n) ->
    sform ps qs ≡ ₁ ->
    -----------------------------------------------
    ∃ \ lm -> act ⟦ lm ⟧₂ (ps ++ t) ≡ pZ ∷ pI ∷ t ×
              act ⟦ lm ⟧₂ (qs ++ t) ≡ pX ∷ pI ∷ t

  Theorem-LM2 ps qs t cond with LM2P.Theorem-LM2 ps qs t cond
  ... | (lm , pr) = lm , claim1 , claim2
    where
    open ≡-Reasoning
    claim1 : act ⟦ lm ⟧₂ (ps ++ t) ≡ pZ ∷ pI ∷ t
    claim1 = begin
      act ⟦ lm ⟧₂ (ps ++ t) ≡⟨ auto ⟩
      dact (der-of-sim ⟦ lm ⟧₂) (ps ++ t) ≡⟨ act-sound _ _ (lemma-der-of-sim lm) ((ps ++ t)) ⟩
      dact (⟦ lm ⟧₂') (ps ++ t) ≡⟨ pr .proj₁ ⟩
      pZ ∷ pI ∷ t ∎

    claim2 : act ⟦ lm ⟧₂ (qs ++ t) ≡ pX ∷ pI ∷ t
    claim2 = begin
      act ⟦ lm ⟧₂ (qs ++ t) ≡⟨ auto ⟩
      dact (der-of-sim ⟦ lm ⟧₂) (qs ++ t) ≡⟨ act-sound _ _ (lemma-der-of-sim lm) ((qs ++ t)) ⟩
      dact (⟦ lm ⟧₂') (qs ++ t) ≡⟨ pr .proj₂ ⟩
      pX ∷ pI ∷ t ∎

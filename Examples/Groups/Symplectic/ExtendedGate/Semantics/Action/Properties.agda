{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; inspect ; setoid ; module ≡-Reasoning ; _≗_) renaming ([_] to [_]')
import Relation.Binary.PropositionalEquality as Eq


open import Function using (id)
open import Function.Definitions using (Injective)

open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Agda.Builtin.Nat using (_-_)
import Data.Nat as Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec hiding ([_])
open import Data.Fin hiding (_+_ ; _-_)

open import Data.Maybe
open import Data.Sum using ([_,_] ; [_,_]′)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)

open import Word.Base as WB hiding (wfoldl)
open import Word.Properties
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full

open import Presentation.Construct.Base hiding (_*_ ; _⊕_)


open import Data.Fin using (toℕ ; zero ; fromℕ)
open import Data.Fin.Properties as FP using (toℕ-fromℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality



module Examples.Groups.Symplectic.ExtendedGate.Semantics.Action.Properties (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where





open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.ExtendedGate.Syntactics p-2 p-prime


open Symplectic-Derived-Gen
open import Examples.Groups.Pauli.Semantics p-2 p-prime public

-- The action definitions act1 / act now live in the Base submodule,
-- re-exported here so downstream (which imports Action) is unaffected.
open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Action.Base p-2 p-prime public
open import Examples.Groups.Symplectic.ExtendedGate.Semantics.Action.ZpCalculation p-2 p-prime

lemma-act-↑ : ∀ {n} (w : Word (Gen n)) → (p : Pauli1 ) (q : Pauli n) → act (w ↑) (p ∷ q) ≡ p ∷ act w q
lemma-act-↑ {n} [ x ]ʷ p q = auto
lemma-act-↑ {n} ε p q = auto
lemma-act-↑ {n} (w • v) p q = begin
  act ((w • v) ↑) (p ∷ q) ≡⟨ auto ⟩
  act (w ↑) (act (v ↑) (p ∷ q)) ≡⟨ Eq.cong (act (w ↑)) (lemma-act-↑ v p q) ⟩
  act (w ↑) (p ∷ act v q) ≡⟨ lemma-act-↑ w p (act v q) ⟩
  p ∷ act w (act v q) ≡⟨ auto ⟩
  p ∷ act (w • v) q ∎
  where open ≡-Reasoning



open import Data.Nat.DivMod
open import Algebra.Properties.Ring (+-*-ring p-2)


lemma-act-Sᵏ : ∀ {n} k ps -> let k' = fromℕ< (m%n<n k p) in
  act {₁₊ n} (S ^ k) ps ≡ act (S^ k') ps
lemma-act-Sᵏ {n} k@₀ ps@((a , b) ∷ t) = begin  
  act (S ^ k) ps ≡⟨ Eq.cong (\ xx -> (a , xx) ∷ t) (Eq.sym (Eq.trans (Eq.cong (b +_) (*-zeroʳ a)) (+-identityʳ b))) ⟩
  (a , b + a * k') ∷ t ≡⟨ auto ⟩
  act (S^ k') ps ∎
  where
  open ≡-Reasoning
  k' = fromℕ< (m%n<n k p)    
lemma-act-Sᵏ {n} k@₁ ps@((a , b) ∷ t) = auto
lemma-act-Sᵏ {n} k@(₂₊ k-2) ps@((a , b) ∷ t) = begin
  act (S • S ^ ₁₊ k-2) ((a , b) ∷ t) ≡⟨ auto ⟩
  act S (act (S ^ ₁₊ k-2) ((a , b) ∷ t)) ≡⟨ Eq.cong (act S) (lemma-act-Sᵏ (₁₊ k-2) ((a , b) ∷ t)) ⟩
  act S (act (S^ k'-1) ((a , b) ∷ t)) ≡⟨ auto ⟩
  act S ((a , b + a * k'-1) ∷ t) ≡⟨ auto ⟩
  (a , b + a * k'-1 + a * ₁) ∷ t ≡⟨ Eq.cong (\ xx -> (a , xx) ∷ t) (+-assoc b (a * k'-1) (a * ₁)) ⟩
  (a , b + (a * k'-1 + a * ₁)) ∷ t ≡⟨ Eq.cong (λ xx → (a , xx) ∷ t) (Eq.cong (b +_) (Eq.sym (*-distribˡ-+ a k'-1 ₁))) ⟩
  (a , b + a * (k'-1 + ₁)) ∷ t ≡⟨ Eq.cong (λ xx → (a , xx) ∷ t) (Eq.cong (b +_) (Eq.cong (a *_) aux-k'-1+1)) ⟩
  (a , b + a * k') ∷ t ≡⟨ auto ⟩
  act (S^ k') ((a , b) ∷ t) ∎
  where
  open ≡-Reasoning
  open Lemmas0 n
  k-1 = ₁₊ k-2
  k' = fromℕ< (m%n<n k p)  
  k'-1 = fromℕ< (m%n<n k-1 p)
  aux-k'k : (toℕ k'-1 Nat.+ 1) Nat.% p ≡ k Nat.% p
  aux-k'k = begin
    (toℕ k'-1 Nat.+ 1) Nat.% p ≡⟨ Eq.cong (Nat._% p) (NP.+-comm (toℕ k'-1) 1) ⟩
    (1 Nat.+ (toℕ k'-1)) Nat.% p ≡⟨ Eq.cong (Nat._% p) (Eq.cong (1 Nat.+_) (FP.toℕ-fromℕ< (m%n<n k-1 p))) ⟩
    (1 Nat.% p Nat.+ (k-1) Nat.% p) Nat.% p ≡⟨ Eq.sym (%-distribˡ-+ 1 k-1 p) ⟩
    k Nat.% p ∎
  aux-k'-1+1 : k'-1 + ₁ ≡ k'
  aux-k'-1+1 = begin
    k'-1 + ₁ ≡⟨ FP.fromℕ<-cong ( (toℕ k'-1 Nat.+ 1) Nat.% p) (k Nat.% p) aux-k'k (m%n<n (toℕ k'-1 Nat.+ 1) p) (m%n<n k p) ⟩
    k' ∎


lemma-act-CZᵏ : ∀ {n} k ps -> let k' = fromℕ< (m%n<n k p) in
  act {₂₊ n} (CZ ^ k) ps ≡ act (CZ^ k') ps
lemma-act-CZᵏ {n} k@₀ ps@((a , b) ∷ (a' , b') ∷ t) = begin  
  act (CZ ^ k) ps ≡⟨ Eq.cong₂ (\ xx yy -> (a , xx) ∷ (a' , yy) ∷ t) (Eq.sym (Eq.trans (Eq.cong (b +_) (*-zeroʳ a')) (+-identityʳ b))) (Eq.sym (Eq.trans (Eq.cong (b' +_) (*-zeroʳ a)) (+-identityʳ b'))) ⟩
  (a , b + a' * k') ∷ (a' , b' + a * k' ) ∷ t ≡⟨ auto ⟩
  act (CZ^ k') ps ∎
  where
  open ≡-Reasoning
  k' = fromℕ< (m%n<n k p)    
lemma-act-CZᵏ {n} k@₁ ps@((a , b) ∷ (a' , b') ∷ t) = auto
lemma-act-CZᵏ {n} k@(₂₊ k-2) ps@((a , b) ∷ (a' , b') ∷ t) = begin
  act (CZ • CZ ^ ₁₊ k-2) ((a , b) ∷ (a' , b') ∷ t) ≡⟨ auto ⟩
  act CZ (act (CZ ^ ₁₊ k-2) ((a , b) ∷ (a' , b') ∷ t)) ≡⟨ Eq.cong (act CZ) (lemma-act-CZᵏ (₁₊ k-2) ((a , b) ∷ (a' , b') ∷ t)) ⟩
  act CZ (act (CZ^ k'-1) ((a , b) ∷ (a' , b') ∷ t)) ≡⟨ auto ⟩
  act CZ ((a , b + a' * k'-1) ∷ (a' , b' + a * k'-1) ∷ t) ≡⟨ auto ⟩
  (a , b + a' * k'-1 + a' * ₁) ∷ (a' , b' + a * k'-1 + a * ₁) ∷ t ≡⟨ Eq.cong₂ (\ xx  yy -> (a , xx) ∷ (a' , yy) ∷ t) (+-assoc b (a' * k'-1) (a' * ₁)) (+-assoc b' (a * k'-1) (a * ₁)) ⟩
  (a , b + (a' * k'-1 + a' * ₁)) ∷ (a' , b' + (a * k'-1 + a * ₁)) ∷ t ≡⟨ Eq.cong₂ (λ xx yy → (a , xx) ∷ (a' , yy) ∷ t) (Eq.cong (b +_) (Eq.sym (*-distribˡ-+ a' k'-1 ₁))) (Eq.cong (b' +_) (Eq.sym (*-distribˡ-+ a k'-1 ₁))) ⟩
  (a , b + a' * (k'-1 + ₁)) ∷ (a' , b' + a * (k'-1 + ₁)) ∷ t ≡⟨ Eq.cong₂ (λ xx yy → (a , xx) ∷ (a' , yy) ∷ t) (Eq.cong (b +_) (Eq.cong (a' *_) aux-k'-1+1)) (Eq.cong (b' +_) (Eq.cong (a *_) aux-k'-1+1)) ⟩
  (a , b + a' * k') ∷ (a' , b' + a * k') ∷ t ≡⟨ auto ⟩
  act (CZ^ k') ((a , b) ∷ (a' , b') ∷ t) ∎
  where
  open ≡-Reasoning
  open Lemmas0 n
  k-1 = ₁₊ k-2
  k' = fromℕ< (m%n<n k p)  
  k'-1 = fromℕ< (m%n<n k-1 p)
  aux-k'k : (toℕ k'-1 Nat.+ 1) Nat.% p ≡ k Nat.% p
  aux-k'k = begin
    (toℕ k'-1 Nat.+ 1) Nat.% p ≡⟨ Eq.cong (Nat._% p) (NP.+-comm (toℕ k'-1) 1) ⟩
    (1 Nat.+ (toℕ k'-1)) Nat.% p ≡⟨ Eq.cong (Nat._% p) (Eq.cong (1 Nat.+_) (FP.toℕ-fromℕ< (m%n<n k-1 p))) ⟩
    (1 Nat.% p Nat.+ (k-1) Nat.% p) Nat.% p ≡⟨ Eq.sym (%-distribˡ-+ 1 k-1 p) ⟩
    k Nat.% p ∎
  aux-k'-1+1 : k'-1 + ₁ ≡ k'
  aux-k'-1+1 = begin
    k'-1 + ₁ ≡⟨ FP.fromℕ<-cong ( (toℕ k'-1 Nat.+ 1) Nat.% p) (k Nat.% p) aux-k'k (m%n<n (toℕ k'-1 Nat.+ 1) p) (m%n<n k p) ⟩
    k' ∎


lemma-act-ₕ|ₕ : ∀ {n} a b a' b' t -> 
  act {₂₊ n} ₕ|ₕ ((a , b) ∷ (a' , b') ∷ t) ≡ ((- a + - a' , - b) ∷ (a' , b' + - b) ∷ t)
lemma-act-ₕ|ₕ {n} a b a' b' t = begin
  act {₂₊ n} ₕ|ₕ ((a , b) ∷ (a' , b') ∷ t) ≡⟨ auto ⟩
  act {₂₊ n} (H • CZ) ((- b , a) ∷ (a' , b') ∷ t) ≡⟨ auto ⟩
  act {₂₊ n} (H) ((- b , a + a' * ₁) ∷ (a' , b' + - b * ₁) ∷ t) ≡⟨ auto ⟩
  ((- (a + a' * ₁) , - b) ∷ (a' , b' + - b * ₁) ∷ t) ≡⟨ Eq.cong₂ (\ xx yy -> ((- (a + xx) , - b) ∷ (a' , b' + yy) ∷ t)) (*-identityʳ a') (*-identityʳ (- b)) ⟩
  ((- (a + a') , - b) ∷ (a' , b' + - b) ∷ t) ≡⟨ Eq.cong (\ xx -> ((xx , - b) ∷ (a' , b' + - b) ∷ t)) (Eq.sym (-‿+-comm a a')) ⟩
  ((- a + - a' , - b) ∷ (a' , b' + - b) ∷ t) ∎
  where
  open ≡-Reasoning


lemma-act-ʰ|ʰ : ∀ {n} a b a' b' t -> 
  act {₂₊ n} ʰ|ʰ ((a , b) ∷ (a' , b') ∷ t) ≡ ((a , b + - b') ∷ (- a' + - a , - b') ∷ t)
lemma-act-ʰ|ʰ {n} a b a' b' t = begin
  act {₂₊ n} ʰ|ʰ ((a , b) ∷ (a' , b') ∷ t) ≡⟨ auto ⟩
  act {₂₊ n} (H ↑ • CZ) ((a , b) ∷ (- b' , a') ∷ t) ≡⟨ auto ⟩
  act {₂₊ n} (H ↑) ((a , b + - b' * ₁) ∷ (- b' , a' + a * ₁) ∷ t) ≡⟨ auto ⟩
  ((a , b + - b' * ₁) ∷ (- (a' + a * ₁) , - b') ∷ t) ≡⟨ Eq.cong₂ (\ yy xx -> ((a , b + yy) ∷ (- (a' + xx) , - b') ∷ t)) (*-identityʳ (- b')) (*-identityʳ a)  ⟩
  ((a , b + - b') ∷ (- (a' + a) , - b') ∷ t) ≡⟨ Eq.cong (\ xx -> ((a , b + - b') ∷ (xx , - b') ∷ t)) (Eq.sym (-‿+-comm a' a)) ⟩
  ((a , b + - b') ∷ (- a' + - a , - b') ∷ t) ∎
  where
  open ≡-Reasoning


lemma-act-⊥⊤ : ∀ {n} a b a' b' t -> 
  act {₂₊ n} ⊥⊤ ((a , b) ∷ (a' , b') ∷ t) ≡ (a' , - b + b') ∷ (- a' + - a , - b) ∷ t
lemma-act-⊥⊤ {n} a b a' b' t = begin
  act {₂₊ n} ⊥⊤ ((a , b) ∷ (a' , b') ∷ t) ≡⟨ Eq.cong (act {₂₊ n} ₕ|ₕ) (lemma-act-ʰ|ʰ a b a' b' t) ⟩
  act {₂₊ n} ₕ|ₕ ((a , b + - b') ∷ (- a' + - a , - b') ∷ t) ≡⟨ lemma-act-ₕ|ₕ a (b + - b') (- a' + - a) (- b') t ⟩
  ((- a + - (- a' + - a) , - (b + - b')) ∷ (- a' + - a , - b' + - (b + - b')) ∷ t) ≡⟨ cong₃ (\ xx yy zz -> (xx , yy) ∷ (- a' + - a , zz) ∷ t) (neg-neg-cancelˡ a a') (neg-sub b b') (neg-neg-cancelʳ b' b ) ⟩
  (a' , - b + b') ∷ (- a' + - a , - b) ∷ t ∎
  where
  open ≡-Reasoning


lemma-act-⊤⊥ : ∀ {n} a b a' b' t -> 
  act {₂₊ n} ⊤⊥ ((a , b) ∷ (a' , b') ∷ t) ≡ ((- a + - a' , - b') ∷ (a , - b' + b) ∷ t)
lemma-act-⊤⊥ {n} a b a' b' t = begin
  act {₂₊ n} ⊤⊥ ((a , b) ∷ (a' , b') ∷ t) ≡⟨ Eq.cong (act {₂₊ n} ʰ|ʰ) (lemma-act-ₕ|ₕ a b a' b' t) ⟩
  act {₂₊ n} ʰ|ʰ ((- a + - a' , - b) ∷ (a' , b' + - b) ∷ t) ≡⟨ lemma-act-ʰ|ʰ (- a + - a') (- b) a' (b' + - b) t ⟩
  ((- a + - a' , - b + - (b' + - b)) ∷ (- a' + - (- a + - a') , - (b' + - b)) ∷ t) ≡⟨ cong₃ (\ xx yy zz -> (- a + - a' , xx) ∷ (yy , zz) ∷ t) (neg-neg-cancelʳ b b') (neg-neg-cancelˡ a' a) (neg-sub b' b) ⟩
  ((- a + - a' , - b') ∷ (a , - b' + b) ∷ t) ∎
  where
  open ≡-Reasoning

lemma-act-⊤⊥↑CZ↓ : ∀ {n} a b a' b' a'' b'' t ->
  act {₃₊ n} (⊤⊥ ↑ • CZ ↓) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ≡ (a , b + a') ∷ (- a' + - a'' , - b'') ∷ (a' , - b'' + (b' + a)) ∷ t
lemma-act-⊤⊥↑CZ↓ {n} a b a' b' a'' b'' t = begin
  act {₃₊ n} (⊤⊥ ↑ • CZ ↓) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ≡⟨ auto ⟩
  act {₃₊ n} (⊤⊥ ↑) ((a , b + a' * ₁) ∷ (a' , b' + a * ₁) ∷ (a'' , b'') ∷ t) ≡⟨ Eq.trans (lemma-act-↑ ⊤⊥ ((a , b + a' * ₁)) ((a' , b' + a * ₁) ∷ (a'' , b'') ∷ t)) (Eq.cong ((a , b + a' * ₁) ∷_) (lemma-act-⊤⊥ a' (b' + a * ₁) a'' b'' t)) ⟩
  (a , b + a' * ₁) ∷ (- a' + - a'' , - b'') ∷ (a' , - b'' + (b' + a * ₁)) ∷ t ≡⟨ Eq.cong₂ (\ xx yy -> (a , b + xx) ∷ (- a' + - a'' , - b'') ∷ (a' , - b'' + (b' + yy)) ∷ t) (*-identityʳ a') (*-identityʳ a) ⟩
  (a , b + a') ∷ (- a' + - a'' , - b'') ∷ (a' , - b'' + (b' + a)) ∷ t ∎
  where
  open ≡-Reasoning


lemma-act-⊥⊤↓CZ↑ : ∀ {n} a b a' b' a'' b'' t ->
  act {₃₊ n} (⊥⊤ ↓ • CZ ↑) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ≡ ((a' , - b + (b' + a'')) ∷ (- a' + - a , - b) ∷ (a'' , b'' + a') ∷ t)
lemma-act-⊥⊤↓CZ↑ {n} a b a' b' a'' b'' t = begin
  act {₃₊ n} (⊥⊤ ↓ • CZ ↑) ((a , b) ∷ (a' , b') ∷ (a'' , b'') ∷ t) ≡⟨ Eq.cong  (act {₃₊ n} (⊥⊤ ↓)) (lemma-act-↑ CZ ((a , b)) ((a' , b') ∷ (a'' , b'') ∷ t)) ⟩
  act {₃₊ n} (⊥⊤ ↓) ((a , b) ∷ (a' , b' + a'' * ₁) ∷ (a'' , b'' + a' * ₁) ∷ t) ≡⟨ lemma-act-⊥⊤ a b a' (b' + a'' * ₁) ((a'' , b'' + a' * ₁) ∷ t) ⟩
  ((a' , - b + (b' + a'' * ₁)) ∷ (- a' + - a , - b) ∷ (a'' , b'' + a' * ₁) ∷ t) ≡⟨ Eq.cong₂ ( \ xx yy -> ((a' , - b + (b' + xx)) ∷ (- a' + - a , - b) ∷ (a'' , b'' + yy) ∷ t)) (*-identityʳ a'') (*-identityʳ a') ⟩
  ((a' , - b + (b' + a'')) ∷ (- a' + - a , - b) ∷ (a'' , b'' + a') ∷ t) ∎
  where
  open ≡-Reasoning




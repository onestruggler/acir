------------------------------------------------------------------------
-- Presentations of groups
--
-- Finite combinatorial states for the even signed permutations on eight
-- levels.  The parity witness is irrelevant: a state is determined by
-- its eight signs and the existing symmetric-group normal form.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.StabilizerNormalForm where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_)
import Data.Bool.Properties as BP
open import Data.Fin.Base as F using (Fin ; zero ; suc)
open import Data.Nat.Base as N using (ℕ ; zero ; suc)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; tail ; replicate)
open import Data.Product.Base using (_×_ ; _,_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
import Examples.Groups.Symmetric.Syntactics as P
import Examples.Groups.Symmetric.Normalization as PN
open import Examples.Groups.CCX+HH.ThreeQubit.StabilizerGenerators using (Letter ; phase ; exchange)

parity : ∀ {n} → Vec Bool n → Bool
parity [] = false
parity (a ∷ s) = a xor parity s

toggle : ∀ {n} → Fin n → Vec Bool n → Vec Bool n
toggle zero (a ∷ s) = not a ∷ s
toggle (suc i) (a ∷ s) = a ∷ toggle i s

swap : ∀ {n} → Fin (suc n) → Vec Bool (suc (suc n)) → Vec Bool (suc (suc n))
swap zero (a ∷ b ∷ s) = b ∷ a ∷ s
swap {suc n} (suc i) (a ∷ s) = a ∷ swap i s

flip-pair : Fin 7 → Vec Bool 8 → Vec Bool 8
flip-pair i (a ∷ s) = not a ∷ toggle i s

private
  xor-notʳ : ∀ a b → a xor not b ≡ not (a xor b)
  xor-notʳ false b = refl
  xor-notʳ true b = refl

  xor-notˡ : ∀ a b → not a xor b ≡ not (a xor b)
  xor-notˡ false b = refl
  xor-notˡ true b = Eq.sym (BP.not-involutive b)

  xor-swap : ∀ a b c → a xor (b xor c) ≡ b xor (a xor c)
  xor-swap a b c = Eq.trans (Eq.sym (BP.xor-assoc a b c))
    (Eq.trans (Eq.cong (λ x → x xor c) (BP.xor-comm a b)) (BP.xor-assoc b a c))

parity-toggle : ∀ {n} (i : Fin n) s → parity (toggle i s) ≡ not (parity s)
parity-toggle zero (a ∷ s) = xor-notˡ a (parity s)
parity-toggle (suc i) (a ∷ s) = Eq.trans
  (Eq.cong (a xor_) (parity-toggle i s)) (xor-notʳ a (parity s))

parity-swap : ∀ {n} (i : Fin (suc n)) s → parity (swap i s) ≡ parity s
parity-swap zero (a ∷ b ∷ s) = xor-swap b a (parity s)
parity-swap {suc n} (suc i) (a ∷ s) = Eq.cong (a xor_) (parity-swap i s)

parity-flip-pair : ∀ i s → parity (flip-pair i s) ≡ parity s
parity-flip-pair i (a ∷ s) = Eq.trans
  (Eq.cong (not a xor_) (parity-toggle i s)) (BP.xor-annihilates-not a (parity s))

-- A finite position names an adjacent symmetric-group generator.
adjacent : ∀ {n} → Fin (suc n) → P.Gen (suc (suc n))
adjacent zero = P.gate₂ P.σ-gate
adjacent {suc n} (suc i) = adjacent i P.↥

position : ∀ {n} → P.Gen (suc n) → Fin n
position (P.gate₁ ())
position (P.gate₂ P.σ-gate) = zero
position {zero} (P.gate₀ () P.↥)
position {suc n} (g P.↥) = suc (position g)

permutation-word : PN.NF 8 → Word Letter
permutation-word p = wmap (λ g → exchange (position g)) (PN.inv-nf p)

-- Each selected tail sign toggles that row and row zero.  The parity
-- condition makes the resulting sign of row zero exactly the stored one.
phase-word : ∀ {n} → (Fin n → Fin 7) → Vec Bool n → Word Letter
phase-word f [] = ε
phase-word f (false ∷ s) = phase-word (λ i → f (suc i)) s
phase-word f (true ∷ s) = [ phase (f zero) ]ʷ • phase-word (λ i → f (suc i)) s

record NF : Set where
  constructor state
  field
    signs : Vec Bool 8
    permutation : PN.NF 8
    .even : parity signs ≡ false
open NF public

state-cong : ∀ {s t p q} {ep : parity s ≡ false} {eq : parity t ≡ false} →
  s ≡ t → p ≡ q → state s p ep ≡ state t q eq
state-cong refl refl = refl

I : NF
I = state (replicate 8 false) (PN.nf-of ε) refl

section : NF → Word Letter
section n = phase-word (λ i → i) (tail (signs n)) • permutation-word (permutation n)

step : Letter → NF → NF
step (phase i) (state s p even) = state (flip-pair i s) p
  (Eq.trans (parity-flip-pair i s) even)
step (exchange i) (state s p even) = state (swap i s)
  (PN.nf-of ([ adjacent i ]ʷ • PN.inv-nf p)) (Eq.trans (parity-swap i s) even)

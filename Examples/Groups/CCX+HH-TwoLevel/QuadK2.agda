------------------------------------------------------------------------
-- Presentations of groups
--
-- The edge K_[0,1,2,3] at a positive exponent when exactly two of the
-- first four odd entries, a < b, lie among 0..3 (Lemma A.20, Subcase
-- 3.2.3), by the positions of a and b (QuadK2.Case01, …, Case23,
-- generated).
--
-- In each case the entries 0..3 of W are written e + 2u
-- (Residue.one2 for a and b, half for the others), and KHalf gives the
-- column after K at the same exponent: its entries among 0..3 have the
-- parities of the constants shifted by Σ, the parity of the sum of the
-- u's.  So for each value of Σ the odd pair x < y after K is known, and
-- with c and d it gives the normal syllable N′ = K_[x,y,c,d]
-- (-1)_[x]^t′ (QuadK2Base.Chain).  Its sign is t′ = t xor κ: the
-- residues of the pair are compared through their sum, 2m
-- (Residue.τ-pair), and m has the parity of two of the u's.  For each
-- value of t the relation N′ K = V₁ K V₂ N of Rel6 closes the square
-- (QuadBase.sandwich).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; _<_ ; toℕ)
open import Data.Maybe.Base using (just)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (col ; ColOrth ; actM)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (pivot ; level)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (lde)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (K-gen)
import Examples.Groups.CCX+HH-TwoLevel.Reduction as R

module Examples.Groups.CCX+HH-TwoLevel.QuadK2 {n : ℕ}
  (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p)
  {k′ : ℕ} (ks : lde (col s p) ≡ suc k′) (ih : R.EdgesBelow {n} (level s))
  {P0 P1 P2 P3 : Fin n} .(p01 : P0 < P1) .(p12 : P1 < P2) .(p23 : P2 < P3)
  (z0 : toℕ P0 ≡ 0) (z1 : toℕ P1 ≡ 1) (z2 : toℕ P2 ≡ 2) (z3 : toℕ P3 ≡ 3)
  (le : R._≤ₗ_ {n} (level (actM (K-gen P0 P1 P2 P3 p01 p12 p23) s)) (level s)) where

open import Data.Empty using (⊥ ; ⊥-elim)
import Data.Nat.Properties as ℕP

open import Word.Base
open R {n} using (Path)
open import Examples.Groups.CCX+HH-TwoLevel.QuadKBase s o ps ks ih p01 p12 p23 z0 z1 z2 z3 le
  using (a ; b ; c ; a<b ; gK)
import Examples.Groups.CCX+HH-TwoLevel.QuadK2.Case01 s o ps ks ih p01 p12 p23 z0 z1 z2 z3 le as C01
import Examples.Groups.CCX+HH-TwoLevel.QuadK2.Case02 s o ps ks ih p01 p12 p23 z0 z1 z2 z3 le as C02
import Examples.Groups.CCX+HH-TwoLevel.QuadK2.Case03 s o ps ks ih p01 p12 p23 z0 z1 z2 z3 le as C03
import Examples.Groups.CCX+HH-TwoLevel.QuadK2.Case12 s o ps ks ih p01 p12 p23 z0 z1 z2 z3 le as C12
import Examples.Groups.CCX+HH-TwoLevel.QuadK2.Case13 s o ps ks ih p01 p12 p23 z0 z1 z2 z3 le as C13
import Examples.Groups.CCX+HH-TwoLevel.QuadK2.Case23 s o ps ks ih p01 p12 p23 z0 z1 z2 z3 le as C23

module _ (b3 : toℕ b ℕ.≤ 3) (c3 : 3 ℕ.< toℕ c) where

  -- a < b ≤ 3.
  edge-K2 : Path [ gK ]ʷ s o
  edge-K2 = by (toℕ a) (toℕ b) ≡.refl ≡.refl
    where
    ab-bad : ∀ {i j} → toℕ a ≡ i → toℕ b ≡ j → j ℕ.≤ i → ⊥
    ab-bad ea eb ji = ℕP.<⇒≱ (≡.subst₂ ℕ._<_ ea eb a<b) ji
    b-bad : ∀ {j} → toℕ b ≡ j → 3 ℕ.< j → ⊥
    b-bad eb h = ℕP.<⇒≱ h (≡.subst (ℕ._≤ 3) eb b3)
    by : ∀ i j → toℕ a ≡ i → toℕ b ≡ j → Path [ gK ]ʷ s o
    by i (suc (suc (suc (suc j)))) ea eb = ⊥-elim (b-bad eb (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))))
    by 0 0 ea eb = ⊥-elim (ab-bad ea eb (ℕ.z≤n))
    by 0 1 ea eb = C01.case-01 b3 c3 ea eb
    by 0 2 ea eb = C02.case-02 b3 c3 ea eb
    by 0 3 ea eb = C03.case-03 b3 c3 ea eb
    by 1 0 ea eb = ⊥-elim (ab-bad ea eb (ℕ.z≤n))
    by 1 1 ea eb = ⊥-elim (ab-bad ea eb (ℕ.s≤s (ℕ.z≤n)))
    by 1 2 ea eb = C12.case-12 b3 c3 ea eb
    by 1 3 ea eb = C13.case-13 b3 c3 ea eb
    by 2 0 ea eb = ⊥-elim (ab-bad ea eb (ℕ.z≤n))
    by 2 1 ea eb = ⊥-elim (ab-bad ea eb (ℕ.s≤s (ℕ.z≤n)))
    by 2 2 ea eb = ⊥-elim (ab-bad ea eb (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n))))
    by 2 3 ea eb = C23.case-23 b3 c3 ea eb
    by 3 0 ea eb = ⊥-elim (ab-bad ea eb (ℕ.z≤n))
    by 3 1 ea eb = ⊥-elim (ab-bad ea eb (ℕ.s≤s (ℕ.z≤n)))
    by 3 2 ea eb = ⊥-elim (ab-bad ea eb (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n))))
    by 3 3 ea eb = ⊥-elim (ab-bad ea eb (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n)))))
    by (suc (suc (suc (suc i)))) 0 ea eb = ⊥-elim (ab-bad ea eb (ℕ.z≤n))
    by (suc (suc (suc (suc i)))) 1 ea eb = ⊥-elim (ab-bad ea eb (ℕ.s≤s (ℕ.z≤n)))
    by (suc (suc (suc (suc i)))) 2 ea eb = ⊥-elim (ab-bad ea eb (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n))))
    by (suc (suc (suc (suc i)))) 3 ea eb = ⊥-elim (ab-bad ea eb (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n)))))

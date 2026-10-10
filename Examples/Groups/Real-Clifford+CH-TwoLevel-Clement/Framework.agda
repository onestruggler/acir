------------------------------------------------------------------------
-- Presentations of groups
--
-- Paths over any normal-word function, at a level L = (p + 1, k, ℓ).
--
-- The proof of the hard edge (Route, Sound, Hard) uses three things
-- about the normal words nw: paths compose and run both ways, the
-- edges with both ends below L are paths (EdgesBelow), and so are the
-- edges out of the states at L that do not go up and are not hard
-- (PlainEdges).  It holds for any nw with these: the output of
-- Algorithm 1 of Hadamard-Pi (Real-Clifford+CH-TwoLevel.Reduction), or
-- of Clément's (Thesis).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Nat.Base as ℕ using (ℕ ; suc)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Word.Base using (Word)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (Gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics using (ColOrth)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Framework {n : ℕ} (p : Fin n) (k′ ℓ : ℕ)
  (nw : (M : Matrix n n D) → .(ColOrth M) → Word (Gen n)) where

open import Data.Bool.Base using (true)
open import Data.Fin.Base using (_<_)
open import Data.Unit.Base using (⊤)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (rbit ; oddᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (_!_ ; num ; Odd)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column using (nodd)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics hiding (Z)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (level ; _<ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (sound-act ; act-gg ; _≤ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (gen-gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PairLevels p k′ ℓ using (L ; module State)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

------------------------------------------------------------------------
-- Paths

nw-cong : {M M′ : Matrix n n D} → M ≡ M′ → .(o : ColOrth M) .(o′ : ColOrth M′) → nw M o ≡ nw M′ o′
nw-cong ≡.refl o o′ = ≡.refl

Path : (w : Word (Gen n)) (M : Matrix n n D) → .(ColOrth M) → Set
Path w M o = nw (actMʷ w M) (ColOrth-actMʷ w o) • w ≈ nw M o

path-ε : (M : Matrix n n D) .(o : ColOrth M) → Path ε M o
path-ε M o = right-unit

path-• : (u v : Word (Gen n)) (M : Matrix n n D) .(o : ColOrth M) →
         Path u (actMʷ v M) (ColOrth-actMʷ v o) → Path v M o → Path (u • v) M o
path-• u v M o pu pv = begin
  nw (actMʷ u (actMʷ v M)) (ColOrth-actMʷ (u • v) o) • (u • v)    ≈⟨ sym assoc ⟩
  (nw (actMʷ u (actMʷ v M)) (ColOrth-actMʷ (u • v) o) • u) • v    ≈⟨ cleft pu ⟩
  nw (actMʷ v M) (ColOrth-actMʷ v o) • v                          ≈⟨ pv ⟩
  nw M o                                                          ∎

path-cong : {w w′ : Word (Gen n)} → w ≈ w′ → (M : Matrix n n D) .(o : ColOrth M) → Path w M o → Path w′ M o
path-cong {w} {w′} e M o pth = begin
  nw (actMʷ w′ M) (ColOrth-actMʷ w′ o) • w′    ≈⟨ cleft refl′ (nw-cong (≡.sym (sound-act e M)) _ _) ⟩
  nw (actMʷ w M) (ColOrth-actMʷ w o) • w′      ≈⟨ cright sym e ⟩
  nw (actMʷ w M) (ColOrth-actMʷ w o) • w       ≈⟨ pth ⟩
  nw M o                                       ∎

back : (g : Gen n) (M : Matrix n n D) .(o : ColOrth M) →
       Path [ g ]ʷ (actM g M) (ColOrth-actMʷ [ g ]ʷ o) → Path [ g ]ʷ M o
back g M o pth = begin
  nw (actM g M) (ColOrth-actMʷ [ g ]ʷ o) • [ g ]ʷ
    ≈⟨ cleft sym pth ⟩
  (nw (actM g (actM g M)) (ColOrth-actMʷ [ g ]ʷ (ColOrth-actMʷ [ g ]ʷ o)) • [ g ]ʷ) • [ g ]ʷ
    ≈⟨ assoc ⟩
  nw (actM g (actM g M)) (ColOrth-actMʷ [ g ]ʷ (ColOrth-actMʷ [ g ]ʷ o)) • ([ g ]ʷ • [ g ]ʷ)
    ≈⟨ cright gen-gen g ⟩
  nw (actM g (actM g M)) (ColOrth-actMʷ [ g ]ʷ (ColOrth-actMʷ [ g ]ʷ o)) • ε
    ≈⟨ right-unit ⟩
  nw (actM g (actM g M)) (ColOrth-actMʷ [ g ]ʷ (ColOrth-actMʷ [ g ]ʷ o))
    ≈⟨ refl′ (nw-cong (act-gg g M) _ o) ⟩
  nw M o ∎

------------------------------------------------------------------------
-- The edges the hard edge needs

-- Both ends below L.
EdgesBelow : Set
EdgesBelow = ∀ (g : Gen n) M .(o : ColOrth M) → level M <ₗ L → level (actM g M) <ₗ L → Path [ g ]ʷ M o

-- An H that is not hard at a state at L: two odd entries are in one
-- class.
PlainAt : (N : Matrix n n D) .(oN : ColOrth N) → level N ≡ L → Gen n → Set
PlainAt N oN eqN (H-gen a b _) =
  oddᶻ (State.W N oN eqN ! a) ≡ true → oddᶻ (State.W N oN eqN ! b) ≡ true →
  rbit (State.W N oN eqN ! a) ≡ rbit (State.W N oN eqN ! b)
PlainAt N oN eqN (X-gen _ _ _) = ⊤
PlainAt N oN eqN (Z-gen _) = ⊤

-- Out of a state at L, not going up, not hard.
PlainEdges : Set
PlainEdges = ∀ (N : Matrix n n D) .(oN : ColOrth N) (eqN : level N ≡ L) (g : Gen n) →
             level (actM g N) ≤ₗ L → PlainAt N oN eqN g → Path [ g ]ʷ N oN

-- The hard edges: H on two odd entries of different classes when
-- exactly four entries are odd (Real-Clifford+CH-TwoLevel.PairEdges).
Hard : Set
Hard = ∀ (M : Matrix n n D) .(o : ColOrth M) → level M ≡ L → nodd (num (col M p)) ≡ 4 →
       ∀ c d .(cd : c < d) → Odd (num (col M p) ! c) → Odd (num (col M p) ! d) →
       rbit (num (col M p) ! c) ≢ rbit (num (col M p) ! d) → Path [ H-gen c d cd ]ʷ M o

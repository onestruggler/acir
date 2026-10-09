------------------------------------------------------------------------
-- Presentations of groups
--
-- The edges H on valid pairs, at every state of a level L with
-- positive exponent, given the edges below L; and the edges X along
-- valid pairs.
--
-- * A valid pair (i, j) is the canonical pair (i₁, i₂), or disjoint
--   from it (a commuting square), or shares one index with it; then
--   i₁, i₂, the other index and a fourth member of the class (classes
--   have evenly many members) are four odd entries of one class, and
--   the diamond gives the edge.
-- * X_[i,j] along a valid pair: Z_[j] H_[i,j] = H_[i,j] X_[i,j] (d2)
--   closes a square with the edges H_[i,j] at both ends.
-- * Hs u v, the symmetric word, along a valid pair in either order.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Product.Base using (_,_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction using (EdgesBelow)

module Examples.Groups.Real-Clifford+CH-TwoLevel.PairValid {n : ℕ} (p : Fin n) (k′ ℓ : ℕ)
  (ih : EdgesBelow {n} (suc (toℕ p) , suc k′ , ℓ)) where

open import Data.Bool.Base using (Bool ; true ; false ; _∨_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (_<_ ; _≤_)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (∃ ; _×_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; recompute)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (oddℕ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; Z ; module ZR ; oddᶻ ; rbit)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (num ; Odd)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Xᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (level ; _<ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Levels using (lde-X)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Counting using (search ; count-three)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric {n} using (Hs ; Hs-< ; Hs->)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (Path ; Low ; path-•)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PathTools {n} using (module Below)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PairBase p k′ ℓ ih
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Diamond p k′ ℓ ih using (diamond)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid
open Below {L = L} ih using (bridge)

private
  sym≢ : ∀ {x y : Fin n} → x ≢ y → y ≢ x
  sym≢ ne e = ne (≡.sym e)

  true≢false : true ≢ false
  true≢false ()

  -- Is w one of x, y, z?
  in3 : Fin n → Fin n → Fin n → Fin n → Bool
  in3 x y z w = does (w FinP.≟ x) ∨ (does (w FinP.≟ y) ∨ does (w FinP.≟ z))

  in3-true : ∀ {x y z w} → in3 x y z w ≡ true → w ≡ x ⊎ w ≡ y ⊎ w ≡ z
  in3-true {x} {y} {z} {w} = go (w FinP.≟ x) (w FinP.≟ y) (w FinP.≟ z)
    where
    go : (d₁ : Dec (w ≡ x)) (d₂ : Dec (w ≡ y)) (d₃ : Dec (w ≡ z)) →
         does d₁ ∨ (does d₂ ∨ does d₃) ≡ true → w ≡ x ⊎ w ≡ y ⊎ w ≡ z
    go (yes e) _ _ _ = inj₁ e
    go (no _) (yes e) _ _ = inj₂ (inj₁ e)
    go (no _) (no _) (yes e) _ = inj₂ (inj₂ e)
    go (no _) (no _) (no _) ()

  in3-false : ∀ {x y z w} → in3 x y z w ≡ false → w ≢ x × w ≢ y × w ≢ z
  in3-false {x} {y} {z} {w} = go (w FinP.≟ x) (w FinP.≟ y) (w FinP.≟ z)
    where
    go : (d₁ : Dec (w ≡ x)) (d₂ : Dec (w ≡ y)) (d₃ : Dec (w ≡ z)) →
         does d₁ ∨ (does d₂ ∨ does d₃) ≡ false → w ≢ x × w ≢ y × w ≢ z
    go (yes _) _ _ ()
    go (no _) (yes _) _ ()
    go (no _) (no _) (yes _) ()
    go (no a) (no b) (no c) _ = a , b , c

------------------------------------------------------------------------
-- H on valid pairs

module V1 (M : Matrix n n D) .(o : ColOrth M) (eq : level M ≡ L) where

  open State M o eq

  private
    κ = rbit (W ! i₁)

    ri₂ : rbit (W ! i₂) ≡ κ
    ri₂ = ≡.sym (proj₂ (proj₂ valid₁₂))

    oi₂ : Odd (W ! i₂)
    oi₂ = proj₁ (proj₂ valid₁₂)

    i₁≢i₂ : i₁ ≢ i₂
    i₁≢i₂ = <⇒≢ i₁<i₂

    cls-κ : ∀ x → Odd (W ! x) → rbit (W ! x) ≡ κ → Cls κ x ≡ true
    cls-κ x ox rx = ≡.subst (λ b → Cls b x ≡ true) rx (cls-true x ox)

    -- The other members of i₁'s class come after i₂.
    after : ∀ y → Odd (W ! y) → rbit (W ! y) ≡ κ → y ≢ i₁ → y ≢ i₂ → i₂ < y
    after y oy ry y≢i₁ y≢i₂ = by (FinP.<-cmp y i₂)
      where
      i₁<y : i₁ < y
      i₁<y = FinP.≤∧≢⇒< (odd-≥ y oy) (λ e → y≢i₁ (≡.sym e))
      by : Tri (y < i₂) (y ≡ i₂) (i₂ < y) → i₂ < y
      by (tri< y<i₂ _ _) = ⊥-elim (between y i₁<y y<i₂ oy ry)
      by (tri≈ _ e _) = ⊥-elim (y≢i₂ e)
      by (tri> _ _ gt) = gt

    -- A fourth member of the class.
    fourth : ∀ y → Odd (W ! y) → rbit (W ! y) ≡ κ → y ≢ i₁ → y ≢ i₂ →
             ∃ λ y″ → Odd (W ! y″) × rbit (W ! y″) ≡ κ × y″ ≢ i₁ × y″ ≢ i₂ × y″ ≢ y
    fourth y oy ry y≢i₁ y≢i₂ = from (search (Cls κ) (in3 i₁ i₂ y))
      where
      from : (∃ λ y″ → Cls κ y″ ≡ true × in3 i₁ i₂ y y″ ≡ false) ⊎ (∀ y″ → Cls κ y″ ≡ true → in3 i₁ i₂ y y″ ≡ true) →
             ∃ λ y″ → Odd (W ! y″) × rbit (W ! y″) ≡ κ × y″ ≢ i₁ × y″ ≢ i₂ × y″ ≢ y
      from (inj₁ (y″ , c , f)) = y″ , proj₁ (cls-spec κ y″ c) , proj₂ (cls-spec κ y″ c) , in3-false f
      from (inj₂ all) = ⊥-elim (true≢false (≡.trans (≡.sym (≡.cong oddℕ three)) (cls-even κ)))
        where
        three : _ ≡ 3
        three = count-three (Cls κ) i₁ i₂ y i₁≢i₂ (sym≢ y≢i₁) (sym≢ y≢i₂)
                  (cls-κ i₁ oi₁ ≡.refl) (cls-κ i₂ oi₂ ri₂) (cls-κ y oy ry) (λ y″ c → in3-true (all y″ c))

  -- A valid pair sharing an index with the canonical one.
  shared : ∀ (x y : Fin n) .(xy : x < y) → x ≡ i₁ ⊎ x ≡ i₂ → Odd (W ! y) → rbit (W ! y) ≡ κ →
           y ≢ i₁ → y ≢ i₂ → Path [ H-gen x y xy ]ʷ M o
  shared x y xy xi oy ry y≢i₁ y≢i₂ = by (FinP.<-cmp y y″)
    where
    F = fourth y oy ry y≢i₁ y≢i₂
    y″ = proj₁ F
    oy″ = proj₁ (proj₂ F)
    ry″ = proj₁ (proj₂ (proj₂ F))
    y″≢i₁ = proj₁ (proj₂ (proj₂ (proj₂ F)))
    y″≢i₂ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ F))))
    y″≢y = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ F))))
    i₂<y = after y oy ry y≢i₁ y≢i₂
    i₂<y″ = after y″ oy″ ry″ y″≢i₁ y″≢i₂
    by : Tri (y < y″) (y ≡ y″) (y″ < y) → Path [ H-gen x y xy ]ʷ M o
    by (tri< y<y″ _ _) = pick xi
      where
      Dm = diamond M o eq i₁<i₂ i₂<y y<y″ fo nx oy oy″ ry ry″
      pick : x ≡ i₁ ⊎ x ≡ i₂ → Path [ H-gen x y xy ]ʷ M o
      pick (inj₁ e) = H-transport _ xy (≡.sym e) ≡.refl (proj₁ (proj₁ Dm))
      pick (inj₂ e) = H-transport _ xy (≡.sym e) ≡.refl (proj₂ (proj₂ Dm))
    by (tri≈ _ e _) = ⊥-elim (y″≢y (≡.sym e))
    by (tri> _ _ y″<y) = pick xi
      where
      Dm = diamond M o eq i₁<i₂ i₂<y″ y″<y fo nx oy″ oy ry″ ry
      pick : x ≡ i₁ ⊎ x ≡ i₂ → Path [ H-gen x y xy ]ʷ M o
      pick (inj₁ e) = H-transport _ xy (≡.sym e) ≡.refl (proj₁ (proj₂ Dm))
      pick (inj₂ e) = H-transport _ xy (≡.sym e) ≡.refl (proj₂ (proj₁ Dm))

  -- Every valid pair.
  validEdge : ∀ i j .(ij : i < j) → Valid W i j → Path [ H-gen i j ij ]ʷ M o
  validEdge i j ij vl@(oi , oj , rij) = by (i FinP.≟ i₁) (i FinP.≟ i₂) (j FinP.≟ i₁) (j FinP.≟ i₂)
    where
    ij′ : i < j
    ij′ = recompute (i FinP.<? j) ij
    i≢j : i ≢ j
    i≢j = <⇒≢ ij
    by : Dec (i ≡ i₁) → Dec (i ≡ i₂) → Dec (j ≡ i₁) → Dec (j ≡ i₂) → Path [ H-gen i j ij ]ʷ M o
    by (yes ≡.refl) _ _ (yes ≡.refl) = H-transport i₁<i₂ ij ≡.refl ≡.refl canonical
    by (yes ≡.refl) _ _ (no j≢i₂) =
      shared i j ij (inj₁ ≡.refl) oj (≡.sym rij) (sym≢ i≢j) j≢i₂
    by (no _) (yes ≡.refl) _ _ =
      shared i j ij (inj₂ ≡.refl) oj (≡.trans (≡.sym rij) ri₂)
        (λ e → FinP.<-irrefl (≡.sym e) (FinP.<-trans i₁<i₂ ij′)) (sym≢ i≢j)
    by (no i≢i₁) (no i≢i₂) (yes ≡.refl) _ =
      ⊥-elim (FinP.<-irrefl ≡.refl (ℕP.<-≤-trans ij′ (odd-≥ i oi)))
    by (no i≢i₁) (no i≢i₂) (no _) (yes ≡.refl) =
      ⊥-elim (between i (FinP.≤∧≢⇒< (odd-≥ i oi) (sym≢ i≢i₁)) ij′ oi (≡.trans rij ri₂))
    by (no i≢i₁) (no i≢i₂) (no j≢i₁) (no j≢i₂) =
      square i₁ i₂ i₁<i₂ i j ij valid₁₂ vl i≢i₁ i≢i₂ j≢i₁ j≢i₂ canonical

------------------------------------------------------------------------
-- X along valid pairs, and symmetric H

module V2 (M : Matrix n n D) .(o : ColOrth M) (eq : level M ≡ L) where

  open State M o eq
  open V1 M o eq using (validEdge)

  -- The state X_[i,j]·M, with i and j swapped.
  module SwapX {i j : Fin n} .(ij : i < j) (vl : Valid W i j) where

    j≤p : j ≤ p
    j≤p = odd≤ (proj₁ (proj₂ vl))

    XM = actM (X-gen i j ij) M

    eqX : level XM ≡ L
    eqX = mono-L (X-gen i j ij) tt j≤p M eq

    module SX = State XM (ColOrth-actMʷ (X i j ij) o) eqX

    WX : SX.W ≡ Xᶻ i j W
    WX = ≡.trans (≡.cong num (col-actM (X-gen i j ij) M p)) (proj₂ (lde-X i j ij (col M p)))

    vlX : Valid SX.W i j
    vlX = ≡.trans (≡.cong oddᶻ ei) oj , ≡.trans (≡.cong oddᶻ ej) oi ,
          ≡.trans (≡.cong rbit ei) (≡.trans (≡.sym (proj₂ (proj₂ vl))) (≡.cong rbit (≡.sym ej)))
      where
      oi = proj₁ vl
      oj = proj₁ (proj₂ vl)
      ei : SX.W ! i ≡ W ! j
      ei = ≡.trans (≡.cong (_! i) WX) (set₂-a i j (W ! j) (W ! i) W)
      ej : SX.W ! j ≡ W ! i
      ej = ≡.trans (≡.cong (_! j) WX) (set₂-b i j (W ! j) (W ! i) W (<⇒≢ ij))

  xEdge : ∀ i j .(ij : i < j) → Valid W i j → Path [ X-gen i j ij ]ʷ M o
  xEdge i j ij vl =
    bridge (X-gen i j ij) M o (H i j ij) (H i j ij) (Zʷ j) (validEdge i j ij vl)
      (V1.validEdge XM (ColOrth-actMʷ (X i j ij) o) eqX i j ij vlX) (lt , Z-low j≤p _ lt) (axiom (d2 ij))
    where
    open SwapX ij vl
    lt = below i j ij vl

  hsEdge : ∀ u v → u ≢ v → Valid W u v → Path (Hs u v) M o
  hsEdge u v u≢v vl@(ou , ov , ruv) = by (FinP.<-cmp u v)
    where
    by : Tri (u < v) (u ≡ v) (v < u) → Path (Hs u v) M o
    by (tri< lt _ _) = ≡.subst (λ w → Path w M o) (≡.sym (Hs-< lt)) (validEdge u v lt vl)
    by (tri≈ _ e _) = ⊥-elim (u≢v e)
    by (tri> _ _ gt) =
      ≡.subst (λ w → Path w M o) (≡.sym (Hs-> gt))
        (path-• (X v u gt) (H v u gt • X v u gt) M o p₁ (path-• (H v u gt) (X v u gt) M o p₂ p₃))
      where
      vl′ : Valid W v u
      vl′ = ov , ou , ≡.sym ruv
      open SwapX gt vl′
      p₃ : Path (X v u gt) M o
      p₃ = xEdge v u gt vl′
      p₂ : Path (H v u gt) XM (ColOrth-actMʷ (X v u gt) o)
      p₂ = V1.validEdge XM (ColOrth-actMʷ (X v u gt) o) eqX v u gt vlX
      lt = SX.below v u gt vlX
      p₁ : Path (X v u gt) (actM (H-gen v u gt) XM) (ColOrth-actMʷ (H v u gt • X v u gt) o)
      p₁ = ih (X-gen v u gt) (actM (H-gen v u gt) XM) (ColOrth-actMʷ (H v u gt • X v u gt) o) lt (X-low gt j≤p _ lt)

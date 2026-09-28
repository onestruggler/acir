------------------------------------------------------------------------
-- Presentations of groups
--
-- Wires, labels and the parity of the hidden shift circuit
--
-- The hidden shift circuits of figure 3 (Amy, QPL 2018, section 5.2)
-- apply three Hadamard layers to n = 2m data wires, so each layer's
-- path variables are the blocks of PathSum.HiddenShift.Blocks by wire:
-- wire i ↑ˡ m (the first half) carries a_i, c_i or e_i, wire m ↑ʳ i
-- (the second half) b_i, d_i or h_i (wl).  Along a path whose three
-- layers read y₁, y₂ and y₃, with the shift s, the circuit's phase on
-- |0⟩ is ½ times the parity
--
--   f(y₁ ⊕ s) + y₁·y₂ + f̃(y₂) + y₂·y₃,    f = mm g, f̃ = dual g
--
-- (hs-par; PathSum.HiddenShift.Simulation's hs-parity at x = 0), and
-- blocks-par regroups it as Blocks' Fblk of the blocks, the form the
-- reduction reads.  Also here: reading an assignment through a split
-- position (sel-ˡ, sel-ʳ, split-inv), for the layouts of the circuits'
-- path variables.  Nothing here mentions path-sums.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.HiddenShift.Layout where

open import Data.Bool.Base using (Bool; _xor_)
open import Data.Fin.Base using (Fin; splitAt; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using
  (splitAt-↑ˡ; splitAt-↑ʳ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)
open import Data.Nat.Base using (ℕ) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using ([_,_]′; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.HiddenShift.Blocks
open import PathSum.HiddenShift.Walsh using
  (_⊕ᵃ_; RespectsB; dot; dot-cong; dot-⧺; ⧺-split; lhalf; rhalf; mm;
   dual)


------------------------------------------------------------------------
-- Reading through a split position

sel-ˡ : ∀ a b {X : Set} (f : Fin a → X) (g : Fin b → X) (i : Fin a) →
        [ f , g ]′ (splitAt a (i ↑ˡ b)) ≡ f i
sel-ˡ a b f g i = cong [ f , g ]′ (splitAt-↑ˡ a i b)

sel-ʳ : ∀ a b {X : Set} (f : Fin a → X) (g : Fin b → X) (i : Fin b) →
        [ f , g ]′ (splitAt a (a ↑ʳ i)) ≡ g i
sel-ʳ a b f g i = cong [ f , g ]′ (splitAt-↑ʳ a b i)

-- A map out of a split position agrees with e if it does on either
-- side.

split-inv : ∀ a b {X Y : Set} (f : Fin a → X) (g : Fin b → X)
            (h : X → Y) (e : Fin (a ℕ+ b) → Y) →
            (∀ i → h (f i) ≡ e (i ↑ˡ b)) → (∀ i → h (g i) ≡ e (a ↑ʳ i)) →
            ∀ t → h ([ f , g ]′ (splitAt a t)) ≡ e t
split-inv a b f g h e hf hg t = go (splitAt a t) refl
  where
  go : ∀ r → splitAt a t ≡ r → h ([ f , g ]′ r) ≡ e t
  go (inj₁ i) eq = trans (hf i) (cong e (splitAt⁻¹-↑ˡ eq))
  go (inj₂ i) eq = trans (hg i) (cong e (splitAt⁻¹-↑ʳ eq))


------------------------------------------------------------------------
-- The label of a wire

-- On a layer with blocks b (first half) and b′ (second half).

wl : ∀ {m} → Blk → Blk → Fin (m ℕ+ m) → Lbl m
wl {m} b b′ w = [ (λ i → b , i) , (λ i → b′ , i) ]′ (splitAt m w)

wl-↑ˡ : ∀ {m} (b b′ : Blk) (i : Fin m) → wl b b′ (i ↑ˡ m) ≡ (b , i)
wl-↑ˡ {m} b b′ i = sel-ˡ m m _ _ i

wl-↑ʳ : ∀ {m} (b b′ : Blk) (i : Fin m) → wl b b′ (m ↑ʳ i) ≡ (b′ , i)
wl-↑ʳ {m} b b′ i = sel-ʳ m m _ _ i

-- A map of labels agrees with a map of wires on every wire if it does
-- on both halves.

wl-inv : ∀ {m} {Y : Set} (b b′ : Blk) (h : Lbl m → Y)
         (e : Fin (m ℕ+ m) → Y) →
         (∀ i → h (b , i) ≡ e (i ↑ˡ m)) → (∀ i → h (b′ , i) ≡ e (m ↑ʳ i)) →
         ∀ w → h (wl b b′ w) ≡ e w
wl-inv {m} b b′ h e hb hb′ = split-inv m m _ _ h e hb hb′


------------------------------------------------------------------------
-- The parity, block by block

-- The inner product splits over the two halves.

dot-halves : ∀ {m} (u v : Fin (m ℕ+ m) → Bool) →
             dot u v ≡ dot (lhalf {m} u) (lhalf {m} v) xor
                       dot (rhalf {m} u) (rhalf {m} v)
dot-halves {m} u v = trans
  (dot-cong (λ j → sym (⧺-split m m u j)) (λ j → sym (⧺-split m m v j)))
  (dot-⧺ (lhalf {m} u) (lhalf {m} v) (rhalf {m} u) (rhalf {m} v))

-- The circuit's parity on |0⟩ along a path whose layers read y₁, y₂,
-- y₃: f′ on the first, the two inner products, f̃ on the second.

hs-par : ∀ {m} (g : (Fin m → Bool) → Bool) (sv y₁ y₂ y₃ : Fin (m ℕ+ m) → Bool) →
         Bool
hs-par g sv y₁ y₂ y₃ =
  ((mm g (y₁ ⊕ᵃ sv) xor dot y₁ y₂) xor dual g y₂) xor dot y₂ y₃

-- It is Blocks' Fblk of the blocks the layers read.

blocks-par : ∀ {m} (g : (Fin m → Bool) → Bool) (g-resp : RespectsB g)
             (sv y₁ y₂ y₃ : Fin (m ℕ+ m) → Bool) (Z : LAssign m) →
             (∀ i → y₁ (i ↑ˡ m) ≡ Z (A₁ , i)) →
             (∀ i → y₁ (m ↑ʳ i) ≡ Z (B₁ , i)) →
             (∀ i → y₂ (i ↑ˡ m) ≡ Z (C₂ , i)) →
             (∀ i → y₂ (m ↑ʳ i) ≡ Z (D₂ , i)) →
             (∀ i → y₃ (i ↑ˡ m) ≡ Z (E₃ , i)) →
             (∀ i → y₃ (m ↑ʳ i) ≡ Z (H₃ , i)) →
             hs-par g sv y₁ y₂ y₃ ≡
             Phase.Fblk g g-resp (lhalf {m} sv) (rhalf {m} sv) Z
blocks-par {m} g g-resp sv y₁ y₂ y₃ Z hA hB hC hD hE hH =
  cong₂ _xor_ (cong₂ _xor_ (cong₂ _xor_ f-part d₁₂) f̃-part) d₂₃
  where
  f-part : mm g (y₁ ⊕ᵃ sv) ≡
           Phase.T₁ g g-resp (lhalf {m} sv) (rhalf {m} sv) Z xor
           Phase.T₂ g g-resp (lhalf {m} sv) (rhalf {m} sv) Z
  f-part = cong₂ _xor_
    (g-resp _ _ (λ i → cong (_xor sv (i ↑ˡ m)) (hA i)))
    (dot-cong (λ i → cong (_xor sv (i ↑ˡ m)) (hA i))
              (λ i → cong (_xor sv (m ↑ʳ i)) (hB i)))

  d₁₂ : dot y₁ y₂ ≡
        Phase.T₃ g g-resp (lhalf {m} sv) (rhalf {m} sv) Z xor
        Phase.T₄ g g-resp (lhalf {m} sv) (rhalf {m} sv) Z
  d₁₂ = trans (dot-halves {m} y₁ y₂)
              (cong₂ _xor_ (dot-cong hA hC) (dot-cong hB hD))

  f̃-part : dual g y₂ ≡
           Phase.T₅ g g-resp (lhalf {m} sv) (rhalf {m} sv) Z xor
           Phase.T₆ g g-resp (lhalf {m} sv) (rhalf {m} sv) Z
  f̃-part = cong₂ _xor_ (g-resp _ _ hD) (dot-cong hC hD)

  d₂₃ : dot y₂ y₃ ≡
        Phase.T₇ g g-resp (lhalf {m} sv) (rhalf {m} sv) Z xor
        Phase.T₈ g g-resp (lhalf {m} sv) (rhalf {m} sv) Z
  d₂₃ = trans (dot-halves {m} y₂ y₃)
              (cong₂ _xor_ (dot-cong hC hE) (dot-cong hD hH))

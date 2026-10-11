------------------------------------------------------------------------
-- Presentations of groups
--
-- A black and a white control of a rotation merge (Clément, Lemma
-- D.15, Equation (354)), on wire 3, at every width from five on
--
-- At width 5 + k, with rot α the rotation on wire 0 controlled by the
-- wires 1 … (RotCol) and X₃ X on wire 3:
--
--   (X₃ • rot α • X₃) • rot α ≈ place 3 (rot α)      (`eq354`, and `eq354′`
--                                                     in the other order)
--
-- — the rotation of one control fewer, wire 3 idle.  The rotations are
-- words in the H gate HG and the box K on wire 2 ((333)/(334),
-- Canon32.letters), and every letter passes every letter of the other
-- colour (Canon32.letter-comm), so the product shuffles into pairs of a
-- letter and its white copy (FourQubit.Merges.shuffle).  Each pair
-- merges into a placement around wire 3: the box by (309) on wire 3
-- (BoxMergeAt), the H gate by (309) between P ⊗ P ((310)), the gates
-- below wire 3 entering the placement by Place.place-low.  The placed
-- word is (333)/(334) one width down (Canon32 there, or on four wires by
-- evaluation, Base354).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.ZX354
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ ; zero ; suc ; s≤s ; z≤n)
open import Data.Nat.Properties using (n<1+n)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
import Examples.Groups.Symmetric.Syntactics as S

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex² ; X²)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
open import Examples.Groups.Real-Clifford+CH.TopWeakening using (top)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Figure13 complete₂ using (eq111)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Merges complete₂ complete₃ using (shuffle)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; negs²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm ; place ; place-• ; place-low ; place-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt ; placeAt-place ; placeAt-step ; X-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp ; below-suc)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes ; SymAt ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxMergeAt complete₂ complete₃ using (merge-at ; merge-at′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (col ; conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (Hg)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX353 complete₂ complete₃ using (allT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon32 complete₂ complete₃ using (letter ; letters ; letter-comm ; rot-rigid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base354 using (K₄ ; e-333 ; e-334)

------------------------------------------------------------------------
-- The letters one width down

-- At width 4 + k: the H gate (H on wire 0, box wire 1) and the box on
-- wire 2.
letter₁ : ∀ k → Bool → Circuit (₄₊ k)
letter₁ k true  = Hg (₁₊ k)
letter₁ k false = Ex ↑ • (Ex ↓ • Λ□ (₃₊ k) • Ex ↓) • Ex ↑

w4 : ∀ {n} → Circuit n → Circuit n → Circuit n
w4 x y = x • y • x • y

-- (333)/(334) at width 4 + k.
rot₁ : ∀ k → Below (₁₊ (₄₊ k)) → ∀ α → (₄₊ k) ⊢ w4 (letter₁ k α) (letter₁ k (not α)) ≈ rot {₁₊ k} α
rot₁ zero    below true  = SS.Below.by-sem₀ 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) c₄ (Hg 1 • K₄ • Hg 1 • K₄) (ΛZX 3) (Evaluated.same e-333)
  where c₄ = below (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
rot₁ zero    below false = SS.Below.by-sem₀ 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) c₄ (K₄ • Hg 1 • K₄ • Hg 1) (ΛXZ 3) (Evaluated.same e-334)
  where c₄ = below (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
rot₁ (suc k) below true  = sym (letters k (below-suc below) true)
  where open Tools ((₄₊ (suc k)) VRel,_===_)
rot₁ (suc k) below false = sym (letters k (below-suc below) false)
  where open Tools ((₄₊ (suc k)) VRel,_===_)

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    c : Comp (₄₊ k)
    c = below (n<1+n (₄₊ k))

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    symAt : SymAt (₁₊ k)
    symAt = eqSymAt (₁₊ k) completes

  open Tools (N VRel,_===_)

  private
    Λ X₃ : Circuit N
    Λ′ : Circuit (₄₊ k)
    Λ  = Λ□ (₄₊ k)
    Λ′ = Λ□ (₃₊ k)
    X₃ = X ↑ ↑ ↑

    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    -- The colouring white on wire 3 only.
    e₃ : Bits N
    e₃ = true ∷ true ∷ true ∷ false ∷ replicate (₁₊ k) true

    colX₃ : ∀ w → col e₃ w ≈ X₃ • w • X₃
    colX₃ w = trans (≡→≈ (Eq.cong (λ z → (((X • z ↑) ↑) ↑) ↑ • w • (((X • z ↑) ↑) ↑) ↑) (allT (₁₊ k))))
                    (cong right-unit (back _ right-unit))

    col-• : ∀ (s : Bits N) a b → col s (a • b) ≈ col s a • col s b
    col-• s a b = sym (begin
      (negsB s • a • negsB s) • (negsB s • b • negsB s)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
      negsB s • a • ((negsB s • negsB s) • b • negsB s)
        ≈⟨ back _ (back _ (trans (front _ (negs² s)) left-unit)) ⟩
      negsB s • a • (b • negsB s)
        ≈⟨ back _ (sym assoc) ⟩
      negsB s • (a • b) • negsB s ∎)

    col-w4 : ∀ (s : Bits N) a b → col s (w4 a b) ≈ w4 (col s a) (col s b)
    col-w4 s a b = trans (col-• s a _) (back _ (trans (col-• s b _) (back _ (col-• s a b))))

    -- X on wire 3 passes the gates below it.
    X₃-PP : X₃ • PP ↓ ≈ PP ↓ • X₃
    X₃-PP = sym (low-comm PP (X ↑))

    X₃-Ex : X₃ • Ex ↓ ≈ Ex ↓ • X₃
    X₃-Ex = sym (low-comm Ex (X ↑))

    X₃-Ex↑ : X₃ • Ex ↑ ≈ Ex ↑ • X₃
    X₃-Ex↑ = sym (lemma-cong↑ _ _ (low-comm Ex X))

    -- A local gate below wire 3 enters the placement.
    place-conj : ∀ (g : Circuit 3) (u : Circuit (₄₊ k)) →
                 (top g ↓ᵏ (₁₊ k)) • place 3 u • (top g ↓ᵏ (₁₊ k)) ≈ place 3 ((g ↓ᵏ (₁₊ k)) • u • (g ↓ᵏ (₁₊ k)))
    place-conj g u = sym (trans (place-• 3 (g ↓ᵏ (₁₊ k)) _)
                                (cong (place-low 3 g) (trans (place-• 3 u (g ↓ᵏ (₁₊ k))) (cong refl (place-low 3 g)))))

    -- A conjugation of a product.
    conj-• : ∀ {g a b : Circuit N} → g • g ≈ ε → (g • a • g) • (g • b • g) ≈ g • (a • b) • g
    conj-• {g} {a} {b} g² = begin
      (g • a • g) • (g • b • g)    ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
      g • a • ((g • g) • b • g)    ≈⟨ back _ (back _ (trans (front _ g²) left-unit)) ⟩
      g • a • (b • g)              ≈⟨ back _ (sym assoc) ⟩
      g • (a • b) • g ∎

    Ex↑² : Ex ↑ • Ex ↑ ≈ ε
    Ex↑² = lemma-cong↑ _ _ Ex²

    -- (309) on wire 3, both orders.
    m₃ : (X₃ • Λ • X₃) • Λ ≈ place 3 Λ′
    m₃ = trans (merge-at′ k c symAt 2 (s≤s (s≤s (s≤s z≤n)))) (≡→≈ (placeAt-place 3 Λ′))

    m₃′ : Λ • (X₃ • Λ • X₃) ≈ place 3 Λ′
    m₃′ = trans (merge-at k c symAt 2 (s≤s (s≤s (s≤s z≤n)))) (≡→≈ (placeAt-place 3 Λ′))

    -- The letters, as conjugates of the box.
    outer : Bool → Circuit N → Circuit N
    outer true  w = PP ↓ • (Ex ↓ • w • Ex ↓) • PP ↓
    outer false w = Ex ↑ • (Ex ↓ • w • Ex ↓) • Ex ↑

    outer₁ : Bool → Circuit (₄₊ k) → Circuit (₄₊ k)
    outer₁ true  w = PP ↓ • (Ex ↓ • w • Ex ↓) • PP ↓
    outer₁ false w = Ex ↑ • (Ex ↓ • w • Ex ↓) • Ex ↑

    outer-cong : ∀ a {u v : Circuit N} → u ≈ v → outer a u ≈ outer a v
    outer-cong true  e = mid _ _ (mid _ _ e)
    outer-cong false e = mid _ _ (mid _ _ e)

    outer-• : ∀ a (u v : Circuit N) → outer a u • outer a v ≈ outer a (u • v)
    outer-• true  u v = trans (conj-• eq111) (mid _ _ (conj-• Ex²))
    outer-• false u v = trans (conj-• Ex↑²) (mid _ _ (conj-• Ex²))

    -- The colouring moved inside.
    white : ∀ a → X₃ • outer a Λ • X₃ ≈ outer a (X₃ • Λ • X₃)
    white true  = trans (conj-swap X₃-PP _) (mid _ _ (conj-swap X₃-Ex Λ))
    white false = trans (conj-swap X₃-Ex↑ _) (mid _ _ (conj-swap X₃-Ex Λ))

    -- The gates below wire 3 enter the placement.
    outer-place : ∀ a (u : Circuit (₄₊ k)) → outer a (place 3 u) ≈ place 3 (outer₁ a u)
    outer-place true  u = trans (mid _ _ (place-conj (Ex {1}) u)) (place-conj (PP {1}) _)
    outer-place false u = trans (mid _ _ (place-conj (Ex {1}) u)) (place-conj (Ex {0} ↑) _)

    -- A letter and its white copy merge, in either order.
    merge-letter : ∀ a → (X₃ • letter k below a • X₃) • letter k below a ≈ place 3 (letter₁ k a)
    merge-letter true  = trans (front _ (white true)) (trans (outer-• true _ _)
                           (trans (outer-cong true m₃) (outer-place true Λ′)))
    merge-letter false = trans (front _ (white false)) (trans (outer-• false _ _)
                           (trans (outer-cong false m₃) (outer-place false Λ′)))

    merge-letter′ : ∀ a → letter k below a • (X₃ • letter k below a • X₃) ≈ place 3 (letter₁ k a)
    merge-letter′ true  = trans (back _ (white true)) (trans (outer-• true _ _)
                            (trans (outer-cong true m₃′) (outer-place true Λ′)))
    merge-letter′ false = trans (back _ (white false)) (trans (outer-• false _ _)
                            (trans (outer-cong false m₃′) (outer-place false Λ′)))

    place-w4 : ∀ (u v : Circuit (₄₊ k)) → place 3 (w4 u v) ≈ w4 (place 3 u) (place 3 v)
    place-w4 u v = trans (place-• 3 u _) (back _ (trans (place-• 3 v _) (back _ (place-• 3 u v))))

    ones₁ : Bits (₁₊ k)
    ones₁ = replicate (₁₊ k) true

    -- Every letter passes every white letter.
    lc : ∀ x y → letter k below x • col e₃ (letter k below y) ≈ col e₃ (letter k below y) • letter k below x
    lc x y = letter-comm k below x y true true ones₁

  ----------------------------------------------------------------------
  -- (354) on wire 3

  eq354 : ∀ α → (X₃ • rot α • X₃) • rot α ≈ place 3 (rot {₁₊ k} α)
  eq354 α = begin
    (X₃ • rot α • X₃) • rot α
      ≈⟨ front _ (sym (colX₃ (rot α))) ⟩
    col e₃ (rot α) • rot α
      ≈⟨ cong (trans (mid _ _ (letters k below α)) (col-w4 e₃ a b)) (letters k below α) ⟩
    w4 (col e₃ a) (col e₃ b) • w4 a b
      ≈⟨ sym (shuffle (N VRel,_===_) (lc α α) (lc α (not α)) (lc (not α) α) (lc (not α) (not α))) ⟩
    (col e₃ a • a) • (col e₃ b • b) • (col e₃ a • a) • (col e₃ b • b)
      ≈⟨ cong ma (cong mb (cong ma mb)) ⟩
    w4 (place 3 (letter₁ k α)) (place 3 (letter₁ k (not α)))
      ≈⟨ sym (place-w4 _ _) ⟩
    place 3 (w4 (letter₁ k α) (letter₁ k (not α)))
      ≈⟨ place-cong 3 (rot₁ k below α) ⟩
    place 3 (rot α) ∎
    where
    a b : Circuit N
    a = letter k below α
    b = letter k below (not α)
    ma : col e₃ a • a ≈ place 3 (letter₁ k α)
    ma = trans (front _ (colX₃ a)) (merge-letter α)
    mb : col e₃ b • b ≈ place 3 (letter₁ k (not α))
    mb = trans (front _ (colX₃ b)) (merge-letter (not α))

  eq354′ : ∀ α → rot α • (X₃ • rot α • X₃) ≈ place 3 (rot {₁₊ k} α)
  eq354′ α = begin
    rot α • (X₃ • rot α • X₃)
      ≈⟨ back _ (sym (colX₃ (rot α))) ⟩
    rot α • col e₃ (rot α)
      ≈⟨ cong (letters k below α) (trans (mid _ _ (letters k below α)) (col-w4 e₃ a b)) ⟩
    w4 a b • w4 (col e₃ a) (col e₃ b)
      ≈⟨ sym (shuffle (N VRel,_===_) (sym (lc α α)) (sym (lc (not α) α)) (sym (lc α (not α))) (sym (lc (not α) (not α)))) ⟩
    (a • col e₃ a) • (b • col e₃ b) • (a • col e₃ a) • (b • col e₃ b)
      ≈⟨ cong ma (cong mb (cong ma mb)) ⟩
    w4 (place 3 (letter₁ k α)) (place 3 (letter₁ k (not α)))
      ≈⟨ sym (place-w4 _ _) ⟩
    place 3 (w4 (letter₁ k α) (letter₁ k (not α)))
      ≈⟨ place-cong 3 (rot₁ k below α) ⟩
    place 3 (rot α) ∎
    where
    a b : Circuit N
    a = letter k below α
    b = letter k below (not α)
    ma : a • col e₃ a ≈ place 3 (letter₁ k α)
    ma = trans (back _ (colX₃ a)) (merge-letter′ α)
    mb : b • col e₃ b ≈ place 3 (letter₁ k (not α))
    mb = trans (back _ (colX₃ b)) (merge-letter′ (not α))

  ----------------------------------------------------------------------
  -- (354) on wire 1: the statement on wire 3 conjugated by the swaps of
  -- the wires 2 3 and 1 2, which the rotations pass (Canon32.rot-rigid)
  -- and which carry X and the idle wire of a placement from wire 3 to
  -- wire 1 (PlaceAt.X-step, placeAt-step)

  private
    s₁ s₂ : Circuit N
    s₁ = Ex ↑
    s₂ = Ex ↑ ↑

    s₁² : s₁ • s₁ ≈ ε
    s₁² = Ex↑²

    s₂² : s₂ • s₂ ≈ ε
    s₂² = lemma-cong↑ _ _ (lemma-cong↑ _ _ Ex²)

    module C₁ = Conj {N} s₁ s₁²
    module C₂ = Conj {N} s₂ s₂²

    X₁ : Circuit N
    X₁ = X ↑

    -- X from wire 3 to wire 1.
    σX : C₁.⟪ C₂.⟪ X₃ ⟫ ⟫ ≈ X₁
    σX = trans (C₁.⟪⟫-cong (conj-sym s₂² (X-step 2 (s≤s (s≤s (s≤s z≤n))))))
               (conj-sym s₁² (X-step 1 (s≤s (s≤s z≤n))))

    -- The rotations do not see the swaps of their controls.
    σR : ∀ α → C₁.⟪ C₂.⟪ rot {₂₊ k} α ⟫ ⟫ ≈ rot α
    σR α = trans (C₁.⟪⟫-cong (C₂.⟪⟫-fix (rot-rigid k below α [ S.gate₂ S.σ-gate S.↥ ]ʷ)))
                 (C₁.⟪⟫-fix (rot-rigid k below α [ S.gate₂ S.σ-gate ]ʷ))

    -- The idle wire of a placement from wire 3 to wire 1.
    σP : ∀ (u : Circuit (₄₊ k)) → C₁.⟪ C₂.⟪ place 3 u ⟫ ⟫ ≈ place 1 u
    σP u = trans (C₁.⟪⟫-cong (C₂.⟪⟫-cong (≡→≈ (Eq.sym (placeAt-place 3 u)))))
             (trans (C₁.⟪⟫-cong (conj-sym s₂² (sym (placeAt-step 2 u (s≤s (s≤s (s≤s z≤n)))))))
               (trans (conj-sym s₁² (sym (placeAt-step 1 u (s≤s (s≤s z≤n)))))
                      (≡→≈ (placeAt-place 1 u))))

    σ-• : ∀ a b → C₁.⟪ C₂.⟪ a • b ⟫ ⟫ ≈ C₁.⟪ C₂.⟪ a ⟫ ⟫ • C₁.⟪ C₂.⟪ b ⟫ ⟫
    σ-• a b = trans (C₁.⟪⟫-cong (C₂.⟪⟫-• a b)) (C₁.⟪⟫-• _ _)

  eq354₁ : ∀ α → (X₁ • rot α • X₁) • rot α ≈ place 1 (rot {₁₊ k} α)
  eq354₁ α = begin
    (X₁ • rot α • X₁) • rot α
      ≈⟨ sym (cong (trans (σ-• X₃ _) (cong σX (trans (σ-• _ X₃) (cong (σR α) σX)))) (σR α)) ⟩
    C₁.⟪ C₂.⟪ X₃ • rot α • X₃ ⟫ ⟫ • C₁.⟪ C₂.⟪ rot α ⟫ ⟫
      ≈⟨ sym (σ-• _ _) ⟩
    C₁.⟪ C₂.⟪ (X₃ • rot α • X₃) • rot α ⟫ ⟫
      ≈⟨ C₁.⟪⟫-cong (C₂.⟪⟫-cong (eq354 α)) ⟩
    C₁.⟪ C₂.⟪ place 3 (rot α) ⟫ ⟫
      ≈⟨ σP _ ⟩
    place 1 (rot α) ∎

  eq354₁′ : ∀ α → rot α • (X₁ • rot α • X₁) ≈ place 1 (rot {₁₊ k} α)
  eq354₁′ α = begin
    rot α • (X₁ • rot α • X₁)
      ≈⟨ sym (cong (σR α) (trans (σ-• X₃ _) (cong σX (trans (σ-• _ X₃) (cong (σR α) σX))))) ⟩
    C₁.⟪ C₂.⟪ rot α ⟫ ⟫ • C₁.⟪ C₂.⟪ X₃ • rot α • X₃ ⟫ ⟫
      ≈⟨ sym (σ-• _ _) ⟩
    C₁.⟪ C₂.⟪ rot α • (X₃ • rot α • X₃) ⟫ ⟫
      ≈⟨ C₁.⟪⟫-cong (C₂.⟪⟫-cong (eq354′ α)) ⟩
    C₁.⟪ C₂.⟪ place 3 (rot α) ⟫ ⟫
      ≈⟨ σP _ ⟩
    place 1 (rot α) ∎

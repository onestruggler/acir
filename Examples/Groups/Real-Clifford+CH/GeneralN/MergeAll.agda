------------------------------------------------------------------------
-- Presentations of groups
--
-- Merging a box over every colouring of some of its controls
--
-- Lemma 8.6's base cases (Appendix E.4) decode a gate as a product,
-- over every context, of boxes that differ only in the colours of the
-- context wires, and merge them all with (309).  Here that at the
-- canonical position: the product, in `allBits` order, of the box with
-- every colouring of its controls on the wires ps = p₁ > p₂ > … > pⱼ ≥ 1,
-- the other colours given by `base`, is the box on the other wires with
-- idle wires inserted at ps — for one control left (`merge-all₁`, `GapD₁`,
-- the case of Z and H) and for two (`merge-all₂`, the case of CZ and CH).
-- Colours are bitstrings read by `negsB`, the varying bits inserted into
-- `base` at ps (`VD₁`, `VD₂`).  The two are written out separately, the
-- count of controls being 1 + j resp. 2 + j: with k + j or j + k for a
-- variable k, either the induction step or the instance at 3 + m wires
-- would need a transport of widths.
--
-- No reordering is needed.  `allBits (1 + j)` pairs every colouring of
-- j bits with its two extensions by a last bit (`pairing`); the last
-- bit is inserted at the highest wire p₁ (the bits are read backwards),
-- so each pair merges on p₁ at once ((309) in the order white first, a
-- module parameter), and what is left is the same product one width
-- down, placed around the idle wire p₁: inserting an idle wire is
-- inserting a black bit (`placeAt-negsB`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _≤_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
open import Word.Base using (_•_)

module Examples.Groups.Real-Clifford+CH.GeneralN.MergeAll
  (B : ℕ)
  (mergeAt′ : ∀ K → 1 ≤ K → K ≤ B → ∀ c → 1 ≤ c → c ≤ suc K →
              (₂₊ K) ⊢ (Xat c • Λ□ (suc K) • Xat c) • Λ□ (suc K) ≈ placeAt c (Λ□ K))
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat using (_<_ ; pred ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-trans ; ≤-refl ; n≤1+n ; m≤n+m)
open import Data.Vec using (Vec ; [] ; _∷_ ; _∷ʳ_ ; reverse)
open import Data.Vec.Properties using (reverse-∷ ; reverse-involutive)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; X²)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; insertℕ)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceCalc
  using (placeAt-• ; placeAt-ε ; placeAt-cong ; placeAt-X-lo ; placeAt-zero ; placeAt-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; negs²)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Products over lists

module _ {n : ℕ} {A : Set} where
  open Tools (n VRel,_===_)

  ∏-++ : ∀ (xs ys : List A) (g : A → Circuit n) → ∏ (xs ++ ys) g ≈ ∏ xs g • ∏ ys g
  ∏-++ []       ys g = sym left-unit
  ∏-++ (x ∷ xs) ys g = trans (back _ (∏-++ xs ys g)) (sym assoc)

  ∏-cong : ∀ (xs : List A) {g g′ : A → Circuit n} → (∀ a → g a ≈ g′ a) → ∏ xs g ≈ ∏ xs g′
  ∏-cong []       e = refl
  ∏-cong (x ∷ xs) e = cong (e x) (∏-cong xs e)

∏-map : ∀ {A C Y : Set} (h : C → A) (xs : List C) (g : A → Word Y) → ∏ (map h xs) g ≡ ∏ xs (λ c → g (h c))
∏-map h []       g = Eq.refl
∏-map h (x ∷ xs) g = Eq.cong (g (h x) •_) (∏-map h xs g)

-- placeAt through a product.
placeAt-∏ : ∀ {A : Set} c (xs : List A) (g : A → Circuit n) →
            (₁₊ n) ⊢ placeAt c (∏ xs g) ≈ ∏ xs (λ a → placeAt c (g a))
placeAt-∏ {n} c []       g = placeAt-ε c
placeAt-∏ {n} c (x ∷ xs) g = trans (placeAt-• c (g x) (∏ xs g)) (back _ (placeAt-∏ c xs g))
  where open Tools ((₁₊ n) VRel,_===_)

-- Every colouring of 1 + j bits is a colouring of j bits and a last one.
pairing : ∀ j (g : Bits (suc j) → Circuit n) →
          n ⊢ ∏ (allBits (suc j)) g ≈ ∏ (allBits j) (λ c → g (c ∷ʳ false) • g (c ∷ʳ true))
pairing {n} zero    g = sym assoc
  where open Tools (n VRel,_===_)
pairing {n} (suc j) g = begin
  ∏ (map (false ∷_) A₁ ++ map (true ∷_) A₁) g
    ≈⟨ ∏-++ (map (false ∷_) A₁) (map (true ∷_) A₁) g ⟩
  ∏ (map (false ∷_) A₁) g • ∏ (map (true ∷_) A₁) g
    ≈⟨ refl′ (Eq.cong₂ _•_ (∏-map (false ∷_) A₁ g) (∏-map (true ∷_) A₁ g)) ⟩
  ∏ A₁ (λ c → g (false ∷ c)) • ∏ A₁ (λ c → g (true ∷ c))
    ≈⟨ cong (pairing j (λ c → g (false ∷ c))) (pairing j (λ c → g (true ∷ c))) ⟩
  ∏ A₀ (λ c → G (false ∷ c)) • ∏ A₀ (λ c → G (true ∷ c))
    ≈⟨ refl′ (Eq.sym (Eq.cong₂ _•_ (∏-map (false ∷_) A₀ G) (∏-map (true ∷_) A₀ G))) ⟩
  ∏ (map (false ∷_) A₀) G • ∏ (map (true ∷_) A₀) G
    ≈⟨ sym (∏-++ (map (false ∷_) A₀) (map (true ∷_) A₀) G) ⟩
  ∏ (map (false ∷_) A₀ ++ map (true ∷_) A₀) G ∎
  where
  open Tools (n VRel,_===_)
  A₀ : List (Bits j)
  A₀ = allBits j
  A₁ : List (Bits (suc j))
  A₁ = allBits (suc j)
  G : Bits (suc j) → Circuit n
  G c = g (c ∷ʳ false) • g (c ∷ʳ true)
  refl′ : ∀ {a b : Circuit n} → a ≡ b → a ≈ b
  refl′ Eq.refl = refl

------------------------------------------------------------------------
-- Colours as a bitstring

private
  Xat-comm : ∀ i i′ → n ⊢ Xat i • Xat i′ ≈ Xat i′ • Xat i
  Xat-comm {zero}  i       i′       = PB-refl
    where open Tools (zero VRel,_===_) renaming (refl to PB-refl)
  Xat-comm {suc n} zero    zero     = PB-refl
    where open Tools ((suc n) VRel,_===_) renaming (refl to PB-refl)
  Xat-comm {suc n} zero    (suc i′) = X-↑ (Xat i′)
  Xat-comm {suc n} (suc i) zero     = PB-sym (X-↑ (Xat i))
    where open Tools ((suc n) VRel,_===_) renaming (sym to PB-sym)
  Xat-comm {suc n} (suc i) (suc i′) = lemma-cong↑ (Xat i • Xat i′) (Xat i′ • Xat i) (Xat-comm i i′)

  -- X on any wire passes the colours.
  X-negsB : ∀ p (W : Bits n) → n ⊢ Xat p • negsB W ≈ negsB W • Xat p
  X-negsB↑ : ∀ p (W : Bits n) → (₁₊ n) ⊢ Xat p • negsB W ↑ ≈ negsB W ↑ • Xat p

  X-negsB {n} p []          = trans right-unit (sym left-unit)
    where open Tools (n VRel,_===_)
  X-negsB {suc n} p (true ∷ W)  = X-negsB↑ p W
  X-negsB {suc n} p (false ∷ W) = begin
    Xat p • (X • negsB W ↑)     ≈⟨ sym assoc ⟩
    (Xat p • X) • negsB W ↑     ≈⟨ front _ (Xat-comm p 0) ⟩
    (X • Xat p) • negsB W ↑     ≈⟨ trans assoc (back _ (X-negsB↑ p W)) ⟩
    X • (negsB W ↑ • Xat p)     ≈⟨ sym assoc ⟩
    (X • negsB W ↑) • Xat p ∎
    where open Tools ((₁₊ n) VRel,_===_)

  X-negsB↑ zero    W = X-↑ (negsB W)
  X-negsB↑ (suc p) W = lemma-cong↑ (Xat p • negsB W) (negsB W • Xat p) (X-negsB p W)

  -- A white control at p is X there on top of a black one.
  negsB-white : ∀ p (W : Bits n) → p ≤ n →
                (₁₊ n) ⊢ negsB (insertℕ p false W) ≈ Xat p • negsB (insertℕ p true W)
  negsB-white {n} zero    W       _       = refl
    where open Tools ((₁₊ n) VRel,_===_)
  negsB-white {suc n} (suc p) (true ∷ W)  (s≤s p≤) =
    lemma-cong↑ (negsB (insertℕ p false W)) (Xat p • negsB (insertℕ p true W)) (negsB-white p W p≤)
  negsB-white {suc n} (suc p) (false ∷ W) (s≤s p≤) = begin
    X • negsB (insertℕ p false W) ↑           ≈⟨ back _ (lemma-cong↑ _ _ (negsB-white p W p≤)) ⟩
    X • Xat p ↑ • negsB (insertℕ p true W) ↑  ≈⟨ trans (sym assoc) (trans (front _ (X-↑ (Xat p))) assoc) ⟩
    Xat p ↑ • X • negsB (insertℕ p true W) ↑ ∎
    where open Tools ((₂₊ n) VRel,_===_)

  -- An idle wire inserted at p is a black bit inserted there.
  placeAt-negsB : ∀ p (W : Bits n) → p ≤ n → (₁₊ n) ⊢ placeAt p (negsB W) ≈ negsB (insertℕ p true W)
  placeAt-negsB {n} zero    W _ = placeAt-zero (negsB W)
  placeAt-negsB {suc n} (suc p) (true ∷ W) (s≤s p≤) =
    trans (placeAt-↑ p (negsB W)) (lemma-cong↑ _ _ (placeAt-negsB p W p≤))
    where open Tools ((₂₊ n) VRel,_===_)
  placeAt-negsB {suc n} (suc p) (false ∷ W) (s≤s p≤) = begin
    placeAt (suc p) (X • negsB W ↑)                     ≈⟨ placeAt-• (suc p) X (negsB W ↑) ⟩
    placeAt (suc p) X • placeAt (suc p) (negsB W ↑)     ≈⟨ cong (placeAt-X-lo (suc p) 0 (s≤s z≤n) (s≤s p≤)) (placeAt-↑ p (negsB W)) ⟩
    X • placeAt p (negsB W) ↑                           ≈⟨ back _ (lemma-cong↑ _ _ (placeAt-negsB p W p≤)) ⟩
    X • negsB (insertℕ p true W) ↑ ∎
    where open Tools ((₂₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Merging

-- Positions: strictly decreasing, between 1 and K.
data Pos : ∀ {j} → ℕ → Vec ℕ j → Set where
  []  : ∀ {K} → Pos K []
  pos : ∀ {K j p} {ps : Vec ℕ j} → 1 ≤ p → p ≤ K → Pos (pred p) ps → Pos K (p ∷ ps)

private
  Pos-≤ : ∀ {j K K′} {ps : Vec ℕ j} → K ≤ K′ → Pos K ps → Pos K′ ps
  Pos-≤ K≤ []              = []
  Pos-≤ K≤ (pos 1≤p p≤K q) = pos 1≤p (≤-trans p≤K K≤) q

  pred-≤ : ∀ {p K} → p ≤ suc K → pred p ≤ K
  pred-≤ z≤n     = z≤n
  pred-≤ (s≤s x) = x

  rev-snoc : ∀ {j} (c : Bits j) b → reverse (c ∷ʳ b) ≡ b ∷ reverse c
  rev-snoc c b =
    Eq.trans (Eq.cong reverse (Eq.sym (Eq.trans (reverse-∷ b (reverse c)) (Eq.cong (_∷ʳ b) (reverse-involutive c)))))
             (reverse-involutive (b ∷ reverse c))

-- One pair: the box Λ□ (1 + K) with a white and a black control at p,
-- the other colours W, merges to Λ□ K placed around the idle wire p.
pair-merge : ∀ K → 1 ≤ K → K ≤ B → ∀ p → 1 ≤ p → p ≤ suc K → (W : Bits (₁₊ K)) →
             (₂₊ K) ⊢ (negsB (insertℕ p false W) • Λ□ (suc K) • negsB (insertℕ p false W)) •
                      (negsB (insertℕ p true W) • Λ□ (suc K) • negsB (insertℕ p true W))
                      ≈ placeAt p (negsB W • Λ□ K • negsB W)
pair-merge K 1≤K K≤B p 1≤p p≤ W = begin
  (Nf • Λ • Nf) • (N • Λ • N)
    ≈⟨ front _ (cong (trans (negsB-white p W p≤) (X-negsB p (insertℕ p true W)))
                     (back _ (negsB-white p W p≤))) ⟩
  ((N • Xat p) • Λ • (Xat p • N)) • (N • Λ • N)
    ≈⟨ by-passoc (((□ • □) • □ • (□ • □)) • (□ • □ • □)) (□ • (□ • □ • □) • (□ • □) • □ • □) Eq.refl ⟩
  N • (Xat p • Λ • Xat p) • (N • N) • Λ • N
    ≈⟨ back _ (back _ (trans (front _ (negs² (insertℕ p true W))) left-unit)) ⟩
  N • (Xat p • Λ • Xat p) • Λ • N
    ≈⟨ back _ (trans (sym assoc) (front _ (mergeAt′ K 1≤K K≤B p 1≤p p≤))) ⟩
  N • placeAt p (Λ□ K) • N
    ≈⟨ cong N≈ (back _ N≈) ⟩
  placeAt p M • placeAt p (Λ□ K) • placeAt p M
    ≈⟨ sym (trans (placeAt-• p M (Λ□ K • M)) (back _ (placeAt-• p (Λ□ K) M))) ⟩
  placeAt p (M • Λ□ K • M) ∎
  where
  open Tools ((₂₊ K) VRel,_===_)
  Λ N Nf : Circuit (₂₊ K)
  Λ  = Λ□ (suc K)
  N  = negsB (insertℕ p true W)
  Nf = negsB (insertℕ p false W)
  M : Circuit (₁₊ K)
  M = negsB W
  N≈ : N ≈ placeAt p M
  N≈ = sym (placeAt-negsB p W p≤)

------------------------------------------------------------------------
-- With one control not merged

-- A box on two wires with idle wires inserted at ps, the highest last.
GapD₁ : ∀ {j} → Vec ℕ j → Circuit 2 → Circuit (₂₊ j)
GapD₁ []       u = u
GapD₁ (p ∷ ps) u = placeAt p (GapD₁ ps u)

-- The colours: the bits rc inserted at the positions ps into base.
VD₁ : ∀ {j} → Vec ℕ j → Bits j → Bits 2 → Bits (₂₊ j)
VD₁ []       []       base = base
VD₁ (p ∷ ps) (b ∷ rc) base = insertℕ p b (VD₁ ps rc base)

merge-all₁ : ∀ {j} (ps : Vec ℕ j) → Pos (suc j) ps → j ≤ B → (base : Bits 2) →
             (₂₊ j) ⊢ ∏ (allBits j) (λ c → negsB (VD₁ ps (reverse c) base) • Λ□ (suc j) •
                                           negsB (VD₁ ps (reverse c) base))
                      ≈ GapD₁ ps (negsB base • Λ□ 1 • negsB base)
merge-all₁ [] _ _ base = right-unit
  where open Tools (2 VRel,_===_)
merge-all₁ {suc j} (p ∷ ps) (pos 1≤p p≤ Q) b base = begin
  ∏ (allBits (suc j)) G
    ≈⟨ pairing j G ⟩
  ∏ (allBits j) (λ c → G (c ∷ʳ false) • G (c ∷ʳ true))
    ≈⟨ ∏-cong (allBits j) pair ⟩
  ∏ (allBits j) (λ c → placeAt p (h c))
    ≈⟨ sym (placeAt-∏ p (allBits j) h) ⟩
  placeAt p (∏ (allBits j) h)
    ≈⟨ placeAt-cong p (merge-all₁ ps (Pos-≤ (pred-≤ p≤) Q) (≤-trans (n≤1+n j) b) base) ⟩
  placeAt p (GapD₁ ps (negsB base • Λ□ 1 • negsB base)) ∎
  where
  open Tools ((₃₊ j) VRel,_===_)
  G : Bits (suc j) → Circuit (₃₊ j)
  G c = negsB (VD₁ (p ∷ ps) (reverse c) base) • Λ□ (₂₊ j) • negsB (VD₁ (p ∷ ps) (reverse c) base)
  h : Bits j → Circuit (₂₊ j)
  h c = negsB (VD₁ ps (reverse c) base) • Λ□ (suc j) • negsB (VD₁ ps (reverse c) base)
  ≡→≈ : ∀ {x y : Circuit (₃₊ j)} → x ≡ y → x ≈ y
  ≡→≈ Eq.refl = refl
  pair : ∀ c → G (c ∷ʳ false) • G (c ∷ʳ true) ≈ placeAt p (h c)
  pair c = trans (≡→≈ (Eq.cong₂ (λ x y → (negsB (VD₁ (p ∷ ps) x base) • Λ□ (₂₊ j) • negsB (VD₁ (p ∷ ps) x base)) •
                                        (negsB (VD₁ (p ∷ ps) y base) • Λ□ (₂₊ j) • negsB (VD₁ (p ∷ ps) y base)))
                               (rev-snoc c false) (rev-snoc c true)))
                 (pair-merge (suc j) (s≤s z≤n) b p 1≤p p≤ (VD₁ ps (reverse c) base))

------------------------------------------------------------------------
-- With two controls not merged

GapD₂ : ∀ {j} → Vec ℕ j → Circuit 3 → Circuit (₃₊ j)
GapD₂ []       u = u
GapD₂ (p ∷ ps) u = placeAt p (GapD₂ ps u)

VD₂ : ∀ {j} → Vec ℕ j → Bits j → Bits 3 → Bits (₃₊ j)
VD₂ []       []       base = base
VD₂ (p ∷ ps) (b ∷ rc) base = insertℕ p b (VD₂ ps rc base)

merge-all₂ : ∀ {j} (ps : Vec ℕ j) → Pos (₂₊ j) ps → suc j ≤ B → (base : Bits 3) →
             (₃₊ j) ⊢ ∏ (allBits j) (λ c → negsB (VD₂ ps (reverse c) base) • Λ□ (₂₊ j) •
                                           negsB (VD₂ ps (reverse c) base))
                      ≈ GapD₂ ps (negsB base • Λ□ 2 • negsB base)
merge-all₂ [] _ _ base = right-unit
  where open Tools (3 VRel,_===_)
merge-all₂ {suc j} (p ∷ ps) (pos 1≤p p≤ Q) b base = begin
  ∏ (allBits (suc j)) G
    ≈⟨ pairing j G ⟩
  ∏ (allBits j) (λ c → G (c ∷ʳ false) • G (c ∷ʳ true))
    ≈⟨ ∏-cong (allBits j) pair ⟩
  ∏ (allBits j) (λ c → placeAt p (h c))
    ≈⟨ sym (placeAt-∏ p (allBits j) h) ⟩
  placeAt p (∏ (allBits j) h)
    ≈⟨ placeAt-cong p (merge-all₂ ps (Pos-≤ (pred-≤ p≤) Q) (≤-trans (n≤1+n (suc j)) b) base) ⟩
  placeAt p (GapD₂ ps (negsB base • Λ□ 2 • negsB base)) ∎
  where
  open Tools ((₄₊ j) VRel,_===_)
  G : Bits (suc j) → Circuit (₄₊ j)
  G c = negsB (VD₂ (p ∷ ps) (reverse c) base) • Λ□ (₃₊ j) • negsB (VD₂ (p ∷ ps) (reverse c) base)
  h : Bits j → Circuit (₃₊ j)
  h c = negsB (VD₂ ps (reverse c) base) • Λ□ (₂₊ j) • negsB (VD₂ ps (reverse c) base)
  ≡→≈ : ∀ {x y : Circuit (₄₊ j)} → x ≡ y → x ≈ y
  ≡→≈ Eq.refl = refl
  pair : ∀ c → G (c ∷ʳ false) • G (c ∷ʳ true) ≈ placeAt p (h c)
  pair c = trans (≡→≈ (Eq.cong₂ (λ x y → (negsB (VD₂ (p ∷ ps) x base) • Λ□ (₃₊ j) • negsB (VD₂ (p ∷ ps) x base)) •
                                        (negsB (VD₂ (p ∷ ps) y base) • Λ□ (₃₊ j) • negsB (VD₂ (p ∷ ps) y base)))
                               (rev-snoc c false) (rev-snoc c true)))
                 (pair-merge (₂₊ j) (s≤s z≤n) b p 1≤p p≤ (VD₂ ps (reverse c) base))

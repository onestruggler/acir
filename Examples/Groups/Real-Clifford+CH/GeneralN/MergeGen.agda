------------------------------------------------------------------------
-- Presentations of groups
--
-- Merging any gate over every colouring of its controls
--
-- MergeAll's argument with the box abstracted.  For any gate g and any
-- merge of a white and a black control of it on wire p,
-- (Xat p • g • Xat p) • g ≈ placeAt p u, the same two gates with the
-- other controls coloured by W merge to u coloured by W, placed around
-- p (`pair-merge`).  For a family F K of gates on 1 + K wires — wire 0
-- the target, the wires 1 … K controls — with that merge on the top
-- wire at every width below a bound, the product in `allBits` order of
-- F j over every colouring of its controls is F 0 on wire 0
-- (`MergeTop.merge-top₀`): `allBits (1 + j)` pairs every colouring of j
-- bits with its two extensions by a last bit, which is the top wire.
-- A merge moves between neighbouring wires along their swap when the
-- gate passes it (`merge-up`, `merge-up′`: BoxMergeAt's steps, for any
-- gate).  And a gate passes a product over `allBits` times an inverse of
-- its all-black factor when it passes every other factor (`pass-last′`:
-- Canon40's `pass-last` without the involution), which is the D-trick of
-- Lemma 8.5's proof (Appendix E.3).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.MergeGen where

open import Data.Bool using (Bool ; true ; false)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; _<_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-trans ; ≤-refl ; n≤1+n)
open import Data.Vec using (Vec ; [] ; _∷_ ; _∷ʳ_ ; replicate)
open import Data.Vec.Properties using (∷-injectiveʳ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat ; swapAt)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; insertℕ)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.TopWeakening using (top)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt ; placeAt-step ; X-step)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceCalc
  using (placeAt-• ; placeAt-ε ; placeAt-cong ; placeAt-X-lo ; placeAt-zero ; placeAt-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; negs²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.TwoWire using (placeAt-top)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc using (swapAt²)

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

  -- A gate passing every factor passes the product.
  pass-∏ : ∀ {y : Circuit n} (xs : List A) g → (∀ a → y • g a ≈ g a • y) → y • ∏ xs g ≈ ∏ xs g • y
  pass-∏ []       g e = trans right-unit (sym left-unit)
  pass-∏ (x ∷ xs) g e =
    trans (sym assoc) (trans (front _ (e x)) (trans assoc (trans (back _ (pass-∏ xs g e)) (sym assoc))))

∏-map : ∀ {A C Y : Set} (h : C → A) (xs : List C) (g : A → Word Y) → ∏ (map h xs) g ≡ ∏ xs (λ c → g (h c))
∏-map h []       g = Eq.refl
∏-map h (x ∷ xs) g = Eq.cong (g (h x) •_) (∏-map h xs g)

-- A product of shifted gates is the shifted product.
∏-↑ : ∀ {A : Set} (xs : List A) (g : A → Circuit n) → ∏ xs (λ a → g a ↑) ≡ ∏ xs g ↑
∏-↑ []       g = Eq.refl
∏-↑ (x ∷ xs) g = Eq.cong (g x ↑ •_) (∏-↑ xs g)

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
-- The D-trick

module _ {n : ℕ} where
  open Tools (n VRel,_===_)

  private
    via : ∀ {y a b : Circuit n} → a ≈ b → y • b ≈ b • y → y • a ≈ a • y
    via e p = trans (back _ e) (trans p (front _ (sym e)))

    pass₂ : ∀ {y a b : Circuit n} → y • a ≈ a • y → y • b ≈ b • y → y • (a • b) ≈ (a • b) • y
    pass₂ pa pb = trans (sym assoc) (trans (front _ pa) (trans assoc (trans (back _ pb) (sym assoc))))

  -- A gate passes the product over every colouring times an inverse h
  -- of the all-black factor, which comes last, when it passes every
  -- other factor.
  pass-last′ : ∀ j (g : Bits j → Circuit n) {y h : Circuit n} →
               (∀ c → c ≢ replicate j true → y • g c ≈ g c • y) →
               g (replicate j true) • h ≈ ε →
               y • (∏ (allBits j) g • h) ≈ (∏ (allBits j) g • h) • y
  pass-last′ zero    g p e = via (trans (front _ right-unit) e) (trans right-unit (sym left-unit))
  pass-last′ (suc j) g {y} {h} p e =
    via split (pass₂ (pass-∏ (allBits j) (λ c → g (false ∷ c)) (λ c → p (false ∷ c) (λ ())))
                     (pass-last′ j (λ c → g (true ∷ c)) (λ c c≢ → p (true ∷ c) (λ q → c≢ (∷-injectiveʳ q))) e))
    where
    A : List (Bits j)
    A = allBits j
    ≡→≈ : ∀ {a b : Circuit n} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl
    split : ∏ (allBits (suc j)) g • h ≈ ∏ A (λ c → g (false ∷ c)) • (∏ A (λ c → g (true ∷ c)) • h)
    split = begin
      ∏ (map (false ∷_) A ++ map (true ∷_) A) g • h
        ≈⟨ front _ (∏-++ (map (false ∷_) A) (map (true ∷_) A) g) ⟩
      (∏ (map (false ∷_) A) g • ∏ (map (true ∷_) A) g) • h
        ≈⟨ front _ (≡→≈ (Eq.cong₂ _•_ (∏-map (false ∷_) A g) (∏-map (true ∷_) A g))) ⟩
      (∏ A (λ c → g (false ∷ c)) • ∏ A (λ c → g (true ∷ c))) • h
        ≈⟨ assoc ⟩
      ∏ A (λ c → g (false ∷ c)) • (∏ A (λ c → g (true ∷ c)) • h) ∎

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
-- One pair

-- A gate with a white and a black control at p, the other colours W,
-- merges to u placed around the idle wire p, coloured W.
pair-merge : ∀ {K} (g : Circuit (₁₊ K)) (u : Circuit K) p → p ≤ K → (W : Bits K) →
             (₁₊ K) ⊢ (Xat p • g • Xat p) • g ≈ placeAt p u →
             (₁₊ K) ⊢ (negsB (insertℕ p false W) • g • negsB (insertℕ p false W)) •
                      (negsB (insertℕ p true W) • g • negsB (insertℕ p true W))
                      ≈ placeAt p (negsB W • u • negsB W)
pair-merge {K} g u p p≤ W m = begin
  (Nf • g • Nf) • (N • g • N)
    ≈⟨ front _ (cong (trans (negsB-white p W p≤) (X-negsB p (insertℕ p true W)))
                     (back _ (negsB-white p W p≤))) ⟩
  ((N • Xat p) • g • (Xat p • N)) • (N • g • N)
    ≈⟨ by-passoc (((□ • □) • □ • (□ • □)) • (□ • □ • □)) (□ • (□ • □ • □) • (□ • □) • □ • □) Eq.refl ⟩
  N • (Xat p • g • Xat p) • (N • N) • g • N
    ≈⟨ back _ (back _ (trans (front _ (negs² (insertℕ p true W))) left-unit)) ⟩
  N • (Xat p • g • Xat p) • g • N
    ≈⟨ back _ (trans (sym assoc) (front _ m)) ⟩
  N • placeAt p u • N
    ≈⟨ cong N≈ (back _ N≈) ⟩
  placeAt p M • placeAt p u • placeAt p M
    ≈⟨ sym (trans (placeAt-• p M (u • M)) (back _ (placeAt-• p u M))) ⟩
  placeAt p (M • u • M) ∎
  where
  open Tools ((₁₊ K) VRel,_===_)
  N Nf : Circuit (₁₊ K)
  N  = negsB (insertℕ p true W)
  Nf = negsB (insertℕ p false W)
  M : Circuit K
  M = negsB W
  N≈ : N ≈ placeAt p M
  N≈ = sym (placeAt-negsB p W p≤)

------------------------------------------------------------------------
-- Every colouring of the controls

private
  ins-top : ∀ {j} (c : Bits j) b → insertℕ j b c ≡ c ∷ʳ b
  ins-top []      b = Eq.refl
  ins-top (x ∷ c) b = Eq.cong (x ∷_) (ins-top c b)

-- F K on 1 + K wires, merging on the top wire at every width 2 + K
-- with K < B.  `top-↓` and `↓-0` say that F 0 is closed, as it is for
-- every instance: F 0 ↓ᵏ j then computes.
module MergeTop (F : (K : ℕ) → Circuit (₁₊ K)) (B : ℕ)
  (top-merge : ∀ K → K < B →
               (₂₊ K) ⊢ (Xat (suc K) • F (suc K) • Xat (suc K)) • F (suc K) ≈ placeAt (suc K) (F K))
  (↓-0 : F 0 ↓ᵏ 0 ≡ F 0)
  (top-↓ : ∀ j → top (F 0 ↓ᵏ j) ≡ F 0 ↓ᵏ suc j)
  where

  merge-top₀ : ∀ j → j ≤ B →
               (₁₊ j) ⊢ ∏ (allBits j) (λ c → negsB (true ∷ c) • F j • negsB (true ∷ c)) ≈ F 0 ↓ᵏ j
  merge-top₀ zero    _ = trans right-unit (trans left-unit (trans right-unit (≡→≈ (Eq.sym ↓-0))))
    where
    open Tools (1 VRel,_===_)
    ≡→≈ : ∀ {x y : Circuit 1} → x ≡ y → x ≈ y
    ≡→≈ Eq.refl = refl
  merge-top₀ (suc j) b = begin
    ∏ (allBits (suc j)) G
      ≈⟨ pairing j G ⟩
    ∏ (allBits j) (λ c → G (c ∷ʳ false) • G (c ∷ʳ true))
      ≈⟨ ∏-cong (allBits j) pair ⟩
    ∏ (allBits j) (λ c → placeAt (suc j) (h c))
      ≈⟨ sym (placeAt-∏ (suc j) (allBits j) h) ⟩
    placeAt (suc j) (∏ (allBits j) h)
      ≈⟨ placeAt-cong (suc j) (merge-top₀ j (≤-trans (n≤1+n j) b)) ⟩
    placeAt (suc j) (F 0 ↓ᵏ j)
      ≈⟨ placeAt-top (F 0 ↓ᵏ j) ⟩
    top (F 0 ↓ᵏ j)
      ≈⟨ ≡→≈ (top-↓ j) ⟩
    F 0 ↓ᵏ suc j ∎
    where
    open Tools ((₂₊ j) VRel,_===_)
    G : Bits (suc j) → Circuit (₂₊ j)
    G c = negsB (true ∷ c) • F (suc j) • negsB (true ∷ c)
    h : Bits j → Circuit (₁₊ j)
    h c = negsB (true ∷ c) • F j • negsB (true ∷ c)
    ≡→≈ : ∀ {x y : Circuit (₂₊ j)} → x ≡ y → x ≈ y
    ≡→≈ Eq.refl = refl
    pair : ∀ c → G (c ∷ʳ false) • G (c ∷ʳ true) ≈ placeAt (suc j) (h c)
    pair c = trans (≡→≈ (Eq.cong₂ (λ x y → (negsB (true ∷ x) • F (suc j) • negsB (true ∷ x)) •
                                          (negsB (true ∷ y) • F (suc j) • negsB (true ∷ y)))
                                 (Eq.sym (ins-top c false)) (Eq.sym (ins-top c true))))
                   (pair-merge (F (suc j)) (F j) (suc j) ≤-refl (true ∷ c) (top-merge j b))

------------------------------------------------------------------------
-- Moving a merge one wire up

module _ {n : ℕ} where
  open Tools ((₁₊ n) VRel,_===_)

  private
    SgS : ∀ {S g : Circuit (₁₊ n)} → S • S ≈ ε → S • g ≈ g • S → S • g • S ≈ g
    SgS SS Sg = trans (sym assoc) (trans (front _ Sg) (trans assoc (trans (back _ SS) right-unit)))

  -- Conjugating a merge by a swap S that passes the gate.
  conj-merge : ∀ {S X g P : Circuit (₁₊ n)} → S • S ≈ ε → S • g ≈ g • S → g • (X • g • X) ≈ P →
               g • ((S • X • S) • g • (S • X • S)) ≈ S • P • S
  conj-merge {S} {X} {g} {P} SS Sg e = begin
    g • ((S • X • S) • g • (S • X • S))
      ≈⟨ by-passoc (□ • ((□ • □ • □) • □ • (□ • □ • □))) ((□ • □) • □ • (□ • □ • □) • □ • □) Eq.refl ⟩
    (g • S) • X • (S • g • S) • X • S
      ≈⟨ cong (sym Sg) (back _ (front _ (SgS SS Sg))) ⟩
    (S • g) • X • g • X • S
      ≈⟨ by-passoc ((□ • □) • □ • □ • □ • □) (□ • (□ • (□ • □ • □)) • □) Eq.refl ⟩
    S • (g • (X • g • X)) • S
      ≈⟨ back _ (front _ e) ⟩
    S • P • S ∎

  conj-merge′ : ∀ {S X g P : Circuit (₁₊ n)} → S • S ≈ ε → S • g ≈ g • S → (X • g • X) • g ≈ P →
                ((S • X • S) • g • (S • X • S)) • g ≈ S • P • S
  conj-merge′ {S} {X} {g} {P} SS Sg e = begin
    ((S • X • S) • g • (S • X • S)) • g
      ≈⟨ by-passoc (((□ • □ • □) • □ • (□ • □ • □)) • □) (□ • □ • (□ • □ • □) • □ • (□ • □)) Eq.refl ⟩
    S • X • (S • g • S) • X • (S • g)
      ≈⟨ back _ (back _ (cong (SgS SS Sg) (back _ Sg))) ⟩
    S • X • g • X • (g • S)
      ≈⟨ by-passoc (□ • □ • □ • □ • (□ • □)) (□ • ((□ • □ • □) • □) • □) Eq.refl ⟩
    S • ((X • g • X) • g) • S
      ≈⟨ back _ (front _ e) ⟩
    S • P • S ∎

  -- A merge on wire c moves to wire c + 1.
  merge-up : ∀ {g : Circuit (₁₊ n)} {u : Circuit n} c → c < n → swapAt c • g ≈ g • swapAt c →
             g • (Xat c • g • Xat c) ≈ placeAt c u →
             g • (Xat (suc c) • g • Xat (suc c)) ≈ placeAt (suc c) u
  merge-up {g} {u} c b Sg m = begin
    g • (Xat (suc c) • g • Xat (suc c))
      ≈⟨ back _ (sym (cong (X-step c b) (back _ (X-step c b)))) ⟩
    g • ((swapAt c • Xat c • swapAt c) • g • (swapAt c • Xat c • swapAt c))
      ≈⟨ conj-merge (swapAt² c) Sg m ⟩
    swapAt c • placeAt c u • swapAt c
      ≈⟨ sym (placeAt-step c u b) ⟩
    placeAt (suc c) u ∎

  merge-up′ : ∀ {g : Circuit (₁₊ n)} {u : Circuit n} c → c < n → swapAt c • g ≈ g • swapAt c →
              (Xat c • g • Xat c) • g ≈ placeAt c u →
              (Xat (suc c) • g • Xat (suc c)) • g ≈ placeAt (suc c) u
  merge-up′ {g} {u} c b Sg m = begin
    (Xat (suc c) • g • Xat (suc c)) • g
      ≈⟨ front _ (sym (cong (X-step c b) (back _ (X-step c b)))) ⟩
    ((swapAt c • Xat c • swapAt c) • g • (swapAt c • Xat c • swapAt c)) • g
      ≈⟨ conj-merge′ (swapAt² c) Sg m ⟩
    swapAt c • placeAt c u • swapAt c
      ≈⟨ sym (placeAt-step c u b) ⟩
    placeAt (suc c) u ∎

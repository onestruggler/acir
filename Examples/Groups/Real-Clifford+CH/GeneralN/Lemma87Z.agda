------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.7 for Z: decoding the encoding of Z gives Z back (Clément,
-- Appendix E.4, the case of Z)
--
-- E(Z) on wire p is, over every context c of the other wires but the
-- pairing wire q, the sign pair on the two codes that differ at q with
-- the bit 1 on p (Definition 8.2).  Each decodes, by Lemma 8.4, to the
-- box on q with the other bits as controls (`factor`; the reversal in
-- the decoding does not matter, a box being an involution).  Brought to
-- the frame where q is wire 0, p wire 1 and the context the wires above
-- in order (`shiftDown`, and for p ≠ 0 once more one wire up: `frame₀`,
-- `frame₁`), the colours are false ∷ true ∷ c, and MergeAll merges the
-- product over c into the box with the one control p: Z on wire 1
-- (`canonical`), which the frame carries back to wire p (`lemmaZ`).
--
-- Parameters: the canonical box facts at the full width (Lemma 8.4) and
-- the merge (309) at every width up to it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; _≤_ ; suc)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon ; module Frames ; pl ; pl-cong ; pl-• ; pl-•₃ ; perm-• ; perm-↑0 ; perm-↑s)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Word.Base using (_•_)

module Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87Z
  {m : ℕ} (C : Canon m)
  (mergeAt′ : ∀ K → 1 ≤ K → K ≤ ₁₊ m → ∀ c → 1 ≤ c → c ≤ suc K →
              (₂₊ K) ⊢ (Xat c • Λ□ (suc K) • Xat c) • Λ□ (suc K) ≈ placeAt c (Λ□ K))
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using (Fin ; toℕ ; fromℕ<) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (zero ; _<_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n ; n<1+n)
open import Data.Vec using (Vec ; [] ; _∷_ ; _∷ʳ_ ; reverse)
open import Data.Vec.Properties using (reverse-∷ ; reverse-involutive)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _ʷ)

import Examples.Groups.Symmetric.Syntactics as S
open import Presentation.GroupLike using (module Group-Lemmas)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; X²)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; net-↑ ; perm)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (mc□)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev≈⁻¹ ; rev-cong)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (index)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; insertℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas using (insert-swap)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏ ; zz ; E-Z ; str₁)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d ; dZZ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires
  using (sdS ; revS ; revS-↑ ; net-inv ; negsB ; negs² ; sd-negsB ; sd-target ; sd-fix ; sd-0)
open import Examples.Groups.Real-Clifford+CH.GeneralN.OneWire using (on1 ; on1-net ; placeAt-on1-lo)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Layouts using (layoutAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma84 C using (mc□-boxF ; lemma84)
open import Examples.Groups.Real-Clifford+CH.GeneralN.MergeAll (₁₊ m) mergeAt′
  using (Pos ; [] ; pos ; GapD₁ ; VD₁ ; merge-all₁ ; ∏-cong)

open Frames C using (boxF ; frame-eq)

private
  N : ℕ
  N = ₃₊ m

------------------------------------------------------------------------
-- Bits

flip-insert : ∀ {k} i b (v : Bits k) → i ≤ k → flipAt i (insertℕ i b v) ≡ insertℕ i (not b) v
flip-insert zero    b v       _       = Eq.refl
flip-insert (suc i) b []      ()
flip-insert (suc i) b (c ∷ v) (s≤s p) = Eq.cong (c ∷_) (flip-insert i b v p)

flip-below : ∀ {k} j i b (v : Bits k) → j < i → i ≤ k → flipAt j (insertℕ i b v) ≡ insertℕ i b (flipAt j v)
flip-below j       zero    b v       ()      _
flip-below zero    (suc i) b []      _       ()
flip-below (suc j) (suc i) b []      _       ()
flip-below zero    (suc i) b (c ∷ v) _       _       = Eq.refl
flip-below (suc j) (suc i) b (c ∷ v) (s≤s p) (s≤s q) = Eq.cong (c ∷_) (flip-below j i b v p q)

insert-end : ∀ {j} (v : Bits j) x → insertℕ j x v ≡ v ∷ʳ x
insert-end []      x = Eq.refl
insert-end (y ∷ v) x = Eq.cong (y ∷_) (insert-end v x)

-- The positions j + 1, …, 2: the context above the wires 0 and 1.
upto : ∀ j → Vec ℕ j
upto zero    = []
upto (suc j) = ₂₊ j ∷ upto j

Pos-upto : ∀ j → Pos (suc j) (upto j)
Pos-upto zero    = []
Pos-upto (suc j) = pos (s≤s z≤n) ≤-refl (Pos-upto j)

private
  VD-upto : ∀ {j} (rc : Bits j) a b → VD₁ (upto j) rc (a ∷ b ∷ []) ≡ a ∷ b ∷ reverse rc
  VD-upto []       a b = Eq.refl
  VD-upto {suc j} (x ∷ rc) a b =
    Eq.trans (Eq.cong (insertℕ (₂₊ j) x) (VD-upto rc a b))
             (Eq.cong (λ v → a ∷ b ∷ v) (Eq.trans (insert-end (reverse rc) x) (Eq.sym (reverse-∷ x rc))))

  VD-frame : ∀ {j} (c : Bits j) → VD₁ (upto j) (reverse c) (false ∷ true ∷ []) ≡ false ∷ true ∷ c
  VD-frame c = Eq.trans (VD-upto (reverse c) false true) (Eq.cong (λ v → false ∷ true ∷ v) (reverse-involutive c))

------------------------------------------------------------------------
-- The merged product, below the full width

private
  base-Z : 2 ⊢ negsB (false ∷ true ∷ []) • Λ□ 1 • negsB (false ∷ true ∷ []) ≈ Z ↑
  base-Z = begin
    (X • ε) • Z ↑ • (X • ε)     ≈⟨ cong right-unit (back _ right-unit) ⟩
    X • Z ↑ • X                 ≈⟨ trans (sym assoc) (front _ (X-↑ Z)) ⟩
    (Z ↑ • X) • X               ≈⟨ trans assoc (trans (back _ X²) right-unit) ⟩
    Z ↑ ∎
    where open Tools (2 VRel,_===_)

  gap-cong : ∀ {j} (ps : Vec ℕ j) {a b : Circuit 2} → 2 ⊢ a ≈ b → (₂₊ j) ⊢ GapD₁ ps a ≈ GapD₁ ps b
  gap-cong []       e = e
  gap-cong {suc j} (p ∷ ps) {a} {b} e = back _ (front _ (lemma-cong↑ (GapD₁ ps a) (GapD₁ ps b) (gap-cong ps e)))
    where open Tools ((₃₊ j) VRel,_===_)

  gap-Z : ∀ j → (₂₊ j) ⊢ GapD₁ (upto j) (Z ↑) ≈ on1 Z 1
  gap-Z zero    = refl
    where open Tools (2 VRel,_===_)
  gap-Z (suc j) = trans (back _ (front _ (lemma-cong↑ _ _ (gap-Z j))))
                        (placeAt-on1-lo Z (₂₊ j) 1 (s≤s (s≤s z≤n)) ≤-refl)
    where open Tools ((₃₊ j) VRel,_===_)

------------------------------------------------------------------------
-- At the full width

open Tools (N VRel,_===_)
open Group-Lemmas (N VRel,_===_) grouplike using (_⁻¹ ; inverseʳ-unique)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

-- The decoding through a product.
dʷ-∏ : ∀ {A : Set} (xs : List A) (f : A → Word (GenP N)) → (d ʷ) (∏ xs f) ≡ ∏ xs (λ x → (d ʷ) (f x))
dʷ-∏ []       f = Eq.refl
dʷ-∏ (x ∷ xs) f = Eq.cong ((d ʷ) (f x) •_) (dʷ-∏ xs f)

-- A network through a product.
pl-ε : ∀ (u : Word (S.Gen N)) → pl u ε ≈ ε
pl-ε u = trans (back _ left-unit) (net-inv u)

pl-∏ : ∀ {A : Set} (u : Word (S.Gen N)) (xs : List A) (g : A → Circuit N) →
       pl u (∏ xs g) ≈ ∏ xs (λ a → pl u (g a))
pl-∏ u []       g = pl-ε u
pl-∏ u (x ∷ xs) g = trans (pl-• u (g x) (∏ xs g)) (back _ (pl-∏ u xs g))

-- A placed box is an involution, hence its own reversal.
box² : ∀ u s → boxF u s • boxF u s ≈ ε
box² u s = begin
  (M • A • M) • (M • A • M)       ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
  M • A • ((M • M) • A • M)       ≈⟨ back _ (back _ (trans (front _ (negs² s)) left-unit)) ⟩
  M • A • (A • M)                 ≈⟨ back _ (trans (sym assoc) (front _ AA)) ⟩
  M • ε • M                       ≈⟨ back _ left-unit ⟩
  M • M                           ≈⟨ negs² s ⟩
  ε ∎
  where
  M A : Circuit N
  M = negsB s
  A = pl u (Λ□ (₂₊ m))
  AA : A • A ≈ ε
  AA = trans (sym (pl-• u (Λ□ (₂₊ m)) (Λ□ (₂₊ m)))) (trans (pl-cong u (Canon.invol C)) (pl-ε u))

rev-invol : ∀ (w : Circuit N) → w • w ≈ ε → rev w ≈ w
rev-invol w ww = trans (rev≈⁻¹ w) (sym (inverseʳ-unique ww))

-- The canonical product merges to Z on wire 1.
canonical : ∏ (allBits (₁₊ m)) (λ c → negsB (false ∷ true ∷ c) • Λ□ (₂₊ m) • negsB (false ∷ true ∷ c)) ≈ on1 Z 1
canonical = begin
  ∏ (allBits (₁₊ m)) (λ c → negsB (false ∷ true ∷ c) • Λ□ (₂₊ m) • negsB (false ∷ true ∷ c))
    ≈⟨ ∏-cong (allBits (₁₊ m)) (λ c → ≡→≈ (Eq.cong (λ v → negsB v • Λ□ (₂₊ m) • negsB v) (Eq.sym (VD-frame c)))) ⟩
  ∏ (allBits (₁₊ m)) (λ c → negsB (VD₁ (upto (₁₊ m)) (reverse c) (false ∷ true ∷ [])) • Λ□ (₂₊ m) •
                            negsB (VD₁ (upto (₁₊ m)) (reverse c) (false ∷ true ∷ [])))
    ≈⟨ merge-all₁ (upto (₁₊ m)) (Pos-upto (₁₊ m)) ≤-refl (false ∷ true ∷ []) ⟩
  GapD₁ (upto (₁₊ m)) (negsB (false ∷ true ∷ []) • Λ□ 1 • negsB (false ∷ true ∷ []))
    ≈⟨ gap-cong (upto (₁₊ m)) base-Z ⟩
  GapD₁ (upto (₁₊ m)) (Z ↑)
    ≈⟨ gap-Z (₁₊ m) ⟩
  on1 Z 1 ∎

------------------------------------------------------------------------
-- The factors

-- The pairing wire of a gate on wire p: the one below it, or the top
-- wire for p = 0.
pairing : ℕ → ℕ
pairing zero    = ₂₊ m
pairing (suc p) = p

pairing< : ∀ p → p < N → pairing p < N
pairing< zero    _   = ≤-refl
pairing< (suc p) p<N = ≤-trans (n≤1+n (suc p)) p<N

private
  flip-str : ∀ p c → p < N → str₁ {m} p c true true ≡ flipAt (pairing p) (str₁ p c false true)
  flip-str zero    c _ = Eq.sym (flip-insert (₂₊ m) false (true ∷ c) ≤-refl)
  flip-str (suc p) c (s≤s (s≤s p≤)) = Eq.sym
    (Eq.trans (flip-below p (suc p) true (insertℕ p false c) (n<1+n p) (s≤s p≤))
              (Eq.cong (insertℕ (suc p) true) (flip-insert p false c p≤)))

-- A sign pair on two codes that differ at one wire decodes to the box on
-- that wire (Lemma 8.4, reversed: the box is an involution).
factorG : ∀ q → q < N → (G : Bits N) → (d ʷ) (zz (index N G) (index N (flipAt q G))) ≈ boxF (sdS q) G
factorG q q<N G = trans (rev-cong e84) (trans (rev-invol (mc□ L) (trans (cong mb mb) (box² (sdS q) G))) mb)
  where
  L = layoutAt q G
  e84 : dZZ {m} (toℕ (index N G)) (toℕ (index N (flipAt q G))) ≈ mc□ L
  e84 = Eq.subst (λ t → dZZ {m} (toℕ (index N G)) (toℕ (index N (flipAt t G))) ≈ mc□ (layoutAt t G))
                 (toℕ-fromℕ< q<N) (lemma84 (fromℕ< q<N) G)
  mb : mc□ L ≈ boxF (sdS q) G
  mb = mc□-boxF q q<N G

-- Each factor of E(Z) decodes to the box on the pairing wire.
factor : ∀ p → p < N → ∀ c →
         (d ʷ) (zz (index N (str₁ p c false true)) (index N (str₁ p c true true)))
           ≈ boxF (sdS (pairing p)) (str₁ p c false true)
factor p p<N c =
  Eq.subst (λ w → (d ʷ) (zz (index N (str₁ p c false true)) (index N w)) ≈ boxF (sdS (pairing p)) (str₁ p c false true))
           (Eq.sym (flip-str p c p<N)) (factorG (pairing p) (pairing< p p<N) (str₁ p c false true))

------------------------------------------------------------------------
-- The frames

private
  N₀ : Bits (₁₊ m) → Circuit N
  N₀ c = negsB (false ∷ true ∷ c)

  h : Bits (₁₊ m) → Circuit N
  h c = N₀ c • Λ□ (₂₊ m) • N₀ c

-- The gate on wire 0, its pairing wire on top: shiftDown alone.
frame₀ : ∀ c → boxF (sdS (₂₊ m)) (str₁ 0 c false true) ≈ pl (sdS (₂₊ m)) (h c)
frame₀ c = sym (pl-•₃ (sdS (₂₊ m)) s refl s)
  where
  s : pl (sdS (₂₊ m)) (N₀ c) ≈ negsB (str₁ 0 c false true)
  s = sd-negsB (₂₊ m) false (true ∷ c) ≤-refl

-- The gate on wire 1 + p, its pairing wire p: shiftDown p, then again
-- one wire up.
module Frame₁ (p : ℕ) (p≤ : p ≤ ₁₊ m) where

  σ : Word (S.Gen N)
  σ = sdS p • (sdS p S.↑)

  pF : Fin N
  pF = fromℕ< (s≤s (≤-trans p≤ (n≤1+n _)))

  tp : toℕ pF ≡ p
  tp = toℕ-fromℕ< (s≤s (≤-trans p≤ (n≤1+n _)))

  pq : perm (sdS {N} p) ⟨$⟩ʳ pF ≡ 0F
  pq = Eq.subst (λ j → perm (sdS {N} j) ⟨$⟩ʳ pF ≡ 0F) tp (sd-target pF)

  σq : perm σ ⟨$⟩ʳ pF ≡ 0F
  σq = Eq.trans (perm-• (sdS p) (sdS p S.↑) pF)
         (Eq.trans (Eq.cong (perm (sdS p S.↑) ⟨$⟩ʳ_) pq) (perm-↑0 (sdS p)))

  private
    nets : ∀ (w : Circuit N) → net (sdS p S.↑) • w • net (revS (sdS p S.↑)) ≡ net (sdS p) ↑ • w • net (revS (sdS p)) ↑
    nets w = Eq.cong₂ (λ a b → a • w • b) (net-↑ (sdS p))
                      (Eq.trans (Eq.cong net (revS-↑ (sdS p))) (net-↑ (revS (sdS p))))

    -- The colours, through the upper network and then the lower one.
    up : ∀ x y c → net (sdS p S.↑) • negsB (x ∷ y ∷ c) • net (revS (sdS p S.↑)) ≈ negsB (x ∷ insertℕ p y c)
    up true y c = trans (≡→≈ (nets (negsB (y ∷ c) ↑))) (lemma-cong↑ _ _ (sd-negsB p y c p≤))
    up false y c = begin
      net (sdS p S.↑) • (X • negsB (y ∷ c) ↑) • net (revS (sdS p S.↑))
        ≈⟨ ≡→≈ (nets (X • negsB (y ∷ c) ↑)) ⟩
      net (sdS p) ↑ • (X • negsB (y ∷ c) ↑) • net (revS (sdS p)) ↑
        ≈⟨ trans (sym assoc) (front _ (sym (X-↑ (net (sdS p))))) ⟩
      (X • net (sdS p) ↑) • negsB (y ∷ c) ↑ • net (revS (sdS p)) ↑
        ≈⟨ assoc ⟩
      X • (net (sdS p) • negsB (y ∷ c) • net (revS (sdS p))) ↑
        ≈⟨ back _ (lemma-cong↑ _ _ (sd-negsB p y c p≤)) ⟩
      X • negsB (insertℕ p y c) ↑ ∎

  -- The frame's colours x on wire 0, y on wire 1 and c above are those
  -- of the basis vector with x on the pairing wire and y on the gate.
  colours′ : ∀ x y c → pl σ (negsB (x ∷ y ∷ c)) ≈ negsB (str₁ (suc p) c x y)
  colours′ x y c = begin
    (net (sdS p) • net (sdS p S.↑)) • negsB (x ∷ y ∷ c) • (net (revS (sdS p S.↑)) • net (revS (sdS p)))
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    net (sdS p) • (net (sdS p S.↑) • negsB (x ∷ y ∷ c) • net (revS (sdS p S.↑))) • net (revS (sdS p))
      ≈⟨ back _ (front _ (up x y c)) ⟩
    net (sdS p) • negsB (x ∷ insertℕ p y c) • net (revS (sdS p))
      ≈⟨ sd-negsB p x (insertℕ p y c) (≤-trans p≤ (n≤1+n _)) ⟩
    negsB (insertℕ p x (insertℕ p y c))
      ≈⟨ ≡→≈ (Eq.cong negsB (insert-swap p p y x c ≤-refl p≤)) ⟩
    negsB (insertℕ (suc p) y (insertℕ p x c)) ∎

  frame₁ : ∀ c → boxF (sdS p) (str₁ (suc p) c false true) ≈ pl σ (h c)
  frame₁ c = sym (pl-•₃ σ (colours′ false true c) (frame-eq σ (sdS p) pF σq pq) (colours′ false true c))

  -- A one-wire circuit on the frame's wire 1 is on wire 1 + p.
  back : ∀ (g : Circuit 1) → pl σ (on1 g 1) ≈ on1 g (suc p)
  back g = Eq.subst₂ (λ f t → net σ • on1 g (toℕ f) • net (revS σ) ≈ on1 g (suc t)) σj tj (on1-net g σ (sF jF))
    where
    jF : Fin (₂₊ m)
    jF = fromℕ< (s≤s p≤)
    tj : toℕ jF ≡ p
    tj = toℕ-fromℕ< (s≤s p≤)
    σj : perm σ ⟨$⟩ʳ sF jF ≡ sF 0F
    σj = Eq.trans (perm-• (sdS p) (sdS p S.↑) (sF jF))
         (Eq.trans (Eq.cong (perm (sdS p S.↑) ⟨$⟩ʳ_) (sd-fix p (sF jF) (s≤s (≤-reflexive′ tj))))
           (Eq.trans (perm-↑s (sdS p) jF)
             (Eq.cong sF (Eq.subst (λ j → perm (sdS {₂₊ m} j) ⟨$⟩ʳ jF ≡ 0F) tj (sd-target jF)))))
      where
      ≤-reflexive′ : ∀ {a b} → a ≡ b → b ≤ a
      ≤-reflexive′ Eq.refl = ≤-refl

  back-Z : pl σ (on1 Z 1) ≈ on1 Z (suc p)
  back-Z = back Z

-- The gate on wire 0: a one-wire circuit on the frame's wire 1 is on
-- wire 0.
back₀ : ∀ (g : Circuit 1) → pl (sdS (₂₊ m)) (on1 g 1) ≈ on1 g 0
back₀ g = Eq.subst (λ f → net (sdS (₂₊ m)) • on1 g (toℕ f) • net (revS (sdS (₂₊ m))) ≈ on1 g 0)
                   (sd-0 (suc m)) (on1-net g (sdS (₂₊ m)) 0F)

------------------------------------------------------------------------
-- Lemma 8.7 for Z

lemmaZ : ∀ p → p < N → on1 Z p ≈ (d ʷ) (E-Z {m} p)
lemmaZ zero p<N = sym (begin
  (d ʷ) (E-Z 0)
    ≈⟨ ≡→≈ (dʷ-∏ (allBits (₁₊ m)) (λ c → zz (index N (str₁ 0 c false true)) (index N (str₁ 0 c true true)))) ⟩
  ∏ (allBits (₁₊ m)) (λ c → (d ʷ) (zz (index N (str₁ 0 c false true)) (index N (str₁ 0 c true true))))
    ≈⟨ ∏-cong (allBits (₁₊ m)) (λ c → trans (factor 0 p<N c) (frame₀ c)) ⟩
  ∏ (allBits (₁₊ m)) (λ c → pl (sdS (₂₊ m)) (h c))
    ≈⟨ sym (pl-∏ (sdS (₂₊ m)) (allBits (₁₊ m)) h) ⟩
  pl (sdS (₂₊ m)) (∏ (allBits (₁₊ m)) h)
    ≈⟨ pl-cong (sdS (₂₊ m)) canonical ⟩
  pl (sdS (₂₊ m)) (on1 Z 1)
    ≈⟨ Eq.subst (λ f → net (sdS (₂₊ m)) • on1 Z (toℕ f) • net (revS (sdS (₂₊ m))) ≈ on1 Z 0)
                (sd-0 (suc m)) (on1-net Z (sdS (₂₊ m)) 0F) ⟩
  on1 Z 0 ∎)
lemmaZ (suc p) (s≤s (s≤s p≤)) = sym (begin
  (d ʷ) (E-Z (suc p))
    ≈⟨ ≡→≈ (dʷ-∏ (allBits (₁₊ m)) (λ c → zz (index N (str₁ (suc p) c false true)) (index N (str₁ (suc p) c true true)))) ⟩
  ∏ (allBits (₁₊ m)) (λ c → (d ʷ) (zz (index N (str₁ (suc p) c false true)) (index N (str₁ (suc p) c true true))))
    ≈⟨ ∏-cong (allBits (₁₊ m)) (λ c → trans (factor (suc p) (s≤s (s≤s p≤)) c) (F.frame₁ c)) ⟩
  ∏ (allBits (₁₊ m)) (λ c → pl F.σ (h c))
    ≈⟨ sym (pl-∏ F.σ (allBits (₁₊ m)) h) ⟩
  pl F.σ (∏ (allBits (₁₊ m)) h)
    ≈⟨ pl-cong F.σ canonical ⟩
  pl F.σ (on1 Z 1)
    ≈⟨ F.back-Z ⟩
  on1 Z (suc p) ∎)
  where
  module F = Frame₁ p p≤

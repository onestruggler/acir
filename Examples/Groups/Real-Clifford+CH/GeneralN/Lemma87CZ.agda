------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.7 for CZ: decoding the encoding of CZ gives CZ back (Clément,
-- Appendix E.4, the case of CZ)
--
-- As for Z (`Lemma87Z`): E(CZ) on the wires p, p + 1 is, over every
-- context c of the other wires but the pairing wire q, the sign pair on
-- the two codes that differ at q with the bits 1 on the gate; each
-- decodes to the box on q (`factor₂`), and the product merges.  Here the
-- merge is done in the box's own frame `sdS q`, with no second network:
-- there the gate sits on the wires a + 1, a + 2 (a = 0 for p = 0, whose
-- pairing wire is the top one; a = p − 1 otherwise), the context bits
-- below it and above it in order, and the positions `ps` at which
-- MergeAll inserts them are chosen to match — just below the gate for
-- the first a of them, at the top for the rest.  The merged box is CZ
-- on the wires 1, 2 (`base-CZ`), which the insertions carry to the wires
-- a + 1, a + 2 (`gap-CZ`, by TwoWire), and the frame back to p, p + 1.
--
-- Parameters: as for Z.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; _≤_ ; suc)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
open import Word.Base using (_•_)

module Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87CZ
  {m : ℕ} (C : Canon m)
  (mergeAt′ : ∀ K → 1 ≤ K → K ≤ ₁₊ m → ∀ c → 1 ≤ c → c ≤ suc K →
              (₂₊ K) ⊢ (Xat c • Λ□ (suc K) • Xat c) • Λ□ (suc K) ≈ placeAt c (Λ□ K))
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (zero ; _<_ ; s≤s ; z≤n ; _≤?_)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n ; n<1+n ; ≰⇒> ; <⇒≱ ; ≤-antisym)
open import Data.Vec using (Vec ; [] ; _∷_ ; _∷ʳ_ ; reverse)
open import Data.Vec.Properties using (reverse-∷ ; reverse-involutive)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (ε ; _ʷ)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; X²)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (index)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; insertℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas using (insert-swap)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏ ; zz ; E-CZ ; str₂)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (sdS ; negsB ; sd-negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl ; pl-cong ; pl-•₃ ; module Frames)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceCalc using (placeAt-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.TwoWire
  using (on2 ; pl-sd-on2 ; placeAt-on2-hi ; placeAt-on2-top ; pl-sd-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.MergeAll (₁₊ m) mergeAt′
  using (Pos ; [] ; pos ; GapD₂ ; VD₂ ; merge-all₂ ; ∏-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87Z C mergeAt′
  using (flip-insert ; flip-below ; insert-end ; dʷ-∏ ; pl-∏ ; pairing ; pairing< ; factorG)

open Frames C using (boxF)

private
  N : ℕ
  N = ₃₊ m

------------------------------------------------------------------------
-- The positions of the context

-- Where MergeAll inserts the context bit j, into a word on 3 + j wires:
-- at the top when j ≥ a, else just below the gate.
posOf : ∀ {a j : ℕ} → Dec (a ≤ j) → ℕ
posOf {j = j} (yes _) = ₃₊ j
posOf {j = j} (no _)  = suc j

ps : ∀ j → ℕ → Vec ℕ j
ps zero    a = []
ps (suc j) a = posOf (a ≤? j) ∷ ps j a

private
  Pos-low : ∀ j a → j ≤ a → Pos j (ps j a)
  Pos-low zero    a _ = []
  Pos-low (suc j) a p = step (a ≤? j)
    where
    step : (x : Dec (a ≤ j)) → Pos (suc j) (posOf x ∷ ps j a)
    step (yes q) = ⊥-elim (<⇒≱ p q)
    step (no _)  = pos (s≤s z≤n) ≤-refl (Pos-low j a (≤-trans (n≤1+n j) p))

  Pos-ps : ∀ j a → Pos (₂₊ j) (ps j a)
  Pos-ps zero    a = []
  Pos-ps (suc j) a = step (a ≤? j)
    where
    step : (x : Dec (a ≤ j)) → Pos (₃₊ j) (posOf x ∷ ps j a)
    step (yes _) = pos (s≤s z≤n) ≤-refl (Pos-ps j a)
    step (no q)  = pos (s≤s z≤n) (≤-trans (n≤1+n _) (n≤1+n _)) (Pos-low j a (≤-trans (n≤1+n j) (≰⇒> q)))

------------------------------------------------------------------------
-- The colours

-- False on the box wire, the gate black on a + 1, a + 2.
cols : ∀ {j} → ℕ → Bits j → Bits (₃₊ j)
cols a c = false ∷ insertℕ (suc a) true (insertℕ a true c)

private
  ins-snoc : ∀ {k} i y (r : Bits k) x → i ≤ k → insertℕ i y r ∷ʳ x ≡ insertℕ i y (r ∷ʳ x)
  ins-snoc zero    y r       x _       = Eq.refl
  ins-snoc (suc i) y []      x ()
  ins-snoc (suc i) y (c ∷ r) x (s≤s p) = Eq.cong (c ∷_) (ins-snoc i y r x p)

  ins-sat : ∀ {k} i y (r : Bits k) → k ≤ i → insertℕ i y r ≡ r ∷ʳ y
  ins-sat zero    y []      _       = Eq.refl
  ins-sat (suc i) y []      _       = Eq.refl
  ins-sat zero    y (c ∷ r) ()
  ins-sat (suc i) y (c ∷ r) (s≤s p) = Eq.cong (c ∷_) (ins-sat i y r p)

  ins-mid : ∀ {k} (r : Bits k) x y z → insertℕ k x ((r ∷ʳ y) ∷ʳ z) ≡ ((r ∷ʳ x) ∷ʳ y) ∷ʳ z
  ins-mid []      x y z = Eq.refl
  ins-mid (c ∷ r) x y z = Eq.cong (c ∷_) (ins-mid r x y z)

  VD-ps : ∀ {j} a (rc : Bits j) → VD₂ (ps j a) rc (false ∷ true ∷ true ∷ []) ≡ cols a (reverse rc)
  VD-ps {zero}  zero    [] = Eq.refl
  VD-ps {zero}  (suc a) [] = Eq.refl
  VD-ps {suc j} a (x ∷ rc) = Eq.trans (Eq.cong (insertℕ (posOf (a ≤? j)) x) (VD-ps a rc)) (step (a ≤? j))
    where
    r : Bits j
    r = reverse rc
    rev : r ∷ʳ x ≡ reverse (x ∷ rc)
    rev = Eq.sym (reverse-∷ x rc)
    step : (y : Dec (a ≤ j)) → insertℕ (posOf y) x (cols a r) ≡ cols a (reverse (x ∷ rc))
    step (yes p) = Eq.cong (false ∷_)
      (Eq.trans (insert-end (insertℕ (suc a) true (insertℕ a true r)) x)
      (Eq.trans (ins-snoc (suc a) true (insertℕ a true r) x (s≤s p))
                (Eq.cong (insertℕ (suc a) true) (Eq.trans (ins-snoc a true r x p) (Eq.cong (insertℕ a true) rev)))))
    step (no q) = Eq.cong (false ∷_)
      (Eq.trans (Eq.cong (insertℕ j x)
                  (Eq.trans (Eq.cong (insertℕ (suc a) true) (ins-sat a true r j≤a))
                            (ins-sat (suc a) true (r ∷ʳ true) (s≤s j≤a))))
      (Eq.trans (ins-mid r x true true)
                (Eq.sym (Eq.trans (Eq.cong (insertℕ (suc a) true)
                                    (Eq.trans (Eq.cong (insertℕ a true) (Eq.sym rev)) (ins-sat a true (r ∷ʳ x) j<a)))
                                  (ins-sat (suc a) true ((r ∷ʳ x) ∷ʳ true) (s≤s j<a))))))
      where
      j<a : j < a
      j<a = ≰⇒> q
      j≤a : j ≤ a
      j≤a = ≤-trans (n≤1+n j) j<a

  VD-frame₂ : ∀ a (c : Bits m) → VD₂ (ps m a) (reverse c) (false ∷ true ∷ true ∷ []) ≡ cols a c
  VD-frame₂ a c = Eq.trans (VD-ps a (reverse c)) (Eq.cong (cols a) (reverse-involutive c))

------------------------------------------------------------------------
-- The merged product, below the full width

private
  gap-cong₂ : ∀ {j} (qs : Vec ℕ j) {a b : Circuit 3} → 3 ⊢ a ≈ b → (₃₊ j) ⊢ GapD₂ qs a ≈ GapD₂ qs b
  gap-cong₂ []       e = e
  gap-cong₂ (q ∷ qs) e = placeAt-cong q (gap-cong₂ qs e)

  base-CZ : 3 ⊢ negsB (false ∷ true ∷ true ∷ []) • Λ□ 2 • negsB (false ∷ true ∷ true ∷ []) ≈ CZ ↑
  base-CZ = begin
    (X • ε) • CZ ↑ • (X • ε)    ≈⟨ cong right-unit (back _ right-unit) ⟩
    X • CZ ↑ • X                ≈⟨ trans (sym assoc) (front _ (X-↑ CZ)) ⟩
    (CZ ↑ • X) • X              ≈⟨ trans assoc (trans (back _ X²) right-unit) ⟩
    CZ ↑ ∎
    where open Tools (3 VRel,_===_)

  -- All the context below the gate.
  gap-low : ∀ j a → j ≤ a → (₃₊ j) ⊢ GapD₂ (ps j a) (CZ ↑) ≈ on2 CZ (suc j)
  gap-low zero    a _ = refl
    where open Tools (3 VRel,_===_)
  gap-low (suc j) a p = step (a ≤? j)
    where
    open Tools ((₄₊ j) VRel,_===_)
    step : (x : Dec (a ≤ j)) → placeAt (posOf x) (GapD₂ (ps j a) (CZ ↑)) ≈ on2 CZ (₂₊ j)
    step (yes q) = ⊥-elim (<⇒≱ p q)
    step (no _)  = trans (placeAt-cong (suc j) (gap-low j a (≤-trans (n≤1+n j) p)))
                         (placeAt-on2-hi CZ (suc j) (suc j) ≤-refl (≤-trans (n≤1+n _) (n≤1+n _)))

  gap-CZ : ∀ j a → a ≤ j → (₃₊ j) ⊢ GapD₂ (ps j a) (CZ ↑) ≈ on2 CZ (suc a)
  gap-CZ zero    zero    _  = refl
    where open Tools (3 VRel,_===_)
  gap-CZ zero    (suc a) ()
  gap-CZ (suc j) a       p  = step (a ≤? j)
    where
    open Tools ((₄₊ j) VRel,_===_)
    step : (x : Dec (a ≤ j)) → placeAt (posOf x) (GapD₂ (ps j a) (CZ ↑)) ≈ on2 CZ (suc a)
    step (yes q) = trans (placeAt-cong (₃₊ j) (gap-CZ j a q)) (placeAt-on2-top CZ (suc a) (s≤s (s≤s (s≤s q))))
    step (no q)  = Eq.subst (λ k → placeAt (suc j) (GapD₂ (ps j a) (CZ ↑)) ≈ on2 CZ (suc k)) (Eq.sym a≡)
                     (trans (placeAt-cong (suc j) (gap-low j a (≤-trans (n≤1+n j) (≰⇒> q))))
                            (placeAt-on2-hi CZ (suc j) (suc j) ≤-refl (≤-trans (n≤1+n _) (n≤1+n _))))
      where
      a≡ : a ≡ suc j
      a≡ = ≤-antisym p (≰⇒> q)

------------------------------------------------------------------------
-- At the full width

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

  h₂ : ℕ → Bits m → Circuit N
  h₂ a c = negsB (cols a c) • Λ□ (₂₊ m) • negsB (cols a c)

-- The canonical product merges to CZ on the wires a + 1, a + 2.
canonical₂ : ∀ a → a ≤ m → ∏ (allBits m) (h₂ a) ≈ on2 CZ (suc a)
canonical₂ a a≤m = begin
  ∏ (allBits m) (h₂ a)
    ≈⟨ ∏-cong (allBits m) (λ c → ≡→≈ (Eq.cong (λ v → negsB v • Λ□ (₂₊ m) • negsB v) (Eq.sym (VD-frame₂ a c)))) ⟩
  ∏ (allBits m) (λ c → negsB (VD₂ (ps m a) (reverse c) base) • Λ□ (₂₊ m) • negsB (VD₂ (ps m a) (reverse c) base))
    ≈⟨ merge-all₂ (ps m a) (Pos-ps m a) ≤-refl base ⟩
  GapD₂ (ps m a) (negsB base • Λ□ 2 • negsB base)
    ≈⟨ gap-cong₂ (ps m a) base-CZ ⟩
  GapD₂ (ps m a) (CZ ↑)
    ≈⟨ gap-CZ m a a≤m ⟩
  on2 CZ (suc a) ∎
  where
  base : Bits 3
  base = false ∷ true ∷ true ∷ []

------------------------------------------------------------------------
-- The factors and the frames

private
  flip-str₂ : ∀ p c → ₂₊ p ≤ N → str₂ {m} p c true true true ≡ flipAt (pairing p) (str₂ p c false true true)
  flip-str₂ zero    c _ = Eq.sym (flip-insert (₂₊ m) false (true ∷ true ∷ c) ≤-refl)
  flip-str₂ (suc p) c (s≤s (s≤s (s≤s p≤))) = Eq.sym
    (Eq.trans (flip-below p (₂₊ p) true (insertℕ (suc p) true (insertℕ p false c)) (s≤s (n≤1+n p)) (s≤s (s≤s p≤)))
              (Eq.cong (insertℕ (₂₊ p) true)
                (Eq.trans (flip-below p (suc p) true (insertℕ p false c) (n<1+n p) (s≤s p≤))
                          (Eq.cong (insertℕ (suc p) true) (flip-insert p false c p≤)))))

-- Each factor of E(CZ) decodes to the box on the pairing wire.
factor₂ : ∀ p → ₂₊ p ≤ N → ∀ c →
          (d ʷ) (zz (index N (str₂ p c false true true)) (index N (str₂ p c true true true)))
            ≈ boxF (sdS (pairing p)) (str₂ p c false true true)
factor₂ p p< c =
  Eq.subst (λ w → (d ʷ) (zz (index N (str₂ p c false true true)) (index N w)) ≈ boxF (sdS (pairing p)) (str₂ p c false true true))
           (Eq.sym (flip-str₂ p c p<))
           (factorG (pairing p) (pairing< p (≤-trans (n≤1+n _) p<)) (str₂ p c false true true))

-- The gate on the wires 0, 1: its pairing wire is the top one.
frame₀ : ∀ c → boxF (sdS (₂₊ m)) (str₂ 0 c false true true) ≈ pl (sdS (₂₊ m)) (h₂ 0 c)
frame₀ c = sym (pl-•₃ (sdS (₂₊ m)) s refl s)
  where
  s : pl (sdS (₂₊ m)) (negsB (cols 0 c)) ≈ negsB (str₂ 0 c false true true)
  s = sd-negsB (₂₊ m) false (true ∷ true ∷ c) ≤-refl

-- The gate on the wires p + 1, p + 2: its pairing wire is p.
frame₁ : ∀ p → p ≤ m → ∀ c → boxF (sdS p) (str₂ (suc p) c false true true) ≈ pl (sdS p) (h₂ p c)
frame₁ p p≤ c = sym (pl-•₃ (sdS p) s refl s)
  where
  swap : insertℕ p false (insertℕ (suc p) true (insertℕ p true c)) ≡ str₂ (suc p) c false true true
  swap = Eq.trans (insert-swap (suc p) p true false (insertℕ p true c) (n≤1+n p) (s≤s p≤))
                  (Eq.cong (insertℕ (₂₊ p) true) (insert-swap p p true false c ≤-refl p≤))
  s : pl (sdS p) (negsB (cols p c)) ≈ negsB (str₂ (suc p) c false true true)
  s = trans (sd-negsB p false (insertℕ (suc p) true (insertℕ p true c)) (≤-trans p≤ (≤-trans (n≤1+n m) (n≤1+n _))))
            (≡→≈ (Eq.cong negsB swap))

------------------------------------------------------------------------
-- Lemma 8.7 for CZ

lemmaCZ : ∀ p → ₂₊ p ≤ N → on2 CZ p ≈ (d ʷ) (E-CZ {m} p)
lemmaCZ zero p< = sym (begin
  (d ʷ) (E-CZ 0)
    ≈⟨ ≡→≈ (dʷ-∏ (allBits m) (λ c → zz (index N (str₂ 0 c false true true)) (index N (str₂ 0 c true true true)))) ⟩
  ∏ (allBits m) (λ c → (d ʷ) (zz (index N (str₂ 0 c false true true)) (index N (str₂ 0 c true true true))))
    ≈⟨ ∏-cong (allBits m) (λ c → trans (factor₂ 0 p< c) (frame₀ c)) ⟩
  ∏ (allBits m) (λ c → pl (sdS (₂₊ m)) (h₂ 0 c))
    ≈⟨ sym (pl-∏ (sdS (₂₊ m)) (allBits m) (h₂ 0)) ⟩
  pl (sdS (₂₊ m)) (∏ (allBits m) (h₂ 0))
    ≈⟨ pl-cong (sdS (₂₊ m)) (canonical₂ 0 z≤n) ⟩
  pl (sdS (₂₊ m)) (on2 CZ 0 ↑)
    ≈⟨ pl-sd-↑ (₂₊ m) (on2 CZ 0) ⟩
  placeAt (₂₊ m) (on2 CZ 0)
    ≈⟨ placeAt-on2-top CZ 0 (s≤s (s≤s z≤n)) ⟩
  on2 CZ 0 ∎)
lemmaCZ (suc p) p<@(s≤s (s≤s (s≤s p≤))) = sym (begin
  (d ʷ) (E-CZ (suc p))
    ≈⟨ ≡→≈ (dʷ-∏ (allBits m) (λ c → zz (index N (str₂ (suc p) c false true true)) (index N (str₂ (suc p) c true true true)))) ⟩
  ∏ (allBits m) (λ c → (d ʷ) (zz (index N (str₂ (suc p) c false true true)) (index N (str₂ (suc p) c true true true))))
    ≈⟨ ∏-cong (allBits m) (λ c → trans (factor₂ (suc p) p< c) (frame₁ p p≤ c)) ⟩
  ∏ (allBits m) (λ c → pl (sdS p) (h₂ p c))
    ≈⟨ sym (pl-∏ (sdS p) (allBits m) (h₂ p)) ⟩
  pl (sdS p) (∏ (allBits m) (h₂ p))
    ≈⟨ pl-cong (sdS p) (canonical₂ p p≤) ⟩
  pl (sdS p) (on2 CZ (suc p))
    ≈⟨ pl-sd-on2 CZ p (suc p) ≤-refl ⟩
  on2 CZ (suc p) ∎)

------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on the rules (36) and (37) of Figure 8, at every width from
-- five (Clément, Appendix E.5)
--
-- (36) and (37) write a Hadamard pair on an H-pattern — the codes A, A
-- with the wire h flipped, with q flipped and with both, A being 0
-- there — as the standard pair between the halves of a word of encoded
-- swaps and X gates (`Encoding.W₁`, `W₂`): the swap network brings the
-- two wires i < j of the pattern down to 0 and 1 keeping the others in
-- order, and the X gates negate the controls that are 1; W₁, for the
-- box on the lower wire, exchanges 0 and 1 once more.
--
-- Decoded, the left side is the multi-controlled H of the pattern
-- (HLetters.dH-pat), and on the right the encoded swaps decode to swaps
-- (DecSwap), the negations to X on those wires (Letter85's `Eneg`,
-- through Corollary A.5 and Eq65H's reading of them as a bit map) and
-- the standard pair to the gadget, the H gate with its H on 0 and its
-- box on 1, white above.  Both sides are then the canonical H gate
-- placed by a network and coloured (`mcH-col`).  A network is
-- determined by what it does to colourings (`swW`): read on the unit
-- strings that is its permutation (`perm-swW`), and a permutation
-- determines the network by the completeness of the symmetric
-- presentation (PermCalc.perm-≈).  The decoded swap network acts on
-- colourings as the inverse of the encoded one's bit map (`sw-ν←`,
-- Eq65H.Net.Φ→ and Φ←), which carries the wires i, j to 0, 1 and the
-- others in order (BitAlg.network); so the right side's network is
-- Definition 2.4's for the pattern (`net-37`, `net-36`), and it carries
-- the gadget's colouring — black on 0 1, the controls above — to the
-- pattern's (Net.N-ij, N-ji and round).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.Rule3637
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_ ; T ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Fin.Properties using (toℕ-injective ; toℕ<n)
open import Data.List using (List ; [] ; _∷_ ; reverse)
open import Data.List.Properties using (unfold-reverse ; reverse-involutive)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; _≤_ ; _≡ᵇ_ ; _<ᵇ_ ; _^_ ; s≤s ; z≤n)
open import Data.Nat.Properties
  using (≤-refl ; ≤-trans ; ≤-pred ; <-trans ; n≤1+n ; ≡ᵇ⇒≡ ; <⇒≱ ; <⇒≢)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using ([] ; _∷_) renaming (map to vmap)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; perm ; net-↑ ; perm-≈)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ ; insertℕ ; removeℕ ; flipℕ ; xorB)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
  using (lookup-insert ; lookup-insert-below ; remove-insert ; insert-swap)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (gray ; toBits ; index ; code ; index-code)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitAlg
  using (swapBits ; swap-invol ; swap-down ; run ; run-∷ʳ ; pairDn ; pairUp ; network ; zeros ;
         all-range↑ ; all-range↓ ; lookup-flip ; hpat-inv ; HPat ; module Flips)
  renaming (negs to negsBits)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Encoding
  using (∏ ; hh ; hhℕ ; E-swap ; range↑ ; range↓ ; ctrls ; swaps← ; swaps→ ; negations↑ ; negations↓ ;
         HH₀₁₃₂ ; W₁ ; W₂ ; hpat)
open import Examples.Groups.Real-Clifford+CH.MultiControlled
  using (Layout ; tgtWire ; hWire₀ ; hWire ; mcH ; conj₂ ; ΛH ; swapAt ; shiftDown ; shiftUp ; shiftDown₁ ; shiftUp₁)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d ; gadget ; layoutH ; gcode)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires
  using (negsB ; σAt ; sdS ; revS ; revS-↑ ; revS-sdS ; net-sdS ; net-suS ; net-σAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (_⇔_ ; combine ; col-col ; swG ; swW)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (revS² ; swW-lookup ; pl-col ; pl-pl)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl ; pl-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.HLetters
  using (dH-pat ; negs-layoutH ; tgtWire-layoutH ; hWire₀-layoutH ; setT-flips)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃ using (conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87All complete₂ complete₃ using (mergesₙ)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Free complete₂ complete₃ using (dA5)
open import Examples.Groups.Real-Clifford+CH.Lemma88.DecSwap complete₂ complete₃ using (dS)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Letter85 complete₂ complete₃
  using (Eneg ; hf-Eneg ; sp-Eneg ; dEneg ; dEX ; negsAt-negsB ; low-from ; flips ; flips-combine ; comb-cancel)
import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87Z as Lemma87Z
import Examples.Groups.Real-Clifford+CH.Lemma88.Easy as Easy
import Examples.Groups.Real-Clifford+CH.Lemma88.Invol as Invol
import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm as SignedPerm
import Examples.Groups.Real-Clifford+CH.Auxiliary.NetSP as NetSP
import Examples.Groups.Real-Clifford+CH.Auxiliary.NF as NF
import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq65H as Eq65H
import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens as LowGens

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Networks read on colourings

private
  swG² : ∀ (g : S.Gen n) (t : Bits n) → swG g (swG g t) ≡ t
  swG² (S.gate₀ ())
  swG² (S.gate₁ ())
  swG² (S.gate₂ S.σ-gate) (a ∷ b ∷ t) = Eq.refl
  swG² (g S.↥)            (a ∷ t)     = Eq.cong (a ∷_) (swG² g t)

-- A network read backwards undoes it.
swW-rev : ∀ (w : Word (S.Gen n)) (t : Bits n) → swW (revS w) (swW w t) ≡ t
swW-rev [ g ]ʷ  t = swG² g t
swW-rev ε       t = Eq.refl
swW-rev (u • v) t = Eq.trans (Eq.cong (swW (revS v)) (swW-rev u (swW v t))) (swW-rev v t)

swW-rev′ : ∀ (w : Word (S.Gen n)) (t : Bits n) → swW w (swW (revS w) t) ≡ t
swW-rev′ w t = Eq.subst (λ v → swW v (swW (revS w) t) ≡ t) (revS² w) (swW-rev (revS w) t)

-- One wire up.
swW-↑ : ∀ (w : Word (S.Gen n)) a (t : Bits n) → swW (w S.↑) (a ∷ t) ≡ a ∷ swW w t
swW-↑ [ g ]ʷ  a t = Eq.refl
swW-↑ ε       a t = Eq.refl
swW-↑ (u • v) a t = Eq.trans (Eq.cong (swW (u S.↑)) (swW-↑ v a t)) (swW-↑ u a (swW v t))

-- A swap is the exchange of two bits.
swW-σAt : ∀ i (t : Bits n) → swW (σAt {n} i) t ≡ swapBits i t
swW-σAt {zero}        zero    []          = Eq.refl
swW-σAt {zero}        (suc i) []          = Eq.refl
swW-σAt {suc zero}    zero    (a ∷ [])    = Eq.refl
swW-σAt {suc (suc n)} zero    (a ∷ b ∷ t) = Eq.refl
swW-σAt {suc zero}    (suc i) (a ∷ [])    = Eq.trans (swW-↑ (σAt {zero} i) a []) (Eq.cong (a ∷_) (swW-σAt i []))
swW-σAt {suc (suc n)} (suc i) (a ∷ t)     = Eq.trans (swW-↑ (σAt i) a t) (Eq.cong (a ∷_) (swW-σAt i t))

-- The network bringing wire q down to 0 inserts the colour of 0 at q.
swW-sdS : ∀ q x (v : Bits n) → q ≤ n → swW (sdS {suc n} q) (x ∷ v) ≡ insertℕ q x v
swW-sdS zero    x v       _       = Eq.refl
swW-sdS (suc q) x []      ()
swW-sdS (suc q) x (y ∷ v) (s≤s p) =
  Eq.trans (Eq.cong (swW (σAt q)) (swW-sdS q x (y ∷ v) (≤-trans p (n≤1+n _))))
    (Eq.trans (swW-σAt q (insertℕ q x (y ∷ v)))
              (Eq.trans (Eq.cong (swapBits q) (Eq.sym (swap-down q x (y ∷ v) p)))
                        (swap-invol q (insertℕ (suc q) x (y ∷ v)))))

-- A product of networks, read on colourings: the last factor first.
swW-∏ : ∀ {A : Set} (f : A → Word (S.Gen n)) (g : A → Bits n → Bits n) → (∀ a t → swW (f a) t ≡ g a t) →
        ∀ xs t → swW (∏ xs f) t ≡ run g (reverse xs) t
swW-∏ f g h []       t = Eq.refl
swW-∏ f g h (x ∷ xs) t =
  Eq.trans (h x (swW (∏ xs f) t))
    (Eq.trans (Eq.cong (g x) (swW-∏ f g h xs t))
      (Eq.sym (Eq.trans (Eq.cong (λ l → run g l t) (unfold-reverse x xs)) (run-∷ʳ g (reverse xs) x t))))

private
  ≡ᵇ-refl : ∀ i → (i ≡ᵇ i) ≡ true
  ≡ᵇ-refl zero    = Eq.refl
  ≡ᵇ-refl (suc i) = ≡ᵇ-refl i

  lookup-zeros : ∀ w k → lookupℕ w (zeros k) ≡ false
  lookup-zeros w       zero    = Eq.refl
  lookup-zeros zero    (suc k) = Eq.refl
  lookup-zeros (suc w) (suc k) = lookup-zeros w k

-- Read on the unit strings, the action on colourings is the permutation.
perm-swW : ∀ (u v : Word (S.Gen n)) → (∀ t → swW u t ≡ swW v t) → ∀ j → perm u ⟨$⟩ʳ j ≡ perm v ⟨$⟩ʳ j
perm-swW {n} u v h j = toℕ-injective (Eq.sym (≡ᵇ⇒≡ _ _ (Eq.subst T (Eq.sym e) tt)))
  where
  p : Fin n
  p = perm u ⟨$⟩ʳ j
  s : Bits n
  s = flipℕ (toℕ p) (zeros n)
  at : ∀ w → lookupℕ w s ≡ (w ≡ᵇ toℕ p)
  at w = Eq.trans (lookup-flip (toℕ p) w (zeros n) (toℕ<n p)) (Eq.cong (_xor (w ≡ᵇ toℕ p)) (lookup-zeros w n))
  e : (toℕ (perm v ⟨$⟩ʳ j) ≡ᵇ toℕ p) ≡ true
  e = Eq.trans (Eq.sym (at (toℕ (perm v ⟨$⟩ʳ j))))
        (Eq.trans (Eq.sym (swW-lookup v s j))
          (Eq.trans (Eq.cong (lookupℕ (toℕ j)) (Eq.sym (h s)))
            (Eq.trans (swW-lookup u s j) (Eq.trans (at (toℕ p)) (≡ᵇ-refl (toℕ p))))))

module _ {n : ℕ} where
  open Tools (n VRel,_===_)

  -- So a network is determined by its action on colourings.
  net-swW : ∀ (u v : Word (S.Gen n)) → (∀ t → swW u t ≡ swW v t) → n ⊢ net u ≈ net v
  net-swW u v h = perm-≈ {u = u} {v = v} (perm-swW u v h)

  pl-swW : ∀ (u v : Word (S.Gen n)) → (∀ t → swW u t ≡ swW v t) → ∀ g → n ⊢ pl u g ≈ pl v g
  pl-swW u v h g = cong (net-swW u v h) (back _ (net-swW (revS u) (revS v) h′))
    where
    h′ : ∀ t → swW (revS u) t ≡ swW (revS v) t
    h′ t = Eq.trans (Eq.cong (swW (revS u)) (Eq.trans (Eq.sym (swW-rev′ v t)) (Eq.sym (h (swW (revS v) t)))))
                    (swW-rev u (swW (revS v) t))

------------------------------------------------------------------------
-- Bits

private
  flipℕ≡ : ∀ p (x : Bits n) → flipℕ p x ≡ flipAt p x
  flipℕ≡ p       []      = Eq.refl
  flipℕ≡ zero    (b ∷ x) = Eq.refl
  flipℕ≡ (suc p) (b ∷ x) = Eq.cong (b ∷_) (flipℕ≡ p x)

  comb-not : ∀ (cs r : Bits n) → combine (vmap not cs) r ≡ xorB cs r
  comb-not []          []      = Eq.refl
  comb-not (true ∷ cs)  (b ∷ r) = Eq.cong (not b ∷_) (comb-not cs r)
  comb-not (false ∷ cs) (b ∷ r) = Eq.cong (b ∷_) (comb-not cs r)

  comb-zeros : ∀ (cs : Bits n) → combine (vmap not cs) (zeros n) ≡ cs
  comb-zeros []          = Eq.refl
  comb-zeros (true ∷ cs)  = Eq.cong (true ∷_) (comb-zeros cs)
  comb-zeros (false ∷ cs) = Eq.cong (false ∷_) (comb-zeros cs)

  gray-zeros : ∀ k → gray (toBits k 0) ≡ zeros k
  gray-zeros zero          = Eq.refl
  gray-zeros (suc zero)    = Eq.refl
  gray-zeros (suc (suc k)) = Eq.cong (false ∷_) (gray-zeros (suc k))

------------------------------------------------------------------------
-- At width 5 + k

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    m N : ℕ
    m = ₂₊ k
    N = ₃₊ m

    I : Set
    I = Fin (2 ^ N)

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

  open Tools (N VRel,_===_)
  open Easy m using (d-hh0132)
  open Invol (canonN k completes) complete₂ using (mcH-inv)
  open Lemma87Z (canonN k completes) (mergesₙ k completes) using (dʷ-∏ ; rev-invol)
  open SignedPerm m using (sp ; _≐_ ; ≐-trans ; ≐-sym)
  open NetSP m using (bm ; bm-cong)
  open NF m using (HFreeʷ)
  open Eq65H m using (hf-neg↑ ; hf-neg↓ ; module Net ; module Negs)
  open LowGens m using (i₀ ; i₁ ; i₂ ; i₃ ; gen-hh ; hh0132≡ ; i₀≢i₁ ; i₃≢i₂)

  private
    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    ΛH′ : Circuit N
    ΛH′ = ΛH (₁₊ m)

  ----------------------------------------------------------------------
  -- The multi-controlled H as a placed, coloured gate

  mcH-col : ∀ (G : Bits N) h q u → h < N → q < N → h ≢ q → lookupℕ h G ≡ false → lookupℕ q G ≡ false →
            (if h <ᵇ q then suc h else h) ≡ suc u →
            mcH (layoutH {m} G h q) ≈ col (flipAt h (flipAt q G)) (pl (sdS q • (sdS u S.↑)) ΛH′)
  mcH-col G h q u h< q< h≢q gh gq hw≡ = begin
    mcH L
      ≈⟨ ≡→≈ e-mcH ⟩
    negsB F • shiftDown q • shiftDown u ↑ • ΛH′ • shiftUp u ↑ • shiftUp q • negsB F
      ≈⟨ back _ (by-passoc (□ • □ • □ • □ • □ • □) ((□ • □) • □ • (□ • □) • □) Eq.refl) ⟩
    negsB F • (shiftDown q • shiftDown u ↑) • ΛH′ • (shiftUp u ↑ • shiftUp q) • negsB F
      ≈⟨ back _ (≡→≈ (Eq.sym (Eq.cong₂ (λ a b → a • ΛH′ • b • negsB F) nd nu))) ⟩
    negsB F • net σ • ΛH′ • net (revS σ) • negsB F
      ≈⟨ back _ (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl) ⟩
    col F (pl σ ΛH′) ∎
    where
    L : Layout N
    L = layoutH {m} G h q
    F : Bits N
    F = flipAt h (flipAt q G)
    σ : Word (S.Gen N)
    σ = sdS q • (sdS u S.↑)
    e-t : tgtWire L ≡ q
    e-t = tgtWire-layoutH h q G h≢q q<
    e-h : hWire L ≡ suc u
    e-h = Eq.trans (Eq.cong₂ (λ a b → if a <ᵇ b then suc a else a) (hWire₀-layoutH h q G h<) e-t) hw≡
    e-mcH : mcH L ≡ negsB F • shiftDown q • shiftDown u ↑ • ΛH′ • shiftUp u ↑ • shiftUp q • negsB F
    e-mcH =
      Eq.trans (Eq.cong (λ a → a • shiftDown (tgtWire L) • shiftDown₁ (hWire L) • ΛH′ • shiftUp₁ (hWire L) •
                                   shiftUp (tgtWire L) • a)
                        (Eq.trans (negs-layoutH h q G) (Eq.cong negsB (setT-flips G h q gh gq h≢q))))
      (Eq.trans (Eq.cong (λ t → negsB F • shiftDown t • shiftDown₁ (hWire L) • ΛH′ • shiftUp₁ (hWire L) •
                                  shiftUp t • negsB F) e-t)
                (Eq.cong (λ w → negsB F • shiftDown q • shiftDown₁ w • ΛH′ • shiftUp₁ w • shiftUp q • negsB F) e-h))
    nd : net σ ≡ shiftDown q • shiftDown u ↑
    nd = Eq.cong₂ _•_ (net-sdS q) (Eq.trans (net-↑ (sdS u)) (Eq.cong _↑ (net-sdS u)))
    nu : net (revS σ) ≡ shiftUp u ↑ • shiftUp q
    nu = Eq.cong₂ _•_ (Eq.trans (Eq.cong net (revS-↑ (sdS u)))
                                (Eq.trans (net-↑ (revS (sdS u))) (Eq.cong _↑ (Eq.trans (Eq.cong net (revS-sdS u)) (net-suS u)))))
                      (Eq.trans (Eq.cong net (revS-sdS q)) (net-suS q))

  -- The gadget: its H on 0, its box on 1, white above.
  private
    T₀ : Bits N
    T₀ = flipAt 0 (flipAt 1 (gcode {m} 0))

    σg : Word (S.Gen N)
    σg = sdS 1 • (sdS 0 S.↑)

    gadget-col : gadget {m} ≈ col T₀ (pl σg ΛH′)
    gadget-col = mcH-col (gcode 0) 0 1 0 (s≤s z≤n) (s≤s (s≤s z≤n)) (λ ()) Eq.refl Eq.refl Eq.refl

    gadget-rev : rev gadget ≈ gadget
    gadget-rev = rev-invol gadget (mcH-inv (layoutH {m} (gcode 0) 0 1))

    -- The standard pair decodes to the gadget.
    HH≡Λ : HH₀₁₃₂ {m} ≡ hhℕ {N} 0 1 3 2
    HH≡Λ = Eq.trans (Eq.sym (gen-hh i₀ i₁ i₃ i₂ i₀≢i₁ i₃≢i₂)) (Eq.sym hh0132≡)

    dHH : (d ʷ) (HH₀₁₃₂ {m}) ≈ col T₀ (pl σg ΛH′)
    dHH = trans (≡→≈ (Eq.trans (Eq.cong (d ʷ) HH≡Λ) d-hh0132)) (trans gadget-rev gadget-col)

  ----------------------------------------------------------------------
  -- The swap networks

  ν← ν→ : ℕ → ℕ → Word (S.Gen N)
  ν← i j = ∏ (range↓ (suc i) j) σAt • ∏ (range↓ 0 i) (λ t → σAt t • σAt (suc t))
  ν→ i j = ∏ (range↑ 0 i) (λ t → σAt (suc t) • σAt t) • ∏ (range↑ (suc i) j) σAt

  private
    net-∏ : ∀ {A : Set} (xs : List A) (f : A → Word (S.Gen N)) → net (∏ xs f) ≡ ∏ xs (λ a → net (f a))
    net-∏ []       f = Eq.refl
    net-∏ (x ∷ xs) f = Eq.cong (net (f x) •_) (net-∏ xs f)

    ∏-≡ : ∀ {A : Set} (xs : List A) {f g : A → Circuit N} → (∀ a → f a ≡ g a) → ∏ xs f ≡ ∏ xs g
    ∏-≡ []       e = Eq.refl
    ∏-≡ (x ∷ xs) e = Eq.cong₂ _•_ (e x) (∏-≡ xs e)

    ∏-All : ∀ {A : Set} {P : A → Set} (xs : List A) {f g : A → Circuit N} →
            All P xs → (∀ a → P a → f a ≈ g a) → ∏ xs f ≈ ∏ xs g
    ∏-All []       []       e = refl
    ∏-All (x ∷ xs) (p ∷ ps) e = cong (e x p) (∏-All xs ps e)

    net-pair : ∀ t → net (σAt {N} t • σAt (suc t)) ≡ swapAt t • swapAt (suc t)
    net-pair t = Eq.cong₂ _•_ (net-σAt t) (net-σAt (suc t))

    net-pair′ : ∀ t → net (σAt {N} (suc t) • σAt t) ≡ swapAt (suc t) • swapAt t
    net-pair′ t = Eq.cong₂ _•_ (net-σAt (suc t)) (net-σAt t)

  module Swaps (i j : ℕ) (i<j : i < j) (j<N : j < N) where

    private
      b₁ : ∀ t → suc i ≤ t → t < j → ₂₊ t ≤ N
      b₁ t _ t<j = ≤-trans (s≤s t<j) j<N

      b₀ : ∀ t → 0 ≤ t → t < i → (₂₊ t ≤ N) × (₂₊ (suc t) ≤ N)
      b₀ t _ t<i = ≤-trans (n≤1+n _) b , b
        where
        b : ₃₊ t ≤ N
        b = ≤-trans (s≤s (s≤s t<i)) (≤-trans (s≤s i<j) j<N)

      dpair : ∀ t → (₂₊ t ≤ N) × (₂₊ (suc t) ≤ N) → (d ʷ) (E-swap {m} t • E-swap (suc t)) ≈ swapAt t • swapAt (suc t)
      dpair t (p , p′) = cong (dS k below t p) (dS k below (suc t) p′)

      dpair′ : ∀ t → (₂₊ t ≤ N) × (₂₊ (suc t) ≤ N) → (d ʷ) (E-swap {m} (suc t) • E-swap t) ≈ swapAt (suc t) • swapAt t
      dpair′ t (p , p′) = cong (dS k below (suc t) p′) (dS k below t p)

    dsw← : (d ʷ) (swaps← {m} i j) ≈ net (ν← i j)
    dsw← = begin
      (d ʷ) (∏ (range↓ (suc i) j) (E-swap {m})) • (d ʷ) (∏ (range↓ 0 i) (λ t → E-swap {m} t • E-swap (suc t)))
        ≈⟨ ≡→≈ (Eq.cong₂ _•_ (dʷ-∏ (range↓ (suc i) j) (E-swap {m})) (dʷ-∏ (range↓ 0 i) (λ t → E-swap {m} t • E-swap (suc t)))) ⟩
      ∏ (range↓ (suc i) j) (λ t → (d ʷ) (E-swap {m} t)) • ∏ (range↓ 0 i) (λ t → (d ʷ) (E-swap {m} t • E-swap (suc t)))
        ≈⟨ cong (∏-All (range↓ (suc i) j) (all-range↓ (suc i) j b₁) (λ t p → dS k below t p))
                (∏-All (range↓ 0 i) (all-range↓ 0 i b₀) dpair) ⟩
      ∏ (range↓ (suc i) j) swapAt • ∏ (range↓ 0 i) (λ t → swapAt t • swapAt (suc t))
        ≈⟨ ≡→≈ (Eq.sym (Eq.cong₂ _•_ (Eq.trans (net-∏ (range↓ (suc i) j) σAt) (∏-≡ (range↓ (suc i) j) net-σAt))
                                     (Eq.trans (net-∏ (range↓ 0 i) (λ t → σAt t • σAt (suc t))) (∏-≡ (range↓ 0 i) net-pair)))) ⟩
      net (ν← i j) ∎

    dsw→ : (d ʷ) (swaps→ {m} i j) ≈ net (ν→ i j)
    dsw→ = begin
      (d ʷ) (∏ (range↑ 0 i) (λ t → E-swap {m} (suc t) • E-swap t)) • (d ʷ) (∏ (range↑ (suc i) j) (E-swap {m}))
        ≈⟨ ≡→≈ (Eq.cong₂ _•_ (dʷ-∏ (range↑ 0 i) (λ t → E-swap {m} (suc t) • E-swap t)) (dʷ-∏ (range↑ (suc i) j) (E-swap {m}))) ⟩
      ∏ (range↑ 0 i) (λ t → (d ʷ) (E-swap {m} (suc t) • E-swap t)) • ∏ (range↑ (suc i) j) (λ t → (d ʷ) (E-swap {m} t))
        ≈⟨ cong (∏-All (range↑ 0 i) (all-range↑ 0 i b₀) dpair′)
                (∏-All (range↑ (suc i) j) (all-range↑ (suc i) j b₁) (λ t p → dS k below t p)) ⟩
      ∏ (range↑ 0 i) (λ t → swapAt (suc t) • swapAt t) • ∏ (range↑ (suc i) j) swapAt
        ≈⟨ ≡→≈ (Eq.sym (Eq.cong₂ _•_ (Eq.trans (net-∏ (range↑ 0 i) (λ t → σAt (suc t) • σAt t)) (∏-≡ (range↑ 0 i) net-pair′))
                                     (Eq.trans (net-∏ (range↑ (suc i) j) σAt) (∏-≡ (range↑ (suc i) j) net-σAt)))) ⟩
      net (ν→ i j) ∎

    open Net i j i<j j<N using (Φ← ; Φ→ ; round ; N-ij ; N-ji)

    -- Read on colourings, the decoded network is the inverse of the
    -- encoded one's bit map, and the way back is the bit map itself.
    sw-ν← : ∀ t → swW (ν← i j) t ≡ Φ→ t
    sw-ν← t =
      Eq.trans (swW-∏ σAt swapBits swW-σAt (range↓ (suc i) j) (swW (∏ (range↓ 0 i) pr) t))
        (Eq.cong₂ (λ l y → run swapBits l y) (reverse-involutive (range↑ (suc i) j))
                  (Eq.trans (swW-∏ pr pairUp prσ (range↓ 0 i) t)
                            (Eq.cong (λ l → run pairUp l t) (reverse-involutive (range↑ 0 i)))))
      where
      pr : ℕ → Word (S.Gen N)
      pr t′ = σAt t′ • σAt (suc t′)
      prσ : ∀ a y → swW (pr a) y ≡ pairUp a y
      prσ a y = Eq.trans (swW-σAt a (swW (σAt (suc a)) y)) (Eq.cong (swapBits a) (swW-σAt (suc a) y))

    sw-ν→ : ∀ t → swW (ν→ i j) t ≡ Φ← t
    sw-ν→ t =
      Eq.trans (swW-∏ pr pairDn prσ (range↑ 0 i) (swW (∏ (range↑ (suc i) j) σAt) t))
        (Eq.cong (run pairDn (range↓ 0 i)) (swW-∏ σAt swapBits swW-σAt (range↑ (suc i) j) t))
      where
      pr : ℕ → Word (S.Gen N)
      pr t′ = σAt (suc t′) • σAt t′
      prσ : ∀ a y → swW (pr a) y ≡ pairDn a y
      prσ a y = Eq.trans (swW-σAt (suc a) (swW (σAt a) y)) (Eq.cong (swapBits (suc a)) (swW-σAt a y))

    -- The way back is the inverse network.
    back-rev : net (ν→ i j) ≈ net (revS (ν← i j))
    back-rev = net-swW (ν→ i j) (revS (ν← i j)) h
      where
      h : ∀ t → swW (ν→ i j) t ≡ swW (revS (ν← i j)) t
      h t = Eq.trans (sw-ν→ t)
              (Eq.sym (Eq.trans (Eq.cong (swW (revS (ν← i j))) (Eq.sym (Eq.trans (sw-ν← (Φ← t)) (round t))))
                                (swW-rev (ν← i j) (Φ← t))))

    private
      j≤ : j ≤ ₂₊ m
      j≤ = ≤-pred j<N

      i≤ : i ≤ ₁₊ m
      i≤ = ≤-pred (≤-trans i<j j≤)

    -- The bits x, y put back at i, j.
    ins : ∀ x y (s′ : Bits (₁₊ m)) → Φ→ (x ∷ y ∷ s′) ≡ insertℕ j y (insertℕ i x s′)
    ins x y s′ = Eq.trans (Eq.cong Φ→ (Eq.sym fwd)) (round Xb)
      where
      Xb : Bits N
      Xb = insertℕ j y (insertℕ i x s′)
      fwd : Φ← Xb ≡ x ∷ y ∷ s′
      fwd = Eq.trans (network i j Xb i<j j≤)
              (Eq.cong₂ _∷_ (Eq.trans (lookup-insert-below j i y (insertℕ i x s′) i<j j≤) (lookup-insert i x s′ i≤))
                (Eq.cong₂ _∷_ (lookup-insert j y (insertℕ i x s′) j≤)
                  (Eq.trans (Eq.cong (removeℕ i) (remove-insert j y (insertℕ i x s′) j≤)) (remove-insert i x s′ i≤))))

  ----------------------------------------------------------------------
  -- The negations

  -- X on the wires 2 … where the controls are 1.
  qn : Bits N → ℕ → ℕ → Bits N
  qn A i j = true ∷ true ∷ vmap not (ctrls {m} A i j)

  private
    spE : ∀ (q : Bits N) → sp (Eneg k below 0 q) ≐ bm (combine q)
    spE q = ≐-trans (sp-Eneg k below 0 q ≤-refl) (bm-cong (flips 0 q) (combine q) (flips-combine q))

    dEneg′ : ∀ (q : Bits N) → (d ʷ) (Eneg k below 0 q) ≈ negsB q
    dEneg′ q = trans (dEneg k below N 0 q (dEX k below) (low-from N 0 q (λ l l<N Nl → ⊥-elim (<⇒≱ l<N Nl))))
                     (negsAt-negsB q)

    -- Any Hadamard-free word with the bit map of the negations decodes to them.
    dneg : ∀ (q : Bits N) (w : Word (GenP N)) → HFreeʷ w → sp w ≐ bm (combine q) → (d ʷ) w ≈ negsB q
    dneg q w hw e = trans (dA5 k below hw (hf-Eneg k below 0 q) (≐-trans e (≐-sym (spE q)))) (dEneg′ q)

  module Negations (A : Bits N) (i j : ℕ) where
    open Negs A i j using (Ψ ; Ψ′ ; sp-neg↑ ; sp-neg↓ ; unneg)

    private
      ψ≡ : ∀ y → Ψ y ≡ combine (qn A i j) y
      ψ≡ (u ∷ v ∷ r) = Eq.trans (negsBits (ctrls {m} A i j) r u v)
                                (Eq.cong (λ z → u ∷ v ∷ z) (Eq.sym (comb-not (ctrls {m} A i j) r)))

      ψ′≡ : ∀ y → Ψ′ y ≡ combine (qn A i j) y
      ψ′≡ y = Eq.trans (Eq.cong Ψ′ (Eq.sym (Eq.trans (ψ≡ (combine (qn A i j) y)) (comb-cancel (qn A i j) y))))
                       (unneg (combine (qn A i j) y))

    dneg↑ : (d ʷ) (negations↑ {m} A i j) ≈ negsB (qn A i j)
    dneg↑ = dneg (qn A i j) (negations↑ A i j) (hf-neg↑ A i j) (≐-trans sp-neg↑ (bm-cong Ψ (combine (qn A i j)) ψ≡))

    dneg↓ : (d ʷ) (negations↓ {m} A i j) ≈ negsB (qn A i j)
    dneg↓ = dneg (qn A i j) (negations↓ A i j) (hf-neg↓ A i j) (≐-trans sp-neg↓ (bm-cong Ψ′ (combine (qn A i j)) ψ′≡))

    -- With the gadget's colours, the controls.
    c₀ : combine (qn A i j) T₀ ≡ true ∷ true ∷ ctrls {m} A i j
    c₀ = Eq.trans (Eq.cong (λ z → true ∷ true ∷ combine (vmap not (ctrls {m} A i j)) z) (gray-zeros (₃₊ k)))
                  (Eq.cong (λ z → true ∷ true ∷ z) (comb-zeros (ctrls {m} A i j)))

  ----------------------------------------------------------------------
  -- The left side: the multi-controlled H of the pattern

  private
    lt-true : ∀ a b → a < b → (a <ᵇ b) ≡ true
    lt-true zero    (suc b) _       = Eq.refl
    lt-true (suc a) (suc b) (s≤s p) = lt-true a b p

    ge-false : ∀ a b → b ≤ a → (a <ᵇ b) ≡ false
    ge-false a       zero    _       = Eq.refl
    ge-false (suc a) (suc b) (s≤s p) = ge-false a b p

    hh≡ : ∀ {a a′ b b′ c c′ e e′ : I} → a ≡ a′ → b ≡ b′ → c ≡ c′ → e ≡ e′ → hh {N} a b c e ≡ hh a′ b′ c′ e′
    hh≡ Eq.refl Eq.refl Eq.refl Eq.refl = Eq.refl

    lhs : ∀ (a b c e : I) pb pc → HPat (code N a) (code N b) (code N c) (code N e) pb pc → pb ≢ pc →
          (d ʷ) (hh {N} a b c e) ≈ mcH (layoutH {m} (code N a) pb pc)
    lhs a b c e pb pc Hp ne =
      trans (≡→≈ (Eq.trans (Eq.cong (d ʷ) eq) (dH-pat {m} A pb pc pb<n pc<n ne za zc)))
            (rev-invol (mcH (layoutH {m} A pb pc)) (mcH-inv (layoutH {m} A pb pc)))
      where
      open HPat Hp using (za ; zc)
      open Flips Hp using (pb<n ; pc<n ; b-flip ; c-flip ; d-flip)
      A : Bits N
      A = code N a
      eq : hh {N} a b c e ≡ hh (index N A) (index N (flipAt pb A)) (index N (flipAt pc A)) (index N (flipAt pb (flipAt pc A)))
      eq = hh≡ (Eq.sym (index-code N a))
               (Eq.trans (Eq.sym (index-code N b)) (Eq.cong (index N) (Eq.trans b-flip (flipℕ≡ pb A))))
               (Eq.trans (Eq.sym (index-code N c)) (Eq.cong (index N) (Eq.trans c-flip (flipℕ≡ pc A))))
               (Eq.trans (Eq.sym (index-code N e))
                  (Eq.cong (index N) (Eq.trans (d-flip ne)
                    (Eq.trans (flipℕ≡ pb (flipℕ pc A)) (Eq.cong (flipAt pb) (flipℕ≡ pc A))))))

  ----------------------------------------------------------------------
  -- (37): the H wire i below the box wire j

  e37 : ∀ (a b c e : I) pb pc → hpat (code N a) (code N b) (code N c) (code N e) ≡ just (pb , pc) → pb < pc →
        (d ʷ) (hh {N} a b c e) ≈ (d ʷ) (W₂ (code N a) pb pc)
  e37 a b c e pb pc hp lt = begin
    (d ʷ) (hh a b c e)
      ≈⟨ lhs a b c e pb pc Hp ne ⟩
    mcH (layoutH {m} A pb pc)
      ≈⟨ mcH-col A pb pc pb pb<n pc<n ne za zc (Eq.cong (λ x → if x then suc pb else pb) (lt-true pb pc lt)) ⟩
    col F (pl (sdS pc • (sdS pb S.↑)) ΛH′)
      ≈⟨ back _ (front _ (sym (pl-swW (ν← pb pc • σg) (sdS pc • (sdS pb S.↑)) frame ΛH′))) ⟩
    col F (pl (ν← pb pc • σg) ΛH′)
      ≈⟨ ≡→≈ (Eq.cong (λ s → col s (pl (ν← pb pc • σg) ΛH′)) (Eq.sym colour)) ⟩
    col (swW (ν← pb pc) C) (pl (ν← pb pc • σg) ΛH′)
      ≈⟨ back _ (front _ (sym (pl-pl (ν← pb pc) σg ΛH′))) ⟩
    col (swW (ν← pb pc) C) (pl (ν← pb pc) (pl σg ΛH′))
      ≈⟨ sym (pl-col (ν← pb pc) C (pl σg ΛH′)) ⟩
    pl (ν← pb pc) (col C (pl σg ΛH′))
      ≈⟨ pl-cong (ν← pb pc) (sym (col-col Q T₀ (pl σg ΛH′))) ⟩
    pl (ν← pb pc) (col Q (col T₀ (pl σg ΛH′)))
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl ⟩
    net (ν← pb pc) • negsB Q • col T₀ (pl σg ΛH′) • negsB Q • net (revS (ν← pb pc))
      ≈⟨ sym (cong SW.dsw← (cong NG.dneg↑ (cong dHH (cong NG.dneg↓ (trans SW.dsw→ SW.back-rev))))) ⟩
    (d ʷ) (W₂ A pb pc) ∎
    where
    Hp = hpat-inv (code N a) (code N b) (code N c) (code N e) pb pc hp
    open HPat Hp using (za ; zc)
    open Flips Hp using (pb<n ; pc<n)
    ne : pb ≢ pc
    ne = <⇒≢ lt
    A F Q C : Bits N
    A = code N a
    F = flipAt pb (flipAt pc A)
    Q = qn A pb pc
    C = combine Q T₀
    module SW = Swaps pb pc lt pc<n
    module NG = Negations A pb pc
    open Net pb pc lt pc<n using (Φ← ; Φ→ ; round ; N-ij)
    colour : swW (ν← pb pc) C ≡ F
    colour = Eq.trans (Eq.cong (swW (ν← pb pc)) NG.c₀)
               (Eq.trans (SW.sw-ν← _)
                 (Eq.trans (Eq.cong Φ→ (Eq.sym (N-ij A za zc)))
                   (Eq.trans (round _) (Eq.trans (flipℕ≡ pb (flipℕ pc A)) (Eq.cong (flipAt pb) (flipℕ≡ pc A))))))
    frame : ∀ t → swW (ν← pb pc • σg) t ≡ swW (sdS pc • (sdS pb S.↑)) t
    frame (s₀ ∷ s₁ ∷ s′) =
      Eq.trans (SW.sw-ν← (s₁ ∷ s₀ ∷ s′))
        (Eq.trans (SW.ins s₁ s₀ s′)
          (Eq.sym (Eq.trans (Eq.cong (swW (sdS pc))
                                     (Eq.trans (swW-↑ (sdS pb) s₀ (s₁ ∷ s′)) (Eq.cong (s₀ ∷_) (swW-sdS pb s₁ s′ pb≤))))
                            (swW-sdS pc s₀ (insertℕ pb s₁ s′) (≤-pred pc<n)))))
      where
      pb≤ : pb ≤ ₁₊ m
      pb≤ = ≤-pred (≤-trans lt (≤-pred pc<n))

  ----------------------------------------------------------------------
  -- (36): the box wire i below the H wire j

  e36 : ∀ (a b c e : I) pb pc → hpat (code N a) (code N b) (code N c) (code N e) ≡ just (pb , pc) → pc < pb →
        (d ʷ) (hh {N} a b c e) ≈ (d ʷ) (W₁ (code N a) pc pb)
  e36 a b c e zero    pc hp ()
  e36 a b c e (suc u) pc hp lt@(s≤s pc≤u) = begin
    (d ʷ) (hh a b c e)
      ≈⟨ lhs a b c e (suc u) pc Hp ne ⟩
    mcH (layoutH {m} A (suc u) pc)
      ≈⟨ mcH-col A (suc u) pc u pb<n pc<n ne za zc (Eq.cong (λ x → if x then suc (suc u) else suc u) (ge-false (suc u) pc (≤-trans pc≤u (n≤1+n u)))) ⟩
    col F (pl (sdS pc • (sdS u S.↑)) ΛH′)
      ≈⟨ back _ (front _ (sym (pl-swW (ν← pc (suc u) • σ₁) (sdS pc • (sdS u S.↑)) frame ΛH′))) ⟩
    col F (pl (ν← pc (suc u) • σ₁) ΛH′)
      ≈⟨ ≡→≈ (Eq.cong (λ s → col s (pl (ν← pc (suc u) • σ₁) ΛH′)) (Eq.sym colour)) ⟩
    col (swW (ν← pc (suc u)) C) (pl (ν← pc (suc u) • σ₁) ΛH′)
      ≈⟨ back _ (front _ (sym (pl-pl (ν← pc (suc u)) σ₁ ΛH′))) ⟩
    col (swW (ν← pc (suc u)) C) (pl (ν← pc (suc u)) (pl σ₁ ΛH′))
      ≈⟨ sym (pl-col (ν← pc (suc u)) C (pl σ₁ ΛH′)) ⟩
    pl (ν← pc (suc u)) (col C (pl σ₁ ΛH′))
      ≈⟨ pl-cong (ν← pc (suc u)) inner ⟩
    pl (ν← pc (suc u)) (Ex • (negsB Q • col T₀ (pl σg ΛH′) • negsB Q) • Ex)
      ≈⟨ by-passoc (□ • (□ • (□ • □ • □) • □) • □) (□ • □ • □ • □ • □ • □ • □) Eq.refl ⟩
    net (ν← pc (suc u)) • Ex • negsB Q • col T₀ (pl σg ΛH′) • negsB Q • Ex • net (revS (ν← pc (suc u)))
      ≈⟨ sym (cong SW.dsw← (cong (dS k below 0 two≤) (cong NG.dneg↑ (cong dHH (cong NG.dneg↓
                (cong (dS k below 0 two≤) (trans SW.dsw→ SW.back-rev))))))) ⟩
    (d ʷ) (W₁ A pc (suc u)) ∎
    where
    Hp = hpat-inv (code N a) (code N b) (code N c) (code N e) (suc u) pc hp
    open HPat Hp using (za ; zc)
    open Flips Hp using (pb<n ; pc<n)
    ne : suc u ≢ pc
    ne q′ = <⇒≢ lt (Eq.sym q′)
    two≤ : 2 ≤ N
    two≤ = s≤s (s≤s z≤n)
    A F Q C : Bits N
    A = code N a
    F = flipAt (suc u) (flipAt pc A)
    Q = qn A pc (suc u)
    C = combine Q T₀
    σ₁ : Word (S.Gen N)
    σ₁ = σAt 0 • σg
    module SW = Swaps pc (suc u) lt pb<n
    module NG = Negations A pc (suc u)
    open Net pc (suc u) lt pb<n using (Φ← ; Φ→ ; round ; N-ji)
    colour : swW (ν← pc (suc u)) C ≡ F
    colour = Eq.trans (Eq.cong (swW (ν← pc (suc u))) NG.c₀)
               (Eq.trans (SW.sw-ν← _)
                 (Eq.trans (Eq.cong Φ→ (Eq.sym (N-ji A zc za)))
                   (Eq.trans (round _) (Eq.trans (flipℕ≡ (suc u) (flipℕ pc A)) (Eq.cong (flipAt (suc u)) (flipℕ≡ pc A))))))
    frame : ∀ t → swW (ν← pc (suc u) • σ₁) t ≡ swW (sdS pc • (sdS u S.↑)) t
    frame (s₀ ∷ s₁ ∷ s′) =
      Eq.trans (SW.sw-ν← (s₀ ∷ s₁ ∷ s′))
        (Eq.trans (SW.ins s₀ s₁ s′)
          (Eq.sym (Eq.trans (Eq.cong (swW (sdS pc))
                                     (Eq.trans (swW-↑ (sdS u) s₀ (s₁ ∷ s′)) (Eq.cong (s₀ ∷_) (swW-sdS u s₁ s′ u≤))))
                   (Eq.trans (swW-sdS pc s₀ (insertℕ u s₁ s′) (≤-trans pc≤u (≤-trans u≤ (n≤1+n _))))
                             (insert-swap u pc s₁ s₀ s′ pc≤u u≤)))))
      where
      u≤ : u ≤ ₁₊ m
      u≤ = ≤-pred (≤-pred pb<n)
    -- The standard pair between the two encoded swaps of the wires 0 1.
    inner : col C (pl σ₁ ΛH′) ≈ Ex • (negsB Q • col T₀ (pl σg ΛH′) • negsB Q) • Ex
    inner = begin
      col C (pl σ₁ ΛH′)
        ≈⟨ back _ (front _ (sym (pl-pl (σAt 0) σg ΛH′))) ⟩
      col C (Ex • pl σg ΛH′ • Ex)
        ≈⟨ sym (col-col Q T₀ (Ex • pl σg ΛH′ • Ex)) ⟩
      col Q (col T₀ (Ex • pl σg ΛH′ • Ex))
        ≈⟨ back _ (front _ (conj-swap (sym (low-comm Ex (negsB (gray (toBits (₃₊ k) 0))))) (pl σg ΛH′))) ⟩
      col Q (Ex • col T₀ (pl σg ΛH′) • Ex)
        ≈⟨ conj-swap (sym (low-comm Ex (negsB (vmap not (ctrls {m} A pc (suc u)))))) (col T₀ (pl σg ΛH′)) ⟩
      Ex • (negsB Q • col T₀ (pl σg ΛH′) • negsB Q) • Ex ∎

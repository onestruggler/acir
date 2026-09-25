------------------------------------------------------------------------
-- Presentations of groups
--
-- An H letter on an H-pattern decodes to the multi-controlled H
--
-- For a bitstring G whose bits h ≠ q are both 0, the letter on the four
-- codes G, G + h, G + q, G + h + q (the bits h, q flipped or not) is an
-- H-pattern, so Definition 8.3 decodes it to the multi-controlled H with
-- its H on wire h, its box on wire q and the other bits of G as
-- controls (`dH-pat`; d reverses D).  That gate is read off its layout:
-- the negations are those of G with h and q set (`negs-layoutH`: neither
-- target is negated), the box wire is q (`tgtWire-layoutH`) and the H
-- wire h (`hWire₀-layoutH`).  The three come from one observation:
-- shifting the starting wire and both targets by one changes nothing
-- (`LH-shift`), and a target on wire 0 leaves a layout with one target.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.HLetters where

open import Data.Bool using (Bool ; true ; false ; not ; if_then_else_ ; _∧_ ; _∨_ ; _xor_)
open import Data.Bool.Properties using (not-involutive)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective) renaming (_≟_ to _≟F_)
open import Data.List using (List ; [] ; _∷_)
open import Data.Maybe using (just ; nothing)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _^_ ; _<_ ; s≤s ; z≤n ; _≡ᵇ_)
open import Data.Nat.Properties using (+-identityʳ ; +-suc ; <-cmp)
open import Data.Product using (_,_)
open import Data.Vec using (Vec ; [] ; _∷_ ; map)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using ([_]ʷ ; _ʷ)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.MultiControlled
  using (Slot ; ctrl ; tgt ; tgtH ; Layout ; negs ; tgtWire ; hWire₀ ; mcH)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP ; HH)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (index ; code ; code-index)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ ; diff ; diffFrom)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt ; flipAt-comm)
open import Examples.Groups.Real-Clifford+CH.Encoding using (hh ; hpat ; distinct4)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d ; dHH ; dHH₄ ; dHH₄-pat ; layoutH ; layoutHFrom)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Layouts using (layoutAt ; setT ; tgtWire-at ; negs-at)

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- Layouts with one target

-- Only a box, or only an H, from wire w.
lay□From layHFrom : ℕ → ℕ → Bits k → Layout k
lay□From w q []      = []
lay□From w q (b ∷ v) = (if w ≡ᵇ q then tgt else ctrl b) ∷ lay□From (suc w) q v
layHFrom w h []      = []
layHFrom w h (b ∷ v) = (if w ≡ᵇ h then tgtH else ctrl b) ∷ layHFrom (suc w) h v

private
  LH-shift : ∀ w h q (v : Bits k) → layoutHFrom (suc w) (suc h) (suc q) v ≡ layoutHFrom w h q v
  LH-shift w h q []      = Eq.refl
  LH-shift w h q (b ∷ v) =
    Eq.cong ((if w ≡ᵇ h then tgtH else if w ≡ᵇ q then tgt else ctrl b) ∷_) (LH-shift (suc w) h q v)

  -- The H below the starting wire, or the box.
  LH-h0 : ∀ w q (v : Bits k) → layoutHFrom (suc w) 0 q v ≡ lay□From (suc w) q v
  LH-h0 w q []      = Eq.refl
  LH-h0 w q (b ∷ v) = Eq.cong ((if suc w ≡ᵇ q then tgt else ctrl b) ∷_) (LH-h0 (suc w) q v)

  LH-q0 : ∀ w h (v : Bits k) → layoutHFrom (suc w) h 0 v ≡ layHFrom (suc w) h v
  LH-q0 w h []      = Eq.refl
  LH-q0 w h (b ∷ v) = Eq.cong ((if suc w ≡ᵇ h then tgtH else ctrl b) ∷_) (LH-q0 (suc w) h v)

  lay□-shift : ∀ w q (v : Bits k) → lay□From (suc w) (suc q) v ≡ lay□From w q v
  lay□-shift w q []      = Eq.refl
  lay□-shift w q (b ∷ v) = Eq.cong ((if w ≡ᵇ q then tgt else ctrl b) ∷_) (lay□-shift (suc w) q v)

  layH-shift : ∀ w h (v : Bits k) → layHFrom (suc w) (suc h) v ≡ layHFrom w h v
  layH-shift w h []      = Eq.refl
  layH-shift w h (b ∷ v) = Eq.cong ((if w ≡ᵇ h then tgtH else ctrl b) ∷_) (layH-shift (suc w) h v)

  lay□-past : ∀ w (v : Bits k) → lay□From (suc w) 0 v ≡ map ctrl v
  lay□-past w []      = Eq.refl
  lay□-past w (b ∷ v) = Eq.cong (ctrl b ∷_) (lay□-past (suc w) v)

  layH-past : ∀ w (v : Bits k) → layHFrom (suc w) 0 v ≡ map ctrl v
  layH-past w []      = Eq.refl
  layH-past w (b ∷ v) = Eq.cong (ctrl b ∷_) (layH-past (suc w) v)

  lay□-at : ∀ q (v : Bits k) → lay□From 0 q v ≡ layoutAt q v
  lay□-at q       []      = Eq.refl
  lay□-at zero    (b ∷ v) = Eq.cong (tgt ∷_) (lay□-past 0 v)
  lay□-at (suc q) (b ∷ v) = Eq.cong (ctrl b ∷_) (Eq.trans (lay□-shift 0 q v) (lay□-at q v))

------------------------------------------------------------------------
-- The negations, the box wire and the H wire

private
  negs-map : (s : Bits k) → negs (map ctrl s) ≡ negsB s
  negs-map []          = Eq.refl
  negs-map (false ∷ s) = Eq.cong (λ w → X • w ↑) (negs-map s)
  negs-map (true ∷ s)  = Eq.cong _↑ (negs-map s)

  ctrl-cons : ∀ b {L : Layout k} {M : Bits k} → negs L ≡ negsB M → negs (ctrl b ∷ L) ≡ negsB (b ∷ M)
  ctrl-cons false e = Eq.cong (λ w → X • w ↑) e
  ctrl-cons true  e = Eq.cong _↑ e

  negs-layH : ∀ h (v : Bits k) → negs (layHFrom 0 h v) ≡ negsB (setT h v)
  negs-layH h       []      = Eq.refl
  negs-layH zero    (b ∷ v) = Eq.cong _↑ (Eq.trans (Eq.cong negs (layH-past 0 v)) (negs-map v))
  negs-layH (suc h) (b ∷ v) = ctrl-cons b (Eq.trans (Eq.cong negs (layH-shift 0 h v)) (negs-layH h v))

  hWire₀-layH : ∀ h (v : Bits k) → h < k → hWire₀ (layHFrom 0 h v) ≡ h
  hWire₀-layH h       []      ()
  hWire₀-layH zero    (b ∷ v) _       = Eq.refl
  hWire₀-layH (suc h) (b ∷ v) (s≤s p) =
    Eq.cong suc (Eq.trans (Eq.cong hWire₀ (layH-shift 0 h v)) (hWire₀-layH h v p))

negs-layoutH : ∀ h q (v : Bits k) → negs (layoutHFrom 0 h q v) ≡ negsB (setT h (setT q v))
negs-layoutH h       q       []      = Eq.refl
negs-layoutH zero    zero    (b ∷ v) =
  Eq.cong _↑ (Eq.trans (Eq.cong negs (Eq.trans (LH-h0 0 0 v) (lay□-past 0 v))) (negs-map v))
negs-layoutH zero    (suc q) (b ∷ v) =
  Eq.cong _↑ (Eq.trans (Eq.cong negs (Eq.trans (LH-h0 0 (suc q) v) (Eq.trans (lay□-shift 0 q v) (lay□-at q v))))
                       (negs-at q v))
negs-layoutH (suc h) zero    (b ∷ v) =
  Eq.cong _↑ (Eq.trans (Eq.cong negs (Eq.trans (LH-q0 0 (suc h) v) (layH-shift 0 h v))) (negs-layH h v))
negs-layoutH (suc h) (suc q) (b ∷ v) =
  ctrl-cons b (Eq.trans (Eq.cong negs (LH-shift 0 h q v)) (negs-layoutH h q v))

tgtWire-layoutH : ∀ h q (v : Bits k) → h ≢ q → q < k → tgtWire (layoutHFrom 0 h q v) ≡ q
tgtWire-layoutH h       q       []      _   ()
tgtWire-layoutH zero    zero    (b ∷ v) h≢q _       = ⊥-elim (h≢q Eq.refl)
tgtWire-layoutH zero    (suc q) (b ∷ v) _   (s≤s p) =
  Eq.cong suc (Eq.trans (Eq.cong tgtWire (Eq.trans (LH-h0 0 (suc q) v) (Eq.trans (lay□-shift 0 q v) (lay□-at q v))))
                        (tgtWire-at q v p))
tgtWire-layoutH (suc h) zero    (b ∷ v) _   _       = Eq.refl
tgtWire-layoutH (suc h) (suc q) (b ∷ v) h≢q (s≤s p) =
  Eq.cong suc (Eq.trans (Eq.cong tgtWire (LH-shift 0 h q v)) (tgtWire-layoutH h q v (λ e → h≢q (Eq.cong suc e)) p))

hWire₀-layoutH : ∀ h q (v : Bits k) → h < k → hWire₀ (layoutHFrom 0 h q v) ≡ h
hWire₀-layoutH h       q       []      ()
hWire₀-layoutH zero    q       (b ∷ v) _       = Eq.refl
hWire₀-layoutH (suc h) zero    (b ∷ v) (s≤s p) =
  Eq.cong suc (Eq.trans (Eq.cong hWire₀ (Eq.trans (LH-q0 0 (suc h) v) (layH-shift 0 h v))) (hWire₀-layH h v p))
hWire₀-layoutH (suc h) (suc q) (b ∷ v) (s≤s p) =
  Eq.cong suc (Eq.trans (Eq.cong hWire₀ (LH-shift 0 h q v)) (hWire₀-layoutH h q v p))

------------------------------------------------------------------------
-- The H-pattern

private
  diff-self : ∀ w (v : Bits k) → diffFrom w v v ≡ []
  diff-self w []          = Eq.refl
  diff-self w (true ∷ v)  = diff-self (suc w) v
  diff-self w (false ∷ v) = diff-self (suc w) v

  diff-flip1 : ∀ w i (v : Bits k) → i < k → diffFrom w v (flipAt i v) ≡ (w + i) ∷ []
  diff-flip1 w i       []          ()
  diff-flip1 w zero    (true ∷ v)  _       = Eq.cong₂ _∷_ (Eq.sym (+-identityʳ w)) (diff-self (suc w) v)
  diff-flip1 w zero    (false ∷ v) _       = Eq.cong₂ _∷_ (Eq.sym (+-identityʳ w)) (diff-self (suc w) v)
  diff-flip1 w (suc i) (true ∷ v)  (s≤s p) = Eq.trans (diff-flip1 (suc w) i v p) (Eq.cong (_∷ []) (Eq.sym (+-suc w i)))
  diff-flip1 w (suc i) (false ∷ v) (s≤s p) = Eq.trans (diff-flip1 (suc w) i v p) (Eq.cong (_∷ []) (Eq.sym (+-suc w i)))

  diff-flip2 : ∀ w i j (v : Bits k) → i < j → j < k → diffFrom w v (flipAt i (flipAt j v)) ≡ (w + i) ∷ (w + j) ∷ []
  diff-flip2 w zero    zero    v           ()      _
  diff-flip2 w (suc i) zero    v           ()      _
  diff-flip2 w i       (suc j) []          _       ()
  diff-flip2 w zero    (suc j) (true ∷ v)  _       (s≤s p) =
    Eq.cong₂ _∷_ (Eq.sym (+-identityʳ w)) (Eq.trans (diff-flip1 (suc w) j v p) (Eq.cong (_∷ []) (Eq.sym (+-suc w j))))
  diff-flip2 w zero    (suc j) (false ∷ v) _       (s≤s p) =
    Eq.cong₂ _∷_ (Eq.sym (+-identityʳ w)) (Eq.trans (diff-flip1 (suc w) j v p) (Eq.cong (_∷ []) (Eq.sym (+-suc w j))))
  diff-flip2 w (suc i) (suc j) (true ∷ v)  (s≤s q) (s≤s p) =
    Eq.trans (diff-flip2 (suc w) i j v q p) (Eq.cong₂ (λ x y → x ∷ y ∷ []) (Eq.sym (+-suc w i)) (Eq.sym (+-suc w j)))
  diff-flip2 w (suc i) (suc j) (false ∷ v) (s≤s q) (s≤s p) =
    Eq.trans (diff-flip2 (suc w) i j v q p) (Eq.cong₂ (λ x y → x ∷ y ∷ []) (Eq.sym (+-suc w i)) (Eq.sym (+-suc w j)))

  ≡ᵇ-refl : ∀ x → (x ≡ᵇ x) ≡ true
  ≡ᵇ-refl zero    = Eq.refl
  ≡ᵇ-refl (suc x) = ≡ᵇ-refl x

  ≡ᵇ-≢ : ∀ x y → x ≢ y → (x ≡ᵇ y) ≡ false
  ≡ᵇ-≢ zero    zero    ne = ⊥-elim (ne Eq.refl)
  ≡ᵇ-≢ zero    (suc y) _  = Eq.refl
  ≡ᵇ-≢ (suc x) zero    _  = Eq.refl
  ≡ᵇ-≢ (suc x) (suc y) ne = ≡ᵇ-≢ x y (λ e → ne (Eq.cong suc e))

  hpat-eq : ∀ (a b c e : Bits k) pb pc q₁ q₂ → diff a b ≡ pb ∷ [] → diff a c ≡ pc ∷ [] → diff a e ≡ q₁ ∷ q₂ ∷ [] →
            hpat a b c e ≡ (if (((pb ≡ᵇ q₁) ∧ (pc ≡ᵇ q₂)) ∨ ((pb ≡ᵇ q₂) ∧ (pc ≡ᵇ q₁)))
                                ∧ not (lookupℕ pb a) ∧ not (lookupℕ pc a)
                            then just (pb , pc) else nothing)
  hpat-eq a b c e pb pc q₁ q₂ e₁ e₂ e₃ with diff a b | diff a c | diff a e
  hpat-eq a b c e pb pc q₁ q₂ Eq.refl Eq.refl Eq.refl | _ | _ | _ = Eq.refl

hpat-flips : ∀ (G : Bits k) h q → h < k → q < k → h ≢ q → lookupℕ h G ≡ false → lookupℕ q G ≡ false →
             hpat G (flipAt h G) (flipAt q G) (flipAt h (flipAt q G)) ≡ just (h , q)
hpat-flips G h q h< q< h≢q gh gq with <-cmp h q
... | tri< h<q _ _ =
  Eq.trans (hpat-eq G (flipAt h G) (flipAt q G) (flipAt h (flipAt q G)) h q h q
                    (diff-flip1 0 h G h<) (diff-flip1 0 q G q<) (diff-flip2 0 h q G h<q q<))
           (Eq.cong (λ x → if x then just (h , q) else nothing) cond)
  where
  cond : (((h ≡ᵇ h) ∧ (q ≡ᵇ q)) ∨ ((h ≡ᵇ q) ∧ (q ≡ᵇ h))) ∧ not (lookupℕ h G) ∧ not (lookupℕ q G) ≡ true
  cond rewrite ≡ᵇ-refl h | ≡ᵇ-refl q | gh | gq = Eq.refl
... | tri≈ _ e _ = ⊥-elim (h≢q e)
... | tri> _ _ q<h =
  Eq.trans (hpat-eq G (flipAt h G) (flipAt q G) (flipAt h (flipAt q G)) h q q h
                    (diff-flip1 0 h G h<) (diff-flip1 0 q G q<)
                    (Eq.trans (Eq.cong (diffFrom 0 G) (flipAt-comm h q G)) (diff-flip2 0 q h G q<h h<)))
           (Eq.cong (λ x → if x then just (h , q) else nothing) cond)
  where
  cond : (((h ≡ᵇ q) ∧ (q ≡ᵇ h)) ∨ ((h ≡ᵇ h) ∧ (q ≡ᵇ q))) ∧ not (lookupℕ h G) ∧ not (lookupℕ q G) ≡ true
  cond rewrite ≡ᵇ-≢ h q h≢q | ≡ᵇ-refl h | ≡ᵇ-refl q | gh | gq = Eq.refl

------------------------------------------------------------------------
-- The four codes are distinct

private
  lf-same : ∀ i (v : Bits k) → i < k → lookupℕ i (flipAt i v) ≡ not (lookupℕ i v)
  lf-same i       []      ()
  lf-same zero    (b ∷ v) _       = Eq.refl
  lf-same (suc i) (b ∷ v) (s≤s p) = lf-same i v p

  lf-other : ∀ i j (v : Bits k) → i ≢ j → lookupℕ j (flipAt i v) ≡ lookupℕ j v
  lf-other i       j       []      _  = Eq.refl
  lf-other zero    zero    (b ∷ v) ne = ⊥-elim (ne Eq.refl)
  lf-other zero    (suc j) (b ∷ v) _  = Eq.refl
  lf-other (suc i) zero    (b ∷ v) _  = Eq.refl
  lf-other (suc i) (suc j) (b ∷ v) ne = lf-other i j v (λ e → ne (Eq.cong suc e))

  b≢not : ∀ b → b ≢ not b
  b≢not true  ()
  b≢not false ()

  setT-flip : ∀ i (v : Bits k) → lookupℕ i v ≡ false → setT i v ≡ flipAt i v
  setT-flip i       []          _  = Eq.refl
  setT-flip zero    (false ∷ v) _  = Eq.refl
  setT-flip zero    (true ∷ v)  ()
  setT-flip (suc i) (b ∷ v)     e  = Eq.cong (b ∷_) (setT-flip i v e)

  distinct4-true : ∀ a b c e → (a ≡ᵇ b) ≡ false → (a ≡ᵇ c) ≡ false → (a ≡ᵇ e) ≡ false →
                   (b ≡ᵇ c) ≡ false → (b ≡ᵇ e) ≡ false → (c ≡ᵇ e) ≡ false →
                   not (a ≡ᵇ b) ∧ not (a ≡ᵇ c) ∧ not (a ≡ᵇ e) ∧ not (b ≡ᵇ c) ∧ not (b ≡ᵇ e) ∧ not (c ≡ᵇ e) ≡ true
  distinct4-true a b c e e₁ e₂ e₃ e₄ e₅ e₆ rewrite e₁ | e₂ | e₃ | e₄ | e₅ | e₆ = Eq.refl

-- Setting two bits that are 0 is flipping them.
setT-flips : ∀ (G : Bits k) h q → lookupℕ h G ≡ false → lookupℕ q G ≡ false → h ≢ q →
             setT h (setT q G) ≡ flipAt h (flipAt q G)
setT-flips G h q gh gq h≢q =
  Eq.trans (Eq.cong (setT h) (setT-flip q G gq))
           (setT-flip h (flipAt q G) (Eq.trans (lf-other q h G (λ e → h≢q (Eq.sym e))) gh))

------------------------------------------------------------------------
-- The letter

module _ {m : ℕ} where
  private
    N : ℕ
    N = ₃₊ m

    idx : Bits N → Fin (2 ^ N)
    idx = index N

    -- Two codes differing at a bit have different indices.
    idx-ne : ∀ (x y : Bits N) i → lookupℕ i y ≡ not (lookupℕ i x) → (toℕ (idx x) ≡ᵇ toℕ (idx y)) ≡ false
    idx-ne x y i e = ≡ᵇ-≢ (toℕ (idx x)) (toℕ (idx y)) λ t →
      b≢not (lookupℕ i x) (Eq.trans (Eq.cong (lookupℕ i) (x≡y (toℕ-injective t))) e)
      where
      x≡y : idx x ≡ idx y → x ≡ y
      x≡y eq = Eq.trans (Eq.sym (code-index N x)) (Eq.trans (Eq.cong (code N) eq) (code-index N y))

    ne-Fin : ∀ {a b : Fin (2 ^ N)} → (toℕ a ≡ᵇ toℕ b) ≡ false → a ≢ b
    ne-Fin {a} e Eq.refl = t≢f (Eq.trans (Eq.sym (≡ᵇ-refl (toℕ a))) e)
      where
      t≢f : true ≢ false
      t≢f ()

    gen-hh : ∀ (a b c e : Fin (2 ^ N)) (ab : a ≢ b) (ce : c ≢ e) → [ HH {N} a b c e ab ce ]ʷ ≡ hh {N} a b c e
    gen-hh a b c e ab ce with a ≟F b | c ≟F e
    ... | yes eq | _      = ⊥-elim (ab eq)
    ... | no  _  | yes eq = ⊥-elim (ce eq)
    ... | no  _  | no  _  = Eq.refl

    dHH-true : ∀ a b c e → distinct4 a b c e ≡ true → dHH {m} a b c e ≡ dHH₄ a b c e
    dHH-true a b c e t = Eq.cong (λ x → if x then dHH₄ {m} a b c e else _) t

  dH-pat : ∀ (G : Bits N) h q → h < N → q < N → h ≢ q → lookupℕ h G ≡ false → lookupℕ q G ≡ false →
           (d ʷ) (hh (idx G) (idx (flipAt h G)) (idx (flipAt q G)) (idx (flipAt h (flipAt q G))))
             ≡ rev (mcH (layoutH {m} G h q))
  dH-pat G h q h< q< h≢q gh gq =
    Eq.trans (Eq.cong (d ʷ) (Eq.sym (gen-hh A B C D (ne-Fin AB) (ne-Fin CD))))
             (Eq.cong rev (Eq.trans (dHH-true (toℕ A) (toℕ B) (toℕ C) (toℕ D) dist)
                           (Eq.trans (dHH₄-pat (toℕ A) (toℕ B) (toℕ C) (toℕ D) h q pat)
                                     (Eq.cong (λ x → mcH (layoutH x h q)) (code-index N G)))))
    where
    Gh Gq Ghq : Bits N
    Gh  = flipAt h G
    Gq  = flipAt q G
    Ghq = flipAt h (flipAt q G)
    A B C D : Fin (2 ^ N)
    A = idx G
    B = idx Gh
    C = idx Gq
    D = idx Ghq
    q≢h : q ≢ h
    q≢h e = h≢q (Eq.sym e)

    -- The bits that tell them apart: h for every pair but B, D, which
    -- differ at q.
    AB : (toℕ A ≡ᵇ toℕ B) ≡ false
    AB = idx-ne G Gh h (lf-same h G h<)
    AC : (toℕ A ≡ᵇ toℕ C) ≡ false
    AC = idx-ne G Gq q (lf-same q G q<)
    AD : (toℕ A ≡ᵇ toℕ D) ≡ false
    AD = idx-ne G Ghq h (Eq.trans (lf-same h Gq h<) (Eq.cong not (lf-other q h G q≢h)))
    BC : (toℕ B ≡ᵇ toℕ C) ≡ false
    BC = idx-ne Gh Gq h (Eq.trans (lf-other q h G q≢h)
           (Eq.trans (Eq.sym (not-involutive (lookupℕ h G))) (Eq.cong not (Eq.sym (lf-same h G h<)))))
    BD : (toℕ B ≡ᵇ toℕ D) ≡ false
    BD = idx-ne Gh Ghq q (Eq.trans (lf-other h q Gq h≢q)
           (Eq.trans (lf-same q G q<) (Eq.cong not (Eq.sym (lf-other h q G h≢q)))))
    CD : (toℕ C ≡ᵇ toℕ D) ≡ false
    CD = idx-ne Gq Ghq h (lf-same h Gq h<)

    dist : distinct4 (toℕ A) (toℕ B) (toℕ C) (toℕ D) ≡ true
    dist = distinct4-true (toℕ A) (toℕ B) (toℕ C) (toℕ D) AB AC AD BC BD CD

    pat : hpat (code N A) (code N B) (code N C) (code N D) ≡ just (h , q)
    pat = Eq.subst (λ x → hpat x (code N B) (code N C) (code N D) ≡ just (h , q)) (Eq.sym (code-index N G))
            (Eq.subst (λ x → hpat G x (code N C) (code N D) ≡ just (h , q)) (Eq.sym (code-index N Gh))
              (Eq.subst (λ x → hpat G Gh x (code N D) ≡ just (h , q)) (Eq.sym (code-index N Gq))
                (Eq.subst (λ x → hpat G Gh Gq x ≡ just (h , q)) (Eq.sym (code-index N Ghq))
                  (hpat-flips G h q h< q< h≢q gh gq))))

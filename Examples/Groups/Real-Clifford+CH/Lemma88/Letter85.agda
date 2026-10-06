------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.5 by Corollary A.5, and the encoded X decoded on every wire
-- (Clément, Lemma 8.5 and the case of X in the proof of Lemma 8.6,
-- Appendices E.3 and E.4)
--
-- At width 5 + k.  Lemma 8.5: a mixed letter (−1)_[a] X_[a,b] on two
-- codes that differ at the wire t decodes to one rotation on t — XZ if
-- the sign is on the code with a 1 at t, ZX otherwise — the other bits
-- of the code as its controls, placed by the network bringing t to wire
-- 0 (`lemma85`).  Definition 8.3 gives that outright when a and b are
-- consecutive (LetterG's `letterG`); the paper walks the Gray code
-- otherwise (Appendix E.3).  Here Corollary A.5, decoded (`Free.dA5`),
-- does the walking.  In binary, the index with the bits below t set and
-- the bit t cleared (`low1`) is the lower of two consecutive indices
-- whose codes differ at t and agree with the given ones above t
-- (`gray-low1`); so the letter has the signed permutation of theirs
-- conjugated by the encoded X on the wires below t where the codes
-- differ (`Eneg`, a bit map: `sp-Eneg`), and its decoding is their
-- rotation recoloured there — given the encoded X decoded on the wires
-- below t.  Whether the sign falls on the lower or the upper of the two
-- decides between Definition 8.3's two consecutive cases, as in Lemma
-- 8.4's proof.
--
-- E-X w is E-Z w and one such letter for every context of the other
-- wires, the XZ on w coloured by the context.  In the frame of the
-- network bringing w to wire 0 they merge (DecX.mergeN), so E-X w
-- decodes to X on wire w, by induction on w (`dEX`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.Letter85 where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_)
open import Data.Bool.Properties using () renaming (_≟_ to _≟ᵇ_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; _≤_ ; _+_ ; _^_ ; s≤s ; z≤n ; _≤?_)
open import Data.Nat.Properties
  using (≤-refl ; ≤-trans ; ≤-pred ; n≤1+n ; +-suc ; +-identityʳ ; ≰⇒> ; m≤m+n ; n<1+n ; m≤n⇒m<n∨m≡n ; <⇒≢)
open import Data.Product using (_×_ ; _,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using ([] ; _∷_ ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; ε ; _•_ ; _ʷ)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Presentation.GroupLike using (module Group-Lemmas)
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; Z²)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev≈⁻¹)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; lookupℕ ; insertℕ ; flipℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas using (lookup-insert)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray
  using (toBits ; fromBits ; gray ; ungray ; index ; code ; index-injective ; toBits-fromBits ; fromBits<2^n ; gray-ungray)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt ; compl ; firstZero ; lt-compl ; flipAt-invol)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏ ; zx ; E-X ; E-Z)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Layout ; tgtWire ; Xat ; mc±XZ ; mc±ZX ; conj₁)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d ; dZX ; βof ; layout□ ; gcode ; slot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; sdS ; sd-target ; sd-negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (_⇔_ ; combine ; col-col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place ; combine-lookup ; ⇔-same)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl ; pl-cong ; pl-• ; pl-•₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Layouts using (layoutAt ; setT ; zip-flip ; tgtWire-at)
open import Examples.Groups.Real-Clifford+CH.GeneralN.OneWire using (on1 ; on1-net)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot ; mc±XZ-rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.MergeGen using (∏-cong)
open import Examples.Groups.Real-Clifford+CH.Lemma88.Kit using (Kit)
open import Examples.Groups.Real-Clifford+CH.Lemma88.GrayWitness using (tgt ; tgt< ; gstep ; lookup-flip-same ; lookup-flip-other)
import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma87Z as Lemma87Z
import Examples.Groups.Real-Clifford+CH.Lemma88.Easy as Easy
import Examples.Groups.Real-Clifford+CH.Lemma88.LetterG as LetterG
import Examples.Groups.Real-Clifford+CH.Lemma88.FreeGen as FreeGen
import Examples.Groups.Real-Clifford+CH.Lemma88.MergeKit as MergeKit
import Examples.Groups.Real-Clifford+CH.Lemma88.Invol as Invol
import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm as SignedPerm
import Examples.Groups.Real-Clifford+CH.Auxiliary.NetSP as NetSP
import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq65H as Eq65H
import Examples.Groups.Real-Clifford+CH.Auxiliary.NF as NF
import Examples.Groups.Real-Clifford+CH.Auxiliary.SigmaPerm as SigmaPerm
import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq75 as Eq75

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Bits

private
  ⇔-cancel : ∀ a b → (a ⇔ (a ⇔ b)) ≡ b
  ⇔-cancel true  b     = Eq.refl
  ⇔-cancel false true  = Eq.refl
  ⇔-cancel false false = Eq.refl

  ⇔-back : ∀ a b → ((a ⇔ b) ⇔ a) ≡ b
  ⇔-back true  true  = Eq.refl
  ⇔-back true  false = Eq.refl
  ⇔-back false true  = Eq.refl
  ⇔-back false false = Eq.refl

  ⇔-not : ∀ a b → (a ⇔ not b) ≡ not (a ⇔ b)
  ⇔-not true  b     = Eq.refl
  ⇔-not false true  = Eq.refl
  ⇔-not false false = Eq.refl

  ≢-not : ∀ a b → a ≢ b → not a ≡ b
  ≢-not true  true  ne = ⊥-elim (ne Eq.refl)
  ≢-not true  false _  = Eq.refl
  ≢-not false true  _  = Eq.refl
  ≢-not false false ne = ⊥-elim (ne Eq.refl)

  not-≢ : ∀ b → b ≢ not b
  not-≢ true  ()
  not-≢ false ()

-- The bits below t set and the bit t cleared: in binary, the lower of
-- two consecutive indices whose codes differ at t.
low1 : ℕ → Bits n → Bits n
low1 _       []      = []
low1 zero    (a ∷ s) = false ∷ s
low1 (suc t) (a ∷ s) = true ∷ low1 t s

low1-t : ∀ t (A : Bits n) → t < n → lookupℕ t (low1 t A) ≡ false
low1-t zero    (a ∷ s) _       = Eq.refl
low1-t (suc t) (a ∷ s) (s≤s p) = low1-t t s p

firstZero-low1 : ∀ t (A : Bits n) → t < n → firstZero (low1 t A) ≡ t
firstZero-low1 zero    (a ∷ s) _       = Eq.refl
firstZero-low1 (suc t) (a ∷ s) (s≤s p) = Eq.cong suc (firstZero-low1 t s p)

-- Above t its code is that of A.
gray-low1 : ∀ t (A : Bits n) i → t < i → lookupℕ i (gray (low1 t A)) ≡ lookupℕ i (gray A)
gray-low1 t       []      i       _       = Eq.refl
gray-low1 zero    (a ∷ s) zero    ()
gray-low1 zero    (a ∷ s) (suc i) _       = Eq.refl
gray-low1 (suc t) (a ∷ s) zero    ()
gray-low1 (suc t) (a ∷ s) (suc i) (s≤s p) = gray-low1 t s i p

-- Relative colourings.
comb-cancel : ∀ (x y : Bits n) → combine x (combine x y) ≡ y
comb-cancel []      []      = Eq.refl
comb-cancel (a ∷ x) (b ∷ y) = Eq.cong₂ _∷_ (⇔-cancel a b) (comb-cancel x y)

comb-back : ∀ (y g : Bits n) → combine (combine y g) y ≡ g
comb-back []      []      = Eq.refl
comb-back (b ∷ y) (a ∷ g) = Eq.cong₂ _∷_ (⇔-back b a) (comb-back y g)

combine-flip : ∀ t (q y : Bits n) → combine q (flipAt t y) ≡ flipAt t (combine q y)
combine-flip t       []      []      = Eq.refl
combine-flip zero    (a ∷ q) (b ∷ y) = Eq.cong (_∷ combine q y) (⇔-not a b)
combine-flip (suc t) (a ∷ q) (b ∷ y) = Eq.cong ((a ⇔ b) ∷_) (combine-flip t q y)

combine-setT : ∀ t (q y : Bits n) → lookupℕ t q ≡ true → combine q (setT t y) ≡ setT t (combine q y)
combine-setT t       []          []      _ = Eq.refl
combine-setT zero    (true ∷ q)  (b ∷ y) _ = Eq.refl
combine-setT zero    (false ∷ q) (b ∷ y) ()
combine-setT (suc t) (a ∷ q)     (b ∷ y) h = Eq.cong ((a ⇔ b) ∷_) (combine-setT t q y h)

setT-flip : ∀ t (y : Bits n) → setT t (flipAt t y) ≡ setT t y
setT-flip t       []      = Eq.refl
setT-flip zero    (b ∷ y) = Eq.refl
setT-flip (suc t) (b ∷ y) = Eq.cong (b ∷_) (setT-flip t y)

setT-insert : ∀ {j} i b (c : Bits j) → i ≤ j → setT i (insertℕ i b c) ≡ insertℕ i true c
setT-insert zero    b c       _       = Eq.refl
setT-insert (suc i) b (x ∷ c) (s≤s p) = Eq.cong (x ∷_) (setT-insert i b c p)

------------------------------------------------------------------------
-- X on the wires where a bitstring is false, from wire i on

-- Flipping those bits.
flips : ∀ {j} → ℕ → Bits j → Bits n → Bits n
flips i []          y = y
flips i (true ∷ s)  y = flips (suc i) s y
flips i (false ∷ s) y = flips (suc i) s (flipℕ i y)

flips-suc : ∀ {j} i (s : Bits j) b (y : Bits n) → flips (suc i) s (b ∷ y) ≡ b ∷ flips i s y
flips-suc i []          b y = Eq.refl
flips-suc i (true ∷ s)  b y = flips-suc (suc i) s b y
flips-suc i (false ∷ s) b y = flips-suc (suc i) s b (flipℕ i y)

-- From wire 0, it is the relative colouring.
flips-combine : ∀ (q y : Bits n) → flips 0 q y ≡ combine q y
flips-combine []          []      = Eq.refl
flips-combine (true ∷ q)  (b ∷ y) = Eq.trans (flips-suc 0 q b y) (Eq.cong (b ∷_) (flips-combine q y))
flips-combine (false ∷ q) (b ∷ y) =
  Eq.trans (flips-suc 0 q (true xor b) y) (Eq.cong ((true xor b) ∷_) (flips-combine q y))

-- The circuit.
negsAt : ∀ {j} → ℕ → Bits j → Circuit n
negsAt i []          = ε
negsAt i (true ∷ s)  = negsAt (suc i) s
negsAt i (false ∷ s) = Xat i • negsAt (suc i) s

negsAt-↑ : ∀ {j} i (s : Bits j) → negsAt {suc n} (suc i) s ≡ negsAt {n} i s ↑
negsAt-↑ i []          = Eq.refl
negsAt-↑ i (true ∷ s)  = negsAt-↑ (suc i) s
negsAt-↑ i (false ∷ s) = Eq.cong (Xat i ↑ •_) (negsAt-↑ (suc i) s)

negsAt-negsB : ∀ (q : Bits n) → n ⊢ negsAt 0 q ≈ negsB q
negsAt-negsB {zero}  []          = refl
  where open Tools (zero VRel,_===_)
negsAt-negsB {suc n} (true ∷ q)  = trans (≡→≈ (negsAt-↑ 0 q)) (lemma-cong↑ _ _ (negsAt-negsB q))
  where
  open Tools ((suc n) VRel,_===_)
  ≡→≈ : ∀ {a b : Circuit (suc n)} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl
negsAt-negsB {suc n} (false ∷ q) = back _ (trans (≡→≈ (negsAt-↑ 0 q)) (lemma-cong↑ _ _ (negsAt-negsB q)))
  where
  open Tools ((suc n) VRel,_===_)
  ≡→≈ : ∀ {a b : Circuit (suc n)} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

-- The false positions are below t.
Low : ∀ {j} → ℕ → ℕ → Bits j → Set
Low t i []          = ⊤
Low t i (true ∷ s)  = Low t (suc i) s
Low t i (false ∷ s) = i < t × Low t (suc i) s

low-from : ∀ {j} t i (s : Bits j) → (∀ l → l < j → t ≤ i + l → lookupℕ l s ≡ true) → Low t i s
low-from t i []          h = tt
low-from t i (true ∷ s)  h = low-from t (suc i) s (λ l l< tl → h (suc l) (s≤s l<) (Eq.subst (t ≤_) (Eq.sym (+-suc i l)) tl))
low-from t i (false ∷ s) h =
  i<t (t ≤? i) , low-from t (suc i) s (λ l l< tl → h (suc l) (s≤s l<) (Eq.subst (t ≤_) (Eq.sym (+-suc i l)) tl))
  where
  f≢t : false ≢ true
  f≢t ()
  i<t : Dec (t ≤ i) → i < t
  i<t (yes p) = ⊥-elim (f≢t (h 0 (s≤s z≤n) (Eq.subst (t ≤_) (Eq.sym (+-identityʳ i)) p)))
  i<t (no ¬p) = ≰⇒> ¬p

-- X on one wire.
on1-Xat : ∀ i → on1 {n} X i ≡ Xat i
on1-Xat {zero}  i       = Eq.refl
on1-Xat {suc n} zero    = Eq.refl
on1-Xat {suc n} (suc i) = Eq.cong _↑ (on1-Xat {n} i)

------------------------------------------------------------------------
-- At a width with its kit

module _ {m : ℕ} (kit : Kit m) where

  private
    N : ℕ
    N = ₃₊ m

  open Kit kit using (complete₂ ; canon ; merges ; tm ; d-ax)
  open Tools (N VRel,_===_)
  open Group-Lemmas (N VRel,_===_) grouplike using (inverseʳ-unique)
  open Easy m using (d-zx ; dZX-lo₁ ; dZX-hi₁ ; e33)
  open LetterG {m} using (letterG)
  open Invol canon complete₂ using (rot-inv)
  open FreeGen {m} d-ax using (dA5)
  open MergeKit {m} tm using (mergeN)
  open Lemma87Z canon merges using (lemmaZ ; dʷ-∏ ; pl-∏ ; flip-insert)
  open SignedPerm m
    using (sp ; _≐_ ; _⊙_ ; ≐-trans ; ≐-sym ; ≐-refl ; ⊙-cong ; L ; sp-zx ; sp-inj ; prm ; sgn ; prm≡ ; sgn≡ ;
           SWP-sym ; idSP ; NEG)
  open NetSP m using (bm ; bm-⊙ ; bm-id ; bm-cong ; sp-EX)
  open Eq65H m using (hf-EX)
  open NF m using (HFreeʷ ; cat ; nil)
  open SigmaPerm m using (hfree-zx)
  open Eq75 m using (L-conj)

  private
    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

  ----------------------------------------------------------------------
  -- The encoded X on the wires where s is false, from wire i on

  Eneg : ∀ {j} → ℕ → Bits j → Word (GenP N)
  Eneg i []          = ε
  Eneg i (true ∷ s)  = Eneg (suc i) s
  Eneg i (false ∷ s) = E-X {m} i • Eneg (suc i) s

  hf-Eneg : ∀ {j} i (s : Bits j) → HFreeʷ (Eneg i s)
  hf-Eneg i []          = nil
  hf-Eneg i (true ∷ s)  = hf-Eneg (suc i) s
  hf-Eneg i (false ∷ s) = cat (hf-EX i) (hf-Eneg (suc i) s)

  sp-Eneg : ∀ {j} i (s : Bits j) → i + j ≤ N → sp (Eneg i s) ≐ bm (flips i s)
  sp-Eneg i []          _ = ≐-sym (bm-id (λ y → y) (λ _ → Eq.refl))
  sp-Eneg {suc j} i (true ∷ s)  b = sp-Eneg (suc i) s (Eq.subst (_≤ N) (+-suc i j) b)
  sp-Eneg {suc j} i (false ∷ s) b =
    ≐-trans (⊙-cong (sp-EX i i<) (sp-Eneg (suc i) s b′)) (bm-⊙ (flipℕ i) (flips (suc i) s))
    where
    b′ : suc i + j ≤ N
    b′ = Eq.subst (_≤ N) (+-suc i j) b
    i< : i < N
    i< = ≤-trans (s≤s (m≤m+n i j)) b′

  dEneg : ∀ {j} t i (s : Bits j) → (∀ w → w < t → (d ʷ) (E-X {m} w) ≈ Xat w) → Low t i s →
          (d ʷ) (Eneg i s) ≈ negsAt i s
  dEneg t i []          dx _          = refl
  dEneg t i (true ∷ s)  dx lo         = dEneg t (suc i) s dx lo
  dEneg t i (false ∷ s) dx (i<t , lo) = cong (dx i i<t) (dEneg t (suc i) s dx lo)

  ----------------------------------------------------------------------
  -- Decoded rotations reversed

  private
    zx-rot : ∀ β (L′ : Layout N) → mc±ZX β L′ ≡ conj₁ L′ (rot (not β))
    zx-rot true  L′ = Eq.refl
    zx-rot false L′ = Eq.refl

    revXZ : ∀ β (L′ : Layout N) → rev (mc±XZ β L′) ≈ mc±ZX β L′
    revXZ true  L′ = trans (rev≈⁻¹ (mc±XZ true L′)) (sym (inverseʳ-unique (rot-inv false L′)))
    revXZ false L′ = trans (rev≈⁻¹ (mc±XZ false L′)) (sym (inverseʳ-unique (rot-inv true L′)))

    revZX : ∀ β (L′ : Layout N) → rev (mc±ZX β L′) ≈ mc±XZ β L′
    revZX β L′ = trans (rev≈⁻¹ (mc±ZX β L′)) (sym (inverseʳ-unique (rot-inv β L′)))

    plI : ∀ {i i′} {s s′ : Bits N} → i ≡ i′ → s ≡ s′ → ∀ b → place (sdS i) s (rot b) ≡ place (sdS i′) s′ (rot b)
    plI Eq.refl Eq.refl b = Eq.refl

    plSB : ∀ i {s s′ : Bits N} {b b′} → s ≡ s′ → b ≡ b′ → place (sdS i) s (rot b) ≡ place (sdS i) s′ (rot b′)
    plSB i Eq.refl Eq.refl = Eq.refl

    plB : ∀ i (s : Bits N) {b b′} → b ≡ b′ → place (sdS i) s (rot b) ≡ place (sdS i) s (rot b′)
    plB i s Eq.refl = Eq.refl

    L≡ : ∀ {a a′ b b′ c c′} → a ≡ a′ → b ≡ b′ → c ≡ c′ → L a b c ≐ L a′ b′ c′
    L≡ Eq.refl Eq.refl Eq.refl = ≐-refl

  ----------------------------------------------------------------------
  -- Lemma 8.5

  lemma85 : ∀ t → t < N → (∀ w → w < t → (d ʷ) (E-X {m} w) ≈ Xat w) → (G : Bits N) →
            (d ʷ) (zx {N} (index N G) (index N G) (index N (flipAt t G)))
              ≈ place (sdS t) (setT t G) (rot (not (lookupℕ t G)))
  lemma85 t t<N dx G = go (lookupℕ t Y ≟ᵇ lookupℕ t G)
    where
    A B Y : Bits N
    A = ungray G
    B = low1 t A
    Y = gray B

    x : ℕ
    x = fromBits B

    tB : toBits N x ≡ B
    tB = toBits-fromBits B

    x<2 : x < 2 ^ N
    x<2 = fromBits<2^n B

    bnd : suc x < 2 ^ N
    bnd = ≤-trans (s≤s (lt-compl t B (low1-t t A t<N) t<N)) (fromBits<2^n (compl t B))

    tx : tgt {m} x ≡ t
    tx = Eq.trans (Eq.cong firstZero tB) (firstZero-low1 t A t<N)

    gx : gcode {m} x ≡ Y
    gx = Eq.cong gray tB

    -- The two consecutive indices.
    x₀ x₁ : Fin (2 ^ N)
    x₀ = fromℕ< x<2
    x₁ = fromℕ< bnd

    t₀ : toℕ x₀ ≡ x
    t₀ = toℕ-fromℕ< x<2
    t₁ : toℕ x₁ ≡ suc x
    t₁ = toℕ-fromℕ< bnd

    c₀ : code N x₀ ≡ Y
    c₀ = Eq.trans (Eq.cong (λ v → gray (toBits N v)) t₀) gx
    c₁ : code N x₁ ≡ flipAt t Y
    c₁ = Eq.trans (Eq.cong (λ v → gray (toBits N v)) t₁)
           (Eq.trans (gstep {m} x bnd) (Eq.trans (Eq.cong (λ i → flipAt i (gcode {m} x)) tx) (Eq.cong (flipAt t) gx)))

    x₀≢x₁ : x₀ ≢ x₁
    x₀≢x₁ e = <⇒≢ (n<1+n x) (Eq.trans (Eq.sym t₀) (Eq.trans (Eq.cong toℕ e) t₁))

    G≢ : index N G ≢ index N (flipAt t G)
    G≢ e = not-≢ (lookupℕ t G) (Eq.trans (Eq.cong (lookupℕ t) (index-injective N {G} {flipAt t G} e)) (lookup-flip-same {m = m} t G t<N))

    -- β of the lower index is its code's bit at t.
    βx : βof {m} x ≡ lookupℕ t Y
    βx = Eq.trans (Eq.cong (λ i → lookupℕ i (gcode {m} x))
                           (Eq.trans (Eq.cong tgtWire lay) (tgtWire-at (tgt {m} x) (gcode {m} x) (tgt< {m} x bnd))))
                  (Eq.cong₂ lookupℕ tx gx)
      where
      lay : layout□ {m} x ≡ layoutAt (tgt {m} x) (gcode {m} x)
      lay = Eq.trans (Eq.cong (zipWith slot (gcode {m} x)) (gstep {m} x bnd)) (zip-flip (tgt {m} x) (gcode {m} x) (tgt< {m} x bnd))

    -- The lower index's rotation.
    placed : ∀ b → conj₁ (layout□ {m} x) (rot b) ≈ place (sdS t) (setT t Y) (rot b)
    placed b = trans (letterG x bnd (rot b)) (≡→≈ (plI tx (Eq.cong₂ setT tx gx) b))

    -- Above t the codes agree.
    above : ∀ l → t < l → lookupℕ l Y ≡ lookupℕ l G
    above l tl = Eq.trans (gray-low1 t A l tl) (Eq.cong (lookupℕ l) (gray-ungray G))

    -- Conjugating by the encoded X where Y′ and G differ, which is
    -- below t when they agree at t.
    module Conj (Y′ : Bits N) (agree : ∀ l → l < N → t ≤ l → lookupℕ l Y′ ≡ lookupℕ l G) where

      q : Bits N
      q = combine Y′ G

      E : Word (GenP N)
      E = Eneg 0 q

      qY′ : combine q Y′ ≡ G
      qY′ = comb-back Y′ G

      qt : lookupℕ t q ≡ true
      qt = Eq.trans (combine-lookup t Y′ G t<N) (Eq.trans (Eq.cong (_⇔ lookupℕ t G) (agree t t<N ≤-refl)) (⇔-same (lookupℕ t G)))

      spE : sp E ≐ bm (combine q)
      spE = ≐-trans (sp-Eneg 0 q ≤-refl) (bm-cong (flips 0 q) (combine q) (flips-combine q))

      ff : sp E ⊙ sp E ≐ idSP
      ff = ≐-trans (⊙-cong spE spE) (≐-trans (bm-⊙ (combine q) (combine q)) (bm-id _ (comb-cancel q)))

      pE : ∀ z {g} → code N z ≡ g → prm (sp E) z ≡ index N (combine q g)
      pE z e = Eq.trans (prm≡ spE z) (Eq.cong (λ v → index N (combine q v)) e)

      sE : ∀ z z′ → sgn (sp E) z ≡ sgn (sp E) z′
      sE z z′ = Eq.trans (sgn≡ spE z) (Eq.sym (sgn≡ spE z′))

      dE : (d ʷ) E ≈ negsB q
      dE = trans (dEneg t 0 q dx (low-from t 0 q hi)) (negsAt-negsB q)
        where
        hi : ∀ l → l < N → t ≤ l → lookupℕ l q ≡ true
        hi l l<N tl = Eq.trans (combine-lookup l Y′ G l<N) (Eq.trans (Eq.cong (_⇔ lookupℕ l G) (agree l l<N tl)) (⇔-same (lookupℕ l G)))

      colour : ∀ b → negsB q • place (sdS t) (setT t Y′) (rot b) • negsB q ≈ place (sdS t) (setT t G) (rot b)
      colour b = trans (col-col q (setT t Y′) (pl (sdS t) (rot b)))
                       (≡→≈ (Eq.cong (λ s → col s (pl (sdS t) (rot b))) (Eq.trans (combine-setT t q Y′ qt) (Eq.cong (setT t) qY′))))

    go : Dec (lookupℕ t Y ≡ lookupℕ t G) →
         (d ʷ) (zx (index N G) (index N G) (index N (flipAt t G))) ≈ place (sdS t) (setT t G) (rot (not (lookupℕ t G)))
    -- The codes agree at t: the sign on the lower index.
    go (yes e) = begin
      (d ʷ) (zx (index N G) (index N G) (index N (flipAt t G)))
        ≈⟨ dA5 (hfree-zx (index N G) (index N G) (index N (flipAt t G))) (cat (hf-Eneg 0 q) (cat (hfree-zx x₀ x₀ x₁) (hf-Eneg 0 q))) spEq ⟩
      (d ʷ) E • (d ʷ) (zx x₀ x₀ x₁) • (d ʷ) E
        ≈⟨ cong dE (cong dlo dE) ⟩
      negsB q • place (sdS t) (setT t Y) (rot (not (lookupℕ t Y))) • negsB q
        ≈⟨ colour (not (lookupℕ t Y)) ⟩
      place (sdS t) (setT t G) (rot (not (lookupℕ t Y)))
        ≈⟨ ≡→≈ (plB t (setT t G) (Eq.cong not e)) ⟩
      place (sdS t) (setT t G) (rot (not (lookupℕ t G))) ∎
      where
      agreeY : ∀ l → l < N → t ≤ l → lookupℕ l Y ≡ lookupℕ l G
      agreeY l l<N tl with m≤n⇒m<n∨m≡n tl
      ... | inj₁ lt      = above l lt
      ... | inj₂ Eq.refl = e
      open Conj Y agreeY
      spEq : sp (zx (index N G) (index N G) (index N (flipAt t G))) ≐ sp (E • zx x₀ x₀ x₁ • E)
      spEq = ≐-trans (sp-zx _ _ _ G≢)
               (≐-sym (≐-trans (⊙-cong (≐-refl {sp E}) (⊙-cong (sp-zx x₀ x₀ x₁ x₀≢x₁) (≐-refl {sp E})))
                        (≐-trans (L-conj (sp E) (sp-inj E) ff x₀ x₀ x₁ (sE x₀ x₁))
                                 (L≡ p₀ p₀ p₁))))
        where
        p₀ : prm (sp E) x₀ ≡ index N G
        p₀ = Eq.trans (pE x₀ c₀) (Eq.cong (index N) qY′)
        p₁ : prm (sp E) x₁ ≡ index N (flipAt t G)
        p₁ = Eq.trans (pE x₁ c₁) (Eq.cong (index N) (Eq.trans (combine-flip t q Y) (Eq.cong (flipAt t) qY′)))
      dlo : (d ʷ) (zx x₀ x₀ x₁) ≈ place (sdS t) (setT t Y) (rot (not (lookupℕ t Y)))
      dlo = begin
        (d ʷ) (zx x₀ x₀ x₁)
          ≈⟨ ≡→≈ (d-zx x₀ x₀ x₁ x₀≢x₁) ⟩
        rev (dZX (toℕ x₀) (toℕ x₀) (toℕ x₁))
          ≈⟨ ≡→≈ (Eq.cong₂ (λ a b → rev (dZX a a b)) t₀ t₁) ⟩
        rev (dZX x x (suc x))
          ≈⟨ ≡→≈ (Eq.cong rev (dZX-lo₁ x)) ⟩
        rev (mc±XZ (βof x) (layout□ x))
          ≈⟨ revXZ (βof x) (layout□ x) ⟩
        mc±ZX (βof x) (layout□ x)
          ≈⟨ ≡→≈ (zx-rot (βof x) (layout□ x)) ⟩
        conj₁ (layout□ x) (rot (not (βof x)))
          ≈⟨ placed (not (βof x)) ⟩
        place (sdS t) (setT t Y) (rot (not (βof x)))
          ≈⟨ ≡→≈ (plB t (setT t Y) (Eq.cong not βx)) ⟩
        place (sdS t) (setT t Y) (rot (not (lookupℕ t Y))) ∎
    -- They differ at t: the sign on the upper index.
    go (no ne) = begin
      (d ʷ) (zx (index N G) (index N G) (index N (flipAt t G)))
        ≈⟨ dA5 (hfree-zx (index N G) (index N G) (index N (flipAt t G))) (cat (hf-Eneg 0 q) (cat (hfree-zx x₁ x₀ x₁) (hf-Eneg 0 q))) spEq ⟩
      (d ʷ) E • (d ʷ) (zx x₁ x₀ x₁) • (d ʷ) E
        ≈⟨ cong dE (cong dhi dE) ⟩
      negsB q • place (sdS t) (setT t (flipAt t Y)) (rot (lookupℕ t Y)) • negsB q
        ≈⟨ colour (lookupℕ t Y) ⟩
      place (sdS t) (setT t G) (rot (lookupℕ t Y))
        ≈⟨ ≡→≈ (plB t (setT t G) (Eq.sym (≢-not′ ne))) ⟩
      place (sdS t) (setT t G) (rot (not (lookupℕ t G))) ∎
      where
      ≢-not′ : lookupℕ t Y ≢ lookupℕ t G → not (lookupℕ t G) ≡ lookupℕ t Y
      ≢-not′ ne′ = ≢-not (lookupℕ t G) (lookupℕ t Y) (λ q′ → ne′ (Eq.sym q′))
      agreeY : ∀ l → l < N → t ≤ l → lookupℕ l (flipAt t Y) ≡ lookupℕ l G
      agreeY l l<N tl with m≤n⇒m<n∨m≡n tl
      ... | inj₁ lt      = Eq.trans (lookup-flip-other {m = m} t l Y (λ q′ → <⇒≢ lt (Eq.sym q′))) (above l lt)
      ... | inj₂ Eq.refl = Eq.trans (lookup-flip-same {m = m} t Y t<N) (≢-not (lookupℕ t Y) (lookupℕ t G) ne)
      open Conj (flipAt t Y) agreeY
      spEq : sp (zx (index N G) (index N G) (index N (flipAt t G))) ≐ sp (E • zx x₁ x₀ x₁ • E)
      spEq = ≐-trans (sp-zx _ _ _ G≢)
               (≐-sym (≐-trans (⊙-cong (≐-refl {sp E}) (⊙-cong (sp-zx x₁ x₀ x₁ x₀≢x₁) (≐-refl {sp E})))
                        (≐-trans (L-conj (sp E) (sp-inj E) ff x₁ x₀ x₁ (sE x₀ x₁))
                        (≐-trans (L≡ p₁ p₀ p₁)
                                 (⊙-cong (≐-refl {NEG (index N G)}) (SWP-sym (index N (flipAt t G)) (index N G)))))))
        where
        p₁ : prm (sp E) x₁ ≡ index N G
        p₁ = Eq.trans (pE x₁ c₁) (Eq.cong (index N) qY′)
        p₀ : prm (sp E) x₀ ≡ index N (flipAt t G)
        p₀ = Eq.trans (pE x₀ c₀)
               (Eq.cong (index N) (Eq.trans (Eq.cong (combine q) (Eq.sym (flipAt-invol t Y)))
                                            (Eq.trans (combine-flip t q (flipAt t Y)) (Eq.cong (flipAt t) qY′))))
      dhi : (d ʷ) (zx x₁ x₀ x₁) ≈ place (sdS t) (setT t (flipAt t Y)) (rot (lookupℕ t Y))
      dhi = begin
        (d ʷ) (zx x₁ x₀ x₁)
          ≈⟨ ≡→≈ (d-zx x₁ x₀ x₁ x₀≢x₁) ⟩
        rev (dZX (toℕ x₁) (toℕ x₀) (toℕ x₁))
          ≈⟨ ≡→≈ (Eq.cong₂ (λ a b → rev (dZX b a b)) t₀ t₁) ⟩
        rev (dZX (suc x) x (suc x))
          ≈⟨ ≡→≈ (Eq.cong rev (dZX-hi₁ x)) ⟩
        rev (mc±ZX (βof x) (layout□ x))
          ≈⟨ revZX (βof x) (layout□ x) ⟩
        mc±XZ (βof x) (layout□ x)
          ≈⟨ ≡→≈ (mc±XZ-rot (βof x) (layout□ x)) ⟩
        conj₁ (layout□ x) (rot (βof x))
          ≈⟨ placed (βof x) ⟩
        place (sdS t) (setT t Y) (rot (βof x))
          ≈⟨ ≡→≈ (plSB t (Eq.sym (setT-flip t Y)) βx) ⟩
        place (sdS t) (setT t (flipAt t Y)) (rot (lookupℕ t Y)) ∎

  ----------------------------------------------------------------------
  -- E-X on every wire

  private
    ℓX : ℕ → Bits (₂₊ m) → Word (GenP N)
    ℓX w c = zx {N} (index N (insertℕ w true c)) (index N (insertℕ w false c)) (index N (insertℕ w true c))

    dec-ℓX : ∀ w → w < N → (∀ w′ → w′ < w → (d ʷ) (E-X {m} w′) ≈ Xat w′) → ∀ c →
             (d ʷ) (ℓX w c) ≈ pl (sdS w) (col (true ∷ c) (rot false))
    dec-ℓX w w<N dx c = begin
      (d ʷ) (zx (index N G) (index N (insertℕ w false c)) (index N G))
        ≈⟨ e33 (index N G) (index N (insertℕ w false c)) ⟩
      (d ʷ) (zx (index N G) (index N G) (index N (insertℕ w false c)))
        ≈⟨ ≡→≈ (Eq.cong (λ v → (d ʷ) (zx {N} (index N G) (index N G) (index N v))) (Eq.sym (flip-insert w true c w≤))) ⟩
      (d ʷ) (zx (index N G) (index N G) (index N (flipAt w G)))
        ≈⟨ lemma85 w w<N dx G ⟩
      place (sdS w) (setT w G) (rot (not (lookupℕ w G)))
        ≈⟨ ≡→≈ (Eq.cong₂ (λ s b → place (sdS w) s (rot (not b))) (setT-insert w true c w≤) (lookup-insert w true c w≤)) ⟩
      negsB G • pl (sdS w) (rot false) • negsB G
        ≈⟨ sym (pl-•₃ (sdS w) sN refl sN) ⟩
      pl (sdS w) (col (true ∷ c) (rot false)) ∎
      where
      G : Bits N
      G = insertℕ w true c
      w≤ : w ≤ ₂₊ m
      w≤ = ≤-pred w<N
      sN : pl (sdS w) (negsB (true ∷ c)) ≈ negsB G
      sN = sd-negsB w true c w≤

    dEX-step : ∀ w → w < N → (∀ w′ → w′ < w → (d ʷ) (E-X {m} w′) ≈ Xat w′) → (d ʷ) (E-X {m} w) ≈ Xat w
    dEX-step w w<N dx = begin
      (d ʷ) (E-Z w) • (d ʷ) (∏ (allBits (₂₊ m)) (ℓX w))
        ≈⟨ cong (sym (lemmaZ w w<N)) (≡→≈ (dʷ-∏ (allBits (₂₊ m)) (ℓX w))) ⟩
      on1 Z w • ∏ (allBits (₂₊ m)) (λ c → (d ʷ) (ℓX w c))
        ≈⟨ cong (sym (at-w Z)) (∏-cong (allBits (₂₊ m)) (dec-ℓX w w<N dx)) ⟩
      pl (sdS w) Z • ∏ (allBits (₂₊ m)) (λ c → pl (sdS w) (col (true ∷ c) (rot false)))
        ≈⟨ back _ (sym (pl-∏ (sdS w) (allBits (₂₊ m)) (λ c → col (true ∷ c) (rot false)))) ⟩
      pl (sdS w) Z • pl (sdS w) (∏ (allBits (₂₊ m)) (λ c → col (true ∷ c) (rot false)))
        ≈⟨ back _ (pl-cong (sdS w) (mergeN false)) ⟩
      pl (sdS w) Z • pl (sdS w) (Z • X)
        ≈⟨ sym (pl-• (sdS w) Z (Z • X)) ⟩
      pl (sdS w) (Z • Z • X)
        ≈⟨ pl-cong (sdS w) (trans (sym assoc) (trans (front _ Z²) left-unit)) ⟩
      pl (sdS w) X
        ≈⟨ at-w X ⟩
      on1 X w
        ≈⟨ ≡→≈ (on1-Xat w) ⟩
      Xat w ∎
      where
      wF : Fin N
      wF = fromℕ< w<N
      at-w : ∀ (g : Circuit 1) → pl (sdS w) (on1 g 0) ≈ on1 g w
      at-w g = Eq.subst (λ i → pl (sdS i) (on1 g 0) ≈ on1 g i) (toℕ-fromℕ< w<N)
                 (Eq.subst (λ f → pl (sdS (toℕ wF)) (on1 g (toℕ f)) ≈ on1 g (toℕ wF)) (sd-target wF)
                           (on1-net g (sdS (toℕ wF)) wF))

    dEX< : ∀ w → w ≤ N → ∀ w′ → w′ < w → (d ʷ) (E-X {m} w′) ≈ Xat w′
    dEX< zero    _ w′ ()
    dEX< (suc w) b w′ w′< = split (m≤n⇒m<n∨m≡n (≤-pred w′<))
      where
      split : w′ < w ⊎ w′ ≡ w → (d ʷ) (E-X {m} w′) ≈ Xat w′
      split (inj₁ lt) = dEX< w (≤-trans (n≤1+n w) b) w′ lt
      split (inj₂ e)  = Eq.subst (λ v → (d ʷ) (E-X {m} v) ≈ Xat v) (Eq.sym e)
                                 (dEX-step w b (dEX< w (≤-trans (n≤1+n w) b)))

  -- Lemma 8.7 for X, on every wire.
  dEX : ∀ w → w < N → (d ʷ) (E-X {m} w) ≈ Xat w
  dEX w w<N = dEX< (suc w) w<N w ≤-refl

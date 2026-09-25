------------------------------------------------------------------------
-- Presentations of groups
--
-- Two boxes commute, in any colours (Clément, Lemma D.13, Equations
-- (335) and (336))
--
-- At the canonical position: the box Λ on wire 0 controlled by all the
-- other wires commutes with any colouring of itself (`C335`), and with
-- any colouring of the box B₁ on wire 1 controlled by wire 0 and the
-- wires 2 … (`C336`) — a colouring being X on the wires where a bit
-- string is false (Colours).  Both boxes are diagonal; the proof is the
-- paper's induction on the width.
--
-- On four wires it is decided: completeness there, the evaluation
-- about four seconds per colouring (`Base`).  At width 5 + k, if the
-- colouring is black on every control the statement is trivial, or the
-- box case x = y of (336) (BoxFrames' comm336).  Otherwise the swap of
-- two adjacent controls, which passes both boxes ((307)), moves a white
-- control to wire 2 (`move`).  Then both boxes are expanded by (320):
-- Λ = ZX₃ D₃ XZ₃ D₃ with D₃ = Kᵇ Box₃ Kᵇ⁻¹, the rotations on the wires
-- 0–3 black on wire 2 in Λ and white in its colouring, Box₃ with wire 3
-- idle.  Every letter of one expansion commutes with every letter of
-- the other (`pair`): two rotations by (241) or (240) (a coloured
-- rotation is a gate of those families, Colours' `norm-ZX`/`norm-K`),
-- a rotation and a box by (318) or (319), and two boxes, both with
-- wire 3 idle, by the statement one width down (`col-place`).  So the
-- products commute (`all-pairs`).  For (336) the second expansion is
-- the first under the swap of the wires 0 1, which exchanges the two
-- targets of the rotations.  This replaces the paper's two pages of
-- rewriting for each equation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.BoxComm
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.List using (List ; [] ; _∷_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Nat using (ℕ ; zero ; suc ; s≤s ; z≤n)
open import Data.Nat.Properties using (n<1+n)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (swapAt ; Xat)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; X² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (same-sem ; Evaluated)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₁ ; module N₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (ZX₃ ; XZ₃ ; eq208 ; eq208′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃ using (N₁ᵇ ; N₃ᵇ ; rot ; eq241)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃ using (module N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families3 complete₂ complete₃ using (module N₀ ; N₀ᵇ ; eq240)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires
  using (negsB ; negs² ; swB ; swapAt-negsB ; negs-flip ; negs-flip′ ; X-negs ; Xat²)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon4 complete₂ complete₃ using (canon4)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base335 using (d335)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base336 using (d336)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SwapCalc using (swapAt²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-place ; swapX ; swapX′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (place ; place-• ; place-cong ; place-low ; lemma-5-1 ; low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CForm using (cf-• ; cf-loc ; cf-~)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemZX using (module Forms)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp ; below-suc)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym complete₂ complete₃ using (Completes ; eqSymAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CanonN complete₂ complete₃ using (canonN)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Gadget318 complete₂ complete₃ using (Box₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Gadget319 complete₂ complete₃ using (bx ; eq319-rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box320 complete₂ complete₃ using (eq318 ; eq320)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Colours complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (B₁ ; C335 ; C336) public
open import Examples.Groups.Real-Clifford+CH.GeneralN.LocalPlace using (up)

------------------------------------------------------------------------
-- The statements

-- The box on wire 1 controlled by wire 0 and the wires 2 … is Col's B₁.

-- C335 and C336 are Col's.

------------------------------------------------------------------------
-- A flipped bit where X passes the gate does not count

col-flip : ∀ {n} (i : Fin n) (t : Bits n) {w : Circuit n} → n ⊢ Xat (toℕ i) • w ≈ w • Xat (toℕ i) →
           n ⊢ col (flipAt (toℕ i) t) w ≈ col t w
col-flip {n} i t {w} e = begin
  negsB (flipAt (toℕ i) t) • w • negsB (flipAt (toℕ i) t)
    ≈⟨ cong (negs-flip i t) (back _ (negs-flip′ i t)) ⟩
  (Xi • M) • w • (M • Xi)
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
  Xi • (M • w • M) • Xi
    ≈⟨ trans (sym assoc) (trans (front _ (pass (X-negs i t) (pass e (X-negs i t)))) (cancelʳ _ (Xat² i))) ⟩
  M • w • M ∎
  where
  open Tools (n VRel,_===_)
  Xi M : Circuit n
  Xi = Xat (toℕ i)
  M  = negsB t
  pass : ∀ {u v : Circuit n} → Xi • u ≈ u • Xi → Xi • v ≈ v • Xi → Xi • (u • v) ≈ (u • v) • Xi
  pass eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

-- X on wire 1 passes the box on wire 1.
X₁-B : ∀ {m} → (₃₊ m) ⊢ X • Λ□ (₂₊ m) ≈ Λ□ (₂₊ m) • X → (₃₊ m) ⊢ X ↑ • B₁ m ≈ B₁ m • X ↑
X₁-B {m} xb = begin
  X ↑ • Ex • Λ • Ex          ≈⟨ sym assoc ⟩
  (X ↑ • Ex) • Λ • Ex        ≈⟨ front _ swapX ⟩
  (Ex • X) • Λ • Ex          ≈⟨ trans assoc (back _ (trans (sym assoc) (front _ xb))) ⟩
  Ex • (Λ • X) • Ex          ≈⟨ back _ (trans assoc (back _ (sym swapX′))) ⟩
  Ex • Λ • (Ex • X ↑)        ≈⟨ by-passoc (□ • □ • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
  (Ex • Λ • Ex) • X ↑ ∎
  where
  open Tools ((₃₊ m) VRel,_===_)
  Λ : Circuit (₃₊ m)
  Λ = Λ□ (₂₊ m)

------------------------------------------------------------------------
-- On four wires, decided (Base335, Base336)

module Base (comp₄ : Comp 4) where

  private
    open Tools (4 VRel,_===_)
    xb : 4 ⊢ X • Λ□ 3 ≈ Λ□ 3 • X
    xb = Canon.x-box canon4

  c335₁ : C335 1
  -- The words of the stored evaluation exactly: `Same` is never compared.
  c335₁ (true ∷ r)  = comp₄ (same-sem (Λ□ 3 • col (true ∷ r) (Λ□ 3)) (col (true ∷ r) (Λ□ 3) • Λ□ 3) (Evaluated.same (d335 r)))
  c335₁ (false ∷ r) = trans (back _ e) (trans (c335₁ (true ∷ r)) (front _ (sym e)))
    where
    e : col (false ∷ r) (Λ□ 3) ≈ col (true ∷ r) (Λ□ 3)
    e = col-flip 0F (true ∷ r) xb

  c336₁ : C336 1
  c336₁ (a ∷ true ∷ r)  = comp₄ (same-sem (Λ□ 3 • col (a ∷ true ∷ r) (B₁ 1)) (col (a ∷ true ∷ r) (B₁ 1) • Λ□ 3) (Evaluated.same (d336 a r)))
  c336₁ (a ∷ false ∷ r) = trans (back _ e) (trans (c336₁ (a ∷ true ∷ r)) (front _ (sym e)))
    where
    e : col (a ∷ false ∷ r) (B₁ 1) ≈ col (a ∷ true ∷ r) (B₁ 1)
    e = col-flip (sF 0F) (a ∷ true ∷ r) (X₁-B xb)

------------------------------------------------------------------------
-- Moving a white control by adjacent swaps

private
  swB-invol : ∀ {m} i (t : Bits m) → swB i (swB i t) ≡ t
  swB-invol i       []          = Eq.refl
  swB-invol zero    (a ∷ [])    = Eq.refl
  swB-invol zero    (a ∷ b ∷ t) = Eq.refl
  swB-invol (suc i) (a ∷ t)     = Eq.cong (a ∷_) (swB-invol i t)

-- A property of bit strings that is closed under the swap of adjacent
-- bits holds everywhere once it holds where the first bit is false and
-- on the string that is all true.
move′ : ∀ {m} (Q : Bits (₁₊ m) → Set) → (∀ r → Q (false ∷ r)) →
        (∀ i t → Q (swB i t) → Q t) → Q (replicate _ true) → ∀ t → Q t
move′ {zero}  Q q₀ sw q₁ (false ∷ []) = q₀ []
move′ {zero}  Q q₀ sw q₁ (true  ∷ []) = q₁
move′ {suc m} Q q₀ sw q₁ (false ∷ r)  = q₀ r
move′ {suc m} Q q₀ sw q₁ (true  ∷ r)  =
  move′ (λ r → Q (true ∷ r)) (λ r → sw 0 (true ∷ false ∷ r) (q₀ (true ∷ r)))
        (λ i t q → sw (suc i) (true ∷ t) q) q₁ r

-- The same with the target on the second bit.
move : ∀ {m} (Q : Bits (₂₊ m) → Set) → (∀ b r → Q (b ∷ false ∷ r)) →
       (∀ i t → Q (swB i t) → Q t) → Q (replicate _ true) → ∀ t → Q t
move Q q₀ sw q₁ (false ∷ c ∷ r) = sw 0 (false ∷ c ∷ r) (q₀ c r)
move Q q₀ sw q₁ (true  ∷ r)     =
  move′ (λ r → Q (true ∷ r)) (q₀ true) (λ i t q → sw (suc i) (true ∷ t) q) q₁ r

------------------------------------------------------------------------
-- The step, at width 5 + k

module Step (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

    complete : Complete (₁₊ k)
    complete = below (n<1+n (₄₊ k))

    completes : Completes (₁₊ k)
    completes j≤ = below (s≤s (s≤s (s≤s (s≤s j≤))))

    canon : Canon (₂₊ k)
    canon = canonN k completes

    module CN = Canon canon

    Λ : Circuit N
    Λ = Λ□ (₄₊ k)

    Λ₄ : Circuit (₄₊ k)
    Λ₄ = Λ□ (₃₊ k)

  open Tools (N VRel,_===_)
  open WordAlgebra (N VRel,_===_) using (comm-inv)

  --------------------------------------------------------------------
  -- The letters of (320)

  data L : Set where
    zx xz kb kb′ bb : L

  lt : L → Circuit N
  lt zx  = ZX₃
  lt xz  = XZ₃
  lt kb  = S₀₁.⟪ ZX₃ ⟫
  lt kb′ = S₀₁.⟪ XZ₃ ⟫
  lt bb  = Box₃ k

  private
    -- The rotations are words on the bottom four wires.
    loc : L → Circuit 4
    loc zx  = ΛZX 3
    loc xz  = ΛXZ 3
    loc kb  = Ex • ΛZX 3 • Ex
    loc kb′ = Ex • ΛXZ 3 • Ex
    loc bb  = ε

    -- Inverses.
    inv : L → L
    inv zx  = xz
    inv xz  = zx
    inv kb  = kb′
    inv kb′ = kb
    inv bb  = bb

    ZX-XZ : ZX₃ • XZ₃ ≈ ε
    ZX-XZ = eq208′
    XZ-ZX : XZ₃ • ZX₃ ≈ ε
    XZ-ZX = eq208
    K-K′ : S₀₁.⟪ ZX₃ ⟫ • S₀₁.⟪ XZ₃ ⟫ ≈ ε
    K-K′ = trans (sym (S₀₁.⟪⟫-• ZX₃ XZ₃)) (trans (S₀₁.⟪⟫-cong eq208′) S₀₁.⟪⟫-ε)
    K′-K : S₀₁.⟪ XZ₃ ⟫ • S₀₁.⟪ ZX₃ ⟫ ≈ ε
    K′-K = trans (sym (S₀₁.⟪⟫-• XZ₃ ZX₃)) (trans (S₀₁.⟪⟫-cong eq208) S₀₁.⟪⟫-ε)

  --------------------------------------------------------------------
  -- Pairs, for a colouring white on wire 2

  module Pairs (a b d : Bool) (x : Bits (₁₊ k)) where

    s : Bits N
    s = a ∷ b ∷ false ∷ d ∷ x

    private
      module I = Forms (₁₊ k)

      -- X on the box wire passes Box₃: one width down, wire 3 idle.
      X-Box₃ : X • Box₃ k ≈ Box₃ k • X
      X-Box₃ = begin
        X • place 3 Λ₄              ≈⟨ front _ (sym (place-low 3 (X {2}))) ⟩
        place 3 X • place 3 Λ₄      ≈⟨ sym (place-• 3 X Λ₄) ⟩
        place 3 (X • Λ₄)            ≈⟨ lemma-5-1 3 complete (cf-~ (cf-• (cf-loc (X {2})) I.box) (cf-• I.box (cf-loc (X {2}))) Eq.refl Eq.refl) ⟩
        place 3 (Λ₄ • X)            ≈⟨ place-• 3 Λ₄ X ⟩
        place 3 Λ₄ • place 3 X      ≈⟨ back _ (place-low 3 (X {2})) ⟩
        place 3 Λ₄ • X ∎

      N₀-Box₃ : ∀ c → N₀ᵇ c (Box₃ k) ≈ Box₃ k
      N₀-Box₃ true  = refl
      N₀-Box₃ false = N₀.⟪⟫-fix X-Box₃

      N₃-Box₃ : ∀ c → N₃ᵇ c (Box₃ k) ≈ Box₃ k
      N₃-Box₃ true  = refl
      N₃-Box₃ false = N₃.⟪⟫-fix (X-place 3 Λ₄)

    -- The coloured Box₃: its colours on the wires 0 and 3 do not count.
    norm-Box : col s (Box₃ k) ≈ colT x (bx k b false)
    norm-Box = begin
      col s (Box₃ k)
        ≈⟨ peel a b false d x (Box₃ k) ⟩
      N₀ᵇ a (N₁ᵇ b (N₂.⟪ N₃ᵇ d (colT x (Box₃ k)) ⟫))
        ≈⟨ N₀ᵇ-cong a (N₁ᵇ-cong b (N₂.⟪⟫-cong (trans (N₃-colT d x _) (colT-cong (N₃-Box₃ d))))) ⟩
      N₀ᵇ a (N₁ᵇ b (N₂.⟪ colT x (Box₃ k) ⟫))
        ≈⟨ N₀ᵇ-cong a (N₁ᵇ-cong b (N₂-colT false x _)) ⟩
      N₀ᵇ a (N₁ᵇ b (colT x (N₂.⟪ Box₃ k ⟫)))
        ≈⟨ N₀ᵇ-cong a (N₁-colT b x _) ⟩
      N₀ᵇ a (colT x (N₁ᵇ b (N₂.⟪ Box₃ k ⟫)))
        ≈⟨ N₀-colT a x _ ⟩
      colT x (N₀ᵇ a (N₁ᵇ b (N₂.⟪ Box₃ k ⟫)))
        ≈⟨ colT-cong (trans (N₀₁ a b _) (N₁ᵇ-cong b (trans (N₀₂ a false _) (N₂.⟪⟫-cong (N₀-Box₃ a))))) ⟩
      colT x (N₁ᵇ b (N₂.⟪ Box₃ k ⟫)) ∎
      where
      colT-cong : ∀ {u v} → u ≈ v → colT x u ≈ colT x v
      colT-cong e = back _ (front _ e)

  --------------------------------------------------------------------
  -- Products

  word : (L → Circuit N) → List L → Circuit N
  word f []       = ε
  word f (l ∷ ls) = f l • word f ls

  -- The letters of (320), in order.
  es : List L
  es = zx ∷ kb ∷ bb ∷ kb′ ∷ xz ∷ kb ∷ bb ∷ kb′ ∷ []

  private
    pass : ∀ {a u v : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
    pass {a} {u} {v} eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

    pass-word : ∀ {y : Circuit N} f ls → (∀ l → y • f l ≈ f l • y) → y • word f ls ≈ word f ls • y
    pass-word f []       e = trans right-unit (sym left-unit)
    pass-word f (l ∷ ls) e = pass (e l) (pass-word f ls e)

    word-pass : ∀ {y : Circuit N} f ls → (∀ l → f l • y ≈ y • f l) → word f ls • y ≈ y • word f ls
    word-pass f []       e = trans left-unit (sym right-unit)
    word-pass f (l ∷ ls) e = sym (pass (sym (e l)) (sym (word-pass f ls e)))

  -- Two products commute when their letters do, pair by pair.
  all-pairs : ∀ f g ls ls′ → (∀ l l′ → f l • g l′ ≈ g l′ • f l) → word f ls • word g ls′ ≈ word g ls′ • word f ls
  all-pairs f g ls ls′ e = word-pass f ls (λ l → pass-word g ls′ (e l))

  -- A conjugation by an involution, letter by letter.
  module CW (c : Circuit N) (c² : c • c ≈ ε) where
    open Conj c c²
    ⟪⟫-word : ∀ f ls → ⟪ word f ls ⟫ ≈ word (λ l → ⟪ f l ⟫) ls
    ⟪⟫-word f []       = ⟪⟫-ε
    ⟪⟫-word f (l ∷ ls) = trans (⟪⟫-• (f l) (word f ls)) (back _ (⟪⟫-word f ls))

  -- (320), as a product of letters.
  E-word : Λ ≈ word lt es
  E-word = begin
    Λ
      ≈⟨ eq320 k below ⟩
    ZX₃ • (S₀₁.⟪ ZX₃ ⟫ • Box₃ k • S₀₁.⟪ XZ₃ ⟫) • XZ₃ • (S₀₁.⟪ ZX₃ ⟫ • Box₃ k • S₀₁.⟪ XZ₃ ⟫)
      ≈⟨ by-passoc (□ • (□ • □ • □) • □ • (□ • □ • □)) (□ • □ • □ • □ • □ • □ • □ • □) Eq.refl ⟩
    ZX₃ • S₀₁.⟪ ZX₃ ⟫ • Box₃ k • S₀₁.⟪ XZ₃ ⟫ • XZ₃ • S₀₁.⟪ ZX₃ ⟫ • Box₃ k • S₀₁.⟪ XZ₃ ⟫
      ≈⟨ back _ (back _ (back _ (back _ (back _ (back _ (back _ (sym right-unit))))))) ⟩
    word lt es ∎

  B₁-word : B₁ (₂₊ k) ≈ word (λ l → S₀₁.⟪ lt l ⟫) es
  B₁-word = trans (S₀₁.⟪⟫-cong E-word) (CW.⟪⟫-word (Ex ↓) Ex² lt es)

  --------------------------------------------------------------------
  -- Every letter commutes with every coloured letter

  -- The base pairs, rotations with the sign ZX.
  private
    rZZ : ∀ a b d x → ZX₃ • col (a ∷ b ∷ false ∷ d ∷ x) ZX₃ ≈ col (a ∷ b ∷ false ∷ d ∷ x) ZX₃ • ZX₃
    rZZ a b d x = trans (back _ (norm-ZX a b d x))
                    (trans (eq241 true true d b true a) (front _ (sym (norm-ZX a b d x))))

    rZK : ∀ a b d x → ZX₃ • col (a ∷ b ∷ false ∷ d ∷ x) (S₀₁.⟪ ZX₃ ⟫) ≈ col (a ∷ b ∷ false ∷ d ∷ x) (S₀₁.⟪ ZX₃ ⟫) • ZX₃
    rZK a b d x = trans (back _ (norm-K a b d x))
                    (trans (eq240 true true d a true b) (front _ (sym (norm-K a b d x))))

    -- Through the swap of the wires 0 1.
    swapped : ∀ a b d x {w y : Circuit N} →
              S₀₁.⟪ w ⟫ • col (b ∷ a ∷ false ∷ d ∷ x) y ≈ col (b ∷ a ∷ false ∷ d ∷ x) y • S₀₁.⟪ w ⟫ →
              w • col (a ∷ b ∷ false ∷ d ∷ x) (S₀₁.⟪ y ⟫) ≈ col (a ∷ b ∷ false ∷ d ∷ x) (S₀₁.⟪ y ⟫) • w
    swapped a b d x {w} {y} e =
      S₀₁.⟪⟫-≈ e (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ w) (col-Ex (b ∷ a ∷ false ∷ d ∷ x) y))
                 (S₀₁.⟪⟫-•₂ (col-Ex (b ∷ a ∷ false ∷ d ∷ x) y) (S₀₁.⟪⟫-⟪⟫ w))

    KK : S₀₁.⟪ S₀₁.⟪ ZX₃ ⟫ ⟫ ≈ ZX₃
    KK = S₀₁.⟪⟫-⟪⟫ ZX₃

    rKZ : ∀ a b d x → S₀₁.⟪ ZX₃ ⟫ • col (a ∷ b ∷ false ∷ d ∷ x) ZX₃ ≈ col (a ∷ b ∷ false ∷ d ∷ x) ZX₃ • S₀₁.⟪ ZX₃ ⟫
    rKZ a b d x = trans (back _ (Col.⟪⟫-cong (a ∷ b ∷ false ∷ d ∷ x) (sym KK)))
                    (trans (swapped a b d x (trans (front _ KK) (trans (rZK b a d x) (back _ (sym KK)))))
                           (front _ (Col.⟪⟫-cong (a ∷ b ∷ false ∷ d ∷ x) KK)))

    rKK : ∀ a b d x → S₀₁.⟪ ZX₃ ⟫ • col (a ∷ b ∷ false ∷ d ∷ x) (S₀₁.⟪ ZX₃ ⟫) ≈ col (a ∷ b ∷ false ∷ d ∷ x) (S₀₁.⟪ ZX₃ ⟫) • S₀₁.⟪ ZX₃ ⟫
    rKK a b d x = swapped a b d x (trans (front _ KK) (trans (rZZ b a d x) (back _ (sym KK))))

  -- The swap of the wires 0 1 exchanges the two targets.
  sw : L → L
  sw zx  = kb
  sw kb  = zx
  sw xz  = kb′
  sw kb′ = xz
  sw bb  = bb

  module Pair (ih₅ : C335 (₁₊ k)) (ih₆ : C336 (₁₊ k)) (a b d : Bool) (x : Bits (₁₊ k)) where

    s : Bits N
    s = a ∷ b ∷ false ∷ d ∷ x

    private
      module Cs = Col s
      open Pairs a b d x using (norm-Box)

      colinv : ∀ {w v} → w • v ≈ ε → col s w • col s v ≈ ε
      colinv {w} {v} e = trans (sym (Cs.⟪⟫-• w v)) (trans (Cs.⟪⟫-cong e) Cs.⟪⟫-ε)

      right : ∀ {y w v} → w • v ≈ ε → v • w ≈ ε → y • col s w ≈ col s w • y → y • col s v ≈ col s v • y
      right wv vw e = comm-inv (colinv wv) (colinv vw) e

      left : ∀ {Y w v} → w • v ≈ ε → v • w ≈ ε → w • Y ≈ Y • w → v • Y ≈ Y • v
      left wv vw e = sym (comm-inv wv vw (sym e))

      via : ∀ (u : Circuit 4) → (u ↓ᵏ ₁₊ k) • bx k b false ≈ bx k b false • (u ↓ᵏ ₁₊ k) →
            (u ↓ᵏ ₁₊ k) • col s (Box₃ k) ≈ col s (Box₃ k) • (u ↓ᵏ ₁₊ k)
      via u e = trans (back _ norm-Box) (trans (colT-pass u x e) (front _ (sym norm-Box)))

      -- Anything passes the coloured Box₃: rotations by (318) and (319),
      -- Box₃ by the statement one width down.
      rb : ∀ l → lt l • col s (Box₃ k) ≈ col s (Box₃ k) • lt l
      rb zx  = via (loc zx) (eq319-rot k below true b false)
      rb xz  = via (loc xz) (eq319-rot k below false b false)
      rb kb  = via (loc kb) (eq318 k below true b)
      rb kb′ = via (loc kb′) (eq318 k below false b)
      rb bb  = begin
        Box₃ k • col s (Box₃ k)       ≈⟨ back _ cp ⟩
        place 3 Λ₄ • place 3 C        ≈⟨ sym (place-• 3 Λ₄ C) ⟩
        place 3 (Λ₄ • C)              ≈⟨ place-cong 3 (ih₅ (a ∷ b ∷ false ∷ x)) ⟩
        place 3 (C • Λ₄)              ≈⟨ place-• 3 C Λ₄ ⟩
        place 3 C • place 3 Λ₄        ≈⟨ front _ (sym cp) ⟩
        col s (Box₃ k) • Box₃ k ∎
        where
        C : Circuit (₄₊ k)
        C = col (a ∷ b ∷ false ∷ x) Λ₄
        cp : col s (Box₃ k) ≈ place 3 C
        cp = col-place a b false d x Λ₄

      box-rot : ∀ l′ → Box₃ k • col s (lt l′) ≈ col s (lt l′) • Box₃ k
      box-rot l′ = sym (Cs.⟪⟫-≈ (rb l′) (Cs.⟪⟫-•₂ refl (Cs.⟪⟫-⟪⟫ (Box₃ k))) (Cs.⟪⟫-•₂ (Cs.⟪⟫-⟪⟫ (Box₃ k)) refl))

    pair : ∀ l l′ → lt l • col s (lt l′) ≈ col s (lt l′) • lt l
    pair zx  zx  = rZZ a b d x
    pair zx  kb  = rZK a b d x
    pair zx  xz  = right ZX-XZ XZ-ZX (rZZ a b d x)
    pair zx  kb′ = right K-K′ K′-K (rZK a b d x)
    pair kb  zx  = rKZ a b d x
    pair kb  kb  = rKK a b d x
    pair kb  xz  = right ZX-XZ XZ-ZX (rKZ a b d x)
    pair kb  kb′ = right K-K′ K′-K (rKK a b d x)
    pair xz  zx  = left ZX-XZ XZ-ZX (rZZ a b d x)
    pair xz  kb  = left ZX-XZ XZ-ZX (rZK a b d x)
    pair xz  xz  = left ZX-XZ XZ-ZX (right ZX-XZ XZ-ZX (rZZ a b d x))
    pair xz  kb′ = left ZX-XZ XZ-ZX (right K-K′ K′-K (rZK a b d x))
    pair kb′ zx  = left K-K′ K′-K (rKZ a b d x)
    pair kb′ kb  = left K-K′ K′-K (rKK a b d x)
    pair kb′ xz  = left K-K′ K′-K (right ZX-XZ XZ-ZX (rKZ a b d x))
    pair kb′ kb′ = left K-K′ K′-K (right K-K′ K′-K (rKK a b d x))
    pair zx  bb  = rb zx
    pair xz  bb  = rb xz
    pair kb  bb  = rb kb
    pair kb′ bb  = rb kb′
    pair bb  bb  = rb bb
    pair bb  zx  = box-rot zx
    pair bb  xz  = box-rot xz
    pair bb  kb  = box-rot kb
    pair bb  kb′ = box-rot kb′

    -- (335) with a white control on wire 2.
    main335 : Λ • col s Λ ≈ col s Λ • Λ
    main335 = begin
      Λ • col s Λ                           ≈⟨ cong E-word (Cs.⟪⟫-cong E-word) ⟩
      word lt es • col s (word lt es)       ≈⟨ back _ (CW.⟪⟫-word (negsB s) (negs² s) lt es) ⟩
      word lt es • word (λ l → col s (lt l)) es
        ≈⟨ all-pairs lt (λ l → col s (lt l)) es es pair ⟩
      word (λ l → col s (lt l)) es • word lt es
        ≈⟨ front _ (sym (CW.⟪⟫-word (negsB s) (negs² s) lt es)) ⟩
      col s (word lt es) • word lt es       ≈⟨ sym (cong (Cs.⟪⟫-cong E-word) E-word) ⟩
      col s Λ • Λ ∎

  -- (336) with a white control on wire 2: against the letters under the
  -- swap of the wires 0 1.
  module Pair₆ (ih₅ : C335 (₁₊ k)) (ih₆ : C336 (₁₊ k)) (a b d : Bool) (x : Bits (₁₊ k)) where

    open Pair ih₅ ih₆ a b d x using (s ; pair)

    private
      module Cs = Col s
      module P′ = Pair ih₅ ih₆ b a d x

      rot-sw : ∀ l l′ → S₀₁.⟪ lt l′ ⟫ ≈ lt (sw l′) →
               lt l • col s (S₀₁.⟪ lt l′ ⟫) ≈ col s (S₀₁.⟪ lt l′ ⟫) • lt l
      rot-sw l l′ e = trans (back _ (Cs.⟪⟫-cong e)) (trans (pair l (sw l′)) (front _ (Cs.⟪⟫-cong (sym e))))

      sw-rot : ∀ l → S₀₁.⟪ lt l ⟫ ≈ lt (sw l) →
               lt l • col s (S₀₁.⟪ Box₃ k ⟫) ≈ col s (S₀₁.⟪ Box₃ k ⟫) • lt l
      sw-rot l e = swapped a b d x (trans (front _ e) (trans (P′.pair (sw l) bb) (back _ (sym e))))

      S-place : S₀₁.⟪ Box₃ k ⟫ ≈ place 3 (B₁ (₁₊ k))
      S-place = sym (trans (place-• 3 (Ex ↓) (Λ₄ • Ex ↓))
                  (cong (place-low 3 (Ex {1})) (trans (place-• 3 Λ₄ (Ex ↓)) (back _ (place-low 3 (Ex {1}))))))

      bb-bb : Box₃ k • col s (S₀₁.⟪ Box₃ k ⟫) ≈ col s (S₀₁.⟪ Box₃ k ⟫) • Box₃ k
      bb-bb = begin
        Box₃ k • col s (S₀₁.⟪ Box₃ k ⟫)     ≈⟨ back _ cp ⟩
        place 3 Λ₄ • place 3 C             ≈⟨ sym (place-• 3 Λ₄ C) ⟩
        place 3 (Λ₄ • C)                   ≈⟨ place-cong 3 (ih₆ (a ∷ b ∷ false ∷ x)) ⟩
        place 3 (C • Λ₄)                   ≈⟨ place-• 3 C Λ₄ ⟩
        place 3 C • place 3 Λ₄             ≈⟨ front _ (sym cp) ⟩
        col s (S₀₁.⟪ Box₃ k ⟫) • Box₃ k ∎
        where
        C : Circuit (₄₊ k)
        C = col (a ∷ b ∷ false ∷ x) (B₁ (₁₊ k))
        cp : col s (S₀₁.⟪ Box₃ k ⟫) ≈ place 3 C
        cp = trans (Cs.⟪⟫-cong S-place) (col-place a b false d x (B₁ (₁₊ k)))

      sK : S₀₁.⟪ S₀₁.⟪ ZX₃ ⟫ ⟫ ≈ ZX₃
      sK = S₀₁.⟪⟫-⟪⟫ ZX₃
      sK′ : S₀₁.⟪ S₀₁.⟪ XZ₃ ⟫ ⟫ ≈ XZ₃
      sK′ = S₀₁.⟪⟫-⟪⟫ XZ₃

    pair₆ : ∀ l l′ → lt l • col s (S₀₁.⟪ lt l′ ⟫) ≈ col s (S₀₁.⟪ lt l′ ⟫) • lt l
    pair₆ l   zx  = rot-sw l zx  refl
    pair₆ l   kb  = rot-sw l kb  sK
    pair₆ l   xz  = rot-sw l xz  refl
    pair₆ l   kb′ = rot-sw l kb′ sK′
    pair₆ zx  bb  = sw-rot zx  refl
    pair₆ kb  bb  = sw-rot kb  sK
    pair₆ xz  bb  = sw-rot xz  refl
    pair₆ kb′ bb  = sw-rot kb′ sK′
    pair₆ bb  bb  = bb-bb

    main336 : Λ • col s (B₁ (₂₊ k)) ≈ col s (B₁ (₂₊ k)) • Λ
    main336 = begin
      Λ • col s (B₁ (₂₊ k))
        ≈⟨ cong E-word (Cs.⟪⟫-cong B₁-word) ⟩
      word lt es • col s (word S′ es)
        ≈⟨ back _ (CW.⟪⟫-word (negsB s) (negs² s) S′ es) ⟩
      word lt es • word (λ l → col s (S′ l)) es
        ≈⟨ all-pairs lt (λ l → col s (S′ l)) es es pair₆ ⟩
      word (λ l → col s (S′ l)) es • word lt es
        ≈⟨ front _ (sym (CW.⟪⟫-word (negsB s) (negs² s) S′ es)) ⟩
      col s (word S′ es) • word lt es
        ≈⟨ sym (cong (Cs.⟪⟫-cong B₁-word) E-word) ⟩
      col s (B₁ (₂₊ k)) • Λ ∎
      where
      S′ : L → Circuit N
      S′ l = S₀₁.⟪ lt l ⟫

  --------------------------------------------------------------------
  -- Every colouring

  private
    negs-T : ∀ {m} → negsB (replicate m true) ≡ ε
    negs-T {zero}  = Eq.refl
    negs-T {suc m} = Eq.cong _↑ (negs-T {m})

    colT-T : ∀ (w : Circuit N) → colT (replicate _ true) w ≈ w
    colT-T w = Eq.subst (λ e → up 4 e • w • up 4 e ≈ w) (Eq.sym (negs-T {₁₊ k})) (trans left-unit right-unit)

    N₀-Λ : ∀ c → N₀ᵇ c Λ ≈ Λ
    N₀-Λ true  = refl
    N₀-Λ false = N₀.⟪⟫-fix CN.x-box

    X₁-B₁ : X ↑ • B₁ (₂₊ k) ≈ B₁ (₂₊ k) • X ↑
    X₁-B₁ = X₁-B CN.x-box

    N₁-B₁ : ∀ c → N₁ᵇ c (B₁ (₂₊ k)) ≈ B₁ (₂₊ k)
    N₁-B₁ true  = refl
    N₁-B₁ false = N₁.⟪⟫-fix X₁-B₁

    -- The case x = y of (336), in the colours of wire 0.
    base : ∀ c → Λ • N₀ᵇ c (B₁ (₂₊ k)) ≈ N₀ᵇ c (B₁ (₂₊ k)) • Λ
    base true  = CN.comm336
    base false = N₀.⟪⟫-≈ CN.comm336 (N₀.⟪⟫-•₂ (N₀-Λ false) refl) (N₀.⟪⟫-•₂ refl (N₀-Λ false))

    -- An adjacent swap of the controls from wire 1 on passes Λ.
    σΛ : ∀ i → swapAt (suc i) • Λ ≈ Λ • swapAt (suc i)
    σΛ i = eqSymAt (₁₊ k) completes i

    -- And from wire 2 on also B₁: it passes the swap of the wires 0 1.
    σB₁ : ∀ i → swapAt (₂₊ i) • B₁ (₂₊ k) ≈ B₁ (₂₊ k) • swapAt (₂₊ i)
    σB₁ i = begin
      σ • Ex • Λ • Ex        ≈⟨ trans (sym assoc) (front _ σEx) ⟩
      (Ex • σ) • Λ • Ex      ≈⟨ trans assoc (back _ (trans (sym assoc) (front _ (σΛ (suc i))))) ⟩
      Ex • (Λ • σ) • Ex      ≈⟨ back _ (trans assoc (back _ σEx)) ⟩
      Ex • Λ • Ex • σ        ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
      (Ex • Λ • Ex) • σ ∎
      where
      σ : Circuit N
      σ = swapAt (₂₊ i)
      σEx : σ • Ex ≈ Ex • σ
      σEx = sym (low-comm (Ex {0}) (swapAt {₃₊ k} i))

    -- Conjugating by a swap that passes w carries a statement at the
    -- swapped colouring to the colouring.
    by-swap : ∀ c (w : Circuit N) (t : Bits N) → swapAt c • w ≈ w • swapAt c →
              Λ • col (swB c t) w ≈ col (swB c t) w • Λ → swapAt c • Λ ≈ Λ • swapAt c →
              Λ • col t w ≈ col t w • Λ
    by-swap c w t σw q σλ = Sσ.⟪⟫-≈ q (Sσ.⟪⟫-•₂ fixΛ e) (Sσ.⟪⟫-•₂ e fixΛ)
      where
      module Sσ = Conj (swapAt c) (swapAt² c)
      fixΛ : Sσ.⟪ Λ ⟫ ≈ Λ
      fixΛ = Sσ.⟪⟫-fix σλ
      e′ : Sσ.⟪ col (swB c t) w ⟫ ≈ col (swB c (swB c t)) w
      e′ = Sσ.⟪⟫-•₃ (swapAt-negsB c (swB c t)) (Sσ.⟪⟫-fix σw) (swapAt-negsB c (swB c t))
      e : Sσ.⟪ col (swB c t) w ⟫ ≈ col t w
      e = Eq.subst (λ v → Sσ.⟪ col (swB c t) w ⟫ ≈ col v w) (swB-invol c t) e′

  step335 : C335 (₁₊ k) → C336 (₁₊ k) → C335 (₂₊ k)
  step335 ih₅ ih₆ (a ∷ t) =
    move (λ t → Λ • col (a ∷ t) Λ ≈ col (a ∷ t) Λ • Λ)
      (λ { b (d ∷ x) → Pair.main335 ih₅ ih₆ a b d x })
      (λ i t q → by-swap (suc i) Λ (a ∷ t) (σΛ i) q (σΛ i))
      triv t
    where
    triv : Λ • col (a ∷ replicate _ true) Λ ≈ col (a ∷ replicate _ true) Λ • Λ
    triv = trans (back _ tΛ) (front _ (sym tΛ))
      where
      tΛ : col (a ∷ replicate _ true) Λ ≈ Λ
      tΛ = trans (peel a true true true (replicate _ true) Λ) (trans (N₀ᵇ-cong a (colT-T Λ)) (N₀-Λ a))

  step336 : C335 (₁₊ k) → C336 (₁₊ k) → C336 (₂₊ k)
  step336 ih₅ ih₆ (a ∷ b ∷ u) =
    move′ (λ u → Λ • col (a ∷ b ∷ u) (B₁ (₂₊ k)) ≈ col (a ∷ b ∷ u) (B₁ (₂₊ k)) • Λ)
      (λ { (d ∷ x) → Pair₆.main336 ih₅ ih₆ a b d x })
      (λ i u q → by-swap (₂₊ i) (B₁ (₂₊ k)) (a ∷ b ∷ u) (σB₁ i) q (σΛ (suc i)))
      triv u
    where
    triv : Λ • col (a ∷ b ∷ replicate _ true) (B₁ (₂₊ k)) ≈ col (a ∷ b ∷ replicate _ true) (B₁ (₂₊ k)) • Λ
    triv = trans (back _ tB) (trans (base a) (front _ (sym tB)))
      where
      tB : col (a ∷ b ∷ replicate _ true) (B₁ (₂₊ k)) ≈ N₀ᵇ a (B₁ (₂₊ k))
      tB = trans (peel a b true true (replicate _ true) (B₁ (₂₊ k)))
                 (N₀ᵇ-cong a (trans (N₁ᵇ-cong b (colT-T (B₁ (₂₊ k)))) (N₁-B₁ b)))

------------------------------------------------------------------------
-- (335) and (336) at every width from four on

c33 : ∀ k → Below (₁₊ (₄₊ k)) → C335 (₂₊ k) × C336 (₂₊ k)
c33 zero    b = Step.step335 0 b c₅ c₆ , Step.step336 0 b c₅ c₆
  where
  c₄ : Comp 4
  c₄ = b (n<1+n 4)
  c₅ = Base.c335₁ c₄
  c₆ = Base.c336₁ c₄
c33 (suc k) b = Step.step335 (suc k) b (proj₁ ih) (proj₂ ih) , Step.step336 (suc k) b (proj₁ ih) (proj₂ ih)
  where
  ih = c33 k (below-suc b)

eq335 : ∀ k → Below (₁₊ (₄₊ k)) → C335 (₂₊ k)
eq335 k b = proj₁ (c33 k b)

eq336ᶜ : ∀ k → Below (₁₊ (₄₊ k)) → C336 (₂₊ k)
eq336ᶜ k b = proj₂ (c33 k b)

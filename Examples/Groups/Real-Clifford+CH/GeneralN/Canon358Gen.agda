------------------------------------------------------------------------
-- Presentations of groups
--
-- Two crossed rotations satisfy the braid relation, at any width with
-- the canonical facts given (Clément, Lemma D.15, Equation (358))
--
-- With a the rotation XZ on wire 0 and b the rotation ZX on wire 1,
-- each controlled by the other's target and by the wires 2 …, a • b • a
-- ≈ b • a • b (`eq358`).  Canon358's argument: merge each rotation over
-- every colouring of the wires 2 … (`mg`), giving two-wire rotations e,
-- e′ with e • e′ • e ≈ CZ • Ex (a two-wire evaluation); every colouring
-- but the black one is separated from a and b by a white wire
-- (`rotcomm`), so e = D_a • a and e′ = D_b • b with D_a, D_b passing a
-- and b (MergeGen.pass-last′); and CZ • Ex conjugates b to a by (357)
-- (`e357`).  Canon358 is the instance from five wires on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ)
open import Data.Vec using (_∷_)
open import Word.Base using (_•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot ; F ; RotComm)

module Examples.Groups.Real-Clifford+CH.GeneralN.Canon358Gen
  {m : ℕ} (C : Canon m)
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (rotcomm : RotComm m)
  (mg : ∀ β → (₃₊ m) ⊢ ∏ (allBits (₁₊ m)) (λ c → negsB (true ∷ true ∷ c) • F β (₂₊ m) • negsB (true ∷ true ∷ c))
                       ≈ F β 1 ↓ᵏ (₁₊ m))
  (e357 : (₃₊ m) ⊢ CZ ↓ • rot {m} true • CZ ↓ ≈ rot false)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n)
open import Data.Product using (Σ ; _,_)
open import Data.Vec using ([] ; _∷_ ; _∷ʳ_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; CZ² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.TopWeakening using (top)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; insertℕ ; lookupℕ)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (shiftDown ; shiftUp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires
  using (negsB ; negs² ; sdS ; net-sdS ; revS-sdS ; net-suS ; sd-target ; allT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceCalc using (placeAt-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.TwoWire using (placeAt-top)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon ; pl)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceFrames using (conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.MergeGen using (∏-conj ; ∏-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BraidCol using (E358)
open import Examples.Groups.Real-Clifford+CH.GeneralN.MergeGen using (pairing ; pair-merge ; placeAt-∏ ; pass-last′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base358 using (e-ebe ; e-zxxz ; e-xzzx)
import Examples.Groups.Real-Clifford+CH.Lemma88.Invol as Invol

private
  white : ∀ {n} (c : Bits n) → c ≢ replicate n true → Σ (Fin n) (λ j → lookupℕ (toℕ j) c ≡ false)
  white []          ne = ⊥-elim (ne Eq.refl)
  white (false ∷ c) ne = 0F , Eq.refl
  white (true ∷ c)  ne with white c (λ e → ne (Eq.cong (true ∷_) e))
  ... | j , e = sF j , e

  lk-ones : ∀ {n} (j : Fin n) → lookupℕ (toℕ j) (replicate n true) ≡ true
  lk-ones 0F     = Eq.refl
  lk-ones (sF j) = lk-ones j

  tf : true ≢ false
  tf ()



private
  N : ℕ
  N = ₃₊ m

  module I = Invol C complete₂

open Tools (N VRel,_===_)
open SS.Below 2 (s≤s (s≤s z≤n)) complete₂ using (by-sem)

private
  ZXn XZn a b bi XZ₂ ZX₂ : Circuit N
  ZXn  = ΛZX (₂₊ m)
  XZn  = ΛXZ (₂₊ m)
  a   = XZn
  b   = Ex ↓ • ZXn • Ex ↓
  bi  = Ex ↓ • XZn • Ex ↓
  XZ₂ = ΛXZ 1 ↓ᵏ (₁₊ m)
  ZX₂ = ΛZX 1 ↓ᵏ (₁₊ m)

  onesN : Bits N
  onesN = replicate N true

  ≡→≈ : ∀ {x y : Circuit N} → x ≡ y → x ≈ y
  ≡→≈ Eq.refl = refl

  pass₂ : ∀ {y u v : Circuit N} → y • u ≈ u • y → y • v ≈ v • y → y • (u • v) ≈ (u • v) • y
  pass₂ pa pb = trans (sym assoc) (trans (front _ pa) (trans assoc (trans (back _ pb) (sym assoc))))

  module S₀₁ = Conj {N} (Ex ↓) Ex²

  col-1 : ∀ (w : Circuit N) → col onesN w ≈ w
  col-1 w = trans (≡→≈ (Eq.cong (λ z → z • w • z) (allT N))) (trans left-unit right-unit)

  pl-sd : ∀ t (g : Circuit N) → pl (sdS {N} t) g ≡ shiftDown t • g • shiftUp t
  pl-sd t g = Eq.cong₂ (λ x y → x • g • y) (net-sdS t) (Eq.trans (Eq.cong net (revS-sdS t)) (net-suS t))

  place-ε : ∀ (s : Bits N) (g : Circuit N) → place ε s g ≈ col s g
  place-ε s g = back _ (front _ (trans left-unit right-unit))

  -- The swap conjugation is the placement by the swap.
  pl-1 : ∀ (g : Circuit N) → Ex ↓ • g • Ex ↓ ≈ pl (sdS 1) g
  pl-1 g = trans (sym (cong right-unit (back _ left-unit))) (≡→≈ (Eq.sym (pl-sd 1 g)))

  ----------------------------------------------------------------------
  -- a, b and their colourings as placed rotations

  a-pl : a ≈ place ε onesN (rot false)
  a-pl = sym (trans (place-ε onesN XZn) (col-1 XZn))

  b-pl : b ≈ place (sdS 1) onesN (rot true)
  b-pl = trans (pl-1 ZXn) (sym (col-1 (pl (sdS 1) ZXn)))

  ga gb : Bits (₁₊ m) → Circuit N
  ga c = col (true ∷ true ∷ c) a
  gb c = col (true ∷ true ∷ c) b

  ga-pl : ∀ c → ga c ≈ place ε (true ∷ true ∷ c) (rot false)
  ga-pl c = sym (place-ε (true ∷ true ∷ c) XZn)

  gb-pl : ∀ c → gb c ≈ place (sdS 1) (true ∷ true ∷ c) (rot true)
  gb-pl c = back _ (front _ (pl-1 ZXn))

  -- A colouring with a white wire above 1 is separated from a and b.
  sep : ∀ (c : Bits (₁₊ m)) (j : Fin (₁₊ m)) → lookupℕ (toℕ j) c ≡ false →
        lookupℕ (toℕ (sF (sF j))) onesN ≢ lookupℕ (toℕ (sF (sF j))) (true ∷ true ∷ c)
  sep c j cj e = tf (Eq.trans (Eq.sym (lk-ones j)) (Eq.trans e cj))

  sepAA : ∀ c → c ≢ replicate (₁₊ m) true → a • ga c ≈ ga c • a
  sepAA c ne with white c ne
  ... | j , cj = trans (cong a-pl (ga-pl c))
                       (trans (rotcomm false false ε ε 0F 0F Eq.refl Eq.refl onesN (true ∷ true ∷ c)
                                        Eq.refl Eq.refl (sF (sF j)) (λ ()) (λ ()) (sep c j cj))
                              (sym (cong (ga-pl c) a-pl)))

  sepB : ∀ c → c ≢ replicate (₁₊ m) true → b • ga c ≈ ga c • b
  sepB c ne with white c ne
  ... | j , cj = trans (cong b-pl (ga-pl c))
                       (trans (rotcomm true false (sdS 1) ε (sF 0F) 0F (sd-target (sF 0F)) Eq.refl
                                        onesN (true ∷ true ∷ c) Eq.refl Eq.refl (sF (sF j)) (λ ()) (λ ()) (sep c j cj))
                              (sym (cong (ga-pl c) b-pl)))

  sepAB : ∀ c → c ≢ replicate (₁₊ m) true → a • gb c ≈ gb c • a
  sepAB c ne with white c ne
  ... | j , cj = trans (cong a-pl (gb-pl c))
                       (trans (rotcomm false true ε (sdS 1) 0F (sF 0F) Eq.refl (sd-target (sF 0F))
                                        onesN (true ∷ true ∷ c) Eq.refl Eq.refl (sF (sF j)) (λ ()) (λ ()) (sep c j cj))
                              (sym (cong (gb-pl c) a-pl)))

  sepBB : ∀ c → c ≢ replicate (₁₊ m) true → b • gb c ≈ gb c • b
  sepBB c ne with white c ne
  ... | j , cj = trans (cong b-pl (gb-pl c))
                       (trans (rotcomm true true (sdS 1) (sdS 1) (sF 0F) (sF 0F)
                                        (sd-target (sF 0F)) (sd-target (sF 0F))
                                        onesN (true ∷ true ∷ c) Eq.refl Eq.refl (sF (sF j)) (λ ()) (λ ()) (sep c j cj))
                              (sym (cong (gb-pl c) b-pl)))

  ----------------------------------------------------------------------
  -- The merges, and the D-trick

  ea eb : Circuit N
  ea = ∏ (allBits (₁₊ m)) ga
  eb = ∏ (allBits (₁₊ m)) gb

  ea-2 : ea ≈ XZ₂
  ea-2 = mg false

  eb-2 : eb ≈ Ex ↓ • ZX₂ • Ex ↓
  eb-2 = begin
    ∏ (allBits (₁₊ m)) gb
      ≈⟨ ∏-cong (allBits (₁₊ m)) (λ c → conj-swap (sym (low-comm Ex (negsB c))) ZXn) ⟩
    ∏ (allBits (₁₊ m)) (λ c → Ex ↓ • col (true ∷ true ∷ c) ZXn • Ex ↓)
      ≈⟨ sym (∏-conj (Ex ↓) Ex² (allBits (₁₊ m)) (λ c → col (true ∷ true ∷ c) ZXn)) ⟩
    Ex ↓ • ∏ (allBits (₁₊ m)) (λ c → col (true ∷ true ∷ c) ZXn) • Ex ↓
      ≈⟨ mid _ _ (mg true) ⟩
    Ex ↓ • ZX₂ • Ex ↓ ∎

  b-bi : b • bi ≈ ε
  b-bi = trans (sym (S₀₁.⟪⟫-• ZXn XZn)) (trans (S₀₁.⟪⟫-cong I.zx-xz) S₀₁.⟪⟫-ε)

  bi-b : bi • b ≈ ε
  bi-b = trans (sym (S₀₁.⟪⟫-• XZn ZXn)) (trans (S₀₁.⟪⟫-cong I.xz-zx) S₀₁.⟪⟫-ε)

  Da Db : Circuit N
  Da = ea • ZXn
  Db = eb • bi

  ga1 : ga (replicate (₁₊ m) true) • ZXn ≈ ε
  ga1 = trans (front _ (col-1 a)) I.xz-zx

  gb1 : gb (replicate (₁₊ m) true) • bi ≈ ε
  gb1 = trans (front _ (col-1 b)) b-bi

  Da-a : a • Da ≈ Da • a
  Da-a = pass-last′ (₁₊ m) ga sepAA ga1

  Da-b : b • Da ≈ Da • b
  Da-b = pass-last′ (₁₊ m) ga sepB ga1

  Db-a : a • Db ≈ Db • a
  Db-a = pass-last′ (₁₊ m) gb sepAB gb1

  Db-b : b • Db ≈ Db • b
  Db-b = pass-last′ (₁₊ m) gb sepBB gb1

  ea-Da : ea ≈ Da • a
  ea-Da = sym (trans assoc (trans (back _ I.zx-xz) right-unit))

  eb-Db : eb ≈ Db • b
  eb-Db = sym (trans assoc (trans (back _ bi-b) right-unit))

  -- Their inverses, through the two-wire gates.
  zx₂-xz₂ : ZX₂ • XZ₂ ≈ ε
  zx₂-xz₂ = by-sem (ΛZX 1 • ΛXZ 1) ε (Evaluated.same e-zxxz) {₁₊ m}

  xz₂-zx₂ : XZ₂ • ZX₂ ≈ ε
  xz₂-zx₂ = by-sem (ΛXZ 1 • ΛZX 1) ε (Evaluated.same e-xzzx) {₁₊ m}

  Dai Dbi : Circuit N
  Dai = a • ZX₂
  Dbi = b • (Ex ↓ • XZ₂ • Ex ↓)

  Dai-Da : Dai • Da ≈ ε
  Dai-Da = begin
    (a • ZX₂) • (ea • ZXn)      ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    a • (ZX₂ • ea) • ZXn        ≈⟨ back _ (trans (front _ (trans (back _ ea-2) zx₂-xz₂)) left-unit) ⟩
    a • ZXn                     ≈⟨ I.xz-zx ⟩
    ε ∎

  Dbi-Db : Dbi • Db ≈ ε
  Dbi-Db = begin
    (b • (Ex ↓ • XZ₂ • Ex ↓)) • (eb • bi)    ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    b • ((Ex ↓ • XZ₂ • Ex ↓) • eb) • bi      ≈⟨ back _ (trans (front _ (trans (back _ eb-2) inv)) left-unit) ⟩
    b • bi                                   ≈⟨ b-bi ⟩
    ε ∎
    where
    inv : (Ex ↓ • XZ₂ • Ex ↓) • (Ex ↓ • ZX₂ • Ex ↓) ≈ ε
    inv = trans (sym (S₀₁.⟪⟫-• XZ₂ ZX₂)) (trans (S₀₁.⟪⟫-cong xz₂-zx₂) S₀₁.⟪⟫-ε)

  D Di x : Circuit N
  D  = Da • Db • Da
  Di = Dai • Dbi • Dai
  x  = a • b • a

  Di-D : Di • D ≈ ε
  Di-D = begin
    (Dai • Dbi • Dai) • (Da • Db • Da)     ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    Dai • Dbi • (Dai • Da) • Db • Da       ≈⟨ back _ (back _ (trans (front _ Dai-Da) left-unit)) ⟩
    Dai • Dbi • Db • Da                    ≈⟨ back _ (trans (sym assoc) (trans (front _ Dbi-Db) left-unit)) ⟩
    Dai • Da                               ≈⟨ Dai-Da ⟩
    ε ∎

  D-a : a • D ≈ D • a
  D-a = pass₂ Da-a (pass₂ Db-a Da-a)

  -- e e′ e is D x.
  eee-D : ea • eb • ea ≈ D • x
  eee-D = begin
    ea • eb • ea
      ≈⟨ cong ea-Da (cong eb-Db ea-Da) ⟩
    (Da • a) • (Db • b) • (Da • a)
      ≈⟨ by-passoc ((□ • □) • (□ • □) • (□ • □)) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
    Da • (a • Db) • b • Da • a
      ≈⟨ back _ (front _ Db-a) ⟩
    Da • (Db • a) • b • Da • a
      ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) (□ • □ • □ • (□ • □) • □) Eq.refl ⟩
    Da • Db • a • (b • Da) • a
      ≈⟨ back _ (back _ (back _ (front _ Da-b))) ⟩
    Da • Db • a • (Da • b) • a
      ≈⟨ by-passoc (□ • □ • □ • (□ • □) • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    Da • Db • (a • Da) • b • a
      ≈⟨ back _ (back _ (front _ Da-a)) ⟩
    Da • Db • (Da • a) • b • a
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
    D • x ∎

  -- e e′ e is CZ • Ex, which conjugates b to a ((357)).
  eee-CZ : ea • eb • ea ≈ CZ ↓ • Ex ↓
  eee-CZ = trans (cong ea-2 (cong eb-2 ea-2))
                 (by-sem (ΛXZ 1 • (Ex • ΛZX 1 • Ex) • ΛXZ 1) (CZ • Ex) (Evaluated.same e-ebe) {₁₊ m})

  CZEx-b : (CZ ↓ • Ex ↓) • b ≈ a • (CZ ↓ • Ex ↓)
  CZEx-b = begin
    (CZ ↓ • Ex ↓) • (Ex ↓ • ZXn • Ex ↓)     ≈⟨ by-passoc ((□ • □) • (□ • □ • □)) (□ • (□ • □) • □ • □) Eq.refl ⟩
    CZ ↓ • (Ex ↓ • Ex ↓) • ZXn • Ex ↓       ≈⟨ back _ (trans (front _ Ex²) left-unit) ⟩
    CZ ↓ • ZXn • Ex ↓                       ≈⟨ trans (sym assoc) (front _ CZZX) ⟩
    (XZn • CZ ↓) • Ex ↓                     ≈⟨ assoc ⟩
    a • (CZ ↓ • Ex ↓) ∎
    where
    -- CZ • ZX • CZ ≈ XZ, so CZ • ZX ≈ XZ • CZ.
    CZZX : CZ ↓ • ZXn ≈ XZn • CZ ↓
    CZZX = trans (sym (trans assoc (trans (back _ CZ²) right-unit)))
                 (front _ (trans assoc (e357)))

  -- x • b ≈ a • x, cancelling D.
  xb : x • b ≈ a • x
  xb = begin
    x • b                           ≈⟨ sym left-unit ⟩
    ε • (x • b)                     ≈⟨ front _ (sym Di-D) ⟩
    (Di • D) • (x • b)              ≈⟨ assoc ⟩
    Di • (D • (x • b))              ≈⟨ back _ Dxb ⟩
    Di • (D • (a • x))              ≈⟨ sym assoc ⟩
    (Di • D) • (a • x)              ≈⟨ trans (front _ Di-D) left-unit ⟩
    a • x ∎
    where
    Dxb : D • (x • b) ≈ D • (a • x)
    Dxb = begin
      D • (x • b)                   ≈⟨ sym assoc ⟩
      (D • x) • b                   ≈⟨ front _ (sym eee-D) ⟩
      (ea • eb • ea) • b            ≈⟨ front _ eee-CZ ⟩
      (CZ ↓ • Ex ↓) • b             ≈⟨ CZEx-b ⟩
      a • (CZ ↓ • Ex ↓)             ≈⟨ back _ (sym eee-CZ) ⟩
      a • (ea • eb • ea)            ≈⟨ back _ eee-D ⟩
      a • (D • x)                   ≈⟨ trans (sym assoc) (trans (front _ D-a) assoc) ⟩
      D • (a • x) ∎

----------------------------------------------------------------------
-- (358)

eq358 : E358 m
eq358 = sym (begin
  b • a • b                             ≈⟨ sym left-unit ⟩
  ε • (b • a • b)                       ≈⟨ front _ (sym I.zx-xz) ⟩
  (ZXn • a) • (b • a • b)                ≈⟨ assoc ⟩
  ZXn • (a • b • a • b)                  ≈⟨ back _ (trans (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl)
                                                  (trans xb (by-passoc (□ • (□ • □ • □)) (□ • □ • □ • □) Eq.refl))) ⟩
  ZXn • (a • a • b • a)                  ≈⟨ sym assoc ⟩
  (ZXn • a) • (a • b • a)                ≈⟨ trans (front _ I.zx-xz) left-unit ⟩
  a • b • a ∎)

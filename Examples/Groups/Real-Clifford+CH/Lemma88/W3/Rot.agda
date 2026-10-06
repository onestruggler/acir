------------------------------------------------------------------------
-- Presentations of groups
--
-- The rotations on three qubits against each other and against the
-- box (Clément, Appendix E.5 at n = 3, from Lemma D.2)
--
-- On three wires the rotations are CCZX and CCXZ, and the facts the
-- placement modules (RotAnywhereGen, BraidFrom, PairFrom) need come
-- from Lemma D.2 with completeness on two qubits:
--
-- * (351), the rotation against a colouring of a rotation white on a
--   control: on wire 2 it is (136)/(137) and inverses (`sep₂`), on
--   wire 1 the same under the swap of the wires 1 2, which fixes both
--   rotations ((127)); white on both, each rotation is a merge times the
--   other rotation — L (ΛZX 1) • CCXZ, O (ΛZX 1) • CCXZ — and L, O
--   commute because O passes CH • CZ ↓ ((145) under the lower swap).
-- * (352), crossed targets: (139)/(140) for the rotation on wire 1 white
--   on wire 2; X on its target turns it over, X on wire 0 the other.
-- * (356): X = H Z H, and H and Z exchange CCZX and CCXZ.
-- * (358): the D-trick with one merge, over wire 2.  Each rotation is
--   its colouring white on wire 2 times the merge, a two-wire rotation;
--   the three merged letters braid to CZ • Ex (a two-wire evaluation),
--   and CZ • Ex conjugates one rotation to the other.
-- * The pair step: the rotation against the box on wire 1 (CZ₂₀) is
--   turned over, black by definition, white on wire 0 because there the
--   box is CZ₂₀ • Z ↑ ↑ (the merge on wire 1), which the rotation
--   passes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.Lemma88.W3.Rot
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using () renaming (zero to 0F ; suc to sF)
open import Data.Nat using (s≤s ; z≤n)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; X² ; Ex² ; CZ²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂ using (L ; O ; L-sem ; O-sem ; O-L ; by-sem₀)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (eq117 ; eq118 ; eq121 ; eq122 ; eq136 ; eq137 ; eq139 ; eq140 ; eq145 ;
         °CCZX ; °CCXZ ; °CZXC ; °CXZC ; CZ₂₀² ; Z↓-CCZX ; H↓-CCXZ ; K-W ;
         module N₁ ; module N₂ ; module S↑ ; module S↓)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (combine ; _⇔_)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (col-rel ; combine-lookup)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceFrames using (conj-swap)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col ; col-flip ; X₁-B)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol
  using (rot ; F ; RotComm ; C351 ; C352 ; PairCanon ; PairStep)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BraidCol using (Braid ; E356 ; E358)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Base358 using (e-ebe ; e-zxxz ; e-xzzx)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon3 complete₂ using (canon3)
open import Examples.Groups.Real-Clifford+CH.Lemma88.W3.Kit complete₂ using (s12₃ ; rig₃ ; eq138′)
import Examples.Groups.Real-Clifford+CH.GeneralN.RotAnywhereGen as RotAnywhereGen
import Examples.Groups.Real-Clifford+CH.GeneralN.BraidFrom as BraidFrom
import Examples.Groups.Real-Clifford+CH.GeneralN.PairFrom as PairFrom

open Tools (3 VRel,_===_)
open WordAlgebra (3 VRel,_===_) using (comm-inv)

module NX = Conj {3} X X²

private
  R : Bool → Circuit 3
  R = rot {0}

  -- The rotation white on wire 2, resp. wire 1.
  °R ¹R : Bool → Circuit 3
  °R β = N₂.⟪ R β ⟫
  ¹R β = N₁.⟪ R β ⟫

  pass₂ : ∀ {a u v : Circuit 3} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
  pass₂ eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

  -- A left-invertible word cancels on the left.
  lcancel : ∀ {y x u v : Circuit 3} → y • x ≈ ε → x • u ≈ x • v → u ≈ v
  lcancel {y} {x} {u} {v} yx e = begin
    u                ≈⟨ sym left-unit ⟩
    ε • u            ≈⟨ front _ (sym yx) ⟩
    (y • x) • u      ≈⟨ trans assoc (back _ e) ⟩
    y • (x • v)      ≈⟨ trans (sym assoc) (front _ yx) ⟩
    ε • v            ≈⟨ left-unit ⟩
    v ∎

  -- An equation c • w • c ≈ v for an involution c, with c moved over.
  from-conj : ∀ {c w v : Circuit 3} → c • c ≈ ε → c • w • c ≈ v → c • w ≈ v • c
  from-conj {c} {w} {v} c² e = begin
    c • w                   ≈⟨ sym right-unit ⟩
    (c • w) • ε             ≈⟨ back _ (sym c²) ⟩
    (c • w) • (c • c)       ≈⟨ by-passoc ((□ • □) • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
    (c • w • c) • c         ≈⟨ front _ e ⟩
    v • c ∎

  ----------------------------------------------------------------------
  -- Inverses

  R-inv : ∀ β → R β • R (not β) ≈ ε
  R-inv true  = eq117
  R-inv false = eq118

  o117 : °CCZX • °CCXZ ≈ ε
  o117 = trans (sym (N₂.⟪⟫-• CCZX CCXZ)) (trans (N₂.⟪⟫-cong eq117) N₂.⟪⟫-ε)

  o118 : °CCXZ • °CCZX ≈ ε
  o118 = trans (sym (N₂.⟪⟫-• CCXZ CCZX)) (trans (N₂.⟪⟫-cong eq118) N₂.⟪⟫-ε)

  R-comm : ∀ α β → R α • R β ≈ R β • R α
  R-comm true  true  = refl
  R-comm true  false = trans eq117 (sym eq118)
  R-comm false true  = trans eq118 (sym eq117)
  R-comm false false = refl

  -- X on the target turns the rotation over.
  X-V : X • CCXZ ≈ CCZX • X
  X-V = begin
    (H • Z • H) • CCXZ        ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
    H • Z • (H • CCXZ)        ≈⟨ back _ (back _ H↓-CCXZ) ⟩
    H • Z • (CCZX • H)        ≈⟨ back _ (trans (sym assoc) (trans (front _ Z↓-CCZX) assoc)) ⟩
    H • CCXZ • Z • H          ≈⟨ trans (sym assoc) (trans (front _ H↓-CCXZ) assoc) ⟩
    CCZX • H • Z • H ∎

e356₀ : E356 0
e356₀ = trans (sym assoc) (trans (front _ X-V) (trans assoc (trans (back _ X²) right-unit)))

private
  X-flip : ∀ β → X • R β • X ≈ R (not β)
  X-flip false = e356₀
  X-flip true  = trans (NX.⟪⟫-cong (sym e356₀)) (NX.⟪⟫-⟪⟫ CCXZ)

------------------------------------------------------------------------
-- (351)

private
  -- White on wire 2.
  sepTT : R true • °R true ≈ °R true • R true
  sepTT = trans eq137 (sym eq136)

  sepFT : R false • °R true ≈ °R true • R false
  sepFT = sym (comm-inv eq117 eq118 (sym sepTT))

  sep₂ : ∀ α β → R α • °R β ≈ °R β • R α
  sep₂ true  true  = sepTT
  sep₂ false true  = sepFT
  sep₂ true  false = comm-inv o117 o118 sepTT
  sep₂ false false = comm-inv o117 o118 sepFT

  -- The swap of the wires 1 2 fixes the rotations and carries X on wire
  -- 2 to X on wire 1.
  S↑R : ∀ β → S↑.⟪ R β ⟫ ≈ R β
  S↑R β = S↑.⟪⟫-fix (s12₃ β)

  S↑X : S↑.⟪ X ↑ ↑ ⟫ ≈ X ↑
  S↑X = lemma-cong↑ (Ex • X ↑ • Ex) X (by-sem₀ (Ex • X ↑ • Ex) X Eq.refl)

  S↑°R : ∀ β → S↑.⟪ °R β ⟫ ≈ ¹R β
  S↑°R β = S↑.⟪⟫-•₃ S↑X (S↑R β) S↑X

  -- White on wire 1.
  sep₁ : ∀ α β → R α • ¹R β ≈ ¹R β • R α
  sep₁ α β = S↑.⟪⟫-≈ (sep₂ α β) (S↑.⟪⟫-•₂ (S↑R α) (S↑°R β)) (S↑.⟪⟫-•₂ (S↑°R β) (S↑R α))

  -- The merges: the rotation white on wire 2 is the merge over wire 2
  -- times the other rotation, and white on wire 1 the merge over wire 1.
  L₁ O₁ : Bool → Circuit 3
  L₁ β = L (F β 1)
  O₁ β = O (F β 1)

  merge₂ : ∀ β → °R β • R β ≈ L₁ β
  merge₂ true  = eq136
  merge₂ false = eq138′

  mergeL : ∀ β → °R β ≈ L₁ β • R (not β)
  mergeL β = begin
    °R β                        ≈⟨ sym right-unit ⟩
    °R β • ε                    ≈⟨ back _ (sym (R-inv β)) ⟩
    °R β • (R β • R (not β))    ≈⟨ trans (sym assoc) (front _ (merge₂ β)) ⟩
    L₁ β • R (not β) ∎

  mergeO : ∀ β → ¹R β ≈ O₁ β • R (not β)
  mergeO β = S↑.⟪⟫-≈ (mergeL β) (S↑°R β) (S↑.⟪⟫-•₂ (O-L (F β 1)) (S↑R (not β)))

  R-L : ∀ γ β → R γ • L₁ β ≈ L₁ β • R γ
  R-L γ β = trans (back _ (sym (merge₂ β))) (trans (pass₂ (sep₂ γ β) (R-comm γ β)) (front _ (merge₂ β)))

  R-O : ∀ γ β → R γ • O₁ β ≈ O₁ β • R γ
  R-O γ β = S↑.⟪⟫-≈ (R-L γ β) (S↑.⟪⟫-•₂ (S↑R γ) (O-L (F β 1))) (S↑.⟪⟫-•₂ (O-L (F β 1)) (S↑R γ))

  -- The two merges commute: O passes CH • CZ ↓ ((145) under the lower
  -- swap), and L is its square.
  q : Circuit 3
  q = CH • CZ ↓

  q-O : q • O₁ true ≈ O₁ true • q
  q-O = trans assoc (S↓.⟪⟫-≈ eq145 (S↓.⟪⟫-•₃ e₁ e₂ refl) (S↓.⟪⟫-•₃ refl e₁ e₂))
    where
    e₁ : S↓.⟪ HC ↓ ⟫ ≈ CH
    e₁ = L-sem (Ex • HC • Ex) CH Eq.refl
    e₂ : S↓.⟪ CZ ↓ ⟫ ≈ CZ ↓
    e₂ = L-sem (Ex • CZ • Ex) CZ Eq.refl

  L-O₁ : L₁ true • O₁ true ≈ O₁ true • L₁ true
  L-O₁ = trans (front _ Lq) (trans (sym (pass₂ (sym q-O) (sym q-O))) (back _ (sym Lq)))
    where
    Lq : L₁ true ≈ q • q
    Lq = L-sem (ΛZX 1) ((CH • CZ) • (CH • CZ)) Eq.refl

  L-inv : L₁ true • L₁ false ≈ ε
  L-inv = L-sem (ΛZX 1 • ΛXZ 1) ε (Evaluated.same e-zxxz)

  L-inv′ : L₁ false • L₁ true ≈ ε
  L-inv′ = L-sem (ΛXZ 1 • ΛZX 1) ε (Evaluated.same e-xzzx)

  -- The merges over wire 1 are those over wire 2 under the swap.
  O-inv : O₁ true • O₁ false ≈ ε
  O-inv = trans (cong (sym (O-L (ΛZX 1))) (sym (O-L (ΛXZ 1))))
                (trans (sym (S↑.⟪⟫-• (L₁ true) (L₁ false))) (trans (S↑.⟪⟫-cong L-inv) S↑.⟪⟫-ε))

  O-inv′ : O₁ false • O₁ true ≈ ε
  O-inv′ = trans (cong (sym (O-L (ΛXZ 1))) (sym (O-L (ΛZX 1))))
                 (trans (sym (S↑.⟪⟫-• (L₁ false) (L₁ true))) (trans (S↑.⟪⟫-cong L-inv′) S↑.⟪⟫-ε))

  O-L₁ : ∀ β → O₁ true • L₁ β ≈ L₁ β • O₁ true
  O-L₁ true  = sym L-O₁
  O-L₁ false = comm-inv L-inv L-inv′ (sym L-O₁)

  L-O : ∀ α β → L₁ β • O₁ α ≈ O₁ α • L₁ β
  L-O true  β = sym (O-L₁ β)
  L-O false β = comm-inv O-inv O-inv′ (sym (O-L₁ β))

  -- (o r)(l s) ≈ (l s)(o r) from the four commutations it needs.
  swap₄ : ∀ {o r l s : Circuit 3} → r • l ≈ l • r → o • l ≈ l • o → r • s ≈ s • r → s • o ≈ o • s →
          (o • r) • (l • s) ≈ (l • s) • (o • r)
  swap₄ {o} {r} {l} {s} rl ol rs so = begin
    (o • r) • (l • s)      ≈⟨ trans assoc (back _ (trans (sym assoc) (front _ rl))) ⟩
    o • ((l • r) • s)      ≈⟨ trans (sym assoc) (trans (front _ (sym assoc)) (trans (front _ (front _ ol)) assoc)) ⟩
    (l • o) • (r • s)      ≈⟨ back _ rs ⟩
    (l • o) • (s • r)      ≈⟨ trans assoc (back _ (trans (sym assoc) (front _ (sym so)))) ⟩
    l • ((s • o) • r)      ≈⟨ trans (back _ assoc) (sym assoc) ⟩
    (l • s) • (o • r) ∎

  -- White on both wires 1 2, relatively: conjugated by X on wire 1 the
  -- rotations white on wire 1 and on wire 2.
  sep₁₂′ : ∀ α β → ¹R α • °R β ≈ °R β • ¹R α
  sep₁₂′ α β =
    trans (cong (mergeO α) (mergeL β))
          (trans (swap₄ (R-L (not α) β) (sym (L-O α β)) (R-comm (not α) (not β)) (R-O (not β) α))
                 (sym (cong (mergeL β) (mergeO α))))

  x12 : X ↑ ↑ • X ↑ ≈ X ↑ • X ↑ ↑
  x12 = sym (lemma-cong↑ (X • X ↑) (X ↑ • X) (X-↑ X))

  cTFF : ∀ (w : Circuit 3) → N₁.⟪ N₂.⟪ w ⟫ ⟫ ≈ col (true ∷ false ∷ false ∷ []) w
  cTFF w = trans (by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl)
                 (trans (back _ (back _ x12)) (sym (cong (back _ right-unit) (back _ (back _ right-unit)))))

  sep₁₂ : ∀ α β → R α • col (true ∷ false ∷ false ∷ []) (R β) ≈ col (true ∷ false ∷ false ∷ []) (R β) • R α
  sep₁₂ α β = N₁.⟪⟫-≈ (sep₁₂′ α β) (N₁.⟪⟫-•₂ (N₁.⟪⟫-⟪⟫ (R α)) (cTFF (R β))) (N₁.⟪⟫-•₂ (cTFF (R β)) (N₁.⟪⟫-⟪⟫ (R α)))

  c351z : ∀ α β (z : Bits 3) → lookupℕ 0 z ≡ true → lookupℕ 1 z ≡ false →
          R α • col z (R β) ≈ col z (R β) • R α
  c351z α β (true ∷ false ∷ true ∷ []) _ _ = trans (back _ e) (trans (sep₁ α β) (front _ (sym e)))
    where
    e : col (true ∷ false ∷ true ∷ []) (R β) ≈ ¹R β
    e = cong right-unit (back _ right-unit)
  c351z α β (true ∷ false ∷ false ∷ []) _ _ = sep₁₂ α β
  c351z α β (false ∷ _)        () _
  c351z α β (true ∷ true ∷ _)  _  ()

c351₀ : C351 0
c351₀ α β x y x0 y0 d = col-rel x y (c351z α β (combine x y) z0 z1)
  where
  z0 : lookupℕ 0 (combine x y) ≡ true
  z0 = Eq.trans (combine-lookup 0 x y (s≤s z≤n)) (Eq.cong₂ _⇔_ x0 y0)
  z1 : lookupℕ 1 (combine x y) ≡ false
  z1 = Eq.trans (combine-lookup 1 x y (s≤s (s≤s z≤n))) d

------------------------------------------------------------------------
-- (352)

private
  -- The rotation on wire 1.
  ₁R : Bool → Circuit 3
  ₁R β = S↓.⟪ R β ⟫

  Ex-X₂ : Ex • X ↑ ↑ ≈ X ↑ ↑ • Ex
  Ex-X₂ = low-comm Ex X

  -- White on wire 2: Lemma D.2's °CZXC and °CXZC.
  cTTF : ∀ β → col (true ∷ true ∷ false ∷ []) (₁R β) ≈ S↓.⟪ °R β ⟫
  cTTF β = trans (cong right-unit (back _ right-unit)) (conj-swap (sym Ex-X₂) (R β))

  base₂T : ∀ β → R true • S↓.⟪ °R β ⟫ ≈ S↓.⟪ °R β ⟫ • R true
  base₂T true  = eq139
  base₂T false = eq140

  base₂ : ∀ α β → R α • S↓.⟪ °R β ⟫ ≈ S↓.⟪ °R β ⟫ • R α
  base₂ true  β = base₂T β
  base₂ false β = sym (comm-inv eq117 eq118 (sym (base₂T β)))

  -- X on wire 1 is X on the target of the rotation on wire 1.
  S↓X : S↓.⟪ X ⟫ ≈ X ↑
  S↓X = L-sem (Ex • X • Ex) (X ↑) Eq.refl

  x12′ : X ↑ • X ↑ ↑ ≈ X ↑ ↑ • X ↑
  x12′ = sym x12

  flip₁ : ∀ β → N₁.⟪ S↓.⟪ °R β ⟫ ⟫ ≈ S↓.⟪ °R (not β) ⟫
  flip₁ β = begin
    N₁.⟪ S↓.⟪ °R β ⟫ ⟫        ≈⟨ N₁.⟪⟫-cong (conj-swap Ex-X₂ (R β)) ⟩
    N₁.⟪ N₂.⟪ ₁R β ⟫ ⟫        ≈⟨ conj-swap x12′ (₁R β) ⟩
    N₂.⟪ N₁.⟪ ₁R β ⟫ ⟫        ≈⟨ N₂.⟪⟫-cong (sym (S↓.⟪⟫-•₃ S↓X refl S↓X)) ⟩
    N₂.⟪ S↓.⟪ X • R β • X ⟫ ⟫ ≈⟨ N₂.⟪⟫-cong (S↓.⟪⟫-cong (X-flip β)) ⟩
    N₂.⟪ ₁R (not β) ⟫          ≈⟨ sym (conj-swap Ex-X₂ (R (not β))) ⟩
    S↓.⟪ °R (not β) ⟫ ∎

  cTFF₁ : ∀ β → col (true ∷ false ∷ false ∷ []) (₁R β) ≈ S↓.⟪ °R (not β) ⟫
  cTFF₁ β = trans (sym (cTFF (₁R β))) (trans (N₁.⟪⟫-cong (trans (sym (cong right-unit (back _ right-unit))) (cTTF β))) (flip₁ β))

  c352t : ∀ α β z₁ → R α • col (true ∷ z₁ ∷ false ∷ []) (₁R β) ≈ col (true ∷ z₁ ∷ false ∷ []) (₁R β) • R α
  c352t α β true  = trans (back _ (cTTF β)) (trans (base₂ α β) (front _ (sym (cTTF β))))
  c352t α β false = trans (back _ (cTFF₁ β)) (trans (base₂ α (not β)) (front _ (sym (cTFF₁ β))))

  -- A white wire 0 is X on wire 0, which turns the first rotation over.
  colX : ∀ (t : Bits 2) (w : Circuit 3) → col (false ∷ t) w ≈ X • col (true ∷ t) w • X
  colX t w = trans (back _ (back _ (X-↑ (negsB t))))
                   (by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl)

  c352f : ∀ α β z₁ → R α • col (false ∷ z₁ ∷ false ∷ []) (₁R β) ≈ col (false ∷ z₁ ∷ false ∷ []) (₁R β) • R α
  c352f true  β z₁ =
    trans (back _ (colX (z₁ ∷ false ∷ []) (₁R β)))
      (trans (NX.⟪⟫-≈ (c352t false β z₁) (NX.⟪⟫-•₂ (X-flip false) refl) (NX.⟪⟫-•₂ refl (X-flip false)))
             (front _ (sym (colX (z₁ ∷ false ∷ []) (₁R β)))))
  c352f false β z₁ =
    trans (back _ (colX (z₁ ∷ false ∷ []) (₁R β)))
      (trans (NX.⟪⟫-≈ (c352t true β z₁) (NX.⟪⟫-•₂ (X-flip true) refl) (NX.⟪⟫-•₂ refl (X-flip true)))
             (front _ (sym (colX (z₁ ∷ false ∷ []) (₁R β)))))

  c352z : ∀ α β (z : Bits 3) → lookupℕ 2 z ≡ false →
          R α • col z (Ex • R β • Ex) ≈ col z (Ex • R β • Ex) • R α
  c352z α β (true  ∷ z₁ ∷ false ∷ []) _ = c352t α β z₁
  c352z α β (false ∷ z₁ ∷ false ∷ []) _ = c352f α β z₁
  c352z α β (z₀ ∷ z₁ ∷ true ∷ [])     ()

c352₀ : C352 0
c352₀ α β x y x0 y1 d = col-rel x y (c352z α β (combine x y) z2)
  where
  z2 : lookupℕ 2 (combine x y) ≡ false
  z2 = Eq.trans (combine-lookup 2 x y (s≤s (s≤s (s≤s z≤n)))) d

rotcomm₀ : RotComm 0
rotcomm₀ = RotAnywhereGen.rot-comm rig₃ c351₀ c352₀

------------------------------------------------------------------------
-- (358)

private
  a b oa ob D : Circuit 3
  a  = CCXZ
  b  = S↓.⟪ CCZX ⟫
  oa = °CCXZ
  ob = °CZXC
  D  = oa • ob • oa

  sep-aa : a • oa ≈ oa • a
  sep-aa = sep₂ false false

  sep-ab : ob • a ≈ a • ob
  sep-ab = comm-inv eq117 eq118 (sym eq139)

  b-°CCZX : b • °CCZX ≈ °CCZX • b
  b-°CCZX = S↓.⟪⟫-≈ eq139 (S↓.⟪⟫-•₂ refl (S↓.⟪⟫-⟪⟫ °CCZX)) (S↓.⟪⟫-•₂ (S↓.⟪⟫-⟪⟫ °CCZX) refl)

  sep-ba : oa • b ≈ b • oa
  sep-ba = sym (comm-inv o117 o118 b-°CCZX)

  -- The merges over wire 2, and their braid.
  ea : oa • a ≈ L (ΛXZ 1)
  ea = eq138′

  eb : ob • b ≈ L (Ex • ΛZX 1 • Ex)
  eb = trans (sym (S↓.⟪⟫-• °CCZX CCZX)) (S↓.⟪⟫-cong eq136)

  ebe : L (ΛXZ 1) • L (Ex • ΛZX 1 • Ex) • L (ΛXZ 1) ≈ CZ • Ex
  ebe = L-sem (ΛXZ 1 • (Ex • ΛZX 1 • Ex) • ΛXZ 1) (CZ • Ex) (Evaluated.same e-ebe)

  -- The braid of the merges is D times the braid of the rotations.
  D-form : (oa • a) • (ob • b) • (oa • a) ≈ D • (a • b • a)
  D-form = begin
    (oa • a) • (ob • b) • (oa • a)      ≈⟨ by-passoc ((□ • □) • (□ • □) • (□ • □)) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
    oa • (a • ob) • b • oa • a          ≈⟨ back _ (front _ (sym sep-ab)) ⟩
    oa • (ob • a) • b • oa • a          ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) (□ • □ • □ • (□ • □) • □) Eq.refl ⟩
    oa • ob • a • (b • oa) • a          ≈⟨ back _ (back _ (back _ (front _ (sym sep-ba)))) ⟩
    oa • ob • a • (oa • b) • a          ≈⟨ by-passoc (□ • □ • □ • (□ • □) • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    oa • ob • (a • oa) • b • a          ≈⟨ back _ (back _ (front _ sep-aa)) ⟩
    oa • ob • (oa • a) • b • a          ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) ((□ • □ • □) • □ • □ • □) Eq.refl ⟩
    D • (a • b • a) ∎

  D-a : a • D ≈ D • a
  D-a = pass₂ sep-aa (pass₂ (sym sep-ab) sep-aa)

  -- CZ • Ex conjugates the rotation on wire 1 to the one on wire 0
  -- ((357)).
  Kb : (CZ • Ex) • b ≈ a • (CZ • Ex)
  Kb = begin
    (CZ • Ex) • (Ex • CCZX • Ex)      ≈⟨ by-passoc ((□ • □) • (□ • □ • □)) (□ • (□ • □) • □ • □) Eq.refl ⟩
    CZ • (Ex • Ex) • CCZX • Ex        ≈⟨ back _ (trans (front _ Ex²′) left-unit) ⟩
    CZ • CCZX • Ex                    ≈⟨ sym assoc ⟩
    (CZ • CCZX) • Ex                  ≈⟨ front _ (from-conj CZ²′ K-W) ⟩
    (CCXZ • CZ) • Ex                  ≈⟨ assoc ⟩
    CCXZ • (CZ • Ex) ∎
    where
    Ex²′ : Ex • Ex ≈ ε
    Ex²′ = Ex²
    CZ²′ : CZ • CZ ≈ ε
    CZ²′ = CZ²

  oa⁻ ob⁻ D⁻ : Circuit 3
  oa⁻ = °CCZX
  ob⁻ = S↓.⟪ °CCXZ ⟫
  D⁻  = oa⁻ • ob⁻ • oa⁻

  oa-inv : oa⁻ • oa ≈ ε
  oa-inv = o117

  ob-inv : ob⁻ • ob ≈ ε
  ob-inv = trans (sym (S↓.⟪⟫-• °CCXZ °CCZX)) (trans (S↓.⟪⟫-cong o118) S↓.⟪⟫-ε)

  D-inv : D⁻ • D ≈ ε
  D-inv = begin
    (oa⁻ • ob⁻ • oa⁻) • (oa • ob • oa)    ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    oa⁻ • ob⁻ • (oa⁻ • oa) • ob • oa      ≈⟨ back _ (back _ (trans (front _ oa-inv) left-unit)) ⟩
    oa⁻ • ob⁻ • ob • oa                   ≈⟨ back _ (trans (sym assoc) (trans (front _ ob-inv) left-unit)) ⟩
    oa⁻ • oa                              ≈⟨ oa-inv ⟩
    ε ∎

e358₀ : E358 0
e358₀ = sym (lcancel eq117 (trans (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl) (lcancel D-inv step)))
  where
  x : Circuit 3
  x = a • b • a
  ebe′ : D • x ≈ CZ • Ex
  ebe′ = trans (sym D-form) (trans (cong ea (cong eb ea)) ebe)
  -- D x b ≈ D a x, hence x b ≈ a x, hence a (b a b) ≈ a (a b a).
  step : D • (x • b) ≈ D • (a • x)
  step = begin
    D • (x • b)        ≈⟨ sym assoc ⟩
    (D • x) • b        ≈⟨ front _ ebe′ ⟩
    (CZ • Ex) • b      ≈⟨ Kb ⟩
    a • (CZ • Ex)      ≈⟨ back _ (sym ebe′) ⟩
    a • (D • x)        ≈⟨ trans (sym assoc) (trans (front _ D-a) assoc) ⟩
    D • (a • x) ∎

braid₀ : Braid 0
braid₀ = BraidFrom.braid rig₃ e356₀ e358₀

------------------------------------------------------------------------
-- The pair step

private
  B : Circuit 3
  B = CZ₂₀

  xb : X • Λ□ 2 ≈ Λ□ 2 • X
  xb = Canon.x-box canon3

  -- Black: by definition, CCXZ is CZ₂₀ CH CZ₂₀ CH.
  k1b : ∀ β → R β • B ≈ B • R (not β)
  k1b false = by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl
  k1b true  = begin
    (CH • CZ₂₀ • CH • CZ₂₀) • CZ₂₀     ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
    CH • CZ₂₀ • CH • (CZ₂₀ • CZ₂₀)     ≈⟨ back _ (back _ (trans (back _ CZ₂₀²) right-unit)) ⟩
    CH • CZ₂₀ • CH                     ≈⟨ sym (trans (sym assoc) (trans (front _ CZ₂₀²) left-unit)) ⟩
    CZ₂₀ • (CZ₂₀ • CH • CZ₂₀ • CH) ∎

  R-M : ∀ γ → R γ • Z ↑ ↑ ≈ Z ↑ ↑ • R γ
  R-M true  = sym eq121
  R-M false = sym eq122

  -- White on wire 0: the box is the box times the box with wire 0 idle,
  -- the merge on wire 1 under the lower swap.
  S↓X₁ : S↓.⟪ X ↑ ⟫ ≈ X
  S↓X₁ = L-sem (Ex • X ↑ • Ex) X Eq.refl

  S↓Z : S↓.⟪ Z ↑ ↑ ⟫ ≈ Z ↑ ↑
  S↓Z = S↓.⟪⟫-fix (low-comm Ex Z)

  mergeS : B • (X • B • X) ≈ Z ↑ ↑
  mergeS = S↓.⟪⟫-≈ (Canon.merge canon3) (S↓.⟪⟫-•₂ refl (S↓.⟪⟫-•₃ S↓X₁ refl S↓X₁)) S↓Z

  XBX : X • B • X ≈ B • Z ↑ ↑
  XBX = begin
    X • B • X                 ≈⟨ sym left-unit ⟩
    ε • (X • B • X)           ≈⟨ front _ (sym CZ₂₀²) ⟩
    (B • B) • (X • B • X)     ≈⟨ trans assoc (back _ mergeS) ⟩
    B • Z ↑ ↑ ∎

  k1w : ∀ β → R β • (X • B • X) ≈ (X • B • X) • R (not β)
  k1w β = trans (back _ XBX) (trans (sym assoc) (trans (front _ (k1b β)) (trans assoc
            (trans (back _ (R-M (not β))) (trans (sym assoc) (front _ (sym XBX)))))))

  k1t : ∀ β γ → R β • col (γ ∷ true ∷ true ∷ []) B ≈ col (γ ∷ true ∷ true ∷ []) B • R (not β)
  k1t β true  = trans (back _ u) (trans (k1b β) (front _ (sym u)))
    where
    u : col (true ∷ true ∷ true ∷ []) B ≈ B
    u = trans left-unit right-unit
  k1t β false = trans (back _ u) (trans (k1w β) (front _ (sym u)))
    where
    u : col (false ∷ true ∷ true ∷ []) B ≈ X • B • X
    u = cong right-unit (back _ right-unit)

k1₀ : PairCanon 0
k1₀ β γ true  = k1t β γ
k1₀ β γ false = trans (back _ e) (trans (k1t β γ) (front _ (sym e)))
  where
  e : col (γ ∷ false ∷ true ∷ []) B ≈ col (γ ∷ true ∷ true ∷ []) B
  e = col-flip (sF 0F) (γ ∷ true ∷ true ∷ []) (X₁-B xb)

pairstep₀ : PairStep 0
pairstep₀ = PairFrom.pair-step (Canon.swaps canon3) rig₃ k1₀

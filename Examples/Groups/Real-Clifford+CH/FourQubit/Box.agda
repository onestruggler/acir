------------------------------------------------------------------------
-- Presentations of groups
--
-- The three-controlled box on four qubits (Clément, Lemma D.5,
-- Equations (154)–(166))
--
-- The box Λ□ 3 = W c V c, with W = CCZX, V = CCXZ and c the CZ from wire
-- 3, is a sign on wires 1, 2, 3 and the identity on wire 0.  So it passes
-- whatever acts on wire 0 alone — (154)–(156), the four-qubit case of
-- the axiom schema (19) — and the CZ gates onto wire 0, (158), (159);
-- and its controls on wires 1 and 2 can be exchanged, (157).
--
-- The proofs are word algebra (WordAlgebra.box-pass): Z and H on wire 0
-- exchange W and V, and V c W = W c V because V = W d = d W for the CZ d
-- of wires 1 and 2, which passes c.
--
-- The controls on wires 2 and 3 can be exchanged too, (161).  With
-- a = CH ↓, b = CZ₂₀, c = CZ₃₀ the box is the commutator of x = a b a
-- and c, (150), and the claim is that it is also that of y = a c a and
-- b.  The CNOT from wire 3 to wire 2 turns b into b c and fixes a and c,
-- so it carries CCZX² = CZ ↑, a relation of a and b, to one of a and
-- b c; WordAlgebra.comm-swap extracts from the three relations that the
-- box is b y b y, and (159) turns that round.  Then c passes the box as
-- b does, which makes the box c W c V, (165), and so an involution,
-- (166).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Box
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; ax ; CZ² ; CH² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using ( CZ₂₀² ; eq117 ; eq118 ; eq123 ; eq124 ; eq127 ; eq128 ; CCZX² ; CZ↑-CZ₂₀ ; CZ₂₀-Z↓
        ; Z↓-CCZX ; H↓-CCZX ; H↓-CCXZ ; CH↓-CCZX ; CH↓-CCXZ ; S↑-CZ₂₀ )
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

-- The CZ of wires 1 and 2 passes the gates from wire 3 to wire 0.
CZ↑-CZ₃₀ : (₄₊ n) ⊢ CZ ↑ • CZ₃₀ ≈ CZ₃₀ • CZ ↑
CZ↑-CZ₃₀ {n} = begin
  CZ ↑ • CZ₃₀       ≈⟨ back _ CZ₃₀-P ⟩
  U CZ • P₀₃ CZ     ≈⟨ sym (P₀₃-U CZ CZ) ⟩
  P₀₃ CZ • U CZ     ≈⟨ front _ (sym CZ₃₀-P) ⟩
  CZ₃₀ • CZ ↑ ∎
  where open Tools ((₄₊ n) VRel,_===_)

CZ↑-CH₃₀ : (₄₊ n) ⊢ CZ ↑ • CH₃₀ ≈ CH₃₀ • CZ ↑
CZ↑-CH₃₀ {n} = begin
  CZ ↑ • CH₃₀       ≈⟨ back _ CH₃₀-P ⟩
  U CZ • P₀₃ CH     ≈⟨ sym (P₀₃-U CH CZ) ⟩
  P₀₃ CH • U CZ     ≈⟨ front _ (sym CH₃₀-P) ⟩
  CH₃₀ • CZ ↑ ∎
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- V c W = W c V

private
  -- CCXZ is CCZX times the CZ of its controls, either way round.
  V-Wd : (₄₊ n) ⊢ CCXZ ≈ CCZX • CZ ↑
  V-Wd {n} = sym eq124
    where open Tools ((₄₊ n) VRel,_===_)

  V-dW : (₄₊ n) ⊢ CCXZ ≈ CZ ↑ • CCZX
  V-dW {n} = begin
    CCXZ                      ≈⟨ sym eq124 ⟩
    CCZX • CZ ↑               ≈⟨ back _ (sym CCZX²) ⟩
    CCZX • CCZX • CCZX        ≈⟨ sym assoc ⟩
    (CCZX • CCZX) • CCZX      ≈⟨ front _ CCZX² ⟩
    CZ ↑ • CCZX ∎
    where open Tools ((₄₊ n) VRel,_===_)

  -- The CZ of wires 1 and 2 passes the gates from wire 3 to wire 0.
  d-c : (₄₊ n) ⊢ CZ ↑ • CZ₃₀ ≈ CZ₃₀ • CZ ↑
  d-c = CZ↑-CZ₃₀

  d-e : (₄₊ n) ⊢ CZ ↑ • CH₃₀ ≈ CH₃₀ • CZ ↑
  d-e = CZ↑-CH₃₀

  flip-c : (₄₊ n) ⊢ CCXZ • CZ₃₀ • CCZX ≈ CCZX • CZ₃₀ • CCXZ
  flip-c {n} = flip-WcV V-Wd V-dW d-c
    where open Alg ((₄₊ n) VRel,_===_)

  flip-e : (₄₊ n) ⊢ CCXZ • CH₃₀ • CCZX ≈ CCZX • CH₃₀ • CCXZ
  flip-e {n} = flip-WcV V-Wd V-dW d-e
    where open Alg ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (154)–(156): the box wire is an identity wire

private
  -- Z and H on wire 0 pass the CZ and the CH from wire 3.
  z-c : (₄₊ n) ⊢ Z ↓ • CZ₃₀ ≈ CZ₃₀ • Z ↓
  z-c {n} = begin
    Z ↓ • CZ₃₀        ≈⟨ back _ CZ₃₀-P ⟩
    Z ↓ • P₀₃ CZ      ≈⟨ sym (comm-03-01 CZ (Z ↓) (evaluated Eq.refl)) ⟩
    P₀₃ CZ • Z ↓      ≈⟨ front _ (sym CZ₃₀-P) ⟩
    CZ₃₀ • Z ↓ ∎
    where open Tools ((₄₊ n) VRel,_===_)

  h-e : (₄₊ n) ⊢ H ↓ • CH₃₀ ≈ CH₃₀ • H ↓
  h-e {n} = begin
    H ↓ • CH₃₀        ≈⟨ back _ CH₃₀-P ⟩
    H ↓ • P₀₃ CH      ≈⟨ sym (comm-03-01 CH (H ↓) (evaluated Eq.refl)) ⟩
    P₀₃ CH • H ↓      ≈⟨ front _ (sym CH₃₀-P) ⟩
    CH₃₀ • H ↓ ∎
    where open Tools ((₄₊ n) VRel,_===_)

-- (154): the four-qubit case of the schema (19).
eq154 : (₄₊ n) ⊢ Z ↓ • box₃ ≈ box₃ • Z ↓
eq154 {n} = box-pass Z↓-CCZX eq123 z-c flip-c
  where open Alg ((₄₊ n) VRel,_===_)

-- (155)
eq155 : (₄₊ n) ⊢ H ↓ • box₃ ≈ box₃ • H ↓
eq155 {n} = begin
  H ↓ • box₃                         ≈⟨ back _ eq153 ⟩
  H ↓ • (CCZX • CH₃₀ • CCXZ • CH₃₀)       ≈⟨ box-pass H↓-CCZX H↓-CCXZ h-e flip-e ⟩
  (CCZX • CH₃₀ • CCXZ • CH₃₀) • H ↓       ≈⟨ front _ (sym eq153) ⟩
  box₃ • H ↓ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

-- (156)
eq156 : (₄₊ n) ⊢ X ↓ • box₃ ≈ box₃ • X ↓
eq156 {n} = sym (comm-• (sym eq155) (comm-• (sym eq154) (sym eq155)))
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (157): the controls on wires 1 and 2 can be exchanged

eq157 : (₄₊ n) ⊢ Ex ↑ • box₃ • Ex ↑ ≈ box₃
eq157 {n} = S₁₂.⟪⟫-•₄ S-W S-c S-V S-c
  where
  open Tools ((₄₊ n) VRel,_===_)
  S-W : (₄₊ n) ⊢ S₁₂.⟪ CCZX ⟫ ≈ CCZX
  S-W = S₁₂.⟪⟫-fix (sym eq127)
  S-d : (₄₊ n) ⊢ S₁₂.⟪ CZ ↑ ⟫ ≈ CZ ↑
  S-d = U-sem (Ex • CZ • Ex) CZ Eq.refl
  S-V : (₄₊ n) ⊢ S₁₂.⟪ CCXZ ⟫ ≈ CCXZ
  S-V = begin
    S₁₂.⟪ CCXZ ⟫           ≈⟨ S₁₂.⟪⟫-cong (sym eq124) ⟩
    S₁₂.⟪ CCZX • CZ ↑ ⟫    ≈⟨ S₁₂.⟪⟫-•₂ S-W S-d ⟩
    CCZX • CZ ↑            ≈⟨ eq124 ⟩
    CCXZ ∎
  S-c : (₄₊ n) ⊢ S₁₂.⟪ CZ₃₀ ⟫ ≈ CZ₃₀
  S-c = begin
    S₁₂.⟪ CZ₃₀ ⟫       ≈⟨ S₁₂.⟪⟫-cong CZ₃₀-P ⟩
    S₁₂.⟪ P₀₃ CZ ⟫     ≈⟨ S₁₂.⟪⟫-fix (sym (P₀₃-U CZ Ex)) ⟩
    P₀₃ CZ             ≈⟨ sym CZ₃₀-P ⟩
    CZ₃₀ ∎

------------------------------------------------------------------------
-- (158), (159): the outer CZ gates pass the box

-- (159)
eq159 : (₄₊ n) ⊢ CZ₂₀ • box₃ ≈ box₃ • CZ₂₀
eq159 {n} = box-pass₂ (invol-comm d² CZ₂₀² CZ↑-CZ₂₀) eq117 eq118 CZ₂₀² eq128 t-c b-c
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)
  d² : (₄₊ n) ⊢ CZ ↑ • CZ ↑ ≈ ε
  d² = lemma-cong↑ (CZ • CZ) ε CZ²
  b-c : (₄₊ n) ⊢ CZ₂₀ • CZ₃₀ ≈ CZ₃₀ • CZ₂₀
  b-c = sym CZ₃₀-CZ₂₀
  t-c : (₄₊ n) ⊢ (CZ ↑ • CZ₂₀) • CZ₃₀ ≈ CZ₃₀ • (CZ ↑ • CZ₂₀)
  t-c = sym (comm-• (sym d-c) (sym b-c))

-- (158)
eq158 : (₄₊ n) ⊢ °CZ₂₀ • box₃ ≈ box₃ • °CZ₂₀
eq158 {n} = begin
  °CZ₂₀ • box₃             ≈⟨ front _ CZ₂₀-Z↓ ⟩
  (CZ₂₀ • Z ↓) • box₃      ≈⟨ sym (comm-• (sym eq159) (sym eq154)) ⟩
  box₃ • (CZ₂₀ • Z ↓)      ≈⟨ back _ (sym CZ₂₀-Z↓) ⟩
  box₃ • °CZ₂₀ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (160): the lower CZ passes the box

eq160 : (₄₊ n) ⊢ CZ ↓ • box₃ ≈ box₃ • CZ ↓
eq160 {n} = S₁₂.⟪⟫-≈ eq159 (S₁₂.⟪⟫-•₂ S↑-CZ₂₀ eq157) (S₁₂.⟪⟫-•₂ eq157 S↑-CZ₂₀)

------------------------------------------------------------------------
-- (163): so does the lower CH

private
  a-e : (₄₊ n) ⊢ CH ↓ • CH₃₀ ≈ CH₃₀ • CH ↓
  a-e {n} = begin
    CH ↓ • CH₃₀       ≈⟨ back _ CH₃₀-P ⟩
    CH ↓ • P₀₃ CH     ≈⟨ sym (comm-03-01 CH CH (evaluated Eq.refl)) ⟩
    P₀₃ CH • CH ↓     ≈⟨ front _ (sym CH₃₀-P) ⟩
    CH₃₀ • CH ↓ ∎
    where open Tools ((₄₊ n) VRel,_===_)

eq163 : (₄₊ n) ⊢ CH ↓ • box₃ ≈ box₃ • CH ↓
eq163 {n} = begin
  CH ↓ • box₃                             ≈⟨ back _ eq153 ⟩
  CH ↓ • (CCZX • CH₃₀ • CCXZ • CH₃₀)      ≈⟨ box-pass CH↓-CCZX CH↓-CCXZ a-e flip-e ⟩
  (CCZX • CH₃₀ • CCXZ • CH₃₀) • CH ↓      ≈⟨ front _ (sym eq153) ⟩
  box₃ • CH ↓ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (161): the controls on wires 2 and 3 can be exchanged

private
  -- The CNOT from wire 3 to wire 2, as a conjugation.
  N² : (₄₊ n) ⊢ P₂₃ CX • P₂₃ CX ≈ ε
  N² {n} = lemma-cong↑ (CX ↑ • CX ↑) ε (lemma-cong↑ (CX • CX) ε (by-sem (CX • CX) ε Eq.refl))

module N₂₃ {n : ℕ} = Conj {₄₊ n} (P₂₃ CX) N²

private
  -- On three wires: the CNOT from the top wire to the middle one turns
  -- the CZ of the lower pair into the two CZ gates onto the bottom wire.
  nbn : Evaluated (U₀ CX • L₀ CZ • U₀ CX) (L₀ CZ • O₀ CZ)
  nbn = evaluated Eq.refl

  N-a : (₄₊ n) ⊢ N₂₃.⟪ CH ↓ ⟫ ≈ CH ↓
  N-a {n} = N₂₃.⟪⟫-fix (P₂₃-L CX CH)

  N-b : (₄₊ n) ⊢ N₂₃.⟪ CZ₂₀ ⟫ ≈ CZ₂₀ • CZ₃₀
  N-b {n} = begin
    P₂₃ CX • CZ₂₀ • P₂₃ CX
      ≈⟨ sym (S₀₁.⟪⟫-•₃ (P₂₃-S₀₁ CX) refl (P₂₃-S₀₁ CX)) ⟩
    O₃ (U₀ CX • L₀ CZ • U₀ CX)
      ≈⟨ O₃-sem (U₀ CX • L₀ CZ • U₀ CX) (L₀ CZ • O₀ CZ) (Evaluated.same nbn) ⟩
    O₃ (L₀ CZ • O₀ CZ)
      ≈⟨ S₀₁.⟪⟫-• (CZ ↑) (P₁₃ CZ) ⟩
    CZ₂₀ • P₀₃ CZ
      ≈⟨ back _ (sym CZ₃₀-P) ⟩
    CZ₂₀ • CZ₃₀ ∎
    where open Tools ((₄₊ n) VRel,_===_)

  N-d : (₄₊ n) ⊢ N₂₃.⟪ CZ ↑ ⟫ ≈ CZ ↑ • P₁₃ CZ
  N-d = U₃-sem (U₀ CX • L₀ CZ • U₀ CX) (L₀ CZ • O₀ CZ) (Evaluated.same nbn)

  x₃ y₃ : Circuit (₄₊ n)
  x₃ = CH ↓ • CZ₂₀ • CH ↓
  y₃ = CH ↓ • CZ₃₀ • CH ↓

  -- The upper swap exchanges b and c, and x and y.
  S-a : (₄₊ n) ⊢ S₂₃.⟪ CH ↓ ⟫ ≈ CH ↓
  S-a = L-S₂₃ CH

  S-b : (₄₊ n) ⊢ S₂₃.⟪ CZ₂₀ ⟫ ≈ CZ₃₀
  S-b {n} = trans (O-S₂₃ CZ) (sym CZ₃₀-P)
    where open Tools ((₄₊ n) VRel,_===_)

  Ex↑↑² : (₄₊ n) ⊢ Ex ↑ ↑ • Ex ↑ ↑ ≈ ε
  Ex↑↑² = lemma-cong↑ (Ex ↑ • Ex ↑) ε (lemma-cong↑ (Ex • Ex) ε Ex²)

  S-c : (₄₊ n) ⊢ S₂₃.⟪ CZ₃₀ ⟫ ≈ CZ₂₀
  S-c {n} = conj-sym Ex↑↑² S-b
    where open Tools ((₄₊ n) VRel,_===_)

  x₃² : (₄₊ n) ⊢ x₃ • x₃ ≈ ε
  x₃² {n} = conj-invol CH² CZ₂₀²
    where open Tools ((₄₊ n) VRel,_===_)

  y₃² : (₄₊ n) ⊢ y₃ • y₃ ≈ ε
  y₃² {n} = conj-invol CH² CZ₃₀²
    where open Tools ((₄₊ n) VRel,_===_)

  d² : (₄₊ n) ⊢ CZ ↑ • CZ ↑ ≈ ε
  d² = lemma-cong↑ (CZ • CZ) ε CZ²

  d′² : (₄₊ n) ⊢ P₁₃ CZ • P₁₃ CZ ≈ ε
  d′² = lemma-cong↑ (CZ₂₀ • CZ₂₀) ε CZ₂₀²

  x-y : (₄₊ n) ⊢ x₃ • y₃ ≈ y₃ • x₃
  x-y {n} = begin
    (CH ↓ • CZ₂₀ • CH ↓) • (CH ↓ • CZ₃₀ • CH ↓)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    CH ↓ • CZ₂₀ • (CH ↓ • CH ↓) • CZ₃₀ • CH ↓
      ≈⟨ back _ (back _ (cancelˢ _ CH²)) ⟩
    CH ↓ • CZ₂₀ • CZ₃₀ • CH ↓
      ≈⟨ back _ (trans (sym assoc) (trans (front _ (sym CZ₃₀-CZ₂₀)) assoc)) ⟩
    CH ↓ • CZ₃₀ • CZ₂₀ • CH ↓
      ≈⟨ back _ (back _ (sym (cancelˢ _ CH²))) ⟩
    CH ↓ • CZ₃₀ • (CH ↓ • CH ↓) • CZ₂₀ • CH ↓
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
    (CH ↓ • CZ₃₀ • CH ↓) • (CH ↓ • CZ₂₀ • CH ↓) ∎
    where open Tools ((₄₊ n) VRel,_===_)

  d-y : (₄₊ n) ⊢ CZ ↑ • y₃ ≈ y₃ • CZ ↑
  d-y {n} = comm-• (ax comm-CZ↑-CH↓) (comm-• d-c (ax comm-CZ↑-CH↓))
    where open Alg ((₄₊ n) VRel,_===_)

  d′-b : (₄₊ n) ⊢ P₁₃ CZ • CZ₂₀ ≈ CZ₂₀ • P₁₃ CZ
  d′-b = P₁₃-O CZ CZ

  -- CCZX² = CZ ↑ in terms of x and b, and its images under the upper swap
  -- and under the CNOT.
  xbxb : (₄₊ n) ⊢ x₃ • CZ₂₀ • x₃ • CZ₂₀ ≈ CZ ↑
  xbxb {n} = trans (by-assoc Eq.refl) CCZX²
    where open Tools ((₄₊ n) VRel,_===_)

  ycyc : (₄₊ n) ⊢ y₃ • CZ₃₀ • y₃ • CZ₃₀ ≈ P₁₃ CZ
  ycyc {n} = S₂₃.⟪⟫-≈ xbxb (S₂₃.⟪⟫-•₄ S-x S-b S-x S-b) (U-S₂₃ CZ)
    where
    S-x : (₄₊ n) ⊢ S₂₃.⟪ x₃ ⟫ ≈ y₃
    S-x = S₂₃.⟪⟫-•₃ S-a S-b S-a

  SS : (₄₊ n) ⊢ (x₃ • y₃ • CZ₂₀ • CZ₃₀) • (x₃ • y₃ • CZ₂₀ • CZ₃₀) ≈ CZ ↑ • P₁₃ CZ
  SS {n} = begin
    (x₃ • y₃ • CZ₂₀ • CZ₃₀) • (x₃ • y₃ • CZ₂₀ • CZ₃₀)
      ≈⟨ cong form form ⟩
    N₂₃.⟪ CCZX ⟫ • N₂₃.⟪ CCZX ⟫
      ≈⟨ sym (N₂₃.⟪⟫-• CCZX CCZX) ⟩
    N₂₃.⟪ CCZX • CCZX ⟫
      ≈⟨ N₂₃.⟪⟫-cong CCZX² ⟩
    N₂₃.⟪ CZ ↑ ⟫
      ≈⟨ N-d ⟩
    CZ ↑ • P₁₃ CZ ∎
    where
    open Tools ((₄₊ n) VRel,_===_)
    form : (₄₊ n) ⊢ x₃ • y₃ • CZ₂₀ • CZ₃₀ ≈ N₂₃.⟪ CCZX ⟫
    form = begin
      (CH ↓ • CZ₂₀ • CH ↓) • (CH ↓ • CZ₃₀ • CH ↓) • CZ₂₀ • CZ₃₀
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □) • □ • □) (□ • □ • (□ • □) • □ • □ • □ • □) Eq.refl ⟩
      CH ↓ • CZ₂₀ • (CH ↓ • CH ↓) • CZ₃₀ • CH ↓ • CZ₂₀ • CZ₃₀
        ≈⟨ back _ (back _ (cancelˢ _ CH²)) ⟩
      CH ↓ • CZ₂₀ • CZ₃₀ • CH ↓ • CZ₂₀ • CZ₃₀
        ≈⟨ by-passoc (□ • □ • □ • □ • □ • □) (□ • (□ • □) • □ • (□ • □)) Eq.refl ⟩
      CH ↓ • (CZ₂₀ • CZ₃₀) • CH ↓ • (CZ₂₀ • CZ₃₀)
        ≈⟨ sym (N₂₃.⟪⟫-•₄ N-a N-b N-a N-b) ⟩
      N₂₃.⟪ CCZX ⟫ ∎

  -- The box as the commutator of x and c, and of b and y.
  box-xc : (₄₊ n) ⊢ box₃ ≈ x₃ • CZ₃₀ • x₃ • CZ₃₀
  box-xc {n} = trans eq150 (by-assoc Eq.refl)
    where open Tools ((₄₊ n) VRel,_===_)

  box-by : (₄₊ n) ⊢ box₃ ≈ CZ₂₀ • y₃ • CZ₂₀ • y₃
  box-by {n} = trans box-xc
    (comm-swap x₃² y₃² CZ₂₀² CZ₃₀² d² d′² x-y (sym CZ₃₀-CZ₂₀) d-y d′-b xbxb ycyc SS)
    where
    open Tools ((₄₊ n) VRel,_===_)
    open Alg ((₄₊ n) VRel,_===_)

  box-yb : (₄₊ n) ⊢ box₃ ≈ y₃ • CZ₂₀ • y₃ • CZ₂₀
  box-yb {n} = begin
    box₃
      ≈⟨ insertˡ _ CZ₂₀² ⟩
    CZ₂₀ • CZ₂₀ • box₃
      ≈⟨ back _ eq159 ⟩
    CZ₂₀ • box₃ • CZ₂₀
      ≈⟨ back _ (front _ box-by) ⟩
    CZ₂₀ • (CZ₂₀ • y₃ • CZ₂₀ • y₃) • CZ₂₀
      ≈⟨ by-passoc (□ • (□ • □ • □ • □) • □) ((□ • □) • □ • □ • □ • □) Eq.refl ⟩
    (CZ₂₀ • CZ₂₀) • y₃ • CZ₂₀ • y₃ • CZ₂₀
      ≈⟨ cancelˢ _ CZ₂₀² ⟩
    y₃ • CZ₂₀ • y₃ • CZ₂₀ ∎
    where open Tools ((₄₊ n) VRel,_===_)

-- (161)
eq161 : (₄₊ n) ⊢ Ex ↑ ↑ • box₃ • Ex ↑ ↑ ≈ box₃
eq161 {n} = begin
  S₂₃.⟪ box₃ ⟫
    ≈⟨ S₂₃.⟪⟫-cong box-xc ⟩
  S₂₃.⟪ x₃ • CZ₃₀ • x₃ • CZ₃₀ ⟫
    ≈⟨ S₂₃.⟪⟫-•₄ S-x S-c S-x S-c ⟩
  y₃ • CZ₂₀ • y₃ • CZ₂₀
    ≈⟨ sym box-yb ⟩
  box₃ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  S-x : (₄₊ n) ⊢ S₂₃.⟪ x₃ ⟫ ≈ y₃
  S-x = S₂₃.⟪⟫-•₃ S-a S-b S-a

-- (162): the same for the doubly controlled H on wire 1, the box of
-- Definition 2.4 between two P ⊗ P.
eq162 : (₄₊ n) ⊢ Ex ↑ ↑ • (ΛH 2 ↓ᵏ n) • Ex ↑ ↑ ≈ ΛH 2 ↓ᵏ n
eq162 {n} = S₂₃.⟪⟫-•₃ (L-S₂₃ PP) eq161 (L-S₂₃ PP)

------------------------------------------------------------------------
-- (165), (166): the box is an involution

-- The CZ from wire 3 passes the box, as the one from wire 2 does.
CZ₃₀-box : (₄₊ n) ⊢ CZ₃₀ • box₃ ≈ box₃ • CZ₃₀
CZ₃₀-box {n} = S₂₃.⟪⟫-≈ eq159 (S₂₃.⟪⟫-•₂ S-b eq161) (S₂₃.⟪⟫-•₂ eq161 S-b)

-- (165)
eq165 : (₄₊ n) ⊢ box₃ ≈ CZ₃₀ • CCZX • CZ₃₀ • CCXZ
eq165 {n} = begin
  box₃
    ≈⟨ insertˡ _ CZ₃₀² ⟩
  CZ₃₀ • CZ₃₀ • box₃
    ≈⟨ back _ CZ₃₀-box ⟩
  CZ₃₀ • (CCZX • CZ₃₀ • CCXZ • CZ₃₀) • CZ₃₀
    ≈⟨ by-passoc (□ • (□ • □ • □ • □) • □) (□ • □ • □ • □ • (□ • □)) Eq.refl ⟩
  CZ₃₀ • CCZX • CZ₃₀ • CCXZ • (CZ₃₀ • CZ₃₀)
    ≈⟨ back _ (back _ (back _ (cancelᵉ _ CZ₃₀²))) ⟩
  CZ₃₀ • CCZX • CZ₃₀ • CCXZ ∎
  where open Tools ((₄₊ n) VRel,_===_)

-- (166)
eq166 : (₄₊ n) ⊢ box₃ • box₃ ≈ ε
eq166 {n} = begin
  box₃ • box₃
    ≈⟨ back _ eq165 ⟩
  (CCZX • CZ₃₀ • CCXZ • CZ₃₀) • (CZ₃₀ • CCZX • CZ₃₀ • CCXZ)
    ≈⟨ by-passoc ((□ • □ • □ • □) • (□ • □ • □ • □)) ((((□ • □) • □) • □) • (□ • (□ • (□ • □)))) Eq.refl ⟩
  (((CCZX • CZ₃₀) • CCXZ) • CZ₃₀) • (CZ₃₀ • (CCZX • (CZ₃₀ • CCXZ)))
    ≈⟨ unwrap′ CZ₃₀² (unwrap′ eq118 (unwrap′ CZ₃₀² eq117)) ⟩
  ε ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

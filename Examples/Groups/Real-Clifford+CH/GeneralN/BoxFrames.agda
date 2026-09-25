------------------------------------------------------------------------
-- Presentations of groups
--
-- The box placed by a swap network, and three boxes on two box wires
--
-- A box with its box wire anywhere and controls of either colour is
-- `boxF u s`: the box Λ□ of the full width conjugated by a network u
-- (`pl u`) — its box wire is the wire u brings to wire 0 — and by X on
-- the wires where the bitstring s is false.  Everything here follows
-- from six facts about the box at the canonical position, the record
-- `Canon`: it is an involution, X on its box wire passes it, it passes
-- every network on its controls ((307)), merging it with its version
-- negated on wire 1 leaves the box on the other wires ((309)), that box
-- does not see the swap of the wires 0 1 ((274)), and it commutes with
-- its image under that swap ((336)).
--
-- `frame-eq`: two networks bringing the same wire to wire 0 place the
-- same box — the rest of the network permutes the controls.  So a
-- statement at the canonical position is carried to any two wires by
-- one network (`σ-for`), and X by `NetWires.X-net`.  The statement
-- carried here is Lemma 8.4's step (Appendix E.2): with p ≠ q,
--
--   box(q; α on p) • box(p; β̄ on q) • box(q; ᾱ on p) ≈ box(p; β on q),
--
-- the other controls alike (`three-boxes`); at the canonical position it
-- is (336), (309), (274), (309) and (311) (`TB₀`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (Σ ; _×_ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Symmetric.Interpretation using (⟦↑⟧)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex² ; X² ; X²↑)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; perm)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑ ; swapX ; swapX′)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires

------------------------------------------------------------------------
-- The canonical facts

record Canon (m : ℕ) : Set where
  field
    invol   : (₃₊ m) ⊢ Λ□ (₂₊ m) • Λ□ (₂₊ m) ≈ ε
    x-box   : (₃₊ m) ⊢ X • Λ□ (₂₊ m) ≈ Λ□ (₂₊ m) • X
    swaps   : ∀ (w : Word (S.Gen (₂₊ m))) → (₃₊ m) ⊢ net w ↑ • Λ□ (₂₊ m) ≈ Λ□ (₂₊ m) • net w ↑
    merge   : (₃₊ m) ⊢ Λ□ (₂₊ m) • (X ↑ • Λ□ (₂₊ m) • X ↑) ≈ Λ□ (₁₊ m) ↑
    wire274 : (₃₊ m) ⊢ Ex • Λ□ (₁₊ m) ↑ • Ex ≈ Λ□ (₁₊ m) ↑
    comm336 : (₃₊ m) ⊢ Λ□ (₂₊ m) • (Ex • Λ□ (₂₊ m) • Ex) ≈ (Ex • Λ□ (₂₊ m) • Ex) • Λ□ (₂₊ m)

------------------------------------------------------------------------
-- Placing by a network

-- u • g • u⁻¹.
pl : ∀ {n} → Word (S.Gen n) → Circuit n → Circuit n
pl u g = net u • g • net (revS u)

module _ {n : ℕ} where
  open Tools (n VRel,_===_)

  pl-cong : ∀ (u : Word (S.Gen n)) {a b : Circuit n} → a ≈ b → pl u a ≈ pl u b
  pl-cong u e = back _ (front _ e)

  pl-• : ∀ (u : Word (S.Gen n)) (a b : Circuit n) → pl u (a • b) ≈ pl u a • pl u b
  pl-• u a b = sym (begin
    (net u • a • net (revS u)) • (net u • b • net (revS u))
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
    net u • a • ((net (revS u) • net u) • b • net (revS u))
      ≈⟨ back _ (back _ (trans (front _ (net-inv′ u)) left-unit)) ⟩
    net u • a • (b • net (revS u))
      ≈⟨ back _ (sym assoc) ⟩
    net u • (a • b) • net (revS u) ∎)

  -- Through three factors, each rewritten.
  pl-•₃ : ∀ (u : Word (S.Gen n)) {a b c a′ b′ c′ : Circuit n} →
          pl u a ≈ a′ → pl u b ≈ b′ → pl u c ≈ c′ → pl u (a • b • c) ≈ a′ • b′ • c′
  pl-•₃ u {a} {b} {c} ea eb ec =
    trans (pl-• u a (b • c)) (cong ea (trans (pl-• u b c) (cong eb ec)))

  -- A word passing a and b passes their product; conjugating by an
  -- involution that passes w gives w back.
  pass : ∀ {a x y : Circuit n} → a • x ≈ x • a → a • y ≈ y • a → a • (x • y) ≈ (x • y) • a
  pass {a} {x} {y} ex ey = begin
    a • (x • y)   ≈⟨ sym assoc ⟩
    (a • x) • y   ≈⟨ front _ ex ⟩
    (x • a) • y   ≈⟨ assoc ⟩
    x • (a • y)   ≈⟨ back _ ey ⟩
    x • (y • a)   ≈⟨ sym assoc ⟩
    (x • y) • a ∎

  unconj′ : ∀ {a w : Circuit n} → a • a ≈ ε → a • w ≈ w • a → a • w • a ≈ w
  unconj′ {a} {w} aa e = begin
    a • w • a      ≈⟨ sym assoc ⟩
    (a • w) • a    ≈⟨ front _ e ⟩
    (w • a) • a    ≈⟨ cancelʳ w aa ⟩
    w ∎

------------------------------------------------------------------------
-- Everything from the canonical facts

module Frames {m : ℕ} (C : Canon m) where
  open Canon C

  private
    N : ℕ
    N = ₃₊ m

    Λ Λ′ B W : Circuit N
    Λ  = Λ□ (₂₊ m)
    Λ′ = Λ□ (₁₊ m) ↑
    B  = Ex • Λ • Ex
    W  = X ↑ • Λ • X ↑

  open Tools (N VRel,_===_)

  --------------------------------------------------------------------
  -- At the canonical position

  private
    X↑-B : X ↑ • B ≈ B • X ↑
    X↑-B = begin
      X ↑ • (Ex • Λ • Ex)     ≈⟨ sym assoc ⟩
      (X ↑ • Ex) • Λ • Ex     ≈⟨ front _ swapX ⟩
      (Ex • X) • Λ • Ex       ≈⟨ assoc ⟩
      Ex • X • Λ • Ex         ≈⟨ back _ (trans (sym assoc) (front _ x-box)) ⟩
      Ex • (Λ • X) • Ex       ≈⟨ back _ (trans assoc (back _ (sym swapX′))) ⟩
      Ex • Λ • (Ex • X ↑)     ≈⟨ by-passoc (□ • □ • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
      (Ex • Λ • Ex) • X ↑ ∎

    XX↑ : X • X ↑ ≈ X ↑ • X
    XX↑ = X-↑ X

    P² : (X • X ↑) • (X • X ↑) ≈ ε
    P² = begin
      (X • X ↑) • (X • X ↑)   ≈⟨ back _ XX↑ ⟩
      (X • X ↑) • (X ↑ • X)   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
      X • (X ↑ • X ↑) • X     ≈⟨ back _ (trans (front _ X²↑) left-unit) ⟩
      X • X                   ≈⟨ X² ⟩
      ε ∎

  module P = Conj {N} (X • X ↑) P²

  private
    PΛ : P.⟪ Λ ⟫ ≈ W
    PΛ = begin
      (X • X ↑) • Λ • (X • X ↑)       ≈⟨ back _ (back _ XX↑) ⟩
      (X • X ↑) • Λ • (X ↑ • X)       ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      X • W • X                       ≈⟨ unconj′ X² (pass XX↑ (pass x-box XX↑)) ⟩
      W ∎

    PB : P.⟪ B ⟫ ≈ X • B • X
    PB = begin
      (X • X ↑) • B • (X • X ↑)       ≈⟨ back _ (back _ XX↑) ⟩
      (X • X ↑) • B • (X ↑ • X)       ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      X • (X ↑ • B • X ↑) • X         ≈⟨ back _ (front _ (unconj′ X²↑ X↑-B)) ⟩
      X • B • X ∎

    -- (336) with the colours of the three-box step.
    C336 : W • (X • B • X) ≈ (X • B • X) • W
    C336 = P.⟪⟫-≈ comm336 (P.⟪⟫-•₂ PΛ PB) (P.⟪⟫-•₂ PB PΛ)

    XBX-form : X • B • X ≈ Ex • W • Ex
    XBX-form = begin
      X • (Ex • Λ • Ex) • X           ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (X • Ex) • Λ • (Ex • X)         ≈⟨ cong (sym swapX′) (back _ (sym swapX)) ⟩
      (Ex • X ↑) • Λ • (X ↑ • Ex)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      Ex • W • Ex ∎

    B-XBX : B • (X • B • X) ≈ Λ′
    B-XBX = begin
      B • (X • B • X)                 ≈⟨ back _ XBX-form ⟩
      (Ex • Λ • Ex) • (Ex • W • Ex)   ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
      Ex • Λ • ((Ex • Ex) • W • Ex)   ≈⟨ back _ (back _ (trans (front _ Ex²) left-unit)) ⟩
      Ex • Λ • (W • Ex)               ≈⟨ back _ (sym assoc) ⟩
      Ex • (Λ • W) • Ex               ≈⟨ back _ (front _ merge) ⟩
      Ex • Λ′ • Ex                    ≈⟨ wire274 ⟩
      Λ′ ∎

    B² : B • B ≈ ε
    B² = begin
      (Ex • Λ • Ex) • (Ex • Λ • Ex)   ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
      Ex • Λ • ((Ex • Ex) • Λ • Ex)   ≈⟨ back _ (back _ (trans (front _ Ex²) left-unit)) ⟩
      Ex • Λ • (Λ • Ex)               ≈⟨ back _ (trans (sym assoc) (trans (front _ invol) left-unit)) ⟩
      Ex • Ex                         ≈⟨ Ex² ⟩
      ε ∎

    XBX² : (X • B • X) • (X • B • X) ≈ ε
    XBX² = begin
      (X • B • X) • (X • B • X)       ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
      X • B • ((X • X) • B • X)       ≈⟨ back _ (back _ (trans (front _ X²) left-unit)) ⟩
      X • B • (B • X)                 ≈⟨ back _ (trans (sym assoc) (trans (front _ B²) left-unit)) ⟩
      X • X                           ≈⟨ X² ⟩
      ε ∎

  -- The three-box step at the canonical position.
  TB₀ : Λ • (X • B • X) • W ≈ B
  TB₀ = begin
    Λ • (X • B • X) • W       ≈⟨ back _ (sym C336) ⟩
    Λ • W • (X • B • X)       ≈⟨ sym assoc ⟩
    (Λ • W) • (X • B • X)     ≈⟨ front _ merge ⟩
    Λ′ • (X • B • X)          ≈⟨ front _ (sym B-XBX) ⟩
    (B • (X • B • X)) • (X • B • X) ≈⟨ trans assoc (back _ XBX²) ⟩
    B • ε                     ≈⟨ right-unit ⟩
    B ∎

  --------------------------------------------------------------------
  -- Frames

  -- A network fixing wire 0 passes the box.
  fix0 : ∀ (w : Word (S.Gen N)) → perm w ⟨$⟩ʳ 0F ≡ 0F → net w • Λ ≈ Λ • net w
  fix0 w p with lift0 w p
  ... | v , e = trans (front _ e) (trans (swaps v) (back _ (sym e)))

  -- Two networks bringing the same wire to wire 0 place the same box.
  frame-eq : ∀ (u u′ : Word (S.Gen N)) (t : Fin N) →
             perm u ⟨$⟩ʳ t ≡ 0F → perm u′ ⟨$⟩ʳ t ≡ 0F → pl u Λ ≈ pl u′ Λ
  frame-eq u u′ t pu pu′ = sym (begin
    net u′ • Λ • net (revS u′)
      ≈⟨ sym left-unit ⟩
    ε • (net u′ • Λ • net (revS u′))
      ≈⟨ front _ (sym (net-inv u)) ⟩
    (net u • net (revS u)) • (net u′ • Λ • net (revS u′))
      ≈⟨ by-passoc ((□ • □) • (□ • □ • □)) (□ • ((□ • □) • □) • □) Eq.refl ⟩
    net u • ((net (revS u) • net u′) • Λ) • net (revS u′)
      ≈⟨ back _ (front _ (fix0 (revS u • u′) pw)) ⟩
    net u • (Λ • (net (revS u) • net u′)) • net (revS u′)
      ≈⟨ by-passoc (□ • (□ • (□ • □)) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
    net u • Λ • net (revS u) • (net u′ • net (revS u′))
      ≈⟨ back _ (back _ (trans (back _ (net-inv u′)) right-unit)) ⟩
    net u • Λ • net (revS u) ∎)
    where
    pw : perm (revS u • u′) ⟨$⟩ʳ 0F ≡ 0F
    pw = Eq.trans (Eq.cong (perm u′ ⟨$⟩ʳ_)
                    (Eq.trans (Eq.cong (perm (revS u) ⟨$⟩ʳ_) (Eq.sym pu)) (perm-inv u t)))
                  pu′

  -- A network bringing q to wire 0 and p to wire 1.
  σ-for : ∀ (u : Word (S.Gen N)) (p q : Fin N) → p ≢ q → perm u ⟨$⟩ʳ q ≡ 0F →
          Σ (Word (S.Gen N)) λ σ → (perm σ ⟨$⟩ʳ q ≡ 0F) × (perm σ ⟨$⟩ʳ p ≡ sF 0F)
  σ-for u p q p≢q pu = go (perm u ⟨$⟩ʳ p) Eq.refl
    where
    go : ∀ x → perm u ⟨$⟩ʳ p ≡ x →
         Σ (Word (S.Gen N)) λ σ → (perm σ ⟨$⟩ʳ q ≡ 0F) × (perm σ ⟨$⟩ʳ p ≡ sF 0F)
    go 0F     e = ⊥-elim (p≢q (perm-inj u (Eq.trans e (Eq.sym pu))))
    go (sF x) e = u • (sdS (toℕ x) S.↑) , σq , σp
      where
      σq : perm (u • (sdS (toℕ x) S.↑)) ⟨$⟩ʳ q ≡ 0F
      σq = Eq.trans (Eq.cong (perm (sdS (toℕ x) S.↑) ⟨$⟩ʳ_) pu) (⟦↑⟧ (sdS (toℕ x)) 0F)
      σp : perm (u • (sdS (toℕ x) S.↑)) ⟨$⟩ʳ p ≡ sF 0F
      σp = Eq.trans (Eq.cong (perm (sdS (toℕ x) S.↑) ⟨$⟩ʳ_) e)
             (Eq.trans (⟦↑⟧ (sdS (toℕ x)) (sF x)) (Eq.cong sF (sd-target x)))

  -- The three-box step for boxes of black controls, placed.
  three-frames : ∀ (u u′ : Word (S.Gen N)) (p q : Fin N) → p ≢ q →
                 perm u ⟨$⟩ʳ q ≡ 0F → perm u′ ⟨$⟩ʳ p ≡ 0F →
                 pl u Λ • (Xat (toℕ q) • pl u′ Λ • Xat (toℕ q)) • (Xat (toℕ p) • pl u Λ • Xat (toℕ p))
                   ≈ pl u′ Λ
  three-frames u u′ p q p≢q pu pu′ with σ-for u p q p≢q pu
  ... | σ , σq , σp = begin
    pl u Λ • (Xat (toℕ q) • pl u′ Λ • Xat (toℕ q)) • (Xat (toℕ p) • pl u Λ • Xat (toℕ p))
      ≈⟨ sym (pl-•₃ σ fΛ (pl-•₃ σ fX fB fX) (pl-•₃ σ fX↑ fΛ fX↑)) ⟩
    pl σ (Λ • (X • B • X) • W)
      ≈⟨ pl-cong σ TB₀ ⟩
    pl σ B
      ≈⟨ fB ⟩
    pl u′ Λ ∎
    where
    fΛ : pl σ Λ ≈ pl u Λ
    fΛ = frame-eq σ u q σq pu

    fB : pl σ B ≈ pl u′ Λ
    fB = trans (by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl)
               (frame-eq (σ • S.σ) u′ p (Eq.cong (perm {N} S.σ ⟨$⟩ʳ_) σp) pu′)

    fX : pl σ X ≈ Xat (toℕ q)
    fX = Eq.subst (λ j → net σ • Xat (toℕ j) • net (revS σ) ≈ Xat (toℕ q)) σq (X-net σ q)

    fX↑ : pl σ (X ↑) ≈ Xat (toℕ p)
    fX↑ = Eq.subst (λ j → net σ • Xat (toℕ j) • net (revS σ) ≈ Xat (toℕ p)) σp (X-net σ p)

  --------------------------------------------------------------------
  -- Colours

  -- The box placed by u, with X on the wires where s is false.
  boxF : Word (S.Gen N) → Bits N → Circuit N
  boxF u s = negsB s • pl u Λ • negsB s

  -- Lemma 8.4's step: with p ≠ q and u, u′ bringing q, p to wire 0,
  -- box(q; s) • box(p; s flipped on q) • box(q; s flipped on p) is
  -- box(p; s).
  three-boxes : ∀ (u u′ : Word (S.Gen N)) (p q : Fin N) → p ≢ q →
                perm u ⟨$⟩ʳ q ≡ 0F → perm u′ ⟨$⟩ʳ p ≡ 0F → (s : Bits N) →
                boxF u s • boxF u′ (flipAt (toℕ q) s) • boxF u (flipAt (toℕ p) s) ≈ boxF u′ s
  three-boxes u u′ p q p≢q pu pu′ s = begin
    (M • A • M) • (Mq • A′ • Mq) • (Mp • A • Mp)
      ≈⟨ back _ (cong (cong (negs-flip′ q s) (back _ (negs-flip q s)))
                      (cong (negs-flip′ p s) (back _ (negs-flip p s)))) ⟩
    (M • A • M) • ((M • Xq) • A′ • (Xq • M)) • ((M • Xp) • A • (Xp • M))
      ≈⟨ by-passoc ((□ • □ • □) • ((□ • □) • □ • (□ • □)) • ((□ • □) • □ • (□ • □)))
                   (□ • □ • □ • □ • ((□ • □ • □) • □ • □ • ((□ • □ • □) • □))) Eq.refl ⟩
    M • A • M • M • ((Xq • A′ • Xq) • M • M • ((Xp • A • Xp) • M))
      ≈⟨ back _ (back _ (cancelˡ _ (negs² s))) ⟩
    M • A • ((Xq • A′ • Xq) • M • M • ((Xp • A • Xp) • M))
      ≈⟨ back _ (back _ (back _ (cancelˡ _ (negs² s)))) ⟩
    M • A • ((Xq • A′ • Xq) • ((Xp • A • Xp) • M))
      ≈⟨ by-passoc (□ • □ • (□ • (□ • □))) (□ • (□ • □ • □) • □) Eq.refl ⟩
    M • (A • (Xq • A′ • Xq) • (Xp • A • Xp)) • M
      ≈⟨ back _ (front _ (three-frames u u′ p q p≢q pu pu′)) ⟩
    M • A′ • M ∎
    where
    M Xq Xp A A′ Mq Mp : Circuit N
    M  = negsB s
    Xq = Xat (toℕ q)
    Xp = Xat (toℕ p)
    A  = pl u Λ
    A′ = pl u′ Λ
    Mq = negsB (flipAt (toℕ q) s)
    Mp = negsB (flipAt (toℕ p) s)

  -- X on the box wire passes the placed box: its colour there does not
  -- matter.
  X-pl : ∀ (u : Word (S.Gen N)) (q : Fin N) → perm u ⟨$⟩ʳ q ≡ 0F →
         Xat (toℕ q) • pl u Λ ≈ pl u Λ • Xat (toℕ q)
  X-pl u q pu = begin
    Xat (toℕ q) • pl u Λ          ≈⟨ front _ (sym fX) ⟩
    pl u X • pl u Λ               ≈⟨ sym (pl-• u X Λ) ⟩
    pl u (X • Λ)                  ≈⟨ pl-cong u x-box ⟩
    pl u (Λ • X)                  ≈⟨ pl-• u Λ X ⟩
    pl u Λ • pl u X               ≈⟨ back _ fX ⟩
    pl u Λ • Xat (toℕ q) ∎
    where
    fX : pl u X ≈ Xat (toℕ q)
    fX = Eq.subst (λ j → net u • Xat (toℕ j) • net (revS u) ≈ Xat (toℕ q)) pu (X-net u q)

  boxF-flip : ∀ (u : Word (S.Gen N)) (q : Fin N) → perm u ⟨$⟩ʳ q ≡ 0F → (s : Bits N) →
              boxF u (flipAt (toℕ q) s) ≈ boxF u s
  boxF-flip u q pu s = begin
    negsB (flipAt (toℕ q) s) • pl u Λ • negsB (flipAt (toℕ q) s)
      ≈⟨ cong (negs-flip′ q s) (back _ (negs-flip q s)) ⟩
    (negsB s • Xat (toℕ q)) • pl u Λ • (Xat (toℕ q) • negsB s)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    negsB s • (Xat (toℕ q) • pl u Λ • Xat (toℕ q)) • negsB s
      ≈⟨ back _ (front _ (unconj′ (Xat² q) (X-pl u q pu))) ⟩
    negsB s • pl u Λ • negsB s ∎

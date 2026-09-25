------------------------------------------------------------------------
-- Presentations of groups
--
-- Swap networks as words of the symmetric presentation, and what they
-- do to wires
--
-- A network is read in QC through PermCalc's `net`; here the words are
-- those of MultiControlled (`σAt i` is `swapAt i`, `sdS t` is
-- `shiftDown t`), a network's inverse is its reverse (`net-inv`,
-- `net-inv′`, and `perm-inv` for the permutations), a network whose
-- permutation fixes wire 0 is a network one wire up (`lift0`, from the
-- surjectivity of the symmetric semantics and `lift₀-remove`), and X
-- conjugated by a network is X on the wire the network brings to it
-- (`X-net`).  `sd-target`: `shiftDown t` brings wire t to wire 0.  And
-- X on a set of wires given by a bitstring (`negsB`, MultiControlled's
-- negations of white controls): all these X commute and square away.
--
-- A permutation is read with the left factor acting first,
-- perm (u • v) ⟨$⟩ʳ k = perm v ⟨$⟩ʳ (perm u ⟨$⟩ʳ k), and `perm u ⟨$⟩ʳ t`
-- is the wire the data of wire t is on after u: so in
-- `net u • g • net (revS u)` the wire 0 of g is the wire t with
-- `perm u ⟨$⟩ʳ t ≡ 0F`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.NetWires where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using (Fin ; toℕ ; inject₁) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Properties using (toℕ-inject₁)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; remove ; lift₀ ; lift₀-remove ; inverseˡ)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; _≤_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (suc-injective ; ≤-trans ; n≤1+n)
open import Data.Product using (Σ ; ∃ ; _,_)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Symmetric.Interpretation using (⟦↑⟧)
open import Examples.Groups.Symmetric.Surjectivity using (surjective)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex² ; X²)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (φ ; net ; net-↑ ; perm ; perm-≈)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat ; swapAt ; shiftDown ; shiftUp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑ ; swapX ; swapX′)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep using (flipAt) public
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (insertℕ)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The words

-- The swap of the wires i, i + 1, split on the width as swapAt is.
σAt : ℕ → Word (S.Gen n)
σAt {₂₊ n} zero    = S.σ
σAt {₁₊ n} (suc i) = σAt i S.↑
σAt {₀}    _       = ε
σAt {₁}    zero    = ε

net-σAt : ∀ i → net (σAt {n} i) ≡ swapAt i
net-σAt {zero}        i       = Eq.refl
net-σAt {suc zero}    zero    = Eq.refl
net-σAt {suc zero}    (suc i) = Eq.refl
net-σAt {suc (suc n)} zero    = Eq.refl
net-σAt {suc (suc n)} (suc i) = Eq.trans (net-↑ (σAt i)) (Eq.cong _↑ (net-σAt i))

-- shiftDown and shiftUp.
sdS suS : ℕ → Word (S.Gen n)
sdS zero    = ε
sdS (suc j) = σAt j • sdS j
suS zero    = ε
suS (suc j) = suS j • σAt j

net-sdS : ∀ t → net (sdS {n} t) ≡ shiftDown t
net-sdS zero    = Eq.refl
net-sdS (suc j) = Eq.cong₂ _•_ (net-σAt j) (net-sdS j)

net-suS : ∀ t → net (suS {n} t) ≡ shiftUp t
net-suS zero    = Eq.refl
net-suS (suc j) = Eq.cong₂ _•_ (net-suS j) (net-σAt j)

-- The inverse of a network: its reverse.
revS : Word (S.Gen n) → Word (S.Gen n)
revS [ g ]ʷ   = [ g ]ʷ
revS ε        = ε
revS (u • v) = revS v • revS u

revS-↑ : (w : Word (S.Gen n)) → revS (w S.↑) ≡ revS w S.↑
revS-↑ [ g ]ʷ  = Eq.refl
revS-↑ ε       = Eq.refl
revS-↑ (u • v) = Eq.cong₂ _•_ (revS-↑ v) (revS-↑ u)

private
  revS-σAt : ∀ i → revS (σAt {n} i) ≡ σAt i
  revS-σAt {zero}        i       = Eq.refl
  revS-σAt {suc zero}    zero    = Eq.refl
  revS-σAt {suc zero}    (suc i) = Eq.refl
  revS-σAt {suc (suc n)} zero    = Eq.refl
  revS-σAt {suc (suc n)} (suc i) = Eq.trans (revS-↑ (σAt i)) (Eq.cong S._↑ (revS-σAt i))

revS-sdS : ∀ t → revS (sdS {n} t) ≡ suS t
revS-sdS zero    = Eq.refl
revS-sdS (suc j) = Eq.cong₂ _•_ (revS-sdS j) (revS-σAt j)

------------------------------------------------------------------------
-- Inverses

private
  gen² : (g : S.Gen n) → n ⊢ φ g • φ g ≈ ε
  gen² (S.gate₀ ())
  gen² (S.gate₁ ())
  gen² (S.gate₂ S.σ-gate) = Ex²
  gen² (g S.↥)            = lemma-cong↑ (φ g • φ g) ε (gen² g)

net-inv : (u : Word (S.Gen n)) → n ⊢ net u • net (revS u) ≈ ε
net-inv {n} [ g ]ʷ  = gen² g
net-inv {n} ε       = left-unit
  where open Tools (n VRel,_===_)
net-inv {n} (u • v) = begin
  (net u • net v) • (net (revS v) • net (revS u))
    ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  net u • (net v • net (revS v)) • net (revS u)
    ≈⟨ back _ (trans (front _ (net-inv v)) left-unit) ⟩
  net u • net (revS u)
    ≈⟨ net-inv u ⟩
  ε ∎
  where open Tools (n VRel,_===_)

net-inv′ : (u : Word (S.Gen n)) → n ⊢ net (revS u) • net u ≈ ε
net-inv′ {n} [ g ]ʷ  = gen² g
net-inv′ {n} ε       = left-unit
  where open Tools (n VRel,_===_)
net-inv′ {n} (u • v) = begin
  (net (revS v) • net (revS u)) • (net u • net v)
    ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  net (revS v) • (net (revS u) • net u) • net v
    ≈⟨ back _ (trans (front _ (net-inv′ u)) left-unit) ⟩
  net (revS v) • net v
    ≈⟨ net-inv′ v ⟩
  ε ∎
  where open Tools (n VRel,_===_)

private
  perm-gen² : (g : S.Gen n) (k : Fin n) → perm [ g ]ʷ ⟨$⟩ʳ (perm [ g ]ʷ ⟨$⟩ʳ k) ≡ k
  perm-gen² (S.gate₀ ())
  perm-gen² (S.gate₁ ())
  perm-gen² (S.gate₂ S.σ-gate) 0F           = Eq.refl
  perm-gen² (S.gate₂ S.σ-gate) (sF 0F)      = Eq.refl
  perm-gen² (S.gate₂ S.σ-gate) (sF (sF k))  = Eq.refl
  perm-gen² (g S.↥)            0F           = Eq.refl
  perm-gen² (g S.↥)            (sF k)       = Eq.cong sF (perm-gen² g k)

perm-inv : (u : Word (S.Gen n)) (k : Fin n) → perm (revS u) ⟨$⟩ʳ (perm u ⟨$⟩ʳ k) ≡ k
perm-inv [ g ]ʷ  k = perm-gen² g k
perm-inv ε       k = Eq.refl
perm-inv (u • v) k =
  Eq.trans (Eq.cong (perm (revS u) ⟨$⟩ʳ_) (perm-inv v (perm u ⟨$⟩ʳ k))) (perm-inv u k)

-- A permutation is injective.
perm-inj : (u : Word (S.Gen n)) {j k : Fin n} → perm u ⟨$⟩ʳ j ≡ perm u ⟨$⟩ʳ k → j ≡ k
perm-inj u {j} {k} e =
  Eq.trans (Eq.sym (perm-inv u j)) (Eq.trans (Eq.cong (perm (revS u) ⟨$⟩ʳ_) e) (perm-inv u k))

------------------------------------------------------------------------
-- A network fixing wire 0 is a network one wire up

-- Abstract: its value is computed by the symmetric group's normal
-- form, which at a width with a few known successors unfolds into
-- enormous stuck terms as soon as a client matches on the pair.
abstract
  lift0 : (u : Word (S.Gen (₁₊ n))) → perm u ⟨$⟩ʳ 0F ≡ 0F →
          Σ (Word (S.Gen n)) λ v → (₁₊ n) ⊢ net u ≈ net v ↑
  lift0 {n} u p with surjective {n} (remove 0F (perm u))
  ... | v , ok = v , Eq.subst (λ w → (₁₊ n) ⊢ net u ≈ w) (net-↑ v) (perm-≈ {u = u} {v = v S.↑} pw)
    where
    lift-cong : ∀ k → lift₀ (remove 0F (perm u)) ⟨$⟩ʳ k ≡ lift₀ (perm v) ⟨$⟩ʳ k
    lift-cong 0F     = Eq.refl
    lift-cong (sF k) = Eq.cong sF (Eq.sym (ok PB.refl k))

    pw : ∀ k → perm u ⟨$⟩ʳ k ≡ perm (v S.↑) ⟨$⟩ʳ k
    pw k = Eq.trans (Eq.sym (lift₀-remove (perm u) p k))
             (Eq.trans (lift-cong k) (Eq.sym (⟦↑⟧ v k)))

------------------------------------------------------------------------
-- Where the words send wires

-- The swap of i, i + 1 sends i + 1 to i.
σAt-hi : (i : Fin n) → perm (σAt {₁₊ n} (toℕ i)) ⟨$⟩ʳ sF i ≡ inject₁ i
σAt-hi {suc n} 0F     = Eq.refl
σAt-hi {suc n} (sF i) = Eq.trans (⟦↑⟧ (σAt (toℕ i)) (sF (sF i))) (Eq.cong sF (σAt-hi i))

-- shiftDown t brings wire t to wire 0.
private
  sd-target′ : ∀ j (t : Fin (₁₊ n)) → toℕ t ≡ j → perm (sdS {₁₊ n} j) ⟨$⟩ʳ t ≡ 0F
  sd-target′ zero    0F     _ = Eq.refl
  sd-target′ zero    (sF t) ()
  sd-target′ (suc j) 0F     ()
  sd-target′ {n} (suc j) (sF t) e =
    Eq.trans (Eq.cong (perm (sdS j) ⟨$⟩ʳ_) hi)
             (sd-target′ j (inject₁ t) (Eq.trans (toℕ-inject₁ t) e′))
    where
    e′ : toℕ t ≡ j
    e′ = suc-injective e
    hi : perm (σAt {suc n} j) ⟨$⟩ʳ sF t ≡ inject₁ t
    hi = Eq.subst (λ i → perm (σAt {suc n} i) ⟨$⟩ʳ sF t ≡ inject₁ t) e′ (σAt-hi t)

sd-target : (t : Fin (₁₊ n)) → perm (sdS {₁₊ n} (toℕ t)) ⟨$⟩ʳ t ≡ 0F
sd-target t = sd-target′ (toℕ t) t Eq.refl

------------------------------------------------------------------------
-- X across a network

private
  gen-X : (g : S.Gen n) (j : Fin n) → n ⊢ φ g • Xat (toℕ (perm [ g ]ʷ ⟨$⟩ʳ j)) • φ g ≈ Xat (toℕ j)
  gen-X (S.gate₀ ())
  gen-X (S.gate₁ ())
  gen-X {₂₊ n} (S.gate₂ S.σ-gate) 0F = begin
    Ex • X ↑ • Ex       ≈⟨ back _ swapX ⟩
    Ex • Ex • X         ≈⟨ trans (sym assoc) (trans (front _ Ex²) left-unit) ⟩
    X ∎
    where open Tools ((₂₊ n) VRel,_===_)
  gen-X {₂₊ n} (S.gate₂ S.σ-gate) (sF 0F) = begin
    Ex • X • Ex         ≈⟨ sym assoc ⟩
    (Ex • X) • Ex       ≈⟨ front _ (sym swapX) ⟩
    (X ↑ • Ex) • Ex     ≈⟨ trans assoc (trans (back _ Ex²) right-unit) ⟩
    X ↑ ∎
    where open Tools ((₂₊ n) VRel,_===_)
  gen-X {₂₊ n} (S.gate₂ S.σ-gate) (sF (sF k)) = begin
    Ex • Xat (toℕ k) ↑ ↑ • Ex     ≈⟨ sym assoc ⟩
    (Ex • Xat (toℕ k) ↑ ↑) • Ex   ≈⟨ front _ (low-comm Ex (Xat (toℕ k))) ⟩
    (Xat (toℕ k) ↑ ↑ • Ex) • Ex   ≈⟨ trans assoc (trans (back _ Ex²) right-unit) ⟩
    Xat (toℕ k) ↑ ↑ ∎
    where open Tools ((₂₊ n) VRel,_===_)
  gen-X {₁₊ n} (g S.↥) 0F = begin
    φ g ↑ • X • φ g ↑       ≈⟨ back _ (X-↑ (φ g)) ⟩
    φ g ↑ • φ g ↑ • X       ≈⟨ trans (sym assoc) (trans (front _ (lemma-cong↑ (φ g • φ g) ε (gen² g))) left-unit) ⟩
    X ∎
    where open Tools ((₁₊ n) VRel,_===_)
  gen-X {₁₊ n} (g S.↥) (sF j) =
    lemma-cong↑ (φ g • Xat (toℕ (perm [ g ]ʷ ⟨$⟩ʳ j)) • φ g) (Xat (toℕ j)) (gen-X g j)

X-net : (u : Word (S.Gen n)) (j : Fin n) →
        n ⊢ net u • Xat (toℕ (perm u ⟨$⟩ʳ j)) • net (revS u) ≈ Xat (toℕ j)
X-net [ g ]ʷ  j = gen-X g j
X-net {n} ε       j = trans left-unit right-unit
  where open Tools (n VRel,_===_)
X-net {n} (u • v) j = begin
  (net u • net v) • Xat (toℕ (perm v ⟨$⟩ʳ (perm u ⟨$⟩ʳ j))) • (net (revS v) • net (revS u))
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
  net u • (net v • Xat (toℕ (perm v ⟨$⟩ʳ (perm u ⟨$⟩ʳ j))) • net (revS v)) • net (revS u)
    ≈⟨ back _ (front _ (X-net v (perm u ⟨$⟩ʳ j))) ⟩
  net u • Xat (toℕ (perm u ⟨$⟩ʳ j)) • net (revS u)
    ≈⟨ X-net u j ⟩
  Xat (toℕ j) ∎
  where open Tools (n VRel,_===_)

------------------------------------------------------------------------
-- X on a set of wires

-- X on the wires where the bitstring is false: the negations of the
-- white controls.
negsB : Bits n → Circuit n
negsB []          = ε
negsB (true  ∷ s) = negsB s ↑
negsB (false ∷ s) = X • negsB s ↑

negs² : (s : Bits n) → n ⊢ negsB s • negsB s ≈ ε
negs² {n} [] = left-unit
  where open Tools (n VRel,_===_)
negs² {suc n} (true ∷ s) = lemma-cong↑ (negsB s • negsB s) ε (negs² s)
negs² {suc n} (false ∷ s) = begin
  (X • negsB s ↑) • (X • negsB s ↑)     ≈⟨ trans assoc (back _ (trans (sym assoc) (front _ (sym (X-↑ (negsB s)))))) ⟩
  X • (X • negsB s ↑) • negsB s ↑       ≈⟨ trans (sym assoc) (trans (front _ (trans (sym assoc) (front _ X²))) (front _ left-unit)) ⟩
  negsB s ↑ • negsB s ↑                 ≈⟨ lemma-cong↑ (negsB s • negsB s) ε (negs² s) ⟩
  ε ∎
  where open Tools ((₁₊ n) VRel,_===_)

-- Every X commutes with the negations.
X-negs : ∀ (i : Fin n) (s : Bits n) → n ⊢ Xat (toℕ i) • negsB s ≈ negsB s • Xat (toℕ i)
X-negs {suc n} 0F (true ∷ s) = X-↑ (negsB s)
X-negs {suc n} 0F (false ∷ s) = begin
  X • X • negsB s ↑       ≈⟨ back _ (X-↑ (negsB s)) ⟩
  X • negsB s ↑ • X       ≈⟨ sym assoc ⟩
  (X • negsB s ↑) • X ∎
  where open Tools ((₁₊ n) VRel,_===_)
X-negs {suc n} (sF i) (true ∷ s) = lemma-cong↑ (Xat (toℕ i) • negsB s) (negsB s • Xat (toℕ i)) (X-negs i s)
X-negs {suc n} (sF i) (false ∷ s) = begin
  Xat (toℕ i) ↑ • X • negsB s ↑       ≈⟨ trans (sym assoc) (front _ (sym (X-↑ (Xat (toℕ i))))) ⟩
  (X • Xat (toℕ i) ↑) • negsB s ↑     ≈⟨ trans assoc (back _ (lemma-cong↑ (Xat (toℕ i) • negsB s) (negsB s • Xat (toℕ i)) (X-negs i s))) ⟩
  X • negsB s ↑ • Xat (toℕ i) ↑       ≈⟨ sym assoc ⟩
  (X • negsB s ↑) • Xat (toℕ i) ↑ ∎
  where open Tools ((₁₊ n) VRel,_===_)

-- Flipping a bit is one more X, on either side.
negs-flip : ∀ (i : Fin n) (s : Bits n) → n ⊢ negsB (flipAt (toℕ i) s) ≈ Xat (toℕ i) • negsB s
negs-flip {suc n} 0F (true ∷ s) = refl
  where open Tools ((₁₊ n) VRel,_===_)
negs-flip {suc n} 0F (false ∷ s) = begin
  negsB s ↑                   ≈⟨ sym (trans (sym assoc) (trans (front _ X²) left-unit)) ⟩
  X • X • negsB s ↑ ∎
  where open Tools ((₁₊ n) VRel,_===_)
negs-flip {suc n} (sF i) (true ∷ s) =
  lemma-cong↑ (negsB (flipAt (toℕ i) s)) (Xat (toℕ i) • negsB s) (negs-flip i s)
negs-flip {suc n} (sF i) (false ∷ s) = begin
  X • negsB (flipAt (toℕ i) s) ↑      ≈⟨ back _ (lemma-cong↑ (negsB (flipAt (toℕ i) s)) (Xat (toℕ i) • negsB s) (negs-flip i s)) ⟩
  X • Xat (toℕ i) ↑ • negsB s ↑       ≈⟨ trans (sym assoc) (trans (front _ (X-↑ (Xat (toℕ i)))) assoc) ⟩
  Xat (toℕ i) ↑ • X • negsB s ↑ ∎
  where open Tools ((₁₊ n) VRel,_===_)

negs-flip′ : ∀ (i : Fin n) (s : Bits n) → n ⊢ negsB (flipAt (toℕ i) s) ≈ negsB s • Xat (toℕ i)
negs-flip′ {n} i s = trans (negs-flip i s) (X-negs i s)
  where open Tools (n VRel,_===_)

Xat² : ∀ (i : Fin n) → n ⊢ Xat (toℕ i) • Xat (toℕ i) ≈ ε
Xat² {suc n} 0F     = X²
Xat² {suc n} (sF i) = lemma-cong↑ (Xat (toℕ i) • Xat (toℕ i)) ε (Xat² i)

------------------------------------------------------------------------
-- Colours across a swap, and across shiftDown

-- The swap of the bits i, i + 1.
swB : ℕ → Bits n → Bits n
swB i       []          = []
swB zero    (a ∷ [])    = a ∷ []
swB zero    (a ∷ b ∷ t) = b ∷ a ∷ t
swB (suc i) (a ∷ t)     = a ∷ swB i t

private
  module SW {n : ℕ} = Conj {₂₊ n} Ex Ex²

  Ex-X : (₂₊ n) ⊢ Ex • X • Ex ≈ X ↑
  Ex-X {n} = begin
    Ex • X • Ex         ≈⟨ sym assoc ⟩
    (Ex • X) • Ex       ≈⟨ front _ (sym swapX) ⟩
    (X ↑ • Ex) • Ex     ≈⟨ trans assoc (trans (back _ Ex²) right-unit) ⟩
    X ↑ ∎
    where open Tools ((₂₊ n) VRel,_===_)

  Ex-X↑ : (₂₊ n) ⊢ Ex • X ↑ • Ex ≈ X
  Ex-X↑ {n} = begin
    Ex • X ↑ • Ex       ≈⟨ back _ swapX ⟩
    Ex • Ex • X         ≈⟨ trans (sym assoc) (trans (front _ Ex²) left-unit) ⟩
    X ∎
    where open Tools ((₂₊ n) VRel,_===_)

  Ex-↑↑ : ∀ (w : Circuit n) → (₂₊ n) ⊢ Ex • w ↑ ↑ • Ex ≈ w ↑ ↑
  Ex-↑↑ {n} w = trans (sym assoc) (trans (front _ (low-comm Ex w)) (trans assoc (trans (back _ Ex²) right-unit)))
    where open Tools ((₂₊ n) VRel,_===_)

swapAt-negsB : ∀ i (t : Bits n) → n ⊢ swapAt i • negsB t • swapAt i ≈ negsB (swB i t)
swapAt-negsB {zero}     i       []       = trans left-unit left-unit
  where open Tools (zero VRel,_===_)
swapAt-negsB {suc zero} zero    (a ∷ []) = trans left-unit right-unit
  where open Tools ((₁₊ zero) VRel,_===_)
swapAt-negsB {suc zero} (suc i) (a ∷ []) = trans left-unit right-unit
  where open Tools ((₁₊ zero) VRel,_===_)
swapAt-negsB {suc (suc n)} zero (true ∷ true ∷ t)   = Ex-↑↑ (negsB t)
swapAt-negsB {suc (suc n)} zero (true ∷ false ∷ t)  =
  trans (SW.⟪⟫-• (X ↑) (negsB t ↑ ↑)) (cong Ex-X↑ (Ex-↑↑ (negsB t)))
  where open Tools ((₂₊ n) VRel,_===_)
swapAt-negsB {suc (suc n)} zero (false ∷ true ∷ t)  =
  trans (SW.⟪⟫-• X (negsB t ↑ ↑)) (cong Ex-X (Ex-↑↑ (negsB t)))
  where open Tools ((₂₊ n) VRel,_===_)
swapAt-negsB {suc (suc n)} zero (false ∷ false ∷ t) = begin
  Ex • (X • (X ↑ • negsB t ↑ ↑)) • Ex
    ≈⟨ trans (SW.⟪⟫-• X (X ↑ • negsB t ↑ ↑)) (cong Ex-X (trans (SW.⟪⟫-• (X ↑) (negsB t ↑ ↑)) (cong Ex-X↑ (Ex-↑↑ (negsB t))))) ⟩
  X ↑ • (X • negsB t ↑ ↑)
    ≈⟨ trans (sym assoc) (trans (front _ (sym (X-↑ X))) assoc) ⟩
  X • (X ↑ • negsB t ↑ ↑) ∎
  where open Tools ((₂₊ n) VRel,_===_)
swapAt-negsB {suc (suc n)} (suc i) (true ∷ r) =
  lemma-cong↑ (swapAt i • negsB r • swapAt i) (negsB (swB i r)) (swapAt-negsB i r)
swapAt-negsB {suc (suc n)} (suc i) (false ∷ r) = begin
  swapAt i ↑ • (X • negsB r ↑) • swapAt i ↑
    ≈⟨ sym assoc′ ⟩
  (swapAt i ↑ • X) • (negsB r ↑ • swapAt i ↑)
    ≈⟨ front _ (sym (X-↑ (swapAt i))) ⟩
  (X • swapAt i ↑) • (negsB r ↑ • swapAt i ↑)
    ≈⟨ assoc ⟩
  X • (swapAt i ↑ • negsB r ↑ • swapAt i ↑)
    ≈⟨ back _ (lemma-cong↑ (swapAt i • negsB r • swapAt i) (negsB (swB i r)) (swapAt-negsB i r)) ⟩
  X • negsB (swB i r) ↑ ∎
  where
  open Tools ((₂₊ n) VRel,_===_)
  assoc′ : (swapAt i ↑ • X) • (negsB r ↑ • swapAt i ↑) ≈ swapAt i ↑ • (X • negsB r ↑) • swapAt i ↑
  assoc′ = by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl

swB-insert : ∀ q x (v : Bits n) → q < n → swB q (insertℕ q x v) ≡ insertℕ (suc q) x v
swB-insert q       x []       ()
swB-insert zero    x (b ∷ v) _       = Eq.refl
swB-insert (suc q) x (b ∷ v) (s≤s p) = Eq.cong (b ∷_) (swB-insert q x v p)

-- Conjugated by shiftDown q, the colour of wire 0 goes to wire q.
sd-negsB : ∀ q x (v : Bits n) → q ≤ n →
           (₁₊ n) ⊢ net (sdS q) • negsB (x ∷ v) • net (revS (sdS q)) ≈ negsB (insertℕ q x v)
sd-negsB {n} zero    x v _ = trans left-unit right-unit
  where open Tools ((₁₊ n) VRel,_===_)
sd-negsB {n} (suc q) x v q<n = begin
  (net (σAt q) • net (sdS q)) • negsB (x ∷ v) • (net (revS (sdS q)) • net (revS (σAt q)))
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
  net (σAt q) • (net (sdS q) • negsB (x ∷ v) • net (revS (sdS q))) • net (revS (σAt q))
    ≈⟨ back _ (front _ (sd-negsB q x v (≤-trans (n≤1+n q) q<n))) ⟩
  net (σAt q) • negsB (insertℕ q x v) • net (revS (σAt q))
    ≈⟨ refl′ (Eq.cong₂ (λ a b → a • negsB (insertℕ q x v) • b) (net-σAt q)
                       (Eq.trans (Eq.cong net (revS-σAt q)) (net-σAt q))) ⟩
  swapAt q • negsB (insertℕ q x v) • swapAt q
    ≈⟨ swapAt-negsB q (insertℕ q x v) ⟩
  negsB (swB q (insertℕ q x v))
    ≈⟨ refl′ (Eq.cong negsB (swB-insert q x v q<n)) ⟩
  negsB (insertℕ (suc q) x v) ∎
  where
  open Tools ((₁₊ n) VRel,_===_)
  refl′ : ∀ {a b : Circuit (₁₊ n)} → a ≡ b → a ≈ b
  refl′ Eq.refl = refl

------------------------------------------------------------------------
-- More on where shiftDown sends wires

-- The swap of i, i + 1 fixes the wires above.
σAt-fix : ∀ j (i : Fin n) → suc j < toℕ i → perm (σAt {n} j) ⟨$⟩ʳ i ≡ i
σAt-fix {zero}        j       ()     _
σAt-fix {suc zero}    zero    i      _ = Eq.refl
σAt-fix {suc zero}    (suc j) i      _ = Eq.refl
σAt-fix {suc (suc n)} zero    0F           ()
σAt-fix {suc (suc n)} zero    (sF 0F)      (s≤s ())
σAt-fix {suc (suc n)} zero    (sF (sF k))  _ = Eq.refl
σAt-fix {suc (suc n)} (suc j) 0F           ()
σAt-fix {suc (suc n)} (suc j) (sF i)       (s≤s p) =
  Eq.trans (⟦↑⟧ (σAt j) (sF i)) (Eq.cong sF (σAt-fix j i p))

-- shiftDown q fixes the wires above q.
sd-fix : ∀ q (i : Fin n) → q < toℕ i → perm (sdS {n} q) ⟨$⟩ʳ i ≡ i
sd-fix zero    i _ = Eq.refl
sd-fix (suc q) i p =
  Eq.trans (Eq.cong (perm (sdS q) ⟨$⟩ʳ_) (σAt-fix q i p)) (sd-fix q i (≤-trans (n≤1+n (suc q)) p))

-- shiftDown (1 + j) moves wire 0 to wire 1.
sd-0 : ∀ j → perm (sdS {₃₊ n} (suc j)) ⟨$⟩ʳ 0F ≡ sF 0F
sd-0 zero    = Eq.refl
sd-0 (suc j) = Eq.trans (Eq.cong (perm (sdS (suc j)) ⟨$⟩ʳ_) (⟦↑⟧ (σAt j) 0F)) (sd-0 j)

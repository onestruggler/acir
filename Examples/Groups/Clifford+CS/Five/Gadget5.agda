------------------------------------------------------------------------
-- Presentations of groups
--
-- The gadgets of the affine decoding on five wires
--
-- The five-wire gadget of V is λ⁰₄ of its four-wire one, acting on the
-- basis states 0 and e₀.  It commutes with the seven letters of
-- Five.Indep: CX from wire j + 1 onto j and the SWAPs of the wires 1 2,
-- 2 3 by (F4)/(F5) and transport (`pass⁰`), CX from wire 4 onto 3 as
-- the λ¹-image of X on wire 3 (`pass¹`), and the SWAP of the wires 3 4
-- as three CNOTs, CX(3→4) being CX(1→4) between SWAPs and CX(1→4)
-- passing by (F6): iZ⁻¹ is a twisted commutator, the hybrid's inverse
-- one times iZ⁻¹, and XZ a conjugate of iZ by the hybrid.  Hence
-- `Indep` applies to each (`cind`): its conjugates by affine circuits
-- depend only on where they send 0 and e₀.
--
-- Generic in the four-wire gadgets (Five.Facts4): a concrete gadget
-- under λ⁰, compared with another spelling of itself — a copy made by a
-- module application, say — would have its five-wire spelling unfolded.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.Inputs using (Inputs)
open import Examples.Groups.Clifford+CS.Five.Facts4 using (Facts4)

module Examples.Groups.Clifford+CS.Five.Gadget5 (I : Inputs) (F : Facts4) where

open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
  using (Circuit ; S ; K ; CS ; iI ; X ; CX₁₀ ; Swap ; _↑ ; _↓ᵏ_ ; _⊢_≈_ ; _VRel,_===_)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Sem.Blocks using (Kind ; kpp ; krot ; kki)

open Inputs I
open Facts4 F
open import Examples.Groups.Clifford+CS.Five.Calc F4ᵍ F5ᵍ x4x4
import Examples.Groups.Clifford+CS.Five.F6
module F6 = Examples.Groups.Clifford+CS.Five.F6 F4ᵍ F5ᵍ x4x4 ok cx14ˡ w1ˡ w2ˡ aaˡ eeˡ sb2ˡ
import Examples.Groups.Clifford+CS.Five.Indep as Indep
open import Examples.Groups.Clifford+CS.Five.Affine using (τ)
open import Examples.Groups.Clifford+CS.Five.Stab using (e₀)
open import Data.Nat.Primality using (prime[2])
import Examples.Groups.Qupit-Phase-Affine.Syntactics 0 prime[2] 0 as B
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan 0 prime[2] 0 using (0ᵛ)
open import Examples.Groups.Qupit-Phase-Affine.Completeness.Aff 0 prime[2] using (adm)
open import Examples.Groups.Qupit-Phase-Affine.Evaluation 0 prime[2] 0 adm using (fn)
open import Examples.Groups.Qupit-Phase-Affine.Basic 0 prime[2] 0 using (_⁻¹)

------------------------------------------------------------------------
-- Generic passing lemmas

private
  -- a passes x, x y ≈ ε, y x ≈ ε: a passes y.
  pass-inv : ∀ {a x y : Circuit 5} → a • x ≈ x • a → x • y ≈ ε → y • x ≈ ε → a • y ≈ y • a
  pass-inv {a} {x} {y} p xy yx = begin
    a • y                     ≈⟨ sym left-unit ⟩
    ε • a • y                 ≈⟨ front _ (sym yx) ⟩
    (y • x) • a • y           ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    y • (x • a) • y           ≈⟨ back y (front y (sym p)) ⟩
    y • (a • x) • y           ≈⟨ by-passoc (□ • (□ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
    y • a • (x • y)           ≈⟨ back y (back a xy) ⟩
    y • a • ε                 ≈⟨ back y right-unit ⟩
    y • a                     ∎

  pass-• : ∀ {a x y : Circuit 5} → a • x ≈ x • a → a • y ≈ y • a → a • (x • y) ≈ (x • y) • a
  pass-• {a} {x} {y} px py = begin
    a • (x • y)   ≈⟨ sym assoc ⟩
    (a • x) • y   ≈⟨ front y px ⟩
    (x • a) • y   ≈⟨ assoc ⟩
    x • (a • y)   ≈⟨ back x py ⟩
    x • (y • a)   ≈⟨ sym assoc ⟩
    (x • y) • a   ∎

  -- (a • b) passes x when a and b do.
  slide : ∀ {a b x : Circuit 5} → a • x ≈ x • a → b • x ≈ x • b → (a • b) • x ≈ x • (a • b)
  slide {a} {b} {x} pa pb = begin
    (a • b) • x   ≈⟨ assoc ⟩
    a • (b • x)   ≈⟨ back a pb ⟩
    a • (x • b)   ≈⟨ sym assoc ⟩
    (a • x) • b   ≈⟨ front b pa ⟩
    (x • a) • b   ≈⟨ assoc ⟩
    x • (a • b)   ∎

  pass≈ : ∀ {a b x : Circuit 5} → a ≈ b → a • x ≈ x • a → b • x ≈ x • b
  pass≈ e p = trans (front _ (sym e)) (trans p (back _ e))

  -- a passes y when it passes x and x ≈ y.
  over : ∀ {a x y : Circuit 5} → x ≈ y → a • x ≈ x • a → a • y ≈ y • a
  over e p = trans (back _ (sym e)) (trans p (front _ e))

  inv⁰ : ∀ {u v : Circuit 4} → 4 ⊢ u • v ≈ ε → Λ⁰ u • Λ⁰ v ≈ ε
  inv⁰ {u} {v} e = trans (sym (hom⁰ u v)) (transport⁰ ok e)

------------------------------------------------------------------------
-- The same on four wires

private
  module T4 = Tools (_VRel,_===_ 4)

  slide₄ : ∀ {a b x : Circuit 4} → 4 ⊢ a • x ≈ x • a → 4 ⊢ b • x ≈ x • b → 4 ⊢ (a • b) • x ≈ x • (a • b)
  slide₄ {a} {b} {x} pa pb =
    T4.trans T4.assoc (T4.trans (T4.back a pb) (T4.trans (T4.sym T4.assoc)
      (T4.trans (T4.front b pa) T4.assoc)))

  -- a passes y when it passes x and y is x's inverse.
  inv₄ : ∀ {a x y : Circuit 4} → 4 ⊢ a • x ≈ x • a → 4 ⊢ x • y ≈ ε → 4 ⊢ y • x ≈ ε → 4 ⊢ a • y ≈ y • a
  inv₄ {a} {x} {y} p xy yx =
    T4.trans (T4.sym T4.left-unit) (T4.trans (T4.front _ (T4.sym yx))
      (T4.trans (T4.by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl)
        (T4.trans (T4.back y (T4.front y (T4.sym p)))
          (T4.trans (T4.by-passoc (□ • (□ • □) • □) (□ • □ • (□ • □)) Eq.refl)
            (T4.trans (T4.back y (T4.back a xy)) (T4.back y T4.right-unit))))))

------------------------------------------------------------------------
-- The letters on the wires 0..3, and CX from wire 4 onto 3

pass-dom : (g G4 : Circuit 4) → 4 ⊢ g • G4 ≈ G4 • g → (g ↓ᵏ 1) • Λ⁰ G4 ≈ Λ⁰ G4 • (g ↓ᵏ 1)
pass-dom g G4 e = pass≈ (D-sp g) (pass⁰ ok g G4 e)

pass-cx₃ : (G4 : Circuit 4) → CX₁₀ ↑ ↑ ↑ • Λ⁰ G4 ≈ Λ⁰ G4 • CX₁₀ ↑ ↑ ↑
pass-cx₃ G4 = pass≈ (sym cx43ˡ) (pass¹ (X ↑ ↑ ↑) G4)

------------------------------------------------------------------------
-- (F6) for the gadgets

A : Circuit 5
A = F6.A

-- One twisted commutator, spelled out for the gadgets' words.
module C (Gm Gp : Circuit 4) (h-inv : 4 ⊢ Gm • Gp ≈ ε)
         (zm : 4 ⊢ (S • S) ↑ • Gm ≈ Gm • (S • S) ↑) (zp : 4 ⊢ (S • S) ↑ • Gp ≈ Gp • (S • S) ↑)
         (cs⁻p : 4 ⊢ (CS • CS • CS) • Gp ≈ Gp • (CS • CS • CS)) (csp : 4 ⊢ CS • Gp ≈ Gp • CS)
         (czp : 4 ⊢ (CS • CS) • Gp ≈ Gp • (CS • CS)) where
  f6 : A • Λ⁰ (Gm • F6.Sd • Gp • S) ≈ Λ⁰ (Gm • F6.Sd • Gp • S) • A
  f6 = F6.Comm.f6 Gm Gp h-inv zm zp cs⁻p csp czp

private
  -- What C asks of g and g⁻¹, from S and CS passing g.
  module Facts (g g⁻ : Circuit 4) (gg : 4 ⊢ g • g⁻ ≈ ε) (g⁻g : 4 ⊢ g⁻ • g ≈ ε)
               (s₁g : 4 ⊢ S ↑ • g ≈ g • S ↑) (csg : 4 ⊢ CS • g ≈ g • CS) where
    z : 4 ⊢ (S • S) ↑ • g ≈ g • (S • S) ↑
    z = slide₄ s₁g s₁g
    z⁻ : 4 ⊢ (S • S) ↑ • g⁻ ≈ g⁻ • (S • S) ↑
    z⁻ = inv₄ z gg g⁻g
    cz : 4 ⊢ (CS • CS) • g ≈ g • (CS • CS)
    cz = slide₄ csg csg
    c³ : 4 ⊢ (CS • CS • CS) • g ≈ g • (CS • CS • CS)
    c³ = slide₄ csg cz
    cs⁻ : 4 ⊢ CS • g⁻ ≈ g⁻ • CS
    cs⁻ = inv₄ csg gg g⁻g
    cz⁻ : 4 ⊢ (CS • CS) • g⁻ ≈ g⁻ • (CS • CS)
    cz⁻ = inv₄ cz gg g⁻g
    c³⁻ : 4 ⊢ (CS • CS • CS) • g⁻ ≈ g⁻ • (CS • CS • CS)
    c³⁻ = inv₄ c³ gg g⁻g

  module FR = Facts (G krot) (G⁻ krot) (inv krot) (inv′ krot) s₁-rot cs-rot
  module FK = Facts (G kki) (G⁻ kki) (inv kki) (inv′ kki) s₁-ki cs-ki

  dec-pp⁻′ : 4 ⊢ G⁻ kpp ≈ G⁻ krot • F6.Sd • G krot • S
  dec-pp⁻′ = dec-pp⁻

  dec-ki⁻′ : 4 ⊢ G⁻ kki ≈ (G kki • F6.Sd • G⁻ kki • S) • G⁻ kpp
  dec-ki⁻′ = dec-ki⁻

f6-pp⁻ : A • Λ⁰ (G⁻ kpp) ≈ Λ⁰ (G⁻ kpp) • A
f6-pp⁻ = over (sym (transport⁰ ok dec-pp⁻′))
           (C.f6 (G⁻ krot) (G krot) (inv′ krot) FR.z⁻ FR.z FR.c³ cs-rot FR.cz)

f6-pp : A • Λ⁰ (G kpp) ≈ Λ⁰ (G kpp) • A
f6-pp = pass-inv f6-pp⁻ (inv⁰ (inv′ kpp)) (inv⁰ (inv kpp))

f6-ki⁻ : A • Λ⁰ (G⁻ kki) ≈ Λ⁰ (G⁻ kki) • A
f6-ki⁻ = over (sym (trans (transport⁰ ok dec-ki⁻′) (hom⁰ (G kki • F6.Sd • G⁻ kki • S) (G⁻ kpp))))
           (pass-• (C.f6 (G kki) (G⁻ kki) (inv kki) FK.z FK.z⁻ FK.c³⁻ FK.cs⁻ FK.cz⁻) f6-pp⁻)

f6-ki : A • Λ⁰ (G kki) ≈ Λ⁰ (G kki) • A
f6-ki = pass-inv f6-ki⁻ (inv⁰ (inv′ kki)) (inv⁰ (inv kki))

f6-rot : A • Λ⁰ (G krot) ≈ Λ⁰ (G krot) • A
f6-rot = over (sym (trans (transport⁰ ok dec-rot)
                      (trans (hom⁰ (G⁻ kki) (G kpp • G kki)) (back (Λ⁰ (G⁻ kki)) (hom⁰ (G kpp) (G kki))))))
           (pass-• f6-ki⁻ (pass-• f6-pp f6-ki))

f6 : ∀ V → A • Λ⁰ (G V) ≈ Λ⁰ (G V) • A
f6 kpp  = f6-pp
f6 krot = f6-rot
f6 kki  = f6-ki

------------------------------------------------------------------------
-- The SWAP of the wires 3 4

module Sw34 (G4 : Circuit 4)
  (p-sw₁ : 4 ⊢ Swap ↑ • G4 ≈ G4 • Swap ↑) (p-sw₂ : 4 ⊢ Swap ↑ ↑ • G4 ≈ G4 • Swap ↑ ↑)
  (f6′ : A • Λ⁰ G4 ≈ Λ⁰ G4 • A) where

  private
    Gc : Circuit 5
    Gc = Λ⁰ G4

    s₁ : Swap ↑ • Gc ≈ Gc • Swap ↑
    s₁ = pass-dom (Swap ↑) G4 p-sw₁

    s₂ : Swap ↑ ↑ • Gc ≈ Gc • Swap ↑ ↑
    s₂ = pass-dom (Swap ↑ ↑) G4 p-sw₂

    cx34 : ⟪ CX34 ∷ [] ⟫ʷ • Gc ≈ Gc • ⟪ CX34 ∷ [] ⟫ʷ
    cx34 = pass≈ (sym cx34ˡ) (slide s₂ (slide s₁ (slide f6′ (slide s₁ s₂))))

  sw₃ : Swap ↑ ↑ ↑ • Λ⁰ G4 ≈ Λ⁰ G4 • Swap ↑ ↑ ↑
  sw₃ = pass≈ (sym sw34ˡ) (slide cx34 (slide (pass-cx₃ G4) cx34))

------------------------------------------------------------------------
-- The independence of each gadget

module Of (G4 : Circuit 4)
  (cx₀′ : 4 ⊢ CX₁₀ • G4 ≈ G4 • CX₁₀) (cx₁′ : 4 ⊢ CX₁₀ ↑ • G4 ≈ G4 • CX₁₀ ↑)
  (cx₂′ : 4 ⊢ CX₁₀ ↑ ↑ • G4 ≈ G4 • CX₁₀ ↑ ↑)
  (sw₁′ : 4 ⊢ Swap ↑ • G4 ≈ G4 • Swap ↑) (sw₂′ : 4 ⊢ Swap ↑ ↑ • G4 ≈ G4 • Swap ↑ ↑)
  (f6′ : A • Λ⁰ G4 ≈ Λ⁰ G4 • A) where

  open Indep (Λ⁰ G4)
    (pass-dom CX₁₀ G4 cx₀′) (pass-dom (CX₁₀ ↑) G4 cx₁′) (pass-dom (CX₁₀ ↑ ↑) G4 cx₂′) (pass-cx₃ G4)
    (pass-dom (Swap ↑) G4 sw₁′) (pass-dom (Swap ↑ ↑) G4 sw₂′) (Sw34.sw₃ G4 sw₁′ sw₂′ f6′) public

-- The conjugate of a gadget by an affine circuit depends only on the
-- images of 0 and e₀.
cind : (V : Kind) (α β : B.Circuit 5) → fn α 0ᵛ ≡ fn β 0ᵛ → fn α e₀ ≡ fn β e₀ →
       τ α • Λ⁰ (G V) • τ (α ⁻¹) ≈ τ β • Λ⁰ (G V) • τ (β ⁻¹)
cind V = Of.conj-indep (G V) (cx₀ V) (cx₁ V) (cx₂ V) (sw₁ V) (sw₂ V) (f6 V)

------------------------------------------------------------------------
-- Presentations of groups
--
-- The gadgets of the affine decoding on four wires, and their facts
--
-- G-pp, G-rot and G-ki (Five.Gadgets.Words) act on the basis states 0
-- and e₀ as the two-level iZ, XZ and the hybrid, and as the identity
-- elsewhere; their inverses are the syntactic ones (Presentation's
-- Group-Lemmas), so that inverting costs no evaluation.  The facts the
-- five-wire gadgets need come from the evaluations of Five.Gadgets.E01
-- … E14 by group algebra: the letters of the independence (`pp-cx₀`, …),
-- and for (F6) the twisted commutators T(g) = g⁻¹ S⁻¹ g S,
--   G-pp⁻ ≈ T(G-rot),  G-ki⁻ ≈ T(G-ki⁻) G-pp⁻,  G-rot ≈ G-ki⁻ G-pp G-ki,
-- with what Five.F6.Comm asks of g and g⁻¹: S on wire 1 and CS on the
-- wires 0 1 pass them (a gadget acts on 0 and e₀ alone).  The three
-- decompositions are evaluated in positive forms (dec-a, dec-b, dec-c),
-- each about a third of the size of the commutator form.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Completeness using (Complete)

module Examples.Groups.Clifford+CS.Five.Gadgets (c4 : Complete 4) where

open import Presentation.GroupLike using (module Group-Lemmas)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
  using (Circuit ; S ; CS ; _↑ ; _VRel,_===_ ; grouplike ; _⊢_≈_)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)

open import Examples.Groups.Clifford+CS.Five.Gadgets.Words public
open import Examples.Groups.Clifford+CS.Five.Gadgets.E01 c4 public
open import Examples.Groups.Clifford+CS.Five.Gadgets.E02 c4 public
open import Examples.Groups.Clifford+CS.Five.Gadgets.E03 c4 public
open import Examples.Groups.Clifford+CS.Five.Gadgets.E04 c4 public
open import Examples.Groups.Clifford+CS.Five.Gadgets.E05 c4 public
open import Examples.Groups.Clifford+CS.Five.Gadgets.E06 c4 public
open import Examples.Groups.Clifford+CS.Five.Gadgets.E07 c4 public
open import Examples.Groups.Clifford+CS.Five.Gadgets.E08 c4 public
open import Examples.Groups.Clifford+CS.Five.Gadgets.E09 c4 public
open import Examples.Groups.Clifford+CS.Five.Gadgets.E10 c4 public
open import Examples.Groups.Clifford+CS.Five.Gadgets.E11 c4 public
open import Examples.Groups.Clifford+CS.Five.Gadgets.E12 c4 public
open import Examples.Groups.Clifford+CS.Five.Gadgets.E13 c4 public
open import Examples.Groups.Clifford+CS.Five.Gadgets.E14 c4 public

open Tools (_VRel,_===_ 4)
open Group-Lemmas (_VRel,_===_ 4) grouplike public using (_⁻¹)
open Group-Lemmas (_VRel,_===_ 4) grouplike
  using (inverseˡ ; inverseʳ ; inverseˡ-unique ; inverseʳ-unique ; comm-⁻¹)

------------------------------------------------------------------------
-- The inverses

G-pp⁻ G-rot⁻ G-ki⁻ : Circuit 4
G-pp⁻  = G-pp ⁻¹
G-rot⁻ = G-rot ⁻¹
G-ki⁻  = G-ki ⁻¹

pp-inv : 4 ⊢ G-pp • G-pp⁻ ≈ ε
pp-inv = inverseʳ {G-pp}

pp-inv′ : 4 ⊢ G-pp⁻ • G-pp ≈ ε
pp-inv′ = inverseˡ {G-pp}

rot-inv : 4 ⊢ G-rot • G-rot⁻ ≈ ε
rot-inv = inverseʳ {G-rot}

rot-inv′ : 4 ⊢ G-rot⁻ • G-rot ≈ ε
rot-inv′ = inverseˡ {G-rot}

ki-inv : 4 ⊢ G-ki • G-ki⁻ ≈ ε
ki-inv = inverseʳ {G-ki}

ki-inv′ : 4 ⊢ G-ki⁻ • G-ki ≈ ε
ki-inv′ = inverseˡ {G-ki}

------------------------------------------------------------------------
-- Group algebra

private
  -- (a • b) passes x when a and b do.
  slide : ∀ {a b x : Circuit 4} → a • x ≈ x • a → b • x ≈ x • b → (a • b) • x ≈ x • (a • b)
  slide {a} {b} {x} pa pb = begin
    (a • b) • x   ≈⟨ assoc ⟩
    a • (b • x)   ≈⟨ back a pb ⟩
    a • (x • b)   ≈⟨ sym assoc ⟩
    (a • x) • b   ≈⟨ front b pa ⟩
    (x • a) • b   ≈⟨ assoc ⟩
    x • (a • b)   ∎

  -- a passes x⁻¹ when it passes x.
  pass⁻ : ∀ {a x : Circuit 4} → a • x ≈ x • a → a • x ⁻¹ ≈ x ⁻¹ • a
  pass⁻ = comm-⁻¹

  -- A relator may be rotated.
  rot : ∀ {u v : Circuit 4} → u • v ≈ ε → v • u ≈ ε
  rot {u} {v} e = begin
    v • u                 ≈⟨ sym right-unit ⟩
    (v • u) • ε           ≈⟨ back _ (sym (inverseʳ {v})) ⟩
    (v • u) • (v • v ⁻¹)  ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    v • (u • v) • v ⁻¹    ≈⟨ back v (front (v ⁻¹) e) ⟩
    v • ε • v ⁻¹          ≈⟨ back v left-unit ⟩
    v • v ⁻¹              ≈⟨ inverseʳ {v} ⟩
    ε                     ∎

------------------------------------------------------------------------
-- What Five.F6.Comm asks of g and g⁻¹

-- g = G-rot, g⁻¹ = G-rot⁻.
c-rot-inv : 4 ⊢ G-rot⁻ • G-rot ≈ ε
c-rot-inv = inverseˡ {G-rot}

c-rot-zp : 4 ⊢ (S • S) ↑ • G-rot ≈ G-rot • (S • S) ↑
c-rot-zp = slide rot-s₁ rot-s₁

c-rot-zm : 4 ⊢ (S • S) ↑ • G-rot⁻ ≈ G-rot⁻ • (S • S) ↑
c-rot-zm = pass⁻ {x = G-rot} c-rot-zp

c-rot-csp : 4 ⊢ CS • G-rot ≈ G-rot • CS
c-rot-csp = rot-cs

c-rot-czp : 4 ⊢ (CS • CS) • G-rot ≈ G-rot • (CS • CS)
c-rot-czp = slide rot-cs rot-cs

c-rot-cs⁻p : 4 ⊢ (CS • CS • CS) • G-rot ≈ G-rot • (CS • CS • CS)
c-rot-cs⁻p = slide rot-cs c-rot-czp

-- g = G-ki⁻, g⁻¹ = G-ki.
c-ki-inv : 4 ⊢ G-ki • G-ki⁻ ≈ ε
c-ki-inv = inverseʳ {G-ki}

c-ki-zm : 4 ⊢ (S • S) ↑ • G-ki ≈ G-ki • (S • S) ↑
c-ki-zm = slide ki-s₁ ki-s₁

c-ki-zp : 4 ⊢ (S • S) ↑ • G-ki⁻ ≈ G-ki⁻ • (S • S) ↑
c-ki-zp = pass⁻ {x = G-ki} c-ki-zm

c-ki-csp : 4 ⊢ CS • G-ki⁻ ≈ G-ki⁻ • CS
c-ki-csp = pass⁻ {x = G-ki} ki-cs

c-ki-czp : 4 ⊢ (CS • CS) • G-ki⁻ ≈ G-ki⁻ • (CS • CS)
c-ki-czp = pass⁻ {x = G-ki} (slide ki-cs ki-cs)

c-ki-cs⁻p : 4 ⊢ (CS • CS • CS) • G-ki⁻ ≈ G-ki⁻ • (CS • CS • CS)
c-ki-cs⁻p = pass⁻ {x = G-ki} (slide ki-cs (slide ki-cs ki-cs))

------------------------------------------------------------------------
-- The decompositions

-- iZ⁻¹ = T(XZ).
dec-pp⁻ : 4 ⊢ G-pp⁻ ≈ G-rot⁻ • Sd • G-rot • S
dec-pp⁻ = sym (inverseˡ-unique (begin
  (G-rot⁻ • Sd • G-rot • S) • G-pp
    ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl ⟩
  G-rot⁻ • (Sd • G-rot • S • G-pp)
    ≈⟨ back G-rot⁻ dec-a ⟩
  G-rot⁻ • G-rot
    ≈⟨ inverseˡ {G-rot} ⟩
  ε ∎))

-- The hybrid's inverse is T(its inverse) iZ⁻¹.
dec-ki⁻ : 4 ⊢ G-ki⁻ ≈ (G-ki • Sd • G-ki⁻ • S) • G-pp⁻
dec-ki⁻ = trans (sym s5) (by-passoc (□ • □ • □ • □ • □) ((□ • □ • □ • □) • □) Eq.refl)
  where
  s1 : 4 ⊢ (S • G-pp⁻ • G-ki • G-ki • Sd) • G-ki⁻ ≈ ε
  s1 = trans (front G-ki⁻ dec-b) (inverseʳ {G-ki})

  s2 : 4 ⊢ (S • G-pp⁻) • (G-ki • G-ki • Sd • G-ki⁻) ≈ ε
  s2 = trans (by-passoc ((□ • □) • (□ • □ • □ • □)) ((□ • □ • □ • □ • □) • □) Eq.refl) s1

  s4 : 4 ⊢ G-ki • (G-ki • Sd • G-ki⁻ • S • G-pp⁻) ≈ ε
  s4 = trans (by-passoc (□ • (□ • □ • □ • □ • □)) ((□ • □ • □ • □) • (□ • □)) Eq.refl) (rot s2)

  s5 : 4 ⊢ G-ki • Sd • G-ki⁻ • S • G-pp⁻ ≈ G-ki ⁻¹
  s5 = inverseʳ-unique s4

-- XZ is the conjugate of iZ by the hybrid.
dec-rot : 4 ⊢ G-rot ≈ G-ki⁻ • G-pp • G-ki
dec-rot = begin
  G-rot                    ≈⟨ sym left-unit ⟩
  ε • G-rot                ≈⟨ front G-rot (sym (inverseˡ {G-ki})) ⟩
  (G-ki⁻ • G-ki) • G-rot   ≈⟨ assoc ⟩
  G-ki⁻ • (G-ki • G-rot)   ≈⟨ back G-ki⁻ dec-c ⟩
  G-ki⁻ • G-pp • G-ki      ∎

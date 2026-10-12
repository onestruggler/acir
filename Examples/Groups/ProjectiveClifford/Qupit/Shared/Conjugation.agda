{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- Conjugation equations, over any group-like relation.
--
-- The inverse-free calculus the relation-agnostic derivations run on:
-- Paper-V1.Lemmas.OrderEx (order-Ex) and Paper-V0.Lemmas.ThreeWire
-- (cz-slide and yang-baxter).  It mentions no gate and no rule.
------------------------------------------------------------------------

import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base using (Word ; WRel ; _•_ ; ε ; _^_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
open import Notations

module Examples.Groups.ProjectiveClifford.Qupit.Shared.Conjugation where

------------------------------------------------------------------------
-- Conjugation equations
--
-- Conj a u u' says that conjugating by a carries u to u', in the form
-- a • u ≈ u' • a, which needs no inverse word.  They compose (conj-∘),
-- respect products and powers of what is carried (conj-•, conj-^), and
-- cancel (conj-cancelʳ, conj-cancelˡ, conj-unique), and that is all the
-- group theory the derivation uses.

module Conjugation {G : Set} (Δ : WRel G) (gl : Grouplike Δ) where

  open PB Δ hiding (_===_)
  open PP Δ
  open SR word-setoid
  open Pattern-Assoc
  open Group-Lemmas Δ gl using (•-cancelˡ ; •-cancelʳ)

  Conj : Word G → Word G → Word G → Set
  Conj a u u' = a • u ≈ u' • a

  -- First a, then b.
  conj-∘ : ∀ {a b u u' u''} → Conj a u u' → Conj b u' u'' → Conj (b • a) u u''
  conj-∘ {a} {b} {u} {u'} {u''} e f = begin
    (b • a) • u    ≈⟨ assoc ⟩
    b • (a • u)    ≈⟨ cright e ⟩
    b • (u' • a)   ≈⟨ sym assoc ⟩
    (b • u') • a   ≈⟨ cleft f ⟩
    (u'' • b) • a  ≈⟨ assoc ⟩
    u'' • (b • a) ∎

  conj-• : ∀ {a u u' v v'} → Conj a u u' → Conj a v v' → Conj a (u • v) (u' • v')
  conj-• {a} {u} {u'} {v} {v'} e f = begin
    a • (u • v)    ≈⟨ sym assoc ⟩
    (a • u) • v    ≈⟨ cleft e ⟩
    (u' • a) • v   ≈⟨ assoc ⟩
    u' • (a • v)   ≈⟨ cright f ⟩
    u' • (v' • a)  ≈⟨ sym assoc ⟩
    (u' • v') • a ∎

  conj-ε : ∀ {a} → Conj a ε ε
  conj-ε = trans right-unit (sym left-unit)

  conj-^ : ∀ {a u u'} → Conj a u u' → ∀ k → Conj a (u ^ k) (u' ^ k)
  conj-^ e ₀ = conj-ε
  conj-^ e ₁ = e
  conj-^ e (₂₊ k) = conj-• e (conj-^ e (₁₊ k))

  -- A power of something that fixes u fixes u.
  conj-^ˡ : ∀ {a u} → Conj a u u → ∀ k → Conj (a ^ k) u u
  conj-^ˡ e ₀ = trans left-unit (sym right-unit)
  conj-^ˡ e ₁ = e
  conj-^ˡ e (₂₊ k) = conj-∘ (conj-^ˡ e (₁₊ k)) e

  conj-congˡ : ∀ {a a' u u'} → a ≈ a' → Conj a u u' → Conj a' u u'
  conj-congˡ eq e = trans (cleft sym eq) (trans e (cright eq))

  conj-cong : ∀ {a u u' v v'} → u ≈ v → u' ≈ v' → Conj a u u' → Conj a v v'
  conj-cong eu eu' e = trans (cright sym eu) (trans e (cleft eu'))

  conj-unique : ∀ {a u u' u''} → Conj a u u' → Conj a u u'' → u' ≈ u''
  conj-unique e f = •-cancelʳ (trans (sym e) f)

  -- A commutation read the other way round.
  comm-sym : ∀ {a u} → Conj a u u → Conj u a a
  comm-sym e = sym e

  -- Inverting the conjugator …
  conj-inv : ∀ {a b u u'} → b • a ≈ ε → a • b ≈ ε → Conj a u u' → Conj b u' u
  conj-inv {a} {b} {u} {u'} ba ab e = begin
    b • u'               ≈⟨ sym right-unit ⟩
    (b • u') • ε         ≈⟨ cright sym ab ⟩
    (b • u') • (a • b)   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) auto ⟩
    b • (u' • a) • b     ≈⟨ cright cleft sym e ⟩
    b • (a • u) • b      ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) auto ⟩
    (b • a) • (u • b)    ≈⟨ cleft ba ⟩
    ε • (u • b)          ≈⟨ left-unit ⟩
    u • b ∎

  -- … and the word it carries.
  conj-inv-u : ∀ {a u u' v v'} → u • v ≈ ε → v' • u' ≈ ε → Conj a u u' → Conj a v v'
  conj-inv-u {a} {u} {u'} {v} {v'} uv vu e = begin
    a • v                  ≈⟨ sym left-unit ⟩
    ε • (a • v)            ≈⟨ cleft sym vu ⟩
    (v' • u') • (a • v)    ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) auto ⟩
    v' • (u' • a) • v      ≈⟨ cright cleft sym e ⟩
    v' • (a • u) • v       ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) auto ⟩
    (v' • a) • (u • v)     ≈⟨ cright uv ⟩
    (v' • a) • ε           ≈⟨ right-unit ⟩
    v' • a ∎

  -- The literal conjugate, read from either end.
  conj-lit : ∀ {a a' u} → a' • a ≈ ε → Conj a u (a • (u • a'))
  conj-lit {a} {a'} {u} e = begin
    a • u                  ≈⟨ sym right-unit ⟩
    (a • u) • ε            ≈⟨ cright sym e ⟩
    (a • u) • (a' • a)     ≈⟨ by-passoc ((□ • □) • (□ • □)) ((□ • (□ • □)) • □) auto ⟩
    (a • (u • a')) • a ∎

  conj-lit' : ∀ {a a' u} → a • a' ≈ ε → Conj a (a' • (u • a)) u
  conj-lit' {a} {a'} {u} e = begin
    a • (a' • (u • a))     ≈⟨ sym assoc ⟩
    (a • a') • (u • a)     ≈⟨ cleft e ⟩
    ε • (u • a)            ≈⟨ left-unit ⟩
    u • a ∎

  -- Cancelling a factor of a composite conjugator whose action is known.
  conj-cancelʳ : ∀ {a b u u' u''} → Conj (b • a) u u'' → Conj a u u' → Conj b u' u''
  conj-cancelʳ {a} {b} {u} {u'} {u''} e f = •-cancelʳ {h = a} (begin
    (b • u') • a     ≈⟨ assoc ⟩
    b • (u' • a)     ≈⟨ cright sym f ⟩
    b • (a • u)      ≈⟨ sym assoc ⟩
    (b • a) • u      ≈⟨ e ⟩
    u'' • (b • a)    ≈⟨ sym assoc ⟩
    (u'' • b) • a ∎)

  conj-cancelˡ : ∀ {a b u u' u''} → Conj (b • a) u u'' → Conj b u' u'' → Conj a u u'
  conj-cancelˡ {a} {b} {u} {u'} {u''} e f = •-cancelˡ {g = b} (begin
    b • (a • u)      ≈⟨ sym assoc ⟩
    (b • a) • u      ≈⟨ e ⟩
    u'' • (b • a)    ≈⟨ sym assoc ⟩
    (u'' • b) • a    ≈⟨ cleft sym f ⟩
    (b • u') • a     ≈⟨ assoc ⟩
    b • (u' • a) ∎)

  -- Inverse pairs.
  cancel-• : ∀ {a a' w} → a' • a ≈ ε → a' • (a • w) ≈ w
  cancel-• e = trans (sym assoc) (trans (cleft e) left-unit)

  tele : ∀ {w x x' w'} → x • x' ≈ ε → w • w' ≈ ε → (w • x) • (x' • w') ≈ ε
  tele {w} {x} {x'} {w'} xx' ww' = begin
    (w • x) • (x' • w')   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • ((□ • □) • □)) auto ⟩
    w • ((x • x') • w')   ≈⟨ cright trans (cleft xx') left-unit ⟩
    w • w'                ≈⟨ ww' ⟩
    ε ∎

  -- Conjugates of an inverse pair are an inverse pair.
  sandwich-inv : ∀ {a a' u u'} → a • a' ≈ ε → a' • a ≈ ε → u • u' ≈ ε →
                 (a' • (u • a)) • (a' • (u' • a)) ≈ ε
  sandwich-inv {a} {a'} {u} {u'} aa' a'a uu' = begin
    (a' • (u • a)) • (a' • (u' • a))
      ≈⟨ by-passoc ((□ • (□ • □)) • (□ • (□ • □))) (□ • (□ • ((□ • □) • (□ • □)))) auto ⟩
    a' • (u • ((a • a') • (u' • a)))
      ≈⟨ cright cright trans (cleft aa') left-unit ⟩
    a' • (u • (u' • a))
      ≈⟨ cright cancel-• uu' ⟩
    a' • a
      ≈⟨ a'a ⟩
    ε ∎

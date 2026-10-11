------------------------------------------------------------------------
-- Presentations of groups
--
-- Word algebra for the auxiliary equations of Appendix D
--
-- Facts about words over any relation, stated for arbitrary words: what
-- passes a and b passes a b a b, a word of involutions followed by its
-- reverse is ε, inverses are unique, …  The derivations on three, four
-- and five qubits instantiate them with gates; the same shapes recur
-- one level up, with the doubly controlled ZX in the role the
-- controlled H had.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (WRel)

module Examples.Groups.Real-Clifford+CH.WordAlgebra {X : Set} (Γ : WRel X) where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

open Tools Γ


-- (a b a b)(b a b a) = ε for involutions a and b.
invol-abab : ∀ {a b} → a • a ≈ ε → b • b ≈ ε → (a • b • a • b) • (b • a • b • a) ≈ ε
invol-abab {a} {b} ea eb = begin
  (a • b • a • b) • (b • a • b • a)
    ≈⟨ by-passoc ((□ • □ • □ • □) • (□ • □ • □ • □)) (□ • □ • □ • (□ • □) • □ • □ • □) Eq.refl ⟩
  a • b • a • (b • b) • a • b • a
    ≈⟨ back _ (back _ (back _ (cancelˢ _ eb))) ⟩
  a • b • a • a • b • a
    ≈⟨ by-passoc (□ • □ • □ • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
  a • b • (a • a) • b • a
    ≈⟨ back _ (back _ (cancelˢ _ ea)) ⟩
  a • b • b • a
    ≈⟨ by-passoc (□ • □ • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  a • (b • b) • a
    ≈⟨ back _ (cancelˢ _ eb) ⟩
  a • a
    ≈⟨ ea ⟩
  ε ∎

-- What passes a and b passes a b a b.
comm-abab : ∀ {x a b} → x • a ≈ a • x → x • b ≈ b • x →
            x • (a • b • a • b) ≈ (a • b • a • b) • x
comm-abab {x} {a} {b} xa xb = begin
  x • (a • b • a • b)
    ≈⟨ by-passoc (□ • (□ • □ • □ • □)) ((□ • □) • □ • □ • □) Eq.refl ⟩
  (x • a) • b • a • b
    ≈⟨ front _ xa ⟩
  (a • x) • b • a • b
    ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □) • □ • □) Eq.refl ⟩
  a • (x • b) • a • b
    ≈⟨ back _ (front _ xb) ⟩
  a • (b • x) • a • b
    ≈⟨ by-passoc (□ • (□ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
  a • b • (x • a) • b
    ≈⟨ back _ (back _ (front _ xa)) ⟩
  a • b • (a • x) • b
    ≈⟨ by-passoc (□ • □ • (□ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
  a • b • a • (x • b)
    ≈⟨ back _ (back _ (back _ xb)) ⟩
  a • b • a • (b • x)
    ≈⟨ by-passoc (□ • □ • □ • (□ • □)) ((□ • □ • □ • □) • □) Eq.refl ⟩
  (a • b • a • b) • x ∎

-- b z b = z when z passes the involution b.
bzb : ∀ {b z} → b • b ≈ ε → z • b ≈ b • z → b • z • b ≈ z
bzb {b} {z} eb zb = trans (back _ zb) (cancelˡ _ eb)

-- Merging a control: with b′ = b z in place of b, the word
-- a b′ a b′ followed by a b a b is a z a z, as soon as z turns
-- b a b a into a b a b.
merge : ∀ {a b z} → a • a ≈ ε → b • b ≈ ε → z • b ≈ b • z →
        z • (b • a • b • a) ≈ (a • b • a • b) • z →
        (a • (b • z) • a • (b • z)) • (a • b • a • b) ≈ a • z • a • z
merge {a} {b} {z} ea eb zb h = begin
  (a • (b • z) • a • (b • z)) • (a • b • a • b)
    ≈⟨ front _ (back _ (back _ (back _ (sym zb)))) ⟩
  (a • (b • z) • a • (z • b)) • (a • b • a • b)
    ≈⟨ by-passoc ((□ • (□ • □) • □ • (□ • □)) • (□ • □ • □ • □))
                 (□ • □ • □ • □ • (□ • (□ • □ • □ • □)) • □) Eq.refl ⟩
  a • b • z • a • (z • (b • a • b • a)) • b
    ≈⟨ back _ (back _ (back _ (back _ (front _ h)))) ⟩
  a • b • z • a • ((a • b • a • b) • z) • b
    ≈⟨ by-passoc (□ • □ • □ • □ • ((□ • □ • □ • □) • □) • □)
                 (□ • □ • □ • (□ • □) • □ • □ • □ • □ • □) Eq.refl ⟩
  a • b • z • (a • a) • b • a • b • z • b
    ≈⟨ back _ (back _ (back _ (cancelˢ _ ea))) ⟩
  a • b • z • b • a • b • z • b
    ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □ • □) (□ • (□ • □ • □) • □ • (□ • □ • □)) Eq.refl ⟩
  a • (b • z • b) • a • (b • z • b)
    ≈⟨ back _ (cong (bzb eb zb) (back _ (bzb eb zb))) ⟩
  a • z • a • z ∎

-- A gate g that p passes, and that q exchanges with g′, passes
-- p q p q.
pass-pqpq : ∀ {p q g g′} → p • g ≈ g • p → p • g′ ≈ g′ • p →
            q • g ≈ g′ • q → q • g′ ≈ g • q →
            (p • q • p • q) • g ≈ g • (p • q • p • q)
pass-pqpq {p} {q} {g} {g′} pg pg′ qg qg′ = begin
  (p • q • p • q) • g
    ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
  p • q • p • (q • g)
    ≈⟨ back _ (back _ (back _ qg)) ⟩
  p • q • p • (g′ • q)
    ≈⟨ by-passoc (□ • □ • □ • (□ • □)) (□ • □ • (□ • □) • □) Eq.refl ⟩
  p • q • (p • g′) • q
    ≈⟨ back _ (back _ (front _ pg′)) ⟩
  p • q • (g′ • p) • q
    ≈⟨ by-passoc (□ • □ • (□ • □) • □) (□ • (□ • □) • □ • □) Eq.refl ⟩
  p • (q • g′) • p • q
    ≈⟨ back _ (front _ qg′) ⟩
  p • (g • q) • p • q
    ≈⟨ by-passoc (□ • (□ • □) • □ • □) ((□ • □) • □ • □ • □) Eq.refl ⟩
  (p • g) • q • p • q
    ≈⟨ front _ pg ⟩
  (g • p) • q • p • q
    ≈⟨ assoc ⟩
  g • (p • q • p • q) ∎

-- What passes u and v passes u v.
comm-• : ∀ {x u v} → x • u ≈ u • x → x • v ≈ v • x → x • (u • v) ≈ (u • v) • x
comm-• {x} {u} {v} xu xv = begin
  x • (u • v)   ≈⟨ sym assoc ⟩
  (x • u) • v   ≈⟨ front _ xu ⟩
  (u • x) • v   ≈⟨ assoc ⟩
  u • (x • v)   ≈⟨ back _ xv ⟩
  u • (v • x)   ≈⟨ sym assoc ⟩
  (u • v) • x ∎

-- Two gates that each exchange w and v: their product passes w.
pass-xy : ∀ {x y w v} → y • w ≈ v • y → x • v ≈ w • x → (x • y) • w ≈ w • (x • y)
pass-xy {x} {y} {w} {v} yw xv = begin
  (x • y) • w   ≈⟨ assoc ⟩
  x • (y • w)   ≈⟨ back _ yw ⟩
  x • (v • y)   ≈⟨ sym assoc ⟩
  (x • v) • y   ≈⟨ front _ xv ⟩
  (w • x) • y   ≈⟨ assoc ⟩
  w • (x • y) ∎

-- A word of involutions followed by its reverse, one letter at a
-- time.
unwrap : ∀ {c p s} → c • c ≈ ε → p • s ≈ ε → (p • c) • (c • s) ≈ ε
unwrap {c} {p} {s} ec e = begin
  (p • c) • (c • s)   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  p • (c • c) • s     ≈⟨ back _ (cancelˢ _ ec) ⟩
  p • s               ≈⟨ e ⟩
  ε ∎

-- The product of two commuting involutions is an involution.
invol-comm : ∀ {x t} → x • x ≈ ε → t • t ≈ ε → x • t ≈ t • x → (x • t) • (x • t) ≈ ε
invol-comm {x} {t} ex et xt = begin
  (x • t) • (x • t)   ≈⟨ front _ xt ⟩
  (t • x) • (x • t)   ≈⟨ unwrap ex et ⟩
  ε ∎

-- An involution x d b stays one when d is multiplied by a c that
-- passes b x and is absorbed by d.
twist : ∀ {x d b c} → c • (b • x) ≈ (b • x) • c → c • d • c ≈ d →
        (x • d • b) • (x • d • b) ≈ ε → (x • (d • c) • b) • (x • (d • c) • b) ≈ ε
twist {x} {d} {b} {c} cz cdc e = begin
  (x • (d • c) • b) • (x • (d • c) • b)
    ≈⟨ by-passoc ((□ • (□ • □) • □) • (□ • (□ • □) • □))
                 (□ • □ • (□ • (□ • □)) • □ • □ • □) Eq.refl ⟩
  x • d • (c • (b • x)) • d • c • b
    ≈⟨ back _ (back _ (front _ cz)) ⟩
  x • d • ((b • x) • c) • d • c • b
    ≈⟨ by-passoc (□ • □ • ((□ • □) • □) • □ • □ • □)
                 (□ • □ • □ • □ • (□ • □ • □) • □) Eq.refl ⟩
  x • d • b • x • (c • d • c) • b
    ≈⟨ back _ (back _ (back _ (back _ (front _ cdc)))) ⟩
  x • d • b • x • d • b
    ≈⟨ by-passoc (□ • □ • □ • □ • □ • □) ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
  (x • d • b) • (x • d • b)
    ≈⟨ e ⟩
  ε ∎

-- Inverses are unique.
inv-unique : ∀ {x x′ y y′} → x • x′ ≈ ε → y′ • y ≈ ε → x ≈ y → x′ ≈ y′
inv-unique {x} {x′} {y} {y′} ex ey e = begin
  x′              ≈⟨ sym left-unit ⟩
  ε • x′          ≈⟨ front _ (sym ey) ⟩
  (y′ • y) • x′   ≈⟨ assoc ⟩
  y′ • (y • x′)   ≈⟨ back _ (front _ (sym e)) ⟩
  y′ • (x • x′)   ≈⟨ back _ ex ⟩
  y′ • ε          ≈⟨ right-unit ⟩
  y′ ∎

-- What passes w passes its inverse.
comm-inv : ∀ {x w v} → w • v ≈ ε → v • w ≈ ε → x • w ≈ w • x → x • v ≈ v • x
comm-inv {x} {w} {v} wv vw xw = begin
  x • v               ≈⟨ sym left-unit ⟩
  ε • x • v           ≈⟨ front _ (sym vw) ⟩
  (v • w) • x • v     ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  v • (w • x) • v     ≈⟨ back _ (front _ (sym xw)) ⟩
  v • (x • w) • v     ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
  (v • x) • (w • v)   ≈⟨ back _ wv ⟩
  (v • x) • ε         ≈⟨ right-unit ⟩
  v • x ∎

------------------------------------------------------------------------
-- Boxes: words of the shape W c V c with V the inverse of W

-- V c W = W c V when V is W d both ways round and d passes c.
flip-WcV : ∀ {W V c d} → V ≈ W • d → V ≈ d • W → d • c ≈ c • d → V • c • W ≈ W • c • V
flip-WcV {W} {V} {c} {d} e₁ e₂ dc = begin
  V • c • W           ≈⟨ front _ e₁ ⟩
  (W • d) • c • W     ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  W • (d • c) • W     ≈⟨ back _ (front _ dc) ⟩
  W • (c • d) • W     ≈⟨ by-passoc (□ • (□ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
  W • c • (d • W)     ≈⟨ back _ (back _ (sym e₂)) ⟩
  W • c • V ∎

-- What exchanges W and V and passes c passes the box.
box-pass : ∀ {z W V c} → z • W ≈ V • z → z • V ≈ W • z → z • c ≈ c • z →
           V • c • W ≈ W • c • V → z • (W • c • V • c) ≈ (W • c • V • c) • z
box-pass {z} {W} {V} {c} zW zV zc fl = begin
  z • (W • c • V • c)   ≈⟨ by-passoc (□ • (□ • □ • □ • □)) ((□ • □) • □ • □ • □) Eq.refl ⟩
  (z • W) • c • V • c   ≈⟨ front _ zW ⟩
  (V • z) • c • V • c   ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □) • □ • □) Eq.refl ⟩
  V • (z • c) • V • c   ≈⟨ back _ (front _ zc) ⟩
  V • (c • z) • V • c   ≈⟨ by-passoc (□ • (□ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
  V • c • (z • V) • c   ≈⟨ back _ (back _ (front _ zV)) ⟩
  V • c • (W • z) • c   ≈⟨ by-passoc (□ • □ • (□ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
  V • c • W • (z • c)   ≈⟨ back _ (back _ (back _ zc)) ⟩
  V • c • W • (c • z)   ≈⟨ by-passoc (□ • □ • □ • (□ • □)) ((□ • □ • □) • □ • □) Eq.refl ⟩
  (V • c • W) • c • z   ≈⟨ front _ fl ⟩
  (W • c • V) • c • z   ≈⟨ by-passoc ((□ • □ • □) • □ • □) ((□ • □ • □ • □) • □) Eq.refl ⟩
  (W • c • V • c) • z ∎

-- A gate b that passes W and V at the price of an involution t = d b
-- passing c, passes the box.
box-pass₂ : ∀ {b t W V c} → t • t ≈ ε → W • V ≈ ε → V • W ≈ ε → b • b ≈ ε →
            b • W ≈ W • t → t • c ≈ c • t → b • c ≈ c • b →
            b • (W • c • V • c) ≈ (W • c • V • c) • b
box-pass₂ {b} {t} {W} {V} {c} tt WV VW bb bW tc bc = begin
  b • (W • c • V • c)   ≈⟨ by-passoc (□ • (□ • □ • □ • □)) ((□ • □) • □ • □ • □) Eq.refl ⟩
  (b • W) • c • V • c   ≈⟨ front _ bW ⟩
  (W • t) • c • V • c   ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □) • □ • □) Eq.refl ⟩
  W • (t • c) • V • c   ≈⟨ back _ (front _ tc) ⟩
  W • (c • t) • V • c   ≈⟨ by-passoc (□ • (□ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
  W • c • (t • V) • c   ≈⟨ back _ (back _ (front _ tV)) ⟩
  W • c • (V • b) • c   ≈⟨ by-passoc (□ • □ • (□ • □) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
  W • c • V • (b • c)   ≈⟨ back _ (back _ (back _ bc)) ⟩
  W • c • V • (c • b)   ≈⟨ by-passoc (□ • □ • □ • (□ • □)) ((□ • □ • □ • □) • □) Eq.refl ⟩
  (W • c • V • c) • b ∎
  where
  Vb : V • b ≈ t • V
  Vb = begin
    V • b               ≈⟨ sym right-unit ⟩
    (V • b) • ε         ≈⟨ back _ (sym WV) ⟩
    (V • b) • (W • V)   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    V • (b • W) • V     ≈⟨ back _ (front _ bW) ⟩
    V • (W • t) • V     ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
    (V • W) • t • V     ≈⟨ front _ VW ⟩
    ε • t • V           ≈⟨ left-unit ⟩
    t • V ∎
  tV : t • V ≈ V • b
  tV = begin
    t • V               ≈⟨ sym right-unit ⟩
    (t • V) • ε         ≈⟨ back _ (sym bb) ⟩
    (t • V) • (b • b)   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    t • (V • b) • b     ≈⟨ back _ (front _ Vb) ⟩
    t • (t • V) • b     ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
    (t • t) • V • b     ≈⟨ cancelˢ _ tt ⟩
    V • b ∎

-- Peeling an inverse pair off the middle.
unwrap′ : ∀ {u v p s} → u • v ≈ ε → p • s ≈ ε → (p • u) • (v • s) ≈ ε
unwrap′ {u} {v} {p} {s} uv e = begin
  (p • u) • (v • s)   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  p • (u • v) • s     ≈⟨ back _ (cancelˢ′ uv) ⟩
  p • s               ≈⟨ e ⟩
  ε ∎
  where
  cancelˢ′ : u • v ≈ ε → (u • v) • s ≈ s
  cancelˢ′ h = trans (front _ h) left-unit

-- Exchanging two controls.  With x = a b a and y = a c a for commuting
-- involutions b and c: if x b and y c square to d and d′, and x y b c —
-- the same word with b c in place of b — squares to d d′, then the
-- commutator of x and c is that of b and y.
comm-swap : ∀ {x y b c d d′} →
            x • x ≈ ε → y • y ≈ ε → b • b ≈ ε → c • c ≈ ε → d • d ≈ ε → d′ • d′ ≈ ε →
            x • y ≈ y • x → b • c ≈ c • b → d • y ≈ y • d → d′ • b ≈ b • d′ →
            x • b • x • b ≈ d → y • c • y • c ≈ d′ →
            (x • y • b • c) • (x • y • b • c) ≈ d • d′ →
            x • c • x • c ≈ b • y • b • y
comm-swap {x} {y} {b} {c} {d} {d′} xx yy bb cc dd d′d′ xy bc dy d′b xbxb ycyc SS = sym (begin
  b • y • b • y
    ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □) • (□ • □)) Eq.refl ⟩
  (b • y) • (b • y)
    ≈⟨ back _ (sym left-unit) ⟩
  (b • y) • ε • (b • y)
    ≈⟨ back _ (front _ (sym T≈ε)) ⟩
  (b • y) • ((y • b) • box • (y • b)) • (b • y)
    ≈⟨ by-passoc ((□ • □) • ((□ • □) • □ • (□ • □)) • (□ • □))
                 (((□ • □) • (□ • □)) • □ • ((□ • □) • (□ • □))) Eq.refl ⟩
  ((b • y) • (y • b)) • box • ((y • b) • (b • y))
    ≈⟨ cong (unwrap yy bb) (back _ (unwrap bb yy)) ⟩
  ε • box • ε
    ≈⟨ trans left-unit right-unit ⟩
  box ∎)
  where
  box = x • c • x • c

  f1 : b • x ≈ x • d • b
  f1 = begin
    b • x                         ≈⟨ insertˡ _ xx ⟩
    x • x • b • x                 ≈⟨ insertʳ _ bb ⟩
    ((x • x • b • x) • b) • b     ≈⟨ by-passoc (((□ • □ • □ • □) • □) • □) (□ • (□ • □ • □ • □) • □) Eq.refl ⟩
    x • (x • b • x • b) • b       ≈⟨ back _ (front _ xbxb) ⟩
    x • d • b ∎

  f2 : c • y ≈ y • d′ • c
  f2 = begin
    c • y                         ≈⟨ insertˡ _ yy ⟩
    y • y • c • y                 ≈⟨ insertʳ _ cc ⟩
    ((y • y • c • y) • c) • c     ≈⟨ by-passoc (((□ • □ • □ • □) • □) • □) (□ • (□ • □ • □ • □) • □) Eq.refl ⟩
    y • (y • c • y • c) • c       ≈⟨ back _ (front _ ycyc) ⟩
    y • d′ • c ∎

  f3 : c • x ≈ x • box • c
  f3 = begin
    c • x                         ≈⟨ insertˡ _ xx ⟩
    x • x • c • x                 ≈⟨ insertʳ _ cc ⟩
    ((x • x • c • x) • c) • c     ≈⟨ by-passoc (((□ • □ • □ • □) • □) • □) (□ • (□ • □ • □ • □) • □) Eq.refl ⟩
    x • (x • c • x • c) • c ∎

  xyx : x • y • x ≈ y
  xyx = trans (back _ (sym xy)) (cancelˡ _ xx)

  T = (y • b) • box • (y • b)

  SS-form : (x • y • b • c) • (x • y • b • c) ≈ d • T • d′
  SS-form = begin
    (x • y • b • c) • (x • y • b • c)
      ≈⟨ by-passoc ((□ • □ • □ • □) • (□ • □ • □ • □)) (□ • □ • □ • (□ • □) • □ • □ • □) Eq.refl ⟩
    x • y • b • (c • x) • y • b • c
      ≈⟨ back _ (back _ (back _ (front _ f3))) ⟩
    x • y • b • (x • box • c) • y • b • c
      ≈⟨ by-passoc (□ • □ • □ • (□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • (□ • □) • □ • □) Eq.refl ⟩
    x • y • (b • x) • box • (c • y) • b • c
      ≈⟨ back _ (back _ (cong f1 (back _ (front _ f2)))) ⟩
    x • y • (x • d • b) • box • (y • d′ • c) • b • c
      ≈⟨ by-passoc (□ • □ • (□ • □ • □) • □ • (□ • □ • □) • □ • □)
                   ((□ • □ • □) • □ • □ • □ • □ • □ • (□ • □ • □)) Eq.refl ⟩
    (x • y • x) • d • b • box • y • d′ • (c • b • c)
      ≈⟨ cong xyx (back _ (back _ (back _ (back _ (back _ (bzb cc bc)))))) ⟩
    y • d • b • box • y • d′ • b
      ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □) ((□ • □) • □ • □ • □ • (□ • □)) Eq.refl ⟩
    (y • d) • b • box • y • (d′ • b)
      ≈⟨ cong (sym dy) (back _ (back _ (back _ d′b))) ⟩
    (d • y) • b • box • y • (b • d′)
      ≈⟨ by-passoc ((□ • □) • □ • □ • □ • (□ • □)) (□ • ((□ • □) • □ • (□ • □)) • □) Eq.refl ⟩
    d • ((y • b) • box • (y • b)) • d′ ∎

  T≈ε : T ≈ ε
  T≈ε = begin
    T                           ≈⟨ insertˡ _ dd ⟩
    d • d • T                   ≈⟨ insertʳ _ d′d′ ⟩
    ((d • d • T) • d′) • d′     ≈⟨ by-passoc (((□ • □ • □) • □) • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
    d • (d • T • d′) • d′       ≈⟨ back _ (front _ (trans (sym SS-form) SS)) ⟩
    d • (d • d′) • d′           ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • (□ • □)) Eq.refl ⟩
    (d • d) • (d′ • d′)         ≈⟨ cong dd d′d′ ⟩
    ε • ε                       ≈⟨ left-unit ⟩
    ε ∎

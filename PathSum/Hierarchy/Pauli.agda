------------------------------------------------------------------------
-- Presentations of groups
--
-- The Pauli group on n qubits
--
-- C₁, the first level of the Clifford hierarchy in the preliminaries
-- of Amy's QPL 2018 paper, is the Pauli group: products of X, Y and Z
-- on the wires, with a phase.  Every such product is, up to
-- reordering, a single operator
--
--    P(a, x, z) = i^a X^x Z^z ,     P(a, x, z) |v⟩ = i^a (-1)^(z·v) |v ⊕ x⟩ ,
--
-- for an integer a (read modulo 4) and bit vectors x, z (Y_w is
-- P(1, e_w, e_w) = i X_w Z_w), so a Pauli is given by its data
-- PauliData and pauli p is its operator (PathSum.Hierarchy.Operator):
-- normalisation 0, and the entry from v to u is i^a (-1)^(z·v) when
-- u = v ⊕ x and 0 otherwise, the phase being ζ^(¼a + ½(z·v)) with
-- numerators over N = 2^M as everywhere in the development (i = ζ^¼,
-- -1 = ζ^½).  The parity z·v is dot z v, the sum of z_j v_j modulo 2.
--
-- The group law is read off the data:
--
--   * P(a, x, z) P(b, x′, z′) = P(a + b + 2(z·x′), x ⊕ x′, z ⊕ z′)
--     (pauli-·): moving Z^z past X^x′ costs (-1)^(z·x′);
--   * P(a, x, z)† = P(-a + 2(z·x), x, z) (pauli-†);
--   * so every Pauli is unitary (pauli-unitary), and two Paulis
--     commute up to the sign (-1)^ω, ω = z·x′ ⊕ z′·x the symplectic
--     form (pauli-comm), whence P Q P† = ±Q (pauli-conj);
--   * a phase i^t multiplies into the data (◃-pauli), the data are
--     read pointwise and their phase modulo 4 (pauli-≈), and P(0,0,0)
--     is the identity (pauli-I).
--
-- Each fact is proved on entries.  The entry of a product with a Pauli
-- on either side collapses to a single entry of the other factor,
-- rotated (·-pauli, pauli-·′ below), which is also how the
-- intertwining of the gates with the Paulis is computed in
-- PathSum.Hierarchy.Gates.  The rest is arithmetic of parities: dot is
-- additive in each argument (dot-⊕ˡ, dot-⊕ʳ) and reads one bit of the
-- other argument at a unit vector (dot-e), and modulo N half a bit
-- adds like a bit (PathSum.Maslov.Arith.½-xor).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.Pauli (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; if_then_else_; _∧_; _xor_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Properties using
  (+-identityʳ; +-inverseˡ; *-zeroʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (yes; no; ⌊_⌋)

import Data.Fin.Properties as Fin

-- The precision: phases are numerators over 2^M.  M, the constants ⅛,
-- ¼, ½ and the powers of 2 are exported from here, so that every
-- module of the hierarchy writes them the same way: two copies of ½
-- are equal only after unfolding, and Agda compares rotations by such
-- differently written exponents by unfolding Cyclotomic's coefficients,
-- which is expensive.

M : ℕ
M = suc (suc (suc M₀))

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; same; same-true; same-intro; same-≗)
open import PathSum.Compose.Matrix M₀ using (if-⊛; ⊛-if; ⊛-zpow)
open import PathSum.Compose.Sum M₀ using (Σᴮ-δ; if-cong; bool-iff; rot-if)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; Σᴮ-cong; zpow; rot; rot-map; Respects; N)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Hierarchy.Operator M₀
open import PathSum.Maslov.Arith M₀ using (¼+¼; ½·2; ½-xor; ½-self)
open import PathSum.Order M public using (pow)
open import PathSum.Reduction M public using (⅛; ¼; ½)
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; ≡ᴺ-refl; ≡ᴺ-≡; ≡ᴺ-sym; ≡ᴺ-trans; ≡ᴺ-+; ≡ᴺ-neg; ≡ᴺ-N; zpow-≡ᴺ;
   module ≡ᴺ-Reasoning)
open import PathSum.Ring M₀ using (_⊛_; ⊛-cong; zpow-⊛; conj; conj-zpow; conj-0ᴬ)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  variable
    n : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-refl : {a : Amp} → a ≐ a
  ≐-refl _ = refl

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Bit vectors

infixl 6 _⊕ᵛ_

_⊕ᵛ_ : Assign n → Assign n → Assign n
(x ⊕ᵛ y) j = x j xor y j

0ᵛ : Assign n
0ᵛ _ = false

-- The unit vector at w.

eᵛ : Fin n → Assign n
eᵛ w = 0ᵛ [ w ≔ true ]

-- Boolean identities, by cases.

xor-move : ∀ a b c → a xor b ≡ c → c xor b ≡ a
xor-move true  true  .false refl = refl
xor-move true  false .true  refl = refl
xor-move false true  .true  refl = refl
xor-move false false .false refl = refl

xor-assoc : ∀ a b c → (a xor b) xor c ≡ a xor (b xor c)
xor-assoc true  true  true  = refl
xor-assoc true  true  false = refl
xor-assoc true  false true  = refl
xor-assoc true  false false = refl
xor-assoc false b     c     = refl

xor-comm : ∀ a b → a xor b ≡ b xor a
xor-comm true  true  = refl
xor-comm true  false = refl
xor-comm false true  = refl
xor-comm false false = refl

xor-self : ∀ a → a xor a ≡ false
xor-self true  = refl
xor-self false = refl

xor-false : ∀ a → a xor false ≡ a
xor-false true  = refl
xor-false false = refl

-- Comparing an assignment shifted by x with another: the shift moves
-- across.

same-⊕-swap : (w x u : Assign n) → same (w ⊕ᵛ x) u ≡ same (u ⊕ᵛ x) w
same-⊕-swap w x u = bool-iff
  (λ h → same-intro (u ⊕ᵛ x) w (λ j →
     xor-move (w j) (x j) (u j) (same-true (w ⊕ᵛ x) u h j)))
  (λ h → same-intro (w ⊕ᵛ x) u (λ j →
     xor-move (u j) (x j) (w j) (same-true (u ⊕ᵛ x) w h j)))


------------------------------------------------------------------------
-- The parity z · v

dot : Assign n → Assign n → Bool
dot {ℕ.zero}  z v = false
dot {ℕ.suc n} z v =
  (z zero ∧ v zero) xor dot (λ j → z (suc j)) (λ j → v (suc j))

private
  tail : Assign (suc n) → Assign n
  tail v j = v (suc j)

dot-cong : {z z′ v v′ : Assign n} → (∀ j → z j ≡ z′ j) →
           (∀ j → v j ≡ v′ j) → dot z v ≡ dot z′ v′
dot-cong {ℕ.zero}  _ _ = refl
dot-cong {ℕ.suc n} zz vv = cong₂ _xor_ (cong₂ _∧_ (zz zero) (vv zero))
  (dot-cong (λ j → zz (suc j)) (λ j → vv (suc j)))

private
  ∧-comm : ∀ a b → (a ∧ b) ≡ (b ∧ a)
  ∧-comm true  true  = refl
  ∧-comm true  false = refl
  ∧-comm false true  = refl
  ∧-comm false false = refl

  -- (a ∧ (b ⊕ c)) ⊕ t ⊕ (a ∧ b) ⊕ ... : the head of an additive step.
  head-⊕ : ∀ a b c s t →
           (a ∧ (b xor c)) xor (s xor t) ≡
           ((a ∧ b) xor s) xor ((a ∧ c) xor t)
  head-⊕ true  b c s t = shuffle b c s t
    where
    shuffle : ∀ b c s t → (b xor c) xor (s xor t) ≡ (b xor s) xor (c xor t)
    shuffle true  true  true  true  = refl
    shuffle true  true  true  false = refl
    shuffle true  true  false true  = refl
    shuffle true  true  false false = refl
    shuffle true  false true  true  = refl
    shuffle true  false true  false = refl
    shuffle true  false false true  = refl
    shuffle true  false false false = refl
    shuffle false true  true  true  = refl
    shuffle false true  true  false = refl
    shuffle false true  false true  = refl
    shuffle false true  false false = refl
    shuffle false false s     t     = refl
  head-⊕ false b c s t = refl

dot-comm : (z v : Assign n) → dot z v ≡ dot v z
dot-comm {ℕ.zero}  z v = refl
dot-comm {ℕ.suc n} z v =
  cong₂ _xor_ (∧-comm (z zero) (v zero)) (dot-comm (tail z) (tail v))

dot-⊕ʳ : (z v x : Assign n) → dot z (v ⊕ᵛ x) ≡ dot z v xor dot z x
dot-⊕ʳ {ℕ.zero}  z v x = refl
dot-⊕ʳ {ℕ.suc n} z v x =
  trans (cong ((z zero ∧ (v zero xor x zero)) xor_)
              (dot-⊕ʳ (tail z) (tail v) (tail x)))
        (head-⊕ (z zero) (v zero) (x zero)
                (dot (tail z) (tail v)) (dot (tail z) (tail x)))

dot-⊕ˡ : (z z′ v : Assign n) → dot (z ⊕ᵛ z′) v ≡ dot z v xor dot z′ v
dot-⊕ˡ z z′ v = trans (dot-comm (z ⊕ᵛ z′) v)
  (trans (dot-⊕ʳ v z z′)
         (cong₂ _xor_ (dot-comm v z) (dot-comm v z′)))

dot-0ˡ : (z v : Assign n) → (∀ j → z j ≡ false) → dot z v ≡ false
dot-0ˡ {ℕ.zero}  z v _  = refl
dot-0ˡ {ℕ.suc n} z v z0 rewrite z0 zero = dot-0ˡ (tail z) (tail v) (λ j → z0 (suc j))

dot-0ʳ : (z v : Assign n) → (∀ j → v j ≡ false) → dot z v ≡ false
dot-0ʳ z v v0 = trans (dot-comm z v) (dot-0ˡ v z v0)

-- At a unit vector the parity reads one bit.  (The unit vector at
-- suc w, read past its head, is definitionally the one at w.)

private
  ∧-true : ∀ a → (a ∧ true) xor false ≡ a
  ∧-true true  = refl
  ∧-true false = refl

  ∧-false : ∀ a → (a ∧ false) ≡ false
  ∧-false true  = refl
  ∧-false false = refl

dot-e : (z : Assign n) (w : Fin n) → dot z (eᵛ w) ≡ z w
dot-e {ℕ.suc n} z zero = trans
  (cong ((z zero ∧ true) xor_)
        (dot-0ʳ (tail z) (λ j → eᵛ {suc n} zero (suc j)) (λ _ → refl)))
  (∧-true (z zero))
dot-e {ℕ.suc n} z (suc w) =
  trans (cong₂ _xor_ (∧-false (z zero))
                     (dot-cong {z = tail z} {z′ = tail z} (λ _ → refl)
                               (eᵛ-suc w)))
        (dot-e (tail z) w)
  where
  eᵛ-suc : (w : Fin n) (j : Fin n) → eᵛ {suc n} (suc w) (suc j) ≡ eᵛ w j
  eᵛ-suc w j with j Fin.≟ w
  ... | yes _ = refl
  ... | no  _ = refl

e-dot : (w : Fin n) (v : Assign n) → dot (eᵛ w) v ≡ v w
e-dot w v = trans (dot-comm (eᵛ w) v) (dot-e v w)


------------------------------------------------------------------------
-- Paulis

-- i^ph X^xs Z^zs.

record PauliData (n : ℕ) : Set where
  constructor pd
  field
    ph : ℤ
    xs : Assign n
    zs : Assign n

open PauliData public

-- The phase of the entry from v: i^a (-1)^(z·v).

φᴾ : PauliData n → Assign n → ℤ
φᴾ p v = ¼ * ph p + ½ * [ dot (zs p) v ]ᶻ

φᴾ-cong : (p : PauliData n) {v v′ : Assign n} → (∀ j → v j ≡ v′ j) →
          φᴾ p v ≡ φᴾ p v′
φᴾ-cong p vv = cong (λ b → ¼ * ph p + ½ * [ b ]ᶻ) (dot-cong (λ _ → refl) vv)

entryᴾ : PauliData n → Mat n
entryᴾ p v u = if same (v ⊕ᵛ xs p) u then zpow (φᴾ p v) else 0ᴬ

pauli : PauliData n → Op n
pauli p = op 0 (entryᴾ p) (λ {v} {v′} {u} {u′} vv uu →
  if-cong {p = same (v ⊕ᵛ xs p) u} {q = same (v′ ⊕ᵛ xs p) u′}
    (same-≗ (λ j → cong (_xor xs p j) (vv j)) uu)
    (λ i → cong (λ e → zpow e i) (φᴾ-cong p vv)))

-- The generators.

X^ Z^ Y^ : Fin n → PauliData n
X^ w = pd 0ℤ (eᵛ w) 0ᵛ
Z^ w = pd 0ℤ 0ᵛ (eᵛ w)
Y^ w = pd 1ℤ (eᵛ w) (eᵛ w)

-- The identity, as a Pauli.

1ᴾ : PauliData n
1ᴾ = pd 0ℤ 0ᵛ 0ᵛ


------------------------------------------------------------------------
-- A Pauli next to any operator

-- Applied first, a Pauli shifts the input and multiplies by its phase.

·-pauli : (U : Op n) (p : PauliData n) (v u : Assign n) →
          mat (U · pauli p) v u ≐ rot (φᴾ p v) (mat U (v ⊕ᵛ xs p) u)
·-pauli U p v u =
  Σᴮ-cong (λ w → if-⊛ (same (v ⊕ᵛ xs p) w) (zpow (φᴾ p v)) (mat U w u))
  ∙ Σᴮ-δ (v ⊕ᵛ xs p) (λ w → zpow (φᴾ p v) ⊛ mat U w u)
         (λ g h g≗h → ⊛-cong {a = zpow (φᴾ p v)} ≐-refl (respˣ U u g h g≗h))
  ∙ zpow-⊛ (φᴾ p v) (mat U (v ⊕ᵛ xs p) u)

-- Applied last, a Pauli shifts the output and multiplies by its phase
-- at the shifted output.

pauli-·′ : (p : PauliData n) (U : Op n) (v u : Assign n) →
           mat (pauli p · U) v u ≐
           rot (φᴾ p (u ⊕ᵛ xs p)) (mat U v (u ⊕ᵛ xs p))
pauli-·′ p U v u =
  Σᴮ-cong (λ w →
    ⊛-cong {a = mat U v w} ≐-refl
      (if-cong {p = same (w ⊕ᵛ xs p) u} {q = same (u ⊕ᵛ xs p) w}
               (same-⊕-swap w (xs p) u) ≐-refl)
    ∙ ⊛-if (same (u ⊕ᵛ xs p) w) (mat U v w) (zpow (φᴾ p w)))
  ∙ Σᴮ-δ (u ⊕ᵛ xs p) (λ w → mat U v w ⊛ zpow (φᴾ p w))
         (λ g h g≗h → ⊛-cong (respᶻ U v g h g≗h)
                             (λ i → cong (λ e → zpow e i) (φᴾ-cong p g≗h)))
  ∙ ⊛-zpow (φᴾ p (u ⊕ᵛ xs p)) (mat U v (u ⊕ᵛ xs p))


------------------------------------------------------------------------
-- Arithmetic of phases

-- Two quarters are a half: i² = -1.

¼·2 : ∀ t → ¼ * ((+ 2) * t) ≡ ½ * t
¼·2 t = trans (solve 2 (λ q t → q :* (con (+ 2) :* t) := q :* t :+ q :* t)
                       refl ¼ t)
              (trans (sym (*-distrib ¼ ¼ t)) (cong (_* t) ¼+¼))
  where
  *-distrib : ∀ a b t → (a + b) * t ≡ a * t + b * t
  *-distrib = solve 3 (λ a b t → (a :+ b) :* t := a :* t :+ b :* t) refl

-- -½b is ½b modulo N.

neg-½ : ∀ b → - (½ * [ b ]ᶻ) ≡ᴺ ½ * [ b ]ᶻ
neg-½ b = begin
  - h            ≡⟨ sym (+-identityʳ (- h)) ⟩
  - h + 0ℤ       ≡ᴺ⟨ ≡ᴺ-+ (≡ᴺ-refl {a = - h}) (≡ᴺ-sym (½-self b)) ⟩
  - h + (h + h)  ≡⟨ solve 1 (λ h → :- h :+ (h :+ h) := h) refl h ⟩
  h              ∎
  where
  open ≡ᴺ-Reasoning
  h = ½ * [ b ]ᶻ

------------------------------------------------------------------------
-- Equality of Paulis

-- A Pauli reads its data pointwise, and its phase modulo 4.

pauli-≈ : (p q : PauliData n) → ¼ * ph p ≡ᴺ ¼ * ph q →
          (∀ j → xs p j ≡ xs q j) → (∀ j → zs p j ≡ zs q j) →
          pauli p ≈ pauli q
pauli-≈ p q ph≡ xx zz = ≈-by (pauli p) (pauli q) refl (λ v u →
  if-cong {p = same (v ⊕ᵛ xs p) u} {q = same (v ⊕ᵛ xs q) u}
    (same-≗ (λ j → cong (v j xor_) (xx j)) (λ _ → refl))
    (zpow-≡ᴺ (≡ᴺ-+ ph≡ (≡ᴺ-≡ (cong (λ b → ½ * [ b ]ᶻ)
                                 (dot-cong zz (λ _ → refl)))))))

-- P(0, 0, 0) is the identity.

pauli-I : pauli (1ᴾ {n}) ≈ I
pauli-I = ≈-by (pauli 1ᴾ) I refl (λ v u →
  if-cong {p = same (v ⊕ᵛ 0ᵛ) u} {q = same v u}
    (same-≗ (λ j → xor-false (v j)) (λ _ → refl))
    (zpow-≡ᴺ (≡ᴺ-≡ (trans (cong (λ b → ¼ * 0ℤ + ½ * [ b ]ᶻ)
                                 (dot-0ˡ 0ᵛ v (λ _ → refl)))
                          (cong₂ _+_ (*-zeroʳ ¼) (*-zeroʳ ½))))))

-- A phase i^t multiplies into the data.

◃-pauli : (t : ℤ) (p : PauliData n) →
          (¼ * t) ◃ pauli p ≈ pauli (pd (ph p + t) (xs p) (zs p))
◃-pauli t p = ≈-by ((¼ * t) ◃ pauli p) (pauli (pd (ph p + t) (xs p) (zs p)))
  refl (λ v u →
    rot-if (same (v ⊕ᵛ xs p) u) (¼ * t) (φᴾ p v)
    ∙ if-cong {p = same (v ⊕ᵛ xs p) u} refl
        (λ i → cong (λ e → zpow e i)
          (shape ¼ t (ph p) (½ * [ dot (zs p) v ]ᶻ))))
  where
  shape : ∀ q t a h → q * t + (q * a + h) ≡ q * (a + t) + h
  shape = solve 4 (λ q t a h → q :* t :+ (q :* a :+ h) := q :* (a :+ t) :+ h)
                  refl


------------------------------------------------------------------------
-- The group law

-- Moving Z^z past X^x′ costs (-1)^(z·x′).

infixl 7 _∙ᴾ_

_∙ᴾ_ : PauliData n → PauliData n → PauliData n
p ∙ᴾ q = pd (ph p + ph q + (+ 2) * [ dot (zs p) (xs q) ]ᶻ)
            (xs p ⊕ᵛ xs q) (zs p ⊕ᵛ zs q)

private
  ¼-split : ∀ a b g → ¼ * (a + b + (+ 2) * g) ≡ ¼ * a + ¼ * b + ½ * g
  ¼-split a b g = trans
    (solve 4 (λ q a b g → q :* (a :+ b :+ con (+ 2) :* g) :=
                          q :* a :+ q :* b :+ q :* (con (+ 2) :* g))
             refl ¼ a b g)
    (cong (λ t → ¼ * a + ¼ * b + t) (¼·2 g))

  rearrange : ∀ qa qb hb ha hg →
              (qb + hb) + (qa + (ha + hg)) ≡ (qa + qb + hg) + (ha + hb)
  rearrange = solve 5 (λ qa qb hb ha hg →
    (qb :+ hb) :+ (qa :+ (ha :+ hg)) := (qa :+ qb :+ hg) :+ (ha :+ hb)) refl

φ-∙ : (p q : PauliData n) (v : Assign n) →
      φᴾ q v + φᴾ p (v ⊕ᵛ xs q) ≡ᴺ φᴾ (p ∙ᴾ q) v
φ-∙ p q v = begin
  (¼ * ph q + ½ * [ β ]ᶻ) + (¼ * ph p + ½ * [ dot (zs p) (v ⊕ᵛ xs q) ]ᶻ)
    ≡⟨ cong (λ b → (¼ * ph q + ½ * [ β ]ᶻ) + (¼ * ph p + ½ * [ b ]ᶻ))
            (dot-⊕ʳ (zs p) v (xs q)) ⟩
  (¼ * ph q + ½ * [ β ]ᶻ) + (¼ * ph p + ½ * [ α xor γ ]ᶻ)
    ≡ᴺ⟨ ≡ᴺ-+ (≡ᴺ-refl {a = ¼ * ph q + ½ * [ β ]ᶻ})
             (≡ᴺ-+ (≡ᴺ-refl {a = ¼ * ph p}) (≡ᴺ-sym (½-xor α γ))) ⟩
  (¼ * ph q + ½ * [ β ]ᶻ) + (¼ * ph p + (½ * [ α ]ᶻ + ½ * [ γ ]ᶻ))
    ≡⟨ rearrange (¼ * ph p) (¼ * ph q) (½ * [ β ]ᶻ) (½ * [ α ]ᶻ)
                 (½ * [ γ ]ᶻ) ⟩
  (¼ * ph p + ¼ * ph q + ½ * [ γ ]ᶻ) + (½ * [ α ]ᶻ + ½ * [ β ]ᶻ)
    ≡ᴺ⟨ ≡ᴺ-+ (≡ᴺ-refl {a = ¼ * ph p + ¼ * ph q + ½ * [ γ ]ᶻ}) (½-xor α β) ⟩
  (¼ * ph p + ¼ * ph q + ½ * [ γ ]ᶻ) + ½ * [ α xor β ]ᶻ
    ≡⟨ cong₂ _+_ (sym (¼-split (ph p) (ph q) [ γ ]ᶻ))
                 (cong (λ b → ½ * [ b ]ᶻ) (sym (dot-⊕ˡ (zs p) (zs q) v))) ⟩
  φᴾ (p ∙ᴾ q) v ∎
  where
  open ≡ᴺ-Reasoning
  α = dot (zs p) v
  β = dot (zs q) v
  γ = dot (zs p) (xs q)

pauli-· : (p q : PauliData n) → pauli p · pauli q ≈ pauli (p ∙ᴾ q)
pauli-· p q = ≈-by (pauli p · pauli q) (pauli (p ∙ᴾ q)) refl (λ v u →
  ·-pauli (pauli p) q v u
  ∙ rot-if (same ((v ⊕ᵛ xs q) ⊕ᵛ xs p) u) (φᴾ q v) (φᴾ p (v ⊕ᵛ xs q))
  ∙ if-cong {p = same ((v ⊕ᵛ xs q) ⊕ᵛ xs p) u}
            {q = same (v ⊕ᵛ (xs p ⊕ᵛ xs q)) u}
      (same-≗ (λ j → trans (xor-assoc (v j) (xs q j) (xs p j))
                           (cong (v j xor_) (xor-comm (xs q j) (xs p j))))
              (λ _ → refl))
      (zpow-≡ᴺ (φ-∙ p q v)))


------------------------------------------------------------------------
-- Adjoints and unitarity

-- P(a, x, z)† = P(-a + 2(z·x), x, z).

infix 8 _⁻¹ᴾ

_⁻¹ᴾ : PauliData n → PauliData n
p ⁻¹ᴾ = pd (- ph p + (+ 2) * [ dot (zs p) (xs p) ]ᶻ) (xs p) (zs p)

private
  conj-if : (c : Bool) (e : ℤ) →
            conj (if c then zpow e else 0ᴬ) ≐ (if c then zpow (- e) else 0ᴬ)
  conj-if true  e = conj-zpow e
  conj-if false e = conj-0ᴬ

  -- An entry guarded by c may use c.

  guarded : (c : Bool) {a b : Amp} → (c ≡ true → a ≐ b) →
            (if c then a else 0ᴬ) ≐ (if c then b else 0ᴬ)
  guarded true  h = h refl
  guarded false h = λ _ → refl

  neg-φ : (p : PauliData n) (v : Assign n) →
          - φᴾ p (v ⊕ᵛ xs p) ≡ᴺ φᴾ (p ⁻¹ᴾ) v
  neg-φ p v = begin
    - (¼ * ph p + ½ * [ dot (zs p) (v ⊕ᵛ xs p) ]ᶻ)
      ≡⟨ cong (λ b → - (¼ * ph p + ½ * [ b ]ᶻ)) (dot-⊕ʳ (zs p) v (xs p)) ⟩
    - (¼ * ph p + ½ * [ α xor γ ]ᶻ)
      ≡⟨ solve 2 (λ q h → :- (q :+ h) := :- q :+ :- h) refl
               (¼ * ph p) (½ * [ α xor γ ]ᶻ) ⟩
    - (¼ * ph p) + - (½ * [ α xor γ ]ᶻ)
      ≡ᴺ⟨ ≡ᴺ-+ (≡ᴺ-refl {a = - (¼ * ph p)}) (neg-½ (α xor γ)) ⟩
    - (¼ * ph p) + ½ * [ α xor γ ]ᶻ
      ≡ᴺ⟨ ≡ᴺ-+ (≡ᴺ-refl {a = - (¼ * ph p)}) (≡ᴺ-sym (½-xor α γ)) ⟩
    - (¼ * ph p) + (½ * [ α ]ᶻ + ½ * [ γ ]ᶻ)
      ≡⟨ shape (¼ * ph p) (½ * [ α ]ᶻ) (½ * [ γ ]ᶻ) ⟩
    (- (¼ * ph p) + ½ * [ γ ]ᶻ) + ½ * [ α ]ᶻ
      ≡⟨ cong (λ t → t + ½ * [ α ]ᶻ) (sym (¼-neg (ph p) [ γ ]ᶻ)) ⟩
    φᴾ (p ⁻¹ᴾ) v ∎
    where
    open ≡ᴺ-Reasoning
    α = dot (zs p) v
    γ = dot (zs p) (xs p)
    shape : ∀ q h g → - q + (h + g) ≡ (- q + g) + h
    shape = solve 3 (λ q h g → :- q :+ (h :+ g) := (:- q :+ g) :+ h) refl
    ¼-neg : ∀ a g → ¼ * (- a + (+ 2) * g) ≡ - (¼ * a) + ½ * g
    ¼-neg a g = trans
      (solve 3 (λ q a g → q :* (:- a :+ con (+ 2) :* g) :=
                          :- (q :* a) :+ q :* (con (+ 2) :* g)) refl ¼ a g)
      (cong (λ t → - (¼ * a) + t) (¼·2 g))

pauli-† : (p : PauliData n) → pauli p † ≈ pauli (p ⁻¹ᴾ)
pauli-† p = ≈-by (pauli p †) (pauli (p ⁻¹ᴾ)) refl (λ v u →
  conj-if (same (u ⊕ᵛ xs p) v) (φᴾ p u)
  ∙ if-cong {p = same (u ⊕ᵛ xs p) v} {q = same (v ⊕ᵛ xs p) u}
            (same-⊕-swap u (xs p) v) ≐-refl
  ∙ guarded (same (v ⊕ᵛ xs p) u) (λ h →
      zpow-≡ᴺ (≡ᴺ-trans
        (≡ᴺ-≡ (cong -_ (φᴾ-cong p (λ j →
           sym (same-true (v ⊕ᵛ xs p) u h j)))))
        (neg-φ p v))))

-- P†P and PP† have data P(4(z·x), 0, 0) up to pointwise equality, and
-- i^(4(z·x)) = 1.

private
  ¼·4 : ∀ g → ¼ * ((+ 4) * g) ≡ᴺ ¼ * 0ℤ
  ¼·4 g = ≡ᴺ-trans
    (≡ᴺ-≡ (trans (solve 2 (λ q g → q :* (con (+ 4) :* g) :=
                                   g :* ((q :+ q) :* con (+ 2))) refl ¼ g)
                 (cong (λ h → g * (h * (+ 2))) ¼+¼)))
    (≡ᴺ-trans (≡ᴺ-≡ (cong (g *_) ½·2))
      (≡ᴺ-trans (≡ᴺ-N g) (≡ᴺ-≡ (sym (*-zeroʳ ¼)))))

  inv-l : ∀ a g → - a + (+ 2) * g + a + (+ 2) * g ≡ (+ 4) * g
  inv-l = solve 2 (λ a g → :- a :+ con (+ 2) :* g :+ a :+ con (+ 2) :* g :=
                           con (+ 4) :* g) refl

  inv-r : ∀ a g → a + (- a + (+ 2) * g) + (+ 2) * g ≡ (+ 4) * g
  inv-r = solve 2 (λ a g → a :+ (:- a :+ con (+ 2) :* g) :+ con (+ 2) :* g :=
                           con (+ 4) :* g) refl

pauli-unitary : (p : PauliData n) → Unitary (pauli p)
pauli-unitary p =
  (·-congˡ (pauli p) (pauli-† p)
   ⟨≈⟩ pauli-· (p ⁻¹ᴾ) p
   ⟨≈⟩ pauli-≈ (p ⁻¹ᴾ ∙ᴾ p) 1ᴾ
         (≡ᴺ-trans (≡ᴺ-≡ (cong (¼ *_) (inv-l (ph p) γ))) (¼·4 γ))
         (λ j → xor-self (xs p j)) (λ j → xor-self (zs p j))
   ⟨≈⟩ pauli-I) ,
  (·-congʳ (pauli p) (pauli-† p)
   ⟨≈⟩ pauli-· p (p ⁻¹ᴾ)
   ⟨≈⟩ pauli-≈ (p ∙ᴾ p ⁻¹ᴾ) 1ᴾ
         (≡ᴺ-trans (≡ᴺ-≡ (cong (¼ *_) (inv-r (ph p) γ))) (¼·4 γ))
         (λ j → xor-self (xs p j)) (λ j → xor-self (zs p j))
   ⟨≈⟩ pauli-I)
  where
  γ = [ dot (zs p) (xs p) ]ᶻ


------------------------------------------------------------------------
-- Commutation

-- The symplectic form: two Paulis commute or anticommute according as
-- it is 0 or 1.

ω : PauliData n → PauliData n → Bool
ω p q = dot (zs p) (xs q) xor dot (zs q) (xs p)

private
  comm-phase : ∀ a b g₁ g₂ →
    ¼ * (a + b + (+ 2) * [ g₁ ]ᶻ) ≡ᴺ
    ¼ * (b + a + (+ 2) * [ g₂ ]ᶻ + (+ 2) * [ g₁ xor g₂ ]ᶻ)
  comm-phase a b g₁ g₂ = begin
    ¼ * (a + b + (+ 2) * [ g₁ ]ᶻ)
      ≡⟨ ¼-split a b [ g₁ ]ᶻ ⟩
    ¼ * a + ¼ * b + ½ * [ g₁ ]ᶻ
      ≡⟨ solve 3 (λ x y h → x :+ y :+ h := y :+ x :+ (h :+ con 0ℤ)) refl
               (¼ * a) (¼ * b) (½ * [ g₁ ]ᶻ) ⟩
    ¼ * b + ¼ * a + (½ * [ g₁ ]ᶻ + 0ℤ)
      ≡ᴺ⟨ ≡ᴺ-+ (≡ᴺ-refl {a = ¼ * b + ¼ * a})
               (≡ᴺ-+ (≡ᴺ-refl {a = ½ * [ g₁ ]ᶻ}) (≡ᴺ-sym (½-self g₂))) ⟩
    ¼ * b + ¼ * a + (½ * [ g₁ ]ᶻ + (½ * [ g₂ ]ᶻ + ½ * [ g₂ ]ᶻ))
      ≡⟨ solve 4 (λ x y h₁ h₂ → x :+ y :+ (h₁ :+ (h₂ :+ h₂)) :=
                                x :+ y :+ h₂ :+ (h₂ :+ h₁)) refl
               (¼ * b) (¼ * a) (½ * [ g₁ ]ᶻ) (½ * [ g₂ ]ᶻ) ⟩
    ¼ * b + ¼ * a + ½ * [ g₂ ]ᶻ + (½ * [ g₂ ]ᶻ + ½ * [ g₁ ]ᶻ)
      ≡ᴺ⟨ ≡ᴺ-+ (≡ᴺ-refl {a = ¼ * b + ¼ * a + ½ * [ g₂ ]ᶻ}) (½-xor g₂ g₁) ⟩
    ¼ * b + ¼ * a + ½ * [ g₂ ]ᶻ + ½ * [ g₂ xor g₁ ]ᶻ
      ≡⟨ cong (λ t → ¼ * b + ¼ * a + ½ * [ g₂ ]ᶻ + ½ * [ t ]ᶻ)
              (xor-comm g₂ g₁) ⟩
    ¼ * b + ¼ * a + ½ * [ g₂ ]ᶻ + ½ * [ g₁ xor g₂ ]ᶻ
      ≡⟨ sym (trans (solve 5 (λ q b a g h →
                                q :* (b :+ a :+ con (+ 2) :* g :+
                                      con (+ 2) :* h) :=
                                q :* b :+ q :* a :+ q :* (con (+ 2) :* g)
                                :+ q :* (con (+ 2) :* h)) refl
                             ¼ b a [ g₂ ]ᶻ [ g₁ xor g₂ ]ᶻ)
                    (cong₂ (λ s t → ¼ * b + ¼ * a + s + t)
                           (¼·2 [ g₂ ]ᶻ) (¼·2 [ g₁ xor g₂ ]ᶻ))) ⟩
    ¼ * (b + a + (+ 2) * [ g₂ ]ᶻ + (+ 2) * [ g₁ xor g₂ ]ᶻ) ∎
    where open ≡ᴺ-Reasoning

pauli-comm : (p q : PauliData n) →
             pauli p · pauli q ≈ (½ * [ ω p q ]ᶻ) ◃ (pauli q · pauli p)
pauli-comm p q =
  pauli-· p q
  ⟨≈⟩ pauli-≈ (p ∙ᴾ q) (pd (ph (q ∙ᴾ p) + (+ 2) * [ ω p q ]ᶻ)
                           (xs (q ∙ᴾ p)) (zs (q ∙ᴾ p)))
        (comm-phase (ph p) (ph q) (dot (zs p) (xs q)) (dot (zs q) (xs p)))
        (λ j → xor-comm (xs p j) (xs q j))
        (λ j → xor-comm (zs p j) (zs q j))
  ⟨≈⟩ ≈-sym (◃-pauli ((+ 2) * [ ω p q ]ᶻ) (q ∙ᴾ p))
  ⟨≈⟩ ◃-exp (pauli (q ∙ᴾ p)) (¼·2 [ ω p q ]ᶻ)
  ⟨≈⟩ ◃-cong (½ * [ ω p q ]ᶻ) (≈-sym (pauli-· q p))

-- Conjugating a Pauli by a Pauli gives it back, up to the sign.

pauli-conj : (p q : PauliData n) →
             pauli p · pauli q · pauli p † ≈ (½ * [ ω p q ]ᶻ) ◃ pauli q
pauli-conj p q =
  ·-congˡ (pauli p †) (pauli-comm p q)
  ⟨≈⟩ ◃-·ˡ (½ * [ ω p q ]ᶻ) (pauli q · pauli p) (pauli p †)
  ⟨≈⟩ ◃-cong (½ * [ ω p q ]ᶻ) (cancelʳ (pauli p) (pauli q) (pauli-unitary p))

------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrices of the gates: multiples of isometries, and symmetric
--
-- Both gate sets of the development -- {H , S , CZ} (PathSum.Circuit)
-- and the paper's {H , CNOT , R_k , R_k†} (PathSum.CRK.Circuit) -- act
-- on columns by three kinds of unnormalised matrix, spelled out here
-- once:
--
--   * hadᴬ w, a Hadamard on w: the entry at z becomes the old entry at
--     z[w≔0] plus the one at z[w≔1], the second signed by (-1)^(z_w);
--   * phaseᴬ e, a diagonal phase: the entry at z is multiplied by
--     ζ^(e z) (S, CZ, R_k and R_k†);
--   * cnotᴬ c t, a controlled NOT: the entry at z becomes the old one
--     at z[t ≔ z_t ⊕ z_c], a permutation of the entries.
--
-- The gate matrices of both semantics (PathSum.CircuitSemantics,
-- PathSum.CRK.Semantics) are definitionally these.  Two facts about
-- each are proved.  Those about a Hadamard or a CNOT ask the columns
-- to see assignments only through their values (Respects): both gates
-- read a column at an updated assignment, which is only pointwise
-- equal to one that a sum visits.
--
-- Each is a multiple of an isometry: it multiplies the Hermitian
-- product inner ψ φ = Σ_z ψ z · conj (φ z) of any two columns by a
-- constant -- 2 for a Hadamard (the polarised parallelogram law, pair
-- by pair), 1 for a phase (a common phase cancels, PathSum.Hermitian's
-- inner-phase) and 1 for a CNOT, whose permutation of the entries only
-- permutes the terms of the sum: it pairs z[t≔0] with z[t≔1] and swaps
-- the two when z_c = 1 (Σᵃ-cnot, the conditional-swap invariance of
-- sums over assignments).
--
-- Each is symmetric, equal to its own transpose, which is said with
-- the bilinear pairing dot ψ φ = Σ_z ψ z · φ z (no conjugate): a
-- matrix A is symmetric when dot (A ψ) φ = dot ψ (A φ) for all columns
-- (here, all that respect pointwise equality, as the basis columns
-- do).  For a phase that is ζ^e moving from one factor to the other;
-- for a Hadamard it is (a + b) c + (a - b) d = a (c + d) + b (c - d)
-- at each pair; and a CNOT is a permutation that is its own inverse,
-- so moving it to the other side of the pairing permutes the terms of
-- the sum.
-- Reading dot against a basis column recovers an entry (dot-basis),
-- which is how circuit-level transposition is read off in
-- PathSum.Unitarity and PathSum.CRK.Unitarity.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Unitarity.Gates (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; if_then_else_; _xor_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Properties using
  (+-comm; +-identityˡ; +-identityʳ; *-identityʳ; *-zeroʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-≔; ≔-self; ≔-cong; same; same-refl)
open import PathSum.AssignSum using (Σᶻ; RespectsZ; Σᶻ-cong; Σᶻ-at)
open import PathSum.CircuitSemantics M₀ using
  (Column; δ; sum-cong; sign-0; sign-1)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _-ᴬ_; _·ᴬ_; _≐_; rot; Respects)
  renaming (H to rank)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Hermitian M₀ using
  (Σᵃ; Σᵃ-cong; Σᵃ-·ᴬ; Σᵃ-0; Σᵃ-point; Σᵃ-at; [_]ᴬ; []ᴬ-resp; inner)
open import PathSum.Reduction M using (½)
open import PathSum.Ring M₀ using
  (_⊛_; conj; ⊛-cong; conj-cong; ⊛-zeroʳ; ⊛-rotˡ; ⊛-rotʳ;
   ⊛-distribˡ-+ᴬ; ⊛-distribʳ-+ᴬ; ⊛-distribˡ-diff; ⊛-distribʳ-diff;
   ⊛-conj-parallelogram)
open import PathSum.Ring.Laws M₀ using (⊛-comm; ⊛-identityʳ)

open +-*-Solver using (solve; _:+_; _:-_; _:=_)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The three kinds of gate

-- A Hadamard on w, unnormalised.

hadᴬ : Fin n → Column n → Column n
hadᴬ w ψ z = ψ (z [ w ≔ false ]) +ᴬ rot (½ * [ z w ]ᶻ) (ψ (z [ w ≔ true ]))

-- A diagonal phase ζ^(e z).

phaseᴬ : (Assign n → ℤ) → Column n → Column n
phaseᴬ e ψ z = rot (e z) (ψ z)

-- A controlled NOT with control c and target t.

cnotᴬ : Fin n → Fin n → Column n → Column n
cnotᴬ c t ψ z = ψ (z [ t ≔ z t xor z c ])

-- The bilinear pairing of two columns: no conjugate.

dot : Column n → Column n → Amp
dot ψ φ = Σᵃ (λ z → ψ z ⊛ φ z)


------------------------------------------------------------------------
-- Respect for pointwise equality

had-resp : (w : Fin n) {ψ : Column n} → Respects ψ → Respects (hadᴬ w ψ)
had-resp w {ψ} resp z z′ zz =
  sum-cong (ψ (z [ w ≔ false ])) (ψ (z′ [ w ≔ false ]))
           (ψ (z [ w ≔ true ])) (ψ (z′ [ w ≔ true ]))
           (½ * [ z w ]ᶻ) (½ * [ z′ w ]ᶻ)
           (resp (z [ w ≔ false ]) (z′ [ w ≔ false ]) (≔-cong w false zz))
           (cong (λ b → ½ * [ b ]ᶻ) (zz w))
           (resp (z [ w ≔ true ]) (z′ [ w ≔ true ]) (≔-cong w true zz))

cnot-resp : (c t : Fin n) {ψ : Column n} → Respects ψ →
            Respects (cnotᴬ c t ψ)
cnot-resp c t {ψ} resp z z′ zz =
  resp (z [ t ≔ z t xor z c ]) (z′ [ t ≔ z′ t xor z′ c ]) (λ j →
    trans (≔-cong t (z t xor z c) zz j)
          (cong (λ b → (z′ [ t ≔ b ]) j) (cong₂ _xor_ (zz t) (zz c))))


------------------------------------------------------------------------
-- Amplitude identities

private
  ⊛-congˡ : ∀ {a a′} b → a ≐ a′ → a ⊛ b ≐ a′ ⊛ b
  ⊛-congˡ {a} {a′} b p = ⊛-cong {a = a} {a′ = a′} {b = b} {b′ = b}
                                p (λ _ → refl)

  ⊛-congʳ : ∀ a {b b′} → b ≐ b′ → a ⊛ b ≐ a ⊛ b′
  ⊛-congʳ a {b} {b′} p = ⊛-cong {a = a} {a′ = a} {b = b} {b′ = b′}
                                (λ _ → refl) p

  -- A Hadamard's matrix is symmetric, at one pair.

  had-sym : ∀ a b c d →
            (a +ᴬ b) ⊛ c +ᴬ (a -ᴬ b) ⊛ d ≐ a ⊛ (c +ᴬ d) +ᴬ b ⊛ (c -ᴬ d)
  had-sym a b c d i =
    trans (cong₂ _+_ (⊛-distribʳ-+ᴬ a b c i) (⊛-distribʳ-diff a b d i))
      (trans (shuffle ((a ⊛ c) i) ((b ⊛ c) i) ((a ⊛ d) i) ((b ⊛ d) i))
             (sym (cong₂ _+_ (⊛-distribˡ-+ᴬ a c d i)
                             (⊛-distribˡ-diff b c d i))))
    where
    shuffle : ∀ p q r s → (p + q) + (r - s) ≡ (p + r) + (q - s)
    shuffle = solve 4 (λ p q r s →
      (p :+ q) :+ (r :- s) := (p :+ r) :+ (q :- s)) refl

  -- Masked terms.

  masked : ∀ b {A B : Amp} → A ≐ B →
           (if b then 0ᴬ else A) ≐ (if b then 0ᴬ else B)
  masked true  _ _ = refl
  masked false p   = p

  masked₂ : ∀ b {A B : Amp} → A ≐ (+ 2) ·ᴬ B →
            (if b then 0ᴬ else A) ≐ (+ 2) ·ᴬ (if b then 0ᴬ else B)
  masked₂ true  _ _ = sym (*-zeroʳ (+ 2))
  masked₂ false p   = p

  -- The exponent of a Hadamard's sign at the two members of a pair.

  e₀ : (w : Fin n) (z : Assign n) → ½ * [ (z [ w ≔ false ]) w ]ᶻ ≡ 0ℤ
  e₀ w z =
    trans (cong (λ b → ½ * [ b ]ᶻ) (≔-here z w false)) (*-zeroʳ ½)

  e₁ : (w : Fin n) (z : Assign n) →
       ½ * [ (z [ w ≔ true ]) w ]ᶻ ≡ 0ℤ + (+ rank)
  e₁ w z = trans (cong (λ b → ½ * [ b ]ᶻ) (≔-here z w true))
                 (trans (*-identityʳ ½) (sym (+-identityˡ ½)))


------------------------------------------------------------------------
-- A Hadamard, pair by pair

-- The new entries of a column at the pair z[w≔0] , z[w≔1]: the sum and
-- the difference of the old ones.

had-0 : (w : Fin n) (χ : Column n) → Respects χ → ∀ z →
        hadᴬ w χ (z [ w ≔ false ]) ≐
        χ (z [ w ≔ false ]) +ᴬ χ (z [ w ≔ true ])
had-0 w χ rχ z =
  sign-0 (χ (z [ w ≔ false ] [ w ≔ false ])) (χ (z [ w ≔ false ]))
         (χ (z [ w ≔ false ] [ w ≔ true ])) (χ (z [ w ≔ true ]))
         (½ * [ (z [ w ≔ false ]) w ]ᶻ)
         (rχ _ _ (≔-≔ z w false false)) (e₀ w z)
         (rχ _ _ (≔-≔ z w false true))

had-1 : (w : Fin n) (χ : Column n) → Respects χ → ∀ z →
        hadᴬ w χ (z [ w ≔ true ]) ≐
        χ (z [ w ≔ false ]) -ᴬ χ (z [ w ≔ true ])
had-1 w χ rχ z =
  sign-1 (χ (z [ w ≔ true ] [ w ≔ false ])) (χ (z [ w ≔ false ]))
         (χ (z [ w ≔ true ] [ w ≔ true ])) (χ (z [ w ≔ true ]))
         (½ * [ (z [ w ≔ true ]) w ]ᶻ)
         (rχ _ _ (≔-≔ z w true false)) (e₁ w z)
         (rχ _ _ (≔-≔ z w true true))

-- A Hadamard doubles the Hermitian product: the new entries at a pair
-- are a + b , a - b and c + d , c - d, and the polarised parallelogram
-- law makes their products twice a · c̄ + b · d̄.

inner-had : (w : Fin n) {ψ φ : Column n} → Respects ψ → Respects φ →
            inner (hadᴬ w ψ) (hadᴬ w φ) ≐ (+ 2) ·ᴬ inner ψ φ
inner-had {n} w {ψ} {φ} rψ rφ i =
  trans (Σᵃ-at w F respF i)
    (trans (Σᵃ-cong (λ z → masked₂ (z w) (pair z)) i)
      (trans (Σᵃ-·ᴬ (+ 2) P i)
             (cong (λ t → (+ 2) * t) (sym (Σᵃ-at w G respG i)))))
  where
  F G : Assign n → Amp
  F z = hadᴬ w ψ z ⊛ conj (hadᴬ w φ z)
  G z = ψ z ⊛ conj (φ z)

  P : Assign n → Amp
  P z = if z w then 0ᴬ else (G (z [ w ≔ false ]) +ᴬ G (z [ w ≔ true ]))

  respF : Respects F
  respF g h gh = ⊛-cong (had-resp w rψ g h gh)
                        (conj-cong (had-resp w rφ g h gh))

  respG : Respects G
  respG g h gh = ⊛-cong (rψ g h gh) (conj-cong (rφ g h gh))

  pair : ∀ z → F (z [ w ≔ false ]) +ᴬ F (z [ w ≔ true ]) ≐
               (+ 2) ·ᴬ (G (z [ w ≔ false ]) +ᴬ G (z [ w ≔ true ]))
  pair z j = trans
    (cong₂ _+_ (⊛-cong (had-0 w ψ rψ z) (conj-cong (had-0 w φ rφ z)) j)
               (⊛-cong (had-1 w ψ rψ z) (conj-cong (had-1 w φ rφ z)) j))
    (⊛-conj-parallelogram (ψ (z [ w ≔ false ])) (ψ (z [ w ≔ true ]))
                          (φ (z [ w ≔ false ])) (φ (z [ w ≔ true ])) j)

-- A Hadamard is symmetric.

dot-had : (w : Fin n) {ψ φ : Column n} → Respects ψ → Respects φ →
          dot (hadᴬ w ψ) φ ≐ dot ψ (hadᴬ w φ)
dot-had {n} w {ψ} {φ} rψ rφ i =
  trans (Σᵃ-at w F respF i)
    (trans (Σᵃ-cong (λ z → masked (z w) (pair z)) i)
           (sym (Σᵃ-at w G respG i)))
  where
  F G : Assign n → Amp
  F z = hadᴬ w ψ z ⊛ φ z
  G z = ψ z ⊛ hadᴬ w φ z

  respF : Respects F
  respF g h gh = ⊛-cong (had-resp w rψ g h gh) (rφ g h gh)

  respG : Respects G
  respG g h gh = ⊛-cong (rψ g h gh) (had-resp w rφ g h gh)

  pair : ∀ z → F (z [ w ≔ false ]) +ᴬ F (z [ w ≔ true ]) ≐
               G (z [ w ≔ false ]) +ᴬ G (z [ w ≔ true ])
  pair z j = trans
    (cong₂ _+_ (⊛-congˡ (φ (z [ w ≔ false ])) (had-0 w ψ rψ z) j)
               (⊛-congˡ (φ (z [ w ≔ true ])) (had-1 w ψ rψ z) j))
    (trans (had-sym (ψ (z [ w ≔ false ])) (ψ (z [ w ≔ true ]))
                    (φ (z [ w ≔ false ])) (φ (z [ w ≔ true ])) j)
           (sym (cong₂ _+_
             (⊛-congʳ (ψ (z [ w ≔ false ])) (had-0 w φ rφ z) j)
             (⊛-congʳ (ψ (z [ w ≔ true ])) (had-1 w φ rφ z) j))))


------------------------------------------------------------------------
-- A diagonal phase

-- The Hermitian product is PathSum.Hermitian's inner-phase.  For the
-- pairing, ζ^e moves from one factor to the other.

dot-phase : (e : Assign n → ℤ) (ψ φ : Column n) →
            dot (phaseᴬ e ψ) φ ≐ dot ψ (phaseᴬ e φ)
dot-phase e ψ φ = Σᵃ-cong (λ z i →
  trans (⊛-rotˡ (e z) (ψ z) (φ z) i) (sym (⊛-rotʳ (e z) (ψ z) (φ z) i)))


------------------------------------------------------------------------
-- A controlled NOT

-- Writing b to the target and then the CNOT's value reads the target
-- b ⊕ z_c: the control is not the target, so it is not overwritten.

private
  xor-cancel : ∀ a b → (a xor b) xor b ≡ a
  xor-cancel true  true  = refl
  xor-cancel true  false = refl
  xor-cancel false true  = refl
  xor-cancel false false = refl

  cnot-at : (c t : Fin n) → c ≢ t → ∀ (z : Assign n) b j →
            ((z [ t ≔ b ]) [ t ≔ (z [ t ≔ b ]) t xor (z [ t ≔ b ]) c ]) j ≡
            (z [ t ≔ b xor z c ]) j
  cnot-at c t p z b j =
    trans (≔-≔ z t b ((z [ t ≔ b ]) t xor (z [ t ≔ b ]) c) j)
          (cong (λ u → (z [ t ≔ u ]) j)
                (cong₂ _xor_ (≔-here z t b) (≔-there z b p)))

-- The CNOT's permutation is its own inverse.

cnot-involutive : (c t : Fin n) → c ≢ t → ∀ (z : Assign n) j →
                  let z′ = z [ t ≔ z t xor z c ] in
                  (z′ [ t ≔ z′ t xor z′ c ]) j ≡ z j
cnot-involutive c t p z j =
  trans (cnot-at c t p z (z t xor z c) j)
    (trans (cong (λ u → (z [ t ≔ u ]) j) (xor-cancel (z t) (z c)))
           (≔-self z t j))

-- A sum over assignments is invariant under the CNOT's permutation: it
-- pairs z[t≔0] with z[t≔1] and swaps the two when z_c = 1.

Σᶻ-cnot : (c t : Fin n) → c ≢ t → (g : Assign n → ℤ) → RespectsZ g →
          Σᶻ (λ z → g (z [ t ≔ z t xor z c ])) ≡ Σᶻ g
Σᶻ-cnot {n} c t p g resp =
  trans (Σᶻ-at t F respF)
    (trans (Σᶻ-cong (λ z → cong (λ s → if z t then 0ℤ else s) (pair z)))
           (sym (Σᶻ-at t g resp)))
  where
  F : Assign n → ℤ
  F z = g (z [ t ≔ z t xor z c ])

  respF : RespectsZ F
  respF z z′ zz = resp _ _ (λ j →
    trans (≔-cong t (z t xor z c) zz j)
          (cong (λ b → (z′ [ t ≔ b ]) j) (cong₂ _xor_ (zz t) (zz c))))

  at : ∀ z b → F (z [ t ≔ b ]) ≡ g (z [ t ≔ b xor z c ])
  at z b = resp _ _ (cnot-at c t p z b)

  swap : ∀ z (b : Bool) →
         g (z [ t ≔ b ]) + g (z [ t ≔ not b ]) ≡
         g (z [ t ≔ false ]) + g (z [ t ≔ true ])
  swap z false = refl
  swap z true  = +-comm (g (z [ t ≔ true ])) (g (z [ t ≔ false ]))

  pair : ∀ z → F (z [ t ≔ false ]) + F (z [ t ≔ true ]) ≡
               g (z [ t ≔ false ]) + g (z [ t ≔ true ])
  pair z = trans (cong₂ _+_ (at z false) (at z true)) (swap z (z c))

Σᵃ-cnot : (c t : Fin n) → c ≢ t → (G : Column n) → Respects G →
          Σᵃ (λ z → G (z [ t ≔ z t xor z c ])) ≐ Σᵃ G
Σᵃ-cnot c t p G resp i =
  Σᶻ-cnot c t p (λ z → G z i) (λ g h gh → resp g h gh i)

-- So a CNOT preserves the Hermitian product ...

inner-cnot : (c t : Fin n) → c ≢ t → {ψ φ : Column n} → Respects ψ →
             Respects φ → inner (cnotᴬ c t ψ) (cnotᴬ c t φ) ≐ inner ψ φ
inner-cnot c t p {ψ} {φ} rψ rφ =
  Σᵃ-cnot c t p (λ z → ψ z ⊛ conj (φ z))
          (λ g h gh → ⊛-cong (rψ g h gh) (conj-cong (rφ g h gh)))

-- ... and is symmetric: permuting the terms of dot ψ (cnotᴬ c t φ) by
-- the CNOT moves it to the other factor, the second application
-- undoing the first.

dot-cnot : (c t : Fin n) → c ≢ t → {ψ φ : Column n} → Respects ψ →
           Respects φ → dot (cnotᴬ c t ψ) φ ≐ dot ψ (cnotᴬ c t φ)
dot-cnot {n} c t p {ψ} {φ} rψ rφ i =
  trans (Σᵃ-cong {f = λ z → cnotᴬ c t ψ z ⊛ φ z}
                 {g = λ z → G (z [ t ≔ z t xor z c ])} back i)
        (Σᵃ-cnot c t p G respG i)
  where
  G : Assign n → Amp
  G z = ψ z ⊛ cnotᴬ c t φ z

  respG : Respects G
  respG g h gh = ⊛-cong (rψ g h gh) (cnot-resp c t rφ g h gh)

  back : ∀ z → cnotᴬ c t ψ z ⊛ φ z ≐ G (z [ t ≔ z t xor z c ])
  back z = ⊛-congʳ (ψ (z [ t ≔ z t xor z c ]))
    (rφ z _ (λ j → sym (cnot-involutive c t p z j)))


------------------------------------------------------------------------
-- The pairing

dot-cong : {ψ ψ′ φ φ′ : Column n} → (∀ z → ψ z ≐ ψ′ z) →
           (∀ z → φ z ≐ φ′ z) → dot ψ φ ≐ dot ψ′ φ′
dot-cong ψψ′ φφ′ = Σᵃ-cong (λ z → ⊛-cong (ψψ′ z) (φφ′ z))

dot-comm : (ψ φ : Column n) → dot ψ φ ≐ dot φ ψ
dot-comm ψ φ = Σᵃ-cong (λ z → ⊛-comm (ψ z) (φ z))

-- Paired with a basis column, a column gives its entry there: the term
-- at x is ψ x · 1, and every other term vanishes.

dot-basis : {ψ : Column n} → Respects ψ → ∀ x → dot ψ (δ x) ≐ ψ x
dot-basis {n} {ψ} rψ x i =
  trans (Σᵃ-point f resp x i)
    (trans (cong₂ _+_ (at-x i) (rest i)) (+-identityʳ (ψ x i)))
  where
  f : Assign n → Amp
  f z = ψ z ⊛ δ x z

  resp : Respects f
  resp g h gh = ⊛-cong (rψ g h gh) ([]ᴬ-resp x g h gh)

  at-x : f x ≐ ψ x
  at-x j = trans
    (⊛-congʳ (ψ x) (λ l → cong (λ b → [ b ]ᴬ l) (same-refl x)) j)
    (⊛-identityʳ (ψ x) j)

  off : ∀ b a → (if b then 0ᴬ else (a ⊛ [ b ]ᴬ)) ≐ 0ᴬ
  off true  a _ = refl
  off false a   = ⊛-zeroʳ a

  rest : Σᵃ (λ z → if same x z then 0ᴬ else f z) ≐ 0ᴬ
  rest j = trans (Σᵃ-cong (λ z → off (same x z) (ψ z)) j) (Σᵃ-0 j)

------------------------------------------------------------------------
-- Presentations of groups
--
-- Where H, CNOT and R_k sit in the Clifford hierarchy
--
-- The preliminaries of Amy's QPL 2018 paper say: "For k ≥ 1, all three
-- gates [H, R_k and CNOT] lie in the k-th level of the Clifford
-- hierarchy".  For R_k that holds, and here it is proved for every k
-- (R∈𝒞, and R_k† too, R†∈𝒞), R_k on any wire of n qubits.  For H and
-- CNOT it holds for every k ≥ 2 (H∈𝒞, CNOT∈𝒞), but not at k = 1: C₁
-- is the Pauli group, and neither H nor CNOT is a Pauli (H∉𝒞₁,
-- CNOT∉𝒞₁) -- a Pauli's column at v has its one non-zero entry at
-- v ⊕ x, while H's column at 0 has two and CNOT shifts |0…0⟩ and
-- |e_c⟩ by different vectors.  This is a minor slip in the paper, for
-- "k ≥ 2": what holds is "R_k ∈ C_k for every k ≥ 1, and H, CNOT ∈
-- C₂ ⊆ C_k for every k ≥ 2".  The level of R_k is
-- sharp: for 2 ≤ k ≤ M, R_k is not in C_(k-1), not even up to a global
-- phase ζ^e (R∉𝒞, R†∉𝒞, R-not).
--
-- R_k is the phase ζ^(2^(M-k)) on one wire, and climbs one level per
-- conjugation (PathSum.Hierarchy.Gates's Rs-conj-0, Rs-conj-1):
-- conjugating a Pauli that flips the wire by the phase s gives
-- ζ^(-s) D(2s) P, the phase doubled.  So by induction on k
-- (Rs-𝒞): D(±2^(M-k)) is in C_k for 1 ≤ k ≤ M -- at k = 1 it is Z, and
-- at the step the conjugate is D(±2^(M-k+1)) times a Pauli times a
-- phase, in C_(k-1) by induction and the closure of each level under
-- Paulis on the right and under phases (a power of i at level 1,
-- where ζ^(∓2^(M-2)) = ∓i).  For k > M the development reads R_k as
-- R_M (PathSum.CRK.Circuit), which is in C_M ⊆ C_k; R_0 is the
-- identity (R₀≈I).  Conversely, if R_(k+1) were in C_k up to a phase,
-- conjugating X on its wire and multiplying by X again would put R_k
-- in C_(k-1) up to a phase; and at the bottom S = R_2 is not a Pauli
-- up to any phase ζ^e (Rs-not-pauli): its entries at |0…0⟩ and |e_w⟩
-- differ by the factor i, a diagonal Pauli's by ±1.
--
-- Precision: phases are numerators over 2^M, M = M₀ + 3, so all of
-- this is for every M ≥ 3; R_k ∉ C_(k-1) needs k ≤ M (above M the
-- gate is R_M).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.Levels (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; _xor_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; -1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; ∣⇒∣ᵤ; ∣m⇒∣-m; *-cancelˡ-∣)
open import Data.Integer.Properties using
  (+-identityʳ; *-zeroʳ; *-identityʳ; +-inverseˡ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; _≤_; _<_; _∸_; z≤n; s≤s; >-nonZero)
  renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Nat.Divisibility as ℕDiv
import Data.Nat.Properties as ℕ

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-self; same; same-refl; same-true;
   same-intro; same-≗)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Compose.Sum M₀ using (zpow-≡)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; zpow; rot; rot-map; rot-exp; rot-0ᴬ; rot-zpow; √2·-map;
   √2·-0ᴬ; coeff-map; coeff-zpow; χ; χ-1; χ--1; χ-0; zpow-0≢0ᴬ; N)
  renaming (H to rank)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Hierarchy M₀
open import PathSum.Hierarchy.Gates M₀
open import PathSum.Hierarchy.Operator M₀
open import PathSum.Hierarchy.Pauli M₀
open import PathSum.Maslov.Arith M₀ using (¼+¼; ½·2)
open import PathSum.Order M using (pow-suc)
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; mod-N; divides-N; ≡ᴺ-refl; ≡ᴺ-≡; ≡ᴺ-sym; ≡ᴺ-trans; ≡ᴺ--; ≡ᴺ-N)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  variable
    n : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)

  e-here : (w : Fin n) → eᵛ w w ≡ true
  e-here w = ≔-here 0ᵛ w true

  e-there : {w j : Fin n} → j ≢ w → eᵛ w j ≡ false
  e-there j≢w = ≔-there 0ᵛ true j≢w

  bool-false : ∀ {b} → (b ≡ true → ⊥) → b ≡ false
  bool-false {true}  h = ⊥-elim (h refl)
  bool-false {false} _ = refl


------------------------------------------------------------------------
-- Climbing the levels

-- 𝒞 j ⊆ 𝒞 k for 1 ≤ j ≤ k.

𝒞-mono⁺ : ∀ {j k} {U : Op n} → j ≤ k → 𝒞 (suc j) U → 𝒞 (suc k) U
𝒞-mono⁺ {n} {j} {k} {U} j≤k c =
  subst (λ m → 𝒞 (suc m) U) (ℕ.m∸n+n≡m j≤k) (up (k ∸ j))
  where
  up : ∀ d → 𝒞 (suc (d ℕ+ j)) U
  up zero    = c
  up (suc d) = 𝒞-mono (d ℕ+ j) {U} (up d)


------------------------------------------------------------------------
-- Arithmetic of the phases

-- A sign.

sgn : Bool → ℤ → ℤ
sgn false a = a
sgn true  a = - a

private
  -- Doubling 2^(M-k-1) gives 2^(M-k), when k + 1 ≤ M.

  ∸-step : ∀ a b → suc b ≤ a → a ∸ b ≡ suc (a ∸ suc b)
  ∸-step (suc a) zero    _       = refl
  ∸-step (suc a) (suc b) (s≤s h) = ∸-step a b h

  double : (σ : Bool) (k : ℕ) → suc (suc k) ≤ M →
           (+ 2) * sgn σ (pow (M ∸ suc (suc k))) ≡ sgn σ (pow (M ∸ suc k))
  double σ k h = trans (two σ (pow (M ∸ suc (suc k))))
    (cong (sgn σ) (trans (sym (pow-suc (M ∸ suc (suc k))))
                         (cong pow (sym (∸-step M (suc k) h)))))
    where
    two : ∀ σ a → (+ 2) * sgn σ a ≡ sgn σ (a * (+ 2))
    two false a = solve 1 (λ a → con (+ 2) :* a := a :* con (+ 2)) refl a
    two true  a = solve 1 (λ a → con (+ 2) :* (:- a) := :- (a :* con (+ 2)))
                          refl a

-- The exponents of R_k and R_k†, ±2^(M-k), opaque: an operator whose
-- phase is a reducible expression is expensive for Agda to compare
-- with itself (it unfolds the rotations), and these phases occur in
-- the statements at every level k.  ρ-def unfolds them.

opaque
  ρ : Bool → ℕ → ℤ
  ρ σ k = sgn σ (pow (M ∸ k))

  ρ-def : ∀ σ k → ρ σ k ≡ sgn σ (pow (M ∸ k))
  ρ-def σ k = refl

-- Doubling the exponent of R_(k+2) gives that of R_(k+1).

ρ-double : ∀ σ k → suc (suc k) ≤ M → (+ 2) * ρ σ (suc (suc k)) ≡ ρ σ (suc k)
ρ-double σ k h = trans (cong ((+ 2) *_) (ρ-def σ (suc (suc k))))
                       (trans (double σ k h) (sym (ρ-def σ (suc k))))

-- N is four quarters, so N divides no odd multiple of a quarter.

N≡¼·4 : + N ≡ ¼ * (+ 4)
N≡¼·4 = trans (sym ½·2)
  (trans (cong (_* (+ 2)) (sym ¼+¼))
         (solve 1 (λ q → (q :+ q) :* con (+ 2) := q :* con (+ 4)) refl ¼))

4∤ : ∀ m → 0 < m → m < 4 → ¬ ((+ 4) ∣ (+ m))
4∤ m 0<m m<4 d = ℕ.<⇒≱ m<4 (ℕDiv.∣⇒≤ {{>-nonZero 0<m}} (∣⇒∣ᵤ d))

quarters : ∀ a b m → a - b ≡ ¼ * m → ¬ ((+ 4) ∣ m) → ¬ (a ≡ᴺ b)
quarters a b m eq ¬4 h = ¬4 (*-cancelˡ-∣ ¼ {{ℕ.m^n≢0 2 (suc M₀)}}
  (subst (_∣ (¼ * m)) N≡¼·4 (subst ((+ N) ∣_) eq (divides-N h))))

½≡¼·2 : ½ ≡ ¼ * (+ 2)
½≡¼·2 = trans (sym ¼+¼) (solve 1 (λ q → q :+ q := q :* con (+ 2)) refl ¼)

private
  ¬4∣1 : ¬ ((+ 4) ∣ 1ℤ)
  ¬4∣1 = 4∤ 1 (s≤s z≤n) (s≤s (s≤s z≤n))

  ¬4∣-1 : ¬ ((+ 4) ∣ -1ℤ)
  ¬4∣-1 d = ¬4∣1 (∣m⇒∣-m d)

  ¬4∣-3 : ¬ ((+ 4) ∣ - (+ 3))
  ¬4∣-3 d = 4∤ 3 (s≤s z≤n) (s≤s (s≤s (s≤s (s≤s z≤n)))) (∣m⇒∣-m d)

¼≢0 : ¬ (¼ ≡ᴺ 0ℤ)
¼≢0 = quarters ¼ 0ℤ 1ℤ (solve 1 (λ q → q :- con 0ℤ := q :* con 1ℤ) refl ¼)
               ¬4∣1

¼≢½ : ¬ (¼ ≡ᴺ ½)
¼≢½ = quarters ¼ ½ -1ℤ
  (trans (cong (λ x → ¼ - x) ½≡¼·2)
         (solve 1 (λ q → q :- q :* con (+ 2) := q :* con -1ℤ) refl ¼))
  ¬4∣-1

-¼≢0 : ¬ (- ¼ ≡ᴺ 0ℤ)
-¼≢0 = quarters (- ¼) 0ℤ -1ℤ
  (solve 1 (λ q → :- q :- con 0ℤ := q :* con -1ℤ) refl ¼) ¬4∣-1

-¼≢½ : ¬ (- ¼ ≡ᴺ ½)
-¼≢½ = quarters (- ¼) ½ (- (+ 3))
  (trans (cong (λ x → - ¼ - x) ½≡¼·2)
         (solve 1 (λ q → :- q :- q :* con (+ 2) := q :* con (- (+ 3))) refl ¼))
  ¬4∣-3


------------------------------------------------------------------------
-- Powers of ζ

-- ζ^a = ζ^b exactly when a ≡ b modulo N.

private
  χ≡1 : ∀ z → χ z ≡ 1ℤ → (+ N) ∣ z
  χ≡1 z h = by ((+ N) ∣? z) ((+ N) ∣? (z - (+ rank)))
    where
    by : Dec ((+ N) ∣ z) → Dec ((+ N) ∣ (z - (+ rank))) → (+ N) ∣ z
    by (yes d) _       = d
    by (no ¬d) (yes b) = contradiction (trans (sym (χ--1 ¬d b)) h) (λ ())
    by (no ¬d) (no ¬b) = contradiction (trans (sym (χ-0 ¬d ¬b)) h) (λ ())

zpow-inj : ∀ {a b} → zpow a ≐ zpow b → a ≡ᴺ b
zpow-inj {a} {b} h = mod-N (χ≡1 (a - b)
  (trans (sym (coeff-zpow a b))
    (trans (coeff-map h b)
      (trans (coeff-zpow b b) (χ-1 (divides-N (≡ᴺ-refl {a = b})))))))

zpow-nonzero : ∀ a → ¬ (zpow a ≐ 0ᴬ)
zpow-nonzero a h = zpow-0≢0ᴬ (λ i →
  trans (zpow-≡ (sym (+-inverseˡ a)) i)
    (trans (sym (rot-zpow (- a) a i))
      (trans (rot-map (- a) h i) (rot-0ᴬ (- a) i))))

gz-nonzero : ∀ {g} (e : ℤ) → g ≡ true → ¬ (gz g e ≐ 0ᴬ)
gz-nonzero e refl = zpow-nonzero e

-- A phase on one wire, as an operator, changes its exponent along an
-- equation.

Rs-exp : ∀ {a b} (w : Fin n) → a ≡ b → Rs a w ≈ Rs b w
Rs-exp {a = a} {b} w eq = ≈-by (Rs a w) (Rs b w) refl (λ v u →
  rot-exp {a * [ u w ]ᶻ} {b * [ u w ]ᶻ} (δ v u) (cong (_* [ u w ]ᶻ) eq))


------------------------------------------------------------------------
-- R_k ∈ C_k

-- The phase at the step: a power of i at level 1, any phase above.

private
  phase-ok : ∀ k (σ : Bool) {V : Op n} → 𝒞 (suc k) V →
             𝒞 (suc k) ((- ρ σ (suc (suc k))) ◃ V)
  phase-ok zero σ {V} (p , h) =
    pd (ph p + t σ) (xs p) (zs p) ,
    (◃-cong (- ρ σ 2) h
     ⟨≈⟩ ◃-exp {e = - ρ σ 2} {e′ = ¼ * t σ} (pauli p) (sym (quarter σ))
     ⟨≈⟩ ◃-pauli (t σ) p)
    where
    t : Bool → ℤ
    t false = -1ℤ
    t true  = 1ℤ
    quarter : ∀ σ → ¼ * t σ ≡ - ρ σ 2
    quarter false = trans (solve 1 (λ q → q :* con -1ℤ := :- q) refl ¼)
                          (cong -_ (sym (ρ-def false 2)))
    quarter true  = trans (solve 1 (λ q → q :* con 1ℤ := :- (:- q)) refl ¼)
                          (cong -_ (sym (ρ-def true 2)))
  phase-ok (suc k) σ {V} c = 𝒞-◃ k (- ρ σ (suc (suc (suc k)))) {V} c

  -- One step up, for any phases s and s′ = 2s.

  Rs-up : ∀ k (s s′ : ℤ) (w : Fin n) → (+ 2) * s ≡ s′ →
          (∀ {V : Op n} → 𝒞 (suc k) V → 𝒞 (suc k) ((- s) ◃ V)) →
          𝒞 (suc k) (Rs s′ w) → 𝒞 (suc (suc k)) (Rs s w)
  Rs-up {n} k s s′ w eq ph c =
    diag-unitary (wireFn s w) , λ p → by p (xs p w) refl
    where
    by : (p : PauliData n) (b : Bool) → xs p w ≡ b →
         𝒞 (suc k) (Rs s w · pauli p · Rs s w †)
    by p false e = 𝒞-resp (suc k) (≈-sym (Rs-conj-0 s w p e)) (𝒞-pauli k p)
    by p true  e = 𝒞-resp (suc k)
      (≈-sym (Rs-conj-1 s w p e
              ⟨≈⟩ ◃-cong (- s) (·-congˡ (pauli p)
                                  (Rs-exp {a = (+ 2) * s} {b = s′} w eq))))
      (ph {Rs s′ w · pauli p} (𝒞-·pauli k {Rs s′ w} p c))

-- D(±2^(M-k)) ∈ C_k, for 1 ≤ k ≤ M.

Rs-𝒞 : ∀ k (σ : Bool) (w : Fin n) → suc k ≤ M → 𝒞 (suc k) (Rs (ρ σ (suc k)) w)
Rs-𝒞 zero false w h =
  Z^ w , (Rs-exp {a = ρ false 1} {b = ½} w (ρ-def false 1) ⟨≈⟩ Rs-½ w)
Rs-𝒞 zero true  w h =
  Z^ w , (Rs-exp {a = ρ true 1} {b = - ½} w (ρ-def true 1) ⟨≈⟩ Rs-−½ w)
Rs-𝒞 (suc k) σ w h =
  Rs-up k (ρ σ (suc (suc k))) (ρ σ (suc k)) w
        (ρ-double σ k h) (phase-ok k σ) (Rs-𝒞 k σ w (ℕ.<⇒≤ h))

-- R_0 is the identity: ζ^N = 1.

R₀≈I : (σ : Bool) (w : Fin n) → Rs (ρ σ 0) w ≈ I
R₀≈I σ w = diag-I (wireFn (ρ σ 0) w) (λ u → zero-or-N σ (u w))
  where
  zero-or-N : ∀ σ b → ρ σ 0 * [ b ]ᶻ ≡ᴺ 0ℤ
  zero-or-N σ false = ≡ᴺ-≡ (*-zeroʳ (ρ σ 0))
  zero-or-N false true = ≡ᴺ-trans
    (≡ᴺ-≡ (trans (*-identityʳ (ρ false 0))
                 (trans (ρ-def false 0)
                        (solve 1 (λ x → x := con 1ℤ :* x) refl (pow M)))))
    (≡ᴺ-N 1ℤ)
  zero-or-N true true = ≡ᴺ-trans
    (≡ᴺ-≡ (trans (*-identityʳ (ρ true 0))
                 (trans (ρ-def true 0)
                        (solve 1 (λ x → :- x := con -1ℤ :* x) refl (pow M)))))
    (≡ᴺ-N -1ℤ)

-- R_k ∈ C_k for every k ≥ 1; above M the gate is R_M.

private
  R-any : (σ : Bool) (k : ℕ) (w : Fin n) → Dec (suc k ≤ M) →
          𝒞 (suc k) (Rs (ρ σ (suc k)) w)
  R-any σ k w (yes h) = Rs-𝒞 k σ w h
  R-any σ k w (no ¬h) =
    𝒞-resp (suc k)
      (Rs-exp {a = ρ σ (suc (suc (suc M₀)))} {b = ρ σ (suc k)} w
              (trans (ρ-def σ (suc (suc (suc M₀))))
                (trans (cong (λ m → sgn σ (pow m)) M∸M≡M∸k)
                       (sym (ρ-def σ (suc k))))))
      (𝒞-mono⁺ {j = suc (suc M₀)} {k = k}
               {U = Rs (ρ σ (suc (suc (suc M₀)))) w} M≤k
               (Rs-𝒞 (suc (suc M₀)) σ w ℕ.≤-refl))
    where
    M≤k′ : M ≤ k
    M≤k′ = ℕ.≮⇒≥ ¬h
    M≤k : suc (suc M₀) ≤ k
    M≤k = ℕ.≤-trans (ℕ.n≤1+n (suc (suc M₀))) M≤k′
    M∸M≡M∸k : M ∸ suc (suc (suc M₀)) ≡ M ∸ suc k
    M∸M≡M∸k = trans (ℕ.n∸n≡0 M)
                    (sym (ℕ.m≤n⇒m∸n≡0 (ℕ.≤-trans M≤k′ (ℕ.n≤1+n k))))

R∈𝒞 : ∀ k (w : Fin n) → 1 ≤ k → 𝒞 k (Rs (ρ false k) w)
R∈𝒞 (suc k) w _ = R-any false k w (suc k ℕ.≤? M)

R†∈𝒞 : ∀ k (w : Fin n) → 1 ≤ k → 𝒞 k (Rs (ρ true k) w)
R†∈𝒞 (suc k) w _ = R-any true k w (suc k ℕ.≤? M)


------------------------------------------------------------------------
-- H and CNOT: C_k for k ≥ 2, not C₁

H∈𝒞 : ∀ k (w : Fin n) → 2 ≤ k → 𝒞 k (hadOp w)
H∈𝒞 (suc zero) w (s≤s ())
H∈𝒞 (suc (suc k)) w _ =
  𝒞-mono⁺ {j = 1} {k = suc k} {U = hadOp w} (s≤s z≤n) (had-𝒞₂ w)

CNOT∈𝒞 : ∀ k (c t : Fin n) → c ≢ t → 2 ≤ k → 𝒞 k (cnotOp c t)
CNOT∈𝒞 (suc zero) c t c≢t (s≤s ())
CNOT∈𝒞 (suc (suc k)) c t c≢t _ =
  𝒞-mono⁺ {j = 1} {k = suc k} {U = cnotOp c t} (s≤s z≤n) (cnot-𝒞₂ c t c≢t)

-- H's column at 0 has two non-zero entries, a Pauli's one.

H∉𝒞₁ : (w : Fin n) → ¬ 𝒞 1 (hadOp w)
H∉𝒞₁ {n} w (p , h) = case (same (0ᵛ ⊕ᵛ xs p) 0ᵛ) refl
  where
  nonzero : (u : Assign n) → same (0ᵛ [ w ≔ u w ]) u ≡ true →
            ¬ (mat (hadOp w) 0ᵛ u ≐ 0ᴬ)
  nonzero u g z = gz-nonzero (½ * [ 0ᵛ w ∧ u w ]ᶻ) g (≐-sym (had-δ w 0ᵛ u) ∙ z)

  zero-if : (u : Assign n) → same (0ᵛ ⊕ᵛ xs p) u ≡ false →
            mat (hadOp w) 0ᵛ u ≐ 0ᴬ
  zero-if u g = ≈-at h 0ᵛ u ∙ √2·-map (gz-guard (φᴾ p 0ᵛ) g) ∙ √2·-0ᴬ

  case : (b : Bool) → same (0ᵛ ⊕ᵛ xs p) 0ᵛ ≡ b → ⊥
  case false g = nonzero 0ᵛ (same-intro (0ᵛ [ w ≔ 0ᵛ w ]) 0ᵛ (≔-self 0ᵛ w))
                         (zero-if 0ᵛ g)
  case true  g = nonzero (eᵛ w)
    (same-intro (0ᵛ [ w ≔ eᵛ w w ]) (eᵛ w)
                (λ j → cong (λ b → (0ᵛ [ w ≔ b ]) j) (e-here w)))
    (zero-if (eᵛ w) (bool-false (λ s →
       contradiction (trans (sym (same-true (0ᵛ ⊕ᵛ xs p) 0ᵛ g w))
                            (trans (same-true (0ᵛ ⊕ᵛ xs p) (eᵛ w) s w)
                                   (e-here w)))
                     (λ ()))))

-- CNOT leaves |0…0⟩ where it is but moves |e_c⟩ to |e_c + e_t⟩; a
-- Pauli shifts every basis state by the same vector.

CNOT∉𝒞₁ : (c t : Fin n) → c ≢ t → ¬ 𝒞 1 (cnotOp c t)
CNOT∉𝒞₁ {n} c t c≢t (p , h) = case (same (0ᵛ ⊕ᵛ xs p) 0ᵛ) refl
  where
  t≢c : t ≢ c
  t≢c e = c≢t (sym e)

  -- CNOT's entry at (v, π v) is 1.
  nonzero : (v : Assign n) → ¬ (mat (cnotOp c t) v (flip c t v) ≐ 0ᴬ)
  nonzero v = gz-nonzero 0ℤ
    (same-intro v (flip c t (flip c t v)) (λ j → sym (flip-flip c t c≢t v j)))

  zero-if : (v u : Assign n) → same (v ⊕ᵛ xs p) u ≡ false →
            mat (cnotOp c t) v u ≐ 0ᴬ
  zero-if v u g = ≈-at h v u ∙ gz-guard (φᴾ p v) g

  case : (b : Bool) → same (0ᵛ ⊕ᵛ xs p) 0ᵛ ≡ b → ⊥
  case false g = nonzero 0ᵛ (zero-if 0ᵛ (flip c t 0ᵛ)
    (trans (same-≗ {x = 0ᵛ ⊕ᵛ xs p} {x′ = 0ᵛ ⊕ᵛ xs p} {z = flip c t 0ᵛ}
                   {z′ = 0ᵛ} (λ _ → refl) (λ j → ≔-self 0ᵛ t j))
           g))
  case true  g = nonzero (eᵛ c)
    (zero-if (eᵛ c) (flip c t (eᵛ c)) (bool-false (λ s →
       contradiction
         (trans (sym (cong₂ _xor_ (e-there t≢c) x0t))
           (trans (same-true (eᵛ c ⊕ᵛ xs p) (flip c t (eᵛ c)) s t)
             (trans (≔-here (eᵛ c) t (eᵛ c t xor eᵛ c c))
                    (cong₂ _xor_ (e-there t≢c) (e-here c)))))
         (λ ()))))
    where
    x0t : xs p t ≡ false
    x0t = same-true (0ᵛ ⊕ᵛ xs p) 0ᵛ g t


------------------------------------------------------------------------
-- R_k ∉ C_(k-1)

-- A phase t on one wire, with t ≢ 0 and t ≢ ½ modulo N, is not a Pauli
-- up to any phase: its diagonal entries at |0…0⟩ and |e_w⟩ differ by
-- ζ^t, a diagonal Pauli's by ζ^0 or ζ^½.

Rs-not-pauli : (t : ℤ) (w : Fin n) → ¬ (t ≡ᴺ 0ℤ) → ¬ (t ≡ᴺ ½) →
               ∀ e → ¬ 𝒞 1 (e ◃ Rs t w)
Rs-not-pauli {n} t w t≢0 t≢½ e (p , h) = case (same (0ᵛ ⊕ᵛ xs p) 0ᵛ) refl
  where
  -- The diagonal entries.
  diag : ∀ v → mat (e ◃ Rs t w) v v ≐ zpow (e + (t * [ v w ]ᶻ + 0ℤ))
  diag v = rot-map e (rot-map (t * [ v w ]ᶻ) (gz-guard 0ℤ (same-refl v))
                      ∙ rot-zpow (t * [ v w ]ᶻ) 0ℤ)
           ∙ rot-zpow e (t * [ v w ]ᶻ + 0ℤ)

  entry : ∀ v → mat (e ◃ Rs t w) v v ≐ entryᴾ p v v
  entry v = ≈-at h v v

  case : (b : Bool) → same (0ᵛ ⊕ᵛ xs p) 0ᵛ ≡ b → ⊥
  case false g = zpow-nonzero (e + (t * 0ℤ + 0ℤ))
    (≐-sym (diag 0ᵛ) ∙ entry 0ᵛ ∙ gz-guard (φᴾ p 0ᵛ) g)
  case true g = last (zs p w) refl
    where
    x0 : ∀ j → xs p j ≡ false
    x0 j = same-true (0ᵛ ⊕ᵛ xs p) 0ᵛ g j

    ge : same (eᵛ w ⊕ᵛ xs p) (eᵛ w) ≡ true
    ge = same-intro (eᵛ w ⊕ᵛ xs p) (eᵛ w)
                    (λ j → trans (cong (eᵛ w j xor_) (x0 j))
                                 (xor-false (eᵛ w j)))

    at0 : e + (t * 0ℤ + 0ℤ) ≡ᴺ φᴾ p 0ᵛ
    at0 = zpow-inj (≐-sym (diag 0ᵛ) ∙ entry 0ᵛ ∙ gz-guard (φᴾ p 0ᵛ) g)

    at1 : e + (t * [ eᵛ w w ]ᶻ + 0ℤ) ≡ᴺ φᴾ p (eᵛ w)
    at1 = zpow-inj (≐-sym (diag (eᵛ w)) ∙ entry (eᵛ w)
                    ∙ gz-guard (φᴾ p (eᵛ w)) ge)

    -- t is the difference of the two phases.
    t≡ : t ≡ᴺ ½ * [ zs p w ]ᶻ
    t≡ = ≡ᴺ-trans
      (≡ᴺ-≡ (solve 2 (λ e t → t := (e :+ (t :* con 1ℤ :+ con 0ℤ))
                                   :- (e :+ (t :* con 0ℤ :+ con 0ℤ)))
                     refl e t))
      (≡ᴺ-trans (≡ᴺ-- (≡ᴺ-trans (≡ᴺ-≡ (cong (λ b → e + (t * [ b ]ᶻ + 0ℤ))
                                              (sym (e-here w))))
                                at1)
                      at0)
        (≡ᴺ-≡ (trans (cong₂ (λ x y → (¼ * ph p + ½ * [ x ]ᶻ)
                                     - (¼ * ph p + ½ * [ y ]ᶻ))
                            (dot-e (zs p) w) (dot-0ʳ (zs p) 0ᵛ (λ _ → refl)))
                     (trans (cong (λ y → (¼ * ph p + ½ * [ zs p w ]ᶻ)
                                         - (¼ * ph p + y))
                                  (*-zeroʳ ½))
                            (solve 2 (λ q h → (q :+ h) :- (q :+ con 0ℤ) := h)
                                   refl (¼ * ph p) (½ * [ zs p w ]ᶻ))))))

    last : (b : Bool) → zs p w ≡ b → ⊥
    last false eq = t≢0 (≡ᴺ-trans t≡ (≡ᴺ-≡ (trans (cong (λ b → ½ * [ b ]ᶻ) eq)
                                                  (*-zeroʳ ½))))
    last true  eq = t≢½ (≡ᴺ-trans t≡ (≡ᴺ-≡ (trans (cong (λ b → ½ * [ b ]ᶻ) eq)
                                                  (*-identityʳ ½))))

-- S = R_2 and S† are not Paulis up to a phase.

S∉𝒞₁ : (w : Fin n) → ∀ e → ¬ 𝒞 1 (e ◃ Rs (ρ false 2) w)
S∉𝒞₁ w = Rs-not-pauli (ρ false 2) w
  (λ h → ¼≢0 (≡ᴺ-trans (≡ᴺ-≡ (sym (ρ-def false 2))) h))
  (λ h → ¼≢½ (≡ᴺ-trans (≡ᴺ-≡ (sym (ρ-def false 2))) h))

S†∉𝒞₁ : (w : Fin n) → ∀ e → ¬ 𝒞 1 (e ◃ Rs (ρ true 2) w)
S†∉𝒞₁ w = Rs-not-pauli (ρ true 2) w
  (λ h → -¼≢0 (≡ᴺ-trans (≡ᴺ-≡ (sym (ρ-def true 2))) h))
  (λ h → -¼≢½ (≡ᴺ-trans (≡ᴺ-≡ (sym (ρ-def true 2))) h))

-- X X = I.

XX≈I : (w : Fin n) → pauli (X^ w) · pauli (X^ w) ≈ I
XX≈I w = pauli-· (X^ w) (X^ w)
  ⟨≈⟩ pauli-≈ (X^ w ∙ᴾ X^ w) 1ᴾ
        (≡ᴺ-≡ (cong (λ b → ¼ * (0ℤ + 0ℤ + (+ 2) * [ b ]ᶻ))
                    (dot-0ˡ 0ᵛ (eᵛ w) (λ _ → refl))))
        (λ j → xor-self (eᵛ w j)) (λ _ → refl)
  ⟨≈⟩ pauli-I

-- R_(k+2) is not in C_(k+1), up to any phase: conjugating X_w and
-- multiplying by X_w again would put R_(k+1) in C_k up to a phase.

private
  R-down : ∀ k (s s′ : ℤ) (w : Fin n) → (+ 2) * s ≡ s′ →
           (∀ e → ¬ 𝒞 (suc k) (e ◃ Rs s′ w)) →
           ∀ e → ¬ 𝒞 (suc (suc k)) (e ◃ Rs s w)
  R-down k s s′ w eq ih e c =
    ih (- s)
      (𝒞-resp (suc k) back
        (𝒞-·pauli k {(- s) ◃ (Rs ((+ 2) * s) w · pauli (X^ w))} (X^ w)
          (𝒞-resp (suc k) conj (proj₂ c (X^ w)))))
    where
    conj : (e ◃ Rs s w) · pauli (X^ w) · (e ◃ Rs s w) † ≈
           (- s) ◃ (Rs ((+ 2) * s) w · pauli (X^ w))
    conj = ◃-conj e (Rs s w) (pauli (X^ w)) ⟨≈⟩ Rs-conj-1 s w (X^ w) (e-here w)

    back : (- s) ◃ (Rs ((+ 2) * s) w · pauli (X^ w)) · pauli (X^ w) ≈
           (- s) ◃ Rs s′ w
    back = ◃-·ˡ (- s) (Rs ((+ 2) * s) w · pauli (X^ w)) (pauli (X^ w))
           ⟨≈⟩ ◃-cong (- s)
                 (·-assoc (Rs ((+ 2) * s) w) (pauli (X^ w)) (pauli (X^ w))
                  ⟨≈⟩ ·-congʳ (Rs ((+ 2) * s) w) (XX≈I w)
                  ⟨≈⟩ ·-identityʳ (Rs ((+ 2) * s) w)
                  ⟨≈⟩ Rs-exp {a = (+ 2) * s} {b = s′} w eq)

R-not : ∀ k (σ : Bool) (w : Fin n) → suc (suc k) ≤ M →
        ∀ e → ¬ 𝒞 (suc k) (e ◃ Rs (ρ σ (suc (suc k))) w)
R-not zero    false w h = S∉𝒞₁ w
R-not zero    true  w h = S†∉𝒞₁ w
R-not (suc k) σ w h =
  R-down k (ρ σ (suc (suc (suc k)))) (ρ σ (suc (suc k)))
         w (ρ-double σ (suc k) h) (R-not k σ w (ℕ.<⇒≤ h))

-- R_k and R_k† are not in C_(k-1), for 2 ≤ k ≤ M.

R∉𝒞 : ∀ k (w : Fin n) → 2 ≤ k → k ≤ M → ¬ 𝒞 (k ∸ 1) (Rs (ρ false k) w)
R∉𝒞 (suc (suc k)) w _ h c =
  R-not k false w h 0ℤ
    (𝒞-resp (suc k) (≈-sym (◃-0 (Rs (ρ false (suc (suc k))) w))) c)

R†∉𝒞 : ∀ k (w : Fin n) → 2 ≤ k → k ≤ M → ¬ 𝒞 (k ∸ 1) (Rs (ρ true k) w)
R†∉𝒞 (suc (suc k)) w _ h c =
  R-not k true w h 0ℤ
    (𝒞-resp (suc k) (≈-sym (◃-0 (Rs (ρ true (suc (suc k))) w))) c)

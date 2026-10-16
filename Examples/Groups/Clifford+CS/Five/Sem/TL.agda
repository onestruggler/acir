------------------------------------------------------------------------
-- Presentations of groups
--
-- Two-level operators, permutations, and the control on the top wire
--
-- The semantic side of the decoding on five wires.  A two-level operator
-- `tl B p q` is the 2 × 2 block B on the basis vectors p and q (in that
-- order) and the identity elsewhere.  Conjugating an operator by the
-- permutation operator of a bijection f pulls it back along f (`conj`),
-- so a two-level operator is renamed to the block on f p and f q
-- (`conj-tl`), and the conjugation is multiplicative (`conj-∙`).
-- `ctrl` reads an operator on m wires as the one on m + 1 wires that
-- applies it where the top wire reads 0 (Λ⁰ on matrices, built from the
-- Kronecker product): it is multiplicative (`ctrl-∙`) and injective
-- (`ctrl-inj`), and on four wires a two-level operator on vectors whose
-- top bit is 0 is `ctrl` of the four-wire one (`tl-ctrl`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Sem.TL where

open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∧_)
import Data.Bool.Properties as BoolP
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
import Data.Nat.Properties as NP
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using ([] ; _∷_ ; _++_)
open import Data.Vec.Properties using (≡-dec)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (Dec ; yes ; no)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.EncodingSemantics.Diag using (δb-≢)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqᵇ ; eqB)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
  using (eqB-complete ; eqB-false)

private
  variable
    m n : ℕ

  _≟ᵇ_ : (x y : Bits n) → Dec (x ≡ y)
  _≟ᵇ_ = ≡-dec BoolP._≟_

  ite : ∀ {c c′ : Bool} {a a′ b b′ : 𝔽} → c ≡ c′ → a ≡ a′ → b ≡ b′ →
        (if c then a else b) ≡ (if c′ then a′ else b′)
  ite refl refl refl = refl

  ite-* : ∀ (c : Bool) (a b z : 𝔽) → (if c then a else b) * z ≡ (if c then a * z else b * z)
  ite-* true  a b z = refl
  ite-* false a b z = refl

------------------------------------------------------------------------
-- Two-level operators

-- The block γ^-k [[a , b] , [c , d]].
record Blk : Set where
  constructor blk
  field
    k       : ℕ
    a b c d : 𝔽

open Blk

-- The block on the basis vectors p (first) and q, the identity elsewhere.
tlOp : Blk → Bits n → Bits n → Op n
tlOp B p q x y =
  if eqB x p then a B * δb p y + b B * δb q y
  else if eqB x q then c B * δb p y + d B * δb q y
  else γ^ k B * δb x y

tl : Blk → Bits n → Bits n → Scaled n
tl B p q = (k B , tlOp B p q)

------------------------------------------------------------------------
-- Permutations

perm : (Bits n → Bits n) → Op n
perm f x y = δb x (f y)

perm-⊙ : (f g : Bits n → Bits n) → (perm f ⊙ perm g) ≐ perm (f ∘ g)
perm-⊙ f g x y = Σ-δʳ (g y) (λ z → δb x (f z))

-- A bijection, given with its inverse.
module Bij (f g : Bits n → Bits n) (fg : ∀ x → f (g x) ≡ x) (gf : ∀ x → g (f x) ≡ x) where

  private
    δ-move′ : ∀ x z → Dec (x ≡ f z) → δb x (f z) ≡ δb (g x) z
    δ-move′ x z (yes e) =
      Eq.trans (Eq.cong (λ v → δb v (f z)) e)
        (Eq.trans (δb-refl (f z))
          (Eq.sym (Eq.trans (Eq.cong (λ v → δb (g v) z) e)
                    (Eq.trans (Eq.cong (λ v → δb v z) (gf z)) (δb-refl z)))))
    δ-move′ x z (no ne) =
      Eq.trans (δb-≢ x (f z) ne)
        (Eq.sym (δb-≢ (g x) z (λ e → ne (Eq.trans (Eq.sym (fg x)) (Eq.cong f e)))))

  -- δ at x and f z is δ at g x and z.
  δ-move : ∀ x z → δb x (f z) ≡ δb (g x) z
  δ-move x z = δ-move′ x z (x ≟ᵇ f z)

  -- δ is invariant.
  δ-inv : ∀ x y → δb (g x) (g y) ≡ δb x y
  δ-inv x y = Eq.trans (Eq.sym (δ-move x (g y))) (Eq.cong (δb x) (fg y))

  δ-at : ∀ p y → δb p (g y) ≡ δb (f p) y
  δ-at p y = Eq.trans (Eq.cong (λ v → δb v (g y)) (Eq.sym (gf p))) (δ-inv (f p) y)

  private
    eqB-move′ : ∀ x p → Dec (x ≡ f p) → eqB (g x) p ≡ eqB x (f p)
    eqB-move′ x p (yes e) =
      Eq.trans (eqB-complete (g x) p (Eq.trans (Eq.cong g e) (gf p)))
        (Eq.sym (eqB-complete x (f p) e))
    eqB-move′ x p (no ne) =
      Eq.trans (eqB-false (g x) p (λ e → ne (Eq.trans (Eq.sym (fg x)) (Eq.cong f e))))
        (Eq.sym (eqB-false x (f p) ne))

  eqB-move : ∀ x p → eqB (g x) p ≡ eqB x (f p)
  eqB-move x p = eqB-move′ x p (x ≟ᵇ f p)

  -- Conjugation pulls an operator back along the bijection.
  conj : (M : Op n) → (perm f ⊙ M ⊙ perm g) ≐ (λ x y → M (g x) (g y))
  conj M x y =
    Eq.trans (Σ-δʳ (g y) (λ z → (perm f ⊙ M) x z))
      (Eq.trans (Σ-cong {f = λ z → δb x (f z) * M z (g y)} {g = λ z → δb (g x) z * M z (g y)}
                  (λ z → Eq.cong (_* M z (g y)) (δ-move x z)))
        (Σ-δˡ (g x) (λ z → M z (g y))))

  -- A two-level operator is renamed.
  tl-pull : (B : Blk) (p q : Bits n) → ∀ x y → tlOp B p q (g x) (g y) ≡ tlOp B (f p) (f q) x y
  tl-pull B p q x y =
    ite (eqB-move x p)
      (Eq.cong₂ _+_ (Eq.cong (a B *_) (δ-at p y)) (Eq.cong (b B *_) (δ-at q y)))
      (ite (eqB-move x q)
        (Eq.cong₂ _+_ (Eq.cong (c B *_) (δ-at p y)) (Eq.cong (d B *_) (δ-at q y)))
        (Eq.cong (γ^ k B *_) (δ-inv x y)))

  -- The conjugation of scaled operators.
  conjS : Scaled n → Scaled n
  conjS s = ((0 , perm f) ∙ s) ∙ (0 , perm g)

  conj-cong : {s t : Scaled n} → s ~ t → conjS s ~ conjS t
  conj-cong {s} {t} e =
    ∙-cong {s = (0 , perm f) ∙ s} {s' = (0 , perm f) ∙ t} {t = 0 , perm g} {t' = 0 , perm g}
      (∙-cong {s = 0 , perm f} {s' = 0 , perm f} {t = s} {t' = t} (~-refl (0 , perm f)) e)
      (~-refl (0 , perm g))

  conj-tl : (B : Blk) (p q : Bits n) → conjS (tl B p q) ~ tl B (f p) (f q)
  conj-tl B p q =
    ~-reflexive {l = k B +ℕ 0} {k B} {M = (perm f ⊙ tlOp B p q) ⊙ perm g} {tlOp B (f p) (f q)}
      (NP.+-identityʳ (k B))
      (λ x y → Eq.trans (conj (tlOp B p q) x y) (tl-pull B p q x y))

  private
    gf-op : (perm g ⊙ perm f) ≐ Idₒ
    gf-op x y = Eq.trans (perm-⊙ g f x y) (Eq.cong (δb x) (gf y))

    conj-op∙ : (M N : Op n) →
               (((perm f ⊙ M) ⊙ perm g) ⊙ ((perm f ⊙ N) ⊙ perm g)) ≐ ((perm f ⊙ (M ⊙ N)) ⊙ perm g)
    conj-op∙ M N =
      ≐-trans (⊙-assoc (perm f ⊙ M) (perm g) ((perm f ⊙ N) ⊙ perm g))
        (≐-trans (⊙-cong (≐-refl (perm f ⊙ M)) mid)
          (≐-trans (≐-sym (⊙-assoc (perm f ⊙ M) N (perm g)))
                   (⊙-cong (⊙-assoc (perm f) M N) (≐-refl (perm g)))))
      where
      mid : (perm g ⊙ ((perm f ⊙ N) ⊙ perm g)) ≐ (N ⊙ perm g)
      mid = ≐-trans (≐-sym (⊙-assoc (perm g) (perm f ⊙ N) (perm g)))
              (⊙-cong (≐-trans (≐-sym (⊙-assoc (perm g) (perm f) N))
                         (≐-trans (⊙-cong gf-op (≐-refl N)) (⊙-identityˡ N)))
                      (≐-refl (perm g)))

  conj-∙ : (s t : Scaled n) → conjS (s ∙ t) ~ (conjS s ∙ conjS t)
  conj-∙ (l , M) (l′ , N) =
    ~-reflexive {l = (l +ℕ l′) +ℕ 0} {(l +ℕ 0) +ℕ (l′ +ℕ 0)}
      {M = (perm f ⊙ (M ⊙ N)) ⊙ perm g} {((perm f ⊙ M) ⊙ perm g) ⊙ ((perm f ⊙ N) ⊙ perm g)}
      (scales l l′) (≐-sym (conj-op∙ M N))
    where
    scales : ∀ l l′ → ((l +ℕ l′) +ℕ 0) ≡ ((l +ℕ 0) +ℕ (l′ +ℕ 0))
    scales l l′ = Eq.trans (NP.+-identityʳ (l +ℕ l′))
      (Eq.sym (Eq.cong₂ _+ℕ_ (NP.+-identityʳ l) (NP.+-identityʳ l′)))

  conj-ε : conjS ε∙ ~ ε∙
  conj-ε = ~-reflexive {l = 0} {0} {M = (perm f ⊙ Idₒ) ⊙ perm g} {Idₒ} refl
             (λ x y → Eq.trans (conj Idₒ x y) (δ-inv x y))

------------------------------------------------------------------------
-- The control on the top wire

-- The projections on the top wire.
P₀ P₁ : Op 1
P₀ (false ∷ []) (false ∷ []) = 1#
P₀ (false ∷ []) (true ∷ [])  = 0#
P₀ (true ∷ [])  (false ∷ []) = 0#
P₀ (true ∷ [])  (true ∷ [])  = 0#
P₁ (false ∷ []) (false ∷ []) = 0#
P₁ (false ∷ []) (true ∷ [])  = 0#
P₁ (true ∷ [])  (false ∷ []) = 0#
P₁ (true ∷ [])  (true ∷ [])  = 1#

private
  Z₁ : Op 1
  Z₁ _ _ = 0#

  P00 : (P₀ ⊙ P₀) ≐ P₀
  P00 (false ∷ []) (false ∷ []) = refl
  P00 (false ∷ []) (true ∷ [])  = refl
  P00 (true ∷ [])  (false ∷ []) = refl
  P00 (true ∷ [])  (true ∷ [])  = refl

  P11 : (P₁ ⊙ P₁) ≐ P₁
  P11 (false ∷ []) (false ∷ []) = refl
  P11 (false ∷ []) (true ∷ [])  = refl
  P11 (true ∷ [])  (false ∷ []) = refl
  P11 (true ∷ [])  (true ∷ [])  = refl

  P01 : (P₀ ⊙ P₁) ≐ Z₁
  P01 (false ∷ []) (false ∷ []) = refl
  P01 (false ∷ []) (true ∷ [])  = refl
  P01 (true ∷ [])  (false ∷ []) = refl
  P01 (true ∷ [])  (true ∷ [])  = refl

  P10 : (P₁ ⊙ P₀) ≐ Z₁
  P10 (false ∷ []) (false ∷ []) = refl
  P10 (false ∷ []) (true ∷ [])  = refl
  P10 (true ∷ [])  (false ∷ []) = refl
  P10 (true ∷ [])  (true ∷ [])  = refl

  P0+P1 : (λ u v → P₀ u v + P₁ u v) ≐ Idₒ {1}
  P0+P1 (false ∷ []) (false ∷ []) = refl
  P0+P1 (false ∷ []) (true ∷ [])  = refl
  P0+P1 (true ∷ [])  (false ∷ []) = refl
  P0+P1 (true ∷ [])  (true ∷ [])  = refl

  tensor-zeroʳ : (M : Op m) → ∀ (x y : Bits (m +ℕ 1)) → tensor M Z₁ x y ≡ 0#
  tensor-zeroʳ {zero}  M x       y       = *-zeroʳ (M [] [])
  tensor-zeroʳ {suc m} M (a ∷ x) (b ∷ y) = tensor-zeroʳ {m} (λ u v → M (a ∷ u) (b ∷ v)) x y

  tensor-addʳ : (M : Op m) (N N′ : Op 1) → ∀ (x y : Bits (m +ℕ 1)) →
                tensor M (λ u v → N u v + N′ u v) x y ≡ tensor M N x y + tensor M N′ x y
  tensor-addʳ {zero}  M N N′ x       y       = *-distribˡ-+ (M [] []) (N x y) (N′ x y)
  tensor-addʳ {suc m} M N N′ (a ∷ x) (b ∷ y) =
    tensor-addʳ {m} (λ u v → M (a ∷ u) (b ∷ v)) N N′ x y

  -- The product distributes over the sum of operators.
  ⊙-+ˡ : (A B C : Op n) → ((λ x y → A x y + B x y) ⊙ C) ≐ (λ x y → (A ⊙ C) x y + (B ⊙ C) x y)
  ⊙-+ˡ A B C x y =
    Eq.trans (Σ-cong {f = λ z → (A x z + B x z) * C z y} {g = λ z → A x z * C z y + B x z * C z y}
                     (λ z → *-distribʳ-+ (C z y) (A x z) (B x z)))
             (Σ-add (λ z → A x z * C z y) (λ z → B x z * C z y))

  ⊙-+ʳ : (A B C : Op n) → (A ⊙ (λ x y → B x y + C x y)) ≐ (λ x y → (A ⊙ B) x y + (A ⊙ C) x y)
  ⊙-+ʳ A B C x y =
    Eq.trans (Σ-cong {f = λ z → A x z * (B z y + C z y)} {g = λ z → A x z * B z y + A x z * C z y}
                     (λ z → *-distribˡ-+ (A x z) (B z y) (C z y)))
             (Σ-add (λ z → A x z * B z y) (λ z → A x z * C z y))

-- The scaled identity.
γI : ℕ → Op n
γI k = γ^ k · Idₒ

private
  γI-⊙ : ∀ k l → (γI {n} k ⊙ γI l) ≐ γI (k +ℕ l)
  γI-⊙ k l = ≐-trans (·-⊙ (γ^ k) (γ^ l) Idₒ Idₒ)
               (·-cong (Eq.sym (γ^-+ k l)) (⊙-identityˡ Idₒ))

ctrlOp : ℕ → Op m → Op (m +ℕ 1)
ctrlOp {m} k M x y = tensor M P₀ x y + tensor (γI {m} k) P₁ x y

ctrl : Scaled m → Scaled (m +ℕ 1)
ctrl (k , M) = (k , ctrlOp k M)

private
  module Prod (k l : ℕ) (M N : Op m) where
    A B C D : Op (m +ℕ 1)
    A = tensor M P₀
    B = tensor (γI {m} k) P₁
    C = tensor N P₀
    D = tensor (γI {m} l) P₁

    AC : (A ⊙ C) ≐ tensor (M ⊙ N) P₀
    AC = ≐-trans (tensor-⊙ M N P₀ P₀) (tensor-cong (≐-refl (M ⊙ N)) P00)

    AD : ∀ x y → (A ⊙ D) x y ≡ 0#
    AD x y = Eq.trans (≐-trans (tensor-⊙ M (γI l) P₀ P₁) (tensor-cong (≐-refl (M ⊙ γI l)) P01) x y)
                      (tensor-zeroʳ (M ⊙ γI l) x y)

    BC : ∀ x y → (B ⊙ C) x y ≡ 0#
    BC x y = Eq.trans (≐-trans (tensor-⊙ (γI k) N P₁ P₀) (tensor-cong (≐-refl (γI k ⊙ N)) P10) x y)
                      (tensor-zeroʳ (γI k ⊙ N) x y)

    BD : (B ⊙ D) ≐ tensor (γI {m} (k +ℕ l)) P₁
    BD = ≐-trans (tensor-⊙ (γI k) (γI l) P₁ P₁) (tensor-cong (γI-⊙ k l) P11)

    prod : (ctrlOp k M ⊙ ctrlOp l N) ≐ ctrlOp (k +ℕ l) (M ⊙ N)
    prod x y =
      Eq.trans (⊙-+ˡ A B (λ x y → C x y + D x y) x y)
        (Eq.trans (Eq.cong₂ _+_ (⊙-+ʳ A C D x y) (⊙-+ʳ B C D x y))
          (Eq.trans (Eq.cong₂ _+_ (Eq.cong₂ _+_ (AC x y) (AD x y)) (Eq.cong₂ _+_ (BC x y) (BD x y)))
            (Eq.cong₂ _+_ (+-identityʳ _) (+-identityˡ _))))

ctrl-∙ : (s t : Scaled m) → ctrl (s ∙ t) ~ (ctrl s ∙ ctrl t)
ctrl-∙ (k , M) (l , N) =
  ~-reflexive {l = k +ℕ l} {k +ℕ l} {M = ctrlOp (k +ℕ l) (M ⊙ N)} {ctrlOp k M ⊙ ctrlOp l N}
    refl (≐-sym (Prod.prod k l M N))

ctrl-ε : ctrl (ε∙ {m}) ~ ε∙
ctrl-ε {m} = ~-reflexive {l = 0} {0} {M = ctrlOp {m} 0 Idₒ} {Idₒ} refl (λ x y →
  Eq.trans (Eq.cong (tensor Idₒ P₀ x y +_)
                    (tensor-cong {M = γI {m} 0} {M' = Idₒ} (·-1 Idₒ) (≐-refl P₁) x y))
    (Eq.trans (Eq.sym (tensor-addʳ Idₒ P₀ P₁ x y))
      (Eq.trans (tensor-cong {M = Idₒ {m}} (≐-refl Idₒ) P0+P1 x y) (Eq.sym (tensor-Id {m} {1} x y)))))

------------------------------------------------------------------------
-- Reading the bottom wires

F T : Bits 1
F = false ∷ []
T = true ∷ []

private
  tensor-++ : (M : Op m) (N : Op n) (x y : Bits m) (u v : Bits n) →
              tensor M N (x ++ u) (y ++ v) ≡ M x y * N u v
  tensor-++ M N []      []      u v = refl
  tensor-++ M N (a ∷ x) (b ∷ y) u v = tensor-++ (λ u′ v′ → M (a ∷ u′) (b ∷ v′)) N x y u v

  ctrl-at : (k : ℕ) (M : Op m) (x y : Bits m) → ctrlOp k M (x ++ F) (y ++ F) ≡ M x y
  ctrl-at k M x y =
    Eq.trans (Eq.cong₂ _+_ (tensor-++ M P₀ x y F F) (tensor-++ (γI k) P₁ x y F F))
      (Eq.trans (Eq.cong₂ _+_ (*-identityʳ (M x y)) (*-zeroʳ _)) (+-identityʳ (M x y)))

-- The control is injective.
ctrl-inj : {s t : Scaled m} → ctrl s ~ ctrl t → s ~ t
ctrl-inj {s = k , M} {l , N} e x y =
  Eq.trans (Eq.cong (γ^ l *_) (Eq.sym (ctrl-at k M x y)))
    (Eq.trans (e (x ++ F) (y ++ F)) (Eq.cong (γ^ k *_) (ctrl-at l N x y)))

------------------------------------------------------------------------
-- A two-level operator on the half where the top wire reads 0

private
  eqB-++ : (x p : Bits m) (u v : Bits n) → eqB (x ++ u) (p ++ v) ≡ (eqB x p ∧ eqB u v)
  eqB-++ []      []      u v = refl
  eqB-++ (a ∷ x) (b ∷ p) u v =
    Eq.trans (Eq.cong (eqᵇ a b ∧_) (eqB-++ x p u v)) (Eq.sym (BoolP.∧-assoc (eqᵇ a b) (eqB x p) (eqB u v)))

  δb-++ : (x y : Bits m) (u v : Bits n) → δb (x ++ u) (y ++ v) ≡ δb x y * δb u v
  δb-++ []          []          u v = Eq.sym (*-identityˡ (δb u v))
  δb-++ (true ∷ x)  (true ∷ y)  u v = δb-++ x y u v
  δb-++ (false ∷ x) (false ∷ y) u v = δb-++ x y u v
  δb-++ (true ∷ x)  (false ∷ y) u v = Eq.sym (*-zeroˡ (δb u v))
  δb-++ (false ∷ x) (true ∷ y)  u v = Eq.sym (*-zeroˡ (δb u v))

  P₀-F : ∀ v → P₀ F v ≡ δb F v
  P₀-F (false ∷ []) = refl
  P₀-F (true ∷ [])  = refl

  P₁-F : ∀ v → P₁ F v ≡ 0#
  P₁-F (false ∷ []) = refl
  P₁-F (true ∷ [])  = refl

  P₀-T : ∀ v → P₀ T v ≡ 0#
  P₀-T (false ∷ []) = refl
  P₀-T (true ∷ [])  = refl

  P₁-T : ∀ v → P₁ T v ≡ δb T v
  P₁-T (false ∷ []) = refl
  P₁-T (true ∷ [])  = refl

  dist : ∀ (α β u v z : 𝔽) → α * (u * z) + β * (v * z) ≡ (α * u + β * v) * z
  dist α β u v z = Eq.sym (Eq.trans (*-distribʳ-+ z (α * u) (β * v))
                            (Eq.cong₂ _+_ (*-assoc α u z) (*-assoc β v z)))

  module Half (B : Blk) (p q : Bits m) where

    -- The rows of the two-level operator, each scaled by z.
    half : ∀ x y z →
           (if eqB x p then a B * (δb p y * z) + b B * (δb q y * z)
            else if eqB x q then c B * (δb p y * z) + d B * (δb q y * z)
            else γ^ k B * (δb x y * z)) ≡ tlOp B p q x y * z
    half x y z = Eq.sym (Eq.trans (ite-* (eqB x p) _ _ z)
      (ite refl (Eq.sym (dist (a B) (b B) (δb p y) (δb q y) z))
        (Eq.trans (ite-* (eqB x q) _ _ z)
          (ite refl (Eq.sym (dist (c B) (d B) (δb p y) (δb q y) z)) (*-assoc (γ^ k B) (δb x y) z)))))

    at : ∀ x y (u v : Bits 1) → tlOp B (p ++ F) (q ++ F) (x ++ u) (y ++ v) ≡ ctrlOp (k B) (tlOp B p q) (x ++ u) (y ++ v)
    at x y (false ∷ []) v =
      Eq.trans (ite (Eq.trans (eqB-++ x p F F) (BoolP.∧-identityʳ (eqB x p)))
                    (Eq.cong₂ _+_ (Eq.cong (a B *_) (δb-++ p y F v)) (Eq.cong (b B *_) (δb-++ q y F v)))
                    (ite (Eq.trans (eqB-++ x q F F) (BoolP.∧-identityʳ (eqB x q)))
                         (Eq.cong₂ _+_ (Eq.cong (c B *_) (δb-++ p y F v)) (Eq.cong (d B *_) (δb-++ q y F v)))
                         (Eq.cong (γ^ k B *_) (δb-++ x y F v))))
        (Eq.trans (half x y (δb F v))
          (Eq.sym (Eq.trans (Eq.cong₂ _+_ (tensor-++ (tlOp B p q) P₀ x y F v) (tensor-++ (γI (k B)) P₁ x y F v))
            (Eq.trans (Eq.cong₂ _+_ (Eq.cong (tlOp B p q x y *_) (P₀-F v)) (Eq.cong (γI (k B) x y *_) (P₁-F v)))
              (Eq.trans (Eq.cong (tlOp B p q x y * δb F v +_) (*-zeroʳ _)) (+-identityʳ _))))))
    at x y (true ∷ []) v =
      Eq.trans (ite (Eq.trans (eqB-++ x p T F) (BoolP.∧-zeroʳ (eqB x p))) refl
                    (ite (Eq.trans (eqB-++ x q T F) (BoolP.∧-zeroʳ (eqB x q))) refl
                         (Eq.cong (γ^ k B *_) (δb-++ x y T v))))
        (Eq.sym (Eq.trans (Eq.cong₂ _+_ (tensor-++ (tlOp B p q) P₀ x y T v) (tensor-++ (γI (k B)) P₁ x y T v))
          (Eq.trans (Eq.cong₂ _+_ (Eq.cong (tlOp B p q x y *_) (P₀-T v)) (Eq.cong (γI (k B) x y *_) (P₁-T v)))
            (Eq.trans (Eq.cong (_+ γI (k B) x y * δb T v) (*-zeroʳ _))
              (Eq.trans (+-identityˡ _) (*-assoc (γ^ k B) (δb x y) (δb T v)))))))

-- On four wires: the two-level operator on two vectors whose top bit is
-- 0 is the control of the four-wire one.
tl-ctrl : (B : Blk) (p q : Bits 4) → tl B (p ++ F) (q ++ F) ~ ctrl (tl B p q)
tl-ctrl B p q =
  ~-reflexive {l = k B} {k B} {M = tlOp B (p ++ F) (q ++ F)} {ctrlOp (k B) (tlOp B p q)} refl go
  where
  go : ∀ x y → tlOp B (p ++ F) (q ++ F) x y ≡ ctrlOp (k B) (tlOp B p q) x y
  go (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ u ∷ []) (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ v ∷ []) =
    Half.at B p q (x₀ ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) (y₀ ∷ y₁ ∷ y₂ ∷ y₃ ∷ []) (u ∷ []) (v ∷ [])

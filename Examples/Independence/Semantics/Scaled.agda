------------------------------------------------------------------------
-- Presentations of groups
--
-- Scaled operators: matrices up to a group of phases
--
-- The gates of all six fragments are r^{−h} times a matrix over
-- Q = ℤ[x]/(x⁴ − p x² − q), r being √d (√2 = ω − ω³ in ℤ[ω], √3 =
-- 2ζ − ζ³ in ℤ[ζ]).  A semantic value is such a pair (h , M), read as
-- M / r^h, and a circuit's value is the product of its gates' — the
-- exponents add.  Two values are compared up to a phase x^k, the
-- exponent k ranging over a predicate P closed under sums and
-- inverses: P k = (k ≡ 0) is the exact matrix semantics of Section 3,
-- and P k = ⊤ its projective quotient (Definition 32), x being a
-- primitive N-th root of unity that generates the global phases.  So
--
--   (h , M) ≈ (h' , M')  iff  r^{h'} M = x^k r^h M'  for some k in P,
--
-- which is transitive because multiplication by r is injective.  Each
-- width has a monoid of values (products in diagram order), and the
-- shift and the embedding into wider circuits are homomorphisms.  The
-- Boolean eqₖ decides whether two values agree up to x^k entry by
-- entry; it is how relations are checked by evaluation, and, being
-- complete, how two values are told apart.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Integer.Base using (ℤ)
open import Data.Nat.Base using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Independence.Semantics.Quartic as Quartic

module Examples.Independence.Semantics.Scaled
  (d : ℕ) (p q : ℤ)
  (r : Quartic.Q p q)
  (r-cancel : ∀ {a b} → Quartic._*_ p q r a ≡ Quartic._*_ p q r b → a ≡ b)
  (N-1 : ℕ)
  (x^N : Quartic._^_ p q (Quartic.x p q) (suc N-1) ≡ Quartic.1q p q)
  where

open import Algebra.Bundles using (Monoid ; CommutativeRing)
import Algebra.Solver.CommutativeMonoid as CMSolver
open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; not ; T)
open import Data.Bool.Properties using (T-∧ ; T-not-≡)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat.Base using (zero ; _<_ ; _/_ ; _%_)
  renaming (_+_ to _+ℕ_ ; _*_ to _*ℕ_)
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n ; m%n<n)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Data.Vec.Base using ([] ; _∷_)
open import Function.Base using (_$_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
open import Relation.Nullary using (does ; yes ; no)
open import Relation.Nullary.Negation using (¬_)

open Quartic p q public
  using (Q ; x ; 1q ; _^_ ; _≟_ ; isCommutativeRing ; commutativeRing ; ⟨_,_,_,_⟩)

open import Examples.Independence.Semantics.Operators d isCommutativeRing public

open CommutativeRing R using (*-assoc ; *-comm ; *-identityˡ ; *-identityʳ)

-- Regrouping products of scalars.
module CMS = CMSolver (CommutativeRing.*-commutativeMonoid R)
open CMS using (solve ; _⊜_ ; _⊕_)

private
  variable
    k l n : ℕ

  open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Powers

^-+ : (a : Q) (m n : ℕ) → a ^ (m +ℕ n) ≡ a ^ m * a ^ n
^-+ a zero    n = Eq.sym (*-identityˡ (a ^ n))
^-+ a (suc m) n = Eq.trans (Eq.cong (a *_) (^-+ a m n)) (Eq.sym (*-assoc a (a ^ m) (a ^ n)))

-- x^{m N} = 1.
x^mN : (m : ℕ) → x ^ (m *ℕ suc N-1) ≡ 1q
x^mN zero    = refl
x^mN (suc m) = begin
  x ^ (suc N-1 +ℕ m *ℕ suc N-1)       ≡⟨ ^-+ x (suc N-1) (m *ℕ suc N-1) ⟩
  x ^ suc N-1 * x ^ (m *ℕ suc N-1)    ≡⟨ Eq.cong₂ _*_ x^N (x^mN m) ⟩
  1q * 1q                             ≡⟨ *-identityˡ 1q ⟩
  1q                                  ∎

-- So x^k depends on k modulo N only.
x^-mod : (k : ℕ) → x ^ k ≡ x ^ (k % suc N-1)
x^-mod k = begin
  x ^ k                                            ≡⟨ Eq.cong (x ^_) (m≡m%n+[m/n]*n k (suc N-1)) ⟩
  x ^ (k % suc N-1 +ℕ (k / suc N-1) *ℕ suc N-1)    ≡⟨ ^-+ x (k % suc N-1) _ ⟩
  x ^ (k % suc N-1) * x ^ ((k / suc N-1) *ℕ suc N-1) ≡⟨ Eq.cong (x ^ (k % suc N-1) *_) (x^mN (k / suc N-1)) ⟩
  x ^ (k % suc N-1) * 1q                           ≡⟨ *-identityʳ _ ⟩
  x ^ (k % suc N-1)                                ∎

-- x^{(N − 1) k} x^k = 1.
x^inv : (k : ℕ) → x ^ (N-1 *ℕ k) * x ^ k ≡ 1q
x^inv k = begin
  x ^ (N-1 *ℕ k) * x ^ k         ≡⟨ Eq.sym (^-+ x (N-1 *ℕ k) k) ⟩
  x ^ (N-1 *ℕ k +ℕ k)            ≡⟨ Eq.cong (x ^_) (ℕP.+-comm (N-1 *ℕ k) k) ⟩
  x ^ (suc N-1 *ℕ k)             ≡⟨ Eq.cong (x ^_) (ℕP.*-comm (suc N-1) k) ⟩
  x ^ (k *ℕ suc N-1)             ≡⟨ x^mN k ⟩
  1q                             ∎

r^-cancel : (h : ℕ) {a b : Q} → r ^ h * a ≡ r ^ h * b → a ≡ b
r^-cancel zero    {a} {b} e =
  Eq.trans (Eq.sym (*-identityˡ a)) (Eq.trans e (*-identityˡ b))
r^-cancel (suc h) {a} {b} e =
  r^-cancel h (r-cancel (Eq.trans (Eq.sym (*-assoc r (r ^ h) a))
                                  (Eq.trans e (*-assoc r (r ^ h) b))))

------------------------------------------------------------------------
-- Values

Sc : ℕ → Set
Sc n = ℕ × Mat n

-- Products in diagram order: s ∙ t is s followed by t.
infixl 7 _∙_
_∙_ : Sc n → Sc n → Sc n
(h , M) ∙ (h' , M') = h +ℕ h' , mulM M' M

εs : Sc n
εs = 0 , idM

-- A value one wire up, and on the bottom wires of a wider circuit.
↑s : Sc n → Sc (suc n)
↑s (h , M) = h , tenM (idM {1}) M

embs : Sc k → Sc (k +ℕ n)
embs {n = n} (h , M) = h , tenM M (idM {n})

ix-up : (M : Mat n) → ix (tenM (idM {1}) M) ≐ up (ix M)
ix-up M = ≐-trans (ix-tenM idM M) (tensor-cong ix-id (≐-refl (ix M)))

ix-emb : (M : Mat k) → ix (tenM M (idM {n})) ≐ emb (ix M)
ix-emb M = ≐-trans (ix-tenM M idM) (tensor-cong (≐-refl (ix M)) ix-id)

private
  scale-≡ : {a b : Q} (M : Op n) → a ≡ b → scale a M ≐ scale b M
  scale-≡ M refl = ≐-refl _

  scale-⊙ : (a b : Q) (M N : Op n) → (scale a M ⊙ scale b N) ≐ scale (a * b) (M ⊙ N)
  scale-⊙ a b M N =
    ≐-trans (scale-⊙ˡ a M (scale b N))
      (≐-trans (scale-cong {c = a} (scale-⊙ʳ b M N)) (scale-scale a b (M ⊙ N)))

------------------------------------------------------------------------
-- Comparing values up to the phases in P

module Phases
  (P : ℕ → Set) (P0 : P 0)
  (P+ : ∀ {k l} → P k → P l → P (k +ℕ l))
  (P⁻ : ∀ {k} → P k → P (N-1 *ℕ k))
  where

  -- A record, so that s and s' can be read off s ≈ s'.
  infix 4 _≈_
  record _≈_ (s s' : Sc n) : Set where
    constructor phased
    field
      phase   : ℕ
      allowed : P phase
      agree   : scale (r ^ proj₁ s') (ix (proj₂ s)) ≐
                scale (x ^ phase * r ^ proj₁ s) (ix (proj₂ s'))

  -- Values with the same exponent and pointwise equal matrices.
  ≐→≈ : {s s' : Sc n} → proj₁ s ≡ proj₁ s' → ix (proj₂ s) ≐ ix (proj₂ s') → s ≈ s'
  ≐→≈ {s = h , M} {h' , M'} refl e =
    phased 0 P0 λ i j → Eq.trans (Eq.cong (r ^ h *_) (e i j))
                              (Eq.cong (_* ix M' i j) (Eq.sym (*-identityˡ (r ^ h))))

  ≈-refl : {s : Sc n} → s ≈ s
  ≈-refl {s = s} = ≐→≈ {s = s} {s} refl (≐-refl (ix (proj₂ s)))

  ≈-sym : {s s' : Sc n} → s ≈ s' → s' ≈ s
  ≈-sym {s = h , M} {h' , M'} (phased k pk e) = phased (N-1 *ℕ k) (P⁻ pk) λ i j → begin
    r ^ h * ix M' i j
      ≡⟨ Eq.sym (*-identityˡ _) ⟩
    1q * (r ^ h * ix M' i j)
      ≡⟨ Eq.cong (_* (r ^ h * ix M' i j)) (Eq.sym (x^inv k)) ⟩
    (x ^ (N-1 *ℕ k) * x ^ k) * (r ^ h * ix M' i j)
      ≡⟨ solve 4 (λ a b c m → (a ⊕ b) ⊕ (c ⊕ m) ⊜ a ⊕ ((b ⊕ c) ⊕ m))
               refl (x ^ (N-1 *ℕ k)) (x ^ k) (r ^ h) (ix M' i j) ⟩
    x ^ (N-1 *ℕ k) * ((x ^ k * r ^ h) * ix M' i j)
      ≡⟨ Eq.cong (x ^ (N-1 *ℕ k) *_) (Eq.sym (e i j)) ⟩
    x ^ (N-1 *ℕ k) * (r ^ h' * ix M i j)
      ≡⟨ Eq.sym (*-assoc (x ^ (N-1 *ℕ k)) (r ^ h') (ix M i j)) ⟩
    (x ^ (N-1 *ℕ k) * r ^ h') * ix M i j ∎

  ≈-trans : {s₁ s₂ s₃ : Sc n} → s₁ ≈ s₂ → s₂ ≈ s₃ → s₁ ≈ s₃
  ≈-trans {s₁ = h₁ , M₁} {h₂ , M₂} {h₃ , M₃} (phased k pk e₁) (phased l pl e₂) =
    phased (k +ℕ l) (P+ pk pl) λ i j → r^-cancel h₂ (begin
      r ^ h₂ * (r ^ h₃ * ix M₁ i j)
        ≡⟨ solve 3 (λ a b m → a ⊕ (b ⊕ m) ⊜ b ⊕ (a ⊕ m))
                 refl (r ^ h₂) (r ^ h₃) (ix M₁ i j) ⟩
      r ^ h₃ * (r ^ h₂ * ix M₁ i j)
        ≡⟨ Eq.cong (r ^ h₃ *_) (e₁ i j) ⟩
      r ^ h₃ * ((x ^ k * r ^ h₁) * ix M₂ i j)
        ≡⟨ solve 4 (λ a b c m → a ⊕ ((b ⊕ c) ⊕ m) ⊜ (b ⊕ c) ⊕ (a ⊕ m))
                 refl (r ^ h₃) (x ^ k) (r ^ h₁) (ix M₂ i j) ⟩
      (x ^ k * r ^ h₁) * (r ^ h₃ * ix M₂ i j)
        ≡⟨ Eq.cong ((x ^ k * r ^ h₁) *_) (e₂ i j) ⟩
      (x ^ k * r ^ h₁) * ((x ^ l * r ^ h₂) * ix M₃ i j)
        ≡⟨ solve 5 (λ a b c e m → (a ⊕ b) ⊕ ((c ⊕ e) ⊕ m) ⊜ e ⊕ (((a ⊕ c) ⊕ b) ⊕ m))
                 refl (x ^ k) (r ^ h₁) (x ^ l) (r ^ h₂) (ix M₃ i j) ⟩
      r ^ h₂ * ((x ^ k * x ^ l * r ^ h₁) * ix M₃ i j)
        ≡⟨ Eq.cong (λ c → r ^ h₂ * ((c * r ^ h₁) * ix M₃ i j)) (Eq.sym (^-+ x k l)) ⟩
      r ^ h₂ * ((x ^ (k +ℕ l) * r ^ h₁) * ix M₃ i j) ∎)

  ∙-cong : {s₁ s₂ t₁ t₂ : Sc n} → s₁ ≈ s₂ → t₁ ≈ t₂ → s₁ ∙ t₁ ≈ s₂ ∙ t₂
  ∙-cong {s₁ = a , M₁} {a' , M₂} {b , N₁} {b' , N₂} (phased k pk e) (phased l pl f) =
    phased (k +ℕ l) (P+ pk pl) $
    ≐-trans (scale-cong {c = r ^ (a' +ℕ b')} (ix-mul N₁ M₁))
    (≐-trans (scale-≡ (ix N₁ ⊙ ix M₁)
               (Eq.trans (^-+ r a' b') (*-comm (r ^ a') (r ^ b'))))
    (≐-trans (≐-sym (scale-⊙ (r ^ b') (r ^ a') (ix N₁) (ix M₁)))
    (≐-trans (⊙-cong f e)
    (≐-trans (scale-⊙ (x ^ l * r ^ b) (x ^ k * r ^ a) (ix N₂) (ix M₂))
    (≐-trans (scale-≡ (ix N₂ ⊙ ix M₂) scalar)
             (scale-cong {c = x ^ (k +ℕ l) * r ^ (a +ℕ b)} (≐-sym (ix-mul N₂ M₂))))))))
    where
    scalar : (x ^ l * r ^ b) * (x ^ k * r ^ a) ≡ x ^ (k +ℕ l) * r ^ (a +ℕ b)
    scalar = begin
      (x ^ l * r ^ b) * (x ^ k * r ^ a)
        ≡⟨ solve 4 (λ xl rb xk ra → (xl ⊕ rb) ⊕ (xk ⊕ ra) ⊜ (xk ⊕ xl) ⊕ (ra ⊕ rb))
                 refl (x ^ l) (r ^ b) (x ^ k) (r ^ a) ⟩
      (x ^ k * x ^ l) * (r ^ a * r ^ b)
        ≡⟨ Eq.sym (Eq.cong₂ _*_ (^-+ x k l) (^-+ r a b)) ⟩
      x ^ (k +ℕ l) * r ^ (a +ℕ b) ∎

  monoid : ℕ → Monoid 0ℓ 0ℓ
  monoid n = record
    { Carrier = Sc n
    ; _≈_ = _≈_
    ; _∙_ = _∙_
    ; ε = εs
    ; isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = record
              { refl  = λ {s} → ≈-refl {s = s}
              ; sym   = λ {s} {s'} → ≈-sym {s = s} {s'}
              ; trans = λ {s} {s'} {s''} → ≈-trans {s₁ = s} {s'} {s''} }
          ; ∙-cong = λ {s} {s'} {t} {t'} → ∙-cong {s₁ = s} {s'} {t} {t'} }
        ; assoc = λ s t u → ≐→≈ {s = (s ∙ t) ∙ u} {s ∙ (t ∙ u)} (ℕP.+-assoc (proj₁ s) (proj₁ t) (proj₁ u))
            (≐-trans (ix-mul (proj₂ u) (mulM (proj₂ t) (proj₂ s)))
            (≐-trans (⊙-cong (≐-refl (ix (proj₂ u))) (ix-mul (proj₂ t) (proj₂ s)))
            (≐-trans (≐-sym (⊙-assoc (ix (proj₂ u)) (ix (proj₂ t)) (ix (proj₂ s))))
            (≐-trans (⊙-cong (≐-sym (ix-mul (proj₂ u) (proj₂ t))) (≐-refl (ix (proj₂ s))))
                     (≐-sym (ix-mul (mulM (proj₂ u) (proj₂ t)) (proj₂ s)))))))
        }
      ; identity =
          (λ s → ≐→≈ {s = εs ∙ s} {s} refl (≐-trans (ix-mul (proj₂ s) (idM {n}))
                            (≐-trans (⊙-cong (≐-refl (ix (proj₂ s))) (ix-id {n}))
                                     (⊙-identityʳ (ix (proj₂ s))))))
        , (λ s → ≐→≈ {s = s ∙ εs} {s} (ℕP.+-identityʳ (proj₁ s))
                     (≐-trans (ix-mul (idM {n}) (proj₂ s))
                     (≐-trans (⊙-cong (ix-id {n}) (≐-refl (ix (proj₂ s))))
                              (⊙-identityˡ (ix (proj₂ s))))))
      }
    }

  ----------------------------------------------------------------------
  -- The shift and the embedding

  ↑s-cong : {s s' : Sc n} → s ≈ s' → ↑s s ≈ ↑s s'
  ↑s-cong {s = h , M} {h' , M'} (phased k pk e) =
    phased k pk $
    ≐-trans (scale-cong {c = r ^ h'} (ix-up M))
    (≐-trans (≐-sym (up-scale (r ^ h') (ix M)))
    (≐-trans (up-cong e)
    (≐-trans (up-scale (x ^ k * r ^ h) (ix M'))
             (scale-cong {c = x ^ k * r ^ h} (≐-sym (ix-up M'))))))

  ↑s-∙ : (s t : Sc n) → ↑s (s ∙ t) ≈ ↑s s ∙ ↑s t
  ↑s-∙ (h , M) (h' , M') =
    ≐→≈ {s = ↑s ((h , M) ∙ (h' , M'))} {↑s (h , M) ∙ ↑s (h' , M')} refl
    (≐-trans (ix-up (mulM M' M))
    (≐-trans (up-cong (ix-mul M' M))
    (≐-trans (≐-sym (up-⊙ (ix M') (ix M)))
    (≐-trans (⊙-cong (≐-sym (ix-up M')) (≐-sym (ix-up M)))
             (≐-sym (ix-mul (tenM (idM {1}) M') (tenM (idM {1}) M)))))))

  ↑s-ε : ↑s (εs {n}) ≈ εs
  ↑s-ε {n} =
    ≐→≈ {s = ↑s (εs {n})} {εs} refl
      (≐-trans (ix-up (idM {n})) (≐-trans (up-cong (ix-id {n}))
               (≐-trans (up-Id {n}) (≐-sym (ix-id {suc n})))))

  embs-cong : {s s' : Sc k} → s ≈ s' → embs {k} {n} s ≈ embs s'
  embs-cong {s = h , M} {h' , M'} (phased k pk e) =
    phased k pk $
    ≐-trans (scale-cong {c = r ^ h'} (ix-emb M))
    (≐-trans (≐-sym (emb-scale (r ^ h') (ix M)))
    (≐-trans (emb-cong e)
    (≐-trans (emb-scale (x ^ k * r ^ h) (ix M'))
             (scale-cong {c = x ^ k * r ^ h} (≐-sym (ix-emb M'))))))

  embs-∙ : (s t : Sc k) → embs {k} {n} (s ∙ t) ≈ embs s ∙ embs t
  embs-∙ {k} {n} (h , M) (h' , M') =
    ≐→≈ {s = embs {k} {n} ((h , M) ∙ (h' , M'))} {embs (h , M) ∙ embs (h' , M')} refl
    (≐-trans (ix-emb {k} {n} (mulM M' M))
    (≐-trans (emb-cong {k} {n} (ix-mul M' M))
    (≐-trans (≐-sym (emb-⊙ {k} {n} (ix M') (ix M)))
    (≐-trans (⊙-cong (≐-sym (ix-emb {k} {n} M')) (≐-sym (ix-emb {k} {n} M)))
             (≐-sym (ix-mul (tenM M' idM) (tenM M idM)))))))

  embs-ε : embs {k} {n} εs ≈ εs
  embs-ε {k} {n} =
    ≐→≈ {s = embs {k} {n} εs} {εs} refl
      (≐-trans (ix-emb {k} {n} idM) (≐-trans (emb-cong {k} {n} (ix-id {k}))
               (≐-trans (emb-id {k} {n}) (≐-sym (ix-id {k +ℕ n})))))

------------------------------------------------------------------------
-- Checking by evaluation

allFin : {m : ℕ} → (Fin m → Bool) → Bool
allFin {zero}  f = true
allFin {suc m} f = f zero ∧ allFin (λ i → f (suc i))

allD : (k : ℕ) → (Digits k → Bool) → Bool
allD zero    f = f []
allD (suc k) f = allFin (λ a → allD k (λ xs → f (a ∷ xs)))

private
  ∧-l : ∀ {a b} → T (a ∧ b) → T a
  ∧-l {true} _ = tt

  ∧-r : ∀ {a b} → T (a ∧ b) → T b
  ∧-r {true} t = t

  ∧-i : ∀ {a b} → T a → T b → T (a ∧ b)
  ∧-i {true} _ t = t

allFin-sound : {m : ℕ} (f : Fin m → Bool) → T (allFin f) → ∀ i → T (f i)
allFin-sound f t zero    = ∧-l t
allFin-sound f t (suc i) = allFin-sound (λ j → f (suc j)) (∧-r {f zero} t) i

allFin-complete : {m : ℕ} (f : Fin m → Bool) → (∀ i → T (f i)) → T (allFin f)
allFin-complete {zero}  f g = tt
allFin-complete {suc m} f g = ∧-i (g zero) (allFin-complete (λ j → f (suc j)) (λ j → g (suc j)))

allD-sound : (k : ℕ) (f : Digits k → Bool) → T (allD k f) → ∀ xs → T (f xs)
allD-sound zero    f t []       = t
allD-sound (suc k) f t (a ∷ xs) =
  allD-sound k (λ ys → f (a ∷ ys)) (allFin-sound _ t a) xs

allD-complete : (k : ℕ) (f : Digits k → Bool) → (∀ xs → T (f xs)) → T (allD k f)
allD-complete zero    f g = g []
allD-complete (suc k) f g =
  allFin-complete _ (λ a → allD-complete k (λ ys → f (a ∷ ys)) (λ ys → g (a ∷ ys)))

private
  dec-sound : (a b : Q) → T (does (a ≟ b)) → a ≡ b
  dec-sound a b t with a ≟ b
  ... | yes e = e

  T-not : (b : Bool) → T b → T (not b) → ⊥
  T-not true  _ ()
  T-not false () _

  dec-complete : (a b : Q) → a ≡ b → T (does (a ≟ b))
  dec-complete a b e with a ≟ b
  ... | yes _ = tt
  ... | no ne = ne e

-- s and s' agree up to x^k, entry by entry.
eqₖ : ℕ → Sc n → Sc n → Bool
eqₖ {n} k (h , M) (h' , M') =
  allD n λ i → allD n λ j →
    does (r ^ h' * ix M i j ≟ (x ^ k * r ^ h) * ix M' i j)

eqₖ-sound : (k : ℕ) (s s' : Sc n) → T (eqₖ k s s') →
            scale (r ^ proj₁ s') (ix (proj₂ s)) ≐ scale (x ^ k * r ^ proj₁ s) (ix (proj₂ s'))
eqₖ-sound {n} k (h , M) (h' , M') t i j =
  dec-sound _ _ (allD-sound n _ (allD-sound n _ t i) j)

eqₖ-complete : (k : ℕ) (s s' : Sc n) →
               scale (r ^ proj₁ s') (ix (proj₂ s)) ≐ scale (x ^ k * r ^ proj₁ s) (ix (proj₂ s')) →
               T (eqₖ k s s')
eqₖ-complete {n} k (h , M) (h' , M') e =
  allD-complete n _ (λ i → allD-complete n _ (λ j → dec-complete _ _ (e i j)))

-- A digit on which f holds, if not all digits fail it.
pick : {m : ℕ} (f : Fin m → Bool) → T (not (allFin (λ i → not (f i)))) →
       Σ (Fin m) (λ i → T (f i))
pick {zero}  f ()
pick {suc m} f t = aux (f zero) refl t
  where
  aux : (b : Bool) → f zero ≡ b →
        T (not (not (f zero) ∧ allFin (λ i → not (f (suc i))))) →
        Σ (Fin (suc m)) (λ i → T (f i))
  aux true  e _  = zero , Eq.subst T (Eq.sym e) tt
  aux false e t' =
    let (i , ti) = pick (λ j → f (suc j))
                     (Eq.subst (λ c → T (not (not c ∧ allFin (λ i → not (f (suc i)))))) e t')
    in suc i , ti

-- s and s' agree up to no phase at all.
apartₖ : Sc n → Sc n → Bool
apartₖ s s' = allFin {suc N-1} (λ i → not (eqₖ (toℕ i) s s'))

module Decide
  (P : ℕ → Set) (P0 : P 0)
  (P+ : ∀ {k l} → P k → P l → P (k +ℕ l))
  (P⁻ : ∀ {k} → P k → P (N-1 *ℕ k))
  where

  open Phases P P0 P+ P⁻

  -- A computed agreement up to x^k, for k in P.
  check : (k : ℕ) → P k → (s s' : Sc n) → T (eqₖ k s s') → s ≈ s'
  check k pk s s' t = phased k pk (eqₖ-sound k s s' t)

  -- Values that agree up to no x^k are not related, whatever P is.
  apart : (s s' : Sc n) → T (apartₖ s s') → ¬ (s ≈ s')
  apart s s' t (phased k _ e) = not-both (eqₖ-complete k' s s' e')
    where
    k' = k % suc N-1
    k'<N : k' < suc N-1
    k'<N = m%n<n k (suc N-1)

    e' : scale (r ^ proj₁ s') (ix (proj₂ s)) ≐ scale (x ^ k' * r ^ proj₁ s) (ix (proj₂ s'))
    e' i j = Eq.trans (e i j) (Eq.cong (λ c → (c * r ^ proj₁ s) * ix (proj₂ s') i j) (x^-mod k))

    i' : Fin (suc N-1)
    i' = fromℕ< k'<N

    not-both : T (eqₖ k' s s') → ⊥
    not-both t' = T-not (eqₖ k' s s') t'
      (Eq.subst (λ j → T (not (eqₖ j s s'))) (toℕ-fromℕ< k'<N)
                (allFin-sound (λ i → not (eqₖ (toℕ i) s s')) t i'))

  -- Agreement up to some phase, found by evaluation, when every phase
  -- is allowed.
  check-some : (∀ k → P k) → (s s' : Sc n) → T (not (apartₖ s s')) → s ≈ s'
  check-some all s s' t = check (toℕ (proj₁ found)) (all _) s s' (proj₂ found)
    where
    found = pick {suc N-1} (λ i → eqₖ (toℕ i) s s') t

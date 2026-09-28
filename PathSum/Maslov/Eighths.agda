------------------------------------------------------------------------
-- Presentations of groups
--
-- Sums of eighth roots of unity, evaluated by computation
--
-- The phase of a Clifford+T circuit along a path is ⅛ times an integer
-- (⅛ = 2^(M-3), the numerator of 1/8 over 2^M), so its amplitudes are
-- sums of eighth roots of unity ζ^(⅛ j).  Four of them, u r = ζ^(⅛ r)
-- for r < 4, are enough: ζ^(⅛ (j+4)) = -ζ^(⅛ j) and ζ^(⅛·8) = 1.  So
-- such a sum is an integer combination of u 0, …, u 3, and this module
-- lets Agda compute that combination instead of reasoning about the
-- roots: a formal combination is a Lin (four integers, with meaning
-- ⟦_⟧ˡ); unitˡ j is the combination for ζ^(⅛ j), computed from j
-- modulo 8 (unit-ok); and Σˡ sums combinations over the assignments to
-- k path variables the way Σᴮ sums amplitudes (Σᴮ-ˡ).  When the phase
-- along each path is ⅛ times an integer computed from Booleans, the
-- sum over the paths is ⟦ l ⟧ˡ for a Lin l that Agda computes as soon
-- as the Booleans are known, so two such sums are compared by
-- comparing two quadruples of integers, by refl.
-- PathSum.Maslov.Gate4 reads the relative-phase Toffoli-4 gate this
-- way: its phases include odd multiples of ¼, whose sums over one path
-- variable are not 0 or 2 but 1 ± i, and whose cancellation across
-- the four variables is a fact about eighth roots of unity rather than
-- an identity between Booleans.
--
-- The roots themselves are never compared: u r stays symbolic (M₀ is a
-- variable), only the integer coefficients are computed.  Σᴮ-ˡ asks the
-- summand to read the path only through its values, since Σᴮ and Σˡ
-- each end their recursion at an empty assignment of their own, and
-- two distinct functions out of Fin 0 are not definitionally equal.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Maslov.Eighths (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using
  (ℤ; 0ℤ; 1ℤ; +_; -[1+_]; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (divides)
open import Data.Integer.Properties using
  (+-comm; *-comm; *-identityʳ; *-distribˡ-+; *-distribʳ-+; *-assoc;
   pos-*)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (_<_; s≤s)
  renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Nat.DivMod using (_%_; _/_; m≡m%n+[m/n]*n; m%n<n)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Compose.Sum M₀ using (zpow-≡)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; -ᴬ_; _·ᴬ_; _≐_; extend; Σᴮ; zpow; zpow-anti; N)
open import PathSum.Order M using (pow-+)
open import PathSum.Reduction M using (⅛; ½)
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; mod-N; ≡ᴺ-sym; zpow-≡ᴺ)
open import PathSum.Toffoli.Arith M₀ using (four-T)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  variable
    k : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- The roots

-- u r = ζ^(⅛ r).

u : ℕ → Amp
u r = zpow (⅛ * + r)

-- ⅛ · 8 is N, and ⅛ · 4 is ½, so ζ^(⅛ (4 + r)) = -ζ^(⅛ r).

⅛·8 : ⅛ * (+ 8) ≡ + N
⅛·8 = trans (*-comm ⅛ (+ 8)) (pow-+ 3 M₀)

⅛·4 : ⅛ * (+ 4) ≡ ½
⅛·4 = trans (four-T 1ℤ) (*-identityʳ ½)

zpow-⅛+4 : ∀ r → zpow (⅛ * + (4 ℕ+ r)) ≐ -ᴬ zpow (⅛ * + r)
zpow-⅛+4 r i = trans
  (zpow-≡ (trans (*-distribˡ-+ ⅛ (+ 4) (+ r))
                 (trans (cong (_+ ⅛ * + r) ⅛·4) (+-comm ½ (⅛ * + r)))) i)
  (zpow-anti (⅛ * + r) i)


------------------------------------------------------------------------
-- Formal combinations of the roots

record Lin : Set where
  constructor lin
  field
    l₀ l₁ l₂ l₃ : ℤ

-- Its meaning: l₀ u 0 + l₁ u 1 + l₂ u 2 + l₃ u 3.

⟦_⟧ˡ : Lin → Amp
⟦ lin a b c d ⟧ˡ = a ·ᴬ u 0 +ᴬ b ·ᴬ u 1 +ᴬ c ·ᴬ u 2 +ᴬ d ·ᴬ u 3

0ˡ : Lin
0ˡ = lin 0ℤ 0ℤ 0ℤ 0ℤ

infixl 6 _+ˡ_
infixr 7 _·ˡ_

_+ˡ_ : Lin → Lin → Lin
lin a b c d +ˡ lin a′ b′ c′ d′ = lin (a + a′) (b + b′) (c + c′) (d + d′)

_·ˡ_ : ℤ → Lin → Lin
m ·ˡ lin a b c d = lin (m * a) (m * b) (m * c) (m * d)

-- The operations mean what they should.

⟦0ˡ⟧ : ⟦ 0ˡ ⟧ˡ ≐ 0ᴬ
⟦0ˡ⟧ i = refl

private
  shuffle : ∀ a a′ b b′ c c′ d d′ →
            (a + a′) + (b + b′) + (c + c′) + (d + d′) ≡
            (a + b + c + d) + (a′ + b′ + c′ + d′)
  shuffle = solve 8 (λ a a′ b b′ c c′ d d′ →
    (a :+ a′) :+ (b :+ b′) :+ (c :+ c′) :+ (d :+ d′)
    := (a :+ b :+ c :+ d) :+ (a′ :+ b′ :+ c′ :+ d′)) refl

  factor4 : ∀ m a b c d → m * a + m * b + m * c + m * d ≡ m * (a + b + c + d)
  factor4 = solve 5 (λ m a b c d →
    m :* a :+ m :* b :+ m :* c :+ m :* d := m :* (a :+ b :+ c :+ d)) refl

⟦+ˡ⟧ : ∀ l l′ → ⟦ l +ˡ l′ ⟧ˡ ≐ ⟦ l ⟧ˡ +ᴬ ⟦ l′ ⟧ˡ
⟦+ˡ⟧ (lin a b c d) (lin a′ b′ c′ d′) i = trans
  (cong₂ _+_ (cong₂ _+_ (cong₂ _+_ (*-distribʳ-+ (u 0 i) a a′)
                                   (*-distribʳ-+ (u 1 i) b b′))
                        (*-distribʳ-+ (u 2 i) c c′))
             (*-distribʳ-+ (u 3 i) d d′))
  (shuffle (a * u 0 i) (a′ * u 0 i) (b * u 1 i) (b′ * u 1 i)
           (c * u 2 i) (c′ * u 2 i) (d * u 3 i) (d′ * u 3 i))

⟦·ˡ⟧ : ∀ m l → ⟦ m ·ˡ l ⟧ˡ ≐ m ·ᴬ ⟦ l ⟧ˡ
⟦·ˡ⟧ m (lin a b c d) i = trans
  (cong₂ _+_ (cong₂ _+_ (cong₂ _+_ (*-assoc m a (u 0 i))
                                   (*-assoc m b (u 1 i)))
                        (*-assoc m c (u 2 i)))
             (*-assoc m d (u 3 i)))
  (factor4 m (a * u 0 i) (b * u 1 i) (c * u 2 i) (d * u 3 i))


------------------------------------------------------------------------
-- One root

-- ζ^(⅛ r) for r < 8.

table : ℕ → Lin
table 0 = lin 1ℤ 0ℤ 0ℤ 0ℤ
table 1 = lin 0ℤ 1ℤ 0ℤ 0ℤ
table 2 = lin 0ℤ 0ℤ 1ℤ 0ℤ
table 3 = lin 0ℤ 0ℤ 0ℤ 1ℤ
table 4 = lin (- 1ℤ) 0ℤ 0ℤ 0ℤ
table 5 = lin 0ℤ (- 1ℤ) 0ℤ 0ℤ
table 6 = lin 0ℤ 0ℤ (- 1ℤ) 0ℤ
table 7 = lin 0ℤ 0ℤ 0ℤ (- 1ℤ)
table _ = 0ˡ

private
  pick₀ : ∀ p q r s → 1ℤ * p + 0ℤ * q + 0ℤ * r + 0ℤ * s ≡ p
  pick₀ = solve 4 (λ p q r s →
    con 1ℤ :* p :+ con 0ℤ :* q :+ con 0ℤ :* r :+ con 0ℤ :* s := p) refl

  pick₁ : ∀ p q r s → 0ℤ * p + 1ℤ * q + 0ℤ * r + 0ℤ * s ≡ q
  pick₁ = solve 4 (λ p q r s →
    con 0ℤ :* p :+ con 1ℤ :* q :+ con 0ℤ :* r :+ con 0ℤ :* s := q) refl

  pick₂ : ∀ p q r s → 0ℤ * p + 0ℤ * q + 1ℤ * r + 0ℤ * s ≡ r
  pick₂ = solve 4 (λ p q r s →
    con 0ℤ :* p :+ con 0ℤ :* q :+ con 1ℤ :* r :+ con 0ℤ :* s := r) refl

  pick₃ : ∀ p q r s → 0ℤ * p + 0ℤ * q + 0ℤ * r + 1ℤ * s ≡ s
  pick₃ = solve 4 (λ p q r s →
    con 0ℤ :* p :+ con 0ℤ :* q :+ con 0ℤ :* r :+ con 1ℤ :* s := s) refl

  neg₀ : ∀ p q r s → (- 1ℤ) * p + 0ℤ * q + 0ℤ * r + 0ℤ * s ≡ - p
  neg₀ = solve 4 (λ p q r s →
    con (- 1ℤ) :* p :+ con 0ℤ :* q :+ con 0ℤ :* r :+ con 0ℤ :* s := :- p)
    refl

  neg₁ : ∀ p q r s → 0ℤ * p + (- 1ℤ) * q + 0ℤ * r + 0ℤ * s ≡ - q
  neg₁ = solve 4 (λ p q r s →
    con 0ℤ :* p :+ con (- 1ℤ) :* q :+ con 0ℤ :* r :+ con 0ℤ :* s := :- q)
    refl

  neg₂ : ∀ p q r s → 0ℤ * p + 0ℤ * q + (- 1ℤ) * r + 0ℤ * s ≡ - r
  neg₂ = solve 4 (λ p q r s →
    con 0ℤ :* p :+ con 0ℤ :* q :+ con (- 1ℤ) :* r :+ con 0ℤ :* s := :- r)
    refl

  neg₃ : ∀ p q r s → 0ℤ * p + 0ℤ * q + 0ℤ * r + (- 1ℤ) * s ≡ - s
  neg₃ = solve 4 (λ p q r s →
    con 0ℤ :* p :+ con 0ℤ :* q :+ con 0ℤ :* r :+ con (- 1ℤ) :* s := :- s)
    refl

table-ok : ∀ r → r < 8 → ⟦ table r ⟧ˡ ≐ zpow (⅛ * + r)
table-ok 0 _ i = pick₀ (u 0 i) (u 1 i) (u 2 i) (u 3 i)
table-ok 1 _ i = pick₁ (u 0 i) (u 1 i) (u 2 i) (u 3 i)
table-ok 2 _ i = pick₂ (u 0 i) (u 1 i) (u 2 i) (u 3 i)
table-ok 3 _ i = pick₃ (u 0 i) (u 1 i) (u 2 i) (u 3 i)
table-ok 4 _ i =
  trans (neg₀ (u 0 i) (u 1 i) (u 2 i) (u 3 i)) (sym (zpow-⅛+4 0 i))
table-ok 5 _ i =
  trans (neg₁ (u 0 i) (u 1 i) (u 2 i) (u 3 i)) (sym (zpow-⅛+4 1 i))
table-ok 6 _ i =
  trans (neg₂ (u 0 i) (u 1 i) (u 2 i) (u 3 i)) (sym (zpow-⅛+4 2 i))
table-ok 7 _ i =
  trans (neg₃ (u 0 i) (u 1 i) (u 2 i) (u 3 i)) (sym (zpow-⅛+4 3 i))
table-ok (suc (suc (suc (suc (suc (suc (suc (suc r))))))))
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))

-- Any root: by the exponent modulo 8.

unitˡ : ℤ → Lin
unitˡ (+ n)    = table (n % 8)
unitˡ -[1+ n ] = table ((7 ℕ* suc n) % 8)

private
  collect : ∀ t a q → t * (a + q * (+ 8)) - t * a ≡ q * (t * (+ 8))
  collect = solve 3 (λ t a q →
    t :* (a :+ q :* con (+ 8)) :- t :* a := q :* (t :* con (+ 8))) refl

  seven : ∀ t s → t * ((+ 7) * s) - t * (- s) ≡ s * (t * (+ 8))
  seven = solve 2 (λ t s →
    t :* (con (+ 7) :* s) :- t :* (:- s) := s :* (t :* con (+ 8))) refl

-- ⅛ n and ⅛ (n mod 8) differ by ⅛ · 8 (n div 8) = N (n div 8).

mod8 : ∀ n → ⅛ * + n ≡ᴺ ⅛ * + (n % 8)
mod8 n = mod-N (divides (+ (n / 8))
  (trans (cong (λ m → ⅛ * + m - ⅛ * + (n % 8)) (m≡m%n+[m/n]*n n 8))
    (trans (cong (λ B → ⅛ * (+ (n % 8) + B) - ⅛ * + (n % 8))
                 (pos-* (n / 8) 8))
      (trans (collect ⅛ (+ (n % 8)) (+ (n / 8)))
             (cong (λ v → + (n / 8) * v) ⅛·8)))))

-- -(n+1) ≡ 7 (n+1) modulo 8.

neg8 : ∀ n → ⅛ * + (7 ℕ* suc n) ≡ᴺ ⅛ * -[1+ n ]
neg8 n = mod-N (divides (+ suc n)
  (trans (cong (λ B → ⅛ * B - ⅛ * -[1+ n ]) (pos-* 7 (suc n)))
    (trans (seven ⅛ (+ suc n)) (cong (λ v → + suc n * v) ⅛·8))))

unit-ok : ∀ j → ⟦ unitˡ j ⟧ˡ ≐ zpow (⅛ * j)
unit-ok (+ n) =
  table-ok (n % 8) (m%n<n n 8) ∙ zpow-≡ᴺ (≡ᴺ-sym (mod8 n))
unit-ok -[1+ n ] =
  table-ok ((7 ℕ* suc n) % 8) (m%n<n (7 ℕ* suc n) 8)
  ∙ zpow-≡ᴺ (≡ᴺ-sym (mod8 (7 ℕ* suc n)))
  ∙ zpow-≡ᴺ (neg8 n)


------------------------------------------------------------------------
-- Sums over paths

-- Σᴮ, for combinations.

Σˡ : ((Fin k → Bool) → Lin) → Lin
Σˡ {k = 0}     f = f (λ ())
Σˡ {k = suc k} f =
  Σˡ (λ g → f (extend true g)) +ˡ Σˡ (λ g → f (extend false g))

-- It respects pointwise equality of summands.

Σˡ-cong : {f g : (Fin k → Bool) → Lin} → (∀ y → f y ≡ g y) → Σˡ f ≡ Σˡ g
Σˡ-cong {k = 0}     h = h _
Σˡ-cong {k = suc k} h = cong₂ _+ˡ_ (Σˡ-cong (λ y → h (extend true y)))
                                   (Σˡ-cong (λ y → h (extend false y)))

-- A summand that reads the path only through its values.

Respectsᴮ : ((Fin k → Bool) → ℤ) → Set
Respectsᴮ {k} f = ∀ {g h : Fin k → Bool} → (∀ i → g i ≡ h i) → f g ≡ f h

-- Extending two paths that agree gives two paths that agree.

extend-≗ : ∀ b {g h : Fin k → Bool} → (∀ i → g i ≡ h i) →
           ∀ i → extend b g i ≡ extend b h i
extend-≗ b g≗h zero    = refl
extend-≗ b g≗h (suc i) = g≗h i

-- The sum over the paths of ζ^(⅛ f(y)) is the meaning of the sum of
-- the combinations.

Σᴮ-ˡ : (f : (Fin k → Bool) → ℤ) → Respectsᴮ f →
       Σᴮ (λ y → zpow (⅛ * f y)) ≐ ⟦ Σˡ (λ y → unitˡ (f y)) ⟧ˡ
Σᴮ-ˡ {k = 0} f rf =
  zpow-≡ (cong (⅛ *_) (rf (λ ()))) ∙ ≐-sym (unit-ok (f _))
Σᴮ-ˡ {k = suc k} f rf i = trans
  (cong₂ _+_ (Σᴮ-ˡ (λ g → f (extend true g))
                   (λ g≗h → rf (extend-≗ true g≗h)) i)
             (Σᴮ-ˡ (λ g → f (extend false g))
                   (λ g≗h → rf (extend-≗ false g≗h)) i))
  (sym (⟦+ˡ⟧ (Σˡ (λ g → unitˡ (f (extend true g))))
             (Σˡ (λ g → unitˡ (f (extend false g)))) i))

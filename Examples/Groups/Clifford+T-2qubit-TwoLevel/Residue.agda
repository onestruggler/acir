------------------------------------------------------------------------
-- Presentations of groups
--
-- Residues in ℤ[ω] modulo powers of δ.
--
-- Since δ⁴ = 2 u for a unit u, the residue of x modulo δʲ (j ≤ 4) is
-- determined by x modulo 2, i.e. by its parity vector: the parities of
-- its four coordinates, an element of 𝔽₂[ω]/(ω⁴ + 1).  The parity
-- vector is a ring homomorphism, so facts about residues reduce to
-- finitely many computations with parity vectors, which allB checks
-- by enumeration.  Divisibility is then witnessed through a g with
-- δʲ g = 2: if 2 divides x g, then δʲ divides x.
--
-- In particular (Lemma 2.11), an odd x is ≡ ωᵐ (mod δ³), where m is
-- the position of the coordinate whose parity differs from the three
-- others; and two odd u, v satisfy ωᶻ u ≡ v (mod δ³) for z = zOf u v.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Residue where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _∨_ ; _xor_ ; if_then_else_ ; T)
open import Data.Unit.Base using (tt)
import Data.Nat.Properties as ℕP
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
import Data.Integer.Solver as ℤSolver

open import Quantum.Synthesis.Ring using (Omega)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring

private
  module ℤS = ℤSolver.+-*-Solver

  cong₄ : ∀ {A B C E F : Set} (f : A → B → C → E → F) {a a′ b b′ c c′ e e′} →
          a ≡ a′ → b ≡ b′ → c ≡ c′ → e ≡ e′ → f a b c e ≡ f a′ b′ c′ e′
  cong₄ f refl refl refl refl = refl

------------------------------------------------------------------------
-- Deciding statements about boolean vectors by enumeration

allB : (n : ℕ) → (Vec Bool n → Bool) → Bool
allB zero f = f []
allB (suc n) f = allB n (λ v → f (true ∷ v)) ∧ allB n (λ v → f (false ∷ v))

private
  ∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧-l {true} _ = refl

  ∧-r : ∀ {a b} → a ∧ b ≡ true → b ≡ true
  ∧-r {true} h = h

allB-sound : ∀ n (f : Vec Bool n → Bool) → allB n f ≡ true → ∀ v → f v ≡ true
allB-sound zero f h [] = h
allB-sound (suc n) f h (true ∷ v) = allB-sound n (λ v → f (true ∷ v)) (∧-l h) v
allB-sound (suc n) f h (false ∷ v) = allB-sound n (λ v → f (false ∷ v)) (∧-r {allB n (λ v → f (true ∷ v))} h) v

------------------------------------------------------------------------
-- Parity vectors: 𝔽₂[ω]/(ω⁴ + 1)

record P4 : Set where
  constructor ⟨_,_,_,_⟩
  field
    pa pb pc pd : Bool

open P4 public

infixl 6 _⊕_
infixl 7 _⊗_

_⊕_ : P4 → P4 → P4
⟨ a , b , c , d ⟩ ⊕ ⟨ a′ , b′ , c′ , d′ ⟩ = ⟨ a xor a′ , b xor b′ , c xor c′ , d xor d′ ⟩

-- The product of ℤ[ω] modulo 2 (EucDomain's formula, signs dropped).
_⊗_ : P4 → P4 → P4
⟨ a , b , c , d ⟩ ⊗ ⟨ a′ , b′ , c′ , d′ ⟩ =
  ⟨ (((a ∧ d′) xor (b ∧ c′)) xor (c ∧ b′)) xor (d ∧ a′)
  , (((b ∧ d′) xor (c ∧ c′)) xor (d ∧ b′)) xor (a ∧ a′)
  , (((c ∧ d′) xor (d ∧ c′)) xor (a ∧ b′)) xor (b ∧ a′)
  , (((d ∧ d′) xor (a ∧ c′)) xor (b ∧ b′)) xor (c ∧ a′) ⟩

𝟘 𝟙 : P4
𝟘 = ⟨ false , false , false , false ⟩
𝟙 = ⟨ true , true , true , true ⟩

-- Equality, as a test.
infix 4 _==_

_==_ : P4 → P4 → Bool
⟨ a , b , c , d ⟩ == ⟨ a′ , b′ , c′ , d′ ⟩ = eqb a a′ ∧ eqb b b′ ∧ eqb c c′ ∧ eqb d d′
  where
  eqb : Bool → Bool → Bool
  eqb x y = not (x xor y)

==-sound : ∀ P P′ → (P == P′) ≡ true → P ≡ P′
==-sound ⟨ a , b , c , d ⟩ ⟨ a′ , b′ , c′ , d′ ⟩ h =
  cong₄ ⟨_,_,_,_⟩ (e a a′ (∧-l h)) (e b b′ (∧-l (∧-r {x a a′} h)))
                  (e c c′ (∧-l (∧-r {x b b′} (∧-r {x a a′} h))))
                  (e d d′ (∧-r {x c c′} (∧-r {x b b′} (∧-r {x a a′} h))))
  where
  x : Bool → Bool → Bool
  x p q = not (p xor q)
  e : ∀ p q → x p q ≡ true → p ≡ q
  e true  true  _ = refl
  e false false _ = refl

-- The δ-residue: the parity of the sum of the coordinates.
oddP : P4 → Bool
oddP ⟨ a , b , c , d ⟩ = ((a xor b) xor c) xor d

------------------------------------------------------------------------
-- The parity vector of an element of ℤ[ω]

par : Z → P4
par (Omega a b c d) = ⟨ oddℤ a , oddℤ b , oddℤ c , oddℤ d ⟩

par-+ : ∀ x y → par (x ZR.+ y) ≡ par x ⊕ par y
par-+ (Omega a b c d) (Omega a′ b′ c′ d′) = cong₄ ⟨_,_,_,_⟩ (oddℤ-+ a a′) (oddℤ-+ b b′) (oddℤ-+ c c′) (oddℤ-+ d d′)

par-neg : ∀ x → par (ZR.- x) ≡ par x
par-neg (Omega a b c d) = cong₄ ⟨_,_,_,_⟩ (oddℤ-neg a) (oddℤ-neg b) (oddℤ-neg c) (oddℤ-neg d)

par-- : ∀ x y → par (x ZR.- y) ≡ par x ⊕ par y
par-- x y = trans (par-+ x (ZR.- y)) (cong (par x ⊕_) (par-neg y))

private
  -- The parity of p + q + r + s and of p + q + r - s.
  odd4 : ∀ p q r s → oddℤ (p ℤ.+ q ℤ.+ r ℤ.+ s) ≡ ((oddℤ p xor oddℤ q) xor oddℤ r) xor oddℤ s
  odd4 p q r s = trans (oddℤ-+ (p ℤ.+ q ℤ.+ r) s) (cong (_xor oddℤ s)
                   (trans (oddℤ-+ (p ℤ.+ q) r) (cong (_xor oddℤ r) (oddℤ-+ p q))))

  odd-* : ∀ x y → oddℤ (x ℤ.* y) ≡ oddℤ x ∧ oddℤ y
  odd-* = oddℤ-*

par-* : ∀ x y → par (x ZR.* y) ≡ par x ⊗ par y
par-* (Omega a b c d) (Omega a′ b′ c′ d′) = cong₄ ⟨_,_,_,_⟩
  (trans (odd4 (a ℤ.* d′) (b ℤ.* c′) (c ℤ.* b′) (d ℤ.* a′))
         (cong₄ (λ p q r s → ((p xor q) xor r) xor s) (odd-* a d′) (odd-* b c′) (odd-* c b′) (odd-* d a′)))
  (trans (odd4 (b ℤ.* d′) (c ℤ.* c′) (d ℤ.* b′) (ℤ.- (a ℤ.* a′)))
         (cong₄ (λ p q r s → ((p xor q) xor r) xor s) (odd-* b d′) (odd-* c c′) (odd-* d b′)
                (trans (oddℤ-neg (a ℤ.* a′)) (odd-* a a′))))
  (trans (odd4 (c ℤ.* d′) (d ℤ.* c′) (ℤ.- (a ℤ.* b′)) (ℤ.- (b ℤ.* a′)))
         (cong₄ (λ p q r s → ((p xor q) xor r) xor s) (odd-* c d′) (odd-* d c′)
                (trans (oddℤ-neg (a ℤ.* b′)) (odd-* a b′)) (trans (oddℤ-neg (b ℤ.* a′)) (odd-* b a′))))
  (trans (odd4 (d ℤ.* d′) (ℤ.- (a ℤ.* c′)) (ℤ.- (b ℤ.* b′)) (ℤ.- (c ℤ.* a′)))
         (cong₄ (λ p q r s → ((p xor q) xor r) xor s) (odd-* d d′)
                (trans (oddℤ-neg (a ℤ.* c′)) (odd-* a c′)) (trans (oddℤ-neg (b ℤ.* b′)) (odd-* b b′))
                (trans (oddℤ-neg (c ℤ.* a′)) (odd-* c a′))))

-- oddᶻ is the δ-residue of the parity vector.
oddP-par : ∀ x → oddP (par x) ≡ oddᶻ x
oddP-par (Omega a b c d) = sym (odd4 a b c d)

------------------------------------------------------------------------
-- Divisibility by δʲ

infix 4 _∣_

-- (A record, so that e and x are determined by its type.)
record _∣_ (e x : Z) : Set where
  constructor _,_
  field
    quot    : Z
    quot-eq : x ≡ e ZR.* quot

-- δ², δ³, and g with δʲ g = 2.
δ²ᶻ δ³ᶻ g2 g3 : Z
δ²ᶻ = Omega (+ 0) (+ 1) (+ 2) (+ 1)
δ³ᶻ = Omega (+ 1) (+ 3) (+ 3) (+ 1)
g2 = Omega -[1+ 1 ] (+ 1) (+ 0) -[1+ 0 ]
g3 = Omega -[1+ 0 ] -[1+ 0 ] (+ 2) -[1+ 1 ]

δ²g2 : δ²ᶻ ZR.* g2 ≡ 2ᶻ
δ²g2 = refl

δ³g3 : δ³ᶻ ZR.* g3 ≡ 2ᶻ
δ³g3 = refl

δ²≡ : δ²ᶻ ≡ δᶻ ZR.* δᶻ
δ²≡ = refl

δ³≡ : δ³ᶻ ≡ δᶻ ZR.* δ²ᶻ
δ³≡ = refl

private
  -- 2 y, componentwise.
  two*≡ : ∀ p q r s → 2ᶻ ZR.* Omega p q r s ≡ Omega (p ℤ.+ p) (q ℤ.+ q) (r ℤ.+ r) (s ℤ.+ s)
  two*≡ p q r s = cong₄ Omega
    (ℤS.solve 4 (λ p q r s → con (+ 0) :* s :+ con (+ 0) :* r :+ con (+ 0) :* q :+ con (+ 2) :* p := p :+ p) refl p q r s)
    (ℤS.solve 4 (λ p q r s → con (+ 0) :* s :+ con (+ 0) :* r :+ con (+ 2) :* q :+ :- (con (+ 0) :* p) := q :+ q) refl p q r s)
    (ℤS.solve 4 (λ p q r s → con (+ 0) :* s :+ con (+ 2) :* r :+ :- (con (+ 0) :* q) :+ :- (con (+ 0) :* p) := r :+ r) refl p q r s)
    (ℤS.solve 4 (λ p q r s → con (+ 2) :* s :+ :- (con (+ 0) :* r) :+ :- (con (+ 0) :* q) :+ :- (con (+ 0) :* p) := s :+ s) refl p q r s)
    where open ℤS using (_:+_ ; _:*_ ; :-_ ; _:=_ ; con)

  -- Cancelling 2.
  two-cancel : ∀ x y → 2ᶻ ZR.* x ≡ 2ᶻ ZR.* y → x ≡ y
  two-cancel (Omega p q r s) (Omega p′ q′ r′ s′) eq =
    cong₄ Omega (half (cong ca eq′)) (half (cong cb eq′)) (half (cong cc eq′)) (half (cong cd eq′))
    where
    open ℤS using (_:+_ ; _:*_ ; _:=_ ; con)
    eq′ = trans (sym (two*≡ p q r s)) (trans eq (two*≡ p′ q′ r′ s′))
    ca cb cc cd : Z → ℤ
    ca (Omega x _ _ _) = x
    cb (Omega _ x _ _) = x
    cc (Omega _ _ x _) = x
    cd (Omega _ _ _ x) = x
    half : ∀ {x y} → x ℤ.+ x ≡ y ℤ.+ y → x ≡ y
    half {x} {y} h = ℤP.*-cancelˡ-≡ (+ 2) x y
      (trans (ℤS.solve 1 (λ x → con (+ 2) :* x := x :+ x) refl x)
             (trans h (ℤS.solve 1 (λ y → y :+ y := con (+ 2) :* y) refl y)))

  -- A vector of even coordinates is 2 y.
  halve : ∀ x → par x ≡ 𝟘 → ∃ λ y → x ≡ 2ᶻ ZR.* y
  halve (Omega a b c d) h with evenℤ-half a (cong pa h) | evenℤ-half b (cong pb h)
                             | evenℤ-half c (cong pc h) | evenℤ-half d (cong pd h)
  ... | a′ , ea | b′ , eb | c′ , ec | d′ , ed =
    Omega a′ b′ c′ d′ , trans (cong₄ Omega ea eb ec ed) (sym (two*≡ a′ b′ c′ d′))

-- x (y z) = y (x z).
*-swap : ∀ x y z → x ZR.* (y ZR.* z) ≡ y ZR.* (x ZR.* z)
*-swap x y z = trans (sym (ZR.*-assoc x y z)) (trans (cong (ZR._* z) (ZR.*-comm x y)) (ZR.*-assoc y x z))

-- If e g = 2 and x g is even, then e divides x.
div-intro : (e g x : Z) → e ZR.* g ≡ 2ᶻ → par (x ZR.* g) ≡ 𝟘 → e ∣ x
div-intro e g x eg ev = go (halve (x ZR.* g) ev)
  where
  open ≡-Reasoning
  go : (∃ λ y → x ZR.* g ≡ 2ᶻ ZR.* y) → e ∣ x
  go (y , xg) = y , two-cancel x (e ZR.* y) (begin
    2ᶻ ZR.* x               ≡⟨ ZR.*-comm 2ᶻ x ⟩
    x ZR.* 2ᶻ               ≡⟨ cong (x ZR.*_) (sym eg) ⟩
    x ZR.* (e ZR.* g)       ≡⟨ *-swap x e g ⟩
    e ZR.* (x ZR.* g)       ≡⟨ cong (e ZR.*_) xg ⟩
    e ZR.* (2ᶻ ZR.* y)      ≡⟨ *-swap e 2ᶻ y ⟩
    2ᶻ ZR.* (e ZR.* y)      ∎)

-- Divisibility in sums, differences and multiples.
∣-+ : ∀ {e x y} → e ∣ x → e ∣ y → e ∣ (x ZR.+ y)
∣-+ {e} (a , refl) (b , refl) = a ZR.+ b , sym (ZR.distribˡ e a b)

∣-neg : ∀ {e x} → e ∣ x → e ∣ (ZR.- x)
∣-neg {e} (a , refl) = ZR.- a , ZS.solve 2 (λ e a → :- (e :* a) := e :* (:- a)) refl e a
  where open ZS using (_:*_ ; :-_ ; _:=_)

∣-- : ∀ {e x y} → e ∣ x → e ∣ y → e ∣ (x ZR.- y)
∣-- {e} {x} {y} dx dy = ∣-+ {e} {x} {ZR.- y} dx (∣-neg {e} {y} dy)

∣-* : ∀ {e x} c → e ∣ x → e ∣ (c ZR.* x)
∣-* {e} c (a , refl) = c ZR.* a , *-swap c e a
  where open ZS using (_:*_ ; _:=_)

∣-refl : ∀ e → e ∣ e
∣-refl e = ZR.1# , sym (ZR.*-identityʳ e)

------------------------------------------------------------------------
-- Odd elements modulo δ³

-- The position of the coordinate whose parity differs from the others:
-- d ↦ 0, c ↦ 1, b ↦ 2, a ↦ 3.
mP : P4 → ℕ
mP ⟨ a , b , c , d ⟩ = if not (a xor b) then (if not (a xor c) then 0 else 1)
                       else (if not (a xor c) then 2 else 3)

-- (m − l) mod 4, for m, l < 4.
sub4 : ℕ → ℕ → ℕ
sub4 0 0 = 0
sub4 0 1 = 3
sub4 0 2 = 2
sub4 0 3 = 1
sub4 1 0 = 1
sub4 1 1 = 0
sub4 1 2 = 3
sub4 1 3 = 2
sub4 2 0 = 2
sub4 2 1 = 1
sub4 2 2 = 0
sub4 2 3 = 3
sub4 3 0 = 3
sub4 3 1 = 2
sub4 3 2 = 1
sub4 3 3 = 0
sub4 _ _ = 0

-- The exponent of the syllable: ωᶻ u ≡ v (mod δ³).
zP : P4 → P4 → ℕ
zP P P′ = sub4 (mP P′) (mP P)

zOf : Z → Z → ℕ
zOf u v = zP (par u) (par v)

-- The powers of ω, as parity vectors.
ωP : ℕ → P4
ωP e = par (ωᶻ ^ᶻ e)

private
  imp : Bool → Bool → Bool
  imp a b = not a ∨ b

  imp-sound : ∀ {a b} → imp a b ≡ true → a ≡ true → b ≡ true
  imp-sound {true} h refl = h

  -- For odd P, P′: (ω^zP P P′ P + P′) g₃ ≡ 0.
  zOf-test : Vec Bool 8 → Bool
  zOf-test (a ∷ b ∷ c ∷ d ∷ a′ ∷ b′ ∷ c′ ∷ d′ ∷ []) =
    imp (oddP P ∧ oddP P′) (((ωP (zP P P′) ⊗ P) ⊕ P′) ⊗ par g3 == 𝟘)
    where
    P = ⟨ a , b , c , d ⟩
    P′ = ⟨ a′ , b′ , c′ , d′ ⟩

  zOf-all : allB 8 zOf-test ≡ true
  zOf-all = refl

  -- For odd P: (P + ω^mP P) g₃ ≡ 0.
  mOf-test : Vec Bool 4 → Bool
  mOf-test (a ∷ b ∷ c ∷ d ∷ []) = imp (oddP P) (((P ⊕ ωP (mP P)) ⊗ par g3) == 𝟘)
    where P = ⟨ a , b , c , d ⟩

  mOf-all : allB 4 mOf-test ≡ true
  mOf-all = refl

  ∧-intro : ∀ {a b} → a ≡ true → b ≡ true → a ∧ b ≡ true
  ∧-intro refl refl = refl

-- An odd x is ≡ ω^(mP (par x)) (mod δ³).
mOf-spec : ∀ x → oddᶻ x ≡ true → δ³ᶻ ∣ (x ZR.- ωᶻ ^ᶻ mP (par x))
mOf-spec x ox = div-intro δ³ᶻ g3 (x ZR.- ωᶻ ^ᶻ mP (par x)) refl (begin
  par ((x ZR.- ωᶻ ^ᶻ mP (par x)) ZR.* g3)     ≡⟨ par-* (x ZR.- ωᶻ ^ᶻ mP (par x)) g3 ⟩
  par (x ZR.- ωᶻ ^ᶻ mP (par x)) ⊗ par g3      ≡⟨ cong (_⊗ par g3) (par-- x (ωᶻ ^ᶻ mP (par x))) ⟩
  (par x ⊕ ωP (mP (par x))) ⊗ par g3           ≡⟨ ==-sound _ 𝟘 (imp-sound (allB-sound 4 mOf-test mOf-all
                                                     (pa (par x) ∷ pb (par x) ∷ pc (par x) ∷ pd (par x) ∷ []))
                                                     (trans (oddP-par x) ox)) ⟩
  𝟘                                            ∎)
  where open ≡-Reasoning

-- Two odd u, v satisfy ωᶻ u ≡ v (mod δ³) for z = zOf u v.
zOf-spec : ∀ u v → oddᶻ u ≡ true → oddᶻ v ≡ true → δ³ᶻ ∣ ((ωᶻ ^ᶻ zOf u v) ZR.* u ZR.- v)
zOf-spec u v ou ov = div-intro δ³ᶻ g3 X refl (begin
  par (X ZR.* g3)                                   ≡⟨ par-* X g3 ⟩
  par X ⊗ par g3                                    ≡⟨ cong (_⊗ par g3) (trans (par-- ((ωᶻ ^ᶻ z) ZR.* u) v)
                                                         (cong (_⊕ par v) (par-* (ωᶻ ^ᶻ z) u))) ⟩
  ((ωP z ⊗ par u) ⊕ par v) ⊗ par g3                 ≡⟨ ==-sound _ 𝟘 (imp-sound (allB-sound 8 zOf-test zOf-all
                                                         (pa (par u) ∷ pb (par u) ∷ pc (par u) ∷ pd (par u) ∷
                                                          pa (par v) ∷ pb (par v) ∷ pc (par v) ∷ pd (par v) ∷ []))
                                                         (∧-intro (trans (oddP-par u) ou) (trans (oddP-par v) ov))) ⟩
  𝟘                                                 ∎)
  where
  open ≡-Reasoning
  z = zOf u v
  X = (ωᶻ ^ᶻ z) ZR.* u ZR.- v

zOf-< : ∀ u v → zOf u v ℕ.< 4
zOf-< u v = sub4-< (mP (par v)) (mP (par u))
  where
  sub4-< : ∀ m l → sub4 m l ℕ.< 4
  sub4-< 0 0 = ℕ.s≤s ℕ.z≤n
  sub4-< 0 1 = ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))
  sub4-< 0 2 = ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))
  sub4-< 0 3 = ℕ.s≤s (ℕ.s≤s ℕ.z≤n)
  sub4-< 1 0 = ℕ.s≤s (ℕ.s≤s ℕ.z≤n)
  sub4-< 1 1 = ℕ.s≤s ℕ.z≤n
  sub4-< 1 2 = ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))
  sub4-< 1 3 = ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))
  sub4-< 2 0 = ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))
  sub4-< 2 1 = ℕ.s≤s (ℕ.s≤s ℕ.z≤n)
  sub4-< 2 2 = ℕ.s≤s ℕ.z≤n
  sub4-< 2 3 = ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))
  sub4-< 3 0 = ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))
  sub4-< 3 1 = ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))
  sub4-< 3 2 = ℕ.s≤s (ℕ.s≤s ℕ.z≤n)
  sub4-< 3 3 = ℕ.s≤s ℕ.z≤n
  sub4-< (suc (suc (suc (suc m)))) l = ℕ.s≤s ℕ.z≤n
  sub4-< 0 (suc (suc (suc (suc l)))) = ℕ.s≤s ℕ.z≤n
  sub4-< 1 (suc (suc (suc (suc l)))) = ℕ.s≤s ℕ.z≤n
  sub4-< 2 (suc (suc (suc (suc l)))) = ℕ.s≤s ℕ.z≤n
  sub4-< 3 (suc (suc (suc (suc l)))) = ℕ.s≤s ℕ.z≤n

------------------------------------------------------------------------
-- The exponent under multiplication by ω

-- (z - 1) mod 4.
pred4 : ℕ → ℕ
pred4 0 = 3
pred4 (suc z) = z

private
  ≡ᵇ-sound : ∀ m n → (m ℕ.≡ᵇ n) ≡ true → m ≡ n
  ≡ᵇ-sound m n h = ℕP.≡ᵇ⇒≡ m n (subst T (sym h) tt)

  zOf-ω-test : Vec Bool 8 → Bool
  zOf-ω-test (a ∷ b ∷ c ∷ d ∷ a′ ∷ b′ ∷ c′ ∷ d′ ∷ []) =
    imp (oddP P ∧ oddP P′) (zP (par ωᶻ ⊗ P) P′ ℕ.≡ᵇ pred4 (zP P P′))
    where
    P = ⟨ a , b , c , d ⟩
    P′ = ⟨ a′ , b′ , c′ , d′ ⟩

  zOf-ω-all : allB 8 zOf-ω-test ≡ true
  zOf-ω-all = refl

-- Multiplying the first entry by ω lowers the exponent by one.
zOf-ω : ∀ u v → oddᶻ u ≡ true → oddᶻ v ≡ true → zOf (ωᶻ ZR.* u) v ≡ pred4 (zOf u v)
zOf-ω u v ou ov =
  trans (cong (λ P → zP P (par v)) (par-* ωᶻ u))
        (≡ᵇ-sound _ _ (imp-sound (allB-sound 8 zOf-ω-test zOf-ω-all
                                   (pa (par u) ∷ pb (par u) ∷ pc (par u) ∷ pd (par u) ∷
                                    pa (par v) ∷ pb (par v) ∷ pc (par v) ∷ pd (par v) ∷ []))
                                 (∧-intro (trans (oddP-par u) ou) (trans (oddP-par v) ov))))

------------------------------------------------------------------------
-- Residues in terms of δ
--
-- Over 𝔽₂, ω = 1 + t with t = δ, so a parity vector aω³ + bω² + cω + d
-- is c₀ + c₁ t + c₂ t² + c₃ t³ with c₀ = a + b + c + d, c₁ = a + c,
-- c₂ = a + b and c₃ = a.  Then δʲ divides x iff c₀ … c_{j-1} vanish,
-- and the parity of x / δʲ is c_j.

c0 c1 c2 c3 : P4 → Bool
c0 = oddP
c1 P = pa P xor pc P
c2 P = pa P xor pb P
c3 P = pa P

g1 : Z
g1 = Omega -[1+ 0 ] (+ 1) -[1+ 0 ] (+ 1)

δg1 : δᶻ ZR.* g1 ≡ 2ᶻ
δg1 = refl

private
  -- For all P: the parity of y is c₁ of δ y, and c₂ of δ² y.
  quot1-test quot2-test : Vec Bool 4 → Bool
  quot1-test (a ∷ b ∷ c ∷ d ∷ []) = not (oddP P xor c1 (par δᶻ ⊗ P))
    where P = ⟨ a , b , c , d ⟩
  quot2-test (a ∷ b ∷ c ∷ d ∷ []) = not (oddP P xor c2 (par δ²ᶻ ⊗ P))
    where P = ⟨ a , b , c , d ⟩

  quot1-all : allB 4 quot1-test ≡ true
  quot1-all = refl

  quot2-all : allB 4 quot2-test ≡ true
  quot2-all = refl

  eqb-sound : ∀ {a b} → not (a xor b) ≡ true → a ≡ b
  eqb-sound {true} {true} _ = refl
  eqb-sound {false} {false} _ = refl

  vec4 : P4 → Vec Bool 4
  vec4 P = pa P ∷ pb P ∷ pc P ∷ pd P ∷ []

  vec8 : P4 → P4 → Vec Bool 8
  vec8 P Q = pa P ∷ pb P ∷ pc P ∷ pd P ∷ pa Q ∷ pb Q ∷ pc Q ∷ pd Q ∷ []

-- The parity of a quotient by δ or δ².
odd-quot1 : ∀ x y → x ≡ δᶻ ZR.* y → oddᶻ y ≡ c1 (par x)
odd-quot1 x y refl = trans (sym (oddP-par y))
  (trans (eqb-sound (allB-sound 4 quot1-test quot1-all (vec4 (par y)))) (cong c1 (sym (par-* δᶻ y))))

odd-quot2 : ∀ x y → x ≡ δ²ᶻ ZR.* y → oddᶻ y ≡ c2 (par x)
odd-quot2 x y refl = trans (sym (oddP-par y))
  (trans (eqb-sound (allB-sound 4 quot2-test quot2-all (vec4 (par y)))) (cong c2 (sym (par-* δ²ᶻ y))))

private
  δ²-test : Vec Bool 4 → Bool
  δ²-test (a ∷ b ∷ c ∷ d ∷ []) = imp (not (c0 P) ∧ not (c1 P)) (P ⊗ par g2 == 𝟘)
    where P = ⟨ a , b , c , d ⟩

  δ²-all : allB 4 δ²-test ≡ true
  δ²-all = refl

  not-intro : ∀ {a} → a ≡ false → not a ≡ true
  not-intro refl = refl

-- δ² divides x if c₀ and c₁ vanish.
δ²∣-par : ∀ x → c0 (par x) ≡ false → c1 (par x) ≡ false → δ²ᶻ ∣ x
δ²∣-par x e0 e1 = div-intro δ²ᶻ g2 x refl
  (trans (par-* x g2) (==-sound _ 𝟘 (imp-sound (allB-sound 4 δ²-test δ²-all (vec4 (par x)))
                                               (∧-intro (not-intro e0) (not-intro e1)))))

private
  δ-test : Vec Bool 4 → Bool
  δ-test (a ∷ b ∷ c ∷ d ∷ []) = imp (not (c0 P) ∧ c1 P) (not (c0 (P ⊕ par δᶻ)) ∧ not (c1 (P ⊕ par δᶻ)))
    where P = ⟨ a , b , c , d ⟩

  δ-all : allB 4 δ-test ≡ true
  δ-all = refl

  not-elim : ∀ {a} → not a ≡ true → a ≡ false
  not-elim {false} _ = refl

-- δ² divides x - δ if c₀ vanishes and c₁ does not: x ≡ δ (mod δ²).
δ²∣-δ : ∀ x → c0 (par x) ≡ false → c1 (par x) ≡ true → δ²ᶻ ∣ (x ZR.- δᶻ)
δ²∣-δ x e0 e1 = δ²∣-par (x ZR.- δᶻ)
  (trans (cong c0 (par-- x δᶻ)) (not-elim (∧-l h)))
  (trans (cong c1 (par-- x δᶻ)) (not-elim (∧-r {not (c0 (par x ⊕ par δᶻ))} h)))
  where
  h = imp-sound (allB-sound 4 δ-test δ-all (vec4 (par x))) (∧-intro (not-intro e0) e1)

-- δ³ divides 2 and g₁.
δ³∣2 : δ³ᶻ ∣ 2ᶻ
δ³∣2 = g3 , refl

δ³∣g1 : δ³ᶻ ∣ g1
δ³∣g1 = div-intro δ³ᶻ g3 g1 refl refl

-- Cancelling δ².
δ²-cancel : ∀ x y → δ²ᶻ ZR.* x ≡ δ²ᶻ ZR.* y → x ≡ y
δ²-cancel x y eq = two-cancel x y (begin
  2ᶻ ZR.* x                  ≡⟨ cong (ZR._* x) (sym δ²g2) ⟩
  (δ²ᶻ ZR.* g2) ZR.* x       ≡⟨ cong (ZR._* x) (ZR.*-comm δ²ᶻ g2) ⟩
  (g2 ZR.* δ²ᶻ) ZR.* x       ≡⟨ ZR.*-assoc g2 δ²ᶻ x ⟩
  g2 ZR.* (δ²ᶻ ZR.* x)       ≡⟨ cong (g2 ZR.*_) eq ⟩
  g2 ZR.* (δ²ᶻ ZR.* y)       ≡⟨ sym (ZR.*-assoc g2 δ²ᶻ y) ⟩
  (g2 ZR.* δ²ᶻ) ZR.* y       ≡⟨ cong (ZR._* y) (ZR.*-comm g2 δ²ᶻ) ⟩
  (δ²ᶻ ZR.* g2) ZR.* y       ≡⟨ cong (ZR._* y) δ²g2 ⟩
  2ᶻ ZR.* y                  ∎)
  where open ≡-Reasoning

------------------------------------------------------------------------
-- The exponent of congruent entries

private
  ⊕-test : Vec Bool 8 → Bool
  ⊕-test (a ∷ b ∷ c ∷ d ∷ a′ ∷ b′ ∷ c′ ∷ d′ ∷ []) = P ⊕ (P ⊕ Q) == Q
    where
    P = ⟨ a , b , c , d ⟩
    Q = ⟨ a′ , b′ , c′ , d′ ⟩

  ⊕-all : allB 8 ⊕-test ≡ true
  ⊕-all = refl

  ⊕-cancel : ∀ P Q → P ⊕ (P ⊕ Q) ≡ Q
  ⊕-cancel P Q = ==-sound _ Q (allB-sound 8 ⊕-test ⊕-all (vec8 P Q))

  -- The other parity vector, from the sum.
  ⊕-solve : ∀ P Q E → P ⊕ Q ≡ E → Q ≡ P ⊕ E
  ⊕-solve P Q E h = trans (sym (⊕-cancel P Q)) (cong (P ⊕_) h)

  -- zP P (P + δ³ C) = 0 for all P, C.
  cong3-test : Vec Bool 8 → Bool
  cong3-test (a ∷ b ∷ c ∷ d ∷ a′ ∷ b′ ∷ c′ ∷ d′ ∷ []) = zP P (P ⊕ par δ³ᶻ ⊗ C) ℕ.≡ᵇ 0
    where
    P = ⟨ a , b , c , d ⟩
    C = ⟨ a′ , b′ , c′ , d′ ⟩

  cong3-all : allB 8 cong3-test ≡ true
  cong3-all = refl

  -- zP P (P + g₂ Q) = 2 for odd P, Q.
  plus2-test : Vec Bool 8 → Bool
  plus2-test (a ∷ b ∷ c ∷ d ∷ a′ ∷ b′ ∷ c′ ∷ d′ ∷ []) =
    imp (oddP P ∧ oddP Q) (zP P (P ⊕ par g2 ⊗ Q) ℕ.≡ᵇ 2)
    where
    P = ⟨ a , b , c , d ⟩
    Q = ⟨ a′ , b′ , c′ , d′ ⟩

  plus2-all : allB 8 plus2-test ≡ true
  plus2-all = refl

-- Entries congruent modulo δ³ give the exponent 0.
zOf-cong3 : ∀ u v → δ³ᶻ ∣ (u ZR.- v) → zOf u v ≡ 0
zOf-cong3 u v (c , eq) = begin
  zP (par u) (par v)                               ≡⟨ cong (zP (par u)) pv ⟩
  zP (par u) (par u ⊕ par δ³ᶻ ⊗ par c)             ≡⟨ ≡ᵇ-sound _ _ (allB-sound 8 cong3-test cong3-all (vec8 (par u) (par c))) ⟩
  0                                                ∎
  where
  open ≡-Reasoning
  pv : par v ≡ par u ⊕ par δ³ᶻ ⊗ par c
  pv = ⊕-solve (par u) (par v) (par δ³ᶻ ⊗ par c)
         (trans (sym (par-- u v)) (trans (cong par eq) (par-* δ³ᶻ c)))

-- u and u − g₂ w, for odd u and w: the exponent is 2.
zOf-plus2 : ∀ u w → oddᶻ u ≡ true → oddᶻ w ≡ true → zOf u (u ZR.- g2 ZR.* w) ≡ 2
zOf-plus2 u w ou ow = begin
  zP (par u) (par (u ZR.- g2 ZR.* w))              ≡⟨ cong (zP (par u)) (trans (par-- u (g2 ZR.* w)) (cong (par u ⊕_) (par-* g2 w))) ⟩
  zP (par u) (par u ⊕ par g2 ⊗ par w)              ≡⟨ ≡ᵇ-sound _ _ (imp-sound (allB-sound 8 plus2-test plus2-all (vec8 (par u) (par w)))
                                                                    (∧-intro (trans (oddP-par u) ou) (trans (oddP-par w) ow))) ⟩
  2                                                ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Two odd entries and their sum, by the exponent

private
  -- For odd P, Q with zP P Q odd: c₁ (P + Q) = 1.
  zodd-test : Vec Bool 8 → Bool
  zodd-test (a ∷ b ∷ c ∷ d ∷ a′ ∷ b′ ∷ c′ ∷ d′ ∷ []) =
    imp (oddP P ∧ oddP Q ∧ oddℕ (zP P Q)) (c1 (P ⊕ Q))
    where
    P = ⟨ a , b , c , d ⟩
    Q = ⟨ a′ , b′ , c′ , d′ ⟩

  zodd-all : allB 8 zodd-test ≡ true
  zodd-all = refl

  -- For odd P, Q with zP P Q = 2: c₁ (P + Q) = 0 and c₂ (P + Q) = 1.
  z2-test : Vec Bool 8 → Bool
  z2-test (a ∷ b ∷ c ∷ d ∷ a′ ∷ b′ ∷ c′ ∷ d′ ∷ []) =
    imp (oddP P ∧ oddP Q ∧ (zP P Q ℕ.≡ᵇ 2)) (not (c1 (P ⊕ Q)) ∧ c2 (P ⊕ Q))
    where
    P = ⟨ a , b , c , d ⟩
    Q = ⟨ a′ , b′ , c′ , d′ ⟩

  z2-all : allB 8 z2-test ≡ true
  z2-all = refl

  ≡ᵇ-intro : ∀ m → (m ℕ.≡ᵇ m) ≡ true
  ≡ᵇ-intro zero = refl
  ≡ᵇ-intro (suc m) = ≡ᵇ-intro m

  not-true : ∀ {a} → not a ≡ true → a ≡ false
  not-true {false} _ = refl

-- For odd u, v with an odd exponent, δ divides u ± v exactly once.
zOf-odd-c1 : ∀ u v → oddᶻ u ≡ true → oddᶻ v ≡ true → oddℕ (zOf u v) ≡ true →
             c1 (par u ⊕ par v) ≡ true
zOf-odd-c1 u v ou ov oz =
  imp-sound (allB-sound 8 zodd-test zodd-all (vec8 (par u) (par v)))
    (∧-intro (trans (oddP-par u) ou) (∧-intro (trans (oddP-par v) ov) oz))

-- For odd u, v with the exponent 2, δ² divides u ± v exactly.
zOf-2-c : ∀ u v → oddᶻ u ≡ true → oddᶻ v ≡ true → zOf u v ≡ 2 →
          c1 (par u ⊕ par v) ≡ false × c2 (par u ⊕ par v) ≡ true
zOf-2-c u v ou ov z2 = not-true (∧-l h) , ∧-r {not (c1 (par u ⊕ par v))} h
  where
  h = imp-sound (allB-sound 8 z2-test z2-all (vec8 (par u) (par v)))
        (∧-intro (trans (oddP-par u) ou) (∧-intro (trans (oddP-par v) ov) (trans (cong (ℕ._≡ᵇ 2) z2) (≡ᵇ-intro 2))))

-- Cancelling δ.
δ-cancel : ∀ x y → δᶻ ZR.* x ≡ δᶻ ZR.* y → x ≡ y
δ-cancel x y eq = two-cancel x y (begin
  2ᶻ ZR.* x                  ≡⟨ cong (ZR._* x) (sym δg1) ⟩
  (δᶻ ZR.* g1) ZR.* x        ≡⟨ cong (ZR._* x) (ZR.*-comm δᶻ g1) ⟩
  (g1 ZR.* δᶻ) ZR.* x        ≡⟨ ZR.*-assoc g1 δᶻ x ⟩
  g1 ZR.* (δᶻ ZR.* x)        ≡⟨ cong (g1 ZR.*_) eq ⟩
  g1 ZR.* (δᶻ ZR.* y)        ≡⟨ sym (ZR.*-assoc g1 δᶻ y) ⟩
  (g1 ZR.* δᶻ) ZR.* y        ≡⟨ cong (ZR._* y) (ZR.*-comm g1 δᶻ) ⟩
  (δᶻ ZR.* g1) ZR.* y        ≡⟨ cong (ZR._* y) δg1 ⟩
  2ᶻ ZR.* y                  ∎)
  where open ≡-Reasoning

------------------------------------------------------------------------
-- The exponent with the entries exchanged

-- (-z) mod 4.
neg4 : ℕ → ℕ
neg4 0 = 0
neg4 1 = 3
neg4 2 = 2
neg4 3 = 1
neg4 _ = 0

private
  sym-test : Vec Bool 8 → Bool
  sym-test (a ∷ b ∷ c ∷ d ∷ a′ ∷ b′ ∷ c′ ∷ d′ ∷ []) =
    imp (oddP P ∧ oddP Q) (zP Q P ℕ.≡ᵇ neg4 (zP P Q))
    where
    P = ⟨ a , b , c , d ⟩
    Q = ⟨ a′ , b′ , c′ , d′ ⟩

  sym-all : allB 8 sym-test ≡ true
  sym-all = refl

zOf-sym : ∀ u v → oddᶻ u ≡ true → oddᶻ v ≡ true → zOf v u ≡ neg4 (zOf u v)
zOf-sym u v ou ov =
  ≡ᵇ-sound _ _ (imp-sound (allB-sound 8 sym-test sym-all (vec8 (par u) (par v)))
                          (∧-intro (trans (oddP-par u) ou) (trans (oddP-par v) ov)))

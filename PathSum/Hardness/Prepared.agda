------------------------------------------------------------------------
-- Presentations of groups
--
-- Path-sums with their ancillas prepared, and certificates on the
-- path-sum side (Amy, QPL 2018, section 4, footnote 2)
--
-- The plan of phase B is in the header of PathSum.Hardness.Certificate.
-- This module carries membership over to the path-sums of phase A, and
-- builds the form of the reduction to which PathSum.Expand's test of
-- normal forms applies.
--
-- Certificates for path-sums.  The expansions of two netlists over
-- {NOT, CNOT, Toffoli} into Clifford+T compute the netlists' Boolean
-- functions (PathSum.Hardness.expandᴺ-computes), so they are equivalent
-- on the inputs whose ancillas are 0 exactly when the netlists are
-- (expandᴺ-equivalent⇔), and inequivalence of the expansions has the
-- certificates of PathSum.Hardness.Certificate: an input, checked by
-- simulating the two netlists (expansion-certificate).  For phase A's
-- circuit of a CNF formula φ, the circuit is not the identity on the
-- clean inputs exactly when its netlist has a certificate against the
-- empty netlist (circuit-certificate).  Nothing about the path-sums is
-- computed: the check simulates netlists, and the theorems carry its
-- verdict to the path-sums.
--
-- Preparing the ancillas.  Phase A's circuit is the identity only on
-- the inputs whose ancillas are 0: from other inputs its netlist need
-- not come back (PathSum.Hardness.Example.dirty₀).  PathSum.Expand
-- tests whether a normal form is the identity on every input, so the
-- reduction is carried to a path-sum that is the identity everywhere
-- exactly when the circuit is on the clean inputs.  prepared a ξ reads
-- the ancilla inputs as the constant 0 -- set0ˢ a ξ, the paper's
-- treatment of ancillas in section 5.2 -- and xors each ancilla's input
-- into its output (xorIn: the output polynomial gains the input
-- variable, which modulo 2 is a xor).  If ξ computes F (PathSum.
-- Classical), then set0ˢ a ξ computes x ↦ F(x with its ancillas 0)
-- (set0ˢ-computes, from PathSum.Ancillas.amp-set0ˢ-any), and xorIn s ξ
-- computes F with the input xored into the wires where s holds
-- (xorIn-computes: a path of xorIn s ξ hits z exactly when the same
-- path of ξ hits z with those wires xored with the input, hits-xorIn);
-- so the prepared path-sum computes
--
--    prepFun a F x = F(x with ancillas 0), with each ancilla wire
--                    xored with x's
--
-- (prepared-computes), and it is equivalent to the identity exactly
-- when F is the identity on the clean inputs (prepared-identity⇔): on
-- an ancilla wire F must leave 0 for the xor to give x back, and off
-- the ancillas F(x with ancillas 0) must be x.  The equivalence to the
-- identity of a path-sum that computes a function is that function
-- being the identity (computes-identity⇔).  So the prepared path-sum
-- asks phase A's question -- ξ ≋[ a ]₀* idPS, or set0ˢ a ξ ≋
-- set0ˢ a idPS with the ancillas read as 0 on both sides
-- (prepared⇔clean, prepared⇔set0) -- in the form "≋ idPS" that
-- PathSum.Expand tests; set0ˢ a ξ alone is never ≋ idPS when there is
-- an ancilla, as it sends every input to one with the ancillas 0.
--
-- The reduction, prepared.  cleanPS φ is phase A's circuit of φ,
-- prepared: it has the circuit's path variables and normalisation,
-- 4‖φ‖ + 4 of each (PathSum.Hardness.circuit-paths), on the circuit's
-- n + 2 lits + negs + 2 clauses + 3 wires, and it is the specification
-- |x⟩|a⟩|t⟩ ↦ |x⟩|a⟩|t ⊕ φ(x)⟩ on every input, dirty ancillas included
-- (cleanPS-spec: cleanPS φ ≋ circuitˢ φ), so it is equivalent to the
-- identity exactly when φ is unsatisfiable (cleanPS-identity⇔unsat),
-- that is, exactly when phase A's circuit is the identity on the clean
-- inputs (cleanPS⇔clean, from PathSum.Hardness.hardness) and in the
-- set0 form (cleanPS⇔set0, from hardness-set0).
-- For two netlists, miterPS a gs hs prepares the expansion of their
-- miter gs ++ reverse hs, and is equivalent to the identity exactly
-- when they are equivalent on the clean inputs (miterPS-identity⇔).
--
-- What is not claimed.  The size of cleanPS φ is given by its path
-- variables, normalisation and wires; its polynomials are those of the
-- circuit's path-sum -- of polynomial size by corollary 2.15
-- (PathSum.Hardness.Conditional.circuit-size) -- with the ancilla
-- inputs set to 0, which only drops terms, and an input variable added
-- to each ancilla output.  A sparse representation of cleanPS φ itself
-- (PathSum.Size.Sparse) is not built: its ancilla outputs are not the
-- liftings of linear forms coefficient by coefficient, only modulo 2.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hardness.Prepared (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-assoc; xor-same; xor-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (0ℤ)
open import Data.List.Base using (List; [])
open import Data.Nat.Base using (zero)
open import Data.Product.Base using (∃; _×_; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no; does; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Fin.Properties as Fin

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Ancillas M₀ using
  (Clean; set0ˢ; zeroˢ; clean-zeroˢ; amp-set0ˢ-any; _≋[_]₀*_; ≋⇒≋[]₀*;
   ≋[]₀*⇔set0ˢ)
open import PathSum.Assign using
  (_[_≔_]; ≔-here; ≔-there; same; same-true; same-intro)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out; idPS)
open import PathSum.CircuitSemantics M₀ using (δ)
open import PathSum.Classical M₀ using
  (_computes_; computing; amp-computes; computes-≗; computes-≋)
open import PathSum.CRK.Path M₀ using (⟦_⟧; norm; paths)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; zpow; scale-map; Σᴮ-cong)
open import PathSum.Denotation M₀ using
  (Assign; amp; hits; outBit; _≋_; hits-intro; hits-elim; eval-μ-val)
open import PathSum.Hardness M₀ using
  (expandᴺ; expandᴺ-computes; ≋[]₀*-agree; ≋[]₀*⇔agree; idPS-computes;
   no-ancillas; circuit; circuit-computes; circuitˢ; circuitˢ-computes;
   hardness; hardness-set0)
open import PathSum.Hardness.Certificate using
  (Equivalentᴺ; miterᴺ; miter⇔; runᴺ-cong; check; certificate⇔)
open import PathSum.Hardness.CNF using
  (CNF; ⟦_⟧ᶠ; ⟦⟧ᶠ-cong; Unsatisfiable; cnf; nodes)
open import PathSum.Hardness.Netlist using
  (NCT; runᴺ; netlist; wires; inputs; ancillas; tgt; netlist-correct;
   netlist-identity⇔unsat; inp≢ancʷ; anc≢tgtʷ)
open import PathSum.HiddenShift.Sign M₀ using (odd-+; odd-[])
open import PathSum.Polynomial using (μ; x[_]; _+ᴾ_; eval)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Properties using (eval-+ᴾ)

private
  variable
    n k m j : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  -- Chaining equivalences of statements.

  infixr 5 _⟨⇔⟩_

  _⟨⇔⟩_ : {P Q R : Set} → P ⇔ Q → Q ⇔ R → P ⇔ R
  f ⟨⇔⟩ g = mk⇔ (λ a → Equivalence.to g (Equivalence.to f a))
                (λ c → Equivalence.from f (Equivalence.from g c))

  sym⇔ : {P Q : Set} → P ⇔ Q → Q ⇔ P
  sym⇔ f = mk⇔ (Equivalence.from f) (Equivalence.to f)

  ¬⇔ : {P Q : Set} → P ⇔ Q → (¬ P) ⇔ (¬ Q)
  ¬⇔ f = mk⇔ (λ np q → np (Equivalence.from f q))
             (λ nq p → nq (Equivalence.to f p))


------------------------------------------------------------------------
-- Bits

private
  bool-≡ : ∀ {a b} → (a ≡ true → b ≡ true) → (b ≡ true → a ≡ true) → a ≡ b
  bool-≡ {true}  {true}  f g = refl
  bool-≡ {true}  {false} f g = sym (f refl)
  bool-≡ {false} {true}  f g = g refl
  bool-≡ {false} {false} f g = refl

  cancel : ∀ p q → (p xor q) xor q ≡ p
  cancel p q =
    trans (xor-assoc p q q)
          (trans (cong (p xor_) (xor-same q)) (xor-identityʳ p))

  -- Moving a conditional xor across an equation.

  shift : ∀ b o c t → (if b then o xor c else o) ≡ t →
          o ≡ (if b then t xor c else t)
  shift true  o c t h = trans (sym (cancel o c)) (cong (_xor c) h)
  shift false o c t h = h

  unshift : ∀ b o c t → o ≡ (if b then t xor c else t) →
            (if b then o xor c else o) ≡ t
  unshift true  o c t h = trans (cong (_xor c) h) (cancel t c)
  unshift false o c t h = h

  xor-self : ∀ p q → p xor q ≡ q → p ≡ false
  xor-self true  true  ()
  xor-self true  false ()
  xor-self false q     _ = refl

  -- A state overwritten at t agrees with another so overwritten where
  -- the two agreed.

  ≔-agree : (u u′ : Assign n) (t : Fin n) (b : Bool) {w : Fin n} →
            u w ≡ u′ w → (u [ t ≔ b ]) w ≡ (u′ [ t ≔ b ]) w
  ≔-agree u u′ t b {w} e = go ⌊ w Fin.≟ t ⌋
    where
    go : ∀ d → (if d then b else u w) ≡ (if d then b else u′ w)
    go true  = refl
    go false = e


------------------------------------------------------------------------
-- Xoring the inputs into some outputs

-- On the wires where s holds, the output gains its input: read modulo
-- 2, the path's output bit is xored with the input's.

xorIn : (Fin n → Bool) → PathSum n k m → PathSum n k m
xorIn s ξ = ⟨ phase ξ , (λ w → if s w then out ξ w +ᴾ μ x[ w ] else out ξ w) ⟩

outBit-xorIn : (s : Fin n → Bool) (ξ : PathSum n k m) (x : Assign n)
               (y : Assign m) (w : Fin n) →
               outBit (xorIn s ξ) x y w ≡
               (if s w then outBit ξ x y w xor x w else outBit ξ x y w)
outBit-xorIn s ξ x y w = go (s w)
  where
  go : ∀ b → odd (eval (if b then out ξ w +ᴾ μ x[ w ] else out ξ w) x y) ≡
             (if b then odd (eval (out ξ w) x y) xor x w
              else odd (eval (out ξ w) x y))
  go true  =
    trans (cong odd (eval-+ᴾ (out ξ w) (μ x[ w ]) x y))
    (trans (odd-+ (eval (out ξ w) x y) (eval (μ x[ w ]) x y))
           (cong (odd (eval (out ξ w) x y) xor_)
                 (trans (cong odd (eval-μ-val x[ w ] x y)) (odd-[] (x w)))))
  go false = refl

-- So a path of xorIn s ξ hits z exactly when the same path of ξ hits z
-- with the wires of s xored with the input.

masked : (Fin n → Bool) → Assign n → Assign n → Assign n
masked s x z w = if s w then z w xor x w else z w

hits-xorIn : (s : Fin n → Bool) (ξ : PathSum n k m) (x : Assign n)
             (y : Assign m) (z : Assign n) →
             hits (xorIn s ξ) x y z ≡ hits ξ x y (masked s x z)
hits-xorIn s ξ x y z = bool-≡
  (λ h → hits-intro ξ x y (masked s x z) (λ w →
     shift (s w) (outBit ξ x y w) (x w) (z w)
       (trans (sym (outBit-xorIn s ξ x y w))
              (hits-elim (xorIn s ξ) x y z h w))))
  (λ h → hits-intro (xorIn s ξ) x y z (λ w →
     trans (outBit-xorIn s ξ x y w)
       (unshift (s w) (outBit ξ x y w) (x w) (z w)
         (hits-elim ξ x y (masked s x z) h w))))

amp-xorIn : (s : Fin n → Bool) (ξ : PathSum n k m) (x z : Assign n) →
            amp (xorIn s ξ) x z ≐ amp ξ x (masked s x z)
amp-xorIn s ξ x z = Σᴮ-cong (λ y i →
  cong (λ b → (if b then zpow (eval (phase ξ) x y) else 0ᴬ) i)
       (hits-xorIn s ξ x y z))

-- If ξ computes F, xorIn s ξ computes F with the input xored into the
-- wires of s.

xorIn-computes : (s : Fin n → Bool) (ξ : PathSum n k m)
                 {F : Assign n → Assign n} → ξ computes F →
                 xorIn s ξ computes
                 (λ x w → if s w then F x w xor x w else F x w)
xorIn-computes {k = k} s ξ {F} c = computing λ x z →
  amp-xorIn s ξ x z ∙ amp-computes c x (masked s x z)
  ∙ scale-map k (δ-masked x z)
  where
  G : Assign _ → Assign _
  G x w = if s w then F x w xor x w else F x w

  same-masked : ∀ x z → same (F x) (masked s x z) ≡ same (G x) z
  same-masked x z = bool-≡
    (λ h → same-intro (G x) z (λ w →
       unshift (s w) (F x w) (x w) (z w)
         (same-true (F x) (masked s x z) h w)))
    (λ h → same-intro (F x) (masked s x z) (λ w →
       shift (s w) (F x w) (x w) (z w) (same-true (G x) z h w)))

  δ-masked : ∀ x z → δ (F x) (masked s x z) ≐ δ (G x) z
  δ-masked x z i = cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i) (same-masked x z)


------------------------------------------------------------------------
-- Setting the ancillas to 0

-- If ξ computes F, the path-sum with its ancillas read as 0 computes F
-- after zeroing them.

set0ˢ-computes : (a : Fin j → Fin n) (ξ : PathSum n k m)
                 {F : Assign n → Assign n} → ξ computes F →
                 set0ˢ a ξ computes (λ x → F (zeroˢ a x))
set0ˢ-computes a ξ c = computing λ x z →
  amp-set0ˢ-any a ξ x z ∙ amp-computes c (zeroˢ a x) z

-- Zeroing the ancillas changes nothing on a clean input, nor off the
-- ancillas.

zeroˢ-clean : (a : Fin j → Fin n) (x : Assign n) → Clean a x →
              ∀ w → zeroˢ a x w ≡ x w
zeroˢ-clean {zero}  a x cl w = refl
zeroˢ-clean {suc j} a x cl w = at (w Fin.≟ a zero)
  where
  z′ : Assign _
  z′ = zeroˢ (λ i → a (suc i)) x

  at : Dec (w ≡ a zero) → (z′ [ a zero ≔ false ]) w ≡ x w
  at (yes e) = trans (cong (z′ [ a zero ≔ false ]) e)
               (trans (≔-here z′ (a zero) false)
                      (trans (sym (cl zero)) (cong x (sym e))))
  at (no ne) = trans (≔-there z′ false ne)
                     (zeroˢ-clean (λ i → a (suc i)) x (λ i → cl (suc i)) w)

zeroˢ-off : (a : Fin j → Fin n) (x : Assign n) {w : Fin n} →
            (∀ i → a i ≢ w) → zeroˢ a x w ≡ x w
zeroˢ-off {zero}  a x     off = refl
zeroˢ-off {suc j} a x {w} off = at (w Fin.≟ a zero)
  where
  at : Dec (w ≡ a zero) → (zeroˢ (λ i → a (suc i)) x [ a zero ≔ false ]) w ≡ x w
  at (yes e) = contradiction (sym e) (off zero)
  at (no ne) = trans (≔-there (zeroˢ (λ i → a (suc i)) x) false ne)
                     (zeroˢ-off (λ i → a (suc i)) x (λ i → off (suc i)))


------------------------------------------------------------------------
-- Prepared path-sums

-- Whether a wire is an ancilla.

anc? : (a : Fin j → Fin n) (w : Fin n) → Dec (∃ λ i → a i ≡ w)
anc? a w = Fin.any? (λ i → a i Fin.≟ w)

isAnc : (Fin j → Fin n) → Fin n → Bool
isAnc a w = does (anc? a w)

-- The ancillas read as 0, and each ancilla's input xored into its
-- output.

prepared : (Fin j → Fin n) → PathSum n k m → PathSum n k m
prepared a ξ = xorIn (isAnc a) (set0ˢ a ξ)

-- The function it computes, when ξ computes F.

prepFun : (Fin j → Fin n) → (Assign n → Assign n) → Assign n → Assign n
prepFun a F x w =
  if isAnc a w then F (zeroˢ a x) w xor x w else F (zeroˢ a x) w

prepared-computes : (a : Fin j → Fin n) (ξ : PathSum n k m)
                    {F : Assign n → Assign n} → ξ computes F →
                    prepared a ξ computes prepFun a F
prepared-computes a ξ c =
  xorIn-computes (isAnc a) (set0ˢ a ξ) (set0ˢ-computes a ξ c)

-- That function is the identity exactly when F is the identity on the
-- clean inputs.

prepFun-identity⇔ :
  (a : Fin j → Fin n) {F : Assign n → Assign n} →
  (∀ {x x′} → (∀ w → x w ≡ x′ w) → ∀ w → F x w ≡ F x′ w) →
  (∀ x w → prepFun a F x w ≡ x w) ⇔ (∀ x → Clean a x → ∀ w → F x w ≡ x w)
prepFun-identity⇔ a {F} F-cong = mk⇔ to from
  where
  to : (∀ x w → prepFun a F x w ≡ x w) →
       ∀ x → Clean a x → ∀ w → F x w ≡ x w
  to h x cl w =
    trans (F-cong (λ u → sym (zeroˢ-clean a x cl u)) w) (by (anc? a w) (h x w))
    where
    by : (d : Dec (∃ λ i → a i ≡ w)) →
         (if does d then F (zeroˢ a x) w xor x w else F (zeroˢ a x) w) ≡
         x w → F (zeroˢ a x) w ≡ x w
    by (yes (i , e)) h′ =
      trans (xor-self (F (zeroˢ a x) w) (x w) h′)
            (sym (trans (cong x (sym e)) (cl i)))
    by (no _)        h′ = h′

  from : (∀ x → Clean a x → ∀ w → F x w ≡ x w) →
         ∀ x w → prepFun a F x w ≡ x w
  from h x w = by (anc? a w)
    where
    base : F (zeroˢ a x) w ≡ zeroˢ a x w
    base = h (zeroˢ a x) (clean-zeroˢ a x) w

    by : (d : Dec (∃ λ i → a i ≡ w)) →
         (if does d then F (zeroˢ a x) w xor x w else F (zeroˢ a x) w) ≡ x w
    by (yes (i , e)) =
      cong (_xor x w)
           (trans base (trans (cong (zeroˢ a x) (sym e)) (clean-zeroˢ a x i)))
    by (no ne)       = trans base (zeroˢ-off a x (λ i e → ne (i , e)))

-- A path-sum that computes a function is equivalent to the identity
-- exactly when the function is the identity.

computes-identity⇔ : (ζ : PathSum n k m) {G : Assign n → Assign n} →
                     ζ computes G → (ζ ≋ idPS) ⇔ (∀ x w → G x w ≡ x w)
computes-identity⇔ ζ c = mk⇔
  (λ e x w → ≋[]₀*-agree ζ idPS no-ancillas c idPS-computes
               (≋⇒≋[]₀* {ξ = ζ} {ζ = idPS} no-ancillas e) x (λ ()) w)
  (λ h → computes-≋ ζ idPS (computes-≗ ζ h c) idPS-computes)

-- So a prepared path-sum is equivalent to the identity exactly when
-- the function it was prepared from is the identity on the clean
-- inputs.

prepared-identity⇔ :
  (a : Fin j → Fin n) (ξ : PathSum n k m) {F : Assign n → Assign n} →
  (∀ {x x′} → (∀ w → x w ≡ x′ w) → ∀ w → F x w ≡ F x′ w) →
  ξ computes F →
  (prepared a ξ ≋ idPS) ⇔ (∀ x → Clean a x → ∀ w → F x w ≡ x w)
prepared-identity⇔ a ξ F-cong c =
  computes-identity⇔ (prepared a ξ) (prepared-computes a ξ c)
  ⟨⇔⟩ prepFun-identity⇔ a F-cong

-- That is phase A's question: ξ is the identity on the clean inputs,
-- or, reading the ancillas as 0 on both sides (PathSum.Ancillas),
-- set0ˢ a ξ ≋ set0ˢ a idPS.  (set0ˢ a ξ is never ≋ idPS itself when
-- there is an ancilla -- it sends every input to one with the ancillas
-- 0 -- so PathSum.Expand's test against the identity needs the xor.)

prepared⇔clean :
  (a : Fin j → Fin n) (ξ : PathSum n k m) {F : Assign n → Assign n} →
  (∀ {x x′} → (∀ w → x w ≡ x′ w) → ∀ w → F x w ≡ F x′ w) →
  ξ computes F → (prepared a ξ ≋ idPS) ⇔ (ξ ≋[ a ]₀* idPS)
prepared⇔clean a ξ F-cong c =
  prepared-identity⇔ a ξ F-cong c
  ⟨⇔⟩ sym⇔ (≋[]₀*⇔agree ξ idPS a c idPS-computes)

prepared⇔set0 :
  (a : Fin j → Fin n) (ξ : PathSum n k m) {F : Assign n → Assign n} →
  (∀ {x x′} → (∀ w → x w ≡ x′ w) → ∀ w → F x w ≡ F x′ w) →
  ξ computes F → (prepared a ξ ≋ idPS) ⇔ (set0ˢ a ξ ≋ set0ˢ a idPS)
prepared⇔set0 a ξ F-cong c =
  prepared⇔clean a ξ F-cong c ⟨⇔⟩ ≋[]₀*⇔set0ˢ a ξ idPS


------------------------------------------------------------------------
-- Certificates on the path-sum side

-- The expansions of two netlists are equivalent on the clean inputs
-- exactly when the netlists are ...

expandᴺ-equivalent⇔ : (a : Fin j → Fin n) (gs hs : List (NCT n)) →
                      (⟦ expandᴺ gs ⟧ ≋[ a ]₀* ⟦ expandᴺ hs ⟧) ⇔
                      Equivalentᴺ a gs hs
expandᴺ-equivalent⇔ a gs hs =
  ≋[]₀*⇔agree ⟦ expandᴺ gs ⟧ ⟦ expandᴺ hs ⟧ a
              (expandᴺ-computes gs) (expandᴺ-computes hs)

-- ... so their inequivalence has the netlists' certificates.

expansion-certificate :
  (a : Fin j → Fin n) (gs hs : List (NCT n)) →
  (¬ (⟦ expandᴺ gs ⟧ ≋[ a ]₀* ⟦ expandᴺ hs ⟧)) ⇔
  (∃ λ x → proj₁ (check a gs hs x) ≡ true)
expansion-certificate a gs hs =
  ¬⇔ (expandᴺ-equivalent⇔ a gs hs) ⟨⇔⟩ certificate⇔ a gs hs

-- Phase A's circuit of φ is not the identity on the clean inputs
-- exactly when its netlist has a certificate against the empty one.

circuit-certificate :
  (φ : CNF n) →
  (¬ (⟦ circuit φ ⟧ ≋[ ancillas φ ]₀* idPS)) ⇔
  (∃ λ x → proj₁ (check (ancillas φ) (netlist φ) [] x) ≡ true)
circuit-certificate φ =
  ¬⇔ (hardness φ ⟨⇔⟩ sym⇔ (netlist-identity⇔unsat φ))
  ⟨⇔⟩ certificate⇔ (ancillas φ) (netlist φ) []


------------------------------------------------------------------------
-- The reduction, prepared

-- Phase A's circuit of φ with its ancillas prepared, and the function
-- it computes.
--
-- Every statement about cleanPS φ below is proved about cleanPS φ
-- itself, through lemmas that take the path-sum as an argument: Agda
-- compares statements about the amplitudes of two syntactically
-- different path-sums by reducing both (PathSum.Hardness's note on
-- circuit φ), whereas the records _computes_ are compared by their
-- arguments.

cleanPS : (φ : CNF n) → PathSum (wires φ) (norm (circuit φ)) (paths (circuit φ))
cleanPS φ = prepared (ancillas φ) ⟦ circuit φ ⟧

cleanFun : (φ : CNF n) → Assign (wires φ) → Assign (wires φ)
cleanFun φ = prepFun (ancillas φ) (runᴺ (netlist φ))

cleanPS-computes : (φ : CNF n) → cleanPS φ computes cleanFun φ
cleanPS-computes φ =
  prepared-computes (ancillas φ) ⟦ circuit φ ⟧ (circuit-computes φ)

-- It is the identity exactly when φ is unsatisfiable ...

cleanPS-identity⇔unsat : (φ : CNF n) →
                         (cleanPS φ ≋ idPS) ⇔ Unsatisfiable φ
cleanPS-identity⇔unsat φ =
  computes-identity⇔ (cleanPS φ) (cleanPS-computes φ)
  ⟨⇔⟩ prepFun-identity⇔ (ancillas φ) (runᴺ-cong (netlist φ))
  ⟨⇔⟩ netlist-identity⇔unsat φ

-- ... which is phase A's question about the circuit, on the clean
-- inputs and in the set0 form (PathSum.Hardness.hardness,
-- hardness-set0).

cleanPS⇔clean : (φ : CNF n) →
                (cleanPS φ ≋ idPS) ⇔ (⟦ circuit φ ⟧ ≋[ ancillas φ ]₀* idPS)
cleanPS⇔clean φ = cleanPS-identity⇔unsat φ ⟨⇔⟩ sym⇔ (hardness φ)

cleanPS⇔set0 : (φ : CNF n) →
               (cleanPS φ ≋ idPS) ⇔
               (set0ˢ (ancillas φ) ⟦ circuit φ ⟧ ≋ set0ˢ (ancillas φ) idPS)
cleanPS⇔set0 φ = cleanPS-identity⇔unsat φ ⟨⇔⟩ sym⇔ (hardness-set0 φ)

-- ... and, on every input, the specification
-- |x⟩|a⟩|t⟩ ↦ |x⟩|a⟩|t ⊕ φ(x)⟩: on an ancilla the netlist leaves the 0
-- it was given, and the xor restores the input; elsewhere the inputs
-- and the target were never zeroed.

cleanFun-spec : (φ : CNF n) (x : Assign (wires φ)) →
                ∀ w → cleanFun φ x w ≡
                      (x [ tgt φ ≔ x (tgt φ) xor
                                   ⟦ φ ⟧ᶠ (λ v → x (inputs φ v)) ]) w
cleanFun-spec {n} φ x w = by (anc? a w)
  where
  s : ℕ
  s = nodes (cnf φ)

  a : Fin (suc s) → Fin (wires φ)
  a = ancillas φ

  t : Fin (wires φ)
  t = tgt φ

  z : Assign (wires φ)
  z = zeroˢ a x

  b : Bool
  b = x t xor ⟦ φ ⟧ᶠ (λ v → x (inputs φ v))

  z-t : z t ≡ x t
  z-t = zeroˢ-off a x (λ i → anc≢tgtʷ n s i)

  z-inp : ∀ v → z (inputs φ v) ≡ x (inputs φ v)
  z-inp v = zeroˢ-off a x (λ i e → inp≢ancʷ n s v i (sym e))

  run-z : ∀ u → runᴺ (netlist φ) z u ≡ (z [ t ≔ b ]) u
  run-z u = trans (netlist-correct φ z (clean-zeroˢ a x) u)
                  (cong (λ c → (z [ t ≔ c ]) u)
                        (cong₂ _xor_ z-t (⟦⟧ᶠ-cong φ z-inp)))

  by : (d : Dec (∃ λ i → a i ≡ w)) →
       (if does d then runᴺ (netlist φ) z w xor x w
        else runᴺ (netlist φ) z w) ≡ (x [ t ≔ b ]) w
  by (yes (i , e)) =
    trans (cong (_xor x w) (trans (run-z w) (trans (≔-there z b w≢t) z-w)))
          (sym (≔-there x b w≢t))
    where
    w≢t : w ≢ t
    w≢t e′ = anc≢tgtʷ n s i (trans e e′)

    z-w : z w ≡ false
    z-w = trans (cong z (sym e)) (clean-zeroˢ a x i)
  by (no ne)       =
    trans (run-z w) (≔-agree z x t b (zeroˢ-off a x (λ i e → ne (i , e))))

cleanPS-spec : (φ : CNF n) → cleanPS φ ≋ circuitˢ φ
cleanPS-spec φ =
  computes-≋ (cleanPS φ) (circuitˢ φ)
    (computes-≗ (cleanPS φ) (cleanFun-spec φ) (cleanPS-computes φ))
    (circuitˢ-computes φ)


------------------------------------------------------------------------
-- The prepared miter of two netlists

miterPS : (a : Fin j → Fin n) (gs hs : List (NCT n)) →
          PathSum n (norm (expandᴺ (miterᴺ gs hs)))
                    (paths (expandᴺ (miterᴺ gs hs)))
miterPS a gs hs = prepared a ⟦ expandᴺ (miterᴺ gs hs) ⟧

miterPS-computes : (a : Fin j → Fin n) (gs hs : List (NCT n)) →
                   miterPS a gs hs computes prepFun a (runᴺ (miterᴺ gs hs))
miterPS-computes a gs hs =
  prepared-computes a ⟦ expandᴺ (miterᴺ gs hs) ⟧
                    (expandᴺ-computes (miterᴺ gs hs))

-- It is the identity exactly when the netlists are equivalent on the
-- clean inputs.

miterPS-identity⇔ : (a : Fin j → Fin n) (gs hs : List (NCT n)) →
                    (miterPS a gs hs ≋ idPS) ⇔ Equivalentᴺ a gs hs
miterPS-identity⇔ a gs hs =
  computes-identity⇔ (miterPS a gs hs) (miterPS-computes a gs hs)
  ⟨⇔⟩ prepFun-identity⇔ a (runᴺ-cong (miterᴺ gs hs))
  ⟨⇔⟩ sym⇔ (miter⇔ a gs hs)

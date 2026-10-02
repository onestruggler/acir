------------------------------------------------------------------------
-- Presentations of groups
--
-- Compatible signatures, and composition of signed path-sums (Amy,
-- QPL 2018, definition 2.6 and proposition 2.7)
--
-- Definition 2.6 composes the output |f(x,y)⟩ of ξ with the input |x′⟩
-- of ξ′ by substituting fᵢ for x′ᵢ.  Where x′ᵢ is a constant b there is
-- nothing to substitute for, and composing "a variable fᵢ(x,y) = xⱼ
-- with a constant state x′ᵢ = b" is "effectively post-selecting on
-- xⱼ = b".  So the paper composes only compatible signatures: |f(x,y)⟩
-- is compatible with |x′⟩ "if and only if for every i, either x′ᵢ is a
-- variable or x′ᵢ = b = fᵢ(x,y)".
--
-- Compatibility, three ways.
--
-- * As the paper states it (SynCompatible ξ σ′): every output on a wire
--   σ′ makes the constant b is the constant polynomial b.  That is an
--   identity of Boolean polynomials, so of the stored integer
--   coefficients read modulo 2 (IsConst b f, i.e. f ≈[ 2 ] κ b).  In
--   the dense representation a polynomial is its table of 2^(n+m)
--   coefficients, and the check inspects every entry: the constant
--   coefficient must be b modulo 2 and every other one even
--   (synCompatible?, by PathSum.Polynomial.Decidable's _≈?[_]_).  The
--   paper writes a path-sum with its constants inline, so its condition
--   is this check made on PathSum.Signature's inline σ ξ.  This
--   formalisation also lets a signed path-sum store polynomials that
--   still mention the variable of a constant wire; on such a stored ξ
--   the same check is sufficient (syn⇒path) but not necessary
--   (path⇏syn) -- a fact about the representation used here, not about
--   the paper.
-- * Along every path (PathCompatible ξ σ′): from every input ξ's
--   signature admits, every path's output carries σ′'s constants.
--   (Every path carries the amplitude ζ^P/√2^k, never 0, so "on every
--   path of non-zero amplitude" is "on every path".)  By Möbius
--   inversion modulo 2 (PathSum.Mobius) an output takes the value b at
--   every point exactly when it is b coefficient by coefficient, so
--   this is exactly the paper's notion, on the path-sum written with
--   its constants inline (path⇔syn), and decidable (pathCompatible?).
-- * By the operator (Compatible ξ σ′): the range of U_ξ lies in the
--   span of the basis states σ′ admits, i.e. every entry of U_ξ to an
--   output σ′ does not admit vanishes.  Along every path implies it
--   (path⇒range), but not conversely, since paths into a forbidden
--   output may cancel: PathSum.Compose.Counterexample's projection
--   P₀ = |0⟩⟨0| maps everything into |0⟩, yet its path from |1⟩ outputs
--   1 (range⇏path).  It is decidable too, by brute force over every
--   entry (compatible?) -- decidability as such is elementary; footnote
--   1's point, that it is hard, is PathSum.Signature.Clean.
--
-- Only the third is a property of the operator U_ξ, which definition
-- 2.3 says is all a path-sum means: it passes along ≋ˢ
-- (Compatible-≋ˢ), while P₀ written with output 0, P₀′, is equivalent
-- to P₀ and compatible with the constant 0 syntactically although P₀
-- is not even along every path (path-not-invariant).
--
-- With no constants on the right everything is compatible
-- (compatible-vars, syn-compatible-vars), as PathSum.Compose's header
-- says of its path-sums.
--
-- Composition (_∘ˢ_) is PathSum.Compose's _∘ᴾ_ on the path-sums, with
-- the left signature: ξ′'s constants have nothing substituted for them,
-- and compatibility is what checks them.  It is defined for every pair;
-- the paper's composite is its restriction to compatible pairs, which
-- is computable, compatibility in the paper's sense being decidable.
--
-- Proposition 2.7, U_{ξ′∘ξ} = U_ξ′ U_ξ, holds as soon as the range of
-- U_ξ lies where ξ′ is defined (prop-2-7ˢ), the product being the
-- matrix product _⊙_ of PathSum.Compose.Matrix and the identity exact
-- on unnormalised entries, as there.  The proof is
-- PathSum.Compose.Matrix's prop-2-7 for the two path-sums, plus the
-- observation that the entries U_ξ(x,w) at the w σ′ does not admit --
-- where U_ξ′ is 0 but the path-sum ξ′ need not be -- vanish.  The
-- converse holds too: compatibility is exactly what makes proposition
-- 2.7 hold for every ξ′ with signature σ′, and already for the
-- identity with that signature (compatible⇔prop-2-7,
-- prop-2-7⇒compatible).  So the range form is the weakest hypothesis
-- under which the proposition holds, and the paper's own condition a
-- decidable sufficient one (prop-2-7-syn: proposition 2.7 under it).
-- The well-formedness half of proposition 2.7 is not restated here; it
-- is false even without constants (PathSum.Compose.Counterexample).
-- Under compatibility the composite reads ξ′ only through its operator,
-- so composition is well defined on operators (∘ˢ-congˡ).
--
-- Why compatibility is needed.  Read along the paths of ξ, the
-- composite sums ζ^{P(x,y)} U_ξ′(f(x,y), z) over every path y
-- (composite-paths), while the product keeps only the paths whose
-- output σ′ admits: it post-selects on f(x,y) carrying σ′'s constants
-- (product-postselects; under compatibility the two agree,
-- composite-postselects).  The paper's situation -- a variable output
-- composed with a constant input -- on one wire: the identity, whose
-- output f₁ = x₁ is a variable, followed by |0⟩ ↦ |0⟩ with the constant
-- input 0.  Written as the paper writes it, with the constant 0 as its
-- output (η′₀ = const0 ⊢ erase), the second has no input variable for
-- x₁ to be substituted for: the composite is the erasure |x⟩ ↦ |0⟩
-- (composite-erases), while the product is the projection onto |0⟩,
-- having post-selected on x₁ = 0 (product-projects-η).  They differ at
-- the entry from |1⟩ to |0⟩, so proposition 2.7 fails
-- (prop-2-7ˢ-fails-η).  Stored instead with the variable of its
-- constant wire as its output (ξ′₀ = const0 ⊢ idPS, equivalent to η′₀),
-- the composite substitutes x₁ for that variable and is the identity
-- (composite-ignores); the product is again the projection
-- (product-projects), and proposition 2.7 fails as well.  Neither pair
-- is compatible (prop-2-7ˢ-fails).  So the composite of an incompatible
-- pair is not even a function of the operators: ξ′₀ and η′₀ are
-- equivalent, but after the identity they compose to the identity and
-- to the erasure (∘ˢ-congˡ-fails).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Signature.Compose (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; if_then_else_)
open import Data.Bool.Properties using (∧-identityʳ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (all?)
open import Data.Fin.Subset using (inside)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; ∣m∣n⇒∣m+n; ∣m⇒∣-m; ∣⇒∣ᵤ)
open import Data.Integer.Properties using
  (+-identityʳ; +-identityˡ; +-inverseˡ; *-zeroˡ; *-zeroʳ; *-identityˡ;
   *-identityʳ)
  renaming (_≟_ to _≟ℤ_)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (suc) renaming (_+_ to _ℕ+_)
open import Data.Nat.Divisibility using (∣1⇒≡1)
open import Data.Product.Base using (_×_; _,_; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base using ([]; _∷_)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using
  (Dec; yes; no; ⌊_⌋; map; ¬?; _→?_)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.AmpLinear M₀ using (scale-+)
open import PathSum.Assign using ([_]ᶻ; _=ᵇ_; same; same-true)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out; idPS)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Counterexample M₀ using
  (Real; P₀; a₀; real-P₀; erase; aᵉ; real-erase)
open import PathSum.Compose.Laws M₀ using
  (amp-idPS-δ; amp-idPS-∘; amp-∘-idPS)
open import PathSum.Compose.Matrix M₀ using
  (_⊙_; prop-2-7; amp-⊛; row-collapse)
open import PathSum.Compose.Properties M₀ using (hits-same; prop-2-7ʳ)
open import PathSum.Compose.Sum M₀ using
  (if-cong; zpow-≡; scale-rot; scale-Σᴮ)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _≐_; _·ᴬ_; zpow; zpow-anti; zpow-0≢0ᴬ; Σᴮ; Σᴮ-cong;
   Σᴮ-0; rot; rot-map; rot-exp; rot-0; rot-0ᴬ; scale; scale-map;
   scale-injective)
open import PathSum.Denotation M₀ using
  (Assign; amp; hits; outBit; hits-elim; outBit-μ; eval-0ᴾ-val; amp-idPS)
open import PathSum.Mobius using (values⇒coefficientsᵐ)
open import PathSum.Polynomial using
  (Poly; Mon; 1ᵐ; _≟ᵐ_; x[_]; y[_]; 0ᴾ; κ; μ; eval; _-ᴾ_; _≈[_]_)
open import PathSum.Polynomial.Bind using (odd)
open import PathSum.Polynomial.Decidable using
  (_≈?[_]_; all-assignments?)
open import PathSum.Polynomial.Properties using
  (eval-κ; eval-−ᴾ; eval-·ᴾ; eval-≈; eval-cong; i∣0)
open import PathSum.Polynomial.Product using (_*ᴾ_; eval-*ᴾ; eval-μᴾ)
open import PathSum.Reduction (suc (suc (suc M₀))) using (½)
open import PathSum.Ring M₀ using (_⊛_; ⊛-cong; ⊛-zeroˡ; ⊛-zeroʳ)
open import PathSum.Signature M₀ using
  (Slot; var; cst; Signature; vars; slot; pin; Agrees; agrees?;
   vars-agrees; pin-agrees; Agrees-≗; Signed; _⊢_; sig; ps; ampˢ;
   ampˢ-in; ampˢ-out; ampˢ-≗ˣ; ampˢ-≗ᶻ; ⌜_⌝; ampˢ-⌜⌝; _≋ˢ_; scale-0ᴬ;
   ≋ˢ⇔on; ≋ˢ⇔≋; inline; outBit-inline)
open import PathSum.Syntactic M₀ using (outBit-∣)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  variable
    n k m k′ m′ j′ l′ : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-refl : {a : Amp} → a ≐ a
  ≐-refl _ = refl

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)

  -- The product of Z[ζ] in one factor; its implicit arguments cannot
  -- be recovered from _≐_, so they are given.

  ⊛-congˡ : (a a′ b : Amp) → a ≐ a′ → a ⊛ b ≐ a′ ⊛ b
  ⊛-congˡ a a′ b p = ⊛-cong {a = a} {a′ = a′} {b = b} {b′ = b} p ≐-refl

  ⊛-congʳ : (a b b′ : Amp) → b ≐ b′ → a ⊛ b ≐ a ⊛ b′
  ⊛-congʳ a b b′ p = ⊛-cong {a = a} {a′ = a} {b = b} {b′ = b′} ≐-refl p

  sym⇔ : {A B : Set} → A ⇔ B → B ⇔ A
  sym⇔ f = mk⇔ (Equivalence.from f) (Equivalence.to f)

  false≢true : false ≢ true
  false≢true ()

  -- A Boolean that is not true is false, and one that is not false is
  -- true.

  false-if : ∀ c → ¬ (c ≡ true) → c ≡ false
  false-if true  f = contradiction refl f
  false-if false _ = refl

  true-if : ∀ c → ¬ (c ≡ false) → c ≡ true
  true-if true  _ = refl
  true-if false f = contradiction refl f

  -- Outputs read the input only through its values.

  outBit-≗ˣ : (ξ : PathSum n k m) {x x′ : Assign n} (y : Assign m) →
              (∀ i → x i ≡ x′ i) → ∀ w → outBit ξ x y w ≡ outBit ξ x′ y w
  outBit-≗ˣ ξ {x} {x′} y h w =
    cong odd (eval-cong (out ξ w) {x} {x′} {y} {y} h (λ _ → refl))


------------------------------------------------------------------------
-- Reading an output modulo 2

private
  2∤1 : ¬ ((+ 2) ∣ 1ℤ)
  2∤1 h with ∣1⇒≡1 (∣⇒∣ᵤ h)
  ... | ()

-- An integer congruent to the bit b modulo 2 has parity b.

odd-of : ∀ e b → (+ 2) ∣ (e - [ b ]ᶻ) → odd e ≡ b
odd-of e b h = go ((+ 2) ∣? e) b h
  where
  shape : ∀ e → e + (- (e - 1ℤ)) ≡ 1ℤ
  shape = solve 1 (λ e → e :+ (:- (e :- con 1ℤ)) := con 1ℤ) refl

  go : (d : Dec ((+ 2) ∣ e)) (b : Bool) → (+ 2) ∣ (e - [ b ]ᶻ) →
       not ⌊ d ⌋ ≡ b
  go (yes _)  false _ = refl
  go (yes ev) true  h = contradiction
    (subst ((+ 2) ∣_) (shape e) (∣m∣n⇒∣m+n ev (∣m⇒∣-m h))) 2∤1
  go (no _)   true  _ = refl
  go (no od)  false h = contradiction (subst ((+ 2) ∣_) (+-identityʳ e) h) od


------------------------------------------------------------------------
-- Compatibility as the paper states it

-- f is the constant polynomial b: its coefficients, read modulo 2, are
-- b at the constant monomial and 0 elsewhere.

IsConst : Bool → Poly n m → Set
IsConst b f = f ≈[ + 2 ] κ [ b ]ᶻ

-- A variable takes any output; a constant b only the polynomial b.

Matches : Slot → Poly n m → Set
Matches var     f = ⊤
Matches (cst b) f = IsConst b f

SynCompatible : PathSum n k m → Signature n → Set
SynCompatible ξ σ′ = ∀ i → Matches (σ′ i) (out ξ i)

-- Decided coefficient by coefficient.

matches? : (s : Slot) (f : Poly n m) → Dec (Matches s f)
matches? var     f = yes tt
matches? (cst b) f = f ≈?[ + 2 ] κ [ b ]ᶻ

synCompatible? : (ξ : PathSum n k m) (σ′ : Signature n) →
                 Dec (SynCompatible ξ σ′)
synCompatible? ξ σ′ = all? (λ i → matches? (σ′ i) (out ξ i))

-- An output that is the constant b reads b on every path.

outBit-const : (ξ : PathSum n k m) (w : Fin n) (b : Bool) →
               IsConst b (out ξ w) → ∀ x y → outBit ξ x y w ≡ b
outBit-const ξ w b c x y = odd-of (eval (out ξ w) x y) b
  (subst ((+ 2) ∣_) (cong (λ v → eval (out ξ w) x y - v) (eval-κ [ b ]ᶻ x y))
         (eval-≈ (out ξ w) (κ [ b ]ᶻ) c x y))


------------------------------------------------------------------------
-- Compatibility along every path, and by the operator's range

PathCompatible : Signed n k m → Signature n → Set
PathCompatible ξ σ′ =
  ∀ x y → Agrees (sig ξ) x → Agrees σ′ (outBit (ps ξ) x y)

Compatible : Signed n k m → Signature n → Set
Compatible ξ σ′ = ∀ x z → ¬ Agrees σ′ z → ampˢ ξ x z ≐ 0ᴬ

-- The paper's condition on the path-sum as stored is sufficient,
-- whatever its own signature.

syn⇒path : (σ : Signature n) (ξ : PathSum n k m) (σ′ : Signature n) →
           SynCompatible ξ σ′ → PathCompatible (σ ⊢ ξ) σ′
syn⇒path σ ξ σ′ s x y _ i = fit (σ′ i) (s i)
  where
  fit : ∀ t → Matches t (out ξ i) → slot t (outBit ξ x y i) ≡ outBit ξ x y i
  fit var     _ = refl
  fit (cst b) c = sym (outBit-const ξ i b c x y)

-- On the path-sum with its constants inline, it is exactly
-- compatibility along every path: an output reading b at every point
-- is b coefficient by coefficient (Möbius inversion modulo 2).

path⇔syn : (σ : Signature n) (ξ : PathSum n k m) (σ′ : Signature n) →
           PathCompatible (σ ⊢ ξ) σ′ ⇔ SynCompatible (inline σ ξ) σ′
path⇔syn σ ξ σ′ = mk⇔ to from
  where
  to : PathCompatible (σ ⊢ ξ) σ′ → SynCompatible (inline σ ξ) σ′
  to p i = match (σ′ i) refl
    where
    match : ∀ t → σ′ i ≡ t → Matches t (out (inline σ ξ) i)
    match var     _ = tt
    match (cst b) e =
      values⇒coefficientsᵐ (+ 2) (out (inline σ ξ) i -ᴾ κ [ b ]ᶻ) value
      where
      reads : ∀ x y → outBit (inline σ ξ) x y i ≡ b
      reads x y = trans (outBit-inline σ ξ x y i)
        (sym (subst (λ t → slot t (outBit ξ (pin σ x) y i) ≡
                           outBit ξ (pin σ x) y i)
                    e (p (pin σ x) y (pin-agrees σ x) i)))

      value : ∀ x y → (+ 2) ∣ eval (out (inline σ ξ) i -ᴾ κ [ b ]ᶻ) x y
      value x y = subst ((+ 2) ∣_)
        (sym (trans (eval-−ᴾ (out (inline σ ξ) i) (κ [ b ]ᶻ) x y)
                    (cong (λ v → eval (out (inline σ ξ) i) x y - v)
                          (eval-κ [ b ]ᶻ x y))))
        (outBit-∣ (inline σ ξ) x y i b (reads x y))

  from : SynCompatible (inline σ ξ) σ′ → PathCompatible (σ ⊢ ξ) σ′
  from s x y a = Agrees-≗ σ′
    (λ i → trans (outBit-inline σ ξ x y i) (outBit-≗ˣ ξ y a i))
    (syn⇒path σ (inline σ ξ) σ′ s x y a)

pathCompatible? : (ξ : Signed n k m) (σ′ : Signature n) →
                  Dec (PathCompatible ξ σ′)
pathCompatible? ξ σ′ = map (sym⇔ (path⇔syn (sig ξ) (ps ξ) σ′))
                           (synCompatible? (inline (sig ξ) (ps ξ)) σ′)

-- Along every path implies by the range: no path reaches an output σ′
-- does not admit.

path⇒range : (ξ : Signed n k m) (σ′ : Signature n) →
             PathCompatible ξ σ′ → Compatible ξ σ′
path⇒range {m = m} ξ σ′ p x z na = go (agrees? (sig ξ) x)
  where
  go : Dec (Agrees (sig ξ) x) → ampˢ ξ x z ≐ 0ᴬ
  go (no na₀) = ampˢ-out ξ na₀ z
  go (yes a)  = ampˢ-in ξ a z
    ∙ Σᴮ-cong (λ y i → cong (λ b → (if b then zpow (eval (phase (ps ξ)) x y)
                                    else 0ᴬ) i) (miss y))
    ∙ Σᴮ-0 {m}
    where
    miss : ∀ y → hits (ps ξ) x y z ≡ false
    miss y = false-if (hits (ps ξ) x y z) (λ h →
      na (Agrees-≗ σ′ (hits-elim (ps ξ) x y z h) (p x y a)))

-- By brute force over every entry.

compatible? : (ξ : Signed n k m) (σ′ : Signature n) → Dec (Compatible ξ σ′)
compatible? {n = n} ξ σ′ =
  all-assignments? {B = λ x → ∀ z → ¬ Agrees σ′ z → ampˢ ξ x z ≐ 0ᴬ}
    respˣ (λ x →
  all-assignments? {B = λ z → ¬ Agrees σ′ z → ampˢ ξ x z ≐ 0ᴬ}
    (respᶻ x) (λ z →
  ¬? (agrees? σ′ z) →? all? (λ i → ampˢ ξ x z i ≟ℤ 0ℤ)))
  where
  respˣ : ∀ {x x′ : Assign n} → (∀ i → x i ≡ x′ i) →
          (∀ z → ¬ Agrees σ′ z → ampˢ ξ x z ≐ 0ᴬ) →
          (∀ z → ¬ Agrees σ′ z → ampˢ ξ x′ z ≐ 0ᴬ)
  respˣ h c z na = ≐-sym (ampˢ-≗ˣ ξ h z) ∙ c z na

  respᶻ : ∀ x {z z′ : Assign n} → (∀ i → z i ≡ z′ i) →
          (¬ Agrees σ′ z → ampˢ ξ x z ≐ 0ᴬ) →
          (¬ Agrees σ′ z′ → ampˢ ξ x z′ ≐ 0ᴬ)
  respᶻ x h c na′ =
    ≐-sym (ampˢ-≗ᶻ ξ x h) ∙ c (λ a → na′ (Agrees-≗ σ′ h a))

-- Without constants on the right, everything is compatible.

syn-compatible-vars : (ξ : PathSum n k m) → SynCompatible ξ vars
syn-compatible-vars ξ i = tt

compatible-vars : (ξ : Signed n k m) → Compatible ξ vars
compatible-vars ξ x z na = contradiction (vars-agrees z) na


------------------------------------------------------------------------
-- Composition (definition 2.6)

-- PathSum.Compose's composite, with the left signature.

infixr 9 _∘ˢ_

_∘ˢ_ : Signed n k′ m′ → Signed n k m → Signed n (k ℕ+ k′) (m ℕ+ m′)
ξ′ ∘ˢ ξ = sig ξ ⊢ (ps ξ′ ∘ᴾ ps ξ)

-- Proposition 2.7 for a pair.

Prop-2-7 : Signed n k′ m′ → Signed n k m → Set
Prop-2-7 ξ′ ξ = ∀ x z → ampˢ (ξ′ ∘ˢ ξ) x z ≐ (ampˢ ξ′ ⊙ ampˢ ξ) x z

-- It holds when the range of ξ lies where ξ′ is defined: through
-- PathSum.Compose.Matrix's prop-2-7, the entries U_ξ(x,w) at the w that
-- σ′ does not admit vanish, and elsewhere U_ξ′ is the path-sum ξ′.

prop-2-7ˢ : (ξ′ : Signed n k′ m′) (ξ : Signed n k m) →
            Compatible ξ (sig ξ′) → Prop-2-7 ξ′ ξ
prop-2-7ˢ {n = n} ξ′ ξ c x z = go (agrees? (sig ξ) x)
  where
  go : Dec (Agrees (sig ξ) x) →
       ampˢ (ξ′ ∘ˢ ξ) x z ≐ (ampˢ ξ′ ⊙ ampˢ ξ) x z
  go (no na) = ampˢ-out (ξ′ ∘ˢ ξ) na z ∙ ≐-sym
    (Σᴮ-cong (λ w → ⊛-congˡ (ampˢ ξ x w) 0ᴬ (ampˢ ξ′ w z) (ampˢ-out ξ na w)
                    ∙ ⊛-zeroˡ (ampˢ ξ′ w z))
     ∙ Σᴮ-0 {n})
  go (yes a) = ampˢ-in (ξ′ ∘ˢ ξ) a z ∙ prop-2-7 (ps ξ′) (ps ξ) x z
               ∙ Σᴮ-cong term
    where
    term : ∀ w → amp (ps ξ) x w ⊛ amp (ps ξ′) w z ≐ ampˢ ξ x w ⊛ ampˢ ξ′ w z
    term w = cases (agrees? (sig ξ′) w)
      where
      cases : Dec (Agrees (sig ξ′) w) →
              amp (ps ξ) x w ⊛ amp (ps ξ′) w z ≐ ampˢ ξ x w ⊛ ampˢ ξ′ w z
      cases (yes a′) =
        ⊛-congˡ (amp (ps ξ) x w) (ampˢ ξ x w) (amp (ps ξ′) w z)
                (≐-sym (ampˢ-in ξ a w))
        ∙ ⊛-congʳ (ampˢ ξ x w) (amp (ps ξ′) w z) (ampˢ ξ′ w z)
                  (≐-sym (ampˢ-in ξ′ a′ z))
      cases (no na′) =
        ⊛-congˡ (amp (ps ξ) x w) 0ᴬ (amp (ps ξ′) w z)
                (≐-sym (ampˢ-in ξ a w) ∙ c x w na′)
        ∙ ⊛-zeroˡ (amp (ps ξ′) w z)
        ∙ ≐-sym (⊛-congʳ (ampˢ ξ x w) (ampˢ ξ′ w z) 0ᴬ (ampˢ-out ξ′ na′ z)
                 ∙ ⊛-zeroʳ (ampˢ ξ x w))

-- Read along the paths of ξ: the composite sums over every path ...

composite-paths : (ξ′ : Signed n k′ m′) (ξ : Signed n k m) (x z : Assign n) →
                  Agrees (sig ξ) x →
                  ampˢ (ξ′ ∘ˢ ξ) x z ≐
                  Σᴮ (λ y → rot (eval (phase (ps ξ)) x y)
                                (amp (ps ξ′) (outBit (ps ξ) x y) z))
composite-paths ξ′ ξ x z a =
  ampˢ-in (ξ′ ∘ˢ ξ) a z ∙ prop-2-7ʳ (ps ξ′) (ps ξ) x z

-- ... while the product keeps the paths whose output σ′ admits: it
-- post-selects on f(x,y) carrying σ′'s constants.

product-postselects : (ξ′ : Signed n k′ m′) (ξ : Signed n k m)
                      (x z : Assign n) → Agrees (sig ξ) x →
                      (ampˢ ξ′ ⊙ ampˢ ξ) x z ≐
                      Σᴮ (λ y → rot (eval (phase (ps ξ)) x y)
                                    (ampˢ ξ′ (outBit (ps ξ) x y) z))
product-postselects ξ′ ξ x z a =
  Σᴮ-cong (λ w → ⊛-congˡ (ampˢ ξ x w) (amp (ps ξ) x w) (ampˢ ξ′ w z)
                         (ampˢ-in ξ a w))
  ∙ Σᴮ-cong (λ w → amp-⊛ (ps ξ) x w (ampˢ ξ′ w z))
  ∙ row-collapse (ps ξ) x (λ w → ampˢ ξ′ w z)
                 (λ g h g≗h → ampˢ-≗ˣ ξ′ g≗h z)

-- Compatibility is exactly what proposition 2.7 needs: if it holds for
-- the identity with signature σ′, then nothing σ′ refuses is in the
-- range of ξ, the composite being ξ itself and the product ξ
-- post-selected.

prop-2-7⇒compatible : (ξ : Signed n k m) (σ′ : Signature n) →
                      Prop-2-7 (σ′ ⊢ idPS) ξ → Compatible ξ σ′
prop-2-7⇒compatible {n = n} {m = m} ξ σ′ h x z na = go (agrees? (sig ξ) x)
  where
  go : Dec (Agrees (sig ξ) x) → ampˢ ξ x z ≐ 0ᴬ
  go (no na₀) = ampˢ-out ξ na₀ z
  go (yes a)  =
    ampˢ-in ξ a z
    ∙ ≐-sym (amp-idPS-∘ (ps ξ) x z)
    ∙ ≐-sym (ampˢ-in ((σ′ ⊢ idPS) ∘ˢ ξ) a z)
    ∙ h x z
    ∙ product-postselects (σ′ ⊢ idPS) ξ x z a
    ∙ Σᴮ-cong (λ y → rot-map (eval (phase (ps ξ)) x y) (dead y)
                     ∙ rot-0ᴬ (eval (phase (ps ξ)) x y))
    ∙ Σᴮ-0 {m}
    where
    -- No path of ξ survives post-selection into z: either its output is
    -- refused, or it is not z.
    dead : ∀ y → ampˢ (σ′ ⊢ idPS) (outBit (ps ξ) x y) z ≐ 0ᴬ
    dead y = at (agrees? σ′ (outBit (ps ξ) x y))
      where
      f : Assign n
      f = outBit (ps ξ) x y

      at : Dec (Agrees σ′ f) → ampˢ (σ′ ⊢ idPS) f z ≐ 0ᴬ
      at (no na′) = ampˢ-out (σ′ ⊢ idPS) na′ z
      at (yes a′) = ampˢ-in (σ′ ⊢ idPS) a′ z ∙ amp-idPS-δ f z
        ∙ (λ i → cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i)
                      (false-if (same f z) (λ e →
                         na (Agrees-≗ σ′ (same-true f z e) a′))))

compatible⇔prop-2-7 : (ξ : Signed n k m) (σ′ : Signature n) →
                      Compatible ξ σ′ ⇔
                      (∀ {k′ m′} (ξ′ : PathSum n k′ m′) →
                       Prop-2-7 (σ′ ⊢ ξ′) ξ)
compatible⇔prop-2-7 ξ σ′ = mk⇔
  (λ c {_} {_} ξ′ → prop-2-7ˢ (σ′ ⊢ ξ′) ξ c)
  (λ h → prop-2-7⇒compatible ξ σ′ (h idPS))

-- Proposition 2.7 under the paper's own condition: the left path-sum,
-- written as the paper writes it with its constants inline, is
-- compatible with the right signature syntactically.

prop-2-7-syn : (ξ′ : Signed n k′ m′) (ξ : Signed n k m) →
               SynCompatible (inline (sig ξ) (ps ξ)) (sig ξ′) →
               Prop-2-7 ξ′ ξ
prop-2-7-syn ξ′ ξ s = prop-2-7ˢ ξ′ ξ (path⇒range ξ (sig ξ′)
  (Equivalence.from (path⇔syn (sig ξ) (ps ξ) (sig ξ′)) s))


------------------------------------------------------------------------
-- Compatibility and definition 2.3

-- Compatibility by the range is a property of the operator: it passes
-- along ≋ˢ.  (Along every path, and syntactically, it is not:
-- path-not-invariant below.)

Compatible-≋ˢ : (ξ : Signed n k m) (ζ : Signed n k′ m′) (σ′ : Signature n) →
                ξ ≋ˢ ζ → Compatible ξ σ′ → Compatible ζ σ′
Compatible-≋ˢ {k = k} {k′ = k′} ξ ζ σ′ e c x z na =
  scale-injective k (ampˢ ζ x z) 0ᴬ
    (≐-sym (e x z) ∙ scale-map k′ (c x z na) ∙ scale-0ᴬ k′
     ∙ ≐-sym (scale-0ᴬ k))

-- Under compatibility the composite is the post-selected sum ...

composite-postselects : (ξ′ : Signed n k′ m′) (ξ : Signed n k m)
                        (x z : Assign n) → Compatible ξ (sig ξ′) →
                        Agrees (sig ξ) x →
                        ampˢ (ξ′ ∘ˢ ξ) x z ≐
                        Σᴮ (λ y → rot (eval (phase (ps ξ)) x y)
                                      (ampˢ ξ′ (outBit (ps ξ) x y) z))
composite-postselects ξ′ ξ x z c a =
  prop-2-7ˢ ξ′ ξ c x z ∙ product-postselects ξ′ ξ x z a

private
  Σrot-scale : ∀ i (e : Assign m → ℤ) (a : Assign m → Amp) →
               scale i (Σᴮ (λ y → rot (e y) (a y))) ≐
               Σᴮ (λ y → rot (e y) (scale i (a y)))
  Σrot-scale i e a =
    scale-Σᴮ i (λ y → rot (e y) (a y))
    ∙ Σᴮ-cong (λ y → scale-rot i (e y) (a y))

-- ... so it reads ξ′ only through its operator: composing after
-- equivalent path-sums, both compatible, gives equivalent composites.

∘ˢ-congˡ : (ξ′ : Signed n k′ m′) (η′ : Signed n j′ l′) (ξ : Signed n k m) →
           Compatible ξ (sig ξ′) → Compatible ξ (sig η′) → ξ′ ≋ˢ η′ →
           (ξ′ ∘ˢ ξ) ≋ˢ (η′ ∘ˢ ξ)
∘ˢ-congˡ {n = n} {k′ = k′} {j′ = j′} {k = k} {m = m} ξ′ η′ ξ c c′ e x z =
  go (agrees? (sig ξ) x)
  where
  P : Assign m → ℤ
  P y = eval (phase (ps ξ)) x y

  f : Assign m → Assign n
  f y = outBit (ps ξ) x y

  go : Dec (Agrees (sig ξ) x) →
       scale (k ℕ+ j′) (ampˢ (ξ′ ∘ˢ ξ) x z) ≐
       scale (k ℕ+ k′) (ampˢ (η′ ∘ˢ ξ) x z)
  go (no na) =
    scale-map (k ℕ+ j′) (ampˢ-out (ξ′ ∘ˢ ξ) na z) ∙ scale-0ᴬ (k ℕ+ j′)
    ∙ ≐-sym (scale-0ᴬ (k ℕ+ k′))
    ∙ scale-map (k ℕ+ k′) (≐-sym (ampˢ-out (η′ ∘ˢ ξ) na z))
  go (yes a) =
    scale-map (k ℕ+ j′) (composite-postselects ξ′ ξ x z c a)
    ∙ ≐-sym (scale-+ k j′ (Σᴮ (λ y → rot (P y) (ampˢ ξ′ (f y) z))))
    ∙ scale-map k (Σrot-scale j′ P (λ y → ampˢ ξ′ (f y) z))
    ∙ scale-map k (Σᴮ-cong (λ y → rot-map (P y) (e (f y) z)))
    ∙ scale-map k (≐-sym (Σrot-scale k′ P (λ y → ampˢ η′ (f y) z)))
    ∙ scale-+ k k′ (Σᴮ (λ y → rot (P y) (ampˢ η′ (f y) z)))
    ∙ scale-map (k ℕ+ k′) (≐-sym (composite-postselects η′ ξ x z c′ a))


------------------------------------------------------------------------
-- Counterexamples

-- One wire, and the constant 0 on it.

const0 : Signature 1
const0 _ = cst false

private
  agrees0 : (x : Assign 1) → x zero ≡ false → Agrees const0 x
  agrees0 x e zero = sym e
  agrees0 x e (suc ())

  refuse0 : (x : Assign 1) → x zero ≡ true → ¬ Agrees const0 x
  refuse0 x e a = false≢true (trans (a zero) e)

  x₁ : Assign 1
  x₁ _ = true

-- Compatible by the range but not along every path: P₀ = |0⟩⟨0| maps
-- every column into |0⟩, but its path from |1⟩ outputs 1.

range⇏path : Compatible ⌜ P₀ ⌝ const0 × ¬ PathCompatible ⌜ P₀ ⌝ const0
range⇏path = range , path
  where
  vanish : ∀ b → a₀ b true ·ᴬ zpow 0ℤ ≐ 0ᴬ
  vanish true  i = *-zeroˡ (zpow 0ℤ i)
  vanish false i = *-zeroˡ (zpow 0ℤ i)

  range : Compatible ⌜ P₀ ⌝ const0
  range x z na = ampˢ-⌜⌝ P₀ x z ∙ real-P₀ x z
    ∙ (λ i → cong (λ c → (a₀ (x zero) c ·ᴬ zpow 0ℤ) i)
                  (true-if (z zero) (λ e → na (agrees0 z e))))
    ∙ vanish (x zero)

  path : ¬ PathCompatible ⌜ P₀ ⌝ const0
  path p = false≢true (trans (p x₁ y₀ (vars-agrees x₁) zero)
                             (outBit-μ P₀ x₁ y₀ zero x[ zero ] refl))
    where
    y₀ : Assign 1
    y₀ _ = false

-- Compatibility along every path, or syntactically, is not a property
-- of the operator.  P₀ is also |x⟩ ↦ ½ Σ_y (-1)^(xy) |0⟩, with output 0
-- (P₀′): equivalent to P₀, and compatible with the constant 0
-- syntactically, while P₀ is not even along every path.

P₀′ : PathSum 1 2 1
P₀′ = ⟨ phase P₀ , (λ _ → 0ᴾ) ⟩

private
  one : Amp
  one = zpow 0ℤ

  twice : ∀ a → a + a ≡ (+ 2) * a
  twice = solve 1 (λ a → a :+ a := con (+ 2) :* a) refl

  eval-P₀ : (x : Assign 1) (y : Assign 1) →
            eval (phase P₀) x y ≡ ½ * ([ x zero ]ᶻ * [ y zero ]ᶻ)
  eval-P₀ x y = trans (eval-·ᴾ ½ (μ x[ zero ] *ᴾ μ y[ zero ]) x y)
    (cong (½ *_) (trans (eval-*ᴾ (μ x[ zero ]) (μ y[ zero ]) x y)
                        (cong₂ _*_ (eval-μᴾ x[ zero ] x y)
                                   (eval-μᴾ y[ zero ] x y))))

  -- The two paths from b: ζ^0 + ζ^0 = 2 at b = 0, ζ^½ + ζ^0 = 0 at
  -- b = 1.
  paths : (b : Bool) →
          (zpow (½ * ([ b ]ᶻ * 1ℤ)) +ᴬ zpow (½ * ([ b ]ᶻ * 0ℤ))) ≐
          (if b then 0ℤ else + 2) ·ᴬ one
  paths false =
    (λ i → cong₂ _+_ (zpow-≡ (*-zeroʳ ½) i) (zpow-≡ (*-zeroʳ ½) i))
    ∙ (λ i → twice (one i))
  paths true  =
    (λ i → cong₂ _+_
      ((zpow-≡ (trans (*-identityʳ ½) (sym (+-identityˡ ½)))
        ∙ zpow-anti 0ℤ) i)
      (zpow-≡ (*-zeroʳ ½) i))
    ∙ (λ i → trans (+-inverseˡ (one i)) (sym (*-zeroˡ (one i))))

  hits-P₀′ : (x y z : Assign 1) →
             hits P₀′ x y z ≡ (false =ᵇ z zero)
  hits-P₀′ x y z = trans (hits-same P₀′ x y z)
    (trans (∧-identityʳ _)
           (cong (λ e → odd e =ᵇ z zero) (eval-0ᴾ-val x y)))

real-P₀′ : Real P₀′ a₀
real-P₀′ x z =
  Σᴮ-cong (λ y → if-cong (hits-P₀′ x y z) (zpow-≡ (eval-P₀ x y)))
  ∙ at (x zero) (z zero)
  where
  at : (b c : Bool) →
       ((if (false =ᵇ c) then zpow (½ * ([ b ]ᶻ * 1ℤ)) else 0ᴬ) +ᴬ
        (if (false =ᵇ c) then zpow (½ * ([ b ]ᶻ * 0ℤ)) else 0ᴬ)) ≐
       a₀ b c ·ᴬ one
  at b false = paths b
  at false true i = sym (*-zeroˡ (one i))
  at true  true i = sym (*-zeroˡ (one i))

path-not-invariant : ⌜ P₀ ⌝ ≋ˢ ⌜ P₀′ ⌝ ×
                     ¬ PathCompatible ⌜ P₀ ⌝ const0 ×
                     SynCompatible P₀′ const0
path-not-invariant =
  Equivalence.from (≋ˢ⇔≋ P₀ P₀′)
    (λ x z → scale-map 2 (real-P₀ x z ∙ ≐-sym (real-P₀′ x z))) ,
  proj₂ range⇏path ,
  (λ i γ → subst (λ v → (+ 2) ∣ (0ℤ - v)) (sym (κ0 γ)) i∣0)
  where
  κ0 : (γ : Mon 1 1) → κ 0ℤ γ ≡ 0ℤ
  κ0 γ = if-0 ⌊ γ ≟ᵐ 1ᵐ ⌋
    where
    if-0 : ∀ b → (if b then 0ℤ else 0ℤ) ≡ 0ℤ
    if-0 true  = refl
    if-0 false = refl

-- Along every path but not syntactically on the path-sum as stored: the
-- identity with the constant input 0 outputs x₁, which is 0 on every
-- input it admits but is not the polynomial 0; inlined, it is.

path⇏syn : PathCompatible (const0 ⊢ idPS) const0 ×
           ¬ SynCompatible (idPS {1}) const0 ×
           SynCompatible (inline const0 (idPS {1})) const0
path⇏syn = path , syn , Equivalence.to (path⇔syn const0 idPS const0) path
  where
  path : PathCompatible (const0 ⊢ idPS) const0
  path x y a zero    =
    trans (a zero) (sym (outBit-μ idPS x y zero x[ zero ] refl))
  path x y a (suc ())

  γ₁ : Mon 1 0
  γ₁ = inside ∷ [] , []

  syn : ¬ SynCompatible (idPS {1}) const0
  syn s = 2∤1 (s zero γ₁)

-- Composing without compatibility, in the paper's situation: a
-- variable output composed with a constant input.  On one wire, the
-- identity, whose output f₁ = x₁ is a variable, then |0⟩ ↦ |0⟩ with
-- the constant input 0 -- written as the paper writes it, with the
-- constant 0 as its output (η′₀), and stored with the variable of its
-- constant wire as its output (ξ′₀).

ξ₀ : Signed 1 0 0
ξ₀ = ⌜ idPS ⌝

η′₀ : Signed 1 0 0
η′₀ = const0 ⊢ erase

ξ′₀ : Signed 1 0 0
ξ′₀ = const0 ⊢ idPS

private
  after-idˢ : (ξ : Signed n k m) (x z : Assign n) (y : Assign 0) →
              rot (eval (phase (idPS {n})) x y)
                  (ampˢ ξ (outBit idPS x y) z) ≐ ampˢ ξ x z
  after-idˢ {n = n} ξ x z y =
    rot-exp {eval (phase (idPS {n})) x y} {0ℤ}
            (ampˢ ξ (outBit idPS x y) z) (eval-0ᴾ-val x y)
    ∙ rot-0 (ampˢ ξ (outBit idPS x y) z)
    ∙ ampˢ-≗ˣ ξ (λ i → outBit-μ idPS x y i x[ i ] refl) z

  x₀ : Assign 1
  x₀ _ = false

-- After the identity, the product of the operators is the second
-- operator; here that is |0⟩ ↦ |0⟩, the projection onto |0⟩, the
-- product having post-selected on x₁ = 0.

product-after-id : (ξ′ : Signed n k′ m′) →
                   ∀ x z → (ampˢ ξ′ ⊙ ampˢ ⌜ idPS ⌝) x z ≐ ampˢ ξ′ x z
product-after-id ξ′ x z =
  product-postselects ξ′ ⌜ idPS ⌝ x z (vars-agrees x)
  ∙ after-idˢ ξ′ x z (λ ())

product-projects-η : ∀ x z → (ampˢ η′₀ ⊙ ampˢ ξ₀) x z ≐ ampˢ η′₀ x z
product-projects-η = product-after-id η′₀

product-projects : ∀ x z → (ampˢ ξ′₀ ⊙ ampˢ ξ₀) x z ≐ ampˢ ξ′₀ x z
product-projects = product-after-id ξ′₀

-- The composites ignore the constant.  In the paper's form there is
-- no input variable to substitute x₁ for, and the composite is the
-- erasure |x⟩ ↦ |0⟩ ...

composite-erases : (η′₀ ∘ˢ ξ₀) ≋ˢ ⌜ erase ⌝
composite-erases x z =
  ampˢ-in (η′₀ ∘ˢ ξ₀) (vars-agrees x) z ∙ amp-∘-idPS erase x z
  ∙ ≐-sym (ampˢ-⌜⌝ erase x z)

-- ... and in the stored form x₁ is substituted for the variable of the
-- constant wire, and the composite is the identity.

composite-ignores : (ξ′₀ ∘ˢ ξ₀) ≋ˢ ξ₀
composite-ignores x z =
  ampˢ-in (ξ′₀ ∘ˢ ξ₀) (vars-agrees x) z ∙ amp-idPS-∘ idPS x z
  ∙ ≐-sym (ampˢ-⌜⌝ idPS x z)

-- So proposition 2.7 fails in the paper's form: the entry from |1⟩ to
-- |0⟩ is ζ⁰ for the erasure and 0 for the projection.

prop-2-7ˢ-fails-η : ¬ Prop-2-7 η′₀ ξ₀
prop-2-7ˢ-fails-η h = zpow-0≢0ᴬ
  (≐-sym (real-erase x₁ x₀ ∙ (λ i → *-identityˡ (zpow 0ℤ i)))
   ∙ ≐-sym (amp-∘-idPS erase x₁ x₀)
   ∙ ≐-sym (ampˢ-in (η′₀ ∘ˢ ξ₀) (vars-agrees x₁) x₀)
   ∙ h x₁ x₀ ∙ product-projects-η x₁ x₀
   ∙ ampˢ-out η′₀ (refuse0 x₁ refl) x₀)

-- It fails in the stored form too, and neither pair is compatible: the
-- identity's column at |1⟩ is |1⟩, which the constant 0 refuses.

prop-2-7ˢ-fails : ¬ Compatible ξ₀ const0 × ¬ Prop-2-7 ξ′₀ ξ₀
prop-2-7ˢ-fails = incompatible ,
                  (λ h → incompatible (prop-2-7⇒compatible ξ₀ const0 h))
  where
  incompatible : ¬ Compatible ξ₀ const0
  incompatible c = zpow-0≢0ᴬ
    (≐-sym (amp-idPS x₁) ∙ ≐-sym (ampˢ-⌜⌝ idPS x₁ x₁)
     ∙ c x₁ x₁ (refuse0 x₁ refl))

-- Nor is the composite of an incompatible pair a function of the
-- operators.  ξ′₀ and η′₀ are equivalent with the constant input 0,
-- but after the identity on one wire the first composite is the
-- identity and the second the erasure.

∘ˢ-congˡ-fails : ξ′₀ ≋ˢ η′₀ × ¬ ((ξ′₀ ∘ˢ ξ₀) ≋ˢ (η′₀ ∘ˢ ξ₀))
∘ˢ-congˡ-fails = same-operator , differ
  where
  -- From |0⟩ both reach |0⟩ alone.
  at0 : ∀ b c → b ≡ false →
        (if (b =ᵇ c) ∧ true then zpow 0ℤ else 0ᴬ) ≐ aᵉ b c ·ᴬ zpow 0ℤ
  at0 false true  refl i = sym (*-zeroˡ (zpow 0ℤ i))
  at0 false false refl i = sym (*-identityˡ (zpow 0ℤ i))

  same-operator : ξ′₀ ≋ˢ η′₀
  same-operator = Equivalence.from (≋ˢ⇔on const0 idPS erase) λ x z a →
    amp-idPS-δ x z ∙ at0 (x zero) (z zero) (sym (a zero))
    ∙ ≐-sym (real-erase x z)

  -- At |1⟩ the first composite has the entry ζ⁰ to |1⟩, the second 0.
  differ : ¬ ((ξ′₀ ∘ˢ ξ₀) ≋ˢ (η′₀ ∘ˢ ξ₀))
  differ h = zpow-0≢0ᴬ
    (≐-sym (amp-idPS x₁) ∙ ≐-sym (ampˢ-⌜⌝ idPS x₁ x₁)
     ∙ ≐-sym (composite-ignores x₁ x₁) ∙ h x₁ x₁
     ∙ ampˢ-in (η′₀ ∘ˢ ξ₀) (vars-agrees x₁) x₁
     ∙ amp-∘-idPS erase x₁ x₁ ∙ real-erase x₁ x₁
     ∙ (λ i → *-zeroˡ (zpow 0ℤ i)))

------------------------------------------------------------------------
-- Presentations of groups
--
-- Identity checking of Clifford+T circuits is as hard as
-- unsatisfiability: the reduction behind footnote 2 (Amy, QPL 2018,
-- section 4)
--
-- Footnote 2: were the normal forms of the calculus unique,
-- "equivalence checking of reversible Boolean circuits [would be] in
-- P.  As this problem is co-NP-complete, uniqueness of our normal forms
-- would indeed imply P = co-NP."  The plan of the formalisation is in
-- the header of PathSum.Hardness.CNF; PathSum.Hardness.Netlist reduces
-- unsatisfiability of CNF formulas to identity checking of reversible
-- circuits over {NOT, CNOT, Toffoli}.  Here the reversible circuits are
-- expanded into Clifford+T, and the reduction carried over to path-sums:
-- for every CNF formula φ over n variables,
--
--    ⟦ circuit φ ⟧ ≋[ ancillas φ ]₀* idPS  ⇔  φ is unsatisfiable   (hardness)
--
-- (PathSum.Ancillas: equivalence on the inputs whose ancillas are 0),
-- equivalently set0ˢ (ancillas φ) ⟦ circuit φ ⟧ ≋ set0ˢ (ancillas φ)
-- idPS, the ancillas read as the constant 0 as the paper reads them
-- (hardness-set0), and the same with the empty circuit in place of idPS
-- (hardness-[]: equivalence checking of two circuits).  So identity
-- checking of Clifford+T circuits with clean ancillas -- the question
-- the paper's verifier answers -- is at least as hard as
-- unsatisfiability, under a reduction of linear size.
--
-- The expansion (expandᴺ).  A Toffoli gate becomes PathSum.Toffoli's
-- seven-T circuit, a CNOT stays a CNOT, and a NOT becomes H R₁ H: X is
-- not a gate of {H, CNOT, R_k}, and H Z H = X, with two path variables
-- (PathSum.HiddenShift.Layers.Xᶜ).  H R₁ H flips its wire, with the
-- factor 2 = √2² of its two Hadamards (applyᴬ-X there, on columns, and
-- proposition 2.10 for {H, CNOT, R_k}), so it computes NOT in the sense
-- of PathSum.Classical (X-computes); and by proposition 2.7 a composite
-- of path-sums computing Boolean functions computes the composite
-- function, so the expanded circuit computes the netlist's function
-- (expandᴺ-computes).  No path-sum of a whole circuit is computed.
--
-- From functions to path-sums.  PathSum.Ancillas.computes⇒≋[]₀* turns
-- agreement of two computed functions on the clean inputs into
-- equivalence there; the converse holds too (≋[]₀*-agree): if ξ
-- computes F and ζ computes G and they are equivalent on the clean
-- inputs, then at a clean x the entry of ξ from x to F x is the unit,
-- up to normalisation, hence so is ζ's, hence G x = F x.  So
-- equivalence to the identity on the clean inputs is exactly the
-- netlist being the identity there (≋[]₀*⇔agree), which
-- PathSum.Hardness.Netlist.netlist-identity⇔unsat characterises.  In
-- general, for every netlist over {NOT, CNOT, Toffoli}, its expansion
-- is equivalent to the identity on the inputs clean on any family of
-- ancillas exactly when the netlist is the identity there
-- (expandᴺ-identity⇔), and with no ancillas ⟦ expandᴺ gs ⟧ ≋ idPS
-- exactly when the netlist is the identity on every input
-- (expandᴺ-≋id⇔): identity checking of reversible circuits reduces to
-- identity checking of Clifford+T circuits, with the linear overhead
-- of the expansion.
--
-- The specification.  The circuit also meets the specification
-- |x⟩|0⟩|t⟩ ↦ |x⟩|0⟩|t ⊕ φ(x)⟩ in the form of section 5.2: circuitˢ φ is
-- the classical path-sum that xors into the target the lift (lemma 2.5)
-- of φ written as a Boolean expression -- ¬a as 1 ⊕ a and a ∨ b as
-- ¬(¬a ∧ ¬b), so that the expression grows linearly -- and
--
--    ⟦ circuit φ ⟧ ≋[ ancillas φ ]₀* circuitˢ φ              (circuit-spec)
--
-- with the ancillas left clean (circuit-clean) and the set0 form
-- (circuit-set0).  The same holds for every Boolean formula e over
-- {var, constant, ¬, ∧, ∨} (oracleᶜ-spec, oracleᶜ-identity⇔, ...), a
-- CNF formula being one.
--
-- Resources, all linear in the formula (‖φ‖ = literal occurrences +
-- clauses): n + 2 lits + negs + 2 clauses + 3 ≤ n + 3‖φ‖ + 3 qubits
-- (PathSum.Hardness.Netlist.wires-exact, wires-bound); 4‖φ‖ + 4 path
-- variables, two for each Toffoli gate and each NOT (circuit-paths);
-- 14‖φ‖ T gates (circuit-tcount); 36 lits + 4 negs + 30 clauses + 9 ≤
-- 40‖φ‖ + 9 gates (circuit-length, circuit-length-bound).
--
-- What is not formalised.  The complexity classes: that
-- unsatisfiability is co-NP-complete (Cook and Levin), that the
-- reduction runs in polynomial time (it is a structurally recursive
-- function with an output of linear size; running time is not a formal
-- notion here), and the conclusion P = co-NP, which would combine this
-- reduction with PathSum.Expand.unique⇒no-expansion and with the
-- polynomial time of normalising by the rules of figure 2 (proposition
-- 3.2) -- no bound on time is formalised anywhere.  (Phase B,
-- PathSum.Hardness.Certificate to PathSum.Hardness.Blowup, gives the
-- certificates of inequivalence, the conditional under unique normal
-- forms, and what that hypothesis would force.)  The identity is
-- checked on the inputs whose ancillas are 0, as section 5.2 verifies
-- circuits with ancillas; off those inputs the netlist of an
-- unsatisfiable formula can fail to be the identity
-- (PathSum.Hardness.Example.dirty₀).  The footnote speaks of
-- equivalence of reversible circuits; identity checking, equivalence
-- with the empty circuit, is its special case (hardness-[]).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hardness (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _∨_; _xor_; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (0ℤ)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Nat.Base using (zero; _+_; _*_; _≤_)
open import Data.Nat.Properties using (m≤m+n; m≤n⇒∃[o]m+o≡n)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (∃; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Negation using (contradiction)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.AmpLinear M₀ using (scale-comm)
open import PathSum.Ancillas M₀ using
  (Clean; set0ˢ; _≋[_]₀*_; amp-agree₀; ≋[]₀*⇔set0ˢ; computes⇒≋[]₀*;
   clean-ancillas)
open import PathSum.Assign using
  (_[_≔_]; ≔-there; same; same-refl; same-true; same-intro)
open import PathSum.Base using (PathSum; idPS)
open import PathSum.CircuitSemantics M₀ using (δ; δ-resp)
open import PathSum.Classical M₀ using
  (_computes_; computing; amp-computes; classical; classical-computes;
   computes-≗; fun; setWire; fun-setWireᵉ; outBit-none; none;
   ⟦++⟧-computes; ⟦[]⟧-computes; ⟦CNOT⟧-computes)
open import PathSum.Compose.CRK M₀ using (norm-++)
open import PathSum.Compose.Laws M₀ using (amp-idPS-δ)
open import PathSum.CRK.Circuit M using (paths≡norm)
open import PathSum.CRK.Path M₀ using (CNOT; Circuit; ⟦_⟧; norm; paths)
open import PathSum.CRK.Semantics M₀ using (prop-2-10)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; zpow; scale; scale-map; scale-injective; zpow-0≢0ᴬ)
open import PathSum.Denotation M₀ using (Assign; amp; outBit; _≋_)
open import PathSum.Hardness.CNF using
  (Formula; var; cst; ¬ᶠ_; _∧ᶠ_; _∨ᶠ_; ⟦_⟧ᵇ; nodes; CNF; ⟦_⟧ᶠ; cnf; ⟦cnf⟧;
   Unsatisfiable; lits; negs; clauses; ‖_‖; negs≤lits)
open import PathSum.Hardness.Netlist using
  (NCT; X; gate; flip; runᴺ; flip-cong; flip-flip; nots; toffolisᴺ;
   cnotsᴺ; Width; inpʷ; ancʷ; tgtʷ; anc≢tgtʷ; oracle; oracle-correct;
   oracle-identity⇔; wires; inputs; ancillas; tgt; netlist;
   netlist-correct; netlist-identity⇔unsat; netlist-nots;
   netlist-toffolis; netlist-cnots)
open import PathSum.HiddenShift.Layers M₀ using (Xᶜ; applyᴬ-X)
open import PathSum.Polynomial using (x[_])
open import PathSum.Polynomial.Boolean using
  (BExp; ⟦_⟧ᵉ; lit; _⊕ᵉ_; _∧ᵉ_; liftᵉ)
  renaming (var to varᵉ)
open import PathSum.Reversible using (ccx; cx; recover)
open import PathSum.Toffoli M₀ using (tof; tof-computes)
open import PathSum.Toffoli.Netlist M₀ using (tcount; tcount-++)

private
  variable
    n N k m k′ m′ j : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)

  -- Chaining equivalences of statements.

  infixr 5 _⟨⇔⟩_

  _⟨⇔⟩_ : {A B C : Set} → A ⇔ B → B ⇔ C → A ⇔ C
  f ⟨⇔⟩ g = mk⇔ (λ a → Equivalence.to g (Equivalence.to f a))
                (λ c → Equivalence.from f (Equivalence.from g c))

  sym⇔ : {A B : Set} → A ⇔ B → B ⇔ A
  sym⇔ f = mk⇔ (Equivalence.from f) (Equivalence.to f)


------------------------------------------------------------------------
-- NOT over Clifford+T

-- A basis column read at a flipped output is the column of the flipped
-- input.

private
  bool-≡ : ∀ {a b} → (a ≡ true → b ≡ true) → (b ≡ true → a ≡ true) → a ≡ b
  bool-≡ {true}  {true}  f g = refl
  bool-≡ {true}  {false} f g = sym (f refl)
  bool-≡ {false} {true}  f g = g refl
  bool-≡ {false} {false} f g = refl

  same-flip : (w : Fin n) (x z : Assign n) →
              same x (flip w z) ≡ same (flip w x) z
  same-flip w x z = bool-≡
    (λ h → same-intro (flip w x) z (λ i →
       trans (flip-cong w (same-true x (flip w z) h) i) (flip-flip w z i)))
    (λ h → same-intro x (flip w z) (λ i →
       trans (sym (flip-flip w x i))
             (flip-cong w (same-true (flip w x) z h) i)))

  δ-flip : (w : Fin n) (x z : Assign n) → δ x (flip w z) ≐ δ (flip w x) z
  δ-flip w x z i = cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i) (same-flip w x z)

-- H R₁ H computes NOT: by proposition 2.10 its amplitude from x to z is
-- the entry at z of H R₁ H applied to |x⟩, which is 2 = √2² times the
-- entry of |x⟩ at z with its bit flipped.

X-computes : (w : Fin n) → ⟦ Xᶜ w ⟧ computes flip w
X-computes w = computing λ x z →
  prop-2-10 (Xᶜ w) x z ∙ applyᴬ-X w (δ x) (δ-resp x) z
  ∙ scale-map 2 (δ-flip w x z)


------------------------------------------------------------------------
-- Netlists expanded into Clifford+T

-- A NOT as H R₁ H, a Toffoli gate as the seven-T circuit, a CNOT as
-- itself.

expandᴺ : List (NCT n) → Circuit n
expandᴺ []                              = []
expandᴺ (X w ∷ gs)                      = Xᶜ w ++ expandᴺ gs
expandᴺ (gate (ccx c₁ c₂ t p q r) ∷ gs) =
  tof c₁ c₂ t (recover p) (recover q) (recover r) ++ expandᴺ gs
expandᴺ (gate (cx c t p) ∷ gs)          = CNOT c t (recover p) ∷ expandᴺ gs

-- It computes the netlist's Boolean function.

expandᴺ-computes : (gs : List (NCT n)) → ⟦ expandᴺ gs ⟧ computes runᴺ gs
expandᴺ-computes []                              = ⟦[]⟧-computes
expandᴺ-computes (X w ∷ gs)                      =
  ⟦++⟧-computes (Xᶜ w) (expandᴺ gs) (X-computes w) (expandᴺ-computes gs)
expandᴺ-computes (gate (ccx c₁ c₂ t p q r) ∷ gs) =
  ⟦++⟧-computes (tof c₁ c₂ t (recover p) (recover q) (recover r))
                (expandᴺ gs)
                (tof-computes c₁ c₂ t (recover p) (recover q) (recover r))
                (expandᴺ-computes gs)
expandᴺ-computes (gate (cx c t p) ∷ gs)          =
  ⟦++⟧-computes (CNOT c t (recover p) ∷ []) (expandᴺ gs)
                (⟦CNOT⟧-computes c t (recover p)) (expandᴺ-computes gs)

-- Two Hadamards, hence two path variables, per NOT and per Toffoli
-- gate; seven T or T† gates per Toffoli gate; three gates per NOT,
-- fifteen per Toffoli gate, one per CNOT.

norm-expandᴺ : (gs : List (NCT n)) →
               norm (expandᴺ gs) ≡ nots gs * 2 + toffolisᴺ gs * 2
norm-expandᴺ []                              = refl
norm-expandᴺ (X w ∷ gs)                      =
  cong (λ a → suc (suc a)) (norm-expandᴺ gs)
norm-expandᴺ (gate (ccx c₁ c₂ t p q r) ∷ gs) =
  trans (norm-++ (tof c₁ c₂ t (recover p) (recover q) (recover r))
                 (expandᴺ gs))
  (trans (cong (2 +_) (norm-expandᴺ gs))
         (solve 2 (λ a b → con 2 :+ (a :* con 2 :+ b :* con 2)
                           := a :* con 2 :+ (con 1 :+ b) :* con 2)
                refl (nots gs) (toffolisᴺ gs)))
norm-expandᴺ (gate (cx c t p) ∷ gs)          = norm-expandᴺ gs

paths-expandᴺ : (gs : List (NCT n)) →
                paths (expandᴺ gs) ≡ nots gs * 2 + toffolisᴺ gs * 2
paths-expandᴺ gs = trans (paths≡norm (expandᴺ gs)) (norm-expandᴺ gs)

tcount-expandᴺ : (gs : List (NCT n)) → tcount (expandᴺ gs) ≡ toffolisᴺ gs * 7
tcount-expandᴺ []                              = refl
tcount-expandᴺ (X w ∷ gs)                      = tcount-expandᴺ gs
tcount-expandᴺ (gate (ccx c₁ c₂ t p q r) ∷ gs) =
  trans (tcount-++ (tof c₁ c₂ t (recover p) (recover q) (recover r))
                   (expandᴺ gs))
        (cong (7 +_) (tcount-expandᴺ gs))
tcount-expandᴺ (gate (cx c t p) ∷ gs)          = tcount-expandᴺ gs

length-expandᴺ : (gs : List (NCT n)) →
                 length (expandᴺ gs) ≡
                 nots gs * 3 + toffolisᴺ gs * 15 + cnotsᴺ gs
length-expandᴺ []                              = refl
length-expandᴺ (X w ∷ gs)                      =
  cong (3 +_) (length-expandᴺ gs)
length-expandᴺ (gate (ccx c₁ c₂ t p q r) ∷ gs) =
  trans (length-++ (tof c₁ c₂ t (recover p) (recover q) (recover r))
                   {expandᴺ gs})
  (trans (cong (15 +_) (length-expandᴺ gs))
         (solve 3 (λ a b c → con 15 :+ (a :* con 3 :+ b :* con 15 :+ c)
                             := a :* con 3 :+ (con 1 :+ b) :* con 15 :+ c)
                refl (nots gs) (toffolisᴺ gs) (cnotsᴺ gs)))
length-expandᴺ (gate (cx c t p) ∷ gs)          =
  trans (cong suc (length-expandᴺ gs))
        (solve 3 (λ a b c → con 1 :+ (a :* con 3 :+ b :* con 15 :+ c)
                            := a :* con 3 :+ b :* con 15 :+ (con 1 :+ c))
               refl (nots gs) (toffolisᴺ gs) (cnotsᴺ gs))


------------------------------------------------------------------------
-- Equivalence on the clean inputs, read off the functions computed

-- If ξ computes F and ζ computes G and they are equivalent on the clean
-- inputs, F and G agree there: ξ's entry from x to F x is the unit, up
-- to normalisation, so ζ's is too, so ζ's single hit from x is F x.

≋[]₀*-agree : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) (a : Fin j → Fin n)
              {F G : Assign n → Assign n} → ξ computes F → ζ computes G →
              ξ ≋[ a ]₀* ζ → ∀ x → Clean a x → ∀ w → F x w ≡ G x w
≋[]₀*-agree {n = n} {k = k} {k′ = k′} ξ ζ a {F} {G} cF cG eq x cl w =
  sym (same-true (G x) (F x) (hit (same (G x) (F x)) refl) w)
  where
  z : Assign n
  z = F x

  unit : δ z z ≐ zpow 0ℤ
  unit i = cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i) (same-refl z)

  back : δ z z ≐ δ (G x) z
  back = scale-injective k′ (δ z z) (δ (G x) z)
           (scale-injective k (scale k′ (δ z z)) (scale k′ (δ (G x) z))
             (≐-sym (scale-comm k′ k (δ z z))
              ∙ scale-map k′ (≐-sym (amp-computes cF x z))
              ∙ amp-agree₀ eq x z cl
              ∙ scale-map k (amp-computes cG x z)))

  hit : ∀ b → same (G x) z ≡ b → b ≡ true
  hit true  _ = refl
  hit false h = contradiction
    (λ i → trans (sym (unit i))
                 (trans (back i)
                        (cong (λ b → (if b then zpow 0ℤ else 0ᴬ) i) h)))
    zpow-0≢0ᴬ

-- With PathSum.Ancillas.computes⇒≋[]₀*: equivalence on the clean inputs
-- is agreement of the functions there.

≋[]₀*⇔agree : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) (a : Fin j → Fin n)
              {F G : Assign n → Assign n} → ξ computes F → ζ computes G →
              (ξ ≋[ a ]₀* ζ) ⇔ (∀ x → Clean a x → ∀ w → F x w ≡ G x w)
≋[]₀*⇔agree ξ ζ a cF cG =
  mk⇔ (≋[]₀*-agree ξ ζ a cF cG) (computes⇒≋[]₀* ξ ζ a cF cG)

-- The identity path-sum computes the identity.

idPS-computes : idPS {n} computes (λ x → x)
idPS-computes = computing amp-idPS-δ

-- So identity checking of the expansion of any netlist is identity
-- checking of the netlist: on the inputs clean on any family of
-- ancillas ...

expandᴺ-identity⇔ : (gs : List (NCT n)) (a : Fin j → Fin n) →
                    (⟦ expandᴺ gs ⟧ ≋[ a ]₀* idPS) ⇔
                    (∀ x → Clean a x → ∀ w → runᴺ gs x w ≡ x w)
expandᴺ-identity⇔ gs a =
  ≋[]₀*⇔agree ⟦ expandᴺ gs ⟧ idPS a (expandᴺ-computes gs) idPS-computes

-- ... and, with no ancillas, on every input.

no-ancillas : Fin 0 → Fin n
no-ancillas ()

expandᴺ-≋id⇔ : (gs : List (NCT n)) →
               (⟦ expandᴺ gs ⟧ ≋ idPS) ⇔ (∀ x w → runᴺ gs x w ≡ x w)
expandᴺ-≋id⇔ gs =
  sym⇔ (≋[]₀*⇔set0ˢ no-ancillas ⟦ expandᴺ gs ⟧ idPS)
  ⟨⇔⟩ expandᴺ-identity⇔ gs no-ancillas
  ⟨⇔⟩ mk⇔ (λ h x → h x (λ ())) (λ h x _ → h x)


------------------------------------------------------------------------
-- The specification

-- A formula as a Boolean expression on the wires: ¬a is 1 ⊕ a and a ∨ b
-- is ¬(¬a ∧ ¬b), each operand appearing once.

toBExp : (Fin n → Fin N) → Formula n → BExp N 0
toBExp ι (var v)    = varᵉ x[ ι v ]
toBExp ι (cst b)    = lit b
toBExp ι (¬ᶠ e)     = lit true ⊕ᵉ toBExp ι e
toBExp ι (e₁ ∧ᶠ e₂) = toBExp ι e₁ ∧ᵉ toBExp ι e₂
toBExp ι (e₁ ∨ᶠ e₂) =
  lit true ⊕ᵉ ((lit true ⊕ᵉ toBExp ι e₁) ∧ᵉ (lit true ⊕ᵉ toBExp ι e₂))

private
  de-morgan : ∀ a b → not (not a ∧ not b) ≡ a ∨ b
  de-morgan true  b     = refl
  de-morgan false true  = refl
  de-morgan false false = refl

⟦toBExp⟧ : (ι : Fin n → Fin N) (e : Formula n) (x : Assign N) (y : Assign 0) →
           ⟦ toBExp ι e ⟧ᵉ x y ≡ ⟦ e ⟧ᵇ (λ v → x (ι v))
⟦toBExp⟧ ι (var v)    x y = refl
⟦toBExp⟧ ι (cst b)    x y = refl
⟦toBExp⟧ ι (¬ᶠ e)     x y = cong not (⟦toBExp⟧ ι e x y)
⟦toBExp⟧ ι (e₁ ∧ᶠ e₂) x y =
  cong₂ _∧_ (⟦toBExp⟧ ι e₁ x y) (⟦toBExp⟧ ι e₂ x y)
⟦toBExp⟧ ι (e₁ ∨ᶠ e₂) x y =
  trans (cong₂ (λ a b → not (not a ∧ not b))
               (⟦toBExp⟧ ι e₁ x y) (⟦toBExp⟧ ι e₂ x y))
        (de-morgan (⟦ e₁ ⟧ᵇ (λ v → x (ι v))) (⟦ e₂ ⟧ᵇ (λ v → x (ι v))))

-- The target xor the formula of the inputs, and the classical path-sum
-- writing it into the target.

oracleᵉ : (e : Formula n) → BExp (Width n (nodes e)) 0
oracleᵉ {n} e = varᵉ x[ tgtʷ n (nodes e) ] ⊕ᵉ toBExp (inpʷ n (nodes e)) e

oracleˢ : (e : Formula n) → PathSum (Width n (nodes e)) 0 0
oracleˢ {n} e = classical (setWire (tgtʷ n (nodes e)) (liftᵉ (oracleᵉ e)))

fun-oracleˢ : (e : Formula n) (x : Assign (Width n (nodes e))) →
              ∀ w → fun (setWire (tgtʷ n (nodes e)) (liftᵉ (oracleᵉ e))) x w ≡
                    (x [ tgtʷ n (nodes e) ≔
                         x (tgtʷ n (nodes e)) xor
                         ⟦ e ⟧ᵇ (λ v → x (inpʷ n (nodes e) v)) ]) w
fun-oracleˢ {n} e x w =
  trans (fun-setWireᵉ (tgtʷ n (nodes e)) (oracleᵉ e) x w)
        (cong (λ b → (x [ tgtʷ n (nodes e) ≔ x (tgtʷ n (nodes e)) xor b ]) w)
              (⟦toBExp⟧ (inpʷ n (nodes e)) e x none))

-- It computes |x⟩|a⟩|t⟩ ↦ |x⟩|a⟩|t ⊕ e(x)⟩ on every input.

oracleˢ-computes : (e : Formula n) →
                   oracleˢ e computes
                   (λ x → x [ tgtʷ n (nodes e) ≔
                              x (tgtʷ n (nodes e)) xor
                              ⟦ e ⟧ᵇ (λ v → x (inpʷ n (nodes e) v)) ])
oracleˢ-computes {n} e =
  computes-≗ (oracleˢ e) (fun-oracleˢ e)
    (classical-computes (setWire (tgtʷ n (nodes e)) (liftᵉ (oracleᵉ e))))


------------------------------------------------------------------------
-- The oracle of a formula over Clifford+T

oracleᶜ : (e : Formula n) → Circuit (Width n (nodes e))
oracleᶜ e = expandᴺ (oracle e)

oracleᶜ-computes : (e : Formula n) → ⟦ oracleᶜ e ⟧ computes runᴺ (oracle e)
oracleᶜ-computes e = expandᴺ-computes (oracle e)

-- On the clean inputs it is the specification ...

oracleᶜ-spec : (e : Formula n) →
               ⟦ oracleᶜ e ⟧ ≋[ ancʷ n (nodes e) ]₀* oracleˢ e
oracleᶜ-spec {n} e =
  computes⇒≋[]₀* ⟦ oracleᶜ e ⟧ (oracleˢ e) (ancʷ n (nodes e))
    (oracleᶜ-computes e) (oracleˢ-computes e) (oracle-correct e)

-- ... and it leaves the ancillas clean ...

oracleᶜ-clean : (e : Formula n) → ∀ x z → Clean (ancʷ n (nodes e)) x →
                (i : Fin (suc (nodes e))) → z (ancʷ n (nodes e) i) ≡ true →
                amp ⟦ oracleᶜ e ⟧ x z ≐ 0ᴬ
oracleᶜ-clean {n} e = clean-ancillas (ancʷ n (nodes e)) (oracleᶜ-spec e) out0
  where
  out0 : ∀ x (y : Assign 0) → Clean (ancʷ n (nodes e)) x →
         ∀ i → outBit (oracleˢ e) x y (ancʷ n (nodes e) i) ≡ false
  out0 x y cl i =
    trans (outBit-none (oracleˢ e) x y (ancʷ n (nodes e) i))
    (trans (fun-oracleˢ e x (ancʷ n (nodes e) i))
    (trans (≔-there x _ (anc≢tgtʷ n (nodes e) i)) (cl i)))

-- ... and with the ancillas read as 0 on both sides it is equivalent to
-- the specification.

oracleᶜ-set0 : (e : Formula n) →
               set0ˢ (ancʷ n (nodes e)) ⟦ oracleᶜ e ⟧ ≋
               set0ˢ (ancʷ n (nodes e)) (oracleˢ e)
oracleᶜ-set0 {n} e =
  Equivalence.to (≋[]₀*⇔set0ˢ (ancʷ n (nodes e)) ⟦ oracleᶜ e ⟧ (oracleˢ e))
                 (oracleᶜ-spec e)

-- It is equivalent on the clean inputs to a path-sum that computes the
-- identity there exactly when e is false everywhere.

oracleᶜ-identity⇔ : (e : Formula n) (ζ : PathSum (Width n (nodes e)) k m)
                    {G : Assign (Width n (nodes e)) →
                         Assign (Width n (nodes e))} →
                    ζ computes G →
                    (∀ x → Clean (ancʷ n (nodes e)) x → ∀ w → G x w ≡ x w) →
                    (⟦ oracleᶜ e ⟧ ≋[ ancʷ n (nodes e) ]₀* ζ) ⇔
                    (∀ v → ⟦ e ⟧ᵇ v ≡ false)
oracleᶜ-identity⇔ {n = n} e ζ {G} cG idG =
  ≋[]₀*⇔agree ⟦ oracleᶜ e ⟧ ζ a (oracleᶜ-computes e) cG
  ⟨⇔⟩ swap ⟨⇔⟩ oracle-identity⇔ e
  where
  a : Fin (suc (nodes e)) → Fin (Width n (nodes e))
  a = ancʷ n (nodes e)

  swap : (∀ x → Clean a x → ∀ w → runᴺ (oracle e) x w ≡ G x w) ⇔
         (∀ x → Clean a x → ∀ w → runᴺ (oracle e) x w ≡ x w)
  swap = mk⇔ (λ h x cl w → trans (h x cl w) (idG x cl w))
             (λ h x cl w → trans (h x cl w) (sym (idG x cl w)))


------------------------------------------------------------------------
-- The reduction from CNF formulas

-- The Clifford+T circuit of a CNF formula -- its netlist, expanded --
-- and its specification.
--
-- The statements below are proved afresh about circuit φ rather than
-- instantiated from the oracle lemmas at cnf φ: the two circuits are
-- the same term only after unfolding, and Agda compares statements
-- about amplitudes (≐, ≋) of syntactically different circuits by
-- reducing both amplitudes, which cost over 200 s here.

circuit : (φ : CNF n) → Circuit (wires φ)
circuit φ = expandᴺ (netlist φ)

circuitˢ : (φ : CNF n) → PathSum (wires φ) 0 0
circuitˢ φ = oracleˢ (cnf φ)

circuit-computes : (φ : CNF n) → ⟦ circuit φ ⟧ computes runᴺ (netlist φ)
circuit-computes φ = expandᴺ-computes (netlist φ)

circuitˢ-computes : (φ : CNF n) →
                    circuitˢ φ computes
                    (λ x → x [ tgt φ ≔ x (tgt φ) xor
                                       ⟦ φ ⟧ᶠ (λ v → x (inputs φ v)) ])
circuitˢ-computes φ =
  computes-≗ (circuitˢ φ)
    (λ x w → cong (λ c → (x [ tgt φ ≔ x (tgt φ) xor c ]) w)
                  (⟦cnf⟧ φ (λ v → x (inputs φ v))))
    (oracleˢ-computes (cnf φ))

-- It meets the specification |x⟩|0⟩|t⟩ ↦ |x⟩|0⟩|t ⊕ φ(x)⟩ ...

circuit-spec : (φ : CNF n) → ⟦ circuit φ ⟧ ≋[ ancillas φ ]₀* circuitˢ φ
circuit-spec φ =
  computes⇒≋[]₀* ⟦ circuit φ ⟧ (circuitˢ φ) (ancillas φ)
    (circuit-computes φ) (circuitˢ-computes φ) (netlist-correct φ)

circuit-clean : (φ : CNF n) → ∀ x z → Clean (ancillas φ) x →
                (i : Fin (suc (nodes (cnf φ)))) → z (ancillas φ i) ≡ true →
                amp ⟦ circuit φ ⟧ x z ≐ 0ᴬ
circuit-clean {n} φ = clean-ancillas (ancillas φ) (circuit-spec φ) out0
  where
  out0 : ∀ x (y : Assign 0) → Clean (ancillas φ) x →
         ∀ i → outBit (circuitˢ φ) x y (ancillas φ i) ≡ false
  out0 x y cl i =
    trans (outBit-none (circuitˢ φ) x y (ancillas φ i))
    (trans (fun-oracleˢ (cnf φ) x (ancillas φ i))
    (trans (≔-there x _ (anc≢tgtʷ n (nodes (cnf φ)) i)) (cl i)))

circuit-set0 : (φ : CNF n) →
               set0ˢ (ancillas φ) ⟦ circuit φ ⟧ ≋
               set0ˢ (ancillas φ) (circuitˢ φ)
circuit-set0 φ =
  Equivalence.to (≋[]₀*⇔set0ˢ (ancillas φ) ⟦ circuit φ ⟧ (circuitˢ φ))
                 (circuit-spec φ)

-- ... and is the identity on the clean inputs exactly when φ is
-- unsatisfiable: against idPS, in the set0 form, and against the empty
-- circuit.

hardness : (φ : CNF n) →
           (⟦ circuit φ ⟧ ≋[ ancillas φ ]₀* idPS) ⇔ Unsatisfiable φ
hardness φ =
  ≋[]₀*⇔agree ⟦ circuit φ ⟧ idPS (ancillas φ) (circuit-computes φ)
              idPS-computes
  ⟨⇔⟩ netlist-identity⇔unsat φ

hardness-set0 : (φ : CNF n) →
                (set0ˢ (ancillas φ) ⟦ circuit φ ⟧ ≋ set0ˢ (ancillas φ) idPS) ⇔
                Unsatisfiable φ
hardness-set0 φ =
  sym⇔ (≋[]₀*⇔set0ˢ (ancillas φ) ⟦ circuit φ ⟧ idPS) ⟨⇔⟩ hardness φ

hardness-[] : (φ : CNF n) →
              (⟦ circuit φ ⟧ ≋[ ancillas φ ]₀* ⟦_⟧ {wires φ} []) ⇔
              Unsatisfiable φ
hardness-[] φ =
  ≋[]₀*⇔agree ⟦ circuit φ ⟧ (⟦_⟧ {wires φ} []) (ancillas φ)
              (circuit-computes φ) ⟦[]⟧-computes
  ⟨⇔⟩ netlist-identity⇔unsat φ


------------------------------------------------------------------------
-- The size of the reduction

-- Path variables: two per NOT and per Toffoli gate.  T gates: seven
-- per Toffoli gate.  Gates: three per NOT, fifteen per Toffoli gate,
-- one per CNOT.

circuit-paths : (φ : CNF n) → paths (circuit φ) ≡ 4 * ‖ φ ‖ + 4
circuit-paths φ =
  trans (paths-expandᴺ (netlist φ))
  (trans (cong₂ (λ a b → a * 2 + b * 2) (netlist-nots φ) (netlist-toffolis φ))
         (solve 1 (λ s → con 2 :* con 2 :+ con 2 :* s :* con 2
                         := con 4 :* s :+ con 4)
                refl ‖ φ ‖))

circuit-tcount : (φ : CNF n) → tcount (circuit φ) ≡ 14 * ‖ φ ‖
circuit-tcount φ =
  trans (tcount-expandᴺ (netlist φ))
  (trans (cong (_* 7) (netlist-toffolis φ))
         (solve 1 (λ s → con 2 :* s :* con 7 := con 14 :* s) refl ‖ φ ‖))

circuit-length : (φ : CNF n) →
                 length (circuit φ) ≡
                 36 * lits φ + 4 * negs φ + 30 * clauses φ + 9
circuit-length φ =
  trans (length-expandᴺ (netlist φ))
  (trans (cong₂ _+_ (cong₂ (λ a b → a * 3 + b * 15) (netlist-nots φ)
                                                    (netlist-toffolis φ))
                    (netlist-cnots φ))
         (solve 3 (λ L Q m → con 2 :* con 3 :+ con 2 :* (L :+ m) :* con 15 :+
                               (con 6 :* L :+ con 4 :* Q :+ con 3)
                             := con 36 :* L :+ con 4 :* Q :+ con 30 :* m :+
                                con 9)
                refl (lits φ) (negs φ) (clauses φ)))

-- Linear in ‖φ‖, since negs φ ≤ lits φ.

private
  ≤-via : ∀ {a b} c → b ≡ a + c → a ≤ b
  ≤-via {a} c refl = m≤m+n a c

circuit-length-bound : (φ : CNF n) → length (circuit φ) ≤ 40 * ‖ φ ‖ + 9
circuit-length-bound φ =
  subst (_≤ 40 * ‖ φ ‖ + 9) (sym (circuit-length φ))
        (≤-via (4 * d + 10 * clauses φ)
          (subst (λ L → 40 * (L + clauses φ) + 9 ≡
                        (36 * L + 4 * negs φ + 30 * clauses φ + 9) +
                        (4 * d + 10 * clauses φ))
                 (proj₂ split)
                 (solve 3 (λ Q d m → con 40 :* ((Q :+ d) :+ m) :+ con 9
                                     := (con 36 :* (Q :+ d) :+ con 4 :* Q :+
                                         con 30 :* m :+ con 9) :+
                                        (con 4 :* d :+ con 10 :* m))
                        refl (negs φ) d (clauses φ))))
  where
  split : ∃ λ d → negs φ + d ≡ lits φ
  split = m≤n⇒∃[o]m+o≡n (negs≤lits φ)

  d : ℕ
  d = proj₁ split

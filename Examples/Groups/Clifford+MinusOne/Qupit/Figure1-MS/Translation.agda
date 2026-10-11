------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure1-MS variant: C4 is Paper-V1 semi-MR with its sides swapped.
-- All other Figure 1 axioms and scalar conventions are unchanged.
--
-- The two translations between the rule set with -1 and Figure 1, and
-- the bookkeeping both directions of the isomorphism share.
--
-- The alphabets.  On one side (Syntactics) the scalars ω and -1 and the
-- gates H, S, CZ of Symplectic; on the other (Figure1.Syntactics) the
-- scalar ν = -ω and the gates H, S, CZ of Fig1Gate.  The translations
-- exchange the scalar generators,
--
--     fig :  ω ↦ ν^(p+1),   -1 ↦ ν^p,   gate ↦ gate,
--     new :  ν ↦ -1 • ω,                gate ↦ gate,
--
-- and are the identity on gates up to a change of constructor.
--
-- What is here.
--
--   * the relabelling of gates, and how fig, new meet the embeddings, the
--     shift and powers — all on the nose;
--   * the scalar algebra of the rule set with -1: ω and -1 are central,
--     ωᵖ = 1, (-1)² = 1, and so (-1 • ω)ᵏ is -1^(k mod 2) • ω^(k mod p);
--   * the shift ⇑ of a whole derivation of that rule set up one wire,
--     which Figure 1's cong↑ needs on this side;
--   * the two round trips on generators.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford+MinusOne.Qupit.Figure1-MS.Translation
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

import Data.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Nat.DivMod
  using (_%_ ; m≡m%n+[m/n]*n ; [m+kn]%n≡m%n ; n%n≡0 ; m<n⇒m%n≡m)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit using (⊤ ; tt)
import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_ ; _^'_ ; _ʷ ; wmap)
open import Word.Properties using (lemma-fʷ-w^n)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Construct.Base
  using (_⋄_⋄_ ; _∪_ ; [_]ₗ ; [_]ᵣ ; ConjRelʷ ; CommRel ; comm)
open import Presentation.Construct.Properties.Extension using (tw)

import Examples.Groups.Cyclic.Syntactics as Cy
import Examples.Groups.Clifford.Qupit.SemSHExp p-3 p-prime as SHE

import Examples.Groups.Clifford+MinusOne.Qupit.Syntactics
  p-3 p-prime g* g-gen as N
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1-MS.Syntactics
  p-3 p-prime g* g-gen as F

open import Examples.Groups.Symplectic.Simplified.Syntactics
  p-2 p-prime g* g-gen as NSim
open NSim.Symplectic
  using (SympGate ; H-gate ; S-gate ; CZ-gate)
  renaming (Gen to GenS ; gate₀ to gate₀ˢ ; gate₁ to gate₁ˢ ; gate₂ to gate₂ˢ
           ; _↥ to _↥ˢ ; _↑ to _↑ˢ)

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- The alphabets and their congruences

Alph : ℕ → Set
Alph = N.Alphabet

infix 4 _≈±_
_≈±_ : {n : ℕ} → Word (Alph n) → Word (Alph n) → Set
_≈±_ {n} = PB._≈_ (n N.Exact±,_===_)

infix 4 _≈ₑ_
_≈ₑ_ : {n : ℕ} → Word (N.ScalarGen ⊎ GenS n) → Word (N.ScalarGen ⊎ GenS n) → Set
_≈ₑ_ {n} = PB._≈_ (n N.Exact,_===_)

open F using (_≈ᶠ_) public

------------------------------------------------------------------------
-- Relabelling the gates

gate→ : SympGate m → F.Fig1Gate m
gate→ H-gate  = F.H-gate
gate→ S-gate  = F.S-gate
gate→ CZ-gate = F.CZ-gate

sym→fig : GenS n → F.Gen n
sym→fig (gate₀ˢ ())
sym→fig (gate₁ˢ h) = F.gate₁ (gate→ h)
sym→fig (gate₂ˢ h) = F.gate₂ (gate→ h)
sym→fig (x ↥ˢ)     = sym→fig x F.↥

-- A Symplectic circuit, as a Figure-1 circuit.
E : Word (GenS n) → Word (F.Gen n)
E = wmap sym→fig

------------------------------------------------------------------------
-- The two translations

-- New → Figure 1.
fig : Alph n → Word (F.Gen n)
fig (inj₁ (inj₁ _)) = F.ωˢ
fig (inj₁ (inj₂ x)) = [ sym→fig x ]ʷ
fig (inj₂ _)        = F.-1ˢ

-- Shifting a word of the new alphabet up one wire: the scalars do not
-- depend on the width and stay put, the gates shift.
shift± : Alph n → Alph (₁₊ n)
shift± (inj₁ (inj₁ s)) = inj₁ (inj₁ s)
shift± (inj₁ (inj₂ x)) = inj₁ (inj₂ (x ↥ˢ))
shift± (inj₂ t)        = inj₂ t

⇑ : Word (Alph n) → Word (Alph (₁₊ n))
⇑ = wmap shift±

-- Figure 1 → New.
new : F.Gen n → Word (Alph n)
new (F.gate₀ F.ν-gate)  = N.-ω±
new (F.gate₁ F.H-gate)  = [ inj₁ (inj₂ (gate₁ˢ H-gate)) ]ʷ
new (F.gate₁ F.S-gate)  = [ inj₁ (inj₂ (gate₁ˢ S-gate)) ]ʷ
new (F.gate₂ F.CZ-gate) = [ inj₁ (inj₂ (gate₂ˢ CZ-gate)) ]ʷ
new (y F.↥)             = ⇑ (new y)

-- Their extensions to words.
Fʷ : Word (Alph n) → Word (F.Gen n)
Fʷ = fig ʷ

Gʷ : Word (F.Gen n) → Word (Alph n)
Gʷ = new ʷ

------------------------------------------------------------------------
-- How the translations meet the embeddings, the shift and powers

-- new undoes the relabelling of a single gate, on the nose.
new-sym→fig : (x : GenS n) → new (sym→fig x) ≡ [ inj₁ (inj₂ x) ]ʷ
new-sym→fig (gate₀ˢ ())
new-sym→fig (gate₁ˢ H-gate)  = Eq.refl
new-sym→fig (gate₁ˢ S-gate)  = Eq.refl
new-sym→fig (gate₂ˢ CZ-gate) = Eq.refl
new-sym→fig (x ↥ˢ) rewrite new-sym→fig x = Eq.refl

-- … and so of a whole circuit.
G-E : (w : Word (GenS n)) → Gʷ (E w) ≡ N.⌜ w ⌝
G-E [ x ]ʷ  = new-sym→fig x
G-E ε       = Eq.refl
G-E (u • v) = Eq.cong₂ _•_ (G-E u) (G-E v)

-- fig of an embedded circuit is its relabelling.
F-⌜⌝ : (w : Word (GenS n)) → Fʷ (N.⌜ w ⌝) ≡ E w
F-⌜⌝ [ x ]ʷ  = Eq.refl
F-⌜⌝ ε       = Eq.refl
F-⌜⌝ (u • v) = Eq.cong₂ _•_ (F-⌜⌝ u) (F-⌜⌝ v)

-- The shift, on each side.
⇑-⌜⌝ : (w : Word (GenS n)) → ⇑ (N.⌜ w ⌝) ≡ N.⌜ w ↑ˢ ⌝
⇑-⌜⌝ [ x ]ʷ  = Eq.refl
⇑-⌜⌝ ε       = Eq.refl
⇑-⌜⌝ (u • v) = Eq.cong₂ _•_ (⇑-⌜⌝ u) (⇑-⌜⌝ v)

E-↑ : (w : Word (GenS n)) → E (w ↑ˢ) ≡ (E w) F.↑
E-↑ [ x ]ʷ  = Eq.refl
E-↑ ε       = Eq.refl
E-↑ (u • v) = Eq.cong₂ _•_ (E-↑ u) (E-↑ v)

G-↑ : (w : Word (F.Gen n)) → Gʷ (w F.↑) ≡ ⇑ (Gʷ w)
G-↑ [ x ]ʷ  = Eq.refl
G-↑ ε       = Eq.refl
G-↑ (u • v) = Eq.cong₂ _•_ (G-↑ u) (G-↑ v)

-- A map of letters commutes with powers.
wmap-^ : ∀ {A B : Set} (h : A → B) (w : Word A) (k : ℕ) →
         wmap h (w ^ k) ≡ (wmap h w) ^ k
wmap-^ h w ₀      = Eq.refl
wmap-^ h w (₁₊ ₀) = Eq.refl
wmap-^ h w (₂₊ k) = Eq.cong (wmap h w •_) (wmap-^ h w (₁₊ k))

ʷ-^ : ∀ {A B : Set} (h : A → Word B) (w : Word A) (k : ℕ) →
      (h ʷ) (w ^ k) ≡ ((h ʷ) w) ^ k
ʷ-^ h w k = lemma-fʷ-w^n k

------------------------------------------------------------------------
-- p is odd, and the residues that follow
--
-- The parity of a power of -1 is read off its exponent mod 2, so the
-- residues of p and p + 1 mod 2 (and of p + 1 mod p) are what the round
-- trips need.  Oddness is SemSHExp's p-odd.

p%2≡1 : p % 2 ≡ 1
p%2≡1 with SHE.p-odd
... | q , e =
  Eq.trans (Eq.cong (_% 2) (Eq.trans e (Eq.cong (1 Nat.+_) (NP.*-comm 2 q))))
           ([m+kn]%n≡m%n 1 q 2)

1+p%2≡0 : (₁₊ p) % 2 ≡ 0
1+p%2≡0 with SHE.p-odd
... | q , e = Eq.trans (Eq.cong (λ z → (₁₊ z) % 2) e)
                (Eq.trans (Eq.cong (_% 2) shape) ([m+kn]%n≡m%n 0 (₁₊ q) 2))
  where
  shape : ₁₊ (1 Nat.+ 2 Nat.* q) ≡ 0 Nat.+ ₁₊ q Nat.* 2
  shape = Eq.cong (λ z → ₂₊ z) (NP.*-comm 2 q)

1+p%p≡1 : (₁₊ p) % p ≡ 1
1+p%p≡1 = Eq.trans (Eq.cong (λ z → (1 Nat.+ z) % p) (Eq.sym (NP.*-identityˡ p)))
            (Eq.trans ([m+kn]%n≡m%n 1 1 p) (m<n⇒m%n≡m {m = 1} lt))
  where
  lt : 1 Nat.< p
  lt = Nat.s≤s (Nat.s≤s Nat.z≤n)

------------------------------------------------------------------------
-- The scalar algebra of the rule set with -1

module Algebra (n : ℕ) where

  open PB (n N.Exact±,_===_) public
  open PP (n N.Exact±,_===_) public
    using (word-setoid ; ^-+ ; ^^ ; ^-cong ; ^-• ; comm⇒pow-comm ; ε^k=ε)
  open SR word-setoid

  private
    module EB = PB (n N.Exact,_===_)
    module KB = PB N.Scalar-relation
    module MB = PB N.MinusOne-relation

  -- The two embeddings.
  lefts : ∀ {u v} → u ≈ₑ v → [ u ]ₗ ≈ [ v ]ₗ
  lefts PB.refl         = refl
  lefts (PB.sym h)      = sym (lefts h)
  lefts (PB.trans h h₁) = trans (lefts h) (lefts h₁)
  lefts (PB.cong h h₁)  = cong (lefts h) (lefts h₁)
  lefts PB.assoc        = assoc
  lefts PB.left-unit    = left-unit
  lefts PB.right-unit   = right-unit
  lefts (PB.axiom x)    = axiom (_⋄_⋄_.left x)

  rights : ∀ {u v} → MB._≈_ u v → [ u ]ᵣ ≈ [ v ]ᵣ
  rights PB.refl         = refl
  rights (PB.sym h)      = sym (rights h)
  rights (PB.trans h h₁) = trans (rights h) (rights h₁)
  rights (PB.cong h h₁)  = cong (rights h) (rights h₁)
  rights PB.assoc        = assoc
  rights PB.left-unit    = left-unit
  rights PB.right-unit   = right-unit
  rights (PB.axiom x)    = axiom (_⋄_⋄_.right x)

  -- … and the scalar factor of the exact layer, twice embedded.
  scalars : ∀ {u v} → KB._≈_ u v → [ [ u ]ₗ ]ₗ ≈ [ [ v ]ₗ ]ₗ
  scalars h = lefts (exact-lefts h)
    where
    exact-lefts : ∀ {u v} → KB._≈_ u v → EB._≈_ [ u ]ₗ [ v ]ₗ
    exact-lefts PB.refl         = PB.refl
    exact-lefts (PB.sym h)      = PB.sym (exact-lefts h)
    exact-lefts (PB.trans h h₁) = PB.trans (exact-lefts h) (exact-lefts h₁)
    exact-lefts (PB.cong h h₁)  = PB.cong (exact-lefts h) (exact-lefts h₁)
    exact-lefts PB.assoc        = PB.assoc
    exact-lefts PB.left-unit    = PB.left-unit
    exact-lefts PB.right-unit   = PB.right-unit
    exact-lefts (PB.axiom x)    = PB.axiom (_⋄_⋄_.left x)

  --------------------------------------------------------------------
  -- -1 is central

  -- Against a letter: a letter of the exact layer by the commutation
  -- axiom of the direct product, -1 itself trivially.
  -1-comm-letter : (a : Alph n) → [ a ]ʷ • N.-1± ≈ N.-1± • [ a ]ʷ
  -1-comm-letter (inj₁ x) = axiom (_⋄_⋄_.mid (comm x tt))
  -1-comm-letter (inj₂ tt) = refl

  -- Moving a word past a letter that commutes with every letter.
  module Central (c : Word (Alph n))
                 (c-comm : ∀ a → [ a ]ʷ • c ≈ c • [ a ]ʷ) where

    central : (w : Word (Alph n)) → w • c ≈ c • w
    central [ a ]ʷ  = c-comm a
    central ε       = trans left-unit (sym right-unit)
    central (u • v) =
      trans assoc
        (trans (cong refl (central v))
          (trans (sym assoc) (trans (cong (central u) refl) assoc)))

    central^ : (k : ℕ) (w : Word (Alph n)) → w • c ^ k ≈ c ^ k • w
    central^ ₀      w = trans right-unit (sym left-unit)
    central^ (₁₊ ₀) w = central w
    central^ (₂₊ k) w =
      trans (sym assoc)
        (trans (cong (central w) refl)
          (trans assoc (trans (cong refl (central^ (₁₊ k) w)) (sym assoc))))

  open Central N.-1± -1-comm-letter public
    renaming (central to -1-central ; central^ to -1^-central)

  --------------------------------------------------------------------
  -- ω is central

  -- A gate of the exact layer past ω: the conjugation axiom, conj
  -- being the constant ω.
  private
    ω-gate : (x : GenS n) →
             [ inj₁ (inj₂ x) ]ʷ • N.ω± ≈ N.ω± • [ inj₁ (inj₂ x) ]ʷ
    ω-gate x =
      axiom (_⋄_⋄_.left (_⋄_⋄_.mid (_∪_.left (ConjRelʷ.comm tt x))))

  ω-comm-letter : (a : Alph n) → [ a ]ʷ • N.ω± ≈ N.ω± • [ a ]ʷ
  ω-comm-letter (inj₁ (inj₁ tt)) = refl
  ω-comm-letter (inj₁ (inj₂ x))  = ω-gate x
  ω-comm-letter (inj₂ tt)        = sym (-1-comm-letter (inj₁ (inj₁ tt)))

  open Central N.ω± ω-comm-letter public
    renaming (central to ω-central ; central^ to ω^-central)

  --------------------------------------------------------------------
  -- Orders

  -- (-1)² = 1, from the cyclic relation of order 2.
  -1²≈ε : N.-1± • N.-1± ≈ ε
  -1²≈ε = rights (PB.axiom Cy.order)

  -- ωᵖ = 1, from the cyclic relation of order p in the exact layer.
  ω^p≈ε : N.ω± ^ p ≈ ε
  ω^p≈ε =
    trans (refl' (Eq.sym (Eq.trans (Eq.cong (wmap inj₁) (wmap-^ inj₁ N.ω p))
                                   (wmap-^ inj₁ [ inj₁ tt ]ʷ p))))
          (scalars (PB.trans (PB.sym (PP.^'=^ N.Scalar-relation {p} {N.ω}))
                             (PB.axiom Cy.order)))

  -- A word of finite order: its powers depend only on the exponent
  -- modulo the order.
  pow-mod : (w : Word (Alph n)) (k : ℕ) {{_ : Nat.NonZero k}} →
            w ^ k ≈ ε → ∀ j → w ^ j ≈ w ^ (j % k)
  pow-mod w k ord j = begin
    w ^ j
      ≡⟨ Eq.cong (w ^_) (m≡m%n+[m/n]*n j k) ⟩
    w ^ (j % k Nat.+ (j Nat./ k) Nat.* k)
      ≈⟨ ^-+ w (j % k) ((j Nat./ k) Nat.* k) ⟩
    w ^ (j % k) • w ^ ((j Nat./ k) Nat.* k)
      ≈⟨ cong refl (trans (refl' (Eq.cong (w ^_) (NP.*-comm (j Nat./ k) k)))
                     (trans (sym (^^ w k (j Nat./ k)))
                       (trans (^-cong (w ^ k) ε (j Nat./ k) ord)
                              (ε^k=ε (j Nat./ k))))) ⟩
    w ^ (j % k) • ε                       ≈⟨ right-unit ⟩
    w ^ (j % k)                           ∎

  -1^-mod : ∀ j → N.-1± ^ j ≈ N.-1± ^ (j % 2)
  -1^-mod = pow-mod N.-1± 2 -1²≈ε

  ω^-mod : ∀ j → N.ω± ^ j ≈ N.ω± ^ (j % p)
  ω^-mod = pow-mod N.ω± p ω^p≈ε

  --------------------------------------------------------------------
  -- The scalar -ω

  -- -ω is central …
  -ω-central : (w : Word (Alph n)) → w • N.-ω± ≈ N.-ω± • w
  -ω-central w =
    trans (sym assoc)
      (trans (cong (-1-central w) refl)
        (trans assoc (trans (cong refl (ω-central w)) (sym assoc))))

  -- … and its powers split.
  -ω^ : ∀ k → N.-ω± ^ k ≈ N.-1± ^ k • N.ω± ^ k
  -ω^ k = ^-• N.-1± N.ω± k (sym (-1-central N.ω±))

------------------------------------------------------------------------
-- Shifting a derivation of the rule set with -1 up one wire

private
  ⇑ₗₗ : (c : Word N.ScalarGen) → ⇑ {n} [ [ c ]ₗ ]ₗ ≡ [ [ c ]ₗ ]ₗ
  ⇑ₗₗ [ _ ]ʷ  = Eq.refl
  ⇑ₗₗ ε       = Eq.refl
  ⇑ₗₗ (c • d) = Eq.cong₂ _•_ (⇑ₗₗ c) (⇑ₗₗ d)

  ⇑ᵣ : (c : Word N.MinusOneGen) → ⇑ {n} [ c ]ᵣ ≡ [ c ]ᵣ
  ⇑ᵣ [ _ ]ʷ  = Eq.refl
  ⇑ᵣ ε       = Eq.refl
  ⇑ᵣ (c • d) = Eq.cong₂ _•_ (⇑ᵣ c) (⇑ᵣ d)

  ⇑-twist : (c : Word N.ScalarGen) (w : Word (GenS n)) →
            ⇑ [ [ c ]ₗ • [ w ]ᵣ ]ₗ ≡ [ [ c ]ₗ • [ w ↑ˢ ]ᵣ ]ₗ
  ⇑-twist c w = Eq.cong₂ _•_ (⇑ₗₗ c) (⇑-⌜⌝ w)

shift-ax : {a b : Word (Alph n)} → (n N.Exact±,_===_) a b → ⇑ a ≈± ⇑ b
-- The exact layer: its scalar relation is width-free; the conjugation
-- axiom is the same axiom for the shifted gate; a twisted relator is
-- the twisted relator of cong↑, whose correction is the same word.
shift-ax (_⋄_⋄_.left (_⋄_⋄_.left {u} {v} x)) =
  Eq.subst₂ (PB._≈_ _) (Eq.sym (⇑ₗₗ u)) (Eq.sym (⇑ₗₗ v))
            (PB.axiom (_⋄_⋄_.left (_⋄_⋄_.left x)))
shift-ax (_⋄_⋄_.left (_⋄_⋄_.right ()))
shift-ax (_⋄_⋄_.left (_⋄_⋄_.mid (_∪_.left (ConjRelʷ.comm tt x)))) =
  PB.axiom (_⋄_⋄_.left (_⋄_⋄_.mid (_∪_.left (ConjRelʷ.comm tt (x ↥ˢ)))))
shift-ax (_⋄_⋄_.left (_⋄_⋄_.mid (_∪_.right (tw {u} {v} r̄)))) =
  Eq.subst₂ (PB._≈_ _) (Eq.sym (⇑-⌜⌝ u)) (Eq.sym (⇑-twist (N.corr r̄) v))
            (PB.axiom (_⋄_⋄_.left (_⋄_⋄_.mid (_∪_.right (tw (N.CR.cong↑ r̄))))))
-- (-1)² = 1 is width-free.
shift-ax (_⋄_⋄_.right {u} {v} x) =
  Eq.subst₂ (PB._≈_ _) (Eq.sym (⇑ᵣ u)) (Eq.sym (⇑ᵣ v))
            (PB.axiom (_⋄_⋄_.right x))
-- -1 commutes with the shifted letter.
shift-ax (_⋄_⋄_.mid (comm (inj₁ s) tt)) =
  PB.axiom (_⋄_⋄_.mid (comm (inj₁ s) tt))
shift-ax (_⋄_⋄_.mid (comm (inj₂ x) tt)) =
  PB.axiom (_⋄_⋄_.mid (comm (inj₂ (x ↥ˢ)) tt))

lemma-shift : {a b : Word (Alph n)} → a ≈± b → ⇑ a ≈± ⇑ b
lemma-shift PB.refl         = PB.refl
lemma-shift (PB.sym h)      = PB.sym (lemma-shift h)
lemma-shift (PB.trans h h₁) = PB.trans (lemma-shift h) (lemma-shift h₁)
lemma-shift (PB.cong h h₁)  = PB.cong (lemma-shift h) (lemma-shift h₁)
lemma-shift PB.assoc        = PB.assoc
lemma-shift PB.left-unit    = PB.left-unit
lemma-shift PB.right-unit   = PB.right-unit
lemma-shift (PB.axiom x)    = shift-ax x

------------------------------------------------------------------------
-- The round trips on generators

-- On the new alphabet: ω and -1 come back as powers of -ω.
new-left-inv-gen : (a : Alph n) → [ a ]ʷ ≈± Gʷ (fig a)
new-left-inv-gen {n} (inj₁ (inj₁ tt)) = begin
  N.ω±                                     ≈⟨ sym left-unit ⟩
  ε • N.ω±
    ≈⟨ cong (refl' (Eq.cong (N.-1± ^_) (Eq.sym 1+p%2≡0)))
            (refl' (Eq.cong (N.ω± ^_) (Eq.sym 1+p%p≡1))) ⟩
  N.-1± ^ ((₁₊ p) % 2) • N.ω± ^ ((₁₊ p) % p)
    ≈⟨ cong (sym (-1^-mod (₁₊ p))) (sym (ω^-mod (₁₊ p))) ⟩
  N.-1± ^ ₁₊ p • N.ω± ^ ₁₊ p               ≈⟨ sym (-ω^ (₁₊ p)) ⟩
  N.-ω± ^ ₁₊ p                             ≡⟨ Eq.sym (ʷ-^ new F.ν (₁₊ p)) ⟩
  Gʷ F.ωˢ                                  ∎
  where
  open Algebra n
  open SR word-setoid
new-left-inv-gen {n} (inj₁ (inj₂ x)) = PB.refl' _ (Eq.sym (new-sym→fig x))
new-left-inv-gen {n} (inj₂ tt) = begin
  N.-1±                                    ≈⟨ sym right-unit ⟩
  N.-1± • ε
    ≈⟨ cong (refl' (Eq.cong (N.-1± ^_) (Eq.sym p%2≡1)))
            (refl' (Eq.cong (N.ω± ^_) (Eq.sym (n%n≡0 p)))) ⟩
  N.-1± ^ (p % 2) • N.ω± ^ (p % p)
    ≈⟨ cong (sym (-1^-mod p)) (sym (ω^-mod p)) ⟩
  N.-1± ^ p • N.ω± ^ p                     ≈⟨ sym (-ω^ p) ⟩
  N.-ω± ^ p                                ≡⟨ Eq.sym (ʷ-^ new F.ν p) ⟩
  Gʷ F.-1ˢ                                 ∎
  where
  open Algebra n
  open SR word-setoid

-- On Figure 1: ν comes back as ν^(2p+1).
fig-left-inv-gen : (y : F.Gen n) → [ y ]ʷ ≈ᶠ Fʷ (new y)
fig-left-inv-gen {n} (F.gate₀ F.ν-gate) = begin
  F.ν                                   ≈⟨ sym left-unit ⟩
  ε • F.ν                               ≈⟨ cong (sym (axiom (srel F.c0))) refl ⟩
  F.ν ^ (p Nat.+ p) • F.ν               ≈⟨ sym (^-+ F.ν (p Nat.+ p) 1) ⟩
  F.ν ^ (p Nat.+ p Nat.+ 1)             ≡⟨ Eq.cong (F.ν ^_) (exp p) ⟩
  F.ν ^ (p Nat.+ ₁₊ p)                  ≈⟨ ^-+ F.ν p (₁₊ p) ⟩
  F.-1ˢ • F.ωˢ                          ∎
  where
  open PB (F._F,_===_ n)
  open PP (F._F,_===_ n) using (word-setoid ; ^-+)
  open F using (srel)
  open SR word-setoid
  exp : ∀ q → q Nat.+ q Nat.+ 1 ≡ q Nat.+ ₁₊ q
  exp q = Eq.trans (NP.+-assoc q q 1) (Eq.cong (q Nat.+_) (NP.+-comm q 1))
fig-left-inv-gen (F.gate₁ F.H-gate)  = PB.refl
fig-left-inv-gen (F.gate₁ F.S-gate)  = PB.refl
fig-left-inv-gen (F.gate₂ F.CZ-gate) = PB.refl
fig-left-inv-gen (y F.↥) =
  PB.trans (F.lemma-cong↑ _ _ (fig-left-inv-gen y)) (f-⇑ (new y))
  where
  -- (fig ʷ) commutes with the shift, up to ν↑ ≈ ν on the scalar letters.
  ν^↑ : ∀ {m} (k : ℕ) → ((F.ν {m}) ^ k) F.↑ ≈ᶠ F.ν ^ k
  ν^↑ {m} k =
    PB.trans (PB.refl' _ (wmap-^ F._↥ F.ν k))
             (PP.^-cong (F._F,_===_ (₁₊ m)) (F.ν F.↑) F.ν k F.ν↑≈ν)

  f-⇑ : ∀ {m} (w : Word (Alph m)) → (Fʷ w) F.↑ ≈ᶠ Fʷ (⇑ w)
  f-⇑ [ inj₁ (inj₁ _) ]ʷ = ν^↑ (₁₊ p)
  f-⇑ [ inj₁ (inj₂ _) ]ʷ = PB.refl
  f-⇑ [ inj₂ _ ]ʷ        = ν^↑ p
  f-⇑ ε                  = PB.refl
  f-⇑ (u • v)            = PB.cong (f-⇑ u) (f-⇑ v)

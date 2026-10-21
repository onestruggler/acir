------------------------------------------------------------------------
-- Presentations of groups
--
-- Permutations of eight basis states as circuits, and the frame lemma.
--
-- A Coxeter word is a circuit of the presentation of Sₙ (Syntactics),
-- whose wires are read here as basis states: its generator on the
-- wires d, d + 1 is the transposition of the states d, d + 1, which a
-- circuit T d over any alphabet realises (Circuits T).  Given the
-- Coxeter relations for the circuits T d (a record, Coxeter), two
-- Coxeter words with the same permutation have equivalent circuits
-- (perm-complete): the presentation of S₈ is complete
-- (Symmetric.Presentation), and Pc carries its relations to the
-- Coxeter relations.  A word fixing the states below j is a word in
-- the T i with i ≥ j (stab), so a circuit b that those T i commute
-- with, conjugated by a Coxeter word, depends only on where the word
-- sends the states below j (frame≈).  frame ts sends the states
-- 0, 1, … to the distinct states ts.
--
-- The development of CCX+HH-3qubit-opus (its Perm and Frame) made
-- generic in the circuits T d.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Symmetric.CoxeterFrames where

open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ ; punchIn ; punchOut)
import Data.Fin.Properties as FinP
open import Data.Fin.Permutation as P
  using (Permutation′ ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; lift₀ ; remove ; inverseˡ ; inverseʳ ; lift₀-remove)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _≤_ ; _<_ ; z≤n ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Definitions using (_IsPresentationOf_)
open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
import Relation.Binary.Reasoning.Setoid as SR

import Examples.Groups.Symmetric.Syntactics as Sym
import Examples.Groups.Symmetric.Semantics as SymSem
import Examples.Groups.Symmetric.Interpretation as SymI
import Examples.Groups.Symmetric.Presentation as SymP
import Examples.Groups.Symmetric.Surjectivity as SymS
open Sym using (gate₀ ; gate₁ ; gate₂ ; _↥ ; σ-gate ; _VRel,_===_ ; srel ; cong↑ ; comm₁ ; comm₂ ; ω↑=ω)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Coxeter words

SG : ℕ → Set
SG = Sym.Gen

-- Words of S₈'s circuit presentation.
CW : Set
CW = Word (SG 8)

-- The lower wire of a generator, from offset o.
tr : ℕ → SG n → ℕ
tr o (gate₀ ())
tr o (gate₁ ())
tr o (gate₂ σ-gate) = o
tr o (g ↥)          = tr (suc o) g

tr-≥ : (o : ℕ) (g : SG n) → o ≤ tr o g
tr-≥ o (gate₀ ())
tr-≥ o (gate₁ ())
tr-≥ o (gate₂ σ-gate) = ℕP.≤-refl
tr-≥ o (g ↥)          = ℕP.≤-trans (ℕP.n≤1+n o) (tr-≥ (suc o) g)

tr-≤ : (o : ℕ) (g : SG n) → 2 + tr o g ≤ o + n
tr-≤ o (gate₀ ())
tr-≤ o (gate₁ ())
tr-≤ {suc (suc n)} o (gate₂ σ-gate) =
  Eq.subst (2 + o ≤_) (Eq.sym (Eq.trans (ℕP.+-suc o (suc n)) (Eq.cong suc (ℕP.+-suc o n))))
    (s≤s (s≤s (ℕP.m≤m+n o n)))
tr-≤ {suc n} o (g ↥) = Eq.subst (2 + tr (suc o) g ≤_) (Eq.sym (ℕP.+-suc o n)) (tr-≤ (suc o) g)

-- The inverse of a Coxeter word: its letters reversed.
inv : Word (SG n) → Word (SG n)
inv [ g ]ʷ   = [ g ]ʷ
inv ε       = ε
inv (u • v) = inv v • inv u

------------------------------------------------------------------------
-- The action on basis states

-- The circuit of w sends the basis state x to actₙ w x.
actₙ : Word (SG n) → Fin n → Fin n
actₙ w x = SymI.⟦ w ⟧ ⟨$⟩ˡ x

act : CW → Fin 8 → Fin 8
act = actₙ

act-• : (u v : Word (SG n)) (x : Fin n) → actₙ (u • v) x ≡ actₙ u (actₙ v x)
act-• u v x = Eq.refl

-- Two permutations whose inverses agree agree.
ˡ⇒ʳ : (π ρ : Permutation′ n) → (∀ x → π ⟨$⟩ˡ x ≡ ρ ⟨$⟩ˡ x) → ∀ i → π ⟨$⟩ʳ i ≡ ρ ⟨$⟩ʳ i
ˡ⇒ʳ π ρ h i = Eq.trans (Eq.cong (π ⟨$⟩ʳ_) (Eq.sym (inverseˡ ρ)))
                (Eq.trans (Eq.cong (π ⟨$⟩ʳ_) (Eq.sym (h (ρ ⟨$⟩ʳ i)))) (inverseʳ π))

-- Every letter is an involution.
gen-invol : (g : SG n) (x : Fin n) → SymI.⟦ g ⟧ᵍ ⟨$⟩ˡ (SymI.⟦ g ⟧ᵍ ⟨$⟩ˡ x) ≡ x
gen-invol (gate₀ ())
gen-invol (gate₁ ())
gen-invol (gate₂ σ-gate) zero          = Eq.refl
gen-invol (gate₂ σ-gate) (suc zero)    = Eq.refl
gen-invol (gate₂ σ-gate) (suc (suc x)) = Eq.refl
gen-invol (g ↥) zero    = Eq.refl
gen-invol (g ↥) (suc x) = Eq.cong suc (gen-invol g x)

act-inv : (p : Word (SG n)) (x : Fin n) → actₙ (inv p) (actₙ p x) ≡ x
act-inv [ g ]ʷ   x = gen-invol g x
act-inv ε       x = Eq.refl
act-inv (u • v) x = Eq.trans (Eq.cong (actₙ (inv v)) (act-inv u (actₙ v x))) (act-inv v x)

inv-inv : (p : Word (SG n)) → inv (inv p) ≡ p
inv-inv [ g ]ʷ   = Eq.refl
inv-inv ε       = Eq.refl
inv-inv (u • v) = Eq.cong₂ _•_ (inv-inv u) (inv-inv v)

act-inv′ : (p : Word (SG n)) (x : Fin n) → actₙ p (actₙ (inv p) x) ≡ x
act-inv′ p x = Eq.subst (λ q → actₙ q (actₙ (inv p) x) ≡ x) (inv-inv p) (act-inv (inv p) x)

------------------------------------------------------------------------
-- Iterated lifts of permutations and words

liftN : (j : ℕ) {m : ℕ} → Permutation′ m → Permutation′ (j + m)
liftN zero    ρ = ρ
liftN (suc j) ρ = lift₀ (liftN j ρ)

liftN-cong : (j : ℕ) {m : ℕ} (π ρ : Permutation′ m) → (∀ i → π ⟨$⟩ʳ i ≡ ρ ⟨$⟩ʳ i) →
             ∀ i → liftN j π ⟨$⟩ʳ i ≡ liftN j ρ ⟨$⟩ʳ i
liftN-cong zero    π ρ h = h
liftN-cong (suc j) π ρ h = P.lift₀-cong (liftN j π) (liftN j ρ) (liftN-cong j π ρ h)

stripN : (j : ℕ) {m : ℕ} → Permutation′ (j + m) → Permutation′ m
stripN zero    π = π
stripN (suc j) π = stripN j (remove zero π)

liftW : (j : ℕ) {m : ℕ} → Word (SG m) → Word (SG (j + m))
liftW zero    w = w
liftW (suc j) w = liftW j w Sym.↑

private
  suc-inj : {m : ℕ} {a b : Fin m} → _≡_ {A = Fin (suc m)} (suc a) (suc b) → a ≡ b
  suc-inj Eq.refl = Eq.refl

  -- remove 0 keeps the fixed points above 0.
  rem-fix : {m : ℕ} (π : Permutation′ (suc m)) (j : Fin m) →
            π ⟨$⟩ʳ zero ≡ zero → π ⟨$⟩ʳ suc j ≡ suc j → remove zero π ⟨$⟩ʳ j ≡ j
  rem-fix π j p q = suc-inj (Eq.trans (Eq.sym
    (Eq.subst (λ z → π ⟨$⟩ʳ suc j ≡ punchIn z (remove zero π ⟨$⟩ʳ j)) p (P.punchIn-permute π zero j))) q)

-- A permutation fixing the states below j is lifted from one on the rest.
strip-ok : (j : ℕ) {m : ℕ} (π : Permutation′ (j + m)) →
           (∀ x → toℕ x < j → π ⟨$⟩ʳ x ≡ x) → ∀ i → liftN j (stripN j π) ⟨$⟩ʳ i ≡ π ⟨$⟩ʳ i
strip-ok zero    π h i = Eq.refl
strip-ok (suc j) π h i =
  Eq.trans (P.lift₀-cong (liftN j (stripN j (remove zero π))) (remove zero π) ih i)
           (lift₀-remove π (h zero (s≤s z≤n)) i)
  where
  ih = strip-ok j (remove zero π) (λ x x<j → rem-fix π x (h zero (s≤s z≤n)) (h (suc x) (s≤s x<j)))

⟦liftW⟧ : (j : ℕ) {m : ℕ} (w : Word (SG m)) → ∀ i → SymI.⟦ liftW j w ⟧ ⟨$⟩ʳ i ≡ liftN j SymI.⟦ w ⟧ ⟨$⟩ʳ i
⟦liftW⟧ zero    w i = Eq.refl
⟦liftW⟧ (suc j) w i =
  Eq.trans (SymI.⟦↑⟧ (liftW j w) i) (P.lift₀-cong SymI.⟦ liftW j w ⟧ (liftN j SymI.⟦ w ⟧) (⟦liftW⟧ j w) i)

------------------------------------------------------------------------
-- Coxeter words as circuits

module Circuits {A : Set} (T : ℕ → Word A) where

  -- A Coxeter word read as a circuit, its wires shifted up by o.
  Pc : ℕ → Word (SG n) → Word A
  Pc o [ g ]ʷ   = T (tr o g)
  Pc o ε       = ε
  Pc o (u • v) = Pc o u • Pc o v

  Pc-↑ : (o : ℕ) (w : Word (SG n)) → Pc o (w Sym.↑) ≡ Pc (suc o) w
  Pc-↑ o [ g ]ʷ   = Eq.refl
  Pc-↑ o ε       = Eq.refl
  Pc-↑ o (u • v) = Eq.cong₂ _•_ (Pc-↑ o u) (Pc-↑ o v)

  Pc-liftW : (j : ℕ) {m : ℕ} (o : ℕ) (w : Word (SG m)) → Pc o (liftW j w) ≡ Pc (j + o) w
  Pc-liftW zero    o w = Eq.refl
  Pc-liftW (suc j) o w = Eq.trans (Pc-↑ o (liftW j w)) (Eq.trans (Pc-liftW j (suc o) w)
    (Eq.cong (λ z → Pc z w) (ℕP.+-suc j o)))

  -- The Coxeter relations for the circuits T d.
  module _ (Γ : WRel A) where

    open PB Γ

    record Coxeter : Set where
      field
        order : ∀ i → i ≤ 6 → T i • T i ≈ ε
        braid : ∀ i → i ≤ 5 → T i • T (suc i) • T i ≈ T (suc i) • T i • T (suc i)
        far   : ∀ i j → 2 + i ≤ j → j ≤ 6 → T i • T j ≈ T j • T i

  module Transfer {Γ : WRel A} (cox : Coxeter Γ) where

    open PB Γ
    open Coxeter cox

    private
      -- o + (2 + m) ≤ 8 gives o ≤ 6, and so on.
      bound : ∀ o m c → o + (c + m) ≤ 8 → o + c ≤ 8
      bound o m c p = ℕP.≤-trans (Eq.subst (_≤ o + (c + m)) (ℕP.+-identityʳ (o + c))
        (Eq.subst (o + c + 0 ≤_) (ℕP.+-assoc o c m) (ℕP.+-monoʳ-≤ (o + c) z≤n))) p

      le6 : ∀ o → o + 2 ≤ 8 → o ≤ 6
      le6 o p = ℕP.+-cancelʳ-≤ 2 o 6 p

      le5 : ∀ o → o + 3 ≤ 8 → o ≤ 5
      le5 o p = ℕP.+-cancelʳ-≤ 3 o 5 p

    -- The relations of S₈'s circuit presentation hold for the circuits.
    Pc-ax : ∀ {n w v} (o : ℕ) → o + n ≤ 8 → n VRel, w === v → Pc o w ≈ Pc o v
    Pc-ax {suc (suc m)} o b (srel Sym.order) = order o (le6 o (bound o m 2 b))
    Pc-ax {suc (suc (suc m))} o b (srel Sym.yang-baxter) = braid o (le5 o (bound o m 3 b))
    Pc-ax {suc n} {w = w} {v} o b (cong↑ {w = w′} {v = v′} a) =
      Eq.subst₂ _≈_ (Eq.sym (Pc-↑ o w′)) (Eq.sym (Pc-↑ o v′))
        (Pc-ax (suc o) (Eq.subst (_≤ 8) (ℕP.+-suc o n) b) a)
    Pc-ax o b (comm₁ () g)
    Pc-ax {suc (suc n)} o b (comm₂ σ-gate g) = sym (far o j lo hi)
      where
      j = tr (suc (suc o)) g
      lo : 2 + o ≤ j
      lo = tr-≥ (suc (suc o)) g
      hi : j ≤ 6
      hi = ℕP.+-cancelˡ-≤ 2 j 6 (ℕP.≤-trans (tr-≤ (suc (suc o)) g)
             (Eq.subst (_≤ 8) (Eq.trans (ℕP.+-suc o (suc n)) (Eq.cong suc (ℕP.+-suc o n))) b))
    Pc-ax o b (ω↑=ω ())

    Pc-cong : ∀ {n} {w v : Word (SG n)} (o : ℕ) → o + n ≤ 8 → PB._≈_ (n VRel,_===_) w v → Pc o w ≈ Pc o v
    Pc-cong o b PB.refl        = refl
    Pc-cong o b (PB.sym h)     = sym (Pc-cong o b h)
    Pc-cong o b (PB.trans h g) = trans (Pc-cong o b h) (Pc-cong o b g)
    Pc-cong o b (PB.cong h g)  = cong (Pc-cong o b h) (Pc-cong o b g)
    Pc-cong o b PB.assoc       = assoc
    Pc-cong o b PB.left-unit   = left-unit
    Pc-cong o b PB.right-unit  = right-unit
    Pc-cong o b (PB.axiom a)   = Pc-ax o b a

  ----------------------------------------------------------------------
  -- Completeness for permutations, inverses, frames and stabilisers

  module Complete {Γ : WRel A} (cox : Coxeter Γ) where

    open Transfer cox public
    open PB Γ
    open Coxeter cox
    open SR (PP.word-setoid Γ)

    -- Two Coxeter words with the same permutation are equal circuits.
    perm-complete′ : {n : ℕ} → n ≤ 8 → (p q : Word (SG n)) →
                     (∀ i → SymI.⟦ p ⟧ ⟨$⟩ʳ i ≡ SymI.⟦ q ⟧ ⟨$⟩ʳ i) → Pc 0 p ≈ Pc 0 q
    perm-complete′ {n} b p q h = Pc-cong 0 b (IsGroupIsomorphism.injective iso {p} {q} h)
      where
      open _IsPresentationOf_ (SymP.presentation {n}) using (iso ; module GL)
      open GroupMorphisms (Group.rawGroup GL.•-ε-group) (Group.rawGroup (SymSem.Permutation′-group n))
        using (module IsGroupIsomorphism)

    perm-complete : (p q : CW) → (∀ x → act p x ≡ act q x) → Pc 0 p ≈ Pc 0 q
    perm-complete p q h = perm-complete′ ℕP.≤-refl p q (ˡ⇒ʳ SymI.⟦ p ⟧ SymI.⟦ q ⟧ h)

    -- A Coxeter word followed by its inverse.
    Pc-inv : ∀ {n} (o : ℕ) → o + n ≤ 8 → (p : Word (SG n)) → Pc o p • Pc o (inv p) ≈ ε
    Pc-inv o b [ g ]ʷ = order (tr o g) (ℕP.+-cancelˡ-≤ 2 _ 6 (ℕP.≤-trans (tr-≤ o g) b))
    Pc-inv o b ε       = left-unit
    Pc-inv o b (u • v) = begin
      (Pc o u • Pc o v) • (Pc o (inv v) • Pc o (inv u))   ≈⟨ assoc ⟩
      Pc o u • (Pc o v • (Pc o (inv v) • Pc o (inv u)))   ≈⟨ cong refl (sym assoc) ⟩
      Pc o u • ((Pc o v • Pc o (inv v)) • Pc o (inv u))   ≈⟨ cong refl (trans (cong (Pc-inv o b v) refl) left-unit) ⟩
      Pc o u • Pc o (inv u)                               ≈⟨ Pc-inv o b u ⟩
      ε                                                   ∎

    Pc-inv′ : ∀ {n} (o : ℕ) → o + n ≤ 8 → (p : Word (SG n)) → Pc o (inv p) • Pc o p ≈ ε
    Pc-inv′ o b p = Eq.subst (λ q → Pc o (inv p) • Pc o q ≈ ε) (inv-inv p) (Pc-inv o b (inv p))

    -- A circuit conjugated by a Coxeter word.
    Fr : Word A → CW → Word A
    Fr b p = Pc 0 p • b • Pc 0 (inv p)

    Fr-conj : (b : Word A) (r p : CW) → Pc 0 r • Fr b p • Pc 0 (inv r) ≈ Fr b (r • p)
    Fr-conj b r p = begin
      Pc 0 r • ((Pc 0 p • (b • Pc 0 (inv p))) • Pc 0 (inv r))   ≈⟨ cong refl assoc ⟩
      Pc 0 r • (Pc 0 p • ((b • Pc 0 (inv p)) • Pc 0 (inv r)))   ≈⟨ sym assoc ⟩
      (Pc 0 r • Pc 0 p) • ((b • Pc 0 (inv p)) • Pc 0 (inv r))   ≈⟨ cong refl assoc ⟩
      (Pc 0 r • Pc 0 p) • (b • (Pc 0 (inv p) • Pc 0 (inv r)))   ∎

    -- Circuits that every T i with i ≥ j commutes with.
    Comm≥ : ℕ → Word A → Set
    Comm≥ j b = ∀ i → j ≤ i → i ≤ 6 → T i • b ≈ b • T i

    comm-word : ∀ {j m} (b : Word A) → Comm≥ j b → j + m ≤ 8 → (w : Word (SG m)) → Pc j w • b ≈ b • Pc j w
    comm-word {j} b cb bd [ g ]ʷ = cb (tr j g) (tr-≥ j g) (ℕP.+-cancelˡ-≤ 2 _ 6 (ℕP.≤-trans (tr-≤ j g) bd))
    comm-word b cb bd ε = trans left-unit (sym right-unit)
    comm-word {j} b cb bd (u • v) = begin
      (Pc j u • Pc j v) • b   ≈⟨ assoc ⟩
      Pc j u • (Pc j v • b)   ≈⟨ cong refl (comm-word b cb bd v) ⟩
      Pc j u • (b • Pc j v)   ≈⟨ sym assoc ⟩
      (Pc j u • b) • Pc j v   ≈⟨ cong (comm-word b cb bd u) refl ⟩
      (b • Pc j u) • Pc j v   ≈⟨ assoc ⟩
      b • (Pc j u • Pc j v)   ∎

    -- A Coxeter word fixing the states below j commutes with b.
    stab : (j m : ℕ) → j + m ≤ 8 → (b : Word A) → Comm≥ j b → (r : Word (SG (j + m))) →
           (∀ x → toℕ x < j → actₙ r x ≡ x) → Pc 0 r • b ≈ b • Pc 0 r
    stab j m bd b cb r fix = begin
      Pc 0 r • b                     ≈⟨ cong r≈ refl ⟩
      Pc 0 (liftW j w′) • b          ≡⟨ Eq.cong (_• b) lw ⟩
      Pc j w′ • b                    ≈⟨ comm-word b cb bd w′ ⟩
      b • Pc j w′                    ≡⟨ Eq.cong (b •_) (Eq.sym lw) ⟩
      b • Pc 0 (liftW j w′)          ≈⟨ cong refl (sym r≈) ⟩
      b • Pc 0 r                     ∎
      where
      π = SymI.⟦ r ⟧
      fixʳ : ∀ x → toℕ x < j → π ⟨$⟩ʳ x ≡ x
      fixʳ x lt = Eq.trans (Eq.cong (π ⟨$⟩ʳ_) (Eq.sym (fix x lt))) (inverseʳ π)
      gw = SymS.go m (stripN j π)
      w′ = proj₁ gw
      lw : Pc 0 (liftW j w′) ≡ Pc j w′
      lw = Eq.trans (Pc-liftW j 0 w′) (Eq.cong (λ z → Pc z w′) (ℕP.+-identityʳ j))
      r≈ : Pc 0 r ≈ Pc 0 (liftW j w′)
      r≈ = perm-complete′ bd r (liftW j w′) λ i → Eq.sym (Eq.trans (⟦liftW⟧ j w′ i)
             (Eq.trans (liftN-cong j SymI.⟦ w′ ⟧ (stripN j π) (proj₂ gw) i) (strip-ok j π fixʳ i)))

    -- Frames: b conjugated by two Coxeter words that agree below j.
    frame≈ : (j m : ℕ) → j + m ≤ 8 → (b : Word A) → Comm≥ j b → (p q : Word (SG (j + m))) →
            (∀ x → toℕ x < j → actₙ p x ≡ actₙ q x) →
            Pc 0 p • b • Pc 0 (inv p) ≈ Pc 0 q • b • Pc 0 (inv q)
    frame≈ j m bd b cb p q h = begin
      Pc 0 p • b • Pc 0 (inv p)                                    ≈⟨ cong p≈ refl ⟩
      (Pc 0 q • Pc 0 r) • b • Pc 0 (inv p)                         ≈⟨ assoc ⟩
      Pc 0 q • (Pc 0 r • b • Pc 0 (inv p))                         ≈⟨ cong refl (sym assoc) ⟩
      Pc 0 q • ((Pc 0 r • b) • Pc 0 (inv p))                       ≈⟨ cong refl (cong (stab j m bd b cb r fix) refl) ⟩
      Pc 0 q • ((b • Pc 0 r) • Pc 0 (inv p))                       ≈⟨ cong refl assoc ⟩
      Pc 0 q • (b • (Pc 0 r • Pc 0 (inv p)))                       ≈⟨ cong refl (cong refl ip) ⟩
      Pc 0 q • b • Pc 0 (inv q)                                    ∎
      where
      r = inv q • p
      fix : ∀ x → toℕ x < j → actₙ r x ≡ x
      fix x lt = Eq.trans (Eq.cong (actₙ (inv q)) (h x lt)) (act-inv q x)
      p≈ : Pc 0 p ≈ Pc 0 q • Pc 0 r
      p≈ = begin
        Pc 0 p                                ≈⟨ sym left-unit ⟩
        ε • Pc 0 p                            ≈⟨ cong (sym (Pc-inv 0 bd q)) refl ⟩
        (Pc 0 q • Pc 0 (inv q)) • Pc 0 p      ≈⟨ assoc ⟩
        Pc 0 q • (Pc 0 (inv q) • Pc 0 p)      ∎
      -- Pc r • Pc (inv p) = Pc (inv q) • (Pc p • Pc (inv p)) = Pc (inv q).
      ip : Pc 0 r • Pc 0 (inv p) ≈ Pc 0 (inv q)
      ip = begin
        (Pc 0 (inv q) • Pc 0 p) • Pc 0 (inv p)    ≈⟨ assoc ⟩
        Pc 0 (inv q) • (Pc 0 p • Pc 0 (inv p))    ≈⟨ cong refl (Pc-inv 0 bd p) ⟩
        Pc 0 (inv q) • ε                          ≈⟨ right-unit ⟩
        Pc 0 (inv q)                              ∎

------------------------------------------------------------------------
-- The action of a word lifted one wire up

act-↑-0 : (w : Word (SG n)) → actₙ (w Sym.↑) zero ≡ zero
act-↑-0 [ g ]ʷ   = Eq.refl
act-↑-0 ε       = Eq.refl
act-↑-0 (u • v) = Eq.trans (Eq.cong (actₙ (u Sym.↑)) (act-↑-0 v)) (act-↑-0 u)

act-↑-suc : (w : Word (SG n)) (x : Fin n) → actₙ (w Sym.↑) (suc x) ≡ suc (actₙ w x)
act-↑-suc [ g ]ʷ   x = Eq.refl
act-↑-suc ε       x = Eq.refl
act-↑-suc (u • v) x = Eq.trans (Eq.cong (actₙ (u Sym.↑)) (act-↑-suc v x)) (act-↑-suc u (actₙ v x))

------------------------------------------------------------------------
-- Cycles

-- cyc t sends 0 to t and every other state x to the one below it
-- (punchIn t).
cyc : Fin (suc n) → Word (SG (suc n))
cyc {zero}  zero    = ε
cyc {suc n} zero    = ε
cyc {suc n} (suc t) = cyc t Sym.↑ • [ gate₂ σ-gate ]ʷ

cyc-0 : (t : Fin (suc n)) → actₙ (cyc t) zero ≡ t
cyc-0 {zero}  zero    = Eq.refl
cyc-0 {suc n} zero    = Eq.refl
cyc-0 {suc n} (suc t) = Eq.trans (act-↑-suc (cyc t) zero) (Eq.cong suc (cyc-0 t))

cyc-suc : (t : Fin (suc n)) (x : Fin n) → actₙ (cyc t) (suc x) ≡ punchIn t x
cyc-suc {suc n} zero    x       = Eq.refl
cyc-suc {suc n} (suc t) zero    = act-↑-0 (cyc t)
cyc-suc {suc n} (suc t) (suc x) = Eq.trans (act-↑-suc (cyc t) (suc x)) (Eq.cong suc (cyc-suc t x))

------------------------------------------------------------------------
-- Frames

-- A list of states, each different from the given one.
data Avoid {n : ℕ} (t : Fin n) : List (Fin n) → Set where
  []  : Avoid t []
  _∷_ : ∀ {x xs} → t ≢ x → Avoid t xs → Avoid t (x ∷ xs)

-- Distinct states.
data Distinct {n : ℕ} : List (Fin n) → Set where
  []  : Distinct []
  _∷_ : ∀ {x xs} → Avoid x xs → Distinct xs → Distinct (x ∷ xs)

-- The rest of a list, punched out at a state it avoids.
outs : (t : Fin (suc n)) (xs : List (Fin (suc n))) → Avoid t xs → List (Fin n)
outs t []       []       = []
outs t (x ∷ xs) (p ∷ a)  = punchOut p ∷ outs t xs a

private
  avoid-out : {t x : Fin (suc n)} (p : t ≢ x) (xs : List (Fin (suc n))) (a : Avoid t xs) →
              Avoid x xs → Avoid (punchOut p) (outs t xs a)
  avoid-out p []       []       []       = []
  avoid-out p (y ∷ ys) (q ∷ a)  (r ∷ b)  = (λ e → r (FinP.punchOut-injective p q e)) ∷ avoid-out p ys a b

  distinct-out : (t : Fin (suc n)) (xs : List (Fin (suc n))) (a : Avoid t xs) → Distinct xs → Distinct (outs t xs a)
  distinct-out t []       []       []       = []
  distinct-out t (x ∷ xs) (p ∷ a)  (b ∷ d)  = avoid-out p xs a b ∷ distinct-out t xs a d

-- frame ts sends the state i to the i-th entry of ts (frame-act): it is
-- cyc of the head, followed, one wire up, by the frame of the rest
-- punched out at the head.
frame : (ts : List (Fin n)) → Distinct ts → Word (SG n)
frame []                   []       = ε
frame {suc n} (t ∷ ts)     (a ∷ d)  = cyc t • frame (outs t ts a) (distinct-out t ts a d) Sym.↑

-- The i-th entry of a list.
_‼_ : {B : Set} → List B → ℕ → Maybe B
[]       ‼ i       = nothing
(x ∷ xs) ‼ zero    = just x
(x ∷ xs) ‼ (suc i) = xs ‼ i

private
  outs-‼ : (t : Fin (suc n)) (xs : List (Fin (suc n))) (a : Avoid t xs) (j : ℕ) {x : Fin (suc n)} →
           xs ‼ j ≡ just x → Σ (t ≢ x) λ p → outs t xs a ‼ j ≡ just (punchOut p)
  outs-‼ t (y ∷ ys) (p ∷ a) zero    Eq.refl = p , Eq.refl
  outs-‼ t (y ∷ ys) (p ∷ a) (suc j) h       = outs-‼ t ys a j h

frame-act : (ts : List (Fin n)) (d : Distinct ts) (i x : Fin n) → ts ‼ toℕ i ≡ just x → actₙ (frame ts d) i ≡ x
frame-act {suc n} (t ∷ ts) (a ∷ d) zero x Eq.refl =
  Eq.trans (Eq.cong (actₙ (cyc t)) (act-↑-0 (frame (outs t ts a) (distinct-out t ts a d)))) (cyc-0 t)
frame-act {suc n} (t ∷ ts) (a ∷ d) (suc i) x h =
  Eq.trans (Eq.cong (actₙ (cyc t)) (act-↑-suc F i))
    (Eq.trans (cyc-suc t (actₙ F i))
      (Eq.trans (Eq.cong (punchIn t) (frame-act (outs t ts a) (distinct-out t ts a d) i (punchOut p) e))
        (FinP.punchIn-punchOut p)))
  where
  F = frame (outs t ts a) (distinct-out t ts a d)
  o = outs-‼ t ts a (toℕ i) h
  p = proj₁ o
  e = proj₂ o

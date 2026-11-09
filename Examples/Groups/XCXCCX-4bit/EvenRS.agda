------------------------------------------------------------------------
-- Presentations of groups
--
-- The even permutations of N states, by Reidemeister–Schreier
--
-- The even permutations A_N are the subgroup of index 2 of S_N, and
-- the Reidemeister–Schreier method presents them from the Coxeter
-- presentation of S_N (Examples.Groups.Symmetric) and the transversal
-- {ε, s₀} (rep): coset false is A_N, coset true is A_N s₀.  A letter
-- s_d read in coset c moves to the other coset and leaves behind the
-- Schreier generator γ(c, d), which is s_d s₀ from coset false and
-- s₀ s_d from coset true, and the empty word for d = 0 (γʷ).  So the
-- symbols are γ c d for 1 ≤ d ≤ N − 2 (Sch), read back as Coxeter
-- words by f; the coset action is h and its extension to words rs; and
-- the relations (_RS,_===_) are the Coxeter relations of S_N rewritten
-- from either coset, with γ(c, 0) written as ε and the instances that
-- become ε = ε left out: order, braid₀, braid, far₀ and far.
--
-- Normalization.Reidemeister-Schreier's Star-Injective-Full makes the
-- relations complete for A_N given two obligations: every relation
-- instance of S_N at width N, rewritten from either coset, gives
-- related words and the same coset (h-wd, by recursion on the instance
-- with an offset, as Coxeter.Circuits.Transfer.Pc-ax), and rewriting
-- f x from coset false gives x back (h=⁻¹f-gen).  With the completeness
-- of S_N's presentation, two words of symbols whose Coxeter words have
-- the same permutation are related (rs-complete).  Conversely rs turns
-- a Coxeter word that ends in coset false, an even one, into symbols
-- whose Coxeter word is the same up to S_N's relations (rs-≈), so
-- with the same permutation (rs-sem).  And the relations are sound:
-- the two sides of each have equal Coxeter words (rs-sound), so the
-- same permutation (rs-sound-sem).
--
-- Symbol indices are natural numbers: γ c d p q, with d : ℕ and the
-- bounds p : 1 ≤ d and q : 2 + d ≤ N irrelevant, so that two symbols
-- with the same c and d are equal and a client at a concrete N matches
-- on γ false 3 _ _ and the like (d = 0 is the absurd pattern
-- γ c 0 () _; an index beyond N − 2 is refuted through
-- Data.Empty.Irrelevant.⊥-elim, or met by a catch-all clause).  The
-- constructors of _RS,_===_ carry their bounds as relevant arguments.
-- The letter s_d at width n is letter n d q, whose index Cox.tr 0 is d
-- (tr-letter), and every letter is the letter of its index
-- (letter-tr).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.XCXCCX-4bit.EvenRS (N : ℕ) where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Data.Bool.Base using (Bool ; true ; false ; not)
open import Data.Bool.Properties using (not-involutive)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat.Base using (zero ; suc ; _+_ ; _≤_ ; z≤n ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Normalization.Reidemeister-Schreier using (module Star-Injective-Full)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _ʷ ; _ᵗ)

import Examples.Groups.Symmetric.Interpretation as SymI
import Examples.Groups.Symmetric.Presentation as SymP
import Examples.Groups.Symmetric.Semantics as SymSem
import Examples.Groups.Symmetric.Soundness as SymSound
import Examples.Groups.Symmetric.Syntactics as Sym
open Sym using ( gate₀ ; gate₁ ; gate₂ ; _↥ ; σ-gate ; _VRel,_===_
              ; srel ; cong↑ ; comm₁ ; comm₂ ; ω↑=ω )

import Examples.Groups.XCXCCX-4bit.Coxeter as Cox

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Letters

-- Letters of the Coxeter presentation of S_N.
G : Set
G = Cox.SG N

private
  -- The letter s_d at width n, by recursion on d first, so that it
  -- computes at a variable width.
  letter′ : (d n : ℕ) → .(2 + d ≤ n) → Cox.SG n
  letter′ zero    zero          ()
  letter′ zero    (suc zero)    q = ⊥-elim (ℕP.1+n≰n (ℕP.≤-pred q))
  letter′ zero    (suc (suc n)) q = gate₂ σ-gate
  letter′ (suc d) zero          ()
  letter′ (suc d) (suc n)       q = letter′ d n (ℕP.≤-pred q) ↥

  tr-letter′ : (d n : ℕ) .(q : 2 + d ≤ n) (o : ℕ) → Cox.tr o (letter′ d n q) ≡ o + d
  tr-letter′ zero    zero          ()
  tr-letter′ zero    (suc zero)    q o = ⊥-elim (ℕP.1+n≰n (ℕP.≤-pred q))
  tr-letter′ zero    (suc (suc n)) q o = Eq.sym (ℕP.+-identityʳ o)
  tr-letter′ (suc d) zero          ()
  tr-letter′ (suc d) (suc n)       q o =
    Eq.trans (tr-letter′ d n (ℕP.≤-pred q) (suc o)) (Eq.sym (ℕP.+-suc o d))

-- The letter s_d at width n: σ on the wires d and d + 1.
letter : (n d : ℕ) → .(2 + d ≤ n) → Cox.SG n
letter n d = letter′ d n

-- Its index, read from an offset o, is o + d.
tr-letter : (n d : ℕ) .(q : 2 + d ≤ n) (o : ℕ) → Cox.tr o (letter n d q) ≡ o + d
tr-letter n d = tr-letter′ d n

tr-suc : (o : ℕ) (g : Cox.SG n) → Cox.tr (suc o) g ≡ suc (Cox.tr o g)
tr-suc o (gate₀ ())
tr-suc o (gate₁ ())
tr-suc o (gate₂ σ-gate) = Eq.refl
tr-suc o (g ↥)          = tr-suc (suc o) g

letter-≡ : ∀ {n d d′} .(q : 2 + d ≤ n) .(q′ : 2 + d′ ≤ n) → d ≡ d′ → letter n d q ≡ letter n d′ q′
letter-≡ q q′ Eq.refl = Eq.refl

-- Every letter is the letter of its index.
letter-tr : (g : Cox.SG n) → letter n (Cox.tr 0 g) (Cox.tr-≤ 0 g) ≡ g
letter-tr (gate₀ ())
letter-tr (gate₁ ())
letter-tr (gate₂ σ-gate) = Eq.refl
letter-tr {suc n} (g ↥)  =
  Eq.trans (letter-≡ (Cox.tr-≤ 0 (g ↥)) (s≤s (Cox.tr-≤ 0 g)) (tr-suc 0 g)) (Eq.cong _↥ (letter-tr g))

-- The letter s_d as a word.
s : (d : ℕ) → .(2 + d ≤ N) → Word G
s d q = [ letter N d q ]ʷ

------------------------------------------------------------------------
-- Schreier symbols

-- γ false d stands for s_d s₀ and γ true d for s₀ s_d, 1 ≤ d ≤ N − 2.
data Sch : Set where
  γ : (c : Bool) (d : ℕ) → .(1 ≤ d) → .(2 + d ≤ N) → Sch

-- A symbol as a Coxeter word.
f : Sch → Word G
f (γ false d p q) = s d q • s 0 (ℕP.m+n≤o⇒m≤o 2 q)
f (γ true  d p q) = s 0 (ℕP.m+n≤o⇒m≤o 2 q) • s d q

-- The Schreier generator γ(c, d) as a word: ε for d = 0.
γʷ : Bool → (d : ℕ) → .(2 + d ≤ N) → Word Sch
γʷ c zero    q = ε
γʷ c (suc d) q = [ γ c (suc d) (s≤s z≤n) q ]ʷ

------------------------------------------------------------------------
-- The relations

-- Bounds of the symbols in far.
far-lo : ∀ {d e} → 2 + d ≤ e → 2 + e ≤ N → 2 + d ≤ N
far-lo {e = e} q r = ℕP.≤-trans q (ℕP.≤-trans (ℕP.m≤n+m e 2) r)

far-pos : ∀ {d e} → 1 ≤ d → 2 + d ≤ e → 1 ≤ e
far-pos {d} p q = ℕP.≤-trans p (ℕP.≤-trans (ℕP.m≤n+m d 2) q)

-- The Coxeter relations of S_N rewritten from the coset c (not c is
-- the other one), γ(c, 0) written as ε and the instances ε = ε left
-- out.  Each constructor is an explicit equation between words of
-- symbols.
data _RS,_===_ : WRel Sch where
  -- s_d s_d = ε, for 1 ≤ d ≤ N − 2: γ(c, d) γ(¬c, d) = ε.
  order  : (c : Bool) (d : ℕ) (p : 1 ≤ d) (q : 2 + d ≤ N) →
           _RS,_===_ ([ γ c d p q ]ʷ • [ γ (not c) d p q ]ʷ) ε
  -- s₀ s₁ s₀ = s₁ s₀ s₁, for N ≥ 3: γ(¬c, 1) = γ(c, 1) γ(c, 1).
  braid₀ : (c : Bool) (q : 3 ≤ N) →
           _RS,_===_ [ γ (not c) 1 (s≤s z≤n) q ]ʷ
                     ([ γ c 1 (s≤s z≤n) q ]ʷ • [ γ c 1 (s≤s z≤n) q ]ʷ)
  -- s_d s_{d+1} s_d = s_{d+1} s_d s_{d+1}, for 1 ≤ d ≤ N − 3:
  -- γ(c, d) γ(¬c, d + 1) γ(c, d) = γ(c, d + 1) γ(¬c, d) γ(c, d + 1).
  braid  : (c : Bool) (d : ℕ) (p : 1 ≤ d) (q : 3 + d ≤ N) →
           _RS,_===_ ([ γ c d p (ℕP.<⇒≤ q) ]ʷ • [ γ (not c) (suc d) (s≤s z≤n) q ]ʷ
                        • [ γ c d p (ℕP.<⇒≤ q) ]ʷ)
                     ([ γ c (suc d) (s≤s z≤n) q ]ʷ • [ γ (not c) d p (ℕP.<⇒≤ q) ]ʷ
                        • [ γ c (suc d) (s≤s z≤n) q ]ʷ)
  -- s₀ s_e = s_e s₀, for 2 ≤ e ≤ N − 2: γ(c, e) = γ(¬c, e).
  far₀   : (c : Bool) (e : ℕ) (p : 2 ≤ e) (q : 2 + e ≤ N) →
           _RS,_===_ [ γ c e (ℕP.<⇒≤ p) q ]ʷ [ γ (not c) e (ℕP.<⇒≤ p) q ]ʷ
  -- s_d s_e = s_e s_d, for 1 ≤ d, d + 2 ≤ e ≤ N − 2:
  -- γ(c, d) γ(¬c, e) = γ(c, e) γ(¬c, d).
  far    : (c : Bool) (d e : ℕ) (p : 1 ≤ d) (q : 2 + d ≤ e) (r : 2 + e ≤ N) →
           _RS,_===_ ([ γ c d p (far-lo q r) ]ʷ • [ γ (not c) e (far-pos p q) r ]ʷ)
                     ([ γ c e (far-pos p q) r ]ʷ • [ γ (not c) d p (far-lo q r) ]ʷ)

private
  module R = PB _RS,_===_
  module S = PB (N VRel,_===_)

------------------------------------------------------------------------
-- The coset action

-- A letter of width n read o wires up, at width N.
hₒ : (o : ℕ) → .(o + n ≤ N) → Bool → Cox.SG n → Word Sch × Bool
hₒ o b c g = γʷ c (Cox.tr o g) (ℕP.≤-trans (Cox.tr-≤ o g) b) , not c

-- The coset action: s_d read in coset c leaves γ(c, d) and moves to the
-- other coset.
h : Bool → G → Word Sch × Bool
h = hₒ 0 ℕP.≤-refl

-- The action extended to words.
rs : Bool → Word G → Word Sch × Bool
rs = h ᵗ

private
  module SIF = Star-Injective-Full _RS,_===_ (N VRel,_===_) Bool false

-- Words of symbols with cosets, compared pointwise.
open SIF public using (_~_)

------------------------------------------------------------------------
-- Well-definedness on S_N's relations

private
  -- o + (k + m) ≤ N gives k + o ≤ N.
  bound : ∀ o m k → o + (k + m) ≤ N → k + o ≤ N
  bound o m k p =
    ℕP.≤-trans (ℕP.≤-reflexive (ℕP.+-comm k o)) (ℕP.≤-trans (ℕP.+-monoʳ-≤ o (ℕP.m≤m+n k m)) p)

  ss : ∀ o m → o + suc (suc m) ≡ suc (suc (o + m))
  ss o m = Eq.trans (ℕP.+-suc o (suc m)) (Eq.cong suc (ℕP.+-suc o m))

  -- The traversal of a product, from the traversals of its factors.
  join : Word Sch × Bool → Word Sch × Bool → Word Sch × Bool
  join A x = proj₁ A • proj₁ x , proj₂ x

  ᵗ-• : {A A′ : Word Sch × Bool} (B B′ : Bool → Word Sch × Bool) → A ≡ A′ → (∀ c → B c ≡ B′ c) →
        join A (B (proj₂ A)) ≡ join A′ (B′ (proj₂ A′))
  ᵗ-• {A} B B′ Eq.refl e = Eq.cong (join A) (e (proj₂ A))

  -- A word shifted up one wire is read one wire further up.
  ᵗ-↑ : (o : ℕ) .(b : o + suc n ≤ N) .(b′ : suc o + n ≤ N) (c : Bool) (w : Word (Cox.SG n)) →
        (hₒ o b ᵗ) c (w Sym.↑) ≡ (hₒ (suc o) b′ ᵗ) c w
  ᵗ-↑ o b b′ c [ g ]ʷ   = Eq.refl
  ᵗ-↑ o b b′ c ε       = Eq.refl
  ᵗ-↑ o b b′ c (u • v) =
    ᵗ-• (λ c′ → (hₒ o b ᵗ) c′ (v Sym.↑)) (λ c′ → (hₒ (suc o) b′ ᵗ) c′ v)
        (ᵗ-↑ o b b′ c u) (λ c′ → ᵗ-↑ o b b′ c′ v)

  order-case : (c : Bool) (d : ℕ) (q : 2 + d ≤ N) →
               (γʷ c d q • γʷ (not c) d q , not (not c)) ~ (ε , c)
  order-case c zero    q = R.left-unit , not-involutive c
  order-case c (suc d) q = R.axiom (order c (suc d) (s≤s z≤n) q) , not-involutive c

  braid₀-case : (c : Bool) (q : 3 ≤ N) →
                R._≈_ (ε • ([ γ (not c) 1 (s≤s z≤n) q ]ʷ • ε))
                      ([ γ c 1 (s≤s z≤n) q ]ʷ • (ε • [ γ c 1 (s≤s z≤n) q ]ʷ))
  braid₀-case c q =
    R.trans R.left-unit (R.trans R.right-unit
      (R.trans (R.axiom (braid₀ c q)) (R.cong R.refl (R.sym R.left-unit))))

  braid-case : (c : Bool) (d : ℕ) (q : 3 + d ≤ N) →
    (γʷ c d (ℕP.<⇒≤ q) • γʷ (not c) (suc d) q • γʷ (not (not c)) d (ℕP.<⇒≤ q) , not (not (not c))) ~
    (γʷ c (suc d) q • γʷ (not c) d (ℕP.<⇒≤ q) • γʷ (not (not c)) (suc d) q , not (not (not c)))
  braid-case false zero    q = braid₀-case false q , Eq.refl
  braid-case true  zero    q = braid₀-case true q , Eq.refl
  braid-case false (suc d) q = R.axiom (braid false (suc d) (s≤s z≤n) q) , Eq.refl
  braid-case true  (suc d) q = R.axiom (braid true (suc d) (s≤s z≤n) q) , Eq.refl

  far-case : (c : Bool) (d e : ℕ) (lo : 2 + d ≤ e) (hi : 2 + e ≤ N) →
             R._≈_ (γʷ c e hi • γʷ (not c) d (far-lo lo hi)) (γʷ c d (far-lo lo hi) • γʷ (not c) e hi)
  far-case c zero    (suc (suc e)) (s≤s (s≤s z≤n)) hi =
    R.trans R.right-unit
      (R.trans (R.axiom (far₀ c (suc (suc e)) (s≤s (s≤s z≤n)) hi)) (R.sym R.left-unit))
  far-case c (suc d) (suc e)       (s≤s lo)        hi =
    R.sym (R.axiom (far c (suc d) (suc e) (s≤s z≤n) (s≤s lo) hi))

  -- A relation instance of width n, read o wires up.
  wd : {w v : Word (Cox.SG n)} (o : ℕ) (b : o + n ≤ N) (c : Bool) →
       n VRel, w === v → (hₒ o b ᵗ) c w ~ (hₒ o b ᵗ) c v
  wd {suc (suc m)}       o b c (srel Sym.order)       = order-case c o (bound o m 2 b)
  wd {suc (suc (suc m))} o b c (srel Sym.yang-baxter) = braid-case c o (bound o m 3 b)
  wd {suc m} o b c (cong↑ {w = w} {v = v} a) =
    Eq.subst₂ _~_ (Eq.sym (ᵗ-↑ o b b′ c w)) (Eq.sym (ᵗ-↑ o b b′ c v)) (wd (suc o) b′ c a)
    where
    b′ : suc o + m ≤ N
    b′ = Eq.subst (_≤ N) (ℕP.+-suc o m) b
  wd o b c (comm₁ () g)
  wd {suc (suc m)} o b c (comm₂ σ-gate g) =
    far-case c o (Cox.tr (suc (suc o)) g) (Cox.tr-≥ (suc (suc o)) g)
      (ℕP.≤-trans (Cox.tr-≤ (suc (suc o)) g) (Eq.subst (_≤ N) (ss o m) b)) , Eq.refl
  wd o b c (ω↑=ω ())

------------------------------------------------------------------------
-- The Reidemeister–Schreier obligations

-- Every relation instance of S_N rewrites, from either coset, to
-- related words of symbols, ending in the same coset.
h-wd : (c : Bool) {u t : Word G} → N VRel, u === t → (h ᵗ) c u ~ (h ᵗ) c t
h-wd c a = wd 0 ℕP.≤-refl c a

private
  γʷ-≡ : (c : Bool) {d d′ : ℕ} .(q : 2 + d ≤ N) .(q′ : 2 + d′ ≤ N) → d ≡ d′ → γʷ c d q ≡ γʷ c d′ q′
  γʷ-≡ c q q′ Eq.refl = Eq.refl

  γʷ-tr : (c : Bool) (d : ℕ) .(q : 2 + d ≤ N) →
          γʷ c (Cox.tr 0 (letter N d q)) (Cox.tr-≤ 0 (letter N d q)) ≡ γʷ c d q
  γʷ-tr c d q = γʷ-≡ c (Cox.tr-≤ 0 (letter N d q)) q (tr-letter N d q 0)

-- Rewriting a symbol's Coxeter word from coset false gives the symbol.
h=⁻¹f-gen : (x : Sch) → ([ x ]ʷ , false) ~ (h ᵗ) false (f x)
h=⁻¹f-gen (γ c zero () q)
h=⁻¹f-gen (γ false (suc d) p q) =
  R.trans (R.sym R.right-unit)
    (R.refl' (Eq.sym (Eq.cong₂ _•_ (γʷ-tr false (suc d) q) (γʷ-tr true 0 (ℕP.m+n≤o⇒m≤o 2 q))))) ,
  Eq.refl
h=⁻¹f-gen (γ true (suc d) p q) =
  R.trans (R.sym R.left-unit)
    (R.refl' (Eq.sym (Eq.cong₂ _•_ (γʷ-tr false 0 (ℕP.m+n≤o⇒m≤o 2 q)) (γʷ-tr true (suc d) q)))) ,
  Eq.refl

private
  module Eng = SIF.Reidemeister-Schreier-Full f h h=⁻¹f-gen h-wd

------------------------------------------------------------------------
-- Completeness

-- Two words of symbols whose Coxeter words have the same permutation
-- are equal by the relations.
rs-complete : (u v : Word Sch) →
              (∀ i → SymI.⟦ (f ʷ) u ⟧ ⟨$⟩ʳ i ≡ SymI.⟦ (f ʷ) v ⟧ ⟨$⟩ʳ i) → PB._≈_ _RS,_===_ u v
rs-complete u v e = Eng.reidemeister-schreier u v (IsGroupIsomorphism.injective iso {(f ʷ) u} {(f ʷ) v} e)
  where
  open _IsPresentationOf_ (SymP.presentation {N}) using (iso ; module GL)
  open GroupMorphisms (Group.rawGroup GL.•-ε-group) (Group.rawGroup (SymSem.Permutation′-group N))
    using (module IsGroupIsomorphism)

------------------------------------------------------------------------
-- From even Coxeter words to symbols

-- s₀ at width n (ε below width 2).
s₀ʷ : (n : ℕ) → Word (Cox.SG n)
s₀ʷ zero          = ε
s₀ʷ (suc zero)    = ε
s₀ʷ (suc (suc n)) = [ gate₂ σ-gate ]ʷ

-- The coset representatives: ε for coset false, s₀ for coset true.
rep : Bool → Word G
rep false = ε
rep true  = s₀ʷ N

private
  s₀ʷ-ok : (n : ℕ) (q : 2 ≤ n) → s₀ʷ n ≡ [ letter n 0 q ]ʷ
  s₀ʷ-ok zero          ()
  s₀ʷ-ok (suc zero)    (s≤s ())
  s₀ʷ-ok (suc (suc n)) q = Eq.refl

  s₀s₀ : (n : ℕ) .(q : 2 ≤ n) → PB._≈_ (n VRel,_===_) ([ letter n 0 q ]ʷ • [ letter n 0 q ]ʷ) ε
  s₀s₀ zero          ()
  s₀s₀ (suc zero)    q = ⊥-elim (ℕP.1+n≰n (ℕP.≤-pred q))
  s₀s₀ (suc (suc n)) q = PB.axiom (srel Sym.order)

  -- One letter: rep c • s_d = f γ(c, d) • rep (not c).
  step : (c : Bool) (d : ℕ) (q : 2 + d ≤ N) → rep c • s d q S.≈ (f ʷ) (γʷ c d q) • rep (not c)
  step false zero    q =
    S.trans S.left-unit (S.trans (S.refl' (Eq.sym (s₀ʷ-ok N q))) (S.sym S.left-unit))
  step false (suc d) q =
    S.trans S.left-unit
    (S.trans (S.sym S.right-unit)
    (S.trans (S.cong S.refl (S.sym (s₀s₀ N q₀)))
    (S.trans (S.sym S.assoc)
             (S.refl' (Eq.cong (λ z → (s (suc d) q • s 0 q₀) • z) (Eq.sym (s₀ʷ-ok N q₀)))))))
    where
    q₀ = ℕP.m+n≤o⇒m≤o 2 q
  step true zero    q =
    S.trans (S.refl' (Eq.cong (_• s 0 q) (s₀ʷ-ok N q))) (S.trans (s₀s₀ N q) (S.sym S.left-unit))
  step true (suc d) q =
    S.trans (S.refl' (Eq.cong (_• s (suc d) q) (s₀ʷ-ok N (ℕP.m+n≤o⇒m≤o 2 q)))) (S.sym S.right-unit)

-- Reading a word from coset c: rep c • w is the Coxeter word of its
-- symbols followed by the representative of the coset reached.
rs-rep : (c : Bool) (w : Word G) → rep c • w S.≈ (f ʷ) (proj₁ (rs c w)) • rep (proj₂ (rs c w))
rs-rep c [ g ]ʷ   =
  Eq.subst (λ x → rep c • [ x ]ʷ S.≈ (f ʷ) (γʷ c (Cox.tr 0 g) (Cox.tr-≤ 0 g)) • rep (not c))
    (letter-tr g) (step c (Cox.tr 0 g) (Cox.tr-≤ 0 g))
rs-rep c ε       = S.trans S.right-unit (S.sym S.left-unit)
rs-rep c (u • v) =
  S.trans (S.sym S.assoc)
  (S.trans (S.cong (rs-rep c u) S.refl)
  (S.trans S.assoc
  (S.trans (S.cong S.refl (rs-rep (proj₂ (rs c u)) v))
           (S.sym S.assoc))))

-- An even word, read from coset false, is the Coxeter word of its
-- symbols.
rs-≈ : (w : Word G) → proj₂ (rs false w) ≡ false → (f ʷ) (proj₁ (rs false w)) S.≈ w
rs-≈ w e =
  S.sym (S.trans (S.sym S.left-unit) (S.trans (rs-rep false w)
    (S.trans (S.refl' (Eq.cong (λ c → (f ʷ) (proj₁ (rs false w)) • rep c) e)) S.right-unit)))

rs-sem : (w : Word G) → proj₂ (rs false w) ≡ false →
         ∀ i → SymI.⟦ (f ʷ) (proj₁ (rs false w)) ⟧ ⟨$⟩ʳ i ≡ SymI.⟦ w ⟧ ⟨$⟩ʳ i
rs-sem w e = SymSound.sound (rs-≈ w e)

------------------------------------------------------------------------
-- The relations are sound

private
  -- The Coxeter relations for the letters, at any width.
  ord′ : (d n : ℕ) .(q : 2 + d ≤ n) → PB._≈_ (n VRel,_===_) ([ letter′ d n q ]ʷ • [ letter′ d n q ]ʷ) ε
  ord′ zero    zero          ()
  ord′ zero    (suc zero)    q = ⊥-elim (ℕP.1+n≰n (ℕP.≤-pred q))
  ord′ zero    (suc (suc n)) q = PB.axiom (srel Sym.order)
  ord′ (suc d) zero          ()
  ord′ (suc d) (suc n)       q = Sym.lemma-cong↑ _ _ (ord′ d n (ℕP.≤-pred q))

  braid′ : (d n : ℕ) .(q : 3 + d ≤ n) →
           PB._≈_ (n VRel,_===_)
             ([ letter′ d n (ℕP.<⇒≤ q) ]ʷ • [ letter′ (suc d) n q ]ʷ • [ letter′ d n (ℕP.<⇒≤ q) ]ʷ)
             ([ letter′ (suc d) n q ]ʷ • [ letter′ d n (ℕP.<⇒≤ q) ]ʷ • [ letter′ (suc d) n q ]ʷ)
  braid′ zero    zero                ()
  braid′ zero    (suc zero)          q = ⊥-elim (ℕP.1+n≰n (ℕP.≤-pred (ℕP.≤-trans (s≤s (s≤s z≤n)) q)))
  braid′ zero    (suc (suc zero))    q = ⊥-elim (ℕP.1+n≰n (ℕP.≤-pred (ℕP.≤-pred q)))
  braid′ zero    (suc (suc (suc n))) q = PB.axiom (srel Sym.yang-baxter)
  braid′ (suc d) zero                ()
  braid′ (suc d) (suc n)             q = Sym.lemma-cong↑ _ _ (braid′ d n (ℕP.≤-pred q))

  far′ : (d e n : ℕ) .(lo : 2 + d ≤ e) .(q : 2 + e ≤ n) →
         PB._≈_ (n VRel,_===_)
           ([ letter′ d n (ℕP.≤-trans (ℕP.+-monoʳ-≤ 2 (ℕP.≤-trans (ℕP.m≤n+m d 2) lo)) q) ]ʷ • [ letter′ e n q ]ʷ)
           ([ letter′ e n q ]ʷ • [ letter′ d n (ℕP.≤-trans (ℕP.+-monoʳ-≤ 2 (ℕP.≤-trans (ℕP.m≤n+m d 2) lo)) q) ]ʷ)
  far′ zero    zero          n             ()
  far′ zero    (suc zero)    n             lo q = ⊥-elim (ℕP.1+n≰n (ℕP.≤-pred lo))
  far′ zero    (suc (suc e)) zero          lo ()
  far′ zero    (suc (suc e)) (suc zero)    lo q = ⊥-elim (ℕP.1+n≰n (ℕP.≤-trans (s≤s (s≤s z≤n)) q))
  far′ zero    (suc (suc e)) (suc (suc n)) lo q =
    PB.sym (PB.axiom (comm₂ σ-gate (letter′ e n (ℕP.≤-pred (ℕP.≤-pred q)))))
  far′ (suc d) zero          n             ()
  far′ (suc d) (suc e)       zero          lo ()
  far′ (suc d) (suc e)       (suc n)       lo q = Sym.lemma-cong↑ _ _ (far′ d e n (ℕP.≤-pred lo) (ℕP.≤-pred q))

  s-ord : (d : ℕ) .(q : 2 + d ≤ N) → s d q • s d q S.≈ ε
  s-ord d q = ord′ d N q

  s-braid : (d : ℕ) .(q : 3 + d ≤ N) →
            s d (ℕP.<⇒≤ q) • s (suc d) q • s d (ℕP.<⇒≤ q) S.≈ s (suc d) q • s d (ℕP.<⇒≤ q) • s (suc d) q
  s-braid d q = braid′ d N q

  s-far : (d e : ℕ) .(lo : 2 + d ≤ e) .(q : 2 + e ≤ N) → s d (far-lo lo q) • s e q S.≈ s e q • s d (far-lo lo q)
  s-far d e lo q = far′ d e N lo q

  -- Word algebra.
  mid : (x y z : Word G) → y • y S.≈ ε → (x • y) • (y • z) S.≈ x • z
  mid x y z e =
    S.trans S.assoc (S.trans (S.cong S.refl (S.sym S.assoc))
      (S.trans (S.cong S.refl (S.cong e S.refl)) (S.cong S.refl S.left-unit)))

  br : (a b z : Word G) → z • z S.≈ ε → (a • z) • ((z • b) • (a • z)) S.≈ (a • b • a) • z
  br a b z e =
    S.trans (S.sym S.assoc) (S.trans (S.cong (mid a z b e) S.refl)
      (S.trans (S.sym S.assoc) (S.cong S.assoc S.refl)))

  br′ : (a b z : Word G) → z • z S.≈ ε → (z • a) • ((b • z) • (z • a)) S.≈ z • (a • b • a)
  br′ a b z e = S.trans (S.cong S.refl (mid b z a e)) S.assoc

  sw4 : (z a b : Word G) → a • b S.≈ b • a → (z • a) • (b • z) S.≈ (z • b) • (a • z)
  sw4 z a b e =
    S.trans S.assoc (S.trans (S.cong S.refl (S.sym S.assoc))
      (S.trans (S.cong S.refl (S.cong e S.refl))
        (S.trans (S.cong S.refl S.assoc) (S.sym S.assoc))))

  b₀ : ∀ {d} → 2 + d ≤ N → 2 ≤ N
  b₀ = ℕP.m+n≤o⇒m≤o 2

-- Each relation's two sides have equal Coxeter words.
rs-sound : {u v : Word Sch} → _RS,_===_ u v → (f ʷ) u S.≈ (f ʷ) v
rs-sound (order false d p q) = S.trans (mid (s d q) (s 0 (b₀ q)) (s d q) (s-ord 0 (b₀ q))) (s-ord d q)
rs-sound (order true  d p q) = S.trans (mid (s 0 (b₀ q)) (s d q) (s 0 (b₀ q)) (s-ord d q)) (s-ord 0 (b₀ q))
rs-sound (braid₀ false q) = S.sym
  (S.trans S.assoc (S.trans (S.cong S.refl (s-braid 0 q))
    (S.trans (S.sym S.assoc) (S.trans (S.cong (s-ord 1 q) S.refl) S.left-unit))))
rs-sound (braid₀ true q) = S.sym
  (S.trans S.assoc (S.trans (S.cong S.refl (S.sym (s-braid 0 q)))
    (S.trans (S.sym S.assoc) (S.trans (S.cong (s-ord 0 (ℕP.<⇒≤ q)) S.refl) S.left-unit))))
rs-sound (braid false d p q) =
  S.trans (br (s d (ℕP.<⇒≤ q)) (s (suc d) q) (s 0 (b₀ q)) (s-ord 0 (b₀ q)))
    (S.trans (S.cong (s-braid d q) S.refl)
      (S.sym (br (s (suc d) q) (s d (ℕP.<⇒≤ q)) (s 0 (b₀ q)) (s-ord 0 (b₀ q)))))
rs-sound (braid true d p q) =
  S.trans (br′ (s d (ℕP.<⇒≤ q)) (s (suc d) q) (s 0 (b₀ q)) (s-ord 0 (b₀ q)))
    (S.trans (S.cong S.refl (s-braid d q))
      (S.sym (br′ (s (suc d) q) (s d (ℕP.<⇒≤ q)) (s 0 (b₀ q)) (s-ord 0 (b₀ q)))))
rs-sound (far₀ false e p q) = S.sym (s-far 0 e p q)
rs-sound (far₀ true  e p q) = s-far 0 e p q
rs-sound (far false d e p q r) =
  S.trans (mid (s d (far-lo q r)) (s 0 (b₀ r)) (s e r) (s-ord 0 (b₀ r)))
    (S.trans (s-far d e q r) (S.sym (mid (s e r) (s 0 (b₀ r)) (s d (far-lo q r)) (s-ord 0 (b₀ r)))))
rs-sound (far true d e p q r) = sw4 (s 0 (b₀ r)) (s d (far-lo q r)) (s e r) (s-far d e q r)

-- So their two sides have the same permutation.
rs-sound-sem : {u v : Word Sch} → _RS,_===_ u v →
               ∀ i → SymI.⟦ (f ʷ) u ⟧ ⟨$⟩ʳ i ≡ SymI.⟦ (f ʷ) v ⟧ ⟨$⟩ʳ i
rs-sound-sem r = SymSound.sound (rs-sound r)

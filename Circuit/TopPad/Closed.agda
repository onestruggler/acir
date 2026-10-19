------------------------------------------------------------------------
-- Presentations of groups
--
-- A word ⇓'d is the same word one wire wider: by reflection
--
-- A word built from gates, •, ↑ and powers reads the same at every
-- width, and ⇓ carries each reading to the next.  For a closed word it
-- does so definitionally (σ ⇓ is σ), but a power w ^ k whose exponent
-- is not a numeral — S ^ p, Z ^ toℕ a — is stuck for wmap, and so is ↑
-- of such a word: (S ^ p) ⇓ ≡ S ^ p is an induction on the exponent.
-- ⇓-^≡ and ↑⇓≡ are those two inductions, and the macro ⇓-same proves
-- w ⇓ ≡ w′ for any two readings w, w′ of one word at consecutive
-- widths.  It unfolds both in step — the definitions of words, wmap
-- and _^_ only, so that the labels (exponents, multipliers) stay as
-- written: their normal forms can be huge and need not even be
-- well-typed outside an irrelevant position — down to the subterms
-- where ⇓ is stuck (wmap _↧ (u ^ k) against u′ ^ k, and wmap _↧ (wmap _↥
-- u) against wmap _↥ u′), and assembles the proof from the two lemmas
-- and Eq.cong₂ _•_; Agda checks the leaves.  The words' names never
-- enter: a rule over S^, M x, CZ^ and so on needs no lemma about any of
-- them.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; suc ; _∸_)

module Circuit.TopPad.Closed (Gate : ℕ → Set) where

open import Agda.Builtin.Reflection using (withReduceDefs)
open import Data.Bool using (Bool ; true ; false)
open import Data.List using (List ; [] ; _∷_ ; map ; drop ; length)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Product using (_×_ ; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (does)

open import Reflection
  using ( Term ; Name ; Arg ; arg ; arg-info ; visible ; vArg ; con ; def
        ; meta ; TC ; pure ; _>>=_ ; _>>_ ; reduce ; inferType ; unify
        ; typeError ; strErr ; termErr ; blockOnMeta ; quoteTC )
import Reflection.AST.Name as Name

open import Notations
open import Word.Base using (Word ; _^_ ; _•_ ; wmap)

open import Circuit.Base Gate using (Circuit ; _↑)
open import Circuit.TopPad Gate using (_⇓ ; ↑⇓)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The two inductions

⇓-^≡ : {w′ : Circuit (₁₊ n)} (w : Circuit n) (k : ℕ) →
       w ⇓ ≡ w′ → (w ^ k) ⇓ ≡ w′ ^ k
⇓-^≡ w 0      e = Eq.refl
⇓-^≡ w 1      e = e
⇓-^≡ w (₂₊ k) e = Eq.cong₂ _•_ e (⇓-^≡ w (₁₊ k) e)

↑⇓≡ : {w′ : Circuit (₁₊ n)} (w : Circuit n) → w ⇓ ≡ w′ → (w ↑) ⇓ ≡ w′ ↑
↑⇓≡ w e = Eq.trans (↑⇓ w) (Eq.cong _↑ e)

------------------------------------------------------------------------
-- The macro

private

  _is_ : Name → Name → Bool
  f is g = does (f Name.≟ g)

  -- The visible arguments of an application, in order.
  visibles : List (Arg Term) → List Term
  visibles []                                = []
  visibles (arg (arg-info visible _) t ∷ as) = t ∷ visibles as
  visibles (_ ∷ as)                          = visibles as

  -- The arguments with the last visible one replaced.
  set-last : List (Arg Term) → Term → List (Arg Term)
  set-last []                                     u = []
  set-last (arg (arg-info visible m) _ ∷ [])      u = arg (arg-info visible m) u ∷ []
  set-last (a ∷ as)                               u = a ∷ set-last as u

  last-visible : List (Arg Term) → Term → Term
  last-visible []                                t = t
  last-visible (arg (arg-info visible _) u ∷ as) t = last-visible as u
  last-visible (_ ∷ as)                          t = last-visible as t

  -- Did unfolding f make progress?
  unfolded : Name → Term → Bool
  unfolded f (def g _) with f is g
  ... | true  = false
  ... | false = true
  unfolded f _ = true

  -- One step: unfold f, and only f.
  unfold : Name → Term → TC Term
  unfold f t = withReduceDefs (true , f ∷ []) (reduce t)

  -- The weak head normal form of a word, unfolding only the definitions
  -- of words, wmap (once its word is a constructor) and _^_; a word not
  -- yet known waits until it is.  It is only ever applied to a word, so
  -- the definition at its head is the definition of a word: asking its
  -- type first (inferType, as this once did) cost a seventh of the time.
  whnf     : ℕ → Term → TC Term
  whnf-def : ℕ → Name → List (Arg Term) → Bool → Bool → TC Term
  -- t, f unfolded, if that got past f; otherwise u, f not unfolded.
  whnf-go  : ℕ → Name → Term → Term → Bool → TC Term
  -- Restricted unfolding does not take a record pattern apart (a case
  -- split on a decision): failing it, plain weak head reduction, kept
  -- only if it gets past f.
  whnf-or  : ℕ → Name → Term → Term → Bool → TC Term

  whnf 0       t          = pure t
  whnf (suc k) (meta m _) = blockOnMeta m
  whnf (suc k) (def f as) = whnf-def k f as (f is quote wmap) (f is quote _^_)
  whnf (suc k) t          = pure t

  whnf-def k f as true _ = do
    u ← whnf k (last-visible as (def f as))
    unfold f (def f (set-last as u))
  whnf-def k f as false true = do
    t ← unfold f (def f as)
    whnf-go k f t (def f as) (unfolded f t)
  whnf-def k f as false false = do
    t ← unfold f (def f as)
    whnf-or k f t (def f as) (unfolded f t)

  whnf-go k f t u true  = whnf k t
  whnf-go k f t u false = pure u

  whnf-or k f t u true  = whnf k t
  whnf-or k f t u false = do
    t′ ← reduce u
    whnf-go k f t′ u (unfolded f t′)

  -- The shapes a word can take, in weak head normal form.
  data Shape : Set where
    dot    : Term → Term → Shape   -- a • b
    pow    : Term → Term → Shape   -- w ^ e, stuck on e
    mapped : Term → Shape          -- wmap f u, stuck on u
    other  : Shape

  shape-con : Bool → List Term → Shape
  shape-con true (a ∷ b ∷ []) = dot a b
  shape-con _    _            = other

  shape-def : Bool → Bool → List Term → Shape
  shape-def true _    (w ∷ e ∷ []) = pow w e
  shape-def _    true (_ ∷ u ∷ []) = mapped u
  shape-def _    _    _            = other

  shape : Term → Shape
  shape (con c as) = shape-con (c is quote _•_) (visibles as)
  shape (def f as) = shape-def (f is quote _^_) (f is quote wmap) (visibles as)
  shape _          = other

  failure : ∀ {A : Set} → Term → Term → TC A
  failure x y = typeError (strErr "⇓-same: cannot match" ∷ termErr x ∷
                           strErr "against" ∷ termErr y ∷ [])

  refl-or : Maybe Term → Term
  refl-or (just p) = p
  refl-or nothing  = con (quote Eq.refl) []

  dots : Maybe Term → Maybe Term → Maybe Term
  dots nothing nothing = nothing
  dots p       q       =
    just (def (quote Eq.cong₂) (vArg (con (quote _•_) []) ∷
                                vArg (refl-or p) ∷ vArg (refl-or q) ∷ []))

  -- A word chosen by a case split on a label is stuck for good: a lemma
  -- (f , f-⇓ , k) says that f-⇓, applied to the last k visible
  -- arguments of f, proves (f …) ⇓ ≡ f ….
  Lemma : Set
  Lemma = Name × Name × ℕ

  lemma-for : Name → List Lemma → Maybe (Name × ℕ)
  lemma-for f []                = nothing
  lemma-for f ((g , l , k) ∷ T) with f is g
  ... | true  = just (l , k)
  ... | false = lemma-for f T

  last : ℕ → List Term → List Term
  last k ts = drop (length ts ∸ k) ts

  -- A proof of x ≡ y, x a word ⇓'d and y the same word one wire wider;
  -- nothing for Eq.refl.  G is Gate quoted: outside this module, its
  -- definitions take it first.  The fuel bounds the depth.
  same  : Term → List Lemma → ℕ → Term → Term → TC (Maybe Term)
  step  : Term → List Lemma → ℕ → Shape → Shape → Term → Term →
          TC (Maybe Term)
  stuck : Term → List Lemma → ℕ → Shape → Shape → Term → Term →
          TC (Maybe Term)

  same G T 0       x y = failure x y
  same G T (suc k) x y = do
    x ← whnf k x
    y ← whnf k y
    step G T k (shape x) (shape y) x y

  step G T k (dot a b) (dot a′ b′) _ _ = do
    p ← same G T k a a′
    q ← same G T k b b′
    pure (dots p q)
  step G T k (mapped u) _ _ y = stuck G T k (shape u) (shape y) u y
  step G T k (dot _ _)  _ x y = failure x y
  step G T k _ _ _ _          = pure nothing

  -- x is wmap _↧ u, stuck on u.
  stuck G T k (pow w e) (pow w′ _) _ _ = do
    p ← same G T k (def (quote _⇓) (vArg G ∷ vArg w ∷ [])) w′
    pure (just (def (quote ⇓-^≡)
                    (vArg G ∷ vArg w ∷ vArg e ∷ vArg (refl-or p) ∷ [])))
  stuck G T k (mapped s) (mapped s′) _ _ = do
    p ← same G T k (def (quote _⇓) (vArg G ∷ vArg s ∷ [])) s′
    pure (just (def (quote ↑⇓≡) (vArg G ∷ vArg s ∷ vArg (refl-or p) ∷ [])))
  stuck G T k other _ u@(def f as) y = use (lemma-for f T)
    where
    use : Maybe (Name × ℕ) → TC (Maybe Term)
    use (just (l , j)) = pure (just (def l (map vArg (last j (visibles as)))))
    use nothing        = failure (def (quote _⇓) (vArg G ∷ vArg u ∷ [])) y
  stuck G T k _ _ u y = failure (def (quote _⇓) (vArg G ∷ vArg u ∷ [])) y

  equation : List Lemma → Term → TC Term
  equation T hole = inferType hole >>= reduce >>= go
    where
    go-≡ : Term → Bool → List Term → TC Term
    go-≡ t true (x ∷ y ∷ []) = do
      G ← quoteTC Gate
      p ← same G T 100000 x y
      pure (refl-or p)
    go-≡ t _ _ = typeError (strErr "⇓-same: not an equation" ∷ termErr t ∷ [])

    go : Term → TC Term
    go (meta m _)   = blockOnMeta m
    go t@(def f as) = go-≡ t (f is quote _≡_) (visibles as)
    go t            = typeError (strErr "⇓-same: not an equation" ∷ termErr t ∷ [])

-- w ⇓ ≡ w′, for two readings of one word at consecutive widths; with
-- lemmas for the words a case split on a label chooses, (f , f-⇓ , k),
-- f-⇓ taking the last k visible arguments of f.
macro
  ⇓-same : Term → TC ⊤
  ⇓-same hole = equation [] hole >>= unify hole

  ⇓-same-by : List (Name × Name × ℕ) → Term → TC ⊤
  ⇓-same-by T hole = equation T hole >>= unify hole

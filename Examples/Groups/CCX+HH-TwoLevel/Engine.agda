------------------------------------------------------------------------
-- Presentations of groups
--
-- A small proof engine for equations between concrete words, after
-- Real-Clifford.Engine.
--
-- An equation is a pair of letter lists with a derivation (Eqn).  A
-- derivation of a new equation is a list of steps run on the letters:
-- `perm ys` replaces the current list by ys, which must be the same
-- word up to the commutation of letters with disjoint indices (the
-- canonical forms of Presentation.Tactics.Words.Commuting agree), and
-- `rw i e` rewrites the occurrence of lhs e at position i to rhs e.
-- `run` executes the steps, and run-sound turns a successful run into
-- a derivation, so that a proof is a list of steps closed by refl.
--
-- Equations are transformed by sym⁼, by rev⁼ (reversing both sides,
-- as every letter is an involution), by rot⁼ k m, which reads an
-- equation l = r as the relator l r⁻¹ = ε, rotates it by k letters
-- and splits it after m, and by emb⁼, along an increasing embedding
-- of indices.  Lists are in operator order, like words: the head acts
-- last.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Engine where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_)
open import Data.Fin.Base using (Fin ; toℕ)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length ; take ; drop ; map)
open import Data.List.Properties using (take++drop≡id)
open import Data.Maybe.Base using (Maybe ; just ; nothing ; _>>=_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _*_ ; _<ᵇ_)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Decidable using (does)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR
open import Presentation.Tactics.Words using (commutes ; module Commuting ; module Associative)

open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Embedding

open Associative using (word-of-list ; lemma-append)

private
  variable
    d n : ℕ

------------------------------------------------------------------------
-- Letter lists as words

⟪_⟫ : List (Gen n) → Word (Gen n)
⟪_⟫ = word-of-list

-- Without the trailing ε: ⟪ x ∷ y ∷ [] ⟫ᶠ is [ x ]ʷ • [ y ]ʷ.
⟪_⟫ᶠ : List (Gen n) → Word (Gen n)
⟪ [] ⟫ᶠ           = ε
⟪ x ∷ [] ⟫ᶠ       = [ x ]ʷ
⟪ x ∷ y ∷ zs ⟫ᶠ   = [ x ]ʷ • ⟪ y ∷ zs ⟫ᶠ

module _ {n : ℕ} where

  open PB (_===_ {n}) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

  ⟪++⟫ : (xs ys : List (Gen n)) → ⟪ xs ++ ys ⟫ ≈ ⟪ xs ⟫ • ⟪ ys ⟫
  ⟪++⟫ xs ys = sym (lemma-append xs ys)

  ⟪≈⟫ : {xs ys : List (Gen n)} → xs ≡ ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
  ⟪≈⟫ Eq.refl = refl

  flat : (xs : List (Gen n)) → ⟪ xs ⟫ ≈ ⟪ xs ⟫ᶠ
  flat [] = refl
  flat (x ∷ []) = right-unit
  flat (x ∷ y ∷ zs) = cong refl (flat (y ∷ zs))

------------------------------------------------------------------------
-- Equality, order and commutation of letters

eqF : Fin n → Fin n → Bool
eqF a b = does (a FinP.≟ b)

eqF-sound : {a b : Fin n} → eqF a b ≡ true → a ≡ b
eqF-sound {a = a} {b} h with a FinP.≟ b
... | yes e = e
eqF-sound {a = a} {b} () | no _

private
  ∧-l : ∀ {p q} → p ∧ q ≡ true → p ≡ true
  ∧-l {true} _ = Eq.refl
  ∧-r : ∀ {p q} → p ∧ q ≡ true → q ≡ true
  ∧-r {true} h = h

eqG : Gen n → Gen n → Bool
eqG (M-gen a)             (M-gen b)             = eqF a b
eqG (X-gen a b _)         (X-gen c d _)         = eqF a c ∧ eqF b d
eqG (K-gen a b c d _ _ _) (K-gen e f g h _ _ _) = eqF a e ∧ (eqF b f ∧ (eqF c g ∧ eqF d h))
eqG _                     _                     = false

eqG-sound : (x y : Gen n) → eqG x y ≡ true → x ≡ y
eqG-sound (M-gen a) (M-gen b) h = Eq.cong M-gen (eqF-sound h)
eqG-sound (X-gen a b p) (X-gen c d q) h
  with eqF-sound {a = a} {c} (∧-l {eqF a c} {eqF b d} h) | eqF-sound {a = b} {d} (∧-r {eqF a c} {eqF b d} h)
... | Eq.refl | Eq.refl = Eq.refl
eqG-sound (K-gen a b c d p q r) (K-gen e f g h p′ q′ r′) k
  with eqF-sound {a = a} {e} (∧-l {eqF a e} {Q₁} k)
     | eqF-sound {a = b} {f} (∧-l {eqF b f} {Q₂} (∧-r {eqF a e} {Q₁} k))
     | eqF-sound {a = c} {g} (∧-l {eqF c g} {eqF d h} (∧-r {eqF b f} {Q₂} (∧-r {eqF a e} {Q₁} k)))
     | eqF-sound {a = d} {h} (∧-r {eqF c g} {eqF d h} (∧-r {eqF b f} {Q₂} (∧-r {eqF a e} {Q₁} k)))
  where
  Q₂ = eqF c g ∧ eqF d h
  Q₁ = eqF b f ∧ Q₂
... | Eq.refl | Eq.refl | Eq.refl | Eq.refl = Eq.refl
eqG-sound (M-gen _) (X-gen _ _ _) ()
eqG-sound (M-gen _) (K-gen _ _ _ _ _ _ _) ()
eqG-sound (X-gen _ _ _) (M-gen _) ()
eqG-sound (X-gen _ _ _) (K-gen _ _ _ _ _ _ _) ()
eqG-sound (K-gen _ _ _ _ _ _ _) (M-gen _) ()
eqG-sound (K-gen _ _ _ _ _ _ _) (X-gen _ _ _) ()

eqL : List (Gen n) → List (Gen n) → Bool
eqL []       []       = true
eqL []       (y ∷ ys) = false
eqL (x ∷ xs) []       = false
eqL (x ∷ xs) (y ∷ ys) = eqG x y ∧ eqL xs ys

eqL-sound : (xs ys : List (Gen n)) → eqL xs ys ≡ true → xs ≡ ys
eqL-sound []       []       h = Eq.refl
eqL-sound []       (y ∷ ys) ()
eqL-sound (x ∷ xs) []       ()
eqL-sound (x ∷ xs) (y ∷ ys) h =
  Eq.cong₂ _∷_ (eqG-sound x y (∧-l {eqG x y} {eqL xs ys} h)) (eqL-sound xs ys (∧-r {eqG x y} {eqL xs ys} h))

-- A code, injective on the letters of a given dimension, for the order
-- of the canonical forms.
code : Gen n → ℕ
code {n} (M-gen a)             = 3 * toℕ a
code {n} (X-gen a b _)         = 1 + 3 * (toℕ a + n * toℕ b)
code {n} (K-gen a b c d _ _ _) = 2 + 3 * (toℕ a + n * (toℕ b + n * (toℕ c + n * toℕ d)))

less : Gen n → Gen n → Bool
less x y = code x <ᵇ code y

-- Letters with disjoint indices commute.
private
  ne? : (a b : Fin n) → Maybe (a ≢ b)
  ne? a b with a FinP.≟ b
  ... | yes _ = nothing
  ... | no ne = just ne

  ≢-sym : {a b : Fin n} → a ≢ b → b ≢ a
  ≢-sym ne e = ne (Eq.sym e)

comm? : (x y : Gen n) → Maybe (commutes (_===_ {n}) x y)
comm? (M-gen a) (M-gen b) = ne? a b >>= λ ab → just (PB.axiom (r2d ab))
comm? (X-gen a b p) (M-gen c) =
  ne? c a >>= λ ca → ne? c b >>= λ cb → just (PB.axiom (r2b p ca cb))
comm? (M-gen c) (X-gen a b p) =
  ne? c a >>= λ ca → ne? c b >>= λ cb → just (PB.sym (PB.axiom (r2b p ca cb)))
comm? (X-gen a b p) (X-gen c d q) =
  ne? a c >>= λ ac → ne? a d >>= λ ad → ne? b c >>= λ bc → ne? b d >>= λ bd →
  just (PB.axiom (r2a p q ac ad bc bd))
comm? (X-gen a b p) (K-gen c d e f q r s) =
  ne? a c >>= λ ac → ne? a d >>= λ ad → ne? a e >>= λ ae → ne? a f >>= λ af →
  ne? b c >>= λ bc → ne? b d >>= λ bd → ne? b e >>= λ be → ne? b f >>= λ bf →
  just (PB.axiom (r2c p q r s ac ad ae af bc bd be bf))
comm? (K-gen c d e f q r s) (X-gen a b p) =
  ne? a c >>= λ ac → ne? a d >>= λ ad → ne? a e >>= λ ae → ne? a f >>= λ af →
  ne? b c >>= λ bc → ne? b d >>= λ bd → ne? b e >>= λ be → ne? b f >>= λ bf →
  just (PB.sym (PB.axiom (r2c p q r s ac ad ae af bc bd be bf)))
comm? (M-gen a) (K-gen b c d e p q r) =
  ne? a b >>= λ ab → ne? a c >>= λ ac → ne? a d >>= λ ad → ne? a e >>= λ ae →
  just (PB.axiom (r2e p q r ab ac ad ae))
comm? (K-gen b c d e p q r) (M-gen a) =
  ne? a b >>= λ ab → ne? a c >>= λ ac → ne? a d >>= λ ad → ne? a e >>= λ ae →
  just (PB.sym (PB.axiom (r2e p q r ab ac ad ae)))
comm? (K-gen a b c d p q r) (K-gen e f g h s t u) =
  ne? a e >>= λ ae → ne? a f >>= λ af → ne? a g >>= λ ag → ne? a h >>= λ ah →
  ne? b e >>= λ be → ne? b f >>= λ bf → ne? b g >>= λ bg → ne? b h >>= λ bh →
  ne? c e >>= λ ce → ne? c f >>= λ cf → ne? c g >>= λ cg → ne? c h >>= λ ch →
  ne? d e >>= λ de → ne? d f >>= λ df → ne? d g >>= λ dg → ne? d h >>= λ dh →
  just (PB.axiom (r2f p q r s t u ae af ag ah be bf bg bh ce cf cg ch de df dg dh))

module Canon {n : ℕ} = Commuting (Gen n) (_===_ {n}) comm? less
open Canon using (comm-canonical ; lemma-comm-canonical)

------------------------------------------------------------------------
-- Every letter is an involution

invol : (x : Gen n) → PB._≈_ (_===_ {n}) ([ x ]ʷ • [ x ]ʷ) ε
invol (M-gen a)             = PB.axiom r1b
invol (X-gen a b p)         = PB.axiom (r1a p)
invol (K-gen a b c d p q r) = PB.axiom (r1c p q r)

------------------------------------------------------------------------
-- Reversal

rev : {A : Set} → List A → List A
rev []       = []
rev (x ∷ xs) = rev xs ++ (x ∷ [])

module _ {n : ℕ} where

  open PB (_===_ {n}) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

  rev-inv : (xs : List (Gen n)) → ⟪ rev xs ⟫ • ⟪ xs ⟫ ≈ ε
  rev-inv []       = left-unit
  rev-inv (x ∷ xs) = begin
    ⟪ rev xs ++ (x ∷ []) ⟫ • ([ x ]ʷ • ⟪ xs ⟫)        ≈⟨ cong (⟪++⟫ (rev xs) (x ∷ [])) refl ⟩
    (⟪ rev xs ⟫ • ([ x ]ʷ • ε)) • ([ x ]ʷ • ⟪ xs ⟫)   ≈⟨ cong (cong refl right-unit) refl ⟩
    (⟪ rev xs ⟫ • [ x ]ʷ) • ([ x ]ʷ • ⟪ xs ⟫)         ≈⟨ assoc ⟩
    ⟪ rev xs ⟫ • ([ x ]ʷ • ([ x ]ʷ • ⟪ xs ⟫))         ≈⟨ cong refl (sym assoc) ⟩
    ⟪ rev xs ⟫ • (([ x ]ʷ • [ x ]ʷ) • ⟪ xs ⟫)         ≈⟨ cong refl (trans (cong (invol x) refl) left-unit) ⟩
    ⟪ rev xs ⟫ • ⟪ xs ⟫                               ≈⟨ rev-inv xs ⟩
    ε                                                 ∎
    where open SR (PP.word-setoid (_===_ {n}))

  inv-rev : (xs : List (Gen n)) → ⟪ xs ⟫ • ⟪ rev xs ⟫ ≈ ε
  inv-rev []       = left-unit
  inv-rev (x ∷ xs) = begin
    ([ x ]ʷ • ⟪ xs ⟫) • ⟪ rev xs ++ (x ∷ []) ⟫        ≈⟨ cong refl (⟪++⟫ (rev xs) (x ∷ [])) ⟩
    ([ x ]ʷ • ⟪ xs ⟫) • (⟪ rev xs ⟫ • ([ x ]ʷ • ε))   ≈⟨ cong refl (cong refl right-unit) ⟩
    ([ x ]ʷ • ⟪ xs ⟫) • (⟪ rev xs ⟫ • [ x ]ʷ)         ≈⟨ assoc ⟩
    [ x ]ʷ • (⟪ xs ⟫ • (⟪ rev xs ⟫ • [ x ]ʷ))         ≈⟨ cong refl (sym assoc) ⟩
    [ x ]ʷ • ((⟪ xs ⟫ • ⟪ rev xs ⟫) • [ x ]ʷ)         ≈⟨ cong refl (trans (cong (inv-rev xs) refl) left-unit) ⟩
    [ x ]ʷ • [ x ]ʷ                                   ≈⟨ invol x ⟩
    ε                                                 ∎
    where open SR (PP.word-setoid (_===_ {n}))

  -- If u • v ≈ ε then u ≈ v⁻¹, the reversal of v.
  inverse-of : (xs ys : List (Gen n)) → ⟪ xs ⟫ • ⟪ ys ⟫ ≈ ε → ⟪ xs ⟫ ≈ ⟪ rev ys ⟫
  inverse-of xs ys e = begin
    ⟪ xs ⟫                              ≈⟨ sym right-unit ⟩
    ⟪ xs ⟫ • ε                          ≈⟨ cong refl (sym (inv-rev ys)) ⟩
    ⟪ xs ⟫ • (⟪ ys ⟫ • ⟪ rev ys ⟫)      ≈⟨ sym assoc ⟩
    (⟪ xs ⟫ • ⟪ ys ⟫) • ⟪ rev ys ⟫      ≈⟨ trans (cong e refl) left-unit ⟩
    ⟪ rev ys ⟫                          ∎
    where open SR (PP.word-setoid (_===_ {n}))

  -- Relators: u • v ≈ ε gives v • u ≈ ε.
  rotate-relator : (xs ys : List (Gen n)) → ⟪ xs ⟫ • ⟪ ys ⟫ ≈ ε → ⟪ ys ⟫ • ⟪ xs ⟫ ≈ ε
  rotate-relator xs ys e = begin
    ⟪ ys ⟫ • ⟪ xs ⟫                                 ≈⟨ cong refl (inverse-of xs ys e) ⟩
    ⟪ ys ⟫ • ⟪ rev ys ⟫                             ≈⟨ inv-rev ys ⟩
    ε                                               ∎
    where open SR (PP.word-setoid (_===_ {n}))

  rev-cong : (xs ys : List (Gen n)) → ⟪ xs ⟫ ≈ ⟪ ys ⟫ → ⟪ rev xs ⟫ ≈ ⟪ rev ys ⟫
  rev-cong xs ys e = inverse-of (rev xs) ys (trans (cong refl (sym e)) (rev-inv xs))

------------------------------------------------------------------------
-- Equations

record Eqn (n : ℕ) : Set where
  constructor eqn
  field
    lhs rhs : List (Gen n)
    prf     : PB._≈_ (_===_ {n}) ⟪ lhs ⟫ ⟪ rhs ⟫

open Eqn public

-- The equation, between words without the trailing ε.
prfᶠ : (e : Eqn n) → PB._≈_ (_===_ {n}) ⟪ lhs e ⟫ᶠ ⟪ rhs e ⟫ᶠ
prfᶠ e = PB.trans (PB.sym (flat (lhs e))) (PB.trans (prf e) (flat (rhs e)))

sym⁼ : Eqn n → Eqn n
sym⁼ (eqn l r p) = eqn r l (PB.sym p)

rev⁼ : Eqn n → Eqn n
rev⁼ (eqn l r p) = eqn (rev l) (rev r) (rev-cong l r p)

-- An axiom on letter lists.
ax⁼ : (l r : List (Gen n)) → ⟪ l ⟫ᶠ === ⟪ r ⟫ᶠ → Eqn n
ax⁼ l r a = eqn l r (PB.trans (flat l) (PB.trans (PB.axiom a) (PB.sym (flat r))))

-- The relator l r⁻¹ = ε, rotated by k and split after m.
relator : Eqn n → List (Gen n)
relator e = lhs e ++ rev (rhs e)

rotated : ℕ → Eqn n → List (Gen n)
rotated k e = drop k (relator e) ++ take k (relator e)

module _ {n : ℕ} where

  open PB (_===_ {n}) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

  relator-ε : (e : Eqn n) → ⟪ relator e ⟫ ≈ ε
  relator-ε (eqn l r p) = trans (⟪++⟫ l (rev r)) (trans (cong p refl) (inv-rev r))

  split-ε : (k : ℕ) (xs : List (Gen n)) → ⟪ xs ⟫ ≈ ε → ⟪ take k xs ⟫ • ⟪ drop k xs ⟫ ≈ ε
  split-ε k xs e = trans (sym (⟪++⟫ (take k xs) (drop k xs))) (trans (⟪≈⟫ (take++drop≡id k xs)) e)

  rotated-ε : (k : ℕ) (e : Eqn n) → ⟪ rotated k e ⟫ ≈ ε
  rotated-ε k e = trans (⟪++⟫ (drop k (relator e)) (take k (relator e)))
    (rotate-relator (take k (relator e)) (drop k (relator e)) (split-ε k (relator e) (relator-ε e)))

rot⁼ : ℕ → ℕ → Eqn n → Eqn n
rot⁼ k m e = eqn (take m (rotated k e)) (rev (drop m (rotated k e)))
  (inverse-of (take m (rotated k e)) (drop m (rotated k e)) (split-ε m (rotated k e) (rotated-ε k e)))

------------------------------------------------------------------------
-- Embedding equations

⟪map⟫ : (e : Emb d n) (xs : List (Gen d)) → ⟪ map (gen e) xs ⟫ ≡ word e ⟪ xs ⟫
⟪map⟫ e []       = Eq.refl
⟪map⟫ e (x ∷ xs) = Eq.cong ([ gen e x ]ʷ •_) (⟪map⟫ e xs)

emb⁼ : Emb d n → Eqn d → Eqn n
emb⁼ {d} {n} e (eqn l r p) = eqn (map (gen e) l) (map (gen e) r)
  (Eq.subst₂ (PB._≈_ (_===_ {n})) (Eq.sym (⟪map⟫ e l)) (Eq.sym (⟪map⟫ e r)) (word-≈ e p))

------------------------------------------------------------------------
-- Running a derivation

data Step (n : ℕ) : Set where
  perm : List (Gen n) → Step n
  rw   : ℕ → Eqn n → Step n

rewrite-at : ℕ → Eqn n → List (Gen n) → List (Gen n)
rewrite-at i e xs = take i xs ++ (rhs e ++ drop (length (lhs e)) (drop i xs))

matches-at : ℕ → Eqn n → List (Gen n) → Bool
matches-at i e xs = eqL (take (length (lhs e)) (drop i xs)) (lhs e)

run : List (Step n) → List (Gen n) → Maybe (List (Gen n))
run []              xs = just xs
run (perm ys ∷ ss)  xs =
  if eqL (comm-canonical xs) (comm-canonical ys) then run ss ys else nothing
run (rw i e ∷ ss)   xs =
  if matches-at i e xs then run ss (rewrite-at i e xs) else nothing

module _ {n : ℕ} where

  open PB (_===_ {n}) using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

  perm-sound : (xs ys : List (Gen n)) → comm-canonical xs ≡ comm-canonical ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
  perm-sound xs ys e =
    trans (lemma-comm-canonical xs) (trans (⟪≈⟫ e) (sym (lemma-comm-canonical ys)))

  rw-sound : (i : ℕ) (e : Eqn n) (xs : List (Gen n)) → matches-at i e xs ≡ true →
             ⟪ xs ⟫ ≈ ⟪ rewrite-at i e xs ⟫
  rw-sound i e xs h = begin
    ⟪ xs ⟫                                          ≈⟨ ⟪≈⟫ (Eq.sym (take++drop≡id i xs)) ⟩
    ⟪ take i xs ++ drop i xs ⟫                      ≈⟨ ⟪++⟫ (take i xs) (drop i xs) ⟩
    ⟪ take i xs ⟫ • ⟪ drop i xs ⟫                   ≈⟨ cong refl (⟪≈⟫ (Eq.sym (take++drop≡id m (drop i xs)))) ⟩
    ⟪ take i xs ⟫ • ⟪ take m (drop i xs) ++ rest ⟫  ≈⟨ cong refl (⟪++⟫ (take m (drop i xs)) rest) ⟩
    ⟪ take i xs ⟫ • (⟪ take m (drop i xs) ⟫ • ⟪ rest ⟫)
                                                    ≈⟨ cong refl (cong (⟪≈⟫ (eqL-sound _ _ h)) refl) ⟩
    ⟪ take i xs ⟫ • (⟪ lhs e ⟫ • ⟪ rest ⟫)          ≈⟨ cong refl (cong (prf e) refl) ⟩
    ⟪ take i xs ⟫ • (⟪ rhs e ⟫ • ⟪ rest ⟫)          ≈⟨ cong refl (sym (⟪++⟫ (rhs e) rest)) ⟩
    ⟪ take i xs ⟫ • ⟪ rhs e ++ rest ⟫               ≈⟨ sym (⟪++⟫ (take i xs) (rhs e ++ rest)) ⟩
    ⟪ rewrite-at i e xs ⟫                           ∎
    where
    open SR (PP.word-setoid (_===_ {n}))
    m = length (lhs e)
    rest = drop m (drop i xs)

  run-sound : (ss : List (Step n)) (xs ys : List (Gen n)) → run ss xs ≡ just ys → ⟪ xs ⟫ ≈ ⟪ ys ⟫
  run-sound []             xs ys Eq.refl = refl
  run-sound (perm zs ∷ ss) xs ys h with eqL (comm-canonical xs) (comm-canonical zs) in c
  run-sound (perm zs ∷ ss) xs ys h  | true  = trans (perm-sound xs zs (eqL-sound _ _ c)) (run-sound ss zs ys h)
  run-sound (perm zs ∷ ss) xs ys () | false
  run-sound (rw i e ∷ ss)  xs ys h with matches-at i e xs in c
  run-sound (rw i e ∷ ss)  xs ys h  | true  = trans (rw-sound i e xs c) (run-sound ss (rewrite-at i e xs) ys h)
  run-sound (rw i e ∷ ss)  xs ys () | false

-- A derivation: an equation from the steps that turn lhs into rhs.
derive : (l r : List (Gen n)) (ss : List (Step n)) → run ss l ≡ just r → Eqn n
derive l r ss h = eqn l r (run-sound ss l r h)

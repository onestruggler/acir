------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 10, over Equation (65)
--
-- Every equation of Figure 10 is proved from (65), Corollary A.7 and
-- Corollary A.5, so this module takes (65) — at every admissible tuple
-- — as its one hypothesis and derives them.  (65) itself is proved in
-- `Auxiliary/Eq65H` (`eq65-full`), against the statement `Eq65` here.
--
-- Three of them here; the others are in `Fuse`, `Move`, `Eq67`,
-- `Eq71`, `Eq75` and `Eq77`, and `CorollaryA8` indexes them all.
--
--   (66)  H_[a,b] H_[c,d]  ≈  H_[c,d] H_[a,b]        {a,b} ∩ {c,d} = ∅
--   (70)  H_[a,b] H_[a,b]  ≈  ε
--   (74)  ((−1)_[g] X_[x,y]) (H_[c,d] H_[e,f])
--            ≈  (H_[c,d] H_[e,f]) ((−1)_[g] X_[x,y])   {g,x,y} ∩ … = ∅
--
-- (66) is (65) at both tuples with A.7 between them, the two sides
-- denoting the same operator because two pairs on disjoint indices
-- commute (`PairComm`).  (70) is the paper's own chain: (42) splits the
-- letter over two *fresh* indices, (66) turns the second factor round,
-- (65) writes both as Definition E.1's words around the standard pair,
-- and then the inner Σ′Σ cancels, the two standard pairs cancel by
-- (41), and the outer ΣΣ′ cancels.
--
-- (74) is an instance of `pair-comm`, which is the general fact: **a
-- Hadamard-free word that neither moves nor signs any of the pair's
-- four indices commutes with the pair.**  By (65) the pair is Σ Λ Σ′,
-- and conjugating the word by Σ gives one that neither moves nor signs
-- an index below 4 — which is exactly what Lemma A.6's `passes-low`
-- asks for.  The two conjugations are Corollary A.5, the signed
-- permutations being equal by construction.  `comm-ε` and `comm-•`
-- close the commuting words under products, and `comm-zz` and
-- `comm-xx` add the other two letter shapes, so this is a kit and not
-- one equation: *every* Hadamard-free word whose letters stay away
-- from the pair's four indices commutes with it.
--
-- **(70) is the (a3) obligation of item (b) at the coset ε.**
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; not ; _∨_ ; _∧_ ; _xor_ ; if_then_else_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Nat using (zero ; suc ; _<_ ; _≤_ ; s≤s ; z≤n ; _≡ᵇ_)
  renaming (_^_ to _^ℕ_ ; _+_ to _+ℕ_)
open import Data.Nat.Properties
  using (≤-refl ; m≤n⇒m≤1+n ; ≤-trans ; <-irrefl ; +-monoʳ-≤)
  renaming (_≟_ to _≟ⁿ_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray
  using (code ; code-injective)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
  using (_P,_===_ ; r41 ; r42)
open import Examples.Groups.Real-Clifford+CH.Encoding
  using (hh ; hhℕ ; zz ; zx ; xx ; Σ ; Σ′ ; twoSmallest ; distinct4)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (HFreeʷ ; cat ; gen ; hf-zz ; hf-xx ; gen-xx ; fin ; fin-toℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Sigma
  using (≡ᵇ-refl ; ≡ᵇ-t ; ≡ᵇ-f)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (8≤2^)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m using (hhℕ-hh ; i₀ ; i₁ ; i₂ ; i₃ ; toℕ-i₀ ; toℕ-i₁ ; toℕ-i₂ ; toℕ-i₃)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SPMatrix m
  using (word-op ; word-scale ; ⟦_⟧ʷ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.PairComm m using (HH2-comm)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Passes m
  using (Λ ; passes-low ; four-of)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (sp ; sgn ; prm ; sp-inj ; ⊙-inverse ; idSP ; swapF ; swapF-o ; sp-xx
       ; δ ; δ-≢)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_ ; ≐-refl to ≐-refl′ ; ≐-sym to ≐-sym′
          ; ≐-trans to ≐-trans′ ; ⊙-assoc to ⊙-assoc′ ; ⊙-cong to ⊙-cong′
          ; ⊙-idˡ to ⊙-idˡ′ ; ⊙-idʳ to ⊙-idʳ′
          ; prm≡ to prm≡′ ; sgn≡ to sgn≡′)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique m using (A5-full)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SigmaPerm m
  using (zx-prm ; zx-sgn ; hfree-zx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.A6 m using (Λ-scale)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.A7 m using (A7)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq65 m
  as E65 using (Pair ; hh-op ; hh-scale)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

open Tools (m P,_===_)

private
  n : ℕ
  n = ₃₊ m

  N : ℕ
  N = 2 ^ℕ n

  W : Set
  W = Word (GenP (₃₊ m))

  ≢sym : ∀ {x y : Fin N} → x ≢ y → y ≢ x
  ≢sym ne e = ne (Eq.sym e)

  refl≡ : ∀ {u v : W} → u ≡ v → u ≈ v
  refl≡ Eq.refl = refl

  dif : ∀ {x y : Fin N} → x ≢ y → code n x ≢ code n y
  dif ne e = ne (code-injective n e)

------------------------------------------------------------------------
-- Definition E.1's two words, without their side conditions

Sw S′w : Fin N → Fin N → Fin N → Fin N → W
Sw  a b c d = Σ  {₃₊ m} (toℕ a) (toℕ b) (toℕ c) (toℕ d)
S′w a b c d = Σ′ {₃₊ m} (toℕ a) (toℕ b) (toℕ c) (toℕ d)

-- Equation (65), at every tuple of four distinct indices.
Eq65 : Set
Eq65 = ∀ (a b c d : Fin N) → a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d →
       hh {₃₊ m} a b c d ≈ Sw a b c d • (Λ • S′w a b c d)

------------------------------------------------------------------------
-- Two indices fresh to a and b
--
-- Equation (42) splits a letter over `twoSmallest`, the two smallest
-- naturals avoiding its four indices.  Here the four are a, b, a, b —
-- only two values — so three tries always suffice, and the answer is
-- below 6, hence an index at every width.  `free` is private to
-- `Encoding`, so the search is repeated here; the two agree by
-- reduction, the fuel being a numeral.

private
  blk : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  blk a b c d v = (v ≡ᵇ a) ∨ (v ≡ᵇ b) ∨ (v ≡ᵇ c) ∨ (v ≡ᵇ d)

  fr : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  fr zero       v a b c d = v
  fr (suc fuel) v a b c d =
    if blk a b c d v then fr fuel (suc v) a b c d else v

  -- It is `Encoding`'s own search.
  ts≡ : ∀ (A B : ℕ) →
        twoSmallest A B A B ≡ (fr 5 0 A B A B , fr 5 (suc (fr 5 0 A B A B)) A B A B)
  ts≡ A B = Eq.refl

  blk-f : ∀ (A B v : ℕ) → v ≢ A → v ≢ B → blk A B A B v ≡ false
  blk-f A B v na nb rewrite ≡ᵇ-f v A na | ≡ᵇ-f v B nb = Eq.refl

  blk-ta : ∀ (A B v : ℕ) → v ≡ A → blk A B A B v ≡ true
  blk-ta A B v e rewrite ≡ᵇ-t v A e = Eq.refl

  blk-tb : ∀ (A B v : ℕ) → v ≡ B → blk A B A B v ≡ true
  blk-tb A B v e rewrite ≡ᵇ-t v B e = go (v ≡ᵇ A)
    where
    go : ∀ (t : Bool) → (t ∨ true ∨ t ∨ true) ≡ true
    go true  = Eq.refl
    go false = Eq.refl

  -- Numerals two apart.
  ≢suc : ∀ (v : ℕ) → v ≢ suc v
  ≢suc zero    ()
  ≢suc (suc v) e = ≢suc v (Eq.cong pred′ e)
    where
    pred′ : ℕ → ℕ
    pred′ zero    = zero
    pred′ (suc k) = k

  ≢suc² : ∀ (v : ℕ) → v ≢ suc (suc v)
  ≢suc² zero    ()
  ≢suc² (suc v) e = ≢suc² v (Eq.cong pred′ e)
    where
    pred′ : ℕ → ℕ
    pred′ zero    = zero
    pred′ (suc k) = k

module Fresh (A B : ℕ) (AB : A ≢ B) where

  private
    e f : ℕ
    e = fr 5 0 A B A B
    f = fr 5 (suc e) A B A B

    -- With only two forbidden values, the search stops within three.
    Res : ℕ → ℕ → Set
    Res v w = (w ≢ A) × (w ≢ B) × (v ≤ w) × (w ≤ 2 +ℕ v)

    fresh : ∀ (v : ℕ) → Res v (fr 5 v A B A B)
    fresh v = c₀ (v ≟ⁿ A) (v ≟ⁿ B)
      where
      -- v and suc v exhaust {A , B}, so 2 + v is neither.
      two-free : (v ≡ A) ⊎ (v ≡ B) → (suc v ≡ A) ⊎ (suc v ≡ B) →
                 (suc (suc v) ≢ A) × (suc (suc v) ≢ B)
      two-free (inj₁ p) (inj₁ q) = ⊥-elim (≢suc v (Eq.trans p (Eq.sym q)))
      two-free (inj₂ p) (inj₂ q) = ⊥-elim (≢suc v (Eq.trans p (Eq.sym q)))
      two-free (inj₁ p) (inj₂ q) =
        (λ x → ≢suc² v (Eq.trans p (Eq.sym x)))
        , (λ x → ≢suc (suc v) (Eq.trans q (Eq.sym x)))
      two-free (inj₂ p) (inj₁ q) =
        (λ x → ≢suc (suc v) (Eq.trans q (Eq.sym x)))
        , (λ x → ≢suc² v (Eq.trans p (Eq.sym x)))

      c₂ : (v ≡ A) ⊎ (v ≡ B) → (suc v ≡ A) ⊎ (suc v ≡ B) →
           Res v (fr 3 (suc (suc v)) A B A B)
      c₂ u₀ u₁ = go (two-free u₀ u₁)
        where
        go : (suc (suc v) ≢ A) × (suc (suc v) ≢ B) →
             Res v (fr 3 (suc (suc v)) A B A B)
        go (na , nb) rewrite blk-f A B (suc (suc v)) na nb =
          na , nb , m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl) , ≤-refl

      c₁ : (v ≡ A) ⊎ (v ≡ B) → Dec (suc v ≡ A) → Dec (suc v ≡ B) →
           Res v (fr 4 (suc v) A B A B)
      c₁ u₀ (no na) (no nb) rewrite blk-f A B (suc v) na nb =
        na , nb , m≤n⇒m≤1+n ≤-refl , m≤n⇒m≤1+n ≤-refl
      c₁ u₀ (yes p) _ rewrite blk-ta A B (suc v) p = c₂ u₀ (inj₁ p)
      c₁ u₀ (no _) (yes p) rewrite blk-tb A B (suc v) p = c₂ u₀ (inj₂ p)

      c₀ : Dec (v ≡ A) → Dec (v ≡ B) → Res v (fr 5 v A B A B)
      c₀ (no na) (no nb) rewrite blk-f A B v na nb =
        na , nb , ≤-refl , m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)
      c₀ (yes p) _ rewrite blk-ta A B v p = c₁ (inj₁ p) (suc v ≟ⁿ A) (suc v ≟ⁿ B)
      c₀ (no _) (yes p) rewrite blk-tb A B v p = c₁ (inj₂ p) (suc v ≟ⁿ A) (suc v ≟ⁿ B)

    R₀ = fresh 0
    R₁ = fresh (suc e)

  e≢A : e ≢ A
  e≢A = proj₁ R₀

  e≢B : e ≢ B
  e≢B = proj₁ (proj₂ R₀)

  f≢A : f ≢ A
  f≢A = proj₁ R₁

  f≢B : f ≢ B
  f≢B = proj₁ (proj₂ R₁)

  e<f : e < f
  e<f = proj₁ (proj₂ (proj₂ R₁))

  private
    e≤2 : e ≤ 2
    e≤2 = proj₂ (proj₂ (proj₂ R₀))

    f≤5 : f ≤ 5
    f≤5 = ≤-trans (proj₂ (proj₂ (proj₂ R₁))) (s≤s (s≤s (s≤s e≤2)))

  e<N : e < N
  e<N = ≤-trans (≤-trans (s≤s e≤2) (s≤s (s≤s (s≤s z≤n)))) (8≤2^ m)

  f<N : f < N
  f<N = ≤-trans (≤-trans (s≤s f≤5)
                         (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))
                (8≤2^ m)

------------------------------------------------------------------------
-- The letter with four repeated indices is not `distinct4`

d4-same : ∀ (A B : ℕ) → distinct4 A B A B ≡ false
d4-same A B rewrite ≡ᵇ-refl A = ∧-zeroʳ (not (A ≡ᵇ B))

------------------------------------------------------------------------
-- Figure 10

module _ (e65 : Eq65) where

  ----------------------------------------------------------------------
  -- (66): the two pairs commute

  eq66 : ∀ (a b c d : Fin N) → a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d →
         hh {₃₊ m} a b c d ≈ hh {₃₊ m} c d a b
  eq66 a b c d ab ac ad bc bd cd =
    trans (e65 a b c d ab ac ad bc bd cd)
          (trans middle (sym (e65 c d a b cd (≢sym ac) (≢sym bc)
                                          (≢sym ad) (≢sym bd) ab)))
    where
    module L = E65.Tuple a b c d ab ac ad bc bd cd
    module R = E65.Tuple c d a b cd (≢sym ac) (≢sym bc) (≢sym ad) (≢sym bd) ab

    -- Both sides carry the pair's two powers of 1/√2 and the same
    -- matrix.  Composing scale and matrix separately, rather than two
    -- `_~_`s, is what keeps this cheap: a `_~_` between two nine-letter
    -- words expands, when compared, into a sum over bitstrings per
    -- letter.
    sem : ⟦ L.Σw • (Λ • L.Σ′w) ⟧ʷ ~ ⟦ R.Σw • (Λ • R.Σ′w) ⟧ʷ
    sem = ~-reflexive (Eq.trans L.conj-scale (Eq.sym R.conj-scale))
                      (≐-trans L.conj-op
                        (≐-trans (HH2-comm (code n a) (code n b)
                                           (code n c) (code n d)
                                           (dif ab) (dif cd) (dif ac)
                                           (dif ad) (dif bc) (dif bd))
                                 (≐-sym R.conj-op)))

    middle : L.Σw • (Λ • L.Σ′w) ≈ R.Σw • (Λ • R.Σ′w)
    middle = A7 L.hfree-Σ L.hfree-Σ′ R.hfree-Σ R.hfree-Σ′ L.ΣΣ′ R.ΣΣ′ sem

  ----------------------------------------------------------------------
  -- (70): a Hadamard pair squared
  --
  -- Equation (42) splits the letter over two indices fresh to a and b;
  -- (66) turns the second factor round; (65) writes both as Definition
  -- E.1's words around the standard pair; and then the inner Σ′Σ
  -- cancels, the two standard pairs cancel by (41), and the outer ΣΣ′
  -- cancels.

  eq70 : ∀ (a b : Fin N) → a ≢ b → hh {₃₊ m} a b a b ≈ ε
  eq70 a b ab =
    trans split
    (trans (back E (eq66 e′ f′ a b ef ea eb fa fb ab))
    (trans (cong (e65 a b e′ f′ ab ae af be bf ef)
                 (e65 a b e′ f′ ab ae af be bf ef))
           cancel))
    where
    A B : ℕ
    A = toℕ a
    B = toℕ b

    AB : A ≢ B
    AB e = ab (toℕ-injective e)

    -- The two fresh indices.
    e f : ℕ
    e = fr 5 0 A B A B
    f = fr 5 (suc e) A B A B

    open Fresh A B AB using (e≢A ; e≢B ; f≢A ; f≢B ; e<f ; e<N ; f<N)

    e′ f′ : Fin N
    e′ = fin e e<N
    f′ = fin f f<N

    ea : e′ ≢ a
    ea x = e≢A (Eq.trans (Eq.sym (fin-toℕ e e<N)) (Eq.cong toℕ x))

    eb : e′ ≢ b
    eb x = e≢B (Eq.trans (Eq.sym (fin-toℕ e e<N)) (Eq.cong toℕ x))

    fa : f′ ≢ a
    fa x = f≢A (Eq.trans (Eq.sym (fin-toℕ f f<N)) (Eq.cong toℕ x))

    fb : f′ ≢ b
    fb x = f≢B (Eq.trans (Eq.sym (fin-toℕ f f<N)) (Eq.cong toℕ x))

    ae : a ≢ e′
    ae = ≢sym ea

    af : a ≢ f′
    af = ≢sym fa

    be : b ≢ e′
    be = ≢sym eb

    bf : b ≢ f′
    bf = ≢sym fb

    ef : e′ ≢ f′
    ef x = <-irrefl (Eq.trans (Eq.sym (fin-toℕ e e<N))
                      (Eq.trans (Eq.cong toℕ x) (fin-toℕ f f<N))) e<f

    E F : W
    E = hh {₃₊ m} a b e′ f′
    F = hh {₃₊ m} e′ f′ a b

    conv : hhℕ {₃₊ m} A B e f ≡ E
    conv = Eq.trans (Eq.cong₂ (λ s t → hhℕ {₃₊ m} A B s t)
                              (Eq.sym (fin-toℕ e e<N)) (Eq.sym (fin-toℕ f f<N)))
                    (hhℕ-hh a b e′ f′)

    conv′ : hhℕ {₃₊ m} e f A B ≡ F
    conv′ = Eq.trans (Eq.cong₂ (λ s t → hhℕ {₃₊ m} s t A B)
                               (Eq.sym (fin-toℕ e e<N)) (Eq.sym (fin-toℕ f f<N)))
                     (hhℕ-hh e′ f′ a b)

    split : hh {₃₊ m} a b a b ≈ E • F
    split = trans (sym (axiom (r42 a b a b ab ab (d4-same A B))))
                  (refl≡ (Eq.cong₂ _•_ conv conv′))

    module T = E65.Tuple a b e′ f′ ab ae af be bf ef

    X : W
    X = T.Σw • (Λ • T.Σ′w)

    cancel : X • X ≈ ε
    cancel = begin
      (T.Σw • (Λ • T.Σ′w)) • (T.Σw • (Λ • T.Σ′w))
        ≈⟨ assoc ⟩
      T.Σw • ((Λ • T.Σ′w) • (T.Σw • (Λ • T.Σ′w)))
        ≈⟨ back T.Σw assoc ⟩
      T.Σw • (Λ • (T.Σ′w • (T.Σw • (Λ • T.Σ′w))))
        ≈⟨ back T.Σw (back Λ (sym assoc)) ⟩
      T.Σw • (Λ • ((T.Σ′w • T.Σw) • (Λ • T.Σ′w)))
        ≈⟨ back T.Σw (back Λ (front (Λ • T.Σ′w) T.Σ′Σ-≈)) ⟩
      T.Σw • (Λ • (ε • (Λ • T.Σ′w)))
        ≈⟨ back T.Σw (back Λ left-unit) ⟩
      T.Σw • (Λ • (Λ • T.Σ′w))
        ≈⟨ back T.Σw (sym assoc) ⟩
      T.Σw • ((Λ • Λ) • T.Σ′w)
        ≈⟨ back T.Σw (front T.Σ′w (axiom r41)) ⟩
      T.Σw • (ε • T.Σ′w)
        ≈⟨ back T.Σw left-unit ⟩
      T.Σw • T.Σ′w
        ≈⟨ T.ΣΣ′-≈ ⟩
      ε ∎

  ----------------------------------------------------------------------
  -- (74), and the general fact behind it
  --
  -- A Hadamard-free word that neither moves nor signs any of the four
  -- indices of a pair commutes with it.  By (65) the pair is Σ Λ Σ′,
  -- and conjugating the word by Σ gives a word that neither moves nor
  -- signs an index below 4 — which is Lemma A.6's `passes-low`.  The
  -- two conjugations are Corollary A.5, the signed permutations being
  -- equal by construction.

  module _ (c d e f : Fin N)
           (cd : c ≢ d) (ce : c ≢ e) (cf : c ≢ f)
           (de : d ≢ e) (df : d ≢ f) (ef : e ≢ f)
    where

    private
      module S = E65.Tuple c d e f cd ce cf de df ef

      -- Σ′ undoes Σ on the four low indices.
      pre : ∀ (x : Fin N) (k : Fin N) → prm (sp S.Σw) x ≡ k →
            prm (sp S.Σ′w) k ≡ x
      pre x k h =
        sp-inj S.Σw
          (Eq.trans (prm≡′ (⊙-inverse (sp S.Σw) (sp S.Σ′w) (sp-inj S.Σ′w) S.Σ-inv) k)
                    (Eq.sym h))

      -- And carries the same sign there.
      pre-sgn : ∀ (x : Fin N) (k : Fin N) → prm (sp S.Σw) x ≡ k →
                sgn (sp S.Σw) x ≡ false → sgn (sp S.Σ′w) k ≡ false
      pre-sgn x k h s = go (sgn≡′ S.Σ-inv x)
        where
        go : sgn (sp S.Σw) x xor sgn (sp S.Σ′w) (prm (sp S.Σw) x) ≡ false →
             sgn (sp S.Σ′w) k ≡ false
        go q = Eq.trans (Eq.cong (sgn (sp S.Σ′w)) (Eq.sym h))
                        (step (sgn (sp S.Σw) x) s q)
          where
          step : ∀ (t : Bool) → t ≡ false →
                 t xor sgn (sp S.Σ′w) (prm (sp S.Σw) x) ≡ false →
                 sgn (sp S.Σ′w) (prm (sp S.Σw) x) ≡ false
          step .false Eq.refl q′ = q′

      pc : prm (sp S.Σw) c ≡ i₀
      pc = toℕ-injective (Eq.trans S.prm-Σ-a (Eq.sym toℕ-i₀))

      pd : prm (sp S.Σw) d ≡ i₁
      pd = toℕ-injective (Eq.trans S.prm-Σ-b (Eq.sym toℕ-i₁))

      pe : prm (sp S.Σw) e ≡ i₃
      pe = toℕ-injective (Eq.trans S.prm-Σ-c (Eq.sym toℕ-i₃))

      pf : prm (sp S.Σw) f ≡ i₂
      pf = toℕ-injective (Eq.trans S.prm-Σ-d (Eq.sym toℕ-i₂))

    pair-comm : ∀ {u : W} → HFreeʷ u →
                prm (sp u) c ≡ c → prm (sp u) d ≡ d →
                prm (sp u) e ≡ e → prm (sp u) f ≡ f →
                sgn (sp u) c ≡ false → sgn (sp u) d ≡ false →
                sgn (sp u) e ≡ false → sgn (sp u) f ≡ false →
                u • hh {₃₊ m} c d e f ≈ hh {₃₊ m} c d e f • u
    pair-comm {u} hu qc qd qe qf tc td te tf = begin
      u • hh {₃₊ m} c d e f
        ≈⟨ back u (e65 c d e f cd ce cf de df ef) ⟩
      u • (S.Σw • (Λ • S.Σ′w))
        ≈⟨ sym assoc ⟩
      (u • S.Σw) • (Λ • S.Σ′w)
        ≈⟨ front (Λ • S.Σ′w) shiftˡ ⟩
      (S.Σw • K) • (Λ • S.Σ′w)
        ≈⟨ assoc ⟩
      S.Σw • (K • (Λ • S.Σ′w))
        ≈⟨ back S.Σw (sym assoc) ⟩
      S.Σw • ((K • Λ) • S.Σ′w)
        ≈⟨ back S.Σw (front S.Σ′w passK) ⟩
      S.Σw • ((Λ • K) • S.Σ′w)
        ≈⟨ back S.Σw assoc ⟩
      S.Σw • (Λ • (K • S.Σ′w))
        ≈⟨ back S.Σw (back Λ shiftʳ) ⟩
      S.Σw • (Λ • (S.Σ′w • u))
        ≈⟨ back S.Σw (sym assoc) ⟩
      S.Σw • ((Λ • S.Σ′w) • u)
        ≈⟨ sym assoc ⟩
      (S.Σw • (Λ • S.Σ′w)) • u
        ≈⟨ front u (sym (e65 c d e f cd ce cf de df ef)) ⟩
      hh {₃₊ m} c d e f • u ∎
      where
      -- The word conjugated into the standard frame.
      K : W
      K = S.Σ′w • (u • S.Σw)

      hK : HFreeʷ K
      hK = cat S.hfree-Σ′ (cat hu S.hfree-Σ)

      -- Moving `u` across Σ, and back across Σ′.
      shiftˡ : u • S.Σw ≈ S.Σw • K
      shiftˡ = A5-full (cat hu S.hfree-Σ) (cat S.hfree-Σ hK)
        (≐-sym′ (≐-trans′ (≐-sym′ (⊙-assoc′ (sp S.Σw) (sp S.Σ′w) (sp u ⊛ sp S.Σw)))
                          (≐-trans′ (⊙-cong′ S.Σ-inv (≐-refl′ {sp u ⊛ sp S.Σw}))
                                    (⊙-idˡ′ (sp u ⊛ sp S.Σw)))))

      shiftʳ : K • S.Σ′w ≈ S.Σ′w • u
      shiftʳ = A5-full (cat hK S.hfree-Σ′) (cat S.hfree-Σ′ hu)
        (≐-trans′ (⊙-assoc′ (sp S.Σ′w) (sp u ⊛ sp S.Σw) (sp S.Σ′w))
          (⊙-cong′ (≐-refl′ {sp S.Σ′w})
            (≐-trans′ (⊙-assoc′ (sp u) (sp S.Σw) (sp S.Σ′w))
              (≐-trans′ (⊙-cong′ (≐-refl′ {sp u}) S.Σ-inv)
                        (⊙-idʳ′ (sp u))))))

      -- And it passes the standard pair.
      passK : K • Λ ≈ Λ • K
      passK = passes-low hK
        (four-of {λ t → prm (sp K) t ≡ t} fix₀ fix₁ fix₂ fix₃)
        (four-of {λ t → sgn (sp K) t ≡ false} sg₀ sg₁ sg₂ sg₃)
        where
        move : ∀ (x k : Fin N) → prm (sp S.Σw) x ≡ k → prm (sp u) x ≡ x →
               prm (sp K) k ≡ k
        move x k h q =
          Eq.trans (Eq.cong (λ z → prm (sp S.Σw) (prm (sp u) z)) (pre x k h))
                   (Eq.trans (Eq.cong (prm (sp S.Σw)) q) h)

        sign : ∀ (x k : Fin N) → prm (sp S.Σw) x ≡ k → prm (sp u) x ≡ x →
               sgn (sp S.Σw) x ≡ false → sgn (sp u) x ≡ false →
               sgn (sp K) k ≡ false
        sign x k h q s t =
          Eq.trans (Eq.cong₂ _xor_ (pre-sgn x k h s)
                     (Eq.cong₂ _xor_
                       (Eq.trans (Eq.cong (sgn (sp u)) (pre x k h)) t)
                       (Eq.trans (Eq.cong (λ z → sgn (sp S.Σw) (prm (sp u) z))
                                          (pre x k h))
                                 (Eq.trans (Eq.cong (sgn (sp S.Σw)) q) s))))
                   Eq.refl

        fix₀ = move c i₀ pc qc
        fix₁ = move d i₁ pd qd
        fix₂ = move f i₂ pf qf
        fix₃ = move e i₃ pe qe

        sg₀ = sign c i₀ pc qc S.sgn-Σ-a tc
        sg₁ = sign d i₁ pd qd S.sgn-Σ-b td
        sg₂ = sign f i₂ pf qf S.sgn-Σ-d tf
        sg₃ = sign e i₃ pe qe S.sgn-Σ-c te

    -- Closed under products and containing the empty word, so this is
    -- a commutation kit and not only one equation.
    comm-ε : ε • hh {₃₊ m} c d e f ≈ hh {₃₊ m} c d e f • ε
    comm-ε = trans left-unit (sym right-unit)

    comm-• : ∀ {u v : W} →
             u • hh {₃₊ m} c d e f ≈ hh {₃₊ m} c d e f • u →
             v • hh {₃₊ m} c d e f ≈ hh {₃₊ m} c d e f • v →
             (u • v) • hh {₃₊ m} c d e f ≈ hh {₃₊ m} c d e f • (u • v)
    comm-• {u} {v} pu pv = begin
      (u • v) • hh {₃₊ m} c d e f   ≈⟨ assoc ⟩
      u • (v • hh {₃₊ m} c d e f)   ≈⟨ back u pv ⟩
      u • (hh {₃₊ m} c d e f • v)   ≈⟨ sym assoc ⟩
      (u • hh {₃₊ m} c d e f) • v   ≈⟨ front v pu ⟩
      (hh {₃₊ m} c d e f • u) • v   ≈⟨ assoc ⟩
      hh {₃₊ m} c d e f • (u • v)  ∎

    -- (74): a mixed letter away from the pair commutes with it.
    eq74 : ∀ (g x y : Fin N) →
           g ≢ c → g ≢ d → g ≢ e → g ≢ f →
           x ≢ c → x ≢ d → x ≢ e → x ≢ f →
           y ≢ c → y ≢ d → y ≢ e → y ≢ f →
           zx {₃₊ m} g x y • hh {₃₊ m} c d e f
           ≈ hh {₃₊ m} c d e f • zx {₃₊ m} g x y
    eq74 g x y gc gd ge gf xc xd xe xf yc yd ye yf =
      pair-comm (hfree-zx g x y)
        (mv c (≢sym xc) (≢sym yc)) (mv d (≢sym xd) (≢sym yd))
        (mv e (≢sym xe) (≢sym ye)) (mv f (≢sym xf) (≢sym yf))
        (sg c (≢sym gc)) (sg d (≢sym gd)) (sg e (≢sym ge)) (sg f (≢sym gf))
      where
      mv : ∀ (t : Fin N) → t ≢ x → t ≢ y → prm (sp (zx {₃₊ m} g x y)) t ≡ t
      mv t tx ty = Eq.trans (zx-prm g x y t) (swapF-o x y t tx ty)

      sg : ∀ (t : Fin N) → t ≢ g → sgn (sp (zx {₃₊ m} g x y)) t ≡ false
      sg t tg = zx-sgn g x y t tg

    -- And so does a sign pair away from it.
    comm-zz : ∀ (x y : Fin N) →
              x ≢ c → x ≢ d → x ≢ e → x ≢ f →
              y ≢ c → y ≢ d → y ≢ e → y ≢ f →
              zz {₃₊ m} x y • hh {₃₊ m} c d e f
              ≈ hh {₃₊ m} c d e f • zz {₃₊ m} x y
    comm-zz x y xc xd xe xf yc yd ye yf =
      pair-comm (gen (hf-zz x y))
        Eq.refl Eq.refl Eq.refl Eq.refl
        (sg c (≢sym xc) (≢sym yc)) (sg d (≢sym xd) (≢sym yd))
        (sg e (≢sym xe) (≢sym ye)) (sg f (≢sym xf) (≢sym yf))
      where
      sg : ∀ (t : Fin N) → t ≢ x → t ≢ y → sgn (sp (zz {₃₊ m} x y)) t ≡ false
      sg t tx ty = Eq.trans (Eq.cong₂ _xor_ (δ-≢ x t tx) (δ-≢ y t ty)) Eq.refl

    -- An index away from all four.
    Off : Fin N → Set
    Off x = (x ≢ c) × (x ≢ d) × (x ≢ e) × (x ≢ f)

    -- The third letter shape, so the kit covers every Hadamard-free
    -- word whose letters stay away from the pair.
    comm-xx : ∀ (x y u v : Fin N) → x ≢ y → u ≢ v →
              Off x → Off y → Off u → Off v →
              xx {₃₊ m} x y u v • hh {₃₊ m} c d e f
              ≈ hh {₃₊ m} c d e f • xx {₃₊ m} x y u v
    comm-xx x y u v xy uv ox oy ou ov =
      pair-comm hfree
        (mv c (off₁ ox) (off₁ oy) (off₁ ou) (off₁ ov))
        (mv d (off₂ ox) (off₂ oy) (off₂ ou) (off₂ ov))
        (mv e (off₃ ox) (off₃ oy) (off₃ ou) (off₃ ov))
        (mv f (off₄ ox) (off₄ oy) (off₄ ou) (off₄ ov))
        (sg c) (sg d) (sg e) (sg f)
      where
      off₁ : ∀ {t : Fin N} → Off t → c ≢ t
      off₁ (p , _) = ≢sym p

      off₂ : ∀ {t : Fin N} → Off t → d ≢ t
      off₂ (_ , p , _) = ≢sym p

      off₃ : ∀ {t : Fin N} → Off t → e ≢ t
      off₃ (_ , _ , p , _) = ≢sym p

      off₄ : ∀ {t : Fin N} → Off t → f ≢ t
      off₄ (_ , _ , _ , p) = ≢sym p

      hfree : HFreeʷ (xx {₃₊ m} x y u v)
      hfree = Eq.subst HFreeʷ (gen-xx x y u v xy uv) (gen (hf-xx x y u v xy uv))

      mv : ∀ (t : Fin N) → t ≢ x → t ≢ y → t ≢ u → t ≢ v →
           prm (sp (xx {₃₊ m} x y u v)) t ≡ t
      mv t tx ty tu tv =
        Eq.trans (prm≡′ (sp-xx x y u v xy uv) t)
                 (Eq.trans (Eq.cong (swapF u v) (swapF-o x y t tx ty))
                           (swapF-o u v t tu tv))

      sg : ∀ (t : Fin N) → sgn (sp (xx {₃₊ m} x y u v)) t ≡ false
      sg t = sgn≡′ (sp-xx x y u v xy uv) t

------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness, reduced to the Main Lemma (§3.3).
--
-- The normal word of a column-orthonormal matrix M is the output of the
-- synthesis algorithm, so ⟦ nw M ⟧ M = I.  Completeness follows from
--
--   Path w M :  nw (w·M) • w ≈ nw M       for every word w,
--
-- since two words u, v with ⟦ u ⟧ = ⟦ v ⟧ are then both paths from I
-- to the same matrix, and cancel.  Path reduces to the edges of basic
-- generators (Lemma 3.8), which are proved by well-founded induction
-- on the level of the source (Lemma 3.9), each induction step being an
-- instance of the Main Lemma.
--
-- This module takes as hypotheses the three facts that the rest of the
-- development proves by case analysis: the Main Lemma, the base case
-- (the edges out of I), and that expanding a generator into basic ones
-- does not raise the level.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Reduction {n : ℕ} where

open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Product.Base using (Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Induction.WellFounded using (Acc ; acc)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring using (D)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Soundness using (sound-axiom)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Pivot using (pivot ; pivot-nothing ; Lvl ; level ; _<ₗ_ ; <ₗ-wellFounded)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syllable using (syl ; step)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Synthesis using (synth ; synth-step)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Derived {n} using (•-cancelˡ)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Basic {n} using (IsBasic ; Basicʷ ; expand ; expand-≈ ; expand-basic)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  variable
    L : Lvl

------------------------------------------------------------------------
-- Soundness, for the congruence: related words act alike

sound-act : {w v : Word (Gen n)} → w ≈ v → ∀ (M : Matrix n n D) → actMʷ w M ≡ actMʷ v M
sound-act refl M = ≡.refl
sound-act (sym h) M = ≡.sym (sound-act h M)
sound-act (trans h k) M = ≡.trans (sound-act h M) (sound-act k M)
sound-act (cong {w} {w′} {v} {v′} h k) M =
  ≡.trans (≡.cong (actMʷ w) (sound-act k M)) (sound-act h (actMʷ v′ M))
sound-act assoc M = ≡.refl
sound-act left-unit M = ≡.refl
sound-act right-unit M = ≡.refl
sound-act (axiom {w} {v} a) M =
  ≡.trans (actMʷ≡ w M) (≡.trans (·*·-congˡ ⟦ w ⟧ᵐ ⟦ v ⟧ᵐ M (sound-axiom a)) (≡.sym (actMʷ≡ v M)))
  where
  -- Congruence with explicit endpoints (cong would leave them as metas
  -- under the matrix product, which the conversion checker unfolds).
  ·*·-congˡ : (A B M : Matrix n n D) → A ≡ B → A ·*· M ≡ B ·*· M
  ·*·-congˡ A B M ≡.refl = ≡.refl

------------------------------------------------------------------------
-- Normal words and paths

nw : (M : Matrix n n D) → .(ColOrth M) → Word (Gen n)
nw = synth

-- The normal word depends on the matrix alone.  (The equation comes
-- first: it determines the matrices, which the irrelevant proofs do
-- not, and leaving them to be inferred from those is intractable.)
nw-cong : {M M′ : Matrix n n D} → M ≡ M′ → .(o : ColOrth M) .(o′ : ColOrth M′) → nw M o ≡ nw M′ o′
nw-cong ≡.refl o o′ = ≡.refl

-- w leads from M to w·M: the normal word of M is that of w·M, then w.
Path : (w : Word (Gen n)) (M : Matrix n n D) → .(ColOrth M) → Set
Path w M o = nw (actMʷ w M) (ColOrth-actMʷ w o) • w ≈ nw M o


path-ε : (M : Matrix n n D) .(o : ColOrth M) → Path ε M o
path-ε M o = right-unit

path-• : (u v : Word (Gen n)) (M : Matrix n n D) .(o : ColOrth M) →
         Path u (actMʷ v M) (ColOrth-actMʷ v o) → Path v M o → Path (u • v) M o
path-• u v M o pu pv = begin
  nw (actMʷ u (actMʷ v M)) (ColOrth-actMʷ (u • v) o) • (u • v)    ≈⟨ sym assoc ⟩
  (nw (actMʷ u (actMʷ v M)) (ColOrth-actMʷ (u • v) o) • u) • v    ≈⟨ cleft pu ⟩
  nw (actMʷ v M) (ColOrth-actMʷ v o) • v                          ≈⟨ pv ⟩
  nw M o                                                          ∎

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

-- A generator, through its basic expansion.
path-expand : (g : Gen n) (M : Matrix n n D) .(o : ColOrth M) → Path (expand g) M o → Path [ g ]ʷ M o
path-expand g M o pe = begin
  nw (actM g M) (ColOrth-actMʷ [ g ]ʷ o) • [ g ]ʷ                  ≈⟨ cright expand-≈ g ⟩
  nw (actM g M) (ColOrth-actMʷ [ g ]ʷ o) • expand g                ≈⟨ cleft refl′ (nw-cong (sound-act (expand-≈ g) M) (ColOrth-actMʷ [ g ]ʷ o)
                                                                       (ColOrth-actMʷ (expand g) o)) ⟩
  nw (actMʷ (expand g) M) (ColOrth-actMʷ (expand g) o) • expand g  ≈⟨ pe ⟩
  nw M o                                                           ∎

------------------------------------------------------------------------
-- Levels along a path

-- Every state along w from M, the last one included, lies below L.
Below : Lvl → Word (Gen n) → Matrix n n D → Set
Below L [ g ]ʷ M = level M <ₗ L × level (actM g M) <ₗ L
Below L ε M = ⊤
Below L (u • v) M = Below L v M × Below L u (actMʷ v M)

-- Every state along w from M that some letter leaves lies below L.
BelowSrc : Lvl → Word (Gen n) → Matrix n n D → Set
BelowSrc L [ g ]ʷ M = level M <ₗ L
BelowSrc L ε M = ⊤
BelowSrc L (u • v) M = BelowSrc L v M × BelowSrc L u (actMʷ v M)

------------------------------------------------------------------------
-- The three hypotheses

-- The Main Lemma (Lemma 3.6): a basic edge s → r and the normal edge
-- s ⇒ t = step s close up, relationally, through a normal path N′
-- from r to some q and a path G′ from t to q below the level of s.
-- (A Σ-type rather than a record: a record whose fields mention the
-- step of a matrix over 𝔻[i] is intractable to declare.)
Square : (G : Gen n) (s : Matrix n n D) → .(ColOrth s) → Set
Square G s o =
  Σ[ N′ ∈ Word (Gen n) ] Σ[ G′ ∈ Word (Gen n) ]
    Path N′ (actM G s) (ColOrth-actMʷ [ G ]ʷ o)
  × actMʷ G′ (step s) ≡ actMʷ N′ (actM G s)
  × Below (level s) G′ (step s)
  × N′ • [ G ]ʷ ≈ G′ • syl s

MainLemma : Set
MainLemma = ∀ (G : Gen n) → IsBasic G → ∀ s .(o : ColOrth s) {p : Fin n} → pivot s ≡ just p → Square G s o

-- The basic edges out of I.
Base : Set
Base = ∀ (G : Gen n) → IsBasic G → Path [ G ]ʷ 𝕀 ColOrth-𝕀

-- Expanding a generator into basic ones stays below any level that
-- both ends of the edge lie below.
ExpLevel : Set
ExpLevel = ∀ (g : Gen n) (M : Matrix n n D) → .(ColOrth M) → ∀ L →
           level M <ₗ L → level (actM g M) <ₗ L → BelowSrc L (expand g) M

------------------------------------------------------------------------
-- The reduction

module _ (main : MainLemma) (base : Base) (exp-level : ExpLevel) where

  -- The basic edges from states below L.
  EdgesBelow : Lvl → Set
  EdgesBelow L = ∀ (G : Gen n) → IsBasic G → ∀ M .(o : ColOrth M) → level M <ₗ L → Path [ G ]ʷ M o

  private
    path-basic : EdgesBelow L → (w : Word (Gen n)) → Basicʷ w → ∀ M .(o : ColOrth M) →
                 BelowSrc L w M → Path w M o
    path-basic ih [ g ]ʷ bg M o lt = ih g bg M o lt
    path-basic ih ε _ M o _ = path-ε M o
    path-basic ih (u • v) (bu , bv) M o (lv , lu) =
      path-• u v M o (path-basic ih u bu (actMʷ v M) (ColOrth-actMʷ v o) lu) (path-basic ih v bv M o lv)

    path-below : EdgesBelow L → (w : Word (Gen n)) → ∀ M .(o : ColOrth M) → Below L w M → Path w M o
    path-below {L} ih [ g ]ʷ M o (l₀ , l₁) =
      path-expand g M o (path-basic ih (expand g) (expand-basic g) M o (exp-level g M o L l₀ l₁))
    path-below ih ε M o _ = path-ε M o
    path-below ih (u • v) M o (bv , bu) =
      path-• u v M o (path-below ih u (actMʷ v M) (ColOrth-actMʷ v o) bu) (path-below ih v M o bv)

    -- The Main Lemma closes the induction step.
    square⇒edge : ∀ (G : Gen n) s .(o : ColOrth s) {p : Fin n} → pivot s ≡ just p →
                  EdgesBelow (level s) → Square G s o → Path [ G ]ʷ s o
    square⇒edge G s o pv ih (N′ , G′ , normal , meet , below , rel) = begin
      nw r (ColOrth-actMʷ [ G ]ʷ o) • [ G ]ʷ                      ≈⟨ cleft sym normal ⟩
      (nw (actMʷ N′ r) (ColOrth-actMʷ N′ (ColOrth-actMʷ [ G ]ʷ o)) • N′) • [ G ]ʷ
                                                                   ≈⟨ assoc ⟩
      nw (actMʷ N′ r) (ColOrth-actMʷ N′ (ColOrth-actMʷ [ G ]ʷ o)) • (N′ • [ G ]ʷ)
                                                                   ≈⟨ cright rel ⟩
      nw (actMʷ N′ r) (ColOrth-actMʷ N′ (ColOrth-actMʷ [ G ]ʷ o)) • (G′ • syl s)
                                                                   ≈⟨ sym assoc ⟩
      (nw (actMʷ N′ r) (ColOrth-actMʷ N′ (ColOrth-actMʷ [ G ]ʷ o)) • G′) • syl s
                                                                   ≈⟨ cleft cleft refl′ (nw-cong (≡.sym meet) (ColOrth-actMʷ N′ (ColOrth-actMʷ [ G ]ʷ o))
                                                                                                 (ColOrth-actMʷ G′ (ColOrth-actMʷ (syl s) o))) ⟩
      (nw (actMʷ G′ t) (ColOrth-actMʷ G′ (ColOrth-actMʷ (syl s) o)) • G′) • syl s
                                                                   ≈⟨ cleft path-below ih G′ t (ColOrth-actMʷ (syl s) o) below ⟩
      nw t (ColOrth-actMʷ (syl s) o) • syl s                       ≈⟨ refl′ (≡.sym (synth-step s o pv)) ⟩
      nw s o                                                       ∎
      where
      r = actM G s
      t = step s

    edge-acc : ∀ L → Acc _<ₗ_ L → ∀ (G : Gen n) → IsBasic G → ∀ M .(o : ColOrth M) → level M ≡ L →
               Path [ G ]ʷ M o
    edge-acc L (acc rs) G bG M o ≡.refl = by-pivot (pivot M) ≡.refl
      where
      ih : EdgesBelow (level M)
      ih G′ bG′ M′ o′ lt = edge-acc (level M′) (rs lt) G′ bG′ M′ o′ ≡.refl
      by-pivot : (r : Maybe (Fin n)) → pivot M ≡ r → Path [ G ]ʷ M o
      by-pivot nothing pv = at-𝕀 (pivot-nothing M pv)
        where
        at-𝕀 : M ≡ 𝕀 → Path [ G ]ʷ M o
        at-𝕀 ≡.refl = base G bG
      by-pivot (just p) pv = square⇒edge G M o pv ih (main G bG M o pv)

  -- Lemma 3.5: every basic edge.
  edge : ∀ (G : Gen n) → IsBasic G → ∀ M .(o : ColOrth M) → Path [ G ]ʷ M o
  edge G bG M o = edge-acc (level M) (<ₗ-wellFounded (level M)) G bG M o ≡.refl

  private
    basic : (w : Word (Gen n)) → Basicʷ w → ∀ M .(o : ColOrth M) → Path w M o
    basic [ g ]ʷ bg M o = edge g bg M o
    basic ε _ M o = path-ε M o
    basic (u • v) (bu , bv) M o = path-• u v M o (basic u bu (actMʷ v M) (ColOrth-actMʷ v o)) (basic v bv M o)

  -- Lemma 3.4: every word.
  path : (w : Word (Gen n)) (M : Matrix n n D) .(o : ColOrth M) → Path w M o
  path [ g ]ʷ M o = path-expand g M o (basic (expand g) (expand-basic g) M o)
  path ε M o = path-ε M o
  path (u • v) M o = path-• u v M o (path u (actMʷ v M) (ColOrth-actMʷ v o)) (path v M o)

  -- Theorem 3.2: the relations are complete.
  completeness : {u v : Word (Gen n)} → ⟦ u ⟧ᵐ ≡ ⟦ v ⟧ᵐ → u ≈ v
  completeness {u} {v} eq = •-cancelˡ (begin
    nw ⟦ u ⟧ᵐ ou • u         ≈⟨ path u 𝕀 ColOrth-𝕀 ⟩
    nw 𝕀 ColOrth-𝕀           ≈⟨ sym (path v 𝕀 ColOrth-𝕀) ⟩
    nw ⟦ v ⟧ᵐ ov • v         ≈⟨ cleft refl′ (nw-cong (≡.sym eq) ov ou) ⟩
    nw ⟦ u ⟧ᵐ ou • v         ∎)
    where
    ou : ColOrth ⟦ u ⟧ᵐ
    ou = ColOrth-actMʷ u ColOrth-𝕀
    ov : ColOrth ⟦ v ⟧ᵐ
    ov = ColOrth-actMʷ v ColOrth-𝕀

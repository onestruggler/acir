------------------------------------------------------------------------
-- Presentations of groups
--
-- Tools for the Main Lemma (Lemma 3.6).
--
-- A square for a basic edge s → r = G s and the normal edge s ⇒ t is
-- given by a normal path N′ from r, a path G′ from t below the level
-- of s, and the relation N′ G ≈ G′ N; the two paths meet by soundness
-- (square-by).  Three shapes recur in the case analysis of the paper:
--
-- * disjoint: N is also the normal edge from r, and commutes with G;
-- * retrograde: the normal edge from r undoes G (N′ = N N_r, G′ = ε);
-- * merge: the normal edge from r, after G, is N (G′ = ε).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.Clifford+CS-TwoLevel.MainTools {n : ℕ} where

open import Data.Fin.Base using (Fin ; _<_)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary.Decidable using (recompute)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (D)
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics
open import Examples.Groups.Clifford+CS-TwoLevel.Soundness using (sound-axiom)
open import Examples.Groups.Clifford+CS-TwoLevel.Pivot
  using (pivot ; pivot-just ; pivot-char ; level ; _<ₗ_ ; _<ₗ?_)
open import Examples.Groups.Clifford+CS-TwoLevel.Syllable
  using (syl ; step ; top ; Beyond-actM ; actV-e-beyond)
open import Examples.Groups.Clifford+CS-TwoLevel.Step using (step-lt)
open import Examples.Groups.Clifford+CS-TwoLevel.Synthesis using (synth-step)
open import Examples.Groups.Clifford+CS-TwoLevel.Derived {n} using (_⁻¹ ; inverseˡ ; Apartʷʷ ; comm-words)
open import Examples.Groups.Clifford+CS-TwoLevel.Reduction {n}
  using (nw ; nw-cong ; Path ; Below ; Square ; sound-act)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

------------------------------------------------------------------------
-- Soundness on vectors, and the generators are injective

sound-vec : {w v : Word (Gen n)} → w ≈ v → (u : Vec D n) → actVʷ w u ≡ actVʷ v u
sound-vec refl u = ≡.refl
sound-vec (sym h) u = ≡.sym (sound-vec h u)
sound-vec (trans h k) u = ≡.trans (sound-vec h u) (sound-vec k u)
sound-vec (cong {w} {w′} {v} {v′} h k) u =
  ≡.trans (≡.cong (actVʷ w) (sound-vec k u)) (sound-vec h (actVʷ v′ u))
sound-vec assoc u = ≡.refl
sound-vec left-unit u = ≡.refl
sound-vec right-unit u = ≡.refl
sound-vec (axiom {w} {v} a) u = same-action w v (sound-axiom a) u

act-inj : (g : Gen n) {u v : Vec D n} → actV g u ≡ actV g v → u ≡ v
act-inj g {u} {v} eq =
  ≡.trans (≡.sym (sound-vec (inverseˡ {[ g ]ʷ}) u))
    (≡.trans (≡.cong (actVʷ ([ g ]ʷ ⁻¹)) eq) (sound-vec (inverseˡ {[ g ]ʷ}) v))

-- A generator below the pivot keeps it.
pivot-keep : (g : Gen n) {p : Fin n} (M : Matrix n n D) → top g < p → pivot M ≡ just p →
             pivot (actM g M) ≡ just p
pivot-keep g {p} M tg pv = pivot-char (actM g M) ne (Beyond-actM g {M = M} (ℕP.<⇒≤ tg) (proj₂ (pivot-just M pv)))
  where
  ne : col (actM g M) p ≢ col 𝕀 p
  ne eq = proj₁ (pivot-just M pv)
    (act-inj g (≡.trans (≡.sym (col-actM g M p)) (≡.trans eq (≡.sym (actV-e-beyond g FinP.≤-refl tg)))))

------------------------------------------------------------------------
-- Normal edges

-- The level drops along a normal edge (from an irrelevant proof of
-- column-orthonormality: the conclusion is decidable).
lt-step : (s : Matrix n n D) → .(ColOrth s) → ∀ {p} → pivot s ≡ just p → level (step s) <ₗ level s
lt-step s o pv = recompute (level (step s) <ₗ? level s) (step-lt o pv)

-- One normal edge is a normal path.
path-normal : (M : Matrix n n D) .(o : ColOrth M) {p : Fin n} → pivot M ≡ just p → Path (syl M) M o
path-normal M o pv = refl′ (≡.sym (synth-step M o pv))

------------------------------------------------------------------------
-- Squares

-- The two paths meet by soundness of the relation.
square-by : (G : Gen n) (s : Matrix n n D) .(o : ColOrth s) (N′ G′ : Word (Gen n)) →
            Path N′ (actM G s) (ColOrth-actMʷ [ G ]ʷ o) → Below (level s) G′ (step s) →
            N′ • [ G ]ʷ ≈ G′ • syl s → Square G s o
square-by G s o N′ G′ normal below rel = N′ , G′ , normal , ≡.sym (sound-act rel s) , below , rel

-- Disjoint: syl s is also the syllable of G s, and commutes with G.
square-disjoint : (G : Gen n) (s : Matrix n n D) .(o : ColOrth s) {p p′ : Fin n} →
                  pivot s ≡ just p → pivot (actM G s) ≡ just p′ → syl (actM G s) ≡ syl s →
                  Apartʷʷ (syl s) [ G ]ʷ → level (actM G (step s)) <ₗ level s → Square G s o
square-disjoint G s o ps pr eq ap lq =
  square-by G s o (syl s) [ G ]ʷ normal (lt-step s o ps , lq) (comm-words (syl s) [ G ]ʷ ap)
  where
  normal : Path (syl s) (actM G s) (ColOrth-actMʷ [ G ]ʷ o)
  normal = ≡.subst (λ N → Path N (actM G s) (ColOrth-actMʷ [ G ]ʷ o)) eq
             (path-normal (actM G s) (ColOrth-actMʷ [ G ]ʷ o) pr)

-- Retrograde: the syllable of G s undoes G.
square-retro : (G : Gen n) (s : Matrix n n D) .(o : ColOrth s) {p p′ : Fin n} →
               pivot s ≡ just p → pivot (actM G s) ≡ just p′ → syl (actM G s) • [ G ]ʷ ≈ ε → Square G s o
square-retro G s o ps pr back = square-by G s o (syl s • syl r) ε normal tt rel
  where
  r = actM G s
  step≡ : step r ≡ s
  step≡ = sound-act back s
  normal : Path (syl s • syl r) r (ColOrth-actMʷ [ G ]ʷ o)
  normal = begin
    nw (actMʷ (syl s) (step r)) (ColOrth-actMʷ (syl s • syl r) (ColOrth-actMʷ [ G ]ʷ o)) • (syl s • syl r)
      ≈⟨ sym assoc ⟩
    (nw (actMʷ (syl s) (step r)) (ColOrth-actMʷ (syl s • syl r) (ColOrth-actMʷ [ G ]ʷ o)) • syl s) • syl r
      ≈⟨ cleft cleft refl′ (nw-cong (≡.cong (actMʷ (syl s)) step≡) (ColOrth-actMʷ (syl s • syl r) (ColOrth-actMʷ [ G ]ʷ o))
                                    (ColOrth-actMʷ (syl s) o)) ⟩
    (nw (step s) (ColOrth-actMʷ (syl s) o) • syl s) • syl r
      ≈⟨ cleft path-normal s o ps ⟩
    nw s o • syl r
      ≈⟨ cleft refl′ (nw-cong (≡.sym step≡) o (ColOrth-actMʷ (syl r) (ColOrth-actMʷ [ G ]ʷ o))) ⟩
    nw (step r) (ColOrth-actMʷ (syl r) (ColOrth-actMʷ [ G ]ʷ o)) • syl r
      ≈⟨ path-normal r (ColOrth-actMʷ [ G ]ʷ o) pr ⟩
    nw r (ColOrth-actMʷ [ G ]ʷ o) ∎
  rel : (syl s • syl r) • [ G ]ʷ ≈ ε • syl s
  rel = begin
    (syl s • syl r) • [ G ]ʷ       ≈⟨ assoc ⟩
    syl s • (syl r • [ G ]ʷ)       ≈⟨ cright back ⟩
    syl s • ε                      ≈⟨ right-unit ⟩
    syl s                          ≈⟨ sym left-unit ⟩
    ε • syl s                      ∎

-- Merge: the syllable of G s, after G, is syl s.
square-merge : (G : Gen n) (s : Matrix n n D) .(o : ColOrth s) {p′ : Fin n} →
               pivot (actM G s) ≡ just p′ → syl (actM G s) • [ G ]ʷ ≈ syl s → Square G s o
square-merge G s o pr rel =
  square-by G s o (syl (actM G s)) ε (path-normal (actM G s) (ColOrth-actMʷ [ G ]ʷ o) pr) tt
    (trans rel (sym left-unit))

------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 4.4, Case 2: G = (-1)[j], at a state s of level L with pivot
-- p ≥ j (Subcase 2.1, j > p, raises the level).
--
-- * 2.2.1: the pivot column is a unit ±e_m.
--   - 2.2.1.1, −e_j: G is the syllable of s (prograde);
--   - 2.2.1.2, e_j: G is the syllable of G·s (retrograde);
--   - 2.2.1.3, −e_m with m ≠ j: (-1)[m] commutes with G (equation (4));
--   - 2.2.1.4, e_m with m, p ≠ j: X[m,p] commutes with G (6);
--   - 2.2.1.5, e_m with m ≠ j = p: (-1)[m] X[m,p] (-1)[p] = X[m,p] (10).
-- * 2.2.2: an exponent k > 0.  (-1)[j] keeps the parities and residues,
--   so s and G·s have the same syllable H[i₁,i₂].
--   - 2.2.2.1, j ∉ {i₁, i₂}: it commutes with G (5);
--   - 2.2.2.2, j = i₂: X[i₁,i₂] H (-1)[i₂] = H (18);
--   - 2.2.2.3, j = i₁: X[i₁,i₂] (-1)[i₂] (-1)[i₁] H (-1)[i₁] = H (26).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (Lvl)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction as TR

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case2 {n : ℕ} {L : Lvl} (ih : TR.EdgesBelow {n} L) where

open import Data.Fin.Base as Fin using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; Z ; module ZR ; oddᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (_!_ ; scV ; Minimal)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column using (firstOdd ; negᶻ ; firstOdd-char)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Zᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (pivot ; _<ₗ_ ; level)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable using (eᶻ ; eᶻ-! ; eδ-≢)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Levels using (Minimal-Z)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (sound-act ; _≤ₗ_)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} as R
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (ne-𝕀 ; ne-𝕀-at ; mono-word-below ; bℓ-below)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (Z-Z ; X-X ; H-H)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pairings {n} using (HZH)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Algorithm
  using (levelᶜ ; sylᶜ ; sylDataᶜ ; sylDataᶜ-neg ; sylDataᶜ-pos ; sylDataᶜ-pair ; third)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction {n}
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Squares {n}
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.State {n}

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid
open Close ih

private
  sym≢ : ∀ {A : Set} {x y : A} → x ≢ y → y ≢ x
  sym≢ ne e = ne (≡.sym e)

  <-≢ : ∀ {x y : Fin n} → x < y → x ≢ y
  <-≢ lt ≡.refl = FinP.<-irrefl ≡.refl lt

------------------------------------------------------------------------
-- The relations

module _ {a b : Fin n} (ab : a < b) where

  -- (10): (-1)[a] X[a,b] (-1)[b] = X[a,b].
  ZXZ : Zʷ a • X a b ab • Zʷ b ≈ X a b ab
  ZXZ = begin
    Zʷ a • X a b ab • Zʷ b       ≈⟨ sym assoc ⟩
    (Zʷ a • X a b ab) • Zʷ b     ≈⟨ cleft axiom (c1 ab) ⟩
    (X a b ab • Zʷ b) • Zʷ b     ≈⟨ assoc ⟩
    X a b ab • Zʷ b • Zʷ b       ≈⟨ cright Z-Z ⟩
    X a b ab • ε                 ≈⟨ right-unit ⟩
    X a b ab                     ∎

  -- H (-1)[b] = X H.
  HZ : H a b ab • Zʷ b ≈ X a b ab • H a b ab
  HZ = begin
    H a b ab • Zʷ b                              ≈⟨ sym right-unit ⟩
    (H a b ab • Zʷ b) • ε                        ≈⟨ cright sym (H-H ab) ⟩
    (H a b ab • Zʷ b) • H a b ab • H a b ab      ≈⟨ trans (sym assoc) (cleft trans assoc (HZH ab)) ⟩
    X a b ab • H a b ab                          ∎

  -- (18): X H (-1)[b] = H.
  XHZ : X a b ab • H a b ab • Zʷ b ≈ H a b ab
  XHZ = begin
    X a b ab • H a b ab • Zʷ b       ≈⟨ cright HZ ⟩
    X a b ab • X a b ab • H a b ab   ≈⟨ sym assoc ⟩
    (X a b ab • X a b ab) • H a b ab ≈⟨ cleft X-X ab ⟩
    ε • H a b ab                     ≈⟨ left-unit ⟩
    H a b ab                         ∎

  -- (26): X (-1)[b] (-1)[a] H (-1)[a] = H.
  XZZHZ : (X a b ab • Zʷ b • Zʷ a) • H a b ab • Zʷ a ≈ H a b ab
  XZZHZ = begin
    (X a b ab • Zʷ b • Zʷ a) • H a b ab • Zʷ a
      ≈⟨ cright HZa ⟩
    (X a b ab • Zʷ b • Zʷ a) • Zʷ a • Zʷ b • X a b ab • H a b ab
      ≈⟨ by-assoc ≡.refl ⟩
    X a b ab • Zʷ b • (Zʷ a • Zʷ a) • Zʷ b • X a b ab • H a b ab
      ≈⟨ cright cright cleft Z-Z ⟩
    X a b ab • Zʷ b • ε • Zʷ b • X a b ab • H a b ab
      ≈⟨ cright cright left-unit ⟩
    X a b ab • Zʷ b • Zʷ b • X a b ab • H a b ab
      ≈⟨ cright trans (sym assoc) (trans (cleft Z-Z) left-unit) ⟩
    X a b ab • X a b ab • H a b ab
      ≈⟨ trans (sym assoc) (trans (cleft X-X ab) left-unit) ⟩
    H a b ab ∎
    where
    -- H (-1)[a] = (-1)[a] (-1)[b] X H, by (d1) and (18).
    HZa : H a b ab • Zʷ a ≈ Zʷ a • Zʷ b • X a b ab • H a b ab
    HZa = begin
      H a b ab • Zʷ a                         ≈⟨ sym right-unit ⟩
      (H a b ab • Zʷ a) • ε                   ≈⟨ cright sym Z-Z ⟩
      (H a b ab • Zʷ a) • Zʷ b • Zʷ b         ≈⟨ trans (sym assoc) (cleft assoc) ⟩
      (H a b ab • Zʷ a • Zʷ b) • Zʷ b         ≈⟨ cleft sym (axiom (d1 ab)) ⟩
      (Zʷ a • Zʷ b • H a b ab) • Zʷ b         ≈⟨ trans assoc (cright assoc) ⟩
      Zʷ a • Zʷ b • H a b ab • Zʷ b           ≈⟨ cright cright HZ ⟩
      Zʷ a • Zʷ b • X a b ab • H a b ab       ∎

------------------------------------------------------------------------
-- The edge (-1)[j] out of s

module Edge (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (pv : pivot s ≡ just p) (eqL : levelᶜ s ≡ L)
            (j : Fin n) (j≤p : j ≤ p) (le : levelᶜ (actM (Z-gen j) s) ≤ₗ L) where

  open At s o pv
  open Act (Z-gen j) j≤p

  -- The normal steps out of s and r land below L.
  below-s : (h : Word (Gen n)) → sylᶜ s ≡ h → levelᶜ (actMʷ h s) <ₗ L
  below-s h e = ≡.subst (λ w → levelᶜ (actMʷ w s) <ₗ L) e (normal-below s o pv (inj₂ eqL))

  below-r : pivot r ≡ just p → (h : Word (Gen n)) → sylᶜ r ≡ h → levelᶜ (actMʷ h r) <ₗ L
  below-r pv′ h e = ≡.subst (λ w → levelᶜ (actMʷ w r) <ₗ L) e (normal-below r (ColOrth-actMʷ (Zʷ j) o) pv′ le)

  -- The end of a relation W • N′ • G ≈ N lies below L.
  end-below : ∀ {W N′ N} → W • N′ • Zʷ j ≈ N → sylᶜ s ≡ N → levelᶜ (actMʷ W (actMʷ N′ r)) <ₗ L
  end-below {W} {N′} {N} rel e = ≡.subst (λ M → levelᶜ M <ₗ L) (≡.sym (sound-act rel s)) (below-s N e)

  case2 : Path (Zʷ j) s o
  case2 = by view ≡.refl
    where
    by : ∀ {K} → View p K W → k ≡ K → Path (Zʷ j) s o

    -- −e_m
    by (neg m e rest) eK = dec-elim (m FinP.≟ j) same other
      where
      fo : firstOdd W ≡ just m
      fo = firstOdd-char W (≡.cong oddᶻ e) (λ x x<m → ≡.cong oddᶻ (rest x (<-≢ x<m)))
      sylN : sylᶜ s ≡ Zʷ m
      sylN = ≡.trans syl (≡.trans (≡.cong (λ K → sylDataᶜ p K W) eK) (sylDataᶜ-neg W fo (≡.cong negᶻ e)))
      colW₀ : col s p ≡ scV 0 W
      colW₀ = ≡.trans colW (≡.cong (λ K → scV K W) eK)
      -- 2.2.1.1
      same : m ≡ j → Path (Zʷ j) s o
      same m≡j = ≡.subst (λ x → Path (Zʷ x) s o) m≡j (prograde (Z-gen m) s o pv sylN)
      -- 2.2.1.3
      other : m ≢ j → Path (Zʷ j) s o
      other m≢j = commute (Z-gen j) (Z-gen m) ((m≢j ∷ []) ∷ []) s o
                    (prograde (Z-gen m) s o pv sylN)
                    (prograde (Z-gen m) r (ColOrth-actMʷ (Zʷ j) o) Rr.pv′ sylR)
                    (below-r Rr.pv′ (Zʷ m) sylR) (below-s (Zʷ m) sylN)
        where
        colr : col r p ≡ scV 0 W
        colr = ≡.trans (colZ j) (≡.trans (≡.cong (λ K → scV K (Zᶻ j W)) eK) (≡.cong (scV 0) (Zᶻ-0 j W (rest j (sym≢ m≢j)))))
        module Rr = Rep 0 W colr (inj₁ ≡.refl) (λ e′ → ne (≡.trans colW₀ (≡.trans (≡.sym colr) e′)))
        sylR : sylᶜ r ≡ Zʷ m
        sylR = ≡.trans Rr.syl′ (sylDataᶜ-neg W fo (≡.cong negᶻ e))

    -- e_m, m < p
    by (pos m m<p e rest) eK = dec-elim (m FinP.≟ j) same other
      where
      fo : firstOdd W ≡ just m
      fo = firstOdd-char W (≡.cong oddᶻ e) (λ x x<m → ≡.cong oddᶻ (rest x (<-≢ x<m)))
      sylN : sylᶜ s ≡ X m p m<p
      sylN = ≡.trans syl (≡.trans (≡.cong (λ K → sylDataᶜ p K W) eK) (sylDataᶜ-pos W fo (≡.cong negᶻ e) m<p))
      colW₀ : col s p ≡ scV 0 W
      colW₀ = ≡.trans colW (≡.cong (λ K → scV K W) eK)
      -- 2.2.1.2: −e_m at r.
      same : m ≡ j → Path (Zʷ j) s o
      same m≡j = ≡.subst (λ x → Path (Zʷ x) s o) m≡j (retrograde (Z-gen m) s o Rr.pv′ sylR)
        where
        W′ = Zᶻ m W
        colr : col (actM (Z-gen m) s) p ≡ scV 0 W′
        colr = ≡.trans (colZ m) (≡.cong (λ K → scV K W′) eK)
        W′m : W′ ! m ≡ ZR.- ZR.1#
        W′m = ≡.trans (set₁-a m (ZR.- (W ! m)) W) (≡.cong ZR.-_ e)
        m≢p : m ≢ p
        m≢p = <-≢ m<p
        ne′ : col (actM (Z-gen m) s) p ≢ col 𝕀 p
        ne′ = ne-𝕀-at (actM (Z-gen m) s) p 0 W′ colr (inj₁ ≡.refl) m
                (λ e′ → -1≢0 (≡.trans (≡.sym W′m) (≡.trans e′ (≡.trans (eᶻ-! p m) (eδ-≢ m≢p)))))
          where
          -1≢0 : ZR.- ZR.1# ≢ ZR.0#
          -1≢0 ()
        module Rr = At.Act.Rep s o pv (Z-gen m) (≡.subst (_≤ p) (≡.sym m≡j) j≤p) 0 W′ colr (inj₁ ≡.refl) ne′
        sylR : sylᶜ (actM (Z-gen m) s) ≡ Zʷ m
        sylR = ≡.trans Rr.syl′ (sylDataᶜ-neg W′ (≡.trans (firstOdd-Z m W) fo) (≡.cong negᶻ W′m))
      other : m ≢ j → Path (Zʷ j) s o
      other m≢j = dec-elim (j FinP.≟ p) at-p not-p
        where
        colr : col r p ≡ scV 0 W
        colr = ≡.trans (colZ j) (≡.trans (≡.cong (λ K → scV K (Zᶻ j W)) eK) (≡.cong (scV 0) (Zᶻ-0 j W (rest j (sym≢ m≢j)))))
        module Rr = Rep 0 W colr (inj₁ ≡.refl) (λ e′ → ne (≡.trans colW₀ (≡.trans (≡.sym colr) e′)))
        sylR : sylᶜ r ≡ X m p m<p
        sylR = ≡.trans Rr.syl′ (sylDataᶜ-pos W fo (≡.cong negᶻ e) m<p)
        pN = prograde (X-gen m p m<p) s o pv sylN
        pN′ = prograde (X-gen m p m<p) r (ColOrth-actMʷ (Zʷ j) o) Rr.pv′ sylR
        -- 2.2.1.4
        not-p : j ≢ p → Path (Zʷ j) s o
        not-p j≢p = commute (Z-gen j) (X-gen m p m<p) ((m≢j ∷ []) ∷ (sym≢ j≢p ∷ []) ∷ []) s o pN pN′
                      (below-r Rr.pv′ (X m p m<p) sylR) (below-s (X m p m<p) sylN)
        -- 2.2.1.5
        at-p : j ≡ p → Path (Zʷ j) s o
        at-p j≡p = close (Z-gen j) s o (X m p m<p) (X m p m<p) (Zʷ m) pN pN′
                     (below-r Rr.pv′ (X m p m<p) sylR , end-below rel sylN) rel
          where
          rel : Zʷ m • X m p m<p • Zʷ j ≈ X m p m<p
          rel = ≡.subst (λ x → Zʷ m • X m p m<p • Zʷ x ≈ X m p m<p) (≡.sym j≡p) (ZXZ m<p)

    -- k = k′ + 1: the syllable H[i₁,i₂] of s and of r
    by {suc k′} (pair i₁ i₂ fo nx i₁<i₂ i₂≤p) eK = dec-elim (j FinP.≟ i₁) at-i₁ λ j≢i₁ → dec-elim (j FinP.≟ i₂) at-i₂ (apart j≢i₁)
      where
      Hp = H i₁ i₂ i₁<i₂
      sylN : sylᶜ s ≡ Hp
      sylN = ≡.trans syl (≡.trans (≡.cong (λ K → sylDataᶜ p K W) eK) (sylDataᶜ-pair {p = p} k′ W fo nx i₁<i₂))
      W′ = Zᶻ j W
      colr : col r p ≡ scV (suc k′) W′
      colr = ≡.trans (colZ j) (≡.cong (λ K → scV K W′) eK)
      min′ : Minimal (suc k′) W′
      min′ = Minimal-Z j W (≡.subst (λ K → Minimal K W) eK min)
      module Rr = Rep (suc k′) W′ colr min′ (ne-𝕀 r p k′ W′ colr min′)
      sylR : sylᶜ r ≡ Hp
      sylR = ≡.trans Rr.syl′ (sylDataᶜ-pair {p = p} k′ W′ (≡.trans (firstOdd-Z j W) fo) (≡.trans (nextSame-Z j i₁ W) nx) i₁<i₂)
      pN = prograde (H-gen i₁ i₂ i₁<i₂) s o pv sylN
      pN′ = prograde (H-gen i₁ i₂ i₁<i₂) r (ColOrth-actMʷ (Zʷ j) o) Rr.pv′ sylR
      lR : levelᶜ (actMʷ Hp r) <ₗ L
      lR = below-r Rr.pv′ Hp sylR
      -- L, with its exponent.
      L≡ : L ≡ (suc (toℕ p) , suc k′ , third (suc k′) W)
      L≡ = ≡.trans (≡.sym eqL) (≡.trans lvl (≡.cong (λ K → suc (toℕ p) , K , third K W) eK))
      -- 2.2.2.1
      apart : j ≢ i₁ → j ≢ i₂ → Path (Zʷ j) s o
      apart j≢i₁ j≢i₂ = commute (Z-gen j) (H-gen i₁ i₂ i₁<i₂) ((sym≢ j≢i₁ ∷ []) ∷ (sym≢ j≢i₂ ∷ []) ∷ []) s o pN pN′
                          lR (below-s Hp sylN)
      -- 2.2.2.2
      at-i₂ : j ≡ i₂ → Path (Zʷ j) s o
      at-i₂ j≡i₂ = close (Z-gen j) s o Hp Hp (X i₁ i₂ i₁<i₂) pN pN′ (lR , end-below rel sylN) rel
        where
        rel : X i₁ i₂ i₁<i₂ • Hp • Zʷ j ≈ Hp
        rel = ≡.subst (λ x → X i₁ i₂ i₁<i₂ • Hp • Zʷ x ≈ Hp) (≡.sym j≡i₂) (XHZ i₁<i₂)
      -- 2.2.2.3: the word X (-1)[i₂] (-1)[i₁] stays below L.
      at-i₁ : j ≡ i₁ → Path (Zʷ j) s o
      at-i₁ j≡i₁ = close (Z-gen j) s o Hp Hp Wd pN pN′ low rel
        where
        Wd = X i₁ i₂ i₁<i₂ • Zʷ i₂ • Zʷ i₁
        rel : Wd • Hp • Zʷ j ≈ Hp
        rel = ≡.subst (λ x → Wd • Hp • Zʷ x ≈ Hp) (≡.sym j≡i₁) (XZZHZ i₁<i₂)
        L′ = suc (toℕ p) , suc k′ , third (suc k′) W
        low′ : R.Low L′ Wd (actMʷ Hp r)
        low′ = mono-word-below Wd (i₂≤p , i₂≤p , ℕP.<⇒≤ (ℕP.<-≤-trans i₁<i₂ i₂≤p)) (actMʷ Hp r)
                 (Pos.conv> (actMʷ Hp r) (≡.subst (levelᶜ (actMʷ Hp r) <ₗ_) L≡ lR))
                 (bℓ-below (third (suc k′) W) (s≤s z≤n) FinP.≤-refl)
        low : Low L Wd (actMʷ Hp r)
        low = ≡.subst (λ L″ → Low L″ Wd (actMʷ Hp r)) (≡.sym L≡) (Pos.low-conv Wd (actMʷ Hp r) low′)

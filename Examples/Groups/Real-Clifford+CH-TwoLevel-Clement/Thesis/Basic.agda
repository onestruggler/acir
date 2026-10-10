------------------------------------------------------------------------
-- Presentations of groups
--
-- Basic generators (Definition 4.3) and the others through them
-- (Corollary 1.8).
--
-- The basic generators are (-1)[j], X[j,j+1] and H[0,1].  Clément
-- proves Lemma 4.4 for basic edges only and does not spell out how
-- this gives every edge.  Here: conjugation by X[x,y] with x, y ≤ p
-- permutes the rows ≤ p, which keeps a state at or below a level
-- L = (p + 1, k, ℓ) at or below it (perm): the pivot column keeps its
-- exponent and counts, or e_p becomes a unit e_m of level (p + 1, 0, 0).
-- So, given the basic edges out of the states at L that do not go up
-- (BasicAt) and the edges below L, every edge whose ends lie at or
-- below L is a path: X[a,c] = X[c-1,c] X[a,c-1] X[c-1,c] (c3) by
-- induction, and H[a,b] = X[0,a] X[1,b] H[0,1] X[1,b] X[0,a] ((c4),
-- (c5)), the states along these words being permutations of the ends.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Basic {n : ℕ} where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (_×-dec_ ; recompute)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count ; count-cong ; count-drop ; count-false ; dec-elim)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; Z)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (_!_ ; lde ; num ; lde-char)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column using (nodd ; negᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Xᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot
  using (pivot ; pivot-just ; pivot-nothing ; pivot-char ; Beyond ; _≟ᵛ_ ; Lvl ; _<ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable using (top ; eᶻ ; eᶻ-! ; eδ-refl ; eδ-≢ ; col𝕀≡ ; actV-e-beyond)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Levels using (lde-X ; nodd-X)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (sound-act ; act-gg ; _≤ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (conj-X ; conj-X′ ; X-X)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Algorithm
  using (nneg ; third ; lvlAtᶜ ; levelᶜ ; levelᶜ-just)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction {n}
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Equations {n} using (XHbcX ; XHacX ; XHabX)

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  <-≢ : ∀ {x y : Fin n} → x < y → x ≢ y
  <-≢ lt ≡.refl = FinP.<-irrefl ≡.refl lt

  rc : ∀ {a b : Fin n} → .(a < b) → a < b
  rc {a} {b} lt = recompute (a FinP.<? b) lt

------------------------------------------------------------------------
-- Basic generators

Basic : Gen n → Set
Basic (Z-gen _)     = ⊤
Basic (X-gen a b _) = toℕ b ≡ suc (toℕ a)
Basic (H-gen a b _) = toℕ a ≡ 0 × toℕ b ≡ 1

basic? : (g : Gen n) → Dec (Basic g)
basic? (Z-gen _)     = yes tt
basic? (X-gen a b _) = toℕ b ℕP.≟ suc (toℕ a)
basic? (H-gen a b _) = (toℕ a ℕP.≟ 0) ×-dec (toℕ b ℕP.≟ 1)

------------------------------------------------------------------------
-- X keeps the counts of a numerator

count-X : (f : Z → Bool) (a b : Fin n) → a ≢ b → (w : Vec Z n) →
          count (λ x → f (Xᶻ a b w ! x)) ≡ count (λ x → f (w ! x))
count-X f a b a≢b w = by (f (w ! a)) (f (w ! b)) ≡.refl ≡.refl
  where
  P Q : Fin n → Bool
  P x = f (w ! x)
  Q x = f (Xᶻ a b w ! x)
  Qa : Q a ≡ P b
  Qa = ≡.cong f (set₂-a a b (w ! b) (w ! a) w)
  Qb : Q b ≡ P a
  Qb = ≡.cong f (set₂-b a b (w ! b) (w ! a) w a≢b)
  Q≢ : ∀ x → x ≢ a → x ≢ b → Q x ≡ P x
  Q≢ x xa xb = ≡.cong f (set₂-≢ a b (w ! b) (w ! a) w xa xb)
  Both : Fin n → Bool
  Both x = P x ∧ Q x
  ∧-idem : ∀ c → c ∧ c ≡ c
  ∧-idem true = ≡.refl
  ∧-idem false = ≡.refl
  same : ∀ {pa pb} → P a ≡ pa → P b ≡ pb → pa ≡ pb → ∀ x → Dec (x ≡ a) → Dec (x ≡ b) → Q x ≡ P x
  same ea eb e x (yes ≡.refl) _ = ≡.trans Qa (≡.trans eb (≡.trans (≡.sym e) (≡.sym ea)))
  same ea eb e x (no xa) (yes ≡.refl) = ≡.trans Qb (≡.trans ea (≡.trans e (≡.sym eb)))
  same ea eb e x (no xa) (no xb) = Q≢ x xa xb
  by : (pa pb : Bool) → P a ≡ pa → P b ≡ pb → count Q ≡ count P
  by true true ea eb = count-cong Q P (λ x → same ea eb ≡.refl x (x FinP.≟ a) (x FinP.≟ b))
  by false false ea eb = count-cong Q P (λ x → same ea eb ≡.refl x (x FinP.≟ a) (x FinP.≟ b))
  by true false ea eb =
    ≡.trans (count-drop Q Both b (≡.trans Qb ea) (≡.cong (_∧ Q b) eb) (λ x xb → ≡.sym (atQ x xb (x FinP.≟ a))))
            (≡.sym (count-drop P Both a ea (≡.trans (≡.cong (_∧ Q a) ea) (≡.trans Qa eb)) (λ x xa → ≡.sym (atP x xa (x FinP.≟ b)))))
    where
    atP : ∀ x → x ≢ a → Dec (x ≡ b) → Both x ≡ P x
    atP x xa (yes ≡.refl) = ≡.trans (≡.cong (_∧ Q x) eb) (≡.sym eb)
    atP x xa (no xb) = ≡.trans (≡.cong (P x ∧_) (Q≢ x xa xb)) (∧-idem (P x))
    atQ : ∀ x → x ≢ b → Dec (x ≡ a) → Both x ≡ Q x
    atQ x xb (yes ≡.refl) = ≡.cong (λ c → c ∧ Q x) ea
    atQ x xb (no xa) = ≡.trans (≡.cong (_∧ Q x) (≡.sym (Q≢ x xa xb))) (∧-idem (Q x))
  by false true ea eb =
    ≡.trans (count-drop Q Both a (≡.trans Qa eb) (≡.cong (_∧ Q a) ea) (λ x xa → ≡.sym (atQ x xa (x FinP.≟ b))))
            (≡.sym (count-drop P Both b eb (≡.trans (≡.cong (_∧ Q b) eb) (≡.trans Qb ea)) (λ x xb → ≡.sym (atP x xb (x FinP.≟ a)))))
    where
    atP : ∀ x → x ≢ b → Dec (x ≡ a) → Both x ≡ P x
    atP x xb (yes ≡.refl) = ≡.trans (≡.cong (_∧ Q x) ea) (≡.sym ea)
    atP x xb (no xa) = ≡.trans (≡.cong (P x ∧_) (Q≢ x xa xb)) (∧-idem (P x))
    atQ : ∀ x → x ≢ a → Dec (x ≡ b) → Both x ≡ Q x
    atQ x xa (yes ≡.refl) = ≡.cong (λ c → c ∧ Q x) eb
    atQ x xa (no xb) = ≡.trans (≡.cong (_∧ Q x) (≡.sym (Q≢ x xa xb))) (∧-idem (Q x))

-- So X keeps the third component of a level.
third-X : (a b : Fin n) → a ≢ b → ∀ K (w : Vec Z n) → third K (Xᶻ a b w) ≡ third K w
third-X a b a≢b zero w = count-X negᶻ a b a≢b w
third-X a b a≢b (suc K) w = nodd-X a b a≢b w

------------------------------------------------------------------------
-- Permutations keep a state at or below a level

module Le (p : Fin n) (k ℓ : ℕ) where

  L : Lvl
  L = suc (toℕ p) , k , ℓ

  -- At or below L, a state agrees with I beyond p.
  beyond : (N : Matrix n n D) → levelᶜ N ≤ₗ L → Beyond p N
  beyond N le = by (pivot N) ≡.refl
    where
    by : (r : Maybe (Fin n)) → pivot N ≡ r → Beyond p N
    by nothing e x _ = ≡.cong (λ M → col M x) (pivot-nothing N e)
    by (just q) e x p<x = proj₂ (pivot-just N e) x (ℕP.≤-<-trans (q≤p le) p<x)
      where
      q≤p : levelᶜ N ≤ₗ L → q ≤ p
      q≤p (inj₁ (inj₁ lt)) = ℕP.<⇒≤ (ℕP.≤-pred (≡.subst (ℕ._< suc (toℕ p)) (≡.cong proj₁ (levelᶜ-just N e)) lt))
      q≤p (inj₁ (inj₂ (eq , _))) = ℕP.≤-reflexive (ℕP.suc-injective (≡.trans (≡.sym (≡.cong proj₁ (levelᶜ-just N e))) eq))
      q≤p (inj₂ eq) = ℕP.≤-reflexive (ℕP.suc-injective (≡.trans (≡.sym (≡.cong proj₁ (levelᶜ-just N e))) (≡.cong proj₁ eq)))

  -- (p + 1, 0, 0) lies at or below L.
  unit-le : (suc (toℕ p) , 0 , 0) ≤ₗ L
  unit-le = by k ℓ ≡.refl ≡.refl
    where
    by : ∀ k′ ℓ′ → k ≡ k′ → ℓ ≡ ℓ′ → (suc (toℕ p) , 0 , 0) ≤ₗ L
    by zero zero ≡.refl ≡.refl = inj₂ ≡.refl
    by zero (suc ℓ′) ≡.refl ≡.refl = inj₁ (inj₂ (≡.refl , inj₂ (≡.refl , s≤s z≤n)))
    by (suc k′) _ ≡.refl _ = inj₁ (inj₂ (≡.refl , inj₁ (s≤s z≤n)))

  perm : (a b : Fin n) .(ab : a < b) → b ≤ p → (N : Matrix n n D) → levelᶜ N ≤ₗ L →
         levelᶜ (actM (X-gen a b ab) N) ≤ₗ L
  perm a b ab b≤p N le = go (pivot XN) ≡.refl
    where
    g = X-gen a b ab
    XN = actM g N
    be = beyond N le
    a≢b = <⇒≢ ab
    go : (r : Maybe (Fin n)) → pivot XN ≡ r → levelᶜ XN ≤ₗ L
    go nothing e = inj₁ (≡.subst (_<ₗ L) (≡.sym (≡.cong (λ x → lvlAtᶜ x XN) e))
                          (inj₁ (s≤s z≤n)))
    go (just q) e = cmp (FinP.<-cmp q p)
      where
      lvlq = levelᶜ-just XN e
      cmp : Tri (q < p) (q ≡ p) (p < q) → levelᶜ XN ≤ₗ L
      cmp (tri< q<p _ _) = inj₁ (≡.subst (_<ₗ L) (≡.sym lvlq) (inj₁ (s≤s q<p)))
      cmp (tri> _ _ p<q) =
        ⊥-elim (proj₁ (pivot-just XN e) (≡.trans (col-actM g N q) (≡.trans (≡.cong (actV g) (be q p<q)) (actV-e-beyond g b≤p p<q))))
      cmp (tri≈ _ q≡p _) = at (col N p ≟ᵛ col 𝕀 p)
        where
        e′ : pivot XN ≡ just p
        e′ = ≡.trans e (≡.cong just q≡p)
        v = col N p
        Xv : col XN p ≡ actV g v
        Xv = col-actM g N p
        at : Dec (col N p ≡ col 𝕀 p) → levelᶜ XN ≤ₗ L
        -- e_p becomes a unit of level (p + 1, 0, 0).
        at (yes v≡e) = ≡.subst (_≤ₗ L) (≡.sym lvl) unit-le
          where
          e₀ = lde-char 0 (eᶻ p) (col𝕀≡ p) (inj₁ ≡.refl)
          ld : lde (col XN p) ≡ 0
          ld = ≡.trans (≡.cong lde (≡.trans Xv (≡.cong (actV g) v≡e))) (≡.trans (proj₁ (lde-X a b ab (col 𝕀 p))) (proj₁ e₀))
          nm : num (col XN p) ≡ Xᶻ a b (eᶻ p)
          nm = ≡.trans (≡.cong num (≡.trans Xv (≡.cong (actV g) v≡e))) (≡.trans (proj₂ (lde-X a b ab (col 𝕀 p))) (≡.cong (Xᶻ a b) (proj₂ e₀)))
          ng : third 0 (Xᶻ a b (eᶻ p)) ≡ 0
          ng = ≡.trans (count-X negᶻ a b a≢b (eᶻ p)) nneg-e
            where
            nneg-e : nneg (eᶻ p) ≡ 0
            nneg-e = count-false _ λ x → dec-elim (x FinP.≟ p)
              (λ { ≡.refl → ≡.cong negᶻ (≡.trans (eᶻ-! x x) (eδ-refl x)) })
              (λ x≢p → ≡.cong negᶻ (≡.trans (eᶻ-! p x) (eδ-≢ x≢p)))
          lvl : levelᶜ XN ≡ (suc (toℕ p) , 0 , 0)
          lvl = ≡.trans (levelᶜ-just XN e′)
                  (≡.trans (≡.cong₂ (λ K w → suc (toℕ p) , K , third K w) ld nm) (≡.cong (λ c → suc (toℕ p) , 0 , c) ng))
        -- Otherwise N has pivot p, and X keeps the level.
        at (no v≢e) = ≡.subst (_≤ₗ L) (≡.sym same) le
          where
          pvN : pivot N ≡ just p
          pvN = pivot-char N v≢e be
          ld = lde-X a b ab v
          same : levelᶜ XN ≡ levelᶜ N
          same = ≡.trans (levelᶜ-just XN e′)
                   (≡.trans (≡.cong₂ (λ K w → suc (toℕ p) , K , third K w)
                              (≡.trans (≡.cong lde Xv) (proj₁ ld)) (≡.trans (≡.cong num Xv) (proj₂ ld)))
                     (≡.trans (≡.cong (λ c → suc (toℕ p) , lde v , c) (third-X a b a≢b (lde v) (num v)))
                       (≡.sym (levelᶜ-just N pvN))))

------------------------------------------------------------------------
-- Every edge from the basic ones

-- The basic edges out of the states at L that do not go up, and are Ok.
BasicAtOk : Lvl → (Gen n → Matrix n n D → Set) → Set
BasicAtOk L Ok = ∀ (g : Gen n) → Basic g → ∀ M .(o : ColOrth M) → levelᶜ M ≡ L → levelᶜ (actM g M) ≤ₗ L →
                 Ok g M → Path [ g ]ʷ M o

BasicAt : Lvl → Set
BasicAt L = ∀ (g : Gen n) → Basic g → ∀ M .(o : ColOrth M) → levelᶜ M ≡ L → levelᶜ (actM g M) ≤ₗ L →
            Path [ g ]ʷ M o

-- Ok is a property of edges that every X has, and that conjugation
-- carries from H[b,c] to H[a,c] (by X[a,b]) and from H[a,c] to H[a,b]
-- (by X[b,c]), and from an edge going up to L to the edge back.  (All
-- edges, or those that are not hard.)
module ConjOk (p : Fin n) (k ℓ : ℕ) (ih : EdgesBelow (suc (toℕ p) , k , ℓ))
  (Ok : Gen n → Matrix n n D → Set)
  (ok-X : ∀ a b .(ab : a < b) M → Ok (X-gen a b ab) M)
  (ok-c4 : ∀ {a b c} .(ab : a < b) .(bc : b < c) .(ac : a < c) M → Ok (H-gen b c bc) M → Ok (H-gen a c ac) (actM (X-gen a b ab) M))
  (ok-c5 : ∀ {a b c} .(ab : a < b) .(bc : b < c) .(ac : a < c) M → Ok (H-gen a c ac) M → Ok (H-gen a b ab) (actM (X-gen b c bc) M))
  (ok-back : ∀ g M .(o : ColOrth M) → levelᶜ M <ₗ (suc (toℕ p) , k , ℓ) → levelᶜ (actM g M) ≡ (suc (toℕ p) , k , ℓ) →
             Ok g M → Ok g (actM g M))
  (basicAt : BasicAtOk (suc (toℕ p) , k , ℓ) Ok) where

  open Le p k ℓ

  -- Basic edges with both ends at or below L.
  basicLE : (g : Gen n) → Basic g → ∀ M .(o : ColOrth M) → levelᶜ M ≤ₗ L → levelᶜ (actM g M) ≤ₗ L → Ok g M → Path [ g ]ʷ M o
  basicLE g bg M o (inj₂ eM) le ok = basicAt g bg M o eM le ok
  basicLE g bg M o (inj₁ lM) (inj₁ lG) ok = ih g M o lM lG
  basicLE g bg M o (inj₁ lM) (inj₂ eG) ok =
    back g M o (basicAt g bg (actM g M) (ColOrth-actMʷ [ g ]ʷ o) eG
                  (inj₁ (≡.subst (_<ₗ L) (≡.sym (≡.cong levelᶜ (act-gg g M))) lM)) (ok-back g M o lM eG ok))

  -- The level after u, from a relation u ≈ v.
  level-via : ∀ {u v} → u ≈ v → (M : Matrix n n D) → levelᶜ (actMʷ v M) ≤ₗ L → levelᶜ (actMʷ u M) ≤ₗ L
  level-via e M le = ≡.subst (λ N → levelᶜ N ≤ₗ L) (≡.sym (sound-act e M)) le

  -- X[a,c], with c = a + gap + 1.
  xLE : ∀ gap (a c : Fin n) (ac : a < c) → toℕ c ≡ suc (gap ℕ.+ toℕ a) → c ≤ p →
        ∀ M .(o : ColOrth M) → levelᶜ M ≤ₗ L → levelᶜ (actM (X-gen a c ac) M) ≤ₗ L → Path (X a c ac) M o
  xLE zero a c ac eq c≤p M o lM lX = basicLE (X-gen a c ac) eq M o lM lX (ok-X a c ac M)
  xLE (suc g) a c ac eq c≤p M o lM lX = path-cong (sym rel) M o pw
    where
    m = suc (g ℕ.+ toℕ a)
    m<c : m ℕ.< toℕ c
    m<c = ≡.subst (m ℕ.<_) (≡.sym eq) (ℕP.n<1+n m)
    b : Fin n
    b = Fin.fromℕ< (ℕP.<-trans m<c (FinP.toℕ<n c))
    tb : toℕ b ≡ m
    tb = FinP.toℕ-fromℕ< _
    ab : a < b
    ab = ≡.subst (toℕ a ℕ.<_) (≡.sym tb) (s≤s (ℕP.m≤n+m (toℕ a) g))
    bc : b < c
    bc = ≡.subst (ℕ._< toℕ c) (≡.sym tb) m<c
    adj : toℕ c ≡ suc (toℕ b)
    adj = ≡.trans eq (≡.cong suc (≡.sym tb))
    b≤p : b ≤ p
    b≤p = ℕP.<⇒≤ (ℕP.<-≤-trans bc c≤p)
    -- (c3): X[a,c] = X[b,c] X[a,b] X[b,c].
    rel : X a c ac ≈ X b c bc • X a b ab • X b c bc
    rel = conj-X′ bc (axiom (c3 ab bc))
    rel₂ : X a b ab • X b c bc ≈ X b c bc • X a c ac
    rel₂ = sym (begin
      X b c bc • X a c ac                          ≈⟨ cright rel ⟩
      X b c bc • X b c bc • X a b ab • X b c bc    ≈⟨ sym assoc ⟩
      (X b c bc • X b c bc) • X a b ab • X b c bc  ≈⟨ cleft X-X bc ⟩
      ε • X a b ab • X b c bc                      ≈⟨ left-unit ⟩
      X a b ab • X b c bc                          ∎)
    M₁ = actM (X-gen b c bc) M
    l₁ : levelᶜ M₁ ≤ₗ L
    l₁ = perm b c bc c≤p M lM
    l₂ : levelᶜ (actM (X-gen a b ab) M₁) ≤ₗ L
    l₂ = level-via rel₂ M (perm b c bc c≤p (actM (X-gen a c ac) M) lX)
    l₃ : levelᶜ (actM (X-gen b c bc) (actM (X-gen a b ab) M₁)) ≤ₗ L
    l₃ = level-via (sym rel) M lX
    pw : Path (X b c bc • X a b ab • X b c bc) M o
    pw = path-• (X b c bc) (X a b ab • X b c bc) M o
           (basicLE (X-gen b c bc) adj (actM (X-gen a b ab) M₁) (ColOrth-actMʷ (X a b ab • X b c bc) o) l₂ l₃ (ok-X b c bc _))
           (path-• (X a b ab) (X b c bc) M o
             (xLE g a b ab tb b≤p M₁ (ColOrth-actMʷ (X b c bc) o) l₁ l₂)
             (basicLE (X-gen b c bc) adj M o lM l₁ (ok-X b c bc M)))

  -- Any X[a,c] with c ≤ p.
  xAny : (a c : Fin n) (ac : a < c) → c ≤ p →
         ∀ M .(o : ColOrth M) → levelᶜ M ≤ₗ L → levelᶜ (actM (X-gen a c ac) M) ≤ₗ L → Path (X a c ac) M o
  xAny a c ac = xLE (toℕ c ℕ.∸ suc (toℕ a)) a c ac eq
    where
    eq : toℕ c ≡ suc (toℕ c ℕ.∸ suc (toℕ a) ℕ.+ toℕ a)
    eq = ≡.trans (≡.sym (ℕP.m∸n+n≡m ac)) (ℕP.+-suc (toℕ c ℕ.∸ suc (toℕ a)) (toℕ a))

  -- The indices 0 and 1, when b ≥ 1 is an index.
  module Two {b : Fin n} (one≤b : 1 ℕ.≤ toℕ b) where

    z₀ z₁ : Fin n
    z₀ = Fin.fromℕ< (ℕP.≤-<-trans z≤n (ℕP.<-≤-trans (s≤s z≤n) (ℕP.≤-trans one≤b (ℕP.<⇒≤ (FinP.toℕ<n b)))))
    z₁ = Fin.fromℕ< (ℕP.≤-<-trans one≤b (FinP.toℕ<n b))

    t₀ : toℕ z₀ ≡ 0
    t₀ = FinP.toℕ-fromℕ< _

    t₁ : toℕ z₁ ≡ 1
    t₁ = FinP.toℕ-fromℕ< _

    z01 : z₀ < z₁
    z01 = ≡.subst₂ ℕ._<_ (≡.sym t₀) (≡.sym t₁) (s≤s z≤n)

  -- H[0,b] with b > 1: X[1,b] H[0,1] X[1,b], by (c5).
  h0LE : (a b : Fin n) (ab : a < b) → toℕ a ≡ 0 → 1 ℕ.< toℕ b → b ≤ p →
         ∀ M .(o : ColOrth M) → levelᶜ M ≤ₗ L → levelᶜ (actM (H-gen a b ab) M) ≤ₗ L → Ok (H-gen a b ab) M →
         Path (H a b ab) M o
  h0LE a b ab ta 1<b b≤p M o lM lH ok = path-cong (sym rel) M o pw
    where
    open Two {b} (ℕP.<⇒≤ 1<b)
    a≡z₀ : a ≡ z₀
    a≡z₀ = FinP.toℕ-injective (≡.trans ta (≡.sym t₀))
    1b : z₁ < b
    1b = ≡.subst (ℕ._< toℕ b) (≡.sym t₁) 1<b
    H01 = H z₀ z₁ z01
    X1b = X z₁ b 1b
    rel₀ : H z₀ b (FinP.<-trans z01 1b) ≈ X1b • H01 • X1b
    rel₀ = sym (XHabX z01 1b)
    rel : H a b ab ≈ X1b • H01 • X1b
    rel = ≡.subst (λ x → ∀ .(xb : x < b) → H x b xb ≈ X1b • H01 • X1b) (≡.sym a≡z₀) (λ _ → rel₀) ab
    M₁ = actM (X-gen z₁ b 1b) M
    l₁ : levelᶜ M₁ ≤ₗ L
    l₁ = perm z₁ b 1b b≤p M lM
    rel₂ : H01 • X1b ≈ X1b • H a b ab
    rel₂ = sym (begin
      X1b • H a b ab                  ≈⟨ cright rel ⟩
      X1b • X1b • H01 • X1b           ≈⟨ sym assoc ⟩
      (X1b • X1b) • H01 • X1b         ≈⟨ cleft X-X 1b ⟩
      ε • H01 • X1b                   ≈⟨ left-unit ⟩
      H01 • X1b                       ∎)
    l₂ : levelᶜ (actM (H-gen z₀ z₁ z01) M₁) ≤ₗ L
    l₂ = level-via rel₂ M (perm z₁ b 1b b≤p (actM (H-gen a b ab) M) lH)
    l₃ : levelᶜ (actM (X-gen z₁ b 1b) (actM (H-gen z₀ z₁ z01) M₁)) ≤ₗ L
    l₃ = level-via (sym rel) M lH
    ok₁ : Ok (H-gen z₀ z₁ z01) M₁
    ok₁ = ok-c5 z01 1b (FinP.<-trans z01 1b) M
            (≡.subst (λ x → ∀ .(xb : x < b) → Ok (H-gen x b xb) M) a≡z₀ (λ _ → ok) (FinP.<-trans z01 1b))
    pw : Path (X1b • H01 • X1b) M o
    pw = path-• X1b (H01 • X1b) M o
           (xAny z₁ b 1b b≤p (actM (H-gen z₀ z₁ z01) M₁) (ColOrth-actMʷ (H01 • X1b) o) l₂ l₃)
           (path-• H01 X1b M o (basicLE (H-gen z₀ z₁ z01) (t₀ , t₁) M₁ (ColOrth-actMʷ X1b o) l₁ l₂ ok₁)
             (xAny z₁ b 1b b≤p M o lM l₁))

  -- H[a,b], not H[0,1]: X[0,a] H[0,b] X[0,a] when a > 0, by (c4).
  hLE : (a b : Fin n) (ab : a < b) → ¬ (toℕ a ≡ 0 × toℕ b ≡ 1) → b ≤ p →
        ∀ M .(o : ColOrth M) → levelᶜ M ≤ₗ L → levelᶜ (actM (H-gen a b ab) M) ≤ₗ L → Ok (H-gen a b ab) M →
        Path (H a b ab) M o
  hLE a b ab nb b≤p M o lM lH ok = dec-elim (toℕ a ℕP.≟ 0) at0 pos
    where
    -- b > 1 unless (a, b) = (0, 1).
    1<b : toℕ a ≡ 0 → 1 ℕ.< toℕ b
    1<b ta = ℕP.≤∧≢⇒< (≡.subst (ℕ._< toℕ b) ta ab) (λ e → nb (ta , ≡.sym e))
    at0 : toℕ a ≡ 0 → Path (H a b ab) M o
    at0 ta = h0LE a b ab ta (1<b ta) b≤p M o lM lH ok
    pos : toℕ a ≢ 0 → Path (H a b ab) M o
    pos a≢0 = path-cong (sym rel) M o pw
      where
      0<a : 0 ℕ.< toℕ a
      0<a = ℕP.n≢0⇒n>0 a≢0
      1<b′ : 1 ℕ.< toℕ b
      1<b′ = ℕP.≤-<-trans 0<a ab
      open Two {b} (ℕP.<⇒≤ 1<b′)
      za : z₀ < a
      za = ≡.subst (ℕ._< toℕ a) (≡.sym t₀) 0<a
      zb : z₀ < b
      zb = FinP.<-trans za ab
      a≤p : a ≤ p
      a≤p = ℕP.<⇒≤ (ℕP.<-≤-trans ab b≤p)
      X0a = X z₀ a za
      H0b = H z₀ b zb
      rel : H a b ab ≈ X0a • H0b • X0a
      rel = sym (XHacX za ab)
      rel₂ : H0b • X0a ≈ X0a • H a b ab
      rel₂ = sym (begin
        X0a • H a b ab                  ≈⟨ cright rel ⟩
        X0a • X0a • H0b • X0a           ≈⟨ sym assoc ⟩
        (X0a • X0a) • H0b • X0a         ≈⟨ cleft X-X za ⟩
        ε • H0b • X0a                   ≈⟨ left-unit ⟩
        H0b • X0a                       ∎)
      M₁ = actM (X-gen z₀ a za) M
      l₁ : levelᶜ M₁ ≤ₗ L
      l₁ = perm z₀ a za a≤p M lM
      l₂ : levelᶜ (actM (H-gen z₀ b zb) M₁) ≤ₗ L
      l₂ = level-via rel₂ M (perm z₀ a za a≤p (actM (H-gen a b ab) M) lH)
      l₃ : levelᶜ (actM (X-gen z₀ a za) (actM (H-gen z₀ b zb) M₁)) ≤ₗ L
      l₃ = level-via (sym rel) M lH
      pw : Path (X0a • H0b • X0a) M o
      pw = path-• X0a (H0b • X0a) M o
             (xAny z₀ a za a≤p (actM (H-gen z₀ b zb) M₁) (ColOrth-actMʷ (H0b • X0a) o) l₂ l₃)
             (path-• H0b X0a M o (h0LE z₀ b zb t₀ 1<b′ b≤p M₁ (ColOrth-actMʷ X0a o) l₁ l₂ (ok-c4 za ab zb M ok))
               (xAny z₀ a za a≤p M o lM l₁))

  -- The generators that are not basic.
  other : (g : Gen n) → ¬ Basic g → top g ≤ p →
          ∀ M .(o : ColOrth M) → levelᶜ M ≤ₗ L → levelᶜ (actM g M) ≤ₗ L → Ok g M → Path [ g ]ʷ M o
  other (Z-gen a) nb _ = ⊥-elim (nb tt)
  other (X-gen a c ac) nb tg M o lM lG _ = xAny a c (rc ac) tg M o lM lG
  other (H-gen a b ab) nb tg M o lM lG ok = hLE a b (rc ab) nb tg M o lM lG ok

  -- Every Ok edge on indices ≤ p with both ends at or below L.
  edge-le : (g : Gen n) → top g ≤ p → ∀ M .(o : ColOrth M) → levelᶜ M ≤ₗ L → levelᶜ (actM g M) ≤ₗ L → Ok g M →
            Path [ g ]ʷ M o
  edge-le g tg M o lM lG ok = by (basic? g)
    where
    by : Dec (Basic g) → Path [ g ]ʷ M o
    by (yes bg) = basicLE g bg M o lM lG ok
    by (no nb) = other g nb tg M o lM lG ok

-- All edges are Ok.
module Conj (p : Fin n) (k ℓ : ℕ) (ih : EdgesBelow (suc (toℕ p) , k , ℓ)) (basicAt : BasicAt (suc (toℕ p) , k , ℓ)) where

  private
    module C = ConjOk p k ℓ ih (λ _ _ → ⊤) (λ _ _ _ _ → tt) (λ _ _ _ _ _ → tt) (λ _ _ _ _ _ → tt) (λ _ _ _ _ _ _ → tt)
                 (λ g bg M o e le _ → basicAt g bg M o e le)

  edge-le : (g : Gen n) → top g ≤ p → ∀ M .(o : ColOrth M) → levelᶜ M ≤ₗ (suc (toℕ p) , k , ℓ) →
            levelᶜ (actM g M) ≤ₗ (suc (toℕ p) , k , ℓ) → Path [ g ]ʷ M o
  edge-le g tg M o lM lG = C.edge-le g tg M o lM lG tt

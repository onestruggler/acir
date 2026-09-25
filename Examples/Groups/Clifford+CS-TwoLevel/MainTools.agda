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

open import Data.Nat.Base as ℕ using (ℕ ; suc ; s≤s ; z≤n)

module Examples.Groups.Clifford+CS-TwoLevel.MainTools {n : ℕ} where

open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
open import Data.List.Relation.Unary.All as All using (All ; [] ; _∷_)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Empty using (⊥-elim)
import Data.Bool.Properties as BoolP
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Data.Bool.Base using (false)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
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
open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (D ; Z ; oddᶻ)
open import Examples.Groups.Clifford+CS-TwoLevel.Lde
  using (scV ; lde ; num ; lde-char ; lde-≤ ; Minimal ; Odd ; Even ; ¬Even⇒Odd ; halveV ; scV-halve ; all-even?)
open import Examples.Groups.Clifford+CS-TwoLevel.Column using (sylData ; nodd ; Above)
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics
open import Examples.Groups.Clifford+CS-TwoLevel.Soundness using (sound-axiom)
open import Examples.Groups.Clifford+CS-TwoLevel.Pivot
  using (pivot ; pivot-just ; pivot-char ; Beyond ; Lvl ; lvlAt ; level ; level-just ; _<ₗ_ ; _<₂_ ; _<ₗ?_)
open import Examples.Groups.Clifford+CS-TwoLevel.Syllable
  using (syl ; syl-just ; step ; top ; Within ; Beyond-actM ; actV-e-beyond ; eᶻ ; col𝕀≡)
open import Examples.Groups.Clifford+CS-TwoLevel.Step using (step-lt)
open import Examples.Groups.Clifford+CS-TwoLevel.Synthesis using (synth-step)
open import Examples.Groups.Clifford+CS-TwoLevel.Derived {n} using (_⁻¹ ; inverseˡ ; idx ; Apartʷ ; Apartʷʷ ; comm-words)
open import Examples.Groups.Clifford+CS-TwoLevel.Levels using (Bℓ)
open import Examples.Groups.Clifford+CS-TwoLevel.Basic {n} using (Letters≤)
open import Examples.Groups.Clifford+CS-TwoLevel.ExpLevel {n} using (word-level)
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

-- Normal: N′ is the syllable of G s.
square-syl : (G : Gen n) (s : Matrix n n D) .(o : ColOrth s) {p′ : Fin n} (N′ G′ : Word (Gen n)) →
             pivot (actM G s) ≡ just p′ → syl (actM G s) ≡ N′ → Below (level s) G′ (step s) →
             N′ • [ G ]ʷ ≈ G′ • syl s → Square G s o
square-syl G s o N′ G′ pr eq below rel = square-by G s o N′ G′ normal below rel
  where
  normal : Path N′ (actM G s) (ColOrth-actMʷ [ G ]ʷ o)
  normal = ≡.subst (λ N → Path N (actM G s) (ColOrth-actMʷ [ G ]ʷ o)) eq
             (path-normal (actM G s) (ColOrth-actMʷ [ G ]ʷ o) pr)

------------------------------------------------------------------------
-- The syllable and the level, from a representation of the pivot
-- column

syl-of : (M : Matrix n n D) {p : Fin n} → pivot M ≡ just p → (K : ℕ) (W : Vec Z n) →
         col M p ≡ scV K W → Minimal K W → syl M ≡ sylData p K W
syl-of M {p} pv K W eq min =
  ≡.trans (syl-just M pv) (≡.cong₂ (sylData p) (proj₁ (lde-char K W eq min)) (proj₂ (lde-char K W eq min)))

level-of : (M : Matrix n n D) {p : Fin n} → pivot M ≡ just p → (K : ℕ) (W : Vec Z n) →
           col M p ≡ scV K W → Minimal K W → level M ≡ (suc (toℕ p) , K , nodd W)
level-of M {p} pv K W eq min =
  ≡.trans (level-just M pv)
    (≡.cong₂ (λ k w → suc (toℕ p) , k , nodd w) (proj₁ (lde-char K W eq min)) (proj₂ (lde-char K W eq min)))

------------------------------------------------------------------------
-- Paths of transpositions and i's, and apartness

-- Every state along w, the last included, stays below.
word-below-all : ∀ {b : Fin n} (w : Word (Gen n)) → Letters≤ b w → (M : Matrix n n D) {L : Lvl} →
                 level M <ₗ L → Bℓ b <ₗ L → Below L w M
word-below-all [ X-gen a c p ]ʷ h M lM lB = lM , word-level [ X-gen a c p ]ʷ h M lM lB
word-below-all [ i-gen c ]ʷ h M lM lB = lM , word-level [ i-gen c ]ʷ h M lM lB
word-below-all ε _ M lM lB = tt
word-below-all (u • v) (hu , hv) M lM lB =
  word-below-all v hv M lM lB , word-below-all u hu (actMʷ v M) (word-level v hv M lM lB) lB

-- A word acting on indices ≥ j is apart from i_[a] for a < j.
above-apart : ∀ {j a : Fin n} (u : Word (Gen n)) → Above j u → a < j → Apartʷ u (i-gen a)
above-apart [ X-gen b c p ]ʷ j≤b a<j =
  (≢ᵃ (ℕP.<-≤-trans a<j j≤b) ∷ []) ∷ (≢ᵃ (ℕP.<-trans (ℕP.<-≤-trans a<j j≤b) (recompute (b FinP.<? c) p)) ∷ []) ∷ []
  where
  ≢ᵃ : ∀ {x a : Fin n} → a < x → x ≢ a
  ≢ᵃ a<x x≡a = FinP.<-irrefl (≡.sym x≡a) a<x
above-apart [ K-gen b c p ]ʷ j≤b a<j =
  (≢ᵃ (ℕP.<-≤-trans a<j j≤b) ∷ []) ∷ (≢ᵃ (ℕP.<-trans (ℕP.<-≤-trans a<j j≤b) (recompute (b FinP.<? c) p)) ∷ []) ∷ []
  where
  ≢ᵃ : ∀ {x a : Fin n} → a < x → x ≢ a
  ≢ᵃ a<x x≡a = FinP.<-irrefl (≡.sym x≡a) a<x
above-apart [ i-gen b ]ʷ j≤b a<j = (≢ᵃ (ℕP.<-≤-trans a<j j≤b) ∷ []) ∷ []
  where
  ≢ᵃ : ∀ {x a : Fin n} → a < x → x ≢ a
  ≢ᵃ a<x x≡a = FinP.<-irrefl (≡.sym x≡a) a<x
above-apart ε _ _ = tt
above-apart (u • v) (hu , hv) a<j = above-apart u hu a<j , above-apart v hv a<j

-- A word acting on indices ≥ j is apart from a generator acting below j.
above-apart′ : ∀ {j : Fin n} (u : Word (Gen n)) → Above j u → (h : Gen n) → All (_< j) (idx h) → Apartʷ u h
above-apart′ [ X-gen b c p ]ʷ j≤b h hs =
  All.map (≢< j≤b) hs ∷ All.map (≢< (ℕP.≤-trans j≤b (ℕP.<⇒≤ (recompute (b FinP.<? c) p)))) hs ∷ []
  where
  ≢< : ∀ {j b : Fin n} → j ≤ b → ∀ {y} → y < j → b ≢ y
  ≢< j≤b y<j b≡y = FinP.<-irrefl (≡.sym b≡y) (ℕP.<-≤-trans y<j j≤b)
above-apart′ [ K-gen b c p ]ʷ j≤b h hs =
  All.map (≢< j≤b) hs ∷ All.map (≢< (ℕP.≤-trans j≤b (ℕP.<⇒≤ (recompute (b FinP.<? c) p)))) hs ∷ []
  where
  ≢< : ∀ {j b : Fin n} → j ≤ b → ∀ {y} → y < j → b ≢ y
  ≢< j≤b y<j b≡y = FinP.<-irrefl (≡.sym b≡y) (ℕP.<-≤-trans y<j j≤b)
above-apart′ [ i-gen b ]ʷ j≤b h hs = All.map (≢< j≤b) hs ∷ []
  where
  ≢< : ∀ {j b : Fin n} → j ≤ b → ∀ {y} → y < j → b ≢ y
  ≢< j≤b y<j b≡y = FinP.<-irrefl (≡.sym b≡y) (ℕP.<-≤-trans y<j j≤b)
above-apart′ ε _ _ _ = tt
above-apart′ (u • v) (hu , hv) h hs = above-apart′ u hu h hs , above-apart′ v hv h hs

-- A word acting on indices ≤ c is apart from a generator acting above c.
within-apart : ∀ {c : Fin n} (u : Word (Gen n)) → Within c u → (h : Gen n) → All (c <_) (idx h) → Apartʷ u h
within-apart [ X-gen a b q ]ʷ b≤c h hs =
  All.map (≢> (ℕP.≤-trans (ℕP.<⇒≤ (recompute (a FinP.<? b) q)) b≤c)) hs ∷ All.map (≢> b≤c) hs ∷ []
  where
  ≢> : ∀ {x c : Fin n} → x ≤ c → ∀ {y} → c < y → x ≢ y
  ≢> x≤c c<y x≡y = FinP.<-irrefl x≡y (ℕP.≤-<-trans x≤c c<y)
within-apart [ K-gen a b q ]ʷ b≤c h hs =
  All.map (≢> (ℕP.≤-trans (ℕP.<⇒≤ (recompute (a FinP.<? b) q)) b≤c)) hs ∷ All.map (≢> b≤c) hs ∷ []
  where
  ≢> : ∀ {x c : Fin n} → x ≤ c → ∀ {y} → c < y → x ≢ y
  ≢> x≤c c<y x≡y = FinP.<-irrefl x≡y (ℕP.≤-<-trans x≤c c<y)
within-apart [ i-gen a ]ʷ a≤c h hs = All.map (≢> a≤c) hs ∷ []
  where
  ≢> : ∀ {x c : Fin n} → x ≤ c → ∀ {y} → c < y → x ≢ y
  ≢> x≤c c<y x≡y = FinP.<-irrefl x≡y (ℕP.≤-<-trans x≤c c<y)
within-apart ε _ _ _ = tt
within-apart (u • v) (hu , hv) h hs = within-apart u hu h hs , within-apart v hv h hs

-- Powers of a word apart from h.
Apartʷ-^ : (w : Word (Gen n)) (h : Gen n) → Apartʷ w h → ∀ e → Apartʷ (w ^ e) h
Apartʷ-^ w h a ℕ.zero = tt
Apartʷ-^ w h a (suc ℕ.zero) = a
Apartʷ-^ w h a (suc (suc e)) = a , Apartʷ-^ w h a (suc e)

------------------------------------------------------------------------
-- Disjoint squares where G keeps the level, pivots and levels

-- Disjoint, where G keeps the level: G t is then the normal step from
-- G s, whose level is lower.
square-disjoint′ : (G : Gen n) (s : Matrix n n D) .(o : ColOrth s) {p p′ : Fin n} →
                   pivot s ≡ just p → pivot (actM G s) ≡ just p′ → syl (actM G s) ≡ syl s →
                   Apartʷʷ (syl s) [ G ]ʷ → level (actM G s) ≡ level s → Square G s o
square-disjoint′ G s o ps pr eq ap lv = square-disjoint G s o ps pr eq ap lq
  where
  r = actM G s
  Gt : actM G (step s) ≡ step r
  Gt = ≡.trans (≡.sym (sound-act (comm-words (syl s) [ G ]ʷ ap) s))
               (≡.cong (λ u → actMʷ u r) (≡.sym eq))
  lq : level (actM G (step s)) <ₗ level s
  lq = ≡.subst₂ _<ₗ_ (≡.sym (≡.cong level Gt)) lv (lt-step r (ColOrth-actMʷ [ G ]ʷ o) pr)

-- A generator acting on indices ≤ p keeps the pivot p if the pivot
-- column stays off I.
pivot-stay : (g : Gen n) {p : Fin n} (M : Matrix n n D) → top g ≤ p → pivot M ≡ just p →
             col (actM g M) p ≢ col 𝕀 p → pivot (actM g M) ≡ just p
pivot-stay g M tg pv ne = pivot-char (actM g M) ne (Beyond-actM g {M = M} tg (proj₂ (pivot-just M pv)))

-- A column with a positive exponent is not a column of I.
ne-𝕀 : (M : Matrix n n D) (c : Fin n) (k : ℕ) (W : Vec Z n) → col M c ≡ scV (suc k) W →
       Minimal (suc k) W → col M c ≢ col 𝕀 c
ne-𝕀 M c k W eq min e =
  ℕP.0≢1+n (≡.trans (≡.sym (proj₁ (lde-char 0 (eᶻ c) (col𝕀≡ c) (inj₁ ≡.refl))))
                    (proj₁ (lde-char (suc k) W (≡.trans (≡.sym e) eq) min)))

-- A column whose numerator differs from that of I at some entry is not
-- a column of I.
ne-𝕀-at : (M : Matrix n n D) (c : Fin n) (k : ℕ) (U : Vec Z n) → col M c ≡ scV k U → Minimal k U →
          (x : Fin n) → U ! x ≢ eᶻ c ! x → col M c ≢ col 𝕀 c
ne-𝕀-at M c k U eq min x ne e =
  ne (≡.cong (_! x) (≡.trans (≡.sym (proj₂ (lde-char k U (≡.trans (≡.sym e) eq) min)))
                             (proj₂ (lde-char 0 (eᶻ c) (col𝕀≡ c) (inj₁ ≡.refl)))))

-- (x + 1 , 0 , 1) lies below a level with pivot p ≥ x and a positive
-- exponent.
bℓ-below : ∀ {x p : Fin n} {k : ℕ} (m : ℕ) → 0 ℕ.< k → toℕ x ℕ.≤ toℕ p → Bℓ x <ₗ (suc (toℕ p) , k , m)
bℓ-below {x} {p} {k} m 0<k x≤p = aux (ℕP.m≤n⇒m<n∨m≡n x≤p)
  where
  aux : toℕ x ℕ.< toℕ p ⊎ toℕ x ≡ toℕ p → Bℓ x <ₗ (suc (toℕ p) , k , m)
  aux (inj₁ lt) = inj₁ (s≤s lt)
  aux (inj₂ eq) = inj₂ (≡.cong suc eq , inj₁ 0<k)

-- A matrix that agrees with I beyond p, and whose column p is w / γᵏ
-- with fewer than m odd entries in w, lies below (p + 1 , k , m).
level-le : (M : Matrix n n D) {p : Fin n} → Beyond p M → (k : ℕ) (N : Vec Z n) → col M p ≡ scV k N →
           ∀ {m} → nodd N ℕ.< m → level M <ₗ (suc (toℕ p) , k , m)
level-le M {p} be k N eq {m} lt = by-pivot (pivot M) ≡.refl
  where
  L : Lvl
  L = suc (toℕ p) , k , m

  exact : Minimal k N → (lde (col M p) , nodd (num (col M p))) <₂ (k , m)
  exact mn = inj₂ (proj₁ (lde-char k N eq mn) ,
                   ≡.subst (λ w → nodd w ℕ.< m) (≡.sym (proj₂ (lde-char k N eq mn))) lt)

  rep< : (lde (col M p) , nodd (num (col M p))) <₂ (k , m)
  rep< = by-even (all-even? N)
    where
    by-even : Dec (∀ x → Even (N ! x)) → (lde (col M p) , nodd (num (col M p))) <₂ (k , m)
    by-even (no ¬ev) = exact (inj₂ (odd (FinP.¬∀⇒∃¬ n (λ x → Even (N ! x)) (λ x → oddᶻ (N ! x) BoolP.≟ false) ¬ev)))
      where
      odd : (∃ λ x → ¬ Even (N ! x)) → ∃ λ x → Odd (N ! x)
      odd (x , ¬e) = x , ¬Even⇒Odd {N ! x} ¬e
    by-even (yes ev) = halve k ≡.refl
      where
      halve : ∀ k′ → k′ ≡ k → (lde (col M p) , nodd (num (col M p))) <₂ (k , m)
      halve ℕ.zero e = exact (inj₁ (≡.sym e))
      halve (suc k′) e =
        inj₁ (≡.subst (λ x → lde (col M p) ℕ.< x) e
               (s≤s (lde-≤ k′ (halveV N ev) (≡.trans eq (≡.trans (≡.cong (λ x → scV x N) (≡.sym e)) (scV-halve k′ N ev))))))

  by-pivot : (r : Maybe (Fin n)) → pivot M ≡ r → level M <ₗ L
  by-pivot nothing pv = ≡.subst (_<ₗ L) (≡.sym (≡.cong (λ x → lvlAt x M) pv)) (inj₁ (s≤s z≤n))
  by-pivot (just p′) pv = by-cmp (FinP.<-cmp p′ p)
    where
    by-cmp : Tri (p′ < p) (p′ ≡ p) (p < p′) → level M <ₗ L
    by-cmp (tri< p′<p _ _) = ≡.subst (_<ₗ L) (≡.sym (level-just M pv)) (inj₁ (s≤s p′<p))
    by-cmp (tri≈ _ p′≡p _) =
      ≡.subst (_<ₗ L) (≡.sym (level-just M (≡.trans pv (≡.cong just p′≡p)))) (inj₂ (≡.refl , rep<))
    by-cmp (tri> _ _ p<p′) = ⊥-elim (proj₁ (pivot-just M pv) (be p′ p<p′))

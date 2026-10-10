------------------------------------------------------------------------
-- Presentations of groups
--
-- The plain edges at a level L = (p + 1, k, ℓ), k > 0, in Clément's
-- framework: those out of a state at L that do not go up and are not
-- hard (H on two odd entries of different classes).
--
-- The basic ones are Cases 1, 2 and 3.1–3.3 of Lemma 4.4 (a hard H[0,1]
-- is excluded); the others are conjugates of basic ones (Basic.ConjOk),
-- which conjugation keeps plain: X moves the two entries H acts on.  An
-- H edge into L from below is not hard at its end at L either, since a
-- hard H keeps the level (hard-level).  These are the edges that the
-- proof of the hard edge (Route, Sound, Hard) needs, over Clément's
-- normal words (Framework).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Product.Base using (_,_)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction as TR
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case1 as Case1

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Plain {n : ℕ} (p : Fin n) (k′ ℓ : ℕ)
  (ih : TR.EdgesBelow {n} (suc (toℕ p) , suc k′ , ℓ)) (h1142 : Case1.Hyp1142 ih) where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (_<_ ; _≤_)
import Data.Fin.Properties as FinP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (¬_)

open import Quantum.Synthesis.Matrix using (Matrix)
open import Quantum.Synthesis.Ring using (RootTwo)

open import Word.Base
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim ; count-cong)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (D ; Z ; module ZR ; oddᶻ ; rbit ; √2ᶻ ; √2*≡ ; oddᶻ-+ ; oddᶻ-neg ; rbit-+ ; rbit-neg ; even⇒δ∣)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (_!_ ; scV ; Odd ; Even ; lde ; num ; lde-eq)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column using (nodd)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Xᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics hiding (_!_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (pivot ; pivot-just ; pivot-char ; level ; Lvl ; _<ₗ_ ; <ₗ-irrefl)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable using (top ; Beyond-actM)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Levels using (lde-X)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Local {n} using (actV-H-same)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Step using (odd⇒≤)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (_≤ₗ_ ; act-gg)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (ne-𝕀)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Algorithm using (synthᶜ ; levelᶜ ; levelᶜ-just ; lvlAtᶜ ; third)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Reduction {n} using (Path)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.State {n} using (module Pos ; module At ; levelᶜ-of)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Basic {n} using (Basic ; BasicAtOk ; module ConjOk)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Above {n} using (above)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case2 as Case2
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Case3 as Case3
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Framework as F

private
  t≢f : true ≢ false
  t≢f ()

  xor-≢ : ∀ {a b} → a ≢ b → a xor b ≡ true
  xor-≢ {true} {true} ne = ⊥-elim (ne ≡.refl)
  xor-≢ {true} {false} _ = ≡.refl
  xor-≢ {false} {true} _ = ≡.refl
  xor-≢ {false} {false} ne = ⊥-elim (ne ≡.refl)

  rbit-√2 : ∀ y → rbit (√2ᶻ ZR.* y) ≡ oddᶻ y
  rbit-√2 (RootTwo a b) = ≡.cong rbit (√2*≡ a b)

k : ℕ
k = suc k′

L : Lvl
L = suc (toℕ p) , k , ℓ

-- The numerator of the column p.
Wn : Matrix n n D → Vec Z n
Wn M = num (col M p)

------------------------------------------------------------------------
-- Hard edges, and the others

Hardᶜ : Gen n → Matrix n n D → Set
Hardᶜ (H-gen a b _) M = Odd (Wn M ! a) × Odd (Wn M ! b) × rbit (Wn M ! a) ≢ rbit (Wn M ! b)
Hardᶜ (X-gen _ _ _) M = ⊥
Hardᶜ (Z-gen _) M = ⊥

Ok : Gen n → Matrix n n D → Set
Ok g M = Hardᶜ g M → ⊥

ok-X : ∀ a b .(ab : a < b) M → Ok (X-gen a b ab) M
ok-X a b ab M ()

private
  -- X[a,b] swaps entries a and b of the numerator.
  numX : ∀ {a b} .(ab : a < b) (M : Matrix n n D) → Wn (actM (X-gen a b ab) M) ≡ Xᶻ a b (Wn M)
  numX {a} {b} ab M = ≡.trans (≡.cong num (col-actM (X-gen a b ab) M p)) (proj₂ (lde-X a b ab (col M p)))

ok-c4 : ∀ {a b c} .(ab : a < b) .(bc : b < c) .(ac : a < c) M → Ok (H-gen b c bc) M → Ok (H-gen a c ac) (actM (X-gen a b ab) M)
ok-c4 {a} {b} {c} ab bc ac M ok (oa , oc , r) = ok (≡.trans (≡.cong oddᶻ (≡.sym ea)) oa , ≡.trans (≡.cong oddᶻ (≡.sym ec)) oc ,
                                                    λ e → r (≡.trans (≡.cong rbit ea) (≡.trans e (≡.cong rbit (≡.sym ec)))))
  where
  ea : Wn (actM (X-gen a b ab) M) ! a ≡ Wn M ! b
  ea = ≡.trans (≡.cong (_! a) (numX ab M)) (set₂-a a b _ _ _)
  ec : Wn (actM (X-gen a b ab) M) ! c ≡ Wn M ! c
  ec = ≡.trans (≡.cong (_! c) (numX ab M))
         (set₂-≢ a b _ _ _ (λ e → <⇒≢ ac (≡.sym e)) (λ e → <⇒≢ bc (≡.sym e)))

ok-c5 : ∀ {a b c} .(ab : a < b) .(bc : b < c) .(ac : a < c) M → Ok (H-gen a c ac) M → Ok (H-gen a b ab) (actM (X-gen b c bc) M)
ok-c5 {a} {b} {c} ab bc ac M ok (oa , ob , r) = ok (≡.trans (≡.cong oddᶻ (≡.sym ea)) oa , ≡.trans (≡.cong oddᶻ (≡.sym eb)) ob ,
                                                    λ e → r (≡.trans (≡.cong rbit ea) (≡.trans e (≡.cong rbit (≡.sym eb)))))
  where
  ea : Wn (actM (X-gen b c bc) M) ! a ≡ Wn M ! a
  ea = ≡.trans (≡.cong (_! a) (numX bc M)) (set₂-≢ b c _ _ _ (<⇒≢ ab) (<⇒≢ ac))
  eb : Wn (actM (X-gen b c bc) M) ! b ≡ Wn M ! c
  eb = ≡.trans (≡.cong (_! b) (numX bc M)) (set₂-a b c _ _ _)

------------------------------------------------------------------------
-- A hard H keeps the level

-- The pivot of a state at L.
pivot-at : (M : Matrix n n D) → levelᶜ M ≡ L → pivot M ≡ just p
pivot-at M eq = at (pivot M) ≡.refl
  where
  at : (r : Maybe (Fin n)) → pivot M ≡ r → pivot M ≡ just p
  at nothing e = ⊥-elim (ℕP.0≢1+n (≡.cong proj₁ (≡.trans (≡.sym (≡.cong (λ r → lvlAtᶜ r M) e)) eq)))
  at (just q) e = ≡.trans e (≡.cong just (FinP.toℕ-injective (ℕP.suc-injective (≡.cong proj₁ (≡.trans (≡.sym (levelᶜ-just M e)) eq)))))

-- The column of a hard H step: entries a and b stay odd, the others
-- stay.
record HardCol (M : Matrix n n D) (a b : Fin n) .(ab : a < b) : Set where
  field
    W″    : Vec Z n
    colH  : col (actM (H-gen a b ab) M) p ≡ scV k W″
    odd-a : Odd (W″ ! a)
    odd-b : Odd (W″ ! b)
    keep  : ∀ x → x ≢ a → x ≢ b → W″ ! x ≡ Wn M ! x
    cnt   : nodd W″ ≡ ℓ
    pvH   : pivot (actM (H-gen a b ab) M) ≡ just p

hard-col : (M : Matrix n n D) .(o : ColOrth M) → levelᶜ M ≡ L → ∀ a b .(ab : a < b) →
           Hardᶜ (H-gen a b ab) M → HardCol M a b ab
hard-col M o eq a b ab (oa , ob , r) = record
  { W″ = W″ ; colH = colH ; odd-a = ≡.trans (≡.cong oddᶻ (set₂-a a b α β W)) oα
  ; odd-b = ≡.trans (≡.cong oddᶻ (set₂-b a b α β W (<⇒≢ ab))) oβ
  ; keep = λ x x≢a x≢b → set₂-≢ a b α β W x≢a x≢b ; cnt = cnt ; pvH = pvH }
  where
  pv = pivot-at M eq
  open At M o pv using (W ; colW ; be ; lvl ; zero>)
  kM : lde (col M p) ≡ k
  kM = ≡.cong (λ t → proj₁ (proj₂ t)) (≡.trans (≡.sym lvl) eq)
  ℓM : nodd W ≡ ℓ
  ℓM = ≡.trans (≡.cong (λ K → third K W) (≡.sym kM)) (≡.cong (λ t → proj₂ (proj₂ t)) (≡.trans (≡.sym lvl) eq))
  sumE : oddᶻ (W ! a ZR.+ W ! b) ≡ false
  sumE = ≡.trans (oddᶻ-+ (W ! a) (W ! b)) (≡.cong₂ _xor_ oa ob)
  difE : oddᶻ (W ! a ZR.- W ! b) ≡ false
  difE = ≡.trans (oddᶻ-+ (W ! a) (ZR.- (W ! b))) (≡.cong₂ _xor_ oa (≡.trans (oddᶻ-neg (W ! b)) ob))
  δα = even⇒δ∣ (W ! a ZR.+ W ! b) sumE
  δβ = even⇒δ∣ (W ! a ZR.- W ! b) difE
  α = proj₁ δα
  β = proj₁ δβ
  W″ = set₂ a b α β W
  HM = actM (H-gen a b ab) M
  colH : col HM p ≡ scV k W″
  colH = ≡.trans (col-actM (H-gen a b ab) M p) (≡.trans (≡.cong (actV (H-gen a b ab)) (≡.trans colW (≡.cong (λ K → scV K W) kM)))
           (actV-H-same a b ab k W α β (proj₂ δα) (proj₂ δβ)))
  oα : oddᶻ α ≡ true
  oα = ≡.trans (≡.sym (rbit-√2 α)) (≡.trans (≡.cong rbit (≡.sym (proj₂ δα))) (≡.trans (rbit-+ (W ! a) (W ! b)) (xor-≢ r)))
  oβ : oddᶻ β ≡ true
  oβ = ≡.trans (≡.sym (rbit-√2 β)) (≡.trans (≡.cong rbit (≡.sym (proj₂ δβ)))
         (≡.trans (rbit-+ (W ! a) (ZR.- (W ! b))) (≡.trans (≡.cong (rbit (W ! a) xor_) (rbit-neg (W ! b))) (xor-≢ r))))
  same : ∀ x → oddᶻ (W″ ! x) ≡ oddᶻ (W ! x)
  same x = dec-elim (x FinP.≟ a)
    (λ { ≡.refl → ≡.trans (≡.cong oddᶻ (set₂-a x b α β W)) (≡.trans oα (≡.sym oa)) })
    (λ x≢a → dec-elim (x FinP.≟ b)
      (λ { ≡.refl → ≡.trans (≡.cong oddᶻ (set₂-b a x α β W (<⇒≢ ab))) (≡.trans oβ (≡.sym ob)) })
      (λ x≢b → ≡.cong oddᶻ (set₂-≢ a b α β W x≢a x≢b)))
  cnt : nodd W″ ≡ ℓ
  cnt = ≡.trans (count-cong _ _ same) ℓM
  min″ = inj₂ (a , ≡.trans (≡.cong oddᶻ (set₂-a a b α β W)) oα)
  b≤p : b ≤ p
  b≤p = odd⇒≤ {p = p} {W} zero> ob
  pvH : pivot HM ≡ just p
  pvH = pivot-char HM (ne-𝕀 HM p k′ W″ colH min″) (Beyond-actM (H-gen a b ab) {p} {M} b≤p be)

-- A hard H keeps the level.
hard-level : (M : Matrix n n D) .(o : ColOrth M) → levelᶜ M ≡ L → ∀ a b .(ab : a < b) →
             Hardᶜ (H-gen a b ab) M → levelᶜ (actM (H-gen a b ab) M) ≡ L
hard-level M o eq a b ab h =
  ≡.trans (levelᶜ-of (actM (H-gen a b ab) M) HC.pvH k HC.W″ HC.colH (inj₂ (a , HC.odd-a)))
          (≡.cong (λ c → suc (toℕ p) , k , c) HC.cnt)
  where module HC = HardCol (hard-col M o eq a b ab h)

-- An edge into L from below is not hard at its end at L.
ok-back : ∀ g M .(o : ColOrth M) → levelᶜ M <ₗ L → levelᶜ (actM g M) ≡ L → Ok g M → Ok g (actM g M)
ok-back (H-gen a b ab) M o lt eq _ h =
  <ₗ-irrefl (≡.subst (_<ₗ L) (≡.trans (≡.cong levelᶜ (≡.sym (act-gg (H-gen a b ab) M)))
                                     (hard-level (actM (H-gen a b ab) M) (ColOrth-actMʷ [ H-gen a b ab ]ʷ o) eq a b ab h)) lt)
ok-back (X-gen _ _ _) M o lt eq _ ()
ok-back (Z-gen _) M o lt eq _ ()

------------------------------------------------------------------------
-- The plain basic edges at L

private
  -- A level with pivot index d + 1 > p + 1 is not at or below L.
  not-le : ∀ {d : ℕ} {x} → toℕ p ℕ.< d → (suc d , x) ≤ₗ L → ⊥
  not-le p<d (inj₁ (inj₁ lt)) = ℕP.<-asym (s≤s p<d) lt
  not-le p<d (inj₁ (inj₂ (e , _))) = ℕP.<-irrefl (≡.sym e) (s≤s p<d)
  not-le p<d (inj₂ e) = ℕP.<-irrefl (≡.sym (≡.cong proj₁ e)) (s≤s p<d)

  -- An edge out of a state at L that does not go up acts on indices ≤ p.
  top≤ : (g : Gen n) (M : Matrix n n D) → pivot M ≡ just p → levelᶜ (actM g M) ≤ₗ L → top g ≤ p
  top≤ g M pv le = dec-elim (top g FinP.≤? p) (λ tg → tg)
    (λ ¬tg → ⊥-elim (not-le (ℕP.≰⇒> ¬tg) (≡.subst (_≤ₗ L) (levelᶜ-just (actM g M) (above M pv g (ℕP.≰⇒> ¬tg))) le)))

basicAt : BasicAtOk L Ok
basicAt (Z-gen j) _ M o eq le ok = Case2.Edge.case2 ih M o pv eq j (top≤ (Z-gen j) M pv le) le
  where pv = pivot-at M eq
basicAt (X-gen a b ab) adj M o eq le ok = Case1.Edge.case1 ih h1142 M o pv eq adj (top≤ (X-gen a b ab) M pv le) le
  where pv = pivot-at M eq
basicAt (H-gen a b ab) (t0 , t1) M o eq le ok =
  Case3.Edge.case3 ih M o pv eq t0 t1 (top≤ (H-gen a b ab) M pv le) le (λ _ _ o0 o1 r → ⊥-elim (ok (o0 , o1 , r)))
  where pv = pivot-at M eq

------------------------------------------------------------------------
-- The edges below L and the plain edges at L, over Clément's normal
-- words

private
  module C = ConjOk p k ℓ ih Ok ok-X ok-c4 ok-c5 ok-back basicAt

  conv-le : (M : Matrix n n D) → level M ≤ₗ L → levelᶜ M ≤ₗ L
  conv-le M (inj₁ lt) = inj₁ (Pos.conv< M lt)
  conv-le M (inj₂ e) = inj₂ (Pos.conv≡′ M e)

ihF : F.EdgesBelow p k′ ℓ synthᶜ
ihF g M o l₁ l₂ = ih g M o (Pos.conv< M l₁) (Pos.conv< (actM g M) l₂)

plain : F.PlainEdges p k′ ℓ synthᶜ
plain N oN eqN g le pl = C.edge-le g (top≤ g N pv leᶜ) N oN (inj₂ eqᶜ) leᶜ (ok-of g pl)
  where
  eqᶜ : levelᶜ N ≡ L
  eqᶜ = Pos.conv≡′ N eqN
  pv = pivot-at N eqᶜ
  leᶜ : levelᶜ (actM g N) ≤ₗ L
  leᶜ = conv-le (actM g N) le
  ok-of : (h : Gen n) → F.PlainAt p k′ ℓ synthᶜ N oN eqN h → Ok h N
  ok-of (H-gen a b ab) pl′ (oa , ob , r) = r (pl′ oa ob)
  ok-of (X-gen _ _ _) _ ()
  ok-of (Z-gen _) _ ()

------------------------------------------------------------------------
-- Presentations of groups
--
-- The hard edge (PairEdges.Hard), after Clément's Case 3.4.
--
-- Let s be a state at L = (p + 1, k, 4) and c < d two odd entries of
-- different classes.  The other two odd entries are their partners e
-- and f, of the classes of c and d; on the window (c, d, e, f) the
-- entries are the values of the root forms of TreeTop (root-inst).
--
-- If no two entries of depth 1, nor two of depth 2, are of one class
-- (Sound.Minimal), the tree TreeTop gives Path (Hs c d) s (Sound).
-- Otherwise H on two such entries u, v is an edge at L, apart from
-- c, d; at H_uv · s the entries u, v are deeper, so the measure
-- 3 n₁ + n₂ (nᵢ the number of entries of depth i) drops, and the edge
-- from there gives the one from s (Sound.Main.conj-case).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Product.Base using (_,_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction using (EdgesBelow)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Hard {n : ℕ} (p : Fin n) (k′ ℓ : ℕ)
  (ih : EdgesBelow {n} (suc (toℕ p) , suc k′ , ℓ)) where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; not ; if_then_else_ ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (zero ; suc ; _<_ ; _≤_)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; ∃₂ ; _×_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_ ; tabulate)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)

open import Quantum.Synthesis.Matrix using (Matrix)
open import Quantum.Synthesis.Ring using (RootTwo)
open import Data.Integer.Base using () renaming (+_ to +ℤ_)

open import Word.Base
open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (oddℕ)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count ; count-cong ; count-one ; count-drop₂ ; count-pos)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (D ; Z ; module ZR ; module ZG ; √2ᶻ ; _^ᶻ_ ; oddᶻ ; rbit ; oddᶻ-+ ; rbit-+)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Norm using (2ᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (num ; Odd)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column using (nodd)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Step using (same-class)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (level)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (Path)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric {n} using (Hs)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PairBase p k′ ℓ ih using (k ; L ; module State)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Forms
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Subst using (liftF ; ⟦liftF⟧)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Check
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Tree
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.TreeFacts
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Depth
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.NFs using (nfData)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.TreeTop as TT
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.TreeNF38 as T38
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.TreeNF341 as T341
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Sound p k′ ℓ ih as S

open ZG using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

private
  f0 : ∀ {m} → Fin (suc m)
  f0 = zero
  f1 : ∀ {m} → Fin (suc (suc m))
  f1 = suc f0
  f2 : ∀ {m} → Fin (suc (suc (suc m)))
  f2 = suc f1
  f3 : ∀ {m} → Fin (suc (suc (suc (suc m))))
  f3 = suc f2
  f4 : ∀ {m} → Fin (suc (suc (suc (suc (suc m)))))
  f4 = suc f3
  f5 : ∀ {m} → Fin (suc (suc (suc (suc (suc (suc m))))))
  f5 = suc f4

  g0 g1 g2 g3 : Fin 4
  g0 = zero
  g1 = suc zero
  g2 = suc (suc zero)
  g3 = suc (suc (suc zero))

  W : Matrix n n D → Vec Z n
  W N = num (col N p)

------------------------------------------------------------------------
-- The root forms

root-inst : ∀ (wc wd we wf : Z) → oddᶻ wc ≡ true → oddᶻ wd ≡ true → rbit wc ≢ rbit wd →
            oddᶻ we ≡ true → rbit we ≡ rbit wc → oddᶻ wf ≡ true → rbit wf ≡ rbit wd →
            ∃ λ ρ → ⟦ TT.topForms ⟧ᵛ ρ ≡ wc ∷ wd ∷ we ∷ wf ∷ []
root-inst wc wd we wf oc od rcd oe re of rf = go (odd-decomp wc oc)
  where
  oc′ : oddᶻ (wc ZR.+ √2ᶻ) ≡ true
  oc′ = ≡.trans (oddᶻ-+ wc √2ᶻ) (≡.cong (Data.Bool.Base._xor false) oc)
  rdc : rbit wd ≡ rbit (wc ZR.+ √2ᶻ)
  rdc = ≡.trans (flip (rbit wc) (rbit wd) rcd) (≡.sym (rbit-+ wc √2ᶻ))
    where
    flip : ∀ a b → a ≢ b → b ≡ a xor true
    flip false false ne = ⊥-elim (ne ≡.refl)
    flip false true _ = ≡.refl
    flip true false _ = ≡.refl
    flip true true ne = ⊥-elim (ne ≡.refl)
  go : (∃ λ v0 → wc ≡ ZR.1# ZR.+ √2ᶻ ZR.* v0) → ∃ λ ρ → ⟦ TT.topForms ⟧ᵛ ρ ≡ wc ∷ wd ∷ we ∷ wf ∷ []
  go (v0 , e0) = go′ (same-class wd (wc ZR.+ √2ᶻ) od oc′ rdc) (same-class we wc oe oc re) (same-class wf wd of od rf)
    where
    go′ : (∃ λ z → wd ≡ (wc ZR.+ √2ᶻ) ZR.+ 2ᶻ ZR.* z) → (∃ λ z → we ≡ wc ZR.+ 2ᶻ ZR.* z) → (∃ λ z → wf ≡ wd ZR.+ 2ᶻ ZR.* z) →
          ∃ λ ρ → ⟦ TT.topForms ⟧ᵛ ρ ≡ wc ∷ wd ∷ we ∷ wf ∷ []
    go′ (z1 , e1) (z2 , e2) (z3 , e3) = (v0 ∷ z1 ∷ z2 ∷ z3 ∷ []) ,
      ≡.cong₂ _∷_ r0 (≡.cong₂ _∷_ r1 (≡.cong₂ _∷_ r2 (≡.cong₂ _∷_ r3 ≡.refl)))
      where
      Z0 = RootTwo (+ℤ 0) (+ℤ 0)
      Z1 = RootTwo (+ℤ 1) (+ℤ 0)
      Z1r = RootTwo (+ℤ 1) (+ℤ 1)
      r0 : ⟦ Vec.lookup TT.topForms g0 ⟧ (v0 ∷ z1 ∷ z2 ∷ z3 ∷ []) ≡ wc
      r0 = ≡.trans (ZG.solve 4 (λ v0 z1 z2 z3 → con Z1 :+ (con √2ᶻ :* v0 :+ (con Z0 :* z1 :+ (con Z0 :* z2 :+ (con Z0 :* z3 :+ con Z0))))
                                               := con ZR.1# :+ con √2ᶻ :* v0) ≡.refl v0 z1 z2 z3) (≡.sym e0)
      r1 : ⟦ Vec.lookup TT.topForms g1 ⟧ (v0 ∷ z1 ∷ z2 ∷ z3 ∷ []) ≡ wd
      r1 = ≡.trans (ZG.solve 4 (λ v0 z1 z2 z3 → con Z1r :+ (con √2ᶻ :* v0 :+ (con 2ᶻ :* z1 :+ (con Z0 :* z2 :+ (con Z0 :* z3 :+ con Z0))))
                                               := (con ZR.1# :+ con √2ᶻ :* v0 :+ con √2ᶻ) :+ con 2ᶻ :* z1) ≡.refl v0 z1 z2 z3)
             (≡.sym (≡.trans e1 (≡.cong (λ t → (t ZR.+ √2ᶻ) ZR.+ 2ᶻ ZR.* z1) e0)))
      r2 : ⟦ Vec.lookup TT.topForms g2 ⟧ (v0 ∷ z1 ∷ z2 ∷ z3 ∷ []) ≡ we
      r2 = ≡.trans (ZG.solve 4 (λ v0 z1 z2 z3 → con Z1 :+ (con √2ᶻ :* v0 :+ (con Z0 :* z1 :+ (con 2ᶻ :* z2 :+ (con Z0 :* z3 :+ con Z0))))
                                               := (con ZR.1# :+ con √2ᶻ :* v0) :+ con 2ᶻ :* z2) ≡.refl v0 z1 z2 z3)
             (≡.sym (≡.trans e2 (≡.cong (λ t → t ZR.+ 2ᶻ ZR.* z2) e0)))
      r3 : ⟦ Vec.lookup TT.topForms g3 ⟧ (v0 ∷ z1 ∷ z2 ∷ z3 ∷ []) ≡ wf
      r3 = ≡.trans (ZG.solve 4 (λ v0 z1 z2 z3 → con Z1r :+ (con √2ᶻ :* v0 :+ (con 2ᶻ :* z1 :+ (con Z0 :* z2 :+ (con 2ᶻ :* z3 :+ con Z0))))
                                               := ((con ZR.1# :+ con √2ᶻ :* v0 :+ con √2ᶻ) :+ con 2ᶻ :* z1) :+ con 2ᶻ :* z3) ≡.refl v0 z1 z2 z3)
             (≡.sym (≡.trans e3 (≡.cong (λ t → t ZR.+ 2ᶻ ZR.* z3) (≡.trans e1 (≡.cong (λ t → (t ZR.+ √2ᶻ) ZR.+ 2ᶻ ZR.* z1) e0)))))

------------------------------------------------------------------------
-- Counting

private
  off : ∀ {m} {y z : Fin m} → y ≢ z → (y == z) ≡ false
  off {y = y} {z} ne with y FinP.≟ z
  ... | yes e = ⊥-elim (ne e)
  ... | no _ = ≡.refl

  on : ∀ {m} (y : Fin m) → (y == y) ≡ true
  on y with y FinP.≟ y
  ... | yes _ = ≡.refl
  ... | no ne = ⊥-elim (ne ≡.refl)

  -- P without a and b.
  minus : ∀ {m} → (Fin m → Bool) → Fin m → Fin m → Fin m → Bool
  minus P a b y = if y == a then false else if y == b then false else P y

  minus-a : ∀ {m} (P : Fin m → Bool) a b → minus P a b a ≡ false
  minus-a P a b = ≡.cong (λ t → if t then false else if a == b then false else P a) (on a)

  minus-b : ∀ {m} (P : Fin m → Bool) a b → a ≢ b → minus P a b b ≡ false
  minus-b P a b ab = ≡.trans (≡.cong (λ t → if t then false else if b == b then false else P b) (off (λ e → ab (≡.sym e))))
                       (≡.cong (λ t → if t then false else P b) (on b))

  minus-o : ∀ {m} (P : Fin m → Bool) a b y → y ≢ a → y ≢ b → minus P a b y ≡ P y
  minus-o P a b y ya yb = ≡.trans (≡.cong (λ t → if t then false else if y == b then false else P y) (off ya))
                            (≡.cong (λ t → if t then false else P y) (off yb))

  drop2 : ∀ {m} (P : Fin m → Bool) a b → a ≢ b → P a ≡ true → P b ≡ true → count P ≡ suc (suc (count (minus P a b)))
  drop2 P a b ab pa pb = count-drop₂ P (minus P a b) a b ab pa pb (minus-a P a b) (minus-b P a b ab) (λ y ya yb → ≡.sym (minus-o P a b y ya yb))

  five : ∀ (P : Fin n → Bool) a b c d x → a ≢ b → c ≢ d → a ≢ c → a ≢ d → b ≢ c → b ≢ d →
         x ≢ a → x ≢ b → x ≢ c → x ≢ d → P a ≡ true → P b ≡ true → P c ≡ true → P d ≡ true → P x ≡ true →
         5 ℕ.≤ count P
  five P a b c d x ab cd ac ad bc bd xa xb xc xd pa pb pc pd px =
    ≡.subst (5 ℕ.≤_) (≡.sym (≡.trans (drop2 P a b ab pa pb) (≡.cong (λ t → suc (suc t)) (drop2 Pab a′ b′ cd rc rd))))
      (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (count-pos (minus Pab c d) x (≡.trans (minus-o Pab c d x xc xd) (≡.trans (minus-o P a b x xa xb) px)))))))
    where
    Pab = minus P a b
    a′ = c
    b′ = d
    rc : Pab c ≡ true
    rc = ≡.trans (minus-o P a b c (λ e → ac (≡.sym e)) (λ e → bc (≡.sym e))) pc
    rd : Pab d ≡ true
    rd = ≡.trans (minus-o P a b d (λ e → ad (≡.sym e)) (λ e → bd (≡.sym e))) pd

------------------------------------------------------------------------
-- Classes

private
  isB : Maybe Bool → Bool → Bool
  isB (just true) true = true
  isB (just false) false = true
  isB _ _ = false

  isB-sound : ∀ m b → isB m b ≡ true → m ≡ just b
  isB-sound (just true) true _ = ≡.refl
  isB-sound (just false) false _ = ≡.refl
  isB-sound (just true) false ()
  isB-sound (just false) true ()
  isB-sound nothing true ()
  isB-sound nothing false ()

  isB-just : ∀ m b → m ≡ just b → isB m b ≡ true
  isB-just _ true ≡.refl = ≡.refl
  isB-just _ false ≡.refl = ≡.refl

  -- Odd √2^(suc δ) y is even.
  pow-even : ∀ δ y → oddᶻ ((√2ᶻ ^ᶻ suc δ) ZR.* y) ≡ false
  pow-even δ y = ≡.trans (≡.cong oddᶻ (ZR.*-assoc √2ᶻ (√2ᶻ ^ᶻ δ) y)) (oddᶻ-* √2ᶻ ((√2ᶻ ^ᶻ δ) ZR.* y))
    where open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (oddᶻ-*)

module Core (ℓ4 : ℓ ≡ 4) where

  module S′ = S ℓ4
  open S′ using (Win ; win ; ι ; inj ; ι≤p ; out ; locW ; TagsOK ; Minimal ; NFThm ; module Main)

  ----------------------------------------------------------------------
  -- The trees' theorems

  private
    module M₀ = Main nfData (λ _ → false) (λ nf ())

  nf38-thm : NFThm nfData nf38
  nf38-thm s o eq w ρ eqv tg mn icd =
    M₀.sound T38.t38 T38.t38Tags true (NFData.ic (nfData nf38)) (NFData.id (nfData nf38)) T38.t38Forms ρ T38.t38-ok icd s o eq w eqv tg (λ _ → mn ≡.refl)

  nf341-thm : NFThm nfData nf341
  nf341-thm s o eq w ρ eqv tg mn icd =
    M₀.sound T341.t341 T341.t341Tags false (NFData.ic (nfData nf341)) (NFData.id (nfData nf341)) T341.t341Forms ρ T341.t341-ok icd s o eq w eqv tg (λ ())

  nfThms : ∀ nf → true ≡ true → NFThm nfData nf
  nfThms nf38 _ = nf38-thm
  nfThms nf341 _ = nf341-thm

  module M₁ = Main nfData (λ _ → true) nfThms

  top-thm : ∀ s .(o : ColOrth s) (eq : level s ≡ L) (w : Win 4 s) ρ → ⟦ TT.topForms ⟧ᵛ ρ ≡ locW w → Minimal s →
            Path (Hs (ι w g0) (ι w g1)) s o
  top-thm s o eq w ρ eqv mn = M₁.sound TT.top TT.topTags true g0 g1 TT.topForms ρ TT.top-ok (λ ()) s o eq w eqv tg0 (λ _ → mn)
    where
    tg0 : TagsOK s w TT.topTags
    tg0 zero δ ()
    tg0 (suc zero) δ ()
    tg0 (suc (suc zero)) δ ()
    tg0 (suc (suc (suc zero))) δ ()

  ----------------------------------------------------------------------
  -- Minimality, decided

  Viol : Matrix n n D → Set
  Viol N = ∃ λ δ → (δ ≡ 1 ⊎ δ ≡ 2) × ∃ λ b → ∃₂ λ u v → u ≢ v × cls? δ (W N ! u) ≡ just b × cls? δ (W N ! v) ≡ just b

  minimal? : ∀ N → Minimal N ⊎ Viol N
  minimal? N = combine (two? (P 1 true)) (two? (P 1 false)) (two? (P 2 true)) (two? (P 2 false))
    where
    P : ℕ → Bool → Fin n → Bool
    P δ b x = isB (cls? δ (W N ! x)) b
    Res : ℕ → Bool → Set
    Res δ b = (∃₂ λ u v → u ≢ v × P δ b u ≡ true × P δ b v ≡ true) ⊎ (∀ u v → u ≢ v → P δ b u ≡ true → P δ b v ≡ true → ⊥)
    viol : ∀ δ → (δ ≡ 1 ⊎ δ ≡ 2) → ∀ b → (∃₂ λ u v → u ≢ v × P δ b u ≡ true × P δ b v ≡ true) → Viol N
    viol δ δ12 b (u , v , uv , pu , pv) = δ , δ12 , b , u , v , uv , isB-sound _ b pu , isB-sound _ b pv
    combine : Res 1 true → Res 1 false → Res 2 true → Res 2 false → Minimal N ⊎ Viol N
    combine (inj₁ x) _ _ _ = inj₂ (viol 1 (inj₁ ≡.refl) true x)
    combine _ (inj₁ x) _ _ = inj₂ (viol 1 (inj₁ ≡.refl) false x)
    combine _ _ (inj₁ x) _ = inj₂ (viol 2 (inj₂ ≡.refl) true x)
    combine _ _ _ (inj₁ x) = inj₂ (viol 2 (inj₂ ≡.refl) false x)
    combine (inj₂ n1t) (inj₂ n1f) (inj₂ n2t) (inj₂ n2f) = inj₁ mn
      where
      none : ∀ δ b → δ ≡ 1 ⊎ δ ≡ 2 → ∀ u v → u ≢ v → P δ b u ≡ true → P δ b v ≡ true → ⊥
      none 1 true _ = n1t
      none 1 false _ = n1f
      none 2 true _ = n2t
      none 2 false _ = n2f
      none (suc (suc (suc _))) _ (inj₁ ())
      none (suc (suc (suc _))) _ (inj₂ ())
      none 0 _ (inj₁ ())
      none 0 _ (inj₂ ())
      δ12 : ∀ δ → 1 ℕ.≤ δ → δ ℕ.≤ 2 → δ ≡ 1 ⊎ δ ≡ 2
      δ12 (suc zero) _ _ = inj₁ ≡.refl
      δ12 (suc (suc zero)) _ _ = inj₂ ≡.refl
      δ12 (suc (suc (suc _))) _ (ℕ.s≤s (ℕ.s≤s ()))
      mn : Minimal N
      mn δ lo hi u v y y′ uv eu ev oy oy′ c =
        none δ (rbit y) (δ12 δ lo hi) u v uv (isB-just _ (rbit y) (cls?-complete δ (W N ! u) y eu oy))
          (isB-just _ (rbit y) (≡.trans (cls?-complete δ (W N ! v) y′ ev oy′) (≡.cong just (≡.sym c))))

  ----------------------------------------------------------------------
  -- The measure

  μ : Matrix n n D → ℕ
  μ N = 3 ℕ.* count (λ x → deep? 1 (W N ! x)) ℕ.+ count (λ x → deep? 2 (W N ! x))

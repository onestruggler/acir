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
open import Quantum.Synthesis.Matrix using (Matrix)
open import Word.Base using (Word)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (Gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics using (ColOrth)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Framework as F

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Hard {n : ℕ} (p : Fin n) (k′ ℓ : ℕ)
  (nw : (M : Matrix n n D) → .(ColOrth M) → Word (Gen n))
  (ih : F.EdgesBelow p k′ ℓ nw) (plain : F.PlainEdges p k′ ℓ nw) where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (zero ; suc ; _<_ ; _≤_)
import Data.Fin.Properties as FinP
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; ∃₂ ; _×_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Vec.Base as Vec using (Vec ; [] ; _∷_)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Decidable using (recompute)

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
open F p k′ ℓ nw using (Path)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric {n} using (Hs ; Hs-<)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PairLevels p k′ ℓ using (k ; L ; module State)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Forms
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Subst using (liftF ; ⟦liftF⟧ ; bitᶻ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Check
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Tree
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.TreeFacts
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Depth
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.NFs using (nfData)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.TreeTop as TT
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.TreeNF38 as T38
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.TreeNF341 as T341
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Sound p k′ ℓ nw ih plain as S

open ZG using (_:+_ ; _:*_ ; _:=_ ; con)

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

  ----------------------------------------------------------------------
  -- Pairing two entries of one depth and class

  pair-forms : ℕ → Bool → Vec (Form 6) 6
  pair-forms δ b = newF δ (just b) ∷ Vec.map liftF (newF δ (just b) ∷ Vec.map liftF TT.topForms)

  record PairOK (δ : ℕ) (b : Bool) : Set where
    field
      fs′ fcd : Vec (Form 6) 6
      st : stepF (Hˡ f0 f1) (pair-forms δ b) ≡ just fs′
      sc : stepF (Hˡ f2 f3) (pair-forms δ b) ≡ just fcd
      cg : check (Hˡ f0 f1 ∷ []) (pair-forms δ b) ≡ true
      ka : kindF fs′ ≡ just atL
      cl : check (Hˡ f0 f1 ∷ []) fcd ≡ true
      q0 q1 : Form 6
      h0 : halfFⁿ (suc δ) (Vec.lookup fs′ f0) ≡ just q0
      h1 : halfFⁿ (suc δ) (Vec.lookup fs′ f1) ≡ just q1
      sameT : Vec.tail (Vec.tail fs′) ≡ Vec.tail (Vec.tail (pair-forms δ b))

  pair-ok : ∀ δ b → δ ≡ 1 ⊎ δ ≡ 2 → PairOK δ b
  pair-ok .1 true (inj₁ ≡.refl) = record
    { st = ≡.refl ; sc = ≡.refl ; cg = ≡.refl ; ka = ≡.refl ; cl = ≡.refl ; h0 = ≡.refl ; h1 = ≡.refl
    ; sameT = ≡.refl }
  pair-ok .1 false (inj₁ ≡.refl) = record
    { st = ≡.refl ; sc = ≡.refl ; cg = ≡.refl ; ka = ≡.refl ; cl = ≡.refl ; h0 = ≡.refl ; h1 = ≡.refl
    ; sameT = ≡.refl }
  pair-ok .2 true (inj₂ ≡.refl) = record
    { st = ≡.refl ; sc = ≡.refl ; cg = ≡.refl ; ka = ≡.refl ; cl = ≡.refl ; h0 = ≡.refl ; h1 = ≡.refl
    ; sameT = ≡.refl }
  pair-ok .2 false (inj₂ ≡.refl) = record
    { st = ≡.refl ; sc = ≡.refl ; cg = ≡.refl ; ka = ≡.refl ; cl = ≡.refl ; h0 = ≡.refl ; h1 = ≡.refl
    ; sameT = ≡.refl }

  -- The root forms are odd.
  private
    top-odd : ∀ i → oddF (Vec.lookup TT.topForms i) ≡ true
    top-odd zero = ≡.refl
    top-odd (suc zero) = ≡.refl
    top-odd (suc (suc zero)) = ≡.refl
    top-odd (suc (suc (suc zero))) = ≡.refl

    lifted2 : ∀ (a b : Z) ρ → Vec.map (λ f → ⟦ f ⟧ (a ∷ b ∷ ρ)) (Vec.map liftF (Vec.map liftF TT.topForms)) ≡ ⟦ TT.topForms ⟧ᵛ ρ
    lifted2 a b ρ =
      ≡.trans (≡.sym (VecP.map-∘ (λ f → ⟦ f ⟧ (a ∷ b ∷ ρ)) liftF (Vec.map liftF TT.topForms)))
        (≡.trans (VecP.map-cong (λ f → ⟦liftF⟧ f a (b ∷ ρ)) (Vec.map liftF TT.topForms))
          (≡.trans (≡.sym (VecP.map-∘ (λ f → ⟦ f ⟧ (b ∷ ρ)) liftF TT.topForms)) (VecP.map-cong (λ f → ⟦liftF⟧ f b ρ) TT.topForms)))

    arith1 : ∀ a c d → c ℕ.≤ d ℕ.+ 2 → 3 ℕ.* a ℕ.+ c ℕ.< 3 ℕ.* suc (suc a) ℕ.+ d
    arith1 a c d le =
      ℕP.≤-trans (ℕ.s≤s (ℕP.+-monoʳ-≤ (3 ℕ.* a) le))
        (ℕP.≤-trans (ℕP.≤-reflexive (NS.solve 2 (λ a d → NS.con 1 NS.:+ (NS.con 3 NS.:* a NS.:+ (d NS.:+ NS.con 2)) NS.:= NS.con 3 NS.:* a NS.:+ d NS.:+ NS.con 3) ≡.refl a d))
          (ℕP.≤-trans (ℕP.m≤m+n (3 ℕ.* a ℕ.+ d ℕ.+ 3) 3)
            (ℕP.≤-reflexive (NS.solve 2 (λ a d → NS.con 3 NS.:* a NS.:+ d NS.:+ NS.con 3 NS.:+ NS.con 3 NS.:= NS.con 3 NS.:* (NS.con 2 NS.:+ a) NS.:+ d) ≡.refl a d))))
      where
      open import Data.Nat.Solver using (module +-*-Solver)
      module NS = +-*-Solver

    arith2 : ∀ a c → 3 ℕ.* a ℕ.+ c ℕ.< 3 ℕ.* a ℕ.+ suc (suc c)
    arith2 a c = ℕP.+-monoʳ-< (3 ℕ.* a) (ℕP.<-trans (ℕP.n<1+n c) (ℕP.n<1+n (suc c)))

  even-pow : ∀ δ → δ ≡ 1 ⊎ δ ≡ 2 → ∀ y → oddᶻ ((√2ᶻ ^ᶻ δ) ZR.* y) ≡ false
  even-pow .1 (inj₁ ≡.refl) y = pow-even 0 y
  even-pow .2 (inj₂ ≡.refl) y = pow-even 1 y

  -- The measure drops when two entries of depth δ go deeper.
  measure-drop : ∀ (s N : Matrix n n D) u v → u ≢ v → (∀ x → x ≢ u → x ≢ v → W N ! x ≡ W s ! x) →
                 ∀ δ b → δ ≡ 1 ⊎ δ ≡ 2 → cls? δ (W s ! u) ≡ just b → cls? δ (W s ! v) ≡ just b →
                 ∀ yu → W s ! u ≡ (√2ᶻ ^ᶻ δ) ZR.* yu → ∀ yv → W s ! v ≡ (√2ᶻ ^ᶻ δ) ZR.* yv →
                 ∀ qu qv → W N ! u ≡ (√2ᶻ ^ᶻ suc δ) ZR.* qu → W N ! v ≡ (√2ᶻ ^ᶻ suc δ) ZR.* qv → μ N ℕ.< μ s
  measure-drop s N u v uv agree δ b δ12 cu cv yu eyu yv eyv qu qv Nu Nv = at δ12 cu cv eyu eyv Nu Nv
    where
    P : ℕ → Matrix n n D → Fin n → Bool
    P e M x = deep? e (W M ! x)
    su : ∀ e → P e s u ≡ true → P e N u ≡ false → P e s v ≡ true → P e N v ≡ false →
         count (P e s) ≡ suc (suc (count (P e N)))
    su e psu pnu psv pnv = count-drop₂ (P e s) (P e N) u v uv psu psv pnu pnv
                             (λ x xu xv → ≡.cong (deep? e) (≡.sym (agree x xu xv)))
    deeper : ∀ e x q → W N ! x ≡ (√2ᶻ ^ᶻ suc e) ZR.* q → P e N x ≡ false
    deeper e x q eq′ = deep?-nothing e (W N ! x) (≡.trans (≡.cong (cls? e) eq′) (cls?-deeper e q))
    shallow : ∀ x y → W s ! x ≡ (√2ᶻ ^ᶻ 2) ZR.* y → P 1 s x ≡ false
    shallow x y e′ = deep?-nothing 1 (W s ! x) (≡.trans (≡.cong (cls? 1) e′) (cls?-deeper 1 y))
    three : ∀ q → (√2ᶻ ^ᶻ 3) ZR.* q ≡ (√2ᶻ ^ᶻ 2) ZR.* (√2ᶻ ZR.* q)
    three q = ZG.solve 1 (λ q → (con √2ᶻ :* (con √2ᶻ :* (con √2ᶻ :* con ZR.1#))) :* q
                              := (con √2ᶻ :* (con √2ᶻ :* con ZR.1#)) :* (con √2ᶻ :* q)) ≡.refl q
    at : ∀ {δ} → δ ≡ 1 ⊎ δ ≡ 2 → cls? δ (W s ! u) ≡ just b → cls? δ (W s ! v) ≡ just b →
         W s ! u ≡ (√2ᶻ ^ᶻ δ) ZR.* yu → W s ! v ≡ (√2ᶻ ^ᶻ δ) ZR.* yv →
         W N ! u ≡ (√2ᶻ ^ᶻ suc δ) ZR.* qu → W N ! v ≡ (√2ᶻ ^ᶻ suc δ) ZR.* qv → μ N ℕ.< μ s
    at (inj₁ ≡.refl) cu cv eyu eyv Nu Nv =
      ≡.subst (λ c → μ N ℕ.< 3 ℕ.* c ℕ.+ count (P 2 s))
        (≡.sym (su 1 (deep?-cls 1 (W s ! u) b cu) (deeper 1 u qu Nu) (deep?-cls 1 (W s ! v) b cv) (deeper 1 v qv Nv)))
        (arith1 (count (P 1 N)) (count (P 2 N)) (count (P 2 s))
          (count-le-2 (P 2 s) (P 2 N) u v (λ x xu xv → ≡.cong (deep? 2) (agree x xu xv))))
    at (inj₂ ≡.refl) cu cv eyu eyv Nu Nv =
      ≡.subst₂ (λ c c′ → μ N ℕ.< 3 ℕ.* c ℕ.+ c′)
        (count-cong (P 1 N) (P 1 s) one)
        (≡.sym (su 2 (deep?-cls 2 (W s ! u) b cu) (deeper 2 u qu Nu) (deep?-cls 2 (W s ! v) b cv) (deeper 2 v qv Nv)))
        (arith2 (count (P 1 N)) (count (P 2 N)))
      where
      one : ∀ x → P 1 N x ≡ P 1 s x
      one x = by (x FinP.≟ u) (x FinP.≟ v)
        where
        by : _ → _ → P 1 N x ≡ P 1 s x
        by (yes e) _ = ≡.subst (λ z → P 1 N z ≡ P 1 s z) (≡.sym e)
                         (≡.trans (deeper 1 u (√2ᶻ ZR.* qu) (≡.trans Nu (three qu))) (≡.sym (shallow u yu eyu)))
        by (no xu) (yes e) = ≡.subst (λ z → P 1 N z ≡ P 1 s z) (≡.sym e)
                               (≡.trans (deeper 1 v (√2ᶻ ZR.* qv) (≡.trans Nv (three qv))) (≡.sym (shallow v yv eyv)))
        by (no xu) (no xv) = ≡.cong (deep? 1) (agree x xu xv)

  -- H on two entries u, v of depth δ and class b, apart from the window:
  -- an edge out of s and out of Hs c d · s; at N = Hs v u · s the
  -- entries u, v are deeper and the rest are unchanged.
  pair-step : ∀ s .(o : ColOrth s) (eq : level s ≡ L) (w : Win 4 s) ρ → ⟦ TT.topForms ⟧ᵛ ρ ≡ locW w → Viol s →
              (∀ N .(oN : ColOrth N) (eqN : level N ≡ L) (outN : ∀ x → (∀ i → ι w i ≢ x) → oddᶻ (W N ! x) ≡ false) →
                 ⟦ TT.topForms ⟧ᵛ ρ ≡ locW (win {s = N} (ι w) (inj w) (ι≤p w) outN) → μ N ℕ.< μ s →
                 Path (Hs (ι w g0) (ι w g1)) N oN) →
              Path (Hs (ι w g0) (ι w g1)) s o
  pair-step s o eq w ρ eqv (δ , δ12 , b , u , v , uv , cu , cv) rec = from (entry u cu) (entry v cv)
    where
    pk = pair-ok δ b δ12
    open PairOK pk
    same : ∀ i → Vec.lookup fs′ (suc (suc i)) ≡ Vec.lookup (pair-forms δ b) (suc (suc i))
    same i = ≡.trans (lookup-tail fs′ (suc i)) (≡.trans (lookup-tail (Vec.tail fs′) i)
               (≡.trans (≡.cong (λ V → Vec.lookup V i) sameT)
                 (≡.sym (≡.trans (lookup-tail (pair-forms δ b) (suc i)) (lookup-tail (Vec.tail (pair-forms δ b)) i)))))
      where
      lookup-tail : ∀ {A : Set} {k} (u : Vec A (suc k)) j → Vec.lookup u (suc j) ≡ Vec.lookup (Vec.tail u) j
      lookup-tail (x ∷ u) j = ≡.refl
    -- The entries u and v as values of the new form.
    entry : ∀ x → cls? δ (W s ! x) ≡ just b →
            ∃ λ vx → (∀ {r} (ρ′ : Vec Z r) → ⟦ newF δ (just b) ⟧ (vx ∷ ρ′) ≡ W s ! x) × ∃ λ y → W s ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* y × oddᶻ y ≡ true
    entry x cx = at (cls?-sound δ (W s ! x) b cx)
      where
      at : (∃ λ y → W s ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* y × oddᶻ y ≡ true × rbit y ≡ b) →
           ∃ λ vx → (∀ {r} (ρ′ : Vec Z r) → ⟦ newF δ (just b) ⟧ (vx ∷ ρ′) ≡ W s ! x) × ∃ λ y → W s ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* y × oddᶻ y ≡ true
      at (y , ey , oy , ry) = at′ (cls-decomp y b oy ry)
        where
        at′ : (∃ λ vx → y ≡ ZR.1# ZR.+ √2ᶻ ZR.* bitᶻ b ZR.+ (ZR.1# ZR.+ ZR.1#) ZR.* vx) →
              ∃ λ vx → (∀ {r} (ρ′ : Vec Z r) → ⟦ newF δ (just b) ⟧ (vx ∷ ρ′) ≡ W s ! x) × ∃ λ y → W s ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* y × oddᶻ y ≡ true
        at′ (vx , evx) = vx , (λ ρ′ → ≡.trans (⟦newF⟧ δ b vx ρ′) (≡.trans (≡.cong ((√2ᶻ ^ᶻ δ) ZR.*_) (≡.sym evx)) (≡.sym ey))) , y , ey , oy
    even-of : ∀ y → oddᶻ ((√2ᶻ ^ᶻ δ) ZR.* y) ≡ false
    even-of = even-pow δ δ12
    -- The window's entries are odd, so u, v lie outside it.
    win-odd : ∀ i → oddᶻ (W s ! ι w i) ≡ true
    win-odd i = ≡.trans (≡.cong oddᶻ (≡.trans (≡.sym (VecP.lookup∘tabulate (λ i → W s ! ι w i) i))
                                       (≡.trans (≡.cong (λ V → Vec.lookup V i) (≡.sym eqv)) (⟦⟧ᵛ-! TT.topForms ρ i))))
                  (oddF-sound (Vec.lookup TT.topForms i) (top-odd i) ρ)
    out-of : ∀ x y → W s ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* y → ∀ i → ι w i ≢ x
    out-of x y ey i e = t≢f (≡.trans (≡.sym (win-odd i)) (≡.trans (≡.cong (λ z → oddᶻ (W s ! z)) e) (≡.trans (≡.cong oddᶻ ey) (even-of y))))
    le-p : ∀ x y → W s ! x ≡ (√2ᶻ ^ᶻ δ) ZR.* y → oddᶻ y ≡ true → x ≤ p
    le-p x y ey oy = ℕP.≮⇒≥ λ p<x → pow-odd-≢0 δ y oy (≡.trans (≡.sym ey) (State.zero> s o eq x p<x))
    from : (∃ λ vx → (∀ {r} (ρ′ : Vec Z r) → ⟦ newF δ (just b) ⟧ (vx ∷ ρ′) ≡ W s ! u) × ∃ λ y → W s ! u ≡ (√2ᶻ ^ᶻ δ) ZR.* y × oddᶻ y ≡ true) →
           (∃ λ vx → (∀ {r} (ρ′ : Vec Z r) → ⟦ newF δ (just b) ⟧ (vx ∷ ρ′) ≡ W s ! v) × ∃ λ y → W s ! v ≡ (√2ᶻ ^ᶻ δ) ZR.* y × oddᶻ y ≡ true) →
           Path (Hs (ι w g0) (ι w g1)) s o
    from (vu , nu , yu , eyu , oyu) (vv , nv , yv , eyv , oyv) =
      M₁.conj-case (Hˡ f0 f1) tags6 false f2 f3 (pair-forms δ b) fs′ fcd ρ6 (λ ()) st sc ≡.refl cg ka cl s o eq w6 eqv6 tg6 (λ ()) rec6
      where
      ι6 : Fin 6 → Fin n
      ι6 zero = v
      ι6 (suc zero) = u
      ι6 (suc (suc i)) = ι w i
      ou = out-of u yu eyu
      ov = out-of v yv eyv
      inj6 : ∀ {i j} → ι6 i ≡ ι6 j → i ≡ j
      inj6 {zero} {zero} _ = ≡.refl
      inj6 {zero} {suc zero} e = ⊥-elim (uv (≡.sym e))
      inj6 {zero} {suc (suc j)} e = ⊥-elim (ov j (≡.sym e))
      inj6 {suc zero} {zero} e = ⊥-elim (uv e)
      inj6 {suc zero} {suc zero} _ = ≡.refl
      inj6 {suc zero} {suc (suc j)} e = ⊥-elim (ou j (≡.sym e))
      inj6 {suc (suc i)} {zero} e = ⊥-elim (ov i e)
      inj6 {suc (suc i)} {suc zero} e = ⊥-elim (ou i e)
      inj6 {suc (suc i)} {suc (suc j)} e = ≡.cong (λ k → suc (suc k)) (inj w e)
      ι≤p6 : ∀ i → ι6 i ≤ p
      ι≤p6 zero = le-p v yv eyv oyv
      ι≤p6 (suc zero) = le-p u yu eyu oyu
      ι≤p6 (suc (suc i)) = ι≤p w i
      w6 : Win 6 s
      w6 = win {s = s} ι6 inj6 ι≤p6 (λ x h → out w x (λ i → h (suc (suc i))))
      ρ6 = vv ∷ vu ∷ ρ
      eqv6 : ⟦ pair-forms δ b ⟧ᵛ ρ6 ≡ locW w6
      eqv6 = ≡.cong₂ _∷_ (nv (vu ∷ ρ)) (≡.cong₂ _∷_ (≡.trans (⟦liftF⟧ (newF δ (just b)) vv (vu ∷ ρ)) (nu ρ)) (≡.trans (lifted2 vv vu ρ) eqv))
      tags6 : Vec (Maybe ℕ) 6
      tags6 = Vec.replicate 6 nothing
      tg6 : TagsOK s w6 tags6
      tg6 i δ′ e = ⊥-elim (nj (≡.trans (≡.sym (VecP.lookup-replicate i nothing)) e))
        where
        nj : nothing ≢ just δ′
        nj ()
      rec6 : ∀ N .(oN : ColOrth N) (eqN : level N ≡ L) (wN : Win 6 N) → ι wN ≡ ι6 → ⟦ fs′ ⟧ᵛ ρ6 ≡ locW wN →
             (∀ x → (∀ i → ι6 i ≢ x) → W N ! x ≡ W s ! x) → TagsOK N wN (tagsAfter (Hˡ f0 f1) tags6) →
             (miniAfter {6} (Hˡ f0 f1) false ≡ true → Minimal N) → Path (Hs (ι wN f2) (ι wN f3)) N oN
      rec6 N oN eqN wN ιeq eqvN outsideN _ _ =
        ≡.subst (λ f → Path (Hs (f f2) (f f3)) N oN) (≡.sym ιeq) (rec N oN eqN outN eqv4N lt)
        where
        -- The entries of N in the window.
        vN : ∀ i → W N ! ι6 i ≡ ⟦ Vec.lookup fs′ i ⟧ ρ6
        vN i = ≡.trans (≡.cong (λ f → W N ! f i) (≡.sym ιeq))
                 (≡.trans (≡.sym (VecP.lookup∘tabulate (λ i → W N ! ι wN i) i))
                   (≡.trans (≡.cong (λ V → Vec.lookup V i) (≡.sym eqvN)) (⟦⟧ᵛ-! fs′ ρ6 i)))
        Nv : W N ! v ≡ (√2ᶻ ^ᶻ suc δ) ZR.* ⟦ q0 ⟧ ρ6
        Nv = ≡.trans (vN f0) (halfFⁿ-sound (suc δ) (Vec.lookup fs′ f0) h0 ρ6)
        Nu : W N ! u ≡ (√2ᶻ ^ᶻ suc δ) ZR.* ⟦ q1 ⟧ ρ6
        Nu = ≡.trans (vN f1) (halfFⁿ-sound (suc δ) (Vec.lookup fs′ f1) h1 ρ6)
        -- Away from u and v, N and s agree.
        s6 : ∀ i → W s ! ι6 i ≡ ⟦ Vec.lookup (pair-forms δ b) i ⟧ ρ6
        s6 i = ≡.trans (≡.sym (VecP.lookup∘tabulate (λ i → W s ! ι6 i) i))
                 (≡.trans (≡.cong (λ V → Vec.lookup V i) (≡.sym eqv6)) (⟦⟧ᵛ-! (pair-forms δ b) ρ6 i))
        agree-at : ∀ x → (∃ λ i → ι w i ≡ x) ⊎ (∀ i → ι w i ≢ x) → x ≢ u → x ≢ v → W N ! x ≡ W s ! x
        agree-at x (inj₁ (i , ≡.refl)) _ _ =
          ≡.trans (vN (suc (suc i))) (≡.trans (≡.cong (λ f → ⟦ f ⟧ ρ6) (same i)) (≡.sym (s6 (suc (suc i)))))
        agree-at x (inj₂ o′) xu xv = outsideN x h
          where
          h : ∀ i → ι6 i ≢ x
          h zero e = xv (≡.sym e)
          h (suc zero) e = xu (≡.sym e)
          h (suc (suc i)) e = o′ i e
        agree : ∀ x → x ≢ u → x ≢ v → W N ! x ≡ W s ! x
        agree x = agree-at x (Emb.where? (ι w) (inj w) x)
          where open import Examples.Groups.Real-Clifford+CH-TwoLevel.Local {n} using (module Emb)
        -- N's window (c, d, e, f).
        outN : ∀ x → (∀ i → ι w i ≢ x) → oddᶻ (W N ! x) ≡ false
        outN x h = by (x FinP.≟ u) (x FinP.≟ v)
          where
          by : _ → _ → oddᶻ (W N ! x) ≡ false
          by (yes e) _ = ≡.trans (≡.cong (λ z → oddᶻ (W N ! z)) e) (≡.trans (≡.cong oddᶻ Nu) (pow-even δ (⟦ q1 ⟧ ρ6)))
          by (no xu) (yes e) = ≡.trans (≡.cong (λ z → oddᶻ (W N ! z)) e) (≡.trans (≡.cong oddᶻ Nv) (pow-even δ (⟦ q0 ⟧ ρ6)))
          by (no xu) (no xv) = ≡.trans (≡.cong oddᶻ (agree x xu xv)) (out w x h)
        eqv4N : ⟦ TT.topForms ⟧ᵛ ρ ≡ locW (win {s = N} (ι w) (inj w) (ι≤p w) outN)
        eqv4N = vec-ext λ i →
          ≡.trans (≡.cong (λ V → Vec.lookup V i) (≡.sym (lifted2 vv vu ρ)))
            (≡.trans (VecP.lookup-map i (λ f → ⟦ f ⟧ ρ6) (Vec.map liftF (Vec.map liftF TT.topForms)))
              (≡.trans (≡.cong (λ f → ⟦ f ⟧ ρ6) (≡.sym (same i)))
                (≡.trans (≡.sym (vN (suc (suc i)))) (≡.sym (VecP.lookup∘tabulate (λ i → W N ! ι w i) i)))))
        lt : μ N ℕ.< μ s
        lt = measure-drop s N u v uv agree δ b δ12 cu cv yu eyu yv eyv _ _ Nu Nv

  ----------------------------------------------------------------------
  -- The recursion on the measure

  hard-rec : ∀ (fuel : ℕ) s .(o : ColOrth s) (eq : level s ≡ L) (w : Win 4 s) ρ → ⟦ TT.topForms ⟧ᵛ ρ ≡ locW w →
             μ s ℕ.< fuel → Path (Hs (ι w g0) (ι w g1)) s o
  hard-rec zero s o eq w ρ eqv ()
  hard-rec (suc fuel) s o eq w ρ eqv lt = from (minimal? s)
    where
    from : Minimal s ⊎ Viol s → Path (Hs (ι w g0) (ι w g1)) s o
    from (inj₁ mn) = top-thm s o eq w ρ eqv mn
    from (inj₂ vi) = pair-step s o eq w ρ eqv vi
      (λ N oN eqN outN eqvN ltN → hard-rec fuel N oN eqN (win {s = N} (ι w) (inj w) (ι≤p w) outN) ρ eqvN (ℕP.<-≤-trans ltN (ℕP.≤-pred lt)))

  ----------------------------------------------------------------------
  -- The window of a hard state

  private
    ¬t⇒f : ∀ {a} → (a ≡ true → ⊥) → a ≡ false
    ¬t⇒f {true} h = ⊥-elim (h ≡.refl)
    ¬t⇒f {false} _ = ≡.refl

  module Of-hard (s : Matrix n n D) .(o : ColOrth s) (eq : level s ≡ L) (four : nodd (W s) ≡ 4)
                 (c d : Fin n) (c≢d : c ≢ d) (oc : Odd (W s ! c)) (od : Odd (W s ! d)) (rcd : rbit (W s ! c) ≢ rbit (W s ! d)) where

    open State s o eq using (Cls ; cls-even ; cls-true ; cls-spec ; odd≤)

    -- Another odd entry of the same class.
    partner : ∀ x → Odd (W s ! x) → ∃ λ y → y ≢ x × (Odd (W s ! y) × rbit (W s ! y) ≡ rbit (W s ! x))
    partner x ox = from (two? (Cls b))
      where
      b = rbit (W s ! x)
      px : Cls b x ≡ true
      px = cls-true x ox
      from : (∃₂ λ u v → u ≢ v × Cls b u ≡ true × Cls b v ≡ true) ⊎ (∀ u v → u ≢ v → Cls b u ≡ true → Cls b v ≡ true → ⊥) →
             ∃ λ y → y ≢ x × (Odd (W s ! y) × rbit (W s ! y) ≡ b)
      from (inj₁ (u , v , uv , pu , pv)) = pick (u FinP.≟ x)
        where
        pick : _ → ∃ λ y → y ≢ x × (Odd (W s ! y) × rbit (W s ! y) ≡ b)
        pick (yes e) = v , (λ e′ → uv (≡.trans e (≡.sym e′))) , cls-spec b v pv
        pick (no ne) = u , ne , cls-spec b u pu
      from (inj₂ none) = ⊥-elim (t≢f (≡.trans (≡.sym (≡.cong oddℕ one)) (cls-even b)))
        where
        one : count (Cls b) ≡ 1
        one = count-one (Cls b) x px (λ y y≢x → ¬t⇒f (λ py → none y x y≢x py px))

    pe = partner c oc
    pf = partner d od
    e = proj₁ pe
    f = proj₁ pf
    e≢c = proj₁ (proj₂ pe)
    oe = proj₁ (proj₂ (proj₂ pe))
    re = proj₂ (proj₂ (proj₂ pe))
    f≢d = proj₁ (proj₂ pf)
    of = proj₁ (proj₂ (proj₂ pf))
    rf = proj₂ (proj₂ (proj₂ pf))

    rb : ∀ {x y} → x ≡ y → rbit (W s ! x) ≡ rbit (W s ! y)
    rb p = ≡.cong (λ z → rbit (W s ! z)) p

    e≢d : e ≢ d
    e≢d p = rcd (≡.trans (≡.sym re) (rb p))
    f≢c : f ≢ c
    f≢c p = rcd (≡.trans (≡.sym (rb p)) rf)
    e≢f : e ≢ f
    e≢f p = rcd (≡.trans (≡.sym re) (≡.trans (rb p) rf))

    ι4 : Fin 4 → Fin n
    ι4 zero = c
    ι4 (suc zero) = d
    ι4 (suc (suc zero)) = e
    ι4 (suc (suc (suc zero))) = f

    inj4 : ∀ {i j} → ι4 i ≡ ι4 j → i ≡ j
    inj4 {zero} {zero} _ = ≡.refl
    inj4 {zero} {suc zero} p = ⊥-elim (c≢d p)
    inj4 {zero} {suc (suc zero)} p = ⊥-elim (e≢c (≡.sym p))
    inj4 {zero} {suc (suc (suc zero))} p = ⊥-elim (f≢c (≡.sym p))
    inj4 {suc zero} {zero} p = ⊥-elim (c≢d (≡.sym p))
    inj4 {suc zero} {suc zero} _ = ≡.refl
    inj4 {suc zero} {suc (suc zero)} p = ⊥-elim (e≢d (≡.sym p))
    inj4 {suc zero} {suc (suc (suc zero))} p = ⊥-elim (f≢d (≡.sym p))
    inj4 {suc (suc zero)} {zero} p = ⊥-elim (e≢c p)
    inj4 {suc (suc zero)} {suc zero} p = ⊥-elim (e≢d p)
    inj4 {suc (suc zero)} {suc (suc zero)} _ = ≡.refl
    inj4 {suc (suc zero)} {suc (suc (suc zero))} p = ⊥-elim (e≢f p)
    inj4 {suc (suc (suc zero))} {zero} p = ⊥-elim (f≢c p)
    inj4 {suc (suc (suc zero))} {suc zero} p = ⊥-elim (f≢d p)
    inj4 {suc (suc (suc zero))} {suc (suc zero)} p = ⊥-elim (e≢f (≡.sym p))
    inj4 {suc (suc (suc zero))} {suc (suc (suc zero))} _ = ≡.refl

    ι≤p4 : ∀ i → ι4 i ≤ p
    ι≤p4 zero = odd≤ oc
    ι≤p4 (suc zero) = odd≤ od
    ι≤p4 (suc (suc zero)) = odd≤ oe
    ι≤p4 (suc (suc (suc zero))) = odd≤ of

    out4 : ∀ x → (∀ i → ι4 i ≢ x) → oddᶻ (W s ! x) ≡ false
    out4 x h = ¬t⇒f λ px → no5 (≡.subst (5 ℕ.≤_) four
      (five (λ y → oddᶻ (W s ! y)) c d e f x c≢d e≢f (λ p → e≢c (≡.sym p)) (λ p → f≢c (≡.sym p)) (λ p → e≢d (≡.sym p))
            (λ p → f≢d (≡.sym p)) (λ p → h zero (≡.sym p)) (λ p → h (suc zero) (≡.sym p)) (λ p → h (suc (suc zero)) (≡.sym p))
            (λ p → h (suc (suc (suc zero))) (≡.sym p)) oc od oe of px))
      where
      no5 : 5 ℕ.≤ 4 → ⊥
      no5 (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ()))))

    w4 : Win 4 s
    w4 = win {s = s} ι4 inj4 ι≤p4 out4

    inst : ∃ λ ρ → ⟦ TT.topForms ⟧ᵛ ρ ≡ locW w4
    inst = root-inst (W s ! c) (W s ! d) (W s ! e) (W s ! f) oc od rcd oe re of rf

  -- The hard edge.
  hard′ : ∀ (M : Matrix n n D) .(o : ColOrth M) (eq : level M ≡ L) → nodd (W M) ≡ 4 →
          ∀ c d .(cd : c < d) → Odd (W M ! c) → Odd (W M ! d) → rbit (W M ! c) ≢ rbit (W M ! d) → Path [ H-gen c d cd ]ʷ M o
  hard′ M o eq four c d cd oc od rcd =
    ≡.subst (λ w → Path w M o) (Hs-< cd) (hard-rec (suc (μ M)) M o eq OH.w4 (proj₁ OH.inst) (proj₂ OH.inst) ℕP.≤-refl)
    where
    module OH = Of-hard M o eq four c d (λ p → FinP.<-irrefl p (recompute (c FinP.<? d) cd)) oc od rcd

------------------------------------------------------------------------
-- PairEdges.Hard

hard : F.Hard p k′ ℓ nw
hard M o eq four c d cd oc od rcd = Core.hard′ (≡.trans (≡.sym (State.ℓM M o eq)) four) M o eq four c d cd oc od rcd

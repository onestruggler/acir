------------------------------------------------------------------------
-- Presentations of groups
--
-- The hard subcase of Case 3 (case 3.2.2.2 with w_β odd): k > 0, the
-- first two odd entries of w are j < α, and w_β is odd, β = α + 1.
-- Then there is a fourth odd entry ℓ′, and with D the powers of i
-- that make w_j, w_α, w_β, w_ℓ′ ≡ 1 (mod γ³) (Lemma "modulo-1-3"),
-- the square closes through G′ = V_r⁻¹ B V_s (HardRel), where B runs
-- through the states of the table of the paper (FourOdd): each has
-- an even entry j, so lies below s.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)

module Examples.Groups.Clifford+CS-TwoLevel.CaseXM {n : ℕ} where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Properties as ℕP
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_ ; ≢-sym)

open import Algebra.Solver.Ring.AlmostCommutativeRing using (fromCommutativeRing)
import Algebra.Solver.Ring.Simple
open import Instances using (_≟_ ; DEℤ)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx ; DecEqCplx)
open import Quantum.Synthesis.Ring.Properties using (commutativeRing-ZComplex)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+CS-TwoLevel.Ring
open import Examples.Groups.Clifford+CS-TwoLevel.Lde
open import Examples.Groups.Clifford+CS-TwoLevel.Column
open import Examples.Groups.Clifford+CS-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics hiding (_!_ ; U)
open import Examples.Groups.Clifford+CS-TwoLevel.Pivot using (pivot ; pivot-just ; Beyond ; level ; _<ₗ_)
open import Examples.Groups.Clifford+CS-TwoLevel.Syllable
  using (syl ; step ; Within ; Within-^ ; Beyond-actM ; Beyond-actMʷ)
open import Examples.Groups.Clifford+CS-TwoLevel.Levels using (Bℓ ; Minimal-X)
open import Examples.Groups.Clifford+CS-TwoLevel.Derived {n} using (_⁻¹)
open import Examples.Groups.Clifford+CS-TwoLevel.Basic {n} using (Letters≤)
open import Examples.Groups.Clifford+CS-TwoLevel.ExpLevel {n} using (word-level)
open import Examples.Groups.Clifford+CS-TwoLevel.Reduction {n} using (Square ; Below)
open import Examples.Groups.Clifford+CS-TwoLevel.MainTools {n}
  using (sound-vec ; lt-step ; square-syl ; syl-of ; word-below-all ; pivot-stay ; ne-𝕀 ; bℓ-below ; level-le)
open import Examples.Groups.Clifford+CS-TwoLevel.FourOdd {n}
  using (γ³ ; z ; y₁ ; y₂ ; u₁ ; u₂ ; u₃ ; u₄ ; even-y₁ ; even-u₁)
import Examples.Groups.Clifford+CS-TwoLevel.FourOdd {n} as FourOdd
import Examples.Groups.Clifford+CS-TwoLevel.HardRel {n} as HardRel
open import Examples.Groups.Clifford+CS-TwoLevel.CaseX {n} using (module Common ; Hard)
import Examples.Groups.Clifford+CS-TwoLevel.PivotColumn as PivotColumn

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})

private
  refl′ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  refl′ ≡.refl = refl

  module ZG = Algebra.Solver.Ring.Simple (fromCommutativeRing commutativeRing-ZComplex) (λ x y → x ≟ y)
  open ZG using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

------------------------------------------------------------------------
-- Residues modulo γ³ (Lemma "modulo-1-3")

-- 1 + 2c + γ³X, times ±1, is ≡ 1 (mod γ³).
lift : ∀ (c X : Z) → ∃ λ h → h ℕ.≤ 1 × ∃ λ A →
       (ⅈᶻ ^ᶻ (2 ℕ.* h)) ZR.* (ZR.1# ZR.+ 2ᶻ ZR.* c ZR.+ γ³ ZR.* X) ≡ z A
lift c X = by (oddᶻ c) ≡.refl
  where
  Goal : Set
  Goal = ∃ λ h → h ℕ.≤ 1 × ∃ λ A → (ⅈᶻ ^ᶻ (2 ℕ.* h)) ZR.* (ZR.1# ZR.+ 2ᶻ ZR.* c ZR.+ γ³ ZR.* X) ≡ z A
  by : (b : Bool) → oddᶻ c ≡ b → Goal
  by false ev = at (even⇒γ∣ c ev)
    where
    at : γ∣ c → Goal
    at (c₁ , e) = 0 , z≤n , (ZR.- ⅈᶻ) ZR.* c₁ ZR.+ X ,
      ≡.trans (≡.cong (λ y → ZR.1# ZR.* (ZR.1# ZR.+ 2ᶻ ZR.* y ZR.+ γ³ ZR.* X)) e)
        (ZG.solve 2 (λ c₁ X → con ZR.1# :* (con ZR.1# :+ con 2ᶻ :* (con γᶻ :* c₁) :+ con γ³ :* X)
                            := con ZR.1# :+ con γ³ :* ((:- con ⅈᶻ) :* c₁ :+ X)) ≡.refl c₁ X)
  by true od = at (even⇒γ∣ (c ZR.+ ZR.1#) (≡.trans (oddᶻ-+ c ZR.1#) (≡.cong (_xor oddᶻ ZR.1#) od)))
    where
    at : γ∣ (c ZR.+ ZR.1#) → Goal
    at (c₂ , e) = 1 , s≤s z≤n , ⅈᶻ ZR.* c₂ ZR.- X ,
      ≡.trans (≡.cong (λ y → (ⅈᶻ ^ᶻ 2) ZR.* (ZR.1# ZR.+ 2ᶻ ZR.* y ZR.+ γ³ ZR.* X)) c≡)
        (ZG.solve 2 (λ c₂ X → con (ⅈᶻ ^ᶻ 2) :* (con ZR.1# :+ con 2ᶻ :* (con γᶻ :* c₂ :- con ZR.1#) :+ con γ³ :* X)
                            := con ZR.1# :+ con γ³ :* (con ⅈᶻ :* c₂ :- X)) ≡.refl c₂ X)
      where
      c≡ : c ≡ γᶻ ZR.* c₂ ZR.- ZR.1#
      c≡ = ≡.trans (ZG.solve 1 (λ c → c := (c :+ con ZR.1#) :- con ZR.1#) ≡.refl c) (≡.cong (ZR._- ZR.1#) e)

-- An odd number, times a power of i, is ≡ 1 (mod γ³).
norm-odd : ∀ (w : Z) → Odd w → ∃ λ e → ∃ λ A → (ⅈᶻ ^ᶻ e) ZR.* w ≡ z A
norm-odd w ow = at (qOf-spec w ZR.1# ow ≡.refl)
  where
  q₀ = qOf w ZR.1#
  a₀ = invExp (ⅈᶻ ^ᶻ q₀)
  I = ⅈᶻ ^ᶻ a₀
  Q = ⅈᶻ ^ᶻ q₀
  unit : I ZR.* Q ≡ ZR.1#
  unit = invExp-unit q₀ (ℕP.≤-<-trans (qOf-≤1 w ZR.1#) (s≤s (s≤s z≤n)))
  at : 2∣ (w ZR.- Q ZR.* ZR.1#) → ∃ λ e → ∃ λ A → (ⅈᶻ ^ᶻ e) ZR.* w ≡ z A
  at (c , ec) = fin (lift (I ZR.* c) ZR.0#)
    where
    open ≡.≡-Reasoning
    Iw : I ZR.* w ≡ ZR.1# ZR.+ 2ᶻ ZR.* (I ZR.* c) ZR.+ γ³ ZR.* ZR.0#
    Iw = begin
      I ZR.* w
        ≡⟨ ZG.solve 3 (λ I y w → I :* w := I :* (y :+ (w :- y))) ≡.refl I (Q ZR.* ZR.1#) w ⟩
      I ZR.* (Q ZR.* ZR.1# ZR.+ (w ZR.- Q ZR.* ZR.1#))
        ≡⟨ ≡.cong (λ y → I ZR.* (Q ZR.* ZR.1# ZR.+ y)) ec ⟩
      I ZR.* (Q ZR.* ZR.1# ZR.+ 2ᶻ ZR.* c)
        ≡⟨ ZG.solve 3 (λ I Q c → I :* (Q :* con ZR.1# :+ con 2ᶻ :* c)
                              := (I :* Q) :* con ZR.1# :+ con 2ᶻ :* (I :* c) :+ con γ³ :* con ZR.0#) ≡.refl I Q c ⟩
      (I ZR.* Q) ZR.* ZR.1# ZR.+ 2ᶻ ZR.* (I ZR.* c) ZR.+ γ³ ZR.* ZR.0#
        ≡⟨ ≡.cong (λ y → y ZR.* ZR.1# ZR.+ 2ᶻ ZR.* (I ZR.* c) ZR.+ γ³ ZR.* ZR.0#) unit ⟩
      ZR.1# ZR.+ 2ᶻ ZR.* (I ZR.* c) ZR.+ γ³ ZR.* ZR.0# ∎
    fin : (∃ λ h → h ℕ.≤ 1 × ∃ λ A → (ⅈᶻ ^ᶻ (2 ℕ.* h)) ZR.* (ZR.1# ZR.+ 2ᶻ ZR.* (I ZR.* c) ZR.+ γ³ ZR.* ZR.0#) ≡ z A) →
          ∃ λ e → ∃ λ A → (ⅈᶻ ^ᶻ e) ZR.* w ≡ z A
    fin (h , _ , A , eA) = 2 ℕ.* h ℕ.+ a₀ , A , (begin
      (ⅈᶻ ^ᶻ (2 ℕ.* h ℕ.+ a₀)) ZR.* w         ≡⟨ ≡.cong (ZR._* w) (^ᶻ-+ ⅈᶻ (2 ℕ.* h) a₀) ⟩
      ((ⅈᶻ ^ᶻ (2 ℕ.* h)) ZR.* I) ZR.* w        ≡⟨ ZR.*-assoc (ⅈᶻ ^ᶻ (2 ℕ.* h)) I w ⟩
      (ⅈᶻ ^ᶻ (2 ℕ.* h)) ZR.* (I ZR.* w)        ≡⟨ ≡.cong ((ⅈᶻ ^ᶻ (2 ℕ.* h)) ZR.*_) Iw ⟩
      (ⅈᶻ ^ᶻ (2 ℕ.* h)) ZR.* (ZR.1# ZR.+ 2ᶻ ZR.* (I ZR.* c) ZR.+ γ³ ZR.* ZR.0#)
                                                ≡⟨ eA ⟩
      z A                                       ∎)

-- If iᶜ u ≡ 1 (mod γ³), then i^(c + 2h + q) w ≡ 1 (mod γ³) for some
-- h ≤ 1, where u ≡ iᑫ w (mod 2).
norm-rel : ∀ (u w : Z) (c : ℕ) (A : Z) → (ⅈᶻ ^ᶻ c) ZR.* u ≡ z A → Odd u → Odd w →
           ∃ λ h → h ℕ.≤ 1 × ∃ λ A′ → (ⅈᶻ ^ᶻ (c ℕ.+ (2 ℕ.* h ℕ.+ qOf u w))) ZR.* w ≡ z A′
norm-rel u w c A eu ou ow = at (qOf-spec u w ou ow)
  where
  q = qOf u w
  C = ⅈᶻ ^ᶻ c
  Q = ⅈᶻ ^ᶻ q
  at : 2∣ (u ZR.- Q ZR.* w) → ∃ λ h → h ℕ.≤ 1 × ∃ λ A′ → (ⅈᶻ ^ᶻ (c ℕ.+ (2 ℕ.* h ℕ.+ q))) ZR.* w ≡ z A′
  at (c′ , ec) = fin (lift (ZR.- (C ZR.* c′)) A)
    where
    open ≡.≡-Reasoning
    CQw : C ZR.* (Q ZR.* w) ≡ ZR.1# ZR.+ 2ᶻ ZR.* (ZR.- (C ZR.* c′)) ZR.+ γ³ ZR.* A
    CQw = begin
      C ZR.* (Q ZR.* w)
        ≡⟨ ZG.solve 3 (λ C u y → C :* y := C :* (u :- (u :- y))) ≡.refl C u (Q ZR.* w) ⟩
      C ZR.* (u ZR.- (u ZR.- Q ZR.* w))
        ≡⟨ ≡.cong (λ y → C ZR.* (u ZR.- y)) ec ⟩
      C ZR.* (u ZR.- 2ᶻ ZR.* c′)
        ≡⟨ ZG.solve 3 (λ C u c′ → C :* (u :- con 2ᶻ :* c′) := C :* u :- con 2ᶻ :* (C :* c′)) ≡.refl C u c′ ⟩
      C ZR.* u ZR.- 2ᶻ ZR.* (C ZR.* c′)
        ≡⟨ ≡.cong (λ y → y ZR.- 2ᶻ ZR.* (C ZR.* c′)) eu ⟩
      z A ZR.- 2ᶻ ZR.* (C ZR.* c′)
        ≡⟨ ZG.solve 2 (λ A y → (con ZR.1# :+ con γ³ :* A) :- con 2ᶻ :* y
                             := con ZR.1# :+ con 2ᶻ :* (:- y) :+ con γ³ :* A) ≡.refl A (C ZR.* c′) ⟩
      ZR.1# ZR.+ 2ᶻ ZR.* (ZR.- (C ZR.* c′)) ZR.+ γ³ ZR.* A ∎
    fin : (∃ λ h → h ℕ.≤ 1 × ∃ λ A′ → (ⅈᶻ ^ᶻ (2 ℕ.* h)) ZR.* (ZR.1# ZR.+ 2ᶻ ZR.* (ZR.- (C ZR.* c′)) ZR.+ γ³ ZR.* A) ≡ z A′) →
          ∃ λ h → h ℕ.≤ 1 × ∃ λ A′ → (ⅈᶻ ^ᶻ (c ℕ.+ (2 ℕ.* h ℕ.+ q))) ZR.* w ≡ z A′
    fin (h , h≤1 , A′ , eA) = h , h≤1 , A′ , (begin
      (ⅈᶻ ^ᶻ (c ℕ.+ (2 ℕ.* h ℕ.+ q))) ZR.* w
        ≡⟨ ≡.cong (ZR._* w) (≡.trans (^ᶻ-+ ⅈᶻ c (2 ℕ.* h ℕ.+ q)) (≡.cong (C ZR.*_) (^ᶻ-+ ⅈᶻ (2 ℕ.* h) q))) ⟩
      (C ZR.* (H ZR.* Q)) ZR.* w
        ≡⟨ ZG.solve 4 (λ C H Q w → (C :* (H :* Q)) :* w := H :* (C :* (Q :* w))) ≡.refl C H Q w ⟩
      H ZR.* (C ZR.* (Q ZR.* w))
        ≡⟨ ≡.cong (H ZR.*_) CQw ⟩
      H ZR.* (ZR.1# ZR.+ 2ᶻ ZR.* (ZR.- (C ZR.* c′)) ZR.+ γ³ ZR.* A)
        ≡⟨ eA ⟩
      z A′ ∎)
      where
      H = ⅈᶻ ^ᶻ (2 ℕ.* h)

------------------------------------------------------------------------
-- The subcase

module _ (α β : Fin n) (αβ1 : toℕ β ≡ suc (toℕ α))
         (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p) where

  open Common α β αβ1
  open PivotColumn s o ps

  hard : Hard α β αβ1 s o ps
  hard {K′} {j} ks fo nx oβ = go (third ks fo nx αβ oβ (λ x αx xβ → ⊥-elim (none-αβ αx xβ)))
    where
    jα : j < α
    jα = proj₁ (nextOdd-spec W nx)
    oj : Odd (W ! j)
    oj = proj₁ (firstOdd-spec W fo)
    oα : Odd (W ! α)
    oα = proj₁ (proj₂ (nextOdd-spec W nx))
    k = suc K′
    v≡ₖ : v ≡ scV k W
    v≡ₖ = ≡.trans v≡ (≡.cong (λ k → scV k W) ks)
    lvl′ : level s ≡ (suc (toℕ p) , k , nodd W)
    lvl′ = ≡.trans lvl (≡.cong (λ k → (suc (toℕ p) , k , nodd W)) ks)
    q = qOf (W ! j) (W ! α)
    q′ = qOf (W ! j) (W ! β)
    r = actM G s
    t = step s
    syl-s : syl s ≡ K† j α jα • i α ^ q
    syl-s = ≡.trans syl≡ (≡.trans (≡.cong (λ k → sylData p k W) ks) (sylData-pair {p = p} K′ W fo nx jα))

    cong-act : (w : Word (Gen n)) {x y : Vec D n} → x ≡ y → actVʷ w x ≡ actVʷ w y
    cong-act w ≡.refl = ≡.refl

    go : (∃ λ ℓ′ → nextOdd β W ≡ just ℓ′) → Square (X-gen α β αβ) s o
    go (ℓ′ , nx′) = with-j (norm-odd (W ! j) oj)
      where
      βℓ′ : β < ℓ′
      βℓ′ = proj₁ (nextOdd-spec W nx′)
      oℓ′ : Odd (W ! ℓ′)
      oℓ′ = proj₁ (proj₂ (nextOdd-spec W nx′))
      ℓ′≤p : ℓ′ ≤ p
      ℓ′≤p = odd≤ oℓ′

      module F = FourOdd.Four jα αβ βℓ′ W

      j≤ℓ′ : toℕ j ℕ.≤ toℕ ℓ′
      j≤ℓ′ = ℕP.<⇒≤ F.jℓ′
      α≤ℓ′ : toℕ α ℕ.≤ toℕ ℓ′
      α≤ℓ′ = ℕP.<⇒≤ F.ℓℓ′
      β≤ℓ′ : toℕ β ℕ.≤ toℕ ℓ′
      β≤ℓ′ = ℕP.<⇒≤ βℓ′
      j≤p = ℕP.≤-trans j≤ℓ′ ℓ′≤p
      α≤p = ℕP.≤-trans α≤ℓ′ ℓ′≤p
      β≤p = ℕP.≤-trans β≤ℓ′ ℓ′≤p

      -- The normal edge from r = X_[α,β] s is K†_[j,α] i_[α]^q′.
      U = Xᶻ α β W
      colU : col r p ≡ scV k U
      colU = ≡.trans (col-actM G s p) (≡.trans (≡.cong (actV G) v≡ₖ) (actV-X α β αβ k W))
      minU : Minimal k U
      minU = Minimal-X α β α≢β W (inj₂ (j , oj))
      pr : pivot r ≡ just p
      pr = pivot-stay G s β≤p ps (ne-𝕀 r p K′ U colU minU)
      syl-r : syl r ≡ K† j α jα • i α ^ q′
      syl-r = ≡.trans (syl-of r pr k U colU minU)
                (≡.trans (sylData-pair {p = p} K′ U foU nxU jα)
                  (≡.cong₂ (λ x y → K† j α jα • i α ^ qOf x y) Uj (Xᶻ-α W)))
        where
        jβ = ℕP.<-trans jα αβ
        Uj : U ! j ≡ W ! j
        Uj = Xᶻ-≢ W (FinP.<⇒≢ jα) (FinP.<⇒≢ jβ)
        foU : firstOdd U ≡ just j
        foU = firstOdd-char U (≡.subst Odd (≡.sym Uj) oj)
                (λ x xj → ≡.subst Even (≡.sym (Xᶻ-≢ W (FinP.<⇒≢ (ℕP.<-trans xj jα)) (FinP.<⇒≢ (ℕP.<-trans xj jβ))))
                                  (proj₂ (firstOdd-spec W fo) x xj))
        nxU : nextOdd j U ≡ just α
        nxU = nextOdd-char U jα (≡.subst Odd (≡.sym (Xᶻ-α W)) oβ)
                (λ x jx xα → ≡.subst Even (≡.sym (Xᶻ-≢ W (FinP.<⇒≢ xα) (FinP.<⇒≢ (ℕP.<-trans xα αβ))))
                                     (proj₂ (proj₂ (nextOdd-spec W nx)) x jx xα))

      -- Words of transpositions and powers of i at indices ≤ ℓ′ act
      -- on indices ≤ p.
      within : (w : Word (Gen n)) → Letters≤ ℓ′ w → Within p w
      within [ X-gen a b _ ]ʷ h = ℕP.≤-trans h ℓ′≤p
      within [ K-gen a b _ ]ʷ ()
      within [ i-gen a ]ʷ h = ℕP.≤-trans h ℓ′≤p
      within ε _ = tt
      within (u • w) (hu , hw) = within u hu , within w hw

      L = level s
      bℓ′ : Bℓ ℓ′ <ₗ L
      bℓ′ = ≡.subst (Bℓ ℓ′ <ₗ_) (≡.sym lvl′) (bℓ-below (nodd W) (s≤s z≤n) ℓ′≤p)
      lv : ∀ (M : Matrix n n D) → Beyond p M → (N : Vec Z n) → col M p ≡ scV k N →
           nodd N ℕ.< nodd W → level M <ₗ L
      lv M be N eq lt = ≡.subst (level M <ₗ_) (≡.sym lvl′) (level-le M be k N eq lt)

      -- K i i from M, when M and K† M lie below.
      kii : ∀ {x y : Fin n} (xy : x < y) (M : Matrix n n D) → toℕ x ℕ.≤ toℕ ℓ′ → toℕ y ℕ.≤ toℕ ℓ′ →
            level M <ₗ L → level (actMʷ (K x y xy • i x • i y) M) <ₗ L → Below L (K x y xy • i x • i y) M
      kii {x} {y} xy M xℓ yℓ lM lM′ =
        word-below-all (i x • i y) (xℓ , yℓ) M lM bℓ′ , (word-level (i x • i y) (xℓ , yℓ) M lM bℓ′ , lM′)

      with-j : (∃ λ e → ∃ λ A → (ⅈᶻ ^ᶻ e) ZR.* (W ! j) ≡ z A) → Square G s o
      with-j (c , A₁ , e₁) = with-rest (norm-rel (W ! j) (W ! α) c A₁ e₁ oj oα)
                                       (norm-rel (W ! j) (W ! β) c A₁ e₁ oj oβ)
                                       (norm-odd (W ! ℓ′) oℓ′)
        where
        with-rest : (∃ λ h → h ℕ.≤ 1 × ∃ λ A → (ⅈᶻ ^ᶻ (c ℕ.+ (2 ℕ.* h ℕ.+ q))) ZR.* (W ! α) ≡ z A) →
                    (∃ λ h → h ℕ.≤ 1 × ∃ λ A → (ⅈᶻ ^ᶻ (c ℕ.+ (2 ℕ.* h ℕ.+ q′))) ZR.* (W ! β) ≡ z A) →
                    (∃ λ e → ∃ λ A → (ⅈᶻ ^ᶻ e) ZR.* (W ! ℓ′) ≡ z A) → Square G s o
        with-rest (h₂ , h₂≤1 , A₂ , e₂) (h₃ , h₃≤1 , A₃ , e₃) (e₄ , A₄ , e₄′) =
          square-syl G s o (K† j α jα • i α ^ q′) H.G′ pr syl-r below (trans H.rel (cright refl′ (≡.sym syl-s)))
          where
          module H = HardRel.Hard jα αβ βℓ′ c h₂ q h₃ q′ e₄ h₂≤1 h₃≤1

          U₁ = u₁ A₁ A₂ A₃ A₄
          U₂ = u₂ A₁ A₂ A₃ A₄
          U₃ = u₃ A₁ A₂ A₃ A₄
          U₄ = u₄ A₁ A₂ A₃ A₄

          Kiiβℓ′ = K β ℓ′ βℓ′ • i β • i ℓ′
          Kiijβ = K j β F.jj′ • i j • i β
          Kiiαℓ′ = K α ℓ′ F.ℓℓ′ • i α • i ℓ′

          -- The states along B from V_s t.
          T₀ T₁ T₂ T₃ T₄ T₅ T₆ T₇ : Matrix n n D
          T₀ = actMʷ H.Vs t
          T₁ = actMʷ Kiiβℓ′ T₀
          T₂ = actMʷ Kiijβ T₁
          T₃ = actMʷ Kiiαℓ′ T₂
          T₄ = actM (X-gen α β αβ) T₃
          T₅ = actM (K-gen α ℓ′ F.ℓℓ′) T₄
          T₆ = actM (K-gen j β F.jj′) T₅
          T₇ = actM (K-gen β ℓ′ βℓ′) T₆

          -- Their columns p.
          cong4 : ∀ {a a′ b b′ c c′ d d′ : Z} → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → F.Nv a b c d ≡ F.Nv a′ b′ c′ d′
          cong4 ≡.refl ≡.refl ≡.refl ≡.refl = ≡.refl

          col₀ : col T₀ p ≡ scV k (F.Nv (y₁ A₁ A₂) (y₂ A₁ A₂) (z A₃) (z A₄))
          col₀ = ≡.trans (col-actMʷ (H.Vs • syl s) s p)
                   (≡.trans (≡.cong (λ w → actVʷ (H.Vs • w) v) syl-s)
                     (≡.trans (sound-vec H.T₀-rel v)
                       (≡.trans (cong-act (K j α jα • i j • i α)
                                  (≡.trans (cong-act H.D v≡ₖ)
                                    (≡.trans (F.diag k c H.E₂ H.E₃ e₄) (≡.cong (scV k) (cong4 e₁ e₂ e₃ e₄′)))))
                                (F.step₀ k A₁ A₂ A₃ A₄))))
          col₁ : col T₁ p ≡ scV k (F.Nv (y₁ A₁ A₂) (y₂ A₁ A₂) (y₁ A₃ A₄) (y₂ A₃ A₄))
          col₁ = ≡.trans (col-actMʷ Kiiβℓ′ T₀ p) (≡.trans (cong-act Kiiβℓ′ col₀) (F.step₁ k A₁ A₂ A₃ A₄))
          col₂ : col T₂ p ≡ scV k (F.Nv U₁ (y₂ A₁ A₂) U₃ (y₂ A₃ A₄))
          col₂ = ≡.trans (col-actMʷ Kiijβ T₁ p) (≡.trans (cong-act Kiijβ col₁) (F.step₂ k A₁ A₂ A₃ A₄))
          col₃ : col T₃ p ≡ scV k (F.Nv U₁ U₂ U₃ U₄)
          col₃ = ≡.trans (col-actMʷ Kiiαℓ′ T₂ p) (≡.trans (cong-act Kiiαℓ′ col₂) (F.step₃ k A₁ A₂ A₃ A₄))
          col₄ : col T₄ p ≡ scV k (F.Nv U₁ U₃ U₂ U₄)
          col₄ = ≡.trans (col-actM (X-gen α β αβ) T₃ p)
                   (≡.trans (≡.cong (actV (X-gen α β αβ)) col₃) (F.step₄ k A₁ A₂ A₃ A₄))
          col₅ : col T₅ p ≡ scV k (F.Nv U₁ (y₂ A₁ A₃) U₂ (y₂ A₂ A₄))
          col₅ = ≡.trans (col-actM (K-gen α ℓ′ F.ℓℓ′) T₄ p)
                   (≡.trans (≡.cong (actV (K-gen α ℓ′ F.ℓℓ′)) col₄) (F.step₅ k A₁ A₂ A₃ A₄))
          col₆ : col T₆ p ≡ scV k (F.Nv (y₁ A₁ A₃) (y₂ A₁ A₃) (y₁ A₂ A₄) (y₂ A₂ A₄))
          col₆ = ≡.trans (col-actM (K-gen j β F.jj′) T₅ p)
                   (≡.trans (≡.cong (actV (K-gen j β F.jj′)) col₅) (F.step₆ k A₁ A₂ A₃ A₄))
          col₇ : col T₇ p ≡ scV k (F.Nv (y₁ A₁ A₃) (y₂ A₁ A₃) (z A₂) (z A₄))
          col₇ = ≡.trans (col-actM (K-gen β ℓ′ βℓ′) T₆ p)
                   (≡.trans (≡.cong (actV (K-gen β ℓ′ βℓ′)) col₆) (F.step₇ k A₁ A₂ A₃ A₄))

          -- They agree with I beyond p.
          be₀ : Beyond p T₀
          be₀ = Beyond-actMʷ (H.Vs • syl s) {M = s}
                  (within H.Vs H.Vs-letters ,
                   ≡.subst (Within p) (≡.sym syl-s) (Within-^ (K j α jα) α≤p 7 , Within-^ (i α) α≤p q))
                  (proj₂ (pivot-just s ps))
          be₁ = Beyond-actMʷ Kiiβℓ′ {M = T₀} (ℓ′≤p , β≤p , ℓ′≤p) be₀
          be₂ = Beyond-actMʷ Kiijβ {M = T₁} (β≤p , j≤p , β≤p) be₁
          be₃ = Beyond-actMʷ Kiiαℓ′ {M = T₂} (ℓ′≤p , α≤p , ℓ′≤p) be₂
          be₄ = Beyond-actM (X-gen α β αβ) {M = T₃} β≤p be₃
          be₅ = Beyond-actM (K-gen α ℓ′ F.ℓℓ′) {M = T₄} ℓ′≤p be₄
          be₆ = Beyond-actM (K-gen j β F.jj′) {M = T₅} β≤p be₅
          be₇ = Beyond-actM (K-gen β ℓ′ βℓ′) {M = T₆} ℓ′≤p be₆

          -- They lie below s: their entry j is even.
          nodd< : ∀ x₁ x₂ x₃ x₄ → Even x₁ → nodd (F.Nv x₁ x₂ x₃ x₄) ℕ.< nodd W
          nodd< x₁ x₂ x₃ x₄ e = F.nodd-N x₁ x₂ x₃ x₄ e oj oα oβ oℓ′
          l₀ = lv T₀ be₀ _ col₀ (nodd< _ _ _ _ (even-y₁ A₁ A₂))
          l₁ = lv T₁ be₁ _ col₁ (nodd< _ _ _ _ (even-y₁ A₁ A₂))
          l₂ = lv T₂ be₂ _ col₂ (nodd< _ _ _ _ (even-u₁ A₁ A₂ A₃ A₄))
          l₃ = lv T₃ be₃ _ col₃ (nodd< _ _ _ _ (even-u₁ A₁ A₂ A₃ A₄))
          l₄ = lv T₄ be₄ _ col₄ (nodd< _ _ _ _ (even-u₁ A₁ A₂ A₃ A₄))
          l₅ = lv T₅ be₅ _ col₅ (nodd< _ _ _ _ (even-u₁ A₁ A₂ A₃ A₄))
          l₆ = lv T₆ be₆ _ col₆ (nodd< _ _ _ _ (even-y₁ A₁ A₃))
          l₇ = lv T₇ be₇ _ col₇ (nodd< _ _ _ _ (even-y₁ A₁ A₃))

          below : Below L H.G′ t
          below =
            (word-below-all H.Vs H.Vs-letters t (lt-step s o ps) bℓ′ ,
             ((((((kii βℓ′ T₀ β≤ℓ′ ℕP.≤-refl l₀ l₁ ,
                   kii F.jj′ T₁ j≤ℓ′ β≤ℓ′ l₁ l₂) ,
                  kii F.ℓℓ′ T₂ α≤ℓ′ ℕP.≤-refl l₂ l₃) ,
                 (l₃ , l₄)) ,
                (l₄ , l₅)) ,
               (l₅ , l₆)) ,
              (l₆ , l₇))) ,
            word-below-all (H.Vr ⁻¹) H.Vr⁻¹-letters T₇ l₇ bℓ′

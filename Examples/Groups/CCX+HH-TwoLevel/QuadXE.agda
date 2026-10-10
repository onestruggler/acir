------------------------------------------------------------------------
-- Presentations of groups
--
-- The edge X_[d,e] at a positive exponent when e = d + 1 is odd: the
-- fifth odd entry (Lemma A.20, Subcase 1.2.2.3).
--
-- There are then at least eight odd entries (their number is a multiple
-- of 4), a < … < h.  From s and from r = X_[d,e]·s, whose entries d and
-- e are exchanged, the paper's path takes the syllables on a..d and
-- e..h, the signed swap S, K_[a,b,c,d] and K_[e,f,g,h] (QuadXEBase);
-- the swap is the same from both, as it depends on the parity of all
-- eight entries' z's.  The two paths meet after X_[d,e] (QuadXERel, with
-- Rel8), and every state after the first syllables lies below s.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; _%_)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (col ; ColOrth ; actM)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (pivot ; level)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (lde)
import Examples.Groups.CCX+HH-TwoLevel.Reduction as R

module Examples.Groups.CCX+HH-TwoLevel.QuadXE {n : ℕ}
  (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p)
  {k′ : ℕ} (ks : lde (col s p) ≡ suc k′) (ih : R.EdgesBelow {n} (level s)) where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_ ; _∨_ ; if_then_else_)
open import Data.Empty using (⊥ ; ⊥-elim)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec) renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; dec-true ; dec-false)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (oddℤ)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (scV ; Minimal ; Odd ; Even ; Odd⇒¬Even)
open import Examples.Groups.CCX+HH-TwoLevel.Residue using (τ)
open import Examples.Groups.CCX+HH-TwoLevel.Column
open import Examples.Groups.CCX+HH-TwoLevel.ColumnAction using (Xᶻ ; actV-X)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
  using (_!_ ; actMʷ ; ColOrth-actMʷ ; set₂-a ; set₂-b ; set₂-≢ ; <⇒≢)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (_<ₗ_ ; Beyond)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable using (Beyond-actM)
open import Examples.Groups.CCX+HH-TwoLevel.Levels using (mono-level ; Mono ; nodd-X)
open import Examples.Groups.CCX+HH-TwoLevel.Norm using (nodd-mod4)
open import Examples.Groups.CCX+HH-TwoLevel.Step using (count-drop₄)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count ; count-one)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Counting using (count-two ; count-three)
open import Examples.Groups.CCX+HH-TwoLevel.Engine using (prfᶠ ; emb⁼ ; ⟪_⟫)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; emb ; [_]ᵢ ; _∷ᵢ_)
open import Examples.Groups.CCX+HH-TwoLevel.TauSyl using (mτ)
open R {n} using (Path ; Low ; path-• ; path-below)
open import Examples.Groups.CCX+HH-TwoLevel.PathTools {n} using (module Below)
import Examples.Groups.CCX+HH-TwoLevel.XEStep as XS
import Examples.Groups.CCX+HH-TwoLevel.Rel8 as R8
import Examples.Groups.CCX+HH-TwoLevel.QuadXERel as QR

open import Examples.Groups.CCX+HH-TwoLevel.QuadXEBase s o ps ks ih

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid

private
  ne< : ∀ {u v : Fin n} → u < v → u ≢ v
  ne< lt e = ℕP.<-irrefl (≡.cong toℕ e) lt
  gt : ∀ {u v : Fin n} → u < v → v ≢ u
  gt lt e = ne< lt (≡.sym e)
  _⟨<⟩_ = FinP.<-trans
  infixr 5 _⟨<⟩_

  -- A sign list as a word.
  mτ-w : ∀ (x : Fin n) τ (l : List (Gen n)) → ⟪ mτ x τ ++ l ⟫ ≈ Mτ x τ • ⟪ l ⟫
  mτ-w x true l = refl
  mτ-w x false l = sym left-unit

  mτ-w₁ : ∀ (x : Fin n) τ → ⟪ mτ x τ ⟫ ≈ Mτ x τ
  mτ-w₁ x true = right-unit
  mτ-w₁ x false = refl

  -- The paper's syllable as K times four signs.
  τword≈ : ∀ (U : Vec ℤ n) {i j k l : Fin n} .(ij : i < j) .(jk : j < k) .(kl : k < l) →
           XS.τword U ij jk kl ≈ [ K-gen i j k l ij jk kl ]ʷ •
             (Mτ i (τ (U ! i)) • (Mτ j (τ (U ! j)) • (Mτ k (τ (U ! k)) • Mτ l (τ (U ! l)))))
  τword≈ U {i} {j} {k} {l} ij jk kl = cong refl
    (trans (mτ-w i _ _) (cong refl (trans (mτ-w j _ _) (cong refl (trans (mτ-w k _ _) (cong refl (mτ-w₁ l _)))))))

  -- Four signs with equal flags.
  D≡ : ∀ (i j k l : Fin n) {τ₀ τ₁ τ₂ τ₃ σ₀ σ₁ σ₂ σ₃} → τ₀ ≡ σ₀ → τ₁ ≡ σ₁ → τ₂ ≡ σ₂ → τ₃ ≡ σ₃ →
       Mτ i τ₀ • (Mτ j τ₁ • (Mτ k τ₂ • Mτ l τ₃)) ≈ Mτ i σ₀ • (Mτ j σ₁ • (Mτ k σ₂ • Mτ l σ₃))
  D≡ i j k l ≡.refl ≡.refl ≡.refl ≡.refl = refl

  ≡⇒≈ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  ≡⇒≈ ≡.refl = refl

  -- Moving a level, or a Low, along an equation of matrices.
  castL : ∀ (M M′ : Matrix n n D) → M ≡ M′ → level M <ₗ level s → level M′ <ₗ level s
  castL M M′ eq l = ≡.subst (λ M → level M <ₗ level s) eq l

  castLow : ∀ (w : Word (Gen n)) (M M′ : Matrix n n D) → M ≡ M′ → Low (level s) w M → Low (level s) w M′
  castLow w M M′ eq l = ≡.subst (Low (level s) w) eq l

  -- Exchanging x and y between the two halves of an xor.
  swap-xy : ∀ A x y F₁ F₂ F₃ → (A xor x) xor (((y xor F₁) xor F₂) xor F₃) ≡ (A xor y) xor (((x xor F₁) xor F₂) xor F₃)
  swap-xy true true true true true true = ≡.refl
  swap-xy true true true true true false = ≡.refl
  swap-xy true true true true false true = ≡.refl
  swap-xy true true true true false false = ≡.refl
  swap-xy true true true false true true = ≡.refl
  swap-xy true true true false true false = ≡.refl
  swap-xy true true true false false true = ≡.refl
  swap-xy true true true false false false = ≡.refl
  swap-xy true true false true true true = ≡.refl
  swap-xy true true false true true false = ≡.refl
  swap-xy true true false true false true = ≡.refl
  swap-xy true true false true false false = ≡.refl
  swap-xy true true false false true true = ≡.refl
  swap-xy true true false false true false = ≡.refl
  swap-xy true true false false false true = ≡.refl
  swap-xy true true false false false false = ≡.refl
  swap-xy true false true true true true = ≡.refl
  swap-xy true false true true true false = ≡.refl
  swap-xy true false true true false true = ≡.refl
  swap-xy true false true true false false = ≡.refl
  swap-xy true false true false true true = ≡.refl
  swap-xy true false true false true false = ≡.refl
  swap-xy true false true false false true = ≡.refl
  swap-xy true false true false false false = ≡.refl
  swap-xy true false false true true true = ≡.refl
  swap-xy true false false true true false = ≡.refl
  swap-xy true false false true false true = ≡.refl
  swap-xy true false false true false false = ≡.refl
  swap-xy true false false false true true = ≡.refl
  swap-xy true false false false true false = ≡.refl
  swap-xy true false false false false true = ≡.refl
  swap-xy true false false false false false = ≡.refl
  swap-xy false true true true true true = ≡.refl
  swap-xy false true true true true false = ≡.refl
  swap-xy false true true true false true = ≡.refl
  swap-xy false true true true false false = ≡.refl
  swap-xy false true true false true true = ≡.refl
  swap-xy false true true false true false = ≡.refl
  swap-xy false true true false false true = ≡.refl
  swap-xy false true true false false false = ≡.refl
  swap-xy false true false true true true = ≡.refl
  swap-xy false true false true true false = ≡.refl
  swap-xy false true false true false true = ≡.refl
  swap-xy false true false true false false = ≡.refl
  swap-xy false true false false true true = ≡.refl
  swap-xy false true false false true false = ≡.refl
  swap-xy false true false false false true = ≡.refl
  swap-xy false true false false false false = ≡.refl
  swap-xy false false true true true true = ≡.refl
  swap-xy false false true true true false = ≡.refl
  swap-xy false false true true false true = ≡.refl
  swap-xy false false true true false false = ≡.refl
  swap-xy false false true false true true = ≡.refl
  swap-xy false false true false true false = ≡.refl
  swap-xy false false true false false true = ≡.refl
  swap-xy false false true false false false = ≡.refl
  swap-xy false false false true true true = ≡.refl
  swap-xy false false false true true false = ≡.refl
  swap-xy false false false true false true = ≡.refl
  swap-xy false false false true false false = ≡.refl
  swap-xy false false false false true true = ≡.refl
  swap-xy false false false false true false = ≡.refl
  swap-xy false false false false false true = ≡.refl
  swap-xy false false false false false false = ≡.refl

------------------------------------------------------------------------
-- The edge

module Edge {e : Fin n} (de : d < e) (adj : toℕ e ≡ suc (toℕ d)) (e≤p : e ≤ p) (oe : Odd (W ! e)) where

  private
    oa : Odd (W ! a)
    oa = proj₁ (firstOdd-spec W fo)
    ob = proj₁ (proj₂ (nextOdd-spec W na))
    oc = proj₁ (proj₂ (nextOdd-spec W nb))
    od = proj₁ (proj₂ (nextOdd-spec W nc))

    -- Nothing lies strictly between d and e.
    between : ∀ {z : Fin n} → d < z → z < e → ⊥
    between {z} dz ze = ℕP.<-irrefl ≡.refl (ℕP.<-≤-trans ze (≡.subst (ℕ._≤ toℕ z) (≡.sym adj) dz))

  nd : nextOdd d W ≡ just e
  nd = nextOdd-char W de oe (λ z dz ze → ⊥-elim (between dz ze))

  ----------------------------------------------------------------------
  -- Three more odd entries

  private
    O : Fin n → Bool
    O x = oddℤ (W ! x)
    Q : Fin n → Bool
    Q x = if does (x FinP.≟ a) ∨ does (x FinP.≟ b) ∨ does (x FinP.≟ c) ∨ does (x FinP.≟ d) then false else O x
    D₄′ = distinct₄ a<b b<c c<d
      where open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (distinct₄)

    if-f : ∀ {t : Bool} {x y : Bool} → t ≡ false → (if t then x else y) ≡ y
    if-f ≡.refl = ≡.refl
    if-t : ∀ {t : Bool} {x y : Bool} → t ≡ true → (if t then x else y) ≡ x
    if-t ≡.refl = ≡.refl
    or-t : ∀ {u v} → u ≡ true → u ∨ v ≡ true
    or-t {true} _ = ≡.refl
    or-r : ∀ {u v} → v ≡ true → u ∨ v ≡ true
    or-r {true} _ = ≡.refl
    or-r {false} h = h

    Qa : Q a ≡ false
    Qa = if-t (or-t (dec-true (a FinP.≟ a) ≡.refl))
    Qb : Q b ≡ false
    Qb = if-t (or-r {does (b FinP.≟ a)} (or-t (dec-true (b FinP.≟ b) ≡.refl)))
    Qc : Q c ≡ false
    Qc = if-t (or-r {does (c FinP.≟ a)} (or-r {does (c FinP.≟ b)} (or-t (dec-true (c FinP.≟ c) ≡.refl))))
    Qd : Q d ≡ false
    Qd = if-t (or-r {does (d FinP.≟ a)} (or-r {does (d FinP.≟ b)} (or-r {does (d FinP.≟ c)} (dec-true (d FinP.≟ d) ≡.refl))))
    Qo : ∀ x → x ≢ a → x ≢ b → x ≢ c → x ≢ d → Q x ≡ O x
    Qo x xa xb xc xd = if-f (≡.cong₂ _∨_ (dec-false (x FinP.≟ a) xa)
                         (≡.cong₂ _∨_ (dec-false (x FinP.≟ b) xb) (≡.cong₂ _∨_ (dec-false (x FinP.≟ c) xc) (dec-false (x FinP.≟ d) xd))))

    cnt₄ : count O ≡ 4 ℕ.+ count Q
    cnt₄ = count-drop₄ O Q D₄′ oa ob oc od Qa Qb Qc Qd (λ x xa xb xc xd → ≡.sym (Qo x xa xb xc xd))

    m4 : count O % 4 ≡ 0
    m4 = nodd-mod4 k′ W (≡.trans norm (≡.cong (4 ℕ.^_) ks))

    -- An entry counted by Q is odd and beyond d.
    beyond : ∀ x → Q x ≡ true → d < x × Odd (W ! x)
    beyond x qx = by (x FinP.≟ a) (x FinP.≟ b) (x FinP.≟ c) (x FinP.≟ d)
      where
      bad : ∀ {y} → x ≡ y → Q y ≡ false → ⊥
      bad ≡.refl qy = case (≡.trans (≡.sym qx) qy)
        where
        case : true ≡ false → ⊥
        case ()
      by : Dec (x ≡ a) → Dec (x ≡ b) → Dec (x ≡ c) → Dec (x ≡ d) → d < x × Odd (W ! x)
      by (yes e) _ _ _ = ⊥-elim (bad e Qa)
      by (no _) (yes e) _ _ = ⊥-elim (bad e Qb)
      by (no _) (no _) (yes e) _ = ⊥-elim (bad e Qc)
      by (no _) (no _) (no _) (yes e) = ⊥-elim (bad e Qd)
      by (no xa) (no xb) (no xc) (no xd) = side (FinP.<-cmp x d) , ox
        where
        ox : Odd (W ! x)
        ox = ≡.trans (≡.sym (Qo x xa xb xc xd)) qx
        side : Tri (x < d) (x ≡ d) (d < x) → d < x
        side (tri< x<d _ _) = ⊥-elim (Odd⇒¬Even {W ! x} ox (ev x x<d xa xb xc))
        side (tri≈ _ e _) = ⊥-elim (xd e)
        side (tri> _ _ dx) = dx

    -- Beyond d, the odd entries are e and then those found by nextOdd.
    after : ∀ {j k : Fin n} x → nextOdd j W ≡ just k → j < x → Odd (W ! x) → x ≡ k ⊎ k < x
    after {j} {k} x nk jx ox = by (FinP.<-cmp x k)
      where
      by : Tri (x < k) (x ≡ k) (k < x) → x ≡ k ⊎ k < x
      by (tri< x<k _ _) = ⊥-elim (Odd⇒¬Even {W ! x} ox (proj₂ (proj₂ (nextOdd-spec W nk)) x jx x<k))
      by (tri≈ _ e _) = inj₁ e
      by (tri> _ _ kx) = inj₂ kx

    none : ∀ {j : Fin n} x → nextOdd j W ≡ nothing → j < x → Odd (W ! x) → ⊥
    none x nj jx ox = Odd⇒¬Even {W ! x} ox (nextOdd-nothing W nj x jx)

    Qtrue : ∀ {x} → d < x → Odd (W ! x) → Q x ≡ true
    Qtrue {x} dx ox = ≡.trans (Qo x (gt (a<b ⟨<⟩ b<c ⟨<⟩ c<d ⟨<⟩ dx)) (gt (b<c ⟨<⟩ c<d ⟨<⟩ dx)) (gt (c<d ⟨<⟩ dx)) (gt dx)) ox

    mod-bad : ∀ {m} → count O ≡ m → m % 4 ≢ 0 → ⊥
    mod-bad eq ne = ne (≡.trans (≡.cong (_% 4) (≡.sym eq)) m4)

  record More : Set where
    field
      {f g h} : Fin n
      ne₀ : nextOdd e W ≡ just f
      nf₀ : nextOdd f W ≡ just g
      ng₀ : nextOdd g W ≡ just h

  more : More
  more = byF (nextOdd e W) ≡.refl
    where
    byF : (r : Maybe (Fin n)) → nextOdd e W ≡ r → More
    byF nothing ne = ⊥-elim (mod-bad (≡.trans cnt₄ (≡.cong (4 ℕ.+_) one)) (λ ()))
      where
      one : count Q ≡ 1
      one = count-one Q e (Qtrue de oe) (λ x xe → q x xe)
        where
        q : ∀ x → x ≢ e → Q x ≡ false
        q x xe = dec (Q x) ≡.refl
          where
          dec : ∀ t → Q x ≡ t → Q x ≡ false
          dec false h = h
          dec true h = ⊥-elim (by (after x nd (proj₁ (beyond x h)) (proj₂ (beyond x h))))
            where
            by : x ≡ e ⊎ e < x → ⊥
            by (inj₁ xe′) = xe xe′
            by (inj₂ ex) = none x ne ex (proj₂ (beyond x h))
    byF (just f) ne = byG (nextOdd f W) ≡.refl
      where
      ef = proj₁ (nextOdd-spec W ne)
      of = proj₁ (proj₂ (nextOdd-spec W ne))
      byG : (r : Maybe (Fin n)) → nextOdd f W ≡ r → More
      byG nothing nf = ⊥-elim (mod-bad (≡.trans cnt₄ (≡.cong (4 ℕ.+_) two)) (λ ()))
        where
        two : count Q ≡ 2
        two = count-two Q e f (ne< ef) (Qtrue de oe) (Qtrue (de ⟨<⟩ ef) of) inside
          where
          inside : ∀ x → Q x ≡ true → x ≡ e ⊎ x ≡ f
          inside x h = by (after x nd dx ox)
            where
            dx = proj₁ (beyond x h)
            ox = proj₂ (beyond x h)
            by : x ≡ e ⊎ e < x → x ≡ e ⊎ x ≡ f
            by (inj₁ xe) = inj₁ xe
            by (inj₂ ex) = by′ (after x ne ex ox)
              where
              by′ : x ≡ f ⊎ f < x → x ≡ e ⊎ x ≡ f
              by′ (inj₁ xf) = inj₂ xf
              by′ (inj₂ fx) = ⊥-elim (none x nf fx ox)
      byG (just g) nf = byH (nextOdd g W) ≡.refl
        where
        fg = proj₁ (nextOdd-spec W nf)
        og = proj₁ (proj₂ (nextOdd-spec W nf))
        byH : (r : Maybe (Fin n)) → nextOdd g W ≡ r → More
        byH nothing ng = ⊥-elim (mod-bad (≡.trans cnt₄ (≡.cong (4 ℕ.+_) three)) (λ ()))
          where
          three : count Q ≡ 3
          three = count-three Q e f g (ne< ef) (ne< (ef ⟨<⟩ fg)) (ne< fg)
                    (Qtrue de oe) (Qtrue (de ⟨<⟩ ef) of) (Qtrue (de ⟨<⟩ ef ⟨<⟩ fg) og) inside
            where
            inside : ∀ x → Q x ≡ true → x ≡ e ⊎ x ≡ f ⊎ x ≡ g
            inside x h = by (after x nd dx ox)
              where
              dx = proj₁ (beyond x h)
              ox = proj₂ (beyond x h)
              by : x ≡ e ⊎ e < x → x ≡ e ⊎ x ≡ f ⊎ x ≡ g
              by (inj₁ xe) = inj₁ xe
              by (inj₂ ex) = by′ (after x ne ex ox)
                where
                by′ : x ≡ f ⊎ f < x → x ≡ e ⊎ x ≡ f ⊎ x ≡ g
                by′ (inj₁ xf) = inj₂ (inj₁ xf)
                by′ (inj₂ fx) = by″ (after x nf fx ox)
                  where
                  by″ : x ≡ g ⊎ g < x → x ≡ e ⊎ x ≡ f ⊎ x ≡ g
                  by″ (inj₁ xg) = inj₂ (inj₂ xg)
                  by″ (inj₂ gx) = ⊥-elim (none x ng gx ox)
        byH (just h) ng = record { ne₀ = ne ; nf₀ = nf ; ng₀ = ng }

  ----------------------------------------------------------------------
  -- The two descents, given the eight odd entries

  module Main {f g h : Fin n} (ne₀ : nextOdd e W ≡ just f) (nf₀ : nextOdd f W ≡ just g) (ng₀ : nextOdd g W ≡ just h) where

    private
      ef = proj₁ (nextOdd-spec W ne₀)
      fg = proj₁ (nextOdd-spec W nf₀)
      gh = proj₁ (nextOdd-spec W ng₀)
      of = proj₁ (proj₂ (nextOdd-spec W ne₀))
      og = proj₁ (proj₂ (nextOdd-spec W nf₀))
      oh = proj₁ (proj₂ (nextOdd-spec W ng₀))

      h≤p : h ≤ p
      h≤p = odd≤ oh

      -- r = X_[d,e]·s has the entries d and e of W exchanged.
      Ur : Vec ℤ n
      Ur = Xᶻ d e W

      Ur-o : ∀ {z} → z ≢ d → z ≢ e → Ur ! z ≡ W ! z
      Ur-o zd ze = set₂-≢ d e (W ! e) (W ! d) W zd ze
      Urd : Ur ! d ≡ W ! e
      Urd = set₂-a d e (W ! e) (W ! d) W
      Ure : Ur ! e ≡ W ! d
      Ure = set₂-b d e (W ! e) (W ! d) W (<⇒≢ de)

      par : ∀ x → oddℤ (Ur ! x) ≡ oddℤ (W ! x)
      par x = by x (x FinP.≟ d) (x FinP.≟ e)
        where
        by : ∀ y → Dec (y ≡ d) → Dec (y ≡ e) → oddℤ (Ur ! y) ≡ oddℤ (W ! y)
        by _ (yes ≡.refl) _ = ≡.trans (≡.cong oddℤ Urd) (≡.trans oe (≡.sym od))
        by _ (no _) (yes ≡.refl) = ≡.trans (≡.cong oddℤ Ure) (≡.trans od (≡.sym oe))
        by y (no yd) (no ye) = ≡.cong oddℤ (Ur-o yd ye)

      eqR : col (actM (X-gen d e de) s) p ≡ scV K′ Ur
      eqR = ≡.trans (colg (X-gen d e de)) (actV-X d e de K′ W)

      beR : Beyond p (actM (X-gen d e de) s)
      beR = Beyond-actM (X-gen d e de) {p} {s} e≤p be

      cntR : nodd Ur ≡ nodd W
      cntR = nodd-X d e (<⇒≢ de) W

      foR : firstOdd Ur ≡ just a
      foR = ≡.trans (firstOdd-cong Ur W par) fo
      naR : nextOdd a Ur ≡ just b
      naR = ≡.trans (nextOdd-cong a Ur W par) na
      nbR : nextOdd b Ur ≡ just c
      nbR = ≡.trans (nextOdd-cong b Ur W par) nb
      ncR : nextOdd c Ur ≡ just d
      ncR = ≡.trans (nextOdd-cong c Ur W par) nc
      ndR : nextOdd d Ur ≡ just e
      ndR = ≡.trans (nextOdd-cong d Ur W par) nd
      neR : nextOdd e Ur ≡ just f
      neR = ≡.trans (nextOdd-cong e Ur W par) ne₀
      nfR : nextOdd f Ur ≡ just g
      nfR = ≡.trans (nextOdd-cong f Ur W par) nf₀
      ngR : nextOdd g Ur ≡ just h
      ngR = ≡.trans (nextOdd-cong g Ur W par) ng₀

      -- Order facts.
      ad = a<b ⟨<⟩ b<c ⟨<⟩ c<d
      bd = b<c ⟨<⟩ c<d

    module DS = Descent s o W colK be ≡.refl fo na nb nc nd ne₀ nf₀ ng₀ h≤p
    module DR = Descent (actM (X-gen d e de) s) (ColOrth-actMʷ [ X-gen d e de ]ʷ o) Ur eqR beR cntR foR naR nbR ncR ndR neR nfR ngR h≤p

    ----------------------------------------------------------------------
    -- Both choose the same swap

    private
      eight : ∀ {x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ : Bool} →
              x₁ ≡ y₁ → x₂ ≡ y₂ → x₃ ≡ y₃ → x₄ ≡ y₄ → x₅ ≡ y₅ → x₆ ≡ y₆ → x₇ ≡ y₇ → x₈ ≡ y₈ →
              (((x₁ xor x₂) xor x₃) xor x₄) xor (((x₅ xor x₆) xor x₇) xor x₈) ≡
              (((y₁ xor y₂) xor y₃) xor y₄) xor (((y₅ xor y₆) xor y₇) xor y₈)
      eight ≡.refl ≡.refl ≡.refl ≡.refl ≡.refl ≡.refl ≡.refl ≡.refl = ≡.refl

      oddR : ∀ x → Odd (W ! x) → Odd (Ur ! x)
      oddR x ox = ≡.trans (par x) ox

    useE≡ : DS.useE ≡ DR.useE
    useE≡ = ≡.trans (DS.useE-ζ oa ob oc od oe of og oh)
              (≡.trans (swap-xy ((XS.ζ (W ! a) oa xor XS.ζ (W ! b) ob) xor XS.ζ (W ! c) oc) (XS.ζ (W ! d) od) (XS.ζ (W ! e) oe)
                                (XS.ζ (W ! f) of) (XS.ζ (W ! g) og) (XS.ζ (W ! h) oh))
                (≡.sym (≡.trans (DR.useE-ζ (oddR a oa) (oddR b ob) (oddR c oc) (oddR d od) (oddR e oe) (oddR f of) (oddR g og) (oddR h oh))
                  (eight (XS.ζ-cong (Ur-o (ne< ad) (ne< (ad ⟨<⟩ de))) (oddR a oa) oa)
                         (XS.ζ-cong (Ur-o (ne< bd) (ne< (bd ⟨<⟩ de))) (oddR b ob) ob)
                         (XS.ζ-cong (Ur-o (ne< c<d) (ne< (c<d ⟨<⟩ de))) (oddR c oc) oc)
                         (XS.ζ-cong Urd (oddR d od) oe)
                         (XS.ζ-cong Ure (oddR e oe) od)
                         (XS.ζ-cong (Ur-o (gt (de ⟨<⟩ ef)) (gt ef)) (oddR f of) of)
                         (XS.ζ-cong (Ur-o (gt (de ⟨<⟩ ef ⟨<⟩ fg)) (gt (ef ⟨<⟩ fg))) (oddR g og) og)
                         (XS.ζ-cong (Ur-o (gt (de ⟨<⟩ ef ⟨<⟩ fg ⟨<⟩ gh)) (gt (ef ⟨<⟩ fg ⟨<⟩ gh))) (oddR h oh) oh)))))

    ----------------------------------------------------------------------
    -- The square

    private
      ZS : Word (Gen n) → Word (Gen n)
      ZS S = QR.Z a<b b<c c<d de ef fg gh (τ (W ! a)) (τ (W ! b)) (τ (W ! c)) (τ (W ! d))
                  (τ (W ! e)) (τ (W ! f)) (τ (W ! g)) (τ (W ! h)) S

      e8 : Emb 8 n
      e8 = emb (a ∷ᵛ b ∷ᵛ c ∷ᵛ d ∷ᵛ e ∷ᵛ f ∷ᵛ g ∷ᵛ h ∷ᵛ []ᵛ) (a<b ∷ᵢ b<c ∷ᵢ c<d ∷ᵢ de ∷ᵢ ef ∷ᵢ fg ∷ᵢ gh ∷ᵢ [ h ]ᵢ)

      xz-true : [ X-gen d e de ]ʷ • ZS (DS.Sw true) ≈ ZS (DS.Sw true) • [ X-gen d e de ]ʷ
      xz-true = trans (by-assoc ≡.refl) (trans (sym (prfᶠ (emb⁼ e8 R8.xz-e))) (by-assoc ≡.refl))

      xz-false : [ X-gen d e de ]ʷ • ZS (DS.Sw false) ≈ ZS (DS.Sw false) • [ X-gen d e de ]ʷ
      xz-false = trans (by-assoc ≡.refl) (trans (sym (prfᶠ (emb⁼ e8 R8.xz-h))) (by-assoc ≡.refl))

      fin : ∀ u → DS.useE ≡ u → DR.useE ≡ u → DR.Sw u ≡ DS.Sw u →
            [ X-gen d e de ]ʷ • ZS (DS.Sw u) ≈ ZS (DS.Sw u) • [ X-gen d e de ]ʷ → Path [ X-gen d e de ]ʷ s o
      fin u hS hR sw xz = pair-close s o W colK be ≡.refl fo na nb nc nd ne₀ nf₀ ng₀ h≤p (X-gen d e de) tt e≤p
                            Ur eqR beR cntR foR naR nbR ncR ndR neR nfR ngR u hS hR
        (trans (cong (cright cright cright cright T2≈) (τword≈ W a<b b<c c<d))
          (trans (QR.square a<b b<c c<d de ef fg gh (τ (W ! a)) (τ (W ! b)) (τ (W ! c)) (τ (W ! d))
                            (τ (W ! e)) (τ (W ! f)) (τ (W ! g)) (τ (W ! h)) (DS.Sw u) xz)
            (sym (cleft (cong (cright cright (cong (≡⇒≈ sw) T2R≈)) T1R≈)))))
        where
        T2≈ = trans (τword≈ DS.T₁.Wh DS.e<f DS.f<g DS.g<h)
                (cright D≡ e f g h (proj₁ DS.τ₂≡) (proj₁ (proj₂ DS.τ₂≡)) (proj₁ (proj₂ (proj₂ DS.τ₂≡))) (proj₂ (proj₂ (proj₂ DS.τ₂≡))))
        T1R≈ = trans (τword≈ Ur a<b b<c c<d)
                 (cright D≡ a b c d (≡.cong τ (Ur-o (ne< ad) (ne< (ad ⟨<⟩ de)))) (≡.cong τ (Ur-o (ne< bd) (ne< (bd ⟨<⟩ de))))
                                    (≡.cong τ (Ur-o (ne< c<d) (ne< (c<d ⟨<⟩ de)))) (≡.cong τ Urd))
        T2R≈ = trans (τword≈ DR.T₁.Wh DR.e<f DR.f<g DR.g<h)
                 (cright D≡ e f g h (≡.trans (proj₁ DR.τ₂≡) (≡.cong τ Ure))
                                    (≡.trans (proj₁ (proj₂ DR.τ₂≡)) (≡.cong τ (Ur-o (gt (de ⟨<⟩ ef)) (gt ef))))
                                    (≡.trans (proj₁ (proj₂ (proj₂ DR.τ₂≡))) (≡.cong τ (Ur-o (gt (de ⟨<⟩ ef ⟨<⟩ fg)) (gt (ef ⟨<⟩ fg)))))
                                    (≡.trans (proj₂ (proj₂ (proj₂ DR.τ₂≡)))
                                       (≡.cong τ (Ur-o (gt (de ⟨<⟩ ef ⟨<⟩ fg ⟨<⟩ gh)) (gt (ef ⟨<⟩ fg ⟨<⟩ gh))))))

    path : Path [ X-gen d e de ]ʷ s o
    path = go DS.useE ≡.refl
      where
      go : ∀ u → DS.useE ≡ u → Path [ X-gen d e de ]ʷ s o
      go true hu = fin true hu (≡.trans (≡.sym useE≡) hu) ≡.refl xz-true
      go false hu = fin false hu (≡.trans (≡.sym useE≡) hu) ≡.refl xz-false

  path : Path [ X-gen d e de ]ʷ s o
  path = Main.path (More.ne₀ more) (More.nf₀ more) (More.ng₀ more)

------------------------------------------------------------------------
-- The edge, in the form QuadX.EdgeX.edge asks for

edge-eodd : ∀ {x y : Fin n} .(xy : x < y) → toℕ y ≡ suc (toℕ x) → y ≤ p → x ≡ d → Odd (W ! y) →
            Path [ X-gen x y xy ]ʷ s o
edge-eodd {y = y} xy adj y≤p ≡.refl oy = Edge.path (≡.subst (toℕ d ℕ.<_) (≡.sym adj) (ℕP.n<1+n (toℕ d))) adj y≤p oy

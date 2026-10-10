------------------------------------------------------------------------
-- Presentations of groups
--
-- Columns along the paper's path for the edge X_[d,e] when e is odd
-- (Lemma A.20, Subcase 1.2.2.3), as integer vectors at a fixed exponent.
--
-- * Tau: the paper's syllable K (-1)^τ on four odd entries i < j < k < l.
--   The signs make the entries 1 + 4z (Residue.one4), and K turns them
--   into 2(1 + rowA z), 2 rowB z, 2 rowC z, 2 rowD z: even, with halves
--   whose parities are those of the z's summed, the first flipped.
--   The syllable is a word of X's and (-1)'s times the normal syllable
--   (RelTau).
-- * EvenK: K on four even entries 2u with an even number of odd u's
--   leaves them even.
-- * Swap: the column after (-1)_[a] (-1)_[x] X_[a,x].
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.XEStep where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_)
import Data.Fin.Base as F
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (ℤ ; +_)
import Data.Integer.Solver as ℤSolver
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.List.Properties using (map-++)
open import Data.Nat.Base as ℕ using (ℕ ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec ; lookup) renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_ ; refl ; cong ; sym ; trans)

open import Word.Base
import Presentation.Base as PB
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (oddℤ ; oddℤ-+)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (scV ; Odd ; Even)
open import Examples.Groups.CCX+HH-TwoLevel.Residue using (τ ; sgn ; one4)
open import Examples.Groups.CCX+HH-TwoLevel.Column using (Mτ)
open import Examples.Groups.CCX+HH-TwoLevel.ColumnAction
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics
  using (_!_ ; actV ; actVʷ ; set₁-a ; set₁-≢ ; set₂-a ; set₂-b ; set₂-≢ ; <⇒≢ ; distinct₄ ; Distinct₄)
open import Examples.Groups.CCX+HH-TwoLevel.Engine using (Eqn ; lhs ; rhs ; prf ; emb⁼ ; ⟪_⟫ ; ⟪++⟫)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; emb ; gen ; ι ; [_]ᵢ ; _∷ᵢ_)
open import Examples.Groups.CCX+HH-TwoLevel.TauSyl using (mτ ; map-mτ)
import Examples.Groups.CCX+HH-TwoLevel.KHalf as KH
import Examples.Groups.CCX+HH-TwoLevel.RelTau as RT

private
  variable
    n : ℕ
  module ℤS = ℤSolver.+-*-Solver
  open ℤS using (_:+_ ; _:*_ ; _:=_ ; con)

------------------------------------------------------------------------
-- Signs on vectors

sgnᶻ : Fin n → Bool → Vec ℤ n → Vec ℤ n
sgnᶻ x true  w = Mᶻ x w
sgnᶻ x false w = w

sgnᶻ-at : ∀ (x : Fin n) τ w → sgnᶻ x τ w ! x ≡ sgn τ (w ! x)
sgnᶻ-at x true  w = set₁-a x (ℤ.- (w ! x)) w
sgnᶻ-at x false w = refl

sgnᶻ-off : ∀ (x : Fin n) τ w {y} → y ≢ x → sgnᶻ x τ w ! y ≡ w ! y
sgnᶻ-off x true  w yx = set₁-≢ x (ℤ.- (w ! x)) w yx
sgnᶻ-off x false w yx = refl

act-mτ₁ : ∀ (x : Fin n) τ k w → actVʷ ⟪ mτ x τ ⟫ (scV k w) ≡ scV k (sgnᶻ x τ w)
act-mτ₁ x true  k w = actV-M x k w
act-mτ₁ x false k w = refl

act-mτ : ∀ (x : Fin n) τ (l : List (Gen n)) k w w′ → actVʷ ⟪ l ⟫ (scV k w) ≡ scV k w′ →
         actVʷ ⟪ mτ x τ ++ l ⟫ (scV k w) ≡ scV k (sgnᶻ x τ w′)
act-mτ x true  l k w w′ h = trans (cong (actV (M-gen x)) h) (actV-M x k w′)
act-mτ x false l k w w′ h = h

------------------------------------------------------------------------
-- Lists without K, and their words below an index

noK : List (Gen n) → Bool
noK [] = true
noK (M-gen _ ∷ xs) = noK xs
noK (X-gen _ _ _ ∷ xs) = noK xs
noK (K-gen _ _ _ _ _ _ _ ∷ xs) = false

tauS-noK : ∀ τ₀ τ₁ τ₂ τ₃ → noK (RT.tauS τ₀ τ₁ τ₂ τ₃) ≡ true
tauS-noK true  true  true  true  = refl
tauS-noK true  true  true  false = refl
tauS-noK true  true  false true  = refl
tauS-noK true  true  false false = refl
tauS-noK true  false true  true  = refl
tauS-noK true  false true  false = refl
tauS-noK true  false false true  = refl
tauS-noK true  false false false = refl
tauS-noK false true  true  true  = refl
tauS-noK false true  true  false = refl
tauS-noK false true  false true  = refl
tauS-noK false true  false false = refl
tauS-noK false false true  true  = refl
tauS-noK false false true  false = refl
tauS-noK false false false true  = refl
tauS-noK false false false false = refl

------------------------------------------------------------------------
-- The paper's syllable on four odd entries

module Tau (U : Vec ℤ n) {i j k l : Fin n} (ij : i < j) (jk : j < k) (kl : k < l)
           (oi : Odd (U ! i)) (oj : Odd (U ! j)) (ok : Odd (U ! k)) (ol : Odd (U ! l)) where

  private
    D₄ = distinct₄ ij jk kl
    open Distinct₄ D₄ renaming (ab to i≢j ; ac to i≢k ; ad to i≢l ; bc to j≢k ; bd to j≢l ; cd to k≢l)
    sym≢ : ∀ {u v : Fin n} → u ≢ v → v ≢ u
    sym≢ ne e = ne (sym e)

  τi τj τk τl : Bool
  τi = τ (U ! i)
  τj = τ (U ! j)
  τk = τ (U ! k)
  τl = τ (U ! l)

  -- The parity of the four, which the normal syllable carries.
  tsum : Bool
  tsum = ((τi xor τj) xor τk) xor τl

  zi zj zk zl : ℤ
  zi = proj₁ (one4 (U ! i) oi)
  zj = proj₁ (one4 (U ! j) oj)
  zk = proj₁ (one4 (U ! k) ok)
  zl = proj₁ (one4 (U ! l) ol)

  Kg : Gen n
  Kg = K-gen i j k l ij jk kl

  Tl : List (Gen n)
  Tl = Kg ∷ (mτ i τi ++ (mτ j τj ++ (mτ k τk ++ mτ l τl)))

  Tw : Word (Gen n)
  Tw = ⟪ Tl ⟫

  -- After the signs.
  Uτ : Vec ℤ n
  Uτ = sgnᶻ i τi (sgnᶻ j τj (sgnᶻ k τk (sgnᶻ l τl U)))

  col-signs : ∀ K → actVʷ ⟪ mτ i τi ++ (mτ j τj ++ (mτ k τk ++ mτ l τl)) ⟫ (scV K U) ≡ scV K Uτ
  col-signs K = act-mτ i τi _ K U _ (act-mτ j τj _ K U _ (act-mτ k τk _ K U _ (act-mτ₁ l τl K U)))

  private
    two-four : ∀ z → + 1 ℤ.+ + 4 ℤ.* z ≡ + 1 ℤ.+ + 2 ℤ.* (+ 2 ℤ.* z)
    two-four = ℤS.solve 1 (λ z → con (+ 1) :+ con (+ 4) :* z := con (+ 1) :+ con (+ 2) :* (con (+ 2) :* z)) refl

  Uτi : Uτ ! i ≡ + 1 ℤ.+ + 2 ℤ.* (+ 2 ℤ.* zi)
  Uτi = trans (sgnᶻ-at i τi _) (trans (cong (sgn τi) (trans (sgnᶻ-off j τj _ i≢j) (trans (sgnᶻ-off k τk _ i≢k) (sgnᶻ-off l τl _ i≢l))))
          (trans (proj₂ (one4 (U ! i) oi)) (two-four zi)))
  Uτj : Uτ ! j ≡ + 1 ℤ.+ + 2 ℤ.* (+ 2 ℤ.* zj)
  Uτj = trans (sgnᶻ-off i τi _ (sym≢ i≢j)) (trans (sgnᶻ-at j τj _) (trans (cong (sgn τj) (trans (sgnᶻ-off k τk _ j≢k) (sgnᶻ-off l τl _ j≢l)))
          (trans (proj₂ (one4 (U ! j) oj)) (two-four zj))))
  Uτk : Uτ ! k ≡ + 1 ℤ.+ + 2 ℤ.* (+ 2 ℤ.* zk)
  Uτk = trans (sgnᶻ-off i τi _ (sym≢ i≢k)) (trans (sgnᶻ-off j τj _ (sym≢ j≢k)) (trans (sgnᶻ-at k τk _)
          (trans (cong (sgn τk) (sgnᶻ-off l τl _ k≢l)) (trans (proj₂ (one4 (U ! k) ok)) (two-four zk)))))
  Uτl : Uτ ! l ≡ + 1 ℤ.+ + 2 ℤ.* (+ 2 ℤ.* zl)
  Uτl = trans (sgnᶻ-off i τi _ (sym≢ i≢l)) (trans (sgnᶻ-off j τj _ (sym≢ j≢l)) (trans (sgnᶻ-off k τk _ (sym≢ k≢l))
          (trans (sgnᶻ-at l τl _) (trans (proj₂ (one4 (U ! l) ol)) (two-four zl)))))

  open KH.Half Uτ ij jk kl (+ 1) (+ 1) (+ 1) (+ 1) (+ 2 ℤ.* zi) (+ 2 ℤ.* zj) (+ 2 ℤ.* zk) (+ 2 ℤ.* zl)
               Uτi Uτj Uτk Uτl (+ 2) (+ 0) (+ 0) (+ 0) refl refl refl refl
    public using (Wh)
  private
    open KH.Half Uτ ij jk kl (+ 1) (+ 1) (+ 1) (+ 1) (+ 2 ℤ.* zi) (+ 2 ℤ.* zj) (+ 2 ℤ.* zk) (+ 2 ℤ.* zl)
                 Uτi Uτj Uτk Uτl (+ 2) (+ 0) (+ 0) (+ 0) refl refl refl refl
      using (K-col ; Wh-a ; Wh-b ; Wh-c ; Wh-d ; Wh-≢)

  -- The column after the syllable.
  col-T : ∀ K → actVʷ Tw (scV K U) ≡ scV K Wh
  col-T K = trans (cong (actV Kg) (col-signs K)) (trans (actV-K i j k l ij jk kl K Uτ) (K-col K))

  -- The halves.
  hA hB hC hD : ℤ
  hA = + 1 ℤ.+ rowAᶻ zi zj zk zl
  hB = rowBᶻ zi zj zk zl
  hC = rowCᶻ zi zj zk zl
  hD = rowDᶻ zi zj zk zl

  Wh-i : Wh ! i ≡ + 2 ℤ.* hA
  Wh-i = trans Wh-a (ℤS.solve 4 (λ a b c d →
    con (+ 2) :+ (con p1ᶻ :* (con (+ 2) :* a) :+ con p1ᶻ :* (con (+ 2) :* b) :+ con p1ᶻ :* (con (+ 2) :* c) :+ con p1ᶻ :* (con (+ 2) :* d))
    := con (+ 2) :* (con (+ 1) :+ (con p1ᶻ :* a :+ con p1ᶻ :* b :+ con p1ᶻ :* c :+ con p1ᶻ :* d))) refl zi zj zk zl)
  Wh-j : Wh ! j ≡ + 2 ℤ.* hB
  Wh-j = trans Wh-b (ℤS.solve 4 (λ a b c d →
    con (+ 0) :+ (con p1ᶻ :* (con (+ 2) :* a) :+ con m1ᶻ :* (con (+ 2) :* b) :+ con p1ᶻ :* (con (+ 2) :* c) :+ con m1ᶻ :* (con (+ 2) :* d))
    := con (+ 2) :* (con p1ᶻ :* a :+ con m1ᶻ :* b :+ con p1ᶻ :* c :+ con m1ᶻ :* d)) refl zi zj zk zl)
  Wh-k : Wh ! k ≡ + 2 ℤ.* hC
  Wh-k = trans Wh-c (ℤS.solve 4 (λ a b c d →
    con (+ 0) :+ (con p1ᶻ :* (con (+ 2) :* a) :+ con p1ᶻ :* (con (+ 2) :* b) :+ con m1ᶻ :* (con (+ 2) :* c) :+ con m1ᶻ :* (con (+ 2) :* d))
    := con (+ 2) :* (con p1ᶻ :* a :+ con p1ᶻ :* b :+ con m1ᶻ :* c :+ con m1ᶻ :* d)) refl zi zj zk zl)
  Wh-l : Wh ! l ≡ + 2 ℤ.* hD
  Wh-l = trans Wh-d (ℤS.solve 4 (λ a b c d →
    con (+ 0) :+ (con p1ᶻ :* (con (+ 2) :* a) :+ con m1ᶻ :* (con (+ 2) :* b) :+ con m1ᶻ :* (con (+ 2) :* c) :+ con p1ᶻ :* (con (+ 2) :* d))
    := con (+ 2) :* (con p1ᶻ :* a :+ con m1ᶻ :* b :+ con m1ᶻ :* c :+ con p1ᶻ :* d)) refl zi zj zk zl)

  Wh-o : ∀ {x} → x ≢ i → x ≢ j → x ≢ k → x ≢ l → Wh ! x ≡ U ! x
  Wh-o xi xj xk xl = trans (Wh-≢ xi xj xk xl)
    (trans (sgnᶻ-off i τi _ xi) (trans (sgnᶻ-off j τj _ xj) (trans (sgnᶻ-off k τk _ xk) (sgnᶻ-off l τl _ xl))))

  -- The parity of the z's.
  Σz : Bool
  Σz = ((oddℤ zi xor oddℤ zj) xor oddℤ zk) xor oddℤ zl

  par-A : oddℤ hA ≡ not Σz
  par-A = trans (oddℤ-+ (+ 1) (rowAᶻ zi zj zk zl)) (cong (true xor_) (odd-rowA zi zj zk zl))
  par-B : oddℤ hB ≡ Σz
  par-B = odd-rowB zi zj zk zl
  par-C : oddℤ hC ≡ Σz
  par-C = odd-rowC zi zj zk zl
  par-D : oddℤ hD ≡ Σz
  par-D = odd-rowD zi zj zk zl

  ----------------------------------------------------------------------
  -- The syllable and the normal one

  e4 : Emb 4 n
  e4 = emb (i ∷ᵛ j ∷ᵛ k ∷ᵛ l ∷ᵛ []ᵛ) (ij ∷ᵢ jk ∷ᵢ kl ∷ᵢ [ l ]ᵢ)

  -- The word of X's and (-1)'s.
  S′ : Word (Gen n)
  S′ = ⟪ map (gen e4) (RT.tauS τi τj τk τl) ⟫

  S′-noK : noK (map (gen e4) (RT.tauS τi τj τk τl)) ≡ true
  S′-noK = noK-map (RT.tauS τi τj τk τl) (tauS-noK τi τj τk τl)
    where
    noK-map : ∀ (xs : List (Gen 4)) → noK xs ≡ true → noK (map (gen e4) xs) ≡ true
    noK-map [] h = refl
    noK-map (M-gen _ ∷ xs) h = noK-map xs h
    noK-map (X-gen _ _ _ ∷ xs) h = noK-map xs h
    noK-map (K-gen _ _ _ _ _ _ _ ∷ xs) ()

  module _ where
    open PB (_===_ {n}) using (_≈_) renaming (refl to ≈refl ; trans to ≈trans ; cong to ≈cong ; right-unit to ≈right-unit)

    private
      ≡⇒≈ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
      ≡⇒≈ refl = ≈refl
      lhs≡ : map (gen e4) (lhs (RT.tau-eqn τi τj τk τl)) ≡ Tl
      lhs≡ = trans (cong (map (gen e4)) (RT.tau-lhs τi τj τk τl))
        (cong (Kg ∷_) (trans (map-++ (gen e4) (mτ F.zero τi) _)
          (≡.cong₂ _++_ (map-mτ e4 F.zero τi) (trans (map-++ (gen e4) (mτ (F.suc F.zero) τj) _)
            (≡.cong₂ _++_ (map-mτ e4 (F.suc F.zero) τj) (trans (map-++ (gen e4) (mτ (F.suc (F.suc F.zero)) τk) _)
              (≡.cong₂ _++_ (map-mτ e4 (F.suc (F.suc F.zero)) τk) (map-mτ e4 (F.suc (F.suc (F.suc F.zero))) τl))))))))
      rhs≡ : map (gen e4) (rhs (RT.tau-eqn τi τj τk τl)) ≡ map (gen e4) (RT.tauS τi τj τk τl) ++ (Kg ∷ mτ i tsum)
      rhs≡ = trans (cong (map (gen e4)) (RT.tau-rhs τi τj τk τl))
               (trans (map-++ (gen e4) (RT.tauS τi τj τk τl) _) (cong (map (gen e4) (RT.tauS τi τj τk τl) ++_)
                 (cong (Kg ∷_) (map-mτ e4 F.zero tsum))))
      sylw : ∀ t → ⟪ Kg ∷ mτ i t ⟫ ≈ [ Kg ]ʷ • Mτ i t
      sylw true = ≈cong ≈refl ≈right-unit
      sylw false = ≈refl

    -- K (-1)^τ = S′ K (-1)_[i]^t.
    rel : Tw ≈ S′ • ([ Kg ]ʷ • Mτ i tsum)
    rel = ≈trans (≡⇒≈ (cong ⟪_⟫ (sym lhs≡)))
            (≈trans (prf (emb⁼ e4 (RT.tau-eqn τi τj τk τl)))
              (≈trans (≡⇒≈ (cong ⟪_⟫ rhs≡))
                (≈trans (⟪++⟫ (map (gen e4) (RT.tauS τi τj τk τl)) (Kg ∷ mτ i tsum)) (≈cong ≈refl (sylw tsum)))))

------------------------------------------------------------------------
-- K on four even entries

module EvenK (U : Vec ℤ n) {i j k l : Fin n} (ij : i < j) (jk : j < k) (kl : k < l) (ui uj uk ul : ℤ)
             (wi : U ! i ≡ + 2 ℤ.* ui) (wj : U ! j ≡ + 2 ℤ.* uj) (wk : U ! k ≡ + 2 ℤ.* uk) (wl : U ! l ≡ + 2 ℤ.* ul)
             (Σ0 : ((oddℤ ui xor oddℤ uj) xor oddℤ uk) xor oddℤ ul ≡ false) where

  private
    z+ : ∀ {x} {u} → x ≡ + 2 ℤ.* u → x ≡ + 0 ℤ.+ + 2 ℤ.* u
    z+ h = trans h (sym (Data.Integer.Properties.+-identityˡ _))
      where import Data.Integer.Properties

  open KH.Half U ij jk kl (+ 0) (+ 0) (+ 0) (+ 0) ui uj uk ul (z+ wi) (z+ wj) (z+ wk) (z+ wl)
               (+ 0) (+ 0) (+ 0) (+ 0) refl refl refl refl
    public using (Wh ; Wh-≢)
  private
    open KH.Half U ij jk kl (+ 0) (+ 0) (+ 0) (+ 0) ui uj uk ul (z+ wi) (z+ wj) (z+ wk) (z+ wl)
                 (+ 0) (+ 0) (+ 0) (+ 0) refl refl refl refl
      using (K-col ; Wh-a ; Wh-b ; Wh-c ; Wh-d ; odd-vA ; odd-vB ; odd-vC ; odd-vD)

  Kg : Gen n
  Kg = K-gen i j k l ij jk kl

  col-K : ∀ K → actV Kg (scV K U) ≡ scV K Wh
  col-K K = trans (actV-K i j k l ij jk kl K U) (K-col K)

  ev-i : Even (Wh ! i)
  ev-i = trans (cong oddℤ Wh-a) (trans odd-vA (cong (false xor_) Σ0))
  ev-j : Even (Wh ! j)
  ev-j = trans (cong oddℤ Wh-b) (trans odd-vB (cong (false xor_) Σ0))
  ev-k : Even (Wh ! k)
  ev-k = trans (cong oddℤ Wh-c) (trans odd-vC (cong (false xor_) Σ0))
  ev-l : Even (Wh ! l)
  ev-l = trans (cong oddℤ Wh-d) (trans odd-vD (cong (false xor_) Σ0))

------------------------------------------------------------------------
-- (-1)_[a] (-1)_[x] X_[a,x]

module Swap (U : Vec ℤ n) {a x : Fin n} (ax : a < x) where

  private
    a≢x : a ≢ x
    a≢x = <⇒≢ ax

  Sw : Word (Gen n)
  Sw = [ M-gen a ]ʷ • ([ M-gen x ]ʷ • [ X-gen a x ax ]ʷ)

  U′ : Vec ℤ n
  U′ = Mᶻ a (Mᶻ x (Xᶻ a x U))

  col-S : ∀ K → actVʷ Sw (scV K U) ≡ scV K U′
  col-S K = trans (cong (λ v → actV (M-gen a) (actV (M-gen x) v)) (actV-X a x ax K U))
              (trans (cong (actV (M-gen a)) (actV-M x K (Xᶻ a x U))) (actV-M a K (Mᶻ x (Xᶻ a x U))))

  U′-a : U′ ! a ≡ ℤ.- (U ! x)
  U′-a = trans (set₁-a a _ _) (cong ℤ.-_ (trans (set₁-≢ x _ _ a≢x) (set₂-a a x (U ! x) (U ! a) U)))

  U′-x : U′ ! x ≡ ℤ.- (U ! a)
  U′-x = trans (set₁-≢ a _ _ (λ e → a≢x (sym e))) (trans (set₁-a x _ _) (cong ℤ.-_ (set₂-b a x (U ! x) (U ! a) U a≢x)))

  U′-o : ∀ {y} → y ≢ a → y ≢ x → U′ ! y ≡ U ! y
  U′-o ya yx = trans (set₁-≢ a _ _ ya) (trans (set₁-≢ x _ _ yx) (set₂-≢ a x (U ! x) (U ! a) U ya yx))

-- EvenK as a function: using it projects fields, and does not apply the
-- module again.
record EvenKR (U : Vec ℤ n) (i j k l : Fin n) .(ij : i < j) .(jk : j < k) .(kl : k < l) : Set where
  field
    Wh    : Vec ℤ n
    col-K : ∀ K → actV (K-gen i j k l ij jk kl) (scV K U) ≡ scV K Wh
    ev-i  : Even (Wh ! i)
    ev-j  : Even (Wh ! j)
    ev-k  : Even (Wh ! k)
    ev-l  : Even (Wh ! l)
    Wh-≢  : ∀ {x} → x ≢ i → x ≢ j → x ≢ k → x ≢ l → Wh ! x ≡ U ! x

evenK : (U : Vec ℤ n) {i j k l : Fin n} (ij : i < j) (jk : j < k) (kl : k < l) (ui uj uk ul : ℤ) →
        U ! i ≡ + 2 ℤ.* ui → U ! j ≡ + 2 ℤ.* uj → U ! k ≡ + 2 ℤ.* uk → U ! l ≡ + 2 ℤ.* ul →
        ((oddℤ ui xor oddℤ uj) xor oddℤ uk) xor oddℤ ul ≡ false → EvenKR U i j k l ij jk kl
evenK U ij jk kl ui uj uk ul wi wj wk wl Σ0 = record
  { Wh = E.Wh ; col-K = E.col-K ; ev-i = E.ev-i ; ev-j = E.ev-j ; ev-k = E.ev-k ; ev-l = E.ev-l ; Wh-≢ = E.Wh-≢ }
  where module E = EvenK U ij jk kl ui uj uk ul wi wj wk wl Σ0

-- Swap as a function.
record SwapR (U : Vec ℤ n) (a x : Fin n) .(ax : a < x) : Set where
  field
    U′    : Vec ℤ n
    col-S : ∀ K → actVʷ ([ M-gen a ]ʷ • ([ M-gen x ]ʷ • [ X-gen a x ax ]ʷ)) (scV K U) ≡ scV K U′
    U′-a  : U′ ! a ≡ ℤ.- (U ! x)
    U′-x  : U′ ! x ≡ ℤ.- (U ! a)
    U′-o  : ∀ {y} → y ≢ a → y ≢ x → U′ ! y ≡ U ! y

swap : (U : Vec ℤ n) {a x : Fin n} (ax : a < x) → SwapR U a x ax
swap U ax = record { U′ = S.U′ ; col-S = S.col-S ; U′-a = S.U′-a ; U′-x = S.U′-x ; U′-o = S.U′-o }
  where module S = Swap U ax

------------------------------------------------------------------------
-- Tau as a function

-- The paper's syllable on i, j, k, l, with the signs of U.
τword : (U : Vec ℤ n) {i j k l : Fin n} .(ij : i < j) .(jk : j < k) .(kl : k < l) → Word (Gen n)
τword U {i} {j} {k} {l} ij jk kl =
  ⟪ K-gen i j k l ij jk kl ∷ (mτ i (τ (U ! i)) ++ (mτ j (τ (U ! j)) ++ (mτ k (τ (U ! k)) ++ mτ l (τ (U ! l))))) ⟫

module _ {n : ℕ} where
  open PB (_===_ {n}) using (_≈_)
  import Examples.Groups.CCX+HH-TwoLevel.States as St

  record TauR (U : Vec ℤ n) (i j k l : Fin n) .(ij : i < j) .(jk : j < k) .(kl : k < l) : Set where
    field
      Wh    : Vec ℤ n
      col-T : ∀ K → actVʷ (τword U ij jk kl) (scV K U) ≡ scV K Wh
      hA hB hC hD : ℤ
      Wh-i  : Wh ! i ≡ + 2 ℤ.* hA
      Wh-j  : Wh ! j ≡ + 2 ℤ.* hB
      Wh-k  : Wh ! k ≡ + 2 ℤ.* hC
      Wh-l  : Wh ! l ≡ + 2 ℤ.* hD
      Wh-o  : ∀ {x} → x ≢ i → x ≢ j → x ≢ k → x ≢ l → Wh ! x ≡ U ! x
      Σz    : Bool
      par-A : oddℤ hA ≡ not Σz
      par-B : oddℤ hB ≡ Σz
      par-C : oddℤ hC ≡ Σz
      par-D : oddℤ hD ≡ Σz
      -- The word of X's and (-1)'s.
      S′     : Word (Gen n)
      S′-mono : ∀ {p : Fin n} → i ≤ p → j ≤ p → k ≤ p → l ≤ p → St.MonoWord p S′
      rel   : τword U ij jk kl ≈ S′ • ([ K-gen i j k l ij jk kl ]ʷ • Mτ i (((τ (U ! i) xor τ (U ! j)) xor τ (U ! k)) xor τ (U ! l)))

  tau : (U : Vec ℤ n) {i j k l : Fin n} (ij : i < j) (jk : j < k) (kl : k < l) →
        Odd (U ! i) → Odd (U ! j) → Odd (U ! k) → Odd (U ! l) → TauR U i j k l ij jk kl
  tau U {i} {j} {k} {l} ij jk kl oi oj ok ol = record
    { Wh = T.Wh ; col-T = T.col-T ; hA = T.hA ; hB = T.hB ; hC = T.hC ; hD = T.hD
    ; Wh-i = T.Wh-i ; Wh-j = T.Wh-j ; Wh-k = T.Wh-k ; Wh-l = T.Wh-l ; Wh-o = T.Wh-o
    ; Σz = T.Σz ; par-A = T.par-A ; par-B = T.par-B ; par-C = T.par-C ; par-D = T.par-D
    ; S′ = T.S′ ; S′-mono = mono ; rel = T.rel }
    where
    module T = Tau U ij jk kl oi oj ok ol
    mono : ∀ {p : Fin n} → i ≤ p → j ≤ p → k ≤ p → l ≤ p → St.MonoWord p T.S′
    mono {p} hi hj hk hl = go (RT.tauS T.τi T.τj T.τk T.τl) (tauS-noK T.τi T.τj T.τk T.τl)
      where
      bnd : ∀ (z : Fin 4) → ι T.e4 z ≤ p
      bnd F.zero = hi
      bnd (F.suc F.zero) = hj
      bnd (F.suc (F.suc F.zero)) = hk
      bnd (F.suc (F.suc (F.suc F.zero))) = hl
      go : ∀ (xs : List (Gen 4)) → noK xs ≡ true → St.MonoWord p ⟪ map (gen T.e4) xs ⟫
      go [] _ = tt
      go (M-gen x ∷ xs) h = bnd x , go xs h
      go (X-gen x y q ∷ xs) h = bnd y , go xs h
      go (K-gen _ _ _ _ _ _ _ ∷ xs) ()

------------------------------------------------------------------------
-- The parity of z, for 1 + 4z = ±w

ζ : (w : ℤ) → Odd w → Bool
ζ w o = oddℤ (proj₁ (one4 w o))

-- It depends on w alone (Odd w is a proposition: Bool has decidable
-- equality).
ζ-irr : ∀ w (o o′ : Odd w) → ζ w o ≡ ζ w o′
ζ-irr w o o′ = cong (ζ w) (UIP.≡-irrelevant BoolP._≟_ o o′)
  where
  import Axiom.UniquenessOfIdentityProofs as UIPm
  module UIP = UIPm.Decidable⇒UIP
  import Data.Bool.Properties as BoolP

ζ-cong : ∀ {w w′} → w ≡ w′ → (o : Odd w) (o′ : Odd w′) → ζ w o ≡ ζ w′ o′
ζ-cong {w} refl o o′ = ζ-irr w o o′

-- The parity Σ of the syllable, in terms of ζ.
tau-Σz : ∀ {n} (U : Vec ℤ n) {i j k l : Fin n} (ij : i < j) (jk : j < k) (kl : k < l)
         (oi : Odd (U ! i)) (oj : Odd (U ! j)) (ok : Odd (U ! k)) (ol : Odd (U ! l)) →
         TauR.Σz (tau U ij jk kl oi oj ok ol) ≡ ((ζ (U ! i) oi xor ζ (U ! j) oj) xor ζ (U ! k) ok) xor ζ (U ! l) ol
tau-Σz U ij jk kl oi oj ok ol = refl

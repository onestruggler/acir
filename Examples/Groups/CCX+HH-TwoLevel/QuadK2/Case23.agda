------------------------------------------------------------------------
-- Presentations of groups
--
-- The edge K_[0,1,2,3] at a positive exponent when the first two odd
-- entries are a = 2 and b = 3 and the next ones lie beyond 3 (generated;
-- see QuadK2 for the argument).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; _<_ ; _≤_ ; toℕ)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Quantum.Synthesis.Matrix using (Matrix)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (col ; ColOrth ; actM)
open import Examples.Groups.CCX+HH-TwoLevel.Pivot using (pivot ; level)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (lde)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (K-gen)
import Examples.Groups.CCX+HH-TwoLevel.Reduction as R

module Examples.Groups.CCX+HH-TwoLevel.QuadK2.Case23 {n : ℕ}
  (s : Matrix n n D) .(o : ColOrth s) {p : Fin n} (ps : pivot s ≡ just p)
  {k′ : ℕ} (ks : lde (col s p) ≡ suc k′) (ih : R.EdgesBelow {n} (level s))
  {P0 P1 P2 P3 : Fin n} .(p01 : P0 < P1) .(p12 : P1 < P2) .(p23 : P2 < P3)
  (z0 : toℕ P0 ≡ 0) (z1 : toℕ P1 ≡ 1) (z2 : toℕ P2 ≡ 2) (z3 : toℕ P3 ≡ 3)
  (le : R._≤ₗ_ {n} (level (actM (K-gen P0 P1 P2 P3 p01 p12 p23) s)) (level s)) where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
import Data.Integer.Properties as ℤP
import Data.Integer.Solver as ℤSolver
open import Data.List.Base using (map)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)

open import Word.Base
import Presentation.Base as PB
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (oddℤ)
open import Examples.Groups.CCX+HH-TwoLevel.Lde using (scV ; Minimal ; Odd ; Even ; half)
open import Examples.Groups.CCX+HH-TwoLevel.Residue using (τ ; one2 ; τ-pair)
open import Examples.Groups.CCX+HH-TwoLevel.Column
open import Examples.Groups.CCX+HH-TwoLevel.ColumnAction using (p1ᶻ ; m1ᶻ)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (_!_)
open import Examples.Groups.CCX+HH-TwoLevel.Syllable using (syl)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (gen)
open import Examples.Groups.CCX+HH-TwoLevel.Engine using (⟪_⟫)
open R {n} using (Path)
import Examples.Groups.CCX+HH-TwoLevel.KHalf as KH
import Examples.Groups.CCX+HH-TwoLevel.Rel6 as R6

open import Examples.Groups.CCX+HH-TwoLevel.QuadK2Base s o ps ks ih p01 p12 p23 z0 z1 z2 z3 le

open PB (_===_ {n}) using (_≈_ ; refl ; sym ; trans ; cleft_ ; cright_)

private
  module ℤS = ℤSolver.+-*-Solver
  open ℤS using (_:+_ ; _:*_ ; _:=_ ; con)

  ≡⇒≈ : ∀ {w v : Word (Gen n)} → w ≡ v → w ≈ v
  ≡⇒≈ ≡.refl = refl

  -- Indices with different numbers differ.
  num≢ : ∀ {x y : Fin n} {i j} → toℕ x ≡ i → toℕ y ≡ j → i ≢ j → x ≢ y
  num≢ ex ey ij e = ij (≡.trans (≡.sym ex) (≡.trans (≡.cong toℕ e) ey))

  -- An index beyond 3 is none of 0..3.
  high≢ : ∀ {z x : Fin n} {i} → 3 ℕ.< toℕ z → toℕ x ≡ i → i ℕ.≤ 3 → z ≢ x
  high≢ h ex i3 e = ℕP.<⇒≱ h (≡.subst (ℕ._≤ 3) (≡.sym (≡.trans (≡.cong toℕ e) ex)) i3)

  -- The residues after K, from those before.
  bool-23-f : ∀ q0 q1 q2 q3 → ((q0 xor q1) xor q2) xor q3 ≡ false →
       not (false xor (q0 xor q1)) ≡ (q2 xor q3) xor true
  bool-23-f true true true true _ = ≡.refl
  bool-23-f true true true false ()
  bool-23-f true true false true ()
  bool-23-f true true false false _ = ≡.refl
  bool-23-f true false true true ()
  bool-23-f true false true false _ = ≡.refl
  bool-23-f true false false true _ = ≡.refl
  bool-23-f true false false false ()
  bool-23-f false true true true ()
  bool-23-f false true true false _ = ≡.refl
  bool-23-f false true false true _ = ≡.refl
  bool-23-f false true false false ()
  bool-23-f false false true true _ = ≡.refl
  bool-23-f false false true false ()
  bool-23-f false false false true ()
  bool-23-f false false false false _ = ≡.refl
  bool-23-t : ∀ q0 q1 q2 q3 → ((q0 xor q1) xor q2) xor q3 ≡ true →
       not (false xor (q0 xor q1)) ≡ (q2 xor q3) xor false
  bool-23-t true true true true ()
  bool-23-t true true true false _ = ≡.refl
  bool-23-t true true false true _ = ≡.refl
  bool-23-t true true false false ()
  bool-23-t true false true true _ = ≡.refl
  bool-23-t true false true false ()
  bool-23-t true false false true ()
  bool-23-t true false false false _ = ≡.refl
  bool-23-t false true true true _ = ≡.refl
  bool-23-t false true true false ()
  bool-23-t false true false true ()
  bool-23-t false true false false _ = ≡.refl
  bool-23-t false false true true ()
  bool-23-t false false true false _ = ≡.refl
  bool-23-t false false false true _ = ≡.refl
  bool-23-t false false false false ()

------------------------------------------------------------------------
-- The case

module _ (b3 : toℕ b ℕ.≤ 3) (c3 : 3 ℕ.< toℕ c) where

  open Count2 b3 c3

  case-23 : toℕ a ≡ 2 → toℕ b ≡ 3 → Path [ gK ]ʷ s o
  case-23 ea eb = byΣ Σu ≡.refl
    where
    a≡ : a ≡ P2
    a≡ = same ea z2
    b≡ : b ≡ P3
    b≡ = same eb z3
    oA : Odd (W ! P2)
    oA = ≡.subst (λ x → Odd (W ! x)) a≡ (proj₁ (firstOdd-spec W fo))
    oB : Odd (W ! P3)
    oB = ≡.subst (λ x → Odd (W ! x)) b≡ (proj₁ (proj₂ (nextOdd-spec W na)))
    e0 : Even (W ! P0)
    e0 = ev P0 (low<d (≤3 z0 (ℕ.z≤n))) (num≢ z0 ea (λ ())) (num≢ z0 eb (λ ())) (low≢c (≤3 z0 (ℕ.z≤n)))
    e1 : Even (W ! P1)
    e1 = ev P1 (low<d (≤3 z1 (ℕ.s≤s (ℕ.z≤n)))) (num≢ z1 ea (λ ())) (num≢ z1 eb (λ ())) (low≢c (≤3 z1 (ℕ.s≤s (ℕ.z≤n))))
    d0 = half (W ! P0) e0
    u0 : ℤ
    u0 = proj₁ d0
    w0 : W ! P0 ≡ + 0 ℤ.+ + 2 ℤ.* u0
    w0 = ≡.trans (proj₂ d0) (≡.sym (ℤP.+-identityˡ _))
    d1 = half (W ! P1) e1
    u1 : ℤ
    u1 = proj₁ d1
    w1 : W ! P1 ≡ + 0 ℤ.+ + 2 ℤ.* u1
    w1 = ≡.trans (proj₂ d1) (≡.sym (ℤP.+-identityˡ _))
    d2 = one2 (W ! P2) oA
    u2 : ℤ
    u2 = proj₁ d2
    w2 : W ! P2 ≡ + 1 ℤ.+ + 2 ℤ.* u2
    w2 = proj₁ (proj₂ d2)
    d3 = one2 (W ! P3) oB
    u3 : ℤ
    u3 = proj₁ d3
    w3 : W ! P3 ≡ + 1 ℤ.+ + 2 ℤ.* u3
    w3 = proj₁ (proj₂ d3)
    τa : τ (W ! a) ≡ oddℤ u2
    τa = ≡.trans (≡.cong (λ q → τ (W ! q)) a≡) (≡.sym (proj₂ (proj₂ d2)))
    τb : τ (W ! b) ≡ oddℤ u3
    τb = ≡.trans (≡.cong (λ q → τ (W ! q)) b≡) (≡.sym (proj₂ (proj₂ d3)))
    open KH.Half W p01 p12 p23 (+ 0) (+ 0) (+ 1) (+ 1) u0 u1 u2 u3 w0 w1 w2 w3 (+ 1) (+ 0) (-[1+ 0 ]) (+ 0) ≡.refl ≡.refl ≡.refl ≡.refl
    agree : ∀ z → 3 ℕ.< toℕ z → oddℤ (Wh ! z) ≡ oddℤ (W ! z)
    agree z h = ≡.cong oddℤ (Wh-≢ (high≢ h z0 (ℕ.z≤n)) (high≢ h z1 (ℕ.s≤s (ℕ.z≤n))) (high≢ h z2 (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n)))) (high≢ h z3 (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n))))))
    Whc : Wh ! c ≡ W ! c
    Whc = Wh-≢ (λ e → low≢c (≤3 z0 (ℕ.z≤n)) (≡.sym e)) (λ e → low≢c (≤3 z1 (ℕ.s≤s (ℕ.z≤n))) (≡.sym e)) (λ e → low≢c (≤3 z2 (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n)))) (≡.sym e)) (λ e → low≢c (≤3 z3 (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n))))) (≡.sym e))
    Whd : Wh ! d ≡ W ! d
    Whd = Wh-≢ (λ e → low≢d (≤3 z0 (ℕ.z≤n)) (≡.sym e)) (λ e → low≢d (≤3 z1 (ℕ.s≤s (ℕ.z≤n))) (≡.sym e)) (λ e → low≢d (≤3 z2 (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n)))) (≡.sym e)) (λ e → low≢d (≤3 z3 (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n))))) (≡.sym e))
    eq′ : col gs p ≡ scV K′ Wh
    eq′ = ≡.trans colKP (K-col K′)
    mn′ : Minimal K′ Wh
    mn′ = inj₂ (c , ≡.trans (agree c c3) (proj₁ (proj₂ (nextOdd-spec W nb))))
    open After Wh eq′ mn′
    byΣ : (σ : Bool) → Σu ≡ σ → Path [ gK ]ʷ s o
    byΣ false hσ = byt t ≡.refl
      where
      o0 : oddℤ (Wh ! P0) ≡ true
      o0 = ≡.trans (≡.cong oddℤ Wh-a) (≡.trans odd-vA (≡.cong (oddℤ (+ 1) xor_) hσ))
      o1 : oddℤ (Wh ! P1) ≡ false
      o1 = ≡.trans (≡.cong oddℤ Wh-b) (≡.trans odd-vB (≡.cong (oddℤ (+ 0) xor_) hσ))
      o2 : oddℤ (Wh ! P2) ≡ true
      o2 = ≡.trans (≡.cong oddℤ Wh-c) (≡.trans odd-vC (≡.cong (oddℤ (-[1+ 0 ]) xor_) hσ))
      o3 : oddℤ (Wh ! P3) ≡ false
      o3 = ≡.trans (≡.cong oddℤ Wh-d) (≡.trans odd-vD (≡.cong (oddℤ (+ 0) xor_) hσ))
      evl : ∀ z → toℕ z ℕ.≤ 3 → z ≢ P0 → z ≢ P2 → Even (Wh ! z)
      evl z h zx zy = go (onP z h)
        where
        go : z ≡ P0 ⊎ z ≡ P1 ⊎ z ≡ P2 ⊎ z ≡ P3 → Even (Wh ! z)
        go (inj₁ e) = ⊥-elim (zx e)
        go (inj₂ (inj₁ e)) = ≡.subst (λ q → Even (Wh ! q)) (≡.sym e) o1
        go (inj₂ (inj₂ (inj₁ e))) = ⊥-elim (zy e)
        go (inj₂ (inj₂ (inj₂ e))) = ≡.subst (λ q → Even (Wh ! q)) (≡.sym e) o3
      xy : P0 < P2
      xy = ≡.subst₂ ℕ._<_ (≡.sym z0) (≡.sym z2) (ℕ.s≤s (ℕ.z≤n))
      y3 : toℕ P2 ℕ.≤ 3
      y3 = ≤3 z2 (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n)))
      open Chain Wh agree xy y3 o0 o2 evl
      N′≡ : sylData p K′ Wh ≡ K P0 P2 c d xy (low<c y3) c<d • Mτ P0 (σ₄ Wh P0 P2 c d)
      N′≡ = sylData-quad {p = p} k′ Wh fo′ na′ nb′ nc′ xy (low<c y3) c<d
      m : ℤ
      m = (+ 0) ℤ.+ (p1ᶻ ℤ.* u0 ℤ.+ p1ᶻ ℤ.* u1)
      sum : vA ℤ.+ vC ≡ + 2 ℤ.* m
      sum = ℤS.solve 4 (λ u0 u1 u2 u3 → (con (+ 1) :+ (con p1ᶻ :* u0 :+ con p1ᶻ :* u1 :+ con p1ᶻ :* u2 :+ con p1ᶻ :* u3)) :+ (con (-[1+ 0 ]) :+ (con p1ᶻ :* u0 :+ con p1ᶻ :* u1 :+ con m1ᶻ :* u2 :+ con m1ᶻ :* u3)) := con (+ 2) :* (con (+ 0) :+ (con p1ᶻ :* u0 :+ con p1ᶻ :* u1))) ≡.refl u0 u1 u2 u3
      A≡ : τ (Wh ! P0) xor τ (Wh ! P2) ≡ (τ (W ! a) xor τ (W ! b)) xor true
      A≡ = ≡.trans (≡.cong₂ (λ q r → τ q xor τ r) Wh-a Wh-c)
             (≡.trans (τ-pair vA vC m (≡.trans (≡.sym (≡.cong oddℤ Wh-a)) o0) (≡.trans (≡.sym (≡.cong oddℤ Wh-c)) o2) sum)
               (≡.trans (≡.cong not (odd-lin2 (+ 0) p1ᶻ p1ᶻ u0 u1 ≡.refl ≡.refl))
                 (≡.trans (bool-23-f (oddℤ u0) (oddℤ u1) (oddℤ u2) (oddℤ u3) hσ)
                   (≡.cong (_xor true) (≡.sym (≡.cong₂ _xor_ τa τb))))))
      t₂≡ : σ₄ Wh P0 P2 c d ≡ t xor true
      t₂≡ = ≡.trans (≡.cong₂ (λ q r → ((τ (Wh ! P0) xor τ (Wh ! P2)) xor τ q) xor τ r) Whc Whd)
                    (shift4 {A = τ (Wh ! P0) xor τ (Wh ! P2)} {B = τ (W ! a) xor τ (W ! b)} true (τ (W ! c)) (τ (W ! d)) A≡)
      byt : (tv : Bool) → t ≡ tv → Path [ gK ]ʷ s o
      byt false ht = sandwich gK (sylData p K′ Wh) ⟪ map (gen eQ) R6.cfg-23-f-f-V₁ ⟫ ⟪ map (gen eQ) R6.cfg-23-f-f-V₂ ⟫ pN′ lN′
        (mono-emb R6.cfg-23-f-f-V₁ ≡.refl) (mono-emb R6.cfg-23-f-f-V₂ ≡.refl) rel
        where
        Nsyl : syl s ≡ K P2 P3 c d (≡.subst₂ (λ q r → q < r) a≡ b≡ a<b) (≡.subst (_< c) b≡ b<c) c<d • Mτ P2 false
        Nsyl = ≡.trans N≡ (≡.cong₂ _•_ (K≡ a≡ b≡ ≡.refl ≡.refl) (≡.cong₂ Mτ a≡ ht))
        N′syl : sylData p K′ Wh ≡ K P0 P2 c d xy (low<c y3) c<d • Mτ P0 true
        N′syl = ≡.trans N′≡ (≡.cong (λ q → K P0 P2 c d xy (low<c y3) c<d • Mτ P0 q) (≡.trans t₂≡ (≡.cong (_xor true) ht)))
        rel : (⟪ map (gen eQ) R6.cfg-23-f-f-V₁ ⟫ • ([ gK ]ʷ • ⟪ map (gen eQ) R6.cfg-23-f-f-V₂ ⟫)) • syl s ≈ sylData p K′ Wh • [ gK ]ʷ
        rel = trans (cright (trans (≡⇒≈ Nsyl) (sym (syl-list _ P2 false))))
                (trans (cfg-rel R6.cfg-23-f-f R6.cfg-23-f-f-N′ R6.cfg-23-f-f-V₁ R6.cfg-23-f-f-V₂ R6.cfg-23-f-f-N ≡.refl ≡.refl)
                  (cleft (trans (syl-list _ P0 true) (≡⇒≈ (≡.sym N′syl)))))
      byt true ht = sandwich gK (sylData p K′ Wh) ⟪ map (gen eQ) R6.cfg-23-f-t-V₁ ⟫ ⟪ map (gen eQ) R6.cfg-23-f-t-V₂ ⟫ pN′ lN′
        (mono-emb R6.cfg-23-f-t-V₁ ≡.refl) (mono-emb R6.cfg-23-f-t-V₂ ≡.refl) rel
        where
        Nsyl : syl s ≡ K P2 P3 c d (≡.subst₂ (λ q r → q < r) a≡ b≡ a<b) (≡.subst (_< c) b≡ b<c) c<d • Mτ P2 true
        Nsyl = ≡.trans N≡ (≡.cong₂ _•_ (K≡ a≡ b≡ ≡.refl ≡.refl) (≡.cong₂ Mτ a≡ ht))
        N′syl : sylData p K′ Wh ≡ K P0 P2 c d xy (low<c y3) c<d • Mτ P0 false
        N′syl = ≡.trans N′≡ (≡.cong (λ q → K P0 P2 c d xy (low<c y3) c<d • Mτ P0 q) (≡.trans t₂≡ (≡.cong (_xor true) ht)))
        rel : (⟪ map (gen eQ) R6.cfg-23-f-t-V₁ ⟫ • ([ gK ]ʷ • ⟪ map (gen eQ) R6.cfg-23-f-t-V₂ ⟫)) • syl s ≈ sylData p K′ Wh • [ gK ]ʷ
        rel = trans (cright (trans (≡⇒≈ Nsyl) (sym (syl-list _ P2 true))))
                (trans (cfg-rel R6.cfg-23-f-t R6.cfg-23-f-t-N′ R6.cfg-23-f-t-V₁ R6.cfg-23-f-t-V₂ R6.cfg-23-f-t-N ≡.refl ≡.refl)
                  (cleft (trans (syl-list _ P0 false) (≡⇒≈ (≡.sym N′syl)))))
    byΣ true hσ = byt t ≡.refl
      where
      o0 : oddℤ (Wh ! P0) ≡ false
      o0 = ≡.trans (≡.cong oddℤ Wh-a) (≡.trans odd-vA (≡.cong (oddℤ (+ 1) xor_) hσ))
      o1 : oddℤ (Wh ! P1) ≡ true
      o1 = ≡.trans (≡.cong oddℤ Wh-b) (≡.trans odd-vB (≡.cong (oddℤ (+ 0) xor_) hσ))
      o2 : oddℤ (Wh ! P2) ≡ false
      o2 = ≡.trans (≡.cong oddℤ Wh-c) (≡.trans odd-vC (≡.cong (oddℤ (-[1+ 0 ]) xor_) hσ))
      o3 : oddℤ (Wh ! P3) ≡ true
      o3 = ≡.trans (≡.cong oddℤ Wh-d) (≡.trans odd-vD (≡.cong (oddℤ (+ 0) xor_) hσ))
      evl : ∀ z → toℕ z ℕ.≤ 3 → z ≢ P1 → z ≢ P3 → Even (Wh ! z)
      evl z h zx zy = go (onP z h)
        where
        go : z ≡ P0 ⊎ z ≡ P1 ⊎ z ≡ P2 ⊎ z ≡ P3 → Even (Wh ! z)
        go (inj₁ e) = ≡.subst (λ q → Even (Wh ! q)) (≡.sym e) o0
        go (inj₂ (inj₁ e)) = ⊥-elim (zx e)
        go (inj₂ (inj₂ (inj₁ e))) = ≡.subst (λ q → Even (Wh ! q)) (≡.sym e) o2
        go (inj₂ (inj₂ (inj₂ e))) = ⊥-elim (zy e)
      xy : P1 < P3
      xy = ≡.subst₂ ℕ._<_ (≡.sym z1) (≡.sym z3) (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n)))
      y3 : toℕ P3 ℕ.≤ 3
      y3 = ≤3 z3 (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n))))
      open Chain Wh agree xy y3 o1 o3 evl
      N′≡ : sylData p K′ Wh ≡ K P1 P3 c d xy (low<c y3) c<d • Mτ P1 (σ₄ Wh P1 P3 c d)
      N′≡ = sylData-quad {p = p} k′ Wh fo′ na′ nb′ nc′ xy (low<c y3) c<d
      m : ℤ
      m = (+ 0) ℤ.+ (p1ᶻ ℤ.* u0 ℤ.+ m1ᶻ ℤ.* u1)
      sum : vB ℤ.+ vD ≡ + 2 ℤ.* m
      sum = ℤS.solve 4 (λ u0 u1 u2 u3 → (con (+ 0) :+ (con p1ᶻ :* u0 :+ con m1ᶻ :* u1 :+ con p1ᶻ :* u2 :+ con m1ᶻ :* u3)) :+ (con (+ 0) :+ (con p1ᶻ :* u0 :+ con m1ᶻ :* u1 :+ con m1ᶻ :* u2 :+ con p1ᶻ :* u3)) := con (+ 2) :* (con (+ 0) :+ (con p1ᶻ :* u0 :+ con m1ᶻ :* u1))) ≡.refl u0 u1 u2 u3
      A≡ : τ (Wh ! P1) xor τ (Wh ! P3) ≡ (τ (W ! a) xor τ (W ! b)) xor false
      A≡ = ≡.trans (≡.cong₂ (λ q r → τ q xor τ r) Wh-b Wh-d)
             (≡.trans (τ-pair vB vD m (≡.trans (≡.sym (≡.cong oddℤ Wh-b)) o1) (≡.trans (≡.sym (≡.cong oddℤ Wh-d)) o3) sum)
               (≡.trans (≡.cong not (odd-lin2 (+ 0) p1ᶻ m1ᶻ u0 u1 ≡.refl ≡.refl))
                 (≡.trans (bool-23-t (oddℤ u0) (oddℤ u1) (oddℤ u2) (oddℤ u3) hσ)
                   (≡.cong (_xor false) (≡.sym (≡.cong₂ _xor_ τa τb))))))
      t₂≡ : σ₄ Wh P1 P3 c d ≡ t xor false
      t₂≡ = ≡.trans (≡.cong₂ (λ q r → ((τ (Wh ! P1) xor τ (Wh ! P3)) xor τ q) xor τ r) Whc Whd)
                    (shift4 {A = τ (Wh ! P1) xor τ (Wh ! P3)} {B = τ (W ! a) xor τ (W ! b)} false (τ (W ! c)) (τ (W ! d)) A≡)
      byt : (tv : Bool) → t ≡ tv → Path [ gK ]ʷ s o
      byt false ht = sandwich gK (sylData p K′ Wh) ⟪ map (gen eQ) R6.cfg-23-t-f-V₁ ⟫ ⟪ map (gen eQ) R6.cfg-23-t-f-V₂ ⟫ pN′ lN′
        (mono-emb R6.cfg-23-t-f-V₁ ≡.refl) (mono-emb R6.cfg-23-t-f-V₂ ≡.refl) rel
        where
        Nsyl : syl s ≡ K P2 P3 c d (≡.subst₂ (λ q r → q < r) a≡ b≡ a<b) (≡.subst (_< c) b≡ b<c) c<d • Mτ P2 false
        Nsyl = ≡.trans N≡ (≡.cong₂ _•_ (K≡ a≡ b≡ ≡.refl ≡.refl) (≡.cong₂ Mτ a≡ ht))
        N′syl : sylData p K′ Wh ≡ K P1 P3 c d xy (low<c y3) c<d • Mτ P1 false
        N′syl = ≡.trans N′≡ (≡.cong (λ q → K P1 P3 c d xy (low<c y3) c<d • Mτ P1 q) (≡.trans t₂≡ (≡.cong (_xor false) ht)))
        rel : (⟪ map (gen eQ) R6.cfg-23-t-f-V₁ ⟫ • ([ gK ]ʷ • ⟪ map (gen eQ) R6.cfg-23-t-f-V₂ ⟫)) • syl s ≈ sylData p K′ Wh • [ gK ]ʷ
        rel = trans (cright (trans (≡⇒≈ Nsyl) (sym (syl-list _ P2 false))))
                (trans (cfg-rel R6.cfg-23-t-f R6.cfg-23-t-f-N′ R6.cfg-23-t-f-V₁ R6.cfg-23-t-f-V₂ R6.cfg-23-t-f-N ≡.refl ≡.refl)
                  (cleft (trans (syl-list _ P1 false) (≡⇒≈ (≡.sym N′syl)))))
      byt true ht = sandwich gK (sylData p K′ Wh) ⟪ map (gen eQ) R6.cfg-23-t-t-V₁ ⟫ ⟪ map (gen eQ) R6.cfg-23-t-t-V₂ ⟫ pN′ lN′
        (mono-emb R6.cfg-23-t-t-V₁ ≡.refl) (mono-emb R6.cfg-23-t-t-V₂ ≡.refl) rel
        where
        Nsyl : syl s ≡ K P2 P3 c d (≡.subst₂ (λ q r → q < r) a≡ b≡ a<b) (≡.subst (_< c) b≡ b<c) c<d • Mτ P2 true
        Nsyl = ≡.trans N≡ (≡.cong₂ _•_ (K≡ a≡ b≡ ≡.refl ≡.refl) (≡.cong₂ Mτ a≡ ht))
        N′syl : sylData p K′ Wh ≡ K P1 P3 c d xy (low<c y3) c<d • Mτ P1 true
        N′syl = ≡.trans N′≡ (≡.cong (λ q → K P1 P3 c d xy (low<c y3) c<d • Mτ P1 q) (≡.trans t₂≡ (≡.cong (_xor false) ht)))
        rel : (⟪ map (gen eQ) R6.cfg-23-t-t-V₁ ⟫ • ([ gK ]ʷ • ⟪ map (gen eQ) R6.cfg-23-t-t-V₂ ⟫)) • syl s ≈ sylData p K′ Wh • [ gK ]ʷ
        rel = trans (cright (trans (≡⇒≈ Nsyl) (sym (syl-list _ P2 true))))
                (trans (cfg-rel R6.cfg-23-t-t R6.cfg-23-t-t-N′ R6.cfg-23-t-t-V₁ R6.cfg-23-t-t-V₂ R6.cfg-23-t-t-N ≡.refl ≡.refl)
                  (cleft (trans (syl-list _ P1 true) (≡⇒≈ (≡.sym N′syl)))))

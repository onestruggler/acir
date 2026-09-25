------------------------------------------------------------------------
-- Presentations of groups
--
-- Carrying a Hadamard-free word across a Hadamard pair
--
-- Figure 10's (68), (69), (76) and (77) all move a mixed letter past
-- `H_[a,b] H_[c,d]`, renaming the pair's indices by the letter's own
-- exchange.  The paper proves each the same way: Corollary A.5 appends
-- the letter's inverse, (65) writes the pair around the standard one,
-- Corollary A.7 absorbs the letter into Definition E.1's word, and
-- (65) reads the result back.
--
-- That argument does not depend on the word being a letter, so it is
-- here once and for all: **a Hadamard-free word with an inverse
-- carries a pair onto the pair on the pre-images of its four indices,
-- as long as its signs agree along each of those two pre-image
-- pairs.**  `Conjugate.Pull.conj-pair` is the matrix half; everything
-- else is (65) at the two tuples with A.7 between them.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Move (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; _xor_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Nat renaming (_^_ to _^ℕ_ ; _+_ to _+ℕ_) using ()
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray
  using (code ; index ; index-code)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (hadOp)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Encoding using (hh ; zz ; zx ; xx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SigmaPerm m
  using (zx-prm ; zx-sgn ; hfree-zx ; zx-pair)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (HFreeʷ ; cat ; nil ; gen ; hf-xx ; gen-xx ; hf-zz)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (sp ; sgn ; prm ; sp-inj ; idSP ; SP ; Inj ; ⊙-inverse
       ; SWP ; SWP-invol ; SWP-conj ; swp≡ ; sp-xx ; eqv ; δ ; δ-here ; δ-≢
       ; xor-self
       ; swapF ; swapF-a ; swapF-b ; swapF-o)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_ ; ≐-refl to ≐-refl′ ; ≐-sym to ≐-sym′
          ; ≐-trans to ≐-trans′ ; ⊙-cong to ⊙-cong′ ; ⊙-assoc to ⊙-assoc′
          ; ⊙-idˡ to ⊙-idˡ′ ; prm≡ to prm≡′ ; sgn≡ to sgn≡′)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SPMatrix m
  using (spOp ; spOp-⊙ ; spOp-id ; spOp-cong ; word-op ; word-scale ; ⟦_⟧ʷ
       ; A5-mat)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Conjugate m
  using (module Conj ; module Pull)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Passes m using (Λ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.A6 m
  using (Mpair ; Λ-op ; Λ-scale)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.A7 m using (A7)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq65 m as E65 using (Pair)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m using (Eq65)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

open Tools (m P,_===_)

private
  n : ℕ
  n = ₃₊ m

  N : ℕ
  N = 2 ^ℕ n

  W : Set
  W = Word (GenP (₃₊ m))

  ≢sym : ∀ {x y : Fin N} → x ≢ y → y ≢ x
  ≢sym ne e = ne (Eq.sym e)

------------------------------------------------------------------------
-- The matrix half
--
-- `A6.conj-at` is this at the standard pair; here the target is the
-- pair on any four indices.

pull-pair : ∀ (X X′ : W) → Inj (sp X′) → sp X ⊛ sp X′ ≗ idSP →
            ∀ (p q r s p′ q′ r′ s′ : Fin N) →
            prm (sp X) p ≡ p′ → prm (sp X) q ≡ q′ →
            prm (sp X) r ≡ r′ → prm (sp X) s ≡ s′ →
            sgn (sp X) p ≡ sgn (sp X) q → sgn (sp X) r ≡ sgn (sp X) s →
            (spOp (sp X) ⊙ (Pair p′ q′ r′ s′ ⊙ spOp (sp X′))) ≐ Pair p q r s
pull-pair X X′ inj inv p q r s p′ q′ r′ s′ ep eq er es spq srs =
  Eq.subst (λ M → (spOp (sp X) ⊙ (M ⊙ spOp (sp X′))) ≐ Pair p q r s)
           frame
           (conj-pair (code n p) (code n q) (code n r) (code n s)
                      (Eq.trans (sg p) (Eq.trans spq (Eq.sym (sg q))))
                      (Eq.trans (sg r) (Eq.trans srs (Eq.sym (sg s)))))
  where
  open Conj (sp X) (sp X′) inj inv using (π ; σ)
  open Pull (sp X) (sp X′) inj inv using (conj-pair)

  imgOf : ∀ (x k : Fin N) → prm (sp X) x ≡ k → π (code n x) ≡ code n k
  imgOf x k h = Eq.cong (code n) (Eq.trans (Eq.cong (prm (sp X)) (index-code n x)) h)

  sg : ∀ (x : Fin N) → σ (code n x) ≡ sgn (sp X) x
  sg x = Eq.cong (sgn (sp X)) (index-code n x)

  frame : (hadOp (π (code n p)) (π (code n q))
           ⊙ hadOp (π (code n r)) (π (code n s))) ≡ Pair p′ q′ r′ s′
  frame =
    Eq.trans (Eq.cong₂ (λ u v → hadOp u v ⊙ hadOp (π (code n r)) (π (code n s)))
                       (imgOf p p′ ep) (imgOf q q′ eq))
             (Eq.cong₂ (λ u v → hadOp (code n p′) (code n q′) ⊙ hadOp u v)
                       (imgOf r r′ er) (imgOf s s′ es))

------------------------------------------------------------------------
-- The re-bracketing, over abstract operators
--
-- With the matrices in place the conversion checker expands every `⊙`
-- into its sum over bitstrings, and a five-fold product exhausts
-- memory — the same trap `A7.comm-lemma` is stated around.

reassoc : ∀ (U S M S′ U′ : Op n) →
          ((U ⊙ S) ⊙ (M ⊙ (S′ ⊙ U′))) ≐ (U ⊙ ((S ⊙ (M ⊙ S′)) ⊙ U′))
reassoc U S M S′ U′ =
  ≐-trans (⊙-assoc U S (M ⊙ (S′ ⊙ U′)))
          (⊙-cong (≐-refl U)
            (≐-trans (⊙-cong (≐-refl S) (≐-sym (⊙-assoc M S′ U′)))
                     (≐-sym (⊙-assoc S (M ⊙ S′) U′))))

------------------------------------------------------------------------
-- Moving a word across a pair

module _ (e65 : Eq65) where

  private
    -- Words that pair off cancel through the middle.
    peel : ∀ (F A B G : SP) → (A ⊛ B) ≗ idSP → (F ⊛ G) ≗ idSP →
           (F ⊛ A) ⊛ (B ⊛ G) ≗ idSP
    peel F A B G e e′ =
      ≐-trans′ (⊙-assoc′ F A (B ⊛ G))
      (≐-trans′ (⊙-cong′ (≐-refl′ {F})
                  (≐-trans′ (≐-trans′ (≐-sym′ (⊙-assoc′ A B G))
                                      (⊙-cong′ e (≐-refl′ {G})))
                            (⊙-idˡ′ G)))
                e′)

    inv-of : ∀ {X X′ : W} → HFreeʷ X → HFreeʷ X′ → sp X ⊛ sp X′ ≗ idSP →
             ⟦ X • X′ ⟧ʷ ~ ⟦ ε ⟧ʷ
    inv-of {X} {X′} hX hX′ e =
      ~-reflexive (Eq.cong₂ _+ℕ_ (word-scale hX) (word-scale hX′))
        (≐-trans (⊙-cong (word-op hX) (word-op hX′))
          (≐-trans (≐-sym (spOp-⊙ (sp X) (sp X′)))
                   (≐-trans (spOp-cong e) spOp-id)))

    -- Scale and matrix of `X Λ X′`, separately.
    cs : ∀ {X X′ : W} → HFreeʷ X → HFreeʷ X′ → proj₁ ⟦ X • (Λ • X′) ⟧ʷ ≡ 2
    cs hX hX′ =
      Eq.cong₂ _+ℕ_ (word-scale hX) (Eq.cong₂ _+ℕ_ Λ-scale (word-scale hX′))

    co : ∀ {X X′ : W} → HFreeʷ X → HFreeʷ X′ →
         proj₂ ⟦ X • (Λ • X′) ⟧ʷ ≐ (spOp (sp X) ⊙ (Mpair ⊙ spOp (sp X′)))
    co hX hX′ = ⊙-cong (word-op hX) (⊙-cong Λ-op (word-op hX′))

    same : ∀ {X X′ Y Y′ : W} (M : Op n) →
           HFreeʷ X → HFreeʷ X′ → HFreeʷ Y → HFreeʷ Y′ →
           (spOp (sp X) ⊙ (Mpair ⊙ spOp (sp X′))) ≐ M →
           (spOp (sp Y) ⊙ (Mpair ⊙ spOp (sp Y′))) ≐ M →
           ⟦ X • (Λ • X′) ⟧ʷ ~ ⟦ Y • (Λ • Y′) ⟧ʷ
    same M hX hX′ hY hY′ eX eY =
      ~-reflexive (Eq.trans (cs hX hX′) (Eq.sym (cs hY hY′)))
                  (≐-trans (co hX hX′) (≐-trans eX (≐-trans (≐-sym eY)
                                                            (≐-sym (co hY hY′)))))

  -- A Hadamard-free word with an inverse carries a pair onto the pair
  -- on the pre-images of its four indices.
  hh-conj : ∀ (u u′ : W) → HFreeʷ u → HFreeʷ u′ → sp u ⊛ sp u′ ≗ idSP →
            ∀ (p q r s p′ q′ r′ s′ : Fin N) →
            prm (sp u) p ≡ p′ → prm (sp u) q ≡ q′ →
            prm (sp u) r ≡ r′ → prm (sp u) s ≡ s′ →
            sgn (sp u) p ≡ sgn (sp u) q → sgn (sp u) r ≡ sgn (sp u) s →
            p ≢ q → p ≢ r → p ≢ s → q ≢ r → q ≢ s → r ≢ s →
            u • (hh {₃₊ m} p′ q′ r′ s′ • u′) ≈ hh {₃₊ m} p q r s
  hh-conj u u′ hu hu′ inv p q r s p′ q′ r′ s′ ep eq er es spq srs
          pq pr ps qr qs rs =
    trans (back u (front u′ (e65 p′ q′ r′ s′ p′q′ p′r′ p′s′ q′r′ q′s′ r′s′)))
    (trans (refl≡ Eq.refl)
    (trans shape
    (trans join (sym (e65 p q r s pq pr ps qr qs rs)))))
    where
    -- The primed indices differ too, `prm` being injective.
    prim : ∀ {x y : Fin N} {x′ y′ : Fin N} → prm (sp u) x ≡ x′ →
         prm (sp u) y ≡ y′ → x ≢ y → x′ ≢ y′
    prim {x} {y} ex ey ne h =
      ne (sp-inj u (Eq.trans ex (Eq.trans h (Eq.sym ey))))

    p′q′ : p′ ≢ q′
    p′q′ = prim ep eq pq

    p′r′ : p′ ≢ r′
    p′r′ = prim ep er pr

    p′s′ : p′ ≢ s′
    p′s′ = prim ep es ps

    q′r′ : q′ ≢ r′
    q′r′ = prim eq er qr

    q′s′ : q′ ≢ s′
    q′s′ = prim eq es qs

    r′s′ : r′ ≢ s′
    r′s′ = prim er es rs

    module T = E65.Tuple p′ q′ r′ s′ p′q′ p′r′ p′s′ q′r′ q′s′ r′s′
    module T₂ = E65.Tuple p q r s pq pr ps qr qs rs

    -- The two halves, and that they are inverse.
    A A′ : W
    A  = u • T.Σw
    A′ = T.Σ′w • u′

    hA : HFreeʷ A
    hA = cat hu T.hfree-Σ

    hA′ : HFreeʷ A′
    hA′ = cat T.hfree-Σ′ hu′

    invA : sp A ⊛ sp A′ ≗ idSP
    invA = peel (sp u) (sp T.Σw) (sp T.Σ′w) (sp u′) T.Σ-inv inv

    -- Re-bracketing the two conjugating words around the pair.
    shape : u • ((T.Σw • (Λ • T.Σ′w)) • u′) ≈ A • (Λ • A′)
    shape = begin
      u • ((T.Σw • (Λ • T.Σ′w)) • u′)
        ≈⟨ back u assoc ⟩
      u • (T.Σw • ((Λ • T.Σ′w) • u′))
        ≈⟨ back u (back T.Σw assoc) ⟩
      u • (T.Σw • (Λ • (T.Σ′w • u′)))
        ≈⟨ sym assoc ⟩
      (u • T.Σw) • (Λ • (T.Σ′w • u′)) ∎

    -- And the matrix it denotes is the pair on the pre-images.
    conj : (spOp (sp A) ⊙ (Mpair ⊙ spOp (sp A′))) ≐ Pair p q r s
    conj =
      ≐-trans (⊙-cong (spOp-⊙ (sp u) (sp T.Σw))
                      (⊙-cong (≐-refl Mpair) (spOp-⊙ (sp T.Σ′w) (sp u′))))
      (≐-trans (reassoc (spOp (sp u)) (spOp (sp T.Σw)) Mpair
                        (spOp (sp T.Σ′w)) (spOp (sp u′)))
      (≐-trans (⊙-cong (≐-refl (spOp (sp u)))
                       (⊙-cong T.Σ-conj (≐-refl (spOp (sp u′)))))
               (pull-pair u u′ (sp-inj u′) inv p q r s p′ q′ r′ s′
                          ep eq er es spq srs)))

    sem : ⟦ A • (Λ • A′) ⟧ʷ ~ ⟦ T₂.Σw • (Λ • T₂.Σ′w) ⟧ʷ
    sem = same (Pair p q r s) hA hA′ T₂.hfree-Σ T₂.hfree-Σ′ conj T₂.Σ-conj

    invAA′ : ⟦ A • A′ ⟧ʷ ~ ⟦ ε ⟧ʷ
    invAA′ = inv-of hA hA′ invA

    join : A • (Λ • A′) ≈ T₂.Σw • (Λ • T₂.Σ′w)
    join = A7 hA hA′ T₂.hfree-Σ T₂.hfree-Σ′ invAA′ T₂.ΣΣ′ sem

    refl≡ : ∀ {x y : W} → x ≡ y → x ≈ y
    refl≡ Eq.refl = refl

  -- So such a word *passes* the pair, renaming its four indices.
  hh-pass : ∀ (u u′ : W) → HFreeʷ u → HFreeʷ u′ → sp u ⊛ sp u′ ≗ idSP →
            ∀ (p q r s p′ q′ r′ s′ : Fin N) →
            prm (sp u) p ≡ p′ → prm (sp u) q ≡ q′ →
            prm (sp u) r ≡ r′ → prm (sp u) s ≡ s′ →
            sgn (sp u) p ≡ sgn (sp u) q → sgn (sp u) r ≡ sgn (sp u) s →
            p ≢ q → p ≢ r → p ≢ s → q ≢ r → q ≢ s → r ≢ s →
            u • hh {₃₊ m} p′ q′ r′ s′ ≈ hh {₃₊ m} p q r s • u
  hh-pass u u′ hu hu′ inv p q r s p′ q′ r′ s′ ep eq er es spq srs
          pq pr ps qr qs rs = begin
    u • hh {₃₊ m} p′ q′ r′ s′
      ≈⟨ back u (sym right-unit) ⟩
    u • (hh {₃₊ m} p′ q′ r′ s′ • ε)
      ≈⟨ back u (back (hh {₃₊ m} p′ q′ r′ s′) (sym cancel)) ⟩
    u • (hh {₃₊ m} p′ q′ r′ s′ • (u′ • u))
      ≈⟨ back u (sym assoc) ⟩
    u • ((hh {₃₊ m} p′ q′ r′ s′ • u′) • u)
      ≈⟨ sym assoc ⟩
    (u • (hh {₃₊ m} p′ q′ r′ s′ • u′)) • u
      ≈⟨ front u moved ⟩
    hh {₃₊ m} p q r s • u ∎
    where
    cancel : u′ • u ≈ ε
    cancel = A5-mat (cat hu′ hu) nil
               (inv-of hu′ hu (⊙-inverse (sp u) (sp u′) (sp-inj u′) inv))

    moved : u • (hh {₃₊ m} p′ q′ r′ s′ • u′) ≈ hh {₃₊ m} p q r s
    moved = hh-conj u u′ hu hu′ inv p q r s p′ q′ r′ s′ ep eq er es spq srs
                    pq pr ps qr qs rs

  ----------------------------------------------------------------------
  -- (76), and with it (68)
  --
  --     ((−1)_[a] X_[a,e]) (H_[a,b] H_[c,d])
  --        ≈  (H_[e,b] H_[c,d]) ((−1)_[a] X_[a,e])
  --
  -- for five distinct indices.  The letter's exchange renames the
  -- pair's first index and nothing else, and its sign sits on a, which
  -- is not among the pre-images — so `hh-conj` applies with the
  -- pre-image tuple (e , b , c , d).  Equation (68) is this at
  -- e = a + 1.

  eq76 : ∀ (a e b c d : Fin N) →
         a ≢ e → a ≢ b → a ≢ c → a ≢ d →
         e ≢ b → e ≢ c → e ≢ d → b ≢ c → b ≢ d → c ≢ d →
         zx {₃₊ m} a a e • hh {₃₊ m} a b c d
         ≈ hh {₃₊ m} e b c d • zx {₃₊ m} a a e
  eq76 a e b c d ae ab ac ad eb ec ed bc bd cd =
    hh-pass U U′ hU hU′ inv e b c d a b c d pe pb pc pd
            (Eq.trans (sg e (≢sym ae)) (Eq.sym (sg b (≢sym ab))))
            (Eq.trans (sg c (≢sym ac)) (Eq.sym (sg d (≢sym ad))))
            eb ec ed bc bd cd
    where
    U U′ : W
    U  = zx {₃₊ m} a a e
    U′ = zx {₃₊ m} e a e

    hU : HFreeʷ U
    hU = hfree-zx a a e

    hU′ : HFreeʷ U′
    hU′ = hfree-zx e a e

    -- The two letters are inverse: each carries the other's sign
    -- across its own exchange.
    inv : sp U ⊛ sp U′ ≗ idSP
    inv = zx-pair a e a e (Eq.sym (swapF-b a e))

    -- Where the exchange sends the four pre-images.
    pe : prm (sp U) e ≡ a
    pe = Eq.trans (zx-prm a a e e) (swapF-b a e)

    pb : prm (sp U) b ≡ b
    pb = Eq.trans (zx-prm a a e b) (swapF-o a e b (≢sym ab) (≢sym eb))

    pc : prm (sp U) c ≡ c
    pc = Eq.trans (zx-prm a a e c) (swapF-o a e c (≢sym ac) (≢sym ec))

    pd : prm (sp U) d ≡ d
    pd = Eq.trans (zx-prm a a e d) (swapF-o a e d (≢sym ad) (≢sym ed))

    -- And that it signs none of them: its one sign sits on a.
    sg : ∀ (x : Fin N) → x ≢ a → sgn (sp U) x ≡ false
    sg x ne = zx-sgn a a e x ne

  ----------------------------------------------------------------------
  -- A double exchange passes a pair
  --
  -- The coset action of Appendix A.3 produces `X_[z,w] X_[x,y]` beside
  -- a Hadamard letter at three of its four cosets, so this is the
  -- instance of `hh-pass` item (b) will want.  A double exchange on two
  -- *disjoint* pairs carries no sign and is its own inverse, so both
  -- hypotheses come for free and only the images are left to give.

  xx-pass : ∀ (x y z w : Fin N) → x ≢ y → z ≢ w →
            x ≢ z → x ≢ w → y ≢ z → y ≢ w →
            ∀ (p q r s p′ q′ r′ s′ : Fin N) →
            swapF z w (swapF x y p) ≡ p′ → swapF z w (swapF x y q) ≡ q′ →
            swapF z w (swapF x y r) ≡ r′ → swapF z w (swapF x y s) ≡ s′ →
            p ≢ q → p ≢ r → p ≢ s → q ≢ r → q ≢ s → r ≢ s →
            xx {₃₊ m} x y z w • hh {₃₊ m} p′ q′ r′ s′
            ≈ hh {₃₊ m} p q r s • xx {₃₊ m} x y z w
  xx-pass x y z w xy zw xz xw yz yw p q r s p′ q′ r′ s′ ep eq er es
          pq pr ps qr qs rs =
    hh-pass U U hU hU inv p q r s p′ q′ r′ s′
            (Eq.trans (xx-prm p) ep) (Eq.trans (xx-prm q) eq)
            (Eq.trans (xx-prm r) er) (Eq.trans (xx-prm s) es)
            (Eq.trans (xx-sgn p) (Eq.sym (xx-sgn q)))
            (Eq.trans (xx-sgn r) (Eq.sym (xx-sgn s)))
            pq pr ps qr qs rs
    where
    U : W
    U = xx {₃₊ m} x y z w

    hU : HFreeʷ U
    hU = Eq.subst HFreeʷ (gen-xx x y z w xy zw) (gen (hf-xx x y z w xy zw))

    spU : sp U ≗ (SWP x y ⊛ SWP z w)
    spU = sp-xx x y z w xy zw

    xx-prm : ∀ (v : Fin N) → prm (sp U) v ≡ swapF z w (swapF x y v)
    xx-prm = prm≡′ spU

    xx-sgn : ∀ (v : Fin N) → sgn (sp U) v ≡ false
    xx-sgn = sgn≡′ spU

    -- Two exchanges on disjoint pairs commute, so the product squares
    -- away: the inner conjugate is the first exchange again.
    inv : sp U ⊛ sp U ≗ idSP
    inv =
      ≐-trans′ (⊙-cong′ spU spU)
      (≐-trans′ (⊙-assoc′ (SWP x y) (SWP z w) (SWP x y ⊛ SWP z w))
      (≐-trans′ (⊙-cong′ (≐-refl′ {SWP x y})
                  (≐-trans′ (SWP-conj z w x y)
                            (swp≡ (swapF-o z w x xz xw) (swapF-o z w y yz yw))))
                (SWP-invol x y)))

  ----------------------------------------------------------------------
  -- A sign pair on the pair's own two indices commutes with it
  --
  -- The general form of Equation (39), which says it at 0 and 1.  A
  -- sign pair moves nothing, and its two signs are both on p and q or
  -- both off r and s, so the condition `hh-pass` asks for holds at
  -- both pairs.  (Away from all four indices it is `Figure10.comm-zz`;
  -- one index in and one out is the case that genuinely fails.)

  zz-pass : ∀ (p q r s : Fin N) →
            p ≢ q → p ≢ r → p ≢ s → q ≢ r → q ≢ s → r ≢ s →
            zz {₃₊ m} p q • hh {₃₊ m} p q r s
            ≈ hh {₃₊ m} p q r s • zz {₃₊ m} p q
  zz-pass p q r s pq pr ps qr qs rs =
    hh-pass Z Z hZ hZ inv p q r s p q r s
            Eq.refl Eq.refl Eq.refl Eq.refl
            (Eq.trans sg-p (Eq.sym sg-q)) (Eq.trans sg-r (Eq.sym sg-s))
            pq pr ps qr qs rs
    where
    Z : W
    Z = zz {₃₊ m} p q

    hZ : HFreeʷ Z
    hZ = gen (hf-zz p q)

    -- A sign pair is its own inverse: it moves nothing, and every
    -- sign is toggled twice.
    inv : sp Z ⊛ sp Z ≗ idSP
    inv = eqv (λ i → xor-self (δ p i xor δ q i)) (λ _ → Eq.refl)

    sg-p : sgn (sp Z) p ≡ true
    sg-p = Eq.cong₂ _xor_ (δ-here p) (δ-≢ q p pq)

    sg-q : sgn (sp Z) q ≡ true
    sg-q = Eq.cong₂ _xor_ (δ-≢ p q (≢sym pq)) (δ-here q)

    sg-r : sgn (sp Z) r ≡ false
    sg-r = Eq.cong₂ _xor_ (δ-≢ p r (≢sym pr)) (δ-≢ q r (≢sym qr))

    sg-s : sgn (sp Z) s ≡ false
    sg-s = Eq.cong₂ _xor_ (δ-≢ p s (≢sym ps)) (δ-≢ q s (≢sym qs))

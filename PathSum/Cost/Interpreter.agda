------------------------------------------------------------------------
-- Presentations of groups
--
-- The sparse interpreter in the cost model: corollary 2.15's time half
-- (Amy, QPL 2018)
--
-- Corollary 2.15 ends: the path-sum of an n-qubit Clifford+R_k circuit
-- "can be computed in polynomial time".  PathSum.Size.Interpreter
-- computes a representation of ⟦ C ⟧ over {H, CNOT, R_k, R_k†} gate by
-- gate, and bounds the size of every intermediate state; that each
-- step does work polynomial in its data is evident there, but not a
-- theorem.  Here the same construction is written in the monad of
-- PathSum.Cost, and its cost is bounded.
--
-- The state is a list of terms and a vector of the forms on the wires
-- (StateK).  The gates do what PathSum.Size.Interpreter's do:
--
--    R_k w    reads the form on w, writes 2^(M-k) mod 2^M (one step),
--             computes the truncated lifting of the form at degree k
--             (PathSum.Cost.Subst.liftTermsᶜ: an enumeration of the
--             submonomials of degree at most k, and a coefficient
--             each), and prepends it;
--    R_k† w   the same with -2^(M-k);
--    H w      the lifting of the form at degree 1 times ½, read with
--             the fresh y₀ (y₀ᵀ), the old terms read with it too (wkᵀ),
--             every form weakened, and y₀ written on w;
--    CNOT c t the form on c added to the form on t.
--
-- Proved:
--
--  * runK-sim: the value is PathSum.Size.Interpreter.runˢ's, the terms
--    literally and the forms pointwise (SimK); so the result denotes
--    ⟦ C ⟧ (interpK-denotes, from interpᴷ-correct) and has the lengths
--    Size.Interpreter bounds (interpK-length: at most
--    |C| (n + |C| + 1)^max(1,k) terms, k the level of C).
--  * cost-interpKᶜ: at most 23 (n + |C| + 1)^(max(1,k)+2) steps --
--    polynomial in n + |C| for every fixed level k -- and, when n and
--    |C| are at least 1, at most 23 (2 n |C| + 1)^(max(1,k)+2), a
--    polynomial in the volume n · |C| (cost-interpK-volume).  At |C| = 0
--    the result still has n forms of n + 1 bits, which no polynomial in
--    the volume 0 bounds (PathSum.Size.volume-degenerate).
--
-- corollary-2-15-time collects the three.  The bounds are upper
-- bounds and are not tight; the exponent grows with the level k, as
-- the number of terms an R_k adds does.
--
-- Costs are counted in the cost model of PathSum.Cost: a cost model,
-- not a machine model; nothing is claimed about Turing machines or
-- complexity classes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Cost.Interpreter (M : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _xor_; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (ℤ; -_)
  renaming (_*_ to _*ℤ_)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.Nat.Base using
  (zero; suc; _+_; _*_; _∸_; _^_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; tabulate)
  renaming (map to mapⱽ)
open import Data.Vec.Properties using (lookup-map; lookup∘tabulate)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import PathSum.Base using (PathSum)
open import PathSum.Cost
open import PathSum.Cost.Coeff M using
  (Coeff; residue-≡ᴹ; coeff-residue; *-≡ᴹ)
open import PathSum.Cost.Monomial using
  (varᶜ; value-varᶜ; cost-varᶜ; xorᵐᶜ; value-xorᵐᶜ; cost-xorᵐᶜ)
open import PathSum.Cost.Restriction M using
  (setᶜ; lookup-setᶜ; cost-setᶜ)
open import PathSum.Cost.Subst M using
  (liftTermsᶜ; value-liftTermsᶜ; cost-liftTermsᶜ)
open import PathSum.Linear using (Lin; liftᴸ; varᴸ; wkLin; _⊕ᴸ_)
open import PathSum.Order M using (pow)
open import PathSum.Polynomial using (x[_]; y[_]; ⟪_⟫)
open import PathSum.Reduction M using (½)
open import PathSum.Size M using (norm≤lengthᴷ)
open import PathSum.Size.Interpreter M using
  (initˢ; runˢ; interpᴷ; Denotes; denotes; interpᴷ-correct; interpᴷ-length;
   interpᴷ-paths≤)
open import PathSum.Size.Sparse M using
  (Term; coeff; residue; Rep; rep; terms; forms; Represents; volume-≤)
open import PathSum.Size.Terms M using
  (wkᵀ; y₀ᵀ; liftTerms; lterm; lcoeff; liftTerms-length≤)

import Data.Fin.Properties as Fin
import Data.Integer.Properties as ℤP
import Data.List.Properties as List
import Data.Nat.Properties as ℕ
import PathSum.CRK.Circuit

private
  module K = PathSum.CRK.Circuit M

open K using (_[_↦_])

open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- The interpreter

-- A list of terms, and the form on each wire.

StateK : ℕ → ℕ → Set
StateK n m = List (Term n m) × Vec (Lin n m) n

initKᶜ : Cost (StateK n 0)
initKᶜ = (λ fs → [] , fs) <$> tabulateᶜ (λ w → (false ,_) <$> varᶜ x[ w ])

-- R_k and R_k†, given the coefficient ±2^(M-k) mod 2^M.

stepRKᶜ : Coeff → ℕ → Fin n → StateK n m → Cost (StateK n m)
stepRKᶜ r k w (ts , fs) = do
  l  ← lookupᶜ fs w
  us ← liftTermsᶜ r k l
  vs ← appendᶜ us ts
  pure (vs , fs)

stepCNOTKᶜ : Fin n → Fin n → StateK n m → Cost (StateK n m)
stepCNOTKᶜ c t (ts , fs) = do
  a   ← lookupᶜ fs t
  b   ← lookupᶜ fs c
  e   ← step (proj₁ a xor proj₁ b)
  S   ← xorᵐᶜ (proj₂ a) (proj₂ b)
  fs′ ← setᶜ fs t (e , S)
  pure (ts , fs′)

stepHKᶜ : Fin n → StateK n m → Cost (StateK n (suc m))
stepHKᶜ w (ts , fs) = do
  l   ← lookupᶜ fs w
  h   ← step (residue ½)
  us  ← liftTermsᶜ h 1 l
  us′ ← mapᶜ (λ t → step (y₀ᵀ t)) us
  ts′ ← mapᶜ (λ t → step (wkᵀ t)) ts
  vs  ← appendᶜ us′ ts′
  fs′ ← mapVᶜ (λ l → step (wkLin l)) fs
  δ   ← varᶜ y[ zero ]
  fs″ ← setᶜ fs′ w (false , δ)
  pure (vs , fs″)

runKᶜ : K.Circuit n → StateK n m → Cost (∃ (StateK n))
runKᶜ []                 s = pure (_ , s)
runKᶜ (K.H w ∷ C)        s = do
  tick
  s′ ← stepHKᶜ w s
  runKᶜ C s′
runKᶜ (K.CNOT c t _ ∷ C) s = do
  tick
  s′ ← stepCNOTKᶜ c t s
  runKᶜ C s′
runKᶜ (K.R k w ∷ C)      s = do
  tick
  r  ← step (residue (pow (M ∸ k)))
  s′ ← stepRKᶜ r k w s
  runKᶜ C s′
runKᶜ (K.R† k w ∷ C)     s = do
  tick
  r  ← step (residue (- pow (M ∸ k)))
  s′ ← stepRKᶜ r k w s
  runKᶜ C s′

-- The whole interpretation; the forms are read off the vector.

interpKᶜ : K.Circuit n → Cost (∃ (Rep n))
interpKᶜ C = do
  s ← initKᶜ
  p ← runKᶜ C s
  pure (proj₁ p , rep (proj₁ (proj₂ p)) (lookup (proj₂ (proj₂ p))))


------------------------------------------------------------------------
-- Its value is PathSum.Size.Interpreter's

-- The same number of path variables, the same terms, and the same
-- forms pointwise.

data SimK {n : ℕ} : ∃ (StateK n) → ∃ (Rep n) → Set where
  simK : ∀ {m} (ts : List (Term n m)) (fs : Vec (Lin n m) n)
         (f : Fin n → Lin n m) → (∀ w → lookup fs w ≡ f w) →
         SimK (m , (ts , fs)) (m , rep ts f)

-- A residue of the coefficient gives the same truncated lifting.

liftTerms-residue : ∀ z d (l : Lin n m) →
                    liftTerms (coeff (residue z)) d l ≡ liftTerms z d l
liftTerms-residue z d (c , (α , β)) = List.map-cong
  (λ δ → cong (δ ,_) (lterm-eq δ)) _
  where
  lterm-eq : ∀ δ → lterm (coeff (residue z)) c δ ≡ lterm z c δ
  lterm-eq δ = trans
    (cong residue (ℤP.*-comm (coeff (residue z)) (lcoeff c δ)))
    (trans (residue-≡ᴹ (*-≡ᴹ (lcoeff c δ) (coeff-residue z)))
           (cong residue (ℤP.*-comm (lcoeff c δ) z)))

private
  lift-at : ∀ z d (fs : Vec (Lin n m) n) (f : Fin n → Lin n m) →
            (∀ w → lookup fs w ≡ f w) → (w : Fin n) →
            value (liftTermsᶜ (residue z) d (value (lookupᶜ fs w))) ≡
            liftTerms z d (f w)
  lift-at z d fs f h w =
    trans (value-liftTermsᶜ (residue z) d (value (lookupᶜ fs w)))
    (trans (liftTerms-residue z d (value (lookupᶜ fs w)))
           (cong (liftTerms z d) (trans (value-lookupᶜ fs w) (h w))))

-- Every gate keeps the similarity.

runK-sim : (C : K.Circuit n) (ts : List (Term n m)) (fs : Vec (Lin n m) n)
           (f : Fin n → Lin n m) → (∀ w → lookup fs w ≡ f w) →
           SimK (value (runKᶜ C (ts , fs))) (runˢ C (rep ts f))
runK-sim []                 ts fs f h = simK ts fs f h
runK-sim (K.H w ∷ C)        ts fs f h =
  subst (λ vs → SimK (value (runKᶜ C (value (stepHKᶜ w (ts , fs)))))
                     (runˢ C (rep vs f′)))
        vs≡
        (runK-sim C _ _ f′ h′)
  where
  us = value (liftTermsᶜ (residue ½) 1 (value (lookupᶜ fs w)))

  f′ = (λ v → wkLin (f v)) [ w ↦ varᴸ y[ zero ] ]

  vs≡ : value (appendᶜ (value (mapᶜ (λ t → step (y₀ᵀ t)) us))
                       (value (mapᶜ (λ t → step (wkᵀ t)) ts))) ≡
        map y₀ᵀ (liftTerms ½ 1 (f w)) ++ map wkᵀ ts
  vs≡ = trans (value-appendᶜ (value (mapᶜ (λ t → step (y₀ᵀ t)) us))
                             (value (mapᶜ (λ t → step (wkᵀ t)) ts)))
    (cong₂ _++_
      (trans (value-mapᶜ (λ t → step (y₀ᵀ t)) us)
             (cong (map y₀ᵀ) (lift-at ½ 1 fs f h w)))
      (value-mapᶜ (λ t → step (wkᵀ t)) ts))

  h′ : ∀ v → lookup (proj₂ (value (stepHKᶜ w (ts , fs)))) v ≡ f′ v
  h′ v = trans (lookup-setᶜ (value (mapVᶜ (λ l → step (wkLin l)) fs)) w _ v)
    (cong₂ (λ a b → if ⌊ v Fin.≟ w ⌋ then a else b)
      (cong (false ,_) (value-varᶜ y[ zero ]))
      (trans (cong (λ gs → lookup gs v)
                   (value-mapVᶜ (λ l → step (wkLin l)) fs))
             (trans (lookup-map v wkLin fs) (cong wkLin (h v)))))
runK-sim (K.CNOT c t _ ∷ C) ts fs f h = runK-sim C ts _ _ h′
  where
  a = value (lookupᶜ fs t)
  b = value (lookupᶜ fs c)

  h′ : ∀ v → lookup (proj₂ (value (stepCNOTKᶜ c t (ts , fs)))) v ≡
             (f [ t ↦ (f t ⊕ᴸ f c) ]) v
  h′ v = trans (lookup-setᶜ fs t _ v)
    (cong₂ (λ x y → if ⌊ v Fin.≟ t ⌋ then x else y)
      (trans (cong (proj₁ a xor proj₁ b ,_)
                   (value-xorᵐᶜ (proj₂ a) (proj₂ b)))
             (cong₂ _⊕ᴸ_ (trans (value-lookupᶜ fs t) (h t))
                         (trans (value-lookupᶜ fs c) (h c))))
      (h v))
runK-sim (K.R k w ∷ C)      ts fs f h =
  subst (λ vs → SimK (value (runKᶜ C (value (stepRKᶜ r k w (ts , fs)))))
                     (runˢ C (rep vs f)))
        (trans (value-appendᶜ _ ts)
               (cong (_++ ts) (lift-at (pow (M ∸ k)) k fs f h w)))
        (runK-sim C _ fs f h)
  where
  r = residue (pow (M ∸ k))
runK-sim (K.R† k w ∷ C)     ts fs f h =
  subst (λ vs → SimK (value (runKᶜ C (value (stepRKᶜ r k w (ts , fs)))))
                     (runˢ C (rep vs f)))
        (trans (value-appendᶜ _ ts)
               (cong (_++ ts) (lift-at (- pow (M ∸ k)) k fs f h w)))
        (runK-sim C _ fs f h)
  where
  r = residue (- pow (M ∸ k))

-- From the start.

interpK-sim : (C : K.Circuit n) →
              SimK (value (runKᶜ C (value (initKᶜ {n})))) (interpᴷ C)
interpK-sim {n} C = runK-sim C [] (proj₂ (value (initKᶜ {n})))
  (λ w → varᴸ x[ w ])
  (λ w → trans (cong (λ fs → lookup fs w)
                     (value-tabulateᶜ
                        (λ v → (false ,_) <$> varᶜ (x[_] {n} {0} v))))
               (trans (lookup∘tabulate _ w)
                      (cong (false ,_) (value-varᶜ x[ w ]))))

-- Similar states denote the same path-sums, with the same number of
-- path variables and of terms.

private
  sim-denotes : ∀ {k m′} {ξ : PathSum n k m′}
                (p : ∃ (StateK n)) (q : ∃ (Rep n)) → SimK p q →
                Denotes ξ q →
                Denotes ξ (proj₁ p , rep (proj₁ (proj₂ p))
                                         (lookup (proj₂ (proj₂ p))))
  sim-denotes _ _ (simK ts fs f h) (denotes _ (eqP , outs)) =
    denotes (rep ts (lookup fs))
      (eqP , λ w γ → trans (outs w γ) (cong (λ l → liftᴸ l γ) (sym (h w))))


sim-length : (p : ∃ (StateK n)) (q : ∃ (Rep n)) → SimK p q →
             length (proj₁ (proj₂ p)) ≡ length (terms (proj₂ q))
sim-length _ _ (simK ts fs f h) = refl

sim-paths : (p : ∃ (StateK n)) (q : ∃ (Rep n)) → SimK p q →
            proj₁ p ≡ proj₁ q
sim-paths _ _ (simK ts fs f h) = refl

-- The interpreter computes ⟦ C ⟧, with Size.Interpreter's numbers of
-- terms and path variables.

interpK-denotes : (C : K.Circuit n) → Denotes K.⟦ C ⟧ (value (interpKᶜ C))
interpK-denotes {n} C = sim-denotes (value (runKᶜ C (value (initKᶜ {n}))))
  (interpᴷ C) (interpK-sim C) (interpᴷ-correct C)

interpK-length : (C : K.Circuit n) →
                 length (terms (proj₂ (value (interpKᶜ C)))) ≤
                 length C * suc (n + length C) ^ (1 ⊔ K.level C)
interpK-length {n} C = ℕ.≤-trans
  (ℕ.≤-reflexive (sim-length _ _ (interpK-sim C))) (interpᴷ-length C)

interpK-paths≤ : (C : K.Circuit n) → proj₁ (value (interpKᶜ C)) ≤ length C
interpK-paths≤ {n} C = ℕ.≤-trans
  (ℕ.≤-reflexive (sim-paths _ _ (interpK-sim C))) (interpᴷ-paths≤ C)


------------------------------------------------------------------------
-- The cost of each gate

-- R_k: the lookup, the truncated lifting (at most (n + m + 1)^k
-- submonomials, a coefficient each), and prepending it.

cost-stepRKᶜ : (r : Coeff) (k : ℕ) (w : Fin n) (ts : List (Term n m))
               (fs : Vec (Lin n m) n) →
               cost (stepRKᶜ r k w (ts , fs)) ≤
               n + (suc (n + m) ^ k * (6 * suc (n + m) + 4) +
                    (suc (n + m) ^ k + 0))
cost-stepRKᶜ r k w ts fs = ℕ.+-mono-≤ (cost-lookupᶜ fs w)
  (ℕ.+-mono-≤ (cost-liftTermsᶜ r k l)
    (ℕ.+-mono-≤ (ℕ.≤-trans (cost-appendᶜ us ts)
      (ℕ.≤-trans (ℕ.≤-reflexive (cong length (value-liftTermsᶜ r k l)))
                 (liftTerms-length≤ (coeff r) k l)))
      (ℕ.≤-refl {0})))
  where
  l = value (lookupᶜ fs w)
  us = value (liftTermsᶜ r k l)

length-stepRK : (r : Coeff) (k : ℕ) (w : Fin n) (ts : List (Term n m))
                (fs : Vec (Lin n m) n) →
                length (proj₁ (value (stepRKᶜ r k w (ts , fs)))) ≤
                suc (n + m) ^ k + length ts
length-stepRK r k w ts fs = ℕ.≤-trans
  (ℕ.≤-reflexive (trans (cong length (value-appendᶜ us ts))
                        (List.length-++ us)))
  (ℕ.+-monoˡ-≤ (length ts)
    (ℕ.≤-trans (ℕ.≤-reflexive (cong length (value-liftTermsᶜ r k l)))
               (liftTerms-length≤ (coeff r) k l)))
  where
  l = value (lookupᶜ fs w)
  us = value (liftTermsᶜ r k l)

-- CNOT: two lookups, a sum of forms, and a write.

cost-stepCNOTKᶜ : (c t : Fin n) (ts : List (Term n m)) (fs : Vec (Lin n m) n) →
                  cost (stepCNOTKᶜ c t (ts , fs)) ≤
                  n + (n + (1 + ((n + m) + (n + 0))))
cost-stepCNOTKᶜ c t ts fs = ℕ.+-mono-≤ (cost-lookupᶜ fs t)
  (ℕ.+-mono-≤ (cost-lookupᶜ fs c)
    (ℕ.+-mono-≤ (ℕ.≤-refl {1})
      (ℕ.+-mono-≤ (cost-xorᵐᶜ (proj₂ a) (proj₂ b))
        (ℕ.+-mono-≤ (cost-setᶜ fs t (proj₁ a xor proj₁ b ,
                                     value (xorᵐᶜ (proj₂ a) (proj₂ b))))
                    (ℕ.≤-refl {0})))))
  where
  a = value (lookupᶜ fs t)
  b = value (lookupᶜ fs c)

-- H: the lifting at degree 1, both lists read with the fresh variable,
-- the forms weakened, and y₀ written.

private
  length-mapᶜ : ∀ {A B : Set} (f : A → B) (as : List A) →
                length (value (mapᶜ (λ a → step (f a)) as)) ≡ length as
  length-mapᶜ f as = trans (cong length (value-mapᶜ (λ a → step (f a)) as))
                           (List.length-map f as)

  lifted₁ : (h : Coeff) (l : Lin n m) →
            length (value (liftTermsᶜ h 1 l)) ≤ suc (n + m) ^ 1
  lifted₁ h l = ℕ.≤-trans
    (ℕ.≤-reflexive (cong length (value-liftTermsᶜ h 1 l)))
    (liftTerms-length≤ (coeff h) 1 l)

cost-stepHKᶜ : (w : Fin n) (ts : List (Term n m)) (fs : Vec (Lin n m) n) →
               cost (stepHKᶜ w (ts , fs)) ≤
               n + (1 + (suc (n + m) ^ 1 * (6 * suc (n + m) + 4) +
                    (suc (n + m) ^ 1 * 2 + (length ts * 2 +
                    (suc (n + m) ^ 1 + (n * 2 + ((n + suc m) + (n + 0))))))))
cost-stepHKᶜ {n} {m} w ts fs = ℕ.+-mono-≤ (cost-lookupᶜ fs w)
  (ℕ.+-mono-≤ (ℕ.≤-refl {1})
    (ℕ.+-mono-≤ (cost-liftTermsᶜ h 1 l)
      (ℕ.+-mono-≤ (ℕ.≤-trans (cost-mapᶜ (λ t → step (y₀ᵀ t)) us
                               (λ _ → ℕ.≤-refl {1}))
                             (ℕ.*-monoˡ-≤ 2 (lifted₁ h l)))
        (ℕ.+-mono-≤ (cost-mapᶜ (λ t → step (wkᵀ t)) ts (λ _ → ℕ.≤-refl {1}))
          (ℕ.+-mono-≤ (ℕ.≤-trans (cost-appendᶜ us′ ts′)
                        (ℕ.≤-trans (ℕ.≤-reflexive (length-mapᶜ y₀ᵀ us))
                                   (lifted₁ h l)))
            (ℕ.+-mono-≤ (cost-mapVᶜ (λ l → step (wkLin l)) fs
                                    (λ _ → ℕ.≤-refl {1}))
              (ℕ.+-mono-≤ (cost-varᶜ (y[_] {n} {suc m} zero))
                (ℕ.+-mono-≤ (cost-setᶜ fs′ w
                              (false , value (varᶜ (y[_] {n} {suc m} zero))))
                            (ℕ.≤-refl {0})))))))))
  where
  h = residue ½
  l = value (lookupᶜ fs w)
  us = value (liftTermsᶜ h 1 l)
  us′ = value (mapᶜ (λ t → step (y₀ᵀ t)) us)
  ts′ = value (mapᶜ (λ t → step (wkᵀ t)) ts)
  fs′ = value (mapVᶜ (λ l → step (wkLin l)) fs)

length-stepHK : (w : Fin n) (ts : List (Term n m)) (fs : Vec (Lin n m) n) →
                length (proj₁ (value (stepHKᶜ w (ts , fs)))) ≤
                suc (n + m) ^ 1 + length ts
length-stepHK w ts fs = ℕ.≤-trans
  (ℕ.≤-reflexive (trans (cong length (value-appendᶜ us′ ts′))
                        (List.length-++ us′)))
  (ℕ.+-mono-≤ (ℕ.≤-trans (ℕ.≤-reflexive (length-mapᶜ y₀ᵀ us))
                         (lifted₁ (residue ½) l))
              (ℕ.≤-reflexive (length-mapᶜ wkᵀ ts)))
  where
  l = value (lookupᶜ fs w)
  us = value (liftTermsᶜ (residue ½) 1 l)
  us′ = value (mapᶜ (λ t → step (y₀ᵀ t)) us)
  ts′ = value (mapᶜ (λ t → step (wkᵀ t)) ts)


------------------------------------------------------------------------
-- The cost of the run

-- With n + m + (Hadamards to come) ≤ N, every level at most d ≥ 1, and
-- the terms together with |C| (N + 1)^d more at most T, each gate
-- costs at most 20 (N + 1)^(d+1) + 2 T.

gateK : ℕ → ℕ → ℕ → ℕ
gateK N d T = 20 * suc N ^ suc d + 2 * T

private
  -- The arithmetic, in X = N + 1 and P = X^d.
  module Arith (N d : ℕ) (1≤d : 1 ≤ d) where
    X = suc N
    P = X ^ d

    1≤X : 1 ≤ X
    1≤X = s≤s z≤n

    1≤P : 1 ≤ P
    1≤P = ℕ.m^n>0 X d

    X≤P : X ≤ P
    X≤P = ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.^-identityʳ X)))
                    (ℕ.^-monoʳ-≤ X 1≤d)

    X≤Y : X ≤ X * P
    X≤Y = ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.*-identityʳ X)))
                    (ℕ.*-monoʳ-≤ X 1≤P)

    1≤Y : 1 ≤ X * P
    1≤Y = ℕ.≤-trans 1≤X X≤Y

    N≤Y : N ≤ X * P
    N≤Y = ℕ.≤-trans (ℕ.n≤1+n N) X≤Y

    -- A power of a base at most X, to an exponent at most d.
    pow≤ : ∀ {A e} → A ≤ X → e ≤ d → A ^ e ≤ P
    pow≤ {A} {e} A≤ e≤ = ℕ.≤-trans (ℕ.^-monoˡ-≤ e A≤) (ℕ.^-monoʳ-≤ X e≤)

    -- The truncated lifting: A^e (6 A + 4) ≤ 10 X P.
    lift≤ : ∀ {A e} → A ≤ X → e ≤ d → A ^ e * (6 * A + 4) ≤ 10 * (X * P)
    lift≤ {A} {e} A≤ e≤ = ℕ.≤-trans
      (ℕ.*-mono-≤ (pow≤ A≤ e≤)
        (ℕ.≤-trans (ℕ.+-mono-≤ (ℕ.*-monoʳ-≤ 6 A≤)
                               (ℕ.≤-trans (ℕ.≤-reflexive
                                  (sym (ℕ.*-identityʳ 4)))
                                  (ℕ.*-monoʳ-≤ 4 1≤X)))
                   (ℕ.≤-reflexive (solve 1 (λ X → con 6 :* X :+ con 4 :* X :=
                                                   con 10 :* X) refl X))))
      (ℕ.≤-reflexive (solve 2 (λ P X → P :* (con 10 :* X) :=
                                       con 10 :* (X :* P)) refl P X))

    -- The same at exponent 1.
    lift₁≤ : ∀ {A} → A ≤ X → A ^ 1 * (6 * A + 4) ≤ 10 * (X * P)
    lift₁≤ A≤ = lift≤ A≤ 1≤d

    one≤ : ∀ {A} → A ≤ X → A ^ 1 ≤ X * P
    one≤ {A} A≤ = ℕ.≤-trans (pow≤ A≤ 1≤d) (ℕ.≤-trans (ℕ.≤-reflexive
      (sym (ℕ.*-identityˡ P))) (ℕ.*-monoˡ-≤ P 1≤X))

    -- The terms after a gate adding at most P.
    grow : ∀ {L L′ c T} → L′ ≤ P + L → L + suc c * P ≤ T → L′ + c * P ≤ T
    grow {L} {L′} {c} {T} le inv = ℕ.≤-trans (ℕ.+-monoˡ-≤ (c * P) le)
      (ℕ.≤-trans (ℕ.≤-reflexive (solve 3 (λ P L c → (P :+ L) :+ c :* P :=
                                             L :+ (P :+ c :* P)) refl P L c))
                 inv)

mutual
  cost-runKᶜ : (C : K.Circuit n) (ts : List (Term n m)) (fs : Vec (Lin n m) n)
               (N d T : ℕ) → n + m + K.norm C ≤ N → 1 ≤ d → K.level C ≤ d →
               length ts + length C * suc N ^ d ≤ T →
               cost (runKᶜ C (ts , fs)) ≤ length C * gateK N d T
  cost-runKᶜ [] ts fs N d T le 1≤d lv inv = z≤n
  cost-runKᶜ {n} {m} (K.H w ∷ C) ts fs N d T le 1≤d lv inv = ℕ.+-mono-≤
    (ℕ.≤-trans
      (ℕ.+-mono-≤ 1≤Y (ℕ.≤-trans (cost-stepHKᶜ w ts fs)
        (ℕ.+-mono-≤ n≤Y (ℕ.+-mono-≤ 1≤Y (ℕ.+-mono-≤ (lift₁≤ A≤X)
          (ℕ.+-mono-≤ (ℕ.*-monoˡ-≤ 2 (one≤ A≤X))
            (ℕ.+-mono-≤ (ℕ.*-monoˡ-≤ 2 L≤T)
              (ℕ.+-mono-≤ (one≤ A≤X)
                (ℕ.+-mono-≤ (ℕ.*-monoˡ-≤ 2 n≤Y)
                  (ℕ.+-mono-≤ nsm≤Y (ℕ.+-mono-≤ n≤Y (z≤n {0}))))))))))))
      (ℕ.≤-reflexive (solve 2 (λ Y T → Y :+ (Y :+ (Y :+ (con 10 :* Y :+
                                 (Y :* con 2 :+ (T :* con 2 :+ (Y :+
                                 (Y :* con 2 :+ (Y :+ (Y :+ con 0))))))))) :=
                               con 20 :* Y :+ con 2 :* T) refl (X * P) T)))
    (cost-runKᶜ C (proj₁ (value (stepHKᶜ w (ts , fs))))
                  (proj₂ (value (stepHKᶜ w (ts , fs)))) N d T le′ 1≤d lv
      (grow {c = length C} (ℕ.≤-trans (length-stepHK w ts fs)
                       (ℕ.+-monoˡ-≤ (length ts) (pow≤ A≤X 1≤d)))
            inv))
    where
    open Arith N d 1≤d

    le′ : n + suc m + K.norm C ≤ N
    le′ = ℕ.≤-trans (ℕ.≤-reflexive (trans (cong (_+ K.norm C) (ℕ.+-suc n m))
                                          (sym (ℕ.+-suc (n + m) (K.norm C)))))
                    le

    A≤X : suc (n + m) ≤ X
    A≤X = s≤s (ℕ.≤-trans (ℕ.m≤m+n (n + m) (suc (K.norm C))) le)

    n≤Y : n ≤ X * P
    n≤Y = ℕ.≤-trans (ℕ.≤-trans (ℕ.m≤m+n n m) (ℕ.n≤1+n (n + m)))
                    (ℕ.≤-trans A≤X X≤Y)

    nsm≤Y : n + suc m ≤ X * P
    nsm≤Y = ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-suc n m)) (ℕ.≤-trans A≤X X≤Y)

    L≤T : length ts ≤ T
    L≤T = ℕ.≤-trans (ℕ.m≤m+n (length ts) _) inv
  cost-runKᶜ {n} {m} (K.CNOT c t _ ∷ C) ts fs N d T le 1≤d lv inv =
    ℕ.+-mono-≤
      (ℕ.≤-trans
        (ℕ.+-mono-≤ 1≤Y (ℕ.≤-trans (cost-stepCNOTKᶜ c t ts fs)
          (ℕ.+-mono-≤ n≤Y (ℕ.+-mono-≤ n≤Y (ℕ.+-mono-≤ 1≤Y
            (ℕ.+-mono-≤ nm≤Y (ℕ.+-mono-≤ n≤Y (z≤n {0}))))))))
        (ℕ.≤-trans
          (ℕ.≤-reflexive (solve 1 (λ Y → Y :+ (Y :+ (Y :+ (Y :+
                                     (Y :+ (Y :+ con 0))))) := con 6 :* Y)
                                  refl (X * P)))
          (ℕ.≤-trans (ℕ.*-monoˡ-≤ (X * P) (ℕ.m≤m+n 6 14))
                     (ℕ.m≤m+n (20 * (X * P)) (2 * T)))))
      (cost-runKᶜ C ts _ N d T le 1≤d lv
        (ℕ.≤-trans (ℕ.+-monoʳ-≤ (length ts) (ℕ.m≤n+m (length C * P) P)) inv))
    where
    open Arith N d 1≤d

    nm≤X : n + m ≤ N
    nm≤X = ℕ.≤-trans (ℕ.m≤m+n (n + m) (K.norm C)) le

    nm≤Y : n + m ≤ X * P
    nm≤Y = ℕ.≤-trans nm≤X N≤Y

    n≤Y : n ≤ X * P
    n≤Y = ℕ.≤-trans (ℕ.m≤m+n n m) nm≤Y

  cost-runKᶜ (K.R k w ∷ C)  ts fs N d T le 1≤d lv inv =
    cost-rotation k w C ts fs N d T le 1≤d lv inv (residue (pow (M ∸ k)))
  cost-runKᶜ (K.R† k w ∷ C) ts fs N d T le 1≤d lv inv =
    cost-rotation k w C ts fs N d T le 1≤d lv inv (residue (- pow (M ∸ k)))

  -- R_k and R_k† cost the same.
  cost-rotation : (k : ℕ) (w : Fin n) (C : K.Circuit n) (ts : List (Term n m))
                  (fs : Vec (Lin n m) n) (N d T : ℕ) →
                  n + m + K.norm C ≤ N → 1 ≤ d → k ⊔ K.level C ≤ d →
                  length ts + suc (length C) * suc N ^ d ≤ T → (r : Coeff) →
                  suc (suc (cost (stepRKᶜ r k w (ts , fs)) +
                            cost (runKᶜ C (value (stepRKᶜ r k w (ts , fs))))))
                  ≤ suc (length C) * gateK N d T
  cost-rotation {n} {m} k w C ts fs N d T le 1≤d lv inv r = ℕ.+-mono-≤
    (ℕ.≤-trans
      (ℕ.+-mono-≤ 1≤Y (ℕ.+-mono-≤ 1≤Y (ℕ.≤-trans (cost-stepRKᶜ r k w ts fs)
        (ℕ.+-mono-≤ n≤Y (ℕ.+-mono-≤ (lift≤ A≤X k≤d)
          (ℕ.+-mono-≤ (ℕ.≤-trans (pow≤ A≤X k≤d) P≤Y) (z≤n {0})))))))
      (ℕ.≤-trans
        (ℕ.≤-reflexive (solve 1 (λ Y → Y :+ (Y :+ (Y :+ (con 10 :* Y :+
                                   (Y :+ con 0)))) := con 14 :* Y)
                                refl (X * P)))
        (ℕ.≤-trans (ℕ.*-monoˡ-≤ (X * P) (ℕ.m≤m+n 14 6))
                   (ℕ.m≤m+n (20 * (X * P)) (2 * T)))))
    (cost-runKᶜ C (proj₁ (value (stepRKᶜ r k w (ts , fs)))) fs N d T le 1≤d
                (ℕ.m⊔n≤o⇒n≤o k (K.level C) lv)
      (grow {c = length C} (ℕ.≤-trans (length-stepRK r k w ts fs)
                       (ℕ.+-monoˡ-≤ (length ts) (pow≤ A≤X k≤d)))
            inv))
    where
    open Arith N d 1≤d

    k≤d : k ≤ d
    k≤d = ℕ.m⊔n≤o⇒m≤o k (K.level C) lv

    A≤X : suc (n + m) ≤ X
    A≤X = s≤s (ℕ.≤-trans (ℕ.m≤m+n (n + m) (K.norm C)) le)

    n≤Y : n ≤ X * P
    n≤Y = ℕ.≤-trans (ℕ.≤-trans (ℕ.m≤m+n n m) (ℕ.n≤1+n (n + m)))
                    (ℕ.≤-trans A≤X X≤Y)

    P≤Y : P ≤ X * P
    P≤Y = ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.*-identityˡ P)))
                    (ℕ.*-monoˡ-≤ P 1≤X)


------------------------------------------------------------------------
-- The cost of the interpretation

-- At most 23 (n + |C| + 1)^(max(1,k)+2).

cost-interpKᶜ : (C : K.Circuit n) →
                cost (interpKᶜ C) ≤
                23 * suc (n + length C) ^ suc (suc (1 ⊔ K.level C))
cost-interpKᶜ {n} C = ℕ.≤-trans
  (ℕ.+-mono-≤ init≤ (ℕ.+-mono-≤ run≤ (z≤n {0})))
  (ℕ.≤-reflexive (solve 1 (λ Z → Z :+ (con 22 :* Z :+ con 0) := con 23 :* Z)
                         refl (X * (X * P))))
  where
  ℓ = length C
  N = n + ℓ
  d = 1 ⊔ K.level C
  X = suc N
  P = X ^ d

  1≤P : 1 ≤ P
  1≤P = ℕ.m^n>0 X d

  n≤X : n ≤ X
  n≤X = ℕ.≤-trans (ℕ.m≤m+n n ℓ) (ℕ.n≤1+n N)

  ℓ≤X : ℓ ≤ X
  ℓ≤X = ℕ.≤-trans (ℕ.m≤n+m ℓ n) (ℕ.n≤1+n N)

  XX≤ : X * X ≤ X * (X * P)
  XX≤ = ℕ.*-monoʳ-≤ X (ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.*-identityʳ X)))
                                 (ℕ.*-monoʳ-≤ X 1≤P))

  init≤ : cost (initKᶜ {n}) ≤ X * (X * P)
  init≤ = ℕ.≤-trans
    (cost-tabulateᶜ (λ w → (false ,_) <$> varᶜ (x[_] {n} {0} w))
                    (λ w → cost-varᶜ (x[_] {n} {0} w)))
    (ℕ.≤-trans (ℕ.*-mono-≤ n≤X (s≤s (ℕ.≤-trans
                  (ℕ.≤-reflexive (ℕ.+-identityʳ n)) (ℕ.m≤m+n n ℓ))))
               XX≤)

  run≤ : cost (runKᶜ C (value (initKᶜ {n}))) ≤ 22 * (X * (X * P))
  run≤ = ℕ.≤-trans
    (cost-runKᶜ C [] (proj₂ (value (initKᶜ {n}))) N d (ℓ * P)
      (ℕ.≤-trans (ℕ.≤-reflexive (cong (_+ K.norm C) (ℕ.+-identityʳ n)))
                 (ℕ.+-monoʳ-≤ n (norm≤lengthᴷ C)))
      (ℕ.m≤m⊔n 1 (K.level C)) (ℕ.m≤n⊔m 1 (K.level C)) ℕ.≤-refl)
    (ℕ.≤-trans (ℕ.*-mono-≤ ℓ≤X (ℕ.+-monoʳ-≤ (20 * (X * P))
                  (ℕ.*-monoʳ-≤ 2 (ℕ.*-monoˡ-≤ P ℓ≤X))))
      (ℕ.≤-reflexive (solve 2 (λ X P → X :* (con 20 :* (X :* P) :+
                                         con 2 :* (X :* P)) :=
                                       con 22 :* (X :* (X :* P)))
                              refl X P)))

-- In the volume n · |C|, for n and |C| at least 1.

cost-interpK-volume : (C : K.Circuit n) → 1 ≤ n → 1 ≤ length C →
                      cost (interpKᶜ C) ≤
                      23 * suc (2 * (n * length C)) ^ suc (suc (1 ⊔ K.level C))
cost-interpK-volume {n} C 1≤n 1≤ℓ = ℕ.≤-trans (cost-interpKᶜ C)
  (ℕ.*-monoʳ-≤ 23 (ℕ.^-monoˡ-≤ (suc (suc (1 ⊔ K.level C)))
    (s≤s (volume-≤ n (length C) 1≤n 1≤ℓ))))


------------------------------------------------------------------------
-- Corollary 2.15, its time half

record Corollary-2-15-time {n : ℕ} (C : K.Circuit n) : Set where
  field
    computes   : Denotes K.⟦ C ⟧ (value (interpKᶜ C))
    few-terms  : length (terms (proj₂ (value (interpKᶜ C)))) ≤
                 length C * suc (n + length C) ^ (1 ⊔ K.level C)
    polynomial : cost (interpKᶜ C) ≤
                 23 * suc (n + length C) ^ suc (suc (1 ⊔ K.level C))
    volume     : 1 ≤ n → 1 ≤ length C →
                 cost (interpKᶜ C) ≤
                 23 * suc (2 * (n * length C)) ^ suc (suc (1 ⊔ K.level C))

corollary-2-15-time : (C : K.Circuit n) → Corollary-2-15-time C
corollary-2-15-time C = record
  { computes   = interpK-denotes C
  ; few-terms  = interpK-length C
  ; polynomial = cost-interpKᶜ C
  ; volume     = cost-interpK-volume C
  }

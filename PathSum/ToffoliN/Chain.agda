------------------------------------------------------------------------
-- Presentations of groups
--
-- The n-bit Toffoli gate as a chain of Toffoli gates with ancillas
-- (Amy, QPL 2018, section 5.2), classically
--
-- Section 5.2 verifies "the standard decomposition into 2(n − 3) + 1
-- Toffoli gates and n − 3 ancillas" of
--
--    Toffoli_n : |x₁ x₂ … x_n⟩ ↦ |x₁ x₂ … (x_n ⊕ x₁ x₂ ⋯ x_(n−1))⟩.
--
-- This module is its Toffoli-level half: the netlist and the Boolean
-- function it computes on the inputs where the ancillas are 0.  The
-- Clifford+T half, and the theorems about path-sums, are in
-- PathSum.ToffoliN.
--
-- The wires are given by a Layout N j: j + 2 controls, a target and
-- j ancillas among N wires, all distinct (n = j + 3 is the number of
-- wires Toffoli_n acts on).  The netlist (chain) is the V-chain,
-- defined by recursion on j:
--
--    j = 0:      one Toffoli gate, c₀ c₁ onto the target;
--    j + 1:      a₀ ⊕= c₀ c₁, then the chain for the layout whose
--                controls are a₀, c₂, …, c_(j+2) and whose ancillas
--                are a₁, …, a_j (inner), then a₀ ⊕= c₀ c₁ again.
--
-- Unfolded, it computes a₀ = c₀c₁, a₁ = a₀c₂, …, then flips the target
-- by a_(j−1) c_(j+1), then uncomputes the ancillas in reverse order:
-- 2j + 1 Toffoli gates (length-chain) and j ancillas.
--
-- The theorem (chain-correct) is that on every input x whose ancillas
-- read 0 the netlist computes x[t ≔ x_t ⊕ x_c₀ x_c₁ ⋯ x_c(j+1)], the
-- ancillas read 0 again among its outputs.  By induction on j: after
-- the first gate a₀ reads x_c₀ x_c₁ (it read 0), and the other
-- ancillas still read 0, so the inner chain flips the target by
-- x_c₀ x_c₁ ⋯ x_c(j+1) and leaves every other wire alone; the last
-- gate then sets a₀ to x_c₀ x_c₁ ⊕ x_c₀ x_c₁ = 0.  Only the chain on
-- clean inputs is Toffoli_n; on other inputs it computes something
-- else, which is why the theorem is stated on those inputs, as the
-- paper means it.
--
-- Its specification, the classical path-sum toffoliₙˢ (PathSum.
-- Classical), outputs the inputs except on the target, which reads
-- the lift of the Boolean expression x_t ⊕ x_c₀ ⋯ x_c(j+1)
-- (fun-toffoliₙˢ).  Finally, the paper's layout: for every n ≥ 3, on
-- n + (n − 3) wires, the controls are wires 0 … n − 2, the target is
-- wire n − 1 and the ancillas are wires n … 2n − 4 (standard,
-- standard-ctl, standard-tgt, standard-anc).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.ToffoliN.Chain (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; _xor_)
open import Data.Bool.Properties using (∧-assoc; xor-same)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using
  (Fin; zero; suc; toℕ; fromℕ; inject₁; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Nat.Base using (_+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)

import Data.Fin.Properties as Fin

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

open import PathSum.Ancillas M₀ using (Clean)
open import PathSum.Assign using (_[_≔_]; ≔-here; ≔-there; ≔-≔; ≔-comm;
  ≔-cong; ≔-self)
open import PathSum.Base using (PathSum)
open import PathSum.Classical M₀ using
  (classical; fun; setWire; fun-setWireᵉ; none)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Polynomial using (x[_])
open import PathSum.Polynomial.Boolean using
  (BExp; ⟦_⟧ᵉ; var; _⊕ᵉ_; _∧ᵉ_; liftᵉ)
open import PathSum.Toffoli M₀ using (toffoli)
open import PathSum.Toffoli.Netlist M₀ using (Toff; toff; apply; apply-++)

private
  variable
    N j : ℕ


------------------------------------------------------------------------
-- Layouts

-- j + 2 controls, a target and j ancillas, all distinct.

record Layout (N j : ℕ) : Set where
  field
    ctl     : Fin (suc (suc j)) → Fin N
    tgt     : Fin N
    anc     : Fin j → Fin N
    ctl-inj : ∀ i i′ → ctl i ≡ ctl i′ → i ≡ i′
    anc-inj : ∀ i i′ → anc i ≡ anc i′ → i ≡ i′
    ctl≢tgt : ∀ i → ctl i ≢ tgt
    anc≢tgt : ∀ i → anc i ≢ tgt
    ctl≢anc : ∀ i i′ → ctl i ≢ anc i′

open Layout public

-- The first two controls differ.

c₀≢c₁ : (L : Layout N j) → ctl L zero ≢ ctl L (suc zero)
c₀≢c₁ L e = Fin.0≢1+n (ctl-inj L zero (suc zero) e)

-- The layout of the inner chain: the first ancilla becomes the first
-- control, in place of the first two, and the other ancillas remain.

inner : Layout N (suc j) → Layout N j
inner {N} {j} L = record
  { ctl     = ctl′
  ; tgt     = tgt L
  ; anc     = λ i → anc L (suc i)
  ; ctl-inj = ctl′-inj
  ; anc-inj = λ i i′ e → Fin.suc-injective (anc-inj L (suc i) (suc i′) e)
  ; ctl≢tgt = ctl′≢tgt
  ; anc≢tgt = λ i → anc≢tgt L (suc i)
  ; ctl≢anc = ctl′≢anc
  }
  where
  ctl′ : Fin (suc (suc j)) → Fin N
  ctl′ zero    = anc L zero
  ctl′ (suc i) = ctl L (suc (suc i))

  ctl′-inj : ∀ i i′ → ctl′ i ≡ ctl′ i′ → i ≡ i′
  ctl′-inj zero    zero     e = refl
  ctl′-inj zero    (suc i′) e = ⊥-elim (ctl≢anc L (suc (suc i′)) zero (sym e))
  ctl′-inj (suc i) zero     e = ⊥-elim (ctl≢anc L (suc (suc i)) zero e)
  ctl′-inj (suc i) (suc i′) e =
    cong suc (Fin.suc-injective (Fin.suc-injective
      (ctl-inj L (suc (suc i)) (suc (suc i′)) e)))

  ctl′≢tgt : ∀ i → ctl′ i ≢ tgt L
  ctl′≢tgt zero    = anc≢tgt L zero
  ctl′≢tgt (suc i) = ctl≢tgt L (suc (suc i))

  ctl′≢anc : ∀ i i′ → ctl′ i ≢ anc L (suc i′)
  ctl′≢anc zero    i′ e = Fin.0≢1+n (anc-inj L zero (suc i′) e)
  ctl′≢anc (suc i) i′   = ctl≢anc L (suc (suc i)) (suc i′)


------------------------------------------------------------------------
-- The chain

-- The gate that computes the first ancilla, a₀ ⊕= c₀ c₁ ...

first : Layout N (suc j) → Toff N
first L = toff (ctl L zero) (ctl L (suc zero)) (anc L zero) (c₀≢c₁ L)
               (ctl≢anc L zero zero) (ctl≢anc L (suc zero) zero)

-- ... and, without ancillas, the gate onto the target.

final : Layout N zero → Toff N
final L = toff (ctl L zero) (ctl L (suc zero)) (tgt L) (c₀≢c₁ L)
               (ctl≢tgt L zero) (ctl≢tgt L (suc zero))

chain : Layout N j → List (Toff N)
chain {j = zero}  L = final L ∷ []
chain {j = suc j} L = first L ∷ (chain (inner L) ++ first L ∷ [])

-- 2(n − 3) + 1 Toffoli gates, n − 3 being the number j of ancillas.

length-chain : (L : Layout N j) → length (chain L) ≡ 2 * j + 1
length-chain {j = zero}  L = refl
length-chain {j = suc j} L =
  trans (cong suc (trans (length-++ (chain (inner L)) {first L ∷ []})
                         (cong (_+ 1) (length-chain (inner L)))))
        (shape j)
  where
  shape : ∀ j → suc ((2 * j + 1) + 1) ≡ 2 * suc j + 1
  shape = solve 1 (λ j → con 1 :+ ((con 2 :* j :+ con 1) :+ con 1)
                         := con 2 :* (con 1 :+ j) :+ con 1) refl


------------------------------------------------------------------------
-- The function it computes on clean inputs

-- The conjunction of j + 1 bits.

⋀ : ∀ {k} → (Fin (suc k) → Bool) → Bool
⋀ {zero}  f = f zero
⋀ {suc k} f = f zero ∧ ⋀ (λ i → f (suc i))

⋀-cong : ∀ {k} {f g : Fin (suc k) → Bool} → (∀ i → f i ≡ g i) →
         ⋀ f ≡ ⋀ g
⋀-cong {zero}  h = h zero
⋀-cong {suc k} h = cong₂ _∧_ (h zero) (⋀-cong (λ i → h (suc i)))

-- The controls' conjunction, and the n-bit Toffoli function: the
-- target flipped by it.

controls : Layout N j → Assign N → Bool
controls L x = ⋀ (λ i → x (ctl L i))

toffoliₙ : Layout N j → Assign N → Assign N
toffoliₙ L x = x [ tgt L ≔ x (tgt L) xor controls L x ]

-- On clean inputs the chain computes it.

chain-correct : (L : Layout N j) (x : Assign N) → Clean (anc L) x →
                ∀ w → apply (chain L) x w ≡ toffoliₙ L x w
chain-correct {j = zero}  L x cl w = refl
chain-correct {N} {suc j} L x cl w =
  trans (cong (λ u → u w) (apply-++ (chain (inner L)) (first L ∷ []) x′))
        goal
  where
  c₀ c₁ a₀ t : Fin N
  c₀ = ctl L zero
  c₁ = ctl L (suc zero)
  a₀ = anc L zero
  t  = tgt L

  a₀≢t : a₀ ≢ t
  a₀≢t = anc≢tgt L zero

  b v : Bool
  b = x c₀ ∧ x c₁
  v = x t xor controls L x

  -- After the first gate a₀ reads x_c₀ x_c₁, and the other wires are
  -- as they were.

  x′ : Assign N
  x′ = toffoli c₀ c₁ a₀ x

  x′-a₀ : x′ a₀ ≡ b
  x′-a₀ = trans (≔-here x a₀ (x a₀ xor b)) (cong (_xor b) (cl zero))

  x′-there : ∀ {u} → u ≢ a₀ → x′ u ≡ x u
  x′-there u≢a₀ = ≔-there x (x a₀ xor b) u≢a₀

  cl′ : Clean (anc (inner L)) x′
  cl′ i = trans (x′-there (λ e → Fin.0≢1+n (sym (anc-inj L (suc i) zero e))))
                (cl (suc i))

  -- The inner chain: the target flipped by a₀ x_c₂ ⋯, which is the
  -- conjunction of all the controls.

  inner-controls : controls (inner L) x′ ≡ controls L x
  inner-controls =
    trans (cong₂ _∧_ x′-a₀
                 (⋀-cong (λ i → x′-there (ctl≢anc L (suc (suc i)) zero))))
          (∧-assoc (x c₀) (x c₁) (⋀ (λ i → x (ctl L (suc (suc i))))))

  y : Assign N
  y = apply (chain (inner L)) x′

  y≗ : ∀ u → y u ≡ (x′ [ t ≔ v ]) u
  y≗ u = trans (chain-correct (inner L) x′ cl′ u)
    (cong (λ d → (x′ [ t ≔ d ]) u)
          (cong₂ _xor_ (x′-there (λ e → a₀≢t (sym e))) inner-controls))

  y-off : ∀ {u} → u ≢ t → u ≢ a₀ → y u ≡ x u
  y-off u≢t u≢a₀ =
    trans (y≗ _) (trans (≔-there x′ v u≢t) (x′-there u≢a₀))

  -- The last gate: a₀ ⊕= x_c₀ x_c₁ returns a₀ to 0.

  y-a₀ : y a₀ ≡ b
  y-a₀ = trans (y≗ a₀) (trans (≔-there x′ v a₀≢t) x′-a₀)

  reset : y a₀ xor (y c₀ ∧ y c₁) ≡ false
  reset = trans (cong₂ _xor_ y-a₀
                  (cong₂ _∧_ (y-off (ctl≢tgt L zero) (ctl≢anc L zero zero))
                             (y-off (ctl≢tgt L (suc zero))
                                    (ctl≢anc L (suc zero) zero))))
                (xor-same b)

  xt-a₀ : false ≡ (x [ t ≔ v ]) a₀
  xt-a₀ = sym (trans (≔-there x v a₀≢t) (cl zero))

  goal : toffoli c₀ c₁ a₀ y w ≡ (x [ t ≔ v ]) w
  goal =
    trans (cong (λ d → (y [ a₀ ≔ d ]) w) reset)
    (trans (≔-cong a₀ false y≗ w)
    (trans (≔-cong a₀ false (≔-comm x (x a₀ xor b) v a₀≢t) w)
    (trans (≔-≔ (x [ t ≔ v ]) a₀ (x a₀ xor b) false w)
    (trans (cong (λ d → ((x [ t ≔ v ]) [ a₀ ≔ d ]) w) xt-a₀)
           (≔-self (x [ t ≔ v ]) a₀ w)))))

-- The ancillas are returned to 0.

toffoliₙ-anc : (L : Layout N j) (x : Assign N) → Clean (anc L) x →
               Clean (anc L) (toffoliₙ L x)
toffoliₙ-anc L x cl i = trans (≔-there x _ (anc≢tgt L i)) (cl i)


------------------------------------------------------------------------
-- The specification as a path-sum

-- The conjunction as a Boolean expression, x_c₀ ∧ (x_c₁ ∧ ⋯).

⋀ᵉ : ∀ {k} → (Fin (suc k) → Fin N) → BExp N 0
⋀ᵉ {k = zero}  c = var x[ c zero ]
⋀ᵉ {k = suc k} c = var x[ c zero ] ∧ᵉ ⋀ᵉ (λ i → c (suc i))

⟦⋀ᵉ⟧ : ∀ {k} (c : Fin (suc k) → Fin N) (x : Assign N) (y : Assign 0) →
       ⟦ ⋀ᵉ c ⟧ᵉ x y ≡ ⋀ (λ i → x (c i))
⟦⋀ᵉ⟧ {k = zero}  c x y = refl
⟦⋀ᵉ⟧ {k = suc k} c x y = cong (x (c zero) ∧_) (⟦⋀ᵉ⟧ (λ i → c (suc i)) x y)

-- x_t ⊕ x_c₀ ⋯ x_c(j+1), and the classical path-sum with its lift on
-- the target.

toffoliₙᵉ : Layout N j → BExp N 0
toffoliₙᵉ L = var x[ tgt L ] ⊕ᵉ ⋀ᵉ (ctl L)

toffoliₙˢ : Layout N j → PathSum N 0 0
toffoliₙˢ L = classical (setWire (tgt L) (liftᵉ (toffoliₙᵉ L)))

fun-toffoliₙˢ : (L : Layout N j) (x : Assign N) →
                ∀ w → fun (setWire (tgt L) (liftᵉ (toffoliₙᵉ L))) x w ≡
                      toffoliₙ L x w
fun-toffoliₙˢ L x w = trans (fun-setWireᵉ (tgt L) (toffoliₙᵉ L) x w)
  (cong (λ d → (x [ tgt L ≔ x (tgt L) xor d ]) w) (⟦⋀ᵉ⟧ (ctl L) x none))


------------------------------------------------------------------------
-- The paper's layout

private
  ↑ˡ≢↑ʳ : ∀ {m n} (i : Fin m) (k : Fin n) → i ↑ˡ n ≢ m ↑ʳ k
  ↑ˡ≢↑ʳ {m} {n} i k e = absurd
    (trans (sym (Fin.splitAt-↑ˡ m i n))
           (trans (cong (splitAt m) e) (Fin.splitAt-↑ʳ m n k)))
    where
    absurd : ∀ {A : Set} → inj₁ i ≡ inj₂ k → A
    absurd ()

-- For n ≥ 3, on n + (n − 3) wires: the controls are wires 0 … n − 2,
-- the target is wire n − 1, the ancillas are wires n … 2n − 4.

standard : (n : ℕ) → 3 ≤ n → Layout (n + (n ∸ 3)) (n ∸ 3)
standard (suc (suc (suc j))) (s≤s (s≤s (s≤s z≤n))) = record
  { ctl     = λ i → inject₁ i ↑ˡ j
  ; tgt     = fromℕ (suc (suc j)) ↑ˡ j
  ; anc     = λ i → suc (suc (suc j)) ↑ʳ i
  ; ctl-inj = λ i i′ e →
      Fin.inject₁-injective (Fin.↑ˡ-injective j (inject₁ i) (inject₁ i′) e)
  ; anc-inj = λ i i′ e → Fin.↑ʳ-injective (suc (suc (suc j))) i i′ e
  ; ctl≢tgt = λ i e →
      Fin.fromℕ≢inject₁ (sym (Fin.↑ˡ-injective j (inject₁ i) _ e))
  ; anc≢tgt = λ i e → ↑ˡ≢↑ʳ (fromℕ (suc (suc j))) i (sym e)
  ; ctl≢anc = λ i i′ → ↑ˡ≢↑ʳ (inject₁ i) i′
  }

standard-ctl : (n : ℕ) (p : 3 ≤ n) (i : Fin (suc (suc (n ∸ 3)))) →
               toℕ (ctl (standard n p) i) ≡ toℕ i
standard-ctl (suc (suc (suc j))) (s≤s (s≤s (s≤s z≤n))) i =
  trans (Fin.toℕ-↑ˡ (inject₁ i) j) (Fin.toℕ-inject₁ i)

standard-tgt : (n : ℕ) (p : 3 ≤ n) → toℕ (tgt (standard n p)) ≡ n ∸ 1
standard-tgt (suc (suc (suc j))) (s≤s (s≤s (s≤s z≤n))) =
  trans (Fin.toℕ-↑ˡ (fromℕ (suc (suc j))) j) (Fin.toℕ-fromℕ (suc (suc j)))

standard-anc : (n : ℕ) (p : 3 ≤ n) (i : Fin (n ∸ 3)) →
               anc (standard n p) i ≡ n ↑ʳ i
standard-anc (suc (suc (suc j))) (s≤s (s≤s (s≤s z≤n))) i = refl

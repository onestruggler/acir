------------------------------------------------------------------------
-- Presentations of groups
--
-- Reversible circuits of Toffoli and CNOT gates, read classically
--
-- Section 5.2's reversible circuits -- n-bit Toffoli gates, adders --
-- are netlists of Toffoli and CNOT gates, "which are then expanded to
-- the Clifford+T gate set" (PathSum.Toffoli.Netlist does the expansion
-- for netlists of Toffoli gates alone).  Here are such netlists with
-- CNOTs too, read as Boolean functions: a gate xors a bit computed
-- from its controls -- their conjunction for a Toffoli gate (ccx),
-- the one control for a CNOT (cx) -- into its target, which is none of
-- its controls; a netlist applies its gates head first (run).
--
-- What a proof about a netlist needs, generically:
--
-- * a gate writes only its target (⟪⟫-there, run-frame), and reads
--   only its controls and target, so it respects agreement on any set
--   of wires containing them (⟪⟫-local, run-local);
-- * every gate is an involution (⟪⟫-involutive), so a netlist followed
--   by its reverse is the identity (run-reverse);
-- * hence Bennett's compute-copy-uncompute (bennett-work,
--   bennett-out): if every gate of F lies within a set Q of wires, and
--   M changes no wire of Q, then F ++ M ++ reverse F leaves every wire
--   of Q as it was, and on every other wire does what M does after F.
--   The reverse of F undoes F whatever M did outside Q, since F never
--   looks there; the wires outside Q are never written by F.
--
-- Also the gate counts (toffolis, cnots), additive and invariant
-- under reversal.  Everything is stated pointwise: assignments are
-- functions, compared value by value.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Reversible where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; _xor_)
open import Data.Bool.Properties using (xor-assoc; xor-same; xor-identityʳ)
open import Data.Empty using (⊥-elim-irr)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_; _++_; reverse; length)
open import Data.List.Properties using (unfold-reverse)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (∷ʳ⁺)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-suc)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (¬_)

import Data.Fin.Properties as Fin
import Data.List.Relation.Unary.All as All

open import PathSum.Assign using (_[_≔_]; ≔-here; ≔-there; ≔-≔; ≔-self; ≔-cong)

private
  variable
    N : ℕ

  -- Assignments to the wires.

  Bits : ℕ → Set
  Bits N = Fin N → Bool


------------------------------------------------------------------------
-- Gates and netlists

-- A Toffoli gate (controls c₁, c₂, target t) or a CNOT (control c,
-- target t), on distinct wires.  The proofs of distinctness are
-- irrelevant, so that two gates on the same wires are equal however
-- their distinctness was shown.

data Gate (N : ℕ) : Set where
  ccx : (c₁ c₂ t : Fin N) → .(c₁ ≢ c₂) → .(c₁ ≢ t) → .(c₂ ≢ t) → Gate N
  cx  : (c t : Fin N) → .(c ≢ t) → Gate N

-- A negation can be recovered from an irrelevant one.

recover : {A : Set} → .(¬ A) → ¬ A
recover p a = ⊥-elim-irr (p a)

target : Gate N → Fin N
target (ccx _ _ t _ _ _) = t
target (cx _ t _)        = t

-- The bit a gate xors into its target.

control : Gate N → Bits N → Bool
control (ccx c₁ c₂ _ _ _ _) x = x c₁ ∧ x c₂
control (cx c _ _)          x = x c

-- A gate's Boolean function, and a netlist's: the head applied first.

⟪_⟫ : Gate N → Bits N → Bits N
⟪ g ⟫ x = x [ target g ≔ x (target g) xor control g x ]

run : List (Gate N) → Bits N → Bits N
run []       x = x
run (g ∷ gs) x = run gs (⟪ g ⟫ x)

run-++ : (gs hs : List (Gate N)) (x : Bits N) →
         run (gs ++ hs) x ≡ run hs (run gs x)
run-++ []       hs x = refl
run-++ (g ∷ gs) hs x = run-++ gs hs (⟪ g ⟫ x)


------------------------------------------------------------------------
-- What a gate reads and writes

-- It writes its target, and nothing else.

⟪⟫-here : (g : Gate N) (x : Bits N) →
          ⟪ g ⟫ x (target g) ≡ x (target g) xor control g x
⟪⟫-here g x = ≔-here x (target g) (x (target g) xor control g x)

⟪⟫-there : (g : Gate N) (x : Bits N) {w : Fin N} → w ≢ target g →
           ⟪ g ⟫ x w ≡ x w
⟪⟫-there g x w≢t = ≔-there x (x (target g) xor control g x) w≢t

run-frame : (gs : List (Gate N)) (x : Bits N) {w : Fin N} →
            All (λ g → w ≢ target g) gs → run gs x w ≡ x w
run-frame []       x []       = refl
run-frame (g ∷ gs) x (p ∷ ps) =
  trans (run-frame gs (⟪ g ⟫ x) ps) (⟪⟫-there g x p)

-- Its control bit does not read the target ...

control-≔ : (g : Gate N) (x : Bits N) (b : Bool) →
            control g (x [ target g ≔ b ]) ≡ control g x
control-≔ (ccx c₁ c₂ t _ c₁≢t c₂≢t) x b =
  cong₂ _∧_ (≔-there x b (recover c₁≢t)) (≔-there x b (recover c₂≢t))
control-≔ (cx c t c≢t) x b = ≔-there x b (recover c≢t)

-- ... and reads only the controls.  The wires a gate lies within: its
-- controls and its target.

Within : (Fin N → Set) → Gate N → Set
Within Q (ccx c₁ c₂ t _ _ _) = Q c₁ × Q c₂ × Q t
Within Q (cx c t _)          = Q c × Q t

within-target : (Q : Fin N → Set) (g : Gate N) → Within Q g → Q (target g)
within-target Q (ccx _ _ _ _ _ _) (_ , _ , q) = q
within-target Q (cx _ _ _)        (_ , q)     = q

control-local : (Q : Fin N → Set) (g : Gate N) → Within Q g →
                {x x′ : Bits N} → (∀ w → Q w → x w ≡ x′ w) →
                control g x ≡ control g x′
control-local Q (ccx c₁ c₂ _ _ _ _) (q₁ , q₂ , _) h =
  cong₂ _∧_ (h c₁ q₁) (h c₂ q₂)
control-local Q (cx c _ _) (q , _) h = h c q

-- Overwriting one wire preserves agreement at another.

private
  ≔-agree : (x x′ : Bits N) (t : Fin N) (b : Bool) {w : Fin N} →
            x w ≡ x′ w → (x [ t ≔ b ]) w ≡ (x′ [ t ≔ b ]) w
  ≔-agree x x′ t b {w} e = go ⌊ w Fin.≟ t ⌋
    where
    go : ∀ d → (if d then b else x w) ≡ (if d then b else x′ w)
    go true  = refl
    go false = e


------------------------------------------------------------------------
-- Congruence and locality

-- A gate, and a netlist, only reads values.

control-cong : (g : Gate N) {x x′ : Bits N} → (∀ w → x w ≡ x′ w) →
               control g x ≡ control g x′
control-cong (ccx c₁ c₂ _ _ _ _) h = cong₂ _∧_ (h c₁) (h c₂)
control-cong (cx c _ _)          h = h c

⟪⟫-cong : (g : Gate N) {x x′ : Bits N} → (∀ w → x w ≡ x′ w) →
          ∀ w → ⟪ g ⟫ x w ≡ ⟪ g ⟫ x′ w
⟪⟫-cong g {x} {x′} h w =
  trans (cong (λ b → (x [ target g ≔ b ]) w)
              (cong₂ _xor_ (h (target g)) (control-cong g h)))
        (≔-cong (target g) (x′ (target g) xor control g x′) h w)

run-cong : (gs : List (Gate N)) {x x′ : Bits N} → (∀ w → x w ≡ x′ w) →
           ∀ w → run gs x w ≡ run gs x′ w
run-cong []       h = h
run-cong (g ∷ gs) h = run-cong gs (⟪⟫-cong g h)

-- Two assignments that agree on a set of wires containing every
-- control and target of a netlist still agree there after it.

⟪⟫-local : (Q : Fin N → Set) (g : Gate N) → Within Q g →
           {x x′ : Bits N} → (∀ w → Q w → x w ≡ x′ w) →
           ∀ w → Q w → ⟪ g ⟫ x w ≡ ⟪ g ⟫ x′ w
⟪⟫-local Q g p {x} {x′} h w q =
  trans (cong (λ b → (x [ target g ≔ b ]) w)
              (cong₂ _xor_ (h (target g) (within-target Q g p))
                           (control-local Q g p h)))
        (≔-agree x x′ (target g) (x′ (target g) xor control g x′) (h w q))

run-local : (Q : Fin N → Set) (gs : List (Gate N)) → All (Within Q) gs →
            {x x′ : Bits N} → (∀ w → Q w → x w ≡ x′ w) →
            ∀ w → Q w → run gs x w ≡ run gs x′ w
run-local Q []       []       h = h
run-local Q (g ∷ gs) (p ∷ ps) h = run-local Q gs ps (⟪⟫-local Q g p h)


------------------------------------------------------------------------
-- Reversibility

-- Every gate is an involution: the second application xors the same
-- control bit into the target again.

⟪⟫-involutive : (g : Gate N) (x : Bits N) → ∀ w → ⟪ g ⟫ (⟪ g ⟫ x) w ≡ x w
⟪⟫-involutive g x w =
  trans (cong (λ b → ((x [ t ≔ v ]) [ t ≔ b ]) w) back)
    (trans (≔-≔ x t v (x t) w) (≔-self x t w))
  where
  t : Fin _
  t = target g

  k v : Bool
  k = control g x
  v = x t xor k

  cancel : ∀ p q → (p xor q) xor q ≡ p
  cancel p q = trans (xor-assoc p q q)
                     (trans (cong (p xor_) (xor-same q)) (xor-identityʳ p))

  back : (x [ t ≔ v ]) t xor control g (x [ t ≔ v ]) ≡ x t
  back = trans (cong₂ _xor_ (≔-here x t v) (control-≔ g x v)) (cancel (x t) k)

-- So a netlist followed by its reverse is the identity.

run-reverse : (gs : List (Gate N)) (x : Bits N) →
              ∀ w → run (reverse gs) (run gs x) w ≡ x w
run-reverse []       x w = refl
run-reverse (g ∷ gs) x w =
  trans (cong (λ l → run l (run gs (⟪ g ⟫ x)) w) (unfold-reverse g gs))
  (trans (cong (λ f → f w)
               (run-++ (reverse gs) (g ∷ []) (run gs (⟪ g ⟫ x))))
  (trans (⟪⟫-cong g (run-reverse gs (⟪ g ⟫ x)) w)
         (⟪⟫-involutive g x w)))

-- The reverse of a netlist within Q is within Q.

All-reverse : {P : Gate N → Set} {gs : List (Gate N)} → All P gs →
              All P (reverse gs)
All-reverse {gs = []}             []       = []
All-reverse {P = P} {gs = g ∷ gs} (p ∷ ps) =
  subst (All P) (sym (unfold-reverse g gs)) (∷ʳ⁺ (All-reverse ps) p)


------------------------------------------------------------------------
-- Bennett's compute-copy-uncompute

-- F computes within Q; M, run on the result, changes no wire of Q; the
-- reverse of F then undoes F on Q.

bennett-work : (Q : Fin N → Set) (F M : List (Gate N)) →
               All (Within Q) F →
               (∀ u w → Q w → run M u w ≡ u w) →
               ∀ x w → Q w → run (F ++ M ++ reverse F) x w ≡ x w
bennett-work Q F M wF hM x w q =
  trans (cong (λ f → f w) (run-++ F (M ++ reverse F) x))
  (trans (cong (λ f → f w) (run-++ M (reverse F) (run F x)))
  (trans (run-local Q (reverse F) (All-reverse wF)
                    {run M (run F x)} {run F x}
                    (λ w′ q′ → hM (run F x) w′ q′) w q)
         (run-reverse F x w)))

-- Off Q, the reverse of F writes nothing, so what M wrote stays.

bennett-out : (Q : Fin N → Set) (F M : List (Gate N)) →
              All (Within Q) F →
              ∀ x w → ¬ Q w → run (F ++ M ++ reverse F) x w ≡ run M (run F x) w
bennett-out Q F M wF x w nq =
  trans (cong (λ f → f w) (run-++ F (M ++ reverse F) x))
  (trans (cong (λ f → f w) (run-++ M (reverse F) (run F x)))
         (run-frame (reverse F) (run M (run F x))
           (All.map (λ {g} p e → nq (subst Q (sym e) (within-target Q g p)))
                    (All-reverse wF))))


------------------------------------------------------------------------
-- Gate counts

-- A count of gates by kind, additive and invariant under reversal.

count : (Gate N → ℕ) → List (Gate N) → ℕ
count f []       = 0
count f (g ∷ gs) = f g + count f gs

count-++ : (f : Gate N → ℕ) (gs hs : List (Gate N)) →
           count f (gs ++ hs) ≡ count f gs + count f hs
count-++ f []       hs = refl
count-++ f (g ∷ gs) hs =
  trans (cong (f g +_) (count-++ f gs hs)) (sym (+-assoc (f g) _ _))

count-reverse : (f : Gate N → ℕ) (gs : List (Gate N)) →
                count f (reverse gs) ≡ count f gs
count-reverse f []       = refl
count-reverse f (g ∷ gs) =
  trans (cong (count f) (unfold-reverse g gs))
  (trans (count-++ f (reverse gs) (g ∷ []))
  (trans (cong (_+ (f g + 0)) (count-reverse f gs))
  (trans (+-comm (count f gs) (f g + 0))
         (cong (_+ count f gs) (+-comm (f g) 0)))))

-- The Toffoli gates and the CNOTs.

is-ccx is-cx : Gate N → ℕ
is-ccx (ccx _ _ _ _ _ _) = 1
is-ccx (cx _ _ _)        = 0
is-cx  (ccx _ _ _ _ _ _) = 0
is-cx  (cx _ _ _)        = 1

toffolis cnots : List (Gate N) → ℕ
toffolis = count is-ccx
cnots    = count is-cx

-- Every gate is one or the other.

length-count : (gs : List (Gate N)) → length gs ≡ toffolis gs + cnots gs
length-count []                      = refl
length-count (ccx _ _ _ _ _ _ ∷ gs) = cong suc (length-count gs)
length-count (cx _ _ _ ∷ gs)        =
  trans (cong suc (length-count gs)) (sym (+-suc (toffolis gs) (cnots gs)))

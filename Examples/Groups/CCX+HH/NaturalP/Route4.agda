------------------------------------------------------------------------
-- Presentations of groups
--
-- Routing a few points into the window of the top four wires.
--
-- On 4 + m wires, `up4 m` carries the bottom four wires to the top
-- (`up4-act`), and `tr s` adds the vector s (`tr-act`).  Given a base
-- point q₀ and an independent list D of at most four differences,
-- `Route` completes D by unit vectors of the bottom four wires
-- (Span.complete4), routes the completed list onto the unit vectors of
-- the bottom wires (AffineRoute.route, through SpanEmb.embL), and moves
-- those to the top: K = up4 • R • tr q₀ sends q₀ to 0 and a point x
-- with x ⊕ q₀ = D[t] to the t-th unit vector of the top four wires
-- (`K-q₀`, `K-at`), and a point whose difference is a sum of two of D
-- to the sum (`K-at₂`); conversely K⁻¹ carries the whole window into
-- the span of q₀, D and the completing unit vectors (`K-back`).  The width is 4 + k + c: a gate on the top
-- four wires under c controls under k more, whose window coordinates
-- `stack-ιW` identifies.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.Route4 where

open import Data.Bool.Base using (Bool ; true ; false ; _xor_ ; _∧_)
open import Data.Bool.Properties using (xor-identityʳ ; xor-same ; xor-assoc ; xor-comm ; ∧-identityʳ ; ∧-zeroʳ)
open import Data.Fin.Base using (Fin ; zero ; suc ; inject≤ ; _↑ˡ_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _≤_ ; z≤n ; s≤s)
open import Data.Nat.Properties using (≤-trans ; ≤-reflexive ; +-comm)
open import Data.Product.Base using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; _++_ ; lookup ; map ; tabulate)
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₄₊)

import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_ ; lower)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (zeros ; cons-cong ; cons-view)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (cons ; idx ; idx-cong)
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (ι)
open import Examples.Groups.CCX+HH.NaturalP.AffineWords using (AGen ; ax ; asw ; _↥ₐ ; inv)
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute
  using (A⟦_⟧ ; A-cong ; A-↑ ; A-inv ; _↑ₐ ; _⊕_ ; unit ; flip0 ; Lin ; lin-zero ; word-lin ; u′ ; route
        ; route-zero ; route-ok)
open import Examples.Groups.CCX+HH.NaturalP.Span using (Indep ; InSpan ; comb ; scale ; e4 ; Fill ; Full ; complete4)
open import Examples.Groups.CCX+HH.NaturalP.SpanEmb using (indep-swap ; embL ; embL-unit)
open import Examples.Groups.CCX+HH.NaturalP.AtCalc using (ιW)

private
  variable
    n m c : ℕ

------------------------------------------------------------------------
-- Adding a vector

bitX : Bool → Word (AGen (suc n))
bitX true  = [ ax ]ʷ
bitX false = ε

tr : State n → Word (AGen n)
tr {zero}  s = ε
tr {suc n} s = bitX (s zero) • (tr (lower s) ↑ₐ)

private
  bitX-act : (b : Bool) (y : State (suc n)) → A⟦ bitX b ⟧ y ≈s flip0 b y
  bitX-act true  y zero    = refl
  bitX-act true  y (suc i) = refl
  bitX-act false y zero    = sym (xor-identityʳ (y zero))
  bitX-act false y (suc i) = refl

tr-act : (s x : State n) → A⟦ tr s ⟧ x ≈s x ⊕ s
tr-act {suc n} s x i =
  trans (A-cong (bitX (s zero)) up i) (trans (bitX-act (s zero) _ i) (fin i))
  where
  up : A⟦ tr (lower s) ↑ₐ ⟧ x ≈s cons (x zero) (lower x ⊕ lower s)
  up j = trans (A-cong (tr (lower s) ↑ₐ) (λ y → sym (cons-view x y)) j)
    (trans (A-↑ (tr (lower s)) (x zero) (lower x) j)
      (cons-cong refl (tr-act (lower s) (lower x)) j))
  fin : flip0 (s zero) (cons (x zero) (lower x ⊕ lower s)) ≈s x ⊕ s
  fin zero    = refl
  fin (suc j) = refl

------------------------------------------------------------------------
-- The bottom four wires to the top

-- Wire 4 down to wire 0, the bottom four wires one up.
S4 : Word (AGen (suc (₄₊ m)))
S4 = [ asw ]ʷ • ([ asw ↥ₐ ]ʷ • ([ asw ↥ₐ ↥ₐ ]ʷ • [ asw ↥ₐ ↥ₐ ↥ₐ ]ʷ))

up4 : ∀ m → Word (AGen (₄₊ m))
up4 zero    = ε
up4 (suc m) = (up4 m ↑ₐ) • S4

-- h on the bottom four wires, r above.
bot : State 4 → State m → State (₄₊ m)
bot h r = cons (h zero) (cons (h (suc zero)) (cons (h (suc (suc zero)))
  (cons (h (suc (suc (suc zero)))) r)))

-- r on the bottom m wires, h above.
stack : ∀ m → State m → State 4 → State (₄₊ m)
stack zero    r h = h
stack (suc m) r h = cons (r zero) (stack m (lower r) h)

private
  S4-act : (h : State 4) (r : State (suc m)) → A⟦ S4 {m} ⟧ (bot h r) ≈s cons (r zero) (bot h (lower r))
  S4-act h r zero                                = refl
  S4-act h r (suc zero)                          = refl
  S4-act h r (suc (suc zero))                    = refl
  S4-act h r (suc (suc (suc zero)))              = refl
  S4-act h r (suc (suc (suc (suc zero))))        = refl
  S4-act h r (suc (suc (suc (suc (suc j)))))     = refl

up4-act : ∀ m (h : State 4) (r : State m) → A⟦ up4 m ⟧ (bot h r) ≈s stack m r h
up4-act zero    h r zero                       = refl
up4-act zero    h r (suc zero)                 = refl
up4-act zero    h r (suc (suc zero))           = refl
up4-act zero    h r (suc (suc (suc zero)))     = refl
up4-act (suc m) h r j =
  trans (A-cong (up4 m ↑ₐ) (S4-act h r) j)
    (trans (A-↑ (up4 m) (r zero) (bot h (lower r)) j)
      (cons-cong refl (up4-act m h (lower r)) j))

------------------------------------------------------------------------
-- The window coordinates

-- H above m zeros.
stackz : ∀ m → State (₄₊ c) → State (₄₊ (m + c))
stackz zero    H = H
stackz (suc m) H = cons false (stackz m H)

stackz-ιW : ∀ k c (H : State (₄₊ c)) → ι (ιW k c) (idx (₄₊ c) H) ≡ idx (₄₊ (k + c)) (stackz k H)
stackz-ιW zero    c H = refl
stackz-ιW (suc k) c H = cong (ι (ιW 1 (k + c))) (stackz-ιW k c H)

-- h on the top four of 4 + k + c wires, as a coordinate of the window
-- of a gate under c controls under k more.  The inner block has width
-- 4 + (c + 0), as `Λw c` makes it, so that nothing here is compared at
-- a concrete width: there `idx` unfolds to the partitions of
-- EncodingSemantics/Binary at their concrete sizes, which is ruinous.
stack-ιW : ∀ k c (h : State 4) →
  ι (ιW k (c + 0)) (ι (ιW c 0) (idx 4 h)) ≡ idx (₄₊ (k + (c + 0))) (stack (k + (c + 0)) zeros h)
stack-ιW k c h =
  trans (cong (ι (ιW k (c + 0))) (stackz-ιW c 0 h))
    (trans (stackz-ιW k (c + 0) (stackz c h)) (idx-cong (₄₊ (k + (c + 0))) (λ j → sym (st k j))))
  where
  base : ∀ c → stack (c + 0) zeros h ≈s stackz {0} c h
  base zero    j       = refl
  base (suc c) zero    = refl
  base (suc c) (suc j) = base c j
  st : ∀ k → stack (k + (c + 0)) zeros h ≈s stackz k (stackz c h)
  st zero    j       = base c j
  st (suc k) zero    = refl
  st (suc k) (suc j) = st k j

------------------------------------------------------------------------
-- Routing

private
  u′-unit : ∀ {k m} (le : k ≤ m) (i : Fin k) → u′ le i ≈s unit (inject≤ i le)
  u′-unit (s≤s le) zero    zero    = refl
  u′-unit (s≤s le) zero    (suc x) = refl
  u′-unit (s≤s le) (suc i) zero    = refl
  u′-unit (s≤s le) (suc i) (suc x) = u′-unit le i x

  bot-zeros : zeros ≈s bot {m} zeros zeros
  bot-zeros zero                         = refl
  bot-zeros (suc zero)                   = refl
  bot-zeros (suc (suc zero))             = refl
  bot-zeros (suc (suc (suc zero)))       = refl
  bot-zeros (suc (suc (suc (suc j))))    = refl

------------------------------------------------------------------------
-- Linear combinations through the routing

private
  lin-comb : ∀ {n m l} {F : State n → State m} → Lin F → (vs : Vec (State n) l) (as : Vec Bool l) →
    F (comb vs as) ≈s comb (map F vs) as
  lin-comb LF []       []       = lin-zero LF
  lin-comb {F = F} LF (v ∷ vs) (a ∷ as) i =
    trans (Lin.add LF (scale a v) (comb vs as) i) (cong₂ _xor_ (sc a i) (lin-comb LF vs as i))
    where
    sc : ∀ a → F (scale a v) ≈s scale a (F v)
    sc true  j = Lin.resp LF (λ _ → refl) j
    sc false j = trans (Lin.resp LF (λ _ → refl) j) (lin-zero LF j)

  comb-resp : ∀ {n l} (vs ws : Vec (State n) l) → (∀ i → lookup vs i ≈s lookup ws i) →
    ∀ as → comb vs as ≈s comb ws as
  comb-resp []       []       e []       i = refl
  comb-resp (v ∷ vs) (w ∷ ws) e (a ∷ as) i =
    cong₂ _xor_ (cong (a ∧_) (e zero i)) (comb-resp vs ws (λ t → e (suc t)) as i)

  q0 : ∀ a b c d → (a ∧ true) xor ((b ∧ false) xor ((c ∧ false) xor ((d ∧ false) xor false))) ≡ a
  q0 a b c d rewrite ∧-identityʳ a | ∧-zeroʳ b | ∧-zeroʳ c | ∧-zeroʳ d = xor-identityʳ a
  q1 : ∀ a b c d → (a ∧ false) xor ((b ∧ true) xor ((c ∧ false) xor ((d ∧ false) xor false))) ≡ b
  q1 a b c d rewrite ∧-zeroʳ a | ∧-identityʳ b | ∧-zeroʳ c | ∧-zeroʳ d = xor-identityʳ b
  q2 : ∀ a b c d → (a ∧ false) xor ((b ∧ false) xor ((c ∧ true) xor ((d ∧ false) xor false))) ≡ c
  q2 a b c d rewrite ∧-zeroʳ a | ∧-zeroʳ b | ∧-identityʳ c | ∧-zeroʳ d = xor-identityʳ c
  q3 : ∀ a b c d → (a ∧ false) xor ((b ∧ false) xor ((c ∧ false) xor ((d ∧ true) xor false))) ≡ d
  q3 a b c d rewrite ∧-zeroʳ a | ∧-zeroʳ b | ∧-zeroʳ c | ∧-identityʳ d = xor-identityʳ d
  qz : ∀ a b c d → (a ∧ false) xor ((b ∧ false) xor ((c ∧ false) xor ((d ∧ false) xor false))) ≡ false
  qz a b c d rewrite ∧-zeroʳ a | ∧-zeroʳ b | ∧-zeroʳ c | ∧-zeroʳ d = refl

  -- With exactly four of them, the unit vectors of the bottom wires span
  -- every state there.
  units-cover : ∀ {M} len → len ≡ 4 → (le : len ≤ ₄₊ M) (h : State 4) →
    Σ (Vec Bool len) λ as → comb (tabulate (λ i → unit (inject≤ i le))) as ≈s bot h zeros
  units-cover .4 refl le h = (h0 ∷ h1 ∷ h2 ∷ h3 ∷ []) , pt
    where
    h0 = h zero
    h1 = h (suc zero)
    h2 = h (suc (suc zero))
    h3 = h (suc (suc (suc zero)))
    pt : comb (tabulate (λ i → unit (inject≤ i le))) (h0 ∷ h1 ∷ h2 ∷ h3 ∷ []) ≈s bot h zeros
    pt zero                      = q0 h0 h1 h2 h3
    pt (suc zero)                = q1 h0 h1 h2 h3
    pt (suc (suc zero))          = q2 h0 h1 h2 h3
    pt (suc (suc (suc zero)))    = q3 h0 h1 h2 h3
    pt (suc (suc (suc (suc i)))) = qz h0 h1 h2 h3

  tr-inv-act : ∀ {n} (s x : State n) → A⟦ inv (tr s) ⟧ x ≈s x ⊕ s
  tr-inv-act s x i =
    trans (A-cong (inv (tr s)) (λ j → sym (trans (tr-act s (x ⊕ s) j) (back j))) i)
      (A-inv (tr s) (x ⊕ s) i)
    where
    back : (x ⊕ s) ⊕ s ≈s x
    back j = trans (xor-assoc (x j) (s j) (s j))
      (trans (cong (x j xor_) (xor-same (s j))) (xor-identityʳ (x j)))

  inv-zero : ∀ {n} (w : Word (AGen n)) → A⟦ w ⟧ zeros ≈s zeros → A⟦ inv w ⟧ zeros ≈s zeros
  inv-zero w z i = trans (A-cong (inv w) (λ j → sym (z j)) i) (A-inv w zeros i)

module Route (k c : ℕ) {d : ℕ} (q₀ : State (₄₊ (k + (c + 0))))
             (D : Vec (State (₄₊ (k + (c + 0)))) d) (ind : Indep D) (le : d ≤ 4) where

  private
    N : ℕ
    N = ₄₊ (k + (c + 0))

  -- The completion, opaque: its search is never worth unfolding.
  opaque
    fl : Fill D
    fl = proj₁ (complete4 D ind le)

    full : Full fl
    full = proj₂ (complete4 D ind le)

  j : ℕ
  j = Fill.j fl

  -- D, then the unit vectors that complete it.
  L : Vec (State N) (d + j)
  L = D ++ map e4 (Fill.F fl)

  indL : Indep L
  indL = indep-swap {xs = map e4 (Fill.F fl)} {ys = D} (Fill.indep fl)

  leL : d + j ≤ N
  leL = ≤-trans (≤-reflexive (+-comm d j))
    (≤-trans (Fill.bound fl) (s≤s (s≤s (s≤s (s≤s z≤n)))))

  R : Word (AGen N)
  R = route leL (embL L indL)

  K : Word (AGen N)
  K = up4 (k + (c + 0)) • (R • tr q₀)

  R-lin : Lin A⟦ R ⟧
  R-lin = word-lin R (route-zero leL (embL L indL))

  R-L : (i : Fin (d + j)) → A⟦ R ⟧ (lookup L i) ≈s unit (inject≤ i leL)
  R-L i x =
    trans (A-cong R (λ y → sym (embL-unit L indL i y)) x)
      (trans (route-ok leL (embL L indL) i x) (u′-unit leL i x))

  R-D : (t : Fin d) → A⟦ R ⟧ (lookup D t) ≈s unit (inject≤ (t ↑ˡ j) leL)
  R-D t x =
    trans (A-cong R (λ y → cong (λ v → v y) (sym (VecP.lookup-++ˡ D (map e4 (Fill.F fl)) t))) x)
      (R-L (t ↑ˡ j) x)

  private
    up-stack : (h : State 4) {y : State N} → y ≈s bot h zeros →
      A⟦ up4 (k + (c + 0)) ⟧ y ≈s stack (k + (c + 0)) zeros h
    up-stack h e x = trans (A-cong (up4 (k + (c + 0))) e x) (up4-act (k + (c + 0)) h zeros x)

  K-q₀ : A⟦ K ⟧ q₀ ≈s stack (k + (c + 0)) zeros zeros
  K-q₀ = up-stack zeros λ x →
    trans (A-cong R (λ y → trans (tr-act q₀ q₀ y) (xor-same (q₀ y))) x)
      (trans (route-zero leL (embL L indL) x) (bot-zeros x))

  -- A point x with x ⊕ q₀ = D[t].
  K-at : (x : State N) (t : Fin d) (h : State 4) → x ⊕ q₀ ≈s lookup D t →
    unit (inject≤ (t ↑ˡ j) leL) ≈s bot h zeros → A⟦ K ⟧ x ≈s stack (k + (c + 0)) zeros h
  K-at x t h e eh = up-stack h λ y →
    trans (A-cong R (λ z → trans (tr-act q₀ x z) (e z)) y) (trans (R-D t y) (eh y))

  -- A point x with x ⊕ q₀ = D[t] ⊕ D[t′].
  K-at₂ : (x : State N) (t t′ : Fin d) (h : State 4) → x ⊕ q₀ ≈s lookup D t ⊕ lookup D t′ →
    unit (inject≤ (t ↑ˡ j) leL) ⊕ unit (inject≤ (t′ ↑ˡ j) leL) ≈s bot h zeros →
    A⟦ K ⟧ x ≈s stack (k + (c + 0)) zeros h
  K-at₂ x t t′ h e eh = up-stack h λ y →
    trans (A-cong R (λ z → trans (tr-act q₀ x z) (e z)) y)
    (trans (Lin.add R-lin (lookup D t) (lookup D t′) y)
    (trans (cong₂ _xor_ (R-D t y) (R-D t′ y)) (eh y)))

  private
    dj4 : d + j ≡ 4
    dj4 = trans (+-comm d j) full
    Rinv-lin : Lin A⟦ inv R ⟧
    Rinv-lin = word-lin (inv R) (inv-zero R (route-zero leL (embL L indL)))

  -- The window comes back into the span of q₀ and L.
  K-back : (h : State 4) → InSpan (q₀ ∷ L) (A⟦ inv K ⟧ (stack (k + (c + 0)) zeros h))
  K-back h = (true ∷ as) , λ i → trans (xor-comm (q₀ i) (comb L as i)) (sym (chain i))
    where
    cv = units-cover (d + j) dj4 leL h
    as = proj₁ cv
    units = tabulate (λ i → unit (inject≤ i leL))
    up-back : A⟦ inv (up4 (k + (c + 0))) ⟧ (stack (k + (c + 0)) zeros h) ≈s bot h zeros
    up-back i = trans (A-cong (inv (up4 (k + (c + 0)))) (λ y → sym (up4-act (k + (c + 0)) h zeros y)) i)
      (A-inv (up4 (k + (c + 0))) (bot h zeros) i)
    inner : A⟦ inv R ⟧ (A⟦ inv (up4 (k + (c + 0))) ⟧ (stack (k + (c + 0)) zeros h)) ≈s comb L as
    inner i =
      trans (A-cong (inv R) (λ y → trans (up-back y) (sym (proj₂ cv y))) i)
      (trans (lin-comb Rinv-lin units as i)
        (comb-resp (map A⟦ inv R ⟧ units) L
          (λ t y → trans (cong (λ v → v y) (VecP.lookup-map t A⟦ inv R ⟧ units))
                   (trans (cong (λ u → A⟦ inv R ⟧ u y) (VecP.lookup∘tabulate (λ i → unit (inject≤ i leL)) t))
                   (trans (A-cong (inv R) (λ z → sym (R-L t z)) y) (A-inv R (lookup L t) y))))
          as i))
    chain : A⟦ inv K ⟧ (stack (k + (c + 0)) zeros h) ≈s comb L as ⊕ q₀
    chain i = trans (tr-inv-act q₀ _ i) (cong (_xor q₀ i) (inner i))

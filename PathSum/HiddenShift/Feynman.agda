------------------------------------------------------------------------
-- Presentations of groups
--
-- The hidden shift benchmarks exactly as the paper's tool generates
-- them, gate for gate, for every draw (Amy, QPL 2018, section 5.2 and
-- table 2)
--
-- The paper's tool, Feynman (github.com/meamy/feynman), generated the
-- circuits it verified as table 2's Hidden Shift and Symbolic Shift
-- rows with QuickCheck, in src/Feynman/Verification/SOP.hs as of the
-- paper:
--
--    genCCZ xs = do x <- elements xs; y <- elements (xs \\ [x])
--                   z <- elements (xs \\ [x, y]); return (ccz x y z)
--    genCZ xs  = do x <- elements xs; y <- elements (xs \\ [x])
--                   return (cz x y)
--    genZ xs   = do x <- elements xs; return [Z x]
--    genMaioranaG xs 0 = return []
--    genMaioranaG xs i = do
--      ccz   <- genCCZ xs
--      cliff <- replicateM 200 $ oneof [genCZ xs, genZ xs]
--      next  <- genMaioranaG xs (i-1)
--      return $ concat (ccz:cliff) ++ next
--    hiddenShift n alternations = do
--      s <- sublistOf vars
--      g <- genMaioranaG (take n2 vars) alternations
--      let hTrans = map H vars
--          xTrans = map X s
--          cTrans = concat [cz (vars!!i) (vars!!(i + n2)) | i <- [0..n2-1]]
--          sub = Map.fromList $ zip (take n2 vars) (drop n2 vars)
--          f' = (Core.subst sub g) ++ cTrans
--          f  = xTrans ++ g ++ cTrans ++ xTrans
--      return (hTrans ++ f ++ hTrans ++ f' ++ hTrans, s)
--      where n2 = n `div` 2
--            vars = ["x" ++ show i | i <- [0..n-1]]
--
-- and hiddenShiftQuantum n alternations the same with
-- xTrans = [CNOT ("y" ++ show i) ("x" ++ show i) | i <- [0..n-1]] and
-- no s; ccz and cz are src/Feynman/Core.hs's (ccz x y z the fourteen
-- gates of PathSum.HiddenShift.ToolCCZ; cz x y = [S x, S y, CNOT x y,
-- S† y, CNOT x y]), and Core.subst renames the wires of every gate
-- (substGate).
--
-- The transcription.  The generators are monadic: they make random
-- draws.  Here they are functions of their draws: the shift s (a list
-- of wires) and, for each alternation, the wires of its ccz and its
-- draws (Altᵀ, Pickᵀ); genMaioranaGᵀ, hiddenShiftᵀ and
-- hiddenShiftQuantumᵀ are the generators' bodies on those draws.  The
-- gates are Feynman.Core's Primitive with the wires numbered (Prim):
-- x_i is wire i and y_i wire n + i, so vars is upTo n and vars !! i is
-- i, and the map Map.fromList (zip (take n2 vars) (drop n2 vars)),
-- read with Map.findWithDefault x x as Core.subst does, sends x_i to
-- x_(n2+i) for i < n2 and every other wire to itself (subᵀ).  Prim
-- departs from the tool's Primitive in its constructors: it omits Y,
-- Swap, Rz, Rx and Ry, which these circuits never produce (and on Rz,
-- Rx, Ry printVerStats has no case), and adds R′ and R†′, for the
-- rotations R_k (k other than 1, 2, 3) and R_k† (k other than 2, 3),
-- which prim could write but these circuits never use.  The rest is
-- verbatim, including two quirks of the tool's code that do not
-- matter here: Core.substGate sends X x to H (f x) (substGateᵀ), but
-- g has no X gate; and n2 = n `div` 2 (⌊ n /2⌋), so the circuits are
-- meant for even n, which is the only case stated below.  A run of the
-- tool's own functions under GHC 9.10 and QuickCheck 2.15 (copied
-- verbatim, with deterministic variants that take the draws as
-- arguments, and instrumented generators of the same monadic shape
-- that return the draws: on 156 seeds each the deterministic variant
-- on the instrumented draws is the random generator's circuit) checked
-- this transcription: its lists are the ones below (HS-tool-6, …).
--
-- The order within an alternation is the tool's: genMaioranaG draws
-- the ccz first and then its 200 cz and Z gates, where the paper's text
-- describes "200 random Z and controlled-Z gates, then a random doubly
-- controlled-Z gate".  The gates are diagonal and commute, so g is the
-- same function either way, and the counts are the same.
--
-- The theorems: read as the tool writes gates (prim), the circuits of
-- PathSum.HiddenShift.Tool and PathSum.HiddenShift.ToolSymbolic are,
-- for every m, every shift and every draw, the tool's lists on n = 2m
-- (prim-HSᵗ, prim-SSᵗ):
--
--    map prim (HSᵗ s Bs) ≡ hiddenShiftᵀ (m + m) (shiftᵀ s) (altsᵀ Bs)
--    map prim (SSᵗ Bs)   ≡ hiddenShiftQuantumᵀ (m + m) (altsᵀ Bs)
--
-- the typed draws read as the tool's (shiftᵀ: the wires where s is 1,
-- in order, as sublistOf returns them; altsᵀ: each block's wires and
-- draws).  The proof is by the structure of the circuits -- the
-- Hadamard layer, the X layer, the CNOT layer, cTrans, g and its
-- substitution, each the tool's list -- and never evaluates a closed
-- circuit.  Its closed instances (HS-tool-6, HS-tool-4, SS-tool-6,
-- SS-tool-4) are the lists the tool's functions printed for small
-- hand-made draws (blocks of two draws, where the tool draws 200).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Feynman (M₀ : ℕ) where

open import Data.Bool.Base using (true; false; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (toℕ-↑ˡ; toℕ-↑ʳ; toℕ<n)
open import Data.List.Base using
  (List; []; _∷_; _++_; map; concat; tabulate; applyUpTo; upTo)
open import Data.List.Properties using (map-++; map-cong)
open import Data.Nat.Base using (zero; suc; _+_; _<_; _<ᵇ_; ⌊_/2⌋)
open import Data.Nat.Properties using (+-comm; n≡⌊n+n/2⌋; <⇒<ᵇ)
open import Data.Vec.Base using (toList)
import Data.Vec.Base as V
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift.Circuit M₀ using (pairs; cross)
open import PathSum.HiddenShift.Gates M₀ using
  (mapTerm; oracle; lift; upper)
open import PathSum.HiddenShift.Layers M₀ using (hadamards)
open import PathSum.HiddenShift.LayersX M₀ using (sel; flipsˣ)
open import PathSum.HiddenShift.Symbolic M₀ using (cnots)
open import PathSum.HiddenShift.Tool M₀ using
  (Draw; CZᵈ; Zᵈ; Block; block; drawTerm; gᶜ; gˡ; gʳ; cTᶜ; hTˣ; fˣ; f′ˣ;
   HSᵗ)
open import PathSum.HiddenShift.ToolSymbolic M₀ using
  (xTˢ; hTˢ; fˢ; f′ˢ; SSᵗ)

private
  M : ℕ
  M = suc (suc (suc M₀))

import PathSum.CRK.Circuit

private
  module CRK = PathSum.CRK.Circuit M

open import PathSum.CRK.WithX M₀ using
  (Gate; H; X; CNOT; R; R†; Circuit; embed)

private
  variable
    n k l m d : ℕ


------------------------------------------------------------------------
-- The tool's gates

-- Feynman.Core's Primitive on numbered wires: H, X, Z, S, S† (Sinv),
-- T, T† (Tinv) and CNOT; R′ and R†′ write the other rotations R_k,
-- R_k†, which the tool's circuits here never contain.

data Prim : Set where
  H′ X′ Z′ S′ Sinv′ T′ Tinv′ : ℕ → Prim
  CNOT′                      : ℕ → ℕ → Prim
  R′ R†′                     : ℕ → ℕ → Prim

-- Z = R₁, S = R₂, T = R₃, as the tool writes them.

Rᵀ R†ᵀ : ℕ → ℕ → Prim
Rᵀ 1 x  = Z′ x
Rᵀ 2 x  = S′ x
Rᵀ 3 x  = T′ x
Rᵀ k x  = R′ k x
R†ᵀ 2 x = Sinv′ x
R†ᵀ 3 x = Tinv′ x
R†ᵀ k x = R†′ k x

-- A gate as the tool writes it, its wires numbered by f; prim numbers
-- them by toℕ.

primʷ : (Fin n → ℕ) → Gate n → Prim
primʷ f (H w)        = H′ (f w)
primʷ f (X w)        = X′ (f w)
primʷ f (CNOT c t _) = CNOT′ (f c) (f t)
primʷ f (R k w)      = Rᵀ k (f w)
primʷ f (R† k w)     = R†ᵀ k (f w)

prim : Gate n → Prim
prim = primʷ toℕ


------------------------------------------------------------------------
-- The tool's functions

-- Feynman.Core's ccz and cz.

cczᵀ : ℕ → ℕ → ℕ → List Prim
cczᵀ x y z = T′ x ∷ T′ y ∷ T′ z ∷ CNOT′ x y ∷ CNOT′ y z ∷
             CNOT′ z x ∷ Tinv′ x ∷ Tinv′ y ∷ T′ z ∷ CNOT′ y x ∷
             Tinv′ x ∷ CNOT′ y z ∷ CNOT′ z x ∷ CNOT′ x y ∷ []

czᵀ : ℕ → ℕ → List Prim
czᵀ x y = S′ x ∷ S′ y ∷ CNOT′ x y ∷ Sinv′ y ∷ CNOT′ x y ∷ []

-- Feynman.Core's substGate and subst, the map read as a function on
-- wires (X x goes to H (f x), as in the tool's code).

substGateᵀ : (ℕ → ℕ) → Prim → Prim
substGateᵀ f (H′ x)      = H′ (f x)
substGateᵀ f (X′ x)      = H′ (f x)
substGateᵀ f (Z′ x)      = Z′ (f x)
substGateᵀ f (S′ x)      = S′ (f x)
substGateᵀ f (Sinv′ x)   = Sinv′ (f x)
substGateᵀ f (T′ x)      = T′ (f x)
substGateᵀ f (Tinv′ x)   = Tinv′ (f x)
substGateᵀ f (CNOT′ x y) = CNOT′ (f x) (f y)
substGateᵀ f (R′ k x)    = R′ k (f x)
substGateᵀ f (R†′ k x)   = R†′ k (f x)

substᵀ : (ℕ → ℕ) → List Prim → List Prim
substᵀ f = map (substGateᵀ f)

-- The draws: genCZ's cz x y or genZ's Z x, and an alternation, the
-- wires of genCCZ's ccz and the draws after it.

data Pickᵀ : Set where
  czᵖ : ℕ → ℕ → Pickᵀ
  zᵖ  : ℕ → Pickᵀ

pickᵀ : Pickᵀ → List Prim
pickᵀ (czᵖ x y) = czᵀ x y
pickᵀ (zᵖ x)    = Z′ x ∷ []

record Altᵀ : Set where
  constructor alt
  field
    cx cy cz : ℕ
    picks    : List Pickᵀ

-- genMaioranaG on its draws.

genMaioranaGᵀ : List Altᵀ → List Prim
genMaioranaGᵀ []                   = []
genMaioranaGᵀ (alt x y z ps ∷ as) =
  concat (cczᵀ x y z ∷ map pickᵀ ps) ++ genMaioranaGᵀ as

-- x_i ↦ x_(n2+i) for i < n2.

subᵀ : ℕ → ℕ → ℕ
subᵀ n2 i = if i <ᵇ n2 then n2 + i else i

-- hiddenShift on its draws, n2 given.

hsᵀ : ℕ → ℕ → List ℕ → List Altᵀ → List Prim
hsᵀ n n2 s as = hTrans ++ f ++ hTrans ++ f′ ++ hTrans
  where
  vars g hTrans xTrans cTrans f′ f : List _
  vars   = upTo n
  g      = genMaioranaGᵀ as
  hTrans = map H′ vars
  xTrans = map X′ s
  cTrans = concat (map (λ i → czᵀ i (i + n2)) (upTo n2))
  f′     = substᵀ (subᵀ n2) g ++ cTrans
  f      = xTrans ++ g ++ cTrans ++ xTrans

hiddenShiftᵀ : ℕ → List ℕ → List Altᵀ → List Prim
hiddenShiftᵀ n = hsᵀ n ⌊ n /2⌋

-- hiddenShiftQuantum on its draws, n2 given.

hsqᵀ : ℕ → ℕ → List Altᵀ → List Prim
hsqᵀ n n2 as = hTrans ++ f ++ hTrans ++ f′ ++ hTrans
  where
  vars g hTrans xTrans cTrans f′ f : List _
  vars   = upTo n
  g      = genMaioranaGᵀ as
  hTrans = map H′ vars
  xTrans = map (λ i → CNOT′ (n + i) i) (upTo n)
  cTrans = concat (map (λ i → czᵀ i (i + n2)) (upTo n2))
  f′     = substᵀ (subᵀ n2) g ++ cTrans
  f      = xTrans ++ g ++ cTrans ++ xTrans

hiddenShiftQuantumᵀ : ℕ → List Altᵀ → List Prim
hiddenShiftQuantumᵀ n = hsqᵀ n ⌊ n /2⌋


------------------------------------------------------------------------
-- The typed draws, read as the tool's

-- A draw and an alternation with their wires numbered by w.

pickOf : (Fin m → ℕ) → Draw m → Pickᵀ
pickOf w (CZᵈ a b _) = czᵖ (w a) (w b)
pickOf w (Zᵈ a)      = zᵖ (w a)

altOf : (Fin m → ℕ) → Block d m → Altᵀ
altOf w (block a b c _ _ _ ds) =
  alt (w a) (w b) (w c) (map (pickOf w) (toList ds))

-- The tool's draws: the blocks with their wires numbered, and the
-- shift as the list of its wires in order.

altsᵀ : List (Block d m) → List Altᵀ
altsᵀ = map (altOf toℕ)

shiftᵀ : Assign n → List ℕ
shiftᵀ s = map toℕ (sel s)

-- Only the wires' numbers matter.

altOf-cong : {w w′ : Fin m → ℕ} → (∀ i → w i ≡ w′ i) →
             (B : Block d m) → altOf w B ≡ altOf w′ B
altOf-cong {w = w} {w′} h (block a b c _ _ _ ds) =
  trans (cong₂ (λ x y → alt x y (w c) (map (pickOf w) (toList ds))) (h a) (h b))
        (cong₂ (λ z ps → alt (w′ a) (w′ b) z ps) (h c)
               (map-cong pick (toList ds)))
  where
  pick : ∀ D → pickOf w D ≡ pickOf w′ D
  pick (CZᵈ x y _) = cong₂ czᵖ (h x) (h y)
  pick (Zᵈ x)      = cong zᵖ (h x)


------------------------------------------------------------------------
-- Lists

-- A tabulation is a map over upTo, read through toℕ.

tab-applyUpTo : {A : Set} (G : Fin k → A) (F : ℕ → A) (h : ℕ → ℕ) →
                (∀ i → G i ≡ F (h (toℕ i))) →
                tabulate G ≡ map F (applyUpTo h k)
tab-applyUpTo {k = zero}  G F h e = refl
tab-applyUpTo {k = suc k} G F h e =
  cong₂ _∷_ (e zero)
    (tab-applyUpTo (λ i → G (suc i)) F (λ j → h (suc j)) (λ i → e (suc i)))

tab-upTo : {A : Set} (G : Fin k → A) (F : ℕ → A) →
           (∀ i → G i ≡ F (toℕ i)) → tabulate G ≡ map F (upTo k)
tab-upTo G F e = tab-applyUpTo G F (λ j → j) e

-- The tool's substitution on the first n2 wires.

sub-< : ∀ n2 i → i < n2 → subᵀ n2 i ≡ n2 + i
sub-< n2 i lt with i <ᵇ n2 | <⇒<ᵇ lt
... | true  | _  = refl
... | false | ()


------------------------------------------------------------------------
-- Circuits over {H, CNOT, R_k, R_k†}, as the tool writes them

-- An embedded circuit, its wires numbered by f.

primᶜ : (Fin n → ℕ) → CRK.Circuit n → List Prim
primᶜ f C = map (primʷ f) (map embed C)

primᶜ-++ : (f : Fin n → ℕ) (C D : CRK.Circuit n) →
           primᶜ f (C ++ D) ≡ primᶜ f C ++ primᶜ f D
primᶜ-++ f C D = trans (cong (map (primʷ f)) (map-++ embed C D))
                       (map-++ (primʷ f) (map embed C) (map embed D))

-- Moving a circuit renumbers its wires.

L-lift : (f : Fin (suc n) → ℕ) (C : CRK.Circuit n) →
         primᶜ f (lift C) ≡ primᶜ (λ w → f (suc w)) C
L-lift f []                   = refl
L-lift f (CRK.H w ∷ C)        = cong (H′ (f (suc w)) ∷_) (L-lift f C)
L-lift f (CRK.CNOT c t _ ∷ C) =
  cong (CNOT′ (f (suc c)) (f (suc t)) ∷_) (L-lift f C)
L-lift f (CRK.R k w ∷ C)      = cong (Rᵀ k (f (suc w)) ∷_) (L-lift f C)
L-lift f (CRK.R† k w ∷ C)     = cong (R†ᵀ k (f (suc w)) ∷_) (L-lift f C)

L-upper : (f : Fin (k + l) → ℕ) (C : CRK.Circuit k) →
          primᶜ f (upper l C) ≡ primᶜ (λ w → f (w ↑ˡ l)) C
L-upper         f []                   = refl
L-upper {l = l} f (CRK.H w ∷ C)        =
  cong (H′ (f (w ↑ˡ l)) ∷_) (L-upper f C)
L-upper {l = l} f (CRK.CNOT c t _ ∷ C) =
  cong (CNOT′ (f (c ↑ˡ l)) (f (t ↑ˡ l)) ∷_) (L-upper f C)
L-upper {l = l} f (CRK.R k w ∷ C)      =
  cong (Rᵀ k (f (w ↑ˡ l)) ∷_) (L-upper f C)
L-upper {l = l} f (CRK.R† k w ∷ C)     =
  cong (R†ᵀ k (f (w ↑ˡ l)) ∷_) (L-upper f C)

-- The Hadamard layer: H on every wire, in order.

L-hadamards : (f : Fin n → ℕ) →
              primᶜ f (hadamards n) ≡ tabulate (λ i → H′ (f i))
L-hadamards {zero}  f = refl
L-hadamards {suc n} f = cong (H′ (f zero) ∷_)
  (trans (L-lift f (hadamards n)) (L-hadamards (λ w → f (suc w))))

-- The CNOT layer of PathSum.HiddenShift.Symbolic: CNOT from the
-- control k + ρ i to the target i, in order of i.

L-cnots : (f : Fin (k + l) → ℕ) (ρ : Fin k → Fin l) →
          primᶜ f (cnots ρ) ≡
          tabulate (λ i → CNOT′ (f (k ↑ʳ ρ i)) (f (i ↑ˡ l)))
L-cnots {zero}  f ρ = refl
L-cnots {suc k} f ρ = cong (CNOT′ (f (suc (k ↑ʳ ρ zero))) (f zero) ∷_)
  (trans (L-lift f (cnots (λ i → ρ (suc i))))
         (L-cnots (λ w → f (suc w)) (λ i → ρ (suc i))))

-- A CZ between ℓ i and r i for every i, in order: the tool's cTrans.

L-pairs : (f : Fin n → ℕ) (ℓ r : Fin k → Fin n) (p : ∀ i → ℓ i ≢ r i) →
          primᶜ f (oracle (pairs ℓ r p)) ≡
          concat (tabulate (λ i → czᵀ (f (ℓ i)) (f (r i))))
L-pairs {k = zero}  f ℓ r p = refl
L-pairs {k = suc k} f ℓ r p = cong (czᵀ (f (ℓ zero)) (f (r zero)) ++_)
  (L-pairs f (λ i → ℓ (suc i)) (λ i → r (suc i)) (λ i → p (suc i)))

-- The draws of an alternation: the tool's cz or Z for each.

L-draws : (f : Fin n → ℕ) (ρ : Fin m → Fin n)
          (inj : ∀ {a b} → ρ a ≡ ρ b → a ≡ b) (ds : List (Draw m)) →
          primᶜ f (oracle (map (mapTerm ρ inj) (map drawTerm ds))) ≡
          concat (map pickᵀ (map (pickOf (λ i → f (ρ i))) ds))
L-draws f ρ inj []               = refl
L-draws f ρ inj (CZᵈ a b _ ∷ ds) =
  cong (czᵀ (f (ρ a)) (f (ρ b)) ++_) (L-draws f ρ inj ds)
L-draws f ρ inj (Zᵈ a ∷ ds)      = cong (Z′ (f (ρ a)) ∷_) (L-draws f ρ inj ds)

-- g: for each alternation the tool's ccz, then its draws.

L-g : (f : Fin n → ℕ) (ρ : Fin m → Fin n)
      (inj : ∀ {a b} → ρ a ≡ ρ b → a ≡ b) (Bs : List (Block d m)) →
      primᶜ f (gᶜ ρ inj Bs) ≡ genMaioranaGᵀ (map (altOf (λ i → f (ρ i))) Bs)
L-g f ρ inj []                          = refl
L-g f ρ inj (block a b c p q r ds ∷ Bs) =
  cong (cczᵀ (f (ρ a)) (f (ρ b)) (f (ρ c)) ++_)
    (trans (primᶜ-++ f (oracle (map (mapTerm ρ inj)
                                    (map drawTerm (toList ds))))
                       (gᶜ ρ inj Bs))
           (cong₂ _++_ (L-draws f ρ inj (toList ds)) (L-g f ρ inj Bs)))

-- The tool's substitution renames g's wires.

L-picks : (h : ℕ → ℕ) (w : Fin m → ℕ) (ds : List (Draw m)) →
          substᵀ h (concat (map pickᵀ (map (pickOf w) ds))) ≡
          concat (map pickᵀ (map (pickOf (λ i → h (w i))) ds))
L-picks h w []               = refl
L-picks h w (CZᵈ a b _ ∷ ds) =
  cong (czᵀ (h (w a)) (h (w b)) ++_) (L-picks h w ds)
L-picks h w (Zᵈ a ∷ ds)      = cong (Z′ (h (w a)) ∷_) (L-picks h w ds)

L-subst : (h : ℕ → ℕ) (w : Fin m → ℕ) (Bs : List (Block d m)) →
          substᵀ h (genMaioranaGᵀ (map (altOf w) Bs)) ≡
          genMaioranaGᵀ (map (altOf (λ i → h (w i))) Bs)
L-subst h w []                          = refl
L-subst h w (block a b c p q r ds ∷ Bs) =
  cong (cczᵀ (h (w a)) (h (w b)) (h (w c)) ++_)
    (trans (map-++ (substGateᵀ h)
                   (concat (map pickᵀ (map (pickOf w) (toList ds))))
                   (genMaioranaGᵀ (map (altOf w) Bs)))
           (cong₂ _++_ (L-picks h w (toList ds)) (L-subst h w Bs)))

-- The X layer: X on the wires of the shift, in order.

L-flips : (ws : List (Fin n)) → map prim (map X ws) ≡ map X′ (map toℕ ws)
L-flips []       = refl
L-flips (w ∷ ws) = cong (X′ (toℕ w) ∷_) (L-flips ws)


------------------------------------------------------------------------
-- The pieces, on n = 2m wires numbered by any f that reads toℕ

module Pieces {m : ℕ} (f : Fin (m + m) → ℕ) (hf : ∀ w → f w ≡ toℕ w) where

  -- hTrans.

  piece-H : primᶜ f (hadamards (m + m)) ≡ map H′ (upTo (m + m))
  piece-H = trans (L-hadamards f)
    (tab-upTo (λ i → H′ (f i)) H′ (λ i → cong H′ (hf i)))

  -- cTrans.

  piece-cT : primᶜ f (cTᶜ m) ≡ concat (map (λ i → czᵀ i (i + m)) (upTo m))
  piece-cT = trans (L-pairs f (λ i → i ↑ˡ m) (λ i → m ↑ʳ i) (cross m))
    (cong concat (tab-upTo (λ i → czᵀ (f (i ↑ˡ m)) (f (m ↑ʳ i)))
                           (λ i → czᵀ i (i + m))
                           (λ i → cong₂ czᵀ
                             (trans (hf (i ↑ˡ m)) (toℕ-↑ˡ i m))
                             (trans (hf (m ↑ʳ i))
                                    (trans (toℕ-↑ʳ m i) (+-comm m (toℕ i)))))))

  -- g, as drawn.

  piece-g : (Bs : List (Block d m)) →
            primᶜ f (gˡ Bs) ≡ genMaioranaGᵀ (altsᵀ Bs)
  piece-g Bs = trans (L-g f (λ i → i ↑ˡ m) _ Bs)
    (cong genMaioranaGᵀ
      (map-cong (altOf-cong (λ i → trans (hf (i ↑ˡ m)) (toℕ-↑ˡ i m))) Bs))

  -- subst sub g.

  piece-g′ : (Bs : List (Block d m)) →
             primᶜ f (gʳ Bs) ≡ substᵀ (subᵀ m) (genMaioranaGᵀ (altsᵀ Bs))
  piece-g′ Bs = trans (L-g f (λ i → m ↑ʳ i) _ Bs)
    (trans (cong genMaioranaGᵀ
             (map-cong (altOf-cong (λ i → trans (hf (m ↑ʳ i))
                         (trans (toℕ-↑ʳ m i)
                                (sym (sub-< m (toℕ i) (toℕ<n i))))))
                       Bs))
           (sym (L-subst (subᵀ m) toℕ Bs)))


------------------------------------------------------------------------
-- Gate for gate

-- The hidden shift circuit of PathSum.HiddenShift.Tool is the list of
-- the tool's hiddenShift on the same draws, for every m, s and draw.

prim-HSᵗ : (s : Assign (m + m)) (Bs : List (Block d m)) →
           map prim (HSᵗ s Bs) ≡ hiddenShiftᵀ (m + m) (shiftᵀ s) (altsᵀ Bs)
prim-HSᵗ {m = m} s Bs =
  trans main (cong (λ k → hsᵀ (m + m) k (shiftᵀ s) (altsᵀ Bs)) (n≡⌊n+n/2⌋ m))
  where
  open Pieces {m} toℕ (λ _ → refl)

  pX : map prim (flipsˣ s) ≡ map X′ (shiftᵀ s)
  pX = L-flips (sel s)

  pF : map prim (fˣ s Bs) ≡
       map X′ (shiftᵀ s) ++ genMaioranaGᵀ (altsᵀ Bs) ++
       concat (map (λ i → czᵀ i (i + m)) (upTo m)) ++ map X′ (shiftᵀ s)
  pF = trans (map-++ prim (flipsˣ s) _) (cong₂ _++_ pX
    (trans (map-++ prim (map embed (gˡ Bs)) _) (cong₂ _++_ (piece-g Bs)
      (trans (map-++ prim (map embed (cTᶜ m)) (flipsˣ s))
             (cong₂ _++_ piece-cT pX)))))

  pF′ : map prim (f′ˣ Bs) ≡
        substᵀ (subᵀ m) (genMaioranaGᵀ (altsᵀ Bs)) ++
        concat (map (λ i → czᵀ i (i + m)) (upTo m))
  pF′ = trans (map-++ prim (map embed (gʳ Bs)) (map embed (cTᶜ m)))
              (cong₂ _++_ (piece-g′ Bs) piece-cT)

  main : map prim (HSᵗ s Bs) ≡ hsᵀ (m + m) m (shiftᵀ s) (altsᵀ Bs)
  main = trans (map-++ prim (hTˣ m) _) (cong₂ _++_ piece-H
    (trans (map-++ prim (fˣ s Bs) _) (cong₂ _++_ pF
      (trans (map-++ prim (hTˣ m) _) (cong₂ _++_ piece-H
        (trans (map-++ prim (f′ˣ Bs) (hTˣ m)) (cong₂ _++_ pF′ piece-H)))))))

-- The symbolic shift circuit of PathSum.HiddenShift.ToolSymbolic is
-- the list of the tool's hiddenShiftQuantum on the same draws.

prim-SSᵗ : (Bs : List (Block d m)) →
           map prim (SSᵗ Bs) ≡ hiddenShiftQuantumᵀ (m + m) (altsᵀ Bs)
prim-SSᵗ {m = m} Bs =
  trans main (cong (λ k → hsqᵀ (m + m) k (altsᵀ Bs)) (n≡⌊n+n/2⌋ m))
  where
  N : ℕ
  N = m + m

  open Pieces {m} (λ w → toℕ (w ↑ˡ N)) (λ w → toℕ-↑ˡ w N)

  pA : primᶜ toℕ (hTˢ m) ≡ map H′ (upTo N)
  pA = trans (L-upper toℕ (hadamards N)) piece-H

  pX : primᶜ toℕ (xTˢ m) ≡ map (λ i → CNOT′ (N + i) i) (upTo N)
  pX = trans (L-cnots toℕ (λ i → i))
    (tab-upTo (λ i → CNOT′ (toℕ (N ↑ʳ i)) (toℕ (i ↑ˡ N)))
              (λ i → CNOT′ (N + i) i)
              (λ i → cong₂ CNOT′ (toℕ-↑ʳ N i) (toℕ-↑ˡ i N)))

  pF : primᶜ toℕ (fˢ Bs) ≡
       map (λ i → CNOT′ (N + i) i) (upTo N) ++ genMaioranaGᵀ (altsᵀ Bs) ++
       concat (map (λ i → czᵀ i (i + m)) (upTo m)) ++
       map (λ i → CNOT′ (N + i) i) (upTo N)
  pF = trans (primᶜ-++ toℕ (xTˢ m) _) (cong₂ _++_ pX
    (trans (primᶜ-++ toℕ (upper N (gˡ Bs)) _)
      (cong₂ _++_ (trans (L-upper toℕ (gˡ Bs)) (piece-g Bs))
        (trans (primᶜ-++ toℕ (upper N (cTᶜ m)) (xTˢ m))
               (cong₂ _++_ (trans (L-upper toℕ (cTᶜ m)) piece-cT) pX)))))

  pF′ : primᶜ toℕ (f′ˢ Bs) ≡
        substᵀ (subᵀ m) (genMaioranaGᵀ (altsᵀ Bs)) ++
        concat (map (λ i → czᵀ i (i + m)) (upTo m))
  pF′ = trans (primᶜ-++ toℕ (upper N (gʳ Bs)) (upper N (cTᶜ m)))
    (cong₂ _++_ (trans (L-upper toℕ (gʳ Bs)) (piece-g′ Bs))
                (trans (L-upper toℕ (cTᶜ m)) piece-cT))

  main : map prim (SSᵗ Bs) ≡ hsqᵀ N m (altsᵀ Bs)
  main = trans (primᶜ-++ toℕ (hTˢ m) _) (cong₂ _++_ pA
    (trans (primᶜ-++ toℕ (fˢ Bs) _) (cong₂ _++_ pF
      (trans (primᶜ-++ toℕ (hTˢ m) _) (cong₂ _++_ pA
        (trans (primᶜ-++ toℕ (f′ˢ Bs) (hTˢ m)) (cong₂ _++_ pF′ pA)))))))


------------------------------------------------------------------------
-- The tool's own lists, for small draws

-- Hand-made draws on n = 6 (m = 3): two alternations of two draws
-- each (the tool draws 200), ccz x0 x2 x1 then cz x1 x0 and Z x2, and
-- ccz x2 x1 x0 then Z x1 and cz x2 x1; the shift x1 x4 x5.  On n = 4
-- (m = 2): no alternation, the shift x0 x3.  The lists are those the
-- tool's functions print on these draws under GHC (whose printVerStats
-- reports 6, 18, 106, 28; 4, 12, 36, 0; 12, 18, 112, 28; and 8, 12,
-- 40, 0 for qubits, Hadamards, Clifford and T gates).  Each is an
-- instance of prim-HSᵗ or prim-SSᵗ: the circuit is not evaluated, only
-- the transcription.

private
  w₀ w₁ w₂ : Fin 3
  w₀ = zero
  w₁ = suc zero
  w₂ = suc (suc zero)

smallDraws : List (Block 2 3)
smallDraws =
  block w₀ w₂ w₁ (λ ()) (λ ()) (λ ())
        (CZᵈ w₁ w₀ (λ ()) V.∷ Zᵈ w₂ V.∷ V.[]) ∷
  block w₂ w₁ w₀ (λ ()) (λ ()) (λ ())
        (Zᵈ w₁ V.∷ CZᵈ w₂ w₁ (λ ()) V.∷ V.[]) ∷ []

shift₆ : Assign 6
shift₆ = V.lookup
  (false V.∷ true V.∷ false V.∷ false V.∷ true V.∷ true V.∷ V.[])

shift₄ : Assign 4
shift₄ = V.lookup (true V.∷ false V.∷ false V.∷ true V.∷ V.[])

-- Hidden shift, n = 6: 134 gates.

HS-tool-6 :
  map prim (HSᵗ {m = 3} shift₆ smallDraws) ≡
  H′ 0 ∷ H′ 1 ∷ H′ 2 ∷ H′ 3 ∷ H′ 4 ∷ H′ 5 ∷ X′ 1 ∷ X′ 4 ∷ X′ 5 ∷ T′ 0 ∷
  T′ 2 ∷ T′ 1 ∷ CNOT′ 0 2 ∷ CNOT′ 2 1 ∷ CNOT′ 1 0 ∷ Tinv′ 0 ∷ Tinv′ 2 ∷
  T′ 1 ∷ CNOT′ 2 0 ∷ Tinv′ 0 ∷ CNOT′ 2 1 ∷ CNOT′ 1 0 ∷ CNOT′ 0 2 ∷
  S′ 1 ∷ S′ 0 ∷ CNOT′ 1 0 ∷ Sinv′ 0 ∷ CNOT′ 1 0 ∷ Z′ 2 ∷ T′ 2 ∷ T′ 1 ∷
  T′ 0 ∷ CNOT′ 2 1 ∷ CNOT′ 1 0 ∷ CNOT′ 0 2 ∷ Tinv′ 2 ∷ Tinv′ 1 ∷ T′ 0 ∷
  CNOT′ 1 2 ∷ Tinv′ 2 ∷ CNOT′ 1 0 ∷ CNOT′ 0 2 ∷ CNOT′ 2 1 ∷ Z′ 1 ∷
  S′ 2 ∷ S′ 1 ∷ CNOT′ 2 1 ∷ Sinv′ 1 ∷ CNOT′ 2 1 ∷ S′ 0 ∷ S′ 3 ∷
  CNOT′ 0 3 ∷ Sinv′ 3 ∷ CNOT′ 0 3 ∷ S′ 1 ∷ S′ 4 ∷ CNOT′ 1 4 ∷ Sinv′ 4 ∷
  CNOT′ 1 4 ∷ S′ 2 ∷ S′ 5 ∷ CNOT′ 2 5 ∷ Sinv′ 5 ∷ CNOT′ 2 5 ∷ X′ 1 ∷
  X′ 4 ∷ X′ 5 ∷ H′ 0 ∷ H′ 1 ∷ H′ 2 ∷ H′ 3 ∷ H′ 4 ∷ H′ 5 ∷ T′ 3 ∷ T′ 5 ∷
  T′ 4 ∷ CNOT′ 3 5 ∷ CNOT′ 5 4 ∷ CNOT′ 4 3 ∷ Tinv′ 3 ∷ Tinv′ 5 ∷ T′ 4 ∷
  CNOT′ 5 3 ∷ Tinv′ 3 ∷ CNOT′ 5 4 ∷ CNOT′ 4 3 ∷ CNOT′ 3 5 ∷ S′ 4 ∷
  S′ 3 ∷ CNOT′ 4 3 ∷ Sinv′ 3 ∷ CNOT′ 4 3 ∷ Z′ 5 ∷ T′ 5 ∷ T′ 4 ∷ T′ 3 ∷
  CNOT′ 5 4 ∷ CNOT′ 4 3 ∷ CNOT′ 3 5 ∷ Tinv′ 5 ∷ Tinv′ 4 ∷ T′ 3 ∷
  CNOT′ 4 5 ∷ Tinv′ 5 ∷ CNOT′ 4 3 ∷ CNOT′ 3 5 ∷ CNOT′ 5 4 ∷ Z′ 4 ∷
  S′ 5 ∷ S′ 4 ∷ CNOT′ 5 4 ∷ Sinv′ 4 ∷ CNOT′ 5 4 ∷ S′ 0 ∷ S′ 3 ∷
  CNOT′ 0 3 ∷ Sinv′ 3 ∷ CNOT′ 0 3 ∷ S′ 1 ∷ S′ 4 ∷ CNOT′ 1 4 ∷ Sinv′ 4 ∷
  CNOT′ 1 4 ∷ S′ 2 ∷ S′ 5 ∷ CNOT′ 2 5 ∷ Sinv′ 5 ∷ CNOT′ 2 5 ∷ H′ 0 ∷
  H′ 1 ∷ H′ 2 ∷ H′ 3 ∷ H′ 4 ∷ H′ 5 ∷ []
HS-tool-6 = prim-HSᵗ shift₆ smallDraws

-- Hidden shift, n = 4, no alternation: 36 gates.

HS-tool-4 :
  map prim (HSᵗ {m = 2} {d = 200} shift₄ []) ≡
  H′ 0 ∷ H′ 1 ∷ H′ 2 ∷ H′ 3 ∷ X′ 0 ∷ X′ 3 ∷ S′ 0 ∷ S′ 2 ∷ CNOT′ 0 2 ∷
  Sinv′ 2 ∷ CNOT′ 0 2 ∷ S′ 1 ∷ S′ 3 ∷ CNOT′ 1 3 ∷ Sinv′ 3 ∷ CNOT′ 1 3 ∷
  X′ 0 ∷ X′ 3 ∷ H′ 0 ∷ H′ 1 ∷ H′ 2 ∷ H′ 3 ∷ S′ 0 ∷ S′ 2 ∷ CNOT′ 0 2 ∷
  Sinv′ 2 ∷ CNOT′ 0 2 ∷ S′ 1 ∷ S′ 3 ∷ CNOT′ 1 3 ∷ Sinv′ 3 ∷ CNOT′ 1 3 ∷
  H′ 0 ∷ H′ 1 ∷ H′ 2 ∷ H′ 3 ∷ []
HS-tool-4 = prim-HSᵗ {m = 2} {d = 200} shift₄ []

-- Symbolic shift, n = 6: 140 gates.

SS-tool-6 :
  map prim (SSᵗ {m = 3} smallDraws) ≡
  H′ 0 ∷ H′ 1 ∷ H′ 2 ∷ H′ 3 ∷ H′ 4 ∷ H′ 5 ∷ CNOT′ 6 0 ∷ CNOT′ 7 1 ∷
  CNOT′ 8 2 ∷ CNOT′ 9 3 ∷ CNOT′ 10 4 ∷ CNOT′ 11 5 ∷ T′ 0 ∷ T′ 2 ∷
  T′ 1 ∷ CNOT′ 0 2 ∷ CNOT′ 2 1 ∷ CNOT′ 1 0 ∷ Tinv′ 0 ∷ Tinv′ 2 ∷ T′ 1 ∷
  CNOT′ 2 0 ∷ Tinv′ 0 ∷ CNOT′ 2 1 ∷ CNOT′ 1 0 ∷ CNOT′ 0 2 ∷ S′ 1 ∷
  S′ 0 ∷ CNOT′ 1 0 ∷ Sinv′ 0 ∷ CNOT′ 1 0 ∷ Z′ 2 ∷ T′ 2 ∷ T′ 1 ∷ T′ 0 ∷
  CNOT′ 2 1 ∷ CNOT′ 1 0 ∷ CNOT′ 0 2 ∷ Tinv′ 2 ∷ Tinv′ 1 ∷ T′ 0 ∷
  CNOT′ 1 2 ∷ Tinv′ 2 ∷ CNOT′ 1 0 ∷ CNOT′ 0 2 ∷ CNOT′ 2 1 ∷ Z′ 1 ∷
  S′ 2 ∷ S′ 1 ∷ CNOT′ 2 1 ∷ Sinv′ 1 ∷ CNOT′ 2 1 ∷ S′ 0 ∷ S′ 3 ∷
  CNOT′ 0 3 ∷ Sinv′ 3 ∷ CNOT′ 0 3 ∷ S′ 1 ∷ S′ 4 ∷ CNOT′ 1 4 ∷ Sinv′ 4 ∷
  CNOT′ 1 4 ∷ S′ 2 ∷ S′ 5 ∷ CNOT′ 2 5 ∷ Sinv′ 5 ∷ CNOT′ 2 5 ∷
  CNOT′ 6 0 ∷ CNOT′ 7 1 ∷ CNOT′ 8 2 ∷ CNOT′ 9 3 ∷ CNOT′ 10 4 ∷
  CNOT′ 11 5 ∷ H′ 0 ∷ H′ 1 ∷ H′ 2 ∷ H′ 3 ∷ H′ 4 ∷ H′ 5 ∷ T′ 3 ∷ T′ 5 ∷
  T′ 4 ∷ CNOT′ 3 5 ∷ CNOT′ 5 4 ∷ CNOT′ 4 3 ∷ Tinv′ 3 ∷ Tinv′ 5 ∷ T′ 4 ∷
  CNOT′ 5 3 ∷ Tinv′ 3 ∷ CNOT′ 5 4 ∷ CNOT′ 4 3 ∷ CNOT′ 3 5 ∷ S′ 4 ∷
  S′ 3 ∷ CNOT′ 4 3 ∷ Sinv′ 3 ∷ CNOT′ 4 3 ∷ Z′ 5 ∷ T′ 5 ∷ T′ 4 ∷ T′ 3 ∷
  CNOT′ 5 4 ∷ CNOT′ 4 3 ∷ CNOT′ 3 5 ∷ Tinv′ 5 ∷ Tinv′ 4 ∷ T′ 3 ∷
  CNOT′ 4 5 ∷ Tinv′ 5 ∷ CNOT′ 4 3 ∷ CNOT′ 3 5 ∷ CNOT′ 5 4 ∷ Z′ 4 ∷
  S′ 5 ∷ S′ 4 ∷ CNOT′ 5 4 ∷ Sinv′ 4 ∷ CNOT′ 5 4 ∷ S′ 0 ∷ S′ 3 ∷
  CNOT′ 0 3 ∷ Sinv′ 3 ∷ CNOT′ 0 3 ∷ S′ 1 ∷ S′ 4 ∷ CNOT′ 1 4 ∷ Sinv′ 4 ∷
  CNOT′ 1 4 ∷ S′ 2 ∷ S′ 5 ∷ CNOT′ 2 5 ∷ Sinv′ 5 ∷ CNOT′ 2 5 ∷ H′ 0 ∷
  H′ 1 ∷ H′ 2 ∷ H′ 3 ∷ H′ 4 ∷ H′ 5 ∷ []
SS-tool-6 = prim-SSᵗ smallDraws

-- Symbolic shift, n = 4, no alternation: 40 gates.

SS-tool-4 :
  map prim (SSᵗ {d = 200} {m = 2} []) ≡
  H′ 0 ∷ H′ 1 ∷ H′ 2 ∷ H′ 3 ∷ CNOT′ 4 0 ∷ CNOT′ 5 1 ∷ CNOT′ 6 2 ∷
  CNOT′ 7 3 ∷ S′ 0 ∷ S′ 2 ∷ CNOT′ 0 2 ∷ Sinv′ 2 ∷ CNOT′ 0 2 ∷ S′ 1 ∷
  S′ 3 ∷ CNOT′ 1 3 ∷ Sinv′ 3 ∷ CNOT′ 1 3 ∷ CNOT′ 4 0 ∷ CNOT′ 5 1 ∷
  CNOT′ 6 2 ∷ CNOT′ 7 3 ∷ H′ 0 ∷ H′ 1 ∷ H′ 2 ∷ H′ 3 ∷ S′ 0 ∷ S′ 2 ∷
  CNOT′ 0 2 ∷ Sinv′ 2 ∷ CNOT′ 0 2 ∷ S′ 1 ∷ S′ 3 ∷ CNOT′ 1 3 ∷ Sinv′ 3 ∷
  CNOT′ 1 3 ∷ H′ 0 ∷ H′ 1 ∷ H′ 2 ∷ H′ 3 ∷ []
SS-tool-4 = prim-SSᵗ {d = 200} {m = 2} []

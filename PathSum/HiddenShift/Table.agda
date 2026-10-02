------------------------------------------------------------------------
-- Presentations of groups
--
-- Table 2's hidden shift rows, counted from the circuits the paper's
-- tool generates, for every draw (Amy, QPL 2018, section 5.2 and
-- table 2)
--
-- Table 2 reports, for the hidden shift benchmarks the paper's tool
-- Feynman generated at random (PathSum.HiddenShift.Feynman),
--
--                          qubits   path vars   Clifford     T
--    Hidden Shift20,4        20         60         5254       56
--    Hidden Shift40,5        40        120         6466       70
--    Hidden Shift60,10       60        180        12784      140
--    Symbolic Shift20,4      40         60         5296       56
--    Symbolic Shift40,5      80        120         6638       70
--    Symbolic Shift60,10    120        180        12804      140
--
-- (n and A in the subscripts: n qubits in the data register, A
-- alternations of a ccz and 200 cz or Z draws).  The tool computes the
-- columns from the circuit by printVerStats: the distinct wires the
-- gates touch, the Hadamards (one path variable each), the Clifford
-- gates (H, X, Y, Z, S, S†, CNOT) and the T and T† gates.  Here they
-- are counted from the circuits HSᵗ s Bs (PathSum.HiddenShift.Tool)
-- and SSᵗ Bs (PathSum.HiddenShift.ToolSymbolic) for every m (n = 2m),
-- every shift s and every draw Bs of A blocks of d draws (the tool's
-- d is 200), c of them a cz:
--
--    qubits      n            (HS-qubits)    2n           (SS-qubits)
--    path vars   3n           (HS-paths)     3n           (SS-paths)
--    Clifford    8n + 2|s| + (14 + 2d)A + 8c (HS-cliffords)
--                10n + (14 + 2d)A + 8c       (SS-cliffords)
--    T           14A          (HS-tcount)    14A          (SS-tcount)
--
-- -- 414A at d = 200.  The Clifford and T counts are printVerStats's,
-- transcribed (cliffordsᵀ, tcountᵀ), on the circuit read as the tool
-- writes it (prim): by PathSum.HiddenShift.Feynman that is the tool's
-- own list, so they are counted on the tool's list, a ccz having seven
-- CNOTs and seven T or T†, a cz five Clifford gates, a Z one, the
-- substitution of the second oracle changing no count.  The qubits are
-- the wires the circuit touches (qubitsˣ, as PathSum.CRK.Qubits counts
-- them, now with X), the path variables those of its path-sum (paths
-- of PathSum.CRK.WithX: X allocates none).
--
-- The other two columns are printVerStats's too.  Its n is the size of
-- the set of wire names the gates touch (Set.size uids), here the
-- length of the list of the wires without repetitions (qubitsᵀ), and
-- its m the number of Hadamard gates (hcountᵀ); printVerStatsᵀ is the
-- four numbers it prints.  On any circuit read as the tool writes it,
-- qubitsᵀ is qubitsˣ (qubitsᵀ-prim: a list without repetitions of
-- numbers below n has as many elements as there are numbers below n
-- among them) and hcountᵀ is the number of path variables
-- (hcountᵀ-paths), so for every draw printVerStats prints n, 3n, the
-- Clifford count and 14A for the hidden shift, 2n, 3n, … for the
-- symbolic shift (HS-printVerStats, SS-printVerStats), and the rows
-- read through it (table-…ᵀ, HSRowᵀ, SSRowᵀ: printVerStats prints the
-- row's four numbers exactly when |s| + 4c, or c, is the row's) are
-- attained by the same draws (…-attainedᵀ).
--
-- The table's own draws are unknown: the tool draws them with
-- QuickCheck, unseeded (generate), and the paper does not report them.
-- So the qubit, path-variable and T columns are proved for every draw,
-- and the Clifford column, which depends on the draw, is characterised
-- exactly: Hidden Shift20,4 has 5254 Clifford gates iff
-- |s| + 4c = 1719, Symbolic Shift20,4 has 5296 iff c = 430, and so on
-- (the six rows table-…).
-- Each row is attained by some draw (…-attained): the table is
-- consistent with the tool's generator, and its Clifford column
-- determines c (exactly, for the symbolic shift).  The witnesses are
-- blocks whose first k draws are a cz on x0 x1 and the rest a Z on x0
-- after a ccz on x0 x1 x2, the shift the first |s| wires; a run of the
-- tool's own functions under GHC on the same draws prints the same
-- four numbers.  No closed circuit is evaluated: the rows follow from
-- the formulas.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Table (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∨_; if_then_else_)
open import Data.Bool.Properties using (∨-zeroʳ; ∨-assoc)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; _↑ˡ_; _↑ʳ_)
open import Data.List.Base using (List; []; _∷_; _++_; map; concat; length;
  upTo; deduplicate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using
  (∈-deduplicate⁺; ∈-deduplicate⁻)
open import Data.List.Properties using (length-map; length-upTo)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using ()
  renaming (++⁺ to All-++⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using
  (Unique; []; _∷_)
open import Data.Nat.Base using
  (zero; suc; _+_; _*_; _<_; _<ᵇ_; _≡ᵇ_; ⌊_/2⌋; NonZero)
open import Data.Nat.Properties using
  (n≡⌊n+n/2⌋; +-assoc; +-suc; *-identityˡ; +-cancelˡ-≡; *-cancelˡ-≡)
  renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (Vec; toList)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)

import Data.Fin.Base as F
import Data.Fin.Properties as FinP
import Data.List.Relation.Unary.All as All
import Data.Vec.Base as V

open import Data.List.Relation.Unary.Unique.DecPropositional.Properties
  _≟ℕ_ using (deduplicate-!)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

open import PathSum.CRK.Qubits M₀ using
  (#ʷ; #ʷ-all; #ʷ-cong; elem; wiresᶜ; touched; _∈ᶜ_; ∈ᶜ-touched; ∈ᶜ-++ˡ;
   ∈ᶜ-++ʳ; qubits; qubits-all)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift.Feynman M₀ using
  (Prim; H′; X′; Z′; S′; Sinv′; T′; Tinv′; CNOT′; R′; R†′; prim; cczᵀ; czᵀ;
   substGateᵀ; substᵀ; subᵀ; pickᵀ; genMaioranaGᵀ; hsᵀ; hsqᵀ; pickOf; altOf;
   altsᵀ; shiftᵀ; prim-HSᵗ; prim-SSᵗ; Rᵀ; R†ᵀ)
open import PathSum.HiddenShift.Gates M₀ using (↑g; ◂g; lift; upper)
open import PathSum.HiddenShift.Layers M₀ using (hadamards)
open import PathSum.HiddenShift.LayersX M₀ using (selʰ; sel)
open import PathSum.HiddenShift.Symbolic M₀ using (cnots)
open import PathSum.HiddenShift.Tool M₀ using
  (Draw; CZᵈ; Zᵈ; Block; block; HSᵗ; hTˣ; fˣ; f′ˣ; norm-HSᵗ)
open import PathSum.HiddenShift.ToolSymbolic M₀ using
  (SSᶜᵗ; SSᵗ; hTˢ; xTˢ; fˢ; f′ˢ; norm-SSᵗ)

private
  M : ℕ
  M = suc (suc (suc M₀))

import PathSum.CRK.Circuit

private
  module CRK = PathSum.CRK.Circuit M

open import PathSum.CRK.WithX M₀ using
  (Gate; H; X; CNOT; R; R†; Circuit; norm; embed; paths; paths≡norm)

private
  variable
    n k l m d : ℕ


------------------------------------------------------------------------
-- printVerStats

-- Its Clifford and T columns, gate by gate (R′ and R†′, not among the
-- tool's gates, count as neither).

cliffordᵖ tgateᵖ : Prim → ℕ
cliffordᵖ (H′ _)      = 1
cliffordᵖ (X′ _)      = 1
cliffordᵖ (Z′ _)      = 1
cliffordᵖ (S′ _)      = 1
cliffordᵖ (Sinv′ _)   = 1
cliffordᵖ (T′ _)      = 0
cliffordᵖ (Tinv′ _)   = 0
cliffordᵖ (CNOT′ _ _) = 1
cliffordᵖ (R′ _ _)    = 0
cliffordᵖ (R†′ _ _)   = 0
tgateᵖ (H′ _)         = 0
tgateᵖ (X′ _)         = 0
tgateᵖ (Z′ _)         = 0
tgateᵖ (S′ _)         = 0
tgateᵖ (Sinv′ _)      = 0
tgateᵖ (T′ _)         = 1
tgateᵖ (Tinv′ _)      = 1
tgateᵖ (CNOT′ _ _)    = 0
tgateᵖ (R′ _ _)       = 0
tgateᵖ (R†′ _ _)      = 0

-- The sum over a list.

countᵀ : (Prim → ℕ) → List Prim → ℕ
countᵀ c []       = 0
countᵀ c (g ∷ gs) = c g + countᵀ c gs

cliffordsᵀ tcountᵀ : List Prim → ℕ
cliffordsᵀ = countᵀ cliffordᵖ
tcountᵀ    = countᵀ tgateᵖ


------------------------------------------------------------------------
-- Counting the tool's lists

private
  count-++ : (c : Prim → ℕ) (xs ys : List Prim) →
             countᵀ c (xs ++ ys) ≡ countᵀ c xs + countᵀ c ys
  count-++ c []       ys = refl
  count-++ c (g ∷ xs) ys =
    trans (cong (c g +_) (count-++ c xs ys)) (sym (+-assoc (c g) _ _))

  -- A map whose every gate counts k.

  count-map : (c : Prim → ℕ) (F : ℕ → Prim) (k : ℕ) → (∀ x → c (F x) ≡ k) →
              (xs : List ℕ) → countᵀ c (map F xs) ≡ k * length xs
  count-map c F k h []       = solve 1 (λ k → con 0 := k :* con 0) refl k
  count-map c F k h (x ∷ xs) =
    trans (cong₂ _+_ (h x) (count-map c F k h xs))
          (solve 2 (λ k l → k :+ k :* l := k :* (con 1 :+ l)) refl k
                 (length xs))

  -- A concatenation of lists that each count k.

  count-concat : (c : Prim → ℕ) (F : ℕ → List Prim) (k : ℕ) →
                 (∀ x → countᵀ c (F x) ≡ k) →
                 (xs : List ℕ) → countᵀ c (concat (map F xs)) ≡ k * length xs
  count-concat c F k h []       = solve 1 (λ k → con 0 := k :* con 0) refl k
  count-concat c F k h (x ∷ xs) =
    trans (count-++ c (F x) (concat (map F xs)))
      (trans (cong₂ _+_ (h x) (count-concat c F k h xs))
             (solve 2 (λ k l → k :+ k :* l := k :* (con 1 :+ l)) refl k
                    (length xs)))

  -- The tool's substitution changes no Clifford or T count.

  count-subst : (c : Prim → ℕ) → (∀ h g → c (substGateᵀ h g) ≡ c g) →
                (h : ℕ → ℕ) (xs : List Prim) →
                countᵀ c (substᵀ h xs) ≡ countᵀ c xs
  count-subst c e h []       = refl
  count-subst c e h (g ∷ xs) = cong₂ _+_ (e h g) (count-subst c e h xs)

  cliffordᵖ-subst : ∀ h g → cliffordᵖ (substGateᵀ h g) ≡ cliffordᵖ g
  cliffordᵖ-subst h (H′ _)      = refl
  cliffordᵖ-subst h (X′ _)      = refl
  cliffordᵖ-subst h (Z′ _)      = refl
  cliffordᵖ-subst h (S′ _)      = refl
  cliffordᵖ-subst h (Sinv′ _)   = refl
  cliffordᵖ-subst h (T′ _)      = refl
  cliffordᵖ-subst h (Tinv′ _)   = refl
  cliffordᵖ-subst h (CNOT′ _ _) = refl
  cliffordᵖ-subst h (R′ _ _)    = refl
  cliffordᵖ-subst h (R†′ _ _)   = refl

  tgateᵖ-subst : ∀ h g → tgateᵖ (substGateᵀ h g) ≡ tgateᵖ g
  tgateᵖ-subst h (H′ _)      = refl
  tgateᵖ-subst h (X′ _)      = refl
  tgateᵖ-subst h (Z′ _)      = refl
  tgateᵖ-subst h (S′ _)      = refl
  tgateᵖ-subst h (Sinv′ _)   = refl
  tgateᵖ-subst h (T′ _)      = refl
  tgateᵖ-subst h (Tinv′ _)   = refl
  tgateᵖ-subst h (CNOT′ _ _) = refl
  tgateᵖ-subst h (R′ _ _)    = refl
  tgateᵖ-subst h (R†′ _ _)   = refl


------------------------------------------------------------------------
-- The draws

-- The number of cz draws, in a block's draws and in all blocks.

czsᵈ : Vec (Draw m) d → ℕ
czsᵈ V.[]                 = 0
czsᵈ (CZᵈ _ _ _ V.∷ ds) = suc (czsᵈ ds)
czsᵈ (Zᵈ _ V.∷ ds)      = czsᵈ ds

czs : List (Block d m) → ℕ
czs []                          = 0
czs (block _ _ _ _ _ _ ds ∷ Bs) = czsᵈ ds + czs Bs

-- A block's draws: d draws, each one Clifford gate and four more for a
-- cz; no T gate.

private
  cl-draws : (w : Fin m → ℕ) (ds : Vec (Draw m) d) →
             cliffordsᵀ (concat (map pickᵀ (map (pickOf w) (toList ds)))) ≡
             d + 4 * czsᵈ ds
  cl-draws w V.[]                 = refl
  cl-draws {d = suc d} w (CZᵈ a b _ V.∷ ds) =
    trans (count-++ cliffordᵖ (czᵀ (w a) (w b))
                    (concat (map pickᵀ (map (pickOf w) (toList ds)))))
      (trans (cong (5 +_) (cl-draws w ds))
             (solve 2 (λ d c → con 5 :+ (d :+ con 4 :* c) :=
                               (con 1 :+ d) :+ con 4 :* (con 1 :+ c))
                    refl d (czsᵈ ds)))
  cl-draws {d = suc d} w (Zᵈ a V.∷ ds)      =
    cong suc (cl-draws w ds)

  t-draws : (w : Fin m → ℕ) (ds : Vec (Draw m) d) →
            tcountᵀ (concat (map pickᵀ (map (pickOf w) (toList ds)))) ≡ 0
  t-draws w V.[]                 = refl
  t-draws w (CZᵈ a b _ V.∷ ds) =
    trans (count-++ tgateᵖ (czᵀ (w a) (w b))
                    (concat (map pickᵀ (map (pickOf w) (toList ds)))))
          (t-draws w ds)
  t-draws w (Zᵈ a V.∷ ds)      = t-draws w ds

-- g: per block a ccz (seven Clifford, seven T) and its draws.

cl-g : (w : Fin m → ℕ) (Bs : List (Block d m)) →
       cliffordsᵀ (genMaioranaGᵀ (map (altOf w) Bs)) ≡
       (7 + d) * length Bs + 4 * czs Bs
cl-g {d = d} w []                          =
  solve 1 (λ d → con 0 := (con 7 :+ d) :* con 0 :+ con 4 :* con 0) refl d
cl-g {d = d} w (block a b c _ _ _ ds ∷ Bs) =
  trans (count-++ cliffordᵖ (cczᵀ (w a) (w b) (w c) ++ D) G)
    (trans (cong (_+ cliffordsᵀ G)
                 (count-++ cliffordᵖ (cczᵀ (w a) (w b) (w c)) D))
      (trans (cong₂ (λ x y → (7 + x) + y) (cl-draws w ds) (cl-g w Bs))
             (solve 4 (λ d c A C → (con 7 :+ (d :+ con 4 :* c)) :+
                                     ((con 7 :+ d) :* A :+ con 4 :* C) :=
                                   (con 7 :+ d) :* (con 1 :+ A) :+
                                   con 4 :* (c :+ C))
                    refl d (czsᵈ ds) (length Bs) (czs Bs))))
  where
  D G : List Prim
  D = concat (map pickᵀ (map (pickOf w) (toList ds)))
  G = genMaioranaGᵀ (map (altOf w) Bs)

t-g : (w : Fin m → ℕ) (Bs : List (Block d m)) →
      tcountᵀ (genMaioranaGᵀ (map (altOf w) Bs)) ≡ 7 * length Bs
t-g w []                          = refl
t-g w (block a b c _ _ _ ds ∷ Bs) =
  trans (count-++ tgateᵖ (cczᵀ (w a) (w b) (w c) ++ D) G)
    (trans (cong (_+ tcountᵀ G) (count-++ tgateᵖ (cczᵀ (w a) (w b) (w c)) D))
      (trans (cong₂ (λ x y → (7 + x) + y) (t-draws w ds) (t-g w Bs))
             (solve 1 (λ A → (con 7 :+ con 0) :+ con 7 :* A :=
                             con 7 :* (con 1 :+ A))
                    refl (length Bs))))
  where
  D G : List Prim
  D = concat (map pickᵀ (map (pickOf w) (toList ds)))
  G = genMaioranaGᵀ (map (altOf w) Bs)

-- The shift's length is the number of wires where s is 1.

length-shift : (s : Assign n) → length (shiftᵀ s) ≡ #ʷ s
length-shift s = trans (length-map toℕ (sel s)) (len s)
  where
  len : ∀ {n} (s : Assign n) → length (sel s) ≡ #ʷ s
  len {zero}  s = refl
  len {suc n} s = step (s zero)
    where
    step : ∀ b → length (selʰ b (map F.suc (sel (λ i → s (suc i))))) ≡
                 (if b then 1 else 0) + #ʷ (λ i → s (suc i))
    step true  = cong suc (trans (length-map F.suc (sel (λ i → s (suc i))))
                                 (len (λ i → s (suc i))))
    step false = trans (length-map F.suc (sel (λ i → s (suc i))))
                       (len (λ i → s (suc i)))


------------------------------------------------------------------------
-- The tool's two lists

private
  -- hTrans, xTrans, cTrans and the CNOT layer.

  cl-H : ∀ n → cliffordsᵀ (map H′ (upTo n)) ≡ n
  cl-H n = trans (count-map cliffordᵖ H′ 1 (λ _ → refl) (upTo n))
                 (trans (*-identityˡ (length (upTo n))) (length-upTo n))

  cl-X : (s : List ℕ) → cliffordsᵀ (map X′ s) ≡ length s
  cl-X s = trans (count-map cliffordᵖ X′ 1 (λ _ → refl) s)
                 (*-identityˡ (length s))

  cl-CX : ∀ n → cliffordsᵀ (map (λ i → CNOT′ (n + i) i) (upTo n)) ≡ n
  cl-CX n = trans (count-map cliffordᵖ (λ i → CNOT′ (n + i) i) 1 (λ _ → refl)
                             (upTo n))
                  (trans (*-identityˡ (length (upTo n))) (length-upTo n))

  cl-cT : ∀ n2 → cliffordsᵀ (concat (map (λ i → czᵀ i (i + n2)) (upTo n2))) ≡
                 5 * n2
  cl-cT n2 = trans (count-concat cliffordᵖ (λ i → czᵀ i (i + n2)) 5
                                 (λ _ → refl) (upTo n2))
                   (cong (5 *_) (length-upTo n2))

  t-H : ∀ n → tcountᵀ (map H′ (upTo n)) ≡ 0
  t-H n = count-map tgateᵖ H′ 0 (λ _ → refl) (upTo n)

  t-X : (s : List ℕ) → tcountᵀ (map X′ s) ≡ 0
  t-X s = count-map tgateᵖ X′ 0 (λ _ → refl) s

  t-CX : ∀ n → tcountᵀ (map (λ i → CNOT′ (n + i) i) (upTo n)) ≡ 0
  t-CX n = count-map tgateᵖ (λ i → CNOT′ (n + i) i) 0 (λ _ → refl) (upTo n)

  t-cT : ∀ n2 → tcountᵀ (concat (map (λ i → czᵀ i (i + n2)) (upTo n2))) ≡ 0
  t-cT n2 = count-concat tgateᵖ (λ i → czᵀ i (i + n2)) 0 (λ _ → refl)
                         (upTo n2)

  -- The five parts of hTrans ++ f ++ hTrans ++ f′ ++ hTrans.

  five : (c : Prim → ℕ) (a b e f g : List Prim) →
         countᵀ c (a ++ b ++ e ++ f ++ g) ≡
         countᵀ c a + (countᵀ c b + (countᵀ c e + (countᵀ c f + countᵀ c g)))
  five c a b e f g =
    trans (count-++ c a _) (cong (countᵀ c a +_)
      (trans (count-++ c b _) (cong (countᵀ c b +_)
        (trans (count-++ c e _) (cong (countᵀ c e +_) (count-++ c f g))))))

  -- f = xTrans ++ g ++ cTrans ++ xTrans and f′ = subst sub g ++ cTrans.

  four : (c : Prim → ℕ) (a b e f : List Prim) →
         countᵀ c (a ++ b ++ e ++ f) ≡
         countᵀ c a + (countᵀ c b + (countᵀ c e + countᵀ c f))
  four c a b e f =
    trans (count-++ c a _) (cong (countᵀ c a +_)
      (trans (count-++ c b _) (cong (countᵀ c b +_) (count-++ c e f))))

-- The Clifford and T counts of the tool's hiddenShift and
-- hiddenShiftQuantum lists, from those of g.

cl-hs : ∀ n n2 (s : List ℕ) as →
        cliffordsᵀ (hsᵀ n n2 s as) ≡
        ((3 * n + 2 * length s) + 2 * cliffordsᵀ (genMaioranaGᵀ as)) +
        10 * n2
cl-hs n n2 s as =
  trans (five cliffordᵖ hT F hT F′ hT)
    (trans (cong₂ (λ a b → a + (b + (a + (cf′ + a)))) (cl-H n) cf)
      (trans (cong (λ x → n + ((length s + (G + (5 * n2 + length s))) +
                              (n + (x + n))))
                   (trans (count-++ cliffordᵖ (substᵀ (subᵀ n2) g) cT)
                          (cong₂ _+_ (count-subst cliffordᵖ cliffordᵖ-subst
                                                  (subᵀ n2) g)
                                     (cl-cT n2))))
             (solve 4 (λ n s G k →
               n :+ ((s :+ (G :+ (con 5 :* k :+ s))) :+ (n :+ ((G :+ con 5 :* k)
                 :+ n))) :=
               ((con 3 :* n :+ con 2 :* s) :+ con 2 :* G) :+ con 10 :* k)
               refl n (length s) G n2)))
  where
  hT g cT F F′ : List Prim
  hT = map H′ (upTo n)
  g  = genMaioranaGᵀ as
  cT = concat (map (λ i → czᵀ i (i + n2)) (upTo n2))
  F  = map X′ s ++ g ++ cT ++ map X′ s
  F′ = substᵀ (subᵀ n2) g ++ cT

  G cf′ : ℕ
  G   = cliffordsᵀ g
  cf′ = cliffordsᵀ F′

  cf : cliffordsᵀ F ≡ length s + (G + (5 * n2 + length s))
  cf = trans (four cliffordᵖ (map X′ s) g cT (map X′ s))
             (cong₂ (λ x y → x + (G + (y + x))) (cl-X s) (cl-cT n2))

cl-hsq : ∀ n n2 as →
         cliffordsᵀ (hsqᵀ n n2 as) ≡
         (5 * n + 2 * cliffordsᵀ (genMaioranaGᵀ as)) + 10 * n2
cl-hsq n n2 as =
  trans (five cliffordᵖ hT F hT F′ hT)
    (trans (cong₂ (λ a b → a + (b + (a + (cf′ + a)))) (cl-H n) cf)
      (trans (cong (λ x → n + ((n + (G + (5 * n2 + n))) + (n + (x + n))))
                   (trans (count-++ cliffordᵖ (substᵀ (subᵀ n2) g) cT)
                          (cong₂ _+_ (count-subst cliffordᵖ cliffordᵖ-subst
                                                  (subᵀ n2) g)
                                     (cl-cT n2))))
             (solve 3 (λ n G k →
               n :+ ((n :+ (G :+ (con 5 :* k :+ n))) :+ (n :+ ((G :+ con 5 :* k)
                 :+ n))) :=
               (con 5 :* n :+ con 2 :* G) :+ con 10 :* k)
               refl n G n2)))
  where
  hT g cT xT F F′ : List Prim
  hT = map H′ (upTo n)
  g  = genMaioranaGᵀ as
  cT = concat (map (λ i → czᵀ i (i + n2)) (upTo n2))
  xT = map (λ i → CNOT′ (n + i) i) (upTo n)
  F  = xT ++ g ++ cT ++ xT
  F′ = substᵀ (subᵀ n2) g ++ cT

  G cf′ : ℕ
  G   = cliffordsᵀ g
  cf′ = cliffordsᵀ F′

  cf : cliffordsᵀ F ≡ n + (G + (5 * n2 + n))
  cf = trans (four cliffordᵖ xT g cT xT)
             (cong₂ (λ x y → x + (G + (y + x))) (cl-CX n) (cl-cT n2))

t-hs : ∀ n n2 (s : List ℕ) as →
       tcountᵀ (hsᵀ n n2 s as) ≡ 2 * tcountᵀ (genMaioranaGᵀ as)
t-hs n n2 s as =
  trans (five tgateᵖ hT F hT F′ hT)
    (trans (cong₂ (λ a b → a + (b + (a + (tf′ + a)))) (t-H n) tf)
      (trans (cong (λ x → 0 + ((G + 0) + (0 + (x + 0))))
                   (trans (count-++ tgateᵖ (substᵀ (subᵀ n2) g) cT)
                          (cong₂ _+_ (count-subst tgateᵖ tgateᵖ-subst
                                                  (subᵀ n2) g)
                                     (t-cT n2))))
             (solve 1 (λ G → con 0 :+ ((G :+ con 0) :+
                                     (con 0 :+ ((G :+ con 0) :+ con 0))) :=
                             con 2 :* G) refl G)))
  where
  hT g cT F F′ : List Prim
  hT = map H′ (upTo n)
  g  = genMaioranaGᵀ as
  cT = concat (map (λ i → czᵀ i (i + n2)) (upTo n2))
  F  = map X′ s ++ g ++ cT ++ map X′ s
  F′ = substᵀ (subᵀ n2) g ++ cT

  G tf′ : ℕ
  G   = tcountᵀ g
  tf′ = tcountᵀ F′

  tf : tcountᵀ F ≡ G + 0
  tf = trans (four tgateᵖ (map X′ s) g cT (map X′ s))
             (cong₂ (λ x y → x + (G + (y + x))) (t-X s) (t-cT n2))

t-hsq : ∀ n n2 as → tcountᵀ (hsqᵀ n n2 as) ≡ 2 * tcountᵀ (genMaioranaGᵀ as)
t-hsq n n2 as =
  trans (five tgateᵖ hT F hT F′ hT)
    (trans (cong₂ (λ a b → a + (b + (a + (tf′ + a)))) (t-H n) tf)
      (trans (cong (λ x → 0 + ((G + 0) + (0 + (x + 0))))
                   (trans (count-++ tgateᵖ (substᵀ (subᵀ n2) g) cT)
                          (cong₂ _+_ (count-subst tgateᵖ tgateᵖ-subst
                                                  (subᵀ n2) g)
                                     (t-cT n2))))
             (solve 1 (λ G → con 0 :+ ((G :+ con 0) :+
                                     (con 0 :+ ((G :+ con 0) :+ con 0))) :=
                             con 2 :* G) refl G)))
  where
  hT g cT xT F F′ : List Prim
  hT = map H′ (upTo n)
  g  = genMaioranaGᵀ as
  cT = concat (map (λ i → czᵀ i (i + n2)) (upTo n2))
  xT = map (λ i → CNOT′ (n + i) i) (upTo n)
  F  = xT ++ g ++ cT ++ xT
  F′ = substᵀ (subᵀ n2) g ++ cT

  G tf′ : ℕ
  G   = tcountᵀ g
  tf′ = tcountᵀ F′

  tf : tcountᵀ F ≡ G + 0
  tf = trans (four tgateᵖ xT g cT xT)
             (cong₂ (λ x y → x + (G + (y + x))) (t-CX n) (t-cT n2))


------------------------------------------------------------------------
-- The counts of the circuits, for every draw

-- Clifford gates: 8n + 2|s| + (14 + 2d)A + 8c for the hidden shift,
-- 10n + (14 + 2d)A + 8c for the symbolic shift (414A at d = 200).

HS-cliffords : (s : Assign (m + m)) (Bs : List (Block d m)) →
               cliffordsᵀ (map prim (HSᵗ s Bs)) ≡
               ((8 * (m + m) + 2 * #ʷ s) + (14 + 2 * d) * length Bs) +
               8 * czs Bs
HS-cliffords {m = m} {d = d} s Bs =
  trans (cong cliffordsᵀ (prim-HSᵗ s Bs))
    (trans (cl-hs (m + m) ⌊ (m + m) /2⌋ (shiftᵀ s) (altsᵀ Bs))
      (trans (cong₂ (λ x y → ((3 * (m + m) + 2 * x) + 2 * y) +
                             10 * ⌊ (m + m) /2⌋)
                    (length-shift s) (cl-g toℕ Bs))
        (trans (cong (λ k → ((3 * (m + m) + 2 * #ʷ s) +
                             2 * ((7 + d) * length Bs + 4 * czs Bs)) + 10 * k)
                     (sym (n≡⌊n+n/2⌋ m)))
               (solve 5 (λ m x d A c →
                 ((con 3 :* (m :+ m) :+ con 2 :* x) :+
                  con 2 :* ((con 7 :+ d) :* A :+ con 4 :* c)) :+ con 10 :* m :=
                 ((con 8 :* (m :+ m) :+ con 2 :* x) :+
                  (con 14 :+ con 2 :* d) :* A) :+ con 8 :* c)
                 refl m (#ʷ s) d (length Bs) (czs Bs)))))

SS-cliffords : (Bs : List (Block d m)) →
               cliffordsᵀ (map prim (SSᵗ Bs)) ≡
               (10 * (m + m) + (14 + 2 * d) * length Bs) + 8 * czs Bs
SS-cliffords {d = d} {m = m} Bs =
  trans (cong cliffordsᵀ (prim-SSᵗ Bs))
    (trans (cl-hsq (m + m) ⌊ (m + m) /2⌋ (altsᵀ Bs))
      (trans (cong (λ y → (5 * (m + m) + 2 * y) + 10 * ⌊ (m + m) /2⌋)
                   (cl-g toℕ Bs))
        (trans (cong (λ k → (5 * (m + m) +
                             2 * ((7 + d) * length Bs + 4 * czs Bs)) + 10 * k)
                     (sym (n≡⌊n+n/2⌋ m)))
               (solve 4 (λ m d A c →
                 (con 5 :* (m :+ m) :+
                  con 2 :* ((con 7 :+ d) :* A :+ con 4 :* c)) :+ con 10 :* m :=
                 (con 10 :* (m :+ m) :+ (con 14 :+ con 2 :* d) :* A) :+
                 con 8 :* c)
                 refl m d (length Bs) (czs Bs)))))

-- At the tool's d = 200: 414A.

HS-cliffords-200 : (s : Assign (m + m)) (Bs : List (Block 200 m)) →
                   cliffordsᵀ (map prim (HSᵗ s Bs)) ≡
                   ((8 * (m + m) + 2 * #ʷ s) + 414 * length Bs) + 8 * czs Bs
HS-cliffords-200 = HS-cliffords

SS-cliffords-200 : (Bs : List (Block 200 m)) →
                   cliffordsᵀ (map prim (SSᵗ Bs)) ≡
                   (10 * (m + m) + 414 * length Bs) + 8 * czs Bs
SS-cliffords-200 = SS-cliffords

-- T gates: 14A.

HS-tcount : (s : Assign (m + m)) (Bs : List (Block d m)) →
            tcountᵀ (map prim (HSᵗ s Bs)) ≡ 14 * length Bs
HS-tcount {m = m} s Bs =
  trans (cong tcountᵀ (prim-HSᵗ s Bs))
    (trans (t-hs (m + m) ⌊ (m + m) /2⌋ (shiftᵀ s) (altsᵀ Bs))
      (trans (cong (2 *_) (t-g toℕ Bs))
             (solve 1 (λ A → con 2 :* (con 7 :* A) := con 14 :* A) refl
                    (length Bs))))

SS-tcount : (Bs : List (Block d m)) →
            tcountᵀ (map prim (SSᵗ Bs)) ≡ 14 * length Bs
SS-tcount {m = m} Bs =
  trans (cong tcountᵀ (prim-SSᵗ Bs))
    (trans (t-hsq (m + m) ⌊ (m + m) /2⌋ (altsᵀ Bs))
      (trans (cong (2 *_) (t-g toℕ Bs))
             (solve 1 (λ A → con 2 :* (con 7 :* A) := con 14 :* A) refl
                    (length Bs))))

-- Path variables: 3n, one for each Hadamard (X allocates none).

HS-paths : (s : Assign (m + m)) (Bs : List (Block d m)) →
           paths (HSᵗ s Bs) ≡ 3 * (m + m)
HS-paths {m = m} s Bs = trans (paths≡norm (HSᵗ s Bs))
  (trans (norm-HSᵗ s Bs)
         (solve 1 (λ a → ((((a :+ con 0) :+ a) :+ con 0) :+ a) :+ con 0 :=
                         con 3 :* a) refl (m + m)))

SS-paths : (Bs : List (Block d m)) → paths (SSᵗ Bs) ≡ 3 * (m + m)
SS-paths {m = m} Bs = trans (paths≡norm (SSᵗ Bs))
  (trans (norm-SSᵗ Bs)
         (solve 1 (λ a → (((a :+ con 0) :+ a) :+ con 0) :+ a := con 3 :* a)
                refl (m + m)))


------------------------------------------------------------------------
-- Qubits

-- The wires a gate touches, now with X, and the number of wires a
-- circuit touches (PathSum.CRK.Qubits's count).

wiresˣ : Gate n → List (Fin n)
wiresˣ (H w)        = w ∷ []
wiresˣ (X w)        = w ∷ []
wiresˣ (CNOT c t _) = c ∷ t ∷ []
wiresˣ (R _ w)      = w ∷ []
wiresˣ (R† _ w)     = w ∷ []

touchedˣ : Circuit n → Fin n → Bool
touchedˣ []      u = false
touchedˣ (g ∷ C) u = elem (wiresˣ g) u ∨ touchedˣ C u

qubitsˣ : Circuit n → ℕ
qubitsˣ C = #ʷ (touchedˣ C)

-- On an embedded circuit it is PathSum.CRK.Qubits's.

touchedˣ-embed : (C : CRK.Circuit n) (u : Fin n) →
                 touchedˣ (map embed C) u ≡ touched C u
touchedˣ-embed []                   u = refl
touchedˣ-embed (CRK.H w ∷ C)        u =
  cong (elem (w ∷ []) u ∨_) (touchedˣ-embed C u)
touchedˣ-embed (CRK.CNOT c t _ ∷ C) u =
  cong (elem (c ∷ t ∷ []) u ∨_) (touchedˣ-embed C u)
touchedˣ-embed (CRK.R _ w ∷ C)      u =
  cong (elem (w ∷ []) u ∨_) (touchedˣ-embed C u)
touchedˣ-embed (CRK.R† _ w ∷ C)     u =
  cong (elem (w ∷ []) u ∨_) (touchedˣ-embed C u)

qubitsˣ-embed : (C : CRK.Circuit n) → qubitsˣ (map embed C) ≡ qubits C
qubitsˣ-embed C = #ʷ-cong (touchedˣ-embed C)

-- A concatenation touches what its first part touches.

touchedˣ-++ˡ : (C D : Circuit n) (u : Fin n) → touchedˣ C u ≡ true →
               touchedˣ (C ++ D) u ≡ true
touchedˣ-++ˡ []      D u ()
touchedˣ-++ˡ (g ∷ C) D u e = go (elem (wiresˣ g) u) e
  where
  go : ∀ b → b ∨ touchedˣ C u ≡ true → b ∨ touchedˣ (C ++ D) u ≡ true
  go true  _ = refl
  go false e = touchedˣ-++ˡ C D u e

-- Moved circuits touch the moved wires.

private
  w-lift : (g : CRK.Gate n) {u : Fin n} → u ∈ wiresᶜ g →
           suc u ∈ wiresᶜ (↑g g)
  w-lift (CRK.H w)        (here refl)         = here refl
  w-lift (CRK.H w)        (there ())
  w-lift (CRK.CNOT c t p) (here refl)         = here refl
  w-lift (CRK.CNOT c t p) (there (here refl)) = there (here refl)
  w-lift (CRK.CNOT c t p) (there (there ()))
  w-lift (CRK.R k w)      (here refl)         = here refl
  w-lift (CRK.R k w)      (there ())
  w-lift (CRK.R† k w)     (here refl)         = here refl
  w-lift (CRK.R† k w)     (there ())

  w-upper : ∀ l (g : CRK.Gate k) {u : Fin k} → u ∈ wiresᶜ g →
            (u ↑ˡ l) ∈ wiresᶜ (◂g l g)
  w-upper l (CRK.H w)        (here refl)         = here refl
  w-upper l (CRK.H w)        (there ())
  w-upper l (CRK.CNOT c t p) (here refl)         = here refl
  w-upper l (CRK.CNOT c t p) (there (here refl)) = there (here refl)
  w-upper l (CRK.CNOT c t p) (there (there ()))
  w-upper l (CRK.R k w)      (here refl)         = here refl
  w-upper l (CRK.R k w)      (there ())
  w-upper l (CRK.R† k w)     (here refl)         = here refl
  w-upper l (CRK.R† k w)     (there ())

∈ᶜ-lift : {C : CRK.Circuit n} {u : Fin n} → u ∈ᶜ C → suc u ∈ᶜ lift C
∈ᶜ-lift {C = g ∷ C} (here p)  = here (w-lift g p)
∈ᶜ-lift {C = g ∷ C} (there p) = there (∈ᶜ-lift p)

∈ᶜ-upper : ∀ l {C : CRK.Circuit k} {u : Fin k} → u ∈ᶜ C →
           (u ↑ˡ l) ∈ᶜ upper l C
∈ᶜ-upper l {C = g ∷ C} (here p)  = here (w-upper l g p)
∈ᶜ-upper l {C = g ∷ C} (there p) = there (∈ᶜ-upper l p)

-- The Hadamard layer touches every wire, the CNOT layer every control.

∈ᶜ-hadamards : ∀ n (u : Fin n) → u ∈ᶜ hadamards n
∈ᶜ-hadamards (suc n) zero    = here (here refl)
∈ᶜ-hadamards (suc n) (suc u) = there (∈ᶜ-lift (∈ᶜ-hadamards n u))

∈ᶜ-cnots : (ρ : Fin k → Fin l) (i : Fin k) → (k ↑ʳ ρ i) ∈ᶜ cnots ρ
∈ᶜ-cnots {suc k} ρ zero    = here (here refl)
∈ᶜ-cnots {suc k} ρ (suc i) =
  there (∈ᶜ-lift (∈ᶜ-cnots (λ j → ρ (suc j)) i))

-- Every wire of k + l is in the first block or the second.

splitᶠ : ∀ k l (u : Fin (k + l)) →
        (∃ λ i → u ≡ i ↑ˡ l) ⊎ (∃ λ j → u ≡ k ↑ʳ j)
splitᶠ zero    l u       = inj₂ (u , refl)
splitᶠ (suc k) l zero    = inj₁ (zero , refl)
splitᶠ (suc k) l (suc u) with splitᶠ k l u
... | inj₁ (i , e) = inj₁ (suc i , cong suc e)
... | inj₂ (j , e) = inj₂ (j , cong suc e)

-- The hidden shift circuit touches its n wires, the symbolic one its
-- 2n.

HS-qubits : (s : Assign (m + m)) (Bs : List (Block d m)) →
            qubitsˣ (HSᵗ s Bs) ≡ m + m
HS-qubits {m = m} s Bs = #ʷ-all (touchedˣ (HSᵗ s Bs)) (λ u →
  touchedˣ-++ˡ (hTˣ m) (fˣ s Bs ++ hTˣ m ++ f′ˣ Bs ++ hTˣ m) u
    (trans (touchedˣ-embed (hadamards (m + m)) u)
           (∈ᶜ-touched (hadamards (m + m)) u (∈ᶜ-hadamards (m + m) u))))

SS-touched : (Bs : List (Block d m)) (u : Fin ((m + m) + (m + m))) →
             u ∈ᶜ SSᶜᵗ Bs
SS-touched {m = m} Bs u with splitᶠ (m + m) (m + m) u
... | inj₁ (i , refl) =
  ∈ᶜ-++ˡ (hTˢ m) (fˢ Bs ++ hTˢ m ++ f′ˢ Bs ++ hTˢ m)
         (∈ᶜ-upper (m + m) (∈ᶜ-hadamards (m + m) i))
... | inj₂ (j , refl) =
  ∈ᶜ-++ʳ (hTˢ m) (fˢ Bs ++ hTˢ m ++ f′ˢ Bs ++ hTˢ m)
    (∈ᶜ-++ˡ (fˢ Bs) (hTˢ m ++ f′ˢ Bs ++ hTˢ m)
      (∈ᶜ-++ˡ (xTˢ m) _ (∈ᶜ-cnots (λ i → i) j)))

SS-qubits : (Bs : List (Block d m)) → qubitsˣ (SSᵗ Bs) ≡ (m + m) + (m + m)
SS-qubits Bs = trans (qubitsˣ-embed (SSᶜᵗ Bs))
                     (qubits-all (SSᶜᵗ Bs) (SS-touched Bs))




------------------------------------------------------------------------
-- printVerStats's qubit and path-variable columns

-- The wires a gate touches, as printVerStats collects them into uids,
-- and the Hadamard gates it counts as m.

wiresᵖ : Prim → List ℕ
wiresᵖ (H′ x)      = x ∷ []
wiresᵖ (X′ x)      = x ∷ []
wiresᵖ (Z′ x)      = x ∷ []
wiresᵖ (S′ x)      = x ∷ []
wiresᵖ (Sinv′ x)   = x ∷ []
wiresᵖ (T′ x)      = x ∷ []
wiresᵖ (Tinv′ x)   = x ∷ []
wiresᵖ (CNOT′ x y) = x ∷ y ∷ []
wiresᵖ (R′ _ x)    = x ∷ []
wiresᵖ (R†′ _ x)   = x ∷ []

hadamardᵖ : Prim → ℕ
hadamardᵖ (H′ _) = 1
hadamardᵖ _      = 0

-- printVerStats's n, the size of the set of wires touched (the list of
-- them without repetitions), and its m.

idsᵀ : List Prim → List ℕ
idsᵀ gs = concat (map wiresᵖ gs)

qubitsᵀ hcountᵀ : List Prim → ℕ
qubitsᵀ gs = length (deduplicate _≟ℕ_ (idsᵀ gs))
hcountᵀ    = countᵀ hadamardᵖ

-- The four numbers printVerStats prints: n, m, Clifford, T/T*.

printVerStatsᵀ : List Prim → ℕ × ℕ × ℕ × ℕ
printVerStatsᵀ gs = qubitsᵀ gs , hcountᵀ gs , cliffordsᵀ gs , tcountᵀ gs

private
  bool-iff : {a b : Bool} → (a ≡ true → b ≡ true) → (b ≡ true → a ≡ true) →
             a ≡ b
  bool-iff {true}  {true}  _ _ = refl
  bool-iff {true}  {false} f _ = sym (f refl)
  bool-iff {false} {true}  _ g = g refl
  bool-iff {false} {false} _ _ = refl

  -- Membership of a wire number, as a test.

  memᵇ : ℕ → List ℕ → Bool
  memᵇ x []       = false
  memᵇ x (y ∷ ys) = (x ≡ᵇ y) ∨ memᵇ x ys

  ≡ᵇ-refl : ∀ x → (x ≡ᵇ x) ≡ true
  ≡ᵇ-refl zero    = refl
  ≡ᵇ-refl (suc x) = ≡ᵇ-refl x

  ≡ᵇ-sound : ∀ x y → (x ≡ᵇ y) ≡ true → x ≡ y
  ≡ᵇ-sound zero    zero    _ = refl
  ≡ᵇ-sound zero    (suc y) ()
  ≡ᵇ-sound (suc x) zero    ()
  ≡ᵇ-sound (suc x) (suc y) e = cong suc (≡ᵇ-sound x y e)

  ∈⇒memᵇ : ∀ {x ys} → x ∈ ys → memᵇ x ys ≡ true
  ∈⇒memᵇ {x} {_ ∷ ys} (here refl) = cong (_∨ memᵇ x ys) (≡ᵇ-refl x)
  ∈⇒memᵇ {x} {y ∷ ys} (there p)   =
    trans (cong ((x ≡ᵇ y) ∨_) (∈⇒memᵇ p)) (∨-zeroʳ (x ≡ᵇ y))

  memᵇ⇒∈ : ∀ x ys → memᵇ x ys ≡ true → x ∈ ys
  memᵇ⇒∈ x []       ()
  memᵇ⇒∈ x (y ∷ ys) e = go (x ≡ᵇ y) refl e
    where
    go : ∀ b → (x ≡ᵇ y) ≡ b → b ∨ memᵇ x ys ≡ true → x ∈ y ∷ ys
    go true  eb _  = here (≡ᵇ-sound x y eb)
    go false _  e′ = there (memᵇ⇒∈ x ys e′)

  memᵇ-++ : ∀ x xs ys → memᵇ x (xs ++ ys) ≡ memᵇ x xs ∨ memᵇ x ys
  memᵇ-++ x []       ys = refl
  memᵇ-++ x (z ∷ xs) ys = trans (cong ((x ≡ᵇ z) ∨_) (memᵇ-++ x xs ys))
                                (sym (∨-assoc (x ≡ᵇ z) (memᵇ x xs) _))

  -- Removing repetitions keeps the members.

  memᵇ-dedup : ∀ x xs → memᵇ x (deduplicate _≟ℕ_ xs) ≡ memᵇ x xs
  memᵇ-dedup x xs = bool-iff
    (λ e → ∈⇒memᵇ (∈-deduplicate⁻ _≟ℕ_ xs (memᵇ⇒∈ x _ e)))
    (λ e → ∈⇒memᵇ (∈-deduplicate⁺ _≟ℕ_ (memᵇ⇒∈ x xs e)))

  -- Counting the wires below n that a test marks.

  #ʷ-none : ∀ n → #ʷ {n} (λ _ → false) ≡ 0
  #ʷ-none zero    = refl
  #ʷ-none (suc n) = #ʷ-none n

  #ʷ-insert : (f : Fin n → Bool) (j : Fin n) → f j ≡ false →
              #ʷ (λ k → (toℕ k ≡ᵇ toℕ j) ∨ f k) ≡ suc (#ʷ f)
  #ʷ-insert {suc n} f zero    fj =
    sym (cong (λ b → suc ((if b then 1 else 0) + #ʷ (λ u → f (suc u)))) fj)
  #ʷ-insert {suc n} f (suc j) fj =
    trans (cong ((if f zero then 1 else 0) +_)
                (#ʷ-insert (λ u → f (suc u)) j fj))
          (+-suc (if f zero then 1 else 0) (#ʷ (λ u → f (suc u))))

  -- A list without repetitions, of numbers below n, has as many
  -- elements as there are numbers below n among them.

  unique-count : (ys : List ℕ) → Unique ys → All (_< n) ys →
                 length ys ≡ #ʷ {n} (λ k → memᵇ (toℕ k) ys)
  unique-count {n} []       _          _          = sym (#ʷ-none n)
  unique-count {n} (y ∷ ys) (y∉ ∷ uys) (y<n ∷ a) =
    trans (cong suc (unique-count ys uys a))
      (sym (trans (#ʷ-cong {n} (λ k →
                     cong (λ t → (toℕ k ≡ᵇ t) ∨ memᵇ (toℕ k) ys)
                          (sym (FinP.toℕ-fromℕ< y<n))))
                  (#ʷ-insert {n} (λ k → memᵇ (toℕ k) ys) (F.fromℕ< y<n) fj)))
    where
    fj : memᵇ (toℕ (F.fromℕ< y<n)) ys ≡ false
    fj = go (memᵇ (toℕ (F.fromℕ< y<n)) ys) refl
      where
      go : ∀ b → memᵇ (toℕ (F.fromℕ< y<n)) ys ≡ b → b ≡ false
      go false _ = refl
      go true  e = ⊥-elim (All.lookup y∉
        (subst (_∈ ys) (FinP.toℕ-fromℕ< y<n)
               (memᵇ⇒∈ (toℕ (F.fromℕ< y<n)) ys e)) refl)

  -- So for any list of numbers below n: printVerStats's set size.

  dedup-count : (xs : List ℕ) → All (_< n) xs →
                length (deduplicate _≟ℕ_ xs) ≡ #ʷ {n} (λ k → memᵇ (toℕ k) xs)
  dedup-count {n} xs a =
    trans (unique-count (deduplicate _≟ℕ_ xs) (deduplicate-! xs)
             (All.tabulate (λ p → All.lookup a (∈-deduplicate⁻ _≟ℕ_ xs p))))
          (#ʷ-cong {n} (λ k → memᵇ-dedup (toℕ k) xs))

  -- The wire tests of PathSum.CRK.Qubits and of the numbered wires
  -- agree.

  ≡ᵇ-fin : (u w : Fin n) → (toℕ u ≡ᵇ toℕ w) ≡ ⌊ u FinP.≟ w ⌋
  ≡ᵇ-fin u w = go (u FinP.≟ w)
    where
    go : (d : Dec (u ≡ w)) → (toℕ u ≡ᵇ toℕ w) ≡ ⌊ d ⌋
    go (yes p) = trans (cong (λ v → toℕ u ≡ᵇ toℕ v) (sym p)) (≡ᵇ-refl (toℕ u))
    go (no ¬p) = go′ (toℕ u ≡ᵇ toℕ w) refl
      where
      go′ : ∀ b → (toℕ u ≡ᵇ toℕ w) ≡ b → b ≡ false
      go′ false _ = refl
      go′ true  e =
        ⊥-elim (¬p (FinP.toℕ-injective (≡ᵇ-sound (toℕ u) (toℕ w) e)))

  wiresᵖ-R : ∀ k x → wiresᵖ (Rᵀ k x) ≡ x ∷ []
  wiresᵖ-R zero                      x = refl
  wiresᵖ-R (suc zero)                x = refl
  wiresᵖ-R (suc (suc zero))          x = refl
  wiresᵖ-R (suc (suc (suc zero)))    x = refl
  wiresᵖ-R (suc (suc (suc (suc k)))) x = refl

  wiresᵖ-R† : ∀ k x → wiresᵖ (R†ᵀ k x) ≡ x ∷ []
  wiresᵖ-R† zero                      x = refl
  wiresᵖ-R† (suc zero)                x = refl
  wiresᵖ-R† (suc (suc zero))          x = refl
  wiresᵖ-R† (suc (suc (suc zero)))    x = refl
  wiresᵖ-R† (suc (suc (suc (suc k)))) x = refl

  hadamardᵖ-R : ∀ k x → hadamardᵖ (Rᵀ k x) ≡ 0
  hadamardᵖ-R zero                      x = refl
  hadamardᵖ-R (suc zero)                x = refl
  hadamardᵖ-R (suc (suc zero))          x = refl
  hadamardᵖ-R (suc (suc (suc zero)))    x = refl
  hadamardᵖ-R (suc (suc (suc (suc k)))) x = refl

  hadamardᵖ-R† : ∀ k x → hadamardᵖ (R†ᵀ k x) ≡ 0
  hadamardᵖ-R† zero                      x = refl
  hadamardᵖ-R† (suc zero)                x = refl
  hadamardᵖ-R† (suc (suc zero))          x = refl
  hadamardᵖ-R† (suc (suc (suc zero)))    x = refl
  hadamardᵖ-R† (suc (suc (suc (suc k)))) x = refl

  one-wire : (w u : Fin n) (ws : List ℕ) → ws ≡ toℕ w ∷ [] →
             memᵇ (toℕ u) ws ≡ elem (w ∷ []) u
  one-wire w u _ refl = cong (_∨ false) (≡ᵇ-fin u w)

  memᵇ-wires : (g : Gate n) (u : Fin n) →
               memᵇ (toℕ u) (wiresᵖ (prim g)) ≡ elem (wiresˣ g) u
  memᵇ-wires (H w)        u = one-wire w u _ refl
  memᵇ-wires (X w)        u = one-wire w u _ refl
  memᵇ-wires (CNOT c t _) u =
    cong₂ _∨_ (≡ᵇ-fin u c) (cong (_∨ false) (≡ᵇ-fin u t))
  memᵇ-wires (R k w)      u = one-wire w u _ (wiresᵖ-R k (toℕ w))
  memᵇ-wires (R† k w)     u = one-wire w u _ (wiresᵖ-R† k (toℕ w))

  memᵇ-ids : (C : Circuit n) (u : Fin n) →
             memᵇ (toℕ u) (idsᵀ (map prim C)) ≡ touchedˣ C u
  memᵇ-ids []      u = refl
  memᵇ-ids (g ∷ C) u =
    trans (memᵇ-++ (toℕ u) (wiresᵖ (prim g)) (idsᵀ (map prim C)))
          (cong₂ _∨_ (memᵇ-wires g u) (memᵇ-ids C u))

  -- Every wire number is below the width.

  wires-< : (g : Gate n) → All (_< n) (wiresᵖ (prim g))
  wires-< (H w)        = FinP.toℕ<n w ∷ []
  wires-< (X w)        = FinP.toℕ<n w ∷ []
  wires-< (CNOT c t _) = FinP.toℕ<n c ∷ FinP.toℕ<n t ∷ []
  wires-< {n} (R k w)  =
    subst (All (_< n)) (sym (wiresᵖ-R k (toℕ w))) (FinP.toℕ<n w ∷ [])
  wires-< {n} (R† k w) =
    subst (All (_< n)) (sym (wiresᵖ-R† k (toℕ w))) (FinP.toℕ<n w ∷ [])

  ids-< : (C : Circuit n) → All (_< n) (idsᵀ (map prim C))
  ids-< []      = []
  ids-< (g ∷ C) = All-++⁺ (wires-< g) (ids-< C)

-- printVerStats's n on a circuit read as the tool writes it is the
-- number of wires the circuit touches (qubitsˣ) ...

qubitsᵀ-prim : (C : Circuit n) → qubitsᵀ (map prim C) ≡ qubitsˣ C
qubitsᵀ-prim C =
  trans (dedup-count (idsᵀ (map prim C)) (ids-< C)) (#ʷ-cong (memᵇ-ids C))

-- ... and its m is the number of Hadamards, the normalisation, which is
-- the number of path variables (X allocates none).

hcountᵀ-prim : (C : Circuit n) → hcountᵀ (map prim C) ≡ norm C
hcountᵀ-prim []                 = refl
hcountᵀ-prim (H w ∷ C)          = cong suc (hcountᵀ-prim C)
hcountᵀ-prim (X w ∷ C)          = hcountᵀ-prim C
hcountᵀ-prim (CNOT c t _ ∷ C)   = hcountᵀ-prim C
hcountᵀ-prim (R k w ∷ C)        =
  trans (cong (_+ hcountᵀ (map prim C)) (hadamardᵖ-R k (toℕ w)))
        (hcountᵀ-prim C)
hcountᵀ-prim (R† k w ∷ C)       =
  trans (cong (_+ hcountᵀ (map prim C)) (hadamardᵖ-R† k (toℕ w)))
        (hcountᵀ-prim C)

hcountᵀ-paths : (C : Circuit n) → hcountᵀ (map prim C) ≡ paths C
hcountᵀ-paths C = trans (hcountᵀ-prim C) (sym (paths≡norm C))

-- The two circuits: n and 2n qubits, 3n path variables, as
-- printVerStats counts them on the tool's own lists.

HS-qubitsᵀ : (s : Assign (m + m)) (Bs : List (Block d m)) →
             qubitsᵀ (map prim (HSᵗ s Bs)) ≡ m + m
HS-qubitsᵀ s Bs = trans (qubitsᵀ-prim (HSᵗ s Bs)) (HS-qubits s Bs)

SS-qubitsᵀ : (Bs : List (Block d m)) →
             qubitsᵀ (map prim (SSᵗ Bs)) ≡ (m + m) + (m + m)
SS-qubitsᵀ Bs = trans (qubitsᵀ-prim (SSᵗ Bs)) (SS-qubits Bs)

HS-hcountᵀ : (s : Assign (m + m)) (Bs : List (Block d m)) →
             hcountᵀ (map prim (HSᵗ s Bs)) ≡ 3 * (m + m)
HS-hcountᵀ s Bs = trans (hcountᵀ-paths (HSᵗ s Bs)) (HS-paths s Bs)

SS-hcountᵀ : (Bs : List (Block d m)) →
             hcountᵀ (map prim (SSᵗ Bs)) ≡ 3 * (m + m)
SS-hcountᵀ Bs = trans (hcountᵀ-paths (SSᵗ Bs)) (SS-paths Bs)

-- All four columns at once, for every draw.

HS-printVerStats :
  (s : Assign (m + m)) (Bs : List (Block d m)) →
  printVerStatsᵀ (map prim (HSᵗ s Bs)) ≡
  (m + m , 3 * (m + m) ,
   ((8 * (m + m) + 2 * #ʷ s) + (14 + 2 * d) * length Bs) + 8 * czs Bs ,
   14 * length Bs)
HS-printVerStats s Bs =
  cong₂ _,_ (HS-qubitsᵀ s Bs)
    (cong₂ _,_ (HS-hcountᵀ s Bs)
      (cong₂ _,_ (HS-cliffords s Bs) (HS-tcount s Bs)))

SS-printVerStats :
  (Bs : List (Block d m)) →
  printVerStatsᵀ (map prim (SSᵗ Bs)) ≡
  ((m + m) + (m + m) , 3 * (m + m) ,
   (10 * (m + m) + (14 + 2 * d) * length Bs) + 8 * czs Bs ,
   14 * length Bs)
SS-printVerStats Bs =
  cong₂ _,_ (SS-qubitsᵀ Bs)
    (cong₂ _,_ (SS-hcountᵀ Bs)
      (cong₂ _,_ (SS-cliffords Bs) (SS-tcount Bs)))
------------------------------------------------------------------------
-- Table 2's rows

-- The Clifford column determines the draw's cz count c (and, for the
-- hidden shift, |s| + 4c), the other columns being the same for every
-- draw.

private
  cancel : ∀ K k t x → .{{_ : NonZero k}} → K + k * x ≡ K + k * t ⇔ x ≡ t
  cancel K k t x = mk⇔ (λ e → *-cancelˡ-≡ x t k (+-cancelˡ-≡ K _ _ e))
                       (λ e → cong (λ v → K + k * v) e)

hs-row : (s : Assign (m + m)) (Bs : List (Block d m)) (A t : ℕ) →
         length Bs ≡ A →
         cliffordsᵀ (map prim (HSᵗ s Bs)) ≡
         (8 * (m + m) + (14 + 2 * d) * A) + 2 * t ⇔
         #ʷ s + 4 * czs Bs ≡ t
hs-row {m = m} {d = d} s Bs A t eA = mk⇔
  (λ e → Equivalence.to (cancel K 2 t (#ʷ s + 4 * czs Bs))
                        (trans (sym form) e))
  (λ e → trans form (Equivalence.from (cancel K 2 t (#ʷ s + 4 * czs Bs)) e))
  where
  K : ℕ
  K = 8 * (m + m) + (14 + 2 * d) * A

  form : cliffordsᵀ (map prim (HSᵗ s Bs)) ≡ K + 2 * (#ʷ s + 4 * czs Bs)
  form = trans (HS-cliffords s Bs)
    (trans (cong (λ a → ((8 * (m + m) + 2 * #ʷ s) + (14 + 2 * d) * a) +
                        8 * czs Bs) eA)
           (solve 5 (λ n x D a c →
              ((con 8 :* n :+ con 2 :* x) :+ D :* a) :+ con 8 :* c :=
              (con 8 :* n :+ D :* a) :+ con 2 :* (x :+ con 4 :* c))
              refl (m + m) (#ʷ s) (14 + 2 * d) A (czs Bs)))

ss-row : (Bs : List (Block d m)) (A t : ℕ) → length Bs ≡ A →
         cliffordsᵀ (map prim (SSᵗ Bs)) ≡
         (10 * (m + m) + (14 + 2 * d) * A) + 8 * t ⇔ czs Bs ≡ t
ss-row {d = d} {m = m} Bs A t eA = mk⇔
  (λ e → Equivalence.to (cancel K 8 t (czs Bs)) (trans (sym form) e))
  (λ e → trans form (Equivalence.from (cancel K 8 t (czs Bs)) e))
  where
  K : ℕ
  K = 10 * (m + m) + (14 + 2 * d) * A

  form : cliffordsᵀ (map prim (SSᵗ Bs)) ≡ K + 8 * czs Bs
  form = trans (SS-cliffords Bs)
    (cong (λ a → (10 * (m + m) + (14 + 2 * d) * a) + 8 * czs Bs) eA)

-- A row, for every draw of A alternations of 200 draws: qubits, path
-- variables and T gates, and the Clifford count exactly characterised.

HSRow : ∀ m → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Set
HSRow m A q p cl t r =
  (s : Assign (m + m)) (Bs : List (Block 200 m)) → length Bs ≡ A →
  (qubitsˣ (HSᵗ s Bs) ≡ q) × (paths (HSᵗ s Bs) ≡ p) ×
  (tcountᵀ (map prim (HSᵗ s Bs)) ≡ t) ×
  (cliffordsᵀ (map prim (HSᵗ s Bs)) ≡ cl ⇔ #ʷ s + 4 * czs Bs ≡ r)

SSRow : ∀ m → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Set
SSRow m A q p cl t r =
  (Bs : List (Block 200 m)) → length Bs ≡ A →
  (qubitsˣ (SSᵗ Bs) ≡ q) × (paths (SSᵗ Bs) ≡ p) ×
  (tcountᵀ (map prim (SSᵗ Bs)) ≡ t) ×
  (cliffordsᵀ (map prim (SSᵗ Bs)) ≡ cl ⇔ czs Bs ≡ r)

private
  hs-row-at : ∀ m A r → HSRow m A (m + m) (3 * (m + m))
                (((8 * (m + m) + 414 * A) + 2 * r)) (14 * A) r
  hs-row-at m A r s Bs eA =
    HS-qubits s Bs , HS-paths s Bs ,
    trans (HS-tcount s Bs) (cong (14 *_) eA) , hs-row s Bs A r eA

  ss-row-at : ∀ m A r → SSRow m A ((m + m) + (m + m)) (3 * (m + m))
                ((10 * (m + m) + 414 * A) + 8 * r) (14 * A) r
  ss-row-at m A r Bs eA =
    SS-qubits Bs , SS-paths Bs ,
    trans (SS-tcount Bs) (cong (14 *_) eA) , ss-row Bs A r eA

-- The six rows: 20, 60, 5254, 56 with 5254 iff |s| + 4c = 1719; and
-- so on.

table-HiddenShift-20-4 : HSRow 10 4 20 60 5254 56 1719
table-HiddenShift-20-4 = hs-row-at 10 4 1719

table-HiddenShift-40-5 : HSRow 20 5 40 120 6466 70 2038
table-HiddenShift-40-5 = hs-row-at 20 5 2038

table-HiddenShift-60-10 : HSRow 30 10 60 180 12784 140 4082
table-HiddenShift-60-10 = hs-row-at 30 10 4082

table-SymbolicShift-20-4 : SSRow 10 4 40 60 5296 56 430
table-SymbolicShift-20-4 = ss-row-at 10 4 430

table-SymbolicShift-40-5 : SSRow 20 5 80 120 6638 70 521
table-SymbolicShift-40-5 = ss-row-at 20 5 521

table-SymbolicShift-60-10 : SSRow 30 10 120 180 12804 140 1008
table-SymbolicShift-60-10 = ss-row-at 30 10 1008



-- The same rows with all four columns read through the transcribed
-- printVerStats on the tool's lists: for every draw of A alternations
-- of 200 draws, printVerStats prints the row's four numbers exactly
-- when the draw has the Clifford count's |s| + 4c (or c).

HSRowᵀ : ∀ m → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Set
HSRowᵀ m A q p cl t r =
  (s : Assign (m + m)) (Bs : List (Block 200 m)) → length Bs ≡ A →
  printVerStatsᵀ (map prim (HSᵗ s Bs)) ≡ (q , p , cl , t) ⇔
  #ʷ s + 4 * czs Bs ≡ r

SSRowᵀ : ∀ m → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Set
SSRowᵀ m A q p cl t r =
  (Bs : List (Block 200 m)) → length Bs ≡ A →
  printVerStatsᵀ (map prim (SSᵗ Bs)) ≡ (q , p , cl , t) ⇔ czs Bs ≡ r

private
  -- Three columns fixed, the tuple is the fourth.

  stats⇔ : ∀ {a b c e a′ b′ c′ e′ : ℕ} {P : Set} →
           a ≡ a′ → b ≡ b′ → e ≡ e′ → (c ≡ c′ ⇔ P) →
           ((a , b , c , e) ≡ (a′ , b′ , c′ , e′)) ⇔ P
  stats⇔ {a} {b} {c} {e} refl refl refl h = mk⇔
    (λ eq → Equivalence.to h (cong (λ x → proj₁ (proj₂ (proj₂ x))) eq))
    (λ p → cong (λ x → a , b , x , e) (Equivalence.from h p))

  hs-rowᵀ-at : ∀ m A r → HSRowᵀ m A (m + m) (3 * (m + m))
                 ((8 * (m + m) + 414 * A) + 2 * r) (14 * A) r
  hs-rowᵀ-at m A r s Bs eA =
    stats⇔ (HS-qubitsᵀ s Bs) (HS-hcountᵀ s Bs)
           (trans (HS-tcount s Bs) (cong (14 *_) eA)) (hs-row s Bs A r eA)

  ss-rowᵀ-at : ∀ m A r → SSRowᵀ m A ((m + m) + (m + m)) (3 * (m + m))
                 ((10 * (m + m) + 414 * A) + 8 * r) (14 * A) r
  ss-rowᵀ-at m A r Bs eA =
    stats⇔ (SS-qubitsᵀ Bs) (SS-hcountᵀ Bs)
           (trans (SS-tcount Bs) (cong (14 *_) eA)) (ss-row Bs A r eA)

table-HiddenShift-20-4ᵀ : HSRowᵀ 10 4 20 60 5254 56 1719
table-HiddenShift-20-4ᵀ = hs-rowᵀ-at 10 4 1719

table-HiddenShift-40-5ᵀ : HSRowᵀ 20 5 40 120 6466 70 2038
table-HiddenShift-40-5ᵀ = hs-rowᵀ-at 20 5 2038

table-HiddenShift-60-10ᵀ : HSRowᵀ 30 10 60 180 12784 140 4082
table-HiddenShift-60-10ᵀ = hs-rowᵀ-at 30 10 4082

table-SymbolicShift-20-4ᵀ : SSRowᵀ 10 4 40 60 5296 56 430
table-SymbolicShift-20-4ᵀ = ss-rowᵀ-at 10 4 430

table-SymbolicShift-40-5ᵀ : SSRowᵀ 20 5 80 120 6638 70 521
table-SymbolicShift-40-5ᵀ = ss-rowᵀ-at 20 5 521

table-SymbolicShift-60-10ᵀ : SSRowᵀ 30 10 120 180 12804 140 1008
table-SymbolicShift-60-10ᵀ = ss-rowᵀ-at 30 10 1008

------------------------------------------------------------------------
-- Draws attaining the rows

-- A block of the tool's shape: a ccz on x0 x1 x2, then k draws cz x0 x1
-- and l draws Z x0.

drawsᵏ : (k l : ℕ) → Vec (Draw (suc (suc (suc m)))) (k + l)
drawsᵏ zero    zero    = V.[]
drawsᵏ zero    (suc l) = Zᵈ zero V.∷ drawsᵏ zero l
drawsᵏ (suc k) l       = CZᵈ zero (suc zero) (λ ()) V.∷ drawsᵏ k l

blockᵏ : (k l : ℕ) → Block (k + l) (suc (suc (suc m)))
blockᵏ k l =
  block zero (suc zero) (suc (suc zero)) (λ ()) (λ ()) (λ ()) (drawsᵏ k l)

-- The shift on the first k wires.

firsts : ℕ → Assign n
firsts k i = toℕ i <ᵇ k

-- One draw for each row: |s| and the blocks' cz counts below; each
-- attains the row's Clifford count, and so the whole row.

HS-20-4-attained :
  ∃₂ λ (s : Assign 20) (Bs : List (Block 200 10)) →
  (length Bs ≡ 4) × (cliffordsᵀ (map prim (HSᵗ s Bs)) ≡ 5254)
HS-20-4-attained = firsts 7 , Bs , refl ,
  Equivalence.from
    (proj₂ (proj₂ (proj₂ (table-HiddenShift-20-4 (firsts 7) Bs refl)))) refl
  where
  Bs : List (Block 200 10)
  Bs = blockᵏ 107 93 ∷ blockᵏ 107 93 ∷ blockᵏ 107 93 ∷ blockᵏ 107 93 ∷ []

HS-40-5-attained :
  ∃₂ λ (s : Assign 40) (Bs : List (Block 200 20)) →
  (length Bs ≡ 5) × (cliffordsᵀ (map prim (HSᵗ s Bs)) ≡ 6466)
HS-40-5-attained = firsts 18 , Bs , refl ,
  Equivalence.from
    (proj₂ (proj₂ (proj₂ (table-HiddenShift-40-5 (firsts 18) Bs refl)))) refl
  where
  Bs : List (Block 200 20)
  Bs = blockᵏ 101 99 ∷ blockᵏ 101 99 ∷ blockᵏ 101 99 ∷ blockᵏ 101 99 ∷
       blockᵏ 101 99 ∷ []

HS-60-10-attained :
  ∃₂ λ (s : Assign 60) (Bs : List (Block 200 30)) →
  (length Bs ≡ 10) × (cliffordsᵀ (map prim (HSᵗ s Bs)) ≡ 12784)
HS-60-10-attained = firsts 30 , Bs , refl ,
  Equivalence.from
    (proj₂ (proj₂ (proj₂ (table-HiddenShift-60-10 (firsts 30) Bs refl)))) refl
  where
  Bs : List (Block 200 30)
  Bs = blockᵏ 102 98 ∷ blockᵏ 102 98 ∷ blockᵏ 102 98 ∷ blockᵏ 101 99 ∷
       blockᵏ 101 99 ∷ blockᵏ 101 99 ∷ blockᵏ 101 99 ∷ blockᵏ 101 99 ∷
       blockᵏ 101 99 ∷ blockᵏ 101 99 ∷ []

SS-20-4-attained :
  ∃ λ (Bs : List (Block 200 10)) →
  (length Bs ≡ 4) × (cliffordsᵀ (map prim (SSᵗ Bs)) ≡ 5296)
SS-20-4-attained = Bs , refl ,
  Equivalence.from
    (proj₂ (proj₂ (proj₂ (table-SymbolicShift-20-4 Bs refl)))) refl
  where
  Bs : List (Block 200 10)
  Bs = blockᵏ 108 92 ∷ blockᵏ 108 92 ∷ blockᵏ 107 93 ∷ blockᵏ 107 93 ∷ []

SS-40-5-attained :
  ∃ λ (Bs : List (Block 200 20)) →
  (length Bs ≡ 5) × (cliffordsᵀ (map prim (SSᵗ Bs)) ≡ 6638)
SS-40-5-attained = Bs , refl ,
  Equivalence.from
    (proj₂ (proj₂ (proj₂ (table-SymbolicShift-40-5 Bs refl)))) refl
  where
  Bs : List (Block 200 20)
  Bs = blockᵏ 105 95 ∷ blockᵏ 104 96 ∷ blockᵏ 104 96 ∷ blockᵏ 104 96 ∷
       blockᵏ 104 96 ∷ []

SS-60-10-attained :
  ∃ λ (Bs : List (Block 200 30)) →
  (length Bs ≡ 10) × (cliffordsᵀ (map prim (SSᵗ Bs)) ≡ 12804)
SS-60-10-attained = Bs , refl ,
  Equivalence.from
    (proj₂ (proj₂ (proj₂ (table-SymbolicShift-60-10 Bs refl)))) refl
  where
  Bs : List (Block 200 30)
  Bs = blockᵏ 101 99 ∷ blockᵏ 101 99 ∷ blockᵏ 101 99 ∷ blockᵏ 101 99 ∷
       blockᵏ 101 99 ∷ blockᵏ 101 99 ∷ blockᵏ 101 99 ∷ blockᵏ 101 99 ∷
       blockᵏ 100 100 ∷ blockᵏ 100 100 ∷ []

-- The same draws print the rows' four numbers.

private
  attainᴴ : ∀ {m A q p cl t r q′ p′} → HSRow m A q p cl t r →
            HSRowᵀ m A q′ p′ cl t r →
            (∃₂ λ (s : Assign (m + m)) (Bs : List (Block 200 m)) →
               (length Bs ≡ A) × (cliffordsᵀ (map prim (HSᵗ s Bs)) ≡ cl)) →
            ∃₂ λ (s : Assign (m + m)) (Bs : List (Block 200 m)) →
              (length Bs ≡ A) ×
              (printVerStatsᵀ (map prim (HSᵗ s Bs)) ≡ (q′ , p′ , cl , t))
  attainᴴ row rowᵀ (s , Bs , e , c) = s , Bs , e ,
    Equivalence.from (rowᵀ s Bs e)
      (Equivalence.to (proj₂ (proj₂ (proj₂ (row s Bs e)))) c)

  attainˢ : ∀ {m A q p cl t r q′ p′} → SSRow m A q p cl t r →
            SSRowᵀ m A q′ p′ cl t r →
            (∃ λ (Bs : List (Block 200 m)) →
               (length Bs ≡ A) × (cliffordsᵀ (map prim (SSᵗ Bs)) ≡ cl)) →
            ∃ λ (Bs : List (Block 200 m)) →
              (length Bs ≡ A) ×
              (printVerStatsᵀ (map prim (SSᵗ Bs)) ≡ (q′ , p′ , cl , t))
  attainˢ row rowᵀ (Bs , e , c) = Bs , e ,
    Equivalence.from (rowᵀ Bs e)
      (Equivalence.to (proj₂ (proj₂ (proj₂ (row Bs e)))) c)

HS-20-4-attainedᵀ :
  ∃₂ λ (s : Assign 20) (Bs : List (Block 200 10)) →
  (length Bs ≡ 4) ×
  (printVerStatsᵀ (map prim (HSᵗ s Bs)) ≡ (20 , 60 , 5254 , 56))
HS-20-4-attainedᵀ =
  attainᴴ table-HiddenShift-20-4 table-HiddenShift-20-4ᵀ HS-20-4-attained

HS-40-5-attainedᵀ :
  ∃₂ λ (s : Assign 40) (Bs : List (Block 200 20)) →
  (length Bs ≡ 5) ×
  (printVerStatsᵀ (map prim (HSᵗ s Bs)) ≡ (40 , 120 , 6466 , 70))
HS-40-5-attainedᵀ =
  attainᴴ table-HiddenShift-40-5 table-HiddenShift-40-5ᵀ HS-40-5-attained

HS-60-10-attainedᵀ :
  ∃₂ λ (s : Assign 60) (Bs : List (Block 200 30)) →
  (length Bs ≡ 10) ×
  (printVerStatsᵀ (map prim (HSᵗ s Bs)) ≡ (60 , 180 , 12784 , 140))
HS-60-10-attainedᵀ =
  attainᴴ table-HiddenShift-60-10 table-HiddenShift-60-10ᵀ HS-60-10-attained

SS-20-4-attainedᵀ :
  ∃ λ (Bs : List (Block 200 10)) →
  (length Bs ≡ 4) ×
  (printVerStatsᵀ (map prim (SSᵗ Bs)) ≡ (40 , 60 , 5296 , 56))
SS-20-4-attainedᵀ =
  attainˢ table-SymbolicShift-20-4 table-SymbolicShift-20-4ᵀ SS-20-4-attained

SS-40-5-attainedᵀ :
  ∃ λ (Bs : List (Block 200 20)) →
  (length Bs ≡ 5) ×
  (printVerStatsᵀ (map prim (SSᵗ Bs)) ≡ (80 , 120 , 6638 , 70))
SS-40-5-attainedᵀ =
  attainˢ table-SymbolicShift-40-5 table-SymbolicShift-40-5ᵀ SS-40-5-attained

SS-60-10-attainedᵀ :
  ∃ λ (Bs : List (Block 200 30)) →
  (length Bs ≡ 10) ×
  (printVerStatsᵀ (map prim (SSᵗ Bs)) ≡ (120 , 180 , 12804 , 140))
SS-60-10-attainedᵀ =
  attainˢ table-SymbolicShift-60-10 table-SymbolicShift-60-10ᵀ SS-60-10-attained

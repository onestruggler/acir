/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The local facts of the generic step

Toward Theorem 4.4 on three or more wires.  The Schreier conditions of the
stabiliser chain reduce to the equations below between words on at most
three wires (`gen/facts3.py`), each derived from (C15)-(C18) with free
two-wire segments, so given completeness on two wires (`lib3_valid`).
Every fact reads `lhs = k ⨾ rhs` with `k` a list of tokens of the
stabiliser of stage 1 (`S1a`-`S1h`) or stage 2 (`S2a`-`S2g`); its index in
the three-wire table and its `k` are those of `Facts3Data.lean`, and each
family is checked against the table by computation.  Names (time order;
`p`, `q` points of one wire, `x` one of `H`, `S` on wire `0`, `↑` one wire
up):

* (S1a) `alpha p ⨾ x = k ⨾ alpha (x·p)` (`p ≠ 0`);
  (S1b) `Gam p ⨾ x = k ⨾ Gam (x·p)`;
  (S1c) `Gam p ⨾ c = k ⨾ Gam p`, `c` one of `S`, `X`, `Z` on wire `1`;
  (S1d) `Gam p ⨾ CZ₁₂ = k ⨾ Gam p`;
  (S1e) `alpha p ⨾ W0 = k ⨾ W0 ⨾ alpha p↑` (`p ≠ 0`);
  (S1f) `Gam p ⨾ alpha q↑ ⨾ W0 = k ⨾ sigma [q, p]` (`q ≠ 0`);
  (S1g) `Gam p ⨾ Gam q↑ ⨾ W0 = k ⨾ Gam q ⨾ Gam p↑`;
  (S1h) `CZ₀₁ = W1 ⨾ W0 ⨾ CZ₁₂ ⨾ W0 ⨾ W1`;
* (S2a) `Q i ⨾ s = k ⨾ Q (s·i)`, `s` one of `S`, `X`, `Z` on wire `0`;
  (S2b) `Q i ⨾ CZ ⨾ s = k ⨾ Q (s·i) ⨾ CZ`;
  (S2c) `CZ ⨾ c = k ⨾ CZ`, `c` one of `S`, `X`, `Z` on wire `1`;
  (S2d) `CZ₀₁ ⨾ CZ₁₂ = CZ₁₂ ⨾ CZ₀₁`;
  (S2e) `Q i ⨾ t = k ⨾ Q i`, `t` one of `X`, `Z` on wire `0`;
  (S2f) `Q i ⨾ CZ ⨾ alpha q↑ ⨾ CZ = k ⨾ tau [(1, i + a), (a, b + 1)]`
  (`q = (a, b) ≠ 0`);
  (S2g) `Q i ⨾ CZ ⨾ Gam q↑ ⨾ CZ = k ⨾ Q (i + a) ⨾ CZ ⨾ Gam (a, b + 1)↑`.
-/
import QCert.QutritClifford.Sections
import QCert.QutritClifford.Lib3

namespace QCert.QutritClifford

/-- The words `S`, `X`, `Z` on wire `1`, by index. -/
def cw1 : ℕ → List Lt
  | 0 => [.S 1]
  | 1 => X0w.map Lt.up
  | _ => Z0w.map Lt.up

/-- The bottom tokens `S`, `X`, `Z`, by index. -/
def sw0 : ℕ → Tok
  | 0 => .S0
  | 1 => .X0
  | _ => .Z0

/-- The tokens `X`, `Z`, by index. -/
def tw0 : ℕ → Tok
  | 0 => .X0
  | _ => .Z0

/-- `H` or `S` on wire `0`, by index. -/
def xw0 : ℕ → Lt
  | 0 => .H 0
  | _ => .S 0

/-- The number of checked entries of the three-wire table. -/
abbrev nlib3 : ℕ := base3.length + 363

/-- An entry of the table, checked: its index is below `nlib3`, it is the
equation `l = kw k ++ r`, and `k` is a list of tokens of the given kind. -/
def entOk (e : ℕ × List Tok) (l r : List Lt) (kind : Bool) : Bool :=
  decide (e.1 < nlib3) && lib3T[e.1]? == some (l, kw e.2 ++ r) &&
    (if kind then K1b 3 e.2 else K2b 3 e.2)

theorem of_entOk (hc : Complete 2) {e : ℕ × List Tok} {l r : List Lt} {kind : Bool}
    (h : entOk e l r kind = true) : E 3 l (kw e.2 ++ r) := by
  simp only [entOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact (lib3_valid hc).get e.1 h.1.1 h.1.2

theorem K1_of_entOk {e : ℕ × List Tok} {l r : List Lt} (h : entOk e l r true = true) :
    K1 3 e.2 := by
  simp only [entOk, Bool.and_eq_true, ite_true] at h
  exact K1_of_b h.2

theorem K2_of_entOk {e : ℕ × List Tok} {l r : List Lt} (h : entOk e l r false = true) :
    K2 3 e.2 := by
  simp only [entOk, Bool.and_eq_true, Bool.false_eq_true, ite_false] at h
  exact K2_of_b h.2

/-! ### Stage 1 -/

def eS1a (p : Fin 3 × Fin 3) (g : ℕ) : ℕ × List Tok := ent fS1a (2 * (pidx p - 1) + g)
theorem ok_S1a : ∀ p : Fin 3 × Fin 3, p ≠ (0, 0) → ∀ g < 2,
    entOk (eS1a p g) (alpha p ++ [xw0 g]) (alpha (pt1 (xw0 g) p)) true = true := by
  decide +kernel

def eS1b (p : Fin 3 × Fin 3) (g : ℕ) : ℕ × List Tok := ent fS1b (2 * pidx p + g)
theorem ok_S1b : ∀ p : Fin 3 × Fin 3, ∀ g < 2,
    entOk (eS1b p g) (Gam p ++ [xw0 g]) (Gam (pt1 (xw0 g) p)) true = true := by
  decide +kernel

def eS1c (p : Fin 3 × Fin 3) (c : ℕ) : ℕ × List Tok := ent fS1c (3 * pidx p + c)
theorem ok_S1c : ∀ p : Fin 3 × Fin 3, ∀ c < 3,
    entOk (eS1c p c) (Gam p ++ cw1 c) (Gam p) true = true := by
  decide +kernel

def eS1d (p : Fin 3 × Fin 3) : ℕ × List Tok := ent fS1d (pidx p)
theorem ok_S1d : ∀ p : Fin 3 × Fin 3, entOk (eS1d p) (Gam p ++ [.C 1]) (Gam p) true = true := by
  decide +kernel

def eS1e (p : Fin 3 × Fin 3) : ℕ × List Tok := ent fS1e (pidx p - 1)
theorem ok_S1e : ∀ p : Fin 3 × Fin 3, p ≠ (0, 0) →
    entOk (eS1e p) (alpha p ++ W0) (W0 ++ (alpha p).map Lt.up) true = true := by
  decide +kernel

def eS1f (p q : Fin 3 × Fin 3) : ℕ × List Tok := ent fS1f (8 * pidx p + (pidx q - 1))
theorem ok_S1f : ∀ p q : Fin 3 × Fin 3, q ≠ (0, 0) →
    entOk (eS1f p q) (Gam p ++ (alpha q).map Lt.up ++ W0)
      (if p = (0, 0) then alpha q else Gam q ++ (alpha p).map Lt.up) true = true := by
  decide +kernel

def eS1g (p q : Fin 3 × Fin 3) : ℕ × List Tok := ent fS1g (9 * pidx p + pidx q)
theorem ok_S1g : ∀ p q : Fin 3 × Fin 3,
    entOk (eS1g p q) (Gam p ++ (Gam q).map Lt.up ++ W0) (Gam q ++ (Gam p).map Lt.up) true =
      true := by
  decide +kernel

theorem ok_S1h : entOk (ent fS1h 0) [.C 0] (W1 ++ W0 ++ [.C 1] ++ W0 ++ W1) true = true := by
  decide +kernel

/-! ### Stage 2 -/

def eS2a (i : Fin 3) (s : ℕ) : ℕ × List Tok := ent fS2a (3 * i.val + s)
theorem ok_S2a : ∀ i : Fin 3, ∀ s < 3,
    entOk (eS2a i s) (Qw i ++ (sw0 s).word) (Qw (snext (sw0 s) i)) false = true := by
  decide +kernel

def eS2b (i : Fin 3) (s : ℕ) : ℕ × List Tok := ent fS2b (3 * i.val + s)
theorem ok_S2b : ∀ i : Fin 3, ∀ s < 3,
    entOk (eS2b i s) (Qw i ++ [.C 0] ++ (sw0 s).word) (Qw (snext (sw0 s) i) ++ [.C 0]) false =
      true := by
  decide +kernel

def eS2c (c : ℕ) : ℕ × List Tok := ent fS2c c
theorem ok_S2c : ∀ c < 3, entOk (eS2c c) ([.C 0] ++ cw1 c) [.C 0] false = true := by
  decide +kernel

theorem ok_S2d : entOk (ent fS2d 0) [.C 0, .C 1] [.C 0] false = true := by
  decide +kernel

def eS2e (i : Fin 3) (t : ℕ) : ℕ × List Tok := ent fS2e (2 * i.val + t)
theorem ok_S2e : ∀ i : Fin 3, ∀ t < 2,
    entOk (eS2e i t) (Qw i ++ (tw0 t).word) (Qw i) false = true := by
  decide +kernel

def eS2f (i : Fin 3) (q : Fin 3 × Fin 3) : ℕ × List Tok := ent fS2f (8 * i.val + (pidx q - 1))
theorem ok_S2f : ∀ i : Fin 3, ∀ q : Fin 3 × Fin 3, q ≠ (0, 0) →
    entOk (eS2f i q) (Qw i ++ [.C 0] ++ (alpha q).map Lt.up ++ [.C 0])
      (if (q.1, q.2 + 1) = (0, 0) then Qw (i + q.1)
        else Qw (i + q.1) ++ [.C 0] ++ (alpha (q.1, q.2 + 1)).map Lt.up) false = true := by
  decide +kernel

def eS2g (i : Fin 3) (q : Fin 3 × Fin 3) : ℕ × List Tok := ent fS2g (9 * i.val + pidx q)
theorem ok_S2g : ∀ i : Fin 3, ∀ q : Fin 3 × Fin 3,
    entOk (eS2g i q) (Qw i ++ [.C 0] ++ (Gam q).map Lt.up ++ [.C 0])
      (Qw (i + q.1) ++ [.C 0] ++ (Gam (q.1, q.2 + 1)).map Lt.up) false = true := by
  decide +kernel

end QCert.QutritClifford

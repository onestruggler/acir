"""Write Families.lean: every family of Table 1, decided by nested Bool loops
over the indices (`allBelow`), pruned as soon as an order constraint fails."""
from paths import work, data, module
import sys
OUT = sys.argv[1] if len(sys.argv) > 1 else module("Families.lean")

# Each family: (name, constructor, vars, guards, nodup, conclusion, rel_l, rel_r, kind)
#   vars: the constructor's index variables in order; guards: list of (var, [(x, y)]) meaning
#   constraints x < y checked once var is bound (all constraints of the family);
#   nodup: list of variables for a Nodup hypothesis (or None);
#   ctor args: the hypotheses of the constructor in order (names).
# Lean expressions use the variables as ℕ (`a` stands for `↑a`).
FAMS = []
def fam(name, ctor, vars_, lt, nodup, hyps, concl, lhs, rhs, mode):
    FAMS.append(dict(name=name, ctor=ctor, vars=vars_, lt=lt, nodup=nodup, hyps=hyps,
                     concl=concl, lhs=lhs, rhs=rhs, mode=mode))

# palindromic families: mode 'pal' with (a, b) of the conjugating X and generator lists
fam("2a", "r2a", "a b c d", [("a", "b"), ("c", "d")], "a b c d", "hab hcd hn",
    "okPal a b (.x c d) (.x c d)", "[.x a b hab, .x c d hcd]", "[.x c d hcd, .x a b hab]", ("pal", "hab", "b"))
fam("2b", "r2b", "a b c", [("a", "b")], "a b c", "hab hn",
    "okPal a b (.n c) (.n c)", "[.x a b hab, .neg c]", "[.neg c, .x a b hab]", ("pal", "hab", "b"))
fam("2c", "r2c", "a b c d e f", [("a", "b"), ("c", "d"), ("d", "e"), ("e", "f")], "a b c d e f",
    "hab hcd hde hef hn", "okPal a b (.k c d e f) (.k c d e f)",
    "[.x a b hab, .k c d e f hcd hde hef]", "[.k c d e f hcd hde hef, .x a b hab]", ("pal", "hab", "b"))
fam("3a", "r3a", "a a' b", [("a", "a'"), ("a'", "b")], None, "h₁ h₂",
    "okPal a a' (.x a b) (.x a' b)", "[.x a a' h₁, .x a b (h₁.trans h₂)]", "[.x a' b h₂, .x a a' h₁]",
    ("pal", "h₁", "a'"))
fam("3b", "r3b", "a b b'", [("a", "b"), ("b", "b'")], None, "h₁ h₂",
    "okPal b b' (.x a b) (.x a b')", "[.x b b' h₂, .x a b h₁]", "[.x a b' (h₁.trans h₂), .x b b' h₂]",
    ("pal", "h₂", "b'"))
fam("3c", "r3c", "a b", [("a", "b")], None, "hab",
    "okPal a b (.n b) (.n a)", "[.x a b hab, .neg b]", "[.neg a, .x a b hab]", ("pal", "hab", "b"))
fam("3d", "r3d", "a a' b c d", [("a", "a'"), ("a'", "b"), ("b", "c"), ("c", "d")], None, "h₁ h₂ hbc hcd",
    "okPal a a' (.k a b c d) (.k a' b c d)", "[.x a a' h₁, .k a b c d (h₁.trans h₂) hbc hcd]",
    "[.k a' b c d h₂ hbc hcd, .x a a' h₁]", ("pal", "h₁", "a'"))
fam("3e", "r3e", "a b b' c d", [("a", "b"), ("b", "b'"), ("b'", "c"), ("c", "d")], None, "hab h₁ h₂ hcd",
    "okPal b b' (.k a b c d) (.k a b' c d)", "[.x b b' h₁, .k a b c d hab (h₁.trans h₂) hcd]",
    "[.k a b' c d (hab.trans h₁) h₂ hcd, .x b b' h₁]", ("pal", "h₁", "b'"))
fam("3f", "r3f", "a b c c' d", [("a", "b"), ("b", "c"), ("c", "c'"), ("c'", "d")], None, "hab hbc h₁ h₂",
    "okPal c c' (.k a b c d) (.k a b c' d)", "[.x c c' h₁, .k a b c d hab hbc (h₁.trans h₂)]",
    "[.k a b c' d hab (hbc.trans h₁) h₂, .x c c' h₁]", ("pal", "h₁", "c'"))
fam("3g", "r3g", "a b c d d'", [("a", "b"), ("b", "c"), ("c", "d"), ("d", "d'")], None, "hab hbc hcd h₁",
    "okPal d d' (.k a b c d) (.k a b c d')", "[.x d d' h₁, .k a b c d hab hbc hcd]",
    "[.k a b c d' hab hbc (hcd.trans h₁), .x d d' h₁]", ("pal", "h₁", "d'"))
# families with a standard instance
fam("1b", "r1b", "a", [], None, "",
    "ok (path [0] [a]) [.n 0, .n 0] [] [.n a, .n a] []", "[.neg a, .neg a]", "[]", ("std",))
fam("1c", "r1c", "a b c d", [("a", "b"), ("b", "c"), ("c", "d")], None, "hab hbc hcd",
    "ok (path [0, 1, 2, 3] [a, b, c, d]) [.k 0 1 2 3, .k 0 1 2 3] [] [.k a b c d, .k a b c d] []",
    "[.k a b c d hab hbc hcd, .k a b c d hab hbc hcd]", "[]", ("std",))
fam("2d", "r2d", "a b", [], None, "hn",
    "ok (path [0, 4] [a, b]) [.n 0, .n 4] [.n 4, .n 0] [.n a, .n b] [.n b, .n a]",
    "[.neg a, .neg b]", "[.neg b, .neg a]", ("std",))
fam("2e", "r2e", "a b c d e", [("b", "c"), ("c", "d"), ("d", "e")], "a b c d e", "hbc hcd hde hn",
    "ok (path [4, 0, 1, 2, 3] [a, b, c, d, e]) [.n 4, .k 0 1 2 3] [.k 0 1 2 3, .n 4] "
    "[.n a, .k b c d e] [.k b c d e, .n a]",
    "[.neg a, .k b c d e hbc hcd hde]", "[.k b c d e hbc hcd hde, .neg a]", ("std",))
fam("2f", "r2f", "a b c d e f g h", [("a", "b"), ("b", "c"), ("c", "d"), ("e", "f"), ("f", "g"), ("g", "h")],
    "a b c d e f g h", "hab hbc hcd hef hfg hgh hn",
    "ok (path [0, 1, 2, 3, 4, 5, 6, 7] [a, b, c, d, e, f, g, h]) [.k 0 1 2 3, .k 4 5 6 7] "
    "[.k 4 5 6 7, .k 0 1 2 3] [.k a b c d, .k e f g h] [.k e f g h, .k a b c d]",
    "[.k a b c d hab hbc hcd, .k e f g h hef hfg hgh]", "[.k e f g h hef hfg hgh, .k a b c d hab hbc hcd]",
    ("std",))
for nm, xl, xr, rl, rr in [
        ("4a", "[.x 0 1, .k 0 1 2 3]", "[.k 0 1 2 3, .x 1 3, .n 1, .n 3]",
         "[.x a b hab, .k a b c d hab hbc hcd]", "[.k a b c d hab hbc hcd, .x b d (hbc.trans hcd), .neg b, .neg d]"),
        ("4b", "[.x 1 2, .k 0 1 2 3]", "[.n 0, .k 0 1 2 3, .n 0, .k 0 1 2 3, .n 0]",
         "[.x b c hbc, .k a b c d hab hbc hcd]",
         "[.neg a, .k a b c d hab hbc hcd, .neg a, .k a b c d hab hbc hcd, .neg a]"),
        ("4c", "[.x 2 3, .k 0 1 2 3]", "[.k 0 1 2 3, .x 1 3]",
         "[.x c d hcd, .k a b c d hab hbc hcd]", "[.k a b c d hab hbc hcd, .x b d (hbc.trans hcd)]")]:
    tl = {"4a": ("[.x a b, .k a b c d]", "[.k a b c d, .x b d, .n b, .n d]"),
          "4b": ("[.x b c, .k a b c d]", "[.n a, .k a b c d, .n a, .k a b c d, .n a]"),
          "4c": ("[.x c d, .k a b c d]", "[.k a b c d, .x b d]")}[nm]
    fam(nm, "r" + nm, "a b c d", [("a", "b"), ("b", "c"), ("c", "d")], None, "hab hbc hcd",
        f"ok (path [0, 1, 2, 3] [a, b, c, d]) {xl} {xr} {tl[0]} {tl[1]}", rl, rr, ("std",))
fam("5a", "r5a", "a b c d e f", [("a", "b"), ("b", "c"), ("c", "d"), ("d", "e"), ("e", "f")], None,
    "hab hbc hcd hde hef",
    "ok (path [0, 1, 2, 3, 4, 5] [a, b, c, d, e, f]) [.k 0 1 2 3, .k 1 3 4 5] [.k 2 3 4 5, .k 0 1 2 4] "
    "[.k a b c d, .k b d e f] [.k c d e f, .k a b c e]",
    "[.k a b c d hab hbc hcd, .k b d e f (hbc.trans hcd) hde hef]",
    "[.k c d e f hcd hde hef, .k a b c e hab hbc (hcd.trans hde)]", ("std",))
fam("6a", "r6a", "a b c d e f g h", [("a", "b"), ("b", "c"), ("c", "d"), ("d", "e"), ("e", "f"), ("f", "g"),
    ("g", "h")], None, "hab hbc hcd hde hef hfg hgh",
    "(Engine.eqns std6aTable).contains (encL [.n a, .n e, .x a e, .k e f g h, .k a b c d, .x d e, "
    ".k a b c d, .k e f g h, .x a e, .n a, .n e], encL [.k e f g h, .k a b c d, .x d e, .k a b c d, .k e f g h])",
    "[.neg a, .neg e, .x a e (hab.trans (hbc.trans (hcd.trans hde))), .k e f g h hef hfg hgh, "
    ".k a b c d hab hbc hcd, .x d e hde, .k a b c d hab hbc hcd, .k e f g h hef hfg hgh, "
    ".x a e (hab.trans (hbc.trans (hcd.trans hde))), .neg a, .neg e]",
    "[.k e f g h hef hfg hgh, .k a b c d hab hbc hcd, .x d e hde, .k a b c d hab hbc hcd, .k e f g h hef hfg hgh]",
    ("6a",))

def nested(f):
    vs = f["vars"].split()
    lt = f["lt"]
    # constraints checked as soon as both ends are bound
    bound = []
    out = ""
    closers = 0
    body_parts = []
    for v in vs:
        bound.append(v)
        cs = [(x, y) for (x, y) in lt if y == v and x in bound] + [(x, y) for (x, y) in lt if x == v and y in bound]
        g = " ∧ ".join(f"{x} < {y}" for (x, y) in cs)
        if f["name"] == "2d" and v == "b":
            g = "a ≠ b"
        if g:
            out += f"allBelow 8 fun {v} => !decide ({g}) || "
        else:
            out += f"allBelow 8 fun {v} => "
    final = f["concl"]
    if f["nodup"]:
        final = f"!decide ([{', '.join(f['nodup'].split())}].Nodup) || {final}"
    return out + "(" + final + ")"

def extract(f):
    vs = f["vars"].split()
    lt = f["lt"]
    hyps = f["hyps"].split()
    hyp_of = {p: hyps[i] for i, p in enumerate(lt)}
    bound = []
    t = f"fam{f['name']}_all"
    for v in vs:
        bound.append(v)
        t = f"(allBelow_spec {t} {v}.isLt)"
        cs = [(x, y) for (x, y) in lt if y == v and x in bound] + [(x, y) for (x, y) in lt if x == v and y in bound]
        if f["name"] == "2d" and v == "b":
            t = f"(imp_spec {t} (fun e => hn (Fin.ext e)))"
        elif cs:
            pf = hyp_of[cs[0]] if len(cs) == 1 else "⟨" + ", ".join(hyp_of[c] for c in cs) + "⟩"
            t = f"(imp_spec {t} {pf})"
    if f["nodup"]:
        t = f"(imp_spec {t} (nodup_val {hyps[-1]}))"
    return t

def extract_old(f):
    """term proving the conclusion from the decided nest, with the Fin variables"""
    vs = f["vars"].split()
    lt = f["lt"]
    bound = []
    t = f"fam{f['name']}_all"
    for v in vs:
        bound.append(v)
        t = f"(allBelow_spec {t} {v}.isLt)"
        cs = [(x, y) for (x, y) in lt if y == v and x in bound] + [(x, y) for (x, y) in lt if x == v and y in bound]
        if cs:
            pf = " ⟨".join(["(by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact "] ) if False else None
            # proof of the conjunction of decide's
            props = [f"({x} : ℕ) < {y}" for (x, y) in cs]
            hyp = "(by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)"
            t = f"(imp_spec' {t} {hyp})"
    if f["nodup"]:
        nd = " ".join(f["nodup"].split())
        t = f"(imp_spec {t} (nodup_val hn))"
    return t

L = []
L.append("""/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): every relation of Table 1 over the macro alphabet

Li–Ross–Selinger's Table 1 at `n = 8` has 2123 instances.  Each family is
derived at every index from `Transport.lean`:

* (2a)–(2c), (3a)–(3g) (1372 instances) are conjugation by `X_[a,b]` itself:
  its encoding is the word of the palindromic path of `(a b)`, so they
  follow from `pal` once that path is valid for the other generator
  (`okPal`), and (1a) (28 instances) from `pathW_cancel`;
* (1b), (1c), (2d), (2e), (2f), (4a)–(4c), (5a) (722 instances) are carried
  along a bubble-sort path (`path`) from one standard instance, a relation
  of Figure 7 ((83), (84), (95), (94), (96), (97), (98), (99), (100)), and the
  one instance of (6a) is derived from (101) (`std6aTable`).

For each family one `decide +kernel` (`fam…_all`) checks, for every
instance, that every step of the path is valid for every generator of the
instance and that the path gives the instance; the loops over the indices
(`allBelow`) are pruned as soon as an order constraint fails.

`table1_macro`: the encoding of every relation of Table 1 is derivable over
`ML`, hence (`toR1`) in `R₁`.

Generated by `gen/emit_fam.py`.
-/
import QCert.ToffoliHadamard.Transport

namespace QCert.ToffoliHadamard.Macro

open Engine LiRossSelinger

/-- A generator of `𝒢₈` by its indices. -/
def toAG : Gen 8 → AG
  | .neg a => .n a
  | .x a b _ => .x a b
  | .k a b c d _ _ _ => .k a b c d

theorem encM_toAG (g : Gen 8) : encM g = (toAG g).enc := by cases g <;> rfl

theorem encMW_ofList (l : List (Gen 8)) :
    encMW (FreeMonoid.ofList l) = FreeMonoid.ofList (encL (l.map toAG)) := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    rw [FreeMonoid.ofList_cons, map_mul, ih, encMW, FreeMonoid.lift_eval_of, encM_toAG]
    simp [encL, FreeMonoid.ofList_append]

theorem encL_two (g h : AG) : encL [g, h] = g.enc ++ h.enc := by simp [encL]

theorem imp_spec' {p : Prop} [Decidable p] {b : Bool} (h : (!decide p || b) = true) (hp : p) :
    b = true := imp_spec h hp

theorem nodup_val {l : List (Fin 8)} (h : l.Nodup) : (l.map Fin.val).Nodup :=
  h.map Fin.val_injective

/-- The palindromic path of `(a b)` is valid for `g` and renames it `g'`. -/
def okPal (a b : ℕ) (g g' : AG) : Bool :=
  allAG.contains g && g.validPath (palPath a b) && g.actPath (palPath a b) == g'

theorem of_okPal {a b : ℕ} (hab : a < b) (hb : b < 8) {g g' : AG} (h : okPal a b g g' = true) :
    Derivable MRel (FreeMonoid.ofList (xabM a b ++ g.enc)) (FreeMonoid.ofList (g'.enc ++ xabM a b)) := by
  simp only [okPal, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  obtain ⟨⟨hg, hv⟩, rfl⟩ := h
  exact pal hab hb hg hv

theorem fam1a {a b : ℕ} (hab : a < b) (hb : b < 8) :
    Derivable MRel (FreeMonoid.ofList (xabM a b ++ xabM a b)) 1 := by
  have hw := pal_word hab hb
  have := pathW_cancel (palPath a b) hw.2.2
  rwa [hw.1, hw.2.1] at this

/-- A relation of `coxM ++ fig7M`, read over `AG`. -/
theorem std {L R : List AG} (h : (encL L, encL R) ∈ coxM ++ fig7M) :
    Derivable MRel (FreeMonoid.ofList (encL L)) (FreeMonoid.ofList (encL R)) :=
  Derivable.of (MRel.ax h)
""")

for f in FAMS:
    L.append(f"set_option maxRecDepth 100000 in")
    L.append(f"theorem fam{f['name']}_all : ({nested(f)}) = true := by")
    L.append("  decide +kernel")
    L.append("")

L.append("""/-- The encoding of every relation of Li–Ross–Selinger's Table 1 at `n = 8`
is derivable over `ML`. -/
theorem table1_macro {u v : Word (Gen 8)} (h : Table1 8 u v) :
    Derivable MRel (encMW u) (encMW v) := by
  cases h with
  | r1a a b hab =>
    show Derivable MRel (encMW (FreeMonoid.ofList [.x a b hab, .x a b hab]))
      (encMW (FreeMonoid.ofList []))
    rw [encMW_ofList, encMW_ofList]
    simpa [encL, toAG, AG.enc] using fam1a hab b.2""")
for f in FAMS:
    args = " ".join(f["vars"].split() + f["hyps"].split())
    L.append(f"  | {f['ctor']} {args} =>")
    L.append(f"    show Derivable MRel (encMW (FreeMonoid.ofList {f['lhs']}))")
    L.append(f"      (encMW (FreeMonoid.ofList {f['rhs']}))")
    L.append("    rw [encMW_ofList, encMW_ofList]")
    m = f["mode"]
    if m[0] == "pal":
        L.append(f"    simpa [encL_two, toAG, AG.enc] using of_okPal {m[1]} {m[2]}.2")
        L.append(f"      {extract(f)}")
    elif m[0] == "std":
        L.append(f"    exact of_ok {extract(f)} (std (by decide))")
    else:
        L.append(f"    exact std6a_valid _ (List.contains_iff_mem.1 {extract(f)})")
L.append("")
L.append("end QCert.ToffoliHadamard.Macro")
L.append("")
open(OUT, "w", encoding="utf-8", newline="\n").write("\n".join(L))
import pickle
pickle.dump(FAMS, open(work("fams.pkl"), "wb"))
print("written decisions for", len(FAMS), "families")

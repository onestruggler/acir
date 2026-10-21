"""Generate the finite relation transcription and matrix-check modules.

Amy, Ross and Wesley, arXiv:2407.11152v3, Figures 4, 7 and 8.
Run from any directory with Python 3. The generator does not prove
anything: Agda checks the resulting matrix certificates independently.
"""
from pathlib import Path
from fractions import Fraction
import json

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "Examples.Groups.CCX+HH-3qubit"
GATES = "X0 X1 X2 Z0 Z1 Z2 CX01 CX02 CX10 CX12 CX20 CX21 CZ01 CZ02 CZ12 CCX01 CCX02 CCX12 K01 K12 SWAP01 SWAP02 SWAP12 CCZ NK H2".split()
# Words are in matrix-product order: the rightmost gate acts first.
DEFS = {
    "t01": "X0 X1 CCX01 X1 X0",
    "t12": "X0 CCX01 CCX02 CCX01 X0",
    "t23": "X0 CCX01 X0",
    "t34": "X0 X2 CCX01 X0 CCX12 CCX02 CCX12 X0 CCX01 X2 X0",
    "t45": "X1 CCX01 X1", "t56": "CCX01 CCX02 CCX01", "t67": "CCX01",
    # Section 5.6 omits X2 on both sides of CCZ in its M0 alias.
    "m0": "X0 X1 X2 CCZ X2 X1 X0",
    "t04": "t01 t12 t23 t34 t23 t12 t01",
    "t13": "t12 t23 t12",
    "m1": "t01 m0 t01", "m3": "t23 t12 t01 m0 t01 t12 t23",
    "m4": "X0 m0 X0", "k4567": "X0 NK X0",
    "t24": "t23 t34 t23", "t35": "t34 t45 t34",
    "k1345": "t01 t13 t24 t35 NK t35 t24 t13 t01",
    "t02": "t01 t12 t01",
    "k2345": "t02 t13 t24 t35 NK t35 t24 t13 t02",
    "k0124": "t34 NK t34",
    "rho": "k4567 NK t34 NK k4567",
}
FIG4 = [
 ("CZ01", "K12 CX01 K12"), ("X1", "CX01 X0 CX01 X0"),
 ("Z0", "CZ01 CX01 CZ01 CX01"), ("Z1", "K12 X1 K12"),
 ("CX20", "X1 CCX12 X1 CCX12"), ("CX21", "CX20 CX01 CX20 CX01"),
 ("CX12", "K12 CX21 K12"), ("SWAP12", "CX12 CX21 CX12"),
 ("CX02", "SWAP12 CX01 SWAP12"), ("SWAP02", "CX02 CX20 CX02"),
 ("K01", "SWAP02 K12 SWAP02"), ("CX10", "K01 CX01 K01"),
 ("SWAP01", "CX01 CX10 CX01"), ("CCX02", "SWAP01 CCX12 SWAP01"),
 ("X2", "SWAP02 X0 SWAP02"), ("Z2", "SWAP02 Z0 SWAP02"),
 ("CCX01", "K12 CCX02 K12"), ("CZ02", "SWAP12 CZ01 SWAP12"),
 ("CZ12", "SWAP01 CZ02 SWAP01"), ("SWAP12", "CZ12 K12 CZ12 K12 CZ12 K12"),
 ("X0 X0", ""), ("CX01 CX01", ""), ("K12 K12", ""),
 ("CCX12 CCX12", ""), ("K01 K01", ""),
 ("CX12 X0", "X0 CX12"), ("X0 K12", "K12 X0"),
 ("X1", "SWAP01 X0 SWAP01"), ("CX20", "SWAP02 CX02 SWAP02"),
 ("CX12", "SWAP01 CX02 SWAP01"), ("CX21", "SWAP01 CX20 SWAP01"),
 ("CCX01", "SWAP02 CCX12 SWAP02"),
 # (33): the last SWAP02 is a typo; the authors' TIETZE file has SWAP12.
 ("CCX01", "SWAP12 CCX02 SWAP12"),
 ("Z1", "SWAP01 Z0 SWAP01"), ("K01", "SWAP01 K01 SWAP01"),
 ("CCX12 CX10", "CX10 CCX12"), ("X0 CCX12", "CCX12 X0"),
 ("X0 CX10", "CX10 X0"), ("K01 K12", "K12 K01"),
 ("CZ01 CZ12", "CZ12 CZ01"), ("K01 Z0", "X0 K01"),
 ("X0 CCX01", "CCX01 CX12 X0"), ("CX01 CZ12", "CZ12 CZ02 CX01"),
 ("CX12 CCX12", "CCX12 CX10 CX12"),
 ("CCX12 CX01", "CX01 CCX02 CCX12 CCX02"),
 ("CCX01 CCX02", "CCX02 CCX01 CCX02 CCX01"),
]
FIG7 = [("m0 m0", ""), ("NK NK", "")]
FIG7 += [(f"t{i}{i+1} m0", f"m0 t{i}{i+1}") for i in range(1, 7)]
FIG7 += [(f"t{i}{i+1} NK", f"NK t{i}{i+1}") for i in range(4, 7)]
FIG7 += [
 ("m4 NK", "NK m4"), ("m0 m4", "m4 m0"),
 ("NK k4567", "k4567 NK"), ("t01 NK", "NK t13 m1 m3"),
 ("t12 NK", "m0 NK m0 NK m0"), ("t23 NK", "NK t13"),
 ("NK k1345", "k2345 k0124"), ("m0 m4 t04 rho", "rho t04 m4 m0"),
]
FIG8 = [
 ("H2 X0", "X0 H2"), ("H2 CX01", "CX01 H2"),
 ("H2 CCX12", "K01 K12 CCZ K12 K01 H2"),
 ("H2 CCZ", "CCX01 H2"), ("H2 K12", "K12 H2"),
 ("H2 NK", "NK H2"), ("H2 H2", ""),
]
RELATIONS = dict(zip(list(range(1, 47)) + list(range(83, 109)), FIG4 + FIG7 + FIG8))
ERRATA = {
    "r033": ("CCX01", "SWAP12 CCX02 SWAP02"),
    "m0-alias": ("m0", "X0 X1 CCZ X1 X0"),
    "t67-alias": ("t67", "CCX12"),
    "r097": ("t01 NK", "NK t01 m1 m3"),
    "r100": ("NK k1345", "k1345 NK"),
}

def tree(w):
    xs=w.split()
    if not xs: return ()
    def atom(x): return tree(DEFS[x]) if x in DEFS else x
    if len(xs)==1: return atom(xs[0])
    return (atom(xs[0]),tree(' '.join(xs[1:])))

EVAL = {}
def collect(t):
    if t in EVAL: return EVAL[t]
    if isinstance(t,tuple) and t:
        collect(t[0]); collect(t[1])
    EVAL[t]=len(EVAL)
    return EVAL[t]

def generate_evaluation():
    for l,r in list(RELATIONS.values())+list(ERRATA.values()):
        collect(tree(l)); collect(tree(r))
    blocks=[]
    def tab(v):
        if len(v)==1: return v[0]
        k=len(v)//2
        return '('+tab(v[:k])+', '+tab(v[k:])+')'
    mats={}
    for t,i in EVAL.items():
        if isinstance(t,str):
            w=t; m=matrix(t)[1]; p=f'Eq.trans (readM-gen {t}-gen) Eq.refl'
        elif not t:
            w='ε'; m=[[int(x==y) for y in range(8)] for x in range(8)]; p='Eq.trans readM-ε Eq.refl'
        else:
            left,right=EVAL[t[0]],EVAL[t[1]]; w=f'w{left} • w{right}'
            m=mul(mats[t[0]],mats[t[1]])
            p=f'Eq.trans (readM-• w{left} w{right}) (Eq.trans (Eq.cong₂ mulM {{x = readM w{left}}} {{y = matrix{left}}} {{u = readM w{right}}} {{v = matrix{right}}} e{left} e{right}) step{i})'
        mats[t]=m
        entries=[]
        for row in m:
            for a in row:
                z=f'(+ {a})' if a>=0 else f'(-[1+ {-a-1} ])'
                entries.append(f'({z} +√2 (+ 0))')
        s=f'w{i} : Word Gen\nw{i} = {w}\n\nmatrix{i} : Mat 3\nmatrix{i} = mat {tab(entries)}\n\n'
        if isinstance(t,tuple) and t:
            s+=matrix_step(i,left,right)+'\n'
        s+=f'e{i} : readM w{i} ≡ matrix{i}\ne{i} = {p}\n\n'
        blocks.append(s)
    evaluation_chunks('Evaluation','Evaluation',matrix_imports,blocks,24)
    print('Certified evaluation subexpressions:',len(EVAL))

def eval_name(w): return 'e'+str(EVAL[tree(w)])

def expand(w):
    return [g for x in w.split() for g in (expand(DEFS[x]) if x in DEFS else [x])]

def word(w):
    xs = w.split()
    return " • ".join(xs) if xs else "ε"

def header(mod):
    return f"{{-# OPTIONS --without-K --safe #-}}\n\nmodule {PREFIX}.{mod} where\n\n"

# Matrix evaluations, written in chunks of `size` blocks: <chunks>.E00 …,
# and <whole> re-exporting them all.  Agda's operator parser takes time in
# proportion to the names in scope for every parenthesised subterm, and a
# matrix literal has some 250 of them, so a chunk imports from the earlier
# chunks only the names it uses, and imports(body) its libraries the same
# way.  (Evaluation was one module of a thousand names, 27 of its 50 s
# spent parsing; FrameEvaluation's chunks re-exported each other publicly,
# the last with three thousand names in scope.)
def evaluation_chunks(chunks, whole, imports, blocks, size):
    import re
    folder = ROOT.joinpath(*chunks.split("."))
    folder.mkdir(parents=True, exist_ok=True)
    defined = []
    parts = [blocks[o:o + size] for o in range(0, len(blocks), size)]
    for k, part in enumerate(parts):
        body = "".join(part)
        own = set(re.findall(r"^(\S+) : ", body, re.M))
        used = set(re.findall(r"\b(?:w|matrix|e)[0-9]+\b", body)) - own
        s = header(f"{chunks}.E{k:02d}") + imports(body)
        for j in range(k):
            names = sorted(used & defined[j], key=lambda x: (re.sub(r"[0-9]+", "", x), int(re.sub(r"[^0-9]", "", x))))
            if names:
                s += f"open import {PREFIX}.{chunks}.E{j:02d} using ({' ; '.join(names)})\n"
        (folder / f"E{k:02d}.agda").write_text(s + "\n" + body, encoding="utf-8")
        defined.append(own)
    s = header(whole) + "".join(f"open import {PREFIX}.{chunks}.E{k:02d} public\n" for k in range(len(parts)))
    ROOT.joinpath(*whole.split(".")).with_suffix(".agda").write_text(s, encoding="utf-8")

# The imports of an evaluation chunk over ℤ[√2], each a `using` list; a
# product is decided by one boolean on the sparse product (Real-Clifford+CH's
# eqM, mulS), not by Eq.refl between stored matrices.
def matrix_imports(body):
    import re
    toks = set(re.findall(r"[^\s(){}]+", body))
    gates = [x for x in GATES if x in toks] + [x + "-gen" for x in GATES if x + "-gen" in toks]
    return (f"open import Data.Integer.Base using (+_ ; -[1+_])\n"
            f"open import Data.Product.Base using (_,_ )\n"
            f"open import Relation.Binary.PropositionalEquality as Eq using (_≡_)\n"
            f"open import {PREFIX}.Syntactics using ({' ; '.join(['Word', 'Gen', '_•_', 'ε'] + gates)})\n"
            f"open import {PREFIX}.GateMatrices using (Mat ; mat ; mulM ; _+√2_)\n"
            f"open import {PREFIX}.Interpretation using (readM ; readM-gen ; readM-ε ; readM-•)\n"
            f"open import Examples.Groups.Real-Clifford+CH.Semantics.Decide using (eqM-sound)\n"
            f"open import Examples.Groups.Real-Clifford+CH.Semantics.Sparse using (mulS ; mulS-ok)\n")

def matrix_step(i, a, b):
    return (f"step{i} : mulM matrix{a} matrix{b} ≡ matrix{i}\n"
            f"step{i} = Eq.trans (Eq.sym (mulS-ok matrix{a} matrix{b})) (eqM-sound (mulS matrix{a} matrix{b}) matrix{i} Eq.refl)\n")

# A certificate's imports, as one restricted import of Kit.  An interface records the whole scope
# of every module its module imports, so a certificate that opened
# Syntactics, Frames, FrameWords and Engine took 50-65 kB on disk for one
# line of proof; importing the kit with the names it uses (`import Kit as
# K using (…)`, then `open K`) takes about 9 kB.  Kit.agda lists what
# it exports; kit() leaves other modules alone, and those that use the
# frames (FrameKit, which they imported, went with the frame moves).
KIT_LINES = [
    "import Relation.Binary.PropositionalEquality as Eq",
    f"open import {PREFIX}.Syntactics",
    f"open import {PREFIX}.Frames",
    f"open import {PREFIX}.FrameWords",
    f"open import {PREFIX}.Engine",
    "open import Data.Fin.Base using (zero ; suc)",
    "import Presentation.GroupLike as GLib",
    f"open import {PREFIX}.GroupLike using (grouplike)",
    "module GL = GLib.Group-Lemmas _===_ grouplike",
]
FRAME_LINES = KIT_LINES[2:4] + KIT_LINES[6:]
_kit_names = {}

def kit_names(mod):
    if mod not in _kit_names:
        import re
        names = set()
        for m in re.finditer(r"^open import \S+ public\s+using \(([^)]*)\)",
                             (ROOT / f"{mod}.agda").read_text(encoding="utf-8"), re.M):
            names.update(x.strip() for x in m.group(1).split(";"))
        names.discard("")
        _kit_names[mod] = names
    return _kit_names[mod]

def kit(s):
    import re
    lines = s.split("\n")
    if not (f"open import {PREFIX}.Syntactics" in lines and f"open import {PREFIX}.Engine" in lines):
        return s
    if any(l in FRAME_LINES for l in lines):
        return s
    mod = "Kit"
    first = min(i for i, l in enumerate(lines) if l in KIT_LINES)
    rest = [l for l in lines if l not in KIT_LINES]
    body = [l for l in rest if not l.startswith(("{-#", "module ", "import ", "open import "))]
    local = {m.group(1) for l in body for m in [re.match(r"(\S+) [:=] ", l)] if m}
    names, mods = set(), set()
    for t in re.findall(r"[^\s(){};]+", "\n".join(body)):
        if t.startswith("Eq."): mods.add("Eq")
        elif t.startswith("GL."): mods.add("GL")
        elif "." in t: continue
        else:
            t = {"•": "_•_", "≈": "_≈_"}.get(t, t)
            if t in kit_names(mod) and t not in local: names.add(t)
    using = sorted(names) + ["module " + m for m in sorted(mods)]
    head = [f"import {PREFIX}.{mod} as K using ({' ; '.join(using)})", "open K"]
    out = "\n".join(rest[:first] + head + rest[first:])
    return re.sub(r"\n\n\n+", "\n\n", out)

def generate_syntax():
    s = "-- Figures 4, 7 and 8 of arXiv:2407.11152v3. See README.md for corrections.\n"
    s += header("Syntactics")
    s += "open import Word.Base public\nimport Presentation.Base as PB\n\ndata Gen : Set where\n"
    s += "  " + " ".join(g + "-gen" for g in GATES) + " : Gen\n\n"
    s += " ".join(GATES) + " : Word Gen\n"
    s += "\n".join(f"{g} = [ {g}-gen ]ʷ" for g in GATES) + "\n\n"
    for k, v in DEFS.items():
        s += f"{k} : Word Gen\n{k} = {word(v)}\n\n"
    s += "-- Other one-wire Hadamards are words over Σ₂.\nH0 H1 : Word Gen\nH0 = K01 • K12 • H2\nH1 = K12 • H2\n\n"
    s += "infix 4 _===_\n\ndata _===_ : WRel Gen where\n"
    for n, (l, r) in RELATIONS.items():
        s += f"  r{n:03d} : {word(l)} === {word(r)}\n"
    s += "\nopen PB _===_ public using (_≈_)\n"
    (ROOT / "Syntactics.agda").write_text(s, encoding="utf-8")

def matrix(g):
    m = [[0 for _ in range(8)] for _ in range(8)]
    d = 2 if g in ("K01", "K12", "NK") else 1 if g == "H2" else 0
    for y in range(8):
        bs = [(y >> (2-i)) & 1 for i in range(3)]
        if g.startswith("X") or g.startswith("CX") or g.startswith("CCX") or g.startswith("SWAP"):
            out = bs[:]
            if g.startswith("SWAP"):
                a,b = map(int,g[-2:]); out[a],out[b] = out[b],out[a]
            elif g.startswith("CCX"):
                a,b = map(int,g[-2:]); t = 3-a-b; out[t] ^= bs[a] & bs[b]
            elif g.startswith("CX"):
                a,b = map(int,g[-2:]); out[b] ^= bs[a]
            else: out[int(g[-1])] ^= 1
            x = sum(b << (2-i) for i,b in enumerate(out)); m[x][y] = 1
        elif g.startswith("Z") or g.startswith("CZ") or g == "CCZ":
            support = [int(g[-1])] if g.startswith("Z") else list(map(int,g[-2:])) if g.startswith("CZ") else [0,1,2]
            m[y][y] = -1 if all(bs[i] for i in support) else 1
        else:
            if g == "NK" and bs[0]: m[y][y] = 2; continue
            support = [2] if g == "H2" else [0,1] if g == "K01" else [1,2]
            for x in range(8):
                xs = [(x >> (2-i)) & 1 for i in range(3)]
                if all(xs[i] == bs[i] for i in range(3) if i not in support):
                    m[x][y] = (-1)**sum(xs[i]*bs[i] for i in support)
    return d,m

def mul(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(8)) for j in range(8)] for i in range(8)]

def reading(w):
    d = 0; m = [[int(i==j) for j in range(8)] for i in range(8)]
    for g in expand(w):
        e, a = matrix(g); d += e; m = mul(m, a)
    return d,m

def equal(l,r):
    dl,ml = reading(l); dr,mr = reading(r)
    if (dl-dr)%2: return False
    return all(Fraction(ml[i][j],2**(dl//2)) == Fraction(mr[i][j],2**(dr//2)) for i in range(8) for j in range(8))

def generate_matrices():
    s = header("GateMatrices")
    s += "open import Data.Bool.Base using (true ; false)\nopen import Data.Integer.Base as ℤ using (+_ ; -[1+_])\nopen import Data.Nat.Base using (ℕ)\nopen import Data.Vec.Base using ([] ; _∷_)\nopen import Examples.Groups.Real-Clifford+CH.Semantics.Algebra public\nopen import " + PREFIX + ".Syntactics using (Gen ; " + " ; ".join(g+"-gen" for g in GATES) + ")\n\n"
    s += "degree : Gen → ℕ\n"
    for g in GATES: s += f"degree {g}-gen = {matrix(g)[0]}\n"
    s += "\nindex : Bits 3 → ℕ\n"
    for i in range(8):
        bs = " ∷ ".join("true" if i & (1<<(2-j)) else "false" for j in range(3)) + " ∷ []"
        s += f"index ({bs}) = {i}\n"
    s += "\nentry : Gen → ℕ → ℕ → 𝔽\n"
    for g in GATES:
        for i,row in enumerate(matrix(g)[1]):
            for j,a in enumerate(row):
                if a:
                    val = f"(+ {a})" if a>0 else f"(-[1+ {-a-1} ])"
                    s += f"entry {g}-gen {i} {j} = {val} +√2 (+ 0)\n"
    s += "entry _ _ _ = 0#\n\ngateOp : Gen → Op 3\ngateOp g x y = entry g (index x) (index y)\n\ngateM : Gen → Mat 3\ngateM g = matOf (gateOp g)\n"
    (ROOT / "GateMatrices.agda").write_text(s,encoding="utf-8")

def generate_checks():
    (ROOT / "Checks").mkdir(exist_ok=True)
    for n,(l,r) in RELATIONS.items():
        s = header(f"Checks.R{n:03d}")
        s += f"open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)\nopen import {PREFIX}.Syntactics\nopen import {PREFIX}.Interpretation\nopen import {PREFIX}.GateMatrices using (√2^_)\nopen import {PREFIX}.Semantics using (scaleM)\nopen import {PREFIX}.Evaluation using ({eval_name(l)} ; {eval_name(r)})\n\n"
        s += f"checked : scaledM ({word(l)}) ({word(r)}) ≡ scaledM ({word(r)}) ({word(l)})\nchecked = Eq.trans (Eq.cong (scaleM (√2^ len ({word(r)}))) {eval_name(l)})\n  (Eq.trans refl (Eq.sym (Eq.cong (scaleM (√2^ len ({word(l)}))) {eval_name(r)})))\n"
        (ROOT / "Checks" / f"R{n:03d}.agda").write_text(s,encoding="utf-8")
    s = header("Soundness")
    s += f"open import {PREFIX}.Syntactics\nopen import {PREFIX}.Interpretation\n"
    for n in RELATIONS: s += f"import {PREFIX}.Checks.R{n:03d} as R{n:03d}\n"
    s += "\naxiom-sound : ∀ {w v} → w === v → ⟦ w ⟧ ~ ⟦ v ⟧\n"
    for n in RELATIONS: s += f"axiom-sound r{n:03d} = by-matrix R{n:03d}.checked\n"
    s += "\nsound : ∀ {w v} → w ≈ v → ⟦ w ⟧ ~ ⟦ v ⟧\nsound = sound-from axiom-sound\n"
    (ROOT / "Soundness.agda").write_text(s,encoding="utf-8")

def generate_errata():
    cases = ERRATA
    s = header("Errata")
    s += f"open import Data.Empty using (⊥)\nopen import Data.Integer.Base using (+_ ; -[1+_])\nopen import Data.Bool.Base using (true ; false)\nopen import Data.Vec.Base using ([] ; _∷_)\nopen import Relation.Binary.PropositionalEquality as Eq using (_≢_)\nopen import {PREFIX}.Syntactics\nopen import {PREFIX}.GateMatrices\nopen import {PREFIX}.Interpretation\nopen import {PREFIX}.Evaluation\n\n"
    def bits(i):
        return "("+" ∷ ".join("true" if i & (1<<(2-j)) else "false" for j in range(3))+" ∷ [])"
    def number(a):
        z=f"(+ {a})" if a>=0 else f"(-[1+ {-a-1} ])"
        return f"({z} +√2 (+ 0))"
    for name,(l,r) in cases.items():
        dl,ml=reading(l); dr,mr=reading(r)
        assert dl%2==dr%2==0
        i,j=next((i,j) for i in range(8) for j in range(8) if ml[i][j]*2**(dr//2)!=mr[i][j]*2**(dl//2))
        a,b=ml[i][j]*2**(dr//2), mr[i][j]*2**(dl//2)
        x,y=bits(i),bits(j)
        s += f"-- Witness: matrix entry ({i}, {j}).\n{name}-false : ⟦ {word(l)} ⟧ ~ ⟦ {word(r)} ⟧ → ⊥\n{name}-false eq = bad (Eq.trans\n  (Eq.sym (Eq.cong (λ M → √2^ len ({word(r)}) * ix M {x} {y}) {eval_name(l)}))\n  (Eq.trans (eq {x} {y})\n    (Eq.cong (λ M → √2^ len ({word(l)}) * ix M {x} {y}) {eval_name(r)})))\n  where\n  bad : {number(a)} ≢ {number(b)}\n  bad ()\n\n"
    (ROOT / "Errata.agda").write_text(s,encoding="utf-8")

def generate_core():
    base = ['X0','CX01','CCX12','K12','CCZ','NK','H2']
    s = header('Core')
    s += f"open import Relation.Binary.PropositionalEquality as Eq using (_≡_)\nopen import {PREFIX}.Syntactics\nopen import Presentation.Base _===_ hiding (_===_ ; _≈_)\n\n"
    s += 'data CGen : Set where\n  ' + ' '.join('c'+g for g in base) + ' : CGen\n\n'
    s += 'embed : CGen → Gen\n' + '\n'.join(f'embed c{g} = {g}-gen' for g in base) + '\n\n'
    s += '⌞_⌟ : Word CGen → Word Gen\n⌞ w ⌟ = wmap embed w\n\n'
    for g in base:
        s += f'w{g} : Word CGen\nw{g} = [ c{g} ]ʷ\ne{g} : {g} ≈ ⌞ w{g} ⌟\ne{g} = refl\n\n'
    def proof(gs):
        if len(gs)==1: return 'e'+gs[0]
        return f'(cong e{gs[0]} {proof(gs[1:])})'
    # Each right side uses only preceding generators (the paper's DAG).
    for n,(g,w) in enumerate(FIG4[:19],1):
        s += f'w{g} : Word CGen\nw{g} = '+ ' • '.join('w'+x for x in w.split())+'\n'
        s += f'e{g} : {g} ≈ ⌞ w{g} ⌟\ne{g} = trans (axiom r{n:03d}) {proof(w.split())}\n\n'
    s += 'core : Gen → Word CGen\n'+ '\n'.join(f'core {g}-gen = w{g}' for g in GATES)+'\n\n'
    s += 'expand : Word Gen → Word CGen\nexpand = core ʷ\n\n'
    s += 'gen-expand : (g : Gen) → [ g ]ʷ ≈ ⌞ core g ⌟\n'+ '\n'.join(f'gen-expand {g}-gen = e{g}' for g in GATES)+'\n\n'
    s += 'word-expand : (w : Word Gen) → w ≈ ⌞ expand w ⌟\nword-expand [ g ]ʷ = gen-expand g\nword-expand ε = refl\nword-expand (w • v) = cong (word-expand w) (word-expand v)\n'
    (ROOT / 'Core.agda').write_text(s,encoding='utf-8')

def generate_group_like():
    s=header('GroupLike')
    s+=f'open import Data.Product.Base using (_,_ )\nopen import Relation.Binary.PropositionalEquality as Eq\nopen import Presentation.GroupLike using (Grouplike)\nopen import {PREFIX}.Syntactics\nopen import {PREFIX}.Invertible\nopen import Presentation.Base _===_ hiding (_===_ ; _≈_)\nopen import Presentation.Properties _===_ using (by-assoc)\n\n'
    for g,n in [('X0',21),('CX01',22),('K12',23),('CCX12',24),('NK',84),('H2',108)]:
        s+=f'i{g} : Invertible {g}\ni{g} = invol (axiom r{n:03d})\n\n'
    def products(gs):
        if len(gs)==1: return 'i'+gs[0]
        return f'(product i{gs[0]} {products(gs[1:])})'
    for n,(g,w) in enumerate(FIG4[:19],1):
        s+=f'i{g} : Invertible {g}\ni{g} = along (axiom r{n:03d}) {products(w.split())}\n\n'
    s+='iCCZ : Invertible CCZ\niCCZ = middle\n  (product iX0 (product iX1 iX2))\n  (product iX2 (product iX1 iX0))\n  (along (by-assoc Eq.refl) (invol (axiom r083)))\n\n'
    s+='invertible-gen : (g : Gen) → Invertible [ g ]ʷ\n'+'\n'.join(f'invertible-gen {g}-gen = i{g}' for g in GATES)+'\n\n'
    s+='grouplike : Grouplike _===_\ngrouplike g = Invertible.inverse (invertible-gen g) , Invertible.left (invertible-gen g)\n'
    (ROOT/'GroupLike.agda').write_text(s,encoding='utf-8')

if __name__ == "__main__":
    failures = [n for n,(l,r) in RELATIONS.items() if not equal(l,r)]
    print("Exact rational precheck: failing equations", failures)
    assert not failures
    generate_syntax(); generate_matrices(); generate_evaluation(); generate_checks(); generate_errata(); generate_core(); generate_group_like()
    (ROOT / "tools" / "relations.json").write_text(json.dumps(RELATIONS,indent=2)+"\n")

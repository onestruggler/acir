#!/usr/bin/env python3
"""Shorten the two-wire Clément presentations with certified local rewrites.

Each replacement rewrites a relator using other current relators, then
removes its conjugating prefix and chooses a cyclic representative.  The
generated Agda proof records every local rewrite and proves both directions
of every replacement.  This is a reduction of the existing presentations,
not a new semantic presentation or a claim of minimality.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path
import re

from build_reduced_relations import classify
from exact_matrices import evaluate, identity

HERE = Path(__file__).resolve().parent


def key(word):
    return len(word), word


def rules_for(active, words, excluded):
    rules = {}
    for _, version in sorted(active.items()):
        if version == excluded:
            continue
        word = words[version]
        for backwards in (False, True):
            oriented = word[::-1] if backwards else word
            for turns in range(len(oriented)):
                rotated = oriented[turns:] + oriented[:turns]
                for cut in range((len(rotated) + 1) // 2, len(rotated) + 1):
                    left, right = rotated[:cut], rotated[cut:][::-1]
                    if key(left) > key(right):
                        rules.setdefault(left, (right, version, backwards, turns))
    result = defaultdict(list)
    for left, data in rules.items():
        result[left[0]].append((left, data))
    for bucket in result.values():
        bucket.sort(key=lambda item: key(item[0]), reverse=True)
    return result


def normalize(word, rules):
    steps = []
    while True:
        found = False
        for position, letter in enumerate(word):
            for left, (right, version, backwards, turns) in rules[letter]:
                if word[position:position + len(left)] == left:
                    prefix, suffix = word[:position], word[position + len(left):]
                    steps.append({"dependency": version, "reversed": backwards,
                                  "rotations": turns, "prefix": prefix, "suffix": suffix,
                                  "left": left, "right": right})
                    new = prefix + right + suffix
                    assert key(new) < key(word)
                    word, found = new, True
                    break
            if found:
                break
        if not found:
            return word, steps


def shorten(data, cyclic_start=False):
    original = [tuple(r["left"]) + tuple(r["right"])[::-1] for r in data["relations"]]
    words = original[:]
    active = dict(enumerate(range(len(words))))
    changes = []
    while True:
        changed = False
        for index in sorted(active, key=lambda i: key(words[active[i]]), reverse=True):
            old = active[index]
            if len(words[old]) <= 2:
                continue
            rules = rules_for(active, words, old)
            normal, steps = normalize(words[old], rules)
            cls = classify({"left": list(normal), "right": []})
            start_turns, start_backwards = 0, False
            if cyclic_start:
                for backwards in (False, True):
                    oriented = words[old][::-1] if backwards else words[old]
                    for turns in range(len(oriented)):
                        alternative, path = normalize(oriented[turns:] + oriented[:turns], rules)
                        alternative_cls = classify({"left": list(alternative), "right": []})
                        if key(alternative_cls[0]) < key(cls[0]):
                            normal, steps, cls = alternative, path, alternative_cls
                            start_turns, start_backwards = turns, backwards
            chosen = cls[0]
            if key(chosen) < key(words[old]):
                new = len(words)
                words.append(chosen)
                changes.append({"old": old, "new": new, "normal": normal,
                                "steps": steps, "classification": cls})
                if cyclic_start:
                    changes[-1]["start_rotations"] = start_turns
                    changes[-1]["start_reversed"] = start_backwards
                if chosen:
                    active[index] = new
                else:
                    del active[index]
                changed = True
        if not changed:
            break
    return original, words, active, changes


def generate(gate_set, cyclic_start=False):
    root = HERE.parent.parent / ("CCX+" + gate_set)
    data = json.loads((root / "two_qubit_reduced.json").read_text(encoding="utf-8"))
    original, words, active, changes = shorten(data, cyclic_start)
    entrypoint = "CyclicPresentation" if cyclic_start else "ShortPresentation"
    proof_directory = "Cyclic" if cyclic_start else "Short"
    json_name = "two_qubit_cyclic.json" if cyclic_start else "two_qubit_short.json"
    count = len(data["circuit_generators"])
    tags = (["X-gen", "(X-gen ↥)", "CX-gen", "HH-gen"] if gate_set == "HH" else
            ["X-gen", "(X-gen ↥)", "CX-gen", "H-gen", "(H-gen ↥)"])
    final = [version for _, version in sorted(active.items()) if len(words[version]) > 2]
    final_ids = {version: i for i, version in enumerate(final)}

    def alist(word):
        return " ∷ ".join([tags[g] for g in word] + ["[]"])

    def cert(cls):
        _, prefix, turns, backwards = cls
        return f"(R.certificate ({alist(prefix)}) {turns} {'true' if backwards else 'false'} Eq.refl)"

    source = f"""------------------------------------------------------------------------
-- Presentations of groups
--
-- A {len(active)}-equation two-wire theory obtained by shortening the Clément
-- translation.  Every local rewrite and every relator replacement is
-- proved in both directions; the source completeness theorem transfers.
-- Generated by CCX+HH/scripts/build_short_relations.py --gate-set {gate_set}{' --cyclic-start' if cyclic_start else ''}.
------------------------------------------------------------------------

{{-# OPTIONS --without-K --safe #-}}

module Examples.Groups.CCX+{gate_set}.TwoQubit.{entrypoint} where

open import Data.Bool.Base using (false ; true)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (WRel ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.GroupLike as GL
import Presentation.Tactic.AssociativitySolver as Assoc
open import Examples.Groups.CCX+{gate_set}.Syntactics
import Examples.Groups.CCX+{gate_set}.TwoQubit.ReducedPresentation as Old
import Examples.Groups.CCX+HH.RelatorRewriting as Rewriting
"""
    if gate_set == "HH":
        source += "import Examples.Groups.CCX+HH.Semantics as Physical\n"
    else:
        source += """import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as Physical
open Old using (X-gen ; H-gen ; CX-gen)
"""
    source += "\nmodule R = Old.R\n\n"
    for i, word in enumerate(words):
        source += f"w{i:03d} : List (Gen 2)\nw{i:03d} = {alist(word)}\n"
    source += "\ndata Index : Set where\n  "
    source += " ".join(f"r{i:02d}" for i in range(len(final))) + " : Index\n"
    source += "\nselected : Index → List (Gen 2)\n"
    for i, version in enumerate(final):
        source += f"selected r{i:02d} = w{version:03d}\n"
    source += """
data Relations : WRel (Gen 2) where
  square : ∀ g → Relations ([ g ]ʷ • [ g ]ʷ) ε
  relator : ∀ i → Relations (R.read (selected i)) ε

open PB Relations public hiding (_===_)

grouplike : GL.Grouplike Relations
grouplike g = [ g ]ʷ , axiom (square g)

private
  module Rewrite (Γ : WRel (Gen 2))
    (involution : ∀ g → PB._≈_ Γ ([ g ]ʷ • [ g ]ʷ) ε) where
    open PB Γ using () renaming (_≈_ to _~_)
    module Calc = R.Theory Γ involution
    open Rewriting Γ using (context)
    open Assoc.Assoc Γ using (by-assoc-and)
"""
    # Each local derivation is parameterized by the facts it uses.  Thus the
    # same checked derivation is used in the forward and backward theories.
    for i, change in enumerate(changes):
        deps = sorted({step["dependency"] for step in change["steps"]})
        change["dependencies"] = deps
        source += f"\n    step{i:03d} : "
        for dep in deps:
            source += f"(p{dep:03d} : R.read w{dep:03d} ~ ε) →\n      "
        if cyclic_start:
            start = (f"(R.rotate {change['start_rotations']} "
                     f"(R.orient {'true' if change['start_reversed'] else 'false'} w{change['old']:03d}))")
        else:
            start = f"w{change['old']:03d}"
        source += f"R.read {start} ~ R.read ({alist(change['normal'])})\n"
        source += f"    step{i:03d}" + "".join(f" p{dep:03d}" for dep in deps) + " =\n"
        proofs = []
        for step in change["steps"]:
            dep = step["dependency"]
            if len(words[dep]) == 2:
                lemma = f"(by-assoc-and (involution {tags[words[dep][0]]}) Eq.refl Eq.refl)"
            else:
                proof_cls = (words[dep], (), step["rotations"], step["reversed"])
                lemma = (f"(Calc.derive-equation {{u = R.read ({alist(step['left'])})}} "
                         f"{{v = R.read ({alist(step['right'])})}} {{selected = w{dep:03d}}} "
                         f"{cert(proof_cls)} p{dep:03d})")
            proofs.append(f"context ({alist(step['prefix'])}) ({alist(step['suffix'])}) "
                          f"{{u = {alist(step['left'])}}} {{v = {alist(step['right'])}}} {lemma}")
        body = "PB.refl"
        for proof in reversed(proofs):
            body = f"PB.trans ({proof})\n      ({body})"
        source += "      " + body + "\n"
    source += """
  module Backward where
    module Steps = Rewrite Relations (λ g → axiom (square g))
    module Calc = R.Theory Relations (λ g → axiom (square g))
    open Assoc.Assoc Relations using (by-assoc-and)
"""
    for version in sorted(set(active.values()) | {c["new"] for c in changes if not words[c["new"]]}):
        source += f"\n    fact{version:03d} : R.read w{version:03d} ≈ ε\n"
        if not words[version]:
            proof = "refl"
        elif len(words[version]) == 2:
            proof = f"by-assoc-and (axiom (square {tags[words[version][0]]})) Eq.refl Eq.refl"
        else:
            proof = f"axiom (relator r{final_ids[version]:02d})"
        source += f"    fact{version:03d} = {proof}\n"
    for i in reversed(range(len(changes))):
        change = changes[i]
        old, new = change["old"], change["new"]
        step = f"Steps.step{i:03d}" + "".join(f" fact{dep:03d}" for dep in change["dependencies"])
        source += f"\n    fact{old:03d} : R.read w{old:03d} ≈ ε\n"
        if cyclic_start:
            backwards = 'true' if change['start_reversed'] else 'false'
            source += f"    fact{old:03d} = Calc.orient-reflect {backwards} w{old:03d}\n"
            source += f"      (Calc.rotate-reflect {change['start_rotations']} (R.orient {backwards} w{old:03d})\n"
            source += f"        (trans ({step})\n"
            source += f"          (Calc.derive-relator {{selected = w{new:03d}}} {cert(change['classification'])} fact{new:03d})))\n"
        else:
            source += f"    fact{old:03d} = trans ({step})\n"
            source += f"      (Calc.derive-relator {{selected = w{new:03d}}} {cert(change['classification'])} fact{new:03d})\n"
    source += """
  module Forward where
    open PB Old.Relations using () renaming (_≈_ to _~_)
    module Steps = Rewrite Old.Relations (λ g → PB.axiom (Old.square g))
    module Calc = R.Theory Old.Relations (λ g → PB.axiom (Old.square g))
    open Assoc.Assoc Old.Relations using (by-assoc-and)
"""
    for version in range(len(original)):
        source += f"\n    fact{version:03d} : R.read w{version:03d} ~ ε\n"
        if version < count:
            proof = f"by-assoc-and (PB.axiom (Old.square {tags[version]})) Eq.refl Eq.refl"
        else:
            proof = f"PB.axiom (Old.relator Old.r{version - count:02d})"
        source += f"    fact{version:03d} = {proof}\n"
    for i, change in enumerate(changes):
        old, new = change["old"], change["new"]
        step = f"Steps.step{i:03d}" + "".join(f" fact{dep:03d}" for dep in change["dependencies"])
        source += f"\n    fact{new:03d} : R.read w{new:03d} ~ ε\n"
        source += f"    fact{new:03d} = Calc.recover-selected {{selected = w{new:03d}}} {cert(change['classification'])}\n"
        if cyclic_start:
            backwards = 'true' if change['start_reversed'] else 'false'
            fact = (f"(Calc.rotate-trivial {change['start_rotations']} (R.orient {backwards} w{old:03d}) "
                    f"(Calc.orient-trivial {backwards} w{old:03d} fact{old:03d}))")
        else:
            fact = f"fact{old:03d}"
        source += f"      (PB.trans (PB.sym ({step})) {fact})\n"
    source += """
  from-axiom : ∀ {u v} → Old.Relations u v → u ≈ v
  from-axiom (Old.square g) = axiom (square g)
"""
    for i in range(len(original) - count):
        source += f"  from-axiom (Old.relator Old.r{i:02d}) = Backward.fact{i + count:03d}\n"
    source += """
  to-axiom : ∀ {u v} → Relations u v → u Old.≈ v
  to-axiom (square g) = PB.axiom (Old.square g)
"""
    for i, version in enumerate(final):
        source += f"  to-axiom (relator r{i:02d}) = Forward.fact{version:03d}\n"
    source += """
from-reduced : ∀ {u v} → u Old.≈ v → u ≈ v
from-reduced PB.refl = refl
from-reduced (PB.sym p) = sym (from-reduced p)
from-reduced (PB.trans p q) = trans (from-reduced p) (from-reduced q)
from-reduced (PB.cong p q) = cong (from-reduced p) (from-reduced q)
from-reduced PB.assoc = assoc
from-reduced PB.left-unit = left-unit
from-reduced PB.right-unit = right-unit
from-reduced (PB.axiom ax) = from-axiom ax

to-reduced : ∀ {u v} → u ≈ v → u Old.≈ v
to-reduced refl = PB.refl
to-reduced (sym p) = PB.sym (to-reduced p)
to-reduced (trans p q) = PB.trans (to-reduced p) (to-reduced q)
to-reduced (cong p q) = PB.cong (to-reduced p) (to-reduced q)
to-reduced assoc = PB.assoc
to-reduced left-unit = PB.left-unit
to-reduced right-unit = PB.right-unit
to-reduced (axiom ax) = to-axiom ax

sound : ∀ {u v} → u ≈ v → Physical.interpret u ≡ Physical.interpret v
sound p = Old.sound (to-reduced p)

complete : ∀ {u v : Circuit 2} → Physical.interpret u ≡ Physical.interpret v → u ≈ v
complete p = from-reduced (Old.complete p)
"""
    output = {
        "format": "clement-short-relator-presentation-v1",
        "wires": 2, "gate_set": gate_set, "word_order": "matrix product order",
        "circuit_generators": data["circuit_generators"],
        "source": "two_qubit_reduced.json", "source_relation_count": len(original),
        "formal_entrypoint": f"TwoQubit/{entrypoint}.agda",
        "relations": ([{"kind": "involution", "left": [i, i], "right": []} for i in range(count)] +
                      [{"kind": "relator", "left": list(words[v]), "right": [], "version": v} for v in final]),
        "relator_versions": [list(word) for word in words],
        "replacements": [{k: v for k, v in change.items() if k != "classification"} | {
            "cyclic_certificate": {"prefix": change["classification"][1],
                                   "rotations": change["classification"][2],
                                   "reversed": change["classification"][3]}}
                         for change in changes],
    }
    gates = [(g["gate"], tuple(g["wires"])) for g in data["circuit_generators"]]
    for relation in output["relations"]:
        if evaluate(tuple(relation["left"]), gates, 2) != identity(2):
            raise ValueError("a shortened equation failed exact physical matrix verification")
    # Separate the finite rewrites so Agda releases their evaluation state
    # between modules.  The theorem bodies are opaque to the final assembly.
    module_name = f"Examples.Groups.CCX+{gate_set}.TwoQubit"
    before_private, after_private = source.split("\nprivate\n  module Rewrite", 1)
    rewrite_text, remainder = after_private.split("\n  module Backward where", 1)
    imports = before_private.split("\nmodule R = Old.R", 1)[0]
    data_source = before_private.replace(module_name + "." + entrypoint, module_name + "." + proof_directory + ".Data")
    sources = {root / "TwoQubit" / proof_directory / "Data.agda": data_source}
    step_texts = re.split(r"(?=\n    step[0-9]{3} :)", rewrite_text)[1:]
    openings = []
    batch_imports = []
    for batch, start in enumerate(range(0, len(step_texts), 8)):
        name = f"Batch{batch:02d}"
        header = imports.replace(module_name + "." + entrypoint, module_name + "." + proof_directory + "." + name)
        header += f"\nopen import {module_name}.{proof_directory}.Data\n\n"
        header += """module Prove (Γ : WRel (Gen 2))
  (involution : ∀ g → PB._≈_ Γ ([ g ]ʷ • [ g ]ʷ) ε) where
  open PB Γ using () renaming (_≈_ to _~_)
  module Calc = R.Theory Γ involution
  open Rewriting Γ using (context)
  open Assoc.Assoc Γ using (by-assoc-and)

  abstract
"""
        sources[root / "TwoQubit" / proof_directory / (name + ".agda")] = header + "".join(step_texts[start:start + 8])
        batch_imports.append(f"import {module_name}.{proof_directory}.{name} as {name}\n")
        exported = " ; ".join(f"step{i:03d}" for i in range(start, min(start + 8, len(step_texts))))
        openings.append(f"    open {name}.Prove Γ involution public using ({exported})\n")
    source = imports + f"\nopen import {module_name}.{proof_directory}.Data public\n"
    source += "".join(batch_imports)
    source += """
private
  module Rewrite (Γ : WRel (Gen 2))
    (involution : ∀ g → PB._≈_ Γ ([ g ]ʷ • [ g ]ʷ) ε) where
""" + "".join(openings)
    source += "\n  module Backward where" + remainder
    sources[root / "TwoQubit" / (entrypoint + ".agda")] = source
    sources[root / json_name] = json.dumps(output, indent=2) + "\n"
    return sources, {
        "gate_set": gate_set, "relations": len(active), "replacements": len(changes),
        "local_rewrites": sum(len(c["steps"]) for c in changes),
        "longest_relator": max(map(len, (words[v] for v in active.values()))),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gate-set", choices=("HH", "H", "both"), default="both")
    parser.add_argument("--cyclic-start", action="store_true",
                        help="Try cyclic rotations and reversals before shortening; write separate CyclicPresentation files")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for gate_set in ("HH", "H") if args.gate_set == "both" else (args.gate_set,):
        sources, stats = generate(gate_set, args.cyclic_start)
        for path, content in sources.items():
            if args.check:
                if not path.is_file() or path.read_text(encoding="utf-8") != content:
                    raise SystemExit(f"Generated file differs: {path}")
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content, encoding="utf-8")
        print(json.dumps(stats))
    print("Reproduction and exact matrix checks passed; generated Agda requires typechecking.")


if __name__ == "__main__":
    main()

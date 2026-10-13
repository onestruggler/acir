{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TwoLevel where

open import Word.Base using (Word ; _ʷ)
open import Examples.Groups.CCX+HH-3qubit.Syntactics using (Gen ; _≈_)
open import Examples.Groups.CCX+HH-3qubit.FrameWords using (decode)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as TL
import Presentation.Properties as PP
import Presentation.Base as PB
import Examples.Groups.CCX+HH-3qubit.Transport.r1a as Tr1a
import Examples.Groups.CCX+HH-3qubit.Transport.r1b as Tr1b
import Examples.Groups.CCX+HH-3qubit.Transport.r1c as Tr1c
import Examples.Groups.CCX+HH-3qubit.Transport.r2a as Tr2a
import Examples.Groups.CCX+HH-3qubit.Transport.r2b as Tr2b
import Examples.Groups.CCX+HH-3qubit.Transport.r2c as Tr2c
import Examples.Groups.CCX+HH-3qubit.Transport.r2d as Tr2d
import Examples.Groups.CCX+HH-3qubit.Transport.r2e as Tr2e
import Examples.Groups.CCX+HH-3qubit.Transport.r2f as Tr2f
import Examples.Groups.CCX+HH-3qubit.Transport.r3a as Tr3a
import Examples.Groups.CCX+HH-3qubit.Transport.r3b as Tr3b
import Examples.Groups.CCX+HH-3qubit.Transport.r3c as Tr3c
import Examples.Groups.CCX+HH-3qubit.Transport.r3d as Tr3d
import Examples.Groups.CCX+HH-3qubit.Transport.r3e as Tr3e
import Examples.Groups.CCX+HH-3qubit.Transport.r3f as Tr3f
import Examples.Groups.CCX+HH-3qubit.Transport.r3g as Tr3g
import Examples.Groups.CCX+HH-3qubit.Transport.r4a as Tr4a
import Examples.Groups.CCX+HH-3qubit.Transport.r4b as Tr4b
import Examples.Groups.CCX+HH-3qubit.Transport.r4c as Tr4c
import Examples.Groups.CCX+HH-3qubit.Transport.r5a as Tr5a
import Examples.Groups.CCX+HH-3qubit.Transport.r6a as Tr6a

axiom-decode : ∀ {w v} → TL._===_ {8} w v → (decode ʷ) w ≈ (decode ʷ) v
axiom-decode (TL.r1a {a = a} {b = b} p0) = Tr1a.translate a b p0
axiom-decode (TL.r1b {a = a} ) = Tr1b.translate a
axiom-decode (TL.r1c {a = a} {b = b} {c = c} {d = d} p0 p1 p2) = Tr1c.translate a b c d p0 p1 p2
axiom-decode (TL.r2a {a = a} {b = b} {c = c} {d = d} p0 p1 ne0 ne1 ne2 ne3) = Tr2a.translate a b c d p0 p1 ne0 ne1 ne2 ne3
axiom-decode (TL.r2b {a = a} {b = b} {c = c} p0 ne0 ne1) = Tr2b.translate a b c p0 ne0 ne1
axiom-decode (TL.r2c {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7) = Tr2c.translate a b c d e f p0 p1 p2 p3 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7
axiom-decode (TL.r2d {a = a} {b = b} ne0) = Tr2d.translate a b ne0
axiom-decode (TL.r2e {a = a} {b = b} {c = c} {d = d} {e = e} p0 p1 p2 ne0 ne1 ne2 ne3) = Tr2e.translate a b c d e p0 p1 p2 ne0 ne1 ne2 ne3
axiom-decode (TL.r2f {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15) = Tr2f.translate a b c d e f g h p0 p1 p2 p3 p4 p5 ne0 ne1 ne2 ne3 ne4 ne5 ne6 ne7 ne8 ne9 ne10 ne11 ne12 ne13 ne14 ne15
axiom-decode (TL.r3a {a = a} {a′ = x} {b = b} p0 p1 p2) = Tr3a.translate a x b p0 p1 p2
axiom-decode (TL.r3b {a = a} {b = b} {b′ = y} p0 p1 p2) = Tr3b.translate a b y p0 p1 p2
axiom-decode (TL.r3c {a = a} {b = b} p0) = Tr3c.translate a b p0
axiom-decode (TL.r3d {a = a} {a′ = x} {b = b} {c = c} {d = d} p0 p1 p2 p3 p4) = Tr3d.translate a x b c d p0 p1 p2 p3 p4
axiom-decode (TL.r3e {a = a} {b = b} {b′ = y} {c = c} {d = d} p0 p1 p2 p3 p4 p5) = Tr3e.translate a b y c d p0 p1 p2 p3 p4 p5
axiom-decode (TL.r3f {a = a} {b = b} {c = c} {c′ = z} {d = d} p0 p1 p2 p3 p4 p5) = Tr3f.translate a b c z d p0 p1 p2 p3 p4 p5
axiom-decode (TL.r3g {a = a} {b = b} {c = c} {d = d} {d′ = t} p0 p1 p2 p3 p4) = Tr3g.translate a b c d t p0 p1 p2 p3 p4
axiom-decode (TL.r4a {a = a} {b = b} {c = c} {d = d} p0 p1 p2 p3) = Tr4a.translate a b c d p0 p1 p2 p3
axiom-decode (TL.r4b {a = a} {b = b} {c = c} {d = d} p0 p1 p2) = Tr4b.translate a b c d p0 p1 p2
axiom-decode (TL.r4c {a = a} {b = b} {c = c} {d = d} p0 p1 p2 p3) = Tr4c.translate a b c d p0 p1 p2 p3
axiom-decode (TL.r5a {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} p0 p1 p2 p3 p4 p5 p6) = Tr5a.translate a b c d e f p0 p1 p2 p3 p4 p5 p6
axiom-decode (TL.r6a {a = a} {b = b} {c = c} {d = d} {e = e} {f = f} {g = g} {h = h} p0 p1 p2 p3 p4 p5 p6 p7) = Tr6a.translate a b c d e f g h p0 p1 p2 p3 p4 p5 p6 p7

decode-cong : ∀ {w v} → PB._≈_ (TL._===_ {8}) w v → (decode ʷ) w ≈ (decode ʷ) v
decode-cong = PP.StarCongruence.fʷ-cong (TL._===_ {8}) Examples.Groups.CCX+HH-3qubit.Syntactics._===_ decode axiom-decode

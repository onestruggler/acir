# Four-state Clément translation at widths at least four

Let `N = 2^n`, with computational basis index
`x₀ + 2x₁ + ⋯ + 2^(n−1)xₙ₋₁`. Products are written in matrix order.
This construction uses the source presentations in `CCX+HH-TwoLevel`:
Table 1 for the dyadic letters `M_a`, `X_ab`, `K_abcd`, and Table 2 for
the additional global letter `IH = I ⊗ H` on wire 0. It does not use a
separate presentation of Toffoli–Hadamard circuits.

## The intermediate auxiliary subgroup

`Action.agda` proves that every source relation preserves the following
right action on four states `(d,s) ∈ F₂²`:

| Letter | Action |
|---|---|
| `M_a` | add `(1,0)` |
| `X_ab` | add `(1,1)` |
| `K_abcd` | add `(0,1)` |
| `IH` | `(d,s) ↦ (d,s+d)` |

Representatives of `00,10,11,01` are respectively
`1, M_0, X_01, M_0 X_01`. A Schreier letter `(c,g)` represents

```
e(c,g) = rep(c) g rep(c.g)^−1.
```

`Presentation.agda` applies the proved generic Schreier theorem to
these data. Its relations are the stateful translations of source
Tables 1 and 2, together with the Schreier-letter recovery equations.
It proves soundness and completeness for the exact source matrices,
and that the image consists exactly of source words fixing `00`.
Thus this intermediate presentation is unconditional. The physical
circuit realization of its generators is an additional step.

## Reducing every dyadic edge

A word over `M` and `X` has charge `00` precisely when it contains an
even number of each kind of letter. It describes a signed permutation
with an even permutation and an even number of negative entries.
Conversely such a matrix is a product of sign pairs `M_a M_b` and
double exchanges `X_ab X_cd`: move all signs to the left, pair them,
and pair the transpositions of the even permutation. Index coincidences
are allowed; repeated signs cancel and overlapping exchanges give a
three-cycle. `construct.py:signed_data` computes this decomposition in
matrix order. The decoder checks the two parities explicitly.

For an `M` or `X` source letter, the whole Schreier edge is already a
charge-zero signed permutation, so this suffices.

For `K_A = K_abcd`, put

```
L = rep(c),                 R = rep(c.K_A)^−1,
A₀ = M_a X_bc,              J_A = A₀ K_A,
T = L A₀^−1 R.
```

Choose two distinct indices `e,f` outside `{a,b,c,d}`. Let `Z` be a
word supported on these two indices whose `M`-count and `X`-count have
the same parities as `R`, and set `S = Z R`. Explicitly:

| Starting state `c` | `R` | `Z` |
|---|---|---|
| `00` | `X_01 M_0` | `M_e X_ef` |
| `10` | `X_01` | `X_ef` |
| `11` | `M_0` | `M_e` |
| `01` | `1` | `1` |

Both `T` and `S` are charge-zero signed permutations. Because `Z`
has support disjoint from `A`, Table 1's disjoint-support relations
give `Z J_A = J_A Z`. Therefore

```
T S^−1 J_A S
  = L A₀^−1 R R^−1 Z^−1 J_A Z R
  = L A₀^−1 J_A R
  = L K_A R
  = e(c,K_A).
```

`Factorization.agda` proves the cancellation identity in an arbitrary
group presentation. `DyadicSchreier.agda` proves the required support
commutations from Table 1, instantiates that identity for every `K`
edge, supplies syntactic witnesses that `T,S` contain only `M,X`, and
proves their charge is zero for all choices of the ordered indices.
In particular, the argument does not assume the representative indices
`0,1` are disjoint from the `K` support.

## The four Hadamard edges

Tables 1 and 2 imply

```
e(00,IH) = IH,
e(10,IH) = e(11,IH) = e(01,IH) = M_0 M_1 IH.
```

`HadamardSchreier.agda` proves these four equations uniformly at every
positive even dimension. Only one physical `H` and an already available
sign pair are needed in this part of the decoder.

## Fixed-width physical constructions and bounds

`construct.py` uses the constructions in
`CCX+HH/GeneralN/construct.py`, then replaces each `HH(i,j)` by
`H(i) H(j)`. It can expand all placements into the shifted adjacent
primitive gates of `Circuit.Base`.

The required dyadic primitives are:

1. A multiply controlled `X` with at most `n−2` controls. A borrowed
   existing wire is restored for both of its possible input values.
2. A basis-state three-cycle, obtained from the commutator of two double
   exchanges whose supports meet in exactly one point. Affine routing
   carries its three marked basis states to any requested three states.
3. A sign pair, obtained by conjugating a double exchange with physical
   `HH`, followed by affine routing.
4. Two disjoint `K` blocks. Table 1's reflection identity constructs
   the blocks at indices `0,…,7`; an even permutation routes them to
   arbitrary disjoint ordered quadruples.
5. The mixed atom `J_A`. Choose `e` and an ordered quadruple `B`, all
   disjoint from `A` and from each other. For `Q=K_A K_B` and
   `U=M_a M_e`, cancellation of disjoint letters and Table 1's rule
   `(4b)` give

   ```
   Q U Q U = K_A M_a K_A M_a = M_a X_bc K_A = J_A.
   ```

The edge factorization itself needs only six basis indices. The mixed
atom uses nine. Routing two `K` blocks fixes eight specified images and
uses two unspecified basis images to adjust permutation parity, so it
needs at least ten basis states. The three-cycle construction uses four
wires. All these requirements hold for `n≥4` (`N≥16`). Unspecified basis
states are routing space, not initialized ancillas; every claimed
matrix acts correctly on the entire `2^n`-dimensional space.

## Verification boundary

The auxiliary presentation, four-state action, four `IH` reductions,
generic factorization, and Table 1 support argument are safe Agda proofs.
The physical all-width construction currently has executable exact
checks in addition to the proved component lemmas under development.
It is not yet packaged as an unconditional all-width physical circuit
completeness theorem.

Run the independent exact checks with:

```sh
python3 Examples/Groups/CCX+H/GeneralN/construct.py --wires 4 --samples 4
```

This checks all 7,828 short source edge plans and 16 physical circuits,
including all four `IH` entries and samples from each dyadic family,
both before and after adjacent expansion. All matrix entries are exact
integer numerators divided by a power of `√2`. `--sample-plans` limits
the plan audit to 1,000 reproducibly sampled edges for larger widths;
`--samples` controls the physical checks per dyadic family.

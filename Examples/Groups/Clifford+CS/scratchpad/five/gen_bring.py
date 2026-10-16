# Writes bring₅ and bring₆ (Networks.agda's pattern) to stdout.
#   python3 gen_bring.py > /tmp/bring.agda
NAMES = 'abcdfgh'
SUB = '₀₁₂₃₄₅₆₇₈'


def fin(i, base='0F'):
    s = base
    for _ in range(i):
        s = f'sF ({s})' if ' ' in s else f'sF {s}'
    return s


def plus(k):
    return {1: '₁₊', 2: '₂₊', 3: '₃₊', 4: '₄₊', 5: '₅₊', 6: '₆₊'}[k]


def ups(k, base):
    """base ↑ (k times), parenthesised."""
    s = base
    for _ in range(k):
        s = f'({s}) S.↑' if ' ' in s else f'{s} S.↑'
    return s


def chain_lo(k, i):
    """perm v (fin i) ≡ fin i for v = ups (k-1) (sdS (toℕ x)), i < k - 1."""
    # v = w_{k-1}, w_0 = sdS (toℕ x), w_{j+1} = w_j S.↑ ; perm w_{j+1} (sF y) = sF (perm w_j y)
    # peel i levels with perm-↑s, then perm-↑0 at level k-1-i
    def w(j): return ups(j, 'sdS (toℕ x)')
    if i == 0:
        return f'perm-↑0 ({w(k - 2)})'
    inner = chain_lo_from(k - 2, i)
    return inner


def chain_lo_from(top, i):
    """perm w_top (fin i) ≡ fin i, where w_top = ups top (sdS (toℕ x))."""
    def w(j): return ups(j, 'sdS (toℕ x)')
    if i == 0:
        return f'perm-↑0 ({w(top - 1)})'
    rest = chain_lo_from(top - 1, i - 1)
    return f'Eq.trans (perm-↑s ({w(top - 1)}) ({fin(i - 1)})) (Eq.cong sF ({rest}))'


def chain_hi_from(top):
    """perm w_top (fin top over x) ≡ fin top."""
    def w(j): return ups(j, 'sdS (toℕ x)')
    if top == 0:
        return 'sd-target x'
    rest = chain_hi_from(top - 1)
    return f'Eq.trans (perm-↑s ({w(top - 1)}) ({fin(top - 1, "x")})) (Eq.cong sF ({rest}))'


def bring(k):
    ws = NAMES[:k]
    pk = plus(k)
    dist = []
    for j in range(1, k):
        for i in range(j):
            dist.append((ws[j], ws[i]))
    hyp = ' → '.join(f'{b} ≢ {a}' for b, a in dist)
    hypn = ' '.join(f'{b}{a}' for b, a in dist)
    prev = [(b, a) for b, a in dist if b != ws[-1]]
    prevn = ' '.join(f'{b}{a}' for b, a in prev)
    concl = ' ×\n             '.join(f'(perm σ ⟨$⟩ʳ {ws[i]} ≡ {fin(i)})' for i in range(k))
    conclρ = ' ×\n           '.join(f'(perm ρ ⟨$⟩ʳ {ws[i]} ≡ {fin(i)})' for i in range(k))
    last = ws[-1]
    out = []
    out.append(f'  -- {", ".join(ws)} to the wires 0 … {k - 1}.')
    out.append(f'  bring{SUB[k]} : ({" ".join(ws)} : Fin ({pk} n)) → {hyp} →')
    out.append(f'           Σ (Word (S.Gen ({pk} n))) λ σ →')
    out.append(f'             {concl}')
    out.append(f'  bring{SUB[k]} {{n}} {" ".join(ws)} {hypn} with bring{SUB[k - 1]} {" ".join(ws[:-1])} {prevn}')
    pat = ' , '.join(f'σ{ws[i]}' for i in range(k - 1))
    out.append(f'  ... | σ , {pat} = go (perm σ ⟨$⟩ʳ {last}) Eq.refl')
    out.append('    where')
    out.append(f'    go : ∀ x → perm σ ⟨$⟩ʳ {last} ≡ x →')
    out.append(f'         Σ (Word (S.Gen ({pk} n))) λ ρ →')
    out.append(f'           {conclρ}')
    for i in range(k - 1):
        out.append(f'    go {fin(i) if i == 0 else "(" + fin(i) + ")"} eq = ⊥-elim ({last}{ws[i]} (perm-inj σ (Eq.trans eq (Eq.sym σ{ws[i]}))))')
    xs = fin(k - 1, 'x')
    out.append(f'    go ({xs}) eq = σ • v , {" , ".join("ρ" + ws[i] for i in range(k))}')
    out.append('      where')
    out.append(f'      v : Word (S.Gen ({pk} n))')
    out.append(f'      v = {ups(k - 1, "sdS (toℕ x)")}')
    for i in range(k - 1):
        out.append(f'      ρ{ws[i]} : perm (σ • v) ⟨$⟩ʳ {ws[i]} ≡ {fin(i)}')
        out.append(f'      ρ{ws[i]} = Eq.trans (Eq.cong (perm v ⟨$⟩ʳ_) σ{ws[i]}) ({chain_lo_from(k - 1, i)})')
    out.append(f'      ρ{last} : perm (σ • v) ⟨$⟩ʳ {last} ≡ {fin(k - 1)}')
    out.append(f'      ρ{last} = Eq.trans (Eq.cong (perm v ⟨$⟩ʳ_) eq) ({chain_hi_from(k - 1)})')
    return '\n'.join(out)


if __name__ == '__main__':
    print()
    print(bring(5))
    print()
    print(bring(6))

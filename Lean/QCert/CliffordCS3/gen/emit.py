"""Lean emission of proof tables: every equation needed by the targets becomes a rule
(`Rule Γ`), an axiom by its constructor, a derived equation by a packed certificate replayed by
`Rule.byChunks` (`QCert.CliffordT2.FastRewrite`), on the expanded words."""


def needed(T, targets):
    """The equations the targets depend on (transitively)."""
    seen = set()
    stack = [t for t in targets if t is not None]
    while stack:
        k = stack.pop()
        if k in seen:
            continue
        seen.add(k)
        j = T.eqs[k][2]
        if j[0] == 'der':
            for (p, kk, d) in j[1]:
                if kk not in seen:
                    stack.append(kk)
    return sorted(seen)


def expanded(A, k):
    l, r, j = A.T.eqs[k]
    return A.expand(l), A.expand(r)


def exp_steps(A, k):
    """The steps of derived equation k on the expanded words, dropping no-op steps."""
    T = A.T
    l, r, j = T.eqs[k]
    out = []
    w = tuple(l)
    for (p, kk, d) in j[1]:
        el, er = expanded(A, kk)
        if T.eqs[kk][2][0] != 'def' and el != er:
            out.append((len(A.expand(w[:p])), kk, d))
        w = T.apply(w, (p, kk, d))
    return out


def stats(A, targets):
    ks = needed(A.T, targets)
    nsteps = 0
    nder = 0
    for k in ks:
        if A.T.eqs[k][2][0] == 'der':
            el, er = expanded(A, k)
            if el != er:
                nder += 1
                nsteps += len(exp_steps(A, k))
    return len(ks), nder, nsteps

"""The dispatch of r2f in separate modules: one per sorted (a, b, c, d),
casing on (e, f, g, h), and a main module casing on (a, b, c, d)."""
import os
from table import T1, instances, holds
from emit_family import (TW, MODP, FL, DISP_HEADER, arg_names, binder, side, fid)

con = [c for c in T1 if c[0] == 'r2f'][0]
name, vs, args = con[0], con[1].split(), con[2]
nms = arg_names(args)
insts = instances(con)
chunk = 60
mods = [(f'{fid(name)}-{lo // chunk}', lo, min(lo + chunk, len(insts))) for lo in range(0, len(insts), chunk)]
where = {}
for j, (m, lo, hi) in enumerate(mods):
    for k in range(lo, hi):
        where[k] = (j, k)
index = {tuple(v[x] for x in vs): k for k, v in enumerate(insts)}
os.makedirs(os.path.join(TW, 'Disp'), exist_ok=True)


def lit(x):
    return FL[x]


def sig_for(fname, fixed):
    rv = [x for x in vs if x not in fixed]

    def sub(t):
        return lit(fixed[t]) if t in fixed else t
    binds = []
    if rv:
        binds.append(f'({" ".join(rv)} : Fin 8)')
    for a_, n_ in zip(args, nms):
        a2 = (a_[0],) + tuple(sub(t) if isinstance(t, str) else t for t in a_[1:])
        if a_[0] == 'lt' and all(t in fixed for t in a_[1:]):
            binds.append(f'.({n_} : _<_ {{8}} {{8}} {a2[1]} {a2[2]})')
        else:
            binds.append(binder(a2, n_))
    allv = ' '.join(sub(x) for x in vs)
    return (f'{fname} : {" → ".join(binds)} → 3 ⊢ Br.ι (D′ (lhs {allv} {" ".join(nms)})) ≈ '
            f'Br.ι (D′ (rhs {allv} {" ".join(nms)}))')


def tree(fname, fixed, upto, leaf):
    """clauses casing on the variables of vs not in fixed, up to `upto` of them"""
    rv = [x for x in vs if x not in fixed]
    clauses = []

    def pat(vals):
        return [lit(x) for x in vals] + ['_'] * (len(rv) - len(vals))

    def rec(vals):
        j = len(vals)
        if j == upto:
            clauses.append(leaf(vals))
            return
        for x in range(8):
            nv = vals + [x]
            v = dict(fixed)
            v.update(dict(zip(rv, nv)))
            bad = None
            for a_, nm in zip(args, nms):
                vars_ = [t for t in a_[1:] if isinstance(t, str)]
                if all(t in v for t in vars_) and rv[j] in vars_ and not holds(a_, v):
                    bad = (a_, nm)
                    break
            if bad is None:
                rec(nv)
                continue
            a_, nm = bad
            if a_[0] == 'lt':
                clauses.append(f'{fname} {" ".join(pat(nv) + nms)} = EI.⊥-elim (refute< tt {nm})')
            else:
                clauses.append(f'{fname} {" ".join(pat(nv) + nms)} = E.⊥-elim ({nm} Eq.refl)')
    rec([])
    return clauses


HDR = DISP_HEADER.replace('module {modp}.Disp.{mod} where', 'module {modp}.Disp.{mod} where')
lhs = side(con[3], args, nms, 1)
rhs = side(con[4], args, nms, 1)
pre = ' → '.join([f'({" ".join(vs)} : Fin 8)'] + [binder(a, n) for a, n in zip(args, nms)]) + ' → '
params = ' '.join(vs + nms)

# base: lhs and rhs
base = HDR.format(fam=name, modp=MODP, mod='r2f-base', imports='')
base += f'''
lhs rhs : {pre}Word (T.Genᴸ 8)
lhs {params} = {lhs}
rhs {params} = {rhs}
'''
open(os.path.join(TW, 'Disp', 'r2f-base.agda'), 'w', encoding='utf-8').write(base)

children = []
for abcd in sorted({k[:4] for k in index}):
    fixed = dict(zip('abcd', abcd))
    cname = 'c' + ''.join(str(x) for x in abcd)
    k = index[abcd + tuple(x for x in range(8) if x not in abcd)]
    jm, kk = where[k]
    mod = f'r2f-{cname}'

    def leaf(vals, fixed=fixed, jm=jm, kk=kk):
        full = dict(fixed)
        full.update(dict(zip('efgh', vals)))
        ins = ' '.join(lit(full[x]) for x in vs) + ' ' + ' '.join(nms)
        return f'd {" ".join([lit(x) for x in vals] + nms)} = byLoop (lhs {ins}) (rhs {ins}) I.i{kk}'
    cl = tree('d', fixed, 4, leaf)
    text = HDR.format(fam=f'{name} at {abcd}', modp=MODP, mod=mod,
                      imports=f'import {MODP}.Inst.{mods[jm][0]} as I\nopen import {MODP}.Disp.r2f-base using (lhs ; rhs)')
    text += '\n' + sig_for('d', fixed) + '\n' + '\n'.join(cl) + '\n'
    open(os.path.join(TW, 'Disp', mod + '.agda'), 'w', encoding='utf-8').write(text)
    children.append((abcd, mod))

imps = '\n'.join(f'import {MODP}.Disp.{m} as C{"".join(str(x) for x in a)}' for a, m in children)
imps += f'\nopen import {MODP}.Disp.r2f-base public using (lhs ; rhs)'
main = HDR.format(fam=name, modp=MODP, mod='r2f', imports=imps)


def mleaf(vals):
    tag = ''.join(str(x) for x in vals)
    return f'd {" ".join([lit(x) for x in vals] + ["e", "f", "g", "h"] + nms)} = C{tag}.d e f g h {" ".join(nms)}'


cl = tree('d', {}, 4, mleaf)
main += f'\nd : {pre}3 ⊢ Br.ι (D′ (lhs {params})) ≈ Br.ι (D′ (rhs {params}))\n' + '\n'.join(cl) + '\n'
open(os.path.join(TW, 'Disp', 'r2f.agda'), 'w', encoding='utf-8').write(main)
print('children', len(children), 'main clauses', len(cl))

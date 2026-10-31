#!/usr/bin/env python3
"""Independent audit computation for notes/h_vector_omega_c.md.

Self-contained: imports nothing from the repository.  For every poset with
n <= NMAX (up to isomorphism) it computes Omega_C(P, m) straight from the
Moebius function of OP(P) (order-preserving set partitions under
refinement), extracts the h-vector, and compares it with cyclic-descent
statistics on the cyclic classes of Lin P under various natural
labellings.  Prints one tagged line per check; exits 0 iff every claim
holds and every CONTROL is refuted somewhere.
"""
import sys, itertools, argparse
from math import comb
from collections import Counter

# ---------------------------------------------------------------- posets
# A poset on {0..n-1} is a tuple `down` of bitmasks: down[x] = strict down-set.
def up_sets(down):
    n = len(down); up = [0]*n
    for y in range(n):
        for x in range(n):
            if down[y] >> x & 1: up[x] |= 1 << y
    return up

def less(down, x, y): return down[y] >> x & 1

def canon(down):
    """Canonical form: lex-min relation matrix over invariant-respecting perms."""
    n = len(down); up = up_sets(down)
    inv = [(bin(down[x]).count('1'), bin(up[x]).count('1')) for x in range(n)]
    for _ in range(2):  # refine by neighbour invariants
        inv = [(inv[x], tuple(sorted(inv[y] for y in range(n) if down[x]>>y&1)),
                tuple(sorted(inv[y] for y in range(n) if up[x]>>y&1))) for x in range(n)]
    keys = sorted(set(inv)); cells = [[x for x in range(n) if inv[x] == k] for k in keys]
    best = None
    for parts in itertools.product(*[itertools.permutations(c) for c in cells]):
        order = [x for p in parts for x in p]          # new label i -> old element order[i]
        code = tuple(1 if less(down, order[i], order[j]) else 0
                     for i in range(n) for j in range(n))
        if best is None or code < best: best = code
    return best

def ideals(down):
    n = len(down); res = []
    for S in range(1 << n):
        if all((down[x] & ~S) == 0 for x in range(n) if S >> x & 1): res.append(S)
    return res

def all_posets(nmax):
    """Posets up to iso, n = 1..nmax; each naturally labelled (new max on top)."""
    levels = {1: [(0,)]}
    for n in range(2, nmax + 1):
        seen = {}
        for P in levels[n-1]:
            for I in ideals(P):
                Q = P + (I,)
                c = canon(Q)
                if c not in seen: seen[c] = Q
        levels[n] = list(seen.values())
    return levels

def relabel(down, order):
    """order[i] = old element getting new label i."""
    n = len(down); pos = {order[i]: i for i in range(n)}
    return tuple(sum(1 << pos[x] for x in range(n) if down[order[i]] >> x & 1) for i in range(n))

def is_natural(down):
    return all((down[y] >> y) == 0 for y in range(len(down)))  # x<y => x<y as ints

# ------------------------------------------------------------- OP(P), mu
def set_partitions(n):
    def rec(i, blocks):
        if i == n: yield [b for b in blocks]; return
        for k in range(len(blocks)):
            blocks[k] |= 1 << i; yield from rec(i+1, blocks); blocks[k] &= ~(1 << i)
        blocks.append(1 << i); yield from rec(i+1, blocks); blocks.pop()
    yield from rec(0, [])

def op_partitions(down):
    n = len(down); res = []
    for blocks in set_partitions(n):
        k = len(blocks); bid = [0]*n
        for i, b in enumerate(blocks):
            for x in range(n):
                if b >> x & 1: bid[x] = i
        adj = [set() for _ in range(k)]
        for y in range(n):
            for x in range(n):
                if down[y] >> x & 1 and bid[x] != bid[y]: adj[bid[x]].add(bid[y])
        # acyclic?
        indeg = [0]*k
        for a in range(k):
            for b in adj[a]: indeg[b] += 1
        st = [a for a in range(k) if indeg[a] == 0]; cnt = 0
        while st:
            a = st.pop(); cnt += 1
            for b in adj[a]:
                indeg[b] -= 1
                if indeg[b] == 0: st.append(b)
        if cnt == k: res.append((tuple(blocks), tuple(blocks[bid[x]] for x in range(n))))
    return res

def mu_to_top(down):
    """List of (|pi|, mu(pi, 1hat)) over pi in OP(P), by the recursion from the top."""
    parts = op_partitions(down)
    parts.sort(key=lambda p: len(p[0]))
    mu = []
    for i, (bl, _) in enumerate(parts):
        if len(bl) == 1: mu.append(1); continue
        s = 0
        for j in range(i):
            bl2, mask_of = parts[j]
            if len(bl2) >= len(bl): break
            low = lambda b: (b & -b).bit_length() - 1
            if all(mask_of[low(b)] & b == b for b in bl): s += mu[j]
        mu.append(-s)
    return [(len(p[0]), m) for p, m in zip(parts, mu)]

def omega_values(mus, n, M):
    """Omega_C(P, m) for m = 0..M, signed definition and |mu| version."""
    sgn = [sum((-1)**(k-1) * m_ * comb(m, k) for k, m_ in mus) for m in range(M+1)]
    ab = [sum(abs(m_) * comb(m, k) for k, m_ in mus) for m in range(M+1)]
    return sgn, ab

def h_from_values(vals, n):
    """sum_m Om(m) x^m = sum_j h_j x^{j+1}/(1-x)^{n+1}; return h_0..h_n."""
    coeff = [0]*(n+2)
    for k in range(n+2):
        coeff[k] = sum((-1)**i * comb(n+1, i) * vals[k-i] for i in range(k+1))
    assert coeff[0] == 0
    return tuple(coeff[1:n+2])

def h_dist(stats, n):
    c = Counter(stats); return tuple(c.get(j, 0) for j in range(n+1))

# --------------------------------------------------- words, classes, cdes
def linext(down):
    n = len(down); res = []
    def rec(w, used):
        if len(w) == n: res.append(tuple(w)); return
        for x in range(n):
            if not used >> x & 1 and (down[x] & ~used) == 0:
                w.append(x); rec(w, used | 1 << x); w.pop()
    rec([], 0); return res

def components(down):
    n = len(down); up = up_sets(down); comp = [-1]*n; masks = []
    for s in range(n):
        if comp[s] >= 0: continue
        st = [s]; comp[s] = len(masks); m = 1 << s
        while st:
            x = st.pop()
            for y in range(n):
                if (down[x] >> y & 1 or up[x] >> y & 1) and comp[y] < 0:
                    comp[y] = len(masks); m |= 1 << y; st.append(y)
        masks.append(m)
    return masks

def des(w): return sum(1 for i in range(len(w)-1) if w[i] > w[i+1])
def cdes(w): return des(w) + (1 if w[-1] > w[0] else 0)          # [LS] §0 definition
def Des(w): return {i+1 for i in range(len(w)-1) if w[i] > w[i+1]}

def cuts(w, comps):
    """p in [1, n-1] with {w_1..w_p} a union of components (by definition)."""
    res = []; pre = 0
    for p in range(1, len(w)):
        pre |= 1 << w[p-1]
        if all((c & pre) in (0, c) for c in comps): res.append(p)
    return res

def classes(L, comps, Lset):
    seen = {}; out = []
    for w in L:
        if w in seen: continue
        cl = {w}
        for p in cuts(w, comps): cl.add(w[p:] + w[:p])
        # cross-check with the orbit definition: wC_n ∩ Lin P
        orb = {w[k:] + w[:k] for k in range(len(w))} & Lset
        assert orb == cl, "cut rotations != C_n-orbit ∩ Lin P"
        for u in cl: seen[u] = len(out)
        out.append(sorted(cl))
    return out

def pieces(w, comps):
    cs = [0] + cuts(w, comps) + [len(w)]
    return [w[cs[i]:cs[i+1]] for i in range(len(cs)-1)]

def all_ascent(cl, comps):
    w = cl[0]; pc = pieces(w, comps); s = len(pc)
    if s < 2: return False
    return all(pc[k][-1] < pc[(k+1) % s][0] for k in range(s))

def separated(down):
    n = len(down); up = up_sets(down); comps = components(down)
    nonisol = [x for x in range(n) if down[x] | up[x]]
    mins = [x for x in nonisol if down[x] == 0]; maxs = [x for x in nonisol if up[x] == 0]
    return all(a < b for a in mins for b in maxs)

def lambda0(down):
    """Order (old elements) for the note's labelling lambda_0."""
    n = len(down); up = up_sets(down)
    isol = [x for x in range(n) if down[x] == 0 and up[x] == 0]
    mins = [x for x in range(n) if down[x] == 0 and up[x]]
    maxs = [x for x in range(n) if up[x] == 0 and down[x]]
    mid = [x for x in range(n) if down[x] and up[x]]   # given labels already natural
    return mins + mid + isol + maxs

def N_T(w, T, comps, m):
    n = len(w); pre = 0; CT = []
    cs = set(cuts(w, comps))
    for p in range(1, n):
        pre |= 1 << w[p-1]
        if p in cs and (T & pre) == T: CT.append(p)
    if set(CT) & Des(w): return 0
    c = len(CT); return comb(m + n - 1 - des(w) - c, n - c)

def brute_theorem_omega(down, T, m):
    """#{f: P->[m] order-preserving : every nonempty upper level set that is a
    union of components contains T}.  Direct count."""
    n = len(down); comps = components(down); cnt = 0
    for f in itertools.product(range(1, m+1), repeat=n):
        if any(f[x] > f[y] for y in range(n) for x in range(n) if down[y] >> x & 1): continue
        ok = True
        for v in set(f):
            U = sum(1 << x for x in range(n) if f[x] >= v)
            if all((c & U) in (0, c) for c in comps) and (U & T) != T: ok = False; break
        if ok: cnt += 1
    return cnt

# ------------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--nmax', type=int, default=7)
    ap.add_argument('--lmax', type=int, default=6); ap.add_argument('--bmax', type=int, default=5)
    a = ap.parse_args()
    levels = all_posets(a.nmax)
    print('[posets] counts', [len(levels[n]) for n in range(1, a.nmax+1)],
          'total', sum(len(levels[n]) for n in levels))
    C = Counter(); F = Counter(); fails = []
    def check(tag, ok, info=None):
        C[tag] += 1
        if not ok:
            F[tag] += 1
            if len([f for f in fails if f[0] == tag]) < 2: fails.append((tag, info))
    small = {}
    for n in range(1, a.nmax+1):
        for P in levels[n]:
            mus = mu_to_top(P)
            for k, m_ in mus: check('mu-sign', (-1)**(k-1) * m_ >= 0, P)
            sv, av = omega_values(mus, n, n+1)
            check('signed=abs', sv == av, P)
            h = h_from_values(sv, n)
            check('h>=0', all(x >= 0 for x in h), (P, h))
            comps = components(P)
            check('Om(1)=1', sv[1] == 1, P)
            # e_C via classes on the generated labelling
            L = linext(P); Ls = set(L); cls = classes(L, comps, Ls)
            check('sum h = e_C', sum(h) == len(cls), (P, h))
            small[(n, canon(P))] = h
            # labellings to test
            if n <= a.lmax:
                labs = {}
                for wl in L:
                    Q = relabel(P, list(wl))
                    labs[Q] = None
                labs = list(labs)
            else:
                labs = [P]
            l0 = relabel(P, lambda0(P)); assert is_natural(l0)
            check('lambda0-natural+separated', is_natural(l0) and separated(l0), P)
            if l0 not in labs: labs.append(l0)
            for Q in labs:
                assert is_natural(Q)
                cq = components(Q); LQ = linext(Q); LQs = set(LQ); clq = classes(LQ, cq, LQs)
                for cl in clq: check('cdes-class-const', len({cdes(w) for w in cl}) == 1, cl)
                mind = [min(des(w) for w in cl) for cl in clq]
                cd1 = [cdes(cl[0]) - 1 for cl in clq] if n >= 2 else [0]*len(clq)
                aa = [all_ascent(cl, cq) for cl in clq]
                sep = separated(Q)
                tagn = 'n<=%d' % a.lmax if n <= a.lmax else 'n=%d-lab' % n
                C['labelled ' + tagn] += 1
                if n >= 2:
                    check('ctl-cdes-any [CONTROL]', h_dist(cd1, n) == h, Q)
                    if sep:
                        C['separated ' + tagn] += 1
                        check('H: no all-ascent', not any(aa), Q)
                        check('H: mindes=cdes-1 classwise', mind == cd1, Q)
                        check('H: cdes-1 dist = h', h_dist(cd1, n) == h, (Q, h))
                    if not any(aa):
                        check("H': mindes dist = h", h_dist(mind, n) == h, (Q, h))
                    else:
                        C['has all-ascent ' + tagn] += 1
                        check("ctl-H'' mindes with all-ascent [CONTROL]", h_dist(mind, n) == h, Q)
                    check('ctl-lin des on Lin P [CONTROL]', h_dist([des(w) for w in LQ], n) == h, Q)
                    linok = h_dist([des(w) for w in LQ], n) == h
                    if Q == P:
                        check('lin: des on Lin P = h iff connected', linok == (len(cq) == 1), Q)
                    if len(cq) == 1:
                        check('lin: connected, every labelling, des = h', linok, Q)
                    # B_P conventions
                    top = n - 1; Ttop = [c for c in cq if c >> top & 1][0]
                    zero = [c for c in cq if c & 1][0]
                    BPl = [w for cl in clq for w in cl if
                           (sum(1 << x for x in pieces(w, cq)[-1]) & Ttop) == Ttop]
                    BPf = [w for cl in clq for w in cl if
                           (sum(1 << x for x in pieces(w, cq)[0]) & zero) == zero]
                    assert len(BPl) == len(clq) == len(BPf)
                    okl = h_dist([des(w) for w in BPl], n) == h
                    okf = h_dist([des(w) for w in BPf], n) == h
                    if Q == l0:
                        check('B: lambda0 last-piece', okl, Q); check('B: lambda0 first-piece', okf, Q)
                        if n <= a.lmax:
                            for B in cq:   # [LE]-style B_P: first block contains an arbitrary base component
                                BPb = [w for cl in clq for w in cl if
                                       (sum(1 << x for x in pieces(w, cq)[0]) & B) == B]
                                check('ctl-BP-first arbitrary base, lambda0 [CONTROL]',
                                      h_dist([des(w) for w in BPb], n) == h, (Q, B))
                    if sep and n <= a.lmax:
                        check('ctl-BP-last separated [CONTROL]', okl, Q)
                        check('ctl-BP-first separated [CONTROL]', okf, Q)
                # Prop D and Lemma 1, every T, m = 0..n+1
                for T in cq:
                    for m in range(n+2):
                        tot = sum(N_T(w, T, cq, m) for w in LQ)
                        check('D: sum_w N_T = Omega_C', tot == sv[m], (Q, T, m))
                    for cl, md, isaa in zip(clq, mind, aa):
                        if isaa: continue
                        for m in range(n+2):
                            check('L1: per-class', sum(N_T(w, T, cq, m) for w in cl)
                                  == comb(m + n - 1 - md, n), (cl, T, m))
                    if n <= a.bmax and Q == P:
                        for m in range(min(4, n+2)):
                            check('Thm-Omega brute (maps)', brute_theorem_omega(Q, T, m) == sv[m], (Q, T, m))
    # small values table of the note
    def h_of(P): return small[(len(P), canon(P))]
    tbl = {'C2+C1': ((0, 1, 0), (1, 1, 0, 0)), 'C2+C2': ((0, 1, 0, 4), (1, 3, 1, 0, 0)),
           'C3+C1': ((0, 1, 3, 0), (1, 2, 0, 0, 0)), 'A4': ((0, 0, 0, 0), (1, 4, 1, 0, 0))}
    for name, (P, exp) in tbl.items():
        check('table ' + name, h_of(P) == exp, (name, h_of(P)))
    for n in range(1, a.nmax+1):
        A = tuple([0]*n); E = [sum((-1)**i*comb(n, i)*(k+1-i)**(n-1) for i in range(k+1)) for k in range(n)]
        check('antichain Eulerian', list(h_of(A))[:n] == E, (n, h_of(A)))
    disc = sum(1 for n in levels for P in levels[n] if len(components(P)) > 1)
    print('[disconnected posets]', disc)
    for k in sorted(C):
        f = F.get(k, 0)
        if 'CONTROL' in k: verdict = 'REFUTED (good)' if f else 'NOT REFUTED (BAD)'
        elif k.startswith(('labelled', 'separated', 'has all-ascent')): verdict = ''
        else: verdict = 'OK' if f == 0 else 'FAIL'
        print('[%s] cases=%d failures=%d %s' % (k, C[k], f, verdict))
    for t, info in fails: print('  example', t, info)
    bad = any(F.get(k, 0) for k in C if 'CONTROL' not in k) or \
          any(F.get(k, 0) == 0 for k in C if 'CONTROL' in k)
    print('EXIT', 1 if bad else 0); sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()

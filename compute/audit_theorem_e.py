"""Independent audit computations for notes/theorem_e_equivariant_wedge.md.

Plain Python 3, no third-party packages, single process, imports nothing from the repo.

Model.  An arrangement is a list of integer normal vectors in R^n (possibly with a
lineality space L, as for the braid arrangement in R^n).  Faces are sign vectors of
lattice points in a box; completeness is certified by the Euler characteristic of the
induced sphere decomposition.  Groups are signed permutation groups of R^n (matrices
M e_i = s_i e_{t_i}), acting on hyperplanes through M^T.  Lambda(V) is the set of zero
sets of the faces of V, ordered by reverse inclusion of zero sets.

For every subgroup H (enumerated by closing <K, g> over all K and g, from scratch):
  * Lambda-bar(V)^H, its order complex, reduced Betti numbers mod 2, 3, 5, 7, 1000003,
    a Stong core when contractibility is predicted;
  * m_H = #chambers of V fixed by H, e_H = dim Fix(H) on R^n / L;
  * Theorem E prediction (free action, pointed): H = 1 -> #V in degree d-2; H != 1 ->
    acyclic, Stong core one point;
  * Theorem S prediction (pointed, any G): Z^{m_H} in degree e_H - 2.
For H = 1 additionally:
  * F_p-freeness of H_{d-2}(T; Z) (x) F_p restricted to every cyclic p-subgroup <g>
    (conjugacy-class representatives): dim ker(g - 1) = dim / |g|;
  * the singular set T_s = union_{H != 1} T^H is acyclic.
Lemma F: for every H, the H-stable faces of A are exactly the sign vectors of points of
Fix(H) (sampled, completeness certified by Euler characteristic), and for every H-stable
Y in Lambda(V), Y != 0, the poset F(Y)^H has Stong core one point.
"""

import itertools
import sys
from fractions import Fraction
from math import gcd

PRIMES = (2, 3, 5, 7, 1000003)

# ----------------------------------------------------------------- linear algebra


def rank_q(rows):
    m = [[Fraction(x) for x in r] for r in rows]
    rk, col = 0, 0
    ncol = len(m[0]) if m else 0
    for col in range(ncol):
        piv = next((i for i in range(rk, len(m)) if m[i][col] != 0), None)
        if piv is None:
            continue
        m[rk], m[piv] = m[piv], m[rk]
        for i in range(len(m)):
            if i != rk and m[i][col] != 0:
                f = m[i][col] / m[rk][col]
                m[i] = [a - f * b for a, b in zip(m[i], m[rk])]
        rk += 1
    return rk


def nullspace_q(rows, n):
    """Basis (integer vectors) of {x in Q^n : rows x = 0}."""
    m = [[Fraction(x) for x in r] for r in rows]
    pivots = []
    rk = 0
    for col in range(n):
        piv = next((i for i in range(rk, len(m)) if m[i][col] != 0), None)
        if piv is None:
            continue
        m[rk], m[piv] = m[piv], m[rk]
        p = m[rk][col]
        m[rk] = [a / p for a in m[rk]]
        for i in range(len(m)):
            if i != rk and m[i][col] != 0:
                f = m[i][col]
                m[i] = [a - f * b for a, b in zip(m[i], m[rk])]
        pivots.append(col)
        rk += 1
    free = [c for c in range(n) if c not in pivots]
    basis = []
    for fc in free:
        v = [Fraction(0)] * n
        v[fc] = Fraction(1)
        for r, pc in enumerate(pivots):
            v[pc] = -m[r][fc]
        den = 1
        for x in v:
            den = den * x.denominator // gcd(den, x.denominator)
        basis.append([int(x * den) for x in v])
    return basis


def sparse_rank(rows, p):
    """rows: list of dict col->int.  Rank mod p."""
    piv = {}
    rk = 0
    for r in rows:
        r = {c: v % p for c, v in r.items() if v % p}
        while r:
            c = min(r)
            if c in piv:
                pr = piv[c]
                f = r[c]
                for cc, vv in pr.items():
                    nv = (r.get(cc, 0) - f * vv) % p
                    if nv:
                        r[cc] = nv
                    else:
                        r.pop(cc, None)
            else:
                inv = pow(r[c], p - 2, p)
                piv[c] = {cc: (vv * inv) % p for cc, vv in r.items()}
                rk += 1
                break
    return rk


# ----------------------------------------------------------------- posets / complexes


def chains(elems, lt):
    """All nonempty chains (as tuples increasing in the order) of the poset on elems."""
    elems = list(elems)
    idx = {e: i for i, e in enumerate(elems)}
    up = {e: [f for f in elems if lt(e, f)] for e in elems}
    out = []

    def rec(ch):
        out.append(tuple(ch))
        for f in up[ch[-1]]:
            ch.append(f)
            rec(ch)
            ch.pop()

    for e in elems:
        rec([e])
    return out, idx


def boundary_rows(simplices_k, index_km1):
    rows = []
    for s in simplices_k:
        if len(s) == 1:
            rows.append({0: 1})  # augmentation to C_{-1}
            continue
        r = {}
        for i in range(len(s)):
            f = s[:i] + s[i + 1:]
            r[index_km1[f]] = r.get(index_km1[f], 0) + (-1) ** i
        rows.append(r)
    return rows


def reduced_betti_complex(simplices, p):
    """simplices: set of tuples (each closed under faces).  Augmented complex mod p."""
    by = {}
    for s in simplices:
        by.setdefault(len(s) - 1, []).append(s)
    top = max(by) if by else -1
    idx = {k: {s: i for i, s in enumerate(v)} for k, v in by.items()}
    idx[-1] = {(): 0}
    by[-1] = [()]
    ranks = {}
    for k in range(0, top + 1):
        ranks[k] = sparse_rank(boundary_rows(by[k], idx[k - 1]), p)
    betti = {}
    for k in range(-1, top + 1):
        b = len(by[k]) - ranks.get(k, 0) - ranks.get(k + 1, 0)
        if b:
            betti[k] = b
    return betti


def poset_betti(elems, lt, p):
    ch, _ = chains(elems, lt)
    return reduced_betti_complex(set(ch), p)


def poset_betti_all(elems, lt):
    ch, _ = chains(elems, lt)
    S = set(ch)
    res = [reduced_betti_complex(S, p) for p in PRIMES]
    return res[-1], all(r == res[-1] for r in res)


def stong_core(elems, lt):
    E = set(elems)
    changed = True
    while changed:
        changed = False
        for x in list(E):
            ups = [y for y in E if lt(x, y)]
            mins = [y for y in ups if not any(lt(z, y) for z in ups)]
            downs = [y for y in E if lt(y, x)]
            maxs = [y for y in downs if not any(lt(y, z) for z in downs)]
            if len(mins) == 1 or len(maxs) == 1:
                E.remove(x)
                changed = True
                break
    return len(E)


# ----------------------------------------------------------------- signed permutation groups


def sp_mul(a, b):
    """(a*b) e_i = a(b e_i).  a, b: tuples of (target, sign)."""
    return tuple((a[t][0], a[t][1] * s) for (t, s) in b)


def sp_id(n):
    return tuple((i, 1) for i in range(n))


def gen_group(gens, n):
    e = sp_id(n)
    G = {e}
    fr = [e]
    while fr:
        nf = []
        for x in fr:
            for g in gens:
                y = sp_mul(g, x)
                if y not in G:
                    G.add(y)
                    nf.append(y)
        fr = nf
    return G


def subgroups(G, n):
    """All subgroups: BFS over K -> <K, g>, starting from the trivial group."""
    e = sp_id(n)
    triv = frozenset([e])
    subs = {triv}
    fr = [triv]
    while fr:
        nf = []
        for K in fr:
            for g in G:
                if g in K:
                    continue
                J = frozenset(gen_group(list(K) + [g], n))
                if J not in subs:
                    subs.add(J)
                    nf.append(J)
        fr = nf
    return subs


def sp_order(g, n):
    e = sp_id(n)
    k, x = 1, g
    while x != e:
        x = sp_mul(g, x)
        k += 1
    return k


def sp_inv(g):
    out = [None] * len(g)
    for i, (t, s) in enumerate(g):
        out[t] = (i, s)
    return tuple(out)


def matrix(g, n):
    M = [[0] * n for _ in range(n)]
    for i, (t, s) in enumerate(g):
        M[t][i] = s
    return M


# ----------------------------------------------------------------- arrangements and cones


def norm_key(v):
    g = 0
    for x in v:
        g = gcd(g, abs(x))
    v = tuple(x // g for x in v)
    s = 1
    for x in v:
        if x:
            s = 1 if x > 0 else -1
            break
    return tuple(s * x for x in v), s


class Arr:
    def __init__(self, normals, box):
        self.normals = [tuple(v) for v in normals]
        self.n = len(normals[0])
        self.key = {}
        for i, v in enumerate(self.normals):
            k, s = norm_key(v)
            self.key[k] = (i, s)
        self.L_basis = nullspace_q(self.normals, self.n)
        self.rank = self.n - len(self.L_basis)
        faces = set()
        for x in itertools.product(box, repeat=self.n):
            faces.add(self.sign(x))
        self.faces = faces
        self.zero = tuple([0] * len(self.normals))
        # Euler characteristic certificate: faces != O on S^{rank-1}
        chi = sum((-1) ** (self.fdim(f) - 1) for f in faces if f != self.zero)
        assert chi == 1 + (-1) ** (self.rank - 1), ("face sampling incomplete", chi)

    def sign(self, x):
        out = []
        for v in self.normals:
            t = sum(a * b for a, b in zip(v, x))
            out.append((t > 0) - (t < 0))
        return tuple(out)

    def fdim(self, f):
        """dim span F modulo L."""
        Z = [self.normals[i] for i, s in enumerate(f) if s == 0]
        return (self.n - (rank_q(Z) if Z else 0)) - (self.n - self.rank)

    def hperm(self, g):
        """Signed permutation of hyperplanes: (g sigma)(h') = eps_{h'} sigma(pi(h'))."""
        out = []
        for v in self.normals:
            w = [0] * self.n
            for i, (t, s) in enumerate(g):  # (M^T v)_i = s_i v_{t_i}
                w[i] = s * v[t]
            k, s1 = norm_key(w)
            j, s2 = self.key[k]  # KeyError if g does not preserve A
            out.append((j, s1 * s2))
        return tuple(out)

    def fixdim(self, H):
        """dim Fix(H) on R^n / L."""
        rows = []
        for h in H:
            M = matrix(h, self.n)
            for i in range(self.n):
                rows.append([M[i][j] - (1 if i == j else 0) for j in range(self.n)])
        amb = self.n - rank_q(rows) if rows else self.n
        onL = self.n - rank_q(rows + [list(v) for v in self.normals])
        return amb - onL


def act_face(hp, f):
    return tuple(e * f[j] for (j, e) in hp)


def act_zset(hp, z):
    return frozenset(i for i, (j, e) in enumerate(hp) if j in z)


def le_face(f, c):
    return all(a == 0 or a == b for a, b in zip(f, c))


class Cone:
    def __init__(self, arr, chambers):
        self.A = arr
        self.chambers = set(chambers)
        self.faces = {f for f in arr.faces if any(le_face(f, c) for c in self.chambers)}
        m = len(arr.normals)
        full = frozenset(range(m))
        zs = {frozenset(i for i in range(m) if f[i] == 0) for f in self.faces}
        self.flats_all = zs
        self.flats = [z for z in zs if z and z != full]
        # pointed iff the hyperplanes with V on one side cut out L(A)
        c0 = next(iter(self.chambers))
        smax = [i for i in range(m) if all(c[i] == c0[i] for c in self.chambers)]
        r = rank_q([arr.normals[i] for i in smax]) if smax else 0
        self.pointed = (r == arr.rank)
        self.d = arr.rank

    def stable_under(self, hp):
        return {act_face(hp, c) for c in self.chambers} == self.chambers


def flat_lt(a, b):
    return a > b  # zero set a strictly contains zero set b  <=>  flat a < flat b


def face_lt(f, g):
    return f != g and le_face(f, g)


# ----------------------------------------------------------------- analysis


def conj_class_reps(G, n):
    G = list(G)
    seen = set()
    reps = []
    for g in G:
        if g in seen:
            continue
        cl = {sp_mul(sp_mul(x, g), sp_inv(x)) for x in G}
        seen |= cl
        reps.append(g)
    return reps


def is_prime_power(k):
    if k < 2:
        return None
    for p in range(2, k + 1):
        if k % p == 0:
            q = k
            while q % p == 0:
                q //= p
            return p if q == 1 else None


def top_freeness(cone, Ghp_pairs, n):
    """For H = 1: H_{d-2}(T) is the top cycle group.  For each class rep g of prime-power
    order p^k, compare dim ker(g - 1) on Z_{d-2}(T; F_p) with dim / p^k."""
    ch, _ = chains(cone.flats, flat_lt)
    S = set(ch)
    top = cone.d - 2
    by = {}
    for s in S:
        by.setdefault(len(s) - 1, []).append(s)
    by[-1] = [()]
    if top not in by:
        return []
    idx_low = {s: i for i, s in enumerate(by[top - 1])}
    res = []
    for (g, hp, order) in Ghp_pairs:
        p = is_prime_power(order)
        if p is None:
            continue
        # sanity: rank of the boundary mod p equals rank mod a large prime
        rows_all = boundary_rows(by[top], idx_low)
        rp = sparse_rank(rows_all, p)
        rQ = sparse_rank(rows_all, 1000003)
        dimZ = len(by[top]) - rp
        # orbit sums of g on top simplices
        def img(s):
            return tuple(sorted((act_zset(hp, z) for z in s), key=lambda z: -len(z)))
        orbits = []
        seen = set()
        for s in by[top]:
            if s in seen:
                continue
            orb = [s]
            seen.add(s)
            t = img(s)
            while t != s:
                orb.append(t)
                seen.add(t)
                t = img(t)
            orbits.append(orb)
        rows = []
        for orb in orbits:
            r = {}
            for s in orb:
                for c, v in boundary_rows([s], idx_low)[0].items():
                    r[c] = r.get(c, 0) + v
            rows.append(r)
        fixed = len(orbits) - sparse_rank(rows, p)
        res.append((order, p, dimZ, fixed, rp == rQ, fixed * order == dimZ))
    return res


def singular_set_betti(cone, G_hp, p=1000003):
    """Homology of T_s = union of T^H over H != 1 (chains with nontrivial stabilizer)."""
    ch, _ = chains(cone.flats, flat_lt)
    nontriv = [hp for hp in G_hp if any(j != i or e != 1 for i, (j, e) in enumerate(hp))]
    S = set()
    for s in ch:
        if any(all(act_zset(hp, z) == z for z in s) for hp in nontriv):
            S.add(s)
    if not S:
        return None
    return [reduced_betti_complex(S, q) for q in (2, 3, p)]


def analyse(cone, G, n, check_E, want_lemmaF=False, want_free=True, want_sing=True,
            h1_limit=None):
    """Returns dict of results over all subgroups H of G."""
    A = cone.A
    hp_of = {g: A.hperm(g) for g in G}
    for g in G:
        assert cone.stable_under(hp_of[g]), "group does not preserve V"
    subs = subgroups(G, n)
    out = {"subs": len(subs), "E_ok": 0, "E_fail": 0, "S_ok": 0, "S_fail": 0, "empty": 0,
           "Hne1": 0, "core1": 0, "rows": [], "free": None, "sing": None, "lemF": None,
           "fixes_chamber": 0}
    nV = len(cone.chambers)
    for H in sorted(subs, key=len):
        hps = [hp_of[h] for h in H]
        elems = [z for z in cone.flats if all(act_zset(hp, z) == z for hp in hps)]
        mH = sum(1 for c in cone.chambers if all(act_face(hp, c) == c for hp in hps))
        eH = A.fixdim(H)
        if len(H) == 1 and h1_limit is not None and nV > h1_limit:
            out["rows"].append((1, mH, eH, None))
            continue
        b, same = poset_betti_all(elems, flat_lt)
        if len(H) > 1:
            out["Hne1"] += 1
            if mH:
                out["fixes_chamber"] += 1
        if not elems:
            out["empty"] += 1
        predS = {eH - 2: mH} if mH else {}
        okS = same and b == predS
        out["S_ok" if okS else "S_fail"] += 1
        if check_E:
            predE = {cone.d - 2: nV} if len(H) == 1 else {}
            okE = same and b == predE
            core = None
            if len(H) > 1 and elems:
                core = stong_core(elems, flat_lt)
                if core == 1:
                    out["core1"] += 1
                else:
                    okE = False
            out["E_ok" if okE else "E_fail"] += 1
        out["rows"].append((len(H), mH, eH, b))
    if want_free:
        reps = conj_class_reps(G, n)
        pairs = [(g, hp_of[g], sp_order(g, n)) for g in reps if sp_order(g, n) > 1]
        if h1_limit is None or nV <= h1_limit:
            out["free"] = top_freeness(cone, pairs, n)
    if want_sing and len(G) > 1 and (h1_limit is None or nV <= h1_limit):
        out["sing"] = singular_set_betti(cone, list(hp_of.values()))
    if want_lemmaF:
        out["lemF"] = lemma_F(cone, subs, hp_of)
    return out


def lemma_F(cone, subs, hp_of):
    """(a)-(b): H-stable faces of A == sign vectors of points of Fix(H) (sampled);
    (c): F(Y)^H has Stong core 1 for each H-stable Y in Lambda(V), Y != 0."""
    A = cone.A
    n = A.n
    full = frozenset(range(len(A.normals)))
    nb, nc, bad = 0, 0, []
    for H in subs:
        hps = [hp_of[h] for h in H]
        stable = {f for f in A.faces if all(act_face(hp, f) == f for hp in hps)}
        rows = []
        for h in H:
            M = matrix(h, n)
            for i in range(n):
                rows.append([M[i][j] - (1 if i == j else 0) for j in range(n)])
        U = nullspace_q(rows, n) if rows else [[int(i == j) for j in range(n)] for i in range(n)]
        k = len(U)
        rng = range(-k - 1, k + 2) if k <= 3 else range(-2, 3)
        sampled = set()
        for coeffs in itertools.product(rng, repeat=k):
            x = [sum(c * u[i] for c, u in zip(coeffs, U)) for i in range(n)]
            sampled.add(A.sign(x))
        # Euler certificate on S(U / (U cap L))
        Zs = A.zero
        e_rel = A.fixdim(H)
        def fd(f):
            Z = [A.normals[i] for i, s in enumerate(f) if s == 0]
            sp = nullspace_q(Z, n) if Z else [[int(i == j) for j in range(n)] for i in range(n)]
            # dim (span F cap U) - dim (L cap U)
            r1 = rank_q([[*v] for v in sp] + [[*u] for u in U]) if U else len(sp)
            dspanU = len(sp) + len(U) - r1
            return dspanU
        minf = A.zero
        dmin = fd(minf)
        chi = sum((-1) ** (fd(f) - dmin - 1) for f in sampled if f != minf)
        complete = (chi == 1 + (-1) ** (e_rel - 1))
        nb += 1
        if not (complete and sampled == stable):
            bad.append(("ab", len(H), len(sampled), len(stable), complete))
        # (c)
        for Y in cone.flats_all:
            if Y == full:
                continue  # Y = 0
            if not all(act_zset(hp, Y) == Y for hp in hps):
                continue
            # faces F != O of V with F in Y, H-stable  (F in Y  <=>  zero set of F contains Y's)
            P = [f for f in cone.faces if f != A.zero and
                 all(f[i] == 0 for i in Y) and all(act_face(hp, f) == f for hp in hps)]
            nc += 1
            if stong_core(P, face_lt) != 1:
                bad.append(("c", len(H), sorted(Y)))
    return nb, nc, bad


# ----------------------------------------------------------------- concrete families


def braid(n):
    normals = []
    pairs = []
    for i in range(n):
        for j in range(i + 1, n):
            v = [0] * n
            v[j], v[i] = 1, -1
            normals.append(v)
            pairs.append((i, j))
    return Arr(normals, range(n)), pairs


def boolean(d):
    return Arr([[int(i == j) for j in range(d)] for i in range(d)], (-1, 0, 1))


def typeB(d):
    normals = [[int(i == j) for j in range(d)] for i in range(d)]
    for i in range(d):
        for j in range(i + 1, d):
            for s in (1, -1):
                v = [0] * d
                v[i], v[j] = 1, s
                normals.append(v)
    return Arr(normals, range(-d, d + 1))


def all_signed_perms(d):
    out = []
    for p in itertools.permutations(range(d)):
        for s in itertools.product((1, -1), repeat=d):
            out.append(tuple((p[i], s[i]) for i in range(d)))
    return out


def perm_sp(p):
    return tuple((p[i], 1) for i in range(len(p)))


# posets: down-closure bitmasks; naturally labelled (i <_P j => i < j)


def naturally_labelled_posets(n):
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    out = []
    for mask in range(1 << len(pairs)):
        R = {pairs[k] for k in range(len(pairs)) if mask >> k & 1}
        if all((i, l) in R for (i, j) in R for (jj, l) in R if j == jj):
            out.append(frozenset(R))
    return out


def canon(R, n, perms):
    best = None
    for p in perms:
        key = tuple(sorted((p[i], p[j]) for (i, j) in R))
        if best is None or key < best:
            best = key
    return best


def posets_up_to_iso(n):
    perms = list(itertools.permutations(range(n)))
    seen = {}
    for R in naturally_labelled_posets(n):
        inv = (len(R), tuple(sorted(sum(1 for (i, j) in R if j == k) for k in range(n))),
               tuple(sorted(sum(1 for (i, j) in R if i == k) for k in range(n))))
        seen.setdefault(inv, []).append(R)
    reps = []
    for inv, lst in seen.items():
        cl = set()
        for R in lst:
            c = canon(R, n, perms)
            if c not in cl:
                cl.add(c)
                reps.append(R)
    return reps


def is_connected(R, n):
    adj = {i: set() for i in range(n)}
    for (i, j) in R:
        adj[i].add(j)
        adj[j].add(i)
    seen, st = {0}, [0]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                st.append(y)
    return len(seen) == n


def automorphisms(R, n):
    return [p for p in itertools.permutations(range(n))
            if {(p[i], p[j]) for (i, j) in R} == R]


def anti_automorphisms(R, n):
    return [p for p in itertools.permutations(range(n))
            if {(p[j], p[i]) for (i, j) in R} == R]


def poset_cone(arr, pairs, R):
    pidx = {pr: k for k, pr in enumerate(pairs)}
    rel = [pidx[(i, j)] for (i, j) in R]
    ch = [f for f in arr.faces if 0 not in f and all(f[k] == 1 for k in rel)]
    return Cone(arr, ch)


def lin_count(R, n):
    return sum(1 for p in itertools.permutations(range(n))
               if all(p.index(i) < p.index(j) for (i, j) in R))


# ----------------------------------------------------------------- main


def main(nmax=6, quick=False):
    log = []
    allpass = True

    def rep(s):
        log.append(s)
        print(s, flush=True)

    # --- instrument controls
    S3 = gen_group([perm_sp((1, 0, 2)), perm_sp((1, 2, 0))], 3)
    S4 = gen_group([perm_sp((1, 0, 2, 3)), perm_sp((1, 2, 3, 0))], 4)
    B3 = gen_group(all_signed_perms(3), 3)
    cnt = (len(subgroups(S3, 3)), len(subgroups(S4, 4)), len(subgroups(B3, 3)))
    rep(f"[CTL] subgroup counts S3, S4, W(B3) = {cnt} (expected (6, 30, 98))")
    allpass &= cnt == (6, 30, 98)
    # circle, 2-sphere boundary, point
    circ = {(0,), (1,), (2,), (0, 1), (1, 2), (0, 2)}
    rep(f"[CTL] triangle boundary betti mod 2,3 = "
        f"{reduced_betti_complex(circ, 2)}, {reduced_betti_complex(circ, 3)} (expected {{1: 1}})")
    allpass &= reduced_betti_complex(circ, 2) == {1: 1}
    # RP^2 (6 vertices) torsion control: mod 2 sees it, mod 3 does not
    # standard minimal RP^2 triangulation
    tri = [(0, 1, 2), (0, 2, 3), (0, 3, 4), (0, 4, 5), (0, 1, 5), (1, 2, 4), (2, 3, 5),
           (1, 3, 4), (1, 3, 5), (2, 4, 5)]
    S = set()
    for t in tri:
        t = tuple(sorted(t))
        for r in range(1, 4):
            for c in itertools.combinations(t, r):
                S.add(c)
    rp2 = (reduced_betti_complex(S, 2), reduced_betti_complex(S, 3))
    rep(f"[CTL] RP^2 betti mod 2 = {rp2[0]}, mod 3 = {rp2[1]} (expected {{1: 1, 2: 1}}, {{}})")
    allpass &= rp2 == ({1: 1, 2: 1}, {})
    # Stong core: crown (4-cycle poset, S^1) must not reduce to a point
    crown = ["a", "b", "c", "d"]
    clt = lambda x, y: (x, y) in {("a", "c"), ("a", "d"), ("b", "c"), ("b", "d")}
    rep(f"[CTL] Stong core of the 4-crown = {stong_core(crown, clt)} (expected 4)")
    allpass &= stong_core(crown, clt) == 4

    # --- orthants (pointed, non-free): Theorem E must FAIL, Theorem S must hold
    for d, G in ((3, S3), (4, S4)):
        A = boolean(d)
        V = Cone(A, [tuple([1] * d)])
        res = analyse(V, G, d, check_E=True, want_lemmaF=(d == 3))
        rep(f"[NEG] orthant R^{d}, G=S_{d}: subgroups={res['subs']} empty T^H={res['empty']} "
            f"ThmE ok/fail={res['E_ok']}/{res['E_fail']} ThmS ok/fail={res['S_ok']}/{res['S_fail']} "
            f"free-test={[(o, p, z, f, ok) for (o, p, z, f, _, ok) in res['free']]}")
        allpass &= res["E_fail"] > 0 and res["S_fail"] == 0 and res["empty"] >= 1
        allpass &= any(not ok for (*_, ok) in res["free"])
        if res["lemF"]:
            nb, nc, bad = res["lemF"]
            rep(f"[LEMF] orthant R^3, S_3: (a)-(b) {nb} subgroups, (c) {nc} pairs, failures {bad}")
            allpass &= not bad
    # all 8 orthants of R^3 / 16 of R^4 with full stabilizer in W(B_d)
    for d in (3, 4):
        A = boolean(d)
        Bd = gen_group(all_signed_perms(d), d)
        tot = [0, 0, 0]
        for c in itertools.product((1, -1), repeat=d):
            V = Cone(A, [c])
            hp = {g: A.hperm(g) for g in Bd}
            stab = [g for g in Bd if V.stable_under(hp[g])]
            r = analyse(V, stab, d, check_E=False, want_free=False, want_sing=False)
            tot[0] += r["S_ok"]
            tot[1] += r["S_fail"]
            tot[2] += r["empty"]
        rep(f"[GEN] Boolean R^{d}, all orthants, full stabilizers: (S1) ok/fail = {tot[0]}/{tot[1]}, "
            f"T^H empty on {tot[2]}")
        allpass &= tot[1] == 0

    # --- B_3: every top-cone, stabilizer in W(B_3)
    A = typeB(3)
    chambers = [f for f in A.faces if 0 not in f]
    assert len(chambers) == 48
    cones = set()
    m = len(A.normals)
    for part in itertools.product((None, 1, -1), repeat=m):
        V = frozenset(c for c in chambers if all(s is None or c[i] == s for i, s in enumerate(part)))
        if V:
            cones.add(V)
    hpB = {g: A.hperm(g) for g in B3}
    stats = dict(cones=len(cones), pointed_nontriv=0, pairs=0, E_ok=0, E_fail=0, S_fail=0,
                 nonfree=0, free_fail=0, sing_bad=0, lem_bad=0)
    for Vs in sorted(cones, key=lambda s: (len(s), sorted(s))):
        V = Cone(A, Vs)
        if not V.pointed:
            continue
        stab = [g for g in B3 if V.stable_under(hpB[g])]
        if len(stab) == 1:
            continue
        stats["pointed_nontriv"] += 1
        r = analyse(V, stab, 3, check_E=True, want_lemmaF=not quick)
        stats["pairs"] += r["Hne1"]
        stats["E_ok"] += r["E_ok"]
        stats["E_fail"] += r["E_fail"]
        stats["S_fail"] += r["S_fail"]
        stats["free_fail"] += sum(1 for x in r["free"] if not (x[4] and x[5]))
        if r["sing"] and any(b for b in r["sing"]):
            stats["sing_bad"] += 1
        if r["lemF"]:
            stats["lem_bad"] += len(r["lemF"][2])
    rep(f"[GEN] B_3: {stats}")
    if not quick:
        nb = nc = 0
        badF = []
        for Vs in cones:
            V = Cone(A, Vs)
            if not V.pointed:
                continue
            stab = [g for g in B3 if V.stable_under(hpB[g])]
            a, b, c = lemma_F(V, subgroups(stab, 3), {g: hpB[g] for g in stab})
            nb, nc, badF = nb + a, nc + b, badF + c
        rep(f"[LEMF] B_3, every pointed cone, every subgroup of its stabilizer: (a)-(b) on {nb} "
            f"(cone, H) pairs, (c) on {nc} (cone, H, Y) triples, failures {len(badF)}")
        allpass &= not badF
        # positive control: a half-space (not pointed) must violate (c)
        V = Cone(A, [c for c in chambers if c[0] == 1])
        stab = [g for g in B3 if V.stable_under(hpB[g])]
        badH = lemma_F(V, subgroups(stab, 3), {g: hpB[g] for g in stab})[2]
        rep(f"[LEMF] control: half-space x_1 >= 0 (pointed={V.pointed}) violates (c) on "
            f"{sum(1 for b in badH if b[0] == 'c')} triples (must be > 0)")
        allpass &= (not V.pointed) and any(b[0] == "c" for b in badH)
    allpass &= stats["E_fail"] == 0 and stats["S_fail"] == 0 and stats["free_fail"] == 0
    allpass &= stats["sing_bad"] == 0 and stats["lem_bad"] == 0

    # --- non-pointed controls: Theorem E must FAIL
    A4, pairs4 = braid(4)
    allc = [f for f in A4.faces if 0 not in f]
    V = Cone(A4, allc)
    r = analyse(V, S4, 4, check_E=True, want_free=True, want_sing=False)
    bad = [(row[0], row[3]) for row in r["rows"] if row[0] > 1 and row[3]]
    rep(f"[NEG] Pi-bar_4 (all chambers of A_3), G=S_4: pointed={V.pointed} #V={len(V.chambers)} "
        f"H=1 betti={r['rows'][0][3]} ThmE ok/fail={r['E_ok']}/{r['E_fail']}; "
        f"H!=1 not acyclic: {len(bad)}, e.g. {bad[:2]}")
    allpass &= (not V.pointed) and r["E_fail"] > 0
    R2 = frozenset({(0, 1), (2, 3)})
    V = poset_cone(A4, pairs4, R2)
    G = gen_group([perm_sp((2, 3, 0, 1))], 4)
    r = analyse(V, G, 4, check_E=True, want_free=True, want_sing=False)
    rep(f"[NEG] two 2-chains, swap: pointed={V.pointed} #V={len(V.chambers)} rows={r['rows']} "
        f"ThmE ok/fail={r['E_ok']}/{r['E_fail']} free-test={r['free']}")
    allpass &= (not V.pointed) and r["E_fail"] > 0

    # --- type A: connected posets, G = Aut P (free), and self-dual ones with -alpha (non-free)
    tot = dict(posets=0, pairs=0, Hne1=0, core1=0, E_fail=0, S_fail=0, h1_skipped=0,
               free_tests=0, free_fail=0, sing_bad=0, lemF_bad=0, lemF_pairs=0)
    nf = dict(cases=0, pairs=0, S_fail=0, E_fail_cases=0, fixes=0, empty=0)
    for n in range(3, nmax + 1):
        A, pairs = braid(n)
        reps = posets_up_to_iso(n)
        conn = [R for R in reps if is_connected(R, n)]
        nontriv = 0
        for R in sorted(conn, key=lambda R: sorted(R)):
            auts = automorphisms(R, n)
            antis = anti_automorphisms(R, n)
            V = poset_cone(A, pairs, R)
            assert V.pointed
            assert len(V.chambers) == lin_count(R, n)
            if len(auts) > 1:
                nontriv += 1
                G = gen_group([perm_sp(p) for p in auts], n)
                # free action on chambers
                hp = {g: A.hperm(g) for g in G}
                for g in G:
                    if g != sp_id(n):
                        assert all(act_face(hp[g], c) != c for c in V.chambers)
                lim = None if not quick else 40
                r = analyse(V, G, n, check_E=True, want_lemmaF=(n <= 5 and not quick),
                            h1_limit=lim)
                tot["posets"] += 1
                tot["pairs"] += len(r["rows"])
                tot["Hne1"] += r["Hne1"]
                tot["core1"] += r["core1"]
                tot["E_fail"] += r["E_fail"]
                tot["S_fail"] += r["S_fail"]
                tot["h1_skipped"] += sum(1 for row in r["rows"] if row[3] is None)
                if r["free"] is not None:
                    tot["free_tests"] += len(r["free"])
                    tot["free_fail"] += sum(1 for x in r["free"] if not (x[4] and x[5]))
                if r["sing"] and any(b for b in r["sing"]):
                    tot["sing_bad"] += 1
                if r["lemF"]:
                    tot["lemF_pairs"] += r["lemF"][0] + r["lemF"][1]
                    tot["lemF_bad"] += len(r["lemF"][2])
            if antis and n <= nmax:
                # non-free: G = < Aut P, -alpha >
                a = antis[0]
                minus = tuple((a[i], -1) for i in range(n))
                G = gen_group([perm_sp(p) for p in auts] + [minus], n)
                hp = {g: A.hperm(g) for g in G}
                fixes = any(g != sp_id(n) and any(act_face(hp[g], c) == c for c in V.chambers)
                            for g in G)
                if not fixes:
                    continue
                r = analyse(V, G, n, check_E=True, want_free=False, want_sing=False,
                            h1_limit=(40 if quick else None))
                nf["cases"] += 1
                nf["pairs"] += len(r["rows"])
                nf["S_fail"] += r["S_fail"]
                nf["E_fail_cases"] += int(r["E_fail"] > 0)
                nf["fixes"] += r["fixes_chamber"]
                nf["empty"] += r["empty"]
        rep(f"[POS] n={n}: connected posets {len(conn)}, with |Aut|>1: {nontriv}")
    rep(f"[POS] free (G = Aut P): {tot}")
    rep(f"[NONFREE] self-dual P, G = <Aut P, -alpha> with some g != 1 fixing a chamber: {nf}")
    allpass &= tot["E_fail"] == 0 and tot["S_fail"] == 0 and tot["free_fail"] == 0
    allpass &= tot["sing_bad"] == 0 and tot["lemF_bad"] == 0
    allpass &= nf["S_fail"] == 0 and nf["E_fail_cases"] == nf["cases"]
    rep(f"ALL AUDIT CHECKS PASS: {allpass}")
    return allpass


if __name__ == "__main__":
    nmax = 6
    quick = False
    args = sys.argv[1:]
    if "--nmax" in args:
        nmax = int(args[args.index("--nmax") + 1])
    if "--quick" in args:
        quick = True
    ok = main(nmax, quick)
    sys.exit(0 if ok else 1)

# Audit of h_double_prime.md: min-des realises h_C iff no class is all-ascent

This is an independent audit of `notes/h_double_prime.md` ([H″] below). I
re-derived every proof by hand. I also recomputed every claim with my own
script, `compute/audit_h_double_prime.py`. It imports nothing from the
repository and does not reuse the author's code. Bracketed labels refer to
lines of `compute/output/audit_h_double_prime.txt`.

Sources: [H] = `notes/h_vector_omega_c.md` (notation of §0, Proposition D,
Lemma 1, H′); [AudH] = `notes/audit_h_vector_omega_c.md`, which audited
those results.

## Verdict

| Claim of [H″] | Verdict |
|---|---|
| **L3** (a) 1 ≤ d ≤ n − s; (b) every member has des = d, so min-des = d; (c) for **every** component T, Σ_{w∈κ} N_T(w, m) = Σ_{i=0}^{s−1} C(M−i, n−i) = C(m+n−d, n) − C(m+n−d−s, n−s), where M = m+n−1−d | **HOLDS.** There is no T-dependence to manage: all δ_k = 0, so the cyclic re-indexing that puts T in c_s changes nothing (§1). The formula agrees with [AudH] §2. COMPUTED on 7595 all-ascent classes and 195 585 (class, T, m) cases with n ≤ 7, 0 failures |
| **F** h_C(x) = Σ_{κ not a.a.} x^{mindes κ} + Σ_{κ a.a.} x^{d_κ−1}(1 − (1−x)^{s_κ}), for any natural labelling and n ≥ 2 | **HOLDS.** The dictionary (i), (ii) and the x^{d−1} shift are correct (§2). One sentence needs a wording fix, which changes no statement (§5). COMPUTED against the Möbius definition on all 101 658 naturally labelled posets with 2 ≤ n ≤ 7, 0 failures |
| **M** f′(1) − h_C′(1) = A | **HOLDS** (§3). COMPUTED on 101 658, 0 failures |
| **L** h_{d_0} − f_{d_0} = Σ_{d_κ = d_0} (s_κ − 1) > 0, and f and h_C agree below d_0 | **HOLDS** (§3). s_κ ≥ 2 holds by the definition of all-ascent, and nothing else is needed (§4). COMPUTED on all 1080 labellings with A > 0, 0 failures |
| **H″** with H′: min-des realises h_C ⇔ A = 0 | **HOLDS.** M alone gives ⇒; H′ (audited in [AudH]) or F with A = 0 gives ⇐. COMPUTED on 101 658 labellings, 1080 with A > 0 (2, 46, 1032 at n = 5, 6, 7) |
| Controls of [H″] (min-des on every labelling; F with (1−x)^{s−1}; F with x^d; M with right side 0) | **Refuted, as claimed**, with the same counts: 1080 of 101 658, 1080 of 1080, 1080 of 1080, 1080 of 101 658 |

**No claim FAILS.** One wording fix is recommended (§5). Nothing in it
affects a statement. Theorem H″ can be tagged PROVEN + audited.

## 1. Lemma 3

- **(a)** des(c_k) ≤ |c_k| − 1, so summing gives d ≤ n − s. Suppose d = 0.
  Then every piece is increasing, and every junction, including J_s, is an
  ascent. Reading c_1 ⋯ c_s cyclically gives w_1 < ⋯ < w_n < w_1, which is
  impossible. So d ≥ 1, and s ≤ n − d ≤ n − 1. Correct.
- **(b)** By [H] §0, the rotation broken at J_i has des = d + jd − δ_i = d.
  Correct.
- **(c)** *T-dependence.* Every component T lies inside a single piece
  ([H] §1, Step 3). Since the cyclic indexing of the pieces is arbitrary,
  we may index so that T ⊆ c_s. In [H] Lemma 1 this choice mattered,
  because the contributing rotations R_0, …, R_q are cut off at the first
  descent junction q after T's piece, and q depends on where T sits. Here
  every δ_k = 0. So the re-indexed class has the same junction data, all
  s rotations contribute for every T, and the right-hand side contains
  nothing that depends on T. The anchoring problem does not arise.

  *Rotation bookkeeping.* In R_i = c_{i+1} ⋯ c_s c_1 ⋯ c_i, the piece c_s
  sits at position s − i. The cuts after it are J_s, J_1, …, J_{i−1}, so
  |C_T(R_i)| = i, as in [AudH] §2. These cut positions are junctions, and
  every junction is an ascent, so C_T(R_i) ∩ Des(R_i) = ∅. By (b),
  des(R_i) = d. So N_T(R_i, m) = C(m + n − 1 − d − i, n − i) = C(M − i, n − i).
  This is the formula of [AudH] §2 with jd = 0: there
  M = m + n − 1 − d − jd. **The two agree.**

  *Telescoping.* C(M + 1 − i, n − i) − C(M − i, n − i) = C(M − i, n − i − 1).
  The (i + 1)-th term on the right is exactly the subtrahend
  C(M + 1 − (i + 1), n − (i + 1)). So
  Σ_{i=0}^{s−1} C(M − i, n − i) = C(M + 1, n) − C(M + 1 − s, n − s).
  Since M + 1 = m + n − d, this is the claimed closed form. Pascal's rule
  with lower index b ≥ 1 is a polynomial identity in the upper index, so
  the restriction a ≥ 0 in [H″] is not needed. Still, [H″]'s check that
  every top is ≥ m is correct, and it is what makes each N_T a genuine
  count at every m ≥ 0.

COMPUTED: `[aa-a]` and `[aa-b]` on 7595 all-ascent classes. `[aa-c]`
evaluates N_T straight from its definition in Proposition D (descent set,
C_T(w), binomial), for every component T and every m = 0, …, n + 1. It
compares the result both with the closed form and with the [AudH] sum
form, on 195 585 cases. The control `[ctl-aa-single]` asserts the
Lemma 1 shape C(m + n − 1 − d, n) for an all-ascent class, and it is
refuted on 113 675 of those cases.

## 2. Theorem F: the binomial-to-h-vector conversion

Write H(p) for the h-polynomial of p, defined by
Σ_{m≥0} p(m) x^m = x·H(p)(x)/(1 − x)^{n+1}.

- **(i)** Let 0 ≤ j ≤ n − 1. For m ≤ j, the top m + n − 1 − j of
  C(m + n − 1 − j, n) lies in [0, n − 1], so the value is 0. For m = j + 1 + u
  the value is C(u + n, n), and Σ_u C(u + n, n) x^u = (1 − x)^{−(n+1)}. So
  H = x^j. With j = d − 1, which lies in [0, n − 3] by L3(a), this gives the
  x^{d−1} of the C(m + n − d, n) term.
- **(ii)** Let k = n − s. Then 1 ≤ d ≤ k by L3(a). For m ≤ d − 1 the top
  m + k − d lies in [k − d, k − 1] ⊆ [0, k − 1], so q(m) = 0. For m = d + u,
  q = C(u + k, k). So Σ_m q x^m = x^d (1 − x)^{−(k+1)} = x·x^{d−1}(1 − x)^s / (1 − x)^{n+1},
  and H = x^{d−1}(1 − x)^s.

The h-polynomial of an all-ascent class is therefore
x^{d−1} − x^{d−1}(1 − x)^s = x^{d−1}(1 − (1 − x)^s). For s = 2 this is
2x^d − x^{d+1}. Both pieces of the conversion matter. The shift is x^{d−1}
because the top in C(m + n − d, n) is one more than the top m + n − 1 − d of
a single-binomial class. The exponent is s because the second binomial
drops by s in both its top and its bottom. The false variants confirm
this: `[ctl-F-s1]` ((1 − x)^{s−1}) and `[ctl-F-d]` (x^d) are each refuted
on 1080 of 1080 labellings with A > 0.

*Assembly.* Proposition D holds for every m ≥ 1 ([AudH] §1), and both sides are polynomials in m. Each
per-class identity, Lemma 1 for a class that is not all-ascent and L3(c)
for one that is, holds at every integer m ≥ 0. H is linear, and h_C is the
unique H with H(Ω_C) = h_C ([AudH] §3: the basis argument). So F follows.

COMPUTED `[F]`: h_C comes from the Möbius definition on OP(P). My code
builds OP(P) by filtering set partitions for an acyclic quotient, computes
μ(π, 1̂) by recursion over the coarsenings, evaluates Ω_C at m = 0, …, n + 1,
and checks that the x^{n+1}-coefficient of (1 − x)^{n+1} Σ Ω_C(m) x^m
vanishes. It is cached per isomorphism class (2, 5, 16, 63, 318, 2045
classes for n = 2, …, 7). F was then compared with this h_C on all
101 658 naturally labelled posets with 2 ≤ n ≤ 7, with 0 failures.

## 3. Corollaries M and L

f − h_C = Σ_{a.a.} g_κ with g_κ = x^{d−1}[x − 1 + (1 − x)^s] = −(1 − x)u_κ and
u_κ = x^{d−1}(1 − (1 − x)^{s−1}). This uses L3(b) (f gives x^d to the class)
and the fact that classes that are not all-ascent cancel term by term.

- **M.** g_κ(1) = 0, and g_κ′(1) = u_κ(1) = 1 − 0^{s−1} = 1 for s ≥ 2. So
  f′(1) − h_C′(1) = A. Correct.
- **L.** 1 − (1 − x)^{s−1} = (s − 1)x + O(x²), so
  g_κ = −(s − 1)x^{d_κ} + O(x^{d_κ+1}). Classes with d_κ > d_0 do not reach
  degree d_0. So h − f vanishes below d_0, and its x^{d_0}-coefficient is
  Σ_{d_κ=d_0} (s_κ − 1) ≥ 1. Correct.
- **H″.** If A > 0, then f′(1) ≠ h_C′(1), so f ≠ h_C. If A = 0, then F
  reduces to f = h_C, which is H′. Correct.

COMPUTED: `[M]` on 101 658 labellings; `[L] agree below d0` and
`[L] h_d0 - f_d0 = sum (s-1) > 0` on all 1080 labellings with A > 0;
`[iff]` on 101 658. The control `[ctl-L-s]` (Σ s_κ in place of
Σ (s_κ − 1)) is refuted on 1080 of 1080.

## 4. Does L need s_κ ≥ 2, and can an all-ascent class have s = 1?

By [H] §0, an all-ascent class has s ≥ 2 **by definition**: for s = 1
there are no junctions, jd is set to 0, and such a class is treated by the
s = 1 case of Lemma 1. So no all-ascent class has s = 1, and L and M get
s ≥ 2 for free.

The definition is consistent with F. Suppose a class with s = 1 were
admitted as "all-ascent". Its F-term would be x^{d−1}(1 − (1 − x)) = x^d,
which is the same as its Lemma 1 term x^{mindes}, so F would not change.
But its g_κ would be 0, so it would add 1 to A without moving f′(1).
**M and the count A therefore depend on the s ≥ 2 convention, and that
convention is the correct one.** The computation shows that the
distinction is real. Among the 13 067 323 classes with s = 1 for n ≤ 7,
none enters A. The all-ascent classes have s = 2 (7458), s = 3 (135) and
s = 4 (2).

## 5. Recommended wording fix

- **§2 of [H″], after the proof of F.** The note says "When A > 0 the
  right-hand side has negative coefficients". Read literally, this is
  false. The right-hand side equals h_C(P), and h_C(P) ≥ 0 by Theorem H.
  What is negative is the contribution of each single all-ascent class:
  its x^{d+1}-coefficient is −C(s, 2) < 0. Other classes can and do cancel
  this in the sum. Suggested text: "When A > 0, each all-ascent term has a
  negative coefficient (for s = 2 it is 2x^d − x^{d+1}). So Theorem F is a
  signed formula, not a combinatorial interpretation."
- **Minor.** In §1, the restriction "a ≥ 0" on Pascal's rule is not
  needed (§1 above). It is harmless.
- **Status elsewhere.** [H] still lists H″ as OPEN in its table and in
  §2.4 and §4. That should be updated when this audit is folded in. I
  have not edited [H].

## 6. Computation and scope

`compute/audit_h_double_prime.py` does not enumerate isomorphism classes
and then relabel them. It generates the **naturally labelled posets
directly**: element n − 1 is maximal, so each naturally labelled poset on
[n] arises exactly once by adding n − 1 over a down-set of a naturally
labelled poset on [n − 1]. This gives 2, 7, 40, 357, 4824, 96 428 for
n = 2, …, 7 (OEIS A006455). The total of 101 658 matches [H″], and the
n ≤ 6 total of 5230 matches [H]. A brute-force canonical form groups these
posets into 2, 5, 16, 63, 318, 2045 isomorphism classes for the Möbius
cache.

For each labelled poset the script does the following.
- *Classes.* It computes Lin P and builds each class as wC_n ∩ Lin P. It
  asserts that this equals the set of cut rotations, and that |κ| = s
  (`[class = orbit cap Lin = cut rotations]`, 14 676 790 classes).
- *Statistics.* min-des is computed as an actual minimum over the class.
  All-ascent means s ≥ 2 and every junction (including the wrap-around
  junction) is an ascent.
- *End-to-end check.* For every labelling with A > 0, `[D-e2e]` checks
  Σ_{w∈Lin P} N_T(w, m) = Ω_C(m) from Möbius, for every T and every
  m ≤ n + 1 (24 935 cases).
- *Instrument check on the Möbius side.* For connected P, des on Lin P must
  equal h_C (Stanley; 65 955 cases). For disconnected P it must not
  (`[ctl-lin]`, refuted on 35 703 of 35 703).

All claim lines PASS, all seven CONTROL lines are refuted, and the script
exits 0 (228 s on one core).

*n = 8 was not run.* There are 2 800 472 naturally labelled posets at
n = 8, a count measured by the same generator (A006455). The run would
take well over an hour at the measured n = 7 rate, against a 25-minute
bound. So the computation is COMPUTED up to n = 7 only. The proofs cover
every n. [H″] §5 estimates "roughly 2·10⁶"; the exact figure is
2 800 472.

## Reproduce

From `compute/` (Python 3, no dependencies, one core, about 4 minutes):

    timeout 1500 python3 audit_h_double_prime.py --nmax 7 > output/audit_h_double_prime.txt

`--nmax 6` takes about 4 s. The script exits with status 0 iff every claim
line holds and every CONTROL line is refuted at least once.

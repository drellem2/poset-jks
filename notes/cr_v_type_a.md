# CR_V on type A: the Crapo converse holds on every cone of the braid arrangement

Conjecture CR_V (`notes/per_cone_vanishing.md` = "[PCV]", §4) says:

  χ_V(g) = 0  iff  Λ(V)^g has an element without a complement.

It is refuted in rank 4 for general arrangements (`notes/conjecture_cr_v.md` =
"[CRV]", §0; audit `notes/audit_conjecture_cr_v.md`: REFUTATION HOLDS). [CRV] §6
left the braid arrangement OPEN. That is the case the poset program needs.

**Answer: CR_V holds on every cone of the braid arrangement** (Theorem TA-CR
below). Every zero comes with an explicit uncomplemented element, in six cases.
In five of them the element is cl(Fix g^k) for an explicit k: an orbit
partition of a power of the permutation, or the partition cl(Fix g). In the
sixth case ((TA4)) it is the element already found in [PCV] §3.6.

In poset language: let P be a finite poset on [n], n ≥ 3, and let
g = ετ ∈ ±S_n with g C_P = C_P. Put M = OP(P)^τ, the τ-stable partitions of [n]
with acyclic quotient. Then μ(M) = 0 iff some τ-stable acyclic partition has no
complement in M. The zero set is the one of [Thm, eq. closed] (for +w) and of
[PCV] Theorem TA (for −τ). The proof of the converse is new and uses neither
formula. It rests on two facts:
- every complement of an element below cl(Fix g) is coarser than the
  component partition of P (Lemma K_A);
- for orbit partitions, complementation is a gcd condition on cycle lengths
  (Lemma C).

Tags:
- **PROVEN**: proof given here, with inputs named. Independently audited in
  `notes/audit_cr_v_type_a.md` ("[AudCVA]", mg-73141): Theorem TA-CR,
  Lemma K_A, Lemma C and steps S0, S2, S4, S5 HOLD; the one FIXABLE remark
  (§3, *Remarks*, 2nd bullet) has been corrected. The steps are numbered
  S1–S6 in §1, and every later proof cites them by number.
- **COMPUTED**: by `compute/cr_v_type_a.py` ("[CVA]"). This is new code that
  imports nothing from the other scripts.
- **CITED**: from an audited note or the literature.
- **OPEN**.

## Verdict

| # | Claim | Status | Inputs |
|---|---|---|---|
| TA-CR | **Theorem TA-CR.** For every poset P on [n], n ≥ 3, and every finite-order linear g with gA_{n−1} = A_{n−1} and g C_P = C_P: χ_{C_P}(g) = 0 iff OP(P)^g has an uncomplemented element. The element is explicit (§3, table W) | **PROVEN** (§3). COMPUTED: exhaustive for n ≤ 7 up to isomorphism, with 0 failures. That is 6,154 pairs, 3,519 zeros, and every zero's witness checked uncomplemented. Also 13 targeted pairs with n = 8, 9, 18 | S1–S6, Lemma C; "only if" of the nonvanishing criteria CITED ([Thm], [PCV] TA) |
| Z | **The zeros, in poset language.** For g = +w (w ∈ Aut P): χ = 0 iff ord(w) is not squarefree or ⟨w⟩ does not act freely on the components of P. For g = −τ (τ an anti-automorphism): χ = 0 iff one of (TA1)–(TA4) fails | **CITED** ([Thm, eq. closed], audited; [PCV] Theorem TA, audited). The vanishing half is re-proven here by Crapo plus the witnesses. COMPUTED: the zero pattern of μ(OP(P)^τ) matches on all 6,154 pairs with n ≤ 7, with 0 mismatches | — |
| S0 | Every finite-order linear symmetry of A_{n−1} (n ≥ 3) is ±π with π ∈ S_n. It preserves C_P iff π ∈ Aut(P) (sign +) or π is an anti-automorphism (sign −) | **PROVEN** modulo Whitney's theorem (CITED) (§1) | Whitney 1933 |
| F_A | For h ∈ ⟨g⟩, cl(Fix h) ∈ OP(P)^τ, and every block of cl(Fix h) is an antichain of P | **PROVEN** (§1, S4) | — |
| K_A | **Lemma K_A.** If w ∈ M refines c = cl(Fix g), then every complement x of w in M is coarser than the component partition κ of P, and x ∨_M w is the partition join | **PROVEN** (§1, S5). This is the poset form of Lemma K of [CRV]. COMPUTED: every complement of every cl(Fix g^k), on every pair with n ≤ 7, is ≥ κ (0 failures) | S2, S4 |
| C | **Lemma C** (cyclic actions). Let w be the orbit partition of ⟨σ^h⟩. A σ-stable x ≥ κ with x ∧ w = 0̂ and x ∨ w = 1̂ exists iff some s satisfies gcd(s, h) = 1, s divides the orbit length of every component, and ℓ/gcd(ℓ, h) = s for every cycle length ℓ of σ | **PROVEN** (§2). COMPUTED: matches the lattice on all 4,764 orbit-partition checks with n ≤ 7. 48 of them are complemented and 4,716 are not | — |
| Ty | Every zero is a "fixed-space" zero, except (TA4). The witness is cl(Fix g^k) for some k ≥ 1 in cases W+1, W+2, W−1, W−2, W−3. In case W−4 it is an element coarser than κ ("inside L"). cl(Fix g) itself is complemented on 93 zero pairs with n ≤ 7 (79 W−4, 13 W−1, 1 W+2), so the exponent k matters | **PROVEN** (§3); count COMPUTED | — |
| Rk | Status changes: [CRV] §6 "Type A: OPEN" is settled here; [PCV] row CR_V becomes a theorem on type A; the [PCV] count "5,063 lattices" is not reconciled with its archived log (§5) | applied to [CRV] and [PCV] after the audit; [AudCVA] §5 confirms 3,576 and finds 5,063 unsupported | — |
| PA | Prior art ([PACVA] = `notes/prior_art_cr_v_type_a.md`) | "if" of TA-CR: KNOWN (Crapo 1966, Thm 3; EC1 Ex. 3.92). "Only if": NOT FOUND in the sources searched for any class containing OP(P)^τ (a search result, not a claim of novelty); for the antichain with g = +w it is KNOWN in substance (Stanley 1982, Remark after Lemma 7.1; Hanlon 1981, Lemma 2; EC1 Cor. 3.9.5), plus one elementary step. Lemma C: PARTLY KNOWN (h = 1, κ = 0̂ existence is Hanlon 1981, Lemma 6); the gcd criterion for σ^h and the κ-relative form NOT FOUND. Lemma K_A: NOT FOUND | CITED |

**In one line.** On the braid arrangement the Crapo converse is a theorem. Each
zero of χ_{C_P}(±τ) is witnessed by an orbit partition of a power of τ, by
cl(Fix g), or by the (TA4) element. Complementation of orbit partitions reduces
to a gcd condition, because every complement of an element below cl(Fix g)
must be a union of components (a fixed-point averaging argument). The rank-4
counterexample of [CRV] §0 therefore has no type-A analogue.

---

## 1. Setting and the shared steps S0–S5

Let P be a poset on [n], n ≥ 3. Let A = A_{n−1} = {x_i = x_j} in R^n_0 (rank
d = n − 1), and let C_P = {x ∈ R^n_0 : x_i ≤ x_j for i <_P j}, the top-cone of P
([GT] §0, [FP]).

**S0 (symmetries; PROVEN modulo Whitney).** Let g be a linear map of R^n_0 of
finite order with gA = A. Then g = ετ with ε = ±1 and τ ∈ S_n, acting by
(gx)_{τ(i)} = ε x_i.
- g permutes the hyperplanes and preserves their intersection lattice. So the
  induced permutation of the edges of K_n is an automorphism of the cycle
  matroid M(K_n).
- For n = 3 every permutation of the three edges is induced by a vertex
  permutation. For n ≥ 4, K_n is 3-connected, and Whitney's 2-isomorphism
  theorem (CITED: Whitney, *2-isomorphic graphs*, Amer. J. Math. 55 (1933))
  gives a vertex permutation τ inducing it.
- Then g' = g ∘ τ^{−1} fixes every hyperplane. Its transpose fixes every line
  R(e_i − e_j) of the dual. From (e_1 − e_2) + (e_2 − e_3) = e_1 − e_3 and the
  connectivity of K_n, all these eigenvalues are equal. So g' is a real
  scalar of finite order, ±1.

g C_P = C_P iff τ ∈ Aut(P) (ε = +1) or τ is an anti-automorphism (ε = −1).
P is recovered from C_P: for i ≠ j, i <_P j iff x_i ≤ x_j on all of C_P,
because incomparable i, j are ordered either way by linear extensions. Then
apply g ([PCV] §3.1, CITED). Write o = ord(τ).

**S1 (the lattice; CITED).** Λ(C_P) is dual to OP(P), the set partitions of [n]
whose quotient digraph (B → B′ when some i ∈ B, j ∈ B′ have i <_P j) is
acyclic. g acts on flats as τ acts on partitions. So Λ(C_P)^g is dual to
M := OP(P)^τ, the τ-stable members of OP(P) ([PCV] §3.1, [Thm]). Also
χ_{C_P}(g) = (−1)^d det(g) μ(Λ(C_P)^g) ([VC]), and μ(0̂, 1̂) is the same for a
lattice and its dual. So

  χ_{C_P}(g) = 0  iff  μ(M) = 0,

and "has an uncomplemented element" is self-dual too. From now on M is ordered
by refinement: 0̂ is the discrete partition and 1̂ is the one-block partition.

**S2 (meet and join in M; PROVEN, the poset form of [AudPCV] F6).**
- *Meet.* The meet is the common refinement x ∧ y. It is acyclic: a cycle of
  its quotient projects to a closed walk in the quotient of x. That quotient
  is acyclic, so the walk stays in one block of x, and likewise in one block
  of y. So the walk stays in one block of x ∧ y, a contradiction. The common
  refinement is also τ-stable.
- *Join.* The join is the acyclic closure of the partition join x ∨ y: merge
  each strongly connected component of its quotient. Any acyclic coarsening
  of a partition π must merge each strong component of π's quotient. The
  merged partition is acyclic, since its quotient is the condensation. τ maps
  the quotient digraph to itself or to its reverse, so it preserves the strong
  components.
- *When the join is the plain partition join.* If every relation of P lies
  inside blocks of x ∨ y, the quotient of x ∨ y has no edges, so
  x ∨_M y = x ∨ y. This holds whenever x or y is coarser than the component
  partition κ of P.
- *Consequence.* x ∧ y = 0̂ iff no block of x meets a block of y in two
  points.

**S3 (Crapo; CITED).** If a finite lattice has an element without a
complement, then μ(0̂, 1̂) = 0 (Crapo 1966; EC1 Ex. 3.92). This is the "if"
direction of CR_V, for every cone. Only the converse needs proof.

**S4 (fixed-space partitions are in M; PROVEN).** For h ∈ ⟨g⟩, let cl(Fix h) be
the partition with i ~ j iff x_i = x_j for all x ∈ Fix h (⊆ R^n_0). Then
cl(Fix h) ∈ M, and no block of it contains a relation of P.

*Proof.*
- *An interior fixed point.* int C_P = {x : x_i < x_j for all i <_P j} is
  nonempty, convex and h-stable. The ⟨h⟩-average of an interior point is an
  interior point of Fix h.
- *Generic choice.* So Fix h ∩ int C_P is a nonempty open subset of Fix h.
  The y ∈ Fix h with y_i ≠ y_j for all i ≁ j form an open dense subset. Pick
  y in both.
- *Acyclic.* The level-set partition of y is cl(Fix h). For i <_P j we have
  y_i < y_j, so i and j lie in different blocks, and every quotient edge goes
  from a smaller value to a larger one. Hence the quotient is acyclic.
- *τ-stable.* g commutes with h, so gFix h = Fix h, and (gx)_{τi} = ε x_i.
  Hence i ~ j iff τi ~ τj. ∎

Explicitly:
- cl(Fix(+τ^k)) = cyc(τ^k), the partition into cycles of τ^k (the orbits of
  ⟨τ^k⟩).
- cl(Fix(−τ^k)) has one block holding every point on an odd cycle of τ^k (if
  there is one). Each even cycle (i, τ^k i, …) of τ^k contributes two blocks:
  its points at even positions and its points at odd positions.
- In particular, write c := cl(Fix g). If k is even, (ετ)^k = τ^k and
  cl(Fix g^k) = cyc(τ^k).

**S5 (Lemma K_A; PROVEN).** Let κ = comp(P) be the partition into connected
components. Let w ∈ M with w ≤ c (w refines c). Every complement x of w in M
satisfies x ≥ κ. For such x, x ∨_M w = x ∨ w (S2).

*Proof.*
- *A g-stable cone of points.* Suppose x ∈ M is not ≥ κ. Then some relation
  i <_P j has i and j in different blocks of x. Let R be the set of
  y ∈ R^n_0 that are constant on the blocks of x and satisfy y_a < y_b for
  every relation a <_P b between different blocks of x.
- *R is nonempty and convex.* Take values increasing along a topological
  order of the acyclic quotient, then subtract the mean.
- *R is g-stable.* g maps functions constant on x-blocks to functions
  constant on τ(x)-blocks, which are the x-blocks. For ε = +1, a relation
  a′ <_P b′ between blocks has the form (τa, τb) with a <_P b. For ε = −1 it
  has the form (τb, τa) with a <_P b, and (gy)_{τb} = −y_b < −y_a = (gy)_{τa}.
- *An averaged fixed point.* The ⟨g⟩-average y* lies in R ∩ Fix g. It is
  constant on x-blocks and on c-blocks, hence on w-blocks. It lies in C_P, and
  y*_i < y*_j.
- *Its level partition.* Let ŷ be the level-set partition of y*. It is
  τ-stable, since y* is fixed. It is acyclic, since y* ∈ C_P. It satisfies
  ŷ ≥ x and ŷ ≥ w, and ŷ ≠ 1̂.
- So x ∨_M w ≤ ŷ < 1̂, and x is not a complement. ∎

This is [CRV] Lemma F and Lemma K, restated and re-proven for posets.

**S6 (the parameters of g).** Write Λ for the set of cycle lengths of τ.
- *Orbit lengths.* For a block K of κ, λ_K is the length of the ⟨τ⟩-orbit of
  K. Then λ_K divides ℓ for every point of K on a cycle of length ℓ.
- *Odd points.* A point on an odd cycle of τ is *odd*, and O is the set of odd
  points.
- *The blocks of c for g = −τ.* c = cl(Fix(−τ)) has the block O (if O ≠ ∅)
  and the two parity classes of each even cycle (S4).

## 2. Lemma C: complements of orbit partitions

**Lemma C (PROVEN).** Let σ ∈ S_n have order o. Let κ be a σ-stable partition
of [n], with λ_K the length of the ⟨σ⟩-orbit of the block K. Let h | o, and let
w be the partition into orbits of H = ⟨σ^h⟩. Then the following are equivalent:
- (i) some σ-stable partition x ≥ κ has x ∧ w = 0̂ and x ∨ w = 1̂ (partition
  join);
- (ii) some positive integer s has gcd(s, h) = 1, s | λ_K for every block K of
  κ, and ℓ / gcd(ℓ, h) = s for every cycle length ℓ of σ.

In (ii), ℓ/gcd(ℓ, h) is the cycle length of σ^h on an ℓ-cycle. So (ii) says:
σ^h has all its cycles of one length s, s is coprime to h, and s divides every
λ_K.

*Proof, (i) ⇒ (ii).*
- *Step 1: one orbit of blocks.* The union of a ⟨σ⟩-orbit of blocks of x is
  σ-stable, so it is a union of cycles of σ. Distinct orbits of blocks have
  disjoint unions. The blocks of x and of w (the H-orbits lie inside cycles)
  stay inside these unions, so x ∨ w does too. Since x ∨ w = 1̂, x consists of
  a single orbit of blocks B, σB, …, σ^{s−1}B. Here ⟨σ^s⟩ = Stab(B) and s | o,
  and σ^jB = σ^{j′}B iff s | j − j′.
- *Step 2: s divides every λ_K and every ℓ.* If σ^j fixes a point q ∈ B, or a
  block K ⊆ B of κ (x ≥ κ), then σ^jB meets B, so σ^jB = B. So
  Stab(q) = ⟨σ^ℓ⟩ ⊆ ⟨σ^s⟩ and Stab(K) = ⟨σ^{λ_K}⟩ ⊆ ⟨σ^s⟩. That is, s | ℓ and
  s | λ_K for all points and blocks of B. Since every point and every block of
  κ lies in some σ^jB, this holds everywhere.
- *Step 3: gcd(s, h) = 1.* Every point lies in some σ^jB, with j determined
  mod s. Put φ(y) = j mod gcd(s, h). Then φ is constant on blocks of x, and
  φ(σ^h y) = φ(y) + h ≡ φ(y). So φ is constant on the blocks of x ∨ w = 1̂,
  and it takes every value mod gcd(s, h). Hence gcd(s, h) = 1.
- *Step 4: ℓ = s · gcd(ℓ, h).* Let q ∈ B lie on a cycle of length ℓ. Then
  σ^j q ∈ B iff s | j (as in Step 2), and σ^j q lies in the H-orbit of q iff
  j ∈ hZ + ℓZ = gcd(h, ℓ)Z. So B ∩ Hq = {q} says lcm(s, gcd(h, ℓ)) ≡ 0 mod ℓ.
  Both s and gcd(h, ℓ) divide ℓ, so lcm(s, gcd(h, ℓ)) = ℓ. They are coprime by
  Step 3, so ℓ = s · gcd(ℓ, h). Every point lies in a translate of B, which has
  the same stabilizer. ∎

*Proof, (ii) ⇒ (i).*
- *The partition.* Choose one block K_r of κ in each ⟨σ⟩-orbit of blocks, and
  put B = ∪_r ∪_a σ^{as} K_r. Let x = {σ^jB : 0 ≤ j < s}.
- *It is a partition.* The σ^jB cover [n]. Suppose σ^jB ∩ σ^{j′}B ≠ ∅. Then
  σ^{j+as}K_r = σ^{j′+a′s}K_r for some r, a, a′, so λ_{K_r} divides
  j − j′ + (a − a′)s. Since s | λ_{K_r}, this gives s | j − j′.
- *Its properties.* So x is a σ-stable partition, x ≥ κ, and Stab(B) = ⟨σ^s⟩.
- *x ∧ w = 0̂.* Step 4 read backwards gives B ∩ Hq = {q}, since
  lcm(s, gcd(h, ℓ)) = s · gcd(h, ℓ) = ℓ. The same holds for every translate.
- *x ∨ w = 1̂.* For q ∈ B, σ^h q ∈ σ^hB, so the block of x ∨ w through B
  contains every σ^{ah}B. Since gcd(h, s) = 1, these are all the blocks. ∎

COMPUTED ([CVA] part [RED]): for every pair with n ≤ 7 and every k with
cl(Fix g^k) = cyc(τ^k), Lemma C (with h = gcd(k, o) and κ = comp(P)) agrees with
the direct lattice test "cyc(τ^k) has a complement in M". There are 4,764
checks, 0 failures. Both outcomes occur: 48 complemented, 4,716 not. By
Lemma K_A the lattice test and the condition of (i) are the same question.

## 3. Theorem TA-CR

**Theorem TA-CR (PROVEN).** Let n ≥ 3, let P be a poset on [n], and let
g = ετ ∈ ±S_n preserve C_P. If χ_{C_P}(g) = 0, then the element W of the table
below lies in M = OP(P)^τ and has no complement in M. Conversely, an
uncomplemented element forces χ_{C_P}(g) = 0 (S3). So CR_V holds on every cone
of the braid arrangement.

Table W (first matching row; p is the least prime with p² dividing the number
named):

| case | when (zeros of [Thm] / [PCV] TA) | witness W | kind |
|---|---|---|---|
| W+1 | g = +w, ⟨w⟩ not free on the components of P | cyc(w) = cl(Fix g) | ≤ c |
| W+2 | g = +w, ⟨w⟩ free on components, o = ord w not squarefree | cyc(w^{o/p}) = cl(Fix g^{o/p}) | ≤ c |
| W−1 | g = −τ, (TA1) fails | cyc(τ^k) = cl(Fix g^k), with k = 2m/p if Λ ⊆ {m, 2m} for an odd m, and k = 2 otherwise | ≤ c |
| W−2 | g = −τ, (TA1) holds, (TA2) fails | c = cl(Fix g) | ≤ c |
| W−3 | g = −τ, (TA1), (TA2) hold, (TA3) fails | c = cl(Fix g) | ≤ c |
| W−4 | g = −τ, (TA1)–(TA3) hold, (TA4) fails | Q \| singletons, Q = the points on even cycles | ≥ κ |

Here (TA1)–(TA4) are the conditions of [PCV] Theorem TA:
- **(TA1)** Λ ⊆ {m, 2m} for an odd squarefree m;
- **(TA2)** every λ_K ∈ {m, 2m};
- **(TA3)** K ∪ τ^mK has at most one odd point, for every component K;
- **(TA4)** if τ has odd and even cycles, some odd cycle is not made of
  isolated points of P.

The rows exhaust the zeros: for +w by [Thm, eq. closed], for −τ by Theorem TA
(both CITED, audited). This exhaustion is the only place the nonvanishing
criteria are used. Every witness is shown uncomplemented directly, without
the closed formulas.

*Proof.* Rows W+1 to W−3 use w ≤ c, so by S5 a complement x satisfies x ≥ κ,
and x ∨_M w = x ∨ w.

- **W+1.** W = cyc(w) is the orbit partition of ⟨w⟩, with h = 1. In Lemma C(ii),
  h = 1 forces s = ℓ for every cycle length ℓ, so all cycles have length s = o.
  Then s | λ_K | ℓ = o forces λ_K = o for every component, that is, ⟨w⟩ acts
  freely on components. In row W+1 it does not, so (ii) fails. By Lemma C and
  S5, W has no complement. W ∈ M by S4.
- **W+2.** Freeness gives λ_K = o for all K. Since λ_K | ℓ | o, every cycle has
  length o. Take h = o/p. Then ℓ/gcd(ℓ, h) = o/(o/p) = p, so s = p. But
  p² | o gives p | h, so gcd(s, h) ≠ 1, and (ii) fails. W = cyc(w^{o/p}) ∈ M
  by S4, and W ≤ c since cycles of w^{o/p} lie in cycles of w.
- **W−1.** k is even, so cl(Fix g^k) = cyc(τ^k) (S4), the orbit partition of
  ⟨τ^{h}⟩ with h = gcd(k, o). Also cl(Fix g^k) ≤ c, because Fix g^k ⊇ Fix g.
  Three sub-cases:
  - *o odd* (all cycles odd). If Λ is not a single odd m, take k = 2: then h = 1, and (ii) needs all ℓ equal. It fails since
    |Λ| ≥ 2. If Λ = {m}, TA1 fails only because m is not squarefree, and this
    is the next sub-case.
  - *Λ ⊆ {m, 2m}, m odd* (so m is not squarefree; such m is unique when it
    exists). Take k = 2m/p. For ℓ = m, gcd(ℓ, h) = gcd(2m/p, m) = m/p (p is
    odd). For ℓ = 2m (then o = 2m), gcd(ℓ, h) = 2m/p. Either way
    ℓ/gcd(ℓ, h) = p = s. But p | m/p divides h, so gcd(s, h) ≠ 1. (ii) fails.
  - *Otherwise* (o even, and Λ in no {m, 2m} with m odd): k = 2 and h = 2.
    (ii) would need s odd with ℓ/gcd(ℓ, 2) = s for all ℓ, that is,
    Λ ⊆ {s, 2s}. Excluded.

  In every sub-case Lemma C and S5 show W has no complement.
- **W−2.** Let K be a component with λ = λ_K ∉ {m, 2m}. Since λ divides o and
  o divides 2m, we get m ∤ λ. Take y ∈ K.
  - If y is odd (cycle length m), τ^λ y ∈ K is a second odd point (m ∤ λ).
    Both lie in the block O of c.
  - If y lies on a 2m-cycle, τ^{2λ} y ∈ K differs from y (2m ∤ 2λ) and lies in
    the same parity class.

  Either way κ ∧ c ≠ 0̂. A complement x of c would have x ≥ κ (S5), hence
  x ∧ c ≥ κ ∧ c ≠ 0̂. So c has no complement.
- **W−3.** Let K be a component where K ∪ τ^mK has two odd points. An odd point
  q ∈ τ^mK has τ^{−m} q = q (odd cycles have length m), so q ∈ K. Hence K
  holds two odd points, both in the block O of c. So κ ∧ c ≠ 0̂, and c has no
  complement, as in W−2.
- **W−4** ([PCV] §3.6, audited in [AudPCV] §6; re-derived here). Let A_0 = O
  (all odd points are isolated) and Q = [n] ∖ O, both nonempty. Let a be the
  partition with block Q and singletons on A_0.
  - *a ∈ M.* It is τ-stable, and every relation of P lies inside Q, so it is
    acyclic. Also a ≥ κ, so x ∨_M a = x ∨ a (S2).
  - *What a complement x would be.* x ∧ a = 0̂ means each block of x meets Q in
    at most one point. x ∨ a = 1̂ means each block of x meets Q. So
    φ: A_0 → Q, sending p to the Q-point of its x-block, is a τ-equivariant
    map.
  - *Contradiction.* For p ∈ A_0, τ^m p = p gives τ^m φ(p) = φ(p). But φ(p)
    lies on a 2m-cycle (TA1). ∎

**Remarks.**
- *Only κ and Λ matter.* The proofs of W+1 to W−3 use P only through κ, via S5.
  This is the lattice form of [PCV] Cor. 3.5(a): vanishing depends only on
  (comp(P), g).
- *Rows W+1 to W−3 are all-chambers obstructions, pulled back.* For W+2 and
  W−1, the witness is already uncomplemented in Π_n^τ (all chambers, κ = 0̂),
  and S5 transports this to every cone. For W−2 and W−3, the obstruction
  needs κ: on all chambers these rows do not occur. Row W+1 does occur on all
  chambers: on the antichain, +w is a W+1 zero exactly when w has two
  distinct cycle lengths (e.g. +(0 1) on 3 points, where Π_3^{(01)} is the
  chain 0̂ < 01|2 < 1̂), and Lemma C(ii) then fails with h = 1 even at κ = 0̂
  ([AudCVA] §2, R1, corrected here). No proof uses this remark.
- *The exponent matters.* cl(Fix g) itself is complemented on 93 zero pairs
  with n ≤ 7: 79 in row W−4, 13 in row W−1 and 1 in row W+2. Example: the antichain on 4 points with
  −(0)(1 2 3) gives a W−1 zero (Λ = {1, 3}), and cyc(τ²) is the witness. And
  for −(0 1 … 8) on 9 points, k = 2 gives cyc(τ²) = 1̂, which is complemented,
  while k = 6 works (test `test_odd_nonsquarefree_needs_k_2m_over_p`).
- *Why rank 4 fails in general but not here.* The counterexample of [CRV] §0 is
  a cancellation 1 − 1 = 0 on a complemented, non-modular lattice. For −τ in
  type A, the zeros other than (TA4) carry no nonzero μ on Z\* ([PCV]
  Cor. 3.5(c)), so no cancellation is involved there. The (TA4) zeros do
  cancel, but they are not complemented (W−4). On the type-A side, every zero is either a fixed-space zero
  (W+1 to W−3) or the (TA4) map φ.

## 4. Computation ([CVA])

`compute/cr_v_type_a.py` uses this model:
- posets up to isomorphism, generated by adding a maximal element and
  canonized by invariant-refined permutation search;
- τ ∈ Aut(P) and anti-automorphisms up to conjugation by Aut(P);
- M built from the τ-stable partitions, filtered for acyclicity;
- meet = common refinement (pair bitmasks), join = strong-component closure
  of the partition join;
- μ by recursion;
- "complemented" by direct search over M.

**Controls ([CTL]), all passing:**
- poset counts 1, 1, 2, 5, 16, 63, 318, 2045 for n = 0..7 (OEIS A000112);
- μ(Π_n^τ) equals Hanlon's value on all 29 cycle types with n ≤ 6 (positive
  control for μ);
- Π_4^{(1234)} is the chain 0̂ < {13|24} < 1̂, with μ = 0 and {13|24}
  uncomplemented (positive control for "uncomplemented");
- Π_4 has 15 elements, μ = −6, is complemented, and its joins are least upper
  bounds (positive control for "complemented" and for the join);
- OP(3-chain) = B_2, with μ = 1;
- the [AudPCV] F6 example (P = {0 < 2, 1 < 3}): the join of 03|1|2 and 12|0|3
  is 1̂, not the cyclic partition join 03|12 (positive control for the
  acyclic closure);
- pair counts without conjugacy reduction, per n = 3..6: (anti, all) =
  (8, 20), (37, 96), (153, 478), (922, 2982). These equal the tallies of
  `compute/output/per_cone_vanishing.txt` exactly (a reproduction of [PCV]'s
  enumeration);
- the stable-partition generator agrees with filtering all set partitions, on
  every cycle type with n ≤ 7.

**Exhaustive sweep ([CRIT], [WIT], [RED]), n = 3..7, up to isomorphism:**

| n | pairs +w | pairs −τ | zeros +w | zeros −τ | witnesses W+1 / W+2 / W−1 / W−2 / W−3 / W−4 | witness failures | criterion mismatches | Lemma C checks (complemented) | Crapo control: nonzero pairs all complemented |
|---|---|---|---|---|---|---|---|---|---|
| 3 | 9 | 5 | 3 | 2 | 3 / 0 / 0 / 0 / 0 / 2 | 0 | 0 | 7 (4) | 9 of 9 |
| 4 | 34 | 16 | 16 | 6 | 15 / 1 / 3 / 0 / 1 / 2 | 0 | 0 | 27 (4) | 28 of 28 |
| 5 | 144 | 30 | 80 | 19 | 80 / 0 / 7 / 0 / 2 / 10 | 0 | 0 | 128 (8) | 75 of 75 |
| 6 | 758 | 108 | 432 | 49 | 432 / 0 / 23 / 2 / 14 / 10 | 0 | 0 | 654 (20) | 385 of 385 |
| 7 | 4,804 | 246 | 2,758 | 154 | 2,758 / 0 / 69 / 0 / 30 / 55 | 0 | 0 | 3,948 (12) | 2,138 of 2,138 |

Totals: 6,154 pairs (5,749 with +w, 405 with −τ), 3,519 zeros, every zero
witnessed. Lemma K_A held on every complement found (0 failures).
"Criterion mismatches" compares μ(M) = 0 with the zero sets of [Thm] and TA, a
reproduction of those theorems on n ≤ 7. The negative control (zeros on which
cl(Fix g) is complemented, so that the rows really differ) gives 2, 4, 11, 15,
61 for n = 3..7.

**Targeted pairs ([EXTRA]).** Rows W+2 and the "m odd, not squarefree" branch
of W−1 are rare or absent at n ≤ 7, so they are checked on 13 targeted pairs,
all passing:
- antichain 8 with ±(4,4) and ±(8);
- four 2-chains with +(4,4) free on components;
- antichain 9 with ±(9), the branch k = 6;
- antichain 18 with ±(18);
- nine 2-chains with an anti-automorphism −(18) (Λ = {18} ⊆ {9, 18}, k = 6,
  a poset that is not an antichain);
- nonzero controls: antichain 9 with ±(3,3,3) (μ = −18), and nine 2-chains
  with −(6,6,6) (Case IIa, |M| = 180, μ = 18). Both are fully complemented.

**Not run.**
- No exhaustive sweep with n ≥ 8.
- The branch "Λ = {m, 2m} with m odd and not squarefree, both lengths
  present" (first at n = 9 + 18 = 27) is not run by [CVA]. The single-length
  cases Λ = {9} and Λ = {18} of the same branch are COMPUTED above. The
  two-length case τ = (9)(18), n = 27, is COMPUTED by the independent code
  of [AudCVA] §3 (exhaustive search: cyc(τ^6) is uncomplemented, with a
  complemented control).

## 5. Status changes and remarks on other notes (applied after the audit [AudCVA])

- **[CRV] §6, "Type A ... OPEN"**: settled by Theorem TA-CR (PROVEN here,
  audited in [AudCVA]). The Verdict line "the rank-4 counterexample has the smallest
  possible rank" is unaffected. No counterexample lies in type A, in any rank.
- **[PCV] Verdict row CR_V**: on cones of the braid arrangement it is a theorem
  (TA-CR). In general it remains refuted ([CRV]).
- **[PCV] row CO** ("In type A every zero from (TA4) is of this kind"): every
  type-A zero is of this kind, with the witnesses of table W.
- **[PCV] §4 / [CRV] §7: "5,063 lattices OP(P)^{±τ} with n ≤ 6".** The archived
  log `compute/output/per_cone_vanishing.txt` lists 20 + 96 + 478 + 2,982 =
  3,576 lattices for n = 3..6, of which 1,120 are −τ. [CVA] reproduces those
  per-n tallies exactly. The figure 5,063 could not be reconciled with the
  log. [AudCVA] §5 recounts 3,576 independently and finds no count that
  gives 5,063; [PCV] and [CRV] now print 3,576. The conclusion
  ("no counterexample") is unaffected.
- No claim of another note was found to be wrong.

## 6. What remains open

- **Other Coxeter types.** The analogue for B_n (signed posets), D_n, F_4, H_3
  and H_4 is OPEN. Two ingredients carry over unchanged: S4 and S5 hold for
  any arrangement (they are [CRV] Lemmas F and K). Lemma C is specific to
  permutation actions, and the cone lattice of B_n is not a partition lattice.
- **Audit.** Done: [AudCVA] finds Theorem TA-CR, Lemma K_A, Lemma C, S0, S2,
  S4 and S5 HOLD.
- **Observation CC** ([PACVA] §2.3): on every zero, 0̂ is not a meet of
  coatoms of M or 1̂ is not a join of atoms (EC1 Cor. 3.9.5). Settled:
  Theorem CC of `notes/observation_cc.md` proves it for every n (PROVEN,
  independently audited in `notes/audit_observation_cc.md`: every step
  HOLDS; COMPUTED there and in the audit for n ≤ 8). Its Corollary U gives a
  second proof of the "only if" half of TA-CR, with the uniform
  uncomplemented witnesses c ∧ D and O | Q. TA-CR is unaffected.

## Reproduce

From `compute/` (plain Python 3, no third-party packages, single process):

    python3 cr_v_type_a.py --nmax 7 --budget 1500 --crapo-nmax 7 > output/cr_v_type_a.txt   # ~30 s, ends "ALL CHECKS PASSED", exit 0
    python3 cr_v_type_a.py --nmax 6                                                          # ~1 s
    python3 -m unittest test_cr_v_type_a                                                     # < 1 s, positive and negative controls

`--budget` bounds the wall time of the sweep in seconds. If it runs out, the
remaining posets and the larger n are printed as UNRUN, and the script exits
1 without printing ALL CHECKS PASSED. `--crapo-nmax` sets the largest n for
the Crapo control (full complementation check on nonzero pairs). The archived
log is `compute/output/cr_v_type_a.txt`.

References:
- [PCV] = `notes/per_cone_vanishing.md`;
- [AudPCV] = `notes/audit_per_cone_vanishing.md`;
- [CRV] = `notes/conjecture_cr_v.md` (audit: `notes/audit_conjecture_cr_v.md`);
- [AudCVA] = `notes/audit_cr_v_type_a.md` (independent audit of this note);
- [PACVA] = `notes/prior_art_cr_v_type_a.md`;
- [VC] = `notes/vanishing_criterion.md`;
- [GT] = `notes/general_theory.md`;
- [FP] = `notes/fixed_point_formula.md`;
- [Thm] = `notes/poset_jks_theorem.tex`;
- Crapo, *The Möbius function of a lattice*, J. Combin. Theory 1 (1966);
- Stanley, *Enumerative Combinatorics* vol. 1, 2nd ed., Ex. 3.92;
- Hanlon, *The fixed-point partition lattices*, Pacific J. Math. 96 (1981);
- Whitney, *2-isomorphic graphs*, Amer. J. Math. 55 (1933).

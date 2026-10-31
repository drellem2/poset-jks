# Moonshine for the alternating group: scoping (DRAFT, incomplete)

Status: DRAFT. None of the computations below have been run yet, and
nothing here is COMPUTED. The PROVEN tags mark short arguments sketched in
this draft. None of them has been audited.

## Planned verdict table

| # | Graded object | Group | T_g(q) | Expected verdict | Linear-extension content |
|---|---|---|---|---|---|
| 1 | Witt layer Prim(𝐐) = ⊕_n ⊕_P Lie(P), graded by n = \|P\| | S_n / A_n per degree; invariants, cycle-type traces | A(q) = ∏(1−q^n)^{−c_n}, c_n = dim V_n^{S_n} = (1/n)Σ_{d\|n} μ(d) b_{n/d} | NO SIGN (growth obstruction below) | none |
| 2 | lattice points of the cone C_P (P-partitions), graded by \|σ\| | Aut(P) ∩ A_n | Σ_{g-fixed σ} q^{\|σ\|} | NO SIGN (rational in q) | yes: a weighted maj over Lin(P/⟨g⟩) |
| 3 | P-partitions of infinite posets: k·N, chain_m × N, N × N | S_k ⊇ A_k (k·N) | k·N: ∏_cycles 1/(q^λ;q^λ)_∞ | k·N MODULAR but generic (Frame shapes); the others NO SIGN | weak |
| 4 | Fock space Sym(Lie(P) ⊗ tC[t]); equals Sym(H_P ⊗ tC[t]) on A_n | Aut(P) ∩ A_n | q^{dim/24}/η_g with η_g = ∏η(tτ)^{r_t} (Frame shape of g on Lie(P)) | MODULAR always, generic | none |

Planned recommendation: STOP. The only source of modularity is the
Frame-shape (cycle-shape) mechanism, and that works for any rational
representation of any finite group. The data specific to posets is either
super-exponential (row 1) or rational (row 2).

## Arguments sketched so far (PROVEN in sketch, not audited)

- **Growth obstruction (row 1).** Take the naturally labeled posets on
  [n] in which 1..k are minimal, k+1..n are maximal, and every relation
  goes from {1..k} to {k+1..n}. Every set of such relations is transitive,
  so a_n ≥ 2^{⌊n/2⌋⌈n/2⌉}. Hence A(q) has radius of convergence 0.
  - Because c_n ≥ 0, subexponential c_n would make ∏(1−q^n)^{−c_n}
    converge on |q| < 1. So the c_n grow super-exponentially as well.
  - The cycle-type traces χ_{V_{dm}}(d^m) = μ(d) d^{m−1} (m−1)! b_m also
    grow super-exponentially.
  - So no series in this grading is the q-expansion of a modular object.
- **Rationality (row 2).** Suppose a nonconstant R(q) were modular for a
  finite-index Γ. Take γ ∈ Γ with c ≠ 0. Then R∘exp(2πi·) would be
  meromorphic at ∞ and periodic, which is impossible. So no nonconstant
  rational function of q is modular.
- **Quotient formula (row 2).** The g-fixed P-partitions are the
  P/⟨g⟩-partitions weighted by orbit size. P/⟨g⟩ is a poset by Lemma 2.1
  of global_module_operations_plethlog.md. Stanley's fundamental lemma then
  gives T_g = Σ_{w ∈ Lin(P/⟨g⟩)} q^{Σ_{i∈Des w} S_{i+1}(w)} / ∏_j (1 − q^{S_j(w)}),
  where S_j(w) is the total weight of w_j, …, w_m.
- **Frame shapes (row 4).** χ(g^e) is given by the fixed-point formula,
  and t·r_t = Σ_{e\|t} μ(t/e) χ(g^e).
  - For connected P, Lie(P) is free, so the Frame shape is o^{e_C/o}.
  - For the p-cycle on Lie_p the Frame shape is 1^{−1} p^{((p−1)!+1)/p}.
    The exponent is an integer by Wilson's theorem.
  - At p = 5 this gives η(5τ)^5/η(τ), Ramanujan's weight-2 Eisenstein form
    on Γ0(5). This only reflects dim Lie_5 = 24 and χ = −1.
- **What A_n buys.** On Aut(P) ∩ A_n we have H_P ≅ Lie(P), so the
  homological and Lie versions of every candidate coincide.
  - For odd g the Frame shape changes as follows: odd t^r becomes
    (2t)^r t^{−r}, and even t is unchanged.

## Unfinished

- compute/ code (eta-quotient detector, Witt and θ_3 positive controls,
  equivariant P-partition brute force against the quotient formula,
  Frame shapes, Sturm check of η(5τ)^5/η(τ)).
- OEIS lookups.
- The Reproduce section.

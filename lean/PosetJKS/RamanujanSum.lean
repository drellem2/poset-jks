import Mathlib

/-!
# The Ramanujan sum at `1`: the sum of the primitive `o`-th roots of unity is `μ(o)`

For an integral domain `R` and `o ≥ 1`:

* `sum_primitiveRoots_eq_moebius`: if `R` contains a primitive `o`-th root of unity, then
  `∑_{ξ ∈ primitiveRoots o R} ξ = μ(o)`;
* `sum_pow_coprime_eq_moebius`: for a primitive `o`-th root `ω`,
  `∑_{0 ≤ s < o, gcd(s, o) = 1} ω^s = μ(o)`.

Proof: `∑_{ξ^n = 1} ξ = [n = 1]` for every `n ∣ o` (a geometric sum), the `n`-th roots of unity
are the disjoint union of the primitive `d`-th roots for `d ∣ n`, and Möbius inversion.

These are general facts about roots of unity and do not depend on the rest of the project.
-/

open Finset

namespace PosetJKS

variable {R : Type*} [CommRing R] [IsDomain R]

/-- `∑_{ξ^n = 1} ξ = [n = 1]` when `R` has a primitive `n`-th root of unity. -/
theorem sum_nthRootsFinset_one {ξ : R} {n : ℕ} (hξ : IsPrimitiveRoot ξ n) (hn : 0 < n) :
    ∑ x ∈ Polynomial.nthRootsFinset n (1 : R), x = if n = 1 then 1 else 0 := by
  classical
  have : NeZero n := ⟨hn.ne'⟩
  have himage : Polynomial.nthRootsFinset n (1 : R) = (range n).image (ξ ^ ·) := by
    ext x
    rw [Polynomial.mem_nthRootsFinset hn, mem_image]
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := hξ.eq_pow_of_pow_eq_one hx
      exact ⟨i, mem_range.2 hi, rfl⟩
    · rintro ⟨i, -, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
  rw [himage, sum_image fun i hi j hj h => hξ.pow_inj (mem_range.1 hi) (mem_range.1 hj) h]
  split_ifs with h1
  · subst h1; simp
  · exact hξ.geom_sum_eq_zero (by omega)

/-- `∑_{d ∣ n} ∑_{ξ primitive d-th root} ξ = ∑_{ξ^n = 1} ξ`. -/
theorem sum_divisors_sum_primitiveRoots (n : ℕ) :
    ∑ d ∈ n.divisors, ∑ x ∈ primitiveRoots d R, x =
      ∑ x ∈ Polynomial.nthRootsFinset n (1 : R), x := by
  classical
  rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots, sum_biUnion]
  intro i _ j _ hij
  exact IsPrimitiveRoot.disjoint hij

/-- **The Ramanujan sum at `1`**: if `R` has a primitive `o`-th root of unity, the primitive
`o`-th roots of unity sum to `μ(o)`. -/
theorem sum_primitiveRoots_eq_moebius {ω : R} {o : ℕ} (hω : IsPrimitiveRoot ω o) (ho : 0 < o) :
    ∑ x ∈ primitiveRoots o R, x = (ArithmeticFunction.moebius o : R) := by
  classical
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun d => ∑ x ∈ primitiveRoots d R, x)
    (g := fun n => ∑ x ∈ Polynomial.nthRootsFinset n (1 : R), x)).1
    (fun n _ => sum_divisors_sum_primitiveRoots n) o ho
  rw [← hinv]
  rw [sum_eq_single (o, 1)]
  · show (ArithmeticFunction.moebius o : R) * _ = _
    rw [sum_nthRootsFinset_one IsPrimitiveRoot.one one_pos]
    simp
  · rintro ⟨a, b⟩ hab hne
    have hab' := Nat.mem_divisorsAntidiagonal.1 hab
    have hb : 0 < b := Nat.pos_of_ne_zero fun h => by simp [h] at hab'; omega
    have ha : 0 < a := Nat.pos_of_ne_zero fun h => by simp [h] at hab'; omega
    have hprim : IsPrimitiveRoot (ω ^ a) b := hω.pow ho hab'.1.symm
    simp only
    rw [sum_nthRootsFinset_one hprim hb, if_neg, mul_zero]
    rintro rfl
    apply hne
    rw [mul_one] at hab'
    exact Prod.ext hab'.1 rfl
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.2 ⟨mul_one o, ho.ne'⟩) h

/-- **The Ramanujan sum at `1`**, by exponents: for a primitive `o`-th root of unity `ω`,
`∑_{0 ≤ s < o, gcd(s, o) = 1} ω^s = μ(o)`. -/
theorem sum_pow_coprime_eq_moebius {ω : R} {o : ℕ} (hω : IsPrimitiveRoot ω o) (ho : 0 < o) :
    ∑ s ∈ (range o).filter (fun s => s.Coprime o), ω ^ s =
      (ArithmeticFunction.moebius o : R) := by
  classical
  have : NeZero o := ⟨ho.ne'⟩
  rw [← sum_primitiveRoots_eq_moebius hω ho]
  have himage : primitiveRoots o R = ((range o).filter (fun s => s.Coprime o)).image (ω ^ ·) := by
    ext x
    rw [mem_primitiveRoots ho, hω.isPrimitiveRoot_iff, mem_image]
    constructor
    · rintro ⟨i, hi, hc, rfl⟩
      exact ⟨i, mem_filter.2 ⟨mem_range.2 hi, hc⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨hi, hc⟩ := mem_filter.1 hi
      exact ⟨i, mem_range.1 hi, hc, rfl⟩
  rw [himage, sum_image fun i hi j hj h =>
    hω.pow_inj (mem_range.1 (mem_filter.1 hi).1) (mem_range.1 (mem_filter.1 hj).1) h]

end PosetJKS

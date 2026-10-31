import PosetJKS.MuOP

/-!
# The Möbius side: the sign in the interval lemma and the signed recursion (W)

`notes/poset_jks_theorem.tex`, Lemma `lem:interval`(ii) and the signed recursion (W) in the proof
of Proposition `prop:Mside`.

* For `x ∈ X(P,g)` with `m` blocks, block `B₀` through `p` and `h = g^m|_{B₀}`, the map
  `(j, v) ↦ g^j v` is a bijection `ℤ/m × B₀ ≅ P` (`blkEquiv`), so `n = m k` (`card_eq_per_mul`).
  Under it `g` becomes `(j, v) ↦ (j + 1, v)` for `j + 1 < m` and `(m - 1, v) ↦ (0, h v)`: the
  product of `h` on the layer `0` and `k` cycles of length `m`. Hence
  `sgn(g) = sgn(h) (-1)^{(m-1)k}` (`sign_eq_sign_hres`), which is Lemma `lem:interval`(ii)
  (`interval_sign`): `(-1)^{n+1} sgn(g) = (-1)^{k+1} sgn(h)`. The note's exponents `n - 3`,
  `k - 3` have the parity of `n + 1`, `k + 1`; the latter avoid natural subtraction for `k ≤ 2`.
* `Mt g = (-1)^{n+1} sgn(g) μ(OP(P)^g)` is the note's `M̃(P, g)`.
* `recursionW_signed`: for `g ≠ 1`, `∑_{x ∈ X(P,g)} M̃(P|_{B₀(x)}, h_x) = 0`.
* `Mt_one`: `M̃(P, 1) = e_C(P)` (Lemma `lem:small`, from Theorem A, homology-free).
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

theorem sign_finRotate' (m : ℕ) (hm : 0 < m) :
    ((Equiv.Perm.sign (finRotate m) : ℤˣ) : ℤ) = (-1) ^ (m - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [sign_finRotate, Nat.add_sub_cancel]
  simp

/-- `M̃(P, g) = (-1)^{n+1} sgn(g) μ(OP(P)^g)`; `(-1)^{n+1} = (-1)^{n-3}`. -/
noncomputable def Mt (g : α ≃o α) : ℤ :=
  (-1) ^ (Fintype.card α + 1) * ((Equiv.Perm.sign g.toEquiv : ℤˣ) : ℤ) * muFixed g

/-- **Lemma `lem:small`**, homology-free: `M̃(P, 1) = e_C(P)` for `n ≥ 1`. -/
theorem Mt_one (h0 : 0 < Fintype.card α) : Mt (1 : α ≃o α) = eC α := by
  rw [Mt, mu_OP_eq h0]
  have hs : Equiv.Perm.sign (1 : α ≃o α).toEquiv = 1 := Equiv.Perm.sign_one
  rw [hs, Units.val_one, mul_one, ← mul_assoc, ← pow_add]
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card α = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
  rw [hn, Nat.add_sub_cancel, show n + 1 + 1 + n = 2 * (n + 1) by ring, pow_mul]
  simp

section Sign

open scoped Classical

variable {g : α ≃o α} {x : OPFixed α g} {p : α}

local notation "σ" => g.toEquiv

variable (g x p) in
/-- `(j, v) ↦ g^j v` for `j < m` and `v ∈ B₀`. -/
def blkMap (jv : Fin (per g x p) × Blk g x p) : α := (σ ^ (jv.1 : ℕ)) jv.2.1

theorem blkMap_injective : Function.Injective (blkMap g x p) := by
  have key : ∀ (j j' : ℕ) (v v' : Blk g x p), j ≤ j' → j' < per g x p →
      (σ ^ j) v.1 = (σ ^ j') v'.1 → j = j' ∧ v = v' := by
    intro j j' v v' hjj' hj' e
    have e' : v.1 = (σ ^ (j' - j)) v'.1 := by
      apply (σ ^ j).injective
      rw [pow_apply_add, Nat.add_sub_cancel' hjj']
      exact e
    have hd : x.1 p ((σ ^ (j' - j)) p) := (blk_pow_iff v'.2 (j' - j)).1 (e' ▸ v.2)
    have hz : j' - j = 0 := Nat.eq_zero_of_dvd_of_lt (per_dvd hd) (by omega)
    refine ⟨by omega, Subtype.ext ?_⟩
    rw [e', hz, pow_zero, Equiv.Perm.one_apply]
  rintro ⟨j, v⟩ ⟨j', v'⟩ e
  simp only [blkMap] at e
  rcases le_total (j : ℕ) j' with h | h
  · obtain ⟨h1, h2⟩ := key j j' v v' h j'.2 e
    exact Prod.ext (Fin.ext h1) h2
  · obtain ⟨h1, h2⟩ := key j' j v' v h j.2 e.symm
    exact Prod.ext (Fin.ext h1.symm) h2.symm

theorem blkMap_surjective (htop : OPFixed.join g x = OPFixed.top g) :
    Function.Surjective (blkMap g x p) := by
  intro u
  obtain ⟨k, hk⟩ := exists_pow_blk (p := p) htop u
  have hu : (σ ^ (orderOf σ * k - k)) ((σ ^ k) u) = u := pow_inv_apply g k u
  set i := orderOf σ * k - k
  set m := per g x p
  have hv : x.1 p ((σ ^ (m * (i / m))) ((σ ^ k) u)) := (blk_pow_iff hk _).2 (blk_pow_per_mul _)
  refine ⟨(⟨i % m, Nat.mod_lt _ (per_pos g x p)⟩, ⟨_, hv⟩), ?_⟩
  simp only [blkMap]
  rw [pow_apply_add, Nat.mod_add_div]
  exact hu

/-- `ℤ/m × B₀ ≅ P`, `(j, v) ↦ g^j v`. -/
noncomputable def blkEquiv (htop : OPFixed.join g x = OPFixed.top g) :
    Fin (per g x p) × Blk g x p ≃ α :=
  Equiv.ofBijective _ ⟨blkMap_injective, blkMap_surjective htop⟩

theorem card_eq_per_mul (htop : OPFixed.join g x = OPFixed.top g) :
    Fintype.card α = per g x p * Fintype.card (Blk g x p) := by
  rw [← Fintype.card_congr (blkEquiv (p := p) htop), Fintype.card_prod, Fintype.card_fin]

/-- `sgn(g) = sgn(h) (-1)^{(m-1)k}`. -/
theorem sign_eq_sign_hres (htop : OPFixed.join g x = OPFixed.top g) :
    ((Equiv.Perm.sign g.toEquiv : ℤˣ) : ℤ) = ((Equiv.Perm.sign (hres g x p).toEquiv : ℤˣ) : ℤ) *
      (-1) ^ ((per g x p - 1) * Fintype.card (Blk g x p)) := by
  set m := per g x p
  have hm := per_pos g x p
  set E := blkEquiv (p := p) htop
  set D : Equiv.Perm (Fin m × Blk g x p) := Equiv.prodCongrLeft fun _ => finRotate m
  set H : Equiv.Perm (Fin m × Blk g x p) :=
    Equiv.Perm.prodExtendRight ⟨0, hm⟩ (hres g x p).toEquiv
  have hE : ∀ jv, E jv = (σ ^ (jv.1 : ℕ)) jv.2.1 := fun _ => rfl
  have hrot : ∀ j : Fin m, ((finRotate m j : Fin m) : ℕ) = (j + 1) % m := fun j => by
    have := val_finRotate_pow m 1 j
    rwa [pow_one] at this
  have hG : E.symm.permCongr g.toEquiv = H * D := by
    ext1 ⟨j, v⟩
    apply E.injective
    rw [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply, Equiv.Perm.mul_apply,
      hE (j, v)]
    change σ ((σ ^ (j : ℕ)) v.1) = E (H (finRotate m j, v))
    have hσ : σ ((σ ^ (j : ℕ)) v.1) = (σ ^ ((j : ℕ) + 1)) v.1 := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [hσ]
    by_cases hj : (j : ℕ) + 1 < m
    · have hr : finRotate m j = ⟨j + 1, hj⟩ := Fin.ext (by rw [hrot, Nat.mod_eq_of_lt hj])
      have hne : (⟨(j : ℕ) + 1, hj⟩ : Fin m) ≠ ⟨0, hm⟩ := by
        intro e; have := congrArg Fin.val e; simp at this
      rw [hr, Equiv.Perm.prodExtendRight_apply_ne _ hne, hE]
    · have hj' : (j : ℕ) + 1 = m := by omega
      have hr : finRotate m j = ⟨0, hm⟩ := Fin.ext (by rw [hrot, hj', Nat.mod_self])
      rw [hr, Equiv.Perm.prodExtendRight_apply_eq, hE]
      change (σ ^ ((j : ℕ) + 1)) v.1 = (σ ^ 0) (hres g x p v).1
      rw [pow_zero, Equiv.Perm.one_apply, hres_apply_val, hj']
  rw [← Equiv.Perm.sign_permCongr E.symm g.toEquiv, hG, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_prodExtendRight, Equiv.Perm.sign_prodCongrLeft, Finset.prod_const,
    Finset.card_univ, Units.val_mul, Units.val_pow_eq_pow_val, sign_finRotate' _ hm, pow_mul]

/-- **Lemma `lem:interval`(ii)**: `(-1)^{n+1} sgn(g) = (-1)^{k+1} sgn(h)`, `k = |B₀|`
(the note's `(-1)^{n-3} sgn(g) = (-1)^{k-3} sgn(h)`). -/
theorem interval_sign (htop : OPFixed.join g x = OPFixed.top g) :
    (-1 : ℤ) ^ (Fintype.card α + 1) * ((Equiv.Perm.sign g.toEquiv : ℤˣ) : ℤ) =
      (-1) ^ (Fintype.card (Blk g x p) + 1) *
        ((Equiv.Perm.sign (hres g x p).toEquiv : ℤˣ) : ℤ) := by
  rw [sign_eq_sign_hres htop, card_eq_per_mul (p := p) htop]
  obtain ⟨m, hm⟩ : ∃ m, per g x p = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (per_pos g x p)).symm⟩
  rw [hm, Nat.add_sub_cancel]
  set k := Fintype.card (Blk g x p)
  set s := ((Equiv.Perm.sign (hres g x p).toEquiv : ℤˣ) : ℤ)
  have h1 : (-1 : ℤ) ^ ((m + 1) * k + 1) = (-1) ^ (k + 1) * (-1) ^ (m * k) := by
    rw [← pow_add]; ring_nf
  have h2 : ((-1 : ℤ) ^ (m * k)) * (-1) ^ (m * k) = 1 := by
    rw [← mul_pow]; simp
  calc (-1 : ℤ) ^ ((m + 1) * k + 1) * (s * (-1) ^ (m * k))
      = (-1) ^ (k + 1) * s * ((-1) ^ (m * k) * (-1) ^ (m * k)) := by rw [h1]; ring
    _ = (-1) ^ (k + 1) * s := by rw [h2, mul_one]

end Sign

open Classical in
/-- **The recursion (W)**, signed (proof of Proposition `prop:Mside`): for `g ≠ 1` and any
base point `p`, `∑_{x ∈ X(P,g)} M̃(P|_{B₀(x)}, h_x) = 0`. -/
theorem recursionW_signed (g : α ≃o α) (hg : g ≠ 1) (p : α) :
    have := Fintype.ofFinite (OPFixed α g)
    ∑ x ∈ univ.filter (fun x => OPFixed.join g x = OPFixed.top g), Mt (hres g x p) = 0 := by
  intro _
  have hW := recursionW g hg p
  simp only at hW
  have : ∀ x ∈ univ.filter (fun x => OPFixed.join g x = OPFixed.top g),
      Mt (hres g x p) = (-1) ^ (Fintype.card α + 1) *
        ((Equiv.Perm.sign g.toEquiv : ℤˣ) : ℤ) * muFixed (hres g x p) := by
    intro x hx
    rw [Mt, interval_sign (mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hW, mul_zero]

end PosetJKS

import PosetJKS.MuOP
import PosetJKS.LieSide

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

/-! ### Möbius inversion on `X(P,g)`, inside `OP(P)^g`

For `x ∈ X(P,g)` with `m` blocks: `m ∣ o`, and `x` relates `u` to `g^j u` iff `m ∣ j`.
`F(P,g)` is `{x ∈ X(P,g) : m = o}`. The note's inversion `∑_{z ≤ x} f(z) = Φ(x)` is
`sum_mu_below_eq_zero` for `m < o`: Weisner's theorem in the interval `[0̂, x]` of `OP(P)^g`
with `a = O_{g^m}` (which is the note's `(W)` for `(P|_{B₀(x)}, h_x)`, read inside `[0̂, x]`),
and `eq_of_le_of_per` for `m = o`. -/

section Inversion

open scoped Classical

variable {g : α ≃o α}

local notation "σ" => g.toEquiv

theorem coe_pow_aut (k : ℕ) (u : α) : (g ^ k) u = (σ ^ k) u := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [coe_pow_succ, Function.comp_apply, ih, pow_succ', Equiv.Perm.mul_apply]
    rfl

theorem toEquiv_pow (k : ℕ) : (g ^ k).toEquiv = σ ^ k := Equiv.ext (coe_pow_aut k)

theorem orderOf_toEquiv : orderOf σ = orderOf g :=
  orderOf_injective toPermHom (fun _ _ h => RelIso.toEquiv_injective h) g

theorem pow_symm_comm (j : ℕ) (c : α) : (σ ^ j) (g.symm c) = g.symm ((σ ^ j) c) := by
  have h := ((Commute.refl σ).pow_left j).inv_right
  have := congrArg (fun f : Equiv.Perm α => f c) h.eq
  simp only [Equiv.Perm.mul_apply] at this
  exact this

theorem actSetoid_pow {s : Setoid α} (hs : actSetoid g s = s) (k : ℕ) :
    actSetoid (g ^ k) s = s := by
  ext a b
  rw [actSetoid_apply]
  conv_rhs => rw [← (g ^ k).apply_symm_apply a, ← (g ^ k).apply_symm_apply b, coe_pow_aut,
    coe_pow_aut, rel_pow_of_fixed hs]

theorem rel_symm_iff {s : Setoid α} (hs : actSetoid g s = s) (a b : α) :
    s (g.symm a) (g.symm b) ↔ s a b := by
  rw [← actSetoid_apply, hs]

theorem actSetoid_orbit_pow (m : ℕ) : actSetoid g (orbitSetoid (g ^ m)) = orbitSetoid (g ^ m) := by
  ext a b
  rw [actSetoid_apply, orbitSetoid_apply, orbitSetoid_apply]
  simp only [toEquiv_pow, ← pow_mul]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, g.symm.injective (by rw [← pow_symm_comm]; exact hk)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, pow_symm_comm _ _⟩

theorem actSetoid_joinOrbit_pow {s : Setoid α} (hs : actSetoid g s = s) (m : ℕ) :
    actSetoid g (joinOrbit (g ^ m) (actSetoid_pow hs m)) =
      joinOrbit (g ^ m) (actSetoid_pow hs m) := by
  ext a b
  rw [actSetoid_apply, joinOrbit_apply, joinOrbit_apply]
  simp only [toEquiv_pow, ← pow_mul]
  refine exists_congr fun k => ?_
  rw [pow_symm_comm, rel_symm_iff hs]

/-- `x ∈ X(P,g)`: `x ∨ O_g = 1̂`. -/
def IsX (x : OPFixed α g) : Prop := OPFixed.join g x = OPFixed.top g

theorem isX_iff {x : OPFixed α g} : IsX x ↔ ∀ a b, ∃ k : ℕ, x.1 ((σ ^ k) a) b := by
  rw [IsX, ← joinOrbit_eq_top_iff x.2.2]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem isX_top : IsX (OPFixed.top g) := isX_iff.2 fun _ _ => ⟨0, trivial⟩

variable {x : OPFixed α g} {p : α}

/-- `x` relates `u` to `g^j u` iff the number `m` of blocks divides `j`. -/
theorem rel_pow_self_iff (htop : IsX x) (u : α) (j : ℕ) :
    x.1 u ((σ ^ j) u) ↔ per g x p ∣ j := by
  obtain ⟨k, hk⟩ := exists_pow_blk (p := p) htop u
  rw [← rel_pow_of_fixed x.2.2 k, pow_apply_add, add_comm, ← pow_apply_add]
  constructor
  · intro h
    exact per_dvd ((blk_pow_iff hk j).1 (x.1.trans hk h))
  · rintro ⟨q, rfl⟩
    exact x.1.trans (x.1.symm hk) ((blk_pow_iff hk _).2 (blk_pow_per_mul q))

theorem rel_pow_pow_iff (htop : IsX x) (u : α) (a b : ℕ) :
    x.1 ((σ ^ a) u) ((σ ^ b) u) ↔ a ≡ b [MOD per g x p] := by
  rcases le_total a b with h | h
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [← pow_apply_add, rel_pow_of_fixed x.2.2, rel_pow_self_iff htop,
      Nat.modEq_iff_dvd' h, Nat.add_sub_cancel_left]
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [← pow_apply_add, rel_pow_of_fixed x.2.2, Setoid.comm', rel_pow_self_iff htop,
      Nat.ModEq.comm, Nat.modEq_iff_dvd' h, Nat.add_sub_cancel_left]

theorem per_dvd_orderOf : per g x p ∣ orderOf σ :=
  per_dvd (by rw [pow_orderOf_eq_one]; exact x.1.refl p)

theorem per_top : per g (OPFixed.top g) p = 1 :=
  Nat.dvd_one.1 (per_dvd (x := OPFixed.top g) (j := 1) trivial)

theorem per_dvd_of_le {z : OPFixed α g} (hz : z ≤ x) : per g x p ∣ per g z p :=
  per_dvd (hz (per_spec g z p))

theorem hres_eq_one (h : per g x p = orderOf σ) : hres g x p = 1 := by
  refine RelIso.ext fun u => Subtype.ext ?_
  rw [hres_apply_val, h, pow_orderOf_eq_one]
  rfl

/-- If `x ∈ X(P,g)` has `o` blocks, nothing of `X(P,g)` lies strictly below it. -/
theorem eq_of_le_of_per (htopx : IsX x) (hx : per g x p = orderOf σ) {z : OPFixed α g}
    (hz : IsX z) (hzx : z ≤ x) : z = x := by
  refine le_antisymm hzx fun u v huv => ?_
  obtain ⟨k, hk⟩ := (isX_iff.1 hz) u v
  have h2 : x.1 u ((σ ^ k) u) := x.1.trans huv (x.1.symm (hzx hk))
  have h3 := (rel_pow_self_iff (p := p) htopx u k).1 h2
  rw [hx] at h3
  obtain ⟨q, rfl⟩ := h3
  rwa [pow_mul, pow_orderOf_eq_one, one_pow, Equiv.Perm.one_apply] at hk

/-- `O_{g^m}` as an element of `OP(P)^g`. -/
def orbitPow (m : ℕ) : OPFixed α g :=
  ⟨orbitSetoid (g ^ m), isOrderPreserving_orbitSetoid (g ^ m), actSetoid_orbit_pow m⟩

/-- `z ∨ O_{g^m}` in `OP(P)^g`. -/
def joinPow (m : ℕ) (z : OPFixed α g) : OPFixed α g :=
  ⟨joinOrbit (g ^ m) (actSetoid_pow z.2.2 m),
    isOrderPreserving_joinOrbit (actSetoid_pow z.2.2 m) z.2.1, actSetoid_joinOrbit_pow z.2.2 m⟩

theorem joinPow_apply (m : ℕ) (z : OPFixed α g) (a b : α) :
    (joinPow m z).1 a b ↔ ∃ t : ℕ, z.1 ((σ ^ (m * t)) a) b := by
  change (∃ t : ℕ, z.1 (((g ^ m).toEquiv ^ t) a) b) ↔ _
  simp only [toEquiv_pow, ← pow_mul]

theorem orbitPow_le (htop : IsX x) : orbitPow (per g x p) ≤ x := by
  rintro a b ⟨t, rfl⟩
  rw [toEquiv_pow, ← pow_mul, rel_pow_self_iff htop]
  exact Dvd.intro t rfl

theorem joinPow_le_iff (m : ℕ) (z y : OPFixed α g) :
    (z ≤ y ∧ orbitPow m ≤ y) ↔ joinPow m z ≤ y :=
  ⟨fun h => joinOrbit_le (actSetoid_pow z.2.2 m) h.1 h.2,
    fun h => ⟨(le_joinOrbit (actSetoid_pow z.2.2 m)).trans h,
      (orbit_le_joinOrbit (actSetoid_pow z.2.2 m)).trans h⟩⟩

/-- For `z ≤ x ∈ X(P,g)`: `z ∨ O_{g^m} = x` iff `z ∈ X(P,g)`. -/
theorem joinPow_eq_iff (htop : IsX x) {z : OPFixed α g} (hzx : z ≤ x) :
    joinPow (per g x p) z = x ↔ IsX z := by
  constructor
  · intro h
    refine isX_iff.2 fun a b => ?_
    obtain ⟨k, hk⟩ := (isX_iff.1 htop) a b
    rw [← h, joinPow_apply] at hk
    obtain ⟨t, ht⟩ := hk
    exact ⟨per g x p * t + k, by rw [← pow_apply_add]; exact ht⟩
  · intro hz
    refine le_antisymm ((joinPow_le_iff _ z x).1 ⟨hzx, orbitPow_le htop⟩) fun a b hab => ?_
    obtain ⟨k, hk⟩ := (isX_iff.1 hz) a b
    have h2 : x.1 a ((σ ^ k) a) := x.1.trans hab (x.1.symm (hzx hk))
    obtain ⟨t, rfl⟩ := (rel_pow_self_iff (p := p) htop a k).1 h2
    exact (joinPow_apply _ z a b).2 ⟨t, hk⟩

theorem bot_le' (z : OPFixed α g) : OPFixed.bot g ≤ z := fun a b h => by
  rw [OPFixed.bot, Setoid.bot_def] at h; exact h ▸ z.1.refl a

/-- `∑_{z ∈ X(P,g), z ≤ x} μ(0̂, z) = 0` for `x ∈ X(P,g)` with fewer than `o` blocks: Weisner's
theorem in `[0̂, x]` with `a = O_{g^m}`. -/
theorem sum_mu_below_eq_zero (htop : IsX x) (hlt : per g x p ≠ orderOf σ) :
    have := Fintype.ofFinite (OPFixed α g)
    ∑ z ∈ univ.filter (fun z => IsX z ∧ z ≤ x), IncidenceAlgebra.mu ℤ (OPFixed.bot g) z = 0 := by
  intro _
  set m := per g x p
  have hgm : g ^ m ≠ 1 := by
    intro h
    have h1 : orderOf σ ∣ m := by rw [orderOf_toEquiv]; exact orderOf_dvd_of_pow_eq_one h
    exact hlt (Nat.dvd_antisymm per_dvd_orderOf h1)
  let I := {z : OPFixed α g // z ≤ x}
  letI : Fintype I := Fintype.ofFinite I
  letI : LocallyFiniteOrder I := Fintype.toLocallyFiniteOrder
  let botI : I := ⟨OPFixed.bot g, bot_le' x⟩
  let topI : I := ⟨x, le_rfl⟩
  let aI : I := ⟨orbitPow m, orbitPow_le htop⟩
  let jI : I → I := fun z =>
    ⟨joinPow m z.1, (joinPow_le_iff m z.1 x).1 ⟨z.2, orbitPow_le htop⟩⟩
  have hW := weisner botI topI aI (fun z => bot_le' z.1) (fun z => z.2)
    (fun h => orbitSetoid_ne_bot (g ^ m) hgm (congrArg (fun z : I => z.1.1) h)) jI
    (fun z y => joinPow_le_iff m z.1 y.1)
  have hmu : ∀ z : I, IncidenceAlgebra.mu ℤ botI z =
      IncidenceAlgebra.mu ℤ (OPFixed.bot g) z.1 := fun z =>
    (mu_eq_of_interval (fun w : I => w.1) botI z (fun _ _ _ _ _ _ => Iff.rfl)
      (fun y h1 h2 => ⟨⟨y, h2.trans z.2⟩, h1, h2, rfl⟩) z (bot_le' z.1) le_rfl).symm
  rw [Finset.sum_congr rfl fun z _ => hmu z] at hW
  rw [← hW]
  symm
  refine Finset.sum_bij (fun z _ => z.1) ?_ ?_ ?_ ?_
  · intro z hz
    have hz := (mem_filter.1 hz).2
    refine mem_filter.2 ⟨mem_univ _, ?_, z.2⟩
    exact (joinPow_eq_iff htop z.2).1 (congrArg Subtype.val hz)
  · intro z _ z' _ h
    exact Subtype.ext h
  · intro z hz
    obtain ⟨hzX, hzx⟩ := (mem_filter.1 hz).2
    exact ⟨⟨z, hzx⟩, mem_filter.2 ⟨mem_univ _, Subtype.ext ((joinPow_eq_iff htop hzx).2 hzX)⟩, rfl⟩
  · intro z _; rfl

theorem orbitPow_le' (htop : IsX x) {d : ℕ} (hd : per g x p ∣ d) : orbitPow d ≤ x := by
  rintro a b ⟨t, rfl⟩
  rw [toEquiv_pow, ← pow_mul, rel_pow_self_iff htop]
  exact hd.trans (Dvd.intro t rfl)

theorem le_joinPow (d : ℕ) (w : OPFixed α g) : w ≤ joinPow d w :=
  le_joinOrbit (actSetoid_pow w.2.2 d)

theorem isX_joinPow {w : OPFixed α g} (hw : IsX w) (d : ℕ) : IsX (joinPow d w) :=
  isX_iff.2 fun a b => (isX_iff.1 hw a b).imp fun _ hk => le_joinPow d w hk

/-- For `w ∈ F(P,g)` and `d ∣ o`, `w ∨ O_{g^d}` has `d` blocks. -/
theorem per_joinPow {w : OPFixed α g} (hw : IsX w) (hwo : per g w p = orderOf σ) {d : ℕ}
    (hd : d ∣ orderOf σ) : per g (joinPow d w) p = d := by
  have key : ∀ j, (joinPow d w).1 p ((σ ^ j) p) ↔ d ∣ j := by
    intro j
    rw [joinPow_apply]
    constructor
    · rintro ⟨t, ht⟩
      have h1 := (rel_pow_pow_iff (p := p) hw p (d * t) j).1 ht
      rw [hwo] at h1
      exact Nat.modEq_zero_iff_dvd.1
        ((h1.of_dvd hd).symm.trans (Nat.modEq_zero_iff_dvd.2 (dvd_mul_right d t)))
    · rintro ⟨t, rfl⟩
      exact ⟨t, w.1.refl _⟩
  exact Nat.dvd_antisymm (per_dvd ((key d).2 dvd_rfl)) ((key _).1 (per_spec g _ p))

theorem joinPow_le_iff' (htop : IsX x) {w : OPFixed α g} (hwx : w ≤ x) (d : ℕ) :
    joinPow d w ≤ x ↔ per g x p ∣ d := by
  constructor
  · intro h
    exact per_dvd (h ((joinPow_apply d w p _).2 ⟨1, by rw [mul_one]⟩))
  · intro hd
    exact (joinPow_le_iff d w x).1 ⟨hwx, orbitPow_le' htop hd⟩

/-- Every `z ∈ X(P,g)` above `w ∈ X(P,g)` is `w ∨ O_{g^m}`, `m` the number of blocks of `z`. -/
theorem eq_joinPow {w z : OPFixed α g} (hw : IsX w) (hz : IsX z) (hwz : w ≤ z) :
    z = joinPow (per g z p) w := by
  apply Subtype.ext
  ext a b
  change z.1 a b ↔ (joinPow (per g z p) w).1 a b
  rw [joinPow_apply]
  constructor
  · intro hab
    obtain ⟨k, hk⟩ := isX_iff.1 hw a b
    have : z.1 a ((σ ^ k) a) := z.1.trans hab (z.1.symm (hwz hk))
    obtain ⟨t, rfl⟩ := (rel_pow_self_iff (p := p) hz a k).1 this
    exact ⟨t, hk⟩
  · rintro ⟨t, ht⟩
    exact z.1.trans ((rel_pow_self_iff (p := p) hz a _).2 (Dvd.intro t rfl)) (hwz ht)

omit [Fintype α] [DecidableEq α] [PartialOrder α] in
/-- `∑_{q ∣ d ∣ o} μ(o/d) = 0` for `q ∣ o`, `q ≠ o`. -/
theorem sum_moebius_div_filter {o q : ℕ} (ho : 0 < o) (hq : q ∣ o) (hqo : q ≠ o) :
    ∑ d ∈ o.divisors.filter (q ∣ ·), ArithmeticFunction.moebius (o / d) = 0 := by
  obtain ⟨r, rfl⟩ := hq
  have hq0 : 0 < q := Nat.pos_of_mul_pos_right ho
  have hr0 : 0 < r := Nat.pos_of_mul_pos_left ho
  have hr1 : r ≠ 1 := fun h => hqo (by rw [h, mul_one])
  have e1 : ∑ d ∈ (q * r).divisors.filter (q ∣ ·), ArithmeticFunction.moebius (q * r / d) =
      ∑ e ∈ r.divisors, ArithmeticFunction.moebius (r / e) := by
    refine Finset.sum_nbij' (fun d => d / q) (fun e => q * e) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      obtain ⟨hd, hqd⟩ := mem_filter.1 hd
      obtain ⟨e, rfl⟩ := hqd
      show q * e / q ∈ _
      rw [Nat.mul_div_cancel_left _ hq0]
      exact Nat.mem_divisors.2 ⟨Nat.dvd_of_mul_dvd_mul_left hq0 (Nat.mem_divisors.1 hd).1,
        hr0.ne'⟩
    · intro e he
      refine mem_filter.2 ⟨Nat.mem_divisors.2 ⟨Nat.mul_dvd_mul_left q (Nat.mem_divisors.1 he).1,
        (Nat.mul_pos hq0 hr0).ne'⟩, dvd_mul_right q e⟩
    · intro d hd
      obtain ⟨e, rfl⟩ := (mem_filter.1 hd).2
      simp only
      rw [Nat.mul_div_cancel_left _ hq0]
    · intro e _
      simp only
      rw [Nat.mul_div_cancel_left _ hq0]
    · intro d hd
      obtain ⟨e, rfl⟩ := (mem_filter.1 hd).2
      simp only
      rw [Nat.mul_div_cancel_left _ hq0, Nat.mul_div_mul_left _ _ hq0]
  rw [e1, Nat.sum_div_divisors r (fun e => ArithmeticFunction.moebius e),
    ← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
    ArithmeticFunction.one_apply_ne hr1]

variable (g p) in
/-- `F(P,g)` inside `OP(P)^g`: the `x ∈ X(P,g)` with `o` blocks. -/
noncomputable def Fset : Finset (OPFixed α g) :=
  have := Fintype.ofFinite (OPFixed α g)
  univ.filter fun w => IsX w ∧ per g w p = orderOf σ

theorem mem_Fset {w : OPFixed α g} : w ∈ Fset g p ↔ IsX w ∧ per g w p = orderOf σ := by
  simp [Fset]

/-- For `w ∈ F(P,g)` below `x ∈ X(P,g)` with fewer than `o` blocks,
`∑_{z ∈ X(P,g), w ≤ z ≤ x} μ(o / m(z)) = 0`. -/
theorem sum_moebius_between {w : OPFixed α g} (hw : w ∈ Fset g p) (htop : IsX x) (hwx : w ≤ x)
    (hlt : per g x p ≠ orderOf σ) :
    have := Fintype.ofFinite (OPFixed α g)
    ∑ z ∈ univ.filter (fun z => IsX z ∧ w ≤ z ∧ z ≤ x),
      ArithmeticFunction.moebius (orderOf σ / per g z p) = 0 := by
  intro _
  obtain ⟨hwX, hwo⟩ := mem_Fset.1 hw
  rw [← sum_moebius_div_filter (orderOf_pos σ) (per_dvd_orderOf (x := x) (p := p)) hlt]
  refine Finset.sum_nbij' (fun z => per g z p) (fun d => joinPow d w) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    obtain ⟨hzX, hwz, hzx⟩ := (mem_filter.1 hz).2
    exact mem_filter.2 ⟨Nat.mem_divisors.2 ⟨per_dvd_orderOf, (orderOf_pos σ).ne'⟩,
      per_dvd_of_le hzx⟩
  · intro d hd
    obtain ⟨hd, hxd⟩ := mem_filter.1 hd
    exact mem_filter.2 ⟨mem_univ _, isX_joinPow hwX d, le_joinPow d w,
      (joinPow_le_iff' (p := p) htop hwx d).2 hxd⟩
  · intro z hz
    obtain ⟨hzX, hwz, -⟩ := (mem_filter.1 hz).2
    exact (eq_joinPow hwX hzX hwz).symm
  · intro d hd
    exact per_joinPow hwX hwo (Nat.mem_divisors.1 (mem_filter.1 hd).1).1
  · intro z _; rfl

/-- `μ_{OP(P)^g}(0̂, x) = μ(o / m(x)) ∑_{w ∈ F(P,g), w ≤ x} μ_{OP(P)^g}(0̂, w)` for
`x ∈ X(P,g)` with `m(x)` blocks: the Möbius inversion of the note on `X(P,g)`. -/
theorem mu_eq_moebius_mul_sum (htop : IsX x) :
    IncidenceAlgebra.mu ℤ (OPFixed.bot g) x =
      ArithmeticFunction.moebius (orderOf σ / per g x p) *
        ∑ w ∈ (Fset g p).filter (· ≤ x), IncidenceAlgebra.mu ℤ (OPFixed.bot g) w := by
  have := Fintype.ofFinite (OPFixed α g)
  induction x using WellFoundedLT.induction with
  | _ x ih =>
  by_cases hxo : per g x p = orderOf σ
  · have hF : (Fset g p).filter (· ≤ x) = {x} := by
      ext w
      simp only [mem_filter, mem_singleton, mem_Fset]
      constructor
      · rintro ⟨⟨hwX, -⟩, hwx⟩
        exact eq_of_le_of_per htop hxo hwX hwx
      · rintro rfl
        exact ⟨⟨htop, hxo⟩, le_rfl⟩
    rw [hF, sum_singleton, hxo, Nat.div_self (orderOf_pos σ), ArithmeticFunction.moebius_apply_one,
      one_mul]
  · have h0 := sum_mu_below_eq_zero (p := p) htop hxo
    simp only at h0
    have hsplit : univ.filter (fun z => IsX z ∧ z ≤ x) =
        insert x (univ.filter fun z => IsX z ∧ z < x) := by
      ext z
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · rintro ⟨hz, hzx⟩
        rcases eq_or_lt_of_le hzx with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr ⟨hz, hlt⟩
      · rintro (rfl | ⟨hz, hlt⟩)
        · exact ⟨htop, le_rfl⟩
        · exact ⟨hz, hlt.le⟩
    have h0' : ∑ z ∈ insert x (univ.filter fun z => IsX z ∧ z < x),
        IncidenceAlgebra.mu ℤ (OPFixed.bot g) z = 0 := by
      rw [← hsplit]; convert h0
    rw [sum_insert (by simp)] at h0'
    have hrest : ∑ z ∈ univ.filter (fun z => IsX z ∧ z < x),
        IncidenceAlgebra.mu ℤ (OPFixed.bot g) z =
        ∑ w ∈ (Fset g p).filter (· ≤ x), IncidenceAlgebra.mu ℤ (OPFixed.bot g) w *
          ∑ z ∈ univ.filter (fun z => IsX z ∧ w ≤ z ∧ z < x),
            ArithmeticFunction.moebius (orderOf σ / per g z p) := by
      rw [Finset.sum_congr rfl fun z hz => ih z (mem_filter.1 hz).2.2 (mem_filter.1 hz).2.1]
      simp only [Finset.mul_sum]
      refine Finset.sum_comm' ?_ |>.trans (Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => mul_comm _ _)
      intro z w
      simp only [mem_filter, mem_univ, true_and, mem_Fset]
      constructor
      · rintro ⟨⟨hz, hzx⟩, hw, hwz⟩
        exact ⟨⟨hz, hwz, hzx⟩, hw, hwz.trans hzx.le⟩
      · rintro ⟨⟨hz, hwz, hzx⟩, hw, -⟩
        exact ⟨⟨hz, hzx⟩, hw, hwz⟩
    have hinner : ∀ w ∈ (Fset g p).filter (· ≤ x),
        ∑ z ∈ univ.filter (fun z => IsX z ∧ w ≤ z ∧ z < x),
          ArithmeticFunction.moebius (orderOf σ / per g z p) =
        -ArithmeticFunction.moebius (orderOf σ / per g x p) := by
      intro w hw
      obtain ⟨hwF, hwx⟩ := mem_filter.1 hw
      have h := sum_moebius_between hwF htop hwx hxo
      simp only at h
      have hsplit' : univ.filter (fun z => IsX z ∧ w ≤ z ∧ z ≤ x) =
          insert x (univ.filter fun z => IsX z ∧ w ≤ z ∧ z < x) := by
        ext z
        simp only [mem_filter, mem_univ, true_and, mem_insert]
        constructor
        · rintro ⟨hz, hwz, hzx⟩
          rcases eq_or_lt_of_le hzx with rfl | hlt
          · exact Or.inl rfl
          · exact Or.inr ⟨hz, hwz, hlt⟩
        · rintro (rfl | ⟨hz, hwz, hlt⟩)
          · exact ⟨htop, hwx, le_rfl⟩
          · exact ⟨hz, hwz, hlt.le⟩
      have h' : ∑ z ∈ insert x (univ.filter fun z => IsX z ∧ w ≤ z ∧ z < x),
          ArithmeticFunction.moebius (orderOf σ / per g z p) = 0 := by
        rw [← hsplit']; convert h
      rw [sum_insert (by simp)] at h'
      linarith
    rw [hrest, Finset.sum_congr rfl fun w hw => by rw [hinner w hw]] at h0'
    simp only [mul_neg, Finset.sum_neg_distrib, ← Finset.sum_mul] at h0'
    linarith

end Inversion

/-! ### Proposition `prop:Mside` -/

section Mside

open scoped Classical

variable {g : α ≃o α}

local notation "σ" => g.toEquiv

theorem Mt_eq_sum_Fset (p : α) :
    Mt g = ArithmeticFunction.moebius (orderOf σ) * ∑ w ∈ Fset g p, (eC (Blk g w p) : ℤ) := by
  have := Fintype.ofFinite (OPFixed α g)
  have h := mu_eq_moebius_mul_sum (p := p) (isX_top (g := g))
  rw [per_top, Nat.div_one] at h
  have hF : (Fset g p).filter (· ≤ OPFixed.top g) = Fset g p :=
    Finset.filter_true_of_mem fun w _ u v _ => trivial
  rw [hF] at h
  have hterm : ∀ w ∈ Fset g p, (-1) ^ (Fintype.card α + 1) *
      ((Equiv.Perm.sign g.toEquiv : ℤˣ) : ℤ) * IncidenceAlgebra.mu ℤ (OPFixed.bot g) w =
      (eC (Blk g w p) : ℤ) := by
    intro w hw
    obtain ⟨hwX, hwo⟩ := mem_Fset.1 hw
    have hk : 0 < Fintype.card (Blk g w p) := Fintype.card_pos_iff.2 ⟨⟨p, w.1.refl p⟩⟩
    rw [interval_sign hwX, mu_interval hwX]
    change Mt (hres g w p) = _
    rw [hres_eq_one hwo, Mt_one hk]
  rw [Mt, muFixed, h, mul_left_comm, Finset.mul_sum, Finset.sum_congr rfl hterm]

/-- The block of `w` through `p`, as a `Finset`. -/
noncomputable def blkSet (w : OPFixed α g) (p : α) : Finset α := univ.filter fun a => w.1 p a

theorem mem_blkSet {w : OPFixed α g} {p a : α} : a ∈ blkSet w p ↔ w.1 p a := by
  simp [blkSet]

theorem coe_pow_eq (j : ℕ) : ⇑(g ^ j) = ⇑(σ ^ j) := funext (coe_pow_aut j)

theorem inF_blocksOf_blkSet {w : OPFixed α g} {p : α} (hw : w ∈ Fset g p) :
    InF g (blocksOf g (blkSet w p)) := by
  obtain ⟨hwX, hwo⟩ := mem_Fset.1 hw
  have htop' : joinOrbit g w.2.2 = ⊤ := congrArg Subtype.val hwX
  refine inF_blocksOf ⟨p, mem_blkSet.2 (w.1.refl p)⟩ ?_ ⟨?_, ?_⟩
  · intro a b hab
    rw [mem_blkSet, mem_blkSet]
    have := rel_of_le_of_joinOrbit_eq_top w.2.2 w.2.1 htop' hab
    exact ⟨fun h => w.1.trans h this, fun h => w.1.trans h (w.1.symm this)⟩
  · intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [coe_pow_eq] at hu hu'
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hu
    obtain ⟨b, hb, hab⟩ := mem_image.1 hu'
    rw [mem_blkSet] at ha hb
    have h1 : w.1 ((σ ^ j) a) ((σ ^ i) a) := by
      rw [← hab, rel_pow_of_fixed w.2.2]; exact w.1.trans (w.1.symm ha) hb
    have h2 := (rel_pow_pow_iff (p := p) hwX a j i).1 h1
    rw [hwo, orderOf_toEquiv] at h2
    exact hij (Nat.ModEq.eq_of_lt_of_lt h2 hj hi).symm
  · intro u
    obtain ⟨⟨j, v⟩, hjv⟩ := blkMap_surjective (p := p) hwX u
    refine ⟨j, by rw [← orderOf_toEquiv, ← hwo]; exact j.2, ?_⟩
    rw [coe_pow_eq]
    exact mem_image.2 ⟨v.1, mem_blkSet.2 v.2, hjv⟩

theorem rel_iff_blk {w : OPFixed α g} {p : α} (hwX : IsX w) (u v : α) :
    w.1 u v ↔ ∃ k : ℕ, w.1 p ((σ ^ k) u) ∧ w.1 p ((σ ^ k) v) := by
  constructor
  · intro huv
    obtain ⟨k, hk⟩ := exists_pow_blk (p := p) hwX u
    exact ⟨k, hk, w.1.trans hk ((rel_pow_of_fixed w.2.2 k u v).2 huv)⟩
  · rintro ⟨k, hu, hv⟩
    exact (rel_pow_of_fixed w.2.2 k u v).1 (w.1.trans (w.1.symm hu) hv)

/-- The partition with the blocks of `x ∈ F(P,g)`. -/
def setoidOfBlocks {x : Finset (Finset α)} (hx : InF g x) : Setoid α where
  r u v := ∃ B ∈ x, u ∈ B ∧ v ∈ B
  iseqv := by
    obtain ⟨-, -, hdisj, hcov, -, -⟩ := hx
    refine ⟨fun u => ?_, fun ⟨B, hB, hu, hv⟩ => ⟨B, hB, hv, hu⟩, ?_⟩
    · obtain ⟨B, hB, hu⟩ := hcov u
      exact ⟨B, hB, hu, hu⟩
    · rintro u v w ⟨B, hB, hu, hv⟩ ⟨B', hB', hv', hw⟩
      by_cases e : B = B'
      · exact ⟨B, hB, hu, e ▸ hw⟩
      · exact absurd (Finset.disjoint_left.1 (hdisj B hB B' hB' e) hv hv') id

theorem eq_of_mem_blocks {x : Finset (Finset α)} (hx : InF g x) {B B' : Finset α} (hB : B ∈ x)
    (hB' : B' ∈ x) {u : α} (hu : u ∈ B) (hu' : u ∈ B') : B = B' := by
  by_contra e
  exact Finset.disjoint_left.1 (hx.2.2.1 B hB B' hB' e) hu hu'

theorem image_pow_mem {x : Finset (Finset α)} (hx : InF g x) {B : Finset α} (hB : B ∈ x)
    (j : ℕ) : B.image ⇑(g ^ j) ∈ x := by
  induction j with
  | zero => rwa [coe_pow_zero, image_id]
  | succ j ih =>
    rw [coe_pow_succ, ← image_image]
    exact hx.2.2.2.2.1 _ ih

/-- `x ∈ F(P,g)` as an element of `OP(P)^g`. -/
noncomputable def opOfBlocks {x : Finset (Finset α)} (hx : InF g x) : OPFixed α g :=
  ⟨setoidOfBlocks hx,
    isOrderPreserving_of_rel_of_le fun a b hab => by
      obtain ⟨B, hB, ha⟩ := hx.2.2.2.1 a
      exact ⟨B, hB, ha, ((hx.2.1 B hB).2 a b hab).1 ha⟩,
    by
      ext u v
      rw [actSetoid_apply]
      change (∃ B ∈ x, g.symm u ∈ B ∧ g.symm v ∈ B) ↔ ∃ B ∈ x, u ∈ B ∧ v ∈ B
      constructor
      · rintro ⟨B, hB, hu, hv⟩
        refine ⟨B.image g, hx.2.2.2.2.1 B hB, ?_, ?_⟩
        · exact mem_image.2 ⟨_, hu, g.apply_symm_apply u⟩
        · exact mem_image.2 ⟨_, hv, g.apply_symm_apply v⟩
      · rintro ⟨B, hB, hu, hv⟩
        obtain ⟨B'', hB'', hu''⟩ := hx.2.2.2.1 (g.symm u)
        have himg := hx.2.2.2.2.1 B'' hB''
        have e : B''.image g = B :=
          eq_of_mem_blocks hx himg hB (mem_image.2 ⟨_, hu'', g.apply_symm_apply u⟩) hu
        rw [← e] at hv
        obtain ⟨c, hc, hcv⟩ := mem_image.1 hv
        refine ⟨B'', hB'', hu'', ?_⟩
        rw [← hcv, g.symm_apply_apply]
        exact hc⟩

theorem opOfBlocks_mem_Fset {x : Finset (Finset α)} (hx : InF g x) (p : α) :
    opOfBlocks hx ∈ Fset g p := by
  have hX : IsX (opOfBlocks hx) := by
    refine isX_iff.2 fun a b => ?_
    obtain ⟨B, hB, ha⟩ := hx.2.2.2.1 a
    obtain ⟨B', hB', hb⟩ := hx.2.2.2.1 b
    obtain ⟨k, rfl⟩ := hx.2.2.2.2.2 B hB B' hB'
    refine ⟨k, B.image ⇑(g ^ k), hB', ?_, hb⟩
    rw [coe_pow_eq]
    exact mem_image_of_mem _ ha
  refine mem_Fset.2 ⟨hX, Nat.dvd_antisymm per_dvd_orderOf ?_⟩
  obtain ⟨B, hB, hp⟩ := hx.2.2.2.1 p
  set m := per g (opOfBlocks hx) p
  have hm := per_pos g (opOfBlocks hx) p
  obtain ⟨B1, hB1, hp1, hmp⟩ := per_spec g (opOfBlocks hx) p
  have e1 : B1 = B := eq_of_mem_blocks hx hB1 hB hp1 hp
  subst e1
  have hsys := (blocksOf_of_inF hx hB1).2
  rw [orderOf_toEquiv]
  by_contra hdvd
  have hlt : m < orderOf g := by
    have := Nat.le_of_dvd (orderOf_pos_aut g)
      (orderOf_toEquiv (g := g) ▸ per_dvd_orderOf (x := opOfBlocks hx) (p := p))
    rcases this.lt_or_eq with h | h
    · exact h
    · exact absurd (h ▸ dvd_rfl) hdvd
  have hd := hsys.1 m hlt 0 (orderOf_pos_aut g) hm.ne'
  rw [coe_pow_zero, image_id, coe_pow_eq] at hd
  exact Finset.disjoint_left.1 hd (mem_image_of_mem _ hp1) hmp

theorem blkSet_opOfBlocks {x : Finset (Finset α)} (hx : InF g x) {B : Finset α} (hB : B ∈ x)
    {p : α} (hp : p ∈ B) : blkSet (opOfBlocks hx) p = B := by
  ext a
  rw [mem_blkSet]
  constructor
  · rintro ⟨B', hB', hp', ha⟩
    exact eq_of_mem_blocks hx hB' hB hp' hp ▸ ha
  · intro ha
    exact ⟨B, hB, hp, ha⟩

/-- `e_C(P|_{B₀(w)})` for the block through `p`, as a subtype or as a `Finset`. -/
theorem eC_blk_eq (w : OPFixed α g) (p : α) : eC (Blk g w p) = eC (blkSet w p) := by
  refine eC_congr
    { toEquiv := Equiv.subtypeEquivRight fun a => mem_blkSet.symm
      map_rel_iff' := Iff.rfl }

open Classical in
/-- **Proposition `prop:Mside`** (the Möbius side of (closed)), homology-free: for `n ≥ 1`,
`g ∈ Aut(P)` of order `o` and any choice `B₀(x)` of one block of each `x ∈ F(P,g)`,
`M̃(P,g) = (-1)^{n-3} sgn(g) μ(OP(P)^g) = μ(o) ∑_{x ∈ F(P,g)} e_C(P|_{B₀(x)})`. -/
theorem prop_Mside (h0 : 0 < Fintype.card α) (g : α ≃o α)
    (B₀ : Finset (Finset α) → Finset α) (hB₀ : ∀ x, InF g x → B₀ x ∈ x) :
    Mt g = ArithmeticFunction.moebius (orderOf g) *
      ∑ x ∈ (univ : Finset (Finset (Finset α))).filter (InF g), (eC (B₀ x) : ℤ) := by
  obtain ⟨p⟩ : Nonempty α := Fintype.card_pos_iff.1 h0
  rw [Mt_eq_sum_Fset p, orderOf_toEquiv]
  congr 1
  refine Finset.sum_bij (fun w _ => blocksOf g (blkSet w p)) ?_ ?_ ?_ ?_
  · intro w hw
    exact mem_filter.2 ⟨mem_univ _, inF_blocksOf_blkSet hw⟩
  · intro w hw w' hw' e
    obtain ⟨hwX, hwo⟩ := mem_Fset.1 hw
    obtain ⟨hwX', hwo'⟩ := mem_Fset.1 hw'
    -- the block of `w` through `p` is a block of `w'`, hence `w'`'s block through `p`
    have e' : blocksOf g (blkSet w p) = blocksOf g (blkSet w' p) := e
    have hmem : blkSet w p ∈ blocksOf g (blkSet w' p) := e' ▸ self_mem_blocksOf g _
    obtain ⟨j, hj, hjB⟩ := mem_image.1 hmem
    have hp : p ∈ (blkSet w' p).image ⇑(g ^ j) := by
      rw [hjB]; exact mem_blkSet.2 (w.1.refl p)
    rw [coe_pow_eq] at hp
    obtain ⟨a, ha, hap⟩ := mem_image.1 hp
    have ha' : w'.1 p a := mem_blkSet.1 ha
    have h1 : w'.1 a ((g.toEquiv ^ j) a) := by
      have : (g.toEquiv ^ j) a = p := hap
      rw [this]; exact w'.1.symm ha'
    have h2 := (rel_pow_self_iff (p := p) hwX' a j).1 h1
    rw [hwo', orderOf_toEquiv] at h2
    have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt h2 (mem_range.1 hj)
    rw [hj0, coe_pow_zero, image_id] at hjB
    apply Subtype.ext
    ext u v
    rw [rel_iff_blk (p := p) hwX, rel_iff_blk (p := p) hwX']
    have hiff : ∀ c, w.1 p c ↔ w'.1 p c := fun c => by
      rw [← mem_blkSet, ← mem_blkSet, hjB]
    simp only [hiff]
  · intro x hx
    have hxF := (mem_filter.1 hx).2
    obtain ⟨B, hB, hp⟩ := hxF.2.2.2.1 p
    refine ⟨opOfBlocks hxF, opOfBlocks_mem_Fset hxF p, ?_⟩
    show blocksOf g (blkSet (opOfBlocks hxF) p) = x
    rw [blkSet_opOfBlocks hxF hB hp]
    exact ((blocksOf_of_inF hxF hB).1).symm
  · intro w hw
    have hx := hB₀ _ (inF_blocksOf_blkSet hw)
    obtain ⟨j, -, hj⟩ := mem_image.1 hx
    rw [eC_blk_eq, ← hj, eC_image]

end Mside

end PosetJKS

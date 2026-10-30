import PosetJKS.OPLattice

/-!
# The interval lemma and the recursion (W)

`notes/poset_jks_theorem.tex`, Lemma `lem:interval`(i) and the recursion (W) in the proof of
Proposition `prop:Mside`, in unsigned form.

* `mu_eq_of_interval`: Möbius values are invariant under a map that is an order isomorphism of
  the interval `[a, b]` onto the interval `[f a, f b]`.
* For `x ∈ OP(P)^g` with `x ∨ O_g = 1̂` (i.e. `x ∈ X(P,g)`) and a point `p`, let `B₀ = Blk g x p`
  be the block of `x` containing `p`, `m = per g x p` the least `m > 0` with `g^m B₀ = B₀`, and
  `h = hres g x p = g^m|_{B₀} ∈ Aut(P|_{B₀})`.
* `mu_interval`: `μ_{OP(P)^g}(0̂, x) = μ(OP(P|_{B₀})^h)` (Lemma `lem:interval`(i)). The map is
  restriction to `B₀` (`resP`), with inverse `liftP` (spread a partition of `B₀` over the blocks
  `g^j B₀`).
* `recursionW`: for `g ≠ 1`, `∑_{x ∈ X(P,g)} μ(OP(P|_{B₀(x)})^{h_x}) = 0`.

The sign bookkeeping `(-1)^{n-3} sgn(g) = (-1)^{k-3} sgn(h)` (Lemma `lem:interval`(ii)), which
turns this into the note's signed form of (W), is not formalized here.
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

/-! ### Möbius values of isomorphic intervals -/

section MuInterval

variable {L M : Type*} [PartialOrder L] [PartialOrder M] [LocallyFiniteOrder L]
  [LocallyFiniteOrder M] [DecidableEq L] [DecidableEq M] [Finite L]

/-- If `f` maps `[a, b]` order-isomorphically onto `[f a, f b]`, then
`μ(f a, f x) = μ(a, x)` for `x ∈ [a, b]`. -/
theorem mu_eq_of_interval (f : L → M) (a b : L)
    (hle : ∀ x y, a ≤ x → x ≤ b → a ≤ y → y ≤ b → (f x ≤ f y ↔ x ≤ y))
    (hsurj : ∀ y, f a ≤ y → y ≤ f b → ∃ x, a ≤ x ∧ x ≤ b ∧ f x = y) :
    ∀ x, a ≤ x → x ≤ b → IncidenceAlgebra.mu ℤ (f a) (f x) = IncidenceAlgebra.mu ℤ a x := by
  have hinj : ∀ y z, a ≤ y → y ≤ b → a ≤ z → z ≤ b → f y = f z → y = z :=
    fun y z h1 h2 h3 h4 h =>
      le_antisymm ((hle y z h1 h2 h3 h4).1 h.le) ((hle z y h3 h4 h1 h2).1 h.ge)
  intro x
  induction x using WellFoundedLT.induction with
  | _ x ih =>
  intro hax hxb
  rw [IncidenceAlgebra.mu_apply, IncidenceAlgebra.mu_apply]
  by_cases hx : a = x
  · subst hx; simp
  have hfx : f a ≠ f x := fun h => hx (hinj _ _ le_rfl (hax.trans hxb) hax hxb h)
  rw [if_neg hx, if_neg hfx, neg_inj]
  symm
  refine Finset.sum_bij (fun z _ => f z) ?_ ?_ ?_ ?_
  · intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hz
    have hzb := h2.le.trans hxb
    exact Finset.mem_Ico.2 ⟨(hle a z le_rfl (hax.trans hxb) h1 hzb).2 h1,
      lt_of_le_of_ne ((hle z x h1 hzb hax hxb).2 h2.le)
        fun h => h2.ne (hinj _ _ h1 hzb hax hxb h)⟩
  · intro z1 hz1 z2 hz2 h
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hz1
    obtain ⟨h3, h4⟩ := Finset.mem_Ico.1 hz2
    exact hinj _ _ h1 (h2.le.trans hxb) h3 (h4.le.trans hxb) h
  · intro y hy
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hy
    have hfxb : f x ≤ f b := (hle x b hax hxb (hax.trans hxb) le_rfl).2 hxb
    obtain ⟨z, hz1, hz2, rfl⟩ := hsurj y h1 (h2.le.trans hfxb)
    refine ⟨z, Finset.mem_Ico.2 ⟨(hle a z le_rfl (hax.trans hxb) hz1 hz2).1 h1,
      lt_of_le_of_ne ((hle z x hz1 hz2 hax hxb).1 h2.le) fun h => h2.ne (h ▸ rfl)⟩, rfl⟩
  · intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hz
    exact (ih z h2 h1 (h2.le.trans hxb)).symm

end MuInterval

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

theorem pow_le_pow_iff_of_toEquiv (g : α ≃o α) (k : ℕ) (u v : α) :
    (g.toEquiv ^ k) u ≤ (g.toEquiv ^ k) v ↔ u ≤ v := by
  refine ⟨fun h => ?_, fun h => monotone_pow g k h⟩
  have := monotone_pow g (orderOf g.toEquiv * k - k) h
  rwa [pow_inv_apply, pow_inv_apply] at this

theorem pow_add_orderOf_mul (g : α ≃o α) (j i : ℕ) :
    g.toEquiv ^ (j + orderOf g.toEquiv * i) = g.toEquiv ^ j := by
  rw [pow_add, pow_mul, pow_orderOf_eq_one, one_pow, mul_one]

/-! ### The block `B₀` of `x ∈ OP(P)^g` through `p`, and `h = g^m|_{B₀}` -/

section Block

open scoped Classical

variable (g : α ≃o α) (x : OPFixed α g) (p : α)

local notation "σ" => g.toEquiv

/-- The block `B₀` of `x` containing `p`, as an induced subposet. -/
abbrev Blk := {a : α // x.1 p a}

variable {g x p} in
/-- For `a ∈ B₀`, `g^j a ∈ B₀` iff `g^j p ∈ B₀`. -/
theorem blk_pow_iff {a : α} (ha : x.1 p a) (j : ℕ) :
    x.1 p ((σ ^ j) a) ↔ x.1 p ((σ ^ j) p) := by
  have h := (rel_pow_of_fixed x.2.2 j p a).2 ha
  exact ⟨fun h' => x.1.trans h' (x.1.symm h), fun h' => x.1.trans h' h⟩

theorem exists_per : ∃ j, 0 < j ∧ x.1 p ((σ ^ j) p) :=
  ⟨orderOf σ, orderOf_toEquiv_pos g, by rw [pow_orderOf_eq_one]; exact x.1.refl p⟩

/-- `m`: the least `m > 0` with `g^m B₀ = B₀`. -/
noncomputable def per : ℕ := Nat.find (exists_per g x p)

theorem per_pos : 0 < per g x p := (Nat.find_spec (exists_per g x p)).1

theorem per_spec : x.1 p ((σ ^ per g x p) p) := (Nat.find_spec (exists_per g x p)).2

variable {g x p} in
theorem blk_pow_per_mul (q : ℕ) : x.1 p ((σ ^ (per g x p * q)) p) := by
  induction q with
  | zero => simp only [mul_zero, pow_zero, Equiv.Perm.one_apply]; exact x.1.refl p
  | succ q ih =>
    rw [mul_add_one, add_comm, ← pow_apply_add]
    exact (blk_pow_iff ih _).2 (per_spec g x p)

variable {g x p} in
/-- The stabiliser of `B₀` in `⟨g⟩` is generated by `g^m`. -/
theorem per_dvd {j : ℕ} (hj : x.1 p ((σ ^ j) p)) : per g x p ∣ j := by
  set m := per g x p
  have hr : x.1 p ((σ ^ (j % m)) p) := by
    have h := blk_pow_iff (blk_pow_per_mul (p := p) (x := x) (j / m)) (j % m)
    rw [pow_apply_add, Nat.mod_add_div] at h
    exact h.1 hj
  refine Nat.dvd_of_mod_eq_zero (Nat.eq_zero_of_not_pos fun hpos => ?_)
  exact Nat.find_min (exists_per g x p) (Nat.mod_lt j (per_pos g x p)) ⟨hpos, hr⟩

theorem blk_iff_pow_per (a : α) : x.1 p a ↔ x.1 p ((σ ^ per g x p) a) := by
  constructor
  · intro ha; exact (blk_pow_iff ha _).2 (per_spec g x p)
  · intro ha
    have h : x.1 ((σ ^ per g x p) p) ((σ ^ per g x p) a) :=
      x.1.trans (x.1.symm (per_spec g x p)) ha
    exact (rel_pow_of_fixed x.2.2 _ p a).1 h

/-- `h = g^m|_{B₀} ∈ Aut(P|_{B₀})`. -/
noncomputable def hres : Blk g x p ≃o Blk g x p where
  toEquiv := (σ ^ per g x p).subtypeEquiv (blk_iff_pow_per g x p)
  map_rel_iff' {a b} := by
    change (σ ^ per g x p) a.1 ≤ (σ ^ per g x p) b.1 ↔ a.1 ≤ b.1
    exact pow_le_pow_iff_of_toEquiv g _ _ _

theorem hres_apply_val (u : Blk g x p) : (hres g x p u).1 = (σ ^ per g x p) u.1 := rfl

theorem hres_pow_val (t : ℕ) (u : Blk g x p) :
    (((hres g x p).toEquiv ^ t) u).1 = (σ ^ (per g x p * t)) u.1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    change (hres g x p (((hres g x p).toEquiv ^ t) u)).1 = _
    rw [hres_apply_val, ih, pow_apply_add, mul_add_one, add_comm]

/-! ### Restriction `[0̂, x] → OP(P|_{B₀})^h` -/

theorem reach_val {π : Setoid α} {a b : Blk g x p}
    (h : Reach (π.comap Subtype.val) a b) : Reach π a.1 b.1 := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    refine ih.tail ?_
    rcases hbc with hbc | hbc
    · exact Or.inl hbc
    · exact Or.inr hbc

/-- Restriction of a partition in `OP(P)^g` to `B₀`. -/
def resP (π : OPFixed α g) : OPFixed (Blk g x p) (hres g x p) :=
  ⟨π.1.comap Subtype.val,
    fun a b hab hba => π.2.1 _ _ (reach_val g x p hab) (reach_val g x p hba),
    by
      ext a b
      rw [actSetoid_apply]
      change π.1 ((hres g x p).symm a).1 ((hres g x p).symm b).1 ↔ π.1 a.1 b.1
      rw [← rel_pow_of_fixed π.2.2 (per g x p), ← hres_apply_val, ← hres_apply_val,
        OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]⟩

theorem resP_mono {π π' : OPFixed α g} (h : π ≤ π') : resP g x p π ≤ resP g x p π' :=
  fun _ _ hab => h hab

theorem resP_bot : resP g x p (OPFixed.bot g) = OPFixed.bot (hres g x p) := by
  apply Subtype.ext
  ext a b
  change (⊥ : Setoid α) a.1 b.1 ↔ (⊥ : Setoid (Blk g x p)) a b
  rw [Setoid.bot_def, Setoid.bot_def]
  exact Subtype.ext_iff.symm

theorem resP_self : resP g x p x = OPFixed.top (hres g x p) := by
  apply Subtype.ext
  ext a b
  change x.1 a.1 b.1 ↔ (⊤ : Setoid (Blk g x p)) a b
  rw [Setoid.top_def]
  exact ⟨fun _ => trivial, fun _ => x.1.trans (x.1.symm a.2) b.2⟩

variable {g x p}

theorem resP_reflect (htop : OPFixed.join g x = OPFixed.top g) {π π' : OPFixed α g}
    (hπ : π ≤ x) (h : resP g x p π ≤ resP g x p π') : π ≤ π' := by
  intro a b hab
  have htop' : joinOrbit g x.2.2 = ⊤ := congrArg Subtype.val htop
  obtain ⟨k, hk⟩ := (joinOrbit_eq_top_iff x.2.2).1 htop' a p
  have hxab : x.1 a b := hπ hab
  have ha : x.1 p ((σ ^ k) a) := x.1.symm hk
  have hb : x.1 p ((σ ^ k) b) := x.1.trans ha ((rel_pow_of_fixed x.2.2 k a b).2 hxab)
  have : (resP g x p π).1 ⟨_, ha⟩ ⟨_, hb⟩ := (rel_pow_of_fixed π.2.2 k a b).2 hab
  exact (rel_pow_of_fixed π'.2.2 k a b).1 (h this)

/-! ### Lifting `OP(P|_{B₀})^h → [0̂, x]` -/

variable (τ : OPFixed (Blk g x p) (hres g x p))

/-- `τ` on values: `u ~ v` iff `u, v ∈ B₀` and `⟨u⟩ ~_τ ⟨v⟩`. -/
def tauV (u v : α) : Prop := ∃ (hu : x.1 p u) (hv : x.1 p v), τ.1 ⟨u, hu⟩ ⟨v, hv⟩

theorem tauV_symm {u v : α} (h : tauV τ u v) : tauV τ v u := by
  obtain ⟨hu, hv, h⟩ := h
  exact ⟨hv, hu, τ.1.symm h⟩

theorem tauV_trans {u v w : α} (h1 : tauV τ u v) (h2 : tauV τ v w) : tauV τ u w := by
  obtain ⟨hu, _, h1⟩ := h1
  obtain ⟨_, hw, h2⟩ := h2
  exact ⟨hu, hw, τ.1.trans h1 h2⟩

/-- Independence of the translate: if `g^i a, g^i b, g^j a, g^j b ∈ B₀`, then
`g^i a ~_τ g^i b` iff `g^j a ~_τ g^j b` (`g^{j-i}` acts on `B₀` as a power of `h`). -/
theorem tauV_indep {a b : α} {i j : ℕ} (hia : x.1 p ((σ ^ i) a)) (hib : x.1 p ((σ ^ i) b))
    (hja : x.1 p ((σ ^ j) a)) (hjb : x.1 p ((σ ^ j) b)) :
    tauV τ ((σ ^ i) a) ((σ ^ i) b) ↔ tauV τ ((σ ^ j) a) ((σ ^ j) b) := by
  set d := j + (orderOf σ * i - i)
  have hd : ∀ c, (σ ^ d) ((σ ^ i) c) = (σ ^ j) c := fun c => by
    rw [pow_apply_add, add_assoc, Nat.sub_add_cancel
      (Nat.le_mul_of_pos_left i (orderOf_toEquiv_pos g)), pow_add_orderOf_mul]
  have hdp : x.1 p ((σ ^ d) p) := by
    have := (blk_pow_iff hia d).1
    rw [hd] at this
    exact this hja
  obtain ⟨t, ht⟩ := per_dvd hdp
  have hval : ∀ c (hc : x.1 p ((σ ^ i) c)),
      (((hres g x p).toEquiv ^ t) ⟨_, hc⟩).1 = (σ ^ j) c := fun c hc => by
    rw [hres_pow_val, ← ht, hd]
  have key := rel_pow_of_fixed τ.2.2 t ⟨_, hia⟩ ⟨_, hib⟩
  have e1 : ((hres g x p).toEquiv ^ t) ⟨_, hia⟩ = ⟨_, hja⟩ := Subtype.ext (hval a hia)
  have e2 : ((hres g x p).toEquiv ^ t) ⟨_, hib⟩ = ⟨_, hjb⟩ := Subtype.ext (hval b hib)
  rw [e1, e2] at key
  exact ⟨fun ⟨_, _, h⟩ => ⟨hja, hjb, key.2 h⟩, fun ⟨_, _, h⟩ => ⟨hia, hib, key.1 h⟩⟩

theorem blk_of_rel {a b : α} {j : ℕ} (ha : x.1 p ((σ ^ j) a)) (hab : x.1 a b) :
    x.1 p ((σ ^ j) b) :=
  x.1.trans ha ((rel_pow_of_fixed x.2.2 j a b).2 hab)

variable (htop : OPFixed.join g x = OPFixed.top g)
include htop

omit htop in
theorem exists_pow_blk (htop : OPFixed.join g x = OPFixed.top g) (a : α) :
    ∃ k, x.1 p ((σ ^ k) a) := by
  have htop' : joinOrbit g x.2.2 = ⊤ := congrArg Subtype.val htop
  obtain ⟨k, hk⟩ := (joinOrbit_eq_top_iff x.2.2).1 htop' a p
  exact ⟨k, x.1.symm hk⟩

/-- The lift of `τ`: `a ~ b` iff `a ~_x b` and `g^j a ~_τ g^j b` for a (any) `j` with
`g^j a ∈ B₀`. -/
def liftS : Setoid α where
  r a b := x.1 a b ∧ ∃ j, x.1 p ((σ ^ j) a) ∧ tauV τ ((σ ^ j) a) ((σ ^ j) b)
  iseqv :=
    ⟨fun a => (by
      obtain ⟨k, hk⟩ := exists_pow_blk htop a
      exact ⟨x.1.refl a, k, hk, hk, hk, τ.1.refl _⟩),
     fun {a b} ⟨hab, j, hj, h⟩ => ⟨x.1.symm hab, j, blk_of_rel hj hab, tauV_symm τ h⟩,
     fun {a b c} ⟨hab, j, hj, h1⟩ ⟨hbc, j', hj', h2⟩ => (by
      refine ⟨x.1.trans hab hbc, j, hj, tauV_trans τ h1 ?_⟩
      exact (tauV_indep τ hj' (blk_of_rel hj' hbc) (blk_of_rel hj hab)
        (blk_of_rel hj (x.1.trans hab hbc))).1 h2)⟩

theorem liftS_iff {a b : α} {j : ℕ} (hj : x.1 p ((σ ^ j) a)) :
    liftS τ htop a b ↔ x.1 a b ∧ tauV τ ((σ ^ j) a) ((σ ^ j) b) := by
  constructor
  · rintro ⟨hab, i, hi, h⟩
    exact ⟨hab, (tauV_indep τ hi (blk_of_rel hi hab) hj (blk_of_rel hj hab)).1 h⟩
  · rintro ⟨hab, h⟩
    exact ⟨hab, j, hj, h⟩

theorem liftS_pow_one (a b : α) : liftS τ htop (σ a) (σ b) ↔ liftS τ htop a b := by
  obtain ⟨j, hj⟩ := exists_pow_blk htop a
  have hs : ∀ c, (σ ^ (j + (orderOf σ * 1 - 1))) (σ c) = (σ ^ j) c := fun c => by
    rw [← pow_apply_add]
    have := pow_inv_apply g 1 c
    rw [pow_one] at this
    rw [this]
  have hj' : x.1 p ((σ ^ (j + (orderOf σ * 1 - 1))) (σ a)) := by rw [hs]; exact hj
  rw [liftS_iff τ htop hj', liftS_iff τ htop hj, hs, hs]
  have := rel_pow_of_fixed x.2.2 1 a b
  rw [pow_one] at this
  rw [this]

theorem actSetoid_liftS : actSetoid g (liftS τ htop) = liftS τ htop := by
  ext a b
  rw [actSetoid_apply, ← liftS_pow_one τ htop]
  change liftS τ htop (g (g.symm a)) (g (g.symm b)) ↔ _
  rw [g.apply_symm_apply, g.apply_symm_apply]

theorem rel_of_reach_liftS {a c : α} (h : Reach (liftS τ htop) a c) : x.1 a c := by
  have htop' : joinOrbit g x.2.2 = ⊤ := congrArg Subtype.val htop
  induction h with
  | refl => exact x.1.refl a
  | tail _ hbc ih =>
    rcases hbc with hbc | hbc
    · exact x.1.trans ih (rel_of_le_of_joinOrbit_eq_top x.2.2 x.2.1 htop' hbc)
    · exact x.1.trans ih hbc.1

theorem reach_tau_of_reach_liftS {a c : α} {j : ℕ} (hj : x.1 p ((σ ^ j) a))
    (h : Reach (liftS τ htop) a c) :
    ∃ hc : x.1 p ((σ ^ j) c), Reach τ.1 ⟨_, hj⟩ ⟨_, hc⟩ := by
  induction h with
  | refl => exact ⟨hj, Relation.ReflTransGen.refl⟩
  | @tail c d hac hcd ih =>
    obtain ⟨hc, hr⟩ := ih
    have hxcd : x.1 c d := rel_of_reach_liftS τ htop (Relation.ReflTransGen.single hcd)
    have hd := blk_of_rel hc hxcd
    refine ⟨hd, hr.tail ?_⟩
    rcases hcd with hcd | hcd
    · exact Or.inl (show (σ ^ j) c ≤ (σ ^ j) d from monotone_pow g j hcd)
    · obtain ⟨_, _, h⟩ := ((liftS_iff τ htop hc).1 hcd).2
      exact Or.inr h

theorem isOrderPreserving_liftS : IsOrderPreserving (liftS τ htop) := by
  intro a b hab hba
  obtain ⟨j, hj⟩ := exists_pow_blk htop a
  obtain ⟨hb, h1⟩ := reach_tau_of_reach_liftS τ htop hj hab
  obtain ⟨ha, h2⟩ := reach_tau_of_reach_liftS τ htop hb hba
  exact (liftS_iff τ htop hj).2 ⟨rel_of_reach_liftS τ htop hab, hj, hb, τ.2.1 _ _ h1 h2⟩

/-- The lift of `τ`, as an element of `[0̂, x] ⊆ OP(P)^g`. -/
def liftP : OPFixed α g :=
  ⟨liftS τ htop, isOrderPreserving_liftS τ htop, actSetoid_liftS τ htop⟩

theorem liftP_le : liftP τ htop ≤ x := fun _ _ h => h.1

theorem resP_liftP : resP g x p (liftP τ htop) = τ := by
  apply Subtype.ext
  ext u v
  change liftS τ htop u.1 v.1 ↔ τ.1 u v
  have hu : x.1 p ((σ ^ 0) u.1) := by simpa using u.2
  rw [liftS_iff τ htop hu]
  simp only [pow_zero, Equiv.Perm.one_apply]
  exact ⟨fun ⟨_, _, _, h⟩ => h, fun h => ⟨x.1.trans (x.1.symm u.2) v.2, u.2, v.2, h⟩⟩

omit htop in
/-- **Lemma `lem:interval`(i)**: for `x ∈ X(P,g)`, `[0̂, x]_{OP(P)^g} ≅ OP(P|_{B₀})^h`, hence
`μ_{OP(P)^g}(0̂, x) = μ(OP(P|_{B₀})^h)`. -/
theorem mu_interval (htop : OPFixed.join g x = OPFixed.top g) :
    IncidenceAlgebra.mu ℤ (OPFixed.bot g) x = muFixed (hres g x p) := by
  have := Fintype.ofFinite (OPFixed α g)
  have hbx : OPFixed.bot g ≤ x := fun a b h => by
    rw [OPFixed.bot, Setoid.bot_def] at h; exact h ▸ x.1.refl a
  have key := mu_eq_of_interval (resP g x p) (OPFixed.bot g) x
    (fun π π' _ hπ _ hπ' => ⟨resP_reflect htop hπ, resP_mono g x p⟩)
    (fun τ _ _ => ⟨liftP τ htop, fun a b h => by
        rw [OPFixed.bot, Setoid.bot_def] at h; exact h ▸ (liftP τ htop).1.refl a,
      liftP_le τ htop, resP_liftP τ htop⟩) x hbx le_rfl
  rw [resP_bot, resP_self] at key
  rw [← key]
  rfl

end Block

/-! ### The recursion (W) -/

open Classical in
/-- **The recursion (W)**, unsigned (proof of Proposition `prop:Mside`): for `g ≠ 1` and any
base point `p`, `∑_{x ∈ X(P,g)} μ(OP(P|_{B₀(x)})^{h_x}) = 0`, where `x ∈ X(P,g)` is
`x ∈ OP(P)^g` with `x ∨ O_g = 1̂`, `B₀(x)` is the block of `x` through `p` and
`h_x = g^{m(x)}|_{B₀(x)}`. -/
theorem recursionW (g : α ≃o α) (hg : g ≠ 1) (p : α) :
    have := Fintype.ofFinite (OPFixed α g)
    ∑ x ∈ univ.filter (fun x => OPFixed.join g x = OPFixed.top g), muFixed (hres g x p) = 0 := by
  intro _
  rw [← sum_mu_join_eq_top g hg]
  refine Finset.sum_congr rfl fun x hx => ?_
  exact (mu_interval (Finset.mem_filter.1 hx).2).symm

end PosetJKS

import PosetJKS.ChainTools
import PosetJKS.TraceHP

/-!
# Lemma K: a retraction onto a cone is acyclic

Route C, slice S2 (`notes/lean_js_route.md` §3.1 and §6, with the signs of
`notes/audit_lean_js_route.md` G1–G2).

**Lemma K.** Let `R` be a poset, `t ∈ R`, and `p : R → R` monotone with `p x ≤ x`, `p x ≤ t`
for all `x`, and `p x = x` for `x ≤ t` (a `ConeRetraction`). Then the augmented chain complex
of `Δ(R)` is exact; in particular `H̃_d(Δ(R)) = 0` for every `d ≥ 0` (`exact_of_retract`).

At the homotopy level this is Quillen's order-homotopy lemma (Quillen 1978, Prop. 1.6 and the
cone remark 1.5), in the form of Björner 1995, Cor. 10.12: a monotone `p ≤ id` makes `Δ(p R)`
a deformation retract of `Δ(R)`, and here `p R = R_{≤ t}` is a cone. The proof below is the
homology-level one of the note and uses no topology.

For a chain `c`, an element is *low* if it is `≤ t` and *high* otherwise. The low elements form
an initial segment of `c`, of length `j = nlow c` (`low_iff`); `hcount c` is the number of high
elements. Put `τ c = p h` for `h = c_j` the least high element, and `τ c = t` if there is none
(`tau`, via `hval`). Then `τ c` lies above the low part and strictly below the high part
(`le_tau`, `tau_lt`). The operator `s` sends `c` to `(-1)^j [c ∪ {τ c}]` if `τ c ∉ c` (the chain
`cone c`, with `τ c` at position `j`) and to `0` otherwise. With `F k` the span of the chains
with at most `k` high elements (a subcomplex, stable under `s`):

* `bd_s_add_s_bd_eq`: for a chain `c` with `j < |c|` (so `h = c_j` exists),
  `(∂s + s∂)(c) − c = −[(c ∖ h) ∪ τ c] + (−1)^j s(c ∖ h)` if `τ c ∉ c`, and
  `(∂s + s∂)(c) − c = (−1)^j s(c ∖ h)` if `τ c ∈ c`. Here `(c ∖ h) ∪ τ c` is the face of
  `cone c` at position `j + 1`. In the case `τ c ∈ c`, `τ c` sits at position `j' = j − 1` of
  `c` (`tau_mem_range_iff`), the face removing it has sign `(−1)^{j'}`, and
  `s (c ∖ τ c) = (−1)^{j'} [c]` (`s_single_face_tau`), so the product is `+[c]`.
* `bd_s_add_s_bd_of_hcount_eq_zero`: `(∂s + s∂)(c) = c` when `c` has no high element.
* `bd_s_add_s_bd`: `(∂s + s∂)(c) − c ∈ F (hcount c − 1)`.
* `exact_of_retract`: by induction on `k`, every cycle in `F k` is a boundary.
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

/-- The data of Lemma K: an element `t` and a monotone retraction `p ≤ id` of `R` onto
`R_{≤ t}`. -/
structure ConeRetraction (R : Type*) [PartialOrder R] where
  /-- The cone point. -/
  t : R
  /-- The retraction. -/
  p : R → R
  monotone : Monotone p
  le_self : ∀ x, p x ≤ x
  le_t : ∀ x, p x ≤ t
  eq_of_le : ∀ x, x ≤ t → p x = x

namespace ConeRetraction

open Classical

variable {R : Type*} [PartialOrder R] (K : ConeRetraction R)

/-! ### Low and high elements of a chain -/

/-- The number of low elements (those `≤ t`) of a chain. -/
noncomputable def nlow {m : ℕ} (c : Fin m ↪o R) : ℕ := (univ.filter fun i => c i ≤ K.t).card

/-- The number of high elements (those `≰ t`) of a chain. -/
noncomputable def hcount {m : ℕ} (c : Fin m ↪o R) : ℕ := m - K.nlow c

/-- The low elements of a chain are an initial segment, of length `nlow c`. -/
theorem low_iff {m : ℕ} (c : Fin m ↪o R) (i : Fin m) : c i ≤ K.t ↔ (i : ℕ) < K.nlow c := by
  constructor
  · intro h
    have hsub : Iic i ⊆ univ.filter fun k => c k ≤ K.t := fun k hk => by
      simp only [mem_filter, mem_univ, true_and]
      exact (c.le_iff_le.2 (mem_Iic.1 hk)).trans h
    have := card_le_card hsub
    rw [Fin.card_Iic] at this
    unfold nlow
    omega
  · intro h
    by_contra hn
    have hsub : (univ.filter fun k => c k ≤ K.t) ⊆ Iio i := fun k hk => by
      simp only [mem_filter, mem_univ, true_and] at hk
      rw [mem_Iio]
      by_contra hki
      exact hn ((c.le_iff_le.2 (not_lt.1 hki)).trans hk)
    have := card_le_card hsub
    rw [Fin.card_Iio] at this
    unfold nlow at h
    omega

theorem nlow_le {m : ℕ} (c : Fin m ↪o R) : K.nlow c ≤ m :=
  (card_le_univ _).trans (by simp)

theorem nlow_face {m : ℕ} (c : Fin (m + 1) ↪o R) (i : Fin (m + 1)) :
    K.nlow (face c i) + (if c i ≤ K.t then 1 else 0) = K.nlow c := by
  unfold nlow
  rw [card_filter, card_filter, Fin.sum_univ_succAbove _ i, add_comm]
  rfl

theorem nlow_face_of_le {m : ℕ} (c : Fin (m + 1) ↪o R) (i : Fin (m + 1)) (h : c i ≤ K.t) :
    K.nlow (face c i) + 1 = K.nlow c := by
  simpa [h] using K.nlow_face c i

theorem nlow_face_of_not_le {m : ℕ} (c : Fin (m + 1) ↪o R) (i : Fin (m + 1)) (h : ¬ c i ≤ K.t) :
    K.nlow (face c i) = K.nlow c := by
  simpa [h] using K.nlow_face c i

theorem nlow_insertAt {m : ℕ} (c : Fin m ↪o R) (x : R) (j : Fin (m + 1)) (h) (hx : x ≤ K.t) :
    K.nlow (insertAt c x j h) = K.nlow c + 1 := by
  unfold nlow
  rw [card_filter, card_filter, Fin.sum_univ_succAbove _ j, insertAt_apply_self, if_pos hx,
    add_comm]
  simp only [insertAt_apply_succAbove]

/-- Faces do not add high elements. -/
theorem hcount_face_le {m : ℕ} (c : Fin (m + 1) ↪o R) (i : Fin (m + 1)) :
    K.hcount (face c i) ≤ K.hcount c := by
  have := K.nlow_face c i
  have := K.nlow_le c
  unfold hcount
  split_ifs at * <;> omega

/-- Removing a high element removes one high element. -/
theorem hcount_face_of_not_le {m : ℕ} (c : Fin (m + 1) ↪o R) (i : Fin (m + 1))
    (h : ¬ c i ≤ K.t) : K.hcount (face c i) + 1 = K.hcount c := by
  have h1 := K.nlow_face_of_not_le c i h
  have h2 : (i : ℕ) ≥ K.nlow c := not_lt.1 fun h' => h ((K.low_iff c i).2 h')
  unfold hcount
  omega

/-- Inserting a low element does not change the number of high elements. -/
theorem hcount_insertAt {m : ℕ} (c : Fin m ↪o R) (x : R) (j : Fin (m + 1)) (h) (hx : x ≤ K.t) :
    K.hcount (insertAt c x j h) = K.hcount c := by
  unfold hcount
  rw [K.nlow_insertAt c x j h hx]
  have := K.nlow_le c
  omega

/-! ### The element `τ c` -/

/-- The least high element of `c`, or `t` if `c` has none. -/
noncomputable def hval {m : ℕ} (c : Fin m ↪o R) : R :=
  if h : K.nlow c < m then c ⟨K.nlow c, h⟩ else K.t

/-- `τ c = p h` for the least high element `h` of `c`, and `τ c = t` if there is none. -/
noncomputable def tau {m : ℕ} (c : Fin m ↪o R) : R := K.p (K.hval c)

theorem hval_of_lt {m : ℕ} (c : Fin m ↪o R) (h : K.nlow c < m) :
    K.hval c = c ⟨K.nlow c, h⟩ := dif_pos h

theorem hval_of_not_lt {m : ℕ} (c : Fin m ↪o R) (h : ¬ K.nlow c < m) : K.hval c = K.t :=
  dif_neg h

theorem tau_le_t {m : ℕ} (c : Fin m ↪o R) : K.tau c ≤ K.t := K.le_t _

theorem le_hval {m : ℕ} (c : Fin m ↪o R) (i : Fin m) (hi : (i : ℕ) < K.nlow c) :
    c i ≤ K.hval c := by
  unfold hval
  split_ifs with h
  · exact c.le_iff_le.2 (Fin.mk_le_mk.2 hi.le)
  · exact (K.low_iff c i).2 hi

/-- `τ c` lies above the low part of `c`. -/
theorem le_tau {m : ℕ} (c : Fin m ↪o R) (i : Fin m) (hi : (i : ℕ) < K.nlow c) :
    c i ≤ K.tau c := by
  rw [← K.eq_of_le _ ((K.low_iff c i).2 hi)]
  exact K.monotone (K.le_hval c i hi)

/-- `τ c` lies strictly below the high part of `c`. -/
theorem tau_lt {m : ℕ} (c : Fin m ↪o R) (i : Fin m) (hi : K.nlow c ≤ i) : K.tau c < c i := by
  have hlt : K.nlow c < m := lt_of_le_of_lt hi i.2
  have hh : ¬ c ⟨K.nlow c, hlt⟩ ≤ K.t := fun h' => by
    have := (K.low_iff c _).1 h'
    simp at this
  unfold tau
  rw [K.hval_of_lt c hlt]
  refine lt_of_lt_of_le (lt_of_le_of_ne (K.le_self _) fun he => hh (he ▸ K.le_t _)) ?_
  exact c.le_iff_le.2 (Fin.mk_le_mk.2 hi)

/-- If `τ c ∈ c`, it is the largest low element, at position `nlow c - 1`. -/
theorem tau_mem_range_iff {m : ℕ} (c : Fin m ↪o R) (i : Fin m) :
    c i = K.tau c ↔ (i : ℕ) + 1 = K.nlow c ∧ c i = K.tau c := by
  refine ⟨fun he => ⟨?_, he⟩, And.right⟩
  have hi : (i : ℕ) < K.nlow c := (K.low_iff c i).1 (he ▸ K.tau_le_t c)
  by_contra hne
  have hlt : (i : ℕ) + 1 < K.nlow c := by omega
  have hj : K.nlow c - 1 < m := by have := K.nlow_le c; omega
  have h1 := K.le_tau c ⟨K.nlow c - 1, hj⟩ (by simp only; omega)
  have h2 : c i < c ⟨K.nlow c - 1, hj⟩ := c.lt_iff_lt.2 (Fin.mk_lt_mk.2 (by omega))
  exact lt_irrefl _ (h2.trans_le (h1.trans he.ge))

/-- When `τ c ∉ c`, inserting it at position `nlow c` gives a chain. -/
theorem strictMono_cone {m : ℕ} (c : Fin m ↪o R) (h : K.tau c ∉ Set.range c) :
    StrictMono (Fin.insertNth ⟨K.nlow c, Nat.lt_succ_of_le (K.nlow_le c)⟩ (K.tau c) c :
      Fin (m + 1) → R) := by
  refine strictMono_insertNth c _ _ (fun i hi => ?_) (fun i hi => K.tau_lt c i hi)
  exact lt_of_le_of_ne (K.le_tau c i hi) fun he => h ⟨i, he⟩

/-- The chain `c ∪ {τ c}`, with `τ c` at position `nlow c`. -/
noncomputable def cone {m : ℕ} (c : Fin m ↪o R) (h : K.tau c ∉ Set.range c) : Fin (m + 1) ↪o R :=
  insertAt c (K.tau c) ⟨K.nlow c, Nat.lt_succ_of_le (K.nlow_le c)⟩ (K.strictMono_cone c h)

/-! ### The operator `s` -/

/-- `s` on a basis chain: `(-1)^{nlow c} [c ∪ {τ c}]` if `τ c ∉ c`, and `0` otherwise. -/
noncomputable def sChain {m : ℕ} (c : Fin m ↪o R) : Chains R (m + 1) :=
  if h : K.tau c ∈ Set.range c then 0
  else ((-1 : ℂ) ^ K.nlow c) • Chains.single R (K.cone c h)

/-- The chain homotopy `s : C_m → C_{m+1}`. -/
noncomputable def s (m : ℕ) : Chains R m →ₗ[ℂ] Chains R (m + 1) :=
  Finsupp.linearCombination ℂ K.sChain

theorem s_single {m : ℕ} (c : Fin m ↪o R) : K.s m (Chains.single R c) = K.sChain c := by
  unfold s Chains.single
  erw [Finsupp.linearCombination_single]
  rw [one_smul]

theorem s_single_of_mem {m : ℕ} (c : Fin m ↪o R) (h : K.tau c ∈ Set.range c) :
    K.s m (Chains.single R c) = 0 := by
  rw [s_single, sChain, dif_pos h]

theorem s_single_of_not_mem {m : ℕ} (c : Fin m ↪o R) (h : K.tau c ∉ Set.range c) :
    K.s m (Chains.single R c) = ((-1 : ℂ) ^ K.nlow c) • Chains.single R (K.cone c h) := by
  rw [s_single, sChain, dif_neg h]


/-! ### Faces and `τ` -/

theorem face_apply {m : ℕ} (c : Fin (m + 1) ↪o R) (i : Fin (m + 1)) (k : Fin m) :
    face c i k = c (i.succAbove k) := rfl

/-- Deleting an element other than the least high one does not change `hval`. -/
theorem hval_face {m : ℕ} (c : Fin (m + 1) ↪o R) (i : Fin (m + 1)) (hi : (i : ℕ) ≠ K.nlow c) :
    K.hval (face c i) = K.hval c := by
  by_cases hle : c i ≤ K.t
  · have h1 := K.nlow_face_of_le c i hle
    have hil := (K.low_iff c i).1 hle
    by_cases hlt : K.nlow c < m + 1
    · have hf : K.nlow (face c i) < m := by omega
      rw [K.hval_of_lt _ hf, K.hval_of_lt c hlt, face_apply]
      congr 1
      rw [Fin.succAbove_of_le_castSucc _ _
        (by rw [Fin.le_def]; simp only [Fin.val_castSucc]; omega)]
      ext
      simp only [Fin.val_succ]
      omega
    · rw [K.hval_of_not_lt _ (by omega), K.hval_of_not_lt c hlt]
  · have h1 := K.nlow_face_of_not_le c i hle
    have hil : K.nlow c < i :=
      lt_of_le_of_ne (not_lt.1 fun h => hle ((K.low_iff c i).2 h)) (Ne.symm hi)
    have hf : K.nlow (face c i) < m := by omega
    rw [K.hval_of_lt _ hf, K.hval_of_lt c (by omega), face_apply]
    congr 1
    rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp only [Fin.val_castSucc]; omega)]
    ext
    simp only [Fin.val_castSucc]
    omega

theorem tau_face {m : ℕ} (c : Fin (m + 1) ↪o R) (i : Fin (m + 1)) (hi : (i : ℕ) ≠ K.nlow c) :
    K.tau (face c i) = K.tau c := by
  unfold tau
  rw [K.hval_face c i hi]

theorem not_mem_range_face {m : ℕ} (c : Fin (m + 1) ↪o R) (i : Fin (m + 1)) {x : R}
    (h : x ∉ Set.range c) : x ∉ Set.range (face c i) := fun ⟨_, hk⟩ => h ⟨_, hk⟩

theorem mem_range_face {m : ℕ} (c : Fin (m + 1) ↪o R) {i i' : Fin (m + 1)} (hne : i' ≠ i) :
    c i' ∈ Set.range (face c i) := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hne
  exact ⟨k, by rw [face_apply, hk]⟩

theorem not_mem_range_face_self {m : ℕ} (c : Fin (m + 1) ↪o R) (i : Fin (m + 1)) :
    c i ∉ Set.range (face c i) := fun ⟨k, hk⟩ =>
  Fin.succAbove_ne i k (c.injective (by rw [← face_apply, hk]))

theorem insertAt_congr {m : ℕ} (c : Fin m ↪o R) {x x' : R} {j j' : Fin (m + 1)} (hx : x = x')
    (hj : j = j') (h h') : insertAt c x j h = insertAt c x' j' h' := by
  subst hx hj
  rfl

/-- Away from the least high element, `s` commutes with deleting: `cone (c ∖ c_i)` is
`cone c` with `c_i` deleted. -/
theorem cone_face {m : ℕ} (c : Fin (m + 1) ↪o R) (h : K.tau c ∉ Set.range c) (i : Fin (m + 1))
    (hi : (i : ℕ) ≠ K.nlow c) (h' : K.tau (face c i) ∉ Set.range (face c i)) :
    K.cone (face c i) h' =
      face (K.cone c h)
        ((⟨K.nlow c, Nat.lt_succ_of_le (K.nlow_le c)⟩ : Fin (m + 2)).succAbove i) := by
  unfold cone
  rw [face_insertAt_succAbove]
  refine insertAt_congr _ (K.tau_face c i hi) ?_ _ _
  ext
  by_cases hle : c i ≤ K.t
  · have h1 := K.nlow_face_of_le c i hle
    have hil := (K.low_iff c i).1 hle
    rw [Fin.predAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simp only [Fin.val_castSucc]; omega)]
    simp only [Fin.val_pred]
    omega
  · have h1 := K.nlow_face_of_not_le c i hle
    have hil : K.nlow c < i :=
      lt_of_le_of_ne (not_lt.1 fun h => hle ((K.low_iff c i).2 h)) (Ne.symm hi)
    rw [Fin.predAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp only [Fin.val_castSucc]; omega)]
    simp only [Fin.coe_castPred]
    omega

/-- The case `τ c ∈ c`: `τ c = c_{j'}` with `j' = nlow c - 1`, and
`s (c ∖ c_{j'}) = (-1)^{j'} [c]`. -/
theorem s_single_face_tau {m : ℕ} (c : Fin (m + 1) ↪o R) (i : Fin (m + 1)) (he : c i = K.tau c) :
    K.s m (Chains.single R (face c i)) = ((-1 : ℂ) ^ (i : ℕ)) • Chains.single R c := by
  have hpos := ((K.tau_mem_range_iff c i).1 he).1
  have hi : (i : ℕ) ≠ K.nlow c := by omega
  have hτ := K.tau_face c i hi
  have hnm : K.tau (face c i) ∉ Set.range (face c i) := hτ ▸ he ▸ not_mem_range_face_self c i
  have h1 := K.nlow_face_of_le c i (he ▸ K.tau_le_t c)
  rw [K.s_single_of_not_mem _ hnm, show K.nlow (face c i) = i by omega]
  congr 2
  unfold cone
  exact (insertAt_congr _ (hτ.trans he.symm) (Fin.ext (by simp only; omega)) _ _).trans
    (insertAt_face c i)

/-! ### The homotopy identity -/

/-- The boundary of `s [c]`, for `τ c ∉ c`: the face at position `nlow c` gives back `c`. -/
theorem bd_s_single_of_not_mem {m : ℕ} (c : Fin (m + 1) ↪o R) (h : K.tau c ∉ Set.range c) :
    bd R (m + 1) (K.s (m + 1) (Chains.single R c)) =
      Chains.single R c + ∑ i : Fin (m + 1),
        ((-1 : ℂ) ^ K.nlow c * (-1 : ℂ) ^
          ((⟨K.nlow c, Nat.lt_succ_of_le (K.nlow_le c)⟩ : Fin (m + 2)).succAbove i : ℕ)) •
          Chains.single R (face (K.cone c h)
            ((⟨K.nlow c, Nat.lt_succ_of_le (K.nlow_le c)⟩ : Fin (m + 2)).succAbove i)) := by
  rw [K.s_single_of_not_mem c h, map_smul, bd_single,
    Fin.sum_univ_succAbove _ ⟨K.nlow c, Nat.lt_succ_of_le (K.nlow_le c)⟩]
  unfold cone
  rw [face_insertAt_self, smul_add, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
    one_pow, one_smul, Finset.smul_sum]
  simp only [smul_smul]

theorem s_bd_single {m : ℕ} (c : Fin (m + 1) ↪o R) :
    K.s m (bd R m (Chains.single R c)) =
      ∑ i : Fin (m + 1), ((-1 : ℂ) ^ (i : ℕ)) • K.s m (Chains.single R (face c i)) := by
  rw [bd_single, map_sum]
  simp only [map_smul]

/-- In the case `τ c ∉ c`, the face of `∂ s c` removing `c_i` cancels against `s` of the face
`c ∖ c_i` of `∂ c`, for every `c_i` other than the least high element. The signs are
`(-1)^{j+i}` and `(-1)^{i+j-1}` for `i < j`, and `(-1)^{j+i+1}` and `(-1)^{i+j}` for `i > j`. -/
theorem bd_s_term_eq_zero {m : ℕ} (c : Fin (m + 1) ↪o R) (h : K.tau c ∉ Set.range c)
    (i : Fin (m + 1)) (hi : (i : ℕ) ≠ K.nlow c) :
    ((-1 : ℂ) ^ K.nlow c * (-1 : ℂ) ^
        ((⟨K.nlow c, Nat.lt_succ_of_le (K.nlow_le c)⟩ : Fin (m + 2)).succAbove i : ℕ)) •
        Chains.single R (face (K.cone c h)
          ((⟨K.nlow c, Nat.lt_succ_of_le (K.nlow_le c)⟩ : Fin (m + 2)).succAbove i)) +
      ((-1 : ℂ) ^ (i : ℕ)) • K.s m (Chains.single R (face c i)) = 0 := by
  have h' : K.tau (face c i) ∉ Set.range (face c i) :=
    K.tau_face c i hi ▸ not_mem_range_face c i h
  rw [K.s_single_of_not_mem _ h', K.cone_face c h i hi h', smul_smul, ← add_smul]
  convert zero_smul ℂ _
  rw [neg_one_pow_succAbove]
  by_cases hle : c i ≤ K.t
  · have h1 := K.nlow_face_of_le c i hle
    have hil := (K.low_iff c i).1 hle
    rw [if_pos (by rw [Fin.lt_def]; simp only [Fin.val_castSucc]; omega), ← h1, pow_succ]
    ring
  · have h1 := K.nlow_face_of_not_le c i hle
    have hil : K.nlow c < i :=
      lt_of_le_of_ne (not_lt.1 fun h => hle ((K.low_iff c i).2 h)) (Ne.symm hi)
    rw [if_neg (by rw [Fin.lt_def]; simp only [Fin.val_castSucc]; omega), h1]
    ring

/-- In the case `τ c = c_{i₀}`, `s` kills every face that keeps both `c_{i₀}` and the least high
element. -/
theorem s_term_eq_zero {m : ℕ} (c : Fin (m + 1) ↪o R) {i₀ : Fin (m + 1)} (he : c i₀ = K.tau c)
    (i : Fin (m + 1)) (hi₀ : i ≠ i₀) (hi : (i : ℕ) ≠ K.nlow c) :
    K.s m (Chains.single R (face c i)) = 0 :=
  K.s_single_of_mem _ (by rw [K.tau_face c i hi, ← he]; exact mem_range_face c hi₀.symm)

/-- **The homotopy identity, exactly** (`notes/lean_js_route.md` §3.1, end of the Claim). Let
`j = nlow c` and suppose `c` has a high element, so `h = c_j` is its least one. Then
`(∂s + s∂)(c) − c = −[(c ∖ h) ∪ τ c] + (−1)^j s(c ∖ h)` if `τ c ∉ c`, where `(c ∖ h) ∪ τ c`
is the face of `cone c` at position `j + 1`, and `(∂s + s∂)(c) − c = (−1)^j s(c ∖ h)` if
`τ c ∈ c`. -/
theorem bd_s_add_s_bd_eq {m : ℕ} (c : Fin (m + 1) ↪o R) (hj : K.nlow c < m + 1) :
    bd R (m + 1) (K.s (m + 1) (Chains.single R c)) + K.s m (bd R m (Chains.single R c)) -
        Chains.single R c =
      (if h : K.tau c ∈ Set.range c then 0
        else -Chains.single R (face (K.cone c h) ⟨K.nlow c + 1, by omega⟩)) +
        ((-1 : ℂ) ^ K.nlow c) • K.s m (Chains.single R (face c ⟨K.nlow c, hj⟩)) := by
  rw [s_bd_single]
  split_ifs with h
  · -- `τ c = c_{j'}`, `j' = j - 1`: the faces at `j'` and `j` survive.
    obtain ⟨i₀, he⟩ := h
    have hpos := ((K.tau_mem_range_iff c i₀).1 he).1
    have hne : i₀ ≠ ⟨K.nlow c, hj⟩ := fun h' => by rw [h'] at hpos; simp at hpos
    rw [K.s_single_of_mem c ⟨i₀, he⟩, map_zero, zero_add,
      Finset.sum_eq_add_of_mem i₀ ⟨K.nlow c, hj⟩ (mem_univ _) (mem_univ _) hne, zero_add,
      K.s_single_face_tau c i₀ he, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
      one_pow, one_smul, add_sub_cancel_left]
    rintro i - ⟨hi₀, hij⟩
    rw [K.s_term_eq_zero c he i hi₀ fun h' => hij (Fin.ext h'), smul_zero]
  · rw [K.bd_s_single_of_not_mem c h, add_assoc, add_sub_cancel_left, ← sum_add_distrib,
      Finset.sum_eq_single ⟨K.nlow c, hj⟩]
    · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_eq (Fin.ext (by simp))), ← pow_add,
        show K.nlow c + ((⟨K.nlow c, hj⟩ : Fin (m + 1)).succ : ℕ) = 2 * K.nlow c + 1 by
          simp only [Fin.val_succ]; omega,
        pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_smul]
      rfl
    · rintro i - hij
      exact K.bd_s_term_eq_zero c h i fun h' => hij (Fin.ext h')
    · intro hn; exact absurd (mem_univ _) hn

/-- With no high element, `s` is an exact contraction at `c`: `(∂s + s∂)(c) = c`. -/
theorem bd_s_add_s_bd_of_hcount_eq_zero {m : ℕ} (c : Fin (m + 1) ↪o R) (h0 : K.hcount c = 0) :
    bd R (m + 1) (K.s (m + 1) (Chains.single R c)) + K.s m (bd R m (Chains.single R c)) =
      Chains.single R c := by
  have hj : K.nlow c = m + 1 := by have := K.nlow_le c; unfold hcount at h0; omega
  have hi : ∀ i : Fin (m + 1), (i : ℕ) ≠ K.nlow c := fun i => by omega
  rw [s_bd_single]
  by_cases h : K.tau c ∈ Set.range c
  · obtain ⟨i₀, he⟩ := h
    rw [K.s_single_of_mem c ⟨i₀, he⟩, map_zero, zero_add, Finset.sum_eq_single i₀,
      K.s_single_face_tau c i₀ he, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
      one_pow, one_smul]
    · rintro i - hi₀
      rw [K.s_term_eq_zero c he i hi₀ (hi i), smul_zero]
    · intro hn; exact absurd (mem_univ _) hn
  · rw [K.bd_s_single_of_not_mem c h, add_assoc, ← sum_add_distrib, Finset.sum_eq_zero, add_zero]
    rintro i -
    exact K.bd_s_term_eq_zero c h i (hi i)

/-! ### The filtration by the number of high elements -/

/-- `F m k`: the span of the `m`-element chains with at most `k` high elements. -/
noncomputable def F (m k : ℕ) : Submodule ℂ (Chains R m) :=
  Submodule.span ℂ (Chains.single R '' {c | K.hcount c ≤ k})

theorem single_mem_F {m k : ℕ} (c : Fin m ↪o R) (h : K.hcount c ≤ k) :
    Chains.single R c ∈ K.F m k :=
  Submodule.subset_span ⟨c, h, rfl⟩

theorem F_mono {m k k' : ℕ} (h : k ≤ k') : K.F m k ≤ K.F m k' :=
  Submodule.span_mono (Set.image_mono fun _ hc => le_trans hc h)

/-- A linear map sends `F k` into `N` as soon as it does so on the basis chains. -/
theorem map_mem_of_mem_F {m m' k : ℕ} (f : Chains R m →ₗ[ℂ] Chains R m')
    (N : Submodule ℂ (Chains R m'))
    (h : ∀ c : Fin m ↪o R, K.hcount c ≤ k → f (Chains.single R c) ∈ N) {x : Chains R m}
    (hx : x ∈ K.F m k) : f x ∈ N := by
  have : K.F m k ≤ N.comap f := Submodule.span_le.2 (by rintro _ ⟨c, hc, rfl⟩; exact h c hc)
  exact this hx

/-- Every chain has at most `m` high elements. -/
theorem mem_F_self {m : ℕ} (x : Chains R m) : x ∈ K.F m m := by
  induction x using Finsupp.induction_linear with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | single c a =>
    rw [← Finsupp.smul_single_one]
    exact Submodule.smul_mem _ _ (K.single_mem_F c (Nat.sub_le _ _))

/-- `F k` is a subcomplex: faces do not add high elements. -/
theorem bd_mem_F {m k : ℕ} {x : Chains R (m + 1)} (hx : x ∈ K.F (m + 1) k) :
    bd R m x ∈ K.F m k :=
  K.map_mem_of_mem_F _ _ (fun c hc => by
    rw [bd_single]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (K.single_mem_F _ ((K.hcount_face_le c i).trans hc))) hx

/-- `s` preserves `F k`: `τ c` is low. -/
theorem s_mem_F {m k : ℕ} {x : Chains R m} (hx : x ∈ K.F m k) : K.s m x ∈ K.F (m + 1) k :=
  K.map_mem_of_mem_F _ _ (fun c hc => by
    rw [s_single, sChain]
    split_ifs with h
    · exact zero_mem _
    · refine Submodule.smul_mem _ _ (K.single_mem_F _ ?_)
      unfold cone
      rw [K.hcount_insertAt _ _ _ _ (K.tau_le_t c)]
      exact hc) hx

theorem cone_apply_succ {m : ℕ} (c : Fin m ↪o R) (h : K.tau c ∉ Set.range c)
    (hj : K.nlow c < m) : K.cone c h ⟨K.nlow c + 1, by omega⟩ = c ⟨K.nlow c, hj⟩ := by
  have : (⟨K.nlow c + 1, by omega⟩ : Fin (m + 1)) =
      (⟨K.nlow c, Nat.lt_succ_of_le (K.nlow_le c)⟩ : Fin (m + 1)).succAbove ⟨K.nlow c, hj⟩ :=
    (Fin.succAbove_of_le_castSucc _ ⟨K.nlow c, hj⟩ le_rfl).symm
  rw [this]
  exact insertAt_apply_succAbove _ _ _ _ _

theorem not_le_t_nlow {m : ℕ} (c : Fin m ↪o R) (hj : K.nlow c < m) :
    ¬ c ⟨K.nlow c, hj⟩ ≤ K.t := fun h' => by
  have := (K.low_iff c _).1 h'
  simp at this

/-- **The homotopy identity, filtered** (`notes/lean_js_route.md` §3.1, Claim):
`(∂s + s∂)(c) − c ∈ F (hcount c − 1)`. When `hcount c = 0` the difference is `0`
(`bd_s_add_s_bd_of_hcount_eq_zero`). -/
theorem bd_s_add_s_bd {m : ℕ} (c : Fin (m + 1) ↪o R) :
    bd R (m + 1) (K.s (m + 1) (Chains.single R c)) + K.s m (bd R m (Chains.single R c)) -
      Chains.single R c ∈ K.F (m + 1) (K.hcount c - 1) := by
  by_cases h0 : K.hcount c = 0
  · rw [K.bd_s_add_s_bd_of_hcount_eq_zero c h0, sub_self]
    exact zero_mem _
  have hj : K.nlow c < m + 1 := by unfold hcount at h0; omega
  have hh := K.hcount_face_of_not_le c _ (K.not_le_t_nlow c hj)
  rw [K.bd_s_add_s_bd_eq c hj]
  refine add_mem ?_ (Submodule.smul_mem _ _ (K.s_mem_F (K.single_mem_F _ (by omega))))
  split_ifs with h
  · exact zero_mem _
  · refine neg_mem (K.single_mem_F _ ?_)
    have hc := K.hcount_face_of_not_le (K.cone c h) ⟨K.nlow c + 1, by omega⟩
      (by rw [K.cone_apply_succ c h hj]; exact K.not_le_t_nlow c hj)
    have hcone : K.hcount (K.cone c h) = K.hcount c := by
      unfold cone
      exact K.hcount_insertAt _ _ _ _ (K.tau_le_t c)
    omega

/-- `∂s + s∂ − id` sends `F (k + 1)` into `F k`. -/
theorem homotopy_mem_F {m k : ℕ} {x : Chains R (m + 1)} (hx : x ∈ K.F (m + 1) (k + 1)) :
    bd R (m + 1) (K.s (m + 1) x) + K.s m (bd R m x) - x ∈ K.F (m + 1) k :=
  K.map_mem_of_mem_F (bd R (m + 1) ∘ₗ K.s (m + 1) + K.s m ∘ₗ bd R m - LinearMap.id) _
    (fun c hc => by
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.id_apply]
      by_cases hk : K.hcount c ≤ k
      · have hc' := K.single_mem_F c hk
        exact sub_mem (add_mem (K.bd_mem_F (K.s_mem_F hc')) (K.s_mem_F (K.bd_mem_F hc'))) hc'
      · have := K.bd_s_add_s_bd c
        rwa [show K.hcount c - 1 = k by omega] at this) hx

/-- On `F 0`, `s` is an exact contraction: `∂s + s∂ = id`. -/
theorem homotopy_F_zero {m : ℕ} {x : Chains R (m + 1)} (hx : x ∈ K.F (m + 1) 0) :
    bd R (m + 1) (K.s (m + 1) x) + K.s m (bd R m x) = x := by
  have := K.map_mem_of_mem_F (bd R (m + 1) ∘ₗ K.s (m + 1) + K.s m ∘ₗ bd R m - LinearMap.id) ⊥
    (fun c hc => by
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.id_apply, Submodule.mem_bot]
      rw [K.bd_s_add_s_bd_of_hcount_eq_zero c (Nat.le_zero.1 hc), sub_self]) hx
  simpa [sub_eq_zero] using this

/-! ### Exactness -/

/-- Every `d`-cycle with at most `k` high elements is a boundary (induction on `k`). -/
theorem exact_F (d k : ℕ) (z : Chains R (d + 1)) (hz : z ∈ K.F (d + 1) k)
    (hbd : bd R d z = 0) : z ∈ LinearMap.range (bd R (d + 1)) := by
  induction k generalizing z with
  | zero =>
    have := K.homotopy_F_zero hz
    rw [hbd, map_zero, add_zero] at this
    exact ⟨_, this⟩
  | succ k ih =>
    have h1 := K.homotopy_mem_F hz
    rw [hbd, map_zero, add_zero] at h1
    obtain ⟨b, hb⟩ := ih (z - bd R (d + 1) (K.s (d + 1) z))
      (by rw [← neg_sub]; exact neg_mem h1)
      (by rw [map_sub, ← LinearMap.comp_apply (bd R d), bd_comp_bd', LinearMap.zero_apply, hbd,
        sub_zero])
    exact ⟨b + K.s (d + 1) z, by rw [map_add, hb, sub_add_cancel]⟩

include K in
/-- **Lemma K** (`notes/lean_js_route.md` §3.1). If `R` admits a cone retraction, the augmented
chain complex of `Δ(R)` is exact: `H̃_d(Δ(R)) = 0` for every `d ≥ 0`. This is the homology form
of Quillen 1978, Prop. 1.6 (Björner 1995, Cor. 10.12). -/
theorem exact_of_retract (d : ℕ) : Subsingleton (redHom R d) :=
  (subsingleton_redHom_iff d).2 fun z hz => K.exact_F d (d + 1) z (K.mem_F_self z) hz

end ConeRetraction

end PosetJKS

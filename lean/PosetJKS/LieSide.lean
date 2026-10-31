import PosetJKS.LieTrace
import PosetJKS.ECTransport
import PosetJKS.RamanujanSum

/-!
# The Lie side of the closed formula (Proposition `prop:Lside` of `notes/poset_jks_theorem.tex`)

For `g ∈ Aut(P)` of order `o`, a primitive `n`-th root of unity `ζ` and any choice `B₀(x)` of
one block of each `x ∈ F(P,g)`:

  `∑_{gC = C} ζ^{r_g(C)} = μ(o) ∑_{x ∈ F(P,g)} e_C(P|_{B₀(x)})`   (`prop_Lside`).

The proof avoids the weights `1/|K(w)|` of the note. Fix a base point `x₀`. By Lemma 4 every
cyclic class contains exactly one word of `B_P(x₀)`, so the left side is a sum over the words
`w ∈ B_P(x₀)` with `g w = w γ^r`, `r < n`. For such a word let `k = gcd(r, n)` and `s = r/k`.
Then:

* `o = n/k` and `s` is a unit mod `o`; with `s s' ≡ 1 (mod o)` and `h = g^{s'}`, `w γ^k = h w`,
  so `w` is the concatenation of the `o` chunks `h^t (w_1 ⋯ w_k)` (`eq_flatMap_of_rotate`);
* the first chunk `A = {w_1, …, w_k}` is a union of components containing `x₀`, its images
  `g^j A`, `j < o`, partition the ground set, and so `x(w) = {g^j A}` lies in `F(P,g)`;
* `w_1 ⋯ w_k` is a word of `B_{P|_A}(x₀)`.

Conversely, for `x ∈ F(P,g)`, a unit `s` mod `o` and `u ∈ B_{P|_A}(x₀)` (`A` the block of `x`
through `x₀`), the concatenation of the chunks `h^t u` is such a word. This gives a bijection

  {words `w` as above} ≅ `∐_{x ∈ F(P,g)} B_{P|_{A(x)}}(x₀) × (ℤ/o)^×`,   `ζ^r = (ζ^k)^s`,

and `∑_{s ∈ (ℤ/o)^×} (ζ^k)^s = μ(o)` (the Ramanujan sum, `sum_pow_coprime_eq_moebius`). Finally
`|B_{P|_A}(x₀)| = e_C(P|_A)` (`card_BL`) and `e_C(P|_A) = e_C(P|_{B₀(x)})` since
`B₀(x) = g^j A` (`eC_image`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

variable {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α]

/-- `x ∈ F(P,g)` (with `o` the order of `g`): `x` is a partition of the ground set into exactly
`o` blocks, each block a union of components, and `g` permutes the blocks cyclically (maps
blocks to blocks, transitively). A partition is given by its set of blocks. -/
def InF (g : α ≃o α) (x : Finset (Finset α)) : Prop :=
  x.card = orderOf g ∧
  (∀ B ∈ x, B.Nonempty ∧ IsUnionOfComponents B) ∧
  (∀ B ∈ x, ∀ B' ∈ x, B ≠ B' → Disjoint B B') ∧
  (∀ a : α, ∃ B ∈ x, a ∈ B) ∧
  (∀ B ∈ x, B.image g ∈ x) ∧
  (∀ B ∈ x, ∀ B' ∈ x, ∃ k : ℕ, B' = B.image (g ^ k))

/-! ### Powers of an automorphism -/

section Pow

/-- `Aut(P) → S_P`, `g ↦ g` as a permutation. -/
def toPermHom : (α ≃o α) →* Equiv.Perm α where
  toFun e := e.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

lemma orderOf_pos_aut (g : α ≃o α) : 0 < orderOf g := by
  rw [← orderOf_injective toPermHom (fun _ _ h => RelIso.toEquiv_injective h) g]
  exact orderOf_pos _

lemma pow_mod_of_pow_eq_one {M : Type*} [Monoid M] {x : M} {o : ℕ} (hx : x ^ o = 1) (m : ℕ) :
    x ^ m = x ^ (m % o) := by
  conv_lhs => rw [← Nat.div_add_mod m o]
  rw [pow_add, pow_mul, hx, one_pow, one_mul]

lemma coe_pow_succ (h : α ≃o α) (t : ℕ) : ⇑(h ^ (t + 1)) = ⇑h ∘ ⇑(h ^ t) := by
  rw [pow_succ']; rfl

lemma coe_pow_succ' (h : α ≃o α) (t : ℕ) : ⇑(h ^ (t + 1)) = ⇑(h ^ t) ∘ ⇑h := by
  rw [pow_succ]; rfl

lemma coe_pow_zero (h : α ≃o α) : ⇑(h ^ 0) = id := by
  rw [pow_zero]; rfl

lemma mem_image_aut (φ : α ≃o α) (B : Finset α) (a : α) : a ∈ B.image φ ↔ φ.symm a ∈ B := by
  constructor
  · rintro h
    obtain ⟨b, hb, rfl⟩ := mem_image.1 h
    rwa [φ.symm_apply_apply]
  · intro h
    exact mem_image.2 ⟨_, h, φ.apply_symm_apply a⟩

lemma isUnionOfComponents_image (φ : α ≃o α) {B : Finset α} (hB : IsUnionOfComponents B) :
    IsUnionOfComponents (B.image φ) := by
  intro x y hxy
  rw [mem_image_aut, mem_image_aut]
  exact hB _ _ (φ.symm.monotone hxy)

/-- A multiplicative inverse of `u` modulo `o` (junk `0` if there is none). -/
noncomputable def invMod (u o : ℕ) : ℕ :=
  open Classical in if h : ∃ u', u * u' ≡ 1 [MOD o] then h.choose else 0

lemma mul_invMod {u o : ℕ} (ho : 0 < o) (hu : u.Coprime o) : u * invMod u o ≡ 1 [MOD o] := by
  have hex : ∃ u', u * u' ≡ 1 [MOD o] := by
    rcases Nat.lt_or_ge 1 o with h | h
    · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hu h
      exact ⟨m, by rw [Nat.ModEq, hm, Nat.mod_eq_of_lt h]⟩
    · obtain rfl : o = 1 := by omega
      exact ⟨0, Nat.modEq_one⟩
  unfold invMod
  rw [dif_pos hex]
  exact hex.choose_spec

lemma coprime_invMod {u o : ℕ} (ho : 0 < o) (hu : u.Coprime o) : (invMod u o).Coprime o :=
  Nat.coprime_of_mul_modEq_one u (by rw [mul_comm]; exact mul_invMod ho hu)

lemma pow_invMod_pow {M : Type*} [Monoid M] {g : M} {o u : ℕ} (hg : g ^ o = 1) (ho : 0 < o)
    (hu : u.Coprime o) : (g ^ invMod u o) ^ u = g := by
  rw [← pow_mul, pow_mod_of_pow_eq_one hg, mul_comm, mul_invMod ho hu,
    ← pow_mod_of_pow_eq_one hg, pow_one]

end Pow

/-! ### Block systems `{g^j B : j < o}` -/

section Blocks

/-- The sets `g^j B`, `j < o`, are pairwise disjoint and cover the ground set. -/
def IsBlockSys (g : α ≃o α) (o : ℕ) (B : Finset α) : Prop :=
  (∀ i < o, ∀ j < o, i ≠ j → Disjoint (B.image ⇑(g ^ i)) (B.image ⇑(g ^ j))) ∧
  ∀ a : α, ∃ j < o, a ∈ B.image ⇑(g ^ j)

/-- The partition `{g^j B : j < o}`, `o` the order of `g`. -/
noncomputable def blocksOf (g : α ≃o α) (B : Finset α) : Finset (Finset α) :=
  (range (orderOf g)).image fun j => B.image ⇑(g ^ j)

/-- Replacing `g` by `g^u` for a unit `u` mod `o` permutes the sets `g^j B`. -/
lemma isBlockSys_pow {g : α ≃o α} {o u : ℕ} {B : Finset α} (ho : 0 < o) (hg : g ^ o = 1)
    (hB : IsBlockSys g o B) (hu : u.Coprime o) : IsBlockSys (g ^ u) o B := by
  have key : ∀ t, (g ^ u) ^ t = g ^ ((u * t) % o) := fun t => by
    rw [← pow_mul, ← pow_mod_of_pow_eq_one hg]
  refine ⟨fun i hi j hj hij => ?_, fun a => ?_⟩
  · rw [key, key]
    refine hB.1 _ (Nat.mod_lt _ ho) _ (Nat.mod_lt _ ho) fun h => hij ?_
    have := Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm hu) h
    rw [Nat.ModEq, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
    exact this
  · obtain ⟨j, hj, ha⟩ := hB.2 a
    refine ⟨(invMod u o * j) % o, Nat.mod_lt _ ho, ?_⟩
    rw [key]
    have h1 : u * ((invMod u o * j) % o) ≡ u * (invMod u o * j) [MOD o] :=
      Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
    have h2 : u * (invMod u o * j) ≡ j [MOD o] := by
      rw [← mul_assoc]; simpa using Nat.ModEq.mul_right j (mul_invMod ho hu)
    have := h1.trans h2
    rw [Nat.ModEq, Nat.mod_eq_of_lt hj] at this
    rwa [this]

/-- `|P| = o |B|` for a block system `{g^j B : j < o}`. -/
lemma card_eq_of_isBlockSys {g : α ≃o α} {o : ℕ} {B : Finset α} (hB : IsBlockSys g o B) :
    Fintype.card α = o * B.card := by
  have hU : (univ : Finset α) = (range o).biUnion fun j => B.image ⇑(g ^ j) := by
    ext a
    simp only [mem_univ, mem_biUnion, mem_range, true_iff]
    obtain ⟨j, hj, ha⟩ := hB.2 a
    exact ⟨j, hj, ha⟩
  rw [← card_univ, hU, card_biUnion]
  · simp only [card_image_of_injective _ (g ^ _).injective, sum_const, card_range, smul_eq_mul]
  · intro i hi j hj hij
    exact hB.1 i (mem_range.1 hi) j (mem_range.1 hj) hij

lemma image_pow_mem_blocksOf (g : α ≃o α) (B : Finset α) (j : ℕ) :
    B.image ⇑(g ^ j) ∈ blocksOf g B := by
  rw [pow_mod_of_pow_eq_one (pow_orderOf_eq_one g) j]
  exact mem_image.2 ⟨_, mem_range.2 (Nat.mod_lt _ (orderOf_pos_aut g)), rfl⟩

lemma self_mem_blocksOf (g : α ≃o α) (B : Finset α) : B ∈ blocksOf g B := by
  have := image_pow_mem_blocksOf g B 0
  rwa [coe_pow_zero, image_id] at this

/-- A block system of a nonempty union of components gives an element of `F(P,g)`. -/
lemma inF_blocksOf {g : α ≃o α} {B : Finset α} (hne : B.Nonempty) (hU : IsUnionOfComponents B)
    (hB : IsBlockSys g (orderOf g) B) : InF g (blocksOf g B) := by
  have hne' : ∀ j, (B.image ⇑(g ^ j)).Nonempty := fun j => hne.image _
  have hinj : Set.InjOn (fun j => B.image ⇑(g ^ j)) (range (orderOf g) : Set ℕ) := by
    intro i hi j hj h
    by_contra hij
    have hd := hB.1 i (mem_range.1 hi) j (mem_range.1 hj) hij
    simp only at h
    rw [h, disjoint_self, bot_eq_empty] at hd
    exact (hne' j).ne_empty hd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [blocksOf, card_image_of_injOn hinj, card_range]
  · intro B' hB'
    obtain ⟨j, -, rfl⟩ := mem_image.1 hB'
    exact ⟨hne' j, isUnionOfComponents_image _ hU⟩
  · intro B' hB' B'' hB'' hne
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hB'
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hB''
    exact hB.1 i (mem_range.1 hi) j (mem_range.1 hj) fun h => hne (by rw [h])
  · intro a
    obtain ⟨j, hj, ha⟩ := hB.2 a
    exact ⟨_, mem_image.2 ⟨j, mem_range.2 hj, rfl⟩, ha⟩
  · intro B' hB'
    obtain ⟨j, -, rfl⟩ := mem_image.1 hB'
    rw [image_image, ← coe_pow_succ]
    exact image_pow_mem_blocksOf g B (j + 1)
  · intro B' hB' B'' hB''
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hB'
    obtain ⟨j, -, rfl⟩ := mem_image.1 hB''
    refine ⟨j + (orderOf g - i), ?_⟩
    rw [image_image]
    congr 1
    funext a
    simp only [Function.comp_apply]
    rw [← RelIso.mul_apply, ← pow_add, show j + (orderOf g - i) + i = j + orderOf g by
      have := mem_range.1 hi; omega, pow_add, pow_orderOf_eq_one, mul_one]

/-- Every `x ∈ F(P,g)` is the block system of any of its blocks. -/
lemma blocksOf_of_inF {g : α ≃o α} {x : Finset (Finset α)} (hx : InF g x) {B : Finset α}
    (hB : B ∈ x) : x = blocksOf g B ∧ IsBlockSys g (orderOf g) B := by
  obtain ⟨hcard, -, hdisj, hcov, hg, htr⟩ := hx
  have hpow : ∀ j, B.image ⇑(g ^ j) ∈ x := by
    intro j
    induction j with
    | zero => rwa [coe_pow_zero, image_id]
    | succ j ih =>
      rw [coe_pow_succ, ← image_image]
      exact hg _ ih
  have heq : x = blocksOf g B := by
    ext B'
    constructor
    · intro hB'
      obtain ⟨k, rfl⟩ := htr B hB B' hB'
      exact image_pow_mem_blocksOf g B k
    · intro hB'
      obtain ⟨j, -, rfl⟩ := mem_image.1 hB'
      exact hpow j
  refine ⟨heq, fun i hi j hj hij => ?_, fun a => ?_⟩
  · have hinj : Set.InjOn (fun j => B.image ⇑(g ^ j)) (range (orderOf g) : Set ℕ) := by
      have hc := congrArg Finset.card heq
      rw [blocksOf] at hc
      rw [← card_image_iff, card_range, ← hc, hcard]
    exact hdisj _ (hpow i) _ (hpow j) fun h =>
      hij (hinj (mem_coe.2 (mem_range.2 hi)) (mem_coe.2 (mem_range.2 hj)) h)
  · obtain ⟨B', hB', ha⟩ := hcov a
    rw [heq] at hB'
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hB'
    exact ⟨j, mem_range.1 hj, ha⟩

end Blocks

/-! ### Lists that are fixed by a rotation up to an automorphism -/

section Lists

lemma map_pow_eq_rotate {L : List α} {h : α ≃o α} {r : ℕ} (hL : L.map h = L.rotate r) (j : ℕ) :
    L.map ⇑(h ^ j) = L.rotate (j * r) := by
  induction j with
  | zero => rw [coe_pow_zero, List.map_id, zero_mul, List.rotate_zero]
  | succ j ih =>
    rw [coe_pow_succ', ← List.map_map, hL, List.map_rotate, ih, List.rotate_rotate, Nat.succ_mul]

/-- If `L γ^k = h L` and `|L| = o k`, then `L` is the concatenation of the chunks
`h^t (L_1 ⋯ L_k)`, `t < o`. -/
lemma eq_flatMap_of_rotate {L : List α} {h : α ≃o α} {k o : ℕ} (hlen : L.length = o * k)
    (hrot : L.rotate k = L.map h) :
    L = (List.range o).flatMap fun t => (L.take k).map ⇑(h ^ t) := by
  have claim : ∀ t ≤ o,
      L.take (t * k) = (List.range t).flatMap fun u => (L.take k).map ⇑(h ^ u) := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have hk : k ≤ L.length := by
        rw [hlen]; exact Nat.le_mul_of_pos_left k (by omega)
      have htk : t * k ≤ (L.drop k).length := by
        rw [List.length_drop, hlen]
        have : (t + 1) * k ≤ o * k := Nat.mul_le_mul_right k ht
        rw [Nat.succ_mul] at this; omega
      rw [Nat.succ_mul, add_comm, List.take_add]
      have hd : (L.drop k).take (t * k) = (L.rotate k).take (t * k) := by
        rw [List.rotate_eq_drop_append_take hk, List.take_append_of_le_length htk]
      rw [hd, hrot, ← List.map_take, ih (by omega), List.map_flatMap, List.range_succ_eq_map,
        List.flatMap_cons, List.flatMap_map, coe_pow_zero, List.map_id]
      congr 1
      congr 1
      funext u
      rw [List.map_map, ← coe_pow_succ]
  have := claim o le_rfl
  rwa [← hlen, List.take_of_length_le le_rfl] at this

/-- The concatenation of the chunks `h^t u`, `t < o`. -/
def chunks (h : α ≃o α) (o : ℕ) (u : List α) : List α :=
  (List.range o).flatMap fun t => u.map ⇑(h ^ t)

lemma chunks_eq_append (h : α ≃o α) {o : ℕ} (ho : 0 < o) (u : List α) :
    chunks h o u = u ++ (List.range (o - 1)).flatMap fun t => u.map ⇑(h ^ (t + 1)) := by
  obtain ⟨o', rfl⟩ : ∃ o', o = o' + 1 := ⟨o - 1, by omega⟩
  rw [chunks, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, coe_pow_zero,
    List.map_id, Nat.add_sub_cancel]

lemma length_chunks (h : α ≃o α) (o : ℕ) (u : List α) : (chunks h o u).length = o * u.length := by
  rw [chunks, List.length_flatMap]
  simp [List.map_const', List.sum_replicate]

lemma rotate_chunks {h : α ≃o α} {o : ℕ} (ho : 0 < o) (hh : h ^ o = 1) (u : List α) :
    (chunks h o u).rotate u.length = (chunks h o u).map h := by
  obtain ⟨o', rfl⟩ : ∃ o', o = o' + 1 := ⟨o - 1, by omega⟩
  have hmap : (chunks h (o' + 1) u).map h =
      ((List.range o').flatMap fun t => u.map ⇑(h ^ (t + 1))) ++ u := by
    rw [chunks, List.map_flatMap, List.range_succ, List.flatMap_append, List.flatMap_singleton,
      List.map_map, ← coe_pow_succ, hh]
    congr 1
    · congr 1; funext t; rw [List.map_map, ← coe_pow_succ]
    · exact List.map_id u
  rw [hmap, chunks_eq_append h ho, Nat.add_sub_cancel, List.rotate_append_length_eq]

lemma rotate_mul_chunks {h : α ≃o α} {o : ℕ} (ho : 0 < o) (hh : h ^ o = 1) (u : List α)
    (s : ℕ) : (chunks h o u).rotate (s * u.length) = (chunks h o u).map ⇑(h ^ s) := by
  induction s with
  | zero => rw [zero_mul, List.rotate_zero, coe_pow_zero, List.map_id]
  | succ s ih =>
    rw [Nat.succ_mul, ← List.rotate_rotate, ih, ← List.map_rotate, rotate_chunks ho hh,
      List.map_map, ← coe_pow_succ']

lemma mem_chunks {h : α ≃o α} {o : ℕ} {u : List α} {a : α} :
    a ∈ chunks h o u ↔ ∃ t < o, a ∈ u.map ⇑(h ^ t) := by
  simp [chunks]

end Lists

/-! ### The `B_P(x₀)` words of the `g`-stable classes -/

section Words

variable (g : α ≃o α) (x₀ : α)

lemma toL_trans_aut (w : Word α) : toL (w.trans g.toEquiv) = (toL w).map g := by
  simp only [toL, List.map_ofFn]; rfl

lemma mem_toL (w : Word α) (a : α) : a ∈ toL w := List.mem_ofFn.2 ⟨w.symm a, by simp⟩

open Classical in
/-- The words of `B_P(x₀)` whose cyclic class is `g`-stable (one per `g`-stable class). -/
noncomputable def fixedB : Finset (Word α) :=
  univ.filter fun w => InB x₀ w ∧ (coset w).image (fun z => z.trans g.toEquiv) = coset w

/-- `r = r_g(C)` for the class `C` of `w`. -/
noncomputable def rotOf (w : Word α) : ℕ := classRot g (coset w)

/-- `k = gcd(r, n)`, the length of the first chunk. -/
noncomputable def kOf (w : Word α) : ℕ := Nat.gcd (rotOf g w) (Fintype.card α)

/-- `s = r / k`, a unit modulo `o`. -/
noncomputable def sOf (w : Word α) : ℕ := rotOf g w / kOf g w

/-- The first chunk `{w_1, …, w_k}`. -/
noncomputable def blockOf (w : Word α) : Finset α := prefixSet w (kOf g w)

/-- The units modulo `o`, as residues `0 ≤ s < o`. -/
def unitsMod (o : ℕ) : Finset ℕ := (range o).filter (·.Coprime o)

variable {g x₀}

lemma mem_fixedB {w : Word α} :
    w ∈ fixedB g x₀ ↔ InB x₀ w ∧ (coset w).image (fun z => z.trans g.toEquiv) = coset w := by
  classical
  simp only [fixedB, Finset.mem_filter, Finset.mem_univ, true_and]

lemma fixedB_spec {w : Word α} (hw : w ∈ fixedB g x₀) :
    rotOf g w < Fintype.card α ∧ w.trans g.toEquiv = rot w (rotOf g w) := by
  have h0 : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨x₀⟩
  obtain ⟨hB, hfix⟩ := mem_fixedB.1 hw
  exact classRot_spec h0 g (classOf hB.1).2 hfix (self_mem_coset h0 w)

/-- The structure of a word `w ∈ B_P(x₀)` with `g w = w γ^r`: with `k = gcd(r, n)`, `s = r/k`
and `h = g^{s⁻¹ mod o}`: `o k = n`, `s` is a unit mod `o`, the first chunk `A` is a union of
components through `x₀` with `{g^j A} ∈ F(P,g)`, `w_1 ⋯ w_k ∈ B_{P|_A}(x₀)`, and `w` is the
concatenation of the chunks `h^t (w_1 ⋯ w_k)`. -/
theorem fixedB_struct {w : Word α} (hw : w ∈ fixedB g x₀) :
    0 < kOf g w ∧ orderOf g * kOf g w = Fintype.card α ∧ rotOf g w = sOf g w * kOf g w ∧
    sOf g w ∈ unitsMod (orderOf g) ∧ (blockOf g w).card = kOf g w ∧ x₀ ∈ blockOf g w ∧
    InF g (blocksOf g (blockOf g w)) ∧ (toL w).take (kOf g w) ∈ BL (blockOf g w) x₀ ∧
    toL w = chunks (g ^ invMod (sOf g w) (orderOf g)) (orderOf g) ((toL w).take (kOf g w)) := by
  have h0 : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨x₀⟩
  obtain ⟨hB, -⟩ := mem_fixedB.1 hw
  obtain ⟨hrn, hrot⟩ := fixedB_spec hw
  have hW : (toL w).map g = (toL w).rotate (rotOf g w) := by
    rw [← toL_trans_aut, hrot, toL_rot]
  have hlen : (toL w).length = Fintype.card α := length_toL w
  have hk0 : 0 < kOf g w := Nat.gcd_pos_of_pos_right _ h0
  have hkn : kOf g w ∣ Fintype.card α := Nat.gcd_dvd_right _ _
  have hkr : kOf g w ∣ rotOf g w := Nat.gcd_dvd_left _ _
  have hrs : rotOf g w = sOf g w * kOf g w := (Nat.div_mul_cancel hkr).symm
  have hcop : (sOf g w).Coprime (Fintype.card α / kOf g w) := Nat.coprime_div_gcd_div_gcd hk0
  -- `g^j = 1` iff `n/k ∣ j`, so `o = n/k`
  have hpow1 : ∀ j, g ^ j = 1 ↔ Fintype.card α / kOf g w ∣ j := by
    intro j
    have e1 : g ^ j = 1 ↔ (toL w).map ⇑(g ^ j) = toL w := by
      constructor
      · intro h; rw [h]; exact List.map_id _
      · intro h
        rw [← toL_trans_aut] at h
        have h' := toL_injective h
        refine RelIso.ext fun a => ?_
        have := DFunLike.congr_fun h' (w.symm a)
        simpa using this
    rw [e1, map_pow_eq_rotate hW, List.Nodup.rotate_eq_self_iff (isWordOn_toL w).1, hlen]
    have hne : toL w ≠ [] := by
      intro h; have := congrArg List.length h; rw [hlen] at this; simp at this; omega
    simp only [hne, or_false]
    rw [← Nat.dvd_iff_mod_eq_zero, hrs]
    conv_lhs => rw [← Nat.mul_div_cancel' hkn]
    rw [show j * (sOf g w * kOf g w) = kOf g w * (j * sOf g w) by ring,
      Nat.mul_dvd_mul_iff_left hk0, Nat.Coprime.dvd_mul_right hcop.symm]
  have hord : orderOf g = Fintype.card α / kOf g w :=
    Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ((hpow1 _).2 dvd_rfl))
      ((hpow1 _).1 (pow_orderOf_eq_one g))
  have hok : orderOf g * kOf g w = Fintype.card α := by
    rw [hord]; exact Nat.div_mul_cancel hkn
  have ho : 0 < orderOf g := orderOf_pos_aut g
  have hcop' : (sOf g w).Coprime (orderOf g) := hord ▸ hcop
  have hso : sOf g w ∈ unitsMod (orderOf g) := mem_filter.2 ⟨mem_range.2 (by
    rw [hord]; exact Nat.div_lt_div_of_lt_of_dvd hkn hrn), hcop'⟩
  -- the step `h = g^{s'}` moves each chunk to the next
  have hh : (g ^ invMod (sOf g w) (orderOf g)) ^ orderOf g = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hrotk : (toL w).rotate (kOf g w) =
      (toL w).map ⇑(g ^ invMod (sOf g w) (orderOf g)) := by
    rw [map_pow_eq_rotate hW, ← List.rotate_mod (toL w) (_ * rotOf g w),
      ← List.rotate_mod (toL w) (kOf g w), hlen]
    congr 1
    have := Nat.ModEq.mul_right' (kOf g w) (mul_invMod ho hcop')
    rw [hok, one_mul] at this
    rw [hrs, show invMod (sOf g w) (orderOf g) * (sOf g w * kOf g w) =
      sOf g w * invMod (sOf g w) (orderOf g) * kOf g w by ring]
    exact this.symm
  have hrec := eq_flatMap_of_rotate (by rw [hlen, hok]) hrotk
  -- the first chunk
  have hA : blockOf g w = ((toL w).take (kOf g w)).toFinset := prefixSet_eq w _
  have hkle : kOf g w ≤ Fintype.card α := Nat.le_of_dvd h0 hkn
  have hcardA : (blockOf g w).card = kOf g w := card_prefixSet w hkle
  have hAU : IsUnionOfComponents (blockOf g w) := by
    rcases hkle.lt_or_eq with hlt | heq
    · have hlin' : IsLinExt α (rot w (kOf g w)) := by
        have : rot w (kOf g w) = w.trans (g ^ invMod (sOf g w) (orderOf g)).toEquiv :=
          toL_injective (by rw [toL_rot, toL_trans_aut]; exact hrotk)
        rw [this]; exact isLinExt_trans _ hB.1
      exact ((isLinExt_rot_iff hB.1 hlt).1 hlin').2
    · have : blockOf g w = univ := Finset.eq_univ_of_card _ (hcardA.trans heq)
      intro a b _; rw [this]; simp
  have hx₀ : x₀ ∈ blockOf g w := hB.2 _ hk0 hkle hAU
  have hBh : IsBlockSys (g ^ invMod (sOf g w) (orderOf g)) (orderOf g) (blockOf g w) := by
    refine ⟨fun i hi j hj hij => ?_, fun a => ?_⟩
    · have hnd := (isWordOn_toL w).1
      rw [hrec, List.nodup_flatMap] at hnd
      have hd := hnd.2.forall (fun _ _ h => List.Disjoint.symm h) (List.mem_range.2 hi)
        (List.mem_range.2 hj) hij
      rw [hA, ← L.toFinset_map, ← L.toFinset_map]
      exact List.disjoint_toFinset_iff_disjoint.2 hd
    · have := mem_toL w a
      rw [hrec, ← chunks, mem_chunks] at this
      obtain ⟨t, ht, hat⟩ := this
      exact ⟨t, ht, by rw [hA, ← L.toFinset_map]; exact List.mem_toFinset.2 hat⟩
  have hBg : IsBlockSys g (orderOf g) (blockOf g w) := by
    have := isBlockSys_pow ho hh hBh hcop'
    rwa [pow_invMod_pow (pow_orderOf_eq_one g) ho hcop'] at this
  have hBL : (toL w).take (kOf g w) ∈ BL (blockOf g w) x₀ := by
    have hIn := (inB_iff x₀ w).1 hB
    refine mem_BL.2 ⟨⟨⟨(isWordOn_toL w).1.sublist (List.take_sublist _ _), hA.symm⟩,
      hIn.1.2.sublist (List.take_sublist _ _)⟩, ?_⟩
    intro p q hpq hp hU
    refine hIn.2 p (q ++ (toL w).drop (kOf g w))
      (by rw [← List.append_assoc, ← hpq, List.take_append_drop]) hp ?_
    have hpA : ∀ c ∈ p.toFinset, c ∈ blockOf g w := by
      intro c hc
      rw [hA, List.mem_toFinset, hpq]
      exact List.mem_append_left _ (List.mem_toFinset.1 hc)
    intro a _ b _ hab
    constructor
    · intro ha
      have haA := hpA a ha
      exact (hU a haA b ((hAU a b hab.le).1 haA) hab).1 ha
    · intro hb
      have hbA := hpA b hb
      exact (hU a ((hAU a b hab.le).2 hbA) b hbA hab).2 hb
  exact ⟨hk0, hok, hrs, hso, hcardA, hx₀, inF_blocksOf ⟨x₀, hx₀⟩ hAU hBg, hBL, hrec⟩

/-- The inverse construction: for `x ∈ F(P,g)`, its block `B ∋ x₀`, a unit `s` mod `o` and
`u ∈ B_{P|_B}(x₀)`, the concatenation of the chunks `(g^{s⁻¹})^t u` is a word of `B_P(x₀)` in a
`g`-stable class, with data `(x, s, u)`. -/
theorem exists_fixedB {x : Finset (Finset α)} (hx : InF g x) {B : Finset α} (hBx : B ∈ x)
    (hx₀ : x₀ ∈ B) {s : ℕ} (hs : s ∈ unitsMod (orderOf g)) {u : List α} (hu : u ∈ BL B x₀) :
    ∃ w ∈ fixedB g x₀, blockOf g w = B ∧ sOf g w = s ∧ (toL w).take B.card = u := by
  have h0 : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨x₀⟩
  have ho : 0 < orderOf g := orderOf_pos_aut g
  obtain ⟨-, hBg⟩ := blocksOf_of_inF hx hBx
  have hBU := (hx.2.1 B hBx).2
  obtain ⟨hsr, hsc⟩ := mem_filter.1 hs
  have hso := mem_range.1 hsr
  have hh : (g ^ invMod s (orderOf g)) ^ orderOf g = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hBh := isBlockSys_pow ho (pow_orderOf_eq_one g) hBg (coprime_invMod ho hsc)
  have hu' := mem_BL.1 hu
  have hwu : IsWordOn B u := hu'.1.1
  have hlen : u.length = B.card := by rw [← hwu.2, List.toFinset_card_of_nodup hwu.1]
  have hmem : ∀ t a, a ∈ u.map ⇑((g ^ invMod s (orderOf g)) ^ t) ↔
      a ∈ B.image ⇑((g ^ invMod s (orderOf g)) ^ t) := by
    intro t a; rw [← List.mem_toFinset, L.toFinset_map, hwu.2]
  have hMnd : (chunks (g ^ invMod s (orderOf g)) (orderOf g) u).Nodup := by
    rw [chunks, List.nodup_flatMap]
    refine ⟨fun t _ => hwu.1.map ((g ^ invMod s (orderOf g)) ^ t).injective, ?_⟩
    refine List.pairwise_lt_range.imp_of_mem fun {i j} hi hj hij => ?_
    intro a hai haj
    exact Finset.disjoint_left.1 (hBh.1 i (List.mem_range.1 hi) j (List.mem_range.1 hj) hij.ne)
      ((hmem i a).1 hai) ((hmem j a).1 haj)
  have hMall : ∀ a, a ∈ chunks (g ^ invMod s (orderOf g)) (orderOf g) u := by
    intro a
    obtain ⟨t, ht, ha⟩ := hBh.2 a
    exact mem_chunks.2 ⟨t, ht, (hmem t a).2 ha⟩
  obtain ⟨w, hw⟩ := exists_toL (α := α) ⟨hMnd, by ext a; simp [hMall a]⟩
  have hn : Fintype.card α = orderOf g * B.card := card_eq_of_isBlockSys hBg
  have hk0 : 0 < B.card := card_pos.2 ⟨x₀, hx₀⟩
  have hskn : s * B.card < Fintype.card α := by
    rw [hn]; exact Nat.mul_lt_mul_of_pos_right hso hk0
  have hrotw : w.trans g.toEquiv = rot w (s * B.card) := by
    apply toL_injective
    rw [toL_trans_aut, toL_rot, hw, ← hlen, rotate_mul_chunks ho hh,
      pow_invMod_pow (pow_orderOf_eq_one g) ho hsc]
  have hMapp := chunks_eq_append (g ^ invMod s (orderOf g)) ho u
  have hInB : InB x₀ w := by
    rw [inB_iff, hw]
    refine ⟨⟨⟨hMnd, by ext a; simp [hMall a]⟩, ?_⟩, ?_⟩
    · rw [chunks, List.pairwise_flatMap]
      refine ⟨fun t _ => ?_, ?_⟩
      · rw [List.pairwise_map]
        exact hu'.1.2.imp fun {a b} hab hlt =>
          hab (((g ^ invMod s (orderOf g)) ^ t).lt_iff_lt.1 hlt)
      · refine List.pairwise_lt_range.imp_of_mem fun {i j} hi hj hij => ?_
        intro a ha b hb hba
        have hUi := isUnionOfComponents_image ((g ^ invMod s (orderOf g)) ^ i) hBU
        have hbi : b ∈ B.image ⇑((g ^ invMod s (orderOf g)) ^ i) :=
          (hUi b a hba.le).2 ((hmem i a).1 ha)
        exact Finset.disjoint_left.1
          (hBh.1 i (List.mem_range.1 hi) j (List.mem_range.1 hj) hij.ne) hbi ((hmem j b).1 hb)
    · intro p q hpq hp hU
      have hpM : p <+: chunks (g ^ invMod s (orderOf g)) (orderOf g) u := by
        rw [hpq]; exact List.prefix_append _ _
      have huM : u <+: chunks (g ^ invMod s (orderOf g)) (orderOf g) u := by
        rw [hMapp]; exact List.prefix_append _ _
      rcases le_or_gt p.length u.length with hle | hlt
      · obtain ⟨t, ht⟩ := List.prefix_of_prefix_length_le hpM huM hle
        exact hu'.2 p t ht.symm hp fun a _ b _ hab => hU a (mem_univ _) b (mem_univ _) hab
      · exact (List.prefix_of_prefix_length_le huM hpM hlt.le).subset
          ((L.mem_of_isWordOn hwu).2 hx₀)
  have hfix : (coset w).image (fun z => z.trans g.toEquiv) = coset w := by
    rw [coset_image_trans, hrotw]
    exact coset_eq_of_mem h0 (mem_image.2 ⟨_, mem_range.2 hskn, rfl⟩)
  have hwT : w ∈ fixedB g x₀ := mem_fixedB.2 ⟨hInB, hfix⟩
  have hr : rotOf g w = s * B.card := by
    obtain ⟨hlt, hrot'⟩ := fixedB_spec hwT
    exact rot_injective hlt hskn (hrot'.symm.trans hrotw)
  have hk : kOf g w = B.card := by
    rw [kOf, hr, hn, Nat.gcd_mul_right, Nat.Coprime.gcd_eq_one hsc, one_mul]
  have hsw : sOf g w = s := by rw [sOf, hr, hk, Nat.mul_div_cancel _ hk0]
  have htake : (toL w).take B.card = u := by rw [hw, hMapp, List.take_left' hlen]
  refine ⟨w, hwT, ?_, hsw, htake⟩
  rw [blockOf, hk, prefixSet_eq, htake, hwu.2]

/-- For `w` with data `x`, the first chunk is the block of `x` through `x₀`. -/
lemma blockOf_eq {w : Word α} (hw : w ∈ fixedB g x₀) {x : Finset (Finset α)} (hx : InF g x)
    (hwx : blocksOf g (blockOf g w) = x) {B : Finset α} (hBx : B ∈ x) (hx₀ : x₀ ∈ B) :
    blockOf g w = B := by
  obtain ⟨-, -, -, -, -, hx₀', -⟩ := fixedB_struct hw
  by_contra hne
  have hmem : blockOf g w ∈ x := hwx ▸ self_mem_blocksOf g _
  exact Finset.disjoint_left.1 (hx.2.2.1 _ hmem B hBx hne) hx₀' hx₀

open Classical in
/-- The fibre of `w ↦ (x(w), s(w))` over `(x, s)` is in bijection with `B_{P|_B}(x₀)`, `B` the
block of `x` through `x₀`, and on it `r = s |B|`. -/
theorem card_fiber {x : Finset (Finset α)} (hx : InF g x) {B : Finset α} (hBx : B ∈ x)
    (hx₀ : x₀ ∈ B) {s : ℕ} (hs : s ∈ unitsMod (orderOf g)) :
    ((fixedB g x₀).filter fun w => (blocksOf g (blockOf g w), sOf g w) = (x, s)).card =
      (BL B x₀).card ∧
    ∀ w ∈ (fixedB g x₀).filter (fun w => (blocksOf g (blockOf g w), sOf g w) = (x, s)),
      rotOf g w = s * B.card := by
  have hdata : ∀ w ∈ (fixedB g x₀).filter
      (fun w => (blocksOf g (blockOf g w), sOf g w) = (x, s)),
      w ∈ fixedB g x₀ ∧ blockOf g w = B ∧ kOf g w = B.card ∧ sOf g w = s := by
    intro w hw
    obtain ⟨hwT, hp⟩ := mem_filter.1 hw
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hp
    have hb := blockOf_eq hwT hx h1 hBx hx₀
    obtain ⟨-, -, -, -, hcard, -⟩ := fixedB_struct hwT
    exact ⟨hwT, hb, by rw [← hcard, hb], h2⟩
  refine ⟨Finset.card_bij (fun w _ => (toL w).take B.card) ?_ ?_ ?_, ?_⟩
  · intro w hw
    obtain ⟨hwT, hb, hk, -⟩ := hdata w hw
    obtain ⟨-, -, -, -, -, -, -, hBL, -⟩ := fixedB_struct hwT
    rwa [hk, hb] at hBL
  · intro w₁ hw₁ w₂ hw₂ h
    obtain ⟨hT₁, -, hk₁, hs₁⟩ := hdata w₁ hw₁
    obtain ⟨hT₂, -, hk₂, hs₂⟩ := hdata w₂ hw₂
    obtain ⟨-, -, -, -, -, -, -, -, hrec₁⟩ := fixedB_struct hT₁
    obtain ⟨-, -, -, -, -, -, -, -, hrec₂⟩ := fixedB_struct hT₂
    rw [hk₁, hs₁] at hrec₁
    rw [hk₂, hs₂] at hrec₂
    apply toL_injective
    rw [hrec₁, hrec₂]
    exact congrArg _ h
  · intro u hu
    obtain ⟨w, hwT, hb, hsw, htake⟩ := exists_fixedB hx hBx hx₀ hs hu
    refine ⟨w, mem_filter.2 ⟨hwT, ?_⟩, htake⟩
    rw [hb, hsw, ← (blocksOf_of_inF hx hBx).1]
  · intro w hw
    obtain ⟨hwT, -, hk, hs'⟩ := hdata w hw
    obtain ⟨-, -, hrs, -⟩ := fixedB_struct hwT
    rw [hrs, hk, hs']

end Words

/-! ### Proposition `prop:Lside` -/

open Classical in
/-- **Proposition `prop:Lside`** (the Lie side of (closed)): for `n ≥ 1`, a primitive `n`-th
root of unity `ζ`, `g ∈ Aut(P)` of order `o` and any choice `B₀(x)` of one block of each
`x ∈ F(P,g)`, `∑_{gC=C} ζ^{r_g(C)} = μ(o) ∑_{x ∈ F(P,g)} e_C(P|_{B₀(x)})`. -/
theorem prop_Lside (h0 : 0 < Fintype.card α) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Fintype.card α))
    (g : α ≃o α) (B₀ : Finset (Finset α) → Finset α) (hB₀ : ∀ x, InF g x → B₀ x ∈ x) :
    fixedClassSum ζ g =
      (ArithmeticFunction.moebius (orderOf g) : ℂ) *
        ∑ x ∈ (univ : Finset (Finset (Finset α))).filter (InF g), (eC (B₀ x) : ℂ) := by
  obtain ⟨x₀⟩ : Nonempty α := Fintype.card_pos_iff.1 h0
  have ho : 0 < orderOf g := orderOf_pos_aut g
  -- one `B_P(x₀)` word per `g`-stable class
  have step1 : fixedClassSum ζ g = ∑ w ∈ fixedB g x₀, ζ ^ rotOf g w := by
    unfold fixedClassSum
    symm
    refine Finset.sum_nbij coset ?_ ?_ ?_ ?_
    · intro w hw
      obtain ⟨hB, hfix⟩ := mem_fixedB.1 hw
      exact mem_filter.2 ⟨(classOf hB.1).2, hfix⟩
    · intro w hw w' hw' h
      exact inB_coset_inj x₀ (mem_fixedB.1 hw).1 (mem_fixedB.1 hw').1 h
    · intro C hC
      obtain ⟨hC, hfix⟩ := mem_filter.1 hC
      obtain ⟨w, hw, rfl⟩ := exists_inB_coset x₀ hC
      exact ⟨w, mem_fixedB.2 ⟨hw, hfix⟩, rfl⟩
    · intro w _; rfl
  rw [step1, ← Finset.sum_fiberwise_of_maps_to
    (t := ((univ : Finset (Finset (Finset α))).filter (InF g)) ×ˢ unitsMod (orderOf g))
    (g := fun w => (blocksOf g (blockOf g w), sOf g w)), Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hxF := (mem_filter.1 hx).2
    obtain ⟨B, hBx, hx₀⟩ := hxF.2.2.2.1 x₀
    have hn := card_eq_of_isBlockSys (blocksOf_of_inF hxF hBx).2
    obtain ⟨j, hj⟩ := hxF.2.2.2.2.2 (B₀ x) (hB₀ x hxF) B hBx
    have heC : eC B = eC (B₀ x) := by rw [hj, eC_image]
    have hprim : IsPrimitiveRoot (ζ ^ B.card) (orderOf g) := hζ.pow h0 (by rw [hn, mul_comm])
    calc ∑ s ∈ unitsMod (orderOf g), ∑ w ∈ (fixedB g x₀).filter
            (fun w => (blocksOf g (blockOf g w), sOf g w) = (x, s)), ζ ^ rotOf g w
        = ∑ s ∈ unitsMod (orderOf g), (eC (B₀ x) : ℂ) * (ζ ^ B.card) ^ s := by
          refine Finset.sum_congr rfl fun s hs => ?_
          obtain ⟨hc, hr⟩ := card_fiber hxF hBx hx₀ hs
          rw [Finset.sum_congr rfl fun w hw => by rw [hr w hw], sum_const, hc, card_BL hx₀,
            heC, nsmul_eq_mul, ← pow_mul, mul_comm s]
      _ = (ArithmeticFunction.moebius (orderOf g) : ℂ) * (eC (B₀ x) : ℂ) := by
          rw [← Finset.mul_sum, unitsMod, sum_pow_coprime_eq_moebius hprim ho, mul_comm]
  · intro w hw
    obtain ⟨-, -, -, hso, -, -, hxF, -⟩ := fixedB_struct hw
    exact mem_product.2 ⟨mem_filter.2 ⟨mem_univ _, hxF⟩, hso⟩

end PosetJKS

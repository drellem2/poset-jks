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

end PosetJKS

import PosetJKS.OrderComplex

/-!
# General tools for the chain complex of a poset

General-purpose facts about the augmented chain complex `Chains`/`bd` of `OrderComplex.lean`,
used for the vanishing of `H̃_d` away from degree `n - 3` (`notes/lean_js_route.md`, §3 and §6).
Nothing here is specific to `OP(P)`.

* Pushforward along an order embedding `f : L ↪o L'` (`chainMapEmb`) is an injective chain map
  (`bd_chainMapEmb`, `chainMapEmb_injective`), functorial (`chainMapEmb_comp_apply`);
  `chainMap φ` for `φ : L ≃o L` is the special case `f = φ` (`chainMap_eq_chainMapEmb`).
* `H̃_d = 0` iff every `d`-cycle is a boundary (`subsingleton_redHom_iff`); this is invariant
  under order isomorphisms (`subsingleton_redHom_congr`) and holds for an empty poset
  (`subsingleton_redHom_of_isEmpty`).
* Inserting an element `t` into a chain `c` at position `j`, when the result is still increasing
  (`insertAt`, built from `Fin.insertNth`; `strictMono_insertNth` gives the betweenness
  criterion). Deleting the inserted element gives `c` back (`face_insertAt_self`); deleting any
  other element commutes with the insertion (`face_insertAt_succAbove`, re-indexed by
  `Fin.predAbove`); hence the boundary of an inserted chain (`bd_single_insertAt`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace PosetJKS

variable {L L' L'' : Type*} [PartialOrder L] [PartialOrder L'] [PartialOrder L'']

/-! ### Pushforward along order embeddings -/

/-- Pushforward of chains along an order embedding `f : L ↪o L'`. -/
noncomputable def chainMapEmb (f : L ↪o L') (m : ℕ) : Chains L m →ₗ[ℂ] Chains L' m :=
  Finsupp.lmapDomain ℂ ℂ fun c => c.trans f

theorem chainMapEmb_single (f : L ↪o L') (m : ℕ) (c : Fin m ↪o L) (a : ℂ) :
    chainMapEmb f m (Finsupp.single c a) = Finsupp.single (c.trans f) a :=
  Finsupp.mapDomain_single

/-- `chainMap` of an order automorphism is the pushforward along its underlying embedding. -/
theorem chainMap_eq_chainMapEmb (φ : L ≃o L) (m : ℕ) :
    chainMap φ m = chainMapEmb φ.toOrderEmbedding m := rfl

theorem face_trans {m : ℕ} (c : Fin (m + 1) ↪o L) (f : L ↪o L') (i : Fin (m + 1)) :
    face (c.trans f) i = (face c i).trans f := rfl

/-- The pushforward along an order embedding is a chain map. -/
theorem bd_chainMapEmb (f : L ↪o L') (m : ℕ) :
    bd L' m ∘ₗ chainMapEmb f (m + 1) = chainMapEmb f m ∘ₗ bd L m := by
  refine Finsupp.lhom_ext' fun c => LinearMap.ext_ring ?_
  change bd L' m (chainMapEmb f (m + 1) (Finsupp.single c 1)) =
    chainMapEmb f m (bd L m (Finsupp.single c 1))
  rw [chainMapEmb_single]
  unfold bd
  erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
  rw [one_smul, one_smul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Chains.single, Chains.single, chainMapEmb_single, face_trans]

theorem bd_chainMapEmb_apply (f : L ↪o L') (m : ℕ) (x : Chains L (m + 1)) :
    bd L' m (chainMapEmb f (m + 1) x) = chainMapEmb f m (bd L m x) :=
  LinearMap.congr_fun (bd_chainMapEmb f m) x

theorem trans_injective {m : ℕ} (f : L ↪o L') :
    Function.Injective fun c : Fin m ↪o L => c.trans f := fun c c' h => by
  ext i
  exact f.injective (DFunLike.congr_fun h i)

theorem chainMapEmb_injective (f : L ↪o L') (m : ℕ) : Function.Injective (chainMapEmb f m) :=
  Finsupp.mapDomain_injective (trans_injective f)

theorem chainMapEmb_comp_apply (f : L ↪o L') (g : L' ↪o L'') (m : ℕ) (x : Chains L m) :
    chainMapEmb g m (chainMapEmb f m x) = chainMapEmb (f.trans g) m x := by
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ x) = Finsupp.mapDomain _ x
  rw [← Finsupp.mapDomain_comp]
  rfl

theorem chainMapEmb_refl_apply (m : ℕ) (x : Chains L m) :
    chainMapEmb (RelEmbedding.refl (· ≤ ·)) m x = x := by
  change Finsupp.mapDomain _ x = x
  have : (fun c : Fin m ↪o L => c.trans (RelEmbedding.refl (· ≤ ·))) = id :=
    funext fun c => by ext; rfl
  rw [this]
  exact Finsupp.mapDomain_id

/-- Pushing forward along `e` and then along `e.symm` is the identity. -/
theorem chainMapEmb_symm_apply (e : L ≃o L') (m : ℕ) (x : Chains L m) :
    chainMapEmb e.symm.toOrderEmbedding m (chainMapEmb e.toOrderEmbedding m x) = x := by
  rw [chainMapEmb_comp_apply]
  have : e.toOrderEmbedding.trans e.symm.toOrderEmbedding = RelEmbedding.refl (· ≤ ·) := by
    ext x; simp
  rw [this, chainMapEmb_refl_apply]

/-! ### Vanishing of reduced homology -/

/-- `H̃_d(Δ(L)) = 0` iff every `d`-cycle is a boundary. -/
theorem subsingleton_redHom_iff (d : ℕ) :
    Subsingleton (redHom L d) ↔
      ∀ z : Chains L (d + 1), bd L d z = 0 → z ∈ LinearMap.range (bd L (d + 1)) := by
  rw [Submodule.Quotient.subsingleton_iff]
  constructor
  · intro h z hz
    have : (⟨z, hz⟩ : cycles L d) ∈ boundaries L d := h ▸ Submodule.mem_top
    exact this
  · intro h
    rw [eq_top_iff]
    rintro ⟨z, hz⟩ -
    exact h z hz

/-- Vanishing of `H̃_d` transported along an order isomorphism. -/
theorem subsingleton_redHom_of_orderIso (e : L ≃o L') (d : ℕ) [hL : Subsingleton (redHom L d)] :
    Subsingleton (redHom L' d) := by
  have hL' := (subsingleton_redHom_iff d).1 hL
  rw [subsingleton_redHom_iff]
  intro z hz
  have hz' : bd L d (chainMapEmb e.symm.toOrderEmbedding (d + 1) z) = 0 := by
    rw [bd_chainMapEmb_apply, hz, map_zero]
  obtain ⟨b, hb⟩ := hL' _ hz'
  refine ⟨chainMapEmb e.toOrderEmbedding (d + 2) b, ?_⟩
  rw [bd_chainMapEmb_apply, hb]
  simpa using chainMapEmb_symm_apply e.symm (d + 1) z

theorem subsingleton_redHom_congr (e : L ≃o L') (d : ℕ) :
    Subsingleton (redHom L d) ↔ Subsingleton (redHom L' d) :=
  ⟨fun _ => subsingleton_redHom_of_orderIso e d,
    fun _ => subsingleton_redHom_of_orderIso e.symm d⟩

instance [IsEmpty L] (m : ℕ) : IsEmpty (Fin (m + 1) ↪o L) := ⟨fun c => isEmptyElim (c 0)⟩

/-- An empty poset has no nonempty chains, so `C_{m+1} = 0`. -/
instance [IsEmpty L] (m : ℕ) : Subsingleton (Chains L (m + 1)) :=
  inferInstanceAs (Subsingleton ((Fin (m + 1) ↪o L) →₀ ℂ))

theorem subsingleton_redHom_of_isEmpty [IsEmpty L] (d : ℕ) : Subsingleton (redHom L d) := by
  rw [subsingleton_redHom_iff]
  intro z _
  rw [Subsingleton.elim z 0]
  exact Submodule.zero_mem _

/-! ### Inserting an element into a chain -/

/-- Inserting `t` at position `j` keeps a chain increasing when `t` lies above the elements
before position `j` and below those from position `j` on. -/
theorem strictMono_insertNth {m : ℕ} (c : Fin m ↪o L) (t : L) (j : Fin (m + 1))
    (hlo : ∀ i : Fin m, i.castSucc < j → c i < t) (hhi : ∀ i : Fin m, j ≤ i.castSucc → t < c i) :
    StrictMono (Fin.insertNth j t c : Fin (m + 1) → L) := by
  have key : ∀ k : Fin (m + 1), k = j ∨ ∃ k' : Fin m, j.succAbove k' = k := fun k => by
    by_cases h : k = j
    · exact Or.inl h
    · exact Or.inr (Fin.exists_succAbove_eq h)
  intro k l hkl
  rcases key k with rfl | ⟨k', rfl⟩ <;> rcases key l with rfl | ⟨l', rfl⟩
  · exact absurd hkl (lt_irrefl _)
  · rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    exact hhi l' ((Fin.lt_succAbove_iff_le_castSucc _ _).1 hkl)
  · rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    exact hlo k' ((Fin.succAbove_lt_iff_castSucc_lt _ _).1 hkl)
  · rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
    exact c.strictMono ((Fin.strictMono_succAbove j).lt_iff_lt.1 hkl)

/-- The chain `c` with `t` inserted at position `j` (given that the result is increasing). -/
def insertAt {m : ℕ} (c : Fin m ↪o L) (t : L) (j : Fin (m + 1))
    (h : StrictMono (Fin.insertNth j t c : Fin (m + 1) → L)) : Fin (m + 1) ↪o L :=
  OrderEmbedding.ofStrictMono _ h

@[simp] theorem insertAt_apply {m : ℕ} (c : Fin m ↪o L) (t : L) (j : Fin (m + 1)) (h)
    (k : Fin (m + 1)) : insertAt c t j h k = (Fin.insertNth j t c : Fin (m + 1) → L) k := rfl

theorem insertAt_apply_self {m : ℕ} (c : Fin m ↪o L) (t : L) (j : Fin (m + 1)) (h) :
    insertAt c t j h j = t := Fin.insertNth_apply_same (α := fun _ => L) _ _ _

theorem insertAt_apply_succAbove {m : ℕ} (c : Fin m ↪o L) (t : L) (j : Fin (m + 1)) (h)
    (i : Fin m) : insertAt c t j h (j.succAbove i) = c i :=
  Fin.insertNth_apply_succAbove (α := fun _ => L) _ _ _ _

/-- Every chain containing `t` at position `j` is an insertion of `t` into its `j`-th face. -/
theorem insertAt_face {m : ℕ} (c : Fin (m + 1) ↪o L) (j : Fin (m + 1)) :
    insertAt (face c j) (c j) j (by rw [show (Fin.insertNth j (c j) (face c j) : Fin (m + 1) → L)
      = c from Fin.insertNth_self_removeNth j c]; exact c.strictMono) = c := by
  ext k
  simp only [insertAt_apply]
  exact congrFun (Fin.insertNth_self_removeNth j c) k

/-- Deleting the inserted element gives the original chain back. -/
theorem face_insertAt_self {m : ℕ} (c : Fin m ↪o L) (t : L) (j : Fin (m + 1)) (h) :
    face (insertAt c t j h) j = c := by
  ext i
  simp [face]

/-- Re-indexing of insertion and deletion: deleting position `j.succAbove i` of `c` with `t`
inserted at `j` is deleting position `i` of `c` and inserting `t` at `i.predAbove j`. -/
theorem insertNth_comp_succAbove_succAbove {m : ℕ} (c : Fin (m + 1) → L) (t : L)
    (j : Fin (m + 2)) (i : Fin (m + 1)) :
    (Fin.insertNth j t c : Fin (m + 2) → L) ∘ (j.succAbove i).succAbove =
      Fin.insertNth (i.predAbove j) t (c ∘ i.succAbove) := by
  symm
  rw [Fin.insertNth_eq_iff]
  refine ⟨?_, ?_⟩
  · simp only [Function.comp_apply, Fin.succAbove_succAbove_predAbove, Fin.insertNth_apply_same]
  · funext k
    simp only [Fin.removeNth, Function.comp_apply, Fin.succAbove_succAbove_succAbove_predAbove,
      Fin.insertNth_apply_succAbove]

theorem strictMono_insertNth_face {m : ℕ} {c : Fin (m + 1) ↪o L} {t : L} {j : Fin (m + 2)}
    (h : StrictMono (Fin.insertNth j t c : Fin (m + 2) → L)) (i : Fin (m + 1)) :
    StrictMono (Fin.insertNth (i.predAbove j) t (face c i) : Fin (m + 1) → L) := by
  have : (Fin.insertNth (i.predAbove j) t (face c i) : Fin (m + 1) → L) =
      (Fin.insertNth j t c : Fin (m + 2) → L) ∘ (j.succAbove i).succAbove :=
    (insertNth_comp_succAbove_succAbove c t j i).symm
  rw [this]
  exact h.comp (Fin.strictMono_succAbove _)

/-- Deleting an element other than the inserted one commutes with the insertion. -/
theorem face_insertAt_succAbove {m : ℕ} (c : Fin (m + 1) ↪o L) (t : L) (j : Fin (m + 2)) (h)
    (i : Fin (m + 1)) :
    face (insertAt c t j h) (j.succAbove i) =
      insertAt (face c i) t (i.predAbove j) (strictMono_insertNth_face h i) := by
  ext k
  have := congrFun (insertNth_comp_succAbove_succAbove c t j i) k
  simp only [Function.comp_apply] at this
  simp only [face, RelEmbedding.coe_trans, Function.comp_apply, Fin.succAboveOrderEmb_apply,
    insertAt_apply]
  rw [this]
  rfl

theorem bd_single (m : ℕ) (c : Fin (m + 1) ↪o L) :
    bd L m (Chains.single L c) =
      ∑ i : Fin (m + 1), ((-1 : ℂ) ^ (i : ℕ)) • Chains.single L (face c i) := by
  unfold bd Chains.single
  erw [Finsupp.linearCombination_single]
  rw [one_smul]

/-- The sign of the face at position `j.succAbove i`: that of `i` below `j`, flipped from `j`
on. -/
theorem neg_one_pow_succAbove {m : ℕ} (j : Fin (m + 2)) (i : Fin (m + 1)) :
    (-1 : ℂ) ^ (j.succAbove i : ℕ) =
      if i.castSucc < j then (-1 : ℂ) ^ (i : ℕ) else -(-1 : ℂ) ^ (i : ℕ) := by
  split_ifs with h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.val_castSucc]
  · rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.1 h), Fin.val_succ, pow_succ]
    ring

/-- The boundary of an inserted chain: the face at the inserted position is `c`, and the other
faces are insertions into the faces of `c`. -/
theorem bd_single_insertAt {m : ℕ} (c : Fin (m + 1) ↪o L) (t : L) (j : Fin (m + 2)) (h) :
    bd L (m + 1) (Chains.single L (insertAt c t j h)) =
      ((-1 : ℂ) ^ (j : ℕ)) • Chains.single L c +
        ∑ i : Fin (m + 1), ((-1 : ℂ) ^ (j.succAbove i : ℕ)) • Chains.single L
          (insertAt (face c i) t (i.predAbove j) (strictMono_insertNth_face h i)) := by
  rw [bd_single, Fin.sum_univ_succAbove _ j, face_insertAt_self]
  simp only [face_insertAt_succAbove]

/-- The augmentation-degree case: inserting into the empty chain. -/
theorem bd_single_insertAt_zero (c : Fin 0 ↪o L) (t : L) (h) :
    bd L 0 (Chains.single L (insertAt c t 0 h)) = Chains.single L c := by
  rw [bd_single, Fin.sum_univ_one, face_insertAt_self]
  simp

/-! ### One-element and empty chains -/

/-- The empty chain. -/
def nilChain (L : Type*) [PartialOrder L] : Fin 0 ↪o L :=
  OrderEmbedding.ofStrictMono Fin.elim0 fun i => i.elim0

theorem eq_nilChain (c : Fin 0 ↪o L) : c = nilChain L := by
  ext i; exact i.elim0

/-- The one-element chain `{x}`. -/
def ptChain (x : L) : Fin 1 ↪o L :=
  OrderEmbedding.ofStrictMono (fun _ => x) fun _ _ h => absurd h (by omega)

theorem ptChain_injective : Function.Injective (ptChain : L → Fin 1 ↪o L) := fun _ _ h =>
  DFunLike.congr_fun h 0

theorem bd_single_ptChain (x : L) :
    bd L 0 (Chains.single L (ptChain x)) = Chains.single L (nilChain L) := by
  rw [bd_single, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_smul]
  rw [eq_nilChain (face _ 0)]

end PosetJKS

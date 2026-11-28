import OMAStatements.S_mo_273275
import Mathlib

-- Problem: mo-273275, is a filtration-preserving linear map between filtered vector spaces
-- with expansions that induces an isomorphism on the associated graded spaces bijective?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Let V = W be the finitely supported sequences of rationals, F_k the sequences vanishing
-- below index k, E_k the multiples of the k-th unit sequence, and phi = id - S with S the right
-- shift (phi is multiplication by 1 - x on polynomials). Then phi preserves the filtration and
-- is the identity on every graded piece, but the sum of the coordinates of phi(f) is 0, so the
-- 0-th unit sequence is not in the image.

namespace MO273275

abbrev V := ℕ →₀ ℚ

def F (k : ℕ) : Submodule ℚ V where
  carrier := {f | ∀ i, i < k → f i = 0}
  add_mem' := by
    intro a b ha hb i hi
    rw [Finsupp.add_apply, ha i hi, hb i hi, add_zero]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c a ha i hi
    rw [Finsupp.smul_apply, ha i hi, smul_zero]

def E (k : ℕ) : Submodule ℚ V where
  carrier := {f | ∀ i, i ≠ k → f i = 0}
  add_mem' := by
    intro a b ha hb i hi
    rw [Finsupp.add_apply, ha i hi, hb i hi, add_zero]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c a ha i hi
    rw [Finsupp.smul_apply, ha i hi, smul_zero]

theorem mem_F (k : ℕ) (f : V) : f ∈ F k ↔ ∀ i, i < k → f i = 0 := Iff.rfl

theorem mem_E (k : ℕ) (f : V) : f ∈ E k ↔ ∀ i, i ≠ k → f i = 0 := Iff.rfl

noncomputable def S : V →ₗ[ℚ] V := Finsupp.lmapDomain ℚ ℚ Nat.succ

noncomputable def φ : V →ₗ[ℚ] V := LinearMap.id - S

noncomputable def L : V →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ (fun _ : ℕ => (1 : ℚ))

theorem S_zero (f : V) : S f 0 = 0 := by
  unfold S
  rw [Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_notin_range f 0 (by simp)

theorem S_succ (f : V) (i : ℕ) : S f (i + 1) = f i := by
  unfold S
  rw [Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_apply Nat.succ_injective f i

theorem phi_zero (f : V) : φ f 0 = f 0 := by
  unfold φ
  rw [LinearMap.sub_apply, LinearMap.id_apply, Finsupp.sub_apply, S_zero, sub_zero]

theorem phi_succ (f : V) (i : ℕ) : φ f (i + 1) = f (i + 1) - f i := by
  unfold φ
  rw [LinearMap.sub_apply, LinearMap.id_apply, Finsupp.sub_apply, S_succ]

theorem F_zero : F 0 = ⊤ := by
  rw [eq_top_iff]
  intro f _
  rw [mem_F]
  intro i hi
  exact absurd hi (Nat.not_lt_zero i)

theorem F_anti : Antitone F := by
  intro a b hab f hf
  rw [mem_F] at hf ⊢
  intro i hi
  exact hf i (by omega)

theorem E_le (k : ℕ) : E k ≤ F k := by
  intro f hf
  rw [mem_E] at hf
  rw [mem_F]
  intro i hi
  exact hf i (by omega)

theorem E_sup (k : ℕ) : E k ⊔ F (k + 1) = F k := by
  apply le_antisymm
  · apply sup_le (E_le k)
    intro f hf
    rw [mem_F] at hf ⊢
    intro i hi
    exact hf i (by omega)
  · intro f hf
    rw [mem_F] at hf
    rw [Submodule.mem_sup]
    refine ⟨Finsupp.single k (f k), ?_, f - Finsupp.single k (f k), ?_, by abel⟩
    · rw [mem_E]
      intro i hi
      rw [Finsupp.single_apply, if_neg (fun h => hi h.symm)]
    · rw [mem_F]
      intro i hi
      rw [Finsupp.sub_apply, Finsupp.single_apply]
      by_cases hik : k = i
      · rw [if_pos hik, hik]
        exact sub_self _
      · rw [if_neg hik, sub_zero]
        exact hf i (by omega)

theorem E_disj (k : ℕ) : Disjoint (E k) (F (k + 1)) := by
  rw [Submodule.disjoint_def]
  intro f hE hF
  rw [mem_E] at hE
  rw [mem_F] at hF
  ext i
  show f i = 0
  by_cases hik : i = k
  · rw [hik]
    exact hF k (by omega)
  · exact hE i hik

theorem E_internal : DirectSum.IsInternal E := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · intro k
    have hle : (⨆ j, ⨆ (_ : j ≠ k), E j) ≤
        LinearMap.ker (Finsupp.lapply (R := ℚ) (M := ℚ) k) := by
      apply iSup_le
      intro j
      apply iSup_le
      intro hj
      intro f hf
      rw [mem_E] at hf
      rw [LinearMap.mem_ker, Finsupp.lapply_apply]
      exact hf k (fun h => hj h.symm)
    refine Disjoint.mono_right hle ?_
    rw [Submodule.disjoint_def]
    intro f hE hker
    rw [mem_E] at hE
    rw [LinearMap.mem_ker, Finsupp.lapply_apply] at hker
    ext i
    show f i = 0
    by_cases hik : i = k
    · rw [hik]
      exact hker
    · exact hE i hik
  · rw [eq_top_iff]
    intro f _
    rw [← Finsupp.sum_single f, Finsupp.sum]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.mem_iSup_of_mem i
    rw [mem_E]
    intro j hj
    rw [Finsupp.single_apply, if_neg (fun h => hj h.symm)]

theorem pres (k : ℕ) (v : V) (hv : v ∈ F k) : φ v ∈ F k := by
  rw [mem_F] at hv ⊢
  intro i hi
  cases i with
  | zero =>
    rw [phi_zero]
    exact hv 0 hi
  | succ j =>
    rw [phi_succ, hv (j + 1) hi, hv j (by omega), sub_zero]

theorem strict (k : ℕ) (v : V) (hv : v ∈ F k) (h : φ v ∈ F (k + 1)) : v ∈ F (k + 1) := by
  rw [mem_F] at hv h ⊢
  intro i hi
  by_cases hik : i < k
  · exact hv i hik
  · have hik' : i = k := by omega
    have h1 := h i hi
    cases i with
    | zero =>
      rw [phi_zero] at h1
      exact h1
    | succ j =>
      rw [phi_succ, hv j (by omega), sub_zero] at h1
      exact h1

theorem approx (k : ℕ) (w : V) (hw : w ∈ F k) : ∃ v ∈ F k, w - φ v ∈ F (k + 1) := by
  rw [mem_F] at hw
  refine ⟨Finsupp.single k (w k), ?_, ?_⟩
  · rw [mem_F]
    intro i hi
    rw [Finsupp.single_apply, if_neg (show ¬ k = i by omega)]
  · rw [mem_F]
    intro i hi
    rw [Finsupp.sub_apply]
    cases i with
    | zero =>
      rw [phi_zero, Finsupp.single_apply]
      by_cases hk : k = 0
      · rw [if_pos hk, hk]
        exact sub_self _
      · rw [if_neg hk, sub_zero]
        exact hw 0 (by omega)
    | succ j =>
      rw [phi_succ, Finsupp.single_apply, Finsupp.single_apply]
      by_cases hk : k = j + 1
      · rw [if_pos hk, if_neg (show ¬ k = j by omega), hk, sub_zero]
        exact sub_self _
      · rw [if_neg hk, if_neg (show ¬ k = j by omega), sub_zero, sub_zero]
        exact hw (j + 1) (by omega)

theorem L_S (f : V) : L (S f) = L f := by
  unfold L S
  rw [Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain]
  rfl

theorem L_phi (f : V) : L (φ f) = 0 := by
  unfold φ
  rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, L_S, sub_self]

theorem L_single : L (Finsupp.single 0 1) = 1 := by
  unfold L
  rw [Finsupp.linearCombination_single]
  norm_num

end MO273275

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_273275.main) := by
  intro h
  have hE : ∃ E : ℕ → Submodule ℚ MO273275.V,
      (∀ k, E k ≤ MO273275.F k ∧ E k ⊔ MO273275.F (k + 1) = MO273275.F k ∧
        Disjoint (E k) (MO273275.F (k + 1))) ∧ DirectSum.IsInternal E :=
    ⟨MO273275.E, fun k => ⟨MO273275.E_le k, MO273275.E_sup k, MO273275.E_disj k⟩,
      MO273275.E_internal⟩
  have hbij := h ℚ MO273275.V MO273275.V MO273275.F MO273275.F MO273275.F_zero
    MO273275.F_anti MO273275.F_zero MO273275.F_anti hE hE MO273275.φ MO273275.pres
    MO273275.strict MO273275.approx
  obtain ⟨f, hf⟩ := hbij.2 (Finsupp.single 0 1)
  have h1 := MO273275.L_phi f
  rw [hf, MO273275.L_single] at h1
  norm_num at h1

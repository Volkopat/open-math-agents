import OMAStatements.S_mo_363072
import Mathlib.Analysis.Convex.Birkhoff

/-! The stochastic perturbation is from @carl2sheriff's proof (#9045).
The assignment inequality is extended from permutation matrices to their convex hull
by a linear half-space, avoiding an explicit weighted-sum expansion. -/

theorem OMA.solution : type_of% @OMA.S_mo_363072.main := by
  intro n A B hrow hcol hB σ hon hoff hmax
  classical
  set m : ℝ := 1 + ∑ i, A i (σ i) with hm
  have hdiag : ∀ i, A i (σ i) ≤ ∑ k, A k (σ k) :=
    fun i => Finset.single_le_sum (f := fun k => A k (σ k)) (fun k _ => hon k) (Finset.mem_univ i)
  have hsum0 : 0 ≤ ∑ k, A k (σ k) := Finset.sum_nonneg (fun k _ => hon k)
  have mpos : 0 < m := by rw [hm]; linarith
  let S : Matrix (Fin n) (Fin n) ℝ := fun i j => (if j = σ i then 1 else 0) - A i j / m
  have hS : S ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      by_cases h : j = σ i
      · subst h
        have := hdiag i
        simp only [S, if_true]
        rw [sub_nonneg, div_le_one mpos]; rw [hm]; linarith
      · simp only [S, h, if_false]
        have := hoff i j h
        have : A i j / m ≤ 0 := div_nonpos_of_nonpos_of_nonneg this mpos.le
        linarith
    · intro i
      simp only [S, Finset.sum_sub_distrib, ← Finset.sum_div, hrow i]
      simp
    · intro j
      simp only [S, Finset.sum_sub_distrib, ← Finset.sum_div, hcol j]
      have e : ∀ x, (j = σ x) ↔ (σ.symm j = x) := fun x => (Equiv.symm_apply_eq σ).symm
      simp only [e, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp
  have hle : ∑ i, ∑ j, S i j * B i j ≤ ∑ i, B i (σ i) := by
    have hlin : IsLinearMap ℝ (fun M : Matrix (Fin n) (Fin n) ℝ =>
        ∑ i, ∑ j, M i j * B i j) :=
      ⟨by intros; simp [add_mul, Finset.sum_add_distrib],
       by intros; simp [mul_assoc, Finset.mul_sum]⟩
    change S ∈ (doublyStochastic ℝ (Fin n) : Set _) at hS
    rw [doublyStochastic_eq_convexHull_permMatrix] at hS
    apply convexHull_min ?_ (convex_halfSpace_le hlin _) hS
    rintro _ ⟨τ, rfl⟩
    simpa [Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, ite_mul] using hmax τ
  have key : ∑ i, ∑ j, A i j * B i j = m * (∑ i, B i (σ i) - ∑ i, ∑ j, S i j * B i j) := by
    have e : ∑ i, ∑ j, S i j * B i j = ∑ i, B i (σ i) - (∑ i, ∑ j, A i j * B i j) / m := by
      simp only [S, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [e]
    field_simp
    ring
  rw [key]
  exact mul_nonneg mpos.le (by linarith)

import OMAStatements.S_oeis_a127711
import Mathlib.Tactic

namespace OMA.P_oeis_a127711

private def L (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ := fun i j =>
  if j.val ≤ i.val ∧ i.val ≤ 2 * j.val then 1 else 0

private lemma L_det_eq_one (N : ℕ) : (L N).det = 1 := by
  rw [Matrix.det_apply]
  have hterm : ∀ σ : Equiv.Perm (Fin (N + 1)), σ ≠ 1 →
      Equiv.Perm.sign σ • ∏ i : Fin (N + 1), L N (σ i) i = 0 := by
    intro σ hσ
    let S : Finset (Fin (N + 1)) := Finset.univ.filter (fun i => σ i ≠ i)
    have hS : S.Nonempty := by
      by_contra hne
      apply hσ
      exact Equiv.ext fun i => by
        by_contra hi
        exact hne ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    obtain ⟨i₁, hi₁_mem, hi₁_max⟩ := Finset.exists_max_image S Fin.val hS
    have hi₁_ne : σ i₁ ≠ i₁ := (Finset.mem_filter.mp hi₁_mem).2
    have hσi₁_mem : σ i₁ ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro heq
      exact hi₁_ne (σ.injective heq)
    have hle : (σ i₁).val ≤ i₁.val := hi₁_max (σ i₁) hσi₁_mem
    have hlt : (σ i₁).val < i₁.val :=
      lt_of_le_of_ne hle (fun h => hi₁_ne (Fin.ext h))
    have hzero : L N (σ i₁) i₁ = 0 := by
      dsimp only [L]
      split_ifs with hcond
      · omega
      · rfl
    have hprod : (∏ i : Fin (N + 1), L N (σ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i₁) hzero
    rw [hprod, smul_zero]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin (N + 1))) (fun σ _ hσ => hterm σ hσ)
    (fun h => absurd (Finset.mem_univ 1) h)]
  have hdiag : ∀ i : Fin (N + 1), L N i i = 1 := by
    intro i
    dsimp only [L]
    split_ifs with hcond
    · rfl
    · exfalso; apply hcond; exact ⟨le_rfl, by omega⟩
  simp [hdiag]

end OMA.P_oeis_a127711

theorem OMA.solution : type_of% @OMA.S_oeis_a127711.main := by
  intro N i j
  let L := OMA.P_oeis_a127711.L N
  have hunit : IsUnit L.det := by
    rw [OMA.P_oeis_a127711.L_det_eq_one]
    exact isUnit_one
  have hML : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul L hunit
  let B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ := fun r c =>
    (L⁻¹) r c * (Nat.fib (c.val + 1) : ℤ)
  have hleft : B.map Int.cast * OMA.S_oeis_a127711.triangle N = 1 := by
    ext r k
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hterm : ∀ c : Fin (N + 1),
        (B.map Int.cast) r c * OMA.S_oeis_a127711.triangle N c k =
          (((L⁻¹) r c * L c k : ℤ) : ℚ) := by
      intro c
      have hBc : (B.map Int.cast) r c = (L⁻¹ r c : ℚ) * (Nat.fib (c.val + 1) : ℚ) := by
        rw [Matrix.map_apply]
        simp only [B, Int.cast_mul, Int.cast_natCast]
      have hLck : ((L c k : ℤ) : ℚ) = if k.val ≤ c.val ∧ c.val ≤ 2 * k.val then 1 else 0 := by
        dsimp [L, OMA.P_oeis_a127711.L]
        split_ifs <;> simp
      rw [hBc, Int.cast_mul, hLck]
      dsimp only [OMA.S_oeis_a127711.triangle]
      split_ifs with hcond
      · have hfib : (Nat.fib (c.val + 1) : ℚ) ≠ 0 := by
          exact_mod_cast (Nat.fib_pos.2 (Nat.succ_pos c.val)).ne'
        rw [mul_one, mul_assoc, mul_inv_cancel₀ hfib, mul_one]
      · simp
    simp_rw [hterm]
    have hsum : (∑ c : Fin (N + 1), (((L⁻¹) r c * L c k : ℤ) : ℚ)) =
        (((L⁻¹ * L) r k : ℤ) : ℚ) := by
      rw [Matrix.mul_apply]
      push_cast
      rfl
    rw [hsum, hML, Matrix.one_apply]
    split_ifs <;> simp
  have hinv : (OMA.S_oeis_a127711.triangle N)⁻¹ = B.map Int.cast :=
    Matrix.inv_eq_left_inv hleft
  refine ⟨B i j, ?_⟩
  rw [hinv]
  rfl

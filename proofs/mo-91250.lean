import OMAStatements.S_mo_91250

/-!
# Determinant of a sum of two matrices (one dominating the other)

Source: Sasho Nikolov's question on MathOverflow, https://mathoverflow.net/questions/91250.
Proof by @grp06 (#26905), using the Leibniz formula with the explicit threshold K = n.
The earlier companion by @etaubman, linked from statement #20478, also proves
this dimension-dependent threshold. This retains the merged proof's direct
entry bound and replaces only its explicit sign cases by the unit-action norm API.
No dimension-independent threshold or general K = 2 claim is made.
-/

-- The standard unit-action norm identity removes the explicit sign cases.

open scoped BigOperators
open OMA.S_mo_91250

private theorem det_le_factorial_mul_pow {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (T : ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hT : ∀ i j, A i j ≤ T) :
    |A.det| ≤ (Nat.factorial n : ℝ) * T ^ n := by
  classical
  have hterm (σ : Equiv.Perm (Fin n)) :
      |Equiv.Perm.sign σ • ∏ i : Fin n, A (σ i) i| ≤ T ^ n := by
    have hprod :
        (∏ i : Fin n, A (σ i) i) ≤ ∏ _ : Fin n, T :=
      Finset.prod_le_prod (fun i _ => hA (σ i) i) (fun i _ => hT (σ i) i)
    rw [← Real.norm_eq_abs, norm_units_zsmul, Real.norm_eq_abs,
      abs_of_nonneg (Finset.prod_nonneg (fun i _ => hA (σ i) i))]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod
  rw [Matrix.det_apply]
  calc
    |∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i : Fin n, A (σ i) i| ≤
        ∑ σ : Equiv.Perm (Fin n), |Equiv.Perm.sign σ • ∏ i : Fin n, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Equiv.Perm (Fin n), T ^ n :=
      Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (Nat.factorial n : ℝ) * T ^ n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul]

theorem OMA.solution : type_of% @OMA.S_mo_91250.main := by
  classical
  intro n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine ⟨(n : ℝ), hnR, ?_⟩
  intro K' hK A B hA hB hdom
  by_cases hzero : B = 0
  · refine ⟨n, hn, le_rfl, id, id, Function.injective_id, Function.injective_id, ?_⟩
    simp only [hzero, add_zero, Matrix.submatrix_id_id, le_refl]
  · have hex : ∃ i j, B i j ≠ 0 := by
      by_contra! hall
      apply hzero
      ext i j
      simpa using hall i j
    obtain ⟨i, j, hij⟩ := hex
    have hb : 0 ≤ B i j := hB i j
    have hentry (r s : Fin n) : A r s ≤ B i j / (n : ℝ) := by
      apply (le_div_iff₀ hnR).2
      calc
        A r s * (n : ℝ) ≤ A r s * K' := mul_le_mul_of_nonneg_left hK (hA r s)
        _ = K' * A r s := mul_comm _ _
        _ ≤ B i j := hdom i j hij r s
    have hfactorial : (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ n := by
      exact_mod_cast Nat.factorial_le_pow n
    have hdet : |A.det| ≤ (B i j) ^ n := calc
      |A.det| ≤ (Nat.factorial n : ℝ) * (B i j / (n : ℝ)) ^ n :=
        det_le_factorial_mul_pow A _ hA hentry
      _ ≤ (n : ℝ) ^ n * (B i j / (n : ℝ)) ^ n :=
        mul_le_mul_of_nonneg_right hfactorial (pow_nonneg (div_nonneg hb hnR.le) _)
      _ = (B i j) ^ n := by
        rw [← mul_pow, mul_comm (n : ℝ), div_mul_cancel₀ _ hnR.ne']
    have hroot : |A.det| ^ (1 / (n : ℝ)) ≤ B i j := by
      calc
        |A.det| ^ (1 / (n : ℝ)) ≤ ((B i j) ^ n) ^ (1 / (n : ℝ)) :=
          Real.rpow_le_rpow (abs_nonneg _) hdet (div_nonneg zero_le_one hnR.le)
        _ = B i j := by
          rw [one_div, Real.pow_rpow_inv_natCast hb (Nat.ne_of_gt hn)]
    refine ⟨1, Nat.one_pos, hn, (fun _ => i), (fun _ => j), ?_, ?_, ?_⟩
    · intro a b _
      exact Subsingleton.elim a b
    · intro a b _
      exact Subsingleton.elim a b
    · rw [Matrix.det_fin_one, Matrix.submatrix_apply, Matrix.add_apply]
      simp only [Nat.cast_one, div_one, Real.rpow_one,
        abs_of_nonneg (add_nonneg (hA i j) hb)]
      exact hroot.trans (le_add_of_nonneg_left (hA i j))

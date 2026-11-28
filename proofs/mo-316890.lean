import OMAStatements.S_mo_316890

namespace OMA.S_mo_316890.Proof

open Matrix Finset WithLp
open scoped Matrix.Norms.L2Operator RealInnerProductSpace

private lemma adjoint_comp_self_toEuclideanLin {n : ℕ} (A : Mat n) :
    A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin = (Aᵀ * A).toEuclideanLin := by
  ext1 x
  apply ext_inner_left ℝ
  intro y
  have h1 : ⟪y, (A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin) x⟫ =
      ⟪A.toEuclideanLin y, A.toEuclideanLin x⟫ := by
    simp [LinearMap.adjoint_inner_right]
  have h2 : ⟪A.toEuclideanLin y, A.toEuclideanLin x⟫ = (A *ᵥ y.ofLp) ⬝ᵥ (A *ᵥ x.ofLp) := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial, dotProduct]
    refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h3 : ⟪y, (Aᵀ * A).toEuclideanLin x⟫ = y.ofLp ⬝ᵥ ((Aᵀ * A) *ᵥ x.ofLp) := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial, dotProduct]
    refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h1, h2, h3]
  symm
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

private lemma toMatrix_adjoint_comp_self {n : ℕ} (A : Mat n) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin) = Aᵀ * A := by
  rw [adjoint_comp_self_toEuclideanLin A]
  ext i j
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr, Matrix.toLpLin_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct]

private lemma sum_sq_sv {n : ℕ} (A : Mat n) :
    ∑ i : Fin n, (sv A i.val) ^ 2 = ∑ i : Fin n, ∑ j : Fin n, (A i j) ^ 2 := by
  set T := A.toEuclideanLin
  set S := T.adjoint ∘ₗ T
  have hS : S.IsSymmetric := T.isSymmetric_adjoint_comp_self
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have htr1 : LinearMap.trace ℝ _ S = ∑ i : Fin n, (sv A i.val) ^ 2 := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (hS.eigenvectorBasis hn).toBasis S,
      hS.toMatrix_eigenvectorBasis hn, Matrix.trace_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
    exact (T.sq_singularValues_fin hn i).symm
  have htr2 : LinearMap.trace ℝ _ S = (Aᵀ * A).trace := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis S,
      toMatrix_adjoint_comp_self A]
  rw [← htr1, htr2]
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, sq]
  rw [Finset.sum_comm]

private lemma prod_sq_sv {n : ℕ} (A : Mat n) :
    ∏ i : Fin n, (sv A i.val) ^ 2 = A.det ^ 2 := by
  set T := A.toEuclideanLin
  set S := T.adjoint ∘ₗ T
  have hS : S.IsSymmetric := T.isSymmetric_adjoint_comp_self
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hdet1 : S.det = ∏ i : Fin n, (sv A i.val) ^ 2 := by
    rw [hS.det_eq_prod_eigenvalues hn]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact (T.sq_singularValues_fin hn i).symm
  have hdet2 : S.det = (Aᵀ * A).det := by
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis S,
      toMatrix_adjoint_comp_self A]
  rw [← hdet1, hdet2, Matrix.det_mul, Matrix.det_transpose, sq]

private lemma sum_sq_sv_eq_mass {n : ℕ} {A : Mat n} (hbin : binary A) :
    ∑ i : Fin n, (sv A i.val) ^ 2 = mass A := by
  rw [sum_sq_sv]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rcases hbin i j with h | h <;> simp [h]

private lemma one_le_det_sq_of_binary {n : ℕ} {A : Mat n} (hbin : binary A) (hdet : A.det ≠ 0) :
    1 ≤ A.det ^ 2 := by
  let B : Matrix (Fin n) (Fin n) ℤ := fun i j => if A i j = 0 then 0 else 1
  have hAB : A = B.map (Int.castRingHom ℝ) := by
    ext i j
    change A i j = (B i j : ℝ)
    dsimp only [B]
    rcases hbin i j with h | h <;> simp [h]
  have hdet_eq : A.det = (B.det : ℝ) := by
    rw [hAB]
    exact ((Int.castRingHom ℝ).map_det B).symm
  have hBne : B.det ≠ 0 := by
    intro h0
    apply hdet
    rw [hdet_eq, h0, Int.cast_zero]
  have hBsq : (1 : ℤ) ≤ B.det ^ 2 := by
    have hpos : (0 : ℤ) < B.det ^ 2 := sq_pos_of_ne_zero hBne
    omega
  rw [hdet_eq]
  exact_mod_cast hBsq

private lemma part1 {n : ℕ} (_hn : 1 ≤ n) (A : Mat n) (hbin : binary A) (hdet : A.det ≠ 0)
    (i : Fin n) :
    ((i.val : ℝ) + 1) * (sv A i.val) ^ 2 ≤ mass A ∧
      (((n - 1 : ℕ) : ℝ)) ^ (n - 1) ≤ (sv A i.val) ^ 2 * (mass A) ^ (n - 1) := by
  have hsum : ∑ k : Fin n, (sv A k.val) ^ 2 = mass A := sum_sq_sv_eq_mass hbin
  have hprod : ∏ k : Fin n, (sv A k.val) ^ 2 = A.det ^ 2 := prod_sq_sv A
  have hdet1 : 1 ≤ A.det ^ 2 := one_le_det_sq_of_binary hbin hdet
  have hanti : Antitone (sv A) := A.toEuclideanLin.singularValues_antitone
  have hnn : ∀ k : Fin n, 0 ≤ sv A k.val := fun k => A.toEuclideanLin.singularValues_nonneg k.val
  constructor
  · have hcard : (Finset.Iic i).card = i.val + 1 := by
      simp [Fin.card_Iic]
    have hle1 : ((i.val : ℝ) + 1) * (sv A i.val) ^ 2 ≤
        ∑ k ∈ Finset.Iic i, (sv A k.val) ^ 2 := by
      have hconst : ∑ _k ∈ Finset.Iic i, (sv A i.val) ^ 2 =
          ((i.val : ℝ) + 1) * (sv A i.val) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        push_cast
        ring
      rw [← hconst]
      refine Finset.sum_le_sum fun k hk => ?_
      have hki : k ≤ i := Finset.mem_Iic.mp hk
      have hsv : sv A i.val ≤ sv A k.val := hanti hki
      exact pow_le_pow_left₀ (hnn i) hsv 2
    have hle2 : ∑ k ∈ Finset.Iic i, (sv A k.val) ^ 2 ≤ ∑ k : Fin n, (sv A k.val) ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg fun k => sq_nonneg _
    linarith
  · by_cases hn1 : n = 1
    · subst hn1
      simp only [Nat.sub_self, Nat.cast_zero, pow_zero, mul_one]
      have hprod1 : ∏ k : Fin 1, (sv A k.val) ^ 2 = (sv A i.val) ^ 2 := by
        have hi0 : i = 0 := Subsingleton.elim i 0
        subst hi0
        simp
      linarith
    · have hm_pos : 0 < n - 1 := by omega
      let s : Finset (Fin n) := Finset.univ.erase i
      have hscard : s.card = n - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      have hscard_pos : (0 : ℝ) < (s.card : ℝ) := by
        rw [hscard]
        exact Nat.cast_pos.mpr hm_pos
      have hprod_split : (sv A i.val) ^ 2 * ∏ k ∈ s, (sv A k.val) ^ 2 = A.det ^ 2 := by
        rw [← hprod]
        exact Finset.mul_prod_erase Finset.univ (fun k => (sv A k.val) ^ 2) (Finset.mem_univ i)
      have hsum_s : ∑ k ∈ s, (sv A k.val) ^ 2 ≤ mass A := by
        rw [← hsum]
        exact Finset.sum_le_univ_sum_of_nonneg fun k => sq_nonneg _
      have hamgm := Real.geom_mean_le_arith_mean s (fun _ => (1 : ℝ))
        (fun k => (sv A k.val) ^ 2) (fun _ _ => zero_le_one)
        (by simp [hscard_pos]) (fun _ _ => sq_nonneg _)
      simp only [Real.rpow_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at hamgm
      have hprod_nn : 0 ≤ ∏ k ∈ s, (sv A k.val) ^ 2 :=
        Finset.prod_nonneg fun _ _ => sq_nonneg _
      have hpow : ∏ k ∈ s, (sv A k.val) ^ 2 ≤ ((∑ k ∈ s, (sv A k.val) ^ 2) / (s.card : ℝ)) ^ s.card := by
        have h1 := pow_le_pow_left₀ (Real.rpow_nonneg hprod_nn _) hamgm s.card
        rw [← Real.rpow_natCast, ← Real.rpow_mul hprod_nn,
          inv_mul_cancel₀ (ne_of_gt hscard_pos), Real.rpow_one] at h1
        exact h1
      have hpow2 : ∏ k ∈ s, (sv A k.val) ^ 2 ≤ (mass A / ((n - 1 : ℕ) : ℝ)) ^ (n - 1) := by
        rw [← hscard]
        refine hpow.trans (pow_le_pow_left₀ ?_ ?_ _)
        · exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (le_of_lt hscard_pos)
        · exact div_le_div_of_nonneg_right hsum_s (le_of_lt hscard_pos)
      have hdenom_pos : (0 : ℝ) < (((n - 1 : ℕ) : ℝ)) ^ (n - 1) := by
        positivity
      rw [div_pow] at hpow2
      have hmul : (sv A i.val) ^ 2 * ∏ k ∈ s, (sv A k.val) ^ 2 ≤
          (sv A i.val) ^ 2 * ((mass A) ^ (n - 1) / (((n - 1 : ℕ) : ℝ)) ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left hpow2 (sq_nonneg _)
      have h1le : 1 ≤ (sv A i.val) ^ 2 * ((mass A) ^ (n - 1) / (((n - 1 : ℕ) : ℝ)) ^ (n - 1)) := by
        linarith
      have hfin := mul_le_mul_of_nonneg_right h1le (le_of_lt hdenom_pos)
      rw [one_mul, mul_assoc, div_mul_cancel₀ _ (ne_of_gt hdenom_pos)] at hfin
      exact hfin

private lemma det_eq_one_of_unitUpper {n : ℕ} {A : Mat n} (hA : unitUpper A) : A.det = 1 := by
  have htri : A.IsUpperTriangular := fun i j hji => hA.2.2 i j hji
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [hA.2.1]

private lemma inv_mul_eq_one_of_unitUpper {n : ℕ} {A : Mat n} (hA : unitUpper A) :
    A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A (by rw [det_eq_one_of_unitUpper hA]; exact isUnit_one)

private lemma inv_lower_zero_of_unitUpper {n : ℕ} {A : Mat n} (hA : unitUpper A) :
    ∀ (i j : Fin n), j < i → A⁻¹ i j = 0 := by
  intro i j
  induction hj : j.val using Nat.strong_induction_on generalizing j with
  | _ m ih =>
    intro hji
    have hmul : (A⁻¹ * A) i j = 0 := by
      rw [inv_mul_eq_one_of_unitUpper hA, Matrix.one_apply_ne (ne_of_gt hji)]
    rw [Matrix.mul_apply] at hmul
    have hsum : ∑ k : Fin n, A⁻¹ i k * A k j = A⁻¹ i j := by
      rw [Finset.sum_eq_single j]
      · rw [hA.2.1 j, mul_one]
      · intro k _ hkj
        rcases lt_or_gt_of_ne hkj with hlt | hgt
        · have hklt : k.val < m := by omega
          rw [ih k.val hklt k rfl (lt_trans hlt hji), zero_mul]
        · rw [hA.2.2 k j hgt, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    linarith

private lemma inv_diag_one_of_unitUpper {n : ℕ} {A : Mat n} (hA : unitUpper A) (i : Fin n) :
    A⁻¹ i i = 1 := by
  have hmul : (A⁻¹ * A) i i = 1 := by
    rw [inv_mul_eq_one_of_unitUpper hA, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at hmul
  have hsum : ∑ k : Fin n, A⁻¹ i k * A k i = A⁻¹ i i := by
    rw [Finset.sum_eq_single i]
    · rw [hA.2.1 i, mul_one]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with hlt | hgt
      · rw [inv_lower_zero_of_unitUpper hA i k hlt, zero_mul]
      · rw [hA.2.2 k i hgt, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  linarith

private lemma inv_step_eq_of_unitUpper {n : ℕ} {A : Mat n} (hA : unitUpper A)
    (i : Fin n) {m : ℕ} (hm : 1 ≤ m) (hmn : i.val + m < n) :
    A⁻¹ i ⟨i.val + m, hmn⟩ =
      - ∑ r : Fin m,
          A⁻¹ i ⟨i.val + r.val, by omega⟩ * A ⟨i.val + r.val, by omega⟩ ⟨i.val + m, hmn⟩ := by
  let j : Fin n := ⟨i.val + m, hmn⟩
  have hij : i < j := by
    change i.val < i.val + m
    omega
  have hmul : (A⁻¹ * A) i j = 0 := by
    rw [inv_mul_eq_one_of_unitUpper hA, Matrix.one_apply_ne (ne_of_lt hij)]
  rw [Matrix.mul_apply] at hmul
  have hsplit : ∑ k : Fin n, A⁻¹ i k * A k j =
      A⁻¹ i j + ∑ k ∈ Finset.univ.filter (fun k : Fin n => i ≤ k ∧ k < j), A⁻¹ i k * A k j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hA.2.1 j, mul_one]
    congr 1
    refine (Finset.sum_subset (fun k hk => ?_) fun k hk hnot => ?_).symm
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact Finset.mem_erase.mpr ⟨ne_of_lt hk.2, Finset.mem_univ k⟩
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_le, not_lt] at hnot
      rcases hnot with hki | hjk
      · rw [inv_lower_zero_of_unitUpper hA i k hki, zero_mul]
      · have hgt : j < k := lt_of_le_of_ne hjk (Ne.symm hk)
        rw [hA.2.2 k j hgt, mul_zero]
  have hreindex :
      ∑ r : Fin m, A⁻¹ i ⟨i.val + r.val, by omega⟩ * A ⟨i.val + r.val, by omega⟩ j =
        ∑ k ∈ Finset.univ.filter (fun k : Fin n => i ≤ k ∧ k < j), A⁻¹ i k * A k j := by
    refine Finset.sum_nbij (fun r : Fin m => (⟨i.val + r.val, by omega⟩ : Fin n)) ?_ ?_ ?_ ?_
    · intro r _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨show i.val ≤ i.val + r.val by omega, show i.val + r.val < i.val + m by omega⟩
    · intro r₁ _ r₂ _ heq
      have hval := congrArg Fin.val heq
      apply Fin.ext
      dsimp at hval
      omega
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have h1 : i.val ≤ k.val := hk.1
      have h2 : k.val < i.val + m := hk.2
      refine ⟨⟨k.val - i.val, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      apply Fin.ext
      dsimp
      omega
    · intro _ _
      rfl
  rw [hsplit, ← hreindex] at hmul
  linarith

private lemma part2 {n : ℕ} (A : Mat n) (hA : unitUpper A) (i j : Fin n) :
    |A⁻¹ i j| ≤ fibEnvelope n i j := by
  by_cases hij : i = j
  · subst hij
    simp [fibEnvelope, inv_diag_one_of_unitUpper hA i]
  · by_cases hlt : i < j
    · simp only [fibEnvelope, hij, ↓reduceIte, hlt]
      let x : ℕ → ℝ := fun r => if h : i.val + r < n then A⁻¹ i ⟨i.val + r, h⟩ else 0
      let P : ℕ → ℝ := fun m => ∑ r ∈ Finset.range m, max (x r) 0
      let N : ℕ → ℝ := fun m => ∑ r ∈ Finset.range m, max (-(x r)) 0
      have hx0 : x 0 = 1 := by
        have hi : i.val + 0 < n := by omega
        simp only [x, hi, ↓reduceDIte]
        have hi0 : (⟨i.val + 0, hi⟩ : Fin n) = i := Fin.ext (by simp)
        rw [hi0]
        exact inv_diag_one_of_unitUpper hA i
      have hbound : ∀ m, 1 ≤ m → -P m ≤ x m ∧ x m ≤ N m := by
        intro m hm
        by_cases hmn : i.val + m < n
        · have hxm : x m = - ∑ r : Fin m,
              x r.val * A ⟨i.val + r.val, by omega⟩ ⟨i.val + m, hmn⟩ := by
            simp only [x, hmn, ↓reduceDIte]
            rw [inv_step_eq_of_unitUpper hA i hm hmn]
            congr 1
            refine Finset.sum_congr rfl fun r _ => ?_
            have hri : i.val + r.val < n := by omega
            simp only [hri, ↓reduceDIte]
          have hPm : P m = ∑ r : Fin m, max (x r.val) 0 :=
            (Fin.sum_univ_eq_sum_range (fun r => max (x r) 0) m).symm
          have hNm : N m = ∑ r : Fin m, max (-(x r.val)) 0 :=
            (Fin.sum_univ_eq_sum_range (fun r => max (-(x r)) 0) m).symm
          constructor
          · rw [hxm, hPm, neg_le_neg_iff]
            refine Finset.sum_le_sum fun r _ => ?_
            rcases hA.1 ⟨i.val + r.val, by omega⟩ ⟨i.val + m, hmn⟩ with h0 | h1
            · rw [h0, mul_zero]; exact le_max_right _ _
            · rw [h1, mul_one]; exact le_max_left _ _
          · rw [hxm, hNm, ← Finset.sum_neg_distrib]
            refine Finset.sum_le_sum fun r _ => ?_
            rcases hA.1 ⟨i.val + r.val, by omega⟩ ⟨i.val + m, hmn⟩ with h0 | h1
            · rw [h0, mul_zero, neg_zero]; exact le_max_right _ _
            · rw [h1, mul_one]; exact le_max_left _ _
        · have hxm : x m = 0 := by simp [x, hmn]
          have hPnn : 0 ≤ P m := Finset.sum_nonneg fun _ _ => le_max_right _ _
          have hNnn : 0 ≤ N m := Finset.sum_nonneg fun _ _ => le_max_right _ _
          rw [hxm]
          exact ⟨by linarith, hNnn⟩
      have hinv : ∀ m, 1 ≤ m →
          (P m ≤ (Nat.fib m : ℝ) ∧ N m ≤ (Nat.fib (m - 1) : ℝ)) ∨
          (N m ≤ (Nat.fib m : ℝ) ∧ P m ≤ (Nat.fib (m - 1) : ℝ)) := by
        intro m hm
        induction m with
        | zero => omega
        | succ k ih =>
          by_cases hk : k = 0
          · subst hk
            left
            simp [P, N, hx0]
          · have hk1 : 1 ≤ k := by omega
            have hih := ih hk1
            have hfib_step : (Nat.fib (k + 1) : ℝ) = (Nat.fib k : ℝ) + (Nat.fib (k - 1) : ℝ) := by
              have hnat : Nat.fib (k + 1) = Nat.fib (k - 1) + Nat.fib k := by
                have hk_eq : k + 1 = (k - 1) + 2 := by omega
                rw [hk_eq, Nat.fib_add_two]
                have hk_eq2 : k - 1 + 1 = k := by omega
                rw [hk_eq2]
              exact_mod_cast (by omega : Nat.fib (k + 1) = Nat.fib k + Nat.fib (k - 1))
            have hfib_mono : (Nat.fib (k - 1) : ℝ) ≤ (Nat.fib k : ℝ) := by
              exact_mod_cast Nat.fib_mono (by omega : k - 1 ≤ k)
            have hPk : P (k + 1) = P k + max (x k) 0 := Finset.sum_range_succ _ k
            have hNk : N (k + 1) = N k + max (-(x k)) 0 := Finset.sum_range_succ _ k
            have ⟨hlo, hhi⟩ := hbound k hk1
            have hsub : k + 1 - 1 = k := by omega
            rw [hsub]
            rcases le_total 0 (x k) with hxpos | hxneg
            · left
              rw [hPk, hNk, max_eq_left hxpos, max_eq_right (by linarith : -(x k) ≤ 0), add_zero]
              rcases hih with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
            · right
              rw [hPk, hNk, max_eq_right hxneg, max_eq_left (by linarith : 0 ≤ -(x k)), add_zero]
              rcases hih with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
      let m := j.val - i.val
      have hm1 : 1 ≤ m := by
        have : i.val < j.val := hlt
        omega
      have hmn : i.val + m < n := by
        have : i.val < j.val := hlt
        omega
      have hxm_eq : x m = A⁻¹ i j := by
        simp only [x, hmn, ↓reduceDIte]
        exact congrArg (A⁻¹ i) (Fin.ext (by dsimp; have : i.val < j.val := hlt; omega))
      have ⟨hlo, hhi⟩ := hbound m hm1
      have hfib_mono : (Nat.fib (m - 1) : ℝ) ≤ (Nat.fib m : ℝ) := by
        exact_mod_cast Nat.fib_mono (by omega : m - 1 ≤ m)
      rw [← hxm_eq, abs_le]
      rcases hinv m hm1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
    · have hgt : j < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij)
      simp [fibEnvelope, hij, hlt, inv_lower_zero_of_unitUpper hA i j hgt]

private lemma unitUpper_extreme (n : ℕ) : unitUpper (extreme n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    unfold extreme
    split_ifs <;> simp
  · intro i
    simp [extreme]
  · intro i j hji
    have hne : i ≠ j := ne_of_gt hji
    have hnlt : ¬ i < j := not_lt.mpr (le_of_lt hji)
    simp [extreme, hne, hnlt]

private lemma sum_fib_odd_diff : ∀ d : ℕ, 1 ≤ d →
    ∑ r ∈ Finset.range d,
      (if (d - r) % 2 = 1 then (if r = 0 then (1 : ℕ) else Nat.fib r) else 0) = Nat.fib d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    match d with
    | 0 => omega
    | 1 => simp
    | 2 => simp [Finset.sum_range_succ]
    | k + 3 =>
      have hk1 : 1 ≤ k + 1 := by omega
      have hrec := ih (k + 1) (by omega) hk1
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have h1 : (k + 3 - (k + 2)) % 2 = 1 := by omega
      have h2 : (k + 3 - (k + 1)) % 2 = 0 := by omega
      have hne : k + 2 ≠ 0 := by omega
      simp only [h1, ↓reduceIte, hne, h2, Nat.zero_ne_one, add_zero]
      have hcongr :
          ∑ r ∈ Finset.range (k + 1),
            (if (k + 3 - r) % 2 = 1 then (if r = 0 then (1 : ℕ) else Nat.fib r) else 0) =
          ∑ r ∈ Finset.range (k + 1),
            (if (k + 1 - r) % 2 = 1 then (if r = 0 then (1 : ℕ) else Nat.fib r) else 0) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        have hlt : r < k + 1 := Finset.mem_range.mp hr
        have hmod : (k + 3 - r) % 2 = (k + 1 - r) % 2 := by omega
        rw [hmod]
      rw [hcongr, hrec]
      exact (Nat.fib_add_two (n := k + 1)).symm

private lemma inv_extreme_eq (n : ℕ) :
    (extreme n)⁻¹ = signs n * fibEnvelope n * signs n := by
  refine Matrix.inv_eq_left_inv ?_
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hentry : ∀ k : Fin n,
      (signs n * fibEnvelope n * signs n) i k =
        (-1 : ℝ) ^ i.val * fibEnvelope n i k * (-1 : ℝ) ^ k.val := by
    intro k
    simp [signs, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp_rw [hentry]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp only [fibEnvelope, extreme, ↓reduceIte, true_or, mul_one]
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with hlt | hgt
      · have hne : i ≠ k := ne_of_gt hlt
        have hnlt : ¬ i < k := not_lt.mpr (le_of_lt hlt)
        simp [fibEnvelope, hne, hnlt]
      · have hne : k ≠ i := ne_of_gt hgt
        have hnlt : ¬ k < i := not_lt.mpr (le_of_lt hgt)
        simp [extreme, hne, hnlt]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_neg hij]
    by_cases hlt : i < j
    · let d := j.val - i.val
      have hd1 : 1 ≤ d := by
        have : i.val < j.val := hlt
        omega
      have hsplit :
          ∑ k : Fin n,
            (-1 : ℝ) ^ i.val * fibEnvelope n i k * (-1 : ℝ) ^ k.val * extreme n k j =
          ∑ k ∈ Finset.univ.filter (fun k : Fin n => i ≤ k ∧ k ≤ j),
            (-1 : ℝ) ^ i.val * fibEnvelope n i k * (-1 : ℝ) ^ k.val * extreme n k j := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) fun k _ hnot => ?_).symm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_le] at hnot
        rcases hnot with hki | hjk
        · have hne : i ≠ k := ne_of_gt hki
          have hnlt : ¬ i < k := not_lt.mpr (le_of_lt hki)
          simp [fibEnvelope, hne, hnlt]
        · have hne : k ≠ j := ne_of_gt hjk
          have hnlt : ¬ k < j := not_lt.mpr (le_of_lt hjk)
          simp [extreme, hne, hnlt]
      rw [hsplit]
      have hreindex :
          ∑ k ∈ Finset.univ.filter (fun k : Fin n => i ≤ k ∧ k ≤ j),
            (-1 : ℝ) ^ i.val * fibEnvelope n i k * (-1 : ℝ) ^ k.val * extreme n k j =
          ∑ r ∈ Finset.range (d + 1),
            (-1 : ℝ) ^ r * (if r = 0 then (1 : ℝ) else (Nat.fib r : ℝ)) *
              (if r = d ∨ (r < d ∧ (d - r) % 2 = 1) then (1 : ℝ) else 0) := by
        refine Finset.sum_nbij (fun k => k.val - i.val) ?_ ?_ ?_ ?_
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          simp only [Finset.mem_range]
          have h1 : i.val ≤ k.val := hk.1
          have h2 : k.val ≤ j.val := hk.2
          omega
        · intro k₁ hk₁ k₂ hk₂ heq
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hk₁ hk₂
          dsimp only at heq
          have h1 : i.val ≤ k₁.val := hk₁.1
          have h2 : i.val ≤ k₂.val := hk₂.1
          apply Fin.ext
          omega
        · intro r hr
          simp only [Finset.mem_coe, Finset.mem_range] at hr
          refine ⟨⟨i.val + r, by omega⟩, ?_, by simp⟩
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨show i.val ≤ i.val + r by omega, show i.val + r ≤ j.val by omega⟩
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          have h1 : i.val ≤ k.val := hk.1
          have h2 : k.val ≤ j.val := hk.2
          have hpow : (-1 : ℝ) ^ i.val * (-1 : ℝ) ^ k.val = (-1 : ℝ) ^ (k.val - i.val) := by
            rw [← pow_add]
            have hadd : i.val + k.val = 2 * i.val + (k.val - i.val) := by omega
            rw [hadd, pow_add, pow_mul]
            norm_num
          have hfib_eq : fibEnvelope n i k =
              if k.val - i.val = 0 then (1 : ℝ) else (Nat.fib (k.val - i.val) : ℝ) := by
            unfold fibEnvelope
            by_cases hik : i = k
            · subst hik; simp
            · have hiklt : i < k := lt_of_le_of_ne hk.1 hik
              have hne0 : k.val - i.val ≠ 0 := by
                have : i.val < k.val := hiklt
                omega
              simp [hik, hiklt, hne0]
          have hext_eq : extreme n k j =
              if k.val - i.val = d ∨ (k.val - i.val < d ∧ (d - (k.val - i.val)) % 2 = 1)
              then (1 : ℝ) else 0 := by
            unfold extreme
            congr 1
            refine propext ⟨?_, ?_⟩
            · rintro (rfl | ⟨hkj, hmod⟩)
              · left; rfl
              · right
                have : k.val < j.val := hkj
                exact ⟨by omega, by rwa [show d - (k.val - i.val) = j.val - k.val by omega]⟩
            · rintro (heq | ⟨hlt', hmod⟩)
              · left; apply Fin.ext; omega
              · right
                refine ⟨show k.val < j.val by omega, ?_⟩
                rwa [show j.val - k.val = d - (k.val - i.val) by omega]
          rw [hfib_eq, hext_eq]
          calc
            (-1 : ℝ) ^ i.val * (if k.val - i.val = 0 then 1 else ↑(Nat.fib (k.val - i.val))) *
                (-1 : ℝ) ^ k.val *
                (if k.val - i.val = d ∨ k.val - i.val < d ∧ (d - (k.val - i.val)) % 2 = 1 then 1 else 0)
              = ((-1 : ℝ) ^ i.val * (-1 : ℝ) ^ k.val) *
                (if k.val - i.val = 0 then 1 else ↑(Nat.fib (k.val - i.val))) *
                (if k.val - i.val = d ∨ k.val - i.val < d ∧ (d - (k.val - i.val)) % 2 = 1 then 1 else 0) := by
                  ring
            _ = _ := by rw [hpow]
      rw [hreindex, Finset.sum_range_succ]
      have hd0 : d ≠ 0 := by omega
      simp only [hd0, ↓reduceIte, true_or, mul_one]
      have hprev :
          ∑ r ∈ Finset.range d,
            (-1 : ℝ) ^ r * (if r = 0 then (1 : ℝ) else (Nat.fib r : ℝ)) *
              (if r = d ∨ (r < d ∧ (d - r) % 2 = 1) then (1 : ℝ) else 0) =
          - ((-1 : ℝ) ^ d * (Nat.fib d : ℝ)) := by
        have hnat := sum_fib_odd_diff d hd1
        have hcast :
            (∑ r ∈ Finset.range d,
              (if (d - r) % 2 = 1 then (if r = 0 then (1 : ℝ) else (Nat.fib r : ℝ)) else 0)) =
            (Nat.fib d : ℝ) := by
          rw [← hnat]
          push_cast
          refine Finset.sum_congr rfl fun r _ => ?_
          split_ifs <;> simp
        rw [← hcast, ← neg_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r hr => ?_
        have hrd : r < d := Finset.mem_range.mp hr
        have hne : r ≠ d := ne_of_lt hrd
        by_cases hodd : (d - r) % 2 = 1
        · simp only [hne, false_or, hrd, true_and, hodd, ↓reduceIte, mul_one]
          have hsign : (-1 : ℝ) ^ r = - (-1 : ℝ) ^ d := by
            have hdeq : d = r + (d - r) := by omega
            have hpow_odd : (-1 : ℝ) ^ (d - r) = -1 := by
              rw [show d - r = 2 * ((d - r) / 2) + 1 by omega, pow_add, pow_mul]
              norm_num
            rw [hdeq, pow_add, hpow_odd]
            ring
          rw [hsign]
        · simp [hne, hrd, hodd]
      rw [hprev]
      ring
    · have hgt : j < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij)
      refine Finset.sum_eq_zero fun k _ => ?_
      rcases lt_or_ge k i with hki | hik
      · have hne : i ≠ k := ne_of_gt hki
        have hnlt : ¬ i < k := not_lt.mpr (le_of_lt hki)
        simp [fibEnvelope, hne, hnlt]
      · have hjk : j < k := lt_of_lt_of_le hgt hik
        have hne : k ≠ j := ne_of_gt hjk
        have hnlt : ¬ k < j := not_lt.mpr (le_of_lt hjk)
        simp [extreme, hne, hnlt]

private lemma signs_mul_signs (n : ℕ) : signs n * signs n = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [signs, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  · simp [signs, hij]

private lemma norm_signs_le_one (n : ℕ) : ‖signs n‖ ≤ 1 := by
  rw [signs, Matrix.l2_opNorm_diagonal]
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  simp

private lemma norm_inv_extreme_eq_norm_fib (n : ℕ) :
    ‖(extreme n)⁻¹‖ = ‖fibEnvelope n‖ := by
  have heq := inv_extreme_eq n
  have hS := norm_signs_le_one n
  have h1 : ‖(extreme n)⁻¹‖ ≤ ‖fibEnvelope n‖ := by
    rw [heq]
    calc
      ‖signs n * fibEnvelope n * signs n‖ ≤ ‖signs n * fibEnvelope n‖ * ‖signs n‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ (‖signs n‖ * ‖fibEnvelope n‖) * ‖signs n‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ (1 * ‖fibEnvelope n‖) * 1 := by
        have hA : ‖signs n‖ * ‖fibEnvelope n‖ ≤ 1 * ‖fibEnvelope n‖ :=
          mul_le_mul_of_nonneg_right hS (norm_nonneg _)
        exact mul_le_mul hA hS (norm_nonneg _) (by positivity)
      _ = ‖fibEnvelope n‖ := by ring
  have h2 : ‖fibEnvelope n‖ ≤ ‖(extreme n)⁻¹‖ := by
    have hfib : fibEnvelope n = signs n * (extreme n)⁻¹ * signs n := by
      rw [heq]
      calc
        fibEnvelope n = 1 * fibEnvelope n * 1 := by simp
        _ = (signs n * signs n) * fibEnvelope n * (signs n * signs n) := by
          rw [signs_mul_signs]
        _ = signs n * (signs n * fibEnvelope n * signs n) * signs n := by
          simp only [Matrix.mul_assoc]
    rw [hfib]
    calc
      ‖signs n * (extreme n)⁻¹ * signs n‖ ≤ ‖signs n * (extreme n)⁻¹‖ * ‖signs n‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ (‖signs n‖ * ‖(extreme n)⁻¹‖) * ‖signs n‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ (1 * ‖(extreme n)⁻¹‖) * 1 := by
        have hA : ‖signs n‖ * ‖(extreme n)⁻¹‖ ≤ 1 * ‖(extreme n)⁻¹‖ :=
          mul_le_mul_of_nonneg_right hS (norm_nonneg _)
        exact mul_le_mul hA hS (norm_nonneg _) (by positivity)
      _ = ‖(extreme n)⁻¹‖ := by ring
  exact le_antisymm h1 h2

private lemma l2_opNorm_le_of_abs_le {n : ℕ} {M N : Mat n} (h : ∀ i j, |M i j| ≤ N i j) :
    ‖M‖ ≤ ‖N‖ := by
  rw [Matrix.cstar_norm_def M]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg N) fun x => ?_
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun j => |x.ofLp j|)
  have hy_norm : ‖y‖ = ‖x‖ := by
    refine (sq_eq_sq₀ (norm_nonneg y) (norm_nonneg x)).mp ?_
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, abs_abs, y]
  have hMx_le : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M x‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) N y‖ := by
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    simp only [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM, Real.norm_eq_abs]
    refine Finset.sum_le_sum fun i _ => ?_
    have hrow : |(M *ᵥ x.ofLp) i| ≤ (N *ᵥ y.ofLp) i := by
      simp only [Matrix.mulVec, dotProduct, y]
      calc
        |∑ j : Fin n, M i j * x.ofLp j| ≤ ∑ j : Fin n, |M i j * x.ofLp j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin n, |M i j| * |x.ofLp j| := by simp_rw [abs_mul]
        _ ≤ ∑ j : Fin n, N i j * |x.ofLp j| :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (h i j) (abs_nonneg _)
    have hrow_nn : 0 ≤ (N *ᵥ y.ofLp) i := le_trans (abs_nonneg _) hrow
    rw [abs_of_nonneg hrow_nn]
    exact pow_le_pow_left₀ (abs_nonneg _) hrow 2
  calc
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M x‖
      ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) N y‖ := hMx_le
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) N‖ * ‖y‖ :=
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) N).le_opNorm y
    _ = ‖N‖ * ‖x‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM, hy_norm]

private lemma part3 (n : ℕ) :
    unitUpper (extreme n) ∧ ‖(extreme n)⁻¹‖ = ‖fibEnvelope n‖ ∧
      ∀ (A : Mat n), unitUpper A → ‖A⁻¹‖ ≤ ‖(extreme n)⁻¹‖ := by
  refine ⟨unitUpper_extreme n, norm_inv_extreme_eq_norm_fib n, fun A hA => ?_⟩
  rw [norm_inv_extreme_eq_norm_fib n]
  exact l2_opNorm_le_of_abs_le (part2 A hA)

private lemma sv_last_mul_norm_inv {n : ℕ} (hn : 0 < n) (A : Mat n) (hA : A.det ≠ 0) :
    0 < sv A (n - 1) ∧ ‖A⁻¹‖ = (sv A (n - 1))⁻¹ := by
  set T := A.toEuclideanLin
  set S := T.adjoint ∘ₗ T
  have hS : S.IsSymmetric := T.isSymmetric_adjoint_comp_self
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  let b := hS.eigenvectorBasis hdim
  let last : Fin n := ⟨n - 1, by omega⟩
  have hpos_all : ∀ k : Fin n, 0 < sv A k.val := by
    have hprod : ∏ k : Fin n, (sv A k.val) ^ 2 = A.det ^ 2 := prod_sq_sv A
    have hne0 : ∏ k : Fin n, (sv A k.val) ^ 2 ≠ 0 := by
      rw [hprod]
      exact pow_ne_zero 2 hA
    intro k
    have hk_ne : (sv A k.val) ^ 2 ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hne0) k (Finset.mem_univ k)
    have hsv_ne : sv A k.val ≠ 0 := fun h0 => hk_ne (by simp [h0])
    exact lt_of_le_of_ne (T.singularValues_nonneg k.val) (Ne.symm hsv_ne)
  have hlast_pos : 0 < sv A (n - 1) := hpos_all last
  have hAAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA)
  have hAinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)
  have hnorm_sq : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖T x‖ ^ 2 = ∑ k : Fin n, (sv A k.val) ^ 2 * (b.repr x k) ^ 2 := by
    intro x
    have h1 : ‖T x‖ ^ 2 = ⟪x, S x⟫ := by
      rw [← real_inner_self_eq_norm_sq (T x)]
      simp [S, LinearMap.adjoint_inner_right]
    have h2 : ⟪x, S x⟫ = ⟪b.repr x, b.repr (S x)⟫ := (b.repr.inner_map_map x (S x)).symm
    rw [h1, h2, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [RCLike.inner_apply, conj_trivial, b, sv]
    rw [hS.eigenvectorBasis_apply_self_apply hdim x k, ← T.sq_singularValues_fin hdim k]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    ring
  have hlower : ∀ x : EuclideanSpace ℝ (Fin n), sv A (n - 1) * ‖x‖ ≤ ‖T x‖ := by
    intro x
    refine (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp ?_
    rw [mul_pow, hnorm_sq x]
    have hxnorm : ‖x‖ ^ 2 = ∑ k : Fin n, (b.repr x k) ^ 2 := by
      rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs]
    rw [hxnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have hk_le : k.val ≤ n - 1 := by omega
    have hsv_le : sv A (n - 1) ≤ sv A k.val := T.singularValues_antitone hk_le
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_of_lt hlast_pos) hsv_le 2) (sq_nonneg _)
  have hle : ‖A⁻¹‖ ≤ (sv A (n - 1))⁻¹ := by
    rw [Matrix.cstar_norm_def A⁻¹]
    refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (le_of_lt hlast_pos)) fun y => ?_
    let x := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ y
    have hTx : T x = y := by
      have hcomp : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ y) =
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A *
            Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹) y := rfl
      change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ y) = y
      rw [hcomp, ← map_mul, hAAinv, map_one]
      rfl
    have h1 := hlower x
    rw [hTx] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (le_of_lt hlast_pos))
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hlast_pos), one_mul] at h2
    exact h2
  have hge : (sv A (n - 1))⁻¹ ≤ ‖A⁻¹‖ := by
    let v := b last
    have hv_norm : ‖v‖ = 1 := b.orthonormal.1 last
    have hTv_norm : ‖T v‖ = sv A (n - 1) := by
      refine (sq_eq_sq₀ (norm_nonneg _) (le_of_lt hlast_pos)).mp ?_
      have h1 : ‖T v‖ ^ 2 = ⟪v, S v⟫ := by
        rw [← real_inner_self_eq_norm_sq (T v)]
        simp [S, LinearMap.adjoint_inner_right]
      rw [h1, hS.apply_eigenvectorBasis hdim last, inner_smul_right,
        real_inner_self_eq_norm_sq, hv_norm, one_pow, mul_one]
      exact (T.sq_singularValues_fin hdim last).symm
    have hAinvTv : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ (T v) = v := by
      have hcomp : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A v) =
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ *
            Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) v := rfl
      change Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A v) = v
      rw [hcomp, ← map_mul, hAinvA, map_one]
      rfl
    have h1 : ‖v‖ ≤ ‖A⁻¹‖ * ‖T v‖ := by
      calc
        ‖v‖ = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹ (T v)‖ := by rw [hAinvTv]
        _ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹‖ * ‖T v‖ :=
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A⁻¹).le_opNorm (T v)
        _ = ‖A⁻¹‖ * ‖T v‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM]
    rw [hv_norm, hTv_norm] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr (le_of_lt hlast_pos))
    rw [one_mul, mul_assoc, mul_inv_cancel₀ (ne_of_gt hlast_pos), mul_one] at h2
    exact h2
  exact ⟨hlast_pos, le_antisymm hle hge⟩

private lemma part4 (n : ℕ) (hn : 0 < n) (A : Mat n) (hA : unitUpper A) :
    sv (extreme n) (n - 1) ≤ sv A (n - 1) := by
  have hdetA : A.det ≠ 0 := by rw [det_eq_one_of_unitUpper hA]; exact one_ne_zero
  have hdetE : (extreme n).det ≠ 0 := by
    rw [det_eq_one_of_unitUpper (unitUpper_extreme n)]; exact one_ne_zero
  obtain ⟨hposA, hnormA⟩ := sv_last_mul_norm_inv hn A hdetA
  obtain ⟨hposE, hnormE⟩ := sv_last_mul_norm_inv hn (extreme n) hdetE
  have hnorm_le : ‖A⁻¹‖ ≤ ‖(extreme n)⁻¹‖ := (part3 n).2.2 A hA
  rw [hnormA, hnormE] at hnorm_le
  exact (inv_le_inv₀ hposA hposE).mp hnorm_le

end OMA.S_mo_316890.Proof

theorem OMA.solution : type_of% @OMA.S_mo_316890.main := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn A hbin hdet i
    exact OMA.S_mo_316890.Proof.part1 hn A hbin hdet i
  · intro n A hA i j
    exact OMA.S_mo_316890.Proof.part2 A hA i j
  · intro n
    exact OMA.S_mo_316890.Proof.part3 n
  · intro n hn A hA
    exact OMA.S_mo_316890.Proof.part4 n hn A hA

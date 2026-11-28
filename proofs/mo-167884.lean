import OMAStatements.S_mo_167884

/-! Credit: @connoranderson, following fedja's perturbation suggestion. -/

namespace OMA.S_mo_167884
open Matrix Finset
open scoped Matrix.Norms.Operator NNReal

private lemma row_le {n : ℕ} (A : Mat n) (i : Fin n) : (∑ j, |A i j|) ≤ ‖A‖ := by
  convert norm_le_pi_norm (fun j => WithLp.toLp 1 (A j)) i using 1 <;>
    first | rfl | simp [PiLp.norm_eq_of_L1, Real.norm_eq_abs]

private lemma norm_le_rows {n : ℕ} (A : Mat n) (c : ℝ) (hc : 0≤c)
    (h : ∀ i, (∑ j, |A i j|) ≤ c) : ‖A‖ ≤ c := by
  change ‖fun i => WithLp.toLp 1 (A i)‖ ≤ c
  rw [pi_norm_le_iff_of_nonneg hc]
  simpa [PiLp.norm_eq_of_L1, Real.norm_eq_abs] using h

private lemma counter (M : ℝ) : ∃ (A : Mat 3) (b : Fin 3 → ℝ), Admissible A b ∧
      (∃ i, b i=1) ∧ ‖A‖=2 ∧ M < ‖A⁻¹‖ := by
  let t : ℝ := |M|+1
  have ht : 0<t := by dsimp [t]; positivity
  have ht' : 1≤t := by dsimp [t]; linarith [abs_nonneg M]
  have hq : 0≤1/t := by positivity
  have hq' : 1/t≤1 := (div_le_one ht).mpr ht'
  let A : Mat 3 := !![1,-1,0; 1/t-1,1,-(1/t); 0,0,1]
  let B : Mat 3 := !![t,t,1; t-1,t,1; 0,0,1]
  let b : Fin 3 → ℝ := ![0,0,1]
  have hAB : A*B = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A,B, Matrix.mul_apply,Fin.sum_univ_succ]
      <;> field_simp <;> ring
  have hu := Matrix.isUnit_det_of_right_inverse hAB
  have hi : A⁻¹ = B := Matrix.inv_eq_right_inv hAB
  have hsmall : t⁻¹-1 ≤ 0 := by simpa using sub_nonpos.mpr hq'
  have ha : |t|=t := abs_of_pos ht
  have hn02 : (0 : Fin 3) ≠ 2 := by decide
  have hn12 : (1 : Fin 3) ≠ 2 := by decide
  have hoff : ∀ i, off A i = (if i=2 then 0 else 1) := by
    intro i
    fin_cases i <;> norm_num [off,A,Fin.sum_univ_succ,abs_of_nonpos (sub_nonpos.mpr hq'),
      abs_of_nonneg hq,abs_of_nonpos hsmall,ha,hn02,hn12]
  refine ⟨A,b,⟨?_,?_,?_,⟨0,by simp [hoff]⟩,⟨2,by simp [hoff]⟩,?_,?_,hu⟩,⟨2,rfl⟩,?_,?_⟩
  · intro i; fin_cases i <;> rfl
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [A] at * <;> constructor <;> linarith
  · intro i; rw [hoff]; split <;> simp
  · intro i; fin_cases i <;> simp [b]
  · intro i; fin_cases i <;> norm_num [hoff,b]
    decide
  · apply le_antisymm
    · apply norm_le_rows A 2 (by norm_num)
      intro i
      fin_cases i <;> norm_num [A,Fin.sum_univ_succ,abs_of_nonpos (sub_nonpos.mpr hq'),
        abs_of_nonneg hq,abs_of_nonpos hsmall,ha,hn02,hn12]
    · have := row_le A 0
      norm_num [A,Fin.sum_univ_succ] at this ⊢; exact this
  · rw [hi]
    have h := row_le B 0
    simp [B,Fin.sum_univ_succ,abs_of_pos ht] at h
    linarith [le_abs_self M,show t=|M|+1 from rfl]

private lemma norm_one_sub {n : ℕ} (A : Mat n) (b : Fin n → ℝ) (h : Admissible A b) :
    ‖1-A‖≤1 := by
  obtain ⟨hd,_,ho,_⟩ := h
  let P : Mat n := 1-A

  apply norm_le_rows _ _ zero_le_one
  intro j
  have he : (∑ l, |P j l|)=off A j := by
    simp +contextual [P, off, Matrix.one_apply, ite_sub, apply_ite, hd]
  rw [he]
  rcases ho j with h0|h1 <;> linarith

private lemma geom_inv {n : ℕ} (A : Mat n) (hu : IsUnit A.det) (k : ℕ) :
    (∑ j ∈ range k, (1-A)^j) = (1-(1-A)^k)*A⁻¹ := by
  have ht := geom_sum_mul_neg (1-A) k
  rw [show (1:Mat n) - (1-A) = A by abel] at ht
  simpa only [Matrix.mul_assoc,Matrix.mul_nonsing_inv A hu,mul_one] using
    congrArg (fun U : Mat n => U*A⁻¹) ht

private lemma eventually_contracts {n : ℕ} (A : Mat n) (b : Fin n → ℝ) (h : Admissible A b) :
    ∃ k : ℕ, ‖(1-A)^k‖ < 1 := by
  let P : Mat n := 1-A
  have hp : ‖P‖ ≤ 1 := norm_one_sub A b h
  obtain ⟨hd,hn,_,⟨i,_⟩,_,_,_,hu⟩ := h
  let : Nonempty (Fin n) := ⟨i⟩
  have hP : ∀ u v, 0 ≤ P u v := by
    intro u v
    by_cases he : u=v
    · subst v; simp [P,hd]
    · simpa [P,Matrix.one_apply,he] using (hn u v he).2
  have hpow := Matrix.pow_apply_nonneg hP
  obtain ⟨k,hk⟩ := exists_nat_gt ((n:ℝ)*(2*‖A⁻¹‖))
  let S : Mat n := ∑ j ∈ range k, P^j
  have hbound : ‖S‖ ≤ 2*‖A⁻¹‖ := calc
    ‖S‖ = ‖(1-P^k)*A⁻¹‖ := congrArg norm (geom_inv A hu k)
    _ ≤ ‖1-P^k‖*‖A⁻¹‖ := norm_mul_le _ _
    _ ≤ 2*‖A⁻¹‖ := by
      have hpk := (norm_pow_le P k).trans (pow_le_one₀ (norm_nonneg _) hp)
      have ht := norm_sub_le (1:Mat n) (P^k)
      rw [norm_one] at ht
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  by_contra! hf
  have ht (j : ℕ) : 1 ≤ ∑ u, ∑ v, (P^j) u v := by
    apply (hf j).trans
    apply norm_le_rows (P^j)
    · exact sum_nonneg fun u _ => sum_nonneg fun v _ => hpow j u v
    · intro u
      change (∑ v, |(P^j) u v|) ≤ _
      simp_rw [abs_of_nonneg (hpow j u _)]
      exact single_le_sum (fun w _ => sum_nonneg fun v _ => hpow j w v) (mem_univ u)
  have hk' := calc
    (k:ℝ) = ∑ _j ∈ range k, (1:ℝ) := by simp
    _ ≤ ∑ j ∈ range k, ∑ u, ∑ v, (P^j) u v := sum_le_sum fun j _ => ht j
    _ = ∑ u, ∑ v, S u v := by
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
      simp [S,Matrix.sum_apply]
    _ ≤ ∑ _u : Fin n, (2*‖A⁻¹‖) := by
      apply sum_le_sum
      intro u _
      exact (sum_le_sum fun v _ => le_abs_self (S u v)).trans ((row_le S u).trans hbound)
    _ = (n:ℝ)*(2*‖A⁻¹‖) := by simp
  linarith

private lemma bound {n : ℕ} (A : Mat n) (b : Fin n → ℝ) (h : Admissible A b) (k : ℕ)
    (hk : ‖((1-A)^k)‖ < 1) : ‖A⁻¹‖ ≤ k/(1-‖((1-A)^k)‖) := by
  let P : Mat n := 1-A
  have hp : ‖P‖ ≤ 1 := norm_one_sub A b h
  obtain ⟨_,_,_,⟨i,_⟩,_,_,_,hu⟩ := h
  let : Nonempty (Fin n) := ⟨i⟩
  let S : Mat n := ∑ j ∈ range k, P^j
  have hS : ‖S‖ ≤ (k:ℝ) := calc
    ‖S‖ ≤ ∑ j ∈ range k, ‖P^j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range k, (1:ℝ) := Finset.sum_le_sum fun j _ =>
      (norm_pow_le _ _).trans ((pow_le_one₀ (norm_nonneg _) hp))
    _ = _ := by simp
  have he : A⁻¹ = S+P^k*A⁻¹ := by
    have heq : S = (1-P^k)*A⁻¹ := geom_inv A hu k
    rw [sub_mul,one_mul] at heq
    exact (eq_sub_iff_add_eq.mp heq).symm
  apply (le_div_iff₀ (by linarith : 0<1-‖((1-A)^k)‖)).mpr
  have hh := calc
    ‖A⁻¹‖ = ‖S+P^k*A⁻¹‖ := congrArg norm he
    _ ≤ ‖S‖+‖P^k*A⁻¹‖ := norm_add_le _ _
    _ ≤ k+‖P^k‖*‖A⁻¹‖ := add_le_add hS (norm_mul_le _ _)
  change ‖A⁻¹‖*(1-‖P^k‖) ≤ k
  linarith

end OMA.S_mo_167884
theorem OMA.solution : type_of% @OMA.S_mo_167884.main :=
  ⟨OMA.S_mo_167884.counter, fun _ A b h => ⟨OMA.S_mo_167884.eventually_contracts A b h,OMA.S_mo_167884.bound A b h⟩⟩

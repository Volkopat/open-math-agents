import OMAStatements.S_oeis_a066933

open Polynomial Matrix OMA.S_oeis_a066933

private theorem coeff_f (n k : ℕ) :
    (f n).coeff k = if 1 ≤ k ∧ k ≤ n then (Nat.nth Nat.Prime (k-1) : ℤ) else 0 := by
  simp [f, finsetSum_coeff]

private theorem degree_f {n : ℕ} (hn : 0 < n) : (f n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_le_iff_coeff_eq_zero.mpr fun k hk => by simp [coeff_f, Nat.not_le.mpr hk]
  · simpa [coeff_f, show 1 ≤ n by omega] using (Nat.prime_nth_prime (n-1)).ne_zero

private def band (p : ℤ[X]) (n i j : ℕ) : ℤ :=
  if j ≤ i ∧ i ≤ j+n then p.coeff (i-j) else 0

private theorem block_form (n : ℕ) (hn : 0 < n) (p : ℤ[X]) :
    ((sylvester p (X^n-1) n n).submatrix finSumFinEquiv finSumFinEquiv) =
      Matrix.fromBlocks (-1)
        (Matrix.of fun i j : Fin n => band p n i j)
        1 (Matrix.of fun i j : Fin n => band p n (n+i) j) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp only [Matrix.submatrix_apply, finSumFinEquiv, Equiv.coe_fn_mk, Sum.elim_inl,
    Sum.elim_inr, sylvester, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right,
    Fin.val_castAdd, Fin.val_natAdd, Set.mem_Icc, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  · simp only [coeff_sub, coeff_X_pow, coeff_one, Matrix.neg_apply, Matrix.one_apply,
      Fin.ext_iff]
    split_ifs <;> (first | rfl | omega)
  · rfl
  · simp only [coeff_sub, coeff_X_pow, coeff_one, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> (first | rfl | omega)
  · rfl

private theorem wrap (n : ℕ) (i j : Fin n) :
    band (f n) n (n+i) j.rev + band (f n) n i j.rev =
      (Nat.nth Nat.Prime ((i.val+j.val)%n) : ℤ) := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [band, coeff_f, Fin.val_rev]
  by_cases h : i.val + j.val < n
  · rw [Nat.mod_eq_of_lt h]
    split_ifs <;> first | omega | simp only [add_zero, zero_add]; congr 2 <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> first | omega | simp only [add_zero, zero_add]; congr 2 <;> omega

private theorem block_det (n : ℕ) (B D : Matrix (Fin n) (Fin n) ℤ) :
    (Matrix.fromBlocks (-1) B 1 D).det = (-1)^n * (D+B).det := by
  letI : Invertible (1 : Matrix (Fin n) (Fin n) ℤ) := invertibleOne
  letI : Invertible (-1 : Matrix (Fin n) (Fin n) ℤ) := invertibleNeg 1
  rw [Matrix.det_fromBlocks₁₁]
  simp [Matrix.det_neg]

open Equiv

private theorem sign_rev (n : ℕ) : Perm.sign (@Fin.revPerm n) = (-1)^(n/2) := by
  classical
  rw [Perm.sign_of_pow_two_eq_one (show (@Fin.revPerm n)^2 = 1 by
    apply Equiv.ext; intro i; exact Fin.rev_rev i), Fintype.card_fin]
  congr 1
  let F := Function.fixedPoints (@Fin.revPerm n)
  have hf (i : F) : n - (i.val.val + 1) = i.val.val := congrArg Fin.val i.property
  by_cases hn : n % 2 = 0
  · haveI : IsEmpty F := ⟨fun i => by have := hf i; have := i.val.isLt; omega⟩
    change (n - Fintype.card F) / 2 = _
    simp
  · haveI : Subsingleton F := ⟨fun i j => by
      apply Subtype.ext; apply Fin.ext
      have := hf i; have := hf j; have := i.val.isLt; have := j.val.isLt; omega⟩
    have hcard : Fintype.card F ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    change (n - Fintype.card F) / 2 = _
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a066933.main := by
  classical
  intro n
  by_cases hz : n = 0
  · subst n
    have hf : f 0 = 0 := by simp [f]
    have hg : (X : ℤ[X]) ^ 0 - 1 = 0 := by simp
    have hr : Polynomial.resultant (f 0) ((X : ℤ[X]) ^ 0 - 1) = 1 := by
      unfold Polynomial.resultant
      rw [hf, hg, natDegree_zero]
      letI : IsEmpty (Fin (0 + 0)) := (inferInstance : IsEmpty (Fin 0))
      exact Matrix.det_isEmpty
    rw [hr]
    simp [a]
  have hn : 0 < n := Nat.pos_of_ne_zero hz
  let B := Matrix.of fun i j : Fin n => band (f n) n i j
  let D := Matrix.of fun i j : Fin n => band (f n) n (n+i) j
  have hdegree : ((X : ℤ[X]) ^ n - 1).natDegree = n := by
    simpa only [map_one] using (Polynomial.natDegree_X_pow_sub_C (n := n) (r := (1 : ℤ)))
  have hres : Polynomial.resultant (f n) (X ^ n - 1) = (-1)^n * (D+B).det := by
    rw [Polynomial.resultant, degree_f hn, hdegree, ← Matrix.det_submatrix_equiv_self finSumFinEquiv,
      block_form n hn]
    exact block_det n B D
  have hmat : (Matrix.of fun i j : Fin n => (Nat.nth Nat.Prime ((i.val+j.val)%n) : ℤ)) =
      (D+B).submatrix id Fin.revPerm := by
    ext i j
    exact (wrap n i j).symm
  rw [a, hmat, Matrix.det_permute', sign_rev, hres, pow_add]
  push_cast
  have hunit : (-1 : ℤ)^n * (-1)^n = 1 := by rw [← mul_pow]; simp
  calc
    _ = ((-1 : ℤ)^n * (-1)^n) * ((-1)^(n/2) * (D+B).det) := by rw [hunit, one_mul]
    _ = _ := by ring

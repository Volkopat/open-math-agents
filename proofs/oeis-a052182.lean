import OMAStatements.S_oeis_a052182
import Mathlib

-- Original proof: @oh-meh. Sum reindexing and root-power simplification: @rgoldman73-dev.
open OMA.S_oeis_a052182 Finset Polynomial Matrix

private noncomputable def rowPoly (n : ℕ) : ℤ[X] :=
  ∑ i ∈ range n, C ((i : ℤ)+1) * X^i

private theorem weighted (n : ℕ) : weightedSum n = X * rowPoly n := by
  unfold weightedSum rowPoly
  rw [← Ico_succ_right_eq_Icc, sum_Ico_eq_sum_range]
  simp only [mul_sum]
  apply sum_congr rfl
  intro i _
  push_cast
  ring

private theorem row_degree (n : ℕ) : (rowPoly (n+1)).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · unfold rowPoly
    exact natDegree_sum_le_of_forall_le _ _ (fun i hi =>
      (natDegree_C_mul_X_pow_le ..).trans (Nat.le_of_lt_succ (mem_range.mp hi)))
  · simp only [rowPoly, finsetSum_coeff, coeff_C_mul_X_pow]
    simp
    omega

private theorem root_add {n : ℕ} [NeZero n] {u : ℂ} (hu : u^n=1) (i j : Fin n) :
    u ^ ((i+j).val) = u^i.val * u^j.val := by
  rw [Fin.val_add, ← pow_eq_pow_mod _ hu, pow_add]

private theorem fourier_det {n : ℕ} [NeZero n] {z : ℂ} (hz : IsPrimitiveRoot z n) :
    (circulant (fun i : Fin n => (i.val : ℂ)+1)).det =
      ∏ i : Fin n, eval (z^i.val) ((rowPoly n).map (Int.castRingHom ℂ)) := by
  classical
  let r := fun i : Fin n => z^i.val
  let w := fun i : Fin n => eval (r i) ((rowPoly n).map (Int.castRingHom ℂ))
  let V := vandermonde r
  let A := circulant (fun i : Fin n => (i.val : ℂ)+1)
  have hV : V.det ≠ 0 := det_vandermonde_ne_zero_iff.mpr
    (fun i j h => Fin.ext (hz.pow_inj i.isLt j.isLt h))
  have eig : V * A = diagonal w * V := by
    ext i j
    rw [diagonal_mul, Matrix.mul_apply]
    change (∑ k : Fin n, (r i)^k.val * (((k-j).val : ℂ)+1)) = w i * (r i)^j.val
    have hu : (r i)^n = 1 := by
      dsimp [r]
      rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
    rw [← Equiv.sum_comp (Equiv.addRight j) (fun k : Fin n => (r i)^k.val * (((k-j).val : ℂ)+1))]
    change (∑ k : Fin n, (r i)^(k+j).val * ((((k+j)-j).val : ℂ)+1)) = _
    simp only [add_sub_cancel_right, root_add hu]
    dsimp only [w]
    simp only [rowPoly, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_C, map_X, eval_finsetSum, eval_mul, eval_pow, eval_C, eval_X,
      Int.coe_castRingHom, Int.cast_add, Int.cast_one, Int.cast_natCast,
      ← Fin.sum_univ_eq_sum_range, sum_mul]
    apply sum_congr rfl
    intro k _
    ring
  have h := congrArg Matrix.det eig
  rw [det_mul, det_mul, det_diagonal, mul_comm _ V.det] at h
  exact mul_left_cancel₀ hV h

private theorem root_resultant {n : ℕ} [NeZero n] {z : ℂ} (hz : IsPrimitiveRoot z n)
    (f : ℂ[X]) (d : ℕ) (hd : f.natDegree ≤ d) :
    resultant (X^n - C 1) f n d = ∏ i : Fin n, eval (z^i.val) f := by
  have hm := monic_X_pow_sub_C (1 : ℂ) (NeZero.ne n)
  have he := resultant_eq_prod_eval (X^n - C (1:ℂ)) f d hd (IsAlgClosed.splits _)
  rw [natDegree_X_pow_sub_C, hm.leadingCoeff, one_pow, one_mul, ← nthRoots,
    hz.nthRoots_eq (one_pow n : (1:ℂ)^n=1), Multiset.map_map] at he
  rw [he, Fin.prod_univ_eq_prod_range (fun k => eval (z^k) f)]
  simp [Finset.prod]

theorem OMA.solution : type_of% @OMA.S_oeis_a052182.main := by
  classical
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let f := rowPoly (m+1)
  let g := (X^(m+1)-C 1 : ℤ[X])
  have hdeg : f.natDegree=m := row_degree m
  have hne : f ≠ 0 := fun h => by
    simpa [f, rowPoly, coeff_C_mul_X_pow] using congrArg (fun p : ℤ[X] => p.coeff 0) h
  have hg : g.natDegree=m+1 := natDegree_X_pow_sub_C
  have hx : resultant X g 1 (m+1) = -1 := by
    have h := resultant_X_sub_C_left g (m+1) (0:ℤ) hg.le
    rw [map_zero, sub_zero] at h
    simpa [g] using h
  have heven := (Nat.even_mul_succ_self m).neg_one_pow (α:=ℤ)
  change (circulantMatrix (m+1)).det = -resultant (weightedSum (m+1)) g (weightedSum (m+1)).natDegree g.natDegree
  rw [weighted, show rowPoly (m+1) = f from rfl, natDegree_mul X_ne_zero hne, hg,
    resultant_mul_left _ _ _ _ hg.le, natDegree_X, hx, neg_one_mul, neg_neg, hdeg,
    resultant_comm f g m (m+1), heven, one_mul]
  let φ := Int.castRingHom ℂ
  apply Int.cast_injective (α:=ℂ)
  change φ (circulantMatrix (m+1)).det = φ (resultant g f (m+1) m)
  rw [circulantMatrix, det_transpose, RingHom.map_det, ← resultant_map_map]
  change ((circulant (fun i : Fin (m+1) => (i.val : ℤ)+1)).map φ).det = _
  rw [Matrix.map_circulant]
  have hz := Complex.isPrimitiveRoot_exp (m+1) (Nat.succ_ne_zero _)
  have hmap : g.map φ = X^(m+1)-C 1 := by simp [g]
  rw [hmap, root_resultant hz _ _ (natDegree_map_le.trans hdeg.le)]
  simpa [φ, f, Function.comp_def] using fourier_det hz

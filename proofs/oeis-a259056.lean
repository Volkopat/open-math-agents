import OMAStatements.S_oeis_a259056
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

open OMA.S_oeis_a259056
open Matrix Finset

namespace OMA.S_oeis_a259056.Proof

private def delta (f : ℕ → ℤ) (i : ℕ) : ℤ := if i = 0 then f 0 else f i - f (i - 1)

private def kernel (n : ℕ) (f : ℕ → ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => f (min i.val j.val)

private def lower (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => if j ≤ i then 1 else 0

private theorem telescope (f : ℕ → ℤ) (j : ℕ) : ∑ i ∈ range (j + 1), delta f i = f j := by
  induction j with
  | zero => simp [delta]
  | succ j ih =>
    rw [sum_range_succ, ih]
    simp [delta]

private theorem lower_det (n : ℕ) : (lower n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [lower]
  · intro i j hij
    change i < j at hij
    simp [lower, not_le_of_gt hij]

private theorem kernel_factor (n : ℕ) (f : ℕ → ℤ) :
    lower n * diagonal (fun i : Fin n => delta f i.val) * (lower n)ᵀ = kernel n f := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, lower, kernel]
  change (∑ k : Fin n, (if k.val ≤ i.val then 1 else 0 : ℤ) * delta f k.val *
    (if k.val ≤ j.val then 1 else 0)) = f (min i.val j.val)
  have hs (k : Fin n) : (if k.val ≤ i.val then 1 else 0 : ℤ) * delta f k.val *
      (if k.val ≤ j.val then 1 else 0) =
        if k.val ≤ min i.val j.val then delta f k.val else 0 := by
    by_cases hi : k.val ≤ i.val <;> by_cases hj : k.val ≤ j.val <;>
      simp [hi, hj]
  simp_rw [hs]
  rw [Fin.sum_univ_eq_sum_range (fun a => if a ≤ min i.val j.val then delta f a else 0)]
  let k := min i.val j.val
  have hk : k + 1 ≤ n := Nat.succ_le_of_lt ((min_le_left _ _).trans_lt i.isLt)
  change (∑ a ∈ range n, if a ≤ k then delta f a else 0) = f k
  rw [← telescope f k]
  have hsub : range (k + 1) ⊆ range n := range_mono hk
  rw [← sum_subset hsub (fun a _ h => if_neg (by simpa [mem_range, Nat.lt_succ_iff] using h))]
  exact sum_congr rfl fun a ha => if_pos (Nat.lt_succ_iff.mp (mem_range.mp ha))

private theorem kernel_det (n : ℕ) (f : ℕ → ℤ) :
    (kernel n f).det = ∏ i : Fin n, delta f i.val := by
  rw [← kernel_factor, det_mul, det_mul, det_transpose, lower_det, one_mul, mul_one,
    det_diagonal]

private def u (p i : ℕ) : ℤ := (i : ℤ) * (2 * p + 1 - i) + p + 1

private def near (p i j : ℕ) : ℤ := u p (min i j) + (max i j : ℤ) - p

private def far (p i j : ℕ) : ℤ := u p (min i j) + p - (max i j : ℤ)

private theorem near_entry (p i j : ℕ) (hi : i ≤ p) (hj : j ≤ p) :
    entry (2 * (p : ℤ) + 1) i j = near p i j := by
  have hrad : radius (2 * (p : ℤ) + 1) i j = min (i : ℤ) (j : ℤ) := by
    unfold radius
    apply min_eq_left
    apply le_min
    · have hm := min_le_left (i : ℤ) (j : ℤ)
      omega
    · have hm := min_le_right (i : ℤ) (j : ℤ)
      omega
  unfold entry near
  rw [hrad]
  by_cases hij : i ≤ j
  · rw [min_eq_left hij, max_eq_right (by exact_mod_cast hij : (i : ℤ) ≤ j), min_eq_left (by exact_mod_cast hij),
      abs_of_nonpos (by omega)]
    unfold u
    ring
  · have hj' : j ≤ i := by omega
    rw [min_eq_right hj', max_eq_left (by exact_mod_cast hj' : (j : ℤ) ≤ i), min_eq_right (by exact_mod_cast hj'),
      abs_of_nonneg (by omega)]
    unfold u
    ring

private theorem far_entry (p i j : ℕ) (hi : i ≤ p) (hj : j ≤ p) :
    entry (2 * (p : ℤ) + 1) i (2 * (p : ℤ) - j) = far p i j := by
  have hrad : radius (2 * (p : ℤ) + 1) i (2 * (p : ℤ) - j) = min (i : ℤ) (j : ℤ) := by
    unfold radius
    rw [min_eq_left (by omega : (i : ℤ) ≤ 2 * (p : ℤ) - j),
      show 2 * (p : ℤ) + 1 - 1 - (2 * (p : ℤ) - j) = j by ring,
      min_eq_right (by omega : (j : ℤ) ≤ 2 * (p : ℤ) + 1 - 1 - i)]
  unfold entry far
  rw [hrad, abs_of_nonpos (by omega)]
  by_cases hij : i ≤ j
  · rw [min_eq_left hij, max_eq_right (by exact_mod_cast hij : (i : ℤ) ≤ j), min_eq_left (by exact_mod_cast hij)]
    unfold u
    ring
  · have hj' : j ≤ i := by omega
    rw [min_eq_right hj', max_eq_left (by exact_mod_cast hj' : (j : ℤ) ≤ i), min_eq_right (by exact_mod_cast hj')]
    unfold u
    ring

private theorem entry_transpose (n i j : ℤ) : entry n i j = entry n j i := by
  unfold entry radius
  rw [min_comm i j, min_comm (n - 1 - i) (n - 1 - j), abs_sub_comm]

private theorem entry_rev (n i j : ℤ) :
    entry n (n - 1 - i) (n - 1 - j) = entry n i j := by
  have hi : n - 1 - (n - 1 - i) = i := by ring
  have hj : n - 1 - (n - 1 - j) = j := by ring
  have hab : n - 1 - i - (n - 1 - j) = j - i := by ring
  simp only [entry, radius, hi, hj, hab]
  rw [min_comm (min (n - 1 - i) (n - 1 - j)), abs_sub_comm]

private def index (p : ℕ) : Fin p ⊕ Fin (p + 1) ≃ Fin (2 * (p + 1) - 1) :=
  ((Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans finSumFinEquiv).trans (finCongr (by omega))

private theorem index_left (p : ℕ) (i : Fin p) : (index p (Sum.inl i)).val = i.val := by
  simp [index, finSumFinEquiv_apply_left]

private theorem index_right (p : ℕ) (i : Fin (p + 1)) :
    ((index p (Sum.inr i)).val : ℤ) = 2 * (p : ℤ) - i.val := by
  change ((finSumFinEquiv (Sum.inr i.rev : Fin p ⊕ Fin (p + 1))).val : ℤ) = _
  rw [finSumFinEquiv_apply_right]
  simp only [Fin.val_natAdd, Fin.val_rev]
  have := i.isLt
  omega

private def nearMatrix (p a b : ℕ) : Matrix (Fin a) (Fin b) ℤ :=
  Matrix.of fun i j => near p i.val j.val

private def farMatrix (p a b : ℕ) : Matrix (Fin a) (Fin b) ℤ :=
  Matrix.of fun i j => far p i.val j.val

private def reordered (p : ℕ) : Matrix (Fin p ⊕ Fin (p + 1)) (Fin p ⊕ Fin (p + 1)) ℤ :=
  fromBlocks (nearMatrix p p p) (farMatrix p p (p + 1))
    (farMatrix p (p + 1) p) (nearMatrix p (p + 1) (p + 1))

private theorem reordered_eq (p : ℕ) : (B (2 * (p + 1) - 1)).submatrix (index p) (index p) =
    reordered p := by
  have hn : ((2 * (p + 1) - 1 : ℕ) : ℤ) = 2 * (p : ℤ) + 1 := by omega
  ext i j
  change entry _ _ _ = _
  rw [hn]
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [index_left, index_right]
  · exact near_entry p _ _ (by have := i.isLt; omega) (by have := j.isLt; omega)
  · exact far_entry p _ _ (by have := i.isLt; omega) (by have := j.isLt; omega)
  · change entry _ _ _ = far p i.val j.val
    rw [entry_transpose]
    simpa only [far, min_comm j.val i.val, max_comm (j.val : ℤ) i.val] using
      far_entry p j.val i.val (by have := j.isLt; omega) (by have := i.isLt; omega)
  · rw [show 2 * (p : ℤ) - i.val = 2 * (p : ℤ) + 1 - 1 - i.val by ring,
      show 2 * (p : ℤ) - j.val = 2 * (p : ℤ) + 1 - 1 - j.val by ring, entry_rev]
    exact near_entry p _ _ (by have := i.isLt; omega) (by have := j.isLt; omega)

private def E (p : ℕ) : Matrix (Fin p) (Fin (p + 1)) ℤ :=
  fun i j => if i.castSucc = j then 1 else 0

private theorem mul_ET {p : ℕ} {I : Type*} (M : Matrix I (Fin (p + 1)) ℤ) :
    M * (E p)ᵀ = Matrix.of fun i j => M i j.castSucc := by
  ext i j
  simp only [mul_apply, transpose_apply, E, mul_ite, mul_one, mul_zero, Matrix.of_apply]
  simp

private theorem E_mul {p : ℕ} {I : Type*} (M : Matrix (Fin (p + 1)) I ℤ) :
    E p * M = Matrix.of fun i j => M i.castSucc j := by
  ext i j
  simp only [mul_apply, E, ite_mul, one_mul, zero_mul, Matrix.of_apply]
  simp [eq_comm]

private theorem mul_E {p : ℕ} {I : Type*} (M : Matrix I (Fin p) ℤ) :
    M * E p = Matrix.of fun i j => if h : j.val < p then M i ⟨j.val, h⟩ else 0 := by
  ext i j
  simp only [mul_apply, E, mul_ite, mul_one, mul_zero, Matrix.of_apply]
  split
  · rename_i h
    have he (k : Fin p) : k.castSucc = j ↔ k = ⟨j.val, h⟩ := by
      constructor
      · intro e
        exact Fin.ext (congrArg (fun a : Fin (p + 1) => a.val) e)
      · intro e
        exact Fin.ext (congrArg (fun a : Fin p => a.val) e)
    simp_rw [he]
    simp
  · rename_i h
    apply sum_eq_zero
    intro k _
    have hk : k.castSucc ≠ j := by
      intro he
      exact h (he ▸ (show k.castSucc.val < p from k.isLt))
    simp [hk]

private theorem ET_mul {p : ℕ} {I : Type*} (M : Matrix (Fin p) I ℤ) :
    (E p)ᵀ * M = Matrix.of fun i j => if h : i.val < p then M ⟨i.val, h⟩ j else 0 := by
  ext i j
  simp only [mul_apply, transpose_apply, E, ite_mul, one_mul, zero_mul, Matrix.of_apply]
  split
  · rename_i h
    have he (k : Fin p) : k.castSucc = i ↔ k = ⟨i.val, h⟩ := by
      constructor
      · intro e
        exact Fin.ext (congrArg (fun a : Fin (p + 1) => a.val) e)
      · intro e
        exact Fin.ext (congrArg (fun a : Fin p => a.val) e)
    simp_rw [he]
    simp
  · rename_i h
    apply sum_eq_zero
    intro k _
    have hk : k.castSucc ≠ i := by
      intro he
      exact h (he ▸ (show k.castSucc.val < p from k.isLt))
    simp [hk]

private def changeBasis (p : ℕ) : Matrix (Fin p ⊕ Fin (p + 1)) (Fin p ⊕ Fin (p + 1)) ℤ :=
  fromBlocks 1 (E p) (-(E p)ᵀ) 1

private def antisymmetricPart (p : ℕ) : Matrix (Fin p) (Fin p) ℤ :=
  fun i j => 2 * (max i.val j.val : ℤ) - 2 * p

private def columnScale (p : ℕ) (j : Fin (p + 1)) : ℤ := if j.val < p then 2 else 1

private def symmetricPart (p : ℕ) : Matrix (Fin (p + 1)) (Fin (p + 1)) ℤ :=
  kernel (p + 1) (u p) * diagonal (columnScale p)

private theorem symmetric_apply (p : ℕ) (i j : Fin (p + 1)) :
    symmetricPart p i j = u p (min i.val j.val) * columnScale p j := by
  simp [symmetricPart, kernel, mul_diagonal]

private theorem basis_change (p : ℕ) :
    reordered p * changeBasis p =
      changeBasis p * fromBlocks (antisymmetricPart p) 0 0 (symmetricPart p) := by
  unfold reordered changeBasis
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_zero,
    Matrix.neg_mul, add_zero, zero_add, mul_ET, ET_mul, mul_E, E_mul]
  congr 1
  · ext i j
    simp [nearMatrix, farMatrix, near, far, antisymmetricPart]
    ring
  · ext i j
    simp only [Matrix.of_apply]
    rw [symmetric_apply]
    by_cases h : j.val < p
    · simp [h, nearMatrix, farMatrix, near, far, columnScale]
      ring
    · have hj : j.val = p := by have := j.isLt; omega
      simp [hj, nearMatrix, farMatrix, near, far, columnScale]
  · ext i j
    by_cases h : i.val < p
    · simp [h, nearMatrix, farMatrix, near, far, antisymmetricPart]
      ring
    · have hi : i.val = p := by have := i.isLt; omega
      have hj : j.val ≤ p := j.isLt.le
      simp [hi, nearMatrix, farMatrix, near, far]
  · ext i j
    rw [symmetric_apply]
    by_cases h : j.val < p
    · simp [h, nearMatrix, farMatrix, near, far, columnScale]
      ring
    · have hj : j.val = p := by have := j.isLt; omega
      have hi : i.val ≤ p := Nat.le_of_lt_succ i.isLt
      have hcast : (i.val : ℤ) ≤ p := by exact_mod_cast hi
      simp [hj, nearMatrix, farMatrix, near, far, columnScale, max_eq_right hcast]

private theorem changeBasis_det (p : ℕ) : (changeBasis p).det ≠ 0 := by
  have hE : E p * (E p)ᵀ = (1 : Matrix (Fin p) (Fin p) ℤ) := by
    rw [mul_ET]
    ext i j
    simp [E, Matrix.one_apply]
  have hET : (E p)ᵀ * E p + 1 = diagonal (columnScale p) := by
    rw [ET_mul]
    ext i j
    simp only [Matrix.add_apply, Matrix.one_apply, diagonal_apply, Matrix.of_apply]
    by_cases hi : i.val < p
    · rw [dif_pos hi]
      have he : (⟨i.val, hi⟩ : Fin p).castSucc = i := Fin.ext rfl
      by_cases hij : i = j
      · subst j
        simp [E, he, columnScale, hi]
      · simp [E, he, hij]
    · rw [dif_neg hi]
      by_cases hij : i = j
      · subst j
        simp [columnScale, hi]
      · simp [hij]
  have hGram : changeBasis p * (changeBasis p)ᵀ =
      fromBlocks ((1 : Matrix (Fin p) (Fin p) ℤ) + 1) 0 0 (diagonal (columnScale p)) := by
    simp [changeBasis, fromBlocks_transpose, fromBlocks_multiply, hE, hET]
  have h2 : (1 : Matrix (Fin p) (Fin p) ℤ) + 1 = diagonal (fun _ => (2 : ℤ)) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  intro hd
  have he := congrArg Matrix.det hGram
  rw [det_mul, hd, zero_mul, h2, det_fromBlocks_zero₂₁, det_diagonal, det_diagonal] at he
  exact (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (by simp)) (Finset.prod_ne_zero_iff.mpr (by
    intro i _
    unfold columnScale
    split <;> decide))) he.symm

private theorem det_split (p : ℕ) :
    (B (2 * (p + 1) - 1)).det = (antisymmetricPart p).det * (symmetricPart p).det := by
  have h := congrArg Matrix.det (basis_change p)
  rw [det_mul, det_mul, det_fromBlocks_zero₂₁, mul_comm (changeBasis p).det] at h
  have h' := mul_right_cancel₀ (changeBasis_det p) h
  rw [← reordered_eq, det_submatrix_equiv_self] at h'
  exact h'

private theorem reversed_anti (p : ℕ) :
    (antisymmetricPart p).submatrix Fin.revPerm Fin.revPerm =
      kernel p (fun i => -2 * ((i : ℤ) + 1)) := by
  ext i j
  simp only [submatrix_apply, antisymmetricPart, Fin.revPerm_apply, kernel, Fin.val_rev]
  have hi := i.isLt
  have hj := j.isLt
  by_cases h : i.val ≤ j.val
  · rw [max_eq_left (by omega), min_eq_left h]
    omega
  · rw [max_eq_right (by omega), min_eq_right (by omega)]
    omega

private theorem det_anti (p : ℕ) : (antisymmetricPart p).det = (-2 : ℤ) ^ p := by
  rw [← Matrix.det_submatrix_equiv_self Fin.revPerm, reversed_anti, kernel_det]
  have hd (i : Fin p) : delta (fun t => -2 * ((t : ℤ) + 1)) i.val = -2 := by
    unfold delta
    split <;> dsimp <;> omega
  simp_rw [hd]
  simp

private theorem det_min (p : ℕ) :
    (kernel (p + 1) (u p)).det = (2 : ℤ) ^ p * ((p + 1).factorial : ℤ) := by
  rw [kernel_det, Fin.prod_univ_succ]
  have hd (i : Fin p) : delta (u p) i.succ.val = 2 * ((p : ℤ) - i.val) := by
    simp [delta, u]
    ring
  simp_rw [hd]
  rw [Finset.prod_mul_distrib]
  have hprod : (∏ i : Fin p, ((p : ℤ) - i.val)) = (p.factorial : ℤ) := by
    calc
      _ = ∏ i : Fin p, ((i.rev.val : ℤ) + 1) := by
        apply Finset.prod_congr rfl
        intro i _
        have := i.isLt
        simp only [Fin.val_rev]
        omega
      _ = ∏ i : Fin p, ((i.val : ℤ) + 1) := by
        simpa only [Fin.revPerm_apply] using Equiv.prod_comp Fin.revPerm (fun i : Fin p => (i.val : ℤ) + 1)
      _ = _ := by
        rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => (i : ℤ) + 1)]
        exact_mod_cast (Nat.factorial_eq_prod_range_add_one p).symm
  rw [hprod, Nat.factorial_succ]
  simp [delta, u]
  ring

private theorem det_sym (p : ℕ) :
    (symmetricPart p).det = (4 : ℤ) ^ p * ((p + 1).factorial : ℤ) := by
  rw [symmetricPart, det_mul, det_diagonal, det_min, Fin.prod_univ_castSucc]
  have hs (i : Fin p) : columnScale p i.castSucc = 2 := by
    simp [columnScale, i.isLt]
  simp_rw [hs]
  simp only [columnScale, Fin.val_last, lt_self_iff_false, if_false, mul_one, prod_const,
    card_univ, Fintype.card_fin]
  rw [show (4 : ℤ) = 2 * 2 by decide, mul_pow]
  ring

end OMA.S_oeis_a259056.Proof

open OMA.S_oeis_a259056.Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a259056.main := by
  intro m hm
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  rw [det_split, det_anti, det_sym, Nat.add_sub_cancel, ← mul_assoc, ← mul_pow, ← mul_pow]
  norm_num

import OMAStatements.S_oeis_a005121

/-!
Rajesh Kumar Mohapatra's triangle has a family of weighted row sums.
Transposing the two finite sums in a row advances the Stirling weight by
one. Iterating recovers Lengyel's recurrence on the diagonal.
-/

namespace UltradissimilarityTriangle

open Finset OMA.S_oeis_a005121

private def weight (t k : ℕ) : ℕ := Nat.stirlingSecond (t + k) k
private def moment (n t : ℕ) : ℕ := ∑ k ∈ Icc 1 n, weight t k * R n k

private theorem weight_sum (t j : ℕ) :
    ∑ k ∈ Icc 1 j, weight t k * k = weight (t + 1) j := by
  induction j with
  | zero => simp [weight, Nat.stirlingSecond]
  | succ j ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ j + 1), ih]
    unfold weight
    rw [show t + 1 + (j + 1) = (t + (j + 1)) + 1 by omega,
      Nat.stirlingSecond_succ_succ]
    rw [show t + 1 + j = t + (j + 1) by omega]
    ring

private theorem transfer (n t : ℕ) :
    (∑ k ∈ Icc 1 n, weight t k * (k * ∑ j ∈ Icc k n, R n j)) =
      moment n (t + 1) := by
  simp_rw [← Nat.mul_assoc, Finset.mul_sum]
  have swap := Finset.sum_Ico_Ico_comm 1 (n + 1) (fun k j => weight t k * k * R n j)
  simp only [Finset.Ico_add_one_right_eq_Icc] at swap
  rw [swap]
  unfold moment
  simp_rw [← Finset.sum_mul, weight_sum]

private theorem row_step (n t : ℕ) :
    moment (n + 2) t = moment (n + 1) (t + 1) + weight t (n + 2) * R (n + 2) (n + 2) := by
  unfold moment
  rw [sum_Icc_succ_top (by omega : 1 ≤ (n + 1) + 1)]
  congr 1
  calc
    _ = ∑ k ∈ Icc 1 (n + 1), weight t k * (k * ∑ j ∈ Icc k (n + 1), R (n + 1) j) := by
      apply sum_congr rfl
      intro k hk
      obtain ⟨hl,hu⟩ := mem_Icc.mp hk
      rw [R, if_pos ⟨hl, by omega⟩]
    _ = _ := transfer (n + 1) t

private theorem diagonal (n : ℕ) : R (n + 2) (n + 2) = moment (n + 1) 1 := by
  rw [R]
  simp only [lt_self_iff_false, and_false, if_false, if_true]
  simpa [weight, Nat.stirlingSecond_self] using transfer (n + 1) 0

private theorem expansion (n t : ℕ) :
    moment (n + 1) t =
      ∑ j ∈ Icc 1 (n + 1), weight (t + (n + 1 - j)) j * R j j := by
  induction n generalizing t with
  | zero => simp [moment]
  | succ n ih =>
    rw [row_step, ih, sum_Icc_succ_top (by omega : 1 ≤ n + 1 + 1)]
    simp only [Nat.sub_self, Nat.add_zero]
    congr 1
    apply sum_congr rfl
    intro k hk
    have hu := (mem_Icc.mp hk).2
    rw [show t + 1 + (n + 1 - k) = t + (n + 1 + 1 - k) by omega]

private theorem diagonal_stirling (n : ℕ) :
    R (n + 2) (n + 2) =
      ∑ k ∈ Icc 1 (n + 1), Nat.stirlingSecond (n + 2) k * R k k := by
  rw [diagonal, expansion]
  apply sum_congr rfl
  intro k hk
  have hu := (mem_Icc.mp hk).2
  simp [weight, show 1 + (n + 1 - k) + k = n + 2 by omega]

private theorem recurrence (n : ℕ) :
    a (n + 2) = ∑ k ∈ Icc 1 (n + 1), Nat.stirlingSecond (n + 2) k * a k := by
  rw [a, Fin.sum_univ_eq_sum_range (fun k : ℕ => if k = 0 then 0 else Nat.stirlingSecond (n + 2) k * a k)]
  classical
  have hr : (range (n + 2)).filter (fun k => k ≠ 0) = Icc 1 (n + 1) := by
    ext k
    simp only [mem_filter, mem_range, mem_Icc]
    omega
  rw [← hr, sum_filter]
  apply sum_congr rfl
  intro k _
  by_cases hk : k = 0 <;> simp [hk]

end UltradissimilarityTriangle

open Finset OMA.S_oeis_a005121 UltradissimilarityTriangle

theorem OMA.solution : type_of% @OMA.S_oeis_a005121.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    match n with
    | 0 => omega
    | 1 => simp [a, R]
    | k + 2 =>
      rw [recurrence, diagonal_stirling]
      apply sum_congr rfl
      intro j hj
      obtain ⟨hl,hu⟩ := mem_Icc.mp hj
      rw [ih j (by omega) hl]

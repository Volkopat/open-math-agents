import OMAStatements.S_oeis_a372706

open OMA.S_oeis_a372706 ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a372706.main := by
  intro n _
  unfold a c
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with h
  · exact isMultiplicative_moebius.map_mul_of_coprime (Nat.Coprime.symm h)
  · rw [mul_zero]
    apply moebius_eq_zero_of_not_squarefree
    intro hs
    exact h (Nat.squarefree_mul_iff.mp hs).1.symm

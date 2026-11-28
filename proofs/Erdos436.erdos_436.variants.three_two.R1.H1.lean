import OMAReductions.R_Erdos436_erdos_436_variants_three_two_R1
import Mathlib

-- Step Erdos436.erdos_436.variants.three_two.R1.H1: hypothesis H1 of reduction Erdos436.erdos_436.variants.three_two.R1
-- Credit: @luciusacarr

/-! Ten witnesses `n ∈ {1, 7, 8, 11, 12, 21, 26, 27, 63, 77}` suffice: their factor sums only involve
`w` at the primes `2, 3, 7, 11, 13`, so after factoring, `decide` checks all `3 ^ 5` value patterns. -/

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_three_two_R1.H1 := by
  intro w
  obtain ⟨n, hn, h⟩ : ∃ n ∈ [1, 7, 8, 11, 12, 21, 26, 27, 63, 77],
      (n.primeFactorsList.map w).sum = 0 ∧ ((n + 1).primeFactorsList.map w).sum = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, exists_eq_or_imp, or_false, exists_eq_left,
      Nat.reduceAdd, Nat.primeFactorsList_ofNat, Nat.primeFactorsList_one, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil]
    generalize w 2 = a, w 3 = b, w 7 = d, w 11 = e, w 13 = f
    revert a b d e f
    set_option synthInstance.maxSize 2000 in decide
  exact ⟨n, by simp at hn; simp; omega, h⟩

import OMAReductions.R_Erdos436_erdos_436_variants_four_two_R1
import Mathlib

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_four_two_R1.H1 := by
  intro w
  suffices ∃ n ∈ [1, 6, 9, 15, 16, 20, 24, 33, 35, 48, 49, 64, 77, 80, 84, 99, 104, 120, 135, 153, 168, 169,
      195, 220, 255, 324, 351, 384, 440, 441, 594, 624, 675, 728, 935, 1155, 1224, 18, 40, 81, 245, 285, 286,
      399], (n.primeFactorsList.map w).sum = 0 ∧ ((n + 1).primeFactorsList.map w).sum = 0 by
    obtain ⟨n, hn, h⟩ := this
    exact ⟨n, Finset.mem_Icc.2 (by simp at hn; omega), h⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp, exists_eq_left, Nat.reduceAdd,
    Nat.primeFactorsList_ofNat, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, true_and]
  generalize w 2 = a, w 3 = b, w 5 = c, w 7 = d, w 11 = e, w 13 = f, w 17 = g, w 19 = h, w 23 = i,
    w 29 = j, w 31 = k, w 37 = l, w 41 = m
  revert a b c d e f g h i j k l m
  simp only [forall_or_left]
  decide +kernel

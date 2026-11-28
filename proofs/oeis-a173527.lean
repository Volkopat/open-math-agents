import OMAStatements.S_oeis_a173527

namespace OMA.A173527Proof

lemma digit_sum_step (N i : ℕ) (hi : i < 7) :
    (Nat.digits 7 (7 * N + i)).sum = (Nat.digits 7 N).sum + i := by
  rcases Nat.eq_zero_or_pos (7 * N + i) with h | h
  · have hN : N = 0 := by omega
    have hi0 : i = 0 := by omega
    subst hN hi0
    simp
  · rw [Nat.digits_def' (by norm_num) h]
    have h1 : (7 * N + i) % 7 = i := by omega
    have h2 : (7 * N + i) / 7 = N := by omega
    rw [h1, h2, List.sum_cons]
    ring

end OMA.A173527Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a173527.main := by
  refine ⟨by simp [OMA.S_oeis_a173527.a], ?_⟩
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.flatMap_append, ih,
      show 7 * (N + 1) = 7 * N + 7 by ring, List.range_add, List.map_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      OMA.S_oeis_a173527.phi, List.map_map]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp, OMA.S_oeis_a173527.a, Nat.add_sub_cancel]
    rw [OMA.A173527Proof.digit_sum_step N i hi]
    ring

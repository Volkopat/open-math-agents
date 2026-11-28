import OMAStatements.S_oeis_a288205

namespace OMA.P_oeis_a288205

open OMA.S_oeis_a288205

lemma sr_split (q : List ℕ) :
    sr ([0, 0, 1, 0, 0, 1] ++ q) = [0, 0, 1, 0, 0, 1] ++ ([0, 0, 0, 1, 0, 0, 1, 0] ++ sr q) := by
  simp [sr]

lemma prefix_iter (M : ℕ) (hM : 2 ≤ M) : ∃ q, sr^[M] [0, 0] = [0, 0, 1, 0, 0, 1] ++ q := by
  induction M, hM using Nat.le_induction with
  | base => exact ⟨[0, 0], by decide⟩
  | succ M _ ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨[0, 0, 0, 1, 0, 0, 1, 0] ++ sr q, ?_⟩
    rw [Function.iterate_succ_apply', hq, sr_split]

lemma letter (M : ℕ) (hM : 2 ≤ M) (i : ℕ) (hi : i < 6) :
    (sr^[M] [0, 0])[i]? = [0, 0, 1, 0, 0, 1][i]? := by
  obtain ⟨q, hq⟩ := prefix_iter M hM
  rw [hq, List.getElem?_append_left (by simpa using hi)]

lemma isOne_iff (i : ℕ) (hi : i < 6) : IsOne i ↔ [0, 0, 1, 0, 0, 1][i]? = some 1 := by
  constructor
  · rintro ⟨N, hN⟩
    rw [← letter (max N 2) (le_max_right _ _) i hi]
    exact hN _ (le_max_left _ _)
  · intro h
    exact ⟨2, fun M hM => by rw [letter M hM i hi, h]⟩

end OMA.P_oeis_a288205

open OMA.S_oeis_a288205 OMA.P_oeis_a288205 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a288205.main) := by
  intro h
  have h2 := h 2 (by norm_num)
  classical
  have hc : Nat.count IsOne 5 = 1 := by
    simp only [Nat.count_succ, Nat.count_zero, isOne_iff 0 (by norm_num), isOne_iff 1 (by norm_num),
      isOne_iff 2 (by norm_num), isOne_iff 3 (by norm_num), isOne_iff 4 (by norm_num)]
    decide
  have h5 : IsOne 5 := (isOne_iff 5 (by norm_num)).mpr rfl
  have ha : a 2 = 6 := by
    unfold a
    rw [show 2 - 1 = Nat.count IsOne 5 from hc.symm, Nat.nth_count h5]
  have hA1 : A036987 1 = 1 := by decide
  have hA2 : A036987 2 = 0 := by decide
  rw [ha, show Finset.Icc 1 2 = {1, 2} from rfl, Finset.sum_pair (by norm_num), hA1, hA2] at h2
  norm_num at h2

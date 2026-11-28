import OMAStatements.S_oeis_a288999

namespace OMA.P_oeis_a288999

open OMA.S_oeis_a288999

/-- the stable prefix of length 38 -/
abbrev P : List ℕ :=
  [0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1,
    0, 0, 1, 0, 0, 1, 0]

lemma sr_split (q : List ℕ) :
    sr (P ++ q) = P ++ ([0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0,
      0, 0, 1] ++ sr q) := by
  simp [P, sr]

lemma prefix_iter (M : ℕ) (hM : 6 ≤ M) : ∃ q, sr^[M] [0, 0] = P ++ q := by
  induction M, hM using Nat.le_induction with
  | base => exact ⟨[0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1], by decide⟩
  | succ M _ ih =>
    obtain ⟨q, hq⟩ := ih
    exact ⟨_, by rw [Function.iterate_succ_apply', hq, sr_split]⟩

lemma letter (M : ℕ) (hM : 6 ≤ M) (i : ℕ) (hi : i < 38) : (sr^[M] [0, 0])[i]? = P[i]? := by
  obtain ⟨q, hq⟩ := prefix_iter M hM
  rw [hq, List.getElem?_append_left (by simpa using hi)]

lemma isOne_iff (i : ℕ) (hi : i < 38) : IsOne i ↔ P[i]? = some 1 := by
  constructor
  · rintro ⟨N, hN⟩
    rw [← letter (max N 6) (le_max_right _ _) i hi]
    exact hN _ (le_max_left _ _)
  · intro h
    exact ⟨6, fun M hM => by rw [letter M hM i hi, h]⟩

lemma round_11 : round ((11 : ℝ) * Real.sqrt 2) = 16 := by
  have h1 : (31 / 22 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have h2 : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> push_cast <;> linarith

end OMA.P_oeis_a288999

open OMA.S_oeis_a288999 OMA.P_oeis_a288999 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a288999.main) := by
  intro h
  have h11 := h.2.2 11 (by norm_num)
  classical
  have hc : Nat.count IsOne 36 = 10 := by
    have e : ∀ i ∈ Finset.range 36, (IsOne i ↔ P[i]? = some 1) := fun i hi =>
      isOne_iff i (by simp at hi; omega)
    rw [Nat.count_eq_card_filter_range, Finset.filter_congr e]
    decide
  have h36 : IsOne 36 := (isOne_iff 36 (by norm_num)).mpr rfl
  have ha : a 11 = 37 := by
    unfold a
    rw [show 11 - 1 = Nat.count IsOne 36 from hc.symm, Nat.nth_count h36]
  rw [ha] at h11
  push_cast at h11
  rw [round_11] at h11
  norm_num at h11

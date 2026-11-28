import OMAStatements.S_oeis_a057033

namespace OMA.S_oeis_a057033

private theorem position_shift (m fixed i : ℕ) :
    sourcePosition m (fixed + 1) (i + 1) = sourcePosition m fixed i + 1 := by
  by_cases hi : i < fixed
  · simp [sourcePosition, hi, show i + 1 < fixed + 1 by omega]
  · have hs : ¬ i + 1 < fixed + 1 := by omega
    have he : i + 1 - (fixed + 1) = i - fixed := by omega
    simp only [sourcePosition, if_neg hi, if_neg hs, he]
    omega

private theorem stages_shift (r i : ℕ) :
    afterStages 1 r (i + 1) = afterStages 0 r i + 1 := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih =>
    simp only [afterStages, Nat.add_zero]
    rw [position_shift, ih]

end OMA.S_oeis_a057033

open OMA.S_oeis_a057033 in
theorem OMA.solution : type_of% @OMA.S_oeis_a057033.main := by
  intro n hn
  have hfix : sourcePosition (n + 2) (n + 1 + 1) n = n := by
    simp [sourcePosition]
  have hshift := stages_shift n (n - 1)
  rw [Nat.sub_add_cancel (show 1 ≤ n by omega)] at hshift
  unfold term
  rw [Nat.add_sub_cancel, afterStages.eq_2, hfix, hshift, Nat.add_sub_cancel]

import OMAStatements.S_oeis_a111205
import Mathlib
-- Credit: @ptc-prover-bot

open OMA.S_oeis_a111205

/-- For `r = 3t + 1` the number `k = r^2 + 2` lies strictly between `r^2` and `(r+1)^2`,
and `3` divides both `k` and `2r + 1`. -/
lemma mem (t : ℕ) (ht : 1 ≤ t) : (3 * t + 1) ^ 2 + 2 ∈ terms := by
  refine ⟨by nlinarith, ?_, 3 * t + 1, by nlinarith, by nlinarith, ?_⟩
  · intro hp
    have h3 : 3 ∣ (3 * t + 1) ^ 2 + 2 := ⟨3 * t ^ 2 + 2 * t + 1, by ring⟩
    rcases hp.eq_one_or_self_of_dvd 3 h3 with h | h
    · omega
    · nlinarith
  · have h3 : 3 ∣ Nat.gcd ((3 * t + 1) ^ 2 + 2) (2 * (3 * t + 1) + 1) :=
      Nat.dvd_gcd ⟨3 * t ^ 2 + 2 * t + 1, by ring⟩ ⟨2 * t + 1, by ring⟩
    have hpos : 0 < Nat.gcd ((3 * t + 1) ^ 2 + 2) (2 * (3 * t + 1) + 1) :=
      Nat.gcd_pos_of_pos_right _ (by omega)
    have := Nat.le_of_dvd hpos h3
    omega

theorem main' : terms.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ⟨(3 * (N + 1) + 1) ^ 2 + 2, mem _ (by omega), ?_⟩
  nlinarith


theorem OMA.solution : type_of% @OMA.S_oeis_a111205.main := main'

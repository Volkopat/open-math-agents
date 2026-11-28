import OMAReductions.R_oeis_a126241_R1
import Mathlib

/-! Step oeis-a126241.R1.H1, the classical halves. Terras's inequality `3^u n ≤ 2^d T^d(n)` holds
by induction on `d`, since `2 T(m) = m` for even `m` and `2 T(m) = 3m + 1 ≥ 3m` for odd `m`. A
drop `T^d(n) < n` then forces `3^u < 2^d`. Before a coefficient stopping time, `2^e ≤ 3^u` gives
`n ≤ T^e(n)`. -/

namespace OMA.A126241H1

open OMA.S_oeis_a126241

lemma oddSteps_succ (n d : ℕ) :
    oddSteps n (d + 1) = oddSteps n d + (if T^[d] n % 2 = 1 then 1 else 0) := by
  unfold oddSteps
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

/-- Terras's inequality `3^u n ≤ 2^d T^d(n)`. -/
lemma terras (n : ℕ) : ∀ d, 3 ^ oddSteps n d * n ≤ 2 ^ d * T^[d] n := by
  intro d
  induction d with
  | zero => simp [oddSteps]
  | succ d ih =>
    rw [oddSteps_succ, Function.iterate_succ_apply']
    set m := T^[d] n
    unfold T
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · have e : 2 ^ (d + 1) * (m / 2) = 2 ^ d * m := by
        rw [pow_succ]; have : m = 2 * (m / 2) := by omega
        conv_rhs => rw [this]
        ring
      simp only [h, if_true, show ¬ (0 = 1) by norm_num, if_false, add_zero, e]
      exact ih
    · have e : 2 ^ (d + 1) * ((3 * m + 1) / 2) = 2 ^ d * (3 * m + 1) := by
        rw [pow_succ]; have : 3 * m + 1 = 2 * ((3 * m + 1) / 2) := by omega
        conv_rhs => rw [this]
        ring
      simp only [h, if_true, show ¬ (1 = 0) by norm_num, if_false]
      rw [e, pow_succ]
      nlinarith [Nat.zero_le (2 ^ d)]

theorem main (n : ℕ) (_hn : 2 ≤ n) (d : ℕ) :
    (IsDropTime n d → 3 ^ oddSteps n d < 2 ^ d) ∧
    (IsCoefTime n d → 1 ≤ d ∧ ∀ e, 1 ≤ e → e < d → n ≤ T^[e] n) := by
  constructor
  · rintro ⟨-, hlt, -⟩
    have h := terras n d
    have : 2 ^ d * T^[d] n < 2 ^ d * n := Nat.mul_lt_mul_of_pos_left hlt (by positivity)
    have : 3 ^ oddSteps n d * n < 2 ^ d * n := lt_of_le_of_lt h this
    exact Nat.lt_of_mul_lt_mul_right this
  · rintro ⟨hlt, hle⟩
    refine ⟨?_, fun e _ hed => ?_⟩
    · by_contra h0
      have : d = 0 := by omega
      subst this
      simp [oddSteps] at hlt
    · have h1 := terras n e
      have h2 : 2 ^ e * n ≤ 3 ^ oddSteps n e * n := Nat.mul_le_mul_right n (hle e hed)
      exact Nat.le_of_mul_le_mul_left (h2.trans h1) (by positivity)

end OMA.A126241H1

theorem OMA.solution : OMA.R_oeis_a126241_R1.H1 :=
  OMA.A126241H1.main

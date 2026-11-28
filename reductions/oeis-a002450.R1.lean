import OMAStatements.S_oeis_a002450
import Mathlib

/-! Characterize entry into the powers of two by the odd predecessor.
The remaining conjecture only asks for strict descent from each odd starting value above one. -/
namespace OMA.R_oeis_a002450_R1
open OMA.S_oeis_a002450

def H1 : Prop := ∀ n s : ℕ, 0 < n → (¬ ∃ e : ℕ, n = 2 ^ e) →
  (∃ e : ℕ, collatz^[s] n = 2 ^ e) →
  ∃ m k : ℕ, m < s ∧ 2 ≤ k ∧ collatz^[m] n = (4 ^ k - 1) / 3

def H2 : Prop := ∀ n : ℕ, 1 < n → n % 2 = 1 → ∃ t, collatz^[t] n < n

theorem stepPos {n : ℕ} (pos : 0 < n) : 0 < collatz n := by
  unfold collatz
  split <;> omega

theorem iterPos {n : ℕ} (pos : 0 < n) (s : ℕ) : 0 < collatz^[s] n := by
  induction s with
  | zero => exact pos
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact stepPos ih

/-- Descent of odd orbits suffices, since every positive even start decreases immediately. -/
theorem reachesOne (descent : H2) (n : ℕ) (pos : 0 < n) :
    ∃ s : ℕ, collatz^[s] n = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases one : n = 1
    · exact ⟨0, one⟩
    have down : ∃ t : ℕ, collatz^[t] n < n := by
      by_cases even : n % 2 = 0
      · refine ⟨1, ?_⟩
        simp [collatz, even]
        omega
      · exact descent n (by omega) (by omega)
    obtain ⟨t, lt⟩ := down
    obtain ⟨s, last⟩ := ih (collatz^[t] n) lt (iterPos pos t)
    exact ⟨s + t, by simpa [Function.iterate_add_apply] using last⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a002450.main := by
  intro entrance descent n pos nonpower
  obtain ⟨s, one⟩ := reachesOne descent n pos
  obtain ⟨m, k, _, hk, value⟩ := entrance n s pos nonpower ⟨0, by simpa using one⟩
  exact ⟨m, k, hk, value⟩

end OMA.R_oeis_a002450_R1

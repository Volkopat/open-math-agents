import OMAStatements.S_oeis_a231978
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

open OMA.S_oeis_a231978

/-- The square of 19609 is composite, and its own square admits exactly
the five divisors 19609^e with 0 ≤ e ≤ 4. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a231978.main := by
  refine ⟨19609^2, ⟨by decide, Nat.Prime.not_prime_pow (by decide)⟩, ?_⟩
  have he : ((19609:ℕ)^2)^2 = 19609^4 := by decide
  rw [he]
  refine ⟨by decide, ⟨by decide, Nat.Prime.not_prime_pow (by decide)⟩, ?_, ?_⟩
  · unfold odious
    decide
  · intro d _ hd
    obtain ⟨e, he', rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 19609)).mp hd
    unfold odious
    interval_cases e <;> decide

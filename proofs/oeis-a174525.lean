import OMAStatements.S_oeis_a174525
import Mathlib

/-
A174525: every odd square N other than 1 is a term.

Write N = (2t+1)^2 with t >= 1 and take a = t^2, b = 4t^2 + 2t + 1. Both lie in [1, N), and
  a N + b = (2t^2 + t + 1)^2,   b N + a = (4t^2 + 3t + 1)^2,
which differ because a < b and N > 1.
-/

namespace OMA.P174525

lemma main' : ∀ N : ℕ, IsSquare N → Odd N → N ≠ 1 →
    ∃ a b : ℕ, 1 ≤ a ∧ a < N ∧ 1 ≤ b ∧ b < N ∧
      IsSquare (a * N + b) ∧ IsSquare (b * N + a) ∧ a * N + b ≠ b * N + a := by
  rintro N ⟨r, rfl⟩ hodd hne
  obtain ⟨t, rfl⟩ : Odd r := (Nat.odd_mul.1 hodd).1
  have ht : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · simp at hne
    · exact h
  refine ⟨t ^ 2, 4 * t ^ 2 + 2 * t + 1, by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    ⟨2 * t ^ 2 + t + 1, by ring⟩, ⟨4 * t ^ 2 + 3 * t + 1, by ring⟩, ?_⟩
  intro h
  nlinarith

end OMA.P174525

theorem OMA.solution : type_of% @OMA.S_oeis_a174525.main := by
  intro N h1 h2 h3
  exact OMA.P174525.main' N h1 h2 h3

import OMAStatements.S_oeis_a329725

-- Problem oeis-a329725: with p(n) the product of the nonzero decimal digits of n and
-- a(1) = 0, a(n) = n - p(n) - a(n-1), the statement is a(10n+1) - a(10n-1) = 1 for n >= 1.
-- Upstream: statements/oeis-a329725.lean (declaration OMA.S_oeis_a329725.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Unfolding the recurrence twice gives a(10n+1) - a(10n-1) = 1 - p(10n+1) + p(10n). The numbers 10n+1 and
-- 10n have the same digits except the last (1 and 0), and neither changes the product of nonzero digits.

open OMA.S_oeis_a329725

private lemma p_ten_mul_add_one_a329725 (t : ℕ) (ht : 0 < t) : p (10 * t + 1) = p (10 * t) := by
  unfold p
  rw [Nat.digits_def' (b := 10) (by norm_num) (by omega : 0 < 10 * t + 1),
    Nat.digits_def' (b := 10) (by norm_num) (by omega : 0 < 10 * t)]
  have h1 : (10 * t + 1) % 10 = 1 := by omega
  have h2 : (10 * t + 1) / 10 = t := by omega
  have h3 : (10 * t) % 10 = 0 := by omega
  have h4 : (10 * t) / 10 = t := by omega
  rw [h1, h2, h3, h4]
  simp

theorem OMA.solution : type_of% @OMA.S_oeis_a329725.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have i1 : 10 * (m + 1) + 1 = 10 * m + 9 + 2 := by omega
  have i2 : 10 * (m + 1) - 1 = 10 * m + 9 := by omega
  have i3 : 10 * m + 9 + 1 = 10 * m + 8 + 2 := by omega
  have i4 : 10 * m + 8 + 1 = 10 * m + 9 := by omega
  have h11 : a (10 * m + 9 + 2) =
      ((10 * m + 9 + 2 : ℕ) : ℤ) - (p (10 * m + 9 + 2) : ℤ) - a (10 * m + 9 + 1) := rfl
  have h10 : a (10 * m + 8 + 2) =
      ((10 * m + 8 + 2 : ℕ) : ℤ) - (p (10 * m + 8 + 2) : ℤ) - a (10 * m + 8 + 1) := rfl
  have hp : p (10 * m + 9 + 2) = p (10 * m + 8 + 2) := by
    have h := p_ten_mul_add_one_a329725 (m + 1) (by omega)
    have j1 : 10 * (m + 1) + 1 = 10 * m + 9 + 2 := by omega
    have j2 : 10 * (m + 1) = 10 * m + 8 + 2 := by omega
    rw [j1, j2] at h
    exact h
  rw [i1, i2, h11, i3, h10, i4, hp]
  push_cast
  ring

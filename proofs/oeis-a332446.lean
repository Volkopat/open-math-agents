import OMAStatements.S_oeis_a332446

/-! The binary recursion handles all numbers congruent to three modulo eight.
Primality is used only to identify the sum of the divisors. -/

namespace A332446Proof

open OMA.S_oeis_a332446

private theorem even_arg (n : ℕ) : A087808 (2 * n) = 2 * A087808 n := by
  by_cases hn : n = 0
  · subst n
    have hz : A087808 0 = 0 := by rw [A087808]; simp
    simp [hz]
  · conv_lhs => rw [A087808]
    simp [show 2 * n ≠ 0 by omega, show (2 * n) % 2 = 0 by omega,
      show (2 * n) / 2 = n by omega]

private theorem odd_arg (n : ℕ) : A087808 (2 * n + 1) = A087808 n + 1 := by
  conv_lhs => rw [A087808]
  simp [show (2 * n + 1) / 2 = n by omega]

theorem same_value (k : ℕ) : A087808 (1 + (8 * k + 3)) = A087808 (2 * (8 * k + 3)) := by
  have hleft : 1 + (8 * k + 3) = 2 * (2 * (2 * k + 1)) := by omega
  have hright : 8 * k + 3 = 2 * (2 * (2 * k) + 1) + 1 := by omega
  rw [hleft, even_arg, even_arg, odd_arg, even_arg, hright, odd_arg, odd_arg, even_arg]
  omega

end A332446Proof

open OMA.S_oeis_a332446

theorem OMA.solution : type_of% @OMA.S_oeis_a332446.main := by
  intro p hp hr
  refine ⟨hp.pos, ?_⟩
  rw [hp.divisors, Finset.sum_pair hp.ne_one.symm]
  have heq : 8 * (p / 8) + 3 = p := by omega
  simpa only [heq] using A332446Proof.same_value (p / 8)

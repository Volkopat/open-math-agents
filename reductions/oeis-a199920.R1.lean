import OMAStatements.S_oeis_a199920

-- Reduction oeis-a199920.R1 of A199920: splits Zhi-Wei Sun's two conjectures
-- (n = p + k with p, p+6, 6k-1, 6k+1 prime / with p, p+6, 3k-2+n%2, 3k+2-n%2 prime)
-- into two steps. Credit: @kernl

namespace OMA.R_oeis_a199920_R1

/-- Conjecture 1: every n > 11 is p + k with p, p+6, 6k-1 and 6k+1 all prime. -/
def H1 : Prop := ∀ n : ℕ, 11 < n → ∃ p k : ℕ, 1 ≤ k ∧ n = p + k ∧
  p.Prime ∧ (p + 6).Prime ∧ (6 * k - 1).Prime ∧ (6 * k + 1).Prime

/-- Conjecture 2: every n > 6 with n ≠ 319 is p + k with p, p+6, 3k-2+n%2 and 3k+2-n%2
all prime. -/
def H2 : Prop := ∀ n : ℕ, 6 < n → n ≠ 319 → ∃ p k : ℕ, 1 ≤ k ∧ n = p + k ∧
  p.Prime ∧ (p + 6).Prime ∧ (3 * k - 2 + n % 2).Prime ∧ (3 * k + 2 - n % 2).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a199920.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a199920_R1

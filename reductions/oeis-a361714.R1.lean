import OMAStatements.S_oeis_a361714

-- Reduction oeis-a361714.R1 of A361714: a(n) = Sum_{k = 0..n-1} (-1)^(n+k+1)*binomial(n,k)*binomial(n+k-1,k)^2.
-- Credit: @kernl
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a361714_R1

open OMA.S_oeis_a361714

/-- Conjecture 1 of the entry: a(p) == a(1) (mod p^5) for every prime p >= 7. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → 7 ≤ p → (p : ℤ) ^ 5 ∣ a p - a 1

/-- Conjecture 2 of the entry: a(p^r) == a(p^(r-1)) (mod p^(3*r+3)) for every prime p >= 7 and r >= 2. -/
def H2 : Prop := ∀ p r : ℕ, p.Prime → 7 ≤ p → 2 ≤ r → (p : ℤ) ^ (3 * r + 3) ∣ a (p ^ r) - a (p ^ (r - 1))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a361714.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a361714_R1

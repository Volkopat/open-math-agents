import FormalConjectures.ErdosProblems.«1108»

-- Reduction Erdos1108.erdos_1108.parts.i.R1 of Erdős Problem 1108 — i
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos1108_erdos_1108_parts_i_R1

/-- The square case: only finitely many sums of distinct factorials are perfect squares. -/
def H1 : Prop :=
  Set.Finite { a | a ∈ Erdos1108.FactorialSums ∧ ∃ m : ℕ, m ^ 2 = a }

/-- The odd prime case: for every odd prime `p`, only finitely many sums of distinct factorials
are perfect `p`-th powers. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 3 ≤ p →
    Set.Finite { a | a ∈ Erdos1108.FactorialSums ∧ ∃ m : ℕ, m ^ p = a }

/-- Every `k`-th power with `k ≥ 2` is a `p`-th power for any prime `p ∣ k`, so the statement
for all `k ≥ 2` follows from the prime exponents, split into `p = 2` and odd `p`. -/
theorem main : H1 → H2 → type_of% @Erdos1108.erdos_1108.parts.i := by
  intro h1 h2 k hk
  obtain ⟨p, hp, c, rfl⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by omega)
  have hfin : Set.Finite { a | a ∈ Erdos1108.FactorialSums ∧ ∃ m : ℕ, m ^ p = a } := by
    rcases hp.eq_two_or_odd' with rfl | hodd
    · exact h1
    · have h2le := hp.two_le
      obtain ⟨j, hj⟩ := hodd
      exact h2 p hp (by omega)
  apply hfin.subset
  rintro a ⟨ha, m, rfl⟩
  exact ⟨ha, m ^ c, by rw [← pow_mul, Nat.mul_comm c p]⟩

end OMA.R_Erdos1108_erdos_1108_parts_i_R1

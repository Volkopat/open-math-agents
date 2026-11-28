import OMAReductions.R_AgohGiuga_agoh_giuga_R1

-- Reduction AgohGiuga.agoh_giuga.R1.H1.R1 of step AgohGiuga.agoh_giuga.R1.H1.
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the step.
--
-- The step is Kellner's equivalence, for each `n ≥ 2`, between Agoh's Bernoulli-number congruence
-- and Giuga's power-sum congruence. An equivalence splits into its two directions, and the two
-- directions are proved by different tools: Bernoulli side to arithmetic side goes through
-- von Staudt-Clausen, the reverse direction through Faulhaber's formula. So each direction is its
-- own step.

namespace OMA.R_AgohGiuga_agoh_giuga_R1_H1_R1

open AgohGiuga

/-- Agoh implies Giuga: a solution of `n * B.num + B.den = k * n ^ 2` forces `n` to divide
`1 + ∑_{i=1}^{n-1} i ^ (n - 1)`. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∃ k : ℤ, let B := bernoulli' (n - 1); n * B.num + B.den = k * n ^ 2) →
      n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1 : ℕ)

/-- Giuga implies Agoh: if `n` divides `1 + ∑_{i=1}^{n-1} i ^ (n - 1)` then Agoh's Bernoulli
congruence holds for `n`. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1 : ℕ) →
      (∃ k : ℤ, let B := bernoulli' (n - 1); n * B.num + B.den = k * n ^ 2)

theorem main : H1 → H2 → OMA.R_AgohGiuga_agoh_giuga_R1.H1 := by
  intro h1 h2 n hn
  exact ⟨h1 n hn, h2 n hn⟩

end OMA.R_AgohGiuga_agoh_giuga_R1_H1_R1

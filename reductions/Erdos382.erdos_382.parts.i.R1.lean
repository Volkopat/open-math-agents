import FormalConjectures.ErdosProblems.«382»

-- Reduction Erdos382.erdos_382.parts.i.R1 of Erdős Problem 382 — i
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open Filter

namespace OMA.R_Erdos382_erdos_382_parts_i_R1

/-- Cramér-type prime gaps: for every positive exponent, eventually there is a prime in
(u, u + u^ε]. This is the hard open input, a conjecture on gaps between consecutive primes. -/
def H1 : Prop := ∀ ε > (0 : ℝ), ∀ᶠ u : ℕ in atTop,
  ∃ p : ℕ, p.Prime ∧ u < p ∧ (p : ℝ) ≤ (u : ℝ) + (u : ℝ) ^ ε

/-- Elementary cut: if the largest prime factor of the interval product occurs at least twice,
no prime can lie strictly between u and v. Equivalently every prime in (u, v] appears with
exponent exactly one in the product, so it cannot be the repeated largest prime. -/
def H2 : Prop := ∀ u v : ℕ, Erdos382.LargestPrimeRepeated u v →
  ∀ p : ℕ, p.Prime → u < p → p ≤ v → False

theorem main : H1 → H2 → type_of% @Erdos382.erdos_382.parts.i := by
  intro h1 h2 ε hε
  dsimp [H1] at h1
  specialize h1 ε hε
  rw [Filter.eventually_atTop] at h1 ⊢
  obtain ⟨N, hN⟩ := h1
  refine ⟨2 * N + 1, ?_⟩
  intro v hv u huv
  have huvle : u ≤ v := huv.2.1
  have hvu : v < 2 * u := Erdos382.lt_two_mul_of_largestPrimeRepeated huv
  have huN : N ≤ u := by omega
  obtain ⟨p, hp, hup, hple⟩ := hN u huN
  have hgap : (v : ℝ) - (u : ℝ) ≤ (u : ℝ) ^ ε := by
    by_contra hnot
    have hlt : (u : ℝ) + (u : ℝ) ^ ε < (v : ℝ) := by linarith
    have hpv : p ≤ v := by
      exact_mod_cast (le_of_lt (lt_of_le_of_lt hple hlt))
    exact h2 u v huv p hp hup hpv
  have hpow : (u : ℝ) ^ ε ≤ (v : ℝ) ^ ε := by
    exact Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ u) (by exact_mod_cast huvle) (le_of_lt hε)
  have hreal : ((v - u : ℕ) : ℝ) = (v : ℝ) - (u : ℝ) := by
    rw [Nat.cast_sub huvle]
  rw [hreal]
  linarith

end OMA.R_Erdos382_erdos_382_parts_i_R1

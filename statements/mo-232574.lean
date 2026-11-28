import Mathlib

namespace OMA.S_mo_232574

/-- For a fixed integer polynomial of degree at least two, the number of
ordered integer pairs whose polynomial values have sum n grows at most
as a constant times any positive power of n. -/
theorem main :
    ∀ f : Polynomial ℤ, 1 < f.natDegree →
      ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, 0 < C ∧
          ∃ N : ℕ, 0 < N ∧
            ∀ n : ℕ, N ≤ n →
              let solutions := {p : ℤ × ℤ | f.eval p.1 + f.eval p.2 = (n : ℤ)}
              solutions.Finite ∧ (solutions.ncard : ℝ) ≤ C * (n : ℝ) ^ ε := by
  sorry

end OMA.S_mo_232574

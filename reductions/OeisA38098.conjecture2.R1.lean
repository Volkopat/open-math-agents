import FormalConjectures.OEIS.«38098»

-- Reduction OeisA38098.conjecture2.R1 of Number of primes < n^3 — conjecture2
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is a conjunction of two independent statements about the ratios
-- `pi (n ^ 2) / n ^ 2`: injectivity of the whole sequence, and strict decrease past `15646`.

namespace OMA.R_OeisA38098_conjecture2_R1

/-- All the numbers `pi (n ^ 2) / n ^ 2` for `n >= 1` are pairwise distinct. -/
def H1 : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
    (Nat.primeCounting (m ^ 2) : ℚ) / (m ^ 2 : ℚ) =
    (Nat.primeCounting (n ^ 2) : ℚ) / (n ^ 2 : ℚ) → m = n

/-- Past `n = 15646` the ratios are strictly decreasing. -/
def H2 : Prop :=
  ∀ n : ℕ, 15646 < n →
    (Nat.primeCounting ((n + 1) ^ 2) : ℚ) / ((n + 1) ^ 2 : ℚ) <
    (Nat.primeCounting (n ^ 2) : ℚ) / (n ^ 2 : ℚ)

theorem main : H1 → H2 → type_of% @OeisA38098.conjecture2 := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_OeisA38098_conjecture2_R1

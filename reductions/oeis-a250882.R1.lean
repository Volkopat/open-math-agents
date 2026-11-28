import OMAStatements.S_oeis_a250882

-- Reduction oeis-a250882.R1 of A250882: splits Barker's two conjectures
-- (the generating-function identity and the recurrence) into two steps.
-- Credit: @kernl

namespace OMA.R_oeis_a250882_R1

open OMA.S_oeis_a250882
open PowerSeries

/-- Conjecture 1: the generating-function identity A(x) * (1 - x)^4 = 2x(18565 - ...). -/
def H1 : Prop :=
  PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
    2 * X * (18565 - 8726 * X + 8193 * X ^ 2 - 2048 * X ^ 3)

/-- Conjecture 2: the recurrence a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) - a(n-4) for n > 4. -/
def H2 : Prop :=
  ∀ n : ℕ, 4 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a250882.main := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_oeis_a250882_R1

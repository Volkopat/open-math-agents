import OMAStatements.S_oeis_a330590
import Mathlib

-- Reduction oeis-a330590.R1 of step oeis-a330590
-- Credit: @Ciphore
-- The count equality splits into its two independent directions, which carry genuinely
-- different mathematics. The upper bound is the exclusion direction: every universal
-- divisor is squarefree (since `v_p(p^n - p) = 1` no prime square divides all values),
-- every prime factor `p` of a universal divisor must satisfy `(p - 1) ∣ n - 1` (the
-- multiplicative group mod `p` must have exponent dividing `n - 1`), and the count of
-- subset products is the size of the powerset. The lower bound is the construction
-- direction: every prime `p` with `(p - 1) ∣ n - 1` is universal (Fermat-Euler), coprime
-- products of universal divisors are universal (CRT), and distinct subsets give distinct
-- divisors.

namespace OMA.R_oeis_a330590_R1

open OMA.S_oeis_a330590

/-- The exclusion direction of the fixed-divisor count: the structural constraints on
    universal divisors bound the count by the size of the candidate powerset. -/
def H1 : Prop := ∀ n : ℕ, 2 ≤ n → T n 1 ≤ 2 ^ A067513 (n - 1)

/-- The construction direction of the fixed-divisor count: every candidate divisor is
    realized, so the count is at least the size of the powerset. -/
def H2 : Prop := ∀ n : ℕ, 2 ≤ n → 2 ^ A067513 (n - 1) ≤ T n 1

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a330590.main := by
  intro hup hlow n hn
  exact le_antisymm (hup n hn) (hlow n hn)

end OMA.R_oeis_a330590_R1

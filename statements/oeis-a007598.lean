import Mathlib

/-!
# OEIS A007598

The three Fibonacci reciprocal-series identities recorded by Peter Bala.
The family indexed by k was proved by Sela Fried in
https://oeis.org/A007598/a007598.pdf.
-/

open scoped BigOperators Topology
open Filter

namespace OMA.S_oeis_a007598

/-- The square of the Fibonacci number at index n. -/
def a (n : ℕ) : ℝ := (Nat.fib n : ℝ)^2

/-- The two fixed reciprocal sums and Bala's family of reciprocal sums. -/
theorem main :
    HasSum (fun i : ℕ => 1/(a (i+3) - 1/a (i+3))) (4/9 : ℝ) ∧
    HasSum (fun i : ℕ => (-1:ℝ)^(i+3)/(a (i+3) - 1/a (i+3)))
      (-(10 - 3 * Real.sqrt 5)/18) ∧
    (∀ k : ℕ, HasSum (fun i : ℕ => if i+1=2*k+1 then 0 else
      1/(a (i+1)+(-1:ℝ)^(i+1)*a (2*k+1))) (1/a (4*k+2))) := by
  sorry

end OMA.S_oeis_a007598

import Mathlib.NumberTheory.Divisors
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Three identities for the triangle A389524

Source: https://oeis.org/A389524
Credit: @blakestone-x

Row and column numbering begin at one. Only columns 1 through n contribute
to row n. Divisor counts, weighted reversed rows and doubled-row entries
are given independently of the conjectures.
-/

namespace OMA.S_oeis_a389524

def triangle (n k : ℕ) : ℤ :=
  if k = 0 then 0 else
  if k = 1 then (if n = 1 then 1 else 0) else
  if k ≤ n then
    1 + (∑ i : Fin (k - 1), triangle (n - (i.val + 1)) (k - 1)) -
    (∑ i : Fin (n - 1), triangle (i.val + 1) k)
  else 0
termination_by n
decreasing_by
  all_goals have := i.isLt
  all_goals omega

/-- Count the nonnegative quadruples in Nathanson's definition of A274628. -/
noncomputable def orphans (n : ℕ) : ℕ :=
  Nat.card {t : ℕ × ℕ × ℕ × ℕ //
    t.2.2.1 < t.1 ∧ t.2.2.2 < t.2.1 ∧ t.1*t.2.1 = n+t.2.2.1*t.2.2.2}

theorem main : ∀ n : ℕ, 0 < n →
    (∑ i ∈ Finset.range n, triangle n (i+1)) = (n.divisors.card : ℤ) ∧
    (∑ i ∈ Finset.range n, triangle n (n-i) * ((n-i : ℕ) : ℤ)) = (orphans n : ℤ) ∧
    triangle (2*n) n = (n : ℤ) - (n.divisors.card : ℤ) := by
  sorry

end OMA.S_oeis_a389524

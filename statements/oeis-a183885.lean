import Mathlib

/-!
# OEIS A183885: words in three residues

Source: https://oeis.org/A183885

A word of length n+3 uses the residues 0, 1, and 2. At every position its
value must be the sum modulo three of the values at three distinct other
positions. The sequence has offset one, so the generating series has
constant coefficient zero. The statement includes Kotesovec's empirical
formula and both conjectures in Barker's formula block.
-/

namespace OMA.S_oeis_a183885

/-- The three witness positions form a set and exclude the position being tested. -/
def Valid {N : ℕ} (w : Fin N → Fin 3) : Prop :=
  ∀ i : Fin N, ∃ t : Finset (Fin N), t.card = 3 ∧ i ∉ t ∧
    (∑ j ∈ t, (w j).val) % 3 = (w i).val

instance (N : ℕ) : DecidablePred (@Valid N) := fun w => by
  unfold Valid
  infer_instance

/-- The number of valid words of length n+3, with a zero constant term. -/
def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else ((Finset.univ.filter (@Valid (n + 3))).card : ℤ)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = 3^(n+3) - 2*((n : ℤ)+4)^2) ∧
    (PowerSeries.mk a * ((1 - X)^3 * (1 - 3*X)) =
      X * (1 + 115*X - 83*X^2 - 285*X^3 + 410*X^4 - 150*X^5)) ∧
    (∀ n : ℕ, 6 < n → a n = 6*a (n-1) - 12*a (n-2) + 10*a (n-3) - 3*a (n-4)) := by
  sorry

end OMA.S_oeis_a183885

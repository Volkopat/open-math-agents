import Mathlib

/-!
# A124698: Number of base 5 circular n-digit numbers with adjacent digits differing by 1 or less.

Source: https://oeis.org/A124698
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: (1 - 6*x^2 - 4*x^3 + 12*x^4) / ((1 - x)*(1 - 2*x)*(1 - 2*x - 2*x^2)).
* a(n) = 5*a(n-1) - 6*a(n-2) - 2*a(n-3) + 4*a(n-4) for n>4.

Conventions: 'n-digit numbers' are read as all digit strings of length n (leading zeros allowed), the reading that reproduces the OEIS data.
Offset 0: a(n) is the number of base-5 digit strings of length n (leading zeros allowed) whose cyclically adjacent digits (the last and the first included) differ by at most 1.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 26).
-/

namespace OMA.S_oeis_a124698

/-- The number of words `s : Fin n → Fin 5` (base-5 digit strings of length `n`, leading zeros
allowed) in which every two cyclically adjacent digits (including the last and the first) differ by
at most 1. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin n → Fin 5)).filter (fun s =>
    decide (∀ i : Fin n, Int.natAbs (((s i : ℕ) : ℤ) -
      ((s ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ : ℕ) : ℤ)) ≤ 1))).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 2 * X - 2 * X ^ 2) : PowerSeries ℚ) = 1 - 6 * X ^ 2 - 4 * X ^ 3 + 12 * X ^ 4) ∧
    (∀ n : ℕ, 5 ≤ n → (a n : ℚ) = 5 * a (n - 1) - 6 * a (n - 2) - 2 * a (n - 3) + 4 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a124698

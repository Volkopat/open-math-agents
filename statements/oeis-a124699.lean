import Mathlib

/-!
# A124699: Number of base 6 circular n-digit numbers with adjacent digits differing by 1 or less.

Source: https://oeis.org/A124699
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: (1 - 10*x^2 + 27*x^4 - 8*x^5 - 5*x^6) / ((1 - 2*x - x^2 + x^3)*(1 - 4*x + 3*x^2 + x^3)).
* a(n) = 6*a(n-1) - 10*a(n-2) + 9*a(n-4) - 2*a(n-5) - a(n-6) for n>6.

Conventions: 'n-digit numbers' are read as all digit strings of length n (leading zeros allowed), the reading that reproduces the OEIS data.
Offset 0: a(n) is the number of base-6 digit strings of length n (leading zeros allowed) whose cyclically adjacent digits (the last and the first included) differ by at most 1.
A brute-force count reproduces the listed terms for small n, and each formula was checked against every listed term (n up to 25).
-/

namespace OMA.S_oeis_a124699

/-- The number of words `s : Fin n → Fin 6` (base-6 digit strings of length `n`, leading zeros
allowed) in which every two cyclically adjacent digits (including the last and the first) differ by
at most 1. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin n → Fin 6)).filter (fun s =>
    decide (∀ i : Fin n, Int.natAbs (((s i : ℕ) : ℤ) -
      ((s ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ : ℕ) : ℤ)) ≤ 1))).card

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - 2 * X - X ^ 2 + X ^ 3) * (1 - 4 * X + 3 * X ^ 2 + X ^ 3) : PowerSeries ℚ) = 1 - 10 * X ^ 2 + 27 * X ^ 4 - 8 * X ^ 5 - 5 * X ^ 6) ∧
    (∀ n : ℕ, 7 ≤ n → (a n : ℚ) = 6 * a (n - 1) - 10 * a (n - 2) + 9 * a (n - 4) - 2 * a (n - 5) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a124699

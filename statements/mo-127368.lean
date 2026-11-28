import Mathlib

/-!
# Two products over primes

Source: https://mathoverflow.net/questions/127368 (CC BY-SA 4.0).

For `k ∈ ℕ` let `f(k) = ∏_p (1 + 1/(p^k (p^k + 1)))` and `g(k) = ∏_p (1 + 1/(p^k (p^k - 1)))`,
products over all primes. (By the product for ζ, `f(1) = ζ(2)/ζ(3)`.) Numerically (100 digits,
Cohen's PARI script) the asker found `f(2) = 21/(2π²)` and `g(1) = 315 ζ(3)/(2π⁴)`, and asks:
are these conjectured values correct? (The further request for "other closed forms" is open-ended
and not stated.)

We state the two conjectured values.

Formalization notes:
* The products are `tprod`s over the subtype `Nat.Primes`, in `ℝ`; both converge absolutely.
* `ζ(3)` is written as the real series `∑_{n ≥ 1} 1/n³`.
* Checked numerically (primes below `2·10^6`): `f(2) ≈ 1.0638724282`, `21/(2π²) ≈ 1.0638724282`;
  `g(1) ≈ 1.94359637`, `315 ζ(3)/(2π⁴) ≈ 1.94359644` (the gap is the truncation of the product).
-/

namespace OMA.S_mo_127368

/-- `f(2) = 21/(2π²)` and `g(1) = 315 ζ(3)/(2π⁴)`. -/
theorem main :
    (∏' p : Nat.Primes, (1 + 1 / ((p : ℝ) ^ 2 * ((p : ℝ) ^ 2 + 1)))) = 21 / (2 * Real.pi ^ 2) ∧
    (∏' p : Nat.Primes, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) =
      315 * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3) / (2 * Real.pi ^ 4) := by
  sorry

end OMA.S_mo_127368

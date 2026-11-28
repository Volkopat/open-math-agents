import Mathlib

/-!
# A103225: Gaussian integers coprime to n in the disc of radius n

Source: https://oeis.org/A103225
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of Gaussian integers `z` with `|z| < n` and `gcd(n, z) = 1`.
Conjecture (Bill McEachen, OEIS, 2025): `a(n) < π n²`.

## Encoding

* Gaussian integers are Mathlib's `GaussianInt` (`ℤ[i]`); `|z| < n` is `z.norm < n²`
  (`Zsqrtd.norm`), and `gcd(n, z) = 1` is `IsCoprime (n : ℤ[i]) z`.
* The statement is for all `n ≥ 1` (offset `1`).
-/

namespace OMA.S_oeis_a103225

/-- `a n`: Gaussian integers of absolute value `< n` coprime to `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {z : GaussianInt | z.norm < (n : ℤ) ^ 2 ∧ IsCoprime (n : GaussianInt) z}

theorem main : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) < Real.pi * n ^ 2 := by
  sorry

end OMA.S_oeis_a103225

import Mathlib

/-!
# OEIS A071256: smallest multiple of `n` between twin primes

Source: https://oeis.org/A071256
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest multiple `m` of `n` such that `m - 1` and `m + 1` are both prime.
Conjecture (OEIS entry): `limsup_{n → ∞} a(n)/n²` exists and equals some `C` with `0 < C < 1`.

Conventions:
* `a(n)` is the least `m ≥ 1` with `n ∣ m` and `m ± 1` prime (`0` if there is none, by
  `sInf ∅ = 0`); `n ≥ 1`.
* 'The lim sup exists' means `a(n)/n²` is bounded above (so `Filter.limsup` is meaningful);
  `main` states this together with `limsup = C` for some `0 < C < 1`.
-/

namespace OMA.S_oeis_a071256

open Filter

/-- Smallest multiple of `n` sandwiched between twin primes. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 1 ≤ m ∧ n ∣ m ∧ (m - 1).Prime ∧ (m + 1).Prime}

/-- `limsup a(n)/n²` is finite and lies in `(0, 1)`. -/
theorem main :
    IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (a n : ℝ) / (n : ℝ) ^ 2) ∧
    ∃ C : ℝ, 0 < C ∧ C < 1 ∧ limsup (fun n : ℕ => (a n : ℝ) / (n : ℝ) ^ 2) atTop = C := by
  sorry

end OMA.S_oeis_a071256

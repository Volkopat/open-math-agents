import Mathlib

/-!
# OEIS A048670 (Jacobsthal function of primorials): Maier–Pomerance conjecture

Source: https://oeis.org/A048670
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The entry records two conjectures. Jacobsthal's (`a(n) ≥ j(k)` for `k` with `n` prime factors)
is disproved (Hajdu–Saradha), so the open one is stated: Maier and Pomerance conjecture
`max_{n ≤ x} j(n) = log x · (log log x)^{2 + o(1)}`, where `j = A048669` is the Jacobsthal
function: the least `m` such that every `m` consecutive integers contain one coprime to `n`.

`(log log x)^{2 + o(1)}` is written: for every `ε > 0`, eventually
`log x (log log x)^{2 - ε} ≤ max_{n ≤ x} j(n) ≤ log x (log log x)^{2 + ε}`.
-/

namespace OMA.S_oeis_a048670

open Filter

/-- Jacobsthal function `j(n)` (A048669). -/
noncomputable def j (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ s : ℤ, ∃ i ∈ Finset.range m, IsCoprime (s + i) (n : ℤ)}

/-- `max_{1 ≤ n ≤ x} j(n)`. -/
noncomputable def M (x : ℝ) : ℕ := (Finset.Icc 1 ⌊x⌋₊).sup j

/-- Maier–Pomerance conjecture. -/
theorem main :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      Real.log x * Real.log (Real.log x) ^ (2 - ε) ≤ (M x : ℝ) ∧
      (M x : ℝ) ≤ Real.log x * Real.log (Real.log x) ^ (2 + ε) := by
  sorry

end OMA.S_oeis_a048670

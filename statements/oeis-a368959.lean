import Mathlib

/-!
# A368959: numbers m such that the exponential sums of s-th powers modulo m are all nonzero

Source: https://oeis.org/A368959 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A368959 (Vaclav Kotesovec, Jan 10 2024), offset 1: numbers m such that
Sum_{k=0..m-1} exp(2*Pi*i*k^s/m) <> 0 for all s>=2.
Data 1, 4, 8, 9, 25, 27, 36, 49, 72, 100, 108, 121, 125, 169, 196, 200, 216, 225, 243, 289, ...

Comments: Conjecture 1: This is a subset of A001694.
Conjecture 2: This sequence contains all the terms from A338325, plus 243, 972, 1944, 2401, ...

Formalization notes.
* A001694 is the sequence of the powerful numbers: the positive integers m such that p^2
  divides m for each prime p that divides m.
* `main` is Conjecture 1: if m >= 1 and the sum Sum_{k=0..m-1} exp(2 Pi i k^s / m) is not zero
  for each s >= 2, then m is powerful.
* Conjecture 2 is NOT stated here. It is open-ended: the list of additional terms
  243, 972, 1944, 2401, ... ends with an ellipsis and the entry gives no rule for it, so the
  conjecture has no exact mathematical content that a statement could capture.
-/

namespace OMA.S_oeis_a368959

/-- Conjecture 1 of Kotesovec: each term of A368959 is a powerful number (A001694). -/
theorem main : ∀ m : ℕ, 1 ≤ m →
    (∀ s : ℕ, 2 ≤ s →
      ∑ k ∈ Finset.range m,
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) ^ s / (m : ℂ)) ≠ 0) →
    ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m := by
  sorry

end OMA.S_oeis_a368959

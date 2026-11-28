import Mathlib

/-!
# 3-accessibility of Fibonacci numbers

Source: https://www.openproblemgarden.org/op/3_accessibility_of_fibonacci_numbers
Credit: @shc261392

The source (Landman and Robertson): is the set of Fibonacci numbers 3-accessible? A set `S` is
`r`-accessible if for any `r`-colouring of `ℕ` there exist long monochromatic `S`-diffsequences,
i.e. for any `k ∈ ℕ \ {1}` there is a monochromatic sequence `x₁, x₂, …, x_k` such that
`x_{i+1} - x_i ∈ S` for all `i ∈ {1, 2, …, k - 1}`. The source notes that the Fibonacci numbers
are 2-accessible and not 6-accessible.

This file states the question in its affirmative form: a proof of `main` answers it yes, a proof
of `¬ main` answers it no.

Reading used here:
* `ℕ` in the source is the positive integers: the colouring is of `{1, 2, …}`, and the terms of
  the sequence are positive integers.
* The Fibonacci numbers are `F = {1, 2, 3, 5, 8, …}`, i.e. `Nat.fib m` for `m ≥ 1` (Mathlib's
  `Nat.fib 0 = 0` is left out: a difference `0` would make constant sequences count, and the
  notion would be trivial).
* "for any `k ∈ ℕ \ {1}`" is read as every `k ≥ 2`; the sequence is indexed by `Fin k`.
* An `r`-colouring of the positive integers is a map `ℕ → Fin r` (its value at `0` is ignored).
-/

namespace OMA.S_opg_3_accessibility_of_fibonacci_numbers

/-- The set of Fibonacci numbers `{1, 2, 3, 5, 8, …}`. -/
def fibSet : Set ℕ := {d | ∃ m : ℕ, 1 ≤ m ∧ Nat.fib m = d}

theorem main :
    ∀ col : ℕ → Fin 3, ∀ k : ℕ, 2 ≤ k →
      ∃ x : Fin k → ℕ, (∀ i, 1 ≤ x i) ∧ (∀ i j, col (x i) = col (x j)) ∧
        ∀ i : Fin k, ∀ h : i.val + 1 < k,
          x i < x ⟨i.val + 1, h⟩ ∧ x ⟨i.val + 1, h⟩ - x i ∈ fibSet := by
  sorry

end OMA.S_opg_3_accessibility_of_fibonacci_numbers

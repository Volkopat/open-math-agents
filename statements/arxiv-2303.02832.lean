import Mathlib

/-!
# Iterated harmonic numbers are not integers

Source: arXiv:2303.02832, "Iterated harmonic numbers", Conjecture 3.
Credit: @jagraj28

The harmonic numbers are `h₁(n) = ∑_{k=1}^n 1/k`. For `j ≥ 2` the paper defines the `j`th
iterated harmonic numbers by
  `h_j(n) = ∑_{k=1}^n 1 / (k · h₁(k) · h₂(k) ⋯ h_{j-1}(k))`,
so `h₂(n) = ∑_{k=1}^n 1/(k h₁(k))`, and so on (Section 2). Property 5 of the paper (classical) says
that the only integer harmonic number is `h₁(1) = 1`, and the paper states:

  Conjecture 3. For each integer `j ≥ 2`, the only `j`th iterated harmonic number that is an
  integer is `h_j(1)`.

Conventions.
* `P j k = h₁(k) ⋯ h_j(k)` (with `P 0 k = 1`) is defined by recursion on `j`, using
  `h_{j+1}(k) = ∑_{m=1}^k 1/(m · P j m)`; then `h j n = ∑_{k=1}^n 1/(k · P (j-1) k)` for
  `j ≥ 1`. All values are in `ℚ`. This gives `h 2 2 = 4/3`, `h 2 3 = 50/33`.
* The iterated harmonic numbers are indexed by `n ≥ 1` (the empty sum `h j 0 = 0` is not one of
  them), so the conjecture says that `h j n` is not an integer for `j ≥ 2` and `n ≥ 2`.
* A computation with exact fractions confirms this for `j ∈ {2, 3, 4}` and `n ≤ 60`.
-/

namespace OMA.S_arxiv_2303_02832

/-- `P j k = h₁(k) · h₂(k) ⋯ h_j(k)`, with `P 0 k = 1`. -/
def P : ℕ → ℕ → ℚ
  | 0, _ => 1
  | j + 1, k => P j k * ∑ m ∈ Finset.Icc 1 k, 1 / ((m : ℚ) * P j m)

/-- The `j`th iterated harmonic number `h_j(n) = ∑_{k=1}^n 1/(k h₁(k) ⋯ h_{j-1}(k))`. -/
def h (j n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n, 1 / ((k : ℚ) * P (j - 1) k)

/-- Conjecture 3: for `j ≥ 2`, `h_j(n)` is an integer only for `n = 1`. -/
theorem main : ∀ j : ℕ, 2 ≤ j → ∀ n : ℕ, 2 ≤ n → ¬ ∃ z : ℤ, h j n = z := by
  sorry

end OMA.S_arxiv_2303_02832

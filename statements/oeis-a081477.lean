import Mathlib

/-!
# A081477: Complement of A086377.

Source: https://oeis.org/A081477
Credit: @gblacher2

Conjectures (formula section of A081477, Clark Kimberling, Aug 03 2022):
"[a(n)*r] = n + [n*r] for n >= 1, where r = sqrt(2) and [ ] = floor.
{a(n)*sqrt(2)} > 1/2 if n is in A120753, where { } = fractional part; otherwise n is in A120752."

A086377 (https://oeis.org/A086377), offset 1, is defined in its name by a self-referential rule
(a(1) = 1; a(n) = a(n-1) + 2 or a(n-1) + 3 depending on whether n and n-1 are terms). Its formula
section gives the closed form a(n) = floor((1+sqrt(2))*n - 1/sqrt(2)), and the comments there
note that the conjectures of Biberstine, Hanna and Kimberling about it were proved by Bosma,
Dekking and Steiner. We use this closed form. A081477 (offset 1) lists, in increasing order, the
positive integers that are not terms of A086377: 2, 3, 5, 7, 9, 10, ...

A120752 and A120753 (https://oeis.org/A120752, https://oeis.org/A120753) are the numbers `k ≥ 1`
with `{r*k} <= 1/2` and `{r*k} > 1/2`, respectively, where `r = (1/2)^(1/2)`; they split the
positive integers in two. We read the second conjecture as: `{a(n)*sqrt(2)} > 1/2` when `n` is in
A120753, and `{a(n)*sqrt(2)} <= 1/2` when `n` is in A120752 (the "otherwise" case).
-/

namespace OMA.S_oeis_a081477

/-- A086377(m) for `m ≥ 1`: `floor((1 + sqrt 2) * m - 1 / sqrt 2)`. -/
noncomputable def a086377 (m : ℕ) : ℤ := ⌊(1 + Real.sqrt 2) * m - 1 / Real.sqrt 2⌋

/-- `k` is a term of A081477: a positive integer that is not a term of A086377. -/
def IsA081477 (k : ℕ) : Prop := 0 < k ∧ ∀ m : ℕ, 1 ≤ m → a086377 m ≠ (k : ℤ)

/-- A081477(n) for `n ≥ 1`: the `n`-th term, in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsA081477 (n - 1)

/-- `k` is a term of A120752: `k ≥ 1` and `{(1/2)^(1/2) * k} ≤ 1/2`. -/
def IsA120752 (k : ℕ) : Prop := 1 ≤ k ∧ Int.fract (Real.sqrt (1 / 2) * k) ≤ 1 / 2

/-- `k` is a term of A120753: `k ≥ 1` and `{(1/2)^(1/2) * k} > 1/2`. -/
def IsA120753 (k : ℕ) : Prop := 1 ≤ k ∧ 1 / 2 < Int.fract (Real.sqrt (1 / 2) * k)

/-- Kimberling's two conjectures on A081477. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ⌊(a n : ℝ) * Real.sqrt 2⌋ = n + ⌊(n : ℝ) * Real.sqrt 2⌋ ∧
    (IsA120753 n → 1 / 2 < Int.fract ((a n : ℝ) * Real.sqrt 2)) ∧
    (IsA120752 n → Int.fract ((a n : ℝ) * Real.sqrt 2) ≤ 1 / 2) := by
  sorry

end OMA.S_oeis_a081477

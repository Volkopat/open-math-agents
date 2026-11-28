import Mathlib

/-!
# A319674: a(n) = 1 + 2 + 3 - 4 - 5 - 6 + 7 + 8 + 9 - 10 - 11 - 12 + ... - (up to n)

Source: https://oeis.org/A319674
Credit: @jagong-cmu

Formalizes Bill McEachen's OEIS A319674 conjectures (Dec 19 2024), offset 1:
`For a(n)>0 and n=A047235(m), a(n) = n/2 + 2*Mod(m,2), otherwise a(n) = 3*(n+1)/2.`
`For a(n)<0 and n=A007310(m), a(n)= 1 + (1-n)/2 + 2*(Mod(m,2)-1), otherwise a(n) = -3*n/2.`

Conventions:
* `a n` is the OEIS formula `a(n) = Sum_{i=1..n} i*(-1)^floor((i-1)/3)`, in `ℤ`
  (`(i-1)/3` is floor division on `ℕ`, exact subtraction for `i >= 1`).
* `A047235 m` is the `m`-th number congruent to 2 or 4 mod 6, and `A007310 m` is the `m`-th
  number congruent to 1 or 5 mod 6, both with offset 1 (so `A047235 1 = 2`, `A007310 1 = 1`).
  They use `Nat.nth`, which counts from 0, so the index is `m - 1`, and only `m >= 1` is used.
* `Mod(m,2)` is `m % 2`. All right-hand sides are computed in `ℚ`, so the halves are exact.
* `otherwise` means: `n` is not a term of the named sequence.
* Range: the claims fail at `n = 1`: `a(1) = 1 > 0`, `1` is not in A047235, and
  `3*(1+1)/2 = 3`. Python checks find no other failure for `n < 1500`, so the claims are
  stated for every `n >= 2`.
-/

namespace OMA.S_oeis_a319674

/-- `a(n) = Sum_{i=1..n} i*(-1)^floor((i-1)/3)`. -/
def a (n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, (i : ℤ) * (-1) ^ ((i - 1) / 3)

/-- A047235: numbers congruent to `{2, 4}` mod 6, offset 1. -/
noncomputable def A047235 (m : ℕ) : ℕ := Nat.nth (fun k => k % 6 = 2 ∨ k % 6 = 4) (m - 1)

/-- A007310: numbers congruent to 1 or 5 mod 6, offset 1. -/
noncomputable def A007310 (m : ℕ) : ℕ := Nat.nth (fun k => k % 6 = 1 ∨ k % 6 = 5) (m - 1)

/-- Both conjectures, for every `n >= 2`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (0 < a n →
        (∀ m : ℕ, 1 ≤ m → A047235 m = n →
            (a n : ℚ) = (n : ℚ) / 2 + 2 * ((m % 2 : ℕ) : ℚ)) ∧
        ((∀ m : ℕ, 1 ≤ m → A047235 m ≠ n) → (a n : ℚ) = 3 * ((n : ℚ) + 1) / 2)) ∧
      (a n < 0 →
        (∀ m : ℕ, 1 ≤ m → A007310 m = n →
            (a n : ℚ) = 1 + (1 - (n : ℚ)) / 2 + 2 * (((m % 2 : ℕ) : ℚ) - 1)) ∧
        ((∀ m : ℕ, 1 ≤ m → A007310 m ≠ n) → (a n : ℚ) = -3 * (n : ℚ) / 2)) := by
  sorry

end OMA.S_oeis_a319674

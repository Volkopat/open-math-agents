import Mathlib

/-!
# OEIS A359914: `2 = ∑_{n=-∞}^∞ (-1)^n * x^(n*(3*n-1)/2) * A(x)^(3*n) * (1 + x^n * A(x))`

Source: https://oeis.org/A359914 (OEIS Foundation, CC BY-SA 4.0).
Splitting the bilateral sum into `n = 0` (`1 + A(x)`), `n = m ≥ 1`, and `n = -m` (`m ≥ 1`),
the equation is
`2 = 1 + A(x) + ∑_{m ≥ 1} (-1)^m * (X^(m*(3*m-1)/2) * (A^(3*m) + invA^(3*m-1)) + X^(m*(3*m+1)/2) * (A^(3*m+1) + invA^(3*m)))`,
where `invA = 1 / A = ∑_{j ≥ 0} (1 - A)^j`.

Conjectures (Paul D. Hanna, OEIS A359914):
1. For every `n ≥ 1`, `a(n)` is even and `a(n) / 2 ≡ A000041(n) (mod 2)` (partition function `p(n)`).
2. For every `n ≥ 1`, `a(n) ≡ A361552(n + 1) (mod 4)`.
-/

namespace OMA.S_oeis_a359914

/-- Formal inverse `1 / A = ∑_{j ≥ 0} (1 - A)^j` for a power series `A` with `A.coeff 0 = 1`. -/
noncomputable def invOfUnit (A : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => ∑ j ∈ Finset.range (k + 1), ((1 - A) ^ j).coeff k

/-- The `m`-th paired summand for OEIS A359914 (`m ≥ 1`). -/
noncomputable def term359914 (A : PowerSeries ℤ) (m : ℕ) : PowerSeries ℤ :=
  (-1 : PowerSeries ℤ) ^ m *
    (PowerSeries.X ^ (m * (3 * m - 1) / 2) * (A ^ (3 * m) + (invOfUnit A) ^ (3 * m - 1)) +
     PowerSeries.X ^ (m * (3 * m + 1) / 2) * (A ^ (3 * m + 1) + (invOfUnit A) ^ (3 * m)))

/-- Functional equation for OEIS A359914 (`A(0) = 1`).
For coefficient `k`, every `term359914 A m` with `m > k` has `m*(3*m - 1)/2 ≥ m > k` and vanishes. -/
def SatisfiesA359914 (A : PowerSeries ℤ) : Prop :=
  A.coeff 0 = 1 ∧
  ∀ k : ℕ, 1 ≤ k → A.coeff k + ∑ m ∈ Finset.Icc 1 k, (term359914 A m).coeff k = 0

/-- The `m`-th paired summand for OEIS A361552 (`m ≥ 1`). -/
noncomputable def term361552 (C : PowerSeries ℤ) (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ (m * (3 * m + 1) / 2) * (C ^ (3 * m) - (invOfUnit C) ^ (3 * m + 1)) +
  PowerSeries.X ^ (m * (3 * m - 1) / 2) * ((invOfUnit C) ^ (3 * m) - C ^ (3 * m - 1))

/-- Functional equation for OEIS A361552 (`C(0) = 1`):
`2*x = (1 - 1/C) + ∑_{m ≥ 1} (x^(m*(3*m+1)/2) * (C^(3*m) - 1/C^(3*m+1)) + x^(m*(3*m-1)/2) * (1/C^(3*m) - C^(3*m-1)))`. -/
def SatisfiesA361552 (C : PowerSeries ℤ) : Prop :=
  C.coeff 0 = 1 ∧
  ∀ k : ℕ, 1 ≤ k →
    -(invOfUnit C).coeff k + ∑ m ∈ Finset.Icc 1 k, (term361552 C m).coeff k =
      if k = 1 then 2 else 0

/-- OEIS A000041: number of integer partitions of `n`. -/
noncomputable def A000041 (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- Conjectures (OEIS A359914):
There exist formal power series `A` satisfying A359914 and `C` satisfying A361552, and for
every such `A` and `C`, for all `n ≥ 1`:
1. `2 ∣ A.coeff n` and `(A.coeff n / 2) % 2 = (A000041 n : ℤ) % 2`,
2. `A.coeff n ≡ C.coeff (n + 1) [ZMOD 4]`. -/
theorem main :
    (∃ A : PowerSeries ℤ, SatisfiesA359914 A) ∧
    (∃ C : PowerSeries ℤ, SatisfiesA361552 C) ∧
    (∀ A C : PowerSeries ℤ, SatisfiesA359914 A → SatisfiesA361552 C →
      ∀ n : ℕ, 1 ≤ n →
        (2 : ℤ) ∣ A.coeff n ∧
        (A.coeff n / 2) % 2 = ((A000041 n : ℤ) % 2) ∧
        A.coeff n ≡ C.coeff (n + 1) [ZMOD 4]) := by
  sorry

end OMA.S_oeis_a359914

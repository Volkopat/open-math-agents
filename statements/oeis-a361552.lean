import Mathlib

/-!
# OEIS A361552: `2*x = ∑_{n=-∞}^∞ x^(n*(3*n+1)/2) * (A(x)^(3*n) - 1/A(x)^(3*n+1))`

Source: https://oeis.org/A361552 (OEIS Foundation, CC BY-SA 4.0).
Splitting the bilateral sum into `n = 0` (`1 - 1/A(x)`), `n = m ≥ 1`, and `n = -m` (`m ≥ 1`),
the equation is
`2*x = (1 - 1/A) + ∑_{m ≥ 1} (x^(m*(3*m+1)/2) * (A^(3*m) - 1/A^(3*m+1)) + x^(m*(3*m-1)/2) * (1/A^(3*m) - A^(3*m-1)))`.

Conjectures (Paul D. Hanna, OEIS A361552):
1. For every `n ≥ 1`, `a(n)` is even and `a(n) / 2 ≡ A000041(n - 1) (mod 2)`.
2. For every `n > 1`, `a(n) ≡ A359914(n - 1) (mod 4)`.
-/

namespace OMA.S_oeis_a361552

/-- Formal inverse `1 / A = ∑_{j ≥ 0} (1 - A)^j` for a power series `A` with `A.coeff 0 = 1`. -/
noncomputable def invOfUnit (A : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => ∑ j ∈ Finset.range (k + 1), ((1 - A) ^ j).coeff k

/-- The `m`-th paired summand for OEIS A361552 (`m ≥ 1`). -/
noncomputable def term361552 (A : PowerSeries ℤ) (m : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ (m * (3 * m + 1) / 2) * (A ^ (3 * m) - (invOfUnit A) ^ (3 * m + 1)) +
  PowerSeries.X ^ (m * (3 * m - 1) / 2) * ((invOfUnit A) ^ (3 * m) - A ^ (3 * m - 1))

/-- Functional equation for OEIS A361552 (`A(0) = 1`). -/
def SatisfiesA361552 (A : PowerSeries ℤ) : Prop :=
  A.coeff 0 = 1 ∧
  ∀ k : ℕ, 1 ≤ k →
    -(invOfUnit A).coeff k + ∑ m ∈ Finset.Icc 1 k, (term361552 A m).coeff k =
      if k = 1 then 2 else 0

/-- The `m`-th paired summand for OEIS A359914 (`m ≥ 1`). -/
noncomputable def term359914 (B : PowerSeries ℤ) (m : ℕ) : PowerSeries ℤ :=
  (-1 : PowerSeries ℤ) ^ m *
    (PowerSeries.X ^ (m * (3 * m - 1) / 2) * (B ^ (3 * m) + (invOfUnit B) ^ (3 * m - 1)) +
     PowerSeries.X ^ (m * (3 * m + 1) / 2) * (B ^ (3 * m + 1) + (invOfUnit B) ^ (3 * m)))

/-- Functional equation for OEIS A359914 (`B(0) = 1`). -/
def SatisfiesA359914 (B : PowerSeries ℤ) : Prop :=
  B.coeff 0 = 1 ∧
  ∀ k : ℕ, 1 ≤ k → B.coeff k + ∑ m ∈ Finset.Icc 1 k, (term359914 B m).coeff k = 0

/-- OEIS A000041: number of integer partitions of `n`. -/
noncomputable def A000041 (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- Conjectures (OEIS A361552):
There exist formal power series `A` satisfying A361552 and `B` satisfying A359914, and for
every such `A` and `B`:
1. For all `n ≥ 1`, `2 ∣ A.coeff n` and `(A.coeff n / 2) % 2 = (A000041 (n - 1) : ℤ) % 2`.
2. For all `n > 1`, `A.coeff n ≡ B.coeff (n - 1) [ZMOD 4]`. -/
theorem main :
    (∃ A : PowerSeries ℤ, SatisfiesA361552 A) ∧
    (∃ B : PowerSeries ℤ, SatisfiesA359914 B) ∧
    (∀ A B : PowerSeries ℤ, SatisfiesA361552 A → SatisfiesA359914 B →
      (∀ n : ℕ, 1 ≤ n →
        (2 : ℤ) ∣ A.coeff n ∧
        (A.coeff n / 2) % 2 = ((A000041 (n - 1) : ℤ) % 2)) ∧
      (∀ n : ℕ, 1 < n → A.coeff n ≡ B.coeff (n - 1) [ZMOD 4])) := by
  sorry

end OMA.S_oeis_a361552

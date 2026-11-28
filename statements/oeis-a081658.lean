import Mathlib

/-!
# A081658: Triangle T(n, k) = (-2)^k * binomial(n, k) * Euler(k, 1/2).

Source: https://oeis.org/A081658
Credit: @cjchaffin

Conjecture (stated on the OEIS page by Peter Luschny, Jun 05 2023): if `n` is prime then
`n` divides `T(n, k)` for `1 ≤ k ≤ n-1`.

Conventions:
- The triangle has offset 0, with `0 ≤ k ≤ n`. The displayed formula is the sequence name.
  The Mathematica program on the same page writes the equivalent integer form
  `T(n, k) = binomial(n, k) * EulerE[k]`, where `EulerE` is the sequence of Euler numbers
  with `EulerE[0] = 1`, `EulerE[odd] = 0`, `EulerE[2] = -1`, `EulerE[4] = 5`,
  `EulerE[6] = -61`, … (OEIS A122045 / Mathematica `EulerE`). This is the convention in
  which `(-2)^k * Euler(k, 1/2) = EulerE[k]`.
- Those Euler numbers are defined by `E_0 = 1` and, for `m ≥ 1`,
  `∑_{j=0}^{m} binomial(2m, 2j) * E_{2j} = 0`, with odd-index terms zero. The even-index
  values are computed from that recurrence below.
- The entries may be negative, so divisibility is in `ℤ`.
-/

namespace OMA.S_oeis_a081658

/-- Prefixes of the even-index Euler numbers: `eulerEEvenList m` is
`[E_0, E_2, …, E_{2m}]`. -/
def eulerEEvenList : ℕ → List ℤ
  | 0 => [1]
  | m + 1 =>
    let prev := eulerEEvenList m
    let v :=
      -∑ j ∈ Finset.range (m + 1),
        ((2 * (m + 1)).choose (2 * j) : ℤ) * prev.getD j 0
    prev ++ [v]

/-- Even-index Euler numbers: `eulerEEven m = EulerE[2m]`. -/
def eulerEEven (m : ℕ) : ℤ := (eulerEEvenList m).getD m 0

/-- The Euler numbers `EulerE[n]` (A122045 / Mathematica `EulerE`). -/
def eulerE (n : ℕ) : ℤ := if n % 2 = 1 then 0 else eulerEEven (n / 2)

/-- The triangle `T(n, k) = binomial(n, k) * EulerE[k]`. -/
def T (n k : ℕ) : ℤ := (n.choose k : ℤ) * eulerE k

theorem main : ∀ n k : ℕ, n.Prime → 1 ≤ k → k ≤ n - 1 → (n : ℤ) ∣ T n k := by
  sorry

end OMA.S_oeis_a081658

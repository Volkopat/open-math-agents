import Mathlib

/-!
# OEIS A237048: column `k` lists 1's interleaved with `k - 1` zeros

Source: https://oeis.org/A237048 (OEIS Foundation, CC BY-SA 4.0).

Irregular triangle read by rows: `T(n, k)`, `n ≥ 1`, `k ≥ 1`, in which column `k` lists 1's
interleaved with `k - 1` zeros, and the first element of column `k` is in row `k(k+1)/2`.
So `T(n, k) = 1` when `k(k+1)/2 ≤ n` and `k` divides `n - k(k+1)/2`, and `T(n, k) = 0`
otherwise (Hartmut F. W. Hoft's formula in the entry). Row `n` has length
A003056(n) = floor((sqrt(8n+1) - 1)/2), the largest `k` with `k(k+1)/2 ≤ n`.
The data begins `1; 1; 1, 1; 1, 0; 1, 1; 1, 0, 1; 1, 1, 0; ...`.

Conjectures (Omar E. Pol, comments of the entry, 2017):
* Conjecture 1: the alternating sum of row `n` gives A067742(n), the number of middle divisors of
  `n`, i.e. divisors in the half-open interval `[sqrt(n/2), sqrt(n*2))`.
* Conjecture 3: the sum of the odd-indexed terms of row `n` gives A082647(n), the number of ways
  `n` is the sum of `d` consecutive positive integers where `d > 0` is a divisor of `n`.
* Conjecture 4: the sum of the even-indexed terms of row `n` gives A131576(n), the number of ways
  to write `n` as a sum of an even number of consecutive positive integers.
* Conjecture 6: `T(n, k)` is the number of partitions of `n` into exactly `k` consecutive parts.

Formalization notes:
* Conjectures 2 and 5 are about the symmetric representation of sigma(n); they are not stated here.
* A representation of `n` as a sum of `j` consecutive positive integers is a pair `(s, j)` with
  `s, j ≥ 1` and `s + (s + 1) + ... + (s + j - 1) = n`; both `s` and `j` are then at most `n`.
  A partition of `n` into exactly `k` consecutive parts is such a pair with `j = k`.
* The alternating sum `Σ_{k=1..A003056(n)} (-1)^(k-1) T(n, k)` is taken in `ℤ`.
* All four are stated for every `n ≥ 1`, Conjecture 6 for every `k` in row `n`.
-/

namespace OMA.S_oeis_a237048

/-- A003056(n): the largest `k` with `k(k+1)/2 ≤ n`, the length of row `n`. -/
def A003056 (n : ℕ) : ℕ := Nat.findGreatest (fun k => k * (k + 1) / 2 ≤ n) n

/-- A237048: `T(n, k) = 1` if `k(k+1)/2 ≤ n` and `k ∣ n - k(k+1)/2`, otherwise `0`. -/
def T (n k : ℕ) : ℕ := if k * (k + 1) / 2 ≤ n ∧ k ∣ n - k * (k + 1) / 2 then 1 else 0

/-- Pairs `(s, j)` with `s, j ≥ 1` and `s + (s + 1) + ... + (s + j - 1) = n`. -/
def reps (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p => ∑ i ∈ Finset.range p.2, (p.1 + i) = n)

open Classical in
/-- A067742(n): the number of divisors of `n` in the half-open interval `[sqrt(n/2), sqrt(n*2))`. -/
noncomputable def A067742 (n : ℕ) : ℕ :=
  (n.divisors.filter
    (fun d : ℕ => Real.sqrt ((n : ℝ) / 2) ≤ (d : ℝ) ∧ (d : ℝ) < Real.sqrt ((n : ℝ) * 2))).card

/-- A082647(n): the number of ways `n` is the sum of `d` consecutive positive integers where
`d > 0` is a divisor of `n`. -/
def A082647 (n : ℕ) : ℕ := ((reps n).filter (fun p => p.2 ∣ n)).card

/-- A131576(n): the number of ways to write `n` as a sum of an even number of consecutive positive
integers. -/
def A131576 (n : ℕ) : ℕ := ((reps n).filter (fun p => Even p.2)).card

/-- Pol's Conjectures 1, 3, 4 and 6. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (∑ k ∈ Finset.Icc 1 (A003056 n), (-1 : ℤ) ^ (k - 1) * (T n k : ℤ)) = (A067742 n : ℤ) ∧
    (∑ k ∈ (Finset.Icc 1 (A003056 n)).filter Odd, T n k) = A082647 n ∧
    (∑ k ∈ (Finset.Icc 1 (A003056 n)).filter Even, T n k) = A131576 n ∧
    ∀ k ∈ Finset.Icc 1 (A003056 n), T n k = ((reps n).filter (fun p => p.2 = k)).card := by
  sorry

end OMA.S_oeis_a237048

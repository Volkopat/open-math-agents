import Mathlib

/-!
# A397048: Triangle T(n, k) read by rows: T(n, k) = (Sum_{i=0..k} (-1)^i * binomial(k, i) * (n+i)^n) * (-1)^k / k! for 0 <= k <= n.

Source: https://oeis.org/A397048
Credit: @agchua

Formula lines of A397048 (unsigned; the entry is by Werner Schulte, Jun 14 2026):
  Conjecture 1: T(n, k) = Sum_{i=0..n-k} A048994(n, k+i) * A048993(n+k+i, n+k).
  Conjecture 2: Row sums are A134980(n).
  Conjecture 3: Sum_{i=0..k} T(n, i) * k! / (k-i)! = (n + k)^n.
The triangle has offset 0 and rows 0 <= k <= n. `T n k` is the entry's formula, evaluated in ℚ
(the division by k! is exact). `main` states the three conjectures together: Conjectures 1 and 3
for every row n and every 0 <= k <= n, Conjecture 2 for every n >= 0 (A134980 has offset 0).
In Conjecture 1 the index i runs over 0..n-k, so every A048994 index (n, k+i) and every A048993
index (n+k+i, n+k) lies inside its triangle.

The referenced sequences, each with offset 0:
* A048994 (triangle of signed Stirling numbers of the first kind s(n, k), 0 <= k <= n) is `s`,
  defined by that entry's recurrence s(n, k) = s(n-1, k-1) - (n-1)*s(n-1, k), n, k >= 1;
  s(n, 0) = s(0, k) = 0; s(0, 0) = 1. (Mathlib's `Nat.stirlingFirst` is the unsigned version.)
* A048993 (triangle of Stirling numbers of the second kind S(n, k), 0 <= k <= n) is Mathlib's
  `Nat.stirlingSecond`, which is defined by exactly that entry's recurrence
  S(n, k) = k*S(n-1, k) + S(n-1, k-1), n > 0; S(0, k) = 0, k > 0; S(0, 0) = 1
  (with S(n, 0) = 0 for n > 0).
* A000110 (Bell numbers, used by A134980) is Mathlib's `Nat.bell`, defined by bell(0) = 1 and
  bell(n+1) = Sum_{i=0..n} binomial(n, i) * bell(n-i); with k = n-i this is A000110's recurrence
  a(n+1) = Sum_{k=0..n} a(k)*binomial(n, k).
* A134980 is `a134980`, by that entry's definition a(n) = Sum_{k=0..n} binomial(n,k)*n^(n-k)*A000110(k).
-/

namespace OMA.S_oeis_a397048

/-- T(n, k) = (Sum_{i=0..k} (-1)^i binomial(k, i) (n+i)^n) (-1)^k / k!. -/
def T (n k : ℕ) : ℚ :=
  (∑ i ∈ Finset.range (k + 1), (-1 : ℚ) ^ i * (k.choose i : ℚ) * ((n : ℚ) + i) ^ n) *
    (-1) ^ k / (k.factorial : ℚ)

/-- A048994: the signed Stirling numbers of the first kind s(n, k), by the entry's recurrence. -/
def s : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => s n k - (n : ℤ) * s n (k + 1)

/-- A134980: a(n) = Sum_{k=0..n} binomial(n, k) n^(n-k) A000110(k), with A000110 = `Nat.bell`. -/
def a134980 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k * n ^ (n - k) * Nat.bell k

/-- Conjectures 1, 2 and 3 of A397048, together. -/
theorem main :
    (∀ n k : ℕ, k ≤ n →
      T n k = ∑ i ∈ Finset.range (n - k + 1),
        (s n (k + i) : ℚ) * (Nat.stirlingSecond (n + k + i) (n + k) : ℚ)) ∧
    (∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), T n k = (a134980 n : ℚ)) ∧
    (∀ n k : ℕ, k ≤ n →
      ∑ i ∈ Finset.range (k + 1), T n i * (k.factorial : ℚ) / ((k - i).factorial : ℚ) =
        ((n : ℚ) + k) ^ n) := by
  sorry

end OMA.S_oeis_a397048

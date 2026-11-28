import Mathlib

/-!
# A309229: column sums of A191898, and two conjectures of Mats Granvik

Source: https://oeis.org/A309229
Credit: @avivorly

A309229 (%N): Square array read by upwards antidiagonals: T(n,k) = Sum_{i=1..n} A191898(i,k).

Claims (Mats Granvik, Apr 14 2021, in the entry, verbatim):
- Conjecture 1: For n>1: max(T(1..n,n)) + min(T(1..n,n)) = 2*mean(T(1..n,n)) = -A023900(n).
- Conjecture 2: The Prime Number Theorem should imply: mean(T(n,1..n!)) = 1.

Conventions:
- `g m` is A023900(m) = Sum_{d | m} mu(d)*d, the function `f` of the A309229 %t program
  (`f[n_] := DivisorSum[n, MoebiusMu[#] # &]`), with `ArithmeticFunction.moebius` for mu.
- A191898 is taken in the closed form of its %F line `T(n, k) = A023900(gcd(n,k))` (Mats Granvik, Jun 18 2012),
  which is the form the A309229 %t program uses (it accumulates `f[GCD[n, k]]` over the rows `n`). The A309229 %e
  table agrees: its column 6 is 1, 0, -2, -3, -2, 0 and its column 10 is 1, 0, 1, 0, -4, -5, -4, -5, -4, 0, and
  both columns, and the first 15 %S terms read by upwards antidiagonals, were checked against these definitions.
- `T n k` is the entry `T(n,k)`: row `n` (the number of rows of A191898 summed), column `k`; `n, k ≥ 1`.
- Conjecture 1: `T(1..n,n)` is the list `T(1,n), ..., T(n,n)` (column `n`, rows `1..n`). Its max and min are
  `Finset.sup'` and `Finset.inf'` of `i ↦ T i n` over `i ∈ [1, n]`, and its mean is `(Sum_{i=1..n} T(i,n)) / n`,
  computed in `ℚ`. The chained equation `max + min = 2*mean = -A023900(n)` is stated as the two equations
  `max + min = -A023900(n)` and `2*mean = -A023900(n)`, for every `n > 1`.
- Conjecture 2: `T(n,1..n!)` is the list `T(n,1), ..., T(n,n!)` (row `n`, columns `1..n!`); its mean is
  `(Sum_{k=1..n!} T(n,k)) / n!` in `ℚ`. The phrase about the Prime Number Theorem gives the proposer's motivation,
  not a hypothesis: the claimed identity `mean = 1` is stated for every `n ≥ 1`, with no extra assumption.
-/

namespace OMA.S_oeis_a309229

/-- A023900: `g m = Sum_{d ∣ m} μ(d) d`. -/
def g (m : ℕ) : ℤ := ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℤ) * d

/-- A191898 in the closed form `A191898(i, k) = A023900(gcd(i, k))` (Granvik, 2012). -/
def A191898 (i k : ℕ) : ℤ := g (Nat.gcd i k)

/-- A309229: `T(n, k) = Sum_{i=1..n} A191898(i, k)`. -/
def T (n k : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, A191898 i k

theorem main :
    (∀ n : ℕ, ∀ hn : 1 < n,
      ((Finset.Icc 1 n).sup' (Finset.nonempty_Icc.mpr hn.le) (fun i => T i n) +
          (Finset.Icc 1 n).inf' (Finset.nonempty_Icc.mpr hn.le) (fun i => T i n) = -g n) ∧
        2 * ((∑ i ∈ Finset.Icc 1 n, T i n : ℚ) / n) = -g n) ∧
    (∀ n : ℕ, 1 ≤ n → (∑ k ∈ Finset.Icc 1 n.factorial, T n k : ℚ) / n.factorial = 1) := by
  sorry

end OMA.S_oeis_a309229

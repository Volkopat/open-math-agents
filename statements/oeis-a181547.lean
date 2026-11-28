import Mathlib

/-!
# OEIS A181547: `a(n) = Σ_{k=0..⌊n/2⌋} C(n-k, k)^5`

Source: https://oeis.org/A181547
Credit: @goncalomsdias (agent: Claude Code, model claude-opus-5-5)

`a(n) = Sum_{k=0..floor(n/2)} C(n-k,k)^5`, offset 0 (`1, 1, 2, 33, 245, 1268, …`).

The entry: "Conjecture: Given F(n,L) = Sum_{k=0..[n/2]} C(n-k,k)^L, then
lim_{n->oo} F(n+1,L)/F(n,L) = (Fibonacci(L)*sqrt(5) + Lucas(L))/2 for L>=0 where
Fibonacci(n) = A000045(n) and Lucas(n) = A000032(n)." This file states that conjecture, for every
`L ≥ 0` (the sequence itself is the case `L = 5`).

Conventions:
* `F(n, L)` is defined in `ℕ` with Mathlib's `Nat.choose`; it is `≥ 1` (the term `k = 0` is `1`), so
  the ratio `F(n+1, L) / F(n, L)` is taken in `ℝ` without division by zero.
* `Fibonacci(L)` is Mathlib's `Nat.fib L` (A000045: `0, 1, 1, 2, …`). Mathlib has no Lucas numbers;
  `Lucas(L)` (A000032: `2, 1, 3, 4, 7, 11, …`) is defined here as `2 Fib(L+1) - Fib(L)`, which gives
  exactly those values (`L_0 = 2`, `L_1 = 1`, and the Fibonacci recurrence), in `ℝ`.
* The limit is `Filter.Tendsto … atTop (nhds …)` in `ℝ`.
* A computation of the ratio at `n = 200, 800, 3000` for `0 ≤ L ≤ 7` shows it approaching the
  conjectured value (which equals `φ^L`, `φ` the golden ratio).
-/

namespace OMA.S_oeis_a181547

open Filter Topology

/-- `F(n, L) = Σ_{k=0..⌊n/2⌋} C(n-k, k)^L`; the sequence is `F(n, 5)`. -/
def F (n L : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), ((n - k).choose k) ^ L

/-- `A181547(n) = F(n, 5)`. -/
def a (n : ℕ) : ℕ := F n 5

/-- The Lucas numbers `2, 1, 3, 4, 7, …` (A000032), as `2 Fib(L+1) - Fib(L)`. -/
def lucas (L : ℕ) : ℝ := 2 * (Nat.fib (L + 1) : ℝ) - (Nat.fib L : ℝ)

/-- Conjecture: `F(n+1, L) / F(n, L) → (Fib(L) √5 + Lucas(L)) / 2` for every `L ≥ 0`. -/
theorem main :
    ∀ L : ℕ, Tendsto (fun n : ℕ => (F (n + 1) L : ℝ) / (F n L : ℝ)) atTop
      (𝓝 (((Nat.fib L : ℝ) * Real.sqrt 5 + lucas L) / 2)) := by
  sorry

end OMA.S_oeis_a181547

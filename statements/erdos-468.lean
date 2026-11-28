import Mathlib

/-!
# Erdős Problem 468

Source: https://www.erdosproblems.com/468
Credit: @mgv27

For any $n$ let $D_n$ be the set of sums of the shape $d_1,d_1+d_2,d_1+d_2+d_3,\ldots$ where
$1<d_1<d_2<\cdots$ are the divisors of $n$. What is the size of $D_n\backslash \cup_{m<n}D_m$?
If $f(N)$ is the minimal $n$ such that $N\in D_n$ then is it true that $f(N)=o(N)$? Perhaps just
for almost all $N$?

Formalization notes:
* `main` states the second question, `f(N) = o(N)`, as `f(N) / N → 0`. The first question
  ("what is the size") is not a yes/no statement, and the "almost all `N`" variant is a weaker
  fallback; neither is stated.
* `d_1 < d_2 < ⋯` are all divisors of `n` greater than `1`, including `n` itself. The partial sum
  ending at the divisor `d` is the sum of all divisors `e` of `n` with `1 < e ≤ d`; this avoids
  sorting the divisors.
* `f(N)` is `sInf {n | N ∈ D_n}`. Some `N` lie in no `D_n` (e.g. `N = 4`: the smallest divisor
  `> 1` is prime, and `2 + d_2 ≥ 5`); for these `sInf ∅ = 0`, which does not affect `f(N) = o(N)`
  if, as a quick search suggests, such `N` are rare (only `N = 4` among `N ≤ 600` was missed
  by `n ≤ 3000`).
* Numeric check (pure Python): `f(2) = 2, f(6) = 4, f(8) = 15, f(9) = 12, f(10) = 21,
  f(11) = 6` (e.g. `D_4 = {2, 6}`, `D_15 = {3, 8, 23}`). Note `f(N) > N` happens (`N = 8`), so the
  question is not trivial.
-/

namespace OMA.S_erdos_468

open Filter Topology

/-- `N ∈ D_n`: `N = d_1 + ⋯ + d_j` for some `j ≥ 1`, where `1 < d_1 < d_2 < ⋯` are the divisors
of `n`; equivalently `N` is the sum of the divisors `e` of `n` with `1 < e ≤ d`, for some divisor
`d > 1` of `n`. -/
def InD (n N : ℕ) : Prop :=
  ∃ d ∈ n.divisors, 1 < d ∧ N = ∑ e ∈ n.divisors.filter (fun e => 1 < e ∧ e ≤ d), e

/-- `f(N)`: the minimal `n` with `N ∈ D_n` (`0` if there is none). -/
noncomputable def f (N : ℕ) : ℕ := sInf {n : ℕ | InD n N}

/-- Erdős Problem 468: is it true that `f(N) = o(N)`? -/
theorem main : Tendsto (fun N : ℕ => (f N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  sorry

end OMA.S_erdos_468

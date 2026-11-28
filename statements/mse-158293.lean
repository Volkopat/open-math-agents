import Mathlib

/-!
# Density of odd numbers in a sequence relating base 2 and base 3 expansion

Source: https://math.stackexchange.com/questions/158293
Credit: @SulkBash

## The problem (as the source states it)

Define the function
$$f(4n) = 6n+1,\quad f(4n+1) = 6n+2,\quad f(4n+2) = 6n+3,\quad f(4n+3) = 6n+5$$
and the sequence $u_0 = 2$, $u_{k+1} = f(u_k)$. Let $d_1 \le d_2$ be the lower and upper
asymptotic density of odd numbers in $u_k$. Experimentally, it seems reasonable to conjecture
$d = d_1 = d_2 = 2/3$.

The first terms are $2, 3, 5, 8, 13, 20, 31, 47, 71, 107, 161, 242$.
- Known: $d_1 \ge 1/2$, because $f(n)$ is odd for even $n$, so no two consecutive terms are
  even.
- A Markov-chain heuristic gives $2/3$. The question is open.

## Formalization notes

* `f` is defined on `ℕ` by the residue `m % 4`, with `n = m / 4`. Every natural number is
  uniquely `4n + r` with `r < 4`, so these are exactly the source's four cases.
* `u k = f^[k] 2` is the orbit $u_0 = 2$, $u_{k+1} = f(u_k)$.
* The density of odd numbers in $u_k$ is the density of the set of indices `k` with `u k` odd.
  Its lower and upper densities are the `liminf` and `limsup` of
  `#{k < K | Odd (u k)} / K`.
  - Both are equal to `2/3` exactly when this proportion converges to `2/3`, which is what
    `main` states.
  - Counting from `k = 0` or from `k = 1` does not change the limit.
-/

namespace OMA.S_mse_158293

open Filter Topology

/-- The map of the source: `f (4n) = 6n+1`, `f (4n+1) = 6n+2`, `f (4n+2) = 6n+3`,
`f (4n+3) = 6n+5`. -/
def f (m : ℕ) : ℕ :=
  if m % 4 = 0 then 6 * (m / 4) + 1
  else if m % 4 = 1 then 6 * (m / 4) + 2
  else if m % 4 = 2 then 6 * (m / 4) + 3
  else 6 * (m / 4) + 5

/-- The orbit `u_0 = 2`, `u_{k+1} = f (u_k)`. -/
def u (k : ℕ) : ℕ := f^[k] 2

/-- The odd terms of the orbit of `2` under `f` have asymptotic density `2/3`. -/
theorem main :
    Tendsto (fun K : ℕ => (((Finset.range K).filter (fun k => Odd (u k))).card : ℝ) / K)
      atTop (𝓝 (2 / 3)) := by
  sorry

end OMA.S_mse_158293

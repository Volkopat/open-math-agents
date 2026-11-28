import Mathlib

/-!
# A084302: remainder of tau(n) modulo 6 (Eldar's mean-value conjecture)

Source: https://oeis.org/A084302 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A084302 (offset 1): a(n) = tau(n) mod 6, where tau(n) is the number of divisors of n;
data 1, 2, 2, 3, 2, 4, 2, 4, 3, 4, 2, 0, ...

The entry records (Amiram Eldar, Jul 11 2024):

  The sums of the first 10^k terms, for k = 1, 2, ..., are 27, 236, 2275, 22166, 220070, ... .
  Conjecture: the asymptotic mean of this sequence is 3*zeta(3)/zeta(2) = 3 * A253905
  = 2.192288... .

Reading of the source:
* `a n` is the number of divisors of `n`, reduced modulo 6, for `n ≥ 1` (the offset).
* "The asymptotic mean" is the limit, as `N → ∞`, of `(a(1) + ... + a(N)) / N`, in `ℝ`.
  (With this indexing the sum of the first 10 terms is 27, as the entry reports.)
* `zeta(s)` for `s = 2, 3` is the Riemann zeta value `∑_{n ≥ 1} 1 / n^s`, written as a real
  series (both series converge).
-/

namespace OMA.S_oeis_a084302

open Filter Topology

/-- A084302(n): the number of divisors of `n`, modulo 6. -/
def a (n : ℕ) : ℕ := n.divisors.card % 6

/-- The Riemann zeta value `ζ(s) = ∑_{n ≥ 1} 1 / n^s` for a natural exponent `s`, as a real series. -/
noncomputable def zeta (s : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ s

/-- Eldar's conjecture: the mean `(a(1) + ... + a(N)) / N` tends to `3 ζ(3) / ζ(2)`. -/
theorem main :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (a n : ℝ)) / N) atTop
      (𝓝 (3 * zeta 3 / zeta 2)) := by
  sorry

end OMA.S_oeis_a084302

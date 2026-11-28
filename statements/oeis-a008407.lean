import Mathlib

/-!
# OEIS A008407: widths of narrowest admissible tuples

Source: https://oeis.org/A008407
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the minimal difference between the first and last of `n` consecutive large primes
permitted by divisibility considerations, i.e. the minimal width of an admissible `n`-tuple:
`0, 2, 6, 8, 12, 16, …` (offset 1). Conjecture (Sun, OEIS entry): (i) `a(n)^(1/n)`
(`n = 3, 4, …`) is strictly decreasing; (ii) `0 < a(n)/n - H_n < (γ + 2)/log n` for all `n > 4`,
where `H_n` is the `n`-th harmonic number and `γ` is Euler's constant.

Conventions:
* A finite set `S ⊆ ℕ` is admissible if for every prime `p` it misses some residue class mod
  `p`. Translating does not change admissibility, so `a(n)` is the least `w` such that some
  admissible `S ⊆ {0, …, w}` with `0 ∈ S` has `n` elements.
* `main` states (i) and (ii). (The entry also lists two further conjectures of Sun about twin
  primes, which are separate statements.)
-/

namespace OMA.S_oeis_a008407

/-- `S` misses a residue class modulo every prime. -/
def Admissible (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ s ∈ S, s % p ≠ r

/-- The minimal width of an admissible `n`-tuple. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {w : ℕ | ∃ S : Finset ℕ, S.card = n ∧ 0 ∈ S ∧ (∀ s ∈ S, s ≤ w) ∧ Admissible S}

/-- The harmonic number `H_n`. -/
noncomputable def H (n : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / i

/-- Sun's conjectures (i) and (ii). -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → (a (n + 1) : ℝ) ^ ((1 : ℝ) / (n + 1)) < (a n : ℝ) ^ ((1 : ℝ) / n)) ∧
    (∀ n : ℕ, 4 < n → 0 < (a n : ℝ) / n - H n ∧
      (a n : ℝ) / n - H n < (Real.eulerMascheroniConstant + 2) / Real.log n) := by
  sorry

end OMA.S_oeis_a008407

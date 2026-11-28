import Mathlib

/-!
# Is there a composite number for which this game with composite numbers never ends?

Source: https://mathoverflow.net/questions/268929
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Start from a natural number `> 1`. If it is a prime power the game is over. Otherwise it has
`k ≥ 2` distinct prime factors, and we add to it the next number with exactly `k` distinct prime
factors; repeat with the result. Question: is there a composite number for which the game never
ends?

Conventions:
* `ω(n)` is the number of distinct prime factors (`n.primeFactors.card`). For `m` with `ω(m) = k`,
  the next number with `k` distinct prime factors is the least `m' > m` with `ω(m') = k` (it exists:
  multiply `m` by a power of one of its prime factors). A step maps `m` to `m + next(m)`.
* The game from `n` never ends iff every iterate has `ω ≥ 2`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_268929

/-- Number of distinct prime factors. -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- The next number after `m` with the same number of distinct prime factors. -/
noncomputable def next (m : ℕ) : ℕ := sInf {m' : ℕ | m < m' ∧ omega m' = omega m}

/-- One move of the game. -/
noncomputable def step (m : ℕ) : ℕ := m + next m

/-- Some composite number starts a game that never ends. -/
theorem main : ∃ n : ℕ, 1 < n ∧ ¬ n.Prime ∧ ∀ i : ℕ, 2 ≤ omega (step^[i] n) := by
  sorry

end OMA.S_mo_268929

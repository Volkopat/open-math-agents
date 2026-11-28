import Mathlib

/-!
# A077223

Source: https://oeis.org/A077223
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(1) = 1` and then alternately even and odd numbers not occurring earlier such that the sum of
any two successive terms is squarefree: `1, 2, 3, 4, 7, 6, 5, 8, …`. Conjecture (OEIS): there
are infinitely many strings of `8` successive terms of the form `k, k+1, …, k+7`.

## Encoding

* Each new term is the least positive integer not used before, of the required parity (even at
  even positions, odd at odd positions, offset `1`), whose sum with the previous term is
  squarefree (definition checked against the OEIS terms). `terms j` is `[a(1), …, a(j+1)]`.
* "Infinitely many strings" means infinitely many positions `i` with `a(i + t) = a(i) + t` for
  `t = 0, …, 7`.
-/

namespace OMA.S_oeis_a077223

/-- `[a(1), …, a(j+1)]`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => [1]
  | j + 1 =>
    let L := terms j
    L ++ [sInf {m : ℕ | 1 ≤ m ∧ m ∉ L ∧ m % 2 = j % 2 ∧ Squarefree (L.getLast! + m)}]

/-- `a n` (offset `1`). -/
noncomputable def a (n : ℕ) : ℕ := (terms (n - 1)).getD (n - 1) 0

theorem main : {i : ℕ | 1 ≤ i ∧ ∀ t < 8, a (i + t) = a i + t}.Infinite := by
  sorry

end OMA.S_oeis_a077223

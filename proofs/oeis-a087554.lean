import OMAStatements.S_oeis_a087554
import Mathlib

/-!
# OEIS A087554: the second claim fails at `n = 2`, `r = 3`

The second claim asks for `S` with `n r < S < n (r + 1)` and `n S + 1` prime. For `n = 2`,
`r = 3` the only candidate is `S = 7`, and `2 · 7 + 1 = 15 = 3 · 5` is not prime.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a087554.main) := by
  rintro ⟨-, h⟩
  obtain ⟨S, h1, h2, hp⟩ := h 2 3 (by norm_num) (by norm_num)
  have hS : S = 7 := by omega
  subst hS
  exact absurd hp (by decide)

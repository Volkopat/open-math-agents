import OMAStatements.S_oeis_a063520

/-!
# OEIS A063520: `n = 2` does have a solution

For every `n`, `(r, s, t) = (n² + 2n, n + 1, 1)` solves `r s t = n (r + s + t)`, since both sides
equal `n (n + 1) (n + 2)`. For `n = 2` this is `(8, 3, 1)`: `8 · 3 · 1 = 24 = 2 · 12`, so the
claimed exception `n = 2` is not one.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a063520.main) := by
  intro h
  have h2 := (h 2 (by norm_num)).mp ⟨8, 3, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  exact h2.1 rfl

import OMAStatements.S_oeis_a261387

/-!
Part (i) of the formal statement is an equivalence asserted for every natural number `n`,
including `n = 0`. For `n = 0` the right-hand side `0 ∉ {1, 2, 8}` holds, while the left-hand side
asks for `0 < k < m` with `k + m = 0`, which is impossible. Hence the statement is false.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a261387.main) := by
  intro h
  obtain ⟨k, m, hk, hkm, hsum, -⟩ := (h.1 0).mpr (by decide)
  omega

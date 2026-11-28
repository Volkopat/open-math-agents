import OMAStatements.S_oeis_a004001

-- As formalized, the step function receives the constant function (fun k => prev), so the
-- recursion never looks at earlier values: a n = n + 2 for n >= 1. In particular a 2 = 4,
-- so a 2 * 2 = 8, although 2 = 2 ^ 1 is a power of two. This refutes the statement as
-- written (a formalization issue), not the OEIS A004001 conjecture itself.
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a004001.main) := by
  intro h
  have hp : OMA.S_oeis_a004001.IsPowTwo 2 := ⟨1, le_refl 1, rfl⟩
  have h2 := (h 2 (by norm_num)).mpr hp
  have e : OMA.S_oeis_a004001.a 2 = 4 := rfl
  rw [e] at h2
  omega

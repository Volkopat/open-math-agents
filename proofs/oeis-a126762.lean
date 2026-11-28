import OMAStatements.S_oeis_a126762

-- Problem: A126762: a(n) is the least k > n such that the remainder when n^k is divided by k is n.
-- Credit: @sobrien032

/- Thomas Ordowski's two minima already differ at n = 363.
   The OEIS term table and the trureturing refutation give this witness. -/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a126762.main) := by
  intro h
  obtain ⟨a, first, second⟩ := h 363 (by decide)
  have upper : a ≤ 366 := first.2 (by
    change 363 < (366 : ℕ) ∧ 363 ^ 366 % 366 = 363
    decide +kernel)
  have low := first.1.1
  have res := first.1.2
  have shifted := second.1.2
  change 363 < a at low
  change 363 ^ a % a = 363 at res
  change 363 ^ (a - 1) % a = 1 at shifted
  have cases : a = 364 ∨ a = 365 ∨ a = 366 := by omega
  rcases cases with rfl | rfl | rfl <;> revert res shifted <;> decide +kernel

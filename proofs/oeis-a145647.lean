import OMAStatements.S_oeis_a145647

-- Disproof: the claimed order-4 recurrence for the gaps fails at n = 14.
-- gap 14 = 26427, while the recurrence predicts 26426.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a145647.main) := by
  rintro ⟨-, -, h⟩
  exact absurd (h 14 (by decide)) (by decide)

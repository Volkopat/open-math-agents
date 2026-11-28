import OMAStatements.S_oeis_a393794

open OMA.S_oeis_a393794

-- Repeating the digit block 1089 twice gives 10891089, whose reversal is
-- nine times as large. Appending a zero therefore gives a second fixed point.
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a393794.main) := by
  intro h
  exact absurd ((h 5 (by decide) 108910890).mp (by decide)) (by decide)

import OMAStatements.S_oeis_a285613

-- Problem: oeis-a285613
-- Upstream: statements/oeis-a285613.lean (declaration OMA.S_oeis_a285613.main)
--
-- The statement is false as formalized.
-- Its last clause asserts a n = 10 * a (n - 1) + 10 * a (n - 2) - 100 * a (n - 3) for every n > 2,
-- but the sequence starts 1, 10, 10, 100, 1100, 11000, so at n = 4 the left side is 1100 and the
-- right side is 10 * 100 + 10 * 10 - 100 * 10 = 100. (The generating function clause has numerator
-- 1 - 100 * X ^ 2 + 1000 * X ^ 4, so the recurrence can only hold for n > 4.)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a285613.main) := by
  intro h
  have hn := h.2.2.2 4 (by norm_num)
  revert hn
  decide

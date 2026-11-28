import OMAStatements.S_oeis_a280373

-- Problem: oeis-a280373
-- Upstream: statements/oeis-a280373.lean (declaration OMA.S_oeis_a280373.main)
--
-- The statement is false as formalized.
-- Its first clause asserts a n = 16 * a (n - 4) for every n > 3, but the sequence starts
-- 1, 2, 5, 8, 16, 40, so at n = 5 the left side is 40 and the right side is 16 * 2 = 32.
-- (The generating function clause has a numerator of degree 12, so the recurrence can only
-- hold for n > 12.)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a280373.main) := by
  intro h
  have hn := h.1 5 (by norm_num)
  revert hn
  decide

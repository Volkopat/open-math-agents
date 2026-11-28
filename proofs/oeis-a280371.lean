import OMAStatements.S_oeis_a280371

-- Problem: oeis-a280371
-- Upstream: statements/oeis-a280371.lean (declaration OMA.S_oeis_a280371.main)
--
-- The statement is false as formalized.
-- Its first clause asserts a n = 10000 * a (n - 4) for every n > 3, but the sequence starts
-- 1, 10, 101, 1000, 10000, 101000, so at n = 5 the left side is 101000 and the right side is
-- 10000 * 10 = 100000. (The generating function clause has a numerator of degree 12, so the
-- recurrence can only hold for n > 12.)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a280371.main) := by
  intro h
  have hn := h.1 5 (by norm_num)
  revert hn
  decide

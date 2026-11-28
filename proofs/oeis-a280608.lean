import OMAStatements.S_oeis_a280608

-- Problem: oeis-a280608
-- Upstream: statements/oeis-a280608.lean (declaration OMA.S_oeis_a280608.main)
--
-- The statement is false as formalized.
-- Its second clause asserts a n = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3) for every n > 4,
-- but the sequence starts 1, 3, 4, 14, 17, 57, 65, so at n = 6 the left side is 65 and the
-- right side is 57 + 4 * 17 - 4 * 14 = 69.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a280608.main) := by
  intro h
  have hn := h.2 6 (by norm_num)
  revert hn
  decide

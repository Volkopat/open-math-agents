import OMAStatements.S_oeis_a281146

-- Problem: A281146 (Rule 515 cellular automaton, x-axis from the origin to the right, read in base 10)
-- Upstream: statements/oeis-a281146.lean (declaration OMA.S_oeis_a281146.main)
--
-- The statement is false as formalized. Its third clause asserts the recurrence
--   a n = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3)   for every n > 2,
-- but the sequence starts 1, 10, 100, 1000, 10100, 101000, so at n = 4 the left side is 10100
-- and the right side is 10 * 1000 + 100 - 10 * 10 = 10000. (The generating function clause of the
-- same statement has numerator 1 - X ^ 2 + 100 * X ^ 4, which already shows that the recurrence
-- can only hold for n > 4.)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a281146.main) := by
  intro h
  have h4 := h.2.2.1 4 (by norm_num)
  revert h4
  decide

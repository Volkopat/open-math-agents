import OMAStatements.S_oeis_a002822

-- Problem: OEIS A002822, B. Selcoe's conjecture that 6j in the sequence forces j in it.
-- Disproof: j = 63. Here 6 * 378 - 1 = 2267 and 6 * 378 + 1 = 2269 are twin primes, so
-- 378 = 6 * 63 is a term, but 6 * 63 - 1 = 377 = 13 * 29 is composite, so 63 is not
-- (J. Kimberley, OEIS A002822, Oct 13 2015; the counterexamples form A263282).

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a002822.main) := by
  intro h
  have hp := (h 63 (by decide) ⟨by decide, by norm_num, by norm_num⟩).2.1
  norm_num at hp

import OMAStatements.S_oeis_a267515

-- Problem: OEIS A267515, Colin Barker's conjectured recurrence and generating function
-- for the Rule 137 center column read in base two.
-- Disproof: the recurrence a(n) = 2 a(n-1) + a(n-7) - 2 a(n-8) says that the center
-- column is periodic with period 7 from n = 1 on; it fails at n = 62, where the center
-- cell differs from the cell at n = 55 (R. J. Mathar, OEIS A267515, Apr 12 2019).

namespace OMA.A267515Proof

open OMA.S_oeis_a267515

set_option maxRecDepth 100000 in
lemma fails : a 62 ≠ 2 * a (62 - 1) + a (62 - 7) - 2 * a (62 - 8) := by
  decide

end OMA.A267515Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267515.main) := by
  intro h
  exact OMA.A267515Proof.fails (h.1 62 (by norm_num))

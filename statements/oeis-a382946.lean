import Mathlib

/-!
# OEIS A382946: least k with a proper divisor d whose base-n digits are, up to order, those of k

Sigrist's sequence: a(n) is the least positive integer k having a proper
divisor d such that the base n expansions of k and d, without leading
zeros, have, up to order, the same digits, or a(n) = -1 if no such k
exists. The -1 case is modelled as a_val n = 0 (sInf of the empty set).
The conjecture is a(n) > 0 for any n > 2.

Modelling notes: the clause without leading zeros is automatic for
Nat.digits (its last digit is never 0), and up to order is List.Perm,
the analogue of the vecsort in the PARI code of the fiche. The proper
divisor clause is d | k together with d < k; k positive and d positive
then follow (d < k gives k >= 1, and 0 | k forces k = 0).

Source: https://oeis.org/A382946
-/

namespace OMA.S_oeis_a382946

/-- The record predicate: d is a proper divisor of k (d | k and d < k)
whose base-n expansion has, up to order, the same digits as that of k. -/
abbrev P (n k d : ℕ) : Prop :=
  d ∣ k ∧ d < k ∧ (Nat.digits n k).Perm (Nat.digits n d)

/-- The function a(n): the least admissible k, or 0 (encoding the -1 of
the fiche) when the admissible set is empty. -/
noncomputable def a_val (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ d, P n k d}

theorem main : ∀ n : ℕ, 2 < n → 0 < a_val n := by
  sorry

end OMA.S_oeis_a382946

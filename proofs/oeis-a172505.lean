import OMAStatements.S_oeis_a172505

-- Problem: A172505: a(n) = numerator of fraction a/b, where gcd(a, b) = 1, whose decimal representation has the form (1)(2)(3)...(n-1)(n).(1)(2)(3)...(n-1)(n)... with period (1)(2)(3)...(n-1)(n).
-- Upstream: formal-conjectures statements/oeis-a172505.lean:0 (declaration OMA.S_oeis_a172505.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: x(n) = C(n) + q(n) with q(n) = C(n)/(10^L(n) - 1), and adding a natural number to a
-- rational number does not change its denominator. So b(n) = A172498(n) for every n, and the
-- conjecture (the two sequences differ somewhere) is false. The listed denominators are not used.

open OMA.S_oeis_a172505 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a172505.main) := by
  rintro ⟨-, n, -, h⟩
  apply h
  show ((C n : ℚ) + (C n : ℚ) / ((10 : ℚ) ^ L n - 1)).den = ((C n : ℚ) / ((10 : ℚ) ^ L n - 1)).den
  exact Rat.natCast_add_den (C n) _

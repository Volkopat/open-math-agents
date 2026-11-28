import OMAStatements.S_oeis_a277088

namespace PisotCeiling558

open OMA.S_oeis_a277088

private def iterate : ℕ → ℕ → ℕ → ℕ
  | 0, x, _ => x
  | n + 1, x, y => iterate n y ((y ^ 2 + x - 1) / x)

private lemma iterate_eq (n i : ℕ) : iterate n (a i) (a (i + 1)) = a (i + n) := by
  induction n generalizing i with
  | zero => simp [iterate]
  | succ n ih =>
    rw [iterate, ← a.eq_3, ih (i + 1)]
    congr 1
    omega

private def value (n : ℕ) : ℕ := iterate n 5 12

private lemma value_eq (n : ℕ) : value n = a n := by
  unfold value
  have h := iterate_eq n 0
  simpa only [Nat.zero_add, a.eq_1, a.eq_2] using h

private lemma witness :
    (value 558 : ℤ) ≠ 3 * (value 557 : ℤ) - 2 * (value 556 : ℤ) + 2 * (value 555 : ℤ) -
      (value 554 : ℤ) + (value 552 : ℤ) - (value 551 : ℤ) - (value 549 : ℤ) := by
  decide +kernel

theorem refute : ¬ (type_of% @OMA.S_oeis_a277088.main) := by
  intro h
  have h558 := h.1 558 (by decide)
  change (a 558 : ℤ) = 3 * (a 557 : ℤ) - 2 * (a 556 : ℤ) + 2 * (a 555 : ℤ) -
    (a 554 : ℤ) + (a 552 : ℤ) - (a 551 : ℤ) - (a 549 : ℤ) at h558
  have hbad := witness
  rw [value_eq 558, value_eq 557, value_eq 556, value_eq 555, value_eq 554, value_eq 552,
    value_eq 551, value_eq 549] at hbad
  exact hbad h558

end PisotCeiling558

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a277088.main) := PisotCeiling558.refute

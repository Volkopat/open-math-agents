import OMAStatements.S_oeis_a277089

namespace PisotCeiling44

open OMA.S_oeis_a277089

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

private def value (n : ℕ) : ℕ := iterate n 6 15

private lemma value_eq (n : ℕ) : value n = a n := by
  unfold value
  have h := iterate_eq n 0
  simpa only [Nat.zero_add, a.eq_1, a.eq_2] using h

private lemma witness :
    (value 44 : ℤ) ≠ 3 * (value 43 : ℤ) - (value 42 : ℤ) - (value 40 : ℤ) +
      2 * (value 38 : ℤ) - 2 * (value 37 : ℤ) := by
  decide +kernel

theorem refute : ¬ (type_of% @OMA.S_oeis_a277089.main) := by
  intro h
  have h44 := h.1 44 (by decide)
  change (a 44 : ℤ) = 3 * (a 43 : ℤ) - (a 42 : ℤ) - (a 40 : ℤ) +
    2 * (a 38 : ℤ) - 2 * (a 37 : ℤ) at h44
  have hbad := witness
  rw [value_eq 44, value_eq 43, value_eq 42, value_eq 40, value_eq 38, value_eq 37] at hbad
  exact hbad h44

end PisotCeiling44

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a277089.main) := PisotCeiling44.refute

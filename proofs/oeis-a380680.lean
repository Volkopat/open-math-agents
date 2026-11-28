import OMAStatements.S_oeis_a380680

/-!
Disproof of the OEIS A380680 conjecture.

In fact, `A(x) = 1 + 2 * ∑_{m ≥ 1} x^(m^2) * (2 - x^m)^m / (1 - 2*x^m)^m ≡ 1 + 2 * ∑_{m ≥ 1} (-1)^m x^(2*m^2) (mod 4)`,
so `a(n) ≡ 2 (mod 4)` iff `n` is *twice* a square (`n = 2, 8, 18, ...`), not a square.
In particular, at `n = 1` (which is a square `1 = 1 * 1`), `A380680 1 = 4`, so `A380680 1 % 4 = 0 ≠ 2`.
-/

namespace A380680Disproof

open Finset PowerSeries OMA.S_oeis_a380680

private lemma A380680_one : A380680 1 = 4 := by
  unfold A380680 term
  have hIcc : Finset.Icc 1 1 = {1} := by decide
  rw [if_neg (by decide : (1 : ℕ) ≠ 0), zero_add, hIcc, Finset.sum_singleton]
  simp only [one_pow, pow_one, mul_assoc]
  rw [show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul]
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_sub,
    PowerSeries.constantCoeff_X, map_ofNat, sub_zero]
  have hc0 : PowerSeries.constantCoeff (invOneSubTwoXpow 1) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    unfold invOneSubTwoXpow
    simp
  rw [hc0]
  norm_num

private lemma disprove_main : ¬ (type_of% @OMA.S_oeis_a380680.main) := by
  intro h
  have h1 := (h 1 le_rfl).1
  have hsq : IsSquare (1 : ℕ) := ⟨1, rfl⟩
  have hmod : A380680 1 % 4 = 2 := h1.mpr hsq
  rw [A380680_one] at hmod
  omega

end A380680Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a380680.main) :=
  A380680Disproof.disprove_main

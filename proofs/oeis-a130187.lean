import OMAStatements.S_oeis_a130187
import Mathlib

-- Problem: A130187, a(n) = numerator of r(n) = -2 z(2n+1) equals (2n+1)!!/A000265(n+1).
-- Upstream: formal-conjectures statements/oeis-a130187.lean (declaration OMA.S_oeis_a130187.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the stated formula holds for all n >= 0).
-- Proof: r(n) = (2n+1)!/(4^n (n+1)!) = (2n+1)!!/(2^n (n+1)); writing n+1 = 2^v o with o odd,
-- o divides the odd number (2n+1)!!, so r(n) = A/2^(n+v) with A = (2n+1)!!/o odd, in lowest terms.

namespace OMA.P_oeis_a130187

open OMA.S_oeis_a130187 Nat

theorem dfo (k : ℕ) : Odd (2 * k + 1)‼ := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, Nat.doubleFactorial_add_two]
    exact Odd.mul ⟨k + 1, by ring⟩ ih

theorem dvd_df (n j : ℕ) (h : j ≤ n) : (2 * j + 1) ∣ (2 * n + 1)‼ := by
  induction n with
  | zero =>
    obtain rfl : j = 0 := by omega
    simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, Nat.doubleFactorial_add_two]
    rcases Nat.lt_or_ge j (n + 1) with hj | hj
    · exact Dvd.dvd.mul_left (ih (by omega)) _
    · obtain rfl : j = n + 1 := by omega
      exact ⟨(2 * n + 1)‼, by ring⟩

theorem r_eq (n : ℕ) : r n = ((2 * n + 1)‼ : ℚ) / (2 ^ n * ((n : ℚ) + 1)) := by
  unfold r z zEgf expSq
  simp only [PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_one]
  rw [if_neg (by omega : 2 * n + 1 + 1 ≠ 0), if_pos (by omega : (2 * n + 1 + 1) % 2 = 0),
    show (2 * n + 1 + 1) / 2 = n + 1 by omega, Nat.factorial_eq_mul_doubleFactorial (2 * n),
    Nat.doubleFactorial_two_mul, Nat.factorial_succ]
  have h4 : (4 : ℚ) ^ (n + 1) = 4 * 2 ^ n * 2 ^ n := by
    rw [pow_succ, show (4 : ℚ) = 2 * 2 by norm_num, mul_pow]
    ring
  push_cast
  rw [h4]
  field_simp
  ring

theorem main' : ∀ n : ℕ,
    (a n : ℚ) = (Nat.doubleFactorial (2 * n + 1) : ℚ) / (oddPart (n + 1) : ℚ) := by
  intro n
  have ho : oddPart (n + 1) * 2 ^ (padicValNat 2 (n + 1)) = n + 1 :=
    Nat.div_mul_cancel pow_padicValNat_dvd
  have hoodd : Odd (oddPart (n + 1)) := by
    rcases Nat.even_or_odd (oddPart (n + 1)) with ⟨c, hc⟩ | h
    · exfalso
      apply pow_succ_padicValNat_not_dvd (p := 2) (n := n + 1) (by omega)
      generalize padicValNat 2 (n + 1) = v at ho ⊢
      exact ⟨c, by rw [← ho, hc, pow_succ]; ring⟩
    · exact h
  obtain ⟨j, hj⟩ := hoodd
  have hdvd : oddPart (n + 1) ∣ (2 * n + 1)‼ := by
    rw [hj]
    apply dvd_df
    have : oddPart (n + 1) ≤ n + 1 := by
      calc oddPart (n + 1) ≤ oddPart (n + 1) * 2 ^ (padicValNat 2 (n + 1)) :=
            Nat.le_mul_of_pos_right _ (by positivity)
        _ = n + 1 := ho
    omega
  obtain ⟨A, hA⟩ := hdvd
  have hAodd : Odd A := by
    have := dfo n
    rw [hA] at this
    exact (Nat.odd_mul.mp this).2
  have ho0 : (oddPart (n + 1) : ℚ) ≠ 0 := by
    rw [hj]
    positivity
  have hr : r n = ((A : ℤ) : ℚ) / (((2 : ℤ) ^ (n + padicValNat 2 (n + 1)) : ℤ) : ℚ) := by
    rw [r_eq, hA]
    have ho' : ((oddPart (n + 1) : ℕ) : ℚ) * 2 ^ (padicValNat 2 (n + 1)) = (n : ℚ) + 1 := by
      exact_mod_cast ho
    rw [← ho']
    push_cast
    rw [pow_add]
    field_simp
  have hnum : a n = (A : ℤ) := by
    unfold a
    rw [hr]
    apply Rat.num_div_eq_of_coprime (by positivity)
    rw [Int.natAbs_pow, Int.natAbs_natCast]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hAodd)
  rw [hnum, hA]
  push_cast
  field_simp

end OMA.P_oeis_a130187

theorem OMA.solution : type_of% @OMA.S_oeis_a130187.main := OMA.P_oeis_a130187.main'

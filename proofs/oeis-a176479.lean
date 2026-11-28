import OMAStatements.S_oeis_a176479
import Mathlib

namespace A176479Aux

open PowerSeries

lemma key (n : ℕ) : ((n : ℚ) + 4) * (Nat.largeSchroder (n + 3) : ℚ) =
    3 * (2 * (n : ℚ) + 5) * (Nat.largeSchroder (n + 2) : ℚ)
      - ((n : ℚ) + 1) * (Nat.largeSchroder (n + 1) : ℚ) := by
  obtain ⟨L, hLdef⟩ : ∃ L : PowerSeries ℚ, L = PowerSeries.map (Nat.castRingHom ℚ) largeSchroderSeries :=
    ⟨_, rfl⟩
  have cL : ∀ k, coeff k L = (Nat.largeSchroder k : ℚ) := by
    intro k
    rw [hLdef, coeff_map, coeff_largeSchroderSeries]
    simp
  have h1 : L = 1 + X * L + X * (L * L) := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ))
      largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
    simp only [map_add, map_mul, map_pow, map_one, PowerSeries.map_X] at h
    rw [← hLdef, pow_two] at h
    exact h
  have h2 : derivative ℚ L = L + X * derivative ℚ L + L * L + 2 * X * L * derivative ℚ L := by
    have e := congrArg (derivative ℚ) h1
    simp only [map_add, Derivation.leibniz, derivative_X, smul_eq_mul,
      Derivation.map_one_eq_zero] at e
    linear_combination e
  have ode : X * (1 - 6 * X + X ^ 2) * derivative ℚ L + (1 - 3 * X) * L = 1 + X := by
    linear_combination (4 * X ^ 2 * derivative ℚ L + 2 * X * L + 1 + X) * h1
      + (X * (1 - X - 2 * X * L)) * h2
  have e3 : (C 3 : PowerSeries ℚ) = 3 := map_ofNat C 3
  have e6 : (C 6 : PowerSeries ℚ) = 6 := map_ofNat C 6
  have ode' : X * derivative ℚ L + X * (X * (X * derivative ℚ L)) + L =
      1 + X + C 6 * (X * (X * derivative ℚ L)) + C 3 * (X * L) := by
    rw [e6, e3]
    linear_combination ode
  have c1 : coeff (n + 3) (X * derivative ℚ L) = (Nat.largeSchroder (n + 3) : ℚ) * ((n : ℚ) + 3) := by
    rw [coeff_succ_X_mul, coeff_derivative, cL]
    push_cast
    ring
  have c2 : coeff (n + 3) (X * (X * (X * derivative ℚ L))) =
      (Nat.largeSchroder (n + 1) : ℚ) * ((n : ℚ) + 1) := by
    rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul, coeff_derivative, cL]
  have c3 : coeff (n + 3) (X * (X * derivative ℚ L)) =
      (Nat.largeSchroder (n + 2) : ℚ) * ((n : ℚ) + 2) := by
    rw [coeff_succ_X_mul, coeff_succ_X_mul, coeff_derivative, cL]
    push_cast
    ring
  have c4 : coeff (n + 3) (X * L) = (Nat.largeSchroder (n + 2) : ℚ) := by
    rw [coeff_succ_X_mul, cL]
  have c5 : coeff (n + 3) (1 : PowerSeries ℚ) = 0 := by
    rw [coeff_one, if_neg (by omega)]
  have c6 : coeff (n + 3) (X : PowerSeries ℚ) = 0 := by
    rw [coeff_X, if_neg (by omega)]
  have hc := congrArg (coeff (n + 3)) ode'
  rw [map_add, map_add, map_add, map_add, map_add, c1, c2, cL, coeff_C_mul, coeff_C_mul, c3, c4,
    c5, c6] at hc
  linear_combination hc

end A176479Aux

open OMA.S_oeis_a176479 A176479Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a176479.main := by
  intro n hn
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n
    simp [a, Nat.smallSchroder]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega]
    have k := key m
    have t3 : 2 * Nat.smallSchroder (m + 3 + 1) = Nat.largeSchroder (m + 3) :=
      Nat.two_mul_smallSchroder_succ (by omega)
    have t2 : 2 * Nat.smallSchroder (m + 2 + 1) = Nat.largeSchroder (m + 2) :=
      Nat.two_mul_smallSchroder_succ (by omega)
    have t1 : 2 * Nat.smallSchroder (m + 1 + 1) = Nat.largeSchroder (m + 1) :=
      Nat.two_mul_smallSchroder_succ (by omega)
    rw [← t3, ← t2, ← t1] at k
    push_cast at k
    unfold a
    have goalq : ((((m + 3 : ℕ) : ℤ) * (((m + 3 : ℕ) : ℤ) - 1) * ((((m + 3 : ℕ) : ℤ) + 1) * (Nat.smallSchroder (m + 3 + 1) : ℤ))
        - 3 * (2 * ((m + 3 : ℕ) : ℤ) - 1) * (((m + 3 : ℕ) : ℤ) - 1) * ((((m + 2 : ℕ) : ℤ) + 1) * (Nat.smallSchroder (m + 2 + 1) : ℤ))
        + ((m + 3 : ℕ) : ℤ) * (((m + 3 : ℕ) : ℤ) - 2) * ((((m + 1 : ℕ) : ℤ) + 1) * (Nat.smallSchroder (m + 1 + 1) : ℤ)) : ℤ) : ℚ) = 0 := by
      push_cast
      linear_combination (((m : ℚ) + 3) * ((m : ℚ) + 2) / 2) * k
    exact_mod_cast goalq

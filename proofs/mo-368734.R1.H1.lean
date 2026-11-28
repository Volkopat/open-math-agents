import OMAReductions.R_mo_368734_R1
import Mathlib

/-! The fifth-power permutation step, following @ivillar (#13526).
Use the power-map bijection on the finite unit group; zero is handled separately. -/

theorem OMA.solution : OMA.R_mo_368734_R1.H1 := by
  intro p hp h5
  have : Fact p.Prime := ⟨hp⟩
  have hcop : (Nat.card (ZMod p)ˣ).Coprime 5 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp,
      Nat.coprime_comm, Nat.prime_five.coprime_iff_not_dvd]
    have := hp.two_le
    omega
  apply Finite.injective_iff_bijective.mp
  intro x y hxy
  have hpow : x ^ 5 = y ^ 5 := add_right_cancel hxy
  by_cases hx : x = 0
  · simp_all
  by_cases hy : y = 0
  · simp_all
  have hu : (Units.mk0 x hx) ^ 5 = (Units.mk0 y hy) ^ 5 := Units.ext hpow
  exact congrArg Units.val (hcop.pow_left_bijective.injective hu)

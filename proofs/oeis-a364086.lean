import OMAStatements.S_oeis_a364086

/-! The primitive-root characterization, following @agchua (#22714).
Apply the Fermat–Euler theorem in the unit group and transport its order bound
directly, retaining the original totient bounds and the k = 0 treatment. -/

open OMA.S_oeis_a364086 in
theorem OMA.solution : type_of% @OMA.S_oeis_a364086.main := by
  intro k
  unfold A002326 HasPrimitiveRoot2
  rw [show 2 * k + 1 - 1 = 2 * k by omega]
  constructor
  · intro h
    refine ⟨?_, h⟩
    have hcop : Nat.Coprime 2 (2 * k + 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
    have h4 : orderOf (2 : ZMod (2 * k + 1)) ∣ Nat.totient (2 * k + 1) := by
      simpa only [← orderOf_units, ZMod.coe_unitOfCoprime, Nat.cast_ofNat] using
        orderOf_dvd_of_pow_eq_one (ZMod.pow_totient (ZMod.unitOfCoprime 2 hcop))
    rw [h] at h4
    have h5 : 0 < Nat.totient (2 * k + 1) := Nat.totient_pos.mpr (by omega)
    have h6 : 0 < 2 * k := Nat.pos_of_dvd_of_pos h4 h5
    have h7 : 2 * k ≤ Nat.totient (2 * k + 1) := Nat.le_of_dvd h5 h4
    have h8 : Nat.totient (2 * k + 1) < 2 * k + 1 := Nat.totient_lt (2 * k + 1) (by omega)
    exact (Nat.totient_eq_iff_prime (by omega)).mp (by omega)
  · intro h
    exact h.2

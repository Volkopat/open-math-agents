import OMAReductions.R_oeis_a293482_R1

-- Step oeis-a293482.R1.H4
-- Credit: @grp06
-- Source: OEIS A293482, https://oeis.org/A293482/internal
-- The cyclic-group reduction is credited to @Ciphore.

theorem OMA.solution : OMA.R_oeis_a293482_R1.H4 := by
  intro p e hp hmod he
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    omega
  letI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  letI : IsCyclic (ZMod (p ^ e))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  have cardUnits : Nat.card (ZMod (p ^ e))ˣ = Nat.totient (p ^ e) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have dvdPred : 5 ∣ p - 1 := by
    refine ⟨p / 5, ?_⟩
    have h := Nat.mod_add_div p 5
    omega
  have totientFormula :
      Nat.totient (p ^ e) = (p - 1) * p ^ (e - 1) :=
    (Nat.totient_prime_pow hp he).trans (Nat.mul_comm _ _)
  have dvdTotient : 5 ∣ Nat.totient (p ^ e) := by
    rw [totientFormula]
    exact dvd_mul_of_dvd_left dvdPred _
  change Nat.card (powMonoidHom 5 : (ZMod (p ^ e))ˣ →* (ZMod (p ^ e))ˣ).range =
    (p - 1) * p ^ (e - 1) / 5
  rw [IsCyclic.card_powMonoidHom_range, cardUnits, Nat.gcd_eq_right dvdTotient,
    totientFormula]

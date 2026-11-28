import OMAReductions.R_oeis_a293482_R1

-- Credit: @grp06
-- Source: OEIS A293482, https://oeis.org/A293482/internal
-- This proves the prime-power clause in the reduction credited to @Ciphore.

theorem OMA.solution : OMA.R_oeis_a293482_R1.H3 := by
  classical
  intro p e hp hres he
  have hp_ge : 2 ≤ p := hp.two_le
  have htot : Nat.totient (p ^ e) = p ^ (e - 1) * (p - 1) :=
    Nat.totient_prime_pow hp (by omega)
  have hcop : (Nat.totient (p ^ e)).Coprime 5 := by
    rw [Nat.coprime_comm, Nat.prime_five.coprime_iff_not_dvd, htot]
    intro hdiv
    rcases Nat.prime_five.dvd_mul.mp hdiv with hpow | hpred
    · have hmod : p % 5 = 0 :=
        Nat.dvd_iff_mod_eq_zero.mp (Nat.prime_five.dvd_of_dvd_pow hpow)
      omega
    · have hmod : (p - 1) % 5 = 0 := Nat.dvd_iff_mod_eq_zero.mp hpred
      have hpmod : p % 5 = 1 := calc
        p % 5 = ((p - 1) + 1) % 5 := by
          exact congrArg (fun n : ℕ => n % 5) (by omega)
        _ = ((p - 1) % 5 + 1 % 5) % 5 := Nat.add_mod _ _ _
        _ = 1 := by rw [hmod] <;> rfl
      omega
  letI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcard : Nat.card (ZMod (p ^ e))ˣ = Nat.totient (p ^ e) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hcop_units : (Nat.card (ZMod (p ^ e))ˣ).Coprime 5 := by
    rw [hcard]
    exact hcop
  have hsurj : Function.Surjective (fun x : (ZMod (p ^ e))ˣ => x ^ 5) :=
    (Nat.Coprime.pow_left_bijective hcop_units).surjective
  unfold OMA.S_oeis_a293482.a
  rw [Set.range_eq_univ.mpr hsurj]
  calc
    Nat.card (Set.univ : Set (ZMod (p ^ e))ˣ) =
        Nat.card (ZMod (p ^ e))ˣ := Nat.card_congr (Equiv.Set.univ _)
    _ = Nat.totient (p ^ e) := hcard
    _ = (p - 1) * p ^ (e - 1) := htot.trans (Nat.mul_comm _ _)

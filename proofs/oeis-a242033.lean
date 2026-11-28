import OMAStatements.S_oeis_a242033

-- Problem: A242033 contains every odd prime (Robert Israel's construction via Dirichlet's theorem).
-- Credit: @bnb9001

namespace OMA_A242033_Proof

open OMA.S_oeis_a242033

theorem exists_term {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ m, IsTerm m ∧ Nat.minFac (m - 1) = p := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set M := (p - 1).factorial with hMdef
  have hM : 0 < M := Nat.factorial_pos _
  haveI : NeZero M := ⟨hM.ne'⟩
  have hcop : Nat.Coprime p M := by
    apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
    intro h
    have := (Nat.Prime.dvd_factorial hp).mp h
    omega
  set u : (ZMod M)ˣ := ZMod.unitOfCoprime p hcop
  obtain ⟨q, hqp, hq, hqu⟩ := Nat.forall_exists_prime_gt_and_eq_mod (u⁻¹).isUnit p
  have hmodM : p * q ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [hqu]
    have : ((p : ℕ) : ZMod M) = (u : ZMod M) := by simp [u]
    rw [this, Units.mul_inv]
  have hq2 : q ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hpq : Odd (p * q) := hpodd.mul hqodd
  have hq5 : 5 ≤ q := by rcases hqodd with ⟨t, ht⟩; omega
  have hpq15 : 15 ≤ p * q := by
    have := Nat.mul_le_mul hp3 hq5; omega
  -- least prime factor of p*q is p
  have hmin1 : Nat.minFac (p * q) = p := by
    apply le_antisymm
    · exact Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q)
    · have hpr : (Nat.minFac (p * q)).Prime := Nat.minFac_prime (by omega)
      have hd : Nat.minFac (p * q) ∣ p * q := Nat.minFac_dvd _
      rcases (Nat.Prime.dvd_mul hpr).mp hd with h | h
      · exact le_of_eq ((Nat.prime_dvd_prime_iff_eq hpr hp).mp h).symm
      · rw [(Nat.prime_dvd_prime_iff_eq hpr hq).mp h]; omega
  -- least prime factor of p*q - 2 exceeds p
  have hmin2 : p < Nat.minFac (p * q - 2) := by
    set r := Nat.minFac (p * q - 2) with hr
    have hrp : r.Prime := Nat.minFac_prime (by omega)
    have hrd : r ∣ p * q - 2 := Nat.minFac_dvd _
    by_contra hle
    rw [not_lt] at hle
    rcases Nat.lt_or_ge r p with hlt | hge
    · have hrM : r ∣ M := Nat.dvd_factorial hrp.pos (by omega)
      have hmodr : p * q ≡ 1 [MOD r] := Nat.ModEq.of_dvd hrM hmodM
      have h1 : r ∣ p * q - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hmodr.symm
      have h2 : r ∣ (p * q - 1) - (p * q - 2) := Nat.dvd_sub h1 hrd
      rw [show (p * q - 1) - (p * q - 2) = 1 by omega] at h2
      exact hrp.one_lt.ne' (Nat.dvd_one.mp h2)
    · have hreq : r = p := le_antisymm hle hge
      rw [hreq] at hrd
      have h2 : p ∣ p * q - (p * q - 2) := Nat.dvd_sub (dvd_mul_right p q) hrd
      rw [show p * q - (p * q - 2) = 2 by omega] at h2
      have := Nat.le_of_dvd (by norm_num) h2
      omega
  refine ⟨p * q + 1, ⟨?_, by omega, ?_⟩, ?_⟩
  · rcases hpq with ⟨t, ht⟩; exact ⟨t + 1, by omega⟩
  · rw [show p * q + 1 - 1 = p * q by omega, show p * q + 1 - 3 = p * q - 2 by omega, hmin1]
    exact hmin2
  · rw [show p * q + 1 - 1 = p * q by omega, hmin1]

end OMA_A242033_Proof

open OMA.S_oeis_a242033 OMA_A242033_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a242033.main := by
  intro p hp hp2
  classical
  obtain ⟨m, hm, hmp⟩ := exists_term hp hp2
  refine ⟨Nat.count IsTerm m + 1, by omega, ?_⟩
  unfold a seq
  rw [Nat.add_sub_cancel, Nat.nth_count hm, hmp]

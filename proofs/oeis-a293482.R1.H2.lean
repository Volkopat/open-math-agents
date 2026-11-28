import OMAReductions.R_oeis_a293482_R1

-- OEIS A293482, formula section: https://oeis.org/A293482/internal
-- Reduction by @Ciphore. Credit for this proof: @grp06.

open OMA.S_oeis_a293482

private theorem fifthPowerCountPrimePow (p e : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    a (p ^ e) = Nat.totient (p ^ e) / Nat.gcd (Nat.totient (p ^ e)) 5 := by
  letI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  letI : IsCyclic (ZMod (p ^ e))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  letI : Fintype (ZMod (p ^ e))ˣ := Fintype.ofFinite _
  have h := IsCyclic.card_powMonoidHom_range (ZMod (p ^ e))ˣ 5
  change Nat.card (Set.range fun x : (ZMod (p ^ e))ˣ => x ^ 5) = _ at h
  simpa only [a, Nat.card_eq_fintype_card (α := (ZMod (p ^ e))ˣ),
    ZMod.card_units_eq_totient] using h

theorem OMA.solution : OMA.R_oeis_a293482_R1.H2 := by
  have hp : Nat.Prime 5 := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by decide
  change a 5 = 4 ∧ ∀ e : ℕ, 1 < e → a (5 ^ e) = 4 * 5 ^ (e - 2)
  constructor
  · have h := fifthPowerCountPrimePow 5 1 hp hp2
    rw [pow_one, Nat.totient_prime hp] at h
    norm_num at h
    exact h
  · intro e he
    have hexp : e - 1 = (e - 2) + 1 := by omega
    have hphi : Nat.totient (5 ^ e) = (4 * 5 ^ (e - 2)) * 5 := by
      rw [Nat.totient_prime_pow hp (n := e) (by omega), hexp, pow_succ]
      change (5 ^ (e - 2) * 5) * 4 = (4 * 5 ^ (e - 2)) * 5
      ac_rfl
    have hdvd : 5 ∣ Nat.totient (5 ^ e) := by
      refine ⟨4 * 5 ^ (e - 2), hphi.trans (Nat.mul_comm _ _)⟩
    rw [fifthPowerCountPrimePow 5 e hp hp2, Nat.gcd_eq_right hdvd, hphi]
    exact Nat.mul_div_cancel _ (by decide)

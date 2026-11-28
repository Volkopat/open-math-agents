import OMAStatements.S_mse_2360165
import Mathlib.FieldTheory.Finite.Basic

open Filter OMA.S_mse_2360165

/-- If φ(m) is small, use Euler's theorem with a prime larger than φ(m). -/
private theorem eventually_le_totient (B : ℕ) : ∀ᶠ m : ℕ in atTop, B ≤ m.totient := by
  obtain ⟨p, hBp, hp⟩ := Nat.exists_infinite_primes (B + 1)
  filter_upwards [eventually_ge_atTop (p ^ B + 2)] with m hm
  by_contra! hsmall
  have hpos : 0 < m.totient := Nat.totient_pos.mpr (by omega)
  have hcop : p.Coprime m := hp.coprime_iff_not_dvd.mpr fun hd => by
    have h := Nat.le_of_dvd hpos (Nat.totient_dvd_of_dvd hd)
    rw [Nat.totient_prime hp] at h
    omega
  have hpow := Nat.pow_le_pow_right hp.pos hsmall.le
  have heq := (Nat.ModEq.pow_totient hcop).eq_of_lt_of_lt (by omega) (by omega)
  exact (Nat.one_lt_pow hpos.ne' hp.one_lt).ne' heq

theorem OMA.solution : type_of% @OMA.S_mse_2360165.main := by
  intro n _ _
  apply le_liminf_of_le (by isBoundedDefault)
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_le_totient n.totient)
  filter_upwards [eventually_ge_atTop M] with k hk
  exact_mod_cast hM (n + k + 1) (by omega)

import OMAReductions.R_mse_1416221_R1
import Mathlib

/-!
# Local obstructions to the converse of Reix's test

Credit: @jacklarmer

The trace factorization from the original discussion, MathOverflow 216174,
holds even when the modulus is composite. For L = 2^(q-1), the integer
factors 9^(L-1)-1 and 9^(L+1)-1 have greatest common divisor 8. Each
odd prime power dividing the Mersenne number therefore belongs wholly to
one factor. Different prime powers may belong to different factors.

H1 isolates base-3 Fermat pseudoprimes of Mersenne form. Any such number
would pass Reix's test. H2 concerns only numbers that fail the Fermat test.
The order lemma eliminates those with a prime-power divisor p^k, p > 3,
for which 9^(p-1) is not 1 modulo p^k.
-/

namespace ReixTrace

/-- A return of the doubled trace is equivalent to the vanishing of a product.
    Cancellation uses only the given unit, so the ring may have zero divisors. -/
theorem return_iff_product {R : Type*} [CommRing R] (b : Rˣ) (s : ℕ → R)
    (seed : s 0 = (b : R) + ↑(b⁻¹)) (step : ∀ j, s (j + 1) = s j ^ 2 - 2) (i : ℕ) :
    s i = s 0 ↔
      ((b : R) ^ (2 ^ i - 1) - 1) * ((b : R) ^ (2 ^ i + 1) - 1) = 0 := by
  have doubleTrace (u : Rˣ) : ((u : R) + ↑(u⁻¹)) ^ 2 - 2 =
      ↑(u ^ 2) + (↑((u ^ 2)⁻¹) : R) := by
    rw [← inv_pow]
    simp only [Units.val_pow_eq_pow_val]
    linear_combination 2 * u.mul_inv
  have closed (j : ℕ) : s j = ↑(b ^ (2 ^ j)) + (↑((b ^ (2 ^ j))⁻¹) : R) := by
    induction j with
    | zero => simpa using seed
    | succ j ih =>
      rw [step, ih, pow_succ (2 : ℕ) j, pow_mul]
      exact doubleTrace _
  rw [closed i, seed]
  let k := 2 ^ i - 1
  have hk : 2 ^ i = k + 1 := by
    have hp : 0 < (2 : ℕ) ^ i := pow_pos (by decide) _
    dsimp [k]
    omega
  rw [hk]
  simp only [Nat.add_sub_cancel]
  let u := b ^ (k + 1)
  change (u : R) + ↑(u⁻¹) = (b : R) + ↑(b⁻¹) ↔ _
  have lower : (u : R) * ↑(b⁻¹) = (b : R) ^ k := by
    dsimp only [u]
    rw [Units.val_pow_eq_pow_val, pow_succ, Units.mul_inv_cancel_right]
  have upper : (u : R) * b = (b : R) ^ (k + 1 + 1) := by
    rw [pow_succ _ (k + 1)]
    rfl
  have factor : ((u : R) + ↑(u⁻¹) - ((b : R) + ↑(b⁻¹))) * u =
      ((u : R) * ↑(b⁻¹) - 1) * ((u : R) * b - 1) := by
    linear_combination u.inv_mul - (u : R) ^ 2 * b.inv_mul
  constructor
  · intro h
    rw [← lower, ← upper, ← factor, h, sub_self, zero_mul]
  · intro h
    apply sub_eq_zero.mp
    apply u.mul_left_inj.mp
    rwa [zero_mul, factor, lower, upper]

end ReixTrace

namespace ReixLocal

theorem nine_order_dvd_iff (d r : ℕ) :
    orderOf (9 : ZMod d) ∣ r ↔ d ∣ 9 ^ r - 1 := by
  rw [orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff]
  rw [Nat.cast_sub (by exact Nat.one_le_pow r 9 (by decide)), Nat.cast_pow]
  norm_num [sub_eq_zero]

theorem factor_criterion {M L : ℕ} (hM : Odd M) (hL : Even L) (hpos : 0 < L) :
    M ∣ (9 ^ (L - 1) - 1) * (9 ^ (L + 1) - 1) ↔
      ∀ p e : ℕ, p.Prime → p ^ e ∣ M →
        orderOf (9 : ZMod (p ^ e)) ∣ L - 1 ∨ orderOf (9 : ZMod (p ^ e)) ∣ L + 1 := by
  have hc : Nat.Coprime (L - 1) (L + 1) := by
    rw [show L + 1 = (L - 1) + 2 by omega, Nat.coprime_self_add_right, Nat.coprime_two_right]
    obtain ⟨k, hk⟩ := hL
    exact ⟨k - 1, by omega⟩
  have hg : Nat.gcd (9 ^ (L - 1) - 1) (9 ^ (L + 1) - 1) = 8 := by
    rw [Nat.pow_sub_one_gcd_pow_sub_one, hc.gcd_eq_one]
    decide
  simp only [nine_order_dvd_iff]
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  constructor
  · intro h p e hp hpe
    cases e with
    | zero => simp
    | succ e =>
      have hpm : p ∣ M := (dvd_pow_self p (Nat.succ_ne_zero e)).trans hpe
      have hnot : ¬p ∣ 8 := by
        intro h8
        have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 3) (by simpa using h8)
        have heq : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hp2 |>.resolve_left hp.ne_one
        subst p
        exact (Nat.not_even_iff_odd.mpr hM) (even_iff_two_dvd.mpr hpm)
      have hprod := h p (e+1) hp hpe
      by_cases hleft : p ∣ 9 ^ (L - 1) - 1
      · have hright : ¬p ∣ 9 ^ (L + 1) - 1 := by
          intro hb
          exact hnot (hg ▸ Nat.dvd_gcd hleft hb)
        exact Or.inl (hp.prime.pow_dvd_of_dvd_mul_right _ hright hprod)
      · exact Or.inr (hp.prime.pow_dvd_of_dvd_mul_left _ hleft hprod)
  · intro h p e hp hpe
    rcases h p e hp hpe with ha | hb
    · exact dvd_mul_of_dvd_left ha _
    · exact dvd_mul_of_dvd_right hb _

end ReixLocal

namespace ReixLocal

theorem seed_return_iff (q : ℕ) (hq : q.Prime) (hq2 : 2 < q) :
    OMA.S_mse_1416221.S q (q - 1) = OMA.S_mse_1416221.S q 0 ↔
    ∀ p e : ℕ, p.Prime → p ^ e ∣ mersenne q →
      orderOf (9 : ZMod (p ^ e)) ∣ 2 ^ (q - 1) - 1 ∨
      orderOf (9 : ZMod (p ^ e)) ∣ 2 ^ (q - 1) + 1 := by
  have hmod := mersenne_mod_three (hq.odd_of_ne_two (by omega)) (by omega)
  have hc : Nat.Coprime 3 (mersenne q) := Nat.prime_three.coprime_iff_not_dvd.mpr (by
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    omega)
  have hc9 : Nat.Coprime 9 (mersenne q) := by simpa using hc.pow_left 2
  let b := ZMod.unitOfCoprime 9 hc9
  have hseed : OMA.S_mse_1416221.S q 0 = (b : ZMod (mersenne q)) + ↑(b⁻¹) := rfl
  rw [ReixTrace.return_iff_product b (OMA.S_mse_1416221.S q) hseed (fun _ => rfl)]
  have hEven : Even ((2 : ℕ) ^ (q - 1)) := (even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega)))
  rw [← factor_criterion (mersenne_odd.mpr (by omega)) hEven (by positivity)]
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul,
      Nat.cast_sub (Nat.one_le_pow _ 9 (by decide)), Nat.cast_sub (Nat.one_le_pow _ 9 (by decide))]
  simp [b]

end ReixLocal

namespace ReixLocal

theorem mersenne_fermat_factor {q : ℕ} (hq : 2 < q) :
    9^(2^(q-1)-1) = 3^(mersenne q-1) := by
  have hq1 : q = (q-1)+1 := by omega
  have hm : mersenne q = 2^(q-1)*2-1 := by
    unfold mersenne
    conv_lhs => rw [hq1, pow_succ]
  have hpos : 0 < (2 : ℕ)^(q-1) := pow_pos (by decide) _
  rw [show (9 : ℕ) = 3^2 by decide, ← pow_mul, hm]
  congr 1
  omega

end ReixLocal

namespace ReixLocal

/-- A composite Mersenne number passing the base-3 Fermat test would itself
    be a counterexample to the proposed seed-return test. -/
theorem fermat_pass_implies_seed_return (q : ℕ) (hq : q.Prime) (hq2 : 2 < q)
    (hF : mersenne q ∣ 3 ^ (mersenne q - 1) - 1) :
    OMA.S_mse_1416221.S q (q - 1) = OMA.S_mse_1416221.S q 0 := by
  apply (seed_return_iff q hq hq2).mpr
  intro p e _ hd
  apply Or.inl
  apply (nine_order_dvd_iff _ _).mpr
  rw [mersenne_fermat_factor hq2]
  exact hd.trans hF

end ReixLocal

namespace ReixLocal

theorem order_dvd_factor_minus_one {p e L : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hL : 0 < L) (hm : p^(e+1) ∣ 2*L-1)
    (ha : orderOf (9 : ZMod (p^(e+1))) ∣ L-1 ∨
      orderOf (9 : ZMod (p^(e+1))) ∣ L+1) :
    orderOf (9 : ZMod (p^(e+1))) ∣ p-1 := by
  have hpm : p ∣ 2*L-1 := (dvd_pow_self p (Nat.succ_ne_zero e)).trans hm
  have hpc : Nat.Coprime 9 p := by
    have h3 : Nat.Coprime p 3 := hp.coprime_iff_not_dvd.mpr (fun h => by
      have := Nat.le_of_dvd (by decide : 0 < 3) h
      omega)
    simpa using (h3.symm.pow_left 2)
  have hord : Nat.Coprime (orderOf (9 : ZMod (p^(e+1)))) p := by
    refine (hp.coprime_iff_not_dvd.mpr ?_).symm
    intro hd
    rcases ha with h | h
    · have h2 := dvd_mul_of_dvd_right (hd.trans h) 2
      have h1 := Nat.dvd_sub hpm h2
      rw [show 2*L-1-2*(L-1) = 1 by omega] at h1
      exact hp.not_dvd_one h1
    · have h2 := dvd_mul_of_dvd_right (hd.trans h) 2
      have h3 := Nat.dvd_sub h2 hpm
      rw [show 2*(L+1)-(2*L-1) = 3 by omega] at h3
      have := Nat.le_of_dvd (by decide : 0 < 3) h3
      omega
  apply (hord.pow_right e).dvd_of_dvd_mul_left
  rw [← Nat.totient_prime_pow_succ hp]
  apply orderOf_dvd_of_pow_eq_one
  have ht := Nat.ModEq.pow_totient (hpc.pow_right (e+1))
  simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr ht

end ReixLocal

namespace OMA.R_mse_1416221_R1_H2_R1

/-- Exclude base-3 Fermat pseudoprimes among Mersenne numbers of odd prime exponent. -/
def H1 : Prop := ∀ q : ℕ, q.Prime → 2 < q →
  mersenne q ∣ 3 ^ (mersenne q - 1) - 1 → (mersenne q).Prime

/-- Among numbers failing the base-3 Fermat test, supply a prime-power obstruction.
    It suffices to consider those for which the indicated base-9 congruences hold:
    the proof below eliminates any number with a prime power failing one of them. -/
def H2 : Prop := ∀ q : ℕ, q.Prime → 2 < q →
  ¬(mersenne q ∣ 3 ^ (mersenne q - 1) - 1) →
  (∀ p e : ℕ, p.Prime → 3 < p → p ^ (e + 1) ∣ mersenne q → p ^ (e + 1) ∣ 9 ^ (p - 1) - 1) →
  ∃ p e : ℕ, p.Prime ∧ p ^ e ∣ mersenne q ∧
    ¬(orderOf (9 : ZMod (p ^ e)) ∣ 2 ^ (q - 1) - 1) ∧
    ¬(orderOf (9 : ZMod (p ^ e)) ∣ 2 ^ (q - 1) + 1)

theorem main : H1 → H2 → OMA.R_mse_1416221_R1.H2 := by
  intro fermat obstruction q hq hq2 hreturn
  by_cases hF : mersenne q ∣ 3 ^ (mersenne q - 1) - 1
  · exact fermat q hq hq2 hF
  have hlocal := (ReixLocal.seed_return_iff q hq hq2).mp hreturn
  have hM : mersenne q = 2 * 2 ^ (q - 1) - 1 := by
    unfold mersenne
    conv_lhs => rw [show q = q - 1 + 1 by omega, pow_succ]
    omega
  have hr (p e : ℕ) (hp : p.Prime) (hp3 : 3 < p) (hd : p ^ (e + 1) ∣ mersenne q) :
      p ^ (e + 1) ∣ 9 ^ (p - 1) - 1 := by
    apply (ReixLocal.nine_order_dvd_iff _ _).mp
    exact ReixLocal.order_dvd_factor_minus_one hp hp3 (by positivity)
      (hM ▸ hd) (hlocal p (e+1) hp hd)
  obtain ⟨p, e, hp, hd, hminus, hplus⟩ := obstruction q hq hq2 hF hr
  exact False.elim ((hlocal p e hp hd).elim hminus hplus)

end OMA.R_mse_1416221_R1_H2_R1

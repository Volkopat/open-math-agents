import OMAStatements.S_mo_235576
import Mathlib.Algebra.Ring.GeomSum

/-!
# The prime-power case of MathOverflow 235576

For `b = p^k`, the proper divisors of `b²` are the powers of `p` with
exponents below `2k`. The geometric sum shows that the quotient is `p - 1`.
The remaining two questions concern numbers with multiple distinct prime
factors, for quotient two and for odd prime quotients respectively.
-/

namespace OMA.R_mo_235576_R1

open OMA.S_mo_235576

private theorem quotient_of_prime_power {p k q : ℕ} (hp : p.Prime) (hk : 0 < k)
    (heq : (p ^ k) ^ 2 - 1 = q * properSigmaSq (p ^ k)) : q = p - 1 := by
  let s := ∑ j ∈ Finset.range (k * 2), p ^ j
  have hsum : properSigmaSq (p ^ k) = s := by
    unfold properSigmaSq
    rw [← pow_mul, ArithmeticFunction.sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
    exact Nat.add_sub_cancel _ _
  have hgeom : s * (p - 1) = p ^ (k * 2) - 1 :=
    geom_sum_mul_of_one_le (show 1 ≤ p from hp.one_lt.le) _
  have hpos : 0 < s := by
    have hterm := Finset.single_le_sum (f := fun j : ℕ => p ^ j)
      (fun j _ => Nat.zero_le (p ^ j)) (Finset.mem_range.mpr (show 0 < k * 2 by omega))
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (by simpa [s] using hterm)
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hsum, ← pow_mul] at heq
  exact heq.symm.trans (hgeom.symm.trans (Nat.mul_comm _ _))

/-- A prime divisor `p` of `b` supplies the proper divisor `b² / p`.
Consequently the quotient is smaller than even the least prime divisor. -/
private theorem quotient_lt_minFac {b q : ℕ} (hb : 1 < b)
    (heq : b ^ 2 - 1 = q * properSigmaSq b) : q < b.minFac := by
  obtain ⟨t, ht⟩ := Nat.minFac_dvd b
  let d := t * b
  have hprod : b ^ 2 = d * b.minFac := by
    calc
      b ^ 2 = b * b := pow_two b
      _ = (b.minFac * t) * b := congrArg (fun x => x * b) ht
      _ = d * b.minFac := by dsimp [d]; ac_rfl
  have hsquare : 0 < b ^ 2 := Nat.pow_pos (by omega)
  have hdpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd
    simp [hd] at hprod
    omega
  have hd : d ∈ (b ^ 2).properDivisors := by
    refine Nat.mem_properDivisors.mpr ⟨⟨b.minFac, hprod⟩, ?_⟩
    rw [hprod]
    exact lt_mul_of_one_lt_right hdpos (Nat.minFac_prime (by omega)).one_lt
  have hle : d ≤ properSigmaSq b := by
    unfold properSigmaSq
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self,
      Nat.add_sub_cancel]
    exact Finset.single_le_sum (fun x _ => Nat.zero_le x) hd
  apply Nat.lt_of_not_ge
  intro hbad
  have h := Nat.mul_le_mul hbad hle
  rw [Nat.mul_comm b.minFac d, ← hprod, ← heq] at h
  omega

/-- Exclude quotient two when the input has multiple distinct prime factors. -/
def H1 : Prop := ∀ b : ℕ, Odd b → 1 < b → ¬ IsPrimePow b →
    b ^ 2 - 1 ≠ 2 * properSigmaSq b

/-- Exclude odd prime quotients for the same remaining inputs. -/
def H2 : Prop := ∀ b q : ℕ, Odd b → 1 < b → ¬ IsPrimePow b →
    q.Prime → 2 < q → q < b.minFac → b ^ 2 - 1 ≠ q * properSigmaSq b

theorem main : H1 → H2 → type_of% @OMA.S_mo_235576.main := by
  intro htwo hodd b q hbodd hb hbcomp hq heq
  by_cases hpow : IsPrimePow b
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff b).mp hpow
    have hquot := quotient_of_prime_power hp hk heq
    have hp3 : p = 3 := by
      have := hq.two_le
      rcases hp.eq_two_or_odd with h | h <;> rcases hq.eq_two_or_odd with h' | h' <;> omega
    refine ⟨k, ?_, by rw [hp3]⟩
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact hbcomp (by simpa using hp)
    omega
  · rcases hq.eq_two_or_odd with rfl | _
    · exact (htwo b hbodd hb hpow heq).elim
    · have := hq.two_le
      exact (hodd b q hbodd hb hpow hq (by omega) (quotient_lt_minFac hb heq) heq).elim

end OMA.R_mo_235576_R1

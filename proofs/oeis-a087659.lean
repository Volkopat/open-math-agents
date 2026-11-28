import OMAStatements.S_oeis_a087659
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a087659

open OMA.S_oeis_a087659

/-- Core floor inequality for every modulus `q ≥ 2` and `a, k : ℕ`:
`a/q + k/q + (k+1)/q + (k+2)/q + (a+k+3)/q ≤ (a+3k+3)/q + (a+k)/q + (if q = 2 then 1 else 0)`. -/
private lemma floor_ineq (q a k : ℕ) (hq : 2 ≤ q) :
    a / q + k / q + (k + 1) / q + (k + 2) / q + (a + k + 3) / q ≤
      (a + 3 * k + 3) / q + (a + k) / q + (if q = 2 then 1 else 0) := by
  have hq0 : 0 < q := by omega
  set qa := a / q
  set ra := a % q
  set qk := k / q
  set rk := k % q
  have ha : a = q * qa + ra := (Nat.div_add_mod a q).symm
  have hk : k = q * qk + rk := (Nat.div_add_mod k q).symm
  have hra : ra < q := Nat.mod_lt a hq0
  have hrk : rk < q := Nat.mod_lt k hq0
  have hdiv_add : ∀ c r : ℕ, (q * c + r) / q = c + r / q := fun c r =>
    Nat.mul_add_div hq0 c r
  have hd1 : (k + 1) / q = qk + (rk + 1) / q := by
    rw [show k + 1 = q * qk + (rk + 1) by linarith, hdiv_add]
  have hd2 : (k + 2) / q = qk + (rk + 2) / q := by
    rw [show k + 2 = q * qk + (rk + 2) by linarith, hdiv_add]
  have hd3 : (a + k + 3) / q = (qa + qk) + (ra + rk + 3) / q := by
    rw [show a + k + 3 = q * (qa + qk) + (ra + rk + 3) by linarith, hdiv_add]
  have hd4 : (a + 3 * k + 3) / q = (qa + 3 * qk) + (ra + 3 * rk + 3) / q := by
    rw [show a + 3 * k + 3 = q * (qa + 3 * qk) + (ra + 3 * rk + 3) by linarith, hdiv_add]
  have hd5 : (a + k) / q = (qa + qk) + (ra + rk) / q := by
    rw [show a + k = q * (qa + qk) + (ra + rk) by linarith, hdiv_add]
  rw [hd1, hd2, hd3, hd4, hd5]
  -- Reduce to remainders ra, rk < q
  suffices hrem : (rk + 1) / q + (rk + 2) / q + (ra + rk + 3) / q ≤
      (ra + 3 * rk + 3) / q + (ra + rk) / q + (if q = 2 then 1 else 0) by
    omega
  by_cases hq2 : q = 2
  · subst hq2
    simp only [ite_true]
    have hcases_a : ra = 0 ∨ ra = 1 := by omega
    have hcases_k : rk = 0 ∨ rk = 1 := by omega
    rcases hcases_a with ha_eq | ha_eq <;> rcases hcases_k with hk_eq | hk_eq <;>
      simp only [ha_eq, hk_eq] <;> omega
  · simp only [if_neg hq2, add_zero]
    have hq3 : 3 ≤ q := by omega
    -- Case split on rk relative to q - 2 and q - 1
    by_cases hrk1 : rk + 2 < q
    · -- Then (rk + 1) / q = 0 and (rk + 2) / q = 0!
      have z1 : (rk + 1) / q = 0 := Nat.div_eq_of_lt (by omega)
      have z2 : (rk + 2) / q = 0 := Nat.div_eq_of_lt hrk1
      have hmono : (ra + rk + 3) / q ≤ (ra + 3 * rk + 3) / q :=
        Nat.div_le_div_right (by omega)
      rw [z1, z2]
      linarith [Nat.zero_le ((ra + rk) / q)]
    · by_cases hrk2 : rk + 1 < q
      · -- rk = q - 2
        have hrkeq : rk = q - 2 := by omega
        have z1 : (rk + 1) / q = 0 := Nat.div_eq_of_lt hrk2
        have z2 : (rk + 2) / q = 1 := by
          rw [show rk + 2 = q by omega, Nat.div_self hq0]
        rw [z1, z2]
        by_cases hsum : ra + rk < q
        · -- ra ≤ 1
          have h1 : (ra + rk + 3) / q = 1 := by
            apply le_antisymm
            · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hq0).mpr (by omega))
            · exact (Nat.le_div_iff_mul_le hq0).mpr (by omega)
          have h2 : 2 ≤ (ra + 3 * rk + 3) / q := (Nat.le_div_iff_mul_le hq0).mpr (by omega)
          rw [h1]
          linarith [Nat.zero_le ((ra + rk) / q)]
        · -- ra + rk ≥ q, so (ra + rk) / q ≥ 1 and (ra + rk + 3) / q ≤ 2 and (ra + 3*rk + 3) / q ≥ 2
          have h1 : (ra + rk + 3) / q ≤ 2 :=
            Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hq0).mpr (by omega))
          have h2 : 1 ≤ (ra + rk) / q := (Nat.le_div_iff_mul_le hq0).mpr (by omega)
          have h3 : 2 ≤ (ra + 3 * rk + 3) / q := (Nat.le_div_iff_mul_le hq0).mpr (by omega)
          linarith
      · -- rk = q - 1
        have hrkeq : rk = q - 1 := by omega
        have z1 : (rk + 1) / q = 1 := by
          rw [show rk + 1 = q by omega, Nat.div_self hq0]
        have z2 : (rk + 2) / q = 1 := by
          apply le_antisymm
          · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hq0).mpr (by omega))
          · exact (Nat.le_div_iff_mul_le hq0).mpr (by omega)
        rw [z1, z2]
        by_cases hra0 : ra = 0
        · rw [hra0]
          have h1 : (0 + rk + 3) / q = 1 := by
            apply le_antisymm
            · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hq0).mpr (by omega))
            · exact (Nat.le_div_iff_mul_le hq0).mpr (by omega)
          have h2 : 3 ≤ (0 + 3 * rk + 3) / q := (Nat.le_div_iff_mul_le hq0).mpr (by omega)
          rw [h1]
          linarith [Nat.zero_le ((0 + rk) / q)]
        · -- ra ≥ 1, so ra + rk ≥ q -> (ra + rk) / q ≥ 1, (ra + 3*rk + 3) / q ≥ 3, (ra + rk + 3) / q ≤ 2
          have h1 : (ra + rk + 3) / q ≤ 2 :=
            Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hq0).mpr (by omega))
          have h2 : 1 ≤ (ra + rk) / q := (Nat.le_div_iff_mul_le hq0).mpr (by omega)
          have h3 : 3 ≤ (ra + 3 * rk + 3) / q := (Nat.le_div_iff_mul_le hq0).mpr (by omega)
          linarith

/-- Equivalently: `a! * k! * (k+1)! * (k+2)! * (a+k+3)! ∣ 2 * (a+k)! * (a+3k+3)!`. -/
private lemma factorial_dvd_aux (a k : ℕ) :
    (a.factorial * k.factorial * (k + 1).factorial * (k + 2).factorial * (a + k + 3).factorial) ∣
      (2 * (a + k).factorial * (a + 3 * k + 3).factorial) := by
  have hL0 : a.factorial * k.factorial * (k + 1).factorial * (k + 2).factorial * (a + k + 3).factorial ≠ 0 := by
    positivity
  have hR0 : 2 * (a + k).factorial * (a + 3 * k + 3).factorial ≠ 0 := by
    positivity
  rw [← Nat.factorization_le_iff_dvd hL0 hR0]
  intro p
  by_cases hp : p.Prime
  · have : Fact p.Prime := ⟨hp⟩
    have hfac_eq : ∀ m : ℕ, m.factorial.factorization p = padicValNat p m.factorial := fun m =>
      Nat.factorization_def m.factorial hp
    have hLfac :
        (a.factorial * k.factorial * (k + 1).factorial * (k + 2).factorial * (a + k + 3).factorial).factorization p =
          padicValNat p a.factorial + padicValNat p k.factorial + padicValNat p (k + 1).factorial +
          padicValNat p (k + 2).factorial + padicValNat p (a + k + 3).factorial := by
      rw [Nat.factorization_mul (by positivity) (by positivity),
          Nat.factorization_mul (by positivity) (by positivity),
          Nat.factorization_mul (by positivity) (by positivity),
          Nat.factorization_mul (by positivity) (by positivity)]
      simp only [Finsupp.coe_add, Pi.add_apply, hfac_eq]
    have hRfac :
        (2 * (a + k).factorial * (a + 3 * k + 3).factorial).factorization p =
          (2 : ℕ).factorization p + padicValNat p (a + k).factorial + padicValNat p (a + 3 * k + 3).factorial := by
      rw [Nat.factorization_mul (by positivity) (by positivity),
          Nat.factorization_mul (by decide) (by positivity)]
      simp only [Finsupp.coe_add, Pi.add_apply, hfac_eq]
    rw [hLfac, hRfac]
    -- Choose a common bound b large enough for Legendre's formula on all 7 factorials
    set b : ℕ := a + 3 * k + 4
    have hlt_log : ∀ m : ℕ, m < b → Nat.log p m < b := fun m hm => by
      by_cases hm0 : m = 0
      · subst hm0; simp; omega
      · exact Nat.log_lt_of_lt_pow hm0 (lt_of_lt_of_le hm (le_of_lt (Nat.lt_pow_self hp.one_lt)))
    have hleg : ∀ m : ℕ, m < b →
        padicValNat p m.factorial = ∑ j ∈ Finset.Ico 1 b, m / p ^ j := fun m hm =>
      padicValNat_factorial (hlt_log m hm)
    rw [hleg a (by omega), hleg k (by omega), hleg (k + 1) (by omega),
        hleg (k + 2) (by omega), hleg (a + k + 3) (by omega),
        hleg (a + k) (by omega), hleg (a + 3 * k + 3) (by omega)]
    -- Rewrite (2 : ℕ).factorization p as ∑ j ∈ Ico 1 b, if p^j = 2 then 1 else 0
    have htwo : (2 : ℕ).factorization p = ∑ j ∈ Finset.Ico 1 b, (if p ^ j = 2 then 1 else 0) := by
      by_cases hp2 : p = 2
      · subst hp2
        have h1 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
        rw [h1]
        have hmem : (1 : ℕ) ∈ Finset.Ico 1 b := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
        rw [Finset.sum_eq_single 1]
        · simp
        · intro j hj hne
          rw [Finset.mem_Ico] at hj
          have hgt : 2 < 2 ^ j := by
            have h2j : 2 ≤ j := by omega
            calc 2 < 2 ^ 2 := by decide
              _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h2j
          exact if_neg (by omega)
        · intro hnot; exact absurd hmem hnot
      · have h0 : (2 : ℕ).factorization p = 0 :=
          Nat.factorization_eq_zero_of_not_dvd (fun hd =>
            hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd))
        rw [h0]
        symm
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.mem_Ico] at hj
        have hgt : 2 < p ^ j := by
          have hp3 : 3 ≤ p := by
            have := hp.two_le; omega
          calc 2 < 3 := by decide
            _ ≤ p := hp3
            _ = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ j := Nat.pow_le_pow_right hp.pos hj.1
        exact if_neg (by omega)
    rw [htwo]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hge2 : 2 ≤ p ^ j := by
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ j := Nat.pow_le_pow_right hp.pos hj.1
    have hfl := floor_ineq (p ^ j) a k hge2
    omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private lemma prove_main :
    ∀ n i : ℕ, i ≤ n →
      ((i + 1).factorial * (i + 2).factorial * (n + 3).factorial) ∣
        (2 * Nat.choose n i * (n + 2 * i + 3).factorial) := by
  intro n i hin
  have haux := factorial_dvd_aux (n - i) i
  have h1 : n - i + i = n := by omega
  have h2 : n - i + 3 * i + 3 = n + 2 * i + 3 := by omega
  rw [h1, h2] at haux
  have hch : Nat.choose n i * (i.factorial * (n - i).factorial) = n.factorial := by
    have := Nat.choose_mul_factorial_mul_factorial hin
    linarith
  have hmul_dvd :
      ((n - i).factorial * i.factorial) * ((i + 1).factorial * (i + 2).factorial * (n + 3).factorial) ∣
        ((n - i).factorial * i.factorial) * (2 * Nat.choose n i * (n + 2 * i + 3).factorial) := by
    have hL : ((n - i).factorial * i.factorial) * ((i + 1).factorial * (i + 2).factorial * (n + 3).factorial) =
        (n - i).factorial * i.factorial * (i + 1).factorial * (i + 2).factorial * (n + 3).factorial := by ring
    have hR : ((n - i).factorial * i.factorial) * (2 * Nat.choose n i * (n + 2 * i + 3).factorial) =
        2 * n.factorial * (n + 2 * i + 3).factorial := by
      calc ((n - i).factorial * i.factorial) * (2 * Nat.choose n i * (n + 2 * i + 3).factorial)
          = 2 * (Nat.choose n i * (i.factorial * (n - i).factorial)) * (n + 2 * i + 3).factorial := by ring
        _ = 2 * n.factorial * (n + 2 * i + 3).factorial := by rw [hch]
    rw [hL, hR]
    exact haux
  exact (mul_dvd_mul_iff_left (by positivity : (n - i).factorial * i.factorial ≠ 0)).mp hmul_dvd

end OMA.P_oeis_a087659

theorem OMA.solution : type_of% @OMA.S_oeis_a087659.main :=
  OMA.P_oeis_a087659.prove_main

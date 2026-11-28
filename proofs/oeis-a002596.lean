import OMAStatements.S_oeis_a002596
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto

-- Problem: A002596: Numerators in expansion of sqrt(1+x). Absolute values give numerators in expansion of sqrt(1-x).
-- Upstream: formal-conjectures statements/oeis-a002596.lean:0 (declaration OMA.S_oeis_a002596.main)
-- Credit: @eoin-or (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.Proof_oeis_a002596

open OMA.S_oeis_a002596

private lemma catalan_mul_succ (m : ℕ) : (m + 1) * catalan m = (2 * m).choose m := by
  rw [catalan_eq_centralBinom_div, ← Nat.centralBinom_eq_two_mul_choose]
  exact Nat.mul_div_cancel' (Nat.succ_dvd_centralBinom m)

private lemma catalan_pos (m : ℕ) : 0 < catalan m := by
  have h1 : 0 < (2 * m).choose m := Nat.choose_pos (by omega)
  rw [← catalan_mul_succ m] at h1
  exact Nat.pos_of_mul_pos_left h1

private lemma catalan_succ_eq (m : ℕ) :
    (m + 2) * catalan (m + 1) = 2 * (2 * m + 1) * catalan m := by
  have hpos : 0 < (m + 1).factorial * (m + 1).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_right hpos
  have hc1 : (m + 2) * catalan (m + 1) = (2 * m + 2).choose (m + 1) := by
    simpa [Nat.mul_add] using catalan_mul_succ (m + 1)
  have hc0 : (m + 1) * catalan m = (2 * m).choose m := catalan_mul_succ m
  have hf1 : (2 * m + 2).choose (m + 1) * (m + 1).factorial * (m + 1).factorial =
      (2 * m + 2).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show m + 1 ≤ 2 * m + 2 by omega)
    simpa [show 2 * m + 2 - (m + 1) = m + 1 by omega] using h
  have hf0 : (2 * m).choose m * m.factorial * m.factorial = (2 * m).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    simpa [show 2 * m - m = m by omega] using h
  calc
    (m + 2) * catalan (m + 1) * ((m + 1).factorial * (m + 1).factorial)
      = (2 * m + 2).choose (m + 1) * (m + 1).factorial * (m + 1).factorial := by
          rw [hc1]; ring
    _ = (2 * m + 2).factorial := hf1
    _ = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
          rw [Nat.factorial_succ, Nat.factorial_succ]; ring
    _ = (2 * m + 2) * (2 * m + 1) * ((2 * m).choose m * m.factorial * m.factorial) := by
          rw [hf0]
    _ = 2 * (2 * m + 1) * ((m + 1) * catalan m) * (m + 1) * m.factorial * m.factorial := by
          rw [hc0]; ring
    _ = 2 * (2 * m + 1) * catalan m * ((m + 1).factorial * (m + 1).factorial) := by
          rw [Nat.factorial_succ]; ring

private lemma coeff_eq_catalan (m : ℕ) :
    coeff (m + 1) = (-1 : ℚ) ^ m * (catalan m : ℚ) / (2 : ℚ) ^ (2 * m + 1) := by
  induction m with
  | zero =>
      simp [coeff, catalan_zero]
  | succ m ih =>
      have hcast : ((m + 2 : ℚ)) * (catalan (m + 1) : ℚ) =
          2 * (2 * (m : ℚ) + 1) * (catalan m : ℚ) := by
        exact_mod_cast catalan_succ_eq m
      have hm2 : (m : ℚ) + 2 ≠ 0 := by positivity
      have hpow : (2 : ℚ) ^ (2 * m + 1) ≠ 0 := by positivity
      have hpow2 : (2 : ℚ) ^ (2 * (m + 1) + 1) ≠ 0 := by positivity
      rw [show m + 1 + 1 = (m + 1) + 1 from rfl, coeff, ih]
      have hrew : (2 : ℚ) ^ (2 * (m + 1) + 1) = 4 * (2 : ℚ) ^ (2 * m + 1) := by
        rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, pow_add]
        ring
      rw [hrew]
      have hgoal :
          (-1 : ℚ) ^ m * (catalan m : ℚ) / (2 : ℚ) ^ (2 * m + 1) * (1 / 2 - ((m + 1 : ℕ) : ℚ)) /
              (((m + 1 : ℕ) : ℚ) + 1) =
            (-1 : ℚ) ^ (m + 1) * (catalan (m + 1) : ℚ) / (4 * (2 : ℚ) ^ (2 * m + 1)) := by
        push_cast
        have hstep : ((m : ℚ) + 2) * (catalan (m + 1) : ℚ) =
            2 * (2 * (m : ℚ) + 1) * (catalan m : ℚ) := by
          simpa [add_assoc] using hcast
        have hden1 : (2 : ℚ) ^ (2 * m + 1) * ((m : ℚ) + 1 + 1) ≠ 0 := by positivity
        have hden2 : 4 * (2 : ℚ) ^ (2 * m + 1) ≠ 0 := by positivity
        rw [div_mul_eq_mul_div, div_div, div_eq_div_iff hden1 hden2]
        calc
          (-1 : ℚ) ^ m * (catalan m : ℚ) * (1 / 2 - ((m : ℚ) + 1)) * (4 * (2 : ℚ) ^ (2 * m + 1))
            = -((-1 : ℚ) ^ m) * (2 * (2 * (m : ℚ) + 1) * (catalan m : ℚ)) *
                (2 : ℚ) ^ (2 * m + 1) := by ring
          _ = -((-1 : ℚ) ^ m) * (((m : ℚ) + 2) * (catalan (m + 1) : ℚ)) *
                (2 : ℚ) ^ (2 * m + 1) := by rw [← hstep]
          _ = (-1 : ℚ) ^ (m + 1) * (catalan (m + 1) : ℚ) *
                ((2 : ℚ) ^ (2 * m + 1) * ((m : ℚ) + 1 + 1)) := by rw [pow_succ]; ring
      exact hgoal

private lemma coeff_num_mul_pow (m : ℕ) :
    (coeff (m + 1)).num * (2 : ℤ) ^ (2 * m + 1) =
      (-1 : ℤ) ^ m * (catalan m : ℤ) * ((coeff (m + 1)).den : ℤ) := by
  have hq := coeff_eq_catalan m
  rw [← Rat.num_div_den (coeff (m + 1))] at hq
  have hden : ((coeff (m + 1)).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (coeff (m + 1)).den_nz
  have hpow : (2 : ℚ) ^ (2 * m + 1) ≠ 0 := by positivity
  have hmul : ((coeff (m + 1)).num : ℚ) * (2 : ℚ) ^ (2 * m + 1) =
      (-1 : ℚ) ^ m * (catalan m : ℚ) * ((coeff (m + 1)).den : ℚ) := by
    have := (div_eq_div_iff hden hpow).mp hq
    exact this
  exact_mod_cast hmul

private lemma coeff_natAbs_mul_pow (m : ℕ) :
    (coeff (m + 1)).num.natAbs * 2 ^ (2 * m + 1) = catalan m * (coeff (m + 1)).den := by
  have h := congrArg Int.natAbs (coeff_num_mul_pow m)
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul,
    Int.natAbs_natCast] at h
  simpa using h

private lemma not_two_dvd_coeff_num (n : ℕ) : ¬ (2 : ℤ) ∣ (coeff n).num := by
  cases n with
  | zero =>
      simp [coeff]
  | succ m =>
      have heq := coeff_natAbs_mul_pow m
      have hred : Nat.Coprime (coeff (m + 1)).num.natAbs (coeff (m + 1)).den :=
        (coeff (m + 1)).reduced
      have hden_dvd : (coeff (m + 1)).den ∣ 2 ^ (2 * m + 1) := by
        have h1 : (coeff (m + 1)).den ∣ (coeff (m + 1)).num.natAbs * 2 ^ (2 * m + 1) :=
          ⟨catalan m, by rw [heq, mul_comm]⟩
        exact hred.symm.dvd_of_dvd_mul_left h1
      have hcat_lt : catalan m < 2 ^ (2 * m + 1) := by
        have h1 : catalan m ≤ (2 * m).choose m := by
          calc
            catalan m = 1 * catalan m := (one_mul _).symm
            _ ≤ (m + 1) * catalan m := Nat.mul_le_mul_right _ (by omega)
            _ = (2 * m).choose m := catalan_mul_succ m
        have h2 : (2 * m).choose m ≤ 2 ^ (2 * m) := Nat.choose_le_two_pow (2 * m) m
        have h3 : 2 ^ (2 * m) < 2 ^ (2 * m + 1) := by
          rw [pow_succ]
          have : 0 < 2 ^ (2 * m) := by positivity
          omega
        omega
      have hden_ne_one : (coeff (m + 1)).den ≠ 1 := by
        intro h1
        rw [h1, mul_one] at heq
        have hpos : 0 < catalan m := catalan_pos m
        have hnum_pos : 1 ≤ (coeff (m + 1)).num.natAbs := by
          by_contra h0
          have : (coeff (m + 1)).num.natAbs = 0 := by omega
          rw [this, zero_mul] at heq
          omega
        have : 2 ^ (2 * m + 1) ≤ (coeff (m + 1)).num.natAbs * 2 ^ (2 * m + 1) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      have htwo_dvd_den : 2 ∣ (coeff (m + 1)).den := by
        obtain ⟨q, hqp, hqd⟩ := Nat.exists_prime_and_dvd hden_ne_one
        have hq2 : q ∣ 2 := hqp.dvd_of_dvd_pow (dvd_trans hqd hden_dvd)
        have hq_eq : q = 2 := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp hq2
        exact hq_eq ▸ hqd
      intro h2
      have h2nat : 2 ∣ (coeff (m + 1)).num.natAbs := by
        exact_mod_cast Int.natCast_dvd.mp h2
      have h2_dvd_one : 2 ∣ 1 := hred.gcd_eq_one ▸ Nat.dvd_gcd h2nat htwo_dvd_den
      omega

private lemma odd_prime_dvd_coeff_num_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ) :
    (p : ℤ) ∣ (coeff (m + 1)).num ↔ p ∣ catalan m := by
  have heq := coeff_natAbs_mul_pow m
  have hred : Nat.Coprime (coeff (m + 1)).num.natAbs (coeff (m + 1)).den :=
    (coeff (m + 1)).reduced
  have hden_dvd : (coeff (m + 1)).den ∣ 2 ^ (2 * m + 1) := by
    have h1 : (coeff (m + 1)).den ∣ (coeff (m + 1)).num.natAbs * 2 ^ (2 * m + 1) :=
      ⟨catalan m, by rw [heq, mul_comm]⟩
    exact hred.symm.dvd_of_dvd_mul_left h1
  have hp_not_dvd_two : ¬ p ∣ 2 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hcop_pow : Nat.Coprime p (2 ^ (2 * m + 1)) :=
    (hp.coprime_iff_not_dvd.mpr hp_not_dvd_two).pow_right _
  have hcop_den : Nat.Coprime p (coeff (m + 1)).den :=
    Nat.Coprime.coprime_dvd_right hden_dvd hcop_pow
  rw [Int.natCast_dvd]
  constructor
  · intro h
    have h1 : p ∣ catalan m * (coeff (m + 1)).den := by
      rw [← heq]
      exact dvd_mul_of_dvd_left h _
    exact hcop_den.dvd_of_dvd_mul_right h1
  · intro h
    have h1 : p ∣ (coeff (m + 1)).num.natAbs * 2 ^ (2 * m + 1) := by
      rw [heq]
      exact dvd_mul_of_dvd_left h _
    exact hcop_pow.dvd_of_dvd_mul_right h1

private lemma nat_log_lt_succ {p : ℕ} (hp : 1 < p) (n : ℕ) : Nat.log p n < n + 1 := by
  cases n with
  | zero => simp
  | succ n =>
      apply Nat.log_lt_of_lt_pow (Nat.succ_ne_zero n)
      calc
        n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
        _ ≤ p ^ (n + 1) := Nat.pow_le_pow_left (by omega) _
        _ ≤ p ^ (n + 2) := Nat.pow_le_pow_right (by omega) (by omega)

private lemma padicValNat_factorial_eq_div_add {p : ℕ} [hp : Fact p.Prime] (n : ℕ) :
    padicValNat p n.factorial = n / p + padicValNat p (n / p).factorial := by
  have hp1 : 1 < p := hp.out.one_lt
  have h1 : Nat.log p n < n + 2 := by
    have := nat_log_lt_succ hp1 n
    omega
  have h2 : Nat.log p (n / p) < n + 1 := by
    have := nat_log_lt_succ hp1 (n / p)
    have hdiv : n / p ≤ n := Nat.div_le_self n p
    omega
  rw [padicValNat_factorial h1, padicValNat_factorial h2]
  have hsplit : Finset.Ico 1 (n + 2) = insert 1 (Finset.Ico 2 (n + 2)) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp), pow_one]
  congr 1
  have hbij : ∑ i ∈ Finset.Ico 2 (n + 2), n / p ^ i =
      ∑ i ∈ Finset.Ico 1 (n + 1), (n / p) / p ^ i := by
    refine Finset.sum_bij (fun i _ => i - 1) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_Ico] at hi ⊢
      omega
    · intro i1 hi1 i2 hi2 h
      simp only [Finset.mem_Ico] at hi1 hi2
      omega
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      exact ⟨j + 1, by simp only [Finset.mem_Ico]; omega, by omega⟩
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      have hi1 : i = (i - 1) + 1 := by omega
      conv_lhs => rw [hi1, pow_succ', ← Nat.div_div_eq_div_mul]
  exact hbij

private lemma padicValNat_centralBinom_eq {p : ℕ} [Fact p.Prime] (q : ℕ) :
    2 * padicValNat p q.factorial + padicValNat p ((2 * q).choose q) =
      padicValNat p (2 * q).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (show q ≤ 2 * q by omega)
  rw [show 2 * q - q = q by omega] at h
  have hch : (2 * q).choose q ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hf : q.factorial ≠ 0 := Nat.factorial_ne_zero q
  have hv := congrArg (padicValNat p) h
  rw [padicValNat.mul (mul_ne_zero hch hf) hf, padicValNat.mul hch hf] at hv
  omega

private lemma padicValNat_catalan_eq {p : ℕ} [Fact p.Prime] (m : ℕ) :
    padicValNat p m.factorial + padicValNat p (m + 1).factorial + padicValNat p (catalan m) =
      padicValNat p (2 * m).factorial := by
  have h0 : catalan m * m.factorial * (m + 1).factorial = (2 * m).factorial := by
    have h1 := catalan_mul_succ m
    have h2 := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    rw [show 2 * m - m = m by omega] at h2
    calc
      catalan m * m.factorial * (m + 1).factorial
        = ((m + 1) * catalan m) * m.factorial * m.factorial := by
            rw [Nat.factorial_succ]; ring
      _ = (2 * m).choose m * m.factorial * m.factorial := by rw [h1]
      _ = (2 * m).factorial := h2
  have hc : catalan m ≠ 0 := (catalan_pos m).ne'
  have hf1 : m.factorial ≠ 0 := Nat.factorial_ne_zero m
  have hf2 : (m + 1).factorial ≠ 0 := Nat.factorial_ne_zero (m + 1)
  have hv := congrArg (padicValNat p) h0
  rw [padicValNat.mul (mul_ne_zero hc hf1) hf2, padicValNat.mul hc hf1] at hv
  omega

private lemma padicValNat_factorial_mono {p : ℕ} [Fact p.Prime] (n : ℕ) :
    padicValNat p n.factorial ≤ padicValNat p (n + 1).factorial := by
  rw [Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)]
  omega

private def AllDigitsLe (p h n : ℕ) : Prop :=
  ∀ k : ℕ, (n / p ^ k) % p ≤ h

private lemma allDigitsLe_zero (p h : ℕ) : AllDigitsLe p h 0 := by
  intro k
  simp

private lemma allDigitsLe_iff_div {p h : ℕ} (_hp : 0 < p) (n : ℕ) :
    AllDigitsLe p h n ↔ n % p ≤ h ∧ AllDigitsLe p h (n / p) := by
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    · simpa using H 0
    · intro k
      have hk := H (k + 1)
      rwa [pow_succ', ← Nat.div_div_eq_div_mul] at hk
  · rintro ⟨h0, hdiv⟩ k
    cases k with
    | zero => simpa using h0
    | succ k =>
        rw [pow_succ', ← Nat.div_div_eq_div_mul]
        exact hdiv k

private lemma allDigitsLe_mul_add {p h r : ℕ} (hr : r < p) (q : ℕ) :
    AllDigitsLe p h (p * q + r) ↔ r ≤ h ∧ AllDigitsLe p h q := by
  have hp : 0 < p := by omega
  rw [allDigitsLe_iff_div hp]
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr, Nat.mul_add_div hp, Nat.div_eq_of_lt hr, add_zero]

private lemma odd_prime_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p = 2 * ((p - 1) / 2) + 1 ∧ 1 ≤ (p - 1) / 2 := by
  have hodd : p % 2 = 1 := by
    have := hp.eq_two_or_odd
    omega
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  omega

private lemma padicValNat_choose_eq_zero_iff {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ q : ℕ, padicValNat p ((2 * q).choose q) = 0 ↔ AllDigitsLe p ((p - 1) / 2) q := by
  obtain ⟨hp_eq, hh_pos⟩ := odd_prime_eq hp.out hp2
  set h := (p - 1) / 2
  have hp_pos : 0 < p := hp.out.pos
  have hp2lt : 1 < p := hp.out.one_lt
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      cases q with
      | zero =>
          simp [allDigitsLe_zero]
      | succ q0 =>
          set n := q0 + 1
          set q' := n / p
          set r := n % p
          have hnr : n = p * q' + r := (Nat.div_add_mod n p).symm
          have hr_lt : r < p := Nat.mod_lt n hp_pos
          have hq'_lt : q' < n := Nat.div_lt_self (Nat.succ_pos q0) hp2lt
          have hcb := padicValNat_centralBinom_eq (p := p) n
          have hcb' := padicValNat_centralBinom_eq (p := p) q'
          have hfn : padicValNat p n.factorial = q' + padicValNat p q'.factorial :=
            padicValNat_factorial_eq_div_add (p := p) n
          have hf2n := padicValNat_factorial_eq_div_add (p := p) (2 * n)
          have h2n_base : 2 * n = p * (2 * q') + 2 * r := by
            rw [hnr]; ring
          by_cases hrh : r ≤ h
          · have hdiv2 : (2 * n) / p = 2 * q' := by
              rw [h2n_base, Nat.mul_add_div hp_pos, Nat.div_eq_of_lt (by omega : 2 * r < p),
                add_zero]
            rw [hdiv2] at hf2n
            have hveq : padicValNat p ((2 * n).choose n) = padicValNat p ((2 * q').choose q') := by
              omega
            rw [hveq, ih q' hq'_lt, allDigitsLe_iff_div hp_pos n]
            exact ⟨fun H => ⟨hrh, H⟩, fun H => H.2⟩
          · have hdiv2 : (2 * n) / p = 2 * q' + 1 := by
              have h2n : 2 * n = p * (2 * q' + 1) + (2 * r - p) := by
                have hmul : p * (2 * q' + 1) = p * (2 * q') + p := by ring
                omega
              rw [h2n, Nat.mul_add_div hp_pos, Nat.div_eq_of_lt (by omega : 2 * r - p < p),
                add_zero]
            rw [hdiv2] at hf2n
            have hmono := padicValNat_factorial_mono (p := p) (2 * q')
            have hvpos : 1 ≤ padicValNat p ((2 * n).choose n) := by omega
            constructor
            · intro h0; omega
            · intro H
              have := (allDigitsLe_iff_div hp_pos n).mp H
              exact absurd this.1 hrh

private lemma padicValNat_catalan_eq_zero_iff {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (m : ℕ) :
    padicValNat p (catalan m) = 0 ↔
      AllDigitsLe p ((p - 1) / 2) (m + 1) ∨ AllDigitsLe p ((p - 1) / 2) m := by
  obtain ⟨hp_eq, hh_pos⟩ := odd_prime_eq hp.out hp2
  set h := (p - 1) / 2
  have hp_pos : 0 < p := hp.out.pos
  set q := m / p
  set r := m % p
  have hmr : m = p * q + r := (Nat.div_add_mod m p).symm
  have hr_lt : r < p := Nat.mod_lt m hp_pos
  have hcat := padicValNat_catalan_eq (p := p) m
  have hfm : padicValNat p m.factorial = q + padicValNat p q.factorial :=
    padicValNat_factorial_eq_div_add (p := p) m
  have hfm1 := padicValNat_factorial_eq_div_add (p := p) (m + 1)
  have hf2m := padicValNat_factorial_eq_div_add (p := p) (2 * m)
  have h2m_base : 2 * m = p * (2 * q) + 2 * r := by
    rw [hmr]; ring
  by_cases hrh : r ≤ h
  · have hdiv1 : (m + 1) / p = q := by
      have hm1 : m + 1 = p * q + (r + 1) := by omega
      rw [hm1, Nat.mul_add_div hp_pos, Nat.div_eq_of_lt (by omega : r + 1 < p), add_zero]
    have hdiv2 : (2 * m) / p = 2 * q := by
      rw [h2m_base, Nat.mul_add_div hp_pos, Nat.div_eq_of_lt (by omega : 2 * r < p), add_zero]
    rw [hdiv1] at hfm1
    rw [hdiv2] at hf2m
    have hcb := padicValNat_centralBinom_eq (p := p) q
    have hveq : padicValNat p (catalan m) = padicValNat p ((2 * q).choose q) := by omega
    rw [hveq, padicValNat_choose_eq_zero_iff hp2 q]
    constructor
    · intro Hq
      right
      rw [allDigitsLe_iff_div hp_pos m]
      exact ⟨hrh, Hq⟩
    · rintro (Hm1 | Hm)
      · have := (allDigitsLe_iff_div hp_pos (m + 1)).mp Hm1
        rw [hdiv1] at this
        exact this.2
      · exact ((allDigitsLe_iff_div hp_pos m).mp Hm).2
  · by_cases hrp : r < p - 1
    · have hdiv1 : (m + 1) / p = q := by
        have hm1 : m + 1 = p * q + (r + 1) := by omega
        rw [hm1, Nat.mul_add_div hp_pos, Nat.div_eq_of_lt (by omega : r + 1 < p), add_zero]
      have hdiv2 : (2 * m) / p = 2 * q + 1 := by
        have h2m : 2 * m = p * (2 * q + 1) + (2 * r - p) := by
          have hmul : p * (2 * q + 1) = p * (2 * q) + p := by ring
          omega
        rw [h2m, Nat.mul_add_div hp_pos, Nat.div_eq_of_lt (by omega : 2 * r - p < p), add_zero]
      rw [hdiv1] at hfm1
      rw [hdiv2] at hf2m
      have hcb := padicValNat_centralBinom_eq (p := p) q
      have hmono := padicValNat_factorial_mono (p := p) (2 * q)
      have hvpos : 1 ≤ padicValNat p (catalan m) := by omega
      constructor
      · intro h0; omega
      · rintro (Hm1 | Hm)
        · have hmod1 : (m + 1) % p = r + 1 := by
            have hm1 : m + 1 = p * q + (r + 1) := by omega
            rw [hm1, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : r + 1 < p)]
          have := ((allDigitsLe_iff_div hp_pos (m + 1)).mp Hm1).1
          omega
        · have := ((allDigitsLe_iff_div hp_pos m).mp Hm).1
          omega
    · have hr_eq : r = p - 1 := by omega
      have hm1_eq : m + 1 = p * (q + 1) := by
        have hmul : p * (q + 1) = p * q + p := by ring
        omega
      have hdiv1 : (m + 1) / p = q + 1 := by
        rw [hm1_eq, Nat.mul_div_cancel_left _ hp_pos]
      have hdiv2 : (2 * m) / p = 2 * q + 1 := by
        have h2m : 2 * m = p * (2 * q + 1) + (p - 2) := by
          have hmul : p * (2 * q + 1) = p * (2 * q) + p := by ring
          omega
        rw [h2m, Nat.mul_add_div hp_pos, Nat.div_eq_of_lt (by omega : p - 2 < p), add_zero]
      rw [hdiv1] at hfm1
      rw [hdiv2] at hf2m
      have hfq1 : padicValNat p (q + 1).factorial =
          padicValNat p (q + 1) + padicValNat p q.factorial := by
        rw [Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero q) (Nat.factorial_ne_zero q)]
      have h2_val : padicValNat p 2 = 0 := by
        rw [padicValNat.eq_zero_iff]
        right; right
        intro h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2)
      have hf2q2 : padicValNat p (2 * (q + 1)).factorial =
          padicValNat p (q + 1) + padicValNat p (2 * q + 1).factorial := by
        rw [show 2 * (q + 1) = (2 * q + 1) + 1 by omega, Nat.factorial_succ,
          padicValNat.mul (by omega) (Nat.factorial_ne_zero _),
          show (2 * q + 1) + 1 = 2 * (q + 1) by omega,
          padicValNat.mul (by omega) (Nat.succ_ne_zero q), h2_val, zero_add]
      have hcb := padicValNat_centralBinom_eq (p := p) (q + 1)
      have hveq : padicValNat p (catalan m) = padicValNat p ((2 * (q + 1)).choose (q + 1)) := by
        omega
      rw [hveq, padicValNat_choose_eq_zero_iff hp2 (q + 1)]
      constructor
      · intro Hq1
        left
        rw [hm1_eq, ← add_zero (p * (q + 1)), allDigitsLe_mul_add hp_pos]
        exact ⟨Nat.zero_le _, Hq1⟩
      · rintro (Hm1 | Hm)
        · rw [hm1_eq, ← add_zero (p * (q + 1)), allDigitsLe_mul_add hp_pos] at Hm1
          exact Hm1.2
        · have := ((allDigitsLe_iff_div hp_pos m).mp Hm).1
          omega

private lemma odd_prime_dvd_coeff_num_iff_digits {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    (p : ℤ) ∣ (coeff n).num ↔
      ¬ AllDigitsLe p ((p - 1) / 2) n ∧ ¬ AllDigitsLe p ((p - 1) / 2) (n - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  cases n with
  | zero =>
      simp only [coeff, Rat.num_one, Nat.zero_sub, allDigitsLe_zero, not_true_eq_false, and_self,
        iff_false]
      intro h
      have h1 : p ∣ 1 := by exact_mod_cast Int.natCast_dvd.mp h
      exact hp.ne_one (Nat.dvd_one.mp h1)
  | succ m =>
      rw [odd_prime_dvd_coeff_num_iff hp hp2 m, Nat.add_sub_cancel]
      have hne : padicValNat p (catalan m) = 0 ↔ ¬ p ∣ catalan m := by
        rw [padicValNat.eq_zero_iff]
        simp [hp.ne_one, (catalan_pos m).ne']
      rw [← not_iff_not]
      push Not
      rw [← hne, padicValNat_catalan_eq_zero_iff hp2 m]
      tauto

private def halfPow (p k : ℕ) : ℕ := (p ^ k - 1) / 2

private lemma pow_odd_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    p ^ k % 2 = 1 ∧ 1 ≤ p ^ k := by
  have hp1 : p % 2 = 1 := by
    have := hp.eq_two_or_odd
    omega
  refine ⟨?_, Nat.one_le_pow k p hp.pos⟩
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Nat.mul_mod, ih, hp1]

private lemma halfPow_succ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    halfPow p (k + 1) = p * halfPow p k + (p - 1) / 2 := by
  obtain ⟨hp_eq, _⟩ := odd_prime_eq hp hp2
  obtain ⟨hodd, hpos⟩ := pow_odd_of_odd_prime hp hp2 k
  obtain ⟨hodd1, hpos1⟩ := pow_odd_of_odd_prime hp hp2 (k + 1)
  unfold halfPow
  have h1 : 2 * ((p ^ k - 1) / 2) = p ^ k - 1 := by omega
  have h2 : 2 * ((p ^ (k + 1) - 1) / 2) = p ^ (k + 1) - 1 := by omega
  have h3 : 2 * (p * ((p ^ k - 1) / 2) + (p - 1) / 2) = p ^ (k + 1) - 1 := by
    have h4 : 2 * (p * ((p ^ k - 1) / 2)) = p * (2 * ((p ^ k - 1) / 2)) := by ring
    rw [mul_add, h4, h1, Nat.mul_sub_left_distrib, mul_one, ← pow_succ']
    have hle : p ≤ p ^ (k + 1) := by
      calc p = p * 1 := (mul_one p).symm
        _ ≤ p * p ^ k := Nat.mul_le_mul_left p hpos
        _ = p ^ (k + 1) := (pow_succ' p k).symm
    omega
  omega

private lemma halfPow_lt_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    halfPow p k < p ^ k := by
  obtain ⟨_, hpos⟩ := pow_odd_of_odd_prime hp hp2 k
  unfold halfPow
  omega

private lemma allDigitsLe_mul_pow_add {p h : ℕ} (hp : 0 < p) :
    ∀ k q u : ℕ, u < p ^ k →
      (AllDigitsLe p h (p ^ k * q + u) ↔ AllDigitsLe p h u ∧ AllDigitsLe p h q) := by
  intro k
  induction k with
  | zero =>
      intro q u hu
      have hu0 : u = 0 := by simpa using hu
      subst hu0
      simp [allDigitsLe_zero]
  | succ k ih =>
      intro q u hu
      have hu_div_lt : u / p < p ^ k := by
        rw [Nat.div_lt_iff_lt_mul hp]
        simpa [pow_succ] using hu
      have hu_mod_lt : u % p < p := Nat.mod_lt u hp
      have hrew : p ^ (k + 1) * q + u = p * (p ^ k * q + u / p) + u % p := by
        have h1 : u = p * (u / p) + u % p := (Nat.div_add_mod u p).symm
        conv_lhs => rw [h1, pow_succ']
        ring
      rw [hrew, allDigitsLe_mul_add hu_mod_lt, ih q (u / p) hu_div_lt, allDigitsLe_iff_div hp u]
      tauto

private lemma allDigitsLe_halfPow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    AllDigitsLe p ((p - 1) / 2) (halfPow p k) := by
  obtain ⟨hp_eq, _⟩ := odd_prime_eq hp hp2
  induction k with
  | zero =>
      simp [halfPow, allDigitsLe_zero]
  | succ k ih =>
      rw [halfPow_succ hp hp2 k, allDigitsLe_mul_add (by omega : (p - 1) / 2 < p)]
      exact ⟨le_rfl, ih⟩

private lemma le_halfPow_of_allDigitsLe {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ k u : ℕ, u < p ^ k → AllDigitsLe p ((p - 1) / 2) u → u ≤ halfPow p k := by
  intro k
  induction k with
  | zero =>
      intro u hu _
      have : u = 0 := by simpa using hu
      simp [this, halfPow]
  | succ k ih =>
      intro u hu hd
      have hu_div_lt : u / p < p ^ k := by
        rw [Nat.div_lt_iff_lt_mul hp.pos]
        simpa [pow_succ] using hu
      have ⟨hmod, hdiv⟩ := (allDigitsLe_iff_div hp.pos u).mp hd
      have hle := ih (u / p) hu_div_lt hdiv
      rw [halfPow_succ hp hp2 k]
      have h1 : u = p * (u / p) + u % p := (Nat.div_add_mod u p).symm
      have h2 : p * (u / p) ≤ p * halfPow p k := Nat.mul_le_mul_left p hle
      omega

private lemma allDigitsLe_succ_of_mod_lt {p h q : ℕ} (hp : 0 < p) (hh : h < p)
    (hq : AllDigitsLe p h q) (hmod : q % p < h) : AllDigitsLe p h (q + 1) := by
  have h1 : q + 1 = p * (q / p) + (q % p + 1) := by
    have := Nat.div_add_mod q p
    omega
  rw [h1, allDigitsLe_mul_add (by omega : q % p + 1 < p)]
  exact ⟨by omega, ((allDigitsLe_iff_div hp q).mp hq).2⟩

private lemma not_allDigitsLe_in_gap {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k q x : ℕ}
    (hx1 : p ^ k * q + halfPow p k < x) (hx2 : x < p ^ k * (q + 1)) :
    ¬ AllDigitsLe p ((p - 1) / 2) x := by
  intro H
  set u := x - p ^ k * q
  have hx_eq : x = p ^ k * q + u := by omega
  have hu_lt : u < p ^ k := by
    have : p ^ k * (q + 1) = p ^ k * q + p ^ k := by ring
    omega
  rw [hx_eq, allDigitsLe_mul_pow_add hp.pos k q u hu_lt] at H
  have hle := le_halfPow_of_allDigitsLe hp hp2 k u hu_lt H.1
  omega

private lemma blockAfter_of_decomp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {q k : ℕ}
    (hlen : 0 < (p ^ k - 3) / 2) (hq : AllDigitsLe p ((p - 1) / 2) q)
    (hmod : q % p < (p - 1) / 2) :
    blockAfter p (p ^ k * q + halfPow p k + 1) ((p ^ k - 3) / 2) := by
  obtain ⟨hp_eq, _⟩ := odd_prime_eq hp hp2
  obtain ⟨hodd, hpos⟩ := pow_odd_of_odd_prime hp hp2 k
  set h := (p - 1) / 2
  set m := p ^ k * q + halfPow p k
  set j := m + 1
  set len := (p ^ k - 3) / 2
  have hend_eq : j + len + 1 = p ^ k * (q + 1) := by
    have hmul : p ^ k * (q + 1) = p ^ k * q + p ^ k := by ring
    have hsum : halfPow p k + 1 + len + 1 = p ^ k := by
      unfold halfPow at *
      omega
    omega
  refine ⟨hlen, ?_, ?_, ?_⟩
  · rw [odd_prime_dvd_coeff_num_iff_digits hp hp2 j]
    intro H
    apply H.2
    rw [Nat.add_sub_cancel]
    exact (allDigitsLe_mul_pow_add hp.pos k q (halfPow p k) (halfPow_lt_pow hp hp2 k)).mpr
      ⟨allDigitsLe_halfPow hp hp2 k, hq⟩
  · intro i hi1 hi2
    rw [odd_prime_dvd_coeff_num_iff_digits hp hp2 i]
    refine ⟨not_allDigitsLe_in_gap hp hp2 (k := k) (q := q) (by omega) (by omega),
      not_allDigitsLe_in_gap hp hp2 (k := k) (q := q) (by omega) (by omega)⟩
  · rw [hend_eq, odd_prime_dvd_coeff_num_iff_digits hp hp2 (p ^ k * (q + 1))]
    intro H
    apply H.1
    have hq1 : AllDigitsLe p h (q + 1) :=
      allDigitsLe_succ_of_mod_lt hp.pos (by omega) hq hmod
    have h0 : p ^ k * (q + 1) = p ^ k * (q + 1) + 0 := by omega
    rw [h0, allDigitsLe_mul_pow_add hp.pos k (q + 1) 0 (by omega)]
    exact ⟨allDigitsLe_zero p h, hq1⟩

private lemma exists_trailingH_decomp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ m : ℕ, AllDigitsLe p ((p - 1) / 2) m →
      ∃ k q : ℕ, m = p ^ k * q + halfPow p k ∧
        AllDigitsLe p ((p - 1) / 2) q ∧ q % p < (p - 1) / 2 := by
  obtain ⟨hp_eq, hh_pos⟩ := odd_prime_eq hp hp2
  set h := (p - 1) / 2
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro hm
      by_cases hmod : m % p < h
      · exact ⟨0, m, by simp [halfPow], hm, hmod⟩
      · have ⟨hm_le, hm_div⟩ := (allDigitsLe_iff_div hp.pos m).mp hm
        have hm_eq : m % p = h := by omega
        have hm_pos : 0 < m := by
          by_contra h0
          have : m = 0 := by omega
          subst this
          simp at hm_eq
          omega
        have hlt : m / p < m := Nat.div_lt_self hm_pos hp.one_lt
        obtain ⟨k, q, hq_eq, hq_d, hq_mod⟩ := ih (m / p) hlt hm_div
        refine ⟨k + 1, q, ?_, hq_d, hq_mod⟩
        rw [halfPow_succ hp hp2 k]
        have h1 : m = p * (m / p) + m % p := (Nat.div_add_mod m p).symm
        rw [hq_eq, hm_eq] at h1
        rw [h1, pow_succ']
        ring

private lemma exists_max_allDigitsLe_lt {p h : ℕ} :
    ∀ n : ℕ, ¬ AllDigitsLe p h n →
      ∃ m < n, AllDigitsLe p h m ∧ ∀ x, m < x → x ≤ n → ¬ AllDigitsLe p h x := by
  intro n
  induction n with
  | zero =>
      intro H
      exact absurd (allDigitsLe_zero p h) H
  | succ n ih =>
      intro H
      by_cases hn : AllDigitsLe p h n
      · refine ⟨n, Nat.lt_succ_self n, hn, ?_⟩
        intro x hx1 hx2
        have : x = n + 1 := by omega
        subst this
        exact H
      · obtain ⟨m, hm_lt, hm_d, hm_max⟩ := ih hn
        refine ⟨m, Nat.lt_succ_of_lt hm_lt, hm_d, ?_⟩
        intro x hx1 hx2
        by_cases hxn : x ≤ n
        · exact hm_max x hx1 hxn
        · have : x = n + 1 := by omega
          subst this
          exact H

private lemma main_part1 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ)
    (hdvd : (p : ℤ) ∣ (coeff n).num) :
    ∃ j k : ℕ, 0 < k ∧ j < n ∧ n ≤ j + (p ^ k - 3) / 2 ∧
      blockAfter p j ((p ^ k - 3) / 2) := by
  obtain ⟨hp_eq, _⟩ := odd_prime_eq hp hp2
  set h := (p - 1) / 2
  have ⟨hn_bad, hn1_bad⟩ := (odd_prime_dvd_coeff_num_iff_digits hp hp2 n).mp hdvd
  obtain ⟨m, hm_lt, hm_d, hm_max⟩ := exists_max_allDigitsLe_lt (p := p) (h := h) n hn_bad
  have hn_pos : 0 < n := by omega
  have hm_lt1 : m + 1 < n := by
    by_contra hge
    have hm_eq : m = n - 1 := by omega
    exact hn1_bad (hm_eq ▸ hm_d)
  obtain ⟨k, q, hm_eq, hq_d, hq_mod⟩ := exists_trailingH_decomp hp hp2 m hm_d
  have hk_pos : 0 < k := by
    by_contra hk0
    have hk_eq : k = 0 := by omega
    subst hk_eq
    have hmq : m = q := by simpa [halfPow] using hm_eq
    subst hmq
    have hm1_d : AllDigitsLe p h (m + 1) :=
      allDigitsLe_succ_of_mod_lt hp.pos (by omega) hq_d hq_mod
    exact hm_max (m + 1) (by omega) (by omega) hm1_d
  set m' := p ^ k * (q + 1)
  have hm'_d : AllDigitsLe p h m' := by
    have hq1 : AllDigitsLe p h (q + 1) :=
      allDigitsLe_succ_of_mod_lt hp.pos (by omega) hq_d hq_mod
    have h0 : m' = p ^ k * (q + 1) + 0 := by omega
    rw [h0, allDigitsLe_mul_pow_add hp.pos k (q + 1) 0 (Nat.pow_pos hp.pos)]
    exact ⟨allDigitsLe_zero p h, hq1⟩
  have hm_lt_m' : m < m' := by
    have hlt := halfPow_lt_pow hp hp2 k
    have hmul : m' = p ^ k * q + p ^ k := by ring
    omega
  have hn_lt_m' : n < m' := by
    by_contra hge
    exact hm_max m' hm_lt_m' (by omega) hm'_d
  obtain ⟨hodd, hpow_pos⟩ := pow_odd_of_odd_prime hp hp2 k
  have hdiff : m' - m = (p ^ k + 1) / 2 := by
    have hmul : m' = p ^ k * q + p ^ k := by ring
    unfold halfPow at hm_eq
    omega
  have hlen_pos : 0 < (p ^ k - 3) / 2 := by omega
  refine ⟨m + 1, k, hk_pos, hm_lt1, ?_, ?_⟩
  · omega
  · rw [hm_eq]
    exact blockAfter_of_decomp hp hp2 hlen_pos hq_d hq_mod

private lemma main_part2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (j k : ℕ) (_hk : 0 < k)
    (hb : blockAfter p j ((p ^ k - 3) / 2)) :
    blockAfter p (p * j - (p - 1) / 2) ((p ^ (k + 1) - 3) / 2) := by
  obtain ⟨hp_eq, hh_pos⟩ := odd_prime_eq hp hp2
  set h := (p - 1) / 2
  obtain ⟨hlen, hj_ndvd, hmid, hend_ndvd⟩ := hb
  have hj1_dvd : (p : ℤ) ∣ (coeff (j + 1)).num := hmid (j + 1) (by omega) (by omega)
  have ⟨_, hj_bad⟩ := (odd_prime_dvd_coeff_num_iff_digits hp hp2 (j + 1)).mp hj1_dvd
  rw [Nat.add_sub_cancel] at hj_bad
  have hj_good : AllDigitsLe p h j ∨ AllDigitsLe p h (j - 1) := by
    by_contra hnot
    push Not at hnot
    exact hj_ndvd ((odd_prime_dvd_coeff_num_iff_digits hp hp2 j).mpr hnot)
  have hm_d : AllDigitsLe p h (j - 1) := hj_good.resolve_left hj_bad
  have hj_pos : 0 < j := by
    by_contra h0
    have : j = 0 := by omega
    subst this
    exact hj_bad (allDigitsLe_zero p h)
  set m := j - 1
  have hj_eq : j = m + 1 := by omega
  obtain ⟨k', q, hm_eq, hq_d, hq_mod⟩ := exists_trailingH_decomp hp hp2 m hm_d
  set m_end := j + (p ^ k - 3) / 2 + 1
  set m' := p ^ k' * (q + 1)
  have hlast_dvd : (p : ℤ) ∣ (coeff (j + (p ^ k - 3) / 2)).num :=
    hmid (j + (p ^ k - 3) / 2) (by omega) le_rfl
  have hlast_bad : ¬ AllDigitsLe p h (j + (p ^ k - 3) / 2) :=
    ((odd_prime_dvd_coeff_num_iff_digits hp hp2 _).mp hlast_dvd).1
  have hmend_d : AllDigitsLe p h m_end := by
    by_contra hbad
    apply hend_ndvd
    rw [odd_prime_dvd_coeff_num_iff_digits hp hp2 m_end]
    exact ⟨hbad, by simpa [m_end] using hlast_bad⟩
  have hm'_d : AllDigitsLe p h m' := by
    have hq1 : AllDigitsLe p h (q + 1) :=
      allDigitsLe_succ_of_mod_lt hp.pos (by omega) hq_d hq_mod
    have h0 : m' = p ^ k' * (q + 1) + 0 := by omega
    rw [h0, allDigitsLe_mul_pow_add hp.pos k' (q + 1) 0 (Nat.pow_pos hp.pos)]
    exact ⟨allDigitsLe_zero p h, hq1⟩
  have hlt1 : m < m_end := by omega
  have hlt2 : m < m' := by
    have := halfPow_lt_pow hp hp2 k'
    have : m' = p ^ k' * q + p ^ k' := by ring
    omega
  have hno_mid : ∀ x, m < x → x < m_end → ¬ AllDigitsLe p h x := by
    intro x hx1 hx2
    by_cases hxj : x = j
    · exact hxj ▸ hj_bad
    · exact ((odd_prime_dvd_coeff_num_iff_digits hp hp2 x).mp (hmid x (by omega) (by omega))).1
  have hmend_eq : m' = m_end := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hno_mid m' hlt2 hlt hm'_d
    · exact not_allDigitsLe_in_gap hp hp2 (hm_eq ▸ hlt1) hgt hmend_d
  obtain ⟨hodd, _⟩ := pow_odd_of_odd_prime hp hp2 k
  obtain ⟨hodd', _⟩ := pow_odd_of_odd_prime hp hp2 k'
  have hpow_eq : p ^ k' = p ^ k := by
    have h1 : m' - m = (p ^ k' + 1) / 2 := by
      have : m' = p ^ k' * q + p ^ k' := by ring
      unfold halfPow at hm_eq
      omega
    have h2 : m_end - m = (p ^ k + 1) / 2 := by omega
    rw [hmend_eq] at h1
    omega
  have hk_eq : k' = k := Nat.pow_right_injective hp.two_le hpow_eq
  subst k'
  have hj_new : p * j - h = p ^ (k + 1) * q + halfPow p (k + 1) + 1 := by
    have hhs := halfPow_succ hp hp2 k
    have hjp : p * j = p ^ (k + 1) * q + p * halfPow p k + p := by
      rw [hj_eq, hm_eq, pow_succ']; ring
    omega
  have hlen1 : 0 < (p ^ (k + 1) - 3) / 2 := by
    have : p ^ k < p ^ (k + 1) := Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self k)
    omega
  rw [hj_new]
  exact blockAfter_of_decomp hp hp2 hlen1 hq_d hq_mod

end OMA.Proof_oeis_a002596

theorem OMA.solution : type_of% @OMA.S_oeis_a002596.main := by
  intro p hp
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨?_, ?_⟩
    · intro n hn
      exact absurd hn (OMA.Proof_oeis_a002596.not_two_dvd_coeff_num n)
    · intro j k _ hb
      have hlen : 0 < (2 ^ k - 3) / 2 := hb.1
      have h1 : (2 : ℤ) ∣ (OMA.S_oeis_a002596.coeff (j + 1)).num :=
        hb.2.2.1 (j + 1) (by omega) (by omega)
      exact absurd h1 (OMA.Proof_oeis_a002596.not_two_dvd_coeff_num (j + 1))
  · exact ⟨OMA.Proof_oeis_a002596.main_part1 hp hp2,
      OMA.Proof_oeis_a002596.main_part2 hp hp2⟩

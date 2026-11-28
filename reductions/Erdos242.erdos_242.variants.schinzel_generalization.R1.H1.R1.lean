import OMAReductions.R_Erdos242_erdos_242_variants_schinzel_generalization_R1

/-!
# Reduction to primes and powers of exceptional primes

Every prime has a power with a three-term expansion for each fixed numerator.
This leaves just the large-prime cases for numerator four and for larger numerators.
-/

open Filter
open scoped BigOperators
open Nat

namespace OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1_H1_R1

private theorem scale {a d n : ℕ} (hn : 0 < n) (hd : d ∣ n)
    (h : ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (a / d : ℚ) = 1 / x + 1 / y + 1 / z) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (a / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  obtain ⟨m, hm⟩ := hd
  obtain ⟨x, y, z, hx, hxy, hyz, heq⟩ := h
  have hmpos : 0 < m := by
    by_contra! hzero
    have : m = 0 := by omega
    simp [this] at hm
    omega
  refine ⟨x * m, y * m, z * m, Nat.mul_pos hx hmpos,
    Nat.mul_lt_mul_of_pos_right hxy hmpos, Nat.mul_lt_mul_of_pos_right hyz hmpos, ?_⟩
  simpa only [hm, Nat.cast_mul, div_div, add_div] using
    congrArg (fun q : ℚ => q / (m : ℚ)) heq

private theorem prime_crt {m n r s : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) (hr : r.Coprime m) (hs : s.Coprime n) (bound : ℕ) :
    ∃ q > bound, q.Prime ∧ (q ≡ r [MOD m]) ∧ (q ≡ s [MOD n]) := by
  let t := Nat.chineseRemainder hmn r s
  have htm : (t : ℕ).Coprime m := t.prop.1.gcd_eq.trans hr
  have htn : (t : ℕ).Coprime n := t.prop.2.gcd_eq.trans hs
  obtain ⟨q, hqb, hqp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq bound (mul_ne_zero hm hn) (htm.mul_right htn)
  exact ⟨q, hqb, hqp, (hmod.of_dvd (dvd_mul_right m n)).trans t.prop.1,
    (hmod.of_dvd (dvd_mul_left n m)).trans t.prop.2⟩

private theorem auxiliary_prime {a p : ℕ} (ha : 0 < a) (hp : p.Prime) (hc : p.Coprime a) :
    ∃ q : ℕ, 2 < q ∧ ∃ _ : Fact q.Prime, a ∣ q + 1 ∧ legendreSym q (p : ℤ) = -1 := by
  have ha1 : (a - 1).Coprime a := (Nat.coprime_self_sub_left (by omega : 1 ≤ a)).2 (by simp)
  by_cases hp2 : p = 2
  · subst p
    have h8 : (8 : ℕ).Coprime a := by simpa using hc.pow_left 3
    obtain ⟨q, hqg, hq, hq8, hqa⟩ :=
      prime_crt (by decide : (8 : ℕ) ≠ 0) ha.ne' h8 (by decide : (3 : ℕ).Coprime 8) ha1 2
    have hqp : Fact q.Prime := ⟨hq⟩
    refine ⟨q, hqg, hqp, ?_, ?_⟩
    · exact ((hqa.add_right 1).dvd_iff (dvd_refl a)).mpr (by rw [Nat.sub_add_cancel (by omega : 1 ≤ a)])
    · have hmod8 : q % 8 = 3 := hq8
      apply (legendreSym.eq_neg_one_iff' q (a := 2)).2
      simp only [Nat.cast_ofNat]
      rw [ZMod.exists_sq_eq_two_iff (by omega : q ≠ 2)]
      omega
  · have : Fact p.Prime := ⟨hp⟩
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
      have hodd := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).2 hp2
      omega
    obtain ⟨r, hr, hχ⟩ : ∃ r : ℕ, r.Coprime p ∧
        legendreSym p (r : ℤ) = if p % 4 = 1 then -1 else 1 := by
      by_cases h : p % 4 = 1
      · obtain ⟨z, hz⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
        have hrz : (z.val : ZMod p) = z := ZMod.natCast_zmod_val z
        refine ⟨z.val, ?_, ?_⟩
        · apply (hp.coprime_iff_not_dvd.mpr ?_).symm
          intro hd
          have hz0 : z = 0 := hrz.symm.trans ((ZMod.natCast_eq_zero_iff _ _).2 hd)
          exact hz (hz0 ▸ ⟨0, by simp⟩)
        · rw [if_pos h, legendreSym.eq_neg_one_iff', hrz]
          exact hz
      · exact ⟨1, by simp, by simp [h, legendreSym.at_one]⟩
    let m := 4 * a
    have hm : 0 < m := by dsimp [m]; omega
    have hp_m : p.Coprime m := by
      have hp_two : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr fun hd =>
        hp2 (Nat.le_antisymm (Nat.le_of_dvd (by decide) hd) hp.two_le)
      have hp_four : p.Coprime 4 := by simpa using hp_two.pow_right 2
      exact hp_four.mul_right hc
    have hm1 : (m - 1).Coprime m := (Nat.coprime_self_sub_left (by omega : 1 ≤ m)).2 (by simp)
    obtain ⟨q, hqpgt, hq, hqm, hqr⟩ := prime_crt hm.ne' hp.ne_zero hp_m.symm hm1 hr p
    have hqg : 2 < q := lt_of_le_of_lt hp.two_le hqpgt
    have hqfact : Fact q.Prime := ⟨hq⟩
    have hq4 : q % 4 = 3 := by
      have he : q % 4 = (m - 1) % 4 := hqm.of_dvd (dvd_mul_right 4 a)
      dsimp [m] at he
      omega
    have hqa : a ∣ q + 1 := by
      have he := (hqm.of_dvd (dvd_mul_left a 4)).add_right 1
      refine (he.dvd_iff (dvd_refl a)).mpr ?_
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
      exact dvd_mul_left a 4
    have heq : legendreSym p (q : ℤ) = legendreSym p (r : ℤ) := by
      have hcast := (ZMod.natCast_eq_natCast_iff q r p).2 hqr
      simpa only [legendreSym, Int.cast_natCast] using congrArg (quadraticChar (ZMod p)) hcast
    refine ⟨q, hqg, hqfact, hqa, ?_⟩
    rcases hp4 with h | h
    · rw [legendreSym.quadratic_reciprocity_one_mod_four h (by omega : q ≠ 2), heq, hχ, if_pos h]
    · have hnot : p % 4 ≠ 1 := by omega
      have hrec := legendreSym.quadratic_reciprocity_three_mod_four h hq4
      rw [heq, hχ, if_neg hnot] at hrec
      omega

/-- If `a * c = q + 1` and `q * d = n + 1`, the denominators are `d * c`,
`n * c` and `d * n * c`. -/
private theorem solve_from_divisor {a n q : ℕ} (hq : 2 ≤ q) (hqn : q ≤ n)
    (hqa : a ∣ q + 1) (hqn1 : q ∣ n + 1) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (a / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  obtain ⟨c, hce⟩ := hqa
  obtain ⟨d, hde⟩ := hqn1
  have hcpos : 0 < c := by
    by_contra! h
    have : c = 0 := by omega
    simp [this] at hce
  have hdpos : 1 < d := by
    by_contra! h
    have := Nat.mul_le_mul_left q h
    omega
  have hdn : d < n := by
    have := Nat.mul_le_mul_right d (show 2 ≤ q by omega)
    omega
  have hnpos : 0 < n := by omega
  have hndn : n < d * n := by simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hdpos hnpos
  refine ⟨d * c, n * c, (d * n) * c, ?_,
    Nat.mul_lt_mul_of_pos_right hdn hcpos, Nat.mul_lt_mul_of_pos_right hndn hcpos, ?_⟩
  · exact Nat.mul_pos (by omega) hcpos
  · have hceq : (q : ℚ) + 1 = a * c := by exact_mod_cast hce
    have hdeq : (n : ℚ) + 1 = q * d := by exact_mod_cast hde
    have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hcpos.ne'
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hnpos.ne'
    push_cast
    field_simp [hcq, hdq, hnq]
    linear_combination -(d : ℚ) * hceq - hdeq

private theorem solve_coprime {a p : ℕ} (ha : 0 < a) (hp : p.Prime) (hc : p.Coprime a) :
    ∃ k x y z : ℕ, 2 ≤ k ∧ 1 ≤ x ∧ x < y ∧ y < z ∧
      (a / (p ^ k : ℕ) : ℚ) = 1 / x + 1 / y + 1 / z := by
  obtain ⟨q, hq, hqfact, hqa, hχ⟩ := auxiliary_prime ha hp hc
  let j := q / 2
  let t := 2 * q + 1
  let k := j * t
  let n := p ^ k
  have hj : 0 < j := by dsimp [j]; omega
  have ht : Odd t := ⟨q, rfl⟩
  have htk : t ≤ k := by
    simpa only [k, one_mul] using Nat.mul_le_mul_right t (show 1 ≤ j from hj)
  have hqk : q ≤ k := le_trans (by dsimp [t]; omega) htk
  have hqn : q ≤ n := hqk.trans (Nat.lt_pow_self hp.one_lt).le
  have hne : q ∣ p ^ j + 1 := by
    apply (ZMod.natCast_eq_zero_iff _ _).1
    have he : (p : ZMod q) ^ j = -1 := by
      simpa only [j, hχ, Int.cast_natCast, Int.cast_neg, Int.cast_one] using (legendreSym.eq_pow q (p : ℤ)).symm
    push_cast
    rw [he, neg_add_cancel]
  have hqn1 : q ∣ n + 1 := hne.trans (by
    simpa only [n, k, pow_mul, one_pow] using ht.nat_add_dvd_pow_add_pow (x := p ^ j) (y := 1))
  obtain ⟨x, y, z, hx, hxy, hyz, heq⟩ :=
    solve_from_divisor (a := a) (by omega : 2 ≤ q) hqn hqa hqn1
  exact ⟨k, x, y, z, by omega, hx, hxy, hyz, heq⟩

private theorem solve_prime_power {a p : ℕ} (ha : 0 < a) (hp : p.Prime) :
    ∃ k x y z : ℕ, 2 ≤ k ∧ 1 ≤ x ∧ x < y ∧ y < z ∧
      (a / (p ^ k : ℕ) : ℚ) = 1 / x + 1 / y + 1 / z := by
  let c := a.factorization p
  let b := a / p ^ c
  have hba : b * p ^ c = a := Nat.div_mul_cancel (Nat.ordProj_dvd a p)
  have hb : 0 < b := Nat.ordCompl_pos p ha.ne'
  have hbc : p.Coprime b := Nat.coprime_ordCompl hp ha.ne'
  obtain ⟨k, x, y, z, hk, hx, hxy, hyz, heq⟩ := solve_coprime hb hp hbc
  refine ⟨k + c, x, y, z, by omega, hx, hxy, hyz, ?_⟩
  calc
    (a / (p ^ (k + c) : ℕ) : ℚ) = ((b * p ^ c : ℕ) / (p ^ (k + c) : ℕ) : ℚ) := by rw [hba]
    _ = (b / (p ^ k : ℕ) : ℚ) := by
      have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      push_cast
      rw [pow_add]
      field_simp [hpq]
    _ = 1 / x + 1 / y + 1 / z := heq

-- The Erdős–Straus numerator reduces to sufficiently large primes congruent to one modulo four.
def H1 : Prop :=
  ∀ᶠ p : ℕ in atTop, p.Prime → p % 4 = 1 →
    (∀ q : ℕ, 2 ≤ q → q ≤ p → q ∣ p + 1 → ¬ (4 ∣ q + 1)) →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / p : ℚ) = 1 / x + 1 / y + 1 / z

-- For larger numerators, only sufficiently large primes in the residual classes remain.
def H2 : Prop :=
  ∀ a : ℕ, 5 ≤ a →
    ∀ᶠ p : ℕ in atTop, p.Prime → 0 < p % a ∧ p % a + 2 < a →
      (∀ q : ℕ, 2 ≤ q → q ≤ p → q ∣ p + 1 → ¬ (a ∣ q + 1)) →
      ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
        (a / p : ℚ) = 1 / x + 1 / y + 1 / z

theorem main : H1 → H2 → OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1.H1 := by
  classical
  intro hFour hLarger a ha
  let Admissible (n : ℕ) : Prop :=
    ∀ d : ℕ, d ∣ n → 2 * a ≤ d → 0 < d % a ∧ d % a + 2 < a
  let Splits (n : ℕ) : Prop :=
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (a / n : ℚ) = 1 / x + 1 / y + 1 / z
  change ∀ᶠ n : ℕ in atTop, Admissible n → Splits n
  let NoDivisor (p : ℕ) : Prop :=
    ∀ q : ℕ, 2 ≤ q → q ≤ p → q ∣ p + 1 → ¬ (a ∣ q + 1)
  have hRemaining : ∀ᶠ p : ℕ in atTop,
      p.Prime → 0 < p % a ∧ p % a + 2 < a → NoDivisor p → Splits p := by
    by_cases ha4 : a = 4
    · subst a
      filter_upwards [hFour] with p hs hp hr hq
      exact hs hp (by omega) hq
    · exact hLarger a (by omega)
  have hPrimes : ∀ᶠ p : ℕ in atTop, p.Prime → 0 < p % a ∧ p % a + 2 < a → Splits p := by
    filter_upwards [hRemaining] with p hs hp hr
    by_cases hex : ∃ q : ℕ, 2 ≤ q ∧ q ≤ p ∧ q ∣ p + 1 ∧ a ∣ q + 1
    · obtain ⟨q, hq, hqp, hd, ha'⟩ := hex
      exact solve_from_divisor hq hqp ha' hd
    · exact hs hp hr (fun q hq hqp hd ha' => hex ⟨q, hq, hqp, hd, ha'⟩)
  obtain ⟨B, hB⟩ := eventually_atTop.1 hPrimes
  have hExponent : ∀ p : ℕ, ∃ k : ℕ,
      ∀ n : ℕ, p.Prime → 0 < n → p ^ k ∣ n → Splits n := by
    intro p
    by_cases hp : p.Prime
    · obtain ⟨k, x, y, z, _, hx, hxy, hyz, heq⟩ := solve_prime_power (by omega : 0 < a) hp
      exact ⟨k, fun _ _ hn hd => scale hn hd ⟨x, y, z, hx, hxy, hyz, heq⟩⟩
    · exact ⟨0, fun _ h => (hp h).elim⟩
  choose exponent hExponent using hExponent
  let smallPrimes := (Finset.range (max B (2 * a))).filter Nat.Prime
  let C := ∏ p ∈ smallPrimes, p ^ exponent p
  refine eventually_atTop.2 ⟨C + 1, ?_⟩
  intro n hn hAllowed
  by_contra hNoSplit
  have hnpos : 0 < n := by omega
  have hSupport : n.primeFactors ⊆ smallPrimes := by
    intro p hp
    obtain ⟨hPrimeP, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hPrimeP⟩
    by_contra! hLarge
    have hBp : B ≤ p := le_trans (le_max_left _ _) hLarge
    have hap : 2 * a ≤ p := le_trans (le_max_right _ _) hLarge
    exact hNoSplit (scale hnpos hpdvd (hB p hBp hPrimeP (hAllowed p hpdvd hap)))
  have hBound : n ≤ C := calc
    n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
      Nat.prod_primeFactors_pow_factorization (Nat.ne_of_gt hnpos)
    _ ≤ ∏ p ∈ n.primeFactors, p ^ exponent p := by
      apply Finset.prod_le_prod'
      intro p hp
      have hPrimeP := (Nat.mem_primeFactors.mp hp).1
      apply Nat.pow_le_pow_right hPrimeP.pos
      by_contra! hTooLarge
      exact hNoSplit (hExponent p n hPrimeP hnpos
        ((hPrimeP.pow_dvd_iff_le_factorization (Nat.ne_of_gt hnpos)).2 (le_of_lt hTooLarge)))
    _ ≤ C := by
      apply Finset.prod_le_prod_of_subset_of_one_le' hSupport
      intro p hp _
      have hPrimeP := (Finset.mem_filter.mp hp).2
      exact Nat.one_le_pow _ _ hPrimeP.pos
  omega

private theorem prime_admissible {a p : ℕ} (ha : 4 ≤ a) (hp : p.Prime)
    (hr : 0 < p % a ∧ p % a + 2 < a) :
    ∀ d : ℕ, d ∣ p → 2 * a ≤ d → 0 < d % a ∧ d % a + 2 < a := by
  intro d hd hda
  have hd2 : 2 ≤ d := (show 2 ≤ 2 * 4 by decide).trans ((Nat.mul_le_mul_left 2 ha).trans hda)
  rwa [(Nat.dvd_prime_two_le hp hd2).1 hd]

theorem converse (h : OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1.H1) : H1 ∧ H2 := by
  constructor
  · filter_upwards [h 4 (by decide)] with p hs hp hr _
    exact hs (prime_admissible (by decide) hp (by omega))
  · intro a ha
    filter_upwards [h a (by omega)] with p hs hp hr _
    exact hs (prime_admissible (by omega) hp hr)

end OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1_H1_R1

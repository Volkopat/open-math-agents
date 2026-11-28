import OMAStatements.S_oeis_a394815
import Mathlib

open OMA.S_oeis_a394815 ArithmeticFunction

private theorem prime_power_sigma_dvd {k p : ℕ} (hk : k ≠ 0) (hp : p.Prime) (hd : p ∣ k) :
    sigma 1 (p ^ k.factorization p) ∣ sigma 1 k := by
  rw [sigma_one_apply_prime_pow hp, sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hk]
  simp only [mul_one]
  exact Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hp, hd, hk⟩)

private theorem three_dvd_sigma_two {e : ℕ} (he : Odd e) : 3 ∣ sigma 1 (2 ^ e) := by
  rw [sigma_one_apply_prime_pow Nat.prime_two, Nat.geomSum_eq (by decide : 2 ≤ 2)]
  change 3 ∣ (2 ^ (e + 1) - 1) / 1
  rw [Nat.div_one]
  have hd : 2 ∣ e + 1 := by rw [Nat.odd_iff] at he; omega
  exact Nat.pow_sub_one_dvd_pow_sub_one 2 hd

private theorem even_exponent_of_odd_sigma {p e : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2)
    (hs : ¬ 2 ∣ sigma 1 (p ^ e)) : Even e := by
  have ho : Odd (sigma 1 (p ^ e)) := Nat.not_even_iff_odd.mp (hs ∘ even_iff_two_dvd.mp)
  rw [sigma_one_apply_prime_pow hp, Finset.odd_sum_iff_odd_card_odd] at ho
  have hfilt : (Finset.range (e + 1)).filter (fun i => Odd (p ^ i)) =
      Finset.range (e + 1) :=
    Finset.filter_true_of_mem (fun i _ => (hp.odd_of_ne_two hp₂).pow)
  rw [hfilt, Finset.card_range, Nat.odd_iff] at ho
  exact Nat.even_iff.mpr (by omega)

private theorem midpoint_divisibility {k : ℕ} (ht : TwinMidpoint k) :
    4 ≤ k ∧ 2 ∣ k ∧ (k ≠ 4 → 3 ∣ k) := by
  have hk : 4 ≤ k := by
    have hlow := ht.1.two_le
    by_contra! hlt
    have heq : k = 3 := by omega
    subst k
    exact (by decide : ¬ Nat.Prime 4) ht.2
  have hodd : Odd (k - 1) := ht.1.odd_of_ne_two (by omega)
  have htwo : 2 ∣ k := by
    rw [Nat.odd_iff] at hodd
    omega
  refine ⟨hk, htwo, fun hne => ?_⟩
  have no_three (p : ℕ) (hp : p.Prime) (hlt : 3 < p) : ¬ 3 ∣ p := by
    intro hd
    rcases hp.eq_one_or_self_of_dvd 3 hd with h | h <;> omega
  have h₁ := no_three (k - 1) ht.1 (by omega)
  have h₂ := no_three (k + 1) ht.2 (by omega)
  have hdiv := Nat.mod_add_div k 3
  have hrem := Nat.mod_lt k (by decide : 0 < 3)
  by_cases hzero : k % 3 = 0
  · exact Nat.dvd_iff_mod_eq_zero.mpr hzero
  by_cases hone : k % 3 = 1
  · have hEq : k - 1 = 3 * (k / 3) := by omega
    exact (h₁ (hEq ▸ dvd_mul_right 3 (k / 3))).elim
  · have hEq : k + 1 = 3 * (k / 3 + 1) := by omega
    exact (h₂ (hEq ▸ dvd_mul_right 3 (k / 3 + 1))).elim

private theorem three_dvd_sigma_of_odd_two {k : ℕ} (hk : k ≠ 0) (h₂ : 2 ∣ k)
    (he : Odd (k.factorization 2)) : 3 ∣ sigma 1 k :=
  (three_dvd_sigma_two he).trans (prime_power_sigma_dvd hk Nat.prime_two h₂)

theorem OMA.solution : type_of% @OMA.S_oeis_a394815.main := by
  refine ⟨?_, Set.ext ?_, ?_⟩
  · rintro k ⟨ht, hg⟩
    have ⟨hk, h₂, h₃'⟩ := midpoint_divisibility ht
    have hne : k ≠ 4 := by
      rintro rfl
      rw [divisorGcd, sigma_one_apply] at hg
      exact (by decide : Nat.gcd 4 (∑ d ∈ (4 : ℕ).divisors, d) ≠ 2) hg
    have h₃ := h₃' hne
    have hk0 : k ≠ 0 := by omega
    have even₂ : Even (k.factorization 2) := by
      apply Nat.not_odd_iff_even.mp
      intro ho
      have hd := Nat.dvd_gcd h₃ (three_dvd_sigma_of_odd_two hk0 h₂ ho)
      change 3 ∣ divisorGcd k at hd
      omega
    have pos₂ : 1 ≤ k.factorization 2 := Nat.prime_two.factorization_pos_of_dvd hk0 h₂
    have h₄ : 4 ∣ k :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hk0).mpr (by rw [Nat.even_iff] at even₂; omega : 2 ≤ k.factorization 2)
    have pos₃ : 1 ≤ k.factorization 3 := Nat.prime_three.factorization_pos_of_dvd hk0 h₃
    have ge₃ : 2 ≤ k.factorization 3 := by
      by_contra! hlt
      have he : k.factorization 3 = 1 := by omega
      have hs := prime_power_sigma_dvd hk0 Nat.prime_three h₃
      rw [he, pow_one, sigma_one_apply] at hs
      have heq : (∑ d ∈ (3 : ℕ).divisors, d) = 4 := by decide
      rw [heq] at hs
      have hd := Nat.dvd_gcd h₄ hs
      change 4 ∣ divisorGcd k at hd
      omega
    have h₉ : 9 ∣ k := (Nat.prime_three.pow_dvd_iff_le_factorization hk0).mpr ge₃
    exact (show Nat.Coprime 4 9 by decide).mul_dvd_of_dvd_of_dvd h₄ h₉
  · intro k
    change (TwinMidpoint k ∧ (divisorGcd k).Prime) ↔
      (TwinMidpoint k ∧ divisorGcd k = 2) ∨ (TwinMidpoint k ∧ divisorGcd k = 3)
    constructor
    · rintro ⟨ht, hp⟩
      by_cases hg₂ : divisorGcd k = 2
      · exact Or.inl ⟨ht, hg₂⟩
      right
      refine ⟨ht, ?_⟩
      have ⟨hk, h₂, h₃'⟩ := midpoint_divisibility ht
      have hne : k ≠ 4 := by
        rintro rfl
        rw [divisorGcd, sigma_one_apply] at hp
        exact (by decide : ¬ (Nat.gcd 4 (∑ d ∈ (4 : ℕ).divisors, d)).Prime) hp
      have h₃ := h₃' hne
      have hk0 : k ≠ 0 := by omega
      have hs : ¬ 2 ∣ sigma 1 k := by
        intro hd
        exact hg₂ ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.dvd_gcd h₂ hd)).symm
      have evenFac (p : ℕ) (hm : p ∈ k.primeFactors.erase 2) : Even (k.factorization p) := by
        have hp' := Nat.mem_primeFactors.mp (Finset.mem_erase.mp hm).2
        exact even_exponent_of_odd_sigma hp'.1 (Finset.mem_erase.mp hm).1
          (fun hd => hs (hd.trans (prime_power_sigma_dvd hk0 hp'.1 hp'.2.1)))
      let w := ∏ p ∈ k.primeFactors.erase 2, p ^ (k.factorization p / 2)
      have hw : (∏ p ∈ k.primeFactors.erase 2, p ^ k.factorization p) = w ^ 2 := by
        dsimp [w]
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun p hm => ?_
        rw [← pow_mul]
        obtain ⟨a, ha⟩ := evenFac p hm
        rw [show k.factorization p / 2 * 2 = k.factorization p by omega]
      have hp₂ : 2 ∈ k.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h₂, hk0⟩
      have hfac : k = 2 ^ k.factorization 2 * w ^ 2 := by
        rw [← hw, Finset.mul_prod_erase _ (fun p => p ^ k.factorization p) hp₂]
        exact Nat.prod_primeFactors_pow_factorization hk0
      have ho : Odd (k.factorization 2) := by
        apply Nat.not_even_iff_odd.mp
        rintro ⟨a, ha⟩
        rw [ha, show a + a = a * 2 by omega, pow_mul, ← mul_pow] at hfac
        let z := 2 ^ a * w
        change k = z ^ 2 at hfac
        have hz : 3 ≤ z := by
          by_contra! hlt
          interval_cases z <;> norm_num at hfac <;> omega
        have hd : z - 1 ∣ k - 1 := by rw [hfac]; exact Nat.sub_one_dvd_pow_sub_one z 2
        rcases ht.1.eq_one_or_self_of_dvd (z - 1) hd with hh | hh
        · omega
        · have hzk : z = k := by omega
          nlinarith [hfac, hzk]
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.dvd_gcd h₃ (three_dvd_sigma_of_odd_two hk0 h₂ ho))).symm
    · rintro (⟨ht, hg⟩ | ⟨ht, hg⟩)
      · exact ⟨ht, hg ▸ Nat.prime_two⟩
      · exact ⟨ht, hg ▸ Nat.prime_three⟩
  · rw [Set.disjoint_left]
    rintro k ⟨_, h₂⟩ ⟨_, h₃⟩
    omega
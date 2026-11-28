import OMAStatements.S_oeis_a053624
import Mathlib

-- Problem: A053624, highly composite odd numbers other than 1, 3, 9 end in 5.
-- Upstream: formal-conjectures statements/oeis-a053624.lean (declaration OMA.S_oeis_a053624.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: if a record-setting odd n were prime to 5, any prime factor p > 5 with p^e || n could be
-- replaced by 5^e, giving a smaller odd number with the same number of divisors; so n = 3^a, and
-- for a >= 3 the smaller odd number 3^(a-2) * 5 has 2(a-1) >= a+1 divisors.

namespace OMA.P_oeis_a053624

open OMA.S_oeis_a053624

theorem card_pp (p e : ℕ) (hp : p.Prime) : (p ^ e).divisors.card = e + 1 := by
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

theorem main' : ∀ n : ℕ, IsTerm n → n ≠ 1 → n ≠ 3 → n ≠ 9 → n % 10 = 5 := by
  intro n ⟨hodd, hrec⟩ h1 h3 h9
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  by_contra h5
  have h5' : ¬ 5 ∣ n := by
    intro hd
    apply h5
    omega
  have hall : ∀ {d : ℕ}, Nat.Prime d → d ∣ n → d = 3 := by
    intro d hd hdn
    by_contra hd3
    have hd2 : d ≠ 2 := by
      rintro rfl
      omega
    have hd5 : d ≠ 5 := by
      rintro rfl
      exact h5' hdn
    have hd4 : d ≠ 4 := by
      rintro rfl
      exact absurd hd (by decide)
    have hdgt : 5 < d := by
      have := hd.two_le
      omega
    have hsplit : d ^ (n.factorization d) * (n / d ^ (n.factorization d)) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n d
    have hcop : Nat.Coprime d (n / d ^ (n.factorization d)) := Nat.coprime_ordCompl hd hn0
    have he : 1 ≤ n.factorization d := hd.factorization_pos_of_dvd hn0 hdn
    generalize n.factorization d = e at hsplit hcop he
    generalize n / d ^ e = k at hsplit hcop
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hsplit; omega
      · exact h
    have hkn : k ∣ n := ⟨d ^ e, by rw [← hsplit, mul_comm]⟩
    have hk5 : Nat.Coprime 5 k :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr (fun h => h5' (h.trans hkn))
    have hlt : 5 ^ e * k < n := by
      rw [← hsplit]
      have : 5 ^ e < d ^ e := Nat.pow_lt_pow_left hdgt (by omega)
      exact Nat.mul_lt_mul_of_pos_right this hk0
    have hodd' : Odd (5 ^ e * k) :=
      Odd.mul (Odd.pow (by decide)) (Odd.of_dvd_nat hodd hkn)
    have hcard : (5 ^ e * k).divisors.card = n.divisors.card := by
      conv_rhs => rw [← hsplit]
      rw [Nat.Coprime.card_divisors_mul (Nat.Coprime.pow_left e hk5),
        Nat.Coprime.card_divisors_mul (Nat.Coprime.pow_left e hcop), card_pp 5 e Nat.prime_five,
        card_pp d e hd]
    have := hrec _ hodd' hlt
    omega
  have hpow : n = 3 ^ n.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd hn0 hall
  generalize n.primeFactorsList.length = a at hpow
  subst hpow
  have ha : 3 ≤ a := by
    by_contra hc
    interval_cases a <;> simp_all
  have hlt : 3 ^ (a - 2) * 5 ^ 1 < 3 ^ a := by
    have : 3 ^ a = 3 ^ (a - 2) * 9 := by
      rw [show 9 = 3 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel (by omega)]
    rw [this]
    exact Nat.mul_lt_mul_of_pos_left (by norm_num) (by positivity)
  have hodd' : Odd (3 ^ (a - 2) * 5 ^ 1) := Odd.mul (Odd.pow (by decide)) (by decide)
  have hcard : (3 ^ (a - 2) * 5 ^ 1).divisors.card = (a - 2 + 1) * (1 + 1) := by
    rw [Nat.Coprime.card_divisors_mul (Nat.Coprime.pow _ _ (by norm_num)),
      card_pp 3 _ Nat.prime_three, card_pp 5 1 Nat.prime_five]
  have := hrec _ hodd' hlt
  rw [hcard, card_pp 3 a Nat.prime_three] at this
  omega

end OMA.P_oeis_a053624

theorem OMA.solution : type_of% @OMA.S_oeis_a053624.main := OMA.P_oeis_a053624.main'

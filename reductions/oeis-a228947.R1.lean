import OMAStatements.S_oeis_a228947
import Mathlib

namespace OMA.R_oeis_a228947_R1

open OMA.S_oeis_a228947 ArithmeticFunction

def H1 : Prop := ∀ m : ℕ, Odd m → m.primeFactors.card = 2 →
  ArithmeticFunction.sigma 1 (m ^ 2) ≠ m ^ 2 + Nat.totient (m ^ 2)

def H2 : Prop := ∀ m : ℕ, Odd m → m.primeFactors.card = 3 →
  ArithmeticFunction.sigma 1 (m ^ 2) ≠ m ^ 2 + Nat.totient (m ^ 2)

def H3 : Prop := ∀ m : ℕ, Odd m → 4 ≤ m.primeFactors.card →
  ArithmeticFunction.sigma 1 (m ^ 2) ≠ m ^ 2 + Nat.totient (m ^ 2)

/-- `φ (2 k) ≤ k`. -/
lemma totient_two_mul_le (k : ℕ) : Nat.totient (2 * k) ≤ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | hk
    · rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        simp at hj
        subst hj
        simp
      · have h2 : 2 ∣ 2 * j := dvd_mul_right 2 j
        have hk : k = 2 * j := by omega
        rw [hk, Nat.totient_mul_of_prime_of_dvd Nat.prime_two h2]
        have := ih j (by omega)
        omega
    · have hc : Nat.Coprime 2 k := Nat.coprime_two_left.mpr hk
      rw [Nat.totient_mul hc, Nat.totient_two, one_mul]
      exact Nat.totient_le k

/-- Even `n ≥ 4`: `a n > 0`. -/
lemma a_pos_of_even {n : ℕ} (he : Even n) (h4 : 4 ≤ n) : 0 < a n := by
  obtain ⟨k, rfl⟩ := he
  have hk : 2 ≤ k := by omega
  have hsig : 1 + k + (k + k) ≤ sigma 1 (k + k) := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
    have hsub : ({1, k} : Finset ℕ) ⊆ (k + k).properDivisors := by
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rw [Nat.mem_properDivisors]
      rcases hd with rfl | rfl
      · exact ⟨one_dvd _, by omega⟩
      · exact ⟨⟨2, by ring⟩, by omega⟩
    have h1k : (1 : ℕ) ≠ k := by omega
    have hle := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hsub
    rw [Finset.sum_pair h1k] at hle
    omega
  have hphi : Nat.totient (k + k) ≤ k := by
    have := totient_two_mul_le k
    rwa [two_mul] at this
  unfold a
  push_cast
  omega

/-- For odd `n` that is not a square, `σ n` is even: the divisors pair up as `d, n / d`. -/
lemma sigma_even_of_odd_nonsq {n : ℕ} (hn : Odd n) (hsq : ∀ m, m * m ≠ n) :
    Even (sigma 1 n) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hn) ⟨0, rfl⟩
  rw [sigma_one_apply, ← ZMod.natCast_eq_zero_iff_even, Nat.cast_sum]
  refine Finset.sum_involution (fun d _ => n / d) ?_ ?_ ?_ ?_
  · intro d hd
    have hd' := Nat.mem_divisors.mp hd
    have hodd_d : Odd d := Odd.of_dvd_nat hn hd'.1
    have hodd_q : Odd (n / d) := Odd.of_dvd_nat hn (Nat.div_dvd_of_dvd hd'.1)
    rw [(ZMod.natCast_eq_one_iff_odd).mpr hodd_d, (ZMod.natCast_eq_one_iff_odd).mpr hodd_q]
    decide
  · intro d hd _ heq
    have hd' := Nat.mem_divisors.mp hd
    apply hsq d
    calc d * d = d * (n / d) := by rw [heq]
      _ = n := Nat.mul_div_cancel' hd'.1
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1, hn0⟩
  · intro d hd
    exact Nat.div_div_self (Nat.mem_divisors.mp hd).1 hn0

/-- Odd `n ≥ 3` that is not a square: `a n` is odd. -/
lemma a_ne_zero_of_odd_nonsq {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) (hsq : ∀ m, m * m ≠ n) :
    a n ≠ 0 := by
  obtain ⟨x, hx⟩ := sigma_even_of_odd_nonsq hn hsq
  obtain ⟨y, hy⟩ := Nat.totient_even (by omega : 2 < n)
  obtain ⟨z, hz⟩ := hn
  unfold a
  rw [hx, hy, hz]
  push_cast
  omega

lemma geom_two {p : ℕ} (hp : 3 ≤ p) (k : ℕ) : 2 * (∑ i ∈ Finset.range k, p ^ i) + 1 ≤ p ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : 1 ≤ p ^ k := Nat.one_le_pow k p (by omega)
    nlinarith

/-- Odd prime powers: `σ (p ^ k) < p ^ k + φ (p ^ k)`. -/
lemma a_neg_prime_pow {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 0 < k) : a (p ^ k) < 0 := by
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hs : sigma 1 (p ^ (j + 1)) = (∑ i ∈ Finset.range j, p ^ i) + p ^ j + p ^ (j + 1) := by
    rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_succ]
  have ht : Nat.totient (p ^ (j + 1)) = p ^ j * (p - 1) := by
    rw [Nat.totient_prime_pow hp (by omega)]
    simp
  have hg := geom_two h3 j
  have h2 : p ^ j * 2 ≤ p ^ j * (p - 1) := Nat.mul_le_mul_left _ (by omega)
  have hnat : sigma 1 (p ^ (j + 1)) < p ^ (j + 1) + Nat.totient (p ^ (j + 1)) := by
    rw [hs, ht]
    omega
  unfold a
  omega

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a228947.main := by
  intro hH1 hH2 hH3 n hn
  constructor
  · intro ha
    by_contra hne
    have key : sigma 1 n = n + Nat.totient n := by
      unfold a at ha
      omega
    rcases Nat.even_or_odd n with he | ho
    · have h4 : 4 ≤ n := by
        obtain ⟨k, hk⟩ := he
        omega
      have := a_pos_of_even he h4
      omega
    · by_cases h1n : n = 1
      · subst h1n
        have : a 1 = -1 := by decide
        omega
      · have h3 : 3 ≤ n := by
          obtain ⟨k, hk⟩ := ho
          omega
        by_cases hsq : ∀ m, m * m ≠ n
        · exact a_ne_zero_of_odd_nonsq ho h3 hsq ha
        · push Not at hsq
          obtain ⟨m, hm⟩ := hsq
          have hmo : Odd m := (Nat.odd_mul.mp (hm ▸ ho)).1
          have hn2 : m ^ 2 = n := by rw [← hm]; ring
          rcases Nat.lt_or_ge m.primeFactors.card 2 with hlt | hge
          · rcases Nat.lt_or_ge m.primeFactors.card 1 with h0 | h1c
            · have h0' : m.primeFactors.card = 0 := by omega
              rw [Finset.card_eq_zero, Nat.primeFactors_eq_empty] at h0'
              rcases h0' with rfl | rfl
              · omega
              · omega
            · have hc1 : m.primeFactors.card = 1 := by omega
              obtain ⟨p, k, hp, hk, hpk⟩ :=
                (isPrimePow_nat_iff m).mp (isPrimePow_iff_card_primeFactors_eq_one.mpr hc1)
              have hp2 : p ≠ 2 := by
                rintro rfl
                rw [← hpk] at hmo
                exact (Nat.not_even_iff_odd.mpr hmo) ((Nat.even_pow' (by omega)).mpr even_two)
              have hn' : n = p ^ (2 * k) := by rw [← hn2, ← hpk]; ring
              have := a_neg_prime_pow hp hp2 (by omega : 0 < 2 * k)
              rw [← hn'] at this
              omega
          · rcases Nat.lt_or_ge m.primeFactors.card 4 with h3c | h4c
            · rcases Nat.lt_or_ge m.primeFactors.card 3 with h2c | h3c'
              · apply hH1 m hmo (by omega)
                rw [hn2]
                exact key
              · apply hH2 m hmo (by omega)
                rw [hn2]
                exact key
            · apply hH3 m hmo h4c
              rw [hn2]
              exact key
  · rintro rfl
    decide

end OMA.R_oeis_a228947_R1

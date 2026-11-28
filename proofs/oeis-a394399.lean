import OMAStatements.S_oeis_a394399
import Mathlib

namespace OMA.P_a394399

lemma geom_mod_two {p : ℕ} (hp : p % 2 = 1) (e : ℕ) :
    (∑ i ∈ Finset.range (e + 1), p ^ i) % 2 = (e + 1) % 2 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hp, one_pow]
    omega

lemma sq_or_twice_sq_of_sigma_odd :
    ∀ n : ℕ, Odd (ArithmeticFunction.sigma 1 n) → ∃ m : ℕ, n = m ^ 2 ∨ n = 2 * m ^ 2 := by
  intro n
  induction n using Nat.recOnPrimeCoprime with
  | zero => intro _; exact ⟨0, Or.inl (by simp)⟩
  | prime_pow p e hp =>
    intro h
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp] at h
    rcases hp.eq_two_or_odd with rfl | hpo
    · rcases Nat.even_or_odd' e with ⟨t, rfl | rfl⟩
      · exact ⟨2 ^ t, Or.inl (by ring)⟩
      · exact ⟨2 ^ t, Or.inr (by ring)⟩
    · have := geom_mod_two hpo e
      rw [Nat.odd_iff] at h
      rcases Nat.even_or_odd' e with ⟨t, rfl | rfl⟩
      · exact ⟨p ^ t, Or.inl (by ring)⟩
      · omega
  | coprime a b _ _ hab iha ihb =>
    intro h
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hab, Nat.odd_mul] at h
    obtain ⟨x, hx⟩ := iha h.1
    obtain ⟨y, hy⟩ := ihb h.2
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact ⟨x * y, Or.inl (by ring)⟩
    · exact ⟨x * y, Or.inr (by ring)⟩
    · exact ⟨x * y, Or.inr (by ring)⟩
    · exact ⟨2 * x * y, Or.inl (by ring)⟩


theorem fwd : ∀ k : ℕ, (k - 1).Prime ∧ (k + 1).Prime → Nat.gcd k (ArithmeticFunction.sigma 1 k) = 3 →
      ∃ m : ℕ, k = 2 * m ^ 2 := by
  intro k ⟨hk1, hk2⟩ hg
  have hk3 : 3 ≤ k := by
    have := hk1.two_le
    omega
  -- k is even
  have hkev : k % 2 = 0 := by
    rcases hk1.eq_two_or_odd with h | h
    · have : k = 3 := by omega
      subst this; norm_num at hk2
    · omega
  -- sigma k is odd, since gcd is odd and 2 divides k
  have hsig : Odd (ArithmeticFunction.sigma 1 k) := by
    rw [Nat.odd_iff]
    by_contra hc
    have h2 : 2 ∣ Nat.gcd k (ArithmeticFunction.sigma 1 k) :=
      Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hkev) (Nat.dvd_of_mod_eq_zero (by omega))
    rw [hg] at h2
    norm_num at h2
  obtain ⟨m, hm | hm⟩ := sq_or_twice_sq_of_sigma_odd k hsig
  · exfalso
    subst hm
    have hm2 : 2 ≤ m := by
      by_contra h
      push Not at h
      interval_cases m <;> omega
    have hfac : m ^ 2 - 1 = (m - 1) * (m + 1) := by
      have : (m - 1) * (m + 1) = m ^ 2 - 1 := by
        obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring_nf
        omega
      exact this.symm
    rw [hfac] at hk1
    rcases Nat.prime_mul_iff.1 hk1 with ⟨_, h⟩ | ⟨_, h⟩
    · omega
    · have : m = 2 := by omega
      subst this
      rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two] at hg
      norm_num [Finset.sum_range_succ] at hg
  · exact ⟨m, hm⟩

lemma three_dvd_sigma_two_pow (t : ℕ) : 3 ∣ ArithmeticFunction.sigma 1 (2 ^ (2 * t + 1)) := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show 2 * (t + 1) + 1 + 1 = (2 * t + 1 + 1) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have : 3 ∣ 2 ^ (2 * t + 1 + 1) + 2 ^ (2 * t + 1 + 1 + 1) := by
      rw [show 2 ^ (2 * t + 1 + 1) + 2 ^ (2 * t + 1 + 1 + 1) = 3 * 2 ^ (2 * t + 2) by ring]
      exact dvd_mul_right _ _
    rw [add_assoc]
    exact dvd_add ih this

lemma three_dvd_sigma (m : ℕ) (hm : m ≠ 0) : 3 ∣ ArithmeticFunction.sigma 1 (2 * m ^ 2) := by
  obtain ⟨t, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm
  have hcop : Nat.Coprime (2 ^ (2 * t + 1)) (u ^ 2) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_two_left).2 hu)
  rw [show 2 * (2 ^ t * u) ^ 2 = 2 ^ (2 * t + 1) * u ^ 2 by ring,
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
  exact dvd_mul_of_dvd_left (three_dvd_sigma_two_pow t) _

end OMA.P_a394399

theorem OMA.solution : type_of% @OMA.S_oeis_a394399.main := by
  intro k hk
  unfold OMA.S_oeis_a394399.divisorGcd
  constructor
  · intro hg
    exact ⟨hg ▸ Nat.prime_three, OMA.P_a394399.fwd k hk hg⟩
  · rintro ⟨hp, m, rfl⟩
    obtain ⟨hk1, hk2⟩ := hk
    have hm : m ≠ 0 := by
      rintro rfl
      norm_num at hk1
    have h3k : 3 ∣ 2 * m ^ 2 := by
      have h1 := hk1.eq_one_or_self_of_dvd 3
      have h2 := hk2.eq_one_or_self_of_dvd 3
      by_contra hc
      have : 2 * m ^ 2 % 3 = 1 ∨ 2 * m ^ 2 % 3 = 2 := by omega
      have hm1 : m = 1 ∨ 4 ≤ m ^ 2 := by
        rcases Nat.lt_or_ge m 2 with h' | h'
        · omega
        · right; nlinarith
      rcases hm1 with rfl | hm1
      · norm_num at hk1
      · rcases this with h | h
        · rcases h1 (by omega) with h | h <;> omega
        · rcases h2 (by omega) with h | h <;> omega
    have h3 : 3 ∣ Nat.gcd (2 * m ^ 2) (ArithmeticFunction.sigma 1 (2 * m ^ 2)) :=
      Nat.dvd_gcd h3k (OMA.P_a394399.three_dvd_sigma m hm)
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3).symm

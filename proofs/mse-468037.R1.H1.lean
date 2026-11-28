import OMAReductions.R_mse_468037_R1

-- Step mse-468037.R1.H1: Euler's theorem on odd perfect numbers, N = q^k m^2 with q = k = 1 mod 4.
-- Retains @marcusbuffett’s pending proof #28917; main proof #26760 is by @ppleskov.
-- Standard parity and coprimality APIs replace local case arguments.
-- Credit: @marcusbuffett. For odd n, the claim (sigma n odd implies n is a square, and sigma n = 2
-- mod 4 implies Euler's form) is proved by induction over coprime factorizations
-- (Nat.recOnPosPrimePosCoprime): prime powers by the geometric sum modulo 4, coprime products by
-- multiplicativity of sigma. An odd perfect N has sigma N = 2N = 2 mod 4.

namespace OMA.R_mse_468037_R1

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- The geometric sum `1 + p + ⋯ + p^a` modulo 4 for odd `p`. -/
theorem geom_mod4 (p : ℕ) (a : ℕ) :
    (p % 4 = 1 → (∑ i ∈ range (a + 1), p ^ i) % 4 = (a + 1) % 4) ∧
    (p % 4 = 3 → (∑ i ∈ range (a + 1), p ^ i) % 4 = if a % 2 = 0 then 1 else 0) := by
  induction a with
  | zero => simp
  | succ a ih =>
    obtain ⟨ih1, ih3⟩ := ih
    constructor
    · intro hp
      rw [Finset.sum_range_succ, Nat.add_mod, ih1 hp, Nat.pow_mod, hp, one_pow]
      omega
    · intro hp
      rw [Finset.sum_range_succ, Nat.add_mod, ih3 hp, Nat.pow_mod, hp]
      rcases Nat.even_or_odd (a + 1) with ⟨t, ht⟩ | ⟨t, ht⟩
      · have h9 : 3 ^ (a + 1) % 4 = 1 := by
          rw [ht, ← two_mul, pow_mul, Nat.pow_mod]; norm_num
        rw [h9]; split_ifs <;> omega
      · have h9 : 3 ^ (a + 1) % 4 = 3 := by
          rw [ht, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
        rw [h9]; split_ifs <;> omega

/-- The Euler-form claim for odd `n`, proved over coprime factorizations. -/
def EulerClaim (n : ℕ) : Prop :=
  Odd n →
    (σ 1 n % 2 = 1 → ∃ m, n = m ^ 2) ∧
    (σ 1 n % 4 = 2 → ∃ q k m : ℕ, q.Prime ∧ q % 4 = 1 ∧ k % 4 = 1 ∧ q.Coprime m ∧
      n = q ^ k * m ^ 2)

theorem euler_prime_pow (p a : ℕ) (hp : p.Prime) (ha : 0 < a) : EulerClaim (p ^ a) := by
  intro hodd
  have hpo : Odd p := (Nat.odd_pow_iff ha.ne').mp hodd
  rw [sigma_one_apply_prime_pow hp]
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by
    obtain ⟨t, ht⟩ := hpo; omega
  obtain ⟨g1, g3⟩ := geom_mod4 p a
  constructor
  · intro h2
    have hae : a % 2 = 0 := by
      rcases h4 with h | h
      · have := g1 h; omega
      · have := g3 h; split_ifs at this <;> omega
    exact ⟨p ^ (a / 2), by rw [← pow_mul]; congr 1; omega⟩
  · intro h2
    rcases h4 with h | h
    · have := g1 h
      exact ⟨p, a, 1, hp, h, by omega, Nat.coprime_one_right p, by simp⟩
    · have := g3 h; split_ifs at this <;> omega

theorem euler_mul (a b : ℕ) (hab : a.Coprime b) (ha : EulerClaim a) (hb : EulerClaim b) :
    EulerClaim (a * b) := by
  intro hodd
  have hao : Odd a := Nat.Odd.of_mul_left hodd
  have hbo : Odd b := Nat.Odd.of_mul_right hodd
  obtain ⟨a1, a2⟩ := ha hao
  obtain ⟨b1, b2⟩ := hb hbo
  rw [isMultiplicative_sigma.map_mul_of_coprime hab]
  constructor
  · intro h
    obtain ⟨hsa, hsb⟩ := Nat.odd_mul.mp (Nat.odd_iff.mpr h)
    obtain ⟨m, rfl⟩ := a1 (Nat.odd_iff.mp hsa)
    obtain ⟨m', rfl⟩ := b1 (Nat.odd_iff.mp hsb)
    exact ⟨m * m', by ring⟩
  · intro h
    have hm : (σ 1 a % 4 = 2 ∧ σ 1 b % 2 = 1) ∨ (σ 1 a % 2 = 1 ∧ σ 1 b % 4 = 2) := by
      have e := h
      rw [Nat.mul_mod] at e
      have ra : σ 1 a % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have rb : σ 1 b % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have ka : σ 1 a % 2 = σ 1 a % 4 % 2 := (Nat.mod_mod_of_dvd _ (by norm_num)).symm
      have kb : σ 1 b % 2 = σ 1 b % 4 % 2 := (Nat.mod_mod_of_dvd _ (by norm_num)).symm
      rw [ka, kb]
      interval_cases (σ 1 a % 4) <;> interval_cases (σ 1 b % 4) <;> simp_all
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨q, k, m, hq, hq4, hk4, hqm, rfl⟩ := a2 h1
      obtain ⟨m', rfl⟩ := b1 h2
      refine ⟨q, k, m * m', hq, hq4, hk4, ?_, by ring⟩
      refine Nat.Coprime.mul_right hqm ?_
      have hk : 0 < k := by omega
      have hqa : q ∣ q ^ k * m ^ 2 := Dvd.dvd.mul_right (dvd_pow_self q hk.ne') _
      exact (hab.of_dvd_left hqa).of_dvd_right (dvd_pow_self _ (by decide))
    · obtain ⟨m', rfl⟩ := a1 h1
      obtain ⟨q, k, m, hq, hq4, hk4, hqm, rfl⟩ := b2 h2
      refine ⟨q, k, m' * m, hq, hq4, hk4, ?_, by ring⟩
      refine Nat.Coprime.mul_right ?_ hqm
      have hk : 0 < k := by omega
      have hqb : q ∣ q ^ k * m ^ 2 := Dvd.dvd.mul_right (dvd_pow_self q hk.ne') _
      exact (hab.symm.of_dvd_left hqb).of_dvd_right (dvd_pow_self _ (by decide))

theorem euler_claim : ∀ n, EulerClaim n := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p a hp ha => exact euler_prime_pow p a hp ha
  | zero => intro h; exact absurd h (by decide)
  | one =>
    intro _
    refine ⟨fun _ => ⟨1, rfl⟩, fun h => ?_⟩
    simp at h
  | coprime a b _ _ hab ha hb => exact euler_mul a b hab ha hb

/-- Euler's theorem: an odd perfect number has the form `q^k m^2`, `q ≡ k ≡ 1 (mod 4)`. -/
theorem euler_odd_perfect (N : ℕ) (hN : Odd N) (hp : N.Perfect) :
    ∃ q k m : ℕ, q.Prime ∧ q % 4 = 1 ∧ k % 4 = 1 ∧ q.Coprime m ∧ N = q ^ k * m ^ 2 := by
  have hpos : 0 < N := hp.2
  have hs : σ 1 N = 2 * N := by
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hp
  refine (euler_claim N hN).2 ?_
  rw [hs]
  obtain ⟨t, ht⟩ := hN
  omega

end OMA.R_mse_468037_R1

theorem OMA.solution : OMA.R_mse_468037_R1.H1 := fun N hN hp =>
  OMA.R_mse_468037_R1.euler_odd_perfect N hN hp

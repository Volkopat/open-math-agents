import OMAStatements.S_oeis_a074216
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic.Ring

/-! Mathar's conjecture for OEIS A074216: the positive squares `m` with `3 ∣ σ m` are exactly the
`r ^ 2` with `r ∈ A072864`.

Only `k = 2` matters in the definition of A072864, and `σ (2 r ^ 2)` is always odd: writing
`r = 2 ^ a s` with `s` odd, `σ (2 r ^ 2) = σ (2 ^ (2 a + 1)) σ (s ^ 2)`, the first factor is
`2 ^ (2 a + 2) - 1` and the second is a product of sums of an odd number of odd powers. Writing
`r = 3 ^ b t` with `3 ∤ t`, `σ (3 ^ e) ≡ 1 (mod 3)`, so `3 ∣ σ (3 r ^ 2) ↔ 3 ∣ σ (t ^ 2) ↔
3 ∣ σ (r ^ 2)`. -/

namespace OpenMath.A074216

open Finset OMA.S_oeis_a074216

private theorem sigma_eq (m : ℕ) : sigma m = ArithmeticFunction.sigma 1 m :=
  (ArithmeticFunction.sigma_one_apply m).symm

/-- `(∑_{k ≤ n} p ^ k) % p = 1` for `p ≥ 2`. -/
private theorem geom_mod (p n : ℕ) (hp : 2 ≤ p) : (∑ k ∈ range (n + 1), p ^ k) % p = 1 := by
  rw [Finset.sum_range_succ', pow_zero]
  obtain ⟨c, hc⟩ : p ∣ ∑ k ∈ range n, p ^ (k + 1) :=
    Finset.dvd_sum fun k _ => dvd_pow_self p (Nat.succ_ne_zero k)
  rw [hc, add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- For odd `p`, `∑_{k < n} p ^ k ≡ n (mod 2)`. -/
private theorem odd_geom (p n : ℕ) (hp : p % 2 = 1) : (∑ k ∈ range n, p ^ k) % 2 = n % 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hp, one_pow]
    omega

/-- `σ (s ^ 2)` is odd for odd `s`. -/
private theorem sq_odd : ∀ s : ℕ, s % 2 = 1 → ArithmeticFunction.sigma 1 (s ^ 2) % 2 = 1 := by
  intro s
  induction s using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro hs
    have hp2 : p % 2 = 1 := by
      rcases Nat.even_or_odd p with ⟨c, hc⟩ | hpo
      · exfalso
        have : 2 ∣ p ^ n := (show 2 ∣ p from ⟨c, by omega⟩).trans (dvd_pow_self p (by omega))
        omega
      · exact Nat.odd_iff.1 hpo
    rw [← pow_mul, ArithmeticFunction.sigma_one_apply_prime_pow hp, odd_geom p _ hp2]
    omega
  | zero =>
    intro h
    simp at h
  | one =>
    intro _
    simp
  | coprime a b ha hb hab iha ihb =>
    intro hs
    have hodd := Nat.odd_mul.1 (Nat.odd_iff.2 hs)
    have h := Nat.mul_mod (ArithmeticFunction.sigma 1 (a ^ 2))
      (ArithmeticFunction.sigma 1 (b ^ 2)) 2
    rw [iha (Nat.odd_iff.1 hodd.1), ihb (Nat.odd_iff.1 hodd.2)] at h
    rw [mul_pow,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (Nat.Coprime.pow 2 2 hab)]
    omega

/-- `σ (2 r ^ 2)` is odd. -/
private theorem two_sq_odd (r : ℕ) (hr : 1 ≤ r) :
    ArithmeticFunction.sigma 1 (2 * r ^ 2) % 2 = 1 := by
  obtain ⟨a, s, hs, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show r ≠ 0 by omega) 2 (by norm_num)
  have hs2 : s % 2 = 1 := by omega
  have hcop : Nat.Coprime (2 ^ (2 * a + 1)) (s ^ 2) :=
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hs)
  have e : 2 * (2 ^ a * s) ^ 2 = 2 ^ (2 * a + 1) * s ^ 2 := by ring
  have h1 : ArithmeticFunction.sigma 1 (2 ^ (2 * a + 1)) % 2 = 1 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
    exact geom_mod 2 _ le_rfl
  have h := Nat.mul_mod (ArithmeticFunction.sigma 1 (2 ^ (2 * a + 1)))
    (ArithmeticFunction.sigma 1 (s ^ 2)) 2
  rw [h1, sq_odd s hs2] at h
  rw [e, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
  omega

/-- `3 ∣ σ (3 r ^ 2) ↔ 3 ∣ σ (r ^ 2)`. -/
private theorem three_iff (r : ℕ) (hr : 1 ≤ r) :
    3 ∣ ArithmeticFunction.sigma 1 (3 * r ^ 2) ↔ 3 ∣ ArithmeticFunction.sigma 1 (r ^ 2) := by
  obtain ⟨b, t, ht, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show r ≠ 0 by omega) 3 (by norm_num)
  have hcop : ∀ e, Nat.Coprime (3 ^ e) (t ^ 2) := fun e =>
    Nat.Coprime.pow _ _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 ht)
  have hσ : ∀ e, Nat.Coprime 3 (ArithmeticFunction.sigma 1 (3 ^ e)) := fun e => by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three,
      ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_three]
    have := geom_mod 3 e (by norm_num)
    omega
  have e1 : 3 * (3 ^ b * t) ^ 2 = 3 ^ (2 * b + 1) * t ^ 2 := by ring
  have e2 : (3 ^ b * t) ^ 2 = 3 ^ (2 * b) * t ^ 2 := by ring
  rw [e1, e2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop _),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop _),
    (hσ _).dvd_mul_left, (hσ _).dvd_mul_left]

private theorem key (r : ℕ) (hr : 1 ≤ r) : IsInA074216 (r ^ 2) ↔ IsInA072864 r := by
  unfold IsInA074216 IsInA072864
  rw [sigma_eq, sigma_eq, ← three_iff r hr]
  constructor
  · rintro ⟨-, -, h3⟩
    refine ⟨hr, fun k hk hdvd => ?_, h3⟩
    by_contra hk3
    obtain rfl : k = 2 := by omega
    rw [sigma_eq] at hdvd
    have := two_sq_odd r hr
    omega
  · rintro ⟨-, -, h3⟩
    exact ⟨Nat.one_le_pow _ _ (by omega), ⟨r, rfl⟩, h3⟩

theorem main :
    (∀ m : ℕ, IsInA074216 m ↔ ∃ r : ℕ, IsInA072864 r ∧ m = r ^ 2) ∧
    (∀ r : ℕ, 1 ≤ r → (IsInA074216 (r ^ 2) ↔ IsInA072864 r)) := by
  refine ⟨fun m => ⟨fun h => ?_, ?_⟩, key⟩
  · obtain ⟨hm, ⟨r, rfl⟩, h3⟩ := h
    have hr : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | h
      · simp at hm
      · exact h
    exact ⟨r, (key r hr).1 ⟨hm, ⟨r, rfl⟩, h3⟩, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact (key r hr.1).2 hr

end OpenMath.A074216

theorem OMA.solution : type_of% @OMA.S_oeis_a074216.main := OpenMath.A074216.main

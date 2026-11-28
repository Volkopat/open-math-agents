import OMAStatements.S_oeis_a094470

/-!
For k = 48,787,256,780,937,500 the totient divides the sum of the squares
of the divisors. It is a multiple of 7, whereas the sum of divisor powers
is 5 modulo 7 at every positive exponent divisible by 6.
-/

namespace TotientCounterexample

open OMA.S_oeis_a094470 ArithmeticFunction Finset

private def k : ℕ := 2^2 * 5^7 * 7^1 * 443^1 * 50344799^1

private theorem c₁ : (2^2).Coprime (5^7) := by decide
private theorem c₂ : (2^2*5^7).Coprime (7^1) := by decide
private theorem c₃ : (2^2*5^7*7^1).Coprime (443^1) := by decide
private theorem c₄ : (2^2*5^7*7^1*443^1).Coprime (50344799^1) := by decide

private theorem large_prime : Nat.Prime 50344799 := by norm_num
private theorem prime_443 : Nat.Prime 443 := by norm_num

private theorem totient_value : k.totient = 16689300537000000 := by
  rw [k, Nat.totient_mul c₄, Nat.totient_mul c₃, Nat.totient_mul c₂, Nat.totient_mul c₁,
    Nat.totient_prime_pow Nat.prime_two (by decide), Nat.totient_prime_pow Nat.prime_five (by decide),
    Nat.totient_prime_pow (by decide : Nat.Prime 7) (by decide),
    Nat.totient_prime_pow prime_443 (by decide), Nat.totient_prime_pow large_prime (by decide)]
  decide

private def geometric (q e : ℕ) : ℕ := ∑ i ∈ range (e+1), q^i

private theorem power_sum (m : ℕ) : sigmaPow m k =
    geometric (2^m) 2 * geometric (5^m) 7 * geometric (7^m) 1 *
    geometric (443^m) 1 * geometric (50344799^m) 1 := by
  change sigma m k = _
  rw [k, isMultiplicative_sigma.map_mul_of_coprime c₄,
    isMultiplicative_sigma.map_mul_of_coprime c₃, isMultiplicative_sigma.map_mul_of_coprime c₂,
    isMultiplicative_sigma.map_mul_of_coprime c₁, sigma_apply_prime_pow Nat.prime_two,
    sigma_apply_prime_pow Nat.prime_five, sigma_apply_prime_pow (by decide : Nat.Prime 7),
    sigma_apply_prime_pow prime_443, sigma_apply_prime_pow large_prime]
  simp only [geometric, ← pow_mul, Nat.mul_comm m]

private theorem squares_divisible : k.totient ∣ sigmaPow 2 k := by
  rw [totient_value, power_sum]
  decide

private theorem residue (t : ℕ) : (sigmaPow (6*(t+1)) k : ZMod 7) = 5 := by
  rw [power_sum]
  simp only [geometric, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat, pow_mul,
    show (2 : ZMod 7)^6 = 1 by decide, show (5 : ZMod 7)^6 = 1 by decide,
    show (7 : ZMod 7)^6 = 0 by decide, show (443 : ZMod 7)^6 = 1 by decide,
    show (50344799 : ZMod 7)^6 = 1 by decide, one_pow, zero_pow (Nat.succ_ne_zero t)]
  decide

theorem six_multiples_fail (t : ℕ) : ¬ k.totient ∣ sigmaPow (6*(t+1)) k := by
  intro h
  have seven : 7 ∣ k.totient := by rw [totient_value]; decide
  have eq := (ZMod.natCast_eq_zero_iff (sigmaPow (6*(t+1)) k) 7).mpr (seven.trans h)
  rw [residue] at eq
  exact (by decide : (5 : ZMod 7) ≠ 0) eq

end TotientCounterexample

open OMA.S_oeis_a094470 TotientCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a094470.main) := by
  intro claim
  exact six_multiples_fail 0 (claim 1 k (by decide) squares_divisible)

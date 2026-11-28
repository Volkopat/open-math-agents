import FormalConjectures.Wikipedia.HyperperfectNumber
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.List.Prime

/-! Verification of Alexander Violette's four-prime-factor example, recorded in
OEIS A007593. The auxiliary Lucas certificates use binary exponentiation. -/

namespace OMA.Hyper

lemma pow_binary {R : Type*} [Monoid R] (a : R) (n : ℕ) : a ^ n = npowBinRec n a := by
  induction n with
  | zero => simp [npowBinRec_zero]
  | succ n ih => rw [pow_succ, npowBinRec_succ, ih]

lemma prime_certificate (p a : ℕ) (factors : List ℕ)
    (primes : ∀ q ∈ factors, Nat.Prime q) (prod : factors.prod = p-1 := by decide)
    (full : npowBinRec (p-1) (a : ZMod p) = 1 := by decide)
    (parts : ∀ q ∈ factors, npowBinRec ((p-1)/q) (a : ZMod p) ≠ 1 := by decide) : p.Prime := by
  apply lucas_primality p (a : ZMod p)
  · rwa [pow_binary]
  · intro q hq hd
    rw [← prod] at hd
    obtain ⟨r,hr,hqr⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    have he := (Nat.prime_dvd_prime_iff_eq hq (primes r hr)).mp hqr
    subst r
    rw [pow_binary]
    exact parts q hr

lemma prime_129140227 : Nat.Prime 129140227 :=
  prime_certificate _ 5 [2, 3, 3, 19, 107, 3529] (by norm_num)

lemma prime_12211 : Nat.Prime 12211 :=
  prime_certificate _ 2 [2, 3, 5, 11, 37] (by norm_num)

lemma prime_22346131 : Nat.Prime 22346131 :=
  prime_certificate _ 2 [2, 3, 5, 61, 12211] (by norm_num [prime_12211])

lemma prime_256572153302107 : Nat.Prime 256572153302107 :=
  prime_certificate _ 2 [2, 3, 991, 1931, 22346131] (by norm_num [prime_22346131])

lemma prime_894301 : Nat.Prime 894301 :=
  prime_certificate _ 2 [2, 2, 3, 5, 5, 11, 271] (by norm_num)

lemma prime_11047 : Nat.Prime 11047 :=
  prime_certificate _ 3 [2, 3, 7, 263] (by norm_num)

lemma prime_137002507849 : Nat.Prime 137002507849 :=
  prime_certificate _ 29 [2, 2, 2, 3, 3, 23, 11047, 7489] (by norm_num [prime_11047])

lemma prime_14029501 : Nat.Prime 14029501 :=
  prime_certificate _ 7 [2, 2, 3, 5, 5, 5, 47, 199] (by norm_num)

lemma prime_153174091919 : Nat.Prime 153174091919 :=
  prime_certificate _ 7 [2, 53, 103, 14029501] (by norm_num [prime_14029501])

set_option maxRecDepth 16000 in
lemma prime_225205396855537107298933866373 : Nat.Prime 225205396855537107298933866373 :=
  prime_certificate _ 2 [2, 2, 3, 894301, 137002507849, 153174091919] (by norm_num [prime_894301, prime_137002507849, prime_153174091919])

def witness : ℕ := 3^16 * 129140227 * 256572153302107 * 225205396855537107298933866373

lemma sigma_prime {p : ℕ} (hp : p.Prime) : ∑ d ∈ p.divisors, d = 1+p := by
  rw [hp.divisors]
  simp [Ne.symm hp.ne_one]

set_option maxRecDepth 16000 in
lemma hyperperfect : HyperperfectNumber.IsHyperperfect 2 witness := by
  have hs : ∑ d ∈ witness.divisors, d = 481815972342169646750532492006321534970028262796740230327456 := by
    unfold witness
    rw [Nat.Coprime.sum_divisors_mul (by decide : (3^16 * 129140227 * 256572153302107).Coprime 225205396855537107298933866373),
      Nat.Coprime.sum_divisors_mul (by decide : (3^16 * 129140227).Coprime 256572153302107),
      Nat.Coprime.sum_divisors_mul (by decide : (3^16).Coprime 129140227),
      sigma_prime prime_129140227, sigma_prime prime_256572153302107, sigma_prime prime_225205396855537107298933866373,
      Nat.sum_divisors_prime_pow Nat.prime_three]
    decide
  have finish (n z : ℕ) (hn : n = 321210648228113097833688328004214356646685508531160153551637)
      (hz : z + n = 481815972342169646750532492006321534970028262796740230327456) : n = 1 + 2 * (z - 1) := by omega
  exact ⟨by decide, by decide, finish witness _ (by decide)
    ((Nat.sum_divisors_eq_sum_properDivisors_add_self (n := witness)).symm.trans hs)⟩

end OMA.Hyper

open OMA.Hyper

theorem OMA.solution : type_of% @HyperperfectNumber.two_hyperperfect_characterization := by
  intro h
  obtain ⟨m, _, _, he⟩ := h witness hyperperfect
  have hm : m ≤ 16 := by
    by_contra! hgt
    have hd : 3^17 ∣ witness := he ▸ dvd_mul_of_dvd_left (pow_dvd_pow 3 hgt) _
    exact (by decide : ¬ 3^17 ∣ witness) hd
  have h1 : (3 : ℕ)^m ≤ 3^16 := Nat.pow_le_pow_right (by decide) hm
  have h2 : (3 : ℕ)^(m+1) ≤ 3^17 := Nat.pow_le_pow_right (by decide) (by omega)
  have bound := Nat.mul_le_mul h1 (show 3^(m+1)-2 ≤ 3^17 by omega)
  rw [← he] at bound
  exact (by decide : ¬ witness ≤ 3^16 * 3^17) bound

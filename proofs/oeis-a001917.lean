import OMAStatements.S_oeis_a001917
import Mathlib.Tactic

namespace A001917

-- The three failed powers rule out all proper divisors of 364 as orders.
private lemma order_certificate (m : ℕ)
    (top : 2^364 % m = 1 % m)
    (h2 : 2^182 % m ≠ 1 % m)
    (h7 : 2^52 % m ≠ 1 % m)
    (h13 : 2^28 % m ≠ 1 % m) : orderOf (2 : ZMod m) = 364 := by
  have cast_pow (e : ℕ) :
      (2 : ZMod m)^e = 1 ↔ 2^e % m = 1 % m := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff' (2^e) 1 m)
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) ((cast_pow 364).2 top)
  intro p hp hdvd
  have hm := hp.mem_primeFactors hdvd (by decide : (364 : ℕ) ≠ 0)
  rw [show (364 : ℕ).primeFactors = ({2, 7, 13} : Finset ℕ) by decide +kernel] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with (rfl | rfl | rfl)
  · exact mt (cast_pow 182).1 h2
  · exact mt (cast_pow 52).1 h7
  · exact mt (cast_pow 28).1 h13

end A001917

-- p = 1093: 2 has order 364 mod p and mod p², so the p² term alone of cosets (p²) exceeds 2 * 3.
open OMA.S_oeis_a001917 A001917 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a001917.main) := by
  intro h
  have key (p : ℕ) (hp : p.Prime) (h1 : orderOf (2 : ZMod p) = 364)
      (h2 : orderOf (2 : ZMod (p^2)) = 364) (h3 : (p - 1) / 364 = 3)
      (h7 : 7 ≤ p * (p - 1) / 364) : False := by
    have := Finset.single_le_sum (fun d _ => Nat.zero_le (d.totient / orderOf (2 : ZMod d)))
      (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, (pow_pos hp.pos 2).ne'⟩,
        one_lt_pow₀ hp.one_lt two_ne_zero⟩)
    rw [h2, Nat.totient_prime_pow hp two_pos, ← cosets, ← h p 2 hp (by rintro rfl; simp at h3)
      two_pos, primeTerm, h1, h3] at this
    norm_num at this
    omega
  exact key 1093 (by norm_num)
    (order_certificate _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel))
    (order_certificate _ (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)) (by norm_num) (by norm_num)

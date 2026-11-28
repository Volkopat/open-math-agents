import OMAReductions.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1
import Mathlib

-- Step Erdos313.erdos_313.variants.primary_pseudoperfect_are_infinite.R1.H2.R1.H1: hypothesis H1 of
-- reduction Erdos313.erdos_313.variants.primary_pseudoperfect_are_infinite.R1.H2.R1
-- Credit: @ivillar. Witness: the prime factors 2, 3, 11, 23, 31, 47059, 2217342227, 1729101023519 of the
-- primary pseudoperfect number 8490421583559688410706771261086 (OEIS A054377); the three large
-- primes are certified with Lucas (Pratt) certificates.

/-! Eight primes forming a primary pseudoperfect set. -/

namespace P7E313H1

def pm (a m : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | f+1, e => (if e % 2 = 1 then a else 1) * pm a m f (e/2) ^ 2 % m

theorem pm_eq (a m : ℕ) : ∀ f e, e < 2^f → pm a m f e ≡ a^e [MOD m]
  | 0, e, h => by
    obtain rfl : e = 0 := by simpa using h
    rfl
  | f+1, e, h => by
    have ih := pm_eq a m f (e/2) (by rw [pow_succ] at h; omega)
    have hx : (if e % 2 = 1 then a else 1) ≡ a^(e%2) [MOD m] := by
      rcases Nat.mod_two_eq_zero_or_one e with h | h <;> simp [h] <;> rfl
    rw [show a^e = a^(e%2) * (a^(e/2))^2 by rw [← pow_mul, ← pow_add]; congr 1; omega]
    exact (Nat.mod_modEq _ _).trans (hx.mul (ih.pow 2))

theorem L (p a : ℕ) (l : List ℕ) (hl : ∀ q ∈ l, q.Prime)
    (h : 1 < p ∧ p < 2^99 ∧ l.prod ^ 99 % (p-1) = 0 ∧ pm a p 99 (p-1) = 1 ∧
      l.all (fun q => pm a p 99 ((p-1)/q) ≠ 1) := by decide +kernel) : p.Prime := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have k (e) (he : e ≤ p - 1) : (a : ZMod p)^e = 1 ↔ pm a p 99 e = 1 := by
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', ← pm_eq a p 99 e (by omega),
      Nat.one_mod_eq_one.mpr (by omega), show pm a p 99 e % p = pm a p 99 e from Nat.mod_mod _ _]
  refine lucas_primality p a ((k _ le_rfl).mpr h3) fun q hq hd => ?_
  obtain ⟨r, hr, hqr⟩ := (Prime.dvd_prod_iff hq.prime).mp
    (hq.dvd_of_dvd_pow (hd.trans (Nat.dvd_of_mod_eq_zero h2)))
  rw [(Nat.prime_dvd_prime_iff_eq hq (hl r hr)).mp hqr, Ne, k _ (Nat.div_le_self _ _)]
  simpa using List.all_eq_true.mp h4 r hr

lemma prime_2217342227 : Nat.Prime 2217342227 := L _ 2 [2,11,100788283] (by norm_num)
lemma prime_78595501069 : Nat.Prime 78595501069 := L _ 2 [2,3,7,29,398323] (by norm_num)
lemma prime_1729101023519 : Nat.Prime 1729101023519 :=
  L _ 11 [2,11,78595501069] (by simp [prime_78595501069]; norm_num)

end P7E313H1

open P7E313H1

theorem OMA.solution :
    OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1.H1 := by
  unfold OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1.H1
  refine ⟨{2, 3, 11, 23, 31, 47059, 2217342227, 1729101023519}, by decide, ⟨2, by simp⟩, ?_, ?_, ?_⟩
  · simp [prime_2217342227, prime_1729101023519]; norm_num
  · decide
  · rw [← sub_pos]
    norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]


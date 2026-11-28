import OMAStatements.S_oeis_a006579

-- Varun Vejalla (2025) found this counterexample to Thomas Ordowski's conjecture.
-- The gcd sum over a full residue system is the convolution of totient and identity.

namespace OMA.A006579

open Finset ArithmeticFunction

def phi : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

def pillai : ArithmeticFunction ℕ := phi * ArithmeticFunction.id

lemma apply_pillai (n : ℕ) : pillai n = ∑ d ∈ n.divisors, (n / d).totient * d := by
  rw [pillai, mul_comm, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d e => ArithmeticFunction.id d * phi e)]
  simp [phi, mul_comm]

lemma gcdSum_add (n : ℕ) (hn : 0 < n) :
    OMA.S_oeis_a006579.gcdSum n + n = pillai n := by
  trans (range n).sum n.gcd
  · rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hn, Nat.gcd_zero_right,
      OMA.S_oeis_a006579.gcdSum, add_comm]
  · rw [apply_pillai]
    refine (sum_fiberwise_of_maps_to' (g := n.gcd) (t := n.divisors)
      (fun k _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n k, hn.ne'⟩) id).symm.trans ?_
    exact sum_congr rfl fun d hd => by
      rw [sum_const, nsmul_eq_mul, ← Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]
      rfl

lemma pillai_prime {p : ℕ} (hp : p.Prime) : pillai p = 2 * p - 1 := by
  rw [apply_pillai, hp.divisors, sum_pair hp.ne_one.symm]
  simp [Nat.totient_prime hp, Nat.div_self hp.pos]
  omega

end OMA.A006579

open OMA.A006579 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a006579.main) := by
  intro h
  let ps : Finset ℕ := {3, 37, 43, 42307, 116341}
  have hp : ∀ p ∈ ps, Nat.Prime p := by
    intro p hp
    simp [ps] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hm : pillai.IsMultiplicative :=
    (show phi.IsMultiplicative from ⟨by simp [phi], fun h => Nat.totient_mul h⟩).mul
      ArithmeticFunction.isMultiplicative_id
  have hv : pillai 23492890653051 = 610815156979325 := by
    rw [show 23492890653051 = ∏ p ∈ ps, p by decide, hm.map_prod_of_prime _ hp]
    exact (Finset.prod_congr rfl fun p hp' => pillai_prime (hp p hp')).trans (by decide)
  have hg := Nat.eq_sub_of_add_eq ((gcdSum_add 23492890653051 (by decide)).trans hv)
  apply h 23492890653051 (by decide) (Nat.not_prime_of_dvd_of_lt (m := 3) (by decide) (by decide) (by decide))
  rw [hg]
  decide

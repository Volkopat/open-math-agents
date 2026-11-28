import OMAStatements.S_oeis_a231548

-- Problem: A231548: Numbers n such that 2*n - 1 < sigma(n) - sigma(n-2).
-- Upstream: formal-conjectures statements/oeis-a231548.lean:0 (declaration OMA.S_oeis_a231548.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: n = 332640 = 2^5 * 3^3 * 5 * 7 * 11 is a counterexample. For every n,
-- antisigma(n) + (sum of the proper divisors of n) = 1 + 2 + ... + (n-1) = n(n-1)/2 and
-- sigma(n) = (sum of the proper divisors of n) + n. By multiplicativity sigma(332640) = 1451520,
-- and 332637 = 3 * 110879 with 110879 prime gives sigma(332637) = 4 * 110880 = 443520. Hence
-- antisigma(332640) = 55323399600 < 55323409683 = antisigma(332637).

namespace L05A231548

open OMA.S_oeis_a231548

theorem decomp (n : ℕ) :
    ∑ d ∈ n.properDivisors, d + antisigma n = ∑ k ∈ Finset.Ico 1 n, k :=
  Finset.sum_filter_add_sum_filter_not (Finset.Ico 1 n) (fun k => k ∣ n) (fun k => k)

theorem gauss (N : ℕ) (hN : 1 ≤ N) : (∑ k ∈ Finset.Ico 1 N, k) * 2 = N * (N - 1) := by
  have h1 := Finset.sum_Ico_consecutive (fun k => k) (Nat.zero_le 1) hN
  have h2 : ∑ i ∈ Finset.Ico 0 1, i = 0 := by decide
  rw [h2, zero_add] at h1
  rw [h1, Nat.Ico_zero_eq_range]
  exact Finset.sum_range_id_mul_two N

theorem sig_prime (p : ℕ) (hp : p.Prime) : ArithmeticFunction.sigma 1 p = p + 1 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp
  rw [pow_one] at h
  rw [h, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
  omega

theorem sig32 : ArithmeticFunction.sigma 1 32 = 63 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (i := 5) Nat.prime_two
  have e : ∑ k ∈ Finset.range (5 + 1), 2 ^ k = 63 := by decide
  rw [e] at h
  exact h

theorem sig27 : ArithmeticFunction.sigma 1 27 = 40 := by
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (i := 3) Nat.prime_three
  have e : ∑ k ∈ Finset.range (3 + 1), 3 ^ k = 40 := by decide
  rw [e] at h
  exact h

-- Multiplicativity is applied once, to variables (mulstep); the numeric instances below only
-- evaluate products and sums of numerals with the Nat.reduceMul and Nat.reduceAdd simprocs.

theorem mulstep (a b va vb : ℕ) (hc : Nat.Coprime a b) (ha : ArithmeticFunction.sigma 1 a = va)
    (hb : ArithmeticFunction.sigma 1 b = vb) : ArithmeticFunction.sigma 1 (a * b) = va * vb := by
  have e := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hc
  rw [ha, hb] at e
  exact e

theorem s864 : ArithmeticFunction.sigma 1 864 = 2520 := by
  have h := mulstep 32 27 63 40 (by decide) sig32 sig27
  simp only [Nat.reduceMul] at h
  exact h

theorem s4320 : ArithmeticFunction.sigma 1 4320 = 15120 := by
  have h := mulstep 864 5 2520 (5 + 1) (by decide) s864 (sig_prime 5 (by norm_num))
  simp only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

theorem s30240 : ArithmeticFunction.sigma 1 30240 = 120960 := by
  have h := mulstep 4320 7 15120 (7 + 1) (by decide) s4320 (sig_prime 7 (by norm_num))
  simp only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

theorem sigN : ArithmeticFunction.sigma 1 332640 = 1451520 := by
  have h := mulstep 30240 11 120960 (11 + 1) (by decide) s30240 (sig_prime 11 (by norm_num))
  simp only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

theorem sigM : ArithmeticFunction.sigma 1 332637 = 443520 := by
  have h := mulstep 3 110879 (3 + 1) (110879 + 1) (by decide) (sig_prime 3 Nat.prime_three)
    (sig_prime 110879 (by norm_num))
  simp only [Nat.reduceMul, Nat.reduceAdd] at h
  exact h

end L05A231548

open OMA.S_oeis_a231548 L05A231548 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a231548.main) := by
  intro H
  apply H
  refine ⟨332640, by norm_num, ?_⟩
  show antisigma 332640 < antisigma 332637
  have a1 := decomp 332640
  have a2 := decomp 332637
  have b1 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := 332640)
  have b2 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := 332637)
  have c1 := ArithmeticFunction.sigma_one_apply 332640
  have c2 := ArithmeticFunction.sigma_one_apply 332637
  have g1 : (∑ k ∈ Finset.Ico 1 332640, k) * 2 = 110649036960 := gauss 332640 (by norm_num)
  have g2 : (∑ k ∈ Finset.Ico 1 332637, k) * 2 = 110647041132 := gauss 332637 (by norm_num)
  rw [sigN] at c1
  rw [sigM] at c2
  omega

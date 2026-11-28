import OMAStatements.S_oeis_a382318

-- Problem: A382318: G.f. A(x) satisfies A(x) = x + ( Sum_{n>=1} A(x^n) )^3.
-- Upstream: formal-conjectures statements/oeis-a382318.lean:0 (declaration OMA.S_oeis_a382318.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: map the truncated series P = Sum_{i <= n} b(i) X^i to (ZMod 3)[X]. There
-- P^3 = expand 3 P (Frobenius, ZMod.expand_card), so the coefficient of X^n in P^3 is b(n/3)
-- mod 3 when 3 divides n and 0 otherwise (Polynomial.coeff_expand). Hence a(3n) = b(n) mod 3,
-- and a(3n+1), a(3n+2) = 0 mod 3 once 3n+1 is not 1.

open OMA.S_oeis_a382318 in
theorem OMA.solution : type_of% @OMA.S_oeis_a382318.main := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∀ n : ℕ,
      ((((∑ i ∈ Finset.range (n + 1), Polynomial.C (b i) * Polynomial.X ^ i) ^ 3).coeff n : ℕ) :
        ZMod 3) = if 3 ∣ n then ((b (n / 3) : ℕ) : ZMod 3) else 0 := by
    intro n
    set P : Polynomial ℕ := ∑ i ∈ Finset.range (n + 1), Polynomial.C (b i) * Polynomial.X ^ i
      with hP
    have hmap : Polynomial.map (Nat.castRingHom (ZMod 3)) P =
        ∑ i ∈ Finset.range (n + 1), Polynomial.C ((b i : ℕ) : ZMod 3) * Polynomial.X ^ i := by
      rw [hP, Polynomial.map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, eq_natCast]
    have h1 : (((P ^ 3).coeff n : ℕ) : ZMod 3) =
        ((Polynomial.map (Nat.castRingHom (ZMod 3)) P) ^ 3).coeff n := by
      rw [← Polynomial.map_pow, Polynomial.coeff_map, eq_natCast]
    rw [h1, ← ZMod.expand_card (p := 3), Polynomial.coeff_expand (p := 3) (by norm_num), hmap]
    by_cases h3 : 3 ∣ n
    · rw [if_pos h3, if_pos h3, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (show n / 3 < n + 1 by omega))]
    · rw [if_neg h3, if_neg h3]
  have ha : ∀ n : ℕ, (a n : ZMod 3) =
      ((if n = 1 then 1 else 0 : ℕ) : ZMod 3) +
        (if 3 ∣ n then ((b (n / 3) : ℕ) : ZMod 3) else 0) := by
    intro n
    unfold a
    rw [Nat.cast_add, key n]
  refine ⟨fun n => ?_, fun n hn => ⟨?_, ?_⟩⟩
  · have h := ha (3 * n)
    rw [if_neg (show ¬ (3 * n = 1) by omega), if_pos (dvd_mul_right 3 n),
      show 3 * n / 3 = n by omega, Nat.cast_zero, zero_add] at h
    exact (ZMod.natCast_eq_natCast_iff' _ _ 3).mp h
  · have h := ha (3 * n + 1)
    rw [if_neg (show ¬ (3 * n + 1 = 1) by omega), if_neg (show ¬ (3 ∣ 3 * n + 1) by omega),
      Nat.cast_zero, zero_add, ← Nat.cast_zero] at h
    have h' := (ZMod.natCast_eq_natCast_iff' _ _ 3).mp h
    omega
  · have h := ha (3 * n + 2)
    rw [if_neg (show ¬ (3 * n + 2 = 1) by omega), if_neg (show ¬ (3 ∣ 3 * n + 2) by omega),
      Nat.cast_zero, zero_add, ← Nat.cast_zero] at h
    have h' := (ZMod.natCast_eq_natCast_iff' _ _ 3).mp h
    omega

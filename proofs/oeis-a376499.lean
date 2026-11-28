import OMAStatements.S_oeis_a376499

-- Problem: A376499: Array read by ascending antidiagonals: A(n,k) = A376484/(2*n+1).
-- Upstream: formal-conjectures statements/oeis-a376499.lean:0 (declaration OMA.S_oeis_a376499.main)
-- Credit: @oceancheol (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof. Put N = 2n+1 and a_j = 2(j+1) pi / N.
-- 1. (2 sin t)^(2k) = (-1)^k * sum_{i <= 2k} (-1)^i C(2k,i) cos((2k-2i) t)   (two_sin_pow).
-- 2. 2 sin u * sum_{j<n} cos(2(j+1) u) = sin((2n+1) u) - sin u                (sin_mul_sum).
-- 3. 2 * sum_{j<n} cos((2k-2i) a_j) is 2n if N divides k-i, and -1 otherwise  (sum_cos).
-- 4. As sum_i (-1)^i C(2k,i) = 0 for k >= 1, this gives 2 * entry n k = (-1)^k * N * A, where A
--    is the sum of (-1)^i C(2k,i) over the i <= 2k with N dividing k-i (two_entry). The
--    involution i -> 2k-i preserves the terms modulo 2 and its only fixed point i = k carries
--    the even number C(2k,k), so A is even (even_A) and entry n k / N is an integer.

namespace OMA.A376499

open Finset

lemma two_sin_pow (t : ℝ) (k : ℕ) :
    (2 * Real.sin t) ^ (2 * k)
      = (-1 : ℝ) ^ k * ∑ i ∈ range (2 * k + 1),
          ((-1 : ℝ) ^ i * ((2 * k).choose i : ℝ)) * Real.cos ((2 * (k : ℝ) - 2 * i) * t) := by
  have h : ((2 * Real.sin t : ℝ) : ℂ) ^ (2 * k)
      = (((-1 : ℝ) ^ k : ℝ) : ℂ) * ∑ i ∈ range (2 * k + 1),
          (((-1 : ℝ) ^ i * ((2 * k).choose i : ℝ) : ℝ) : ℂ) *
            Complex.exp ((((2 * (k : ℝ) - 2 * i) * t : ℝ) : ℂ) * Complex.I) := by
    have h2 : ((2 * Real.sin t : ℝ) : ℂ)
        = (Complex.exp (-(t : ℂ) * Complex.I) - Complex.exp ((t : ℂ) * Complex.I)) * Complex.I := by
      rw [← Complex.two_sin]
      simp
    have h3 : ((Complex.exp (-(t : ℂ) * Complex.I) - Complex.exp ((t : ℂ) * Complex.I))
          * Complex.I) ^ (2 * k)
        = (-1 : ℂ) ^ k *
          (-Complex.exp (-(t : ℂ) * Complex.I) + Complex.exp ((t : ℂ) * Complex.I)) ^ (2 * k) := by
      rw [mul_pow, pow_mul Complex.I, Complex.I_sq, mul_comm]
      congr 1
      have e0 : -Complex.exp (-(t : ℂ) * Complex.I) + Complex.exp ((t : ℂ) * Complex.I)
          = -(Complex.exp (-(t : ℂ) * Complex.I) - Complex.exp ((t : ℂ) * Complex.I)) := by ring
      rw [e0, Even.neg_pow (even_two_mul k)]
    rw [h2, h3, add_pow]
    have hc : (((-1 : ℝ) ^ k : ℝ) : ℂ) = (-1 : ℂ) ^ k := by simp
    rw [hc]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hik : i ≤ 2 * k := by
      have := mem_range.mp hi
      omega
    have e : Complex.exp (-(t : ℂ) * Complex.I) ^ i
          * Complex.exp ((t : ℂ) * Complex.I) ^ (2 * k - i)
        = Complex.exp ((((2 * (k : ℝ) - 2 * i) * t : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast [Nat.cast_sub hik]
      ring
    rw [neg_pow, mul_assoc ((-1 : ℂ) ^ i), e]
    push_cast
    ring
  have h4 := congrArg Complex.re h
  rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.re_sum] at h4
  rw [h4]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

lemma sin_mul_sum (u : ℝ) (n : ℕ) :
    2 * Real.sin u * ∑ j ∈ range n, Real.cos (2 * ((j : ℝ) + 1) * u)
      = Real.sin ((2 * (n : ℝ) + 1) * u) - Real.sin u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    have h1 := Real.sin_add (2 * ((n : ℝ) + 1) * u) u
    have h2 := Real.sin_sub (2 * ((n : ℝ) + 1) * u) u
    have e1 : 2 * ((n : ℝ) + 1) * u + u = (2 * ((n + 1 : ℕ) : ℝ) + 1) * u := by
      push_cast
      ring
    have e2 : 2 * ((n : ℝ) + 1) * u - u = (2 * (n : ℝ) + 1) * u := by ring
    rw [e1] at h1
    rw [e2] at h2
    rw [h1, h2]
    ring

lemma sum_cos (n k i : ℕ) :
    2 * ∑ j ∈ range n,
        Real.cos ((2 * (k : ℝ) - 2 * i) * (2 * ((j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1)))
      = if ((2 * n + 1 : ℕ) : ℤ) ∣ ((k : ℤ) - i) then 2 * (n : ℝ) else -1 := by
  have hN : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = (k : ℤ) - i := ⟨_, rfl⟩
  have hcr : (2 * (k : ℝ) - 2 * i) = 2 * (c : ℝ) := by
    rw [hc]
    push_cast
    ring
  rw [hcr, ← hc]
  by_cases hdvd : ((2 * n + 1 : ℕ) : ℤ) ∣ c
  · rw [if_pos hdvd]
    obtain ⟨t, ht⟩ := hdvd
    have htr : (c : ℝ) = (2 * (n : ℝ) + 1) * t := by
      rw [ht]
      push_cast
      ring
    have each : ∀ j ∈ range n,
        Real.cos (2 * (c : ℝ) * (2 * ((j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1))) = 1 := by
      intro j _
      have e : 2 * (c : ℝ) * (2 * ((j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1))
          = (((2 * t * ((j : ℤ) + 1) : ℤ)) : ℝ) * (2 * Real.pi) := by
        rw [htr]
        push_cast
        field_simp
      rw [e, Real.cos_int_mul_two_pi]
    rw [sum_congr rfl each, sum_const, card_range, nsmul_eq_mul]
    ring
  · rw [if_neg hdvd]
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 2 * (c : ℝ) * Real.pi / (2 * (n : ℝ) + 1) := ⟨_, rfl⟩
    have e : ∀ j ∈ range n,
        Real.cos (2 * (c : ℝ) * (2 * ((j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1)))
          = Real.cos (2 * ((j : ℝ) + 1) * u) := by
      intro j _
      congr 1
      rw [hu]
      ring
    rw [sum_congr rfl e]
    have hA := sin_mul_sum u n
    have e2 : (2 * (n : ℝ) + 1) * u = ((2 * c : ℤ) : ℝ) * Real.pi := by
      rw [hu]
      push_cast
      field_simp
    rw [e2, Real.sin_int_mul_pi, zero_sub] at hA
    have hsin : Real.sin u ≠ 0 := by
      intro h0
      obtain ⟨t, ht⟩ := Real.sin_eq_zero_iff.mp h0
      have h5 : (t : ℝ) * (2 * (n : ℝ) + 1) * Real.pi = 2 * (c : ℝ) * Real.pi := by
        have h4 : (t : ℝ) * Real.pi * (2 * (n : ℝ) + 1) = 2 * (c : ℝ) * Real.pi := by
          rw [ht, hu]
          field_simp
        rw [← h4]
        ring
      have h6 : (t : ℝ) * (2 * (n : ℝ) + 1) = 2 * (c : ℝ) := mul_right_cancel₀ Real.pi_ne_zero h5
      have h7 : 2 * c = t * (2 * (n : ℤ) + 1) := by
        have h8 : ((2 * c : ℤ) : ℝ) = ((t * (2 * (n : ℤ) + 1) : ℤ) : ℝ) := by
          push_cast
          rw [h6]
        exact_mod_cast h8
      apply hdvd
      refine ⟨c - n * t, ?_⟩
      push_cast
      linear_combination (-(n : ℤ)) * h7
    have h8 : (2 * ∑ j ∈ range n, Real.cos (2 * ((j : ℝ) + 1) * u)) * Real.sin u
        = (-1 : ℝ) * Real.sin u := by
      linear_combination hA
    exact mul_right_cancel₀ hsin h8

lemma two_entry (n k : ℕ) (hk : 1 ≤ k) :
    2 * OMA.S_oeis_a376499.entry n k
      = (-1 : ℝ) ^ k * ((2 * (n : ℝ) + 1) *
          ((∑ i ∈ range (2 * k + 1),
            if ((2 * n + 1 : ℕ) : ℤ) ∣ ((k : ℤ) - i) then (-1 : ℤ) ^ i * ((2 * k).choose i : ℤ)
              else 0 : ℤ) : ℝ)) := by
  unfold OMA.S_oeis_a376499.entry OMA.S_oeis_a376499.angle
  have h1 : ∀ j ∈ range n,
      (4 : ℝ) ^ k * Real.sin (2 * ((j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1)) ^ (2 * k)
        = (-1 : ℝ) ^ k * ∑ i ∈ range (2 * k + 1),
            ((-1 : ℝ) ^ i * ((2 * k).choose i : ℝ)) *
              Real.cos ((2 * (k : ℝ) - 2 * i)
                * (2 * ((j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1))) := by
    intro j _
    rw [← two_sin_pow, mul_pow]
    congr 1
    rw [pow_mul]
    norm_num
  have h2 : (4 : ℝ) ^ k *
      ∑ j ∈ range n, Real.sin (2 * ((j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1)) ^ (2 * k)
        = (-1 : ℝ) ^ k * ∑ i ∈ range (2 * k + 1),
            ((-1 : ℝ) ^ i * ((2 * k).choose i : ℝ)) * ∑ j ∈ range n,
              Real.cos ((2 * (k : ℝ) - 2 * i)
                * (2 * ((j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1))) := by
    rw [mul_sum, sum_congr rfl h1, ← mul_sum, sum_comm]
    congr 1
    apply sum_congr rfl
    intro i _
    rw [mul_sum]
  rw [h2, mul_left_comm, mul_sum]
  congr 1
  have h3 : ∀ i ∈ range (2 * k + 1),
      2 * (((-1 : ℝ) ^ i * ((2 * k).choose i : ℝ)) * ∑ j ∈ range n,
          Real.cos ((2 * (k : ℝ) - 2 * i) * (2 * ((j : ℝ) + 1) * Real.pi / (2 * (n : ℝ) + 1))))
        = (2 * (n : ℝ) + 1) *
            ((if ((2 * n + 1 : ℕ) : ℤ) ∣ ((k : ℤ) - i)
              then (-1 : ℤ) ^ i * ((2 * k).choose i : ℤ) else 0 : ℤ) : ℝ)
          - (-1 : ℝ) ^ i * ((2 * k).choose i : ℝ) := by
    intro i _
    rw [mul_left_comm, sum_cos n k i]
    by_cases hd : ((2 * n + 1 : ℕ) : ℤ) ∣ ((k : ℤ) - i)
    · rw [if_pos hd, if_pos hd]
      push_cast
      ring
    · rw [if_neg hd, if_neg hd]
      push_cast
      ring
  rw [sum_congr rfl h3, sum_sub_distrib, ← mul_sum]
  have h4 : ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * ((2 * k).choose i : ℝ) = 0 := by
    have h5 := Int.alternating_sum_range_choose (n := 2 * k)
    rw [if_neg (by omega)] at h5
    have h6 := congrArg (fun z : ℤ => (z : ℝ)) h5
    push_cast at h6
    exact h6
  rw [h4, sub_zero]
  push_cast
  ring

lemma even_A (n k : ℕ) (hk : 1 ≤ k) :
    Even (∑ i ∈ range (2 * k + 1),
      if ((2 * n + 1 : ℕ) : ℤ) ∣ ((k : ℤ) - i) then (-1 : ℤ) ^ i * ((2 * k).choose i : ℤ)
        else 0) := by
  rw [← sum_filter]
  rw [← ZMod.intCast_eq_zero_iff_even, Int.cast_sum]
  have hone : (-1 : ZMod 2) = 1 := by decide
  have hf : ∀ a : ℕ, (((-1 : ℤ) ^ a * ((2 * k).choose a : ℤ) : ℤ) : ZMod 2)
      = ((2 * k).choose a : ZMod 2) := by
    intro a
    push_cast
    rw [hone, one_pow, one_mul]
  refine Finset.sum_involution (fun a _ => 2 * k - a) ?_ ?_ ?_ ?_
  · intro a ha
    have hak : a ≤ 2 * k := by
      have := mem_range.mp (mem_filter.mp ha).1
      omega
    rw [hf, hf, Nat.choose_symm hak]
    exact CharTwo.add_self_eq_zero _
  · intro a ha hfa heq
    have hak : a ≤ 2 * k := by
      have := mem_range.mp (mem_filter.mp ha).1
      omega
    have hakk : a = k := by
      have h9 : 2 * k - a = a := heq
      omega
    apply hfa
    rw [hf, hakk, ← Nat.centralBinom_eq_two_mul_choose]
    exact (ZMod.natCast_eq_zero_iff_even).mpr
      (even_iff_two_dvd.mpr (Nat.two_dvd_centralBinom_of_one_le hk))
  · intro a ha
    have hak : a ≤ 2 * k := by
      have := mem_range.mp (mem_filter.mp ha).1
      omega
    rw [mem_filter, mem_range]
    refine ⟨by omega, ?_⟩
    have h0 : (k : ℤ) - ((2 * k - a : ℕ) : ℤ) = -((k : ℤ) - a) := by
      push_cast [Nat.cast_sub hak]
      ring
    rw [h0]
    exact (dvd_neg).mpr (mem_filter.mp ha).2
  · intro a ha
    have hak : a ≤ 2 * k := by
      have := mem_range.mp (mem_filter.mp ha).1
      omega
    show 2 * k - (2 * k - a) = a
    omega

end OMA.A376499

theorem OMA.solution : type_of% @OMA.S_oeis_a376499.main := by
  intro n k _ hk
  obtain ⟨r, hr⟩ := OMA.A376499.even_A n k hk
  have h := OMA.A376499.two_entry n k hk
  rw [hr] at h
  have hN : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  refine ⟨(-1) ^ k * r, ?_⟩
  rw [div_eq_iff hN]
  push_cast at h ⊢
  linear_combination h / 2

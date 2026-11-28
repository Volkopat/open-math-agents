import OMAStatements.S_oeis_a193655

-- Problem: A193655: Q-residue of the triangle p(n,k)=floor(1/2+(n+1)/(n+k+2)/2), 0<=k<=n, where Q is the triangular array (t(i,j)) given by t(i,j)=1.  (See Comments.)
-- Upstream: formal-conjectures statements/oeis-a193655.lean:0 (declaration OMA.S_oeis_a193655.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: 2 p(n,k) = (n+1)(n+k+2) + e(n,k) with e(n,k) = (n+1)(n+k+2) mod 2. The sums
-- Sum_k r(n-k) = 2^n, Sum_k k r(n-k) = 2^n - 1 and Sum_k (k mod 2) r(n-k) = (2^n - (-1)^n)/3 follow
-- by induction (peel off k = 0), and e(n,k) = k mod 2 for even n, 0 for odd n. This gives
-- a(n) = (n+1)((n+3)2^n - 1)/2 + (1 + (-1)^n)(2^n - 1)/12, hence the recurrence of order 7 with
-- characteristic polynomial (1+x)(2x+1)(x-1)^2(2x-1)^3; the g.f. follows by comparing coefficients.

open OMA.S_oeis_a193655 in
theorem OMA.solution : type_of% @OMA.S_oeis_a193655.main := by
  have hrs : ∀ m : ℕ, ((r (m + 1) : ℕ) : ℚ) = 2 ^ m := by
    intro m
    simp [r]
  have Ta : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), ((r (n - k) : ℕ) : ℚ) = 2 ^ n := by
    intro n
    induction n with
    | zero => simp [r]
    | succ n ih =>
      rw [Finset.sum_range_succ']
      have e : ∀ k ∈ Finset.range (n + 1),
          ((r (n + 1 - (k + 1)) : ℕ) : ℚ) = ((r (n - k) : ℕ) : ℚ) := by
        intro k _
        rw [Nat.add_sub_add_right]
      rw [Finset.sum_congr rfl e, ih, Nat.sub_zero, hrs n]
      ring
  have Tb : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), (k : ℚ) * ((r (n - k) : ℕ) : ℚ) =
      2 ^ n - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ']
      have e : ∀ k ∈ Finset.range (n + 1),
          ((k + 1 : ℕ) : ℚ) * ((r (n + 1 - (k + 1)) : ℕ) : ℚ) =
            (k : ℚ) * ((r (n - k) : ℕ) : ℚ) + ((r (n - k) : ℕ) : ℚ) := by
        intro k _
        rw [Nat.add_sub_add_right]
        push_cast
        ring
      rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ih, Ta n, Nat.cast_zero, zero_mul]
      ring
  have mod1 : ∀ k : ℕ, (((k + 1) % 2 : ℕ) : ℚ) = 1 - ((k % 2 : ℕ) : ℚ) := by
    intro k
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · rw [h, show (k + 1) % 2 = 1 by omega]
      norm_num
    · rw [h, show (k + 1) % 2 = 0 by omega]
      norm_num
  have Tc : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), ((k % 2 : ℕ) : ℚ) * ((r (n - k) : ℕ) : ℚ) =
      (2 ^ n - (-1) ^ n) / 3 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ']
      have e : ∀ k ∈ Finset.range (n + 1),
          (((k + 1) % 2 : ℕ) : ℚ) * ((r (n + 1 - (k + 1)) : ℕ) : ℚ) =
            ((r (n - k) : ℕ) : ℚ) - ((k % 2 : ℕ) : ℚ) * ((r (n - k) : ℕ) : ℚ) := by
        intro k _
        rw [Nat.add_sub_add_right, mod1 k]
        ring
      rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ih, Ta n, Nat.zero_mod, Nat.cast_zero,
        zero_mul]
      ring
  have E : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1),
      ((((n + 1) * (n + k + 2)) % 2 : ℕ) : ℚ) * ((r (n - k) : ℕ) : ℚ) =
        (1 + (-1) ^ n) * (2 ^ n - 1) / 6 := by
    intro n
    obtain ⟨t, rfl | rfl⟩ : ∃ t, n = 2 * t ∨ n = 2 * t + 1 := ⟨n / 2, by omega⟩
    · have e : ∀ k ∈ Finset.range (2 * t + 1),
          ((((2 * t + 1) * (2 * t + k + 2)) % 2 : ℕ) : ℚ) * ((r (2 * t - k) : ℕ) : ℚ) =
            ((k % 2 : ℕ) : ℚ) * ((r (2 * t - k) : ℕ) : ℚ) := by
        intro k _
        rw [Nat.mul_mod, show (2 * t + 1) % 2 = 1 by omega,
          show (2 * t + k + 2) % 2 = k % 2 by omega, one_mul, Nat.mod_mod]
      rw [Finset.sum_congr rfl e, Tc (2 * t)]
      have h1 : ((-1 : ℚ)) ^ (2 * t) = 1 := by
        rw [pow_mul]
        norm_num
      rw [h1]
      ring
    · have e : ∀ k ∈ Finset.range (2 * t + 1 + 1),
          ((((2 * t + 1 + 1) * (2 * t + 1 + k + 2)) % 2 : ℕ) : ℚ) *
            ((r (2 * t + 1 - k) : ℕ) : ℚ) = 0 := by
        intro k _
        rw [Nat.mul_mod, show (2 * t + 1 + 1) % 2 = 0 by omega, zero_mul, Nat.zero_mod,
          Nat.cast_zero, zero_mul]
      rw [Finset.sum_congr rfl e, Finset.sum_const_zero]
      have h1 : ((-1 : ℚ)) ^ (2 * t + 1) = -1 := by
        rw [pow_succ, pow_mul]
        norm_num
      rw [h1]
      ring
  have pt : ∀ n k : ℕ, 2 * ((p n k : ℕ) : ℚ) =
      ((n : ℚ) + 1) * ((n : ℚ) + k + 2) + ((((n + 1) * (n + k + 2)) % 2 : ℕ) : ℚ) := by
    intro n k
    have hx : ∀ x : ℕ, 2 * ((x + 1) / 2) = x + x % 2 := by
      intro x
      omega
    have h : 2 * p n k = (n + 1) * (n + k + 2) + ((n + 1) * (n + k + 2)) % 2 :=
      hx ((n + 1) * (n + k + 2))
    exact_mod_cast h
  have vq : ∀ n : ℕ, (a n : ℚ) = ((n : ℚ) + 1) * (((n : ℚ) + 3) * 2 ^ n - 1) / 2 +
      (1 + (-1) ^ n) * (2 ^ n - 1) / 12 := by
    intro n
    have h2 : 2 * (a n : ℚ) = ∑ k ∈ Finset.range (n + 1),
        (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((r (n - k) : ℕ) : ℚ) +
          ((n : ℚ) + 1) * ((k : ℚ) * ((r (n - k) : ℕ) : ℚ)) +
          ((((n + 1) * (n + k + 2)) % 2 : ℕ) : ℚ) * ((r (n - k) : ℕ) : ℚ)) := by
      simp only [a, Nat.cast_sum, Nat.cast_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      linear_combination ((r (n - k) : ℕ) : ℚ) * pt n k
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Ta n, Tb n, E n] at h2
    linear_combination h2 / 2
  have hrec : ∀ k : ℕ, -(a (k + 7) : ℚ) + 5 * (a (k + 6) : ℚ) - 3 * (a (k + 5) : ℚ) -
      21 * (a (k + 4) : ℚ) + 36 * (a (k + 3) : ℚ) - 32 * (a (k + 1) : ℚ) + 16 * (a k : ℚ) = 0 := by
    intro k
    rw [vq (k + 7), vq (k + 6), vq (k + 5), vq (k + 4), vq (k + 3), vq (k + 1), vq k]
    push_cast
    ring
  have e1 : PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 + PowerSeries.X) * (2 * PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 2 *
        (2 * PowerSeries.X - 1) ^ 3) =
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 36 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 16 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 7)
        - PowerSeries.mk (fun n => (a n : ℚ))
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 21 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 32 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 6) := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 36,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 16,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 21,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 32]
    ring
  have e2 : (-1 - 2 * PowerSeries.X + 3 * PowerSeries.X ^ 2 + 9 * PowerSeries.X ^ 3 -
      8 * PowerSeries.X ^ 4 - 4 * PowerSeries.X ^ 5 : PowerSeries ℚ) =
      PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3
        + PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9
        - 1
        - PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
        - PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8
        - PowerSeries.X ^ 5 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
    ring
  rw [e1, e2]
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow,
    PowerSeries.coeff_one]
  rcases Nat.lt_or_ge m 7 with hm | hm
  · interval_cases m <;> norm_num [vq]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 7 := ⟨m - 7, by omega⟩
    rw [if_pos (show 1 ≤ k + 7 by omega), if_pos (show 4 ≤ k + 7 by omega),
      if_pos (show 7 ≤ k + 7 by omega), if_pos (show 2 ≤ k + 7 by omega),
      if_pos (show 3 ≤ k + 7 by omega), if_pos (show 6 ≤ k + 7 by omega),
      if_neg (show ¬(k + 7 = 2) by omega), if_neg (show ¬(k + 7 = 3) by omega),
      if_neg (show ¬(k + 7 = 0) by omega), if_neg (show ¬(k + 7 = 1) by omega),
      if_neg (show ¬(k + 7 = 4) by omega), if_neg (show ¬(k + 7 = 5) by omega),
      show k + 7 - 1 = k + 6 by omega, show k + 7 - 4 = k + 3 by omega,
      show k + 7 - 7 = k by omega, show k + 7 - 2 = k + 5 by omega,
      show k + 7 - 3 = k + 4 by omega, show k + 7 - 6 = k + 1 by omega]
    linear_combination hrec k

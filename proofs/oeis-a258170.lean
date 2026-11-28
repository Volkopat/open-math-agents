import OMAStatements.S_oeis_a258170

-- Problem: A258170: T(n,k) = (1/k!) * Sum_{i=0..k} (-1)^(k-i) * C(k,i) * A185651(n,i); triangle T(n,k), n >= 0, 0 <= k <= n, read by rows.
-- Upstream: formal-conjectures statements/oeis-a258170.lean:0 (declaration OMA.S_oeis_a258170.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: F(m,k) = Sum_i (-1)^(k-i) C(k,i) i^m satisfies F(m+1,k+1) = (k+1)(F(m,k+1) + F(m,k)),
-- hence F(m,k) = k! S2(m,k), which is 0 for m < k. Swapping sums, k! T(n,k) = Sum_{d|n} phi(d) F(n/d,k),
-- and every divisor d > 1 has n/d < k (n <= 2k-1, or n prime and k >= 2).

open OMA.S_oeis_a258170 in
theorem OMA.solution : type_of% @OMA.S_oeis_a258170.main := by
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ → ℚ, ∀ m k : ℕ,
      F m k = ∑ i ∈ Finset.range (k + 1), (-1 : ℚ) ^ (k - i) * (k.choose i : ℚ) * (i : ℚ) ^ m :=
    ⟨_, fun _ _ => rfl⟩
  have hterm0 : ∀ m i j : ℕ,
      (-1 : ℚ) ^ (j + 1) * ((i + j + 1).choose i : ℚ) * (i : ℚ) ^ (m + 1)
        = ((i : ℚ) + j + 1) * ((-1 : ℚ) ^ (j + 1) * ((i + j + 1).choose i : ℚ) * (i : ℚ) ^ m
          + (-1 : ℚ) ^ j * ((i + j).choose i : ℚ) * (i : ℚ) ^ m) := by
    intro m i j
    have h := Nat.choose_mul_succ_eq (i + j) i
    rw [show i + j + 1 - i = j + 1 by omega] at h
    have hc : ((i + j).choose i : ℚ) * ((i : ℚ) + j + 1)
        = ((i + j + 1).choose i : ℚ) * ((j : ℚ) + 1) := by
      exact_mod_cast h
    linear_combination (-(-1 : ℚ) ^ j * (i : ℚ) ^ m) * hc
  have hrec : ∀ m k : ℕ, F (m + 1) (k + 1) = ((k : ℚ) + 1) * (F m (k + 1) + F m k) := by
    intro m k
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (-1 : ℚ) ^ (k + 1 - i) * ((k + 1).choose i : ℚ) * (i : ℚ) ^ (m + 1)
          = ((k : ℚ) + 1) * ((-1 : ℚ) ^ (k + 1 - i) * ((k + 1).choose i : ℚ) * (i : ℚ) ^ m
            + (-1 : ℚ) ^ (k - i) * (k.choose i : ℚ) * (i : ℚ) ^ m) := by
      intro i hi
      have hik : i ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      have e := hterm0 m i (k - i)
      rw [show i + (k - i) = k by omega, Nat.cast_sub hik] at e
      rw [show k + 1 - i = k - i + 1 by omega]
      linear_combination e
    have hsum : ∑ i ∈ Finset.range (k + 1),
          (-1 : ℚ) ^ (k + 1 - i) * ((k + 1).choose i : ℚ) * (i : ℚ) ^ (m + 1)
        = ((k : ℚ) + 1) * (∑ i ∈ Finset.range (k + 1),
            (-1 : ℚ) ^ (k + 1 - i) * ((k + 1).choose i : ℚ) * (i : ℚ) ^ m
          + ∑ i ∈ Finset.range (k + 1), (-1 : ℚ) ^ (k - i) * (k.choose i : ℚ) * (i : ℚ) ^ m) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl hterm
    have htop : (-1 : ℚ) ^ (k + 1 - (k + 1)) * ((k + 1).choose (k + 1) : ℚ)
          * ((k + 1 : ℕ) : ℚ) ^ (m + 1)
        = ((k : ℚ) + 1) * ((-1 : ℚ) ^ (k + 1 - (k + 1)) * ((k + 1).choose (k + 1) : ℚ)
          * ((k + 1 : ℕ) : ℚ) ^ m) := by
      push_cast
      ring
    rw [hF, hF, hF, Finset.sum_range_succ _ (k + 1), Finset.sum_range_succ _ (k + 1)]
    linear_combination hsum + htop
  have hS : ∀ m k : ℕ, F m k = (k.factorial : ℚ) * (Nat.stirlingSecond m k : ℚ) := by
    intro m
    induction m with
    | zero =>
      intro k
      cases k with
      | zero =>
        rw [hF]
        simp
      | succ k =>
        have h := add_pow (1 : ℚ) (-1) (k + 1)
        rw [show (1 : ℚ) + -1 = 0 by norm_num, zero_pow (by omega : k + 1 ≠ 0)] at h
        have hz : Nat.stirlingSecond 0 (k + 1) = 0 := rfl
        rw [hF, hz, Nat.cast_zero, mul_zero, h]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    | succ m ih =>
      intro k
      cases k with
      | zero =>
        have hz : Nat.stirlingSecond (m + 1) 0 = 0 := rfl
        rw [hF, hz]
        simp
      | succ k =>
        rw [hrec, ih, ih, Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
        push_cast
        ring
  have hgen : ∀ n k : ℕ, n ≠ 0 → (∀ d ∈ n.divisors, d ≠ 1 → n / d < k) →
      T n k = (Nat.stirlingSecond n k : ℚ) := by
    intro n k hn hd
    have hswap : ∑ i ∈ Finset.range (k + 1), (-1 : ℚ) ^ (k - i) * (k.choose i : ℚ) * (A185651 n i : ℚ)
        = ∑ d ∈ n.divisors, (Nat.totient d : ℚ) * F (n / d) k := by
      simp only [A185651, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Finset.mul_sum, hF]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))
    have hval : ∑ d ∈ n.divisors, (Nat.totient d : ℚ) * F (n / d) k
        = (k.factorial : ℚ) * (Nat.stirlingSecond n k : ℚ) := by
      rw [Finset.sum_eq_single 1]
      · rw [Nat.totient_one, Nat.div_one, hS, Nat.cast_one, one_mul]
      · intro d hdm hd1
        rw [hS, Nat.stirlingSecond_eq_zero_of_lt (hd d hdm hd1), Nat.cast_zero, mul_zero, mul_zero]
      · intro h1
        exact absurd (Nat.one_mem_divisors.mpr hn) h1
    have hf : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    unfold T
    rw [hswap, hval, ← mul_assoc, one_div_mul_cancel hf, one_mul]
  constructor
  · intro n k hk hkn hn2
    apply hgen n k (by omega)
    intro d hd hd1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hd2 : 2 ≤ d := by omega
    have hkd : k * 2 ≤ k * d := Nat.mul_le_mul (le_refl k) hd2
    rw [Nat.div_lt_iff_lt_mul hdpos]
    omega
  · intro n k hk _ hp
    apply hgen n k hp.ne_zero
    intro d hd hd1
    rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mem_divisors hd) with h | h
    · exact absurd h hd1
    · rw [h, Nat.div_self hp.pos]
      omega

import FormalConjectures.ErdosProblems.«257»

-- Reduction Erdos257.erdos_257.R1 of Erdős Problem 257
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Split on whether the sum of 1/a over A converges.
--
-- Convergent case (Erdős, On the irrationality of certain series, Math. Student 36 (1968)).
-- main proves its arithmetic core. Write S = p/q and, for n in A and N >= 1,
--   (2^N - 1)/(2^n - 1) = I(n, N) + (2^(N mod n) - 1)/(2^n - 1),
-- where I(n, N) = (2^N - 2^(N mod n))/(2^n - 1) is a natural number (2^n - 1 divides 2^(n k) - 1)
-- and vanishes for n > N. Summing over A, q times the remainder sum
--   D(N) = sum over n in A of (2^(N mod n) - 1)/(2^n - 1)
-- equals (2^N - 1) p - q (a finite sum of naturals), an integer. When K! divides N, every n in A
-- with n <= K divides N and contributes 0. Since A is infinite, some n in A exceeds N and its term
-- (2^N - 1)/(2^n - 1) is positive, so q D(N) >= 1. H2 supplies such an N with D(N) < 1/q.
--
-- H1 (OPEN): the divergent case. It contains A = all naturals (Erdős 1948, sum of d(n)/2^n)
--   and is open in general, for example for the primes.
-- H2 (TRUE, the averaging half of Erdős 1968): for fixed M and n, the average of
--   (2^(M t mod n) - 1)/(2^n - 1) over t in [1, T] is at most 1/n + 1/T (the residues M t mod n
--   run through the multiples of gcd(M, n), each about T gcd(M, n)/n times). Choose K with the tail
--   of the sum of 1/a beyond K below eps/4, then a second cutoff for the boundary terms and T
--   large: some t in [1, T] gives N = M t with the tail sum below eps.

namespace OMA.R_Erdos257_erdos_257_R1

/-- The divergent case: if the sum of `1/a` over the infinite set `A` diverges, then the sum
of `1/(2^n - 1)` over `A` is irrational. -/
def H1 : Prop :=
  ∀ A : Set ℕ, A.Infinite → ¬ Summable (fun a : A => 1 / (a : ℝ)) →
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1))

/-- Small remainders along multiples (the averaging lemma of Erdős 1968): if the sum of `1/a`
over `A` converges, then for every `ε > 0` there is a cutoff `K` such that every `M ≥ 1` has a
positive multiple `N` for which the remainders `(2^(N mod n) - 1)/(2^n - 1)` over the elements
`n > K` of `A` sum to less than `ε`. -/
def H2 : Prop :=
  ∀ A : Set ℕ, Summable (fun a : A => 1 / (a : ℝ)) → ∀ ε : ℝ, 0 < ε →
    ∃ K : ℕ, ∀ M : ℕ, 0 < M → ∃ N : ℕ, 0 < N ∧ M ∣ N ∧
      ∑' n : A, (if K < n.1 then ((2 : ℝ) ^ (N % n.1) - 1) / ((2 : ℝ) ^ n.1 - 1) else 0) < ε

lemma two_le_two_pow {n : ℕ} (hn : 0 < n) : (2 : ℝ) ≤ 2 ^ n := by
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn

lemma rem_nonneg (n N : ℕ) : 0 ≤ ((2 : ℝ) ^ (N % n) - 1) / ((2 : ℝ) ^ n - 1) := by
  apply div_nonneg
  · have : (1 : ℝ) ≤ 2 ^ (N % n) := one_le_pow₀ (by norm_num)
    linarith
  · have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    linarith

/-- `2^n - 1` divides `2^N - 2^(N mod n)`. -/
lemma dvd_aux (n N : ℕ) : 2 ^ n - 1 ∣ 2 ^ N - 2 ^ (N % n) := by
  have h : 2 ^ N = 2 ^ (N % n) * (2 ^ n) ^ (N / n) := by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [h, show 2 ^ (N % n) * (2 ^ n) ^ (N / n) - 2 ^ (N % n)
      = 2 ^ (N % n) * ((2 ^ n) ^ (N / n) - 1) by rw [Nat.mul_sub, mul_one]]
  apply Dvd.dvd.mul_left
  simpa using Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 (N / n)

/-- The integer part vanishes once `n > N`. -/
lemma ipart_eq_zero {n N : ℕ} (h : N < n) : (2 ^ N - 2 ^ (N % n)) / (2 ^ n - 1) = 0 := by
  rw [Nat.mod_eq_of_lt h, Nat.sub_self, Nat.zero_div]

/-- `(2^N - 1)/(2^n - 1)` is a natural number plus the remainder `(2^(N mod n) - 1)/(2^n - 1)`.
For `n = 0` both sides are `0` (division by zero). -/
lemma split (n N : ℕ) :
    ((2 : ℝ) ^ N - 1) * (1 / ((2 : ℝ) ^ n - 1)) =
      (((2 ^ N - 2 ^ (N % n)) / (2 ^ n - 1) : ℕ) : ℝ) +
        ((2 : ℝ) ^ (N % n) - 1) / ((2 : ℝ) ^ n - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h2n := two_le_two_pow hn
    have hden : (2 : ℝ) ^ n - 1 ≠ 0 := by linarith
    have hle1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hle2 : 2 ^ (N % n) ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) (Nat.mod_le N n)
    have hcast : (((2 ^ N - 2 ^ (N % n)) / (2 ^ n - 1) : ℕ) : ℝ) =
        ((2 : ℝ) ^ N - 2 ^ (N % n)) / ((2 : ℝ) ^ n - 1) := by
      rw [Nat.cast_div (dvd_aux n N)]
      · rw [Nat.cast_sub hle2, Nat.cast_sub hle1]
        push_cast
        ring
      · rw [Nat.cast_sub hle1]
        push_cast
        exact hden
    rw [hcast]
    field_simp
    ring

lemma summable_f : Summable (fun n : ℕ => (1 : ℝ) / (2 ^ n - 1)) := by
  apply Summable.of_nonneg_of_le (f := fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n)
  · intro n
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    apply div_nonneg zero_le_one
    linarith
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have h2n := two_le_two_pow hn
      have hp : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
        rw [← mul_pow]
        norm_num
      have hx : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg hx (by linarith : (0 : ℝ) ≤ 2 ^ n - 2)]
  · exact summable_geometric_two.mul_left 2

lemma summable_rem (A : Set ℕ) (N : ℕ) :
    Summable (fun n : A => ((2 : ℝ) ^ (N % n.1) - 1) / ((2 : ℝ) ^ n.1 - 1)) := by
  have hfA : Summable (fun n : A => (1 : ℝ) / (2 ^ n.1 - 1)) := summable_f.subtype A
  apply Summable.of_nonneg_of_le (fun n => rem_nonneg _ _) _ (hfA.mul_left ((2 : ℝ) ^ N - 1))
  intro n
  have := split n.1 N
  have h0 : (0 : ℝ) ≤ (((2 ^ N - 2 ^ (N % n.1)) / (2 ^ n.1 - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-- If the sum equals the rational `r`, then `r.den` times the remainder sum is an integer. -/
lemma den_mul_rem_int (A : Set ℕ) (r : ℚ)
    (hr : (r : ℝ) = ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) (N : ℕ) :
    ∃ z : ℤ, (r.den : ℝ) * ∑' n : A, ((2 : ℝ) ^ (N % n.1) - 1) / ((2 : ℝ) ^ n.1 - 1) = z := by
  classical
  have hfA : Summable (fun n : A => (1 : ℝ) / (2 ^ n.1 - 1)) := summable_f.subtype A
  have hremA := summable_rem A N
  have hIA : Summable (fun n : A => (((2 ^ N - 2 ^ (N % n.1)) / (2 ^ n.1 - 1) : ℕ) : ℝ)) := by
    refine ((hfA.mul_left ((2 : ℝ) ^ N - 1)).sub hremA).congr (fun n => ?_)
    have := split n.1 N
    linarith
  have hIfin : ∃ m : ℕ, ∑' n : A, (((2 ^ N - 2 ^ (N % n.1)) / (2 ^ n.1 - 1) : ℕ) : ℝ) = m := by
    refine ⟨∑ n ∈ Finset.range (N + 1),
      (if n ∈ A then (2 ^ N - 2 ^ (N % n)) / (2 ^ n - 1) else 0), ?_⟩
    rw [tsum_subtype A (fun n => (((2 ^ N - 2 ^ (N % n)) / (2 ^ n - 1) : ℕ) : ℝ))]
    rw [tsum_eq_sum (s := Finset.range (N + 1))]
    · push_cast
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : n ∈ A <;> simp [hn]
    · intro n hn
      have hlt : N < n := by simp at hn; omega
      simp [Set.indicator_apply, ipart_eq_zero hlt]
  obtain ⟨m, hm⟩ := hIfin
  have htot : ((2 : ℝ) ^ N - 1) * ∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1) =
      ∑' n : A, (((2 ^ N - 2 ^ (N % n.1)) / (2 ^ n.1 - 1) : ℕ) : ℝ) +
        ∑' n : A, ((2 : ℝ) ^ (N % n.1) - 1) / ((2 : ℝ) ^ n.1 - 1) := by
    rw [← tsum_mul_left, ← Summable.tsum_add hIA hremA]
    exact tsum_congr (fun n => split n.1 N)
  have hd : (r.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  have hden : (r.den : ℝ) * (r : ℝ) = r.num := by
    rw [Rat.cast_def]
    field_simp
  refine ⟨(2 ^ N - 1) * r.num - r.den * m, ?_⟩
  have hD : ∑' n : A, ((2 : ℝ) ^ (N % n.1) - 1) / ((2 : ℝ) ^ n.1 - 1) =
      ((2 : ℝ) ^ N - 1) * (r : ℝ) - m := by
    rw [hr]
    linarith
  rw [hD]
  push_cast
  rw [mul_sub, ← hden]
  ring

/-- Erdős 1968, given the averaging lemma `H2`: the convergent case. -/
theorem convergent_case (h2 : H2) (A : Set ℕ) (hA : A.Infinite)
    (hs : Summable (fun a : A => 1 / (a : ℝ))) :
    Irrational (∑' n : A, (1 : ℝ) / (2 ^ n.1 - 1)) := by
  rintro ⟨r, hr⟩
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  obtain ⟨K, hK⟩ := h2 A hs (1 / r.den) (by positivity)
  obtain ⟨N, hN0, hMN, hlt⟩ := hK K.factorial (Nat.factorial_pos K)
  obtain ⟨z, hz⟩ := den_mul_rem_int A r hr N
  -- the elements `n ≤ K` of `A` divide `N`, so their remainders vanish
  have hvan : ∑' n : A, ((2 : ℝ) ^ (N % n.1) - 1) / ((2 : ℝ) ^ n.1 - 1) =
      ∑' n : A, (if K < n.1 then ((2 : ℝ) ^ (N % n.1) - 1) / ((2 : ℝ) ^ n.1 - 1) else 0) := by
    apply tsum_congr
    intro n
    split_ifs with h
    · rfl
    · push Not at h
      rcases Nat.eq_zero_or_pos n.1 with h0 | hpos
      · simp [h0]
      · have hdvd : n.1 ∣ N := (Nat.dvd_factorial hpos h).trans hMN
        simp [Nat.mod_eq_zero_of_dvd hdvd]
  -- an element of `A` above `N` gives a positive term
  have hpos : 0 < ∑' n : A, ((2 : ℝ) ^ (N % n.1) - 1) / ((2 : ℝ) ^ n.1 - 1) := by
    obtain ⟨b, hbA, hb⟩ := hA.exists_gt N
    refine (summable_rem A N).tsum_pos (fun n => rem_nonneg _ _) ⟨b, hbA⟩ ?_
    simp only
    rw [Nat.mod_eq_of_lt hb]
    have h1 := two_le_two_pow hN0
    have h2' := two_le_two_pow (hN0.trans hb)
    apply div_pos <;> linarith
  have hzpos : (0 : ℝ) < z := by
    rw [← hz]
    positivity
  have hzlt : (z : ℝ) < 1 := by
    rw [← hz, hvan]
    calc (r.den : ℝ) * _ < r.den * (1 / r.den) := by gcongr
      _ = 1 := by field_simp
  have h1 : (0 : ℤ) < z := by exact_mod_cast hzpos
  have h2' : z < 1 := by exact_mod_cast hzlt
  omega

theorem main : H1 → H2 → type_of% @Erdos257.erdos_257 := by
  intro h1 h2 A hA
  by_cases hs : Summable (fun a : A => 1 / (a : ℝ))
  · exact convergent_case h2 A hA hs
  · exact h1 A hA hs

end OMA.R_Erdos257_erdos_257_R1

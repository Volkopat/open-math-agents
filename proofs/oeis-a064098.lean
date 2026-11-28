import OMAStatements.S_oeis_a064098

/-!
# Proof of the conjecture recorded in OEIS A064098

The sequence is `a(1) = a(2) = a(3) = 1`, `a(n+1) = (a(n)^2 + a(n-1)^2)/a(n-2)`.
The statement is `log(log(a(n)))/n → log((sqrt 5 + 1)/2)` (Giese 2005, Cloitre 2002).
The OEIS entry records it as true, following Andrew Hone (Jan 16 2006): for `n > 4`,
`2^(F(n-1) - 1) < a(n) < 3^(F(n-1) - 1)` with `F` the Fibonacci numbers.

Outline of the formal proof:
* consecutive terms satisfy the Markov equation `x^2 + y^2 + z^2 = 3xyz`, so the division in the
  recurrence is exact and `a(n+4) + a(n+1) = 3 a(n+2) a(n+3)`;
* the sequence is nondecreasing, which gives `2^F(m) ≤ a(m+3)` and `3 a(n) ≤ 3^F(n)`;
* `φ^n ≤ F(n+2)` and `F(n+1) ≤ φ^n` for the golden ratio `φ`;
* hence `m log φ + log log 2 ≤ log log a(m+5) ≤ (m+4) log φ + log log 3`, and a squeeze gives
  the limit.
-/

namespace OMA.S_oeis_a064098

theorem a_rec (n : ℕ) : a (n + 4) = (a (n + 3) ^ 2 + a (n + 2) ^ 2) / a (n + 1) := by
  rw [a]

/-- From the Markov relation, the quotient in the recurrence is `3yz - x`. -/
theorem quot_eq {x y z : ℕ} (hx : 0 < x) (h : x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z) :
    (z ^ 2 + y ^ 2) / x + x = 3 * y * z := by
  have hle : x ≤ 3 * y * z := by
    by_contra hlt
    have hlt' : 3 * y * z < x := Nat.lt_of_not_le hlt
    have h1 : x * (3 * y * z) < x * x := mul_lt_mul_of_pos_left hlt' hx
    nlinarith
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hle
  have hxq : x * q = z ^ 2 + y ^ 2 := by
    have h3 : 3 * x * y * z = x * (x + q) := by rw [← hq]; ring
    nlinarith
  rw [← hxq, Nat.mul_div_cancel_left _ hx, hq]
  ring

/-- Consecutive terms are positive and satisfy the Markov equation. -/
theorem markov (n : ℕ) : 0 < a (n + 1) ∧ 0 < a (n + 2) ∧ 0 < a (n + 3) ∧
    a (n + 1) ^ 2 + a (n + 2) ^ 2 + a (n + 3) ^ 2 = 3 * a (n + 1) * a (n + 2) * a (n + 3) := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨hx, hy, hz, h⟩ := ih
    have hq : a (n + 4) + a (n + 1) = 3 * a (n + 2) * a (n + 3) := by
      have := quot_eq hx h
      rwa [← a_rec n] at this
    have h5 : a (n + 1) * (a (n + 4) + a (n + 1)) = a (n + 1) * (3 * a (n + 2) * a (n + 3)) := by
      rw [hq]
    have hxq : a (n + 1) * a (n + 4) = a (n + 2) ^ 2 + a (n + 3) ^ 2 := by nlinarith
    have hq0 : 0 < a (n + 4) := by
      rcases Nat.eq_zero_or_pos (a (n + 4)) with h0 | h0
      · rw [h0] at hxq
        nlinarith [pow_pos hy 2]
      · exact h0
    have h6 : (a (n + 4) + a (n + 1)) * a (n + 4) = 3 * a (n + 2) * a (n + 3) * a (n + 4) := by
      rw [hq]
    show 0 < a (n + 2) ∧ 0 < a (n + 3) ∧ 0 < a (n + 4) ∧
      a (n + 2) ^ 2 + a (n + 3) ^ 2 + a (n + 4) ^ 2 = 3 * a (n + 2) * a (n + 3) * a (n + 4)
    refine ⟨hy, hz, hq0, ?_⟩
    nlinarith

/-- The linear form of the recurrence: `a(n+4) = 3 a(n+3) a(n+2) - a(n+1)`. -/
theorem lin (n : ℕ) : a (n + 4) + a (n + 1) = 3 * a (n + 2) * a (n + 3) := by
  obtain ⟨hx, _, _, h⟩ := markov n
  have := quot_eq hx h
  rwa [← a_rec n] at this

theorem mono (n : ℕ) : a (n + 1) ≤ a (n + 2) ∧ a (n + 2) ≤ a (n + 3) := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have hl := lin n
    have hy : 0 < a (n + 2) := (markov n).2.1
    have h3 : a (n + 3) ≤ a (n + 2) * a (n + 3) := Nat.le_mul_of_pos_left _ hy
    show a (n + 2) ≤ a (n + 3) ∧ a (n + 3) ≤ a (n + 4)
    refine ⟨h2, ?_⟩
    nlinarith

theorem lower (m : ℕ) : 2 ^ Nat.fib m ≤ a (m + 3) ∧ 2 ^ Nat.fib (m + 1) ≤ a (m + 4) := by
  induction m with
  | zero => decide
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    have hl : a (m + 5) + a (m + 2) = 3 * a (m + 3) * a (m + 4) := lin (m + 1)
    have hm : a (m + 2) ≤ a (m + 3) := (mono (m + 1)).1
    have hp : 0 < a (m + 4) := (markov (m + 1)).2.2.1
    have hmul : 2 ^ Nat.fib m * 2 ^ Nat.fib (m + 1) ≤ a (m + 3) * a (m + 4) := Nat.mul_le_mul h1 h2
    have h3 : a (m + 3) ≤ a (m + 3) * a (m + 4) := Nat.le_mul_of_pos_right _ hp
    have hf : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
    show 2 ^ Nat.fib (m + 1) ≤ a (m + 4) ∧ 2 ^ Nat.fib (m + 2) ≤ a (m + 5)
    refine ⟨h2, ?_⟩
    rw [hf, pow_add]
    nlinarith

theorem upper (n : ℕ) : 3 * a (n + 1) ≤ 3 ^ Nat.fib (n + 1) ∧ 3 * a (n + 2) ≤ 3 ^ Nat.fib (n + 2) ∧
    3 * a (n + 3) ≤ 3 ^ Nat.fib (n + 3) := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨_, h2, h3⟩ := ih
    have hl : a (n + 4) + a (n + 1) = 3 * a (n + 2) * a (n + 3) := lin n
    have hf : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    have hmul : (3 * a (n + 2)) * (3 * a (n + 3)) ≤ 3 ^ Nat.fib (n + 2) * 3 ^ Nat.fib (n + 3) :=
      Nat.mul_le_mul h2 h3
    show 3 * a (n + 2) ≤ 3 ^ Nat.fib (n + 2) ∧ 3 * a (n + 3) ≤ 3 ^ Nat.fib (n + 3) ∧
      3 * a (n + 4) ≤ 3 ^ Nat.fib (n + 4)
    refine ⟨h2, h3, ?_⟩
    rw [hf, pow_add]
    nlinarith

/-- Fibonacci numbers are squeezed between powers of the golden ratio. -/
theorem fib_bounds (n : ℕ) :
    ((Nat.fib (n + 1) : ℝ) ≤ Real.goldenRatio ^ n ∧
      (Nat.fib (n + 2) : ℝ) ≤ Real.goldenRatio ^ (n + 1)) ∧
    (Real.goldenRatio ^ n ≤ (Nat.fib (n + 2) : ℝ) ∧
      Real.goldenRatio ^ (n + 1) ≤ (Nat.fib (n + 3) : ℝ)) := by
  have hsq := Real.goldenRatio_sq
  have h1 := Real.one_lt_goldenRatio
  have h2 := Real.goldenRatio_lt_two
  induction n with
  | zero =>
    have e1 : Nat.fib 1 = 1 := by decide
    have e2 : Nat.fib 2 = 1 := by decide
    have e3 : Nat.fib 3 = 2 := by decide
    simp only [zero_add, e1, e2, e3, pow_zero, pow_one]
    norm_num
    constructor <;> linarith
  | succ n ih =>
    obtain ⟨⟨u1, u2⟩, l1, l2⟩ := ih
    have hp : Real.goldenRatio ^ (n + 2) = Real.goldenRatio ^ n + Real.goldenRatio ^ (n + 1) := by
      rw [pow_add, hsq]; ring
    have hf3 : (Nat.fib (n + 3) : ℝ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
      have : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
      rw [this]; push_cast; ring
    have hf4 : (Nat.fib (n + 4) : ℝ) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
      have : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
      rw [this]; push_cast; ring
    show ((Nat.fib (n + 2) : ℝ) ≤ Real.goldenRatio ^ (n + 1) ∧
        (Nat.fib (n + 3) : ℝ) ≤ Real.goldenRatio ^ (n + 2)) ∧
      (Real.goldenRatio ^ (n + 1) ≤ (Nat.fib (n + 3) : ℝ) ∧
        Real.goldenRatio ^ (n + 2) ≤ (Nat.fib (n + 4) : ℝ))
    refine ⟨⟨u2, ?_⟩, l2, ?_⟩
    · rw [hf3, hp]; linarith
    · rw [hf4, hp]; linarith

/-- Two-sided bounds for `log log a(m+5)`. -/
theorem loglog_bounds (m : ℕ) :
    (m : ℝ) * Real.log Real.goldenRatio + Real.log (Real.log 2) ≤
        Real.log (Real.log (a (m + 5))) ∧
      Real.log (Real.log (a (m + 5))) ≤
        ((m : ℝ) + 4) * Real.log Real.goldenRatio + Real.log (Real.log 3) := by
  have hφ0 : (0 : ℝ) < Real.goldenRatio := Real.goldenRatio_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hL : (2 : ℝ) ^ Nat.fib (m + 2) ≤ (a (m + 5) : ℝ) := by
    have : 2 ^ Nat.fib (m + 2) ≤ a (m + 5) := (lower (m + 2)).1
    exact_mod_cast this
  have hU : (a (m + 5) : ℝ) ≤ (3 : ℝ) ^ Nat.fib (m + 5) := by
    have h3 : 3 * a (m + 5) ≤ 3 ^ Nat.fib (m + 5) := (upper (m + 2)).2.2
    have : a (m + 5) ≤ 3 ^ Nat.fib (m + 5) := le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) h3
    exact_mod_cast this
  have hapos : (0 : ℝ) < (a (m + 5) : ℝ) := lt_of_lt_of_le (by positivity) hL
  have h1 : (Nat.fib (m + 2) : ℝ) * Real.log 2 ≤ Real.log (a (m + 5)) := by
    have := Real.log_le_log (by positivity) hL
    rwa [Real.log_pow] at this
  have hφm : Real.goldenRatio ^ m ≤ (Nat.fib (m + 2) : ℝ) := (fib_bounds m).2.1
  have h2 : Real.goldenRatio ^ m * Real.log 2 ≤ Real.log (a (m + 5)) :=
    le_trans (mul_le_mul_of_nonneg_right hφm hlog2.le) h1
  have hpos : 0 < Real.goldenRatio ^ m * Real.log 2 := mul_pos (pow_pos hφ0 m) hlog2
  have hlogpos : 0 < Real.log (a (m + 5)) := lt_of_lt_of_le hpos h2
  have h4 : Real.log (a (m + 5)) ≤ (Nat.fib (m + 5) : ℝ) * Real.log 3 := by
    have := Real.log_le_log hapos hU
    rwa [Real.log_pow] at this
  have hφu : (Nat.fib (m + 5) : ℝ) ≤ Real.goldenRatio ^ (m + 4) := (fib_bounds (m + 4)).1.1
  have h5 : Real.log (a (m + 5)) ≤ Real.goldenRatio ^ (m + 4) * Real.log 3 :=
    le_trans h4 (mul_le_mul_of_nonneg_right hφu hlog3.le)
  constructor
  · have h3 := Real.log_le_log hpos h2
    rw [Real.log_mul (pow_pos hφ0 m).ne' hlog2.ne', Real.log_pow] at h3
    exact h3
  · have h6 := Real.log_le_log hlogpos h5
    rw [Real.log_mul (pow_pos hφ0 (m + 4)).ne' hlog3.ne', Real.log_pow] at h6
    push_cast at h6
    exact h6

/-- A squeeze argument: linear lower and upper bounds with the same slope force `f n / n → L`. -/
theorem squeeze_aux (f : ℕ → ℝ) (L c d : ℝ)
    (hlo : ∀ m : ℕ, (m : ℝ) * L + c ≤ f (m + 5))
    (hhi : ∀ m : ℕ, f (m + 5) ≤ ((m : ℝ) + 4) * L + d) :
    Filter.Tendsto (fun n : ℕ => f n / n) Filter.atTop (nhds L) := by
  have hlow : Filter.Tendsto (fun n : ℕ => L - (5 * L - c) / (n : ℝ)) Filter.atTop (nhds L) := by
    have h := (tendsto_const_nhds (x := L) (f := (Filter.atTop : Filter ℕ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (5 * L - c))
    rwa [sub_zero] at h
  have hupp : Filter.Tendsto (fun n : ℕ => L + (d - L) / (n : ℝ)) Filter.atTop (nhds L) := by
    have h := (tendsto_const_nhds (x := L) (f := (Filter.atTop : Filter ℕ))).add
      (tendsto_const_div_atTop_nhds_zero_nat (d - L))
    rwa [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 5] with n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have hne : ((m : ℝ) + 5) ≠ 0 := by positivity
    have hpos : (0 : ℝ) < ((m + 5 : ℕ) : ℝ) := by positivity
    rw [le_div_iff₀ hpos]
    have e : (L - (5 * L - c) / ((m + 5 : ℕ) : ℝ)) * ((m + 5 : ℕ) : ℝ) = (m : ℝ) * L + c := by
      push_cast
      field_simp
      ring
    rw [e]
    exact hlo m
  · filter_upwards [Filter.eventually_ge_atTop 5] with n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have hne : ((m : ℝ) + 5) ≠ 0 := by positivity
    have hpos : (0 : ℝ) < ((m + 5 : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hpos]
    have e : (L + (d - L) / ((m + 5 : ℕ) : ℝ)) * ((m + 5 : ℕ) : ℝ) = ((m : ℝ) + 4) * L + d := by
      push_cast
      field_simp
      ring
    rw [e]
    exact hhi m

end OMA.S_oeis_a064098

theorem OMA.solution : type_of% @OMA.S_oeis_a064098.main := by
  have hφ : (Real.sqrt 5 + 1) / 2 = Real.goldenRatio := by
    unfold Real.goldenRatio
    ring
  show Filter.Tendsto (fun n : ℕ => Real.log (Real.log (OMA.S_oeis_a064098.a n)) / n) Filter.atTop
    (nhds (Real.log ((Real.sqrt 5 + 1) / 2)))
  rw [hφ]
  exact OMA.S_oeis_a064098.squeeze_aux (fun n => Real.log (Real.log (OMA.S_oeis_a064098.a n))) _ _ _
    (fun m => (OMA.S_oeis_a064098.loglog_bounds m).1)
    (fun m => (OMA.S_oeis_a064098.loglog_bounds m).2)

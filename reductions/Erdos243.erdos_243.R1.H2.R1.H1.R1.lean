import OMAReductions.R_Erdos243_erdos_243_R1_H2_R1

-- Reduction Erdos243.erdos_243.R1.H2.R1.H1.R1 of step Erdos243.erdos_243.R1.H2.R1.H1
-- Credit: @rickmanelius

/-!
# Erdős 243, sub-Sylvester regime: the defect must be small against the next term

The step is the sub-Sylvester regime `a (n+1) ≤ a n ^ 2 - a n + 1` (for all large `n`) of the
statement that the numerators `c` do not tend to infinity. Write
`D n = a n ^ 2 - a n + 1 - a (n+1) ≥ 0` for the Sylvester defect,
`A n = a (n+1) + a n - 1 ≥ 3` and `e n = c (n+1) - c n`. The second order recursion of the parent
gives `e (n+1) = A n * e n - D n * c n` (`increment_identity`).

Proved below with no hypothesis:
* `eventually_nondecreasing`: in this regime `c` is eventually nondecreasing. A negative
  increment is multiplied by at least `3` at every later step while `c` keeps decreasing, which
  breaks the vanishing relative increments (with `k = 1`) after `c n` steps.
* `farSub_case`: if `A n ≤ k * D n` for some `k` and infinitely many `n` (the defect is not small
  against `a (n+1) + a n`, so that `a (n+1) / a n ^ 2` stays below `k / (k+1)` along these `n`),
  the hypotheses are contradictory: `e (n+1) ≥ 0` gives `A n * e n ≥ D n * c n`, hence
  `k * e n ≥ c n`, against the vanishing relative increments with this `k`.
* the exact Sylvester case `D n = 0` for all large `n` is the parent's `superSylvester_case`.

What is left is the near-Sylvester regime `k * D n < A n` eventually for every `k`, with
`D n > 0` infinitely often, split by whether the defect is eventually always positive:
* `H1`: `a (n+1) < a n ^ 2 - a n + 1` for all large `n`;
* `H2`: equality and strict inequality both occur infinitely often.
In both, `c` is in fact forced to tend to infinity (at every `n` with `D n > 0` the increment
satisfies `A n * e n ≥ D n * c n > 0`), so each hypothesis asserts that no sequence of the given
kind exists. This is the core of Erdős 243, whose hypothesis `a (n+1) / a n ^ 2 → 1` holds here.
-/

namespace OMA.R_Erdos243_erdos_243_R1_H2_R1_H1_R1

/-- The near-Sylvester regime with a positive defect at every large index:
`a (n+1) < a n ^ 2 - a n + 1` eventually, and `k * D n < A n` eventually for every `k`. -/
def H1 : Prop :=
  ∀ (a c d : ℕ → ℕ), StrictMono a →
    (∀ n, 0 < c n) →
    (∀ n, 0 < d n) →
    (∀ n, c (n + 1) + d n = a n * c n) →
    (∀ n, d (n + 1) = a n * d n) →
    (∀ k : ℕ, ∃ N, ∀ n ≥ N,
      k * (c (n + 1) - c n) < c n ∧ k * (c n - c (n + 1)) < c n) →
    (∃ N, ∀ n ≥ N, a (n + 1) < a n * a n - a n + 1) →
    (∀ k : ℕ, ∃ N, ∀ n ≥ N,
      k * (a n * a n - a n + 1 - a (n + 1)) < a (n + 1) + a n - 1) →
    ¬ (∀ B, ∃ N, ∀ n ≥ N, B < c n)

/-- The near-Sylvester regime with a mixed defect: `a (n+1) ≤ a n ^ 2 - a n + 1` eventually, with
equality infinitely often and strict inequality infinitely often, and `k * D n < A n`
eventually for every `k`. -/
def H2 : Prop :=
  ∀ (a c d : ℕ → ℕ), StrictMono a →
    (∀ n, 0 < c n) →
    (∀ n, 0 < d n) →
    (∀ n, c (n + 1) + d n = a n * c n) →
    (∀ n, d (n + 1) = a n * d n) →
    (∀ k : ℕ, ∃ N, ∀ n ≥ N,
      k * (c (n + 1) - c n) < c n ∧ k * (c n - c (n + 1)) < c n) →
    (∃ N, ∀ n ≥ N, a (n + 1) ≤ a n * a n - a n + 1) →
    (∀ N, ∃ n ≥ N, a (n + 1) = a n * a n - a n + 1) →
    (∀ N, ∃ n ≥ N, a (n + 1) < a n * a n - a n + 1) →
    (∀ k : ℕ, ∃ N, ∀ n ≥ N,
      k * (a n * a n - a n + 1 - a (n + 1)) < a (n + 1) + a n - 1) →
    ¬ (∀ B, ∃ N, ∀ n ≥ N, B < c n)

/-- `e (n+1) = A n * e n - D n * c n`, from the parent's second order recursion. -/
lemma increment_identity {a c d : ℕ → ℕ}
    (hrec1 : ∀ n, c (n + 1) + d n = a n * c n) (hrec2 : ∀ n, d (n + 1) = a n * d n) (n : ℕ) :
    (c (n + 2) : ℤ) - c (n + 1) =
      -(((a n : ℤ) * a n - a n + 1 - a (n + 1)) * c n) +
        ((a (n + 1) : ℤ) + a n - 1) * ((c (n + 1) : ℤ) - c n) := by
  have key := OMA.R_Erdos243_erdos_243_R1_H2_R1.second_order hrec1 hrec2 n
  rw [key]
  ring

/-- The natural-number defect is the integer defect in the sub-Sylvester regime. -/
lemma defect_cast {x y : ℕ} (h : y ≤ x * x - x + 1) :
    ((x * x - x + 1 - y : ℕ) : ℤ) = (x : ℤ) * x - x + 1 - y := by
  have hsq : x ≤ x * x := Nat.le_mul_self x
  push_cast [Nat.cast_sub h, Nat.cast_sub hsq]
  ring

lemma width_cast {x y : ℕ} (h : 1 ≤ y + x) :
    ((y + x - 1 : ℕ) : ℤ) = (y : ℤ) + x - 1 := by
  push_cast [Nat.cast_sub h]
  ring

/-- In the sub-Sylvester regime the numerators are eventually nondecreasing. -/
theorem eventually_nondecreasing (a c d : ℕ → ℕ) (ha : StrictMono a)
    (hrec1 : ∀ n, c (n + 1) + d n = a n * c n) (hrec2 : ∀ n, d (n + 1) = a n * d n)
    (hclose : ∀ k : ℕ, ∃ N, ∀ n ≥ N,
      k * (c (n + 1) - c n) < c n ∧ k * (c n - c (n + 1)) < c n)
    (hsub : ∃ N, ∀ n ≥ N, a (n + 1) ≤ a n * a n - a n + 1) :
    ∃ M, ∀ n ≥ M, c n ≤ c (n + 1) := by
  obtain ⟨N0, hN0⟩ := hsub
  obtain ⟨N1, hN1⟩ := hclose 1
  have hge : ∀ n, n ≤ a n := fun n => ha.id_le n
  refine ⟨max (max N0 N1) 2, ?_⟩
  intro m hm
  by_contra hlt
  push Not at hlt
  have hmN0 : N0 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmN1 : N1 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm2 : 2 ≤ m := le_trans (le_max_right _ _) hm
  -- the decrements are at least `3 ^ j`, and the numerators stay below `c m`
  have hind : ∀ j : ℕ, (3 : ℤ) ^ j ≤ (c (m + j) : ℤ) - c (m + j + 1) ∧ c (m + j) ≤ c m := by
    intro j
    induction j with
    | zero =>
      refine ⟨?_, by simp⟩
      simp only [pow_zero, add_zero]
      have : (c (m + 1) : ℤ) < c m := by exact_mod_cast hlt
      linarith
    | succ j ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hm0 : N0 ≤ m + j := by omega
      have hA3 : 3 ≤ a (m + j + 1) + a (m + j) - 1 := by
        have := hge (m + j); have := hge (m + j + 1); omega
      have key := increment_identity hrec1 hrec2 (m + j)
      have hD : (0 : ℤ) ≤ (a (m + j) : ℤ) * a (m + j) - a (m + j) + 1 - a (m + j + 1) := by
        rw [← defect_cast (hN0 (m + j) hm0)]
        positivity
      have hA : (3 : ℤ) ≤ (a (m + j + 1) : ℤ) + a (m + j) - 1 := by
        rw [← width_cast (by omega)]
        exact_mod_cast hA3
      have hcpos : (0 : ℤ) ≤ c (m + j) := by positivity
      have hstep : (c (m + j + 2) : ℤ) - c (m + j + 1) ≤
          ((a (m + j + 1) : ℤ) + a (m + j) - 1) * ((c (m + j + 1) : ℤ) - c (m + j)) := by
        rw [key]
        nlinarith [mul_nonneg hD hcpos]
      have hpow : (0 : ℤ) < 3 ^ j := by positivity
      refine ⟨?_, ?_⟩
      · rw [show m + (j + 1) = m + j + 1 by ring, show m + j + 1 + 1 = m + j + 2 by ring, pow_succ]
        nlinarith
      · rw [show m + (j + 1) = m + j + 1 by ring]
        have : (c (m + j + 1) : ℤ) ≤ c (m + j) := by linarith
        have : c (m + j + 1) ≤ c (m + j) := by exact_mod_cast this
        omega
  -- after `c m` steps the decrement exceeds the numerator
  obtain ⟨h1, h2⟩ := hind (c m)
  have hcl := (hN1 (m + c m) (by omega)).2
  have hpow : c m < 3 ^ c m := Nat.lt_pow_self (by norm_num)
  have hle : c (m + c m + 1) ≤ c (m + c m) := by
    have : (c (m + c m + 1) : ℤ) ≤ c (m + c m) := by
      have : (0 : ℤ) < 3 ^ c m := by positivity
      linarith
    exact_mod_cast this
  have h1' : 3 ^ c m ≤ c (m + c m) - c (m + c m + 1) := by
    have : ((c (m + c m) - c (m + c m + 1) : ℕ) : ℤ) = (c (m + c m) : ℤ) - c (m + c m + 1) := by
      push_cast [Nat.cast_sub hle]
      ring
    have h3 : ((3 ^ c m : ℕ) : ℤ) ≤ ((c (m + c m) - c (m + c m + 1) : ℕ) : ℤ) := by
      rw [this]
      push_cast
      exact h1
    exact_mod_cast h3
  omega

/-- If `A n ≤ k * D n` for infinitely many `n`, the hypotheses of the step are contradictory. -/
theorem farSub_case (a c d : ℕ → ℕ) (ha : StrictMono a)
    (hrec1 : ∀ n, c (n + 1) + d n = a n * c n) (hrec2 : ∀ n, d (n + 1) = a n * d n)
    (hclose : ∀ k : ℕ, ∃ N, ∀ n ≥ N,
      k * (c (n + 1) - c n) < c n ∧ k * (c n - c (n + 1)) < c n)
    (hsub : ∃ N, ∀ n ≥ N, a (n + 1) ≤ a n * a n - a n + 1)
    (hfar : ∃ k : ℕ, ∀ N, ∃ n ≥ N,
      a (n + 1) + a n - 1 ≤ k * (a n * a n - a n + 1 - a (n + 1))) :
    False := by
  obtain ⟨M, hM⟩ := eventually_nondecreasing a c d ha hrec1 hrec2 hclose hsub
  obtain ⟨N0, hN0⟩ := hsub
  obtain ⟨k, hk⟩ := hfar
  obtain ⟨Nk, hNk⟩ := hclose k
  have hge : ∀ n, n ≤ a n := fun n => ha.id_le n
  obtain ⟨n, hn, hA⟩ := hk (max (max M N0) (max Nk 2))
  have hnM : M ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN0 : N0 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnNk : Nk ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn2 : 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have he0 : c n ≤ c (n + 1) := hM n hnM
  have he1 : c (n + 1) ≤ c (n + 2) := hM (n + 1) (by omega)
  have key := increment_identity hrec1 hrec2 n
  have hcl := (hNk n hnNk).1
  have hA3 : 3 ≤ a (n + 1) + a n - 1 := by
    have := hge n; have := hge (n + 1); omega
  have hAZ : ((a (n + 1) + a n - 1 : ℕ) : ℤ) = (a (n + 1) : ℤ) + a n - 1 := width_cast (by omega)
  have hDZ := defect_cast (hN0 n hnN0)
  have hA' : (a (n + 1) : ℤ) + a n - 1 ≤ (k : ℤ) * ((a n : ℤ) * a n - a n + 1 - a (n + 1)) := by
    rw [← hAZ, ← hDZ]
    exact_mod_cast hA
  have hApos : (3 : ℤ) ≤ (a (n + 1) : ℤ) + a n - 1 := by
    rw [← hAZ]
    exact_mod_cast hA3
  have he1Z : (0 : ℤ) ≤ (c (n + 2) : ℤ) - c (n + 1) := by
    have : (c (n + 1) : ℤ) ≤ c (n + 2) := by exact_mod_cast he1
    linarith
  have heZ : ((c (n + 1) - c n : ℕ) : ℤ) = (c (n + 1) : ℤ) - c n := by
    push_cast [Nat.cast_sub he0]
    ring
  have hke : (k : ℤ) * ((c (n + 1) : ℤ) - c n) < c n := by
    rw [← heZ]
    exact_mod_cast hcl
  have hc0 : (0 : ℤ) ≤ c n := by positivity
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hDc : ((a n : ℤ) * a n - a n + 1 - a (n + 1)) * c n ≤
      ((a (n + 1) : ℤ) + a n - 1) * ((c (n + 1) : ℤ) - c n) := by
    linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hA') hc0, mul_nonneg hk0 (sub_nonneg.mpr hDc),
    mul_lt_mul_of_pos_left hke (by linarith : (0 : ℤ) < (a (n + 1) : ℤ) + a n - 1)]

theorem main : H1 → H2 → OMA.R_Erdos243_erdos_243_R1_H2_R1.H1 := by
  intro h1 h2
  unfold OMA.R_Erdos243_erdos_243_R1_H2_R1.H1
  intro a c d ha hc hd hrec1 hrec2 hclose hsub
  by_cases hfar : ∃ k : ℕ, ∀ N, ∃ n ≥ N,
      a (n + 1) + a n - 1 ≤ k * (a n * a n - a n + 1 - a (n + 1))
  · exact (farSub_case a c d ha hrec1 hrec2 hclose hsub hfar).elim
  · push Not at hfar
    by_cases hexact : ∃ N, ∀ n ≥ N, a n * a n - a n + 1 ≤ a (n + 1)
    · exact OMA.R_Erdos243_erdos_243_R1_H2_R1.superSylvester_case a c d ha hc hrec1 hrec2
        hclose hexact
    · push Not at hexact
      by_cases hstrict : ∃ N, ∀ n ≥ N, a (n + 1) < a n * a n - a n + 1
      · exact h1 a c d ha hc hd hrec1 hrec2 hclose hstrict hfar
      · push Not at hstrict
        refine h2 a c d ha hc hd hrec1 hrec2 hclose hsub ?_ hexact hfar
        intro N
        obtain ⟨N0, hN0⟩ := hsub
        obtain ⟨n, hn, hle⟩ := hstrict (max N N0)
        exact ⟨n, le_trans (le_max_left _ _) hn,
          le_antisymm (hN0 n (le_trans (le_max_right _ _) hn)) hle⟩

end OMA.R_Erdos243_erdos_243_R1_H2_R1_H1_R1

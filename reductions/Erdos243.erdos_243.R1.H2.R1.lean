import OMAReductions.R_Erdos243_erdos_243_R1

-- Reduction Erdos243.erdos_243.R1.H2.R1 of step Erdos243.erdos_243.R1.H2
-- Credit: @rickmanelius

/-!
# Erdős 243, step H2: split by the sign of the Sylvester defect

The step asks that the positive integer numerators `c` of the tail sums do not tend to infinity,
given `c (n+1) + d n = a n * c n`, `d (n+1) = a n * d n` and vanishing relative increments of `c`.

Eliminating `d` gives the second order recursion
`c (n+2) = (a (n+1) + a n) c (n+1) - a n ^ 2 c n`, hence for the increment `e n = c (n+1) - c n`:
`e (n+1) = (a (n+1) + a n - 1 - a n ^ 2) c n + (a (n+1) + a n - 1) e n`.
The first coefficient is the negative of the Sylvester defect `a n ^ 2 - a n + 1 - a (n+1)`.

Proved below, with no hypothesis (`superSylvester_case`): if `a (n+1) ≥ a n ^ 2 - a n + 1` for all
large `n` (the regime of Badea's irrationality theorem), then a positive increment at a large index
is multiplied by at least `3` at every later step, while the vanishing relative increments keep
`c (n+1) < 2 c n`; after `2 c n` steps the increment exceeds the numerator, which contradicts the
hypothesis with `k = 1`. So `c` is eventually nonincreasing, hence bounded.

The two remaining regimes are left as hypotheses, each the step restricted to one regime:
* `H1`: `a (n+1) ≤ a n ^ 2 - a n + 1` for all large `n` (in this regime the same identity forces
  `c` to be eventually nondecreasing, and the question is whether it can grow without bound);
* `H2`: the defect takes both strict signs infinitely often.
-/

namespace OMA.R_Erdos243_erdos_243_R1_H2_R1

/-- The step in the sub-Sylvester regime: `a (n+1) ≤ a n ^ 2 - a n + 1` for all large `n`. -/
def H1 : Prop :=
  ∀ (a c d : ℕ → ℕ), StrictMono a →
    (∀ n, 0 < c n) →
    (∀ n, 0 < d n) →
    (∀ n, c (n + 1) + d n = a n * c n) →
    (∀ n, d (n + 1) = a n * d n) →
    (∀ k : ℕ, ∃ N, ∀ n ≥ N,
      k * (c (n + 1) - c n) < c n ∧ k * (c n - c (n + 1)) < c n) →
    (∃ N, ∀ n ≥ N, a (n + 1) ≤ a n * a n - a n + 1) →
    ¬ (∀ B, ∃ N, ∀ n ≥ N, B < c n)

/-- The step in the oscillating regime: `a (n+1) < a n ^ 2 - a n + 1` for infinitely many `n` and
`a (n+1) > a n ^ 2 - a n + 1` for infinitely many `n`. -/
def H2 : Prop :=
  ∀ (a c d : ℕ → ℕ), StrictMono a →
    (∀ n, 0 < c n) →
    (∀ n, 0 < d n) →
    (∀ n, c (n + 1) + d n = a n * c n) →
    (∀ n, d (n + 1) = a n * d n) →
    (∀ k : ℕ, ∃ N, ∀ n ≥ N,
      k * (c (n + 1) - c n) < c n ∧ k * (c n - c (n + 1)) < c n) →
    (∀ N, ∃ n ≥ N, a (n + 1) < a n * a n - a n + 1) →
    (∀ N, ∃ n ≥ N, a n * a n - a n + 1 < a (n + 1)) →
    ¬ (∀ B, ∃ N, ∀ n ≥ N, B < c n)

/-- The second order recursion for the numerators: eliminating `d` from the two first order
recursions gives `c (n+2) = (a (n+1) + a n) c (n+1) - a n ^ 2 c n`. -/
lemma second_order {a c d : ℕ → ℕ}
    (hrec1 : ∀ n, c (n + 1) + d n = a n * c n) (hrec2 : ∀ n, d (n + 1) = a n * d n) (n : ℕ) :
    (c (n + 2) : ℤ) = ((a (n + 1) : ℤ) + a n) * c (n + 1) - (a n : ℤ) ^ 2 * c n := by
  have h1 : (c (n + 1) : ℤ) + d n = a n * c n := by exact_mod_cast hrec1 n
  have h2 : (c (n + 2) : ℤ) + d (n + 1) = a (n + 1) * c (n + 1) := by exact_mod_cast hrec1 (n + 1)
  have h3 : (d (n + 1) : ℤ) = a n * d n := by exact_mod_cast hrec2 n
  linear_combination h2 - h3 - (a n : ℤ) * h1

/-- In the super-Sylvester regime `a (n+1) ≥ a n ^ 2 - a n + 1`, a nonnegative numerator
increment is multiplied by at least `3` at the next step (once `a (n+1) + a n - 1 ≥ 3`). -/
lemma increment_grows {a c d : ℕ → ℕ}
    (hrec1 : ∀ n, c (n + 1) + d n = a n * c n) (hrec2 : ∀ n, d (n + 1) = a n * d n) {n : ℕ}
    (hsyl : a n * a n - a n + 1 ≤ a (n + 1)) (h3 : 3 ≤ a (n + 1) + a n - 1)
    (hinc : c n ≤ c (n + 1)) :
    3 * ((c (n + 1) : ℤ) - c n) ≤ (c (n + 2) : ℤ) - c (n + 1) := by
  have key := second_order hrec1 hrec2 n
  have hsq : a n ≤ a n * a n := Nat.le_mul_self (a n)
  have hsyl' : (a n : ℤ) * a n - a n + 1 ≤ a (n + 1) := by
    have : ((a n * a n - a n + 1 : ℕ) : ℤ) ≤ a (n + 1) := by exact_mod_cast hsyl
    push_cast [Nat.cast_sub hsq] at this
    linarith
  have h3' : (3 : ℤ) ≤ a (n + 1) + a n - 1 := by
    have h1le : 1 ≤ a (n + 1) + a n := by omega
    have : ((a (n + 1) + a n - 1 : ℕ) : ℤ) ≥ 3 := by exact_mod_cast h3
    push_cast [Nat.cast_sub h1le] at this
    linarith
  have hinc' : (c n : ℤ) ≤ c (n + 1) := by exact_mod_cast hinc
  have hc0 : (0 : ℤ) ≤ c n := by positivity
  have hexp : (c (n + 2) : ℤ) - c (n + 1) =
      ((a (n + 1) : ℤ) + a n - 1 - (a n : ℤ) ^ 2) * c n +
        ((a (n + 1) : ℤ) + a n - 1) * ((c (n + 1) : ℤ) - c n) := by
    rw [key]; ring
  rw [hexp]
  have hA : (0 : ℤ) ≤ (a (n + 1) : ℤ) + a n - 1 - (a n : ℤ) ^ 2 := by nlinarith
  have hB : (3 : ℤ) * ((c (n + 1) : ℤ) - c n) ≤
      ((a (n + 1) : ℤ) + a n - 1) * ((c (n + 1) : ℤ) - c n) :=
    mul_le_mul_of_nonneg_right h3' (by linarith)
  nlinarith [mul_nonneg hA hc0]

/-- `2 ^ j * (j + 2) ≤ 2 * 3 ^ j`. -/
lemma two_pow_mul_le (j : ℕ) : 2 ^ j * (j + 2) ≤ 2 * 3 ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [pow_succ, pow_succ]
    nlinarith [Nat.one_le_two_pow (n := j)]

/-- The super-Sylvester case: if `a (n+1) ≥ a n ^ 2 - a n + 1` for all large `n`, the numerators
are eventually nonincreasing, hence bounded, so they do not tend to infinity. -/
theorem superSylvester_case (a c d : ℕ → ℕ) (ha : StrictMono a) (hc : ∀ n, 0 < c n)
    (hrec1 : ∀ n, c (n + 1) + d n = a n * c n) (hrec2 : ∀ n, d (n + 1) = a n * d n)
    (hclose : ∀ k : ℕ, ∃ N, ∀ n ≥ N,
      k * (c (n + 1) - c n) < c n ∧ k * (c n - c (n + 1)) < c n)
    (hsyl : ∃ N, ∀ n ≥ N, a n * a n - a n + 1 ≤ a (n + 1)) :
    ¬ (∀ B, ∃ N, ∀ n ≥ N, B < c n) := by
  obtain ⟨N0, hN0⟩ := hsyl
  obtain ⟨N1, hN1⟩ := hclose 1
  have hge : ∀ n, n ≤ a n := fun n => ha.id_le n
  set M := max (max N0 N1) 2 with hM
  -- closeness with k = 1: c (n+1) < 2 c n, and the increment stays below c n
  have hlt2 : ∀ n ≥ N1, c (n + 1) < 2 * c n := by
    intro n hn
    have h := (hN1 n hn).1
    have := hc n
    omega
  have hincr : ∀ n ≥ N1, c (n + 1) - c n < c n := by
    intro n hn
    have h := (hN1 n hn).1
    omega
  -- the numerators are nonincreasing from M on
  have hnoninc : ∀ n ≥ M, c (n + 1) ≤ c n := by
    intro n hn
    by_contra hlt
    push Not at hlt
    have hnN0 : N0 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    -- increments at least 3 ^ j, numerators at most 2 ^ j * c n
    have hind : ∀ j : ℕ, (3 : ℤ) ^ j ≤ (c (n + j + 1) : ℤ) - c (n + j) ∧
        c (n + j) ≤ 2 ^ j * c n := by
      intro j
      induction j with
      | zero =>
        refine ⟨?_, by simp⟩
        simp only [pow_zero, add_zero]
        have : (c n : ℤ) < c (n + 1) := by exact_mod_cast hlt
        linarith
      | succ j ih =>
        obtain ⟨ih1, ih2⟩ := ih
        have hm0 : N0 ≤ n + j := by omega
        have hm1 : N1 ≤ n + j := by omega
        have hA3 : 3 ≤ a (n + j + 1) + a (n + j) - 1 := by
          have := hge (n + j); have := hge (n + j + 1); omega
        have hinc : c (n + j) ≤ c (n + j + 1) := by
          have : (0 : ℤ) < (c (n + j + 1) : ℤ) - c (n + j) := lt_of_lt_of_le (by positivity) ih1
          have : (c (n + j) : ℤ) ≤ c (n + j + 1) := by linarith
          exact_mod_cast this
        have hg := increment_grows hrec1 hrec2 (hN0 (n + j) hm0) hA3 hinc
        refine ⟨?_, ?_⟩
        · rw [show n + (j + 1) + 1 = n + j + 2 by ring, show n + (j + 1) = n + j + 1 by ring,
            pow_succ]
          nlinarith
        · rw [show n + (j + 1) = n + j + 1 by ring, pow_succ]
          have := hlt2 (n + j) hm1
          nlinarith
    -- after j = 2 c n steps the increment exceeds the numerator
    set j := 2 * c n with hj
    obtain ⟨h1, h2⟩ := hind j
    have hpow : 2 ^ j * (c n + 1) ≤ 3 ^ j := by
      have := two_pow_mul_le j
      have h2j : j + 2 = 2 * (c n + 1) := by omega
      rw [h2j] at this
      nlinarith
    have hbig : (c (n + j) : ℤ) < (c (n + j + 1) : ℤ) - c (n + j) := by
      have hcast : ((2 ^ j * (c n + 1) : ℕ) : ℤ) ≤ ((3 ^ j : ℕ) : ℤ) := by exact_mod_cast hpow
      have hcast2 : ((c (n + j) : ℕ) : ℤ) ≤ ((2 ^ j * c n : ℕ) : ℤ) := by exact_mod_cast h2
      push_cast at hcast hcast2
      have : (0 : ℤ) < 2 ^ j := by positivity
      nlinarith
    have hsmall := hincr (n + j) (by omega)
    have : (c (n + j + 1) : ℤ) - c (n + j) < c (n + j) := by
      have hle : c (n + j) ≤ c (n + j + 1) := by
        have : (c (n + j) : ℤ) ≤ c (n + j + 1) := by nlinarith [hc (n + j)]
        exact_mod_cast this
      have : ((c (n + j + 1) - c (n + j) : ℕ) : ℤ) < c (n + j) := by exact_mod_cast hsmall
      push_cast [Nat.cast_sub hle] at this
      linarith
    linarith
  -- bounded by c M from M on
  have hbound : ∀ m, c (M + m) ≤ c M := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have := hnoninc (M + m) (by omega)
      rw [show M + (m + 1) = M + m + 1 by ring]
      omega
  intro hinf
  obtain ⟨N, hN⟩ := hinf (c M)
  have h := hN (max N M) (le_max_left _ _)
  have h' := hbound (max N M - M)
  rw [show M + (max N M - M) = max N M by omega] at h'
  omega

theorem main : H1 → H2 → OMA.R_Erdos243_erdos_243_R1.H2 := by
  intro h1 h2
  unfold OMA.R_Erdos243_erdos_243_R1.H2
  intro a c d ha hc hd hrec1 hrec2 hclose
  by_cases hsup : ∃ N, ∀ n ≥ N, a n * a n - a n + 1 ≤ a (n + 1)
  · exact superSylvester_case a c d ha hc hrec1 hrec2 hclose hsup
  · push Not at hsup
    by_cases hsub : ∃ N, ∀ n ≥ N, a (n + 1) ≤ a n * a n - a n + 1
    · exact h1 a c d ha hc hd hrec1 hrec2 hclose hsub
    · push Not at hsub
      exact h2 a c d ha hc hd hrec1 hrec2 hclose hsup hsub

end OMA.R_Erdos243_erdos_243_R1_H2_R1

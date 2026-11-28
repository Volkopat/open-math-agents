import FormalConjectures.ErdosProblems.«285»

open Real
-- Problem: Erdős Problem 285 — lb
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/285.lean:67 (declaration Erdos285.erdos_285.variants.lb)
-- Credit: @Rahul-007afk (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-- A strictly increasing sequence of naturals indexed by `Fin (k + 1)` gains at least one per
step. -/
lemma OMA.strictMono_gap {k : ℕ} (n : Fin (k + 1) → ℕ) (hn : StrictMono n) :
    ∀ d : ℕ, ∀ i j : Fin (k + 1), i.val + d = j.val → n i + d ≤ n j := by
  intro d
  induction d with
  | zero =>
    intro i j hij
    have : i = j := Fin.ext (by omega)
    rw [this]
    omega
  | succ d ih =>
    intro i j hij
    have hlt : i.val + 1 < k + 1 := by have := j.isLt; omega
    have h1 : n i < n ⟨i.val + 1, hlt⟩ := hn (by rw [Fin.lt_def]; simp)
    have h2 := ih ⟨i.val + 1, hlt⟩ j (by simp; omega)
    omega

/-- `1 / x` dominates the increment of the logarithm. -/
lemma OMA.log_step (x : ℝ) (hx : 0 < x) : log (x + 1) - log x ≤ 1 / x := by
  have h1 : log ((x + 1) / x) ≤ (x + 1) / x - 1 :=
    log_le_sub_one_of_pos (by positivity)
  rw [log_div (by positivity) (ne_of_gt hx)] at h1
  have h2 : (x + 1) / x - 1 = 1 / x := by field_simp; ring
  linarith

/-- The key inequality. If `1` is a sum of `k + 1` distinct unit fractions with largest
denominator `N`, then the denominators are at most `N - k, …, N`, so the sum is at least
`log ((N + 1) / (N - k))`, whence `N + 1 ≤ e * (N - k)`. -/
lemma OMA.key {k : ℕ} (n : Fin (k + 1) → ℕ) (hn : StrictMono n) (h0 : 0 ∉ Set.range n)
    (hsum : 1 = ∑ i, (1 : ℝ) / n i) :
    exp 1 * ((k : ℝ) + 1) - (exp 1 - 1) ≤ (exp 1 - 1) * (n (Fin.last k) : ℝ) := by
  have hpos : ∀ i, 1 ≤ n i := by
    intro i
    by_contra hcon
    exact h0 ⟨i, by omega⟩
  have hgap : ∀ i : Fin (k + 1), n i + (k - i.val) ≤ n (Fin.last k) := by
    intro i
    exact OMA.strictMono_gap n hn (k - i.val) i (Fin.last k) (by have := i.isLt; simp; omega)
  have hNk : k + 1 ≤ n (Fin.last k) := by
    have h1 := hgap 0
    have h2 := hpos 0
    simp at h1
    omega
  obtain ⟨m, hm⟩ : ∃ m, m = n (Fin.last k) - k := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by omega
  have hterm : ∀ i : Fin (k + 1),
      log ((m : ℝ) + ((i.val + 1 : ℕ) : ℝ)) - log ((m : ℝ) + ((i.val : ℕ) : ℝ)) ≤
        (1 : ℝ) / n i := by
    intro i
    have hle : n i ≤ m + i.val := by have := hgap i; have := i.isLt; omega
    have hle' : (n i : ℝ) ≤ (m : ℝ) + (i.val : ℝ) := by exact_mod_cast hle
    have hni : (0 : ℝ) < n i := by exact_mod_cast hpos i
    have hx : (0 : ℝ) < (m : ℝ) + (i.val : ℝ) := by linarith
    have h1 := OMA.log_step ((m : ℝ) + (i.val : ℝ)) hx
    have h2 : (1 : ℝ) / ((m : ℝ) + (i.val : ℝ)) ≤ 1 / n i :=
      one_div_le_one_div_of_le hni hle'
    have h3 : (m : ℝ) + ((i.val + 1 : ℕ) : ℝ) = (m : ℝ) + (i.val : ℝ) + 1 := by
      push_cast; ring
    rw [h3]
    linarith
  have hsumle : ∑ i : Fin (k + 1),
      (log ((m : ℝ) + ((i.val + 1 : ℕ) : ℝ)) - log ((m : ℝ) + ((i.val : ℕ) : ℝ))) ≤
        ∑ i : Fin (k + 1), (1 : ℝ) / n i :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have htel : ∑ i : Fin (k + 1),
      (log ((m : ℝ) + ((i.val + 1 : ℕ) : ℝ)) - log ((m : ℝ) + ((i.val : ℕ) : ℝ))) =
        log ((m : ℝ) + ((k + 1 : ℕ) : ℝ)) - log ((m : ℝ) + ((0 : ℕ) : ℝ)) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ => log ((m : ℝ) + ((i + 1 : ℕ) : ℝ)) - log ((m : ℝ) + ((i : ℕ) : ℝ)))
      (k + 1)]
    exact Finset.sum_range_sub (fun i : ℕ => log ((m : ℝ) + ((i : ℕ) : ℝ))) (k + 1)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hlog : log ((m : ℝ) + ((k + 1 : ℕ) : ℝ)) ≤ 1 + log (m : ℝ) := by
    have e0 : (m : ℝ) + ((0 : ℕ) : ℝ) = m := by simp
    rw [htel, e0] at hsumle
    linarith
  have hexp : (m : ℝ) + ((k + 1 : ℕ) : ℝ) ≤ exp 1 * m := by
    have hpos' : (0 : ℝ) < (m : ℝ) + ((k + 1 : ℕ) : ℝ) := by positivity
    calc (m : ℝ) + ((k + 1 : ℕ) : ℝ) = exp (log ((m : ℝ) + ((k + 1 : ℕ) : ℝ))) :=
          (exp_log hpos').symm
      _ ≤ exp (1 + log (m : ℝ)) := exp_le_exp.2 hlog
      _ = exp 1 * m := by rw [exp_add, exp_log hmpos]
  have hmN : (m : ℝ) = (n (Fin.last k) : ℝ) - (k : ℝ) := by
    rw [hm, Nat.cast_sub (by omega)]
  rw [hmN] at hexp
  push_cast at hexp
  nlinarith [hexp]

theorem OMA.solution : type_of% @Erdos285.erdos_285.variants.lb := by
  intro f S hS h
  have he : (1 : ℝ) < exp 1 := by
    have := add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  refine ⟨fun k => (-(exp 1 - 1) / exp 1) / ((k : ℝ) + 1), ?_, ?_⟩
  · show (fun k : ℕ => (-(exp 1 - 1) / exp 1) / ((k : ℝ) + 1)) =o[Filter.atTop]
      (fun _ : ℕ => (1 : ℝ))
    rw [Asymptotics.isLittleO_one_iff]
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (-(exp 1 - 1) / exp 1)
    rw [mul_zero] at h1
    refine h1.congr (fun k => ?_)
    ring
  · intro k hk
    obtain ⟨n, hn, h0, hsum, hlast⟩ := (h k hk).1
    have hkey := OMA.key n hn h0 hsum
    rw [hlast] at hkey
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have he1 : (0 : ℝ) < exp 1 - 1 := by linarith
    have hepos : (0 : ℝ) < exp 1 := by linarith
    have heq : (1 + (-(exp 1 - 1) / exp 1) / ((k : ℝ) + 1)) * exp 1 /
        (exp 1 - 1) * ((k : ℝ) + 1) =
        (exp 1 * ((k : ℝ) + 1) - (exp 1 - 1)) / (exp 1 - 1) := by
      field_simp
      ring
    show (1 + (-(exp 1 - 1) / exp 1) / ((k : ℝ) + 1)) * exp 1 /
        (exp 1 - 1) * ((k : ℝ) + 1) ≤ (f k : ℝ)
    rw [heq, div_le_iff₀ he1]
    linarith

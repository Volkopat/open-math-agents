import FormalConjectures.ErdosProblems.«897»

-- Reduction Erdos897.erdos_897.variants.parts.i.R1 of Erdős Problem 897 (variant, part i)
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 897 (completely additive variant) from Elliott's theorem and a one-sided to two-sided step

The statement asks: if `f` is additive, `f (p ^ k) / log (p ^ k)` is unbounded above, and either
`f (p ^ k) = f p` for all `k` or `f (p ^ k) = k * f p` for all `k`, is
`(f (n + 1) - f n) / log n` unbounded above?

Two remarks on the formal statement.
* The first alternative is vacuous as formalised: `k = 0` gives `f p = f 1 = 0` for every prime,
  so `f (p ^ k) = 0` and the limsup hypothesis fails. Only the completely additive alternative
  `f (p ^ k) = k * f p` carries content.
* For it, the negation of the conclusion says `f (n + 1) - f n ≤ C * log n` for all `n ≥ 2`
  (finitely many exceptions are absorbed into `C`), and the hypothesis says `f p / log p` is
  unbounded above on primes.

Hypotheses.
* `H1` (deep, known): Elliott's theorem, conjectured by Ruzsa (P. D. T. A. Elliott, *Arithmetic
  Functions and Integer Products*, Springer 1985, Theorem 14.1; quoted from A. Hildebrand,
  *Recent progress in probabilistic number theory*, Astérisque 147-148 (1987), 95-106, section 5):
  there is an absolute constant `c` with
  `inf_λ max_{n ≤ N} |f n - λ log n| ≤ c * max_{n ≤ N ^ c} |f (n + 1) - f n|`
  for every additive `f` and every `N ≥ 1`. The infimum is written with an `ε`.
* `H2` (open core): for such `f`, a one-sided bound `f (n + 1) - f n ≤ C * log n` forces a lower
  bound `f (n + 1) - f n ≥ -C' * log n`. This is stronger than the target (given `H1` it is
  equivalent to the target together with the lower bound `f n ≥ -K log n`), so the reduction is
  upward in `H2`.

`main`: under the negated conclusion, `H2` makes the differences two-sided `O(log n)`. For a prime
`p`, `H1` at `N = p` gives `λ` with `|f n - λ log n| ≤ E` for `n ≤ p`, where `E = O(log p)`.
Evaluating at `n = 2 ^ j` with `2 ^ j ≤ p < 2 ^ (j + 1)` (here `f (2 ^ j) = j * f 2`) bounds `λ`
by an absolute constant, and evaluating at `n = p` bounds `f p` by `K * log p`.
-/

namespace OMA.R_Erdos897_erdos_897_variants_parts_i_R1

open Real Filter

/-- Elliott's theorem (Ruzsa's conjecture), Theorem 14.1 of *Arithmetic Functions and Integer
Products* (1985). -/
def H1 : Prop :=
  ∃ c : ℕ, ∀ f : ℕ → ℝ,
    (∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → f (a * b) = f a + f b) →
    ∀ (N : ℕ) (D : ℝ), 1 ≤ N →
      (∀ n : ℕ, 1 ≤ n → n ≤ N ^ c → |f (n + 1) - f n| ≤ D) →
      ∀ ε : ℝ, 0 < ε → ∃ lam : ℝ, ∀ n : ℕ, 1 ≤ n → n ≤ N →
        |f n - lam * Real.log n| ≤ c * D + ε

/-- Open core: for a completely additive function, differences bounded above by `C log n` are
also bounded below by `-C' log n`. -/
def H2 : Prop :=
  ∀ f : ℕ → ℝ,
    (∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → f (a * b) = f a + f b) →
    (∀ k p : ℕ, p.Prime → f (p ^ k) = k * f p) →
    (∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → f (n + 1) - f n ≤ C * Real.log n) →
    ∃ C' : ℝ, ∀ n : ℕ, 2 ≤ n → -(C' * Real.log n) ≤ f (n + 1) - f n

/-- A bound valid from `N₀` on extends to all `n ≥ 2` after enlarging the constant. -/
lemma extend_bound (g : ℕ → ℝ) (C : ℝ) (N₀ : ℕ)
    (h : ∀ n : ℕ, N₀ ≤ n → 2 ≤ n → g n ≤ C * Real.log n) :
    ∃ C₁ : ℝ, ∀ n : ℕ, 2 ≤ n → g n ≤ C₁ * Real.log n := by
  induction N₀ generalizing C with
  | zero => exact ⟨C, fun n hn => h n (Nat.zero_le n) hn⟩
  | succ N ih =>
    refine ih (max C (g N / Real.log N)) ?_
    intro n hn hn2
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
    rcases Nat.eq_or_lt_of_le hn with heq | hlt
    · subst heq
      calc g N = g N / Real.log N * Real.log N := by field_simp
        _ ≤ max C (g N / Real.log N) * Real.log N :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hlog.le
    · calc g n ≤ C * Real.log n := h n hlt hn2
        _ ≤ max C (g N / Real.log N) * Real.log n :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hlog.le

/-- Every prime lies in a dyadic block `2 ^ j ≤ p < 2 ^ (j + 1)` with `j ≥ 1`, and then
`log p < 2 * j * log 2`. -/
lemma dyadic (p : ℕ) (hp : 2 ≤ p) :
    ∃ j : ℕ, 1 ≤ j ∧ 2 ^ j ≤ p ∧ Real.log p < 2 * (j * Real.log 2) := by
  refine ⟨Nat.log 2 p, ?_, Nat.pow_log_le_self 2 (by omega), ?_⟩
  · exact Nat.log_pos (by norm_num) hp
  · have h1 : p < 2 ^ (Nat.log 2 p + 1) := Nat.lt_pow_succ_log_self (by norm_num) p
    have h2 : (p : ℝ) < (2 : ℝ) ^ (Nat.log 2 p + 1) := by exact_mod_cast h1
    have h3 : Real.log p < Real.log ((2 : ℝ) ^ (Nat.log 2 p + 1)) :=
      Real.log_lt_log (by exact_mod_cast (by omega : 0 < p)) h2
    rw [Real.log_pow] at h3
    have hj : (1 : ℝ) ≤ (Nat.log 2 p : ℝ) := by
      exact_mod_cast Nat.log_pos (by norm_num) hp
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    push_cast at h3
    nlinarith

/-- The analytic heart: two-sided `O(log n)` differences plus Elliott's theorem bound `f p`. -/
lemma bound_of_two_sided (h1 : H1) (f : ℕ → ℝ)
    (hadd : ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → f (a * b) = f a + f b)
    (hpow : ∀ k p : ℕ, p.Prime → f (p ^ k) = k * f p)
    (D₀ : ℝ) (hD₀ : 0 ≤ D₀)
    (hD : ∀ n : ℕ, 2 ≤ n → |f (n + 1) - f n| ≤ D₀ * Real.log n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℕ, p.Prime → f p ≤ K * Real.log p := by
  obtain ⟨c, hc⟩ := h1
  have hf1 : f 1 = 0 := by
    have := hadd 1 1 one_pos one_pos (Nat.coprime_one_left 1)
    simp at this
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set A : ℝ := (c : ℝ) * (D₀ * c) with hA
  set B : ℝ := (c : ℝ) * |f 2| + 1 with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  -- E ≤ A * log p + B
  set M : ℝ := (|f 2| + 2 * Real.log 2 * (A + B / Real.log 2)) / Real.log 2 with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M + A + B / Real.log 2, by positivity, ?_⟩
  intro p hp
  have hp2 : 2 ≤ p := hp.two_le
  have hlp : Real.log 2 ≤ Real.log p :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
  have hlp0 : 0 < Real.log p := lt_of_lt_of_le hl2 hlp
  -- hypothesis of Elliott at N = p
  have hdiff : ∀ n : ℕ, 1 ≤ n → n ≤ p ^ c →
      |f (n + 1) - f n| ≤ D₀ * (c * Real.log p) + |f 2| := by
    intro n hn1 hn
    rcases Nat.eq_or_lt_of_le hn1 with h | h
    · subst h
      have : D₀ * (c * Real.log p) ≥ 0 := by positivity
      simp only [hf1, sub_zero]
      norm_num
      linarith
    · have hn2 : 2 ≤ n := h
      have h0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hle : Real.log n ≤ c * Real.log p := by
        have : (n : ℝ) ≤ (p : ℝ) ^ c := by exact_mod_cast hn
        calc Real.log n ≤ Real.log ((p : ℝ) ^ c) := Real.log_le_log h0 this
          _ = c * Real.log p := Real.log_pow _ _
      calc |f (n + 1) - f n| ≤ D₀ * Real.log n := hD n hn2
        _ ≤ D₀ * (c * Real.log p) := mul_le_mul_of_nonneg_left hle hD₀
        _ ≤ D₀ * (c * Real.log p) + |f 2| := le_add_of_nonneg_right (abs_nonneg _)
  obtain ⟨lam, hlam⟩ := hc f hadd p (D₀ * (c * Real.log p) + |f 2|) (by omega) hdiff 1 one_pos
  have hE : (c : ℝ) * (D₀ * (c * Real.log p) + |f 2|) + 1 = A * Real.log p + B := by
    rw [hA, hB]; ring
  rw [hE] at hlam
  obtain ⟨j, hj1, hj2, hj3⟩ := dyadic p hp2
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  -- at n = 2 ^ j
  have e1 := hlam (2 ^ j) (Nat.one_le_two_pow) hj2
  rw [hpow j 2 Nat.prime_two] at e1
  have hlogpow : Real.log ((2 ^ j : ℕ) : ℝ) = j * Real.log 2 := by
    push_cast
    exact Real.log_pow _ _
  rw [hlogpow] at e1
  -- at n = p
  have e2 := hlam p (by omega) le_rfl
  have e1' := (abs_le.mp e1).1
  have e2' := (abs_le.mp e2).2
  -- bound lam: lam * (j log 2) ≤ j f 2 + A log p + B
  have hjl : 0 < (j : ℝ) * Real.log 2 := by positivity
  have hBl : B ≤ B / Real.log 2 * Real.log p := by
    calc B = B / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ B / Real.log 2 * Real.log p :=
        mul_le_mul_of_nonneg_left hlp (by positivity)
  have hf2 : f 2 ≤ |f 2| := le_abs_self _
  -- lam * log 2 ≤ |f 2| + 2 log 2 (A + B / log 2)
  have hlam1 : lam * Real.log 2 ≤ M * Real.log 2 := by
    have hMl : M * Real.log 2 = |f 2| + 2 * Real.log 2 * (A + B / Real.log 2) := by
      rw [hM]; field_simp
    rw [hMl]
    -- from e1': lam * (j log 2) ≤ j f 2 + A log p + B
    have s1 : lam * (j * Real.log 2) ≤ j * f 2 + (A * Real.log p + B) := by linarith
    have s2 : A * Real.log p + B ≤ (A + B / Real.log 2) * Real.log p := by
      rw [add_mul]; linarith
    have s3 : (A + B / Real.log 2) * Real.log p
        ≤ (A + B / Real.log 2) * (2 * (j * Real.log 2)) :=
      mul_le_mul_of_nonneg_left hj3.le (by positivity)
    have s4 : j * (lam * Real.log 2)
        ≤ j * (|f 2| + 2 * Real.log 2 * (A + B / Real.log 2)) := by
      have : (j : ℝ) * f 2 ≤ j * |f 2| := mul_le_mul_of_nonneg_left hf2 hjpos.le
      nlinarith
    exact le_of_mul_le_mul_left s4 hjpos
  have hlamM : lam ≤ M := le_of_mul_le_mul_right hlam1 hl2
  have hlamp : lam * Real.log p ≤ M * Real.log p :=
    mul_le_mul_of_nonneg_right hlamM hlp0.le
  calc f p ≤ lam * Real.log p + (A * Real.log p + B) := by linarith
    _ ≤ M * Real.log p + (A * Real.log p + B / Real.log 2 * Real.log p) := by linarith
    _ = (M + A + B / Real.log 2) * Real.log p := by ring

theorem main : H1 → H2 → type_of% @Erdos897.erdos_897.variants.parts.i := by
  intro h1 h2 f hadd hlim hcase
  by_contra hne
  have hf1 : f 1 = 0 := by
    have := hadd 1 one_pos 1 one_pos (Nat.coprime_one_left 1)
    simp at this
    linarith
  -- unboundedness extracted from the limsup hypothesis
  have hfreq : ∀ K : ℝ, ∃ p k : ℕ, p.Prime ∧
      ((K : ℝ) : EReal) < (f (p ^ k) / Real.log ((p : ℝ) ^ k) : EReal) := by
    intro K
    by_contra hcon
    have hev : ∀ᶠ x : ℕ × ℕ in atTop ⊓ 𝓟 {(p, k) : ℕ × ℕ | p.Prime},
        (f (x.1 ^ x.2) / Real.log ((x.1 : ℝ) ^ x.2) : EReal) ≤ (K : EReal) := by
      have hmem : {(p, k) : ℕ × ℕ | p.Prime} ∈ atTop ⊓ 𝓟 {(p, k) : ℕ × ℕ | p.Prime} :=
        mem_inf_of_right (mem_principal_self _)
      filter_upwards [hmem] with x hx
      by_contra hlt
      exact hcon ⟨x.1, x.2, hx, not_le.mp hlt⟩
    have := Filter.limsup_le_of_le (h := hev)
    rw [hlim] at this
    exact absurd this (by simp)
  have hpowcase : ∀ k p : ℕ, p.Prime → f (p ^ k) = k * f p := by
    rcases hcase with hc | hc
    · exfalso
      obtain ⟨p, k, hp, hlt⟩ := hfreq 0
      have h0 : f (p ^ k) = 0 := by
        rw [hc k p hp, ← hc 0 p hp, pow_zero, hf1]
      rw [h0] at hlt
      simp at hlt
    · exact hc
  have hunb : ∀ K : ℝ, 0 ≤ K → ∃ p : ℕ, p.Prime ∧ K * Real.log p < f p := by
    intro K hK
    obtain ⟨p, k, hp, hlt⟩ := hfreq K
    refine ⟨p, hp, ?_⟩
    have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    rw [hpowcase k p hp, Real.log_pow] at hlt
    rw [← EReal.coe_div] at hlt
    have hlt' : K < (k * f p) / (k * Real.log p) := by exact_mod_cast hlt
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp at hlt'
      linarith
    · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      have : (k * f p) / (k * Real.log p) = f p / Real.log p := by
        field_simp
      rw [this, lt_div_iff₀ hlp] at hlt'
      exact hlt'
  -- the negated conclusion gives a one-sided bound
  have hlt : Filter.atTop.limsup
      (fun n : ℕ => ((f (n + 1) - f n) / (n : ℝ).log : EReal)) < ⊤ := lt_top_iff_ne_top.mpr hne
  obtain ⟨C, hC1, -⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have hev := Filter.eventually_lt_of_limsup_lt hC1
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  have hone : ∀ n : ℕ, N₀ ≤ n → 2 ≤ n → f (n + 1) - f n ≤ C * Real.log n := by
    intro n hn hn2
    have h := hN₀ n hn
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
    rw [← EReal.coe_sub, ← EReal.coe_div] at h
    have h' : (f (n + 1) - f n) / Real.log n < C := by exact_mod_cast h
    rw [div_lt_iff₀ hlog] at h'
    exact h'.le
  obtain ⟨C₁, hC₁⟩ := extend_bound (fun n => f (n + 1) - f n) C N₀ hone
  have hadd' : ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b → f (a * b) = f a + f b :=
    fun a b ha hb hab => hadd a ha b hb hab
  obtain ⟨C₂, hC₂⟩ := h2 f hadd' hpowcase ⟨C₁, hC₁⟩
  have htwo : ∀ n : ℕ, 2 ≤ n → |f (n + 1) - f n| ≤ (|C₁| + |C₂|) * Real.log n := by
    intro n hn
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have u := hC₁ n hn
    have l := hC₂ n hn
    have u1 : C₁ * Real.log n ≤ |C₁| * Real.log n :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hlog.le
    have l1 : C₂ * Real.log n ≤ |C₂| * Real.log n :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hlog.le
    have a1 : 0 ≤ |C₁| * Real.log n := by positivity
    have a2 : 0 ≤ |C₂| * Real.log n := by positivity
    rw [abs_le]
    constructor <;> nlinarith
  obtain ⟨K, hK0, hK⟩ := bound_of_two_sided h1 f hadd' hpowcase (|C₁| + |C₂|) (by positivity) htwo
  obtain ⟨p, hp, hlt⟩ := hunb K hK0
  exact absurd (hK p hp) (not_le.mpr hlt)

end OMA.R_Erdos897_erdos_897_variants_parts_i_R1

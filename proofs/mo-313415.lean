import OMAStatements.S_mo_313415

-- Problem: Asymptotic behavior of row sums in 2-d array of random variables
-- (https://mathoverflow.net/questions/313415).
-- Credit: @ricnov (the owner of the agent is credited as the solver)
--
-- Answer: yes. With f(n) = (n + 1)^3 * ceil((32/27)^(n/3 + 1)) agents on day n, the proportion
-- m = 1/2 does best: it does better than every other m' in [0, 1], whatever the joint distribution
-- of the arrays. (An exponential number of agents, of rate (1/3) log(32/27), makes the largest
-- number of wins in a row about 2n/3, and 1/2 is the proportion that is best for an agent who
-- wins two bets out of three.)
--
-- Proof. Write t = n/3 (integer division) and compare both row sums with the threshold 2^t.
--
-- Lower bound for m = 1/2 (OMA.half_low). An agent with at least n - t wins has bankroll
-- 2^k (1/2)^(n-k) >= 2^t. One agent has exactly n - t wins with probability
-- p = binom(n, t) / 2^n >= (27/32)^t / (4 (n + 1)), by (27/4)^t <= (3t + 1) binom(3t, t)
-- (OMA.choose_lower, by induction). By independence no agent has n - t wins with probability at
-- most (1 - p)^f(n) <= 1 / (1 + f(n) p) <= 4 / (n + 1).
--
-- Upper bound for m' != 1/2 (OMA.upper_all), by a first moment bound for the row sum restricted
-- to the agents with at most L wins (OMA.RowLaw.sum_ge_le), where the binomial sums are
-- estimated with sum_k binom(n, k) 2^k = 3^n.
-- * m' <= 1/4: L = n; the expected row sum is f(n) (1 + m'/2)^n <= f(n) (9/8)^n, and
--   (32/27) (9/8)^3 / 2 = 27/32 < 1.
-- * m' = 1: L = n - 1; the row sum is 0 unless some agent wins all n bets.
-- * 1/4 <= m' < 1: L = n - t + j with j = t/q. Some agent has more than L wins with probability
--   at most a constant times (n + 1)^3 / 2^j, and the restricted first moment divided by 2^t is at
--   most a constant times (n + 1)^3 rho^t R^j, where rho = (1 + 2m')^2 (1 - m') / 2 and
--   R = (1 + 2m') / (2 (1 - m')). Since 2 - (1 + 2m')^2 (1 - m') = (2m' - 1)^2 (m' + 1), rho < 1
--   for m' != 1/2, and q is chosen with R rho^q < 1 (OMA.exists_q).
-- All the bounds are of the form polynomial times geometric along n/d (OMA.tendsto_poly_geom).

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace OMA

/-- The number of agents on day `n`. -/
noncomputable def ff (n : ℕ) : ℕ := (n + 1) ^ 3 * ⌈((32 : ℝ) / 27) ^ (n / 3 + 1)⌉₊

lemma ff_strictMono : StrictMono ff := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  unfold ff
  have h1 : (n + 1) ^ 3 < (n + 1 + 1) ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have h2 : ⌈((32 : ℝ) / 27) ^ (n / 3 + 1)⌉₊ ≤ ⌈((32 : ℝ) / 27) ^ ((n + 1) / 3 + 1)⌉₊ := by
    apply Nat.ceil_mono
    apply pow_le_pow_right₀ (by norm_num)
    have := Nat.div_le_div_right (c := 3) (Nat.le_succ n)
    omega
  have h3 : 0 < ⌈((32 : ℝ) / 27) ^ (n / 3 + 1)⌉₊ := Nat.ceil_pos.2 (by positivity)
  exact Nat.mul_lt_mul_of_lt_of_le' h1 h2 h3

lemma ff_ge (n : ℕ) : ((n : ℝ) + 1) ^ 3 * ((32 : ℝ) / 27) ^ (n / 3 + 1) ≤ (ff n : ℝ) := by
  unfold ff
  push_cast
  have h := Nat.le_ceil (((32 : ℝ) / 27) ^ (n / 3 + 1))
  have hn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by positivity
  exact mul_le_mul_of_nonneg_left h hn

lemma ff_le (n : ℕ) : (ff n : ℝ) ≤ 2 * ((n : ℝ) + 1) ^ 3 * ((32 : ℝ) / 27) ^ (n / 3 + 1) := by
  unfold ff
  push_cast
  have hx : (1 : ℝ) ≤ ((32 : ℝ) / 27) ^ (n / 3 + 1) := one_le_pow₀ (by norm_num)
  have h := Nat.ceil_lt_add_one (le_trans zero_le_one hx)
  have hn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by positivity
  have h2 : (⌈((32 : ℝ) / 27) ^ (n / 3 + 1)⌉₊ : ℝ) ≤ 2 * ((32 : ℝ) / 27) ^ (n / 3 + 1) := by linarith
  calc ((n : ℝ) + 1) ^ 3 * (⌈((32 : ℝ) / 27) ^ (n / 3 + 1)⌉₊ : ℝ)
      ≤ ((n : ℝ) + 1) ^ 3 * (2 * ((32 : ℝ) / 27) ^ (n / 3 + 1)) := mul_le_mul_of_nonneg_left h2 hn
    _ = 2 * ((n : ℝ) + 1) ^ 3 * ((32 : ℝ) / 27) ^ (n / 3 + 1) := by ring

/-- `binom(3t+3, t+1) (t+1)(2t+1)(2t+2) = binom(3t, t) (3t+1)(3t+2)(3t+3)`. -/
lemma choose_step (t : ℕ) :
    ((3 * (t + 1)).choose (t + 1) : ℝ) * (((t : ℝ) + 1) * (2 * t + 1) * (2 * t + 2))
      = ((3 * t).choose t : ℝ) * ((3 * (t : ℝ) + 1) * (3 * t + 2) * (3 * t + 3)) := by
  have h1 : (3 * t + 1) * (3 * t).choose t = (3 * t + 1).choose (t + 1) * (t + 1) :=
    Nat.add_one_mul_choose_eq (3 * t) t
  have h2 : (3 * t + 1).choose (t + 1) * (3 * t + 1 + 1)
      = (3 * t + 1 + 1).choose (t + 1) * (3 * t + 1 + 1 - (t + 1)) :=
    Nat.choose_mul_succ_eq (3 * t + 1) (t + 1)
  have h3 : (3 * t + 2).choose (t + 1) * (3 * t + 2 + 1)
      = (3 * t + 2 + 1).choose (t + 1) * (3 * t + 2 + 1 - (t + 1)) :=
    Nat.choose_mul_succ_eq (3 * t + 2) (t + 1)
  have e2 : 3 * t + 1 + 1 - (t + 1) = 2 * t + 1 := by omega
  have e3 : 3 * t + 2 + 1 - (t + 1) = 2 * t + 2 := by omega
  rw [e2] at h2
  rw [e3] at h3
  have e4 : 3 * (t + 1) = 3 * t + 2 + 1 := by ring
  rw [e4]
  have h1' : (3 * (t : ℝ) + 1) * ((3 * t).choose t : ℝ)
      = ((3 * t + 1).choose (t + 1) : ℝ) * ((t : ℝ) + 1) := by exact_mod_cast h1
  have h2' : ((3 * t + 1).choose (t + 1) : ℝ) * (3 * (t : ℝ) + 1 + 1)
      = ((3 * t + 1 + 1).choose (t + 1) : ℝ) * (2 * (t : ℝ) + 1) := by exact_mod_cast h2
  have h3' : ((3 * t + 2).choose (t + 1) : ℝ) * (3 * (t : ℝ) + 2 + 1)
      = ((3 * t + 2 + 1).choose (t + 1) : ℝ) * (2 * (t : ℝ) + 2) := by exact_mod_cast h3
  have e5 : 3 * t + 1 + 1 = 3 * t + 2 := by ring
  rw [e5] at h2'
  linear_combination (-(2 * (t : ℝ) + 1) * ((t : ℝ) + 1)) * h3' - ((3 * (t : ℝ) + 3) * ((t : ℝ) + 1)) * h2'
    - ((3 * (t : ℝ) + 2) * (3 * (t : ℝ) + 3)) * h1'

/-- `(27/4)^t ≤ (3t+1) binom(3t, t)`. -/
lemma choose_lower (t : ℕ) : ((27 : ℝ) / 4) ^ t ≤ (3 * (t : ℝ) + 1) * ((3 * t).choose t : ℝ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hs := choose_step t
    have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    have hc : (0 : ℝ) ≤ ((3 * t).choose t : ℝ) := Nat.cast_nonneg _
    have hD : (0 : ℝ) < ((t : ℝ) + 1) * (2 * t + 1) * (2 * t + 2) := by positivity
    have hpoly : ((27 : ℝ) / 4) * (((t : ℝ) + 1) * (2 * t + 1) * (2 * t + 2))
        ≤ (3 * (t : ℝ) + 4) * (3 * t + 2) * (3 * t + 3) := by
      nlinarith [mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht]
    have hpow : ((27 : ℝ) / 4) ^ (t + 1) = ((27 : ℝ) / 4) ^ t * (27 / 4) := pow_succ _ _
    refine le_of_mul_le_mul_right ?_ hD
    push_cast
    calc ((27 : ℝ) / 4) ^ (t + 1) * (((t : ℝ) + 1) * (2 * t + 1) * (2 * t + 2))
        = ((27 : ℝ) / 4) ^ t * ((27 / 4) * (((t : ℝ) + 1) * (2 * t + 1) * (2 * t + 2))) := by
          rw [hpow]; ring
      _ ≤ ((3 * (t : ℝ) + 1) * ((3 * t).choose t : ℝ)) * ((3 * (t : ℝ) + 4) * (3 * t + 2) * (3 * t + 3)) := by
          apply mul_le_mul ih hpoly (by positivity) (by positivity)
      _ = (3 * ((t : ℝ) + 1) + 1) * (((3 * (t + 1)).choose (t + 1) : ℝ) * (((t : ℝ) + 1) * (2 * t + 1) * (2 * t + 2))) := by
          rw [hs]; ring
      _ = (3 * ((t : ℝ) + 1) + 1) * ((3 * (t + 1)).choose (t + 1) : ℝ) * (((t : ℝ) + 1) * (2 * t + 1) * (2 * t + 2)) := by
          ring

/-- A polynomial times a geometric sequence along `n / d` tends to `0`. -/
lemma tendsto_poly_geom (c d : ℕ) (hd : 0 < d) (σ : ℝ) (h0 : 0 ≤ σ) (h1 : σ < 1) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ c * σ ^ (n / d)) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun n : ℕ => n / d) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨b * d, fun n hn => ?_⟩
    exact (Nat.le_div_iff_mul_le hd).2 hn
  have hbase : Tendsto (fun s : ℕ => ((2 * (d : ℝ)) ^ c) * ((s : ℝ) ^ c * σ ^ s)) atTop (𝓝 0) := by
    have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one c (r := σ)
      (by rw [abs_of_nonneg h0]; exact h1)
    simpa using h.const_mul ((2 * (d : ℝ)) ^ c)
  have hcomp := hbase.comp hdiv
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hcomp
  filter_upwards [eventually_ge_atTop d] with n hn
  have hs1 : 1 ≤ n / d := (Nat.le_div_iff_mul_le hd).2 (by simpa using hn)
  have hlt : n < d * (n / d) + d := by
    have := Nat.lt_div_mul_add (a := n) hd
    rw [Nat.mul_comm] at this
    exact this
  have hle : (n : ℝ) + 1 ≤ 2 * (d : ℝ) * ((n / d : ℕ) : ℝ) := by
    have h1' : n + 1 ≤ d * (n / d) + d := hlt
    have h2' : d * (n / d) + d ≤ 2 * d * (n / d) := by nlinarith
    exact_mod_cast le_trans h1' h2'
  have hσ : (0 : ℝ) ≤ σ ^ (n / d) := pow_nonneg h0 _
  calc ((n : ℝ) + 1) ^ c * σ ^ (n / d)
      ≤ (2 * (d : ℝ) * ((n / d : ℕ) : ℝ)) ^ c * σ ^ (n / d) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hle c) hσ
    _ = (2 * (d : ℝ)) ^ c * ((((n / d : ℕ) : ℝ)) ^ c * σ ^ (n / d)) := by rw [mul_pow]; ring


/-- `∑_k binom(n, k) / 2^n = 1`. -/
lemma sum_pmf (n : ℕ) : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) / 2 ^ n = 1 := by
  rw [← Finset.sum_div]
  have h : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [h]
  exact div_self (by positivity)

/-- The law of one row: independent variables, each with the law `Bin(n, 1/2)`. -/
def RowLaw {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (n N : ℕ) (X : Fin N → Ω → ℕ) : Prop :=
  (∀ i, Measurable (X i)) ∧ iIndepFun X P ∧
    ∀ i k, P {ω | X i ω = k} = (n.choose k : ℝ≥0∞) / 2 ^ n

lemma RowLaw.meas_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {n N : ℕ}
    {X : Fin N → Ω → ℕ} (h : RowLaw P n N X) (i : Fin N) (k : ℕ) :
    MeasurableSet {ω | X i ω = k} :=
  (h.1 i) (measurableSet_singleton k)

lemma RowLaw.real_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {n N : ℕ}
    {X : Fin N → Ω → ℕ} (h : RowLaw P n N X) (i : Fin N) (k : ℕ) :
    P.real {ω | X i ω = k} = (n.choose k : ℝ) / 2 ^ n := by
  rw [measureReal_def, h.2.2 i k]
  simp

lemma RowLaw.real_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n N : ℕ} {X : Fin N → Ω → ℕ} (h : RowLaw P n N X) (i : Fin N) (L : ℕ) :
    P.real {ω | X i ω ≤ L} = ∑ k ∈ Finset.range (L + 1), (n.choose k : ℝ) / 2 ^ n := by
  have hset : {ω | X i ω ≤ L} = X i ⁻¹' (Finset.range (L + 1) : Set ℕ) := by
    ext ω
    simp
  rw [hset, ← sum_measureReal_preimage_singleton (Finset.range (L + 1))
    (fun k _ => h.meas_eq i k)]
  exact Finset.sum_congr rfl fun k _ => h.real_eq i k

lemma RowLaw.real_gt {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n N : ℕ} {X : Fin N → Ω → ℕ} (h : RowLaw P n N X) (i : Fin N) (L : ℕ) :
    P.real {ω | L < X i ω} = 1 - ∑ k ∈ Finset.range (L + 1), (n.choose k : ℝ) / 2 ^ n := by
  have hset : {ω | L < X i ω} = {ω | X i ω ≤ L}ᶜ := by
    ext ω
    simp
  have hm : MeasurableSet {ω | X i ω ≤ L} := (h.1 i) (measurableSet_Iic (a := L))
  rw [hset, probReal_compl_eq_one_sub hm, h.real_le i L]

/-- Independence: the probability that no agent reaches `k0` wins. -/
lemma RowLaw.all_lt_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n N : ℕ} {X : Fin N → Ω → ℕ} (h : RowLaw P n N X) (k0 : ℕ) :
    P.real {ω | ∀ i, X i ω < k0} ≤ (1 - (n.choose k0 : ℝ) / 2 ^ n) ^ N := by
  have hsub : {ω | ∀ i, X i ω < k0} ⊆ ⋂ i, (X i ⁻¹' {k0}ᶜ) := by
    intro ω hω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro i
    exact (hω i).ne
  have hind : P (⋂ i, (X i ⁻¹' {k0}ᶜ)) = ∏ i, P (X i ⁻¹' {k0}ᶜ) :=
    h.2.1.meas_iInter fun i => ⟨{k0}ᶜ, (measurableSet_singleton k0).compl, rfl⟩
  have hreal : P.real (⋂ i, (X i ⁻¹' {k0}ᶜ)) = ∏ i : Fin N, P.real (X i ⁻¹' {k0}ᶜ) := by
    simp only [measureReal_def, hind, ENNReal.toReal_prod]
  have hone : ∀ i : Fin N, P.real (X i ⁻¹' {k0}ᶜ) = 1 - (n.choose k0 : ℝ) / 2 ^ n := by
    intro i
    have hc : X i ⁻¹' {k0}ᶜ = {ω | X i ω = k0}ᶜ := rfl
    rw [hc, probReal_compl_eq_one_sub (h.meas_eq i k0), h.real_eq i k0]
  calc P.real {ω | ∀ i, X i ω < k0} ≤ P.real (⋂ i, (X i ⁻¹' {k0}ᶜ)) := measureReal_mono hsub
    _ = ∏ i : Fin N, P.real (X i ⁻¹' {k0}ᶜ) := hreal
    _ = (1 - (n.choose k0 : ℝ) / 2 ^ n) ^ N := by
        simp only [hone, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- First moment bound for the row sum of `W (X i)`, truncated at `L` wins. -/
lemma RowLaw.sum_ge_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n N : ℕ} {X : Fin N → Ω → ℕ} (h : RowLaw P n N X) (W : ℕ → ℝ) (hW : ∀ k, 0 ≤ W k) (L : ℕ) (a : ℝ)
    (ha : 0 < a) :
    P.real {ω | a ≤ ∑ i, W (X i ω)} ≤
      N * (1 - ∑ k ∈ Finset.range (L + 1), (n.choose k : ℝ) / 2 ^ n)
        + N * (∑ k ∈ Finset.range (L + 1), (n.choose k : ℝ) / 2 ^ n * W k) / a := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Ω → ℝ, T = fun ω => ∑ i, ∑ k ∈ Finset.range (L + 1),
      ({ω | X i ω = k}).indicator (fun _ => W k) ω := ⟨_, rfl⟩
  have hTeq : ∀ ω, (∀ i, X i ω ≤ L) → ∑ i, W (X i ω) = T ω := by
    intro ω hω
    rw [hT]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (X i ω)]
    · simp
    · intro k _ hk
      have : ω ∉ {ω | X i ω = k} := fun hmem => hk hmem.symm
      simp [Set.indicator_of_notMem this]
    · intro hnot
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (hω i))) hnot
  have hsub : {ω | a ≤ ∑ i, W (X i ω)} ⊆ (⋃ i, {ω | L < X i ω}) ∪ {ω | a ≤ T ω} := by
    intro ω hω
    by_cases hall : ∀ i, X i ω ≤ L
    · right
      show a ≤ T ω
      rw [← hTeq ω hall]
      exact hω
    · left
      obtain ⟨i, hi⟩ := not_forall.1 hall
      exact Set.mem_iUnion.2 ⟨i, not_le.1 hi⟩
  have hunion : P.real (⋃ i, {ω | L < X i ω})
      ≤ N * (1 - ∑ k ∈ Finset.range (L + 1), (n.choose k : ℝ) / 2 ^ n) := by
    calc P.real (⋃ i, {ω | L < X i ω}) ≤ ∑ i : Fin N, P.real {ω | L < X i ω} :=
          measureReal_iUnion_fintype_le _
      _ = ∑ _i : Fin N, (1 - ∑ k ∈ Finset.range (L + 1), (n.choose k : ℝ) / 2 ^ n) :=
          Finset.sum_congr rfl fun i _ => h.real_gt i L
      _ = N * (1 - ∑ k ∈ Finset.range (L + 1), (n.choose k : ℝ) / 2 ^ n) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hint_term : ∀ (i : Fin N) (k : ℕ),
      Integrable (({ω | X i ω = k}).indicator (fun _ => W k)) P :=
    fun i k => (integrable_const _).indicator (h.meas_eq i k)
  have hTint : Integrable T P := by
    rw [hT]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hint_term i k
  have hTnn : 0 ≤ᵐ[P] T := by
    rw [hT]
    exact Eventually.of_forall fun ω => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun k _ => Set.indicator_nonneg (fun _ _ => hW k) ω
  have hinner : ∀ i : Fin N, ∫ ω, ∑ k ∈ Finset.range (L + 1),
      ({ω | X i ω = k}).indicator (fun _ => W k) ω ∂P
        = ∑ k ∈ Finset.range (L + 1), (n.choose k : ℝ) / 2 ^ n * W k := by
    intro i
    rw [integral_finsetSum _ fun k _ => hint_term i k]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_indicator_const _ (h.meas_eq i k), h.real_eq i k, smul_eq_mul]
  have hTintegral : ∫ ω, T ω ∂P
      = N * ∑ k ∈ Finset.range (L + 1), (n.choose k : ℝ) / 2 ^ n * W k := by
    rw [hT]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hint_term i k]
    simp [hinner]
  have hmarkov : a * P.real {ω | a ≤ T ω} ≤ ∫ ω, T ω ∂P :=
    mul_meas_ge_le_integral_of_nonneg hTnn hTint a
  have hT' : P.real {ω | a ≤ T ω}
      ≤ N * (∑ k ∈ Finset.range (L + 1), (n.choose k : ℝ) / 2 ^ n * W k) / a := by
    rw [le_div_iff₀ ha, mul_comm]
    rw [hTintegral] at hmarkov
    exact hmarkov
  calc P.real {ω | a ≤ ∑ i, W (X i ω)}
      ≤ P.real ((⋃ i, {ω | L < X i ω}) ∪ {ω | a ≤ T ω}) := measureReal_mono hsub
    _ ≤ P.real (⋃ i, {ω | L < X i ω}) + P.real {ω | a ≤ T ω} := measureReal_union_le _ _
    _ ≤ _ := add_le_add hunion hT'


/-- `∑_k binom(n, k) 2^k = 3^n`. -/
lemma sum_choose_two (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * 2 ^ k) = 3 ^ n := by
  have h := add_pow (2 : ℝ) 1 n
  simp only [one_pow, mul_one] at h
  have h3 : (2 : ℝ) + 1 = 3 := by norm_num
  rw [h3] at h
  rw [h]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Upper tail of the law `Bin(n, 1/2)`. -/
lemma tail_le (n L : ℕ) (hL : L ≤ n) :
    1 - ∑ k ∈ Finset.range (L + 1), (n.choose k : ℝ) / 2 ^ n
      ≤ ((3 : ℝ) / 2) ^ n / 2 ^ (L + 1) := by
  have hsplit := Finset.sum_range_add_sum_Ico (fun k => (n.choose k : ℝ) / 2 ^ n)
    (Nat.succ_le_succ hL)
  rw [sum_pmf n] at hsplit
  have h1 : 1 - ∑ k ∈ Finset.range (L + 1), (n.choose k : ℝ) / 2 ^ n
      = ∑ k ∈ Finset.Ico (L + 1) (n + 1), (n.choose k : ℝ) / 2 ^ n := by linarith
  rw [h1]
  calc ∑ k ∈ Finset.Ico (L + 1) (n + 1), (n.choose k : ℝ) / 2 ^ n
      ≤ ∑ k ∈ Finset.Ico (L + 1) (n + 1), (n.choose k : ℝ) * 2 ^ k / (2 ^ n * 2 ^ (L + 1)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : L + 1 ≤ k := (Finset.mem_Ico.1 hk).1
        have hpow : (2 : ℝ) ^ (L + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk'
        have hc : (0 : ℝ) ≤ (n.choose k : ℝ) := Nat.cast_nonneg _
        have h2n : (0 : ℝ) < 2 ^ n := by positivity
        rw [div_le_div_iff₀ h2n (by positivity)]
        have := mul_le_mul_of_nonneg_left hpow (mul_nonneg hc h2n.le)
        linarith
    _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * 2 ^ k / (2 ^ n * 2 ^ (L + 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact Finset.mem_range.2 (Finset.mem_Ico.1 hk).2
        · intro k _ _
          positivity
    _ = 3 ^ n / (2 ^ n * 2 ^ (L + 1)) := by rw [← Finset.sum_div, sum_choose_two]
    _ = ((3 : ℝ) / 2) ^ n / 2 ^ (L + 1) := by rw [div_pow, div_div]

lemma pow_shift (n k d : ℕ) (h : k + d ≤ n) (u v : ℝ) (hv : 0 ≤ v) (huv : 2 * v ≤ u) :
    u ^ k * v ^ (n - k) * 2 ^ (k + d) ≤ u ^ (k + d) * v ^ (n - (k + d)) * 2 ^ k := by
  have hu : 0 ≤ u := by linarith
  have e1 : n - k = (n - (k + d)) + d := by omega
  have hpw : (2 * v) ^ d ≤ u ^ d := pow_le_pow_left₀ (by positivity) huv d
  have hnn : 0 ≤ u ^ k * v ^ (n - (k + d)) * 2 ^ k := by positivity
  calc u ^ k * v ^ (n - k) * 2 ^ (k + d)
      = u ^ k * v ^ (n - (k + d)) * 2 ^ k * (2 * v) ^ d := by
        rw [e1, pow_add, pow_add, mul_pow]
        ring
    _ ≤ u ^ k * v ^ (n - (k + d)) * 2 ^ k * u ^ d := mul_le_mul_of_nonneg_left hpw hnn
    _ = u ^ (k + d) * v ^ (n - (k + d)) * 2 ^ k := by
        rw [pow_add]
        ring

/-- First moment of the bankroll over the outcomes with at most `L` wins, for `u ≥ 2 v`. -/
lemma moment_le (n L : ℕ) (hL : L ≤ n) (u v : ℝ) (hv : 0 ≤ v) (huv : 2 * v ≤ u) :
    ∑ k ∈ Finset.range (L + 1), (n.choose k : ℝ) / 2 ^ n * (u ^ k * v ^ (n - k))
      ≤ u ^ L * v ^ (n - L) * ((3 : ℝ) / 2) ^ n / 2 ^ L := by
  have hu : 0 ≤ u := by linarith
  have hconst : 0 ≤ u ^ L * v ^ (n - L) / (2 ^ n * 2 ^ L) := by positivity
  calc ∑ k ∈ Finset.range (L + 1), (n.choose k : ℝ) / 2 ^ n * (u ^ k * v ^ (n - k))
      ≤ ∑ k ∈ Finset.range (L + 1),
          (n.choose k : ℝ) * 2 ^ k * (u ^ L * v ^ (n - L) / (2 ^ n * 2 ^ L)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkL : k ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkL
        have key := pow_shift n k d hL u v hv huv
        have hc : (0 : ℝ) ≤ (n.choose k : ℝ) := Nat.cast_nonneg _
        have hden : (0 : ℝ) < 2 ^ n * 2 ^ (k + d) := by positivity
        calc (n.choose k : ℝ) / 2 ^ n * (u ^ k * v ^ (n - k))
            = (n.choose k : ℝ) * (u ^ k * v ^ (n - k) * 2 ^ (k + d)) / (2 ^ n * 2 ^ (k + d)) := by
              field_simp
          _ ≤ (n.choose k : ℝ) * (u ^ (k + d) * v ^ (n - (k + d)) * 2 ^ k)
                / (2 ^ n * 2 ^ (k + d)) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left key hc) hden.le
          _ = (n.choose k : ℝ) * 2 ^ k
                * (u ^ (k + d) * v ^ (n - (k + d)) / (2 ^ n * 2 ^ (k + d))) := by ring
    _ ≤ ∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * 2 ^ k * (u ^ L * v ^ (n - L) / (2 ^ n * 2 ^ L)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hk) (Nat.succ_le_succ hL))
        · intro k _ _
          have hc : (0 : ℝ) ≤ (n.choose k : ℝ) := Nat.cast_nonneg _
          positivity
    _ = 3 ^ n * (u ^ L * v ^ (n - L) / (2 ^ n * 2 ^ L)) := by
        rw [← Finset.sum_mul, sum_choose_two]
    _ = u ^ L * v ^ (n - L) * ((3 : ℝ) / 2) ^ n / 2 ^ L := by
        rw [div_pow]
        field_simp

/-- First moment of the bankroll over all outcomes. -/
lemma moment_all (n : ℕ) (u v : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) / 2 ^ n * (u ^ k * v ^ (n - k))
      = ((u + v) / 2) ^ n := by
  rw [div_pow, add_pow, Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma Q_le (n j : ℕ) :
    ((3 : ℝ) / 2) ^ n / 2 ^ (n - n / 3 + j) ≤ ((27 : ℝ) / 32) ^ (n / 3) * (1 / 2) ^ j := by
  have ht : 3 * (n / 3) ≤ n := Nat.mul_div_le n 3
  generalize n / 3 = t at *
  have h1 : (2 : ℝ) ^ (n - t + j) * 2 ^ t = 2 ^ n * 2 ^ j := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h2 : ((3 : ℝ) / 4) ^ n ≤ ((27 : ℝ) / 64) ^ t := by
    calc ((3 : ℝ) / 4) ^ n ≤ ((3 : ℝ) / 4) ^ (3 * t) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) ht
      _ = ((27 : ℝ) / 64) ^ t := by
          rw [pow_mul]
          norm_num
  have e2 : ((1 : ℝ) / 2) ^ j * 2 ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  have e3 : ((27 : ℝ) / 64) ^ t * 2 ^ t = (27 / 32) ^ t := by
    rw [← mul_pow]
    norm_num
  have e4 : ((3 : ℝ) / 2) ^ n = (3 / 4) ^ n * 2 ^ n := by
    rw [← mul_pow]
    norm_num
  rw [div_le_iff₀ (by positivity)]
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 2 ^ t)
  calc ((3 : ℝ) / 2) ^ n * 2 ^ t = (3 / 4) ^ n * 2 ^ t * 2 ^ n := by
        rw [e4]
        ring
    _ ≤ (27 / 64) ^ t * 2 ^ t * 2 ^ n := by
        have hnn : (0 : ℝ) ≤ 2 ^ t * 2 ^ n := by positivity
        have := mul_le_mul_of_nonneg_right h2 hnn
        linarith
    _ = (27 / 32) ^ t * 2 ^ n := by rw [e3]
    _ = (27 / 32) ^ t * 2 ^ n * ((1 / 2) ^ j * 2 ^ j) := by rw [e2, mul_one]
    _ = (27 / 32) ^ t * (1 / 2) ^ j * (2 ^ n * 2 ^ j) := by ring
    _ = (27 / 32) ^ t * (1 / 2) ^ j * (2 ^ (n - t + j) * 2 ^ t) := by rw [h1]
    _ = (27 / 32) ^ t * (1 / 2) ^ j * 2 ^ (n - t + j) * 2 ^ t := by ring

lemma bankroll_nonneg (m : ℝ) (hm : m ∈ Set.Icc (0 : ℝ) 1) (n k : ℕ) :
    0 ≤ OMA.S_mo_313415.bankroll m n k := by
  unfold OMA.S_mo_313415.bankroll
  have h1 : 0 ≤ 1 + 2 * m := by linarith [hm.1]
  have h2 : 0 ≤ 1 - m := by linarith [hm.2]
  positivity

lemma half_bankroll_ge (n k : ℕ) (hk : n - n / 3 ≤ k) :
    (2 : ℝ) ^ (n / 3) ≤ OMA.S_mo_313415.bankroll (1 / 2) n k := by
  have ht3 : 3 * (n / 3) ≤ n := Nat.mul_div_le n 3
  unfold OMA.S_mo_313415.bankroll
  have e1 : (1 : ℝ) + 2 * (1 / 2) = 2 := by norm_num
  have e2 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [e1, e2]
  have h1 : (2 : ℝ) ^ (2 * (n / 3)) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : ((1 : ℝ) / 2) ^ (n / 3) ≤ (1 / 2) ^ (n - k) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc (2 : ℝ) ^ (n / 3) = 2 ^ (2 * (n / 3)) * (1 / 2) ^ (n / 3) := by
        rw [two_mul, pow_add, mul_assoc, ← mul_pow]
        norm_num
    _ ≤ 2 ^ k * (1 / 2) ^ (n - k) := mul_le_mul h1 h2 (by positivity) (by positivity)

lemma one_sub_pow_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    (1 - p) ^ N ≤ 1 / (1 + N * p) := by
  have h1 : 1 + (N : ℝ) * p ≤ (1 + p) ^ N := one_add_mul_le_pow (by linarith) N
  have h2 : (1 - p) ^ N * (1 + p) ^ N ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hpos : 0 < 1 + (N : ℝ) * p := by positivity
  rw [le_div_iff₀ hpos]
  calc (1 - p) ^ N * (1 + N * p) ≤ (1 - p) ^ N * (1 + p) ^ N :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith) N)
    _ ≤ 1 := h2

lemma Np_lower (n : ℕ) :
    ((n : ℝ) + 1) / 4 ≤ (ff n : ℝ) * ((n.choose (n - n / 3) : ℝ) / 2 ^ n) := by
  have ht3 : 3 * (n / 3) ≤ n := Nat.mul_div_le n 3
  have ht3' : n ≤ 3 * (n / 3) + 2 := by omega
  have htn : n / 3 ≤ n := Nat.div_le_self n 3
  have hff := ff_ge n
  generalize n / 3 = t at *
  have hsymm : n.choose (n - t) = n.choose t := Nat.choose_symm htn
  have hmono : (3 * t).choose t ≤ n.choose t := Nat.choose_le_choose t ht3
  have hlow := choose_lower t
  have h2n : (2 : ℝ) ^ n ≤ 4 * 8 ^ t := by
    calc (2 : ℝ) ^ n ≤ 2 ^ (3 * t + 2) := pow_le_pow_right₀ (by norm_num) ht3'
      _ = 4 * 8 ^ t := by
          rw [pow_add, pow_mul]
          norm_num
          ring
  have hab : ((32 : ℝ) / 27) ^ t * (27 / 4) ^ t = 8 ^ t := by
    rw [← mul_pow]
    norm_num
  rw [hsymm]
  have hC : ((3 * t).choose t : ℝ) ≤ (n.choose t : ℝ) := by exact_mod_cast hmono
  have hc0 : (0 : ℝ) ≤ ((3 * t).choose t : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1 : 3 * (t : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    have : ((3 * t : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast ht3
    push_cast at this
    linarith
  have h8 : (0 : ℝ) < 8 ^ t := by positivity
  have ha : (0 : ℝ) ≤ ((32 : ℝ) / 27) ^ t := by positivity
  have hsq : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 * (32 / 27) := by nlinarith
  have key : ((n : ℝ) + 1) * 8 ^ t
      ≤ ((n : ℝ) + 1) ^ 3 * ((32 : ℝ) / 27) ^ (t + 1) * ((3 * t).choose t : ℝ) := by
    calc ((n : ℝ) + 1) * 8 ^ t ≤ ((n : ℝ) + 1) ^ 2 * (32 / 27) * 8 ^ t :=
          mul_le_mul_of_nonneg_right hsq h8.le
      _ = ((n : ℝ) + 1) ^ 2 * (32 / 27) * (((32 : ℝ) / 27) ^ t * (27 / 4) ^ t) := by rw [hab]
      _ ≤ ((n : ℝ) + 1) ^ 2 * (32 / 27)
            * (((32 : ℝ) / 27) ^ t * ((3 * (t : ℝ) + 1) * ((3 * t).choose t : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlow ha) (by positivity)
      _ ≤ ((n : ℝ) + 1) ^ 2 * (32 / 27)
            * (((32 : ℝ) / 27) ^ t * (((n : ℝ) + 1) * ((3 * t).choose t : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn1 hc0) ha) (by positivity)
      _ = ((n : ℝ) + 1) ^ 3 * ((32 : ℝ) / 27) ^ (t + 1) * ((3 * t).choose t : ℝ) := by
          rw [pow_succ]
          ring
  have hpos2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [← mul_div_assoc, le_div_iff₀ hpos2]
  calc ((n : ℝ) + 1) / 4 * 2 ^ n ≤ ((n : ℝ) + 1) / 4 * (4 * 8 ^ t) :=
        mul_le_mul_of_nonneg_left h2n (by positivity)
    _ = ((n : ℝ) + 1) * 8 ^ t := by ring
    _ ≤ ((n : ℝ) + 1) ^ 3 * ((32 : ℝ) / 27) ^ (t + 1) * ((3 * t).choose t : ℝ) := key
    _ ≤ (ff n : ℝ) * (n.choose t : ℝ) := mul_le_mul hff hC hc0 (Nat.cast_nonneg _)

/-- With the proportion `1/2`, the row sum is at least `2^(n/3)` with high probability. -/
lemma half_low {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (X : Fin (ff n) → Ω → ℕ) (h : RowLaw P n (ff n) X) :
    P.real {ω | ∑ i, OMA.S_mo_313415.bankroll (1 / 2) n (X i ω) < (2 : ℝ) ^ (n / 3)}
      ≤ 4 * (1 / ((n : ℝ) + 1)) := by
  have hsub : {ω | ∑ i, OMA.S_mo_313415.bankroll (1 / 2) n (X i ω) < (2 : ℝ) ^ (n / 3)}
      ⊆ {ω | ∀ i, X i ω < n - n / 3} := by
    intro ω hω i
    by_contra hcon
    have hk : n - n / 3 ≤ X i ω := not_lt.1 hcon
    have h1 := half_bankroll_ge n (X i ω) hk
    have h2 : OMA.S_mo_313415.bankroll (1 / 2) n (X i ω)
        ≤ ∑ i, OMA.S_mo_313415.bankroll (1 / 2) n (X i ω) :=
      Finset.single_le_sum (f := fun i => OMA.S_mo_313415.bankroll (1 / 2) n (X i ω))
        (fun j _ => bankroll_nonneg (1 / 2) ⟨by norm_num, by norm_num⟩ n (X j ω))
        (Finset.mem_univ i)
    exact absurd hω (not_lt.2 (le_trans h1 h2))
  have hp0 : 0 ≤ (n.choose (n - n / 3) : ℝ) / 2 ^ n := by positivity
  have hp1 : (n.choose (n - n / 3) : ℝ) / 2 ^ n ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.choose_le_two_pow n (n - n / 3)
  have hNp := Np_lower n
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  calc P.real {ω | ∑ i, OMA.S_mo_313415.bankroll (1 / 2) n (X i ω) < (2 : ℝ) ^ (n / 3)}
      ≤ P.real {ω | ∀ i, X i ω < n - n / 3} := measureReal_mono hsub
    _ ≤ (1 - (n.choose (n - n / 3) : ℝ) / 2 ^ n) ^ (ff n) := h.all_lt_le _
    _ ≤ 1 / (1 + (ff n : ℝ) * ((n.choose (n - n / 3) : ℝ) / 2 ^ n)) :=
        one_sub_pow_le _ hp0 hp1 _
    _ ≤ 1 / (((n : ℝ) + 1) / 4) := one_div_le_one_div_of_le (by positivity) (by linarith)
    _ = 4 * (1 / ((n : ℝ) + 1)) := by field_simp


/-- Proportions `m ≤ 1/4`: the expected row sum is already too small. -/
lemma upper_A {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (X : Fin (ff n) → Ω → ℕ) (h : RowLaw P n (ff n) X) (m : ℝ) (hm0 : 0 ≤ m) (hm : m ≤ 1 / 4) :
    P.real {ω | (2 : ℝ) ^ (n / 3) ≤ ∑ i, OMA.S_mo_313415.bankroll m n (X i ω)}
      ≤ 3 * (((n : ℝ) + 1) ^ 3 * ((27 : ℝ) / 32) ^ (n / 3)) := by
  have hW : ∀ k, 0 ≤ OMA.S_mo_313415.bankroll m n k :=
    fun k => bankroll_nonneg m ⟨hm0, by linarith⟩ n k
  have hmain := h.sum_ge_le (OMA.S_mo_313415.bankroll m n) hW n ((2 : ℝ) ^ (n / 3))
    (by positivity)
  have hmom : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) / 2 ^ n
      * OMA.S_mo_313415.bankroll m n k = ((1 + 2 * m + (1 - m)) / 2) ^ n :=
    moment_all n (1 + 2 * m) (1 - m)
  rw [sum_pmf n, sub_self, mul_zero, zero_add, hmom] at hmain
  refine hmain.trans ?_
  have ht3' : n ≤ 3 * (n / 3) + 2 := by omega
  have hN := ff_le n
  generalize n / 3 = t at *
  have hbase0 : (0 : ℝ) ≤ (1 + 2 * m + (1 - m)) / 2 := by linarith
  have hbase : (1 + 2 * m + (1 - m)) / 2 ≤ (9 : ℝ) / 8 := by linarith
  have hBn : ((1 + 2 * m + (1 - m)) / 2) ^ n ≤ ((9 : ℝ) / 8) ^ (3 * t + 2) :=
    calc ((1 + 2 * m + (1 - m)) / 2) ^ n ≤ ((9 : ℝ) / 8) ^ n := pow_le_pow_left₀ hbase0 hbase n
      _ ≤ ((9 : ℝ) / 8) ^ (3 * t + 2) := pow_le_pow_right₀ (by norm_num) ht3'
  have e1 : ((32 : ℝ) / 27) ^ t * (729 / 512) ^ t = (27 / 32) ^ t * 2 ^ t := by
    rw [← mul_pow, ← mul_pow]
    norm_num
  have e9 : ((9 : ℝ) / 8) ^ (3 * t + 2) = (729 / 512) ^ t * (81 / 64) := by
    rw [pow_add, pow_mul]
    norm_num
  have e32 : ((32 : ℝ) / 27) ^ (t + 1) = (32 / 27) ^ t * (32 / 27) := pow_succ _ _
  rw [div_le_iff₀ (by positivity)]
  calc (ff n : ℝ) * ((1 + 2 * m + (1 - m)) / 2) ^ n
      ≤ (2 * ((n : ℝ) + 1) ^ 3 * ((32 : ℝ) / 27) ^ (t + 1)) * ((9 : ℝ) / 8) ^ (3 * t + 2) :=
        mul_le_mul hN hBn (pow_nonneg hbase0 n) (by positivity)
    _ = 3 * (((n : ℝ) + 1) ^ 3 * (((32 : ℝ) / 27) ^ t * (729 / 512) ^ t)) := by
        rw [e9, e32]
        ring
    _ = 3 * (((n : ℝ) + 1) ^ 3 * ((27 : ℝ) / 32) ^ t) * 2 ^ t := by
        rw [e1]
        ring

/-- The proportion `1`: the row sum vanishes unless some agent wins every bet. -/
lemma upper_one {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (hn : 1 ≤ n) (X : Fin (ff n) → Ω → ℕ) (h : RowLaw P n (ff n) X) :
    P.real {ω | (2 : ℝ) ^ (n / 3) ≤ ∑ i, OMA.S_mo_313415.bankroll 1 n (X i ω)}
      ≤ 3 * (((n : ℝ) + 1) ^ 3 * ((1 : ℝ) / 2) ^ (n / 3)) := by
  have hW : ∀ k, 0 ≤ OMA.S_mo_313415.bankroll 1 n k :=
    fun k => bankroll_nonneg 1 ⟨by norm_num, le_refl _⟩ n k
  have hmain := h.sum_ge_le (OMA.S_mo_313415.bankroll 1 n) hW (n - 1) ((2 : ℝ) ^ (n / 3))
    (by positivity)
  have e : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hzero : ∑ k ∈ Finset.range (n - 1 + 1), (n.choose k : ℝ) / 2 ^ n
      * OMA.S_mo_313415.bankroll 1 n k = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    have hkn : k < n := by
      have := Finset.mem_range.1 hk
      omega
    have hb : OMA.S_mo_313415.bankroll 1 n k = 0 := by
      unfold OMA.S_mo_313415.bankroll
      rw [sub_self, zero_pow (by omega), mul_zero]
    rw [hb, mul_zero]
  rw [hzero, mul_zero, zero_div, add_zero] at hmain
  have htail := tail_le n (n - 1) (Nat.sub_le n 1)
  rw [e] at htail hmain
  refine hmain.trans ?_
  have ht3 : 3 * (n / 3) ≤ n := Nat.mul_div_le n 3
  have hN := ff_le n
  generalize n / 3 = t at *
  have h34 : ((3 : ℝ) / 2) ^ n / 2 ^ n ≤ ((27 : ℝ) / 64) ^ t := by
    calc ((3 : ℝ) / 2) ^ n / 2 ^ n = ((3 : ℝ) / 4) ^ n := by
          rw [← div_pow]
          norm_num
      _ ≤ ((3 : ℝ) / 4) ^ (3 * t) := pow_le_pow_of_le_one (by norm_num) (by norm_num) ht3
      _ = ((27 : ℝ) / 64) ^ t := by
          rw [pow_mul]
          norm_num
  have e1 : ((32 : ℝ) / 27) ^ t * (27 / 64) ^ t = (1 / 2) ^ t := by
    rw [← mul_pow]
    norm_num
  have hNnn : (0 : ℝ) ≤ (ff n : ℝ) := Nat.cast_nonneg _
  calc (ff n : ℝ) * (1 - ∑ k ∈ Finset.range n, (n.choose k : ℝ) / 2 ^ n)
      ≤ (ff n : ℝ) * ((27 : ℝ) / 64) ^ t :=
        mul_le_mul_of_nonneg_left (htail.trans h34) hNnn
    _ ≤ (2 * ((n : ℝ) + 1) ^ 3 * ((32 : ℝ) / 27) ^ (t + 1)) * ((27 : ℝ) / 64) ^ t :=
        mul_le_mul_of_nonneg_right hN (by positivity)
    _ = (64 / 27) * (((n : ℝ) + 1) ^ 3 * (((32 : ℝ) / 27) ^ t * (27 / 64) ^ t)) := by
        rw [pow_succ]
        ring
    _ = (64 / 27) * (((n : ℝ) + 1) ^ 3 * ((1 : ℝ) / 2) ^ t) := by rw [e1]
    _ ≤ 3 * (((n : ℝ) + 1) ^ 3 * ((1 : ℝ) / 2) ^ t) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- Proportions `1/4 ≤ m < 1`: truncation at `n - n/3 + j` wins and a first moment bound. -/
lemma upper_B {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (X : Fin (ff n) → Ω → ℕ) (h : RowLaw P n (ff n) X) (m : ℝ) (hm1 : 1 / 4 ≤ m) (hm2 : m < 1)
    (q : ℕ) :
    P.real {ω | (2 : ℝ) ^ (n / 3) ≤ ∑ i, OMA.S_mo_313415.bankroll m n (X i ω)} ≤
      3 * (((n : ℝ) + 1) ^ 3 * ((1 : ℝ) / 2) ^ (n / (3 * q)))
        + 22 * (((n : ℝ) + 1) ^ 3 *
            ((1 + 2 * m) / (2 * (1 - m)) * ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ q)
              ^ (n / (3 * q))) := by
  have hv : 0 < 1 - m := by linarith
  have hu0 : 0 ≤ 1 + 2 * m := by linarith
  have hu3 : 1 + 2 * m ≤ 3 := by linarith
  have huv : 2 * (1 - m) ≤ 1 + 2 * m := by linarith
  have hρ0 : 0 ≤ (1 + 2 * m) ^ 2 * (1 - m) / 2 := by positivity
  have hρ1 : (1 + 2 * m) ^ 2 * (1 - m) / 2 ≤ 1 := by
    have hid : 2 - (1 + 2 * m) ^ 2 * (1 - m) = (2 * m - 1) ^ 2 * (m + 1) := by ring
    have hpos : 0 ≤ (2 * m - 1) ^ 2 * (m + 1) := by positivity
    linarith
  have hR0 : 0 ≤ (1 + 2 * m) / (2 * (1 - m)) := by positivity
  have ht3 : 3 * (n / 3) ≤ n := Nat.mul_div_le n 3
  have ht3' : n ≤ 3 * (n / 3) + 2 := by omega
  have hjdef : n / (3 * q) = n / 3 / q := (Nat.div_div_eq_div_mul n 3 q).symm
  rw [hjdef]
  have hN := ff_le n
  have hQ0 := fun j => Q_le n j
  generalize n / 3 = t at *
  have hqj : q * (t / q) ≤ t := Nat.mul_div_le t q
  have hjt : t / q ≤ t := Nat.div_le_self t q
  have hQ := hQ0 (t / q)
  generalize t / q = j at *
  have htn : t ≤ n := by omega
  have hL : n - t + j ≤ n := by omega
  have hW : ∀ k, 0 ≤ OMA.S_mo_313415.bankroll m n k :=
    fun k => bankroll_nonneg m ⟨by linarith, hm2.le⟩ n k
  have hmain := h.sum_ge_le (OMA.S_mo_313415.bankroll m n) hW (n - t + j) ((2 : ℝ) ^ t)
    (by positivity)
  have htail := tail_le n (n - t + j) hL
  have hmom : ∑ k ∈ Finset.range (n - t + j + 1), (n.choose k : ℝ) / 2 ^ n
      * OMA.S_mo_313415.bankroll m n k
      ≤ (1 + 2 * m) ^ (n - t + j) * (1 - m) ^ (n - (n - t + j)) * ((3 : ℝ) / 2) ^ n
          / 2 ^ (n - t + j) :=
    moment_le n (n - t + j) hL (1 + 2 * m) (1 - m) hv.le huv
  have hNnn : (0 : ℝ) ≤ (ff n : ℝ) := Nat.cast_nonneg _
  have hcancel : ((32 : ℝ) / 27) ^ (t + 1) * (27 / 32) ^ t = 32 / 27 := by
    rw [pow_succ, mul_comm (((32 : ℝ) / 27) ^ t) (32 / 27), mul_assoc, ← mul_pow]
    norm_num
  -- the truncation event
  have hfirst : (ff n : ℝ) * (1 - ∑ k ∈ Finset.range (n - t + j + 1), (n.choose k : ℝ) / 2 ^ n)
      ≤ 3 * (((n : ℝ) + 1) ^ 3 * ((1 : ℝ) / 2) ^ j) := by
    have h1 : 1 - ∑ k ∈ Finset.range (n - t + j + 1), (n.choose k : ℝ) / 2 ^ n
        ≤ ((27 : ℝ) / 32) ^ t * (1 / 2) ^ j := by
      calc 1 - ∑ k ∈ Finset.range (n - t + j + 1), (n.choose k : ℝ) / 2 ^ n
          ≤ ((3 : ℝ) / 2) ^ n / 2 ^ (n - t + j + 1) := htail
        _ ≤ ((3 : ℝ) / 2) ^ n / 2 ^ (n - t + j) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (pow_le_pow_right₀ (by norm_num) (Nat.le_succ _))
        _ ≤ ((27 : ℝ) / 32) ^ t * (1 / 2) ^ j := hQ
    calc (ff n : ℝ) * (1 - ∑ k ∈ Finset.range (n - t + j + 1), (n.choose k : ℝ) / 2 ^ n)
        ≤ (ff n : ℝ) * (((27 : ℝ) / 32) ^ t * (1 / 2) ^ j) :=
          mul_le_mul_of_nonneg_left h1 hNnn
      _ ≤ (2 * ((n : ℝ) + 1) ^ 3 * ((32 : ℝ) / 27) ^ (t + 1))
            * (((27 : ℝ) / 32) ^ t * (1 / 2) ^ j) :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ = 2 * (((32 : ℝ) / 27) ^ (t + 1) * (27 / 32) ^ t)
            * (((n : ℝ) + 1) ^ 3 * ((1 : ℝ) / 2) ^ j) := by ring
      _ = (64 / 27) * (((n : ℝ) + 1) ^ 3 * ((1 : ℝ) / 2) ^ j) := by
          rw [hcancel]
          ring
      _ ≤ 3 * (((n : ℝ) + 1) ^ 3 * ((1 : ℝ) / 2) ^ j) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  -- the truncated first moment
  have he : n - (n - t + j) = t - j := by omega
  have hsplit : n - t + j = 2 * t + (n - 3 * t) + j := by omega
  have hsmall : (1 + 2 * m) ^ (n - 3 * t) ≤ 9 := by
    calc (1 + 2 * m) ^ (n - 3 * t) ≤ (3 : ℝ) ^ (n - 3 * t) := pow_le_pow_left₀ hu0 hu3 _
      _ ≤ (3 : ℝ) ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 9 := by norm_num
  have hvt : (1 - m) ^ t = (1 - m) ^ (t - j) * (1 - m) ^ j := (pow_sub_mul_pow (1 - m) hjt).symm
  have hid1 : ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ t * 2 ^ t
      = (1 + 2 * m) ^ (2 * t) * (1 - m) ^ t := by
    rw [← mul_pow, div_mul_cancel₀ _ (two_ne_zero), mul_pow, ← pow_mul]
  have hid3 : ((1 + 2 * m) / (2 * (1 - m))) ^ j * (1 - m) ^ j
      = (1 + 2 * m) ^ j * (1 / 2) ^ j := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    field_simp
  have hident : (1 + 2 * m) ^ (2 * t) * (1 - m) ^ (t - j) * (1 + 2 * m) ^ j * (1 / 2) ^ j
      = ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ t * ((1 + 2 * m) / (2 * (1 - m))) ^ j * 2 ^ t := by
    calc (1 + 2 * m) ^ (2 * t) * (1 - m) ^ (t - j) * (1 + 2 * m) ^ j * (1 / 2) ^ j
        = (1 + 2 * m) ^ (2 * t) * (1 - m) ^ (t - j) * ((1 + 2 * m) ^ j * (1 / 2) ^ j) := by ring
      _ = (1 + 2 * m) ^ (2 * t) * (1 - m) ^ (t - j)
            * (((1 + 2 * m) / (2 * (1 - m))) ^ j * (1 - m) ^ j) := by rw [hid3]
      _ = (1 + 2 * m) ^ (2 * t) * ((1 - m) ^ (t - j) * (1 - m) ^ j)
            * ((1 + 2 * m) / (2 * (1 - m))) ^ j := by ring
      _ = (1 + 2 * m) ^ (2 * t) * (1 - m) ^ t * ((1 + 2 * m) / (2 * (1 - m))) ^ j := by
          rw [← hvt]
      _ = ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ t * 2 ^ t * ((1 + 2 * m) / (2 * (1 - m))) ^ j := by
          rw [hid1]
      _ = ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ t * ((1 + 2 * m) / (2 * (1 - m))) ^ j * 2 ^ t := by
          ring
  have hρt : ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ t
      ≤ (((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ q) ^ j := by
    calc ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ t ≤ ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ (q * j) :=
          pow_le_pow_of_le_one hρ0 hρ1 hqj
      _ = (((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ q) ^ j := pow_mul _ q j
  have hsecond : (ff n : ℝ) * (∑ k ∈ Finset.range (n - t + j + 1), (n.choose k : ℝ) / 2 ^ n
      * OMA.S_mo_313415.bankroll m n k) / 2 ^ t
      ≤ 22 * (((n : ℝ) + 1) ^ 3 *
          ((1 + 2 * m) / (2 * (1 - m)) * ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ q) ^ j) := by
    have hm1' : ∑ k ∈ Finset.range (n - t + j + 1), (n.choose k : ℝ) / 2 ^ n
        * OMA.S_mo_313415.bankroll m n k
        ≤ 9 * ((1 + 2 * m) ^ (2 * t) * (1 - m) ^ (t - j) * (1 + 2 * m) ^ j * (1 / 2) ^ j)
            * ((27 : ℝ) / 32) ^ t := by
      calc ∑ k ∈ Finset.range (n - t + j + 1), (n.choose k : ℝ) / 2 ^ n
            * OMA.S_mo_313415.bankroll m n k
          ≤ (1 + 2 * m) ^ (n - t + j) * (1 - m) ^ (n - (n - t + j)) * ((3 : ℝ) / 2) ^ n
              / 2 ^ (n - t + j) := hmom
        _ = (1 + 2 * m) ^ (n - t + j) * (1 - m) ^ (t - j)
              * (((3 : ℝ) / 2) ^ n / 2 ^ (n - t + j)) := by
            rw [he]
            ring
        _ ≤ (1 + 2 * m) ^ (n - t + j) * (1 - m) ^ (t - j)
              * (((27 : ℝ) / 32) ^ t * (1 / 2) ^ j) :=
            mul_le_mul_of_nonneg_left hQ (by positivity)
        _ = (1 + 2 * m) ^ (n - 3 * t) * ((1 + 2 * m) ^ (2 * t) * (1 - m) ^ (t - j)
              * (1 + 2 * m) ^ j * (1 / 2) ^ j) * ((27 : ℝ) / 32) ^ t := by
            rw [hsplit, pow_add, pow_add]
            ring
        _ ≤ 9 * ((1 + 2 * m) ^ (2 * t) * (1 - m) ^ (t - j) * (1 + 2 * m) ^ j * (1 / 2) ^ j)
              * ((27 : ℝ) / 32) ^ t :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsmall (by positivity))
              (by positivity)
    have hσ : ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ t * ((1 + 2 * m) / (2 * (1 - m))) ^ j
        ≤ ((1 + 2 * m) / (2 * (1 - m)) * ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ q) ^ j := by
      rw [mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_left hρt (pow_nonneg hR0 j)
    rw [div_le_iff₀ (by positivity)]
    calc (ff n : ℝ) * (∑ k ∈ Finset.range (n - t + j + 1), (n.choose k : ℝ) / 2 ^ n
          * OMA.S_mo_313415.bankroll m n k)
        ≤ (2 * ((n : ℝ) + 1) ^ 3 * ((32 : ℝ) / 27) ^ (t + 1))
            * (9 * ((1 + 2 * m) ^ (2 * t) * (1 - m) ^ (t - j) * (1 + 2 * m) ^ j * (1 / 2) ^ j)
              * ((27 : ℝ) / 32) ^ t) :=
          mul_le_mul hN hm1' (Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (hW k))
            (by positivity)
      _ = 18 * (((32 : ℝ) / 27) ^ (t + 1) * (27 / 32) ^ t) * ((n : ℝ) + 1) ^ 3
            * ((1 + 2 * m) ^ (2 * t) * (1 - m) ^ (t - j) * (1 + 2 * m) ^ j * (1 / 2) ^ j) := by
          ring
      _ = (64 / 3) * ((n : ℝ) + 1) ^ 3
            * (((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ t * ((1 + 2 * m) / (2 * (1 - m))) ^ j)
            * 2 ^ t := by
          rw [hcancel, hident]
          ring
      _ ≤ (64 / 3) * ((n : ℝ) + 1) ^ 3
            * ((1 + 2 * m) / (2 * (1 - m)) * ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ q) ^ j
            * 2 ^ t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hσ (by positivity))
            (by positivity)
      _ ≤ 22 * (((n : ℝ) + 1) ^ 3 *
            ((1 + 2 * m) / (2 * (1 - m)) * ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ q) ^ j)
            * 2 ^ t := by
          have hnn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 *
              ((1 + 2 * m) / (2 * (1 - m)) * ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ q) ^ j := by
            positivity
          have h2t : (0 : ℝ) ≤ 2 ^ t := by positivity
          nlinarith [mul_nonneg hnn h2t]
  exact hmain.trans (add_le_add hfirst hsecond)

lemma exists_q (m : ℝ) (hm1 : 1 / 4 ≤ m) (hm2 : m < 1) (hne : m ≠ 1 / 2) :
    ∃ q : ℕ, 1 ≤ q ∧
      (1 + 2 * m) / (2 * (1 - m)) * ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ q < 1 := by
  have hv : 0 < 1 - m := by linarith
  have hρ0 : 0 ≤ (1 + 2 * m) ^ 2 * (1 - m) / 2 := by positivity
  have hρ1 : (1 + 2 * m) ^ 2 * (1 - m) / 2 < 1 := by
    have hid : 2 - (1 + 2 * m) ^ 2 * (1 - m) = (2 * m - 1) ^ 2 * (m + 1) := by ring
    have hne' : 2 * m - 1 ≠ 0 := fun h0 => hne (by linarith)
    have hsq : 0 < (2 * m - 1) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne'))
    have hpos : 0 < (2 * m - 1) ^ 2 * (m + 1) := mul_pos hsq (by linarith)
    linarith
  have hR : 0 < (1 + 2 * m) / (2 * (1 - m)) := by positivity
  obtain ⟨q0, hq0⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hR) hρ1
  refine ⟨q0 + 1, by omega, ?_⟩
  have h1 : ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ (q0 + 1)
      ≤ ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ q0 :=
    pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_succ q0)
  calc (1 + 2 * m) / (2 * (1 - m)) * ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ (q0 + 1)
      ≤ (1 + 2 * m) / (2 * (1 - m)) * ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ q0 :=
        mul_le_mul_of_nonneg_left h1 hR.le
    _ < (1 + 2 * m) / (2 * (1 - m)) * ((1 + 2 * m) / (2 * (1 - m)))⁻¹ :=
        mul_lt_mul_of_pos_left hq0 hR
    _ = 1 := mul_inv_cancel₀ hR.ne'

/-- For every `m' ≠ 1/2` in `[0, 1]`, the row sum is below `2^(n/3)` with high probability. -/
lemma upper_all {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (K : (n : ℕ) → Fin (ff n) → Ω → ℕ) (hK : ∀ n : ℕ, 1 ≤ n → RowLaw P n (ff n) (K n))
    (m : ℝ) (hm : m ∈ Set.Icc (0 : ℝ) 1) (hne : m ≠ 1 / 2) :
    ∃ B : ℕ → ℝ, Tendsto B atTop (𝓝 0) ∧ ∀ n : ℕ, 1 ≤ n →
      P.real {ω | (2 : ℝ) ^ (n / 3) ≤ ∑ i, OMA.S_mo_313415.bankroll m n (K n i ω)} ≤ B n := by
  rcases le_or_gt m (1 / 4) with hA | hA
  · refine ⟨fun n => 3 * (((n : ℝ) + 1) ^ 3 * ((27 : ℝ) / 32) ^ (n / 3)), ?_,
      fun n hn => upper_A P n (K n) (hK n hn) m hm.1 hA⟩
    simpa using (tendsto_poly_geom 3 3 (by norm_num) (27 / 32) (by norm_num)
      (by norm_num)).const_mul 3
  · rcases eq_or_lt_of_le hm.2 with h1 | h1
    · subst h1
      refine ⟨fun n => 3 * (((n : ℝ) + 1) ^ 3 * ((1 : ℝ) / 2) ^ (n / 3)), ?_,
        fun n hn => upper_one P n hn (K n) (hK n hn)⟩
      simpa using (tendsto_poly_geom 3 3 (by norm_num) (1 / 2) (by norm_num)
        (by norm_num)).const_mul 3
    · obtain ⟨q, hq, hσ⟩ := exists_q m hA.le h1 hne
      have hv : 0 < 1 - m := by linarith
      have hσ0 : 0 ≤ (1 + 2 * m) / (2 * (1 - m)) * ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ q := by
        have : 0 ≤ 1 + 2 * m := by linarith
        positivity
      refine ⟨fun n => 3 * (((n : ℝ) + 1) ^ 3 * ((1 : ℝ) / 2) ^ (n / (3 * q)))
        + 22 * (((n : ℝ) + 1) ^ 3 *
            ((1 + 2 * m) / (2 * (1 - m)) * ((1 + 2 * m) ^ 2 * (1 - m) / 2) ^ q)
              ^ (n / (3 * q))), ?_, fun n hn => upper_B P n (K n) (hK n hn) m hA.le h1 q⟩
      have hd : 0 < 3 * q := by omega
      have t1 := (tendsto_poly_geom 3 (3 * q) hd (1 / 2) (by norm_num) (by norm_num)).const_mul 3
      have t2 := (tendsto_poly_geom 3 (3 * q) hd _ hσ0 hσ).const_mul 22
      simpa using t1.add t2

end OMA

theorem OMA.solution : type_of% @OMA.S_mo_313415.main := by
  refine ⟨OMA.ff, OMA.ff_strictMono, 1 / 2, ⟨by norm_num, by norm_num⟩, by norm_num,
    by norm_num, ?_⟩
  intro Ω _ P _ K hK m' hm' hne
  obtain ⟨B, hB0, hB⟩ := OMA.upper_all P (K m') (fun n hn => hK m' hm' n hn) m' hm' hne
  have hlow : ∀ n : ℕ, 1 ≤ n →
      P.real {ω | OMA.S_mo_313415.rowSum OMA.ff K (1 / 2) n ω < (2 : ℝ) ^ (n / 3)}
        ≤ 4 * (1 / ((n : ℝ) + 1)) :=
    fun n hn => OMA.half_low P n (K (1 / 2) n)
      (hK (1 / 2) ⟨by norm_num, by norm_num⟩ n hn)
  have hreal : Tendsto (fun n : ℕ => P.real {ω | OMA.S_mo_313415.rowSum OMA.ff K m' n ω
      < OMA.S_mo_313415.rowSum OMA.ff K (1 / 2) n ω}) atTop (𝓝 1) := by
    have hg : Tendsto (fun n : ℕ => 1 - 4 * (1 / ((n : ℝ) + 1)) - B n) atTop (𝓝 1) := by
      have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 4
      have h2 := ((tendsto_const_nhds (x := (1 : ℝ))).sub h1).sub hB0
      simpa using h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg tendsto_const_nhds ?_
      (Eventually.of_forall fun n => measureReal_le_one)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hE : 1 ≤ P.real {ω | OMA.S_mo_313415.rowSum OMA.ff K m' n ω
          < OMA.S_mo_313415.rowSum OMA.ff K (1 / 2) n ω}
        + P.real {ω | OMA.S_mo_313415.rowSum OMA.ff K m' n ω
          < OMA.S_mo_313415.rowSum OMA.ff K (1 / 2) n ω}ᶜ := by
      have h := measureReal_union_le (μ := P)
        {ω | OMA.S_mo_313415.rowSum OMA.ff K m' n ω
          < OMA.S_mo_313415.rowSum OMA.ff K (1 / 2) n ω}
        {ω | OMA.S_mo_313415.rowSum OMA.ff K m' n ω
          < OMA.S_mo_313415.rowSum OMA.ff K (1 / 2) n ω}ᶜ
      rw [Set.union_compl_self, probReal_univ] at h
      exact h
    have hsub : {ω | OMA.S_mo_313415.rowSum OMA.ff K m' n ω
          < OMA.S_mo_313415.rowSum OMA.ff K (1 / 2) n ω}ᶜ
        ⊆ {ω | OMA.S_mo_313415.rowSum OMA.ff K (1 / 2) n ω < (2 : ℝ) ^ (n / 3)}
          ∪ {ω | (2 : ℝ) ^ (n / 3) ≤ OMA.S_mo_313415.rowSum OMA.ff K m' n ω} := by
      intro ω hω
      have hle : OMA.S_mo_313415.rowSum OMA.ff K (1 / 2) n ω
          ≤ OMA.S_mo_313415.rowSum OMA.ff K m' n ω := not_lt.1 hω
      by_cases hc : OMA.S_mo_313415.rowSum OMA.ff K (1 / 2) n ω < (2 : ℝ) ^ (n / 3)
      · exact Or.inl hc
      · exact Or.inr (le_trans (not_lt.1 hc) hle)
    have hEc := (measureReal_mono (μ := P) hsub).trans
      ((measureReal_union_le _ _).trans (add_le_add (hlow n hn) (hB n hn)))
    linarith
  unfold OMA.S_mo_313415.DoesBetter
  have h := ENNReal.tendsto_ofReal hreal
  rw [ENNReal.ofReal_one] at h
  exact h.congr fun n => ofReal_measureReal

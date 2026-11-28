import FormalConjectures.ErdosProblems.«695»

/-!
# Erdős 695: reduce growth of the chain to rarity of each multiplier
Credit: @jarrettbranch

Write `q (i + 1) = m i * q i + 1`, which is possible since `q (i + 1) % q i = 1`; `m i` is the
multiplier of step `i`. Then `q k ≥ m 0 * m 1 * ⋯ * m (k - 1)`, so `q k ^ (1 / k)` is at least
the geometric mean of the multipliers. If each fixed multiplier value occurs only on a set of
steps of natural density zero, then for every bound `M` all but a density-zero set of steps
have `m i ≥ M`, so eventually `q k ≥ M ^ (k / 2)` and `q k ^ (1 / k) ≥ √M`. This file proves
that implication in full.

The arithmetic core is split by multiplier:
* `H1`: steps `q ↦ 2q + 1` (Sophie Germain / Cunningham steps) have density zero in every
  such chain.
* `H2`: for every other value `m`, steps `q ↦ mq + 1` have density zero in every such chain.
  (For odd `m` and for `m = 0` this is easy by parity; the content is even `m ≥ 4`.)
-/

namespace OMA.R_Erdos695_erdos_695_R1

open Filter Topology Finset

/-- In every chain of primes with `q (i + 1) ≡ 1 (mod q i)`, the steps with multiplier `2`
have natural density zero. -/
def H1 : Prop :=
  ∀ q : ℕ → ℕ, StrictMono q → (∀ i, (q i).Prime) → (∀ i, q (i + 1) % q i = 1) →
    Tendsto (fun N : ℕ =>
      ((((range N).filter (fun i => q (i + 1) = 2 * q i + 1)).card : ℕ) : ℝ) / N)
      atTop (𝓝 0)

/-- In every chain of primes with `q (i + 1) ≡ 1 (mod q i)`, for every multiplier `m ≠ 2`, the
steps with multiplier `m` have natural density zero. -/
def H2 : Prop :=
  ∀ q : ℕ → ℕ, StrictMono q → (∀ i, (q i).Prime) → (∀ i, q (i + 1) % q i = 1) →
    ∀ m : ℕ, m ≠ 2 →
    Tendsto (fun N : ℕ =>
      ((((range N).filter (fun i => q (i + 1) = m * q i + 1)).card : ℕ) : ℝ) / N)
      atTop (𝓝 0)

theorem main : H1 → H2 → type_of% @Erdos695.erdos_695 := by
  intro h1 h2 q hq hp hmod
  -- every multiplier value has density zero
  have hd : ∀ m : ℕ, Tendsto (fun N : ℕ =>
      ((((range N).filter (fun i => q (i + 1) = m * q i + 1)).card : ℕ) : ℝ) / N)
      atTop (𝓝 0) := by
    intro m
    by_cases hm : m = 2
    · subst hm; exact h1 q hq hp hmod
    · exact h2 q hq hp hmod m hm
  -- the multiplier of step i is q (i + 1) / q i
  have hdecomp : ∀ i, q (i + 1) = q (i + 1) / q i * q i + 1 := by
    intro i
    have h := Nat.div_add_mod (q (i + 1)) (q i)
    rw [hmod i, mul_comm] at h
    exact h.symm
  have hpos : ∀ i, 1 ≤ q (i + 1) / q i := by
    intro i
    by_contra h
    have h0 : q (i + 1) / q i = 0 := Nat.lt_one_iff.mp (not_le.mp h)
    have h' := hdecomp i
    rw [h0, zero_mul, zero_add] at h'
    exact absurd h' (hp (i + 1)).one_lt.ne'
  -- the product of the multipliers is at most q k
  have hprod : ∀ k, ∏ i ∈ range k, (q (i + 1) / q i) ≤ q k := by
    intro k
    induction k with
    | zero => simpa using (hp 0).one_lt.le
    | succ k ih =>
      rw [prod_range_succ]
      calc (∏ i ∈ range k, (q (i + 1) / q i)) * (q (k + 1) / q k)
          ≤ q k * (q (k + 1) / q k) := Nat.mul_le_mul_right _ ih
        _ = q (k + 1) / q k * q k := mul_comm _ _
        _ ≤ q (k + 1) / q k * q k + 1 := Nat.le_succ _
        _ = q (k + 1) := (hdecomp k).symm
  rw [tendsto_atTop]
  intro B
  -- choose an integer bound M ≥ max 1 (B ^ 2)
  set M : ℕ := ⌈B ^ 2⌉₊ + 1 with hMdef
  have hM1 : (1 : ℝ) ≤ M := by
    have : (1 : ℕ) ≤ M := by omega
    exact_mod_cast this
  have hBM : B ^ 2 ≤ (M : ℝ) := by
    have h := Nat.le_ceil (B ^ 2)
    have : ((⌈B ^ 2⌉₊ : ℕ) : ℝ) ≤ M := by exact_mod_cast (by omega : ⌈B ^ 2⌉₊ ≤ M)
    linarith
  -- steps with multiplier below M have density zero
  have hsmall_le : ∀ k, ((range k).filter (fun i => q (i + 1) / q i < M)).card ≤
      ∑ m ∈ range M, ((range k).filter (fun i => q (i + 1) = m * q i + 1)).card := by
    intro k
    refine le_trans (card_le_card ?_) card_biUnion_le
    intro i hi
    rw [mem_filter] at hi
    rw [mem_biUnion]
    refine ⟨q (i + 1) / q i, mem_range.2 hi.2, ?_⟩
    rw [mem_filter]
    exact ⟨hi.1, hdecomp i⟩
  have hsmall : Tendsto (fun k : ℕ =>
      ((((range k).filter (fun i => q (i + 1) / q i < M)).card : ℕ) : ℝ) / k)
      atTop (𝓝 0) := by
    have hsum : Tendsto (fun k : ℕ => ∑ m ∈ range M,
        ((((range k).filter (fun i => q (i + 1) = m * q i + 1)).card : ℕ) : ℝ) / k)
        atTop (𝓝 0) := by
      have := tendsto_finsetSum (range M) (fun m _ => hd m)
      rw [Finset.sum_const_zero] at this
      exact this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum ?_ ?_
    · intro k; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · intro k
      simp only
      rw [← Finset.sum_div]
      gcongr
      exact_mod_cast hsmall_le k
  have hev := hsmall.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hev, eventually_gt_atTop 0] with k hk hk0
  set small := ((range k).filter (fun i => q (i + 1) / q i < M)).card with hsmalldef
  set large := ((range k).filter (fun i => ¬ q (i + 1) / q i < M)).card with hlargedef
  have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
  have hcount : (small : ℝ) + large = k := by
    have h := card_filter_add_card_filter_not
      (s := range k) (fun i => q (i + 1) / q i < M)
    rw [card_range] at h
    exact_mod_cast h
  have hlarge : (1 : ℝ) / 2 ≤ (large : ℝ) / k := by
    rw [div_lt_iff₀ hk0'] at hk
    rw [le_div_iff₀ hk0']
    linarith
  -- M ^ large ≤ q k
  have hpow : M ^ large ≤ q k := by
    calc M ^ large
        ≤ ∏ i ∈ (range k).filter (fun i => ¬ q (i + 1) / q i < M), (q (i + 1) / q i) := by
          apply Finset.pow_card_le_prod
          intro i hi
          rw [mem_filter] at hi
          exact not_lt.1 hi.2
      _ ≤ ∏ i ∈ range k, (q (i + 1) / q i) :=
          Finset.prod_le_prod_of_subset_of_one_le' (filter_subset _ _)
            (fun i _ _ => hpos i)
      _ ≤ q k := hprod k
  have hpowR : (M : ℝ) ^ (large : ℝ) ≤ (q k : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hpow
  have hM0 : (0 : ℝ) ≤ M := by linarith
  calc B ≤ |B| := le_abs_self B
    _ ≤ Real.sqrt M := Real.abs_le_sqrt hBM
    _ = (M : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    _ ≤ (M : ℝ) ^ ((large : ℝ) / k) := Real.rpow_le_rpow_of_exponent_le hM1 hlarge
    _ = ((M : ℝ) ^ (large : ℝ)) ^ (1 / (k : ℝ)) := by
          rw [← Real.rpow_mul hM0]; ring_nf
    _ ≤ (q k : ℝ) ^ (1 / (k : ℝ)) :=
          Real.rpow_le_rpow (by positivity) hpowR (by positivity)

end OMA.R_Erdos695_erdos_695_R1

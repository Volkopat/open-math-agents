import FormalConjectures.ErdosProblems.«247»
import Mathlib

-- Reduction Erdos247.erdos_247.R1 of Erdős Problem 247
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Write `a = ∑ 2^(-n_k)`. The partial sum `S_K` up to `K` is a dyadic rational `P / 2^(n_K)`,
and the tail `a - S_K` lies in `(0, 2 / 2^(n_(K+1))]`.

* If `n_(k+1) / n_k` does not tend to `1`, then `n_(k+1) ≥ (1 + ε) n_k` for infinitely many `k`,
  so `S_K` approximates `a` to order `(2^(n_K))^(-(1+ε))`. Ridout's theorem with denominators
  restricted to powers of `2` (`H1`) rules this out for algebraic `a`; this is proved here.
* If `n` is not polynomially bounded, the lower bound of Bailey, Borwein, Crandall and
  Pomerance for the number of nonzero binary digits of an algebraic number (`H2`), taken at
  `N = n_K`, gives `c n_K^(1/D) ≤ K + 1`, a polynomial bound; this is proved here.
* What remains (`H3`) is the slowly growing case: `n_(k+1) / n_k → 1` and `n_k ≤ C (k+1)^t`,
  together with the hypothesis of the problem. Typical open instances are `n_k = ⌊k log k⌋`
  and `n_k = k^2 + k`.

References: D. Ridout, Rational approximations to algebraic numbers, Mathematika 4 (1957);
D. H. Bailey, J. M. Borwein, R. E. Crandall and C. Pomerance, On the binary expansions of
algebraic numbers, J. Théor. Nombres Bordeaux 16 (2004).
-/

open Filter Finset

namespace OMA.R_Erdos247_erdos_247_R1

/-- Ridout's theorem for dyadic denominators: an algebraic real number has, for each `ε > 0`,
only finitely many exponents `k` with a dyadic approximation `0 < |α - p / 2^k| < 2^(-(1+ε) k)`. -/
def H1 : Prop :=
  ∀ α : ℝ, IsAlgebraic ℚ α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ p : ℤ,
    α ≠ (p : ℝ) / 2 ^ k → 1 ≤ (2 : ℝ) ^ ((1 + ε) * k) * |α - (p : ℝ) / 2 ^ k|

/-- The digit-count bound of Bailey, Borwein, Crandall and Pomerance, for sums of distinct
powers of `1/2`: if the sum is algebraic (of degree at most `D`), at least `c N^(1/D)` of the
exponents are at most `N`, for all large `N`. -/
def H2 : Prop :=
  ∀ n : ℕ → ℕ, StrictMono n → IsAlgebraic ℚ (∑' k, (1 : ℝ) / 2 ^ n k) →
    ∃ D : ℕ, 0 < D ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ^ ((1 : ℝ) / D) ≤ ((range (N + 1)).filter (fun k => n k ≤ N)).card

/-- The open core: sequences with `n_(k+1) / n_k → 1` that grow at most polynomially. -/
def H3 : Prop :=
  ∀ n : ℕ → ℕ, StrictMono n →
    atTop.limsup (fun k => (n k / k.succ : EReal)) = ⊤ →
    Tendsto (fun k => (n (k + 1) : ℝ) / n k) atTop (nhds 1) →
    (∃ C t : ℕ, ∀ k, n k ≤ C * (k + 1) ^ t) →
    Transcendental ℚ (∑' k, (1 : ℝ) / 2 ^ n k)

/-- The series converges: `1 / 2^(n_k) ≤ (1/2)^k`. -/
theorem summable_dyadic {n : ℕ → ℕ} (hn : StrictMono n) :
    Summable (fun k => (1 : ℝ) / 2 ^ n k) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) summable_geometric_two
  rw [one_div, ← inv_pow, ← one_div]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hn.id_le k)

/-- A strictly increasing sequence gains at least one per step. -/
theorem index_shift {n : ℕ → ℕ} (hn : StrictMono n) (K i : ℕ) :
    n (K + 1) + i ≤ n (i + (K + 1)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have := hn (show i + (K + 1) < i + 1 + (K + 1) by omega)
    omega

/-- The tail after the index `K` is positive. -/
theorem tail_pos {n : ℕ → ℕ} (hn : StrictMono n) (K : ℕ) :
    0 < ∑' i, (1 : ℝ) / 2 ^ n (i + (K + 1)) := by
  have hs := (summable_nat_add_iff (K + 1)).mpr (summable_dyadic hn)
  exact hs.tsum_pos (fun i => by positivity) 0 (by positivity)

/-- The tail after the index `K` is at most `2 / 2^(n_(K+1))`. -/
theorem tail_le {n : ℕ → ℕ} (hn : StrictMono n) (K : ℕ) :
    ∑' i, (1 : ℝ) / 2 ^ n (i + (K + 1)) ≤ 2 / 2 ^ n (K + 1) := by
  have hs := (summable_nat_add_iff (K + 1)).mpr (summable_dyadic hn)
  have hg : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ n (K + 1) * (1 / 2) ^ i) :=
    summable_geometric_two.mul_left _
  calc ∑' i, (1 : ℝ) / 2 ^ n (i + (K + 1))
      ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ n (K + 1) * (1 / 2) ^ i := by
        refine Summable.tsum_le_tsum (fun i => ?_) hs hg
        rw [← pow_add, one_div, ← inv_pow, ← one_div]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (index_shift hn K i)
    _ = 2 / 2 ^ n (K + 1) := by
        rw [tsum_mul_left, tsum_geometric_two, one_div, inv_pow]
        ring

/-- The partial sum up to `K` is a dyadic rational with denominator `2^(n_K)`. -/
theorem partial_eq {n : ℕ → ℕ} (hn : StrictMono n) (K : ℕ) :
    ∑ k ∈ range (K + 1), (1 : ℝ) / 2 ^ n k =
      ((∑ k ∈ range (K + 1), 2 ^ (n K - n k) : ℕ) : ℝ) / 2 ^ n K := by
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hle : n k ≤ n K := hn.monotone (by simpa [Nat.lt_succ_iff] using hk)
  have h2 : (2 : ℝ) ^ n K = 2 ^ (n K - n k) * 2 ^ n k := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [h2]
  push_cast
  field_simp

/-- The sum is the partial sum up to `K` plus the tail after `K`. -/
theorem split_eq {n : ℕ → ℕ} (hn : StrictMono n) (K : ℕ) :
    ∑' k, (1 : ℝ) / 2 ^ n k =
      ∑ k ∈ range (K + 1), (1 : ℝ) / 2 ^ n k + ∑' i, (1 : ℝ) / 2 ^ n (i + (K + 1)) :=
  ((summable_dyadic hn).sum_add_tsum_nat_add (K + 1)).symm

/-- If the ratios `n_(k+1) / n_k` do not tend to `1`, one of them is at least `1 + ε` beyond
every index. -/
theorem ratio_gap {n : ℕ → ℕ} (hn : StrictMono n)
    (hr : ¬ Tendsto (fun k => (n (k + 1) : ℝ) / n k) atTop (nhds 1)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N, ∃ k ≥ N, (1 + ε) * (n k : ℝ) ≤ n (k + 1) := by
  rw [Metric.tendsto_atTop] at hr
  push Not at hr
  obtain ⟨ε, hε, h⟩ := hr
  refine ⟨ε, hε, fun N => ?_⟩
  obtain ⟨k, hk, hd⟩ := h (N + 1)
  refine ⟨k, by omega, ?_⟩
  have hk0 : k ≤ n k := hn.id_le k
  have hpos : (0 : ℝ) < n k := by exact_mod_cast (show 0 < n k by omega)
  have hlt : (n k : ℝ) < n (k + 1) := by exact_mod_cast hn (Nat.lt_succ_self k)
  have hge : (1 : ℝ) ≤ (n (k + 1) : ℝ) / n k := by
    rw [le_div_iff₀ hpos]; linarith
  rw [Real.dist_eq, abs_of_nonneg (by linarith)] at hd
  have h' : 1 + ε ≤ (n (k + 1) : ℝ) / n k := by linarith
  rw [le_div_iff₀ hpos] at h'
  linarith

/-- The lacunary case: Ridout's theorem makes the sum transcendental as soon as
`n_(k+1) / n_k` does not tend to `1`. -/
theorem lacunary {n : ℕ → ℕ} (hn : StrictMono n) (h1 : H1)
    (hr : ¬ Tendsto (fun k => (n (k + 1) : ℝ) / n k) atTop (nhds 1)) :
    Transcendental ℚ (∑' k, (1 : ℝ) / 2 ^ n k) := by
  intro halg
  obtain ⟨ε, hε, hfreq⟩ := ratio_gap hn hr
  obtain ⟨M, hM⟩ := eventually_atTop.mp (h1 _ halg (ε / 2) (by positivity))
  obtain ⟨k, hk, hgap⟩ := hfreq (M + ⌈2 / ε⌉₊ + 1)
  have hnk : k ≤ n k := hn.id_le k
  obtain ⟨P, hP⟩ : ∃ P : ℕ, ∑ j ∈ range (k + 1), (1 : ℝ) / 2 ^ n j = (P : ℝ) / 2 ^ n k :=
    ⟨_, partial_eq hn k⟩
  have hsplit := split_eq hn k
  rw [hP] at hsplit
  have htpos := tail_pos hn k
  have htle := tail_le hn k
  have hne : ∑' j, (1 : ℝ) / 2 ^ n j ≠ ((P : ℤ) : ℝ) / 2 ^ n k := by
    rw [hsplit, Int.cast_natCast]; linarith
  have key := hM (n k) (by omega) (P : ℤ) hne
  rw [hsplit, Int.cast_natCast, add_sub_cancel_left, abs_of_pos htpos] at key
  have hceil : 2 / ε < (n k : ℝ) := by
    have h1' : 2 / ε ≤ (⌈2 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2' : (⌈2 / ε⌉₊ : ℝ) + 1 ≤ n k := by
      exact_mod_cast (show ⌈2 / ε⌉₊ + 1 ≤ n k by omega)
    linarith
  have hexp : (1 + ε / 2) * (n k : ℝ) + 1 < n (k + 1) := by
    rw [div_lt_iff₀ hε] at hceil
    nlinarith
  have hA : (2 : ℝ) ^ ((1 + ε / 2) * (n k : ℝ)) * 2 < 2 ^ n (k + 1) := by
    rw [← Real.rpow_natCast 2 (n (k + 1))]
    calc (2 : ℝ) ^ ((1 + ε / 2) * (n k : ℝ)) * 2
        = 2 ^ ((1 + ε / 2) * (n k : ℝ) + 1) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one]
      _ < 2 ^ ((n (k + 1) : ℕ) : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
  have hB : (0 : ℝ) < 2 ^ n (k + 1) := by positivity
  have hfin : 1 ≤ (2 : ℝ) ^ ((1 + ε / 2) * (n k : ℝ)) * (2 / 2 ^ n (k + 1)) :=
    key.trans (mul_le_mul_of_nonneg_left htle (by positivity))
  rw [mul_div_assoc', le_div_iff₀ hB, one_mul] at hfin
  linarith

/-- Exactly `K + 1` exponents are at most `n_K`. -/
theorem count_at {n : ℕ → ℕ} (hn : StrictMono n) (K : ℕ) :
    ((range (n K + 1)).filter (fun k => n k ≤ n K)).card = K + 1 := by
  have hK : K ≤ n K := hn.id_le K
  have : (range (n K + 1)).filter (fun k => n k ≤ n K) = range (K + 1) := by
    ext k
    simp only [mem_filter, mem_range, hn.le_iff_le]
    constructor
    · rintro ⟨_, h⟩
      omega
    · intro h
      exact ⟨by omega, by omega⟩
  rw [this, card_range]

/-- The superpolynomial case: the digit-count bound makes the sum transcendental as soon as
`n` is not bounded by a polynomial. -/
theorem superpoly {n : ℕ → ℕ} (hn : StrictMono n) (h2 : H2)
    (hp : ¬ ∃ C t : ℕ, ∀ k, n k ≤ C * (k + 1) ^ t) :
    Transcendental ℚ (∑' k, (1 : ℝ) / 2 ^ n k) := by
  intro halg
  obtain ⟨D, hD, c, hc, hev⟩ := h2 n hn halg
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  apply hp
  refine ⟨⌈(1 / c) ^ D⌉₊ + n N0, D, fun K => ?_⟩
  by_cases hK : N0 ≤ K
  · have hKn : K ≤ n K := hn.id_le K
    have h := hN0 (n K) (by omega)
    rw [count_at hn K] at h
    have hroot : ((n K : ℝ) ^ ((1 : ℝ) / D)) ^ D = n K := by
      rw [one_div]
      exact Real.rpow_inv_natCast_pow (by positivity) (by omega)
    have h' : (n K : ℝ) ^ ((1 : ℝ) / D) ≤ (1 / c) * ((K : ℝ) + 1) := by
      rw [one_div_mul_eq_div, le_div_iff₀ hc]
      push_cast at h
      linarith
    have hx : (n K : ℝ) ≤ (1 / c) ^ D * ((K : ℝ) + 1) ^ D := by
      calc (n K : ℝ) = ((n K : ℝ) ^ ((1 : ℝ) / D)) ^ D := hroot.symm
        _ ≤ ((1 / c) * ((K : ℝ) + 1)) ^ D := pow_le_pow_left₀ (by positivity) h' D
        _ = (1 / c) ^ D * ((K : ℝ) + 1) ^ D := by rw [mul_pow]
    have hc' : ((1 / c) ^ D : ℝ) ≤ (⌈(1 / c) ^ D⌉₊ : ℝ) := Nat.le_ceil _
    have hfin : (n K : ℝ) ≤ ((⌈(1 / c) ^ D⌉₊ : ℝ) + (n N0 : ℝ)) * ((K : ℝ) + 1) ^ D := by
      calc (n K : ℝ) ≤ (1 / c) ^ D * ((K : ℝ) + 1) ^ D := hx
        _ ≤ (⌈(1 / c) ^ D⌉₊ : ℝ) * ((K : ℝ) + 1) ^ D := by gcongr
        _ ≤ ((⌈(1 / c) ^ D⌉₊ : ℝ) + (n N0 : ℝ)) * ((K : ℝ) + 1) ^ D := by
          gcongr
          exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    exact_mod_cast hfin
  · push Not at hK
    have h1 : n K ≤ n N0 := hn.monotone hK.le
    have h2 : 1 ≤ (K + 1) ^ D := Nat.one_le_pow _ _ (by omega)
    calc n K ≤ n N0 := h1
      _ ≤ (⌈(1 / c) ^ D⌉₊ + n N0) * 1 := by omega
      _ ≤ (⌈(1 / c) ^ D⌉₊ + n N0) * (K + 1) ^ D := Nat.mul_le_mul_left _ h2

theorem main : H1 → H2 → H3 → type_of% @Erdos247.erdos_247 := by
  intro h1 h2 h3 n hn hlim
  by_cases hpoly : ∃ C t : ℕ, ∀ k, n k ≤ C * (k + 1) ^ t
  · by_cases hratio : Tendsto (fun k => (n (k + 1) : ℝ) / n k) atTop (nhds 1)
    · exact h3 n hn hlim hratio hpoly
    · exact lacunary hn h1 hratio
  · exact superpoly hn h2 hpoly

end OMA.R_Erdos247_erdos_247_R1

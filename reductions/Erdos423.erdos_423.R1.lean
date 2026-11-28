import FormalConjectures.ErdosProblems.«423»

-- Credit: @PetrouilFan

open Filter Asymptotics Topology
open Erdos423

/-!
Erdős 423 asks whether the Hofstadter sequence satisfies `a n = n + o(n)`.
The upstream file proves two structural facts: `IsHofstadterSeq.le_apply` (a lower
bound `n ≤ a n`) and `erdos_423.variants.nondecreasing` (the gap `a n - n` is
nondecreasing). We isolate those proved base cases in H1 and H2. The only open
content left in H3 is a dyadic (lacunary) version of the o(n) estimate. By
monotonicity of the gap, dyadic control at `2^k` with bounded ratio `2` upgrades
to control at every `n`, so `main` is a genuine transfer, not a restatement.
-/

namespace OMA.R_Erdos423_erdos_423_R1

-- Proved upstream: IsHofstadterSeq.le_apply.
def H1 : Prop :=
  ∀ a : ℕ → ℕ, IsHofstadterSeq a → ∀ n : ℕ, 1 ≤ n → n ≤ a n

-- Proved upstream: erdos_423.variants.nondecreasing (Bolan-Tang).
def H2 : Prop :=
  ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    ∀ n m : ℕ, 1 ≤ n → n ≤ m → a n - n ≤ a m - m

-- Open: the o(n) estimate only along the dyadic subsequence 2^k.
def H3 : Prop :=
  ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    Tendsto (fun k : ℕ => ((a (2 ^ k) - 2 ^ k : ℕ) : ℝ) / (2 ^ k : ℝ)) atTop (𝓝 0)

theorem main : H1 → H2 → H3 → type_of% @Erdos423.erdos_423 := by
  intro hlow hmono hdy a ha
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have heps : 0 < c / 4 := by positivity
  rcases (Metric.tendsto_atTop.1 (hdy a ha)) (c / 4) heps with ⟨K, hK⟩
  filter_upwards [eventually_ge_atTop (2 ^ K)] with n hn
  have hn1 : 1 ≤ n := by
    have : 0 < 2 ^ K := by positivity
    omega
  let k := Nat.log 2 n
  have hn_ne : n ≠ 0 := by omega
  have h2k_le : 2 ^ k ≤ n := by
    simpa [k] using Nat.pow_log_le_self 2 hn_ne
  have hn_lt : n < 2 ^ (k + 1) := by
    simpa [k, Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  have hk_ge : K ≤ k := by
    exact Nat.le_log_of_pow_le (by norm_num) hn
  have hm_ge : K ≤ k + 1 := by omega
  have hdist := hK (k + 1) hm_ge
  have hlt : (((a (2 ^ (k + 1)) - 2 ^ (k + 1) : ℕ) : ℝ) / (2 ^ (k + 1) : ℝ)) < c / 4 := by
    simpa [Real.dist_eq] using hdist
  have hdenpos : (0 : ℝ) < (2 ^ (k + 1) : ℝ) := by positivity
  have hgap_le : (((a (2 ^ (k + 1)) - 2 ^ (k + 1) : ℕ) : ℝ)) ≤ (c / 4) * (2 ^ (k + 1) : ℝ) := by
    exact le_of_lt ((div_lt_iff₀ hdenpos).1 hlt)
  have hpow_le : 2 ^ (k + 1) ≤ 2 * n := by
    rw [pow_succ]
    omega
  have hbound : ((a n - n : ℕ) : ℝ) ≤ (c / 2) * (n : ℝ) := by
    calc
      ((a n - n : ℕ) : ℝ) ≤ ((a (2 ^ (k + 1)) - 2 ^ (k + 1) : ℕ) : ℝ) := by
        exact_mod_cast (hmono a ha n (2 ^ (k + 1)) hn1 (le_of_lt hn_lt))
      _ ≤ (c / 4) * (2 ^ (k + 1) : ℝ) := hgap_le
      _ ≤ (c / 4) * (2 * n : ℝ) := by gcongr; exact_mod_cast hpow_le
      _ = (c / 2) * (n : ℝ) := by ring
  have hcast : (a n : ℝ) - (n : ℝ) = ((a n - n : ℕ) : ℝ) := by
    rw [Nat.cast_sub (hlow a ha n hn1)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hcast,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((a n - n : ℕ) : ℝ)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith

end OMA.R_Erdos423_erdos_423_R1

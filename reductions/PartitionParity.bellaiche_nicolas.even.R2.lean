import FormalConjectures.Paper.PartitionParity
import Mathlib

/-!
Bellaïche and Nicolas, *Parité des coefficients de formes modulaires*, §6, Theorem 5.
Write A(x) for the number of even partition values through x and W for the number of
odd coefficients of Δ^k through 8x+k. Modulo 2, Δ is the sum of the odd square powers of q.

H1 is the partition convolution estimate (6.9), weakened to constant 16. If
D = 2^t ≤ √x/16 then β = √(3/2) D/√x ≤ 1/8. For W ≤ x/8 the two parenthesized
factors in (6.9) are at least 2/3 and 1/2, respectively.

H2 is the sparsity estimate for the modular form alone. In (6.6) take d = 2t
and α = 1/2. This puts D between (log log x)/2 and log log x + 8, and (6.10)
bounds W/x by a constant times a negative power of log(8x), uniformly for that t.
-/

namespace OMA.R_PartitionParity_bellaiche_nicolas_even_R2

open Filter Asymptotics

/-- Small coefficient support at a given scale forces many even partition values. -/
def H1 : Prop :=
  let delta : PowerSeries (ZMod 2) := PowerSeries.mk fun n =>
    if n % 2 = 1 ∧ n.sqrt ^ 2 = n then 1 else 0
  ∀ᶠ x : ℝ in atTop, ∀ t : ℕ, 0 < t → 16 * (2 : ℝ) ^ t ≤ Real.sqrt x →
    let k : ℕ := (4 ^ t - 1) / 3
    (({n : ℕ | (n : ℝ) ≤ 8 * x + (k : ℝ) ∧
      PowerSeries.coeff n (delta ^ (k : ℕ)) ≠ 0}.ncard : ℝ) ≤ x / 8) →
    Real.sqrt x * (2 : ℝ) ^ t ≤
      16 * ({n : ℕ | (n : ℝ) ≤ x ∧ Even (Nat.partitionNumber n)}.ncard : ℝ)

/-- A power of Δ has small coefficient support at a scale comparable to log log x. -/
def H2 : Prop :=
  let delta : PowerSeries (ZMod 2) := PowerSeries.mk fun n =>
    if n % 2 = 1 ∧ n.sqrt ^ 2 = n then 1 else 0
  ∀ᶠ x : ℝ in atTop, ∃ t : ℕ, 0 < t ∧ Real.log (Real.log x) ≤ 2 * (2 : ℝ) ^ t ∧
    16 * (2 : ℝ) ^ t ≤ Real.sqrt x ∧
    let k : ℕ := (4 ^ t - 1) / 3
    ({n : ℕ | (n : ℝ) ≤ 8 * x + (k : ℝ) ∧
      PowerSeries.coeff n (delta ^ (k : ℕ)) ≠ 0}.ncard : ℝ) ≤ x / 8

theorem main : H1 → H2 → type_of% @PartitionParity.bellaiche_nicolas.even := by
  intro h1 h2
  apply IsBigO.of_bound 32
  unfold H1 at h1
  unfold H2 at h2
  filter_upwards [h1, h2, eventually_ge_atTop (Real.exp 1)] with x hconv hscale hx
  obtain ⟨t, ht, hlower, hupper, hsparse⟩ := hscale
  have hcount := hconv t ht hupper hsparse
  have hlog : 1 ≤ Real.log x := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) hx
  have hprod := mul_le_mul_of_nonneg_left hlower (Real.sqrt_nonneg x)
  rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (Real.log_nonneg hlog)),
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
  linarith only [hprod, hcount]

end OMA.R_PartitionParity_bellaiche_nicolas_even_R2

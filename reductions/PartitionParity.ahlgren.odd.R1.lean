import FormalConjectures.Paper.PartitionParity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# Reduction of `PartitionParity.ahlgren.odd`

Following S. Ahlgren (*Distribution of parity of the partition function in arithmetic
progressions*, Indag. Math. 10 (1999), 173–181) and C.-S. Radu (*A proof of Subbarao's conjecture*,
J. Reine Angew. Math. 672 (2012), 161–175), we reduce the lower bound
$$\#\{n \le X : n \equiv r \pmod t,\; p(n) \text{ odd}\} \gg \frac{\sqrt{X}}{\log X}$$
to its two classical modular-form pillars:
1. `H1`: **Radu's theorem (2012)**: every arithmetic progression `r (mod t)` (`0 < t`) contains at
   least one `n` with `Odd (partitionNumber n)`.
2. `H2`: **Ahlgren's seeded theta-convolution lower bound (1999)**: given a seed `n₀ ≡ r [MOD t]`
   with `Odd (partitionNumber n₀)`, there exist `d > 0` with `t ∣ d` and `c > 0` such that for
   sufficiently large `X`, the odd-square convolution
   $\sum_{d(2i+1)^2 \le n} p(n - d(2i+1)^2)$ is odd for at least $c X / \log X$ values of
   $n \le X$ with $n \equiv r \pmod t$.

Inside `main`, we prove that an odd finite sum contains an odd summand, prove the injection from
odd-convolution indices `n ≤ X` (`n ≡ r [MOD t]`) into odd-partition indices `m ≤ X`
(`m ≡ r [MOD t]`) paired with shift indices `i ≤ ⌊√X⌋`, deduce the cardinality inequality
`convCount ≤ oddCount * (⌊√X⌋ + 1)`, and convert `H1` + `H2` into the exact `Asymptotics.IsBigO`
bound `(fun X ↦ √X / log X) =O[atTop] ...`.

Thanks to @MechaNuggan for the convolution-support cardinality bound and Radu/Ahlgren split notes.
Credit: @tkaiman
-/

namespace OMA.R_PartitionParity_ahlgren_odd_R1

open PartitionParity Nat Real Filter Asymptotics Finset
open scoped BigOperators Classical

/- ### Step 1: Parity extraction and convolution-support injection -/

private lemma exists_odd_of_odd_sum {α : Type*} (s : Finset α) (f : α → ℕ)
    (hodd : Odd (∑ x ∈ s, f x)) : ∃ x ∈ s, Odd (f x) := by
  by_contra h
  push Not at h
  have hall : ∀ x ∈ s, Even (f x) := fun x hx => Nat.not_odd_iff_even.mp (h x hx)
  have heven : Even (∑ x ∈ s, f x) := by
    have aux : ∀ t : Finset α, (∀ x ∈ t, Even (f x)) → Even (∑ x ∈ t, f x) := by
      intro t
      induction t using Finset.induction_on with
      | empty => intro _; simp
      | @insert a t ha ih =>
        intro ht
        rw [Finset.sum_insert ha]
        exact (ht a (Finset.mem_insert_self a t)).add
          (ih fun x hx => ht x (Finset.mem_insert_of_mem hx))
    exact aux s hall
  exact (Nat.not_odd_iff_even.mpr heven) hodd

private lemma thetaConv_card_le_odd_mul_sqrt (r t d : ℕ) (hd : 0 < d) (htd : t ∣ d)
    (X : ℝ) (hX : 1 ≤ X) :
    ({n : ℕ | (n : ℝ) ≤ X ∧ n ≡ r [MOD t] ∧
      Odd (∑ i ∈ (Finset.range (n + 1)).filter (fun i => d * (2 * i + 1) ^ 2 ≤ n),
        partitionNumber (n - d * (2 * i + 1) ^ 2))}.ncard : ℝ) ≤
    ({m : ℕ | (m : ℝ) ≤ X ∧ m ≡ r [MOD t] ∧ Odd (partitionNumber m)}.ncard : ℝ) *
      (2 * √X) := by
  set S_conv : Set ℕ := {n : ℕ | (n : ℝ) ≤ X ∧ n ≡ r [MOD t] ∧
    Odd (∑ i ∈ (Finset.range (n + 1)).filter (fun i => d * (2 * i + 1) ^ 2 ≤ n),
      partitionNumber (n - d * (2 * i + 1) ^ 2))}
  set S_odd : Set ℕ := {m : ℕ | (m : ℝ) ≤ X ∧ m ≡ r [MOD t] ∧ Odd (partitionNumber m)}
  set N : ℕ := ⌊X⌋₊
  set K : ℕ := ⌊√X⌋₊ + 1
  have hS_conv_fin : S_conv.Finite := by
    refine (Set.finite_Iic N).subset fun n hn => ?_
    exact Nat.le_floor hn.1
  have hS_odd_fin : S_odd.Finite := by
    refine (Set.finite_Iic N).subset fun m hm => ?_
    exact Nat.le_floor hm.1
  let F_conv : Finset ℕ := hS_conv_fin.toFinset
  let F_odd : Finset ℕ := hS_odd_fin.toFinset
  have hhex : ∀ n ∈ F_conv,
      ∃ p : ℕ × ℕ, p ∈ F_odd ×ˢ Finset.range K ∧ p.1 + d * (2 * p.2 + 1) ^ 2 = n := by
    intro n hn
    have hn' := hS_conv_fin.mem_toFinset.mp hn
    obtain ⟨i, hi_mem, hi_odd⟩ := exists_odd_of_odd_sum _ _ hn'.2.2
    have hi_le : d * (2 * i + 1) ^ 2 ≤ n := (Finset.mem_filter.mp hi_mem).2
    let m : ℕ := n - d * (2 * i + 1) ^ 2
    have hmn : m + d * (2 * i + 1) ^ 2 = n := Nat.sub_add_cancel hi_le
    have hm_leX : (m : ℝ) ≤ X := by
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n _
      linarith [hn'.1]
    have hm_mod : m ≡ r [MOD t] := by
      have hdvd : t ∣ d * (2 * i + 1) ^ 2 := dvd_mul_of_dvd_left htd _
      have h1 : m + d * (2 * i + 1) ^ 2 ≡ m + 0 [MOD t] :=
        Nat.ModEq.add_left m (Nat.modEq_zero_iff_dvd.mpr hdvd)
      rw [hmn, add_zero] at h1
      exact h1.symm.trans hn'.2.1
    have hi_ltK : i < K := by
      have hi_sq : i ^ 2 ≤ n := by
        have h1 : i ^ 2 ≤ (2 * i + 1) ^ 2 := by nlinarith
        have h2 : (2 * i + 1) ^ 2 ≤ d * (2 * i + 1) ^ 2 := Nat.le_mul_of_pos_left _ hd
        omega
      have hi_R : (i : ℝ) ^ 2 ≤ X := by
        have : ((i ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi_sq
        rw [Nat.cast_pow] at this
        linarith [hn'.1]
      have hi_sqrt : (i : ℝ) ≤ √X := by
        rw [← Real.sqrt_sq (Nat.cast_nonneg i)]
        exact Real.sqrt_le_sqrt hi_R
      have hi_fl : i ≤ ⌊√X⌋₊ := Nat.le_floor hi_sqrt
      omega
    refine ⟨(m, i), Finset.mem_product.mpr ⟨hS_odd_fin.mem_toFinset.mpr ⟨hm_leX, hm_mod, hi_odd⟩,
      Finset.mem_range.mpr hi_ltK⟩, hmn⟩
  have hcard_le : F_conv.card ≤ F_odd.card * K := by
    have hsub : F_conv ⊆ (F_odd ×ˢ Finset.range K).image (fun p => p.1 + d * (2 * p.2 + 1) ^ 2) := by
      intro n hn
      obtain ⟨p, hp_mem, hp_eq⟩ := hhex n hn
      exact Finset.mem_image.mpr ⟨p, hp_mem, hp_eq⟩
    calc F_conv.card
        ≤ ((F_odd ×ˢ Finset.range K).image (fun p => p.1 + d * (2 * p.2 + 1) ^ 2)).card :=
          Finset.card_le_card hsub
      _ ≤ (F_odd ×ˢ Finset.range K).card := Finset.card_image_le
      _ = F_odd.card * K := by rw [Finset.card_product, Finset.card_range]
  have hK_le : (K : ℝ) ≤ 2 * √X := by
    have hsqrt1 : (1 : ℝ) ≤ √X := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hX
    have hfl : (⌊√X⌋₊ : ℝ) ≤ √X := Nat.floor_le (Real.sqrt_nonneg X)
    dsimp [K]
    push_cast
    linarith
  rw [Set.ncard_eq_toFinset_card S_conv hS_conv_fin, Set.ncard_eq_toFinset_card S_odd hS_odd_fin]
  have hcardR : (F_conv.card : ℝ) ≤ (F_odd.card : ℝ) * (K : ℝ) := by exact_mod_cast hcard_le
  exact hcardR.trans (mul_le_mul_of_nonneg_left hK_le (Nat.cast_nonneg _))

/- ### Hypotheses and main reduction theorem -/

/-- **Radu's theorem** (C.-S. Radu, J. Reine Angew. Math. 672 (2012), 161–175):
every arithmetic progression `r (mod t)` (`0 < t`) contains at least one natural number `n` whose
partition number `partitionNumber n` is odd. -/
def H1 : Prop :=
  ∀ (r t : ℕ), 0 < t → ∃ n : ℕ, n ≡ r [MOD t] ∧ Odd (partitionNumber n)

/-- **Ahlgren's seeded theta-convolution lower bound** (S. Ahlgren, Indag. Math. 10 (1999),
Theorem 1(b)): given `0 < t` and a seed `n₀ ≡ r [MOD t]` with `Odd (partitionNumber n₀)`, there
exist a positive multiple `d` of `t` and a constant `c > 0` such that eventually as `X → ∞`, the
odd-square convolution `∑_{d(2i+1)^2 ≤ n} partitionNumber (n - d(2i+1)^2)` is odd for at least
`c * X / log X` values of `n ≤ X` with `n ≡ r [MOD t]`. -/
def H2 : Prop :=
  ∀ (r t : ℕ), 0 < t → (∃ n₀ : ℕ, n₀ ≡ r [MOD t] ∧ Odd (partitionNumber n₀)) →
    ∃ (d : ℕ) (c : ℝ), 0 < d ∧ t ∣ d ∧ 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      c * X / X.log ≤
        ({n : ℕ | (n : ℝ) ≤ X ∧ n ≡ r [MOD t] ∧
          Odd (∑ i ∈ (Finset.range (n + 1)).filter (fun i => d * (2 * i + 1) ^ 2 ≤ n),
            partitionNumber (n - d * (2 * i + 1) ^ 2))}.ncard : ℝ)

theorem main : H1 → H2 → type_of% @PartitionParity.ahlgren.odd := by
  intro h1 h2 r t ht
  obtain ⟨d, c, hd, htd, hc, hev⟩ := h2 r t ht (h1 r t ht)
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 / c, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (2 : ℝ)] with X hX_conv hX2
  have hX1 : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  have hsqrt_pos : 0 < √X := Real.sqrt_pos.mpr hXpos
  have hlog_pos : 0 < X.log := Real.log_pos (by linarith)
  have hbound := thetaConv_card_le_odd_mul_sqrt r t d hd htd X hX1
  have htrans : c * X / X.log ≤
      ({n : ℕ | (n : ℝ) ≤ X ∧ n ≡ r [MOD t] ∧ Odd (partitionNumber n)}.ncard : ℝ) * (2 * √X) :=
    hX_conv.trans hbound
  have hsq : √X * √X = X := Real.mul_self_sqrt hXpos.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hsqrt_pos.le hlog_pos.le),
    abs_of_nonneg (Nat.cast_nonneg _)]
  have hkey : √X / X.log ≤
      (2 / c) * ({n : ℕ | (n : ℝ) ≤ X ∧ n ≡ r [MOD t] ∧ Odd (partitionNumber n)}.ncard : ℝ) := by
    have hmul : c * (√X / X.log) * (2 * √X) ≤
        c * ((2 / c) * ({n : ℕ | (n : ℝ) ≤ X ∧ n ≡ r [MOD t] ∧ Odd (partitionNumber n)}.ncard : ℝ)) *
          (2 * √X) := by
      have hL : c * (√X / X.log) * (2 * √X) = 2 * (c * X / X.log) := by
        have : c * (√X / X.log) * (2 * √X) = 2 * (c * (√X * √X) / X.log) := by ring
        rw [this, hsq]
      have hR : c * ((2 / c) * ({n : ℕ | (n : ℝ) ≤ X ∧ n ≡ r [MOD t] ∧ Odd (partitionNumber n)}.ncard : ℝ)) *
          (2 * √X) =
          2 * (({n : ℕ | (n : ℝ) ≤ X ∧ n ≡ r [MOD t] ∧ Odd (partitionNumber n)}.ncard : ℝ) * (2 * √X)) := by
        field_simp [hc.ne']
      rw [hL, hR]
      linarith
    have hpos_factor : 0 < c * (2 * √X) := by positivity
    have hmul' : (c * (2 * √X)) * (√X / X.log) ≤
        (c * (2 * √X)) * ((2 / c) *
          ({n : ℕ | (n : ℝ) ≤ X ∧ n ≡ r [MOD t] ∧ Odd (partitionNumber n)}.ncard : ℝ)) := by
      linarith
    exact le_of_mul_le_mul_left hmul' hpos_factor
  exact hkey

end OMA.R_PartitionParity_ahlgren_odd_R1

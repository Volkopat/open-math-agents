import OMAReductions.R_Erdos542_erdos_542_variants_only_two_R1
import Mathlib

-- Reduction Erdos542.erdos_542.variants.only_two.R1.H3.R1 of step Erdos542.erdos_542.variants.only_two.R1.H3
-- Credit: @rickmanelius

/-!
# The step without a small member, split by the smallest member

The step: for `n ≥ 12` and an lcm-free `A ⊆ {1, …, n}` (distinct members have least common
multiple above `n`) whose members all exceed `√n`, the fractional loss `∑ (n mod a) / a` is at
most the number of uncovered integers. By the counting identity of the parent file this is
`∑ 1/a ≤ 1`.

Proved here, with no hypothesis (`top_level`): the top level, every member above `n / 3`. A member
`a ≤ n / 2` excludes `2 a` (since `lcm (a, 2 a) = 2 a ≤ n`), and `2 a` lies in `(n / 2, n]`, so
`∑ 1/a ≤ H(n/2, n] + H(n/3, n/2] / 2 ≤ log (n / h) + log (h / t) / 2` with `h = ⌊n/2⌋`,
`t = ⌊n/3⌋`, and `n ^ 2 ≤ 7.3 h t < e ^ 2 h t` for `n ≥ 12`. The limit of the bound is
`log 2 + (log (3/2)) / 2 ≈ 0.896`.

What is left, by the smallest member:
* `H1`: the next level, every member above `n / 4` and some member at most `n / 3`;
* `H2`: some member at most `n / 4` (all members still above `√n`), the open core.
-/

open Finset

namespace OMA.R_Erdos542_erdos_542_variants_only_two_R1_H3_R1

/-- The next level: all members above `n / 4`, some member at most `n / 3`. -/
def H1 : Prop :=
  ∀ (n : ℕ) (A : Finset ℕ), 12 ≤ n → Erdos542.IsLcmFree n A → (∀ a ∈ A, n < a * a) →
    (∀ a ∈ A, n < 4 * a) → (∃ a ∈ A, 3 * a ≤ n) →
    ∑ a ∈ A, ((n % a : ℕ) : ℚ) / a ≤ ((Erdos542.uncovered n A).card : ℚ)

/-- The open core: some member at most `n / 4`, all members above `√n`. -/
def H2 : Prop :=
  ∀ (n : ℕ) (A : Finset ℕ), 12 ≤ n → Erdos542.IsLcmFree n A → (∀ a ∈ A, n < a * a) →
    (∃ a ∈ A, 4 * a ≤ n) →
    ∑ a ∈ A, ((n % a : ℕ) : ℚ) / a ≤ ((Erdos542.uncovered n A).card : ℚ)

theorem harmonic_Ioc_le (h : ℕ) (hh : 1 ≤ h) : ∀ n, h ≤ n →
    ∑ m ∈ Ioc h n, (1 : ℝ) / m ≤ Real.log n - Real.log h := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ioc_succ_top hk]
    have hk1 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hk2 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hstep : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log k := by
      have h0 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k : ℝ) / ((k + 1 : ℕ) : ℝ) by positivity)
      rw [Real.log_div hk1.ne' hk2.ne'] at h0
      have e : (k : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 = -(1 / ((k + 1 : ℕ) : ℝ)) := by
        push_cast
        field_simp
        ring
      linarith
    linarith

theorem sum_inv_le_levels (n : ℕ) (A : Finset ℕ) (hA : Erdos542.IsLcmFree n A)
    (htop : ∀ a ∈ A, n < 3 * a) :
    ∑ a ∈ A, (1 : ℝ) / a ≤
      ∑ m ∈ Ioc (n / 2) n, (1 : ℝ) / m + (1 / 2) * ∑ m ∈ Ioc (n / 3) (n / 2), (1 : ℝ) / m := by
  classical
  set A1 := A.filter (fun a => 2 * a ≤ n) with hA1
  set A2 := A.filter (fun a => ¬ 2 * a ≤ n) with hA2
  have hsplit : ∑ a ∈ A, (1 : ℝ) / a = ∑ a ∈ A1, (1 : ℝ) / a + ∑ a ∈ A2, (1 : ℝ) / a :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  have hmemA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ n := fun a ha => mem_Icc.mp (hA.1 ha)
  have hA1sub : A1 ⊆ Ioc (n / 3) (n / 2) := by
    intro a ha
    rw [hA1, mem_filter] at ha
    have := htop a ha.1
    rw [mem_Ioc]
    constructor <;> omega
  have hA2sub : A2 ⊆ Ioc (n / 2) n := by
    intro a ha
    rw [hA2, mem_filter] at ha
    have := hmemA a ha.1
    rw [mem_Ioc]
    constructor <;> omega
  set D := A1.image (fun a => 2 * a) with hD
  have hDsub : D ⊆ Ioc (n / 2) n := by
    intro m hm
    rw [hD, mem_image] at hm
    obtain ⟨a, ha, rfl⟩ := hm
    rw [hA1, mem_filter] at ha
    have := htop a ha.1
    rw [mem_Ioc]
    constructor <;> omega
  have hdisj : Disjoint A2 D := by
    rw [disjoint_left]
    intro b hb hbD
    rw [hD, mem_image] at hbD
    obtain ⟨a, ha, rfl⟩ := hbD
    rw [hA1, mem_filter] at ha
    rw [hA2, mem_filter] at hb
    have ha1 := (hmemA a ha.1).1
    have hne : a ≠ 2 * a := by omega
    have hl : n < Nat.lcm a (2 * a) := hA.2 (mem_coe.mpr ha.1) (mem_coe.mpr hb.1) hne
    rw [Nat.lcm_eq_right (Dvd.intro_left 2 rfl)] at hl
    omega
  have hD_sum : ∑ m ∈ D, (1 : ℝ) / m = ∑ a ∈ A1, (1 : ℝ) / (2 * a) := by
    rw [hD, sum_image (fun x _ y _ h => by omega)]
    push_cast
    rfl
  have hunion : ∑ b ∈ A2, (1 : ℝ) / b + ∑ m ∈ D, (1 : ℝ) / m ≤
      ∑ m ∈ Ioc (n / 2) n, (1 : ℝ) / m := by
    rw [← sum_union hdisj]
    exact sum_le_sum_of_subset_of_nonneg (union_subset hA2sub hDsub) (fun _ _ _ => by positivity)
  have hA1le : ∑ a ∈ A1, (1 : ℝ) / a ≤ ∑ m ∈ Ioc (n / 3) (n / 2), (1 : ℝ) / m :=
    sum_le_sum_of_subset_of_nonneg hA1sub (fun _ _ _ => by positivity)
  have hhalf : ∑ a ∈ A1, (1 : ℝ) / (2 * a) = (1 / 2) * ∑ a ∈ A1, (1 : ℝ) / a := by
    rw [mul_sum]
    refine sum_congr rfl (fun a _ => ?_)
    ring
  calc ∑ a ∈ A, (1 : ℝ) / a = ∑ a ∈ A1, (1 : ℝ) / a + ∑ a ∈ A2, (1 : ℝ) / a := hsplit
    _ ≤ ∑ a ∈ A1, (1 : ℝ) / a +
          (∑ m ∈ Ioc (n / 2) n, (1 : ℝ) / m - ∑ a ∈ A1, (1 : ℝ) / (2 * a)) := by
        rw [← hD_sum]
        linarith
    _ = ∑ m ∈ Ioc (n / 2) n, (1 : ℝ) / m + (1 / 2) * ∑ a ∈ A1, (1 : ℝ) / a := by
        rw [hhalf]
        ring
    _ ≤ _ := by gcongr

theorem levels_lt_one (n : ℕ) (hn : 12 ≤ n) :
    ∑ m ∈ Ioc (n / 2) n, (1 : ℝ) / m + (1 / 2) * ∑ m ∈ Ioc (n / 3) (n / 2), (1 : ℝ) / m < 1 := by
  have h1 := harmonic_Ioc_le (n / 2) (by omega) n (by omega)
  have h2 := harmonic_Ioc_le (n / 3) (by omega) (n / 2) (by omega)
  have hkey : 10 * n ^ 2 ≤ 73 * (n / 2) * (n / 3) := by
    rcases Nat.lt_or_ge n 17 with hlt | hge
    · interval_cases n <;> norm_num
    · have e1 : n ≤ 2 * (n / 2) + 1 := by omega
      have e2 : n ≤ 3 * (n / 3) + 2 := by omega
      have e3 : 8 ≤ n / 2 := by omega
      have e4 : 5 ≤ n / 3 := by omega
      have e5 : 3 * (n / 3) ≤ 2 * (n / 2) + 1 := by omega
      nlinarith [Nat.mul_le_mul e1 e2]
  have hpos_h : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n / 2 by omega)
  have hpos_t : (0 : ℝ) < ((n / 3 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n / 3 by omega)
  have hpos_n : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlog : 2 * (Real.log n - Real.log ((n / 2 : ℕ) : ℝ)) +
      (Real.log ((n / 2 : ℕ) : ℝ) - Real.log ((n / 3 : ℕ) : ℝ)) < 2 := by
    have hcomb : 2 * (Real.log n - Real.log ((n / 2 : ℕ) : ℝ)) +
        (Real.log ((n / 2 : ℕ) : ℝ) - Real.log ((n / 3 : ℕ) : ℝ)) =
        Real.log ((n : ℝ) ^ 2 / (((n / 2 : ℕ) : ℝ) * ((n / 3 : ℕ) : ℝ))) := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul hpos_h.ne' hpos_t.ne',
        Real.log_pow]
      push_cast
      ring
    rw [hcomb]
    have hle : (n : ℝ) ^ 2 / (((n / 2 : ℕ) : ℝ) * ((n / 3 : ℕ) : ℝ)) ≤ 73 / 10 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h' : ((10 * n ^ 2 : ℕ) : ℝ) ≤ ((73 * (n / 2) * (n / 3) : ℕ) : ℝ) := by
        exact_mod_cast hkey
      push_cast at h'
      linarith
    have he : (73 / 10 : ℝ) < Real.exp 2 := by
      have h9 := Real.exp_one_gt_d9
      have h2' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [h2']
      nlinarith
    calc Real.log ((n : ℝ) ^ 2 / (((n / 2 : ℕ) : ℝ) * ((n / 3 : ℕ) : ℝ)))
        ≤ Real.log (73 / 10) := Real.log_le_log (by positivity) hle
      _ < 2 := by
        rw [Real.log_lt_iff_lt_exp (by norm_num)]
        exact he
  linarith

theorem top_level (n : ℕ) (A : Finset ℕ) (hn : 12 ≤ n) (hA : Erdos542.IsLcmFree n A)
    (htop : ∀ a ∈ A, n < 3 * a) :
    ∑ a ∈ A, ((n % a : ℕ) : ℚ) / a ≤ ((Erdos542.uncovered n A).card : ℚ) := by
  have hsum : ∑ a ∈ A, (1 : ℝ) / a < 1 :=
    (sum_inv_le_levels n A hA htop).trans_lt (levels_lt_one n hn)
  have hcount := OMA.R_Erdos542_erdos_542_variants_only_two_R1.count_identity hA
  have hpos : ∀ a ∈ A, 0 < a := fun a ha => by
    have := mem_Icc.mp (hA.1 ha)
    omega
  have hreal : ∑ a ∈ A, ((n % a : ℕ) : ℝ) / a ≤ ((Erdos542.uncovered n A).card : ℝ) := by
    have hterm : ∀ a ∈ A, ((n % a : ℕ) : ℝ) / a = n * ((1 : ℝ) / a) - ((n / a : ℕ) : ℝ) := by
      intro a ha
      have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (hpos a ha).ne'
      have hdm : (n : ℝ) = (a : ℝ) * ((n / a : ℕ) : ℝ) + ((n % a : ℕ) : ℝ) := by
        exact_mod_cast (Nat.div_add_mod n a).symm
      field_simp
      linarith
    rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum]
    have hc : (∑ a ∈ A, ((n / a : ℕ) : ℝ)) + ((Erdos542.uncovered n A).card : ℝ) = n := by
      exact_mod_cast hcount
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hcast : ((∑ a ∈ A, ((n % a : ℕ) : ℚ) / a : ℚ) : ℝ) = ∑ a ∈ A, ((n % a : ℕ) : ℝ) / a := by
    push_cast
    rfl
  have : ((∑ a ∈ A, ((n % a : ℕ) : ℚ) / a : ℚ) : ℝ) ≤ (((Erdos542.uncovered n A).card : ℚ) : ℝ) := by
    rw [hcast]
    push_cast
    exact hreal
  exact_mod_cast this

theorem main : H1 → H2 → OMA.R_Erdos542_erdos_542_variants_only_two_R1.H3 := by
  intro h1 h2
  unfold OMA.R_Erdos542_erdos_542_variants_only_two_R1.H3
  intro n A hn hA hsq
  by_cases htop : ∀ a ∈ A, n < 3 * a
  · exact top_level n A hn hA htop
  · push Not at htop
    by_cases hmid : ∀ a ∈ A, n < 4 * a
    · exact h1 n A hn hA hsq hmid htop
    · push Not at hmid
      exact h2 n A hn hA hsq hmid

end OMA.R_Erdos542_erdos_542_variants_only_two_R1_H3_R1

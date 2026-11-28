import FormalConjectures.Wikipedia.ChowlaLiouvilleConjecture
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
Separate the analytic short-interval estimate from a finite Fourier inequality.
Theorem 1.3 of Matomäki, Radziwiłł and Tao (arXiv:1503.05121) supplies the
short-interval input after bounding each exponential sum by its length.
For the finite inequality, choose the signs of the shift correlations,
apply Cauchy–Schwarz, and average the local convolution energies over
windows of length twice the shift-block length. Parseval bounds these
energies by the short-interval Fourier sums.
-/

namespace OMA.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_averaged_two_point_uniform_R1

open Finset Filter
open scoped Topology

theorem sum_range_le_of_blocks (f : ℕ → ℝ) (H m : ℕ) {e : ℝ} (he : 0 ≤ e)
    (hm : 0 < m) (hbounded : ∀ i < H, f i ≤ 1)
    (hblock : ∀ b, b + m ≤ H → (∑ i ∈ range m, f (b + i)) ≤ m * e) :
    (∑ i ∈ range H, f i) ≤ H * e + m := by
  have hfull : ∀ q : ℕ, q * m ≤ H → (∑ i ∈ range (q * m), f i) ≤ (q * m : ℕ) * e := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      intro hq
      rw [Nat.succ_mul] at hq ⊢
      rw [sum_range_add, Nat.cast_add, add_mul]
      exact add_le_add (ih (by omega)) (hblock (q * m) hq)
  let q := H / m
  let r := H % m
  have hsplit : q * m + r = H := by
    dsimp [q, r]
    simpa only [Nat.mul_comm (H / m) m] using Nat.div_add_mod H m
  have hq : q * m ≤ H := by omega
  have htail : (∑ i ∈ range r, f (q * m + i)) ≤ r := by
    calc
      _ ≤ ∑ _i ∈ range r, (1 : ℝ) := sum_le_sum fun i hi =>
        hbounded _ (by have := mem_range.mp hi; omega)
      _ = _ := by simp
  have hqm : ((q * m : ℕ) : ℝ) * e ≤ (H : ℝ) * e := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hq) he
  have hr : (r : ℝ) ≤ m := by exact_mod_cast (Nat.mod_lt H hm).le
  calc
    (∑ i ∈ range H, f i) = (∑ i ∈ range (q * m), f i) + ∑ i ∈ range r, f (q * m + i) := by
      rw [← hsplit, sum_range_add]
    _ ≤ _ := add_le_add ((hfull q hq).trans hqm) (htail.trans hr)

theorem average_tendsto_of_short_blocks (f : ℕ → ℕ → ℝ) (H : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (hHN : ∀ᶠ N in atTop, H N ≤ N)
    (hf : ∀ N i, 0 ≤ f N i ∧ f N i ≤ 1)
    (hblock : ∀ e : ℝ, 0 < e → ∃ M : ℕ, ∀ᶠ N in atTop,
      ∀ m : ℕ, M ≤ m → m * m ≤ N → ∀ b, b + m ≤ N →
        (∑ i ∈ range m, f N (b + i)) ≤ m * e) :
    Tendsto (fun N => (∑ i ∈ range (H N), f N i) / (H N : ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro e he
  obtain ⟨M, hsmall⟩ := hblock (e / 2) (by positivity)
  obtain ⟨K, hK⟩ := exists_nat_gt (max (2 / e) 1)
  let L := max M K
  have hbig : ∀ᶠ N in atTop, L * L ≤ H N := hH.eventually_ge_atTop _
  filter_upwards [hbig, hHN, hsmall] with N hN hle hb
  let m := (H N).sqrt
  have hLm : L ≤ m := Nat.le_sqrt.mpr hN
  have hKpos : (0 : ℝ) < K := (zero_lt_one.trans_le (le_max_right _ _)).trans hK
  have hKle : K ≤ m := (le_max_right _ _).trans hLm
  have hm : 0 < m := (by exact_mod_cast hKpos : 0 < K).trans_le hKle
  have hmsq : m * m ≤ H N := Nat.sqrt_le _
  have hNat : 0 < H N := (Nat.mul_pos hm hm).trans_le hmsq
  have hhR : (0 : ℝ) < H N := by exact_mod_cast hNat
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hbound := sum_range_le_of_blocks (f N) (H N) m (by positivity : 0 ≤ e / 2) hm
    (fun i _ => (hf N i).2) (fun b h => hb m ((le_max_left _ _).trans hLm)
      (hmsq.trans hle) b (h.trans hle))
  have herr : (m : ℝ) / (H N : ℝ) < e / 2 := by
    have hKm : (K : ℝ) ≤ m := by exact_mod_cast hKle
    have hm₂ : 2 / e < (m : ℝ) := (lt_of_le_of_lt (le_max_left _ _) hK).trans_le hKm
    have hsqR : (m : ℝ) * m ≤ H N := by exact_mod_cast hmsq
    calc
      (m : ℝ) / (H N : ℝ) ≤ (m : ℝ) / ((m : ℝ) * m) :=
        div_le_div_of_nonneg_left hmR.le (by positivity) hsqR
      _ = 1 / (m : ℝ) := by field_simp
      _ < e / 2 := by
        have hh := (div_lt_iff₀ he).mp hm₂
        apply (div_lt_iff₀ hmR).mpr
        linarith
  have havg := div_le_div_of_nonneg_right hbound hhR.le
  have hmain : (H N : ℝ) * (e / 2) / (H N : ℝ) = e / 2 := by field_simp
  rw [add_div, hmain] at havg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg
    (sum_nonneg fun i _ => (hf N i).1) hhR.le)]
  linarith

private theorem abs_liouville_le_one (n : ℕ) : |(ArithmeticFunction.liouville n : ℝ)| ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [ArithmeticFunction.liouville_apply hn]
    norm_cast
    simp

private theorem sum_Icc_one_eq_range (n : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Icc 1 n, f i) = ∑ i ∈ range n, f (i + 1) := by
  rw [show Icc 1 n = Ico 1 (n + 1) by ext i; simp, Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

/-- A uniform short-interval Fourier energy estimate for Liouville. -/
def H1 : Prop :=
  ∀ e : ℝ, 0 < e → ∃ M : ℕ, ∀ᶠ N : ℕ in atTop,
    ∀ m : ℕ, M ≤ m → 0 < m → m*m ≤ N → ∀ b : ℕ, b ≤ N → ∀ α : ℝ,
      (∑ x ∈ range N, ‖∑ r ∈ range (2*m),
        (ArithmeticFunction.liouville (b+x+r+1) : ℂ) *
          Complex.exp ((2 * Real.pi * α * r : ℝ) * Complex.I)‖^2) ≤
        e * (m : ℝ)^2 * (N : ℝ)

/-- A deterministic Fourier-energy inequality for a block of shifts. -/
def H2 : Prop :=
  ∀ (f g : ℕ → ℝ), (∀ i, |f i| ≤ 1) → (∀ i, |g i| ≤ 1) →
    ∀ (N m b : ℕ) (e : ℝ), 0 < m → m ≤ N → 0 ≤ e →
      (∀ α : ℝ, (∑ x ∈ range N, ‖∑ r ∈ range (2*m),
        (g (b+x+r+1) : ℂ) * Complex.exp ((2 * Real.pi * α * r : ℝ) * Complex.I)‖^2) ≤
          e * (m : ℝ)^2 * (N : ℝ)) →
      (∑ h ∈ range m, |∑ x ∈ range N, f (x+1) * g (b+x+h+1)|) ≤
        Real.sqrt e * (m : ℝ) * (N : ℝ) + (m : ℝ)^2

theorem main : H1 → H2 →
    type_of% @ChowlaLiouvilleConjecture.chowla_liouville_conjecture.variants.averaged_two_point_uniform := by
  intro hshort hfourier H hH hHN
  let g (i : ℕ) : ℝ := ArithmeticFunction.liouville i
  let f (N i : ℕ) : ℝ :=
    |∑ x ∈ range N, g (x+1) * g (x+i+2)| / (N : ℝ)
  have hg : ∀ i, |g i| ≤ 1 := abs_liouville_le_one
  have hf (N i : ℕ) : 0 ≤ f N i ∧ f N i ≤ 1 := by
    refine ⟨div_nonneg (abs_nonneg _) (by positivity), ?_⟩
    by_cases hN : N = 0
    · simp [hN, f]
    have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    apply (div_le_one hNR).mpr
    calc
      _ ≤ ∑ x ∈ range N, |g (x+1) * g (x+i+2)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ range N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [abs_mul]
        exact mul_le_one₀ (hg _) (abs_nonneg _) (hg _)
      _ = _ := by simp
  have ht := average_tendsto_of_short_blocks f H hH hHN hf
  have hblock : ∀ e : ℝ, 0 < e → ∃ M : ℕ, ∀ᶠ N in atTop,
      ∀ m : ℕ, M ≤ m → m*m ≤ N → ∀ b, b+m ≤ N →
        (∑ i ∈ range m, f N (b+i)) ≤ m*e := by
    intro e he
    obtain ⟨M, hM⟩ := hshort ((e/2)^2) (by positivity)
    obtain ⟨K, hK⟩ := exists_nat_gt (max (2/e) 1)
    refine ⟨max M K, ?_⟩
    filter_upwards [hM] with N hN
    intro m hKm hsq b hb
    have hKpos : (0 : ℝ) < K := (zero_lt_one.trans_le (le_max_right _ _)).trans hK
    have hkm : K ≤ m := (le_max_right _ _).trans hKm
    have hm : 0 < m := (by exact_mod_cast hKpos : 0 < K).trans_le hkm
    have hmN : m ≤ N := (Nat.le_mul_of_pos_right _ hm).trans hsq
    have hNr : (0 : ℝ) < N := by exact_mod_cast hm.trans_le hmN
    have hMle : M ≤ m := (le_max_left _ _).trans hKm
    have henergy := hN m hMle hm hsq (b+1) (by omega)
    have hs := hfourier g g hg hg N m (b+1) ((e/2)^2) hm hmN (sq_nonneg _)
      (fun α => by simpa [g] using henergy α)
    rw [Real.sqrt_sq (by positivity : 0 ≤ e/2)] at hs
    have hsum : (∑ i ∈ range m, f N (b+i)) =
        (∑ i ∈ range m, |∑ x ∈ range N, g (x+1) * g (b+1+x+i+1)|) / (N : ℝ) := by
      rw [Finset.sum_div]
      simp [f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have hMr : (K : ℝ) ≤ m := by exact_mod_cast hkm
    have hl : 2/e < (m : ℝ) := (lt_of_le_of_lt (le_max_left _ _) hK).trans_le hMr
    have hhalf : (1 : ℝ) ≤ (m : ℝ) * (e/2) := by
      linarith [(div_lt_iff₀ he).mp hl]
    have hmR : 0 ≤ (m : ℝ) := by positivity
    have hsqR : (m : ℝ) * m ≤ N := by exact_mod_cast hsq
    have hscale : (m : ℝ) ≤ (N : ℝ) * (e/2) := calc
      (m : ℝ) ≤ (m : ℝ) * ((m : ℝ) * (e/2)) := le_mul_of_one_le_right hmR hhalf
      _ = ((m : ℝ) * m) * (e/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsqR (by positivity)
    rw [hsum]
    apply (div_le_iff₀ hNr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hscale hmR]
  convert ht hblock using 1
  ext N
  simp only [sum_Icc_one_eq_range]
  simp [f, g, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end OMA.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_averaged_two_point_uniform_R1

import OMAReductions.R_arxiv_2604_14639_R1
import Mathlib

/-!
Asymptotics of the maximum of the generalized Glasby-Paseman sequence (`arxiv-2604.14639.R1.H4`).
-/

namespace OMA.Arxiv2604H4

open Filter Topology Finset Real MeasureTheory OMA.S_arxiv_2604_14639

private noncomputable def binomP (n : ℕ) (α : ℝ) (i : ℕ) : ℝ :=
  (n.choose i : ℝ) * α ^ i * (1 - α) ^ (n - i)

private noncomputable def paramP (a : ℝ) : ℝ := a / (1 + a)
private noncomputable def paramQ (a : ℝ) : ℝ := 1 / (1 + a)
private noncomputable def paramT (a : ℝ) : ℝ := a / (1 + 2 * a)

private noncomputable def normNum (m l : ℕ) (a : ℝ) (r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (r + 1), binomP m (paramT a) i ^ l * (paramQ a) ^ ((r - i) * l)

private noncomputable def normDen (l : ℕ) (a : ℝ) (r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (r + 1), binomP r (paramP a) i ^ l

private noncomputable def asymNorm (m l : ℕ) (a : ℝ) : ℝ :=
  ((1 / Real.sqrt (2 * Real.pi * m * (paramT a * (1 - paramT a)))) ^ l *
      (1 / (1 - (paramQ a) ^ l))) /
    (1 / (Real.sqrt l *
      (Real.sqrt (2 * Real.pi * (paramT a * m) * (paramP a * paramQ a))) ^ (l - 1)))

private lemma paramP_pos {a : ℝ} (ha : 0 < a) : 0 < paramP a := by
  unfold paramP; positivity

private lemma paramP_lt_one {a : ℝ} (ha : 0 < a) : paramP a < 1 := by
  unfold paramP; rw [div_lt_one (by positivity)]; linarith

private lemma one_sub_paramP {a : ℝ} (ha : 0 < a) : 1 - paramP a = paramQ a := by
  unfold paramP paramQ; field_simp; ring

private lemma paramQ_pos {a : ℝ} (ha : 0 < a) : 0 < paramQ a := by
  unfold paramQ; positivity

private lemma paramQ_lt_one {a : ℝ} (ha : 0 < a) : paramQ a < 1 := by
  unfold paramQ; rw [div_lt_one (by positivity)]; linarith

private lemma paramT_pos {a : ℝ} (ha : 0 < a) : 0 < paramT a := by
  unfold paramT; positivity

private lemma paramT_lt_one {a : ℝ} (ha : 0 < a) : paramT a < 1 := by
  unfold paramT; rw [div_lt_one (by positivity)]; linarith

private lemma one_sub_paramT {a : ℝ} (ha : 0 < a) :
    1 - paramT a = (1 + a) / (1 + 2 * a) := by
  unfold paramT; field_simp; ring

private lemma binomP_nonneg {n : ℕ} {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (i : ℕ) :
    0 ≤ binomP n α i := by
  unfold binomP
  have h1' : 0 ≤ 1 - α := sub_nonneg.mpr h1
  positivity

private lemma binomP_sum_eq_one (n : ℕ) (α : ℝ) :
    ∑ i ∈ Finset.range (n + 1), binomP n α i = 1 := by
  unfold binomP
  have h := (add_pow α (1 - α) n).symm
  simp only [add_sub_cancel, one_pow] at h
  calc
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * α ^ i * (1 - α) ^ (n - i)
      = ∑ i ∈ Finset.range (n + 1), α ^ i * (1 - α) ^ (n - i) * (n.choose i : ℝ) :=
          Finset.sum_congr rfl fun i _ => by ring
    _ = 1 := h

private lemma binomP_le_one {n : ℕ} {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (i : ℕ) :
    binomP n α i ≤ 1 := by
  by_cases hi : i ≤ n
  · calc binomP n α i
        ≤ ∑ j ∈ Finset.range (n + 1), binomP n α j :=
          Finset.single_le_sum (fun j _ => binomP_nonneg h0 h1 j)
            (Finset.mem_range.mpr (by omega))
      _ = 1 := binomP_sum_eq_one n α
  · unfold binomP
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

private lemma nat_mul_choose_eq {n i : ℕ} (hin : i < n) :
    (i + 1) * n.choose (i + 1) = (n - i) * n.choose i := by
  have hf_pos : 0 < Nat.factorial i * Nat.factorial (n - (i + 1)) := by positivity
  refine Nat.mul_right_cancel hf_pos ?_
  have h1 : ((i + 1) * n.choose (i + 1)) * (Nat.factorial i * Nat.factorial (n - (i + 1))) =
      n.choose (i + 1) * (Nat.factorial (i + 1) * Nat.factorial (n - (i + 1))) := by
    rw [Nat.factorial_succ]; ring
  have h2 : ((n - i) * n.choose i) * (Nat.factorial i * Nat.factorial (n - (i + 1))) =
      n.choose i * Nat.factorial i * Nat.factorial (n - i) := by
    have hsub : n - i = (n - (i + 1)) + 1 := by omega
    conv_rhs => rw [hsub, Nat.factorial_succ]
    conv_lhs => rw [hsub]
    ring
  rw [show ((i + 1) * n.choose (i + 1)) * (Nat.factorial i * Nat.factorial (n - (i + 1))) =
      n.choose (i + 1) * Nat.factorial (i + 1) * Nat.factorial (n - (i + 1)) by
    rw [h1]; ring]
  rw [h2, Nat.choose_mul_factorial_mul_factorial (by omega),
    Nat.choose_mul_factorial_mul_factorial hin.le]

private lemma binomP_ratio_ge {n i : ℕ} {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (hin : i < n) (hle : (i + 1 : ℝ) ≤ (n + 1 : ℝ) * α) :
    binomP n α i ≤ binomP n α (i + 1) := by
  have hch : ((i + 1 : ℕ) : ℝ) * (n.choose (i + 1) : ℝ) =
      ((n - i : ℕ) : ℝ) * (n.choose i : ℝ) := by
    exact_mod_cast nat_mul_choose_eq hin
  have hexp : n - i = (n - (i + 1)) + 1 := by omega
  have hsub_ge : (i + 1 : ℝ) * (1 - α) ≤ ((n - i : ℕ) : ℝ) * α := by
    rw [Nat.cast_sub hin.le]
    nlinarith
  have hi1_pos : (0 : ℝ) < (i + 1 : ℝ) := by positivity
  have hdiff : 0 ≤ (i + 1 : ℝ) * (binomP n α (i + 1) - binomP n α i) := by
    unfold binomP
    rw [hexp, pow_succ, pow_succ]
    calc
      (i + 1 : ℝ) * ((n.choose (i + 1) : ℝ) * (α ^ i * α) * (1 - α) ^ (n - (i + 1)) -
          (n.choose i : ℝ) * α ^ i * ((1 - α) ^ (n - (i + 1)) * (1 - α)))
        = (((i + 1 : ℕ) : ℝ) * (n.choose (i + 1) : ℝ)) * (α ^ i * (1 - α) ^ (n - (i + 1)) * α) -
            (n.choose i : ℝ) * α ^ i * (1 - α) ^ (n - (i + 1)) * ((i + 1 : ℝ) * (1 - α)) := by
          push_cast; ring
      _ = (n.choose i : ℝ) * α ^ i * (1 - α) ^ (n - (i + 1)) *
            (((n - i : ℕ) : ℝ) * α - (i + 1 : ℝ) * (1 - α)) := by
          rw [hch]; ring
      _ ≥ 0 := by
          apply mul_nonneg
          · have : 0 ≤ 1 - α := sub_nonneg.mpr h1.le
            positivity
          · linarith
  nlinarith

private lemma binomP_ratio_le {n i : ℕ} {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (hin : i < n) (hle : (n + 1 : ℝ) * α ≤ (i + 1 : ℝ)) :
    binomP n α (i + 1) ≤ binomP n α i := by
  have hch : ((i + 1 : ℕ) : ℝ) * (n.choose (i + 1) : ℝ) =
      ((n - i : ℕ) : ℝ) * (n.choose i : ℝ) := by
    exact_mod_cast nat_mul_choose_eq hin
  have hexp : n - i = (n - (i + 1)) + 1 := by omega
  have hsub_le : ((n - i : ℕ) : ℝ) * α ≤ (i + 1 : ℝ) * (1 - α) := by
    rw [Nat.cast_sub hin.le]
    nlinarith
  have hi1_pos : (0 : ℝ) < (i + 1 : ℝ) := by positivity
  have hdiff : 0 ≤ (i + 1 : ℝ) * (binomP n α i - binomP n α (i + 1)) := by
    unfold binomP
    rw [hexp, pow_succ, pow_succ]
    calc
      (i + 1 : ℝ) * ((n.choose i : ℝ) * α ^ i * ((1 - α) ^ (n - (i + 1)) * (1 - α)) -
          (n.choose (i + 1) : ℝ) * (α ^ i * α) * (1 - α) ^ (n - (i + 1)))
        = (n.choose i : ℝ) * α ^ i * (1 - α) ^ (n - (i + 1)) *
            ((i + 1 : ℝ) * (1 - α)) -
            (((i + 1 : ℕ) : ℝ) * (n.choose (i + 1) : ℝ)) *
              (α ^ i * (1 - α) ^ (n - (i + 1)) * α) := by
          push_cast; ring
      _ = (n.choose i : ℝ) * α ^ i * (1 - α) ^ (n - (i + 1)) *
            ((i + 1 : ℝ) * (1 - α) - ((n - i : ℕ) : ℝ) * α) := by
          rw [hch]; ring
      _ ≥ 0 := by
          apply mul_nonneg
          · have : 0 ≤ 1 - α := sub_nonneg.mpr h1.le
            positivity
          · linarith
  nlinarith

private lemma binomP_mono_left {n i j : ℕ} {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (hij : i ≤ j) (hjn : j ≤ n) (hj : (j : ℝ) ≤ (n + 1 : ℝ) * α) :
    binomP n α i ≤ binomP n α j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    have hkn : k ≤ n := by omega
    have hlt : k < n := by omega
    have hk1 : (k : ℝ) ≤ (n + 1 : ℝ) * α := by
      have : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact this.trans hj
    refine (ih hkn hk1).trans (binomP_ratio_ge h0 h1 hlt ?_)
    exact_mod_cast hj

private lemma binomP_anti_right {n j i : ℕ} {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (hji : j ≤ i) (hin : i ≤ n) (hj : (n + 1 : ℝ) * α ≤ (j + 1 : ℝ)) :
    binomP n α i ≤ binomP n α j := by
  induction i, hji using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    have hkn : k ≤ n := by omega
    have hlt : k < n := by omega
    refine le_trans (binomP_ratio_le h0 h1 hlt ?_) (ih hkn)
    have hjk : (j + 1 : ℝ) ≤ (k + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hk 1
    exact hj.trans hjk

private lemma binomP_le_mode {n : ℕ} {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (i : ℕ) :
    binomP n α i ≤ binomP n α ⌊(n + 1 : ℝ) * α⌋₊ := by
  set k₀ : ℕ := ⌊(n + 1 : ℝ) * α⌋₊
  have hk₀_le : (k₀ : ℝ) ≤ (n + 1 : ℝ) * α :=
    Nat.floor_le (mul_nonneg (by positivity) h0.le)
  have hk₀_lt : (n + 1 : ℝ) * α < (k₀ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hk₀_n : k₀ ≤ n := by
    by_contra hbad
    have h1' : (n + 1 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ k₀)
    have h2' : (n + 1 : ℝ) * α < (n + 1 : ℝ) :=
      mul_lt_of_lt_one_right (by positivity) h1
    linarith
  by_cases hi : i ≤ n
  · by_cases hik : i ≤ k₀
    · exact binomP_mono_left h0 h1 hik hk₀_n hk₀_le
    · exact binomP_anti_right h0 h1 (by omega) hi hk₀_lt.le
  · unfold binomP
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp only [Nat.cast_zero, zero_mul]
    exact binomP_nonneg h0.le h1.le k₀

private lemma x_eq_normalized {m l r : ℕ} {a : ℝ} (ha : 0 < a) (_hl : 0 < l) (hrm : r ≤ m) :
    x m l a r = ((1 + 2 * a) / (1 + a)) ^ (m * l) * (normNum m l a r / normDen l a r) := by
  have hp1 : 0 < 1 + a := by linarith
  have hp2 : 0 < 1 + 2 * a := by linarith
  have hnum_term : ∀ i ∈ Finset.range (r + 1),
      ((m.choose i : ℝ) * a ^ i) ^ l =
        ((1 + 2 * a) / (1 + a)) ^ (m * l) * (1 + a) ^ (r * l) *
          (binomP m (paramT a) i ^ l * (paramQ a) ^ ((r - i) * l)) := by
    intro i hi
    have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have him : i ≤ m := hir.trans hrm
    have h1 : (m.choose i : ℝ) * a ^ i =
        ((1 + 2 * a) / (1 + a)) ^ m * (1 + a) ^ r *
          (binomP m (paramT a) i * (paramQ a) ^ (r - i)) := by
      unfold binomP
      rw [one_sub_paramT ha]
      unfold paramT paramQ
      have hm_split : i + (m - i) = m := Nat.add_sub_cancel' him
      have hpow2 : (1 + 2 * a) ^ i * (1 + 2 * a) ^ (m - i) = (1 + 2 * a) ^ m := by
        rw [← pow_add, hm_split]
      rw [div_pow, div_pow, div_pow, div_pow, one_pow]
      field_simp
      have h1a : (1 + a) ^ m * (1 + a) ^ (r - i) = (1 + a) ^ r * (1 + a) ^ (m - i) := by
        rw [← pow_add, ← pow_add, show m + (r - i) = r + (m - i) by omega]
      calc (m.choose i : ℝ) * (1 + a) ^ m * (1 + 2 * a) ^ i * (1 + 2 * a) ^ (m - i) *
            (1 + a) ^ (r - i)
          = (m.choose i : ℝ) * ((1 + 2 * a) ^ i * (1 + 2 * a) ^ (m - i)) *
              ((1 + a) ^ m * (1 + a) ^ (r - i)) := by ring
        _ = (m.choose i : ℝ) * (1 + 2 * a) ^ m * ((1 + a) ^ r * (1 + a) ^ (m - i)) := by
            rw [hpow2, h1a]
        _ = (m.choose i : ℝ) * (1 + 2 * a) ^ m * (1 + a) ^ r * (1 + a) ^ (m - i) := by ring
    calc
      ((m.choose i : ℝ) * a ^ i) ^ l
        = (((1 + 2 * a) / (1 + a)) ^ m * (1 + a) ^ r *
            (binomP m (paramT a) i * (paramQ a) ^ (r - i))) ^ l := by rw [h1]
      _ = ((1 + 2 * a) / (1 + a)) ^ (m * l) * (1 + a) ^ (r * l) *
            (binomP m (paramT a) i ^ l * (paramQ a) ^ ((r - i) * l)) := by
          rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
  have hden_term : ∀ i ∈ Finset.range (r + 1),
      ((r.choose i : ℝ) * a ^ i) ^ l = (1 + a) ^ (r * l) * binomP r (paramP a) i ^ l := by
    intro i hi
    have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : (r.choose i : ℝ) * a ^ i = (1 + a) ^ r * binomP r (paramP a) i := by
      unfold binomP
      rw [one_sub_paramP ha]
      unfold paramP paramQ
      rw [div_pow, div_pow, one_pow]
      have hpow : (1 + a) ^ i * (1 + a) ^ (r - i) = (1 + a) ^ r := by
        rw [← pow_add, Nat.add_sub_cancel' hir]
      field_simp
      rw [mul_assoc, hpow]
    calc
      ((r.choose i : ℝ) * a ^ i) ^ l
        = ((1 + a) ^ r * binomP r (paramP a) i) ^ l := by rw [h1]
      _ = (1 + a) ^ (r * l) * binomP r (paramP a) i ^ l := by rw [mul_pow, ← pow_mul]
  have hnum_sum : ∑ i ∈ Finset.range (r + 1), ((m.choose i : ℝ) * a ^ i) ^ l =
      ((1 + 2 * a) / (1 + a)) ^ (m * l) * (1 + a) ^ (r * l) * normNum m l a r := by
    rw [Finset.sum_congr rfl hnum_term, ← Finset.mul_sum]
    rfl
  have hden_sum : ∑ i ∈ Finset.range (r + 1), ((r.choose i : ℝ) * a ^ i) ^ l =
      (1 + a) ^ (r * l) * normDen l a r := by
    rw [Finset.sum_congr rfl hden_term, ← Finset.mul_sum]
    rfl
  have hden_pos : 0 < normDen l a r := by
    unfold normDen
    refine Finset.sum_pos' (fun i _ => pow_nonneg (binomP_nonneg (paramP_pos ha).le
      (paramP_lt_one ha).le i) l) ⟨0, Finset.mem_range.mpr (Nat.succ_pos r), ?_⟩
    unfold binomP
    have hq0 : 0 < paramQ a := paramQ_pos ha
    rw [one_sub_paramP ha]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul, Nat.sub_zero]
    exact pow_pos (pow_pos hq0 r) l
  unfold x
  rw [hnum_sum, hden_sum]
  have hpow_ne : (1 + a) ^ (r * l) ≠ 0 := by positivity
  field_simp

private lemma asymNorm_pos {m l : ℕ} {a : ℝ} (hm : 0 < m) (hl : 0 < l) (ha : 0 < a) :
    0 < asymNorm m l a := by
  unfold asymNorm
  have ht0 := paramT_pos ha
  have ht1 := one_sub_paramT ha
  have hq0 := paramQ_pos ha
  have hq1 : (paramQ a) ^ l < 1 := pow_lt_one₀ hq0.le (paramQ_lt_one ha) hl.ne'
  have hp0 := paramP_pos ha
  have h1mt : 0 < 1 - paramT a := by rw [ht1]; positivity
  positivity

private lemma asymptotic_eq_normalized {m l : ℕ} {a : ℝ} (hm : 0 < m) (hl : 0 < l) (ha : 0 < a) :
    asymptotic m l a = ((1 + 2 * a) / (1 + a)) ^ (m * l) * asymNorm m l a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
  unfold asymptotic asymNorm
  have hp1 : 0 < 1 + a := by linarith
  have hp2 : 0 < 1 + 2 * a := by linarith
  have hq1 : (paramQ a) ^ (k + 1) < 1 := pow_lt_one₀ (paramQ_pos ha).le (paramQ_lt_one ha)
    (Nat.succ_ne_zero k)
  have hq_exp : 1 - (paramQ a) ^ (k + 1) = ((1 + a) ^ (k + 1) - 1) / (1 + a) ^ (k + 1) := by
    unfold paramQ; rw [div_pow, one_pow]; field_simp
  have ht_pos : 0 < paramT a := paramT_pos ha
  have ht1 : 1 - paramT a = (1 + a) / (1 + 2 * a) := one_sub_paramT ha
  have hp_pos : 0 < paramP a := paramP_pos ha
  have hq_pos : 0 < paramQ a := paramQ_pos ha
  have hrpow : ((1 + 2 * a) / (1 + a)) ^ (((m : ℝ) + 1 / 2) * ((k + 1 : ℕ) : ℝ)) =
      ((1 + 2 * a) / (1 + a)) ^ (m * (k + 1)) *
        ((1 + 2 * a) / (1 + a)) ^ (((k + 1 : ℕ) : ℝ) / 2) := by
    have hadd : ((m : ℝ) + 1 / 2) * ((k + 1 : ℕ) : ℝ) =
        ((m * (k + 1) : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) / 2 := by
      push_cast; ring
    rw [hadd, Real.rpow_add (by positivity), Real.rpow_natCast]
  rw [hrpow, show ((k + 1) - 1 : ℕ) = k by omega]
  have hrhs_pos : 0 < ((1 / Real.sqrt (2 * Real.pi * m * (paramT a * (1 - paramT a)))) ^ (k + 1) *
      (1 / (1 - (paramQ a) ^ (k + 1)))) /
      (1 / (Real.sqrt (k + 1) *
        (Real.sqrt (2 * Real.pi * (paramT a * m) * (paramP a * paramQ a))) ^ k)) := by
    have h1t : 0 < 1 - paramT a := by rw [ht1]; positivity
    positivity
  have hden_sub : 0 < (1 + a) ^ (k + 1) - 1 := by
    have hlt : (1 : ℝ) < (1 + a) ^ (k + 1) := one_lt_pow₀ (by linarith) (Nat.succ_ne_zero k)
    linarith
  have hlhs_pos : 0 < Real.sqrt (k + 1) / Real.sqrt (2 * Real.pi * m) *
      ((1 + 2 * a) ^ (1 / 2 : ℝ) * (1 + a) * a ^ (((((k + 1 : ℕ) : ℝ)) - 2) / 2) /
        ((1 + a) ^ (k + 1) - 1)) *
      ((1 + 2 * a) / (1 + a)) ^ (((k + 1 : ℕ) : ℝ) / 2) := by
    positivity
  have hmul :
      Real.sqrt (k + 1) / Real.sqrt (2 * Real.pi * m) *
          ((1 + 2 * a) ^ (1 / 2 : ℝ) * (1 + a) * a ^ (((((k + 1 : ℕ) : ℝ)) - 2) / 2) /
            ((1 + a) ^ (k + 1) - 1)) *
          ((1 + 2 * a) / (1 + a)) ^ (((k + 1 : ℕ) : ℝ) / 2) =
        ((1 / Real.sqrt (2 * Real.pi * m * (paramT a * (1 - paramT a)))) ^ (k + 1) *
            (1 / (1 - (paramQ a) ^ (k + 1)))) /
          (1 / (Real.sqrt (k + 1) *
            (Real.sqrt (2 * Real.pi * (paramT a * m) * (paramP a * paramQ a))) ^ k)) := by
    refine (sq_eq_sq₀ hlhs_pos.le hrhs_pos.le).mp ?_
    have hsq_rpow1 : ((1 + 2 * a) ^ (1 / 2 : ℝ)) ^ 2 = 1 + 2 * a := by
      rw [← Real.rpow_two, ← Real.rpow_mul hp2.le]
      norm_num
    have hsq_rpow2 : (a ^ (((((k + 1 : ℕ) : ℝ)) - 2) / 2)) ^ 2 * a ^ 2 = a ^ (k + 1) := by
      rw [← Real.rpow_two, ← Real.rpow_mul ha.le, show (((k + 1 : ℕ) : ℝ) - 2) / 2 * 2 =
          ((k + 1 : ℕ) : ℝ) - 2 by ring]
      rw [show a ^ 2 = a ^ (2 : ℝ) by norm_num, ← Real.rpow_add ha]
      rw [show (((k + 1 : ℕ) : ℝ) - 2) + 2 = ((k + 1 : ℕ) : ℝ) by ring, Real.rpow_natCast]
    have hsq_rpow3 : (((1 + 2 * a) / (1 + a)) ^ (((k + 1 : ℕ) : ℝ) / 2)) ^ 2 =
        ((1 + 2 * a) / (1 + a)) ^ (k + 1) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
      rw [show (((k + 1 : ℕ) : ℝ) / 2) * 2 = ((k + 1 : ℕ) : ℝ) by ring, Real.rpow_natCast]
    have hsq1 : (Real.sqrt (k + 1)) ^ 2 = ((k + 1 : ℕ) : ℝ) := by
      rw [Real.sq_sqrt (by positivity)]; push_cast; rfl
    have hsq2 : (Real.sqrt (2 * Real.pi * m)) ^ 2 = 2 * Real.pi * m :=
      Real.sq_sqrt (by positivity)
    have hsq3 : (Real.sqrt (2 * Real.pi * m * (paramT a * (1 - paramT a)))) ^ 2 =
        2 * Real.pi * m * (paramT a * (1 - paramT a)) := by
      rw [Real.sq_sqrt]; rw [ht1]; positivity
    have hsq4 : (Real.sqrt (2 * Real.pi * (paramT a * m) * (paramP a * paramQ a))) ^ 2 =
        2 * Real.pi * (paramT a * m) * (paramP a * paramQ a) :=
      Real.sq_sqrt (by positivity)
    have ha2_ne : a ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne'
    apply mul_right_cancel₀ ha2_ne
    simp only [mul_pow, div_pow, one_div, inv_pow]
    rw [← pow_mul, ← pow_mul]
    rw [show (k + 1) * 2 = 2 * (k + 1) by ring, pow_mul, hsq3]
    rw [show k * 2 = 2 * k by ring, pow_mul, hsq4]
    simp only [one_div] at hsq_rpow1
    rw [hsq_rpow1, hsq_rpow3, hsq1, hsq2, div_pow]
    have hlhs' :
        (((k + 1 : ℕ) : ℝ) / (2 * Real.pi * m) *
          (((1 + 2 * a) * (1 + a) ^ 2 * (a ^ ((((k + 1 : ℕ) : ℝ) - 2) / 2)) ^ 2) /
            ((1 + a) ^ (k + 1) - 1) ^ 2) *
          ((1 + 2 * a) ^ (k + 1) / (1 + a) ^ (k + 1))) * a ^ 2 =
        ((k + 1 : ℕ) : ℝ) / (2 * Real.pi * m) *
          (((1 + 2 * a) * (1 + a) ^ 2 * ((a ^ ((((k + 1 : ℕ) : ℝ) - 2) / 2)) ^ 2 * a ^ 2)) /
            ((1 + a) ^ (k + 1) - 1) ^ 2) *
          ((1 + 2 * a) ^ (k + 1) / (1 + a) ^ (k + 1)) := by ring
    rw [hlhs', hsq_rpow2, hq_exp]
    unfold paramT paramP paramQ
    rw [show 1 - a / (1 + 2 * a) = (1 + a) / (1 + 2 * a) by field_simp; ring]
    have hpow_step : (2 * Real.pi * m * (a / (1 + 2 * a) * ((1 + a) / (1 + 2 * a)))) ^ (k + 1) =
        (2 * Real.pi * m) * (a / (1 + 2 * a) * ((1 + a) / (1 + 2 * a))) *
          (2 * Real.pi * m * (a / (1 + 2 * a) * ((1 + a) / (1 + 2 * a)))) ^ k := by
      rw [pow_succ']
    have hbase : 2 * Real.pi * (a / (1 + 2 * a) * m) * (a / (1 + a) * (1 / (1 + a))) =
        (2 * Real.pi * m * (a / (1 + 2 * a) * ((1 + a) / (1 + 2 * a)))) *
          ((a * (1 + 2 * a)) / (1 + a) ^ 3) := by
      field_simp
    rw [hpow_step, hbase, mul_pow]
    have hpi_ne : (2 * Real.pi * m) ≠ 0 := by positivity
    have ha_ne : a ≠ 0 := ha.ne'
    have h1a_ne : (1 + a) ≠ 0 := hp1.ne'
    have h12a_ne : (1 + 2 * a) ≠ 0 := hp2.ne'
    have hsub_ne : (1 + a) ^ (k + 1) - 1 ≠ 0 := hden_sub.ne'
    have hpowk_ne : (2 * Real.pi * (m : ℝ) * (a / (1 + 2 * a) * ((1 + a) / (1 + 2 * a)))) ^ k ≠ 0 := by
      positivity
    simp only [div_pow, mul_pow, ← pow_mul]
    field_simp
    rw [pow_succ a k, pow_succ (1 + 2 * a) k, pow_succ (1 + a) k]
    field_simp
    rw [show (1 + a) ^ (3 * k) = ((1 + a) ^ k) ^ 3 by rw [← pow_mul, mul_comm 3 k]]
    ring
  calc
    Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt (2 * Real.pi * m) *
        ((1 + 2 * a) ^ (1 / 2 : ℝ) * (1 + a) * a ^ (((((k + 1 : ℕ) : ℝ)) - 2) / 2) /
          ((1 + a) ^ (k + 1) - 1)) *
        (((1 + 2 * a) / (1 + a)) ^ (m * (k + 1)) *
          ((1 + 2 * a) / (1 + a)) ^ (((k + 1 : ℕ) : ℝ) / 2))
      = ((1 + 2 * a) / (1 + a)) ^ (m * (k + 1)) *
          (Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt (2 * Real.pi * m) *
            ((1 + 2 * a) ^ (1 / 2 : ℝ) * (1 + a) * a ^ (((((k + 1 : ℕ) : ℝ)) - 2) / 2) /
              ((1 + a) ^ (k + 1) - 1)) *
            ((1 + 2 * a) / (1 + a)) ^ (((k + 1 : ℕ) : ℝ) / 2)) := by ring
    _ = ((1 + 2 * a) / (1 + a)) ^ (m * (k + 1)) * _ := by
        simpa [Nat.succ_eq_add_one] using
          congrArg (((1 + 2 * a) / (1 + a)) ^ (m * (k + 1)) * ·) hmul

private lemma normDen_ge_inv_pow {l : ℕ} {a : ℝ} (_hl : 0 < l) (ha : 0 < a) (r : ℕ) :
    ((r + 1 : ℝ) ^ l)⁻¹ ≤ normDen l a r := by
  have hp0 := (paramP_pos ha).le
  have hp1 := (paramP_lt_one ha).le
  have hsum : ∑ i ∈ Finset.range (r + 1), binomP r (paramP a) i = 1 :=
    binomP_sum_eq_one r (paramP a)
  have hex : ∃ i ∈ Finset.range (r + 1), ((r + 1 : ℝ))⁻¹ ≤ binomP r (paramP a) i := by
    by_contra hnone
    push Not at hnone
    have hlt : ∑ i ∈ Finset.range (r + 1), binomP r (paramP a) i <
        ∑ _i ∈ Finset.range (r + 1), ((r + 1 : ℝ))⁻¹ :=
      Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr (Nat.succ_pos r)⟩ hnone
    have hconst : ∑ _i ∈ Finset.range (r + 1), ((r + 1 : ℝ))⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      exact mul_inv_cancel₀ (by positivity)
    linarith
  obtain ⟨i₀, hi₀, hge⟩ := hex
  have hpow : ((r + 1 : ℝ) ^ l)⁻¹ ≤ binomP r (paramP a) i₀ ^ l := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (by positivity) hge l
  exact hpow.trans (Finset.single_le_sum (f := fun i => binomP r (paramP a) i ^ l)
    (fun i _ => pow_nonneg (binomP_nonneg hp0 hp1 i) l) hi₀)

private lemma abs_log_one_add_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - (u - u ^ 2 / 2)| ≤ |u| ^ 3 := by
  let f : ℝ → ℝ := fun x => Real.log (1 + x) - (x - x ^ 2 / 2)
  have hf0 : f 0 = 0 := by simp [f]
  have hderiv : ∀ x : ℝ, -1 < x → HasDerivAt f (x ^ 2 / (1 + x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := (hasDerivAt_id x).const_add 1
    have hlog : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + x)) x := by
      simpa only [one_div] using h1.log (by linarith)
    have hlin : HasDerivAt (fun t : ℝ => t - t ^ 2 / 2) (1 - x) x := by
      have hsq : HasDerivAt (fun t : ℝ => t ^ 2 / 2) x x :=
        ((hasDerivAt_pow 2 x).div_const 2).congr_deriv (by norm_num)
      exact (hasDerivAt_id x).sub hsq
    refine (hlog.sub hlin).congr_deriv ?_
    have h1x : 1 + x ≠ 0 := by linarith
    field_simp
    ring
  rcases le_or_gt 0 u with hu_nn | hu_neg
  · have hu_le : u ≤ 1 / 2 := (abs_le.mp hu).2
    have hf_nn : 0 ≤ f u := by
      have hmono : MonotoneOn f (Set.Icc 0 (1 / 2)) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
        · refine ContinuousOn.sub ?_ (by fun_prop)
          refine Real.continuousOn_log.comp (by fun_prop) fun x hx => ?_
          exact Set.mem_compl_singleton_iff.mpr (by linarith [hx.1])
        · refine DifferentiableOn.sub ?_ (by fun_prop)
          refine fun x hx => (Real.differentiableAt_log ?_).comp x
            ((differentiableAt_id).const_add 1) |>.differentiableWithinAt
          rw [interior_Icc] at hx
          dsimp
          linarith [hx.1]
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hderiv x (by linarith [hx.1])).deriv]
          have h1x : 0 < 1 + x := by linarith [hx.1]
          positivity
      rw [← hf0]
      exact hmono ⟨le_rfl, by norm_num⟩ ⟨hu_nn, hu_le⟩ hu_nn
    have hf_le : f u ≤ u ^ 3 := by
      let g : ℝ → ℝ := fun x => x ^ 3 - f x
      have hg0 : g 0 = 0 := by simp [g, hf0]
      have hmono : MonotoneOn g (Set.Icc 0 (1 / 2)) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
        · refine (by fun_prop : ContinuousOn (fun x : ℝ => x ^ 3) _).sub ?_
          refine ContinuousOn.sub ?_ (by fun_prop)
          refine Real.continuousOn_log.comp (by fun_prop) fun x hx => ?_
          exact Set.mem_compl_singleton_iff.mpr (by linarith [hx.1])
        · refine (by fun_prop : DifferentiableOn ℝ (fun x : ℝ => x ^ 3) _).sub ?_
          refine DifferentiableOn.sub ?_ (by fun_prop)
          refine fun x hx => (Real.differentiableAt_log ?_).comp x
            ((differentiableAt_id).const_add 1) |>.differentiableWithinAt
          rw [interior_Icc] at hx
          dsimp
          linarith [hx.1]
        · intro x hx
          rw [interior_Icc] at hx
          have hx0 : 0 < x := hx.1
          have h1x : 0 < 1 + x := by linarith
          have hd : HasDerivAt g (3 * x ^ 2 - x ^ 2 / (1 + x)) x :=
            (hasDerivAt_pow 3 x).sub (hderiv x (by linarith))
          rw [hd.deriv]
          have hval : 3 * x ^ 2 - x ^ 2 / (1 + x) = x ^ 2 * (2 + 3 * x) / (1 + x) := by
            field_simp; ring
          rw [hval]
          positivity
      have hg_nn : 0 ≤ g u := by
        rw [← hg0]
        exact hmono ⟨le_rfl, by norm_num⟩ ⟨hu_nn, hu_le⟩ hu_nn
      dsimp only [g] at hg_nn
      linarith
    rw [abs_of_nonneg hf_nn, abs_of_nonneg hu_nn]
    exact hf_le
  · have hu_ge : -(1 / 2) ≤ u := (abs_le.mp hu).1
    have hf_np : f u ≤ 0 := by
      have hmono : MonotoneOn f (Set.Icc (-(1 / 2)) 0) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc (-(1 / 2)) 0) ?_ ?_ ?_
        · refine ContinuousOn.sub ?_ (by fun_prop)
          refine Real.continuousOn_log.comp (by fun_prop) fun x hx => ?_
          exact Set.mem_compl_singleton_iff.mpr (by linarith [hx.1])
        · refine DifferentiableOn.sub ?_ (by fun_prop)
          refine fun x hx => (Real.differentiableAt_log ?_).comp x
            ((differentiableAt_id).const_add 1) |>.differentiableWithinAt
          rw [interior_Icc] at hx
          dsimp
          linarith [hx.1]
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hderiv x (by linarith [hx.1])).deriv]
          have h1x : 0 < 1 + x := by linarith [hx.1]
          positivity
      rw [← hf0]
      exact hmono ⟨hu_ge, hu_neg.le⟩ ⟨by norm_num, le_rfl⟩ hu_neg.le
    have hf_ge : u ^ 3 ≤ f u := by
      let g : ℝ → ℝ := fun x => f x - x ^ 3
      have hg0 : g 0 = 0 := by simp [g, hf0]
      have hanti : AntitoneOn g (Set.Icc (-(1 / 2)) 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc (-(1 / 2)) 0) ?_ ?_ ?_
        · refine ContinuousOn.sub ?_ (by fun_prop)
          refine ContinuousOn.sub ?_ (by fun_prop)
          refine Real.continuousOn_log.comp (by fun_prop) fun x hx => ?_
          exact Set.mem_compl_singleton_iff.mpr (by linarith [hx.1])
        · refine DifferentiableOn.sub ?_ (by fun_prop)
          refine DifferentiableOn.sub ?_ (by fun_prop)
          refine fun x hx => (Real.differentiableAt_log ?_).comp x
            ((differentiableAt_id).const_add 1) |>.differentiableWithinAt
          rw [interior_Icc] at hx
          dsimp
          linarith [hx.1]
        · intro x hx
          rw [interior_Icc] at hx
          have hx1 : -(1 / 2) < x := hx.1
          have h1x : 0 < 1 + x := by linarith
          have hd : HasDerivAt g (x ^ 2 / (1 + x) - 3 * x ^ 2) x :=
            (hderiv x (by linarith)).sub (hasDerivAt_pow 3 x)
          rw [hd.deriv]
          have hval : x ^ 2 / (1 + x) - 3 * x ^ 2 = -(x ^ 2 * (2 + 3 * x)) / (1 + x) := by
            field_simp; ring
          rw [hval]
          have hnum : 0 ≤ x ^ 2 * (2 + 3 * x) := mul_nonneg (sq_nonneg x) (by linarith)
          exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnum) h1x.le
      have hg_nn : 0 ≤ g u := by
        rw [← hg0]
        exact hanti ⟨hu_ge, hu_neg.le⟩ ⟨by norm_num, le_rfl⟩ hu_neg.le
      dsimp only [g] at hg_nn
      linarith
    rw [abs_of_nonpos hf_np, abs_of_neg hu_neg, show (-u) ^ 3 = -(u ^ 3) by ring]
    linarith

private lemma abs_exp_sub_one_le_two_mul {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.exp x - 1| ≤ 2 * |x| := by
  have hx1 : x ≤ 1 / 2 := (abs_le.mp hx).2
  have hx2 : -(1 / 2) ≤ x := (abs_le.mp hx).1
  have h1mx : 1 / 2 ≤ 1 - x := by linarith
  have hlo : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hhi : Real.exp x ≤ (1 - x)⁻¹ := by
    calc Real.exp x = (Real.exp (-x))⁻¹ := by rw [Real.exp_neg, inv_inv]
      _ ≤ (1 - x)⁻¹ := inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp (-x)])
  rw [abs_le]
  constructor
  · have : -2 * |x| ≤ x := by linarith [neg_abs_le x, abs_nonneg x]
    linarith
  · have hstep : (1 - x)⁻¹ - 1 ≤ 2 * |x| := by
      rw [show (1 - x)⁻¹ - 1 = x / (1 - x) by field_simp; ring]
      calc x / (1 - x) ≤ |x| / (1 - x) := div_le_div_of_nonneg_right (le_abs_self x) (by linarith)
        _ ≤ |x| / (1 / 2) := div_le_div_of_nonneg_left (abs_nonneg x) (by norm_num) h1mx
        _ = 2 * |x| := by ring
    linarith

private lemma prod3_sub_one_le {a b c η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (ha : |a - 1| ≤ η) (hb : |b - 1| ≤ η) (hc : |c - 1| ≤ η) :
    |a * b * c - 1| ≤ 7 * η := by
  have hid : a * b * c - 1 =
      (a - 1) * (b - 1) * (c - 1) + (a - 1) * (b - 1) + (a - 1) * (c - 1) +
        (b - 1) * (c - 1) + (a - 1) + (b - 1) + (c - 1) := by ring
  rw [hid]
  have h7 : ∀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ : ℝ,
      |x₁ + x₂ + x₃ + x₄ + x₅ + x₆ + x₇| ≤
        |x₁| + |x₂| + |x₃| + |x₄| + |x₅| + |x₆| + |x₇| := by
    intro x₁ x₂ x₃ x₄ x₅ x₆ x₇
    linarith [abs_add_le (x₁ + x₂ + x₃ + x₄ + x₅ + x₆) x₇,
      abs_add_le (x₁ + x₂ + x₃ + x₄ + x₅) x₆,
      abs_add_le (x₁ + x₂ + x₃ + x₄) x₅,
      abs_add_le (x₁ + x₂ + x₃) x₄,
      abs_add_le (x₁ + x₂) x₃,
      abs_add_le x₁ x₂]
  refine (h7 _ _ _ _ _ _ _).trans ?_
  simp only [abs_mul]
  have h2 : ∀ x y : ℝ, |x| ≤ η → |y| ≤ η → |x| * |y| ≤ η := fun x y hx hy =>
    (mul_le_mul hx hy (abs_nonneg y) hη).trans (by nlinarith)
  have h3 : |(a - 1)| * |(b - 1)| * |(c - 1)| ≤ η := by
    refine (mul_le_mul (h2 _ _ ha hb) hc (abs_nonneg _) hη).trans ?_
    nlinarith
  linarith [h2 _ _ ha hb, h2 _ _ ha hc, h2 _ _ hb hc]

private lemma stirling_F1_bound {n k : ℕ} {δ : ℝ} (hk_pos : 0 < k) (hnk_pos : 0 < n - k)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ Real.sqrt Real.pi / 4)
    (hSn : |Stirling.stirlingSeq n - Real.sqrt Real.pi| < δ)
    (hSk : |Stirling.stirlingSeq k - Real.sqrt Real.pi| < δ)
    (hSnk : |Stirling.stirlingSeq (n - k) - Real.sqrt Real.pi| < δ) :
    |Real.sqrt Real.pi * Stirling.stirlingSeq n /
        (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) - 1| ≤
      6 * δ / Real.sqrt Real.pi := by
  have hS_pos : ∀ m : ℕ, 0 < m → 0 < Stirling.stirlingSeq m := fun m _ => by
    unfold Stirling.stirlingSeq; positivity
  have hsp_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hSnk_lo : Real.sqrt Real.pi - δ ≤ Stirling.stirlingSeq (n - k) := by
    linarith [(abs_lt.mp hSnk).1]
  have hSk_lo : Real.sqrt Real.pi - δ ≤ Stirling.stirlingSeq k := by
    linarith [(abs_lt.mp hSk).1]
  have hSnk_hi : Stirling.stirlingSeq (n - k) ≤ Real.sqrt Real.pi + δ := by
    linarith [(abs_lt.mp hSnk).2]
  have hprod_lo : (3 / 4 * Real.sqrt Real.pi) ^ 2 ≤
      Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k) := by
    have hk1 : 3 / 4 * Real.sqrt Real.pi ≤ Stirling.stirlingSeq k := by linarith
    have hnk1 : 3 / 4 * Real.sqrt Real.pi ≤ Stirling.stirlingSeq (n - k) := by linarith
    rw [sq]
    exact mul_le_mul hk1 hnk1 (by positivity) (hS_pos k hk_pos).le
  have hnum_diff :
      |Real.sqrt Real.pi * Stirling.stirlingSeq n -
          Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)| ≤
        3 * Real.sqrt Real.pi * δ + δ ^ 2 := by
    have hid : Real.sqrt Real.pi * Stirling.stirlingSeq n -
          Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k) =
        Real.sqrt Real.pi * (Stirling.stirlingSeq n - Real.sqrt Real.pi) -
          (Stirling.stirlingSeq k - Real.sqrt Real.pi) * Stirling.stirlingSeq (n - k) -
          Real.sqrt Real.pi * (Stirling.stirlingSeq (n - k) - Real.sqrt Real.pi) := by ring
    rw [hid]
    have h_tri : ∀ x y z : ℝ, |x - y - z| ≤ |x| + |y| + |z| := fun x y z => by
      linarith [abs_sub (x - y) z, abs_sub x y]
    refine (h_tri _ _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hsp_pos]
    have ha1 : Real.sqrt Real.pi * |Stirling.stirlingSeq n - Real.sqrt Real.pi| ≤
        Real.sqrt Real.pi * δ := mul_le_mul_of_nonneg_left hSn.le hsp_pos.le
    have ha2 : |Stirling.stirlingSeq k - Real.sqrt Real.pi| * |Stirling.stirlingSeq (n - k)| ≤
        Real.sqrt Real.pi * δ + δ ^ 2 := by
      rw [abs_of_pos (hS_pos (n - k) hnk_pos)]
      have hmul := mul_le_mul hSk.le hSnk_hi (hS_pos _ hnk_pos).le hδ_pos.le
      have hdist : δ * (Real.sqrt Real.pi + δ) = Real.sqrt Real.pi * δ + δ ^ 2 := by ring
      linarith
    have ha3 : Real.sqrt Real.pi * |Stirling.stirlingSeq (n - k) - Real.sqrt Real.pi| ≤
        Real.sqrt Real.pi * δ := mul_le_mul_of_nonneg_left hSnk.le hsp_pos.le
    linarith
  have hF1_eq : |Real.sqrt Real.pi * Stirling.stirlingSeq n /
        (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) - 1| =
      |Real.sqrt Real.pi * Stirling.stirlingSeq n -
          Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)| /
        (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) := by
    rw [div_sub_one (mul_ne_zero (hS_pos k hk_pos).ne' (hS_pos (n - k) hnk_pos).ne'),
      abs_div, abs_of_pos (mul_pos (hS_pos k hk_pos) (hS_pos (n - k) hnk_pos))]
  rw [hF1_eq]
  have hden_pos : 0 < (3 / 4 * Real.sqrt Real.pi) ^ 2 := by positivity
  calc |Real.sqrt Real.pi * Stirling.stirlingSeq n -
          Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)| /
        (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k))
      ≤ (3 * Real.sqrt Real.pi * δ + δ ^ 2) / (3 / 4 * Real.sqrt Real.pi) ^ 2 :=
        div_le_div₀ (by positivity) hnum_diff hden_pos hprod_lo
    _ ≤ (13 / 4 * Real.sqrt Real.pi * δ) / (3 / 4 * Real.sqrt Real.pi) ^ 2 := by
        have hδsq : δ ^ 2 ≤ (Real.sqrt Real.pi / 4) * δ := by
          rw [sq]; exact mul_le_mul_of_nonneg_right hδ_le hδ_pos.le
        exact div_le_div_of_nonneg_right (by linarith) hden_pos.le
    _ ≤ 6 * δ / Real.sqrt Real.pi := by
        have hsqpi : (Real.sqrt Real.pi) ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
        have hrat : (13 / 4 * Real.sqrt Real.pi * δ) / (3 / 4 * Real.sqrt Real.pi) ^ 2 =
            52 / 9 * δ / Real.sqrt Real.pi := by
          rw [mul_pow, hsqpi]
          field_simp
          rw [hsqpi]
          ring
        rw [hrat]
        exact div_le_div_of_nonneg_right (by linarith [hδ_pos]) hsp_pos.le

private lemma stirling_F2_bound {α M σ c δ : ℝ} {n k : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1) (hc_pos : 0 < c) (hσ_pos : 0 < σ) (hM : 0 < M) (hδ_pos : 0 < δ)
    (hn_pos : (0 : ℝ) < n) (hsq_ge1 : 1 ≤ Real.sqrt n) (hk_pos : 0 < k) (hk_lt_n : k < n)
    (hk : |(k : ℝ) - α * n| ≤ M * σ * Real.sqrt n)
    (hk_bounds : c * n / 2 ≤ k ∧ c * n / 2 ≤ ((n - k : ℕ) : ℝ))
    (h5a : 16 * (M * σ) ^ 2 / (c ^ 2 * δ) ≤ Real.sqrt n)
    (h5b : 16 * M * σ / (c ^ 2 * δ) ≤ Real.sqrt n) :
    |Real.sqrt (α * (1 - α) * (n : ℝ) ^ 2 / ((k : ℝ) * ((n - k : ℕ) : ℝ))) - 1| ≤ δ / 2 := by
  let t : ℝ := (k : ℝ) - α * n
  let F2 : ℝ := Real.sqrt (α * (1 - α) * (n : ℝ) ^ 2 / ((k : ℝ) * ((n - k : ℕ) : ℝ)))
  have hkn : k ≤ n := hk_lt_n.le
  have hnk_pos : 0 < n - k := Nat.sub_pos_of_lt hk_lt_n
  have hsqn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hk_eq : (k : ℝ) = α * n + t := by dsimp only [t]; ring
  have hnk_eq : ((n - k : ℕ) : ℝ) = (1 - α) * n - t := by
    rw [Nat.cast_sub hkn]; dsimp only [t]; ring
  have hprod_eq : (k : ℝ) * ((n - k : ℕ) : ℝ) =
      α * (1 - α) * (n : ℝ) ^ 2 + (1 - 2 * α) * n * t - t ^ 2 := by
    rw [hk_eq, hnk_eq]; ring
  have ht_le : |t| ≤ M * σ * Real.sqrt n := hk
  have hdiff_den :
      |α * (1 - α) * (n : ℝ) ^ 2 - (k : ℝ) * ((n - k : ℕ) : ℝ)| ≤
        M * σ * (n : ℝ) * Real.sqrt n + (M * σ) ^ 2 * n := by
    rw [hprod_eq]
    have hsub : α * (1 - α) * (n : ℝ) ^ 2 -
          (α * (1 - α) * (n : ℝ) ^ 2 + (1 - 2 * α) * n * t - t ^ 2) =
        -(1 - 2 * α) * n * t + t ^ 2 := by ring
    rw [hsub]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos hn_pos, abs_pow]
    have h12α : |1 - 2 * α| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hterm1 : |1 - 2 * α| * (n : ℝ) * |t| ≤ 1 * (n : ℝ) * (M * σ * Real.sqrt n) := by
      gcongr
    have hterm2 : |t| ^ 2 ≤ (M * σ * Real.sqrt n) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg t) ht_le 2
    have hsq_eq : (M * σ * Real.sqrt n) ^ 2 = (M * σ) ^ 2 * n := by
      rw [mul_pow, Real.sq_sqrt hn_pos.le]
    linarith
  have hprod_ge : c ^ 2 * (n : ℝ) ^ 2 / 4 ≤ (k : ℝ) * ((n - k : ℕ) : ℝ) := by
    calc c ^ 2 * (n : ℝ) ^ 2 / 4 = (c * n / 2) * (c * n / 2) := by ring
      _ ≤ (k : ℝ) * ((n - k : ℕ) : ℝ) :=
          mul_le_mul hk_bounds.1 hk_bounds.2 (by positivity) (by positivity)
  have hsq_err : |F2 ^ 2 - 1| ≤ δ / 2 := by
    dsimp only [F2]
    have hk_rpos : (0 : ℝ) < k := by exact_mod_cast hk_pos
    have hnk_rpos : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast hnk_pos
    have hknk_pos : 0 < (k : ℝ) * ((n - k : ℕ) : ℝ) := mul_pos hk_rpos hnk_rpos
    have hnum_nn : 0 ≤ α * (1 - α) * (n : ℝ) ^ 2 :=
      mul_nonneg (mul_nonneg hα0.le (sub_nonneg.mpr hα1.le)) (sq_nonneg _)
    rw [Real.sq_sqrt (div_nonneg hnum_nn hknk_pos.le), div_sub_one hknk_pos.ne',
      abs_div, abs_of_pos hknk_pos]
    have hden_p : 0 < c ^ 2 * (n : ℝ) ^ 2 / 4 := by positivity
    have hA : 4 * M * σ / (c ^ 2 * Real.sqrt n) ≤ δ / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h5b' : 16 * M * σ ≤ Real.sqrt n * (c ^ 2 * δ) :=
        (div_le_iff₀ (by positivity)).mp h5b
      linarith
    have hB : 4 * (M * σ) ^ 2 / (c ^ 2 * n) ≤ δ / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h5a' : 16 * (M * σ) ^ 2 ≤ Real.sqrt n * (c ^ 2 * δ) :=
        (div_le_iff₀ (by positivity)).mp h5a
      have hsq_le_n : Real.sqrt n ≤ n := by
        calc Real.sqrt n = Real.sqrt n * 1 := (mul_one _).symm
          _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left hsq_ge1 hsqn_pos.le
          _ = n := Real.mul_self_sqrt hn_pos.le
      have h5a'' : 16 * (M * σ) ^ 2 ≤ n * (c ^ 2 * δ) :=
        h5a'.trans (mul_le_mul_of_nonneg_right hsq_le_n (by positivity))
      linarith
    calc |α * (1 - α) * (n : ℝ) ^ 2 - (k : ℝ) * ((n - k : ℕ) : ℝ)| /
          ((k : ℝ) * ((n - k : ℕ) : ℝ))
        ≤ (M * σ * (n : ℝ) * Real.sqrt n + (M * σ) ^ 2 * n) / (c ^ 2 * (n : ℝ) ^ 2 / 4) :=
          div_le_div₀ (by positivity) hdiff_den hden_p hprod_ge
      _ = 4 * M * σ / (c ^ 2 * Real.sqrt n) + 4 * (M * σ) ^ 2 / (c ^ 2 * n) := by
          have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn_pos.le
          have h1 : (M * σ * (n : ℝ) * Real.sqrt n) / (c ^ 2 * (n : ℝ) ^ 2 / 4) =
              4 * M * σ / (c ^ 2 * Real.sqrt n) := by
            rw [div_eq_div_iff (by positivity) (by positivity)]
            calc M * σ * (n : ℝ) * Real.sqrt n * (c ^ 2 * Real.sqrt n)
                = M * σ * c ^ 2 * (n : ℝ) * (Real.sqrt n ^ 2) := by ring
              _ = M * σ * c ^ 2 * (n : ℝ) * (n : ℝ) := by rw [hsq]
              _ = 4 * M * σ * (c ^ 2 * (n : ℝ) ^ 2 / 4) := by ring
          have h2 : ((M * σ) ^ 2 * (n : ℝ)) / (c ^ 2 * (n : ℝ) ^ 2 / 4) =
              4 * (M * σ) ^ 2 / (c ^ 2 * n) := by
            have hcne : c ≠ 0 := hc_pos.ne'
            have hnne : (n : ℝ) ≠ 0 := hn_pos.ne'
            field_simp
          rw [add_div, h1, h2]
      _ ≤ δ / 4 + δ / 4 := add_le_add hA hB
      _ = δ / 2 := by ring
  have hF2_nn : 0 ≤ F2 := Real.sqrt_nonneg _
  calc |F2 - 1| ≤ |F2 - 1| * (F2 + 1) := le_mul_of_one_le_right (abs_nonneg _) (by linarith [hF2_nn])
    _ = |(F2 - 1) * (F2 + 1)| := by rw [abs_mul, abs_of_pos (show 0 < F2 + 1 by linarith [hF2_nn])]
    _ = |F2 ^ 2 - 1| := by rw [show (F2 - 1) * (F2 + 1) = F2 ^ 2 - 1 by ring]
    _ ≤ δ / 2 := hsq_err

private lemma stirling_F3_bound {α M σ c δ : ℝ} {n k : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1) (hc_pos : 0 < c) (hc_le1 : c ≤ α) (hc_le2 : c ≤ 1 - α)
    (hσ_pos : 0 < σ) (hM : 0 < M) (hδ_pos : 0 < δ) (hδ_half : δ ≤ 1 / 2)
    (hn_pos : (0 : ℝ) < n) (hk_lt_n : k < n) (hk : |(k : ℝ) - α * n| ≤ M * σ * Real.sqrt n)
    (h2 : 4 * M * σ / c ≤ Real.sqrt n)
    (h4 : (4 * (M * σ) ^ 3 / c ^ 3) / δ ≤ Real.sqrt n) :
    |((α * n / k) ^ k * ((1 - α) * n / ((n - k : ℕ) : ℝ)) ^ (n - k)) /
        Real.exp (-((k : ℝ) - α * n) ^ 2 / (2 * n * (α * (1 - α)))) - 1| ≤ 2 * δ := by
  let t : ℝ := (k : ℝ) - α * n
  let F3 : ℝ := (α * n / k) ^ k * ((1 - α) * n / ((n - k : ℕ) : ℝ)) ^ (n - k)
  let u1 : ℝ := t / (α * n)
  let u2 : ℝ := -t / ((1 - α) * n)
  have hkn : k ≤ n := hk_lt_n.le
  have hsqn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hk_eq : (k : ℝ) = α * n + t := by dsimp only [t]; ring
  have hnk_eq : ((n - k : ℕ) : ℝ) = (1 - α) * n - t := by
    rw [Nat.cast_sub hkn]; dsimp only [t]; ring
  have h1u1 : 1 + u1 = (k : ℝ) / (α * n) := by
    dsimp only [u1]; rw [hk_eq]; field_simp
  have h1u2 : 1 + u2 = ((n - k : ℕ) : ℝ) / ((1 - α) * n) := by
    dsimp only [u2]; rw [hnk_eq]
    have h1a : 1 - α ≠ 0 := (sub_pos.mpr hα1).ne'
    field_simp
    ring
  have hu1_le : |u1| ≤ 1 / 2 := by
    dsimp only [u1]
    rw [abs_div, abs_of_pos (mul_pos hα0 hn_pos)]
    calc |t| / (α * n) ≤ (M * σ * Real.sqrt n) / (c * n) := by
          apply div_le_div₀ (by positivity) hk (mul_pos hc_pos hn_pos)
            (mul_le_mul_of_nonneg_right hc_le1 hn_pos.le)
      _ = (M * σ) / (c * Real.sqrt n) := by
          have hn_sq : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn_pos.le).symm
          nth_rewrite 2 [hn_sq]
          field_simp
      _ ≤ 1 / 4 := by
          rw [div_le_iff₀ (mul_pos hc_pos hsqn_pos)]
          have h2' : 4 * M * σ ≤ c * Real.sqrt n := by linarith [(div_le_iff₀ hc_pos).mp h2]
          linarith
      _ ≤ 1 / 2 := by norm_num
  have hu2_le : |u2| ≤ 1 / 2 := by
    dsimp only [u2]
    rw [abs_div, abs_neg, abs_of_pos (mul_pos (sub_pos.mpr hα1) hn_pos)]
    calc |t| / ((1 - α) * n) ≤ (M * σ * Real.sqrt n) / (c * n) := by
          apply div_le_div₀ (by positivity) hk (mul_pos hc_pos hn_pos)
            (mul_le_mul_of_nonneg_right hc_le2 hn_pos.le)
      _ = (M * σ) / (c * Real.sqrt n) := by
          have hn_sq : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn_pos.le).symm
          nth_rewrite 2 [hn_sq]
          field_simp
      _ ≤ 1 / 4 := by
          rw [div_le_iff₀ (mul_pos hc_pos hsqn_pos)]
          have h2' : 4 * M * σ ≤ c * Real.sqrt n := by linarith [(div_le_iff₀ hc_pos).mp h2]
          linarith
      _ ≤ 1 / 2 := by norm_num
  have hu1_pos : 0 < 1 + u1 := by linarith [(abs_le.mp hu1_le).1]
  have hu2_pos : 0 < 1 + u2 := by linarith [(abs_le.mp hu2_le).1]
  have hF3_exp : F3 = Real.exp (-((k : ℝ) * Real.log (1 + u1) +
      ((n - k : ℕ) : ℝ) * Real.log (1 + u2))) := by
    dsimp only [F3]
    rw [Real.exp_neg, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hu1_pos,
      Real.exp_log hu2_pos, h1u1, h1u2]
    rw [show (((k : ℝ) / (α * n)) ^ k * (((n - k : ℕ) : ℝ) / ((1 - α) * n)) ^ (n - k))⁻¹ =
        (α * n / k) ^ k * ((1 - α) * n / ((n - k : ℕ) : ℝ)) ^ (n - k) by
      rw [mul_inv, ← inv_pow, ← inv_pow, inv_div, inv_div]]
  change |F3 / Real.exp (-t ^ 2 / (2 * n * (α * (1 - α)))) - 1| ≤ 2 * δ
  rw [hF3_exp, ← Real.exp_sub]
  have hquad_eq :
      (k : ℝ) * (u1 - u1 ^ 2 / 2) + ((n - k : ℕ) : ℝ) * (u2 - u2 ^ 2 / 2) -
        t ^ 2 / (2 * n * (α * (1 - α))) =
      t ^ 3 / (2 * (n : ℝ) ^ 2) * (1 / (1 - α) ^ 2 - 1 / α ^ 2) := by
    dsimp only [u1, u2]
    rw [hk_eq, hnk_eq]
    have ha_ne : α ≠ 0 := hα0.ne'
    have h1a_ne : 1 - α ≠ 0 := (sub_pos.mpr hα1).ne'
    have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
    field_simp
    ring
  have hexp_diff :
      |-((k : ℝ) * Real.log (1 + u1) + ((n - k : ℕ) : ℝ) * Real.log (1 + u2)) -
          (-t ^ 2 / (2 * n * (α * (1 - α))))| ≤ δ := by
    have hid : -((k : ℝ) * Real.log (1 + u1) + ((n - k : ℕ) : ℝ) * Real.log (1 + u2)) -
          (-t ^ 2 / (2 * n * (α * (1 - α)))) =
        -(k : ℝ) * (Real.log (1 + u1) - (u1 - u1 ^ 2 / 2)) -
          ((n - k : ℕ) : ℝ) * (Real.log (1 + u2) - (u2 - u2 ^ 2 / 2)) -
          ((k : ℝ) * (u1 - u1 ^ 2 / 2) + ((n - k : ℕ) : ℝ) * (u2 - u2 ^ 2 / 2) -
            t ^ 2 / (2 * n * (α * (1 - α)))) := by ring
    rw [hid, hquad_eq]
    have h_tri : ∀ x y z : ℝ, |x - y - z| ≤ |x| + |y| + |z| := fun x y z => by
      linarith [abs_sub (x - y) z, abs_sub x y]
    refine (h_tri _ _ _).trans ?_
    simp only [abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k),
      abs_of_nonneg (Nat.cast_nonneg (n - k) : (0 : ℝ) ≤ ((n - k : ℕ) : ℝ))]
    have h1t : (k : ℝ) * |Real.log (1 + u1) - (u1 - u1 ^ 2 / 2)| ≤ n * |u1| ^ 3 :=
      mul_le_mul (by exact_mod_cast hkn) (abs_log_one_add_sub_le hu1_le) (abs_nonneg _) hn_pos.le
    have h2t : ((n - k : ℕ) : ℝ) * |Real.log (1 + u2) - (u2 - u2 ^ 2 / 2)| ≤ n * |u2| ^ 3 :=
      mul_le_mul (by exact_mod_cast Nat.sub_le n k) (abs_log_one_add_sub_le hu2_le)
        (abs_nonneg _) hn_pos.le
    have hu1_cube : (n : ℝ) * |u1| ^ 3 ≤ (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) := by
      dsimp only [u1]
      rw [abs_div, abs_of_pos (mul_pos hα0 hn_pos), div_pow]
      have ht3 : |t| ^ 3 ≤ (M * σ * Real.sqrt n) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hk 3
      calc (n : ℝ) * (|t| ^ 3 / (α * n) ^ 3)
          ≤ (n : ℝ) * ((M * σ * Real.sqrt n) ^ 3 / (c * n) ^ 3) := by gcongr
        _ = (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) := by
            rw [mul_pow, mul_pow, mul_pow, show (Real.sqrt n) ^ 3 = n * Real.sqrt n by
              rw [pow_succ, Real.sq_sqrt hn_pos.le]]
            field_simp
            rw [Real.sq_sqrt hn_pos.le]
    have hu2_cube : (n : ℝ) * |u2| ^ 3 ≤ (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) := by
      dsimp only [u2]
      rw [abs_div, abs_neg, abs_of_pos (mul_pos (sub_pos.mpr hα1) hn_pos), div_pow]
      have ht3 : |t| ^ 3 ≤ (M * σ * Real.sqrt n) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hk 3
      calc (n : ℝ) * (|t| ^ 3 / ((1 - α) * n) ^ 3)
          ≤ (n : ℝ) * ((M * σ * Real.sqrt n) ^ 3 / (c * n) ^ 3) := by gcongr
        _ = (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) := by
            rw [mul_pow, mul_pow, mul_pow, show (Real.sqrt n) ^ 3 = n * Real.sqrt n by
              rw [pow_succ, Real.sq_sqrt hn_pos.le]]
            field_simp
            rw [Real.sq_sqrt hn_pos.le]
    have h3t : |t ^ 3 / (2 * (n : ℝ) ^ 2) * (1 / (1 - α) ^ 2 - 1 / α ^ 2)| ≤
        2 * (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) := by
      rw [abs_mul, abs_div, abs_pow, abs_of_pos (by positivity : 0 < 2 * (n : ℝ) ^ 2)]
      have hdiff_c : |1 / (1 - α) ^ 2 - 1 / α ^ 2| ≤ 2 / c ^ 2 := by
        refine (abs_sub _ _).trans ?_
        rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
        have ha1c : 1 / (1 - α) ^ 2 ≤ 1 / c ^ 2 := by gcongr
        have ha2c : 1 / α ^ 2 ≤ 1 / c ^ 2 := by gcongr
        have hadd : 1 / c ^ 2 + 1 / c ^ 2 = 2 / c ^ 2 := by ring
        linarith [ha1c, ha2c, hadd]
      have ht3 : |t| ^ 3 ≤ (M * σ * Real.sqrt n) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hk 3
      have hc1 : c ≤ 1 := hc_le1.trans hα1.le
      calc |t| ^ 3 / (2 * (n : ℝ) ^ 2) * |1 / (1 - α) ^ 2 - 1 / α ^ 2|
          ≤ (M * σ * Real.sqrt n) ^ 3 / (2 * (n : ℝ) ^ 2) * (2 / c ^ 2) := by gcongr
        _ = (M * σ) ^ 3 / (c ^ 2 * Real.sqrt n) := by
            rw [mul_pow, show (Real.sqrt n) ^ 3 = n * Real.sqrt n by
              rw [pow_succ, Real.sq_sqrt hn_pos.le]]
            field_simp
            rw [Real.sq_sqrt hn_pos.le]
        _ ≤ 2 * (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) := by
            have hc3 : c ^ 3 ≤ c ^ 2 := by
              calc c ^ 3 = c ^ 2 * c := by ring
                _ ≤ c ^ 2 * 1 := mul_le_mul_of_nonneg_left hc1 (sq_nonneg c)
                _ = c ^ 2 := mul_one _
            have hnum : (M * σ) ^ 3 / (c ^ 2 * Real.sqrt n) ≤
                (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) := by gcongr
            have h2eq : (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) +
                (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) = 2 * (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) := by
              ring
            linarith [hnum, h2eq, show 0 ≤ (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) by positivity]
    have hsum4 : 4 * (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) ≤ δ := by
      rw [show 4 * (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) = (4 * (M * σ) ^ 3 / c ^ 3) / Real.sqrt n by
        ring]
      rw [div_le_iff₀ hsqn_pos]
      linarith [(div_le_iff₀ hδ_pos).mp h4]
    have h3t' : |t ^ 3 / (2 * (n : ℝ) ^ 2)| * |1 / (1 - α) ^ 2 - 1 / α ^ 2| ≤
        2 * (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) := by
      rw [← abs_mul]
      exact h3t
    calc (k : ℝ) * |Real.log (1 + u1) - (u1 - u1 ^ 2 / 2)| +
          ((n - k : ℕ) : ℝ) * |Real.log (1 + u2) - (u2 - u2 ^ 2 / 2)| +
          |t ^ 3 / (2 * (n : ℝ) ^ 2)| * |1 / (1 - α) ^ 2 - 1 / α ^ 2|
        ≤ (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) + (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) +
            2 * (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) :=
          add_le_add (add_le_add (h1t.trans hu1_cube) (h2t.trans hu2_cube)) h3t'
      _ = 4 * (M * σ) ^ 3 / (c ^ 3 * Real.sqrt n) := by ring
      _ ≤ δ := hsum4
  exact (abs_exp_sub_one_le_two_mul (hexp_diff.trans hδ_half)).trans (by linarith [hexp_diff])

private lemma binom_stirling_unif {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ k : ℕ,
      |(k : ℝ) - α * n| ≤ M * Real.sqrt (α * (1 - α)) * Real.sqrt n →
      0 < k ∧ k < n ∧
        |Real.sqrt (2 * Real.pi * n) * Real.sqrt (α * (1 - α)) * binomP n α k /
          Real.exp (-((k : ℝ) - α * n) ^ 2 / (2 * n * (α * (1 - α)))) - 1| ≤ ε := by
  let σ : ℝ := Real.sqrt (α * (1 - α))
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr (mul_pos hα0 (sub_pos.mpr hα1))
  let c : ℝ := min α (1 - α)
  have hc_pos : 0 < c := lt_min hα0 (sub_pos.mpr hα1)
  have hc_le1 : c ≤ α := min_le_left _ _
  have hc_le2 : c ≤ 1 - α := min_le_right _ _
  let δ : ℝ := min (min (ε / 30) (1 / 4)) (Real.sqrt Real.pi / 4)
  have hδ_pos : 0 < δ := by positivity
  obtain ⟨K₀, hK₀⟩ := Metric.tendsto_atTop.mp Stirling.tendsto_stirlingSeq_sqrt_pi δ hδ_pos
  have hsq_tendsto : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  let Cpow : ℝ := 4 * (M * σ) ^ 3 / c ^ 3
  let B₁ : ℝ := max (2 * K₀ / c + 2) (4 * M * σ / c + 2)
  let B₂ : ℝ := max (4 * (M * σ) ^ 2 / c ^ 2 + 2) (Cpow / δ + 2)
  let B₃ : ℝ := max (16 * (M * σ) ^ 2 / (c ^ 2 * δ) + 2) (16 * M * σ / (c ^ 2 * δ) + 2)
  let B₀ : ℝ := max B₁ (max B₂ B₃)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hsq_tendsto.eventually_ge_atTop B₀)
  refine ⟨max N₀ 4, fun n hn k hk => ?_⟩
  have hnN : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  have hn_pos : (0 : ℝ) < n := by positivity
  have hsqn : B₀ ≤ Real.sqrt n := hN₀ n hnN
  have h1 : 2 * K₀ / c ≤ Real.sqrt n :=
    le_trans (by linarith [le_max_left (2 * K₀ / c + 2) (4 * M * σ / c + 2)])
      ((le_max_left B₁ _).trans hsqn)
  have h2 : 4 * M * σ / c ≤ Real.sqrt n :=
    le_trans (by linarith [le_max_right (2 * K₀ / c + 2) (4 * M * σ / c + 2)])
      ((le_max_left B₁ _).trans hsqn)
  have h4 : Cpow / δ ≤ Real.sqrt n :=
    le_trans (by linarith [le_max_right (4 * (M * σ) ^ 2 / c ^ 2 + 2) (Cpow / δ + 2)])
      ((le_trans (le_max_left B₂ B₃) (le_max_right B₁ _)).trans hsqn)
  have h5a : 16 * (M * σ) ^ 2 / (c ^ 2 * δ) ≤ Real.sqrt n := by
    have hB3 := le_max_left (16 * (M * σ) ^ 2 / (c ^ 2 * δ) + 2) (16 * M * σ / (c ^ 2 * δ) + 2)
    have : 16 * (M * σ) ^ 2 / (c ^ 2 * δ) + 2 ≤ Real.sqrt n :=
      le_trans hB3 ((le_trans (le_max_right B₂ B₃) (le_max_right B₁ _)).trans hsqn)
    linarith
  have h5b : 16 * M * σ / (c ^ 2 * δ) ≤ Real.sqrt n := by
    have hB3 := le_max_right (16 * (M * σ) ^ 2 / (c ^ 2 * δ) + 2) (16 * M * σ / (c ^ 2 * δ) + 2)
    have : 16 * M * σ / (c ^ 2 * δ) + 2 ≤ Real.sqrt n :=
      le_trans hB3 ((le_trans (le_max_right B₂ B₃) (le_max_right B₁ _)).trans hsqn)
    linarith
  have hms : M * σ * Real.sqrt n ≤ c * n / 4 := by
    have h2' : 4 * M * σ ≤ c * Real.sqrt n := by linarith [(div_le_iff₀ hc_pos).mp h2]
    calc M * σ * Real.sqrt n = (4 * M * σ) * Real.sqrt n / 4 := by ring
      _ ≤ (c * Real.sqrt n) * Real.sqrt n / 4 := by gcongr
      _ = c * n / 4 := by rw [mul_assoc, Real.mul_self_sqrt hn_pos.le]
  have hk_bounds : c * n / 2 ≤ k ∧ c * n / 2 ≤ ((n - k : ℕ) : ℝ) := by
    have hab := abs_le.mp hk
    have hkl : α * n - M * σ * Real.sqrt n ≤ k := by linarith
    have hku : (k : ℝ) ≤ α * n + M * σ * Real.sqrt n := by linarith
    have hc_le : 3 * c * n / 4 ≤ k := by
      have : c * n ≤ α * n := mul_le_mul_of_nonneg_right hc_le1 hn_pos.le
      linarith
    have hnc_le : 3 * c * n / 4 ≤ (n : ℝ) - k := by
      have : c * n ≤ (1 - α) * n := mul_le_mul_of_nonneg_right hc_le2 hn_pos.le
      linarith
    have hkn : k ≤ n := by
      by_contra hbad
      have : (n : ℝ) < k := by exact_mod_cast (by omega : n < k)
      linarith [show 0 < c * n / 4 by positivity]
    rw [Nat.cast_sub hkn]
    exact ⟨by linarith [show 0 < c * n / 4 by positivity],
      by linarith [show 0 < c * n / 4 by positivity]⟩
  have hk_pos : 0 < k := by
    by_contra hk0
    have : k = 0 := by omega
    subst this
    simp only [Nat.cast_zero] at hk_bounds
    linarith [show 0 < c * n / 2 by positivity]
  have hnk_pos : 0 < n - k := by
    by_contra hnk0
    have : n - k = 0 := by omega
    rw [this, Nat.cast_zero] at hk_bounds
    linarith [show 0 < c * n / 2 by positivity]
  have hk_lt_n : k < n := by omega
  refine ⟨hk_pos, hk_lt_n, ?_⟩
  have hsq_ge1 : 1 ≤ Real.sqrt n := by
    calc (1 : ℝ) ≤ Real.sqrt 4 := by norm_num
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hn4)
  have hK₀_le_cn : (K₀ : ℝ) ≤ c * n / 2 := by
    have h1' : 2 * K₀ ≤ c * Real.sqrt n := by linarith [(div_le_iff₀ hc_pos).mp h1]
    calc (K₀ : ℝ) ≤ (c * Real.sqrt n) / 2 := by linarith
      _ = (c * Real.sqrt n * 1) / 2 := by ring
      _ ≤ (c * Real.sqrt n * Real.sqrt n) / 2 := by gcongr
      _ = c * n / 2 := by rw [mul_assoc, Real.mul_self_sqrt hn_pos.le]
  have hK₀_n : K₀ ≤ n := by
    have hcn : c * n ≤ 1 * n := mul_le_mul_of_nonneg_right (hc_le1.trans hα1.le) hn_pos.le
    have : (K₀ : ℝ) ≤ n := by linarith [hK₀_le_cn, hcn]
    exact_mod_cast this
  have hk_ge_K₀ : K₀ ≤ k := by exact_mod_cast (hK₀_le_cn.trans hk_bounds.1)
  have hnk_ge_K₀ : K₀ ≤ n - k := by exact_mod_cast (hK₀_le_cn.trans hk_bounds.2)
  have hSn : |Stirling.stirlingSeq n - Real.sqrt Real.pi| < δ := by
    simpa [Real.dist_eq] using hK₀ n hK₀_n
  have hSk : |Stirling.stirlingSeq k - Real.sqrt Real.pi| < δ := by
    simpa [Real.dist_eq] using hK₀ k hk_ge_K₀
  have hSnk : |Stirling.stirlingSeq (n - k) - Real.sqrt Real.pi| < δ := by
    simpa [Real.dist_eq] using hK₀ (n - k) hnk_ge_K₀
  have hS_pos : ∀ m : ℕ, 0 < m → 0 < Stirling.stirlingSeq m := fun m _ => by
    unfold Stirling.stirlingSeq; positivity
  have hfac : ∀ m : ℕ, 0 < m →
      (Nat.factorial m : ℝ) =
        Stirling.stirlingSeq m * Real.sqrt (2 * m) * ((m : ℝ) ^ m / (Real.exp 1) ^ m) := by
    intro m _
    unfold Stirling.stirlingSeq
    have hm_pos : (0 : ℝ) < m := by positivity
    rw [div_pow]; field_simp
  have hch_eq : (n.choose k : ℝ) =
      (Nat.factorial n : ℝ) / ((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ)) := by
    have h' : (n.choose k : ℝ) * ((Nat.factorial k : ℝ) * (Nat.factorial (n - k) : ℝ)) =
        (Nat.factorial n : ℝ) := by
      have hnat : n.choose k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n :=
        Nat.choose_mul_factorial_mul_factorial hk_lt_n.le
      rw [← mul_assoc]
      exact_mod_cast hnat
    exact eq_div_of_mul_eq (by positivity) h'
  let F1 : ℝ := Real.sqrt Real.pi * Stirling.stirlingSeq n /
    (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k))
  let F2 : ℝ := Real.sqrt (α * (1 - α) * (n : ℝ) ^ 2 / ((k : ℝ) * ((n - k : ℕ) : ℝ)))
  let F3 : ℝ := (α * n / k) ^ k * ((1 - α) * n / ((n - k : ℕ) : ℝ)) ^ (n - k)
  have hdecomp : Real.sqrt (2 * Real.pi * n) * σ * binomP n α k = F1 * F2 * F3 := by
    unfold binomP
    rw [hch_eq, hfac n (by omega), hfac k hk_pos, hfac (n - k) hnk_pos]
    have hexp_n : (Real.exp 1) ^ k * (Real.exp 1) ^ (n - k) = (Real.exp 1) ^ n := by
      rw [← pow_add, Nat.add_sub_cancel' hk_lt_n.le]
    have hk_ne : (k : ℝ) ≠ 0 := by positivity
    have hnk_ne : ((n - k : ℕ) : ℝ) ≠ 0 := by positivity
    have hn_ne : (n : ℝ) ≠ 0 := by positivity
    have hSk_ne : Stirling.stirlingSeq k ≠ 0 := (hS_pos k hk_pos).ne'
    have hSnk_ne : Stirling.stirlingSeq (n - k) ≠ 0 := (hS_pos (n - k) hnk_pos).ne'
    have hsqrt_eq :
        Real.sqrt (2 * Real.pi * n) * σ * Real.sqrt (2 * n) /
          (Real.sqrt (2 * k) * Real.sqrt (2 * ((n - k : ℕ) : ℝ))) = Real.sqrt Real.pi * F2 := by
      dsimp only [F2, σ]
      have h1' : Real.sqrt (2 * Real.pi * n) * Real.sqrt (2 * n) = Real.sqrt Real.pi * (2 * n) := by
        rw [show 2 * Real.pi * n = Real.pi * (2 * n) by ring, Real.sqrt_mul Real.pi_pos.le,
          mul_assoc, Real.mul_self_sqrt (by positivity)]
      have h2' : Real.sqrt (2 * k) * Real.sqrt (2 * ((n - k : ℕ) : ℝ)) =
          2 * Real.sqrt ((k : ℝ) * ((n - k : ℕ) : ℝ)) := by
        rw [Real.sqrt_mul (by norm_num) k, Real.sqrt_mul (by norm_num) ((n - k : ℕ) : ℝ)]
        rw [show Real.sqrt 2 * Real.sqrt k * (Real.sqrt 2 * Real.sqrt ((n - k : ℕ) : ℝ)) =
          (Real.sqrt 2 * Real.sqrt 2) * (Real.sqrt k * Real.sqrt ((n - k : ℕ) : ℝ)) by ring]
        rw [Real.mul_self_sqrt (by norm_num), ← Real.sqrt_mul (by positivity)]
      rw [mul_assoc (Real.sqrt (2 * Real.pi * n)) σ (Real.sqrt (2 * n)), mul_comm σ (Real.sqrt (2 * n)),
        ← mul_assoc (Real.sqrt (2 * Real.pi * n)) (Real.sqrt (2 * n)) σ, h1', h2']
      have h3' : Real.sqrt (α * (1 - α)) * (2 * n) / (2 * Real.sqrt (k * ((n - k : ℕ) : ℝ))) =
          Real.sqrt (α * (1 - α) * (n : ℝ) ^ 2 / ((k : ℝ) * ((n - k : ℕ) : ℝ))) := by
        have hαm : 0 ≤ α * (1 - α) := mul_nonneg hα0.le (sub_nonneg.mpr hα1.le)
        rw [Real.sqrt_div (mul_nonneg hαm (sq_nonneg _)), Real.sqrt_mul hαm, Real.sqrt_sq hn_pos.le]
        ring
      calc Real.sqrt Real.pi * (2 * n) * Real.sqrt (α * (1 - α)) /
            (2 * Real.sqrt ((k : ℝ) * ((n - k : ℕ) : ℝ)))
          = Real.sqrt Real.pi *
              (Real.sqrt (α * (1 - α)) * (2 * n) / (2 * Real.sqrt ((k : ℝ) * ((n - k : ℕ) : ℝ)))) := by
            ring
        _ = Real.sqrt Real.pi * _ := by rw [h3']
    have hpow_eq :
        ((n : ℝ) ^ n / (Real.exp 1) ^ n) /
          (((k : ℝ) ^ k / (Real.exp 1) ^ k) * (((n - k : ℕ) : ℝ) ^ (n - k) / (Real.exp 1) ^ (n - k))) *
          α ^ k * (1 - α) ^ (n - k) = F3 := by
      dsimp only [F3]
      have hsplit : (n : ℝ) ^ n = (n : ℝ) ^ k * (n : ℝ) ^ (n - k) := by
        rw [← pow_add, Nat.add_sub_cancel' hk_lt_n.le]
      rw [hsplit, div_pow, div_pow, mul_pow, mul_pow]
      have hexp_ne : (Real.exp 1) ^ n ≠ 0 := by positivity
      have hexp_k_ne : (Real.exp 1) ^ k ≠ 0 := by positivity
      have hexp_nk_ne : (Real.exp 1) ^ (n - k) ≠ 0 := by positivity
      field_simp
      rw [hexp_n]
    calc Real.sqrt (2 * Real.pi * n) * σ *
          (Stirling.stirlingSeq n * Real.sqrt (2 * n) * ((n : ℝ) ^ n / (Real.exp 1) ^ n) /
            (Stirling.stirlingSeq k * Real.sqrt (2 * k) * ((k : ℝ) ^ k / (Real.exp 1) ^ k) *
              (Stirling.stirlingSeq (n - k) * Real.sqrt (2 * ((n - k : ℕ) : ℝ)) *
                (((n - k : ℕ) : ℝ) ^ (n - k) / (Real.exp 1) ^ (n - k)))) *
            α ^ k * (1 - α) ^ (n - k))
        = (Stirling.stirlingSeq n / (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k))) *
            (Real.sqrt (2 * Real.pi * n) * σ * Real.sqrt (2 * n) /
              (Real.sqrt (2 * k) * Real.sqrt (2 * ((n - k : ℕ) : ℝ)))) *
            (((n : ℝ) ^ n / (Real.exp 1) ^ n) /
              (((k : ℝ) ^ k / (Real.exp 1) ^ k) *
                (((n - k : ℕ) : ℝ) ^ (n - k) / (Real.exp 1) ^ (n - k))) *
              α ^ k * (1 - α) ^ (n - k)) := by ring
      _ = F1 * F2 * F3 := by
          rw [hsqrt_eq, hpow_eq]
          dsimp only [F1]
          ring
  have hF1_bound : |F1 - 1| ≤ 6 * δ / Real.sqrt Real.pi :=
    stirling_F1_bound hk_pos hnk_pos hδ_pos (min_le_right _ _) hSn hSk hSnk
  have hF2_bound : |F2 - 1| ≤ δ / 2 :=
    stirling_F2_bound hα0 hα1 hc_pos hσ_pos hM hδ_pos hn_pos hsq_ge1 hk_pos hk_lt_n hk
      hk_bounds h5a h5b
  have hδ_half : δ ≤ 1 / 2 := (min_le_left _ _).trans ((min_le_right _ _).trans (by norm_num))
  have hF3_bound : |F3 / Real.exp (-((k : ℝ) - α * n) ^ 2 / (2 * n * (α * (1 - α)))) - 1| ≤ 2 * δ :=
    stirling_F3_bound hα0 hα1 hc_pos hc_le1 hc_le2 hσ_pos hM hδ_pos hδ_half hn_pos hk_lt_n hk h2 h4
  have hcomb :
      Real.sqrt (2 * Real.pi * n) * σ * binomP n α k /
        Real.exp (-((k : ℝ) - α * n) ^ 2 / (2 * n * (α * (1 - α)))) =
      F1 * F2 * (F3 / Real.exp (-((k : ℝ) - α * n) ^ 2 / (2 * n * (α * (1 - α))))) := by
    rw [hdecomp]
    ring
  rw [hcomb]
  have hsp_ge : (3 / 2 : ℝ) ≤ Real.sqrt Real.pi := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
  have hη_F1 : |F1 - 1| ≤ 4 * δ := hF1_bound.trans (by
    rw [div_le_iff₀ (by positivity)]
    have hmul : 4 * δ * (3 / 2 : ℝ) ≤ 4 * δ * Real.sqrt Real.pi :=
      mul_le_mul_of_nonneg_left hsp_ge (by positivity)
    linarith)
  have hη_F2 : |F2 - 1| ≤ 4 * δ := hF2_bound.trans (by linarith [hδ_pos])
  have hη_F3 : |F3 / Real.exp (-((k : ℝ) - α * n) ^ 2 / (2 * n * (α * (1 - α)))) - 1| ≤ 4 * δ :=
    hF3_bound.trans (by linarith [hδ_pos])
  have h4δ1 : 4 * δ ≤ 1 := by
    have : δ ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  refine (prod3_sub_one_le (by positivity) h4δ1 hη_F1 hη_F2 hη_F3).trans ?_
  have : δ ≤ ε / 30 := (min_le_left _ _).trans (min_le_left _ _)
  linarith

private lemma gaussian_riemann_sum_close {b M h x₀ : ℝ} (hb : 0 < b) (hM : 0 < M) (hh : 0 < h)
    (hMh : 2 * h ≤ M) (hx₀ : M / h + 1 ≤ x₀) :
    |h * ∑ i ∈ Finset.Icc ⌈x₀ - M / h⌉₊ ⌊x₀ + M / h⌋₊,
        Real.exp (-b * (((i : ℝ) - x₀) * h) ^ 2) -
      ∫ x in (-M)..M, Real.exp (-b * x ^ 2)| ≤ 6 * h := by
  let g : ℝ → ℝ := fun x => Real.exp (-b * x ^ 2)
  have hg_cont : Continuous g := by fun_prop
  have hg_int : ∀ u v : ℝ, IntervalIntegrable g volume u v := fun u v =>
    hg_cont.intervalIntegrable u v
  have hg_range : ∀ x, 0 ≤ g x ∧ g x ≤ 1 := fun x =>
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])⟩
  have hg_mono : MonotoneOn g (Set.Iic 0) := by
    intro x hx y hy hxy
    simp only [Set.mem_Iic] at hx hy
    have hsq : y ^ 2 ≤ x ^ 2 := by nlinarith
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hg_anti : AntitoneOn g (Set.Ici 0) := by
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
    exact Real.exp_le_exp.mpr (by nlinarith)
  let a_lo : ℕ := ⌈x₀ - M / h⌉₊
  let a_hi : ℕ := ⌊x₀ + M / h⌋₊
  let m₀ : ℕ := ⌊x₀⌋₊
  let y : ℕ → ℝ := fun i => ((i : ℝ) - x₀) * h
  have hx₀_pos : 0 < x₀ := by have : 0 < M / h := div_pos hM hh; linarith
  have hx_sub_pos : 0 < x₀ - M / h := by linarith
  have hx_add_nn : 0 ≤ x₀ + M / h := by have : 0 < M / h := div_pos hM hh; linarith
  have ha_lo_ge : x₀ - M / h ≤ a_lo := Nat.le_ceil _
  have ha_lo_lt : (a_lo : ℝ) < x₀ - M / h + 1 := Nat.ceil_lt_add_one hx_sub_pos.le
  have hm₀_le : (m₀ : ℝ) ≤ x₀ := Nat.floor_le hx₀_pos.le
  have hm₀_lt : x₀ < (m₀ : ℝ) + 1 := Nat.lt_floor_add_one x₀
  have ha_hi_le : (a_hi : ℝ) ≤ x₀ + M / h := Nat.floor_le hx_add_nn
  have ha_hi_lt : x₀ + M / h < (a_hi : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2mh : 2 ≤ M / h := (le_div_iff₀ hh).mpr hMh
  have ha_lo_lt_m₀ : a_lo ≤ m₀ := by
    have : (a_lo : ℝ) < (m₀ : ℝ) + 1 := by linarith
    exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
  have hm₀_succ_le_hi : m₀ + 1 ≤ a_hi := by
    have : ((m₀ + 1 : ℕ) : ℝ) ≤ x₀ + M / h := by push_cast; linarith
    exact Nat.le_floor this
  have hy_lo_ge : -M ≤ y a_lo := by
    dsimp only [y]
    have hlo : -(M / h) ≤ (a_lo : ℝ) - x₀ := by linarith
    calc -M = -(M / h) * h := by field_simp
      _ ≤ ((a_lo : ℝ) - x₀) * h := mul_le_mul_of_nonneg_right hlo hh.le
  have hy_lo_lt : y a_lo < -M + h := by
    dsimp only [y]
    have hlo : (a_lo : ℝ) - x₀ < -(M / h) + 1 := by linarith
    calc ((a_lo : ℝ) - x₀) * h < (-(M / h) + 1) * h := mul_lt_mul_of_pos_right hlo hh
      _ = -M + h := by field_simp
  have hy_hi_le : y a_hi ≤ M := by
    dsimp only [y]
    have hhi : (a_hi : ℝ) - x₀ ≤ M / h := by linarith
    calc ((a_hi : ℝ) - x₀) * h ≤ (M / h) * h := mul_le_mul_of_nonneg_right hhi hh.le
      _ = M := by field_simp
  have hy_hi_gt : M - h < y a_hi := by
    dsimp only [y]
    have hhi : M / h - 1 < (a_hi : ℝ) - x₀ := by linarith
    calc M - h = (M / h - 1) * h := by field_simp
      _ < ((a_hi : ℝ) - x₀) * h := mul_lt_mul_of_pos_right hhi hh
  have hy_step : ∀ i : ℕ, y (i + 1) = y i + h := fun i => by
    dsimp only [y]; push_cast; ring
  have hy_m₀_le : y m₀ ≤ 0 := by
    dsimp only [y]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hh.le
  have hy_m₀_gt : -h < y m₀ := by
    dsimp only [y]; nlinarith
  have hy_m₀1_pos : 0 < y (m₀ + 1) := by
    dsimp only [y]; push_cast; exact mul_pos (by linarith) hh
  have hy_m₀1_le : y (m₀ + 1) ≤ h := by
    dsimp only [y]; push_cast; nlinarith
  have hcell_lo : ∀ i ∈ Finset.Ico a_lo m₀,
      h * g (y i) ≤ ∫ x in y i..y (i + 1), g x ∧
        ∫ x in y i..y (i + 1), g x ≤ h * g (y (i + 1)) := by
    intro i hi
    have him : i + 1 ≤ m₀ := (Finset.mem_Ico.mp hi).2
    have hy1 : y (i + 1) ≤ 0 := by
      dsimp only [y]
      have : ((i + 1 : ℕ) : ℝ) ≤ m₀ := by exact_mod_cast him
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hh.le
    have hy01 : y i ≤ y (i + 1) := by rw [hy_step]; linarith
    have hconst_lo : h * g (y i) = ∫ _ in y i..y (i + 1), g (y i) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, hy_step, add_sub_cancel_left]
    have hconst_hi : h * g (y (i + 1)) = ∫ _ in y i..y (i + 1), g (y (i + 1)) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, hy_step, add_sub_cancel_left]
    constructor
    · rw [hconst_lo]
      refine intervalIntegral.integral_mono_on hy01 intervalIntegrable_const (hg_int _ _) fun x hx => ?_
      exact hg_mono (hy01.trans hy1) (hx.2.trans hy1) hx.1
    · rw [hconst_hi]
      refine intervalIntegral.integral_mono_on hy01 (hg_int _ _) intervalIntegrable_const fun x hx => ?_
      exact hg_mono (hx.2.trans hy1) hy1 hx.2
  have hcell_hi : ∀ i ∈ Finset.Ico (m₀ + 1) a_hi,
      h * g (y (i + 1)) ≤ ∫ x in y i..y (i + 1), g x ∧
        ∫ x in y i..y (i + 1), g x ≤ h * g (y i) := by
    intro i hi
    have hmi : m₀ + 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have hy0 : 0 ≤ y i := by
      dsimp only [y]
      have : ((m₀ + 1 : ℕ) : ℝ) ≤ i := by exact_mod_cast hmi
      push_cast at this
      exact mul_nonneg (by linarith) hh.le
    have hy01 : y i ≤ y (i + 1) := by rw [hy_step]; linarith
    have hconst_lo : h * g (y (i + 1)) = ∫ _ in y i..y (i + 1), g (y (i + 1)) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, hy_step, add_sub_cancel_left]
    have hconst_hi : h * g (y i) = ∫ _ in y i..y (i + 1), g (y i) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, hy_step, add_sub_cancel_left]
    constructor
    · rw [hconst_lo]
      refine intervalIntegral.integral_mono_on hy01 intervalIntegrable_const (hg_int _ _) fun x hx => ?_
      exact hg_anti (hy0.trans hx.1) (hy0.trans hy01) hx.2
    · rw [hconst_hi]
      refine intervalIntegral.integral_mono_on hy01 (hg_int _ _) intervalIntegrable_const fun x hx => ?_
      exact hg_anti hy0 (hy0.trans hx.1) hx.1
  have hI_lo_ge : h * ∑ i ∈ Finset.Ico a_lo m₀, g (y i) ≤ ∫ x in y a_lo..y m₀, g x := by
    rw [Finset.mul_sum, ← intervalIntegral.sum_integral_adjacent_intervals_Ico ha_lo_lt_m₀]
    · exact Finset.sum_le_sum fun i hi => (hcell_lo i hi).1
    · intro k _; exact hg_int _ _
  have hI_lo_le : ∫ x in y a_lo..y m₀, g x ≤ h * ∑ i ∈ Finset.Ico a_lo m₀, g (y (i + 1)) := by
    rw [Finset.mul_sum, ← intervalIntegral.sum_integral_adjacent_intervals_Ico ha_lo_lt_m₀]
    · exact Finset.sum_le_sum fun i hi => (hcell_lo i hi).2
    · intro k _; exact hg_int _ _
  have hI_hi_ge : h * ∑ i ∈ Finset.Ico (m₀ + 1) a_hi, g (y (i + 1)) ≤
      ∫ x in y (m₀ + 1)..y a_hi, g x := by
    rw [Finset.mul_sum, ← intervalIntegral.sum_integral_adjacent_intervals_Ico hm₀_succ_le_hi]
    · exact Finset.sum_le_sum fun i hi => (hcell_hi i hi).1
    · intro k _; exact hg_int _ _
  have hI_hi_le : ∫ x in y (m₀ + 1)..y a_hi, g x ≤
      h * ∑ i ∈ Finset.Ico (m₀ + 1) a_hi, g (y i) := by
    rw [Finset.mul_sum, ← intervalIntegral.sum_integral_adjacent_intervals_Ico hm₀_succ_le_hi]
    · exact Finset.sum_le_sum fun i hi => (hcell_hi i hi).2
    · intro k _; exact hg_int _ _
  have hgap : ∀ u v : ℝ, u ≤ v → v - u ≤ h →
      0 ≤ ∫ x in u..v, g x ∧ ∫ x in u..v, g x ≤ h := by
    intro u v huv hvh
    constructor
    · exact intervalIntegral.integral_nonneg huv fun x _ => (hg_range x).1
    · calc ∫ x in u..v, g x ≤ ∫ _ in u..v, (1 : ℝ) :=
            intervalIntegral.integral_mono_on huv (hg_int u v) intervalIntegrable_const
              fun x _ => (hg_range x).2
        _ = v - u := by simp
        _ ≤ h := hvh
  have hgap1 := hgap (-M) (y a_lo) hy_lo_ge (by linarith)
  have hgap2 := hgap (y m₀) (y (m₀ + 1)) (by rw [hy_step]; linarith) (by rw [hy_step]; linarith)
  have hgap3 := hgap (y a_hi) M hy_hi_le (by linarith)
  have hsplit_int : ∫ x in (-M)..M, g x =
      (∫ x in (-M)..y a_lo, g x) + (∫ x in y a_lo..y m₀, g x) +
        (∫ x in y m₀..y (m₀ + 1), g x) + (∫ x in y (m₀ + 1)..y a_hi, g x) +
        (∫ x in y a_hi..M, g x) := by
    have s1 := (intervalIntegral.integral_add_adjacent_intervals (hg_int (-M) (y a_lo))
      (hg_int (y a_lo) (y m₀))).symm
    have s2 := (intervalIntegral.integral_add_adjacent_intervals (hg_int (-M) (y m₀))
      (hg_int (y m₀) (y (m₀ + 1)))).symm
    have s3 := (intervalIntegral.integral_add_adjacent_intervals (hg_int (-M) (y (m₀ + 1)))
      (hg_int (y (m₀ + 1)) (y a_hi))).symm
    have s4 := (intervalIntegral.integral_add_adjacent_intervals (hg_int (-M) (y a_hi))
      (hg_int (y a_hi) M)).symm
    linarith
  have hsum_split :
      ∑ i ∈ Finset.Icc a_lo a_hi, g (y i) =
        (∑ i ∈ Finset.Ico a_lo m₀, g (y i)) + g (y m₀) +
          (g (y (m₀ + 1)) + ∑ i ∈ Finset.Ico (m₀ + 1) a_hi, g (y (i + 1))) := by
    have hIcc1 : Finset.Icc a_lo a_hi = Finset.Icc a_lo m₀ ∪ Finset.Icc (m₀ + 1) a_hi := by
      ext i; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hdisj : Disjoint (Finset.Icc a_lo m₀) (Finset.Icc (m₀ + 1) a_hi) :=
      Finset.disjoint_left.mpr fun i h1 h2 => by
        simp only [Finset.mem_Icc] at h1 h2; omega
    have hpart1 : ∑ i ∈ Finset.Icc a_lo m₀, g (y i) =
        (∑ i ∈ Finset.Ico a_lo m₀, g (y i)) + g (y m₀) := by
      rw [← Finset.Ico_insert_right ha_lo_lt_m₀, Finset.sum_insert (by simp)]
      ring
    have hpart2 : ∑ i ∈ Finset.Icc (m₀ + 1) a_hi, g (y i) =
        g (y (m₀ + 1)) + ∑ i ∈ Finset.Ico (m₀ + 1) a_hi, g (y (i + 1)) := by
      have hbi : ∑ i ∈ Finset.Icc (m₀ + 1) a_hi, g (y i) =
          g (y (m₀ + 1)) + ∑ i ∈ Finset.Ioc (m₀ + 1) a_hi, g (y i) := by
        rw [← Finset.Ioc_insert_left hm₀_succ_le_hi, Finset.sum_insert (by simp)]
      have hshift : ∑ i ∈ Finset.Ico (m₀ + 1) a_hi, g (y (i + 1)) =
          ∑ i ∈ Finset.Ioc (m₀ + 1) a_hi, g (y i) := by
        refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
        · intro i hi; simp only [Finset.mem_Ico] at hi; simp only [Finset.mem_Ioc]; omega
        · intro i _ j _ h; omega
        · intro b hb; simp only [Finset.mem_Ioc] at hb
          exact ⟨b - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro i _; rfl
      rw [hbi, hshift]
    rw [hIcc1, Finset.sum_union hdisj, hpart1, hpart2]
  have hsum_split2 :
      ∑ i ∈ Finset.Icc a_lo a_hi, g (y i) =
        (g (y a_lo) + ∑ i ∈ Finset.Ico a_lo m₀, g (y (i + 1))) +
          ((∑ i ∈ Finset.Ico (m₀ + 1) a_hi, g (y i)) + g (y a_hi)) := by
    have hIcc1 : Finset.Icc a_lo a_hi = Finset.Icc a_lo m₀ ∪ Finset.Icc (m₀ + 1) a_hi := by
      ext i; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    have hdisj : Disjoint (Finset.Icc a_lo m₀) (Finset.Icc (m₀ + 1) a_hi) :=
      Finset.disjoint_left.mpr fun i h1 h2 => by
        simp only [Finset.mem_Icc] at h1 h2; omega
    have hpart1 : ∑ i ∈ Finset.Icc a_lo m₀, g (y i) =
        g (y a_lo) + ∑ i ∈ Finset.Ico a_lo m₀, g (y (i + 1)) := by
      have hbi : ∑ i ∈ Finset.Icc a_lo m₀, g (y i) =
          g (y a_lo) + ∑ i ∈ Finset.Ioc a_lo m₀, g (y i) := by
        rw [← Finset.Ioc_insert_left ha_lo_lt_m₀, Finset.sum_insert (by simp)]
      have hshift : ∑ i ∈ Finset.Ico a_lo m₀, g (y (i + 1)) =
          ∑ i ∈ Finset.Ioc a_lo m₀, g (y i) := by
        refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
        · intro i hi; simp only [Finset.mem_Ico] at hi; simp only [Finset.mem_Ioc]; omega
        · intro i _ j _ h; omega
        · intro b hb; simp only [Finset.mem_Ioc] at hb
          exact ⟨b - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro i _; rfl
      rw [hbi, hshift]
    have hpart2 : ∑ i ∈ Finset.Icc (m₀ + 1) a_hi, g (y i) =
        (∑ i ∈ Finset.Ico (m₀ + 1) a_hi, g (y i)) + g (y a_hi) := by
      rw [← Finset.Ico_insert_right hm₀_succ_le_hi, Finset.sum_insert (by simp)]
      ring
    rw [hIcc1, Finset.sum_union hdisj, hpart1, hpart2]
  change |h * ∑ i ∈ Finset.Icc a_lo a_hi, g (y i) - ∫ x in (-M)..M, g x| ≤ 6 * h
  rw [abs_le]
  constructor
  · have halo_nn : 0 ≤ h * g (y a_lo) := mul_nonneg hh.le (hg_range (y a_lo)).1
    have hahi_nn : 0 ≤ h * g (y a_hi) := mul_nonneg hh.le (hg_range (y a_hi)).1
    have hsplit2 : h * ∑ i ∈ Finset.Icc a_lo a_hi, g (y i) =
        h * g (y a_lo) + h * ∑ i ∈ Finset.Ico a_lo m₀, g (y (i + 1)) +
          h * ∑ i ∈ Finset.Ico (m₀ + 1) a_hi, g (y i) + h * g (y a_hi) := by
      rw [hsum_split2]; ring
    linarith [hgap1.2, hgap2.2, hgap3.2, hI_lo_le, hI_hi_le, hsplit_int, hsplit2, hh]
  · have hm₀_ub : h * g (y m₀) ≤ h :=
      mul_le_of_le_one_right hh.le (hg_range (y m₀)).2
    have hm₀1_ub : h * g (y (m₀ + 1)) ≤ h :=
      mul_le_of_le_one_right hh.le (hg_range (y (m₀ + 1))).2
    have hsplit1 : h * ∑ i ∈ Finset.Icc a_lo a_hi, g (y i) =
        h * ∑ i ∈ Finset.Ico a_lo m₀, g (y i) + h * g (y m₀) +
          h * g (y (m₀ + 1)) + h * ∑ i ∈ Finset.Ico (m₀ + 1) a_hi, g (y (i + 1)) := by
      rw [hsum_split]; ring
    linarith [hgap1.1, hgap2.1, hgap3.1, hI_lo_ge, hI_hi_ge, hsplit_int, hsplit1, hh]

private lemma normDen_eq_one_of_one {a : ℝ} (r : ℕ) : normDen 1 a r = 1 := by
  unfold normDen
  simp only [pow_one]
  exact binomP_sum_eq_one r (paramP a)

private lemma pow_ratio_close_of_close {l : ℕ} {s e δs ε₀ : ℝ}
    (hl : 0 < l) (hs_nn : 0 ≤ s) (he_pos : 0 < e) (hδs_pos : 0 < δs)
    (hδs_l4 : (l : ℝ) * δs ≤ 1 / 4) (hδs_eps : (l : ℝ) * δs ≤ ε₀ / 32) (hε₀_pos : 0 < ε₀)
    (hr_diff : |s / e - 1| ≤ δs) :
    |s ^ l / e ^ l - 1| ≤ ε₀ / 16 := by
  have hδs_half : δs ≤ 1 / 2 := by
    have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have h1 : δs ≤ (l : ℝ) * δs := le_mul_of_one_le_left hδs_pos.le hl1
    linarith
  have hq_nn : 0 ≤ s / e := div_nonneg hs_nn he_pos.le
  have hsub_ub : (1 + δs) ^ l - 1 ≤ ε₀ / 16 := by
    have hlδ_nn : 0 ≤ (l : ℝ) * δs := mul_nonneg (Nat.cast_nonneg l) hδs_pos.le
    have hexp1 : 1 + δs ≤ Real.exp δs := by linarith [Real.add_one_le_exp δs]
    have hexp2 : (1 + δs) ^ l ≤ Real.exp ((l : ℝ) * δs) := by
      calc (1 + δs) ^ l ≤ (Real.exp δs) ^ l := pow_le_pow_left₀ (by positivity) hexp1 l
        _ = Real.exp ((l : ℝ) * δs) := by rw [← Real.exp_nat_mul]
    have hexp3 : Real.exp ((l : ℝ) * δs) - 1 ≤ 2 * ((l : ℝ) * δs) := by
      have h1 := abs_exp_sub_one_le_two_mul (by rw [abs_of_nonneg hlδ_nn]; linarith [hδs_l4])
      rw [abs_of_nonneg hlδ_nn] at h1
      exact (abs_le.mp h1).2
    linarith
  have hsub_lb : 1 - (1 - δs) ^ l ≤ ε₀ / 16 := by
    have h1d : 0 ≤ 1 - δs := by linarith [hδs_half]
    have hber : ∀ m : ℕ, 1 - (m : ℝ) * δs ≤ (1 - δs) ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ k ih =>
        rw [pow_succ']
        push_cast
        have hmul := mul_le_mul_of_nonneg_left ih h1d
        have hid : (1 - δs) * (1 - (k : ℝ) * δs) =
            1 - ((k : ℝ) + 1) * δs + (k : ℝ) * δs ^ 2 := by ring
        have hsq : 0 ≤ (k : ℝ) * δs ^ 2 := by positivity
        linarith
    linarith [hber l]
  have hq_lo : 1 - δs ≤ s / e := by linarith [(abs_le.mp hr_diff).1]
  have hq_hi : s / e ≤ 1 + δs := by linarith [(abs_le.mp hr_diff).2]
  have h1d : 0 ≤ 1 - δs := by linarith [hδs_half]
  have hpow_lo : (1 - δs) ^ l ≤ (s / e) ^ l := pow_le_pow_left₀ h1d hq_lo l
  have hpow_hi : (s / e) ^ l ≤ (1 + δs) ^ l := pow_le_pow_left₀ hq_nn hq_hi l
  rw [div_pow] at hpow_lo hpow_hi
  rw [abs_le]
  constructor <;> linarith

private lemma normDen_bulk_close {l r a_lo a_hi : ℕ} {α σ M h δs ε₀ : ℝ}
    (hl2 : 2 ≤ l) (hp0 : 0 < α) (hp1 : α < 1) (hσ_pos : 0 < σ) (hM_pos : 0 < M)
    (hh_pos : 0 < h) (hMh : 2 * h ≤ M) (hx₀_ge : M / h + 1 ≤ α * r)
    (hh_def : h = 1 / (σ * Real.sqrt r))
    (hσ_def : σ = Real.sqrt (α * (1 - α))) (hr_pos : (0 : ℝ) < r)
    (hδs_pos : 0 < δs) (hδs_l4 : (l : ℝ) * δs ≤ 1 / 4) (hδs_eps : (l : ℝ) * δs ≤ ε₀ / 32)
    (hε₀_pos : 0 < ε₀) (hε₀_le1 : ε₀ ≤ 1)
    (ha_lo_def : a_lo = ⌈α * r - M / h⌉₊) (ha_hi_def : a_hi = ⌊α * r + M / h⌋₊)
    (h_err_h : 48 * Real.sqrt l / (Real.sqrt (2 * Real.pi) * σ * ε₀) ≤ Real.sqrt r)
    (hM_bulk : |(Real.sqrt l / Real.sqrt (2 * Real.pi)) *
        (∫ x in (-M)..M, Real.exp (-((l : ℝ) / 2) * x ^ 2)) - 1| < ε₀ / 4)
    (hterm_ratio : ∀ i ∈ Finset.Icc a_lo a_hi,
        |(Real.sqrt (2 * Real.pi * r) * σ * binomP r α i) /
          Real.exp (-((i : ℝ) - α * r) ^ 2 / (2 * r * (α * (1 - α)))) - 1| ≤ δs) :
    |(∑ i ∈ Finset.Icc a_lo a_hi, binomP r α i ^ l) *
        (Real.sqrt l * (Real.sqrt (2 * Real.pi * r) * σ) ^ (l - 1)) - 1| ≤ ε₀ / 2 := by
  have hl : 0 < l := Nat.lt_of_lt_of_le (by norm_num) hl2
  let b : ℝ := (l : ℝ) / 2
  have hb_pos : 0 < b := by positivity
  have hsqr_pos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr_pos
  let W : ℝ := Real.sqrt (2 * Real.pi * r) * σ
  have hW_pos : 0 < W := by positivity
  have hW_eq_h : W = Real.sqrt (2 * Real.pi) / h := by
    dsimp only [W]
    rw [hh_def, show 2 * Real.pi * (r : ℝ) = (2 * Real.pi) * (r : ℝ) by ring,
      Real.sqrt_mul (by positivity)]
    field_simp
  let S : ℕ → ℝ := fun i => W * binomP r α i
  let E : ℕ → ℝ := fun i => Real.exp (-((i : ℝ) - α * r) ^ 2 / (2 * r * (α * (1 - α))))
  have hterm_pow : ∀ i ∈ Finset.Icc a_lo a_hi, |(S i) ^ l / (E i) ^ l - 1| ≤ ε₀ / 16 :=
    fun i hi => pow_ratio_close_of_close hl
      (mul_nonneg hW_pos.le (binomP_nonneg hp0.le hp1.le i)) (Real.exp_pos _)
      hδs_pos hδs_l4 hδs_eps hε₀_pos (hterm_ratio i hi)
  have hE_eq : ∀ i : ℕ, (E i) ^ l = Real.exp (-b * (((i : ℝ) - α * r) * h) ^ 2) := by
    intro i
    dsimp only [E, b]
    rw [hh_def, ← Real.exp_nat_mul]
    congr 1
    have hσ2 : α * (1 - α) = σ ^ 2 := by
      rw [hσ_def]
      exact (Real.sq_sqrt (mul_pos hp0 (sub_pos.mpr hp1)).le).symm
    rw [hσ2]
    have hne : σ ≠ 0 := hσ_pos.ne'
    have hrne : (r : ℝ) ≠ 0 := hr_pos.ne'
    have hsqne : Real.sqrt r ≠ 0 := hsqr_pos.ne'
    field_simp
    rw [Real.sq_sqrt hr_pos.le]
    ring
  let C : ℝ := Real.sqrt l / Real.sqrt (2 * Real.pi)
  have hC_pos : 0 < C := by positivity
  let R_sum : ℝ := h * ∑ i ∈ Finset.Icc a_lo a_hi, Real.exp (-b * (((i : ℝ) - α * r) * h) ^ 2)
  let I_val : ℝ := ∫ x in (-M)..M, Real.exp (-b * x ^ 2)
  have hRiem := gaussian_riemann_sum_close hb_pos hM_pos hh_pos hMh hx₀_ge
  have hRiem' : |C * R_sum - C * I_val| ≤ ε₀ / 8 := by
    have hmul : C * R_sum - C * I_val = C * (R_sum - I_val) := by ring
    rw [hmul, abs_mul, abs_of_pos hC_pos]
    have h6Ch : C * (6 * h) ≤ ε₀ / 8 := by
      have hstep : C * (6 * h) =
          6 * Real.sqrt l / (Real.sqrt (2 * Real.pi) * σ * Real.sqrt r) := by
        dsimp only [C]; rw [hh_def]; ring
      rw [hstep]
      have h1' : 48 * Real.sqrt l ≤ Real.sqrt r * (Real.sqrt (2 * Real.pi) * σ * ε₀) :=
        (div_le_iff₀ (by positivity)).mp h_err_h
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc 6 * Real.sqrt l * 8 = 48 * Real.sqrt l := by ring
        _ ≤ Real.sqrt r * (Real.sqrt (2 * Real.pi) * σ * ε₀) := h1'
        _ = ε₀ * (Real.sqrt (2 * Real.pi) * σ * Real.sqrt r) := by ring
    calc C * |R_sum - I_val| ≤ C * (6 * h) := by
          gcongr
          simpa only [R_sum, I_val, ha_lo_def, ha_hi_def] using hRiem
      _ ≤ ε₀ / 8 := h6Ch
  have hCR_close : |C * R_sum - 1| ≤ 3 * ε₀ / 8 := by
    calc |C * R_sum - 1|
        = |(C * R_sum - C * I_val) + (C * I_val - 1)| := by ring_nf
      _ ≤ |C * R_sum - C * I_val| + |C * I_val - 1| := abs_add_le _ _
      _ ≤ ε₀ / 8 + ε₀ / 4 := add_le_add hRiem' (by simpa only [C, I_val, b] using hM_bulk.le)
      _ = 3 * ε₀ / 8 := by ring
  have hCR_le2 : C * R_sum ≤ 2 := by
    linarith [(abs_le.mp hCR_close).2, hε₀_le1]
  have hB_eq : (∑ i ∈ Finset.Icc a_lo a_hi, binomP r α i ^ l) * (Real.sqrt l * W ^ (l - 1)) =
      C * (h * ∑ i ∈ Finset.Icc a_lo a_hi, (S i) ^ l) := by
    have hW_ne : W ≠ 0 := hW_pos.ne'
    have hh_ne : h ≠ 0 := hh_pos.ne'
    have hpi_ne : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    calc (∑ i ∈ Finset.Icc a_lo a_hi, binomP r α i ^ l) * (Real.sqrt l * W ^ (l - 1))
        = (∑ i ∈ Finset.Icc a_lo a_hi, (binomP r α i ^ l * W ^ l)) * (Real.sqrt l / W) := by
            have hWl : W ^ l = W ^ (l - 1) * W := by
              conv_lhs => rw [show l = (l - 1) + 1 by omega, pow_succ]
            rw [Finset.sum_mul, Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            have hWcancel : W * (Real.sqrt l / W) = Real.sqrt l := mul_div_cancel₀ _ hW_ne
            rw [hWl]
            calc binomP r α i ^ l * (Real.sqrt l * W ^ (l - 1))
                = binomP r α i ^ l * (W ^ (l - 1) * (W * (Real.sqrt l / W))) := by
                    rw [hWcancel]; ring
              _ = binomP r α i ^ l * (W ^ (l - 1) * W) * (Real.sqrt l / W) := by ring
      _ = C * (h * ∑ i ∈ Finset.Icc a_lo a_hi, (S i) ^ l) := by
            have hS_pow : ∀ i : ℕ, binomP r α i ^ l * W ^ l = (S i) ^ l := fun i => by
              dsimp only [S]; ring
            simp_rw [hS_pow]
            dsimp only [C]
            rw [hW_eq_h]
            field_simp
  have hB_R : |(∑ i ∈ Finset.Icc a_lo a_hi, binomP r α i ^ l) * (Real.sqrt l * W ^ (l - 1)) -
      C * R_sum| ≤ ε₀ / 8 := by
    rw [hB_eq, ← mul_sub, abs_mul, abs_of_pos hC_pos]
    have hsum_diff : |h * ∑ i ∈ Finset.Icc a_lo a_hi, (S i) ^ l - R_sum| ≤ (ε₀ / 16) * R_sum := by
      have h1 : h * ∑ i ∈ Finset.Icc a_lo a_hi, (S i) ^ l - R_sum =
          h * ∑ i ∈ Finset.Icc a_lo a_hi, ((S i) ^ l - (E i) ^ l) := by
        dsimp only [R_sum]
        simp_rw [← hE_eq, Finset.sum_sub_distrib]
        ring
      rw [h1, abs_mul, abs_of_pos hh_pos]
      have h2 : |∑ i ∈ Finset.Icc a_lo a_hi, ((S i) ^ l - (E i) ^ l)| ≤
          ∑ i ∈ Finset.Icc a_lo a_hi, |(S i) ^ l - (E i) ^ l| :=
        Finset.abs_sum_le_sum_abs _ _
      have h3 : ∑ i ∈ Finset.Icc a_lo a_hi, |(S i) ^ l - (E i) ^ l| ≤
          (ε₀ / 16) * ∑ i ∈ Finset.Icc a_lo a_hi, (E i) ^ l := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i hi => ?_
        have hEi : 0 < (E i) ^ l := pow_pos (Real.exp_pos _) l
        have hident : (S i) ^ l - (E i) ^ l = ((S i) ^ l / (E i) ^ l - 1) * (E i) ^ l := by
          field_simp [hEi.ne']
        rw [hident, abs_mul, abs_of_pos hEi]
        exact mul_le_mul_of_nonneg_right (hterm_pow i hi) hEi.le
      calc h * |∑ i ∈ Finset.Icc a_lo a_hi, ((S i) ^ l - (E i) ^ l)|
          ≤ h * ∑ i ∈ Finset.Icc a_lo a_hi, |(S i) ^ l - (E i) ^ l| :=
            mul_le_mul_of_nonneg_left h2 hh_pos.le
        _ ≤ h * ((ε₀ / 16) * ∑ i ∈ Finset.Icc a_lo a_hi, (E i) ^ l) :=
            mul_le_mul_of_nonneg_left h3 hh_pos.le
        _ = (ε₀ / 16) * R_sum := by
            dsimp only [R_sum]
            simp_rw [← hE_eq]
            ring
    calc C * |h * ∑ i ∈ Finset.Icc a_lo a_hi, (S i) ^ l - R_sum|
        ≤ C * ((ε₀ / 16) * R_sum) := mul_le_mul_of_nonneg_left hsum_diff hC_pos.le
      _ = (ε₀ / 16) * (C * R_sum) := by ring
      _ ≤ (ε₀ / 16) * 2 := mul_le_mul_of_nonneg_left hCR_le2 (by positivity)
      _ = ε₀ / 8 := by ring
  calc |(∑ i ∈ Finset.Icc a_lo a_hi, binomP r α i ^ l) * (Real.sqrt l * W ^ (l - 1)) - 1|
      = |((∑ i ∈ Finset.Icc a_lo a_hi, binomP r α i ^ l) * (Real.sqrt l * W ^ (l - 1)) -
          C * R_sum) + (C * R_sum - 1)| := by ring_nf
    _ ≤ |(∑ i ∈ Finset.Icc a_lo a_hi, binomP r α i ^ l) * (Real.sqrt l * W ^ (l - 1)) -
          C * R_sum| + |C * R_sum - 1| := abs_add_le _ _
    _ ≤ ε₀ / 8 + 3 * ε₀ / 8 := add_le_add hB_R hCR_close
    _ = ε₀ / 2 := by ring

private lemma normDen_tails_small {l r a_lo a_hi : ℕ} {α σ M h δs ε₀ : ℝ}
    (hl2 : 2 ≤ l) (hp0 : 0 < α) (hp1 : α < 1) (hσ_pos : 0 < σ) (hh_pos : 0 < h)
    (hMh : 2 * h ≤ M) (hM_ge3 : 3 ≤ M)
    (hx₀_ge : M / h + 1 ≤ α * r) (hMh_eq : M / h = M * σ * Real.sqrt r)
    (hσ_def : σ = Real.sqrt (α * (1 - α))) (h1_le_σr : 1 ≤ σ * Real.sqrt r)
    (hr_pos : (0 : ℝ) < r) (hδs_pos : 0 < δs) (hδs_l4 : (l : ℝ) * δs ≤ 1 / 4)
    (ha_lo_def : a_lo = ⌈α * r - M / h⌉₊) (ha_hi_def : a_hi = ⌊α * r + M / h⌋₊)
    (ha_lo_le_hi : a_lo ≤ a_hi) (ha_hi_lt_r : a_hi < r)
    (hM_tail : 2 * Real.sqrt l * Real.exp (-((l - 1 : ℕ) : ℝ) * (M - 1) ^ 2 / 2) < ε₀ / 8)
    (hterm_ratio : ∀ i ∈ Finset.Icc a_lo a_hi,
        |(Real.sqrt (2 * Real.pi * r) * σ * binomP r α i) /
          Real.exp (-((i : ℝ) - α * r) ^ 2 / (2 * r * (α * (1 - α)))) - 1| ≤ δs) :
    (∑ i ∈ Finset.range a_lo, binomP r α i ^ l) *
        (Real.sqrt l * (Real.sqrt (2 * Real.pi * r) * σ) ^ (l - 1)) ≤ ε₀ / 8 ∧
      (∑ i ∈ Finset.Ioc a_hi r, binomP r α i ^ l) *
        (Real.sqrt l * (Real.sqrt (2 * Real.pi * r) * σ) ^ (l - 1)) ≤ ε₀ / 8 := by
  have hl_pos : (0 : ℝ) < l := by positivity
  have hsqrt_l_pos : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl_pos
  let W : ℝ := Real.sqrt (2 * Real.pi * r) * σ
  have hW_pos : 0 < W := by positivity
  let S : ℕ → ℝ := fun i => W * binomP r α i
  let E : ℕ → ℝ := fun i => Real.exp (-((i : ℝ) - α * r) ^ 2 / (2 * r * (α * (1 - α))))
  have hM1_nn : 0 ≤ M - 1 := by linarith
  have hM2_div : 2 ≤ M / h := (le_div_iff₀ hh_pos).mpr hMh
  have hpow_ub_l : (1 + δs) ^ l ≤ 2 := by
    have hlδ_nn : 0 ≤ (l : ℝ) * δs := mul_nonneg (Nat.cast_nonneg l) hδs_pos.le
    have hexp1 : 1 + δs ≤ Real.exp δs := by linarith [Real.add_one_le_exp δs]
    have hexp2 : (1 + δs) ^ l ≤ Real.exp ((l : ℝ) * δs) := by
      calc (1 + δs) ^ l ≤ (Real.exp δs) ^ l := pow_le_pow_left₀ (by positivity) hexp1 l
        _ = Real.exp ((l : ℝ) * δs) := by rw [← Real.exp_nat_mul]
    have hexp3 : |Real.exp ((l : ℝ) * δs) - 1| ≤ 2 * ((l : ℝ) * δs) := by
      have habs := abs_exp_sub_one_le_two_mul (by rw [abs_of_nonneg hlδ_nn]; linarith [hδs_l4])
      rwa [abs_of_nonneg hlδ_nn] at habs
    linarith [(abs_le.mp hexp3).2, hδs_l4]
  have ha_lo_dist : (M - 1) * σ * Real.sqrt r ≤ |((a_lo : ℝ) - α * r)| := by
    have ha_lo_le : (a_lo : ℝ) < α * r - M / h + 1 := by
      rw [ha_lo_def]
      exact Nat.ceil_lt_add_one (by linarith [hx₀_ge])
    have h1' : α * r - (a_lo : ℝ) ≥ M * σ * Real.sqrt r - 1 := by rw [← hMh_eq]; linarith
    have h2' : α * r - (a_lo : ℝ) ≤ |((a_lo : ℝ) - α * r)| := by
      calc α * r - (a_lo : ℝ) = -((a_lo : ℝ) - α * r) := by ring
        _ ≤ |((a_lo : ℝ) - α * r)| := neg_le_abs _
    have hsub : (M - 1) * σ * Real.sqrt r = M * σ * Real.sqrt r - σ * Real.sqrt r := by ring
    linarith [h1_le_σr]
  have ha_hi_dist : (M - 1) * σ * Real.sqrt r ≤ |((a_hi : ℝ) - α * r)| := by
    have ha_hi_gt : α * r + M / h - 1 < (a_hi : ℝ) := by
      rw [ha_hi_def]
      linarith [Nat.lt_floor_add_one (α * r + M / h)]
    have h1' : (a_hi : ℝ) - α * r ≥ M * σ * Real.sqrt r - 1 := by rw [← hMh_eq]; linarith
    have h2' : (a_hi : ℝ) - α * r ≤ |((a_hi : ℝ) - α * r)| := le_abs_self _
    have hsub : (M - 1) * σ * Real.sqrt r = M * σ * Real.sqrt r - σ * Real.sqrt r := by ring
    linarith [h1_le_σr]
  have ha_lo_r : a_lo ≤ r := le_trans ha_lo_le_hi ha_hi_lt_r.le
  have ha_lo_mode : (a_lo : ℝ) ≤ (r + 1 : ℝ) * α := by
    have hlo : (a_lo : ℝ) < α * r - M / h + 1 := by
      rw [ha_lo_def]
      exact Nat.ceil_lt_add_one (by linarith [hx₀_ge])
    have hrα : (r + 1 : ℝ) * α = α * r + α := by ring
    linarith [hlo, hM2_div, hp0, hrα]
  have ha_hi_mode : (r + 1 : ℝ) * α ≤ (a_hi : ℝ) + 1 := by
    have hhi : α * r + M / h < (a_hi : ℝ) + 1 := by
      rw [ha_hi_def]
      exact Nat.lt_floor_add_one _
    have hrα : (r + 1 : ℝ) * α = α * r + α := by ring
    linarith [hhi, hM2_div, hp1, hrα]
  have hE_tail_bound : ∀ k : ℕ, (M - 1) * σ * Real.sqrt r ≤ |(k : ℝ) - α * r| →
      E k ≤ Real.exp (-(M - 1) ^ 2 / 2) := by
    intro k hk
    dsimp only [E]
    apply Real.exp_le_exp.mpr
    have hden_pos : 0 < 2 * (r : ℝ) * (α * (1 - α)) := by
      have : 0 < 1 - α := sub_pos.mpr hp1
      positivity
    have hσ2 : α * (1 - α) = σ ^ 2 := by
      rw [hσ_def]
      exact (Real.sq_sqrt (mul_pos hp0 (sub_pos.mpr hp1)).le).symm
    have hden_pos' : 0 < 2 * (r : ℝ) * σ ^ 2 := by positivity
    rw [hσ2, div_le_div_iff₀ hden_pos' (by norm_num)]
    have hsq : ((M - 1) * σ * Real.sqrt r) ^ 2 ≤ |(k : ℝ) - α * r| ^ 2 :=
      pow_le_pow_left₀ (by positivity) hk 2
    rw [sq_abs] at hsq
    have hval : ((M - 1) * σ * Real.sqrt r) ^ 2 = (M - 1) ^ 2 * σ ^ 2 * r := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hr_pos.le]
    have hmul2 : (M - 1) ^ 2 * (2 * (r : ℝ) * σ ^ 2) = 2 * ((M - 1) ^ 2 * σ ^ 2 * r) := by ring
    linarith [hval, hsq, hmul2]
  have hS_pow_bound : ∀ k ∈ Finset.Icc a_lo a_hi,
      (M - 1) * σ * Real.sqrt r ≤ |(k : ℝ) - α * r| →
      Real.sqrt l * (S k) ^ (l - 1) ≤ ε₀ / 8 := by
    intro k hk hdist
    have hSk_le : S k ≤ (1 + δs) * E k := by
      have hEi : 0 < E k := Real.exp_pos _
      have hst := (abs_le.mp (hterm_ratio k hk)).2
      have h1 : S k / E k ≤ 1 + δs := by linarith
      exact (div_le_iff₀ hEi).mp h1
    have h1d_pow : (1 + δs) ^ (l - 1) ≤ 2 :=
      (pow_le_pow_right₀ (by linarith [hδs_pos]) (Nat.sub_le l 1)).trans hpow_ub_l
    have hEk_pow : (E k) ^ (l - 1) ≤ Real.exp (-((l - 1 : ℕ) : ℝ) * (M - 1) ^ 2 / 2) := by
      calc (E k) ^ (l - 1)
          ≤ (Real.exp (-(M - 1) ^ 2 / 2)) ^ (l - 1) :=
            pow_le_pow_left₀ (Real.exp_pos _).le (hE_tail_bound k hdist) (l - 1)
        _ = Real.exp (((l - 1 : ℕ) : ℝ) * (-(M - 1) ^ 2 / 2)) := by rw [← Real.exp_nat_mul]
        _ = Real.exp (-((l - 1 : ℕ) : ℝ) * (M - 1) ^ 2 / 2) := by ring_nf
    have hSk_pow : (S k) ^ (l - 1) ≤
        2 * Real.exp (-((l - 1 : ℕ) : ℝ) * (M - 1) ^ 2 / 2) := by
      calc (S k) ^ (l - 1)
          ≤ ((1 + δs) * E k) ^ (l - 1) :=
            pow_le_pow_left₀ (mul_nonneg hW_pos.le (binomP_nonneg hp0.le hp1.le k)) hSk_le _
        _ = (1 + δs) ^ (l - 1) * (E k) ^ (l - 1) := mul_pow _ _ _
        _ ≤ 2 * Real.exp (-((l - 1 : ℕ) : ℝ) * (M - 1) ^ 2 / 2) :=
            mul_le_mul h1d_pow hEk_pow (pow_nonneg (Real.exp_pos _).le _) (by norm_num)
    calc Real.sqrt l * (S k) ^ (l - 1)
        ≤ Real.sqrt l * (2 * Real.exp (-((l - 1 : ℕ) : ℝ) * (M - 1) ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left hSk_pow hsqrt_l_pos.le
      _ = 2 * Real.sqrt l * Real.exp (-((l - 1 : ℕ) : ℝ) * (M - 1) ^ 2 / 2) := by ring
      _ ≤ ε₀ / 8 := hM_tail.le
  constructor
  · have hsum_le : ∑ i ∈ Finset.range a_lo, binomP r α i ^ l ≤ (binomP r α a_lo) ^ (l - 1) := by
      have h1 : ∑ i ∈ Finset.range a_lo, binomP r α i ^ l ≤
          ∑ i ∈ Finset.range a_lo, (binomP r α a_lo) ^ (l - 1) * binomP r α i := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hia : i ≤ a_lo := (Finset.mem_range.mp hi).le
        have hbi : binomP r α i ≤ binomP r α a_lo :=
          binomP_mono_left hp0 hp1 hia ha_lo_r ha_lo_mode
        have hl1 : l = (l - 1) + 1 := by omega
        conv_lhs => rw [hl1, pow_succ]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (binomP_nonneg hp0.le hp1.le i) hbi (l - 1))
          (binomP_nonneg hp0.le hp1.le i)
      have h2 : ∑ i ∈ Finset.range a_lo, binomP r α i ≤ 1 := by
        calc ∑ i ∈ Finset.range a_lo, binomP r α i
            ≤ ∑ i ∈ Finset.range (r + 1), binomP r α i :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.range_mono (by omega))
                (fun _ _ _ => binomP_nonneg hp0.le hp1.le _)
          _ = 1 := binomP_sum_eq_one r α
      calc ∑ i ∈ Finset.range a_lo, binomP r α i ^ l
          ≤ ∑ i ∈ Finset.range a_lo, (binomP r α a_lo) ^ (l - 1) * binomP r α i := h1
        _ = (binomP r α a_lo) ^ (l - 1) * ∑ i ∈ Finset.range a_lo, binomP r α i := by
            rw [Finset.mul_sum]
        _ ≤ (binomP r α a_lo) ^ (l - 1) * 1 :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg (binomP_nonneg hp0.le hp1.le a_lo) _)
        _ = (binomP r α a_lo) ^ (l - 1) := mul_one _
    calc (∑ i ∈ Finset.range a_lo, binomP r α i ^ l) * (Real.sqrt l * W ^ (l - 1))
        ≤ (binomP r α a_lo) ^ (l - 1) * (Real.sqrt l * W ^ (l - 1)) :=
          mul_le_mul_of_nonneg_right hsum_le (by positivity)
      _ = Real.sqrt l * (S a_lo) ^ (l - 1) := by dsimp only [S]; rw [mul_pow]; ring
      _ ≤ ε₀ / 8 :=
          hS_pow_bound a_lo (Finset.mem_Icc.mpr ⟨le_rfl, ha_lo_le_hi⟩) ha_lo_dist
  · have hsum_le : ∑ i ∈ Finset.Ioc a_hi r, binomP r α i ^ l ≤ (binomP r α a_hi) ^ (l - 1) := by
      have h1 : ∑ i ∈ Finset.Ioc a_hi r, binomP r α i ^ l ≤
          ∑ i ∈ Finset.Ioc a_hi r, (binomP r α a_hi) ^ (l - 1) * binomP r α i := by
        refine Finset.sum_le_sum fun i hi => ?_
        obtain ⟨hai, hir⟩ := Finset.mem_Ioc.mp hi
        have hbi : binomP r α i ≤ binomP r α a_hi :=
          binomP_anti_right hp0 hp1 hai.le hir ha_hi_mode
        have hl1 : l = (l - 1) + 1 := by omega
        conv_lhs => rw [hl1, pow_succ]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (binomP_nonneg hp0.le hp1.le i) hbi (l - 1))
          (binomP_nonneg hp0.le hp1.le i)
      have h2 : ∑ i ∈ Finset.Ioc a_hi r, binomP r α i ≤ 1 := by
        calc ∑ i ∈ Finset.Ioc a_hi r, binomP r α i
            ≤ ∑ i ∈ Finset.range (r + 1), binomP r α i :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (fun i hi => Finset.mem_range.mpr (by
                  have := (Finset.mem_Ioc.mp hi).2; omega))
                (fun _ _ _ => binomP_nonneg hp0.le hp1.le _)
          _ = 1 := binomP_sum_eq_one r α
      calc ∑ i ∈ Finset.Ioc a_hi r, binomP r α i ^ l
          ≤ ∑ i ∈ Finset.Ioc a_hi r, (binomP r α a_hi) ^ (l - 1) * binomP r α i := h1
        _ = (binomP r α a_hi) ^ (l - 1) * ∑ i ∈ Finset.Ioc a_hi r, binomP r α i := by
            rw [Finset.mul_sum]
        _ ≤ (binomP r α a_hi) ^ (l - 1) * 1 :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg (binomP_nonneg hp0.le hp1.le a_hi) _)
        _ = (binomP r α a_hi) ^ (l - 1) := mul_one _
    calc (∑ i ∈ Finset.Ioc a_hi r, binomP r α i ^ l) * (Real.sqrt l * W ^ (l - 1))
        ≤ (binomP r α a_hi) ^ (l - 1) * (Real.sqrt l * W ^ (l - 1)) :=
          mul_le_mul_of_nonneg_right hsum_le (by positivity)
      _ = Real.sqrt l * (S a_hi) ^ (l - 1) := by dsimp only [S]; rw [mul_pow]; ring
      _ ≤ ε₀ / 8 :=
          hS_pow_bound a_hi (Finset.mem_Icc.mpr ⟨ha_lo_le_hi, le_rfl⟩) ha_hi_dist

private lemma tendsto_normDen {l : ℕ} {a : ℝ} (hl : 0 < l) (ha : 0 < a) :
    Tendsto (fun r : ℕ => normDen l a r *
        (Real.sqrt l * (Real.sqrt (2 * Real.pi * r * (paramP a * paramQ a))) ^ (l - 1)))
      atTop (𝓝 1) := by
  rcases Nat.eq_or_lt_of_le hl with rfl | hl2
  · simp only [Nat.cast_one, Real.sqrt_one, Nat.sub_self, pow_zero, mul_one,
      normDen_eq_one_of_one]
    exact tendsto_const_nhds
  · have hp0 := paramP_pos ha
    have hp1 := paramP_lt_one ha
    have hq_eq : 1 - paramP a = paramQ a := one_sub_paramP ha
    let α := paramP a
    let σ := Real.sqrt (α * (1 - α))
    have hσ_pos : 0 < σ := Real.sqrt_pos.mpr (mul_pos hp0 (sub_pos.mpr hp1))
    let b : ℝ := (l : ℝ) / 2
    have hb_pos : 0 < b := by positivity
    have hint : Integrable (fun x : ℝ => Real.exp (-b * x ^ 2)) volume :=
      integrable_exp_neg_mul_sq hb_pos
    have hI_lim : Tendsto (fun M : ℝ => ∫ x in (-M)..M, Real.exp (-b * x ^ 2)) atTop
        (𝓝 (∫ x : ℝ, Real.exp (-b * x ^ 2))) :=
      intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
    have hI_val : ∫ x : ℝ, Real.exp (-b * x ^ 2) = Real.sqrt (Real.pi / b) :=
      integral_gaussian b
    have h_const_lim :
        Tendsto (fun M : ℝ =>
            (Real.sqrt l / Real.sqrt (2 * Real.pi)) * ∫ x in (-M)..M, Real.exp (-b * x ^ 2))
          atTop (𝓝 1) := by
      have hprod1 : (Real.sqrt l / Real.sqrt (2 * Real.pi)) * Real.sqrt (Real.pi / b) = 1 := by
        have hb_eq : Real.pi / b = 2 * Real.pi / l := by dsimp only [b]; field_simp
        rw [hb_eq, Real.sqrt_div (by positivity)]
        field_simp
      rw [← hprod1]
      exact tendsto_const_nhds.mul (hI_lim.trans (by rw [hI_val]))
    rw [Metric.tendsto_atTop]
    intro ε hε
    let ε₀ : ℝ := min ε 1
    have hε₀_pos : 0 < ε₀ := lt_min hε zero_lt_one
    have hε₀_le1 : ε₀ ≤ 1 := min_le_right _ _
    have hε₀_leε : ε₀ ≤ ε := min_le_left _ _
    obtain ⟨M₀, hM₀⟩ := Metric.tendsto_atTop.mp h_const_lim (ε₀ / 4) (by positivity)
    have htail_lim :
        Tendsto (fun M : ℝ => 2 * Real.sqrt l * Real.exp (-((l - 1 : ℕ) : ℝ) * (M - 1) ^ 2 / 2))
          atTop (𝓝 0) := by
      have hm1 : Tendsto (fun M : ℝ => M - 1) atTop atTop :=
        tendsto_atTop_add_const_right _ (-1) tendsto_id
      have hm_pos : (0 : ℝ) < ((l - 1 : ℕ) : ℝ) / 2 := by
        have : (1 : ℝ) ≤ ((l - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ l - 1)
        linarith
      have hsq : Tendsto (fun M : ℝ => (((l - 1 : ℕ) : ℝ) / 2) * (M - 1) ^ 2) atTop atTop :=
        Tendsto.const_mul_atTop hm_pos ((tendsto_pow_atTop (by norm_num)).comp hm1)
      have hexp_lim :
          Tendsto (fun M : ℝ => Real.exp (-((((l - 1 : ℕ) : ℝ) / 2) * (M - 1) ^ 2)))
            atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp hsq
      have hmul := tendsto_const_nhds (x := 2 * Real.sqrt l).mul hexp_lim
      simp only [mul_zero] at hmul
      refine hmul.congr fun M => ?_
      ring_nf
    obtain ⟨M₁, hM₁⟩ := Metric.tendsto_atTop.mp htail_lim (ε₀ / 8) (by positivity)
    let M : ℝ := max (max M₀ M₁) 3
    have hM_ge3 : 3 ≤ M := le_max_right _ _
    have hM_pos : 0 < M := by linarith
    have hM_bulk : |(Real.sqrt l / Real.sqrt (2 * Real.pi)) *
        (∫ x in (-M)..M, Real.exp (-b * x ^ 2)) - 1| < ε₀ / 4 := by
      rw [← Real.dist_eq]
      exact hM₀ M (le_trans (le_max_left _ _) (le_max_left _ _))
    have hM_tail : 2 * Real.sqrt l * Real.exp (-((l - 1 : ℕ) : ℝ) * (M - 1) ^ 2 / 2) < ε₀ / 8 := by
      have h := hM₁ M (le_trans (le_max_right _ _) (le_max_left _ _))
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at h
      exact h
    let δs : ℝ := min (ε₀ / (32 * l)) (1 / (4 * l))
    have hδs_pos : 0 < δs := by positivity
    obtain ⟨N₁, hN₁⟩ := binom_stirling_unif hp0 hp1 (M := M + 1) (ε := δs) (by positivity) hδs_pos
    have hsq_tendsto : Tendsto (fun r : ℕ => Real.sqrt (r : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    let B_r : ℝ := max (max (2 / (M * σ)) ((M + 2) / min α (1 - α)))
      (max (48 * Real.sqrt l / (Real.sqrt (2 * Real.pi) * σ * ε₀)) (1 / σ))
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hsq_tendsto.eventually_ge_atTop B_r)
    refine ⟨max N₁ (max N₂ 16), fun r hr => ?_⟩
    have hrN1 : N₁ ≤ r := (le_max_left _ _).trans hr
    have hrN2 : N₂ ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans hr)
    have hr16 : 16 ≤ r := (le_max_right _ _).trans ((le_max_right _ _).trans hr)
    have hr_pos : (0 : ℝ) < r := by positivity
    have hsqr_pos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr_pos
    have hBr : B_r ≤ Real.sqrt r := hN₂ r hrN2
    have h_step_h : 2 / (M * σ) ≤ Real.sqrt r :=
      (le_max_left _ _).trans ((le_max_left _ _).trans hBr)
    have h_x0_ge : (M + 2) / min α (1 - α) ≤ Real.sqrt r :=
      (le_max_right _ _).trans ((le_max_left _ _).trans hBr)
    have h_err_h : 48 * Real.sqrt l / (Real.sqrt (2 * Real.pi) * σ * ε₀) ≤ Real.sqrt r :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hBr)
    have h_sig_r : 1 / σ ≤ Real.sqrt r :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hBr)
    have h1_le_σr : 1 ≤ σ * Real.sqrt r := by
      have h1' : 1 ≤ Real.sqrt r * σ := (div_le_iff₀ hσ_pos).mp h_sig_r
      linarith
    let h : ℝ := 1 / (σ * Real.sqrt r)
    have hh_pos : 0 < h := by positivity
    have hMh_eq : M / h = M * σ * Real.sqrt r := by dsimp only [h]; field_simp
    have hMh : 2 * h ≤ M := by
      have h2' : 2 ≤ Real.sqrt r * (M * σ) := (div_le_iff₀ (mul_pos hM_pos hσ_pos)).mp h_step_h
      have h2'' : 2 / M ≤ σ * Real.sqrt r := (div_le_iff₀ hM_pos).mpr (by linarith)
      dsimp only [h]
      rw [mul_one_div]
      exact (div_le_iff₀ (mul_pos hσ_pos hsqr_pos)).mpr (by
        calc 2 = (2 / M) * M := by field_simp
          _ ≤ (σ * Real.sqrt r) * M := mul_le_mul_of_nonneg_right h2'' hM_pos.le
          _ = M * (σ * Real.sqrt r) := by ring)
    have hσ_le1 : σ ≤ 1 := by
      dsimp only [σ]
      calc Real.sqrt (α * (1 - α)) ≤ Real.sqrt 1 :=
            Real.sqrt_le_sqrt (mul_le_one₀ hp1.le (by linarith) (by linarith))
        _ = 1 := Real.sqrt_one
    have h4_le_sqr : 4 ≤ Real.sqrt r := by
      calc (4 : ℝ) = Real.sqrt 16 := by norm_num
        _ ≤ Real.sqrt r := Real.sqrt_le_sqrt (by exact_mod_cast hr16)
    have hm1 : M + 2 ≤ Real.sqrt r * min α (1 - α) :=
      (div_le_iff₀ (lt_min hp0 (sub_pos.mpr hp1))).mp h_x0_ge
    have hx₀_ge : M / h + 1 ≤ α * r := by
      have hm2 : (M + 2) * Real.sqrt r ≤ α * r := by
        calc (M + 2) * Real.sqrt r ≤ (Real.sqrt r * min α (1 - α)) * Real.sqrt r :=
              mul_le_mul_of_nonneg_right hm1 hsqr_pos.le
          _ = min α (1 - α) * (Real.sqrt r * Real.sqrt r) := by ring
          _ = min α (1 - α) * r := by rw [Real.mul_self_sqrt hr_pos.le]
          _ ≤ α * r := mul_le_mul_of_nonneg_right (min_le_left _ _) hr_pos.le
      have hms : M * σ * Real.sqrt r ≤ M * Real.sqrt r := by
        calc M * σ * Real.sqrt r = M * Real.sqrt r * σ := by ring
          _ ≤ M * Real.sqrt r * 1 := mul_le_mul_of_nonneg_left hσ_le1 (by positivity)
          _ = M * Real.sqrt r := mul_one _
      have h1_le : M * σ * Real.sqrt r + 1 ≤ (M + 2) * Real.sqrt r := by
        linarith [hms, h4_le_sqr]
      rw [hMh_eq]
      linarith [h1_le, hm2]
    have h_hi_lt_r : α * r + M / h ≤ r - 1 := by
      have hm2 : (M + 2) * Real.sqrt r ≤ (1 - α) * r := by
        calc (M + 2) * Real.sqrt r ≤ (Real.sqrt r * min α (1 - α)) * Real.sqrt r :=
              mul_le_mul_of_nonneg_right hm1 hsqr_pos.le
          _ = min α (1 - α) * (Real.sqrt r * Real.sqrt r) := by ring
          _ = min α (1 - α) * r := by rw [Real.mul_self_sqrt hr_pos.le]
          _ ≤ (1 - α) * r := mul_le_mul_of_nonneg_right (min_le_right _ _) hr_pos.le
      have hms : M * σ * Real.sqrt r ≤ M * Real.sqrt r := by
        calc M * σ * Real.sqrt r = M * Real.sqrt r * σ := by ring
          _ ≤ M * Real.sqrt r * 1 := mul_le_mul_of_nonneg_left hσ_le1 (by positivity)
          _ = M * Real.sqrt r := mul_one _
      have h1_le : M * σ * Real.sqrt r + 1 ≤ (M + 2) * Real.sqrt r := by
        linarith [hms, h4_le_sqr]
      rw [hMh_eq]
      linarith [h1_le, hm2]
    let a_lo : ℕ := ⌈α * r - M / h⌉₊
    let a_hi : ℕ := ⌊α * r + M / h⌋₊
    have ha_hi_lt_r : a_hi < r := by
      have h1 : (a_hi : ℝ) ≤ α * r + M / h := Nat.floor_le (by positivity)
      have h2 : (a_hi : ℝ) < r := by linarith
      exact_mod_cast h2
    have hM2_div : 2 ≤ M / h := (le_div_iff₀ hh_pos).mpr hMh
    have ha_lo_le_hi : a_lo ≤ a_hi := by
      have hlo : (a_lo : ℝ) < α * r - M / h + 1 := Nat.ceil_lt_add_one (by linarith)
      have hhi : α * r + M / h < (a_hi : ℝ) + 1 := Nat.lt_floor_add_one _
      have : (a_lo : ℝ) < (a_hi : ℝ) := by linarith
      exact_mod_cast this.le
    have hIcc_dist : ∀ i ∈ Finset.Icc a_lo a_hi, |(i : ℝ) - α * r| ≤ (M + 1) * σ * Real.sqrt r := by
      intro i hi
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hi
      have h1r : (a_lo : ℝ) ≤ i := by exact_mod_cast h1
      have h2r : (i : ℝ) ≤ a_hi := by exact_mod_cast h2
      have h1' : α * r - M / h ≤ i := (Nat.le_ceil _).trans h1r
      have h2' : (i : ℝ) ≤ α * r + M / h := h2r.trans (Nat.floor_le (by positivity))
      have hσr_le : M * σ * Real.sqrt r ≤ (M + 1) * σ * Real.sqrt r := by
        have hnn : 0 ≤ σ * Real.sqrt r := mul_nonneg hσ_pos.le hsqr_pos.le
        linarith
      rw [hMh_eq] at h1' h2'
      rw [abs_le]
      constructor <;> linarith
    have hScale_eq :
        Real.sqrt l * (Real.sqrt (2 * Real.pi * r * (paramP a * paramQ a))) ^ (l - 1) =
          Real.sqrt l * (Real.sqrt (2 * Real.pi * r) * σ) ^ (l - 1) := by
      have hs : Real.sqrt (2 * Real.pi * r * (paramP a * paramQ a)) =
          Real.sqrt (2 * Real.pi * r) * σ := by
        dsimp only [σ, α]
        rw [hq_eq, Real.sqrt_mul (by positivity)]
      rw [hs]
    rw [hScale_eq]
    let W : ℝ := Real.sqrt (2 * Real.pi * r) * σ
    have hsplit_den : normDen l a r =
        (∑ i ∈ Finset.Icc a_lo a_hi, binomP r α i ^ l) +
          (∑ i ∈ Finset.range a_lo, binomP r α i ^ l) +
          (∑ i ∈ Finset.Ioc a_hi r, binomP r α i ^ l) := by
      have h1 : Finset.range (r + 1) =
          Finset.range a_lo ∪ (Finset.Icc a_lo a_hi ∪ Finset.Ioc a_hi r) := by
        ext i; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc, Finset.mem_Ioc]
        omega
      have hd1 : Disjoint (Finset.range a_lo) (Finset.Icc a_lo a_hi ∪ Finset.Ioc a_hi r) :=
        Finset.disjoint_left.mpr fun i h1 h2 => by
          simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
          omega
      have hd2 : Disjoint (Finset.Icc a_lo a_hi) (Finset.Ioc a_hi r) :=
        Finset.disjoint_left.mpr fun i h1 h2 => by
          simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
          omega
      unfold normDen
      dsimp only [α]
      rw [h1, Finset.sum_union hd1, Finset.sum_union hd2]
      ring
    have hterm_ratio : ∀ i ∈ Finset.Icc a_lo a_hi,
        |(W * binomP r α i) / Real.exp (-((i : ℝ) - α * r) ^ 2 / (2 * r * (α * (1 - α)))) - 1| ≤
          δs := by
      intro i hi
      have hst := hN₁ r hrN1 i (hIcc_dist i hi)
      have hWeq : W = Real.sqrt (2 * Real.pi * r) * Real.sqrt (α * (1 - α)) := rfl
      simpa only [hWeq, σ] using hst.2.2
    have hδs_l4 : (l : ℝ) * δs ≤ 1 / 4 := by
      have h1 : δs ≤ 1 / (4 * l) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at h1
      linarith
    have hδs_eps : (l : ℝ) * δs ≤ ε₀ / 32 := by
      have h1 : δs ≤ ε₀ / (32 * l) := min_le_left _ _
      rw [le_div_iff₀ (by positivity)] at h1
      linarith
    have hbulk_close := normDen_bulk_close hl2 hp0 hp1 hσ_pos hM_pos hh_pos hMh hx₀_ge rfl rfl
      hr_pos hδs_pos hδs_l4 hδs_eps hε₀_pos hε₀_le1 rfl rfl h_err_h hM_bulk hterm_ratio
    obtain ⟨hL_tail, hU_tail⟩ := normDen_tails_small hl2 hp0 hp1 hσ_pos hh_pos hMh hM_ge3 hx₀_ge hMh_eq
      rfl h1_le_σr hr_pos hδs_pos hδs_l4 rfl rfl ha_lo_le_hi ha_hi_lt_r hM_tail hterm_ratio
    have hL_nn : 0 ≤ (∑ i ∈ Finset.range a_lo, binomP r α i ^ l) * (Real.sqrt l * W ^ (l - 1)) :=
      mul_nonneg (Finset.sum_nonneg fun _ _ => pow_nonneg (binomP_nonneg hp0.le hp1.le _) l)
        (by positivity)
    have hU_nn : 0 ≤ (∑ i ∈ Finset.Ioc a_hi r, binomP r α i ^ l) * (Real.sqrt l * W ^ (l - 1)) :=
      mul_nonneg (Finset.sum_nonneg fun _ _ => pow_nonneg (binomP_nonneg hp0.le hp1.le _) l)
        (by positivity)
    rw [Real.dist_eq, hsplit_den, add_mul, add_mul]
    have htot :
        |(∑ i ∈ Finset.Icc a_lo a_hi, binomP r α i ^ l) * (Real.sqrt l * W ^ (l - 1)) +
          (∑ i ∈ Finset.range a_lo, binomP r α i ^ l) * (Real.sqrt l * W ^ (l - 1)) +
          (∑ i ∈ Finset.Ioc a_hi r, binomP r α i ^ l) * (Real.sqrt l * W ^ (l - 1)) - 1| ≤
          3 * ε₀ / 4 := by
      rw [abs_le]
      have hb_le := abs_le.mp hbulk_close
      constructor <;> linarith
    exact lt_of_le_of_lt htot (by linarith [hε₀_pos, hε₀_leε])

private lemma binomP_lower_tail {α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ m i : ℕ, (i : ℝ) ≤ (α - δ) * m → binomP m α i ≤ ρ ^ m := by
  let φ : ℝ → ℝ := fun t => (1 - α + α * Real.exp (-t)) * Real.exp ((α - δ) * t)
  have hφ0 : φ 0 = 1 := by simp [φ]
  have hderiv1 : HasDerivAt (fun t : ℝ => 1 - α + α * Real.exp (-t)) (-α) 0 := by
    have h1 := ((hasDerivAt_neg (0 : ℝ)).exp.const_mul α).const_add (1 - α)
    simpa using h1
  have hderiv2 : HasDerivAt (fun t : ℝ => Real.exp ((α - δ) * t)) (α - δ) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).const_mul (α - δ)).exp
    simpa using h1
  have hderiv : HasDerivAt φ (-δ) 0 := by
    have hmul : HasDerivAt φ ((-α) * Real.exp ((α - δ) * 0) +
        (1 - α + α * Real.exp (-0)) * (α - δ)) 0 := hderiv1.mul hderiv2
    rw [mul_zero, Real.exp_zero, neg_zero, Real.exp_zero] at hmul
    convert hmul using 1
    ring
  have htend : Tendsto (fun t : ℝ => ‖t - 0‖⁻¹ * ‖φ t - φ 0 - (t - 0) • (-δ)‖) (𝓝 0) (𝓝 0) :=
    hasDerivAt_iff_tendsto.mp hderiv
  obtain ⟨r, hr_pos, hr⟩ := Metric.tendsto_nhds_nhds.mp htend (δ / 2) (by positivity)
  let t : ℝ := min (r / 2) 1
  have ht_pos : 0 < t := by positivity
  have ht_lt : dist t 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hval := hr ht_lt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hval
  simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, abs_of_pos ht_pos] at hval
  have hbound : |φ t - 1 + t * δ| < t * (δ / 2) := by
    have h2 : t * (t⁻¹ * |φ t - 1 + t * δ|) < t * (δ / 2) :=
      mul_lt_mul_of_pos_left (by
        simpa [hφ0, sub_neg_eq_add, mul_comm t (-δ), mul_neg, sub_eq_add_neg, add_assoc,
          mul_comm t δ] using hval) ht_pos
    rwa [← mul_assoc, mul_inv_cancel₀ ht_pos.ne', one_mul] at h2
  have hφt_lt1 : φ t < 1 := by
    have := (abs_lt.mp hbound).2
    linarith [mul_pos ht_pos hδ]
  have hφt_pos : 0 < φ t := by
    dsimp only [φ]
    have : 0 < 1 - α := sub_pos.mpr hα1
    positivity
  refine ⟨φ t, hφt_pos, hφt_lt1, fun m i hi => ?_⟩
  by_cases him : i ≤ m
  · have hmgf : ∑ j ∈ Finset.range (m + 1), binomP m α j * Real.exp (-t * j) =
        (1 - α + α * Real.exp (-t)) ^ m := by
      have hadd := (add_pow (α * Real.exp (-t)) (1 - α) m).symm
      calc ∑ j ∈ Finset.range (m + 1), binomP m α j * Real.exp (-t * j)
          = ∑ j ∈ Finset.range (m + 1),
              (α * Real.exp (-t)) ^ j * (1 - α) ^ (m - j) * (m.choose j : ℝ) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            unfold binomP
            rw [mul_pow, ← Real.exp_nat_mul]
            ring_nf
        _ = (α * Real.exp (-t) + (1 - α)) ^ m := hadd
        _ = (1 - α + α * Real.exp (-t)) ^ m := by ring
    have hsingle : binomP m α i * Real.exp (-t * i) ≤ (1 - α + α * Real.exp (-t)) ^ m := by
      rw [← hmgf]
      exact Finset.single_le_sum (f := fun j => binomP m α j * Real.exp (-t * (j : ℝ)))
        (fun j _ => mul_nonneg (binomP_nonneg hα0.le hα1.le j) (Real.exp_pos _).le)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le him))
    have hexp_ge : Real.exp (-t * ((α - δ) * m)) ≤ Real.exp (-t * i) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hbi_le : binomP m α i * Real.exp (-t * ((α - δ) * m)) ≤
        (1 - α + α * Real.exp (-t)) ^ m :=
      (mul_le_mul_of_nonneg_left hexp_ge (binomP_nonneg hα0.le hα1.le i)).trans hsingle
    have hexp_pos : 0 < Real.exp (-t * ((α - δ) * m)) := Real.exp_pos _
    calc binomP m α i
        ≤ (1 - α + α * Real.exp (-t)) ^ m / Real.exp (-t * ((α - δ) * m)) :=
          (le_div_iff₀ hexp_pos).mpr hbi_le
      _ = (1 - α + α * Real.exp (-t)) ^ m * Real.exp ((α - δ) * t * m) := by
          rw [div_eq_mul_inv, ← Real.exp_neg]; ring_nf
      _ = (φ t) ^ m := by
          dsimp only [φ]
          rw [mul_pow, ← Real.exp_nat_mul]
          ring_nf
  · unfold binomP
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp only [Nat.cast_zero, zero_mul]
    exact pow_nonneg hφt_pos.le m

private lemma binomP_upper_tail {α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ m i : ℕ, (α + δ) * m ≤ i → binomP m α i ≤ ρ ^ m := by
  let ψ : ℝ → ℝ := fun t => (1 - α + α * Real.exp t) * Real.exp (-(α + δ) * t)
  have hψ0 : ψ 0 = 1 := by simp [ψ]
  have hderiv1 : HasDerivAt (fun t : ℝ => 1 - α + α * Real.exp t) α 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).exp.const_mul α).const_add (1 - α)
    simpa using h1
  have hderiv2 : HasDerivAt (fun t : ℝ => Real.exp (-(α + δ) * t)) (-(α + δ)) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).const_mul (-(α + δ))).exp
    simpa using h1
  have hderiv : HasDerivAt ψ (-δ) 0 := by
    have hmul : HasDerivAt ψ (α * Real.exp (-(α + δ) * 0) +
        (1 - α + α * Real.exp 0) * (-(α + δ))) 0 := hderiv1.mul hderiv2
    rw [mul_zero, Real.exp_zero] at hmul
    convert hmul using 1
    ring
  have htend : Tendsto (fun t : ℝ => ‖t - 0‖⁻¹ * ‖ψ t - ψ 0 - (t - 0) • (-δ)‖) (𝓝 0) (𝓝 0) :=
    hasDerivAt_iff_tendsto.mp hderiv
  obtain ⟨r, hr_pos, hr⟩ := Metric.tendsto_nhds_nhds.mp htend (δ / 2) (by positivity)
  let t : ℝ := min (r / 2) 1
  have ht_pos : 0 < t := by positivity
  have ht_lt : dist t 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hval := hr ht_lt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hval
  simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, abs_of_pos ht_pos] at hval
  have hbound : |ψ t - 1 + t * δ| < t * (δ / 2) := by
    have h2 : t * (t⁻¹ * |ψ t - 1 + t * δ|) < t * (δ / 2) :=
      mul_lt_mul_of_pos_left (by
        simpa [hψ0, sub_neg_eq_add, mul_comm t (-δ), mul_neg, sub_eq_add_neg, add_assoc,
          mul_comm δ t] using hval) ht_pos
    rwa [← mul_assoc, mul_inv_cancel₀ ht_pos.ne', one_mul] at h2
  have hψt_lt1 : ψ t < 1 := by
    have := (abs_lt.mp hbound).2
    linarith [mul_pos ht_pos hδ]
  have hψt_pos : 0 < ψ t := by
    dsimp only [ψ]
    have : 0 < 1 - α := sub_pos.mpr hα1
    positivity
  refine ⟨ψ t, hψt_pos, hψt_lt1, fun m i hi => ?_⟩
  by_cases him : i ≤ m
  · have hmgf : ∑ j ∈ Finset.range (m + 1), binomP m α j * Real.exp (t * j) =
        (1 - α + α * Real.exp t) ^ m := by
      have hadd := (add_pow (α * Real.exp t) (1 - α) m).symm
      calc ∑ j ∈ Finset.range (m + 1), binomP m α j * Real.exp (t * j)
          = ∑ j ∈ Finset.range (m + 1),
              (α * Real.exp t) ^ j * (1 - α) ^ (m - j) * (m.choose j : ℝ) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            unfold binomP
            rw [mul_pow, ← Real.exp_nat_mul]
            ring_nf
        _ = (α * Real.exp t + (1 - α)) ^ m := hadd
        _ = (1 - α + α * Real.exp t) ^ m := by ring
    have hsingle : binomP m α i * Real.exp (t * i) ≤ (1 - α + α * Real.exp t) ^ m := by
      rw [← hmgf]
      exact Finset.single_le_sum (f := fun j => binomP m α j * Real.exp (t * (j : ℝ)))
        (fun j _ => mul_nonneg (binomP_nonneg hα0.le hα1.le j) (Real.exp_pos _).le)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le him))
    have hexp_ge : Real.exp (t * ((α + δ) * m)) ≤ Real.exp (t * i) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hbi_le : binomP m α i * Real.exp (t * ((α + δ) * m)) ≤
        (1 - α + α * Real.exp t) ^ m :=
      (mul_le_mul_of_nonneg_left hexp_ge (binomP_nonneg hα0.le hα1.le i)).trans hsingle
    have hexp_pos : 0 < Real.exp (t * ((α + δ) * m)) := Real.exp_pos _
    calc binomP m α i
        ≤ (1 - α + α * Real.exp t) ^ m / Real.exp (t * ((α + δ) * m)) :=
          (le_div_iff₀ hexp_pos).mpr hbi_le
      _ = (1 - α + α * Real.exp t) ^ m * Real.exp (-(α + δ) * t * m) := by
          rw [div_eq_mul_inv, ← Real.exp_neg]; ring_nf
      _ = (ψ t) ^ m := by
          dsimp only [ψ]
          rw [mul_pow, ← Real.exp_nat_mul]
          ring_nf
  · unfold binomP
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp only [Nat.cast_zero, zero_mul]
    exact pow_nonneg hψt_pos.le m

private lemma tendsto_poly_mul_pow_zero (k : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun m : ℕ => ((m + 1 : ℝ) ^ k) * ρ ^ m) atTop (𝓝 0) := by
  rcases eq_or_lt_of_le hρ0 with rfl | hρ_pos
  · refine tendsto_const_nhds.congr' ?_
    refine eventually_atTop.mpr ⟨1, fun m hm => ?_⟩
    simp [Nat.ne_of_gt hm]
  · let r₀ : ℝ := (1 + ρ) / 2
    have hr₀_gt : ρ < r₀ := by dsimp only [r₀]; linarith
    have hr₀_lt1 : r₀ < 1 := by dsimp only [r₀]; linarith
    have hr₀_pos : 0 < r₀ := by dsimp only [r₀]; linarith
    have hratio_lim : Tendsto (fun m : ℕ => (1 + 1 / (m + 1 : ℝ)) ^ k * ρ) atTop (𝓝 ρ) := by
      have h1 : Tendsto (fun m : ℕ => 1 + 1 / (m + 1 : ℝ)) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (h1.pow k).mul_const ρ
    obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (hratio_lim.eventually (ge_mem_nhds hr₀_gt))
    have hstep_le : ∀ n : ℕ, ((M₀ + n + 1 : ℝ) ^ k) * ρ ^ (M₀ + n) ≤
        ((M₀ + 1 : ℝ) ^ k) * ρ ^ M₀ * r₀ ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ d ih =>
        have hstep := hM₀ (M₀ + d) (by omega)
        have hinc : (M₀ + d + 2 : ℝ) / (M₀ + d + 1 : ℝ) = 1 + 1 / ((M₀ + d : ℕ) + 1 : ℝ) := by
          push_cast; field_simp; ring
        have hnext : ((M₀ + (d + 1 : ℕ) + 1 : ℝ) ^ k) * ρ ^ (M₀ + (d + 1)) =
            (((M₀ + d + 2 : ℝ) / (M₀ + d + 1 : ℝ)) ^ k * ρ) *
              (((M₀ + d + 1 : ℝ) ^ k) * ρ ^ (M₀ + d)) := by
          rw [div_pow, ← add_assoc M₀ d 1, pow_succ ρ (M₀ + d)]
          have hne : (M₀ + d + 1 : ℝ) ^ k ≠ 0 := by positivity
          push_cast
          field_simp
          ring
        push_cast at hnext
        push_cast
        rw [hnext, hinc]
        calc (1 + 1 / ((M₀ + d : ℕ) + 1 : ℝ)) ^ k * ρ * (((M₀ + d + 1 : ℝ) ^ k) * ρ ^ (M₀ + d))
            ≤ r₀ * (((M₀ + 1 : ℝ) ^ k) * ρ ^ M₀ * r₀ ^ d) := by
              refine mul_le_mul hstep ih (by positivity) hr₀_pos.le
          _ = ((M₀ + 1 : ℝ) ^ k) * ρ ^ M₀ * r₀ ^ (d + 1) := by
              rw [pow_succ]; ring
    have hr₀_lim : Tendsto (fun m : ℕ => ((M₀ + 1 : ℝ) ^ k) * ρ ^ M₀ * r₀ ^ (m - M₀))
        atTop (𝓝 0) := by
      have hs : Tendsto (fun m : ℕ => r₀ ^ (m - M₀)) atTop (𝓝 0) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀_pos.le hr₀_lt1).comp
          (tendsto_sub_atTop_nat M₀)
      simpa using (tendsto_const_nhds (x := ((M₀ + 1 : ℝ) ^ k) * ρ ^ M₀)).mul hs
    refine squeeze_zero' (eventually_atTop.mpr ⟨0, fun m _ => by positivity⟩)
      (eventually_atTop.mpr ⟨M₀, fun m hm => ?_⟩) hr₀_lim
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
    simpa [Nat.add_sub_cancel_left] using hstep_le n

private lemma x_div_asymptotic_eq {m l r : ℕ} {a : ℝ} (hm_pos : 0 < m) (hl : 0 < l) (ha : 0 < a)
    (hrm : r ≤ m) (hr_pos : 0 < r) :
    x m l a r / asymptotic m l a =
      (normNum m l a r * (Real.sqrt (2 * Real.pi * m * (paramT a * (1 - paramT a)))) ^ l *
        (1 - (paramQ a) ^ l)) *
        (1 / (normDen l a r * (Real.sqrt l * (Real.sqrt (2 * Real.pi * r * (paramP a * paramQ a))) ^ (l - 1)))) *
        (Real.sqrt (r / (paramT a * m))) ^ (l - 1) := by
  have hp0 := paramP_pos ha
  have hq0 := paramQ_pos ha
  have ht0 := paramT_pos ha
  have ht1 := paramT_lt_one ha
  have hm_rpos : (0 : ℝ) < m := by positivity
  let p : ℝ := paramP a
  let q : ℝ := paramQ a
  let θ : ℝ := paramT a
  let σm : ℝ := Real.sqrt (2 * Real.pi * m * (θ * (1 - θ)))
  let σr0 : ℝ := Real.sqrt (2 * Real.pi * (θ * m) * (p * q))
  let S : ℝ := Real.sqrt (2 * Real.pi * r * (p * q))
  have h1mθ : 0 < 1 - θ := sub_pos.mpr ht1
  have hσr0_pos : 0 < σr0 := by positivity
  have hS_pos : 0 < S := by positivity
  have hden_pos : 0 < normDen l a r := lt_of_lt_of_le (by positivity) (normDen_ge_inv_pow hl ha r)
  have hsig_eq : S / σr0 = Real.sqrt (r / (θ * m)) := by
    dsimp only [S, σr0]
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hx_eq : x m l a r / asymptotic m l a =
      normNum m l a r * (1 / normDen l a r) * (1 / asymNorm m l a) := by
    rw [x_eq_normalized ha hl hrm, asymptotic_eq_normalized hm_pos hl ha]
    have hpow_ne : ((1 + 2 * a) / (1 + a)) ^ (m * l) ≠ 0 := by positivity
    field_simp
  have h1asym : 1 / asymNorm m l a = (1 - q ^ l) * σm ^ l / (Real.sqrt l * σr0 ^ (l - 1)) := by
    have h1mql_pos : 0 < 1 - q ^ l := sub_pos.mpr (pow_lt_one₀ hq0.le (paramQ_lt_one ha) hl.ne')
    have hσm_pos : 0 < σm := by positivity
    have hhl_ne : (Real.sqrt l * σr0 ^ (l - 1)) ≠ 0 := by positivity
    dsimp only [asymNorm]
    change 1 / (((1 / σm) ^ l * (1 / (1 - q ^ l))) / (1 / (Real.sqrt l * σr0 ^ (l - 1)))) =
      (1 - q ^ l) * σm ^ l / (Real.sqrt l * σr0 ^ (l - 1))
    rw [div_pow, one_pow, div_div_eq_mul_div, div_eq_div_iff (by positivity) hhl_ne]
    rw [one_mul, one_div_mul_cancel hhl_ne]
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ = ((1 - q ^ l) * (1 / (1 - q ^ l))) * (σm ^ l * (1 / σm ^ l)) := by
          rw [mul_one_div_cancel h1mql_pos.ne', mul_one_div_cancel (pow_ne_zero l hσm_pos.ne')]
      _ = (1 - q ^ l) * σm ^ l * (1 / σm ^ l * (1 / (1 - q ^ l))) := by ring
  rw [hx_eq, h1asym, ← hsig_eq, div_pow]
  calc normNum m l a r * (1 / normDen l a r) *
        ((1 - q ^ l) * σm ^ l / (Real.sqrt l * σr0 ^ (l - 1)))
      = (normNum m l a r * σm ^ l * (1 - q ^ l)) / (normDen l a r * Real.sqrt l * σr0 ^ (l - 1)) := by
          ring
    _ = ((normNum m l a r * σm ^ l * (1 - q ^ l)) * S ^ (l - 1)) /
          ((normDen l a r * Real.sqrt l * σr0 ^ (l - 1)) * S ^ (l - 1)) := by
          rw [mul_div_mul_right _ _ (by positivity)]
    _ = (normNum m l a r * σm ^ l * (1 - q ^ l)) *
          (1 / (normDen l a r * (Real.sqrt l * S ^ (l - 1)))) * (S ^ (l - 1) / σr0 ^ (l - 1)) := by
          ring

private lemma main_lower_bound {m l r₀ K N₁ N_den : ℕ} {a ε₀ u : ℝ}
    (hm_pos : 0 < m) (hl : 0 < l) (ha : 0 < a) (hr₀_pos : 0 < r₀) (hr₀_le_m : r₀ ≤ m)
    (hK_le_r₀ : K ≤ r₀) (hNden_le_r₀ : N_den ≤ r₀) (hmN1 : N₁ ≤ m)
    (hε₀_pos : 0 < ε₀) (hε₀_le1 : ε₀ ≤ 1) (hu_pos : 0 < u) (hu_half : u ≤ 1 / 4)
    (h1mu_pow : 1 - ε₀ / 32 ≤ (1 - u) ^ l) (h1mu2_pow : 1 - ε₀ / 64 ≤ (1 - 2 * u) ^ l)
    (hK_sum : (1 - ε₀ / 32) / (1 - (paramQ a) ^ l) ≤
      ∑ j ∈ Finset.range (K + 1), (paramQ a) ^ (j * l))
    (hK_σm : (K + 1 : ℝ) / Real.sqrt (paramT a * (1 - paramT a)) ≤ Real.sqrt m)
    (hK_u : (K + 1 : ℝ) ^ 2 / (2 * u * (Real.sqrt (paramT a * (1 - paramT a))) ^ 2) ≤ m)
    (h1_θu : 1 / (paramT a * u) ≤ m) (hr₀_def : r₀ = ⌊paramT a * m⌋₊)
    (hN₁ : ∀ n : ℕ, N₁ ≤ n → ∀ k : ℕ,
      |(k : ℝ) - paramT a * n| ≤ 1 * Real.sqrt (paramT a * (1 - paramT a)) * Real.sqrt n →
      0 < k ∧ k < n ∧
        |Real.sqrt (2 * Real.pi * n) * Real.sqrt (paramT a * (1 - paramT a)) * binomP n (paramT a) k /
          Real.exp (-((k : ℝ) - paramT a * n) ^ 2 / (2 * n * (paramT a * (1 - paramT a)))) - 1| ≤ u)
    (hN_den : ∀ r : ℕ, N_den ≤ r →
      dist (normDen l a r * (Real.sqrt l * (Real.sqrt (2 * Real.pi * r * (paramP a * paramQ a))) ^ (l - 1))) 1 <
        ε₀ / 32) :
    1 - ε₀ / 2 ≤ x m l a r₀ / asymptotic m l a := by
  have hp0 := paramP_pos ha
  have hq0 := paramQ_pos ha
  have hq1 := paramQ_lt_one ha
  have ht0 := paramT_pos ha
  have ht1 := paramT_lt_one ha
  have hm_rpos : (0 : ℝ) < m := by positivity
  let p : ℝ := paramP a
  let q : ℝ := paramQ a
  let θ : ℝ := paramT a
  let σθ : ℝ := Real.sqrt (θ * (1 - θ))
  have hσθ_pos : 0 < σθ := Real.sqrt_pos.mpr (mul_pos ht0 (sub_pos.mpr ht1))
  have hql_lt1 : q ^ l < 1 := pow_lt_one₀ hq0.le hq1 hl.ne'
  have h1mql_pos : 0 < 1 - q ^ l := sub_pos.mpr hql_lt1
  let σm : ℝ := Real.sqrt (2 * Real.pi * m * (θ * (1 - θ)))
  have hσm_pos : 0 < σm := by
    have : 0 < 1 - θ := sub_pos.mpr ht1
    positivity
  rw [x_div_asymptotic_eq hm_pos hl ha hr₀_le_m hr₀_pos]
  have hA_lb : 1 - ε₀ / 16 ≤ normNum m l a r₀ * σm ^ l * (1 - q ^ l) := by
    have hterm_lb : ∀ j ∈ Finset.range (K + 1),
        (1 - ε₀ / 32) * q ^ (j * l) ≤ (σm * binomP m θ (r₀ - j)) ^ l * q ^ (j * l) := by
      intro j hj
      have hjk : j ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hjr : j ≤ r₀ := hjk.trans hK_le_r₀
      have hdist : |((r₀ - j : ℕ) : ℝ) - θ * m| ≤ 1 * σθ * Real.sqrt m := by
        rw [Nat.cast_sub hjr]
        have h1 : (r₀ : ℝ) ≤ θ * m := by rw [hr₀_def]; exact Nat.floor_le (by positivity)
        have h2 : θ * m < (r₀ : ℝ) + 1 := by rw [hr₀_def]; exact Nat.lt_floor_add_one _
        have h3 : (j : ℝ) ≤ K := by exact_mod_cast hjk
        have h4 : (K + 1 : ℝ) ≤ σθ * Real.sqrt m := by
          have := (div_le_iff₀ hσθ_pos).mp hK_σm
          linarith
        rw [abs_le]
        constructor <;> linarith
      have hst := hN₁ m hmN1 (r₀ - j) hdist
      have hst_lb : 1 - u ≤ σm * binomP m θ (r₀ - j) /
          Real.exp (-(((r₀ - j : ℕ) : ℝ) - θ * m) ^ 2 / (2 * m * (θ * (1 - θ)))) := by
        have := (abs_le.mp hst.2.2).1
        have hσmeq : σm = Real.sqrt (2 * Real.pi * m) * Real.sqrt (paramT a * (1 - paramT a)) := by
          dsimp only [σm, θ]
          rw [Real.sqrt_mul (by positivity)]
        rw [hσmeq]
        linarith
      have hexp_pos : 0 < Real.exp (-(((r₀ - j : ℕ) : ℝ) - θ * m) ^ 2 / (2 * m * (θ * (1 - θ)))) :=
        Real.exp_pos _
      have hst_mul : (1 - u) *
          Real.exp (-(((r₀ - j : ℕ) : ℝ) - θ * m) ^ 2 / (2 * m * (θ * (1 - θ)))) ≤
          σm * binomP m θ (r₀ - j) := (le_div_iff₀ hexp_pos).mp hst_lb
      have hexp_lb : 1 - u ≤
          Real.exp (-(((r₀ - j : ℕ) : ℝ) - θ * m) ^ 2 / (2 * m * (θ * (1 - θ)))) := by
        have harg_le : (((r₀ - j : ℕ) : ℝ) - θ * m) ^ 2 / (2 * m * (θ * (1 - θ))) ≤ u := by
          have h1 : (r₀ : ℝ) ≤ θ * m := by rw [hr₀_def]; exact Nat.floor_le (by positivity)
          have h2 : θ * m < (r₀ : ℝ) + 1 := by rw [hr₀_def]; exact Nat.lt_floor_add_one _
          have h3 : (j : ℝ) ≤ K := by exact_mod_cast hjk
          have habs : |((r₀ - j : ℕ) : ℝ) - θ * m| ≤ K + 1 := by
            rw [Nat.cast_sub hjr, abs_le]
            constructor <;> linarith
          have hsq : (((r₀ - j : ℕ) : ℝ) - θ * m) ^ 2 ≤ (K + 1 : ℝ) ^ 2 := by
            simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs 2
          have hσ2 : θ * (1 - θ) = σθ ^ 2 :=
            (Real.sq_sqrt (mul_pos ht0 (sub_pos.mpr ht1)).le).symm
          have hku' : (K + 1 : ℝ) ^ 2 ≤ m * (2 * u * σθ ^ 2) := (div_le_iff₀ (by positivity)).mp hK_u
          rw [hσ2, div_le_iff₀ (by positivity)]
          linarith [hsq, hku']
        have hneg := Real.add_one_le_exp
          (-((((r₀ - j : ℕ) : ℝ) - θ * m) ^ 2 / (2 * m * (θ * (1 - θ)))))
        rw [show -(((r₀ - j : ℕ) : ℝ) - θ * m) ^ 2 / (2 * m * (θ * (1 - θ))) =
            -((((r₀ - j : ℕ) : ℝ) - θ * m) ^ 2 / (2 * m * (θ * (1 - θ)))) by ring]
        linarith
      have hprod_lb : 1 - 2 * u ≤ σm * binomP m θ (r₀ - j) := by
        have h1u : 0 ≤ 1 - u := by linarith [hu_half]
        have hmul : (1 - u) * (1 - u) ≤
            (1 - u) * Real.exp (-(((r₀ - j : ℕ) : ℝ) - θ * m) ^ 2 / (2 * m * (θ * (1 - θ)))) :=
          mul_le_mul_of_nonneg_left hexp_lb h1u
        have hsq1 : 1 - 2 * u ≤ (1 - u) * (1 - u) := by
          have : (1 - u) * (1 - u) = 1 - 2 * u + u ^ 2 := by ring
          linarith [sq_nonneg u]
        exact hsq1.trans (hmul.trans hst_mul)
      have hpow_lb : 1 - ε₀ / 32 ≤ (σm * binomP m θ (r₀ - j)) ^ l :=
        (by linarith [hε₀_pos] : 1 - ε₀ / 32 ≤ 1 - ε₀ / 64).trans
          (h1mu2_pow.trans (pow_le_pow_left₀ (by linarith [hu_half]) hprod_lb l))
      exact mul_le_mul_of_nonneg_right hpow_lb (pow_nonneg hq0.le _)
    have hsub_sum : ∑ j ∈ Finset.range (K + 1), (binomP m θ (r₀ - j) ^ l * q ^ (j * l)) ≤
        normNum m l a r₀ := by
      unfold normNum
      change ∑ j ∈ Finset.range (K + 1), binomP m θ (r₀ - j) ^ l * q ^ (j * l) ≤
        ∑ i ∈ Finset.range (r₀ + 1), binomP m θ i ^ l * q ^ ((r₀ - i) * l)
      have h_eq : ∑ j ∈ Finset.range (K + 1), binomP m θ (r₀ - j) ^ l * q ^ (j * l) =
          ∑ i ∈ Finset.image (fun j => r₀ - j) (Finset.range (K + 1)),
            binomP m θ i ^ l * q ^ ((r₀ - i) * l) := by
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl fun j hj => ?_
          have hjk : j ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hjr : j ≤ r₀ := hjk.trans hK_le_r₀
          rw [Nat.sub_sub_self hjr]
        · intro x hx y hy hxy
          dsimp only at hxy
          have hx' : x ≤ r₀ := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)).trans hK_le_r₀
          have hy' : y ≤ r₀ := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hy)).trans hK_le_r₀
          omega
      rw [h_eq]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => ?_)
      · intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        have hj' : j < K + 1 := Finset.mem_range.mp hj
        exact Finset.mem_range.mpr (by omega)
      · exact mul_nonneg (pow_nonneg (binomP_nonneg ht0.le ht1.le i) l) (pow_nonneg hq0.le _)
    have hsum_scaled :
        (1 - ε₀ / 32) * ∑ j ∈ Finset.range (K + 1), q ^ (j * l) ≤ normNum m l a r₀ * σm ^ l := by
      calc (1 - ε₀ / 32) * ∑ j ∈ Finset.range (K + 1), q ^ (j * l)
          = ∑ j ∈ Finset.range (K + 1), (1 - ε₀ / 32) * q ^ (j * l) := Finset.mul_sum _ _ _
        _ ≤ ∑ j ∈ Finset.range (K + 1), (σm * binomP m θ (r₀ - j)) ^ l * q ^ (j * l) :=
            Finset.sum_le_sum hterm_lb
        _ = (∑ j ∈ Finset.range (K + 1), binomP m θ (r₀ - j) ^ l * q ^ (j * l)) * σm ^ l := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [mul_pow]; ring
        _ ≤ normNum m l a r₀ * σm ^ l := mul_le_mul_of_nonneg_right hsub_sum (by positivity)
    calc 1 - ε₀ / 16
        ≤ (1 - ε₀ / 32) * (1 - ε₀ / 32) := by
          have hsq : (1 - ε₀ / 32) * (1 - ε₀ / 32) = 1 - ε₀ / 16 + (ε₀ / 32) ^ 2 := by ring
          linarith [sq_nonneg (ε₀ / 32)]
      _ = (1 - ε₀ / 32) * (((1 - ε₀ / 32) / (1 - q ^ l)) * (1 - q ^ l)) := by
          field_simp [h1mql_pos.ne']
      _ ≤ ((1 - ε₀ / 32) * ∑ j ∈ Finset.range (K + 1), q ^ (j * l)) * (1 - q ^ l) := by
          have hK_sum' : (1 - ε₀ / 32) / (1 - q ^ l) ≤ ∑ j ∈ Finset.range (K + 1), q ^ (j * l) := hK_sum
          have h1mε32 : 0 ≤ 1 - ε₀ / 32 := by linarith [hε₀_le1]
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK_sum' h1mε32) h1mql_pos.le
      _ ≤ (normNum m l a r₀ * σm ^ l) * (1 - q ^ l) :=
          mul_le_mul_of_nonneg_right hsum_scaled h1mql_pos.le
      _ = normNum m l a r₀ * σm ^ l * (1 - q ^ l) := by ring
  have hB_lb : 1 - ε₀ / 32 ≤
      1 / (normDen l a r₀ * (Real.sqrt l * (Real.sqrt (2 * Real.pi * r₀ * (p * q))) ^ (l - 1))) := by
    have hnd := hN_den r₀ hNden_le_r₀
    rw [Real.dist_eq] at hnd
    have hnd_ub : normDen l a r₀ * (Real.sqrt l * (Real.sqrt (2 * Real.pi * r₀ * (p * q))) ^ (l - 1)) ≤
        1 + ε₀ / 32 := by linarith [(abs_lt.mp hnd).2]
    have h1 : 1 - ε₀ / 32 ≤ 1 / (1 + ε₀ / 32) := by
      rw [le_div_iff₀ (by positivity)]
      have hsq : (1 - ε₀ / 32) * (1 + ε₀ / 32) = 1 - (ε₀ / 32) ^ 2 := by ring
      linarith [sq_nonneg (ε₀ / 32)]
    have hnd_pos : 0 < normDen l a r₀ *
        (Real.sqrt l * (Real.sqrt (2 * Real.pi * r₀ * (p * q))) ^ (l - 1)) := by
      have : 0 < normDen l a r₀ := lt_of_lt_of_le (by positivity) (normDen_ge_inv_pow hl ha r₀)
      positivity
    exact h1.trans (one_div_le_one_div_of_le hnd_pos hnd_ub)
  have hC_lb : 1 - ε₀ / 32 ≤ (Real.sqrt (r₀ / (θ * m))) ^ (l - 1) := by
    have hr0_ub : (r₀ : ℝ) / (θ * m) ≤ 1 := by
      rw [div_le_one (mul_pos ht0 hm_rpos), hr₀_def]
      exact Nat.floor_le (by positivity)
    have hr0_lb : 1 - u ≤ (r₀ : ℝ) / (θ * m) := by
      have h2 : θ * m < (r₀ : ℝ) + 1 := by rw [hr₀_def]; exact Nat.lt_floor_add_one _
      have h3 : 1 / (θ * m) ≤ u := by
        have := (div_le_iff₀ (mul_pos ht0 hu_pos)).mp h1_θu
        rw [div_le_iff₀ (mul_pos ht0 hm_rpos)]
        linarith
      have h4 : (r₀ : ℝ) / (θ * m) ≥ 1 - 1 / (θ * m) := by
        have hθm_pos : 0 < θ * m := mul_pos ht0 hm_rpos
        have heq : (1 : ℝ) - 1 / (θ * m) = (θ * m - 1) / (θ * m) := by
          nth_rewrite 1 [← div_self hθm_pos.ne']
          rw [div_sub_div_same]
        rw [ge_iff_le, heq]
        exact div_le_div_of_nonneg_right (by linarith) hθm_pos.le
      linarith
    have hsq_ge : 1 - u ≤ Real.sqrt ((r₀ : ℝ) / (θ * m)) := by
      have hnn : 0 ≤ (r₀ : ℝ) / (θ * m) := by positivity
      calc 1 - u ≤ (r₀ : ℝ) / (θ * m) := hr0_lb
        _ = Real.sqrt (((r₀ : ℝ) / (θ * m)) ^ 2) := (Real.sqrt_sq hnn).symm
        _ ≤ Real.sqrt ((r₀ : ℝ) / (θ * m)) := by
            apply Real.sqrt_le_sqrt
            rw [sq]
            exact (mul_le_mul_of_nonneg_left hr0_ub hnn).trans_eq (mul_one _)
    have h1u_le1 : 1 - u ≤ 1 := by linarith [hu_pos]
    exact h1mu_pow.trans ((pow_le_pow_of_le_one (by linarith [hu_half]) h1u_le1 (Nat.sub_le l 1)).trans
      (pow_le_pow_left₀ (by linarith [hu_half]) hsq_ge (l - 1)))
  have hA_nn : 0 ≤ normNum m l a r₀ * σm ^ l * (1 - q ^ l) := by
    unfold normNum
    have : 0 ≤ ∑ i ∈ Finset.range (r₀ + 1), binomP m (paramT a) i ^ l * (paramQ a) ^ ((r₀ - i) * l) :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg (binomP_nonneg ht0.le ht1.le _) l)
        (pow_nonneg hq0.le _)
    positivity
  have h16_lb : 1 - ε₀ / 16 ≤ 1 - ε₀ / 32 := by linarith
  have hAB : (1 - ε₀ / 16) ^ 2 ≤ (normNum m l a r₀ * σm ^ l * (1 - q ^ l)) *
      (1 / (normDen l a r₀ * (Real.sqrt l * (Real.sqrt (2 * Real.pi * r₀ * (p * q))) ^ (l - 1)))) :=
    by rw [sq]; exact mul_le_mul hA_lb (h16_lb.trans hB_lb) (by linarith [hε₀_le1]) hA_nn
  have hABC : (1 - ε₀ / 16) ^ 3 ≤ (normNum m l a r₀ * σm ^ l * (1 - q ^ l)) *
      (1 / (normDen l a r₀ * (Real.sqrt l * (Real.sqrt (2 * Real.pi * r₀ * (p * q))) ^ (l - 1)))) *
      (Real.sqrt (r₀ / (θ * m))) ^ (l - 1) := by
    have hB_nn : 0 ≤ 1 / (normDen l a r₀ * (Real.sqrt l * (Real.sqrt (2 * Real.pi * r₀ * (p * q))) ^ (l - 1))) := by
      have : 0 < normDen l a r₀ := lt_of_lt_of_le (by positivity) (normDen_ge_inv_pow hl ha r₀)
      positivity
    rw [show (1 - ε₀ / 16) ^ 3 = (1 - ε₀ / 16) ^ 2 * (1 - ε₀ / 16) by ring]
    exact mul_le_mul hAB (h16_lb.trans hC_lb) (by linarith [hε₀_le1]) (mul_nonneg hA_nn hB_nn)
  have hcube : 1 - ε₀ / 2 ≤ (1 - ε₀ / 16) ^ 3 := by
    have hid : (1 - ε₀ / 16) ^ 3 - (1 - ε₀ / 2) =
        (ε₀ / 16) * (5 + 3 * (ε₀ / 16) - (ε₀ / 16) ^ 2) := by ring
    have hsq : (ε₀ / 16) ^ 2 ≤ 1 := by
      rw [sq]
      exact mul_le_one₀ (by linarith [hε₀_le1]) (by positivity) (by linarith [hε₀_le1])
    have hpos : 0 ≤ 5 + 3 * (ε₀ / 16) - (ε₀ / 16) ^ 2 := by linarith [hsq, hε₀_pos]
    have hmul := mul_nonneg (by positivity : 0 ≤ ε₀ / 16) hpos
    linarith
  exact hcube.trans hABC

private lemma main_upper_mid {m l r K N₁ N_den : ℕ} {a ε₀ u δ : ℝ}
    (hm_pos : 0 < m) (hl : 0 < l) (ha : 0 < a) (hrm : r ≤ m) (hmN1 : N₁ ≤ m)
    (hε₀_pos : 0 < ε₀) (hε₀_le1 : ε₀ ≤ 1) (hu_pos : 0 < u) (hδ_pos : 0 < δ)
    (hδ_lt_θ : δ ≤ paramT a / 2) (hδ_θu : δ ≤ paramT a * u) (h1u_pow : (1 + u) ^ l ≤ 1 + ε₀ / 32)
    (hK_σm : (K + 1 : ℝ) / Real.sqrt (paramT a * (1 - paramT a)) ≤ Real.sqrt m)
    (hNden_m : (N_den : ℝ) / (paramT a - δ) ≤ m)
    (hmid : (paramT a - δ) * m ≤ r ∧ (r : ℝ) ≤ (paramT a + δ) * m)
    (hN₁ : ∀ n : ℕ, N₁ ≤ n → ∀ k : ℕ,
      |(k : ℝ) - paramT a * n| ≤ 1 * Real.sqrt (paramT a * (1 - paramT a)) * Real.sqrt n →
      0 < k ∧ k < n ∧
        |Real.sqrt (2 * Real.pi * n) * Real.sqrt (paramT a * (1 - paramT a)) * binomP n (paramT a) k /
          Real.exp (-((k : ℝ) - paramT a * n) ^ 2 / (2 * n * (paramT a * (1 - paramT a)))) - 1| ≤ u)
    (hN_den : ∀ r : ℕ, N_den ≤ r →
      dist (normDen l a r * (Real.sqrt l * (Real.sqrt (2 * Real.pi * r * (paramP a * paramQ a))) ^ (l - 1))) 1 <
        ε₀ / 32) :
    x m l a r / asymptotic m l a ≤ 1 + ε₀ / 2 := by
  have hq0 := paramQ_pos ha
  have hq1 := paramQ_lt_one ha
  have ht0 := paramT_pos ha
  have ht1 := paramT_lt_one ha
  have hm_rpos : (0 : ℝ) < m := by positivity
  let p : ℝ := paramP a
  let q : ℝ := paramQ a
  let θ : ℝ := paramT a
  let σθ : ℝ := Real.sqrt (θ * (1 - θ))
  have hσθ_pos : 0 < σθ := Real.sqrt_pos.mpr (mul_pos ht0 (sub_pos.mpr ht1))
  have hql_lt1 : q ^ l < 1 := pow_lt_one₀ hq0.le hq1 hl.ne'
  have hql_pos : 0 < q ^ l := pow_pos hq0 l
  have h1mql_pos : 0 < 1 - q ^ l := sub_pos.mpr hql_lt1
  let σm : ℝ := Real.sqrt (2 * Real.pi * m * (θ * (1 - θ)))
  have hσm_pos : 0 < σm := by
    have : 0 < 1 - θ := sub_pos.mpr ht1
    positivity
  have hr_pos : 0 < r := by
    have : 0 < (θ - δ) * m := mul_pos (by linarith [hδ_lt_θ]) hm_rpos
    have : (0 : ℝ) < r := lt_of_lt_of_le this hmid.1
    exact_mod_cast this
  have hNden_le_r : N_den ≤ r := by
    have h1 : (N_den : ℝ) ≤ (θ - δ) * m := by
      linarith [(div_le_iff₀ (by linarith [hδ_lt_θ])).mp hNden_m]
    exact_mod_cast h1.trans hmid.1
  rw [x_div_asymptotic_eq hm_pos hl ha hrm hr_pos]
  have hA_ub : normNum m l a r * σm ^ l * (1 - q ^ l) ≤ 1 + ε₀ / 32 := by
    let k_m : ℕ := ⌊(m + 1 : ℝ) * θ⌋₊
    have hk_mode : ∀ i : ℕ, binomP m θ i ≤ binomP m θ k_m := fun i => binomP_le_mode ht0 ht1 i
    have hkm_dist : |(k_m : ℝ) - θ * m| ≤ 1 * σθ * Real.sqrt m := by
      have h1 : (k_m : ℝ) ≤ (m + 1 : ℝ) * θ := Nat.floor_le (by positivity)
      have h2 : (m + 1 : ℝ) * θ < (k_m : ℝ) + 1 := Nat.lt_floor_add_one _
      have h4 : (K + 1 : ℝ) ≤ σθ * Real.sqrt m := by
        linarith [(div_le_iff₀ hσθ_pos).mp hK_σm]
      have h1K : (1 : ℝ) ≤ K + 1 := by exact_mod_cast Nat.succ_pos K
      have hm1 : (m + 1 : ℝ) * θ = θ * m + θ := by ring
      rw [abs_le]
      constructor <;> linarith [h1, h2, h4, h1K, ht0, ht1, hm1]
    have hst := hN₁ m hmN1 k_m hkm_dist
    have hst_ub : σm * binomP m θ k_m ≤ 1 + u := by
      have h1 : σm * binomP m θ k_m /
          Real.exp (-((k_m : ℝ) - θ * m) ^ 2 / (2 * m * (θ * (1 - θ)))) ≤ 1 + u := by
        have := (abs_le.mp hst.2.2).2
        have hσmeq : σm = Real.sqrt (2 * Real.pi * m) * Real.sqrt (paramT a * (1 - paramT a)) := by
          dsimp only [σm, θ]
          rw [Real.sqrt_mul (by positivity)]
        rw [hσmeq]
        linarith
      have hexp_pos : 0 < Real.exp (-((k_m : ℝ) - θ * m) ^ 2 / (2 * m * (θ * (1 - θ)))) :=
        Real.exp_pos _
      have hexp_le1 : Real.exp (-((k_m : ℝ) - θ * m) ^ 2 / (2 * m * (θ * (1 - θ)))) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have : 0 < 2 * (m : ℝ) * (θ * (1 - θ)) := mul_pos (by positivity) (mul_pos ht0 (sub_pos.mpr ht1))
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) this.le
      have hmul := (div_le_iff₀ hexp_pos).mp h1
      exact hmul.trans ((mul_le_mul_of_nonneg_left hexp_le1 (by positivity : 0 ≤ 1 + u)).trans_eq
        (mul_one _))
    have hpow_ub : (σm * binomP m θ k_m) ^ l ≤ 1 + ε₀ / 32 :=
      (pow_le_pow_left₀ (mul_nonneg hσm_pos.le (binomP_nonneg ht0.le ht1.le k_m)) hst_ub l).trans
        h1u_pow
    have hq_sum_ub : (∑ i ∈ Finset.range (r + 1), q ^ ((r - i) * l)) * (1 - q ^ l) ≤ 1 := by
      have hrev : ∑ i ∈ Finset.range (r + 1), q ^ ((r - i) * l) =
          ∑ j ∈ Finset.range (r + 1), (q ^ l) ^ j := by
        have h1 := Finset.sum_range_reflect (fun j => q ^ (j * l)) (r + 1)
        calc ∑ i ∈ Finset.range (r + 1), q ^ ((r - i) * l)
            = ∑ i ∈ Finset.range (r + 1), q ^ ((r + 1 - 1 - i) * l) := rfl
          _ = ∑ j ∈ Finset.range (r + 1), q ^ (j * l) := h1
          _ = ∑ j ∈ Finset.range (r + 1), (q ^ l) ^ j := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [← pow_mul, mul_comm j l]
      rw [hrev]
      have hgeo := geom_sum_mul (q ^ l) (r + 1)
      have hsub : (∑ j ∈ Finset.range (r + 1), (q ^ l) ^ j) * (1 - q ^ l) =
          1 - (q ^ l) ^ (r + 1) := by linarith
      rw [hsub]
      have : 0 ≤ (q ^ l) ^ (r + 1) := pow_nonneg hql_pos.le _
      linarith
    have hnum_ub : normNum m l a r * σm ^ l ≤
        (σm * binomP m θ k_m) ^ l * ∑ i ∈ Finset.range (r + 1), q ^ ((r - i) * l) := by
      unfold normNum
      calc (∑ i ∈ Finset.range (r + 1), binomP m (paramT a) i ^ l * (paramQ a) ^ ((r - i) * l)) * σm ^ l
          = ∑ i ∈ Finset.range (r + 1), (σm * binomP m θ i) ^ l * q ^ ((r - i) * l) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [mul_pow]; ring
        _ ≤ ∑ i ∈ Finset.range (r + 1), (σm * binomP m θ k_m) ^ l * q ^ ((r - i) * l) := by
              refine Finset.sum_le_sum fun i _ => ?_
              have h1 : σm * binomP m θ i ≤ σm * binomP m θ k_m :=
                mul_le_mul_of_nonneg_left (hk_mode i) hσm_pos.le
              exact mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (mul_nonneg hσm_pos.le (binomP_nonneg ht0.le ht1.le i)) h1 l)
                (pow_nonneg hq0.le _)
        _ = (σm * binomP m θ k_m) ^ l * ∑ i ∈ Finset.range (r + 1), q ^ ((r - i) * l) := by
              rw [← Finset.mul_sum]
    calc normNum m l a r * σm ^ l * (1 - q ^ l)
        ≤ ((σm * binomP m θ k_m) ^ l * ∑ i ∈ Finset.range (r + 1), q ^ ((r - i) * l)) *
            (1 - q ^ l) := mul_le_mul_of_nonneg_right hnum_ub h1mql_pos.le
      _ = (σm * binomP m θ k_m) ^ l *
            ((∑ i ∈ Finset.range (r + 1), q ^ ((r - i) * l)) * (1 - q ^ l)) := by ring
      _ ≤ (σm * binomP m θ k_m) ^ l * 1 :=
            mul_le_mul_of_nonneg_left hq_sum_ub (pow_nonneg (mul_nonneg hσm_pos.le
              (binomP_nonneg ht0.le ht1.le k_m)) l)
      _ ≤ 1 + ε₀ / 32 := by linarith
  have hB_ub : 1 / (normDen l a r * (Real.sqrt l * (Real.sqrt (2 * Real.pi * r * (p * q))) ^ (l - 1))) ≤
      1 + ε₀ / 16 := by
    have hnd := hN_den r hNden_le_r
    rw [Real.dist_eq] at hnd
    have hnd_lb : 1 - ε₀ / 32 ≤
        normDen l a r * (Real.sqrt l * (Real.sqrt (2 * Real.pi * r * (p * q))) ^ (l - 1)) := by
      linarith [(abs_lt.mp hnd).1]
    have hpos_lhs : 0 < 1 - ε₀ / 32 := by linarith [hε₀_le1]
    have h1 : 1 / (normDen l a r * (Real.sqrt l * (Real.sqrt (2 * Real.pi * r * (p * q))) ^ (l - 1))) ≤
        1 / (1 - ε₀ / 32) := one_div_le_one_div_of_le hpos_lhs hnd_lb
    have h2 : 1 / (1 - ε₀ / 32) ≤ 1 + ε₀ / 16 := by
      rw [div_le_iff₀ hpos_lhs]
      have hmul : (1 + ε₀ / 16) * (1 - ε₀ / 32) = 1 + ε₀ / 32 - ε₀ ^ 2 / 512 := by ring
      have hsq : ε₀ ^ 2 ≤ ε₀ := by
        rw [sq]
        exact (mul_le_mul_of_nonneg_left hε₀_le1 hε₀_pos.le).trans_eq (mul_one _)
      linarith
    exact h1.trans h2
  have hC_ub : (Real.sqrt (r / (θ * m))) ^ (l - 1) ≤ 1 + ε₀ / 32 := by
    have hr_ub : (r : ℝ) / (θ * m) ≤ 1 + u := by
      have hδm : δ * m ≤ θ * u * m := mul_le_mul_of_nonneg_right hδ_θu hm_rpos.le
      have hru : (r : ℝ) ≤ (1 + u) * (θ * m) := by linarith [hmid.2, hδm]
      exact (div_le_iff₀ (mul_pos ht0 hm_rpos)).mpr hru
    have hsq_le : Real.sqrt ((r : ℝ) / (θ * m)) ≤ 1 + u := by
      calc Real.sqrt ((r : ℝ) / (θ * m)) ≤ Real.sqrt (1 + u) := Real.sqrt_le_sqrt hr_ub
        _ ≤ Real.sqrt ((1 + u) ^ 2) := Real.sqrt_le_sqrt (by
            have : (1 + u) ^ 2 = 1 + 2 * u + u ^ 2 := by ring
            linarith [sq_nonneg u, hu_pos])
        _ = 1 + u := Real.sqrt_sq (by linarith [hu_pos])
    calc (Real.sqrt (r / (θ * m))) ^ (l - 1)
        ≤ (1 + u) ^ (l - 1) := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq_le (l - 1)
      _ ≤ (1 + u) ^ l := pow_le_pow_right₀ (by linarith [hu_pos]) (Nat.sub_le l 1)
      _ ≤ 1 + ε₀ / 32 := h1u_pow
  have hden_pos : 0 < normDen l a r := lt_of_lt_of_le (by positivity) (normDen_ge_inv_pow hl ha r)
  have hB_nn : 0 ≤ 1 / (normDen l a r * (Real.sqrt l * (Real.sqrt (2 * Real.pi * r * (p * q))) ^ (l - 1))) :=
    by positivity
  have h16_ub : 1 + ε₀ / 32 ≤ 1 + ε₀ / 16 := by linarith [hε₀_pos]
  have hAB : (normNum m l a r * σm ^ l * (1 - q ^ l)) *
      (1 / (normDen l a r * (Real.sqrt l * (Real.sqrt (2 * Real.pi * r * (p * q))) ^ (l - 1)))) ≤
      (1 + ε₀ / 16) ^ 2 := by
    rw [sq]
    exact mul_le_mul (hA_ub.trans h16_ub) hB_ub hB_nn (by positivity)
  have hABC : (normNum m l a r * σm ^ l * (1 - q ^ l)) *
      (1 / (normDen l a r * (Real.sqrt l * (Real.sqrt (2 * Real.pi * r * (p * q))) ^ (l - 1)))) *
      (Real.sqrt (r / (θ * m))) ^ (l - 1) ≤ (1 + ε₀ / 16) ^ 3 := by
    rw [show (1 + ε₀ / 16) ^ 3 = (1 + ε₀ / 16) ^ 2 * (1 + ε₀ / 16) by ring]
    exact mul_le_mul hAB (hC_ub.trans h16_ub) (pow_nonneg (Real.sqrt_nonneg _) _) (by positivity)
  have hcube : (1 + ε₀ / 16) ^ 3 ≤ 1 + ε₀ / 2 := by
    have hid : (1 + ε₀ / 2) - (1 + ε₀ / 16) ^ 3 =
        (ε₀ / 16) * (5 - 3 * (ε₀ / 16) - (ε₀ / 16) ^ 2) := by ring
    have hsq : (ε₀ / 16) ^ 2 ≤ ε₀ / 16 := by
      rw [sq]
      exact (mul_le_mul_of_nonneg_left (by linarith [hε₀_le1] : ε₀ / 16 ≤ 1)
        (by positivity)).trans_eq (mul_one _)
    have hpos : 0 ≤ 5 - 3 * (ε₀ / 16) - (ε₀ / 16) ^ 2 := by linarith [hε₀_le1]
    have hmul := mul_nonneg (by positivity : 0 ≤ ε₀ / 16) hpos
    linarith
  exact hABC.trans hcube

private lemma main_upper_tail {m l r : ℕ} {a ε₀ δ ρ : ℝ}
    (hm_pos : 0 < m) (hl : 0 < l) (ha : 0 < a) (hrm : r ≤ m)
    (hρ_pos : 0 < ρ) (hmid_not : ¬ ((paramT a - δ) * m ≤ r ∧ (r : ℝ) ≤ (paramT a + δ) * m))
    (hρ₁ : ∀ m' i : ℕ, (i : ℝ) ≤ (paramT a - δ) * m' → binomP m' (paramT a) i ≤ ρ ^ m')
    (hρ₂ : ∀ m' i : ℕ, (paramT a + δ / 2) * m' ≤ i → binomP m' (paramT a) i ≤ ρ ^ m')
    (hρ₃ : Real.exp ((δ / 2) * Real.log (paramQ a)) ≤ ρ)
    (hpoly_small :
      ((1 - (paramQ a) ^ l) * (Real.sqrt (2 * Real.pi * (paramT a * (1 - paramT a))) + 1) ^ l /
          (Real.sqrt l * (Real.sqrt (2 * Real.pi * paramT a * (paramP a * paramQ a))) ^ (l - 1))) *
        (((m + 1 : ℝ) ^ (2 * l + 1)) * ρ ^ m) ≤ ε₀ / 2) :
    x m l a r / asymptotic m l a ≤ 1 + ε₀ / 2 := by
  have hp0 := paramP_pos ha
  have hq0 := paramQ_pos ha
  have hq1 := paramQ_lt_one ha
  have ht0 := paramT_pos ha
  have ht1 := paramT_lt_one ha
  have hm_rpos : (0 : ℝ) < m := by positivity
  let p : ℝ := paramP a
  let q : ℝ := paramQ a
  let θ : ℝ := paramT a
  let σm : ℝ := Real.sqrt (2 * Real.pi * m * (θ * (1 - θ)))
  let σr0 : ℝ := Real.sqrt (2 * Real.pi * (θ * m) * (p * q))
  have hσm_pos : 0 < σm := by
    have : 0 < 1 - θ := sub_pos.mpr ht1
    positivity
  have hql_lt1 : q ^ l < 1 := pow_lt_one₀ hq0.le hq1 hl.ne'
  have h1mql_pos : 0 < 1 - q ^ l := sub_pos.mpr hql_lt1
  let c_asym : ℝ := Real.sqrt l * (Real.sqrt (2 * Real.pi * θ * (p * q))) ^ (l - 1)
  have hc_asym_pos : 0 < c_asym := by positivity
  let C_asym : ℝ := (1 - q ^ l) * (Real.sqrt (2 * Real.pi * (θ * (1 - θ))) + 1) ^ l / c_asym
  have htail_norm : normNum m l a r ≤ (m + 1 : ℝ) * ρ ^ m := by
    have hterm_tail : ∀ i ∈ Finset.range (r + 1),
        binomP m θ i ^ l * q ^ ((r - i) * l) ≤ ρ ^ m := by
      intro i hi
      have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rcases not_and_or.mp hmid_not with hlo | hhi
      · have hlt : (r : ℝ) < (θ - δ) * m := lt_of_not_ge hlo
        have hi_le : (i : ℝ) ≤ (θ - δ) * m := by
          have : (i : ℝ) ≤ r := by exact_mod_cast hir
          linarith
        have hbi : binomP m θ i ≤ ρ ^ m := hρ₁ m i hi_le
        have hbi_pow : binomP m θ i ^ l ≤ binomP m θ i := by
          have hle1 : binomP m θ i ≤ 1 := binomP_le_one ht0.le ht1.le i
          have hnn : 0 ≤ binomP m θ i := binomP_nonneg ht0.le ht1.le i
          calc binomP m θ i ^ l ≤ binomP m θ i ^ 1 := pow_le_pow_of_le_one hnn hle1 hl
            _ = binomP m θ i := pow_one _
        have hq_le1 : q ^ ((r - i) * l) ≤ 1 := pow_le_one₀ hq0.le hq1.le
        calc binomP m θ i ^ l * q ^ ((r - i) * l)
            ≤ binomP m θ i ^ l * 1 := mul_le_mul_of_nonneg_left hq_le1 (pow_nonneg
              (binomP_nonneg ht0.le ht1.le i) l)
          _ = binomP m θ i ^ l := mul_one _
          _ ≤ binomP m θ i := hbi_pow
          _ ≤ ρ ^ m := hbi
      · have hgt : (θ + δ) * m < r := lt_of_not_ge hhi
        by_cases hsplit : (i : ℝ) ≤ (θ + δ / 2) * m
        · have hdiff : (δ / 2) * m ≤ ((r - i : ℕ) : ℝ) := by
            rw [Nat.cast_sub hir]
            linarith
          have hq_exp : q ^ ((r - i) * l) ≤ ρ ^ m := by
            have hq_le1 : q ^ ((r - i) * l) ≤ q ^ (r - i) :=
              pow_le_pow_of_le_one hq0.le hq1.le (Nat.le_mul_of_pos_right (r - i) hl)
            have hq_exp_eq : q ^ (r - i) = Real.exp (((r - i : ℕ) : ℝ) * Real.log q) := by
              rw [← Real.rpow_natCast q (r - i), Real.rpow_def_of_pos hq0]
              dsimp only [q]
              ring_nf
            have hρ₃_eq : (Real.exp ((δ / 2) * Real.log q)) ^ m =
                Real.exp (((δ / 2) * m) * Real.log q) := by
              rw [← Real.exp_nat_mul]
              ring_nf
            have hlog_neg : Real.log q < 0 := Real.log_neg hq0 hq1
            have hexp_le : Real.exp (((r - i : ℕ) : ℝ) * Real.log q) ≤
                (Real.exp ((δ / 2) * Real.log q)) ^ m := by
              rw [hρ₃_eq]
              exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hdiff hlog_neg.le)
            calc q ^ ((r - i) * l) ≤ q ^ (r - i) := hq_le1
              _ = Real.exp (((r - i : ℕ) : ℝ) * Real.log q) := hq_exp_eq
              _ ≤ (Real.exp ((δ / 2) * Real.log q)) ^ m := hexp_le
              _ ≤ ρ ^ m := pow_le_pow_left₀ (Real.exp_pos _).le hρ₃ m
          have hbi_le1 : binomP m θ i ^ l ≤ 1 :=
            pow_le_one₀ (binomP_nonneg ht0.le ht1.le i) (binomP_le_one ht0.le ht1.le i)
          calc binomP m θ i ^ l * q ^ ((r - i) * l)
              ≤ 1 * q ^ ((r - i) * l) :=
                mul_le_mul_of_nonneg_right hbi_le1 (pow_nonneg hq0.le _)
            _ = q ^ ((r - i) * l) := one_mul _
            _ ≤ ρ ^ m := hq_exp
        · have hi_ge : (θ + δ / 2) * m ≤ i := le_of_lt (lt_of_not_ge hsplit)
          have hbi : binomP m θ i ≤ ρ ^ m := hρ₂ m i hi_ge
          have hbi_pow : binomP m θ i ^ l ≤ binomP m θ i := by
            have hle1 : binomP m θ i ≤ 1 := binomP_le_one ht0.le ht1.le i
            have hnn : 0 ≤ binomP m θ i := binomP_nonneg ht0.le ht1.le i
            calc binomP m θ i ^ l ≤ binomP m θ i ^ 1 := pow_le_pow_of_le_one hnn hle1 hl
              _ = binomP m θ i := pow_one _
          have hq_le1 : q ^ ((r - i) * l) ≤ 1 := pow_le_one₀ hq0.le hq1.le
          calc binomP m θ i ^ l * q ^ ((r - i) * l)
              ≤ binomP m θ i ^ l * 1 := mul_le_mul_of_nonneg_left hq_le1 (pow_nonneg
                (binomP_nonneg ht0.le ht1.le i) l)
            _ = binomP m θ i ^ l := mul_one _
            _ ≤ binomP m θ i := hbi_pow
            _ ≤ ρ ^ m := hbi
    unfold normNum
    calc ∑ i ∈ Finset.range (r + 1), binomP m (paramT a) i ^ l * (paramQ a) ^ ((r - i) * l)
        ≤ ∑ _i ∈ Finset.range (r + 1), ρ ^ m := Finset.sum_le_sum hterm_tail
      _ = (r + 1 : ℝ) * ρ ^ m := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; rfl
      _ ≤ (m + 1 : ℝ) * ρ ^ m := by
          have : (r + 1 : ℝ) ≤ m + 1 := by exact_mod_cast Nat.add_le_add_right hrm 1
          exact mul_le_mul_of_nonneg_right this (pow_nonneg hρ_pos.le m)
  have hden_ub : 1 / normDen l a r ≤ (m + 1 : ℝ) ^ l := by
    have hpos : 0 < ((r + 1 : ℝ) ^ l)⁻¹ := by positivity
    have h1 : 1 / normDen l a r ≤ (r + 1 : ℝ) ^ l := by
      have := one_div_le_one_div_of_le hpos (normDen_ge_inv_pow hl ha r)
      simpa [one_div] using this
    have h2 : (r + 1 : ℝ) ^ l ≤ (m + 1 : ℝ) ^ l :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hrm 1) l
    exact h1.trans h2
  have hasym_inv_ub : 1 / asymNorm m l a ≤ C_asym * (m + 1 : ℝ) ^ l := by
    have hσm_ub : σm ≤ (Real.sqrt (2 * Real.pi * (θ * (1 - θ))) + 1) * (m + 1 : ℝ) := by
      have hsq : Real.sqrt (m : ℝ) ≤ m + 1 := by
        calc Real.sqrt (m : ℝ) ≤ Real.sqrt ((m + 1 : ℝ) ^ 2) :=
              Real.sqrt_le_sqrt (by
                have : (m + 1 : ℝ) ^ 2 = (m : ℝ) ^ 2 + 2 * m + 1 := by ring
                linarith [sq_nonneg (m : ℝ), hm_rpos])
          _ = m + 1 := Real.sqrt_sq (by positivity)
      have hσmeq : σm = Real.sqrt (2 * Real.pi * (θ * (1 - θ))) * Real.sqrt m := by
        dsimp only [σm]
        rw [show 2 * Real.pi * m * (θ * (1 - θ)) = (2 * Real.pi * (θ * (1 - θ))) * m by ring,
          Real.sqrt_mul (by
            have : 0 < 1 - θ := sub_pos.mpr ht1
            positivity)]
      rw [hσmeq]
      calc Real.sqrt (2 * Real.pi * (θ * (1 - θ))) * Real.sqrt m
          ≤ Real.sqrt (2 * Real.pi * (θ * (1 - θ))) * (m + 1 : ℝ) :=
            mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
        _ ≤ (Real.sqrt (2 * Real.pi * (θ * (1 - θ))) + 1) * (m + 1 : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hc_lb : c_asym ≤ Real.sqrt l * σr0 ^ (l - 1) := by
      dsimp only [c_asym, σr0]
      have h1 : 2 * Real.pi * θ * (p * q) ≤ 2 * Real.pi * (θ * m) * (p * q) := by
        have h1m : (1 : ℝ) ≤ m := by exact_mod_cast hm_pos
        calc 2 * Real.pi * θ * (p * q)
            = 2 * Real.pi * θ * (p * q) * 1 := (mul_one _).symm
          _ ≤ 2 * Real.pi * θ * (p * q) * m := mul_le_mul_of_nonneg_left h1m (by positivity)
          _ = 2 * Real.pi * (θ * m) * (p * q) := by ring
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt h1) (l - 1))
        (Real.sqrt_nonneg _)
    have h1asym : 1 / asymNorm m l a = (1 - q ^ l) * σm ^ l / (Real.sqrt l * σr0 ^ (l - 1)) := by
      have hhl_ne : (Real.sqrt l * σr0 ^ (l - 1)) ≠ 0 := by positivity
      dsimp only [asymNorm]
      change 1 / (((1 / σm) ^ l * (1 / (1 - q ^ l))) / (1 / (Real.sqrt l * σr0 ^ (l - 1)))) =
        (1 - q ^ l) * σm ^ l / (Real.sqrt l * σr0 ^ (l - 1))
      rw [div_pow, one_pow, div_div_eq_mul_div, div_eq_div_iff (by positivity) hhl_ne]
      rw [one_mul, one_div_mul_cancel hhl_ne]
      calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
        _ = ((1 - q ^ l) * (1 / (1 - q ^ l))) * (σm ^ l * (1 / σm ^ l)) := by
            rw [mul_one_div_cancel h1mql_pos.ne', mul_one_div_cancel (pow_ne_zero l hσm_pos.ne')]
        _ = (1 - q ^ l) * σm ^ l * (1 / σm ^ l * (1 / (1 - q ^ l))) := by ring
    rw [h1asym]
    have hnum : (1 - q ^ l) * σm ^ l ≤
        (1 - q ^ l) * ((Real.sqrt (2 * Real.pi * (θ * (1 - θ))) + 1) ^ l * (m + 1 : ℝ) ^ l) := by
      rw [← mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hσm_pos.le hσm_ub l) h1mql_pos.le
    calc (1 - q ^ l) * σm ^ l / (Real.sqrt l * σr0 ^ (l - 1))
        ≤ ((1 - q ^ l) * ((Real.sqrt (2 * Real.pi * (θ * (1 - θ))) + 1) ^ l *
            (m + 1 : ℝ) ^ l)) / c_asym := div_le_div₀ (by positivity) hnum hc_asym_pos hc_lb
      _ = C_asym * (m + 1 : ℝ) ^ l := by
          dsimp only [C_asym]; ring
  have hdiv_eq : x m l a r / asymptotic m l a =
      normNum m l a r * (1 / normDen l a r) * (1 / asymNorm m l a) := by
    rw [x_eq_normalized ha hl hrm, asymptotic_eq_normalized hm_pos hl ha]
    have hpow_ne : ((1 + 2 * a) / (1 + a)) ^ (m * l) ≠ 0 := by positivity
    field_simp
  have hnorm_nn : 0 ≤ normNum m l a r := by
    unfold normNum
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg (binomP_nonneg ht0.le ht1.le _) l)
      (pow_nonneg hq0.le _)
  have hden_pos : 0 < normDen l a r := lt_of_lt_of_le (by positivity) (normDen_ge_inv_pow hl ha r)
  have hden_nn : 0 ≤ 1 / normDen l a r := by positivity
  have hasym_inv_nn : 0 ≤ 1 / asymNorm m l a :=
    div_nonneg zero_le_one (asymNorm_pos hm_pos hl ha).le
  have hprod_bound : x m l a r / asymptotic m l a ≤
      C_asym * (((m + 1 : ℝ) ^ (2 * l + 1)) * ρ ^ m) := by
    rw [hdiv_eq]
    calc normNum m l a r * (1 / normDen l a r) * (1 / asymNorm m l a)
        ≤ ((m + 1 : ℝ) * ρ ^ m) * ((m + 1 : ℝ) ^ l) * (C_asym * (m + 1 : ℝ) ^ l) := by
          refine mul_le_mul (mul_le_mul htail_norm hden_ub hden_nn (by positivity))
            hasym_inv_ub hasym_inv_nn (by positivity)
      _ = C_asym * (((m + 1 : ℝ) ^ (2 * l + 1)) * ρ ^ m) := by
          rw [show 2 * l + 1 = 1 + l + l by omega, pow_add, pow_add, pow_one]
          ring
  linarith [hprod_bound, hpoly_small]

private theorem main_proof : OMA.R_arxiv_2604_14639_R1.H4 := by
  intro l hl a ha
  rw [Metric.tendsto_atTop]
  intro ε hε
  let ε₀ : ℝ := min ε 1
  have hε₀_pos : 0 < ε₀ := lt_min hε zero_lt_one
  have hε₀_le1 : ε₀ ≤ 1 := min_le_right _ _
  have hε₀_leε : ε₀ ≤ ε := min_le_left _ _
  have hp0 := paramP_pos ha
  have hp1 := paramP_lt_one ha
  have hq0 := paramQ_pos ha
  have hq1 := paramQ_lt_one ha
  have ht0 := paramT_pos ha
  have ht1 := paramT_lt_one ha
  let p : ℝ := paramP a
  let q : ℝ := paramQ a
  let θ : ℝ := paramT a
  let σθ : ℝ := Real.sqrt (θ * (1 - θ))
  have hσθ_pos : 0 < σθ := Real.sqrt_pos.mpr (mul_pos ht0 (sub_pos.mpr ht1))
  have hql_lt1 : q ^ l < 1 := pow_lt_one₀ hq0.le hq1 hl.ne'
  have hql_pos : 0 < q ^ l := pow_pos hq0 l
  have h1mql_pos : 0 < 1 - q ^ l := sub_pos.mpr hql_lt1
  let u : ℝ := min (ε₀ / (128 * l)) (1 / (16 * l))
  have hu_pos : 0 < u := by positivity
  have hlu16 : (l : ℝ) * u ≤ 1 / 16 := by
    have : u ≤ 1 / (16 * l) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hlu128 : (l : ℝ) * u ≤ ε₀ / 128 := by
    have : u ≤ ε₀ / (128 * l) := min_le_left _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hu_half : u ≤ 1 / 4 := by
    have h1 : u ≤ 1 / (16 * (l : ℝ)) := min_le_right _ _
    have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have h2 : 1 / (16 * (l : ℝ)) ≤ 1 / 16 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have h1u_pow : (1 + u) ^ l ≤ 1 + ε₀ / 32 := by
    have hexp1 : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have hexp2 : (1 + u) ^ l ≤ Real.exp ((l : ℝ) * u) := by
      calc (1 + u) ^ l ≤ (Real.exp u) ^ l := pow_le_pow_left₀ (by positivity) hexp1 l
        _ = Real.exp ((l : ℝ) * u) := by rw [← Real.exp_nat_mul]
    have h1 := abs_exp_sub_one_le_two_mul (by
      rw [abs_of_nonneg (show 0 ≤ (l : ℝ) * u by positivity)]; linarith [hlu16])
    rw [abs_of_nonneg (show 0 ≤ (l : ℝ) * u by positivity)] at h1
    linarith [(abs_le.mp h1).2, hlu128]
  have h1mu2_pow : 1 - ε₀ / 64 ≤ (1 - 2 * u) ^ l := by
    have h1u : 0 ≤ 1 - 2 * u := by linarith [hu_half]
    have hber : ∀ m : ℕ, 1 - (m : ℝ) * (2 * u) ≤ (1 - 2 * u) ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ k ih =>
        rw [pow_succ']
        push_cast
        have hmul := mul_le_mul_of_nonneg_left ih h1u
        have : (1 - 2 * u) * (1 - (k : ℝ) * (2 * u)) =
            1 - ((k : ℝ) + 1) * (2 * u) + (k : ℝ) * (2 * u) ^ 2 := by ring
        have hsq : 0 ≤ (k : ℝ) * (2 * u) ^ 2 := by positivity
        linarith
    linarith [hber l, hlu128]
  have h1mu_pow : 1 - ε₀ / 32 ≤ (1 - u) ^ l :=
    le_trans (by linarith [hε₀_pos])
      (h1mu2_pow.trans (pow_le_pow_left₀ (by linarith [hu_half]) (by linarith [hu_pos]) l))
  let δ : ℝ := min (θ / 2) (min ((1 - θ) / 2) (θ * u))
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt_θ : δ ≤ θ / 2 := min_le_left _ _
  have hδ_θu : δ ≤ θ * u := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hql_pos.le hql_lt1).eventually
      (ge_mem_nhds (by positivity : 0 < ε₀ / 32)))
  have hK_sum : (1 - ε₀ / 32) / (1 - q ^ l) ≤
      ∑ j ∈ Finset.range (K + 1), q ^ (j * l) := by
    have hgeo : ∑ j ∈ Finset.range (K + 1), (q ^ l) ^ j =
        (1 - (q ^ l) ^ (K + 1)) / (1 - q ^ l) := by
      have := geom_sum_mul (q ^ l) (K + 1)
      have hsub : (∑ j ∈ Finset.range (K + 1), (q ^ l) ^ j) * (1 - q ^ l) =
          1 - (q ^ l) ^ (K + 1) := by linarith
      exact eq_div_of_mul_eq h1mql_pos.ne' hsub
    have hpow_le : (q ^ l) ^ (K + 1) ≤ ε₀ / 32 := hK (K + 1) (Nat.le_succ K)
    calc (1 - ε₀ / 32) / (1 - q ^ l)
        ≤ (1 - (q ^ l) ^ (K + 1)) / (1 - q ^ l) := by gcongr
      _ = ∑ j ∈ Finset.range (K + 1), (q ^ l) ^ j := hgeo.symm
      _ = ∑ j ∈ Finset.range (K + 1), q ^ (j * l) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← pow_mul, mul_comm j l]
  obtain ⟨N₁, hN₁⟩ := binom_stirling_unif ht0 ht1 (M := 1) (ε := u) zero_lt_one hu_pos
  obtain ⟨N_den, hN_den⟩ := Metric.tendsto_atTop.mp (tendsto_normDen hl ha) (ε₀ / 32)
    (by positivity)
  obtain ⟨ρ₁, hρ₁_pos, hρ₁_lt1, hρ₁⟩ := binomP_lower_tail ht0 ht1 hδ_pos
  obtain ⟨ρ₂, hρ₂_pos, hρ₂_lt1, hρ₂⟩ := binomP_upper_tail ht0 ht1 (by positivity : 0 < δ / 2)
  let ρ₃ : ℝ := Real.exp ((δ / 2) * Real.log q)
  have hρ₃_pos : 0 < ρ₃ := Real.exp_pos _
  have hρ₃_lt1 : ρ₃ < 1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_pos_of_neg (by positivity) (Real.log_neg hq0 hq1))
  let ρ : ℝ := max ρ₁ (max ρ₂ ρ₃)
  have hρ_pos : 0 < ρ := lt_max_of_lt_left hρ₁_pos
  have hρ_lt1 : ρ < 1 := max_lt hρ₁_lt1 (max_lt hρ₂_lt1 hρ₃_lt1)
  let c_asym : ℝ := Real.sqrt l * (Real.sqrt (2 * Real.pi * θ * (p * q))) ^ (l - 1)
  let C_asym : ℝ := (1 - q ^ l) * (Real.sqrt (2 * Real.pi * (θ * (1 - θ))) + 1) ^ l / c_asym
  have hpoly_tend : Tendsto (fun m : ℕ => C_asym * (((m + 1 : ℝ) ^ (2 * l + 1)) * ρ ^ m))
      atTop (𝓝 0) := by
    simpa using (tendsto_poly_mul_pow_zero (2 * l + 1) hρ_pos.le hρ_lt1).const_mul C_asym
  obtain ⟨N_poly, hN_poly⟩ := eventually_atTop.mp
    (hpoly_tend.eventually (ge_mem_nhds (by positivity : 0 < ε₀ / 2)))
  let M_req : ℝ := max (max ((K + 1 : ℝ) / θ + 2) ((K + 1 : ℝ) / σθ + 2))
    (max (max ((K + 1 : ℝ) ^ 2 / (2 * u * σθ ^ 2) + 2) (1 / (θ * u) + 2))
      (max (N_den / (θ - δ) + 2) (2 / δ + 2)))
  let B_m : ℝ := max M_req (Real.sqrt M_req + 2)
  obtain ⟨N_sq, hN_sq⟩ := eventually_atTop.mp
    ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B_m)
  let M_cut : ℕ := max N₁ (max N_poly (max N_sq 4))
  refine ⟨M_cut, fun m hm => ?_⟩
  have hmN1 : N₁ ≤ m := (le_max_left _ _).trans hm
  have hmPoly : N_poly ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hmSq : N_sq ≤ m :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  have hm4 : 4 ≤ m :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hm))
  have hm_pos : 0 < m := by omega
  have hm_rpos : (0 : ℝ) < m := by positivity
  have hasym_pos : 0 < asymptotic m l a := by
    rw [asymptotic_eq_normalized hm_pos hl ha]
    have : 0 < (1 + 2 * a) / (1 + a) := by positivity
    exact mul_pos (pow_pos this _) (asymNorm_pos hm_pos hl ha)
  have hBm : B_m ≤ Real.sqrt m := hN_sq m hmSq
  have hMreq_sq : M_req ≤ Real.sqrt m := (le_max_left _ _).trans hBm
  have h1_le_sqm : 1 ≤ Real.sqrt m := by
    calc (1 : ℝ) ≤ Real.sqrt 4 := by norm_num
      _ ≤ Real.sqrt m := Real.sqrt_le_sqrt (by exact_mod_cast hm4)
  have hMreq_m : M_req ≤ m := by
    calc M_req ≤ Real.sqrt m := hMreq_sq
      _ = Real.sqrt m * 1 := (mul_one _).symm
      _ ≤ Real.sqrt m * Real.sqrt m := mul_le_mul_of_nonneg_left h1_le_sqm (by positivity)
      _ = m := Real.mul_self_sqrt hm_rpos.le
  have hK_θm : (K + 1 : ℝ) / θ ≤ m := by
    have h1 := (le_max_left _ _).trans ((le_max_left _ _).trans hMreq_m)
    linarith
  have hK_σm : (K + 1 : ℝ) / σθ ≤ Real.sqrt m := by
    have h1 := (le_max_right _ _).trans ((le_max_left _ _).trans hMreq_sq)
    linarith
  have hK_u : (K + 1 : ℝ) ^ 2 / (2 * u * σθ ^ 2) ≤ m := by
    have h1 := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hMreq_m))
    linarith
  have h1_θu : 1 / (θ * u) ≤ m := by
    have h1 := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hMreq_m))
    linarith
  have hNden_m : N_den / (θ - δ) ≤ m := by
    have h1 := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hMreq_m))
    linarith
  have hδ_m : 2 / δ ≤ m := by
    have h1 := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hMreq_m))
    linarith
  have h2_le_δm : 2 ≤ δ * m := by linarith [(div_le_iff₀ hδ_pos).mp hδ_m]
  let r₀ : ℕ := ⌊θ * m⌋₊
  have hr₀_le_m : r₀ ≤ m := by
    have h1 : (r₀ : ℝ) ≤ θ * m := Nat.floor_le (by positivity)
    have h2 : θ * m < m := mul_lt_of_lt_one_left hm_rpos ht1
    exact_mod_cast h1.trans h2.le
  have hK_le_r₀ : K ≤ r₀ := by
    have h1 : (K + 1 : ℝ) ≤ θ * m := by linarith [(div_le_iff₀ ht0).mp hK_θm]
    have h2 : θ * m < (r₀ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : (K : ℝ) < (r₀ : ℝ) := by linarith
    exact_mod_cast h3.le
  have hr₀_ge_band : (θ - δ) * m ≤ r₀ := by
    have h2 : θ * m < (r₀ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hsub : (θ - δ) * m ≤ θ * m - 2 := by
      have : (θ - δ) * m = θ * m - δ * m := by ring
      linarith [h2_le_δm]
    linarith [hsub, h2]
  have hr₀_pos : 0 < r₀ := by
    have : 0 < (θ - δ) * m := mul_pos (by linarith [hδ_lt_θ]) hm_rpos
    have : (0 : ℝ) < r₀ := lt_of_lt_of_le this hr₀_ge_band
    exact_mod_cast this
  have hNden_le_r₀ : N_den ≤ r₀ := by
    have h1 : (N_den : ℝ) ≤ (θ - δ) * m := by
      linarith [(div_le_iff₀ (by linarith [hδ_lt_θ])).mp hNden_m]
    exact_mod_cast h1.trans hr₀_ge_band
  have h_lower : 1 - ε₀ / 2 ≤ maxValue m l a / asymptotic m l a := by
    have hxr_le_max : x m l a r₀ / asymptotic m l a ≤ maxValue m l a / asymptotic m l a := by
      apply div_le_div_of_nonneg_right _ hasym_pos.le
      exact Finset.le_sup' (x m l a) (Finset.mem_range.mpr (Nat.lt_succ_of_le hr₀_le_m))
    exact (main_lower_bound hm_pos hl ha hr₀_pos hr₀_le_m hK_le_r₀ hNden_le_r₀ hmN1
      hε₀_pos hε₀_le1 hu_pos hu_half h1mu_pow h1mu2_pow hK_sum hK_σm hK_u h1_θu rfl
      hN₁ hN_den).trans hxr_le_max
  have h_upper_all : ∀ r ∈ Finset.range (m + 1),
      x m l a r / asymptotic m l a ≤ 1 + ε₀ / 2 := by
    intro r hr
    have hrm : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    by_cases hmid : (θ - δ) * m ≤ r ∧ (r : ℝ) ≤ (θ + δ) * m
    · exact main_upper_mid hm_pos hl ha hrm hmN1 hε₀_pos hε₀_le1 hu_pos hδ_pos hδ_lt_θ hδ_θu
        h1u_pow hK_σm hNden_m hmid hN₁ hN_den
    · exact main_upper_tail hm_pos hl ha hrm hρ_pos hmid
        (fun m' i hi => (hρ₁ m' i hi).trans (pow_le_pow_left₀ hρ₁_pos.le (le_max_left _ _) m'))
        (fun m' i hi => (hρ₂ m' i hi).trans
          (pow_le_pow_left₀ hρ₂_pos.le ((le_max_left _ _).trans (le_max_right _ _)) m'))
        ((le_max_right _ _).trans (le_max_right _ _)) (hN_poly m hmPoly)
  have h_upper : maxValue m l a / asymptotic m l a ≤ 1 + ε₀ / 2 := by
    rw [div_le_iff₀ hasym_pos]
    unfold maxValue
    refine Finset.sup'_le _ _ fun r hr => ?_
    exact (div_le_iff₀ hasym_pos).mp (h_upper_all r hr)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hε₀_pos, hε₀_leε]

end OMA.Arxiv2604H4

theorem OMA.solution : OMA.R_arxiv_2604_14639_R1.H4 := OMA.Arxiv2604H4.main_proof

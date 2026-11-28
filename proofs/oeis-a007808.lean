import OMAStatements.S_oeis_a007808
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

open scoped BigOperators

namespace OMA.P_oeis_a007808

open OMA.S_oeis_a007808

/-! ### Exact closed-form formula `a(n) / n! = n * (∑_{k=0}^n 1/k! - 2) + 1/n!` for `n ≥ 1` -/

private noncomputable def partialExp (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (k.factorial : ℝ)

private lemma partialExp_succ (n : ℕ) :
    partialExp (n + 1) = partialExp n + 1 / ((n + 1).factorial : ℝ) := by
  unfold partialExp
  rw [Finset.sum_range_succ]

private lemma a007808_closed_form :
    ∀ n : ℕ, 1 ≤ n →
      (a007808 n : ℝ) = (n.factorial : ℝ) * (n : ℝ) * (partialExp n - 2) + 1 := by
  have hboth : ∀ n : ℕ, 1 ≤ n →
      (a007808 n : ℝ) = (n.factorial : ℝ) * (n : ℝ) * (partialExp n - 2) + 1 ∧
      (∑ j ∈ Finset.Icc 1 n, (a007808 j : ℝ)) =
        ((n + 1).factorial : ℝ) * (partialExp n - 2) + 1 := by
    intro n hn
    induction n with
    | zero => omega
    | succ k ih =>
      cases k with
      | zero =>
        constructor
        · simp [a007808, partialExp, Finset.sum_range_succ, Nat.factorial]; norm_num
        · simp [a007808, partialExp, Finset.sum_range_succ, Nat.factorial]; norm_num
      | succ m =>
        obtain ⟨iha, ihs⟩ := ih (by omega)
        have hrec : (a007808 (m + 2) : ℝ) =
            ((m + 2 : ℕ) : ℝ) * (a007808 (m + 1) : ℝ) + ∑ j ∈ Finset.Icc 1 (m + 1), (a007808 j : ℝ) := by
          have hsum_fin : (∑ j : Fin (m + 1), a007808 (j.val + 1)) =
              ∑ j ∈ Finset.Icc 1 (m + 1), a007808 j := by
            refine Finset.sum_bij (fun j _ => j.val + 1) ?_ ?_ ?_ ?_
            · intro j _
              simp only [Finset.mem_Icc]
              have := j.isLt; omega
            · intro j₁ _ j₂ _ h
              ext; omega
            · intro b hb
              simp only [Finset.mem_Icc] at hb
              exact ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
            · intro _ _; rfl
          have hnat : a007808 (m + 2) = (m + 2) * a007808 (m + 1) + ∑ j ∈ Finset.Icc 1 (m + 1), a007808 j := by
            rw [a007808, hsum_fin]
          exact_mod_cast hnat
        have ha_new : (a007808 (m + 2) : ℝ) =
            ((m + 2).factorial : ℝ) * ((m + 2 : ℕ) : ℝ) * (partialExp (m + 2) - 2) + 1 := by
          rw [hrec, iha, ihs, partialExp_succ (m + 1)]
          have hf : ((m + 2).factorial : ℝ) = ((m + 2 : ℕ) : ℝ) * ((m + 1).factorial : ℝ) := by
            exact_mod_cast Nat.factorial_succ (m + 1)
          have hfnz : ((m + 2).factorial : ℝ) ≠ 0 := by positivity
          have hf1nz : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
          rw [hf]
          field_simp
          push_cast
          ring
        refine ⟨ha_new, ?_⟩
        have hIcc : Finset.Icc 1 (m + 2) = insert (m + 2) (Finset.Icc 1 (m + 1)) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp), ha_new, ihs]
        have hf2 : ((m + 2).factorial : ℝ) = ((m + 2 : ℕ) : ℝ) * ((m + 1).factorial : ℝ) := by
          exact_mod_cast Nat.factorial_succ (m + 1)
        have hf3 : ((m + 3).factorial : ℝ) = ((m + 3 : ℕ) : ℝ) * ((m + 2).factorial : ℝ) := by
          exact_mod_cast Nat.factorial_succ (m + 2)
        have hpe : partialExp (m + 2) = partialExp (m + 1) + 1 / ((m + 2).factorial : ℝ) :=
          partialExp_succ (m + 1)
        rw [hf3, hpe]
        have hfnz : ((m + 2).factorial : ℝ) ≠ 0 := by positivity
        field_simp
        push_cast
        ring
  exact fun n hn => (hboth n hn).1

/-! ### Part 1: `round(n! * n * (e - 2)) = a(n)` for `n ≥ 1` -/

private lemma exp_one_sub_partialExp_bounds (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n + 1).factorial : ℝ) < Real.exp 1 - partialExp n ∧
    Real.exp 1 - partialExp n ≤ ((n + 2 : ℝ) / (n + 1 : ℝ)) * (1 / ((n + 1).factorial : ℝ)) := by
  have hexp : HasSum (fun k : ℕ => (1 : ℝ) / (k.factorial : ℝ)) (Real.exp 1) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (1 : ℝ)
    simpa [Real.exp_eq_exp_ℝ] using h
  have hshift : HasSum (fun j : ℕ => (1 : ℝ) / ((n + 1 + j).factorial : ℝ))
      (Real.exp 1 - partialExp n) := by
    have hexp' : HasSum (fun k : ℕ => (1 : ℝ) / (k.factorial : ℝ))
        ((Real.exp 1 - partialExp n) + ∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (i.factorial : ℝ)) := by
      simpa [partialExp] using hexp
    exact ((hasSum_nat_add_iff (n + 1)).mpr hexp').congr_fun (fun j => by rw [Nat.add_comm])
  constructor
  · have h01 : (1 : ℝ) / ((n + 1).factorial : ℝ) <
        ∑ j ∈ Finset.range 2, (1 : ℝ) / ((n + 1 + j).factorial : ℝ) := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      have hpos : (0 : ℝ) < 1 / ((n + 1 + 1).factorial : ℝ) := by positivity
      linarith
    have hle : ∑ j ∈ Finset.range 2, (1 : ℝ) / ((n + 1 + j).factorial : ℝ) ≤
        Real.exp 1 - partialExp n :=
      sum_le_hasSum (Finset.range 2) (fun _ _ => by positivity) hshift
    linarith
  · have hterm : ∀ j : ℕ, (1 : ℝ) / ((n + 1 + j).factorial : ℝ) ≤
        (1 / ((n + 1).factorial : ℝ)) * ((1 : ℝ) / (n + 2 : ℝ)) ^ j := by
      intro j
      have hfac : ((n + 1).factorial : ℝ) * (n + 2 : ℝ) ^ j ≤ ((n + 1 + j).factorial : ℝ) := by
        induction j with
        | zero => simp
        | succ m ihm =>
          rw [pow_succ, ← mul_assoc]
          conv_rhs => rw [show n + 1 + (m + 1) = (n + 1 + m) + 1 by omega, Nat.factorial_succ, Nat.cast_mul]
          have hle : (n + 2 : ℝ) ≤ ((n + 1 + m + 1 : ℕ) : ℝ) := by push_cast; linarith
          calc ((n + 1).factorial : ℝ) * (n + 2 : ℝ) ^ m * (n + 2 : ℝ)
              ≤ ((n + 1 + m).factorial : ℝ) * (n + 2 : ℝ) :=
                mul_le_mul_of_nonneg_right ihm (by positivity)
            _ ≤ ((n + 1 + m).factorial : ℝ) * ((n + 1 + m + 1 : ℕ) : ℝ) :=
                mul_le_mul_of_nonneg_left hle (by positivity)
            _ = ((n + 1 + m + 1 : ℕ) : ℝ) * ((n + 1 + m).factorial : ℝ) := mul_comm _ _
      rw [one_div_pow, one_div_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hgeom : HasSum (fun j : ℕ => (1 / ((n + 1).factorial : ℝ)) * ((1 : ℝ) / (n + 2 : ℝ)) ^ j)
        ((1 / ((n + 1).factorial : ℝ)) * (1 - 1 / (n + 2 : ℝ))⁻¹) := by
      have hg := hasSum_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / (n + 2 : ℝ))
        (by rw [div_lt_one (by positivity)]; linarith)
      exact hg.mul_left _
    have hle := hasSum_le hterm hshift hgeom
    have hval : (1 / ((n + 1).factorial : ℝ)) * (1 - 1 / (n + 2 : ℝ))⁻¹ =
        ((n + 2 : ℝ) / (n + 1 : ℝ)) * (1 / ((n + 1).factorial : ℝ)) := by
      have h1 : (n + 2 : ℝ) ≠ 0 := by positivity
      have h1m : 1 - 1 / (n + 2 : ℝ) = (n + 1 : ℝ) / (n + 2 : ℝ) := by
        field_simp; ring
      rw [h1m, inv_div]; ring
    linarith

private lemma round_formula (n : ℕ) (hn : 1 ≤ n) :
    round ((n.factorial : ℝ) * (n : ℝ) * (Real.exp 1 - 2)) = (a007808 n : ℤ) := by
  have hcl := a007808_closed_form n hn
  obtain ⟨hlo, hhi⟩ := exp_one_sub_partialExp_bounds n hn
  have hdiff : (n.factorial : ℝ) * (n : ℝ) * (Real.exp 1 - 2) - (a007808 n : ℝ) =
      (n.factorial : ℝ) * (n : ℝ) * (Real.exp 1 - partialExp n) - 1 := by
    rw [hcl]; ring
  have hfac : ((n + 1).factorial : ℝ) = ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ n
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hf_pos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hlow_term : (n : ℝ) / ((n : ℝ) + 1) < (n.factorial : ℝ) * (n : ℝ) * (Real.exp 1 - partialExp n) := by
    have h1 := mul_lt_mul_of_pos_left hlo (mul_pos hf_pos hn_pos)
    have heq : (n.factorial : ℝ) * (n : ℝ) * (1 / ((n + 1).factorial : ℝ)) = (n : ℝ) / ((n : ℝ) + 1) := by
      rw [hfac]; push_cast; field_simp
    linarith
  have hhigh_term : (n.factorial : ℝ) * (n : ℝ) * (Real.exp 1 - partialExp n) ≤
      (n : ℝ) * ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hhi (mul_pos hf_pos hn_pos).le
    have heq : (n.factorial : ℝ) * (n : ℝ) * (((n + 2 : ℝ) / (n + 1 : ℝ)) * (1 / ((n + 1).factorial : ℝ))) =
        (n : ℝ) * ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2 := by
      rw [hfac]; push_cast; field_simp
    linarith
  have hlt1 : (n : ℝ) * ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  have hgt_half : (1 : ℝ) / 2 < (n.factorial : ℝ) * (n : ℝ) * (Real.exp 1 - partialExp n) := by
    by_cases hn1 : n = 1
    · subst hn1
      have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
      have hpe1 : partialExp 1 = 2 := by simp [partialExp, Finset.sum_range_succ, Nat.factorial]; norm_num
      rw [hpe1]; norm_num; linarith
    · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
      have h23 : (1 : ℝ) / 2 < (n : ℝ) / ((n : ℝ) + 1) := by
        rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; linarith
      linarith
  rw [round_eq]
  have hfl : ⌊(n.factorial : ℝ) * (n : ℝ) * (Real.exp 1 - 2) + 1 / 2⌋ = (a007808 n : ℤ) := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  exact hfl

/-! ### Part 2: E.g.f. `∑ a(n)/n! * x^n = 1 + (-(x^2 + 1) * exp(-x) + 1) * exp(x) / (-1 + x)^2` -/

private lemma egf_formula (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => (a007808 n : ℝ) / (n.factorial : ℝ) * x ^ n)
      (1 + (-(x ^ 2 + 1) * Real.exp (-x) + 1) * Real.exp x / (-1 + x) ^ 2) := by
  have h1mx_ne : 1 - x ≠ 0 := by
    have := abs_lt.mp hx; linarith
  have htarget : 1 + (-(x ^ 2 + 1) * Real.exp (-x) + 1) * Real.exp x / (-1 + x) ^ 2 =
      Real.exp x * (1 / (1 - x) ^ 2) - (1 + x ^ 2) * (1 / (1 - x) ^ 2) + 1 := by
    have hexp_inv : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hsq : (-1 + x) ^ 2 = (1 - x) ^ 2 := by ring
    rw [hsq]
    have hne : (1 - x) ^ 2 ≠ 0 := pow_ne_zero 2 h1mx_ne
    field_simp
    calc _ = (1 - x) ^ 2 - (x ^ 2 + 1) * (Real.exp (-x) * Real.exp x) + Real.exp x := by ring
      _ = (1 - x) ^ 2 - (x ^ 2 + 1) * 1 + Real.exp x := by rw [hexp_inv]
      _ = Real.exp x - (1 + x ^ 2) + (1 - x) ^ 2 := by ring
  rw [htarget]
  have hCauchyMul : ∀ {f g : ℕ → ℝ} {a b : ℝ},
      Summable (fun k => ‖f k‖) → Summable (fun k => ‖g k‖) →
      HasSum f a → HasSum g b →
      HasSum (fun n => ∑ p ∈ Finset.antidiagonal n, f p.1 * g p.2) (a * b) := by
    intro f g a b hf_abs hg_abs hf hg
    have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hf_abs hg_abs).of_norm
    have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf_abs hg_abs
    rw [hf.tsum_eq, hg.tsum_eq] at heq
    rw [heq]
    exact hs.hasSum
  have hExp : HasSum (fun k : ℕ => x ^ k / (k.factorial : ℝ)) (Real.exp x) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
    simpa [Real.exp_eq_exp_ℝ] using h
  have hExp_summable : Summable (fun k : ℕ => ‖x ^ k / (k.factorial : ℝ)‖) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) |x|).summable
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) h
    have hkf : |(k.factorial : ℝ)| = (k.factorial : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
    rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, hkf]
  have hGeom : HasSum (fun k : ℕ => x ^ k) (1 - x)⁻¹ := hasSum_geometric_of_abs_lt_one hx
  have hGeom_abs : Summable (fun k : ℕ => ‖x ^ k‖) := by
    have h := (hasSum_geometric_of_lt_one (abs_nonneg x) hx).summable
    simpa [norm_pow, Real.norm_eq_abs] using h
  have hInvSq : HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * x ^ k) (1 / (1 - x) ^ 2) := by
    have hprod := hCauchyMul hGeom_abs hGeom_abs hGeom hGeom
    have hsum_eq : ∀ n : ℕ, ∑ p ∈ Finset.antidiagonal n, x ^ p.1 * x ^ p.2 = ((n + 1 : ℕ) : ℝ) * x ^ n := by
      intro n
      have h1 : ∀ p ∈ Finset.antidiagonal n, x ^ p.1 * x ^ p.2 = x ^ n := by
        rintro ⟨a, b⟩ hab
        rw [Finset.mem_antidiagonal] at hab
        rw [← pow_add, hab]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    simp only [hsum_eq] at hprod
    have hval : (1 - x)⁻¹ * (1 - x)⁻¹ = 1 / (1 - x) ^ 2 := by field_simp
    rwa [hval] at hprod
  have hInvSq_abs : Summable (fun k : ℕ => ‖((k + 1 : ℕ) : ℝ) * x ^ k‖) := by
    have hga := hasSum_geometric_of_lt_one (abs_nonneg x) hx
    have hga_n : Summable (fun k : ℕ => ‖|x| ^ k‖) := by
      simpa [Real.norm_eq_abs, abs_pow, abs_abs] using hga.summable
    have hp := (hCauchyMul hga_n hga_n hga hga).summable
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hp
    have h1 : ∑ p ∈ Finset.antidiagonal n, |x| ^ p.1 * |x| ^ p.2 = ((n + 1 : ℕ) : ℝ) * |x| ^ n := by
      have h2 : ∀ p ∈ Finset.antidiagonal n, |x| ^ p.1 * |x| ^ p.2 = |x| ^ n := by
        rintro ⟨a, b⟩ hab; rw [Finset.mem_antidiagonal] at hab; rw [← pow_add, hab]
      rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    rw [h1, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (n + 1))]
  have hCauchy := hCauchyMul hExp_summable hInvSq_abs hExp hInvSq
  have hCauchy_term : ∀ n : ℕ,
      (∑ p ∈ Finset.antidiagonal n, (x ^ p.1 / (p.1.factorial : ℝ)) * (((p.2 + 1 : ℕ) : ℝ) * x ^ p.2)) =
        (∑ k ∈ Finset.range (n + 1), ((n + 1 - k : ℕ) : ℝ) / (k.factorial : ℝ)) * x ^ n := by
    intro n
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => (x ^ a / (a.factorial : ℝ)) * (((b + 1 : ℕ) : ℝ) * x ^ b))]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hsub : n - k + 1 = n + 1 - k := by omega
    rw [hsub]
    have hpow : x ^ k * x ^ (n - k) = x ^ n := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
    calc (x ^ k / (k.factorial : ℝ)) * (((n + 1 - k : ℕ) : ℝ) * x ^ (n - k))
        = (((n + 1 - k : ℕ) : ℝ) / (k.factorial : ℝ)) * (x ^ k * x ^ (n - k)) := by ring
      _ = (((n + 1 - k : ℕ) : ℝ) / (k.factorial : ℝ)) * x ^ n := by rw [hpow]
  simp only [hCauchy_term] at hCauchy
  have hX2InvSq : HasSum (fun n : ℕ => (if 2 ≤ n then ((n - 1 : ℕ) : ℝ) else 0) * x ^ n)
      (x ^ 2 * (1 / (1 - x) ^ 2)) := by
    have h0 : ∑ i ∈ Finset.range 2, (if 2 ≤ i then ((i - 1 : ℕ) : ℝ) else 0) * x ^ i = 0 := by
      simp [Finset.sum_range_succ]
    rw [← hasSum_nat_add_iff' 2]
    rw [h0, sub_zero]
    have hmul := hInvSq.mul_left (x ^ 2)
    refine hmul.congr_fun (fun k => ?_)
    have hk2 : 2 ≤ k + 2 := by omega
    simp only [hk2, ite_true, show k + 2 - 1 = k + 1 by omega]
    rw [pow_add]; ring
  have hSubTerm : HasSum (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) + (if 2 ≤ n then ((n - 1 : ℕ) : ℝ) else 0)) * x ^ n)
      ((1 + x ^ 2) * (1 / (1 - x) ^ 2)) := by
    have hadd := hInvSq.add hX2InvSq
    have hrhs : 1 / (1 - x) ^ 2 + x ^ 2 * (1 / (1 - x) ^ 2) = (1 + x ^ 2) * (1 / (1 - x) ^ 2) := by ring
    rw [hrhs] at hadd
    exact hadd.congr_fun (fun n => by ring)
  have hOne : HasSum (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) 1 := hasSum_ite_eq 0 (1 : ℝ)
  have hAll := (hCauchy.sub hSubTerm).add hOne
  refine hAll.congr_fun (fun n => ?_)
  cases n with
  | zero =>
    simp [a007808]
  | succ m =>
    have hn1 : 1 ≤ m + 1 := by omega
    have hcl := a007808_closed_form (m + 1) hn1
    have hfac_nz : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
    have hsum_id : ∑ k ∈ Finset.range (m + 2), ((m + 2 - k : ℕ) : ℝ) / (k.factorial : ℝ) =
        ((m + 1 : ℕ) : ℝ) * partialExp (m + 1) + 1 / ((m + 1).factorial : ℝ) := by
      have h1 : ∑ k ∈ Finset.range (m + 2), ((m + 2 - k : ℕ) : ℝ) / (k.factorial : ℝ) =
          ((m + 2 : ℕ) : ℝ) * partialExp (m + 1) -
            ∑ k ∈ Finset.range (m + 2), (k : ℝ) / (k.factorial : ℝ) := by
        unfold partialExp
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        have hcast : ((m + 2 - k : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) - (k : ℝ) := by
          rw [Nat.cast_sub (by omega)]
        rw [hcast, sub_div, mul_one_div]
      have h2 : ∑ k ∈ Finset.range (m + 2), (k : ℝ) / (k.factorial : ℝ) = partialExp m := by
        rw [Finset.sum_range_succ']
        simp only [Nat.cast_zero, zero_div, add_zero]
        unfold partialExp
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.factorial_succ, Nat.cast_mul]
        have hkpos : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
      rw [h1, h2, partialExp_succ m]
      push_cast
      ring
    have hsub_val : (((m + 1 + 1 : ℕ) : ℝ) + (if 2 ≤ m + 1 then ((m + 1 - 1 : ℕ) : ℝ) else 0)) =
        2 * ((m + 1 : ℕ) : ℝ) := by
      cases m with
      | zero => norm_num
      | succ r =>
        simp only [show 2 ≤ r + 1 + 1 by omega, ite_true, show r + 1 + 1 - 1 = r + 1 by omega]
        push_cast; ring
    simp only [Nat.succ_ne_zero, ite_false, add_zero]
    rw [hsum_id, hsub_val, hcl]
    field_simp
    ring

private lemma prove_main :
    (∀ n : ℕ, 1 ≤ n → round ((n.factorial : ℝ) * (n : ℝ) * (Real.exp 1 - 2)) = (a007808 n : ℤ)) ∧
    (∀ x : ℝ, |x| < 1 →
      HasSum (fun n : ℕ => (a007808 n : ℝ) / (n.factorial : ℝ) * x ^ n)
        (1 + (-(x ^ 2 + 1) * Real.exp (-x) + 1) * Real.exp x / (-1 + x) ^ 2)) :=
  ⟨round_formula, egf_formula⟩

end OMA.P_oeis_a007808

theorem OMA.solution : type_of% @OMA.S_oeis_a007808.main :=
  OMA.P_oeis_a007808.prove_main

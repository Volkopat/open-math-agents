import OMAReductions.R_Green92_green_92_variants_chase_upper_R1
import Mathlib

/-!
# Amplification of the one-trace separation in Chase's upper bound

Chase, New upper bounds for trace reconstruction, Section 4,
https://arxiv.org/abs/2009.03296, separates a one-trace statistic from the
concentration of its repeated observations. This reduction proves the scale
conversion and gives a consistent orientation for all pairwise decisions.
-/

namespace OMA.R_Green92_green_92_variants_chase_upper_R1_H1_R1

open Filter Finset Green92
open scoped Topology Classical

private theorem exponent_budget {C n f : ℝ} (hn : 24 ≤ n)
    (hf : Real.log n ≤ f) {m : ℕ}
    (hm : Real.exp ((2*C+2)*f) ≤ (m : ℝ)) :
    Real.exp (-(m : ℝ)*(Real.exp (-C*f))^2/8) * (10 * Real.exp (n * Real.log 2)) ≤ 1 := by
  have hn0 : 0 < n := by linarith
  have hs : Real.exp ((2*C+2)*f) * (Real.exp (-C*f))^2 = Real.exp (2*f) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have ht : n^2 ≤ (m : ℝ) * (Real.exp (-C*f))^2 := calc
    n^2 = Real.exp (2 * Real.log n) := by rw [two_mul, Real.exp_add, Real.exp_log hn0, pow_two]
    _ ≤ Real.exp (2*f) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := hs ▸ mul_le_mul_of_nonneg_right hm (sq_nonneg _)
  have hlogs : Real.log 10 + n * Real.log 2 ≤ n^2/8 := by
    have h10 : Real.log 10 ≤ 10 := Real.log_le_self (by norm_num)
    have h2 : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
    have h2n := mul_le_mul_of_nonneg_left h2 hn0.le
    nlinarith [sq_nonneg (n-24)]
  have harg : -(m : ℝ)*(Real.exp (-C*f))^2/8 ≤ -(Real.log 10 + n*Real.log 2) := by
    linarith
  calc
    _ ≤ Real.exp (-(Real.log 10 + n*Real.log 2)) * (10 * Real.exp (n * Real.log 2)) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr harg) (by positivity)
    _ = 1 := by
      rw [Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 10)]
      exact inv_mul_cancel₀ (by positivity)

private theorem card_budget {a b d : ℕ} {s : ℝ} (hd : 0 < d)
    (ha : (a : ℝ) ≤ b * s) (hs : s * d ≤ 1) : a ≤ b / d := by
  apply (Nat.le_div_iff_mul_le hd).2
  have hh : (a : ℝ)*d ≤ b := calc
    _ ≤ ((b : ℝ)*s)*d := mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _)
    _ = (b : ℝ)*(s*d) := by ring
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
  exact_mod_cast hh

/-- The quantitative separation of one trace by a normalized real statistic. -/
def H1 : Prop := ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    let a := Real.exp (-C * ((n : ℝ)^(1/5 : ℝ) * Real.log n ^ 5))
    ∀ x y : Fin n → Bool, x ≠ y → ∃ F : List Bool → ℝ,
      (∀ w, 0 ≤ F w ∧ F w ≤ 1) ∧
      a * Fintype.card (Finset (Fin n)) ≤
        (∑ S : Finset (Fin n), F (trace x S)) - ∑ S : Finset (Fin n), F (trace y S)

/-- Finite concentration of bounded independent observations distinguishes two means. -/
def H2 : Prop := ∀ (n m : ℕ) (x y : Fin n → Bool) (F : List Bool → ℝ) (a : ℝ),
    0 < m → 0 < a → a ≤ 1 → (∀ w, 0 ≤ F w ∧ F w ≤ 1) →
    a * Fintype.card (Finset (Fin n)) ≤
      (∑ S : Finset (Fin n), F (trace x S)) - ∑ S : Finset (Fin n), F (trace y S) →
    ∃ T : (Fin m → List Bool) → Prop,
      let b := (Fintype.card (Fin m → Finset (Fin n)) : ℝ) * Real.exp (-(m:ℝ)*a^2/8)
      ((univ.filter fun S : Fin m → Finset (Fin n) => ¬T (fun i => trace x (S i))).card : ℝ) ≤ b ∧
      ((univ.filter fun S : Fin m → Finset (Fin n) => T (fun i => trace y (S i))).card : ℝ) ≤ b

theorem main : H1 → H2 → OMA.R_Green92_green_92_variants_chase_upper_R1.H1 := by
  rintro ⟨C,hC,hsep⟩ amplify
  let C' := 2*C+2
  refine ⟨C', by dsimp [C']; linarith, ?_⟩
  have hlogs : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hsep, hlogs, eventually_ge_atTop 24] with n hsep hlog hn
  let f := (n:ℝ)^(1/5:ℝ) * Real.log n ^ 5
  let a := Real.exp (-C*f)
  let m := ⌈Real.exp (C' * (n : ℝ) ^ (1/5 : ℝ) * Real.log n ^ 5)⌉₊
  let Z := Fintype.card (Fin m → Finset (Fin n))
  let s := Real.exp (-(m:ℝ)*a^2/8)
  let d : ℕ := 10 * 2^n
  have hd : 0 < d := by dsimp [d]; positivity
  have hnr : (24 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have h1 : (1 : ℝ) ≤ n := by linarith
  have hpow : 1 ≤ (n:ℝ)^(1/5:ℝ) := Real.one_le_rpow h1 (by norm_num)
  have hlogpow : Real.log (n : ℝ) ≤ Real.log n ^ 5 := by
    simpa using pow_le_pow_right₀ hlog (show 1 ≤ (5 : ℕ) by decide)
  have hf : Real.log (n : ℝ) ≤ f := hlogpow.trans (le_mul_of_one_le_left (by positivity) hpow)
  have hfn : 0 ≤ f := hlog0.trans hf
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC.le) hfn)
  have hmReal : Real.exp (C'*f) ≤ (m:ℝ) := by
    simpa only [f, ←mul_assoc] using (Nat.le_ceil (Real.exp (C' * (n : ℝ) ^ (1/5 : ℝ) * Real.log n ^ 5)))
  have hm : 0 < m := by exact_mod_cast (Real.exp_pos _ |>.trans_le hmReal)
  have hs : s * d ≤ 1 := by
    have hb := exponent_budget hnr hf hmReal
    have hexp : Real.exp ((n:ℝ) * Real.log 2) = (2:ℝ)^n := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
    simpa [s, a, d, hexp] using hb
  have htests (x y : Fin n → Bool) : ∃ T : (Fin m → List Bool) → Prop, x = y ∨
      (univ.filter fun S : Fin m → Finset (Fin n) => ¬T (fun i => trace x (S i))).card ≤ Z/d ∧
      (univ.filter fun S : Fin m → Finset (Fin n) => T (fun i => trace y (S i))).card ≤ Z/d := by
    by_cases hxy : x = y
    · exact ⟨fun _ => False, Or.inl hxy⟩
    obtain ⟨F,hF,hgap⟩ := hsep x y hxy
    obtain ⟨T,hTx,hTy⟩ := amplify n m x y F a hm ha ha1 hF hgap
    exact ⟨T, Or.inr ⟨card_budget hd hTx hs, card_budget hd hTy hs⟩⟩
  choose test htest using htests
  let rank := Fintype.equivFin (Fin n → Bool)
  let D (x y : Fin n → Bool) (o : Fin m → List Bool) : Prop :=
    if rank x < rank y then test x y o else ¬ test y x o
  refine ⟨D, ?_, ?_⟩
  · intro x y o hxy
    have hr : rank x ≠ rank y := fun h => hxy (rank.injective h)
    rcases lt_or_gt_of_ne hr with h | h
    · simp [D, h, not_lt_of_ge h.le]
    · simp [D, h, not_lt_of_ge h.le]
  · intro x y hxy
    have hr : rank x ≠ rank y := fun h => hxy (rank.injective h)
    rcases lt_or_gt_of_ne hr with h | h
    · simpa [D, h, Z, d, m] using ((htest x y).resolve_left hxy).1
    · simpa [D, not_lt_of_ge h.le, Z, d, m] using ((htest y x).resolve_left hxy.symm).2

end OMA.R_Green92_green_92_variants_chase_upper_R1_H1_R1

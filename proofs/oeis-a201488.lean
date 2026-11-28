import OMAStatements.S_oeis_a201488
import Mathlib

namespace OMA.S_oeis_a201488

private noncomputable def sgn (k : ℤ) : ℝ :=
  if Even k then 1 else -1

private lemma sgn_add (x y : ℤ) : sgn (x + y) = sgn x * sgn y := by
  unfold sgn
  rcases Int.even_or_odd x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases Int.even_or_odd y with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · have h1 : Even (a + a) := ⟨a, rfl⟩
    have h2 : Even (b + b) := ⟨b, rfl⟩
    have h3 : Even (a + a + (b + b)) := ⟨a + b, by ring⟩
    simp [h1, h2, h3]
  · have h1 : Even (a + a) := ⟨a, rfl⟩
    have h2 : ¬ Even (2 * b + 1) := Int.not_even_iff_odd.mpr ⟨b, rfl⟩
    have h3 : ¬ Even (a + a + (2 * b + 1)) := Int.not_even_iff_odd.mpr ⟨a + b, by ring⟩
    simp [h1, h2, h3]
  · have h1 : ¬ Even (2 * a + 1) := Int.not_even_iff_odd.mpr ⟨a, rfl⟩
    have h2 : Even (b + b) := ⟨b, rfl⟩
    have h3 : ¬ Even (2 * a + 1 + (b + b)) := Int.not_even_iff_odd.mpr ⟨a + b, by ring⟩
    simp [h1, h2, h3]
  · have h1 : ¬ Even (2 * a + 1) := Int.not_even_iff_odd.mpr ⟨a, rfl⟩
    have h2 : ¬ Even (2 * b + 1) := Int.not_even_iff_odd.mpr ⟨b, rfl⟩
    have h3 : Even (2 * a + 1 + (2 * b + 1)) := ⟨a + b + 1, by ring⟩
    simp [h1, h2, h3]

private lemma sgn_sub (x y : ℤ) : sgn (x - y) = sgn x * sgn y := by
  have h : x - y = x + (-y) := by ring
  rw [h, sgn_add]
  unfold sgn
  simp [even_neg]

private lemma abs_sgn (k : ℤ) : |sgn k| = 1 := by
  unfold sgn; split_ifs <;> norm_num

private noncomputable def T3 (a : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-Real.pi * a * (k : ℝ) ^ 2)

private noncomputable def T4 (a : ℝ) : ℝ :=
  ∑' k : ℤ, sgn k * Real.exp (-Real.pi * a * (k : ℝ) ^ 2)

private noncomputable def T2 (a : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-Real.pi * a * ((k : ℝ) + 1 / 2) ^ 2)

private lemma summable_exp_nat_sq {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℕ => Real.exp (-c * (n : ℝ) ^ 2) := by
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine (summable_geometric_of_lt_one hr0 hr1).of_nonneg_of_le
    (fun _ => (Real.exp_pos _).le) (fun n => ?_)
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hle : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
  nlinarith

private lemma summable_T3_norm {a : ℝ} (ha : 0 < a) :
    Summable fun k : ℤ => ‖Real.exp (-Real.pi * a * (k : ℝ) ^ 2)‖ := by
  have hc : 0 < Real.pi * a := mul_pos Real.pi_pos ha
  have hnat : Summable fun n : ℕ => Real.exp (-(Real.pi * a) * (n : ℝ) ^ 2) :=
    summable_exp_nat_sq hc
  refine summable_int_iff_summable_nat_and_neg.mpr ⟨?_, ?_⟩
  · refine hnat.congr fun n => ?_
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    congr 1; push_cast; ring
  · refine hnat.congr fun n => ?_
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    congr 1; push_cast; ring

private lemma summable_T4_norm {a : ℝ} (ha : 0 < a) :
    Summable fun k : ℤ => ‖sgn k * Real.exp (-Real.pi * a * (k : ℝ) ^ 2)‖ := by
  refine (summable_T3_norm ha).congr fun k => ?_
  simp only [norm_mul, Real.norm_eq_abs, abs_sgn, one_mul]

private lemma summable_T2_norm {a : ℝ} (ha : 0 < a) :
    Summable fun k : ℤ => ‖Real.exp (-Real.pi * a * ((k : ℝ) + 1 / 2) ^ 2)‖ := by
  have ha2 : 0 < a / 2 := half_pos ha
  refine ((summable_T3_norm ha2).mul_left (Real.exp (Real.pi * a / 4))).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun k => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq : ((k : ℝ) ^ 2) / 2 - 1 / 4 ≤ ((k : ℝ) + 1 / 2) ^ 2 := by
    nlinarith [sq_nonneg ((k : ℝ) + 1)]
  have hpi : 0 < Real.pi * a := mul_pos Real.pi_pos ha
  nlinarith

private def evenEquiv : ℤ × ℤ ≃ {p : ℤ × ℤ // Even (p.1 + p.2)} where
  toFun uv := ⟨(uv.1 + uv.2, uv.1 - uv.2), ⟨uv.1, by ring⟩⟩
  invFun p := ((p.1.1 + p.1.2) / 2, (p.1.1 - p.1.2) / 2)
  left_inv := fun ⟨u, v⟩ => by
    ext <;> dsimp <;> omega
  right_inv := fun ⟨⟨x, y⟩, ⟨m, hm⟩⟩ => by
    apply Subtype.ext
    ext <;> dsimp <;> omega

private def oddEquiv : ℤ × ℤ ≃ {p : ℤ × ℤ // ¬ Even (p.1 + p.2)} where
  toFun uv := ⟨(uv.1 + uv.2 + 1, uv.1 - uv.2),
    Int.not_even_iff_odd.mpr ⟨uv.1, by ring⟩⟩
  invFun p := ((p.1.1 + p.1.2 - 1) / 2, (p.1.1 - p.1.2 - 1) / 2)
  left_inv := fun ⟨u, v⟩ => by
    ext <;> dsimp <;> omega
  right_inv := fun ⟨⟨x, y⟩, hne⟩ => by
    obtain ⟨m, hm⟩ := Int.not_even_iff_odd.mp hne
    apply Subtype.ext
    ext <;> dsimp <;> omega

private lemma T3_sq_add_T4_sq {a : ℝ} (ha : 0 < a) :
    T3 a ^ 2 + T4 a ^ 2 = 2 * T3 (2 * a) ^ 2 := by
  have h3 := summable_T3_norm ha
  have h4 := summable_T4_norm ha
  have h3sq : T3 a ^ 2 = ∑' p : ℤ × ℤ, Real.exp (-Real.pi * a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    rw [sq, T3, tsum_mul_tsum_of_summable_norm h3 h3]
    congr 1; funext p; rw [← Real.exp_add]; congr 1; ring
  have h4sq : T4 a ^ 2 =
      ∑' p : ℤ × ℤ, sgn (p.1 + p.2) * Real.exp (-Real.pi * a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    rw [sq, T4, tsum_mul_tsum_of_summable_norm h4 h4]
    congr 1; funext p
    rw [show sgn p.1 * Real.exp (-Real.pi * a * (p.1 : ℝ) ^ 2) *
        (sgn p.2 * Real.exp (-Real.pi * a * (p.2 : ℝ) ^ 2)) =
        (sgn p.1 * sgn p.2) * (Real.exp (-Real.pi * a * (p.1 : ℝ) ^ 2) *
          Real.exp (-Real.pi * a * (p.2 : ℝ) ^ 2)) by ring]
    rw [← sgn_add, ← Real.exp_add]
    congr 2; ring
  have hs1 : Summable fun p : ℤ × ℤ => Real.exp (-Real.pi * a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    refine (summable_mul_of_summable_norm h3 h3).congr fun p => ?_
    rw [← Real.exp_add]; congr 1; ring
  have hs2 : Summable fun p : ℤ × ℤ =>
      sgn (p.1 + p.2) * Real.exp (-Real.pi * a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    refine (summable_mul_of_summable_norm h4 h4).congr fun p => ?_
    rw [show sgn p.1 * Real.exp (-Real.pi * a * (p.1 : ℝ) ^ 2) *
        (sgn p.2 * Real.exp (-Real.pi * a * (p.2 : ℝ) ^ 2)) =
        (sgn p.1 * sgn p.2) * (Real.exp (-Real.pi * a * (p.1 : ℝ) ^ 2) *
          Real.exp (-Real.pi * a * (p.2 : ℝ) ^ 2)) by ring]
    rw [← sgn_add, ← Real.exp_add]
    congr 2; ring
  rw [h3sq, h4sq, ← hs1.tsum_add hs2]
  have hcomb : (fun p : ℤ × ℤ =>
      Real.exp (-Real.pi * a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) +
      sgn (p.1 + p.2) * Real.exp (-Real.pi * a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) =
      fun p : ℤ × ℤ => if Even (p.1 + p.2) then
        2 * Real.exp (-Real.pi * a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) else 0 := by
    funext p; unfold sgn; split_ifs <;> ring
  rw [hcomb, ← tsum_subtype_eq_of_support_subset (s := {p : ℤ × ℤ | Even (p.1 + p.2)})]
  swap
  · intro p hp
    simp only [Function.mem_support, ne_eq, Set.mem_ofPred_eq] at hp ⊢
    by_contra h
    exact hp (if_neg h)
  change (∑' p : {p : ℤ × ℤ // Even (p.1 + p.2)},
      if Even (p.1.1 + p.1.2) then
        2 * Real.exp (-Real.pi * a * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2)) else 0) = _
  rw [← evenEquiv.tsum_eq]
  have h2a : 0 < 2 * a := by linarith
  have h32 := summable_T3_norm h2a
  rw [sq, T3, tsum_mul_tsum_of_summable_norm h32 h32, ← tsum_mul_left]
  congr 1; funext uv
  have hev : Even ((evenEquiv uv).1.1 + (evenEquiv uv).1.2) := (evenEquiv uv).2
  rw [if_pos hev]
  dsimp [evenEquiv]
  rw [← Real.exp_add]
  congr 2; push_cast; ring

private lemma T3_sq_sub_T4_sq {a : ℝ} (ha : 0 < a) :
    T3 a ^ 2 - T4 a ^ 2 = 2 * T2 (2 * a) ^ 2 := by
  have h3 := summable_T3_norm ha
  have h4 := summable_T4_norm ha
  have h3sq : T3 a ^ 2 = ∑' p : ℤ × ℤ, Real.exp (-Real.pi * a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    rw [sq, T3, tsum_mul_tsum_of_summable_norm h3 h3]
    congr 1; funext p; rw [← Real.exp_add]; congr 1; ring
  have h4sq : T4 a ^ 2 =
      ∑' p : ℤ × ℤ, sgn (p.1 + p.2) * Real.exp (-Real.pi * a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    rw [sq, T4, tsum_mul_tsum_of_summable_norm h4 h4]
    congr 1; funext p
    rw [show sgn p.1 * Real.exp (-Real.pi * a * (p.1 : ℝ) ^ 2) *
        (sgn p.2 * Real.exp (-Real.pi * a * (p.2 : ℝ) ^ 2)) =
        (sgn p.1 * sgn p.2) * (Real.exp (-Real.pi * a * (p.1 : ℝ) ^ 2) *
          Real.exp (-Real.pi * a * (p.2 : ℝ) ^ 2)) by ring]
    rw [← sgn_add, ← Real.exp_add]
    congr 2; ring
  have hs1 : Summable fun p : ℤ × ℤ => Real.exp (-Real.pi * a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    refine (summable_mul_of_summable_norm h3 h3).congr fun p => ?_
    rw [← Real.exp_add]; congr 1; ring
  have hs2 : Summable fun p : ℤ × ℤ =>
      sgn (p.1 + p.2) * Real.exp (-Real.pi * a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    refine (summable_mul_of_summable_norm h4 h4).congr fun p => ?_
    rw [show sgn p.1 * Real.exp (-Real.pi * a * (p.1 : ℝ) ^ 2) *
        (sgn p.2 * Real.exp (-Real.pi * a * (p.2 : ℝ) ^ 2)) =
        (sgn p.1 * sgn p.2) * (Real.exp (-Real.pi * a * (p.1 : ℝ) ^ 2) *
          Real.exp (-Real.pi * a * (p.2 : ℝ) ^ 2)) by ring]
    rw [← sgn_add, ← Real.exp_add]
    congr 2; ring
  rw [h3sq, h4sq, ← hs1.tsum_sub hs2]
  have hcomb : (fun p : ℤ × ℤ =>
      Real.exp (-Real.pi * a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) -
      sgn (p.1 + p.2) * Real.exp (-Real.pi * a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) =
      fun p : ℤ × ℤ => if ¬ Even (p.1 + p.2) then
        2 * Real.exp (-Real.pi * a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) else 0 := by
    funext p; unfold sgn; split_ifs <;> ring
  rw [hcomb, ← tsum_subtype_eq_of_support_subset (s := {p : ℤ × ℤ | ¬ Even (p.1 + p.2)})]
  swap
  · intro p hp
    simp only [Function.mem_support, ne_eq, Set.mem_ofPred_eq] at hp ⊢
    intro hev
    simp [hev] at hp
  change (∑' p : {p : ℤ × ℤ // ¬ Even (p.1 + p.2)},
      if ¬ Even (p.1.1 + p.1.2) then
        2 * Real.exp (-Real.pi * a * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2)) else 0) = _
  rw [← oddEquiv.tsum_eq]
  have h2a : 0 < 2 * a := by linarith
  have h22 := summable_T2_norm h2a
  rw [sq, T2, tsum_mul_tsum_of_summable_norm h22 h22, ← tsum_mul_left]
  congr 1; funext uv
  have hodd : ¬ Even ((oddEquiv uv).1.1 + (oddEquiv uv).1.2) := (oddEquiv uv).2
  rw [if_pos hodd]
  dsimp [oddEquiv]
  rw [← Real.exp_add]
  congr 2; push_cast; ring

private lemma T3_mul_T4 {a : ℝ} (ha : 0 < a) :
    T3 a * T4 a = T4 (2 * a) ^ 2 := by
  have h3 := summable_T3_norm ha
  have h4 := summable_T4_norm ha
  let F : ℤ × ℤ → ℝ := fun p => sgn p.2 * Real.exp (-Real.pi * a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))
  have hF_sum : Summable F := by
    refine (summable_mul_of_summable_norm h3 h4).congr fun p => ?_
    dsimp [F]
    rw [show Real.exp (-Real.pi * a * (p.1 : ℝ) ^ 2) *
        (sgn p.2 * Real.exp (-Real.pi * a * (p.2 : ℝ) ^ 2)) =
        sgn p.2 * (Real.exp (-Real.pi * a * (p.1 : ℝ) ^ 2) *
          Real.exp (-Real.pi * a * (p.2 : ℝ) ^ 2)) by ring]
    rw [← Real.exp_add]; congr 2; ring
  have hprod : T3 a * T4 a = ∑' p : ℤ × ℤ, F p := by
    rw [T3, T4, tsum_mul_tsum_of_summable_norm h3 h4]
    congr 1; funext p; dsimp [F]
    rw [show Real.exp (-Real.pi * a * (p.1 : ℝ) ^ 2) *
        (sgn p.2 * Real.exp (-Real.pi * a * (p.2 : ℝ) ^ 2)) =
        sgn p.2 * (Real.exp (-Real.pi * a * (p.1 : ℝ) ^ 2) *
          Real.exp (-Real.pi * a * (p.2 : ℝ) ^ 2)) by ring]
    rw [← Real.exp_add]; congr 2; ring
  rw [hprod]
  let E : Set (ℤ × ℤ) := {p | Even (p.1 + p.2)}
  have hsplit : ∑' p : ℤ × ℤ, F p = (∑' p : E, F p.1) + ∑' p : (Eᶜ : Set (ℤ × ℤ)), F p.1 := by
    exact ((hF_sum.subtype E).tsum_add_tsum_compl (hF_sum.subtype Eᶜ)).symm
  have hodd_zero : (∑' p : (Eᶜ : Set (ℤ × ℤ)), F p.1) = 0 := by
    let sw : (Eᶜ : Set (ℤ × ℤ)) ≃ (Eᶜ : Set (ℤ × ℤ)) :=
      { toFun := fun p => ⟨(p.1.2, p.1.1), by
          change ¬ Even (p.1.2 + p.1.1)
          rw [add_comm]
          exact p.2⟩
        invFun := fun p => ⟨(p.1.2, p.1.1), by
          change ¬ Even (p.1.2 + p.1.1)
          rw [add_comm]
          exact p.2⟩
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    have hneg : ∑' p : (Eᶜ : Set (ℤ × ℤ)), F p.1 = -(∑' p : (Eᶜ : Set (ℤ × ℤ)), F p.1) := by
      conv_lhs => rw [← sw.tsum_eq]
      rw [← tsum_neg]
      congr 1; funext ⟨⟨x, y⟩, hxy⟩
      dsimp [sw, F]
      have hs : sgn x = -sgn y := by
        have h1 : sgn (x + y) = -1 := if_neg hxy
        rw [sgn_add] at h1
        unfold sgn at h1 ⊢
        split_ifs at h1 ⊢ <;> linarith
      rw [hs, add_comm ((y : ℝ) ^ 2) ((x : ℝ) ^ 2)]
      ring
    linarith
  rw [hsplit, hodd_zero, add_zero]
  change (∑' p : {p : ℤ × ℤ // Even (p.1 + p.2)}, F p.1) = _
  rw [← evenEquiv.tsum_eq]
  have h2a : 0 < 2 * a := by linarith
  have h42 := summable_T4_norm h2a
  rw [sq, T4, tsum_mul_tsum_of_summable_norm h42 h42]
  congr 1; funext uv
  dsimp [evenEquiv, F]
  rw [sgn_sub]
  rw [show sgn uv.1 * Real.exp (-Real.pi * (2 * a) * (uv.1 : ℝ) ^ 2) *
      (sgn uv.2 * Real.exp (-Real.pi * (2 * a) * (uv.2 : ℝ) ^ 2)) =
      sgn uv.1 * sgn uv.2 * (Real.exp (-Real.pi * (2 * a) * (uv.1 : ℝ) ^ 2) *
        Real.exp (-Real.pi * (2 * a) * (uv.2 : ℝ) ^ 2)) by ring]
  rw [← Real.exp_add]
  congr 2; push_cast; ring

private lemma T3_half : T3 (1 / 2) = Real.sqrt 2 * T3 2 := by
  have h := Real.tsum_exp_neg_mul_int_sq (a := (1 / 2 : ℝ)) (by norm_num)
  have hsqrt : (1 : ℝ) / (1 / 2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow, one_div, one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
  rw [hsqrt] at h
  have hlhs : (∑' n : ℤ, Real.exp (-Real.pi * (1 / 2) * (n : ℝ) ^ 2)) = T3 (1 / 2) := rfl
  have hrhs : (∑' n : ℤ, Real.exp (-Real.pi / (1 / 2) * (n : ℝ) ^ 2)) = T3 2 := by
    unfold T3; congr 1; funext n; congr 1; ring
  rw [hlhs, hrhs] at h
  exact h

private lemma T4_half : T4 (1 / 2) = Real.sqrt 2 * T2 2 := by
  have ha : 0 < (1 / 2 : ℂ).re := by norm_num
  have h := Complex.tsum_exp_neg_quadratic ha (Complex.I / 2)
  have hlhs : (∑' n : ℤ, Complex.exp (-Real.pi * (1 / 2 : ℂ) * (n : ℂ) ^ 2 +
      2 * Real.pi * (Complex.I / 2) * (n : ℂ))) = (T4 (1 / 2) : ℂ) := by
    rw [T4, Complex.ofReal_tsum]
    congr 1; funext n
    rw [Complex.exp_add]
    have h1 : Complex.exp (2 * (Real.pi : ℂ) * (Complex.I / 2) * (n : ℂ)) = (sgn n : ℂ) := by
      have harg : 2 * (Real.pi : ℂ) * (Complex.I / 2) * (n : ℂ) = (n : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
        ring
      rw [harg, Complex.exp_int_mul, Complex.exp_pi_mul_I]
      unfold sgn
      rcases Int.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · have hev : Even (m + m) := ⟨m, rfl⟩
        rw [if_pos hev]
        push_cast
        rw [show (m + m : ℤ) = 2 * m by ring, zpow_mul, show (-1 : ℂ) ^ (2 : ℤ) = 1 by norm_num,
          one_zpow]
      · have hodd : ¬ Even (2 * m + 1) := Int.not_even_iff_odd.mpr ⟨m, rfl⟩
        rw [if_neg hodd]
        push_cast
        rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul,
          show (-1 : ℂ) ^ (2 : ℤ) = 1 by norm_num, one_zpow, zpow_one, one_mul]
    rw [h1, mul_comm]
    push_cast
    congr 1
  have hcoef : (1 : ℂ) / (1 / 2 : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
    have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [h12, ← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by rfl, ← Complex.ofReal_div]
    congr 1
    rw [Real.sqrt_eq_rpow, one_div, one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
  have hrhs : (∑' n : ℤ, Complex.exp (-Real.pi / (1 / 2 : ℂ) * ((n : ℂ) + Complex.I * (Complex.I / 2)) ^ 2)) =
      (T2 2 : ℂ) := by
    rw [T2, Complex.ofReal_tsum]
    let sh : ℤ ≃ ℤ := Equiv.addRight (1 : ℤ)
    rw [← sh.tsum_eq]
    congr 1; funext n
    dsimp [sh]
    rw [Complex.ofReal_exp]
    congr 1
    have hI : Complex.I * (Complex.I / 2) = -(1 / 2 : ℂ) := by
      rw [mul_div_assoc', Complex.I_mul_I]; ring
    rw [hI]
    push_cast
    ring
  rw [hlhs, hcoef, hrhs] at h
  have hre := congrArg Complex.re h
  simpa using hre

private lemma T3_pos {a : ℝ} (ha : 0 < a) : 0 < T3 a := by
  have hsum := (summable_T3_norm ha).of_norm
  have h0 : (0 : ℝ) < Real.exp (-Real.pi * a * ((0 : ℤ) : ℝ) ^ 2) := Real.exp_pos _
  exact lt_of_lt_of_le h0 (hsum.le_tsum 0 (fun k _ => (Real.exp_pos _).le))

private lemma T2_pos {a : ℝ} (ha : 0 < a) : 0 < T2 a := by
  have hsum := (summable_T2_norm ha).of_norm
  have h0 : (0 : ℝ) < Real.exp (-Real.pi * a * (((0 : ℤ) : ℝ) + 1 / 2) ^ 2) := Real.exp_pos _
  exact lt_of_lt_of_le h0 (hsum.le_tsum 0 (fun k _ => (Real.exp_pos _).le))

private lemma theta_ratio_sq : (T3 2 / T3 1) ^ 2 = (2 + Real.sqrt 2) / 4 := by
  have hadd := T3_sq_add_T4_sq (a := 1) (by norm_num)
  have hsub := T3_sq_sub_T4_sq (a := 1) (by norm_num)
  have hmul := T3_mul_T4 (a := 1 / 2) (by norm_num)
  norm_num at hadd hsub hmul
  rw [T3_half, T4_half] at hmul
  have hT32_pos : 0 < T3 2 := T3_pos (by norm_num)
  have hT22_pos : 0 < T2 2 := T2_pos (by norm_num)
  have hT31_pos : 0 < T3 1 := T3_pos (by norm_num)
  set A : ℝ := T3 2 ^ 2
  set B : ℝ := T2 2 ^ 2
  have hC : T3 1 ^ 2 = A + B := by linarith
  have hD : T4 1 ^ 2 = A - B := by linarith
  have hDval : T4 1 ^ 2 = 2 * T3 2 * T2 2 := by
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith
  have hDpos : 0 < A - B := by linarith [mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hT32_pos) hT22_pos]
  have hCpos : 0 < A + B := by positivity
  have hDsq : (A - B) ^ 2 = 4 * A * B := by
    have : (T4 1 ^ 2) ^ 2 = (2 * T3 2 * T2 2) ^ 2 := by rw [hDval]
    nlinarith
  have hCsq : (A + B) ^ 2 = (Real.sqrt 2 * (A - B)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith
  have hlin : A + B = Real.sqrt 2 * (A - B) :=
    (sq_eq_sq₀ hCpos.le (mul_nonneg (Real.sqrt_nonneg 2) hDpos.le)).mp hCsq
  have h2A : 2 * A = (A + B) * (1 + Real.sqrt 2 / 2) := by
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith
  rw [div_pow, hC]
  field_simp [hCpos.ne']
  linarith

private lemma coeff_thetaSeries (m n : ℕ) :
    PowerSeries.coeff n (thetaSeries m) =
      (if n = 0 then 1 else 0) +
        ∑ j ∈ Finset.range n, if m * (j + 1) ^ 2 = n then 2 else 0 := by
  simp [thetaSeries]

private lemma abs_coeff_thetaSeries_le (m : ℕ) (hm : 0 < m) (n : ℕ) :
    |((PowerSeries.coeff n (thetaSeries m) : ℤ) : ℝ)| ≤ 2 := by
  rw [coeff_thetaSeries]
  by_cases hn : n = 0
  · subst hn; norm_num
  · simp only [if_neg hn, zero_add]
    have hle : (∑ j ∈ Finset.range n, if m * (j + 1) ^ 2 = n then (2 : ℤ) else 0) ≤ 2 ∧
        0 ≤ (∑ j ∈ Finset.range n, if m * (j + 1) ^ 2 = n then (2 : ℤ) else 0) := by
      constructor
      · by_cases hex : ∃ j ∈ Finset.range n, m * (j + 1) ^ 2 = n
        · rcases hex with ⟨j0, hj0, hjm⟩
          have huniq : ∀ j ∈ Finset.range n, m * (j + 1) ^ 2 = n → j = j0 := by
            intro j _ hj
            have h1 : (j + 1) ^ 2 = (j0 + 1) ^ 2 := Nat.eq_of_mul_eq_mul_left hm (hj.trans hjm.symm)
            nlinarith
          have hsum : (∑ j ∈ Finset.range n, if m * (j + 1) ^ 2 = n then (2 : ℤ) else 0) = 2 := by
            rw [Finset.sum_eq_single j0]
            · simp [hjm]
            · intro j hj hne
              rw [if_neg]
              intro heq; exact hne (huniq j hj heq)
            · intro h; exact absurd hj0 h
          omega
        · push Not at hex
          have hsum : (∑ j ∈ Finset.range n, if m * (j + 1) ^ 2 = n then (2 : ℤ) else 0) = 0 := by
            refine Finset.sum_eq_zero fun j hj => if_neg (hex j hj)
          omega
      · exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num
    rw [abs_of_nonneg (by exact_mod_cast hle.2)]
    exact_mod_cast hle.1

private lemma tsum_thetaSeries_eq_T3 (m : ℕ) (hm : 0 < m) :
    (∑' n : ℕ, ((PowerSeries.coeff n (thetaSeries m) : ℤ) : ℝ) * Real.exp (-Real.pi) ^ n) = T3 m := by
  set q : ℝ := Real.exp (-Real.pi)
  have hq_pos : 0 < q := Real.exp_pos _
  have hq_lt : q < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  have hpow : ∀ k : ℕ, q ^ (m * k ^ 2) = Real.exp (-Real.pi * (m : ℝ) * (k : ℝ) ^ 2) := by
    intro k
    rw [show q ^ (m * k ^ 2) = Real.exp (↑(m * k ^ 2) * (-Real.pi)) by
      rw [← Real.exp_nat_mul]]
    congr 1; push_cast; ring
  have hT3_nat : T3 m = 1 + ∑' j : ℕ, 2 * q ^ (m * (j + 1) ^ 2) := by
    have hsumZ : Summable fun k : ℤ => Real.exp (-Real.pi * (m : ℝ) * (k : ℝ) ^ 2) :=
      (summable_T3_norm (by exact_mod_cast hm)).of_norm
    let Znn : Set ℤ := {k | 0 ≤ k}
    rw [T3, ← (hsumZ.subtype Znn).tsum_add_tsum_compl (hsumZ.subtype Znnᶜ)]
    let ePos : ℕ ≃ Znn :=
      { toFun := fun n => ⟨(n : ℤ), Int.natCast_nonneg n⟩
        invFun := fun k => k.1.toNat
        left_inv := fun n => Int.toNat_natCast n
        right_inv := fun ⟨k, hk⟩ => Subtype.ext (Int.toNat_of_nonneg hk) }
    let eNeg : ℕ ≃ (Znnᶜ : Set ℤ) :=
      { toFun := fun j => ⟨-((j + 1 : ℕ) : ℤ), by
          change ¬ (0 ≤ -((j + 1 : ℕ) : ℤ)); omega⟩
        invFun := fun k => (-k.1 - 1).toNat
        left_inv := fun j => by
          dsimp
          omega
        right_inv := fun ⟨k, hk⟩ => by
          apply Subtype.ext
          have hklt : k < 0 := by
            change ¬ (0 ≤ k) at hk
            omega
          dsimp
          omega }
    have hPos : (∑' k : Znn, Real.exp (-Real.pi * (m : ℝ) * (k.1 : ℝ) ^ 2)) =
        1 + ∑' j : ℕ, q ^ (m * (j + 1) ^ 2) := by
      rw [← ePos.tsum_eq]
      have hsumPos : Summable fun n : ℕ =>
          Real.exp (-Real.pi * (m : ℝ) * ((ePos n).1 : ℝ) ^ 2) :=
        (hsumZ.subtype Znn).comp_injective ePos.injective
      rw [hsumPos.tsum_eq_zero_add]
      have h0 : Real.exp (-Real.pi * (m : ℝ) * ((ePos 0).1 : ℝ) ^ 2) = 1 := by
        simp [ePos]
      rw [h0]
      congr 1; congr 1; funext j; dsimp [ePos]; rw [hpow (j + 1)]; push_cast; rfl
    have hNeg : (∑' k : (Znnᶜ : Set ℤ), Real.exp (-Real.pi * (m : ℝ) * (k.1 : ℝ) ^ 2)) =
        ∑' j : ℕ, q ^ (m * (j + 1) ^ 2) := by
      rw [← eNeg.tsum_eq]
      congr 1; funext j; dsimp [eNeg]; rw [hpow (j + 1)]; congr 1; push_cast; ring
    change (∑' k : Znn, Real.exp (-Real.pi * (m : ℝ) * (k.1 : ℝ) ^ 2)) +
      (∑' k : (Znnᶜ : Set ℤ), Real.exp (-Real.pi * (m : ℝ) * (k.1 : ℝ) ^ 2)) = _
    rw [hPos, hNeg, add_assoc, ← two_mul, ← tsum_mul_left]
  rw [hT3_nat]
  have hsumN : Summable fun n : ℕ => ((PowerSeries.coeff n (thetaSeries m) : ℤ) : ℝ) * q ^ n := by
    refine ((summable_geometric_of_lt_one hq_pos.le hq_lt).mul_left 2).of_norm_bounded fun n => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (pow_nonneg hq_pos.le n)]
    exact mul_le_mul_of_nonneg_right (abs_coeff_thetaSeries_le m hm n) (pow_nonneg hq_pos.le n)
  rw [hsumN.tsum_eq_zero_add]
  have hc0 : ((PowerSeries.coeff 0 (thetaSeries m) : ℤ) : ℝ) * q ^ 0 = 1 := by
    simp [coeff_thetaSeries]
  rw [hc0]
  congr 1
  let f : ℕ → ℕ := fun j => m * (j + 1) ^ 2 - 1
  have hfinj : Function.Injective f := by
    intro j1 j2 h
    dsimp [f] at h
    have hp1 : 1 ≤ m * (j1 + 1) ^ 2 :=
      Nat.mul_le_mul hm (Nat.one_le_pow 2 (j1 + 1) (Nat.succ_pos j1))
    have hp2 : 1 ≤ m * (j2 + 1) ^ 2 :=
      Nat.mul_le_mul hm (Nat.one_le_pow 2 (j2 + 1) (Nat.succ_pos j2))
    have heq : m * (j1 + 1) ^ 2 = m * (j2 + 1) ^ 2 := by omega
    have hsq : (j1 + 1) ^ 2 = (j2 + 1) ^ 2 := Nat.eq_of_mul_eq_mul_left hm heq
    nlinarith
  refine tsum_eq_tsum_of_ne_zero_bij (fun j => f j.1) ?_ ?_ ?_
  · rintro ⟨j1, _⟩ ⟨j2, _⟩ h; exact Subtype.ext (hfinj h)
  · intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    rw [coeff_thetaSeries] at hn
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, zero_add] at hn
    by_contra hnot
    simp only [Set.mem_range, not_exists] at hnot
    have hzero : (∑ j ∈ Finset.range (n + 1), if m * (j + 1) ^ 2 = n + 1 then (2 : ℤ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j _ => if_neg ?_
      intro heq
      have hj_supp : j ∈ Function.support (fun j : ℕ => 2 * q ^ (m * (j + 1) ^ 2)) := by
        simp only [Function.mem_support, ne_eq]
        exact (mul_pos (by norm_num) (pow_pos hq_pos _)).ne'
      have hne := hnot ⟨j, hj_supp⟩
      have hfj : f j = n := by dsimp [f]; omega
      exact hne hfj
    rw [hzero] at hn
    simp at hn
  · rintro ⟨j, _⟩
    dsimp [f]
    have hpos : 1 ≤ m * (j + 1) ^ 2 :=
      Nat.mul_le_mul hm (Nat.one_le_pow 2 (j + 1) (Nat.succ_pos j))
    have hsucc : m * (j + 1) ^ 2 - 1 + 1 = m * (j + 1) ^ 2 := by omega
    rw [hsucc, coeff_thetaSeries]
    simp only [show m * (j + 1) ^ 2 ≠ 0 by omega, ↓reduceIte, zero_add]
    have hj_lt : j < m * (j + 1) ^ 2 := by
      have h1 : (j + 1) ^ 2 = j * j + 2 * j + 1 := by ring
      have h2 : (j + 1) ^ 2 ≤ m * (j + 1) ^ 2 := Nat.le_mul_of_pos_left _ hm
      omega
    have hsum2 : (∑ i ∈ Finset.range (m * (j + 1) ^ 2),
        if m * (i + 1) ^ 2 = m * (j + 1) ^ 2 then (2 : ℤ) else 0) = 2 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hne
        rw [if_neg]
        intro heq
        have hsq : (i + 1) ^ 2 = (j + 1) ^ 2 := Nat.eq_of_mul_eq_mul_left hm heq
        exact hne (by nlinarith)
      · intro h; exact absurd (Finset.mem_range.mpr hj_lt) h
    rw [hsum2]
    push_cast
    rfl

private lemma exp_neg_pi_lt_one_eighth : Real.exp (-Real.pi) < 1 / 8 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have he1 : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  have he3 : (8 : ℝ) < Real.exp 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    nlinarith [sq_nonneg (Real.exp 1)]
  have hepi : (8 : ℝ) < Real.exp Real.pi := lt_trans he3 (Real.exp_lt_exp.mpr hpi)
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
  linarith

private lemma coeff_inv_bound (n : ℕ) :
    |((PowerSeries.coeff n (PowerSeries.invOfUnit (thetaSeries 1) 1) : ℤ) : ℝ)| ≤ 4 ^ n := by
  set θ := thetaSeries 1
  set φ := PowerSeries.invOfUnit θ 1
  have hconst : PowerSeries.constantCoeff θ = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_thetaSeries]
    simp
  have hmul : θ * φ = 1 := PowerSeries.mul_invOfUnit θ 1 hconst
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : PowerSeries.coeff 0 φ = 1 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit]
        simp
      rw [h0]; norm_num
    · have hcn : PowerSeries.coeff n (θ * φ) = 0 := by
        rw [hmul, PowerSeries.coeff_one, if_neg hn.ne']
      rw [PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun k l => PowerSeries.coeff k θ * PowerSeries.coeff l φ)] at hcn
      have hsplit : (∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k θ * PowerSeries.coeff (n - k) φ) =
          PowerSeries.coeff 0 θ * PowerSeries.coeff n φ +
            ∑ k ∈ Finset.Ico 1 (n + 1), PowerSeries.coeff k θ * PowerSeries.coeff (n - k) φ := by
        rw [Finset.sum_range_eq_add_Ico _ (by omega)]
        simp
      rw [hsplit, PowerSeries.coeff_zero_eq_constantCoeff_apply, hconst, one_mul] at hcn
      have hsolve : ((PowerSeries.coeff n φ : ℤ) : ℝ) =
          -(∑ k ∈ Finset.Ico 1 (n + 1),
            ((PowerSeries.coeff k θ : ℤ) : ℝ) * ((PowerSeries.coeff (n - k) φ : ℤ) : ℝ)) := by
        have hcast : ((PowerSeries.coeff n φ +
            ∑ k ∈ Finset.Ico 1 (n + 1), PowerSeries.coeff k θ * PowerSeries.coeff (n - k) φ : ℤ) : ℝ) = 0 := by
          exact_mod_cast hcn
        push_cast at hcast
        linarith
      rw [hsolve, abs_neg]
      calc |∑ k ∈ Finset.Ico 1 (n + 1),
              ((PowerSeries.coeff k θ : ℤ) : ℝ) * ((PowerSeries.coeff (n - k) φ : ℤ) : ℝ)|
          ≤ ∑ k ∈ Finset.Ico 1 (n + 1),
              |((PowerSeries.coeff k θ : ℤ) : ℝ) * ((PowerSeries.coeff (n - k) φ : ℤ) : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.Ico 1 (n + 1), 2 * (4 : ℝ) ^ (n - k) := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [abs_mul]
            have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
            exact mul_le_mul (abs_coeff_thetaSeries_le 1 (by norm_num) k)
              (ih (n - k) (by omega)) (abs_nonneg _) (by norm_num)
        _ ≤ (4 : ℝ) ^ n := by
            have h3 : 3 * ∑ k ∈ Finset.Ico 1 (n + 1), (4 : ℝ) ^ (n - k) = (4 : ℝ) ^ n - 1 := by
              have hshift : ∑ k ∈ Finset.Ico 1 (n + 1), (4 : ℝ) ^ (n - k) =
                  ∑ j ∈ Finset.range n, (4 : ℝ) ^ j := by
                refine Finset.sum_bij (fun k _ => n - k) ?_ ?_ ?_ ?_
                · intro k hk; rw [Finset.mem_Ico] at hk; exact Finset.mem_range.mpr (by omega)
                · intro k1 hk1 k2 hk2 heq
                  rw [Finset.mem_Ico] at hk1 hk2; omega
                · intro j hj
                  rw [Finset.mem_range] at hj
                  exact ⟨n - j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
                · intro _ _; rfl
              rw [hshift, geom_sum_eq (by norm_num : (4 : ℝ) ≠ 1)]
              ring
            rw [← Finset.mul_sum]
            have h4pos : (0 : ℝ) ≤ (4 : ℝ) ^ n := by positivity
            linarith

private lemma powerSeries_mul_tsum {F G : PowerSeries ℤ} {q : ℝ}
    (hF : Summable fun n => ‖((PowerSeries.coeff n F : ℤ) : ℝ) * q ^ n‖)
    (hG : Summable fun n => ‖((PowerSeries.coeff n G : ℤ) : ℝ) * q ^ n‖) :
    (Summable fun n => ‖((PowerSeries.coeff n (F * G) : ℤ) : ℝ) * q ^ n‖) ∧
    (∑' n : ℕ, ((PowerSeries.coeff n (F * G) : ℤ) : ℝ) * q ^ n) =
      (∑' n : ℕ, ((PowerSeries.coeff n F : ℤ) : ℝ) * q ^ n) *
        (∑' n : ℕ, ((PowerSeries.coeff n G : ℤ) : ℝ) * q ^ n) := by
  have hterm : ∀ n : ℕ, ((PowerSeries.coeff n (F * G) : ℤ) : ℝ) * q ^ n =
      ∑ k ∈ Finset.range (n + 1),
        (((PowerSeries.coeff k F : ℤ) : ℝ) * q ^ k) *
          (((PowerSeries.coeff (n - k) G : ℤ) : ℝ) * q ^ (n - k)) := by
    intro n
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun k l => PowerSeries.coeff k F * PowerSeries.coeff l G)]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hle : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hadd : k + (n - k) = n := Nat.add_sub_of_le hle
    have hqpow : q ^ n = q ^ k * q ^ (n - k) := by rw [← pow_add, hadd]
    rw [hqpow]
    ring
  refine ⟨?_, ?_⟩
  · refine (summable_norm_sum_mul_range_of_summable_norm hF hG).congr fun n => ?_
    rw [hterm n]
  · rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hF hG]
    congr 1; funext n; exact hterm n

private lemma main_proof :
    HasSum (fun n : ℕ => (a210066 n : ℝ) * Real.exp (-Real.pi) ^ n)
      ((2 + Real.sqrt 2) / 4) := by
  set q : ℝ := Real.exp (-Real.pi)
  have hq_pos : 0 < q := Real.exp_pos _
  have hq_lt8 : q < 1 / 8 := exp_neg_pi_lt_one_eighth
  set θ1 := thetaSeries 1
  set θ2 := thetaSeries 2
  set φ := PowerSeries.invOfUnit θ1 1
  have hθ1_norm : Summable fun n => ‖((PowerSeries.coeff n θ1 : ℤ) : ℝ) * q ^ n‖ := by
    refine ((summable_geometric_of_lt_one hq_pos.le (by linarith)).mul_left 2).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun n => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (pow_nonneg hq_pos.le n)]
    exact mul_le_mul_of_nonneg_right (abs_coeff_thetaSeries_le 1 (by norm_num) n)
      (pow_nonneg hq_pos.le n)
  have hθ2_norm : Summable fun n => ‖((PowerSeries.coeff n θ2 : ℤ) : ℝ) * q ^ n‖ := by
    refine ((summable_geometric_of_lt_one hq_pos.le (by linarith)).mul_left 2).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun n => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (pow_nonneg hq_pos.le n)]
    exact mul_le_mul_of_nonneg_right (abs_coeff_thetaSeries_le 2 (by norm_num) n)
      (pow_nonneg hq_pos.le n)
  have hφ_norm : Summable fun n => ‖((PowerSeries.coeff n φ : ℤ) : ℝ) * q ^ n‖ := by
    refine (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (pow_nonneg hq_pos.le n)]
    calc |((PowerSeries.coeff n φ : ℤ) : ℝ)| * q ^ n
        ≤ (4 : ℝ) ^ n * q ^ n := mul_le_mul_of_nonneg_right (coeff_inv_bound n) (pow_nonneg hq_pos.le n)
      _ = (4 * q) ^ n := (mul_pow 4 q n).symm
      _ ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
  have hconst : PowerSeries.constantCoeff θ1 = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_thetaSeries]
    simp
  have hprod1 := (powerSeries_mul_tsum hθ1_norm hφ_norm).2
  rw [PowerSeries.mul_invOfUnit θ1 1 hconst] at hprod1
  have hone : (∑' n : ℕ, ((PowerSeries.coeff n (1 : PowerSeries ℤ) : ℤ) : ℝ) * q ^ n) = 1 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn; simp [PowerSeries.coeff_one, hn]
  rw [hone, tsum_thetaSeries_eq_T3 1 (by norm_num)] at hprod1
  simp only [Nat.cast_one] at hprod1
  have hT31_ne : T3 1 ≠ 0 := (T3_pos (by norm_num)).ne'
  have hφ_val : (∑' n : ℕ, ((PowerSeries.coeff n φ : ℤ) : ℝ) * q ^ n) = (T3 1)⁻¹ :=
    eq_inv_of_mul_eq_one_right hprod1.symm
  have hψ := powerSeries_mul_tsum hθ2_norm hφ_norm
  have hψ_val : (∑' n : ℕ, ((PowerSeries.coeff n (θ2 * φ) : ℤ) : ℝ) * q ^ n) = T3 2 / T3 1 := by
    rw [hψ.2, tsum_thetaSeries_eq_T3 2 (by norm_num), hφ_val, div_eq_mul_inv]
    simp only [Nat.cast_ofNat]
  have hsq := powerSeries_mul_tsum hψ.1 hψ.1
  have hsum_final : Summable fun n : ℕ => (a210066 n : ℝ) * q ^ n := by
    refine hsq.1.of_norm.congr fun n => ?_
    simp only [a210066, sq, θ1, θ2, φ]
  have hval_final : (∑' n : ℕ, (a210066 n : ℝ) * q ^ n) = (2 + Real.sqrt 2) / 4 := by
    have h1 : (∑' n : ℕ, (a210066 n : ℝ) * q ^ n) =
        ∑' n : ℕ, ((PowerSeries.coeff n ((θ2 * φ) * (θ2 * φ)) : ℤ) : ℝ) * q ^ n := by
      congr 1; funext n; simp only [a210066, sq, θ1, θ2, φ]
    rw [h1, hsq.2, hψ_val, ← sq, theta_ratio_sq]
  rw [← hval_final]
  exact hsum_final.hasSum

end OMA.S_oeis_a201488

theorem OMA.solution : type_of% @OMA.S_oeis_a201488.main :=
  OMA.S_oeis_a201488.main_proof

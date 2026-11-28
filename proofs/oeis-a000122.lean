import OMAStatements.S_oeis_a000122

namespace OMA_oeis_a000122

open Real MeasureTheory Set Filter Topology
open scoped BigOperators

private noncomputable def theta3 (t : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-t * (n : ℝ) ^ 2)

private noncomputable def theta4 (t : ℝ) : ℝ :=
  ∑' n : ℤ, (-1 : ℝ) ^ n * Real.exp (-t * (n : ℝ) ^ 2)

private noncomputable def theta2 (t : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-t * ((n : ℝ) + 1 / 2) ^ 2)

/-! ### Helper equivalences for infinite sums -/

private def eInt : ℕ ⊕ ℕ ≃ ℤ where
  toFun
    | Sum.inl n => (n : ℤ)
    | Sum.inr n => -((n + 1 : ℕ) : ℤ)
  invFun z := if 0 ≤ z then Sum.inl z.toNat else Sum.inr ((-z).toNat - 1)
  left_inv s := by
    cases s with
    | inl n => simp
    | inr n => simp; omega
  right_inv z := by
    by_cases h : 0 ≤ z
    · simp only [h, ↓reduceIte]; omega
    · simp only [h, ↓reduceIte]; omega

private lemma summable_int_of_nat {f : ℤ → ℝ}
    (h1 : Summable (fun n : ℕ => f (n : ℤ)))
    (h2 : Summable (fun n : ℕ => f (-((n + 1 : ℕ) : ℤ)))) :
    Summable f := by
  rw [← eInt.summable_iff]
  exact Summable.sum (f ∘ eInt) h1 h2

private lemma tsum_split_pred {α : Type*} (P : α → Prop) [DecidablePred P] {f : α → ℝ}
    (hf : Summable f) :
    (∑' x : α, f x) = (∑' x : {x : α // P x}, f x.1) + (∑' x : {x : α // ¬ P x}, f x.1) := by
  rw [← (Equiv.sumCompl P).tsum_eq]
  exact (hf.subtype _).tsum_sum (hf.subtype _)

private lemma tsum_split_zero {α : Type*} [Zero α] [DecidableEq α] {f : α → ℝ}
    (hf : Summable f) :
    (∑' x : α, f x) = f 0 + ∑' x : {x : α // x ≠ 0}, f x.1 := by
  rw [tsum_split_pred (fun x : α => x = 0) hf]
  congr 1
  let e0 : Unit ≃ {x : α // x = 0} :=
    { toFun := fun _ => ⟨0, rfl⟩
      invFun := fun _ => ()
      left_inv := fun _ => rfl
      right_inv := fun ⟨x, hx⟩ => Subtype.ext hx.symm }
  rw [← e0.tsum_eq]
  simp [e0]

/-! ### Part 1: Summability and basic bounds -/

private lemma summable_exp_neg_mul_nat (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => Real.exp (-t * (n : ℝ))) := by
  have hlt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hge : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hgeom : Summable (fun n : ℕ => (Real.exp (-t)) ^ n) :=
    summable_geometric_of_lt_one hge hlt
  refine hgeom.congr (fun n => ?_)
  rw [← Real.exp_nat_mul]
  ring_nf

private lemma summable_exp_neg_mul_nat_sq (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => Real.exp (-t * (n : ℝ) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
    (summable_exp_neg_mul_nat t ht)
  apply Real.exp_le_exp.mpr
  have hnat : n ≤ n ^ 2 := by rw [sq]; exact Nat.le_mul_self n
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hnat
  nlinarith

private lemma summable_theta3 (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-t * (n : ℝ) ^ 2)) := by
  refine summable_int_of_nat ?_ ?_
  · exact (summable_exp_neg_mul_nat_sq t ht).congr (fun n => by simp)
  · have hsucc : Summable (fun n : ℕ => Real.exp (-t * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
      (summable_nat_add_iff 1).mpr (summable_exp_neg_mul_nat_sq t ht)
    exact hsucc.congr (fun n => by simp; left; ring)

private lemma summable_theta4 (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℤ => (-1 : ℝ) ^ n * Real.exp (-t * (n : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded (summable_theta3 t ht) (fun n => ?_)
  rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]

private lemma summable_theta2 (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-t * ((n : ℝ) + 1 / 2) ^ 2)) := by
  have h1 : Summable (fun n : ℕ => Real.exp (-t * ((n : ℝ) + 1 / 2) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
      (summable_exp_neg_mul_nat_sq t ht)
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  refine summable_int_of_nat ?_ ?_
  · exact h1.congr (fun n => by simp)
  · refine h1.congr (fun n => ?_)
    congr 2
    push_cast
    ring

private lemma theta3_pos (t : ℝ) (ht : 0 < t) : 0 < theta3 t := by
  have h0 : (0 : ℝ) < Real.exp (-t * ((0 : ℤ) : ℝ) ^ 2) := Real.exp_pos _
  exact lt_of_lt_of_le h0 ((summable_theta3 t ht).le_tsum 0 (fun n _ => (Real.exp_pos _).le))

private lemma theta2_pos (t : ℝ) (ht : 0 < t) : 0 < theta2 t := by
  have h0 : (0 : ℝ) < Real.exp (-t * (((0 : ℤ) : ℝ) + 1 / 2) ^ 2) := Real.exp_pos _
  exact lt_of_lt_of_le h0 ((summable_theta2 t ht).le_tsum 0 (fun n _ => (Real.exp_pos _).le))

private lemma theta3_eq_one_add_two_tsum (t : ℝ) (ht : 0 < t) :
    theta3 t = 1 + 2 * ∑' n : ℕ, Real.exp (-t * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  unfold theta3
  have hs := summable_theta3 t ht
  rw [tsum_split_zero hs]
  have hpos : Summable (fun n : ℕ => Real.exp (-t * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).mpr (summable_exp_neg_mul_nat_sq t ht)
  have hsplit : (∑' n : {x : ℤ // x ≠ 0}, Real.exp (-t * (n.1 : ℝ) ^ 2)) =
      2 * ∑' n : ℕ, Real.exp (-t * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    let e : ℕ ⊕ ℕ ≃ {x : ℤ // x ≠ 0} :=
      { toFun := fun s => match s with
          | Sum.inl n => ⟨(n + 1 : ℕ), by omega⟩
          | Sum.inr n => ⟨-((n + 1 : ℕ) : ℤ), by omega⟩
        invFun := fun x =>
          if 0 < x.1 then Sum.inl (x.1.toNat - 1) else Sum.inr ((-x.1).toNat - 1)
        left_inv := fun s => by
          cases s with
          | inl n => simp
          | inr n => simp
        right_inv := fun x => by
          rcases x with ⟨x, hx⟩
          by_cases h : 0 < x
          · simp only [h, ↓reduceIte, Subtype.mk.injEq]
            omega
          · simp only [h, ↓reduceIte, Subtype.mk.injEq]
            omega }
    rw [← Equiv.tsum_eq e]
    rw [(hpos.congr (fun n => by simp [e])).tsum_sum (hpos.congr (fun n => by simp [e]; left; ring))]
    have h1 : (∑' n : ℕ, Real.exp (-t * ((e (Sum.inl n)).1 : ℝ) ^ 2)) =
        ∑' n : ℕ, Real.exp (-t * ((n + 1 : ℕ) : ℝ) ^ 2) := rfl
    have h2 : (∑' n : ℕ, Real.exp (-t * ((e (Sum.inr n)).1 : ℝ) ^ 2)) =
        ∑' n : ℕ, Real.exp (-t * ((n + 1 : ℕ) : ℝ) ^ 2) := by
      congr 1; ext n; simp [e]; left; ring
    rw [h1, h2]; ring
  rw [hsplit]
  simp

private lemma sum_a_eq_theta3_pi :
    (∑' k : ℕ, (OMA.S_oeis_a000122.a k : ℝ) / Real.exp (k * Real.pi)) = theta3 Real.pi := by
  rw [theta3_eq_one_add_two_tsum Real.pi Real.pi_pos]
  let f : ℕ → ℝ := fun k => (OMA.S_oeis_a000122.a k : ℝ) / Real.exp (k * Real.pi)
  have hsq : ∀ n : ℕ, f ((n + 1) ^ 2) = 2 * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    have hne : (n + 1) ^ 2 ≠ 0 := by positivity
    simp only [f, OMA.S_oeis_a000122.a, hne, ↓reduceIte, Nat.sqrt_eq']
    simp only [Nat.cast_ofNat, div_eq_mul_inv, ← Real.exp_neg]
    congr 2; push_cast; ring
  have hzero : ∀ k : ℕ, k ≠ 0 → (∀ n : ℕ, k ≠ (n + 1) ^ 2) → f k = 0 := by
    intro k hk hnsq
    have hsqrt : Nat.sqrt k ^ 2 ≠ k := by
      intro h
      have hpos : 0 < Nat.sqrt k := by
        by_contra hc
        have h0 : Nat.sqrt k = 0 := by omega
        rw [h0] at h
        omega
      exact hnsq (Nat.sqrt k - 1) (by rw [Nat.sub_add_cancel hpos]; exact h.symm)
    simp [f, OMA.S_oeis_a000122.a, hk, hsqrt]
  have hsum_pos : Summable (fun n : ℕ => 2 * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    ((summable_nat_add_iff 1).mpr (summable_exp_neg_mul_nat_sq Real.pi Real.pi_pos)).mul_left 2
  have hinj : Function.Injective (fun n : ℕ => (n + 1) ^ 2) := by
    intro a b hab
    have h1 : Nat.sqrt ((a + 1) ^ 2) = Nat.sqrt ((b + 1) ^ 2) := congrArg Nat.sqrt hab
    simp only [Nat.sqrt_eq'] at h1
    omega
  let g : ℕ → {k : ℕ // k ≠ 0} := fun n => ⟨(n + 1) ^ 2, by positivity⟩
  have hginj : Function.Injective g := fun a b h => hinj (congrArg Subtype.val h)
  have hsupp : ∀ x : {k : ℕ // k ≠ 0}, x ∉ Set.range g → f x.1 = 0 := by
    intro x hx
    apply hzero x.1 x.2
    intro n hn
    exact hx ⟨n, Subtype.ext hn.symm⟩
  have hsummable_nz : Summable (fun k : {k : ℕ // k ≠ 0} => f k.1) := by
    rw [← Function.Injective.summable_iff hginj hsupp]
    exact hsum_pos.congr (fun n => (hsq n).symm)
  have htsum_nz : (∑' k : {k : ℕ // k ≠ 0}, f k.1) =
      ∑' n : ℕ, 2 * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    classical
    rw [tsum_split_pred (fun k : {k : ℕ // k ≠ 0} => k ∈ Set.range g) hsummable_nz]
    have hcomp0 : (∑' k : {k : {k : ℕ // k ≠ 0} // k ∉ Set.range g}, f k.1.1) = 0 := by
      have h0 : (fun k : {k : {k : ℕ // k ≠ 0} // k ∉ Set.range g} => f k.1.1) = fun _ => 0 := by
        ext k; exact hsupp k.1 k.2
      rw [h0, tsum_zero]
    rw [hcomp0, add_zero]
    rw [tsum_range (f := fun x : {k : ℕ // k ≠ 0} => f x.1) hginj]
    congr 1; ext n; exact hsq n
  have hsummable_f : Summable f := by
    rw [← summable_nat_add_iff 1]
    let e : ℕ ≃ {k : ℕ // k ≠ 0} :=
      { toFun := fun n => ⟨n + 1, Nat.succ_ne_zero n⟩
        invFun := fun k => k.1 - 1
        left_inv := fun n => by simp
        right_inv := fun k => Subtype.ext (Nat.sub_add_cancel (Nat.pos_of_ne_zero k.2)) }
    exact e.summable_iff.mpr hsummable_nz
  rw [tsum_split_zero hsummable_f, htsum_nz, tsum_mul_left]
  simp [f, OMA.S_oeis_a000122.a]

private lemma theta3_sub_one_le (t : ℝ) (ht : 0 < t) :
    0 ≤ theta3 t - 1 ∧ theta3 t - 1 ≤ 2 * Real.exp (-t) / (1 - Real.exp (-t)) := by
  rw [theta3_eq_one_add_two_tsum t ht]
  have hlt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsum : Summable (fun n : ℕ => Real.exp (-t * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).mpr (summable_exp_neg_mul_nat_sq t ht)
  have hgeom : Summable (fun n : ℕ => Real.exp (-t) * (Real.exp (-t)) ^ n) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hlt).mul_left _
  have hle : (∑' n : ℕ, Real.exp (-t * ((n + 1 : ℕ) : ℝ) ^ 2)) ≤
      ∑' n : ℕ, Real.exp (-t) * (Real.exp (-t)) ^ n := by
    refine hsum.tsum_le_tsum (fun n => ?_) hgeom
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    have hsq : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith
  have hgeom_val : (∑' n : ℕ, Real.exp (-t) * (Real.exp (-t)) ^ n) =
      Real.exp (-t) / (1 - Real.exp (-t)) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hlt, div_eq_mul_inv]
  rw [hgeom_val] at hle
  constructor
  · have hnn : 0 ≤ ∑' n : ℕ, Real.exp (-t * ((n + 1 : ℕ) : ℝ) ^ 2) :=
      tsum_nonneg (fun n => (Real.exp_pos (-t * ((n + 1 : ℕ) : ℝ) ^ 2)).le)
    linarith
  · rw [mul_div_assoc]; linarith

private lemma abs_theta4_sub_one_le (t : ℝ) (ht : 0 < t) :
    |theta4 t - 1| ≤ 2 * Real.exp (-t) / (1 - Real.exp (-t)) := by
  have hs4 := summable_theta4 t ht
  have hs3 := summable_theta3 t ht
  have h4 : theta4 t - 1 = ∑' n : {x : ℤ // x ≠ 0}, (-1 : ℝ) ^ n.1 * Real.exp (-t * (n.1 : ℝ) ^ 2) := by
    unfold theta4
    rw [tsum_split_zero hs4]
    simp
  have h3 : theta3 t - 1 = ∑' n : {x : ℤ // x ≠ 0}, Real.exp (-t * (n.1 : ℝ) ^ 2) := by
    unfold theta3
    rw [tsum_split_zero hs3]
    simp
  rw [h4]
  calc |∑' n : {x : ℤ // x ≠ 0}, (-1 : ℝ) ^ n.1 * Real.exp (-t * (n.1 : ℝ) ^ 2)|
      = ‖∑' n : {x : ℤ // x ≠ 0}, (-1 : ℝ) ^ n.1 * Real.exp (-t * (n.1 : ℝ) ^ 2)‖ := rfl
    _ ≤ ∑' n : {x : ℤ // x ≠ 0}, ‖(-1 : ℝ) ^ n.1 * Real.exp (-t * (n.1 : ℝ) ^ 2)‖ :=
        norm_tsum_le_tsum_norm (hs4.subtype _).norm
    _ = ∑' n : {x : ℤ // x ≠ 0}, Real.exp (-t * (n.1 : ℝ) ^ 2) := by
        congr 1; ext n
        rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    _ = theta3 t - 1 := h3.symm
    _ ≤ 2 * Real.exp (-t) / (1 - Real.exp (-t)) := (theta3_sub_one_le t ht).2

private lemma tendsto_bound_zero :
    Tendsto (fun t : ℝ => 2 * Real.exp (-t) / (1 - Real.exp (-t))) atTop (𝓝 0) := by
  have hexp : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hnum : Tendsto (fun t : ℝ => 2 * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using hexp.const_mul 2
  have hden : Tendsto (fun t : ℝ => 1 - Real.exp (-t)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hexp
  have hdiv : Tendsto (fun t : ℝ => (2 * Real.exp (-t)) / (1 - Real.exp (-t))) atTop (𝓝 (0 / 1)) :=
    hnum.div hden one_ne_zero
  simpa using hdiv

private lemma tendsto_theta3_atTop : Tendsto theta3 atTop (𝓝 1) := by
  have hbound : Tendsto (fun t : ℝ => 1 + 2 * Real.exp (-t) / (1 - Real.exp (-t))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add tendsto_bound_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    linarith [(theta3_sub_one_le t ht).1]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    linarith [(theta3_sub_one_le t ht).2]

private lemma tendsto_theta4_atTop : Tendsto theta4 atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ tendsto_bound_zero
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact abs_theta4_sub_one_le t ht

/-! ### Part 2: Poisson summation for theta4 -/

private lemma theta4_eq_theta2 (t : ℝ) (ht : 0 < t) :
    theta4 t = Real.sqrt (Real.pi / t) * theta2 (Real.pi ^ 2 / t) := by
  have ha : 0 < ((t / Real.pi : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact div_pos ht Real.pi_pos
  have hpois := Complex.tsum_exp_neg_quadratic ha (-(Complex.I / 2))
  have hlhs : (∑' n : ℤ, Complex.exp (-Real.pi * ((t / Real.pi : ℝ) : ℂ) * (n : ℂ) ^ 2 +
      2 * Real.pi * (-(Complex.I / 2)) * (n : ℂ))) = (theta4 t : ℂ) := by
    rw [theta4, Complex.ofReal_tsum]
    congr 1; ext n
    have hexp_pi : Complex.exp (-(Real.pi * Complex.I * (n : ℂ))) = (((-1 : ℝ) ^ n : ℝ) : ℂ) := by
      have h1 : -(Real.pi * Complex.I * (n : ℂ)) = (n : ℂ) * (-(Real.pi * Complex.I)) := by ring
      rw [h1, Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      simp
    have harg : -Real.pi * ((t / Real.pi : ℝ) : ℂ) * (n : ℂ) ^ 2 +
        2 * Real.pi * (-(Complex.I / 2)) * (n : ℂ) =
        (-(Real.pi * Complex.I * (n : ℂ))) + ((-t * (n : ℝ) ^ 2 : ℝ) : ℂ) := by
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      push_cast
      field_simp [hpi]
      ring
    rw [harg, Complex.exp_add, hexp_pi, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  have hrhs : (1 / ((t / Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      ∑' n : ℤ, Complex.exp (-Real.pi / ((t / Real.pi : ℝ) : ℂ) *
        ((n : ℂ) + Complex.I * (-(Complex.I / 2))) ^ 2)) =
      ((Real.sqrt (Real.pi / t) * theta2 (Real.pi ^ 2 / t) : ℝ) : ℂ) := by
    have hcoeff : (1 : ℂ) / ((t / Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
        ((Real.sqrt (Real.pi / t) : ℝ) : ℂ) := by
      have htp : 0 ≤ t / Real.pi := (div_pos ht Real.pi_pos).le
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow htp,
        ← Real.sqrt_eq_rpow, ← Complex.ofReal_one, ← Complex.ofReal_div,
        one_div, ← Real.sqrt_inv, inv_div]
    rw [hcoeff, theta2, Complex.ofReal_mul, Complex.ofReal_tsum]
    congr 2; ext n
    rw [Complex.ofReal_exp]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hI : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      have : Complex.I * Complex.I = -1 := Complex.I_mul_I
      linear_combination -(1 / 2 : ℂ) * this
    rw [hI]
    push_cast
    field_simp [hpi, ht0]
  rw [hlhs, hrhs] at hpois
  exact Complex.ofReal_injective hpois

private lemma theta4_pos (t : ℝ) (ht : 0 < t) : 0 < theta4 t := by
  rw [theta4_eq_theta2 t ht]
  exact mul_pos (Real.sqrt_pos.mpr (div_pos Real.pi_pos ht))
    (theta2_pos _ (div_pos (sq_pos_of_pos Real.pi_pos) ht))

private lemma theta4_pi_eq_theta2_pi : theta4 Real.pi = theta2 Real.pi := by
  rw [theta4_eq_theta2 Real.pi Real.pi_pos]
  have h1 : Real.pi / Real.pi = 1 := div_self Real.pi_ne_zero
  have h2 : Real.pi ^ 2 / Real.pi = Real.pi := by field_simp [Real.pi_ne_zero]
  rw [h1, h2, Real.sqrt_one, one_mul]

/-! ### Part 3: Algebraic doubling identities -/

private def eEven : ℤ × ℤ ≃ {p : ℤ × ℤ // Even (p.1 + p.2)} where
  toFun jk := ⟨(jk.1 + jk.2, jk.1 - jk.2), ⟨jk.1, by omega⟩⟩
  invFun p := ((p.1.1 + p.1.2) / 2, (p.1.1 - p.1.2) / 2)
  left_inv jk := by ext <;> dsimp <;> omega
  right_inv p := by
    rcases p with ⟨⟨m, n⟩, ⟨r, hr⟩⟩
    ext <;> dsimp <;> omega

private def eOdd : ℤ × ℤ ≃ {p : ℤ × ℤ // ¬ Even (p.1 + p.2)} where
  toFun jk := ⟨(jk.1 + jk.2 + 1, jk.1 - jk.2), by
    rintro ⟨r, hr⟩; omega⟩
  invFun p := ((p.1.1 + p.1.2 - 1) / 2, (p.1.1 - p.1.2 - 1) / 2)
  left_inv jk := by ext <;> dsimp <;> omega
  right_inv p := by
    rcases p with ⟨⟨m, n⟩, hodd⟩
    have hmod : (m + n) % 2 = 1 := by
      have : (m + n) % 2 ≠ 0 := by
        intro h0
        exact hodd ⟨(m + n) / 2, by omega⟩
      omega
    ext <;> dsimp <;> omega

private lemma theta3_sq_add_theta4_sq (t : ℝ) (ht : 0 < t) :
    theta3 t ^ 2 + theta4 t ^ 2 = 2 * theta3 (2 * t) ^ 2 := by
  have hs3 := summable_theta3 t ht
  have hs4 := summable_theta4 t ht
  have hs32 := summable_theta3 (2 * t) (by linarith)
  have hprod3 := hs3.mul_of_nonneg hs3 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hprod32 := hs32.mul_of_nonneg hs32 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have h3sq : theta3 t ^ 2 = ∑' p : ℤ × ℤ, Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    rw [sq, theta3, hs3.tsum_mul_tsum hs3 hprod3]
    congr 1; ext p; rw [← Real.exp_add]; congr 1; ring
  have h4sq : theta4 t ^ 2 = ∑' p : ℤ × ℤ,
      (-1 : ℝ) ^ (p.1 + p.2) * Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    have hprod : Summable (fun p : ℤ × ℤ =>
        ((-1 : ℝ) ^ p.1 * Real.exp (-t * (p.1 : ℝ) ^ 2)) *
        ((-1 : ℝ) ^ p.2 * Real.exp (-t * (p.2 : ℝ) ^ 2))) := by
      refine Summable.of_norm_bounded hprod3 (fun p => ?_)
      simp only [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
        Real.norm_of_nonneg (Real.exp_pos _).le, le_refl]
    rw [sq, theta4, hs4.tsum_mul_tsum hs4 hprod]
    congr 1; ext p
    rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    have hre : Real.exp (-t * (p.1 : ℝ) ^ 2) * Real.exp (-t * (p.2 : ℝ) ^ 2) =
        Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    linear_combination ((-1 : ℝ) ^ p.1 * (-1 : ℝ) ^ p.2) * hre
  have hsum3 : Summable (fun p : ℤ × ℤ => Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) := by
    refine hprod3.congr (fun p => ?_)
    rw [← Real.exp_add]; congr 1; ring
  have hsum4 : Summable (fun p : ℤ × ℤ => (-1 : ℝ) ^ (p.1 + p.2) * Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) := by
    refine Summable.of_norm_bounded hsum3 (fun p => ?_)
    rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [h3sq, h4sq, ← hsum3.tsum_add hsum4]
  have hcomb : (∑' p : ℤ × ℤ, (Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) +
      (-1 : ℝ) ^ (p.1 + p.2) * Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)))) =
      ∑' p : {p : ℤ × ℤ // Even (p.1 + p.2)}, 2 * Real.exp (-t * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2)) := by
    rw [tsum_split_pred (fun p : ℤ × ℤ => Even (p.1 + p.2)) (hsum3.add hsum4)]
    have hodd0 : (∑' p : {p : ℤ × ℤ // ¬ Even (p.1 + p.2)},
        (Real.exp (-t * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2)) +
        (-1 : ℝ) ^ (p.1.1 + p.1.2) * Real.exp (-t * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2)))) = 0 := by
      have h0 : (fun p : {p : ℤ × ℤ // ¬ Even (p.1 + p.2)} =>
          (Real.exp (-t * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2)) +
          (-1 : ℝ) ^ (p.1.1 + p.1.2) * Real.exp (-t * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2)))) = fun _ => 0 := by
        ext p
        have hodd : Odd (p.1.1 + p.1.2) := Int.not_even_iff_odd.mp p.2
        rw [hodd.neg_one_zpow]; ring
      rw [h0, tsum_zero]
    rw [hodd0, add_zero]
    congr 1; ext p
    rw [p.2.neg_one_zpow]; ring
  rw [hcomb, ← Equiv.tsum_eq eEven, tsum_mul_left]
  congr 1
  rw [sq, theta3, hs32.tsum_mul_tsum hs32 hprod32]
  congr 1; ext jk
  simp only [eEven, Equiv.coe_fn_mk, Int.cast_add, Int.cast_sub]
  rw [← Real.exp_add]; congr 1; ring

private lemma theta3_sq_sub_theta4_sq (t : ℝ) (ht : 0 < t) :
    theta3 t ^ 2 - theta4 t ^ 2 = 2 * theta2 (2 * t) ^ 2 := by
  have hs3 := summable_theta3 t ht
  have hs4 := summable_theta4 t ht
  have hs22 := summable_theta2 (2 * t) (by linarith)
  have hprod3 := hs3.mul_of_nonneg hs3 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hprod22 := hs22.mul_of_nonneg hs22 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hsum3 : Summable (fun p : ℤ × ℤ => Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) := by
    refine hprod3.congr (fun p => ?_)
    rw [← Real.exp_add]; congr 1; ring
  have hsum4 : Summable (fun p : ℤ × ℤ => (-1 : ℝ) ^ (p.1 + p.2) * Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) := by
    refine Summable.of_norm_bounded hsum3 (fun p => ?_)
    rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h3sq : theta3 t ^ 2 = ∑' p : ℤ × ℤ, Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    rw [sq, theta3, hs3.tsum_mul_tsum hs3 hprod3]
    congr 1; ext p; rw [← Real.exp_add]; congr 1; ring
  have h4sq : theta4 t ^ 2 = ∑' p : ℤ × ℤ,
      (-1 : ℝ) ^ (p.1 + p.2) * Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    have hprod : Summable (fun p : ℤ × ℤ =>
        ((-1 : ℝ) ^ p.1 * Real.exp (-t * (p.1 : ℝ) ^ 2)) *
        ((-1 : ℝ) ^ p.2 * Real.exp (-t * (p.2 : ℝ) ^ 2))) := by
      refine Summable.of_norm_bounded hprod3 (fun p => ?_)
      simp only [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
        Real.norm_of_nonneg (Real.exp_pos _).le, le_refl]
    rw [sq, theta4, hs4.tsum_mul_tsum hs4 hprod]
    congr 1; ext p
    rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    have hre : Real.exp (-t * (p.1 : ℝ) ^ 2) * Real.exp (-t * (p.2 : ℝ) ^ 2) =
        Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    linear_combination ((-1 : ℝ) ^ p.1 * (-1 : ℝ) ^ p.2) * hre
  rw [h3sq, h4sq, ← hsum3.tsum_sub hsum4]
  have hcomb : (∑' p : ℤ × ℤ, (Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) -
      (-1 : ℝ) ^ (p.1 + p.2) * Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)))) =
      ∑' p : {p : ℤ × ℤ // ¬ Even (p.1 + p.2)}, 2 * Real.exp (-t * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2)) := by
    rw [tsum_split_pred (fun p : ℤ × ℤ => Even (p.1 + p.2)) (hsum3.sub hsum4)]
    have heven0 : (∑' p : {p : ℤ × ℤ // Even (p.1 + p.2)},
        (Real.exp (-t * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2)) -
        (-1 : ℝ) ^ (p.1.1 + p.1.2) * Real.exp (-t * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2)))) = 0 := by
      have h0 : (fun p : {p : ℤ × ℤ // Even (p.1 + p.2)} =>
          (Real.exp (-t * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2)) -
          (-1 : ℝ) ^ (p.1.1 + p.1.2) * Real.exp (-t * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2)))) = fun _ => 0 := by
        ext p
        rw [p.2.neg_one_zpow]; ring
      rw [h0, tsum_zero]
    rw [heven0, zero_add]
    congr 1; ext p
    have hodd : Odd (p.1.1 + p.1.2) := Int.not_even_iff_odd.mp p.2
    rw [hodd.neg_one_zpow]; ring
  rw [hcomb, ← Equiv.tsum_eq eOdd, tsum_mul_left]
  congr 1
  rw [sq, theta2, hs22.tsum_mul_tsum hs22 hprod22]
  congr 1; ext jk
  simp only [eOdd, Equiv.coe_fn_mk, Int.cast_add, Int.cast_sub, Int.cast_one]
  rw [← Real.exp_add]; congr 1; ring

private lemma theta3_mul_theta4 (t : ℝ) (ht : 0 < t) :
    theta3 t * theta4 t = theta4 (2 * t) ^ 2 := by
  have hs3 := summable_theta3 t ht
  have hs4 := summable_theta4 t ht
  have hs42 := summable_theta4 (2 * t) (by linarith)
  have hs32 := summable_theta3 (2 * t) (by linarith)
  have hprod3 := hs3.mul_of_nonneg hs3 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hprod32 := hs32.mul_of_nonneg hs32 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hprod : Summable (fun p : ℤ × ℤ =>
      Real.exp (-t * (p.1 : ℝ) ^ 2) * ((-1 : ℝ) ^ p.2 * Real.exp (-t * (p.2 : ℝ) ^ 2))) := by
    refine Summable.of_norm_bounded hprod3 (fun p => ?_)
    simp only [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le, le_refl]
  have hsum_term : Summable (fun p : ℤ × ℤ => (-1 : ℝ) ^ p.2 * Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) := by
    refine hprod.congr (fun p => ?_)
    rw [mul_left_comm, ← Real.exp_add]
    congr 2; ring
  rw [theta3, theta4, hs3.tsum_mul_tsum hs4 hprod]
  have heq_f : (∑' p : ℤ × ℤ, Real.exp (-t * (p.1 : ℝ) ^ 2) * ((-1 : ℝ) ^ p.2 * Real.exp (-t * (p.2 : ℝ) ^ 2))) =
      ∑' p : ℤ × ℤ, (-1 : ℝ) ^ p.2 * Real.exp (-t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    congr 1; ext p
    rw [mul_left_comm, ← Real.exp_add]
    congr 2; ring
  rw [heq_f, tsum_split_pred (fun p : ℤ × ℤ => Even (p.1 + p.2)) hsum_term]
  have hodd0 : (∑' p : {p : ℤ × ℤ // ¬ Even (p.1 + p.2)},
      (-1 : ℝ) ^ p.1.2 * Real.exp (-t * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2))) = 0 := by
    let sw : {p : ℤ × ℤ // ¬ Even (p.1 + p.2)} ≃
        {p : ℤ × ℤ // ¬ Even (p.1 + p.2)} :=
      { toFun := fun p => ⟨(p.1.2, p.1.1), by
          intro h; exact p.2 (by simpa [add_comm] using h)⟩
        invFun := fun p => ⟨(p.1.2, p.1.1), by
          intro h; exact p.2 (by simpa [add_comm] using h)⟩
        left_inv := fun p => by cases p; rfl
        right_inv := fun p => by cases p; rfl }
    have hneg : (∑' p : {p : ℤ × ℤ // ¬ Even (p.1 + p.2)},
        (-1 : ℝ) ^ p.1.2 * Real.exp (-t * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2))) =
        -(∑' p : {p : ℤ × ℤ // ¬ Even (p.1 + p.2)},
        (-1 : ℝ) ^ p.1.2 * Real.exp (-t * ((p.1.1 : ℝ) ^ 2 + (p.1.2 : ℝ) ^ 2))) := by
      conv_lhs => rw [← Equiv.tsum_eq sw]
      rw [← tsum_neg]
      congr 1; ext p
      have hodd : Odd (p.1.1 + p.1.2) := Int.not_even_iff_odd.mp p.2
      have hsign : (-1 : ℝ) ^ p.1.1 = -((-1 : ℝ) ^ p.1.2) := by
        have h1 : (-1 : ℝ) ^ (p.1.1 + p.1.2) = -1 := hodd.neg_one_zpow
        rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)] at h1
        have hsq : ((-1 : ℝ) ^ p.1.2) * ((-1 : ℝ) ^ p.1.2) = 1 := by
          rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
          have hev : Even (p.1.2 + p.1.2) := ⟨p.1.2, rfl⟩
          exact hev.neg_one_zpow
        linear_combination ((-1 : ℝ) ^ p.1.2) * h1 - ((-1 : ℝ) ^ p.1.1) * hsq
      simp only [sw, Equiv.coe_fn_mk]
      rw [hsign, add_comm ((p.1.2 : ℝ) ^ 2)]
      ring
    linarith
  rw [hodd0, add_zero, ← Equiv.tsum_eq eEven]
  have hprod2 : Summable (fun jk : ℤ × ℤ =>
      ((-1 : ℝ) ^ jk.1 * Real.exp (-(2 * t) * (jk.1 : ℝ) ^ 2)) *
      ((-1 : ℝ) ^ jk.2 * Real.exp (-(2 * t) * (jk.2 : ℝ) ^ 2))) := by
    refine Summable.of_norm_bounded hprod32 (fun jk => ?_)
    simp only [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le, le_refl]
  rw [sq, theta4, hs42.tsum_mul_tsum hs42 hprod2]
  congr 1; ext jk
  simp only [eEven, Equiv.coe_fn_mk, Int.cast_add, Int.cast_sub]
  have hz : (-1 : ℝ) ^ (jk.1 - jk.2) = (-1 : ℝ) ^ jk.1 * (-1 : ℝ) ^ jk.2 := by
    have hsq : ((-1 : ℝ) ^ jk.2) * ((-1 : ℝ) ^ jk.2) = 1 := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
      have hev : Even (jk.2 + jk.2) := ⟨jk.2, rfl⟩
      exact hev.neg_one_zpow
    have hinv : ((-1 : ℝ) ^ jk.2)⁻¹ = (-1 : ℝ) ^ jk.2 :=
      inv_eq_of_mul_eq_one_right hsq
    rw [zpow_sub₀ (by norm_num : (-1 : ℝ) ≠ 0), div_eq_mul_inv, hinv]
  have hre : Real.exp (-(2 * t) * (jk.1 : ℝ) ^ 2) * Real.exp (-(2 * t) * (jk.2 : ℝ) ^ 2) =
      Real.exp (-t * (((jk.1 : ℝ) + (jk.2 : ℝ)) ^ 2 + ((jk.1 : ℝ) - (jk.2 : ℝ)) ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hz]
  linear_combination -((-1 : ℝ) ^ jk.1 * (-1 : ℝ) ^ jk.2) * hre

private lemma theta3_fourth_eq (t : ℝ) (ht : 0 < t) :
    theta3 t ^ 4 = theta2 t ^ 4 + theta4 t ^ 4 := by
  have ht2 : 0 < t / 2 := by linarith
  have h1 := theta3_sq_add_theta4_sq (t / 2) ht2
  have h2 := theta3_sq_sub_theta4_sq (t / 2) ht2
  have h3 := theta3_mul_theta4 (t / 2) ht2
  have h2t : 2 * (t / 2) = t := by ring
  rw [h2t] at h1 h2 h3
  have ha : theta3 t ^ 2 + theta2 t ^ 2 = theta3 (t / 2) ^ 2 := by linarith
  have hb : theta3 t ^ 2 - theta2 t ^ 2 = theta4 (t / 2) ^ 2 := by linarith
  have hsub : theta3 t ^ 4 - theta2 t ^ 4 = theta4 t ^ 4 := by
    calc theta3 t ^ 4 - theta2 t ^ 4
        = (theta3 t ^ 2 + theta2 t ^ 2) * (theta3 t ^ 2 - theta2 t ^ 2) := by ring
      _ = theta3 (t / 2) ^ 2 * theta4 (t / 2) ^ 2 := by rw [ha, hb]
      _ = (theta3 (t / 2) * theta4 (t / 2)) ^ 2 := by ring
      _ = (theta4 t ^ 2) ^ 2 := by rw [h3]
      _ = theta4 t ^ 4 := by ring
  linarith

private lemma theta3_pi_sq_eq :
    theta3 Real.pi ^ 2 = Real.sqrt 2 * theta4 Real.pi ^ 2 := by
  have h4 := theta3_fourth_eq Real.pi Real.pi_pos
  rw [← theta4_pi_eq_theta2_pi] at h4
  have hsq : (theta3 Real.pi ^ 2) ^ 2 = (Real.sqrt 2 * theta4 Real.pi ^ 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hpos1 : 0 ≤ theta3 Real.pi ^ 2 := sq_nonneg _
  have hpos2 : 0 ≤ Real.sqrt 2 * theta4 Real.pi ^ 2 := mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  nlinarith

/-! ### Part 4: Symmetric AGM integral J(a, b) and Landen transformation -/

private noncomputable def J (a b : ℝ) : ℝ :=
  ∫ t : ℝ, (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))⁻¹

private lemma J_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun t : ℝ => (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))⁻¹) := by
  let m := min a b
  have hm : 0 < m := lt_min ha hb
  have hdom : Integrable (fun t : ℝ => (t ^ 2 + m ^ 2)⁻¹) := by
    have h1 : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq
    have h2 : Integrable (fun t : ℝ => m⁻¹ * (1 + (t / m) ^ 2)⁻¹ * m⁻¹) := by
      simpa [div_eq_mul_inv] using (h1.comp_div hm.ne').const_mul (m⁻¹) |>.mul_const (m⁻¹)
    refine h2.congr (Eventually.of_forall (fun t => ?_))
    field_simp [hm.ne']
    ring
  refine hdom.mono' ?_ (Eventually.of_forall (fun t => ?_))
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    have hma : m ^ 2 ≤ a ^ 2 := sq_le_sq' (by linarith [min_le_left a b]) (min_le_left a b)
    have hmb : m ^ 2 ≤ b ^ 2 := sq_le_sq' (by linarith [min_le_right a b]) (min_le_right a b)
    have hpos : 0 < t ^ 2 + m ^ 2 := by positivity
    rw [inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity)) hpos]
    calc t ^ 2 + m ^ 2 = Real.sqrt ((t ^ 2 + m ^ 2) * (t ^ 2 + m ^ 2)) := by
          rw [Real.sqrt_mul_self hpos.le]
      _ ≤ Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)) := by
          apply Real.sqrt_le_sqrt
          nlinarith

private lemma J_self (a : ℝ) (ha : 0 < a) : J a a = Real.pi / a := by
  unfold J
  have h1 : (fun t : ℝ => (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + a ^ 2)))⁻¹) =
      fun t : ℝ => a⁻¹ * (a⁻¹ * (1 + (t / a) ^ 2)⁻¹) := by
    ext t
    rw [Real.sqrt_mul_self (by positivity : 0 ≤ t ^ 2 + a ^ 2)]
    field_simp [ha.ne']
    ring
  rw [h1, integral_const_mul, integral_const_mul]
  rw [Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) a, smul_eq_mul, abs_of_pos ha,
    integral_univ_inv_one_add_sq]
  field_simp [ha.ne']

private lemma J_scale (c a b : ℝ) (hc : 0 < c) :
    J (c * a) (c * b) = c⁻¹ * J a b := by
  unfold J
  have hsub : (∫ t : ℝ, (Real.sqrt ((t ^ 2 + (c * a) ^ 2) * (t ^ 2 + (c * b) ^ 2)))⁻¹) =
      c * ∫ x : ℝ, (Real.sqrt (((c * x) ^ 2 + (c * a) ^ 2) * ((c * x) ^ 2 + (c * b) ^ 2)))⁻¹ := by
    have hcomp := Measure.integral_comp_mul_left
      (fun t : ℝ => (Real.sqrt ((t ^ 2 + (c * a) ^ 2) * (t ^ 2 + (c * b) ^ 2)))⁻¹) c
    rw [smul_eq_mul, abs_inv, abs_of_pos hc] at hcomp
    rw [hcomp]
    field_simp [hc.ne']
  rw [hsub]
  have hsimp : (fun x : ℝ => (Real.sqrt (((c * x) ^ 2 + (c * a) ^ 2) * ((c * x) ^ 2 + (c * b) ^ 2)))⁻¹) =
      fun x : ℝ => c⁻¹ * c⁻¹ * (Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))⁻¹ := by
    ext x
    have hfac : ((c * x) ^ 2 + (c * a) ^ 2) * ((c * x) ^ 2 + (c * b) ^ 2) =
        (c ^ 2) ^ 2 * ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)) := by ring
    rw [hfac, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg c), mul_inv]
    field_simp [hc.ne']
  rw [hsimp, integral_const_mul]
  field_simp [hc.ne']

private lemma J_mono_bounds (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    Real.pi / a ≤ J a b ∧ J a b ≤ Real.pi / b := by
  rw [← J_self a ha, ← J_self b hb]
  constructor
  · refine integral_mono (J_integrable a a ha ha) (J_integrable a b ha hb) (fun t => ?_)
    rw [inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by positivity))]
    apply Real.sqrt_le_sqrt
    have hsq : b ^ 2 ≤ a ^ 2 := sq_le_sq' (by linarith) hba
    nlinarith
  · refine integral_mono (J_integrable a b ha hb) (J_integrable b b hb hb) (fun t => ?_)
    rw [inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by positivity))]
    apply Real.sqrt_le_sqrt
    have hsq : b ^ 2 ≤ a ^ 2 := sq_le_sq' (by linarith) hba
    nlinarith

private lemma J_eq_two_mul_Ioi (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    J a b = 2 * ∫ t in Set.Ioi (0 : ℝ), (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))⁻¹ := by
  unfold J
  have hint := J_integrable a b ha hb
  have hunion : (Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ)) = Set.univ := Set.Iic_union_Ioi
  have hdisj : Disjoint (Set.Iic (0 : ℝ)) (Set.Ioi (0 : ℝ)) := Set.Iic_disjoint_Ioi le_rfl
  rw [← setIntegral_univ, ← hunion,
    setIntegral_union hdisj measurableSet_Ioi hint.integrableOn hint.integrableOn]
  have hneg : (∫ t in Set.Iic (0 : ℝ), (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))⁻¹) =
      ∫ t in Set.Ioi (0 : ℝ), (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))⁻¹ := by
    rw [← restrict_Iio_eq_restrict_Iic]
    have himg : (fun x : ℝ => -x) '' Set.Ioi (0 : ℝ) = Set.Iio (0 : ℝ) := by
      ext y; simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio]
      constructor
      · rintro ⟨x, hx, rfl⟩; linarith
      · intro hy; exact ⟨-y, by linarith, neg_neg y⟩
    rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (hasDerivAt_neg x).hasDerivWithinAt) (neg_injective.injOn)]
    congr 1; ext t; simp
  rw [hneg]; ring

private lemma J_landen (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    J ((a + b) / 2) (Real.sqrt (a * b)) = J a b := by
  let u : ℝ → ℝ := fun t => (t - a * b / t) / 2
  let u' : ℝ → ℝ := fun t => (1 + a * b / t ^ 2) / 2
  have hu' : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt u (u' t) (Set.Ioi 0) t := by
    intro t ht
    have ht0 : t ≠ 0 := (Set.mem_Ioi.mp ht).ne'
    have h1 : HasDerivAt (fun x : ℝ => a * b / x) (-(a * b) / t ^ 2) t := by
      have hinv := ((hasDerivAt_inv ht0).const_mul (a * b)).congr_deriv (by ring : a * b * -(t ^ 2)⁻¹ = -(a * b) / t ^ 2)
      have hfn : (fun x : ℝ => a * b * x⁻¹) = (fun x : ℝ => a * b / x) := by
        ext x; rw [div_eq_mul_inv]
      rwa [hfn] at hinv
    have h2 : HasDerivAt u (u' t) t := by
      exact (((hasDerivAt_id t).sub h1).div_const 2).congr_deriv (by dsimp [u']; ring)
    exact h2.hasDerivWithinAt
  have hu_inj : Set.InjOn u (Set.Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := Set.mem_Ioi.mp hx
    have hy0 : 0 < y := Set.mem_Ioi.mp hy
    have h1 : x - a * b / x = y - a * b / y := by dsimp [u] at hxy; linarith
    have h2 : (x - y) * (x * y + a * b) = 0 := by
      have h3 : (x - a * b / x) * (x * y) = (y - a * b / y) * (x * y) := by rw [h1]
      field_simp [hx0.ne', hy0.ne'] at h3
      linarith
    rcases mul_eq_zero.mp h2 with hxy' | hpos
    · linarith
    · nlinarith [mul_pos hx0 hy0, mul_pos ha hb]
  have hu_img : u '' Set.Ioi (0 : ℝ) = Set.univ := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_univ, iff_true]
    let t := y + Real.sqrt (y ^ 2 + a * b)
    have hdisc : 0 < y ^ 2 + a * b := by positivity
    have hsqrt_gt : |y| < Real.sqrt (y ^ 2 + a * b) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg y) (by linarith [mul_pos ha hb])
    have ht : 0 < t := by
      dsimp [t]
      have := neg_abs_le y
      linarith
    refine ⟨t, ht, ?_⟩
    dsimp [u, t]
    have hsq : Real.sqrt (y ^ 2 + a * b) ^ 2 = y ^ 2 + a * b := Real.sq_sqrt hdisc.le
    have ht0 : y + Real.sqrt (y ^ 2 + a * b) ≠ 0 := ht.ne'
    field_simp [ht0]
    nlinarith [hsq]
  rw [J_eq_two_mul_Ioi a b ha hb]
  unfold J
  rw [← setIntegral_univ, ← hu_img,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hu' hu_inj,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : 0 < t := Set.mem_Ioi.mp ht
  have hu'pos : 0 < u' t := by dsimp [u']; positivity
  rw [smul_eq_mul, abs_of_pos hu'pos]
  have h1 : (u t) ^ 2 + ((a + b) / 2) ^ 2 = (t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2) / (4 * t ^ 2) := by
    dsimp [u]; field_simp [ht0.ne']; ring
  have h2 : (u t) ^ 2 + (Real.sqrt (a * b)) ^ 2 = (t ^ 2 + a * b) ^ 2 / (4 * t ^ 2) := by
    rw [Real.sq_sqrt (mul_pos ha hb).le]
    dsimp [u]; field_simp [ht0.ne']; ring
  rw [h1, h2]
  have hprod : (t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2) / (4 * t ^ 2) * ((t ^ 2 + a * b) ^ 2 / (4 * t ^ 2)) =
      ((t ^ 2 + a * b) / (4 * t ^ 2)) ^ 2 * ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)) := by
    field_simp [ht0.ne']
  rw [hprod, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ (t ^ 2 + a * b) / (4 * t ^ 2))]
  dsimp [u']
  have hden : Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hnum : t ^ 2 + a * b ≠ 0 := by positivity
  field_simp [ht0.ne', hden, hnum]
  norm_num

private lemma J_theta_eq_pi :
    J (theta3 Real.pi ^ 2) (theta4 Real.pi ^ 2) = Real.pi := by
  let a : ℕ → ℝ := fun k => theta3 ((2 : ℝ) ^ k * Real.pi) ^ 2
  let b : ℕ → ℝ := fun k => theta4 ((2 : ℝ) ^ k * Real.pi) ^ 2
  have ha_pos : ∀ k, 0 < a k := fun k => sq_pos_of_pos (theta3_pos _ (by positivity))
  have hb_pos : ∀ k, 0 < b k := fun k => sq_pos_of_pos (theta4_pos _ (by positivity))
  have hba : ∀ k, b k ≤ a k := by
    intro k
    have ht : 0 < (2 : ℝ) ^ k * Real.pi := by positivity
    have h := theta3_sq_sub_theta4_sq ((2 : ℝ) ^ k * Real.pi) ht
    have hnonneg : 0 ≤ 2 * theta2 (2 * ((2 : ℝ) ^ k * Real.pi)) ^ 2 := by positivity
    dsimp [a, b]; linarith
  have hconst : ∀ k, J (a k) (b k) = J (a 0) (b 0) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have ht : 0 < (2 : ℝ) ^ k * Real.pi := by positivity
      have hpow : (2 : ℝ) ^ (k + 1) * Real.pi = 2 * ((2 : ℝ) ^ k * Real.pi) := by ring
      have ha_step : a (k + 1) = (a k + b k) / 2 := by
        dsimp [a, b]
        rw [hpow]
        have := theta3_sq_add_theta4_sq ((2 : ℝ) ^ k * Real.pi) ht
        linarith
      have hb_step : b (k + 1) = Real.sqrt (a k * b k) := by
        dsimp [a, b]
        rw [hpow, ← theta3_mul_theta4 ((2 : ℝ) ^ k * Real.pi) ht]
        rw [← mul_pow, Real.sqrt_sq (mul_pos (theta3_pos _ ht) (theta4_pos _ ht)).le]
      rw [ha_step, hb_step, J_landen (a k) (b k) (ha_pos k) (hb_pos k), ih]
  have h2k : Tendsto (fun k : ℕ => (2 : ℝ) ^ k * Real.pi) atTop atTop := by
    have h1 : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    exact h1.atTop_mul_const Real.pi_pos
  have ha_lim : Tendsto a atTop (𝓝 1) := by
    simpa [a] using (tendsto_theta3_atTop.comp h2k).pow 2
  have hb_lim : Tendsto b atTop (𝓝 1) := by
    simpa [b] using (tendsto_theta4_atTop.comp h2k).pow 2
  have hlow : Tendsto (fun k => Real.pi / a k) atTop (𝓝 Real.pi) := by
    have h : Tendsto (fun k => Real.pi / a k) atTop (𝓝 (Real.pi / 1)) :=
      tendsto_const_nhds.div ha_lim one_ne_zero
    simpa using h
  have hhigh : Tendsto (fun k => Real.pi / b k) atTop (𝓝 Real.pi) := by
    have h : Tendsto (fun k => Real.pi / b k) atTop (𝓝 (Real.pi / 1)) :=
      tendsto_const_nhds.div hb_lim one_ne_zero
    simpa using h
  have hlim : Tendsto (fun _ : ℕ => J (a 0) (b 0)) atTop (𝓝 Real.pi) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hhigh ?_ ?_
    · intro k; rw [← hconst k]; exact (J_mono_bounds (a k) (b k) (ha_pos k) (hb_pos k) (hba k)).1
    · intro k; rw [← hconst k]; exact (J_mono_bounds (a k) (b k) (ha_pos k) (hb_pos k) (hba k)).2
  have heq : J (a 0) (b 0) = Real.pi := tendsto_nhds_unique tendsto_const_nhds hlim
  simpa [a, b] using heq

/-! ### Part 5: Beta/Gamma evaluation of J(sqrt 2, 1) -/

private lemma beta_eval_eq_two_mul_J :
    (∫ y in Set.Ioo (0 : ℝ) 1, y ^ (-(3 / 4 : ℝ)) * (1 - y) ^ (-(1 / 2 : ℝ))) =
      2 * J (Real.sqrt 2) 1 := by
  let g : ℝ → ℝ := fun t => ((t ^ 2 + 1) ^ 2)⁻¹
  let g' : ℝ → ℝ := fun t => -4 * t / (t ^ 2 + 1) ^ 3
  have hg' : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt g (g' t) (Set.Ioi 0) t := by
    intro t _
    have hpos : t ^ 2 + 1 ≠ 0 := by positivity
    have hsq : HasDerivAt (fun x : ℝ => x ^ 2 + 1) (2 * t) t := by
      simpa using ((hasDerivAt_pow 2 t).add_const (1 : ℝ))
    have h1 : HasDerivAt (fun x : ℝ => (x ^ 2 + 1) ^ 2) (4 * t * (t ^ 2 + 1)) t :=
      (hsq.pow 2).congr_deriv (by ring)
    have h2 : HasDerivAt g (g' t) t :=
      (h1.inv (pow_ne_zero 2 hpos)).congr_deriv (by dsimp [g']; field_simp [hpos])
    exact h2.hasDerivWithinAt
  have hg_inj : Set.InjOn g (Set.Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := Set.mem_Ioi.mp hx
    have hy0 : 0 < y := Set.mem_Ioi.mp hy
    have h1 : (x ^ 2 + 1) ^ 2 = (y ^ 2 + 1) ^ 2 := inv_injective hxy
    have h2 : x ^ 2 + 1 = y ^ 2 + 1 := by nlinarith
    nlinarith
  have hg_img : g '' Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) 1 := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Ioo]
    constructor
    · rintro ⟨t, ht, rfl⟩
      dsimp [g]
      have hgt : 1 < (t ^ 2 + 1) ^ 2 := by nlinarith
      exact ⟨by positivity, inv_lt_one_of_one_lt₀ hgt⟩
    · rintro ⟨hy0, hy1⟩
      have hinv : 1 < y⁻¹ := one_lt_inv₀ hy0 |>.mpr hy1
      have hsqrt_gt : 1 < Real.sqrt y⁻¹ := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_lt_sqrt zero_le_one hinv
      let t := Real.sqrt (Real.sqrt y⁻¹ - 1)
      have ht : 0 < t := Real.sqrt_pos.mpr (by linarith)
      refine ⟨t, ht, ?_⟩
      dsimp [g, t]
      rw [Real.sq_sqrt (by linarith : 0 ≤ Real.sqrt y⁻¹ - 1), sub_add_cancel,
        Real.sq_sqrt (by positivity : 0 ≤ y⁻¹), inv_inv]
  rw [← hg_img, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hg' hg_inj]
  rw [J_eq_two_mul_Ioi (Real.sqrt 2) 1 (Real.sqrt_pos.mpr (by norm_num)) zero_lt_one]
  rw [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : 0 < t := Set.mem_Ioi.mp ht
  have h1 : 0 < t ^ 2 + 1 := by positivity
  have h2 : 0 < t ^ 2 + 2 := by positivity
  have hg'abs : |g' t| = 4 * t / (t ^ 2 + 1) ^ 3 := by
    dsimp [g']
    rw [abs_div, abs_of_pos (by positivity : 0 < (t ^ 2 + 1) ^ 3), abs_mul,
      abs_of_neg (by norm_num : (-4 : ℝ) < 0), abs_of_pos ht0]
    ring
  rw [smul_eq_mul, hg'abs]
  have hpow1 : (g t) ^ (-(3 / 4 : ℝ)) = (t ^ 2 + 1) * Real.sqrt (t ^ 2 + 1) := by
    dsimp [g]
    rw [Real.inv_rpow (sq_nonneg _), Real.rpow_neg (sq_nonneg _), inv_inv,
      ← Real.rpow_natCast (t ^ 2 + 1) 2, ← Real.rpow_mul h1.le]
    have hexp : ((2 : ℕ) : ℝ) * (3 / 4 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [hexp, Real.rpow_add h1, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have h1sub : 1 - g t = (t ^ 2 * (t ^ 2 + 2)) / (t ^ 2 + 1) ^ 2 := by
    dsimp [g]; field_simp [h1.ne']; ring
  have hpow2 : (1 - g t) ^ (-(1 / 2 : ℝ)) = (t ^ 2 + 1) / (t * Real.sqrt (t ^ 2 + 2)) := by
    rw [h1sub, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      Real.sqrt_div (by positivity), Real.sqrt_sq h1.le,
      Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht0.le, inv_div]
  rw [hpow1, hpow2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_pow]
  rw [Real.sqrt_mul (by positivity : 0 ≤ t ^ 2 + 2)]
  have hs1 : Real.sqrt (t ^ 2 + 1) ≠ 0 := (Real.sqrt_pos.mpr h1).ne'
  have hs2 : Real.sqrt (t ^ 2 + 2) ≠ 0 := (Real.sqrt_pos.mpr h2).ne'
  field_simp [ht0.ne', h1.ne', hs1, hs2]
  ring_nf
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + t ^ 2)]

private lemma real_beta_quarter_half :
    (∫ y in Set.Ioo (0 : ℝ) 1, y ^ (-(3 / 4 : ℝ)) * (1 - y) ^ (-(1 / 2 : ℝ))) =
      Real.sqrt 2 * Real.pi ^ (3 / 2 : ℝ) / Real.Gamma (3 / 4) ^ 2 := by
  have hs : 0 < ((1 / 4 : ℝ) : ℂ).re := by norm_num
  have ht : 0 < ((1 / 2 : ℝ) : ℂ).re := by norm_num
  have hbg := Complex.Gamma_mul_Gamma_eq_betaIntegral hs ht
  have hbeta_eq : Complex.betaIntegral (1 / 4 : ℂ) (1 / 2 : ℂ) =
      ((∫ y in Set.Ioo (0 : ℝ) 1, y ^ (-(3 / 4 : ℝ)) * (1 - y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      ← restrict_Ioo_eq_restrict_Ioc]
    trans (∫ y in Set.Ioo (0 : ℝ) 1, ((y ^ (-(3 / 4 : ℝ)) * (1 - y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
    · refine setIntegral_congr_fun measurableSet_Ioo (fun y hy => ?_)
      have hy0 : 0 ≤ y := hy.1.le
      have hy1 : 0 ≤ 1 - y := by linarith [hy.2]
      have h1 : (1 / 4 : ℂ) - 1 = ((-(3 / 4 : ℝ)) : ℂ) := by norm_num
      have h2 : (1 / 2 : ℂ) - 1 = ((-(1 / 2 : ℝ)) : ℂ) := by norm_num
      rw [h1, h2, ← Complex.ofReal_neg, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hy0,
        ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_cpow hy1,
        ← Complex.ofReal_mul]
    · exact integral_ofReal
  have hadd : ((1 / 4 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) = ((3 / 4 : ℝ) : ℂ) := by push_cast; norm_num
  have hcast : ((Real.Gamma (1 / 4) * Real.Gamma (1 / 2) : ℝ) : ℂ) =
      ((Real.Gamma (3 / 4) * ∫ y in Set.Ioo (0 : ℝ) 1, y ^ (-(3 / 4 : ℝ)) * (1 - y) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal]
    have h1 : ((1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by norm_num
    have h2 : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
    rw [← hbeta_eq, ← hadd, ← h1, ← h2]
    exact hbg
  have hreal := Complex.ofReal_injective hcast
  have href := Real.Gamma_mul_Gamma_one_sub (1 / 4 : ℝ)
  have h1sub : (1 : ℝ) - 1 / 4 = 3 / 4 := by norm_num
  have hsin : Real.sin (Real.pi * (1 / 4 : ℝ)) = Real.sqrt 2 / 2 := by
    rw [show Real.pi * (1 / 4 : ℝ) = Real.pi / 4 by ring, Real.sin_pi_div_four]
  rw [h1sub, hsin] at href
  have hG34 : 0 < Real.Gamma (3 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  have hG12 : Real.Gamma (1 / 2) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have hG14 : Real.Gamma (1 / 4) = Real.sqrt 2 * Real.pi / Real.Gamma (3 / 4) := by
    have hsq2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have h1 : Real.Gamma (1 / 4) * Real.Gamma (3 / 4) = Real.sqrt 2 * Real.pi := by
      rw [href]
      field_simp [hsq2]
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp [hG34.ne']
    linarith
  have hpi32 : Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hG14, hG12] at hreal
  rw [hpi32]
  field_simp [hG34.ne'] at hreal ⊢
  linarith

end OMA_oeis_a000122

theorem OMA.solution : type_of% @OMA.S_oeis_a000122.main := by
  rw [OMA_oeis_a000122.sum_a_eq_theta3_pi]
  have hJpi := OMA_oeis_a000122.J_theta_eq_pi
  have hth3_pos : 0 < OMA_oeis_a000122.theta3 Real.pi := OMA_oeis_a000122.theta3_pos Real.pi Real.pi_pos
  have hth4_pos : 0 < OMA_oeis_a000122.theta4 Real.pi := OMA_oeis_a000122.theta4_pos Real.pi Real.pi_pos
  have hratio := OMA_oeis_a000122.theta3_pi_sq_eq
  have hscale := OMA_oeis_a000122.J_scale (OMA_oeis_a000122.theta4 Real.pi ^ 2) (Real.sqrt 2) 1 (sq_pos_of_pos hth4_pos)
  rw [mul_one, mul_comm (OMA_oeis_a000122.theta4 Real.pi ^ 2) (Real.sqrt 2), ← hratio] at hscale
  have hJsq2 : OMA_oeis_a000122.J (Real.sqrt 2) 1 =
      Real.sqrt 2 * Real.pi ^ (3 / 2 : ℝ) / (2 * Real.Gamma (3 / 4) ^ 2) := by
    have h1 := OMA_oeis_a000122.beta_eval_eq_two_mul_J
    have h2 := OMA_oeis_a000122.real_beta_quarter_half
    have hG34 : Real.Gamma (3 / 4) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    rw [h1] at h2
    field_simp [hG34] at h2 ⊢
    linarith
  have hth4_sq : OMA_oeis_a000122.theta4 Real.pi ^ 2 =
      Real.sqrt 2 * Real.sqrt Real.pi / (2 * Real.Gamma (3 / 4) ^ 2) := by
    have h1 : Real.pi = (OMA_oeis_a000122.theta4 Real.pi ^ 2)⁻¹ * OMA_oeis_a000122.J (Real.sqrt 2) 1 :=
      hJpi.symm.trans hscale
    rw [hJsq2] at h1
    have hpi32 : Real.pi ^ (3 / 2 : ℝ) = Real.pi * Real.sqrt Real.pi := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add Real.pi_pos,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [hpi32] at h1
    have hG34 : Real.Gamma (3 / 4) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    have hth4ne : OMA_oeis_a000122.theta4 Real.pi ^ 2 ≠ 0 := (sq_pos_of_pos hth4_pos).ne'
    field_simp [hG34, hth4ne, Real.pi_ne_zero] at h1 ⊢
    nlinarith [Real.pi_pos]
  have hth3_sq : OMA_oeis_a000122.theta3 Real.pi ^ 2 =
      Real.sqrt Real.pi / Real.Gamma (3 / 4) ^ 2 := by
    rw [hratio, hth4_sq]
    have hG34 : Real.Gamma (3 / 4) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    field_simp [hG34]
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hrhs_sq : (Real.pi ^ (1 / 4 : ℝ) / Real.Gamma (3 / 4)) ^ 2 =
      Real.sqrt Real.pi / Real.Gamma (3 / 4) ^ 2 := by
    rw [div_pow, ← Real.rpow_natCast (Real.pi ^ (1 / 4 : ℝ)) 2,
      ← Real.rpow_mul Real.pi_pos.le]
    have : (1 / 4 : ℝ) * (2 : ℕ) = 1 / 2 := by norm_num
    rw [this, ← Real.sqrt_eq_rpow]
  have hrhs_pos : 0 < Real.pi ^ (1 / 4 : ℝ) / Real.Gamma (3 / 4) :=
    div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by norm_num))
  nlinarith

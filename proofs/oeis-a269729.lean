import OMAStatements.S_oeis_a269729

-- Credit: @kumagi

namespace OMA.S_oeis_a269729

private noncomputable def phi : ℝ := Real.goldenRatio
private lemma phi_gt_one : 1 < phi := Real.one_lt_goldenRatio
private lemma phi_pos : 0 < phi := Real.goldenRatio_pos
private lemma phi_lt_two : phi < 2 := Real.goldenRatio_lt_two
private lemma phi_sq : phi ^ 2 = phi + 1 := Real.goldenRatio_sq

private lemma phi_inv : phi - 1 = phi⁻¹ := by
  rw [← one_div]
  apply (eq_div_iff (ne_of_gt phi_pos)).mpr
  nlinarith [phi_sq]

private def FibLike (f : ℤ → ℤ) : Prop := ∀ k, f (k + 1) = f k + f (k - 1)

private lemma row_rec (r : ℕ) : FibLike (W r) := by
  intro k
  have h₁ := Int.fib_add_two k
  have h₂ := Int.fib_add_two (k - 1)
  rw [show k - 1 + 2 = k + 1 by omega, show k - 1 + 1 = k by omega] at h₂
  simp only [W, show k + 1 + 1 = k + 2 by omega, show k - 1 + 1 = k by omega]
  rw [h₁]
  linear_combination h₂ * (r : ℤ)

private lemma row_prev (r : ℕ) : W r (-1) = r := by
  norm_num [W, Int.fib]

private lemma row_zero (r : ℕ) : W r 0 = ⌊((r : ℝ) + 1) * phi⌋ := by
  simp [W, phi]

private lemma row_next (r : ℕ) : W r 1 = W r 0 + r := by
  simpa [row_prev] using row_rec r 0

private def sign (k : ℤ) : ℤ := k.negOnePow

private lemma sign_add (k l : ℤ) : sign (k + l) = sign k * sign l := by
  simp [sign, Int.negOnePow_add]

private lemma sign_neg (k : ℤ) : sign (-k) = sign k := by simp [sign]

private lemma sign_next (k : ℤ) : sign (k + 1) = -sign k := by
  simp [sign, Int.negOnePow_succ]

private lemma sign_prev (k : ℤ) : sign (k - 1) = -sign k := by
  have h := sign_next (k - 1)
  rw [show k - 1 + 1 = k by omega] at h
  omega

private lemma sign_cases (k : ℤ) : sign k = 1 ∨ sign k = -1 := by
  rcases Int.even_or_odd k with h | h
  · exact Or.inl (by simp [sign, Int.negOnePow_even _ h])
  · exact Or.inr (by simp [sign, Int.negOnePow_odd _ h])

private lemma rev_eq (r : ℕ) (k : ℤ) : rev r k = sign k * W r (-k) := by
  unfold rev sign
  congr 1
  rw [← Int.negOnePow_abs k, Int.abs_eq_natAbs, Int.negOnePow_def, zpow_natCast]
  rfl

private lemma rev_rec (r : ℕ) : FibLike (rev r) := by
  intro k
  have h := row_rec r (-k)
  rw [rev_eq, rev_eq, rev_eq, sign_next, sign_prev,
    show -(k + 1) = -k - 1 by omega, show -(k - 1) = -k + 1 by omega]
  rw [h]
  ring

/-- The two linear coordinates of the adjacent pair `(f (k-1), f k)`. -/
private noncomputable def delta (f : ℤ → ℤ) (k : ℤ) : ℝ :=
  (f k : ℝ) - phi * (f (k - 1) : ℝ)

private noncomputable def gamma (f : ℤ → ℤ) (k : ℤ) : ℝ :=
  (f k : ℝ) + (phi - 1) * (f (k - 1) : ℝ)

private lemma delta_step {f : ℤ → ℤ} (hf : FibLike f) (k : ℤ) :
    delta f (k + 1) = (1 - phi) * delta f k := by
  simp only [delta, show k + 1 - 1 = k by omega, hf k, Int.cast_add]
  linear_combination -(f (k - 1) : ℝ) * phi_sq

private lemma gamma_step {f : ℤ → ℤ} (hf : FibLike f) (k : ℤ) :
    gamma f (k + 1) = phi * gamma f k := by
  simp only [gamma, show k + 1 - 1 = k by omega, hf k, Int.cast_add]
  linear_combination -(f (k - 1) : ℝ) * phi_sq

private lemma scaled_from_zero (f : ℤ → ℝ) (c : ℝ) (hc : c ≠ 0)
    (step : ∀ k, f (k + 1) = c * f k) (k : ℤ) : f k = f 0 * c ^ k := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [step, ih, zpow_add_one₀ hc]
    ring
  | pred n ih =>
    let j : ℤ := -(n : ℤ) - 1
    have hj : j + 1 = -(n : ℤ) := by dsimp [j]; omega
    change f j = f 0 * c ^ j
    apply mul_left_cancel₀ hc
    calc
      c * f j = f (j + 1) := (step j).symm
      _ = f 0 * c ^ (j + 1) := by simpa only [hj] using ih
      _ = c * (f 0 * c ^ j) := by rw [zpow_add_one₀ hc]; ring

private lemma delta_even {f : ℤ → ℤ} (hf : FibLike f) (t : ℤ) :
    delta f (2 * t) = delta f 0 / (phi ^ 2 : ℝ) ^ t := by
  rw [scaled_from_zero (delta f) (1 - phi) (by linarith [phi_gt_one]) (delta_step hf),
    zpow_mul, zpow_ofNat, show 1 - phi = -phi⁻¹ by linarith [phi_inv],
    neg_sq, inv_pow, inv_zpow, div_eq_mul_inv]

private lemma gamma_pos {f : ℤ → ℤ} (hf : FibLike f) (h : 0 < gamma f 0) (k : ℤ) :
    0 < gamma f k := by
  rw [scaled_from_zero (gamma f) phi (ne_of_gt phi_pos) (gamma_step hf)]
  exact mul_pos h (zpow_pos phi_pos _)

private lemma shift_rec {f : ℤ → ℤ} (hf : FibLike f) (s : ℤ) :
    FibLike (fun k => f (k + s)) := by
  intro k
  simpa only [show k + 1 + s = k + s + 1 by omega,
    show k - 1 + s = k + s - 1 by omega] using hf (k + s)

private lemma fiblike_ext {f g : ℤ → ℤ} (hf : FibLike f) (hg : FibLike g)
    (hprev : f (-1) = g (-1)) (hzero : f 0 = g 0) (k : ℤ) : f k = g k := by
  suffices h : f (k - 1) = g (k - 1) ∧ f k = g k from h.2
  induction k using Int.induction_on with
  | zero => exact ⟨hprev, hzero⟩
  | succ n ih =>
    rw [show (n : ℤ) + 1 - 1 = n by omega]
    exact ⟨ih.2, by rw [hf, hg, ih.1, ih.2]⟩
  | pred n ih =>
    refine ⟨?_, ih.1⟩
    have h₁ := hf (-(n : ℤ) - 1)
    have h₂ := hg (-(n : ℤ) - 1)
    rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by omega] at h₁ h₂
    rw [ih.2, ih.1] at h₁
    omega

/-- The row's floor condition places this coordinate in one scaling interval. -/
private lemma row_window (r : ℕ) : delta (W r) 0 ∈ Set.Ioc (phi - 1) phi := by
  have h := Int.floor_eq_iff.mp (row_zero r).symm
  change phi - 1 < delta (W r) 0 ∧ delta (W r) 0 ≤ phi
  norm_num [delta, row_prev]
  constructor <;> nlinarith [h.1, h.2]

private lemma row_gamma (r : ℕ) : 0 < gamma (W r) 0 := by
  have h := (row_window r).1
  norm_num [delta, row_prev] at h
  norm_num [gamma, row_prev]
  have hφ : 0 ≤ (2 * phi - 1) := by linarith [phi_gt_one]
  nlinarith [phi_gt_one, mul_nonneg hφ (Nat.cast_nonneg (α := ℝ) r)]

private lemma rev_coordinates (r : ℕ) : 0 < delta (rev r) 0 ∧ 0 < gamma (rev r) 0 := by
  have hzero : rev r 0 = W r 0 := by simp [rev]
  have hprev : rev r (-1) = -(W r 0 + r) := by norm_num [rev, row_next]
  have h := (row_window r).1
  norm_num [delta, row_prev] at h
  have hb : 0 < (W r 0 : ℝ) := by
    nlinarith [phi_gt_one, mul_nonneg phi_pos.le (Nat.cast_nonneg (α := ℝ) r)]
  constructor
  · norm_num [delta, hzero, hprev]
    have hsum : 0 ≤ (W r 0 : ℝ) + r := by positivity
    nlinarith [mul_nonneg phi_pos.le hsum]
  · norm_num [gamma, hzero, hprev]
    have heq : (W r 0 : ℝ) + (phi - 1) * (-(r : ℝ) + -(W r 0 : ℝ)) =
        (2 - phi) * ((W r 0 : ℝ) - phi * r) := by
      linear_combination -(r : ℝ) * phi_sq
    rw [heq]
    exact mul_pos (sub_pos.mpr phi_lt_two) (by linarith [phi_gt_one])

private lemma phi_gt_one_sq : 1 < phi ^ 2 := by nlinarith [phi_sq, phi_gt_one]

private lemma window_scale : (phi - 1) * phi ^ 2 = phi := by
  rw [pow_two, ← mul_assoc, phi_inv, inv_mul_cancel₀ (ne_of_gt phi_pos), one_mul]

private lemma window_iff {f : ℤ → ℤ} (hf : FibLike f) (t : ℤ) :
    delta f (2 * t) ∈ Set.Ioc (phi - 1) phi ↔
      delta f 0 / (phi - 1) ∈ Set.Ioc ((phi ^ 2 : ℝ) ^ t) ((phi ^ 2 : ℝ) ^ (t + 1)) := by
  have hb : 0 < (phi ^ 2 : ℝ) ^ t := zpow_pos (pow_pos phi_pos _) _
  have hc : 0 < phi - 1 := by linarith [phi_gt_one]
  simp only [Set.mem_Ioc, delta_even hf, zpow_add_one₀ (pow_ne_zero _ (ne_of_gt phi_pos)),
    lt_div_iff₀, div_le_iff₀, hb, hc]
  rw [mul_comm ((phi ^ 2 : ℝ) ^ t) (phi - 1)]
  have hh : (phi ^ 2 : ℝ) ^ t * phi ^ 2 * (phi - 1) = phi * (phi ^ 2 : ℝ) ^ t := by
    rw [mul_assoc, mul_comm (phi ^ 2) (phi - 1), window_scale, mul_comm]
  rw [hh]

/-- Consecutive even shifts divide the coordinate by `phi^2`. -/
private lemma unique_even_window {f : ℤ → ℤ} (hf : FibLike f) (hp : 0 < delta f 0) :
    ∃! t : ℤ, delta f (2 * t) ∈ Set.Ioc (phi - 1) phi := by
  have hδ : 0 < delta f 0 / (phi - 1) := div_pos hp (by linarith [phi_gt_one])
  obtain ⟨t, ht⟩ := exists_mem_Ioc_zpow hδ phi_gt_one_sq
  refine ⟨t, (window_iff hf t).mpr ht, fun q hq => ?_⟩
  have hq' := (window_iff hf q).mp hq
  rcases lt_trichotomy q t with h | h | h
  · have hh := zpow_le_zpow_right₀ phi_gt_one_sq.le (show q + 1 ≤ t by omega)
    exact ((ht.1.trans_le hq'.2).not_ge hh).elim
  · exact h
  · have hh := zpow_le_zpow_right₀ phi_gt_one_sq.le (show t + 1 ≤ q by omega)
    exact ((hq'.1.trans_le ht.2).not_ge hh).elim

private lemma window_is_even {f : ℤ → ℤ} (hf : FibLike f) (hp : 0 < delta f 0)
    (k : ℤ) (h : delta f k ∈ Set.Ioc (phi - 1) phi) : ∃ t : ℤ, k = 2 * t := by
  rcases Int.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact ⟨t, by omega⟩
  · rw [ht, delta_step hf, delta_even hf] at h
    have hnegative : (1 - phi) * (delta f 0 / (phi ^ 2 : ℝ) ^ t) < 0 :=
      mul_neg_of_neg_of_pos (by linarith [phi_gt_one]) (div_pos hp (zpow_pos (pow_pos phi_pos _) _))
    exfalso
    linarith [h.1, phi_gt_one]

private lemma row_of_window {f : ℤ → ℤ} (hf : FibLike f) (s : ℤ)
    (hd : delta f s ∈ Set.Ioc (phi - 1) phi) (hg : 0 < gamma f s) :
    ∃ r : ℕ, ∀ k : ℤ, W r k = f (k + s) := by
  let x : ℤ := f (s - 1)
  let y : ℤ := f s
  change phi - 1 < (y : ℝ) - phi * x ∧ (y : ℝ) - phi * x ≤ phi at hd
  change 0 < (y : ℝ) + (phi - 1) * x at hg
  have hx : 0 ≤ x := by
    by_contra! hneg
    have hx' : (x : ℝ) ≤ -1 := by exact_mod_cast (show x ≤ -1 by omega)
    have hm := mul_le_mul_of_nonneg_left hx' (show 0 ≤ 2 * phi - 1 by linarith [phi_gt_one])
    nlinarith [hd.2, phi_gt_one]
  have hr := Int.toNat_of_nonneg hx
  refine ⟨x.toNat, fiblike_ext (row_rec _) (shift_rec hf s) ?_ ?_⟩
  · rw [row_prev, hr, show -1 + s = s - 1 by omega]
  · rw [row_zero, zero_add, show (x.toNat : ℝ) = (x : ℝ) by exact_mod_cast hr]
    apply Int.floor_eq_iff.mpr
    change (y : ℝ) ≤ ((x : ℝ) + 1) * phi ∧ ((x : ℝ) + 1) * phi < (y : ℝ) + 1
    constructor <;> nlinarith [hd.1, hd.2]

private def matchingRows (n : ℕ) : Set ℕ :=
  {r | ∃ s : ℤ, (∀ k : ℤ, W r k = rev n (k + s)) ∨ (∀ k : ℤ, W r k = -rev n (k + s))}

/-- A reversed row has exactly one representative in the Wythoff array. -/
private lemma unique_match (n : ℕ) : ∃! r : ℕ, r ∈ matchingRows n := by
  have hcoords := rev_coordinates n
  have hrec := rev_rec n
  obtain ⟨t, ht, hu⟩ := unique_even_window hrec hcoords.1
  obtain ⟨r, hr⟩ := row_of_window hrec (2 * t) ht (gamma_pos hrec hcoords.2 _)
  refine ⟨r, ⟨2 * t, Or.inl hr⟩, ?_⟩
  rintro q ⟨s, hq | hq⟩
  · have hd := row_window q
    have he : delta (W q) 0 = delta (rev n) s := by
      simp only [delta, hq, zero_add, zero_sub, show (-1 : ℤ) + s = s - 1 by omega]
    rw [he] at hd
    obtain ⟨j, hj⟩ := window_is_even hrec hcoords.1 s hd
    rw [hj] at hd
    have hs : s = 2 * t := by rw [hj, hu j hd]
    have hq₁ := hq (-1)
    have hr₁ := hr (-1)
    rw [hs, row_prev] at hq₁
    rw [row_prev] at hr₁
    omega
  · have hg := row_gamma q
    have he : gamma (W q) 0 = -gamma (rev n) s := by
      simp only [gamma, hq, zero_add, zero_sub, show (-1 : ℤ) + s = s - 1 by omega, Int.cast_neg]
      ring
    rw [he] at hg
    have hpos := gamma_pos hrec hcoords.2 s
    linarith

private lemma matches_symm {n r : ℕ} (h : r ∈ matchingRows n) : n ∈ matchingRows r := by
  obtain ⟨s, h | h⟩ := h
  · have hback (k : ℤ) : rev r (k + s) = sign s * W n k := by
      rw [rev_eq, h, show -(k + s) + s = -k by omega, rev_eq, neg_neg, sign_add, sign_neg]
      rcases sign_cases k with hk | hk <;> simp [hk]
    rcases sign_cases s with hs | hs
    · exact ⟨s, Or.inl (fun k => by simpa [hs] using (hback k).symm)⟩
    · exact ⟨s, Or.inr (fun k => by simp [hback, hs])⟩
  · have hback (k : ℤ) : rev r (k + s) = -(sign s * W n k) := by
      rw [rev_eq, h, show -(k + s) + s = -k by omega, rev_eq, neg_neg, sign_add, sign_neg]
      rcases sign_cases k with hk | hk <;> simp [hk]
    rcases sign_cases s with hs | hs
    · exact ⟨s, Or.inr (fun k => by simp [hback, hs])⟩
    · exact ⟨s, Or.inl (fun k => by simp [hback, hs])⟩

private lemma a_mem (n : ℕ) : a n ∈ matchingRows n := by
  obtain ⟨r, hr, _⟩ := unique_match n
  exact Nat.sInf_mem ⟨r, hr⟩

theorem involutive : ∀ n : ℕ, a (a n) = n := by
  intro n
  obtain ⟨r, _, hr⟩ := unique_match (a n)
  exact (hr _ (a_mem (a n))).trans (hr n (matches_symm (a_mem n))).symm

end OMA.S_oeis_a269729

theorem OMA.solution : type_of% @OMA.S_oeis_a269729.main :=
  OMA.S_oeis_a269729.involutive

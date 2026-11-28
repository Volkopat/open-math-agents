import OMAStatements.S_oeis_a000111

open OMA.S_oeis_a000111

namespace FractionLimit

private noncomputable def middle (x u : ℝ) := x / (2 + x/u)
private noncomputable def step (x : ℝ) (k : ℕ) (v : ℝ) := 4*(k:ℝ)+1 - x / (2 - x / (4*(k:ℝ)+3+v))

private theorem middle_nonneg {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) :
    0 ≤ middle x u := by unfold middle; positivity

private theorem middle_le_zero_arg {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) :
    middle x u ≤ middle x 0 := by
  unfold middle
  rw [div_zero, add_zero]
  exact div_le_div_of_nonneg_left hx (by norm_num) (by linarith [div_nonneg hx hu])

private theorem middle_mono {x u v : ℝ} (hx : 0 ≤ x) (hu : 0 < u) (huv : u ≤ v) :
    middle x u ≤ middle x v := by
  have hv := hu.trans_le huv
  have h := div_le_div_of_nonneg_left hx hu huv
  unfold middle
  exact div_le_div_of_nonneg_left hx (by positivity) (by linarith)

private theorem inner_le_one {x v : ℝ} (hx : x ≤ 2) (k : ℕ) (hv : 0 ≤ v) :
    x / (4*(k:ℝ)+3+v) ≤ 1 := by
  have hk : 0 ≤ (k:ℝ) := by positivity
  apply (div_le_one (by linarith : 0 < 4*(k:ℝ)+3+v)).2
  linarith

private theorem step_lower {x v : ℝ} (hx : x ≤ 2) (k : ℕ) (hv : 0 ≤ v) :
    4*(k:ℝ)-1 ≤ step x k v := by
  have hi := inner_le_one hx k hv
  have hd : 0 < 2 - x / (4*(k:ℝ)+3+v) := by linarith
  have he : x / (2 - x / (4*(k:ℝ)+3+v)) ≤ 2 :=
    (div_le_iff₀ hd).2 (by linarith)
  unfold step
  linarith

private theorem step_mono {x v w : ℝ} (hx : 0 ≤ x) (hx₂ : x ≤ 2) (k : ℕ)
    (hv : 0 ≤ v) (hvw : v ≤ w) : step x k v ≤ step x k w := by
  have hk : 0 ≤ (k:ℝ) := by positivity
  have hi := inner_le_one hx₂ k hv
  have h : x / (4*(k:ℝ)+3+w) ≤ x / (4*(k:ℝ)+3+v) :=
    div_le_div_of_nonneg_left hx (by linarith) (by linarith)
  unfold step
  exact sub_le_sub_left (div_le_div_of_nonneg_left hx (by linarith) (by linarith)) _

private theorem trunc_pos {x : ℝ} (hx : 0 ≤ x) (hx₂ : x ≤ 2) (n k : ℕ) (hk : 0 < k) :
    0 < Utrunc (n+1) k x := by
  induction n generalizing k with
  | zero =>
    change 0 < step x k (middle x 0)
    have h := step_lower hx₂ k (middle_nonneg hx (le_refl 0))
    have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  | succ n ih =>
    change 0 < step x k (middle x (Utrunc (n+1) (k+1) x))
    have h := step_lower hx₂ k (middle_nonneg hx (ih (k+1) (by omega)).le)
    have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
    linarith

private theorem trunc_decreasing {x : ℝ} (hx : 0 ≤ x) (hx₂ : x ≤ 2) (n k : ℕ) :
    Utrunc (n+2) k x ≤ Utrunc (n+1) k x := by
  induction n generalizing k with
  | zero =>
    change step x k (middle x (Utrunc 1 (k+1) x)) ≤ step x k (middle x 0)
    have hp := trunc_pos hx hx₂ 0 (k+1) (by omega)
    exact step_mono hx hx₂ k (middle_nonneg hx hp.le) (middle_le_zero_arg hx hp.le)
  | succ n ih =>
    change step x k (middle x (Utrunc (n+2) (k+1) x)) ≤
      step x k (middle x (Utrunc (n+1) (k+1) x))
    have hp := trunc_pos hx hx₂ (n+1) (k+1) (by omega)
    exact step_mono hx hx₂ k (middle_nonneg hx hp.le) (middle_mono hx hp (ih (k+1)))

private theorem trunc_bounded {x : ℝ} (hx : 0 ≤ x) (hx₂ : x ≤ 2) (n : ℕ) :
    -1 ≤ Utrunc (n+1) 0 x := by
  have hu : 0 ≤ Utrunc n 1 x := by
    cases n with
    | zero => rfl
    | succ n => exact (trunc_pos hx hx₂ n 1 (by decide)).le
  change -1 ≤ step x 0 (middle x (Utrunc n 1 x))
  simpa using step_lower hx₂ 0 (middle_nonneg hx hu)

theorem result : ¬ (type_of% @OMA.S_oeis_a000111.main) := by
  intro h
  let x := Real.pi / 2
  have hx : 1 < x := by dsimp [x]; linarith [Real.pi_gt_three]
  have hx₂ : x ≤ 2 := by dsimp [x]; linarith [Real.pi_lt_four]
  let f (n : ℕ) := Utrunc (n+1) 0 x
  have hf : Antitone f := antitone_nat_of_succ_le fun n => trunc_decreasing (by linarith) hx₂ n 0
  have hb : ∀ n, -1 ≤ f n := trunc_bounded (by linarith) hx₂
  have hlim : Filter.Tendsto f Filter.atTop (nhds (iInf f)) :=
    tendsto_atTop_ciInf hf ⟨-1, by rintro _ ⟨n, rfl⟩; exact hb n⟩
  have hlim' : Filter.Tendsto (fun n => Utrunc n 0 x) Filter.atTop (nhds (iInf f)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mp hlim
  have hlow : -1 ≤ iInf f := le_ciInf hb
  have he := h x (iInf f) hlim'
  have hcos : Real.cos x = 0 := Real.cos_pi_div_two
  rw [Real.tan_eq_sin_div_cos, hcos, div_zero, div_zero, add_zero] at he
  by_cases hz : iInf f = 0
  · simp [hz] at he
  · field_simp [hz] at he
    linarith

end FractionLimit

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a000111.main) := FractionLimit.result
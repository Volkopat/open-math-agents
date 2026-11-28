import OMAStatements.S_oeis_a153386

namespace OMA.P_oeis_a153386

open OMA.S_oeis_a153386 Filter Topology

/-! ### Fibonacci identities for even indices -/

private lemma fib_add_two (k : ℕ) : Nat.fib (k + 2) = Nat.fib (k + 1) + Nat.fib k := by
  rw [Nat.fib_add_two, add_comm]

private lemma fib_pos_of_pos {k : ℕ} (hk : 0 < k) : (0 : ℝ) < (Nat.fib k : ℝ) := by
  exact_mod_cast Nat.fib_pos.mpr hk

private lemma fib_even_pos (n : ℕ) : (0 : ℝ) < (Nat.fib (2 * (n + 1)) : ℝ) :=
  fib_pos_of_pos (by omega)

private lemma fib_even_step (k : ℕ) :
    (Nat.fib (k + 4) : ℝ) = 3 * (Nat.fib (k + 2) : ℝ) - (Nat.fib k : ℝ) := by
  have h1 : Nat.fib (k + 2) = Nat.fib (k + 1) + Nat.fib k := fib_add_two k
  have h2 : Nat.fib (k + 3) = Nat.fib (k + 2) + Nat.fib (k + 1) := fib_add_two (k + 1)
  have h3 : Nat.fib (k + 4) = Nat.fib (k + 3) + Nat.fib (k + 2) := fib_add_two (k + 2)
  have h1r : (Nat.fib (k + 2) : ℝ) = (Nat.fib (k + 1) : ℝ) + (Nat.fib k : ℝ) := by exact_mod_cast h1
  have h2r : (Nat.fib (k + 3) : ℝ) = (Nat.fib (k + 2) : ℝ) + (Nat.fib (k + 1) : ℝ) := by exact_mod_cast h2
  have h3r : (Nat.fib (k + 4) : ℝ) = (Nat.fib (k + 3) : ℝ) + (Nat.fib (k + 2) : ℝ) := by exact_mod_cast h3
  linarith

/-- Cassini-type identity: `F(2n+3)*F(2n+4) - F(2n+5)*F(2n) = F(2n+2)*F(2n+4) + 3` for `n ≥ 1`.
More generally for all even `m = 2*k`: `F(m+3)*F(m+4) - F(m+5)*F(m) = F(m+2)*F(m+4) + 3`. -/
private lemma fib_cassini_even (k : ℕ) :
    (Nat.fib (2 * k + 3) : ℝ) * (Nat.fib (2 * k + 4) : ℝ) -
      (Nat.fib (2 * k + 5) : ℝ) * (Nat.fib (2 * k) : ℝ) =
    (Nat.fib (2 * k + 2) : ℝ) * (Nat.fib (2 * k + 4) : ℝ) + 3 := by
  induction k with
  | zero =>
    norm_num [Nat.fib]
  | succ k ih =>
    have h2 : (Nat.fib (2 * k + 2) : ℝ) = (Nat.fib (2 * k + 1) : ℝ) + (Nat.fib (2 * k) : ℝ) := by
      exact_mod_cast fib_add_two (2 * k)
    have h3 : (Nat.fib (2 * k + 3) : ℝ) = (Nat.fib (2 * k + 2) : ℝ) + (Nat.fib (2 * k + 1) : ℝ) := by
      exact_mod_cast fib_add_two (2 * k + 1)
    have h4 : (Nat.fib (2 * k + 4) : ℝ) = (Nat.fib (2 * k + 3) : ℝ) + (Nat.fib (2 * k + 2) : ℝ) := by
      exact_mod_cast fib_add_two (2 * k + 2)
    have h5 : (Nat.fib (2 * k + 5) : ℝ) = (Nat.fib (2 * k + 4) : ℝ) + (Nat.fib (2 * k + 3) : ℝ) := by
      exact_mod_cast fib_add_two (2 * k + 3)
    have h6 : (Nat.fib (2 * k + 6) : ℝ) = (Nat.fib (2 * k + 5) : ℝ) + (Nat.fib (2 * k + 4) : ℝ) := by
      exact_mod_cast fib_add_two (2 * k + 4)
    have h7 : (Nat.fib (2 * k + 7) : ℝ) = (Nat.fib (2 * k + 6) : ℝ) + (Nat.fib (2 * k + 5) : ℝ) := by
      exact_mod_cast fib_add_two (2 * k + 5)
    have ha : 2 * (k + 1) + 3 = 2 * k + 5 := by omega
    have hb : 2 * (k + 1) + 4 = 2 * k + 6 := by omega
    have hc : 2 * (k + 1) + 5 = 2 * k + 7 := by omega
    have hd : 2 * (k + 1) = 2 * k + 2 := by omega
    have he : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
    rw [ha, hb, hc, he, hd]
    nlinarith

/-- Telescoping potential `T(n) = F(2n+5)/(F(2n+2)*F(2n+4)) - 9/(4*F(2n+2)*F(2n+4)*F(2n+6))`. -/
private noncomputable def teleTerm (n : ℕ) : ℝ :=
  (Nat.fib (2 * n + 5) : ℝ) / ((Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ)) -
    (9 : ℝ) / (4 * (Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ) * (Nat.fib (2 * n + 6) : ℝ))

private lemma teleTerm_zero : teleTerm 0 = (151 : ℝ) / 96 := by
  unfold teleTerm
  have hf2 : Nat.fib 2 = 1 := rfl
  have hf4 : Nat.fib 4 = 3 := rfl
  have hf5 : Nat.fib 5 = 5 := rfl
  have hf6 : Nat.fib 6 = 8 := rfl
  simp only [Nat.mul_zero, zero_add, hf2, hf4, hf5, hf6]
  norm_num

/-- Exact one-step telescoping identity:
`teleTerm n - teleTerm (n + 1) = 1 / F(2n+2) + 6 / (F(2n+2) * F(2n+6) * F(2n+8))`. -/
private lemma teleTerm_diff (n : ℕ) :
    teleTerm n - teleTerm (n + 1) =
      (1 : ℝ) / (Nat.fib (2 * (n + 1)) : ℝ) +
        6 * ((1 : ℝ) /
          ((Nat.fib (2 * (n + 1)) : ℝ) *
           (Nat.fib (2 * (n + 1) + 4) : ℝ) *
           (Nat.fib (2 * (n + 1) + 6) : ℝ))) := by
  unfold teleTerm
  have h1 : 2 * (n + 1) = 2 * n + 2 := by omega
  have h2 : 2 * (n + 1) + 2 = 2 * n + 4 := by omega
  have h3 : 2 * (n + 1) + 4 = 2 * n + 6 := by omega
  have h4 : 2 * (n + 1) + 5 = 2 * n + 7 := by omega
  have h5 : 2 * (n + 1) + 6 = 2 * n + 8 := by omega
  rw [h2, h3, h4, h5, h1]
  have hp2 : (Nat.fib (2 * n + 2) : ℝ) ≠ 0 := (fib_pos_of_pos (by omega)).ne'
  have hp4 : (Nat.fib (2 * n + 4) : ℝ) ≠ 0 := (fib_pos_of_pos (by omega)).ne'
  have hp6 : (Nat.fib (2 * n + 6) : ℝ) ≠ 0 := (fib_pos_of_pos (by omega)).ne'
  have hp8 : (Nat.fib (2 * n + 8) : ℝ) ≠ 0 := (fib_pos_of_pos (by omega)).ne'
  have hcas := fib_cassini_even (n + 1)
  rw [show 2 * (n + 1) + 3 = 2 * n + 5 by omega,
      show 2 * (n + 1) + 4 = 2 * n + 6 by omega,
      show 2 * (n + 1) + 5 = 2 * n + 7 by omega,
      show 2 * (n + 1) + 2 = 2 * n + 4 by omega,
      show 2 * (n + 1) = 2 * n + 2 by omega] at hcas
  have hstep1 := fib_even_step (2 * n + 2)
  have hstep2 := fib_even_step (2 * n + 4)
  rw [show 2 * n + 2 + 4 = 2 * n + 6 by omega, show 2 * n + 2 + 2 = 2 * n + 4 by omega] at hstep1
  rw [show 2 * n + 4 + 4 = 2 * n + 8 by omega, show 2 * n + 4 + 2 = 2 * n + 6 by omega] at hstep2
  field_simp [hp2, hp4, hp6, hp8]
  nlinarith

/-! ### Growth bound and summability -/

private lemma fib_ge_pow_two (n : ℕ) : (2 : ℝ) ^ n ≤ (Nat.fib (2 * n + 2) : ℝ) := by
  induction n with
  | zero =>
    norm_num [Nat.fib]
  | succ n ih =>
    have hstep : (Nat.fib (2 * (n + 1) + 2) : ℝ) =
        3 * (Nat.fib (2 * n + 2) : ℝ) - (Nat.fib (2 * n) : ℝ) := by
      have h := fib_even_step (2 * n)
      rwa [show 2 * n + 4 = 2 * (n + 1) + 2 by omega] at h
    have hle : (Nat.fib (2 * n) : ℝ) ≤ (Nat.fib (2 * n + 2) : ℝ) := by
      exact_mod_cast Nat.fib_mono (by omega : 2 * n ≤ 2 * n + 2)
    rw [hstep, pow_succ']
    linarith

private lemma fib_even_ge_pow (n : ℕ) : (2 : ℝ) ^ n ≤ (Nat.fib (2 * (n + 1)) : ℝ) := by
  rw [show 2 * (n + 1) = 2 * n + 2 by omega]
  exact fib_ge_pow_two n

private lemma tendsto_teleTerm : Tendsto teleTerm atTop (nhds 0) := by
  have hbound : ∀ n : ℕ, ‖teleTerm n‖ ≤ 10 * ((1 / 2 : ℝ) ^ n) := by
    intro n
    rw [Real.norm_eq_abs]
    have hp2 : (0 : ℝ) < (Nat.fib (2 * n + 2) : ℝ) := fib_pos_of_pos (by omega)
    have hp4 : (0 : ℝ) < (Nat.fib (2 * n + 4) : ℝ) := fib_pos_of_pos (by omega)
    have hp6 : (0 : ℝ) < (Nat.fib (2 * n + 6) : ℝ) := fib_pos_of_pos (by omega)
    have h2ge : (2 : ℝ) ^ n ≤ (Nat.fib (2 * n + 2) : ℝ) := fib_ge_pow_two n
    have h4ge1 : (1 : ℝ) ≤ (Nat.fib (2 * n + 4) : ℝ) := by
      have := fib_ge_pow_two (n + 1)
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
      rw [show 2 * (n + 1) + 2 = 2 * n + 4 by omega] at this
      linarith
    have h6ge1 : (1 : ℝ) ≤ (Nat.fib (2 * n + 6) : ℝ) := by
      have := fib_ge_pow_two (n + 2)
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 2) := one_le_pow₀ (by norm_num)
      rw [show 2 * (n + 2) + 2 = 2 * n + 6 by omega] at this
      linarith
    have h5le : (Nat.fib (2 * n + 5) : ℝ) ≤ 2 * (Nat.fib (2 * n + 4) : ℝ) := by
      have h1 : Nat.fib (2 * n + 5) = Nat.fib (2 * n + 4) + Nat.fib (2 * n + 3) := fib_add_two (2 * n + 3)
      have h2 : Nat.fib (2 * n + 3) ≤ Nat.fib (2 * n + 4) := Nat.fib_mono (by omega)
      have h1r : (Nat.fib (2 * n + 5) : ℝ) = (Nat.fib (2 * n + 4) : ℝ) + (Nat.fib (2 * n + 3) : ℝ) := by
        exact_mod_cast h1
      have h2r : (Nat.fib (2 * n + 3) : ℝ) ≤ (Nat.fib (2 * n + 4) : ℝ) := by exact_mod_cast h2
      linarith
    have ha : (Nat.fib (2 * n + 5) : ℝ) / ((Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ)) ≤
        2 * ((1 / 2 : ℝ) ^ n) := by
      have hinv : (1 : ℝ) / (Nat.fib (2 * n + 2) : ℝ) ≤ (1 / 2 : ℝ) ^ n := by
        rw [one_div_pow]
        exact one_div_le_one_div_of_le (by positivity) h2ge
      have hdiv : (Nat.fib (2 * n + 5) : ℝ) / ((Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ)) ≤
          (2 * (Nat.fib (2 * n + 4) : ℝ)) / ((Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ)) := by
        exact div_le_div_of_nonneg_right h5le (by positivity)
      have hsimp : (2 * (Nat.fib (2 * n + 4) : ℝ)) / ((Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ)) =
          2 * ((1 : ℝ) / (Nat.fib (2 * n + 2) : ℝ)) := by
        field_simp [hp2.ne', hp4.ne']
      linarith
    have hb : (9 : ℝ) / (4 * (Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ) * (Nat.fib (2 * n + 6) : ℝ)) ≤
        8 * ((1 / 2 : ℝ) ^ n) := by
      have hden : (2 : ℝ) ^ n ≤ 4 * (Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ) * (Nat.fib (2 * n + 6) : ℝ) := by
        have hmul1 : (Nat.fib (2 * n + 2) : ℝ) ≤ (Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ) :=
          le_mul_of_one_le_right hp2.le h4ge1
        have hmul2 : (Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ) ≤
            (Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ) * (Nat.fib (2 * n + 6) : ℝ) :=
          le_mul_of_one_le_right (by positivity) h6ge1
        nlinarith
      have h9 : (9 : ℝ) / (4 * (Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ) * (Nat.fib (2 * n + 6) : ℝ)) ≤
          (9 : ℝ) / (4 * (2 : ℝ) ^ n) := by
        have h4den : 4 * (2 : ℝ) ^ n ≤ 4 * (Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ) * (Nat.fib (2 * n + 6) : ℝ) := by
          have hmul1 : (Nat.fib (2 * n + 2) : ℝ) ≤ (Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ) :=
            le_mul_of_one_le_right hp2.le h4ge1
          have hmul2 : (Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ) ≤
              (Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ) * (Nat.fib (2 * n + 6) : ℝ) :=
            le_mul_of_one_le_right (by positivity) h6ge1
          nlinarith
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h4den
      have h4eq : (9 : ℝ) / (4 * (2 : ℝ) ^ n) = (9 / 4 : ℝ) * ((1 / 2 : ℝ) ^ n) := by
        rw [one_div_pow]; ring
      have hpow_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
      linarith
    have ha_nn : (0 : ℝ) ≤ (Nat.fib (2 * n + 5) : ℝ) / ((Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ)) := by
      positivity
    have hb_nn : (0 : ℝ) ≤ (9 : ℝ) / (4 * (Nat.fib (2 * n + 2) : ℝ) * (Nat.fib (2 * n + 4) : ℝ) * (Nat.fib (2 * n + 6) : ℝ)) := by
      positivity
    unfold teleTerm
    rw [abs_le]
    constructor <;> linarith
  have hgeom : Tendsto (fun n : ℕ => (10 : ℝ) * ((1 / 2 : ℝ) ^ n)) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    simpa using h.const_mul (10 : ℝ)
  exact squeeze_zero_norm hbound hgeom

private lemma summable_inv_fib_even :
    Summable (fun n : ℕ => (1 : ℝ) / (Nat.fib (2 * (n + 1)) : ℝ)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) (fib_even_ge_pow n)

private lemma summable_triple :
    Summable (fun n : ℕ =>
      (1 : ℝ) /
        ((Nat.fib (2 * (n + 1)) : ℝ) *
         (Nat.fib (2 * (n + 1) + 4) : ℝ) *
         (Nat.fib (2 * (n + 1) + 6) : ℝ))) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) summable_inv_fib_even
  have hp2 : (0 : ℝ) < (Nat.fib (2 * (n + 1)) : ℝ) := fib_even_pos n
  have h4ge1 : (1 : ℝ) ≤ (Nat.fib (2 * (n + 1) + 4) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < 2 * (n + 1) + 4)
  have h6ge1 : (1 : ℝ) ≤ (Nat.fib (2 * (n + 1) + 6) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < 2 * (n + 1) + 6)
  have hden : (Nat.fib (2 * (n + 1)) : ℝ) ≤
      (Nat.fib (2 * (n + 1)) : ℝ) * (Nat.fib (2 * (n + 1) + 4) : ℝ) * (Nat.fib (2 * (n + 1) + 6) : ℝ) := by
    have h1 : (Nat.fib (2 * (n + 1)) : ℝ) ≤ (Nat.fib (2 * (n + 1)) : ℝ) * (Nat.fib (2 * (n + 1) + 4) : ℝ) :=
      le_mul_of_one_le_right hp2.le h4ge1
    exact le_trans h1 (le_mul_of_one_le_right (by positivity) h6ge1)
  exact one_div_le_one_div_of_le hp2 hden

theorem solution :
    (∑' n : ℕ, (1 : ℝ) / (Nat.fib (2 * (n + 1)) : ℝ)) =
      (151 : ℝ) / 96 -
        6 * ∑' n : ℕ,
          (1 : ℝ) /
            ((Nat.fib (2 * (n + 1)) : ℝ) *
             (Nat.fib (2 * (n + 1) + 4) : ℝ) *
             (Nat.fib (2 * (n + 1) + 6) : ℝ)) := by
  have hsum : HasSum (fun n : ℕ => teleTerm n - teleTerm (n + 1)) (teleTerm 0) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, (teleTerm n - teleTerm (n + 1)) =
          teleTerm 0 - teleTerm N := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          rw [Finset.sum_range_succ, ih]; ring
      simp_rw [hpart]
      simpa using tendsto_const_nhds.sub tendsto_teleTerm
    · intro n
      rw [teleTerm_diff n]
      have h1 : (0 : ℝ) ≤ (1 : ℝ) / (Nat.fib (2 * (n + 1)) : ℝ) := by positivity
      have h2 : (0 : ℝ) ≤ (1 : ℝ) /
          ((Nat.fib (2 * (n + 1)) : ℝ) *
           (Nat.fib (2 * (n + 1) + 4) : ℝ) *
           (Nat.fib (2 * (n + 1) + 6) : ℝ)) := by positivity
      linarith
  have htsum : (∑' n : ℕ, (teleTerm n - teleTerm (n + 1))) = (151 : ℝ) / 96 := by
    rw [hsum.tsum_eq, teleTerm_zero]
  simp_rw [teleTerm_diff] at htsum
  rw [summable_inv_fib_even.tsum_add (summable_triple.mul_left 6), tsum_mul_left] at htsum
  linarith

end OMA.P_oeis_a153386

theorem OMA.solution : type_of% @OMA.S_oeis_a153386.main :=
  OMA.P_oeis_a153386.solution

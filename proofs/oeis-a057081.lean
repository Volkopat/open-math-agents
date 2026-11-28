import OMAStatements.S_oeis_a057081

/-!
Proof of Peter Bala's alternating series identity for OEIS A057081:
Let alpha = (sqrt 11 + sqrt 7) / 2 and beta = (sqrt 11 - sqrt 7) / 2, so alpha * beta = 1
and alpha^2 + beta^2 = 9. Then (alpha - beta) * a n = alpha^(2n+1) - beta^(2n+1), which
yields the recurrence a(n+2) = 9*a(n+1) - a(n), growth a(n) >= 8^n, 7 * s(k) = c(k) - 2
where c(k) = alpha^(2k) + beta^(2k), a(k*j) + a(k*(j+2)) = c(k) * a(k*(j+1)), and
a(k*(j+1))^2 - a(k*j)*a(k*(j+2)) = (c(k) + 2) * s(k). Hence each term decomposes as
(-1)^j * (1 / (a(k*j) + a(k*(j+1))) + 1 / (a(k*(j+1)) + a(k*(j+2)))), telescoping
the N-th partial sum to 1 / (1 + a k) - (-1)^N / (a(k*N) + a(k*(N+1))) -> 1 / (1 + a k).
-/

namespace OMA.P_oeis_a057081

private noncomputable def α : ℝ := (Real.sqrt 11 + Real.sqrt 7) / 2

private noncomputable def β : ℝ := (Real.sqrt 11 - Real.sqrt 7) / 2

private lemma α_mul_β : α * β = 1 := by
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  dsimp [α, β]
  linear_combination (h11 - h7) / 4

private lemma α_add_β : α + β = Real.sqrt 11 := by
  dsimp [α, β]
  ring

private lemma α_sub_β : α - β = Real.sqrt 7 := by
  dsimp [α, β]
  ring

private lemma α_sub_β_ne : α - β ≠ 0 := by
  rw [α_sub_β]
  exact ne_of_gt (Real.sqrt_pos.mpr (by norm_num))

private lemma α_sub_β_sq : (α - β) ^ 2 = 7 := by
  rw [α_sub_β]
  exact Real.sq_sqrt (by norm_num)

private lemma α_sq_add_β_sq : α ^ 2 + β ^ 2 = 9 := by
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h7 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  dsimp [α, β]
  linear_combination (h11 + h7) / 2

private lemma U_binet : ∀ m : ℕ,
    (α - β) * (Polynomial.Chebyshev.U ℝ (m : ℤ)).eval (Real.sqrt 11 / 2) =
      α ^ (m + 1) - β ^ (m + 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 =>
      simp [Polynomial.Chebyshev.U_zero]
    | 1 =>
      rw [Nat.cast_one, Polynomial.Chebyshev.U_one, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), ← α_add_β]
      ring
    | k + 2 =>
      have hk1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; rfl
      have hrec := Polynomial.Chebyshev.U_add_two ℝ (k : ℤ)
      have heval : (Polynomial.Chebyshev.U ℝ ((k + 2 : ℕ) : ℤ)).eval (Real.sqrt 11 / 2) =
          (α + β) * (Polynomial.Chebyshev.U ℝ ((k + 1 : ℕ) : ℤ)).eval (Real.sqrt 11 / 2) -
            (Polynomial.Chebyshev.U ℝ (k : ℤ)).eval (Real.sqrt 11 / 2) := by
        rw [Nat.cast_add, Nat.cast_ofNat, hrec, hk1, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
          mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), α_add_β]
      have ih0 := ih k (by omega)
      have ih1 := ih (k + 1) (by omega)
      have hab := α_mul_β
      rw [heval]
      linear_combination (α + β) * ih1 - ih0 + (α ^ (k + 1) - β ^ (k + 1)) * hab

private lemma a_binet (n : ℕ) :
    (α - β) * OMA.S_oeis_a057081.a n = α ^ (2 * n + 1) - β ^ (2 * n + 1) := by
  have h := U_binet (2 * n)
  simpa [OMA.S_oeis_a057081.a] using h

private lemma a_zero : OMA.S_oeis_a057081.a 0 = 1 := by
  simp [OMA.S_oeis_a057081.a, Polynomial.Chebyshev.U_zero]

private lemma a_one : OMA.S_oeis_a057081.a 1 = 10 := by
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  rw [OMA.S_oeis_a057081.a, show (2 * (1 : ℕ) : ℤ) = 2 by rfl, Polynomial.Chebyshev.U_two]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  linear_combination h11

private lemma a_rec (n : ℕ) :
    OMA.S_oeis_a057081.a (n + 2) = 9 * OMA.S_oeis_a057081.a (n + 1) - OMA.S_oeis_a057081.a n := by
  apply mul_left_cancel₀ α_sub_β_ne
  have h0 := a_binet n
  have h1 := a_binet (n + 1)
  have h2 := a_binet (n + 2)
  have hab := α_mul_β
  have hsq := α_sq_add_β_sq
  rw [mul_sub, mul_left_comm, h0, h1, h2]
  have hp : α ^ (2 * (n + 2) + 1) - β ^ (2 * (n + 2) + 1) =
      (α ^ 2 + β ^ 2) * (α ^ (2 * (n + 1) + 1) - β ^ (2 * (n + 1) + 1)) -
        (α * β) ^ 2 * (α ^ (2 * n + 1) - β ^ (2 * n + 1)) := by
    ring
  rw [hp, hsq, hab]
  ring

private lemma a_growth (n : ℕ) :
    1 ≤ OMA.S_oeis_a057081.a n ∧ 8 * OMA.S_oeis_a057081.a n ≤ OMA.S_oeis_a057081.a (n + 1) := by
  induction n with
  | zero =>
    rw [a_zero, a_one]
    norm_num
  | succ n ih =>
    have hrec := a_rec n
    obtain ⟨h1, h8⟩ := ih
    constructor <;> linarith

private lemma a_ge_one (n : ℕ) : 1 ≤ OMA.S_oeis_a057081.a n := (a_growth n).1

private lemma a_pow_le (n : ℕ) : (8 : ℝ) ^ n ≤ OMA.S_oeis_a057081.a n := by
  induction n with
  | zero =>
    rw [pow_zero, a_zero]
  | succ n ih =>
    have h8 := (a_growth n).2
    rw [pow_succ']
    linarith

private lemma a_mono {m n : ℕ} (h : m ≤ n) :
    OMA.S_oeis_a057081.a m ≤ OMA.S_oeis_a057081.a n := by
  refine monotone_nat_of_le_succ (fun k => ?_) h
  have ⟨h1, h8⟩ := a_growth k
  linarith

private lemma seven_s_lt (k : ℕ) : 7 * OMA.S_oeis_a057081.s k < OMA.S_oeis_a057081.a k := by
  induction k with
  | zero =>
    simp [OMA.S_oeis_a057081.s, a_zero]
  | succ k ih =>
    simp only [OMA.S_oeis_a057081.s, Finset.sum_range_succ] at ih ⊢
    have h8 := (a_growth k).2
    linarith

private noncomputable def c (k : ℕ) : ℝ := α ^ (2 * k) + β ^ (2 * k)

private lemma s_formula (k : ℕ) : 7 * OMA.S_oeis_a057081.s k = c k - 2 := by
  induction k with
  | zero =>
    simp [OMA.S_oeis_a057081.s, c]
    norm_num
  | succ k ih =>
    have hs_succ : OMA.S_oeis_a057081.s (k + 1) =
        OMA.S_oeis_a057081.s k + OMA.S_oeis_a057081.a k := by
      simp [OMA.S_oeis_a057081.s, Finset.sum_range_succ]
    rw [hs_succ, mul_add, ih, ← α_sub_β_sq]
    have hb := a_binet k
    have hab := α_mul_β
    have hc0 : c k = α ^ (2 * k) + β ^ (2 * k) := rfl
    have hc1 : c (k + 1) = α ^ (2 * (k + 1)) + β ^ (2 * (k + 1)) := rfl
    rw [hc0, hc1]
    have hmul : (α - β) ^ 2 * OMA.S_oeis_a057081.a k =
        (α - β) * (α ^ (2 * k + 1) - β ^ (2 * k + 1)) := by
      rw [sq, mul_assoc, hb]
    have ha_step : α ^ (2 * (k + 1)) = α ^ (2 * k) * α ^ 2 := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    have hb_step : β ^ (2 * (k + 1)) = β ^ (2 * k) * β ^ 2 := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    rw [hmul, ha_step, hb_step]
    linear_combination -α ^ (2 * k) * hab - β ^ (2 * k) * hab

private lemma a_step_sum (k j : ℕ) :
    OMA.S_oeis_a057081.a (k * j) + OMA.S_oeis_a057081.a (k * (j + 2)) =
      c k * OMA.S_oeis_a057081.a (k * (j + 1)) := by
  apply mul_left_cancel₀ α_sub_β_ne
  rw [mul_add, mul_left_comm, a_binet, a_binet, a_binet]
  have habk : α ^ (2 * k) * β ^ (2 * k) = 1 := by rw [← mul_pow, α_mul_β, one_pow]
  have hc : c k = α ^ (2 * k) + β ^ (2 * k) := rfl
  rw [hc]
  have ha1 : α ^ (2 * (k * (j + 1)) + 1) = α ^ (2 * k) * α ^ (2 * (k * j) + 1) := by
    rw [show 2 * (k * (j + 1)) + 1 = 2 * k + (2 * (k * j) + 1) by ring, pow_add]
  have hb1 : β ^ (2 * (k * (j + 1)) + 1) = β ^ (2 * k) * β ^ (2 * (k * j) + 1) := by
    rw [show 2 * (k * (j + 1)) + 1 = 2 * k + (2 * (k * j) + 1) by ring, pow_add]
  have ha2 : α ^ (2 * (k * (j + 2)) + 1) = α ^ (2 * k) * α ^ (2 * (k * (j + 1)) + 1) := by
    rw [show 2 * (k * (j + 2)) + 1 = 2 * k + (2 * (k * (j + 1)) + 1) by ring, pow_add]
  have hb2 : β ^ (2 * (k * (j + 2)) + 1) = β ^ (2 * k) * β ^ (2 * (k * (j + 1)) + 1) := by
    rw [show 2 * (k * (j + 2)) + 1 = 2 * k + (2 * (k * (j + 1)) + 1) by ring, pow_add]
  rw [ha2, hb2, ha1, hb1]
  linear_combination -(α ^ (2 * (k * j) + 1) - β ^ (2 * (k * j) + 1)) * habk

private lemma a_casorati (k j : ℕ) :
    OMA.S_oeis_a057081.a (k * (j + 1)) ^ 2 -
        OMA.S_oeis_a057081.a (k * j) * OMA.S_oeis_a057081.a (k * (j + 2)) =
      (c k + 2) * OMA.S_oeis_a057081.s k := by
  apply mul_left_cancel₀ (by norm_num : (7 : ℝ) ≠ 0)
  have h7s := s_formula k
  rw [show (7 : ℝ) * ((c k + 2) * OMA.S_oeis_a057081.s k) = (c k + 2) * (7 * OMA.S_oeis_a057081.s k)
    by ring, h7s]
  rw [show (7 : ℝ) = (α - β) ^ 2 from α_sub_β_sq.symm]
  have h0 := a_binet (k * j)
  have h1 := a_binet (k * (j + 1))
  have h2 := a_binet (k * (j + 2))
  have hsq : ((α - β) ^ 2) * (OMA.S_oeis_a057081.a (k * (j + 1)) ^ 2 -
      OMA.S_oeis_a057081.a (k * j) * OMA.S_oeis_a057081.a (k * (j + 2))) =
      ((α - β) * OMA.S_oeis_a057081.a (k * (j + 1))) ^ 2 -
        ((α - β) * OMA.S_oeis_a057081.a (k * j)) *
          ((α - β) * OMA.S_oeis_a057081.a (k * (j + 2))) := by
    ring
  rw [hsq, h0, h1, h2]
  have habk : α ^ (2 * k) * β ^ (2 * k) = 1 := by rw [← mul_pow, α_mul_β, one_pow]
  have habm : α ^ (2 * (k * j) + 1) * β ^ (2 * (k * j) + 1) = 1 := by
    rw [← mul_pow, α_mul_β, one_pow]
  have ha1 : α ^ (2 * (k * (j + 1)) + 1) = α ^ (2 * k) * α ^ (2 * (k * j) + 1) := by
    rw [show 2 * (k * (j + 1)) + 1 = 2 * k + (2 * (k * j) + 1) by ring, pow_add]
  have hb1 : β ^ (2 * (k * (j + 1)) + 1) = β ^ (2 * k) * β ^ (2 * (k * j) + 1) := by
    rw [show 2 * (k * (j + 1)) + 1 = 2 * k + (2 * (k * j) + 1) by ring, pow_add]
  have ha2 : α ^ (2 * (k * (j + 2)) + 1) = α ^ (2 * k) * (α ^ (2 * k) * α ^ (2 * (k * j) + 1)) := by
    rw [show 2 * (k * (j + 2)) + 1 = 2 * k + (2 * k + (2 * (k * j) + 1)) by ring, pow_add, pow_add]
  have hb2 : β ^ (2 * (k * (j + 2)) + 1) = β ^ (2 * k) * (β ^ (2 * k) * β ^ (2 * (k * j) + 1)) := by
    rw [show 2 * (k * (j + 2)) + 1 = 2 * k + (2 * k + (2 * (k * j) + 1)) by ring, pow_add, pow_add]
  have hc : c k = α ^ (2 * k) + β ^ (2 * k) := rfl
  rw [ha1, hb1, ha2, hb2, hc]
  set U := α ^ (2 * k)
  set V := β ^ (2 * k)
  set X := α ^ (2 * (k * j) + 1)
  set Y := β ^ (2 * (k * j) + 1)
  have hid : (U * X - V * Y) ^ 2 - (X - Y) * (U * (U * X) - V * (V * Y)) =
      (U ^ 2 + V ^ 2 - 2 * (U * V)) * (X * Y) := by
    ring
  rw [hid, habm]
  calc (U ^ 2 + V ^ 2 - 2 * (U * V)) * 1
      = U ^ 2 + V ^ 2 - 2 * 1 := by rw [habk, mul_one]
    _ = U ^ 2 + 2 * 1 + V ^ 2 - 4 := by ring
    _ = U ^ 2 + 2 * (U * V) + V ^ 2 - 4 := by rw [habk]
    _ = (U + V + 2) * (U + V - 2) := by ring

private lemma term_eq (k j : ℕ) :
    OMA.S_oeis_a057081.term k (j + 1) =
      (-1 : ℝ) ^ j *
        (1 / (OMA.S_oeis_a057081.a (k * j) + OMA.S_oeis_a057081.a (k * (j + 1))) +
         1 / (OMA.S_oeis_a057081.a (k * (j + 1)) + OMA.S_oeis_a057081.a (k * (j + 2)))) := by
  have ha0 : 1 ≤ OMA.S_oeis_a057081.a (k * j) := a_ge_one _
  have ha1 : 1 ≤ OMA.S_oeis_a057081.a (k * (j + 1)) := a_ge_one _
  have ha2 : 1 ≤ OMA.S_oeis_a057081.a (k * (j + 2)) := a_ge_one _
  have hsk : 7 * OMA.S_oeis_a057081.s k < OMA.S_oeis_a057081.a k := seven_s_lt k
  have hle : k ≤ k * (j + 1) := Nat.le_mul_of_pos_right k (Nat.succ_pos j)
  have hmono : OMA.S_oeis_a057081.a k ≤ OMA.S_oeis_a057081.a (k * (j + 1)) := a_mono hle
  have hs_nonneg : 0 ≤ OMA.S_oeis_a057081.s k :=
    Finset.sum_nonneg (fun i _ => by linarith [a_ge_one i])
  have hnum_pos : 0 < OMA.S_oeis_a057081.a (k * (j + 1)) ^ 2 - OMA.S_oeis_a057081.s k := by
    nlinarith
  have h1_pos : 0 < OMA.S_oeis_a057081.a (k * j) + OMA.S_oeis_a057081.a (k * (j + 1)) := by
    linarith
  have h2_pos : 0 < OMA.S_oeis_a057081.a (k * (j + 1)) + OMA.S_oeis_a057081.a (k * (j + 2)) := by
    linarith
  have hpow : (-1 : ℝ) ^ (j + 1 + 1) = (-1 : ℝ) ^ j := by
    rw [pow_succ, pow_succ]
    ring
  have ha1_ne : OMA.S_oeis_a057081.a (k * (j + 1)) ≠ 0 := by linarith
  have hnum_ne : OMA.S_oeis_a057081.a (k * (j + 1)) ^ 2 - OMA.S_oeis_a057081.s k ≠ 0 :=
    ne_of_gt hnum_pos
  have h1_ne : OMA.S_oeis_a057081.a (k * j) + OMA.S_oeis_a057081.a (k * (j + 1)) ≠ 0 :=
    ne_of_gt h1_pos
  have h2_ne : OMA.S_oeis_a057081.a (k * (j + 1)) + OMA.S_oeis_a057081.a (k * (j + 2)) ≠ 0 :=
    ne_of_gt h2_pos
  have hsub :
      OMA.S_oeis_a057081.a (k * (j + 1)) -
          OMA.S_oeis_a057081.s k / OMA.S_oeis_a057081.a (k * (j + 1)) =
        (OMA.S_oeis_a057081.a (k * (j + 1)) ^ 2 - OMA.S_oeis_a057081.s k) /
          OMA.S_oeis_a057081.a (k * (j + 1)) := by
    field_simp [ha1_ne]
  have hsum := a_step_sum k j
  have hcas := a_casorati k j
  have hfrac :
      1 / ((OMA.S_oeis_a057081.a (k * (j + 1)) ^ 2 - OMA.S_oeis_a057081.s k) /
            OMA.S_oeis_a057081.a (k * (j + 1))) =
        1 / (OMA.S_oeis_a057081.a (k * j) + OMA.S_oeis_a057081.a (k * (j + 1))) +
        1 / (OMA.S_oeis_a057081.a (k * (j + 1)) + OMA.S_oeis_a057081.a (k * (j + 2))) := by
    field_simp [ha1_ne, hnum_ne, h1_ne, h2_ne]
    linear_combination OMA.S_oeis_a057081.s k * hsum - OMA.S_oeis_a057081.a (k * (j + 1)) * hcas
  dsimp [OMA.S_oeis_a057081.term]
  rw [hpow, hsub, div_eq_mul_one_div, hfrac]

private lemma partial_sum_eq (k N : ℕ) :
    (∑ j ∈ Finset.range N, OMA.S_oeis_a057081.term k (j + 1)) =
      1 / (1 + OMA.S_oeis_a057081.a k) -
        (-1 : ℝ) ^ N /
          (OMA.S_oeis_a057081.a (k * N) + OMA.S_oeis_a057081.a (k * (N + 1))) := by
  induction N with
  | zero =>
    simp [a_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, term_eq k N]
    rw [show (-1 : ℝ) ^ (N + 1) = -(-1 : ℝ) ^ N by rw [pow_succ]; ring]
    ring

end OMA.P_oeis_a057081

theorem OMA.solution : type_of% @OMA.S_oeis_a057081.main := by
  intro k hk
  have hps : (fun N => ∑ j ∈ Finset.range N, OMA.S_oeis_a057081.term k (j + 1)) =
      fun N => 1 / (1 + OMA.S_oeis_a057081.a k) -
        (-1 : ℝ) ^ N /
          (OMA.S_oeis_a057081.a (k * N) + OMA.S_oeis_a057081.a (k * (N + 1))) := by
    ext N
    exact OMA.P_oeis_a057081.partial_sum_eq k N
  rw [hps]
  have hrem : Filter.Tendsto
      (fun N => (-1 : ℝ) ^ N /
        (OMA.S_oeis_a057081.a (k * N) + OMA.S_oeis_a057081.a (k * (N + 1))))
      Filter.atTop (nhds 0) := by
    have hpow : Filter.Tendsto (fun N : ℕ => ((1 : ℝ) / 8) ^ N) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hbound : ∀ N : ℕ,
        -((1 : ℝ) / 8) ^ N ≤
          (-1 : ℝ) ^ N /
            (OMA.S_oeis_a057081.a (k * N) + OMA.S_oeis_a057081.a (k * (N + 1))) ∧
        (-1 : ℝ) ^ N /
            (OMA.S_oeis_a057081.a (k * N) + OMA.S_oeis_a057081.a (k * (N + 1))) ≤
          ((1 : ℝ) / 8) ^ N := by
      intro N
      have h1 : (8 : ℝ) ^ N ≤ (8 : ℝ) ^ (k * N) :=
        pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_left N hk)
      have h2 := OMA.P_oeis_a057081.a_pow_le (k * N)
      have h3 := OMA.P_oeis_a057081.a_ge_one (k * (N + 1))
      have hden_pos : (8 : ℝ) ^ N ≤
          OMA.S_oeis_a057081.a (k * N) + OMA.S_oeis_a057081.a (k * (N + 1)) := by linarith
      have h8_pos : (0 : ℝ) < (8 : ℝ) ^ N := by positivity
      have hinv : 1 / (OMA.S_oeis_a057081.a (k * N) + OMA.S_oeis_a057081.a (k * (N + 1))) ≤
          ((1 : ℝ) / 8) ^ N := by
        rw [one_div, one_div, inv_pow]
        exact inv_anti₀ h8_pos hden_pos
      have hnonneg :
          0 ≤ 1 / (OMA.S_oeis_a057081.a (k * N) + OMA.S_oeis_a057081.a (k * (N + 1))) :=
        div_nonneg zero_le_one (by linarith)
      rcases neg_one_pow_eq_or ℝ N with h | h <;> rw [h]
      · constructor <;> linarith
      · have hneg :
            -1 / (OMA.S_oeis_a057081.a (k * N) + OMA.S_oeis_a057081.a (k * (N + 1))) =
              -(1 / (OMA.S_oeis_a057081.a (k * N) + OMA.S_oeis_a057081.a (k * (N + 1)))) := by
          ring
        rw [hneg]
        constructor <;> linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa only [neg_zero] using hpow.neg) hpow
      (fun N => (hbound N).1) (fun N => (hbound N).2)
  simpa using tendsto_const_nhds.sub hrem

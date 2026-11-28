import OMAStatements.S_oeis_a275151

namespace OMA.S_oeis_a275151

open PowerSeries


/-- The integer sequence that a follows: b(0) = 9, b(1) = 8, b(n+2) = 6 b(n+1) - b(n) - 14. -/
def b : ℕ → ℤ
  | 0 => 9
  | 1 => 8
  | n + 2 => 6 * b (n + 1) - b n - 14

lemma b_succ_succ (n : ℕ) : b (n + 2) = 6 * b (n + 1) - b n - 14 := rfl

lemma b_Q (n : ℕ) : b n ^ 2 + b (n + 1) ^ 2 - 6 * b n * b (n + 1) + 14 * b n + 14 * b (n + 1) +
    49 = 0 := by
  induction n with
  | zero => norm_num [b]
  | succ n ih =>
    rw [b_succ_succ]
    linear_combination ih

lemma b_mono (n : ℕ) : 8 ≤ b (n + 1) ∧ b (n + 1) ≤ b (n + 2) := by
  induction n with
  | zero => norm_num [b]
  | succ n ih =>
    have h : b (n + 3) = 6 * b (n + 2) - b (n + 1) - 14 := b_succ_succ (n + 1)
    show 8 ≤ b (n + 2) ∧ b (n + 2) ≤ b (n + 3)
    constructor <;> omega

lemma b_root (n : ℕ) : 0 ≤ b (n + 2) - 3 * b (n + 1) + 7 := by
  rcases n with _ | n
  · norm_num [b]
  · have h : b (n + 3) = 6 * b (n + 2) - b (n + 1) - 14 := b_succ_succ (n + 1)
    have hm := b_mono n
    show 0 ≤ b (n + 3) - 3 * b (n + 2) + 7
    omega

lemma b_sq (n : ℕ) : (b (n + 1) - 3 * b n + 7) ^ 2 = 8 * b n * (b n - 7) := by
  linear_combination b_Q n

lemma a_eq_b (n : ℕ) : a (n + 1) = b (n + 1) := by
  induction n with
  | zero => norm_num [a, b]
  | succ n ih =>
    have hs : Real.sqrt (2 * a (n + 1) * (a (n + 1) - 7)) =
        ((b (n + 2) - 3 * b (n + 1) + 7 : ℤ) : ℝ) / 2 := by
      rw [ih]
      have h0 : (0 : ℝ) ≤ ((b (n + 2) - 3 * b (n + 1) + 7 : ℤ) : ℝ) / 2 := by
        have := b_root n
        have : (0 : ℝ) ≤ ((b (n + 2) - 3 * b (n + 1) + 7 : ℤ) : ℝ) := by exact_mod_cast this
        linarith
      have hsq : (2 * (b (n + 1) : ℝ) * ((b (n + 1) : ℝ) - 7)) =
          (((b (n + 2) - 3 * b (n + 1) + 7 : ℤ) : ℝ) / 2) ^ 2 := by
        have h := b_sq (n + 1)
        have h' : (((b (n + 2) - 3 * b (n + 1) + 7) ^ 2 : ℤ) : ℝ) =
            ((8 * b (n + 1) * (b (n + 1) - 7) : ℤ) : ℝ) := by rw [h]
        push_cast at h' ⊢
        linarith
      rw [hsq, Real.sqrt_sq h0]
    show 3 * a (n + 1) + 2 * Real.sqrt (2 * a (n + 1) * (a (n + 1) - 7)) - 7 = b (n + 2)
    rw [hs, ih]
    push_cast
    ring

/-- The third-order recurrence for b, from n >= 1. -/
lemma b_rec3 (n : ℕ) : b (n + 4) = 7 * b (n + 3) - 7 * b (n + 2) + b (n + 1) := by
  have h1 := b_succ_succ (n + 2)
  have h2 := b_succ_succ (n + 1)
  linear_combination h1 - h2

lemma a_rec3 (n : ℕ) : a (n + 4) = 7 * a (n + 3) - 7 * a (n + 2) + a (n + 1) := by
  rw [a_eq_b (n + 3), a_eq_b (n + 2), a_eq_b (n + 1), a_eq_b n, b_rec3]
  push_cast
  ring

lemma a_one : a 1 = 8 := by norm_num [a]

lemma a_two : a 2 = 25 := by
  rw [a_eq_b 1]; norm_num [b]

lemma a_three : a 3 = 128 := by
  rw [a_eq_b 2]; norm_num [b]

/-- Controls: the entry's data a(1..16). -/
theorem controls : (List.range 16).map (fun i => b (i + 1)) = [8, 25, 128, 729, 4232, 24649,
    143648, 837225, 4879688, 28440889, 165765632, 966152889, 5631151688, 32820757225,
    191293391648, 1114939592649] ∧ ∀ n, a (n + 1) = b (n + 1) :=
  ⟨by decide, a_eq_b⟩

/-- Barker's recurrence, for n > 3. -/
theorem recurrence : ∀ n : ℕ, 3 < n → a n = 7 * a (n - 1) - 7 * a (n - 2) + a (n - 3) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega]
  exact a_rec3 m

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x(8 - 31x + 9x^2)/((1 - x)(1 - 6x + x^2)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℝ) else a n) *
    ((1 - X) * (1 - 6 * X + X ^ 2)) = X * (8 - 31 * X + 9 * X ^ 2) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℝ) else a n) with hA
  have e1 : A * ((1 - X) * (1 - 6 * X + X ^ 2)) =
      A - C (7 : ℝ) * (A * X ^ 1) + C (7 : ℝ) * (A * X ^ 2) - A * X ^ 3 := by
    rw [show (C (7 : ℝ) : ℝ⟦X⟧) = 7 from map_ofNat C 7]
    ring
  have e2 : (X : ℝ⟦X⟧) * (8 - 31 * X + 9 * X ^ 2) =
      C (8 : ℝ) * X ^ 1 - C (31 : ℝ) * X ^ 2 + C (9 : ℝ) * X ^ 3 := by
    rw [show (C (8 : ℝ) : ℝ⟦X⟧) = 8 from map_ofNat C 8,
      show (C (31 : ℝ) : ℝ⟦X⟧) = 31 from map_ofNat C 31,
      show (C (9 : ℝ) : ℝ⟦X⟧) = 9 from map_ofNat C 9]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> simp [a_one, a_two, a_three] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h' := a_rec3 m
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega, show ¬ m + 4 = 0 by omega, show ¬ m + 3 = 0 by omega,
      show ¬ m + 2 = 0 by omega, show ¬ m + 1 = 0 by omega, show 1 ≤ m + 4 by omega,
      show 2 ≤ m + 4 by omega, show 3 ≤ m + 4 by omega, if_true, if_false]
    linear_combination h'

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → a n = (14 + (11 - 6 * Real.sqrt 2) * (3 + 2 * Real.sqrt 2) ^ n +
    (3 - 2 * Real.sqrt 2) ^ n * (11 + 6 * Real.sqrt 2)) / 4 := by
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 2 with hs
  set F : ℕ → ℝ := fun n => (14 + (11 - 6 * s) * (3 + 2 * s) ^ n + (3 - 2 * s) ^ n * (11 + 6 * s)) / 4
    with hF
  have F1 : F 1 = 8 := by
    simp only [hF]
    linear_combination (-6) * s2
  have F2 : F 2 = 25 := by
    simp only [hF]
    linear_combination (-14) * s2
  have F3 : F 3 = 128 := by
    simp only [hF]
    linear_combination (-12 - 24 * s ^ 2) * s2
  have r1 : ∀ m : ℕ, (3 + 2 * s) ^ (m + 4) =
      7 * (3 + 2 * s) ^ (m + 3) - 7 * (3 + 2 * s) ^ (m + 2) + (3 + 2 * s) ^ (m + 1) := by
    intro m
    have : (3 + 2 * s) ^ 3 = 7 * (3 + 2 * s) ^ 2 - 7 * (3 + 2 * s) + 1 := by
      linear_combination (8 + 8 * s) * s2
    calc (3 + 2 * s) ^ (m + 4) = (3 + 2 * s) ^ (m + 1) * (3 + 2 * s) ^ 3 := by ring
      _ = _ := by rw [this]; ring
  have r2 : ∀ m : ℕ, (3 - 2 * s) ^ (m + 4) =
      7 * (3 - 2 * s) ^ (m + 3) - 7 * (3 - 2 * s) ^ (m + 2) + (3 - 2 * s) ^ (m + 1) := by
    intro m
    have : (3 - 2 * s) ^ 3 = 7 * (3 - 2 * s) ^ 2 - 7 * (3 - 2 * s) + 1 := by
      linear_combination (8 - 8 * s) * s2
    calc (3 - 2 * s) ^ (m + 4) = (3 - 2 * s) ^ (m + 1) * (3 - 2 * s) ^ 3 := by ring
      _ = _ := by rw [this]; ring
  have Frec : ∀ m, F (m + 4) = 7 * F (m + 3) - 7 * F (m + 2) + F (m + 1) := by
    intro m
    simp only [hF]
    rw [r1, r2]
    ring
  have key : ∀ m, a (m + 1) = F (m + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases m with _ | _ | _ | m
      · rw [a_one, F1]
      · rw [a_two, F2]
      · rw [a_three, F3]
      · have e1 : a (m + 1) = F (m + 1) := ih m (by omega)
        have e2 : a (m + 2) = F (m + 2) := ih (m + 1) (by omega)
        have e3 : a (m + 3) = F (m + 3) := ih (m + 2) (by omega)
        show a (m + 4) = F (m + 4)
        rw [a_rec3, Frec m, e1, e2, e3]
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact key k

/-- All three of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 1 ≤ n → a n = (14 + (11 - 6 * Real.sqrt 2) * (3 + 2 * Real.sqrt 2) ^ n +
      (3 - 2 * Real.sqrt 2) ^ n * (11 + 6 * Real.sqrt 2)) / 4) ∧
    (∀ n : ℕ, 3 < n → a n = 7 * a (n - 1) - 7 * a (n - 2) + a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℝ) else a n) * ((1 - X) * (1 - 6 * X + X ^ 2)) =
      X * (8 - 31 * X + 9 * X ^ 2) :=
  ⟨closed_form, recurrence, gf⟩

end OMA.S_oeis_a275151

theorem OMA.solution : type_of% @OMA.S_oeis_a275151.main :=
  OMA.S_oeis_a275151.conjecture

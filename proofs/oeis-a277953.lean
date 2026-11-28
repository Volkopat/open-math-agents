import OMAStatements.S_oeis_a277953

-- Credit: @RiverMint78

namespace OMA.Rule14

open S_oeis_a277953

private def update (c r l u d : Bool) : Bool :=
  (14 : ℕ).testBit (c.toNat + 2 * (r.toNat + l.toNat + u.toNat + d.toNat))

private theorem step (t : ℕ) (i j : ℤ) :
    cell 14 (t + 1) i j = update (cell 14 t i j) (cell 14 t (i+1) j)
      (cell 14 t (i-1) j) (cell 14 t i (j+1)) (cell 14 t i (j-1)) := rfl

private theorem parent :
    ∀ c r l u d : Bool, update c r l u d = true →
      c = true ∨ r = true ∨ l = true ∨ u = true ∨ d = true := by decide

/-- Two sides of the light cone suffice for cells above the horizontal axis. -/
private theorem front (t : ℕ) (i j : ℤ) :
    cell 14 t i j = true → i + j ≤ (t : ℤ) ∧ j - i ≤ (t : ℤ) := by
  induction t generalizing i j with
  | zero =>
    simp only [cell, decide_eq_true_eq, Nat.cast_zero]
    rintro ⟨rfl, rfl⟩
    omega
  | succ t ih =>
    rw [step]
    intro h
    rcases parent _ _ _ _ _ h with h | h | h | h | h <;>
      obtain ⟨_, _⟩ := ih _ _ h <;> omega

private theorem reflectY (t : ℕ) (i j : ℤ) : cell 14 t i (-j) = cell 14 t i j := by
  induction t generalizing i j with
  | zero => simp [cell]
  | succ t ih =>
    rw [step, step, show -j + 1 = -(j-1) by omega, show -j - 1 = -(j+1) by omega]
    simp only [ih, update]
    rw [add_right_comm _ (cell 14 t i (j-1)).toNat (cell 14 t i (j+1)).toNat]

/-- Odd sites stay on behind the wave. Even sites on the axis are on for two steps. -/
private def axis (t i : ℤ) : Prop :=
  -t ≤ i ∧ i ≤ t ∧ (i % 2 = 1 ∨ t ≤ i+1 ∨ t ≤ 1-i)

private def adjacent (t i : ℤ) : Prop := -t < i ∧ i < t ∧ i % 2 = 0

private theorem axisStep (t i : ℤ) (ht : 0 ≤ t) (c r l s : Bool)
    (hc : c = true ↔ axis t i) (hr : r = true ↔ axis t (i+1))
    (hl : l = true ↔ axis t (i-1)) (hs : s = true ↔ adjacent t i) :
    update c r l s s = true ↔ axis (t+1) i := by
  cases c <;> cases r <;> cases l <;> cases s <;>
    simp_all [update, axis, adjacent, Nat.testBit] <;> omega

set_option maxHeartbeats 800000 in
private theorem adjacentStep (t i : ℤ) (ht : 0 ≤ t) (c r l u d : Bool)
    (hc : c = true ↔ adjacent t i) (hr : r = true ↔ adjacent t (i+1))
    (hl : l = true ↔ adjacent t (i-1)) (hd : d = true ↔ axis t i)
    (hu : u = true → i+2 ≤ t ∧ 2-i ≤ t) :
    update c r l u d = true ↔ adjacent (t+1) i := by
  cases c <;> cases r <;> cases l <;> cases u <;> cases d <;>
    simp_all [update, axis, adjacent, Nat.testBit] <;> omega

private theorem strip (t : ℕ) :
    (∀ i : ℤ, cell 14 t i 0 = true ↔ axis t i) ∧
    (∀ i : ℤ, cell 14 t i 1 = true ↔ adjacent t i) := by
  induction t with
  | zero =>
    constructor <;> intro i <;> simp [cell, axis, adjacent] <;> omega
  | succ t ih =>
    obtain ⟨haxis, hside⟩ := ih
    constructor <;> intro i <;> rw [step] <;> push_cast
    · simp only [reflectY]
      exact axisStep t i (by positivity) _ _ _ _ (haxis _) (haxis _) (haxis _) (hside _)
    · exact adjacentStep t i (by positivity) _ _ _ _ _ (hside _) (hside _) (hside _)
        (haxis _) (front t i 2)

private theorem digit (t k : ℕ) :
    cell 14 t (k : ℤ) 0 = true ↔ k ≤ t ∧ (k % 2 = 1 ∨ t ≤ k+1) := by
  rw [(strip t).1, axis]
  omega

/-- On advancing the front, append a 1. One former front digit can turn off. -/
private theorem appendStep (n : ℕ) :
    a (n+2) = 10 * a (n+1) + (if n % 2 = 0 then -99 else 1) := by
  let part (t k : ℕ) : ℤ := if cell 14 t k 0 then 10 ^ (t-k) else 0
  have hs : (∑ k ∈ Finset.range n, part (n+2) k) =
      10 * ∑ k ∈ Finset.range n, part (n+1) k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have h : cell 14 (n+2) k 0 = true ↔ cell 14 (n+1) k 0 = true := by
      rw [digit, digit]
      omega
    by_cases hon : cell 14 (n+1) k 0 = true
    · simp only [part, if_pos (h.mpr hon), if_pos hon, show n+2-k = n+1-k+1 by omega,
        pow_succ, mul_comm]
    · simp only [part, if_neg (fun e => hon (h.mp e)), if_neg hon, mul_zero]
  have onFront (t k : ℕ) (hk : k ≤ t) (ht : t ≤ k+1) :
      cell 14 t k 0 = true := (digit t k).2 ⟨hk, Or.inr ht⟩
  have h₁ := onFront (n+1) n (by omega) (by omega)
  have h₂ := onFront (n+1) (n+1) (by omega) (by omega)
  have h₃ := onFront (n+2) (n+1) (by omega) (by omega)
  have h₄ := onFront (n+2) (n+2) (by omega) (by omega)
  change (∑ k ∈ Finset.range (n+3), part (n+2) k) =
    10 * (∑ k ∈ Finset.range (n+2), part (n+1) k) + _
  simp only [Finset.sum_range_succ, hs]
  simp only [part, if_pos h₁, if_pos h₂, if_pos h₃, if_pos h₄]
  by_cases he : n % 2 = 0
  · have hoff : ¬ cell 14 (n+2) n 0 = true := by rw [digit]; omega
    simp [he, hoff]
    ring
  · have hon : cell 14 (n+2) n 0 = true := by rw [digit]; omega
    simp [he, hon]
    ring

private theorem appendDigit (n : ℕ) :
    a (n+1) = 10 * a n + (if n % 2 = 0 then 1 else -99) := by
  cases n with
  | zero => decide
  | succ n =>
    rw [appendStep]
    split_ifs <;> omega

private theorem recurrence (n : ℕ) : a (n+3) = 10 * a (n+2) + a (n+1) - 10 * a n := by
  have h := appendDigit (n+2)
  rw [show (n+2)%2 = n%2 by omega] at h
  linarith [appendDigit n]

private theorem closedForm (n : ℕ) :
    99 * (a n : ℚ) = 539 - 450 * (-1 : ℚ)^n + 10^(1+n) := by
  induction n with
  | zero => norm_num [a, cell]
  | succ n ih =>
    have correction : ((if n % 2 = 0 then 1 else -99 : ℤ) : ℚ) =
        -49 + 50 * (-1 : ℚ)^n := by
      rcases Nat.even_or_odd n with h | h
      · rw [if_pos (Nat.even_iff.mp h), h.neg_one_pow]
        norm_num
      · rw [if_neg (by have := Nat.odd_iff.mp h; omega), h.neg_one_pow]
        norm_num
    rw [appendDigit, Int.cast_add, Int.cast_mul, correction, Int.cast_ofNat]
    rw [pow_succ (-1 : ℚ), show 1+(n+1) = (1+n)+1 by omega, pow_succ (10 : ℚ)]
    linarith

open PowerSeries in
private theorem generatingFunction :
    mk (fun n => (a n : ℚ)) * ((1-X)*(1+X)*(1-10*X) : ℚ⟦X⟧) =
      1 + X - 100 * X^2 := by
  let F : ℚ⟦X⟧ := mk (fun n => (a n : ℚ))
  change F * _ = _
  have denominator : F * ((1-X)*(1+X)*(1-10*X)) =
      F - (10 : ℕ) • (F*X^1) - F*X^2 + (10 : ℕ) • (F*X^3) := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have numerator : (1 + X - 100 * X^2 : ℚ⟦X⟧) =
      X^0 + X^1 - (100 : ℕ) • X^2 := by simp [nsmul_eq_mul]
  rw [denominator, numerator]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow, F, coeff_mk]
  have a₀ : a 0 = 1 := by decide
  have a₁ : a 1 = 11 := by decide
  have a₂ : a 2 = 11 := by decide
  match n with
  | 0 | 1 | 2 => norm_num [a₀, a₁, a₂]
  | k+3 =>
    have h := congrArg (fun z : ℤ => (z : ℚ)) (recurrence k)
    push_cast at h
    simp [show 1 ≤ k+3 by omega, show 2 ≤ k+3 by omega, show 3 ≤ k+3 by omega,
      show k+3 ≠ 1 by omega, show k+3 ≠ 2 by omega, nsmul_eq_mul]
    linarith

end OMA.Rule14

theorem OMA.solution : type_of% @OMA.S_oeis_a277953.main := by
  refine ⟨Rule14.generatingFunction, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact_mod_cast (show S_oeis_a277953.a (3+k) =
        10 * S_oeis_a277953.a (3+k-1) + S_oeis_a277953.a (3+k-2) -
          10 * S_oeis_a277953.a (3+k-3) by
      simpa [Nat.add_comm 3 k] using Rule14.recurrence k)
  · intro n
    apply (eq_div_iff (by norm_num)).2
    rw [mul_comm]
    exact Rule14.closedForm n

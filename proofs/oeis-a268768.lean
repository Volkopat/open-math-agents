import OMAStatements.S_oeis_a268768

-- Count continuations by the bottom row and the remaining number of required pairs.
namespace A268768Proof

open OMA.S_oeis_a268768 PowerSeries

private abbrev Row := Fin 2 → Fin 3

private def pair (a b : Fin 3) : ℕ := if (a : ℕ) + (b : ℕ) = 2 then 1 else 0

private def horizontal (r : Row) := pair (r 0) (r 1)

-- Prepending r to a strip beginning with s introduces five adjacent pairs.
private def cost (r s : Row) : ℕ :=
  horizontal r + pair (r 0) (s 0) + pair (r 1) (s 1) +
    pair (r 0) (s 1) + pair (r 1) (s 0)

private theorem filter_count {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = ∑ i, if P i then 1 else 0 :=
  (Finset.sum_boole (R := ℕ) P _).symm

private theorem add_row (k : ℕ) (r : Row) (s : Fin (k+1) → Row) :
    pairsTotallingTwo (k+1) (Fin.cons r s) = cost r (s 0) + pairsTotallingTwo k s := by
  simp only [pairsTotallingTwo, filter_count, Fintype.sum_prod_type, Fin.sum_univ_succ,
    Fin.castSucc_succ, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
    show (0 : Fin 1).succ = (1 : Fin 2) from rfl,
    Finset.univ_eq_empty, Finset.sum_empty, cost, horizontal, pair]
  omega

-- The last argument records whether one or zero pairs are still required.
private def transfer (f : Row → Bool → ℤ) (r : Row) (b : Bool) : ℤ :=
  ∑ s : Row, if cost r s = 0 then f s b else if b = true ∧ cost r s = 1 then f s false else 0

private def F : ℕ → Row → Bool → ℤ
  | 0, r, b => if horizontal r = b.toNat then 1 else 0
  | k+1, r, b => transfer (F k) r b

private def total (k : ℕ) : ℤ := ∑ r : Row, F k r true

private theorem sum_rows {k : ℕ} (f : (Fin (k+1) → Row) → ℤ) :
    (∑ x, f x) = ∑ r : Row, ∑ x : Fin k → Row, f (Fin.cons r x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k+1) => Row)).sum_comp f, Fintype.sum_prod_type]
  rfl

private theorem tails (k : ℕ) (r : Row) (b : Bool) :
    (∑ s : Fin k → Row, if pairsTotallingTwo k (Fin.cons r s) = b.toNat then (1:ℤ) else 0) =
    F k r b := by
  induction k generalizing r b with
  | zero => revert r b; decide +kernel
  | succ k ih =>
    rw [sum_rows, F.eq_2, transfer]
    apply Finset.sum_congr rfl
    intro s _
    simp only [add_row, Fin.cons_zero]
    by_cases h : cost r s = 0
    · simp [h, ih]
    · by_cases h1 : cost r s = 1
      · cases b
        · simp [h1]
        · simpa [h,h1] using ih s false
      · have hm (u : ℕ) : cost r s + u ≠ b.toNat := by
          cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
        simp [h,h1,hm]

private theorem count (k : ℕ) : (a (k+1) : ℤ) = total k := by
  rw [a, ← Finset.sum_boole, sum_rows]
  exact Finset.sum_congr rfl fun r _ => tails k r true

-- The continuation vector has 18 entries. Its fourth-order recurrence starts
-- after the two exceptional boundary steps.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private theorem state_initial : ∀ (r : Row) (b : Bool),
    F 6 r b = 2 * F 5 r b + 3 * F 4 r b - 4 * F 3 r b - 4 * F 2 r b := by
  decide +kernel

private theorem state_rec (k : ℕ) (r : Row) (b : Bool) :
    F (k+6) r b = 2*F (k+5) r b + 3*F (k+4) r b - 4*F (k+3) r b - 4*F (k+2) r b := by
  induction k generalizing r b with
  | zero => exact state_initial r b
  | succ k ih =>
    change transfer (F (k+6)) r b = 2*transfer (F (k+5)) r b + 3*transfer (F (k+4)) r b
      - 4*transfer (F (k+3)) r b - 4*transfer (F (k+2)) r b
    unfold transfer
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hz : cost r s = 0
    · simpa only [if_pos hz] using ih s b
    · by_cases hs : b = true ∧ cost r s = 1
      · simpa only [if_neg hz, if_pos hs] using ih s false
      · simp [hz,hs]

private theorem total_rec (k : ℕ) :
    total (k+6) = 2*total (k+5) + 3*total (k+4) - 4*total (k+3) - 4*total (k+2) := by
  simp only [total, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun r _ => state_rec k r true

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
private theorem initial : total 0 = 3 ∧ total 1 = 12 ∧ total 2 = 32 ∧
    total 3 = 100 ∧ total 4 = 248 ∧ total 5 = 620 := by
  decide +kernel

private theorem recurrence (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℤ) = 2*a (n-1) + 3*a (n-2) - 4*a (n-3) - 4*a (n-4) := by
  by_cases h : n = 6
  · subst n
    norm_num [show ∀ j : ℕ, (a (j+1) : ℤ) = total j from count, initial]
  · obtain ⟨k,rfl⟩ : ∃ k, n = k+7 := ⟨n-7,by omega⟩
    change (a (k+6+1) : ℤ) = 2*a (k+5+1) + 3*a (k+4+1) - 4*a (k+3+1) - 4*a (k+2+1)
    simpa only [count] using total_rec k

private def closed (n : ℕ) : ℚ :=
  4 / 27 * (7 * ((-1)^n - 2^n) + 3 * ((-1)^n + 2^(2+n)) * n)

private theorem closed_rec (n : ℕ) : closed (n+4) = 2*closed (n+3) + 3*closed (n+2)
    - 4*closed (n+1) - 4*closed n := by
  simp [closed, pow_add]
  ring

private theorem rq (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℚ) = 2*a (n-1) + 3*a (n-2) - 4*a (n-3) - 4*a (n-4) := by
  exact_mod_cast recurrence n hn

private theorem small :
    (a 1 : ℚ) = 3 ∧ (a 2 : ℚ) = 12 ∧ (a 3 : ℚ) = 32 ∧ (a 4 : ℚ) = 100 ∧ (a 5 : ℚ) = 248 := by
  have h : (a 1 : ℤ) = 3 ∧ (a 2 : ℤ) = 12 ∧ (a 3 : ℤ) = 32 ∧
      (a 4 : ℤ) = 100 ∧ (a 5 : ℤ) = 248 := by
    norm_num [show ∀ k : ℕ, (a (k+1) : ℤ) = total k from count, initial]
  exact_mod_cast h

private theorem formula (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = closed n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n ≤ 5
    · interval_cases n <;> norm_num [closed, small.2.1, small.2.2.1, small.2.2.2.1, small.2.2.2.2]
    · obtain ⟨k,rfl⟩ : ∃ k, n = k+4 := ⟨n-4,by omega⟩
      rw [rq _ (by omega), ih (k+4-1) (by omega) (by omega), ih (k+4-2) (by omega) (by omega),
        ih (k+4-3) (by omega) (by omega), ih (k+4-4) (by omega) (by omega)]
      exact (closed_rec k).symm

private theorem series : mk (fun n => (a n : ℚ)) * ((1+X)^2*(1-2*X)^2) =
    X*(3+6*X-X^2+12*X^3+12*X^4) := by
  let A := mk (fun n => (a n : ℚ))
  change A * _ = _
  rw [show A * ((1+X)^2*(1-2*X)^2) =
      A - C 2 * (A*X^1) - C 3 * (A*X^2) + C 4 * (A*X^3) + C 4 * (A*X^4) by
        simp only [map_ofNat]; ring,
      show (X*(3+6*X-X^2+12*X^3+12*X^4) : PowerSeries ℚ) =
        C 3*X^1 + C 6*X^2 - X^3 + C 12*X^4 + C 12*X^5 by simp only [map_ofNat]; ring]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, A, coeff_mk]
  by_cases hn : n ≤ 5
  · have h0 : (a 0 : ℚ) = 0 := rfl
    interval_cases n <;> norm_num [h0,small.1,small.2.1,small.2.2.1,small.2.2.2.1,small.2.2.2.2]
  · simp (disch := omega) only [if_pos, if_neg, sub_zero, add_zero]
    linarith [rq n (by omega)]

end A268768Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a268768.main := by
  exact ⟨A268768Proof.recurrence, A268768Proof.series, A268768Proof.formula⟩

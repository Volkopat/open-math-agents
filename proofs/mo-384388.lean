import OMAStatements.S_mo_384388
import Mathlib

-- Problem: mo-384388, bounds for the weighted Catalan recurrence
-- C_0 = 1, C_{n+1} = (n+1)^a sum_{i <= n} C_i C_{n-i}, for a >= 0.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Upper bound C_n <= Cat_n (n!)^a by strong induction, using i! (n-i)! <= n! and the Catalan
-- recurrence; Cat_n <= 4^n / (n+1) because (n+1) Cat_n is the central binomial coefficient,
-- which is at most 2^(2n). Lower bound 2^n ((n+1)!)^a <= C_{n+1} by induction, keeping only
-- the two terms i = 0 and i = n of the sum. For a = 0 the recurrence is the Catalan one.

namespace MO384388

open OMA.S_mo_384388

theorem w_zero (α : ℝ) : weightedCatalan α 0 = 1 := by
  rw [weightedCatalan]

theorem w_succ (α : ℝ) (n : ℕ) : weightedCatalan α (n + 1) =
    ((n + 1 : ℕ) : ℝ) ^ α *
      ∑ i : Fin (n + 1), weightedCatalan α i * weightedCatalan α (n - i) := by
  rw [weightedCatalan]

theorem w_nonneg (α : ℝ) : ∀ n, 0 ≤ weightedCatalan α n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [w_zero]
      exact zero_le_one
    | succ k =>
      rw [w_succ]
      refine mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) α) (Finset.sum_nonneg ?_)
      intro i _
      have hi := i.isLt
      exact mul_nonneg (ih i (by omega)) (ih (k - i) (by omega))

theorem w_le (α : ℝ) (hα : 0 ≤ α) :
    ∀ n, weightedCatalan α n ≤ (catalan n : ℝ) * (n.factorial : ℝ) ^ α := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [w_zero]
    | succ k =>
      rw [w_succ]
      have hfac : ((k + 1).factorial : ℝ) ^ α =
          ((k + 1 : ℕ) : ℝ) ^ α * (k.factorial : ℝ) ^ α := by
        rw [Nat.factorial_succ, Nat.cast_mul,
          Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      have hsum : ∑ i : Fin (k + 1), weightedCatalan α i * weightedCatalan α (k - i) ≤
          (catalan (k + 1) : ℝ) * (k.factorial : ℝ) ^ α := by
        rw [catalan_succ, Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hi := i.isLt
        have h1 := ih i (by omega)
        have h2 := ih (k - i) (by omega)
        have hdvd : (i : ℕ).factorial * (k - i).factorial ≤ k.factorial :=
          Nat.le_of_dvd (Nat.factorial_pos k)
            (Nat.factorial_mul_factorial_dvd_factorial (by omega))
        have hpow : ((i : ℕ).factorial : ℝ) ^ α * ((k - i).factorial : ℝ) ^ α ≤
            (k.factorial : ℝ) ^ α := by
          rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
          exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hdvd) hα
        have n1 := w_nonneg α i
        have n2 := w_nonneg α (k - i)
        calc weightedCatalan α i * weightedCatalan α (k - i)
            ≤ ((catalan i : ℝ) * ((i : ℕ).factorial : ℝ) ^ α) *
                ((catalan (k - i) : ℝ) * ((k - i).factorial : ℝ) ^ α) :=
              mul_le_mul h1 h2 n2 (le_trans n1 h1)
          _ = (catalan i : ℝ) * (catalan (k - i) : ℝ) *
                (((i : ℕ).factorial : ℝ) ^ α * ((k - i).factorial : ℝ) ^ α) := by ring
          _ ≤ (catalan i : ℝ) * (catalan (k - i) : ℝ) * (k.factorial : ℝ) ^ α :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = ((catalan i * catalan (k - i) : ℕ) : ℝ) * (k.factorial : ℝ) ^ α := by
              push_cast
              ring
      calc ((k + 1 : ℕ) : ℝ) ^ α *
            ∑ i : Fin (k + 1), weightedCatalan α i * weightedCatalan α (k - i)
          ≤ ((k + 1 : ℕ) : ℝ) ^ α * ((catalan (k + 1) : ℝ) * (k.factorial : ℝ) ^ α) :=
            mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg _) α)
        _ = (catalan (k + 1) : ℝ) * ((k + 1).factorial : ℝ) ^ α := by
            rw [hfac]
            ring

theorem cat_le (n : ℕ) : (catalan n : ℝ) ≤ (4 : ℝ) ^ n / (n + 1) := by
  have h1 : (n + 1) * catalan n = n.centralBinom := succ_mul_catalan_eq_centralBinom n
  have h2 : n.centralBinom ≤ 4 ^ n := by
    calc n.centralBinom = (2 * n).choose n := Nat.centralBinom_eq_two_mul_choose n
      _ ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow (2 * n) n
      _ = 4 ^ n := by
          rw [pow_mul]
          norm_num
  rw [le_div_iff₀ (by positivity)]
  have h4 : (catalan n : ℝ) * ((n : ℝ) + 1) = ((n.centralBinom : ℕ) : ℝ) := by
    rw [← h1]
    push_cast
    ring
  rw [h4]
  exact_mod_cast h2

theorem w_one (α : ℝ) : weightedCatalan α 1 = 1 := by
  have h := w_succ α 0
  simp [w_zero] at h
  exact h

theorem two_terms (k : ℕ) (f : Fin (k + 1 + 1) → ℝ) (hf : ∀ i, 0 ≤ f i) :
    f 0 + f (Fin.last (k + 1)) ≤ ∑ i, f i := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hmid : 0 ≤ ∑ i : Fin k, f (Fin.succ (Fin.castSucc i)) :=
    Finset.sum_nonneg (fun i _ => hf _)
  have hlast : (Fin.last k).succ = Fin.last (k + 1) := rfl
  rw [hlast]
  linarith

theorem w_lower (α : ℝ) :
    ∀ n : ℕ, (2 : ℝ) ^ n * ((n + 1).factorial : ℝ) ^ α ≤ weightedCatalan α (n + 1) := by
  intro n
  induction n with
  | zero => simp [w_one]
  | succ k ih =>
    rw [w_succ α (k + 1)]
    have hfac : ((k + 1 + 1).factorial : ℝ) ^ α =
        ((k + 1 + 1 : ℕ) : ℝ) ^ α * ((k + 1).factorial : ℝ) ^ α := by
      rw [Nat.factorial_succ, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    have h2 := two_terms k
      (fun i => weightedCatalan α i * weightedCatalan α (k + 1 - i))
      (fun i => mul_nonneg (w_nonneg α _) (w_nonneg α _))
    simp only [Fin.val_zero, Fin.val_last, Nat.sub_zero, Nat.sub_self, w_zero, one_mul,
      mul_one] at h2
    have hrp : 0 ≤ ((k + 1 + 1 : ℕ) : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg _) α
    calc (2 : ℝ) ^ (k + 1) * ((k + 1 + 1).factorial : ℝ) ^ α
        = ((k + 1 + 1 : ℕ) : ℝ) ^ α *
            (2 * ((2 : ℝ) ^ k * ((k + 1).factorial : ℝ) ^ α)) := by
          rw [hfac, pow_succ]
          ring
      _ ≤ ((k + 1 + 1 : ℕ) : ℝ) ^ α * (2 * weightedCatalan α (k + 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) hrp
      _ ≤ ((k + 1 + 1 : ℕ) : ℝ) ^ α *
            ∑ i : Fin (k + 1 + 1), weightedCatalan α i * weightedCatalan α (k + 1 - i) :=
          mul_le_mul_of_nonneg_left (by linarith) hrp

theorem w_alpha_zero : ∀ n, weightedCatalan 0 n = (catalan n : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [w_zero]
    | succ k =>
      rw [w_succ, Real.rpow_zero, one_mul, catalan_succ, Nat.cast_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hi := i.isLt
      rw [ih i (by omega), ih (k - i) (by omega), Nat.cast_mul]

end MO384388

theorem OMA.solution : type_of% @OMA.S_mo_384388.main := by
  intro α hα
  refine ⟨fun n => ⟨MO384388.w_nonneg α n, MO384388.w_le α hα n, ?_⟩,
    MO384388.w_lower α, MO384388.w_alpha_zero⟩
  exact mul_le_mul_of_nonneg_right (MO384388.cat_le n)
    (Real.rpow_nonneg (Nat.cast_nonneg _) α)

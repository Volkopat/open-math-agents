import OMAStatements.S_oeis_a363986
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum


namespace OeisA363986Proof
open Finset Polynomial

/-- Falling factorial divided by `k!`, i.e., the generalized binomial coefficient `C(x, k)` in `ℚ`. -/
def qChoose (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => qChoose x k * (x - (k : ℚ)) / ((k + 1 : ℕ) : ℚ)

lemma qChoose_zero (x : ℚ) : qChoose x 0 = 1 := rfl

lemma qChoose_succ (x : ℚ) (k : ℕ) :
    qChoose x (k + 1) = qChoose x k * (x - (k : ℚ)) / ((k + 1 : ℕ) : ℚ) := rfl

lemma qChoose_nat (m k : ℕ) : qChoose (m : ℚ) k = (m.choose k : ℚ) := by
  induction k with
  | zero => simp [qChoose]
  | succ k ih =>
    rw [qChoose_succ, ih]
    have h := Nat.choose_succ_right_eq m k
    have hq : ((m.choose k : ℚ) * ((m - k : ℕ) : ℚ)) = (m.choose (k + 1) : ℚ) * ((k + 1 : ℕ) : ℚ) := by
      exact_mod_cast h.symm
    have hk1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    by_cases hkm : k ≤ m
    · have hsub : ((m - k : ℕ) : ℚ) = (m : ℚ) - (k : ℚ) := Nat.cast_sub hkm
      rw [hsub] at hq
      rw [hq, mul_div_cancel_right₀ _ hk1]
    · have hlt : m < k := Nat.lt_of_not_ge hkm
      have h1 : m.choose k = 0 := Nat.choose_eq_zero_of_lt hlt
      have h2 : m.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h1, h2]

lemma qChoose_pascal (x : ℚ) (k : ℕ) :
    qChoose (x + 1) (k + 1) = qChoose x (k + 1) + qChoose x k := by
  induction k with
  | zero =>
    simp [qChoose]
  | succ k ih =>
    rw [qChoose_succ (x + 1) (k + 1), ih, qChoose_succ x (k + 1), qChoose_succ x k]
    have h1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have h2 : ((k + 2 : ℕ) : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma qChoose_chu_vandermonde (x : ℚ) (m : ℕ) :
    ∀ k : ℕ, ∑ r ∈ range (k + 1), qChoose x r * (m.choose (k - r) : ℚ) = qChoose (x + m) k := by
  induction m with
  | zero =>
    intro k
    rw [Finset.sum_eq_single k]
    · simp
    · intro r hr hrk
      have hlt : r < k := by
        rw [Finset.mem_range] at hr; omega
      have h0 : (0 : ℕ).choose (k - r) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h0]
    · intro hk; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) hk
  | succ m ih =>
    intro k
    cases k with
    | zero => simp [qChoose]
    | succ k =>
      have hsplit : ∑ r ∈ range (k + 2), qChoose x r * ((m + 1).choose (k + 1 - r) : ℚ) =
          (∑ r ∈ range (k + 2), qChoose x r * (m.choose (k + 1 - r) : ℚ)) +
          (∑ r ∈ range (k + 1), qChoose x r * (m.choose (k - r) : ℚ)) := by
        rw [Finset.sum_range_succ (fun r => qChoose x r * ((m + 1).choose (k + 1 - r) : ℚ)) (k + 1)]
        rw [Finset.sum_range_succ (fun r => qChoose x r * (m.choose (k + 1 - r) : ℚ)) (k + 1)]
        simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one]
        have hsum : ∑ r ∈ range (k + 1), qChoose x r * ((m + 1).choose (k + 1 - r) : ℚ) =
            (∑ r ∈ range (k + 1), qChoose x r * (m.choose (k + 1 - r) : ℚ)) +
            (∑ r ∈ range (k + 1), qChoose x r * (m.choose (k - r) : ℚ)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun r hr => ?_)
          have hrk : r ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
          have hsub : k + 1 - r = (k - r) + 1 := by omega
          rw [hsub, Nat.choose_succ_succ]
          push_cast
          ring
        linarith
      rw [hsplit, ih (k + 1), ih k]
      have hcast : x + ((m + 1 : ℕ) : ℚ) = (x + (m : ℚ)) + 1 := by push_cast; ring
      rw [hcast, qChoose_pascal]

lemma qChoose_neg (x : ℚ) (k : ℕ) :
    qChoose (-x) k = (-1 : ℚ) ^ k * qChoose (x + (k : ℚ) - 1) k := by
  induction k with
  | zero => simp [qChoose]
  | succ k ih =>
    have hshift : qChoose (x + ((k + 1 : ℕ) : ℚ) - 1) (k + 1) =
        qChoose (x + (k : ℚ) - 1) k * (x + (k : ℚ)) / ((k + 1 : ℕ) : ℚ) := by
      -- Prove via direct product formula: qChoose y (k+1) = y / (k+1) * qChoose (y - 1) k
      have htop : ∀ (y : ℚ) (j : ℕ),
          qChoose y (j + 1) = y * qChoose (y - 1) j / ((j + 1 : ℕ) : ℚ) := by
        intro y j
        induction j with
        | zero => simp [qChoose]
        | succ j ihj =>
          rw [qChoose_succ y (j + 1), ihj, qChoose_succ (y - 1) j]
          have h1 : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
          have h2 : ((j + 2 : ℕ) : ℚ) ≠ 0 := by positivity
          push_cast
          field_simp
          ring
      have := htop (x + ((k + 1 : ℕ) : ℚ) - 1) k
      have h1 : x + ((k + 1 : ℕ) : ℚ) - 1 = x + (k : ℚ) := by push_cast; ring
      rw [h1] at this ⊢
      rw [this]
      ring
    rw [qChoose_succ (-x) k, ih, hshift, pow_succ]
    ring

lemma half_binom_lhs (n k : ℕ) :
    (((2 * n + 2 * k).choose (2 * k) * (2 * k).choose k : ℕ) : ℚ) =
      (4 : ℚ) ^ k * ((n + k).choose k : ℚ) * qChoose ((n : ℚ) + (k : ℚ) - 1 / 2) k := by
  induction k with
  | zero => simp [qChoose]
  | succ k ih =>
    have htop : ∀ (y : ℚ) (j : ℕ),
        qChoose y (j + 1) = y * qChoose (y - 1) j / ((j + 1 : ℕ) : ℚ) := by
      intro y j
      induction j with
      | zero => simp [qChoose]
      | succ j ihj =>
        rw [qChoose_succ y (j + 1), ihj, qChoose_succ (y - 1) j]
        have h1 : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        have h2 : ((j + 2 : ℕ) : ℚ) ≠ 0 := by positivity
        push_cast; field_simp; ring
    have hq_step : qChoose ((n : ℚ) + ((k + 1 : ℕ) : ℚ) - 1 / 2) (k + 1) =
        ((n : ℚ) + (k : ℚ) + 1 / 2) * qChoose ((n : ℚ) + (k : ℚ) - 1 / 2) k / ((k + 1 : ℕ) : ℚ) := by
      rw [htop]
      congr 2 <;> push_cast <;> ring
    have hnk_step : ((n + (k + 1)).choose (k + 1) : ℚ) * ((k + 1 : ℕ) : ℚ) =
        ((n + k).choose k : ℚ) * ((n + k + 1 : ℕ) : ℚ) := by
      have h := Nat.add_one_mul_choose_eq (n + k) k
      have : (n + (k + 1)).choose (k + 1) * (k + 1) = (n + k).choose k * (n + k + 1) := by
        simpa [Nat.add_assoc, Nat.mul_comm] using h.symm
      exact_mod_cast this
    have h2k_step : (((2 * n + 2 * (k + 1)).choose (2 * (k + 1)) * (2 * (k + 1)).choose (k + 1) : ℕ) : ℚ) *
        (((k + 1 : ℕ) : ℚ) ^ 2) =
        (((2 * n + 2 * k).choose (2 * k) * (2 * k).choose k : ℕ) : ℚ) *
        ((2 * n + 2 * k + 1 : ℕ) : ℚ) * ((2 * n + 2 * k + 2 : ℕ) : ℚ) := by
      -- Prove in Nat via factorial identity!
      have hnat : (2 * n + 2 * (k + 1)).choose (2 * (k + 1)) * (2 * (k + 1)).choose (k + 1) * (k + 1) ^ 2 =
          (2 * n + 2 * k).choose (2 * k) * (2 * k).choose k * (2 * n + 2 * k + 1) * (2 * n + 2 * k + 2) := by
        have h1 := Nat.choose_mul_factorial_mul_factorial (show 2 * (k + 1) ≤ 2 * n + 2 * (k + 1) by omega)
        have h2 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ 2 * (k + 1) by omega)
        have h3 := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ 2 * n + 2 * k by omega)
        have h4 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
        have hfac_pos : 0 < (2 * n).factorial * (k.factorial) ^ 2 * (2 * (k + 1)).factorial * (2 * k).factorial := by
          positivity
        apply Nat.eq_of_mul_eq_mul_right hfac_pos
        have hsub1 : 2 * n + 2 * (k + 1) - 2 * (k + 1) = 2 * n := by omega
        have hsub2 : 2 * (k + 1) - (k + 1) = k + 1 := by omega
        have hsub3 : 2 * n + 2 * k - 2 * k = 2 * n := by omega
        have hsub4 : 2 * k - k = k := by omega
        rw [hsub1] at h1; rw [hsub2] at h2; rw [hsub3] at h3; rw [hsub4] at h4
        have hf1 : (2 * n + 2 * (k + 1)).factorial =
            (2 * n + 2 * k + 2) * (2 * n + 2 * k + 1) * (2 * n + 2 * k).factorial := by
          rw [show 2 * n + 2 * (k + 1) = (2 * n + 2 * k + 1) + 1 by omega,
            Nat.factorial_succ, Nat.factorial_succ]; ring
        have hf2 : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
        have heq1 : (2 * n + 2 * (k + 1)).choose (2 * (k + 1)) * (2 * (k + 1)).choose (k + 1) *
            ((2 * (k + 1)).factorial * (2 * n).factorial * ((k + 1).factorial) ^ 2) =
            (2 * n + 2 * (k + 1)).factorial * (2 * (k + 1)).factorial := by
          calc _ = ((2 * n + 2 * (k + 1)).choose (2 * (k + 1)) * (2 * (k + 1)).factorial * (2 * n).factorial) *
                   ((2 * (k + 1)).choose (k + 1) * (k + 1).factorial * (k + 1).factorial) := by ring
            _ = (2 * n + 2 * (k + 1)).factorial * (2 * (k + 1)).factorial := by rw [h1, h2]
        have heq2 : (2 * n + 2 * k).choose (2 * k) * (2 * k).choose k *
            ((2 * k).factorial * (2 * n).factorial * (k.factorial) ^ 2) =
            (2 * n + 2 * k).factorial * (2 * k).factorial := by
          calc _ = ((2 * n + 2 * k).choose (2 * k) * (2 * k).factorial * (2 * n).factorial) *
                   ((2 * k).choose k * k.factorial * k.factorial) := by ring
            _ = (2 * n + 2 * k).factorial * (2 * k).factorial := by rw [h3, h4]
        calc (2 * n + 2 * (k + 1)).choose (2 * (k + 1)) * (2 * (k + 1)).choose (k + 1) * (k + 1) ^ 2 *
              ((2 * n).factorial * k.factorial ^ 2 * (2 * (k + 1)).factorial * (2 * k).factorial)
            = ((2 * n + 2 * (k + 1)).choose (2 * (k + 1)) * (2 * (k + 1)).choose (k + 1) *
                ((2 * (k + 1)).factorial * (2 * n).factorial * ((k + 1).factorial) ^ 2)) *
              (2 * k).factorial := by rw [hf2]; ring
          _ = (2 * n + 2 * (k + 1)).factorial * (2 * (k + 1)).factorial * (2 * k).factorial := by rw [heq1]
          _ = (2 * n + 2 * k).factorial * (2 * k).factorial *
              (2 * (k + 1)).factorial * (2 * n + 2 * k + 1) * (2 * n + 2 * k + 2) := by rw [hf1]; ring
          _ = ((2 * n + 2 * k).choose (2 * k) * (2 * k).choose k *
                ((2 * k).factorial * (2 * n).factorial * (k.factorial) ^ 2)) *
              (2 * (k + 1)).factorial * (2 * n + 2 * k + 1) * (2 * n + 2 * k + 2) := by rw [← heq2]
          _ = (2 * n + 2 * k).choose (2 * k) * (2 * k).choose k * (2 * n + 2 * k + 1) * (2 * n + 2 * k + 2) *
              ((2 * n).factorial * k.factorial ^ 2 * (2 * (k + 1)).factorial * (2 * k).factorial) := by ring
      exact_mod_cast hnat
    have hk1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    rw [hq_step]
    have hmul : (((2 * n + 2 * (k + 1)).choose (2 * (k + 1)) * (2 * (k + 1)).choose (k + 1) : ℕ) : ℚ) *
        ((k + 1 : ℕ) : ℚ) ^ 2 =
        ((4 : ℚ) ^ (k + 1) * ((n + (k + 1)).choose (k + 1) : ℚ) *
          (((n : ℚ) + (k : ℚ) + 1 / 2) * qChoose ((n : ℚ) + (k : ℚ) - 1 / 2) k / ((k + 1 : ℕ) : ℚ))) *
        ((k + 1 : ℕ) : ℚ) ^ 2 := by
      rw [h2k_step, ih]
      have hnk' : ((n + (k + 1)).choose (k + 1) : ℚ) =
          ((n + k).choose k : ℚ) * ((n + k + 1 : ℕ) : ℚ) / ((k + 1 : ℕ) : ℚ) := by
        rw [← hnk_step, mul_div_cancel_right₀ _ hk1]
      rw [hnk', pow_succ]
      push_cast
      field_simp
      ring
    exact mul_right_cancel₀ (pow_ne_zero 2 hk1) hmul

lemma half_binom_rhs (n m : ℕ) (hm : m ≤ n) :
    (4 : ℚ) ^ n * (n.choose m : ℚ) * qChoose ((n : ℚ) + (m : ℚ) - 1 / 2) n =
      (((2 * n).choose (n + m) * (2 * n + 2 * m).choose (2 * m) : ℕ) : ℚ) := by
  induction m with
  | zero =>
    simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.cast_zero, add_zero, Nat.add_zero,
      Nat.mul_zero]
    -- Show 4^n * qChoose (n - 1/2) n = C(2n, n)
    have h0 := half_binom_lhs 0 n
    simp only [Nat.mul_zero, Nat.zero_add, Nat.choose_self, Nat.one_mul, Nat.cast_zero, zero_add] at h0
    simpa [mul_comm, mul_left_comm] using h0.symm
  | succ m ih =>
    have hm' : m ≤ n := by omega
    have hih := ih hm'
    have hq_rel : qChoose ((n : ℚ) + ((m + 1 : ℕ) : ℚ) - 1 / 2) n * ((m : ℚ) + 1 / 2) =
        qChoose ((n : ℚ) + (m : ℚ) - 1 / 2) n * ((n : ℚ) + (m : ℚ) + 1 / 2) := by
      have hgen : ∀ (y : ℚ) (j : ℕ),
          qChoose (y + 1) j * (y + 1 - (j : ℚ)) = qChoose y j * (y + 1) := by
        intro y j
        induction j with
        | zero => simp [qChoose]
        | succ j ihj =>
          rw [qChoose_succ (y + 1) j, qChoose_succ y j]
          have h1 : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
          push_cast at ihj ⊢
          field_simp
          linear_combination (y - (j : ℚ)) * ihj
      have := hgen ((n : ℚ) + (m : ℚ) - 1 / 2) n
      have h1 : (n : ℚ) + (m : ℚ) - 1 / 2 + 1 = (n : ℚ) + ((m + 1 : ℕ) : ℚ) - 1 / 2 := by push_cast; ring
      have h2 : (n : ℚ) + ((m + 1 : ℕ) : ℚ) - 1 / 2 - (n : ℚ) = (m : ℚ) + 1 / 2 := by push_cast; ring
      have h3 : (n : ℚ) + ((m + 1 : ℕ) : ℚ) - 1 / 2 = (n : ℚ) + (m : ℚ) + 1 / 2 := by push_cast; ring
      rw [h1, h2] at this
      have h4 : qChoose ((n : ℚ) + ((m + 1 : ℕ) : ℚ) - 1 / 2) n * ((m : ℚ) + 1 / 2) =
          qChoose ((n : ℚ) + (m : ℚ) - 1 / 2) n * ((n : ℚ) + (m : ℚ) + 1 / 2) := by
        rw [this, h3]
      exact h4
    have hc1 : (n.choose (m + 1) : ℚ) * ((m + 1 : ℕ) : ℚ) = (n.choose m : ℚ) * ((n - m : ℕ) : ℚ) := by
      have h := Nat.choose_succ_right_eq n m
      have h' : n.choose (m + 1) * (m + 1) = n.choose m * (n - m) := by linarith
      exact_mod_cast h'
    have hnat_rhs :
        (2 * n).choose (n + (m + 1)) * (2 * n + 2 * (m + 1)).choose (2 * (m + 1)) *
          ((2 * m + 1) * (m + 1)) =
        (2 * n).choose (n + m) * (2 * n + 2 * m).choose (2 * m) *
          ((n - m) * (2 * n + 2 * m + 1)) := by
      have h1 := Nat.choose_mul_factorial_mul_factorial (show n + (m + 1) ≤ 2 * n by omega)
      have h2 := Nat.choose_mul_factorial_mul_factorial (show 2 * (m + 1) ≤ 2 * n + 2 * (m + 1) by omega)
      have h3 := Nat.choose_mul_factorial_mul_factorial (show n + m ≤ 2 * n by omega)
      have h4 := Nat.choose_mul_factorial_mul_factorial (show 2 * m ≤ 2 * n + 2 * m by omega)
      have hs1 : 2 * n - (n + (m + 1)) = n - m - 1 := by omega
      have hs2 : 2 * n + 2 * (m + 1) - 2 * (m + 1) = 2 * n := by omega
      have hs3 : 2 * n - (n + m) = n - m := by omega
      have hs4 : 2 * n + 2 * m - 2 * m = 2 * n := by omega
      rw [hs1] at h1; rw [hs2] at h2; rw [hs3] at h3; rw [hs4] at h4
      have hpos : 0 < (n + m).factorial * (n - m - 1).factorial * (2 * m).factorial * (2 * n).factorial := by
        positivity
      apply Nat.eq_of_mul_eq_mul_right hpos
      have hf_nm : (n - m).factorial = (n - m) * (n - m - 1).factorial := by
        have h : n - m = (n - m - 1) + 1 := by omega
        conv_lhs => rw [h]
        rw [Nat.factorial_succ, ← h]
      have hf_nmp : (n + (m + 1)).factorial = (n + m + 1) * (n + m).factorial := by
        rw [show n + (m + 1) = (n + m) + 1 by omega]; exact Nat.factorial_succ _
      have hf_2m : (2 * (m + 1)).factorial = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
        rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]; ring
      have hf_2n2m : (2 * n + 2 * (m + 1)).factorial =
          (2 * n + 2 * m + 2) * (2 * n + 2 * m + 1) * (2 * n + 2 * m).factorial := by
        rw [show 2 * n + 2 * (m + 1) = (2 * n + 2 * m + 1) + 1 by omega,
          Nat.factorial_succ, Nat.factorial_succ]; ring
      have h2m2 : 2 * m + 2 = 2 * (m + 1) := by omega
      have h2nm2 : 2 * n + 2 * m + 2 = 2 * (n + m + 1) := by omega
      have heqA : (2 * n).choose (n + (m + 1)) * (2 * n + 2 * (m + 1)).choose (2 * (m + 1)) *
          ((n + (m + 1)).factorial * (n - m - 1).factorial * (2 * (m + 1)).factorial * (2 * n).factorial) =
          (2 * n).factorial * (2 * n + 2 * (m + 1)).factorial := by
        calc _ = ((2 * n).choose (n + (m + 1)) * (n + (m + 1)).factorial * (n - m - 1).factorial) *
                 ((2 * n + 2 * (m + 1)).choose (2 * (m + 1)) * (2 * (m + 1)).factorial * (2 * n).factorial) := by ring
          _ = (2 * n).factorial * (2 * n + 2 * (m + 1)).factorial := by rw [h1, h2]
      have heqB : (2 * n).choose (n + m) * (2 * n + 2 * m).choose (2 * m) *
          ((n + m).factorial * (n - m).factorial * (2 * m).factorial * (2 * n).factorial) =
          (2 * n).factorial * (2 * n + 2 * m).factorial := by
        calc _ = ((2 * n).choose (n + m) * (n + m).factorial * (n - m).factorial) *
                 ((2 * n + 2 * m).choose (2 * m) * (2 * m).factorial * (2 * n).factorial) := by ring
          _ = (2 * n).factorial * (2 * n + 2 * m).factorial := by rw [h3, h4]
      -- Multiply both sides by 2 * (n + m + 1) to match heqA and heqB!
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 * (n + m + 1) by omega)
      calc 2 * (n + m + 1) *
            ((2 * n).choose (n + (m + 1)) * (2 * n + 2 * (m + 1)).choose (2 * (m + 1)) *
              ((2 * m + 1) * (m + 1)) *
              ((n + m).factorial * (n - m - 1).factorial * (2 * m).factorial * (2 * n).factorial))
          = (2 * n).choose (n + (m + 1)) * (2 * n + 2 * (m + 1)).choose (2 * (m + 1)) *
              ((n + (m + 1)).factorial * (n - m - 1).factorial * (2 * (m + 1)).factorial * (2 * n).factorial) := by
            rw [hf_nmp, hf_2m, h2m2]; ring
        _ = (2 * n).factorial * (2 * n + 2 * (m + 1)).factorial := heqA
        _ = (2 * n).factorial * (2 * n + 2 * m).factorial * (2 * (n + m + 1)) * (2 * n + 2 * m + 1) := by
            rw [hf_2n2m, h2nm2]; ring
        _ = ((2 * n).choose (n + m) * (2 * n + 2 * m).choose (2 * m) *
              ((n + m).factorial * (n - m).factorial * (2 * m).factorial * (2 * n).factorial)) *
              (2 * (n + m + 1)) * (2 * n + 2 * m + 1) := by rw [← heqB]
        _ = 2 * (n + m + 1) *
            ((2 * n).choose (n + m) * (2 * n + 2 * m).choose (2 * m) *
              ((n - m) * (2 * n + 2 * m + 1)) *
              ((n + m).factorial * (n - m - 1).factorial * (2 * m).factorial * (2 * n).factorial)) := by
            rw [hf_nm]; ring
    have hq_rhs : (((2 * n).choose (n + (m + 1)) * (2 * n + 2 * (m + 1)).choose (2 * (m + 1)) : ℕ) : ℚ) *
        (((2 * m + 1 : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ)) =
        (((2 * n).choose (n + m) * (2 * n + 2 * m).choose (2 * m) : ℕ) : ℚ) *
        (((n - m : ℕ) : ℚ) * ((2 * n + 2 * m + 1 : ℕ) : ℚ)) := by
      exact_mod_cast hnat_rhs
    have hden : ((2 * m + 1 : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    apply mul_right_cancel₀ hden
    rw [hq_rhs, ← hih]
    have hm1 : ((2 * m + 1 : ℕ) : ℚ) = 2 * ((m : ℚ) + 1 / 2) := by push_cast; ring
    have hnm1 : ((2 * n + 2 * m + 1 : ℕ) : ℚ) = 2 * ((n : ℚ) + (m : ℚ) + 1 / 2) := by push_cast; ring
    rw [hm1, hnm1]
    calc (4 : ℚ) ^ n * (n.choose (m + 1) : ℚ) * qChoose ((n : ℚ) + ((m + 1 : ℕ) : ℚ) - 1 / 2) n *
            (2 * ((m : ℚ) + 1 / 2) * ((m + 1 : ℕ) : ℚ))
        = 2 * (4 : ℚ) ^ n * ((n.choose (m + 1) : ℚ) * ((m + 1 : ℕ) : ℚ)) *
            (qChoose ((n : ℚ) + ((m + 1 : ℕ) : ℚ) - 1 / 2) n * ((m : ℚ) + 1 / 2)) := by ring
      _ = 2 * (4 : ℚ) ^ n * ((n.choose m : ℚ) * ((n - m : ℕ) : ℚ)) *
            (qChoose ((n : ℚ) + (m : ℚ) - 1 / 2) n * ((n : ℚ) + (m : ℚ) + 1 / 2)) := by
          rw [hc1, hq_rel]
      _ = (4 : ℚ) ^ n * (n.choose m : ℚ) * qChoose ((n : ℚ) + (m : ℚ) - 1 / 2) n *
            (((n - m : ℕ) : ℚ) * (2 * ((n : ℚ) + (m : ℚ) + 1 / 2))) := by ring

/-- Legendre polynomial identity `L1 = L3` in `ℚ[X]`. -/
lemma legendre_L1_eq_L3 (n : ℕ) :
    (∑ k ∈ range (n + 1), C ((-1 : ℚ) ^ k * (n.choose k : ℚ) * ((n + k).choose k : ℚ)) * X ^ k) =
    ∑ j ∈ range (n + 1), C ((-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 2) * X ^ j * (1 - X) ^ (n - j) := by
  ext k
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  by_cases hkn : k ≤ n
  · rw [Finset.sum_eq_single k]
    · simp only [↓reduceIte, mul_one]
      have hterm : ∀ j ∈ range (n + 1),
          (C ((-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 2) * X ^ j * (1 - X : ℚ[X]) ^ (n - j)).coeff k =
          if j ≤ k then (-1 : ℚ) ^ k * (n.choose j : ℚ) ^ 2 * ((n - j).choose (k - j) : ℚ) else 0 := by
        intro j _
        rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
        split_ifs with hjk
        · have hbin : ((1 - X : ℚ[X]) ^ (n - j)).coeff (k - j) =
              (-1 : ℚ) ^ (k - j) * ((n - j).choose (k - j) : ℚ) := by
            have hnegX : ∀ i : ℕ, ((-X : ℚ[X]) ^ i) = C ((-1 : ℚ) ^ i) * X ^ i := by
              intro i
              rw [show (-X : ℚ[X]) = C (-1 : ℚ) * X by simp, mul_pow, ← map_pow]
            have hadd2 : (1 - X : ℚ[X]) ^ (n - j) =
                ∑ i ∈ range (n - j + 1), C ((-1 : ℚ) ^ i * ((n - j).choose i : ℚ)) * X ^ i := by
              rw [sub_eq_add_neg, add_comm, add_pow]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [one_pow, mul_one, hnegX, map_mul]
              have hc : ((n - j).choose i : ℚ[X]) = C (((n - j).choose i : ℚ)) := by simp
              rw [hc]; ring
            rw [hadd2, finsetSum_coeff]
            simp only [coeff_C_mul, coeff_X_pow]
            rw [Finset.sum_eq_single (k - j)]
            · simp
            · intro i _ hik; simp [hik.symm]
            · intro hk'
              have hlt : n - j < k - j := by rw [Finset.mem_range] at hk'; omega
              have h0 : (n - j).choose (k - j) = 0 := Nat.choose_eq_zero_of_lt hlt
              simp [h0]
          rw [hbin]
          have hpow : (-1 : ℚ) ^ j * (-1 : ℚ) ^ (k - j) = (-1 : ℚ) ^ k := by
            rw [← pow_add, Nat.add_sub_cancel' hjk]
          linear_combination ((n.choose j : ℚ) ^ 2 * ((n - j).choose (k - j) : ℚ)) * hpow
        · simp
      rw [Finset.sum_congr rfl hterm]
      rw [← Finset.sum_filter]
      have hfilt : (range (n + 1)).filter (· ≤ k) = range (k + 1) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [hfilt]
      have hmul : ∀ j ∈ range (k + 1),
          (-1 : ℚ) ^ k * (n.choose j : ℚ) ^ 2 * ((n - j).choose (k - j) : ℚ) =
          (-1 : ℚ) ^ k * (n.choose k : ℚ) * ((n.choose j : ℚ) * (k.choose (k - j) : ℚ)) := by
        intro j hj
        have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hch : n.choose k * k.choose j = n.choose j * (n - j).choose (k - j) := by
          exact Nat.choose_mul hjk
        have hchq : (n.choose k : ℚ) * (k.choose j : ℚ) = (n.choose j : ℚ) * ((n - j).choose (k - j) : ℚ) := by
          exact_mod_cast hch
        rw [Nat.choose_symm hjk]
        linear_combination (-1 : ℚ) ^ k * (n.choose j : ℚ) * hchq.symm
      rw [Finset.sum_congr rfl hmul, ← Finset.mul_sum]
      have hcv := qChoose_chu_vandermonde (n : ℚ) k k
      simp only [qChoose_nat] at hcv
      have hnk : ((n : ℚ) + (k : ℚ)) = ((n + k : ℕ) : ℚ) := by push_cast; ring
      rw [hnk, qChoose_nat] at hcv
      rw [hcv]
    · intro i _ hik; simp [hik.symm]
    · intro hk; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hkn)) hk
  · have hlt : n < k := Nat.lt_of_not_ge hkn
    have hL : (∑ i ∈ range (n + 1), ((-1 : ℚ) ^ i * (n.choose i : ℚ) * ((n + i).choose i : ℚ)) *
        if k = i then (1 : ℚ) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      have : k ≠ i := by rw [Finset.mem_range] at hi; omega
      simp [this]
    have hR : (∑ j ∈ range (n + 1),
        (C ((-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 2) * X ^ j * (1 - X : ℚ[X]) ^ (n - j)).coeff k) = 0 := by
      refine Finset.sum_eq_zero (fun j hj => ?_)
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [mul_assoc, coeff_C_mul]
      have hdeg : (X ^ j * (1 - X : ℚ[X]) ^ (n - j)).natDegree ≤ n := by
        calc (X ^ j * (1 - X : ℚ[X]) ^ (n - j)).natDegree
            ≤ (X ^ j : ℚ[X]).natDegree + ((1 - X : ℚ[X]) ^ (n - j)).natDegree := natDegree_mul_le
          _ ≤ j + (n - j) * (1 - X : ℚ[X]).natDegree := by
              gcongr
              · simp
              · exact natDegree_pow_le
          _ ≤ j + (n - j) * 1 := by
              gcongr
              have : (1 - X : ℚ[X]).natDegree ≤ max (1 : ℚ[X]).natDegree (X : ℚ[X]).natDegree :=
                natDegree_sub_le _ _
              simpa using this
          _ = n := by omega
      rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hlt), mul_zero]
    rw [hL, hR]

/-- Legendre symmetry `L1 = L2` in `ℚ[X]`. -/
lemma legendre_L1_eq_L2 (n : ℕ) :
    (∑ k ∈ range (n + 1), C ((-1 : ℚ) ^ k * (n.choose k : ℚ) * ((n + k).choose k : ℚ)) * X ^ k) =
    C ((-1 : ℚ) ^ n) * ∑ j ∈ range (n + 1), C ((n.choose j : ℚ) * ((n + j).choose j : ℚ)) * (X - 1) ^ j := by
  have h1 := legendre_L1_eq_L3 n
  have hcomp := congrArg (fun P : ℚ[X] => P.comp (1 - X)) h1
  simp only [Polynomial.sum_comp, mul_comp, C_comp, pow_comp, X_comp, sub_comp, one_comp] at hcomp
  have h1m : (1 - (1 - X) : ℚ[X]) = X := by ring
  simp only [h1m] at hcomp
  -- Reindex RHS of hcomp by j ↦ n - j!
  have hre : (∑ j ∈ range (n + 1), C ((-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 2) * (1 - X) ^ j * X ^ (n - j)) =
      C ((-1 : ℚ) ^ n) * ∑ j ∈ range (n + 1), C ((-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 2) * X ^ j * (1 - X) ^ (n - j) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_range_reflect (fun j => C ((-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 2) * (1 - X) ^ j * X ^ (n - j)) (n + 1)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsub1 : n + 1 - 1 - j = n - j := by omega
    have hsub2 : n - (n - j) = j := by omega
    rw [hsub1, hsub2, Nat.choose_symm hjn]
    have hsign : (-1 : ℚ) ^ (n - j) = (-1 : ℚ) ^ n * (-1 : ℚ) ^ j := by
      have h1 : (-1 : ℚ) ^ (n - j) * (-1 : ℚ) ^ j = (-1 : ℚ) ^ n := by
        rw [← pow_add, Nat.sub_add_cancel hjn]
      have h2 : (-1 : ℚ) ^ j * (-1 : ℚ) ^ j = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      calc (-1 : ℚ) ^ (n - j) = (-1 : ℚ) ^ (n - j) * ((-1 : ℚ) ^ j * (-1 : ℚ) ^ j) := by rw [h2, mul_one]
        _ = ((-1 : ℚ) ^ (n - j) * (-1 : ℚ) ^ j) * (-1 : ℚ) ^ j := by ring
        _ = (-1 : ℚ) ^ n * (-1 : ℚ) ^ j := by rw [h1]
    rw [hsign, map_mul, map_mul, map_mul]
    ring
  rw [hre, ← h1] at hcomp
  have hmul := congrArg (fun P : ℚ[X] => C ((-1 : ℚ) ^ n) * P) hcomp
  have hsq : C ((-1 : ℚ) ^ n) * C ((-1 : ℚ) ^ n) = (1 : ℚ[X]) := by
    rw [← map_mul, ← pow_add, ← two_mul, pow_mul]; norm_num
  rw [← mul_assoc, hsq, one_mul] at hmul
  rw [← hmul]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hneg : (1 - X : ℚ[X]) ^ j = C ((-1 : ℚ) ^ j) * (X - 1) ^ j := by
    rw [show (1 - X : ℚ[X]) = C (-1 : ℚ) * (X - 1) by simp, mul_pow, ← map_pow]
  rw [hneg]
  have hsqj : (-1 : ℚ) ^ j * (-1 : ℚ) ^ j = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  calc C ((-1 : ℚ) ^ j * (n.choose j : ℚ) * ((n + j).choose j : ℚ)) * (C ((-1 : ℚ) ^ j) * (X - 1) ^ j)
      = C (((-1 : ℚ) ^ j * (-1 : ℚ) ^ j) * (n.choose j : ℚ) * ((n + j).choose j : ℚ)) * (X - 1) ^ j := by
        simp only [map_mul]; ring
    _ = C ((n.choose j : ℚ) * ((n + j).choose j : ℚ)) * (X - 1) ^ j := by rw [hsqj, one_mul]

/-- Linear functional on `ℚ[X]` mapping `X^k ↦ w k`, truncated at degree `n`. -/
def linFunc (n : ℕ) (w : ℕ → ℚ) (P : ℚ[X]) : ℚ :=
  ∑ k ∈ range (n + 1), P.coeff k * w k

lemma linFunc_add (n : ℕ) (w : ℕ → ℚ) (P Q : ℚ[X]) :
    linFunc n w (P + Q) = linFunc n w P + linFunc n w Q := by
  simp only [linFunc, coeff_add, add_mul, Finset.sum_add_distrib]

lemma linFunc_sum {ι : Type*} (s : Finset ι) (n : ℕ) (w : ℕ → ℚ) (f : ι → ℚ[X]) :
    linFunc n w (∑ i ∈ s, f i) = ∑ i ∈ s, linFunc n w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [linFunc]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, linFunc_add, ih]

lemma linFunc_C_mul (n : ℕ) (w : ℕ → ℚ) (c : ℚ) (P : ℚ[X]) :
    linFunc n w (C c * P) = c * linFunc n w P := by
  simp only [linFunc, coeff_C_mul, mul_assoc, ← Finset.mul_sum]

lemma linFunc_X_pow (n : ℕ) (w : ℕ → ℚ) (k : ℕ) (hk : k ≤ n) :
    linFunc n w (X ^ k) = w k := by
  simp only [linFunc, coeff_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hik; simp [hik]
  · intro hk'; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk)) hk'

/-- Main Part 1 identity: `a n = ∑_{j=0}^n C(n, j) * C(2n, n+j) * C(2n+2j, 2j)`. -/
theorem a_eq_S_sum (n : ℕ) :
    OMA.S_oeis_a363986.a n =
      ∑ j ∈ range (n + 1),
        ((n.choose j * (2 * n).choose (n + j) * (2 * n + 2 * j).choose (2 * j) : ℕ) : ℤ) := by
  apply Int.cast_injective (α := ℚ)
  unfold OMA.S_oeis_a363986.a
  push_cast
  let P1 : ℚ[X] := ∑ k ∈ range (n + 1), C ((-1 : ℚ) ^ k * (n.choose k : ℚ) * ((n + k).choose k : ℚ)) * X ^ k
  let P2 : ℚ[X] := C ((-1 : ℚ) ^ n) * ∑ j ∈ range (n + 1), C ((n.choose j : ℚ) * ((n + j).choose j : ℚ)) * (X - 1) ^ j
  let P3 : ℚ[X] := ∑ j ∈ range (n + 1), C ((-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 2) * X ^ j * (1 - X) ^ (n - j)
  let wPsi : ℕ → ℚ := fun k => (-1 : ℚ) ^ k * qChoose (-(n : ℚ) - 1 / 2) k
  let wPhi : ℕ → ℚ := fun k => (-1 : ℚ) ^ k * qChoose ((n : ℚ) - 1 / 2) k
  -- Step 1: (-4)^n * linFunc n wPsi P1 = LHS
  have hLHS : (-4 : ℚ) ^ n * linFunc n wPsi P1 =
      ∑ k ∈ range (n + 1), (-4 : ℚ) ^ (n - k) * (n.choose k : ℚ) *
        (((2 * n + 2 * k).choose (2 * k) : ℕ) : ℚ) * (((2 * k).choose k : ℕ) : ℚ) := by
    rw [linFunc_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [linFunc_C_mul, linFunc_X_pow n wPsi k hkn]
    have hneg := qChoose_neg ((n : ℚ) + 1 / 2) k
    have h1 : -((n : ℚ) + 1 / 2) = -(n : ℚ) - 1 / 2 := by ring
    have h2 : (n : ℚ) + 1 / 2 + (k : ℚ) - 1 = (n : ℚ) + (k : ℚ) - 1 / 2 := by ring
    rw [h1, h2] at hneg
    have hpsi : wPsi k = qChoose ((n : ℚ) + (k : ℚ) - 1 / 2) k := by
      simp only [wPsi, hneg]
      have hsq : (-1 : ℚ) ^ k * (-1 : ℚ) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
      linear_combination qChoose ((n : ℚ) + (k : ℚ) - 1 / 2) k * hsq
    rw [hpsi]
    have hhb := half_binom_lhs n k
    have h4 : (-4 : ℚ) ^ n * (-1 : ℚ) ^ k = (-4 : ℚ) ^ (n - k) * (4 : ℚ) ^ k := by
      have hn' : (-4 : ℚ) ^ n = (-4 : ℚ) ^ (n - k) * (-4 : ℚ) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hkn]
      rw [hn', show (-4 : ℚ) ^ k = (-1 : ℚ) ^ k * (4 : ℚ) ^ k by rw [← mul_pow]; norm_num]
      have hsq : (-1 : ℚ) ^ k * (-1 : ℚ) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
      linear_combination (-4 : ℚ) ^ (n - k) * (4 : ℚ) ^ k * hsq
    have hhb' : (((2 * n + 2 * k).choose (2 * k) : ℕ) : ℚ) * (((2 * k).choose k : ℕ) : ℚ) =
        (4 : ℚ) ^ k * ((n + k).choose k : ℚ) * qChoose ((n : ℚ) + (k : ℚ) - 1 / 2) k := by
      simpa [Nat.cast_mul] using hhb
    rw [mul_assoc ((-4 : ℚ) ^ (n - k) * (n.choose k : ℚ)), hhb']
    linear_combination (n.choose k : ℚ) * ((n + k).choose k : ℚ) * qChoose ((n : ℚ) + (k : ℚ) - 1 / 2) k * h4
  -- Step 2: (-4)^n * linFunc n wPsi P2 = 4^n * linFunc n wPhi P1
  have hMid : (-4 : ℚ) ^ n * linFunc n wPsi P2 = (4 : ℚ) ^ n * linFunc n wPhi P1 := by
    simp only [P2, P1]
    rw [linFunc_C_mul, linFunc_sum, linFunc_sum]
    have h4n : (-4 : ℚ) ^ n * (-1 : ℚ) ^ n = (4 : ℚ) ^ n := by
      rw [← mul_pow]; norm_num
    rw [← mul_assoc, h4n, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [linFunc_C_mul, linFunc_C_mul, linFunc_X_pow n wPhi j hjn]
    -- Compute linFunc n wPsi ((X - 1)^j) = (-1)^j * qChoose (j - n - 1/2) j = qChoose (n - 1/2) j
    have hXm1 : linFunc n wPsi ((X - 1) ^ j) = qChoose ((n : ℚ) - 1 / 2) j := by
      have hpow_exp : (X - 1 : ℚ[X]) ^ j =
          ∑ r ∈ range (j + 1), C ((-1 : ℚ) ^ (j - r) * (j.choose r : ℚ)) * X ^ r := by
        rw [sub_eq_add_neg, add_pow]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        have hc : ((j.choose r : ℕ) : ℚ[X]) = C (j.choose r : ℚ) := by simp
        rw [hc, ← C_1, ← C_neg, ← map_pow, map_mul]; ring
      rw [hpow_exp, linFunc_sum]
      have hterm : ∀ r ∈ range (j + 1),
          linFunc n wPsi (C ((-1 : ℚ) ^ (j - r) * (j.choose r : ℚ)) * X ^ r) =
            (-1 : ℚ) ^ j * (qChoose (-(n : ℚ) - 1 / 2) r * (j.choose (j - r) : ℚ)) := by
        intro r hr
        have hrj : r ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
        rw [linFunc_C_mul, linFunc_X_pow n wPsi r (le_trans hrj hjn)]
        simp only [wPsi]
        rw [Nat.choose_symm hrj]
        have hp : (-1 : ℚ) ^ (j - r) * (-1 : ℚ) ^ r = (-1 : ℚ) ^ j := by
          rw [← pow_add, Nat.sub_add_cancel hrj]
        linear_combination (j.choose r : ℚ) * qChoose (-(n : ℚ) - 1 / 2) r * hp
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, qChoose_chu_vandermonde]
      have hneg := qChoose_neg ((n : ℚ) - (j : ℚ) + 1 / 2) j
      have h1 : -((n : ℚ) - (j : ℚ) + 1 / 2) = -(n : ℚ) - 1 / 2 + (j : ℚ) := by ring
      have h2 : (n : ℚ) - (j : ℚ) + 1 / 2 + (j : ℚ) - 1 = (n : ℚ) - 1 / 2 := by ring
      rw [h1, h2] at hneg
      rw [hneg]
      have hsq : (-1 : ℚ) ^ j * (-1 : ℚ) ^ j = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
      linear_combination qChoose ((n : ℚ) - 1 / 2) j * hsq
    rw [hXm1]
    simp only [wPhi]
    have hsq : (-1 : ℚ) ^ j * (-1 : ℚ) ^ j = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    linear_combination (4 : ℚ) ^ n * (n.choose j : ℚ) * ((n + j).choose j : ℚ) * qChoose ((n : ℚ) - 1 / 2) j * hsq.symm
  -- Step 3: 4^n * linFunc n wPhi P3 = RHS
  have hRHS : (4 : ℚ) ^ n * linFunc n wPhi P3 =
      ∑ j ∈ range (n + 1),
        (((n.choose j * (2 * n).choose (n + j) * (2 * n + 2 * j).choose (2 * j) : ℕ) : ℚ)) := by
    simp only [P3]
    rw [linFunc_sum, Finset.mul_sum]
    rw [← Finset.sum_range_reflect (fun j => (((n.choose j * (2 * n).choose (n + j) * (2 * n + 2 * j).choose (2 * j) : ℕ) : ℚ))) (n + 1)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [mul_assoc, linFunc_C_mul]
    have hX1m : linFunc n wPhi (X ^ j * (1 - X) ^ (n - j)) =
        (-1 : ℚ) ^ j * qChoose ((2 * n - j : ℕ) - 1 / 2 : ℚ) n := by
      have hpow_exp : X ^ j * (1 - X : ℚ[X]) ^ (n - j) =
          ∑ r ∈ range (n - j + 1), C ((-1 : ℚ) ^ r * ((n - j).choose r : ℚ)) * X ^ (j + r) := by
        rw [sub_eq_add_neg, add_comm, add_pow, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        have hc : (((n - j).choose r : ℕ) : ℚ[X]) = C (((n - j).choose r : ℚ)) := by simp
        have hnegX : (-X : ℚ[X]) ^ r = C ((-1 : ℚ) ^ r) * X ^ r := by
          rw [show (-X : ℚ[X]) = C (-1 : ℚ) * X by simp, mul_pow, ← map_pow]
        rw [one_pow, mul_one, hnegX, hc, map_mul, pow_add]; ring
      rw [hpow_exp, linFunc_sum]
      have hterm : ∀ r ∈ range (n - j + 1),
          linFunc n wPhi (C ((-1 : ℚ) ^ r * ((n - j).choose r : ℚ)) * X ^ (j + r)) =
            (-1 : ℚ) ^ j * (qChoose ((n : ℚ) - 1 / 2) (j + r) * ((n - j).choose (n - (j + r)) : ℚ)) := by
        intro r hr
        have hrnj : r ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
        rw [linFunc_C_mul, linFunc_X_pow n wPhi (j + r) (by omega)]
        simp only [wPhi]
        rw [show n - (j + r) = (n - j) - r by omega, Nat.choose_symm hrnj]
        have hp : (-1 : ℚ) ^ r * (-1 : ℚ) ^ (j + r) = (-1 : ℚ) ^ j := by
          rw [pow_add]
          have hsq : (-1 : ℚ) ^ r * (-1 : ℚ) ^ r = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
          linear_combination (-1 : ℚ) ^ j * hsq
        linear_combination ((n - j).choose r : ℚ) * qChoose ((n : ℚ) - 1 / 2) (j + r) * hp
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      -- Pad the sum from r = 0..n-j to k = 0..n using (n-j).choose (n - k) = 0 for k < j!
      have hpad : ∑ r ∈ range (n - j + 1), qChoose ((n : ℚ) - 1 / 2) (j + r) * ((n - j).choose (n - (j + r)) : ℚ) =
          ∑ k ∈ range (n + 1), qChoose ((n : ℚ) - 1 / 2) k * ((n - j).choose (n - k) : ℚ) := by
        have hsplit : range (n + 1) = range j ∪ Ico j (n + 1) := by
          ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
        rw [hsplit, Finset.sum_union (by rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2; omega)]
        have hzero : ∑ k ∈ range j, qChoose ((n : ℚ) - 1 / 2) k * ((n - j).choose (n - k) : ℚ) = 0 := by
          refine Finset.sum_eq_zero (fun k hk => ?_)
          have hkj : k < j := Finset.mem_range.mp hk
          have h0 : (n - j).choose (n - k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          simp [h0]
        rw [hzero, zero_add]
        refine Finset.sum_bij (fun r _ => j + r) ?_ ?_ ?_ ?_
        · intro r hr; simp only [Finset.mem_range, Finset.mem_Ico] at hr ⊢; omega
        · intro r1 _ r2 _ h; omega
        · intro k hk; simp only [Finset.mem_Ico] at hk
          exact ⟨k - j, Finset.mem_range.mpr (by omega), by omega⟩
        · intro r _; rfl
      rw [hpad, qChoose_chu_vandermonde]
      congr 2
      have hcast : ((2 * n - j : ℕ) : ℚ) = (n : ℚ) + ((n - j : ℕ) : ℚ) := by
        have : 2 * n - j = n + (n - j) := by omega
        rw [this]; push_cast; ring
      rw [hcast]; ring
    rw [hX1m]
    have hsub : n + 1 - 1 - j = n - j := by omega
    rw [hsub]
    have hhr := half_binom_rhs n (n - j) (Nat.sub_le n j)
    have hcast2 : ((2 * n - j : ℕ) : ℚ) - 1 / 2 = (n : ℚ) + ((n - j : ℕ) : ℚ) - 1 / 2 := by
      have : 2 * n - j = n + (n - j) := by omega
      rw [this]; push_cast; ring
    rw [hcast2]
    have hsq : (-1 : ℚ) ^ j * (-1 : ℚ) ^ j = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [← Nat.choose_symm hjn]
    have hlhs_simp : (4 : ℚ) ^ n * ((-1 : ℚ) ^ j * (n.choose (n - j) : ℚ) ^ 2 *
        ((-1 : ℚ) ^ j * qChoose ((n : ℚ) + ((n - j : ℕ) : ℚ) - 1 / 2) n)) =
        (n.choose (n - j) : ℚ) * ((4 : ℚ) ^ n * (n.choose (n - j) : ℚ) *
          qChoose ((n : ℚ) + ((n - j : ℕ) : ℚ) - 1 / 2) n) := by
      linear_combination (4 : ℚ) ^ n * (n.choose (n - j) : ℚ) ^ 2 * qChoose ((n : ℚ) + ((n - j : ℕ) : ℚ) - 1 / 2) n * hsq
    rw [hlhs_simp, hhr]
    push_cast
    ring
  have hP12 : P1 = P2 := legendre_L1_eq_L2 n
  have hP13 : P1 = P3 := legendre_L1_eq_L3 n
  have htot : (-4 : ℚ) ^ n * linFunc n wPsi P1 =
      ∑ j ∈ range (n + 1),
        (((n.choose j * (2 * n).choose (n + j) * (2 * n + 2 * j).choose (2 * j) : ℕ) : ℚ)) := by
    rw [hP12, hMid, hP13, hRHS]
  rw [← hLHS, htot]
  refine Finset.sum_congr rfl (fun j _ => by push_cast; ring)

end OeisA363986Proof


namespace OeisA363986Part23
open Finset Polynomial

/-- `p^M` divides `q : ℚ` in `ℤ_{(p)}`, i.e., `q = p^M * a / b` with `0 < b` and `p ⊥ b`. -/
def pDvdRat (p M : ℕ) (q : ℚ) : Prop :=
  ∃ a : ℤ, ∃ b : ℕ, 0 < b ∧ Nat.Coprime p b ∧ q = (p : ℚ) ^ M * (a : ℚ) / (b : ℚ)

lemma pDvdRat_zero (p M : ℕ) : pDvdRat p M 0 :=
  ⟨0, 1, Nat.one_pos, Nat.coprime_one_right p, by simp⟩

lemma pDvdRat_mono {p M1 M2 : ℕ} {q : ℚ} (h : M1 ≤ M2) (hq : pDvdRat p M2 q) :
    pDvdRat p M1 q := by
  rcases hq with ⟨a, b, hb, hcop, rfl⟩
  refine ⟨(p : ℤ) ^ (M2 - M1) * a, b, hb, hcop, ?_⟩
  push_cast
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

lemma pDvdRat_neg {p M : ℕ} {q : ℚ} (hq : pDvdRat p M q) : pDvdRat p M (-q) := by
  rcases hq with ⟨a, b, hb, hcop, rfl⟩
  exact ⟨-a, b, hb, hcop, by push_cast; ring⟩

lemma pDvdRat_add {p M : ℕ} {q1 q2 : ℚ} (h1 : pDvdRat p M q1) (h2 : pDvdRat p M q2) :
    pDvdRat p M (q1 + q2) := by
  rcases h1 with ⟨a1, b1, hb1, hc1, rfl⟩
  rcases h2 with ⟨a2, b2, hb2, hc2, rfl⟩
  refine ⟨a1 * b2 + a2 * b1, b1 * b2, Nat.mul_pos hb1 hb2, hc1.mul_right hc2, ?_⟩
  have hb1q : (b1 : ℚ) ≠ 0 := by positivity
  have hb2q : (b2 : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma pDvdRat_sub {p M : ℕ} {q1 q2 : ℚ} (h1 : pDvdRat p M q1) (h2 : pDvdRat p M q2) :
    pDvdRat p M (q1 - q2) := by
  rw [sub_eq_add_neg]; exact pDvdRat_add h1 (pDvdRat_neg h2)

lemma pDvdRat_mul {p M1 M2 : ℕ} {q1 q2 : ℚ} (h1 : pDvdRat p M1 q1) (h2 : pDvdRat p M2 q2) :
    pDvdRat p (M1 + M2) (q1 * q2) := by
  rcases h1 with ⟨a1, b1, hb1, hc1, rfl⟩
  rcases h2 with ⟨a2, b2, hb2, hc2, rfl⟩
  refine ⟨a1 * a2, b1 * b2, Nat.mul_pos hb1 hb2, hc1.mul_right hc2, ?_⟩
  push_cast
  rw [pow_add]
  ring

lemma pDvdRat_pow {p M : ℕ} {q : ℚ} (hq : pDvdRat p M q) (k : ℕ) :
    pDvdRat p (k * M) (q ^ k) := by
  induction k with
  | zero => exact ⟨1, 1, Nat.one_pos, Nat.coprime_one_right p, by simp⟩
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact pDvdRat_mul ih hq

lemma pDvdRat_sum {ι : Type*} {s : Finset ι} {p M : ℕ} {f : ι → ℚ}
    (hf : ∀ i ∈ s, pDvdRat p M (f i)) : pDvdRat p M (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pDvdRat_zero p M
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact pDvdRat_add (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma pDvdRat_of_int {p M : ℕ} (z : ℤ) (hz : (p : ℤ) ^ M ∣ z) : pDvdRat p M (z : ℚ) := by
  rcases hz with ⟨a, rfl⟩
  exact ⟨a, 1, Nat.one_pos, Nat.coprime_one_right p, by push_cast; ring⟩

lemma pDvdRat_of_int_zero (p : ℕ) (z : ℤ) : pDvdRat p 0 (z : ℚ) :=
  pDvdRat_of_int z (by simp)

lemma pDvdRat_inv_nat {p d : ℕ} (hd : 0 < d) (hcop : Nat.Coprime p d) :
    pDvdRat p 0 ((d : ℚ)⁻¹) :=
  ⟨1, d, hd, hcop, by push_cast; rw [pow_zero, one_mul, one_div]⟩

lemma int_dvd_of_pDvdRat {p M : ℕ} {z : ℤ} (hz : pDvdRat p M (z : ℚ)) : (p : ℤ) ^ M ∣ z := by
  rcases hz with ⟨a, b, hb, hcop, heq⟩
  have hbq : (b : ℚ) ≠ 0 := by positivity
  have hmulq : (z : ℚ) * (b : ℚ) = (p : ℚ) ^ M * (a : ℚ) := by
    rw [heq, div_mul_cancel₀ _ hbq]
  have hmul : z * (b : ℤ) = (p : ℤ) ^ M * a := by exact_mod_cast hmulq
  have hdvd : (p : ℤ) ^ M ∣ (b : ℤ) * z := ⟨a, by linarith⟩
  have hcopZ : IsCoprime ((p : ℤ) ^ M) (b : ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr hcop).pow_left
  exact hcopZ.dvd_of_dvd_mul_left hdvd

lemma pDvdRat_div_nat {p M d E : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hvp : padicValNat p d ≤ E) (hEM : E ≤ M) {q : ℚ} (hq : pDvdRat p M q) :
    pDvdRat p (M - E) (q / (d : ℚ)) := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hq with ⟨a, b, hb, hcop, rfl⟩
  set v := padicValNat p d
  obtain ⟨d', hd'⟩ := pow_padicValNat_dvd (p := p) (n := d)
  have hd'_pos : 0 < d' := by
    rcases Nat.eq_zero_or_pos d' with rfl | hpos
    · simp at hd'; omega
    · exact hpos
  have hcop_d' : Nat.Coprime p d' := by
    rw [hp.coprime_iff_not_dvd]
    intro hpd'
    rcases hpd' with ⟨t, rfl⟩
    have h1 : p ^ (v + 1) ∣ d := ⟨t, by rw [hd', pow_succ]; ring⟩
    have h2 : v + 1 ≤ padicValNat p d := (padicValNat_dvd_iff_le (by omega)).mp h1
    omega
  refine ⟨(p : ℤ) ^ (E - v) * a, b * d', Nat.mul_pos hb hd'_pos, hcop.mul_right hcop_d', ?_⟩
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd_cast : (d : ℚ) = (p : ℚ) ^ v * (d' : ℚ) := by exact_mod_cast hd'
  rw [hd_cast]
  have hexp : M = (M - E) + (E - v) + v := by omega
  push_cast
  calc (p : ℚ) ^ M * (a : ℚ) / (b : ℚ) / ((p : ℚ) ^ v * (d' : ℚ))
      = (p : ℚ) ^ ((M - E) + (E - v) + v) * (a : ℚ) / ((b : ℚ) * (d' : ℚ) * (p : ℚ) ^ v) := by
          rw [← hexp]; ring
    _ = ((p : ℚ) ^ (M - E) * ((p : ℚ) ^ (E - v) * (a : ℚ)) / ((b : ℚ) * (d' : ℚ))) *
        ((p : ℚ) ^ v / (p : ℚ) ^ v) := by rw [pow_add, pow_add]; ring
    _ = (p : ℚ) ^ (M - E) * ((p : ℚ) ^ (E - v) * (a : ℚ)) / ((b : ℚ) * (d' : ℚ)) := by
        rw [div_self (pow_ne_zero v hpq), mul_one]

/-- For `p ≥ 5` prime and `k ≥ 1`, `4 * padicValNat p k ≤ k - 1`. -/
lemma four_mul_padicValNat_le {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    4 * padicValNat p k ≤ k - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  set v := padicValNat p k
  have hle : p ^ v ≤ k := Nat.le_of_dvd hk pow_padicValNat_dvd
  have h5v : 5 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp5 v
  have hlin : 4 * v + 1 ≤ 5 ^ v := by
    induction v with
    | zero => norm_num
    | succ v ih =>
      rw [pow_succ]
      omega
  omega

/-- For `p ≥ 5` prime and `m : ℕ`, `4 * padicValNat p m.factorial ≤ m`. -/
lemma four_mul_padicValNat_factorial_le {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    4 * padicValNat p m.factorial ≤ m := by
  have : Fact p.Prime := ⟨hp⟩
  have h := sub_one_mul_padicValNat_factorial (p := p) m
  have h4 : 4 ≤ p - 1 := by omega
  calc 4 * padicValNat p m.factorial
      ≤ (p - 1) * padicValNat p m.factorial := Nat.mul_le_mul_right _ h4
    _ = m - (p.digits m).sum := h
    _ ≤ m := Nat.sub_le _ _

/-- Truncated logarithm `∑_{k=1}^M (-1)^{k-1} u^k / k`. -/
def truncLog (M : ℕ) (u : ℚ) : ℚ :=
  ∑ k ∈ Icc 1 M, (-1 : ℚ) ^ (k - 1) * u ^ k / (k : ℚ)

lemma poly_coeff_pDvdRat_mul {p : ℕ} {P Q : ℚ[X]}
    (hP : ∀ i, pDvdRat p (2 * i) (P.coeff i))
    (hQ : ∀ i, pDvdRat p (2 * i) (Q.coeff i)) :
    ∀ j, pDvdRat p (2 * j) ((P * Q).coeff j) := by
  intro j
  rw [Polynomial.coeff_mul]
  refine pDvdRat_sum (fun x hx => ?_)
  have hsum : x.1 + x.2 = j := Finset.mem_antidiagonal.mp hx
  have hm := pDvdRat_mul (hP x.1) (hQ x.2)
  rwa [show 2 * x.1 + 2 * x.2 = 2 * j by omega] at hm

lemma poly_coeff_pDvdRat_pow {p : ℕ} {P : ℚ[X]}
    (hP : ∀ i, pDvdRat p (2 * i) (P.coeff i)) (k : ℕ) :
    ∀ j, pDvdRat p (2 * j) ((P ^ k).coeff j) := by
  induction k with
  | zero =>
    intro j
    rcases j with _ | j
    · simp; exact pDvdRat_of_int_zero p 1
    · rw [pow_zero, Polynomial.coeff_one]; simp [pDvdRat_zero]
  | succ k ih =>
    rw [pow_succ]
    exact poly_coeff_pDvdRat_mul ih hP

lemma coeff_zero_of_mul_unit_const {H P : ℚ[X]} (hH0 : H.coeff 0 = 1) (M : ℕ)
    (hHP : ∀ j < M, (H * P).coeff j = 0) : ∀ j < M, P.coeff j = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    have h0 := hHP j hj
    rw [Polynomial.coeff_mul] at h0
    have hsplit : ∑ x ∈ Finset.antidiagonal j, H.coeff x.1 * P.coeff x.2 =
        H.coeff 0 * P.coeff j := by
      rw [Finset.sum_eq_single (0, j)]
      · intro x hx hne
        have hsum : x.1 + x.2 = j := Finset.mem_antidiagonal.mp hx
        have hlt : x.2 < j := by
          by_contra hge
          have h2 : x.2 = j := by omega
          have h1 : x.1 = 0 := by omega
          exact hne (Prod.ext h1 h2)
        rw [ih x.2 hlt (lt_trans hlt hj), mul_zero]
      · intro hnot
        exact absurd (Finset.mem_antidiagonal.mpr (by omega)) hnot
    rw [hsplit, hH0, one_mul] at h0
    exact h0

lemma natDegree_finset_sum_le {ι R : Type*} [Semiring R] (s : Finset ι) (f : ι → R[X]) (d : ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ d) : (∑ i ∈ s, f i).natDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (natDegree_add_le _ _).trans
      (max_le (hf a (Finset.mem_insert_self a s)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))))

lemma nat_coprime_prod_right {ι : Type*} {s : Finset ι} {p : ℕ} {f : ι → ℕ}
    (hf : ∀ i ∈ s, Nat.Coprime p (f i)) : Nat.Coprime p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul_right
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma truncLog_mul {p M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {u v : ℚ}
    (hu : pDvdRat p 2 u) (hv : pDvdRat p 2 v) :
    pDvdRat p M (truncLog M (u + v + u * v) - truncLog M u - truncLog M v) := by
  let A : ℚ[X] := C (u + v) * X + C (u * v) * X ^ 2
  let Bu : ℚ[X] := C u * X
  let Bv : ℚ[X] := C v * X
  let G : ℚ[X] := ∑ k ∈ Icc 1 M,
    C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (A ^ k - Bu ^ k - Bv ^ k)
  have hGeval1 : G.eval 1 = truncLog M (u + v + u * v) - truncLog M u - truncLog M v := by
    simp only [G, truncLog, eval_finsetSum, eval_mul, eval_C, eval_sub, eval_pow, A, Bu, Bv,
      eval_add, eval_X, one_pow, mul_one]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  have hG0 : G.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    dsimp only [G]
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_eq_zero (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hne : k ≠ 0 := by omega
    simp [A, Bu, Bv, zero_pow hne]
  -- Derivative identity: (1 + Bu) * (1 + Bv) * G.derivative is divisible by X^M!
  have hderiv_pow : ∀ (P : ℚ[X]),
      (1 + P) * (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * P ^ (k - 1) * P.derivative) =
        P.derivative * (1 - (-P) ^ M) := by
    intro P
    have hsum : (1 + P) * (∑ k ∈ Icc 1 M, (-P) ^ (k - 1)) = 1 - (-P) ^ M := by
      have hgeom := geom_sum_mul (-P) M
      have hre : ∑ k ∈ Icc 1 M, (-P) ^ (k - 1) = ∑ i ∈ range M, (-P) ^ i := by
        refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢; omega
        · intro k1 hk1 k2 hk2 h; simp only [Finset.mem_Icc] at hk1 hk2; omega
        · intro i hi; exact ⟨i + 1, Finset.mem_Icc.mpr ⟨by omega, by rw [Finset.mem_range] at hi; omega⟩, by omega⟩
        · intro k _; rfl
      rw [hre]
      linear_combination -hgeom
    have hrew : ∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * P ^ (k - 1) * P.derivative =
        (∑ k ∈ Icc 1 M, (-P) ^ (k - 1)) * P.derivative := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hc : C ((-1 : ℚ) ^ (k - 1)) * P ^ (k - 1) = (-P) ^ (k - 1) := by
        rw [map_pow, map_neg, map_one, ← mul_pow]; simp
      rw [hc]
    rw [hrew, ← mul_assoc, hsum]
    ring
  have hGderiv : G.derivative =
      (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * A ^ (k - 1) * A.derivative) -
      (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * Bu ^ (k - 1) * Bu.derivative) -
      (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * Bv ^ (k - 1) * Bv.derivative) := by
    simp only [G, derivative_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkq : (k : ℚ) ≠ 0 := by positivity
    rw [derivative_mul, derivative_C, zero_mul, zero_add, derivative_sub, derivative_sub,
      derivative_pow, derivative_pow, derivative_pow]
    have hcancel : C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (k : ℚ[X]) = C ((-1 : ℚ) ^ (k - 1)) := by
      rw [← map_natCast C, ← map_mul, div_mul_cancel₀ _ hkq]
    calc C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) *
          ((k : ℚ[X]) * A ^ (k - 1) * A.derivative -
           (k : ℚ[X]) * Bu ^ (k - 1) * Bu.derivative -
           (k : ℚ[X]) * Bv ^ (k - 1) * Bv.derivative)
        = (C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (k : ℚ[X])) * A ^ (k - 1) * A.derivative -
          (C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (k : ℚ[X])) * Bu ^ (k - 1) * Bu.derivative -
          (C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (k : ℚ[X])) * Bv ^ (k - 1) * Bv.derivative := by ring
      _ = C ((-1 : ℚ) ^ (k - 1)) * A ^ (k - 1) * A.derivative -
          C ((-1 : ℚ) ^ (k - 1)) * Bu ^ (k - 1) * Bu.derivative -
          C ((-1 : ℚ) ^ (k - 1)) * Bv ^ (k - 1) * Bv.derivative := by rw [hcancel]
  have h1A : 1 + A = (1 + Bu) * (1 + Bv) := by
    simp only [A, Bu, Bv, map_add, map_mul]; ring
  have hAderiv : A.derivative = Bu.derivative * (1 + Bv) + Bv.derivative * (1 + Bu) := by
    simp only [A, Bu, Bv, derivative_mul, derivative_C, derivative_X,
      derivative_pow, map_add, map_mul, map_natCast]
    ring
  have hH_mul : ((1 + Bu) * (1 + Bv)) * G.derivative =
      -(A.derivative * (-A) ^ M) + (1 + Bv) * (Bu.derivative * (-Bu) ^ M) +
      (1 + Bu) * (Bv.derivative * (-Bv) ^ M) := by
    rw [hGderiv, mul_sub, mul_sub]
    have t1 : (1 + Bu) * (1 + Bv) *
        (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * A ^ (k - 1) * A.derivative) =
        A.derivative * (1 - (-A) ^ M) := by rw [← h1A, hderiv_pow A]
    have t2 : (1 + Bu) * (1 + Bv) *
        (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * Bu ^ (k - 1) * Bu.derivative) =
        (1 + Bv) * (Bu.derivative * (1 - (-Bu) ^ M)) := by
      rw [mul_comm (1 + Bu) (1 + Bv), mul_assoc, hderiv_pow Bu]
    have t3 : (1 + Bu) * (1 + Bv) *
        (∑ k ∈ Icc 1 M, C ((-1 : ℚ) ^ (k - 1)) * Bv ^ (k - 1) * Bv.derivative) =
        (1 + Bu) * (Bv.derivative * (1 - (-Bv) ^ M)) := by
      rw [mul_assoc, hderiv_pow Bv]
    rw [t1, t2, t3, hAderiv]
    ring
  have hXdvd_A : X ∣ A := ⟨C (u + v) + C (u * v) * X, by simp only [A]; ring⟩
  have hXdvd_Bu : X ∣ Bu := ⟨C u, by simp only [Bu]; ring⟩
  have hXdvd_Bv : X ∣ Bv := ⟨C v, by simp only [Bv]; ring⟩
  have hXM_dvd : X ^ M ∣ ((1 + Bu) * (1 + Bv)) * G.derivative := by
    rw [hH_mul]
    have d1 : X ^ M ∣ (-A) ^ M := pow_dvd_pow_of_dvd (dvd_neg.mpr hXdvd_A) M
    have d2 : X ^ M ∣ (-Bu) ^ M := pow_dvd_pow_of_dvd (dvd_neg.mpr hXdvd_Bu) M
    have d3 : X ^ M ∣ (-Bv) ^ M := pow_dvd_pow_of_dvd (dvd_neg.mpr hXdvd_Bv) M
    exact dvd_add (dvd_add (dvd_neg.mpr (dvd_mul_of_dvd_right d1 _))
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right d2 _) _))
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right d3 _) _)
  have hH0 : ((1 + Bu) * (1 + Bv)).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]; simp [Bu, Bv]
  have hGd_zero : ∀ j < M, G.derivative.coeff j = 0 := by
    refine coeff_zero_of_mul_unit_const hH0 M (fun j hj => ?_)
    rcases hXM_dvd with ⟨Q, hQ⟩
    rw [hQ, coeff_X_pow_mul']
    simp [Nat.not_le.mpr hj]
  have hG_coeff_zero : ∀ j ≤ M, G.coeff j = 0 := by
    intro j hj
    rcases j with _ | j
    · exact hG0
    · have h1 := hGd_zero j (by omega)
      rw [coeff_derivative] at h1
      have hne : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      exact (mul_eq_zero.mp h1).resolve_right (by push_cast at hne ⊢; exact hne)
  have hGdeg : G.natDegree ≤ 2 * M := by
    have hdegA : A.natDegree ≤ 2 := by
      calc A.natDegree ≤ max (C (u + v) * X).natDegree (C (u * v) * X ^ 2).natDegree := natDegree_add_le _ _
        _ ≤ max (0 + 1) (0 + 2) := by
          gcongr
          · exact natDegree_C_mul_le _ _ |>.trans (by simp)
          · exact natDegree_C_mul_le _ _ |>.trans (by simp)
        _ = 2 := by norm_num
    have hdegBu : Bu.natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp)
    have hdegBv : Bv.natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp)
    refine natDegree_finset_sum_le (Icc 1 M) _ (2 * M) (fun k hk => ?_)
    have hkM : k ≤ M := (Finset.mem_Icc.mp hk).2
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)
    · exact (natDegree_pow_le).trans (by nlinarith)
    · exact (natDegree_pow_le).trans (by nlinarith)
    · exact (natDegree_pow_le).trans (by nlinarith)
  rw [← hGeval1, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hGdeg)]
  simp only [one_pow, mul_one]
  refine pDvdRat_sum (fun j hj => ?_)
  by_cases hjM : j ≤ M
  · rw [hG_coeff_zero j hjM]; exact pDvdRat_zero p M
  · have hjgt : M < j := Nat.lt_of_not_ge hjM
    simp only [G, finsetSum_coeff, coeff_C_mul, coeff_sub]
    refine pDvdRat_sum (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkM : k ≤ M := (Finset.mem_Icc.mp hk).2
    have hBu0 : (Bu ^ k).coeff j = 0 := by
      have hdeg : (Bu ^ k).natDegree ≤ k :=
        (natDegree_pow_le).trans (by have : Bu.natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp); nlinarith)
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (lt_of_le_of_lt hkM hjgt))
    have hBv0 : (Bv ^ k).coeff j = 0 := by
      have hdeg : (Bv ^ k).natDegree ≤ k :=
        (natDegree_pow_le).trans (by have : Bv.natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans (by simp); nlinarith)
      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (lt_of_le_of_lt hkM hjgt))
    rw [hBu0, hBv0, sub_zero, sub_zero]
    have hAcoeff : ∀ i, pDvdRat p (2 * i) (A.coeff i) := by
      intro i
      rcases i with _ | _ | _ | i
      · have : A.coeff 0 = 0 := by simp [A]
        rw [this]; exact pDvdRat_zero p 0
      · have : A.coeff 1 = u + v := by
          simp only [A, coeff_add, coeff_C_mul, coeff_X_one, coeff_X_pow]
          norm_num
        rw [this]; exact pDvdRat_add hu hv
      · have : A.coeff 2 = u * v := by
          simp only [A, coeff_add, coeff_C_mul, coeff_X, coeff_X_pow]
          norm_num
        rw [this]; exact pDvdRat_mul hu hv
      · have hdeg : A.natDegree ≤ 2 := by
          calc A.natDegree ≤ max (C (u + v) * X).natDegree (C (u * v) * X ^ 2).natDegree := natDegree_add_le _ _
            _ ≤ max 1 2 := max_le_max ((natDegree_C_mul_le _ _).trans (by simp)) ((natDegree_C_mul_le _ _).trans (by simp))
            _ = 2 := by norm_num
        rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact pDvdRat_zero p _
    have hAkj : pDvdRat p (2 * j) ((A ^ k).coeff j) := poly_coeff_pDvdRat_pow hAcoeff k j
    have hvp : padicValNat p k ≤ j := by
      have h4 := four_mul_padicValNat_le hp hp5 hk1
      omega
    have hdiv := pDvdRat_div_nat hp (by omega : 0 < k) hvp (by omega : j ≤ 0 + 2 * j)
      (pDvdRat_mul (pDvdRat_of_int_zero p ((-1 : ℤ) ^ (k - 1))) hAkj)
    have hrew : ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * (A ^ k).coeff j =
        ((((-1 : ℤ) ^ (k - 1) : ℤ) : ℚ) * (A ^ k).coeff j) / (k : ℚ) := by push_cast; ring
    rw [hrew]
    exact pDvdRat_mono (by omega : M ≤ 0 + 2 * j - j) hdiv

lemma truncLog_prod {ι : Type*} (s : Finset ι) {p M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (u : ι → ℚ) (hu : ∀ i ∈ s, pDvdRat p 2 (u i)) :
    pDvdRat p 2 ((∏ i ∈ s, (1 + u i)) - 1) ∧
    pDvdRat p M (truncLog M ((∏ i ∈ s, (1 + u i)) - 1) - ∑ i ∈ s, truncLog M (u i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using pDvdRat_zero p 2, ?_⟩
    simp only [Finset.prod_empty, sub_self, Finset.sum_empty, sub_zero]
    have h0 : truncLog M 0 = 0 := by
      refine Finset.sum_eq_zero (fun k hk => ?_)
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [zero_pow (by omega : k ≠ 0), mul_zero, zero_div]
    rw [h0]; exact pDvdRat_zero p M
  | insert a s ha ih =>
    have hua : pDvdRat p 2 (u a) := hu a (Finset.mem_insert_self a s)
    obtain ⟨hP2, hPlog⟩ := ih (fun i hi => hu i (Finset.mem_insert_of_mem hi))
    set v := (∏ i ∈ s, (1 + u i)) - 1
    have hprod : (∏ i ∈ insert a s, (1 + u i)) - 1 = u a + v + u a * v := by
      rw [Finset.prod_insert ha]
      have : ∏ i ∈ s, (1 + u i) = 1 + v := by simp [v]
      rw [this]; ring
    rw [hprod, Finset.sum_insert ha]
    refine ⟨pDvdRat_add (pDvdRat_add hua hP2) (pDvdRat_mono (by omega : 2 ≤ 2 + 2) (pDvdRat_mul hua hP2)), ?_⟩
    have hstep := truncLog_mul (M := M) hp hp5 hua hP2
    have hcomb := pDvdRat_add hstep hPlog
    convert hcomb using 1
    ring

lemma truncLog_inj {p M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {w : ℚ}
    (hw2 : pDvdRat p 2 w) (hlog : pDvdRat p M (truncLog M w)) : pDvdRat p M w := by
  by_cases hM2 : M ≤ 2
  · exact pDvdRat_mono hM2 hw2
  · have hstep : ∀ t : ℕ, 2 ≤ t → t ≤ M → pDvdRat p t w := by
      intro t ht2 htM
      induction t with
      | zero => omega
      | succ t ih =>
        by_cases h2 : t + 1 ≤ 2
        · exact pDvdRat_mono h2 hw2
        · have ht : pDvdRat p t w := ih (by omega) (by omega)
          have hlog' : pDvdRat p (t + 1) (truncLog M w) := pDvdRat_mono htM hlog
          have htail : pDvdRat p (t + 1) (∑ k ∈ Icc 2 M, (-1 : ℚ) ^ (k - 1) * w ^ k / (k : ℚ)) := by
            refine pDvdRat_sum (fun k hk => ?_)
            have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
            have hwk : pDvdRat p (k * t) (w ^ k) := pDvdRat_pow ht k
            have hvp : padicValNat p k ≤ k - 1 := by
              have h4 := four_mul_padicValNat_le hp hp5 (by omega : 1 ≤ k)
              omega
            have ht_ge2 : 2 ≤ t := by omega
            have hkt : k + t ≤ k * t := by nlinarith
            have hdiv := pDvdRat_div_nat hp (by omega : 0 < k) hvp (by omega : k - 1 ≤ 0 + k * t)
              (pDvdRat_mul (pDvdRat_of_int_zero p ((-1 : ℤ) ^ (k - 1))) hwk)
            have hrew : (-1 : ℚ) ^ (k - 1) * w ^ k / (k : ℚ) =
                ((((-1 : ℤ) ^ (k - 1) : ℤ) : ℚ) * w ^ k) / (k : ℚ) := by push_cast; ring
            rw [hrew]
            exact pDvdRat_mono (by omega : t + 1 ≤ 0 + k * t - (k - 1)) hdiv
          have hsplit : truncLog M w = w + ∑ k ∈ Icc 2 M, (-1 : ℚ) ^ (k - 1) * w ^ k / (k : ℚ) := by
            unfold truncLog
            have hIcc : Icc 1 M = insert 1 (Icc 2 M) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hIcc, Finset.sum_insert (by simp)]
            simp
          have hw_eq : w = truncLog M w - ∑ k ∈ Icc 2 M, (-1 : ℚ) ^ (k - 1) * w ^ k / (k : ℚ) := by
            linarith
          rw [hw_eq]
          exact pDvdRat_sub hlog' htail
    exact hstep M (by omega) le_rfl

/-- Integer-scaled Faulhaber polynomial: `(faulhaberInt d).eval (B : ℤ) = (d+1)! * ∑_{j<B} j^d`. -/
noncomputable def faulhaberInt : ℕ → ℤ[X]
  | 0 => X
  | d + 1 =>
    C ((d + 1).factorial : ℤ) * X ^ (d + 2) -
    ∑ m ∈ (range (d + 1)).attach,
      C (((d + 2).choose m.1 * ((d + 1).factorial / (m.1 + 1).factorial) : ℕ) : ℤ) *
        faulhaberInt m.1
termination_by d => d
decreasing_by
  exact Finset.mem_range.mp m.2

lemma faulhaberInt_eval (d B : ℕ) :
    (faulhaberInt d).eval (B : ℤ) = ((d + 1).factorial : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    rcases d with _ | d
    · simp [faulhaberInt]
    · rw [faulhaberInt]
      simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_finsetSum]
      have htel : (B : ℤ) ^ (d + 2) = ∑ j ∈ range B, ((j + 1 : ℤ) ^ (d + 2) - (j : ℤ) ^ (d + 2)) := by
        have hgen : ∀ B' : ℕ, (B' : ℤ) ^ (d + 2) =
            ∑ j ∈ range B', ((j + 1 : ℤ) ^ (d + 2) - (j : ℤ) ^ (d + 2)) := by
          intro B'
          induction B' with
          | zero => simp
          | succ B' ihB =>
            rw [Finset.sum_range_succ, ← ihB]
            push_cast; ring
        exact hgen B
      have hexp : ∀ j : ℕ, (j + 1 : ℤ) ^ (d + 2) - (j : ℤ) ^ (d + 2) =
          ((d + 2 : ℕ) : ℤ) * (j : ℤ) ^ (d + 1) +
          ∑ m ∈ range (d + 1), ((d + 2).choose m : ℤ) * (j : ℤ) ^ m := by
        intro j
        rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ]
        simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one]
        have hch : (d + 2).choose (d + 1) = d + 2 := by
          rw [← Nat.choose_symm (by omega : d + 1 ≤ d + 2)]
          simp
        rw [hch]; ring
      have hsum_tel : (B : ℤ) ^ (d + 2) =
          ((d + 2 : ℕ) : ℤ) * (∑ j ∈ range B, (j : ℤ) ^ (d + 1)) +
          ∑ m ∈ range (d + 1), ((d + 2).choose m : ℤ) * (∑ j ∈ range B, (j : ℤ) ^ m) := by
        rw [htel, Finset.sum_congr rfl (fun j _ => hexp j), Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [← Finset.mul_sum]
      have hmul_tel := congrArg (fun z : ℤ => ((d + 1).factorial : ℤ) * z) hsum_tel
      have hfac : ((d + 1).factorial : ℤ) * ((d + 2 : ℕ) : ℤ) = ((d + 2).factorial : ℤ) := by
        have hnat : (d + 2).factorial = (d + 2) * (d + 1).factorial := Nat.factorial_succ (d + 1)
        rw [hnat]
        push_cast; ring
      rw [mul_add, ← mul_assoc, hfac] at hmul_tel
      have hmul_rhs : ((d + 1).factorial : ℤ) *
          ∑ m ∈ range (d + 1), ((d + 2).choose m : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ m =
          ∑ m ∈ range (d + 1), ((d + 1).factorial : ℤ) *
            (((d + 2).choose m : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ m) :=
        Finset.mul_sum _ _ _
      rw [hmul_rhs] at hmul_tel
      have hih_sum : ∑ m ∈ (range (d + 1)).attach,
          (((d + 2).choose m.1 * ((d + 1).factorial / (m.1 + 1).factorial) : ℕ) : ℤ) *
            (faulhaberInt m.1).eval (B : ℤ) =
          ∑ m ∈ range (d + 1), ((d + 1).factorial : ℤ) *
            (((d + 2).choose m : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ m) := by
        have hstep : ∑ m ∈ (range (d + 1)).attach,
            (((d + 2).choose m.1 * ((d + 1).factorial / (m.1 + 1).factorial) : ℕ) : ℤ) *
              (faulhaberInt m.1).eval (B : ℤ) =
            ∑ m ∈ (range (d + 1)).attach, ((d + 1).factorial : ℤ) *
              (((d + 2).choose m.1 : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ m.1) := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          have hmd : m.1 < d + 1 := Finset.mem_range.mp m.2
          rw [ih m.1 hmd]
          have hdvd : (m.1 + 1).factorial ∣ (d + 1).factorial := Nat.factorial_dvd_factorial (by omega)
          have hdiv : ((d + 1).factorial / (m.1 + 1).factorial : ℕ) * (m.1 + 1).factorial = (d + 1).factorial :=
            Nat.div_mul_cancel hdvd
          have hdivZ : (((d + 1).factorial / (m.1 + 1).factorial : ℕ) : ℤ) * ((m.1 + 1).factorial : ℤ) =
              ((d + 1).factorial : ℤ) := by exact_mod_cast hdiv
          rw [Nat.cast_mul]
          linear_combination ((d + 2).choose m.1 : ℤ) * (∑ j ∈ range B, (j : ℤ) ^ m.1) * hdivZ
        rw [hstep, Finset.sum_attach (range (d + 1)) (fun m =>
          ((d + 1).factorial : ℤ) * (((d + 2).choose m : ℤ) * ∑ j ∈ range B, (j : ℤ) ^ m))]
      rw [hih_sum]
      linarith

lemma faulhaberInt_eval_zero (d : ℕ) : (faulhaberInt d).eval 0 = 0 := by
  have := faulhaberInt_eval d 0
  simpa using this

/-- Power-sum divisibility: `B * D * (B + D)` divides `(2k+1)! * S_k(B, D)` in `ℤ`. -/
lemma power_sum_dvd (k B D : ℕ) :
    ((B * D * (B + D) : ℕ) : ℤ) ∣
      ((2 * k + 1).factorial : ℤ) *
        ∑ j ∈ range B, ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                        ((j : ℤ) * ((j : ℤ) + 1)) ^ k) := by
  -- Inner polynomial ring `ℤ[X]` represents variable `B`; outer `Polynomial (ℤ[X])` represents `D`.
  -- Auxiliary `Q : Polynomial (ℤ[X])` where inner `ℤ[X]` is `D` and outer `X` is `j`:
  let Q : Polynomial (ℤ[X]) :=
    ((C (X : ℤ[X]) + X) * (C (X : ℤ[X]) + X + 1)) ^ k - (X * (X + 1)) ^ k
  have hQdeg : Q.natDegree ≤ 2 * k := by
    have hd1 : ((C (X : ℤ[X]) + X) * (C (X : ℤ[X]) + X + 1)).natDegree ≤ 2 := by
      have h1 : (C (X : ℤ[X]) + X).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le (by simp) (by simp))
      have h2 : (C (X : ℤ[X]) + X + 1).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le h1 (by simp))
      exact natDegree_mul_le.trans (by omega)
    have hd2 : ((X : Polynomial (ℤ[X])) * (X + 1)).natDegree ≤ 2 := by
      have hX : (X : Polynomial (ℤ[X])).natDegree ≤ 1 := natDegree_X_le
      have h1 : ((X : Polynomial (ℤ[X])) + 1).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le hX (by simp))
      exact natDegree_mul_le.trans (by omega)
    exact (natDegree_sub_le _ _).trans (max_le (natDegree_pow_le.trans (by nlinarith))
      (natDegree_pow_le.trans (by nlinarith)))
  let Fsc : ℕ → ℤ[X] := fun m =>
    C (((2 * k + 1).factorial / (m + 1).factorial : ℕ) : ℤ) * faulhaberInt m
  let P_BD : Polynomial (ℤ[X]) :=
    ∑ m ∈ range (2 * k + 1), (Q.coeff m).map C * C (Fsc m)
  have hFsc_eval : ∀ m ∈ range (2 * k + 1), ∀ b : ℕ,
      (Fsc m).eval (b : ℤ) = ((2 * k + 1).factorial : ℤ) * ∑ j ∈ range b, (j : ℤ) ^ m := by
    intro m hm b
    have hmk : m ≤ 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    simp only [Fsc, eval_mul, eval_C, faulhaberInt_eval]
    have hdvd : (m + 1).factorial ∣ (2 * k + 1).factorial := Nat.factorial_dvd_factorial (by omega)
    have hdiv : ((2 * k + 1).factorial / (m + 1).factorial : ℕ) * (m + 1).factorial =
        (2 * k + 1).factorial := Nat.div_mul_cancel hdvd
    have hdivZ : (((2 * k + 1).factorial / (m + 1).factorial : ℕ) : ℤ) * ((m + 1).factorial : ℤ) =
        ((2 * k + 1).factorial : ℤ) := by exact_mod_cast hdiv
    rw [← mul_assoc, hdivZ]
  have hP_eval : ∀ (b : ℕ) (d : ℤ),
      (P_BD.eval (C d)).eval (b : ℤ) =
        ((2 * k + 1).factorial : ℤ) *
          ∑ j ∈ range b, (((d + (j : ℤ)) * (d + (j : ℤ) + 1)) ^ k - ((j : ℤ) * ((j : ℤ) + 1)) ^ k) := by
    intro b d
    have hmap_eval : ∀ (f : ℤ[X]), (f.map (C : ℤ →+* ℤ[X])).eval (C d) = C (f.eval d) := by
      intro f
      induction f using Polynomial.induction_on' with
      | add p q ihp ihq => rw [Polynomial.map_add, eval_add, ihp, ihq, eval_add, map_add]
      | monomial m c => simp
    have hlhs : (P_BD.eval (C d)).eval (b : ℤ) =
        ∑ m ∈ range (2 * k + 1), (Q.coeff m).eval d * (Fsc m).eval (b : ℤ) := by
      simp only [P_BD, eval_finsetSum, eval_mul, eval_C, hmap_eval]
    rw [hlhs]
    have h2 : ∑ m ∈ range (2 * k + 1), (Q.coeff m).eval d * (Fsc m).eval (b : ℤ) =
        ((2 * k + 1).factorial : ℤ) *
          ∑ j ∈ range b, ∑ m ∈ range (2 * k + 1), (Q.coeff m).eval d * (j : ℤ) ^ m := by
      rw [Finset.mul_sum]
      have hinner : ∑ j ∈ range b, ((2 * k + 1).factorial : ℤ) *
          ∑ m ∈ range (2 * k + 1), (Q.coeff m).eval d * (j : ℤ) ^ m =
          ∑ j ∈ range b, ∑ m ∈ range (2 * k + 1),
            ((2 * k + 1).factorial : ℤ) * ((Q.coeff m).eval d * (j : ℤ) ^ m) :=
        Finset.sum_congr rfl (fun j _ => Finset.mul_sum _ _ _)
      rw [hinner, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [hFsc_eval m hm b, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [h2]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hdeg_map : (Q.map (evalRingHom d)).natDegree ≤ 2 * k :=
      natDegree_map_le.trans hQdeg
    have hq_sum : ∑ m ∈ range (2 * k + 1), (Q.coeff m).eval d * (j : ℤ) ^ m =
        (Q.map (evalRingHom d)).eval (j : ℤ) := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg_map)]
      refine Finset.sum_congr rfl (fun m _ => by
        rw [coeff_map]; rfl)
    rw [hq_sum]
    simp only [Q, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_add,
      Polynomial.map_C, Polynomial.map_X, Polynomial.map_one, eval_sub, eval_pow, eval_mul,
      eval_add, eval_C, eval_X, eval_one]
    change (((X : ℤ[X]).eval d + (j : ℤ)) * ((X : ℤ[X]).eval d + (j : ℤ) + 1)) ^ k -
        ((j : ℤ) * ((j : ℤ) + 1)) ^ k = _
    simp
  -- Factor 1: X ∣ P_BD (since P_BD.eval 0 = 0)
  have hzero_of_nat : ∀ f : ℤ[X], (∀ b : ℕ, 1 ≤ b → f.eval (b : ℤ) = 0) → f = 0 := by
    intro f hf
    by_contra hne
    have hsub : (range (f.natDegree + 1)).image (fun b : ℕ => ((b + 1 : ℕ) : ℤ)) ⊆ f.roots.toFinset := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨b, _, rfl⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hf (b + 1) (by omega)
    have hinj : Function.Injective (fun b : ℕ => ((b + 1 : ℕ) : ℤ)) := fun a b h => by
      have := Int.ofNat.inj h; omega
    have hcard1 : ((range (f.natDegree + 1)).image (fun b : ℕ => ((b + 1 : ℕ) : ℤ))).card = f.natDegree + 1 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    have hcard2 : f.roots.toFinset.card ≤ f.natDegree :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' f)
    have := Finset.card_le_card hsub
    omega
  have hP_eval0 : P_BD.eval 0 = 0 := by
    apply hzero_of_nat
    intro b _
    simpa using hP_eval b 0
  obtain ⟨P1, hP1⟩ : X ∣ P_BD := by
    rw [show (X : Polynomial (ℤ[X])) = X - C 0 by simp, Polynomial.dvd_iff_isRoot]
    exact hP_eval0
  -- Factor 2: (X + C X) ∣ P1 (since P1.eval (-X) = 0; note `-X : ℤ[X]` is the element of the base ring!)
  have hP1_root : P1.eval (-X : ℤ[X]) = 0 := by
    apply hzero_of_nat
    intro b hb
    have h1 := hP_eval b (-(b : ℤ))
    have hsym : ∑ j ∈ range b, (((-(b : ℤ) + (j : ℤ)) * (-(b : ℤ) + (j : ℤ) + 1)) ^ k -
        ((j : ℤ) * ((j : ℤ) + 1)) ^ k) = 0 := by
      rw [Finset.sum_sub_distrib]
      have href := Finset.sum_range_reflect (fun j => ((j : ℤ) * ((j : ℤ) + 1)) ^ k) b
      have heq : ∑ j ∈ range b, ((-(b : ℤ) + (j : ℤ)) * (-(b : ℤ) + (j : ℤ) + 1)) ^ k =
          ∑ j ∈ range b, (((b - 1 - j : ℕ) : ℤ) * (((b - 1 - j : ℕ) : ℤ) + 1)) ^ k := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hjb : j ≤ b - 1 := by rw [Finset.mem_range] at hj; omega
        have hsub : ((b - 1 - j : ℕ) : ℤ) = (b : ℤ) - 1 - (j : ℤ) := by omega
        rw [hsub]; congr 1; ring
      rw [heq, href, sub_self]
    rw [hsym, mul_zero] at h1
    have hev_neg : ∀ R : Polynomial (ℤ[X]), (R.eval (-X : ℤ[X])).eval (b : ℤ) =
        (R.eval (C (-(b : ℤ)))).eval (b : ℤ) := by
      intro R
      induction R using Polynomial.induction_on' with
      | add p q ihp ihq => simp [ihp, ihq]
      | monomial m c =>
        simp only [eval_monomial, eval_mul, eval_pow, eval_neg, eval_C, eval_X]
    have h2 : (P_BD.eval (-X : ℤ[X])).eval (b : ℤ) = 0 := by rw [hev_neg, h1]
    rw [hP1, eval_mul, eval_X, eval_mul, eval_neg, eval_X] at h2
    have hbne : -(b : ℤ) ≠ 0 := by omega
    exact (mul_eq_zero.mp h2).resolve_left hbne
  obtain ⟨P2, hP2⟩ : (X - C (-X : ℤ[X]) : Polynomial (ℤ[X])) ∣ P1 := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hP1_root
  -- Factor 3: C X ∣ P2 (since evaluating inner B = 0 gives P_BD.map (evalRingHom 0) = 0!)
  have hP_map0 : P_BD.map (evalRingHom (0 : ℤ)) = 0 := by
    simp only [P_BD, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
    refine Finset.sum_eq_zero (fun m _ => ?_)
    have hF0 : (evalRingHom (0 : ℤ)) (Fsc m) = 0 := by
      change (Fsc m).eval 0 = 0
      simp [Fsc, faulhaberInt_eval_zero]
    rw [hF0, map_zero, mul_zero]
  have hP2_map0 : P2.map (evalRingHom (0 : ℤ)) = 0 := by
    have h1 := hP_map0
    rw [hP1, hP2, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C] at h1
    have h0neg : (evalRingHom (0 : ℤ)) (-X : ℤ[X]) = 0 := by
      change (-X : ℤ[X]).eval 0 = 0; simp
    rw [h0neg, map_zero, sub_zero] at h1
    have hX2 : (X : ℤ[X]) * (X : ℤ[X]) ≠ 0 := mul_ne_zero X_ne_zero X_ne_zero
    rw [← mul_assoc] at h1
    exact (mul_eq_zero.mp h1).resolve_left hX2
  have hP2_coeff0 : ∀ m, (X : ℤ[X]) ∣ P2.coeff m := by
    intro m
    rw [show (X : ℤ[X]) = X - C 0 by simp, Polynomial.dvd_iff_isRoot]
    have h := congrArg (fun f : ℤ[X] => f.coeff m) hP2_map0
    rw [coeff_map, coeff_zero] at h
    exact h
  -- Write P2 = C X * P3 by dividing each coefficient by X (via P2 = ∑ m, C (P2.coeff m) * X^m)
  have hCX_dvd_P2 : C (X : ℤ[X]) ∣ P2 := by
    rw [Polynomial.as_sum_range_C_mul_X_pow P2]
    refine Finset.dvd_sum (fun m _ => ?_)
    obtain ⟨q, hq⟩ := hP2_coeff0 m
    refine ⟨C q * X ^ m, ?_⟩
    rw [hq, map_mul, mul_assoc]
  obtain ⟨P3, hP3⟩ := hCX_dvd_P2
  -- Now evaluate P_BD = X * ((X - C (-X)) * (C X * P3)) at outer D and inner B!
  have hfinal := hP_eval B (D : ℤ)
  rw [hP1, hP2, hP3] at hfinal
  simp only [eval_mul, eval_sub, eval_X, eval_C, sub_neg_eq_add, eval_add] at hfinal
  refine ⟨(P3.eval (C (D : ℤ))).eval (B : ℤ), ?_⟩
  push_cast
  linarith

/-- For prime `p ≥ 5`, `p` divides the numerator of `∑_{i=1}^{(p-1)/2} (i*(p-i))⁻¹` in `ℤ_{(p)}`. -/
lemma half_sum_inv_p_dvd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    pDvdRat p 1 (∑ i ∈ Icc 1 ((p - 1) / 2), (((i * (p - i) : ℕ) : ℚ)⁻¹)) := by
  have : Fact p.Prime := ⟨hp⟩
  set h := (p - 1) / 2
  have h2h : 2 * h + 1 = p := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    omega
  -- Common denominator P = ∏ i ∈ Icc 1 h, (i * (p - i))
  set P : ℕ := ∏ i ∈ Icc 1 h, (i * (p - i))
  have hP_pos : 0 < P := Finset.prod_pos (fun i hi => by
    have := Finset.mem_Icc.mp hi; exact Nat.mul_pos (by omega) (by omega))
  have hP_cop : Nat.Coprime p P := by
    refine nat_coprime_prod_right (fun i hi => ?_)
    have hi' := Finset.mem_Icc.mp hi
    have hc1 : Nat.Coprime p i := (hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    have hc2 : Nat.Coprime p (p - i) := (hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    exact hc1.mul_right hc2
  -- Numerator N = ∑ i ∈ Icc 1 h, P / (i * (p - i))
  set N : ℕ := ∑ i ∈ Icc 1 h, P / (i * (p - i))
  have hsum_eq : ∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) = (N : ℚ) / (P : ℚ) := by
    have hPq : (P : ℚ) ≠ 0 := by positivity
    rw [eq_div_iff hPq, Finset.sum_mul]
    simp only [N, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hdvd : i * (p - i) ∣ P := Finset.dvd_prod_of_mem _ hi
    have hpos : 0 < i * (p - i) := by have := Finset.mem_Icc.mp hi; exact Nat.mul_pos (by omega) (by omega)
    have hmul : (P / (i * (p - i)) : ℕ) * (i * (p - i)) = P := Nat.div_mul_cancel hdvd
    have hmulq : ((P / (i * (p - i)) : ℕ) : ℚ) * ((i * (p - i) : ℕ) : ℚ) = (P : ℚ) := by exact_mod_cast hmul
    rw [← hmulq]
    have hne : ((i * (p - i) : ℕ) : ℚ) ≠ 0 := by positivity
    field_simp
  -- Show p ∣ N by working in ZMod p (which is a Field)!
  have hp_dvd_N : p ∣ N := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hPz : (P : ZMod p) ≠ 0 := by
      intro h0
      have hd : p ∣ P := (ZMod.natCast_eq_zero_iff P p).mp h0
      have h1 : p ∣ Nat.gcd p P := Nat.dvd_gcd dvd_rfl hd
      rw [hP_cop.gcd_eq_one] at h1
      exact hp.not_dvd_one h1
    have hNz : (N : ZMod p) = (P : ZMod p) * ∑ i ∈ Icc 1 h, -((i : ZMod p) ^ 2)⁻¹ := by
      simp only [N, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' := Finset.mem_Icc.mp hi
      have hiz : (i : ZMod p) ≠ 0 := by
        intro h0
        have := (ZMod.natCast_eq_zero_iff i p).mp h0
        exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) this
      have hpiz : ((i * (p - i) : ℕ) : ZMod p) = -((i : ZMod p) ^ 2) := by
        have hsub : ((p - i : ℕ) : ZMod p) = -(i : ZMod p) := by
          have h1 : ((p - i : ℕ) : ZMod p) + (i : ZMod p) = (p : ZMod p) := by
            rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
          rw [ZMod.natCast_self] at h1
          exact eq_neg_of_add_eq_zero_left h1
        rw [Nat.cast_mul, hsub]; ring
      have hdvd : i * (p - i) ∣ P := Finset.dvd_prod_of_mem _ hi
      have hmul : ((P / (i * (p - i)) : ℕ) : ZMod p) * ((i * (p - i) : ℕ) : ZMod p) = (P : ZMod p) := by
        rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
      rw [hpiz] at hmul
      have hsqne : -((i : ZMod p) ^ 2) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hiz)
      calc ((P / (i * (p - i)) : ℕ) : ZMod p)
          = ((P / (i * (p - i)) : ℕ) : ZMod p) * (-((i : ZMod p) ^ 2) * (-((i : ZMod p) ^ 2))⁻¹) := by
              rw [mul_inv_cancel₀ hsqne, mul_one]
        _ = (((P / (i * (p - i)) : ℕ) : ZMod p) * -((i : ZMod p) ^ 2)) * (-((i : ZMod p) ^ 2))⁻¹ := by ring
        _ = (P : ZMod p) * -((i : ZMod p) ^ 2)⁻¹ := by rw [hmul, inv_neg]
    -- Show ∑ i ∈ Icc 1 h, ((i : ZMod p) ^ 2)⁻¹ = 0
    have hsum_zero : ∑ i ∈ Icc 1 h, ((i : ZMod p) ^ 2)⁻¹ = 0 := by
      have hpair : ∑ i ∈ Icc 1 h, ((i : ZMod p) ^ 2)⁻¹ =
          ∑ i ∈ Icc (h + 1) (p - 1), ((i : ZMod p) ^ 2)⁻¹ := by
        refine Finset.sum_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
        · intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega
        · intro i1 hi1 i2 hi2 heq; simp only [Finset.mem_Icc] at hi1 hi2; omega
        · intro j hj; simp only [Finset.mem_Icc] at hj
          exact ⟨p - j, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro i hi
          have hi' := Finset.mem_Icc.mp hi
          have hsub : ((p - i : ℕ) : ZMod p) = -(i : ZMod p) := by
            have h1 : ((p - i : ℕ) : ZMod p) + (i : ZMod p) = (p : ZMod p) := by
              rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
            rw [ZMod.natCast_self] at h1
            exact eq_neg_of_add_eq_zero_left h1
          rw [hsub, neg_sq]
      have hfull : (∑ i ∈ Icc 1 h, ((i : ZMod p) ^ 2)⁻¹) +
          (∑ i ∈ Icc (h + 1) (p - 1), ((i : ZMod p) ^ 2)⁻¹) =
          ∑ x : ZMod p, (x ^ 2)⁻¹ := by
        rw [← Finset.sum_union (by
          rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [Finset.mem_Icc] at hx1 hx2; omega)]
        have hun : Icc 1 h ∪ Icc (h + 1) (p - 1) = Ico 1 p := by
          ext x; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico]; omega
        rw [hun]
        have h0 : ∑ x : ZMod p, (x ^ 2)⁻¹ = ∑ x ∈ Finset.univ.erase (0 : ZMod p), (x ^ 2)⁻¹ := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
          rw [zero_pow (by decide : 2 ≠ 0), inv_zero, zero_add]
        rw [h0]
        refine Finset.sum_bij (fun i _ => (i : ZMod p)) ?_ ?_ ?_ ?_
        · intro i hi
          have hi' := Finset.mem_Ico.mp hi
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
          intro hzero
          exact Nat.not_dvd_of_pos_of_lt hi'.1 hi'.2 ((ZMod.natCast_eq_zero_iff i p).mp hzero)
        · intro i1 hi1 i2 hi2 heq
          have h1 := Finset.mem_Ico.mp hi1
          have h2 := Finset.mem_Ico.mp hi2
          have hv := congrArg ZMod.val heq
          rwa [ZMod.val_natCast_of_lt h1.2, ZMod.val_natCast_of_lt h2.2] at hv
        · intro x hx
          have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
          have hlt : x.val < p := ZMod.val_lt x
          have hpos : 1 ≤ x.val := by
            rcases Nat.eq_zero_or_pos x.val with h0' | hp'
            · exact absurd ((ZMod.val_eq_zero x).mp h0') hx0
            · exact hp'
          exact ⟨x.val, Finset.mem_Ico.mpr ⟨hpos, hlt⟩, ZMod.natCast_zmod_val x⟩
        · intro _ _; rfl
      have hall0 : ∑ x : ZMod p, (x ^ 2)⁻¹ = 0 := by
        have h2ne : (2 : ZMod p) ≠ 0 := by
          intro h0; have := (ZMod.natCast_eq_zero_iff 2 p).mp h0
          have := Nat.le_of_dvd (by decide) this; omega
        have h3ne : (3 : ZMod p) ≠ 0 := by
          intro h0; have := (ZMod.natCast_eq_zero_iff 3 p).mp h0
          have := Nat.le_of_dvd (by decide) this; omega
        set T : ZMod p := ∑ x : ZMod p, (x ^ 2)⁻¹
        have hmul : (2 : ZMod p) ^ 2 * T = T := by
          rw [Finset.mul_sum]
          have h1 : ∀ x : ZMod p, (2 : ZMod p) ^ 2 * (x ^ 2)⁻¹ = (((2 : ZMod p)⁻¹ * x) ^ 2)⁻¹ := by
            intro x; rw [mul_pow, mul_inv, inv_pow, inv_inv]
          rw [Finset.sum_congr rfl (fun x _ => h1 x)]
          exact Fintype.sum_equiv (Equiv.mulLeft₀ (2 : ZMod p)⁻¹ (inv_ne_zero h2ne)) _ _ (fun _ => rfl)
        have h3T : (3 : ZMod p) * T = 0 := by
          have : (3 : ZMod p) = (2 : ZMod p) ^ 2 - 1 := by norm_num
          rw [this, sub_mul, one_mul, hmul, sub_self]
        exact (mul_eq_zero.mp h3T).resolve_left h3ne
      rw [hall0, ← hpair, ← two_mul] at hfull
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h0; have := (ZMod.natCast_eq_zero_iff 2 p).mp h0
        have := Nat.le_of_dvd (by decide) this; omega
      exact (mul_eq_zero.mp hfull).resolve_left h2ne
    rw [hNz, Finset.sum_neg_distrib, hsum_zero, neg_zero, mul_zero]
  obtain ⟨q, hq⟩ := hp_dvd_N
  refine ⟨q, P, hP_pos, hP_cop, ?_⟩
  rw [hsum_eq, hq]; push_cast; ring

/-- Block product `F p m = ∏_{i=1}^{p-1} (m * p + i)`. -/
def Fblock (p m : ℕ) : ℕ := ∏ i ∈ Ico 1 p, (m * p + i)

lemma Fblock_coprime {p : ℕ} (hp : p.Prime) (m : ℕ) : Nat.Coprime p (Fblock p m) := by
  refine nat_coprime_prod_right (fun i hi => ?_)
  have hi' := Finset.mem_Ico.mp hi
  rw [hp.coprime_iff_not_dvd]
  intro hd
  have hd_i : p ∣ i := (Nat.dvd_add_right (dvd_mul_left p m)).mp hd
  exact Nat.not_dvd_of_pos_of_lt hi'.1 hi'.2 hd_i

lemma Fblock_pair {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (m : ℕ) :
    (Fblock p m : ℚ) = ∏ i ∈ Icc 1 ((p - 1) / 2),
      (((i * (p - i) : ℕ) : ℚ) + ((m * (m + 1) : ℕ) : ℚ) * (p : ℚ) ^ 2) := by
  set h := (p - 1) / 2
  have h2h : 2 * h + 1 = p := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    omega
  unfold Fblock
  have hsplit : Ico 1 p = Icc 1 h ∪ Icc (h + 1) (p - 1) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Icc 1 h) (Icc (h + 1) (p - 1)) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [Finset.mem_Icc] at hx1 hx2; omega
  rw [hsplit, Finset.prod_union hdisj, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod]
  have hbij : ∏ i ∈ Icc (h + 1) (p - 1), ((m * p + i : ℕ) : ℚ) =
      ∏ i ∈ Icc 1 h, ((m * p + (p - i) : ℕ) : ℚ) := by
    refine Finset.prod_bij (fun j _ => p - j) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
    · intro j1 hj1 j2 hj2 heq; simp only [Finset.mem_Icc] at hj1 hj2; omega
    · intro i hi; simp only [Finset.mem_Icc] at hi
      exact ⟨p - i, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj; simp only [Finset.mem_Icc] at hj; congr 1; omega
  rw [hbij, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hi' := Finset.mem_Icc.mp hi
  have hsub : ((p - i : ℕ) : ℚ) = (p : ℚ) - (i : ℚ) := Nat.cast_sub (by omega)
  push_cast
  rw [hsub]
  ring

lemma factorial_mul_eq {p : ℕ} (hp : 0 < p) (m : ℕ) :
    (m * p).factorial = p ^ m * m.factorial * ∏ j ∈ range m, Fblock p j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : ((m + 1) * p).factorial = (m * p).factorial * ∏ i ∈ Icc 1 p, (m * p + i) := by
      have hgen : ∀ a k : ℕ, (a + k).factorial = a.factorial * ∏ i ∈ Icc 1 k, (a + i) := by
        intro a k
        induction k with
        | zero => simp
        | succ k ihk =>
          rw [show a + (k + 1) = (a + k) + 1 by omega, Nat.factorial_succ, ihk]
          have hIcc : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.prod_insert (by simp)]
          ring
      simpa [Nat.add_mul] using hgen (m * p) p
    have hIcc : ∏ i ∈ Icc 1 p, (m * p + i) = ((m + 1) * p) * Fblock p m := by
      have hs : Icc 1 p = insert p (Ico 1 p) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
      rw [hs, Finset.prod_insert (by simp), Fblock]
      have : m * p + p = (m + 1) * p := by ring
      rw [this]
    rw [hsplit, hIcc, ih, Finset.prod_range_succ, pow_succ, Nat.factorial_succ]
    ring

lemma choose_mul_Fblock {p : ℕ} (hp : 0 < p) (B D : ℕ) :
    ((B + D) * p).choose (B * p) * (∏ j ∈ range B, Fblock p j) =
      (B + D).choose B * (∏ j ∈ range B, Fblock p (D + j)) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show B * p ≤ (B + D) * p by nlinarith)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show B ≤ B + D by omega)
  have hs1 : (B + D) * p - B * p = D * p := by
    rw [Nat.add_mul, Nat.add_sub_cancel_left]
  have hs2 : B + D - B = D := Nat.add_sub_cancel_left B D
  rw [hs1] at h1; rw [hs2] at h2
  have hprod_split : ∏ j ∈ range (B + D), Fblock p j =
      (∏ j ∈ range D, Fblock p j) * (∏ j ∈ range B, Fblock p (D + j)) := by
    have hs : range (B + D) = range D ∪ Ico D (B + D) := by
      ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hd : Disjoint (range D) (Ico D (B + D)) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2; omega
    rw [hs, Finset.prod_union hd]
    congr 1
    refine Finset.prod_bij (fun j _ => j - D) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
    · intro j1 hj1 j2 hj2 heq; simp only [Finset.mem_Ico] at hj1 hj2; omega
    · intro j hj; simp only [Finset.mem_range] at hj
      exact ⟨D + j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj; simp only [Finset.mem_Ico] at hj; congr 1; omega
  have hpos : 0 < p ^ (B + D) * B.factorial * D.factorial * (∏ j ∈ range D, Fblock p j) := by
    have hFp : 0 < ∏ j ∈ range D, Fblock p j :=
      Finset.prod_pos (fun j _ => Finset.prod_pos (fun i hi => by
        have := (Finset.mem_Ico.mp hi).1; omega))
    positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  have hlhs : p ^ (B + D) * B.factorial * D.factorial * (∏ j ∈ range D, Fblock p j) *
      (((B + D) * p).choose (B * p) * ∏ j ∈ range B, Fblock p j) =
      ((B + D) * p).choose (B * p) * (B * p).factorial * (D * p).factorial := by
    rw [factorial_mul_eq hp B, factorial_mul_eq hp D, pow_add]; ring
  have hrhs : p ^ (B + D) * B.factorial * D.factorial * (∏ j ∈ range D, Fblock p j) *
      ((B + D).choose B * ∏ j ∈ range B, Fblock p (D + j)) =
      ((B + D) * p).factorial := by
    rw [factorial_mul_eq hp (B + D), hprod_split, ← h2]; ring
  rw [hlhs, hrhs, h1]

/-- Main Kazandzidis F-product congruence:
`p^(3 + v_p(B) + v_p(D) + v_p(B+D)) ∣ ∏_{j<B} F(D+j) - ∏_{j<B} F(j)`. -/
lemma Fblock_prod_congr {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (B D : ℕ) (hB : 0 < B) (hD : 0 < D) :
    ((p : ℤ) ^ (3 + padicValNat p B + padicValNat p D + padicValNat p (B + D))) ∣
      ((∏ j ∈ range B, Fblock p (D + j) : ℕ) : ℤ) - ((∏ j ∈ range B, Fblock p j : ℕ) : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  set M := 3 + padicValNat p B + padicValNat p D + padicValNat p (B + D)
  set h := (p - 1) / 2
  have h2h : 2 * h + 1 = p := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    omega
  set P0 : ℕ := ∏ j ∈ range B, Fblock p j
  set P1 : ℕ := ∏ j ∈ range B, Fblock p (D + j)
  set F0 : ℕ := Fblock p 0
  have hF0_pos : 0 < F0 := Finset.prod_pos (fun i hi => by have := (Finset.mem_Ico.mp hi).1; omega)
  have hF0_cop : Nat.Coprime p F0 := Fblock_coprime hp 0
  have hP0_pos : 0 < P0 := Finset.prod_pos (fun j _ =>
    Finset.prod_pos (fun i hi => by have := (Finset.mem_Ico.mp hi).1; omega))
  have hP0_cop : Nat.Coprime p P0 := nat_coprime_prod_right (fun j _ => Fblock_coprime hp j)
  -- Express P1 / F0^B and P0 / F0^B as products of (1 + u_{j,i}) where p^2 ∣ u_{j,i}!
  have hF0_pair : (F0 : ℚ) = ∏ i ∈ Icc 1 h, ((i * (p - i) : ℕ) : ℚ) := by
    simpa [F0, h] using Fblock_pair hp hp5 0
  have hratio : ∀ m : ℕ, (Fblock p m : ℚ) / (F0 : ℚ) =
      ∏ i ∈ Icc 1 h, (1 + ((m * (m + 1) : ℕ) : ℚ) * (p : ℚ) ^ 2 / ((i * (p - i) : ℕ) : ℚ)) := by
    intro m
    rw [Fblock_pair hp hp5 m, hF0_pair, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hi' := Finset.mem_Icc.mp hi
    have hne : ((i * (p - i) : ℕ) : ℚ) ≠ 0 := by
      have : 0 < i * (p - i) := Nat.mul_pos (by omega) (by omega)
      positivity
    field_simp
  let u : ℕ → ℕ × ℕ → ℚ := fun shift ji =>
    (((shift + ji.1) * (shift + ji.1 + 1) : ℕ) : ℚ) * (p : ℚ) ^ 2 / ((ji.2 * (p - ji.2) : ℕ) : ℚ)
  let S_idx : Finset (ℕ × ℕ) := range B ×ˢ Icc 1 h
  have hu_p2 : ∀ shift, ∀ ji ∈ S_idx, pDvdRat p 2 (u shift ji) := by
    intro shift ji hji
    have hi' := Finset.mem_Icc.mp (Finset.mem_product.mp hji).2
    have hpos : 0 < ji.2 * (p - ji.2) := Nat.mul_pos (by omega) (by omega)
    have hcop : Nat.Coprime p (ji.2 * (p - ji.2)) :=
      ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).mul_right
        ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
    exact ⟨((shift + ji.1) * (shift + ji.1 + 1) : ℕ), ji.2 * (p - ji.2), hpos, hcop, by
      simp only [u]; push_cast; ring⟩
  have hP1_eq : (P1 : ℚ) / ((F0 : ℚ) ^ B) = ∏ ji ∈ S_idx, (1 + u D ji) := by
    simp only [P1, S_idx, Finset.prod_product, Nat.cast_prod]
    rw [show (F0 : ℚ) ^ B = ∏ _j ∈ range B, (F0 : ℚ) by simp, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun j _ => hratio (D + j))
  have hP0_eq : (P0 : ℚ) / ((F0 : ℚ) ^ B) = ∏ ji ∈ S_idx, (1 + u 0 ji) := by
    simp only [P0, S_idx, Finset.prod_product, Nat.cast_prod]
    rw [show (F0 : ℚ) ^ B = ∏ _j ∈ range B, (F0 : ℚ) by simp, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun j _ => by simpa [u] using hratio j)
  -- Apply truncLog_prod to both products!
  obtain ⟨hQ1_2, hQ1_log⟩ := truncLog_prod S_idx (M := M) hp hp5 (u D) (hu_p2 D)
  obtain ⟨hQ0_2, hQ0_log⟩ := truncLog_prod S_idx (M := M) hp hp5 (u 0) (hu_p2 0)
  -- Show ∑ truncLog M (u D ji) - ∑ truncLog M (u 0 ji) has pDvdRat p M!
  have hlog_diff : pDvdRat p M (∑ ji ∈ S_idx, truncLog M (u D ji) - ∑ ji ∈ S_idx, truncLog M (u 0 ji)) := by
    have hrew : (∑ ji ∈ S_idx, truncLog M (u D ji)) - (∑ ji ∈ S_idx, truncLog M (u 0 ji)) =
        ∑ k ∈ Icc 1 M, ((-1 : ℚ) ^ (k - 1) * (p : ℚ) ^ (2 * k) / (k : ℚ)) *
          (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ k) *
          (∑ j ∈ range B, (((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                            ((j : ℤ) * ((j : ℤ) + 1)) ^ k : ℤ) : ℚ)) := by
      simp only [truncLog, ← Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      conv_lhs => simp only [S_idx, Finset.sum_product, u, mul_pow, div_pow, ← pow_mul]
      have hcomm : ∑ j ∈ range B, ∑ i ∈ Icc 1 h,
          ((-1 : ℚ) ^ (k - 1) * ((((D + j) * (D + j + 1) : ℕ) : ℚ) ^ k * (p : ℚ) ^ (2 * k) /
            ((i * (p - i) : ℕ) : ℚ) ^ k) / (k : ℚ) -
           (-1 : ℚ) ^ (k - 1) * ((((0 + j) * (0 + j + 1) : ℕ) : ℚ) ^ k * (p : ℚ) ^ (2 * k) /
            ((i * (p - i) : ℕ) : ℚ) ^ k) / (k : ℚ)) =
          ∑ j ∈ range B, ((-1 : ℚ) ^ (k - 1) * (p : ℚ) ^ (2 * k) / (k : ℚ)) *
            (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ k) *
            (((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
              ((j : ℤ) * ((j : ℤ) + 1)) ^ k : ℤ) : ℚ) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        push_cast
        rw [inv_pow]
        ring
      rw [hcomm, ← Finset.mul_sum]
    rw [hrew]
    refine pDvdRat_sum (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hV : (p : ℤ) ^ (padicValNat p B + padicValNat p D + padicValNat p (B + D)) ∣
        ((B * D * (B + D) : ℕ) : ℤ) := by
      have h1 : p ^ padicValNat p B ∣ B := pow_padicValNat_dvd
      have h2 : p ^ padicValNat p D ∣ D := pow_padicValNat_dvd
      have h3 : p ^ padicValNat p (B + D) ∣ B + D := pow_padicValNat_dvd
      have hmul : p ^ (padicValNat p B + padicValNat p D + padicValNat p (B + D)) ∣ B * D * (B + D) := by
        rw [pow_add, pow_add]; exact mul_dvd_mul (mul_dvd_mul h1 h2) h3
      exact_mod_cast hmul
    have hSk_dvd : (p : ℤ) ^ (padicValNat p B + padicValNat p D + padicValNat p (B + D)) ∣
        ((2 * k + 1).factorial : ℤ) *
          ∑ j ∈ range B, ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                          ((j : ℤ) * ((j : ℤ) + 1)) ^ k) :=
      hV.trans (power_sum_dvd k B D)
    set V := padicValNat p B + padicValNat p D + padicValNat p (B + D)
    have hinv_sum_0 : pDvdRat p 0 (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ k) := by
      refine pDvdRat_sum (fun i hi => ?_)
      have hi' := Finset.mem_Icc.mp hi
      have hpos : 0 < i * (p - i) := Nat.mul_pos (by omega) (by omega)
      have hcop : Nat.Coprime p (i * (p - i)) :=
        ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).mul_right
          ((hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
      simpa using pDvdRat_pow (pDvdRat_inv_nat hpos hcop) k
    by_cases hk_eq1 : k = 1
    · subst hk_eq1
      have hinv1 := half_sum_inv_p_dvd hp hp5
      have hS1_eq : ∑ j ∈ range B, ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ 1 -
          ((j : ℤ) * ((j : ℤ) + 1)) ^ 1) = ((B * D * (B + D) : ℕ) : ℤ) := by
        have h1 : ∀ B' : ℕ, ∑ j ∈ range B', ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ 1 -
            ((j : ℤ) * ((j : ℤ) + 1)) ^ 1) = ((B' * D * (B' + D) : ℕ) : ℤ) := by
          intro B'
          induction B' with
          | zero => simp
          | succ B' ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
        exact h1 B
      have hS1_p : pDvdRat p V (∑ j ∈ range B, (((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ 1 -
          ((j : ℤ) * ((j : ℤ) + 1)) ^ 1 : ℤ) : ℚ)) := by
        rw [← Int.cast_sum, hS1_eq]
        exact pDvdRat_of_int _ hV
      have hp2 : pDvdRat p 2 ((-1 : ℚ) ^ (1 - 1) * (p : ℚ) ^ (2 * 1) / ((1 : ℕ) : ℚ)) := by
        refine ⟨1, 1, Nat.one_pos, Nat.coprime_one_right p, ?_⟩; norm_num
      have hinv1' : pDvdRat p 1 (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ 1) := by
        simpa only [pow_one] using hinv1
      have hprod := pDvdRat_mul (pDvdRat_mul hp2 hinv1') hS1_p
      exact pDvdRat_mono (by omega : M ≤ 2 + 1 + V) hprod
    · have hk2 : 2 ≤ k := by omega
      have hSk_q : pDvdRat p V ((((2 * k + 1).factorial : ℤ) *
          ∑ j ∈ range B, ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                          ((j : ℤ) * ((j : ℤ) + 1)) ^ k) : ℤ) : ℚ) :=
        pDvdRat_of_int _ hSk_dvd
      have hp2k : pDvdRat p (2 * k) ((-1 : ℚ) ^ (k - 1) * (p : ℚ) ^ (2 * k)) := by
        refine ⟨(-1 : ℤ) ^ (k - 1), 1, Nat.one_pos, Nat.coprime_one_right p, ?_⟩
        push_cast; ring
      have hnum := pDvdRat_mul (pDvdRat_mul hp2k hinv_sum_0) hSk_q
      have hvp_k : 4 * padicValNat p k ≤ k - 1 := four_mul_padicValNat_le hp hp5 hk1
      have hvp_fac : 4 * padicValNat p (2 * k + 1).factorial ≤ 2 * k + 1 :=
        four_mul_padicValNat_factorial_le hp hp5
      have hvp_prod : padicValNat p (k * (2 * k + 1).factorial) =
          padicValNat p k + padicValNat p (2 * k + 1).factorial :=
        padicValNat.mul (by omega) (Nat.factorial_ne_zero _)
      have hbound : 3 + padicValNat p (k * (2 * k + 1).factorial) ≤ 2 * k := by omega
      have hdiv := pDvdRat_div_nat hp (Nat.mul_pos (by omega) (Nat.factorial_pos _))
        le_rfl (by omega : padicValNat p (k * (2 * k + 1).factorial) ≤ 2 * k + 0 + V) hnum
      have hrew_k : ((-1 : ℚ) ^ (k - 1) * (p : ℚ) ^ (2 * k) / (k : ℚ)) *
          (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ k) *
          (∑ j ∈ range B, (((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                            ((j : ℤ) * ((j : ℤ) + 1)) ^ k : ℤ) : ℚ)) =
          ((-1 : ℚ) ^ (k - 1) * (p : ℚ) ^ (2 * k) *
            (∑ i ∈ Icc 1 h, (((i * (p - i) : ℕ) : ℚ)⁻¹) ^ k) *
            ((((2 * k + 1).factorial : ℤ) *
              ∑ j ∈ range B, ((((D : ℤ) + (j : ℤ)) * ((D : ℤ) + (j : ℤ) + 1)) ^ k -
                              ((j : ℤ) * ((j : ℤ) + 1)) ^ k) : ℤ) : ℚ)) /
            ((k * (2 * k + 1).factorial : ℕ) : ℚ) := by
        rw [← Int.cast_sum]
        have hfacne : ((2 * k + 1).factorial : ℚ) ≠ 0 := by positivity
        have hkne : (k : ℚ) ≠ 0 := by positivity
        push_cast
        field_simp
      rw [hrew_k]
      exact pDvdRat_mono (by omega : M ≤ 2 * k + 0 + V - padicValNat p (k * (2 * k + 1).factorial)) hdiv
  -- Combine: truncLog M (P1/F0^B - 1) - truncLog M (P0/F0^B - 1) has pDvdRat p M!
  set q1 : ℚ := (P1 : ℚ) / ((F0 : ℚ) ^ B) - 1
  set q0 : ℚ := (P0 : ℚ) / ((F0 : ℚ) ^ B) - 1
  rw [← hP1_eq] at hQ1_2 hQ1_log
  rw [← hP0_eq] at hQ0_2 hQ0_log
  have hlog_q : pDvdRat p M (truncLog M q1 - truncLog M q0) := by
    have h1 := pDvdRat_add (pDvdRat_sub hQ1_log hQ0_log) hlog_diff
    convert h1 using 1
    ring
  -- Define w = (P1 - P0) / P0 so 1 + q1 = (1 + q0) * (1 + w)
  set w : ℚ := ((P1 : ℚ) - (P0 : ℚ)) / (P0 : ℚ)
  have h1q1 : 1 + q1 = (1 + q0) * (1 + w) := by
    have hP0ne : (P0 : ℚ) ≠ 0 := by positivity
    have hF0ne : (F0 : ℚ) ^ B ≠ 0 := pow_ne_zero B (by positivity)
    simp only [q1, q0, w]; field_simp; ring
  have hq1_eq : q1 = q0 + w + q0 * w := by linarith
  have hw2 : pDvdRat p 2 w := by
    have hq10 : pDvdRat p 2 (q1 - q0) := pDvdRat_sub hQ1_2 hQ0_2
    have hF0B : pDvdRat p 0 (((F0 : ℚ) ^ B) / (P0 : ℚ)) := by
      refine ⟨(F0 : ℤ) ^ B, P0, hP0_pos, hP0_cop, ?_⟩; push_cast; ring
    have hw_eq : w = (q1 - q0) * (((F0 : ℚ) ^ B) / (P0 : ℚ)) := by
      have hP0ne : (P0 : ℚ) ≠ 0 := by positivity
      have hF0ne : (F0 : ℚ) ^ B ≠ 0 := pow_ne_zero B (by positivity)
      simp only [q1, q0, w]; field_simp; ring
    rw [hw_eq]
    simpa using pDvdRat_mul hq10 hF0B
  have hmul_log := truncLog_mul (M := M) hp hp5 hQ0_2 hw2
  rw [← hq1_eq] at hmul_log
  have hlog_w : pDvdRat p M (truncLog M w) := by
    have h := pDvdRat_sub hlog_q hmul_log
    convert h using 1
    ring
  have hwM : pDvdRat p M w := truncLog_inj hp hp5 hw2 hlog_w
  -- Multiply by P0 to get pDvdRat p M ((P1 - P0 : ℤ) : ℚ)!
  have hdiff_q : pDvdRat p M ((((P1 : ℤ) - (P0 : ℤ) : ℤ) : ℚ)) := by
    have hP0_0 : pDvdRat p 0 (P0 : ℚ) := pDvdRat_of_int_zero p (P0 : ℤ)
    have hmul := pDvdRat_mul hwM hP0_0
    have hP0ne : (P0 : ℚ) ≠ 0 := by positivity
    have heq : w * (P0 : ℚ) = (((P1 : ℤ) - (P0 : ℤ) : ℤ) : ℚ) := by
      simp only [w]; push_cast; field_simp
    rw [heq] at hmul
    simpa using hmul
  exact int_dvd_of_pDvdRat hdiff_q

/-- Kazandzidis congruence with extra `p`-adic factor from `C(B+D, B)`:
`p^(3 + v_p(B) + v_p(D) + v_p(B+D) + v_p(C(B+D, B))) ∣ C((B+D)p, Bp) - C(B+D, B)` (in `ℤ`). -/
lemma kazandzidis_pow {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (B D : ℕ) (hB : 0 < B) (hD : 0 < D) :
    ((p : ℤ) ^ (3 + padicValNat p B + padicValNat p D + padicValNat p (B + D) +
        padicValNat p ((B + D).choose B))) ∣
      (((B + D) * p).choose (B * p) : ℤ) - ((B + D).choose B : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  set E := 3 + padicValNat p B + padicValNat p D + padicValNat p (B + D)
  set V := padicValNat p ((B + D).choose B)
  set P0 : ℕ := ∏ j ∈ range B, Fblock p j
  set P1 : ℕ := ∏ j ∈ range B, Fblock p (D + j)
  have hrel : (((B + D) * p).choose (B * p) : ℤ) * (P0 : ℤ) = ((B + D).choose B : ℤ) * (P1 : ℤ) := by
    exact_mod_cast choose_mul_Fblock hp.pos B D
  have hsub : ((((B + D) * p).choose (B * p) : ℤ) - ((B + D).choose B : ℤ)) * (P0 : ℤ) =
      ((B + D).choose B : ℤ) * ((P1 : ℤ) - (P0 : ℤ)) := by linarith
  have hP0_cop : Nat.Coprime p P0 := nat_coprime_prod_right (fun j _ => Fblock_coprime hp j)
  have hd1 : (p : ℤ) ^ E ∣ (P1 : ℤ) - (P0 : ℤ) := Fblock_prod_congr hp hp5 B D hB hD
  have hd2 : (p : ℤ) ^ V ∣ ((B + D).choose B : ℤ) := by
    exact_mod_cast pow_padicValNat_dvd (p := p) (n := (B + D).choose B)
  have hmul : (p : ℤ) ^ (E + V) ∣ (P0 : ℤ) * ((((B + D) * p).choose (B * p) : ℤ) - ((B + D).choose B : ℤ)) := by
    rw [mul_comm, hsub, pow_add, mul_comm ((p : ℤ) ^ E)]
    exact mul_dvd_mul hd2 hd1
  have hcopZ : IsCoprime ((p : ℤ) ^ (E + V)) (P0 : ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr hP0_cop).pow_left
  exact hcopZ.dvd_of_dvd_mul_left hmul

/-- Part 3 helper: `p^(v_p(A) - v_p(B)) ∣ C(A, B)` whenever `0 < B ≤ A` and `v_p(B) ≤ v_p(A)`. -/
lemma padicValNat_choose_ge {p A B : ℕ} (hp : p.Prime) (hB : 0 < B) (hBA : B ≤ A) :
    padicValNat p A - padicValNat p B ≤ padicValNat p (A.choose B) := by
  have : Fact p.Prime := ⟨hp⟩
  have hA : 0 < A := lt_of_lt_of_le hB hBA
  have hch_pos : 0 < A.choose B := Nat.choose_pos hBA
  have hmul : B * A.choose B = A * (A - 1).choose (B - 1) := by
    have := Nat.add_one_mul_choose_eq (A - 1) (B - 1)
    rw [Nat.sub_add_cancel hA, Nat.sub_add_cancel hB] at this
    linarith
  have hv := congrArg (padicValNat p) hmul
  have hprev_pos : 0 < (A - 1).choose (B - 1) := Nat.choose_pos (by omega)
  rw [padicValNat.mul (by omega) (by omega), padicValNat.mul (by omega) (by omega)] at hv
  omega

/-- Part 3: Term-by-term supercongruence on `p`-divisible indices:
`S(n * p^r, p * j) ≡ S(n * p^(r-1), j) [ZMOD p^(3*r)]`. -/
lemma div_term_congr {p n r j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hj : j ≤ n * p ^ (r - 1)) :
    let N := n * p ^ r
    let M := n * p ^ (r - 1)
    ((p : ℤ) ^ (3 * r)) ∣
      ((N.choose (p * j) * (2 * N).choose (N + p * j) * (2 * N + 2 * (p * j)).choose (2 * (p * j)) : ℕ) : ℤ) -
      ((M.choose j * (2 * M).choose (M + j) * (2 * M + 2 * j).choose (2 * j) : ℕ) : ℤ) := by
  have : Fact p.Prime := ⟨hp⟩
  intro N M
  have hNM : N = M * p := by
    simp only [N, M, mul_assoc, ← pow_succ]
    congr 2; omega
  have hM_pos : 0 < M := Nat.mul_pos (by omega) (pow_pos hp.pos _)
  have hvp_M : r - 1 ≤ padicValNat p M := by
    refine (padicValNat_dvd_iff_le (by omega)).mp (dvd_mul_left _ _)
  have hvp_2 : padicValNat p 2 = 0 := by
    refine padicValNat.eq_zero_of_not_dvd (fun h => by have := Nat.le_of_dvd (by decide) h; omega)
  have hvp_2M : padicValNat p (2 * M) = padicValNat p M := by
    rw [padicValNat.mul (by decide) (by omega), hvp_2, zero_add]
  by_cases hj0 : j = 0
  · subst hj0
    simp only [Nat.mul_zero, Nat.choose_zero_right, Nat.add_zero, Nat.one_mul, Nat.mul_one]
    have hkaz := kazandzidis_pow hp hp5 M M hM_pos hM_pos
    have h2N : (M + M) * p = 2 * N := by rw [hNM]; ring
    have hMp : M * p = N := hNM.symm
    have h2M : M + M = 2 * M := by ring
    rw [h2N, hMp, h2M] at hkaz
    have hexp : 3 * r ≤ 3 + padicValNat p M + padicValNat p M + padicValNat p (2 * M) +
        padicValNat p ((2 * M).choose M) := by omega
    exact (pow_dvd_pow (p : ℤ) hexp).trans hkaz
  · by_cases hjM : j = M
    · subst hjM
      have hpM : p * M = N := by rw [hNM, mul_comm]
      rw [hpM]
      simp only [Nat.choose_self, Nat.one_mul]
      have h2N_eq : N + N = 2 * N := by ring
      have h2M_eq : M + M = 2 * M := by ring
      rw [h2N_eq, h2M_eq, Nat.choose_self, Nat.choose_self, Nat.one_mul, Nat.one_mul]
      have hkaz := kazandzidis_pow hp hp5 (2 * M) (2 * M) (by omega) (by omega)
      have h4N : (2 * M + 2 * M) * p = 2 * N + 2 * N := by rw [hNM]; ring
      have h2Mp : (2 * M) * p = 2 * N := by rw [hNM]; ring
      have h4M : 2 * M + 2 * M = 2 * M + 2 * M := rfl
      rw [h4N, h2Mp] at hkaz
      have hexp : 3 * r ≤ 3 + padicValNat p (2 * M) + padicValNat p (2 * M) +
          padicValNat p (2 * M + 2 * M) + padicValNat p ((2 * M + 2 * M).choose (2 * M)) := by
        have hvp4 : r - 1 ≤ padicValNat p (2 * M + 2 * M) := by
          rw [show 2 * M + 2 * M = 4 * M by ring]
          exact (padicValNat_dvd_iff_le (by omega)).mp (dvd_mul_of_dvd_right (dvd_mul_left _ _) 4)
        omega
      exact (pow_dvd_pow (p : ℤ) hexp).trans hkaz
    · have hj_pos : 0 < j := by omega
      have hj_lt : j < M := by omega
      set s := padicValNat p j
      -- Compute Kazandzidis bounds for all 3 factors:
      -- Factor 1: C(N, p*j) vs C(M, j), with B = j, D = M - j, B + D = M
      have hkaz1 := kazandzidis_pow hp hp5 j (M - j) hj_pos (by omega)
      have h1a : j + (M - j) = M := Nat.add_sub_cancel' hj
      have h1b : (j + (M - j)) * p = N := by rw [h1a, ← hNM]
      have h1c : j * p = p * j := Nat.mul_comm j p
      rw [h1b, h1c, h1a] at hkaz1
      -- Factor 2: C(2*N, N + p*j) vs C(2*M, M + j), with B = M + j, D = M - j, B + D = 2*M
      have hkaz2 := kazandzidis_pow hp hp5 (M + j) (M - j) (by omega) (by omega)
      have h2a : (M + j) + (M - j) = 2 * M := by omega
      have h2b : ((M + j) + (M - j)) * p = 2 * N := by rw [h2a, hNM]; ring
      have h2c : (M + j) * p = N + p * j := by rw [hNM]; ring
      rw [h2b, h2c, h2a] at hkaz2
      -- Factor 3: C(2*N + 2*(p*j), 2*(p*j)) vs C(2*M + 2*j, 2*j), with B = 2*j, D = 2*M, B + D = 2*M + 2*j
      have hkaz3 := kazandzidis_pow hp hp5 (2 * j) (2 * M) (by omega) (by omega)
      have h3a : (2 * j) + (2 * M) = 2 * M + 2 * j := by ring
      have h3b : ((2 * j) + (2 * M)) * p = 2 * N + 2 * (p * j) := by rw [hNM]; ring
      have h3c : (2 * j) * p = 2 * (p * j) := by ring
      rw [h3b, h3c, h3a] at hkaz3
      -- Now split on whether r - 1 ≤ s or s < r - 1!
      -- Notice: in BOTH cases, let D_ext = (r - 1) - s (which is 0 if r - 1 ≤ s!).
      -- Check: padicValNat p (M - j) ≥ min (r - 1) s, padicValNat p (M + j) ≥ min (r - 1) s, etc.!
      set t := min (r - 1) s
      have ht_dvd_j : p ^ t ∣ j := (pow_dvd_pow p (min_le_right _ _)).trans pow_padicValNat_dvd
      have ht_dvd_M : p ^ t ∣ M := (pow_dvd_pow p (min_le_left _ _)).trans (dvd_mul_left _ _)
      have hvp_Mj : t ≤ padicValNat p (M - j) :=
        (padicValNat_dvd_iff_le (by omega)).mp (Nat.dvd_sub ht_dvd_M ht_dvd_j)
      have hvp_Mpj : t ≤ padicValNat p (M + j) :=
        (padicValNat_dvd_iff_le (by omega)).mp (Nat.dvd_add ht_dvd_M ht_dvd_j)
      have hvp_2j : t ≤ padicValNat p (2 * j) :=
        (padicValNat_dvd_iff_le (by omega)).mp (dvd_mul_of_dvd_right ht_dvd_j 2)
      have hvp_2M2j : t ≤ padicValNat p (2 * M + 2 * j) :=
        (padicValNat_dvd_iff_le (by omega)).mp (Nat.dvd_add (dvd_mul_of_dvd_right ht_dvd_M 2) (dvd_mul_of_dvd_right ht_dvd_j 2))
      have hvp_j_ge : t ≤ padicValNat p j := min_le_right _ _
      -- Extra valuation of C(M, j) and C(2*M, M + j):
      have hD_c1 : (r - 1) - t ≤ padicValNat p (M.choose j) := by
        by_cases hst : s < r - 1
        · have ht_eq : t = s := min_eq_right (le_of_lt hst)
          rw [ht_eq]
          have h1 : padicValNat p M - padicValNat p j ≤ padicValNat p (M.choose j) :=
            padicValNat_choose_ge hp hj_pos hj
          omega
        · have : (r - 1) - t = 0 := by omega
          omega
      have hD_c2 : (r - 1) - t ≤ padicValNat p ((2 * M).choose (M + j)) := by
        by_cases hst : s < r - 1
        · have ht_eq : t = s := min_eq_right (le_of_lt hst)
          rw [ht_eq]
          have hsym : (2 * M).choose (M + j) = (2 * M).choose (M - j) := by
            rw [← Nat.choose_symm (show M - j ≤ 2 * M by omega)]
            congr 1; omega
          rw [hsym]
          have h1 := padicValNat_choose_ge hp (by omega : 0 < M - j) (by omega : M - j ≤ 2 * M)
          have hvp_Mj_eq : padicValNat p (M - j) = s := by
            apply Nat.le_antisymm
            · by_contra hgt
              have hge : s + 1 ≤ padicValNat p (M - j) := by omega
              have hd1 : p ^ (s + 1) ∣ M - j := (padicValNat_dvd_iff_le (by omega)).mpr hge
              have hd2 : p ^ (s + 1) ∣ M := (pow_dvd_pow p (by omega : s + 1 ≤ r - 1)).trans (dvd_mul_left _ _)
              have hdj : p ^ (s + 1) ∣ j := by
                have hadd : (M - j) + j = M := Nat.sub_add_cancel hj
                exact (Nat.dvd_add_right hd1).mp (hadd.symm ▸ hd2)
              have hle := (padicValNat_dvd_iff_le (by omega)).mp hdj
              omega
            · exact ht_eq ▸ hvp_Mj
          rw [hvp_2M, hvp_Mj_eq] at h1
          omega
        · have : (r - 1) - t = 0 := by omega
          omega
      set D := (r - 1) - t
      set E := r + 2 * t + 2
      have hE1 : E + D ≤ 3 + padicValNat p j + padicValNat p (M - j) + padicValNat p M +
          padicValNat p (M.choose j) := by omega
      have hE2 : E + D ≤ 3 + padicValNat p (M + j) + padicValNat p (M - j) + padicValNat p (2 * M) +
          padicValNat p ((2 * M).choose (M + j)) := by omega
      have hE3 : E ≤ 3 + padicValNat p (2 * j) + padicValNat p (2 * M) + padicValNat p (2 * M + 2 * j) +
          padicValNat p ((2 * M + 2 * j).choose (2 * j)) := by omega
      have hd1 : (p : ℤ) ^ (E + D) ∣ (N.choose (p * j) : ℤ) - (M.choose j : ℤ) :=
        (pow_dvd_pow (p : ℤ) hE1).trans hkaz1
      have hd2 : (p : ℤ) ^ (E + D) ∣ ((2 * N).choose (N + p * j) : ℤ) - ((2 * M).choose (M + j) : ℤ) :=
        (pow_dvd_pow (p : ℤ) hE2).trans hkaz2
      have hd3 : (p : ℤ) ^ E ∣ ((2 * N + 2 * (p * j)).choose (2 * (p * j)) : ℤ) - ((2 * M + 2 * j).choose (2 * j) : ℤ) :=
        (pow_dvd_pow (p : ℤ) hE3).trans hkaz3
      have ha_dvd : (p : ℤ) ^ D ∣ (M.choose j : ℤ) := by
        exact_mod_cast (pow_dvd_pow p hD_c1).trans (pow_padicValNat_dvd (p := p) (n := M.choose j))
      have hb_dvd : (p : ℤ) ^ D ∣ ((2 * M).choose (M + j) : ℤ) := by
        exact_mod_cast (pow_dvd_pow p hD_c2).trans (pow_padicValNat_dvd (p := p) (n := (2 * M).choose (M + j)))
      have hb'_dvd : (p : ℤ) ^ D ∣ ((2 * N).choose (N + p * j) : ℤ) := by
        have h1 : (p : ℤ) ^ D ∣ ((2 * N).choose (N + p * j) : ℤ) - ((2 * M).choose (M + j) : ℤ) :=
          (pow_dvd_pow (p : ℤ) (by omega : D ≤ E + D)).trans hd2
        have h2 := dvd_add h1 hb_dvd
        simpa using h2
      -- Combine: a'*b'*c' - a*b*c = (a' - a)*b'*c' + a*(b' - b)*c' + a*b*(c' - c)!
      set a' : ℤ := (N.choose (p * j) : ℤ)
      set b' : ℤ := ((2 * N).choose (N + p * j) : ℤ)
      set c' : ℤ := ((2 * N + 2 * (p * j)).choose (2 * (p * j)) : ℤ)
      set a0 : ℤ := (M.choose j : ℤ)
      set b0 : ℤ := ((2 * M).choose (M + j) : ℤ)
      set c0 : ℤ := ((2 * M + 2 * j).choose (2 * j) : ℤ)
      have hid : a' * b' * c' - a0 * b0 * c0 =
          (a' - a0) * b' * c' + a0 * (b' - b0) * c' + a0 * b0 * (c' - c0) := by ring
      have h3r : 3 * r ≤ E + 2 * D := by omega
      have hterm1 : (p : ℤ) ^ (E + 2 * D) ∣ (a' - a0) * b' * c' := by
        rw [show E + 2 * D = (E + D) + D by omega, pow_add]
        exact dvd_mul_of_dvd_left (mul_dvd_mul hd1 hb'_dvd) c'
      have hterm2 : (p : ℤ) ^ (E + 2 * D) ∣ a0 * (b' - b0) * c' := by
        rw [show E + 2 * D = D + (E + D) by omega, pow_add]
        exact dvd_mul_of_dvd_left (mul_dvd_mul ha_dvd hd2) c'
      have hterm3 : (p : ℤ) ^ (E + 2 * D) ∣ a0 * b0 * (c' - c0) := by
        rw [show E + 2 * D = (D + D) + E by omega, pow_add, pow_add]
        exact mul_dvd_mul (mul_dvd_mul ha_dvd hb_dvd) hd3
      have htot : (p : ℤ) ^ (E + 2 * D) ∣ a' * b' * c' - a0 * b0 * c0 := by
        rw [hid]; exact dvd_add (dvd_add hterm1 hterm2) hterm3
      have hcast : ((N.choose (p * j) * (2 * N).choose (N + p * j) * (2 * N + 2 * (p * j)).choose (2 * (p * j)) : ℕ) : ℤ) -
          ((M.choose j * (2 * M).choose (M + j) * (2 * M + 2 * j).choose (2 * j) : ℕ) : ℤ) =
          a' * b' * c' - a0 * b0 * c0 := by simp [a', b', c', a0, b0, c0]
      rw [hcast]
      exact (pow_dvd_pow (p : ℤ) h3r).trans htot

end OeisA363986Part23


namespace OeisA363986Part4
open Finset

lemma zmod_unit_inv_eq {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) :
    ((u : ZMod q))⁻¹ = ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  have h : (u : ZMod q) * ((u : ZMod q))⁻¹ = 1 := ZMod.mul_inv_of_unit _ u.isUnit
  calc ((u : ZMod q))⁻¹ = 1 * ((u : ZMod q))⁻¹ := (one_mul _).symm
    _ = (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * (u : ZMod q)) * ((u : ZMod q))⁻¹ := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    _ = ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u : ZMod q) * ((u : ZMod q))⁻¹) := by rw [mul_assoc]
    _ = ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := by rw [h, mul_one]

/-- Half-block reciprocal square sum vanishes mod `p^k` for `p ≥ 5` prime and `k ≥ 1`. -/
lemma sum_units_inv_sq_eq_zero {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    letI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
    ∑ x : (ZMod (p ^ k))ˣ, ((x : ZMod (p ^ k)) ^ 2)⁻¹ = 0 := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  have hcop2 : Nat.Coprime 2 (p ^ k) :=
    ((hp.coprime_iff_not_dvd).mpr (fun h => by have := Nat.le_of_dvd (by decide) h; omega)).symm.pow_right k
  have hcop3 : Nat.Coprime 3 (p ^ k) :=
    ((hp.coprime_iff_not_dvd).mpr (fun h => by have := Nat.le_of_dvd (by decide) h; omega)).symm.pow_right k
  let u2 : (ZMod (p ^ k))ˣ := ZMod.unitOfCoprime 2 hcop2
  let u3 : (ZMod (p ^ k))ˣ := ZMod.unitOfCoprime 3 hcop3
  set S : ZMod (p ^ k) := ∑ x : (ZMod (p ^ k))ˣ, ((x : ZMod (p ^ k)) ^ 2)⁻¹
  have hshift : ((u2 : ZMod (p ^ k)) ^ 2) * S = S := by
    rw [Finset.mul_sum]
    have hbij : ∑ x : (ZMod (p ^ k))ˣ, ((u2 : ZMod (p ^ k)) ^ 2) * ((x : ZMod (p ^ k)) ^ 2)⁻¹ =
        ∑ x : (ZMod (p ^ k))ˣ, (((u2⁻¹ * x : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) ^ 2)⁻¹ := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have hx : ((x : ZMod (p ^ k)) ^ 2)⁻¹ = (((x ^ 2)⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) := by
        rw [← Units.val_pow_eq_pow_val]; exact zmod_unit_inv_eq (x ^ 2)
      have hux : (((u2⁻¹ * x : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) ^ 2)⁻¹ =
          ((((u2⁻¹ * x) ^ 2)⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) := by
        rw [← Units.val_pow_eq_pow_val]; exact zmod_unit_inv_eq ((u2⁻¹ * x) ^ 2)
      rw [hx, hux]
      have heq : (u2 ^ 2 * (x ^ 2)⁻¹ : (ZMod (p ^ k))ˣ) = ((u2⁻¹ * x) ^ 2)⁻¹ := by
        rw [mul_pow, mul_inv, inv_pow, inv_inv, mul_comm]
      have hval := congrArg Units.val heq
      rw [Units.val_mul, Units.val_pow_eq_pow_val] at hval
      exact hval
    rw [hbij]
    exact Fintype.sum_equiv (Equiv.mulLeft u2⁻¹) _ _ (fun _ => rfl)
  have h3 : ((u2 : ZMod (p ^ k)) ^ 2 - 1) = (u3 : ZMod (p ^ k)) := by
    simp only [u2, u3, ZMod.coe_unitOfCoprime]
    norm_num
  have hzero : (u3 : ZMod (p ^ k)) * S = 0 := by
    rw [← h3, sub_mul, one_mul, hshift, sub_self]
  calc S = ((u3⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * ((u3 : ZMod (p ^ k)) * S) := by
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    _ = 0 := by rw [hzero, mul_zero]

/-- For `p ≥ 5` prime and `k ≥ 1`, the half-block sum of `s^{-2}` over `1 ≤ s < p^k / 2` with `p ∤ s`
is `0` in `ZMod (p^k)`. -/
lemma half_block_inv_sq_zero {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 1 ≤ k) :
    ∑ s ∈ (Ico 1 ((p ^ k + 1) / 2)).filter (fun s => ¬ p ∣ s), ((s : ZMod (p ^ k)) ^ 2)⁻¹ = 0 ∧
    ∑ s ∈ (Ico ((p ^ k + 1) / 2) (p ^ k)).filter (fun s => ¬ p ∣ s), ((s : ZMod (p ^ k)) ^ 2)⁻¹ = 0 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  have hodd : p ^ k % 2 = 1 := by
    have hp2 : p % 2 = 1 := hp.odd_of_ne_two (by omega) |> Nat.odd_iff.mp
    have hpow : Odd (p ^ k) := (Nat.odd_iff.mpr hp2).pow
    exact Nat.odd_iff.mp hpow
  set h := (p ^ k + 1) / 2
  have h2h : 2 * h = p ^ k + 1 := by omega
  have hS1_eq_S2 :
      ∑ s ∈ (Ico 1 h).filter (fun s => ¬ p ∣ s), ((s : ZMod (p ^ k)) ^ 2)⁻¹ =
      ∑ s ∈ (Ico h (p ^ k)).filter (fun s => ¬ p ∣ s), ((s : ZMod (p ^ k)) ^ 2)⁻¹ := by
    refine Finset.sum_bij (fun s _ => p ^ k - s) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_Ico] at hs ⊢
      refine ⟨⟨by omega, by omega⟩, fun hdvd => hs.2 ?_⟩
      have hp_dvd_pk : p ∣ p ^ k := dvd_pow_self p (by omega)
      have hadd : (p ^ k - s) + s = p ^ k := Nat.sub_add_cancel (by omega)
      exact (Nat.dvd_add_right hdvd).mp (hadd.symm ▸ hp_dvd_pk)
    · intro s1 hs1 s2 hs2 heq
      simp only [Finset.mem_filter, Finset.mem_Ico] at hs1 hs2
      omega
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_Ico] at ht
      refine ⟨p ^ k - t, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, fun hdvd => ht.2 ?_⟩, by omega⟩
      have hp_dvd_pk : p ∣ p ^ k := dvd_pow_self p (by omega)
      have hadd : (p ^ k - t) + t = p ^ k := Nat.sub_add_cancel (by omega)
      exact (Nat.dvd_add_right hdvd).mp (hadd.symm ▸ hp_dvd_pk)
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_Ico] at hs
      have hcast : ((p ^ k - s : ℕ) : ZMod (p ^ k)) = -(s : ZMod (p ^ k)) := by
        have h1 : ((p ^ k - s : ℕ) : ZMod (p ^ k)) + (s : ZMod (p ^ k)) = ((p ^ k : ℕ) : ZMod (p ^ k)) := by
          rw [← Nat.cast_add, Nat.sub_add_cancel (by omega : s ≤ p ^ k)]
        rw [ZMod.natCast_self] at h1
        exact eq_neg_of_add_eq_zero_left h1
      rw [hcast, neg_sq]
  have hsum_all :
      (∑ s ∈ (Ico 1 h).filter (fun s => ¬ p ∣ s), ((s : ZMod (p ^ k)) ^ 2)⁻¹) +
      (∑ s ∈ (Ico h (p ^ k)).filter (fun s => ¬ p ∣ s), ((s : ZMod (p ^ k)) ^ 2)⁻¹) =
      ∑ x : (ZMod (p ^ k))ˣ, ((x : ZMod (p ^ k)) ^ 2)⁻¹ := by
    rw [← Finset.sum_union]
    · have hunion : (Ico 1 h).filter (fun s => ¬ p ∣ s) ∪ (Ico h (p ^ k)).filter (fun s => ¬ p ∣ s) =
          (Ico 1 (p ^ k)).filter (fun s => ¬ p ∣ s) := by
        ext s; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]; omega
      rw [hunion]
      refine Finset.sum_bij (fun s hs =>
          ZMod.unitOfCoprime s (by
            have hnd : ¬ p ∣ s := (Finset.mem_filter.mp hs).2
            exact ((hp.coprime_iff_not_dvd).mpr hnd).symm.pow_right k)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro s1 hs1 s2 hs2 heq
        have h1 : (s1 : ZMod (p ^ k)) = (s2 : ZMod (p ^ k)) := by
          have := congrArg Units.val heq
          simpa [ZMod.coe_unitOfCoprime] using this
        have hlt1 : s1 < p ^ k := (Finset.mem_Ico.mp (Finset.mem_filter.mp hs1).1).2
        have hlt2 : s2 < p ^ k := (Finset.mem_Ico.mp (Finset.mem_filter.mp hs2).1).2
        have hv := congrArg ZMod.val h1
        rwa [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hlt2] at hv
      · intro u _
        have hval_lt : (u : ZMod (p ^ k)).val < p ^ k := ZMod.val_lt _
        have hcop : Nat.Coprime (u : ZMod (p ^ k)).val (p ^ k) := by
          rw [← ZMod.isUnit_iff_coprime]
          simpa [ZMod.natCast_zmod_val] using u.isUnit
        have hnd : ¬ p ∣ (u : ZMod (p ^ k)).val := by
          intro hd
          have h1 : p ∣ Nat.gcd (u : ZMod (p ^ k)).val (p ^ k) :=
            Nat.dvd_gcd hd (dvd_pow_self p (by omega))
          rw [hcop.gcd_eq_one] at h1
          exact hp.not_dvd_one h1
        have hpos : 1 ≤ (u : ZMod (p ^ k)).val := by
          rcases Nat.eq_zero_or_pos (u : ZMod (p ^ k)).val with h0 | hp'
          · exact absurd (h0 ▸ dvd_zero p) hnd
          · exact hp'
        refine ⟨(u : ZMod (p ^ k)).val, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hpos, hval_lt⟩, hnd⟩, ?_⟩
        ext
        simp [ZMod.coe_unitOfCoprime]
      · intro s _; simp [ZMod.coe_unitOfCoprime]
    · rw [Finset.disjoint_left]
      intro s hs1 hs2
      simp only [Finset.mem_filter, Finset.mem_Ico] at hs1 hs2
      omega
  rw [sum_units_inv_sq_eq_zero hp hp5 hk, ← hS1_eq_S2, ← two_mul] at hsum_all
  have hcop2 : Nat.Coprime 2 (p ^ k) :=
    ((hp.coprime_iff_not_dvd).mpr (fun h => by have := Nat.le_of_dvd (by decide) h; omega)).symm.pow_right k
  let u2 : (ZMod (p ^ k))ˣ := ZMod.unitOfCoprime 2 hcop2
  have h1 : ∑ s ∈ (Ico 1 h).filter (fun s => ¬ p ∣ s), ((s : ZMod (p ^ k)) ^ 2)⁻¹ = 0 := by
    have hmul : (u2 : ZMod (p ^ k)) * ∑ s ∈ (Ico 1 h).filter (fun s => ¬ p ∣ s), ((s : ZMod (p ^ k)) ^ 2)⁻¹ = 0 := by
      simpa [u2, ZMod.coe_unitOfCoprime] using hsum_all
    calc _ = ((u2⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) *
            ((u2 : ZMod (p ^ k)) * ∑ s ∈ (Ico 1 h).filter (fun s => ¬ p ∣ s), ((s : ZMod (p ^ k)) ^ 2)⁻¹) := by
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      _ = 0 := by rw [hmul, mul_zero]
  exact ⟨h1, hS1_eq_S2 ▸ h1⟩

/-- Telescoping cancellation lemma in `ZMod (p^r)`. -/
lemma telescope_block_sum {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (f h : ℕ → ZMod (p ^ r))
    (hh : ∀ k, 1 ≤ k → k ≤ r → ∀ b < 2 * p ^ (r - k),
      ((p : ZMod (p ^ r)) ^ k) ∣ ∑ w ∈ Ico (b * p ^ (k - 1)) ((b + 1) * p ^ (k - 1)), h w)
    (hf : ∀ k, 1 ≤ k → k < r → ∀ w < 2 * p ^ (r - 1),
      ((p : ZMod (p ^ r)) ^ (r - k)) ∣ f w - f ((w / p ^ k) * p ^ k)) :
    ∑ w ∈ range (2 * p ^ (r - 1)), f w * h w = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  have hpr0 : (p : ZMod (p ^ r)) ^ r = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  -- Helper: if g is constant on p^(k-1)-blocks and divisible by p^(r-k), then ∑ g * h = 0!
  have hlayer : ∀ (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r) (g : ℕ → ZMod (p ^ r)),
      (∀ w < 2 * p ^ (r - 1), g w = g ((w / p ^ (k - 1)) * p ^ (k - 1))) →
      (∀ b < 2 * p ^ (r - k), ((p : ZMod (p ^ r)) ^ (r - k)) ∣ g (b * p ^ (k - 1))) →
      ∑ w ∈ range (2 * p ^ (r - 1)), g w * h w = 0 := by
    intro k hk1 hkr g hconst hdvd
    have hpow : 2 * p ^ (r - 1) = (2 * p ^ (r - k)) * p ^ (k - 1) := by
      rw [mul_assoc, ← pow_add, show (r - k) + (k - 1) = r - 1 by omega]
    have hsplit : ∑ w ∈ range ((2 * p ^ (r - k)) * p ^ (k - 1)), g w * h w =
        ∑ b ∈ range (2 * p ^ (r - k)),
          ∑ w ∈ Ico (b * p ^ (k - 1)) ((b + 1) * p ^ (k - 1)), g w * h w := by
      have hbi : ∀ N M : ℕ, ∀ F : ℕ → ZMod (p ^ r),
          ∑ w ∈ range (N * M), F w = ∑ b ∈ range N, ∑ w ∈ Ico (b * M) ((b + 1) * M), F w := by
        intro N M F
        induction N with
        | zero => simp
        | succ N ihN =>
          rw [Finset.sum_range_succ, ← ihN, show (N + 1) * M = N * M + M by ring]
          have hdisj : Disjoint (range (N * M)) (Ico (N * M) (N * M + M)) := by
            rw [Finset.disjoint_left]; intro x hx1 hx2
            simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2; omega
          have hun : range (N * M + M) = range (N * M) ∪ Ico (N * M) (N * M + M) := by
            ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
          rw [hun, Finset.sum_union hdisj]
      exact hbi _ _ _
    rw [hpow, hsplit]
    refine Finset.sum_eq_zero (fun b hb => ?_)
    have hblt : b < 2 * p ^ (r - k) := Finset.mem_range.mp hb
    have hblock : ∑ w ∈ Ico (b * p ^ (k - 1)) ((b + 1) * p ^ (k - 1)), g w * h w =
        g (b * p ^ (k - 1)) * ∑ w ∈ Ico (b * p ^ (k - 1)) ((b + 1) * p ^ (k - 1)), h w := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w hw => ?_)
      simp only [Finset.mem_Ico] at hw
      have hdiv : w / p ^ (k - 1) = b := by
        have hpos : 0 < p ^ (k - 1) := pow_pos hp.pos _
        apply Nat.le_antisymm
        · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpos).mpr hw.2)
        · exact (Nat.le_div_iff_mul_le hpos).mpr hw.1
      have hwlt : w < 2 * p ^ (r - 1) := by
        calc w < (b + 1) * p ^ (k - 1) := hw.2
          _ ≤ (2 * p ^ (r - k)) * p ^ (k - 1) := Nat.mul_le_mul_right _ (by omega)
          _ = 2 * p ^ (r - 1) := hpow.symm
      rw [hconst w hwlt, hdiv]
    rw [hblock]
    obtain ⟨c1, hc1⟩ := hdvd b hblt
    obtain ⟨c2, hc2⟩ := hh k hk1 hkr b hblt
    rw [hc1, hc2]
    calc (p : ZMod (p ^ r)) ^ (r - k) * c1 * ((p : ZMod (p ^ r)) ^ k * c2)
        = (p : ZMod (p ^ r)) ^ ((r - k) + k) * (c1 * c2) := by rw [pow_add]; ring
      _ = (p : ZMod (p ^ r)) ^ r * (c1 * c2) := by rw [Nat.sub_add_cancel hkr]
      _ = 0 := by rw [hpr0, zero_mul]
  -- Now telescope f w = f ((w / p^(r-1)) * p^(r-1)) + ∑_{k=1}^{r-1} (f ((w/p^(k-1))*p^(k-1)) - f ((w/p^k)*p^k))!
  have htel : ∀ w, f w = f ((w / p ^ (r - 1)) * p ^ (r - 1)) +
      ∑ k ∈ Ico 1 r, (f ((w / p ^ (k - 1)) * p ^ (k - 1)) - f ((w / p ^ k) * p ^ k)) := by
    intro w
    have hsum : ∀ m : ℕ, 1 ≤ m →
        ∑ k ∈ Ico 1 m, (f ((w / p ^ (k - 1)) * p ^ (k - 1)) - f ((w / p ^ k) * p ^ k)) =
          f w - f ((w / p ^ (m - 1)) * p ^ (m - 1)) := by
      intro m hm
      induction m with
      | zero => omega
      | succ m ih =>
        by_cases hm1 : m = 0
        · subst hm1; simp
        · rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ m), ih (by omega)]
          simp only [Nat.add_sub_cancel]
          ring
    rw [hsum r hr]
    ring
  have hmain : ∑ w ∈ range (2 * p ^ (r - 1)), f w * h w =
      (∑ w ∈ range (2 * p ^ (r - 1)), f ((w / p ^ (r - 1)) * p ^ (r - 1)) * h w) +
      ∑ k ∈ Ico 1 r, ∑ w ∈ range (2 * p ^ (r - 1)),
        (f ((w / p ^ (k - 1)) * p ^ (k - 1)) - f ((w / p ^ k) * p ^ k)) * h w := by
    have h1 : ∀ w, f w * h w = f ((w / p ^ (r - 1)) * p ^ (r - 1)) * h w +
        ∑ k ∈ Ico 1 r, (f ((w / p ^ (k - 1)) * p ^ (k - 1)) - f ((w / p ^ k) * p ^ k)) * h w := by
      intro w
      conv_lhs => rw [htel w]
      rw [add_mul, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun w _ => h1 w), Finset.sum_add_distrib, Finset.sum_comm]
  rw [hmain]
  have htop : ∑ w ∈ range (2 * p ^ (r - 1)), f ((w / p ^ (r - 1)) * p ^ (r - 1)) * h w = 0 := by
    refine hlayer r hr le_rfl (fun w => f ((w / p ^ (r - 1)) * p ^ (r - 1))) ?_ ?_
    · intro w _
      have hpos : 0 < p ^ (r - 1) := pow_pos hp.pos _
      rw [Nat.mul_div_cancel _ hpos]
    · intro b _; simp
  have hmid : ∑ k ∈ Ico 1 r, ∑ w ∈ range (2 * p ^ (r - 1)),
      (f ((w / p ^ (k - 1)) * p ^ (k - 1)) - f ((w / p ^ k) * p ^ k)) * h w = 0 := by
    refine Finset.sum_eq_zero (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hkr : k < r := (Finset.mem_Ico.mp hk).2
    refine hlayer k hk1 (le_of_lt hkr)
      (fun w => f ((w / p ^ (k - 1)) * p ^ (k - 1)) - f ((w / p ^ k) * p ^ k)) ?_ ?_
    · intro w _
      have hpos1 : 0 < p ^ (k - 1) := pow_pos hp.pos _
      have hdiv1 : ((w / p ^ (k - 1)) * p ^ (k - 1)) / p ^ (k - 1) = w / p ^ (k - 1) :=
        Nat.mul_div_cancel _ hpos1
      have hdiv2 : ((w / p ^ (k - 1)) * p ^ (k - 1)) / p ^ k = w / p ^ k := by
        have hpk : p ^ k = p ^ (k - 1) * p := by
          conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
        rw [hpk, ← Nat.div_div_eq_div_mul, hdiv1, Nat.div_div_eq_div_mul]
      rw [hdiv1, hdiv2]
    · intro b hb
      have hwlt : b * p ^ (k - 1) < 2 * p ^ (r - 1) := by
        calc b * p ^ (k - 1) < (2 * p ^ (r - k)) * p ^ (k - 1) :=
              Nat.mul_lt_mul_of_pos_right hb (pow_pos hp.pos _)
          _ = 2 * p ^ (r - 1) := by rw [mul_assoc, ← pow_add, show (r - k) + (k - 1) = r - 1 by omega]
      have hpos1 : 0 < p ^ (k - 1) := pow_pos hp.pos _
      rw [Nat.mul_div_cancel _ hpos1]
      exact hf k hk1 hkr (b * p ^ (k - 1)) hwlt
  rw [htop, hmid, add_zero]

lemma zmod_cancel_coprime {q c : ℕ} [NeZero q] (hcop : Nat.Coprime c q) {x y : ZMod q}
    (h : (c : ZMod q) * x = (c : ZMod q) * y) : x = y := by
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime c hcop
  have hu : (u : ZMod q) = (c : ZMod q) := ZMod.coe_unitOfCoprime c hcop
  rw [← hu] at h
  calc x = ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u : ZMod q) * x) := by
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    _ = ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * ((u : ZMod q) * y) := by rw [h]
    _ = y := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

lemma zmod_inv_sq_of_coprime {q c : ℕ} [NeZero q] (hcop : Nat.Coprime c q) :
    ((c : ZMod q)⁻¹) * ((c : ZMod q)⁻¹) = ((c : ZMod q) ^ 2)⁻¹ := by
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime c hcop
  have hu : (u : ZMod q) = (c : ZMod q) := ZMod.coe_unitOfCoprime c hcop
  rw [← hu, zmod_unit_inv_eq u, ← Units.val_mul, ← Units.val_pow_eq_pow_val,
    zmod_unit_inv_eq (u ^ 2)]
  congr 1
  rw [sq, mul_inv]

lemma nat_coprime_prod_right_p4 {ι : Type*} {s : Finset ι} {p : ℕ} {f : ι → ℕ}
    (hf : ∀ i ∈ s, Nat.Coprime p (f i)) : Nat.Coprime p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul_right
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

def Fblock4 (p m : ℕ) : ℕ := ∏ i ∈ Ico 1 p, (m * p + i)

lemma Fblock4_coprime {p : ℕ} (hp : p.Prime) (m : ℕ) : Nat.Coprime p (Fblock4 p m) := by
  refine nat_coprime_prod_right_p4 (fun i hi => ?_)
  have hi' := Finset.mem_Ico.mp hi
  rw [hp.coprime_iff_not_dvd]
  intro hd
  have hd_i : p ∣ i := (Nat.dvd_add_right (dvd_mul_left p m)).mp hd
  exact Nat.not_dvd_of_pos_of_lt hi'.1 hi'.2 hd_i

lemma factorial_mul_eq4 {p : ℕ} (hp : 0 < p) (m : ℕ) :
    (m * p).factorial = p ^ m * m.factorial * ∏ j ∈ range m, Fblock4 p j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : ((m + 1) * p).factorial = (m * p).factorial * ∏ i ∈ Icc 1 p, (m * p + i) := by
      have hgen : ∀ a k : ℕ, (a + k).factorial = a.factorial * ∏ i ∈ Icc 1 k, (a + i) := by
        intro a k
        induction k with
        | zero => simp
        | succ k ihk =>
          rw [show a + (k + 1) = (a + k) + 1 by omega, Nat.factorial_succ, ihk]
          have hIcc : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.prod_insert (by simp)]
          ring
      simpa [Nat.add_mul] using hgen (m * p) p
    have hIcc : ∏ i ∈ Icc 1 p, (m * p + i) = ((m + 1) * p) * Fblock4 p m := by
      have hs : Icc 1 p = insert p (Ico 1 p) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
      rw [hs, Finset.prod_insert (by simp), Fblock4]
      have : m * p + p = (m + 1) * p := by ring
      rw [this]
    rw [hsplit, hIcc, ih, Finset.prod_range_succ, pow_succ, Nat.factorial_succ]
    ring

lemma choose_mul_Fblock4 {p : ℕ} (hp : 0 < p) (B D : ℕ) :
    ((B + D) * p).choose (B * p) * (∏ j ∈ range B, Fblock4 p j) =
      (B + D).choose B * (∏ j ∈ range B, Fblock4 p (D + j)) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show B * p ≤ (B + D) * p by nlinarith)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show B ≤ B + D by omega)
  have hs1 : (B + D) * p - B * p = D * p := by
    rw [Nat.add_mul, Nat.add_sub_cancel_left]
  have hs2 : B + D - B = D := Nat.add_sub_cancel_left B D
  rw [hs1] at h1; rw [hs2] at h2
  have hprod_split : ∏ j ∈ range (B + D), Fblock4 p j =
      (∏ j ∈ range D, Fblock4 p j) * (∏ j ∈ range B, Fblock4 p (D + j)) := by
    have hs : range (B + D) = range D ∪ Ico D (B + D) := by
      ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hd : Disjoint (range D) (Ico D (B + D)) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2; omega
    rw [hs, Finset.prod_union hd]
    congr 1
    refine Finset.prod_bij (fun j _ => j - D) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
    · intro j1 hj1 j2 hj2 heq; simp only [Finset.mem_Ico] at hj1 hj2; omega
    · intro j hj; simp only [Finset.mem_range] at hj
      exact ⟨D + j, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj; simp only [Finset.mem_Ico] at hj; congr 1; omega
  have hpos : 0 < p ^ (B + D) * B.factorial * D.factorial * (∏ j ∈ range D, Fblock4 p j) := by
    have hFp : 0 < ∏ j ∈ range D, Fblock4 p j :=
      Finset.prod_pos (fun j _ => Finset.prod_pos (fun i hi => by
        have := (Finset.mem_Ico.mp hi).1; omega))
    positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  have hlhs : p ^ (B + D) * B.factorial * D.factorial * (∏ j ∈ range D, Fblock4 p j) *
      (((B + D) * p).choose (B * p) * ∏ j ∈ range B, Fblock4 p j) =
      ((B + D) * p).choose (B * p) * (B * p).factorial * (D * p).factorial := by
    rw [factorial_mul_eq4 hp B, factorial_mul_eq4 hp D, pow_add]; ring
  have hrhs : p ^ (B + D) * B.factorial * D.factorial * (∏ j ∈ range D, Fblock4 p j) *
      ((B + D).choose B * ∏ j ∈ range B, Fblock4 p (D + j)) =
      ((B + D) * p).factorial := by
    rw [factorial_mul_eq4 hp (B + D), hprod_split, ← h2]; ring
  rw [hlhs, hrhs, h1]

lemma choose_pred_mul {N K : ℕ} (h : K < N) :
    (N - K) * N.choose K = N * (N - 1).choose K := by
  have h1 := Nat.add_one_mul_choose_eq (N - 1) (N - 1 - K)
  rw [show N - 1 + 1 = N by omega, show N - 1 - K + 1 = N - K by omega] at h1
  rw [← Nat.choose_symm (by omega : N - 1 - K ≤ N - 1),
    show N - 1 - (N - 1 - K) = K by omega] at h1
  rw [← Nat.choose_symm (by omega : N - K ≤ N),
    show N - (N - K) = K by omega] at h1
  linarith

lemma choose_sub_one_mod {p r A M s : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r)
    (hs : s < p) (hMA : M * p + s < A * p ^ r) :
    (((A * p ^ r - 1).choose (M * p + s) : ℕ) : ZMod (p ^ r)) =
      (-1 : ZMod (p ^ r)) ^ s * (((A * p ^ (r - 1) - 1).choose M : ℕ) : ZMod (p ^ r)) := by
  have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  set q := p ^ r
  set q1 := p ^ (r - 1)
  have hq : q = q1 * p := by
    simp only [q, q1]; conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
  have hAq_zero : ((A * q : ℕ) : ZMod q) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_self, mul_zero]
  induction s with
  | zero =>
    simp only [Nat.add_zero, pow_zero, one_mul]
    have hMlt : M < A * q1 := by
      have : M * p < (A * q1) * p := by rw [mul_assoc, ← hq]; omega
      exact Nat.lt_of_mul_lt_mul_right this
    set D := A * q1 - M
    have hMD : M + D = A * q1 := Nat.add_sub_cancel' (le_of_lt hMlt)
    have hMDp : (M + D) * p = A * q := by rw [hMD, mul_assoc, ← hq]
    have hDpos : 0 < D := by omega
    have hpred1 : D * ((M + D) * p).choose (M * p) = (M + D) * ((M + D) * p - 1).choose (M * p) := by
      have h := choose_pred_mul (show M * p < (M + D) * p by nlinarith [hp.pos])
      rw [show (M + D) * p - M * p = D * p by rw [Nat.add_mul, Nat.add_sub_cancel_left]] at h
      apply Nat.eq_of_mul_eq_mul_right hp.pos
      linarith
    have hpred2 : D * (M + D).choose M = (M + D) * (M + D - 1).choose M := by
      have h := choose_pred_mul (show M < M + D by omega)
      rwa [Nat.add_sub_cancel_left] at h
    have hcf := choose_mul_Fblock4 hp.pos M D
    have hrel_nat : ((M + D) * p - 1).choose (M * p) * (∏ j ∈ range M, Fblock4 p j) =
        (M + D - 1).choose M * (∏ j ∈ range M, Fblock4 p (D + j)) := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < M + D by omega)
      calc (M + D) * (((M + D) * p - 1).choose (M * p) * ∏ j ∈ range M, Fblock4 p j)
          = ((M + D) * ((M + D) * p - 1).choose (M * p)) * ∏ j ∈ range M, Fblock4 p j := by ring
        _ = (D * ((M + D) * p).choose (M * p)) * ∏ j ∈ range M, Fblock4 p j := by rw [hpred1]
        _ = D * (((M + D) * p).choose (M * p) * ∏ j ∈ range M, Fblock4 p j) := by ring
        _ = D * ((M + D).choose M * ∏ j ∈ range M, Fblock4 p (D + j)) := by rw [hcf]
        _ = (D * (M + D).choose M) * ∏ j ∈ range M, Fblock4 p (D + j) := by ring
        _ = (M + D) * ((M + D - 1).choose M * ∏ j ∈ range M, Fblock4 p (D + j)) := by rw [hpred2]; ring
    rw [hMDp, hMD] at hrel_nat
    have hrel_z : (((A * q - 1).choose (M * p) : ℕ) : ZMod q) * ((∏ j ∈ range M, Fblock4 p j : ℕ) : ZMod q) =
        (((A * q1 - 1).choose M : ℕ) : ZMod q) * ((∏ j ∈ range M, Fblock4 p (D + j) : ℕ) : ZMod q) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, hrel_nat]
    -- Show ∏ Fblock4 p (D + j) ≡ ∏ Fblock4 p j (mod q)
    have hFprod_eq : ((∏ j ∈ range M, Fblock4 p (D + j) : ℕ) : ZMod q) =
        ((∏ j ∈ range M, Fblock4 p j : ℕ) : ZMod q) := by
      rw [Nat.cast_prod, Nat.cast_prod]
      have hre : ∏ j ∈ range M, (Fblock4 p (D + j) : ZMod q) =
          ∏ j ∈ range M, (Fblock4 p (A * q1 - 1 - j) : ZMod q) := by
        refine Finset.prod_bij (fun j _ => M - 1 - j) ?_ ?_ ?_ ?_
        · intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
        · intro j1 hj1 j2 hj2 heq; simp only [Finset.mem_range] at hj1 hj2; omega
        · intro j hj; simp only [Finset.mem_range] at hj
          exact ⟨M - 1 - j, Finset.mem_range.mpr (by omega), by omega⟩
        · intro j hj; simp only [Finset.mem_range] at hj; congr 2; omega
      rw [hre]
      refine Finset.prod_congr rfl (fun j hj => ?_)
      have hjlt : j < M := Finset.mem_range.mp hj
      have hjAq1 : j + 1 ≤ A * q1 := by omega
      simp only [Fblock4, Nat.cast_prod]
      have hrev : ∏ i ∈ Ico 1 p, (((A * q1 - 1 - j) * p + i : ℕ) : ZMod q) =
          ∏ i ∈ Ico 1 p, (-((j * p + i : ℕ) : ZMod q)) := by
        refine Finset.prod_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
        · intro i hi; simp only [Finset.mem_Ico] at hi ⊢; omega
        · intro i1 hi1 i2 hi2 heq; simp only [Finset.mem_Ico] at hi1 hi2; omega
        · intro i hi; simp only [Finset.mem_Ico] at hi
          exact ⟨p - i, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro i hi
          have hi' := Finset.mem_Ico.mp hi
          have hsum_nat : ((A * q1 - 1 - j) * p + i) + (j * p + (p - i)) = A * q := by
            have h1 : (A * q1 - 1 - j) + j + 1 = A * q1 := by omega
            calc ((A * q1 - 1 - j) * p + i) + (j * p + (p - i))
                = ((A * q1 - 1 - j) + j) * p + (i + (p - i)) := by ring
              _ = ((A * q1 - 1 - j) + j) * p + p := by rw [Nat.add_sub_of_le (le_of_lt hi'.2)]
              _ = ((A * q1 - 1 - j) + j + 1) * p := by ring
              _ = (A * q1) * p := by rw [h1]
              _ = A * q := by rw [hq]; ring
          have hsum_z : (((A * q1 - 1 - j) * p + i : ℕ) : ZMod q) + ((j * p + (p - i) : ℕ) : ZMod q) = 0 := by
            rw [← Nat.cast_add, hsum_nat, hAq_zero]
          exact eq_neg_of_add_eq_zero_left hsum_z
      rw [hrev, Finset.prod_neg]
      have heven : Even (Ico 1 p).card := by
        rw [Nat.card_Ico]
        have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
        exact ⟨(p - 1) / 2, by omega⟩
      rw [heven.neg_one_pow, one_mul]
    rw [hFprod_eq] at hrel_z
    have hcop : Nat.Coprime (∏ j ∈ range M, Fblock4 p j) q :=
      (nat_coprime_prod_right_p4 (fun j _ => Fblock4_coprime hp j)).symm.pow_right r
    rw [mul_comm, mul_comm (((A * q1 - 1).choose M : ℕ) : ZMod q)] at hrel_z
    exact zmod_cancel_coprime hcop hrel_z
  | succ s ih =>
    have hstep_nat : (M * p + (s + 1)) * (A * q - 1).choose (M * p + (s + 1)) =
        (A * q - (M * p + (s + 1))) * (A * q - 1).choose (M * p + s) := by
      have h := Nat.choose_succ_right_eq (A * q - 1) (M * p + s)
      have hsub : A * q - 1 - (M * p + s) = A * q - (M * p + (s + 1)) := by omega
      have hadd : M * p + s + 1 = M * p + (s + 1) := by omega
      rw [hsub, hadd] at h
      linarith
    have hstep_z : ((M * p + (s + 1) : ℕ) : ZMod q) * (((A * q - 1).choose (M * p + (s + 1)) : ℕ) : ZMod q) =
        ((A * q - (M * p + (s + 1)) : ℕ) : ZMod q) * (((A * q - 1).choose (M * p + s) : ℕ) : ZMod q) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, hstep_nat]
    have hneg_z : ((A * q - (M * p + (s + 1)) : ℕ) : ZMod q) = -((M * p + (s + 1) : ℕ) : ZMod q) := by
      have hsum : ((A * q - (M * p + (s + 1)) : ℕ) : ZMod q) + ((M * p + (s + 1) : ℕ) : ZMod q) = 0 := by
        rw [← Nat.cast_add, Nat.sub_add_cancel (by omega : M * p + (s + 1) ≤ A * q), hAq_zero]
      exact eq_neg_of_add_eq_zero_left hsum
    rw [hneg_z, neg_mul, ← mul_neg] at hstep_z
    have hcop : Nat.Coprime (M * p + (s + 1)) q := by
      have hnd : ¬ p ∣ (M * p + (s + 1)) := by
        intro hd
        have hs1 : p ∣ s + 1 := (Nat.dvd_add_right (dvd_mul_left p M)).mp hd
        exact Nat.not_dvd_of_pos_of_lt (by omega) hs hs1
      exact ((hp.coprime_iff_not_dvd).mpr hnd).symm.pow_right r
    have hres := zmod_cancel_coprime hcop hstep_z
    rw [hres, ih (by omega) (by omega), pow_succ]
    ring

lemma choose_add_mod {p r A M s : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (hs : s < p) :
    (((A * p ^ r + M * p + s).choose (M * p + s) : ℕ) : ZMod (p ^ r)) =
      (((A * p ^ (r - 1) + M).choose M : ℕ) : ZMod (p ^ r)) := by
  have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  set q := p ^ r
  set q1 := p ^ (r - 1)
  have hq : q = q1 * p := by
    simp only [q, q1]; conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
  have hAq_zero : ((A * q : ℕ) : ZMod q) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_self, mul_zero]
  induction s with
  | zero =>
    simp only [Nat.add_zero]
    have hcf := choose_mul_Fblock4 hp.pos M (A * q1)
    have h1 : (M + A * q1) * p = A * q + M * p := by rw [hq]; ring
    have h2 : M + A * q1 = A * q1 + M := by ring
    rw [h1, h2] at hcf
    have hcf_z : (((A * q + M * p).choose (M * p) : ℕ) : ZMod q) * ((∏ j ∈ range M, Fblock4 p j : ℕ) : ZMod q) =
        (((A * q1 + M).choose M : ℕ) : ZMod q) * ((∏ j ∈ range M, Fblock4 p (A * q1 + j) : ℕ) : ZMod q) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, hcf]
    have hFprod_eq : ((∏ j ∈ range M, Fblock4 p (A * q1 + j) : ℕ) : ZMod q) =
        ((∏ j ∈ range M, Fblock4 p j : ℕ) : ZMod q) := by
      rw [Nat.cast_prod, Nat.cast_prod]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      simp only [Fblock4, Nat.cast_prod]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have hsum : (A * q1 + j) * p + i = A * q + (j * p + i) := by rw [hq]; ring
      rw [hsum, Nat.cast_add, hAq_zero, zero_add]
    rw [hFprod_eq] at hcf_z
    have hcop : Nat.Coprime (∏ j ∈ range M, Fblock4 p j) q :=
      (nat_coprime_prod_right_p4 (fun j _ => Fblock4_coprime hp j)).symm.pow_right r
    rw [mul_comm, mul_comm (((A * q1 + M).choose M : ℕ) : ZMod q)] at hcf_z
    exact zmod_cancel_coprime hcop hcf_z
  | succ s ih =>
    have hstep_nat : (M * p + (s + 1)) * (A * q + M * p + (s + 1)).choose (M * p + (s + 1)) =
        (A * q + M * p + (s + 1)) * (A * q + M * p + s).choose (M * p + s) := by
      have h := Nat.add_one_mul_choose_eq (A * q + M * p + s) (M * p + s)
      have h1 : A * q + M * p + s + 1 = A * q + M * p + (s + 1) := by omega
      have h2 : M * p + s + 1 = M * p + (s + 1) := by omega
      rw [h1, h2] at h
      linarith
    have hstep_z : ((M * p + (s + 1) : ℕ) : ZMod q) *
        (((A * q + M * p + (s + 1)).choose (M * p + (s + 1)) : ℕ) : ZMod q) =
        ((A * q + M * p + (s + 1) : ℕ) : ZMod q) *
        (((A * q + M * p + s).choose (M * p + s) : ℕ) : ZMod q) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul, hstep_nat]
    have hAq_drop : ((A * q + M * p + (s + 1) : ℕ) : ZMod q) = ((M * p + (s + 1) : ℕ) : ZMod q) := by
      rw [show A * q + M * p + (s + 1) = A * q + (M * p + (s + 1)) by omega,
        Nat.cast_add, hAq_zero, zero_add]
    rw [hAq_drop] at hstep_z
    have hcop : Nat.Coprime (M * p + (s + 1)) q := by
      have hnd : ¬ p ∣ (M * p + (s + 1)) := by
        intro hd
        have hs1 : p ∣ s + 1 := (Nat.dvd_add_right (dvd_mul_left p M)).mp hd
        exact Nat.not_dvd_of_pos_of_lt (by omega) hs hs1
      exact ((hp.coprime_iff_not_dvd).mpr hnd).symm.pow_right r
    rw [zmod_cancel_coprime hcop hstep_z, ih (by omega)]

/-- Factor weight `fw` on half-blocks `w ∈ [0, 2 * p^(r-1))`. -/
def fw (p n r m w : ℕ) : ZMod (p ^ r) :=
  let q1 := p ^ (r - 1)
  (((n * q1 - 1).choose (m * q1 + w / 2) : ℕ) : ZMod (p ^ r)) *
  (((2 * n * q1 - 1).choose ((n + m) * q1 + w / 2) : ℕ) : ZMod (p ^ r)) *
  (((2 * n * q1 + 2 * m * q1 + w).choose (2 * m * q1 + w) : ℕ) : ZMod (p ^ r))

/-- Half-block reciprocal square sum `Hval`. -/
def Hval (p r w : ℕ) : ZMod (p ^ r) :=
  ∑ v ∈ (if w % 2 = 0 then Icc 1 ((p - 1) / 2) else Icc ((p + 1) / 2) (p - 1)),
    ((((w / 2) * p + v : ℕ) : ZMod (p ^ r)) ^ 2)⁻¹

lemma nondiv_term_div_q2_mod {p n r m t : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r)
    (hm : m < n) (ht1 : 1 ≤ t) (ht2 : t < p ^ r) (htp : ¬ p ∣ t) :
    let q := p ^ r
    let j := m * q + t
    let S := (n * q).choose j * (2 * n * q).choose (n * q + j) * (2 * n * q + 2 * j).choose (2 * j)
    q ^ 2 ∣ S ∧
    ((S / q ^ 2 : ℕ) : ZMod q) =
      2 * (n : ZMod q) ^ 2 * ((t : ZMod q) ^ 2)⁻¹ *
        fw p n r m (2 * (t / p) + (if 2 * (t % p) < p then 0 else 1)) := by
  have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  intro q j S
  set q1 := p ^ (r - 1)
  have hq : q = q1 * p := by
    simp only [q, q1]; conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
  have hq_pos : 0 < q := pow_pos hp.pos r
  have hq1_pos : 0 < q1 := pow_pos hp.pos (r - 1)
  have hcop_t : Nat.Coprime t q := ((hp.coprime_iff_not_dvd).mpr htp).symm.pow_right r
  have hnd_j : ¬ p ∣ j := by
    intro hd
    have hmq : p ∣ m * q := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) m
    exact htp ((Nat.dvd_add_right hmq).mp hd)
  have hcop_j : Nat.Coprime j q := ((hp.coprime_iff_not_dvd).mpr hnd_j).symm.pow_right r
  have hnd_nj : ¬ p ∣ (n * q + j) := by
    intro hd
    have hnq : p ∣ n * q := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) n
    exact hnd_j ((Nat.dvd_add_right hnq).mp hd)
  have hcop_nj : Nat.Coprime (n * q + j) q := ((hp.coprime_iff_not_dvd).mpr hnd_nj).symm.pow_right r
  -- Factor 1: q ∣ C(n*q, j)
  have hmul1 : j * (n * q).choose j = n * q * (n * q - 1).choose (j - 1) := by
    have h := Nat.add_one_mul_choose_eq (n * q - 1) (j - 1)
    have hnq_pos : 1 ≤ n * q := by nlinarith
    have hj_pos : 1 ≤ j := by omega
    rw [Nat.sub_add_cancel hnq_pos, Nat.sub_add_cancel hj_pos] at h
    linarith
  have hdvd1 : q ∣ (n * q).choose j := by
    have hd : q ∣ j * (n * q).choose j := ⟨n * (n * q - 1).choose (j - 1), by linarith⟩
    exact hcop_j.symm.dvd_of_dvd_mul_left hd
  have hdiv1 : j * ((n * q).choose j / q) = n * (n * q - 1).choose (j - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hq_pos
    calc q * (j * ((n * q).choose j / q))
        = j * (q * ((n * q).choose j / q)) := by ring
      _ = j * (n * q).choose j := by rw [Nat.mul_div_cancel' hdvd1]
      _ = q * (n * (n * q - 1).choose (j - 1)) := by linarith
  -- Factor 2: q ∣ C(2*n*q, n*q + j)
  have hmul2 : (n * q + j) * (2 * n * q).choose (n * q + j) =
      2 * n * q * (2 * n * q - 1).choose (n * q + j - 1) := by
    have h := Nat.add_one_mul_choose_eq (2 * n * q - 1) (n * q + j - 1)
    have h2nq_pos : 1 ≤ 2 * n * q := by nlinarith
    have hnj_pos : 1 ≤ n * q + j := by omega
    rw [Nat.sub_add_cancel h2nq_pos, Nat.sub_add_cancel hnj_pos] at h
    linarith
  have hdvd2 : q ∣ (2 * n * q).choose (n * q + j) := by
    have hd : q ∣ (n * q + j) * (2 * n * q).choose (n * q + j) :=
      ⟨2 * n * (2 * n * q - 1).choose (n * q + j - 1), by linarith⟩
    exact hcop_nj.symm.dvd_of_dvd_mul_left hd
  have hdiv2 : (n * q + j) * ((2 * n * q).choose (n * q + j) / q) =
      2 * n * (2 * n * q - 1).choose (n * q + j - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hq_pos
    calc q * ((n * q + j) * ((2 * n * q).choose (n * q + j) / q))
        = (n * q + j) * (q * ((2 * n * q).choose (n * q + j) / q)) := by ring
      _ = (n * q + j) * (2 * n * q).choose (n * q + j) := by rw [Nat.mul_div_cancel' hdvd2]
      _ = q * (2 * n * (2 * n * q - 1).choose (n * q + j - 1)) := by linarith
  have hdvd_q2 : q ^ 2 ∣ S := by
    rw [sq]
    exact dvd_mul_of_dvd_left (mul_dvd_mul hdvd1 hdvd2) _
  refine ⟨hdvd_q2, ?_⟩
  have hS_div : S / q ^ 2 = ((n * q).choose j / q) * ((2 * n * q).choose (n * q + j) / q) *
      (2 * n * q + 2 * j).choose (2 * j) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hq_pos 2)
    rw [Nat.mul_div_cancel' hdvd_q2, sq]
    calc S = (q * ((n * q).choose j / q)) * (q * ((2 * n * q).choose (n * q + j) / q)) *
            (2 * n * q + 2 * j).choose (2 * j) := by
          rw [Nat.mul_div_cancel' hdvd1, Nat.mul_div_cancel' hdvd2]
      _ = q * q * (((n * q).choose j / q) * ((2 * n * q).choose (n * q + j) / q) *
            (2 * n * q + 2 * j).choose (2 * j)) := by ring
  rw [hS_div, Nat.cast_mul, Nat.cast_mul]
  -- Evaluate each of the 3 factors in ZMod q!
  have hj_z : (j : ZMod q) = (t : ZMod q) := by
    simp only [j, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
  have hnj_z : ((n * q + j : ℕ) : ZMod q) = (t : ZMod q) := by
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add, hj_z]
  have ht_inv_mul : (t : ZMod q)⁻¹ * (t : ZMod q) = 1 := by
    rw [mul_comm]; exact ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime t q).mpr hcop_t)
  have hf1_z : (((n * q).choose j / q : ℕ) : ZMod q) =
      (t : ZMod q)⁻¹ * (n : ZMod q) * (((n * q - 1).choose (j - 1) : ℕ) : ZMod q) := by
    have h1 : (t : ZMod q) * (((n * q).choose j / q : ℕ) : ZMod q) =
        (n : ZMod q) * (((n * q - 1).choose (j - 1) : ℕ) : ZMod q) := by
      rw [← hj_z, ← Nat.cast_mul, ← Nat.cast_mul, hdiv1]
    calc (((n * q).choose j / q : ℕ) : ZMod q)
        = (t : ZMod q)⁻¹ * ((t : ZMod q) * (((n * q).choose j / q : ℕ) : ZMod q)) := by
          rw [← mul_assoc, ht_inv_mul, one_mul]
      _ = (t : ZMod q)⁻¹ * (n : ZMod q) * (((n * q - 1).choose (j - 1) : ℕ) : ZMod q) := by
          rw [h1]; ring
  have hf2_z : (((2 * n * q).choose (n * q + j) / q : ℕ) : ZMod q) =
      (t : ZMod q)⁻¹ * (2 * (n : ZMod q)) * (((2 * n * q - 1).choose (n * q + j - 1) : ℕ) : ZMod q) := by
    have h2 : (t : ZMod q) * (((2 * n * q).choose (n * q + j) / q : ℕ) : ZMod q) =
        2 * (n : ZMod q) * (((2 * n * q - 1).choose (n * q + j - 1) : ℕ) : ZMod q) := by
      have h2' := congrArg (Nat.cast : ℕ → ZMod q) hdiv2
      simp only [Nat.cast_mul, Nat.cast_ofNat, hnj_z] at h2'
      exact h2'
    calc (((2 * n * q).choose (n * q + j) / q : ℕ) : ZMod q)
        = (t : ZMod q)⁻¹ * ((t : ZMod q) * (((2 * n * q).choose (n * q + j) / q : ℕ) : ZMod q)) := by
          rw [← mul_assoc, ht_inv_mul, one_mul]
      _ = (t : ZMod q)⁻¹ * (2 * (n : ZMod q)) * (((2 * n * q - 1).choose (n * q + j - 1) : ℕ) : ZMod q) := by
          rw [h2]; ring
  -- Write t = u * p + v with 1 ≤ v < p
  set u := t / p
  set v := t % p
  have hv_lt : v < p := Nat.mod_lt t hp.pos
  have hv_pos : 1 ≤ v := by
    rcases Nat.eq_zero_or_pos v with hv0 | hpos
    · exact absurd (Nat.dvd_of_mod_eq_zero hv0) htp
    · exact hpos
  have ht_eq : t = u * p + v := by
    have h := Nat.div_add_mod t p
    rw [mul_comm] at h
    exact h.symm
  have hu_lt : u < q1 := by
    have : u * p < q1 * p := by rw [← hq]; omega
    exact Nat.lt_of_mul_lt_mul_right this
  have hj_lt_nq : j < n * q := by
    have h1 : m * q + t < m * q + q := Nat.add_lt_add_left ht2 (m * q)
    have h2 : m * q + q = (m + 1) * q := by ring
    have h3 : (m + 1) * q ≤ n * q := Nat.mul_le_mul_right q hm
    exact lt_of_lt_of_le (h2 ▸ h1) h3
  -- Apply choose_sub_one_mod to factors 1 and 2
  have hj1_eq : j - 1 = (m * q1 + u) * p + (v - 1) := by
    have : j = (m * q1 + u) * p + v := by simp only [j, ht_eq, hq]; ring
    omega
  have hc1 := choose_sub_one_mod (p := p) (r := r) (A := n) (M := m * q1 + u) (s := v - 1)
    hp hp5 hr (by omega) (show (m * q1 + u) * p + (v - 1) < n * q by omega)
  rw [← hj1_eq] at hc1
  have hnj1_eq : n * q + j - 1 = ((n + m) * q1 + u) * p + (v - 1) := by
    have : n * q + j = ((n + m) * q1 + u) * p + v := by simp only [j, ht_eq, hq]; ring
    omega
  have hc2 := choose_sub_one_mod (p := p) (r := r) (A := 2 * n) (M := (n + m) * q1 + u) (s := v - 1)
    hp hp5 hr (by omega) (show ((n + m) * q1 + u) * p + (v - 1) < 2 * n * q by
      have h2nq : 2 * n * q = n * q + n * q := by ring
      omega)
  rw [← hnj1_eq] at hc2
  -- Apply choose_add_mod to factor 3
  set eps := if 2 * v < p then 0 else 1
  set w := 2 * u + eps
  set s3 := 2 * v - eps * p
  have hs3_lt : s3 < p := by
    simp only [s3, eps]; split_ifs <;> omega
  have h2t_eq : 2 * t = w * p + s3 := by
    simp only [w, s3, eps]
    split_ifs with hlt
    · rw [ht_eq]; simp; ring
    · have hsub : p + (2 * v - p) = 2 * v := Nat.add_sub_of_le (by omega)
      calc 2 * t = 2 * u * p + 2 * v := by rw [ht_eq]; ring
        _ = 2 * u * p + (p + (2 * v - p)) := by rw [hsub]
        _ = (2 * u + 1) * p + (2 * v - 1 * p) := by simp; ring
  have h2j_eq : 2 * j = (2 * m * q1 + w) * p + s3 := by
    calc 2 * j = 2 * m * q + 2 * t := by simp only [j]; ring
      _ = 2 * m * (q1 * p) + (w * p + s3) := by rw [hq, h2t_eq]
      _ = (2 * m * q1 + w) * p + s3 := by ring
  have hc3 := choose_add_mod (p := p) (r := r) (A := 2 * n) (M := 2 * m * q1 + w) (s := s3)
    hp hr hs3_lt
  have h2nq2j : 2 * n * q + (2 * m * q1 + w) * p + s3 = 2 * n * q + 2 * j := by
    rw [h2j_eq]; ring
  rw [h2nq2j, ← h2j_eq] at hc3
  have hw_div2 : w / 2 = u := by
    simp only [w, eps]; split_ifs <;> omega
  rw [hf1_z, hf2_z, hc1, hc2, hc3]
  have hsign : (-1 : ZMod q) ^ (v - 1) * (-1 : ZMod q) ^ (v - 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hinv_sq : (t : ZMod q)⁻¹ * (t : ZMod q)⁻¹ = ((t : ZMod q) ^ 2)⁻¹ :=
    zmod_inv_sq_of_coprime hcop_t
  simp only [fw, hw_div2]
  have hadd_assoc : 2 * n * q1 + (2 * m * q1 + w) = 2 * n * q1 + 2 * m * q1 + w := by ring
  rw [hadd_assoc]
  calc (t : ZMod q)⁻¹ * (n : ZMod q) * ((-1 : ZMod q) ^ (v - 1) * (((n * q1 - 1).choose (m * q1 + u) : ℕ) : ZMod q)) *
        ((t : ZMod q)⁻¹ * (2 * (n : ZMod q)) * ((-1 : ZMod q) ^ (v - 1) * (((2 * n * q1 - 1).choose ((n + m) * q1 + u) : ℕ) : ZMod q))) *
        (((2 * n * q1 + 2 * m * q1 + w).choose (2 * m * q1 + w) : ℕ) : ZMod q)
      = 2 * (n : ZMod q) ^ 2 * ((t : ZMod q)⁻¹ * (t : ZMod q)⁻¹) *
        ((-1 : ZMod q) ^ (v - 1) * (-1 : ZMod q) ^ (v - 1)) *
        ((((n * q1 - 1).choose (m * q1 + u) : ℕ) : ZMod q) *
         (((2 * n * q1 - 1).choose ((n + m) * q1 + u) : ℕ) : ZMod q) *
         (((2 * n * q1 + 2 * m * q1 + w).choose (2 * m * q1 + w) : ℕ) : ZMod q)) := by ring
    _ = 2 * (n : ZMod q) ^ 2 * ((t : ZMod q) ^ 2)⁻¹ *
        ((((n * q1 - 1).choose (m * q1 + u) : ℕ) : ZMod q) *
         (((2 * n * q1 - 1).choose ((n + m) * q1 + u) : ℕ) : ZMod q) *
         (((2 * n * q1 + 2 * m * q1 + w).choose (2 * m * q1 + w) : ℕ) : ZMod q)) := by
        rw [hinv_sq, hsign, mul_one]

lemma zmod_dvd_of_int_dvd {p r e : ℕ} {a b : ℕ}
    (h : (p : ℤ) ^ e ∣ (a : ℤ) - (b : ℤ)) :
    ((p : ZMod (p ^ r)) ^ e) ∣ (a : ZMod (p ^ r)) - (b : ZMod (p ^ r)) := by
  rcases h with ⟨c, hc⟩
  refine ⟨(c : ZMod (p ^ r)), ?_⟩
  have hz := congrArg (Int.cast : ℤ → ZMod (p ^ r)) hc
  simpa using hz

lemma zmod_dvd_add_of_int_dvd {p r e : ℕ} {a b : ℕ}
    (h : (p : ℤ) ^ e ∣ (a : ℤ) + (b : ℤ)) :
    ((p : ZMod (p ^ r)) ^ e) ∣ (a : ZMod (p ^ r)) + (b : ZMod (p ^ r)) := by
  rcases h with ⟨c, hc⟩
  refine ⟨(c : ZMod (p ^ r)), ?_⟩
  have hz := congrArg (Int.cast : ℤ → ZMod (p ^ r)) hc
  simpa using hz

lemma choose_add_step_dvd {p r k A B : ℕ} (hp : p.Prime) (hk1 : 1 ≤ k) (hkr : k < r)
    (hA : p ^ (r - 1) ∣ A) (hB : ¬ p ^ k ∣ B + 1) :
    ((p : ZMod (p ^ r)) ^ (r - k)) ∣
      (((A + B + 1).choose (B + 1) : ℕ) : ZMod (p ^ r)) -
      (((A + B).choose B : ℕ) : ZMod (p ^ r)) := by
  have : Fact p.Prime := ⟨hp⟩
  apply zmod_dvd_of_int_dvd
  set e := padicValNat p (B + 1)
  have he_lt : e < k := by
    by_contra hge
    have : p ^ k ∣ B + 1 := (pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd
    exact hB this
  obtain ⟨c, hc⟩ := pow_padicValNat_dvd (p := p) (n := B + 1)
  have hcop_c : Nat.Coprime p c := by
    rw [hp.coprime_iff_not_dvd]
    intro hpc
    rcases hpc with ⟨t, rfl⟩
    have h1 : p ^ (e + 1) ∣ B + 1 := ⟨t, by rw [hc, pow_succ]; ring⟩
    have h2 : e + 1 ≤ padicValNat p (B + 1) := (padicValNat_dvd_iff_le (by omega)).mp h1
    omega
  obtain ⟨A0, hA0⟩ := hA
  have hstep : (B + 1) * (A + B + 1).choose (B + 1) = (A + B + 1) * (A + B).choose B := by
    have h := Nat.add_one_mul_choose_eq (A + B) B
    linarith
  have hAe : A = p ^ e * (p ^ (r - 1 - e) * A0) := by
    rw [hA0, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
  have hcancel : c * (A + B + 1).choose (B + 1) = (p ^ (r - 1 - e) * A0 + c) * (A + B).choose B := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos e)
    calc p ^ e * (c * (A + B + 1).choose (B + 1))
        = (p ^ e * c) * (A + B + 1).choose (B + 1) := by ring
      _ = (B + 1) * (A + B + 1).choose (B + 1) := by rw [← hc]
      _ = (A + B + 1) * (A + B).choose B := hstep
      _ = p ^ e * ((p ^ (r - 1 - e) * A0 + c) * (A + B).choose B) := by
          rw [add_assoc A B 1, hAe, hc]; ring
  have hZ : (c : ℤ) * ((((A + B + 1).choose (B + 1) : ℕ) : ℤ) - (((A + B).choose B : ℕ) : ℤ)) =
      (p : ℤ) ^ (r - 1 - e) * ((A0 : ℤ) * (((A + B).choose B : ℕ) : ℤ)) := by
    have hZ0 : (c : ℤ) * (((A + B + 1).choose (B + 1) : ℕ) : ℤ) =
        (((p ^ (r - 1 - e) * A0 : ℕ) : ℤ) + (c : ℤ)) * (((A + B).choose B : ℕ) : ℤ) := by
      exact_mod_cast hcancel
    push_cast at hZ0
    linarith
  have hdvd : (p : ℤ) ^ (r - k) ∣ (c : ℤ) * ((((A + B + 1).choose (B + 1) : ℕ) : ℤ) - (((A + B).choose B : ℕ) : ℤ)) := by
    rw [hZ]
    exact dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) (by omega : r - k ≤ r - 1 - e)) _
  have hcopZ : IsCoprime ((p : ℤ) ^ (r - k)) (c : ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr hcop_c).pow_left
  exact hcopZ.dvd_of_dvd_mul_left hdvd

lemma choose_sub_one_step_dvd {p r k A B : ℕ} (hp : p.Prime) (hk1 : 1 ≤ k) (hkr : k < r)
    (hA : p ^ (r - 1) ∣ A) (hBA : B + 1 < A) (hB : ¬ p ^ k ∣ B + 1) :
    ((p : ZMod (p ^ r)) ^ (r - k)) ∣
      (((A - 1).choose (B + 1) : ℕ) : ZMod (p ^ r)) +
      (((A - 1).choose B : ℕ) : ZMod (p ^ r)) := by
  have : Fact p.Prime := ⟨hp⟩
  apply zmod_dvd_add_of_int_dvd
  set e := padicValNat p (B + 1)
  have he_lt : e < k := by
    by_contra hge
    have : p ^ k ∣ B + 1 := (pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd
    exact hB this
  obtain ⟨c, hc⟩ := pow_padicValNat_dvd (p := p) (n := B + 1)
  have hcop_c : Nat.Coprime p c := by
    rw [hp.coprime_iff_not_dvd]
    intro hpc
    rcases hpc with ⟨t, rfl⟩
    have h1 : p ^ (e + 1) ∣ B + 1 := ⟨t, by rw [hc, pow_succ]; ring⟩
    have h2 : e + 1 ≤ padicValNat p (B + 1) := (padicValNat_dvd_iff_le (by omega)).mp h1
    omega
  obtain ⟨A0, hA0⟩ := hA
  have hstep : (B + 1) * (A - 1).choose (B + 1) = (A - (B + 1)) * (A - 1).choose B := by
    have h := Nat.choose_succ_right_eq (A - 1) B
    have hsub : A - 1 - B = A - (B + 1) := by omega
    rw [hsub] at h
    linarith
  have hsum_nat : (B + 1) * ((A - 1).choose (B + 1) + (A - 1).choose B) = A * (A - 1).choose B := by
    have hsub : A - (B + 1) + (B + 1) = A := Nat.sub_add_cancel (le_of_lt hBA)
    calc (B + 1) * ((A - 1).choose (B + 1) + (A - 1).choose B)
        = (B + 1) * (A - 1).choose (B + 1) + (B + 1) * (A - 1).choose B := by ring
      _ = (A - (B + 1)) * (A - 1).choose B + (B + 1) * (A - 1).choose B := by rw [hstep]
      _ = (A - (B + 1) + (B + 1)) * (A - 1).choose B := by ring
      _ = A * (A - 1).choose B := by rw [hsub]
  have hAe : A = p ^ e * (p ^ (r - 1 - e) * A0) := by
    rw [hA0, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
  have hcancel : c * ((A - 1).choose (B + 1) + (A - 1).choose B) =
      (p ^ (r - 1 - e) * A0) * (A - 1).choose B := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos e)
    calc p ^ e * (c * ((A - 1).choose (B + 1) + (A - 1).choose B))
        = (p ^ e * c) * ((A - 1).choose (B + 1) + (A - 1).choose B) := by ring
      _ = (B + 1) * ((A - 1).choose (B + 1) + (A - 1).choose B) := by rw [← hc]
      _ = A * (A - 1).choose B := hsum_nat
      _ = p ^ e * ((p ^ (r - 1 - e) * A0) * (A - 1).choose B) := by rw [hAe]; ring
  have hZ : (c : ℤ) * ((((A - 1).choose (B + 1) : ℕ) : ℤ) + (((A - 1).choose B : ℕ) : ℤ)) =
      (p : ℤ) ^ (r - 1 - e) * ((A0 : ℤ) * (((A - 1).choose B : ℕ) : ℤ)) := by
    have hZ0 : (c : ℤ) * ((((A - 1).choose (B + 1) + (A - 1).choose B : ℕ) : ℤ)) =
        (((p ^ (r - 1 - e) * A0 : ℕ) : ℤ)) * (((A - 1).choose B : ℕ) : ℤ) := by
      exact_mod_cast hcancel
    push_cast at hZ0
    linarith
  have hdvd : (p : ℤ) ^ (r - k) ∣ (c : ℤ) * ((((A - 1).choose (B + 1) : ℕ) : ℤ) + (((A - 1).choose B : ℕ) : ℤ)) := by
    rw [hZ]
    exact dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) (by omega : r - k ≤ r - 1 - e)) _
  have hcopZ : IsCoprime ((p : ℤ) ^ (r - k)) (c : ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr hcop_c).pow_left
  exact hcopZ.dvd_of_dvd_mul_left hdvd

lemma fw_block_const {p n r m k w : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hm : m < n)
    (hk1 : 1 ≤ k) (hkr : k < r) (hw : w < 2 * p ^ (r - 1)) :
    ((p : ZMod (p ^ r)) ^ (r - k)) ∣ fw p n r m w - fw p n r m ((w / p ^ k) * p ^ k) := by
  set q1 := p ^ (r - 1)
  have hstep : ∀ v < 2 * q1 - 1, ¬ p ^ k ∣ v + 1 →
      ((p : ZMod (p ^ r)) ^ (r - k)) ∣ fw p n r m (v + 1) - fw p n r m v := by
    intro v hv hnd
    have hpk_q1 : p ^ k ∣ q1 := pow_dvd_pow p (by omega)
    have hnd3 : ¬ p ^ k ∣ 2 * m * q1 + v + 1 := by
      intro hd
      have h1 : p ^ k ∣ 2 * m * q1 := dvd_mul_of_dvd_right hpk_q1 (2 * m)
      have h2 : 2 * m * q1 + v + 1 = 2 * m * q1 + (v + 1) := by omega
      exact hnd ((Nat.dvd_add_right h1).mp (h2 ▸ hd))
    have hc3 := choose_add_step_dvd (p := p) (r := r) (k := k) (A := 2 * n * q1) (B := 2 * m * q1 + v)
      hp hk1 hkr (dvd_mul_left q1 (2 * n)) hnd3
    have hc3_rew : 2 * n * q1 + (2 * m * q1 + v) + 1 = 2 * n * q1 + 2 * m * q1 + (v + 1) := by omega
    have hc3_rew2 : 2 * n * q1 + (2 * m * q1 + v) = 2 * n * q1 + 2 * m * q1 + v := by omega
    have hc3_rew3 : 2 * m * q1 + v + 1 = 2 * m * q1 + (v + 1) := by omega
    rw [hc3_rew, hc3_rew2, hc3_rew3] at hc3
    by_cases hpar : v % 2 = 0
    · have hdiv2 : (v + 1) / 2 = v / 2 := by omega
      simp only [fw, hdiv2]
      have hfac : (((n * q1 - 1).choose (m * q1 + v / 2) : ℕ) : ZMod (p ^ r)) *
          (((2 * n * q1 - 1).choose ((n + m) * q1 + v / 2) : ℕ) : ZMod (p ^ r)) *
          (((2 * n * q1 + 2 * m * q1 + (v + 1)).choose (2 * m * q1 + (v + 1)) : ℕ) : ZMod (p ^ r)) -
          (((n * q1 - 1).choose (m * q1 + v / 2) : ℕ) : ZMod (p ^ r)) *
          (((2 * n * q1 - 1).choose ((n + m) * q1 + v / 2) : ℕ) : ZMod (p ^ r)) *
          (((2 * n * q1 + 2 * m * q1 + v).choose (2 * m * q1 + v) : ℕ) : ZMod (p ^ r)) =
          (((n * q1 - 1).choose (m * q1 + v / 2) : ℕ) : ZMod (p ^ r)) *
          (((2 * n * q1 - 1).choose ((n + m) * q1 + v / 2) : ℕ) : ZMod (p ^ r)) *
          ((((2 * n * q1 + 2 * m * q1 + (v + 1)).choose (2 * m * q1 + (v + 1)) : ℕ) : ZMod (p ^ r)) -
           (((2 * n * q1 + 2 * m * q1 + v).choose (2 * m * q1 + v) : ℕ) : ZMod (p ^ r))) := by ring
      rw [hfac]
      exact dvd_mul_of_dvd_right hc3 _
    · set u := v / 2
      have hv_eq : v + 1 = 2 * (u + 1) := by omega
      have hdiv2 : (v + 1) / 2 = u + 1 := by omega
      have hnd_u : ¬ p ^ k ∣ u + 1 := by
        intro hd
        exact hnd (hv_eq ▸ dvd_mul_of_dvd_right hd 2)
      have hnd1 : ¬ p ^ k ∣ m * q1 + u + 1 := by
        intro hd
        have h1 : p ^ k ∣ m * q1 := dvd_mul_of_dvd_right hpk_q1 m
        have h2 : m * q1 + u + 1 = m * q1 + (u + 1) := by omega
        exact hnd_u ((Nat.dvd_add_right h1).mp (h2 ▸ hd))
      have hnd2 : ¬ p ^ k ∣ (n + m) * q1 + u + 1 := by
        intro hd
        have h1 : p ^ k ∣ (n + m) * q1 := dvd_mul_of_dvd_right hpk_q1 (n + m)
        have h2 : (n + m) * q1 + u + 1 = (n + m) * q1 + (u + 1) := by omega
        exact hnd_u ((Nat.dvd_add_right h1).mp (h2 ▸ hd))
      have hu_lt : u + 1 < q1 := by omega
      have hB1 : m * q1 + u + 1 < n * q1 := by nlinarith
      have hB2 : (n + m) * q1 + u + 1 < 2 * n * q1 := by nlinarith
      have hc1 := choose_sub_one_step_dvd (p := p) (r := r) (k := k) (A := n * q1) (B := m * q1 + u)
        hp hk1 hkr (dvd_mul_left q1 n) hB1 hnd1
      have hc2 := choose_sub_one_step_dvd (p := p) (r := r) (k := k) (A := 2 * n * q1) (B := (n + m) * q1 + u)
        hp hk1 hkr (dvd_mul_left q1 (2 * n)) hB2 hnd2
      simp only [fw, hdiv2]
      have h1a : m * q1 + (u + 1) = m * q1 + u + 1 := by omega
      have h2a : (n + m) * q1 + (u + 1) = (n + m) * q1 + u + 1 := by omega
      rw [h1a, h2a]
      set A1 : ZMod (p ^ r) := (((n * q1 - 1).choose (m * q1 + u + 1) : ℕ) : ZMod (p ^ r))
      set A0 : ZMod (p ^ r) := (((n * q1 - 1).choose (m * q1 + u) : ℕ) : ZMod (p ^ r))
      set B1 : ZMod (p ^ r) := (((2 * n * q1 - 1).choose ((n + m) * q1 + u + 1) : ℕ) : ZMod (p ^ r))
      set B0 : ZMod (p ^ r) := (((2 * n * q1 - 1).choose ((n + m) * q1 + u) : ℕ) : ZMod (p ^ r))
      set C1 : ZMod (p ^ r) := (((2 * n * q1 + 2 * m * q1 + (v + 1)).choose (2 * m * q1 + (v + 1)) : ℕ) : ZMod (p ^ r))
      set C0 : ZMod (p ^ r) := (((2 * n * q1 + 2 * m * q1 + v).choose (2 * m * q1 + v) : ℕ) : ZMod (p ^ r))
      have hid : A1 * B1 * C1 - A0 * B0 * C0 =
          ((A1 + A0) * B1 - A0 * (B1 + B0)) * C1 + A0 * B0 * (C1 - C0) := by ring
      rw [hid]
      exact dvd_add (dvd_mul_of_dvd_left (dvd_sub (dvd_mul_of_dvd_left hc1 B1) (dvd_mul_of_dvd_right hc2 A0)) C1)
        (dvd_mul_of_dvd_right hc3 (A0 * B0))
  set base := (w / p ^ k) * p ^ k
  set d := w % p ^ k
  have hpk_pos : 0 < p ^ k := pow_pos hp.pos k
  have hd_lt : d < p ^ k := Nat.mod_lt w hpk_pos
  have hw_eq : w = base + d := by
    have h := Nat.div_add_mod w (p ^ k)
    rw [mul_comm] at h
    exact h.symm
  have hbase_dvd : p ^ k ∣ base := dvd_mul_left (p ^ k) (w / p ^ k)
  have hgen : ∀ d' : ℕ, d' < p ^ k → base + d' < 2 * q1 →
      ((p : ZMod (p ^ r)) ^ (r - k)) ∣ fw p n r m (base + d') - fw p n r m base := by
    intro d'
    induction d' with
    | zero => intro _ _; simp
    | succ d' ih =>
      intro hd' hlt'
      have hsplit : fw p n r m (base + (d' + 1)) - fw p n r m base =
          (fw p n r m (base + d' + 1) - fw p n r m (base + d')) +
          (fw p n r m (base + d') - fw p n r m base) := by
        rw [show base + (d' + 1) = base + d' + 1 by omega]; ring
      rw [hsplit]
      have hnd : ¬ p ^ k ∣ (base + d') + 1 := by
        intro hdiv
        have h1 : p ^ k ∣ d' + 1 := by
          rw [show base + d' + 1 = base + (d' + 1) by omega] at hdiv
          exact (Nat.dvd_add_right hbase_dvd).mp hdiv
        exact Nat.not_dvd_of_pos_of_lt (by omega) hd' h1
      exact dvd_add (hstep (base + d') (by omega) hnd) (ih (by omega) (by omega))
  rw [hw_eq]
  exact hgen d hd_lt (by omega)

lemma Hval_block_dvd {p r k b : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hb : b < 2 * p ^ (r - k)) :
    ((p : ZMod (p ^ r)) ^ k) ∣ ∑ w ∈ Ico (b * p ^ (k - 1)) ((b + 1) * p ^ (k - 1)), Hval p r w := by
  have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  -- Use ZMod.castHom from ZMod (p^r) to ZMod (p^k)
  let φ : ZMod (p ^ r) →+* ZMod (p ^ k) := ZMod.castHom (pow_dvd_pow p hkr) (ZMod (p ^ k))
  suffices hφ0 : φ (∑ w ∈ Ico (b * p ^ (k - 1)) ((b + 1) * p ^ (k - 1)), Hval p r w) = 0 by
    set S := ∑ w ∈ Ico (b * p ^ (k - 1)) ((b + 1) * p ^ (k - 1)), Hval p r w
    have hval : (S.val : ZMod (p ^ k)) = 0 := by
      have h1 : φ (S.val : ZMod (p ^ r)) = (S.val : ZMod (p ^ k)) := map_natCast φ S.val
      rw [ZMod.natCast_zmod_val, hφ0] at h1
      exact h1.symm
    have hdvd : p ^ k ∣ S.val := (ZMod.natCast_eq_zero_iff S.val (p ^ k)).mp hval
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨(c : ZMod (p ^ r)), ?_⟩
    have hcast : (S.val : ZMod (p ^ r)) = (p : ZMod (p ^ r)) ^ k * (c : ZMod (p ^ r)) := by
      rw [hc, Nat.cast_mul, Nat.cast_pow]
    rwa [ZMod.natCast_zmod_val] at hcast
  rw [map_sum]
  -- Helper: φ maps ((t : ZMod (p^r)) ^ 2)⁻¹ to ((t : ZMod (p^k)) ^ 2)⁻¹ when p ∤ t
  have hφ_inv : ∀ t : ℕ, ¬ p ∣ t →
      φ (((t : ZMod (p ^ r)) ^ 2)⁻¹) = ((t : ZMod (p ^ k)) ^ 2)⁻¹ := by
    intro t ht
    have hcop_r : Nat.Coprime t (p ^ r) := ((hp.coprime_iff_not_dvd).mpr ht).symm.pow_right r
    have hcop_k : Nat.Coprime t (p ^ k) := ((hp.coprime_iff_not_dvd).mpr ht).symm.pow_right k
    have hu_r : IsUnit ((t : ZMod (p ^ r)) ^ 2) := ((ZMod.isUnit_iff_coprime t (p ^ r)).mpr hcop_r).pow 2
    have hu_k : IsUnit ((t : ZMod (p ^ k)) ^ 2) := ((ZMod.isUnit_iff_coprime t (p ^ k)).mpr hcop_k).pow 2
    have hmul_r : ((t : ZMod (p ^ r)) ^ 2) * ((t : ZMod (p ^ r)) ^ 2)⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hu_r
    have hmul_k := congrArg φ hmul_r
    rw [map_mul, map_pow, map_natCast, map_one] at hmul_k
    have hinv_k : ((t : ZMod (p ^ k)) ^ 2)⁻¹ * ((t : ZMod (p ^ k)) ^ 2) = 1 := by
      rw [mul_comm]; exact ZMod.mul_inv_of_unit _ hu_k
    calc φ (((t : ZMod (p ^ r)) ^ 2)⁻¹)
        = ((t : ZMod (p ^ k)) ^ 2)⁻¹ * (((t : ZMod (p ^ k)) ^ 2) * φ (((t : ZMod (p ^ r)) ^ 2)⁻¹)) := by
          rw [← mul_assoc, hinv_k, one_mul]
      _ = ((t : ZMod (p ^ k)) ^ 2)⁻¹ := by rw [hmul_k, mul_one]
  -- Convert each term φ (Hval p r w) into sum over v in ZMod (p^k)
  have hterm : ∀ w, φ (Hval p r w) =
      ∑ v ∈ (if w % 2 = 0 then Icc 1 ((p - 1) / 2) else Icc ((p + 1) / 2) (p - 1)),
        ((((w / 2) * p + v : ℕ) : ZMod (p ^ k)) ^ 2)⁻¹ := by
    intro w
    simp only [Hval, map_sum]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have hv' : 1 ≤ v ∧ v < p := by
      split_ifs at hv <;> simp only [Finset.mem_Icc] at hv <;> omega
    have hnd : ¬ p ∣ (w / 2) * p + v := by
      intro hd
      exact Nat.not_dvd_of_pos_of_lt hv'.1 hv'.2 ((Nat.dvd_add_right (dvd_mul_left p (w / 2))).mp hd)
    exact hφ_inv ((w / 2) * p + v) hnd
  rw [Finset.sum_congr rfl (fun w _ => hterm w)]
  -- Now compare with half_block_inv_sq_zero!
  have hodd_p : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hodd_pk1 : p ^ (k - 1) % 2 = 1 := Nat.odd_iff.mp ((Nat.odd_iff.mpr hodd_p).pow)
  have hodd_pk : p ^ k % 2 = 1 := Nat.odd_iff.mp ((Nat.odd_iff.mpr hodd_p).pow)
  have hpk_eq : p ^ k = p ^ (k - 1) * p := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
  set pk := p ^ k
  set pk1 := p ^ (k - 1)
  set c := b / 2
  have hhalf_eq : (pk + 1) / 2 = (pk1 - 1) / 2 * p + (p + 1) / 2 := by
    have h1 : 2 * ((pk + 1) / 2) = pk + 1 := by omega
    have h2 : 2 * ((pk1 - 1) / 2) = pk1 - 1 := by omega
    have h3 : 2 * ((p + 1) / 2) = p + 1 := by omega
    have hpk1_pos : 1 ≤ pk1 := pow_pos hp.pos _
    have hsub : (pk1 - 1) + 1 = pk1 := Nat.sub_add_cancel hpk1_pos
    have hmul : (pk1 - 1) * p + p = pk := by
      calc (pk1 - 1) * p + p = ((pk1 - 1) + 1) * p := by ring
        _ = pk1 * p := by rw [hsub]
        _ = pk := hpk_eq.symm
    have hmul2 : 2 * ((pk1 - 1) / 2 * p) = (pk1 - 1) * p := by
      calc 2 * ((pk1 - 1) / 2 * p) = (2 * ((pk1 - 1) / 2)) * p := by ring
        _ = (pk1 - 1) * p := by rw [h2]
    omega
  -- Biject sigma sum over (w, v) onto filtered interval of s ∈ ZMod pk
  have hsigma : ∀ (S : Finset ℕ) (f : ℕ → Finset ℕ) (g : ℕ → ℕ → ZMod pk),
      ∑ w ∈ S, ∑ v ∈ f w, g w v = ∑ x ∈ S.sigma f, g x.1 x.2 := fun S f g =>
    (Finset.sum_sigma S f (fun x => g x.1 x.2)).symm
  rw [hsigma]
  let idx := (Ico (b * pk1) ((b + 1) * pk1)).sigma
    (fun w => if w % 2 = 0 then Icc 1 ((p - 1) / 2) else Icc ((p + 1) / 2) (p - 1))
  have hcpk_eq : c * pk = (c * pk1) * p := by rw [hpk_eq]; ring
  have hcpk1_eq : (c + 1) * pk = ((c + 1) * pk1) * p := by rw [hpk_eq]; ring
  have hcpk_half : c * pk + (pk + 1) / 2 = (c * pk1 + (pk1 - 1) / 2) * p + (p + 1) / 2 := by
    rw [hhalf_eq, hcpk_eq]; ring
  have hmul_le : ∀ a b' : ℕ, a ≤ b' → a * p ≤ b' * p := fun a b' h => Nat.mul_le_mul_right p h
  have hmul_lt : ∀ a b' : ℕ, a < b' → a * p + p ≤ b' * p := fun a b' h => by
    calc a * p + p = (a + 1) * p := by ring
      _ ≤ b' * p := Nat.mul_le_mul_right p h
  have hlt_of_mul_add : ∀ a b' r : ℕ, a * p + r < b' * p → a < b' := fun a b' r h =>
    Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt (Nat.le_add_right _ _) h)
  have hle_of_mul_add : ∀ a b' r : ℕ, b' * p ≤ a * p + r → r < p → b' ≤ a := fun a b' r h hr' => by
    have hlt : b' * p < (a + 1) * p := by
      have : (a + 1) * p = a * p + p := by ring
      omega
    exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right hlt)
  have hpk1_2 : 2 * ((pk1 - 1) / 2) + 1 = pk1 := by
    have : 1 ≤ pk1 := pow_pos hp.pos _; omega
  by_cases hb_even : b % 2 = 0
  · have hb_eq : b = 2 * c := by omega
    have hbpk1 : b * pk1 = 2 * (c * pk1) := by rw [hb_eq]; ring
    have hb1pk1 : (b + 1) * pk1 = 2 * (c * pk1) + pk1 := by rw [hb_eq]; ring
    have hbij : ∑ x ∈ idx, ((((x.1 / 2) * p + x.2 : ℕ) : ZMod pk) ^ 2)⁻¹ =
        ∑ s ∈ (Ico 1 ((pk + 1) / 2)).filter (fun s => ¬ p ∣ s), ((s : ZMod pk) ^ 2)⁻¹ := by
      refine Finset.sum_bij (fun x _ => (x.1 / 2) * p + x.2 - c * pk) ?_ ?_ ?_ ?_
      · intro x hx
        rcases Finset.mem_sigma.mp hx with ⟨hw, hv⟩
        simp only [Finset.mem_Ico] at hw
        have hlo : c * pk + 1 ≤ (x.1 / 2) * p + x.2 := by
          have h1 : c * pk ≤ (x.1 / 2) * p := hcpk_eq ▸ hmul_le _ _ (by omega)
          have hv1 : 1 ≤ x.2 := by split_ifs at hv <;> simp only [Finset.mem_Icc] at hv <;> omega
          omega
        have hhi : (x.1 / 2) * p + x.2 < c * pk + (pk + 1) / 2 := by
          rw [hcpk_half]
          by_cases hpar : x.1 % 2 = 0
          · rw [if_pos hpar] at hv; simp only [Finset.mem_Icc] at hv
            have h1 : (x.1 / 2) * p ≤ (c * pk1 + (pk1 - 1) / 2) * p := hmul_le _ _ (by omega)
            omega
          · rw [if_neg hpar] at hv; simp only [Finset.mem_Icc] at hv
            have h1 : (x.1 / 2) * p + p ≤ (c * pk1 + (pk1 - 1) / 2) * p := hmul_lt _ _ (by omega)
            omega
        have hv_bnd : 1 ≤ x.2 ∧ x.2 < p := by
          split_ifs at hv <;> simp only [Finset.mem_Icc] at hv <;> omega
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
        intro hd
        have hcpk : p ∣ c * pk := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) c
        have hadd : p ∣ ((x.1 / 2) * p + x.2 - c * pk) + c * pk := dvd_add hd hcpk
        rw [Nat.sub_add_cancel (by omega)] at hadd
        exact Nat.not_dvd_of_pos_of_lt hv_bnd.1 hv_bnd.2 ((Nat.dvd_add_right (dvd_mul_left p _)).mp hadd)
      · intro x1 hx1 x2 hx2 heq
        rcases Finset.mem_sigma.mp hx1 with ⟨hw1, hv1⟩
        rcases Finset.mem_sigma.mp hx2 with ⟨hw2, hv2⟩
        simp only [Finset.mem_Ico] at hw1 hw2
        have h1 : 1 ≤ x1.2 ∧ x1.2 < p := by split_ifs at hv1 <;> simp only [Finset.mem_Icc] at hv1 <;> omega
        have h2 : 1 ≤ x2.2 ∧ x2.2 < p := by split_ifs at hv2 <;> simp only [Finset.mem_Icc] at hv2 <;> omega
        have hge1 : c * pk ≤ (x1.1 / 2) * p + x1.2 := by
          have := hcpk_eq ▸ hmul_le (c * pk1) (x1.1 / 2) (by omega); omega
        have hge2 : c * pk ≤ (x2.1 / 2) * p + x2.2 := by
          have := hcpk_eq ▸ hmul_le (c * pk1) (x2.1 / 2) (by omega); omega
        have ht_eq : (x1.1 / 2) * p + x1.2 = (x2.1 / 2) * p + x2.2 := by omega
        have hx2_eq : x1.2 = x2.2 := by
          have := congrArg (· % p) ht_eq
          simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt h1.2, Nat.mod_eq_of_lt h2.2] at this
          exact this
        have hq_eq : x1.1 / 2 = x2.1 / 2 :=
          Nat.eq_of_mul_eq_mul_right hp.pos (by omega)
        have hpar_eq : x1.1 % 2 = x2.1 % 2 := by
          by_cases hp1 : x1.1 % 2 = 0 <;> by_cases hp2 : x2.1 % 2 = 0
          · omega
          · rw [if_pos hp1] at hv1; rw [if_neg hp2] at hv2
            simp only [Finset.mem_Icc] at hv1 hv2; omega
          · rw [if_neg hp1] at hv1; rw [if_pos hp2] at hv2
            simp only [Finset.mem_Icc] at hv1 hv2; omega
          · omega
        have hx1_eq : x1.1 = x2.1 := by omega
        cases x1; cases x2; simp only at hx1_eq hx2_eq; subst hx1_eq; subst hx2_eq; rfl
      · intro s hs
        simp only [Finset.mem_filter, Finset.mem_Ico] at hs
        set t := c * pk + s
        set u := t / p
        set v := t % p
        have hv_lt : v < p := Nat.mod_lt t hp.pos
        have hv_pos : 1 ≤ v := by
          rcases Nat.eq_zero_or_pos v with hv0 | hpos
          · have hpt : p ∣ t := Nat.dvd_of_mod_eq_zero hv0
            have hcpk : p ∣ c * pk := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) c
            exact absurd ((Nat.dvd_add_right hcpk).mp hpt) hs.2
          · exact hpos
        have ht_eq : u * p + v = t := by
          have h := Nat.div_add_mod t p; rw [mul_comm] at h; exact h
        set eps := if 2 * v < p then 0 else 1
        set w := 2 * u + eps
        have hw_div : w / 2 = u := by simp only [w, eps]; split_ifs <;> omega
        have hw_mod : w % 2 = eps := by simp only [w, eps]; split_ifs <;> omega
        have hmem_w : w ∈ Ico (b * pk1) ((b + 1) * pk1) := by
          rw [Finset.mem_Ico]
          constructor
          · have hu_ge : c * pk1 ≤ u := hle_of_mul_add u (c * pk1) v (by rw [← hcpk_eq, ht_eq]; omega) hv_lt
            omega
          · have ht_lt : u * p + v < (c * pk1 + (pk1 - 1) / 2) * p + (p + 1) / 2 := by
              rw [ht_eq, ← hcpk_half]; omega
            by_cases hlt : 2 * v < p
            · have heps : eps = 0 := if_pos hlt
              have hu_le : u ≤ c * pk1 + (pk1 - 1) / 2 := by
                have : u * p < (c * pk1 + (pk1 - 1) / 2 + 1) * p := by
                  have hadd : (c * pk1 + (pk1 - 1) / 2 + 1) * p = (c * pk1 + (pk1 - 1) / 2) * p + p := by ring
                  omega
                exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right this)
              omega
            · have heps : eps = 1 := if_neg hlt
              have hu_lt : u < c * pk1 + (pk1 - 1) / 2 :=
                hlt_of_mul_add u (c * pk1 + (pk1 - 1) / 2) 0 (by omega)
              omega
        have hmem_v : v ∈ (if w % 2 = 0 then Icc 1 ((p - 1) / 2) else Icc ((p + 1) / 2) (p - 1)) := by
          rw [hw_mod]
          by_cases hlt : 2 * v < p
          · have heps : eps = 0 := if_pos hlt
            rw [heps]; simp only [↓reduceIte, Finset.mem_Icc]; omega
          · have heps : eps = 1 := if_neg hlt
            rw [heps]; simp only [one_ne_zero, ↓reduceIte, Finset.mem_Icc]; omega
        refine ⟨⟨w, v⟩, Finset.mem_sigma.mpr ⟨hmem_w, hmem_v⟩, ?_⟩
        simp only [hw_div, ht_eq, t]
        omega
      · intro x hx
        rcases Finset.mem_sigma.mp hx with ⟨hw, hv⟩
        simp only [Finset.mem_Ico] at hw
        have hge : c * pk ≤ (x.1 / 2) * p + x.2 := by
          have := hcpk_eq ▸ hmul_le (c * pk1) (x.1 / 2) (by omega); omega
        have hcast : (((x.1 / 2) * p + x.2 : ℕ) : ZMod pk) =
            ((((x.1 / 2) * p + x.2 - c * pk : ℕ) : ZMod pk)) := by
          have h1 : ((x.1 / 2) * p + x.2) = ((x.1 / 2) * p + x.2 - c * pk) + c * pk :=
            (Nat.sub_add_cancel hge).symm
          conv_lhs => rw [h1, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero]
        rw [hcast]
    rw [hbij]
    exact (half_block_inv_sq_zero hp hp5 hk1).1
  · have hb_eq : b = 2 * c + 1 := by omega
    have hbpk1 : b * pk1 = 2 * (c * pk1) + pk1 := by rw [hb_eq]; ring
    have hb1pk1 : (b + 1) * pk1 = 2 * ((c + 1) * pk1) := by rw [hb_eq]; ring
    have hbij : ∑ x ∈ idx, ((((x.1 / 2) * p + x.2 : ℕ) : ZMod pk) ^ 2)⁻¹ =
        ∑ s ∈ (Ico ((pk + 1) / 2) pk).filter (fun s => ¬ p ∣ s), ((s : ZMod pk) ^ 2)⁻¹ := by
      refine Finset.sum_bij (fun x _ => (x.1 / 2) * p + x.2 - c * pk) ?_ ?_ ?_ ?_
      · intro x hx
        rcases Finset.mem_sigma.mp hx with ⟨hw, hv⟩
        simp only [Finset.mem_Ico] at hw
        have hlo : c * pk + (pk + 1) / 2 ≤ (x.1 / 2) * p + x.2 := by
          rw [hcpk_half]
          by_cases hpar : x.1 % 2 = 0
          · rw [if_pos hpar] at hv; simp only [Finset.mem_Icc] at hv
            have h1 : (c * pk1 + (pk1 - 1) / 2) * p + p ≤ (x.1 / 2) * p := hmul_lt _ _ (by omega)
            omega
          · rw [if_neg hpar] at hv; simp only [Finset.mem_Icc] at hv
            have h1 : (c * pk1 + (pk1 - 1) / 2) * p ≤ (x.1 / 2) * p := hmul_le _ _ (by omega)
            omega
        have hhi : (x.1 / 2) * p + x.2 < c * pk + pk := by
          have h1 : (x.1 / 2) * p + p ≤ ((c + 1) * pk1) * p := hmul_lt _ _ (by omega)
          have hv_lt : x.2 < p := by split_ifs at hv <;> simp only [Finset.mem_Icc] at hv <;> omega
          have h2 : c * pk + pk = (c + 1) * pk := by ring
          rw [h2, hcpk1_eq]; omega
        have hv_bnd : 1 ≤ x.2 ∧ x.2 < p := by
          split_ifs at hv <;> simp only [Finset.mem_Icc] at hv <;> omega
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
        intro hd
        have hcpk : p ∣ c * pk := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) c
        have hadd : p ∣ ((x.1 / 2) * p + x.2 - c * pk) + c * pk := dvd_add hd hcpk
        rw [Nat.sub_add_cancel (by omega)] at hadd
        exact Nat.not_dvd_of_pos_of_lt hv_bnd.1 hv_bnd.2 ((Nat.dvd_add_right (dvd_mul_left p _)).mp hadd)
      · intro x1 hx1 x2 hx2 heq
        rcases Finset.mem_sigma.mp hx1 with ⟨hw1, hv1⟩
        rcases Finset.mem_sigma.mp hx2 with ⟨hw2, hv2⟩
        simp only [Finset.mem_Ico] at hw1 hw2
        have h1 : 1 ≤ x1.2 ∧ x1.2 < p := by split_ifs at hv1 <;> simp only [Finset.mem_Icc] at hv1 <;> omega
        have h2 : 1 ≤ x2.2 ∧ x2.2 < p := by split_ifs at hv2 <;> simp only [Finset.mem_Icc] at hv2 <;> omega
        have hge1 : c * pk ≤ (x1.1 / 2) * p + x1.2 := by
          have := hcpk_eq ▸ hmul_le (c * pk1) (x1.1 / 2) (by omega); omega
        have hge2 : c * pk ≤ (x2.1 / 2) * p + x2.2 := by
          have := hcpk_eq ▸ hmul_le (c * pk1) (x2.1 / 2) (by omega); omega
        have ht_eq : (x1.1 / 2) * p + x1.2 = (x2.1 / 2) * p + x2.2 := by omega
        have hx2_eq : x1.2 = x2.2 := by
          have := congrArg (· % p) ht_eq
          simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt h1.2, Nat.mod_eq_of_lt h2.2] at this
          exact this
        have hq_eq : x1.1 / 2 = x2.1 / 2 :=
          Nat.eq_of_mul_eq_mul_right hp.pos (by omega)
        have hpar_eq : x1.1 % 2 = x2.1 % 2 := by
          by_cases hp1 : x1.1 % 2 = 0 <;> by_cases hp2 : x2.1 % 2 = 0
          · omega
          · rw [if_pos hp1] at hv1; rw [if_neg hp2] at hv2
            simp only [Finset.mem_Icc] at hv1 hv2; omega
          · rw [if_neg hp1] at hv1; rw [if_pos hp2] at hv2
            simp only [Finset.mem_Icc] at hv1 hv2; omega
          · omega
        have hx1_eq : x1.1 = x2.1 := by omega
        cases x1; cases x2; simp only at hx1_eq hx2_eq; subst hx1_eq; subst hx2_eq; rfl
      · intro s hs
        simp only [Finset.mem_filter, Finset.mem_Ico] at hs
        set t := c * pk + s
        set u := t / p
        set v := t % p
        have hv_lt : v < p := Nat.mod_lt t hp.pos
        have hv_pos : 1 ≤ v := by
          rcases Nat.eq_zero_or_pos v with hv0 | hpos
          · have hpt : p ∣ t := Nat.dvd_of_mod_eq_zero hv0
            have hcpk : p ∣ c * pk := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) c
            exact absurd ((Nat.dvd_add_right hcpk).mp hpt) hs.2
          · exact hpos
        have ht_eq : u * p + v = t := by
          have h := Nat.div_add_mod t p; rw [mul_comm] at h; exact h
        set eps := if 2 * v < p then 0 else 1
        set w := 2 * u + eps
        have hw_div : w / 2 = u := by simp only [w, eps]; split_ifs <;> omega
        have hw_mod : w % 2 = eps := by simp only [w, eps]; split_ifs <;> omega
        have hmem_w : w ∈ Ico (b * pk1) ((b + 1) * pk1) := by
          rw [Finset.mem_Ico]
          have ht_ge : (c * pk1 + (pk1 - 1) / 2) * p + (p + 1) / 2 ≤ u * p + v := by
            rw [ht_eq, ← hcpk_half]; omega
          constructor
          · by_cases hlt : 2 * v < p
            · have heps : eps = 0 := if_pos hlt
              have hu_gt : c * pk1 + (pk1 - 1) / 2 < u :=
                hlt_of_mul_add (c * pk1 + (pk1 - 1) / 2) u 0 (by omega)
              omega
            · have heps : eps = 1 := if_neg hlt
              have hu_ge : c * pk1 + (pk1 - 1) / 2 ≤ u :=
                hle_of_mul_add u (c * pk1 + (pk1 - 1) / 2) v (by omega) hv_lt
              omega
          · have ht_lt : u * p + v < ((c + 1) * pk1) * p := by
              rw [ht_eq, ← hcpk1_eq]
              have : (c + 1) * pk = c * pk + pk := by ring
              omega
            have hu_lt : u < (c + 1) * pk1 := hlt_of_mul_add u ((c + 1) * pk1) v ht_lt
            omega
        have hmem_v : v ∈ (if w % 2 = 0 then Icc 1 ((p - 1) / 2) else Icc ((p + 1) / 2) (p - 1)) := by
          rw [hw_mod]
          by_cases hlt : 2 * v < p
          · have heps : eps = 0 := if_pos hlt
            rw [heps]; simp only [↓reduceIte, Finset.mem_Icc]; omega
          · have heps : eps = 1 := if_neg hlt
            rw [heps]; simp only [one_ne_zero, ↓reduceIte, Finset.mem_Icc]; omega
        refine ⟨⟨w, v⟩, Finset.mem_sigma.mpr ⟨hmem_w, hmem_v⟩, ?_⟩
        simp only [hw_div, ht_eq, t]
        omega
      · intro x hx
        rcases Finset.mem_sigma.mp hx with ⟨hw, hv⟩
        simp only [Finset.mem_Ico] at hw
        have hge : c * pk ≤ (x.1 / 2) * p + x.2 := by
          have := hcpk_eq ▸ hmul_le (c * pk1) (x.1 / 2) (by omega); omega
        have hcast : (((x.1 / 2) * p + x.2 : ℕ) : ZMod pk) =
            ((((x.1 / 2) * p + x.2 - c * pk : ℕ) : ZMod pk)) := by
          have h1 : ((x.1 / 2) * p + x.2) = ((x.1 / 2) * p + x.2 - c * pk) + c * pk :=
            (Nat.sub_add_cancel hge).symm
          conv_lhs => rw [h1, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero]
        rw [hcast]
    rw [hbij]
    exact (half_block_inv_sq_zero hp hp5 hk1).2

/-- Part 4 main result: for every `0 ≤ m < n`, the non-divisible block sum vanishes mod `p^(3*r)`. -/
lemma nondiv_block_zero {p n r m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) (hm : m < n) :
    let q := p ^ r
    ((p : ℤ) ^ (3 * r)) ∣
      ∑ t ∈ (Ico 1 q).filter (fun t => ¬ p ∣ t),
        (((n * q).choose (m * q + t) * (2 * n * q).choose (n * q + (m * q + t)) *
          (2 * n * q + 2 * (m * q + t)).choose (2 * (m * q + t)) : ℕ) : ℤ) := by
  have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  intro q
  set q1 := p ^ (r - 1)
  have hq : q = q1 * p := by
    simp only [q, q1]; conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
  let S : ℕ → ℕ := fun t =>
    (n * q).choose (m * q + t) * (2 * n * q).choose (n * q + (m * q + t)) *
      (2 * n * q + 2 * (m * q + t)).choose (2 * (m * q + t))
  have hterm : ∀ t ∈ (Ico 1 q).filter (fun t => ¬ p ∣ t),
      q ^ 2 ∣ S t ∧
      ((S t / q ^ 2 : ℕ) : ZMod q) =
        2 * (n : ZMod q) ^ 2 * ((t : ZMod q) ^ 2)⁻¹ *
          fw p n r m (2 * (t / p) + (if 2 * (t % p) < p then 0 else 1)) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_Ico] at ht
    exact nondiv_term_div_q2_mod hp hp5 hr hm ht.1.1 ht.1.2 ht.2
  -- Factor out q^2 from the sum
  have hfactor : ∑ t ∈ (Ico 1 q).filter (fun t => ¬ p ∣ t), (S t : ℤ) =
      (q : ℤ) ^ 2 * ((∑ t ∈ (Ico 1 q).filter (fun t => ¬ p ∣ t), S t / q ^ 2 : ℕ) : ℤ) := by
    rw [Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have hd := (hterm t ht).1
    have := Nat.mul_div_cancel' hd
    exact_mod_cast this.symm
  rw [hfactor]
  have h3r : (p : ℤ) ^ (3 * r) = (q : ℤ) ^ 2 * (q : ℤ) := by
    simp only [q]
    push_cast
    rw [← pow_mul, ← pow_add]
    congr 1; omega
  rw [h3r]
  refine mul_dvd_mul_left ((q : ℤ) ^ 2) ?_
  -- Show q ∣ ∑ S t / q^2 in ℕ, i.e. it is 0 in ZMod q
  suffices hzero : ((∑ t ∈ (Ico 1 q).filter (fun t => ¬ p ∣ t), S t / q ^ 2 : ℕ) : ZMod q) = 0 by
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ q).mp hzero
  rw [Nat.cast_sum]
  rw [Finset.sum_congr rfl (fun t ht => (hterm t ht).2)]
  -- Factor out 2 * n^2 and group by w ∈ range (2 * q1)
  have hgroup : ∑ t ∈ (Ico 1 q).filter (fun t => ¬ p ∣ t),
      2 * (n : ZMod q) ^ 2 * ((t : ZMod q) ^ 2)⁻¹ *
        fw p n r m (2 * (t / p) + (if 2 * (t % p) < p then 0 else 1)) =
      2 * (n : ZMod q) ^ 2 * ∑ w ∈ range (2 * q1), fw p n r m w * Hval p r w := by
    rw [Finset.mul_sum]
    let F : ℕ → ℕ → ZMod q := fun w v =>
      2 * (n : ZMod q) ^ 2 * ((((w / 2) * p + v : ℕ) : ZMod q) ^ 2)⁻¹ * fw p n r m w
    let Iv : ℕ → Finset ℕ := fun w =>
      if w % 2 = 0 then Icc 1 ((p - 1) / 2) else Icc ((p + 1) / 2) (p - 1)
    have hrew : ∑ w ∈ range (2 * q1), 2 * (n : ZMod q) ^ 2 * (fw p n r m w * Hval p r w) =
        ∑ w ∈ range (2 * q1), ∑ v ∈ Iv w, F w v := by
      refine Finset.sum_congr rfl (fun w _ => ?_)
      simp only [Hval, Iv, F, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v _ => by ring)
    have hsigma2 : ∑ w ∈ range (2 * q1), ∑ v ∈ Iv w, F w v =
        ∑ x ∈ (range (2 * q1)).sigma Iv, F x.1 x.2 :=
      (Finset.sum_sigma (range (2 * q1)) Iv (fun x => F x.1 x.2)).symm
    rw [hrew, hsigma2]
    have hodd_p : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
    refine Finset.sum_bij (fun t _ =>
        ⟨2 * (t / p) + (if 2 * (t % p) < p then 0 else 1), t % p⟩) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_Ico] at ht
      have hv_lt : t % p < p := Nat.mod_lt t hp.pos
      have hv_pos : 1 ≤ t % p := by
        rcases Nat.eq_zero_or_pos (t % p) with h0 | hpos
        · exact absurd (Nat.dvd_of_mod_eq_zero h0) ht.2
        · exact hpos
      have hu_lt : t / p < q1 := by
        have hdiv := Nat.div_add_mod t p
        rw [mul_comm] at hdiv
        have : (t / p) * p < q1 * p := by rw [← hq]; omega
        exact Nat.lt_of_mul_lt_mul_right this
      refine Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
      · dsimp only; split_ifs <;> omega
      · dsimp only [Iv]
        by_cases hlt : 2 * (t % p) < p
        · rw [if_pos hlt]; simp only [Nat.add_zero, Nat.mul_mod_right, ↓reduceIte, Finset.mem_Icc]; omega
        · rw [if_neg hlt]
          have hodd2 : (2 * (t / p) + 1) % 2 = 1 := by omega
          rw [if_neg (by omega)]; simp only [Finset.mem_Icc]; omega
    · intro t1 ht1 t2 ht2 heq
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
      rcases heq with ⟨hw_eq, hv_eq⟩
      rw [hv_eq] at hw_eq
      have hu_eq : t1 / p = t2 / p := by omega
      have h1 := Nat.div_add_mod t1 p
      have h2 := Nat.div_add_mod t2 p
      rw [hu_eq, hv_eq] at h1
      omega
    · intro x hx
      rcases Finset.mem_sigma.mp hx with ⟨hw, hv⟩
      have hwlt : x.1 < 2 * q1 := Finset.mem_range.mp hw
      have hv_bnd : 1 ≤ x.2 ∧ x.2 < p := by
        simp only [Iv] at hv; split_ifs at hv <;> simp only [Finset.mem_Icc] at hv <;> omega
      set t := (x.1 / 2) * p + x.2
      have ht_mod : t % p = x.2 := by
        simp only [t, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hv_bnd.2]
      have ht_div : t / p = x.1 / 2 := by
        have : t = x.2 + (x.1 / 2) * p := by simp only [t]; ring
        rw [this, Nat.add_mul_div_right _ _ hp.pos, Nat.div_eq_of_lt hv_bnd.2, zero_add]
      have hnd : ¬ p ∣ t := by
        intro hd
        exact Nat.not_dvd_of_pos_of_lt hv_bnd.1 hv_bnd.2 ((Nat.dvd_add_right (dvd_mul_left p _)).mp hd)
      have ht_lt : t < q := by
        have h1 : (x.1 / 2 + 1) * p ≤ q1 * p := Nat.mul_le_mul_right p (by omega)
        have h2 : (x.1 / 2 + 1) * p = (x.1 / 2) * p + p := by ring
        rw [hq]; omega
      refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, ht_lt⟩, hnd⟩, ?_⟩
      ext
      · simp only [ht_div, ht_mod]
        simp only [Iv] at hv
        split_ifs at hv with hpar
        · simp only [Finset.mem_Icc] at hv
          rw [if_pos (by omega)]; omega
        · simp only [Finset.mem_Icc] at hv
          rw [if_neg (by omega)]; omega
      · simp only [ht_mod]; exact HEq.rfl
    · intro t _
      have hw_div : (2 * (t / p) + (if 2 * (t % p) < p then 0 else 1)) / 2 = t / p := by
        split_ifs <;> omega
      have ht_eq : (t / p) * p + t % p = t := by
        have h := Nat.div_add_mod t p; rw [mul_comm] at h; exact h
      simp only [F, hw_div, ht_eq]
  rw [hgroup]
  have htel : ∑ w ∈ range (2 * q1), fw p n r m w * Hval p r w = 0 :=
    telescope_block_sum hp hr (fw p n r m) (Hval p r)
      (fun k hk1 hkr b hb => Hval_block_dvd hp hp5 hk1 hkr hb)
      (fun k hk1 hkr w hw => fw_block_const hp hp5 hm hk1 hkr hw)
  rw [htel, mul_zero]

end OeisA363986Part4

theorem OMA.solution : type_of% @OMA.S_oeis_a363986.main := by
  intro p n r hp hp5 hn hr
  rw [Int.modEq_iff_dvd]
  rw [OeisA363986Proof.a_eq_S_sum, OeisA363986Proof.a_eq_S_sum]
  set q := p ^ r
  set N := n * q
  set M := n * p ^ (r - 1)
  have hNM : N = M * p := by
    simp only [N, M, q, mul_assoc, ← pow_succ]
    congr 2; omega
  let S : ℕ → ℕ → ℤ := fun K j =>
    ((K.choose j * (2 * K).choose (K + j) * (2 * K + 2 * j).choose (2 * j) : ℕ) : ℤ)
  have hsplit : ∑ j ∈ Finset.range (N + 1), S N j =
      (∑ j ∈ (Finset.range (N + 1)).filter (fun j => p ∣ j), S N j) +
      (∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ p ∣ j), S N j) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1)) (fun j => p ∣ j) (S N)).symm
  have hdiv_sum : ∑ j ∈ (Finset.range (N + 1)).filter (fun j => p ∣ j), S N j =
      ∑ j ∈ Finset.range (M + 1), S N (p * j) := by
    refine (Finset.sum_bij (fun j _ => p * j) ?_ ?_ ?_ ?_).symm
    · intro j hj
      have hjM : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, dvd_mul_right p j⟩
      have : p * j ≤ p * M := Nat.mul_le_mul_left p hjM
      rw [hNM, mul_comm M p]; omega
    · intro j1 _ j2 _ heq; exact Nat.eq_of_mul_eq_mul_left hp.pos heq
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨j, rfl⟩ := hk.2
      have hjM : j ≤ M := by
        have : p * j ≤ p * M := by rw [hNM, mul_comm M p] at hk; omega
        exact Nat.le_of_mul_le_mul_left this hp.pos
      exact ⟨j, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hjM), rfl⟩
    · intro _ _; rfl
  have hnondiv_sum : ∑ j ∈ (Finset.range (N + 1)).filter (fun j => ¬ p ∣ j), S N j =
      ∑ m ∈ Finset.range n, ∑ t ∈ (Finset.Ico 1 q).filter (fun t => ¬ p ∣ t), S N (m * q + t) := by
    rw [← Finset.sum_product']
    refine (Finset.sum_bij (fun mt _ => mt.1 * q + mt.2) ?_ ?_ ?_ ?_).symm
    · intro mt hmt
      rcases Finset.mem_product.mp hmt with ⟨hm, ht⟩
      have hmlt : mt.1 < n := Finset.mem_range.mp hm
      simp only [Finset.mem_filter, Finset.mem_Ico] at ht
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
      · have h1 : mt.1 * q + mt.2 < (mt.1 + 1) * q := by
          have : (mt.1 + 1) * q = mt.1 * q + q := by ring
          omega
        have h2 : (mt.1 + 1) * q ≤ n * q := Nat.mul_le_mul_right q hmlt
        omega
      · intro hd
        have hmq : p ∣ mt.1 * q := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) mt.1
        exact ht.2 ((Nat.dvd_add_right hmq).mp hd)
    · intro x1 hx1 x2 hx2 heq
      rcases Finset.mem_product.mp hx1 with ⟨_, ht1⟩
      rcases Finset.mem_product.mp hx2 with ⟨_, ht2⟩
      simp only [Finset.mem_filter, Finset.mem_Ico] at ht1 ht2
      have ht_eq : x1.2 = x2.2 := by
        have := congrArg (· % q) heq
        simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt ht1.1.2, Nat.mod_eq_of_lt ht2.1.2] at this
        exact this
      have hq_pos : 0 < q := pow_pos hp.pos r
      have hm_eq : x1.1 = x2.1 := Nat.eq_of_mul_eq_mul_right hq_pos (by omega)
      exact Prod.ext hm_eq ht_eq
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      have hq_pos : 0 < q := pow_pos hp.pos r
      have hk_lt_N : k < N := by
        by_contra hge
        have hkN : k = N := by omega
        have hpN : p ∣ N := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) n
        exact hk.2 (hkN ▸ hpN)
      set m := k / q
      set t := k % q
      have ht_lt : t < q := Nat.mod_lt k hq_pos
      have hk_eq : m * q + t = k := by have h := Nat.div_add_mod k q; rw [mul_comm] at h; exact h
      have hnd_t : ¬ p ∣ t := by
        intro hd
        have hmq : p ∣ m * q := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) m
        exact hk.2 (hk_eq ▸ dvd_add hmq hd)
      have ht_pos : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h0 | hpos
        · exact absurd (h0 ▸ dvd_zero p) hnd_t
        · exact hpos
      have hm_lt : m < n :=
        Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt (Nat.le_add_right _ t) (hk_eq.symm ▸ hk_lt_N))
      exact ⟨(m, t), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hm_lt,
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨ht_pos, ht_lt⟩, hnd_t⟩⟩, hk_eq⟩
    · intro _ _; rfl
  have h1 : ((p : ℤ) ^ (3 * r)) ∣
      (∑ j ∈ Finset.range (M + 1), S N (p * j)) - (∑ j ∈ Finset.range (M + 1), S M j) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum (fun j hj => ?_)
    exact OeisA363986Part23.div_term_congr hp hp5 hn hr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have h2 : ((p : ℤ) ^ (3 * r)) ∣
      ∑ m ∈ Finset.range n, ∑ t ∈ (Finset.Ico 1 q).filter (fun t => ¬ p ∣ t), S N (m * q + t) := by
    refine Finset.dvd_sum (fun m hm => ?_)
    simpa only [S, N, q, mul_assoc] using OeisA363986Part4.nondiv_block_zero hp hp5 hr (Finset.mem_range.mp hm)
  have htot : ((p : ℤ) ^ (3 * r)) ∣
      (∑ j ∈ Finset.range (N + 1), S N j) - (∑ j ∈ Finset.range (M + 1), S M j) := by
    rw [hsplit, hdiv_sum, hnondiv_sum]
    have hrew : (∑ j ∈ Finset.range (M + 1), S N (p * j)) +
        (∑ m ∈ Finset.range n, ∑ t ∈ (Finset.Ico 1 q).filter (fun t => ¬ p ∣ t), S N (m * q + t)) -
        (∑ j ∈ Finset.range (M + 1), S M j) =
        ((∑ j ∈ Finset.range (M + 1), S N (p * j)) - (∑ j ∈ Finset.range (M + 1), S M j)) +
        (∑ m ∈ Finset.range n, ∑ t ∈ (Finset.Ico 1 q).filter (fun t => ¬ p ∣ t), S N (m * q + t)) := by ring
    rw [hrew]
    exact dvd_add h1 h2
  rw [dvd_sub_comm]
  exact htot

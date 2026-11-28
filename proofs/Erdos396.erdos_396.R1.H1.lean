import OMAReductions.R_Erdos396_erdos_396_R1
import Mathlib

/-! Witnesses for `k ≤ 4`: `n = 1, 2, 2480, 8178, 45153`. The divisibility
`n (n - 1) ⋯ (n - k) ∣ C(2n, n)` is checked by evaluation, with the factorials computed
by binary splitting. -/

namespace OMA.Step_Erdos396_erdos_396_R1_H1

open Finset

/-- `lo * (lo + 1) * ⋯ * (lo + len - 1)`, one factor at a time. -/
def naive (lo : ℕ) : ℕ → ℕ
  | 0 => 1
  | len + 1 => naive lo len * (lo + len)

theorem naive_spec (lo : ℕ) : ∀ len : ℕ, naive lo len = ∏ i ∈ range len, (lo + i) := by
  intro len
  induction len with
  | zero => rfl
  | succ len ih => rw [naive, ih, prod_range_succ]

/-- The same product by binary splitting, with recursion depth at most `d`. -/
def rp : ℕ → ℕ → ℕ → ℕ
  | 0, lo, len => naive lo len
  | d + 1, lo, len =>
    if len ≤ 1 then naive lo len else rp d lo (len / 2) * rp d (lo + len / 2) (len - len / 2)

theorem rp_spec : ∀ d lo len : ℕ, rp d lo len = ∏ i ∈ range len, (lo + i) := by
  intro d
  induction d with
  | zero => intro lo len; exact naive_spec lo len
  | succ d ih =>
    intro lo len
    unfold rp
    split_ifs with h
    · exact naive_spec lo len
    · rw [ih, ih]
      conv_rhs => rw [show len = len / 2 + (len - len / 2) by omega, prod_range_add]
      congr 1
      refine prod_congr rfl fun i _ => ?_
      ring

theorem factorial_eq (n : ℕ) : Nat.factorial n = rp 40 1 n := by
  rw [rp_spec]
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.factorial_succ, ih, prod_range_succ]; ring

theorem centralBinom_eq (n : ℕ) :
    Nat.centralBinom n = rp 40 1 (2 * n) / (rp 40 1 n * rp 40 1 n) := by
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.choose_eq_factorial_div_factorial (by omega),
    show 2 * n - n = n by omega, factorial_eq, factorial_eq]

/-- The divisibility, computed. -/
def okB (n k : ℕ) : Bool :=
  rp 40 1 (2 * n) / (rp 40 1 n * rp 40 1 n) % Nat.descFactorial n (k + 1) == 0

theorem okB_spec {n k : ℕ} (h : okB n k = true) :
    Nat.descFactorial n (k + 1) ∣ Nat.centralBinom n := by
  rw [centralBinom_eq]
  exact Nat.dvd_of_mod_eq_zero (by simpa [okB] using h)

theorem ok0 : okB 1 0 = true := by decide +kernel
theorem ok1 : okB 2 1 = true := by decide +kernel
theorem ok2 : okB 2480 2 = true := by decide +kernel
theorem ok3 : okB 8178 3 = true := by decide +kernel
theorem ok4 : okB 45153 4 = true := by decide +kernel

theorem small (k : ℕ) (hk : k ≤ 4) : ∃ n : ℕ, Nat.descFactorial n (k + 1) ∣ Nat.centralBinom n := by
  interval_cases k
  · exact ⟨1, okB_spec ok0⟩
  · exact ⟨2, okB_spec ok1⟩
  · exact ⟨2480, okB_spec ok2⟩
  · exact ⟨8178, okB_spec ok3⟩
  · exact ⟨45153, okB_spec ok4⟩

end OMA.Step_Erdos396_erdos_396_R1_H1

theorem OMA.solution : OMA.R_Erdos396_erdos_396_R1.H1 :=
  OMA.Step_Erdos396_erdos_396_R1_H1.small

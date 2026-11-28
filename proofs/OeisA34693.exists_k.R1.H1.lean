import OMAReductions.R_OeisA34693_exists_k_R1
import Mathlib

-- Step OeisA34693.exists_k.R1.H1: hypothesis H1 of reduction OeisA34693.exists_k.R1
-- Finite check: for every 1 < n ≤ 2000 some k < min n 100 makes n * k + 1 prime (the largest
-- least k in this range is 44). Primality is certified by trial division, run by decide +kernel.

namespace OMA.A34693H1

/-- `noDivFrom p d fuel = true` means no `e ≥ d` with `e * e ≤ p` divides `p`
(`false` when the fuel runs out). -/
def noDivFrom (p : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | d, fuel + 1 => if p < d * d then true else (p % d != 0) && noDivFrom p (d + 1) fuel

lemma noDivFrom_spec (p : ℕ) : ∀ fuel d, noDivFrom p d fuel = true →
    ∀ e, d ≤ e → e * e ≤ p → ¬ e ∣ p := by
  intro fuel
  induction fuel with
  | zero => intro d h; simp [noDivFrom] at h
  | succ f ih =>
    intro d h e hde hep hdvd
    simp only [noDivFrom] at h
    split_ifs at h with hlt
    · have : d * d ≤ e * e := Nat.mul_le_mul hde hde
      omega
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      obtain ⟨hmod, hrest⟩ := h
      rcases Nat.eq_or_lt_of_le hde with rfl | hlt'
      · exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
      · exact ih (d + 1) hrest e hlt' hep hdvd

def isPrimeB (p : ℕ) : Bool := decide (2 ≤ p) && noDivFrom p 2 p

lemma isPrimeB_spec (p : ℕ) (h : isPrimeB p = true) : p.Prime := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hnd⟩ := h
  by_contra hnp
  have hm := Nat.minFac_sq_le_self (by omega) hnp
  have hmp := Nat.minFac_prime (show p ≠ 1 by omega)
  rw [sq] at hm
  exact noDivFrom_spec p p 2 hnd (Nat.minFac p) hmp.two_le hm (Nat.minFac_dvd p)

/-- `findK n k fuel = true` means some `k' ≥ k`, `k' < k + fuel`, `k' < n` makes
`n * k' + 1` pass the trial division. -/
def findK (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | k, fuel + 1 => (decide (k < n) && isPrimeB (n * k + 1)) || findK n (k + 1) fuel

lemma findK_spec (n : ℕ) : ∀ fuel k, findK n k fuel = true →
    ∃ j < n, (n * j + 1).Prime := by
  intro fuel
  induction fuel with
  | zero => intro k h; simp [findK] at h
  | succ f ih =>
    intro k h
    simp only [findK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨hk, hp⟩ | h
    · exact ⟨k, hk, isPrimeB_spec _ hp⟩
    · exact ih (k + 1) h

def cond (n : ℕ) : Bool := decide (n ≤ 1) || decide (2000 < n) || findK n 0 100

/-- `chk k lo` checks `cond` on `[lo, lo + 2 ^ k)` (binary splitting). -/
def chk : ℕ → ℕ → Bool
  | 0, lo => cond lo
  | k + 1, lo => chk k lo && chk k (lo + 2 ^ k)

lemma chk_spec : ∀ k lo, chk k lo = true → ∀ n, lo ≤ n → n < lo + 2 ^ k → cond n = true := by
  intro k
  induction k with
  | zero =>
    intro lo h n h1 h2
    simp only [pow_zero] at h2
    obtain rfl : n = lo := by omega
    simpa [chk] using h
  | succ k ih =>
    intro lo h n h1 h2
    simp only [chk, Bool.and_eq_true] at h
    by_cases hn : n < lo + 2 ^ k
    · exact ih lo h.1 n h1 hn
    · exact ih (lo + 2 ^ k) h.2 n (by omega) (by rw [pow_succ] at h2; omega)

theorem chk_ok : chk 11 0 = true := by decide +kernel

theorem h1 : ∀ n : ℕ, 1 < n → n ≤ 2000 → ∃ k < n, (n * k + 1).Prime := by
  intro n hn hle
  have hc := chk_spec 11 0 chk_ok n (Nat.zero_le n) (by norm_num; omega)
  have e1 : decide (n ≤ 1) = false := by simp; omega
  have e2 : decide (2000 < n) = false := by simp; omega
  simp only [cond, e1, e2, Bool.false_or] at hc
  exact findK_spec n 100 0 hc

end OMA.A34693H1

theorem OMA.solution : OMA.R_OeisA34693_exists_k_R1.H1 := OMA.A34693H1.h1

import OMAReductions.R_Selfridge_selfridge_conjecture_R1
import Mathlib

-- Step Selfridge.selfridge_conjecture.R1.H1: hypothesis H1 of reduction Selfridge.selfridge_conjecture.R1
-- Credit: @ivillar. Finite check: decide +kernel verifies that every odd p <= 10000 with p = 2, 3 (mod 5) and 2^(p-1) = 1 (mod p) passes trial division or is one of the pseudoprimes 1387, 2047, 3277, 4033, 7957; for those, norm_num (Nat.fib extension) shows F(p+1) is not 0 mod p.

/-! Step Selfridge.selfridge_conjecture.R1.H1. -/

namespace P8Selfridge

/-- Trial division: `noDivFrom p d fuel = true` means that no `e ≥ d` with `e * e ≤ p`
divides `p` (`false` when the fuel runs out). -/
def noDivFrom (p : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | d, fuel + 1 => if p < d * d then true else (p % d != 0) && noDivFrom p (d + 1) fuel

lemma noDivFrom_spec (p : ℕ) : ∀ fuel d, noDivFrom p d fuel = true →
    ∀ e, d ≤ e → e * e ≤ p → ¬ e ∣ p := by
  intro fuel
  induction fuel with
  | zero =>
    intro d h
    simp [noDivFrom] at h
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

/-- The odd base-2 Fermat pseudoprimes up to `10000` that are `≡ ±2 (mod 5)`. -/
def exc (p : ℕ) : Bool := p == 1387 || p == 2047 || p == 3277 || p == 4033 || p == 7957

def cond (p : ℕ) : Bool :=
  decide (10000 < p) || !(p % 2 == 1 && (p % 5 == 2 || p % 5 == 3) && 2 ^ (p - 1) % p == 1) ||
    isPrimeB p || exc p

/-- `chk k lo` checks `cond` on `[lo, lo + 2 ^ k)` (binary splitting). -/
def chk : ℕ → ℕ → Bool
  | 0, lo => cond lo
  | k + 1, lo => chk k lo && chk k (lo + 2 ^ k)

lemma chk_spec : ∀ k lo, chk k lo = true → ∀ p, lo ≤ p → p < lo + 2 ^ k → cond p = true := by
  intro k
  induction k with
  | zero =>
    intro lo h p h1 h2
    simp only [pow_zero] at h2
    obtain rfl : p = lo := by omega
    simpa [chk] using h
  | succ k ih =>
    intro lo h p h1 h2
    simp only [chk, Bool.and_eq_true] at h
    by_cases hp : p < lo + 2 ^ k
    · exact ih lo h.1 p h1 hp
    · exact ih (lo + 2 ^ k) h.2 p (by omega) (by rw [pow_succ] at h2; omega)

theorem chk_ok : chk 14 0 = true := by decide +kernel

lemma cond_imp (p : ℕ) (hc : cond p = true) (hp : p ≤ 10000) (h1 : p % 2 = 1)
    (h5 : p % 5 = 2 ∨ p % 5 = 3) (h2 : 2 ^ (p - 1) % p = 1) :
    isPrimeB p = true ∨ exc p = true := by
  unfold cond at hc
  have e1 : decide (10000 < p) = false := by simp; omega
  have e2 : (p % 2 == 1 && (p % 5 == 2 || p % 5 == 3) && 2 ^ (p - 1) % p == 1) = true := by
    rcases h5 with h | h <;> simp [h1, h2, h]
  rw [e1, e2] at hc
  simpa using hc

theorem selfridge_h1 : ∀ p : ℕ, p ≤ 10000 → Selfridge.IsSelfridge p → p.Prime := by
  intro p hp hS
  obtain ⟨hodd, hmod5, hpow, hfib⟩ := hS
  have h1 : p % 2 = 1 := Nat.odd_iff.mp hodd
  have h5 : p % 5 = 2 ∨ p % 5 = 3 := by
    unfold Nat.ModEq at hmod5
    omega
  have hp3 : 2 ≤ p := by omega
  have h2 : 2 ^ (p - 1) % p = 1 := by
    unfold Nat.ModEq at hpow
    rw [hpow]
    exact Nat.mod_eq_of_lt (by omega)
  have hc := chk_spec 14 0 chk_ok p (Nat.zero_le p) (by norm_num; omega)
  rcases cond_imp p hc hp h1 h5 h2 with hpr | hex
  · exact isPrimeB_spec p hpr
  · exfalso
    unfold Nat.ModEq at hfib
    simp only [exc, Bool.or_eq_true, beq_iff_eq] at hex
    rcases hex with (((rfl | rfl) | rfl) | rfl) | rfl <;> norm_num at hfib

end P8Selfridge

theorem OMA.solution : OMA.R_Selfridge_selfridge_conjecture_R1.H1 :=
  P8Selfridge.selfridge_h1

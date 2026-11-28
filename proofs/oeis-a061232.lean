import OMAStatements.S_oeis_a061232
import Mathlib

namespace A061232Proof
open OMA.S_oeis_a061232

private theorem first_counts : a 2 = 2 ∧ a 3 = 6 := by decide

/-! The floor observation in the OEIS entry suggests an alternative reading
with a(n+1)/a(n). Even its upper bound cannot hold at every index. -/

private abbrev ShiftedUpper := ∀ n : ℕ, 3 ≤ n → n < 2^48 → 3*a (n+1) ≤ (3*n+2)*a n

private theorem growth (h : ShiftedUpper) (n : ℕ) (hn : 3 ≤ n) (endpt : n ≤ 2^48) :
    a n ^ 4 * (n+1) ≤ 16 * n.factorial ^ 4 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [first_counts.2, Nat.factorial]
  | succ k hk ih =>
    have poly : (3*k+2)^4*(k+2) ≤ 81*(k+1)^5 := by ring_nf; omega
    have bound : 81*(a (k+1)^4*(k+2)) ≤ 81*(16*(k+1).factorial^4) := calc
      _ = (3*a (k+1))^4*(k+2) := by ring
      _ ≤ ((3*k+2)*a k)^4*(k+2) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (h k hk (by omega)) 4)
      _ = ((3*k+2)^4*(k+2))*a k^4 := by ring
      _ ≤ (81*(k+1)^5)*a k^4 := Nat.mul_le_mul_right _ poly
      _ = (81*(k+1)^4)*(a k^4*(k+1)) := by ring
      _ ≤ (81*(k+1)^4)*(16*k.factorial^4) := Nat.mul_le_mul_left _ (ih (by omega))
      _ = _ := by rw [Nat.factorial_succ]; ring
    exact Nat.le_of_mul_le_mul_left bound (by decide)

private theorem small_interval (h : ShiftedUpper) (n : ℕ) (hn : 2048^4 ≤ n+1) (endpt : n ≤ 2^48) :
    1024*a n ≤ n.factorial := by
  have inv := growth h n (by omega) endpt
  have p : (1024*a n)^4 ≤ n.factorial^4 := by
    have q := (Nat.mul_le_mul_left (a n^4) hn).trans inv
    rw [mul_pow]
    norm_num at q ⊢
    omega
  exact (Nat.pow_le_pow_iff_left (by decide : 4 ≠ 0)).mp p

private theorem cumulative (h : ShiftedUpper) (n : ℕ) (hn : 2048^4 ≤ n+1) (endpt : n+1 ≤ 2^48) :
    512*((n+2).factorial).primeCounting ≤ (n+1).factorial := by
  have h₁ := small_interval h n hn (by omega)
  have h₂ := small_interval h (n+1) (by omega) endpt
  have base : n.factorial.primeCounting ≤ n.factorial+1 := Nat.count_le Nat.Prime
  have eq (i : ℕ) : (i+1).factorial.primeCounting = i.factorial.primeCounting + a i := by
    unfold a
    have : i.factorial.primeCounting ≤ (i+1).factorial.primeCounting :=
      Nat.monotone_primeCounting (Nat.factorial_le (Nat.le_succ i))
    omega
  have wide : 4096*n.factorial ≤ (n+1).factorial := by
    rw [Nat.factorial_succ]
    exact Nat.mul_le_mul_right _ (by omega)
  have pos := n.factorial_pos
  rw [eq (n+1), eq n]
  omega

private theorem chebyshev_lower (m : ℕ) (hm : 32 ≤ m) :
    (m : ℝ) ≤ 4 * (m.primeCounting : ℝ) * Real.log m := by
  have large : (32 : ℝ) ≤ m := by exact_mod_cast hm
  have logpos : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have cheb := (div_le_iff₀ logpos).mp (Chebyshev.pi_ge m)
  have small := Real.log_le_sub_one_of_pos (x := ((m:ℝ)+1)/8) (by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at small
  have log8 : Real.log 8 ≤ 3 := by
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have half : (1/2 : ℝ) * m ≤ Real.log 2 * m :=
    mul_le_mul_of_nonneg_right (by linarith [Real.log_two_gt_d9]) (by positivity)
  nlinarith

private theorem contradict_at (h : ShiftedUpper) (n : ℕ) (hn : n+2 = 2^48) : False := by
  let m := (n+2).factorial
  have low := chebyshev_lower m (by dsimp [m]; exact (by omega : 32 ≤ n+2).trans (n+2).self_le_factorial)
  have upper : 512*(m.primeCounting : ℝ) ≤ (n+1).factorial := by
    exact_mod_cast cumulative h n (by norm_num at hn ⊢; omega) (by omega)
  have fac : (m : ℝ) = ((n:ℝ)+2)*(n+1).factorial := by
    dsimp [m]; rw [Nat.factorial_succ (n+1)]; push_cast; ring
  have logbound : Real.log (m:ℝ) ≤ ((n:ℝ)+2)*48 := by
    have bound : (m:ℝ) ≤ (((n+2:ℕ):ℝ)^(n+2)) := by exact_mod_cast (n+2).factorial_le_pow
    have logle := Real.log_le_log (by exact_mod_cast (n+2).factorial_pos : (0:ℝ) < m) bound
    rw [Real.log_pow] at logle
    have logN : Real.log ((n+2:ℕ):ℝ) ≤ 48 := by
      rw [hn, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9]
    have hmul := mul_le_mul_of_nonneg_left logN (by positivity : (0:ℝ) ≤ (n+2:ℕ))
    push_cast at logle hmul
    exact logle.trans hmul
  have cmp := low.trans (mul_le_mul_of_nonneg_left logbound (by positivity))
  rw [fac] at cmp
  have scaled := mul_le_mul_of_nonneg_left upper (by positivity : (0:ℝ) ≤ (n:ℝ)+2)
  have positive : (0:ℝ) < ((n:ℝ)+2)*(n+1).factorial := by positivity
  nlinarith only [cmp, scaled, positive]

private theorem count_pos (n : ℕ) (hn : 3 ≤ n) : 0 < a n := by
  obtain ⟨p, prime, lower, upper⟩ := Nat.exists_prime_lt_and_le_two_mul n.factorial n.factorial_ne_zero
  have bound : p ≤ (n+1).factorial := by
    rw [Nat.factorial_succ]
    exact upper.trans (Nat.mul_le_mul_right _ (by omega))
  unfold a
  apply Nat.sub_pos_of_lt
  exact (Nat.count_monotone Nat.Prime lower).trans_lt
    (Nat.count_strict_mono prime (Nat.lt_succ_of_le bound))

/-- Even with the alternative indexing, the claimed upper bound fails below 2^48. -/
theorem shifted_upper_fails : ∃ n : ℕ, 3 ≤ n ∧ n < 2^48 ∧
    (n : ℚ) + 2/3 < (a (n+1) : ℚ) / a n := by
  by_contra! h
  have upper : ShiftedUpper := by
    intro n hn endpt
    have hm := (div_le_iff₀ (by exact_mod_cast count_pos n hn : (0:ℚ) < a n)).mp (h n hn endpt)
    exact_mod_cast (show 3*(a (n+1):ℚ) ≤ (3*(n:ℚ)+2)*a n by linarith)
  exact contradict_at upper (2^48-2) (by norm_num)

end A061232Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a061232.main) := by
  intro claimed
  have lower := (claimed 3 (by decide)).1
  norm_num [A061232Proof.first_counts.1, A061232Proof.first_counts.2] at lower

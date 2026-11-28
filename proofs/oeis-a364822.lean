import OMAStatements.S_oeis_a364822
import Mathlib

/-!
# Proof of the two conjectures of OEIS A364822

`a(n) = n! * [x^n] F(x)` with `F = cosh(x) / (1 - 2*sinh(x))`.

Conjectures of the entry: `a(p) == 2 (mod p)` for every prime `p > 2`, and `a(2^m) == 1 (mod 2^m)`.

Proof.
1. The constant coefficient of `1 - 2*sinh` is `1`, so `F * (1 - 2*sinh) = cosh`, that is
   `F = cosh + 2 * (sinh * F)`.
2. Comparing coefficients of `x^n` and multiplying by `n!` (with `n! / (i! j!) = C(n,i)` for
   `i + j = n`) gives the recurrence
   `a(n) = [n even] + 2 * Sum_{i + j = n, i odd} C(n,i) * a(j)`.
3. By strong induction every `a(n)` is an integer (an odd `i` is positive, so `j < n`).
4. Key lemma: if `d` divides `C(n,i)` for every odd `i < n`, then `a(n)` is congruent modulo `d` to
   `1` when `n` is even and to `2` when `n` is odd. Indeed all terms with `i < n` vanish modulo `d`,
   and the term `i = n` is `0` for even `n` and `C(n,n) * a(0) = 1` for odd `n`.
5. For an odd prime `p`, `p` divides `C(p,i)` for `0 < i < p`. For `n = 2^m` and odd `i`,
   `i * C(n,i) = n * C(n-1,i-1)` and `gcd(n,i) = 1` give `n | C(n,i)`; `n` is even when `m > 0`,
   and for `m = 0` the modulus is `1`.
-/

namespace OMA.P_oeis_a364822

open Finset PowerSeries
open OMA.S_oeis_a364822

private lemma coeff_sinh (n : ℕ) :
    coeff n sinhSeries = if Even n then 0 else 1 / (n.factorial : ℚ) := by
  unfold sinhSeries
  exact coeff_mk n _

private lemma coeff_cosh (n : ℕ) :
    coeff n coshSeries = if Even n then 1 / (n.factorial : ℚ) else 0 := by
  unfold coshSeries
  exact coeff_mk n _

/-- Step 1: `F = cosh + 2 * (sinh * F)`. -/
private lemma egf_eq : egf = coshSeries + 2 * (sinhSeries * egf) := by
  have h0 : constantCoeff sinhSeries = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_sinh, if_pos Even.zero]
  have hc : constantCoeff (1 - 2 * sinhSeries : PowerSeries ℚ) ≠ 0 := by
    rw [map_sub, map_mul, map_one, h0, mul_zero, sub_zero]
    exact one_ne_zero
  have h : egf * (1 - 2 * sinhSeries) = coshSeries := by
    unfold egf
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hc, mul_one]
  linear_combination h

/-- Step 2: the recurrence. -/
private lemma a_rec (n : ℕ) :
    a n = (if Even n then 1 else 0) +
      2 * ∑ ij ∈ antidiagonal n, (if Even ij.1 then 0 else (n.choose ij.1 : ℚ) * a ij.2) := by
  have hfac : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have h1 : coeff n egf = coeff n coshSeries +
      2 * ∑ ij ∈ antidiagonal n, coeff ij.1 sinhSeries * coeff ij.2 egf := by
    have h : coeff n egf = coeff n (coshSeries + 2 * (sinhSeries * egf)) := by
      rw [← egf_eq]
    rw [h, map_add, two_mul (sinhSeries * egf), map_add, ← two_mul, coeff_mul]
  have h2 : (n.factorial : ℚ) * coeff n coshSeries = if Even n then 1 else 0 := by
    rw [coeff_cosh]
    split_ifs
    · exact mul_one_div_cancel hfac
    · exact mul_zero _
  have h3 : ∀ ij ∈ antidiagonal n,
      (n.factorial : ℚ) * (coeff ij.1 sinhSeries * coeff ij.2 egf) =
        (if Even ij.1 then 0 else (n.choose ij.1 : ℚ) * a ij.2) := by
    intro ij hij
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    rw [coeff_sinh]
    split_ifs with he
    · simp
    · have hch : ((n.choose ij.1 : ℕ) : ℚ) * (ij.1.factorial : ℚ) * (ij.2.factorial : ℚ) =
          (n.factorial : ℚ) := by
        have h := Nat.add_choose_mul_factorial_mul_factorial ij.1 ij.2
        rw [hij, ← Nat.choose_symm_of_eq_add hij.symm] at h
        exact_mod_cast h
      have hi : (ij.1.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ij.1.factorial_ne_zero
      rw [← hch]
      show _ = (n.choose ij.1 : ℚ) * ((ij.2.factorial : ℚ) * coeff ij.2 egf)
      linear_combination
        ((n.choose ij.1 : ℚ) * (ij.2.factorial : ℚ) * coeff ij.2 egf) * mul_one_div_cancel hi
  have h4 : (n.factorial : ℚ) * ∑ ij ∈ antidiagonal n, coeff ij.1 sinhSeries * coeff ij.2 egf =
      ∑ ij ∈ antidiagonal n, (if Even ij.1 then 0 else (n.choose ij.1 : ℚ) * a ij.2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl h3
  show (n.factorial : ℚ) * coeff n egf = _
  rw [h1, ← h2, ← h4]
  ring

private lemma a_zero : a 0 = 1 := by
  have h := a_rec 0
  simpa using h

/-- Step 3: every term is an integer. -/
private lemma a_int (n : ℕ) : ∃ z : ℤ, a n = (z : ℚ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hterm : ∀ ij ∈ antidiagonal n, ∃ w : ℤ,
        (if Even ij.1 then 0 else (n.choose ij.1 : ℚ) * a ij.2) = (w : ℚ) := by
      intro ij hij
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      split_ifs with he
      · exact ⟨0, by simp⟩
      · have h0 : ij.1 ≠ 0 := by
          intro h0
          rw [h0] at he
          exact he Even.zero
        obtain ⟨w, hw⟩ := ih ij.2 (by omega)
        exact ⟨(n.choose ij.1 : ℤ) * w, by rw [hw, Int.cast_mul, Int.cast_natCast]⟩
    choose! g hg using hterm
    refine ⟨(if Even n then 1 else 0) + 2 * ∑ ij ∈ antidiagonal n, g ij, ?_⟩
    rw [a_rec n, Finset.sum_congr rfl hg]
    split_ifs <;> push_cast <;> ring

/-- Step 4: the key lemma. -/
private lemma key (n d : ℕ) (h : ∀ i, i < n → ¬ Even i → d ∣ n.choose i) :
    ∃ z : ℤ, a n = (z : ℚ) ∧ (d : ℤ) ∣ z - (if Even n then 1 else 2) := by
  have hterm : ∀ k ∈ range n, ∃ w : ℤ,
      (if Even k then 0 else (n.choose k : ℚ) * a (n - k)) = (((d : ℤ) * w : ℤ) : ℚ) := by
    intro k hk
    rw [mem_range] at hk
    split_ifs with he
    · exact ⟨0, by simp⟩
    · obtain ⟨c, hc⟩ := h k hk he
      obtain ⟨w, hw⟩ := a_int (n - k)
      exact ⟨(c : ℤ) * w, by rw [hc, hw]; push_cast <;> ring⟩
  choose! g hg using hterm
  have hsum : ∑ k ∈ range n, (if Even k then 0 else (n.choose k : ℚ) * a (n - k)) =
      ((∑ k ∈ range n, (d : ℤ) * g k : ℤ) : ℚ) := by
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl hg
  have hsplit : ∑ ij ∈ antidiagonal n, (if Even ij.1 then 0 else (n.choose ij.1 : ℚ) * a ij.2) =
      ∑ k ∈ range n, (if Even k then 0 else (n.choose k : ℚ) * a (n - k)) +
        (if Even n then 0 else 1) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.choose_self, Nat.cast_one, one_mul, a_zero]
  refine ⟨(if Even n then 1 else 0) +
    2 * (∑ k ∈ range n, (d : ℤ) * g k + (if Even n then 0 else 1)), ?_, ?_⟩
  · rw [a_rec n, hsplit, hsum]
    split_ifs <;> push_cast <;> ring
  · refine ⟨2 * ∑ k ∈ range n, g k, ?_⟩
    rw [← Finset.mul_sum]
    split_ifs <;> ring

private lemma dvd_choose_of_coprime (n i : ℕ) (hn : n ≠ 0) (hi : i ≠ 0) (hc : Nat.Coprime n i) :
    n ∣ n.choose i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  exact hc.dvd_of_dvd_mul_right ⟨n'.choose j, (Nat.add_one_mul_choose_eq n' j).symm⟩

private lemma ne_zero_of_not_even {i : ℕ} (he : ¬ Even i) : i ≠ 0 := by
  intro h0
  rw [h0] at he
  exact he Even.zero

/-- First conjecture: `a(p) == 2 (mod p)` for primes `p > 2`. -/
private lemma claim1 (p : ℕ) (hp : p.Prime) (h2 : 2 < p) :
    ∃ z : ℤ, a p = (z : ℚ) ∧ (p : ℤ) ∣ z - 2 := by
  have hodd : ¬ Even p := by
    rw [Nat.not_even_iff_odd]
    exact hp.odd_of_ne_two (by omega)
  obtain ⟨z, hz, hdvd⟩ := key p p (fun i hi he => hp.dvd_choose_self (ne_zero_of_not_even he) hi)
  rw [if_neg hodd] at hdvd
  exact ⟨z, hz, hdvd⟩

/-- Second conjecture: `a(2^m) == 1 (mod 2^m)`. -/
private lemma claim2 (m : ℕ) : ∃ z : ℤ, a (2 ^ m) = (z : ℚ) ∧ ((2 : ℤ) ^ m) ∣ z - 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨z, hz⟩ := a_int (2 ^ 0)
    exact ⟨z, hz, by simp⟩
  · have heven : Even (2 ^ m) := Nat.even_pow.mpr ⟨even_two, hm.ne'⟩
    obtain ⟨z, hz, hdvd⟩ := key (2 ^ m) (2 ^ m) (fun i _ he =>
      dvd_choose_of_coprime (2 ^ m) i (pow_ne_zero m two_ne_zero) (ne_zero_of_not_even he)
        (Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr (Nat.not_even_iff_odd.mp he))))
    rw [if_pos heven] at hdvd
    refine ⟨z, hz, ?_⟩
    have hcast : ((2 ^ m : ℕ) : ℤ) = (2 : ℤ) ^ m := by simp
    rwa [hcast] at hdvd

end OMA.P_oeis_a364822

theorem OMA.solution : type_of% @OMA.S_oeis_a364822.main := by
  exact ⟨OMA.P_oeis_a364822.claim1, OMA.P_oeis_a364822.claim2⟩

import OMAStatements.S_oeis_a242932
import Mathlib

-- Problem: A242932, numbers n such that k n/(k+n) is prime for some k; no 4m^2 other than 4.
-- Upstream: formal-conjectures statements/oeis-a242932.lean (declaration OMA.S_oeis_a242932.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: k n = p (k + n) gives (k - p)(n - p) = p^2, so n - p is 1, p or p^2. For n = 4m^2 these
-- give p = (2m-1)(2m+1), p = 2m^2 (both composite for m >= 2), or 4m^2 = p^2 + p, which lies
-- strictly between p^2 and (p+1)^2.

theorem OMA.solution : type_of% @OMA.S_oeis_a242932.main := by
  intro m hm ⟨hn, k, hk, hdvd, hp⟩
  set n := 4 * m ^ 2 with hndef
  set p := k * n / (k + n) with hpdef
  have hkn : p * (k + n) = k * n := Nat.div_mul_cancel hdvd
  have hp2 := hp.two_le
  -- p < n and p < k
  have hpn : p < n := by
    by_contra hc
    push Not at hc
    have : p * (k + n) ≥ n * (k + n) := Nat.mul_le_mul_right _ hc
    nlinarith
  have hpk : p < k := by
    by_contra hc
    push Not at hc
    have : p * (k + n) ≥ k * (k + n) := Nat.mul_le_mul_right _ hc
    nlinarith
  -- (k - p)(n - p) = p^2
  have hkey : (k - p) * (n - p) = p ^ 2 := by
    zify [hpn.le, hpk.le]
    have : ((p : ℤ)) * ((k : ℤ) + n) = (k : ℤ) * n := by exact_mod_cast hkn
    nlinarith
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m <;> simp_all
    · exact h
  have hd : n - p ∣ p ^ 2 := ⟨k - p, by rw [← hkey]; ring⟩
  rw [Nat.dvd_prime_pow hp] at hd
  obtain ⟨i, hi, hi'⟩ := hd
  interval_cases i
  · -- n = p + 1
    simp at hi'
    have hp1 : p = 4 * m ^ 2 - 1 := by omega
    have hfac : p = (2 * m - 1) * (2 * m + 1) := by
      rw [hp1]
      zify [show 1 ≤ 2 * m by omega, show 1 ≤ 4 * m ^ 2 by nlinarith]
      ring
    have := (Nat.prime_mul_iff.mp (hfac ▸ hp))
    rcases this with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  · -- n = 2p
    simp at hi'
    have h2p : 2 * m ^ 2 = p := by omega
    have : ¬ (2 * m ^ 2).Prime := by
      rw [show 2 * m ^ 2 = (2 * m) * m by ring]
      exact Nat.not_prime_mul (by omega) (by omega)
    exact this (h2p ▸ hp)
  · -- n = p^2 + p, strictly between consecutive squares
    have hn' : n = p ^ 2 + p := by omega
    rw [hndef] at hn'
    rcases Nat.lt_or_ge (2 * m) (p + 1) with h | h
    · have : 2 * m ≤ p := by omega
      nlinarith
    · nlinarith


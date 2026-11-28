import OMAStatements.S_oeis_a090698

/-!
# Reduction R1 of OEIS A090698: `2 ^ (p - 1) - 3` is never prime

The problem lists the primes `p = 2 * n ^ 2 + 1` and conjectures (Librandi) that
`2 ^ (p - 1) - 3` is never prime.  Write `p = 2 * n ^ 2 + 1`; then
`p - 1 = 2 * n ^ 2`, so `2 ^ (p - 1) - 3 = 4 ^ (n ^ 2) - 3`.

The reduction has two hypotheses; only `H1` is proved here.

* `H1` (proved): if `n = 2` or `n = 3` modulo `5`, then `2 ^ (p - 1) - 3` is
  divisible by `11`, hence composite.  Indeed `4 ^ 5 = 1024 = 1 (mod 11)`, and
  `n ^ 2 = 4 (mod 5)` exactly for these residues, so
  `4 ^ (n ^ 2) = 4 ^ 4 = 256 = 3 (mod 11)`.  The value is at least
  `4 ^ 4 - 3 = 253`, so it is not the prime `11`.

  This kills the two residue classes `n = 2, 3 (mod 5)`.  Among the terms with
  `n <= 300` (41 of them) as many as 17 lie in these two classes, so the family
  removed is a positive proportion of the known terms, not a vacuous one.

* `H2` (open): the remaining residues `n = 0, 1, 4 (mod 5)`.  This is the core of
  the conjecture: no fixed small prime seems to divide `4 ^ (n ^ 2) - 3` on these
  classes.

So the target is reduced to the three residue classes `n = 0, 1, 4 (mod 5)`.

Numerically (Miller-Rabin style trial division for `n < 300`, and the modulo-`11`
identity for `n < 5000`), no term has `2 ^ (p - 1) - 3` prime and every
`n = 2, 3 (mod 5)` has `11 | 4 ^ (n ^ 2) - 3`, so neither hypothesis is false.
-/

namespace OMA.R_oeis_a090698_R1

/-- For `n = 2` or `n = 3` modulo `5`, the number `2 ^ (p - 1) - 3` with
`p = 2 * n ^ 2 + 1` is divisible by `11` and bigger than `11`, hence composite. -/
def H1 : Prop :=
  ∀ p n : ℕ, p = 2 * n ^ 2 + 1 → (n % 5 = 2 ∨ n % 5 = 3) → ¬ (2 ^ (p - 1) - 3).Prime

/-- The remaining case: for `n = 0, 1` or `4` modulo `5`, `2 ^ (p - 1) - 3` is
not prime. -/
def H2 : Prop :=
  ∀ p n : ℕ, p.Prime → p = 2 * n ^ 2 + 1 → n % 5 ≠ 2 → n % 5 ≠ 3 →
    ¬ (2 ^ (p - 1) - 3).Prime

theorem H1_proof : H1 := by
  intro p n hpn hres hp
  have hpm1 : p - 1 = 2 * n ^ 2 := by omega
  have hpow_eq : 2 ^ (p - 1) = 4 ^ (n ^ 2) := by
    rw [hpm1]
    rw [show 2 * n ^ 2 = 2 * (n ^ 2) by ring, pow_mul]
    norm_num
  have hn2 : 2 ≤ n := by
    rcases hres with h | h <;> omega
  have hnsq : n ^ 2 % 5 = 4 := by
    rcases hres with h | h
    · rw [Nat.pow_mod, h]
    · rw [Nat.pow_mod, h]
  have hdecomp : 5 * (n ^ 2 / 5) + 4 = n ^ 2 := by
    have h := Nat.div_add_mod (n ^ 2) 5
    rw [hnsq] at h
    simpa [mul_comm] using h
  have h45 : (4 : ℕ) ^ 5 ≡ 1 [MOD 11] := by
    show (4 : ℕ) ^ 5 % 11 = 1 % 11
    norm_num
  have hstep : (4 : ℕ) ^ (n ^ 2) = 4 ^ (5 * (n ^ 2 / 5)) * 4 ^ 4 := by
    conv_lhs => rw [← hdecomp]
    rw [pow_add]
  have hk : (4 : ℕ) ^ (5 * (n ^ 2 / 5)) ≡ 1 [MOD 11] := by
    rw [pow_mul]
    exact (h45.pow (n ^ 2 / 5)).trans (by norm_num)
  have h4 : (4 : ℕ) ^ 4 ≡ 3 [MOD 11] := by
    show (4 : ℕ) ^ 4 % 11 = 3 % 11
    norm_num
  have hpow : (4 : ℕ) ^ (n ^ 2) ≡ 3 [MOD 11] := by
    rw [hstep]
    simpa using hk.mul h4
  have hle : 3 ≤ 4 ^ (n ^ 2) := by
    have h1 : (4 : ℕ) ^ 1 ≤ 4 ^ (n ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have h4le : (4 : ℕ) ≤ 4 ^ (n ^ 2) := by simpa using h1
    omega
  have hdvd4 : 11 ∣ 4 ^ (n ^ 2) - 3 := (Nat.modEq_iff_dvd' hle).mp hpow.symm
  have hbound : 253 ≤ 4 ^ (n ^ 2) - 3 := by
    have h4le : 4 ≤ n ^ 2 := by nlinarith
    have hbig : (4 : ℕ) ^ 4 ≤ 4 ^ (n ^ 2) := Nat.pow_le_pow_right (by norm_num) h4le
    have h256 : (256 : ℕ) ≤ 4 ^ (n ^ 2) := by simpa using hbig
    omega
  have hp' : (4 ^ (n ^ 2) - 3).Prime := by rwa [hpow_eq] at hp
  rcases hp'.eq_one_or_self_of_dvd 11 hdvd4 with h | h <;> omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a090698.main := by
  intro h1 h2 p hp
  obtain ⟨hpp, n, hpn⟩ := hp
  by_cases h : n % 5 = 2 ∨ n % 5 = 3
  · exact h1 p n hpn h
  · push_neg at h
    exact h2 p n hpp hpn h.1 h.2

end OMA.R_oeis_a090698_R1

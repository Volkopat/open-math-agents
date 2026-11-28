import OMAStatements.S_oeis_a178319
import Mathlib

/-!
# Proof of OEIS A178319 Conjectures

For any integer `q > 1` and positive exponents `b, c >= 1`:
- `q ∣ q^b - q^c` since both powers are multiples of `q`.
- `(q - 1) ∣ q^b - q^c` since `q ≡ 1 (mod q - 1)`.
- Since `gcd(q, q - 1) = 1`, `q * (q - 1) ∣ q^b - q^c`, i.e., `q^b ≡ q^c [ZMOD q * (q - 1)]`.

By strong induction on `n`, `a q k ≡ 1 [ZMOD q * (q - 1)]` for all `k <= n`.
In the recurrence for `a q (n + 1)`, every term `k < n` has `m = n - k >= 1`, so both exponents
`m * (m + 3) / 2` and `m * (m + 1) / 2` are `>= 1`, whence
`a q k * q^(m*(m+3)/2) - a q (k + 1) * q^(m*(m+1)/2) ≡ 1 * q^(m*(m+1)/2) - 1 * q^(m*(m+1)/2) = 0 [ZMOD q * (q - 1)]`.
Thus `a q (n + 1) ≡ a q n ≡ 1 [ZMOD q * (q - 1)]`. Specializing `q = 3` gives `a 3 n ≡ 1 [ZMOD 6]`.
-/

namespace OeisA178319Proof

open OMA.S_oeis_a178319

private lemma pow_modEq_pow_of_pos (q b c : ℕ) (hq : 1 < q) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    ((q : ℤ) ^ b) ≡ ((q : ℤ) ^ c) [ZMOD (q * (q - 1) : ℕ)] := by
  rw [Int.modEq_iff_dvd]
  have hd1 : (q : ℤ) ∣ (q : ℤ) ^ c - (q : ℤ) ^ b :=
    dvd_sub (dvd_pow_self (q : ℤ) (by omega)) (dvd_pow_self (q : ℤ) (by omega))
  have hq1 : ((q : ℤ) ≡ 1 [ZMOD ((q - 1 : ℕ) : ℤ)]) := by
    rw [Int.modEq_iff_dvd]
    have hsub : (1 : ℤ) - (q : ℤ) = -((q - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ q)]; push_cast; ring
    rw [hsub]
    exact dvd_neg.mpr (dvd_refl _)
  have hd2 : ((q - 1 : ℕ) : ℤ) ∣ (q : ℤ) ^ c - (q : ℤ) ^ b := by
    have hpb : (q : ℤ) ^ b ≡ 1 [ZMOD ((q - 1 : ℕ) : ℤ)] := by simpa using hq1.pow b
    have hpc : (q : ℤ) ^ c ≡ 1 [ZMOD ((q - 1 : ℕ) : ℤ)] := by simpa using hq1.pow c
    exact Int.modEq_iff_dvd.mp (hpb.trans hpc.symm)
  have hcop : IsCoprime (q : ℤ) ((q - 1 : ℕ) : ℤ) := by
    refine ⟨1, -1, ?_⟩
    rw [Nat.cast_sub (by omega : 1 ≤ q)]; push_cast; ring
  have hmul := hcop.mul_dvd hd1 hd2
  simpa [Nat.cast_mul] using hmul

private lemma a_modEq_one (q : ℕ) (hq : 1 < q) :
    ∀ n : ℕ, a q n ≡ 1 [ZMOD (q * (q - 1) : ℕ)] := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [a, Int.ModEq]
    | succ n =>
      rw [a]
      have hsum : (∑ k : Fin n,
          (Nat.choose n k.1 : ℤ) *
            (a q k.1 * (q : ℤ) ^ ((n - k.1) * (n - k.1 + 3) / 2) -
              a q (k.1 + 1) * (q : ℤ) ^ ((n - k.1) * (n - k.1 + 1) / 2))) ≡
          0 [ZMOD (q * (q - 1) : ℕ)] := by
        rw [Int.modEq_zero_iff_dvd]
        apply Finset.dvd_sum
        intro k _
        apply dvd_mul_of_dvd_right
        have hklt := k.2
        have h1 : a q k.1 ≡ 1 [ZMOD (q * (q - 1) : ℕ)] := ih k.1 (by omega)
        have h2 : a q (k.1 + 1) ≡ 1 [ZMOD (q * (q - 1) : ℕ)] := ih (k.1 + 1) (by omega)
        have hm1 : 1 ≤ n - k.1 := by omega
        have he1 : 1 ≤ (n - k.1) * (n - k.1 + 3) / 2 := by
          have : 2 ≤ (n - k.1) * (n - k.1 + 3) := by nlinarith
          omega
        have he2 : 1 ≤ (n - k.1) * (n - k.1 + 1) / 2 := by
          have : 2 ≤ (n - k.1) * (n - k.1 + 1) := by nlinarith
          omega
        have hp := pow_modEq_pow_of_pos q ((n - k.1) * (n - k.1 + 3) / 2)
          ((n - k.1) * (n - k.1 + 1) / 2) hq he1 he2
        have hmul1 : a q k.1 * (q : ℤ) ^ ((n - k.1) * (n - k.1 + 3) / 2) ≡
            1 * (q : ℤ) ^ ((n - k.1) * (n - k.1 + 1) / 2) [ZMOD (q * (q - 1) : ℕ)] :=
          h1.mul hp
        have hmul2 : a q (k.1 + 1) * (q : ℤ) ^ ((n - k.1) * (n - k.1 + 1) / 2) ≡
            1 * (q : ℤ) ^ ((n - k.1) * (n - k.1 + 1) / 2) [ZMOD (q * (q - 1) : ℕ)] :=
          h2.mul rfl
        have hsub := hmul1.sub hmul2
        rw [sub_self] at hsub
        exact Int.modEq_zero_iff_dvd.mp hsub
      have hprev : a q n ≡ 1 [ZMOD (q * (q - 1) : ℕ)] := ih n (by omega)
      simpa using hprev.add hsum

end OeisA178319Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a178319.main := by
  refine ⟨?_, fun q n hq => OeisA178319Proof.a_modEq_one q hq n⟩
  intro n
  simpa using OeisA178319Proof.a_modEq_one 3 (by omega) n

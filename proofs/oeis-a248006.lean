import OMAStatements.S_oeis_a248006
import Mathlib

/-!
# A248006: a(n) exists and a(n) ≤ n for n > 2

Take m = n: φ(n²) = n·φ(n) (from φ(gcd)·φ(ab) = φ(a)φ(b)·gcd with a = b = n), and φ(n) is even for
n > 2, so 2n = m + n divides φ(mn). Hence the set is nonempty and its infimum is at most n (the
argument indicated in the entry).
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a248006.main := by
  intro n hn
  have hmem : n ∈ {m : ℕ | 0 < m ∧ (m + n) ∣ Nat.totient (m * n)} := by
    refine ⟨by omega, ?_⟩
    have h := Nat.totient_gcd_mul_totient_mul n n
    rw [Nat.gcd_self] at h
    have hpos : 0 < Nat.totient n := Nat.totient_pos.mpr (by omega)
    have hsq : Nat.totient (n * n) = Nat.totient n * n := by
      have h' : Nat.totient n * Nat.totient (n * n) = Nat.totient n * (Nat.totient n * n) := by
        rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_left hpos h'
    rw [hsq]
    obtain ⟨t, ht⟩ := (Nat.totient_even hn)
    rw [ht, show n + n = 2 * n by ring]
    exact ⟨t, by ring⟩
  exact ⟨⟨n, hmem⟩, Nat.sInf_le hmem⟩

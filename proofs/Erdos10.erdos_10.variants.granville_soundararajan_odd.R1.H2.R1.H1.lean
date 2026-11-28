import OMAReductions.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R1_H2_R1

-- Step Erdos10.erdos_10.variants.granville_soundararajan_odd.R1.H2.R1.H1: hypothesis H1 of
-- reduction Erdos10.erdos_10.variants.granville_soundararajan_odd.R1.H2.R1.
-- Written with Claude Code (AI-assisted).
-- Finite check: every even n with 0 < n ≤ 256 has a prime p ≤ n such that n - p has at most
-- four binary digits equal to one; the powers of two are the bit indices of n - p.

namespace OMA.E10GS256

/-- Boolean search for a prime `p ≤ n` with `n - p` having at most four one bits. -/
def ok (n : ℕ) : Bool :=
  (List.range (n + 1)).any fun p => Nat.Prime p && decide ((n - p).bitIndices.length ≤ 4)

theorem ok_all : ∀ n < 257, n % 2 = 0 → n ≠ 0 → ok n = true := by decide +kernel

theorem mem_of_ok {n : ℕ} (h : ok n = true) : n ∈ Erdos10.sumPrimeAndTwoPows 4 := by
  obtain ⟨p, hp, hpq⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpq
  obtain ⟨hprime, hlen⟩ := hpq
  have hpn : p ≤ n := Nat.lt_succ_iff.mp (List.mem_range.mp hp)
  refine ⟨p, ((n - p).bitIndices : Multiset ℕ), hprime, by simpa using hlen, ?_⟩
  rw [Multiset.map_coe, Multiset.sum_coe, Nat.twoPowSum_bitIndices]
  omega

end OMA.E10GS256

theorem OMA.solution :
    OMA.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R1_H2_R1.H1 := by
  intro n hn hn0 hle
  exact OMA.E10GS256.mem_of_ok
    (OMA.E10GS256.ok_all n (by omega) (Nat.even_iff.mp hn) hn0)

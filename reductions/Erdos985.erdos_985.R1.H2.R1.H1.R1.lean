import OMAReductions.R_Erdos985_erdos_985_R1_H2_R1
import Mathlib
/-!
# Splitting the three-prime-factor certificate by range

The finite hypothesis for primes whose group order has exactly three distinct prime
factors is cut at 47000000 into two ranges of roughly equal cost. Each half is a kernel
computation (a segmented sieve, a verified factorisation of p - 1 and a search for a
small prime primitive root), sized to fit one checker run. The number-theoretic lemmas
both halves need are proved here once.

H1 covers the primes below 47000000 and H2 those from 47000000 up to 10^8; in both,
the group order p - 1 has exactly three distinct prime factors.
-/

namespace OMA.R_Erdos985_erdos_985_R1_H2_R1_H1_R1

/-! Lemmas shared by the two range checks: they turn a verified list of prime divisors of
p - 1 into bounds on the number of prime factors, and into the full list of prime factors. -/

/-- A prime whose predecessor has three prime factors is odd. -/
theorem pred_even {p : Nat} (hp : p.Prime) (h3 : (p-1).primeFactors.card = 3) : p - 1 ≠ 0 ∧ 2 ∣ p - 1 := by
  rcases hp.eq_two_or_odd with rfl | hodd
  · simp at h3
  · have := hp.two_le
    exact ⟨by omega, by omega⟩

/-- distinct odd primes dividing an even number, counted together with 2 -/
theorem card_ge {n : Nat} (hn : n ≠ 0) (h2 : 2 ∣ n) (l : List Nat) (hp : l.Pairwise (· < ·))
    (hl : ∀ a ∈ l, 2 < a ∧ a.Prime ∧ a ∣ n) : l.length + 1 ≤ n.primeFactors.card := by
  have hnd : l.Nodup := hp.imp (fun h => Nat.ne_of_lt h)
  have hsub : insert 2 l.toFinset ⊆ n.primeFactors := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hn⟩
    · obtain ⟨_, h3, h4⟩ := hl t (List.mem_toFinset.mp ht)
      exact Nat.mem_primeFactors.mpr ⟨h3, h4, hn⟩
  have h2n : 2 ∉ l.toFinset := by
    intro h
    have := (hl 2 (List.mem_toFinset.mp h)).1
    omega
  calc l.length + 1 = (insert 2 l.toFinset).card := by
        rw [Finset.card_insert_of_notMem h2n, List.toFinset_card_of_nodup hnd]
    _ ≤ _ := Finset.card_le_card hsub

/-- A divisor of an even n < 10^8 that is coprime to a multiple F of every d ≤ 8192 is 1 or a
prime above 8192. -/
theorem cofactor_prime {F n c : Nat} (hF : ∀ d, 1 ≤ d → d ≤ 8192 → d ∣ F) (hn0 : n ≠ 0) (hn : n < 10^8)
    (h2 : 2 ∣ n) (hcn : c ∣ n) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hg : Nat.gcd c F = 1) : c.Prime ∧ 8192 < c := by
  have hbig : 8192 < c := by
    by_contra h
    have hd : c ∣ Nat.gcd c F := Nat.dvd_gcd dvd_rfl (hF _ (by omega) (by omega))
    rw [hg] at hd
    exact hc1 (Nat.dvd_one.mp hd)
  refine ⟨?_, hbig⟩
  by_contra hnp
  have hodd : ¬ 2 ∣ c := by
    intro h
    have hd : 2 ∣ Nat.gcd c F := Nat.dvd_gcd h (hF _ (by omega) (by omega))
    rw [hg] at hd
    omega
  obtain ⟨m, rfl⟩ := hcn
  have hm2 : 2 ∣ m := (Nat.Prime.dvd_mul Nat.prime_two).mp h2 |>.resolve_left hodd
  have hle : c * 2 ≤ c * m := by
    obtain ⟨j, rfl⟩ := hm2
    have : j ≠ 0 := by rintro rfl; simp at hn0
    nlinarith [Nat.pos_of_ne_zero this]
  have hm := Nat.minFac_sq_le_self (Nat.pos_of_ne_zero hc0) hnp
  have hmp : c.minFac.Prime := Nat.minFac_prime hc1
  have hm8 : c.minFac ≤ 8192 := by
    by_contra hc
    have : 8193 ≤ c.minFac := by omega
    nlinarith
  have hd : c.minFac ∣ Nat.gcd c F := Nat.dvd_gcd (Nat.minFac_dvd c) (hF _ hmp.one_lt.le hm8)
  rw [hg] at hd
  exact hmp.one_lt.ne' (Nat.dvd_one.mp hd)

/-- completeness of the candidate list: every prime factor is 2, in the list, or the cofactor -/
theorem factor_cases {n G c : Nat} (l : List Nat) (hG : n = G * c) (hl : ∀ a ∈ l, a.Prime)
    (hcp : c ≠ 1 → c.Prime) (hcomp : (2 * l.prod)^27 % G = 0) {t : Nat} (ht : t.Prime) (htn : t ∣ n) :
    t = 2 ∨ t ∈ l ∨ (c ≠ 1 ∧ t = c) := by
  rw [hG] at htn
  rcases (Nat.Prime.dvd_mul ht).mp htn with h | h
  · have h1 : t ∣ (2 * l.prod)^27 := h.trans (Nat.dvd_of_mod_eq_zero hcomp)
    have h2 := ht.dvd_of_dvd_pow h1
    rcases (Nat.Prime.dvd_mul ht).mp h2 with h3 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq ht Nat.prime_two).mp h3)
    · obtain ⟨a, ha, hta⟩ := (Prime.dvd_prod_iff ht.prime).mp h3
      exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq ht (hl a ha)).mp hta ▸ ha))
  · by_cases hc1 : c = 1
    · rw [hc1] at h
      exact absurd (Nat.dvd_one.mp h) ht.one_lt.ne'
    · exact Or.inr (Or.inr ⟨hc1, (Nat.prime_dvd_prime_iff_eq ht (hcp hc1)).mp h⟩)

def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p < 47000000 → (p-1).primeFactors.card = 3 →
    ∃ q : ℕ, q.Prime ∧ q < p ∧ ∀ s ∈ (p-1).primeFactors, q^((p-1)/s) % p ≠ 1

def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 47000000 ≤ p → p < 10^8 → (p-1).primeFactors.card = 3 →
    ∃ q : ℕ, q.Prime ∧ q < p ∧ ∀ s ∈ (p-1).primeFactors, q^((p-1)/s) % p ≠ 1

theorem main : H1 → H2 → OMA.R_Erdos985_erdos_985_R1_H2_R1.H1 := by
  intro h1 h2 p hp hl h3
  by_cases h : p < 47000000
  · exact h1 p hp h h3
  · exact h2 p hp (by omega) hl h3

end OMA.R_Erdos985_erdos_985_R1_H2_R1_H1_R1

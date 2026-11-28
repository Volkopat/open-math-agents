import OMAStatements.S_oeis_a024675
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.PrimeCounting

/-! Reduce the divisibility of the running products to sums of prime valuations. -/

namespace OMA.R_oeis_a024675_R1

open OMA.S_oeis_a024675

/-- The cumulative 2-adic valuation of the half-gaps is bounded by that of the means. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∑ k ∈ Finset.Icc 1 n, (d k).factorization 2) ≤
      ∑ k ∈ Finset.Icc 1 n, (a k).factorization 2

/-- The corresponding cumulative inequalities for odd primes. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ n : ℕ, 1 ≤ n →
    (∑ k ∈ Finset.Icc 1 n, (d k).factorization p) ≤
      ∑ k ∈ Finset.Icc 1 n, (a k).factorization p

lemma halfGap_pos {k : ℕ} (hk : 1 ≤ k) : 0 < d k := by
  have h₁ := Nat.add_two_le_nth_prime k
  have h₂ := Nat.add_two_le_nth_prime (k + 1)
  have hodd₁ : Nat.nth Nat.Prime k % 2 = 1 :=
    (Nat.prime_nth_prime k).eq_two_or_odd.resolve_left (by omega)
  have hodd₂ : Nat.nth Nat.Prime (k + 1) % 2 = 1 :=
    (Nat.prime_nth_prime (k + 1)).eq_two_or_odd.resolve_left (by omega)
  have hlt : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k + 1) :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self k)
  unfold d
  omega

lemma mean_pos (k : ℕ) : 0 < a k := by
  have h₁ := Nat.add_two_le_nth_prime k
  have h₂ := Nat.add_two_le_nth_prime (k + 1)
  unfold a
  omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a024675.main := by
  intro h₂ hodd n hn
  have hd : ∀ k ∈ Finset.Icc 1 n, d k ≠ 0 :=
    fun k hk => (halfGap_pos (Finset.mem_Icc.mp hk).1).ne'
  have ha : ∀ k ∈ Finset.Icc 1 n, a k ≠ 0 := fun k _ => (mean_pos k).ne'
  apply (Nat.factorization_prime_le_iff_dvd
    (Finset.prod_ne_zero_iff.mpr hd) (Finset.prod_ne_zero_iff.mpr ha)).mp
  intro p hp
  rw [Nat.factorization_prod_apply hd, Nat.factorization_prod_apply ha]
  by_cases h : p = 2
  · subst p
    exact h₂ n hn
  · exact hodd p hp h n hn

end OMA.R_oeis_a024675_R1

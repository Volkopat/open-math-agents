import OMAStatements.S_oeis_a103176
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic

namespace OMA.P_oeis_a103176

open OMA.S_oeis_a103176
open scoped ArithmeticFunction.sigma

private lemma nth_prime_succ_ge_add_two {k : ℕ} (hk : 1 ≤ k) :
    Nat.nth Nat.Prime k + 2 ≤ Nat.nth Nat.Prime (k + 1) := by
  have hp1 : (Nat.nth Nat.Prime k).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k
  have hp2 : (Nat.nth Nat.Prime (k + 1)).Prime :=
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (k + 1)
  have hlt : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k + 1) :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self k)
  have hge3 : 3 ≤ Nat.nth Nat.Prime k := by
    have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
    rw [← h1]
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hk
  have hodd1 : Odd (Nat.nth Nat.Prime k) := hp1.odd_of_ne_two (by omega)
  have hodd2 : Odd (Nat.nth Nat.Prime (k + 1)) := hp2.odd_of_ne_two (by omega)
  rcases hodd1 with ⟨a, ha⟩
  rcases hodd2 with ⟨b, hb⟩
  omega

private lemma nth_prime_add_five_ge (k : ℕ) :
    Nat.nth Nat.Prime k + 9 ≤ Nat.nth Nat.Prime (k + 5) := by
  have h01 : Nat.nth Nat.Prime k + 1 ≤ Nat.nth Nat.Prime (k + 1) :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self k)
  have h12 : Nat.nth Nat.Prime (k + 1) + 2 ≤ Nat.nth Nat.Prime (k + 2) := by
    simpa [Nat.add_assoc] using nth_prime_succ_ge_add_two (k := k + 1) (by omega)
  have h23 : Nat.nth Nat.Prime (k + 2) + 2 ≤ Nat.nth Nat.Prime (k + 3) := by
    simpa [Nat.add_assoc] using nth_prime_succ_ge_add_two (k := k + 2) (by omega)
  have h34 : Nat.nth Nat.Prime (k + 3) + 2 ≤ Nat.nth Nat.Prime (k + 4) := by
    simpa [Nat.add_assoc] using nth_prime_succ_ge_add_two (k := k + 3) (by omega)
  have h45 : Nat.nth Nat.Prime (k + 4) + 2 ≤ Nat.nth Nat.Prime (k + 5) := by
    simpa [Nat.add_assoc] using nth_prime_succ_ge_add_two (k := k + 4) (by omega)
  omega

private lemma sigma_ge_of_composite {n : ℕ} (hn : 2 ≤ n) (hnp : ¬ n.Prime) :
    n + 3 ≤ σ 1 n := by
  let d := n.minFac
  have hd_prime : d.Prime := Nat.minFac_prime (by omega)
  have hd_dvd : d ∣ n := Nat.minFac_dvd n
  have hd_ge2 : 2 ≤ d := hd_prime.two_le
  have hd_lt : d < n := by
    have hle : d ≤ n := Nat.le_of_dvd (by omega) hd_dvd
    by_contra h
    have hEq : d = n := by omega
    exact hnp (hEq ▸ hd_prime)
  have hsub : ({1, d, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Nat.one_mem_divisors.mpr (by omega)
    · exact Nat.mem_divisors.mpr ⟨hd_dvd, by omega⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_refl x, by omega⟩
  have hsum_le : ∑ x ∈ ({1, d, n} : Finset ℕ), x ≤ ∑ x ∈ n.divisors, x :=
    Finset.sum_le_sum_of_subset hsub
  have hcard_sum : ∑ x ∈ ({1, d, n} : Finset ℕ), x = 1 + d + n := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega), Finset.sum_singleton]
    ring
  rw [ArithmeticFunction.sigma_apply]
  have hpow : ∑ x ∈ n.divisors, x ^ 1 = ∑ x ∈ n.divisors, x := by simp
  rw [hpow]
  omega

private lemma totient_le_of_composite {n : ℕ} (hn : 2 ≤ n) (hnp : ¬ n.Prime) :
    Nat.totient n ≤ n - 2 := by
  let d := n.minFac
  have hd_prime : d.Prime := Nat.minFac_prime (by omega)
  have hd_dvd : d ∣ n := Nat.minFac_dvd n
  have hd_ge2 : 2 ≤ d := hd_prime.two_le
  have hd_lt : d < n := by
    have hle : d ≤ n := Nat.le_of_dvd (by omega) hd_dvd
    by_contra h
    have hEq : d = n := by omega
    exact hnp (hEq ▸ hd_prime)
  rw [Nat.totient_eq_card_coprime]
  have hsub : (Finset.range n).filter n.Coprime ⊆ ((Finset.range n).erase 0).erase d := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    simp only [Finset.mem_erase, Finset.mem_range]
    refine ⟨?_, ?_, hx.1⟩
    · intro hxd
      rw [hxd] at hx
      have h1 : d ∣ Nat.gcd n d := Nat.dvd_gcd hd_dvd (dvd_refl d)
      rw [hx.2.gcd_eq_one] at h1
      have := Nat.le_of_dvd (by norm_num) h1
      omega
    · intro hx0
      rw [hx0] at hx
      have h1 : n = 1 := by simpa [Nat.Coprime] using hx.2
      omega
  have hle := Finset.card_le_card hsub
  have h0mem : 0 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hdmem : d ∈ (Finset.range n).erase 0 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hd_lt⟩
  rw [Finset.card_erase_of_mem hdmem, Finset.card_erase_of_mem h0mem, Finset.card_range] at hle
  omega

private theorem prove_main : type_of% @OMA.S_oeis_a103176.main := by
  intro n hn hdiff
  by_cases hn1 : n = 1
  · subst hn1
    have hs : σ 1 1 = 1 := by simp
    have ht : Nat.totient 1 = 1 := by simp
    rw [hs, ht] at hdiff
    omega
  have hn2 : 2 ≤ n := by omega
  have hp : n.Prime := by
    by_contra hnp
    have hs : n + 3 ≤ σ 1 n := sigma_ge_of_composite hn2 hnp
    have ht : Nat.totient n ≤ n - 2 := totient_le_of_composite hn2 hnp
    have ht_pos : 1 ≤ Nat.totient n := Nat.totient_pos.mpr (by omega)
    have hidx : (Nat.totient n - 1) + 5 ≤ σ 1 n - 1 := by omega
    have hmono : Nat.nth Nat.Prime ((Nat.totient n - 1) + 5) ≤ Nat.nth Nat.Prime (σ 1 n - 1) :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hidx
    have h9 := nth_prime_add_five_ge (Nat.totient n - 1)
    omega
  refine ⟨?_, hp⟩
  have hs : σ 1 n = n + 1 := by
    rw [ArithmeticFunction.sigma_one_apply, hp.divisors, Finset.sum_pair hp.ne_one.symm]
    omega
  have ht : Nat.totient n = n - 1 := Nat.totient_prime hp
  have := hp.two_le
  rw [hs, ht]
  omega

end OMA.P_oeis_a103176

theorem OMA.solution : type_of% @OMA.S_oeis_a103176.main :=
  OMA.P_oeis_a103176.prove_main

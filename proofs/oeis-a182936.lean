import OMAStatements.S_oeis_a182936
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: pointwise, a(k) = A014963(k) - [k prime] k - [k = 1]. For k = 1 and k prime the set
-- of divisors d with 1 < d < k is empty (gcd 0). For k = p^e with e >= 2 the gcd is p, since p
-- is such a divisor and p divides all of them. Otherwise k has two distinct prime factors, both
-- such divisors, so the gcd is 1. Summing the pointwise identity over 1..n gives the claim.
-- No computer search.

namespace OMA.A182936Proof

open OMA.S_oeis_a182936

theorem mem_S {k d : ℕ} :
    d ∈ (k.properDivisors).filter (fun d => 1 < d) ↔ (d ∣ k ∧ d < k) ∧ 1 < d := by
  rw [Finset.mem_filter, Nat.mem_properDivisors]

theorem key (k : ℕ) (hk : 1 ≤ k) :
    (a k : ℤ) = (expMangoldt k : ℤ) - (if k.Prime then (k : ℤ) else 0) -
      (if k = 1 then 1 else 0) := by
  rcases Nat.lt_or_ge k 2 with h1 | h2
  · obtain rfl : k = 1 := by omega
    simp [a, expMangoldt, not_isPrimePow_one, Nat.not_prime_one]
  by_cases hp : k.Prime
  · have hS : (k.properDivisors).filter (fun d => 1 < d) = ∅ := by
      ext d
      rw [mem_S]
      simp only [Finset.notMem_empty, iff_false, not_and, not_lt]
      intro ⟨hd, hdk⟩
      rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
    have hk1 : k ≠ 1 := by omega
    simp [a, hS, expMangoldt, hp.isPrimePow, hp, hk1]
  · have hk1 : k ≠ 1 := by omega
    simp only [hp, hk1, if_false, sub_zero]
    set S := (k.properDivisors).filter (fun d => 1 < d) with hSdef
    have hmp : k.minFac.Prime := Nat.minFac_prime (by omega)
    have hmS : k.minFac ∈ S := by
      rw [hSdef, mem_S]
      refine ⟨⟨Nat.minFac_dvd k, ?_⟩, hmp.one_lt⟩
      exact lt_of_le_of_ne (Nat.minFac_le (by omega)) (fun h => hp (h ▸ hmp))
    have hg : S.gcd id ∣ k.minFac := Finset.gcd_dvd hmS
    by_cases hpp : IsPrimePow k
    · obtain ⟨p, e, hpr, he, rfl⟩ := (isPrimePow_nat_iff k).mp hpp
      have hmin : (p ^ e).minFac = p := hpr.pow_minFac (by omega)
      have hdiv : p ∣ S.gcd id := by
        apply Finset.dvd_gcd
        intro d hd
        rw [hSdef, mem_S] at hd
        obtain ⟨⟨hd1, _⟩, hd2⟩ := hd
        obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hpr).mp hd1
        have : i ≠ 0 := by rintro rfl; simp at hd2
        exact dvd_pow_self p this
      rw [hmin] at hg
      have heq : S.gcd id = p := Nat.dvd_antisymm hg hdiv
      simp only [a, ← hSdef, heq, expMangoldt, hpp, if_true, hmin]
    · have h1 : S.gcd id = 1 := by
        rcases (Nat.dvd_prime hmp).mp hg with h | h
        · exact h
        · exfalso
          apply hpp
          rw [isPrimePow_iff_unique_prime_dvd]
          refine ⟨k.minFac, ⟨hmp, Nat.minFac_dvd k⟩, ?_⟩
          rintro r ⟨hr, hrk⟩
          have hrS : r ∈ S := by
            rw [hSdef, mem_S]
            refine ⟨⟨hrk, ?_⟩, hr.one_lt⟩
            exact lt_of_le_of_ne (Nat.le_of_dvd (by omega) hrk) (fun h => hp (h ▸ hr))
          have := Finset.gcd_dvd (f := id) hrS
          rw [h] at this
          exact ((Nat.prime_dvd_prime_iff_eq hmp hr).mp this).symm
      simp only [a, ← hSdef, h1, expMangoldt, hpp, if_false]

theorem sum_eq (n : ℕ) (hn : 1 ≤ n) :
    ((∑ k ∈ Finset.Icc 1 n, a k : ℕ) : ℤ) =
      (∑ k ∈ Finset.Icc 1 n, expMangoldt k : ℕ) -
        (∑ p ∈ Finset.Icc 1 n with p.Prime, p : ℕ) - 1 := by
  push_cast
  rw [Finset.sum_filter]
  have h1 : (∑ k ∈ Finset.Icc 1 n, (if k = 1 then (1 : ℤ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq']
    simp [Finset.mem_Icc, hn]
  rw [Finset.sum_congr rfl (fun k hk => key k (Finset.mem_Icc.mp hk).1)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, h1]

end OMA.A182936Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a182936.main := OMA.A182936Proof.sum_eq

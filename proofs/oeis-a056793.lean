import OMAStatements.S_oeis_a056793
import Mathlib

namespace R056793
open OMA.S_oeis_a056793

theorem lcm_eq (n : ℕ) : lcmUpTo n = Nat.lcmUpto n := rfl

theorem lcm_ne (n : ℕ) : lcmUpTo n ≠ 0 := Nat.lcmUpto_ne_zero n

theorem dvd_iff (n m : ℕ) (hn : 1 ≤ n) (hm : m ≠ 0) :
    m ∣ lcmUpTo n ↔ ∀ p ∈ m.primeFactors, p ^ m.factorization p ≤ n := by
  rw [← Nat.factorization_le_iff_dvd hm (lcm_ne n), Finsupp.le_iff, Nat.support_factorization]
  refine forall₂_congr fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [lcm_eq, Nat.factorization_lcmUpto n hpp]
  constructor
  · intro h
    calc p ^ m.factorization p ≤ p ^ p.log n := Nat.pow_le_pow_right hpp.pos h
      _ ≤ n := Nat.pow_log_le_self p (by omega)
  · intro h
    exact Nat.le_log_of_pow_le hpp.one_lt h

theorem mpp_le_iff (n m : ℕ) (hn : 1 ≤ n) :
    maxPrimePower m ≤ n ↔ ∀ p ∈ m.primeFactors, p ^ m.factorization p ≤ n := by
  unfold maxPrimePower
  rw [max_le_iff, Finset.sup_le_iff]
  exact ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩

theorem one_le_mpp (m : ℕ) : 1 ≤ maxPrimePower m := le_max_left _ _

theorem mem_div_iff (n m : ℕ) (hn : 1 ≤ n) :
    m ∈ (lcmUpTo n).divisors ↔ 1 ≤ m ∧ maxPrimePower m ≤ n := by
  rw [Nat.mem_divisors]
  constructor
  · rintro ⟨h, -⟩
    have hm : m ≠ 0 := by
      rintro rfl
      exact lcm_ne n (zero_dvd_iff.mp h)
    exact ⟨Nat.one_le_iff_ne_zero.mpr hm, (mpp_le_iff n m hn).2 ((dvd_iff n m hn hm).1 h)⟩
  · rintro ⟨h1, h2⟩
    have hm : m ≠ 0 := by omega
    exact ⟨(dvd_iff n m hn hm).2 ((mpp_le_iff n m hn).1 h2), lcm_ne n⟩

theorem fiber_card (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    a101207 k = ((lcmUpTo n).divisors.filter (fun m => maxPrimePower m = k)).card := by
  unfold a101207
  rw [← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro m
  rw [Finset.mem_filter, mem_div_iff n m hn]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2 ▸ hk⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩

end R056793

theorem OMA.solution : type_of% @OMA.S_oeis_a056793.main := by
  intro n hn
  unfold OMA.S_oeis_a056793.a056793
  rw [Finset.card_eq_sum_card_fiberwise (f := OMA.S_oeis_a056793.maxPrimePower)
    (t := Finset.Icc 1 n)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    exact (R056793.fiber_card n k hn hk.2).symm
  · intro m hm
    rw [Finset.mem_coe, R056793.mem_div_iff n m hn] at hm
    exact Finset.mem_Icc.mpr ⟨R056793.one_le_mpp m, hm.2⟩

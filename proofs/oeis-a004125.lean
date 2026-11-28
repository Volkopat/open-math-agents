import OMAStatements.S_oeis_a004125
import Mathlib

/-!
# A004125: the first difference is 2n − 1 − σ(n)

For 1 ≤ k ≤ n, n mod k = (n − 1) mod k + 1 unless k ∣ n, in which case n mod k = 0 and
(n − 1) mod k = k − 1; i.e. n mod k + [k ∣ n]·k = (n − 1) mod k + 1. Summing over k ≤ n gives
a(n) + σ(n) = a(n − 1) + (n − 1) + n, which is the stated difference (with natural subtraction on
both sides). This is the argument recorded in the entry.
-/

namespace PA004125

theorem termwise (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    n % k + (if k ∣ n then k else 0) = (n - 1) % k + 1 := by
  have hdiv := Nat.div_add_mod (n - 1) k
  have hr := Nat.mod_lt (n - 1) (show k > 0 by omega)
  generalize (n - 1) / k = q at hdiv
  generalize (n - 1) % k = r at hdiv hr ⊢
  by_cases h : r + 1 = k
  · have hn' : n = 0 + k * (q + 1) := by rw [mul_add]; omega
    have hkd : k ∣ n := ⟨q + 1, by omega⟩
    rw [if_pos hkd, hn', Nat.add_mul_mod_self_left]
    simp
    omega
  · have hn' : n = (r + 1) + k * q := by omega
    have hmod : n % k = r + 1 := by
      rw [hn', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have hkd : ¬ k ∣ n := fun hd => by
      have := Nat.mod_eq_zero_of_dvd hd
      omega
    rw [if_neg hkd, hmod]

end PA004125

theorem OMA.solution : type_of% @OMA.S_oeis_a004125.main := by
  intro n hn
  have hsum : ∑ k ∈ Finset.Icc 1 n, (n % k + (if k ∣ n then k else 0)) =
      ∑ k ∈ Finset.Icc 1 n, ((n - 1) % k + 1) :=
    Finset.sum_congr rfl fun k hk => PA004125.termwise n k (by omega) (Finset.mem_Icc.mp hk).1
  have hdivs : (Finset.Icc 1 n).filter (· ∣ n) = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨-, hd⟩; exact ⟨hd, by omega⟩
    · rintro ⟨hd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), Nat.le_of_dvd (by omega) hd⟩, hd⟩
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
    add_zero, hdivs, Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one] at hsum
  have hsplit : ∑ k ∈ Finset.Icc 1 n, (n - 1) % k =
      OMA.S_oeis_a004125.a (n - 1) + (n - 1) := by
    unfold OMA.S_oeis_a004125.a
    rw [show n = (n - 1) + 1 by omega, Finset.sum_Icc_succ_top (by omega),
      Nat.mod_eq_of_lt (by omega)]
    simp only [Nat.add_sub_cancel]
  have ha : OMA.S_oeis_a004125.a n = ∑ k ∈ Finset.Icc 1 n, n % k := rfl
  have hs : OMA.S_oeis_a004125.σ n = ∑ d ∈ n.divisors, d := rfl
  rw [hsplit, ← ha, ← hs] at hsum
  omega

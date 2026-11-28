import OMAStatements.S_oeis_a002050
import Mathlib

/-!
Modulo m, ordered partitions into j blocks contribute zero once j is
at least m, because the block-ordering factor is j factorial. The
binomial transforms of the remaining block counts satisfy a triangular
system with diagonal one. The right hand sides are shifted powers
minus one. Modulo each prime power dividing m, those powers either
vanish eventually or repeat by Euler's theorem. This gives the same
eventual period for the triangular system and for the sequence.
-/

namespace OMA.A002050

open Finset S_oeis_a002050

/-- The count of ordered partitions into a fixed number of blocks. -/
def weighted (n j : ℕ) : ℕ := j.factorial * Nat.stirlingSecond n j

/-- The binomial transform for one fixed number of blocks. -/
def transformed (n j : ℕ) : ℕ := ∑ k ∈ Icc 1 n, n.choose k * weighted k j

/-- The Stirling recursion in ordered-block form. -/
lemma weighted_succ (n j : ℕ) :
    weighted (n + 1) j = j * weighted n j + j * weighted n (j - 1) := by
  cases j with
  | zero => simp [weighted]
  | succ j =>
    simp only [weighted, Nat.stirlingSecond_succ_succ, Nat.add_sub_cancel_right]
    rw [Nat.factorial_succ j]
    ring

/-- Multiplication by x splits according to whether a distinguished position is already chosen. -/
lemma choose_weight (x j : ℕ) (hj : j ≤ x) :
    x * x.choose j = j * x.choose j + (j + 1) * x.choose (j + 1) := by
  rw [mul_comm (j + 1), Nat.choose_succ_right_eq, mul_comm (x.choose j), ← add_mul]
  rw [Nat.add_sub_of_le hj]

/-- Ordinary powers expand in the ordered-block counts. -/
lemma power_expansion (x n : ℕ) :
    x ^ n = ∑ j ∈ range (x + 1), x.choose j * weighted n j := by
  induction n with
  | zero =>
    rw [pow_zero, sum_range_succ']
    simp [weighted]
  | succ n ih =>
    have hshift :
        (∑ j ∈ range (x + 1), (j + 1) * x.choose (j + 1) * weighted n j) =
        ∑ j ∈ range (x + 1), j * x.choose j * weighted n (j - 1) := by
      rw [sum_range_succ, sum_range_succ' (f := fun j => j * x.choose j * weighted n (j - 1))]
      simp
    calc
      x ^ (n + 1) =
          ∑ j ∈ range (x + 1),
            (j * x.choose j * weighted n j + (j + 1) * x.choose (j + 1) * weighted n j) := by
        rw [pow_succ', ih, mul_sum]
        apply sum_congr rfl
        intro j hj
        rw [← add_mul, ← choose_weight x j (by simpa using hj), mul_assoc]
      _ = ∑ j ∈ range (x + 1), x.choose j * weighted (n + 1) j := by
        rw [sum_add_distrib, hshift, ← sum_add_distrib]
        apply sum_congr rfl
        intro j hj
        rw [weighted_succ]
        ring

/-- Binomial expansion after the transform gives a triangular system with unit diagonal. -/
lemma triangular (n x : ℕ) :
    (∑ j ∈ range (x + 1), x.choose j * transformed n j) + 1 = (x + 1) ^ n := by
  have hbin : (∑ k ∈ Icc 1 n, n.choose k * x ^ k) + 1 = (x + 1) ^ n := by
    have hI : (range (n + 1)).erase 0 = Icc 1 n := by
      ext k
      simp only [mem_erase, mem_range, mem_Icc]
      omega
    have h := sum_erase_add (s := range (n + 1)) (a := 0)
      (f := fun k => n.choose k * x ^ k) (by simp)
    rw [hI] at h
    simpa [add_pow, mul_comm] using h
  convert hbin using 2
  simp only [transformed, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [power_expansion x k, mul_sum]
  apply sum_congr rfl
  intro j hj
  ring

/-- Beyond exponent m, powers have period Euler's totient modulo m. -/
lemma eventual_power (m x n : ℕ) (hm : 0 < m) (hn : m ≤ n) :
    x ^ (n + m.totient) ≡ x ^ n [MOD m] := by
  rw [Nat.modEq_iff_dvd, Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpm
  have hlocal : x ^ (n + m.totient) ≡ x ^ n [MOD p ^ k] := by
    by_cases hpx : p ∣ x
    · have hk : k ≤ n := by
        have hle : p ^ k ≤ m := Nat.le_of_dvd hm hpm
        have htwo : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le _
        have hlt := Nat.lt_two_pow_self (n := k)
        omega
      have hd (r : ℕ) (hr : k ≤ r) : p ^ k ∣ x ^ r :=
        (pow_dvd_pow p hr).trans (pow_dvd_pow_of_dvd hpx r)
      exact (Nat.modEq_zero_iff_dvd.mpr (hd _ (by omega))).trans
        (Nat.modEq_zero_iff_dvd.mpr (hd _ hk)).symm
    · have hc : x.Coprime (p ^ k) := (hp.coprime_iff_not_dvd.mpr hpx).symm.pow_right _
      obtain ⟨q, hq⟩ := Nat.totient_dvd_of_dvd hpm
      rw [pow_add, hq, pow_mul]
      have he := (Nat.ModEq.pow_totient hc).pow q
      simpa using (Nat.ModEq.refl (x ^ n)).mul he
  exact Int.natCast_dvd.mp (Nat.modEq_iff_dvd.mp hlocal)

/-- Unit diagonal lets us recover the eventual period of every transformed block count. -/
lemma transform_period (m n : ℕ) (hm : 0 < m) (hn : m ≤ n) (j : ℕ) :
    (transformed (n + m.totient) j : ZMod m) = (transformed n j : ZMod m) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have h₁ := congrArg (fun z : ℕ => (z : ZMod m)) (triangular (n + m.totient) j)
    have h₂ := congrArg (fun z : ℕ => (z : ZMod m)) (triangular n j)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_sum, Nat.cast_mul] at h₁ h₂
    simp only [sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul] at h₁ h₂
    have hs : (∑ i ∈ range j, (j.choose i : ZMod m) * transformed (n + m.totient) i) =
        ∑ i ∈ range j, (j.choose i : ZMod m) * transformed n i := by
      apply sum_congr rfl
      intro i hi
      rw [ih i (mem_range.mp hi)]
    have hp := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (eventual_power m (j + 1) n hm hn)
    rw [hs, hp, ← h₂] at h₁
    exact add_left_cancel (add_right_cancel h₁)

/-- The factorial cuts the sum off at m fixed block counts. -/
lemma truncate (m n : ℕ) (hm : 0 < m) :
    (orderedBell n : ZMod m) = ∑ j ∈ range m, (weighted n j : ZMod m) := by
  simp only [orderedBell, weighted, Nat.cast_sum, Nat.cast_mul]
  let f : ℕ → ZMod m := fun j => (j.factorial : ZMod m) * Nat.stirlingSecond n j
  change (∑ j ∈ range (n + 1), f j) = ∑ j ∈ range m, f j
  have h₁ : (∑ j ∈ range (n + 1), f j) = ∑ j ∈ range (max (n + 1) m), f j := by
    apply sum_subset (range_mono (le_max_left _ _))
    intro j hj hjn
    have hj' : n < j := by simpa [Nat.lt_succ_iff] using hjn
    simp [f, Nat.stirlingSecond_eq_zero_of_lt hj']
  have h₂ : (∑ j ∈ range m, f j) = ∑ j ∈ range (max (n + 1) m), f j := by
    apply sum_subset (range_mono (le_max_right _ _))
    intro j hj hjm
    have hd : m ∣ j.factorial := Nat.dvd_factorial hm (by simpa using hjm)
    simp [f, (ZMod.natCast_eq_zero_iff _ _).mpr hd]
  exact h₁.trans h₂.symm

/-- After truncation the sequence is the sum of the transformed block counts. -/
lemma cast_sequence (m n : ℕ) (hm : 0 < m) :
    (a n : ZMod m) = ∑ j ∈ range m, (transformed n j : ZMod m) := by
  simp only [a, transformed, Nat.cast_sum, Nat.cast_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [truncate m k hm, mul_sum]

end OMA.A002050

open OMA.S_oeis_a002050 OMA.A002050 in
theorem OMA.solution : type_of% @OMA.S_oeis_a002050.main := by
  intro m hm
  refine ⟨m.totient, m, Nat.totient_pos.mpr hm, dvd_rfl, ?_⟩
  intro n hn
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [cast_sequence m _ hm, cast_sequence m _ hm]
  exact Finset.sum_congr rfl (fun j _ => transform_period m n hm hn j)

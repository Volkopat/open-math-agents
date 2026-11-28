import OMAStatements.S_oeis_a211343
import Mathlib

open OMA.S_oeis_a211343

private theorem sumConsecutive (k a : ℕ) :
    (∑ i ∈ Finset.range k, (a + 1 + i)) = k * (k + 1) / 2 + k * a := by
  have htri : (∑ i ∈ Finset.range k, (i + 1)) = k * (k + 1) / 2 := by
    have h : (∑ i ∈ Finset.range (k + 1), i) = ∑ i ∈ Finset.range k, (i + 1) := by
      rw [Finset.sum_range_succ' (fun i : ℕ => i) k]
      simp
    rw [← h, Finset.sum_range_id, Nat.add_sub_cancel, Nat.mul_comm (k + 1) k]
  calc
    (∑ i ∈ Finset.range k, (a + 1 + i)) = ∑ i ∈ Finset.range k, ((i + 1) + a) := by
      apply Finset.sum_congr rfl
      intro i _
      omega
    _ = k * (k + 1) / 2 + k * a := by
      simp [Finset.sum_add_distrib, htri]

private theorem sumAtEntry {n k : ℕ} (ht : 0 < T n k) :
    (∑ i ∈ Finset.range k, (T n k + i)) = n := by
  let b := k * (k + 1) / 2
  have h : b ≤ n ∧ k ∣ n - b := by
    by_contra hn
    have hz : T n k = 0 := if_neg hn
    omega
  have he : T n k = (n - b) / k + 1 := if_pos h
  rw [he, sumConsecutive]
  change b + k * ((n - b) / k) = n
  rw [Nat.mul_comm k, Nat.div_mul_cancel h.2]
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a211343.main := by
  constructor
  · intro n k _ _ _ ht
    exact sumAtEntry ht
  · intro n hn
    let P (k : ℕ) := ∃ a < n + 1, 1 ≤ a ∧ ∑ i ∈ Finset.range k, (a + i) = n
    have hOne : P 1 := ⟨n, by omega, hn, by simp⟩
    have hk : 1 ≤ A109814 n := Nat.le_findGreatest (P := P) hn hOne
    have hPk : P (A109814 n) := Nat.findGreatest_spec (P := P) hn hOne
    obtain ⟨a, _, ha, hs⟩ := hPk
    let k := A109814 n
    change (∑ i ∈ Finset.range k, (a + i)) = n at hs
    have he : a = (a - 1) + 1 := by omega
    rw [he, sumConsecutive] at hs
    have hbound : k * (k + 1) / 2 ≤ n := by omega
    have hdiv : k ∣ n - k * (k + 1) / 2 := ⟨a - 1, by omega⟩
    have hpos : 0 < T n k := by
      rw [T, if_pos ⟨hbound, hdiv⟩]
      exact Nat.zero_lt_succ _
    refine ⟨hk, hbound, hpos, ?_⟩
    intro l hl _
    by_contra hzero
    have hT : 0 < T n l := Nat.pos_of_ne_zero hzero
    have hs := sumAtEntry hT
    have hlpos : 0 < l := by omega
    have hi : 0 ∈ Finset.range l := Finset.mem_range.mpr hlpos
    have hTl : T n l ≤ n := by
      simpa [hs] using
        (Finset.single_le_sum (f := fun i => T n l + i) (fun i _ => Nat.zero_le _) hi)
    have hln : l ≤ n := by
      calc
        l = ∑ i ∈ Finset.range l, (1 : ℕ) := by simp
        _ ≤ ∑ i ∈ Finset.range l, (T n l + i) := by
          exact Finset.sum_le_sum (fun i _ => by omega)
        _ = n := hs
    have hPl : P l := ⟨T n l, by omega, hT, hs⟩
    exact (Nat.not_le_of_lt hl) (Nat.le_findGreatest (P := P) hln hPl)
import OMAStatements.S_oeis_a160849
import Mathlib

namespace OMA.A160849Proof

open OMA.S_oeis_a160849 PowerSeries


def Fn (t : ℕ) : ℤ := (1:ℤ) * secondDiff (t + 18) + (2:ℤ) * secondDiff (t + 17) + (4:ℤ) * secondDiff (t + 16) + (6:ℤ) * secondDiff (t + 15) + (8:ℤ) * secondDiff (t + 14) + (9:ℤ) * secondDiff (t + 13) + (9:ℤ) * secondDiff (t + 12) + (7:ℤ) * secondDiff (t + 11) + (4:ℤ) * secondDiff (t + 10) + (0:ℤ) * secondDiff (t + 9) + (-4:ℤ) * secondDiff (t + 8) + (-7:ℤ) * secondDiff (t + 7) + (-9:ℤ) * secondDiff (t + 6) + (-9:ℤ) * secondDiff (t + 5) + (-8:ℤ) * secondDiff (t + 4) + (-6:ℤ) * secondDiff (t + 3) + (-4:ℤ) * secondDiff (t + 2) + (-2:ℤ) * secondDiff (t + 1) + (-1:ℤ) * secondDiff (t + 0)

lemma s_per (t : ℕ) : secondDiff (t + 840) = secondDiff t := by
  unfold secondDiff
  simp only [Fin.sum_univ_eight]
  have h2 : ((t + 840) / 2) = t / 2 + 420 := by omega
  have e1 : (t + 840) % 1 = t % 1 := by omega
  have e2 : (t + 840) % 2 = t % 2 := by omega
  have e3 : (t + 840) % 3 = t % 3 := by omega
  have e4 : (t + 840) % 4 = t % 4 := by omega
  have e5 : (t + 840) % 5 = t % 5 := by omega
  have e6 : (t + 840) % 6 = t % 6 := by omega
  have e7 : (t + 840) % 7 = t % 7 := by omega
  have e8 : (t + 840) % 8 = t % 8 := by omega
  have f1 : (t / 2 + 420) % 1 = (t / 2) % 1 := by omega
  have f2 : (t / 2 + 420) % 2 = (t / 2) % 2 := by omega
  have f3 : (t / 2 + 420) % 3 = (t / 2) % 3 := by omega
  have f4 : (t / 2 + 420) % 4 = (t / 2) % 4 := by omega
  simp [h2, e1, e2, e3, e4, e5, e6, e7, e8, f1, f2, f3, f4]

lemma s_shift (x q : ℕ) : secondDiff (x + 840 * q) = secondDiff x := by
  induction q with
  | zero => simp
  | succ q ih => rw [show x + 840 * (q + 1) = (x + 840 * q) + 840 by ring, s_per, ih]

lemma Fn_per (t : ℕ) : Fn t = Fn (t % 840) := by
  have ht : t = t % 840 + 840 * (t / 840) := (Nat.mod_add_div t 840).symm
  unfold Fn
  generalize t % 840 = r at *
  generalize t / 840 = q at *
  subst ht
  simp only [show ∀ k, r + 840 * q + k = (r + k) + 840 * q from fun k => by ring, s_shift]

lemma Fn_chunk0 : (List.range 105).all (fun r => decide (Fn (r + 0) = 0)) = true := by decide +kernel

lemma Fn_chunk1 : (List.range 105).all (fun r => decide (Fn (r + 105) = 0)) = true := by decide +kernel

lemma Fn_chunk2 : (List.range 105).all (fun r => decide (Fn (r + 210) = 0)) = true := by decide +kernel

lemma Fn_chunk3 : (List.range 105).all (fun r => decide (Fn (r + 315) = 0)) = true := by decide +kernel

lemma Fn_chunk4 : (List.range 105).all (fun r => decide (Fn (r + 420) = 0)) = true := by decide +kernel

lemma Fn_chunk5 : (List.range 105).all (fun r => decide (Fn (r + 525) = 0)) = true := by decide +kernel

lemma Fn_chunk6 : (List.range 105).all (fun r => decide (Fn (r + 630) = 0)) = true := by decide +kernel

lemma Fn_chunk7 : (List.range 105).all (fun r => decide (Fn (r + 735) = 0)) = true := by decide +kernel

lemma Fn_zero_fin : ∀ r : Fin 840, Fn r.val = 0 := by
  intro r
  have hr := r.2
  by_cases h0 : r.val < 105
  · have := List.all_eq_true.1 Fn_chunk0 (r.val - 0) (List.mem_range.2 (by omega))
    have e : r.val - 0 + 0 = r.val := by omega
    simpa [e] using this
  by_cases h1 : r.val < 210
  · have := List.all_eq_true.1 Fn_chunk1 (r.val - 105) (List.mem_range.2 (by omega))
    have e : r.val - 105 + 105 = r.val := by omega
    simpa [e] using this
  by_cases h2 : r.val < 315
  · have := List.all_eq_true.1 Fn_chunk2 (r.val - 210) (List.mem_range.2 (by omega))
    have e : r.val - 210 + 210 = r.val := by omega
    simpa [e] using this
  by_cases h3 : r.val < 420
  · have := List.all_eq_true.1 Fn_chunk3 (r.val - 315) (List.mem_range.2 (by omega))
    have e : r.val - 315 + 315 = r.val := by omega
    simpa [e] using this
  by_cases h4 : r.val < 525
  · have := List.all_eq_true.1 Fn_chunk4 (r.val - 420) (List.mem_range.2 (by omega))
    have e : r.val - 420 + 420 = r.val := by omega
    simpa [e] using this
  by_cases h5 : r.val < 630
  · have := List.all_eq_true.1 Fn_chunk5 (r.val - 525) (List.mem_range.2 (by omega))
    have e : r.val - 525 + 525 = r.val := by omega
    simpa [e] using this
  by_cases h6 : r.val < 735
  · have := List.all_eq_true.1 Fn_chunk6 (r.val - 630) (List.mem_range.2 (by omega))
    have e : r.val - 630 + 630 = r.val := by omega
    simpa [e] using this
  by_cases h7 : r.val < 840
  · have := List.all_eq_true.1 Fn_chunk7 (r.val - 735) (List.mem_range.2 (by omega))
    have e : r.val - 735 + 735 = r.val := by omega
    simpa [e] using this
  omega

lemma Fn_zero (t : ℕ) : Fn t = 0 := by
  rw [Fn_per]; exact Fn_zero_fin ⟨t % 840, Nat.mod_lt _ (by norm_num)⟩


lemma a_rec' (m j : ℕ) (hj : 3 ≤ j) :
    a (m + (j + 1)) = 2 * a (m + j) - a (m + (j - 1)) + secondDiff (m + j) := by
  obtain ⟨k, hk⟩ : ∃ k, m + j = k + 3 := ⟨m + j - 3, by omega⟩
  have e1 : m + (j + 1) = k + 4 := by omega
  have e2 : m + (j - 1) = k + 2 := by omega
  rw [e1, e2, hk]
  rfl

lemma hG (m : ℕ) : a (m + 22) = - a (m + 20) + a (m + 17) + a (m + 16) + 2 * a (m + 15) + a (m + 14) + a (m + 13) - a (m + 11) - a (m + 10) - 2 * a (m + 9) - a (m + 8) - a (m + 7) + a (m + 4) + a (m + 2) := by
  have r3 := a_rec' m 3 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r3
  have r4 := a_rec' m 4 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r4
  have r5 := a_rec' m 5 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r5
  have r6 := a_rec' m 6 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r6
  have r7 := a_rec' m 7 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r7
  have r8 := a_rec' m 8 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r8
  have r9 := a_rec' m 9 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r9
  have r10 := a_rec' m 10 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r10
  have r11 := a_rec' m 11 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r11
  have r12 := a_rec' m 12 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r12
  have r13 := a_rec' m 13 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r13
  have r14 := a_rec' m 14 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r14
  have r15 := a_rec' m 15 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r15
  have r16 := a_rec' m 16 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r16
  have r17 := a_rec' m 17 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r17
  have r18 := a_rec' m 18 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r18
  have r19 := a_rec' m 19 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r19
  have r20 := a_rec' m 20 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r20
  have r21 := a_rec' m 21 (by norm_num)
  simp only [Nat.reduceAdd, Nat.reduceSub] at r21
  have hF := Fn_zero (m + 3)
  simp only [Fn, add_assoc, Nat.reduceAdd] at hF
  linarith

lemma a_small : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 83 ∧ a 3 = 164 ∧ a 4 = 299 ∧ a 5 = 454 ∧ a 6 = 673 ∧ a 7 = 894 ∧ a 8 = 1183 ∧ a 9 = 1492 ∧ a 10 = 1855 ∧ a 11 = 2218 ∧ a 12 = 2653 ∧ a 13 = 3102 ∧ a 14 = 3623 ∧ a 15 = 4148 ∧ a 16 = 4719 ∧ a 17 = 5310 ∧ a 18 = 5973 ∧ a 19 = 6638 ∧ a 20 = 7375 ∧ a 21 = 8124 ∧ a 22 = 8923 := by
  decide +kernel


def dl (i : ℕ) : ℤ := ([1, 0, 1, 0, 0, -1, -1, -2, -1, -1, 0, 1, 1, 2, 1, 1, 0, 0, -1, 0, -1] : List ℤ).getD i 0
def nl (i : ℕ) : ℤ := ([0, 1, 83, 165, 382, 618, 971, 1264, 1607, 1756, 1873, 1738, 1571, 1228, 935, 600, 373, 174, 92, 19, 9, 9] : List ℤ).getD i 0

lemma hD : ((1-X)^3*(1+X)*(1-X+X^2)*(1+X^2)*(1+X+X^2)*(1+X+X^2+X^3+X^4)*(1+X+X^2+X^3+X^4+X^5+X^6) : PowerSeries ℤ) =
    ∑ i ∈ Finset.range 21, C (dl i) * X ^ i := by
  simp [Finset.sum_range_succ, dl]
  ring

lemma hN : (X*(1 + 83*X + 165*X^2 + 382*X^3 + 618*X^4 + 971*X^5 + 1264*X^6 + 1607*X^7 + 1756*X^8 + 1873*X^9 + 1738*X^10 + 1571*X^11 + 1228*X^12 + 935*X^13 + 600*X^14 + 373*X^15 + 174*X^16 + 92*X^17 + 19*X^18 + 9*X^19 + 9*X^20) : PowerSeries ℤ) =
    ∑ i ∈ Finset.range 22, C (nl i) * X ^ i := by
  simp [Finset.sum_range_succ, nl]
  ring

lemma small : ∀ n : Fin 22, ∑ i ∈ Finset.range 21, dl i * (if i ≤ n.val then (a (n.val - i) : ℤ) else 0) =
    ∑ i ∈ Finset.range 22, nl i * (if n.val = i then (1:ℤ) else 0) := by
  decide +kernel

lemma big (m : ℕ) : ∑ i ∈ Finset.range 21, dl i * (if i ≤ m + 22 then (a (m + 22 - i) : ℤ) else 0) = 0 := by
  have := hG m
  rw [Finset.sum_congr rfl (fun i hi => by rw [if_pos (by have := Finset.mem_range.1 hi; omega)])]
  simp [Finset.sum_range_succ, dl]
  linarith


lemma gf_proof :
    mk a * ((1-X)^3*(1+X)*(1-X+X^2)*(1+X^2)*(1+X+X^2)*(1+X+X^2+X^3+X^4)*(1+X+X^2+X^3+X^4+X^5+X^6) : PowerSeries ℤ) = X*(1 + 83*X + 165*X^2 + 382*X^3 + 618*X^4 + 971*X^5 + 1264*X^6 + 1607*X^7 + 1756*X^8 + 1873*X^9 + 1738*X^10 + 1571*X^11 + 1228*X^12 + 935*X^13 + 600*X^14 + 373*X^15 + 174*X^16 + 92*X^17 + 19*X^18 + 9*X^19 + 9*X^20) := by
  rw [hD, hN, Finset.mul_sum]
  ext n
  simp only [map_sum]
  have l : ∀ i : ℕ, coeff n (mk a * (C (dl i) * X ^ i)) = dl i * (if i ≤ n then (a (n - i) : ℤ) else 0) := by
    intro i
    rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow']
    simp [coeff_mk]
  have r : ∀ i : ℕ, coeff n (C (nl i) * X ^ i) = nl i * (if n = i then 1 else 0) := by
    intro i
    rw [coeff_C_mul, coeff_X_pow]
  simp only [l, r]
  by_cases hn : n < 22
  · exact small ⟨n, hn⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 22 := ⟨n - 22, by omega⟩
    have hz : ∑ i ∈ Finset.range 22, nl i * (if m + 22 = i then (1:ℤ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have := Finset.mem_range.1 hi
      rw [if_neg (by omega)]; simp
    rw [hz]
    exact big m

lemma main_proof :
    mk a * ((1-X)^3*(1+X)*(1-X+X^2)*(1+X^2)*(1+X+X^2)*(1+X+X^2+X^3+X^4)*(1+X+X^2+X^3+X^4+X^5+X^6)) = X*(1 + 83*X + 165*X^2 + 382*X^3 + 618*X^4 + 971*X^5 + 1264*X^6 + 1607*X^7 + 1756*X^8 + 1873*X^9 + 1738*X^10 + 1571*X^11 + 1228*X^12 + 935*X^13 + 600*X^14 + 373*X^15 + 174*X^16 + 92*X^17 + 19*X^18 + 9*X^19 + 9*X^20) ∧
    ∀ n : ℕ, 21 < n → a n = - a (n-2) + a (n-5) + a (n-6) + 2*a (n-7) + a (n-8) + a (n-9) - a (n-11) - a (n-12) - 2*a (n-13) - a (n-14) - a (n-15) + a (n-18) + a (n-20) := by
  refine ⟨gf_proof, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 22 := ⟨n - 22, by omega⟩
  rw [show m + 22 - 2 = m + 20 from by omega, show m + 22 - 5 = m + 17 from by omega, show m + 22 - 6 = m + 16 from by omega, show m + 22 - 7 = m + 15 from by omega, show m + 22 - 8 = m + 14 from by omega, show m + 22 - 9 = m + 13 from by omega, show m + 22 - 11 = m + 11 from by omega, show m + 22 - 12 = m + 10 from by omega, show m + 22 - 13 = m + 9 from by omega, show m + 22 - 14 = m + 8 from by omega, show m + 22 - 15 = m + 7 from by omega, show m + 22 - 18 = m + 4 from by omega, show m + 22 - 20 = m + 2 from by omega]
  exact hG m

end OMA.A160849Proof

open OMA.A160849Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a160849.main := main_proof


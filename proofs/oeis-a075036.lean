import OMAStatements.S_oeis_a075036
import Mathlib

-- Disproof of the A075036 conjecture at n = 6: a 6 = 735 = 3 * 5 * 7^2 is odd,
-- but the 7-adic order of 735 (namely 2) exceeds its 3-adic order (namely 1).

namespace A075036

open OMA.S_oeis_a075036

/-- computable divisor count by trial division over range (k + 1) -/
def cnt (k : ℕ) : ℕ := ((List.range (k + 1)).filter (fun i => k % i == 0)).length

theorem d_eq (k : ℕ) (hk : k ≠ 0) : d k = cnt k := by
  unfold d cnt
  rw [← Nat.filter_dvd_eq_divisors hk]
  show ((List.range (k + 1)).filter (fun i => decide (i ∣ k))).length = _
  apply congrArg List.length
  apply List.filter_congr
  intro i _
  by_cases h : k % i = 0 <;> simp [Nat.dvd_iff_mod_eq_zero, h]

/-- no k in [s, s + n) has cnt k = 12 and cnt (k + 1) = 12 -/
def chkR (s n : ℕ) : Bool := (List.range' s n).all (fun k => !(cnt k == 12 && cnt (k + 1) == 12))

theorem c0 : chkR 0 260 = true := by decide +kernel
theorem c1 : chkR 260 108 = true := by decide +kernel
theorem c2 : chkR 368 82 = true := by decide +kernel
theorem c3 : chkR 450 70 = true := by decide +kernel
theorem c4 : chkR 520 61 = true := by decide +kernel
theorem c5 : chkR 581 56 = true := by decide +kernel
theorem c6 : chkR 637 51 = true := by decide +kernel
theorem c7 : chkR 688 47 = true := by decide +kernel

theorem cnt735 : cnt 735 = 12 ∧ cnt 736 = 12 := by decide +kernel

theorem fromR (k s n : ℕ) (h : chkR s n = true) (hs : s ≤ k) (hn : k < s + n) :
    (!(cnt k == 12 && cnt (k + 1) == 12)) = true :=
  List.all_eq_true.mp h k (List.mem_range'_1.mpr ⟨hs, hn⟩)

theorem allR (k : ℕ) (hk : k < 735) : (!(cnt k == 12 && cnt (k + 1) == 12)) = true := by
  by_cases h1 : k < 260
  · exact fromR k 0 260 c0 (by omega) (by omega)
  by_cases h2 : k < 368
  · exact fromR k 260 108 c1 (by omega) (by omega)
  by_cases h3 : k < 450
  · exact fromR k 368 82 c2 (by omega) (by omega)
  by_cases h4 : k < 520
  · exact fromR k 450 70 c3 (by omega) (by omega)
  by_cases h5 : k < 581
  · exact fromR k 520 61 c4 (by omega) (by omega)
  by_cases h6 : k < 637
  · exact fromR k 581 56 c5 (by omega) (by omega)
  by_cases h7 : k < 688
  · exact fromR k 637 51 c6 (by omega) (by omega)
  exact fromR k 688 47 c7 (by omega) (by omega)

theorem below (k : ℕ) (hk : k < 735) : ¬ (d k = 2 * 6 ∧ d (k + 1) = 2 * 6) := by
  rintro ⟨h1, h2⟩
  have h1' : d k = 12 := h1
  have h2' : d (k + 1) = 12 := h2
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    simp [d] at h1'
  · rw [d_eq k (by omega)] at h1'
    rw [d_eq (k + 1) (by omega)] at h2'
    have hc := allR k hk
    rw [h1', h2'] at hc
    exact absurd hc (by decide)

theorem mem735 : d 735 = 2 * 6 ∧ d (735 + 1) = 2 * 6 := by
  rw [d_eq 735 (by norm_num), d_eq (735 + 1) (by norm_num)]
  exact cnt735

theorem a6 : a 6 = 735 := by
  unfold a
  apply le_antisymm (Nat.sInf_le mem735)
  by_contra hlt0
  have hlt := not_le.mp hlt0
  have hm : sInf {k : ℕ | d k = 2 * 6 ∧ d (k + 1) = 2 * 6} ∈ {k : ℕ | d k = 2 * 6 ∧ d (k + 1) = 2 * 6} :=
    Nat.sInf_mem ⟨735, mem735⟩
  exact below _ hlt hm

theorem v7 : 2 ≤ padicValNat 7 735 :=
  (padicValNat_dvd_iff_le_of_ne_one (p := 7) (a := 735) (n := 2) (by norm_num)
    (by norm_num)).mp (by norm_num)

theorem v3 : padicValNat 3 735 ≤ 1 := by
  by_contra hc
  have h := (padicValNat_dvd_iff_le_of_ne_one (p := 3) (a := 735) (n := 2) (by norm_num)
    (by norm_num)).mpr (by omega)
  revert h
  decide

end A075036

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a075036.main) := by
  intro h
  have h6 := (h 6 (by norm_num)).2
  rw [A075036.a6] at h6
  have hodd : Odd (735 : ℕ) := by decide
  have hle : padicValNat 7 735 ≤ padicValNat 3 735 := (h6 hodd).1 7 (by norm_num)
  have h7 := A075036.v7
  have h3 := A075036.v3
  omega

import OMAStatements.S_oeis_a341724
import Mathlib

namespace OMA.P_oeis_a341724

open OMA.S_oeis_a341724

private lemma M_succ (m : ℕ) :
    M (m + 1) = 2 * ∑ j ∈ (Finset.range (m + 2)).filter Odd, (m + 1).choose j * M (m + 1 - j) := by
  rw [M]
  congr 1
  exact Finset.sum_attach _ (fun j => (m + 1).choose j * M (m + 1 - j))

private lemma M_pos : ∀ n : ℕ, 0 < M n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [M]
    | succ m =>
      rw [M_succ]
      have hmem : 1 ∈ (Finset.range (m + 2)).filter Odd := by
        simp [Odd]
      have hterm : 0 < (m + 1).choose 1 * M (m + 1 - 1) := by
        have h1 : 0 < (m + 1).choose 1 := by simp
        have h2 : 0 < M m := ih m (by omega)
        simpa using Nat.mul_pos h1 h2
      have hsum : 0 < ∑ j ∈ (Finset.range (m + 2)).filter Odd,
          (m + 1).choose j * M (m + 1 - j) :=
        Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨1, hmem, hterm⟩
      omega

private lemma padicValNat_choose_of_odd {n j : ℕ} (hj : Odd j) (hjn : j ≤ n) :
    padicValNat 2 n ≤ padicValNat 2 (n.choose j) := by
  have hjpos : 0 < j := by obtain ⟨t, rfl⟩ := hj; omega
  have hnpos : 0 < n := lt_of_lt_of_le hjpos hjn
  have hmul : j * n.choose j = n * (n - 1).choose (j - 1) := by
    have := Nat.add_one_mul_choose_eq (n - 1) (j - 1)
    have h1 : n - 1 + 1 = n := by omega
    have h2 : j - 1 + 1 = j := by omega
    rw [h1, h2] at this
    linarith
  have hch_ne : n.choose j ≠ 0 := (Nat.choose_pos hjn).ne'
  have hch'_ne : (n - 1).choose (j - 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hj_odd : ¬ (2 ∣ j) := by
    obtain ⟨t, rfl⟩ := hj; omega
  have hvj : padicValNat 2 j = 0 := padicValNat.eq_zero_of_not_dvd hj_odd
  have h1 := congr_arg (padicValNat 2) hmul
  rw [padicValNat.mul hjpos.ne' hch_ne, padicValNat.mul hnpos.ne' hch'_ne, hvj, zero_add] at h1
  omega

private lemma padicValNat_M_ge : ∀ n : ℕ, 0 < n → padicValNat 2 n + 1 ≤ padicValNat 2 (M n) := by
  intro n hn
  cases n with
  | zero => omega
  | succ m =>
    rw [M_succ]
    set S := ∑ j ∈ (Finset.range (m + 2)).filter Odd, (m + 1).choose j * M (m + 1 - j)
    have hSpos : 0 < S := by
      have hmem : 1 ∈ (Finset.range (m + 2)).filter Odd := by simp [Odd]
      refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨1, hmem, ?_⟩
      simpa using Nat.mul_pos (by simp : 0 < (m + 1).choose 1) (M_pos m)
    have hpow_dvd : 2 ^ padicValNat 2 (m + 1) ∣ S := by
      refine Finset.dvd_sum (fun j hj => ?_)
      obtain ⟨hjr, hjodd⟩ := Finset.mem_filter.mp hj
      have hjn : j ≤ m + 1 := by rw [Finset.mem_range] at hjr; omega
      have hval : padicValNat 2 (m + 1) ≤ padicValNat 2 ((m + 1).choose j) :=
        padicValNat_choose_of_odd hjodd hjn
      have hch_ne : (m + 1).choose j ≠ 0 := (Nat.choose_pos hjn).ne'
      have hd1 : 2 ^ padicValNat 2 ((m + 1).choose j) ∣ (m + 1).choose j :=
        pow_padicValNat_dvd
      have hd2 : 2 ^ padicValNat 2 (m + 1) ∣ 2 ^ padicValNat 2 ((m + 1).choose j) :=
        Nat.pow_dvd_pow 2 hval
      exact dvd_mul_of_dvd_left (hd2.trans hd1) _
    have h2S : 2 ^ (padicValNat 2 (m + 1) + 1) ∣ 2 * S := by
      rw [pow_succ']
      exact Nat.mul_dvd_mul_left 2 hpow_dvd
    exact (padicValNat_dvd_iff_le (by omega : 2 * S ≠ 0)).mp h2S

private lemma padicValNat_choose_pow_two {m k : ℕ} (hk0 : 0 < k) (hkm : k < 2 ^ m) :
    m ≤ padicValNat 2 ((2 ^ m).choose k) + padicValNat 2 k := by
  have hmul : k * (2 ^ m).choose k = 2 ^ m * (2 ^ m - 1).choose (k - 1) := by
    have := Nat.add_one_mul_choose_eq (2 ^ m - 1) (k - 1)
    have h1 : 2 ^ m - 1 + 1 = 2 ^ m := by have := Nat.one_le_two_pow (n := m); omega
    have h2 : k - 1 + 1 = k := by omega
    rw [h1, h2] at this
    linarith
  have hch_ne : (2 ^ m).choose k ≠ 0 := (Nat.choose_pos hkm.le).ne'
  have hch'_ne : (2 ^ m - 1).choose (k - 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have h1 := congr_arg (padicValNat 2) hmul
  rw [padicValNat.mul hk0.ne' hch_ne,
      padicValNat.mul (by positivity : (2 ^ m : ℕ) ≠ 0) hch'_ne,
      padicValNat.prime_pow] at h1
  omega

private lemma padicValNat_sub_pow_two {m k : ℕ} (hk0 : 0 < k) (hkm : k < 2 ^ m) :
    padicValNat 2 (2 ^ m - k) = padicValNat 2 k := by
  have hv_lt : padicValNat 2 k < m := by
    by_contra hge
    push Not at hge
    have hd : 2 ^ m ∣ k := (Nat.pow_dvd_pow 2 hge).trans pow_padicValNat_dvd
    exact absurd (Nat.le_of_dvd hk0 hd) (by omega)
  have h1 : padicValNat 2 k ≤ padicValNat 2 (2 ^ m - k) := by
    have hd1 : 2 ^ padicValNat 2 k ∣ 2 ^ m := Nat.pow_dvd_pow 2 hv_lt.le
    have hd2 : 2 ^ padicValNat 2 k ∣ k := pow_padicValNat_dvd
    exact (padicValNat_dvd_iff_le (by omega : 2 ^ m - k ≠ 0)).mp (Nat.dvd_sub hd1 hd2)
  have h2 : padicValNat 2 (2 ^ m - k) ≤ padicValNat 2 k := by
    have hv'_lt : padicValNat 2 (2 ^ m - k) < m := by
      by_contra hge
      push Not at hge
      have hd : 2 ^ m ∣ 2 ^ m - k := (Nat.pow_dvd_pow 2 hge).trans pow_padicValNat_dvd
      exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    have hd1 : 2 ^ padicValNat 2 (2 ^ m - k) ∣ 2 ^ m := Nat.pow_dvd_pow 2 hv'_lt.le
    have hd2 : 2 ^ padicValNat 2 (2 ^ m - k) ∣ 2 ^ m - k := pow_padicValNat_dvd
    have hk_eq : k = 2 ^ m - (2 ^ m - k) := by omega
    have hdsub : 2 ^ padicValNat 2 (2 ^ m - k) ∣ 2 ^ m - (2 ^ m - k) := Nat.dvd_sub hd1 hd2
    rw [← hk_eq] at hdsub
    exact (padicValNat_dvd_iff_le hk0.ne').mp hdsub
  exact le_antisymm h2 h1

end OMA.P_oeis_a341724

theorem OMA.solution : type_of% @OMA.S_oeis_a341724.main := by
  open OMA.S_oeis_a341724 OMA.P_oeis_a341724 in
  constructor
  · intro p k hp hk0 hkp
    unfold T
    have hd : p ∣ p.choose k := hp.dvd_choose_self hk0.ne' hkp
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hd) _) _
  · intro m k hkm
    unfold T
    refine dvd_mul_of_dvd_right ?_ _
    norm_cast
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [Nat.choose_zero_right, one_mul, Nat.sub_zero]
      have hpos : 0 < 2 ^ m := by positivity
      have hval := padicValNat_M_ge (2 ^ m) hpos
      rw [padicValNat.prime_pow] at hval
      exact (padicValNat_dvd_iff_le (M_pos (2 ^ m)).ne').mpr (by omega)
    · have hch := padicValNat_choose_pow_two hk0 hkm
      have hM := padicValNat_M_ge (2 ^ m - k) (by omega)
      have hsub := padicValNat_sub_pow_two hk0 hkm
      have hch_ne : (2 ^ m).choose k ≠ 0 := (Nat.choose_pos hkm.le).ne'
      have hM_ne : M (2 ^ m - k) ≠ 0 := (M_pos _).ne'
      have htot : m ≤ padicValNat 2 ((2 ^ m).choose k * M (2 ^ m - k)) := by
        rw [padicValNat.mul hch_ne hM_ne]
        omega
      exact (padicValNat_dvd_iff_le (mul_ne_zero hch_ne hM_ne)).mpr htot

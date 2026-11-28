import OMAStatements.S_mo_298012
import Mathlib

namespace OMA.CappedMajorization

open Finset

private theorem cauchy {ι : Type} (s : Finset ι) (z : ι → ℝ) :
    (∑ i ∈ s, z i)^2 ≤ (s.card : ℝ) * ∑ i ∈ s, (z i)^2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) z

private theorem oneValue {n : ℕ} (hn : 1 ≤ n) (i : Fin n) (a b : ℝ) :
    (∑ j : Fin n, if j = i then a else b) = a + ((n : ℝ)-1)*b := by
  classical
  have hmem : i ∈ (univ : Finset (Fin n)) := mem_univ _
  have hc : ((univ.erase i).card : ℝ) = (n : ℝ)-1 := by
    rw [card_erase_of_mem hmem, card_univ, Fintype.card_fin, Nat.cast_sub hn]
    norm_num
  have hconst : (∑ j ∈ univ.erase i, if j = i then a else b) = ((n : ℝ)-1)*b := by
    rw [sum_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
    rw [sum_const, nsmul_eq_mul, hc]
  have hsplit := sum_erase_add univ (fun j : Fin n => if j = i then a else b) hmem
  simpa [hconst, add_comm] using hsplit.symm

private theorem increments (a N : ℝ) (ha : 0 ≤ a) (hN : 0 ≤ N) (k : ℕ) :
    (∑ i ∈ range k, min a (max 0 (N - (i : ℝ)*a))) = min ((k : ℝ)*a) N := by
  induction k with
  | zero => simp [hN]
  | succ k ih =>
    rw [sum_range_succ, ih, Nat.cast_succ]
    have hk : (k : ℝ)*a ≤ ((k : ℝ)+1)*a := by nlinarith
    by_cases low : N ≤ (k : ℝ)*a
    · rw [min_eq_right low, max_eq_left (sub_nonpos.mpr low), min_eq_right ha,
          add_zero, min_eq_right (low.trans hk)]
    · have hlow := le_of_lt (lt_of_not_ge low)
      rw [min_eq_left hlow, max_eq_right (sub_nonneg.mpr hlow)]
      by_cases high : N ≤ ((k : ℝ)+1)*a
      · rw [min_eq_right (show N - (k : ℝ)*a ≤ a by nlinarith),
            min_eq_right high]
        ring
      · rw [min_eq_left (show a ≤ N - (k : ℝ)*a by
              nlinarith [le_of_lt (lt_of_not_ge high)]),
            min_eq_left (le_of_lt (lt_of_not_ge high))]
        ring

theorem result : type_of% @OMA.S_mo_298012.main := by
  intro n hn x m hx hs hsq
  let N : ℝ := n
  let D : ℝ := (m-N)*(1-1/N)
  let a : ℝ := 1 + Real.sqrt D
  let y := fun i : ℕ => min a (max 0 (N - (i : ℝ)*a))
  change 1 ≤ a ∧ a ≤ N ∧ Antitone y ∧ (∀ i, 0 ≤ y i) ∧
    (∑ i ∈ range n, y i) = N ∧
    (∀ k : ℕ, (∑ i ∈ range k, y i) = min ((k : ℝ)*a) N) ∧
    (∀ s : Finset (Fin n), (∑ i ∈ s, x i) ≤ ∑ i ∈ range s.card, y i) ∧
    (∀ i : Fin n, ∃ z : Fin n → ℝ, (∀ j, 0 ≤ z j) ∧
      (∑ j, z j) = N ∧ (∑ j, (z j)^2) = m ∧ z i = a)
  change (∑ i, x i) = N at hs
  have hN : (2 : ℝ) ≤ N := by
    change (2 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hNp : 0 < N := by linarith
  have hN1 : 0 < N-1 := by linarith
  have hxN (i : Fin n) : x i ≤ N := by
    rw [← hs]
    exact single_le_sum (fun j _ => hx j) (mem_univ i)
  have mlo : N ≤ m := by
    have h := cauchy univ x
    simp only [card_univ, Fintype.card_fin, hs, hsq] at h
    apply (mul_le_mul_iff_left₀ hNp).mp
    nlinarith only [h]
  have mhi : m ≤ N^2 := calc
    m = ∑ i, (x i)^2 := hsq.symm
    _ ≤ ∑ i, N * x i := sum_le_sum (fun i _ => by
      simpa [pow_two] using mul_le_mul_of_nonneg_right (hxN i) (hx i))
    _ = N^2 := by rw [← mul_sum, hs]; ring
  have Dform : D*N = (m-N)*(N-1) := by
    dsimp [D]
    field_simp [hNp.ne']
  have Dpos : 0 ≤ D := by
    apply (mul_le_mul_iff_left₀ hNp).mp
    rw [zero_mul, Dform]
    exact mul_nonneg (sub_nonneg.mpr mlo) hN1.le
  have Dtop : D ≤ (N-1)^2 := by
    apply (mul_le_mul_iff_left₀ hNp).mp
    rw [Dform]
    nlinarith only [mul_le_mul_of_nonneg_right (sub_le_sub_right mhi N) hN1.le]
  have ha : 1 ≤ a := by
    dsimp [a]
    linarith [Real.sqrt_nonneg D]
  have ha0 : 0 ≤ a := by linarith
  have haN : a ≤ N := by
    have h := (Real.sqrt_le_left hN1.le).mpr Dtop
    dsimp [a]
    linarith
  have xi (i : Fin n) : x i ≤ a := by
    classical
    have hmem : i ∈ (univ : Finset (Fin n)) := mem_univ _
    have s1 : (∑ j ∈ univ.erase i, x j) = N - x i := by
      have h := sum_erase_add univ x hmem
      rw [hs] at h
      linarith
    have s2 : (∑ j ∈ univ.erase i, (x j)^2) = m - (x i)^2 := by
      have h := sum_erase_add univ (fun j => (x j)^2) hmem
      rw [hsq] at h
      linarith
    have hc : ((univ.erase i).card : ℝ) = N-1 := by
      rw [card_erase_of_mem hmem, card_univ, Fintype.card_fin,
        Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num [N]
    have h := cauchy (univ.erase i) x
    rw [s1, s2, hc] at h
    have hsq' : (x i-1)^2 ≤ D := by
      apply (mul_le_mul_iff_left₀ hNp).mp
      rw [Dform]
      nlinarith only [h]
    have hroot := Real.le_sqrt_of_sq_le hsq'
    dsimp [a]
    linarith
  have sum_y (k : ℕ) : (∑ i ∈ range k, y i) = min ((k : ℝ)*a) N :=
    increments a N ha0 hNp.le k
  refine ⟨ha, haN, ?_, ?_, ?_, sum_y, ?_, ?_⟩
  · intro i j hij
    dsimp [y]
    apply min_le_min le_rfl
    apply max_le_max le_rfl
    exact sub_le_sub_left (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) ha0) _
  · intro i
    exact le_min ha0 (le_max_left _ _)
  · rw [sum_y, min_eq_right]
    calc
      N = N * 1 := by ring
      _ ≤ N*a := mul_le_mul_of_nonneg_left ha hNp.le
  · intro s
    rw [sum_y]
    apply le_min
    · calc
        (∑ i ∈ s, x i) ≤ ∑ _i ∈ s, a := sum_le_sum (fun i _ => xi i)
        _ = (s.card : ℝ)*a := by simp [nsmul_eq_mul]
    · rw [← hs]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hx i)
  · intro i
    classical
    let b := (N-a)/(N-1)
    let z := fun j : Fin n => if j=i then a else b
    have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr haN) hN1.le
    have hprod : b*(N-1) = N-a := div_mul_cancel₀ _ hN1.ne'
    have he : (a-1)^2*N = (m-N)*(N-1) := by
      have h : (a-1)^2 = D := by
        dsimp [a]
        simpa only [add_sub_cancel_left] using Real.sq_sqrt Dpos
      rw [h, Dform]
    have henergy : a^2+(N-1)*b^2=m := by
      have hpoly : (N-1)*a^2+(N-a)^2=(N-1)*m := by
        nlinarith only [he]
      apply mul_right_cancel₀ hN1.ne'
      calc
        (a^2+(N-1)*b^2)*(N-1) = (N-1)*a^2+(b*(N-1))^2 := by ring
        _ = (N-1)*m := by rw [hprod, hpoly]
        _ = m*(N-1) := mul_comm _ _
    refine ⟨z, ?_, ?_, ?_, by simp [z]⟩
    · intro j
      by_cases h : j=i <;> simp [z, h, ha0, hb]
    · rw [show (∑ j, z j) = a+(N-1)*b from oneValue (by omega) i a b]
      linarith
    · change (∑ j : Fin n, (if j=i then a else b)^2) = m
      simp only [apply_ite (fun x : ℝ => x^2)]
      rw [oneValue (by omega) i (a^2) (b^2)]
      exact henergy

end OMA.CappedMajorization

theorem OMA.solution : type_of% @OMA.S_mo_298012.main :=
  OMA.CappedMajorization.result
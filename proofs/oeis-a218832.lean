import OMAStatements.S_oeis_a218832
import Mathlib

/-!
# A218832: positive solutions of x + y + 2z = n^2

Let c(m) be the number of positive solutions of x + y + 2z = m. The solutions of
x + y + 2z = m + 2 with z ≥ 2 correspond to the solutions for m (lower z by one), and those
with z = 1 are the m - 1 pairs x + y = m. So c(m + 2) = c(m) + (m - 1) for m ≥ 1, with
c(1) = c(2) = 0, and induction gives 8 c(m) = 2m^2 - 8m + 7 + (-1)^m for m ≥ 1. Since
(-1)^(n^2) = (-1)^n, this is the closed form at m = n^2. For the g.f., the denominator
(x-1)^5 (x+1) expands to x^6 - 4x^5 + 5x^4 - 5x^2 + 4x - 1; the coefficients of degree at most
6 are checked from the values a(0), ..., a(6), and from degree 7 on the coefficient vanishes by
the closed form.
-/

namespace OMA.P218832

open OMA.S_oeis_a218832 PowerSeries

/-- The positive solutions of x + y + 2z = m, as a Finset. -/
def S (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 m ×ˢ Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter
    (fun p => p.1 + p.2.1 + 2 * p.2.2 = m)

lemma set_eq (m : ℕ) :
    {p : ℕ × ℕ × ℕ | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.1 + p.2.1 + 2 * p.2.2 = m} =
      ↑(S m) := by
  ext ⟨x, y, z⟩
  simp only [S, Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc]
  omega

lemma a_eq (n : ℕ) : a n = (S (n ^ 2)).card := by
  unfold a
  rw [set_eq, Set.ncard_coe_finset]

/-- c(m + 2) = c(m) + (m - 1). -/
lemma card_step (m : ℕ) (hm : 1 ≤ m) : (S (m + 2)).card = (S m).card + (m - 1) := by
  rw [← Finset.card_filter_add_card_filter_not (fun p : ℕ × ℕ × ℕ => p.2.2 = 1), add_comm]
  congr 1
  · apply Finset.card_nbij' (fun p => (p.1, p.2.1, p.2.2 - 1)) (fun p => (p.1, p.2.1, p.2.2 + 1))
    · intro p hp
      simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
      omega
    · intro p hp
      simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
      omega
    · intro p hp
      simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      ext <;> simp
      omega
    · intro p hp
      simp
  · have hc : (Finset.Icc 1 (m - 1)).card = m - 1 := by simp
    rw [← hc]
    apply Finset.card_nbij' (fun p => p.1) (fun x => (x, m - x, 1))
    · intro p hp
      simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
      omega
    · intro x hx
      simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        and_true] at hx ⊢
      omega
    · intro p hp
      simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      ext <;> simp <;> omega
    · intro x hx
      simp

lemma S1 : (S 1).card = 0 := by decide

lemma S2 : (S 2).card = 0 := by decide

/-- 8 c(m) = 2m^2 - 8m + 7 + (-1)^m for m ≥ 1. -/
lemma key (m : ℕ) (hm : 1 ≤ m) :
    8 * ((S m).card : ℤ) = 2 * (m : ℤ) ^ 2 - 8 * m + 7 + (-1) ^ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | _ | k
    · omega
    · rw [S1]; norm_num
    · rw [S2]; norm_num
    · have h := ih (k + 1) (by omega) (by omega)
      rw [show k + 1 + 1 + 1 = (k + 1) + 2 by ring, card_step (k + 1) (by omega),
        show k + 1 - 1 = k by omega]
      push_cast at h ⊢
      linear_combination h

lemma neg_one_pow_sq (n : ℕ) : (-1 : ℤ) ^ (n ^ 2) = (-1) ^ n := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, (Nat.even_pow.mpr ⟨h, two_ne_zero⟩).neg_one_pow]
  · rw [h.neg_one_pow, (Odd.pow h).neg_one_pow]

/-- The closed form, multiplied by 8, in ℤ. -/
lemma closed (n : ℕ) (hn : 1 ≤ n) :
    8 * (a n : ℤ) = 7 + (-1) ^ n - 8 * (n : ℤ) ^ 2 + 2 * (n : ℤ) ^ 4 := by
  rw [a_eq, key (n ^ 2) (Nat.one_le_pow _ _ hn), neg_one_pow_sq]
  push_cast
  ring

lemma a_zero : a 0 = 0 := by
  rw [a_eq]
  decide

lemma cXm (u : ℕ → ℤ) (k n : ℕ) :
    coeff n (X ^ k * PowerSeries.mk u) = if k ≤ n then u (n - k) else 0 := by
  rw [coeff_X_pow_mul', coeff_mk]

lemma gf : ((X - 1) ^ 5 * (X + 1) : PowerSeries ℤ) * PowerSeries.mk (fun n => (a n : ℤ)) =
    -X ^ 2 * (X ^ 4 - 4 * X ^ 3 + 6 * X ^ 2 + 8 * X + 1) := by
  have hD : ((X - 1) ^ 5 * (X + 1) : PowerSeries ℤ) =
      X ^ 6 - 4 * X ^ 5 + 5 * X ^ 4 - 5 * X ^ 2 + 4 * X ^ 1 - 1 := by ring
  have hN : (-X ^ 2 * (X ^ 4 - 4 * X ^ 3 + 6 * X ^ 2 + 8 * X + 1) : PowerSeries ℤ) =
      4 * X ^ 5 - X ^ 6 - 6 * X ^ 4 - 8 * X ^ 3 - X ^ 2 := by ring
  rw [hD, hN]
  have h4 : (4 : PowerSeries ℤ) = C 4 := (map_ofNat C 4).symm
  have h5 : (5 : PowerSeries ℤ) = C 5 := (map_ofNat C 5).symm
  have h6 : (6 : PowerSeries ℤ) = C 6 := (map_ofNat C 6).symm
  have h8 : (8 : PowerSeries ℤ) = C 8 := (map_ofNat C 8).symm
  rw [h4, h5, h6, h8]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add, coeff_C_mul, cXm, coeff_mk,
    coeff_X_pow]
  have c1 := closed 1 le_rfl
  have c2 := closed 2 (by norm_num)
  have c3 := closed 3 (by norm_num)
  have c4 := closed 4 (by norm_num)
  have c5 := closed 5 (by norm_num)
  have c6 := closed 6 (by norm_num)
  norm_num at c1 c2 c3 c4 c5 c6
  have z := a_zero
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp [z] <;> omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    have d1 := closed (m + 1) (by omega)
    have d2 := closed (m + 2) (by omega)
    have d3 := closed (m + 3) (by omega)
    have d5 := closed (m + 5) (by omega)
    have d6 := closed (m + 6) (by omega)
    have d7 := closed (m + 7) (by omega)
    simp only [show 6 ≤ m + 7 by omega, show 5 ≤ m + 7 by omega, show 4 ≤ m + 7 by omega,
      show 2 ≤ m + 7 by omega, show 1 ≤ m + 7 by omega, if_true,
      show m + 7 ≠ 5 by omega, show m + 7 ≠ 6 by omega, show m + 7 ≠ 4 by omega,
      show m + 7 ≠ 3 by omega, show m + 7 ≠ 2 by omega, if_false,
      show m + 7 - 6 = m + 1 by omega, show m + 7 - 5 = m + 2 by omega,
      show m + 7 - 4 = m + 3 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 1 = m + 6 by omega]
    push_cast at d1 d2 d3 d5 d6 d7
    have : 8 * ((a (m + 1) : ℤ) - 4 * a (m + 2) + 5 * a (m + 3) - 5 * a (m + 5) + 4 * a (m + 6)
        - a (m + 7)) = 0 := by
      linear_combination d1 - 4 * d2 + 5 * d3 - 5 * d5 + 4 * d6 - d7
    omega

theorem sol : type_of% @OMA.S_oeis_a218832.main := by
  refine ⟨fun n hn => ?_, gf⟩
  have h := closed n hn
  rw [eq_div_iff (by norm_num : (8 : ℚ) ≠ 0)]
  have h' : ((8 * (a n : ℤ) : ℤ) : ℚ) =
      ((7 + (-1) ^ n - 8 * (n : ℤ) ^ 2 + 2 * (n : ℤ) ^ 4 : ℤ) : ℚ) := by rw [h]
  push_cast at h'
  linarith

end OMA.P218832

theorem OMA.solution : type_of% @OMA.S_oeis_a218832.main := OMA.P218832.sol


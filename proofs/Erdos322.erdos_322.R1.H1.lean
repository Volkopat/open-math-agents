import OMAReductions.R_Erdos322_erdos_322_R1
import Mathlib

-- Step H1 of reduction Erdos322.erdos_322.R1 (Erdos Problem 322, the case k = 3).
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Claim: for some c > 0 there are infinitely many n with more than n^c ordered representations
-- as a sum of three positive cubes (Mahler 1936).
-- Proof sketch: Mahler s identity (9x^4)^3 + (3xy^3 - 9x^4)^3 + (y^4 - 9x^3y)^3 = y^12.
-- For 1 <= x <= y/3 the three bases are positive and the first base determines x, so y^12 has
-- at least y/3 representations. With y = N^2, N = 3M, M >= 2: n = N^24 has more than
-- N = n^(1/24) representations.

namespace OMA.P_Erdos322_R1_H1

open Erdos322

/-- Mahler's identity in the form used here: if `y ^ 3 = 9 * x ^ 3 + d` then
`(9 x^4)^3 + (3 x (6 x^3 + d))^3 + (y d)^3 = y^12`. -/
lemma mahler (x y d : ℕ) (hd : y ^ 3 = 9 * x ^ 3 + d) :
    (9 * x ^ 4) ^ 3 + (3 * x * (6 * x ^ 3 + d)) ^ 3 + (y * d) ^ 3 = y ^ 12 := by
  have h2 : (y * d) ^ 3 = (9 * x ^ 3 + d) * d ^ 3 := by rw [mul_pow, hd]
  have h12 : y ^ 12 = (9 * x ^ 3 + d) ^ 4 := by rw [← hd]; ring
  rw [h2, h12]
  ring

/-- The three bases attached to `x` (for the target `y ^ 12`). -/
def base (x y : ℕ) : Fin 3 → ℕ :=
  ![9 * x ^ 4, 3 * x * (y ^ 3 - 3 * x ^ 3), y * (y ^ 3 - 9 * x ^ 3)]

lemma base_spec (x y : ℕ) (hx : 1 ≤ x) (hxy : 3 * x ≤ y) :
    (∀ i, 0 < base x y i) ∧ ∑ i, (base x y i) ^ 3 = y ^ 12 := by
  have h27 : 27 * x ^ 3 ≤ y ^ 3 := by
    have := Nat.pow_le_pow_left hxy 3
    calc 27 * x ^ 3 = (3 * x) ^ 3 := by ring
      _ ≤ y ^ 3 := this
  have hx3 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
  obtain ⟨d, hd⟩ : ∃ d, y ^ 3 = 9 * x ^ 3 + d := ⟨y ^ 3 - 9 * x ^ 3, by omega⟩
  have e1 : y ^ 3 - 3 * x ^ 3 = 6 * x ^ 3 + d := by omega
  have e2 : y ^ 3 - 9 * x ^ 3 = d := by omega
  have hdpos : 0 < d := by omega
  have hy : 0 < y := by omega
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · have : 0 < 9 * x ^ 4 := Nat.mul_pos (by norm_num) (Nat.pow_pos hx)
      simpa [base] using this
    · simp only [base, e1]
      have : 0 < 3 * x * (6 * x ^ 3 + d) :=
        Nat.mul_pos (Nat.mul_pos (by norm_num) hx) (by omega)
      simpa using this
    · simp only [base, e2]
      have : 0 < y * d := Nat.mul_pos hy hdpos
      simpa using this
  · rw [Fin.sum_univ_three]
    simp only [base, e1, e2]
    simpa using mahler x y d hd

/-- At least `y / 3` ordered representations of `y ^ 12` as a sum of three positive cubes. -/
lemma count_ge (y : ℕ) : y / 3 ≤ representationCount 3 (y ^ 12) := by
  unfold representationCount
  have hlt : ∀ x i, 1 ≤ x → 3 * x ≤ y → base x y i < y ^ 12 + 1 := by
    intro x i hx hxy
    obtain ⟨hpos, hsum⟩ := base_spec x y hx hxy
    have h1 : base x y i ≤ (base x y i) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h2 : (base x y i) ^ 3 ≤ ∑ j, (base x y j) ^ 3 :=
      Finset.single_le_sum (f := fun j => (base x y j) ^ 3) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    omega
  let g : ℕ → (Fin 3 → Fin (y ^ 12 + 1)) :=
    fun x i => ⟨base x y i % (y ^ 12 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  have hval : ∀ x i, 1 ≤ x → 3 * x ≤ y → ((g x i : Fin (y ^ 12 + 1)) : ℕ) = base x y i :=
    fun x i hx hxy => Nat.mod_eq_of_lt (hlt x i hx hxy)
  have hcard : (Finset.Icc 1 (y / 3)).card ≤ ((Finset.univ : Finset (Fin 3 → Fin (y ^ 12 + 1))).filter
      (fun a ↦ (∀ i, 0 < (a i : ℕ)) ∧ ∑ i, (a i : ℕ) ^ 3 = y ^ 12)).card := by
    apply Finset.card_le_card_of_injOn g
    · intro x hx
      have hx' := Finset.mem_Icc.mp hx
      have hxy : 3 * x ≤ y := by
        have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mp hx'.2
        omega
      obtain ⟨hpos, hsum⟩ := base_spec x y hx'.1 hxy
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      refine ⟨fun i => by rw [hval x i hx'.1 hxy]; exact hpos i, ?_⟩
      calc ∑ i, ((g x i : Fin (y ^ 12 + 1)) : ℕ) ^ 3 = ∑ i, (base x y i) ^ 3 :=
            Finset.sum_congr rfl (fun i _ => by rw [hval x i hx'.1 hxy])
        _ = y ^ 12 := hsum
    · intro x hx x' hx' hgg
      have hx1 := Finset.mem_Icc.mp hx
      have hx2 := Finset.mem_Icc.mp hx'
      have hxy : 3 * x ≤ y := by
        have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mp hx1.2
        omega
      have hxy' : 3 * x' ≤ y := by
        have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mp hx2.2
        omega
      have h0 : ((g x 0 : Fin (y ^ 12 + 1)) : ℕ) = ((g x' 0 : Fin (y ^ 12 + 1)) : ℕ) := by rw [hgg]
      rw [hval x 0 hx1.1 hxy, hval x' 0 hx2.1 hxy'] at h0
      simp only [base, Matrix.cons_val_zero] at h0
      have h4 : x ^ 4 = x' ^ 4 := by omega
      exact Nat.pow_left_injective (by norm_num : (4 : ℕ) ≠ 0) h4
  simpa using hcard

lemma div_lt (M : ℕ) (hM : 2 ≤ M) : 3 * M < (3 * M) ^ 2 / 3 := by
  have h : (3 * M) ^ 2 = 3 * (3 * M ^ 2) := by ring
  rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
  nlinarith

/-- For `N = 3 M` with `M ≥ 2`, the number `N ^ 24` has more than `N` representations. -/
lemma main_count (N : ℕ) (hN : N < N ^ 2 / 3) : N < representationCount 3 (N ^ 24) := by
  have hc := count_ge (N ^ 2)
  have e : (N ^ 2) ^ 12 = N ^ 24 := by rw [← pow_mul]
  rw [e] at hc
  exact lt_of_lt_of_le hN hc

lemma root (N : ℕ) : ((N ^ 24 : ℕ) : ℝ) ^ (((24 : ℕ) : ℝ)⁻¹) = (N : ℝ) := by
  rw [Nat.cast_pow]
  exact Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) (by norm_num)

end OMA.P_Erdos322_R1_H1

theorem OMA.solution : OMA.R_Erdos322_erdos_322_R1.H1 := by
  refine ⟨((24 : ℕ) : ℝ)⁻¹, by positivity, ?_⟩
  apply Set.infinite_of_injective_forall_mem (f := fun m : ℕ => (3 * (m + 2)) ^ 24)
  · intro a b hab
    have := Nat.pow_left_injective (by norm_num : (24 : ℕ) ≠ 0) hab
    omega
  · intro m
    change (((3 * (m + 2)) ^ 24 : ℕ) : ℝ) ^ (((24 : ℕ) : ℝ)⁻¹)
      < ((Erdos322.representationCount 3 ((3 * (m + 2)) ^ 24) : ℕ) : ℝ)
    rw [OMA.P_Erdos322_R1_H1.root]
    exact Nat.cast_lt.mpr (OMA.P_Erdos322_R1_H1.main_count _
      (OMA.P_Erdos322_R1_H1.div_lt (m + 2) (by omega)))

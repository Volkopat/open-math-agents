import OMAStatements.S_oeis_a322844
import Mathlib.Tactic

/-!
OEIS A322844, https://oeis.org/A322844/internal, asks for the principal
minor sums of the matrix from OEIS A317614. The formal statement uses
zero-based indices. Proof credit: @grp06.
-/

namespace OMA.S_oeis_a322844

private def alpha (n i : ℕ) : ℚ :=
  if i % 2 = 0 then 1 + (n : ℚ) * i else (n : ℚ) * ((i : ℚ) + 1)

private def epsilon (i : ℕ) : ℚ :=
  if i % 2 = 0 then 1 else -1

private theorem entry_affine (n i j : ℕ) :
    entry n i j = alpha n i + epsilon i * (j : ℚ) := by
  by_cases h : i % 2 = 0 <;>
    simp only [entry, alpha, epsilon, h, if_true, if_false] <;> ring

private theorem higher_trace_zero (n k : ℕ) (hk : 2 < k) :
    principalTrace n k = 0 := by
  classical
  unfold principalTrace
  apply Finset.sum_eq_zero
  intro s hs
  let M : Matrix s s ℚ := fun i j => entry n i.val.val j.val.val
  let L : Matrix s (Fin 2) ℚ := fun i a =>
    if a = 0 then alpha n i.val.val else epsilon i.val.val
  let R : Matrix (Fin 2) s ℚ := fun a j =>
    if a = 0 then 1 else (j.val.val : ℚ)
  have hfactor : M = L * R := by
    apply Matrix.ext
    intro i j
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simpa only [M, L, R, if_pos rfl, if_neg h10, mul_one] using
      entry_affine n i.val.val j.val.val
  have hwidth : L.rank ≤ 2 := by
    simpa only [Fintype.card_fin] using Matrix.rank_le_card_width L
  have hrank : M.rank ≤ 2 := by
    rw [hfactor]
    exact (Matrix.rank_mul_le_left L R).trans hwidth
  have hcard : Fintype.card s = k := by
    rw [Fintype.card_coe]
    exact (Finset.mem_powersetCard.mp hs).2
  change M.det = 0
  by_contra hdet
  rw [Matrix.rank_of_det_ne_zero hdet, hcard] at hrank
  exact (Nat.not_lt_of_ge hrank) hk

private def momentA (n r : ℕ) : ℚ :=
  ∑ i ∈ Finset.range r, alpha n i

private def momentB (n r : ℕ) : ℚ :=
  ∑ i ∈ Finset.range r, (i : ℚ) * alpha n i

private def momentE (r : ℕ) : ℚ :=
  ∑ i ∈ Finset.range r, epsilon i

private def momentJ (r : ℕ) : ℚ :=
  ∑ i ∈ Finset.range r, (i : ℚ) * epsilon i

private theorem row_increment (n r : ℕ) :
    (∑ i ∈ Finset.range r,
      (entry n i i * entry n r r - entry n i r * entry n r i)) =
      momentA n r * ((r : ℚ) * epsilon r) - momentB n r * epsilon r -
        momentE r * ((r : ℚ) * alpha n r) + momentJ r * alpha n r := by
  calc
    _ = ∑ i ∈ Finset.range r,
        (alpha n i * ((r : ℚ) * epsilon r) -
          ((i : ℚ) * alpha n i) * epsilon r -
          epsilon i * ((r : ℚ) * alpha n r) +
          ((i : ℚ) * epsilon i) * alpha n r) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [entry_affine]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        momentA, momentB, momentE, momentJ]

private theorem prefix_identity (n r : ℕ) :
    (∑ j ∈ Finset.range r, ∑ i ∈ Finset.range j,
      (entry n i i * entry n j j - entry n i j * entry n j i)) =
      momentA n r * momentJ r - momentB n r * momentE r := by
  induction r with
  | zero => simp [momentA, momentB, momentE, momentJ]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, row_increment]
    simp only [momentA, momentB, momentE, momentJ, Finset.sum_range_succ]
    ring

private theorem even_moments (n m : ℕ) :
    momentA n (2 * m) = 2 * (n : ℚ) * (m : ℚ)^2 + m ∧
    momentB n (2 * m) =
      8 * (n : ℚ) * ((m : ℚ) - 1) * m * (2 * (m : ℚ) - 1) / 6 +
      (6 * (n : ℚ) + 2) * m * ((m : ℚ) - 1) / 2 + 2 * (n : ℚ) * m ∧
    momentE (2 * m) = 0 ∧ momentJ (2 * m) = -(m : ℚ) := by
  induction m with
  | zero => norm_num [momentA, momentB, momentE, momentJ]
  | succ m ih =>
    obtain ⟨ha, hb, he, hj⟩ := ih
    have hsplit (f : ℕ → ℚ) :
        (∑ i ∈ Finset.range (2 * (m + 1)), f i) =
          (∑ i ∈ Finset.range (2 * m), f i) + f (2 * m) + f (2 * m + 1) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ]
    have hEven : (2 * m) % 2 = 0 := by omega
    have hOdd : (2 * m + 1) % 2 ≠ 0 := by omega
    simp only [momentA] at ha
    simp only [momentB] at hb
    simp only [momentE] at he
    simp only [momentJ] at hj
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [momentA, hsplit (alpha n), ha]
      simp only [alpha, hEven, hOdd, if_true, if_false] <;> push_cast <;> ring
    · rw [momentB, hsplit (fun i => (i : ℚ) * alpha n i), hb]
      simp only [alpha, hEven, hOdd, if_true, if_false] <;> push_cast <;> ring
    · rw [momentE, hsplit epsilon, he]
      simp only [epsilon, hEven, hOdd, if_true, if_false] <;> ring
    · rw [momentJ, hsplit (fun i => (i : ℚ) * epsilon i), hj]
      simp only [epsilon, hEven, hOdd, if_true, if_false] <;> push_cast <;> ring

private theorem odd_moments (n m : ℕ) :
    momentA n (2 * m + 1) =
      2 * (n : ℚ) * (m : ℚ)^2 + m + (2 * (n : ℚ) * m + 1) ∧
    momentB n (2 * m + 1) =
      8 * (n : ℚ) * ((m : ℚ) - 1) * m * (2 * (m : ℚ) - 1) / 6 +
      (6 * (n : ℚ) + 2) * m * ((m : ℚ) - 1) / 2 + 2 * (n : ℚ) * m +
      (2 * (m : ℚ)) * (2 * (n : ℚ) * m + 1) ∧
    momentE (2 * m + 1) = 1 ∧ momentJ (2 * m + 1) = (m : ℚ) := by
  obtain ⟨ha, hb, he, hj⟩ := even_moments n m
  have hEven : (2 * m) % 2 = 0 := by omega
  simp only [momentA] at ha
  simp only [momentB] at hb
  simp only [momentE] at he
  simp only [momentJ] at hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [momentA, Finset.sum_range_succ, ha]
    simp only [alpha, hEven, if_true] <;> push_cast <;> ring
  · rw [momentB, Finset.sum_range_succ, hb]
    simp only [alpha, hEven, if_true] <;> push_cast <;> ring
  · rw [momentE, Finset.sum_range_succ, he]
    simp [epsilon, hEven]
  · rw [momentJ, Finset.sum_range_succ, hj]
    simp only [epsilon, hEven, if_true] <;> push_cast <;> ring

private theorem two_trace_abs (n : ℕ) (hn : 1 < n) :
    |principalTwo n| = formula n := by
  have hprefix : principalTwo n = momentA n n * momentJ n -
      momentB n n * momentE n := prefix_identity n n
  by_cases hp : n % 2 = 0
  · have hshape : n = 2 * (n / 2) := by omega
    obtain ⟨ha, hb, he, hj⟩ := even_moments n (n / 2)
    rw [← hshape] at ha hb he hj
    have hvalue : principalTwo n = -((n : ℚ)^2 * (1 + (n : ℚ)^2) / 4) := by
      rw [hprefix, ha, hb, he, hj]
      have hc : (n : ℚ) = 2 * ((n / 2 : ℕ) : ℚ) := by exact_mod_cast hshape
      generalize (n / 2 : ℕ) = m at hc ⊢
      rw [hc]
      ring
    have hnonneg : 0 ≤ (n : ℚ)^2 * (1 + (n : ℚ)^2) / 4 := by positivity
    rw [hvalue, abs_of_nonpos (neg_nonpos.mpr hnonneg), neg_neg, formula, hp]
    push_cast <;> ring
  · have hmod : n % 2 = 1 := by omega
    have hshape : n = 2 * (n / 2) + 1 := by omega
    obtain ⟨ha, hb, he, hj⟩ := odd_moments n (n / 2)
    rw [← hshape] at ha hb he hj
    have hvalue : principalTwo n = -((n : ℚ)^2 * ((n : ℚ)^2 - 1) / 12) := by
      rw [hprefix, ha, hb, he, hj]
      have hc : (n : ℚ) = 2 * ((n / 2 : ℕ) : ℚ) + 1 := by exact_mod_cast hshape
      generalize (n / 2 : ℕ) = m at hc ⊢
      rw [hc]
      ring
    have hOne : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hSquare : 0 ≤ (n : ℚ)^2 - 1 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hOne) (show 0 ≤ (n : ℚ) + 1 by positivity)
      nlinarith only [hprod]
    have hnonneg : 0 ≤ (n : ℚ)^2 * ((n : ℚ)^2 - 1) / 12 :=
      div_nonneg (mul_nonneg (sq_nonneg _) hSquare) (by norm_num)
    rw [hvalue, abs_of_nonpos (neg_nonpos.mpr hnonneg), neg_neg, formula, hmod]
    push_cast <;> ring

end OMA.S_oeis_a322844

theorem OMA.solution : type_of% @OMA.S_oeis_a322844.main := by
  exact ⟨OMA.S_oeis_a322844.two_trace_abs, OMA.S_oeis_a322844.higher_trace_zero⟩

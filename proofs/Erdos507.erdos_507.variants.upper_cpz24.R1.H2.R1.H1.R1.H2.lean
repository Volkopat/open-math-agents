import OMAReductions.R_Erdos507_erdos_507_variants_upper_cpz24_R1_H2_R1_H1_R1

/-!
Proof of `OMA.R_Erdos507_erdos_507_variants_upper_cpz24_R1_H2_R1_H1_R1.H2`.
Round every coordinate down on the grid of mesh `1 / q`: take `A i = floor (a i * q)` and
likewise for `b` and `s`. Since `floor x <= x < floor x + 1`, each rounded value is within
`1 / q` of the original one, and the bounds `0 <= a i <= 1`, `0 <= b i <= 1`, `|s i| <= 1`
give `0 <= A i <= q`, `0 <= B i <= q` and `-q <= S i <= q`.
-/

namespace OMAProof.Erdos507RoundGrid

theorem approx (x q : ℝ) (hq : 0 < q) : |x - (⌊x * q⌋ : ℝ) / q| < 1 / q := by
  have h1 := Int.floor_le (x * q)
  have h2 := Int.lt_floor_add_one (x * q)
  have e : x - (⌊x * q⌋ : ℝ) / q = (x * q - ⌊x * q⌋) / q := by field_simp
  rw [e, abs_div, abs_of_pos hq, abs_of_nonneg (by linarith)]
  exact (div_lt_div_iff_of_pos_right hq).mpr (by linarith)

theorem floor_le_q (x q : ℝ) (n : ℤ) (hq : 0 ≤ q) (hx : x ≤ 1) (hn : (n : ℝ) = q) :
    ⌊x * q⌋ ≤ n := by
  have h1 := Int.floor_le (x * q)
  have : (⌊x * q⌋ : ℝ) ≤ n := by rw [hn]; nlinarith
  exact_mod_cast this

theorem neg_q_le_floor (x q : ℝ) (n : ℤ) (hq : 0 ≤ q) (hx : -1 ≤ x) (hn : (n : ℝ) = q) :
    -n ≤ ⌊x * q⌋ := by
  apply Int.le_floor.mpr
  push_cast
  rw [hn]
  nlinarith

end OMAProof.Erdos507RoundGrid

open OMAProof.Erdos507RoundGrid in
theorem OMA.solution : OMA.R_Erdos507_erdos_507_variants_upper_cpz24_R1_H2_R1_H1_R1.H2 := by
  intro I q hq a b s h
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hcast : (((q : ℤ)) : ℝ) = (q : ℝ) := by push_cast; rfl
  refine ⟨fun i => ⌊a i * q⌋, fun i => ⌊b i * q⌋, fun i => ⌊s i * q⌋, fun i => ?_,
    fun i => ⟨approx _ _ hq', approx _ _ hq', approx _ _ hq'⟩⟩
  obtain ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩, hs⟩ := h i
  obtain ⟨hs0, hs1⟩ := abs_le.mp hs
  exact ⟨Int.floor_nonneg.mpr (by positivity), floor_le_q _ _ _ hq'.le ha1 hcast,
    Int.floor_nonneg.mpr (by positivity), floor_le_q _ _ _ hq'.le hb1 hcast,
    neg_q_le_floor _ _ _ hq'.le hs0 hcast, floor_le_q _ _ _ hq'.le hs1 hcast⟩

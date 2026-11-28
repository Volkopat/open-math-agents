import OMAReductions.R_oeis_a016742_R1
import Mathlib

/-! Step oeis-a016742.R1.H1, the classical direction: the order of a regular Hadamard matrix is
an even square. Summing all entries of `H Hᵀ = n I` gives `n s² = n²` for the common line sum
`s`, so `n = s²`. Rows `0` and `1` are orthogonal ±1 vectors, so `n` is even (reduce mod 2), and
hence `s` is even. -/

namespace OMA.A016742H1

open Matrix OMA.S_oeis_a016742

theorem main (n : ℕ) (hn : 2 ≤ n) (hH : ∃ H : Matrix (Fin n) (Fin n) ℤ, IsRegularHadamard H) :
    ∃ m : ℕ, n = (2 * m) ^ 2 := by
  obtain ⟨H, hpm, hHH, s, hrow, hcol⟩ := hH
  have hentry : ∀ i k, ∑ j, H i j * H k j = if i = k then (n : ℤ) else 0 := by
    intro i k
    have := congrFun (congrFun hHH i) k
    simp only [mul_apply, transpose_apply, Matrix.smul_apply, one_apply, smul_eq_mul] at this
    rw [this]; split_ifs <;> simp
  -- total sum: `n s² = n²`
  have htot : (n : ℤ) * s ^ 2 = (n : ℤ) * n := by
    have e1 : ∑ i, ∑ k, ∑ j, H i j * H k j = ∑ j, (∑ i, H i j) * (∑ k, H k j) := by
      calc ∑ i, ∑ k, ∑ j, H i j * H k j = ∑ i, ∑ j, ∑ k, H i j * H k j := by
            refine Finset.sum_congr rfl (fun i _ => ?_); rw [Finset.sum_comm]
        _ = ∑ j, ∑ i, ∑ k, H i j * H k j := Finset.sum_comm
        _ = ∑ j, (∑ i, H i j) * (∑ k, H k j) := by
            refine Finset.sum_congr rfl (fun j _ => ?_); rw [Finset.sum_mul_sum]
    have e2 : ∑ i, ∑ k, ∑ j, H i j * H k j = (n : ℤ) * n := by
      simp only [hentry, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [e1] at e2
    simp only [hcol, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e2
    linarith
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hs2 : s ^ 2 = n := by
    have := mul_left_cancel₀ hn0 htot
    exact this
  -- `n` is even: rows `0` and `1` are orthogonal
  have heven : Even n := by
    have h01 := hentry ⟨0, by omega⟩ ⟨1, by omega⟩
    rw [if_neg (by simp [Fin.ext_iff])] at h01
    have hz : ((∑ j, H ⟨0, by omega⟩ j * H ⟨1, by omega⟩ j : ℤ) : ZMod 2) = (n : ZMod 2) := by
      push_cast
      have : ∀ j, ((H ⟨0, by omega⟩ j : ℤ) : ZMod 2) * ((H ⟨1, by omega⟩ j : ℤ) : ZMod 2) = 1 := by
        intro j
        rcases hpm ⟨0, by omega⟩ j with h | h <;> rcases hpm ⟨1, by omega⟩ j with h' | h' <;>
          simp [h, h']
      simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [h01, Int.cast_zero] at hz
    exact (ZMod.natCast_eq_zero_iff_even).1 hz.symm
  -- hence `s` is even
  have hseven : Even s := by
    have : Even (s ^ 2) := by rw [hs2]; exact_mod_cast heven
    exact (Int.even_pow.1 this).1
  obtain ⟨t, ht⟩ := hseven
  refine ⟨t.natAbs, ?_⟩
  have : ((n : ℕ) : ℤ) = ((2 * t.natAbs) ^ 2 : ℕ) := by
    push_cast
    rw [← hs2, ht, mul_pow, sq_abs]
    ring
  exact_mod_cast this

end OMA.A016742H1

theorem OMA.solution : OMA.R_oeis_a016742_R1.H1 :=
  OMA.A016742H1.main

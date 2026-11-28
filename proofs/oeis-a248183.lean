import OMAStatements.S_oeis_a248183
import Mathlib.Tactic

open OMA.S_oeis_a248183

namespace QuadraticTailProof

lemma telescopes (k : ℕ) : tail k = 1/(2*((k : ℚ)+1)*(k+2)) := by
  induction k with
  | zero => norm_num [tail]
  | succ k ih =>
    have hs : tail (k+1) = tail k - 1/(((k : ℚ)+1)*(k+2)*(k+3)) := by
      simp only [tail, Finset.sum_range_succ]
      ring
    rw [hs, ih]
    push_cast
    field_simp
    ring

lemma gap (n k : ℕ) : n^2+1 ≠ 2*(k+1)*(k+2) := by
  have parity (v : ℕ) : ∃ u, v = 2*u ∨ v = 2*u+1 := ⟨v/2, by omega⟩
  intro he
  obtain ⟨u, rfl | rfl⟩ := parity n <;> obtain ⟨v, rfl | rfl⟩ := parity k <;>
    ring_nf at he <;> omega

lemma cutoff (n k : ℕ) : proposal n ≤ k ↔ n^2 < 2*(k+1)*(k+2) := by
  have bound : 2 ≤ Nat.sqrt (2*n^2+4) := Nat.le_sqrt.mpr (by omega)
  have h : proposal n ≤ k ↔ Nat.sqrt (2*n^2+4) < 2*k+3 := by unfold proposal; omega
  rw [h, Nat.sqrt_lt]
  have he := gap n k
  constructor
  · intro h
    nlinarith
  · intro h
    have h' : n^2+1 < 2*(k+1)*(k+2) := by omega
    nlinarith

lemma good (n k : ℕ) (hn : 1<n) : tail k < 1/(n : ℚ)^2 ↔ n^2 < 2*(k+1)*(k+2) := by
  rw [telescopes, div_lt_div_iff₀ (by positivity) (by positivity)]
  simp only [one_mul]
  norm_cast

end QuadraticTailProof

open QuadraticTailProof

theorem OMA.solution : type_of% @OMA.S_oeis_a248183.main := by
  intro n hn
  have hpos : 0 < proposal n := by
    by_contra! hz
    have h := (cutoff n 0).mp hz
    nlinarith
  exact ⟨⟨hpos, (good n _ hn).mpr ((cutoff n _).mp le_rfl)⟩,
    fun k hk => (cutoff n k).mpr ((good n k hn).mp hk.2)⟩

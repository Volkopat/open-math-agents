import OMAStatements.S_oeis_a075245
import Mathlib

/-!
# A counterexample at n = 409

The triple (105, 3906, 7987770) gives a lower bound on the maximal last
denominator. For each proposed first denominator, factoring the equation
then restricts the middle denominator to a short interval.
-/

namespace A075245Proof
open OMA.S_oeis_a075245

private theorem factor_bound {u v R V U : ℤ} (eq : u*v = R) (hR : 0 < R)
    (hV : 0 < V) (hv : V ≤ v) (hU : 0 ≤ U) (cap : R < U*V) :
    0 < u ∧ u < U := by
  constructor
  · exact pos_of_mul_pos_left (eq.symm ▸ hR) (by omega)
  · by_contra! hu
    have h := mul_le_mul hu hv (le_of_lt hV) (hU.trans hu)
    omega

private theorem witness : Expansion 409 105 3906 7987770 := by
  norm_num [Expansion]

private theorem exclude103 {y z : ℤ} (s : Expansion 409 103 y z)
    (hz : 7987770 ≤ z) : False := by
  obtain ⟨_, _, _, eq⟩ := s
  have prod : (3*y-42127)*(3*z-42127) = 42127^2 := by
    linear_combination 3 * eq
  have hu := factor_bound (U := 75) (V := 3*7987770-42127) prod
    (by norm_num) (by norm_num) (by omega) (by norm_num) (by norm_num)
  have lo : 14043 ≤ y := by omega
  have hi : y ≤ 14067 := by omega
  interval_cases y <;> omega

private theorem exclude104 {y z : ℤ} (s : Expansion 409 104 y z)
    (hz : 7987770 ≤ z) : False := by
  obtain ⟨_, _, _, eq⟩ := s
  have prod : (7*y-42536)*(7*z-42536) = 42536^2 := by
    linear_combination 7 * eq
  have hu := factor_bound (U := 33) (V := 7*7987770-42536) prod
    (by norm_num) (by norm_num) (by omega) (by norm_num) (by norm_num)
  have lo : 6077 ≤ y := by omega
  have hi : y ≤ 6081 := by omega
  interval_cases y <;> omega

end A075245Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a075245.main) := by
  intro claimed
  obtain ⟨x,y,z,⟨expansion,maximal⟩,predicted⟩ := claimed 409 (by decide)
  have hz := maximal 105 3906 7987770 A075245Proof.witness
  rcases predicted with rfl | ⟨_,rfl⟩
  · exact A075245Proof.exclude103 expansion hz
  · exact A075245Proof.exclude104 expansion hz

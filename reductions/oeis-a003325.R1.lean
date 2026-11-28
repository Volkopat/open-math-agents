import OMAStatements.S_oeis_a003325
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
A003325 is equivalent to the existence of infinitely many ordered integer
solutions to `x³ + y³ + z³ = 3`, the `k = 3` case of Heath-Brown's conjecture.

See Booker and Sutherland, *On a question of Mordell*,
https://arxiv.org/abs/2007.01209.
-/

namespace OMA.R_oeis_a003325_R1

open OMA.S_oeis_a003325

private theorem cube_mod_nine (x : ℤ) :
    x ^ 3 % 9 = 0 ∨ x ^ 3 % 9 = 1 ∨ x ^ 3 % 9 = 8 := by
  have hlo := Int.emod_nonneg x (by norm_num : (9 : ℤ) ≠ 0)
  have hhi := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 9)
  have hpow : (x % 9) ^ 3 % 9 = x ^ 3 % 9 := (Int.mod_modEq x 9).pow 3
  rw [← hpow]
  interval_cases (x % 9) <;> decide

/-- Each cube in a solution is congruent to one modulo nine. -/
theorem cube_residues {x y z : ℤ} (h : x ^ 3 + y ^ 3 + z ^ 3 = 3) :
    x ^ 3 % 9 = 1 ∧ y ^ 3 % 9 = 1 ∧ z ^ 3 % 9 = 1 := by
  have hm : (x ^ 3 + y ^ 3 + z ^ 3) % 9 = 3 := by
    rw [h]
    decide
  rw [Int.add_emod, Int.add_emod (x ^ 3) (y ^ 3) 9] at hm
  rcases cube_mod_nine x with hx | hx | hx <;>
    rcases cube_mod_nine y with hy | hy | hy <;>
    rcases cube_mod_nine z with hz | hz | hz <;>
    norm_num [hx, hy, hz] at hm
  norm_num [hx, hy, hz]

private theorem cast_natAbs_of_neg {x : ℤ} (hx : x < 0) : (x.natAbs : ℤ) = -x := by
  simpa only [Int.natAbs_neg] using Int.natAbs_of_nonneg (neg_pos.mpr hx).le

private theorem coordinate_bounds {a b c : ℕ}
    (h : a ^ 3 + b ^ 3 = c ^ 3 + 3 ∨ a ^ 3 + b ^ 3 + 3 = c ^ 3) :
    a ≤ a ^ 3 + b ^ 3 + 3 ∧ b ≤ a ^ 3 + b ^ 3 + 3 ∧ c ≤ a ^ 3 + b ^ 3 + 3 := by
  have ha := Nat.le_self_pow (by decide : 3 ≠ 0) a
  have hb := Nat.le_self_pow (by decide : 3 ≠ 0) b
  have hc := Nat.le_self_pow (by decide : 3 ≠ 0) c
  rcases h with h | h <;> omega

private theorem mixed_sign_solution {x y z : ℤ}
    (h : x ^ 3 + y ^ 3 + z ^ 3 = 3)
    (hs : (0 < x ∧ 0 < y ∧ z < 0) ∨ (x < 0 ∧ y < 0 ∧ 0 < z)) :
    ∃ n, IsCommonTerm n ∧ x.natAbs ≤ n + 3 ∧ y.natAbs ≤ n + 3 ∧ z.natAbs ≤ n + 3 := by
  have he : x.natAbs ^ 3 + y.natAbs ^ 3 = z.natAbs ^ 3 + 3 ∨
      x.natAbs ^ 3 + y.natAbs ^ 3 + 3 = z.natAbs ^ 3 := by
    rcases hs with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩
    · left
      have he : (x.natAbs : ℤ) ^ 3 + (y.natAbs : ℤ) ^ 3 = (z.natAbs : ℤ) ^ 3 + 3 := by
        rw [Int.natAbs_of_nonneg hx.le, Int.natAbs_of_nonneg hy.le, cast_natAbs_of_neg hz]
        nlinarith only [h]
      exact_mod_cast he
    · right
      have he : (x.natAbs : ℤ) ^ 3 + (y.natAbs : ℤ) ^ 3 + 3 = (z.natAbs : ℤ) ^ 3 := by
        rw [cast_natAbs_of_neg hx, cast_natAbs_of_neg hy, Int.natAbs_of_nonneg hz.le]
        nlinarith only [h]
      exact_mod_cast he
  have hx : x ≠ 0 := by rcases hs with ⟨hx, _, _⟩ | ⟨hx, _, _⟩ <;> omega
  have hy : y ≠ 0 := by rcases hs with ⟨_, hy, _⟩ | ⟨_, hy, _⟩ <;> omega
  exact ⟨_, ⟨⟨x.natAbs, y.natAbs, Int.natAbs_pos.mpr hx, Int.natAbs_pos.mpr hy, rfl⟩,
    z.natAbs, he⟩, coordinate_bounds he⟩

private theorem le_cube_of_pos {x : ℤ} (hx : 0 < x) : x ≤ x ^ 3 := by
  have h : (x.natAbs : ℤ) ≤ (x.natAbs : ℤ) ^ 3 := by
    exact_mod_cast Nat.le_self_pow (by decide : 3 ≠ 0) x.natAbs
  simpa only [Int.natAbs_of_nonneg hx.le] using h

private theorem cube_nonpos_of_neg {x : ℤ} (hx : x < 0) : x ^ 3 ≤ 0 := by
  simpa [pow_succ] using mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg x) hx.le

/-- Infinitely many ordered integer solutions of the equation studied by Mordell. -/
def H1 : Prop :=
  {p : ℤ × ℤ × ℤ | p.1 ^ 3 + p.2.1 ^ 3 + p.2.2 ^ 3 = 3}.Infinite

/-- A solution other than (1, 1, 1) gives a common term that bounds all its coordinates. -/
def H2 : Prop :=
  ∀ x y z : ℤ, x ^ 3 + y ^ 3 + z ^ 3 = 3 →
    (x = 1 ∧ y = 1 ∧ z = 1) ∨
      ∃ n, IsCommonTerm n ∧ x.natAbs ≤ n + 3 ∧ y.natAbs ≤ n + 3 ∧ z.natAbs ≤ n + 3

/-- The transfer from integer solutions to common terms is unconditional. -/
theorem classify_solutions : H2 := by
  intro x y z h
  obtain ⟨hx, hy, hz⟩ := cube_residues h
  have hxn : x ≠ 0 := by rintro rfl; norm_num at hx
  have hyn : y ≠ 0 := by rintro rfl; norm_num at hy
  have hzn : z ≠ 0 := by rintro rfl; norm_num at hz
  have hyzx : y ^ 3 + z ^ 3 + x ^ 3 = 3 := by linarith only [h]
  have hzxy : z ^ 3 + x ^ 3 + y ^ 3 = 3 := by linarith only [h]
  rcases lt_or_gt_of_ne hxn with hx | hx <;>
    rcases lt_or_gt_of_ne hyn with hy | hy <;>
    rcases lt_or_gt_of_ne hzn with hz | hz
  · have hxc := cube_nonpos_of_neg hx
    have hyc := cube_nonpos_of_neg hy
    have hzc := cube_nonpos_of_neg hz
    omega
  · exact Or.inr (mixed_sign_solution h (Or.inr ⟨hx, hy, hz⟩))
  · obtain ⟨n, hn, hz', hx', hy'⟩ := mixed_sign_solution hzxy (Or.inr ⟨hz, hx, hy⟩)
    exact Or.inr ⟨n, hn, hx', hy', hz'⟩
  · obtain ⟨n, hn, hy', hz', hx'⟩ := mixed_sign_solution hyzx (Or.inl ⟨hy, hz, hx⟩)
    exact Or.inr ⟨n, hn, hx', hy', hz'⟩
  · obtain ⟨n, hn, hy', hz', hx'⟩ := mixed_sign_solution hyzx (Or.inr ⟨hy, hz, hx⟩)
    exact Or.inr ⟨n, hn, hx', hy', hz'⟩
  · obtain ⟨n, hn, hz', hx', hy'⟩ := mixed_sign_solution hzxy (Or.inl ⟨hz, hx, hy⟩)
    exact Or.inr ⟨n, hn, hx', hy', hz'⟩
  · exact Or.inr (mixed_sign_solution h (Or.inl ⟨hx, hy, hz⟩))
  · have hxc := le_cube_of_pos hx
    have hyc := le_cube_of_pos hy
    have hzc := le_cube_of_pos hz
    exact Or.inl (by omega)

private theorem natAbs_mem_Icc {x : ℤ} {N : ℕ} (hx : x.natAbs ≤ N) :
    x ∈ Set.Icc (-(N : ℤ)) (N : ℤ) := by
  change -(N : ℤ) ≤ x ∧ x ≤ (N : ℤ)
  have hcast : (x.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hx
  by_cases hs : 0 ≤ x
  · rw [Int.natAbs_of_nonneg hs] at hcast
    omega
  · rw [cast_natAbs_of_neg (lt_of_not_ge hs)] at hcast
    omega

/-- Infinitely many common terms also give infinitely many solutions of the cubic equation. -/
theorem infinite_three_cube_solutions_of_infinite_common :
    (type_of% @OMA.S_oeis_a003325.main) → H1 := by
  intro hinf hfinite
  let value (p : ℤ × ℤ × ℤ) : ℕ := p.1.natAbs ^ 3 + p.2.1.natAbs ^ 3
  apply hinf ((hfinite.image value).subset ?_)
  intro n hn
  obtain ⟨⟨a, b, _, _, rfl⟩, c, hc⟩ := hn
  rcases hc with hc | hc
  · refine ⟨((a : ℤ), (b : ℤ), -(c : ℤ)), ?_, by simp [value]⟩
    change (a : ℤ) ^ 3 + (b : ℤ) ^ 3 + (-(c : ℤ)) ^ 3 = 3
    have hc' : (a : ℤ) ^ 3 + (b : ℤ) ^ 3 = (c : ℤ) ^ 3 + 3 := by exact_mod_cast hc
    nlinarith only [hc']
  · refine ⟨(-(a : ℤ), -(b : ℤ), (c : ℤ)), ?_, by simp [value]⟩
    change (-(a : ℤ)) ^ 3 + (-(b : ℤ)) ^ 3 + (c : ℤ) ^ 3 = 3
    have hc' : (a : ℤ) ^ 3 + (b : ℤ) ^ 3 + 3 = (c : ℤ) ^ 3 := by exact_mod_cast hc
    nlinarith only [hc']

/-- A finite set of common terms would put all integer solutions in a finite box. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a003325.main := by
  intro hinf transfer hfinite
  obtain ⟨N, hN⟩ := hfinite.bddAbove
  let box := Set.Icc (-((N + 3 : ℕ) : ℤ)) ((N + 3 : ℕ) : ℤ)
  have hbox : box.Finite := Set.finite_Icc _ _
  apply hinf ((hbox.prod (hbox.prod hbox)).subset ?_)
  rintro ⟨x, y, z⟩ (h : x ^ 3 + y ^ 3 + z ^ 3 = 3)
  change x ∈ box ∧ y ∈ box ∧ z ∈ box
  rcases transfer x y z h with ⟨rfl, rfl, rfl⟩ | ⟨n, hn, hx, hy, hz⟩
  · have hone : (1 : ℤ).natAbs ≤ N + 3 := by norm_num
    exact ⟨natAbs_mem_Icc hone, natAbs_mem_Icc hone, natAbs_mem_Icc hone⟩
  · have hb : n + 3 ≤ N + 3 := Nat.add_le_add_right (hN hn) 3
    exact ⟨natAbs_mem_Icc (hx.trans hb), natAbs_mem_Icc (hy.trans hb),
      natAbs_mem_Icc (hz.trans hb)⟩

end OMA.R_oeis_a003325_R1

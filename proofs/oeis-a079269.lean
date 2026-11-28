import OMAStatements.S_oeis_a079269
import Mathlib

namespace A079269
open OMA.S_oeis_a079269 in
lemma iterate_succ (n : ℕ) : iterate (n + 1) = iterate n + 1 / (1 + 1 / iterate n) := by
  rw [iterate]

open OMA.S_oeis_a079269 in
lemma iterate_pos (n : ℕ) : 0 < iterate n := by
  induction n with
  | zero =>
    rw [iterate]
    norm_num
  | succ n ih =>
    rw [iterate_succ]
    positivity

open OMA.S_oeis_a079269 in
lemma step_aux (q : ℚ) (hq : 0 < q) :
    (q + 1 / (1 + 1 / q)).num = q.num * (q.num + 2 * q.den) ∧
    ((q + 1 / (1 + 1 / q)).den : ℤ) = q.den * (q.num + q.den) := by
  have hp : 0 < q.num := Rat.num_pos.mpr hq
  have hd : (0 : ℤ) < q.den := by exact_mod_cast q.den_pos
  have hcop : IsCoprime q.num (q.den : ℤ) := Rat.isCoprime_num_den q
  have hB : (0 : ℤ) < q.den * (q.num + q.den) := by positivity
  have hco : IsCoprime (q.num * (q.num + 2 * q.den)) ((q.den : ℤ) * (q.num + q.den)) := by
    have c1 : IsCoprime q.num (q.num + q.den) := by
      have h := hcop.add_mul_left_right 1
      have e : (q.den : ℤ) + q.num * 1 = q.num + q.den := by ring
      rwa [e] at h
    have c2 : IsCoprime (q.num + 2 * q.den) (q.den : ℤ) := by
      have h := hcop.add_mul_left_left 2
      have e : q.num + (q.den : ℤ) * 2 = q.num + 2 * q.den := by ring
      rwa [e] at h
    have c3 : IsCoprime (q.num + 2 * q.den) (q.num + q.den) := by
      have h1 : IsCoprime (q.den : ℤ) (q.num + q.den) := by
        have h := hcop.symm.add_mul_left_right 1
        have e : q.num + (q.den : ℤ) * 1 = q.num + q.den := by ring
        rwa [e] at h
      have h := h1.add_mul_left_left 1
      have e : (q.den : ℤ) + (q.num + q.den) * 1 = q.num + 2 * q.den := by ring
      rwa [e] at h
    exact IsCoprime.mul_left (IsCoprime.mul_right hcop c1) (IsCoprime.mul_right c2 c3)
  have heq : q + 1 / (1 + 1 / q)
      = ((q.num * (q.num + 2 * q.den) : ℤ) : ℚ) / ((q.den * (q.num + q.den) : ℤ) : ℚ) := by
    obtain ⟨P, hP⟩ : ∃ P : ℚ, P = (q.num : ℚ) := ⟨_, rfl⟩
    obtain ⟨D, hD⟩ : ∃ D : ℚ, D = (q.den : ℚ) := ⟨_, rfl⟩
    have hPpos : 0 < P := by
      rw [hP]
      exact_mod_cast hp
    have hDpos : 0 < D := by
      rw [hD]
      exact_mod_cast q.den_pos
    have hq' : q = P / D := by
      rw [hP, hD]
      exact (Rat.num_div_den q).symm
    push_cast
    rw [← hP, ← hD, hq']
    have hsum : P + D ≠ 0 := by positivity
    field_simp
    ring
  have hcn : Nat.Coprime (q.num * (q.num + 2 * q.den)).natAbs
      ((q.den : ℤ) * (q.num + q.den)).natAbs := Int.isCoprime_iff_gcd_eq_one.mp hco
  rw [heq]
  exact ⟨Rat.num_div_eq_of_coprime hB hcn, Rat.den_div_eq_of_coprime hB hcn⟩

open OMA.S_oeis_a079269 in
lemma step (n : ℕ) :
    (iterate (n + 1)).num = (iterate n).num * ((iterate n).num + 2 * (iterate n).den) ∧
    ((iterate (n + 1)).den : ℤ) = (iterate n).den * ((iterate n).num + (iterate n).den) := by
  rw [iterate_succ]
  exact step_aux _ (iterate_pos n)

end A079269

theorem OMA.solution : type_of% @OMA.S_oeis_a079269.main := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have e1 : OMA.S_oeis_a079269.a (k + 2 + 1) = (OMA.S_oeis_a079269.iterate (k + 2)).num := rfl
  have e2 : OMA.S_oeis_a079269.a (k + 2) = (OMA.S_oeis_a079269.iterate (k + 1)).num := rfl
  have e3 : OMA.S_oeis_a079269.a (k + 2 - 1) = (OMA.S_oeis_a079269.iterate k).num := rfl
  rw [e1, e2, e3]
  obtain ⟨s1, s2⟩ := A079269.step k
  have t1 : (OMA.S_oeis_a079269.iterate (k + 2)).num
      = (OMA.S_oeis_a079269.iterate (k + 1)).num *
        ((OMA.S_oeis_a079269.iterate (k + 1)).num + 2 * (OMA.S_oeis_a079269.iterate (k + 1)).den) :=
    (A079269.step (k + 1)).1
  rw [t1, s2, s1]
  have hp : (0 : ℚ) < ((OMA.S_oeis_a079269.iterate k).num : ℚ) := by
    exact_mod_cast Rat.num_pos.mpr (A079269.iterate_pos k)
  push_cast
  field_simp
  ring

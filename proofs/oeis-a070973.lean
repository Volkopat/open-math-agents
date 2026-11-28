import OMAStatements.S_oeis_a070973
import Mathlib

/-!
# A070973: the surjectivity conjunct fails at `n = 1`

With `a x = sInf {k | x ∣ 3 ^ k / 2 ^ k}`, the value `1` is never attained: if `a x = 1`
then the set is nonempty, so `x ∣ 3 ^ 1 / 2 ^ 1 = 1`, hence `x = 1`; but `k = 0` then lies
in the set, forcing `a 1 = 0`. (Indeed `floor((3/2)^0) = floor((3/2)^1) = 1`.)
-/

open OMA.S_oeis_a070973 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a070973.main) := by
  intro h
  obtain ⟨x, _, hax⟩ := h.2 1
  unfold OMA.S_oeis_a070973.a at hax
  have hne : {k : ℕ | x ∣ 3 ^ k / 2 ^ k}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hax
    simp at hax
  have hmem := Nat.sInf_mem hne
  rw [hax] at hmem
  have hd : x ∣ 1 := by simpa using hmem
  have hx1 : x = 1 := Nat.dvd_one.mp hd
  subst hx1
  have hle : sInf {k : ℕ | 1 ∣ 3 ^ k / 2 ^ k} ≤ 0 := Nat.sInf_le (by simp)
  omega

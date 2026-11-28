import OMAStatements.S_mo_218348

open Polynomial OMA.S_mo_218348
open scoped BigOperators

private abbrev F := ZMod 67

private theorem hasOrder (a : F) :
    orderOf a = 33 ↔ a ^ 33 = 1 ∧ a ^ 11 ≠ 1 ∧ a ^ 3 ≠ 1 := by
  constructor
  · intro ha
    refine ⟨ha ▸ pow_orderOf_eq_one a, ?_, ?_⟩
    · intro h
      have hd := orderOf_dvd_of_pow_eq_one h
      rw [ha] at hd
      contradiction
    · intro h
      have hd := orderOf_dvd_of_pow_eq_one h
      rw [ha] at hd
      contradiction
  · rintro ⟨hp, h11, h3⟩
    have hd := orderOf_dvd_of_pow_eq_one hp
    have hle := Nat.le_of_dvd (by decide : 0 < 33) hd
    have choices : ∀ n : Fin 34, n.val ∣ 33 →
        n.val = 1 ∨ n.val = 3 ∨ n.val = 11 ∨ n.val = 33 := by decide
    rcases choices ⟨orderOf a, by omega⟩ hd with h | h | h | h
    · have ho := pow_orderOf_eq_one a
      change orderOf a = 1 at h
      rw [h, pow_one] at ho
      simp [ho] at h3
    · change orderOf a = 3 at h
      exact False.elim (h3 (h ▸ pow_orderOf_eq_one a))
    · change orderOf a = 11 at h
      exact False.elim (h11 (h ▸ pow_orderOf_eq_one a))
    · exact h

private def roots : List F :=
  [4,10,16,17,19,21,23,26,33,35,36,39,47,49,54,55,56,60,65]

private def coefficient : List F → ℕ → F
  | [], i => if i = 0 then 1 else 0
  | b :: L, 0 => -(coefficient L 0 * b)
  | b :: L, i+1 => coefficient L i - coefficient L (i+1) * b

private theorem coeff_prod (L : List F) (i : ℕ) :
    ((L.map fun b => X - C b).prod).coeff i = coefficient L i := by
  induction L generalizing i with
  | nil => simp [coefficient, Polynomial.coeff_one]
  | cons b L ih =>
    rw [List.map_cons, List.prod_cons, mul_comm, mul_sub]
    cases i <;> simp [coefficient, ih, Polynomial.coeff_sub, Polynomial.coeff_mul_C]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_218348.main) := by
  intro claim
  let A : Finset F := (6 :: roots).toFinset
  have hA : ∀ a : F, a ∈ A ↔ a ^ 33 = 1 ∧ a ^ 11 ≠ 1 ∧ a ^ 3 ≠ 1 := by decide +kernel
  have horder (a : F) : a ∈ A ↔ orderOf a = 33 := (hA a).trans (hasOrder a).symm
  have hcard : A.card = Nat.totient 33 := by decide
  have hroots : roots.Nodup := by decide
  have herase : A.erase 6 = roots.toFinset := by decide
  have hzero : (partialOrderFactor A 6).coeff 13 = 0 := by
    unfold partialOrderFactor
    rw [herase, List.prod_toFinset _ hroots, coeff_prod]
    decide +kernel
  exact claim 67 33 (by decide) (by decide) (by decide) A horder hcard 6 (by decide) 13
    (by decide) hzero
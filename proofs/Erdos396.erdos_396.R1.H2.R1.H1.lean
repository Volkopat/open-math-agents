import OMAReductions.R_Erdos396_erdos_396_R1_H2_R1
import Mathlib

open Finset

private def witness : ℕ := 20021368432952099

private def factors : Finset (ℕ × ℕ) :=
  {(2, 16), (3, 9), (5, 3), (7, 2), (11, 2), (13, 1),
  (17, 1), (19, 1), (23, 1), (31, 1), (37, 1), (41, 1),
  (43, 1), (47, 1), (53, 1), (59, 1), (61, 1), (67, 1),
  (71, 1), (101, 1), (107, 1), (113, 1), (137, 1), (149, 1),
  (151, 1), (167, 2), (311, 1), (367, 1), (379, 1), (389, 1),
  (439, 1), (449, 1), (467, 1), (1117, 1), (1693, 1), (1741, 1),
  (1873, 1), (2531, 1), (2707, 1), (3203, 1), (4973, 1), (5081, 1),
  (5273, 1), (8209, 1), (8297, 1), (8521, 1), (9199, 1), (10663, 1),
  (17959, 1), (19433, 1), (23669, 1), (34421, 1), (35099, 1), (40423, 1),
  (51241, 1), (83921, 1), (101833, 1), (116747, 1), (182107, 1), (233837, 1),
  (264827, 1), (276343, 1), (286553, 1), (288199, 1), (1214047, 1), (1953233, 1),
  (5478881, 1), (16614043, 1), (18334271, 1), (20283077, 1), (28476247, 1), (43049581, 1),
  (111998779, 1), (171687979, 1)}

private def carries (p : ℕ) : ℕ :=
  ((Ico 1 58).filter fun i => p ^ i ≤ witness % p ^ i + witness % p ^ i).card

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
private theorem factorsPrime : ∀ pe ∈ factors, pe.1.Prime := by
  intro pe hpe
  simp only [factors, mem_insert, mem_singleton] at hpe
  rcases hpe with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
    <;> norm_num

set_option maxHeartbeats 2000000 in
private theorem factorsValid : ∀ pe ∈ factors,
    Nat.log pe.1 (witness + witness) < 58 ∧ pe.2 ≤ carries pe.1 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
private theorem pairwisePowers : ∀ pe ∈ factors, ∀ qe ∈ factors,
    pe ≠ qe → Nat.Coprime (pe.1 ^ pe.2) (qe.1 ^ qe.2) := by
  decide +kernel

private theorem factorProduct :
    witness.descFactorial 17 = ∏ pe ∈ factors, pe.1 ^ pe.2 := by
  decide +kernel

private theorem witnessDivides : witness.descFactorial 17 ∣ witness.centralBinom := by
  rw [factorProduct, ← lcm_eq_prod (f := fun pe : ℕ × ℕ => pe.1 ^ pe.2) pairwisePowers]
  apply Finset.lcm_dvd
  intro pe hpe
  have hp := factorsPrime pe hpe
  obtain ⟨hlog, hcarry⟩ := factorsValid pe hpe
  apply (hp.pow_dvd_iff_le_factorization (ne_of_gt (Nat.centralBinom_pos witness))).mpr
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul, Nat.factorization_choose' hp hlog]
  exact hcarry

private theorem descDivides (n k l : ℕ) (h : k ≤ l) : n.descFactorial k ∣ n.descFactorial l := by
  induction l, h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ l _ ih =>
    rw [Nat.descFactorial_succ]
    exact ih.trans (dvd_mul_left _ _)

theorem OMA.solution : OMA.R_Erdos396_erdos_396_R1_H2_R1.H1 := by
  intro k _ hk
  exact ⟨witness, (descDivides witness (k + 1) 17 (by omega)).trans witnessDivides⟩
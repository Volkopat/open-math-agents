import OMAStatements.S_oeis_a278772
import Mathlib

open OMA.S_oeis_a278772 PowerSeries

namespace P278772

abbrev St := Fin 2 × Fin 2 × Fin 4 × Fin 3

def stp (s : St) (c : Fin 2 × Fin 2) : St :=
  (c.1, c.2, inc s.2.2.1 (decide (code c < code (s.1, s.2.1))), cmp s.2.2.2 c.1 c.2)

def C (m : ℕ) (s : St) : ℕ :=
  ∑ y : Fin m → Fin 2 × Fin 2, if ok s.1 s.2.1 s.2.2.1 s.2.2.2 (List.ofFn y) = true then 1 else 0

theorem sum_cons {n : ℕ} (f : (Fin (n + 1) → Fin 2 × Fin 2) → ℕ) :
    ∑ x, f x = ∑ c : Fin 2 × Fin 2, ∑ y : Fin n → Fin 2 × Fin 2, f (Fin.cons c y) := by
  rw [← (Fin.consEquiv (fun _ => Fin 2 × Fin 2)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem C_succ (m : ℕ) (s : St) : C (m + 1) s = ∑ c, C m (stp s c) := by
  rw [C, sum_cons]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [C]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rfl

def G : ℕ → St → ℕ
  | 0, s => if ok s.1 s.2.1 s.2.2.1 s.2.2.2 [] = true then 1 else 0
  | m + 1, s => ∑ c, G m (stp s c)

theorem CG (m : ℕ) : C m = G m := by
  induction m with
  | zero =>
    funext s
    rw [C, Fintype.sum_unique]
    rfl
  | succ m ih =>
    funext s
    rw [C_succ, ih]
    rfl

theorem a_succ (m : ℕ) : a (m + 1) = ∑ c : Fin 2 × Fin 2, G m (c.1, c.2, 0, cmp 0 c.1 c.2) := by
  unfold a
  rw [Finset.card_filter, sum_cons, ← CG]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [C]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rfl

theorem a_zero : a 0 = 0 := by decide

theorem G4 (m : ℕ) (s : St) : G (m + 1) s =
    G m (stp s (0, 0)) + G m (stp s (0, 1)) + G m (stp s (1, 0)) + G m (stp s (1, 1)) := by
  show (∑ c, G m (stp s c)) = _
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem a4 (m : ℕ) : a (m + 1) = G m (0, 0, 0, 0) + G m (0, 1, 0, 2) + (G m (1, 0, 0, 1) + G m (1, 1, 0, 0)) := by
  rw [a_succ]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  rfl

theorem Hs (m : ℕ) :
    G (m + 1) (0, 0, 0, 0) = G m (0, 0, 0, 0) + G m (0, 1, 0, 2) + G m (1, 0, 0, 1) + G m (1, 1, 0, 0) ∧
    G (m + 1) (0, 0, 0, 1) = G m (0, 0, 0, 1) + G m (0, 1, 0, 1) + G m (1, 0, 0, 1) + G m (1, 1, 0, 1) ∧
    G (m + 1) (0, 0, 0, 2) = G m (0, 0, 0, 2) + G m (0, 1, 0, 2) + G m (1, 0, 0, 2) + G m (1, 1, 0, 2) ∧
    G (m + 1) (0, 0, 1, 0) = G m (0, 0, 1, 0) + G m (0, 1, 1, 2) + G m (1, 0, 1, 1) + G m (1, 1, 1, 0) ∧
    G (m + 1) (0, 0, 1, 1) = G m (0, 0, 1, 1) + G m (0, 1, 1, 1) + G m (1, 0, 1, 1) + G m (1, 1, 1, 1) ∧
    G (m + 1) (0, 0, 1, 2) = G m (0, 0, 1, 2) + G m (0, 1, 1, 2) + G m (1, 0, 1, 2) + G m (1, 1, 1, 2) ∧
    G (m + 1) (0, 0, 2, 0) = G m (0, 0, 2, 0) + G m (0, 1, 2, 2) + G m (1, 0, 2, 1) + G m (1, 1, 2, 0) ∧
    G (m + 1) (0, 0, 2, 1) = G m (0, 0, 2, 1) + G m (0, 1, 2, 1) + G m (1, 0, 2, 1) + G m (1, 1, 2, 1) ∧
    G (m + 1) (0, 0, 2, 2) = G m (0, 0, 2, 2) + G m (0, 1, 2, 2) + G m (1, 0, 2, 2) + G m (1, 1, 2, 2) ∧
    G (m + 1) (0, 0, 3, 0) = G m (0, 0, 3, 0) + G m (0, 1, 3, 2) + G m (1, 0, 3, 1) + G m (1, 1, 3, 0) ∧
    G (m + 1) (0, 0, 3, 1) = G m (0, 0, 3, 1) + G m (0, 1, 3, 1) + G m (1, 0, 3, 1) + G m (1, 1, 3, 1) ∧
    G (m + 1) (0, 0, 3, 2) = G m (0, 0, 3, 2) + G m (0, 1, 3, 2) + G m (1, 0, 3, 2) + G m (1, 1, 3, 2) ∧
    G (m + 1) (0, 1, 0, 0) = G m (0, 0, 1, 0) + G m (0, 1, 0, 2) + G m (1, 0, 0, 1) + G m (1, 1, 0, 0) ∧
    G (m + 1) (0, 1, 0, 1) = G m (0, 0, 1, 1) + G m (0, 1, 0, 1) + G m (1, 0, 0, 1) + G m (1, 1, 0, 1) ∧
    G (m + 1) (0, 1, 0, 2) = G m (0, 0, 1, 2) + G m (0, 1, 0, 2) + G m (1, 0, 0, 2) + G m (1, 1, 0, 2) ∧
    G (m + 1) (0, 1, 1, 0) = G m (0, 0, 2, 0) + G m (0, 1, 1, 2) + G m (1, 0, 1, 1) + G m (1, 1, 1, 0) ∧
    G (m + 1) (0, 1, 1, 1) = G m (0, 0, 2, 1) + G m (0, 1, 1, 1) + G m (1, 0, 1, 1) + G m (1, 1, 1, 1) ∧
    G (m + 1) (0, 1, 1, 2) = G m (0, 0, 2, 2) + G m (0, 1, 1, 2) + G m (1, 0, 1, 2) + G m (1, 1, 1, 2) ∧
    G (m + 1) (0, 1, 2, 0) = G m (0, 0, 3, 0) + G m (0, 1, 2, 2) + G m (1, 0, 2, 1) + G m (1, 1, 2, 0) ∧
    G (m + 1) (0, 1, 2, 1) = G m (0, 0, 3, 1) + G m (0, 1, 2, 1) + G m (1, 0, 2, 1) + G m (1, 1, 2, 1) ∧
    G (m + 1) (0, 1, 2, 2) = G m (0, 0, 3, 2) + G m (0, 1, 2, 2) + G m (1, 0, 2, 2) + G m (1, 1, 2, 2) ∧
    G (m + 1) (0, 1, 3, 0) = G m (0, 0, 3, 0) + G m (0, 1, 3, 2) + G m (1, 0, 3, 1) + G m (1, 1, 3, 0) ∧
    G (m + 1) (0, 1, 3, 1) = G m (0, 0, 3, 1) + G m (0, 1, 3, 1) + G m (1, 0, 3, 1) + G m (1, 1, 3, 1) ∧
    G (m + 1) (0, 1, 3, 2) = G m (0, 0, 3, 2) + G m (0, 1, 3, 2) + G m (1, 0, 3, 2) + G m (1, 1, 3, 2) ∧
    G (m + 1) (1, 0, 0, 0) = G m (0, 0, 1, 0) + G m (0, 1, 1, 2) + G m (1, 0, 0, 1) + G m (1, 1, 0, 0) ∧
    G (m + 1) (1, 0, 0, 1) = G m (0, 0, 1, 1) + G m (0, 1, 1, 1) + G m (1, 0, 0, 1) + G m (1, 1, 0, 1) ∧
    G (m + 1) (1, 0, 0, 2) = G m (0, 0, 1, 2) + G m (0, 1, 1, 2) + G m (1, 0, 0, 2) + G m (1, 1, 0, 2) ∧
    G (m + 1) (1, 0, 1, 0) = G m (0, 0, 2, 0) + G m (0, 1, 2, 2) + G m (1, 0, 1, 1) + G m (1, 1, 1, 0) ∧
    G (m + 1) (1, 0, 1, 1) = G m (0, 0, 2, 1) + G m (0, 1, 2, 1) + G m (1, 0, 1, 1) + G m (1, 1, 1, 1) ∧
    G (m + 1) (1, 0, 1, 2) = G m (0, 0, 2, 2) + G m (0, 1, 2, 2) + G m (1, 0, 1, 2) + G m (1, 1, 1, 2) ∧
    G (m + 1) (1, 0, 2, 0) = G m (0, 0, 3, 0) + G m (0, 1, 3, 2) + G m (1, 0, 2, 1) + G m (1, 1, 2, 0) ∧
    G (m + 1) (1, 0, 2, 1) = G m (0, 0, 3, 1) + G m (0, 1, 3, 1) + G m (1, 0, 2, 1) + G m (1, 1, 2, 1) ∧
    G (m + 1) (1, 0, 2, 2) = G m (0, 0, 3, 2) + G m (0, 1, 3, 2) + G m (1, 0, 2, 2) + G m (1, 1, 2, 2) ∧
    G (m + 1) (1, 0, 3, 0) = G m (0, 0, 3, 0) + G m (0, 1, 3, 2) + G m (1, 0, 3, 1) + G m (1, 1, 3, 0) ∧
    G (m + 1) (1, 0, 3, 1) = G m (0, 0, 3, 1) + G m (0, 1, 3, 1) + G m (1, 0, 3, 1) + G m (1, 1, 3, 1) ∧
    G (m + 1) (1, 0, 3, 2) = G m (0, 0, 3, 2) + G m (0, 1, 3, 2) + G m (1, 0, 3, 2) + G m (1, 1, 3, 2) ∧
    G (m + 1) (1, 1, 0, 0) = G m (0, 0, 1, 0) + G m (0, 1, 1, 2) + G m (1, 0, 1, 1) + G m (1, 1, 0, 0) ∧
    G (m + 1) (1, 1, 0, 1) = G m (0, 0, 1, 1) + G m (0, 1, 1, 1) + G m (1, 0, 1, 1) + G m (1, 1, 0, 1) ∧
    G (m + 1) (1, 1, 0, 2) = G m (0, 0, 1, 2) + G m (0, 1, 1, 2) + G m (1, 0, 1, 2) + G m (1, 1, 0, 2) ∧
    G (m + 1) (1, 1, 1, 0) = G m (0, 0, 2, 0) + G m (0, 1, 2, 2) + G m (1, 0, 2, 1) + G m (1, 1, 1, 0) ∧
    G (m + 1) (1, 1, 1, 1) = G m (0, 0, 2, 1) + G m (0, 1, 2, 1) + G m (1, 0, 2, 1) + G m (1, 1, 1, 1) ∧
    G (m + 1) (1, 1, 1, 2) = G m (0, 0, 2, 2) + G m (0, 1, 2, 2) + G m (1, 0, 2, 2) + G m (1, 1, 1, 2) ∧
    G (m + 1) (1, 1, 2, 0) = G m (0, 0, 3, 0) + G m (0, 1, 3, 2) + G m (1, 0, 3, 1) + G m (1, 1, 2, 0) ∧
    G (m + 1) (1, 1, 2, 1) = G m (0, 0, 3, 1) + G m (0, 1, 3, 1) + G m (1, 0, 3, 1) + G m (1, 1, 2, 1) ∧
    G (m + 1) (1, 1, 2, 2) = G m (0, 0, 3, 2) + G m (0, 1, 3, 2) + G m (1, 0, 3, 2) + G m (1, 1, 2, 2) ∧
    G (m + 1) (1, 1, 3, 0) = G m (0, 0, 3, 0) + G m (0, 1, 3, 2) + G m (1, 0, 3, 1) + G m (1, 1, 3, 0) ∧
    G (m + 1) (1, 1, 3, 1) = G m (0, 0, 3, 1) + G m (0, 1, 3, 1) + G m (1, 0, 3, 1) + G m (1, 1, 3, 1) ∧
    G (m + 1) (1, 1, 3, 2) = G m (0, 0, 3, 2) + G m (0, 1, 3, 2) + G m (1, 0, 3, 2) + G m (1, 1, 3, 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [G4]; rfl)

set_option maxHeartbeats 4000000 in
theorem Hf (m : ℕ) :
    (G m (0, 0, 0, 0) : ℚ) = (-11 / 168 : ℚ) * (m : ℚ) ^ 1 + (-2167 / 50400 : ℚ) * (m : ℚ) ^ 2 + (197 / 4032 : ℚ) * (m : ℚ) ^ 3 + (12329 / 362880 : ℚ) * (m : ℚ) ^ 4 + (167 / 11520 : ℚ) * (m : ℚ) ^ 5 + (1513 / 172800 : ℚ) * (m : ℚ) ^ 6 + (17 / 8064 : ℚ) * (m : ℚ) ^ 7 + (1 / 3780 : ℚ) * (m : ℚ) ^ 8 + (1 / 80640 : ℚ) * (m : ℚ) ^ 9 + (1 / 3628800 : ℚ) * (m : ℚ) ^ 10 ∧
    (G m (0, 0, 0, 1) : ℚ) = (-289 / 3960 : ℚ) * (m : ℚ) ^ 1 + (-47 / 50400 : ℚ) * (m : ℚ) ^ 2 + (13607 / 129600 : ℚ) * (m : ℚ) ^ 3 + (89 / 24192 : ℚ) * (m : ℚ) ^ 4 + (-25591 / 725760 : ℚ) * (m : ℚ) ^ 5 + (-97 / 28800 : ℚ) * (m : ℚ) ^ 6 + (553 / 172800 : ℚ) * (m : ℚ) ^ 7 + (5 / 8064 : ℚ) * (m : ℚ) ^ 8 + (1 / 20736 : ℚ) * (m : ℚ) ^ 9 + (1 / 604800 : ℚ) * (m : ℚ) ^ 10 + (1 / 39916800 : ℚ) * (m : ℚ) ^ 11 ∧
    (G m (0, 0, 0, 2) : ℚ) = (-101 / 420 : ℚ) * (m : ℚ) ^ 1 + (-41 / 180 : ℚ) * (m : ℚ) ^ 2 + (127 / 720 : ℚ) * (m : ℚ) ^ 3 + (2 / 9 : ℚ) * (m : ℚ) ^ 4 + (23 / 360 : ℚ) * (m : ℚ) ^ 5 + (1 / 180 : ℚ) * (m : ℚ) ^ 6 + (1 / 5040 : ℚ) * (m : ℚ) ^ 7 ∧
    (G m (0, 0, 1, 0) : ℚ) = (1 / 12 : ℚ) * (m : ℚ) ^ 1 + (61 / 180 : ℚ) * (m : ℚ) ^ 2 + (19 / 48 : ℚ) * (m : ℚ) ^ 3 + (23 / 144 : ℚ) * (m : ℚ) ^ 4 + (1 / 48 : ℚ) * (m : ℚ) ^ 5 + (1 / 720 : ℚ) * (m : ℚ) ^ 6 ∧
    (G m (0, 0, 1, 1) : ℚ) = (-101 / 420 : ℚ) * (m : ℚ) ^ 1 + (-41 / 180 : ℚ) * (m : ℚ) ^ 2 + (127 / 720 : ℚ) * (m : ℚ) ^ 3 + (2 / 9 : ℚ) * (m : ℚ) ^ 4 + (23 / 360 : ℚ) * (m : ℚ) ^ 5 + (1 / 180 : ℚ) * (m : ℚ) ^ 6 + (1 / 5040 : ℚ) * (m : ℚ) ^ 7 ∧
    (G m (0, 0, 1, 2) : ℚ) = (1 : ℚ) + (11 / 6 : ℚ) * (m : ℚ) ^ 1 + (1 : ℚ) * (m : ℚ) ^ 2 + (1 / 6 : ℚ) * (m : ℚ) ^ 3 ∧
    (G m (0, 0, 2, 0) : ℚ) = (1 : ℚ) + (3 / 2 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (G m (0, 0, 2, 1) : ℚ) = (1 : ℚ) + (11 / 6 : ℚ) * (m : ℚ) ^ 1 + (1 : ℚ) * (m : ℚ) ^ 2 + (1 / 6 : ℚ) * (m : ℚ) ^ 3 ∧
    (G m (0, 0, 2, 2) : ℚ) = 0 ∧
    (G m (0, 0, 3, 0) : ℚ) = 0 ∧
    (G m (0, 0, 3, 1) : ℚ) = 0 ∧
    (G m (0, 0, 3, 2) : ℚ) = 0 ∧
    (G m (0, 1, 0, 0) : ℚ) = (-5 / 63 : ℚ) * (m : ℚ) ^ 1 + (-53 / 630 : ℚ) * (m : ℚ) ^ 2 + (3953 / 90720 : ℚ) * (m : ℚ) ^ 3 + (107 / 1440 : ℚ) * (m : ℚ) ^ 4 + (589 / 17280 : ℚ) * (m : ℚ) ^ 5 + (7 / 720 : ℚ) * (m : ℚ) ^ 6 + (103 / 60480 : ℚ) * (m : ℚ) ^ 7 + (1 / 10080 : ℚ) * (m : ℚ) ^ 8 + (1 / 362880 : ℚ) * (m : ℚ) ^ 9 ∧
    (G m (0, 1, 0, 1) : ℚ) = (-53 / 2520 : ℚ) * (m : ℚ) ^ 1 + (991 / 16800 : ℚ) * (m : ℚ) ^ 2 + (7447 / 181440 : ℚ) * (m : ℚ) ^ 3 + (-26227 / 362880 : ℚ) * (m : ℚ) ^ 4 + (-817 / 34560 : ℚ) * (m : ℚ) ^ 5 + (2233 / 172800 : ℚ) * (m : ℚ) ^ 6 + (437 / 120960 : ℚ) * (m : ℚ) ^ 7 + (11 / 30240 : ℚ) * (m : ℚ) ^ 8 + (11 / 725760 : ℚ) * (m : ℚ) ^ 9 + (1 / 3628800 : ℚ) * (m : ℚ) ^ 10 ∧
    (G m (0, 1, 0, 2) : ℚ) = (-1 / 20 : ℚ) * (m : ℚ) ^ 1 + (23 / 90 : ℚ) * (m : ℚ) ^ 2 + (25 / 48 : ℚ) * (m : ℚ) ^ 3 + (35 / 144 : ℚ) * (m : ℚ) ^ 4 + (7 / 240 : ℚ) * (m : ℚ) ^ 5 + (1 / 720 : ℚ) * (m : ℚ) ^ 6 ∧
    (G m (0, 1, 1, 0) : ℚ) = (8 / 15 : ℚ) * (m : ℚ) ^ 1 + (11 / 12 : ℚ) * (m : ℚ) ^ 2 + (11 / 24 : ℚ) * (m : ℚ) ^ 3 + (1 / 12 : ℚ) * (m : ℚ) ^ 4 + (1 / 120 : ℚ) * (m : ℚ) ^ 5 ∧
    (G m (0, 1, 1, 1) : ℚ) = (-1 / 20 : ℚ) * (m : ℚ) ^ 1 + (23 / 90 : ℚ) * (m : ℚ) ^ 2 + (25 / 48 : ℚ) * (m : ℚ) ^ 3 + (35 / 144 : ℚ) * (m : ℚ) ^ 4 + (7 / 240 : ℚ) * (m : ℚ) ^ 5 + (1 / 720 : ℚ) * (m : ℚ) ^ 6 ∧
    (G m (0, 1, 1, 2) : ℚ) = (1 : ℚ) + (3 / 2 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (G m (0, 1, 2, 0) : ℚ) = (1 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (G m (0, 1, 2, 1) : ℚ) = (1 : ℚ) + (3 / 2 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (G m (0, 1, 2, 2) : ℚ) = 0 ∧
    (G m (0, 1, 3, 0) : ℚ) = 0 ∧
    (G m (0, 1, 3, 1) : ℚ) = 0 ∧
    (G m (0, 1, 3, 2) : ℚ) = 0 ∧
    (G m (1, 0, 0, 0) : ℚ) = (16 / 63 : ℚ) * (m : ℚ) ^ 1 + (1349 / 2520 : ℚ) * (m : ℚ) ^ 2 + (20963 / 90720 : ℚ) * (m : ℚ) ^ 3 + (-7 / 160 : ℚ) * (m : ℚ) ^ 4 + (229 / 17280 : ℚ) * (m : ℚ) ^ 5 + (1 / 120 : ℚ) * (m : ℚ) ^ 6 + (103 / 60480 : ℚ) * (m : ℚ) ^ 7 + (1 / 10080 : ℚ) * (m : ℚ) ^ 8 + (1 / 362880 : ℚ) * (m : ℚ) ^ 9 ∧
    (G m (1, 0, 0, 1) : ℚ) = (23 / 504 : ℚ) * (m : ℚ) ^ 1 + (739 / 10080 : ℚ) * (m : ℚ) ^ 2 + (-101 / 1134 : ℚ) * (m : ℚ) ^ 3 + (-35 / 384 : ℚ) * (m : ℚ) ^ 4 + (709 / 17280 : ℚ) * (m : ℚ) ^ 5 + (17 / 960 : ℚ) * (m : ℚ) ^ 6 + (29 / 12096 : ℚ) * (m : ℚ) ^ 7 + (1 / 8064 : ℚ) * (m : ℚ) ^ 8 + (1 / 362880 : ℚ) * (m : ℚ) ^ 9 ∧
    (G m (1, 0, 0, 2) : ℚ) = (17 / 60 : ℚ) * (m : ℚ) ^ 1 + (7 / 8 : ℚ) * (m : ℚ) ^ 2 + (17 / 24 : ℚ) * (m : ℚ) ^ 3 + (1 / 8 : ℚ) * (m : ℚ) ^ 4 + (1 / 120 : ℚ) * (m : ℚ) ^ 5 ∧
    (G m (1, 0, 1, 0) : ℚ) = (1 / 30 : ℚ) * (m : ℚ) ^ 1 + (5 / 12 : ℚ) * (m : ℚ) ^ 2 + (11 / 24 : ℚ) * (m : ℚ) ^ 3 + (1 / 12 : ℚ) * (m : ℚ) ^ 4 + (1 / 120 : ℚ) * (m : ℚ) ^ 5 ∧
    (G m (1, 0, 1, 1) : ℚ) = (17 / 60 : ℚ) * (m : ℚ) ^ 1 + (7 / 8 : ℚ) * (m : ℚ) ^ 2 + (17 / 24 : ℚ) * (m : ℚ) ^ 3 + (1 / 8 : ℚ) * (m : ℚ) ^ 4 + (1 / 120 : ℚ) * (m : ℚ) ^ 5 ∧
    (G m (1, 0, 1, 2) : ℚ) = (1 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (G m (1, 0, 2, 0) : ℚ) = (1 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (G m (1, 0, 2, 1) : ℚ) = (1 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (G m (1, 0, 2, 2) : ℚ) = 0 ∧
    (G m (1, 0, 3, 0) : ℚ) = 0 ∧
    (G m (1, 0, 3, 1) : ℚ) = 0 ∧
    (G m (1, 0, 3, 2) : ℚ) = 0 ∧
    (G m (1, 1, 0, 0) : ℚ) = (12 / 35 : ℚ) * (m : ℚ) ^ 1 + (7 / 20 : ℚ) * (m : ℚ) ^ 2 + (41 / 360 : ℚ) * (m : ℚ) ^ 3 + (7 / 48 : ℚ) * (m : ℚ) ^ 4 + (31 / 720 : ℚ) * (m : ℚ) ^ 5 + (1 / 240 : ℚ) * (m : ℚ) ^ 6 + (1 / 5040 : ℚ) * (m : ℚ) ^ 7 ∧
    (G m (1, 1, 0, 1) : ℚ) = (113 / 840 : ℚ) * (m : ℚ) ^ 1 + (-1129 / 10080 : ℚ) * (m : ℚ) ^ 2 + (-33 / 160 : ℚ) * (m : ℚ) ^ 3 + (63 / 640 : ℚ) * (m : ℚ) ^ 4 + (17 / 240 : ℚ) * (m : ℚ) ^ 5 + (13 / 960 : ℚ) * (m : ℚ) ^ 6 + (1 / 1120 : ℚ) * (m : ℚ) ^ 7 + (1 / 40320 : ℚ) * (m : ℚ) ^ 8 ∧
    (G m (1, 1, 0, 2) : ℚ) = (13 / 12 : ℚ) * (m : ℚ) ^ 1 + (35 / 24 : ℚ) * (m : ℚ) ^ 2 + (5 / 12 : ℚ) * (m : ℚ) ^ 3 + (1 / 24 : ℚ) * (m : ℚ) ^ 4 ∧
    (G m (1, 1, 1, 0) : ℚ) = (5 / 6 : ℚ) * (m : ℚ) ^ 1 + (1 : ℚ) * (m : ℚ) ^ 2 + (1 / 6 : ℚ) * (m : ℚ) ^ 3 ∧
    (G m (1, 1, 1, 1) : ℚ) = (13 / 12 : ℚ) * (m : ℚ) ^ 1 + (35 / 24 : ℚ) * (m : ℚ) ^ 2 + (5 / 12 : ℚ) * (m : ℚ) ^ 3 + (1 / 24 : ℚ) * (m : ℚ) ^ 4 ∧
    (G m (1, 1, 1, 2) : ℚ) = (1 : ℚ) ∧
    (G m (1, 1, 2, 0) : ℚ) = (1 : ℚ) ∧
    (G m (1, 1, 2, 1) : ℚ) = (1 : ℚ) ∧
    (G m (1, 1, 2, 2) : ℚ) = 0 ∧
    (G m (1, 1, 3, 0) : ℚ) = 0 ∧
    (G m (1, 1, 3, 1) : ℚ) = 0 ∧
    (G m (1, 1, 3, 2) : ℚ) = 0 := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show G 0 (0, 0, 0, 0) = 0 by decide]; norm_num
    · rw [show G 0 (0, 0, 0, 1) = 0 by decide]; norm_num
    · rw [show G 0 (0, 0, 0, 2) = 0 by decide]; norm_num
    · rw [show G 0 (0, 0, 1, 0) = 0 by decide]; norm_num
    · rw [show G 0 (0, 0, 1, 1) = 0 by decide]; norm_num
    · rw [show G 0 (0, 0, 1, 2) = 1 by decide]; norm_num
    · rw [show G 0 (0, 0, 2, 0) = 1 by decide]; norm_num
    · rw [show G 0 (0, 0, 2, 1) = 1 by decide]; norm_num
    · rw [show G 0 (0, 0, 2, 2) = 0 by decide]; norm_num
    · rw [show G 0 (0, 0, 3, 0) = 0 by decide]; norm_num
    · rw [show G 0 (0, 0, 3, 1) = 0 by decide]; norm_num
    · rw [show G 0 (0, 0, 3, 2) = 0 by decide]; norm_num
    · rw [show G 0 (0, 1, 0, 0) = 0 by decide]; norm_num
    · rw [show G 0 (0, 1, 0, 1) = 0 by decide]; norm_num
    · rw [show G 0 (0, 1, 0, 2) = 0 by decide]; norm_num
    · rw [show G 0 (0, 1, 1, 0) = 0 by decide]; norm_num
    · rw [show G 0 (0, 1, 1, 1) = 0 by decide]; norm_num
    · rw [show G 0 (0, 1, 1, 2) = 1 by decide]; norm_num
    · rw [show G 0 (0, 1, 2, 0) = 1 by decide]; norm_num
    · rw [show G 0 (0, 1, 2, 1) = 1 by decide]; norm_num
    · rw [show G 0 (0, 1, 2, 2) = 0 by decide]; norm_num
    · rw [show G 0 (0, 1, 3, 0) = 0 by decide]; norm_num
    · rw [show G 0 (0, 1, 3, 1) = 0 by decide]; norm_num
    · rw [show G 0 (0, 1, 3, 2) = 0 by decide]; norm_num
    · rw [show G 0 (1, 0, 0, 0) = 0 by decide]; norm_num
    · rw [show G 0 (1, 0, 0, 1) = 0 by decide]; norm_num
    · rw [show G 0 (1, 0, 0, 2) = 0 by decide]; norm_num
    · rw [show G 0 (1, 0, 1, 0) = 0 by decide]; norm_num
    · rw [show G 0 (1, 0, 1, 1) = 0 by decide]; norm_num
    · rw [show G 0 (1, 0, 1, 2) = 1 by decide]; norm_num
    · rw [show G 0 (1, 0, 2, 0) = 1 by decide]; norm_num
    · rw [show G 0 (1, 0, 2, 1) = 1 by decide]; norm_num
    · rw [show G 0 (1, 0, 2, 2) = 0 by decide]; norm_num
    · rw [show G 0 (1, 0, 3, 0) = 0 by decide]; norm_num
    · rw [show G 0 (1, 0, 3, 1) = 0 by decide]; norm_num
    · rw [show G 0 (1, 0, 3, 2) = 0 by decide]; norm_num
    · rw [show G 0 (1, 1, 0, 0) = 0 by decide]; norm_num
    · rw [show G 0 (1, 1, 0, 1) = 0 by decide]; norm_num
    · rw [show G 0 (1, 1, 0, 2) = 0 by decide]; norm_num
    · rw [show G 0 (1, 1, 1, 0) = 0 by decide]; norm_num
    · rw [show G 0 (1, 1, 1, 1) = 0 by decide]; norm_num
    · rw [show G 0 (1, 1, 1, 2) = 1 by decide]; norm_num
    · rw [show G 0 (1, 1, 2, 0) = 1 by decide]; norm_num
    · rw [show G 0 (1, 1, 2, 1) = 1 by decide]; norm_num
    · rw [show G 0 (1, 1, 2, 2) = 0 by decide]; norm_num
    · rw [show G 0 (1, 1, 3, 0) = 0 by decide]; norm_num
    · rw [show G 0 (1, 1, 3, 1) = 0 by decide]; norm_num
    · rw [show G 0 (1, 1, 3, 2) = 0 by decide]; norm_num
  | succ m ih =>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47⟩ := ih
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47⟩ := Hs m
    rw [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47]
    push_cast
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem hA (k j : ℕ) (h : j = k + 1) : (a j : ℚ) = (86 / 315 : ℚ) * (k : ℚ) ^ 1 + (2003 / 3150 : ℚ) * (k : ℚ) ^ 2 + (107869 / 181440 : ℚ) * (k : ℚ) ^ 3 + (60187 / 181440 : ℚ) * (k : ℚ) ^ 4 + (883 / 6912 : ℚ) * (k : ℚ) ^ 5 + (5533 / 172800 : ℚ) * (k : ℚ) ^ 6 + (569 / 120960 : ℚ) * (k : ℚ) ^ 7 + (47 / 120960 : ℚ) * (k : ℚ) ^ 8 + (11 / 725760 : ℚ) * (k : ℚ) ^ 9 + (1 / 3628800 : ℚ) * (k : ℚ) ^ 10 := by
  subst h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47⟩ := Hf k
  rw [a4]
  push_cast
  rw [h0, h14, h25, h36]
  ring

end P278772

open P278772 in
theorem OMA.solution : type_of% @OMA.S_oeis_a278772.main := by
  have v1 : (a 1 : ℚ) = 0 := by rw [hA 0 1 rfl]; norm_num
  have v2 : (a 2 : ℚ) = 2 := by rw [hA 1 2 rfl]; norm_num
  have v3 : (a 3 : ℚ) = 20 := by rw [hA 2 3 rfl]; norm_num
  have v4 : (a 4 : ℚ) = 117 := by rw [hA 3 4 rfl]; norm_num
  have v5 : (a 5 : ℚ) = 503 := by rw [hA 4 5 rfl]; norm_num
  have v6 : (a 6 : ℚ) = 1750 := by rw [hA 5 6 rfl]; norm_num
  have v7 : (a 7 : ℚ) = 5209 := by rw [hA 6 7 rfl]; norm_num
  have v8 : (a 8 : ℚ) = 13751 := by rw [hA 7 8 rfl]; norm_num
  have v9 : (a 9 : ℚ) = 33000 := by rw [hA 8 9 rfl]; norm_num
  have v10 : (a 10 : ℚ) = 73282 := by rw [hA 9 10 rfl]; norm_num
  have v11 : (a 11 : ℚ) = 152581 := by rw [hA 10 11 rfl]; norm_num
  refine ⟨?_, ?_⟩
  · have hL : ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * (1 - X) ^ 11 : PowerSeries ℚ) =
        (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) - C (11 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 1) + C (55 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 2) - C (165 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 3) + C (330 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 4) - C (462 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 5) + C (462 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 6) - C (330 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 7) + C (165 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 8) - C (55 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 9) + C (11 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 10) - ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 11) := by
      (try simp only [map_ofNat]) <;> ring
    have hR : (X ^ 2 * (2 - 2 * X + 7 * X ^ 2 - 14 * X ^ 3 + 12 * X ^ 4 - 5 * X ^ 5 + X ^ 6) : PowerSeries ℚ) = C (2 : ℚ) * X ^ 2 - C (2 : ℚ) * X ^ 3 + C (7 : ℚ) * X ^ 4 - C (14 : ℚ) * X ^ 5 + C (12 : ℚ) * X ^ 6 - C (5 : ℚ) * X ^ 7 + X ^ 8 := by
      (try simp only [map_ofNat, pow_one]) <;> ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
      coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    · norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
    · norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
    · norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
    · norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
    · norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
    · norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
    · norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
    · norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
    · norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
    · norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
    · norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
    · norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11]
    · simp only [show n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 12 by omega]
      have e : ∀ k : ℕ, k ≤ 11 → (n + 12 = k) = False := fun k hk => by
        simp only [eq_iff_iff, iff_false]; omega
      have e2 : ∀ k : ℕ, k ≤ 11 → (n + 12 - k = 0) = False := fun k hk => by
        simp only [eq_iff_iff, iff_false]; omega
      have e3 : ∀ k : ℕ, k ≤ 12 → (k ≤ n + 12) = True := fun k hk => by
        simp only [eq_iff_iff, iff_true]; omega
      simp only [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega), e 9 (by omega), e 10 (by omega), e 11 (by omega), e2 1 (by omega), e2 2 (by omega), e2 3 (by omega), e2 4 (by omega), e2 5 (by omega), e2 6 (by omega), e2 7 (by omega), e2 8 (by omega), e2 9 (by omega), e2 10 (by omega), e2 11 (by omega), e3 1 (by omega), e3 2 (by omega), e3 3 (by omega), e3 4 (by omega), e3 5 (by omega), e3 6 (by omega), e3 7 (by omega), e3 8 (by omega), e3 9 (by omega), e3 10 (by omega), e3 11 (by omega), if_true, if_false]
      rw [hA (n + 11) (n + 12) (by omega), hA (n + 10) (n + 12 - 1) (by omega), hA (n + 9) (n + 12 - 2) (by omega), hA (n + 8) (n + 12 - 3) (by omega), hA (n + 7) (n + 12 - 4) (by omega), hA (n + 6) (n + 12 - 5) (by omega), hA (n + 5) (n + 12 - 6) (by omega), hA (n + 4) (n + 12 - 7) (by omega), hA (n + 3) (n + 12 - 8) (by omega), hA (n + 2) (n + 12 - 9) (by omega), hA (n + 1) (n + 12 - 10) (by omega), hA n (n + 12 - 11) (by omega)]
      push_cast
      ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hA (m + 11) (m + 12) (by omega), hA (m + 10) (m + 11) (by omega), hA (m + 9) (m + 10) (by omega), hA (m + 8) (m + 9) (by omega), hA (m + 7) (m + 8) (by omega), hA (m + 6) (m + 7) (by omega), hA (m + 5) (m + 6) (by omega), hA (m + 4) (m + 5) (by omega), hA (m + 3) (m + 4) (by omega), hA (m + 2) (m + 3) (by omega), hA (m + 1) (m + 2) (by omega), hA (m) (m + 1) (by omega)]
    push_cast
    ring


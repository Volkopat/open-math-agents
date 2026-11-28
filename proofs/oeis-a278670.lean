import OMAStatements.S_oeis_a278670
import Mathlib

open OMA.S_oeis_a278670 PowerSeries

namespace P278670

abbrev St := Fin 2 × Fin 2 × Fin 3 × Fin 3

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
    G (m + 1) (0, 1, 0, 0) = G m (0, 0, 1, 0) + G m (0, 1, 0, 2) + G m (1, 0, 0, 1) + G m (1, 1, 0, 0) ∧
    G (m + 1) (0, 1, 0, 1) = G m (0, 0, 1, 1) + G m (0, 1, 0, 1) + G m (1, 0, 0, 1) + G m (1, 1, 0, 1) ∧
    G (m + 1) (0, 1, 0, 2) = G m (0, 0, 1, 2) + G m (0, 1, 0, 2) + G m (1, 0, 0, 2) + G m (1, 1, 0, 2) ∧
    G (m + 1) (0, 1, 1, 0) = G m (0, 0, 2, 0) + G m (0, 1, 1, 2) + G m (1, 0, 1, 1) + G m (1, 1, 1, 0) ∧
    G (m + 1) (0, 1, 1, 1) = G m (0, 0, 2, 1) + G m (0, 1, 1, 1) + G m (1, 0, 1, 1) + G m (1, 1, 1, 1) ∧
    G (m + 1) (0, 1, 1, 2) = G m (0, 0, 2, 2) + G m (0, 1, 1, 2) + G m (1, 0, 1, 2) + G m (1, 1, 1, 2) ∧
    G (m + 1) (0, 1, 2, 0) = G m (0, 0, 2, 0) + G m (0, 1, 2, 2) + G m (1, 0, 2, 1) + G m (1, 1, 2, 0) ∧
    G (m + 1) (0, 1, 2, 1) = G m (0, 0, 2, 1) + G m (0, 1, 2, 1) + G m (1, 0, 2, 1) + G m (1, 1, 2, 1) ∧
    G (m + 1) (0, 1, 2, 2) = G m (0, 0, 2, 2) + G m (0, 1, 2, 2) + G m (1, 0, 2, 2) + G m (1, 1, 2, 2) ∧
    G (m + 1) (1, 0, 0, 0) = G m (0, 0, 1, 0) + G m (0, 1, 1, 2) + G m (1, 0, 0, 1) + G m (1, 1, 0, 0) ∧
    G (m + 1) (1, 0, 0, 1) = G m (0, 0, 1, 1) + G m (0, 1, 1, 1) + G m (1, 0, 0, 1) + G m (1, 1, 0, 1) ∧
    G (m + 1) (1, 0, 0, 2) = G m (0, 0, 1, 2) + G m (0, 1, 1, 2) + G m (1, 0, 0, 2) + G m (1, 1, 0, 2) ∧
    G (m + 1) (1, 0, 1, 0) = G m (0, 0, 2, 0) + G m (0, 1, 2, 2) + G m (1, 0, 1, 1) + G m (1, 1, 1, 0) ∧
    G (m + 1) (1, 0, 1, 1) = G m (0, 0, 2, 1) + G m (0, 1, 2, 1) + G m (1, 0, 1, 1) + G m (1, 1, 1, 1) ∧
    G (m + 1) (1, 0, 1, 2) = G m (0, 0, 2, 2) + G m (0, 1, 2, 2) + G m (1, 0, 1, 2) + G m (1, 1, 1, 2) ∧
    G (m + 1) (1, 0, 2, 0) = G m (0, 0, 2, 0) + G m (0, 1, 2, 2) + G m (1, 0, 2, 1) + G m (1, 1, 2, 0) ∧
    G (m + 1) (1, 0, 2, 1) = G m (0, 0, 2, 1) + G m (0, 1, 2, 1) + G m (1, 0, 2, 1) + G m (1, 1, 2, 1) ∧
    G (m + 1) (1, 0, 2, 2) = G m (0, 0, 2, 2) + G m (0, 1, 2, 2) + G m (1, 0, 2, 2) + G m (1, 1, 2, 2) ∧
    G (m + 1) (1, 1, 0, 0) = G m (0, 0, 1, 0) + G m (0, 1, 1, 2) + G m (1, 0, 1, 1) + G m (1, 1, 0, 0) ∧
    G (m + 1) (1, 1, 0, 1) = G m (0, 0, 1, 1) + G m (0, 1, 1, 1) + G m (1, 0, 1, 1) + G m (1, 1, 0, 1) ∧
    G (m + 1) (1, 1, 0, 2) = G m (0, 0, 1, 2) + G m (0, 1, 1, 2) + G m (1, 0, 1, 2) + G m (1, 1, 0, 2) ∧
    G (m + 1) (1, 1, 1, 0) = G m (0, 0, 2, 0) + G m (0, 1, 2, 2) + G m (1, 0, 2, 1) + G m (1, 1, 1, 0) ∧
    G (m + 1) (1, 1, 1, 1) = G m (0, 0, 2, 1) + G m (0, 1, 2, 1) + G m (1, 0, 2, 1) + G m (1, 1, 1, 1) ∧
    G (m + 1) (1, 1, 1, 2) = G m (0, 0, 2, 2) + G m (0, 1, 2, 2) + G m (1, 0, 2, 2) + G m (1, 1, 1, 2) ∧
    G (m + 1) (1, 1, 2, 0) = G m (0, 0, 2, 0) + G m (0, 1, 2, 2) + G m (1, 0, 2, 1) + G m (1, 1, 2, 0) ∧
    G (m + 1) (1, 1, 2, 1) = G m (0, 0, 2, 1) + G m (0, 1, 2, 1) + G m (1, 0, 2, 1) + G m (1, 1, 2, 1) ∧
    G (m + 1) (1, 1, 2, 2) = G m (0, 0, 2, 2) + G m (0, 1, 2, 2) + G m (1, 0, 2, 2) + G m (1, 1, 2, 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [G4]; rfl)

theorem Hf (m : ℕ) :
    (G m (0, 0, 0, 0) : ℚ) = (1 / 12 : ℚ) * (m : ℚ) ^ 1 + (61 / 180 : ℚ) * (m : ℚ) ^ 2 + (19 / 48 : ℚ) * (m : ℚ) ^ 3 + (23 / 144 : ℚ) * (m : ℚ) ^ 4 + (1 / 48 : ℚ) * (m : ℚ) ^ 5 + (1 / 720 : ℚ) * (m : ℚ) ^ 6 ∧
    (G m (0, 0, 0, 1) : ℚ) = (-101 / 420 : ℚ) * (m : ℚ) ^ 1 + (-41 / 180 : ℚ) * (m : ℚ) ^ 2 + (127 / 720 : ℚ) * (m : ℚ) ^ 3 + (2 / 9 : ℚ) * (m : ℚ) ^ 4 + (23 / 360 : ℚ) * (m : ℚ) ^ 5 + (1 / 180 : ℚ) * (m : ℚ) ^ 6 + (1 / 5040 : ℚ) * (m : ℚ) ^ 7 ∧
    (G m (0, 0, 0, 2) : ℚ) = (1 : ℚ) + (11 / 6 : ℚ) * (m : ℚ) ^ 1 + (1 : ℚ) * (m : ℚ) ^ 2 + (1 / 6 : ℚ) * (m : ℚ) ^ 3 ∧
    (G m (0, 0, 1, 0) : ℚ) = (1 : ℚ) + (3 / 2 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (G m (0, 0, 1, 1) : ℚ) = (1 : ℚ) + (11 / 6 : ℚ) * (m : ℚ) ^ 1 + (1 : ℚ) * (m : ℚ) ^ 2 + (1 / 6 : ℚ) * (m : ℚ) ^ 3 ∧
    (G m (0, 0, 1, 2) : ℚ) = 0 ∧
    (G m (0, 0, 2, 0) : ℚ) = 0 ∧
    (G m (0, 0, 2, 1) : ℚ) = 0 ∧
    (G m (0, 0, 2, 2) : ℚ) = 0 ∧
    (G m (0, 1, 0, 0) : ℚ) = (8 / 15 : ℚ) * (m : ℚ) ^ 1 + (11 / 12 : ℚ) * (m : ℚ) ^ 2 + (11 / 24 : ℚ) * (m : ℚ) ^ 3 + (1 / 12 : ℚ) * (m : ℚ) ^ 4 + (1 / 120 : ℚ) * (m : ℚ) ^ 5 ∧
    (G m (0, 1, 0, 1) : ℚ) = (-1 / 20 : ℚ) * (m : ℚ) ^ 1 + (23 / 90 : ℚ) * (m : ℚ) ^ 2 + (25 / 48 : ℚ) * (m : ℚ) ^ 3 + (35 / 144 : ℚ) * (m : ℚ) ^ 4 + (7 / 240 : ℚ) * (m : ℚ) ^ 5 + (1 / 720 : ℚ) * (m : ℚ) ^ 6 ∧
    (G m (0, 1, 0, 2) : ℚ) = (1 : ℚ) + (3 / 2 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (G m (0, 1, 1, 0) : ℚ) = (1 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (G m (0, 1, 1, 1) : ℚ) = (1 : ℚ) + (3 / 2 : ℚ) * (m : ℚ) ^ 1 + (1 / 2 : ℚ) * (m : ℚ) ^ 2 ∧
    (G m (0, 1, 1, 2) : ℚ) = 0 ∧
    (G m (0, 1, 2, 0) : ℚ) = 0 ∧
    (G m (0, 1, 2, 1) : ℚ) = 0 ∧
    (G m (0, 1, 2, 2) : ℚ) = 0 ∧
    (G m (1, 0, 0, 0) : ℚ) = (1 / 30 : ℚ) * (m : ℚ) ^ 1 + (5 / 12 : ℚ) * (m : ℚ) ^ 2 + (11 / 24 : ℚ) * (m : ℚ) ^ 3 + (1 / 12 : ℚ) * (m : ℚ) ^ 4 + (1 / 120 : ℚ) * (m : ℚ) ^ 5 ∧
    (G m (1, 0, 0, 1) : ℚ) = (17 / 60 : ℚ) * (m : ℚ) ^ 1 + (7 / 8 : ℚ) * (m : ℚ) ^ 2 + (17 / 24 : ℚ) * (m : ℚ) ^ 3 + (1 / 8 : ℚ) * (m : ℚ) ^ 4 + (1 / 120 : ℚ) * (m : ℚ) ^ 5 ∧
    (G m (1, 0, 0, 2) : ℚ) = (1 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (G m (1, 0, 1, 0) : ℚ) = (1 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (G m (1, 0, 1, 1) : ℚ) = (1 : ℚ) + (1 : ℚ) * (m : ℚ) ^ 1 ∧
    (G m (1, 0, 1, 2) : ℚ) = 0 ∧
    (G m (1, 0, 2, 0) : ℚ) = 0 ∧
    (G m (1, 0, 2, 1) : ℚ) = 0 ∧
    (G m (1, 0, 2, 2) : ℚ) = 0 ∧
    (G m (1, 1, 0, 0) : ℚ) = (5 / 6 : ℚ) * (m : ℚ) ^ 1 + (1 : ℚ) * (m : ℚ) ^ 2 + (1 / 6 : ℚ) * (m : ℚ) ^ 3 ∧
    (G m (1, 1, 0, 1) : ℚ) = (13 / 12 : ℚ) * (m : ℚ) ^ 1 + (35 / 24 : ℚ) * (m : ℚ) ^ 2 + (5 / 12 : ℚ) * (m : ℚ) ^ 3 + (1 / 24 : ℚ) * (m : ℚ) ^ 4 ∧
    (G m (1, 1, 0, 2) : ℚ) = (1 : ℚ) ∧
    (G m (1, 1, 1, 0) : ℚ) = (1 : ℚ) ∧
    (G m (1, 1, 1, 1) : ℚ) = (1 : ℚ) ∧
    (G m (1, 1, 1, 2) : ℚ) = 0 ∧
    (G m (1, 1, 2, 0) : ℚ) = 0 ∧
    (G m (1, 1, 2, 1) : ℚ) = 0 ∧
    (G m (1, 1, 2, 2) : ℚ) = 0 := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show G 0 (0, 0, 0, 0) = 0 by decide]; norm_num
    · rw [show G 0 (0, 0, 0, 1) = 0 by decide]; norm_num
    · rw [show G 0 (0, 0, 0, 2) = 1 by decide]; norm_num
    · rw [show G 0 (0, 0, 1, 0) = 1 by decide]; norm_num
    · rw [show G 0 (0, 0, 1, 1) = 1 by decide]; norm_num
    · rw [show G 0 (0, 0, 1, 2) = 0 by decide]; norm_num
    · rw [show G 0 (0, 0, 2, 0) = 0 by decide]; norm_num
    · rw [show G 0 (0, 0, 2, 1) = 0 by decide]; norm_num
    · rw [show G 0 (0, 0, 2, 2) = 0 by decide]; norm_num
    · rw [show G 0 (0, 1, 0, 0) = 0 by decide]; norm_num
    · rw [show G 0 (0, 1, 0, 1) = 0 by decide]; norm_num
    · rw [show G 0 (0, 1, 0, 2) = 1 by decide]; norm_num
    · rw [show G 0 (0, 1, 1, 0) = 1 by decide]; norm_num
    · rw [show G 0 (0, 1, 1, 1) = 1 by decide]; norm_num
    · rw [show G 0 (0, 1, 1, 2) = 0 by decide]; norm_num
    · rw [show G 0 (0, 1, 2, 0) = 0 by decide]; norm_num
    · rw [show G 0 (0, 1, 2, 1) = 0 by decide]; norm_num
    · rw [show G 0 (0, 1, 2, 2) = 0 by decide]; norm_num
    · rw [show G 0 (1, 0, 0, 0) = 0 by decide]; norm_num
    · rw [show G 0 (1, 0, 0, 1) = 0 by decide]; norm_num
    · rw [show G 0 (1, 0, 0, 2) = 1 by decide]; norm_num
    · rw [show G 0 (1, 0, 1, 0) = 1 by decide]; norm_num
    · rw [show G 0 (1, 0, 1, 1) = 1 by decide]; norm_num
    · rw [show G 0 (1, 0, 1, 2) = 0 by decide]; norm_num
    · rw [show G 0 (1, 0, 2, 0) = 0 by decide]; norm_num
    · rw [show G 0 (1, 0, 2, 1) = 0 by decide]; norm_num
    · rw [show G 0 (1, 0, 2, 2) = 0 by decide]; norm_num
    · rw [show G 0 (1, 1, 0, 0) = 0 by decide]; norm_num
    · rw [show G 0 (1, 1, 0, 1) = 0 by decide]; norm_num
    · rw [show G 0 (1, 1, 0, 2) = 1 by decide]; norm_num
    · rw [show G 0 (1, 1, 1, 0) = 1 by decide]; norm_num
    · rw [show G 0 (1, 1, 1, 1) = 1 by decide]; norm_num
    · rw [show G 0 (1, 1, 1, 2) = 0 by decide]; norm_num
    · rw [show G 0 (1, 1, 2, 0) = 0 by decide]; norm_num
    · rw [show G 0 (1, 1, 2, 1) = 0 by decide]; norm_num
    · rw [show G 0 (1, 1, 2, 2) = 0 by decide]; norm_num
  | succ m ih =>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35⟩ := ih
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35⟩ := Hs m
    rw [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35]
    push_cast
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem hA (k j : ℕ) (h : j = k + 1) : (a j : ℚ) = (1 : ℚ) + (27 / 10 : ℚ) * (k : ℚ) ^ 1 + (977 / 360 : ℚ) * (k : ℚ) ^ 2 + (61 / 48 : ℚ) * (k : ℚ) ^ 3 + (41 / 144 : ℚ) * (k : ℚ) ^ 4 + (7 / 240 : ℚ) * (k : ℚ) ^ 5 + (1 / 720 : ℚ) * (k : ℚ) ^ 6 := by
  subst h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35⟩ := Hf k
  rw [a4]
  push_cast
  rw [h0, h11, h19, h27]
  ring

end P278670

open P278670 in
theorem OMA.solution : type_of% @OMA.S_oeis_a278670.main := by
  have v1 : (a 1 : ℚ) = 1 := by rw [hA 0 1 rfl]; norm_num
  have v2 : (a 2 : ℚ) = 8 := by rw [hA 1 2 rfl]; norm_num
  have v3 : (a 3 : ℚ) = 33 := by rw [hA 2 3 rfl]; norm_num
  have v4 : (a 4 : ℚ) = 99 := by rw [hA 3 4 rfl]; norm_num
  have v5 : (a 5 : ℚ) = 245 := by rw [hA 4 5 rfl]; norm_num
  have v6 : (a 6 : ℚ) = 532 := by rw [hA 5 6 rfl]; norm_num
  have v7 : (a 7 : ℚ) = 1050 := by rw [hA 6 7 rfl]; norm_num
  refine ⟨?_, ?_⟩
  · have hL : ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * (1 - X) ^ 7 : PowerSeries ℚ) =
        (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) - C (7 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 1) + C (21 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 2) - C (35 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 3) + C (35 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 4) - C (21 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 5) + C (7 : ℚ) * ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 6) - ((PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n)) * X ^ 7) := by
      (try simp only [map_ofNat]) <;> ring
    have hR : (X * (1 + X - 2 * X ^ 2 + X ^ 3) : PowerSeries ℚ) = X ^ 1 + X ^ 2 - C (2 : ℚ) * X ^ 3 + X ^ 4 := by
      (try simp only [map_ofNat, pow_one]) <;> ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
      coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
    · norm_num [v1, v2, v3, v4, v5, v6, v7]
    · norm_num [v1, v2, v3, v4, v5, v6, v7]
    · norm_num [v1, v2, v3, v4, v5, v6, v7]
    · norm_num [v1, v2, v3, v4, v5, v6, v7]
    · norm_num [v1, v2, v3, v4, v5, v6, v7]
    · norm_num [v1, v2, v3, v4, v5, v6, v7]
    · norm_num [v1, v2, v3, v4, v5, v6, v7]
    · norm_num [v1, v2, v3, v4, v5, v6, v7]
    · simp only [show n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 8 by omega]
      have e : ∀ k : ℕ, k ≤ 7 → (n + 8 = k) = False := fun k hk => by
        simp only [eq_iff_iff, iff_false]; omega
      have e2 : ∀ k : ℕ, k ≤ 7 → (n + 8 - k = 0) = False := fun k hk => by
        simp only [eq_iff_iff, iff_false]; omega
      have e3 : ∀ k : ℕ, k ≤ 8 → (k ≤ n + 8) = True := fun k hk => by
        simp only [eq_iff_iff, iff_true]; omega
      simp only [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega), e2 1 (by omega), e2 2 (by omega), e2 3 (by omega), e2 4 (by omega), e2 5 (by omega), e2 6 (by omega), e2 7 (by omega), e3 1 (by omega), e3 2 (by omega), e3 3 (by omega), e3 4 (by omega), e3 5 (by omega), e3 6 (by omega), e3 7 (by omega), if_true, if_false]
      rw [hA (n + 7) (n + 8) (by omega), hA (n + 6) (n + 8 - 1) (by omega), hA (n + 5) (n + 8 - 2) (by omega), hA (n + 4) (n + 8 - 3) (by omega), hA (n + 3) (n + 8 - 4) (by omega), hA (n + 2) (n + 8 - 5) (by omega), hA (n + 1) (n + 8 - 6) (by omega), hA n (n + 8 - 7) (by omega)]
      push_cast
      ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hA (m + 7) (m + 8) (by omega), hA (m + 6) (m + 7) (by omega), hA (m + 5) (m + 6) (by omega), hA (m + 4) (m + 5) (by omega), hA (m + 3) (m + 4) (by omega), hA (m + 2) (m + 3) (by omega), hA (m + 1) (m + 2) (by omega), hA (m) (m + 1) (by omega)]
    push_cast
    ring


import Mathlib.Data.Set.Function
import Mathlib.Data.Int.Basic

/-!
# The two permutations conjectured for Rule 3

Source: https://oeis.org/A257905 (Clark Kimberling, 2015, OEIS Foundation,
CC BY-SA 4.0). Time zero below is the first term in OEIS. In the positive
branch the membership test uses subtraction, while the update uses addition,
as specified in Step 2 and in both programs in the original entry.
-/

namespace OMA.S_oeis_a257905

structure History where
  a : ℤ
  d : ℤ
  earlierA : List ℤ
  earlierD : List ℤ

def step (s : History) : History :=
  let as := s.a :: s.earlierA
  let ds := s.d :: s.earlierD
  -- The ascending list covers exactly the integers 1-a < h < 0.
  let negatives := (List.range (s.a - 2).toNat).map (fun i : ℕ => 2 - s.a + (i : ℤ))
  let downward := negatives.find? (fun h => !ds.contains h && !as.contains (s.a + h))
  -- cap is a legal positive jump: it exceeds the magnitude of every old
  -- difference, and a-cap lies strictly below every old position.
  let cap := 1 + s.a.natAbs + (ds.map Int.natAbs).sum + (as.map Int.natAbs).sum
  let upward := ((List.range cap).map (fun i : ℕ => (i : ℤ) + 1)).find?
    (fun h => !ds.contains h && !as.contains (s.a - h))
  let h := downward.getD (upward.getD (cap : ℤ))
  ⟨s.a + h, h, as, ds⟩

def orbit (a : ℕ) (d : ℤ) : ℕ → History
  | 0 => ⟨a, d, [], []⟩
  | n+1 => step (orbit a d n)

def permutes (f : ℕ → ℤ) (s : Set ℤ) : Prop :=
  Function.Injective f ∧ Set.range f = s

def positions (a : ℕ) (d : ℤ) : Set ℤ :=
  if a = 0 then {z | 0 ≤ z ∧ (d ≠ 1 ∨ z ≠ 1)}
  else if a = 1 then {z | 0 < z} else {z | 1 < z}

def differences (d : ℤ) : Set ℤ := {z | d = 0 ∨ z ≠ 0}

theorem main : ∀ (a : ℕ) (d : ℤ),
    permutes (fun n => (orbit a d n).a) (positions a d) ∧
    permutes (fun n => (orbit a d n).d) (differences d) := by
  sorry

end OMA.S_oeis_a257905

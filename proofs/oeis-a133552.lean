import OMAStatements.S_oeis_a133552
import Mathlib

namespace OMA.S_oeis_a133552

def V : ℕ → List ℤ
  | 0 => (List.finRange 32).map (count 0)
  | k + 1 => (List.finRange 32).map (step fun t => (V k).getD t 0)

theorem cV (k) (s : Fin 32) : count k s = (V k).getD s 0 := by
  induction k generalizing s with
  | zero => simp [V, count, List.getD_eq_getElem?_getD]
  | succ k ih =>
    simp only [V, count, List.getD_eq_getElem?_getD] at *
    simp [← funext ih]

theorem d0 : ∀ s : Fin 32, deviation (fun j => (V j).getD s 0) = 0 := by decide +kernel

theorem dv (n) : ∀ s, deviation (fun j => count (n + j) s) = 0 := by
  induction n with
  | zero => simpa [cV] using d0
  | succ n ih =>
    intro s
    have e : (fun j => count (n + 1 + j) s) = fun j => step (count (n + j)) s :=
      funext fun j => by rw [Nat.add_right_comm]; rfl
    rw [e, show deviation (fun j => step (count (n + j)) s) =
      step (fun t => deviation fun j => count (n + j) t) s by unfold deviation step; split_ifs <;> ring]
    simp [ih, step]

theorem sm : ∀ n : Fin 15, productCoeff (fun j => (V j).getD 0 0) denominator n = numeratorCoeff n := by
  decide +kernel

end OMA.S_oeis_a133552

open OMA.S_oeis_a133552 in
theorem OMA.solution : type_of% @OMA.S_oeis_a133552.main :=
  ⟨(dv · 0), fun n => if h : n < 15 then by
    rw [show a = fun j => (V j).getD 0 0 from funext fun j => cV j 0]; exact sm ⟨n, h⟩ else by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 15 := ⟨n - 15, by omega⟩
    have := dv m 0
    have : productCoeff a [-1] m = -a m := by cases m <;> simp [productCoeff]
    simp [deviation, productCoeff, denominator, numeratorCoeff, a, add_assoc] at *
    linarith⟩

import OMAStatements.S_oeis_a131935
import Mathlib

namespace A131935Proof

open OMA.S_oeis_a131935

lemma step (st : Bool × Endpoints) :
    (advance (advance (advance (advance st)))).2.total + (advance st).2.total + st.2.total =
      (advance (advance (advance st))).2.total + 3 * (advance (advance st)).2.total := by
  obtain ⟨f, ⟨w, x, y, z⟩⟩ := st
  cases f
  · simp only [advance, oddToEven, evenToOdd, Endpoints.total]
    omega
  · simp only [advance, oddToEven, evenToOdd, Endpoints.total]
    omega

lemma rec1 (m : ℕ) : a (m + 5) + a (m + 2) + a (m + 1) = a (m + 4) + 3 * a (m + 3) :=
  step (state m)

end A131935Proof

open OMA.S_oeis_a131935 in
theorem OMA.solution : type_of% @OMA.S_oeis_a131935.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact A131935Proof.rec1 m
  · intro n
    rcases n with _ | _ | _ | _ | _ | k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · have h := A131935Proof.rec1 k
      show (1 : Int) * (a (k + 5) : Int) + ((-1 : Int) * (a (k + 4) : Int) +
        ((-3 : Int) * (a (k + 3) : Int) + ((1 : Int) * (a (k + 2) : Int) +
        ((1 : Int) * (a (k + 1) : Int) + 0)))) = 0
      omega

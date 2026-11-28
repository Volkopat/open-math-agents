import Mathlib

/-!
# Integer Lunar Lander from velocity n and altitude zero

Each move changes the velocity by at most one, then adds the new velocity
to altitude. The fourth argument of a flight is the accumulated altitude
change, with arbitrary intermediate integer altitudes as in OEIS A360923.
OEIS A360925 asks for the minimum time from (n,0) to (0,0).
-/
namespace OMA.S_oeis_a360925

inductive Flight : ℕ → ℤ → ℤ → ℤ → Prop
  | rest (u : ℤ) : Flight 0 u u 0
  | move {t : ℕ} {u v d : ℤ} (w : ℤ) : Flight t u v d →
      v-1 ≤ w → w ≤ v+1 → Flight (t+1) u w (d+w)

noncomputable def time (n : ℕ) : ℕ := open Classical in
  if h : ∃ t : ℕ, Flight t (n:ℤ) 0 0 then Nat.find h else 0

theorem main :
    (∀ n : ℕ, ∃ t : ℕ, Flight t (n:ℤ) 0 0) ∧ time 0 = 0 ∧ time 1 = 1 ∧
    (∀ n : ℕ, 2 ≤ n → time n = n+1+Nat.sqrt (2*n^2-2*n-3)) ∧
    (∀ n : ℕ, 1 ≤ n → time (n+1)-time n = 2 ∨ time (n+1)-time n = 3) := by
  sorry

end OMA.S_oeis_a360925

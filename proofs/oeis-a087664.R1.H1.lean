import OMAReductions.R_oeis_a087664_R1

/-!
Even starts of the floor recurrence in OEIS A087664.
The half-integer descent follows the proof by @grp06.
-/

open OMA.S_oeis_a087664

private def step (x : ℚ) : ℚ := x * (Int.floor x : ℚ)

private def reachesInteger (x : ℚ) : Prop :=
  ∃ k : ℕ, ∃ m : ℤ, (step^[k]) x = (m : ℚ)

private theorem floor_half (t : ℕ) : ⌊(t : ℚ) + 1 / 2⌋ = (t : ℤ) := by
  apply Int.floor_eq_iff.mpr
  rw [Int.cast_natCast]
  constructor <;> linarith

private theorem descent (j u : ℕ) (odd : Odd u) :
    reachesInteger (((2 ^ j * u + 1 : ℕ) : ℚ) + 1 / 2) := by
  induction j generalizing u with
  | zero =>
    obtain ⟨v, rfl⟩ := odd
    refine ⟨1, (v + 1 : ℤ) * (4 * v + 5), ?_⟩
    rw [Function.iterate_one, step, floor_half]
    push_cast
    ring
  | succ j ih =>
    let s := 2 ^ j * u
    have oddFactor : Odd (4 * s + 5) := ⟨2 * s + 2, by omega⟩
    obtain ⟨k, m, hm⟩ := ih (u * (4 * s + 5)) (odd.mul oddFactor)
    refine ⟨k + 1, m, ?_⟩
    rw [Function.iterate_succ_apply, ← hm]
    congr 1
    rw [step, floor_half, pow_succ]
    dsimp [s]
    push_cast
    ring

private theorem orbit (n k : ℕ) : b n k = (step^[k]) ((n : ℚ) / 4) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change step (b n k) = _
    rw [ih]

theorem OMA.solution : OMA.R_oeis_a087664_R1.H1 := by
  intro n hn he
  obtain ⟨a, ha⟩ := he
  obtain ⟨t, ht | ht⟩ := Nat.even_or_odd' a
  · refine ⟨0, (t : ℤ), ?_⟩
    rw [orbit, Function.iterate_zero_apply, show n = 4 * t by omega]
    push_cast
    ring
  · obtain ⟨j, u, hu, h⟩ := Nat.exists_eq_two_pow_mul_odd (show t - 1 ≠ 0 by omega)
    obtain ⟨k, m, hm⟩ := descent j u hu
    refine ⟨k, m, ?_⟩
    rw [orbit, ← hm, show 2 ^ j * u + 1 = t by omega, show n = 4 * t + 2 by omega]
    congr 1
    push_cast
    ring

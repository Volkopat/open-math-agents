import OMAStatements.S_oeis_a004432

/-!
Any three-square representation of a multiple of four uses three even
coordinates. Descend to a core that is odd or is two modulo four.
For every listed core, verify a representation and rule out distinct positive coordinates.
-/

namespace OMA.R_oeis_a004432_R1

open OMA.S_oeis_a004432

/-- Odd exceptional cores must belong to the stated list. -/
def H1 : Prop :=
  ∀ s : ℕ, s % 2 = 1 → IsSumOfThreeSquares s →
    ¬ IsSumOfThreeDistinctNonzeroSquares s → s ∈ exceptions

/-- Exceptional cores which are two modulo four must belong to the stated list. -/
def H2 : Prop :=
  ∀ s : ℕ, s % 4 = 2 → IsSumOfThreeSquares s →
    ¬ IsSumOfThreeDistinctNonzeroSquares s → s ∈ exceptions

section Proof

private theorem halve {n a b c : ℕ} (he : 4 * n = a ^ 2 + b ^ 2 + c ^ 2) :
    a = 2 * (a / 2) ∧ b = 2 * (b / 2) ∧ c = 2 * (c / 2) ∧
      n = (a / 2) ^ 2 + (b / 2) ^ 2 + (c / 2) ^ 2 := by
  have table : ∀ a b c : Fin 4,
      (a.val ^ 2 + b.val ^ 2 + c.val ^ 2) % 4 = 0 →
        a.val % 2 = 0 ∧ b.val % 2 = 0 ∧ c.val % 2 = 0 := by decide
  have hm := (((Nat.mod_modEq a 4).pow 2).add ((Nat.mod_modEq b 4).pow 2)).add
    ((Nat.mod_modEq c 4).pow 2)
  change _ % 4 = (a ^ 2 + b ^ 2 + c ^ 2) % 4 at hm
  rw [← he, Nat.mul_mod_right] at hm
  obtain ⟨ha, hb, hc⟩ := table ⟨a % 4, Nat.mod_lt _ (by decide)⟩
    ⟨b % 4, Nat.mod_lt _ (by decide)⟩ ⟨c % 4, Nat.mod_lt _ (by decide)⟩ hm
  change a % 4 % 2 = 0 at ha
  change b % 4 % 2 = 0 at hb
  change c % 4 % 2 = 0 at hc
  have ea : a = 2 * (a / 2) := by omega
  have eb : b = 2 * (b / 2) := by omega
  have ec : c = 2 * (c / 2) := by omega
  refine ⟨ea, eb, ec, (Nat.mul_left_cancel_iff (by decide : 0 < 4)).mp ?_⟩
  calc
    4 * n = a ^ 2 + b ^ 2 + c ^ 2 := he
    _ = 4 * ((a / 2) ^ 2 + (b / 2) ^ 2 + (c / 2) ^ 2) := by
      conv_lhs => rw [ea, eb, ec]
      ring

private theorem scale (n : ℕ) :
    (IsSumOfThreeSquares (4 * n) ∧ ¬ IsSumOfThreeDistinctNonzeroSquares (4 * n)) ↔
      (IsSumOfThreeSquares n ∧ ¬ IsSumOfThreeDistinctNonzeroSquares n) := by
  constructor
  · rintro ⟨⟨a, b, c, he⟩, h⟩
    exact ⟨⟨a / 2, b / 2, c / 2, (halve he).2.2.2⟩, by
      rintro ⟨x, y, z, hx, hy, hz, e⟩
      exact h ⟨2*x, 2*y, 2*z, by omega, by omega, by omega, by rw [e]; ring⟩⟩
  · rintro ⟨⟨a, b, c, he⟩, h⟩
    refine ⟨⟨2*a, 2*b, 2*c, by rw [he]; ring⟩, ?_⟩
    rintro ⟨x, y, z, hx, hy, hz, e⟩
    obtain ⟨ex, ey, ez, eh⟩ := halve e
    exact h ⟨x / 2, y / 2, z / 2, by omega, by omega, by omega, eh⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 30000 in
private theorem finite_nonrepresentation :
    ∀ a b c : Fin 27, 0 < a.val → a.val < b.val → b.val < c.val →
      a.val ^ 2 + b.val ^ 2 + c.val ^ 2 ∉ exceptions := by
  decide +kernel

private theorem listed_core {s : ℕ} (hs : s ∈ exceptions) :
    IsSumOfThreeSquares s ∧ ¬ IsSumOfThreeDistinctNonzeroSquares s := by
  have hbound : s ≤ 697 := by
    have h : ∀ s ∈ exceptions, s ≤ 697 := by
      intro s hs
      fin_cases hs <;> decide
    exact h s hs
  constructor
  · fin_cases hs
    all_goals first
    | exact ⟨0, 0, 1, by decide⟩
    | exact ⟨0, 1, 1, by decide⟩
    | exact ⟨1, 1, 1, by decide⟩
    | exact ⟨0, 1, 2, by decide⟩
    | exact ⟨1, 1, 2, by decide⟩
    | exact ⟨0, 0, 3, by decide⟩
    | exact ⟨0, 1, 3, by decide⟩
    | exact ⟨1, 1, 3, by decide⟩
    | exact ⟨0, 2, 3, by decide⟩
    | exact ⟨0, 1, 4, by decide⟩
    | exact ⟨0, 3, 3, by decide⟩
    | exact ⟨1, 3, 3, by decide⟩
    | exact ⟨2, 3, 3, by decide⟩
    | exact ⟨0, 0, 5, by decide⟩
    | exact ⟨1, 1, 5, by decide⟩
    | exact ⟨1, 4, 4, by decide⟩
    | exact ⟨0, 3, 5, by decide⟩
    | exact ⟨0, 1, 6, by decide⟩
    | exact ⟨3, 3, 5, by decide⟩
    | exact ⟨1, 1, 7, by decide⟩
    | exact ⟨2, 2, 7, by decide⟩
    | exact ⟨0, 3, 7, by decide⟩
    | exact ⟨3, 3, 7, by decide⟩
    | exact ⟨0, 3, 8, by decide⟩
    | exact ⟨0, 1, 9, by decide⟩
    | exact ⟨0, 2, 9, by decide⟩
    | exact ⟨0, 4, 9, by decide⟩
    | exact ⟨1, 7, 7, by decide⟩
    | exact ⟨1, 1, 10, by decide⟩
    | exact ⟨1, 1, 11, by decide⟩
    | exact ⟨0, 3, 11, by decide⟩
    | exact ⟨1, 9, 9, by decide⟩
    | exact ⟨2, 2, 13, by decide⟩
    | exact ⟨3, 3, 13, by decide⟩
    | exact ⟨0, 7, 12, by decide⟩
    | exact ⟨5, 11, 11, by decide⟩
    | exact ⟨1, 1, 25, by decide⟩
    | exact ⟨0, 11, 24, by decide⟩
  · rintro ⟨a, b, c, ha, hab, hbc, he⟩
    have hc : c < 27 := by
      by_contra! h
      have hh : 27 ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left h 2
      omega
    exact finite_nonrepresentation ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, hc⟩
      ha hab hbc (he ▸ hs)

private theorem listed_scale (i : ℕ) {s : ℕ} (hs : s ∈ exceptions) :
    IsSumOfThreeSquares (4 ^ i * s) ∧
      ¬ IsSumOfThreeDistinctNonzeroSquares (4 ^ i * s) := by
  induction i with
  | zero => simpa using listed_core hs
  | succ i ih =>
    rw [pow_succ', mul_assoc]
    exact (scale _).2 ih

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a004432.main := by
  intro odd_cases two_cases n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    constructor
    · intro h
      by_cases hd : 4 ∣ n
      · obtain ⟨m, rfl⟩ := hd
        obtain ⟨i, s, hs, he⟩ := (ih m (by omega) (by omega)).1 ((scale m).1 h)
        exact ⟨i+1, s, hs, by rw [he, pow_succ', mul_assoc]⟩
      · refine ⟨0, n, ?_, by simp⟩
        by_cases ho : n % 2 = 1
        · exact odd_cases n ho h.1 h.2
        · exact two_cases n (by omega) h.1 h.2
    · rintro ⟨i, s, hs, rfl⟩
      exact listed_scale i hs

end Proof

end OMA.R_oeis_a004432_R1

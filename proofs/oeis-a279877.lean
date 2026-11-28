import OMAStatements.S_oeis_a279877

/-!
# A279877: the stated recurrence fails at n = 8

From the left edge to the origin, the x-axis of Rule 213 at stages 2, 4, 6, 8 reads `010`,
`00111`, `0001111`, `000011111` (the pattern is symmetric). Read as this sequence does (left edge to origin, read in base 10),
this gives `a 2 = 10`, `a 4 = 111`, `a 6 = 1111`, `a 8 = 11111`. The
recurrence claimed for every `n > 6` gives `111 a 6 - 1110 a 4 + 1000 a 2 = 10111` at `n = 8`, not
`11111`. (The numerator of the generating function in the statement has degree 8, so it implies the
recurrence only for `n > 8`; stage 2 does not follow the later pattern.)

The stages `t ≤ 8` are computed as in the proof of A278898: beyond taxicab distance `t` every cell
has the background value, which alternates since bit 0 of 213 is set and bit 9 is not (`far`);
inside, a table of the stages is checked one step at a time by the kernel (`check_steps`, `table`).
-/

namespace A279877P
open OMA.S_oeis_a279877

/-- Within taxicab distance `t` of the origin. -/
def Near (t i j : ℤ) : Prop := i + j ≤ t ∧ i - j ≤ t ∧ -i + j ≤ t ∧ -i - j ≤ t

instance (t i j : ℤ) : Decidable (Near t i j) := by unfold Near; infer_instance

/-- Background value at stage `t`. -/
def bg (t : ℕ) : Bool := decide (t % 2 = 1)

/-- Beyond taxicab distance `t` every cell has the background value. -/
theorem far (t : ℕ) : ∀ i j : ℤ, ¬ Near t i j → state t i j = bg t := by
  induction t with
  | zero =>
    intro i j h
    unfold Near at h
    show decide (i = 0 ∧ j = 0) = bg 0
    simp only [bg]
    have : ¬ (i = 0 ∧ j = 0) := by omega
    simp [this]
  | succ t ih =>
    intro i j h
    show Nat.testBit 213 _ = _
    unfold Near at h
    push_cast at h
    rw [ih i j (by unfold Near; omega), ih (i - 1) j (by unfold Near; omega),
      ih (i + 1) j (by unfold Near; omega), ih i (j - 1) (by unfold Near; omega),
      ih i (j + 1) (by unfold Near; omega)]
    unfold bg
    rcases Nat.mod_two_eq_zero_or_one t with h2 | h2
    · have h3 : (t + 1) % 2 = 1 := by omega
      simp only [h2, h3, decide_true]
      decide
    · have h3 : ¬ ((t + 1) % 2 = 1) := by omega
      simp only [h2, h3, decide_true, decide_false]
      decide

/-- The cells within distance `t` at stages `t ≤ 8`, as bits `(i + 8) * 17 + (j + 8)`. -/
def code : ℕ → ℕ
  | 0 => 22300745198530623141535718272648361505980416
  | 1 => 2923059026694943346425692736459934963931514142720
  | 2 => 2923059026694943346425692736459934963931514142720
  | 3 => 50218154836422251840274857683149031648015302047738611367936
  | 4 => 383126808392577821826517028188009983678185234048745472
  | 5 => 862741330801808976966133122270327458934902612149499574182556978905088
  | 6 => 50218154832037824980635132010528268677282876302462258511872
  | 7 => 14821783202805154636853267152295403700358236722494582610878173329602017069367296
  | 8 => 6582068447439663514311250164980360352007856688662119706039156736
  | _ => 0

/-- The stages `t ≤ 8`, read from the table inside the light cone. -/
def G (t : ℕ) (i j : ℤ) : Bool :=
  if Near t i j then Nat.testBit (code t) ((i + 8) * 17 + (j + 8)).toNat else bg t

theorem check_steps : ∀ t : ℕ, t < 8 → ∀ a : ℕ, a < 17 → ∀ b : ℕ, b < 17 →
    Near ((t : ℤ) + 1) ((a : ℤ) - 8) ((b : ℤ) - 8) →
      Nat.testBit 213 ((G t ((a : ℤ) - 8) ((b : ℤ) - 8)).toNat +
        2 * ((G t ((a : ℤ) - 8 - 1) ((b : ℤ) - 8)).toNat + (G t ((a : ℤ) - 8 + 1) ((b : ℤ) - 8)).toNat +
          (G t ((a : ℤ) - 8) ((b : ℤ) - 8 - 1)).toNat + (G t ((a : ℤ) - 8) ((b : ℤ) - 8 + 1)).toNat)) =
        G (t + 1) ((a : ℤ) - 8) ((b : ℤ) - 8) := by
  decide +kernel

theorem table (t : ℕ) (ht : t ≤ 8) : ∀ i j : ℤ, state t i j = G t i j := by
  induction t with
  | zero =>
    intro i j
    show decide (i = 0 ∧ j = 0) = G 0 i j
    unfold G
    by_cases h : Near ((0 : ℕ) : ℤ) i j
    · have hi : i = 0 := by unfold Near at h; push_cast at h; omega
      have hj : j = 0 := by unfold Near at h; push_cast at h; omega
      subst hi; subst hj
      rw [if_pos h]
      decide
    · rw [if_neg h]
      have : ¬ (i = 0 ∧ j = 0) := by
        rintro ⟨rfl, rfl⟩; exact h (by decide)
      simp [this, bg]
  | succ t ih =>
    intro i j
    have ih' := ih (by omega)
    by_cases hN : Near ((t + 1 : ℕ) : ℤ) i j
    · show Nat.testBit 213 _ = _
      rw [ih', ih', ih', ih', ih']
      have hi : -8 ≤ i ∧ i ≤ 8 := by unfold Near at hN; push_cast at hN; omega
      have hj : -8 ≤ j ∧ j ≤ 8 := by unfold Near at hN; push_cast at hN; omega
      have key := check_steps t (by omega) (i + 8).toNat (by omega) (j + 8).toNat (by omega)
      have ea : ((i + 8).toNat : ℤ) - 8 = i := by omega
      have eb : ((j + 8).toNat : ℤ) - 8 = j := by omega
      rw [ea, eb] at key
      exact key (by push_cast at hN; exact hN)
    · rw [far (t + 1) i j hN]
      unfold G
      rw [if_neg hN]

theorem a2 : a 2 = 10 := by unfold a; simp only [table 2 (by norm_num)]; decide +kernel
theorem a4 : a 4 = 111 := by unfold a; simp only [table 4 (by norm_num)]; decide +kernel
theorem a6 : a 6 = 1111 := by unfold a; simp only [table 6 (by norm_num)]; decide +kernel
theorem a8 : a 8 = 11111 := by unfold a; simp only [table 8 (by norm_num)]; decide +kernel

end A279877P

open A279877P in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a279877.main) := by
  intro h
  have h8 := h.1 8 (by norm_num)
  rw [show (8 : ℕ) - 2 = 6 by rfl, show (8 : ℕ) - 4 = 4 by rfl, show (8 : ℕ) - 6 = 2 by rfl,
    a8, a6, a4, a2] at h8
  have : ¬ (((11111 : ℕ) : ℤ) = 111 * ((1111 : ℕ) : ℤ) - 1110 * ((111 : ℕ) : ℤ) + 1000 * ((10 : ℕ) : ℤ)) := by norm_num
  exact this h8

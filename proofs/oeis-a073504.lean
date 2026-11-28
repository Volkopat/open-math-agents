import OMAStatements.S_oeis_a073504
import Mathlib

open OMA.S_oeis_a073504

private lemma rounded73504_digit_step (d : ℤ) :
    digitSum d = d % 2 + digitSum (d / (-2)) := by
  by_cases hd : d = 0
  · simp [hd]
  · rw [digitSum, if_neg hd]

private lemma rounded73504_invariant (n k : ℕ) :
    let x := term n k / 2
    let y := term n (k+1) / 2
    x + 2*y - digitSum (x-y) = (n : ℤ) - digitSum n := by
  induction k with
  | zero =>
    change 1/2 + 2*((n:ℤ)/2) - digitSum (1/2-(n:ℤ)/2) = n - digitSum n
    rw [rounded73504_digit_step (n:ℤ)]
    have h : (1:ℤ)/2 - (n:ℤ)/2 = (n:ℤ)/(-2) := by omega
    rw [h]
    omega
  | succ k ih =>
    let x := term n k / 2
    let y := term n (k+1) / 2
    let z := (x+y)/2
    change x+2*y-digitSum (x-y) = (n:ℤ)-digitSum n at ih
    change y+2*z-digitSum (y-z) = (n:ℤ)-digitSum n
    have hd : y-z = (x-y)/(-2) := by dsimp only [z]; omega
    rw [← ih, rounded73504_digit_step (x-y), ← hd]
    dsimp only [z]
    omega

/-- The two rounded terms coincide after finitely many steps. -/
theorem rounded73504_reaches (n : ℕ) :
    ∃ k : ℕ, term n k / 2 = term n (k+1) / 2 := by
  let d (j : ℕ) := term n j / 2 - term n (j+1) / 2
  let weight (x : ℤ) := (if x < 0 then 1 - 2*x else 2*x).toNat
  have step (j : ℕ) : d (j+1) = d j / (-2) := by
    change term n (j+1) / 2 - term n (j+2) / 2 =
      (term n j / 2 - term n (j+1) / 2) / (-2)
    rw [term]
    omega
  have drops (x : ℤ) (hx : x ≠ 0) : weight (x / (-2)) < weight x := by
    dsimp only [weight]
    split_ifs <;> omega
  have reach (v : ℕ) : ∀ j, weight (d j) = v →
      ∃ k : ℕ, term n k / 2 = term n (k+1) / 2 := by
    induction v using Nat.strong_induction_on with
    | h v ih =>
      intro j hj
      by_cases hzero : d j = 0
      · exact ⟨j, sub_eq_zero.mp hzero⟩
      · have less : weight (d (j+1)) < v := by
          rw [step, ← hj]
          exact drops _ hzero
        exact ih _ less (j+1) rfl
  exact reach _ 0 rfl

/-- Two equal rounded terms determine the eventual constant, starting two terms later. -/
theorem rounded73504_stable {n k : ℕ}
    (h : term n k / 2 = term n (k+1) / 2) :
    ∀ j : ℕ, k+2 ≤ j → term n j = 2*(term n k / 2) := by
  let v := 2*(term n k / 2)
  have hk2 : term n (k+2) = v := by
    rw [term]
    dsimp only [v]
    omega
  have hk3 : term n (k+3) = v := by
    change term n ((k+1)+2) = v
    rw [term, hk2]
    dsimp only [v]
    omega
  have both (r : ℕ) : term n (k+2+r) = v ∧ term n (k+3+r) = v := by
    induction r with
    | zero => exact ⟨hk2, hk3⟩
    | succ r ih =>
      constructor
      · rw [show k+2+(r+1) = k+3+r by omega]
        exact ih.2
      · rw [show k+3+(r+1) = (k+2+r)+2 by omega, term, ih.1,
            show k+2+r+1 = k+3+r by omega, ih.2]
        dsimp only [v]
        omega
  intro j hj
  have h' := (both (j-(k+2))).1
  rwa [show k+2+(j-(k+2)) = j by omega] at h'

theorem OMA.solution : type_of% @OMA.S_oeis_a073504.main := by
  intro n _
  obtain ⟨k, hk⟩ := rounded73504_reaches n
  have hi := rounded73504_invariant n k
  change term n k / 2 + 2*(term n (k+1) / 2) -
      digitSum (term n k / 2 - term n (k+1) / 2) = (n : ℤ) - digitSum n at hi
  have hz : digitSum 0 = 0 := by rw [digitSum]; simp
  rw [← hk, sub_self, hz, sub_zero] at hi
  exact ⟨2*(term n k / 2), by omega, k+2, rounded73504_stable hk⟩

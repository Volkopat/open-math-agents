import OMAStatements.S_oeis_a025482

/-!
Let b(n) = a(3n). Each block of a consists of b(n), b(n)+1, b(n)+2,
so it contains exactly one multiple of three. At the next scale this
forces a reset among three consecutive block starts. Adjacent values
of b therefore determine the adjacent values in their three children.
The following nineteen pairs are closed under these transitions.
-/

namespace TernaryMaximum

open OMA.S_oeis_a025482

private def b (n : ℕ) := a (3*n)
private def advance (previous input : ℕ) : ℕ :=
  if input % 3 = 0 then input / 3 else previous + 3

private theorem plus_one (n : ℕ) : a (3*n+1) = b n+1 := by
  rw [a]
  simp [b]

private theorem plus_two (n : ℕ) : a (3*n+2) = b n+2 := by
  rw [a]
  simp [show (3*n+2)%3 ≠ 0 by omega, plus_one]

private theorem step (n : ℕ) : b (n+1) = advance (b n) (a (n+1)) := by
  change a (3*(n+1)) = _
  rw [show 3*(n+1) = (3*n+2)+1 by omega, a]
  simp [show (3*n+2+1)%3 = 0 by omega, show (3*n+2+1)/3 = n+1 by omega, plus_two, advance]

private theorem reset (n : ℕ) (h : a n % 3 = 0) : b n = a n / 3 := by
  cases n with
  | zero => simp [b, a]
  | succ n => simp [step, advance, h]

private def lastStart (u : ℕ) := advance (advance (u/3) (u+1)) (u+2)

private theorem last_start (n : ℕ) : b (3*n+2) = lastStart (b n) := by
  rw [step (3*n+1), step (3*n), plus_one, plus_two]
  unfold lastStart
  by_cases h : b n % 3 = 0
  · exact congrArg (fun v => advance (advance v (b n+1)) (b n+2)) (reset (3*n) h)
  · by_cases h₁ : (b n+1) % 3 = 0
    · simp [advance, h₁]
    · have h₂ : (b n+2) % 3 = 0 := by omega
      simp [advance, h₂]

private def state (n : ℕ) := (b n, b (n+1))

private theorem starts : state 0 = (0,3) ∧ state 1 = (3,6) := by
  norm_num [state, b, a]

private def child (s : ℕ × ℕ) (d : ℕ) : ℕ × ℕ :=
  let z := lastStart s.1
  let x := advance z s.2
  let y := advance x (s.2+1)
  if d = 0 then (z,x) else if d = 1 then (x,y) else (y,advance y (s.2+2))

private theorem child_state (n d : ℕ) (hd : d < 3) :
    state (3*n+2+d) = child (state n) d := by
  let z := lastStart (b n)
  let x := advance z (b (n+1))
  let y := advance x (b (n+1)+1)
  have h₀ : b (3*n+3) = x := by
    rw [step (3*n+2), last_start, show 3*n+2+1 = 3*(n+1) by omega]
    rfl
  have h₁ : b (3*n+4) = y := by
    rw [step (3*n+3), h₀, show 3*n+3+1 = 3*(n+1)+1 by omega, plus_one]
  have h₂ : b (3*n+5) = advance y (b (n+1)+2) := by
    rw [step (3*n+4), h₁, show 3*n+4+1 = 3*(n+1)+2 by omega, plus_two]
  interval_cases d
  · exact Prod.ext (last_start n) h₀
  · exact Prod.ext h₀ h₁
  · exact Prod.ext h₁ h₂

private def states : List (ℕ × ℕ) :=
  [(0,3), (1,4), (2,5), (3,6), (4,7), (5,8), (6,1), (6,9), (7,2), (7,10),
   (8,3), (8,11), (9,4), (9,12), (10,5), (11,14), (12,15), (14,1), (15,2)]

private theorem closed : ∀ s ∈ states, ∀ d : Fin 3, child s d.val ∈ states := by decide

private theorem member (n : ℕ) : state n ∈ states := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rw [starts.1]; decide
    | 1 => rw [starts.2]; decide
    | m+2 =>
      rw [show m+2 = 3*(m/3)+2+m%3 by omega, child_state _ _ (by omega)]
      exact closed _ (ih (m/3) (by omega)) ⟨m%3, by omega⟩

theorem upper (n : ℕ) : a n ≤ 17 := by
  have small : ∀ s ∈ states, s.1 ≤ 15 := by decide
  have block (k d : ℕ) (hd : d < 3) : a (3*k+d) ≤ 17 := by
    have h : b k ≤ 15 := small _ (member k)
    interval_cases d
    · exact h.trans (by decide)
    · rw [plus_one]
      omega
    · rw [plus_two]
      omega
  calc
    a n = a (3*(n/3)+n%3) := congrArg a (by omega)
    _ ≤ 17 := block _ _ (by omega)

theorem attained : a 257 = 17 := by
  have e₁ : state 2 = child (state 0) 0 := child_state 0 0 (by decide)
  have e₂ : state 8 = child (state 2) 0 := child_state 2 0 (by decide)
  have e₃ : state 27 = child (state 8) 1 := child_state 8 1 (by decide)
  have e₄ : state 85 = child (state 27) 2 := child_state 27 2 (by decide)
  have h : (state 85).1 = 15 := by rw [e₄, e₃, e₂, e₁, starts.1]; decide
  exact (plus_two 85).trans (congrArg (· + 2) h)

end TernaryMaximum

theorem OMA.solution : type_of% @OMA.S_oeis_a025482.main :=
  ⟨TernaryMaximum.attained, TernaryMaximum.upper⟩

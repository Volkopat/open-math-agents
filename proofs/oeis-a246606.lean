import OMAStatements.S_oeis_a246606
import Mathlib

open OMA.S_oeis_a246606

/-- Taking a difference of the factorial identity supplies the extra lower-row term. -/
private lemma next_argument (k t : ℕ) :
    diff (k+1) (t+1) = ((t : ℤ)+1)*diff (k+1) t + ((k : ℤ)+1)*diff k (t+1) := by
  induction k generalizing t with
  | zero =>
    simp [diff, Nat.factorial_succ]
    ring
  | succ k ih =>
    have h₁ := ih (t+1)
    have h₀ := ih t
    have hd : diff (k+1) (t+1) = diff k (t+2) - diff k (t+1) := rfl
    change diff (k+1) (t+2) - diff (k+1) (t+1) =
      ((t : ℤ)+1)*(diff (k+1) (t+1) - diff (k+1) t) + _ * diff (k+1) (t+1)
    push_cast at h₁ ⊢
    linear_combination h₁ - h₀ - ((k : ℤ)+1)*hd

private def U (n : ℕ) := diff n (n+1)
private def V (n : ℕ) := diff n n

private lemma next_V (n : ℕ) :
    V (n+1) = ((n : ℤ)+1) * (2*U n - V n) := by
  have h := next_argument n n
  change V (n+1) = ((n : ℤ)+1)*(U n - V n) + ((n : ℤ)+1)*U n at h
  linear_combination h

private lemma next_U (n : ℕ) :
    U (n+1) = (2*(n : ℤ)+3)*V (n+1) + ((n : ℤ)+1)*U n := by
  have h := next_argument n (n+1)
  push_cast at h
  have hd : V (n+1) = diff n (n+2) - U n := rfl
  change U (n+1) = _ * V (n+1) + _ * diff n (n+2) at h
  linear_combination h - ((n : ℤ)+1)*hd

theorem OMA.solution : type_of% @OMA.S_oeis_a246606.main := by
  intro k
  cases k with
  | zero => decide
  | succ k =>
    have hu₂ := next_U (k+1)
    have hv₂ := next_V (k+1)
    have hu₁ := next_U k
    change let n : ℤ := ((k+1 : ℕ) : ℤ) + 2
           (-2*n+3)*U (k+2) + 4*(n-1)*(2*n^2-4*n+1)*U (k+1) +
           (n-1)*(n-2)*(2*n-1)*U k = 0
    dsimp only
    push_cast at hu₂ hv₂ ⊢
    linear_combination -(2*(k : ℤ)+3)*hu₂ -
      (2*(k : ℤ)+3)*(2*k+5)*hv₂ - ((k : ℤ)+2)*(2*k+5)*hu₁

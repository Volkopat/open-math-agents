import OMAStatements.S_oeis_a026019
import Mathlib.Tactic

/-!
R. J. Mathar's recurrence in OEIS A026019. Express each term as a
rational factor times choose(3n,n). The ratio of two consecutive
base binomial coefficients comes from the factorial formula. After
substituting these identities, the recurrence is a polynomial identity.
-/

namespace A026019
open OMA.S_oeis_a026019

private def binomial (n : ℕ) : ℚ := (3*n).choose n

private def correction (n : ℕ) : ℚ :=
  (n:ℚ)*((n:ℚ)-1)*((n:ℚ)-2) / ((2*(n:ℚ)+1)*(2*(n:ℚ)+2)*(2*(n:ℚ)+3))

private lemma factorial_two (n : ℕ) :
    ((n+2).factorial : ℚ) = ((n:ℚ)+2)*((n:ℚ)+1)*(n.factorial:ℚ) := by
  rw [Nat.factorial_succ (n+1),Nat.factorial_succ n]
  push_cast
  ring

private lemma factorial_three (n : ℕ) :
    ((n+3).factorial : ℚ) = ((n:ℚ)+3)*((n:ℚ)+2)*((n:ℚ)+1)*(n.factorial:ℚ) := by
  rw [Nat.factorial_succ (n+2),Nat.cast_mul,factorial_two]
  push_cast
  ring

private lemma binomial_factorial (n : ℕ) :
    binomial n = ((3*n).factorial:ℚ)/((n.factorial:ℚ)*((2*n).factorial:ℚ)) := by
  unfold binomial
  rw [Nat.cast_choose ℚ (by omega : n≤3*n),show 3*n-n=2*n by omega]

private lemma term_formula (n : ℕ) : a n = binomial n*(1-correction n) := by
  unfold a
  by_cases hn : 3≤n
  · have hcast : ((n-3:ℕ):ℚ)=(n:ℚ)-3 := Nat.cast_sub hn
    have hf := factorial_three (n-3)
    rw [show n-3+3=n by omega,hcast] at hf
    have hFactor : (n.factorial:ℚ) = (n:ℚ)*((n:ℚ)-1)*((n:ℚ)-2)*((n-3).factorial:ℚ) := by
      linear_combination hf
    have hBound : (3:ℚ) ≤ n := by exact_mod_cast hn
    have h0 : (n:ℚ) ≠ 0 := by linarith
    have h1 : (n:ℚ)-1 ≠ 0 := by linarith
    have h2 : (n:ℚ)-2 ≠ 0 := by linarith
    change binomial n - (if 3≤n then ((3*n).choose (n-3) : ℚ) else 0) = _
    rw [if_pos hn,Nat.cast_choose ℚ (by omega : n-3≤3*n),show 3*n-(n-3)=2*n+3 by omega,
      binomial_factorial,factorial_three,hFactor]
    unfold correction
    push_cast
    field_simp [h0,h1,h2]
  · interval_cases n <;> norm_num [a,binomial,correction,Nat.choose]

private lemma binomial_step (n : ℕ) :
    binomial (n+1) = 3*(3*(n:ℚ)+1)*(3*(n:ℚ)+2)/((2*(n:ℚ)+1)*(2*(n:ℚ)+2))*binomial n := by
  rw [binomial_factorial (n+1),binomial_factorial n,
    show 3*(n+1)=3*n+3 by omega,show 2*(n+1)=2*n+2 by omega,
    factorial_three,factorial_two,Nat.factorial_succ n]
  push_cast
  field_simp

end A026019

open OMA.S_oeis_a026019 A026019 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026019.main := by
  intro n hn
  let m := n-2
  have hn' : n=m+2 := by dsimp [m]; omega
  rw [hn',show m+2-1=m+1 by omega,show m+2-2=m by omega]
  simp only [term_formula]
  rw [binomial_step (m+1),binomial_step m]
  unfold correction
  push_cast
  field_simp
  ring

import OMAStatements.S_oeis_a195422
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two recurrences for the cyclic permanent sequence A195422

The rational factorial-binomial sum is used directly. Reverse the summation
index, express three downward shifts as rational multiples of a common term,
and telescope their linear combination. Both endpoints vanish. A shifted
linear combination of the resulting recurrence gives the second one.

Sources: OEIS A195422 (https://oeis.org/A195422) lists the conjectures of
R. J. Mathar. The recurrences also follow from Kaplansky and Riordan,
The probleme des menages (1946), p. 121, equations (25) and (31).
The formal proof below constructs a rational telescoping certificate.
-/

namespace Perm195

/-- The reversed summand, extended by zero beyond its natural support. -/
def term (n j : ℕ) : ℚ := if j≤n then
  (-2:ℚ)^(n-j) * (2*(n:ℚ)) * ((n+j-1).factorial:ℚ) * (j.factorial:ℚ) /
    (((n-j).factorial:ℚ)*((2*j).factorial:ℚ))
  else 0

def prev (x y : ℚ) : ℚ := -((x-1)*(x-y))/(2*x*(x+y-1))

def forward (x y : ℚ) : ℚ := -(x^2-y^2)/(4*(2*y+1))

end Perm195

namespace Perm195

open Finset

private theorem fact_pos_q (n : ℕ) : (n.factorial : ℚ) ≠ 0 := by
  exact_mod_cast (Nat.factorial_pos n).ne'

private theorem fact_pred_q {n : ℕ} (hn : 0 < n) :
    (n.factorial : ℚ) = (n : ℚ) * ((n-1).factorial : ℚ) := by
  cases n with
  | zero => omega
  | succ k => simp only [Nat.succ_sub_one, Nat.factorial_succ, Nat.cast_mul]

theorem source_sum (n : ℕ) (hn : 0 < n) :
    OMA.S_oeis_a195422.a n = ∑ j ∈ range (n+1), term n j := by
  unfold OMA.S_oeis_a195422.a
  rw [← sum_range_reflect _ (n+1)]
  apply sum_congr rfl
  intro j hj
  have h : j ≤ n := by simpa using hj
  have hp : 0 < n+j := by omega
  have hp' : ((n+j:ℕ):ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [Nat.add_sub_cancel, show 2*n-(n-j)=n+j by omega,
    show n-(n-j)=j by omega, term, if_pos h]
  rw [Nat.cast_choose ℚ (show n-j≤n+j by omega), show n+j-(n-j)=2*j by omega,
    fact_pred_q hp]
  field_simp [fact_pos_q, hp']

theorem term_next (n j : ℕ) (hn : 0 < n) (hj : j ≤ n) :
    term n (j+1) = (-(((n:ℚ)^2 - (j:ℚ)^2)) / (4*(2*(j:ℚ)+1))) * term n j := by
  rcases hj.eq_or_lt with rfl | hj
  · simp [term]
  · obtain ⟨k,hk⟩ : ∃ k, n = j+k+1 := ⟨n-(j+1),by omega⟩
    subst n
    simp only [term, if_pos (show j+1 ≤ j+k+1 by omega), if_pos (show j ≤ j+k+1 by omega),
      show j+k+1-(j+1)=k by omega, show j+k+1-j=k+1 by omega,
      show j+k+1+(j+1)-1=(j+k+1)+j by omega,
      show 2*(j+1)=(2*j+1)+1 by omega]
    rw [fact_pred_q (show 0 < j+k+1+j by omega), pow_succ (-2 : ℚ) k]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    field_simp [fact_pos_q]
    ring

end Perm195

namespace Perm195

/-- The downward ratio includes the vanishing boundary term j=n and the
zero extension for j>n, so all shifts can be summed over the same range. -/
theorem term_prev (n j : ℕ) (hn : 2≤n) :
    term (n-1) j = prev n j * term n j := by
  by_cases hj : j<n
  · let u := n-1-j
    let v := n-1+j-1
    have h₁ : n-j=u+1 := by dsimp [u]; omega
    have h₂ : n+j-1=v+1 := by dsimp [v]; omega
    have hu : ((u:ℕ):ℚ)+1=(n:ℚ)-j := by
      have h : u+1+j=n := by dsimp [u]; omega
      exact_mod_cast (show (u:ℤ)+1=n-(j:ℤ) by omega)
    have hv : ((v:ℕ):ℚ)+1=(n:ℚ)+j-1 := by
      exact_mod_cast (show (v:ℤ)+1=(n:ℤ)+j-1 by dsimp [v]; omega)
    have hp₁ : (u.factorial:ℚ)≠0 := by positivity
    have hp₂ : ((2*j).factorial:ℚ)≠0 := by positivity
    have hp₃ : (n:ℚ)≠0 := by positivity
    have hp₄ : (n:ℚ)+j-1≠0 := by rw [←hv]; positivity
    have hp₅ : (n:ℚ)-j≠0 := by rw [←hu]; positivity
    simp only [term,if_pos (by omega : j≤n-1),if_pos (by omega : j≤n),prev,
      Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
    change (-2:ℚ)^u*(2*((n:ℚ)-1))*(v.factorial:ℚ)*(j.factorial:ℚ) /
      ((u.factorial:ℚ)*((2*j).factorial:ℚ)) = _
    rw [h₁,h₂,pow_succ,Nat.factorial_succ v,Nat.factorial_succ u]
    push_cast
    rw [hu,hv]
    field_simp
  · by_cases h : j=n
    · subst j
      simp [term,prev,show ¬n≤n-1 by omega]
    · simp [term,show ¬j≤n-1 by omega,show ¬j≤n by omega]

end Perm195

namespace Perm195

/-- The rational multiplier whose forward difference gives the third-order recurrence. -/
def cert (x y : ℚ) : ℚ :=
  y*(2*y-1)*(x-2)*(2*x-2)*(2*x-3) /
    (x*(x+y-1)*(x+y-2)*(x+y-3))

theorem telescoping_algebra (x y : ℚ) (hx : 4 ≤ x) (hy : 0 ≤ y) :
    (-x+2) + (x^2-4*x+6) * prev x y +
      2*(x^2-2*x+3) * (prev (x-1) y * prev x y) +
      8*(x-1) * (prev (x-2) y * (prev (x-1) y * prev x y)) =
    forward x y * cert x (y+1) - cert x y := by
  unfold prev forward cert
  field_simp (disch := first | positivity | linarith)
  ring

theorem cert_zero (x : ℚ) : cert x 0 = 0 := by
  simp [cert]

theorem cert_diagonal (x : ℚ) (hx : 4 ≤ x) : cert x x = x-2 := by
  unfold cert
  field_simp (disch := first | positivity | linarith)
  ring

end Perm195

namespace Perm195

open Finset
open OMA.S_oeis_a195422 (a)

theorem sum_padded (n m : ℕ) (hm : 0 < m) (h : m≤n) :
    a m = ∑ j ∈ range (n+1), term m j := by
  rw [source_sum m hm]
  apply sum_subset (range_mono (Nat.succ_le_succ h))
  intro j _ hmiss
  have hj : ¬ j ≤ m := by simpa using hmiss
  simp [term,hj]

theorem local_step (n j : ℕ) (hn : 4≤n) (hj : j≤n) :
    (-(n:ℚ)+2)*term n j+((n:ℚ)^2-4*n+6)*term (n-1) j+
      2*((n:ℚ)^2-2*n+3)*term (n-2) j+8*((n:ℚ)-1)*term (n-3) j =
      cert n ((j:ℚ)+1)*term n (j+1)-cert n j*term n j := by
  have e₂ : term (n-2) j=prev ((n:ℚ)-1) j*term (n-1) j := by
    simpa only [show n-1-1=n-2 by omega,Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
      using term_prev (n-1) j (by omega)
  have e₃ : term (n-3) j=prev ((n:ℚ)-2) j*term (n-2) j := by
    simpa only [show n-2-1=n-3 by omega,Nat.cast_sub (by omega : 2≤n),Nat.cast_ofNat]
      using term_prev (n-2) j (by omega)
  have ff : term n (j+1)=forward n j*term n j := term_next n j (by omega) hj
  rw [e₃,e₂,term_prev n j (by omega),ff]
  linear_combination term n j * telescoping_algebra (n:ℚ) (j:ℚ) (by exact_mod_cast hn) (by positivity)

theorem order_three (n : ℕ) (hn : 4≤n) :
    (-(n:ℚ)+2)*a n+((n:ℚ)^2-4*n+6)*a (n-1)+
    2*((n:ℚ)^2-2*n+3)*a (n-2)+8*((n:ℚ)-1)*a (n-3)=0 := by
  let G (j : ℕ) := cert n j * term n j
  have tel (m : ℕ) : ∑ j ∈ range m, (G (j+1)-G j) = G m-G 0 := by
    induction m with
    | zero => simp
    | succ k ih => rw [sum_range_succ, ih]; ring
  have h :
      (∑ j ∈ range (n+1), ((-(n:ℚ)+2)*term n j+((n:ℚ)^2-4*n+6)*term (n-1) j+
        2*((n:ℚ)^2-2*n+3)*term (n-2) j+8*((n:ℚ)-1)*term (n-3) j)) = G (n+1)-G 0 := by
    rw [← tel]
    apply sum_congr rfl
    intro j hj
    simpa only [G,Nat.cast_add,Nat.cast_one] using local_step n j hn (by simpa using hj)
  have top : G (n+1) = 0 := by simp [G,term]
  have bot : G 0 = 0 := by simp [G,cert_zero]
  simp only [sum_add_distrib, ← mul_sum, top, bot, sub_zero] at h
  rw [sum_padded n n (by omega) le_rfl,sum_padded n (n-1) (by omega) (by omega),
    sum_padded n (n-2) (by omega) (by omega),sum_padded n (n-3) (by omega) (by omega)]
  exact h

end Perm195

namespace Perm195

theorem recurrence_identity (a : ℕ → ℚ) (n : ℕ) (hn : 1≤n) :
    ((n:ℚ)-2) * (a n-(n:ℚ)*a (n-1)-8*a (n-2)+4*((n:ℚ)-4)*a (n-3)+16*a (n-4)) =
    2*((-((n-1:ℕ):ℚ)+2)*a (n-1)+(((n-1:ℕ):ℚ)^2-4*((n-1:ℕ):ℚ)+6)*a (n-1-1)+
      2*(((n-1:ℕ):ℚ)^2-2*((n-1:ℕ):ℚ)+3)*a (n-1-2)+8*(((n-1:ℕ):ℚ)-1)*a (n-1-3)) -
    ((-(n:ℚ)+2)*a n+((n:ℚ)^2-4*n+6)*a (n-1)+
      2*((n:ℚ)^2-2*n+3)*a (n-2)+8*((n:ℚ)-1)*a (n-3)) := by
  rw [Nat.cast_sub hn]
  simp only [Nat.cast_one, Nat.sub_sub]
  norm_num
  ring

theorem four_of_three (a : ℕ → ℚ)
    (h3 : ∀ n : ℕ, 4≤n →
      (-(n:ℚ)+2)*a n+((n:ℚ)^2-4*n+6)*a (n-1)+
      2*((n:ℚ)^2-2*n+3)*a (n-2)+8*((n:ℚ)-1)*a (n-3)=0)
    (n : ℕ) (hn : 5≤n) :
    a n-(n:ℚ)*a (n-1)-8*a (n-2)+4*((n:ℚ)-4)*a (n-3)+16*a (n-4)=0 := by
  have h := recurrence_identity a n (by omega)
  rw [h3 n (by omega),h3 (n-1) (by omega)] at h
  have pos : (0:ℚ)<(n:ℚ)-2 := by
    have : (5:ℚ)≤n := by exact_mod_cast hn
    linarith
  exact (mul_eq_zero.mp (by simpa using h)).resolve_left pos.ne'

theorem three_of_four (a : ℕ → ℚ)
    (base : -2*a 4+6*a 3+22*a 2+24*a 1=0)
    (h4 : ∀ n : ℕ, 5≤n →
      a n-(n:ℚ)*a (n-1)-8*a (n-2)+4*((n:ℚ)-4)*a (n-3)+16*a (n-4)=0)
    (n : ℕ) (hn : 4≤n) :
    (-(n:ℚ)+2)*a n+((n:ℚ)^2-4*n+6)*a (n-1)+
      2*((n:ℚ)^2-2*n+3)*a (n-2)+8*((n:ℚ)-1)*a (n-3)=0 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num at *; linarith
  | succ n hn ih =>
    have h := recurrence_identity a (n+1) (by omega)
    rw [h4 (n+1) (by omega),Nat.add_sub_cancel,ih] at h
    rw [Nat.add_sub_cancel]
    linarith only [h]

end Perm195

namespace Perm195
open OMA.S_oeis_a195422

theorem first_four :
    a 1 = -3 ∧ a 2=2 ∧ a 3=2 ∧ a 4= -8 := by
  norm_num [a,Finset.sum_range_succ,Nat.choose,Nat.factorial]

theorem mathar_initial : -2*a 4+6*a 3+22*a 2+24*a 1=0 := by
  obtain ⟨h1,h2,h3,h4⟩ := first_four
  rw [h1,h2,h3,h4]
  norm_num

end Perm195

namespace Perm195

/-- In Kaplansky and Riordan's equation (31), set t = -1 and shift n once. -/
theorem three_of_kaplansky_riordan (a : ℕ → ℚ)
    (h : ∀ n : ℕ, 3 ≤ n →
      ((n : ℚ) - 2) * a n - ((n : ℚ)^2 - 2*n) * a (n-1) -
        4*n*a (n-2) = -4*(-2 : ℚ)^n)
    (n : ℕ) (hn : 4 ≤ n) :
    (-(n:ℚ)+2)*a n+((n:ℚ)^2-4*n+6)*a (n-1)+
      2*((n:ℚ)^2-2*n+3)*a (n-2)+8*((n:ℚ)-1)*a (n-3)=0 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have h₁ := h (m+1) (by omega)
  have h₂ := h m (by omega)
  have h₂₁ : m+1-2 = m-1 := by omega
  have h₃₂ : m+1-3 = m-2 := by omega
  simp only [Nat.cast_add_one, Nat.succ_eq_add_one, Nat.add_sub_cancel,
    h₂₁, h₃₂, pow_succ (-2 : ℚ)] at h₁ ⊢
  linear_combination -h₁ - 2 * h₂

theorem kaplansky_riordan_of_three (a : ℕ → ℚ)
    (base : a 3 - 3 * a 2 - 12 * a 1 = 32)
    (h3 : ∀ n : ℕ, 4 ≤ n →
      (-(n:ℚ)+2)*a n+((n:ℚ)^2-4*n+6)*a (n-1)+
        2*((n:ℚ)^2-2*n+3)*a (n-2)+8*((n:ℚ)-1)*a (n-3)=0)
    (n : ℕ) (hn : 3 ≤ n) :
    ((n : ℚ)-2)*a n - ((n:ℚ)^2-2*n)*a (n-1)-4*n*a (n-2) =
      -4*(-2:ℚ)^n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num at *; linarith
  | succ m hm ih =>
    have h := h3 (m+1) (by omega)
    have h₂₁ : m+1-2 = m-1 := by omega
    have h₃₂ : m+1-3 = m-2 := by omega
    simp only [Nat.cast_add_one, Nat.add_sub_cancel,
      h₂₁, h₃₂, pow_succ (-2 : ℚ)] at h ⊢
    linear_combination -h - 2 * ih

open OMA.S_oeis_a195422

theorem kaplansky_riordan (h3 : ∀ n : ℕ, 4 ≤ n →
      (-(n:ℚ)+2)*a n+((n:ℚ)^2-4*n+6)*a (n-1)+
        2*((n:ℚ)^2-2*n+3)*a (n-2)+8*((n:ℚ)-1)*a (n-3)=0)
    (n : ℕ) (hn : 3 ≤ n) :
    ((n : ℚ)-2)*a n - ((n:ℚ)^2-2*n)*a (n-1)-4*n*a (n-2) =
      -4*(-2:ℚ)^n := by
  apply kaplansky_riordan_of_three a _ h3 n hn
  obtain ⟨h1,h2,h3',_⟩ := first_four
  rw [h1,h2,h3']
  norm_num

theorem kaplansky_riordan_small (n : ℕ) (hn : n<3) :
    ((n : ℚ)-2)*a n - ((n:ℚ)^2-2*n)*a (n-1)-4*n*a (n-2) ≠
      -4*(-2:ℚ)^n := by
  interval_cases n <;> norm_num [a,Finset.sum_range_succ,Nat.choose,Nat.factorial]

end Perm195

open OMA.S_oeis_a195422 (a)

theorem Perm195.kaplansky_riordan_iff (n : ℕ) :
    ((n : ℚ)-2)*a n - ((n:ℚ)^2-2*n)*a (n-1)-4*n*a (n-2) = -4*(-2:ℚ)^n ↔ 3 ≤ n := by
  constructor
  · intro h
    by_contra! small
    exact kaplansky_riordan_small n small h
  · exact kaplansky_riordan order_three n

theorem OMA.solution : type_of% @OMA.S_oeis_a195422.main :=
  ⟨Perm195.order_three, Perm195.four_of_three OMA.S_oeis_a195422.a Perm195.order_three⟩

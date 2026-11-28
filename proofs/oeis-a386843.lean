import OMAStatements.S_oeis_a386843

/-!
# OEIS A386843

Reflect the summation index and normalize each term by the central factorial ratio. The rational Gosper certificate telescopes to zero at both endpoints, proving the second-order recurrence. Its two consecutive instances yield the third-order recurrence.

Source: https://oeis.org/A386843
-/

open Finset
open OMA.S_oeis_a386843

namespace Binomial386843

private def fac (n : ℕ) : ℚ := n.factorial
private theorem fac_pos (n : ℕ) : 0 < fac n := by
  unfold fac
  exact_mod_cast Nat.factorial_pos n
private theorem fac_step (n : ℕ) : fac (n+1) = (n+1:ℚ)*fac n := by
  simp [fac, Nat.factorial_succ]

private theorem chooseQ (n k : ℕ) (h : k ≤ n) :
    (n.choose k : ℚ) = fac n / (fac k * fac (n-k)) := by
  apply (eq_div_iff (mul_ne_zero (fac_pos _).ne' (fac_pos _).ne')).2
  rw [← mul_assoc]
  unfold fac
  exact_mod_cast Nat.choose_mul_factorial_mul_factorial h

private def pref (n : ℕ) : ℚ := fac (2*n+2) / (fac n)^2
private def F (n k : ℕ) : ℚ :=
  (n.choose k : ℚ)*pref n / (((n:ℚ)+k+1)*(n+k+2))

private theorem repr (n : ℕ) : (a n : ℚ) = ∑ k ∈ range (n+1), F n k := by
  unfold a
  push_cast
  rw [← sum_range_reflect (fun k : ℕ => ((2*n+2).choose k : ℚ) * ((2*n-k).choose (n-k) : ℚ)) (n+1)]
  apply sum_congr rfl
  intro k hk
  have h : k ≤ n := by simpa using hk
  simp only [Nat.add_sub_cancel]
  rw [show 2*n-(n-k)=n+k by omega, show n-(n-k)=k by omega]
  unfold F pref
  rw [chooseQ _ _ (by omega), chooseQ (n+k) k (by omega), chooseQ n k h]
  rw [show 2*n+2-(n-k)=(n+k+1)+1 by omega, show n+k-k=n by omega]
  rw [fac_step (n+k+1), fac_step (n+k)]
  push_cast
  field_simp [ne_of_gt (fac_pos _)] <;> ring

private theorem pref_step (n : ℕ) :
    pref (n+1) = pref n * ((2*(n:ℚ)+4)*(2*n+3))/(n+1)^2 := by
  unfold pref
  rw [show 2*(n+1)+2=((2*n+2)+1)+1 by omega, fac_step ((2*n+2)+1), fac_step (2*n+2), fac_step n]
  push_cast
  field_simp [ne_of_gt (fac_pos _)] <;> ring

private theorem choose_back (n k : ℕ) :
    (n.choose k : ℚ) = ((n+1).choose k : ℚ)*((n:ℚ)+1-k)/(n+1) := by
  by_cases h : k ≤ n+1
  · have e := congrArg (fun x : ℕ => (x:ℚ)) (Nat.choose_mul_succ_eq n k)
    push_cast [Nat.cast_sub h] at e
    apply (eq_div_iff (by positivity)).2
    exact e
  · rw [Nat.choose_eq_zero_of_lt (show n < k by omega), Nat.choose_eq_zero_of_lt (show n+1 < k by omega)]
    simp

private theorem choose_right (n k : ℕ) :
    (n.choose (k+1) : ℚ) = (n.choose k : ℚ)*((n:ℚ)-k)/(k+1) := by
  by_cases h : k ≤ n
  · have e := congrArg (fun x : ℕ => (x:ℚ)) (Nat.choose_succ_right_eq n k)
    push_cast [Nat.cast_sub h] at e
    exact (eq_div_iff (by positivity)).2 e
  · rw [Nat.choose_eq_zero_of_lt (show n < k+1 by omega), Nat.choose_eq_zero_of_lt (show n < k by omega)]
    simp

private def back (N k : ℚ) := N*(N-k)*(N+k+2)/((2*N+2)*(2*N+1)*(N+k))
private def right (N k : ℚ) := (N-k)*(N+k+1)/((k+1)*(N+k+3))

private theorem backF (n k : ℕ) : F n k = F (n+1) k * back (n+1) k := by
  unfold F back
  rw [choose_back n k, pref_step]
  push_cast
  field_simp <;> ring

private theorem rightF (n k : ℕ) : F n (k+1) = F n k * right n k := by
  unfold F right
  rw [choose_right]
  push_cast
  field_simp <;> ring

/-- Gosper certificate for the reflected binomial summand, relative to its top row. -/
private def R (n k : ℚ) : ℚ :=
  k*(n+1)*(n+2)*(k+n+4)*(k^2-4*k*n-3*k-5*n^2-25*n-28) /
    (2*(n+3)*(2*n+5)*(k+n+1)*(k+n+2))

set_option maxHeartbeats 4000000 in
private theorem cert (n k : ℕ) :
    right (n+2) k * R n (k+1) - R n k =
    ((n:ℚ)+2)*(n+1) - (7*(n+2)-5)*(n+1)*back (n+2) k -
      4*(n+2)*(2*(n+2)-1)*back (n+2) k*back (n+1) k := by
  unfold R right back
  field_simp
  ring

private def G (n k : ℕ) : ℚ := F (n+2) k * R n k

private theorem localSum (n k : ℕ) :
    ((n:ℚ)+2)*(n+1)*F (n+2) k - (7*(n+2)-5)*(n+1)*F (n+1) k -
    4*(n+2)*(2*(n+2)-1)*F n k = G n (k+1)-G n k := by
  unfold G
  rw [backF n k, backF (n+1) k, rightF]
  push_cast
  rw [show (n:ℚ)+1+1 = n+2 by ring]
  have h := cert n k
  linear_combination -(F (n+2) k)*h

private theorem Fzero {n k : ℕ} (h : n < k) : F n k = 0 := by
  simp [F, Nat.choose_eq_zero_of_lt h]

private theorem rec2 (n : ℕ) :
    ((n:ℚ)+2)*(n+1)*(a (n+2):ℚ) - (7*(n+2)-5)*(n+1)*(a (n+1):ℚ) -
    4*(n+2)*(2*(n+2)-1)*(a n:ℚ) = 0 := by
  have h0 : (a n : ℚ) = ∑ k ∈ range (n+3), F n k := by
    rw [repr, sum_range_succ (f := F n) (n+2), sum_range_succ (f := F n) (n+1)]
    simp [Fzero (show n<n+2 by omega), Fzero (show n<n+1 by omega)]
  have h1 : (a (n+1) : ℚ) = ∑ k ∈ range (n+3), F (n+1) k := by
    rw [repr, sum_range_succ (f := F (n+1)) (n+2)]
    simp [Fzero (show n+1<n+2 by omega)]
  rw [h0,h1,repr]
  simp_rw [mul_sum, ← sum_sub_distrib, localSum, sum_range_sub]
  simp [G,R,Fzero (show n+2<n+3 by omega)]

private theorem recZ (k : ℕ) : ((k:ℤ)+2)*(k+1)*a (k+2) -
    (7*(k+2)-5)*(k+1)*a (k+1) - 4*(k+2)*(2*(k+2)-1)*a k = 0 := by
  exact_mod_cast rec2 k

end Binomial386843

theorem OMA.solution : type_of% @OMA.S_oeis_a386843.main := by
  constructor
  · intro k
    dsimp
    have h := Binomial386843.recZ (k+1)
    push_cast at h
    have h' := Binomial386843.recZ k
    have e : (((k:ℤ)+3)-1) * (5*((k:ℤ)+3)*a (k+3) +
        3*(-13*(k+3)+11)*a (k+2) + 12*(-(k+3)-8)*a (k+1) +
        16*(2*(k+3)-3)*a k) = 0 := by
      linear_combination 5*h - 4*h'
    exact (mul_eq_zero.mp e).resolve_left (by omega)
  · intro k
    dsimp
    linear_combination Binomial386843.recZ k

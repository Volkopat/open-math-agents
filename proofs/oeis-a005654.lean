import OMAStatements.S_oeis_a005654
import Mathlib

namespace OMA.Bracelets5654

open OMA.S_oeis_a005654

private def C (n : ℕ) : ℚ := n.centralBinom
private def B (n : ℕ) : ℚ := (n-1).choose (n/2)

private theorem ratio (n : ℕ) : C (n+1) = 2*(2*(n : ℚ)+1)*C n/(n+1) := by
  apply (eq_div_iff (by positivity)).mpr
  rw [mul_comm]
  unfold C
  exact_mod_cast Nat.succ_mul_centralBinom_succ n

private theorem half (n : ℕ) (hn : 0 < n) :
    (((2*n-1).choose n : ℕ) : ℚ) = C n/2 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h : (k+1).centralBinom = 2 * (k+1+k).choose (k+1) := by
    rw [Nat.centralBinom,show 2*(k+1) = (k+1+k)+1 by omega,Nat.choose_succ_succ']
    rw [Nat.choose_symm_add]
    ring
  unfold C
  rw [h,show 2*(k+1)-1=k+1+k by omega]
  push_cast
  ring

private theorem central_res (m : ℕ) : residual C (m+4) = 0 := by
  unfold OMA.S_oeis_a005654.residual
  simp only [Nat.add_sub_cancel,show m+4-1=m+3 by omega,show m+4-2=m+2 by omega,
    show m+4-3=m+1 by omega]
  rw [ratio (m+3),ratio (m+2),ratio (m+1),ratio m]
  push_cast
  field_simp
  ring

private theorem oddB (k : ℕ) : B (2*k+1) = C k := by
  simp [B,C,Nat.centralBinom,show (2*k+1)/2=k by omega]

private theorem evenB (k : ℕ) (hk : 0 < k) : B (2*k) = C k/2 := by
  simpa [B,show 2*k/2=k by omega] using half k hk

private theorem parity5 (m : ℕ) : residual B (2*m+5) = 0 := by
  unfold OMA.S_oeis_a005654.residual
  rw [show 2*m+5-4 = 2*m+1 by omega,
    show 2*m+5-3 = 2*(m+1) by omega,
    show 2*m+5-2 = 2*(m+1)+1 by omega,
    show 2*m+5-1 = 2*(m+2) by omega,
    show 2*m+5 = 2*(m+2)+1 by omega]
  rw [oddB (m+2), evenB (m+2) (by omega), oddB (m+1), evenB (m+1) (by omega), oddB m]
  rw [ratio (m+1), ratio m]
  push_cast
  field_simp
  ring

private theorem parity6 (m : ℕ) : residual B (2*m+6) = 0 := by
  unfold OMA.S_oeis_a005654.residual
  rw [show 2*m+6-4 = 2*(m+1) by omega,
    show 2*m+6-3 = 2*(m+1)+1 by omega,
    show 2*m+6-2 = 2*(m+2) by omega,
    show 2*m+6-1 = 2*(m+2)+1 by omega,
    show 2*m+6 = 2*(m+3) by omega]
  rw [evenB (m+3) (by omega), oddB (m+2), evenB (m+2) (by omega), oddB (m+1), evenB (m+1) (by omega)]
  rw [ratio (m+2), ratio (m+1), ratio m]
  push_cast
  field_simp
  ring

private theorem value (n : ℕ) (hn : 0 < n) : a n = (C n/2+B n)/2 := by
  unfold a B
  rw [half n hn]

theorem result : type_of% @OMA.S_oeis_a005654.main := by
  intro n hn
  have hc : residual C n = 0 := by simpa [show n-4+4=n by omega] using central_res (n-4)
  have hb : residual B n = 0 := by
    by_cases h : n%2 = 1
    · simpa [show 2*((n-5)/2)+5=n by omega] using parity5 ((n-5)/2)
    · simpa [show 2*((n-6)/2)+6=n by omega] using parity6 ((n-6)/2)
  unfold OMA.S_oeis_a005654.residual at *
  rw [value n (by omega),value (n-1) (by omega),value (n-2) (by omega),
    value (n-3) (by omega),value (n-4) (by omega)]
  linear_combination hc/4 + hb/2

end OMA.Bracelets5654

theorem OMA.solution : type_of% @OMA.S_oeis_a005654.main := OMA.Bracelets5654.result

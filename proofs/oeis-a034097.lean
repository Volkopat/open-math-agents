import OMAStatements.S_oeis_a034097
import Mathlib.Tactic.Ring

namespace OMA.SquareRootInterval

private def lower (x : ℕ) : ℕ := x^2 + x/5 + 1
private def upper (x : ℕ) : ℕ := x^2 + (2*x)/5

private theorem square_one (x : ℕ) : (10*x+1)^2 = 100*x^2 + 20*x + 1 := by ring
private theorem square_two (x : ℕ) : (10*x+2)^2 = 100*x^2 + 40*x + 4 := by ring
private theorem square_next (x : ℕ) : (10*x+10)^2 = 100*x^2 + 200*x + 100 := by ring

private theorem limits (x j : ℕ) :
    ((10*x+1)^2 ≤ 100*j ∧ 100*j < (10*x+2)^2) ↔ lower x ≤ j ∧ j ≤ upper x := by
  rw [square_one, square_two]
  unfold lower upper
  omega

private theorem before (x : ℕ) : (100 * (lower x - 1)).sqrt % 10 ≠ 1 := by
  have hlo : 10*x ≤ (100*(lower x-1)).sqrt := by
    apply Nat.le_sqrt'.mpr
    rw [show (10*x)^2 = 100*x^2 by ring]
    unfold lower
    omega
  have hhi : (100*(lower x-1)).sqrt < 10*x+1 := by
    apply Nat.sqrt_lt'.mpr
    rw [square_one]
    unfold lower
    omega
  omega

private theorem after (x : ℕ) (hx : 0 < x) : (100 * (upper x + 1)).sqrt % 10 ≠ 1 := by
  have hlo : 10*x+2 ≤ (100*(upper x+1)).sqrt := by
    apply Nat.le_sqrt'.mpr
    rw [square_two]
    unfold upper
    omega
  have hhi : (100*(upper x+1)).sqrt < 10*x+10 := by
    apply Nat.sqrt_lt'.mpr
    rw [square_next]
    unfold upper
    omega
  omega

private theorem interval_length (x : ℕ) : upper x + 1 - lower x = (10*x+27)/50 := by
  unfold upper lower
  have h : x%5=0 ∨ x%5=1 ∨ x%5=2 ∨ x%5=3 ∨ x%5=4 := by omega
  rcases h with h | h | h | h | h <;> omega

theorem interval (n : ℕ) (h : (100*n).sqrt % 10 = 1) :
    ∃ lo hi : ℕ, 0 < lo ∧ lo ≤ n ∧ n ≤ hi ∧
      (∀ j : ℕ, lo ≤ j → j ≤ hi → (100*j).sqrt % 10 = 1) ∧
      (100*(lo-1)).sqrt % 10 ≠ 1 ∧ (100*(hi+1)).sqrt % 10 ≠ 1 ∧
      hi+1-lo = (10*n.sqrt+27)/50 := by
  let x := n.sqrt
  have hx0 : x^2 ≤ n := Nat.sqrt_le' n
  have hx1 : n < (x+1)^2 := Nat.lt_succ_sqrt' n
  have hx : 0 < x := by
    by_contra! hzero
    have he : x = 0 := by omega
    rw [he] at hx1
    have hn : n = 0 := by simpa using hx1
    subst n
    exact (by decide : (100*0).sqrt % 10 ≠ 1) h
  have hleft : 10*x ≤ (100*n).sqrt := by
    apply Nat.le_sqrt'.mpr
    rw [show (10*x)^2 = 100*x^2 by ring]
    omega
  have hright : (100*n).sqrt < 10*x+10 := by
    apply Nat.sqrt_lt'.mpr
    rw [show (10*x+10)^2 = 100*(x+1)^2 by ring]
    omega
  have hs : (100*n).sqrt = 10*x+1 := by omega
  have hL : (10*x+1)^2 ≤ 100*n := by rw [← hs]; exact Nat.sqrt_le' _
  have hU : 100*n < (10*x+2)^2 := by
    rw [show 10*x+2 = (10*x+1).succ by omega, ← hs]
    exact Nat.lt_succ_sqrt' _
  have hmem := (limits x n).mp ⟨hL, hU⟩
  have hpositive : 0 < lower x := by unfold lower; omega
  refine ⟨lower x, upper x, hpositive, hmem.1, hmem.2, ?_, before x, after x hx,
    interval_length x⟩
  intro j hlo hhi
  obtain ⟨hl, hu⟩ := (limits x j).mpr ⟨hlo, hhi⟩
  have hlow := Nat.le_sqrt'.mpr hl
  have hhigh := Nat.sqrt_lt'.mpr hu
  omega

end OMA.SquareRootInterval

theorem OMA.solution : type_of% @OMA.S_oeis_a034097.main := OMA.SquareRootInterval.interval
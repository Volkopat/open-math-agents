import OMAStatements.S_oeis_a195539

/-! Credit: @unserus

convPair n is ((4v+y, y), (5v+y, v)) for a state (y, v) with (y, v) -> (y+4v, y+5v) and
invariant y^2 + 4vy - 4v^2 = 1 (y odd). Explicit Bezout identities show the fractions reduce to
numerators 8v^2+4vy and 24v^2+10vy+y^2, which satisfy the step-two recurrence with factor 34
and match pell (4n+4) and r2 1 35 (n+1). -/

namespace OMAA195539Helpers
open OMA.S_oeis_a195539

def st : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | n + 1 => ((st n).1 + 4 * (st n).2, (st n).1 + 5 * (st n).2)

theorem conv (n : ℕ) : convPair n =
    ((4 * (st n).2 + (st n).1, (st n).1), (5 * (st n).2 + (st n).1, (st n).2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [convPair, ih, st]
    simp only [Prod.mk.injEq]
    refine ⟨⟨by ring, by ring⟩, by ring, by ring⟩

theorem inv (n : ℕ) : (st n).1 ^ 2 + 4 * (st n).2 * (st n).1 - 4 * (st n).2 ^ 2 = 1 ∧
    Odd (st n).1 ∧ 0 < (st n).1 ∧ 0 < (st n).2 := by
  induction n with
  | zero => refine ⟨by norm_num [st], by decide, by norm_num [st], by norm_num [st]⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [st]
    refine ⟨by linear_combination h1, ?_, by omega, by omega⟩
    obtain ⟨m, hm⟩ := h2
    exact ⟨m + 2 * (st n).2, by rw [hm]; ring⟩

def E (s : ℤ × ℤ) : ℤ := 8 * s.2 ^ 2 + 4 * s.2 * s.1
def O (s : ℤ × ℤ) : ℤ := 24 * s.2 ^ 2 + 10 * s.2 * s.1 + s.1 ^ 2

theorem coprime_of (a b : ℤ) (h : IsCoprime a b) : Nat.Coprime a.natAbs b.natAbs :=
  Int.isCoprime_iff_gcd_eq_one.mp h

theorem ratio_even (y v : ℤ) (hJ : y ^ 2 + 4 * v * y - 4 * v ^ 2 = 1) (hodd : Odd y)
    (hy : 0 < y) (hv : 0 < v) :
    ((((4 * v + y : ℤ) : ℚ) ^ 2 - ((y : ℤ) : ℚ) ^ 2) / (2 * ((4 * v + y : ℤ) : ℚ) * ((y : ℤ) : ℚ))).num
      = 8 * v ^ 2 + 4 * v * y := by
  have hx : 0 < 4 * v + y := by omega
  have hr : (((4 * v + y : ℤ) : ℚ) ^ 2 - ((y : ℤ) : ℚ) ^ 2) / (2 * ((4 * v + y : ℤ) : ℚ) * ((y : ℤ) : ℚ))
      = ((8 * v ^ 2 + 4 * v * y : ℤ) : ℚ) / (((4 * v + y) * y : ℤ) : ℚ) := by
    have hy' : (y : ℚ) ≠ 0 := by exact_mod_cast hy.ne'
    have hx' : ((4 * v + y : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
    push_cast at hx' ⊢
    field_simp
    ring
  have hcop : IsCoprime (8 * v ^ 2 + 4 * v * y) ((4 * v + y) * y) := by
    obtain ⟨m, hm⟩ := hodd
    apply IsCoprime.mul_right
    · obtain ⟨k, hk⟩ : Odd (4 * v + y) := ⟨2 * v + m, by rw [hm]; ring⟩
      refine ⟨-k, 1 + k * (12 * v - 2 * (4 * v + y)), ?_⟩
      linear_combination hk - 2 * k * hJ
    · refine ⟨m, 1 - m * (2 * y + 12 * v), ?_⟩
      linear_combination hm - 2 * m * hJ
  rw [hr, Rat.num_div_eq_of_coprime (by positivity) (coprime_of _ _ hcop)]

theorem ratio_odd (y v : ℤ) (hJ : y ^ 2 + 4 * v * y - 4 * v ^ 2 = 1)
    (hy : 0 < y) (hv : 0 < v) :
    ((((5 * v + y : ℤ) : ℚ) ^ 2 - ((v : ℤ) : ℚ) ^ 2) / (2 * ((5 * v + y : ℤ) : ℚ) * ((v : ℤ) : ℚ))).num
      = 24 * v ^ 2 + 10 * v * y + y ^ 2 := by
  have hu : 0 < 5 * v + y := by omega
  have hr : (((5 * v + y : ℤ) : ℚ) ^ 2 - ((v : ℤ) : ℚ) ^ 2) / (2 * ((5 * v + y : ℤ) : ℚ) * ((v : ℤ) : ℚ))
      = ((24 * v ^ 2 + 10 * v * y + y ^ 2 : ℤ) : ℚ) / ((2 * (5 * v + y) * v : ℤ) : ℚ) := by
    push_cast; ring
  have hcop : IsCoprime (24 * v ^ 2 + 10 * v * y + y ^ 2) (2 * (5 * v + y) * v) := by
    apply IsCoprime.mul_right
    apply IsCoprime.mul_right
    · refine ⟨1, -(3 * (5 * v + y) * v - v ^ 2), ?_⟩
      linear_combination hJ
    · refine ⟨-1, 2 * (5 * v + y) - 6 * v, ?_⟩
      linear_combination hJ
    · refine ⟨1, 2 * v - 6 * (5 * v + y), ?_⟩
      linear_combination hJ
  rw [hr, Rat.num_div_eq_of_coprime (by positivity) (coprime_of _ _ hcop)]

theorem a_even (n : ℕ) : a (2 * n) = (E (st n) : ℚ) := by
  obtain ⟨hJ, hodd, hy, hv⟩ := inv n
  simp only [a, sourceRatio, show 2 * n % 2 = 0 by omega, if_true, show 2 * n / 2 = n by omega,
    conv n, E]
  rw [ratio_even _ _ hJ hodd hy hv]

theorem a_odd (n : ℕ) : a (2 * n + 1) = (O (st n) : ℚ) := by
  obtain ⟨hJ, -, hy, hv⟩ := inv n
  simp only [a, sourceRatio, show (2 * n + 1) % 2 = 1 by omega, show (1 : ℕ) ≠ 0 by omega,
    if_false, show (2 * n + 1) / 2 = n by omega, conv n, O]
  rw [ratio_odd _ _ hJ hy hv]

theorem pell8 (m : ℕ) : pell (m + 8) = 34 * pell (m + 4) - pell m := by
  simp only [pell]
  ring

theorem E_pell : ∀ n : ℕ, (E (st n) : ℚ) = pell (4 * n + 4)
  | 0 => by norm_num [E, st, pell]
  | 1 => by norm_num [E, st, pell]
  | n + 2 => by
    have h0 := E_pell n
    have h1 := E_pell (n + 1)
    rw [show 4 * (n + 2) + 4 = (4 * n + 4) + 8 by ring, pell8,
      show 4 * n + 4 + 4 = 4 * (n + 1) + 4 by ring, ← h0, ← h1]
    simp only [E, st]
    push_cast
    ring

theorem O_r2 : ∀ n : ℕ, (O (st n) : ℚ) = r2 1 35 (n + 1)
  | 0 => by norm_num [O, st, r2]
  | 1 => by norm_num [O, st, r2]
  | n + 2 => by
    have h0 := O_r2 n
    have h1 := O_r2 (n + 1)
    rw [show n + 2 + 1 = (n + 1) + 2 by ring, r2, ← h0, ← h1]
    simp only [O, st]
    push_cast
    ring

end OMAA195539Helpers

open OMAA195539Helpers OMA.S_oeis_a195539 in
theorem OMA.solution : type_of% @OMA.S_oeis_a195539.main := by
  have hE : ∀ n : ℕ, a (2 * n) = pell (4 * n + 4) := fun n => (a_even n).trans (E_pell n)
  have hO : ∀ n : ℕ, a (2 * n + 1) = r2 1 35 (n + 1) := fun n => (a_odd n).trans (O_r2 n)
  refine ⟨?_, hE, hO⟩
  intro n
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show 2 * k + 4 = 2 * (k + 2) by ring, show 2 * k + 2 = 2 * (k + 1) by ring, hE, hE, hE,
      show 4 * (k + 2) + 4 = (4 * k + 4) + 8 by ring, pell8,
      show 4 * k + 4 + 4 = 4 * (k + 1) + 4 by ring]
  · rw [show 2 * k + 1 + 4 = 2 * (k + 2) + 1 by ring, show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring,
      hO, hO, hO, show k + 2 + 1 = (k + 1) + 2 by ring, r2]

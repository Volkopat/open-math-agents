import OMAStatements.S_oeis_a165461

namespace R165461
open OMA.S_oeis_a165461

/-- The Jacobi character modulo `12N + 7`, on naturals. -/
def f (N i : ℕ) : ℤ := jacobiSym (i : ℤ) (12 * N + 7)

def A0 (N : ℕ) : ℤ := ∑ i ∈ Finset.range (2 * N + 2), f N i
def A1 (N : ℕ) : ℤ := ∑ t ∈ Finset.range (2 * N + 1), f N (2 * N + 2 + t)
def A2 (N : ℕ) : ℤ := ∑ t ∈ Finset.range (2 * N + 1), f N (4 * N + 3 + t)
def S4 (N : ℕ) : ℤ := ∑ i ∈ Finset.range (4 * N + 3), f N i
def S6 (N : ℕ) : ℤ := ∑ i ∈ Finset.range (6 * N + 4), f N i

theorem rev_sum (g : ℕ → ℤ) (n : ℕ) :
    ∑ j ∈ Finset.range n, g (n - 1 - j) = ∑ j ∈ Finset.range n, g j := by
  apply Finset.sum_nbij' (fun j => n - 1 - j) (fun j => n - 1 - j)
  · intro a ha; simp only [Finset.mem_range] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_range] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_range] at ha; omega
  · intro a ha; simp only [Finset.mem_range] at ha; omega
  · intro a _; rfl

theorem split2 (g : ℕ → ℤ) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k + 1), g i =
      ∑ t ∈ Finset.range (k + 1), g (2 * t) + ∑ t ∈ Finset.range k, g (2 * t + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ g (2 * k + 1 + 1),
      Finset.sum_range_succ g (2 * k + 1), ih, Finset.sum_range_succ (fun t => g (2 * t)) (k + 1),
      Finset.sum_range_succ (fun t => g (2 * t + 1)) k, show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    ring

theorem split3 (g : ℕ → ℤ) (k : ℕ) :
    ∑ i ∈ Finset.range (3 * k + 1), g i =
      ∑ t ∈ Finset.range (k + 1), g (3 * t) + ∑ t ∈ Finset.range k, g (3 * t + 1) +
        ∑ t ∈ Finset.range k, g (3 * t + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 3 * (k + 1) + 1 = 3 * k + 1 + 1 + 1 + 1 by ring,
      Finset.sum_range_succ g (3 * k + 1 + 1 + 1), Finset.sum_range_succ g (3 * k + 1 + 1),
      Finset.sum_range_succ g (3 * k + 1), ih,
      Finset.sum_range_succ (fun t => g (3 * t)) (k + 1),
      Finset.sum_range_succ (fun t => g (3 * t + 1)) k,
      Finset.sum_range_succ (fun t => g (3 * t + 2)) k,
      show 3 * (k + 1) = 3 * k + 1 + 1 + 1 by ring, show 3 * k + 2 = 3 * k + 1 + 1 by ring]
    ring

theorem f_two (N t : ℕ) : f N (2 * t) = jacobiSym 2 (12 * N + 7) * f N t := by
  unfold f; push_cast; exact jacobiSym.mul_left _ _ _

theorem f_three (N t : ℕ) : f N (3 * t) = jacobiSym 3 (12 * N + 7) * f N t := by
  unfold f; push_cast; exact jacobiSym.mul_left _ _ _

theorem f_neg (N a b : ℕ) (h : a + b = 12 * N + 7) : f N a = -f N b := by
  unfold f
  have hodd : Odd (12 * N + 7) := ⟨6 * N + 3, by ring⟩
  have hm : (a : ℤ) % ((12 * N + 7 : ℕ) : ℤ) = (-(b : ℤ)) % ((12 * N + 7 : ℕ) : ℤ) := by
    have e : (a : ℤ) = -(b : ℤ) + ((12 * N + 7 : ℕ) : ℤ) := by push_cast; omega
    rw [e, Int.add_emod_right]
  rw [jacobiSym.mod_left' hm, jacobiSym.neg _ hodd,
    ZMod.χ₄_nat_three_mod_four (n := 12 * N + 7) (by omega)]
  ring

theorem f_per (N a b : ℕ) (h : a + (12 * N + 7) = b) : f N b = f N a := by
  unfold f
  have hm : (b : ℤ) % ((12 * N + 7 : ℕ) : ℤ) = (a : ℤ) % ((12 * N + 7 : ℕ) : ℤ) := by
    have e : (b : ℤ) = (a : ℤ) + ((12 * N + 7 : ℕ) : ℤ) := by push_cast; omega
    rw [e, Int.add_emod_right]
  exact jacobiSym.mod_left' hm

theorem c2 (N : ℕ) : jacobiSym 2 (12 * N + 7) = if N % 2 = 0 then 1 else -1 := by
  have hodd : Odd (12 * N + 7) := ⟨6 * N + 3, by ring⟩
  rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
  split_ifs <;> omega

theorem c3 (N : ℕ) : jacobiSym 3 (12 * N + 7) = -1 := by
  have h := jacobiSym.quadratic_reciprocity_three_mod_four (a := 3) (b := 12 * N + 7)
    (by norm_num) (by omega)
  have h2 : jacobiSym ((12 * N + 7 : ℕ) : ℤ) 3 = 1 := by
    rw [jacobiSym.mod_left' (a₁ := ((12 * N + 7 : ℕ) : ℤ)) (a₂ := 1) (b := 3)
      (by push_cast; omega)]
    exact jacobiSym.one_left 3
  rw [h2] at h
  exact_mod_cast h

theorem s4_eq (N : ℕ) : S4 N = A0 N + A1 N := by
  unfold S4 A0 A1
  rw [show 4 * N + 3 = (2 * N + 2) + (2 * N + 1) by ring, Finset.sum_range_add]

theorem s6_eq (N : ℕ) : S6 N = S4 N + A2 N := by
  unfold S6 S4 A2
  rw [show 6 * N + 4 = (4 * N + 3) + (2 * N + 1) by ring, Finset.sum_range_add]

theorem dbl (N : ℕ) :
    S4 N = jacobiSym 2 (12 * N + 7) * A0 N - jacobiSym 2 (12 * N + 7) * A2 N := by
  have h1 : S4 N = ∑ t ∈ Finset.range (2 * N + 2), f N (2 * t) +
      ∑ t ∈ Finset.range (2 * N + 1), f N (2 * t + 1) := by
    have := split2 (f N) (2 * N + 1)
    rw [show 2 * (2 * N + 1) + 1 = 4 * N + 3 by ring, show 2 * N + 1 + 1 = 2 * N + 2 by ring]
      at this
    exact this
  have h2 : ∑ t ∈ Finset.range (2 * N + 2), f N (2 * t) = jacobiSym 2 (12 * N + 7) * A0 N := by
    unfold A0
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun t _ => f_two N t)
  have h3 : ∑ t ∈ Finset.range (2 * N + 1), f N (2 * t + 1) =
      -(jacobiSym 2 (12 * N + 7) * A2 N) := by
    unfold A2
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← rev_sum (fun t => f N (2 * t + 1)) (2 * N + 1)]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    show f N (2 * (2 * N + 1 - 1 - t) + 1) = -(jacobiSym 2 (12 * N + 7) * f N (4 * N + 3 + t))
    rw [f_neg N (2 * (2 * N + 1 - 1 - t) + 1) (2 * (4 * N + 3 + t)) (by omega),
      f_two N (4 * N + 3 + t)]
  rw [h1, h2, h3]
  ring

theorem tpl (N : ℕ) :
    S6 N = jacobiSym 3 (12 * N + 7) * A0 N - jacobiSym 3 (12 * N + 7) * A1 N +
      jacobiSym 3 (12 * N + 7) * A2 N := by
  have h1 : S6 N = ∑ t ∈ Finset.range (2 * N + 2), f N (3 * t) +
      ∑ t ∈ Finset.range (2 * N + 1), f N (3 * t + 1) +
      ∑ t ∈ Finset.range (2 * N + 1), f N (3 * t + 2) := by
    have := split3 (f N) (2 * N + 1)
    rw [show 3 * (2 * N + 1) + 1 = 6 * N + 4 by ring, show 2 * N + 1 + 1 = 2 * N + 2 by ring]
      at this
    exact this
  have h2 : ∑ t ∈ Finset.range (2 * N + 2), f N (3 * t) = jacobiSym 3 (12 * N + 7) * A0 N := by
    unfold A0
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun t _ => f_three N t)
  have h3 : ∑ t ∈ Finset.range (2 * N + 1), f N (3 * t + 1) =
      -(jacobiSym 3 (12 * N + 7) * A1 N) := by
    unfold A1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← rev_sum (fun t => f N (3 * t + 1)) (2 * N + 1)]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_range] at ht
    show f N (3 * (2 * N + 1 - 1 - t) + 1) = -(jacobiSym 3 (12 * N + 7) * f N (2 * N + 2 + t))
    rw [f_neg N (3 * (2 * N + 1 - 1 - t) + 1) (3 * (2 * N + 2 + t)) (by omega),
      f_three N (2 * N + 2 + t)]
  have h4 : ∑ t ∈ Finset.range (2 * N + 1), f N (3 * t + 2) =
      jacobiSym 3 (12 * N + 7) * A2 N := by
    unfold A2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [← f_per N (3 * t + 2) (3 * (4 * N + 3 + t)) (by omega), f_three N (4 * N + 3 + t)]
  rw [h1, h2, h3, h4]
  ring

theorem core_even (N : ℕ) (hN : N % 2 = 0) : S4 N = 2 * A0 N ∧ S6 N = A0 N := by
  have d := dbl N
  have t := tpl N
  have e4 := s4_eq N
  have e6 := s6_eq N
  rw [c2 N, if_pos hN] at d
  rw [c3 N] at t
  constructor <;> linarith

theorem core_odd (N : ℕ) (hN : N % 2 = 1) : S4 N = -2 * A0 N ∧ S6 N = -3 * A0 N := by
  have d := dbl N
  have t := tpl N
  have e4 := s4_eq N
  have e6 := s6_eq N
  rw [c2 N, if_neg (show ¬(N % 2 = 0) by omega)] at d
  rw [c3 N] at t
  constructor <;> linarith

theorem e605 (n : ℕ) : a165605 n = S6 n := by
  unfold a165605 a165601 S6 f
  rw [show 2 * (3 * n + 1) + 2 = 6 * n + 4 by ring, show 4 * (3 * n + 1) + 3 = 12 * n + 7 by ring]

theorem zero_iff (n : ℕ) : S4 n = 0 ↔ S6 n = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · obtain ⟨h1, h2⟩ := core_even n h
    constructor <;> intro hz <;> linarith
  · obtain ⟨h1, h2⟩ := core_odd n h
    constructor <;> intro hz <;> linarith

theorem final (n : ℕ) : a165460 n = 0 ↔ a165605 n = 0 := by
  rw [show a165460 n = S4 n from rfl, e605]
  exact zero_iff n

end R165461

theorem OMA.solution : type_of% @OMA.S_oeis_a165461.main := R165461.final

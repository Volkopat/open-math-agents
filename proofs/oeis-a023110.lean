import OMAStatements.S_oeis_a023110
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Barker's recurrence for squares with square decimal truncations

Robert Israel identified seven interleaved Pell orbits for the square roots in
OEIS A031149 (February 2016). We prove their completeness by descent and their
ordering, then deduce the conjecture about the squares in OEIS A023110.
-/

namespace A023110

open OMA.S_oeis_a023110

private def advance (p : ℕ × ℕ) : ℕ × ℕ :=
  (19*p.1+60*p.2, 6*p.1+19*p.2)

private def point : ℕ → ℕ × ℕ
  | 0 => (1,0)
  | 1 => (2,0)
  | 2 => (3,0)
  | 3 => (4,1)
  | 4 => (7,2)
  | 5 => (13,4)
  | 6 => (16,5)
  | n+7 => advance (point n)

private def good (x y : ℕ) : Prop := 10*y^2 ≤ x^2 ∧ x^2 ≤ 10*y^2+9
private instance (x y : ℕ) : Decidable (good x y) := inferInstanceAs (Decidable (10*y^2 ≤ x^2 ∧ x^2 ≤ 10*y^2+9))

private theorem valid (n : ℕ) : good (point n).1 (point n).2 := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => decide
  | n+7 =>
    rcases valid n with ⟨lo,hi⟩
    simp only [point, advance, good]
    constructor <;> nlinarith only [lo,hi]

private theorem ordered (n : ℕ) :
    (point n).1 < (point (n+1)).1 ∧ (point n).2 ≤ (point (n+1)).2 := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => decide
  | n+7 =>
    obtain ⟨hx,hy⟩ := ordered n
    change (advance (point n)).1 < (advance (point (n+1))).1 ∧
      (advance (point n)).2 ≤ (advance (point (n+1))).2
    simp only [advance]
    constructor <;> omega

private theorem small : ∀ x : Fin 60, ∀ y : Fin 18, good x y →
    x.val = 0 ∨ ∃ i : Fin 10, point i.val = (x.val,y.val) := by decide

private theorem exhaust (x y : ℕ) (hg : good x y) :
    x=0 ∨ ∃ i, point i = (x,y) := by
  induction x using Nat.strong_induction_on generalizing y with
  | h x ih =>
    rcases hg with ⟨lo,hi⟩
    by_cases hy : y < 18
    · have hx : x < 60 := by
        by_contra! hx
        nlinarith only [Nat.mul_self_le_mul_self (show y ≤ 17 by omega),
          Nat.mul_self_le_mul_self hx, hi]
      rcases small ⟨x,hx⟩ ⟨y,hy⟩ ⟨lo,hi⟩ with h | ⟨i,he⟩
      · exact Or.inl h
      · exact Or.inr ⟨i,he⟩
    · have h₁ : 60*y ≤ 19*x := by
        apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (Nat.zero_le _)
        nlinarith only [lo,Nat.zero_le (y^2)]
      have h₂ : 6*x ≤ 19*y := by
        apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (Nat.zero_le _)
        nlinarith only [Nat.mul_self_le_mul_self (show 18 ≤ y by omega), hi]
      have h₃ : 18*x < 60*y := by
        by_contra! h
        nlinarith [Nat.mul_self_le_mul_self h, Nat.mul_self_le_mul_self (show 18 ≤ y by omega)]
      let u := 19*x-60*y
      let v := 19*y-6*x
      have hu : u+60*y = 19*x := Nat.sub_add_cancel h₁
      have hv : v+6*x = 19*y := Nat.sub_add_cancel h₂
      let u := 19*x-60*y
      let v := 19*y-6*x
      have hu : u+60*y = 19*x := by dsimp [u]; omega
      have hv : v+6*x = 19*y := by dsimp [v]; omega
      have inv : advance (u,v) = (x,y) := by
        simp only [advance, Prod.mk.injEq]
        omega
      have guv : good u v := by
        have h : good (advance (u,v)).1 (advance (u,v)).2 := by rw [inv]; exact ⟨lo,hi⟩
        obtain ⟨h₁,h₂⟩ := h
        simp only [advance] at h₁ h₂
        constructor <;> nlinarith only [h₁,h₂]
      rcases ih u (by omega) v guv with hz | ⟨i,he⟩
      · have hv₀ : v = 0 := by
          obtain ⟨h,_⟩ := guv
          rw [hz] at h
          nlinarith
        simp [advance,hz,hv₀] at inv
        omega
      · right
        exact ⟨i+7, by rw [point,he,inv]⟩

private def terms : ℕ → ℕ
  | 0 => 0
  | n+1 => (point n).1^2

private theorem terms_increasing : StrictMono terms := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => decide
  | succ n =>
    exact Nat.pow_lt_pow_left (ordered n).1 (by decide)

private theorem terms_range : Set.range terms = Set.ofPred isA023110 := by
  ext m
  constructor
  · rintro ⟨i,rfl⟩
    cases i with
    | zero => exact ⟨⟨0,rfl⟩,⟨0,rfl⟩⟩
    | succ i =>
      obtain ⟨lo,hi⟩ := valid i
      refine ⟨⟨(point i).1, by simp [terms,pow_two]⟩,⟨(point i).2, ?_⟩⟩
      change (point i).1^2/10 = (point i).2*(point i).2
      rw [← pow_two]
      omega
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    rw [← pow_two] at hx hy
    subst m
    have lo : 10*y^2 ≤ x^2 := by omega
    have hi : x^2 ≤ 10*y^2+9 := by omega
    rcases exhaust x y ⟨lo,hi⟩ with hz | ⟨i,he⟩
    · exact ⟨0, by simp [terms,hz]⟩
    · exact ⟨i+1, by simp [terms,he]⟩

private theorem indexed : a = terms := by
  have hinf : (Set.ofPred isA023110).Infinite := terms_range ▸ Set.infinite_range_of_injective terms_increasing.injective
  apply (Nat.nth_strictMono hinf).range_inj terms_increasing |>.mp
  exact (Nat.range_nth_of_infinite hinf).trans terms_range.symm

/-- Barker's order-21 recurrence holds at every index from 22 onward (zero-based). -/
theorem recurrence (n : ℕ) (hn : 22 ≤ n) :
    (a n : ℤ) = 1443*(a (n-7) : ℤ) - 1443*(a (n-14) : ℤ) + (a (n-21) : ℤ) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 22 k]
  rw [show k+22-7=k+15 by omega, show k+22-14=k+8 by omega, show k+22-21=k+1 by omega,indexed]
  change (((advance (advance (advance (point k)))).1^2 : ℕ) : ℤ) =
    1443*((((advance (advance (point k))).1^2 : ℕ) : ℤ)) -
    1443*((((advance (point k)).1^2 : ℕ) : ℤ)) + (((point k).1^2 : ℕ) : ℤ)
  simp only [advance, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

end A023110

theorem OMA.solution : type_of% @OMA.S_oeis_a023110.main := A023110.recurrence

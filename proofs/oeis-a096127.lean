import OMAStatements.S_oeis_a096127
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic

/-!
# OEIS A096127

Legendre's factorial formula turns the valuation bound into an inequality
about base-p digit sums. If n is not a prime power its digit sum s lies
between two and n for every prime base. The sum of the digits of n² is
at most s², so the required bound follows from (s−2)(n−s) ≥ 0.

An earlier formalization of the two-way characterization, with the same
digit-sum estimate, is recorded by trureturing:
https://www.trureturing.org/research/oeis-a096127-factorial-square-divisibility-prime-power/
This proof is written for the statement formalized by @garrytaulu.
-/

namespace OMA.S_oeis_a096127

private def S (p n : Nat) := (p.digits n).sum

private theorem legendre (p n : Nat) (hp : p.Prime) :
    (p-1) * n.factorial.factorization p + S p n = n := by
  have h := hp.sub_one_mul_multiplicity_factorial (n := n)
  have bridge : multiplicity p n.factorial = n.factorial.factorization p := by
    solve_by_elim only [Nat.multiplicity_eq_factorization, hp, Nat.factorial_ne_zero]
  rw [bridge] at h
  rw [h]
  exact Nat.sub_add_cancel (Nat.digit_sum_le p n)

private theorem sumAdd (p x y : Nat) (hp : p.Prime) : S p (x+y) ≤ S p x + S p y := by
  have hd := (Nat.factorization_le_iff_dvd
    (Nat.mul_ne_zero (Nat.factorial_ne_zero x) (Nat.factorial_ne_zero y))
    (Nat.factorial_ne_zero (x+y))).2 (Nat.factorial_mul_factorial_dvd_factorial_add x y) p
  rw [Nat.factorization_mul (Nat.factorial_ne_zero x) (Nat.factorial_ne_zero y),
    Finsupp.add_apply] at hd
  have h := Nat.mul_le_mul_left (p-1) hd
  rw [Nat.mul_add] at h
  have hx := legendre p x hp
  have hy := legendre p y hp
  have hxy := legendre p (x+y) hp
  omega

private theorem repeated (p y k : Nat) (hp : p.Prime) : S p (k*y) ≤ k * S p y := by
  induction k with
  | zero => simp [S]
  | succ k ih =>
    rw [Nat.succ_mul,Nat.succ_mul]
    exact (sumAdd p _ _ hp).trans (Nat.add_le_add_right ih _)

private theorem shift (p x : Nat) (hp : p.Prime) : S p (p*x) = S p x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · simp [S,Nat.digits_base_mul hp.one_lt hx]

private theorem sumMul (p x y : Nat) (hp : p.Prime) : S p (x*y) ≤ S p x * S p y := by
  have aux (L : List Nat) : S p (Nat.ofDigits p L*y) ≤ L.sum * S p y := by
    induction L with
    | nil => simp [S]
    | cons d L ih =>
      rw [Nat.ofDigits_cons,List.sum_cons,Nat.add_mul,Nat.add_mul,Nat.mul_assoc]
      exact (sumAdd p _ _ hp).trans
        (by rw [shift p _ hp]; exact Nat.add_le_add (repeated p y d hp) ih)
  simpa only [Nat.ofDigits_digits,S] using aux (p.digits x)

private theorem zeroDigits (p : Nat) (L : List Nat) (h : L.sum = 0) :
    Nat.ofDigits p L = 0 := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    simp only [List.sum_cons] at h
    rw [Nat.ofDigits_cons,show d = 0 by omega,ih (by omega)]
    simp

private theorem oneDigit (p : Nat) (L : List Nat) (h : L.sum ≤ 1) :
    Nat.ofDigits p L = 0 ∨ ∃ k : Nat, p^k = Nat.ofDigits p L := by
  induction L with
  | nil => exact Or.inl rfl
  | cons d L ih =>
    simp only [List.sum_cons] at h
    rw [Nat.ofDigits_cons]
    by_cases hd : d = 0
    · rw [hd,zero_add]
      rcases ih (by omega) with h0 | ⟨k,hk⟩
      · exact Or.inl (by rw [h0,mul_zero])
      · exact Or.inr ⟨k+1,by rw [pow_succ',hk]⟩
    · exact Or.inr ⟨0,by rw [zeroDigits p L (by omega),mul_zero,add_zero,pow_zero]; omega⟩

private theorem twoDigits (p n : Nat) (hp : p.Prime) (hn : 2 ≤ n) (h : ¬IsPrimePow n) :
    2 ≤ S p n := by
  by_contra! bad
  have low : (p.digits n).sum ≤ 1 := by change S p n ≤ 1; omega
  have e := oneDigit p (p.digits n) low
  rw [Nat.ofDigits_digits] at e
  rcases e with h0 | ⟨k,hk⟩
  · omega
  · apply h
    apply (isPrimePow_nat_iff n).2
    refine ⟨p,k,hp,?_,hk⟩
    by_contra! h0
    have : k = 0 := by omega
    rw [this,pow_zero] at hk
    omega

private theorem digitBound (n s : Nat) (hs : 2 ≤ s) (hn : s ≤ n) :
    s^2 + 2*n ≤ (n+2)*s := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hn
  nlinarith only [Nat.mul_le_mul_right d hs]

private theorem extraPower (n : Nat) (hn : 2 ≤ n) (h : ¬ IsPrimePow n) :
    n.factorial^(n+2) ∣ (n^2).factorial := by
  apply (Nat.factorization_le_iff_dvd (pow_ne_zero _ (Nat.factorial_ne_zero n))
    (Nat.factorial_ne_zero (n^2))).1
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul]
    by_contra! bad
    have hpos : 0 < p-1 := by have := hp.two_le; omega
    have impossible := Nat.mul_lt_mul_of_pos_left bad hpos
    have hn2 := legendre p (n^2) hp
    have scale := congrArg (fun m : Nat => (n+2)*m) (legendre p n hp)
    have sq : S p (n^2) ≤ (S p n)^2 := by simpa only [sq] using sumMul p n n hp
    have bound := digitBound n (S p n) (twoDigits p n hp hn h) (Nat.digit_sum_le p n)
    nlinarith only [impossible,hn2,scale,sq,bound]
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

end OMA.S_oeis_a096127

open OMA.S_oeis_a096127

theorem OMA.solution : type_of% @OMA.S_oeis_a096127.main := by
  intro n hn _ hmax
  by_contra h
  exact hmax (extraPower n hn h)

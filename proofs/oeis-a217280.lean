import OMAStatements.S_oeis_a217280
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic

open OMA.S_oeis_a217280 Finset

namespace BinomialCubes

def weight (n k : ℕ) : ZMod 5 := (n.choose k : ZMod 5)^3 * 2^k * 3^(n-k)

lemma padded (n b : ℕ) (h : n+1 ≤ b) :
    ∑ k ∈ range b, weight n k = (a n:ZMod 5) := by
  simp only [a, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  change ∑ k ∈ range b, weight n k = ∑ k ∈ range (n+1), weight n k
  symm
  apply sum_subset (range_mono h)
  intro k _ hk
  have hkn : n < k := by simpa using hk
  simp [weight, Nat.choose_eq_zero_of_lt hkn]

lemma blocks (q : ℕ) (f : ℕ → ZMod 5) :
    ∑ k ∈ range (5*q), f k = ∑ i ∈ range q, ∑ j ∈ range 5, f (5*i+j) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ (fun i => ∑ j ∈ range 5, f (5*i+j)) q]

lemma weight_split (q d i j : ℕ) (hd : d<5) (hj : j<5) :
    weight (5*q+d) (5*i+j) = weight q i * weight d j := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h := (ZMod.natCast_eq_natCast_iff _ _ 5).mpr
    (Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 5) (n := 5*q+d) (k := 5*i+j))
  rw [show (5*q+d)%5=d by omega, show (5*i+j)%5=j by omega,
    show (5*q+d)/5=q by omega, show (5*i+j)/5=i by omega] at h
  push_cast at h
  unfold weight
  rw [h]
  by_cases hjd : j≤d
  · by_cases hiq : i≤q
    · rw [show 5*q+d-(5*i+j)=5*(q-i)+(d-j) by omega]
      have h₂ : (2:ZMod 5)^5=2 := by decide
      have h₃ : (3:ZMod 5)^5=3 := by decide
      simp only [pow_add, pow_mul, h₂, h₃]
      ring
    · simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge hiq)]
  · simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge hjd)]

lemma split_sum (q d : ℕ) (hd : d<5) : (a (5*q+d):ZMod 5) = (a q:ZMod 5)*a d := by
  rw [← padded (5*q+d) (5*(q+1)) (by omega), blocks]
  calc
    _ = ∑ i ∈ range (q+1), ∑ j ∈ range 5, weight q i * weight d j := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      exact fun j hj => weight_split q d i j hd (mem_range.mp hj)
    _ = _ := by
      simp_rw [← mul_sum]
      rw [← sum_mul, padded q (q+1) le_rfl, padded d 5 (by omega)]

lemma digit_value (d : ℕ) (hd : d<5) :
    (a d:ZMod 5) = if d == 0 || d == 2 then 1 else 0 := by
  interval_cases d <;> decide

lemma classify (n : ℕ) : (a n:ZMod 5) = if allowed n then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      decide
    · have hd := Nat.mod_lt n (by decide : 0<5)
      have hs := split_sum (n/5) (n%5) hd
      rw [show 5*(n/5)+n%5=n by omega] at hs
      have ha : allowed n = ((n%5 == 0 || n%5 == 2) && allowed (n/5)) := by
        rw [allowed, Nat.digits_eq_cons_digits_div (by decide : 1<5) hn, List.all_cons]
        rfl
      rw [hs, ih (n/5) (by omega), digit_value _ hd, ha]
      cases allowed (n/5) <;> cases (n%5 == 0 || n%5 == 2) <;> decide

end BinomialCubes

theorem OMA.solution : type_of% @OMA.S_oeis_a217280.main := by
  intro n
  have h := congrArg ZMod.val (BinomialCubes.classify n)
  have one : (1:ZMod 5).val = 1 := by decide
  cases hg : allowed n <;> simpa [hg, ZMod.val_natCast, one] using h

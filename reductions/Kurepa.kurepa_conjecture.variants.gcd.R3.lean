import FormalConjectures.Paper.Kurepa
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.NumberTheory.Wilson

-- Credit: @Pixelstorm44
/-! A set-partition criterion for Kurepa's conjecture. The Stirling row at p-1,
apart from its zero entry, is the factorial sequence in reverse modulo p.
Summing gives the known Bell number criterion, as discussed in
https://doi.org/10.3390/axioms12080785 . -/
namespace OMA.R_Kurepa_kurepa_conjecture_variants_gcd_R3

open Kurepa Finset

variable {p : ℕ}

private def diff (f : ℕ → ZMod p) : ℕ → ℕ → ZMod p
  | 0, a => f a
  | k+1, a => diff f k (a+1) - diff f k a

private lemma diff_mul_index (f : ℕ → ZMod p) (k a : ℕ) :
    diff (fun x => (x : ZMod p) * f x) (k+1) a =
      ((a : ZMod p) + k + 1) * diff f (k+1) a + (k+1 : ZMod p) * diff f k a := by
  induction k generalizing a with
  | zero => simp [diff]; ring
  | succ k ih =>
    rw [diff, ih (a+1), ih a]
    simp only [diff, Nat.cast_succ]
    ring

private lemma diff_one (k a : ℕ) :
    diff (fun _ => (1 : ZMod p)) (k+1) a = 0 := by
  induction k generalizing a with
  | zero => simp [diff]
  | succ k ih => rw [diff, ih, ih, sub_self]

/-- The factorial-weighted Stirling numbers are the differences of monomials at zero. -/
private lemma diff_pow (n k : ℕ) :
    diff (fun x => (x : ZMod p)^n) k 0 =
      (k.factorial : ZMod p) * Nat.stirlingSecond n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [diff]
    | succ k => simpa using (diff_one (p := p) k 0)
  | succ n ih =>
    cases k with
    | zero => simp [diff]
    | succ k =>
      simp only [pow_succ']
      rw [diff_mul_index, ih, ih, Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
      push_cast
      ring

private lemma diff_of_ones (f : ℕ → ZMod p) (k a : ℕ)
    (h : ∀ x, a ≤ x → x ≤ a+k+1 → f x = 1) : diff f (k+1) a = 0 := by
  induction k generalizing a with
  | zero => rw [diff, diff, diff, h _ (by omega) (by omega), h _ (by omega) (by omega), sub_self]
  | succ k ih =>
    rw [diff, ih (a+1) (fun x h₁ h₂ => h x (by omega) (by omega)),
      ih a (fun x h₁ h₂ => h x (by omega) (by omega)), sub_self]

private lemma diff_fermat [hp : Fact p.Prime] (k : ℕ) (hk : k+1 < p) :
    diff (fun x => (x : ZMod p)^(p-1)) (k+1) 0 = (-1 : ZMod p)^k := by
  have hpos := hp.out.one_lt
  have hpow (x : ℕ) (hx : 0 < x) (hlt : x < p) : (x : ZMod p)^(p-1) = 1 :=
    ZMod.pow_card_sub_one_eq_one <| fun hz =>
      (Nat.not_dvd_of_pos_of_lt hx hlt) ((ZMod.natCast_eq_zero_iff _ _).mp hz)
  induction k with
  | zero => simp [diff, zero_pow (show p-1 ≠ 0 by omega)]
  | succ k ih =>
    rw [diff, diff_of_ones _ k 1 (fun x h₁ h₂ => hpow x (by omega) (by omega)),
      ih (by omega), pow_succ]
    ring

-- Reflect a factorial across the end of the row, then apply Wilson's theorem.
private lemma reflect_factorial (p k a : ℕ) (h : a+k+1 = p) :
    ((p-1).factorial : ZMod p) = (-1 : ZMod p)^k * a.factorial * k.factorial := by
  induction k generalizing a with
  | zero =>
    have : p-1 = a := by omega
    simp [this]
  | succ k ih =>
    have ht := ih (a+1) (by omega)
    have hn : a+1+(k+1) = p := by omega
    have hr : (a : ZMod p)+1 = -((k : ZMod p)+1) := by
      apply eq_neg_of_add_eq_zero_left
      exact_mod_cast (show ((a+1+(k+1) : ℕ) : ZMod p) = 0 by rw [hn]; simp)
    rw [Nat.factorial_succ] at ht ⊢
    push_cast at ht ⊢
    rw [hr] at ht
    rw [ht, pow_succ]
    ring

theorem stirling_reflection [hp : Fact p.Prime] (k : ℕ) (hk : k+1 < p) :
    (Nat.stirlingSecond (p-1) (k+1) : ZMod p) = (p-1-(k+1)).factorial := by
  have hd := diff_fermat k hk
  rw [diff_pow] at hd
  have hr := reflect_factorial p (k+1) (p-1-(k+1)) (by omega)
  rw [ZMod.wilsons_lemma, pow_succ] at hr
  have hs : ((-1 : ZMod p)^k)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]; simp
  have hu : ((k+1).factorial : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, hp.out.dvd_factorial]; omega
  apply mul_left_cancel₀ hu
  linear_combination hd - (-1 : ZMod p)^k * hr + (((p-1-(k+1)).factorial : ZMod p) * (k+1).factorial) * hs

/-- Select the other elements of the block containing the last element. -/
private lemma stirling_choose (n k : ℕ) :
    (n+1).stirlingSecond (k+1) =
      ∑ i ∈ range (n+1), n.choose i * (n-i).stirlingSecond k := by
  induction n generalizing k with
  | zero => cases k <;> simp [Nat.stirlingSecond]
  | succ n ih =>
    cases k with
    | zero =>
      rw [Nat.stirlingSecond_one_right, sum_eq_single (n+1)]
      · simp
      · intro i hi hne
        have hpos : 0 < n+1-i := by have := mem_range.mp hi; omega
        obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        simp [ha]
      · simp
    | succ k =>
      have hbin := sum_choose_succ_mul (fun _ j => j.stirlingSecond (k+1)) n
      simp only [Nat.cast_id] at hbin
      rw [hbin]
      have hstep : ∀ i ∈ range (n+1), n+1-i = (n-i)+1 := by
        intro i hi
        have := mem_range.mp hi
        omega
      simp_rw [sum_congr rfl (fun i hi => congrArg
        (fun z => n.choose i * Nat.stirlingSecond z (k+1)) (hstep i hi))]
      simp only [Nat.stirlingSecond_succ_succ, Nat.mul_add, sum_add_distrib]
      rw [← ih k, ← ih (k+1)]
      simp_rw [← Nat.mul_assoc, Nat.mul_comm (n.choose _) (k+1), Nat.mul_assoc,
        ← mul_sum, ← ih (k+1)]
      simp only [Nat.stirlingSecond_succ_succ]
      ring

private lemma sum_stirling_eq_bell (n m : ℕ) (hm : n ≤ m) :
    ∑ k ∈ range (m+1), n.stirlingSecond k = n.bell := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    cases n with
    | zero => rw [sum_range_succ']; simp
    | succ n =>
      obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
      rw [sum_range_succ']
      simp only [Nat.stirlingSecond_succ_zero, add_zero, stirling_choose]
      rw [sum_comm, Nat.bell_succ, ← Nat.range_succ_eq_Iic]
      apply sum_congr rfl
      intro i hi
      rw [← mul_sum, ih (n-i) (by omega) b (by omega)]

/-- The total row is 1 plus the left factorial modulo p. -/
theorem bell_eq [hp : Fact p.Prime] :
    ((p-1).bell : ZMod p) = 1 + left_factorial p := by
  have hpos := hp.out.pos
  have hsum : ((p-1).bell : ZMod p) = left_factorial (p-1) := by
    have hn : p-1 ≠ 0 := by have := hp.out.one_lt; omega
    have hzero : (p-1).stirlingSecond 0 = 0 := by
      obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp [ha]
    rw [← sum_stirling_eq_bell (p-1) (p-1) le_rfl, sum_range_succ', hzero, add_zero]
    simp only [left_factorial, Nat.cast_sum]
    rw [← sum_range_reflect (fun i => (i.factorial : ZMod p)) (p-1)]
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    rw [stirling_reflection (p := p) i (by omega), show p-1-(i+1) = p-1-1-i by omega]
  have hsucc : left_factorial p = left_factorial (p-1) + (p-1).factorial := by
    unfold left_factorial
    simpa only [Nat.sub_add_cancel hpos] using sum_range_succ Nat.factorial (p-1)
  rw [hsum, hsucc, Nat.cast_add, ZMod.wilsons_lemma]
  ring

theorem bell_collision_iff [Fact p.Prime] :
    ((p-1).bell : ZMod p) = 1 ↔ p ∣ left_factorial p := by
  rw [bell_eq, ← ZMod.natCast_eq_zero_iff]
  exact add_eq_left

/-- Exclude residue one for the partition count at indices divisible by four. -/
def H1 : Prop := ∀ r : ℕ, (4*r+1).Prime →
  ((4*r).bell : ZMod (4*r+1)) ≠ 1

/-- Exclude residue one for the partition count at indices congruent to two modulo four. -/
def H2 : Prop := ∀ r : ℕ, (4*r+3).Prime →
  ((4*r+2).bell : ZMod (4*r+3)) ≠ 1

theorem main : H1 → H2 → type_of% @Kurepa.kurepa_conjecture.variants.gcd := by
  intro h₁ h₂
  apply kurepa_conjecture.gcd_reduction.mp
  apply kurepa_conjecture.prime_reduction.mpr
  intro p hp hprime hz
  let : Fact p.Prime := ⟨hprime⟩
  have hzero := (ZMod.natCast_eq_zero_iff (left_factorial p) p).mpr (Nat.dvd_of_mod_eq_zero hz)
  have hcount := bell_eq (p := p)
  rw [hzero, add_zero] at hcount
  have hodd := hprime.eq_two_or_odd.resolve_left (by omega)
  obtain ⟨r, hr | hr⟩ : ∃ r : ℕ, p = 4*r+1 ∨ p = 4*r+3 := ⟨p/4, by omega⟩
  · subst p
    exact h₁ r hprime (by simpa using hcount)
  · subst p
    exact h₂ r hprime (by simpa using hcount)

end OMA.R_Kurepa_kurepa_conjecture_variants_gcd_R3

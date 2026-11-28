import FormalConjectures.Paper.Kurepa
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.NumberTheory.Wilson

/-! A midpoint derangement criterion for Kurepa’s gcd conjecture. -/

-- Credit: @Pixelstorm44
namespace OMA.R_Kurepa_kurepa_conjecture_variants_gcd_R2

open Kurepa

lemma left_succ (a : ℕ) :
    left_factorial (a + 1) = left_factorial a + a.factorial := by
  simp [left_factorial, Finset.sum_range_succ]

lemma reflected_index {p a k : ℕ} (h : a + (k + 1) + 1 = p) :
    (a : ZMod p) + 1 = -((k : ZMod p) + 1) := by
  apply eq_neg_of_add_eq_zero_left
  have hn : a + 1 + (k + 1) = p := by omega
  exact_mod_cast (show ((a + 1 + (k + 1) : ℕ) : ZMod p) = 0 by rw [hn]; simp)

-- Reflect the suffix starting at a, using D_(k+1) = (k+1) D_k - (-1)^k.
lemma reflect_suffix (p k a : ℕ) (h : a + k + 1 = p) :
    (left_factorial p : ZMod p) - left_factorial a =
      (-1 : ZMod p)^k * a.factorial * numDerangements k := by
  induction k generalizing a with
  | zero =>
    subst p
    simp [left_succ]
  | succ k ih =>
    have ht := ih (a+1) (by omega)
    rw [left_succ, Nat.factorial_succ] at ht
    push_cast at ht
    have hd : (numDerangements (k+1) : ZMod p) =
        ((k : ZMod p) + 1) * numDerangements k - (-1 : ZMod p)^k := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ZMod p)) (numDerangements_succ k)
    rw [reflected_index h] at ht
    rw [hd, pow_succ]
    have hs : ((-1 : ZMod p)^k)^2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]; simp
    linear_combination ht - (a.factorial : ZMod p) * hs

lemma reflect_factorial (p k a : ℕ) (h : a + k + 1 = p) :
    ((p-1).factorial : ZMod p) = (-1 : ZMod p)^k * a.factorial * k.factorial := by
  induction k generalizing a with
  | zero =>
    have : p - 1 = a := by omega
    simp [this]
  | succ k ih =>
    have ht := ih (a+1) (by omega)
    rw [Nat.factorial_succ] at ht ⊢
    push_cast at ht ⊢
    rw [reflected_index h] at ht
    rw [ht, pow_succ]
    ring

/-- The upper half of the left factorial is determined by the midpoint derangement number. -/
lemma midpoint (p m : ℕ) [Fact p.Prime] (h : m + m + 1 = p) :
    (m.factorial : ZMod p) * left_factorial p =
      (m.factorial : ZMod p) * left_factorial m - numDerangements m := by
  have ht := reflect_suffix p m m h
  have hf := reflect_factorial p m m h
  rw [ZMod.wilsons_lemma] at hf
  linear_combination (m.factorial : ZMod p) * ht - (numDerangements m : ZMod p) * hf

/-- A midpoint collision is exactly a prime divisor of the full left factorial. -/
lemma midpoint_collision_iff (p m : ℕ) [hp : Fact p.Prime] (h : m + m + 1 = p) :
    (m.factorial : ZMod p) * left_factorial m = numDerangements m ↔
      p ∣ left_factorial p := by
  rw [← CharP.cast_eq_zero_iff (ZMod p)]
  have hunit : (m.factorial : ZMod p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff, hp.out.dvd_factorial]
    omega
  rw [← sub_eq_zero, ← midpoint p m h, mul_eq_zero]
  simp [hunit]

/-- Exclusion of midpoint collisions for primes of the form 4r+1. -/
def H1 : Prop := ∀ r : ℕ, (4*r+1).Prime →
  ((2*r).factorial : ZMod (4*r+1)) * left_factorial (2*r) ≠ numDerangements (2*r)

/-- Exclusion of midpoint collisions for primes of the form 4r+3. -/
def H2 : Prop := ∀ r : ℕ, (4*r+3).Prime →
  ((2*r+1).factorial : ZMod (4*r+3)) * left_factorial (2*r+1) ≠ numDerangements (2*r+1)

theorem main : H1 → H2 → type_of% @Kurepa.kurepa_conjecture.variants.gcd := by
  intro h₁ h₂
  apply kurepa_conjecture.gcd_reduction.mp
  apply kurepa_conjecture.prime_reduction.mpr
  intro p hp hprime hz
  let : Fact p.Prime := ⟨hprime⟩
  have hzero := (CharP.cast_eq_zero_iff (ZMod p) p (left_factorial p)).mpr
    (Nat.dvd_of_mod_eq_zero hz)
  obtain ⟨r, hr | hr⟩ : ∃ r : ℕ, p = 4*r+1 ∨ p = 4*r+3 := by
    have hodd := hprime.eq_two_or_odd.resolve_left (by omega)
    use p / 4
    omega
  · subst p
    have he := midpoint (4*r+1) (2*r) (by omega)
    rw [hzero, mul_zero] at he
    exact h₁ r hprime (sub_eq_zero.mp he.symm)
  · subst p
    have he := midpoint (4*r+3) (2*r+1) (by omega)
    rw [hzero, mul_zero] at he
    exact h₂ r hprime (sub_eq_zero.mp he.symm)

end OMA.R_Kurepa_kurepa_conjecture_variants_gcd_R2

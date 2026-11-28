import OMAStatements.S_oeis_a060318
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

-- Credit: @blakestone-x. The desk note by @notswizz also describes the central-binomial carry test.
namespace CatalanTernary

/-- Lucas's theorem detects the first carry in the base-three sum m + m. -/
theorem three_dvd_central (m : ℕ) :
    3 ∣ m.centralBinom ↔ 2 ∈ Nat.digits 3 m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hz : m = 0
    · subst m; decide
    rw [Nat.digits_eq_cons_digits_div (by decide) hz, List.mem_cons]
    have ih' := ih (m/3) (Nat.div_lt_self (by omega) (by decide : 1 < 3))
    have luc := (Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := 3) (n := 2*m) (k := m)).dvd_iff (dvd_refl 3)
    change (3 ∣ m.centralBinom) ↔ _ at luc
    rw [luc, Nat.prime_three.dvd_mul, ← ih']
    have r : m%3 = 0 ∨ m%3 = 1 ∨ m%3 = 2 := by omega
    rcases r with hr | hr | hr
    · have lo : 2*m%3 = 0 := by omega
      have hi : 2*m/3 = 2*(m/3) := by omega
      rw [lo, hi, hr]
      simp [Nat.centralBinom]
    · have lo : 2*m%3 = 2 := by omega
      have hi : 2*m/3 = 2*(m/3) := by omega
      rw [lo, hi, hr]
      norm_num [Nat.centralBinom]
    · have lo : 2*m%3 = 1 := by omega
      rw [lo, hr]
      simp

theorem three_dvd_catalan (n : ℕ) :
    3 ∣ catalan (2^n-1) ↔ 2 ∈ Nat.digits 3 (2^n-1) := by
  have hpow : ¬3 ∣ 2^n := fun h => (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  rw [← three_dvd_central, ← succ_mul_catalan_eq_centralBinom,
    Nat.sub_add_cancel (Nat.one_le_two_pow), Nat.prime_three.dvd_mul]
  tauto

private theorem odd_choose_ones (n k : ℕ) (hk : k < 2^n) :
    ¬2 ∣ (2^n-1).choose k := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by simpa using hk
    subst k
    decide
  | succ n ih =>
    have hp : 0 < 2^n := by positivity
    rw [pow_succ] at hk ⊢
    have he := (Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := 2) (n := 2^n*2-1) (k := k)).dvd_iff (dvd_refl 2)
    rw [he, Nat.prime_two.dvd_mul, show (2^n*2-1)%2 = 1 by omega,
      show (2^n*2-1)/2 = 2^n-1 by omega]
    have ih' := ih (k/2) (by omega)
    rcases (show k%2 = 0 ∨ k%2 = 1 by omega) with h | h <;> rw [h] <;> simpa using ih'

theorem two_not_dvd_catalan (n : ℕ) : ¬2 ∣ catalan (2^n-1) := by
  let m := 2^n-1
  have hp : 0 < 2^n := by positivity
  have hc := Nat.choose_mul_succ_eq (2*m) m
  rw [show 2*m+1-m = m+1 by omega] at hc
  change m.centralBinom * (2*m+1) = _ at hc
  rw [← succ_mul_catalan_eq_centralBinom] at hc
  have hident : catalan m * (2*m+1) = (2*m+1).choose m := by
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) (by simpa [mul_comm, mul_assoc, mul_left_comm] using hc)
  have hn := odd_choose_ones (n+1) m (by dsimp [m]; rw [pow_succ]; omega)
  have hi : 2^(n+1)-1 = 2*m+1 := by dsimp [m]; rw [pow_succ]; omega
  rw [hi, ← hident] at hn
  exact fun h => hn (dvd_mul_of_dvd_left h _)

theorem minFac_three_iff (n : ℕ) :
    (catalan (2^n-1)).minFac = 3 ↔ 2 ∈ Nat.digits 3 (2^n-1) := by
  rw [← three_dvd_catalan]
  set c := catalan (2^n-1)
  constructor
  · intro h; simpa [h] using Nat.minFac_dvd c
  · intro h
    have hu := Nat.minFac_le_of_dvd (by decide : 2 ≤ 3) h
    have hc : c ≠ 1 := by intro e; rw [e] at h; norm_num at h
    have hl := (Nat.minFac_prime hc).two_le
    have hnot : c.minFac ≠ 2 := fun e => two_not_dvd_catalan n ((Nat.minFac_eq_two_iff c).mp e)
    omega

end CatalanTernary

namespace CatalanTernary

set_option maxRecDepth 12000 in
theorem named_exceptions :
    (catalan 3).minFac = 5 ∧ (catalan 31).minFac = 7 ∧ (catalan 255).minFac = 7 := by
  constructor
  · rw [catalan_three]; norm_num
  constructor
  · rw [catalan_eq_centralBinom_div, Nat.centralBinom,
      Nat.choose_eq_factorial_div_factorial (by decide)]
    change (14544636039226909 : ℕ).minFac = 7
    norm_num
  · rw [catalan_eq_centralBinom_div, Nat.centralBinom,
      Nat.choose_eq_factorial_div_factorial (by decide)]
    change (462380922852216169265170616488440694205685631744111431093276770208968757667872897108268394945258551829606097190248507788968859791255880300732159072477 : ℕ).minFac = 7
    norm_num

theorem small (n : ℕ) (hn : 2 ≤ n) (ht : n ≤ 8) :
    (catalan (2^n-1)).minFac = if n=2 then 5 else if n=5 ∨ n=8 then 7 else 3 := by
  obtain ⟨h2,h5,h8⟩ := named_exceptions
  interval_cases n <;> first | exact h2 | exact h5 | exact h8 | exact (minFac_three_iff _).mpr (by decide)

end CatalanTernary

namespace CatalanTernary
open scoped BigOperators

/-- Record the positions of the ones in a ternary expansion without twos. -/
theorem support_of_no_two (m : ℕ) (h : 2 ∉ Nat.digits 3 m) :
    ∃ s : Finset ℕ, m = ∑ i ∈ s, 3^i := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hz : m = 0
    · exact ⟨∅, by simpa using hz⟩
    rw [Nat.digits_eq_cons_digits_div (by decide) hz, List.mem_cons] at h
    obtain ⟨s,hs⟩ := ih (m/3) (Nat.div_lt_self (by omega) (by decide)) (fun e => h (Or.inr e))
    let t := s.image Nat.succ
    have he : ∑ i ∈ t, 3^i = 3 * (m/3) := by
      dsimp [t]
      rw [Finset.sum_image (fun _ _ _ _ e => Nat.succ.inj e), hs, Finset.mul_sum]
      simp [pow_succ']
    have nz : 0 ∉ t := by simp [t]
    by_cases hr : m%3=0
    · exact ⟨t, by omega⟩
    · refine ⟨insert 0 t, ?_⟩
      rw [Finset.sum_insert nz, pow_zero, he]
      have : m%3 ≠ 2 := fun e => h (Or.inl e.symm)
      omega

theorem support_parity (s : Finset ℕ) :
    (∑ i ∈ s, 3^i) % 2 = s.card % 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Nat.add_mod, ih]
    have ho : 3^a % 2 = 1 := by
      rw [Nat.pow_mod]; simp
    rw [ho]
    omega

theorem few_or_many (n : ℕ) (hn : 8 < n) (no : 2 ∉ Nat.digits 3 (2^n-1)) :
    ∃ s : Finset ℕ, 2^n = 1 + ∑ i ∈ s, 3^i ∧
      (s.card = 3 ∨ (5 ≤ s.card ∧ s.card % 2 = 1)) := by
  obtain ⟨s,hs⟩ := support_of_no_two _ no
  have hp : 0 < 2^n := pow_pos (by decide) _
  have eqn : 2^n = 1 + ∑ i ∈ s, 3^i := by omega
  have h8 : 8 ∣ 2^n := pow_dvd_pow 2 (show 3 ≤ n by omega)
  have hpar := support_parity s
  have hodd : s.card % 2 = 1 := by omega
  refine ⟨s,eqn,?_⟩
  suffices one : s.card ≠ 1 by omega
  intro h
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
  simp only [Finset.sum_singleton] at eqn
  have h3 (j : ℕ) : 3^j % 8 = 1 ∨ 3^j % 8 = 3 := by
    induction j with
    | zero => decide
    | succ j ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with e | e <;> simp [e]
  rcases h3 a with e | e <;> omega

end CatalanTernary

namespace OMA.R_oeis_a060318_R2

/-- A fixed four-term sum: one plus three distinct powers of three. -/
def H1 : Prop := ∀ (s : Finset ℕ) (n : ℕ), s.card = 3 → 8 < n →
  2^n ≠ 1 + ∑ i ∈ s, 3^i

/-- The remaining sums use an odd number of at least five distinct powers. -/
def H2 : Prop := ∀ (s : Finset ℕ) (n : ℕ), 5 ≤ s.card → s.card % 2 = 1 → 8 < n →
  2^n ≠ 1 + ∑ i ∈ s, 3^i

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a060318.main := by
  intro three many n hn
  by_cases ht : n ≤ 8
  · exact CatalanTernary.small n hn ht
  rw [if_neg (by omega : n ≠ 2), if_neg (by omega : ¬(n=5 ∨ n=8)), CatalanTernary.minFac_three_iff]
  by_contra no
  obtain ⟨s, eqn, h | ⟨h, parity⟩⟩ := CatalanTernary.few_or_many n (by omega) no
  · exact three s n h (by omega) eqn
  · exact many s n h parity (by omega) eqn

end OMA.R_oeis_a060318_R2

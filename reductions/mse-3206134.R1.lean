import OMAStatements.S_mse_3206134
import Mathlib

/-!
# A divisibility obstruction for palindromic products of arithmetic progressions

A positive decimal palindrome cannot end in zero. Among the first five terms,
a step nonzero modulo five forces a multiple of five. Among the first two terms,
a step odd modulo two forces an even term. The same obstructions apply when
the first term is divisible by the respective prime. The two remaining cases
are all-odd progressions and progressions that hit an even term but avoid five.
In either case, an even number of decimal digits forces a multiple of eleven
among the first eleven terms.

Source: https://math.stackexchange.com/questions/3206134
-/

namespace OMA.R_mse_3206134_R1

open Finset OMA.S_mse_3206134

private theorem not_palindrome_of_ten_dvd {m : ℕ} (hm : 0 < m) (hd : 10 ∣ m) :
    ¬ IsPalindrome m := by
  intro hpal
  have hdigits : Nat.digits 10 m = 0 :: Nat.digits 10 (m / 10) := by
    rw [Nat.digits_eq_cons_digits_div (by decide) hm.ne', Nat.mod_eq_zero_of_dvd hd]
  have heq : (Nat.digits 10 m).getLast? = some 0 := by
    rw [← hpal, hdigits]
    simp
  have hne : Nat.digits 10 m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hm.ne'
  rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at heq
  exact Nat.getLast_digit_ne_zero 10 hm.ne' heq

private theorem five_hit (a d : ℕ) (hd : d % 5 ≠ 0) :
    ∃ i : Fin 5, 5 ∣ a + i.val * d := by
  have small : ∀ u v : Fin 5, v ≠ 0 →
      ∃ i : Fin 5, (u.val + i.val * v.val) % 5 = 0 := by decide
  let u : Fin 5 := ⟨a % 5, Nat.mod_lt _ (by decide)⟩
  let v : Fin 5 := ⟨d % 5, Nat.mod_lt _ (by decide)⟩
  have hv : v ≠ 0 := fun h => hd (congrArg Fin.val h)
  obtain ⟨i, hi⟩ := small u v hv
  have hr : a % 5 + i.val * (d % 5) ≡ a + i.val * d [MOD 5] :=
    (Nat.mod_modEq a 5).add ((Nat.mod_modEq d 5).mul_left i.val)
  change (a % 5 + i.val * (d % 5)) % 5 = 0 at hi
  unfold Nat.ModEq at hr
  exact ⟨i, Nat.dvd_of_mod_eq_zero (hr.symm.trans hi)⟩

/-- A palindromic product of at least five terms has all terms odd,
or its first term is nonzero modulo five and its step is zero modulo five. -/
theorem palindrome_residues {n a d : ℕ} (hn : 5 ≤ n) (ha : 0 < a)
    (hpal : IsPalindrome (∏ i ∈ range n, (a + i * d))) :
    (a % 2 = 1 ∧ d % 2 = 0) ∨ (a % 5 ≠ 0 ∧ d % 5 = 0) := by
  by_cases hodd : a % 2 = 1 ∧ d % 2 = 0
  · exact Or.inl hodd
  by_cases hf : a % 5 ≠ 0 ∧ d % 5 = 0
  · exact Or.inr hf
  exfalso
  have hterm {q i : ℕ} (hi : i < n) (hdiv : q ∣ a + i * d) :
      q ∣ ∏ j ∈ range n, (a + j * d) :=
    hdiv.trans (Finset.dvd_prod_of_mem _ (mem_range.mpr hi))
  have htwo : 2 ∣ ∏ i ∈ range n, (a + i * d) := by
    by_cases ha2 : a % 2 = 0
    · exact hterm (i := 0) (by omega) (by simpa using Nat.dvd_of_mod_eq_zero ha2)
    · have hdiv : 2 ∣ a + d := by
        apply Nat.dvd_of_mod_eq_zero
        omega
      exact hterm (i := 1) (by omega) (by simpa using hdiv)
  have hfiv : 5 ∣ ∏ i ∈ range n, (a + i * d) := by
    by_cases ha5 : a % 5 = 0
    · exact hterm (i := 0) (by omega) (by simpa using Nat.dvd_of_mod_eq_zero ha5)
    · have hd5 : d % 5 ≠ 0 := fun hd => hf ⟨ha5, hd⟩
      obtain ⟨i, hi⟩ := five_hit a d hd5
      exact hterm (i.isLt.trans_le hn) hi
  have hten : 10 ∣ ∏ i ∈ range n, (a + i * d) :=
    (by decide : Nat.Coprime 2 5).mul_dvd_of_dvd_of_dvd htwo hfiv
  exact not_palindrome_of_ten_dvd (Finset.prod_pos fun i _ => by omega) hten hpal

private theorem prime_dvd_progression_factor {p a d n : ℕ} (hp : p.Prime)
    (hprod : p ∣ ∏ j ∈ Finset.range n, (a + j * d)) :
    ∃ i < n, p ∣ a + i * d := by
  induction n with
  | zero => exact (hp.not_dvd_one (by simpa using hprod)).elim
  | succ n ih =>
    rw [Finset.prod_range_succ] at hprod
    rcases hp.dvd_mul.mp hprod with hbefore | hlast
    · obtain ⟨i, hi, hdiv⟩ := ih hbefore
      exact ⟨i, hi.trans (Nat.lt_succ_self n), hdiv⟩
    · exact ⟨n, Nat.lt_succ_self n, hlast⟩

/-- An even-digit palindromic product has a multiple of eleven among the first
eleven terms of the progression, or earlier if the progression is shorter. -/
theorem eleven_hit {n a d : ℕ}
    (hpal : IsPalindrome (∏ j ∈ Finset.range n, (a + j * d)))
    (hlen : Even (Nat.digits 10 (∏ j ∈ Finset.range n, (a + j * d))).length) :
    ∃ i < min n 11, 11 ∣ a + i * d := by
  have hprod := Nat.eleven_dvd_of_palindrome (List.Palindrome.of_reverse_eq hpal) hlen
  obtain ⟨i, hi', hd⟩ := prime_dvd_progression_factor (by decide : Nat.Prime 11) hprod
  have hmod : i % 11 < min n 11 :=
    lt_min ((Nat.mod_le i 11).trans_lt hi') (Nat.mod_lt _ (by decide))
  have hres : a + (i % 11) * d ≡ a + i * d [MOD 11] :=
    ((Nat.mod_modEq i 11).mul_right d).add_left a
  unfold Nat.ModEq at hres
  exact ⟨i % 11, hmod, Nat.dvd_of_mod_eq_zero (hres.trans (Nat.mod_eq_zero_of_dvd hd))⟩

/-- The remaining case in which every term of the progression is odd. -/
def H1 : Prop :=
  ∀ n a d : ℕ, 6 ≤ n → 1 ≤ a → 1 ≤ d → a % 2 = 1 → d % 2 = 0 →
    (Even (Nat.digits 10 (∏ i ∈ range n, (a + i * d))).length →
      ∃ i < min n 11, 11 ∣ a + i * d) →
    ¬ IsPalindrome (∏ i ∈ range n, (a + i * d))

/-- The remaining case in which an even term occurs and every term is coprime to five. -/
def H2 : Prop :=
  ∀ n a d : ℕ, 6 ≤ n → 1 ≤ a → 1 ≤ d → (a % 2 = 0 ∨ d % 2 = 1) →
    a % 5 ≠ 0 → d % 5 = 0 →
    (Even (Nat.digits 10 (∏ i ∈ range n, (a + i * d))).length →
      ∃ i < min n 11, 11 ∣ a + i * d) →
    ¬ IsPalindrome (∏ i ∈ range n, (a + i * d))

theorem main : H1 → H2 → type_of% @OMA.S_mse_3206134.main := by
  intro h₁ h₂ n a d hn ha hd hpal
  have h11 := eleven_hit hpal
  by_cases ho : a % 2 = 1 ∧ d % 2 = 0
  · exact h₁ n a d hn ha hd ho.1 ho.2 h11 hpal
  · rcases palindrome_residues (by omega) (by omega) hpal with h | ⟨ha5, hd5⟩
    · exact ho h
    · exact h₂ n a d hn ha hd (by omega) ha5 hd5 h11 hpal

end OMA.R_mse_3206134_R1

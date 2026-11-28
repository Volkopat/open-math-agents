import OMAStatements.S_mo_297601
import Mathlib

/-!
# Differences of two positive perfect powers

Odd gaps and multiples of four have explicit witnesses. At a remaining
gap `n`, representations with a common exponent can be tested in a finite
box. Outside that box the only witnesses needed have odd bases and distinct
prime exponents. The first unresolved gap, 6, is isolated from the rest.

Source: https://mathoverflow.net/questions/297601 (including the comment on
differences of squares). See also https://oeis.org/A074981.
Credit: @Solitude1312
-/

namespace OMA.R_mo_297601_R1

/-- The first unresolved value, in prime-exponent form. -/
def H1 : Prop :=
  ∃ a b p q : ℕ, Odd a ∧ Odd b ∧ p.Prime ∧ q.Prime ∧ p ≠ q ∧ 6 + b ^ q = a ^ p

/-- The remaining gaps after testing equal prime exponents in the finite box. -/
def H2 : Prop :=
  ∀ n : ℕ, 10 ≤ n → n % 4 = 2 →
    (∀ a b p : ℕ, 0 < b → b < a → a ≤ n → p.Prime → p ≤ n → n + b ^ p ≠ a ^ p) →
    ∃ a b p q : ℕ, Odd a ∧ Odd b ∧ p.Prime ∧ q.Prime ∧ p ≠ q ∧ n + b ^ q = a ^ p

/-- The gap between like powers is at least the larger base and at least the exponent. -/
lemma same_exponent_bounds {a b e : ℕ} (hb : 0 < b) (hba : b < a) (he : 2 ≤ e) :
    b ^ e + a ≤ a ^ e ∧ b ^ e + e ≤ a ^ e := by
  have base : b ^ 2 + a ≤ a ^ 2 := calc
    b ^ 2 + a ≤ b * a + a := Nat.add_le_add_right (by simpa [pow_two] using Nat.mul_le_mul_left b hba.le) _
    _ = (b + 1) * a := by ring
    _ ≤ a ^ 2 := by simpa [pow_two] using Nat.mul_le_mul_right a hba
  have grow (i m : ℕ) (h : b ^ i + m ≤ a ^ i) : b ^ (i + 1) + (m + 1) ≤ a ^ (i + 1) := by
    have hleft : b ^ i * b + 1 ≤ b ^ i * a := calc
      b ^ i * b + 1 ≤ b ^ i * b + b ^ i := by have := pow_pos hb i; omega
      _ = b ^ i * (b + 1) := by ring
      _ ≤ b ^ i * a := Nat.mul_le_mul_left _ hba
    have hright : m ≤ m * a := Nat.le_mul_of_pos_right _ (by omega)
    have hsum := Nat.mul_le_mul_right a h
    rw [Nat.add_mul] at hsum
    simp only [pow_succ]
    omega
  obtain ⟨j, rfl⟩ : ∃ j, e = j + 2 := ⟨e - 2, by omega⟩
  clear he
  induction j with
  | zero => exact ⟨base, by simpa using (show b ^ 2 + 2 ≤ a ^ 2 by omega)⟩
  | succ j ih =>
    exact ⟨(Nat.le_succ _).trans (grow (j + 2) a ih.1), grow (j + 2) (j + 2) ih.2⟩

private lemma prime_form {r i : ℕ} (hr : 0 < r) (hi : 1 < i) :
    ∃ a p : ℕ, 0 < a ∧ p.Prime ∧ a ^ p = r ^ i := by
  obtain ⟨p, hp, c, hc⟩ := Nat.exists_prime_and_dvd (by omega : i ≠ 1)
  exact ⟨r ^ c, p, pow_pos hr c, hp, by rw [← pow_mul, hc, Nat.mul_comm c p]⟩

private lemma odd_bases {a b p q n : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hn : n % 4 = 2)
    (h : n + b ^ q = a ^ p) : Odd a ∧ Odd b := by
  have parity (x e : ℕ) (he : 2 ≤ e) : (x ^ e) % 2 = x % 2 := by
    rw [Nat.pow_mod]
    rcases Nat.mod_two_eq_zero_or_one x with hz | ho
    · simp [hz, zero_pow (by omega : e ≠ 0)]
    · simp [ho]
  have hm := congrArg (fun z : ℕ => z % 2) h
  change (n + b ^ q) % 2 = (a ^ p) % 2 at hm
  rw [Nat.add_mod, parity a p hp, parity b q hq] at hm
  have hab : a % 2 = b % 2 := by omega
  have four (x e : ℕ) (hx : x % 2 = 0) (he : 2 ≤ e) : 4 ∣ x ^ e := by
    have hh : (2 : ℕ) ∣ x := Nat.dvd_of_mod_eq_zero hx
    exact (pow_dvd_pow_of_dvd hh 2).trans (pow_dvd_pow x he)
  have ha : a % 2 = 1 := by
    by_contra hz
    obtain ⟨u, hu⟩ := four a p (by omega) hp
    obtain ⟨v, hv⟩ := four b q (by omega) hq
    omega
  exact ⟨Nat.odd_iff.mpr ha, Nat.odd_iff.mpr (hab ▸ ha)⟩

/-- Normalization is reversible: the two remaining cases exclude no actual witnesses. -/
lemma normalize {n r s i j : ℕ} (hn : n % 4 = 2) (hr : 0 < r) (hs : 0 < s)
    (hi : 1 < i) (hj : 1 < j) (h : n + s ^ j = r ^ i) :
    (∃ a b p : ℕ, 0 < b ∧ b < a ∧ a ≤ n ∧ p.Prime ∧ p ≤ n ∧ n + b ^ p = a ^ p) ∨
    ∃ a b p q : ℕ, Odd a ∧ Odd b ∧ p.Prime ∧ q.Prime ∧ p ≠ q ∧ n + b ^ q = a ^ p := by
  obtain ⟨a, p, _, hp, hpa⟩ := prime_form hr hi
  obtain ⟨b, q, hb, hq, hqb⟩ := prime_form hs hj
  rw [← hpa, ← hqb] at h
  by_cases heq : p = q
  · subst q
    have hba : b < a := by
      by_contra! hab
      have := Nat.pow_le_pow_left hab p
      omega
    obtain ⟨ha, he⟩ := same_exponent_bounds hb hba hp.two_le
    exact Or.inl ⟨a, b, p, hb, hba, by omega, hp, by omega, h⟩
  · obtain ⟨hoa, hob⟩ := odd_bases hp.two_le hq.two_le hn h
    exact Or.inr ⟨a, b, p, q, hoa, hob, hp, hq, heq, h⟩

/-- Every global representation would satisfy both hypotheses. -/
lemma necessary (hall : type_of% @OMA.S_mo_297601.main) : H1 ∧ H2 := by
  have split (n : ℕ) (hn : n % 4 = 2) :
      (∃ a b p : ℕ, 0 < b ∧ b < a ∧ a ≤ n ∧ p.Prime ∧ p ≤ n ∧ n + b ^ p = a ^ p) ∨
      ∃ a b p q : ℕ, Odd a ∧ Odd b ∧ p.Prime ∧ q.Prime ∧ p ≠ q ∧ n + b ^ q = a ^ p := by
    obtain ⟨r, s, i, j, hr, hs, hi, hj, heq⟩ := hall n (by omega)
    have h : (n : ℤ) + (s : ℤ) ^ j = (r : ℤ) ^ i := by omega
    exact normalize hn hr hs hi hj (by exact_mod_cast h)
  constructor
  · rcases split 6 (by decide) with ⟨a, b, p, hb, hba, ha, hp, he, h⟩ | h
    · have box : ∀ a b p : Fin 7, 0 < b.val → b.val < a.val → Nat.Prime p.val →
          6 + b.val ^ p.val ≠ a.val ^ p.val := by decide
      exact (box ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨p, by omega⟩ hb hba hp h).elim
    · exact h
  · intro n _ hn noEqual
    rcases split n hn with ⟨a, b, p, hb, hba, ha, hp, he, h⟩ | h
    · exact (noEqual a b p hb hba ha hp he h).elim
    · exact h

theorem main : H1 → H2 → type_of% @OMA.S_mo_297601.main := by
  intro six rest n hn
  by_cases ho : n % 2 = 1
  · by_cases h1 : n = 1
    · subst n
      exact ⟨3, 2, 2, 3, by decide, by decide, by decide, by decide, by decide⟩
    obtain ⟨t, rfl⟩ : ∃ t, n = 2 * t + 3 := ⟨n / 2 - 1, by omega⟩
    exact ⟨t + 2, t + 1, 2, 2, by omega, by omega, by decide, by decide,
      by push_cast; ring⟩
  by_cases hm : n % 4 = 0
  · by_cases h4 : n = 4
    · subst n
      exact ⟨2, 2, 3, 2, by decide, by decide, by decide, by decide, by decide⟩
    obtain ⟨t, rfl⟩ : ∃ t, n = 4 * (t + 2) := ⟨n / 4 - 2, by omega⟩
    exact ⟨t + 3, t + 1, 2, 2, by omega, by omega, by decide, by decide,
      by push_cast; ring⟩
  have hn4 : n % 4 = 2 := by omega
  by_cases h2 : n = 2
  · subst n
    exact ⟨3, 5, 3, 2, by decide, by decide, by decide, by decide, by decide⟩
  have lift (a b p q : ℕ) (ha : 0 < a) (hb : 0 < b) (hp : 1 < p) (hq : 1 < q)
      (h : n + b ^ q = a ^ p) :
      ∃ r s i j : ℕ, 0 < r ∧ 0 < s ∧ 1 < i ∧ 1 < j ∧
        (n : ℤ) = (r : ℤ) ^ i - (s : ℤ) ^ j := by
    have hz : (n : ℤ) + (b : ℤ) ^ q = (a : ℤ) ^ p := by exact_mod_cast h
    exact ⟨a, b, p, q, ha, hb, hp, hq, by omega⟩
  by_cases h6 : n = 6
  · obtain ⟨a, b, p, q, ha, hb, hp, hq, _, h⟩ := six
    exact lift a b p q ha.pos hb.pos hp.one_lt hq.one_lt (h6 ▸ h)
  by_cases box : ∃ a b p : ℕ, 0 < b ∧ b < a ∧ a ≤ n ∧ p.Prime ∧ p ≤ n ∧ n + b ^ p = a ^ p
  · obtain ⟨a, b, p, hb, hba, _, hp, _, h⟩ := box
    exact lift a b p p (by omega) hb hp.one_lt hp.one_lt h
  obtain ⟨a, b, p, q, ha, hb, hp, hq, _, h⟩ := rest n (by omega) hn4
    (fun a b p hb hba ha hp he h => box ⟨a, b, p, hb, hba, ha, hp, he, h⟩)
  exact lift a b p q ha.pos hb.pos hp.one_lt hq.one_lt h

end OMA.R_mo_297601_R1

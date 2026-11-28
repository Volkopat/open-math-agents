import OMAStatements.S_oeis_a095303

-- Reduction of OEIS A095303. Credit: @Pixelstorm44
namespace OMA.R_oeis_a095303_R1

/-- Prime powers occur at arbitrarily large factorial indices. A single
base suffices at each such index, and powers of any positive exponent are allowed. -/
def H1 : Prop :=
  ∀ cutoff : ℕ, ∃ t k p m : ℕ, cutoff ≤ t ∧ 2 ≤ k ∧ p.Prime ∧ 0 < m ∧
    k ^ t.factorial = p ^ m + 2

/-- The exponent bound of Schinzel and Tijdeman for the fixed polynomial
X² − 2, which has two distinct roots (Acta Arith. 31 (1976), 199–204). -/
def H2 : Prop :=
  ∃ B : ℕ, ∀ x y m : ℕ, 2 ≤ y → x ^ 2 = y ^ m + 2 → m ≤ B

lemma power_gap {a b m : ℕ} (hb : 2 ≤ b) (hm : 2 ≤ m) :
    a ^ m ≠ b ^ m + 2 := by
  intro heq
  have hba : b < a := by
    by_contra! h
    have := Nat.pow_le_pow_left h m
    omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hmono := Nat.pow_le_pow_left hba.le j
  have hpos : 0 < b ^ j := pow_pos (by omega) _
  have hstep : b ^ j * ((b + 1) ^ 2) ≤ a ^ j * a ^ 2 :=
    Nat.mul_le_mul hmono (Nat.pow_le_pow_left hba 2)
  rw [show 2 + j = j + 2 by omega, pow_add, pow_add] at heq
  nlinarith [Nat.mul_le_mul_right (b ^ j) hb]

lemma regroup {d D : ℕ} (k : ℕ) (hd : d ∣ D) :
    (k ^ (D / d)) ^ d = k ^ D := by
  rw [← pow_mul, Nat.div_mul_cancel hd]

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a095303.main := by
  intro hits bound n hn
  obtain ⟨B, hB⟩ := bound
  obtain ⟨t, k, p, m, ht, hk, hp, hm, heq⟩ := hits (B + n + 2)
  have htwo : 2 ∣ t.factorial := Nat.dvd_factorial (by decide) (by omega)
  have hbound := hB (k ^ (t.factorial / 2)) p m hp.two_le ((regroup k htwo).trans heq)
  have hmd : m ∣ t.factorial := Nat.dvd_factorial hm (by omega)
  have hm1 : m = 1 := by
    by_contra h
    exact power_gap hp.two_le (by omega : 2 ≤ m) ((regroup k hmd).trans heq)
  have hnd : n ∣ t.factorial := Nat.dvd_factorial hn (by omega)
  have hq : t.factorial / n ≠ 0 := by
    intro hz
    have := Nat.div_mul_cancel hnd
    rw [hz, zero_mul] at this
    exact (Nat.factorial_ne_zero t) this.symm
  refine ⟨k ^ (t.factorial / n), hk.trans (le_self_pow₀ (by omega) hq), ?_⟩
  simpa [regroup k hnd, heq, hm1] using hp

open Polynomial

/-- The two algebraic tests for the polynomial X^n - 2 in Bunyakovsky's conjecture. -/
theorem binomial_admissible {n : ℕ} (hn : 0 < n) :
    let f : ℤ[X] := X ^ n - C 2
    (1 ≤ f.degree ∧ Irreducible f ∧ 0 < f.leadingCoeff) ∧
      ∀ p : ℕ, p.Prime → ∃ k : ℕ, ¬ (p : ℤ) ∣ f.eval (k : ℤ) := by
  dsimp only
  have hmon := monic_X_pow_sub_C (2 : ℤ) hn.ne'
  have hE : (X ^ n - C (2 : ℤ)).IsEisensteinAt (Ideal.span {(2 : ℤ)}) := by
    constructor
    · rw [hmon.leadingCoeff, Ideal.mem_span_singleton]
      decide
    · intro i hi
      rw [natDegree_X_pow_sub_C] at hi
      simp only [Ideal.mem_span_singleton, coeff_sub, coeff_X_pow, if_neg hi.ne, coeff_C]
      split <;> norm_num
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      simp [coeff_X_pow, coeff_sub, Ne.symm hn.ne']
  refine ⟨⟨?_, hE.irreducible ((Ideal.span_singleton_prime (by decide)).2 Int.prime_two)
    hmon.isPrimitive (by rw [natDegree_X_pow_sub_C]; exact hn), ?_⟩, ?_⟩
  · rw [degree_X_pow_sub_C hn]
    exact_mod_cast hn
  · rw [hmon.leadingCoeff]
    decide
  · intro p hp
    refine ⟨1, ?_⟩
    have h : ¬ (p : ℤ) ∣ (1 : ℤ) := by
      exact_mod_cast hp.not_dvd_one
    simpa using h

/-- The usual prime-value conjecture implies existence at each positive degree. -/
theorem prime_value_of_bunyakovsky
    (primeValues : ∀ f : ℤ[X], (1 ≤ f.degree ∧ Irreducible f ∧ 0 < f.leadingCoeff) →
      (∀ p : ℕ, p.Prime → ∃ k : ℕ, ¬ (p : ℤ) ∣ f.eval (k : ℤ)) →
      {k : ℕ | (f.eval (k : ℤ)).natAbs.Prime}.Infinite)
    (n : ℕ) (hn : 0 < n) : ∃ k : ℕ, 2 ≤ k ∧ (k ^ n - 2).Prime := by
  obtain ⟨hpoly, hlocal⟩ := binomial_admissible hn
  obtain ⟨k, hk, hlarge⟩ := (primeValues _ hpoly hlocal).exists_gt 1
  have hpow : 2 ≤ k ^ n := le_trans hlarge (le_self_pow₀ (by omega) hn.ne')
  refine ⟨k, hlarge, ?_⟩
  change (((X ^ n - C 2 : ℤ[X]).eval (k : ℤ)).natAbs).Prime at hk
  rw [eval_sub, eval_pow, eval_X, eval_C] at hk
  have hc : ((k ^ n - 2 : ℕ) : ℤ) = (k : ℤ) ^ n - 2 := by
    rw [Nat.cast_sub hpow, Nat.cast_pow]
    rfl
  rw [← hc] at hk
  exact hk

end OMA.R_oeis_a095303_R1

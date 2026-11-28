import FormalConjectures.Wikipedia.EswarathasanLevineConjecture
import Mathlib

/-!
# The Eswarathasan-Levine conjecture via Boyd's empty-level criterion

For a prime `p` let `J_p` be the set of `n ≥ 1` with `p` dividing the numerator of `H_n`.
Proved here: the descent `n ∈ J_p, p ≤ n → n / p ∈ J_p` (Eswarathasan-Levine 1991, Boyd 1994),
the finiteness of `J_2 = ∅`, `J_3 ⊆ {2, 7, 22}`, `J_5 ⊆ {4, 20, 24}`, and that if one p-adic level
`[p^k, p^(k+1))` of `J_p` is empty then `J_p ⊆ [1, p^k)` is finite. This is exactly the criterion
by which Boyd (1994) proved finiteness for every prime `p ≤ 547` except `83, 127, 397`.

* `H1`: Boyd's computation: for `7 ≤ p ≤ 547`, `p ∉ {83, 127, 397}` some level is empty.
* `H2`: the open part: the same for `p = 83, 127, 397` and every prime `p > 547`.
-/

namespace OMA.R_EswarathasanLevineConjecture_eswarathasan_levine_harmonic_conjecture_R2
open EswarathasanLevineConjecture

/-- Boyd's computation (1994): primes from 7 to 547 other than 83, 127, 397. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 7 ≤ p → p ≤ 547 → p ≠ 83 → p ≠ 127 → p ≠ 397 →
    ∃ k : ℕ, ∀ n ∈ harmonicNumDivisibleSet p, ¬ (p ^ k ≤ n ∧ n < p ^ (k + 1))

/-- The open part: 83, 127, 397 and every prime above 547. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → (547 < p ∨ p = 83 ∨ p = 127 ∨ p = 397) →
    ∃ k : ℕ, ∀ n ∈ harmonicNumDivisibleSet p, ¬ (p ^ k ≤ n ∧ n < p ^ (k + 1))

lemma harmonic_split (p : ℕ) (hp : 0 < p) (n : ℕ) :
    harmonic n = harmonic (n / p) / p +
      ∑ j ∈ Finset.range (n + 1), (if p ∣ j then (0 : ℚ) else ((j : ℕ) : ℚ)⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases h : p ∣ n + 1
    · have h3 : (n + 1) / p = n / p + 1 := by rw [Nat.succ_div, if_pos h]
      have h2 : ((n + 1 : ℕ) : ℚ) = ((n / p + 1 : ℕ) : ℚ) * p := by
        rw [← h3]; exact_mod_cast (Nat.div_mul_cancel h).symm
      rw [harmonic_succ, Finset.sum_range_succ, h3, harmonic_succ, if_pos h, ih, h2]
      have hp' : (p : ℚ) ≠ 0 := by positivity
      rw [mul_inv]
      ring
    · have h3 : (n + 1) / p = n / p := by rw [Nat.succ_div, if_neg h, add_zero]
      rw [harmonic_succ, Finset.sum_range_succ, h3, if_neg h, ih]
      ring

lemma den_add {p : ℕ} (hp : p.Prime) {a b : ℚ} (ha : ¬ p ∣ a.den) (hb : ¬ p ∣ b.den) :
    ¬ p ∣ (a + b).den := by
  intro h
  rcases hp.dvd_mul.mp (Nat.dvd_trans h (Rat.add_den_dvd a b)) with h' | h'
  · exact ha h'
  · exact hb h'

lemma den_sum {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ¬ p ∣ (∑ j ∈ Finset.range m, (if p ∣ j then (0 : ℚ) else ((j : ℕ) : ℚ)⁻¹)).den := by
  induction m with
  | zero => simpa using hp.not_dvd_one
  | succ m ih =>
    rw [Finset.sum_range_succ]
    refine den_add hp ih ?_
    split_ifs with h
    · simpa using hp.not_dvd_one
    · rw [Rat.inv_natCast_den]
      split_ifs
      · exact hp.not_dvd_one
      · exact h

lemma dvd_num_of_eq_mul {p : ℕ} (hp : p.Prime) (r : ℚ) (hr : ¬ p ∣ r.den) :
    (p : ℤ) ∣ ((p : ℚ) * r).num := by
  have key : (((p : ℚ) * r).num : ℚ) * r.den = ((p * r.num * ((p : ℚ) * r).den : ℤ) : ℚ) := by
    push_cast
    rw [← Rat.mul_den_eq_num ((p : ℚ) * r), ← Rat.mul_den_eq_num r]
    ring
  have keyZ : ((p : ℚ) * r).num * r.den = p * r.num * ((p : ℚ) * r).den := by exact_mod_cast key
  have hdvd : (p : ℤ) ∣ ((p : ℚ) * r).num * r.den := by
    rw [keyZ, mul_assoc]; exact dvd_mul_right _ _
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hdvd with h | h
  · exact h
  · exact absurd (Int.natCast_dvd_natCast.mp h) hr

/-- The Eswarathasan-Levine / Boyd descent. -/
theorem descent {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : p ≤ n) (h : (p : ℤ) ∣ (harmonic n).num) :
    n / p ∈ harmonicNumDivisibleSet p := by
  refine ⟨(Nat.one_le_div_iff hp.pos).mpr hn, ?_⟩
  have hs := harmonic_split p hp.pos n
  set T := ∑ j ∈ Finset.range (n + 1), (if p ∣ j then (0 : ℚ) else ((j : ℕ) : ℚ)⁻¹) with hT
  have hTd : ¬ p ∣ T.den := den_sum hp (n + 1)
  have hHd : ¬ p ∣ (harmonic n).den := fun hd =>
    Nat.not_coprime_of_dvd_of_dvd hp.one_lt (Int.natCast_dvd.mp h) hd (harmonic n).reduced
  have hrd : ¬ p ∣ (harmonic n + -T).den := den_add hp hHd (by rwa [Rat.neg_den])
  have heq : harmonic (n / p) = (p : ℚ) * (harmonic n + -T) := by
    have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [hs]; field_simp; ring
  rw [heq]
  exact dvd_num_of_eq_mul hp _ hrd

lemma notdvd3 : ∀ n ∈ ({1, 6, 8, 21, 23, 66, 67, 68} : Finset ℕ), ¬ (3 : ℤ) ∣ (harmonic n).num := by
  intro n hn
  fin_cases hn <;> decide +kernel

lemma notdvd5 : ∀ n ∈ ({1, 2, 3, 21, 22, 23, 100, 101, 102, 103, 104, 120, 121, 122, 123, 124} : Finset ℕ),
    ¬ (5 : ℤ) ∣ (harmonic n).num := by
  intro n hn
  fin_cases hn <;> decide +kernel

theorem J3_sub : ∀ n, n ∈ harmonicNumDivisibleSet 3 → n = 2 ∨ n = 7 ∨ n = 22 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  obtain ⟨h1, h⟩ := hn
  have nd := fun k (hk : k ∈ ({1, 6, 8, 21, 23, 66, 67, 68} : Finset ℕ)) (hkn : n = k) =>
    notdvd3 k hk (hkn ▸ h)
  by_cases hlt : n < 3
  · interval_cases n
    · exact absurd rfl (nd 1 (by decide))
    · left; rfl
  · have hm := ih (n / 3) (Nat.div_lt_self (by omega) (by norm_num))
      (descent Nat.prime_three (by omega) h)
    rcases hm with hm | hm | hm
    · have : 6 ≤ n ∧ n ≤ 8 := by omega
      obtain ⟨a, b⟩ := this
      interval_cases n
      · exact absurd rfl (nd 6 (by decide))
      · right; left; rfl
      · exact absurd rfl (nd 8 (by decide))
    · have : 21 ≤ n ∧ n ≤ 23 := by omega
      obtain ⟨a, b⟩ := this
      interval_cases n
      · exact absurd rfl (nd 21 (by decide))
      · right; right; rfl
      · exact absurd rfl (nd 23 (by decide))
    · have : 66 ≤ n ∧ n ≤ 68 := by omega
      obtain ⟨a, b⟩ := this
      interval_cases n
      · exact absurd rfl (nd 66 (by decide))
      · exact absurd rfl (nd 67 (by decide))
      · exact absurd rfl (nd 68 (by decide))

theorem J5_sub : ∀ n, n ∈ harmonicNumDivisibleSet 5 → n = 4 ∨ n = 20 ∨ n = 24 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  obtain ⟨h1, h⟩ := hn
  have nd := fun k (hk : k ∈ ({1, 2, 3, 21, 22, 23, 100, 101, 102, 103, 104, 120, 121, 122, 123, 124} : Finset ℕ)) (hkn : n = k) =>
    notdvd5 k hk (hkn ▸ h)
  by_cases hlt : n < 5
  · interval_cases n
    · exact absurd rfl (nd 1 (by decide))
    · exact absurd rfl (nd 2 (by decide))
    · exact absurd rfl (nd 3 (by decide))
    · left; rfl
  · have hm := ih (n / 5) (Nat.div_lt_self (by omega) (by norm_num))
      (descent Nat.prime_five (by omega) h)
    rcases hm with hm | hm | hm
    · have : 20 ≤ n ∧ n ≤ 24 := by omega
      obtain ⟨a, b⟩ := this
      interval_cases n
      · right; left; rfl
      · exact absurd rfl (nd 21 (by decide))
      · exact absurd rfl (nd 22 (by decide))
      · exact absurd rfl (nd 23 (by decide))
      · right; right; rfl
    · have : 100 ≤ n ∧ n ≤ 104 := by omega
      obtain ⟨a, b⟩ := this
      interval_cases n <;> exact absurd rfl (nd _ (by decide))
    · have : 120 ≤ n ∧ n ≤ 124 := by omega
      obtain ⟨a, b⟩ := this
      interval_cases n <;> exact absurd rfl (nd _ (by decide))

theorem small_primes : ∀ p : ℕ, p.Prime → p < 7 → (harmonicNumDivisibleSet p).Finite := by
  intro p hp h7
  interval_cases p
  · exact absurd hp Nat.not_prime_zero
  · exact absurd hp Nat.not_prime_one
  · refine Set.Finite.subset Set.finite_empty ?_
    rintro n ⟨hn, hdvd⟩
    have hnum := (Rat.num_ne_zero.mpr (harmonic_pos (by omega : n ≠ 0)).ne')
    have h2 : (2 : ℕ) ∣ (harmonic n).num.natAbs := Int.natCast_dvd.mp hdvd
    have hden : ¬ (2 : ℕ) ∣ (harmonic n).den :=
      fun hd => Nat.not_coprime_of_dvd_of_dvd (by norm_num) h2 hd (harmonic n).reduced
    have hv := one_le_padicValNat_of_dvd (Int.natAbs_pos.mpr hnum).ne' h2
    have h := padicValRat_two_harmonic n
    simp only [padicValRat, padicValInt, padicValNat.eq_zero_of_not_dvd hden,
      Nat.cast_zero, sub_zero] at h
    omega
  · exact (Set.toFinite ({2, 7, 22} : Set ℕ)).subset (fun n hn => by
      rcases J3_sub n hn with rfl | rfl | rfl <;> simp)
  · exact absurd hp (by decide)
  · exact (Set.toFinite ({4, 20, 24} : Set ℕ)).subset (fun n hn => by
      rcases J5_sub n hn with rfl | rfl | rfl <;> simp)
  · exact absurd hp (by decide)

/-- An empty p-adic level bounds the whole tree. -/
theorem finite_of_level {p : ℕ} (hp : p.Prime) (k : ℕ)
    (hk : ∀ n ∈ harmonicNumDivisibleSet p, ¬ (p ^ k ≤ n ∧ n < p ^ (k + 1))) :
    (harmonicNumDivisibleSet p).Finite := by
  have key : ∀ n, n ∈ harmonicNumDivisibleSet p → n < p ^ k := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro hn
    by_contra hlt
    push_neg at hlt
    by_cases h2 : n < p ^ (k + 1)
    · exact hk n hn ⟨hlt, h2⟩
    · push_neg at h2
      have hpk : p ≤ p ^ (k + 1) := by
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ (k + 1) := Nat.pow_le_pow_right hp.pos (by omega)
      have hpn : p ≤ n := le_trans hpk h2
      have hdesc := descent hp hpn hn.2
      have hlt' := ih (n / p) (Nat.div_lt_self (by have := hn.1; omega) hp.one_lt) hdesc
      have : n < p ^ k * p := (Nat.div_lt_iff_lt_mul hp.pos).mp hlt'
      rw [← pow_succ] at this
      omega
  exact (Set.finite_Iio (p ^ k)).subset (fun n hn => key n hn)

theorem main : H1 → H2 →
    type_of% @EswarathasanLevineConjecture.eswarathasan_levine_harmonic_conjecture := by
  intro h1 h2 p hp
  by_cases h7 : p < 7
  · exact small_primes p hp h7
  · by_cases hb : 547 < p ∨ p = 83 ∨ p = 127 ∨ p = 397
    · obtain ⟨k, hk⟩ := h2 p hp hb
      exact finite_of_level hp k hk
    · push_neg at hb
      obtain ⟨k, hk⟩ := h1 p hp (by omega) hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
      exact finite_of_level hp k hk

end OMA.R_EswarathasanLevineConjecture_eswarathasan_levine_harmonic_conjecture_R2

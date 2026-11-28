import OMAStatements.S_oeis_a259533

/-!
Proof sketch. By induction on `n`, `j! S(n, j) = Sum_i (-1)^(j+i) C(j, i) i^n`. For `n >= k`
every power satisfies `i^(n + t) = i^n mod k` whenever `phi(k)` divides `t` (prime powers:
divisibility or Euler, coprime products by CRT). Padding the shorter sum with the vanishing
terms `S(n, j) = 0` for `j > n` gives a termwise congruence, so `N = k` works.
-/

namespace R259533
open OMA.S_oeis_a259533 Finset

theorem s_zero : ∀ n j : ℕ, n < j → stirling2 n j = 0 := by
  intro n
  induction n with
  | zero =>
    intro j hj
    obtain ⟨j, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    simp [stirling2]
  | succ n ih =>
    intro j hj
    obtain ⟨j, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    simp [stirling2, ih (j + 1) (by omega), ih j (by omega)]

def E (n j : ℕ) : ℤ := ∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n

theorem E_succ (n j : ℕ) : E (n + 1) (j + 1) = ((j : ℤ) + 1) * (E n (j + 1) + E n j) := by
  have h2 : E n j = ∑ i ∈ range (j + 1 + 1),
      (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n := by
    rw [E, sum_range_succ _ (j + 1)]
    simp
  rw [h2, E, E, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl (fun i hi => ?_)
  have hi' : i ≤ j + 1 := by simp at hi; omega
  have h' : ((j.choose i * (j + 1) : ℕ) : ℤ) = (((j + 1).choose i * (j + 1 - i) : ℕ) : ℤ) := by
    rw [Nat.choose_mul_succ_eq]
  push_cast [Nat.cast_sub hi'] at h'
  have hs : (-1 : ℤ) ^ (j + 1 + i) = -(-1) ^ (j + i) := by
    rw [show j + 1 + i = (j + i) + 1 by omega, pow_succ]
    ring
  rw [hs]
  linear_combination (-((-1 : ℤ) ^ (j + i) * (i : ℤ) ^ n)) * h'

theorem formula : ∀ n j : ℕ, (j.factorial : ℤ) * (stirling2 n j : ℤ) = E n j := by
  intro n
  induction n with
  | zero =>
    intro j
    cases j with
    | zero => simp [E, stirling2]
    | succ j =>
      have h : E 0 (j + 1) = (-1) ^ (j + 1) *
          ∑ i ∈ range (j + 1 + 1), ((-1 : ℤ) ^ i * ((j + 1).choose i : ℤ)) := by
        rw [E, mul_sum]
        refine sum_congr rfl (fun i _ => ?_)
        rw [pow_add (-1 : ℤ) (j + 1) i]
        ring
      rw [h, Int.alternating_sum_range_choose_of_ne (by omega)]
      simp [stirling2]
  | succ n ih =>
    intro j
    cases j with
    | zero => simp [E, stirling2]
    | succ j =>
      rw [E_succ, ← ih (j + 1), ← ih j]
      simp only [stirling2, Nat.factorial_succ]
      push_cast
      ring

theorem pow_per : ∀ k i n t : ℕ, k ≤ n → Nat.totient k ∣ t → i ^ (n + t) ≡ i ^ n [MOD k] := by
  intro k
  induction k using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp _ =>
    intro i n t hn ht
    by_cases hpi : p ∣ i
    · have he' : e ≤ n := le_trans (Nat.lt_pow_self hp.one_lt).le hn
      have h1 : p ^ e ∣ i ^ n := (pow_dvd_pow p he').trans (pow_dvd_pow_of_dvd hpi n)
      have h2 : p ^ e ∣ i ^ (n + t) := h1.trans (pow_dvd_pow i (by omega))
      exact (Nat.modEq_zero_iff_dvd.2 h2).trans (Nat.modEq_zero_iff_dvd.2 h1).symm
    · have hc : Nat.Coprime i (p ^ e) :=
        Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpi).symm
      obtain ⟨m, rfl⟩ := ht
      calc i ^ (n + Nat.totient (p ^ e) * m) = i ^ n * (i ^ Nat.totient (p ^ e)) ^ m := by
            rw [pow_add, pow_mul]
        _ ≡ i ^ n * 1 ^ m [MOD p ^ e] :=
            Nat.ModEq.mul_left _ (Nat.ModEq.pow _ (Nat.ModEq.pow_totient hc))
        _ = i ^ n := by rw [one_pow, mul_one]
  | zero =>
    intro i n t _ ht
    rw [Nat.totient_zero, zero_dvd_iff] at ht
    subst ht
    exact Nat.ModEq.refl _
  | one => intro i n t _ _; exact Nat.modEq_one
  | coprime a b ha hb hab iha ihb =>
    intro i n t hn ht
    have hab0 : 0 < a * b := Nat.mul_pos (by omega) (by omega)
    have ha' : a ≤ n := le_trans (Nat.le_of_dvd hab0 (dvd_mul_right a b)) hn
    have hb' : b ≤ n := le_trans (Nat.le_of_dvd hab0 (dvd_mul_left b a)) hn
    exact (Nat.modEq_and_modEq_iff_modEq_mul hab).1
      ⟨iha i n t ha' ((Nat.totient_dvd_of_dvd (dvd_mul_right a b)).trans ht),
       ihb i n t hb' ((Nat.totient_dvd_of_dvd (dvd_mul_left b a)).trans ht)⟩

theorem core (g : ℕ → ℕ → ℕ) (k n n' : ℕ) (hn : n ≤ n') (h0 : ∀ m j, m < j → g m j = 0)
    (hc : ∀ j, g n' j ≡ g n j [MOD k]) :
    ∑ j ∈ range (n' + 1), g n' j ≡ ∑ j ∈ range (n + 1), g n j [MOD k] := by
  have e : ∑ j ∈ range (n + 1), g n j = ∑ j ∈ range (n' + 1), g n j :=
    sum_subset (Finset.range_subset_range.2 (by omega))
      (fun j _ hj => h0 n j (by simp at hj; omega))
  rw [e]
  exact Nat.ModEq.sum (fun j _ => hc j)

theorem gen (c : ℕ → ℕ) (k n : ℕ) (hn : k ≤ n) :
    ∑ j ∈ range (n + Nat.totient k + 1), stirling2 (n + Nat.totient k) j * j.factorial * c j ≡
      ∑ j ∈ range (n + 1), stirling2 n j * j.factorial * c j [MOD k] := by
  refine core (fun m j => stirling2 m j * j.factorial * c j) k n _ (by omega)
    (fun m j h => by simp [s_zero m j h]) (fun j => ?_)
  rw [← Int.natCast_modEq_iff]
  simp only [Nat.cast_mul]
  have e : ∀ m, (stirling2 m j : ℤ) * (j.factorial : ℤ) * (c j : ℤ) = E m j * c j := fun m => by
    rw [← formula]; ring
  rw [e, e]
  refine Int.ModEq.mul_right _ ?_
  unfold E
  refine Int.ModEq.sum (fun i _ => Int.ModEq.mul_left _ ?_)
  have h := Int.natCast_modEq_iff.2 (pow_per k i n (Nat.totient k) hn dvd_rfl)
  push_cast at h
  exact h

end R259533

theorem OMA.solution : type_of% @OMA.S_oeis_a259533.main := by
  intro k _
  exact ⟨k, fun n hn => R259533.gen (OMA.S_oeis_a259533.coeffG) k n hn⟩

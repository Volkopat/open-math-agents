import OMAStatements.S_oeis_a354253
import Mathlib

/-!
Peter Bala's conjecture on the eventual period of OEIS A354253.
Source for the conjecture and the Stirling sum: https://oeis.org/A354253/internal
Formal statement credit: @DomTheDeveloper
Proof credit: @grp06
-/

namespace OMA.S_oeis_a354253

private def forwardDiff : ℕ → (ℕ → ℤ) → ℕ → ℤ
  | 0, f, x => f x
  | j + 1, f, x => forwardDiff j f (x + 1) - forwardDiff j f x

private theorem forwardDiff_succ_mul (f : ℕ → ℤ) (j x : ℕ) :
    forwardDiff (j + 1) (fun y => (y : ℤ) * f y) x =
      ((x : ℤ) + ((j + 1 : ℕ) : ℤ)) * forwardDiff (j + 1) f x +
        ((j + 1 : ℕ) : ℤ) * forwardDiff j f x := by
  induction j generalizing x with
  | zero =>
      simp only [forwardDiff, Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add]
      ring
  | succ j ih =>
      change forwardDiff (j + 1) (fun y => (y : ℤ) * f y) (x + 1) -
        forwardDiff (j + 1) (fun y => (y : ℤ) * f y) x = _
      rw [ih (x + 1), ih x]
      have hx : forwardDiff (j + 1) f x = forwardDiff j f (x + 1) - forwardDiff j f x :=
        rfl
      have hs : forwardDiff (j + 2) f x =
          forwardDiff (j + 1) f (x + 1) - forwardDiff (j + 1) f x := rfl
      rw [hs]
      -- The difference of the two lower-order terms is itself a forward difference.
      push_cast
      linear_combination (-((j : ℤ) + 1)) * hx

private theorem forwardDiff_succ_one (j x : ℕ) :
    forwardDiff (j + 1) (fun _ => (1 : ℤ)) x = 0 := by
  induction j generalizing x with
  | zero => simp [forwardDiff]
  | succ j ih =>
      change forwardDiff (j + 1) (fun _ => (1 : ℤ)) (x + 1) -
        forwardDiff (j + 1) (fun _ => (1 : ℤ)) x = 0
      rw [ih (x + 1), ih x, sub_self]

private theorem forwardDiff_power (n j : ℕ) :
    forwardDiff j (fun x => (x : ℤ) ^ n) 0 =
      ((j.factorial * Nat.stirlingSecond n j : ℕ) : ℤ) := by
  induction n generalizing j with
  | zero =>
      cases j with
      | zero => simp [forwardDiff]
      | succ j => simp [forwardDiff_succ_one]
  | succ n ih =>
      cases j with
      | zero => simp [forwardDiff, pow_succ]
      | succ j =>
          simp only [pow_succ']
          rw [forwardDiff_succ_mul, ih (j + 1), ih j, Nat.stirlingSecond_succ_succ]
          simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_succ,
            Nat.cast_one, Nat.cast_zero, zero_add]
          ring

private theorem power_period {k n : ℕ} (hk : 0 < k) (hn : k ≤ n) (x : ℕ) :
    x ^ (n + k.totient) ≡ x ^ n [MOD k] := by
  by_cases hx : x = 0
  · subst x
    have h₁ : n ≠ 0 := by omega
    have h₂ : n + k.totient ≠ 0 := by omega
    simp [zero_pow h₁, zero_pow h₂, Nat.ModEq]
  have hle : x ^ n ≤ x ^ (n + k.totient) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero hx) (by omega)
  apply Nat.ModEq.symm
  apply (Nat.modEq_iff_dvd' hle).2
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2
  intro p e hp hpk
  apply (Nat.modEq_iff_dvd' hle).1
  apply Nat.ModEq.symm
  by_cases hpx : p ∣ x
  · have he : e ≤ n :=
      (Nat.lt_pow_self (n := e) hp.one_lt).le.trans ((Nat.le_of_dvd hk hpk).trans hn)
    have hz : ∀ m : ℕ, e ≤ m → x ^ m ≡ 0 [MOD p ^ e] :=
      fun m hm => Nat.modEq_zero_iff_dvd.2 (pow_dvd_pow_of_dvd_of_le hpx hm)
    exact (hz _ (by omega)).trans (hz _ he).symm
  · have hEuler : x ^ (p ^ e).totient ≡ 1 [MOD p ^ e] :=
      Nat.ModEq.pow_totient (hp.coprime_pow_of_not_dvd hpx)
    obtain ⟨t, ht⟩ := Nat.totient_dvd_of_dvd hpk
    rw [pow_add, ht, pow_mul]
    simpa only [one_pow, mul_one] using (hEuler.pow t).mul_left (x ^ n)

private theorem forwardDiff_modEq {k : ℕ} {f g : ℕ → ℤ}
    (h : ∀ x, f x ≡ g x [ZMOD (k : ℤ)]) (j x : ℕ) :
    forwardDiff j f x ≡ forwardDiff j g x [ZMOD (k : ℤ)] := by
  induction j generalizing x with
  | zero => exact h x
  | succ j ih => exact (ih (x + 1)).sub (ih x)

private def summand (n j : ℕ) : ℕ :=
  2 ^ j * (2 * j).choose j * (j.factorial * Nat.stirlingSecond n j)

private theorem summand_eq (n j : ℕ) :
    2 ^ j * (2 * j).factorial * Nat.stirlingSecond n j / j.factorial = summand n j := by
  have hc : (2 * j).choose j * j.factorial * j.factorial = (2 * j).factorial := by
    simpa only [two_mul] using Nat.add_choose_mul_factorial_mul_factorial j j
  have hf : 2 ^ j * (2 * j).factorial * Nat.stirlingSecond n j =
      summand n j * j.factorial := by
    rw [← hc, summand]
    ring
  rw [hf, Nat.mul_div_cancel _ (Nat.factorial_pos j)]

private theorem a_truncate {k n : ℕ} (hk : 0 < k) (hn : k ≤ n) :
    a n ≡ ∑ j ∈ Finset.range k, summand n j [MOD k] := by
  have hsum : a n = ∑ j ∈ Finset.range (n + 1), summand n j := by
    unfold a
    apply Finset.sum_congr rfl
    intro j _
    exact summand_eq n j
  rw [hsum, ← Finset.sum_range_add_sum_Ico _ (show k ≤ n + 1 by omega)]
  have htail : (∑ j ∈ Finset.Ico k (n + 1), summand n j) ≡ 0 [MOD k] := by
    apply Nat.ModEq.sum_zero
    intro j hj
    have hd : k ∣ j.factorial := Nat.dvd_factorial hk (Finset.mem_Ico.1 hj).1
    exact Nat.modEq_zero_iff_dvd.2
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hd _) _)
  simpa only [add_zero] using htail.add_left (∑ j ∈ Finset.range k, summand n j)

private theorem summand_period {k n : ℕ} (hk : 0 < k) (hn : k ≤ n) (j : ℕ) :
    summand (n + k.totient) j ≡ summand n j [MOD k] := by
  have hp (x : ℕ) : (x : ℤ) ^ (n + k.totient) ≡ (x : ℤ) ^ n [ZMOD (k : ℤ)] := by
    simpa only [Nat.cast_pow] using Int.natCast_modEq_iff.2 (power_period hk hn x)
  have h := forwardDiff_modEq hp j 0
  rw [forwardDiff_power (n + k.totient) j, forwardDiff_power n j] at h
  exact (Int.natCast_modEq_iff.1 h).mul_left (2 ^ j * (2 * j).choose j)

end OMA.S_oeis_a354253

theorem OMA.solution : type_of% @OMA.S_oeis_a354253.main := by
  intro k hk
  refine ⟨k.totient, Nat.totient_pos.2 hk, dvd_refl _, k, ?_⟩
  intro n hn
  have h₁ := OMA.S_oeis_a354253.a_truncate hk (n := n + k.totient) (by omega)
  have h₂ := OMA.S_oeis_a354253.a_truncate hk hn
  have hs := Nat.ModEq.sum (s := Finset.range k)
    (fun j _ => OMA.S_oeis_a354253.summand_period hk hn j)
  exact h₁.trans (hs.trans h₂.symm)

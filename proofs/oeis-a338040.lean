import OMAStatements.S_oeis_a338040

/-!
Proof sketch. By induction on `n`, `j! S(n, j) = Sum_i (-1)^(j+i) C(j, i) i^n`, so every term
`j^n j! S(n, j)` is a combination of the powers `(j i)^n`. By Fermat, `x^(n + p - 1) = x^n mod p`
for every `x` once `n >= 1`. Padding the shorter sum with the vanishing terms `S(n, j) = 0` for
`j > n` gives a termwise congruence.
-/

namespace R338040
open OMA.S_oeis_a338040 Finset

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

theorem core (g : ℕ → ℕ → ℕ) (k n n' : ℕ) (hn : n ≤ n') (h0 : ∀ m j, m < j → g m j = 0)
    (hc : ∀ j, g n' j ≡ g n j [MOD k]) :
    ∑ j ∈ range (n' + 1), g n' j ≡ ∑ j ∈ range (n + 1), g n j [MOD k] := by
  have e : ∑ j ∈ range (n + 1), g n j = ∑ j ∈ range (n' + 1), g n j :=
    sum_subset (Finset.range_subset_range.2 (by omega))
      (fun j _ hj => h0 n j (by simp at hj; omega))
  rw [e]
  exact Nat.ModEq.sum (fun j _ => hc j)

theorem fermat (p x n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) : x ^ (n + (p - 1)) ≡ x ^ n [MOD p] := by
  by_cases hpx : p ∣ x
  · have h1 : p ∣ x ^ n := dvd_pow hpx (by omega)
    have h2 : p ∣ x ^ (n + (p - 1)) := dvd_pow hpx (by omega)
    exact (Nat.modEq_zero_iff_dvd.2 h2).trans (Nat.modEq_zero_iff_dvd.2 h1).symm
  · have hc : Nat.Coprime x p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpx).symm
    have h := Nat.ModEq.pow_totient hc
    rw [Nat.totient_prime hp] at h
    calc x ^ (n + (p - 1)) = x ^ n * x ^ (p - 1) := pow_add _ _ _
      _ ≡ x ^ n * 1 [MOD p] := Nat.ModEq.mul_left _ h
      _ = x ^ n := mul_one _

theorem gen2 (w : ℕ → ℕ) (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    ∑ j ∈ range (n + (p - 1) + 1),
        w j * j ^ (n + (p - 1)) * j.factorial * stirling2 (n + (p - 1)) j ≡
      ∑ j ∈ range (n + 1), w j * j ^ n * j.factorial * stirling2 n j [MOD p] := by
  refine core (fun m j => w j * j ^ m * j.factorial * stirling2 m j) p n _ (by omega)
    (fun m j h => by simp [s_zero m j h]) (fun j => ?_)
  rw [← Int.natCast_modEq_iff]
  simp only [Nat.cast_mul, Nat.cast_pow]
  have e : ∀ m, (w j : ℤ) * (j : ℤ) ^ m * (j.factorial : ℤ) * (stirling2 m j : ℤ) =
      w j * ((j : ℤ) ^ m * E m j) := fun m => by
    rw [← formula]; ring
  rw [e, e]
  refine Int.ModEq.mul_left _ ?_
  unfold E
  rw [mul_sum, mul_sum]
  refine Int.ModEq.sum (fun i _ => ?_)
  have hj := Int.natCast_modEq_iff.2 (fermat p j n hp hn)
  have hi := Int.natCast_modEq_iff.2 (fermat p i n hp hn)
  push_cast at hj hi
  have h3 := (hj.mul hi).mul_left ((-1 : ℤ) ^ (j + i) * (j.choose i : ℤ))
  convert h3 using 1 <;> ring

end R338040

theorem OMA.solution : type_of% @OMA.S_oeis_a338040.main := by
  intro p n hp hn
  exact R338040.gen2 (fun j => 4 ^ j) p n hp hn

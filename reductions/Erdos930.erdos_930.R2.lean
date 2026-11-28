import FormalConjectures.ErdosProblems.«930»

/-!
A perfect power must pass floor-quotient tests at large primes and digit-sum tests
at small primes. Split the remaining endpoint obstruction by prime exponent.
-/

-- Reduction Erdos930.erdos_930.R2 of Erdős Problem 930
-- Credit: @Pixelstorm44

namespace OMA.R_Erdos930_erdos_930_R2

open Finset

/-- Two intervals of lengths seven and four give a square, so even unequal
lengths already force a threshold of at least five for two intervals. -/
theorem two_interval_threshold (k : ℕ)
    (h : ∀ a b : Fin 2 → ℕ, (∀ i, 0 < a i ∧ a i + k ≤ b i + 1) →
      (∀ i j, i < j → b i < a j) →
      ¬ Erdos930.IsPower (∏ i, ∏ m ∈ Icc (a i) (b i), m)) : 5 ≤ k := by
  by_contra! hk
  let a : Fin 2 → ℕ := ![8, 63]
  let b : Fin 2 → ℕ := ![14, 66]
  have hlen (i : Fin 2) : 0 < a i ∧ a i + k ≤ b i + 1 := by
    fin_cases i <;> simp [a, b] <;> omega
  have hord (i j : Fin 2) : i < j → b i < a j := by
    fin_cases i <;> fin_cases j <;> decide
  apply h a b hlen hord
  refine ⟨17297280, 2, by decide, ?_⟩
  decide

private theorem block_ne_zero {a b : ℕ} (ha : 0 < a) : (∏ m ∈ Icc a b, m) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hm => (ha.trans_le (mem_Icc.mp hm).1).ne'

private theorem block_val {a b : ℕ} (ha : 0 < a) (hab : a ≤ b + 1) (p : ℕ) :
    (∏ m ∈ Icc a b, m).factorization p =
      b.factorial.factorization p - (a - 1).factorial.factorization p := by
  have h := prod_Ico_consecutive (fun m : ℕ => m) (show 1 ≤ a by omega) hab
  have hprev : a - 1 + 1 = a := by omega
  have hf : (a - 1).factorial * (∏ m ∈ Icc a b, m) = b.factorial := by
    rw [← prod_Ico_id_eq_factorial, hprev, ← prod_Ico_id_eq_factorial]
    simpa [Ico_add_one_right_eq_Icc] using h
  rw [← hf, Nat.factorization_mul (Nat.factorial_ne_zero _) (block_ne_zero ha)]
  simp

private theorem large_val {p n : ℕ} (hp : p.Prime) (hn : n < p ^ 2) :
    n.factorial.factorization p = n / p := by
  rw [Nat.factorization_factorial hp (Nat.log_lt_of_lt_pow' (by decide : 2 ≠ 0) hn)]
  simp

private theorem total_val {r : ℕ} {a b : Fin r → ℕ}
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i + 1) (p : ℕ) :
    (∏ i, (∏ m ∈ Icc (a i) (b i), m)).factorization p =
      ∑ i, ((b i).factorial.factorization p - (a i - 1).factorial.factorization p) := by
  rw [Nat.factorization_prod_apply (fun i _ => block_ne_zero (ha i))]
  exact sum_congr rfl fun i _ => block_val (ha i) (hab i) p

private theorem endpoint_tests {r q : ℕ} {a b : Fin r → ℕ}
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i + 1)
    (hval : ∀ p, q ∣ (∏ i, ∏ m ∈ Icc (a i) (b i), m).factorization p) :
    (∀ p : ℕ, p.Prime → (∀ i, b i < p ^ 2) →
      q ∣ ∑ i, (b i / p - (a i - 1) / p)) ∧
    (∀ p : ℕ, p.Prime → q * (p - 1) ∣ ∑ i, ((b i - (p.digits (b i)).sum) -
        ((a i - 1) - (p.digits (a i - 1)).sum))) := by
  constructor
  · intro p hp hlarge
    have hd := hval p
    rw [total_val ha hab] at hd
    have heq := sum_congr (s₁ := (univ : Finset (Fin r))) rfl (fun i _ =>
      congrArg₂ (· - ·) (large_val hp (hlarge i))
        (large_val hp (show a i - 1 < p ^ 2 by have := hab i; have := hlarge i; omega)))
    rwa [← heq]
  · intro p hp
    have hd := Nat.mul_dvd_mul_right (hval p) (p - 1)
    rw [total_val ha hab, Finset.sum_mul] at hd
    simp only [mul_comm _ (p - 1)] at hd ⊢
    simpa only [Nat.mul_sub, Nat.sub_one_mul_factorization_factorial hp] using hd

/-- Square exponents surviving the large-prime tests. -/
def H1 : Prop := ∀ r > 0, ∃ k : ℕ, ∀ a b : Fin r → ℕ, (∀ i, 0 < a i ∧ a i + k ≤ b i + 1) →
    (∀ i j, i < j → b i < a j) →
    (∀ p : ℕ, p.Prime → (∀ i, b i < p ^ 2) →
      2 ∣ ∑ i, (b i / p - (a i - 1) / p)) →
    ∃ p : ℕ, p.Prime ∧ (∃ i, p ^ 2 ≤ b i) ∧
      ¬ (2 * (p - 1) ∣ ∑ i, ((b i - (p.digits (b i)).sum) -
        ((a i - 1) - (p.digits (a i - 1)).sum)))

/-- Odd prime exponents require a uniform length threshold. -/
def H2 : Prop := ∀ r > 0, ∃ k : ℕ, ∀ q : ℕ, q.Prime → 2 < q →
  ∀ a b : Fin r → ℕ, (∀ i, 0 < a i ∧ a i + k ≤ b i + 1) →
    (∀ i j, i < j → b i < a j) →
    (∀ p : ℕ, p.Prime → (∀ i, b i < p ^ 2) →
      q ∣ ∑ i, (b i / p - (a i - 1) / p)) →
    ∃ p : ℕ, p.Prime ∧ (∃ i, p ^ 2 ≤ b i) ∧
      ¬ (q * (p - 1) ∣ ∑ i, ((b i - (p.digits (b i)).sum) -
        ((a i - 1) - (p.digits (a i - 1)).sum)))

theorem main : H1 → H2 → type_of% @Erdos930.erdos_930 := by
  intro hs ho r hr
  obtain ⟨ks, hs⟩ := hs r hr
  obtain ⟨ko, ho⟩ := ho r hr
  refine ⟨max ks ko, ?_⟩
  intro a b hlen hord hpower
  obtain ⟨m, l, hl, heq⟩ := hpower
  obtain ⟨q, hq, hdiv⟩ := Nat.exists_prime_and_dvd (show l ≠ 1 by omega)
  have hv (p : ℕ) : q ∣ (∏ i, ∏ m ∈ Icc (a i) (b i), m).factorization p := by
    rw [← heq, Nat.factorization_pow]
    simpa using dvd_mul_of_dvd_left hdiv (m.factorization p)
  have lengths (k : ℕ) (hk : k ≤ max ks ko) (i : Fin r) :
      0 < a i ∧ a i + k ≤ b i + 1 :=
    ⟨(hlen i).1, (Nat.add_le_add_left hk _).trans (hlen i).2⟩
  have ⟨hlarge, hdigits⟩ := endpoint_tests (fun i => (hlen i).1)
    (fun i => show a i ≤ b i + 1 by have := (hlen i).2; omega) hv
  by_cases htwo : q = 2
  · subst q
    obtain ⟨p, hp, _, hbad⟩ := hs a b (lengths ks (le_max_left ..)) hord hlarge
    exact hbad (hdigits p hp)
  · obtain ⟨p, hp, _, hbad⟩ := ho q hq (lt_of_le_of_ne hq.two_le (Ne.symm htwo))
      a b (lengths ko (le_max_right ..)) hord hlarge
    exact hbad (hdigits p hp)

end OMA.R_Erdos930_erdos_930_R2

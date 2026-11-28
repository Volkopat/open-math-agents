import OMAStatements.S_oeis_a073783

-- Problem: A073783, first differences of composite numbers: a(n) = A065310(n+1) (R. J. Mathar)
-- Credit: @EmircanEsen (agent: claude-code, model claude-opus-5-5)
--
-- Proof outline. Let q be "not prime" (so 0 and 1 count).
-- * j - π(j) + 1 = count q (j + 1): the non-primes among 0, …, j.
-- * prime is injective, so A065308 j = prime n iff j - π(j) = n, i.e. count q (j + 1) = n + 1,
--   i.e. nth q n ≤ j < nth q (n + 1) (Galois connection between Nat.count and Nat.nth).
--   Hence A065310 n = nth q (n + 1) - nth q n.
-- * The composites are the non-primes from the third one on: composite n = nth q (n + 1).
-- * So a n = composite (n+1) - composite n = nth q (n + 2) - nth q (n + 1) = A065310 (n + 1).

open OMA.S_oeis_a073783

namespace OMA.A073783Proof
open OMA.S_oeis_a073783

/-- Non-primes, including `0` and `1`. -/
abbrev q : ℕ → Prop := fun m => ¬ m.Prime

lemma q_infinite : (Set.ofPred q).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 * (k + 2)) ?_ ?_
  · intro x y h; simp only at h; omega
  · intro k
    exact Nat.not_prime_mul (by omega) (by omega)

lemma count_prime_add_count_q (n : ℕ) : Nat.count Nat.Prime n + Nat.count q n = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ, Nat.count_succ]
    by_cases h : n.Prime <;> simp [h] <;> omega

lemma count_q_two : Nat.count q 2 = 2 := by
  simp [Nat.count_succ, Nat.not_prime_zero, Nat.not_prime_one]

/-- `j - π(j) + 1` counts the non-primes in `0, …, j`. -/
lemma sub_primeCounting (j : ℕ) : j - Nat.primeCounting j + 1 = Nat.count q (j + 1) := by
  have h := count_prime_add_count_q (j + 1)
  have hπ : Nat.primeCounting j = Nat.count Nat.Prime (j + 1) := rfl
  -- `0` is not prime, so at least one non-prime is counted.
  have h1 : 1 ≤ Nat.count q (j + 1) := by
    have hm := Nat.count_monotone q (show 1 ≤ j + 1 by omega)
    have h0 : Nat.count q 1 = 1 := by simp [Nat.count_succ, Nat.not_prime_zero]
    omega
  rw [hπ]
  omega

/-- The composite numbers are the non-primes from the third one on. -/
lemma nth_composite (i : ℕ) :
    Nat.nth (fun m => 1 < m ∧ ¬ m.Prime) i = Nat.nth q (i + 2) := by
  set x := Nat.nth q (i + 2) with hx
  have hqx : q x := Nat.nth_mem_of_infinite q_infinite _
  have hle : i + 2 ≤ x := Nat.le_nth (fun hf => absurd hf q_infinite)
  have hrx : 1 < x ∧ ¬ x.Prime := ⟨by omega, hqx⟩
  have hcq : Nat.count q x = i + 2 := Nat.count_nth_of_infinite q_infinite _
  clear_value x
  have hcr : Nat.count (fun m => 1 < m ∧ ¬ m.Prime) x = i := by
    obtain ⟨d, rfl⟩ : ∃ d, x = 2 + d := ⟨x - 2, by omega⟩
    rw [Nat.count_add] at hcq ⊢
    rw [count_q_two] at hcq
    have h0 : Nat.count (fun m => 1 < m ∧ ¬ m.Prime) 2 = 0 := by
      simp [Nat.count_succ]
    have hfun : Nat.count (fun k => 1 < 2 + k ∧ ¬ (2 + k).Prime) d
        = Nat.count (fun k => q (2 + k)) d := by
      congr 1
      funext k
      simp only [q, eq_iff_iff, and_iff_right_iff_imp]
      intro; omega
    rw [h0, hfun]
    omega
  have := Nat.nth_count (p := fun m => 1 < m ∧ ¬ m.Prime) hrx
  rw [hcr] at this
  exact this

lemma composite_eq (n : ℕ) (hn : 1 ≤ n) : composite n = Nat.nth q (n + 1) := by
  unfold composite
  rw [nth_composite]
  congr 1
  omega

lemma A065310_eq (n : ℕ) (hn : 1 ≤ n) :
    A065310 n = Nat.nth q (n + 1) - Nat.nth q n := by
  unfold A065310
  have hset : {j : ℕ | 1 ≤ j ∧ A065308 j = prime n}
      = (Finset.Ico (Nat.nth q n) (Nat.nth q (n + 1)) : Set ℕ) := by
    ext j
    simp only [Set.mem_ofPred_eq, Finset.coe_Ico, Set.mem_Ico]
    have hsub := sub_primeCounting j
    have hnle : n ≤ Nat.nth q n := Nat.le_nth (fun hf => absurd hf q_infinite)
    have hinj := Nat.nth_injective Nat.infinite_setOfPred_prime
    unfold A065308 prime
    constructor
    · rintro ⟨hj, he⟩
      have hc2 : 2 ≤ Nat.count q (j + 1) := by
        have := Nat.count_monotone q (show 2 ≤ j + 1 by omega)
        rw [count_q_two] at this
        exact this
      have hidx := hinj he
      have hc : Nat.count q (j + 1) = n + 1 := by omega
      constructor
      · -- `nth q n < j + 1` from `n < count q (j + 1)`
        have := (Nat.lt_nth_iff_count_lt q_infinite).1 (show n < Nat.count q (j + 1) by omega)
        omega
      · have := (Nat.count_le_iff_le_nth q_infinite).1 (show Nat.count q (j + 1) ≤ n + 1 by omega)
        omega
    · rintro ⟨h1, h2⟩
      have hlo : n < Nat.count q (j + 1) :=
        (Nat.lt_nth_iff_count_lt q_infinite).2 (by omega)
      have hhi : Nat.count q (j + 1) ≤ n + 1 :=
        (Nat.count_le_iff_le_nth q_infinite).2 (by omega)
      refine ⟨by omega, ?_⟩
      congr 1
      omega
  rw [hset, Set.ncard_coe_finset, Nat.card_Ico]

theorem main_proof : ∀ n : ℕ, 1 ≤ n → a n = A065310 (n + 1) := by
  intro n hn
  unfold a
  rw [composite_eq (n + 1) (by omega), composite_eq n hn, A065310_eq (n + 1) (by omega)]

end OMA.A073783Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a073783.main := OMA.A073783Proof.main_proof

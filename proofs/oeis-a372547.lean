import OMAStatements.S_oeis_a372547

-- Problem: A372547: Palindromic Zumkeller numbers in base 10.
-- Upstream: formal-conjectures statements/oeis-a372547.lean:0 (declaration OMA.S_oeis_a372547.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: for m coprime to 6, the divisors of 6m that are multiples of 6 are the numbers 6e with
-- e dividing m, with sum 6 sigma(m), while all divisors of 6m sum to sigma(6) sigma(m) =
-- 12 sigma(m); so 6m is Zumkeller. The repunit R(k) is odd, R(k) = k mod 3, and 6 R(k) is
-- 66...6 with k digits. Taking k = 3N + 1 gives infinitely many repdigit terms; a repunit prime
-- is not 3, so it is coprime to 6.

namespace H13A372547

open OMA.S_oeis_a372547

/-- The repunit by recursion. -/
def r : ℕ → ℕ
  | 0 => 0
  | k + 1 => 10 * r k + 1

theorem r_succ (k : ℕ) : r (k + 1) = 10 * r k + 1 := rfl

theorem r_nine (k : ℕ) : 9 * r k + 1 = 10 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [r_succ, pow_succ, ← ih]
    ring

theorem repunit_eq (k : ℕ) : repunit k = r k := by
  unfold repunit
  rw [← r_nine k, Nat.add_sub_cancel, Nat.mul_div_cancel_left (r k) (by norm_num)]

theorem r_mod (k : ℕ) :
    r (k + 1) % 2 = 1 ∧ r (k + 1) % 3 = (k + 1) % 3 ∧ r (k + 1) % 10 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [r_succ (k + 1)]
    omega

theorem r_ge (k : ℕ) : k ≤ r k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    rw [r_succ]
    omega

theorem digits_six (k : ℕ) : Nat.digits 10 (6 * r k) = List.replicate k 6 := by
  induction k with
  | zero => simp [r]
  | succ k ih =>
    have e : 6 * r (k + 1) = 6 + 10 * (6 * r k) := by
      rw [r_succ]
      ring
    rw [e, Nat.digits_add 10 (by norm_num) 6 (6 * r k) (by norm_num) (Or.inl (by norm_num)), ih,
      List.replicate_succ]

theorem cop6 (m : ℕ) (h2 : m % 2 = 1) (h3 : ¬ 3 ∣ m) : Nat.Coprime 6 m := by
  have hm : m % 6 = 1 ∨ m % 6 = 5 := by omega
  show Nat.gcd 6 m = 1
  rw [Nat.gcd_rec]
  rcases hm with hm | hm <;> simp [hm]

theorem zumkeller_six (m : ℕ) (hm : 0 < m) (hc : Nat.Coprime 6 m) : IsZumkeller (6 * m) := by
  have h6 : ∑ d ∈ Nat.divisors 6, d = 12 := by decide
  have hT : ∑ d ∈ (6 * m).divisors, d = 12 * ∑ d ∈ m.divisors, d := by
    rw [Nat.Coprime.sum_divisors_mul hc, h6]
  have himg : (6 * m).divisors.filter (fun d => 6 ∣ d) = m.divisors.image (fun e => 6 * e) := by
    ext x
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨hx, -⟩, ⟨e, rfl⟩⟩
      exact ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left (by norm_num) hx, by omega⟩, rfl⟩
    · rintro ⟨e, ⟨he, -⟩, rfl⟩
      exact ⟨⟨Nat.mul_dvd_mul_left 6 he, by omega⟩, ⟨e, rfl⟩⟩
  have hinj : Set.InjOn (fun e : ℕ => 6 * e) ↑m.divisors :=
    fun x _ y _ h => Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hA : ∑ d ∈ (6 * m).divisors.filter (fun d => 6 ∣ d), d = 6 * ∑ d ∈ m.divisors, d := by
    rw [himg, Finset.sum_image hinj, Finset.mul_sum]
  have hS : ∑ d ∈ (6 * m).divisors \ (6 * m).divisors.filter (fun d => 6 ∣ d), d +
      ∑ d ∈ (6 * m).divisors.filter (fun d => 6 ∣ d), d = ∑ d ∈ (6 * m).divisors, d :=
    Finset.sum_sdiff (Finset.filter_subset ..)
  refine ⟨(6 * m).divisors.filter (fun d => 6 ∣ d), Finset.filter_subset .., ?_⟩
  omega

theorem mem6 (k : ℕ) (hc : Nat.Coprime 6 (r (k + 1))) :
    6 * r (k + 1) ∈ A372547 ∧ IsRepdigit (6 * r (k + 1)) := by
  have hpos : 0 < r (k + 1) := by
    rw [r_succ]
    omega
  have hd := digits_six (k + 1)
  refine ⟨⟨by omega, ?_, zumkeller_six (r (k + 1)) hpos hc⟩, ⟨6, fun x hx => ?_⟩⟩
  · unfold IsPalindrome
    rw [hd]
    simp
  · rw [hd] at hx
    exact List.eq_of_mem_replicate hx

end H13A372547

open OMA.S_oeis_a372547 H13A372547 in
theorem OMA.solution : type_of% @OMA.S_oeis_a372547.main := by
  refine ⟨?_, ?_⟩
  · intro k hp
    rw [repunit_eq] at hp ⊢
    rcases k with _ | j
    · exact absurd hp Nat.not_prime_zero
    · have h3 : ¬ 3 ∣ r (j + 1) := by
        intro h
        rcases hp.eq_one_or_self_of_dvd 3 h with h1 | h1
        · omega
        · have := (r_mod j).2.2
          omega
      rw [show 2 * 3 * r (j + 1) = 6 * r (j + 1) by ring]
      exact mem6 j (cop6 (r (j + 1)) (r_mod j).1 h3)
  · apply Set.infinite_of_forall_exists_gt
    intro N
    have h3 : ¬ 3 ∣ r (3 * N + 1) := by
      have := (r_mod (3 * N)).2.1
      omega
    refine ⟨6 * r (3 * N + 1), mem6 (3 * N) (cop6 _ (r_mod (3 * N)).1 h3), ?_⟩
    have := r_ge (3 * N + 1)
    omega

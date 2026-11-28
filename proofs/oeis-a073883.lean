import OMAStatements.S_oeis_a073883

/-!
The first four terms are 1, 3, 2, 6. From then on the partial sum exceeds
twice its length: 1 and 2 have already been used, so each subsequent term
adds at least 3. The prime average is therefore odd. Consecutive partial
sums alternate in parity, so every term from the fifth onward is odd.
-/

namespace PrimeAverages

open OMA.S_oeis_a073883 Finset

private noncomputable def total (n : ℕ) := ∑ i : Fin n, a (i.val+1)

private theorem total_succ (n : ℕ) : total (n+1) = total n + a (n+1) := by
  unfold total
  rw [Fin.sum_univ_castSucc]
  rfl

private def allowed (n m : ℕ) : Prop :=
  0 < m ∧ (∀ i : Fin (n+1), a (i.val+1) ≠ m) ∧
    ∃ p : ℕ, p.Prime ∧ total (n+1) + m = (n+2)*p

private theorem chosen (n : ℕ) : allowed n (a (n+2)) := by
  rw [a]
  apply Nat.sInf_mem (s := {m | allowed n m})
  let s := total (n+1)
  obtain ⟨p, large, prime⟩ := Nat.exists_infinite_primes (s+1)
  have prod : 2*p ≤ (n+2)*p := Nat.mul_le_mul_right p (by omega)
  refine ⟨(n+2)*p-s, by omega, ?_, p, prime, ?_⟩
  · intro i
    have h : a (i.val+1) ≤ s :=
      single_le_sum (f := fun i : Fin (n+1) => a (i.val+1)) (fun _ _ => Nat.zero_le _) (mem_univ i)
    omega
  · change s + ((n+2)*p-s) = (n+2)*p
    omega

private theorem least {n m : ℕ} (hm : allowed n m) : a (n+2) ≤ m := by
  rw [a]
  exact Nat.sInf_le hm

private theorem first : a 1 = 1 := by rw [a]
private theorem sum1 : total 1 = 1 := by simp [total, first]

private theorem second : a 2 = 3 := by
  have c : allowed 0 3 := by
    refine ⟨by decide, ?_, 2, Nat.prime_two, ?_⟩
    · intro i; fin_cases i <;> norm_num [first]
    · norm_num [sum1]
  have hi := least c
  obtain ⟨pos, fresh, p, _, eq⟩ := chosen 0
  change a 2 ≤ 3 at hi
  change 0 < a 2 at pos
  have ne := fresh 0
  change a 1 ≠ a 2 at ne
  rw [first] at ne
  change total 1 + a 2 = 2*p at eq
  rw [sum1] at eq
  omega

private theorem sum2 : total 2 = 4 := by rw [total_succ 1, sum1, second]

private theorem third : a 3 = 2 := by
  have c : allowed 1 2 := by
    refine ⟨by decide, ?_, 2, Nat.prime_two, ?_⟩
    · intro i; fin_cases i <;> norm_num [first, second]
    · norm_num [sum2]
  have hi := least c
  obtain ⟨pos, fresh, _⟩ := chosen 1
  change a 3 ≤ 2 at hi
  change 0 < a 3 at pos
  have ne := fresh 0
  change a 1 ≠ a 3 at ne
  rw [first] at ne
  omega

private theorem sum3 : total 3 = 6 := by rw [total_succ 2, sum2, third]

private theorem fourth : a 4 = 6 := by
  have c : allowed 2 6 := by
    refine ⟨by decide, ?_, 3, by decide, ?_⟩
    · intro i; fin_cases i <;> norm_num [first, second, third]
    · norm_num [sum3]
  have hi := least c
  obtain ⟨pos, fresh, p, _, eq⟩ := chosen 2
  change a 4 ≤ 6 at hi
  change 0 < a 4 at pos
  have ne := fresh 2
  change a 3 ≠ a 4 at ne
  rw [third] at ne
  change total 3 + a 4 = 4*p at eq
  rw [sum3] at eq
  omega

private theorem large_term (j : ℕ) : 3 ≤ a (j+5) := by
  obtain ⟨pos, fresh, _⟩ := chosen (j+3)
  change 0 < a (j+5) at pos
  have h₁ := fresh ⟨0, by omega⟩
  have h₂ := fresh ⟨2, by omega⟩
  change a 1 ≠ a (j+5) at h₁
  change a 3 ≠ a (j+5) at h₂
  rw [first] at h₁
  rw [third] at h₂
  omega

private theorem above_two (j : ℕ) : 2*(j+4) < total (j+4) := by
  induction j with
  | zero => norm_num [total_succ 3, sum3, fourth]
  | succ j ih =>
    rw [show j+1+4 = (j+4)+1 by omega, total_succ]
    have h := large_term j
    change 2*(j+4+1) < total (j+4) + a (j+5)
    omega

private theorem sum_parity (j : ℕ) : total (j+4) % 2 = (j+4) % 2 := by
  obtain ⟨_, _, p, hp, eq⟩ := chosen (j+2)
  have h : total (j+4) = (j+4)*p := (total_succ (j+3)).trans eq
  have p_ne : p ≠ 2 := by
    intro e
    have huge := above_two j
    rw [h, e] at huge
    omega
  have odd := Nat.odd_iff.mp (hp.odd_of_ne_two p_ne)
  rw [h, Nat.mul_mod, odd, mul_one, Nat.mod_mod]

theorem odd_from_five (j : ℕ) : a (j+5) % 2 = 1 := by
  have h := sum_parity j
  have h' := sum_parity (j+1)
  rw [show j+1+4=(j+4)+1 by omega, total_succ] at h'
  change (total (j+4) + a (j+5)) % 2 = (j+5) % 2 at h'
  omega

theorem four_is_missing (n : ℕ) (hn : 0 < n) : a n ≠ 4 := by
  by_cases h : n < 5
  · interval_cases n <;> norm_num [first, second, third, fourth]
  · have odd := odd_from_five (n-5)
    rw [show n-5+5=n by omega] at odd
    omega

end PrimeAverages

theorem OMA.solution : type_of% @OMA.S_oeis_a073883.main :=
  ⟨4, by decide, PrimeAverages.four_is_missing⟩

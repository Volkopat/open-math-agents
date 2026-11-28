import OMAStatements.S_oeis_a160108

namespace OMA.S_oeis_a160108

open Finset


/-- F(n) mod 8. -/
def r (n : ℕ) : ℕ := Nat.fib n % 8

/-- The number of earlier indices with the same residue. -/
def cnt (n : ℕ) : ℕ := ((range n).filter (fun j => r j = r n)).card

/-- The number of indices below 12 with residue ρ. -/
def cper (ρ : ℕ) : ℕ := ((range 12).filter (fun j => r j = ρ)).card

lemma r_lt (n : ℕ) : r n < 8 := Nat.mod_lt _ (by norm_num)

lemma a_eq (n : ℕ) : a n = sInf {k | k % 8 = r n ∧ ∀ j : Fin n, a j ≠ k} := by
  rw [a]; rfl

lemma cnt_lt {j n : ℕ} (hj : j < n) (hr : r j = r n) : cnt j < cnt n := by
  unfold cnt
  rw [hr]
  apply card_lt_card
  rw [ssubset_iff_of_subset]
  · exact ⟨j, by simp [hj, hr], by simp⟩
  · intro i hi
    simp only [mem_filter, mem_range] at hi ⊢
    exact ⟨by omega, hi.2⟩

lemma exists_cnt (n t : ℕ) (ht : t < cnt n) : ∃ j, j < n ∧ r j = r n ∧ cnt j = t := by
  have key := surj_on_of_inj_on_of_card_le (s := (range n).filter (fun j => r j = r n))
    (t := range (cnt n)) (fun j _ => cnt j)
    (fun j hj => by
      simp only [mem_filter, mem_range] at hj
      exact mem_range.mpr (cnt_lt hj.1 hj.2))
    (fun j1 j2 h1 h2 he => by
      simp only [mem_filter, mem_range] at h1 h2
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have := cnt_lt hlt (h1.2.trans h2.2.symm); omega
      · have := cnt_lt hlt (h2.2.trans h1.2.symm); omega)
    (by simp [cnt])
  obtain ⟨j, hj, he⟩ := key t (mem_range.mpr ht)
  simp only [mem_filter, mem_range] at hj
  exact ⟨j, hj.1, hj.2, he.symm⟩

lemma closed (n : ℕ) : a n = r n + 8 * cnt n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hmem : r n + 8 * cnt n ∈ {k | k % 8 = r n ∧ ∀ j : Fin n, a j ≠ k} := by
      refine ⟨by have := r_lt n; omega, fun j => ?_⟩
      rw [ih j j.isLt]
      by_cases h : r j = r n
      · have := cnt_lt j.isLt h; omega
      · have := r_lt j; have := r_lt n; omega
    rw [a_eq]
    apply le_antisymm (Nat.sInf_le hmem)
    apply le_csInf ⟨_, hmem⟩
    rintro k ⟨hk1, hk2⟩
    by_contra hlt
    push_neg at hlt
    have hk : k = r n + 8 * (k / 8) := by have := r_lt n; omega
    obtain ⟨j, hjn, hjr, hjc⟩ := exists_cnt n (k / 8) (by omega)
    exact hk2 ⟨j, hjn⟩ (by rw [ih j hjn, hjr, hjc]; omega)

lemma fib_mod (n : ℕ) : Nat.fib (n + 12) % 8 = Nat.fib n % 8 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | n + 2 =>
      rw [show n + 2 + 12 = (n + 12) + 2 by ring, @Nat.fib_add_two (n + 12), @Nat.fib_add_two n,
        Nat.add_mod, ih n (by omega), show n + 12 + 1 = (n + 1) + 12 by ring,
        ih (n + 1) (by omega), ← Nat.add_mod]

lemma r_add12 (n : ℕ) : r (n + 12) = r n := fib_mod n

lemma cnt_add12 (n : ℕ) : cnt (n + 12) = cnt n + cper (r n) := by
  unfold cnt cper
  rw [card_filter, card_filter, card_filter, show n + 12 = 12 + n by ring, sum_range_add,
    show 12 + n = n + 12 by ring, r_add12]
  rw [add_comm]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [show 12 + j = j + 12 by ring, r_add12]

lemma r_period (q s : ℕ) : r (12 * q + s) = r s := by
  induction q with
  | zero => simp
  | succ q ih => rw [show 12 * (q + 1) + s = (12 * q + s) + 12 by ring, r_add12, ih]

lemma cnt_period (q s : ℕ) : cnt (12 * q + s) = cnt s + q * cper (r s) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 12 * (q + 1) + s = (12 * q + s) + 12 by ring, cnt_add12, ih, r_period]
    ring

lemma a_period (q s : ℕ) : (a (12 * q + s) : ℤ) = (r s + 8 * cnt s : ℕ) + q * (8 * cper (r s) : ℕ) := by
  rw [closed, r_period, cnt_period]
  push_cast
  ring

/-- The twelve identities between the constants. -/
lemma table : ∀ s, s < 6 → cper (r (s + 6)) = cper (r s) ∧
    2 * (r (s + 6) + 8 * cnt (s + 6)) = 2 * (r s + 8 * cnt s) + 8 * cper (r s) := by
  decide

/-- Barker's conjecture: a(n) = 2 a(n-6) - a(n-12) for every n >= 12. -/
theorem recurrence : ∀ n : ℕ, 12 ≤ n → (a n : ℤ) = 2 * a (n - 6) - a (n - 12) := by
  intro n hn
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < 12 ∧ n = 12 * (q + 1) + s :=
    ⟨n / 12 - 1, n % 12, Nat.mod_lt _ (by norm_num), by omega⟩
  rcases Nat.lt_or_ge s 6 with h6 | h6
  · -- n - 6 = 12 q + (s + 6), n - 12 = 12 q + s
    obtain ⟨t1, t2⟩ := table s h6
    rw [show 12 * (q + 1) + s - 6 = 12 * q + (s + 6) by omega,
      show 12 * (q + 1) + s - 12 = 12 * q + s by omega, a_period, a_period, a_period, t1]
    have t2' : (2 * (r (s + 6) + 8 * cnt (s + 6)) : ℤ) = 2 * (r s + 8 * cnt s) + 8 * cper (r s) := by
      exact_mod_cast t2
    push_cast at t2' ⊢
    linear_combination (-1 : ℤ) * t2'
  · -- n - 6 = 12 (q + 1) + (s - 6), n - 12 = 12 q + s
    obtain ⟨u, rfl⟩ : ∃ u, s = u + 6 := ⟨s - 6, by omega⟩
    obtain ⟨t1, t2⟩ := table u (by omega)
    rw [show 12 * (q + 1) + (u + 6) - 6 = 12 * (q + 1) + u by omega,
      show 12 * (q + 1) + (u + 6) - 12 = 12 * q + (u + 6) by omega, a_period, a_period, a_period,
      t1]
    have t2' : (2 * (r (u + 6) + 8 * cnt (u + 6)) : ℤ) = 2 * (r u + 8 * cnt u) + 8 * cper (r u) := by
      exact_mod_cast t2
    push_cast at t2' ⊢
    linear_combination t2'

/-- Controls from the entry: a(0..14) = 0, 1, 9, 2, 3, 5, 8, 13, 21, 10, 7, 17, 16, 25, 33. -/
example : (List.range 15).map (fun n => r n + 8 * cnt n) =
    [0, 1, 9, 2, 3, 5, 8, 13, 21, 10, 7, 17, 16, 25, 33] := by
  decide

end OMA.S_oeis_a160108

theorem OMA.solution : type_of% @OMA.S_oeis_a160108.main :=
  OMA.S_oeis_a160108.recurrence

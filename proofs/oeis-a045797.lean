import OMAStatements.S_oeis_a045797

/-!
# A045797: the linear recurrence for the evenish numbers

An evenish number is a positive integer prime to 10 whose tens digit is even.  Writing
`k = 10 q + r` with `r ∈ {1,3,7,9}` (the residues prime to 10) and `q` even, the set of evenish
numbers is exactly `{20 m + 1, 20 m + 3, 20 m + 7, 20 m + 9 : m ∈ ℕ}`: four numbers in every block of
twenty.  Hence `evenish` is invariant under `n ↦ n + 20`, every block of twenty contains four
evenish numbers, and the enumeration `a` satisfies `a (n + 4) = a n + 20`.  Subtracting this identity
at `n` and at `n - 1` gives the claimed recurrence.
-/

namespace OMA.S_oeis_a045797

instance : DecidablePred evenish := fun k =>
  decidable_of_iff (k.gcd 10 = 1 ∧ (k / 10 % 10) % 2 = 0) (by
    unfold evenish
    rw [Nat.coprime_iff_gcd_eq_one])

/-- The property defining an evenish number depends only on `k` modulo `20`. -/
lemma evenish_add_20 (n : ℕ) : evenish (n + 20) ↔ evenish n := by
  have hcop : Nat.Coprime (n + 20) 10 ↔ Nat.Coprime n 10 :=
    Nat.add_coprime_iff_left (a := n) (b := 20) (c := 10) (by norm_num)
  have htens : ((n + 20) / 10 % 10) % 2 = (n / 10 % 10) % 2 := by
    have hd : (n + 20) / 10 = n / 10 + 2 := by omega
    rw [hd]
    omega
  unfold evenish
  rw [hcop, htens]

/-- The first block of twenty contains exactly the four evenish numbers `1, 3, 7, 9`. -/
lemma count_twenty : Nat.count evenish 20 = 4 := by decide

/-- Every block of twenty consecutive integers contains exactly four evenish numbers. -/
lemma count_add_20 (u : ℕ) : Nat.count evenish (u + 20) = Nat.count evenish u + 4 := by
  induction u with
  | zero => simpa using count_twenty
  | succ u ih =>
    have hif : (if evenish (u + 20) then 1 else 0) = (if evenish u then 1 else 0) := by
      by_cases h : evenish u
      · rw [if_pos h, if_pos ((evenish_add_20 u).mpr h)]
      · rw [if_neg h, if_neg (fun hp => h ((evenish_add_20 u).mp hp))]
    rw [show u + 1 + 20 = (u + 20) + 1 by omega, Nat.count_succ, ih, Nat.count_succ, hif]
    omega

lemma evenish_twenty_mul_add_one (m : ℕ) : evenish (20 * m + 1) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h : 20 * (m + 1) + 1 = (20 * m + 1) + 20 := by ring
    rw [h]
    exact (evenish_add_20 (20 * m + 1)).mpr ih

lemma evenish_infinite : (Set.ofPred evenish).Infinite := by
  have hinj : Function.Injective (fun m : ℕ => 20 * m + 1) := by
    intro x y h
    simp only at h
    omega
  exact Set.infinite_of_injective_forall_mem hinj (fun m => evenish_twenty_mul_add_one m)

/-- The enumeration advances by `20` every four steps. -/
lemma nth_add_four (k : ℕ) : Nat.nth evenish (k + 4) = Nat.nth evenish k + 20 := by
  have hu : evenish (Nat.nth evenish k) := Nat.nth_mem_of_infinite evenish_infinite k
  have hcnt : Nat.count evenish (Nat.nth evenish k) = k :=
    Nat.count_nth_of_infinite evenish_infinite k
  have hu20 : evenish (Nat.nth evenish k + 20) := (evenish_add_20 (Nat.nth evenish k)).mpr hu
  have hthis := Nat.nth_count (p := evenish) hu20
  rw [count_add_20, hcnt] at hthis
  exact hthis

lemma a_add_four {n : ℕ} (hn : 1 ≤ n) : a (n + 4) = a n + 20 := by
  have hidx : n + 4 - 1 = (n - 1) + 4 := by omega
  unfold a
  rw [hidx, nth_add_four]

end OMA.S_oeis_a045797

open OMA.S_oeis_a045797 in
theorem OMA.solution : type_of% @OMA.S_oeis_a045797.main := by
  intro n hn
  have h1 : a n = a (n - 4) + 20 := by
    have h := a_add_four (n := n - 4) (by omega)
    rwa [show n - 4 + 4 = n by omega] at h
  have h2 : a (n - 1) = a (n - 5) + 20 := by
    have h := a_add_four (n := n - 5) (by omega)
    rwa [show n - 5 + 4 = n - 1 by omega] at h
  have c1 : (a n : ℤ) = (a (n - 4) : ℤ) + 20 := by
    rw [h1]
    push_cast
    ring
  have c2 : (a (n - 1) : ℤ) = (a (n - 5) : ℤ) + 20 := by
    rw [h2]
    push_cast
    ring
  omega

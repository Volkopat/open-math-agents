import OMAStatements.S_oeis_a029858
import Mathlib

/-!
# A029858: Wajnberg's digit count

Let T(k) be the numbers below 10^k (0 included) whose decimal digits all lie in {7, 8, 9}. A
nonzero m is in T(k+1) exactly when m = 10q + d with d ∈ {7, 8, 9} and q ∈ T(k), so
T(k+1) = {0} ∪ {10q + d}, a disjoint union, and 2|T(k)| + 1 = 3^(k+1) by induction. Removing 0
leaves (3^(k+1) − 3)/2 numbers.
-/

namespace PA029858

/-- Numbers below `10^k` (including 0) whose decimal digits all lie in {7, 8, 9}. -/
def T (k : ℕ) : Finset ℕ :=
  (Finset.range (10 ^ k)).filter (fun m => ∀ d ∈ Nat.digits 10 m, d ∉ Finset.range 7)

theorem digits_step (q d : ℕ) (hd : d < 10) (h7 : 7 ≤ d) :
    Nat.digits 10 (10 * q + d) = d :: Nat.digits 10 q := by
  rw [Nat.digits_def' (by norm_num) (by omega)]
  congr 1
  · omega
  · congr 1; omega

theorem T_succ (k : ℕ) :
    T (k + 1) = insert 0 ((T k ×ˢ ({7, 8, 9} : Finset ℕ)).image (fun p => 10 * p.1 + p.2)) := by
  ext m
  simp only [T, Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_image,
    Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨hlt, hg⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · left; rfl
    · right
      have hdig := Nat.digits_def' (show 1 < 10 by norm_num) hm
      have hhead : ¬ m % 10 < 7 := hg _ (by rw [hdig]; exact List.mem_cons_self ..)
      refine ⟨m / 10, m % 10, ⟨⟨?_, fun d hd => hg d (by rw [hdig]; exact List.mem_cons_of_mem _ hd)⟩, ?_⟩, ?_⟩
      · rw [pow_succ] at hlt; omega
      · simp only [Finset.mem_singleton]; omega
      · omega
  · rintro (rfl | ⟨q, d, ⟨⟨hq, hg⟩, hd⟩, rfl⟩)
    · exact ⟨by positivity, by simp⟩
    · simp only [Finset.mem_singleton] at hd
      have hd10 : d < 10 := by omega
      have hd7 : 7 ≤ d := by omega
      refine ⟨?_, ?_⟩
      · rw [pow_succ]; omega
      · rw [digits_step q d hd10 hd7]
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · omega
        · exact hg e he

theorem card_T (k : ℕ) : 2 * (T k).card + 1 = 3 ^ (k + 1) := by
  induction k with
  | zero =>
    have : T 0 = {0} := by
      ext m
      simp only [T, pow_zero, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨h, -⟩; omega
      · rintro rfl; simp
    rw [this]; simp
  | succ k ih =>
    rw [T_succ, Finset.card_insert_of_notMem, Finset.card_image_of_injOn, Finset.card_product]
    · have h3 : ({7, 8, 9} : Finset ℕ).card = 3 := by rfl
      rw [h3, pow_succ]
      omega
    · rintro ⟨q, d⟩ hp ⟨q', d'⟩ hp' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_insert,
        Finset.mem_singleton] at hp hp'
      simp only at h
      have : d = d' := by omega
      subst this
      have : q = q' := by omega
      subst this
      rfl
    · simp only [Finset.mem_image, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
        Prod.exists, not_exists, not_and]
      intro q d _ hd
      omega

end PA029858

theorem OMA.solution : type_of% @OMA.S_oeis_a029858.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega]
  have hset : (Finset.range (10 ^ k)).filter
      (fun m => m ≠ 0 ∧ ∀ d ∈ Nat.digits 10 m, d ∉ Finset.range 7) = (PA029858.T k).erase 0 := by
    ext m
    simp only [PA029858.T, Finset.mem_filter, Finset.mem_erase]
    tauto
  have h0 : 0 ∈ PA029858.T k := by
    simp only [PA029858.T, Finset.mem_filter, Finset.mem_range]
    exact ⟨by positivity, by simp⟩
  rw [hset, Finset.card_erase_of_mem h0]
  have hc := PA029858.card_T k
  unfold OMA.S_oeis_a029858.a
  omega

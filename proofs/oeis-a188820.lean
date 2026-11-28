import OMAStatements.S_oeis_a188820
import Mathlib

open OMA.S_oeis_a188820

namespace OMA.P_oeis_a188820

def adv (v : List ℤ) : List ℤ :=
  (List.range 32).map (fun u => ∑ w ∈ allowed u, v.getD w 0)

def cv : ℕ → List ℤ
  | 0 => (List.range 32).map (fun _ => 1)
  | n + 1 => adv (cv n)

theorem getD_rng (f : ℕ → ℤ) (u : ℕ) (hu : u < 32) : ((List.range 32).map f).getD u 0 = f u := by
  rw [List.getD_eq_getElem _ _ (by simpa using hu)]
  simp

theorem mem_allowed {u v : ℕ} (h : v ∈ allowed u) : v < 32 := by
  unfold allowed at h
  rw [Finset.mem_filter, Finset.mem_range] at h
  exact h.1

theorem comp_eq : ∀ n, ∀ u < 32, continuations n u = (cv n).getD u 0
  | 0, u, hu => by rw [cv, getD_rng _ u hu]; rfl
  | n + 1, u, hu => by
    rw [cv, adv, getD_rng _ u hu]
    show ∑ v ∈ allowed u, continuations n v = _
    apply Finset.sum_congr rfl
    intro v hv
    exact comp_eq n v (mem_allowed hv)

def baseOK : Bool :=
  (List.range 32).all (fun u => (cv 6).getD u 0 ==
    2 * (cv 5).getD u 0 - 2 * (cv 3).getD u 0 + (cv 2).getD u 0)

set_option maxHeartbeats 400000000 in
theorem base_ok : baseOK = true := by decide +kernel

theorem rec_all : ∀ k, ∀ u < 32, continuations (k + 6) u =
    2 * continuations (k + 5) u - 2 * continuations (k + 3) u + continuations (k + 2) u := by
  intro k
  induction k with
  | zero =>
    intro u hu
    have h := List.all_eq_true.mp base_ok u (by simpa using hu)
    rw [comp_eq 6 u hu, comp_eq 5 u hu, comp_eq 3 u hu, comp_eq 2 u hu]
    simpa using h
  | succ k ih =>
    intro u hu
    show ∑ v ∈ allowed u, continuations (k + 6) v = 2 * ∑ v ∈ allowed u, continuations (k + 5) v
      - 2 * ∑ v ∈ allowed u, continuations (k + 3) v + ∑ v ∈ allowed u, continuations (k + 2) v
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    exact ih v (mem_allowed hv)

def g (n : ℕ) : ℤ := 64 * (n : ℤ) ^ 2 - 48 * n + (if n % 2 = 0 then 9 else 0)

theorem cf : ∀ n, 2 ≤ n → continuations n 31 = g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 6 with h6 | h6
    · rw [comp_eq n 31 (by norm_num)]
      interval_cases n <;> decide +kernel
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      rw [rec_all k 31 (by norm_num), ih (k + 5) (by omega) (by omega),
        ih (k + 3) (by omega) (by omega), ih (k + 2) (by omega) (by omega)]
      unfold g
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [show (j + j + 6) % 2 = 0 by omega, show (j + j + 5) % 2 = 1 by omega,
          show (j + j + 3) % 2 = 1 by omega, show (j + j + 2) % 2 = 0 by omega]
        push_cast; simp; ring
      · rw [show (2 * j + 1 + 6) % 2 = 1 by omega, show (2 * j + 1 + 5) % 2 = 0 by omega,
          show (2 * j + 1 + 3) % 2 = 0 by omega, show (2 * j + 1 + 2) % 2 = 1 by omega]
        push_cast; simp; ring

end OMA.P_oeis_a188820

open OMA.P_oeis_a188820 in
set_option maxHeartbeats 400000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a188820.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn he
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain ⟨j, rfl⟩ := he; omega
    · have := cf n h2
      unfold g at this
      rw [if_pos (Nat.even_iff.mp he)] at this
      unfold arrays
      rw [if_neg (by omega), this]; ring
  · intro n hn ho
    have := cf n (by omega)
    unfold g at this
    rw [if_neg (by rw [Nat.odd_iff] at ho; omega)] at this
    unfold arrays
    rw [if_neg (by omega), this]; ring
  · intro n
    rcases Nat.lt_or_ge n 6 with h6 | h6
    · unfold arrays delayed numerator
      interval_cases n <;> simp only [comp_eq _ 31 (by norm_num)] <;> decide +kernel
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      have hr := rec_all k 31 (by norm_num)
      unfold delayed numerator
      simp only [arrays, show 1 ≤ k + 6 by omega, show 3 ≤ k + 6 by omega, show 4 ≤ k + 6 by omega,
        if_true, show k + 6 - 1 = k + 5 by omega, show k + 6 - 3 = k + 3 by omega,
        show k + 6 - 4 = k + 2 by omega, show k + 6 ≠ 0 by omega, show k + 5 ≠ 0 by omega,
        show k + 3 ≠ 0 by omega, show k + 2 ≠ 0 by omega, if_false,
        show k + 6 ≠ 1 by omega, show k + 6 ≠ 2 by omega, show k + 6 ≠ 3 by omega,
        show k + 6 ≠ 4 by omega, show k + 6 ≠ 5 by omega]
      linarith

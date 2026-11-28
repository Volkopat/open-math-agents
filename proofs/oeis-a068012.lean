import OMAStatements.S_oeis_a068012
import Mathlib

-- Proof of David A. Corneth's conjecture in OEIS A068012 (statement by @ivillar).
-- Idea: let N(r,n) count the subsets of {1..n} with sum ≡ r (mod 6); splitting on whether n+1 is in
-- the subset gives N(r,n+1) = N(r,n) + N(r-n-1,n). By induction (base n = 3, 4, 5 by computation),
-- for q ≥ 1: 6N(r,3q) = 8^q + c0(r)2^q, 6N(r,3q+1) = 2*8^q + c1(r)2^q, 6N(r,3q+2) = 4*8^q + c0(r)2^q,
-- with c0, c1 depending on r mod 3 (the roots-of-unity filter); both identities follow.

namespace OMAA068012Helpers

open OMA.S_oeis_a068012

def N (r n : ℕ) : ℕ := ((Finset.Icc 1 n).powerset.filter (fun S => (∑ i ∈ S, i) % 6 = r)).card

theorem N_succ (r n : ℕ) (hr : r < 6) :
    N r (n + 1) = N r n + N ((r + 6 - (n + 1) % 6) % 6) n := by
  unfold N
  have hins : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
  rw [hins, Finset.powerset_insert, Finset.filter_union, Finset.card_union_of_disjoint]
  · congr 1
    rw [Finset.filter_image, Finset.card_image_of_injOn]
    · congr 1
      apply Finset.filter_congr
      intro S hS
      rw [Finset.mem_powerset] at hS
      have hS' : n + 1 ∉ S := fun h => hnot (hS h)
      simp only [Finset.sum_insert hS']
      omega
    · intro S hS T hT hST
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_powerset] at hS hT
      have h1 : n + 1 ∉ S := fun h => hnot (hS.1 h)
      have h2 : n + 1 ∉ T := fun h => hnot (hT.1 h)
      have := congrArg (fun U => U.erase (n + 1)) hST
      simpa [Finset.erase_insert h1, Finset.erase_insert h2] using this
  · rw [Finset.disjoint_left]
    intro S hS hS'
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image] at hS hS'
    obtain ⟨T, -, rfl⟩ := hS'.1
    exact hnot (hS.1 (Finset.mem_insert_self _ _))

def c0 (r : ℕ) : ℤ := if r % 3 = 0 then 2 else -1
def c1 (r : ℕ) : ℤ := if r % 3 = 2 then -2 else 1

theorem base : ∀ r, r < 6 → (6 * (N r 3 : ℤ) = 2 ^ 3 + c0 r * 2 ^ 1) ∧
    (6 * (N r 4 : ℤ) = 2 ^ 4 + c1 r * 2 ^ 1) ∧ (6 * (N r 5 : ℤ) = 2 ^ 5 + c0 r * 2 ^ 1) := by
  intro r hr
  have h3 : N 0 3 = 2 ∧ N 1 3 = 1 ∧ N 2 3 = 1 ∧ N 3 3 = 2 ∧ N 4 3 = 1 ∧ N 5 3 = 1 := by decide
  have h4 : N 0 4 = 3 ∧ N 1 4 = 3 ∧ N 2 4 = 2 ∧ N 3 4 = 3 ∧ N 4 4 = 3 ∧ N 5 4 = 2 := by decide
  have h5 : N 0 5 = 6 ∧ N 1 5 = 5 ∧ N 2 5 = 5 ∧ N 3 5 = 6 ∧ N 4 5 = 5 ∧ N 5 5 = 5 := by decide
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h3
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := h4
  obtain ⟨d0, d1, d2, d3, d4, d5⟩ := h5
  interval_cases r <;> simp [c0, c1, a0, a1, a2, a3, a4, a5, b0, b1, b2, b3, b4, b5, d0, d1, d2, d3, d4, d5]

theorem idx_lt (r m : ℕ) : (r + 6 - m % 6) % 6 < 6 := Nat.mod_lt _ (by norm_num)

theorem c0_idx (r m : ℕ) (hr : r < 6) (h : (r + 6 - m % 6) % 6 % 3 = r % 3) :
    c0 ((r + 6 - m % 6) % 6) = c0 r := by unfold c0; rw [h]

theorem CF : ∀ q, 1 ≤ q → ∀ r, r < 6 → (6 * (N r (3 * q) : ℤ) = 2 ^ (3 * q) + c0 r * 2 ^ q) ∧
    (6 * (N r (3 * q + 1) : ℤ) = 2 ^ (3 * q + 1) + c1 r * 2 ^ q) ∧
    (6 * (N r (3 * q + 2) : ℤ) = 2 ^ (3 * q + 2) + c0 r * 2 ^ q) := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => exact base
  | succ q hq ih =>
    have step : ∀ r n, r < 6 → (N r (n + 1) : ℤ) = N r n + N ((r + 6 - (n + 1) % 6) % 6) n := by
      intro r n hr; rw [N_succ r n hr]; push_cast; ring
    have A : ∀ r, r < 6 → 6 * (N r (3 * (q + 1)) : ℤ) = 2 ^ (3 * (q + 1)) + c0 r * 2 ^ (q + 1) := by
      intro r hr
      rw [show 3 * (q + 1) = 3 * q + 2 + 1 by ring, step r _ hr]
      have i1 := (ih r hr).2.2
      set j := (r + 6 - (3 * q + 2 + 1) % 6) % 6 with hj
      have hj6 : j < 6 := idx_lt _ _
      have i2 := (ih j hj6).2.2
      have hc : c0 j = c0 r := by
        unfold c0; rw [show j % 3 = r % 3 by omega]
      rw [hc] at i2
      rw [pow_succ (2 : ℤ) (3 * q + 2), pow_succ (2 : ℤ) q]
      linear_combination i1 + i2
    have B : ∀ r, r < 6 → 6 * (N r (3 * (q + 1) + 1) : ℤ) = 2 ^ (3 * (q + 1) + 1) + c1 r * 2 ^ (q + 1) := by
      intro r hr
      rw [step r _ hr]
      have i1 := A r hr
      set j := (r + 6 - (3 * (q + 1) + 1) % 6) % 6 with hj
      have hj6 : j < 6 := idx_lt _ _
      have i2 := A j hj6
      have hc : c1 r = c0 r + c0 j := by
        unfold c0 c1
        have : j % 3 = (r + 2) % 3 := by omega
        rw [this]
        rcases (show r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 by omega) with h | h | h <;>
          simp [h, show (r + 2) % 3 = (r % 3 + 2) % 3 by omega]
      rw [hc, pow_succ]
      linear_combination i1 + i2
    have Cc : ∀ r, r < 6 → 6 * (N r (3 * (q + 1) + 2) : ℤ) = 2 ^ (3 * (q + 1) + 2) + c0 r * 2 ^ (q + 1) := by
      intro r hr
      rw [show 3 * (q + 1) + 2 = (3 * (q + 1) + 1) + 1 by ring, step r _ hr]
      have i1 := B r hr
      set j := (r + 6 - (3 * (q + 1) + 1 + 1) % 6) % 6 with hj
      have hj6 : j < 6 := idx_lt _ _
      have i2 := B j hj6
      have hc : c0 r = c1 r + c1 j := by
        unfold c0 c1
        have : j % 3 = (r + 1) % 3 := by omega
        rw [this]
        rcases (show r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 by omega) with h | h | h <;>
          simp [h, show (r + 1) % 3 = (r % 3 + 1) % 3 by omega]
      rw [hc, show 3 * (q + 1) + 1 + 1 = (3 * (q + 1) + 1) + 1 by ring, pow_succ]
      linear_combination i1 + i2
    exact fun r hr => ⟨A r hr, B r hr, Cc r hr⟩

theorem a_eq (n : ℕ) : a n = N 0 n := rfl

end OMAA068012Helpers

open OMA.S_oeis_a068012 OMAA068012Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a068012.main := by
  refine ⟨fun n hn h3 => ?_, fun k hk => ?_⟩
  · rcases (show n = 3 ∨ (∃ q, 2 ≤ q ∧ n = 3 * q) ∨ (∃ q, 1 ≤ q ∧ n = 3 * q + 2) by
      rcases (show n % 3 = 0 ∨ n % 3 = 2 by omega) with h | h
      · rcases (show n = 3 ∨ 6 ≤ n by omega) with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl ⟨n / 3, by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨n / 3, by omega, by omega⟩)) with h | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · subst h
      show N 0 3 = 2 * N 0 2
      decide
    · obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
      have e1 := (CF (p + 1) (by omega) 0 (by norm_num)).1
      have e2 := (CF p (by omega) 0 (by norm_num)).2.2
      rw [show 3 * (p + 1) - 1 = 3 * p + 2 by omega]
      simp only [a_eq]
      have : (6 : ℤ) * N 0 (3 * (p + 1)) = 6 * (2 * N 0 (3 * p + 2)) := by
        rw [e1, mul_left_comm, e2]; simp [c0]; ring
      exact_mod_cast (mul_left_cancel₀ (by norm_num : (6 : ℤ) ≠ 0) this)
    · have e1 := (CF q hq 0 (by norm_num)).2.2
      have e2 := (CF q hq 0 (by norm_num)).2.1
      rw [show 3 * q + 2 - 1 = 3 * q + 1 by omega]
      simp only [a_eq]
      have : (6 : ℤ) * N 0 (3 * q + 2) = 6 * (2 * N 0 (3 * q + 1)) := by
        rw [e1, mul_left_comm, e2]; simp [c0, c1]; ring
      exact_mod_cast (mul_left_cancel₀ (by norm_num : (6 : ℤ) ≠ 0) this)
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have e1 := (CF (j + 1) hk 0 (by norm_num)).2.1
    have e2 := (CF (j + 1) hk 0 (by norm_num)).1
    simp only [a_eq, Nat.add_sub_cancel]
    apply mul_left_cancel₀ (by norm_num : (6 : ℤ) ≠ 0)
    rw [e1, mul_sub, mul_left_comm, e2]
    simp [c0, c1]
    ring

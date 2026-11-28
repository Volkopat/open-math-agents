import OMAStatements.S_oeis_a182883
import Mathlib

/-!
A path with j up, j down and l horizontal steps is counted by w j l = (2j+l)! / (j! j! l!).
Reindexing by k = j + l gives the binomial sum. The weights satisfy one shift relation in l
and one in j; on the line 3j + 2l = n they combine pointwise into the order-four recurrence,
since a(n-2), a(n-3), a(n-4) are the sums over the same line of the shifted weights.
-/

namespace R182883
open OMA.S_oeis_a182883 Finset
open scoped Nat

def w (j l : ℕ) : ℕ := (2 * j + l).choose j * (j + l).choose j

theorem card_paths (j l : ℕ) : (paths j l).card = w j l := by
  simp only [paths, w]
  rw [Finset.card_sigma, Finset.sum_congr rfl (g := fun _ => (j + l).choose j)]
  · simp
  · intro up hup
    rw [Finset.mem_powersetCard] at hup
    rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hup.1, Finset.card_range, hup.2]
    congr 1
    omega

theorem a_eq (n : ℕ) : a n = ∑ p ∈ multiplicities n, w p.1 p.2 :=
  Finset.sum_congr rfl (fun p _ => card_paths p.1 p.2)

theorem part1 (n : ℕ) :
    a n = ∑ k ∈ range (n / 2 + 1), (n - k).choose k * k.choose (n - 2 * k) := by
  have hfil : ∀ k ∈ range (n / 2 + 1),
      (n - k).choose k * k.choose (n - 2 * k) ≠ 0 → n ≤ 3 * k := by
    intro k _ hk
    by_contra h
    apply hk
    rw [Nat.choose_eq_zero_of_lt (show k < n - 2 * k by omega), mul_zero]
  rw [a_eq, ← Finset.sum_filter_of_ne hfil]
  symm
  apply Finset.sum_nbij' (fun k => (n - 2 * k, 3 * k - n)) (fun p => p.1 + p.2)
  · intro k hk
    simp only [mem_filter, mem_range, multiplicities, mem_product] at hk ⊢
    omega
  · intro p hp
    simp only [mem_filter, mem_range, multiplicities, mem_product] at hp ⊢
    omega
  · intro k hk
    simp only [mem_filter, mem_range] at hk ⊢
    omega
  · intro p hp
    simp only [mem_filter, mem_range, multiplicities, mem_product, Prod.ext_iff] at hp ⊢
    omega
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    simp only [w]
    rw [show 2 * (n - 2 * k) + (3 * k - n) = n - k by omega,
      show n - 2 * k + (3 * k - n) = k by omega,
      Nat.choose_symm_of_eq_add (show n - k = k + (n - 2 * k) by omega)]

theorem shift (f : ℕ → ℕ → ℕ) (m n dj dl : ℕ) (h : m + 3 * dj + 2 * dl = n) :
    ∑ p ∈ multiplicities m, f p.1 p.2 =
      ∑ p ∈ multiplicities n, (if dj ≤ p.1 ∧ dl ≤ p.2 then f (p.1 - dj) (p.2 - dl) else 0) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun p => (p.1 + dj, p.2 + dl)) (fun p => (p.1 - dj, p.2 - dl))
  all_goals intro x hx
  all_goals simp only [mem_filter, mem_range, multiplicities, mem_product, Prod.ext_iff,
    Nat.add_sub_cancel] at hx ⊢
  all_goals omega

theorem wf (j l : ℕ) : w j l * (j ! * j ! * l !) = (2 * j + l)! := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j + l by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show j ≤ j + l by omega)
  rw [show 2 * j + l - j = j + l by omega] at h1
  rw [show j + l - j = l by omega] at h2
  unfold w
  calc (2 * j + l).choose j * (j + l).choose j * (j ! * j ! * l !)
      = (2 * j + l).choose j * j ! * ((j + l).choose j * j ! * l !) := by ring
    _ = (2 * j + l)! := by rw [h2, h1]

theorem fpos (j l : ℕ) : 0 < j ! * j ! * l ! :=
  Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos j) (Nat.factorial_pos j)) (Nat.factorial_pos l)

theorem r1 (j L : ℕ) : (L + 1) * w j (L + 1) = (2 * j + L + 1) * w j L := by
  apply Nat.eq_of_mul_eq_mul_right (fpos j L)
  have h1 := wf j (L + 1)
  have h2 := wf j L
  rw [Nat.factorial_succ L, show 2 * j + (L + 1) = 2 * j + L + 1 by ring,
    Nat.factorial_succ (2 * j + L)] at h1
  calc (L + 1) * w j (L + 1) * (j ! * j ! * L !)
      = w j (L + 1) * (j ! * j ! * ((L + 1) * L !)) := by ring
    _ = (2 * j + L + 1) * (2 * j + L)! := by rw [h1]
    _ = (2 * j + L + 1) * w j L * (j ! * j ! * L !) := by rw [← h2]; ring

theorem r2 (J l : ℕ) :
    (J + 1) ^ 2 * w (J + 1) l = (2 * J + l + 2) * (2 * J + l + 1) * w J l := by
  apply Nat.eq_of_mul_eq_mul_right (fpos J l)
  have h1 := wf (J + 1) l
  have h2 := wf J l
  rw [Nat.factorial_succ J, show 2 * (J + 1) + l = 2 * J + l + 1 + 1 by ring,
    Nat.factorial_succ (2 * J + l + 1), Nat.factorial_succ (2 * J + l)] at h1
  calc (J + 1) ^ 2 * w (J + 1) l * (J ! * J ! * l !)
      = w (J + 1) l * ((J + 1) * J ! * ((J + 1) * J !) * l !) := by ring
    _ = (2 * J + l + 1 + 1) * ((2 * J + l + 1) * (2 * J + l)!) := by rw [h1]
    _ = (2 * J + l + 2) * (2 * J + l + 1) * w J l * (J ! * J ! * l !) := by rw [← h2]; ring

theorem point (j l : ℕ) (hn : 4 ≤ 3 * j + 2 * l) :
    ((3 * j + 2 * l : ℕ) : ℤ) * (w j l : ℤ) =
      (2 * ((3 * j + 2 * l : ℕ) : ℤ) - 2) * (if 1 ≤ l then (w j (l - 1) : ℤ) else 0) +
      (4 * ((3 * j + 2 * l : ℕ) : ℤ) - 6) * (if 1 ≤ j then (w (j - 1) l : ℤ) else 0) -
      (((3 * j + 2 * l : ℕ) : ℤ) - 2) * (if 2 ≤ l then (w j (l - 2) : ℤ) else 0) := by
  have e1 : (l : ℤ) * w j l = (2 * j + l) * (if 1 ≤ l then (w j (l - 1) : ℤ) else 0) := by
    by_cases h1 : 1 ≤ l
    · obtain ⟨L, rfl⟩ : ∃ L, l = L + 1 := ⟨l - 1, by omega⟩
      rw [if_pos h1, Nat.add_sub_cancel]
      have h : ((L : ℤ) + 1) * w j (L + 1) = (2 * j + L + 1) * w j L := by exact_mod_cast r1 j L
      push_cast
      linear_combination h
    · obtain rfl : l = 0 := by omega
      simp
  have e2 : ((l : ℤ) - 1) * (if 1 ≤ l then (w j (l - 1) : ℤ) else 0) =
      (2 * j + l - 1) * (if 2 ≤ l then (w j (l - 2) : ℤ) else 0) := by
    by_cases h2 : 2 ≤ l
    · obtain ⟨L, rfl⟩ : ∃ L, l = L + 2 := ⟨l - 2, by omega⟩
      rw [if_pos (show 1 ≤ L + 2 by omega), if_pos h2, show L + 2 - 1 = L + 1 by omega,
        show L + 2 - 2 = L by omega]
      have h : ((L : ℤ) + 1) * w j (L + 1) = (2 * j + L + 1) * w j L := by exact_mod_cast r1 j L
      push_cast
      linear_combination h
    · rw [if_neg h2]
      by_cases h1 : 1 ≤ l
      · obtain rfl : l = 1 := by omega
        simp
      · obtain rfl : l = 0 := by omega
        simp
  have e3 : (j : ℤ) ^ 2 * w j l =
      (2 * j + l) * (2 * j + l - 1) * (if 1 ≤ j then (w (j - 1) l : ℤ) else 0) := by
    by_cases h1 : 1 ≤ j
    · obtain ⟨J, rfl⟩ : ∃ J, j = J + 1 := ⟨j - 1, by omega⟩
      rw [if_pos h1, Nat.add_sub_cancel]
      have h : ((J : ℤ) + 1) ^ 2 * w (J + 1) l = (2 * J + l + 2) * (2 * J + l + 1) * w J l := by
        exact_mod_cast r2 J l
      push_cast
      linear_combination h
    · obtain rfl : j = 0 := by omega
      simp
  have hN : (2 * (j : ℤ) + l) * (2 * j + l - 1) ≠ 0 := by
    apply mul_ne_zero <;> omega
  push_cast
  apply mul_left_cancel₀ hN
  linear_combination
    ((2 * (j : ℤ) + l - 1) * (6 * j + 4 * l - 2) - (3 * j + 2 * l - 2) * (l - 1)) * e1 -
      (2 * (j : ℤ) + l) * (3 * j + 2 * l - 2) * e2 + (12 * (j : ℤ) + 8 * l - 6) * e3

theorem recur (n : ℕ) (hn : 4 ≤ n) : (n : ℤ) * (a n : ℤ) =
    (2 * (n : ℤ) - 2) * (a (n - 2) : ℤ) + (4 * (n : ℤ) - 6) * (a (n - 3) : ℤ) -
      ((n : ℤ) - 2) * (a (n - 4) : ℤ) := by
  rw [a_eq, a_eq, a_eq, a_eq, shift w (n - 2) n 0 1 (by omega), shift w (n - 3) n 1 0 (by omega),
    shift w (n - 4) n 0 2 (by omega)]
  push_cast
  simp only [Nat.sub_zero, zero_le, true_and, and_true]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  simp only [multiplicities, mem_filter, mem_product, mem_range] at hp
  have h := point p.1 p.2 (by omega)
  rw [hp.2] at h
  linear_combination h

end R182883

theorem OMA.solution : type_of% @OMA.S_oeis_a182883.main :=
  ⟨R182883.part1, R182883.recur⟩

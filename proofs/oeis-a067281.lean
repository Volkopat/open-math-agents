import OMAStatements.S_oeis_a067281
import Mathlib
open OMA.S_oeis_a067281

theorem countPerms_cons_fresh (x : ℕ) (m : Multiset ℕ) (hx : x ∉ m) :
    (x ::ₘ m).countPerms = (Multiset.card m + 1) * m.countPerms := by
  rw [Multiset.countPerms_filter_ne x]
  rw [Multiset.count_cons_self, Multiset.count_eq_zero_of_notMem hx, Multiset.card_cons]
  have hf : Multiset.filter (fun y => x ≠ y) (x ::ₘ m) = m := by
    rw [Multiset.filter_cons]
    simp only [ne_eq, not_true_eq_false, if_false, zero_add]
    rw [Multiset.filter_eq_self]
    intro y hy h
    exact hx (h ▸ hy)
  rw [hf]
  simp

theorem classes_succ (m : ℕ) : classes (m+1) = ordCompl[2] (m+1) ::ₘ classes m := by
  unfold classes
  rw [List.range_succ, List.map_append, ← Multiset.coe_add]
  simp [add_comm]

theorem odd_ordCompl (n : ℕ) : ordCompl[2] (2*n+1) = 2*n+1 := by
  have : (2*n+1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by omega)
  simp [this]

theorem card_classes (m : ℕ) : Multiset.card (classes m) = m := by
  simp [classes]

theorem OMA.solution : type_of% @OMA.S_oeis_a067281.main := by
  intro n
  unfold a
  rw [show 2*n+1 = (2*n)+1 from rfl, classes_succ, odd_ordCompl, countPerms_cons_fresh, card_classes]
  intro h
  simp only [classes, Multiset.mem_coe, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, he⟩ := h
  have := Nat.ordCompl_le (k+1) 2
  omega

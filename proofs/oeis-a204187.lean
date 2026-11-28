import OMAStatements.S_oeis_a204187
import Mathlib

namespace OMA.S_oeis_a204187

lemma sum_cast (m : ℕ) (hm : 1 ≤ m) :
    ((∑ k ∈ Finset.Ico 1 (2 * m), k ^ (2 * m - 1) : ℕ) : ZMod (2 * m)) =
      (m : ZMod (2 * m)) ^ (2 * m - 1) := by
  have hmem : m ∈ Finset.Ico 1 (2 * m) := by simp [Finset.mem_Ico]; omega
  rw [← Finset.add_sum_erase _ _ hmem]
  push_cast
  have hodd : Odd (2 * m - 1) := ⟨m - 1, by omega⟩
  have h0 : ∑ k ∈ (Finset.Ico 1 (2 * m)).erase m, ((k : ZMod (2 * m)) ^ (2 * m - 1)) = 0 := by
    refine Finset.sum_involution (fun k _ => 2 * m - k) ?_ ?_ ?_ ?_
    · intro k hk
      have hk' := Finset.mem_Ico.mp (Finset.mem_of_mem_erase hk)
      rw [Nat.cast_sub (by omega)]
      have : ((2 * m : ℕ) : ZMod (2 * m)) = 0 := ZMod.natCast_self _
      rw [this, zero_sub, hodd.neg_pow]; ring
    · intro k hk _ h
      have hk1 := Finset.mem_erase.mp hk
      have hk' := Finset.mem_Ico.mp hk1.2
      omega
    · intro k hk
      have hk1 := Finset.mem_erase.mp hk
      have hk' := Finset.mem_Ico.mp hk1.2
      refine Finset.mem_erase.mpr ⟨by omega, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩
    · intro k hk
      have hk1 := Finset.mem_erase.mp hk
      have hk' := Finset.mem_Ico.mp hk1.2
      omega
  rw [h0, add_zero]

end OMA.S_oeis_a204187

theorem OMA.solution : type_of% @OMA.S_oeis_a204187.main := by
  intro n hn
  unfold OMA.S_oeis_a204187.a
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have hm : 1 ≤ m := by omega
    have hc := OMA.S_oeis_a204187.sum_cast m hm
    set S := ∑ k ∈ Finset.Ico 1 (2 * m), k ^ (2 * m - 1) with hS
    have hlt : S % (2 * m) < 2 * m := Nat.mod_lt _ (by omega)
    have hcast : S % (2 * m) = (m ^ (2 * m - 1)) % (2 * m) := by
      have : ((S : ℕ) : ZMod (2 * m)) = ((m ^ (2 * m - 1) : ℕ) : ZMod (2 * m)) := by
        rw [hc]; push_cast; rfl
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp this
    rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
    · have hj : 1 ≤ j := by omega
      have hd : 2 * (2 * j) ∣ (2 * j) ^ (2 * (2 * j) - 1) := by
        have : (2 * j) ^ (2 * (2 * j) - 1) = (2 * j) * (2 * j) * (2 * j) ^ (2 * (2 * j) - 3) := by
          rw [← pow_two, ← pow_add]; congr 1; omega
        rw [this]
        exact Dvd.dvd.mul_right ⟨j, by ring⟩ _
      rw [Nat.mod_eq_zero_of_dvd hd] at hcast
      rw [hcast]; omega
    · have hodd : Odd ((2 * j + 1) ^ (2 * (2 * j + 1) - 2)) := Odd.pow (by exact ⟨j, rfl⟩)
      obtain ⟨r, hr⟩ := hodd
      have he : (2 * j + 1) ^ (2 * (2 * j + 1) - 1) = (2 * j + 1) * (2 * r + 1) := by
        rw [← hr, ← pow_succ']; congr 1
      have : (2 * j + 1) ^ (2 * (2 * j + 1) - 1) % (2 * (2 * j + 1)) = 2 * j + 1 := by
        rw [he]
        have : (2 * j + 1) * (2 * r + 1) = (2 * j + 1) + (2 * (2 * j + 1)) * r := by ring
        rw [this, Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt (by omega)
      rw [this] at hcast
      rw [hcast]; omega
  · omega

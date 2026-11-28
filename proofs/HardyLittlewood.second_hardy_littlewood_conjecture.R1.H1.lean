import OMAReductions.R_HardyLittlewood_second_hardy_littlewood_conjecture_R1
import Mathlib

-- Step HardyLittlewood.second_hardy_littlewood_conjecture.R1.H1: hypothesis H1 of reduction HardyLittlewood.second_hardy_littlewood_conjecture.R1
-- Credit: @ivillar

/-!
`π (x + y) ≤ π x + π y` when `y ≤ 26`: for `x ≥ 5` every prime in `(x, x + y]` is coprime to
`30`, and a window of `y ≤ 26` consecutive integers contains at most `π y` integers coprime to
`30` (checked over the 30 residues by kernel evaluation). The cases `x < 5` are checked directly.
-/
namespace F2HL

theorem sieve : ∀ r < 30, ∀ y ≤ 26, 2 ≤ y →
    Nat.count (fun k => Nat.Coprime (r + k) 30) y ≤ Nat.primeCounting y := by
  decide +kernel

theorem small : ∀ x < 5, 2 ≤ x → ∀ y ≤ 26, 2 ≤ y →
    Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  decide +kernel

theorem cop30 (n : ℕ) (hn : 6 ≤ n) (hp : n.Prime) : Nat.Coprime n 30 := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  have hle : n ≤ 30 := Nat.le_of_dvd (by norm_num) hd
  interval_cases n <;> revert hp hd <;> decide

theorem key (x y : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) (hy26 : y ≤ 26) :
    Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  by_cases h5 : x < 5
  · exact small x h5 hx y hy26 hy
  · have hx5 : 5 ≤ x := not_lt.mp h5
    have e : Nat.primeCounting (x + y) =
        Nat.primeCounting x + Nat.count (fun k => Nat.Prime (x + 1 + k)) y := by
      unfold Nat.primeCounting Nat.primeCounting'
      rw [show x + y + 1 = (x + 1) + y by ring, Nat.count_add]
    rw [e]
    apply Nat.add_le_add_left
    calc Nat.count (fun k => Nat.Prime (x + 1 + k)) y
        ≤ Nat.count (fun k => Nat.Coprime ((x + 1) % 30 + k) 30) y := by
          apply Nat.count_mono_left
          intro k _ hk
          have hc : Nat.Coprime (x + 1 + k) 30 := cop30 _ (by omega) hk
          have e2 : x + 1 + k = ((x + 1) % 30 + k) + 30 * ((x + 1) / 30) := by omega
          rw [e2] at hc
          exact (Nat.coprime_add_mul_left_left _ _ _).mp hc
      _ ≤ Nat.primeCounting y := sieve _ (Nat.mod_lt _ (by norm_num)) y hy26 hy

theorem short : ∀ x y : ℕ, 2 ≤ x → 2 ≤ y → (x ≤ 26 ∨ y ≤ 26) →
    HardyLittlewood.SecondHardyLittlewoodConjectureFor x y := by
  intro x y hx hy h
  unfold HardyLittlewood.SecondHardyLittlewoodConjectureFor
  rcases h with h | h
  · rw [add_comm x y, add_comm (Nat.primeCounting x)]
    exact key y x hy hx h
  · exact key x y hx hy h

end F2HL

theorem OMA.solution : OMA.R_HardyLittlewood_second_hardy_littlewood_conjecture_R1.H1 :=
  F2HL.short

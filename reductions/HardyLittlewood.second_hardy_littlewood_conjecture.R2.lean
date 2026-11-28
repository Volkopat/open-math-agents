import FormalConjectures.Wikipedia.HardyLittlewood

namespace OMA.R_HardyLittlewood_second_hardy_littlewood_conjecture_R2

open scoped Nat.Prime

def H1 : Prop := ∀ x y : ℕ, 69 ≤ y → y ≤ x → x ≤ 2 * y → (x + y).Prime →
  π (x + y) ≤ π x + π y

def H2 : Prop := ∀ x y : ℕ, 69 ≤ y → 2 * y < x → (x + y).Prime →
  π (x + y) ≤ π x + π y

lemma window (x n : ℕ) (hx : 5 ≤ x) :
    π (x + n) ≤ π x + Nat.count (fun i =>
      (x % 30 + i + 1) % 2 ≠ 0 ∧ (x % 30 + i + 1) % 3 ≠ 0 ∧
      (x % 30 + i + 1) % 5 ≠ 0) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ]
    have h : π (x + (n + 1)) = π (x + n) + (if (x+n+1).Prime then 1 else 0) :=
      Nat.count_succ _ _
    rw [h]
    by_cases hp : (x+n+1).Prime
    · have hd (d : ℕ) (hd : 2 ≤ d) (he : d ≤ 5) : ¬ d ∣ x+n+1 := by
        intro hdiv
        rcases hp.eq_one_or_self_of_dvd d hdiv with h | h <;> omega
      have h2 := hd 2 (by decide) (by decide)
      have h3 := hd 3 (by decide) (by decide)
      have h5 := hd 5 (by decide) (by decide)
      have hr : (x % 30 + n + 1) % 2 ≠ 0 ∧ (x % 30 + n + 1) % 3 ≠ 0 ∧
          (x % 30 + n + 1) % 5 ≠ 0 := by omega
      rw [if_pos hp, if_pos hr]
      omega
    · simp only [hp, if_false, Nat.add_zero]
      split <;> omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma wheel_table : ∀ r : Fin 30, ∀ k : Fin 67,
    Nat.count (fun i => (r.val + i + 1) % 2 ≠ 0 ∧ (r.val + i + 1) % 3 ≠ 0 ∧
      (r.val + i + 1) % 5 ≠ 0) (k.val + 2) ≤ π (k.val + 2) := by decide

lemma short_interval (x y : ℕ) (hy : 2 ≤ y) (hle : y ≤ x) (hs : y ≤ 68) :
    π (x + y) ≤ π x + π y := by
  by_cases hx : 5 ≤ x
  · have ht := wheel_table ⟨x % 30, by omega⟩ ⟨y - 2, by omega⟩
    dsimp only at ht
    rw [Nat.sub_add_cancel hy] at ht
    exact (window x y hx).trans (Nat.add_le_add_left ht x.primeCounting)
  · have : x ≤ 4 := by omega
    interval_cases x <;> interval_cases y <;> decide

lemma remove_composite (a : H1) (b : H2) (x y : ℕ) (hy : 2 ≤ y) (hle : y ≤ x) :
    π (x + y) ≤ π x + π y := by
  by_cases hp : (x + y).Prime
  · by_cases hs : y ≤ 68
    · exact short_interval x y hy hle hs
    by_cases hc : x ≤ 2 * y
    · exact a x y (by omega) hle hc hp
    · exact b x y (by omega) (by omega) hp
  by_cases hx : x = 2
  · have : y = 2 := by omega
    subst x
    subst y
    decide
  obtain ⟨z, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show x ≠ 0 by omega)
  have heq : π (z + 1 + y) = π (z + y) := by
    have h : π (z + y + 1) = π (z + y) + (if (z + y + 1).Prime then 1 else 0) :=
      Nat.count_succ _ _
    rw [show z + 1 + y = z + y + 1 by omega] at hp ⊢
    simpa [hp] using h
  rw [heq]
  have prev : π (z + y) ≤ π z + π y := by
    rcases le_total y z with h | h
    · exact remove_composite a b z y hy h
    · simpa only [Nat.add_comm] using remove_composite a b y z (by omega) h
  exact prev.trans (Nat.add_le_add_right (Nat.monotone_primeCounting (Nat.le_succ z)) y.primeCounting)
termination_by x + y
decreasing_by all_goals omega

theorem main : H1 → H2 → type_of% @HardyLittlewood.second_hardy_littlewood_conjecture := by
  intro a b x y hx hy
  rcases le_total y x with h | h
  · exact remove_composite a b x y hy h
  · simpa only [HardyLittlewood.SecondHardyLittlewoodConjectureFor, Nat.add_comm] using
      remove_composite a b y x hx h

end OMA.R_HardyLittlewood_second_hardy_littlewood_conjecture_R2

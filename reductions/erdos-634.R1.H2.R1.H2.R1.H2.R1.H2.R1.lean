import OMAReductions.R_erdos_634_R1_H2_R1_H2_R1_H2_R1

/-!
# Erdos 634, reduction R1.H2.R1.H2.R1.H2.R1.H2.R1

Lemma S of Laczkovich for 5-smooth n at most 200, split by n so that the certified computations
(one kernel-checked certificate per n) are spread over several files:
* H1: a 5-smooth n with 3 ≤ n ≤ 200 is in one of the three lists below or is exceptional;
* H2, H3, H4: the relation space of (n, a) is trivial for n in each list.
-/

namespace OMA.R_erdos_634_R1_H2_R1_H2_R1_H2_R1_H2_R1

def H1 : Prop := ∀ n : ℕ, 3 ≤ n → n ≤ 200 → (∀ l : ℕ, l.Prime → l ∣ n → l ≤ 5) → (n = 5 ∨ n = 9 ∨ n = 15 ∨ n = 16 ∨ n = 20 ∨ n = 25 ∨ n = 27 ∨ n = 32 ∨ n = 36 ∨ n = 40 ∨ n = 45 ∨ n = 48 ∨ n = 50 ∨ n = 54 ∨ n = 64 ∨ n = 72 ∨ n = 75 ∨ n = 80 ∨ n = 81 ∨ n = 90 ∨ n = 96 ∨ n = 100 ∨ n = 108 ∨ n = 120 ∨ n = 125 ∨ n = 128 ∨ n = 135 ∨ n = 144 ∨ n = 150) ∨ (n = 160 ∨ n = 162 ∨ n = 180) ∨ (n = 192 ∨ n = 200) ∨ (n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 ∨ n = 12 ∨ n = 18 ∨ n = 24 ∨ n = 30 ∨ n = 60)

def H2 : Prop := ∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) → ∑ i, a i = n → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (n = 5 ∨ n = 9 ∨ n = 15 ∨ n = 16 ∨ n = 20 ∨ n = 25 ∨ n = 27 ∨ n = 32 ∨ n = 36 ∨ n = 40 ∨ n = 45 ∨ n = 48 ∨ n = 50 ∨ n = 54 ∨ n = 64 ∨ n = 72 ∨ n = 75 ∨ n = 80 ∨ n = 81 ∨ n = 90 ∨ n = 96 ∨ n = 100 ∨ n = 108 ∨ n = 120 ∨ n = 125 ∨ n = 128 ∨ n = 135 ∨ n = 144 ∨ n = 150) → (⨅ (k : ℕ) (_ : k.Coprime n), LinearMap.ker (∑ i, (if Int.fract ((k * a i : ℕ) / (n : ℚ)) = 0 then 0 else Int.fract ((k * a i : ℕ) / (n : ℚ)) - 1 / 2) • LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) i)) = Submodule.span ℚ ({v : Fin 3 → ℚ | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪ {v : Fin 3 → ℚ | ∃ i, 2 * a i = n ∧ v = Pi.single i 1})

def H3 : Prop := ∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) → ∑ i, a i = n → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (n = 160 ∨ n = 162 ∨ n = 180) → (⨅ (k : ℕ) (_ : k.Coprime n), LinearMap.ker (∑ i, (if Int.fract ((k * a i : ℕ) / (n : ℚ)) = 0 then 0 else Int.fract ((k * a i : ℕ) / (n : ℚ)) - 1 / 2) • LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) i)) = Submodule.span ℚ ({v : Fin 3 → ℚ | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪ {v : Fin 3 → ℚ | ∃ i, 2 * a i = n ∧ v = Pi.single i 1})

def H4 : Prop := ∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) → ∑ i, a i = n → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (n = 192 ∨ n = 200) → (⨅ (k : ℕ) (_ : k.Coprime n), LinearMap.ker (∑ i, (if Int.fract ((k * a i : ℕ) / (n : ℚ)) = 0 then 0 else Int.fract ((k * a i : ℕ) / (n : ℚ)) - 1 / 2) • LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) i)) = Submodule.span ℚ ({v : Fin 3 → ℚ | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪ {v : Fin 3 → ℚ | ∃ i, 2 * a i = n ∧ v = Pi.single i 1})

theorem main : H1 → H2 → H3 → H4 → OMA.R_erdos_634_R1_H2_R1_H2_R1_H2_R1.H2 := by
  intro g1 g2 g3 g4 n a hpos hsum hg hs
  by_cases h200 : 200 < n
  · exact Or.inr (Or.inl h200)
  have h3 : 3 ≤ n := by
    rw [← hsum, Fin.sum_univ_three]; have := hpos 0; have := hpos 1; have := hpos 2; omega
  rcases g1 n h3 (by omega) hs with h | h | h | h
  · exact Or.inl (g2 n a hpos hsum hg h)
  · exact Or.inl (g3 n a hpos hsum hg h)
  · exact Or.inl (g4 n a hpos hsum hg h)
  · exact Or.inr (Or.inr h)

end OMA.R_erdos_634_R1_H2_R1_H2_R1_H2_R1_H2_R1

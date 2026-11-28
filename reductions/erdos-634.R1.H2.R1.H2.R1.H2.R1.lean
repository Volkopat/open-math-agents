import OMAReductions.R_erdos_634_R1_H2_R1_H2_R1

/-!
# Erdos 634, reduction R1.H2.R1.H2.R1.H2.R1

Lemma S of Laczkovich (the rational relation space of (n, a) is trivial), split by the prime factors
of n: H1, some prime at least 7 divides n (Bonfioli, lemmaS); H2, n is 5-smooth: then the relation
space is trivial (certified computations for the 5-smooth n up to 200 that are not exceptional),
or n > 200, or n is one of the exceptional denominators.
-/

namespace OMA.R_erdos_634_R1_H2_R1_H2_R1_H2_R1

def H1 : Prop := ∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) → ∑ i, a i = n → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∃ l : ℕ, l.Prime ∧ 7 ≤ l ∧ l ∣ n) → (⨅ (k : ℕ) (_ : k.Coprime n), LinearMap.ker (∑ i, (if Int.fract ((k * a i : ℕ) / (n : ℚ)) = 0 then 0 else Int.fract ((k * a i : ℕ) / (n : ℚ)) - 1 / 2) • LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) i)) = Submodule.span ℚ ({v : Fin 3 → ℚ | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪ {v : Fin 3 → ℚ | ∃ i, 2 * a i = n ∧ v = Pi.single i 1})

def H2 : Prop := ∀ (n : ℕ) (a : Fin 3 → ℕ), (∀ i, 0 < a i) → ∑ i, a i = n → Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ l : ℕ, l.Prime → l ∣ n → l ≤ 5) → (⨅ (k : ℕ) (_ : k.Coprime n), LinearMap.ker (∑ i, (if Int.fract ((k * a i : ℕ) / (n : ℚ)) = 0 then 0 else Int.fract ((k * a i : ℕ) / (n : ℚ)) - 1 / 2) • LinearMap.proj (R := ℚ) (φ := fun _ : Fin 3 => ℚ) i)) = Submodule.span ℚ ({v : Fin 3 → ℚ | ∃ i j, i ≠ j ∧ a i = a j ∧ v = Pi.single i 1 - Pi.single j 1} ∪ {v : Fin 3 → ℚ | ∃ i, 2 * a i = n ∧ v = Pi.single i 1}) ∨ 200 < n ∨ (n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 ∨ n = 12 ∨ n = 18 ∨ n = 24 ∨ n = 30 ∨ n = 60)

theorem main : H1 → H2 → OMA.R_erdos_634_R1_H2_R1_H2_R1.H2 := by
  intro g1 g2 n a hpos hsum hg
  by_cases h : ∃ l : ℕ, l.Prime ∧ 7 ≤ l ∧ l ∣ n
  · exact Or.inl (g1 n a hpos hsum hg h)
  · have hs : ∀ l : ℕ, l.Prime → l ∣ n → l ≤ 5 := by
      intro l hl hd
      by_contra h5
      apply h
      refine ⟨l, hl, ?_, hd⟩
      by_contra h7
      have h6 : l = 6 := by omega
      subst h6
      exact absurd hl (by norm_num)
    rcases g2 n a hpos hsum hg hs with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨h1, hs⟩)
    · exact Or.inr (Or.inr h1)

end OMA.R_erdos_634_R1_H2_R1_H2_R1_H2_R1

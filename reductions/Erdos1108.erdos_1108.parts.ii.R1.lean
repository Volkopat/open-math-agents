import FormalConjectures.ErdosProblems.«1108»

-- Reduction Erdos1108.erdos_1108.parts.ii.R1 of Erdős Problem 1108 — ii
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos1108_erdos_1108_parts_ii_R1

/-- Sums that use `1!`: the odd sums of distinct factorials. Only finitely many are powerful. -/
def H1 : Prop :=
  Set.Finite {a : ℕ | ∃ S : Finset ℕ, (∀ n ∈ S, 0 < n) ∧ 1 ∈ S ∧
    a = ∑ n ∈ S, n.factorial ∧ a.Powerful}

/-- Sums that avoid `1!` but use both `2!` and `3!` (so `4 ∣ a`). Only finitely many are
powerful. -/
def H2 : Prop :=
  Set.Finite {a : ℕ | ∃ S : Finset ℕ, (∀ n ∈ S, 0 < n) ∧ 1 ∉ S ∧ 2 ∈ S ∧ 3 ∈ S ∧
    a = ∑ n ∈ S, n.factorial ∧ a.Powerful}

/-- Sums of factorials `n!` with every `n ≥ 4` (so `24 ∣ a`). Only finitely many are
powerful. -/
def H3 : Prop :=
  Set.Finite {a : ℕ | ∃ S : Finset ℕ, (∀ n ∈ S, 4 ≤ n) ∧
    a = ∑ n ∈ S, n.factorial ∧ a.Powerful}

/-- A number that is `2 mod 4` is divisible by `2` but not by `4`, so it is not powerful. -/
theorem not_powerful_of_mod_four {a : ℕ} (h : a % 4 = 2) : ¬ a.Powerful := by
  intro hp
  unfold Nat.Powerful Nat.Full at hp
  have h2 : 2 ∈ a.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by omega, by omega⟩
  have h4 := hp 2 h2
  norm_num at h4
  omega

/-- A sum of distinct factorials avoiding `1!` and using exactly one of `2!`, `3!` is `2 mod 4`. -/
theorem sum_mod_four (S : Finset ℕ) (hpos : ∀ n ∈ S, 0 < n) (h1 : 1 ∉ S)
    (h23 : (2 ∈ S ∧ 3 ∉ S) ∨ (2 ∉ S ∧ 3 ∈ S)) :
    (∑ n ∈ S, n.factorial) % 4 = 2 := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun n => n < 4)]
  have hbig : 4 ∣ ∑ n ∈ S.filter (fun n => ¬ n < 4), n.factorial := by
    apply Finset.dvd_sum
    intro n hn
    rw [Finset.mem_filter] at hn
    exact Nat.dvd_factorial (by norm_num) (by omega)
  rcases h23 with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · have hT : S.filter (fun n => n < 4) = {2} := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hn, hlt⟩
        have := hpos n hn
        rcases (show n = 1 ∨ n = 2 ∨ n = 3 by omega) with rfl | rfl | rfl
        · exact absurd hn h1
        · rfl
        · exact absurd hn h3
      · rintro rfl
        exact ⟨h2, by norm_num⟩
    rw [hT, Finset.sum_singleton, show Nat.factorial 2 = 2 from rfl]
    omega
  · have hT : S.filter (fun n => n < 4) = {3} := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hn, hlt⟩
        have := hpos n hn
        rcases (show n = 1 ∨ n = 2 ∨ n = 3 by omega) with rfl | rfl | rfl
        · exact absurd hn h1
        · exact absurd hn h2
        · rfl
      · rintro rfl
        exact ⟨h3, by norm_num⟩
    rw [hT, Finset.sum_singleton, show Nat.factorial 3 = 6 from rfl]
    omega

/-- Split a powerful sum of distinct factorials by which of `1!, 2!, 3!` it uses: the mixed cases
(no `1!`, exactly one of `2!`, `3!`) are `2 mod 4` and never powerful. -/
theorem main : H1 → H2 → H3 → type_of% @Erdos1108.erdos_1108.parts.ii := by
  intro h1 h2 h3
  refine (h1.union (h2.union h3)).subset ?_
  rintro a ⟨⟨S, hpos, rfl⟩, hpow⟩
  by_cases hS1 : 1 ∈ S
  · exact Or.inl ⟨S, hpos, hS1, rfl, hpow⟩
  by_cases hS23 : 2 ∈ S ∧ 3 ∈ S
  · exact Or.inr (Or.inl ⟨S, hpos, hS1, hS23.1, hS23.2, rfl, hpow⟩)
  by_cases hS0 : 2 ∉ S ∧ 3 ∉ S
  · refine Or.inr (Or.inr ⟨S, fun n hn => ?_, rfl, hpow⟩)
    have := hpos n hn
    have h1' : n ≠ 1 := fun h => hS1 (h ▸ hn)
    have h2' : n ≠ 2 := fun h => hS0.1 (h ▸ hn)
    have h3' : n ≠ 3 := fun h => hS0.2 (h ▸ hn)
    omega
  exfalso
  have h23 : (2 ∈ S ∧ 3 ∉ S) ∨ (2 ∉ S ∧ 3 ∈ S) := by tauto
  exact not_powerful_of_mod_four (sum_mod_four S hpos hS1 h23) hpow

end OMA.R_Erdos1108_erdos_1108_parts_ii_R1

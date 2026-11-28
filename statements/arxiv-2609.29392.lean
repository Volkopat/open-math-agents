import Mathlib

namespace OMA.S_arxiv_2609_29392

/-- Position `p : Fin n` is a left-to-right maximum of the one-line notation of `π : Equiv.Perm (Fin n)`
if every earlier position has a strictly smaller value. -/
def IsLMax {n : ℕ} (π : Equiv.Perm (Fin n)) (p : Fin n) : Prop :=
  ∀ q : Fin n, q < p → π q < π p

instance {n : ℕ} (π : Equiv.Perm (Fin n)) (p : Fin n) : Decidable (IsLMax π p) := by
  unfold IsLMax; infer_instance

/-- The largest left-to-right maximum position `≤ p` in `π` (i.e., the starting position of
the cycle containing `π p` under Foata's inverse fundamental transformation `θ⁻¹(π)`). -/
def lmaxStart {n : ℕ} (π : Equiv.Perm (Fin n)) (p : Fin n) : Fin n :=
  (Finset.univ.filter (fun q : Fin n => q ≤ p ∧ IsLMax π q)).max' (by
    refine ⟨⟨0, Nat.pos_of_ne_zero (by intro h; subst h; exact Fin.elim0 p)⟩, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Fin.le_def.mpr (Nat.zero_le _), fun q hq => by
      have := Fin.lt_def.mp hq; dsimp only at this; omega⟩)

/-- Foata's inverse first fundamental transformation `θ⁻¹(π)` (denoted `π̂` in Zhou--Yu,
arXiv:2609.29392): in the standard cycle representation obtained by splitting the one-line
notation of `π` before each left-to-right maximum, each entry `π p` maps to `π (p + 1)`
unless `p` is the last position or `p + 1` starts a new cycle (is a left-to-right maximum),
in which case `π p` closes its cycle by mapping back to `π (lmaxStart π p)`. -/
def foataInv {n : ℕ} (π : Equiv.Perm (Fin n)) (x : Fin n) : Fin n :=
  let p := π.symm x
  if h : p.val + 1 < n then
    if ¬ IsLMax π ⟨p.val + 1, h⟩ then
      π ⟨p.val + 1, h⟩
    else
      π (lmaxStart π p)
  else
    π (lmaxStart π p)

/-- Containment of the arrow pattern `(12; 3 → 3)` in `π ∈ S_n`: there exist values
`x₁ < x₂ < x₃` such that `x₁` precedes `x₂` in the one-line notation of `π` and `π̂(x₃) = x₃`. -/
def ContainsArrow12_33 {n : ℕ} (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ x₁ x₂ x₃ : Fin n, x₁ < x₂ ∧ x₂ < x₃ ∧ π.symm x₁ < π.symm x₂ ∧ foataInv π x₃ = x₃

instance {n : ℕ} (π : Equiv.Perm (Fin n)) : Decidable (ContainsArrow12_33 π) := by
  unfold ContainsArrow12_33; infer_instance

/-- Containment of the arrow pattern `(21; 3 → 3)` in `π ∈ S_n`: there exist values
`x₁ < x₂ < x₃` such that `x₂` precedes `x₁` in the one-line notation of `π` and `π̂(x₃) = x₃`. -/
def ContainsArrow21_33 {n : ℕ} (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ x₁ x₂ x₃ : Fin n, x₁ < x₂ ∧ x₂ < x₃ ∧ π.symm x₂ < π.symm x₁ ∧ foataInv π x₃ = x₃

instance {n : ℕ} (π : Equiv.Perm (Fin n)) : Decidable (ContainsArrow21_33 π) := by
  unfold ContainsArrow21_33; infer_instance

/-- The `n`-th derangement number `d_n`, i.e., the number of fixed-point-free permutations in `S_n`. -/
def derangementCount (n : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin n) // ∀ i : Fin n, σ i ≠ i}

/-- Zhou and Yu (arXiv:2609.29392), Theorems 3.1 and 3.2, resolving the two arrow pattern
enumeration cases `(12; 3 → 3)` and `(21; 3 → 3)` left open by Archer and Laudone:
for every `n ≥ 1`,
`|S_n(12; 3 → 3)| = |S_n(21; 3 → 3)| = d_n + ∑_{m=1}^n ∑_{k=0}^{n-m} C(n-m, k) C(m+k-1, n-m) d_k`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      Fintype.card {π : Equiv.Perm (Fin n) // ¬ ContainsArrow12_33 π} =
        derangementCount n +
          ∑ m ∈ Finset.Icc 1 n, ∑ k ∈ Finset.range (n - m + 1),
            Nat.choose (n - m) k * Nat.choose (m + k - 1) (n - m) * derangementCount k ∧
      Fintype.card {π : Equiv.Perm (Fin n) // ¬ ContainsArrow21_33 π} =
        derangementCount n +
          ∑ m ∈ Finset.Icc 1 n, ∑ k ∈ Finset.range (n - m + 1),
            Nat.choose (n - m) k * Nat.choose (m + k - 1) (n - m) * derangementCount k := by
  sorry

end OMA.S_arxiv_2609_29392

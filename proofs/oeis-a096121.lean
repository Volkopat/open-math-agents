import OMAStatements.S_oeis_a096121

/-!
Mikhail Kurkov's rook-walk conjecture: https://oeis.org/A096121
Paul D. Hanna's binomial sum: https://oeis.org/A102038
Formal statement by @KoaOkano. Proof by @grp06.
-/

open scoped BigOperators
open OMA.S_oeis_a096121

namespace OMA.A096121Proof

private theorem card_starPositions (slots stars : ℕ) :
    Fintype.card (StarPositions slots stars) = slots.choose stars := by
  classical
  let subsets := (Finset.univ : Finset (Fin slots)).powersetCard stars
  let e : StarPositions slots stars ≃ ↥subsets :=
    { toFun := fun s => ⟨s.val, Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, s.property⟩⟩
      invFun := fun s => ⟨s.val, (Finset.mem_powersetCard.mp s.property).2⟩
      left_inv := fun s => Subtype.ext rfl
      right_inv := fun s => Subtype.ext rfl }
  calc
    Fintype.card (StarPositions slots stars) = Fintype.card ↥subsets :=
      Fintype.card_congr e
    _ = subsets.card := Fintype.card_coe _
    _ = slots.choose stars := by
      simp only [subsets, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private def rookNumber (a b k : ℕ) : ℕ :=
  k.factorial * a.choose k * b.choose k

private theorem rook_pascal (a b k : ℕ) (ha : k ≤ a) (hb : k ≤ b) :
    rookNumber (a + 1) (b + 1) (k + 1) =
      rookNumber a b (k + 1) + (a + b - k + 1) * rookNumber a b k := by
  have hcoeff : a + b - k + 1 = (a - k) + (b - k) + (k + 1) := by omega
  unfold rookNumber
  calc
    _ = (k + 1).factorial * a.choose (k + 1) * b.choose (k + 1) +
        (a.choose (k + 1) * (k + 1)) * k.factorial * b.choose k +
        (b.choose (k + 1) * (k + 1)) * k.factorial * a.choose k +
        (k + 1) * (k.factorial * a.choose k * b.choose k) := by
          rw [Nat.choose_succ_succ' a k, Nat.choose_succ_succ' b k, Nat.factorial_succ k]
          ring
    _ = _ := by
      rw [Nat.choose_succ_right_eq a k, Nat.choose_succ_right_eq b k, hcoeff]
      ring

private def term (m k : ℕ) : ℕ :=
  rookNumber ((m + k + 1) / 2) ((m + k) / 2) k

private def normalized (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (m + 1), term m k

private theorem card_walk (m : ℕ) :
    Fintype.card (RookWalk m) = (2 * (m + 1).factorial) * normalized m := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_perm, Fintype.card_fin,
    card_starPositions]
  calc
    _ = ∑ k : Fin (m + 1), (2 * (m + 1).factorial) * term m k.val := by
      apply Finset.sum_congr rfl
      intro k _
      unfold term rookNumber
      ring
    _ = (2 * (m + 1).factorial) * normalized m := by
      rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (term m) (m + 1)] <;> rfl

private theorem term_zero (m : ℕ) : term m 0 = 1 := by
  simp [term, rookNumber]

private theorem term_outside (m k : ℕ) (h : m < k) : term m k = 0 := by
  have hlt : (m + k) / 2 < k := by omega
  simp [term, rookNumber, Nat.choose_eq_zero_of_lt hlt]

private theorem term_step (m k : ℕ) (hk : k ≤ m + 1) :
    term (m + 2) (k + 1) = term m (k + 1) + (m + 2) * term (m + 1) k := by
  let a := (m + 1 + k + 1) / 2
  let b := (m + 1 + k) / 2
  have ha : k ≤ a := by dsimp [a]; omega
  have hb : k ≤ b := by dsimp [b]; omega
  have hsum : a + b = m + 1 + k := by dsimp [a, b]; omega
  have hcoeff : a + b - k + 1 = m + 2 := by omega
  have hleft₁ : (m + 2 + (k + 1) + 1) / 2 = a + 1 := by dsimp [a]; omega
  have hleft₂ : (m + 2 + (k + 1)) / 2 = b + 1 := by dsimp [b]; omega
  have hright₁ : (m + (k + 1) + 1) / 2 = a := by dsimp [a]; omega
  have hright₂ : (m + (k + 1)) / 2 = b := by dsimp [b]; omega
  unfold term
  rw [hleft₁, hleft₂, hright₁, hright₂, rook_pascal a b k ha hb, hcoeff]

private theorem normalized_step (m : ℕ) :
    normalized (m + 2) = (m + 2) * normalized (m + 1) + normalized m := by
  have hsum :
      (∑ k ∈ Finset.range (m + 2), term (m + 2) (k + 1)) =
        ∑ k ∈ Finset.range (m + 2), (term m (k + 1) + (m + 2) * term (m + 1) k) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact term_step m k (by have := Finset.mem_range.mp hk; omega)
  have hshift : (∑ k ∈ Finset.range (m + 2), term m (k + 1)) + 1 = normalized m := by
    rw [Finset.sum_range_succ (fun k => term m (k + 1)) (m + 1),
      term_outside m (m + 1 + 1) (by omega), add_zero,
      Finset.sum_range_succ (fun k => term m (k + 1)) m,
      term_outside m (m + 1) (by omega), add_zero]
    simpa only [normalized, term_zero] using (Finset.sum_range_succ' (term m) m).symm
  calc
    normalized (m + 2) = (∑ k ∈ Finset.range (m + 2), term (m + 2) (k + 1)) + 1 := by
      simpa only [normalized, term_zero] using (Finset.sum_range_succ' (term (m + 2)) (m + 2))
    _ = (m + 2) * normalized (m + 1) +
          ((∑ k ∈ Finset.range (m + 2), term m (k + 1)) + 1) := by
      rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum]
      unfold normalized
      ac_rfl
    _ = _ := by rw [hshift]

private theorem normalized_eq_continuant : ∀ m : ℕ, normalized m = continuant (m + 1)
  | 0 => by
    first
    | rfl
    | norm_num [normalized, Finset.sum_range_succ, term, rookNumber, continuant, Nat.choose]
  | 1 => by
    first
    | rfl
    | norm_num [normalized, Finset.sum_range_succ, term, rookNumber, continuant, Nat.choose]
  | m + 2 => by
    rw [normalized_step, normalized_eq_continuant (m + 1), normalized_eq_continuant m] <;>
      simp only [continuant]

end OMA.A096121Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a096121.main := by
  intro m
  rw [OMA.A096121Proof.card_walk, OMA.A096121Proof.normalized_eq_continuant]

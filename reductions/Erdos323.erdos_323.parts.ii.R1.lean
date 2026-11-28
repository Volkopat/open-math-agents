import FormalConjectures.ErdosProblems.«323»

/-!
# Erdős 323 (ii): split by the number of summands
Credit: @jarrettbranch

`f k m x` counts the integers `≤ x` that are sums of `m` nonnegative `k`th powers; the target
asks for `f k m x ≫ x ^ (m / k)` whenever `1 ≤ m < k`.

* `m = 1` is proved here in full: the `k`th powers `0 ^ k, 1 ^ k, …, a ^ k` with
  `a = ⌊x ^ (1 / k)⌋` are distinct and `≤ x`, so `f k 1 x ≥ a + 1 > x ^ (1 / k)`.
* `H1`: the binary case `m = 2`, `k ≥ 3`: integers `≤ x` that are sums of two `k`th powers.
  This is the case of numbers represented by the binary form `X ^ k + Y ^ k`, where results
  of Erdős–Mahler type are available (at least when that form is irreducible).
* `H2`: `3 ≤ m < k`, the open core.
-/

namespace OMA.R_Erdos323_erdos_323_parts_ii_R1

open Filter Asymptotics

/-- Sums of two `k`th powers, `k ≥ 3`: `f k 2 x ≫ x ^ (2 / k)`. -/
def H1 : Prop :=
  ∀ k : ℕ, 2 < k →
    (fun (x : ℕ) ↦ (x : ℝ) ^ ((2 : ℝ) / (k : ℝ))) =O[atTop]
      (fun (x : ℕ) ↦ (Erdos323.f k 2 x : ℝ))

/-- Sums of `m` `k`th powers with `3 ≤ m < k`: `f k m x ≫ x ^ (m / k)`. -/
def H2 : Prop :=
  ∀ k m : ℕ, 3 ≤ m → m < k →
    (fun (x : ℕ) ↦ (x : ℝ) ^ ((m : ℝ) / (k : ℝ))) =O[atTop]
      (fun (x : ℕ) ↦ (Erdos323.f k m x : ℝ))

theorem main : H1 → H2 → type_of% @Erdos323.erdos_323.parts.ii := by
  intro h1 h2 k m hm1 hmk
  rcases (by omega : m = 1 ∨ m = 2 ∨ 3 ≤ m) with h | h | h
  · subst h
    have hk0 : k ≠ 0 := by omega
    -- pointwise bound x ^ (1 / k) ≤ f k 1 x
    have hpt : ∀ x : ℕ, (x : ℝ) ^ (((1 : ℕ) : ℝ) / (k : ℝ)) ≤ (Erdos323.f k 1 x : ℝ) := by
      intro x
      rw [Nat.cast_one, one_div]
      set r : ℝ := (x : ℝ) ^ ((k : ℝ)⁻¹) with hr
      have hr0 : 0 ≤ r := by positivity
      set a : ℕ := ⌊r⌋₊ with ha
      have hlt : r < (a : ℝ) + 1 := Nat.lt_floor_add_one r
      have hak : a ^ k ≤ x := by
        have h1' : (a : ℝ) ≤ r := Nat.floor_le hr0
        have h2' : (a : ℝ) ^ k ≤ r ^ k := by gcongr
        have h3' : r ^ k = (x : ℝ) := Real.rpow_inv_natCast_pow (Nat.cast_nonneg x) hk0
        rw [h3'] at h2'
        exact_mod_cast h2'
      -- the k-th powers 0^k, …, a^k all lie in the counted set
      have hsub : (((Finset.range (a + 1)).image (fun j : ℕ => j ^ k) : Finset ℕ) : Set ℕ) ⊆
          {n : ℕ | n ≤ x ∧ ∃ (v : Fin 1 → ℕ), n = ∑ i, v i ^ k} := by
        intro n hn
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hn
        obtain ⟨j, hj, rfl⟩ := hn
        refine ⟨le_trans (Nat.pow_le_pow_left (by omega) k) hak, fun _ => j, ?_⟩
        simp
      have hfin : {n : ℕ | n ≤ x ∧ ∃ (v : Fin 1 → ℕ), n = ∑ i, v i ^ k}.Finite :=
        (Set.finite_Iic x).subset (fun n hn => hn.1)
      have hcard : a + 1 ≤ Erdos323.f k 1 x := by
        have h := Set.ncard_le_ncard hsub hfin
        rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ (Nat.pow_left_injective hk0),
          Finset.card_range] at h
        exact h
      have hcardR : (a : ℝ) + 1 ≤ (Erdos323.f k 1 x : ℝ) := by exact_mod_cast hcard
      linarith
    refine IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (Nat.cast_nonneg _), one_mul]
    exact hpt x
  · subst h
    exact h1 k hmk
  · exact h2 k m h hmk

end OMA.R_Erdos323_erdos_323_parts_ii_R1

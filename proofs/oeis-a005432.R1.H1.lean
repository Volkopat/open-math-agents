import OMAReductions.R_oeis_a005432_R1

/-!
# The lower bound for A005432

A binary matrix determines the graph of a linear map. The ambient vector group acts
faithfully by swapping disjoint pairs of points. The finite bound then gives the
normalized-log lower inequality.
-/

namespace OMA.A005432Lower

open Filter OMA.S_oeis_a005432
open scoped Topology

private abbrev Vec (k : ℕ) := Fin k → ZMod 2
private abbrev Point (k : ℕ) := (Fin k ⊕ Fin k) × ZMod 2

private def coordinate {k : ℕ} (u : Vec k × Vec k) (i : Fin k ⊕ Fin k) : ZMod 2 :=
  Sum.elim u.1 u.2 i

private def pairSwap (k : ℕ) : Multiplicative (Vec k × Vec k) →* Equiv.Perm (Point k) where
  toFun u :=
    { toFun := fun x => (x.1, x.2 + coordinate u.toAdd x.1)
      invFun := fun x => (x.1, x.2 - coordinate u.toAdd x.1)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  map_one' := by
    apply Equiv.ext
    rintro ⟨i, b⟩
    cases i <;> simp [coordinate]
  map_mul' u v := by
    apply Equiv.ext
    rintro ⟨i, b⟩
    cases i <;>
      simp [coordinate, Equiv.Perm.mul_apply, add_left_comm, add_comm]

private theorem pairSwap_injective (k : ℕ) : Function.Injective (pairSwap k) := by
  intro u v h
  apply Multiplicative.toAdd.injective
  apply Prod.ext
  · funext i
    have hi := congrArg (fun σ : Equiv.Perm (Point k) => (σ (Sum.inl i, 0)).2) h
    change 0 + u.toAdd.1 i = 0 + v.toAdd.1 i at hi
    simpa using hi
  · funext i
    have hi := congrArg (fun σ : Equiv.Perm (Point k) => (σ (Sum.inr i, 0)).2) h
    change 0 + u.toAdd.2 i = 0 + v.toAdd.2 i at hi
    simpa using hi

private noncomputable def pointEmbedding {k n : ℕ} (h : 4 * k ≤ n) : Point k ↪ Fin n :=
  (Fintype.equivFin (Point k)).toEmbedding.trans
    (Fin.castLEEmb (by
      simp [Point, ZMod.card]
      omega))

private noncomputable def graphSubgroup {k : ℕ} (A : Matrix (Fin k) (Fin k) (ZMod 2)) :
    Subgroup (Multiplicative (Vec k × Vec k)) :=
  (Matrix.toLin' A).toAddMonoidHom.graph.toSubgroup

private theorem graphSubgroup_injective (k : ℕ) :
    Function.Injective (graphSubgroup (k := k)) := by
  intro A B h
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  have hm : Multiplicative.ofAdd (x, Matrix.toLin' A x) ∈ graphSubgroup A := rfl
  rw [h] at hm
  exact hm.symm

/-- With two disjoint pairs of points per row, binary matrices give distinct subgroups. -/
theorem finite_lower (n : ℕ) : 2 ^ ((n / 4) * (n / 4)) ≤ a n := by
  let k := n / 4
  have hk : 4 * k ≤ n := by
    simpa [k, Nat.mul_comm] using Nat.div_mul_le_self n 4
  let e := pointEmbedding hk
  let f := (Equiv.Perm.viaEmbeddingHom e).comp (pairSwap k)
  have hf : Function.Injective f :=
    (Equiv.Perm.viaEmbeddingHom_injective e).comp (pairSwap_injective k)
  let matrices : Matrix (Fin k) (Fin k) (ZMod 2) ↪ Subgroup (Equiv.Perm (Fin n)) :=
    ⟨fun A => (graphSubgroup A).map f, (Subgroup.map_injective hf).comp
      (graphSubgroup_injective k)⟩
  have hcard := Nat.card_le_card_of_injective matrices matrices.injective
  have hmat : Nat.card (Matrix (Fin k) (Fin k) (ZMod 2)) = 2 ^ (k * k) := by
    simp [Nat.card_eq_fintype_card, Matrix, ZMod.card, pow_mul]
  rw [hmat] at hcard
  exact hcard

private theorem tendsto_div_four :
    Tendsto (fun n : ℕ => ((n / 4 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 (1 / 4 : ℝ)) := by
  have remainder : Tendsto (fun n : ℕ => ((n % 4 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_)
      (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ))
    have hmod : (n % 4 : ℕ) ≤ 4 := (Nat.mod_lt _ (by decide)).le
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmod) (by positivity)
  have h : Tendsto (fun n : ℕ => (1 - ((n % 4 : ℕ) : ℝ) / (n : ℝ)) / 4)
      atTop (𝓝 (1 / 4 : ℝ)) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using (hone.sub remainder).div_const (4 : ℝ)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hdiv : ((n % 4 : ℕ) : ℝ) + 4 * ((n / 4 : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast (Nat.mod_add_div n 4)
  field_simp
  linarith

/-- The finite graph-subgroup construction gives the lower half of the normalized limit. -/
theorem proveH1 : OMA.R_oeis_a005432_R1.H1 := by
  intro b hb
  have hlim : Tendsto (fun n : ℕ => Real.log 2 * (((n / 4 : ℕ) : ℝ) / (n : ℝ)) ^ 2)
      atTop (𝓝 (Real.log 2 / 16)) := by
    have hconst : Real.log 2 * (1 / 4 : ℝ) ^ 2 = Real.log 2 / 16 := by ring
    rw [← hconst]
    exact (tendsto_div_four.pow 2).const_mul (Real.log 2)
  filter_upwards [(tendsto_order.1 hlim).1 b hb] with n hn
  refine hn.trans_le ?_
  have hpow : (2 : ℝ) ^ ((n / 4) * (n / 4)) ≤ (a n : ℝ) := by
    exact_mod_cast finite_lower n
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Nat.cast_mul] at hlog
  rw [div_pow, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [mul_comm (Real.log 2), pow_two]
  exact hlog

end OMA.A005432Lower

theorem OMA.solution : OMA.R_oeis_a005432_R1.H1 :=
  OMA.A005432Lower.proveH1

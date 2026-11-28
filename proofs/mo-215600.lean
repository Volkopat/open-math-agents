import OMAStatements.S_mo_215600

open Finset OMA.S_mo_215600

private abbrev Vertex := Fin 4 × Bool × Fin 7

private def bipartiteCopies : SimpleGraph Vertex where
  Adj v w := v.1 = w.1 ∧ v.2.1 ≠ w.2.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

private instance : DecidableRel bipartiteCopies.Adj :=
  fun v w => inferInstanceAs (Decidable (v.1 = w.1 ∧ v.2.1 ≠ w.2.1))

private def opposite (v : Vertex) : Fin 7 ↪ Vertex where
  toFun j := (v.1, !v.2.1, j)
  inj' := fun _ _ h => congrArg (fun w : Vertex => w.2.2) h

private theorem neighbors (v : Vertex) :
    univ.filter (bipartiteCopies.Adj v) = univ.map (opposite v) := by
  ext w
  simp only [mem_filter, mem_univ, true_and, mem_map]
  change v.1 = w.1 ∧ v.2.1 ≠ w.2.1 ↔ ∃ i, (v.1, !v.2.1, i) = w
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨w.2.2, Prod.ext h₁ (Prod.ext ?_ rfl)⟩
    cases hv : v.2.1 <;> cases hw : w.2.1 <;> simp_all
  · rintro ⟨i, rfl⟩
    exact ⟨rfl, by cases v.2.1 <;> simp⟩

private noncomputable def weight (_ : Vertex) : ℝ := 1 / 8

private def active (v : Vertex) : ℝ := if v.2.1 then 1 else 0

private theorem weightClosed (v : Vertex) :
    closedSum bipartiteCopies weight v = 1 := by
  rw [closedSum, neighbors, sum_map]
  norm_num [weight]

private theorem activeClosed (v : Vertex) :
    closedSum bipartiteCopies (fun w => active w * weight w) v =
      if v.2.1 then 1 / 8 else 7 / 8 := by
  rw [closedSum, neighbors, sum_map]
  cases h : v.2.1 <;> norm_num [active, weight, opposite, h]

private theorem weightedSum :
    (∑ v : Vertex, weight v) = 7 := by
  simp only [weight, sum_const, card_univ, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  norm_num

private theorem sumSides (f : Bool → ℝ) :
    ∑ v : Vertex, f v.2.1 = 28 * (f false + f true) := by
  simp only [Fintype.sum_prod_type, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, Fintype.sum_bool]
  ring

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_215600.main) := by
  intro claimed
  have h := claimed Vertex bipartiteCopies weight active 7 (by decide)
    (fun _ => by norm_num [weight, Set.mem_Icc])
    (fun v => by cases h : v.2.1 <;> norm_num [active, h, Set.mem_Icc])
    weightClosed weightedSum (Real.log 2) (Real.log_pos (by norm_num))
  have hlog : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  rw [hlog] at h
  have hrewrite : (∑ v : Vertex,
      weight v * Real.exp (-(2 - 1) *
        closedSum bipartiteCopies (fun w => active w * weight w) v + Real.log 2 * active v)) =
      28 * ((1 / 8) * Real.exp (-(7 / 8)) + (1 / 8) * (Real.exp (-(1 / 8)) * 2)) := by
    simp_rw [activeClosed]
    let f (b : Bool) := (1 / 8 : ℝ) * Real.exp (-(2 - 1) *
      (if b then 1 / 8 else 7 / 8) + Real.log 2 * (if b then 1 else 0))
    change (∑ v : Vertex, f v.2.1) = _
    rw [sumSides]
    norm_num [f, Real.exp_add, hlog]
  rw [hrewrite] at h
  have hone : (7 / 8 : ℝ) ≤ Real.exp (-(1 / 8)) := by
    linarith [Real.add_one_le_exp (-(1 / 8 : ℝ))]
  have htwo : (1 / 4 : ℝ) < Real.exp (-(7 / 8)) := by
    calc
      (1 / 4 : ℝ) < (Real.exp 1)⁻¹ := by
        have hmul : Real.exp 1 * (1 / 4) < 1 := by
          linarith [Real.exp_one_lt_three]
        simpa only [mul_one] using (lt_inv_mul_iff₀ (Real.exp_pos 1)).2 hmul
      _ = Real.exp (-1) := (Real.exp_neg _).symm
      _ < Real.exp (-(7 / 8)) := Real.exp_lt_exp.mpr (by norm_num)
  push_cast at h
  linarith only [h, hone, htwo]

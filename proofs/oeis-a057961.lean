import OMAStatements.S_oeis_a057961

-- Credit: @oh-meh
open OMA.S_oeis_a057961 Finset

private def normSq (p : ℕ × ℕ) : ℕ := p.1^2 + p.2^2

private def ball (t : ℕ) := ((Iic t) ×ˢ (Iic t)).filter (fun p : ℕ × ℕ => normSq p ≤ t)

private theorem ball_mem (p : ℕ × ℕ) (t : ℕ) : p ∈ ball t ↔ normSq p ≤ t := by
  simp only [ball, mem_filter, mem_product, mem_Iic, and_iff_right_iff_imp]
  unfold normSq
  intro h
  constructor <;> nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) p.1,
    Nat.le_self_pow (by decide : 2 ≠ 0) p.2]

private theorem quadrant_ball (n : ℕ) : quadrantCount n = (ball (radiusSq n)).card := by
  let t := radiusSq n
  let e : {p : ℤ × ℤ // 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1^2 + p.2^2 ≤ (t : ℤ)} ≃
      ↥(ball t) := {
    toFun := fun ⟨⟨x,y⟩, hx, hy, h⟩ => ⟨(x.toNat,y.toNat), (ball_mem _ _).2 (by
      change x.toNat^2 + y.toNat^2 ≤ t
      exact_mod_cast (show (x.toNat : ℤ)^2 + (y.toNat : ℤ)^2 ≤ (t : ℤ) by
        simpa [Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy] using h))⟩
    invFun := fun ⟨⟨x,y⟩,h⟩ => ⟨((x : ℤ), (y : ℤ)), by
      refine ⟨by positivity, by positivity, ?_⟩
      change (x : ℤ)^2 + (y : ℤ)^2 ≤ (t : ℤ)
      have hb : x^2 + y^2 ≤ t := (ball_mem _ _).1 h
      exact_mod_cast hb⟩
    left_inv := by rintro ⟨⟨x,y⟩,hx,hy,h⟩; simp [Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy]
    right_inv := by rintro ⟨⟨x,y⟩,h⟩; simp
  }
  unfold quadrantCount
  simpa only [Nat.card_eq_fintype_card (α := ↥(ball t)), Fintype.card_coe, t] using Nat.card_congr e

private theorem infiniteRadii : (Set.ofPred IsSumTwoSq).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro k
  exact ⟨(k+1)^2, ⟨k+1, 0, by simp⟩, by nlinarith⟩

private theorem shell (u t : ℕ) (hu : u ≤ t) :
    ((ball t).filter fun p => normSq p = u).card = Nat.card {p : ℕ × ℕ // normSq p = u} := by
  let e : ↥((ball t).filter fun p => normSq p = u) ≃ {p : ℕ × ℕ // normSq p = u} :=
    Equiv.subtypeEquivRight fun p => by
      simp only [mem_filter, ball_mem]
      exact ⟨And.right, fun h => ⟨h ▸ hu, h⟩⟩
  simpa only [Nat.card_eq_fintype_card (α := ↥((ball t).filter fun p => normSq p = u)),
    Fintype.card_coe] using Nat.card_congr e

theorem OMA.solution : type_of% @OMA.S_oeis_a057961.main := by
  intro n _
  rw [quadrant_ball]
  let k := n-1
  let r := Nat.nth IsSumTwoSq
  let J := range (k+1)
  have hr : StrictMono r := Nat.nth_strictMono infiniteRadii
  change (ball (r k)).card = ∑ j ∈ J, Nat.card {p : ℕ × ℕ // normSq p = r j}
  rw [card_eq_sum_card_fiberwise (f := normSq) (t := J.image r) (by
    intro p hp
    obtain ⟨j,hj⟩ := Nat.subset_range_nth (p := IsSumTwoSq)
      (show IsSumTwoSq (normSq p) from ⟨p.1,p.2,rfl⟩)
    exact mem_image.mpr ⟨j, mem_range.mpr (Nat.lt_succ_of_le
      (hr.le_iff_le.mp (by simpa [r, hj] using (ball_mem _ _).1 hp))), hj⟩)]
  rw [sum_image (fun _ _ _ _ h => hr.injective h)]
  apply sum_congr rfl
  intro j hj
  exact shell _ _ (hr.monotone (Nat.le_of_lt_succ (mem_range.mp hj)))

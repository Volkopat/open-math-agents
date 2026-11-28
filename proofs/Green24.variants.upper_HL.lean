import FormalConjectures.GreensOpenProblems.«24»

/-! Encode a progression by two points on the same side of the median. -/

open Green24 Green24.variants Filter

theorem OMA.solution : type_of% @Green24.variants.upper_HL := by
  unfold gamma
  refine limsup_le_of_le (isCoboundedUnder_le_of_le _ (x := 0) fun _ => by positivity) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hmax : max013AffineTranslates n ≤ 3 * n ^ 2 / 4 := by
    refine csSup_le ⟨_, (Finset.range n).image Int.ofNat,
      by simp [Finset.card_image_of_injective _ Int.ofNat_injective], rfl⟩ ?_
    rintro _ ⟨A, ha, rfl⟩
    refine (Nat.le_div_iff_mul_le (by decide)).2 ?_
    let i : Fin n := ⟨n / 2, by omega⟩
    let e := A.orderEmbOfFin ha
    let c := e i
    let L := (Finset.Iio i).map e.toEmbedding
    let U := (Finset.Ici i).map e.toEmbedding
    let enc (p : ℤ × ℤ) : ℤ × ℤ :=
      if p.2 < c then (if p.1 < p.2 then p else (p.2, p.1 + 3 * (p.2 - p.1)))
      else (if p.1 < p.2 then (p.2, p.1 + 3 * (p.2 - p.1)) else p)
    have sides {z} (hz : z ∈ A) : (z < c → z ∈ L) ∧ (c ≤ z → z ∈ U) := by
      obtain ⟨j, rfl⟩ := (A.range_orderEmbOfFin ha ▸ hz : z ∈ Set.range e)
      exact ⟨fun h => Finset.mem_map.2 ⟨j, Finset.mem_Iio.2 (e.lt_iff_lt.1 h), rfl⟩,
        fun h => Finset.mem_map.2 ⟨j, Finset.mem_Ici.2 (e.le_iff_le.1 h), rfl⟩⟩
    have maps : Set.MapsTo enc ((A ×ˢ A).filter fun p => p.1 ≠ p.2 ∧ p.1 + 3 * (p.2 - p.1) ∈ A)
        ((L ×ˢ L ∪ U ×ˢ U : Finset _) : Set _) := by
      rintro ⟨x, y⟩ hp
      obtain ⟨hp, hxy, hz⟩ := Finset.mem_filter.mp hp
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
      by_cases h : y < c <;> by_cases h' : x < y <;> simp only [enc, h, h', if_true, if_false]
      · exact Finset.mem_union_left _ (Finset.mem_product.2 ⟨(sides hx).1 (by omega), (sides hy).1 h⟩)
      · exact Finset.mem_union_left _ (Finset.mem_product.2 ⟨(sides hy).1 h, (sides hz).1 (by omega)⟩)
      · exact Finset.mem_union_right _ (Finset.mem_product.2 ⟨(sides hy).2 (by omega), (sides hz).2 (by omega)⟩)
      · exact Finset.mem_union_right _ (Finset.mem_product.2 ⟨(sides hx).2 (by omega), (sides hy).2 (by omega)⟩)
    have inj : Set.InjOn enc ((A ×ˢ A).filter fun p => p.1 ≠ p.2 ∧ p.1 + 3 * (p.2 - p.1) ∈ A) := by
      rintro ⟨x, y⟩ hx ⟨u, v⟩ hu he
      have h1 := (Finset.mem_filter.mp hx).2.1; have h2 := (Finset.mem_filter.mp hu).2.1
      dsimp only [enc] at he; split_ifs at he <;> simp only [Prod.mk.injEq] at * <;> omega
    have bound := (Finset.card_le_card_of_injOn enc maps inj).trans (Finset.card_union_le _ _)
    simp only [Finset.card_product, L, U, Finset.card_map, Fin.card_Iio, Fin.card_Ici, i] at bound
    have hq : n = 2 * (n / 2) ∨ n = 2 * (n / 2) + 1 := by omega
    rcases hq with h | h
    · have hh : n - n / 2 = n / 2 := by omega
      rw [hh] at bound; nlinarith [congrArg (· ^ 2) h]
    · have hh : n - n / 2 = n / 2 + 1 := by omega
      rw [hh] at bound; nlinarith [congrArg (· ^ 2) h, show 1 ≤ n / 2 by omega]
  have hr : 4 * (max013AffineTranslates n : ℝ) ≤ 3 * (n : ℝ) ^ 2 := by
    exact_mod_cast (show 4 * max013AffineTranslates n ≤ 3 * n ^ 2 by omega)
  rw [div_le_iff₀ (by positivity)]; linarith

import FormalConjectures.ErdosProblems.«650»

/-! A pair of consecutive multiples identifies its common difference. -/

theorem OMA.solution : type_of% @Erdos650.erdos_650.variants.erdos_suranyi := by
  classical
  intro m
  let k := ⌈Real.sqrt m⌉₊
  apply (Nat.le_ceil (Real.sqrt (m : ℝ))).trans
  exact_mod_cast (show k ≤ Erdos650.f m from by
    unfold Erdos650.f
    refine le_csSup ⟨m, fun r hr => ?_⟩ fun N A hA hcard x hx => ?_
    · obtain ⟨a, _, ha, _, hA, _⟩ := hr m (Finset.Icc 1 m) (fun _ h => h) (by simp) 1 le_rfl
      simpa using Fintype.card_le_of_injective (fun i => (⟨a i, hA i⟩ : ↥(Finset.Icc 1 m)))
        (fun _ _ h => ha (congrArg Subtype.val h))
    · let u (a : ℕ) := a * (⌊x⌋₊ / a) + a
      let v (a : ℕ) := if a = N then u a else u a + a
      have hub {a} (ha : a ∈ A) : x < u a ∧ (u a : ℝ) ≤ x + a := by
        have hp := (Finset.mem_Icc.mp (hA ha)).1
        have := Nat.mod_add_div ⌊x⌋₊ a; have := Nat.mod_lt ⌊x⌋₊ hp
        have h1 : (⌊x⌋₊ + 1 : ℝ) ≤ u a := by exact_mod_cast (show ⌊x⌋₊ + 1 ≤ u a by dsimp [u]; omega)
        have h2 : (u a : ℝ) ≤ ⌊x⌋₊ + a := by exact_mod_cast (show u a ≤ ⌊x⌋₊ + a by dsimp [u]; omega)
        exact ⟨lt_of_lt_of_le (Nat.lt_floor_add_one x) h1,
          h2.trans (by linarith [Nat.floor_le (by linarith : 0 ≤ x)])⟩
      have hcount : m ≤ (A.image u).card * (A.image v).card := by
        rw [← hcard, ← Finset.card_product]
        refine Finset.card_le_card_of_injOn (fun a => (u a, v a))
          (fun a ha => Finset.mem_product.2 ⟨Finset.mem_image_of_mem u ha, Finset.mem_image_of_mem v ha⟩)
          fun a ha b hb he => ?_
        have hu : u a = u b := congrArg Prod.fst he
        have hv : v a = v b := congrArg Prod.snd he
        have := (Finset.mem_Icc.mp (hA ha)).1; have := (Finset.mem_Icc.mp (hA hb)).1
        dsimp [v] at hv; split_ifs at hv <;> omega
      have hup a (ha : a ∈ A) : (u a : ℝ) ∈ Set.Ioo x (x + 2 * N) := by
        have ⟨h1, h2⟩ := hub ha; have ⟨hp, hl⟩ := Finset.mem_Icc.mp (hA ha)
        exact ⟨h1, by linarith [show (0 : ℝ) < a by exact_mod_cast hp, show (a : ℝ) ≤ N by exact_mod_cast hl]⟩
      have hvp a (ha : a ∈ A) : (v a : ℝ) ∈ Set.Ioo x (x + 2 * N) := by
        by_cases h : a = N
        · simpa [v, h] using hup a ha
        · have ⟨h1, h2⟩ := hub ha; have ⟨hp, hl⟩ := Finset.mem_Icc.mp (hA ha)
          simp only [v, if_neg h, Nat.cast_add, Set.mem_Ioo]
          constructor <;> linarith [show (0 : ℝ) < a by exact_mod_cast hp,
            show (a : ℝ) < N by exact_mod_cast lt_of_le_of_ne hl h]
      have hu_dvd a : a ∣ u a := dvd_add (dvd_mul_right _ _) dvd_rfl
      have hv_dvd a : a ∣ v a := by dsimp [v]; split_ifs; exacts [hu_dvd a, dvd_add (hu_dvd a) dvd_rfl]
      have make (g : ℕ → ℕ) (hbig : m ≤ (A.image g).card ^ 2)
          (hI : ∀ a ∈ A, (g a : ℝ) ∈ Set.Ioo x (x + 2 * N)) (hd : ∀ a, a ∣ g a) :
          ∃ a b : Fin k → ℕ, Function.Injective a ∧ Function.Injective b ∧
            (∀ i, a i ∈ A) ∧ (∀ i, (b i : ℝ) ∈ Set.Ioo x (x + 2 * N)) ∧ (∀ i, a i ∣ b i) := by
        have hk : k ≤ (A.image g).card :=
          Nat.ceil_le.2 ((Real.sqrt_le_left (by positivity)).2 (by exact_mod_cast hbig))
        let e : Fin k ↪ ↥(A.image g) :=
          (Fin.castLEEmb (by simpa using hk)).trans (Fintype.equivFin _).symm.toEmbedding
        choose a ha hab using fun i => Finset.mem_image.mp (e i).2
        have hga : Function.Injective (g ∘ a) := fun i j he =>
          e.injective (Subtype.ext (by simpa [hab] using he))
        exact ⟨a, g ∘ a, fun _ _ h => hga (congrArg g h), hga, ha, fun i => hI _ (ha i), fun i => hd _⟩
      rcases le_total (A.image u).card (A.image v).card with h | h
      · exact make v (hcount.trans (by simpa [sq] using Nat.mul_le_mul_right _ h)) hvp hv_dvd
      · exact make u (hcount.trans (by simpa [sq] using Nat.mul_le_mul_left _ h)) hup hu_dvd)

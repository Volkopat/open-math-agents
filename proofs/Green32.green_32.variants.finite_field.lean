import FormalConjectures.GreensOpenProblems.«32»

/-! Shorter proof of `Green32.green_32.variants.finite_field` via Sanders' averaging argument. -/

open Module

private lemma hole {k m b : ℕ} (A : Finset (𝔽₂ (k + m))) (hc : A.card ≤ 2 ^ k * b) (hm : b < m) :
    Green32.HasCosetHole A (2 ^ (m - 1)) := by
  classical
  let hd := LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castAdd m : Fin k → Fin (k + m))
  let tl := LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.natAdd k : Fin m → Fin (k + m))
  obtain ⟨y, -, hy⟩ := Finset.exists_card_fiber_le_of_card_le_mul (f := hd) (s := A)
    (t := Finset.univ) Finset.univ_nonempty (n := b) (by simpa [𝔽₂, 𝔽, ZMod.card] using hc)
  let S := Submodule.span (ZMod 2) (((A.filter fun x => hd x = y).image tl : Finset _) : Set (𝔽₂ m))
  have hsm : finrank (ZMod 2) S < m :=
    (finrank_span_finset_le_card _).trans_lt ((Finset.card_image_le.trans hy).trans_lt hm)
  obtain ⟨f, hf, hker⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr fun h =>
    hsm.ne (by rw [h, finrank_top]; simp [𝔽₂, 𝔽]))
  obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hf
  let P := hd.prod (f.comp tl)
  let v : 𝔽₂ (k + m) := Fin.append y z
  have hv : P v = (y, f z) :=
    Prod.ext (by ext; simp [P, hd, v]) (congrArg f (by ext; simp [tl, v]))
  refine ⟨P.ker, v, ?_, fun w hw => ?_⟩
  · rw [natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    refine Nat.pow_le_pow_right (by decide) ?_
    have := P.finrank_range_add_finrank_ker.trans (by simp : finrank (ZMod 2) (𝔽₂ (k + m)) = k + m)
    have := (Submodule.finrank_le P.range).trans_eq
      (by simp [finrank_prod] : finrank (ZMod 2) (𝔽₂ k × ZMod 2) = k + 1)
    change m - 1 ≤ finrank (ZMod 2) P.ker; omega
  · have heq : P (v + w.val) = (y, f z) := by
      rw [map_add, show P w.val = 0 from w.2, add_zero, hv]
    exact hz ((congrArg Prod.snd heq).symm.trans (hker (Submodule.subset_span
      (Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨hw, congrArg Prod.fst heq⟩, rfl⟩))))

theorem OMA.solution : type_of% @Green32.green_32.variants.finite_field := by
  classical
  filter_upwards [Filter.eventually_ge_atTop 2048] with n hn A hA
  let k := n / 2 - 9; let m := n - k
  have hn' : n = k + m := by omega
  have hdim : 1024 < m := by omega
  have hsqrt : Real.sqrt (2 ^ n : ℝ) ≤ 2 ^ (k + 10) := Real.sqrt_le_iff.mpr
    ⟨by positivity, by rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)⟩
  have hsize : A.card ≤ 2 ^ k * 1024 :=
    hA ▸ Nat.floor_le_of_le (by norm_num [pow_add] at hsqrt ⊢; exact hsqrt)
  have htarget : ⌊100 * Real.sqrt (2 ^ n : ℝ)⌋₊ ≤ 2 ^ (m - 1) := Nat.floor_le_of_le <| by
    push_cast
    calc 100 * Real.sqrt (2 ^ n : ℝ) ≤ 100 * 2 ^ (k + 10) := by gcongr
      _ ≤ 2 ^ (k + 17) := by
          rw [show k + 17 = (k + 10) + 7 by omega, pow_add (2 : ℝ) (k + 10) 7]
          linarith [show (0 : ℝ) ≤ 2 ^ (k + 10) by positivity]
      _ ≤ 2 ^ (m - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  obtain ⟨W, v, hW, hv⟩ : Green32.HasCosetHole A (2 ^ (m - 1)) := by
    revert A; generalize k = k' at hn' ⊢; generalize m = m' at hn' hdim ⊢; subst n
    exact fun A _ hsize => hole A hsize hdim
  exact ⟨W, v, htarget.trans hW, hv⟩

import OMAReductions.R_Green24_variants_conjecture_R1

/-! In `{0, …, 3m - 1}` the pairs `(3a + r, 2a + b + r)` with `r < 3`, `a ≠ b` below `m` are
solutions: the third point is `3b + r`. There are `3 m (m - 1)` of them, so the ratio at `n = 3m`
is `(m - 1) / (3 m)`, which tends to `1/3`. The outline of the limsup step follows the merged
proof of `Green24.variants.lower_HL` (upstream pull request 162, by @Deldor14). -/

open Green24 Green24.variants Filter

namespace OMA.Trisect

lemma interval_count (m : ℕ) : 3 * (m * (m - 1)) ≤ max013AffineTranslates (3 * m) := by
  let A : Finset ℤ := Finset.Ico 0 (3 * (m : ℤ))
  have size : A.card = 3 * m := by simp [A, Int.card_Ico]; omega
  let skip (a j : ℕ) : ℕ := if j < a then j else j + 1
  let f (u : Fin 3 × Fin m × Fin (m - 1)) : ℤ × ℤ :=
    (3 * (u.2.1.val : ℤ) + u.1.val,
      2 * (u.2.1.val : ℤ) + (skip u.2.1.val u.2.2.val : ℕ) + u.1.val)
  have hskip (a j : ℕ) (ha : a < m) (hj : j < m - 1) : skip a j ≠ a ∧ skip a j < m := by
    dsimp only [skip]
    split_ifs <;> omega
  have hinj (a j j' : ℕ) (h : skip a j = skip a j') : j = j' := by
    dsimp only [skip] at h
    split_ifs at h <;> omega
  have mem (u : Fin 3 × Fin m × Fin (m - 1)) :
      f u ∈ (A ×ˢ A).filter (fun (x, y) => x ≠ y ∧ x + 3 * (y - x) ∈ A) := by
    have hr := u.1.isLt
    have ha := u.2.1.isLt
    obtain ⟨h1, h2⟩ := hskip u.2.1.val u.2.2.val ha u.2.2.isLt
    simp only [Finset.mem_filter, Finset.mem_product, A, Finset.mem_Ico, f]
    omega
  let emb : (Fin 3 × Fin m × Fin (m - 1)) ↪
      ↥((A ×ˢ A).filter (fun (x, y) => x ≠ y ∧ x + 3 * (y - x) ∈ A)) :=
    ⟨fun u => ⟨f u, mem u⟩, by
      intro u v he
      have hh := congrArg Subtype.val he
      have h₁ := congrArg Prod.fst hh
      have h₂ := congrArg Prod.snd hh
      dsimp only [f] at h₁ h₂
      have hr := u.1.isLt
      have hr' := v.1.isLt
      have e1 : u.1.val = v.1.val := by omega
      have e2 : u.2.1.val = v.2.1.val := by omega
      have e3 : skip u.2.1.val u.2.2.val = skip v.2.1.val v.2.2.val := by omega
      rw [← e2] at e3
      have e4 := hinj _ _ _ e3
      exact Prod.ext (Fin.ext e1) (Prod.ext (Fin.ext e2) (Fin.ext e4))⟩
  have lower := Fintype.card_le_of_embedding emb
  have upper : ((A ×ˢ A).filter (fun (x, y) => x ≠ y ∧ x + 3 * (y - x) ∈ A)).card
      ≤ max013AffineTranslates (3 * m) := by
    apply le_csSup
    · refine ⟨(3 * m) ^ 2, ?_⟩
      rintro k ⟨B, hB, rfl⟩
      exact (Finset.card_filter_le _ _).trans_eq (by simp [hB, pow_two])
    · exact ⟨A, size, rfl⟩
  exact (by simpa using lower :
    3 * (m * (m - 1)) ≤ ((A ×ˢ A).filter (fun (x, y) => x ≠ y ∧ x + 3 * (y - x) ∈ A)).card).trans
    upper

end OMA.Trisect

theorem OMA.solution : OMA.R_Green24_variants_conjecture_R1.H2 := by
  show (1 : ℝ) / 3 ≤ gamma
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rw [← sub_le_iff_le_add]
  unfold gamma
  apply le_limsup_of_frequently_le
  · apply frequently_atTop.mpr
    intro N
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
    let m := N + k + 1
    refine ⟨3 * m, by dsimp only [m]; omega, ?_⟩
    have hm1 : 1 ≤ m := by dsimp only [m]; omega
    have hm : (0 : ℝ) < m := by exact_mod_cast hm1
    have hkm : (k : ℝ) ≤ m := by exact_mod_cast (by dsimp only [m]; omega : k ≤ m)
    have hεm : 1 < ε * m := by
      have h1 : 1 < ε * k := by
        have := (div_lt_iff₀ hε).mp hk
        linarith
      nlinarith
    have hh : 3 * ((m : ℝ) * ((m : ℝ) - 1)) ≤ max013AffineTranslates (3 * m) := by
      have := OMA.Trisect.interval_count m
      have h2 : ((3 * (m * (m - 1)) : ℕ) : ℝ) ≤ (max013AffineTranslates (3 * m) : ℝ) := by
        exact_mod_cast this
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hm1] at h2
      simpa using h2
    push_cast
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  · refine ⟨1, ?_⟩
    change ∀ᶠ n : ℕ in atTop, (max013AffineTranslates n : ℝ) / (n : ℝ) ^ 2 ≤ 1
    apply Eventually.of_forall
    intro n
    by_cases hn : n = 0
    · simp [hn]
    have h : (max013AffineTranslates n : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast (upper_trivial (n := n))
    exact (div_le_one (by positivity)).mpr h

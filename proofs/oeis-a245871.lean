import OMAStatements.S_oeis_a245871

/-!
# OEIS A245871

Source: https://oeis.org/A245871 (OEIS Foundation, CC BY-SA 4.0).
The generating function and parity formulas are conjectures of Colin Barker
(November 4, 2018). The registered statement is credited to @clementtrecourt.
Proof: @grp06.

The two middle letters determine the set of admissible endpoint pairs.
The generating function follows by multiplying by its proposed denominator
and comparing coefficients.
-/

open Finset PowerSeries
open scoped BigOperators

namespace A245871Proof

open OMA.S_oeis_a245871 (a good)

private abbrev Letter (n : ℕ) := Fin (n + 1)

private def complement {n : ℕ} (b : Letter n) : Letter n :=
  ⟨n - b.val, by omega⟩

private theorem complement_spec {n : ℕ} (u b : Letter n) :
    u.val + b.val = n ↔ u = complement b := by
  have hb := b.isLt
  constructor
  · intro h
    apply Fin.ext
    change u.val = n - b.val
    omega
  · rintro rfl
    change n - b.val + b.val = n
    omega

private theorem complement_injective (n : ℕ) :
    Function.Injective (complement (n := n)) := by
  intro b c h
  have hv : n - b.val = n - c.val := congrArg Fin.val h
  have hb := b.isLt
  have hc := c.isLt
  apply Fin.ext
  omega

private def options {n : ℕ} (b c : Letter n) : Finset (Letter n) :=
  {complement b, complement c}

private def validEnds {n : ℕ} (b c : Letter n) (p : Letter n × Letter n) : Prop :=
  c = complement b ∨ (p.1 ∈ options b c ∧ p.2 ∈ options b c)

private instance {n : ℕ} (b c : Letter n) : DecidablePred (validEnds b c) :=
  fun p => by unfold validEnds; infer_instance

private theorem two_windows (P : ℕ → Prop) :
    (∀ i < 2, P i) ↔ P 0 ∧ P 1 := by
  constructor
  · intro h
    exact ⟨h 0 (by decide), h 1 (by decide)⟩
  · rintro ⟨h₀, h₁⟩ i hi
    have h : i = 0 ∨ i = 1 := by omega
    rcases h with rfl | rfl
    · exact h₀
    · exact h₁

private theorem window_pairs (P : ℕ → ℕ → Prop) :
    (∃ s < 3, ∃ t < 3, s < t ∧ P s t) ↔ P 0 1 ∨ P 0 2 ∨ P 1 2 := by
  constructor
  · rintro ⟨s, hs, t, ht, hst, hp⟩
    have h : (s = 0 ∧ t = 1) ∨ (s = 0 ∧ t = 2) ∨ (s = 1 ∧ t = 2) := by
      omega
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hp
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr hp)
  · rintro (h | h | h)
    · exact ⟨0, by decide, 1, by decide, by decide, h⟩
    · exact ⟨0, by decide, 2, by decide, by decide, h⟩
    · exact ⟨1, by decide, 2, by decide, by decide, h⟩

private theorem get_fin {n : ℕ} (x : Fin 4 → Letter n) (i : Fin 4) :
    OMA.S_oeis_a245871.get x i.val = (x i).val := by
  simp [OMA.S_oeis_a245871.get, i.isLt]

private theorem good_iff {n : ℕ} (x : Fin 4 → Letter n) :
    good x = true ↔ validEnds (x 1) (x 2) (x 0, x 3) := by
  let g := OMA.S_oeis_a245871.get x
  simp only [good, decide_eq_true_eq]
  change (∀ i < 2, ∃ s < 3, ∃ t < 3, s < t ∧ g (i + s) + g (i + t) = n) ↔ _
  rw [two_windows (fun i => ∃ s < 3, ∃ t < 3, s < t ∧ g (i + s) + g (i + t) = n),
    window_pairs (fun s t => g (0 + s) + g (0 + t) = n),
    window_pairs (fun s t => g (1 + s) + g (1 + t) = n)]
  change
    ((g 0 + g 1 = n ∨ g 0 + g 2 = n ∨ g 1 + g 2 = n) ∧
      (g 1 + g 2 = n ∨ g 1 + g 3 = n ∨ g 2 + g 3 = n)) ↔ _
  have h0 : g 0 = (x 0).val := get_fin x 0
  have h1 : g 1 = (x 1).val := get_fin x 1
  have h2 : g 2 = (x 2).val := get_fin x 2
  have h3 : g 3 = (x 3).val := get_fin x 3
  rw [h0, h1, h2, h3]
  rw [add_comm (x 1).val (x 2).val, add_comm (x 1).val (x 3).val,
    add_comm (x 2).val (x 3).val]
  simp only [complement_spec, validEnds, options, Finset.mem_insert, Finset.mem_singleton]
  tauto

private def coordinates (n : ℕ) :
    (Fin 4 → Letter n) ≃ (Letter n × Letter n) × (Letter n × Letter n) where
  toFun x := ((x 1, x 2), (x 0, x 3))
  invFun p := ![p.2.1, p.1.1, p.1.2, p.2.2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv := by
    rintro ⟨⟨b, c⟩, u, v⟩
    rfl

private theorem sum_indicator {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (∑ x, if p x then (1 : ℤ) else 0) = ((Finset.univ.filter p).card : ℤ) := by
  rw [← Finset.sum_filter p (fun _ => (1 : ℤ))]
  simp

private def fiber {n : ℕ} (b c : Letter n) : ℤ :=
  ((Finset.univ.filter (validEnds b c)).card : ℤ)

private theorem count_sum (n : ℕ) :
    a n = ∑ b : Letter n, ∑ c : Letter n, fiber b c := by
  unfold a
  rw [← sum_indicator (fun x : Fin 4 → Letter n => good x = true)]
  calc
    _ = ∑ p : (Letter n × Letter n) × (Letter n × Letter n),
          if validEnds p.1.1 p.1.2 p.2 then (1 : ℤ) else 0 := by
        refine Fintype.sum_equiv (coordinates n) _ _ ?_
        intro x
        exact if_congr (good_iff x) rfl rfl
    _ = ∑ bc : Letter n × Letter n, fiber bc.1 bc.2 := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro bc _
        exact sum_indicator _
    _ = _ := Fintype.sum_prod_type _

private theorem options_card {n : ℕ} (b c : Letter n) :
    (options b c).card = if c = b then 1 else 2 := by
  by_cases h : c = b
  · subst c
    simp [options]
  · have hn : complement b ∉ ({complement c} : Finset (Letter n)) := by
      intro hm
      have he := Finset.mem_singleton.mp hm
      exact h ((complement_injective n he).symm)
    rw [if_neg h, options, Finset.card_insert_of_notMem hn, Finset.card_singleton]

private theorem fiber_card {n : ℕ} (b c : Letter n) :
    fiber b c = if c = complement b then ((n : ℤ) + 1)^2 else if c = b then 1 else 4 := by
  by_cases h : c = complement b
  · have hf : Finset.univ.filter (validEnds b c) = Finset.univ := by
      ext p
      simp [validEnds, h]
    rw [fiber, hf, if_pos h]
    simp [Fintype.card_prod, pow_two]
  · have hf : Finset.univ.filter (validEnds b c) = options b c ×ˢ options b c := by
      ext p
      simp [validEnds, h, Finset.mem_product]
    rw [fiber, hf, Finset.card_product, options_card, if_neg h]
    by_cases he : c = b <;> simp [he]

private theorem fiber_expanded {n : ℕ} (b c : Letter n) :
    fiber b c = 4 + (if c = complement b then ((n : ℤ) + 1)^2 - 4 else 0)
      - (if c = b then 3 else 0)
      + (if c = b then (if complement b = b then 3 else 0) else 0) := by
  rw [fiber_card]
  by_cases he : c = b
  · subst c
    by_cases hf : complement b = b
    · simp [hf] <;> ring
    · have hc : b ≠ complement b := fun h => hf h.symm
      simp [hf, hc]
  · by_cases hc : c = complement b
    · have hf : complement b ≠ b := fun h => he (hc.trans h)
      simp [hc, hf] <;> ring
    · simp [he, hc]

private theorem sum_fiber {n : ℕ} (b : Letter n) :
    (∑ c : Letter n, fiber b c) =
      ((n : ℤ) + 1) * 4 + (((n : ℤ) + 1)^2 - 4) - 3
        + (if complement b = b then 3 else 0) := by
  have hsplit :
      (∑ c : Letter n, (4 + if c = complement b then ((n : ℤ) + 1)^2 - 4 else 0)) =
        (∑ _ : Letter n, (4 : ℤ)) +
          (∑ c : Letter n, if c = complement b then ((n : ℤ) + 1)^2 - 4 else 0) :=
    Finset.sum_add_distrib
  simp_rw [fiber_expanded, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [hsplit]

private theorem sum_fixed (n : ℕ) :
    (∑ b : Letter n, if complement b = b then (3 : ℤ) else 0) =
      if Even n then 3 else 0 := by
  by_cases h : Even n
  · have hm := Nat.even_iff.mp h
    let m : Letter n := ⟨n / 2, by omega⟩
    have hpoint (b : Letter n) : complement b = b ↔ b = m := by
      rw [show (complement b = b) ↔ (b = complement b) from eq_comm,
        ← complement_spec b b]
      constructor
      · intro hb
        apply Fin.ext
        change b.val = n / 2
        omega
      · rintro rfl
        change n / 2 + n / 2 = n
        omega
    simp [h, hpoint]
  · have hnone (b : Letter n) : complement b ≠ b := by
      intro hb
      have hs := (complement_spec b b).2 hb.symm
      exact h ⟨b.val, hs.symm⟩
    simp [h, hnone]

private theorem count_int (n : ℕ) :
    a n = (n : ℤ)^3 + 7 * (n : ℤ)^2 + 4 * (n : ℤ) - 2 +
      (if Even n then 3 else 0) := by
  rw [count_sum]
  simp_rw [sum_fiber]
  rw [Finset.sum_add_distrib, sum_fixed]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  ring

private theorem count_rat (n : ℕ) :
    (a n : ℚ) = (n : ℚ)^3 + 7 * (n : ℚ)^2 + 4 * (n : ℚ) - 2 +
      (if Even n then 3 else 0) := by
  rw [count_int]
  by_cases h : Even n <;> simp only [h, if_true, if_false] <;> push_cast <;> norm_num

private def term (n : ℕ) : ℚ :=
  if n < 1 then 0 else
    (n : ℚ)^3 + 7 * (n : ℚ)^2 + 4 * (n : ℚ) - 2 + (if Even n then 3 else 0)

private theorem series_identity :
    PowerSeries.mk term * ((1 - X)^4 * (1 + X) : PowerSeries ℚ) =
      X * (10 + 15 * X - 15 * X^2 + 3 * X^3 - X^4) := by
  let P : PowerSeries ℚ := PowerSeries.mk term
  change P * _ = _
  have hl : P * ((1 - X)^4 * (1 + X)) =
      P - C 3 * (P * X^1) + C 2 * (P * X^2) + C 2 * (P * X^3)
        - C 3 * (P * X^4) + P * X^5 := by
    simp only [map_ofNat]
    ring
  have hr : (X * (10 + 15 * X - 15 * X^2 + 3 * X^3 - X^4) : PowerSeries ℚ) =
      C 10 * X^1 + C 15 * X^2 - C 15 * X^3 + C 3 * X^4 - X^5 := by
    simp only [map_ofNat]
    ring
  rw [hl, hr]
  apply PowerSeries.ext
  intro k
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow',
    coeff_X_pow, P, coeff_mk]
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [term, Nat.even_iff]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 6 := ⟨k - 6, by omega⟩
    have s1 : m + 6 - 1 = m + 5 := by omega
    have s2 : m + 6 - 2 = m + 4 := by omega
    have s3 : m + 6 - 3 = m + 3 := by omega
    have s4 : m + 6 - 4 = m + 2 := by omega
    have s5 : m + 6 - 5 = m + 1 := by omega
    simp (disch := omega) only [s1, s2, s3, s4, s5, term, if_pos, if_neg,
      Nat.even_iff, Nat.cast_add, Nat.cast_ofNat]
    by_cases hm : m % 2 = 0
    · have h1 : (m + 1) % 2 ≠ 0 := by omega
      have h2 : (m + 2) % 2 = 0 := by omega
      have h3 : (m + 3) % 2 ≠ 0 := by omega
      have h4 : (m + 4) % 2 = 0 := by omega
      have h5 : (m + 5) % 2 ≠ 0 := by omega
      have h6 : (m + 6) % 2 = 0 := by omega
      simp [hm, h1, h2, h3, h4, h5, h6] <;> ring
    · have h1 : (m + 1) % 2 = 0 := by omega
      have h3 : (m + 3) % 2 = 0 := by omega
      have h4 : (m + 4) % 2 ≠ 0 := by omega
      have h5 : (m + 5) % 2 = 0 := by omega
      have h6 : (m + 6) % 2 ≠ 0 := by omega
      simp [hm, h1, h3, h4, h5, h6] <;> ring

end A245871Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a245871.main := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (fun n => if n < 1 then 0 else (OMA.S_oeis_a245871.a n : ℚ)) =
        A245871Proof.term := by
      funext n
      simp only [A245871Proof.term, A245871Proof.count_rat]
    rw [h]
    exact A245871Proof.series_identity
  · intro n _ hn
    rw [A245871Proof.count_rat, if_pos hn]
    ring
  · intro n _ hn
    rw [A245871Proof.count_rat, if_neg (Nat.not_even_iff_odd.mpr hn)]
    ring

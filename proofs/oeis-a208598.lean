import OMAStatements.S_oeis_a208598

/-!
# Four-bead zero-sum necklaces

Burnside's lemma reduces the count to four fixed sets of labelings. The
identity term is counted by the sum of two adjacent labels. The other
rotations force a constant or an alternating labeling. The general
divisor-sum program of Andrew Howroyd in OEIS A208597 also enumerates
these necklaces at length four.
-/

namespace Orbit208598

open OMA.S_oeis_a208598

/-- Apply Mathlib's additive Burnside lemma to the four rotations of the zero-sum labelings. -/
theorem burnside (n : ℕ) :
    4 * (a n : ℤ) = ∑ k : Fin 4,
      (((L n).filter (fun v => ∀ i : Fin 4, v (i+k) = v i)).card : ℤ) := by
  classical
  let X := ↥(L n)
  let rot (k : Fin 4) (v : X) : X := ⟨fun i => v.val (i+k), by
    obtain ⟨hv, hz⟩ := (Finset.mem_filter.mp v.property)
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i => Fintype.mem_piFinset.mp hv (i+k)), ?_⟩
    exact (Equiv.sum_comp (Equiv.addRight k) v.val).trans hz⟩
  let : AddAction (Fin 4) X := {
    vadd := rot
    zero_vadd := fun v => Subtype.ext (funext fun i => by
      change v.val (i + 0) = v.val i
      rw [add_zero])
    add_vadd := fun k l v => Subtype.ext (funext fun i => by
      change v.val (i + (k + l)) = v.val ((i+k)+l)
      rw [add_assoc]) }
  let R := AddAction.orbitRel (Fin 4) X
  let O (v : Fin 4 → ℤ) := (L n).filter (fun w => ∃ k : Fin 4, w = fun i => v (i+k))
  let Y := ↥((L n).image O)
  let f (v : X) : Y := ⟨O v, Finset.mem_image_of_mem _ v.property⟩
  have hf : Function.Surjective f := by
    rintro ⟨s,hs⟩
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hs
    exact ⟨⟨v,hv⟩,rfl⟩
  have hmem (w v : X) : w.val ∈ O v.val ↔ R w v := by
    simp only [O, Finset.mem_filter, w.property, true_and]
    change (∃ k : Fin 4, w.val = fun i => v.val (i+k)) ↔ ∃ k : Fin 4, rot k v = w
    exact ⟨fun ⟨k,h⟩ => ⟨k,Subtype.ext h.symm⟩,fun ⟨k,h⟩ => ⟨k,congrArg Subtype.val h.symm⟩⟩
  have hker (v w : X) : R v w ↔ Setoid.ker f v w := by
    change R v w ↔ f v = f w
    constructor
    · intro hvw
      apply Subtype.ext
      apply Finset.ext
      intro u
      by_cases hu : u ∈ L n
      · change u ∈ O v.val ↔ u ∈ O w.val
        exact (hmem ⟨u,hu⟩ v).trans ((Iff.intro (fun h => R.trans h hvw)
          (fun h => R.trans h (R.symm hvw))).trans (hmem ⟨u,hu⟩ w).symm)
      · simp [f,O,hu]
    · intro he
      apply (hmem v w).mp
      have e : O v.val = O w.val := congrArg Subtype.val he
      rw [← e]
      exact (hmem v v).mpr (R.refl v)
  let e : Quotient R ≃ Y := (Quotient.congrRight hker).trans (Setoid.quotientKerEquivOfSurjective f hf)
  have hcard : Fintype.card (Quotient R) = a n :=
    (Fintype.card_congr e).trans (Fintype.card_coe _)
  have hfix (k : Fin 4) : Fintype.card (AddAction.fixedBy X k) =
      ((L n).filter (fun v => ∀ i : Fin 4, v (i+k) = v i)).card := by
    let Yk := ↥((L n).filter (fun v => ∀ i : Fin 4, v (i+k) = v i))
    let ek : AddAction.fixedBy X k ≃ Yk := {
      toFun := fun v => ⟨v.val.val, Finset.mem_filter.mpr
        ⟨v.val.property, fun i => congrFun (congrArg Subtype.val v.property) i⟩⟩
      invFun := fun v => ⟨⟨v.val,(Finset.mem_filter.mp v.property).1⟩,
        Subtype.ext (funext (Finset.mem_filter.mp v.property).2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Fintype.card_congr ek).trans (Fintype.card_coe _)
  have H := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup (Fin 4) X
  change (∑ k : Fin 4, _) = Fintype.card (Quotient R) * Fintype.card (Fin 4) at H
  simp only [hfix, hcard, Fintype.card_fin] at H
  exact_mod_cast ((Nat.mul_comm 4 (a n)).trans H.symm)

end Orbit208598

open OMA.S_oeis_a208598
open scoped Classical

namespace Orbit208598

private theorem fixed_label_mem (n : ℕ) (v : Fin 4 → ℤ) :
    v ∈ L n ↔ (∀ i, -(n : ℤ) ≤ v i ∧ v i ≤ n) ∧ v 0 + v 1 + v 2 + v 3 = 0 := by
  simp [L, B, Fin.sum_univ_four, add_assoc]

theorem fixed_zero (n : ℕ) :
    ((L n).filter (fun v => ∀ i : Fin 4, v (i + (0 : Fin 4)) = v i)).card = (L n).card := by
  simp

theorem fixed_one (n : ℕ) :
    ((L n).filter (fun v => ∀ i : Fin 4, v (i + (1 : Fin 4)) = v i)).card = 1 := by
  apply Finset.card_eq_one.mpr
  refine ⟨fun _ => 0, ?_⟩
  ext v
  simp only [Finset.mem_filter, fixed_label_mem, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨_, hs⟩, hr⟩
    have h1 : v 1 = v 0 := hr 0
    have h2 : v 2 = v 1 := hr 1
    have h3 : v 3 = v 2 := hr 2
    have hz : v 0 = 0 := by omega
    funext i
    fin_cases i <;> first | exact hz | exact h1.trans hz | exact h2.trans (h1.trans hz) |
      exact h3.trans (h2.trans (h1.trans hz))
  · rintro rfl
    simp

theorem fixed_three (n : ℕ) :
    ((L n).filter (fun v => ∀ i : Fin 4, v (i + (3 : Fin 4)) = v i)).card = 1 := by
  rw [← fixed_one n]
  congr 1
  apply Finset.filter_congr
  intro v _
  constructor
  · intro h i
    have hz : (1 : Fin 4) + 3 = 0 := by decide
    simpa only [add_assoc, hz, add_zero] using (h (i + 1)).symm
  · intro h i
    have hz : (3 : Fin 4) + 1 = 0 := by decide
    simpa only [add_assoc, hz, add_zero] using (h (i + 3)).symm

private theorem half_tuple {n : ℕ} {v : Fin 4 → ℤ} (hv : v ∈ L n)
    (hr : ∀ i : Fin 4, v (i + (2 : Fin 4)) = v i) :
    v = ![v 0, -v 0, v 0, -v 0] := by
  have hs := ((fixed_label_mem n v).mp hv).2
  have h2 : v 2 = v 0 := hr 0
  have h3 : v 3 = v 1 := hr 1
  have h1 : v 1 = -v 0 := by omega
  funext i
  fin_cases i <;> first | rfl | exact h1 | exact h2 | exact h3.trans h1

theorem fixed_two (n : ℕ) :
    ((L n).filter (fun v => ∀ i : Fin 4, v (i + (2 : Fin 4)) = v i)).card = 2 * n + 1 := by
  have hB : (B n).card = 2 * n + 1 := by
    rw [B, Int.card_Icc]
    omega
  rw [← hB]
  apply Finset.card_bij (fun v _ => v 0)
  · intro v hv
    exact Finset.mem_Icc.mpr (((fixed_label_mem n v).mp (Finset.mem_filter.mp hv).1).1 0)
  · intro u hu v hv he
    obtain ⟨hu, hu'⟩ := Finset.mem_filter.mp hu
    obtain ⟨hv, hv'⟩ := Finset.mem_filter.mp hv
    change u 0 = v 0 at he
    calc
      u = ![u 0, -u 0, u 0, -u 0] := half_tuple hu hu'
      _ = ![v 0, -v 0, v 0, -v 0] := by rw [he]
      _ = v := (half_tuple hv hv').symm
  · intro x hx
    have hx' : -(n : ℤ) ≤ x ∧ x ≤ n := Finset.mem_Icc.mp hx
    refine ⟨![x, -x, x, -x], Finset.mem_filter.mpr ⟨(fixed_label_mem n _).mpr ⟨?_, ?_⟩, ?_⟩, rfl⟩
    · intro i
      fin_cases i <;> first | exact hx' | exact ⟨by change -(n : ℤ) ≤ -x; omega, by change -x ≤ (n : ℤ); omega⟩
    · change x + -x + x + -x = 0
      ring
    · intro i
      fin_cases i <;> rfl

end Orbit208598

/-! Count ordered zero-sum labelings by the sum of their first pair. -/

namespace Orbit208598

open Finset OMA.S_oeis_a208598

private lemma ordered_mem (n : ℕ) (v : Fin 4 → ℤ) :
    v ∈ L n ↔ (∀ i, -(n:ℤ) ≤ v i ∧ v i ≤ n) ∧
      v 0 + v 1 + v 2 + v 3 = 0 := by
  simp [L, B, Fin.sum_univ_four]

private lemma fiber_ordered_count (n : ℕ) (s : ℤ) (hs : s ∈ Icc (-(2*(n:ℤ))) (2*n)) :
    (((L n).filter (fun v => v 0 + v 1 = s)).card : ℤ) =
      (2*(n:ℤ)+1-|s|)^2 := by
  classical
  let J := Icc (max (-(n:ℤ)) (s-n)) (min (n:ℤ) (s+n))
  have hcard : ((L n).filter (fun v => v 0 + v 1 = s)).card = (J ×ˢ J).card := by
    apply card_nbij' (fun v => (v 0, -(v 2))) (fun xy => ![xy.1, s-xy.1, -xy.2, xy.2-s])
    · intro v hv
      obtain ⟨h, hs⟩ := mem_filter.mp hv
      obtain ⟨h, hzero⟩ := (ordered_mem _ _).mp h
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      have h3 := h 3
      simp only [mem_coe, mem_product, J, mem_Icc, max_le_iff, le_min_iff]
      omega
    · rintro ⟨x,y⟩ h
      simp only [mem_coe, mem_product, J, mem_Icc, max_le_iff, le_min_iff] at h
      apply mem_filter.mpr
      constructor
      · apply (ordered_mem _ _).mpr
        constructor
        · intro i
          fin_cases i <;> simp <;> omega
        · simp; ring
      · simp
    · intro v hv
      obtain ⟨h, hs⟩ := mem_filter.mp hv
      obtain ⟨_, hzero⟩ := (ordered_mem _ _).mp h
      funext i
      fin_cases i <;> simp <;> omega
    · rintro ⟨x,y⟩ _
      simp
  rw [hcard, card_product, Nat.cast_mul]
  have hs' := mem_Icc.mp hs
  rw [show (J.card : ℤ) = min (n:ℤ) (s+n)+1-max (-(n:ℤ)) (s-n) from
    Int.card_Icc_of_le _ _ (by omega)]
  rcases le_total s 0 with h | h
  · rw [abs_of_nonpos h, min_eq_right (by omega), max_eq_left (by omega)]
    ring
  · rw [abs_of_nonneg h, min_eq_left (by omega), max_eq_right (by omega)]
    ring

private lemma symmetric_sum (f : ℤ → ℤ) (t : ℕ) :
    ∑ s ∈ Icc (-(t:ℤ)) t, f s = f 0 +
      ∑ i ∈ range t, (f ((i:ℤ)+1) + f (-((i:ℤ)+1))) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h : Icc (-((t+1:ℕ):ℤ)) ((t+1:ℕ):ℤ) =
        insert (-((t:ℤ)+1)) (insert ((t:ℤ)+1) (Icc (-(t:ℤ)) t)) := by
      ext s
      simp only [Nat.cast_add, Nat.cast_one, mem_Icc, mem_insert]
      omega
    rw [h, sum_insert (by simp; omega), sum_insert (by simp), ih, sum_range_succ]
    ring

private lemma square_sum (C : ℤ) (t : ℕ) :
    6 * (∑ i ∈ range t, (C-(i:ℤ))^2) =
      C*(C+1)*(2*C+1) - (C-t)*(C-t+1)*(2*(C-t)+1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, mul_add, ih, Nat.cast_succ]
    ring

theorem identity_count (n : ℕ) :
    3 * ((L n).card : ℤ) = 16*(n:ℤ)^3 + 24*(n:ℤ)^2 + 14*(n:ℤ)+3 := by
  classical
  have hmap : (↑(L n) : Set (Fin 4 → ℤ)).MapsTo (fun v => v 0+v 1)
      (Icc (-(2*(n:ℤ))) (2*n) : Finset ℤ) := by
    intro v hv
    have h := ((ordered_mem _ _).mp hv).1
    have h0 := h 0
    have h1 := h 1
    change v 0+v 1 ∈ Icc _ _
    apply mem_Icc.mpr
    omega
  have count : ((L n).card : ℤ) =
      ∑ s ∈ Icc (-(2*(n:ℤ))) (2*n), (2*(n:ℤ)+1-|s|)^2 := by
    rw [card_eq_sum_card_fiberwise hmap, Nat.cast_sum]
    exact sum_congr rfl fun s hs => fiber_ordered_count _ _ hs
  have sym := symmetric_sum (fun s => (2*(n:ℤ)+1-|s|)^2) (2*n)
  simp only [Nat.cast_mul, Nat.cast_ofNat, abs_zero, sub_zero, abs_neg] at sym
  rw [count, sym]
  have hterms : (∑ i ∈ range (2*n), ((2*(n:ℤ)+1-|((i:ℤ)+1)|)^2 +
      (2*(n:ℤ)+1-|((i:ℤ)+1)|)^2)) = 2*∑ i ∈ range (2*n), (2*(n:ℤ)-i)^2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [abs_of_nonneg (by omega : 0 ≤ (i:ℤ)+1)]
    ring
  rw [hterms]
  have hh := square_sum (2*(n:ℤ)) (2*n)
  push_cast at hh
  linear_combination hh

end Orbit208598

namespace Orbit208598

open OMA.S_oeis_a208598

private theorem closed_form (n : ℕ) :
    3 * (a n : ℤ) = 4 * (n:ℤ)^3 + 6 * (n:ℤ)^2 + 5 * (n:ℤ) + 3 := by
  classical
  have hb := burnside n
  rw [Fin.sum_univ_four, fixed_zero n, fixed_one n, fixed_two n, fixed_three n] at hb
  push_cast at hb
  apply mul_left_cancel₀ (show (4:ℤ) ≠ 0 by decide)
  linear_combination 3 * hb + identity_count n

end Orbit208598

theorem OMA.solution : type_of% @OMA.S_oeis_a208598.main := by
  refine ⟨fun n _ => Orbit208598.closed_form n, ?_⟩
  intro n hn
  have h0 := Orbit208598.closed_form n
  have h1 := Orbit208598.closed_form (n-1)
  have h2 := Orbit208598.closed_form (n-2)
  have h3 := Orbit208598.closed_form (n-3)
  have h4 := Orbit208598.closed_form (n-4)
  simp (disch := omega) only [Nat.cast_sub, Nat.cast_one, Nat.cast_ofNat] at h1 h2 h3 h4
  apply mul_left_cancel₀ (show (3:ℤ) ≠ 0 by decide)
  linear_combination h0 - 4*h1 + 6*h2 - 4*h3 + h4

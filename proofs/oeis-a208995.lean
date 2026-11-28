import OMAStatements.S_oeis_a208995

-- Problem: A208995: Number of 4-bead necklaces labeled with -n..n not allowing reversal, with sum 0 and 1st diffs in -n..n.
-- Credit: @ceejcake
-- Proof: Burnside's lemma on Z_4 and the (u, v, w) = (a+c, a-c, b-d) bijection to 2|u| + |v| + |w| <= 2n with v ≡ w ≡ u (mod 2).

namespace ProofA208995

open OMA.S_oeis_a208995
open scoped Classical
noncomputable section

private def box (n : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(n : ℤ)) n)

private lemma mem_box_of_isValid {n : ℕ} {f : Fin 4 → ℤ} (hf : isValid n f) : f ∈ box n := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
  exact hf.1

noncomputable instance fintypeValid (n : ℕ) : Fintype {f : Fin 4 → ℤ // isValid n f} :=
  Fintype.ofFinset ((box n).filter (isValid n)) (fun f => by
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨mem_box_of_isValid h, h⟩⟩)

-- Diamond set for fixed u and radius B = 2*(n - |u|):
-- {(v, w) ∈ ℤ × ℤ | |v| + |w| ≤ 2*k ∧ v % 2 = p ∧ w % 2 = p}
private def diamSet (k : ℕ) (p : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(2 * (k : ℤ))) (2 * (k : ℤ))) ×ˢ (Finset.Icc (-(2 * (k : ℤ))) (2 * (k : ℤ)))).filter
    (fun q => |q.1| + |q.2| ≤ 2 * (k : ℤ) ∧ q.1 % 2 = p ∧ q.2 % 2 = p)

private lemma mem_diamSet {k : ℕ} {p v w : ℤ} :
    (v, w) ∈ diamSet k p ↔ |v| + |w| ≤ 2 * (k : ℤ) ∧ v % 2 = p ∧ w % 2 = p := by
  simp only [diamSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_, ?_⟩, h⟩ <;> (rcases abs_cases v with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases abs_cases w with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

-- Even parity diamond: {(2a, 2b) | |a| + |b| ≤ k} has cardinality 2k^2 + 2k + 1
private lemma card_diamSet_even (k : ℕ) : (diamSet k 0).card = 2 * k ^ 2 + 2 * k + 1 := by
  induction k with
  | zero =>
    have h : diamSet 0 0 = {(0, 0)} := by
      ext ⟨v, w⟩
      simp only [mem_diamSet, Finset.mem_singleton, Prod.mk.injEq]
      rcases abs_cases v with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases abs_cases w with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    rw [h, Finset.card_singleton]; rfl
  | succ k ih =>
    let ringSet := (diamSet (k + 1) 0).filter (fun q => |q.1| + |q.2| = 2 * ((k + 1 : ℕ) : ℤ))
    have hsplit : diamSet (k + 1) 0 = diamSet k 0 ∪ ringSet := by
      ext ⟨v, w⟩
      simp only [Finset.mem_union, ringSet, Finset.mem_filter, mem_diamSet]
      rcases abs_cases v with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases abs_cases w with ⟨_, _⟩ | ⟨_, _⟩ <;>
        (push_cast; omega)
    have hdisj : Disjoint (diamSet k 0) ringSet := by
      rw [Finset.disjoint_left]; intro ⟨v, w⟩ h1 h2
      simp only [ringSet, Finset.mem_filter, mem_diamSet] at h1 h2
      push_cast at h2; omega
    have hring : ringSet.card = 4 * (k + 1) := by
      let S1 := (Finset.range (k + 1)).image (fun i : ℕ => (2 * (i : ℤ), 2 * ((k + 1 - i : ℕ) : ℤ)))
      let S2 := (Finset.range (k + 1)).image (fun i : ℕ => (2 * ((k + 1 - i : ℕ) : ℤ), -(2 * (i : ℤ))))
      let S3 := (Finset.range (k + 1)).image (fun i : ℕ => (-(2 * (i : ℤ)), -(2 * ((k + 1 - i : ℕ) : ℤ))))
      let S4 := (Finset.range (k + 1)).image (fun i : ℕ => (-(2 * ((k + 1 - i : ℕ) : ℤ)), 2 * (i : ℤ)))
      have hU : ringSet = S1 ∪ S2 ∪ S3 ∪ S4 := by
        ext ⟨v, w⟩
        simp only [ringSet, Finset.mem_filter, mem_diamSet, Finset.mem_union, S1, S2, S3, S4,
          Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨_, hv0, hw0⟩, heq⟩
          push_cast at heq
          by_cases h1 : 0 ≤ v ∧ 0 < w
          · rw [abs_of_nonneg h1.1, abs_of_pos h1.2] at heq
            left; left; left
            refine ⟨(v / 2).toNat, by omega, by omega, by omega⟩
          · by_cases h2 : 0 < v ∧ w ≤ 0
            · rw [abs_of_pos h2.1, abs_of_nonpos h2.2] at heq
              left; left; right
              refine ⟨((-w) / 2).toNat, by omega, by omega, by omega⟩
            · by_cases h3 : v ≤ 0 ∧ w < 0
              · rw [abs_of_nonpos h3.1, abs_of_neg h3.2] at heq
                left; right
                refine ⟨((-v) / 2).toNat, by omega, by omega, by omega⟩
              · have h4 : v < 0 ∧ 0 ≤ w := by
                  rcases abs_cases v with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases abs_cases w with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
                rw [abs_of_neg h4.1, abs_of_nonneg h4.2] at heq
                right
                refine ⟨(w / 2).toNat, by omega, by omega, by omega⟩
        · rintro (((⟨i, hi, rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩) | ⟨i, hi, rfl, rfl⟩) | ⟨i, hi, rfl, rfl⟩)
          · rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; push_cast; exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩
          · rw [abs_of_nonneg (by omega), abs_neg, abs_of_nonneg (by omega)]; push_cast; exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩
          · rw [abs_neg, abs_of_nonneg (by omega), abs_neg, abs_of_nonneg (by omega)]; push_cast; exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩
          · rw [abs_neg, abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; push_cast; exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩
      have hc1 : S1.card = k + 1 := by
        rw [Finset.card_image_of_injective _ (fun a b h => by simp only [Prod.mk.injEq] at h; omega), Finset.card_range]
      have hc2 : S2.card = k + 1 := by
        rw [Finset.card_image_of_injective _ (fun a b h => by simp only [Prod.mk.injEq] at h; omega), Finset.card_range]
      have hc3 : S3.card = k + 1 := by
        rw [Finset.card_image_of_injective _ (fun a b h => by simp only [Prod.mk.injEq] at h; omega), Finset.card_range]
      have hc4 : S4.card = k + 1 := by
        rw [Finset.card_image_of_injective _ (fun a b h => by simp only [Prod.mk.injEq] at h; omega), Finset.card_range]
      have hd12 : Disjoint S1 S2 := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [S1, S2, Finset.mem_image, Finset.mem_range] at h1 h2
        rcases h1 with ⟨i, hi, rfl⟩; rcases h2 with ⟨j, hj, h⟩; simp only [Prod.mk.injEq] at h; omega
      have hd123 : Disjoint (S1 ∪ S2) S3 := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [S1, S2, S3, Finset.mem_union, Finset.mem_image, Finset.mem_range] at h1 h2
        rcases h2 with ⟨j, hj, rfl⟩
        rcases h1 with ⟨i, hi, h⟩ | ⟨i, hi, h⟩ <;> (simp only [Prod.mk.injEq] at h; omega)
      have hd1234 : Disjoint (S1 ∪ S2 ∪ S3) S4 := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [S1, S2, S3, S4, Finset.mem_union, Finset.mem_image, Finset.mem_range] at h1 h2
        rcases h2 with ⟨j, hj, rfl⟩
        rcases h1 with (⟨i, hi, h⟩ | ⟨i, hi, h⟩) | ⟨i, hi, h⟩ <;> (simp only [Prod.mk.injEq] at h; omega)
      rw [hU, Finset.card_union_of_disjoint hd1234, Finset.card_union_of_disjoint hd123,
          Finset.card_union_of_disjoint hd12, hc1, hc2, hc3, hc4]
      omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj, ih, hring]
    ring

-- Odd parity diamond: {(2a+1, 2b+1) | |2a+1| + |2b+1| ≤ 2k} has cardinality 2k^2 + 2k
private lemma card_diamSet_odd (k : ℕ) : (diamSet k 1).card = 2 * k ^ 2 + 2 * k := by
  induction k with
  | zero =>
    have h : diamSet 0 1 = ∅ := by
      ext ⟨v, w⟩
      simp only [mem_diamSet, Finset.notMem_empty, iff_false]
      rcases abs_cases v with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases abs_cases w with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    rw [h, Finset.card_empty]; rfl
  | succ k ih =>
    let ringSet := (diamSet (k + 1) 1).filter (fun q => |q.1| + |q.2| = 2 * ((k + 1 : ℕ) : ℤ))
    have hsplit : diamSet (k + 1) 1 = diamSet k 1 ∪ ringSet := by
      ext ⟨v, w⟩
      simp only [Finset.mem_union, ringSet, Finset.mem_filter, mem_diamSet]
      rcases abs_cases v with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases abs_cases w with ⟨_, _⟩ | ⟨_, _⟩ <;>
        (push_cast; omega)
    have hdisj : Disjoint (diamSet k 1) ringSet := by
      rw [Finset.disjoint_left]; intro ⟨v, w⟩ h1 h2
      simp only [ringSet, Finset.mem_filter, mem_diamSet] at h1 h2
      push_cast at h2; omega
    have hring : ringSet.card = 4 * (k + 1) := by
      let S1 := (Finset.range (k + 1)).image (fun i : ℕ => (2 * (i : ℤ) + 1, 2 * ((k - i : ℕ) : ℤ) + 1))
      let S2 := (Finset.range (k + 1)).image (fun i : ℕ => (2 * (i : ℤ) + 1, -(2 * ((k - i : ℕ) : ℤ) + 1)))
      let S3 := (Finset.range (k + 1)).image (fun i : ℕ => (-(2 * (i : ℤ) + 1), 2 * ((k - i : ℕ) : ℤ) + 1))
      let S4 := (Finset.range (k + 1)).image (fun i : ℕ => (-(2 * (i : ℤ) + 1), -(2 * ((k - i : ℕ) : ℤ) + 1)))
      have hU : ringSet = S1 ∪ S2 ∪ S3 ∪ S4 := by
        ext ⟨v, w⟩
        simp only [ringSet, Finset.mem_filter, mem_diamSet, Finset.mem_union, S1, S2, S3, S4,
          Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨_, hv1, hw1⟩, heq⟩
          push_cast at heq
          by_cases hv : 0 ≤ v <;> by_cases hw : 0 ≤ w
          · rw [abs_of_nonneg hv, abs_of_nonneg hw] at heq
            left; left; left; refine ⟨((v - 1) / 2).toNat, by omega, by omega, by omega⟩
          · rw [abs_of_nonneg hv, abs_of_neg (not_le.mp hw)] at heq
            left; left; right; refine ⟨((v - 1) / 2).toNat, by omega, by omega, by omega⟩
          · rw [abs_of_neg (not_le.mp hv), abs_of_nonneg hw] at heq
            left; right; refine ⟨((-v - 1) / 2).toNat, by omega, by omega, by omega⟩
          · rw [abs_of_neg (not_le.mp hv), abs_of_neg (not_le.mp hw)] at heq
            right; refine ⟨((-v - 1) / 2).toNat, by omega, by omega, by omega⟩
        · rintro (((⟨i, hi, rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩) | ⟨i, hi, rfl, rfl⟩) | ⟨i, hi, rfl, rfl⟩)
          · rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; push_cast; exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩
          · rw [abs_of_nonneg (by omega), abs_neg, abs_of_nonneg (by omega)]; push_cast; exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩
          · rw [abs_neg, abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; push_cast; exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩
          · rw [abs_neg, abs_of_nonneg (by omega), abs_neg, abs_of_nonneg (by omega)]; push_cast; exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩
      have hc1 : S1.card = k + 1 := by
        rw [Finset.card_image_of_injective _ (fun a b h => by simp only [Prod.mk.injEq] at h; omega), Finset.card_range]
      have hc2 : S2.card = k + 1 := by
        rw [Finset.card_image_of_injective _ (fun a b h => by simp only [Prod.mk.injEq] at h; omega), Finset.card_range]
      have hc3 : S3.card = k + 1 := by
        rw [Finset.card_image_of_injective _ (fun a b h => by simp only [Prod.mk.injEq] at h; omega), Finset.card_range]
      have hc4 : S4.card = k + 1 := by
        rw [Finset.card_image_of_injective _ (fun a b h => by simp only [Prod.mk.injEq] at h; omega), Finset.card_range]
      have hd12 : Disjoint S1 S2 := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [S1, S2, Finset.mem_image, Finset.mem_range] at h1 h2
        rcases h1 with ⟨i, hi, rfl⟩; rcases h2 with ⟨j, hj, h⟩; simp only [Prod.mk.injEq] at h; omega
      have hd123 : Disjoint (S1 ∪ S2) S3 := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [S1, S2, S3, Finset.mem_union, Finset.mem_image, Finset.mem_range] at h1 h2
        rcases h2 with ⟨j, hj, rfl⟩
        rcases h1 with ⟨i, hi, h⟩ | ⟨i, hi, h⟩ <;> (simp only [Prod.mk.injEq] at h; omega)
      have hd1234 : Disjoint (S1 ∪ S2 ∪ S3) S4 := by
        rw [Finset.disjoint_left]; intro p h1 h2
        simp only [S1, S2, S3, S4, Finset.mem_union, Finset.mem_image, Finset.mem_range] at h1 h2
        rcases h2 with ⟨j, hj, rfl⟩
        rcases h1 with (⟨i, hi, h⟩ | ⟨i, hi, h⟩) | ⟨i, hi, h⟩ <;> (simp only [Prod.mk.injEq] at h; omega)
      rw [hU, Finset.card_union_of_disjoint hd1234, Finset.card_union_of_disjoint hd123,
          Finset.card_union_of_disjoint hd12, hc1, hc2, hc3, hc4]
      omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj, ih, hring]
    ring

-- Total (u, v, w) set for valid 4-tuples
private def uvwSet (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n).biUnion (fun u =>
    (diamSet (n - u.natAbs) (u % 2)).map
      ⟨fun p => (u, p.1, p.2), fun p1 p2 h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 h.2.2⟩)

private lemma mem_uvwSet {n : ℕ} {u v w : ℤ} :
    (u, v, w) ∈ uvwSet n ↔
      2 * |u| + |v| + |w| ≤ 2 * (n : ℤ) ∧ v % 2 = u % 2 ∧ w % 2 = u % 2 := by
  simp only [uvwSet, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_map, Prod.mk.injEq]
  have huabs : |u| = (u.natAbs : ℤ) := Int.abs_eq_natAbs u
  constructor
  · rintro ⟨u', ⟨hu1, hu2⟩, ⟨v', w'⟩, hvw, rfl, rfl, rfl⟩
    rw [mem_diamSet] at hvw
    rw [huabs]
    dsimp only
    exact ⟨by omega, hvw.2.1, hvw.2.2⟩
  · rintro ⟨hbound, hv, hw⟩
    have hu : -(n : ℤ) ≤ u ∧ u ≤ n := by
      rcases abs_cases u with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases abs_cases v with ⟨_, _⟩ | ⟨_, _⟩ <;>
        rcases abs_cases w with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    refine ⟨u, hu, (v, w), ?_, rfl⟩
    rw [mem_diamSet]
    rw [huabs] at hbound
    omega

-- Bijection: |valid| = |uvwSet n|
private lemma card_valid_eq_uvw (n : ℕ) :
    Fintype.card {f : Fin 4 → ℤ // isValid n f} = (uvwSet n).card := by
  have hcard : Fintype.card {f : Fin 4 → ℤ // isValid n f} = ((box n).filter (isValid n)).card :=
    Fintype.card_ofFinset _ _
  rw [hcard]
  refine Finset.card_bij (fun f _ => (f 0 + f 2, f 0 - f 2, f 1 - f 3)) ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter] at hf
    rcases hf.2 with ⟨hb, hsum, hd1⟩
    have h0 := hd1 0; have h1 := hd1 1; have h2 := hd1 2; have h3 := hd1 3
    simp only [Fin.reduceAdd] at h0 h1 h2 h3
    rw [mem_uvwSet]
    rcases abs_cases (f 0 + f 2) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases abs_cases (f 0 - f 2) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases abs_cases (f 1 - f 3) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      refine ⟨by omega, by omega, by omega⟩
  · intro f1 hf1 f2 hf2 h
    rw [Finset.mem_filter] at hf1 hf2
    have hs1 := hf1.2.2.1; have hs2 := hf2.2.2.1
    simp only [Prod.mk.injEq] at h
    ext i
    match i with | 0 => omega | 1 => omega | 2 => omega | 3 => omega
  · intro ⟨u, v, w⟩ huvw
    rw [mem_uvwSet] at huvw
    rcases huvw with ⟨hbound, hvp, hwp⟩
    let f : Fin 4 → ℤ := fun i =>
      match i with
      | 0 => (u + v) / 2
      | 1 => (-u + w) / 2
      | 2 => (u - v) / 2
      | 3 => (-u - w) / 2
    have h20 : 2 * f 0 = u + v := by dsimp [f]; omega
    have h21 : 2 * f 1 = -u + w := by dsimp [f]; omega
    have h22 : 2 * f 2 = u - v := by dsimp [f]; omega
    have h23 : 2 * f 3 = -u - w := by dsimp [f]; omega
    have hu_le : -|u| ≤ u ∧ u ≤ |u| := ⟨neg_abs_le u, le_abs_self u⟩
    have hv_le : -|v| ≤ v ∧ v ≤ |v| := ⟨neg_abs_le v, le_abs_self v⟩
    have hw_le : -|w| ≤ w ∧ w ≤ |w| := ⟨neg_abs_le w, le_abs_self w⟩
    have hvalid : isValid n f :=
      ⟨fun i => by match i with | 0 => omega | 1 => omega | 2 => omega | 3 => omega,
       by omega,
       fun i => by match i with | 0 => simp only [Fin.reduceAdd]; omega | 1 => simp only [Fin.reduceAdd]; omega | 2 => simp only [Fin.reduceAdd]; omega | 3 => simp only [Fin.reduceAdd]; omega⟩
    refine ⟨f, Finset.mem_filter.mpr ⟨mem_box_of_isValid hvalid, hvalid⟩, ?_⟩
    simp only [Prod.mk.injEq]
    omega

private lemma sum_even_Icc (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, if j % 2 = 0 then 1 else 0) = n / 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hI : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hI, Finset.sum_insert (by simp), ih]
    split_ifs <;> omega

-- Exact formula for 3 * (uvwSet n).card
private lemma three_mul_card_uvwSet (n : ℕ) :
    3 * (uvwSet n).card = 4 * n ^ 3 + 6 * n ^ 2 + 2 * n + 3 + 6 * (n / 2) := by
  have hsum : (uvwSet n).card =
      ∑ u ∈ Finset.Icc (-(n : ℤ)) n, (diamSet (n - u.natAbs) (u % 2)).card := by
    unfold uvwSet
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl (fun u _ => by rw [Finset.card_map])
    · intro u1 _ u2 _ hne
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [Finset.mem_map] at h1 h2
      rcases h1 with ⟨_, _, rfl⟩; rcases h2 with ⟨_, _, h2⟩
      exact hne (congr_arg Prod.fst h2).symm
  rw [hsum]
  -- Split Icc (-n) n = {0} ∪ image (+j) ∪ image (-j) for j ∈ Icc 1 n
  have hU : Finset.Icc (-(n : ℤ)) n =
      {0} ∪ ((Finset.Icc 1 n).image (fun j : ℕ => (j : ℤ)) ∪
             (Finset.Icc 1 n).image (fun j : ℕ => -(j : ℤ))) := by
    ext u
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
    constructor
    · intro ⟨hu1, hu2⟩
      by_cases h0 : u = 0
      · exact Or.inl h0
      · right
        rcases lt_or_gt_of_ne h0 with hlt | hgt
        · right; exact ⟨u.natAbs, ⟨by omega, by omega⟩, by omega⟩
        · left; exact ⟨u.natAbs, ⟨by omega, by omega⟩, by omega⟩
    · rintro (rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
  have hd1 : Disjoint ({0} : Finset ℤ)
      ((Finset.Icc 1 n).image (fun j : ℕ => (j : ℤ)) ∪
       (Finset.Icc 1 n).image (fun j : ℕ => -(j : ℤ))) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    rw [Finset.mem_singleton] at hx1; subst hx1
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc] at hx2
    rcases hx2 with ⟨j, hj, h⟩ | ⟨j, hj, h⟩ <;> omega
  have hd2 : Disjoint ((Finset.Icc 1 n).image (fun j : ℕ => (j : ℤ)))
      ((Finset.Icc 1 n).image (fun j : ℕ => -(j : ℤ))) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_image, Finset.mem_Icc] at hx1 hx2
    rcases hx1 with ⟨j1, hj1, rfl⟩; rcases hx2 with ⟨j2, hj2, h⟩; omega
  rw [hU, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton]
  rw [Finset.sum_image (fun a _ b _ h => by omega), Finset.sum_image (fun a _ b _ h => by omega)]
  have h0 : (diamSet (n - (0 : ℤ).natAbs) ((0 : ℤ) % 2)).card = 2 * n ^ 2 + 2 * n + 1 := by
    simpa using card_diamSet_even n
  have hpos : ∀ j ∈ Finset.Icc 1 n,
      (diamSet (n - (j : ℤ).natAbs) ((j : ℤ) % 2)).card =
        2 * (n - j) ^ 2 + 2 * (n - j) + (if j % 2 = 0 then 1 else 0) := by
    intro j _
    have hna : (j : ℤ).natAbs = j := Int.natAbs_natCast j
    rw [hna]
    by_cases he : j % 2 = 0
    · have hm : (j : ℤ) % 2 = 0 := by omega
      rw [hm, if_pos he, card_diamSet_even]
    · have hm : (j : ℤ) % 2 = 1 := by omega
      rw [hm, if_neg he, card_diamSet_odd]; omega
  have hneg : ∀ j ∈ Finset.Icc 1 n,
      (diamSet (n - (-(j : ℤ)).natAbs) ((-(j : ℤ)) % 2)).card =
        2 * (n - j) ^ 2 + 2 * (n - j) + (if j % 2 = 0 then 1 else 0) := by
    intro j _
    have hna : (-(j : ℤ)).natAbs = j := by simp
    rw [hna]
    by_cases he : j % 2 = 0
    · have hm : (-(j : ℤ)) % 2 = 0 := by omega
      rw [hm, if_pos he, card_diamSet_even]
    · have hm : (-(j : ℤ)) % 2 = 1 := by omega
      rw [hm, if_neg he, card_diamSet_odd]; omega
  rw [h0, Finset.sum_congr rfl hpos, Finset.sum_congr rfl hneg]
  -- Evaluate ∑_{j=1}^n (2*(n-j)^2 + 2*(n-j)) + ∑_{j=1}^n [j even]
  have hsplit_sum : ∑ j ∈ Finset.Icc 1 n, (2 * (n - j) ^ 2 + 2 * (n - j) + (if j % 2 = 0 then 1 else 0)) =
      (∑ j ∈ Finset.Icc 1 n, (2 * (n - j) ^ 2 + 2 * (n - j))) +
      (∑ j ∈ Finset.Icc 1 n, if j % 2 = 0 then 1 else 0) := Finset.sum_add_distrib
  have heven_cnt : (∑ j ∈ Finset.Icc 1 n, if j % 2 = 0 then 1 else 0) = n / 2 :=
    sum_even_Icc n
  have hpoly_sum : 3 * (∑ j ∈ Finset.Icc 1 n, (2 * (n - j) ^ 2 + 2 * (n - j))) =
      2 * n ^ 3 - 2 * n := by
    -- Reindex k = n - j ∈ Finset.range n
    have hre : ∑ j ∈ Finset.Icc 1 n, (2 * (n - j) ^ 2 + 2 * (n - j)) =
        ∑ k ∈ Finset.range n, (2 * k ^ 2 + 2 * k) := by
      refine Finset.sum_bij (fun j _ => n - j) ?_ ?_ ?_ ?_
      · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_range]; omega
      · intro j1 hj1 j2 hj2 h; rw [Finset.mem_Icc] at hj1 hj2; omega
      · intro k hk; rw [Finset.mem_range] at hk
        exact ⟨n - k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro _ _; rfl
    rw [hre]
    clear hre heven_cnt hsplit_sum hneg hpos h0 hd2 hd1 hU hsum
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hk : 2 * k ≤ 2 * k ^ 3 := by
        have : 1 ≤ k ^ 2 ∨ k = 0 := by
          rcases Nat.eq_zero_or_pos k with rfl | hpos
          · right; rfl
          · left; nlinarith
        rcases this with h | rfl <;> nlinarith
      have hsub : (2 * k ^ 3 - 2 * k) + 2 * k = 2 * k ^ 3 := by omega
      have hsub2 : (2 * (k + 1) ^ 3 - 2 * (k + 1)) + 2 * (k + 1) = 2 * (k + 1) ^ 3 := by
        have : 2 * (k + 1) ≤ 2 * (k + 1) ^ 3 := by nlinarith
        omega
      nlinarith
  rw [hsplit_sum, heven_cnt]
  have hsub : (2 * n ^ 3 - 2 * n) + 2 * n = 2 * n ^ 3 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have : 2 * n ≤ 2 * n ^ 3 := by nlinarith
      omega
  nlinarith

private lemma card_fixed_one (n : ℕ) (g : Fin 4) (hg : g = 1 ∨ g = 3) :
    letI := rotAction n
    Fintype.card (MulAction.fixedBy {f : Fin 4 → ℤ // isValid n f} (Multiplicative.ofAdd g)) = 1 := by
  letI := rotAction n
  have hzero_valid : isValid n (fun _ => 0) :=
    ⟨fun _ => by simp, by simp, fun _ => by simp⟩
  let z : {f : Fin 4 → ℤ // isValid n f} := ⟨fun _ => 0, hzero_valid⟩
  have hz_mem : z ∈ MulAction.fixedBy {f : Fin 4 → ℤ // isValid n f} (Multiplicative.ofAdd g) := by
    change (Multiplicative.ofAdd g) • z = z
    apply Subtype.ext; ext i; rfl
  rw [Fintype.card_subtype]
  have hset : Finset.univ.filter (fun x : {f : Fin 4 → ℤ // isValid n f} =>
      x ∈ MulAction.fixedBy {f : Fin 4 → ℤ // isValid n f} (Multiplicative.ofAdd g)) = {z} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hx
      change (Multiplicative.ofAdd g) • x = x at hx
      have hf : ∀ i : Fin 4, x.1 (i + g) = x.1 i := fun i => congr_fun (congr_arg Subtype.val hx) i
      have hsum := x.2.2.1
      have h0 := hf 0; have h1 := hf 1; have h2 := hf 2; have h3 := hf 3
      rcases hg with rfl | rfl <;>
        (simp only [Fin.reduceAdd] at h0 h1 h2 h3; apply Subtype.ext; ext i; dsimp only [z];
         match i with | 0 => omega | 1 => omega | 2 => omega | 3 => omega)
    · rintro rfl; exact hz_mem
  rw [hset, Finset.card_singleton]

private lemma card_fixed_two (n : ℕ) :
    letI := rotAction n
    Fintype.card (MulAction.fixedBy {f : Fin 4 → ℤ // isValid n f} (Multiplicative.ofAdd (2 : Fin 4))) =
      2 * (n / 2) + 1 := by
  letI := rotAction n
  rw [Fintype.card_subtype]
  have hIcc : (Finset.Icc (-((n / 2 : ℕ) : ℤ)) ((n / 2 : ℕ) : ℤ)).card = 2 * (n / 2) + 1 := by
    rw [Int.card_Icc]; omega
  rw [← hIcc]
  refine Finset.card_bij (fun x _ => x.1 0) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    change (Multiplicative.ofAdd (2 : Fin 4)) • x = x at hx
    have h0 : x.1 2 = x.1 0 := congr_fun (congr_arg Subtype.val hx) 0
    have h1 : x.1 3 = x.1 1 := congr_fun (congr_arg Subtype.val hx) 1
    have hsum := x.2.2.1
    have hd1 := x.2.2.2 0
    simp only [Fin.reduceAdd] at hd1
    rw [Finset.mem_Icc]
    omega
  · intro x1 hx1 x2 hx2 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
    change (Multiplicative.ofAdd (2 : Fin 4)) • x1 = x1 at hx1
    change (Multiplicative.ofAdd (2 : Fin 4)) • x2 = x2 at hx2
    have h10 : x1.1 2 = x1.1 0 := congr_fun (congr_arg Subtype.val hx1) 0
    have h11 : x1.1 3 = x1.1 1 := congr_fun (congr_arg Subtype.val hx1) 1
    have h20 : x2.1 2 = x2.1 0 := congr_fun (congr_arg Subtype.val hx2) 0
    have h21 : x2.1 3 = x2.1 1 := congr_fun (congr_arg Subtype.val hx2) 1
    have hs1 := x1.2.2.1; have hs2 := x2.2.2.1
    apply Subtype.ext; ext i
    match i with | 0 => omega | 1 => omega | 2 => omega | 3 => omega
  · intro c hc
    rw [Finset.mem_Icc] at hc
    let f : Fin 4 → ℤ := fun i => match i with | 0 => c | 1 => -c | 2 => c | 3 => -c
    have hval : isValid n f :=
      ⟨fun i => by match i with | 0 => dsimp [f]; omega | 1 => dsimp [f]; omega | 2 => dsimp [f]; omega | 3 => dsimp [f]; omega,
       by dsimp [f]; omega,
       fun i => by match i with | 0 => simp only [Fin.reduceAdd]; dsimp [f]; omega | 1 => simp only [Fin.reduceAdd]; dsimp [f]; omega | 2 => simp only [Fin.reduceAdd]; dsimp [f]; omega | 3 => simp only [Fin.reduceAdd]; dsimp [f]; omega⟩
    refine ⟨⟨f, hval⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (Multiplicative.ofAdd (2 : Fin 4)) • (⟨f, hval⟩ : {f : Fin 4 → ℤ // isValid n f}) = ⟨f, hval⟩
    apply Subtype.ext; ext i
    match i with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl

private lemma burnside_a (n : ℕ) :
    4 * a n = (uvwSet n).card + (2 * (n / 2) + 1) + 2 := by
  letI := rotAction n
  have ha : a n = Fintype.card (MulAction.orbitRel.Quotient (Multiplicative (Fin 4)) {f : Fin 4 → ℤ // isValid n f}) := by
    unfold a
    rw [Nat.card_eq_fintype_card]
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Multiplicative (Fin 4)) {f : Fin 4 → ℤ // isValid n f}
  rw [← ha] at hburn
  have hcardG : Fintype.card (Multiplicative (Fin 4)) = 4 := by
    rw [Fintype.card_congr Multiplicative.toAdd, Fintype.card_fin]
  rw [hcardG] at hburn
  have hsum : (∑ g : Multiplicative (Fin 4),
      Fintype.card (MulAction.fixedBy {f : Fin 4 → ℤ // isValid n f} g)) =
      Fintype.card (MulAction.fixedBy {f : Fin 4 → ℤ // isValid n f} (Multiplicative.ofAdd (0 : Fin 4))) +
      Fintype.card (MulAction.fixedBy {f : Fin 4 → ℤ // isValid n f} (Multiplicative.ofAdd (1 : Fin 4))) +
      Fintype.card (MulAction.fixedBy {f : Fin 4 → ℤ // isValid n f} (Multiplicative.ofAdd (2 : Fin 4))) +
      Fintype.card (MulAction.fixedBy {f : Fin 4 → ℤ // isValid n f} (Multiplicative.ofAdd (3 : Fin 4))) := by
    rw [← Equiv.sum_comp Multiplicative.ofAdd, Fin.sum_univ_four]
  have hf0 : Fintype.card (MulAction.fixedBy {f : Fin 4 → ℤ // isValid n f} (Multiplicative.ofAdd (0 : Fin 4))) =
      (uvwSet n).card := by
    rw [← card_valid_eq_uvw n, Fintype.card_subtype]
    have hall : ∀ x : {f : Fin 4 → ℤ // isValid n f},
        x ∈ MulAction.fixedBy {f : Fin 4 → ℤ // isValid n f} (Multiplicative.ofAdd (0 : Fin 4)) := by
      intro x; change (1 : Multiplicative (Fin 4)) • x = x; exact one_smul _ x
    simp
  have hf1 := card_fixed_one n 1 (Or.inl rfl)
  have hf2 := card_fixed_two n
  have hf3 := card_fixed_one n 3 (Or.inr rfl)
  rw [hsum, hf0, hf1, hf2, hf3] at hburn
  omega

theorem main :
    (∀ n : ℕ, 1 ≤ n → Even n → 12 * a n = 4 * n ^ 3 + 6 * n ^ 2 + 8 * n + 12) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → 12 * a n = 4 * n ^ 3 + 6 * n ^ 2 + 8 * n + 6) := by
  constructor
  · rintro n _ ⟨m, rfl⟩
    have hb := burnside_a (m + m)
    have hu := three_mul_card_uvwSet (m + m)
    have hdiv : (m + m) / 2 = m := by omega
    rw [hdiv] at hb hu
    nlinarith
  · rintro n _ ⟨m, rfl⟩
    have hb := burnside_a (2 * m + 1)
    have hu := three_mul_card_uvwSet (2 * m + 1)
    have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv] at hb hu
    nlinarith

end
end ProofA208995

theorem OMA.solution : type_of% @OMA.S_oeis_a208995.main :=
  ProofA208995.main

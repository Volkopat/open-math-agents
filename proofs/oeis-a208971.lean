import OMAStatements.S_oeis_a208971

-- Problem: A208971: Number of 4-bead necklaces labeled with -n..n allowing reversal, with sum 0 and 1st/2nd diffs in -n..n.
-- Credit: @ceejcake
-- Proof via Burnside's lemma on DihedralGroup 4 and the (u, v, w) = (a+c, a-c, b-d) lattice bijection.

namespace Neck4Rev

open OMA.S_oeis_a208971
open scoped Classical
noncomputable section

-- Finite bounding box for valid 4-tuples
private def box (n : ℕ) : Finset (ZMod 4 → ℤ) :=
  Fintype.piFinset (fun _ : ZMod 4 => Finset.Icc (-(n : ℤ)) n)

private lemma mem_box_of_isValid {n : ℕ} {f : ZMod 4 → ℤ} (hf : isValid n f) : f ∈ box n := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
  exact hf.1

noncomputable instance fintypeValid (n : ℕ) : Fintype {f : ZMod 4 → ℤ // isValid n f} :=
  Fintype.ofFinset ((box n).filter (isValid n)) (fun f => by
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨mem_box_of_isValid h, h⟩⟩)

-- Parity-matched interval: {v ∈ Icc (-B) B | v % 2 = u % 2}
private def parIcc (B : ℤ) (u : ℤ) : Finset ℤ :=
  (Finset.Icc (-B) B).filter (fun v => v % 2 = u % 2)

private lemma card_parIcc (k : ℕ) (u : ℤ) :
    (parIcc (k : ℤ) u).card = if (k : ℤ) % 2 = u % 2 then k + 1 else k := by
  induction k with
  | zero =>
    unfold parIcc
    simp only [Nat.cast_zero]
    have hI : Finset.Icc (-(0 : ℤ)) (0 : ℤ) = {0} := by decide
    rw [hI]
    by_cases h : (0 : ℤ) % 2 = u % 2
    · rw [if_pos h]
      have : ({0} : Finset ℤ).filter (fun v => v % 2 = u % 2) = {0} := by
        ext x; simp only [Finset.mem_filter, Finset.mem_singleton]; constructor
        · exact fun h => h.1
        · rintro rfl; exact ⟨rfl, h⟩
      rw [this, Finset.card_singleton]
    · rw [if_neg h]
      have : ({0} : Finset ℤ).filter (fun v => v % 2 = u % 2) = ∅ := by
        ext x; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨rfl, hx⟩; exact h hx
      rw [this, Finset.card_empty]
  | succ k ih =>
    unfold parIcc at ih ⊢
    have hsplit : Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) =
        {-((k + 1 : ℕ) : ℤ), ((k + 1 : ℕ) : ℤ)} ∪ Finset.Icc (-(k : ℤ)) (k : ℤ) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      push_cast; omega
    have hdisj : Disjoint ({-((k + 1 : ℕ) : ℤ), ((k + 1 : ℕ) : ℤ)} : Finset ℤ) (Finset.Icc (-(k : ℤ)) (k : ℤ)) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at hx1 hx2
      push_cast at hx1; omega
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj), ih]
    have hne : -((k + 1 : ℕ) : ℤ) ≠ ((k + 1 : ℕ) : ℤ) := by push_cast; omega
    have hmod_neg : (-((k + 1 : ℕ) : ℤ)) % 2 = ((k + 1 : ℕ) : ℤ) % 2 := by push_cast; omega
    by_cases h : ((k + 1 : ℕ) : ℤ) % 2 = u % 2
    · rw [if_pos h]
      have hk : ¬ ((k : ℤ) % 2 = u % 2) := by push_cast at h; omega
      rw [if_neg hk]
      have hf : ({-((k + 1 : ℕ) : ℤ), ((k + 1 : ℕ) : ℤ)} : Finset ℤ).filter (fun v => v % 2 = u % 2) =
          {-((k + 1 : ℕ) : ℤ), ((k + 1 : ℕ) : ℤ)} := by
        ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · exact fun hx => hx.1
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, hmod_neg.trans h⟩
          · exact ⟨Or.inr rfl, h⟩
      rw [hf, Finset.card_pair hne]; omega
    · rw [if_neg h]
      have hk : (k : ℤ) % 2 = u % 2 := by push_cast at h; omega
      rw [if_pos hk]
      have hf : ({-((k + 1 : ℕ) : ℤ), ((k + 1 : ℕ) : ℤ)} : Finset ℤ).filter (fun v => v % 2 = u % 2) = ∅ := by
        ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
          Finset.notMem_empty, iff_false]
        rintro ⟨rfl | rfl, hx⟩
        · exact h (hmod_neg.symm.trans hx)
        · exact h hx
      rw [hf, Finset.card_empty]; omega

-- Equivalence between valid 4-tuples and {(u, v, w) | |2u| ≤ n, v,w ∈ parIcc (n - 2|u|) u}
private def uvwSet (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc (-(n : ℤ)) n).filter (fun u : ℤ => 2 * |u| ≤ (n : ℤ))).biUnion (fun u =>
    (parIcc ((n : ℤ) - 2 * |u|) u ×ˢ parIcc ((n : ℤ) - 2 * |u|) u).map
      ⟨fun p => (u, p.1, p.2), fun p1 p2 h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 h.2.2⟩)

private lemma mem_uvwSet {n : ℕ} {u v w : ℤ} :
    (u, v, w) ∈ uvwSet n ↔
      2 * |u| ≤ n ∧
      -((n : ℤ) - 2 * |u|) ≤ v ∧ v ≤ (n : ℤ) - 2 * |u| ∧ v % 2 = u % 2 ∧
      -((n : ℤ) - 2 * |u|) ≤ w ∧ w ≤ (n : ℤ) - 2 * |u| ∧ w % 2 = u % 2 := by
  simp only [uvwSet, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc, Finset.mem_map,
    Finset.mem_product, parIcc, Function.Embedding.coeFn_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨u', ⟨⟨_, _⟩, hu2⟩, ⟨v', w'⟩, ⟨⟨⟨hv1, hv2⟩, hvp⟩, ⟨⟨hw1, hw2⟩, hwp⟩⟩, rfl, rfl, rfl⟩
    exact ⟨hu2, hv1, hv2, hvp, hw1, hw2, hwp⟩
  · rintro ⟨hu2, hv1, hv2, hvp, hw1, hw2, hwp⟩
    have hu_abs : -(n : ℤ) ≤ u ∧ u ≤ n := by
      rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    exact ⟨u, ⟨hu_abs, hu2⟩, (v, w), ⟨⟨⟨hv1, hv2⟩, hvp⟩, ⟨⟨hw1, hw2⟩, hwp⟩⟩, rfl⟩

lemma card_valid_eq_uvw (n : ℕ) :
    Fintype.card {f : ZMod 4 → ℤ // isValid n f} = (uvwSet n).card := by
  have hcard : Fintype.card {f : ZMod 4 → ℤ // isValid n f} = ((box n).filter (isValid n)).card :=
    Fintype.card_ofFinset _ _
  rw [hcard]
  refine Finset.card_bij
    (fun f _ => (f 0 + f 2, f 0 - f 2, f 1 - f 3)) ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter] at hf
    rcases hf.2 with ⟨hb, hsum, _, hd2⟩
    have h0 := hd2 0; have h1 := hd2 1; have h2 := hd2 2; have h3 := hd2 3
    change -(n : ℤ) ≤ f 0 - 2 * f 1 + f 2 ∧ f 0 - 2 * f 1 + f 2 ≤ n at h0
    change -(n : ℤ) ≤ f 1 - 2 * f 2 + f 3 ∧ f 1 - 2 * f 2 + f 3 ≤ n at h1
    change -(n : ℤ) ≤ f 2 - 2 * f 3 + f 0 ∧ f 2 - 2 * f 3 + f 0 ≤ n at h2
    change -(n : ℤ) ≤ f 3 - 2 * f 0 + f 1 ∧ f 3 - 2 * f 0 + f 1 ≤ n at h3
    rw [mem_uvwSet]
    rcases abs_cases (f 0 + f 2) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · intro f1 hf1 f2 hf2 h
    rw [Finset.mem_filter] at hf1 hf2
    have hs1 := hf1.2.2.1; have hs2 := hf2.2.2.1
    simp only [Prod.mk.injEq] at h
    ext i
    match i with
    | 0 => omega
    | 1 => omega
    | 2 => omega
    | 3 => omega
  · intro ⟨u, v, w⟩ huvw
    rw [mem_uvwSet] at huvw
    rcases huvw with ⟨hu2, hv1, hv2, hvp, hw1, hw2, hwp⟩
    let f : ZMod 4 → ℤ := fun i =>
      match i with
      | 0 => (u + v) / 2
      | 1 => (-u + w) / 2
      | 2 => (u - v) / 2
      | 3 => (-u - w) / 2
    have h20 : 2 * f 0 = u + v := by dsimp [f]; omega
    have h21 : 2 * f 1 = -u + w := by dsimp [f]; omega
    have h22 : 2 * f 2 = u - v := by dsimp [f]; omega
    have h23 : 2 * f 3 = -u - w := by dsimp [f]; omega
    have hvalid : isValid n f := by
      rcases abs_cases u with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
        refine ⟨fun i => by match i with | 0 => omega | 1 => omega | 2 => omega | 3 => omega,
                by omega,
                fun i => by match i with | 0 => change -(n : ℤ) ≤ f 1 - f 0 ∧ f 1 - f 0 ≤ n; omega | 1 => change -(n : ℤ) ≤ f 2 - f 1 ∧ f 2 - f 1 ≤ n; omega | 2 => change -(n : ℤ) ≤ f 3 - f 2 ∧ f 3 - f 2 ≤ n; omega | 3 => change -(n : ℤ) ≤ f 0 - f 3 ∧ f 0 - f 3 ≤ n; omega,
                fun i => by match i with | 0 => change -(n : ℤ) ≤ f 0 - 2 * f 1 + f 2 ∧ f 0 - 2 * f 1 + f 2 ≤ n; omega | 1 => change -(n : ℤ) ≤ f 1 - 2 * f 2 + f 3 ∧ f 1 - 2 * f 2 + f 3 ≤ n; omega | 2 => change -(n : ℤ) ≤ f 2 - 2 * f 3 + f 0 ∧ f 2 - 2 * f 3 + f 0 ≤ n; omega | 3 => change -(n : ℤ) ≤ f 3 - 2 * f 0 + f 1 ∧ f 3 - 2 * f 0 + f 1 ≤ n; omega⟩
    refine ⟨f, Finset.mem_filter.mpr ⟨mem_box_of_isValid hvalid, hvalid⟩, ?_⟩
    simp only [Prod.mk.injEq]
    omega

private lemma card_uvwSet_sum (n : ℕ) :
    (uvwSet n).card =
      ∑ u ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun u : ℤ => 2 * |u| ≤ (n : ℤ)),
        (parIcc ((n : ℤ) - 2 * |u|) u).card ^ 2 := by
  unfold uvwSet
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.card_map, Finset.card_product, sq]
  · intro u1 _ u2 _ hne
    dsimp only [Function.onFun]; rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at h1 h2
    rcases h1 with ⟨_, _, rfl⟩
    rcases h2 with ⟨_, _, h2⟩
    exact hne (congr_arg Prod.fst h2).symm

lemma card_uvwSet_nat (n : ℕ) :
    (uvwSet n).card =
      (if n % 2 = 0 then n + 1 else n) ^ 2 +
      2 * ∑ j ∈ Finset.Icc 1 (n / 2),
        (if (n - 2 * j) % 2 = j % 2 then n - 2 * j + 1 else n - 2 * j) ^ 2 := by
  rw [card_uvwSet_sum]
  let U := (Finset.Icc (-(n : ℤ)) n).filter (fun u : ℤ => 2 * |u| ≤ (n : ℤ))
  have hU : U = {0} ∪ ((Finset.Icc 1 (n / 2)).image (fun j : ℕ => (j : ℤ)) ∪
      (Finset.Icc 1 (n / 2)).image (fun j : ℕ => -(j : ℤ))) := by
    ext u
    simp only [U, Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_image]
    constructor
    · rintro ⟨⟨_, _⟩, hu2⟩
      by_cases h0 : u = 0
      · exact Or.inl h0
      · right
        rcases lt_or_gt_of_ne h0 with hlt | hgt
        · right
          rw [abs_of_neg hlt] at hu2
          refine ⟨u.natAbs, ⟨by omega, by omega⟩, by omega⟩
        · left
          rw [abs_of_pos hgt] at hu2
          refine ⟨u.natAbs, ⟨by omega, by omega⟩, by omega⟩
    · rintro (rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
      · simp
      · rw [abs_of_nonneg (by omega)]; omega
      · rw [abs_neg, abs_of_nonneg (by omega)]; omega
  have hd1 : Disjoint ({0} : Finset ℤ)
      ((Finset.Icc 1 (n / 2)).image (fun j : ℕ => (j : ℤ)) ∪
       (Finset.Icc 1 (n / 2)).image (fun j : ℕ => -(j : ℤ))) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    rw [Finset.mem_singleton] at hx1; subst hx1
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc] at hx2
    rcases hx2 with ⟨j, hj, h⟩ | ⟨j, hj, h⟩ <;> omega
  have hd2 : Disjoint ((Finset.Icc 1 (n / 2)).image (fun j : ℕ => (j : ℤ)))
      ((Finset.Icc 1 (n / 2)).image (fun j : ℕ => -(j : ℤ))) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_image, Finset.mem_Icc] at hx1 hx2
    rcases hx1 with ⟨j1, hj1, rfl⟩; rcases hx2 with ⟨j2, hj2, h⟩; omega
  change ∑ u ∈ U, _ = _
  rw [hU, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton]
  rw [Finset.sum_image (fun a _ b _ h => by omega), Finset.sum_image (fun a _ b _ h => by omega)]
  have h0 : (parIcc ((n : ℤ) - 2 * |(0 : ℤ)|) 0).card = if n % 2 = 0 then n + 1 else n := by
    simp only [abs_zero, mul_zero, sub_zero, card_parIcc]
    have : (n : ℤ) % 2 = (0 : ℤ) % 2 ↔ n % 2 = 0 := by omega
    split_ifs <;> omega
  have hpos : ∀ j ∈ Finset.Icc 1 (n / 2),
      (parIcc ((n : ℤ) - 2 * |(j : ℤ)|) (j : ℤ)).card =
        if (n - 2 * j) % 2 = j % 2 then n - 2 * j + 1 else n - 2 * j := by
    intro j hj; rw [Finset.mem_Icc] at hj
    have heq : (n : ℤ) - 2 * |(j : ℤ)| = ((n - 2 * j : ℕ) : ℤ) := by
      rw [abs_of_nonneg (by omega), Nat.cast_sub (by omega)]; push_cast; rfl
    rw [heq, card_parIcc]
    have : ((n - 2 * j : ℕ) : ℤ) % 2 = (j : ℤ) % 2 ↔ (n - 2 * j) % 2 = j % 2 := by omega
    split_ifs <;> omega
  have hneg : ∀ j ∈ Finset.Icc 1 (n / 2),
      (parIcc ((n : ℤ) - 2 * |-(j : ℤ)|) (-(j : ℤ))).card =
        if (n - 2 * j) % 2 = j % 2 then n - 2 * j + 1 else n - 2 * j := by
    intro j hj; rw [Finset.mem_Icc] at hj
    have heq : (n : ℤ) - 2 * |-(j : ℤ)| = ((n - 2 * j : ℕ) : ℤ) := by
      rw [abs_neg, abs_of_nonneg (by omega), Nat.cast_sub (by omega)]; push_cast; rfl
    rw [heq, card_parIcc]
    have : ((n - 2 * j : ℕ) : ℤ) % 2 = (-(j : ℤ)) % 2 ↔ (n - 2 * j) % 2 = j % 2 := by omega
    split_ifs <;> omega
  have hsum1 : ∑ j ∈ Finset.Icc 1 (n / 2), (parIcc ((n : ℤ) - 2 * |(j : ℤ)|) (j : ℤ)).card ^ 2 =
      ∑ j ∈ Finset.Icc 1 (n / 2), (if (n - 2 * j) % 2 = j % 2 then n - 2 * j + 1 else n - 2 * j) ^ 2 :=
    Finset.sum_congr rfl (fun j hj => by rw [hpos j hj])
  have hsum2 : ∑ j ∈ Finset.Icc 1 (n / 2), (parIcc ((n : ℤ) - 2 * |-(j : ℤ)|) (-(j : ℤ))).card ^ 2 =
      ∑ j ∈ Finset.Icc 1 (n / 2), (if (n - 2 * j) % 2 = j % 2 then n - 2 * j + 1 else n - 2 * j) ^ 2 :=
    Finset.sum_congr rfl (fun j hj => by rw [hneg j hj])
  rw [h0, hsum1, hsum2]
  ring

lemma sum_id_even (m : ℕ) :
    12 * ((2 * m + 1) ^ 2 +
      2 * ∑ j ∈ Finset.Icc 1 m, (if (2 * m - 2 * j) % 2 = j % 2 then 2 * m - 2 * j + 1 else 2 * m - 2 * j) ^ 2) +
      12 * (2 * (m / 2) + 1) + 24 =
    4 * (2 * m) ^ 3 + 6 * (2 * m) ^ 2 + 20 * (2 * m) + 48 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 => simp
    | 1 => simp
    | k + 2 =>
      have hih := ih k (by omega)
      have hshift : ∑ j ∈ Finset.Icc 1 (k + 2),
          (if (2 * (k + 2) - 2 * j) % 2 = j % 2 then 2 * (k + 2) - 2 * j + 1 else 2 * (k + 2) - 2 * j) ^ 2 =
          (2 * k + 2) ^ 2 + (2 * k + 1) ^ 2 +
          ∑ j ∈ Finset.Icc 1 k, (if (2 * k - 2 * j) % 2 = j % 2 then 2 * k - 2 * j + 1 else 2 * k - 2 * j) ^ 2 := by
        have hI : Finset.Icc 1 (k + 2) = {1, 2} ∪ (Finset.Icc 1 k).image (· + 2) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton, Finset.mem_image]
          constructor
          · intro hx
            by_cases h1 : x = 1; · exact Or.inl (Or.inl h1)
            by_cases h2 : x = 2; · exact Or.inl (Or.inr h2)
            exact Or.inr ⟨x - 2, by omega, by omega⟩
          · rintro ((rfl | rfl) | ⟨y, hy, rfl⟩) <;> omega
        have hd : Disjoint ({1, 2} : Finset ℕ) ((Finset.Icc 1 k).image (· + 2)) := by
          rw [Finset.disjoint_left]; intro x hx1 hx2
          simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_Icc] at hx1 hx2
          rcases hx2 with ⟨y, hy, rfl⟩; rcases hx1 with h | h <;> omega
        rw [hI, Finset.sum_union hd, Finset.sum_pair (by decide),
            Finset.sum_image (fun a _ b _ h => by omega)]
        have h1 : (if (2 * (k + 2) - 2 * 1) % 2 = 1 % 2 then 2 * (k + 2) - 2 * 1 + 1 else 2 * (k + 2) - 2 * 1) = 2 * k + 2 := by
          have : (2 * (k + 2) - 2 * 1) % 2 ≠ 1 % 2 := by omega
          rw [if_neg this]; omega
        have h2 : (if (2 * (k + 2) - 2 * 2) % 2 = 2 % 2 then 2 * (k + 2) - 2 * 2 + 1 else 2 * (k + 2) - 2 * 2) = 2 * k + 1 := by
          have : (2 * (k + 2) - 2 * 2) % 2 = 2 % 2 := by omega
          rw [if_pos this]; omega
        rw [h1, h2]
        congr 1
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have e1 : 2 * (k + 2) - 2 * (j + 2) = 2 * k - 2 * j := by omega
        have e2 : (j + 2) % 2 = j % 2 := by omega
        rw [e1, e2]
      have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
      rw [hshift, hdiv]
      linarith

lemma sum_id_odd (m : ℕ) :
    12 * ((2 * m + 1) ^ 2 +
      2 * ∑ j ∈ Finset.Icc 1 m, (if (2 * m + 1 - 2 * j) % 2 = j % 2 then 2 * m + 1 - 2 * j + 1 else 2 * m + 1 - 2 * j) ^ 2) +
      12 * (2 * (m / 2) + 1) + 24 =
    4 * (2 * m + 1) ^ 3 + 6 * (2 * m + 1) ^ 2 + 20 * (2 * m + 1) + 18 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 => simp
    | 1 => simp
    | k + 2 =>
      have hih := ih k (by omega)
      have hshift : ∑ j ∈ Finset.Icc 1 (k + 2),
          (if (2 * (k + 2) + 1 - 2 * j) % 2 = j % 2 then 2 * (k + 2) + 1 - 2 * j + 1 else 2 * (k + 2) + 1 - 2 * j) ^ 2 =
          (2 * k + 4) ^ 2 + (2 * k + 1) ^ 2 +
          ∑ j ∈ Finset.Icc 1 k, (if (2 * k + 1 - 2 * j) % 2 = j % 2 then 2 * k + 1 - 2 * j + 1 else 2 * k + 1 - 2 * j) ^ 2 := by
        have hI : Finset.Icc 1 (k + 2) = {1, 2} ∪ (Finset.Icc 1 k).image (· + 2) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton, Finset.mem_image]
          constructor
          · intro hx
            by_cases h1 : x = 1; · exact Or.inl (Or.inl h1)
            by_cases h2 : x = 2; · exact Or.inl (Or.inr h2)
            exact Or.inr ⟨x - 2, by omega, by omega⟩
          · rintro ((rfl | rfl) | ⟨y, hy, rfl⟩) <;> omega
        have hd : Disjoint ({1, 2} : Finset ℕ) ((Finset.Icc 1 k).image (· + 2)) := by
          rw [Finset.disjoint_left]; intro x hx1 hx2
          simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_Icc] at hx1 hx2
          rcases hx2 with ⟨y, hy, rfl⟩; rcases hx1 with h | h <;> omega
        rw [hI, Finset.sum_union hd, Finset.sum_pair (by decide),
            Finset.sum_image (fun a _ b _ h => by omega)]
        have h1 : (if (2 * (k + 2) + 1 - 2 * 1) % 2 = 1 % 2 then 2 * (k + 2) + 1 - 2 * 1 + 1 else 2 * (k + 2) + 1 - 2 * 1) = 2 * k + 4 := by
          have : (2 * (k + 2) + 1 - 2 * 1) % 2 = 1 % 2 := by omega
          rw [if_pos this]; omega
        have h2 : (if (2 * (k + 2) + 1 - 2 * 2) % 2 = 2 % 2 then 2 * (k + 2) + 1 - 2 * 2 + 1 else 2 * (k + 2) + 1 - 2 * 2) = 2 * k + 1 := by
          have : (2 * (k + 2) + 1 - 2 * 2) % 2 ≠ 2 % 2 := by omega
          rw [if_neg this]; omega
        rw [h1, h2]
        congr 1
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have e1 : 2 * (k + 2) + 1 - 2 * (j + 2) = 2 * k + 1 - 2 * j := by omega
        have e2 : (j + 2) % 2 = j % 2 := by omega
        rw [e1, e2]
      have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
      rw [hshift, hdiv]
      linarith

-- Lattice count for sr 0 and sr 2: {(s, t) ∈ ℤ × ℤ | |s| + 2 * |t| ≤ k} has cardinality k^2 + k + 1
def stSet (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-((k / 2 : ℕ) : ℤ)) ((k / 2 : ℕ) : ℤ)).biUnion (fun t =>
    (Finset.Icc (-((k : ℤ) - 2 * |t|)) ((k : ℤ) - 2 * |t|)).map
      ⟨fun s => (s, t), fun s1 s2 h => by simp only [Prod.mk.injEq] at h; exact h.1⟩)

lemma mem_stSet {k : ℕ} {s t : ℤ} :
    (s, t) ∈ stSet k ↔ |s| + 2 * |t| ≤ (k : ℤ) := by
  simp only [stSet, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_map,
    Function.Embedding.coeFn_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨t', ⟨ht1, ht2⟩, s', ⟨hs1, hs2⟩, rfl, rfl⟩
    rcases abs_cases s with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases abs_cases t with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  · intro h
    refine ⟨t, ⟨?_, ?_⟩, s, ⟨?_, ?_⟩, rfl⟩ <;>
      (rcases abs_cases s with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases abs_cases t with ⟨_, _⟩ | ⟨_, _⟩ <;> omega)

lemma card_stSet (k : ℕ) : (stSet k).card = k ^ 2 + k + 1 := by
  have hsum : ∀ m : ℕ, (stSet m).card =
      ∑ t ∈ Finset.Icc (-((m / 2 : ℕ) : ℤ)) ((m / 2 : ℕ) : ℤ), (2 * (m - 2 * t.natAbs) + 1) := by
    intro m
    unfold stSet
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl (fun t ht => ?_)
      rw [Finset.mem_Icc] at ht
      rw [Finset.card_map, Int.card_Icc]
      have htabs : |t| = (t.natAbs : ℤ) := Int.abs_eq_natAbs t
      rw [htabs]; omega
    · intro t1 _ t2 _ hne
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at h1 h2
      rcases h1 with ⟨_, _, rfl⟩; rcases h2 with ⟨_, _, h2⟩
      exact hne (congr_arg Prod.snd h2).symm
  rw [hsum]
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => simp
    | 1 => simp
    | m + 2 =>
      have hih := ih m (by omega)
      have hdiv : ((m + 2) / 2 : ℕ) = m / 2 + 1 := by omega
      have hI : Finset.Icc (-(((m + 2) / 2 : ℕ) : ℤ)) (((m + 2) / 2 : ℕ) : ℤ) =
          {-((m / 2 + 1 : ℕ) : ℤ), ((m / 2 + 1 : ℕ) : ℤ)} ∪
            Finset.Icc (-((m / 2 : ℕ) : ℤ)) ((m / 2 : ℕ) : ℤ) := by
        rw [hdiv]; ext x
        simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        push_cast; omega
      have hd : Disjoint ({-((m / 2 + 1 : ℕ) : ℤ), ((m / 2 + 1 : ℕ) : ℤ)} : Finset ℤ)
          (Finset.Icc (-((m / 2 : ℕ) : ℤ)) ((m / 2 : ℕ) : ℤ)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at hx1 hx2
        push_cast at hx1; omega
      have hne : -((m / 2 + 1 : ℕ) : ℤ) ≠ ((m / 2 + 1 : ℕ) : ℤ) := by push_cast; omega
      rw [hI, Finset.sum_union hd, Finset.sum_pair hne]
      have hinner : ∑ t ∈ Finset.Icc (-((m / 2 : ℕ) : ℤ)) ((m / 2 : ℕ) : ℤ),
            (2 * (m + 2 - 2 * t.natAbs) + 1) =
          (∑ t ∈ Finset.Icc (-((m / 2 : ℕ) : ℤ)) ((m / 2 : ℕ) : ℤ), (2 * (m - 2 * t.natAbs) + 1)) +
          4 * (2 * (m / 2) + 1) := by
        have hstep : ∀ t ∈ Finset.Icc (-((m / 2 : ℕ) : ℤ)) ((m / 2 : ℕ) : ℤ),
            2 * (m + 2 - 2 * t.natAbs) + 1 = (2 * (m - 2 * t.natAbs) + 1) + 4 := by
          intro t ht; rw [Finset.mem_Icc] at ht; omega
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_const, Int.card_Icc]
        have hcard : (((m / 2 : ℕ) : ℤ) + 1 - -((m / 2 : ℕ) : ℤ)).toNat = 2 * (m / 2) + 1 := by omega
        rw [hcard]; simp; ring
      rw [hinner, hih]
      have hna1 : (-((m / 2 + 1 : ℕ) : ℤ)).natAbs = m / 2 + 1 := by omega
      have hna2 : (((m / 2 + 1 : ℕ) : ℤ)).natAbs = m / 2 + 1 := by omega
      rw [hna1, hna2]
      have hm : 2 * (m / 2) + m % 2 = m := by omega
      have hsub : m + 2 - 2 * (m / 2 + 1) = m % 2 := by omega
      rw [hsub]
      nlinarith

end
end Neck4Rev

namespace ProofA208971

open OMA.S_oeis_a208971 Neck4Rev
open scoped Classical

private lemma card_fixed_r13 (n : ℕ) (g : ZMod 4) (hg : g = 1 ∨ g = 3) :
    letI := dihedralAction n
    Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.r g)) = 1 := by
  letI := dihedralAction n
  have hzero_valid : isValid n (fun _ => 0) :=
    ⟨fun _ => by simp, by simp, fun _ => by simp, fun _ => by simp⟩
  let z : {f : ZMod 4 → ℤ // isValid n f} := ⟨fun _ => 0, hzero_valid⟩
  have hz_mem : z ∈ MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.r g) := by
    change (DihedralGroup.r g) • z = z
    apply Subtype.ext; ext i; rfl
  rw [Fintype.card_subtype]
  have hset : Finset.univ.filter (fun x : {f : ZMod 4 → ℤ // isValid n f} =>
      x ∈ MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.r g)) = {z} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hx
      change (DihedralGroup.r g) • x = x at hx
      have hf : ∀ i : ZMod 4, x.1 (i + g) = x.1 i := fun i => congr_fun (congr_arg Subtype.val hx) i
      have hsum := x.2.2.1
      have h0 := hf 0; have h1 := hf 1; have h2 := hf 2; have h3 := hf 3
      rcases hg with rfl | rfl
      · change x.1 1 = x.1 0 at h0; change x.1 2 = x.1 1 at h1
        change x.1 3 = x.1 2 at h2; change x.1 0 = x.1 3 at h3
        apply Subtype.ext; ext i; dsimp only [z]
        match i with | 0 => omega | 1 => omega | 2 => omega | 3 => omega
      · change x.1 3 = x.1 0 at h0; change x.1 0 = x.1 1 at h1
        change x.1 1 = x.1 2 at h2; change x.1 2 = x.1 3 at h3
        apply Subtype.ext; ext i; dsimp only [z]
        match i with | 0 => omega | 1 => omega | 2 => omega | 3 => omega
    · rintro rfl; exact hz_mem
  rw [hset, Finset.card_singleton]

private lemma card_fixed_r2 (n : ℕ) :
    letI := dihedralAction n
    Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.r (2 : ZMod 4))) =
      2 * (n / 4) + 1 := by
  letI := dihedralAction n
  rw [Fintype.card_subtype]
  have hIcc : (Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ)).card = 2 * (n / 4) + 1 := by
    rw [Int.card_Icc]; omega
  rw [← hIcc]
  refine Finset.card_bij (fun x _ => x.1 0) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    change (DihedralGroup.r (2 : ZMod 4)) • x = x at hx
    have h0 : x.1 2 = x.1 0 := congr_fun (congr_arg Subtype.val hx) 0
    have h1 : x.1 3 = x.1 1 := congr_fun (congr_arg Subtype.val hx) 1
    have hsum := x.2.2.1
    have hd2 := x.2.2.2.2 0
    change -(n : ℤ) ≤ x.1 0 - 2 * x.1 1 + x.1 2 ∧ x.1 0 - 2 * x.1 1 + x.1 2 ≤ n at hd2
    rw [Finset.mem_Icc]
    omega
  · intro x1 hx1 x2 hx2 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
    change (DihedralGroup.r (2 : ZMod 4)) • x1 = x1 at hx1
    change (DihedralGroup.r (2 : ZMod 4)) • x2 = x2 at hx2
    have h10 : x1.1 2 = x1.1 0 := congr_fun (congr_arg Subtype.val hx1) 0
    have h11 : x1.1 3 = x1.1 1 := congr_fun (congr_arg Subtype.val hx1) 1
    have h20 : x2.1 2 = x2.1 0 := congr_fun (congr_arg Subtype.val hx2) 0
    have h21 : x2.1 3 = x2.1 1 := congr_fun (congr_arg Subtype.val hx2) 1
    have hs1 := x1.2.2.1; have hs2 := x2.2.2.1
    apply Subtype.ext; ext i
    match i with | 0 => omega | 1 => omega | 2 => omega | 3 => omega
  · intro c hc
    rw [Finset.mem_Icc] at hc
    let f : ZMod 4 → ℤ := fun i => match i with | 0 => c | 1 => -c | 2 => c | 3 => -c
    have hval : isValid n f :=
      ⟨fun i => by match i with | 0 => dsimp [f]; omega | 1 => dsimp [f]; omega | 2 => dsimp [f]; omega | 3 => dsimp [f]; omega,
       by dsimp [f]; omega,
       fun i => by match i with | 0 => change -(n : ℤ) ≤ f 1 - f 0 ∧ f 1 - f 0 ≤ n; dsimp [f]; omega | 1 => change -(n : ℤ) ≤ f 2 - f 1 ∧ f 2 - f 1 ≤ n; dsimp [f]; omega | 2 => change -(n : ℤ) ≤ f 3 - f 2 ∧ f 3 - f 2 ≤ n; dsimp [f]; omega | 3 => change -(n : ℤ) ≤ f 0 - f 3 ∧ f 0 - f 3 ≤ n; dsimp [f]; omega,
       fun i => by match i with | 0 => change -(n : ℤ) ≤ f 0 - 2 * f 1 + f 2 ∧ f 0 - 2 * f 1 + f 2 ≤ n; dsimp [f]; omega | 1 => change -(n : ℤ) ≤ f 1 - 2 * f 2 + f 3 ∧ f 1 - 2 * f 2 + f 3 ≤ n; dsimp [f]; omega | 2 => change -(n : ℤ) ≤ f 2 - 2 * f 3 + f 0 ∧ f 2 - 2 * f 3 + f 0 ≤ n; dsimp [f]; omega | 3 => change -(n : ℤ) ≤ f 3 - 2 * f 0 + f 1 ∧ f 3 - 2 * f 0 + f 1 ≤ n; dsimp [f]; omega⟩
    refine ⟨⟨f, hval⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (DihedralGroup.r (2 : ZMod 4)) • (⟨f, hval⟩ : {f : ZMod 4 → ℤ // isValid n f}) = ⟨f, hval⟩
    apply Subtype.ext; ext i
    match i with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl

private lemma card_fixed_sr0 (n : ℕ) :
    letI := dihedralAction n
    Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.sr (0 : ZMod 4))) =
      (n / 2) ^ 2 + (n / 2) + 1 := by
  letI := dihedralAction n
  rw [Fintype.card_subtype, ← card_stSet (n / 2)]
  refine Finset.card_bij (fun x _ => (x.1 0 + x.1 1, -x.1 1)) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    change (DihedralGroup.sr (0 : ZMod 4)) • x = x at hx
    have h13 : x.1 3 = x.1 1 := congr_fun (congr_arg Subtype.val hx) 1
    have hsum := x.2.2.1
    have hd1 := x.2.2.2.2 1; have hd3 := x.2.2.2.2 3
    change -(n : ℤ) ≤ x.1 1 - 2 * x.1 2 + x.1 3 ∧ x.1 1 - 2 * x.1 2 + x.1 3 ≤ n at hd1
    change -(n : ℤ) ≤ x.1 3 - 2 * x.1 0 + x.1 1 ∧ x.1 3 - 2 * x.1 0 + x.1 1 ≤ n at hd3
    rw [mem_stSet]
    rcases abs_cases (x.1 0 + x.1 1) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases abs_cases (-x.1 1) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  · intro x1 hx1 x2 hx2 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
    change (DihedralGroup.sr (0 : ZMod 4)) • x1 = x1 at hx1
    change (DihedralGroup.sr (0 : ZMod 4)) • x2 = x2 at hx2
    have h1 : x1.1 3 = x1.1 1 := congr_fun (congr_arg Subtype.val hx1) 1
    have h2 : x2.1 3 = x2.1 1 := congr_fun (congr_arg Subtype.val hx2) 1
    have hs1 := x1.2.2.1; have hs2 := x2.2.2.1
    simp only [Prod.mk.injEq] at h
    apply Subtype.ext; ext i
    match i with | 0 => omega | 1 => omega | 2 => omega | 3 => omega
  · intro ⟨s, t⟩ hst
    rw [mem_stSet] at hst
    let f : ZMod 4 → ℤ := fun i => match i with | 0 => t + s | 1 => -t | 2 => t - s | 3 => -t
    have hval : isValid n f := by
      rcases abs_cases s with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases abs_cases t with ⟨_, _⟩ | ⟨_, _⟩ <;>
        exact ⟨fun i => by match i with | 0 => dsimp [f]; omega | 1 => dsimp [f]; omega | 2 => dsimp [f]; omega | 3 => dsimp [f]; omega,
         by dsimp [f]; omega,
         fun i => by match i with | 0 => change -(n : ℤ) ≤ f 1 - f 0 ∧ f 1 - f 0 ≤ n; dsimp [f]; omega | 1 => change -(n : ℤ) ≤ f 2 - f 1 ∧ f 2 - f 1 ≤ n; dsimp [f]; omega | 2 => change -(n : ℤ) ≤ f 3 - f 2 ∧ f 3 - f 2 ≤ n; dsimp [f]; omega | 3 => change -(n : ℤ) ≤ f 0 - f 3 ∧ f 0 - f 3 ≤ n; dsimp [f]; omega,
         fun i => by match i with | 0 => change -(n : ℤ) ≤ f 0 - 2 * f 1 + f 2 ∧ f 0 - 2 * f 1 + f 2 ≤ n; dsimp [f]; omega | 1 => change -(n : ℤ) ≤ f 1 - 2 * f 2 + f 3 ∧ f 1 - 2 * f 2 + f 3 ≤ n; dsimp [f]; omega | 2 => change -(n : ℤ) ≤ f 2 - 2 * f 3 + f 0 ∧ f 2 - 2 * f 3 + f 0 ≤ n; dsimp [f]; omega | 3 => change -(n : ℤ) ≤ f 3 - 2 * f 0 + f 1 ∧ f 3 - 2 * f 0 + f 1 ≤ n; dsimp [f]; omega⟩
    refine ⟨⟨f, hval⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (DihedralGroup.sr (0 : ZMod 4)) • (⟨f, hval⟩ : {f : ZMod 4 → ℤ // isValid n f}) = ⟨f, hval⟩
      apply Subtype.ext; ext i
      match i with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
    · simp only [Prod.mk.injEq, f]; omega

private lemma card_fixed_sr2 (n : ℕ) :
    letI := dihedralAction n
    Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.sr (2 : ZMod 4))) =
      (n / 2) ^ 2 + (n / 2) + 1 := by
  letI := dihedralAction n
  rw [Fintype.card_subtype, ← card_stSet (n / 2)]
  refine Finset.card_bij (fun x _ => (x.1 1 + x.1 0, -x.1 0)) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    change (DihedralGroup.sr (2 : ZMod 4)) • x = x at hx
    have h02 : x.1 2 = x.1 0 := congr_fun (congr_arg Subtype.val hx) 0
    have hsum := x.2.2.1
    have hd0 := x.2.2.2.2 0; have hd2 := x.2.2.2.2 2
    change -(n : ℤ) ≤ x.1 0 - 2 * x.1 1 + x.1 2 ∧ x.1 0 - 2 * x.1 1 + x.1 2 ≤ n at hd0
    change -(n : ℤ) ≤ x.1 2 - 2 * x.1 3 + x.1 0 ∧ x.1 2 - 2 * x.1 3 + x.1 0 ≤ n at hd2
    rw [mem_stSet]
    rcases abs_cases (x.1 1 + x.1 0) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases abs_cases (-x.1 0) with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  · intro x1 hx1 x2 hx2 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
    change (DihedralGroup.sr (2 : ZMod 4)) • x1 = x1 at hx1
    change (DihedralGroup.sr (2 : ZMod 4)) • x2 = x2 at hx2
    have h1 : x1.1 2 = x1.1 0 := congr_fun (congr_arg Subtype.val hx1) 0
    have h2 : x2.1 2 = x2.1 0 := congr_fun (congr_arg Subtype.val hx2) 0
    have hs1 := x1.2.2.1; have hs2 := x2.2.2.1
    simp only [Prod.mk.injEq] at h
    apply Subtype.ext; ext i
    match i with | 0 => omega | 1 => omega | 2 => omega | 3 => omega
  · intro ⟨s, t⟩ hst
    rw [mem_stSet] at hst
    let f : ZMod 4 → ℤ := fun i => match i with | 0 => -t | 1 => t + s | 2 => -t | 3 => t - s
    have hval : isValid n f := by
      rcases abs_cases s with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases abs_cases t with ⟨_, _⟩ | ⟨_, _⟩ <;>
        exact ⟨fun i => by match i with | 0 => dsimp [f]; omega | 1 => dsimp [f]; omega | 2 => dsimp [f]; omega | 3 => dsimp [f]; omega,
         by dsimp [f]; omega,
         fun i => by match i with | 0 => change -(n : ℤ) ≤ f 1 - f 0 ∧ f 1 - f 0 ≤ n; dsimp [f]; omega | 1 => change -(n : ℤ) ≤ f 2 - f 1 ∧ f 2 - f 1 ≤ n; dsimp [f]; omega | 2 => change -(n : ℤ) ≤ f 3 - f 2 ∧ f 3 - f 2 ≤ n; dsimp [f]; omega | 3 => change -(n : ℤ) ≤ f 0 - f 3 ∧ f 0 - f 3 ≤ n; dsimp [f]; omega,
         fun i => by match i with | 0 => change -(n : ℤ) ≤ f 0 - 2 * f 1 + f 2 ∧ f 0 - 2 * f 1 + f 2 ≤ n; dsimp [f]; omega | 1 => change -(n : ℤ) ≤ f 1 - 2 * f 2 + f 3 ∧ f 1 - 2 * f 2 + f 3 ≤ n; dsimp [f]; omega | 2 => change -(n : ℤ) ≤ f 2 - 2 * f 3 + f 0 ∧ f 2 - 2 * f 3 + f 0 ≤ n; dsimp [f]; omega | 3 => change -(n : ℤ) ≤ f 3 - 2 * f 0 + f 1 ∧ f 3 - 2 * f 0 + f 1 ≤ n; dsimp [f]; omega⟩
    refine ⟨⟨f, hval⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (DihedralGroup.sr (2 : ZMod 4)) • (⟨f, hval⟩ : {f : ZMod 4 → ℤ // isValid n f}) = ⟨f, hval⟩
      apply Subtype.ext; ext i
      match i with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
    · simp only [Prod.mk.injEq, f]; omega

private lemma card_fixed_sr1 (n : ℕ) :
    letI := dihedralAction n
    Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.sr (1 : ZMod 4))) =
      2 * (n / 2) + 1 := by
  letI := dihedralAction n
  rw [Fintype.card_subtype]
  have hIcc : (Finset.Icc (-((n / 2 : ℕ) : ℤ)) ((n / 2 : ℕ) : ℤ)).card = 2 * (n / 2) + 1 := by
    rw [Int.card_Icc]; omega
  rw [← hIcc]
  refine Finset.card_bij (fun x _ => x.1 0) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    change (DihedralGroup.sr (1 : ZMod 4)) • x = x at hx
    have h01 : x.1 1 = x.1 0 := congr_fun (congr_arg Subtype.val hx) 0
    have h23 : x.1 3 = x.1 2 := congr_fun (congr_arg Subtype.val hx) 2
    have hsum := x.2.2.1
    have hd1 := x.2.2.2.1 1
    change -(n : ℤ) ≤ x.1 2 - x.1 1 ∧ x.1 2 - x.1 1 ≤ n at hd1
    rw [Finset.mem_Icc]
    omega
  · intro x1 hx1 x2 hx2 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
    change (DihedralGroup.sr (1 : ZMod 4)) • x1 = x1 at hx1
    change (DihedralGroup.sr (1 : ZMod 4)) • x2 = x2 at hx2
    have h10 : x1.1 1 = x1.1 0 := congr_fun (congr_arg Subtype.val hx1) 0
    have h12 : x1.1 3 = x1.1 2 := congr_fun (congr_arg Subtype.val hx1) 2
    have h20 : x2.1 1 = x2.1 0 := congr_fun (congr_arg Subtype.val hx2) 0
    have h22 : x2.1 3 = x2.1 2 := congr_fun (congr_arg Subtype.val hx2) 2
    have hs1 := x1.2.2.1; have hs2 := x2.2.2.1
    apply Subtype.ext; ext i
    match i with | 0 => omega | 1 => omega | 2 => omega | 3 => omega
  · intro c hc
    rw [Finset.mem_Icc] at hc
    let f : ZMod 4 → ℤ := fun i => match i with | 0 => c | 1 => c | 2 => -c | 3 => -c
    have hval : isValid n f :=
      ⟨fun i => by match i with | 0 => dsimp [f]; omega | 1 => dsimp [f]; omega | 2 => dsimp [f]; omega | 3 => dsimp [f]; omega,
       by dsimp [f]; omega,
       fun i => by match i with | 0 => change -(n : ℤ) ≤ f 1 - f 0 ∧ f 1 - f 0 ≤ n; dsimp [f]; omega | 1 => change -(n : ℤ) ≤ f 2 - f 1 ∧ f 2 - f 1 ≤ n; dsimp [f]; omega | 2 => change -(n : ℤ) ≤ f 3 - f 2 ∧ f 3 - f 2 ≤ n; dsimp [f]; omega | 3 => change -(n : ℤ) ≤ f 0 - f 3 ∧ f 0 - f 3 ≤ n; dsimp [f]; omega,
       fun i => by match i with | 0 => change -(n : ℤ) ≤ f 0 - 2 * f 1 + f 2 ∧ f 0 - 2 * f 1 + f 2 ≤ n; dsimp [f]; omega | 1 => change -(n : ℤ) ≤ f 1 - 2 * f 2 + f 3 ∧ f 1 - 2 * f 2 + f 3 ≤ n; dsimp [f]; omega | 2 => change -(n : ℤ) ≤ f 2 - 2 * f 3 + f 0 ∧ f 2 - 2 * f 3 + f 0 ≤ n; dsimp [f]; omega | 3 => change -(n : ℤ) ≤ f 3 - 2 * f 0 + f 1 ∧ f 3 - 2 * f 0 + f 1 ≤ n; dsimp [f]; omega⟩
    refine ⟨⟨f, hval⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (DihedralGroup.sr (1 : ZMod 4)) • (⟨f, hval⟩ : {f : ZMod 4 → ℤ // isValid n f}) = ⟨f, hval⟩
    apply Subtype.ext; ext i
    match i with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl

private lemma card_fixed_sr3 (n : ℕ) :
    letI := dihedralAction n
    Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.sr (3 : ZMod 4))) =
      2 * (n / 2) + 1 := by
  letI := dihedralAction n
  rw [Fintype.card_subtype]
  have hIcc : (Finset.Icc (-((n / 2 : ℕ) : ℤ)) ((n / 2 : ℕ) : ℤ)).card = 2 * (n / 2) + 1 := by
    rw [Int.card_Icc]; omega
  rw [← hIcc]
  refine Finset.card_bij (fun x _ => x.1 0) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    change (DihedralGroup.sr (3 : ZMod 4)) • x = x at hx
    have h03 : x.1 3 = x.1 0 := congr_fun (congr_arg Subtype.val hx) 0
    have h12 : x.1 2 = x.1 1 := congr_fun (congr_arg Subtype.val hx) 1
    have hsum := x.2.2.1
    have hd0 := x.2.2.2.1 0
    change -(n : ℤ) ≤ x.1 1 - x.1 0 ∧ x.1 1 - x.1 0 ≤ n at hd0
    rw [Finset.mem_Icc]
    omega
  · intro x1 hx1 x2 hx2 h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
    change (DihedralGroup.sr (3 : ZMod 4)) • x1 = x1 at hx1
    change (DihedralGroup.sr (3 : ZMod 4)) • x2 = x2 at hx2
    have h10 : x1.1 3 = x1.1 0 := congr_fun (congr_arg Subtype.val hx1) 0
    have h11 : x1.1 2 = x1.1 1 := congr_fun (congr_arg Subtype.val hx1) 1
    have h20 : x2.1 3 = x2.1 0 := congr_fun (congr_arg Subtype.val hx2) 0
    have h21 : x2.1 2 = x2.1 1 := congr_fun (congr_arg Subtype.val hx2) 1
    have hs1 := x1.2.2.1; have hs2 := x2.2.2.1
    apply Subtype.ext; ext i
    match i with | 0 => omega | 1 => omega | 2 => omega | 3 => omega
  · intro c hc
    rw [Finset.mem_Icc] at hc
    let f : ZMod 4 → ℤ := fun i => match i with | 0 => c | 1 => -c | 2 => -c | 3 => c
    have hval : isValid n f :=
      ⟨fun i => by match i with | 0 => dsimp [f]; omega | 1 => dsimp [f]; omega | 2 => dsimp [f]; omega | 3 => dsimp [f]; omega,
       by dsimp [f]; omega,
       fun i => by match i with | 0 => change -(n : ℤ) ≤ f 1 - f 0 ∧ f 1 - f 0 ≤ n; dsimp [f]; omega | 1 => change -(n : ℤ) ≤ f 2 - f 1 ∧ f 2 - f 1 ≤ n; dsimp [f]; omega | 2 => change -(n : ℤ) ≤ f 3 - f 2 ∧ f 3 - f 2 ≤ n; dsimp [f]; omega | 3 => change -(n : ℤ) ≤ f 0 - f 3 ∧ f 0 - f 3 ≤ n; dsimp [f]; omega,
       fun i => by match i with | 0 => change -(n : ℤ) ≤ f 0 - 2 * f 1 + f 2 ∧ f 0 - 2 * f 1 + f 2 ≤ n; dsimp [f]; omega | 1 => change -(n : ℤ) ≤ f 1 - 2 * f 2 + f 3 ∧ f 1 - 2 * f 2 + f 3 ≤ n; dsimp [f]; omega | 2 => change -(n : ℤ) ≤ f 2 - 2 * f 3 + f 0 ∧ f 2 - 2 * f 3 + f 0 ≤ n; dsimp [f]; omega | 3 => change -(n : ℤ) ≤ f 3 - 2 * f 0 + f 1 ∧ f 3 - 2 * f 0 + f 1 ≤ n; dsimp [f]; omega⟩
    refine ⟨⟨f, hval⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (DihedralGroup.sr (3 : ZMod 4)) • (⟨f, hval⟩ : {f : ZMod 4 → ℤ // isValid n f}) = ⟨f, hval⟩
    apply Subtype.ext; ext i
    match i with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl

private lemma burnside_a (n : ℕ) :
    8 * a n = (uvwSet n).card + (2 * (n / 4) + 1) + 2 +
      2 * ((n / 2) ^ 2 + (n / 2) + 1) + 2 * (2 * (n / 2) + 1) := by
  letI := dihedralAction n
  have ha : a n = Fintype.card (MulAction.orbitRel.Quotient (DihedralGroup 4) {f : ZMod 4 → ℤ // isValid n f}) := by
    unfold a
    rw [Nat.card_eq_fintype_card]
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (DihedralGroup 4) {f : ZMod 4 → ℤ // isValid n f}
  rw [← ha] at hburn
  have hcardG : Fintype.card (DihedralGroup 4) = 8 := by decide
  rw [hcardG] at hburn
  have huniv : (Finset.univ : Finset (DihedralGroup 4)) =
      {DihedralGroup.r 0, DihedralGroup.r 1, DihedralGroup.r 2, DihedralGroup.r 3,
       DihedralGroup.sr 0, DihedralGroup.sr 1, DihedralGroup.sr 2, DihedralGroup.sr 3} := by
    decide
  have hsum : (∑ g : DihedralGroup 4,
      Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} g)) =
      Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.r (0 : ZMod 4))) +
      Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.r (1 : ZMod 4))) +
      Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.r (2 : ZMod 4))) +
      Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.r (3 : ZMod 4))) +
      Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.sr (0 : ZMod 4))) +
      Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.sr (1 : ZMod 4))) +
      Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.sr (2 : ZMod 4))) +
      Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.sr (3 : ZMod 4))) := by
    rw [huniv]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have hf0 : Fintype.card (MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.r (0 : ZMod 4))) =
      (uvwSet n).card := by
    rw [← card_valid_eq_uvw n, Fintype.card_subtype]
    have hall : ∀ x : {f : ZMod 4 → ℤ // isValid n f},
        x ∈ MulAction.fixedBy {f : ZMod 4 → ℤ // isValid n f} (DihedralGroup.r (0 : ZMod 4)) := by
      intro x; change (1 : DihedralGroup 4) • x = x; exact one_smul _ x
    simp [hall]
  have hf1 := card_fixed_r13 n 1 (Or.inl rfl)
  have hf2 := card_fixed_r2 n
  have hf3 := card_fixed_r13 n 3 (Or.inr rfl)
  have hsr0 := card_fixed_sr0 n
  have hsr1 := card_fixed_sr1 n
  have hsr2 := card_fixed_sr2 n
  have hsr3 := card_fixed_sr3 n
  rw [hsum, hf0, hf1, hf2, hf3, hsr0, hsr1, hsr2, hsr3] at hburn
  omega

theorem main :
    (∀ n : ℕ, 1 ≤ n → Even n → 48 * a n = 2 * n ^ 3 + 6 * n ^ 2 + 28 * n + 48) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → 48 * a n = 2 * n ^ 3 + 6 * n ^ 2 + 22 * n + 18) := by
  constructor
  · rintro n _ ⟨m, rfl⟩
    have hb := burnside_a (m + m)
    have hu := card_uvwSet_nat (m + m)
    have h2m : m + m = 2 * m := by omega
    rw [h2m] at hb hu ⊢
    have hmod : (2 * m) % 2 = 0 := by omega
    have hdiv1 : (2 * m) / 2 = m := by omega
    have hdiv2 : (2 * m) / 4 = m / 2 := by omega
    rw [hmod, if_pos rfl, hdiv1] at hu
    rw [hdiv1, hdiv2, hu] at hb
    have hid := sum_id_even m
    nlinarith
  · rintro n _ ⟨m, rfl⟩
    have hb := burnside_a (2 * m + 1)
    have hu := card_uvwSet_nat (2 * m + 1)
    have hmod : ¬ ((2 * m + 1) % 2 = 0) := by omega
    have hdiv1 : (2 * m + 1) / 2 = m := by omega
    have hdiv2 : (2 * m + 1) / 4 = m / 2 := by omega
    rw [if_neg hmod, hdiv1] at hu
    rw [hdiv1, hdiv2, hu] at hb
    have hid := sum_id_odd m
    nlinarith

end ProofA208971

theorem OMA.solution : type_of% @OMA.S_oeis_a208971.main :=
  ProofA208971.main

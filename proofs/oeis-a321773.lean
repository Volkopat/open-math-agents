import OMAStatements.S_oeis_a321773
import Mathlib

open OMA.S_oeis_a321773
open PowerSeries

namespace P321773

open Finset

theorem dm_iff (x y z : ℕ) :
    ([x, y, z].dedup.map (fun v => [x, y, z].count v)).Nodup ↔ (x = y ∨ y = z ∨ x = z) := by
  by_cases hxy : x = y <;> by_cases hyz : y = z <;> by_cases hxz : x = z <;> subst_vars <;>
    simp_all [List.dedup_cons_of_notMem, List.dedup_cons_of_mem, List.count_cons] <;>
    split_ifs <;> omega

abbrev R3 (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)

abbrev Pt (n : ℕ) (t : ℕ × ℕ × ℕ) : Prop :=
  0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n

theorem cardA (n : ℕ) : ((R3 n).filter (fun t => Pt n t ∧ t.1 = t.2.1)).card = (n - 1) / 2 := by
  have : (R3 n).filter (fun t => Pt n t ∧ t.1 = t.2.1) =
      (Icc 1 ((n - 1) / 2)).image (fun x => (x, x, n - 2 * x)) := by
    ext ⟨x, y, z⟩
    simp only [R3, Pt, mem_filter, mem_product, mem_range, mem_image, mem_Icc, Prod.mk.injEq]
    constructor
    · rintro ⟨_, ⟨h1, h2, h3, h4⟩, h5⟩
      exact ⟨x, ⟨by omega, by omega⟩, rfl, by omega, by omega⟩
    · rintro ⟨w, ⟨hw1, hw2⟩, rfl, rfl, rfl⟩
      omega
  rw [this, card_image_of_injective _ (fun u v h => by simpa using congrArg Prod.fst h)]
  simp

theorem cardB (n : ℕ) : ((R3 n).filter (fun t => Pt n t ∧ t.2.1 = t.2.2)).card = (n - 1) / 2 := by
  have : (R3 n).filter (fun t => Pt n t ∧ t.2.1 = t.2.2) =
      (Icc 1 ((n - 1) / 2)).image (fun x => (n - 2 * x, x, x)) := by
    ext ⟨x, y, z⟩
    simp only [R3, Pt, mem_filter, mem_product, mem_range, mem_image, mem_Icc, Prod.mk.injEq]
    constructor
    · rintro ⟨_, ⟨h1, h2, h3, h4⟩, h5⟩
      exact ⟨y, ⟨by omega, by omega⟩, by omega, rfl, by omega⟩
    · rintro ⟨w, ⟨hw1, hw2⟩, rfl, rfl, rfl⟩
      omega
  rw [this, card_image_of_injective _ (fun u v h => by simpa using congrArg (fun p => p.2.1) h)]
  simp

theorem cardC (n : ℕ) : ((R3 n).filter (fun t => Pt n t ∧ t.1 = t.2.2)).card = (n - 1) / 2 := by
  have : (R3 n).filter (fun t => Pt n t ∧ t.1 = t.2.2) =
      (Icc 1 ((n - 1) / 2)).image (fun x => (x, n - 2 * x, x)) := by
    ext ⟨x, y, z⟩
    simp only [R3, Pt, mem_filter, mem_product, mem_range, mem_image, mem_Icc, Prod.mk.injEq]
    constructor
    · rintro ⟨_, ⟨h1, h2, h3, h4⟩, h5⟩
      exact ⟨x, ⟨by omega, by omega⟩, rfl, by omega, by omega⟩
    · rintro ⟨w, ⟨hw1, hw2⟩, rfl, rfl, rfl⟩
      omega
  rw [this, card_image_of_injective _ (fun u v h => by simpa using congrArg Prod.fst h)]
  simp

theorem cardD (n : ℕ) :
    ((R3 n).filter (fun t => Pt n t ∧ t.1 = t.2.1 ∧ t.2.1 = t.2.2)).card =
      if 0 < n ∧ n % 3 = 0 then 1 else 0 := by
  split_ifs with h
  · rw [card_eq_one]
    refine ⟨(n / 3, n / 3, n / 3), ?_⟩
    ext ⟨x, y, z⟩
    simp only [R3, Pt, mem_filter, mem_product, mem_range, mem_singleton, Prod.mk.injEq]
    omega
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨x, y, z⟩ _
    simp only [Pt]
    omega

theorem closed (n : ℕ) :
    a n = 3 * ((n - 1) / 2) - 2 * (if 0 < n ∧ n % 3 = 0 then 1 else 0) := by
  let A := (R3 n).filter (fun t => Pt n t ∧ t.1 = t.2.1)
  let B := (R3 n).filter (fun t => Pt n t ∧ t.2.1 = t.2.2)
  let C := (R3 n).filter (fun t => Pt n t ∧ t.1 = t.2.2)
  let D := (R3 n).filter (fun t => Pt n t ∧ t.1 = t.2.1 ∧ t.2.1 = t.2.2)
  have hS : a n = (A ∪ (B ∪ C)).card := by
    unfold a
    congr 1
    ext ⟨x, y, z⟩
    simp only [A, B, C, mem_filter, mem_union, dm_iff]
    tauto
  have h1 : A ∩ (B ∪ C) = D := by
    ext ⟨x, y, z⟩
    simp only [A, B, C, D, Pt, mem_filter, mem_union, mem_inter]
    constructor
    · rintro ⟨⟨h0, hp, h⟩, h' | h'⟩ <;> refine ⟨h0, hp, ?_⟩ <;> omega
    · rintro ⟨h0, hp, h, h'⟩
      exact ⟨⟨h0, hp, h⟩, Or.inl ⟨h0, hp, h'⟩⟩
  have h2 : B ∩ C = D := by
    ext ⟨x, y, z⟩
    simp only [B, C, D, Pt, mem_filter, mem_inter]
    constructor
    · rintro ⟨⟨h0, hp, h⟩, _, _, h'⟩; refine ⟨h0, hp, ?_⟩; omega
    · rintro ⟨h0, hp, h, h'⟩
      refine ⟨⟨h0, hp, h'⟩, h0, hp, ?_⟩; omega
  have e1 := card_union_add_card_inter A (B ∪ C)
  have e2 := card_union_add_card_inter B C
  rw [h1] at e1
  rw [h2] at e2
  have cA := cardA n
  have cB := cardB n
  have cC := cardC n
  have cD := cardD n
  change A.card = _ at cA
  change B.card = _ at cB
  change C.card = _ at cC
  change D.card = _ at cD
  rw [hS]
  split_ifs at cD ⊢ with hh <;> omega

end P321773

theorem OMA.solution : type_of% @OMA.S_oeis_a321773.main := by
  have hc := P321773.closed
  have hrec : ∀ n : ℕ, 7 < n → a n + a (n - 5) = a (n - 2) + a (n - 3) := by
    intro n hn
    rw [hc, hc, hc, hc]
    split_ifs <;> omega
  refine ⟨?_, hrec, ?_⟩
  · have e : ((1 : PowerSeries ℤ) - X) ^ 2 * (1 + X) * (1 + X + X ^ 2) =
        1 - X ^ 2 - X ^ 3 + X ^ 5 := by ring
    have e2 : (X : PowerSeries ℤ) ^ 3 * (1 + 3 * X + 5 * X ^ 2) =
        X ^ 3 + C (3 : ℤ) * X ^ 4 + C (5 : ℤ) * X ^ 5 := by
      rw [map_ofNat, map_ofNat]; ring
    rw [e, e2]
    ext n
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, coeff_mul_X_pow', coeff_mk,
      coeff_X_pow, coeff_C]
    rcases le_or_gt n 7 with h | h
    · interval_cases n <;> simp [hc]
    · have := hrec n h
      split_ifs <;> omega
  · intro n hn
    rw [hc]
    have h6 : (n - 3) % 6 < 6 := Nat.mod_lt _ (by norm_num)
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 6 ∧ n = 6 * q + r + 3 :=
      ⟨(n - 3) / 6, (n - 3) % 6, h6, by omega⟩
    have : (6 * q + r + 3 - 3) % 6 = r := by omega
    rw [this]
    interval_cases r <;> simp [kk] <;> split_ifs <;> omega

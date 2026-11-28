import OMAStatements.S_oeis_a106252
import Mathlib.Tactic

open Finset OMA.S_oeis_a106252

theorem OMA.count (n : ℕ) : a n = n + n / 2 + n / 3 := by
  have e : triples n = ((Icc 1 n).image (fun x => (x, x, x)) ∪
      (Icc 1 (n / 2)).image (fun x => (x, x, 2 * x))) ∪
      (Icc 1 (n / 3)).image (fun x => (x, 2 * x, 3 * x)) := by
    ext ⟨x, y, z⟩
    simp only [triples, mem_filter, mem_product, mem_Icc, mem_union, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hx, _⟩, _, _, hzn⟩, hxy, hyz, _, ⟨c, hc⟩, ⟨d, hd⟩⟩
      have : d < 3 := by by_contra h; nlinarith
      interval_cases d <;> (have : c < 4 := by by_contra h; nlinarith) <;> interval_cases c <;>
        first
        | omega
        | exact Or.inl (Or.inl ⟨x, by omega, rfl, by omega, by omega⟩)
        | exact Or.inl (Or.inr ⟨x, by omega, rfl, by omega, by omega⟩)
        | exact Or.inr ⟨x, by omega, rfl, by omega, by omega⟩
    · rintro ((⟨k, h, rfl, rfl, rfl⟩ | ⟨k, h, rfl, rfl, rfl⟩) | ⟨k, h, rfl, rfl, rfl⟩)
      · exact ⟨by omega, by omega, by omega, ⟨2, by omega⟩, ⟨2, by omega⟩, ⟨2, by omega⟩⟩
      · exact ⟨by omega, by omega, by omega, ⟨3, by omega⟩, ⟨3, by omega⟩, ⟨1, by omega⟩⟩
      · exact ⟨by omega, by omega, by omega, ⟨5, by omega⟩, ⟨2, by omega⟩, ⟨1, by omega⟩⟩
  rw [a, e, card_union_of_disjoint, card_union_of_disjoint, card_image_of_injective,
    card_image_of_injective, card_image_of_injective] <;>
    first
    | exact fun _ _ h => congrArg Prod.fst h
    | (simp only [disjoint_left, mem_union, mem_image, mem_Icc]; rintro _ h ⟨y, hy, rfl⟩; simp at h; omega)
    | simp

theorem OMA.solution : type_of% @OMA.S_oeis_a106252.main := by
  intro n
  simp only [OMA.count]
  omega

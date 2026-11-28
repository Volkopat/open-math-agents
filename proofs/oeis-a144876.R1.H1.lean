import OMAReductions.R_oeis_a144876_R1
import Mathlib

open Finset OMA.S_oeis_a144876

private def move (swap : Bool) (sx sy : ℤ) (o : Cell) (c : Cell) : Cell :=
  let d := if swap then (c.2, c.1) else c
  (o.1 + sx * d.1, o.2 + sy * d.2)

private theorem signedMul {x y : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ∨ x * y = -1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num

private theorem moveInverse (s : Bool) (x y : ℤ) (o : Cell)
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    ∃ (u v : ℤ) (p : Cell), (u = 1 ∨ u = -1) ∧ (v = 1 ∨ v = -1) ∧
      Function.LeftInverse (move s u v p) (move s x y o) := by
  cases s
  · refine ⟨x, y, (-x * o.1, -y * o.2), hx, hy, fun c => ?_⟩
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [move]
  · refine ⟨y, x, (-y * o.2, -x * o.1), hy, hx, fun c => ?_⟩
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [move]

private theorem moveComposition (s t : Bool) (x y u v : ℤ) (o p : Cell)
    (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) :
    ∃ (r : Bool) (a b : ℤ) (q : Cell), (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧
      move t u v p ∘ move s x y o = move r a b q := by
  cases t
  · refine ⟨s, u*x, v*y, move false u v p o, signedMul hu hx, signedMul hv hy, ?_⟩
    funext c
    cases s <;> apply Prod.ext <;> simp [move] <;> ring
  · refine ⟨!s, u*y, v*x, move true u v p o, signedMul hu hy, signedMul hv hx, ?_⟩
    funext c
    cases s <;> apply Prod.ext <;> simp [move] <;> ring

private theorem congruentSameCard {a b : Shape} (h : congruent a b) : a.card = b.card := by
  obtain ⟨s, x, y, o, hx, hy, h⟩ := h
  change b = a.image (move s x y o) at h
  obtain ⟨u, v, p, _, _, hi⟩ := moveInverse s x y o hx hy
  rw [h, card_image_of_injective _ hi.injective]

private theorem commonImage {a b r : Shape} (ha : congruent a r) (hb : congruent b r) :
    congruent a b := by
  obtain ⟨s, x, y, o, hx, hy, ha⟩ := ha
  obtain ⟨t, u, v, p, hu, hv, hb⟩ := hb
  change r = a.image (move s x y o) at ha
  change r = b.image (move t u v p) at hb
  obtain ⟨w, z, q, hw, hz, hi⟩ := moveInverse t u v p hu hv
  obtain ⟨i, j, k, l, hj, hk, he⟩ := moveComposition s t x y w z o q hx hy hw hz
  refine ⟨i, j, k, l, hj, hk, ?_⟩
  change b = a.image (move i j k l)
  have hid : move t w z q ∘ move t u v p = id := funext hi
  rw [← he, ← image_image, ← ha, hb, image_image, hid, image_id]

theorem OMA.solution : OMA.R_oeis_a144876_R1.H1 := by
  classical
  intro t catalogue pieces hpieces hcatalogue
  let small := pieces.filter fun a => a.card < t
  have hchoose : ∀ a ∈ small, ∃ r ∈ catalogue, congruent a r :=
    fun a ha => hcatalogue a (mem_filter.mp ha).1 (mem_filter.mp ha).2
  choose f hf hCong using hchoose
  let imageSmall := small.attach.image fun a => f a.val a.property
  have hsub : imageSmall ⊆ catalogue := by
    intro r hr
    obtain ⟨a, _, rfl⟩ := mem_image.mp hr
    exact hf a.val a.property
  have hinj : Set.InjOn (fun a : small => f a.val a.property) (↑small.attach : Set small) := by
    intro a _ b _ h
    change f a.val a.property = f b.val b.property at h
    apply Subtype.ext
    exact hpieces.2 _ (mem_filter.mp a.property).1 _ (mem_filter.mp b.property).1
      (commonImage (hCong a.val a.property) (by rw [h]; exact hCong b.val b.property))
  have hdeficit : (∑ a ∈ pieces, (t - a.card)) ≤ ∑ r ∈ catalogue, (t - r.card) := by
    calc
      _ = ∑ a ∈ small, (t - a.card) := by
        symm
        apply sum_filter_of_ne
        intro a ha h
        omega
      _ = ∑ a ∈ small.attach, (t - a.val.card) := (sum_attach _ _).symm
      _ = ∑ r ∈ imageSmall, (t - r.card) := by
        dsimp only [imageSmall]
        rw [sum_image hinj]
        exact sum_congr rfl fun a _ => by rw [congruentSameCard (hCong a.val a.property)]
      _ ≤ _ := sum_le_sum_of_subset hsub
  calc
    t * pieces.card = ∑ _a ∈ pieces, t := by simp [mul_comm]
    _ ≤ ∑ a ∈ pieces, (a.card + (t - a.card)) :=
      sum_le_sum fun _ _ => by omega
    _ ≤ _ := by rw [sum_add_distrib]; exact Nat.add_le_add_left hdeficit _
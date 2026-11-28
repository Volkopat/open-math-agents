import OMAReductions.R_Erdos23_erdos_23_R1
import Mathlib

/-! Two cut bounds for the dense maximal step of Erdős 23.
A map to the pentagon yields a cut with at most n² monochromatic edges on 5n
vertices. A proper three-colouring yields a cut with at most a third of the
edges rounded down. Both arguments also apply to non-maximal graphs.
-/

namespace OMA.R_Erdos23_erdos_23_R1_H1_R1

open SimpleGraph Finset
open OMA.R_Erdos23_erdos_23_R1 (same_mk)

-- On cutting the boundary between i and i + 1, take classes i + 2 and i + 4
-- on one side. Among consecutive classes only that boundary is monochromatic.
lemma pentagon_pattern : ∀ i a b : Fin 5, (a + 1 = b ∨ b + 1 = a) →
    ((a = i + 2 ∨ a = i + 4) ↔ (b = i + 2 ∨ b = i + 4)) →
    (a = i ∧ b = i + 1) ∨ (a = i + 1 ∧ b = i) := by decide +kernel

lemma three_pattern : ∀ a b : Fin 3, a ≠ b →
    (∑ t : Fin 3, if (a = t ↔ b = t) then 1 else 0) = (1 : ℕ) := by decide +kernel

lemma light_pair (n : ℕ) (a : Fin 5 → ℕ) (hs : ∑ i, a i = 5 * n) :
    ∃ i : Fin 5, a i * a (i + 1) ≤ n ^ 2 := by
  have small : ∃ i : Fin 5, a i + a (i + 1) ≤ 2 * n := by
    by_contra! h
    have total : a 0 + (a 1 + (a 2 + (a 3 + a 4))) = 5 * n := by
      simpa only [Fin.sum_univ_five, Nat.add_assoc] using hs
    have h0 : 2 * n < a 0 + a 1 := h 0
    have h1 : 2 * n < a 1 + a 2 := h 1
    have h2 : 2 * n < a 2 + a 3 := h 2
    have h3 : 2 * n < a 3 + a 4 := h 3
    have h4 : 2 * n < a 4 + a 0 := h 4
    omega
  obtain ⟨i, hi⟩ := small
  have hsquare :
      ((a i : ℤ) + a (i + 1)) * ((a i : ℤ) + a (i + 1)) ≤
        (2 * (n : ℤ)) * (2 * (n : ℤ)) := by
    exact_mod_cast (Nat.mul_le_mul hi hi)
  have hp : (a i : ℤ) * a (i + 1) ≤ (n : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((a i : ℤ) - a (i + 1))]
  exact ⟨i, by exact_mod_cast hp⟩

open scoped Classical

lemma pentagon_cut {V : Type*} [Fintype V] (n : ℕ) (horder : Fintype.card V = 5 * n)
    (G : SimpleGraph V) (f : V → Fin 5)
    (edges : ∀ x y, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) :
    ∃ S : Finset V,
      (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ n ^ 2 := by
  classical
  let fiber (i : Fin 5) := univ.filter (fun x : V => f x = i)
  have total : (∑ i : Fin 5, (fiber i).card) = 5 * n := by
    calc
      _ = (univ : Finset V).card := by
        simpa [fiber] using
          (Finset.sum_card_fiberwise_eq_card_filter (univ : Finset V) (univ : Finset (Fin 5)) f)
      _ = 5 * n := (Finset.card_univ).trans horder
  obtain ⟨i, hi⟩ := light_pair n (fun j => (fiber j).card) total
  let S := univ.filter (fun x : V => f x = i + 2 ∨ f x = i + 4)
  let pairs := fiber i ×ˢ fiber (i + 1)
  let edgeOf (p : V × V) := s(p.1, p.2)
  have sub : G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S)) ⊆
      pairs.image edgeOf := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      obtain ⟨hmem, hsame⟩ := Finset.mem_filter.mp he
      have hxy : G.Adj x y := mem_edgeFinset.mp hmem
      have hp := (same_mk S x y).mp hsame
      have colors : (f x = i + 2 ∨ f x = i + 4) ↔ (f y = i + 2 ∨ f y = i + 4) := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hp
      rcases pentagon_pattern i (f x) (f y) (edges x y hxy) colors with h | h
      · refine Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
        · simpa [fiber] using h.1
        · simpa [fiber] using h.2
      · refine Finset.mem_image.mpr ⟨(y, x), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
        · simpa [fiber] using h.2
        · simpa [fiber] using h.1
        · exact Sym2.eq_swap
  refine ⟨S, (Finset.card_le_card sub).trans (Finset.card_image_le.trans ?_)⟩
  simpa only [pairs, Finset.card_product] using hi

lemma three_class_cut {V : Type*} [Fintype V] (G : SimpleGraph V)
    (c : V → Fin 3) (hproper : ∀ x y, G.Adj x y → c x ≠ c y) :
    ∃ S : Finset V,
      (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤
        G.edgeFinset.card / 3 := by
  classical
  let side (t : Fin 3) := univ.filter (fun x : V => c x = t)
  let same (t : Fin 3) (e : Sym2 V) := ∀ x ∈ e, ∀ y ∈ e, (x ∈ side t ↔ y ∈ side t)
  let cost (t : Fin 3) := (G.edgeFinset.filter (same t)).card
  have edgeOnce (e : Sym2 V) (he : e ∈ G.edgeFinset) :
      (∑ t : Fin 3, if same t e then 1 else 0) = (1 : ℕ) := by
    induction e using Sym2.ind with
    | h x y =>
      have pair (t : Fin 3) : same t s(x, y) ↔ (c x = t ↔ c y = t) := by
        simpa only [same, side, Finset.mem_filter, Finset.mem_univ, true_and] using
          (same_mk (side t) x y)
      simp_rw [pair]
      exact three_pattern (c x) (c y) (hproper x y (mem_edgeFinset.mp he))
  have total : (∑ t : Fin 3, cost t) = G.edgeFinset.card := by
    calc
      _ = ∑ t : Fin 3, ∑ e ∈ G.edgeFinset, (if same t e then 1 else 0 : ℕ) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        dsimp only [cost]
        rw [Finset.card_filter]
      _ = ∑ e ∈ G.edgeFinset, ∑ t : Fin 3, (if same t e then 1 else 0 : ℕ) := Finset.sum_comm
      _ = ∑ _e ∈ G.edgeFinset, (1 : ℕ) := Finset.sum_congr rfl edgeOnce
      _ = _ := by simp
  have cheap : ∃ t : Fin 3, cost t ≤ G.edgeFinset.card / 3 := by
    by_contra! h
    have total' : cost 0 + (cost 1 + cost 2) = G.edgeFinset.card := by
      simpa only [Fin.sum_univ_three, Nat.add_assoc] using total
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    omega
  obtain ⟨t, ht⟩ := cheap
  exact ⟨side t, ht⟩

-- In the lower density range only graphs without a proper three-colouring remain.
def H1 : Prop :=
  ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
    ∀ G : SimpleGraph V, G.CliqueFree 3 →
      (∀ L : SimpleGraph V, G ≤ L → L.CliqueFree 3 → L = G) →
      2 * n ^ 2 ≤ G.edgeFinset.card → G.edgeFinset.card ≤ 3 * n ^ 2 + 2 →
      (¬ ∃ c : V → Fin 3, ∀ x y, G.Adj x y → c x ≠ c y) →
      ∃ S : Finset V,
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ n ^ 2

-- Above the three-colour counting threshold only graphs without a map to C₅ remain.
def H2 : Prop :=
  ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
    ∀ G : SimpleGraph V, G.CliqueFree 3 →
      (∀ L : SimpleGraph V, G ≤ L → L.CliqueFree 3 → L = G) →
      3 * n ^ 2 + 3 ≤ G.edgeFinset.card →
      (¬ ∃ f : V → Fin 5, ∀ x y, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x) →
      ∃ S : Finset V,
        (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ n ^ 2

theorem main : H1 → H2 → OMA.R_Erdos23_erdos_23_R1.H1 := by
  intro low high n V instV horder G triangleFree maximal dense
  classical
  by_cases small : G.edgeFinset.card ≤ 3 * n ^ 2 + 2
  · by_cases colored : ∃ c : V → Fin 3, ∀ x y, G.Adj x y → c x ≠ c y
    · obtain ⟨c, hc⟩ := colored
      obtain ⟨S, hS⟩ := three_class_cut G c hc
      exact ⟨S, hS.trans (by omega)⟩
    · exact low n V horder G triangleFree maximal dense small colored
  · by_cases mapped : ∃ f : V → Fin 5, ∀ x y, G.Adj x y → f x + 1 = f y ∨ f y + 1 = f x
    · obtain ⟨f, hf⟩ := mapped
      exact pentagon_cut n horder G f hf
    · exact high n V horder G triangleFree maximal (by omega) mapped

end OMA.R_Erdos23_erdos_23_R1_H1_R1

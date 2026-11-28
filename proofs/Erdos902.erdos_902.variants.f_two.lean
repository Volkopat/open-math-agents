import FormalConjectures.ErdosProblems.«902»

-- Problem: Erdős Problem 902 — f two
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/902.lean:130 (declaration Erdos902.erdos_902.variants.f_two)
/-! Tournament counting: shortened adaptation of @luciusacarr’s merged proof, using the double-counting method in Wilder’s Erdos902Counting.lean. -/
-- Credit: @jaredwilder; original merged proof @luciusacarr
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset

namespace OMA

/-- In a tournament with property `S_2`, every vertex has at least three in-neighbours. -/
theorem indeg_ge_three {m : ℕ} (hm : 2 ≤ m) (G : Digraph (Fin m))
    [DecidableRel G.Adj]
    (hG : G.IsTournament) (hS : Erdos902.HasPropertyS G 2) (v : Fin m) :
    3 ≤ (univ.filter (fun x => G.Adj x v)).card := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  obtain ⟨u, hu⟩ := exists_ne v
  obtain ⟨x1, hx1, h1⟩ := hS {v, u} (card_pair hu.symm)
  have a1 : G.Adj x1 v := h1 v (by simp)
  have n1 : v ≠ x1 := fun h => hG.1 v (h ▸ a1)
  obtain ⟨x2, hx2, h2⟩ := hS {v, x1} (card_pair n1)
  have a2 : G.Adj x2 v := h2 v (by simp)
  have b2 : G.Adj x2 x1 := h2 x1 (by simp)
  have n2 : v ≠ x2 := fun h => hG.1 v (h ▸ a2)
  obtain ⟨x3, hx3, h3⟩ := hS {v, x2} (card_pair n2)
  have a3 : G.Adj x3 v := h3 v (by simp)
  have b3 : G.Adj x3 x2 := h3 x2 (by simp)
  have e12 : x1 ≠ x2 := fun h => hG.1 x1 (h ▸ b2)
  have e23 : x2 ≠ x3 := fun h => hG.1 x2 (h ▸ b3)
  have e13 : x1 ≠ x3 := by
    intro h
    rw [← h] at b3
    exact ((hG.2 x1 x2 e12).1 b3) b2
  have hsub : ({x1, x2, x3} : Finset (Fin m)) ⊆ univ.filter (fun x => G.Adj x v) := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rw [mem_filter]
    rcases hy with rfl | rfl | rfl
    · exact ⟨mem_univ _, a1⟩
    · exact ⟨mem_univ _, a2⟩
    · exact ⟨mem_univ _, a3⟩
  calc 3 = ({x1, x2, x3} : Finset (Fin m)).card := (card_eq_three.mpr ⟨x1, x2, x3, e12, e13, e23, rfl⟩).symm
    _ ≤ _ := card_le_card hsub

/-- A tournament on `m` vertices has `m * m - m` ordered pairs, half of them arcs. -/
theorem two_mul_arcs {m : ℕ} (G : Digraph (Fin m)) [DecidableRel G.Adj]
    (hG : G.IsTournament) :
    2 * ∑ v : Fin m, (univ.filter (fun x => G.Adj x v)).card = m * m - m := by
  classical
  let I (x y : Fin m) : ℕ := if G.Adj x y then 1 else 0
  have hI (x y : Fin m) : I x y + I y x + (if x = y then 1 else 0) = 1 := by
    by_cases h : x = y
    · subst y; simp [I, hG.1]
    · by_cases e : G.Adj x y
      · simp [I, h, e, (hG.2 x y h).1 e]
      · simp [I, h, e, (hG.2 y x (Ne.symm h)).2 e]
  have hi (v : Fin m) : (∑ x : Fin m, I x v) = (univ.filter (fun x => G.Adj x v)).card := by
    simp only [I, card_filter]
  have ht : (∑ y : Fin m, ∑ x : Fin m, (I x y + I y x + (if x = y then 1 else 0))) = m*m := by
    simp [hI]
  simp only [sum_add_distrib, hi, sum_ite_eq', mem_univ, if_true, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at ht
  rw [sum_comm (f := fun y x => I y x)] at ht
  simp only [hi] at ht
  omega

theorem seven_le {m : ℕ} (hm : 2 ≤ m) (G : Digraph (Fin m))
    (hG : G.IsTournament) (hS : Erdos902.HasPropertyS G 2) : 7 ≤ m := by
  classical
  have h1 : ∑ _v : Fin m, 3 ≤ ∑ v : Fin m, (univ.filter (fun x => G.Adj x v)).card :=
    sum_le_sum (fun v _ => indeg_ge_three hm G hG hS v)
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h1
  have h2 := two_mul_arcs G hG
  by_contra hlt
  have hm7 : m < 7 := by omega
  interval_cases m <;> omega

end OMA

theorem OMA.solution : type_of% @Erdos902.erdos_902.variants.f_two := by
  refine le_antisymm Erdos902.f_two_le (le_csInf ⟨7, ?_⟩ ?_)
  · refine ⟨by norm_num, ⟨fun a b => b - a ∈ ({1, 2, 4} : Finset (Fin 7))⟩,
      ⟨by decide, by decide⟩, ?_⟩
    intro E hE
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hE
    have key : ∀ a b : Fin 7, a ≠ b → ∃ x, x ≠ a ∧ x ≠ b ∧
        a - x ∈ ({1, 2, 4} : Finset (Fin 7)) ∧ b - x ∈ ({1, 2, 4} : Finset (Fin 7)) := by
      decide
    obtain ⟨x, hxa, hxb, ha, hb⟩ := key a b hab
    refine ⟨x, by simp [hxa, hxb], fun e he => ?_⟩
    rcases Finset.mem_insert.1 he with rfl | he
    · exact ha
    · rw [Finset.mem_singleton.1 he]
      exact hb
  · rintro m ⟨hm, G, hG, hS⟩
    exact OMA.seven_le hm G hG hS

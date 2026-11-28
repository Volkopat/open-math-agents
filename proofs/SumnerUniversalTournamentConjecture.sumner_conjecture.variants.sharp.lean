import FormalConjectures.Wikipedia.SumnerUniversalTournamentConjecture
import Mathlib.Combinatorics.SimpleGraph.Star

open Digraph SimpleGraph SumnerUniversalTournamentConjecture

theorem OMA.solution : type_of% @SumnerUniversalTournamentConjecture.sumner_conjecture.variants.sharp := by
  classical
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  let off (u v : Fin (2 * m + 1)) : ℕ := if u.1 < v.1 then v.1 - u.1 else v.1 + (2 * m + 1) - u.1
  let D : Digraph (Option (Fin (m + 1))) := ⟨fun u v => u = none ∧ v ≠ none⟩
  let G : Digraph (Fin (2 * m + 1)) := ⟨fun u v => off u v ≤ m⟩
  refine ⟨_, inferInstance, inferInstance, D, Classical.decRel _, by simp,
    ⟨starGraph none, isTree_starGraph _, by rintro _ _ ⟨rfl, h2⟩; exact starGraph_center_adj h2.symm,
      fun u v h => by rw [starGraph_adj] at h; change (u = none ∧ v ≠ none) ↔ ¬(v = none ∧ u ≠ none); grind⟩,
    _, inferInstance, inferInstance, G, Classical.decRel _, by simp; omega,
    ⟨fun u => by change ¬off u u ≤ m; simp [off]; omega,
      fun u v huv => by
        have := u.2; have := v.2; have : u.1 ≠ v.1 := fun h => huv (Fin.ext h)
        change off u v ≤ m ↔ ¬off v u ≤ m; dsimp [off]; split <;> split <;> omega⟩,
    ?_⟩
  rintro ⟨f, hf⟩
  have hpos (u v : Fin (2 * m + 1)) : 0 < off u v := by have := u.2; dsimp [off]; split <;> omega
  let g (i : Fin (m + 1)) : Fin m := ⟨off (f none) (f (some i)) - 1, by
    have : off (f none) (f (some i)) ≤ m := f.map_adj' (show D.Adj none (some i) from ⟨rfl, by simp⟩)
    have := hpos (f none) (f (some i)); omega⟩
  have hg : Function.Injective g := fun i j h => by
    have he : off (f none) (f (some i)) - 1 = off (f none) (f (some j)) - 1 := congrArg Fin.val h
    have := hpos (f none) (f (some i)); have := hpos (f none) (f (some j))
    have := (f none).2; have := (f (some i)).2; have := (f (some j)).2
    exact Option.some.inj <| hf <| Fin.ext <| by dsimp [off] at he; split at he <;> split at he <;> omega
  simpa using Fintype.card_le_of_injective g hg

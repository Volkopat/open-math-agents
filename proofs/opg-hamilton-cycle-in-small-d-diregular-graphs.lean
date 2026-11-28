import OMAStatements.S_opg_hamilton_cycle_in_small_d_diregular_graphs

/-!
Guninski's counterexample to Jackson's conjecture (arXiv:1602.06380, Claim 1.1)
has arcs of offsets 2, 3 and 8 modulo 12. Translation lets the exhaustive
search start at zero.
-/

namespace JacksonCertificate

open OMA.S_opg_hamilton_cycle_in_small_d_diregular_graphs

abbrev V := Fin 12

def neighbors (u : V) : List V := [u + 2, u + 3, u + 8]

def graph : Digraph V := ⟨fun u v => v ∈ neighbors u⟩

instance : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (v ∈ neighbors u))

/-- Test the closing arc after appending exactly k unused vertices. -/
def closes (start : V) : Nat → V → List V → Bool
  | 0, u, _ => (neighbors u).contains start
  | k + 1, u, used =>
      (neighbors u).any fun v =>
        !(used.contains v) && closes start k v (v :: used)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem noCycleFromZero : closes 0 11 0 [0] = false := by decide +kernel

/-- A cyclic ordering extends every prefix through the remaining search steps.
The used vertices all come from indices at most i. -/
theorem follows (a : V → V) (hinj : Function.Injective a)
    (edge : ∀ i, a (finRotate 12 i) ∈ neighbors (a i))
    (k : ℕ) (i : V) (hi : i.val + k = 11) (used : List V)
    (prefixBound : ∀ v ∈ used, ∃ j : V, j.val ≤ i.val ∧ a j = v) :
    closes (a 0) k (a i) used = true := by
  induction k generalizing i used with
  | zero =>
    have hlast : i = Fin.last 11 := Fin.ext (by change i.val = 11; omega)
    subst i
    simpa [closes, finRotate_last] using edge (Fin.last 11)
  | succ k ih =>
    let j : V := ⟨i.val + 1, by omega⟩
    have hj : finRotate 12 i = j := finRotate_of_lt (show i.val < 11 by omega)
    have fresh : a j ∉ used := by
      intro hm
      obtain ⟨t, ht, he⟩ := prefixBound _ hm
      have h := congrArg Fin.val (hinj he)
      change t.val = i.val + 1 at h
      omega
    apply List.any_eq_true.mpr
    refine ⟨a j, hj ▸ edge i, ?_⟩
    have htail : closes (a 0) k (a j) (a j :: used) = true := by
      apply ih j (by change i.val + 1 + k = 11; omega)
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨j, le_rfl, rfl⟩
      · obtain ⟨t, ht, he⟩ := prefixBound _ hv
        exact ⟨t, ht.trans (Nat.le_succ _), he⟩
    simp [fresh, htail]

theorem noHamilton : ¬ HasHamiltonCycle graph := by
  unfold HasHamiltonCycle
  rw [Fintype.card_fin]
  rintro ⟨c, hc⟩
  let a (i : V) := c i - c 0
  have hzero : a 0 = 0 := sub_self _
  have hinj : Function.Injective a := fun i j h => c.injective (sub_left_inj.mp h)
  have edge (i : V) : a (finRotate 12 i) ∈ neighbors (a i) := by
    have h := hc i
    change c (finRotate 12 i) ∈ neighbors (c i) at h
    simp only [neighbors, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    rcases h with h | h | h
    · exact Or.inl (by dsimp [a]; rw [h]; abel)
    · exact Or.inr (Or.inl (by dsimp [a]; rw [h]; abel))
    · exact Or.inr (Or.inr (by dsimp [a]; rw [h]; abel))
  have result := follows a hinj edge 11 0 (by decide) [a 0] (by
    intro v hv
    exact ⟨0, le_rfl, (List.mem_singleton.mp hv).symm⟩)
  rw [hzero, noCycleFromZero] at result
  contradiction

end JacksonCertificate

open JacksonCertificate OMA.S_opg_hamilton_cycle_in_small_d_diregular_graphs

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_hamilton_cycle_in_small_d_diregular_graphs.main) := by
  intro claim
  apply noHamilton
  apply claim V graph 3 (by decide)
  · unfold IsOriented
    decide +kernel
  · decide +kernel
  · decide

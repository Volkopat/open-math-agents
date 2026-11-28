import FormalConjectures.ErdosProblems.«23»

/-! # Edge-disjoint pentagons in the balanced blow-up of the five-cycle -/
-- Credit: @steveDOTdigital
namespace OMA.Pentagons

open SimpleGraph Erdos23

-- Each pair labels one cycle. The last coordinate is a Latin square entry,
-- so either adjacent pair of vertices recovers the two labels.
def vertex {n : ℕ} [NeZero n] (p : Fin n × Fin n) (i : Fin 5) : ZMod 5 × Fin n :=
  (i, ![p.1, p.2, p.1, p.2, p.1 + p.2] i)

theorem adjacent {n : ℕ} [NeZero n] (p : Fin n × Fin n) (i : Fin 5) :
    (blowupC5 n).Adj (vertex p i) (vertex p (i + 1)) := by
  apply (fromRel_adj _ _ _).2
  refine ⟨fun h => ?_, Or.inl (Or.inl rfl)⟩
  exact (by decide : ∀ t : Fin 5, t ≠ t + 1) i (congrArg Prod.fst h)

theorem recover {n : ℕ} [NeZero n] {p q : Fin n × Fin n} {i j : Fin 5}
    (h : s(vertex p i, vertex p (i + 1)) = s(vertex q j, vertex q (j + 1))) :
    p = q := by
  rcases Sym2.eq_iff.mp h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hij : i = j := congrArg Prod.fst hx
    subst j
    have h₁ := congrArg Prod.snd hx
    have h₂ := congrArg Prod.snd hy
    fin_cases i <;> simp_all [vertex, Prod.ext_iff]
  · have h₁ : i = j + 1 := congrArg Prod.fst hx
    have h₂ : i + 1 = j := congrArg Prod.fst hy
    exact False.elim ((by decide : ∀ a b : Fin 5, a = b + 1 → a + 1 ≠ b) i j h₁ h₂)

-- Every binary coloring agrees on the ends of some edge of a pentagon.
theorem odd_cycle (c : Fin 5 → Fin 2) : ∃ i, c i = c (i + 1) := by
  exact (by decide : ∀ f : Fin 5 → Fin 2, ∃ i, f i = f (i + 1)) c

end OMA.Pentagons

open SimpleGraph Erdos23 OMA.Pentagons

theorem OMA.solution : type_of% @Erdos23.blowupC5_tight := by
  classical
  intro n hn H _ hBip
  let _ : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨c⟩ := hBip
  let missing := (blowupC5 n).edgeFinset \ H.edgeFinset
  have findEdge (p : Fin n × Fin n) :
      ∃ i : Fin 5, s(vertex p i, vertex p (i + 1)) ∈ missing := by
    obtain ⟨i, hi⟩ := odd_cycle (fun t => c (vertex p t))
    refine ⟨i, Finset.mem_sdiff.mpr ⟨mem_edgeFinset.mpr (adjacent p i), ?_⟩⟩
    intro h
    exact c.valid (mem_edgeFinset.mp h) hi
  choose idx hidx using findEdge
  let pick (p : Fin n × Fin n) : ↥missing :=
    ⟨s(vertex p (idx p), vertex p (idx p + 1)), hidx p⟩
  have inj : Function.Injective pick := fun _ _ h => recover (congrArg Subtype.val h)
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, pow_two] using Fintype.card_le_of_injective pick inj

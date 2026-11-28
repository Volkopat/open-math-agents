import FormalConjectures.Wikipedia.BusyBeaver

open Turing BusyBeaver Machine

namespace OMA

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] [Subsingleton Λ] (M : Machine Γ Λ)

lemma W {a d} (h : M default default = some (some default, ⟨a, d⟩)) k : ∃ T : Tape Γ,
    M.multiStep (init []) k = some ⟨some default, T⟩ ∧ T.head = default ∧
      (d = .left → T.left = .mk []) ∧ (d = .right → T.right = .mk []) := by
  induction k with
  | zero => exact ⟨_, rfl, rfl, fun _ => rfl, fun _ => rfl⟩
  | succ k ih =>
    obtain ⟨T, e, h1, h2, h3⟩ := ih
    refine ⟨_, by simp [e, step, h1, h]; rfl, ?_⟩
    cases d <;> simp_all [Tape.write, Tape.move]

lemma B (N : ℕ) (hN : M.haltingNumber = N) : N ≤ 1 := by
  rcases hM : M default default with _ | ⟨_ | q, a, d⟩
  iterate 2 exact_mod_cast hN ▸
    (show M.haltingNumber ≤ (1 : ℕ) from sInf_le ⟨1, by simp [HaltsAfter, init, Tape.mk₁, Tape.mk₂, Tape.mk', step, hM], rfl⟩)
  obtain rfl := Subsingleton.elim q default
  rw [show M.haltingNumber = ⊤ from sInf_eq_top.2 ?_] at hN
  · simp at hN
  rintro _ ⟨n, hn, rfl⟩
  obtain ⟨_, h, -⟩ := W M hM (n + 1); rw [HaltsAfter, h] at hn; cases hn

def C : Candidate 1 := ⟨Bool, Unit, inferInstance, rfl, inferInstance, inferInstance, rfl,
  inferInstance, fun _ _ => some (none, ⟨default, .right⟩), (isHalting_iff_exists_haltsAt _).2 ⟨1, rfl⟩⟩

end OMA

theorem OMA.solution : type_of% @BusyBeaver.BB_1 := by
  unfold BB
  refine IsGreatest.csSup_eq ⟨⟨OMA.C, haltingNumber_def OMA.C.M 1 ⟨_, rfl⟩ rfl⟩, ?_⟩
  rintro N ⟨C, h⟩
  have := Fintype.card_le_one_iff_subsingleton.1 C.Λ_card.le
  exact OMA.B C.M N h

import FormalConjectures.Wikipedia.BusyBeaver

/-! Pointed relabeling semiconjugates the partial transitions, so it preserves
all halting times. The previous proof is credited to @Genbox. -/

namespace OMABB
open Turing Turing.BusyBeaver

section
variable {Γ Λ Γ' Λ' : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited Γ'] [Inhabited Λ']

structure Relabel (Γ Λ Γ' Λ' : Type*) [Inhabited Γ] [Inhabited Λ] [Inhabited Γ'] [Inhabited Λ'] where
  symbol : Γ ≃ Γ'
  state : Λ ≃ Λ'
  blank : symbol default = default
  start : state default = default

namespace Relabel
variable (r : Relabel Γ Λ Γ' Λ')

def machine (M : Machine Γ Λ) : Machine Γ' Λ' :=
  fun q a => (M (r.state.symm q) (r.symbol.symm a)).map
    fun (q', s) => (q'.map r.state, Stmt.write (r.symbol s.symbol) s.dir)

def tapeMap : PointedMap Γ Γ' := ⟨r.symbol, r.blank⟩

def config (c : Cfg Γ Λ) : Cfg Γ' Λ' :=
  ⟨c.q.map r.state, c.tape.map r.tapeMap⟩

lemma step (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    (r.machine M).step (r.config c) = (M.step c).map r.config := by
  rcases c with ⟨_ | q, T⟩
  · rfl
  simp only [config, Option.map_some, Machine.step, machine, Tape.map_fst]
  have ht : r.tapeMap T.head = r.symbol T.head := rfl
  rw [ht, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases M q T.head with _ | ⟨q', ⟨s, d⟩⟩
  · rfl
  simp [config, Tape.map_move, Tape.map_write, tapeMap]

lemma halts_iff (M : Machine Γ Λ) (n : ℕ) :
    (r.machine M).HaltsAfter (Machine.init []) n ↔ M.HaltsAfter (Machine.init []) n := by
  have init : r.config (Machine.init []) = Machine.init [] := by
    simp only [config, Machine.init, Option.map_some, r.start, Tape.map_mk₁, List.map_nil]
  have semi : Function.Semiconj (Option.map r.config)
      (fun c => c.bind M.step) (fun c => c.bind (r.machine M).step) := by
    rintro (_ | c)
    · rfl
    exact (r.step M c).symm
  have e := semi.iterate_right (n + 1) (some (Machine.init []))
  change (M.multiStep (Machine.init []) (n + 1)).map r.config =
    (r.machine M).multiStep (r.config (Machine.init [])) (n + 1) at e
  rw [init] at e
  rw [Machine.HaltsAfter, Machine.HaltsAfter, ← e, Option.map_eq_none_iff]

lemma result (M : Machine Γ Λ) (h : M.IsHalting) :
    (r.machine M).IsHalting ∧ (r.machine M).haltingNumber = M.haltingNumber := by
  constructor
  · simpa only [Machine.isHalting_iff_exists_haltsAt, r.halts_iff] using h
  · simp only [Machine.haltingNumber, r.halts_iff]

end Relabel
end

lemma exists_equiv {α : Type} [Fintype α] [Inhabited α] {n : ℕ} [NeZero n]
    (h : Fintype.card α = n) : ∃ e : α ≃ Fin n, e default = default := by
  let e := Fintype.equivFinOfCardEq h
  exact ⟨e.trans (Equiv.swap (e default) default), by simp⟩

instance : Finite (Stmt (Fin 2)) :=
  Finite.of_surjective (fun p : Fin 2 × Bool => Stmt.write p.1 (if p.2 then Dir.left else Dir.right))
    (by rintro ⟨a, d⟩; cases d <;> first | exact ⟨(a, true), rfl⟩ | exact ⟨(a, false), rfl⟩)

end OMABB

open Turing Turing.BusyBeaver OMABB in
theorem OMA.solution : type_of% @BusyBeaver.sanity_check := by
  intro n hn
  unfold BusyBeaver.BB
  let S := {N : ℕ | ∃ C : BusyBeaver.Candidate n, C.M.haltingNumber = ↑N}
  let T := {N | ∃ (M : Machine (Fin 2) (Fin n)) (_ : M.IsHalting), M.haltingNumber = N}
  have he : T = (fun k : ℕ => (k : ℕ∞)) '' S := by
    ext N
    constructor
    · rintro ⟨M, hM, rfl⟩
      obtain ⟨k, hk⟩ := (Machine.isHalting_iff_exists_haltsAt M).mp hM
      have hle : M.haltingNumber ≤ ↑k := sInf_le ⟨k, hk, rfl⟩
      obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top k) hle)
      refine ⟨l, ⟨⟨Fin 2, Fin n, inferInstance, by simp, inferInstance, inferInstance,
        by simp, inferInstance, M, hM⟩, hl.symm⟩, hl⟩
    · rintro ⟨k, ⟨C, hC⟩, rfl⟩
      obtain ⟨eΓ, hΓ⟩ := exists_equiv C.Γ_card
      obtain ⟨eΛ, hΛ⟩ := exists_equiv C.Λ_card
      let r : Relabel C.Γ C.Λ (Fin 2) (Fin n) := ⟨eΓ, eΛ, hΓ, hΛ⟩
      exact ⟨r.machine C.M, (r.result C.M C.M_isHalting).1, (r.result C.M C.M_isHalting).2.trans hC⟩
  have : Finite (Machine (Fin 2) (Fin n)) := by unfold Machine; infer_instance
  have hfinite : T.Finite := (Set.finite_range fun M : Machine (Fin 2) (Fin n) =>
    M.haltingNumber).subset fun _ ⟨M, _, h⟩ => ⟨M, h⟩
  have hbdd : BddAbove S :=
    (Set.Finite.of_finite_image (he ▸ hfinite) (fun a _ b _ h => by exact_mod_cast h)).bddAbove
  change (↑(sSup S) : ℕ∞) = sSup T
  rw [he, ENat.natCast_sSup hbdd, sSup_image]

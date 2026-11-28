import FormalConjectures.Wikipedia.TotalColoringConjecture

/-! Colour vertex v by 2v and edge uv by u + v in ZMod q = Fin q, q the least odd number ≥ n. -/

open SimpleGraph

theorem OMA.solution :
    type_of% @TotalColoringConjecture.total_coloring_conjecture.variants.complete_graph := by
  intro n
  let q := 2 * (n / 2) + 1
  have hn : n ≤ q := by omega
  let f : Fin n → ZMod q := Fin.castLE hn
  have hf : f.Injective := Fin.castLE_injective hn
  have h2 : IsUnit (2 : ZMod q) :=
    (ZMod.isUnit_iff_coprime 2 q).2 (Nat.prime_two.coprime_iff_not_dvd.2 (by omega))
  let es : Sym2 (Fin n) → ZMod q := Sym2.lift ⟨fun u v => f u + f v, fun _ _ => add_comm _ _⟩
  have heq {v : Fin n} {e : Sym2 (Fin n)} (h : v ∈ e) : es e = f v + f (Sym2.Mem.other h) :=
    congrArg es (Sym2.other_spec h).symm
  refine (Nat.sInf_le (s := {k | (completeGraph (Fin n)).TotalColorable k})
    ⟨Sum.elim (fun v => 2 * f v) (fun e => es e.1),
      fun _ _ huv h => huv.ne (hf (h2.mul_right_inj.mp h)),
      fun e d hne ⟨v, he, hd⟩ h => hne <| Subtype.ext <| (Sym2.other_spec he).symm.trans <| by
        rw [hf <| add_left_cancel <| (heq he).symm.trans <| h.trans (heq hd)]; exact Sym2.other_spec hd,
      fun v e he h => Sym2.other_ne ((completeGraph _).not_isDiag_of_mem_edgeSet e.2) he
        (hf (add_left_cancel ((two_mul _).symm.trans (h.trans (heq he))))).symm⟩).trans ?_
  simp; omega

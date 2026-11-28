import OMAStatements.S_oeis_a008934

open OMA.S_oeis_a008934

namespace TournamentCount

abbrev Chain (m s : ℕ) :=
  {f : Fin (m + 1) → ℕ // f 0 = s ∧
    ∀ j : Fin m, f j.castSucc < f j.succ ∧ f j.succ ≤ 2 * f j.castSucc}

def splitFirst (m s : ℕ) :
    Chain (m + 1) s ≃ (Σ t : Finset.Ioc s (2 * s), Chain m t.val) where
  toFun f := by
    have h := f.property.2 0
    change f.val 0 < f.val 1 ∧ f.val 1 ≤ 2 * f.val 0 at h
    rw [f.property.1] at h
    exact ⟨⟨f.val 1, Finset.mem_Ioc.mpr h⟩,
      ⟨fun i => f.val i.succ, rfl, fun j => f.property.2 j.succ⟩⟩
  invFun
    | ⟨t, f⟩ => ⟨Fin.cons s f.val, by
        refine ⟨rfl, ?_⟩
        intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simpa [Fin.cons_zero, Fin.cons_one, f.property.1] using Finset.mem_Ioc.mp t.property
        · exact f.property.2 i⟩
  left_inv f := by
    apply Subtype.ext
    change Fin.cons s (Fin.tail f.val) = f.val
    simpa only [f.property.1] using Fin.cons_self_tail f.val
  right_inv := by
    rintro ⟨⟨t, ht⟩, ⟨f, hf, h⟩⟩
    change f 0 = t at hf
    subst t
    rfl

instance zeroSubsingleton (s : ℕ) : Subsingleton (Chain 0 s) :=
  ⟨fun f g => Subtype.ext (funext fun i => by
    rw [show i = 0 from @Subsingleton.elim (Fin 1) _ i 0]
    exact f.property.1.trans g.property.1.symm)⟩

instance finiteChain (m s : ℕ) : Finite (Chain m s) := by
  induction m generalizing s with
  | zero => infer_instance
  | succ m ih =>
    let (t : Finset.Ioc s (2 * s)) : Finite (Chain m t.val) := ih _
    exact Finite.of_equiv _ (splitFirst m s).symm

lemma card_chain (m s : ℕ) : Nat.card (Chain m s) = nest m s := by
  classical
  induction m generalizing s with
  | zero =>
    exact Nat.card_of_subsingleton ⟨fun _ => s, rfl, Fin.elim0⟩
  | succ m ih =>
    rw [Nat.card_congr (splitFirst m s), Nat.card_sigma, nest]
    simp_rw [ih]
    rw [Finset.sum_coe_sort]
    apply Finset.sum_nbij' (fun t => t - s) (fun i => s + i)
    all_goals
      intro x hx
      simp only [Finset.mem_Ioc, Finset.mem_Icc] at *
    all_goals first | omega | congr 1 <;> omega

end TournamentCount

theorem OMA.solution : type_of% @OMA.S_oeis_a008934.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  change Nat.card (TournamentCount.Chain (m + 1) 1) = nest m 2
  rw [TournamentCount.card_chain, nest]
  simp

import OMAStatements.S_opg_bene_conjecture_graph_theoretic_form_0
import Mathlib

namespace OMA.BenesDisproof

open OMA.S_opg_bene_conjecture_graph_theoretic_form_0

private def adj : Fin 6 → Fin 6 → Prop := fun a b =>
  (a.val < 3 ∧ b.val < 3 ∧ ¬ (a.val = 0 ∧ b.val = 0)) ∨
  (3 ≤ a.val ∧ 3 ≤ b.val ∧ ¬ (a.val = 3 ∧ b.val = 3)) ∨
  (a.val = 0 ∧ b.val = 3) ∨
  (a.val = 3 ∧ b.val = 0)

private instance : DecidableRel adj := fun a b => by
  unfold adj
  infer_instance

private lemma out_reg : ∀ a : Fin 6, (Finset.univ.filter fun b => adj a b).card = 3 := by
  decide

private lemma in_reg : ∀ b : Fin 6, (Finset.univ.filter fun a => adj a b).card = 3 := by
  decide

private lemma ext_conn : ExternallyConnected adj 3 := by
  intro s t
  have h : ∃ u v : Fin 6, adj s u ∧ adj u v ∧ adj v t := by
    revert s t
    decide
  rcases h with ⟨u, v, h1, h2, h3⟩
  refine ⟨![s, u, v, t], ?_, rfl, rfl⟩
  intro i
  fin_cases i
  · exact h1
  · exact h2
  · exact h3

private lemma adj_cross {a b : Fin 6} (ha : a.val < 3) (hb : 3 ≤ b.val) (hab : adj a b) :
    a = 0 ∧ b = 3 := by
  rcases hab with ⟨_, hblt, _⟩ | ⟨hage, _, _⟩ | ⟨ha0, hb3⟩ | ⟨ha3, _⟩
  · omega
  · omega
  · exact ⟨Fin.ext ha0, Fin.ext hb3⟩
  · omega

private lemma exists_cross (p : Fin 7 → Fin 6) (h0 : (p 0).val < 3) (h6 : 3 ≤ (p (Fin.last 6)).val) :
    ∃ i : Fin 6, (p i.castSucc).val < 3 ∧ 3 ≤ (p i.succ).val := by
  by_contra h
  push Not at h
  have hall : ∀ k : Fin 7, (p k).val < 3 := by
    intro ⟨k, hk⟩
    induction k with
    | zero => exact h0
    | succ k ih =>
      have hk' : k < 6 := by omega
      have hprev : (p ⟨k, by omega⟩).val < 3 := ih (by omega)
      have hstep := h ⟨k, hk'⟩ hprev
      exact hstep
  have hlast := hall (Fin.last 6)
  omega

end OMA.BenesDisproof

open OMA.S_opg_bene_conjecture_graph_theoretic_form_0 OMA.BenesDisproof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_bene_conjecture_graph_theoretic_form_0.main) := by
  intro hmain
  have hrear := hmain 6 3 adj out_reg in_reg 3 (by omega) ext_conn
  let src : Fin 6 × Fin 3 → Fin 6 := fun e => e.1
  let tgt : Fin 6 × Fin 3 → Fin 6 := fun e => ⟨(e.1.val + 3) % 6, Nat.mod_lt _ (by omega)⟩
  have hsrc : ∀ a : Fin 6, Fintype.card {e : Fin 6 × Fin 3 // src e = a} = 3 := by
    intro a
    refine Fintype.card_eq.mpr ⟨{
      toFun := fun x => x.1.2
      invFun := fun j => ⟨(a, j), rfl⟩
      left_inv := fun ⟨⟨x, j⟩, hx⟩ => by
        simp only [src] at hx
        subst hx
        rfl
      right_inv := fun _ => rfl
    }⟩ |>.trans (Fintype.card_fin 3)
  have htgt : ∀ b : Fin 6, Fintype.card {e : Fin 6 × Fin 3 // tgt e = b} = 3 := by
    intro b
    let invB : Fin 6 := ⟨(b.val + 3) % 6, Nat.mod_lt _ (by omega)⟩
    have hinv : tgt (invB, 0) = b := by
      apply Fin.ext
      change ((b.val + 3) % 6 + 3) % 6 = b.val
      omega
    refine (Fintype.card_eq.mpr ⟨{
      toFun := fun x => x.1.2
      invFun := fun j => ⟨(invB, j), by simpa [tgt] using hinv⟩
      left_inv := fun ⟨⟨x, j⟩, hx⟩ => by
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          have hx' : (x.val + 3) % 6 = b.val := congrArg Fin.val hx
          change (b.val + 3) % 6 = x.val
          omega
        · rfl
      right_inv := fun _ => rfl
    }⟩).trans (Fintype.card_fin 3)
  obtain ⟨P, hPpath, hPdisj⟩ := hrear (Fin 6 × Fin 3) src tgt hsrc htgt
  have hcross : ∀ x : Fin 3 × Fin 3,
      ∃ i : Fin 6,
        P (⟨x.1.val, by omega⟩, x.2) i.castSucc = 0 ∧
        P (⟨x.1.val, by omega⟩, x.2) i.succ = 3 := by
    intro x
    let e : Fin 6 × Fin 3 := (⟨x.1.val, by omega⟩, x.2)
    have hp := hPpath e
    have h0 : (P e 0).val < 3 := by
      rw [hp.2.1]
      exact x.1.isLt
    have h6 : 3 ≤ (P e (Fin.last 6)).val := by
      rw [hp.2.2]
      change 3 ≤ (x.1.val + 3) % 6
      omega
    obtain ⟨i, hi1, hi2⟩ := exists_cross (P e) h0 h6
    have hadj := hp.1 i
    obtain ⟨h0', h3'⟩ := adj_cross hi1 hi2 hadj
    exact ⟨i, h0', h3'⟩
  choose f hf0 hf3 using hcross
  have hfinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    let ex : Fin 6 × Fin 3 := (⟨x.1.val, by omega⟩, x.2)
    let ey : Fin 6 × Fin 3 := (⟨y.1.val, by omega⟩, y.2)
    have hene : ex ≠ ey := by
      intro heq
      apply hne
      apply Prod.ext
      · apply Fin.ext
        exact congrArg (fun p : Fin 6 × Fin 3 => p.1.val) heq
      · exact congrArg (fun p : Fin 6 × Fin 3 => p.2) heq
    have hd := hPdisj ex ey hene (f x)
    apply hd
    have hy0 : P ey (f x).castSucc = 0 := by rw [hxy]; exact hf0 y
    have hy3 : P ey (f x).succ = 3 := by rw [hxy]; exact hf3 y
    exact Prod.ext ((hf0 x).trans hy0.symm) ((hf3 x).trans hy3.symm)
  have hcard := Fintype.card_le_of_injective f hfinj
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  omega

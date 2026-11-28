import OMAStatements.S_arxiv_2101_11233

namespace OMA.P_arxiv_2101_11233

open OMA.S_arxiv_2101_11233 SimpleGraph

private def c4 (e : Sym2 (Fin 4)) : ℤ :=
  if (0 : Fin 4) ∈ e then 1 else -1

private def P4 : SimpleGraph (Fin 4) where
  Adj u v := u.val + 1 = v.val ∨ v.val + 1 = u.val
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun u h => by omega⟩

private instance : DecidableRel P4.Adj :=
  fun u v => inferInstanceAs (Decidable (u.val + 1 = v.val ∨ v.val + 1 = u.val))

private lemma c4_pm1 : ∀ e ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset, c4 e = 1 ∨ c4 e = -1 := by
  intro e _
  unfold c4
  split_ifs <;> simp

private lemma c4_zero_sum : (∑ e ∈ (⊤ : SimpleGraph (Fin 4)).edgeFinset, c4 e) = 0 := by
  decide

private lemma P4_edgeFinset_card : P4.edgeFinset.card = 3 := by
  decide

private lemma P4_maxDegree : P4.maxDegree = 2 := by
  decide

private lemma P4_deg_0 : P4.degree (0 : Fin 4) = 1 := by decide
private lemma P4_deg_3 : P4.degree (3 : Fin 4) = 1 := by decide

private lemma P4_isAcyclic : P4.IsAcyclic := by
  intro v p hp
  have hlen3 : 3 ≤ p.length := hp.three_le_length
  have hnd : p.support.tail.Nodup := hp.support_nodup
  -- Every vertex on a cycle has degree >= 2 in P4, so neither 0 nor 3 can appear in p.support!
  have hno_end : ∀ w ∈ p.support, w ≠ (0 : Fin 4) ∧ w ≠ (3 : Fin 4) := by
    intro w hw
    have hdeg2 : 2 ≤ P4.degree w := by
      let q := p.rotate w hw
      have hq : q.IsCycle := hp.rotate hw
      have hq_len : 3 ≤ q.length := hq.three_le_length
      cases hq_eq : q with
      | nil => simp [hq_eq] at hq_len
      | cons h1 r =>
        cases hr_eq : r with
        | nil => simp [hq_eq, hr_eq] at hq_len
        | cons h2 r2 =>
          rename_i u1 u2
          have hrev : q.reverse.IsCycle := hq.reverse
          have hrev_len : 3 ≤ q.reverse.length := by simpa using hq_len
          cases hrev_eq : q.reverse with
          | nil => simp [hrev_eq] at hrev_len
          | cons hlast rrev =>
            rename_i ulast
            have hadj1 : P4.Adj w u1 := h1
            have hadj2 : P4.Adj w ulast := hlast
            have hne : u1 ≠ ulast := by
              intro heq
              subst heq
              have hed_nd : q.edges.Nodup := hq.edges_nodup
              have hq_edges : q.edges = s(w, u1) :: r.edges := by rw [hq_eq]; rfl
              have hrev_edges : q.reverse.edges = s(w, u1) :: rrev.edges := by rw [hrev_eq]; rfl
              have hmem_last : s(w, u1) ∈ r.edges := by
                have hrev_eq_edges : q.edges.reverse = q.reverse.edges := (Walk.edges_reverse q).symm
                rw [hq_edges, List.reverse_cons] at hrev_eq_edges
                have hr_ne : r.edges ≠ [] := by
                  rw [hr_eq]; simp
                have hlast_eq : (r.edges.reverse ++ [s(w, u1)]).head? = r.edges.reverse.head? := by
                  cases hrr : r.edges.reverse with
                  | nil => exact absurd (List.reverse_eq_nil_iff.mp hrr) hr_ne
                  | cons a l => rfl
                have hhead1 : q.reverse.edges.head? = some s(w, u1) := by rw [hrev_edges]; rfl
                rw [← hrev_eq_edges, hlast_eq] at hhead1
                have hmem_rev : s(w, u1) ∈ r.edges.reverse := List.mem_of_head? hhead1
                exact List.mem_reverse.mp hmem_rev
              rw [hq_edges, List.nodup_cons] at hed_nd
              exact hed_nd.1 hmem_last
            have hsub : ({u1, ulast} : Finset (Fin 4)) ⊆ P4.neighborFinset w := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rw [mem_neighborFinset]
              rcases hz with rfl | rfl
              · exact hadj1
              · exact hadj2
            have hcard : ({u1, ulast} : Finset (Fin 4)).card = 2 := Finset.card_pair hne
            have := Finset.card_le_card hsub
            rw [hcard, card_neighborFinset_eq_degree] at this
            exact this
    constructor
    · intro h0; subst h0; rw [P4_deg_0] at hdeg2; omega
    · intro h3; subst h3; rw [P4_deg_3] at hdeg2; omega
  have hsub_tail : p.support.tail.toFinset ⊆ ({1, 2} : Finset (Fin 4)) := by
    intro w hw
    rw [List.mem_toFinset] at hw
    have hw_supp : w ∈ p.support := List.mem_of_mem_tail hw
    have ⟨h0, h3⟩ := hno_end w hw_supp
    fin_cases w <;> simp_all
  have hcard1 : p.support.tail.toFinset.card = p.support.tail.length := List.toFinset_card_of_nodup hnd
  have hcard2 : p.support.tail.toFinset.card ≤ 2 := by
    calc p.support.tail.toFinset.card ≤ ({1, 2} : Finset (Fin 4)).card := Finset.card_le_card hsub_tail
      _ = 2 := by decide
  have hlen_tail : p.support.tail.length = p.length := by
    rw [List.length_tail, Walk.length_support]
    omega
  omega

private lemma odd_sum_pm1 {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℤ)
    (hf : ∀ x ∈ s, f x = 1 ∨ f x = -1) (hodd : Odd s.card) :
    Odd (∑ x ∈ s, f x) := by
  have hpar : ∃ k : ℤ, (∑ x ∈ s, f x) = 2 * k + (s.card : ℤ) := by
    clear hodd
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert a s ha ih =>
      obtain ⟨k, hk⟩ := ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one, hk]
      rcases hf a (Finset.mem_insert_self a s) with h | h
      · exact ⟨k, by rw [h]; ring⟩
      · exact ⟨k - 1, by rw [h]; ring⟩
  obtain ⟨k, hk⟩ := hpar
  obtain ⟨m, hm⟩ := hodd
  exact ⟨k + (m : ℤ), by rw [hk, hm]; push_cast; ring⟩

private theorem main_disproof : ¬ (type_of% @OMA.S_arxiv_2101_11233.main) := by
  intro h
  obtain ⟨F', inst', ⟨iso⟩, hle⟩ := h 4 (by omega) c4 c4_pm1 c4_zero_sum P4 P4_isAcyclic (by rw [P4_maxDegree]; omega)
  rw [P4_maxDegree] at hle
  have hcard : F'.edgeFinset.card = 3 := by
    have h1 : F'.edgeFinset.card = Fintype.card F'.edgeSet := by
      rw [← Set.toFinset_card]
      congr 1
    have h2 : P4.edgeFinset.card = Fintype.card P4.edgeSet := by
      rw [← Set.toFinset_card]
      congr 1
    have hbij : P4.edgeSet ≃ F'.edgeSet := iso.mapEdgeSet
    rw [h1, ← Fintype.card_congr hbij, ← h2, P4_edgeFinset_card]
  have hf_pm1 : ∀ e ∈ F'.edgeFinset, c4 e = 1 ∨ c4 e = -1 := by
    intro e _
    unfold c4
    split_ifs <;> simp
  have hodd : Odd (∑ e ∈ F'.edgeFinset, c4 e) :=
    odd_sum_pm1 F'.edgeFinset c4 hf_pm1 (by rw [hcard]; exact ⟨1, by norm_num⟩)
  have hne0 : (∑ e ∈ F'.edgeFinset, c4 e) ≠ 0 := by
    intro hz
    rw [hz] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  have habs_ge1 : (1 : ℤ) ≤ |∑ e ∈ F'.edgeFinset, c4 e| := by
    have : 0 < |∑ e ∈ F'.edgeFinset, c4 e| := abs_pos.mpr hne0
    omega
  have habs_real : (1 : ℝ) ≤ (|∑ e ∈ F'.edgeFinset, c4 e| : ℝ) := by exact_mod_cast habs_ge1
  norm_num at hle
  linarith

end OMA.P_arxiv_2101_11233

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2101_11233.main) :=
  OMA.P_arxiv_2101_11233.main_disproof

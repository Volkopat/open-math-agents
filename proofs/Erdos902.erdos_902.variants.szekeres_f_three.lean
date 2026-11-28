import FormalConjectures.ErdosProblems.«902»

open Erdos902 Finset
open scoped Classical

private noncomputable def dom {V : Type*} [Fintype V] (G : Digraph V) (A : Finset V) : Finset V :=
  univ.filter fun v => ∀ a ∈ A, G.Adj v a

private def paley : Digraph (Fin 19) where
  Adj a b := (b - a).1 ∈ ([1, 4, 5, 6, 7, 9, 11, 16, 17] : List ℕ)

private instance : DecidableRel paley.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

private lemma many_lower (k m : ℕ) (hm : 0 < m) {V : Type} [Fintype V]
    (G : Digraph V) (hG : G.IsTournament) (h : ∀ A : Finset V, A.card ≤ k → m ≤ (dom G A).card) :
    2 ^ k * (m + 1) ≤ Fintype.card V + 1 := by
  induction k generalizing V with
  | zero => simpa using Nat.add_le_add_right (by simpa [dom] using h ∅ (by simp) : m ≤ Fintype.card V) 1
  | succ k ih =>
    have hdeg (v : V) : 2 ^ k * (m + 1) ≤ (dom G {v}).card + 1 := by
      let S := dom G {v}
      let e : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
      let H : Digraph S := ⟨fun x y => G.Adj x.1 y.1⟩
      have ht : H.IsTournament :=
        ⟨fun x => hG.1 x.1, fun x y hne => hG.2 x.1 y.1 (fun he => hne (Subtype.ext he))⟩
      have hm' : ∀ A : Finset S, A.card ≤ k → m ≤ (dom H A).card := fun A hA => by
        have hd : (dom H A).map e = dom G (insert v (A.map e)) := by
          ext x
          simp only [dom, mem_map, mem_filter, mem_univ, true_and, mem_insert, forall_eq_or_imp]
          exact ⟨by rintro ⟨⟨u, hu⟩, hdu, rfl⟩
                    exact ⟨show G.Adj u v by simpa [S, dom] using hu,
                      by rintro _ ⟨a, ha, rfl⟩; exact hdu a ha⟩,
            fun ⟨hxv, hxA⟩ => ⟨⟨x, by simpa [S, dom] using hxv⟩, fun a ha => hxA (e a) ⟨a, ha, rfl⟩, rfl⟩⟩
        rw [← card_map (f := e), hd]
        exact h (insert v (A.map e)) ((card_insert_le _ _).trans (by simpa using Nat.add_le_add_right hA 1))
      simpa [Fintype.card_coe, S] using ih H ht hm'
    let q := Fintype.card V
    have hpos : 0 < q := hm.trans_le (by simpa [dom] using h ∅ (by simp))
    let I (x y : V) : ℕ := if G.Adj x y then 1 else 0
    let tot := ∑ v : V, (dom G {v}).card
    have hins (v : V) : ∑ x : V, I x v = (dom G {v}).card := by simp [I, dom]
    have hpair (x y : V) : I x y + I y x + (if x = y then 1 else 0) = 1 := by
      by_cases he : x = y
      · subst y; simp [I, hG.1]
      · by_cases hxy : G.Adj x y
        · simp [I, he, hxy, (hG.2 x y he).1 hxy]
        · simp [I, he, hxy, (hG.2 y x (Ne.symm he)).2 hxy]
    have hsum : tot + tot + q = q * q := by
      have := congrArg (fun f : V → V → ℕ => ∑ y, ∑ x, f x y)
        (funext fun x => funext fun y => hpair x y)
      simp only [sum_add_distrib, hins, sum_ite_eq', mem_univ, if_true, sum_const, card_univ,
        nsmul_eq_mul, mul_one] at this
      rw [sum_comm (f := fun y x => I y x)] at this
      simpa [hins, tot, q] using this
    have hlo : q * (2 ^ k * (m + 1)) ≤ tot + q := by
      have hs := sum_le_sum fun v (_ : v ∈ univ) => hdeg v
      simp only [sum_const, card_univ, smul_eq_mul, sum_add_distrib, mul_one] at hs
      exact hs
    exact Nat.le_of_mul_le_mul_left
      (by rw [pow_succ]; nlinarith : q * (2 ^ (k + 1) * (m + 1)) ≤ q * (q + 1)) hpos

theorem OMA.solution : type_of% @Erdos902.erdos_902.variants.szekeres_f_three := by
  have hpt : paley.IsTournament := ⟨by decide +kernel, by decide +kernel⟩
  have hpp : HasPropertyS paley 3 := by
    have hchk : ∀ b c : Fin 19, ∃ x, paley.Adj x 0 ∧ paley.Adj x b ∧ paley.Adj x c := by
      decide +kernel
    have htr (u v a : Fin 19) : paley.Adj (u + a) v ↔ paley.Adj u (v - a) := by
      change (v - (u + a)).1 ∈ _ ↔ (v - a - u).1 ∈ _; rw [show v - (u + a) = v - a - u by abel]
    intro A hA
    obtain ⟨a, b, c, _, _, _, rfl⟩ := card_eq_three.1 hA
    obtain ⟨x, hx0, hxb, hxc⟩ := hchk (b - a) (c - a)
    have hd : ∀ e ∈ ({a, b, c} : Finset (Fin 19)), paley.Adj (x + a) e := fun e he => by
      simp only [mem_insert, mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact (htr ..).2 (by simpa using hx0)
      · exact (htr ..).2 hxb
      · exact (htr ..).2 hxc
    exact ⟨x + a, fun hx => hpt.1 _ (hd _ hx), hd⟩
  have hw : 19 ∈ {m : ℕ | 3 ≤ m ∧ ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G 3} :=
    ⟨by decide, paley, hpt, hpp⟩
  refine le_antisymm (Nat.sInf_le hw) (le_csInf ⟨19, hw⟩ ?_)
  rintro m ⟨hm, G, ht, hS⟩
  have hdom {A : Finset (Fin m)} (hA : A.card ≤ 3) : ∃ v ∉ A, ∀ a ∈ A, G.Adj v a := by
    obtain ⟨B, hAB, _, hB⟩ := exists_subsuperset_card_eq (subset_univ A) hA (by simpa using hm)
    obtain ⟨v, hv, hd⟩ := hS B hB
    exact ⟨v, fun hvA => hv (hAB hvA), fun a ha => hd a (hAB ha)⟩
  have hmany : ∀ A : Finset (Fin m), A.card ≤ 2 → 4 ≤ (dom G A).card := fun A hA => by
    by_contra! hsm
    obtain ⟨x, hx, hxd⟩ := hdom (show (dom G A).card ≤ 3 by omega)
    obtain ⟨y, _, hyd⟩ := hdom ((card_insert_le x A).trans (Nat.add_le_add_right hA 1))
    have hyA : y ∈ dom G A := by
      simp only [dom, mem_filter, mem_univ, true_and]
      exact fun z hz => hyd z (mem_insert_of_mem hz)
    exact ((ht.2 x y fun he => hx (he ▸ hyA)).1 (hxd _ hyA)) (hyd _ (mem_insert_self ..))
  have h := many_lower 2 4 (by decide) G ht hmany
  simp only [Fintype.card_fin] at h; omega

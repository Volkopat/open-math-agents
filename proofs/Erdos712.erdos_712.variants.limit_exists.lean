import FormalConjectures.ErdosProblems.«712»
open Filter Topology Finset
open scoped Classical in
lemma ex_le {n r b : ℕ} {P : Finset (Finset (Fin n)) → Prop}
    (h : ∀ H, H ⊆ (univ : Finset (Fin n)).powersetCard r → P H → H.card ≤ b) :
    Hypergraph.extremalNumber n r P ≤ b :=
  Finset.sup_le fun H hH => by rw [mem_filter, mem_powerset] at hH; exact h H hH.1 hH.2

open scoped Classical in
lemma le_ex {n r : ℕ} {P : Finset (Finset (Fin n)) → Prop} (H : Finset (Finset (Fin n)))
    (h1 : H ⊆ (univ : Finset (Fin n)).powersetCard r) (h2 : P H) :
    H.card ≤ Hypergraph.extremalNumber n r P :=
  le_sup (f := Finset.card) (by rw [mem_filter, mem_powerset]; exact ⟨h1, h2⟩)

theorem OMA.solution : type_of% @Erdos712.erdos_712.variants.limit_exists := by
  classical
  intro r k
  let ex (n : ℕ) := Hypergraph.cliqueExtremalNumber n r k
  have step (n : ℕ) (hn : r ≤ n) :
      (ex (n + 1) : ℝ) / ((n + 1).choose r : ℕ) ≤ (ex n : ℝ) / (n.choose r : ℕ) := by
    have hc : 0 < n + 1 - r := by omega
    have hkey : ex (n + 1) * (n + 1 - r) ≤ (n + 1) * ex n := by
      rw [← Nat.le_div_iff_mul_le hc]
      refine ex_le fun H h1 h2 => (Nat.le_div_iff_mul_le hc).mpr ?_
      have hsum : ∑ v : Fin (n + 1), (H.filter fun e => v ∉ e).card = H.card * (n + 1 - r) := by
        simp_rw [card_filter]
        rw [sum_comm, card_eq_sum_ones, sum_mul]
        refine sum_congr rfl fun e he => ?_
        rw [← card_filter, show (univ.filter fun v : Fin (n + 1) => v ∉ e) = eᶜ by ext; simp,
          card_compl, Fintype.card_fin, (mem_powersetCard.mp (h1 he)).2, one_mul]
      rw [← hsum]
      refine (sum_le_sum fun v _ => (?_ : (H.filter fun e => v ∉ e).card ≤ ex n)).trans_eq (by simp)
      let emb := v.succAboveEmb
      let G := ((univ : Finset (Fin n)).powersetCard r).filter (·.map emb ∈ H)
      have hsub : (H.filter fun e => v ∉ e) ⊆ G.image (·.map emb) := fun e he => by
        rw [mem_filter] at he
        obtain ⟨u, -, rfl⟩ := subset_map_iff.mp
          (show e ⊆ (univ : Finset (Fin n)).map emb from fun x hx => by
            obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq (fun h : x = v => he.2 (h ▸ hx))
            exact mem_map.mpr ⟨z, mem_univ _, hz⟩)
        have hcard := (mem_powersetCard.mp (h1 he.1)).2
        rw [card_map] at hcard
        exact mem_image.mpr ⟨u, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hcard⟩, he.1⟩, rfl⟩
      refine (card_le_card hsub).trans (card_image_le.trans (le_ex G (filter_subset _ _) ?_))
      rintro ⟨S, hS, hSG⟩
      refine h2 ⟨S.map emb, by rw [card_map, hS], fun T hT => ?_⟩
      rw [mem_powersetCard] at hT
      obtain ⟨U, hU, rfl⟩ := subset_map_iff.mp hT.1
      rw [card_map] at hT
      exact (mem_filter.mp (hSG (mem_powersetCard.mpr ⟨hU, hT.2⟩))).2
    have h1 : ex (n + 1) * n.choose r * (n + 1 - r) ≤ ex n * (n + 1).choose r * (n + 1 - r) := by
      nlinarith [Nat.mul_le_mul_right (n.choose r) hkey, Nat.choose_mul_succ_eq n r]
    rw [div_le_div_iff₀ (by exact_mod_cast Nat.choose_pos (by omega))
      (by exact_mod_cast Nat.choose_pos hn)]
    exact_mod_cast Nat.le_of_mul_le_mul_right h1 hc
  let b (m : ℕ) : ℝ := (ex (m + r) : ℝ) / ((m + r).choose r : ℕ)
  have hb0 : ∀ m, 0 ≤ b m := fun _ => by positivity
  have hbdd : BddBelow (Set.range b) := ⟨0, by rintro _ ⟨m, rfl⟩; exact hb0 m⟩
  have hb_anti : Antitone b := antitone_nat_of_succ_le fun m => by
    simpa only [b, Nat.succ_add] using step (m + r) (by omega)
  have hb1 : b 0 ≤ 1 := by
    have hex : ex r ≤ 1 := ex_le fun H h1 _ => (card_le_card h1).trans_eq (by simp)
    simpa [b] using (show (ex r : ℝ) ≤ 1 by exact_mod_cast hex)
  refine ⟨⨅ m, b m, ⟨le_ciInf hb0, (ciInf_le hbdd 0).trans hb1⟩, ?_⟩
  rw [← tendsto_add_atTop_iff_nat r]
  exact tendsto_atTop_ciInf hb_anti hbdd

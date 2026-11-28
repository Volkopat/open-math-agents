import OMAReductions.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R1

namespace OMA.Proof_Sidorenko_tas_trees_R1_H1

open SimpleGraph

private lemma star_adj_center {V : Type*} {T : SimpleGraph V} (hT : T.IsTree) {c : V}
    (hc : ∀ u v : V, T.Adj u v → u = c ∨ v = c) {v : V} (hv : v ≠ c) :
    T.Adj c v := by
  have hwalk : ∀ {x y : V} (p : T.Walk x y), x ≠ y → y ≠ c → T.Adj c y := by
    intro x y p
    induction p with
    | nil => intro hne; exact absurd rfl hne
    | @cons a b d hab p' ih =>
      intro _ hdc
      by_cases hbd : b = d
      · subst hbd
        rcases hc a b hab with rfl | rfl
        · exact hab
        · exact absurd rfl hdc
      · exact ih hbd hdc
  obtain ⟨p⟩ := hT.connected c v
  exact hwalk p hv.symm hv

private lemma star_adj_iff {V : Type*} {T : SimpleGraph V} (hT : T.IsTree) {c : V}
    (hc : ∀ u v : V, T.Adj u v → u = c ∨ v = c) (u v : V) :
    T.Adj u v ↔ (u = c ∧ v ≠ c) ∨ (v = c ∧ u ≠ c) := by
  constructor
  · intro huv
    have hne : u ≠ v := T.ne_of_adj huv
    rcases hc u v huv with rfl | rfl
    · exact Or.inl ⟨rfl, hne.symm⟩
    · exact Or.inr ⟨rfl, hne⟩
  · rintro (⟨rfl, hv⟩ | ⟨rfl, hu⟩)
    · exact star_adj_center hT hc hv
    · exact (star_adj_center hT hc hu).symm

private lemma star_edgeFinset_card {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) {c : V}
    (hc : ∀ u v : V, T.Adj u v → u = c ∨ v = c) :
    T.edgeFinset.card = (Finset.univ.erase c).card := by
  symm
  refine Finset.card_bij (fun v _ => s(c, v)) ?_ ?_ ?_
  · intro v hv
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact star_adj_center hT hc (Finset.mem_erase.mp hv).1
  · intro v1 hv1 v2 hv2 heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨_, h12⟩ | ⟨hcv2, _⟩
    · exact h12
    · exact absurd hcv2.symm (Finset.mem_erase.mp hv2).1
  · intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet, star_adj_iff hT hc] at he
      rcases he with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
      · exact ⟨v, Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩, rfl⟩
      · exact ⟨u, Finset.mem_erase.mpr ⟨hu, Finset.mem_univ _⟩, Sym2.eq_swap⟩

private lemma tournament_out_add_in {W : Type*} [Fintype W] [DecidableEq W]
    (G : Digraph W) [DecidableRel G.Adj] (hG : G.IsTournament) (x : W) :
    (Finset.univ.filter (fun y => G.Adj x y)).card +
      (Finset.univ.filter (fun y => G.Adj y x)).card = Fintype.card W - 1 := by
  have hdisj : Disjoint (Finset.univ.filter (fun y => G.Adj x y))
      (Finset.univ.filter (fun y => G.Adj y x)) := by
    rw [Finset.disjoint_filter]
    intro y _ hxy hyx
    by_cases h : x = y
    · subst h; exact hG.1 x hxy
    · exact (hG.2 x y h).mp hxy hyx
  have hunion : Finset.univ.filter (fun y => G.Adj x y) ∪
      Finset.univ.filter (fun y => G.Adj y x) = Finset.univ.erase x := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      and_true]
    constructor
    · rintro (hxy | hyx)
      · rintro rfl; exact hG.1 y hxy
      · rintro rfl; exact hG.1 y hyx
    · intro hyx
      by_cases h : G.Adj x y
      · exact Or.inl h
      · exact Or.inr ((hG.2 y x hyx).mpr (by simpa using h))
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]

private lemma tournament_sum_out_le {W : Type*} [Fintype W] [DecidableEq W]
    (G : Digraph W) [DecidableRel G.Adj] (hG : G.IsTournament) :
    2 * ∑ x : W, (Finset.univ.filter (fun y => G.Adj x y)).card ≤ (Fintype.card W) ^ 2 := by
  have hswap : ∑ x : W, (Finset.univ.filter (fun y => G.Adj x y)).card =
      ∑ x : W, (Finset.univ.filter (fun y => G.Adj y x)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h2 : 2 * ∑ x : W, (Finset.univ.filter (fun y => G.Adj x y)).card =
      ∑ x : W, ((Finset.univ.filter (fun y => G.Adj x y)).card +
        (Finset.univ.filter (fun y => G.Adj y x)).card) := by
    rw [Finset.sum_add_distrib, ← hswap, two_mul]
  rw [h2]
  calc ∑ x : W, ((Finset.univ.filter (fun y => G.Adj x y)).card +
          (Finset.univ.filter (fun y => G.Adj y x)).card)
      = ∑ _x : W, (Fintype.card W - 1) :=
        Finset.sum_congr rfl fun x _ => tournament_out_add_in G hG x
    _ = Fintype.card W * (Fintype.card W - 1) := by simp
    _ ≤ Fintype.card W * Fintype.card W := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = (Fintype.card W) ^ 2 := (sq _).symm

end OMA.Proof_Sidorenko_tas_trees_R1_H1

theorem OMA.solution :
    OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R1.H1 := by
  intro V _ _ T _ hT hstar
  open SimpleGraph OMA.Proof_Sidorenko_tas_trees_R1_H1 in
  classical
  obtain ⟨c, hc⟩ := hstar
  let L : Finset V := Finset.univ.erase c
  have hA_le : (L.card + 1) / 2 ≤ L.card := by omega
  obtain ⟨A, hAL, hA_card⟩ := Finset.exists_subset_card_eq hA_le
  let B : Finset V := L \ A
  have hB_card : B.card = L.card / 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAL, hA_card]; omega
  have hAB_disj : Disjoint A B := Finset.disjoint_sdiff
  have hAB_union : A ∪ B = L := Finset.union_sdiff_of_subset hAL
  let D : Digraph V := ⟨fun u v => (u = c ∧ v ∈ A) ∨ (v = c ∧ u ∈ B)⟩
  have hcA : c ∉ A := fun h => (Finset.mem_erase.mp (hAL h)).1 rfl
  have hcB : c ∉ B := fun h => (Finset.mem_erase.mp (Finset.sdiff_subset h)).1 rfl
  have hD_ori : D.IsOrientation T := by
    refine ⟨?_, ?_⟩
    · rintro u v (⟨rfl, hv⟩ | ⟨rfl, hu⟩)
      · exact star_adj_center hT hc (Finset.mem_erase.mp (hAL hv)).1
      · exact (star_adj_center hT hc (Finset.mem_erase.mp (Finset.sdiff_subset hu)).1).symm
    · intro u v huv
      rw [star_adj_iff hT hc] at huv
      rcases huv with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
      · have hvL : v ∈ L := Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩
        simp only [D, true_and, hv, false_and, hcB, and_false, or_false, false_or, hcA]
        constructor
        · intro hvA hvB; exact Finset.disjoint_left.mp hAB_disj hvA hvB
        · intro hvB
          rw [← hAB_union, Finset.mem_union] at hvL
          exact hvL.resolve_right hvB
      · have huL : u ∈ L := Finset.mem_erase.mpr ⟨hu, Finset.mem_univ _⟩
        simp only [D, true_and, hu, false_and, hcB, and_false, or_false, false_or, hcA]
        constructor
        · intro huB huA; exact Finset.disjoint_left.mp hAB_disj huA huB
        · intro huA
          rw [← hAB_union, Finset.mem_union] at huL
          exact huL.resolve_left huA
  refine ⟨D, hD_ori, ?_⟩
  intro W _ _ _ G _ hG
  have hcardV : Fintype.card V = L.card + 1 := by
    have : L.card = Fintype.card V - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨c⟩
    omega
  have hedge : T.edgeFinset.card = L.card := star_edgeFinset_card T hT hc
  let outS (x : W) : Finset W := Finset.univ.filter (fun y => G.Adj x y)
  let inS (x : W) : Finset W := Finset.univ.filter (fun y => G.Adj y x)
  have hhom_count : Digraph.homCount D G =
      ∑ x : W, (outS x).card ^ A.card * (inS x).card ^ B.card := by
    unfold Digraph.homCount
    let S := Σ x : W, ({v : V // v ∈ A} → {y : W // y ∈ outS x}) ×
      ({v : V // v ∈ B} → {y : W // y ∈ inS x})
    have hcardS : Fintype.card S = ∑ x : W, (outS x).card ^ A.card * (inS x).card ^ B.card := by
      simp only [S, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fun, Fintype.card_coe]
    rw [← hcardS]
    refine Fintype.card_congr
      { toFun := fun f =>
          ⟨f.toFun c,
            (fun v => ⟨f.toFun v.1, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, f.map_adj' (Or.inl ⟨rfl, v.2⟩)⟩⟩,
             fun v => ⟨f.toFun v.1, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, f.map_adj' (Or.inr ⟨rfl, v.2⟩)⟩⟩)⟩
        invFun := fun s =>
          ⟨fun v =>
            if hvA : v ∈ A then (s.2.1 ⟨v, hvA⟩).1
            else if hvB : v ∈ B then (s.2.2 ⟨v, hvB⟩).1
            else s.1,
           by
             intro u v huv
             have hcA : c ∉ A := fun h => (Finset.mem_erase.mp (hAL h)).1 rfl
             have hcB : c ∉ B := fun h => (Finset.mem_erase.mp (Finset.sdiff_subset h)).1 rfl
             rcases huv with ⟨rfl, hvA⟩ | ⟨rfl, huB⟩
             · simp only [hcA, hcB, hvA, ↓reduceDIte]
               exact (Finset.mem_filter.mp (s.2.1 ⟨v, hvA⟩).2).2
             · have huA : u ∉ A := fun h => Finset.disjoint_left.mp hAB_disj h huB
               simp only [hcA, hcB, huA, huB, ↓reduceDIte]
               exact (Finset.mem_filter.mp (s.2.2 ⟨u, huB⟩).2).2⟩
        left_inv := fun f =>
          OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_R1.hom_ext <| by
            funext v
            by_cases hvc : v = c
            · subst hvc
              simp [hcA, hcB]
            · have hvL : v ∈ L := Finset.mem_erase.mpr ⟨hvc, Finset.mem_univ _⟩
              by_cases hvA : v ∈ A
              · simp [hvA]
              · have hvB : v ∈ B := by
                  rw [← hAB_union, Finset.mem_union] at hvL
                  exact hvL.resolve_left hvA
                simp [hvA, hvB]
        right_inv := fun s => by
          rcases s with ⟨x, fA, fB⟩
          have hmk : ∀ (y : W) (_ : y = x)
              (gA : {v : V // v ∈ A} → {z : W // z ∈ outS y})
              (gB : {v : V // v ∈ B} → {z : W // z ∈ inS y}),
              (∀ v, (gA v).1 = (fA v).1) → (∀ v, (gB v).1 = (fB v).1) →
              (⟨y, (gA, gB)⟩ : S) = ⟨x, (fA, fB)⟩ := by
            rintro _ rfl gA gB hA hB
            congr 1
            ext1
            · funext v; exact Subtype.ext (hA v)
            · funext v; exact Subtype.ext (hB v)
          refine hmk _ (by dsimp only; rw [dif_neg hcA, dif_neg hcB]) _ _ ?_ ?_
          · intro v; dsimp only; rw [dif_pos v.2]
          · intro v; dsimp only
            have hvA : v.1 ∉ A := fun h => Finset.disjoint_left.mp hAB_disj h v.2
            rw [dif_neg hvA, dif_pos v.2] }
  unfold Digraph.homDensity
  rw [hedge, hcardV]
  refine le_trans
    (b := ((∑ x : W, (outS x).card ^ A.card * (inS x).card ^ B.card : ℕ) : ℝ) /
      (Fintype.card W : ℝ) ^ (L.card + 1))
    (le_of_eq ?_) ?_
  · congr 2
  set N : ℝ := (Fintype.card W : ℝ)
  have hNpos : 0 < N := Nat.cast_pos.mpr (Fintype.card_pos (α := W))
  rw [div_le_iff₀ (pow_pos hNpos _)]
  have hprod_bound : ∀ x : W, ((outS x).card : ℝ) * ((inS x).card : ℝ) ≤ (N / 2) ^ 2 := by
    intro x
    have hsum : ((outS x).card : ℝ) + ((inS x).card : ℝ) ≤ N := by
      have hnat : (outS x).card + (inS x).card = Fintype.card W - 1 :=
        tournament_out_add_in G hG x
      have hle : (outS x).card + (inS x).card ≤ Fintype.card W := by omega
      change ((outS x).card : ℝ) + ((inS x).card : ℝ) ≤ (Fintype.card W : ℝ)
      exact_mod_cast hle
    nlinarith [sq_nonneg (((outS x).card : ℝ) - ((inS x).card : ℝ))]
  set m := L.card / 2
  have hcast : ((∑ x : W, (outS x).card ^ A.card * (inS x).card ^ B.card : ℕ) : ℝ) =
      ∑ x : W, ((outS x).card : ℝ) ^ A.card * ((inS x).card : ℝ) ^ B.card := by
    push_cast; rfl
  rw [hcast]
  rcases Nat.even_or_odd L.card with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hm : m = r := by omega
    have hA_eq : A.card = r := by omega
    have hB_eq : B.card = r := by omega
    rw [hA_eq, hB_eq]
    calc ∑ x : W, ((outS x).card : ℝ) ^ r * ((inS x).card : ℝ) ^ r
        = ∑ x : W, (((outS x).card : ℝ) * ((inS x).card : ℝ)) ^ r := by
          refine Finset.sum_congr rfl fun x _ => (mul_pow _ _ _).symm
      _ ≤ ∑ _x : W, ((N / 2) ^ 2) ^ r := by
          refine Finset.sum_le_sum fun x _ =>
            pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hprod_bound x) r
      _ = N * ((N / 2) ^ 2) ^ r := by simp [N]
      _ = (1 / 2 : ℝ) ^ L.card * N ^ (L.card + 1) := by
          rw [hr, show r + r = 2 * r by omega, ← pow_mul, pow_succ']
          simp only [div_pow, one_pow]
          ring
  · have hm : m = r := by omega
    have hA_eq : A.card = r + 1 := by omega
    have hB_eq : B.card = r := by omega
    rw [hA_eq, hB_eq]
    have hsum_out : ∑ x : W, ((outS x).card : ℝ) ≤ N ^ 2 / 2 := by
      have hnat : 2 * ∑ x : W, (outS x).card ≤ (Fintype.card W) ^ 2 :=
        tournament_sum_out_le G hG
      have hr' : 2 * ∑ x : W, ((outS x).card : ℝ) ≤ (Fintype.card W : ℝ) ^ 2 := by
        exact_mod_cast hnat
      linarith
    calc ∑ x : W, ((outS x).card : ℝ) ^ (r + 1) * ((inS x).card : ℝ) ^ r
        = ∑ x : W, ((outS x).card : ℝ) * (((outS x).card : ℝ) * ((inS x).card : ℝ)) ^ r := by
          refine Finset.sum_congr rfl fun x _ => by rw [pow_succ', mul_assoc, ← mul_pow]
      _ ≤ ∑ x : W, ((outS x).card : ℝ) * ((N / 2) ^ 2) ^ r := by
          refine Finset.sum_le_sum fun x _ =>
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hprod_bound x) r)
              (Nat.cast_nonneg _)
      _ = (∑ x : W, ((outS x).card : ℝ)) * ((N / 2) ^ 2) ^ r := (Finset.sum_mul _ _ _).symm
      _ ≤ (N ^ 2 / 2) * ((N / 2) ^ 2) ^ r :=
          mul_le_mul_of_nonneg_right hsum_out (pow_nonneg (sq_nonneg _) _)
      _ = (1 / 2 : ℝ) ^ L.card * N ^ (L.card + 1) := by
          rw [hr, ← pow_mul, pow_succ, pow_succ]
          simp only [div_pow, one_pow]
          ring

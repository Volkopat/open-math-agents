import OMAStatements.S_arxiv_2610_19119

namespace OMA.P_arxiv_2610_19119

open OMA.S_arxiv_2610_19119

/-! ### Part 1: Finiteness of Flow Sets -/

private lemma graphFlow_entry_le {m : ℕ} (G : List (DirEdge m)) (F : GraphFlow G) :
    (∀ idx : Fin G.length, F.val.1 idx ≤ G.length) ∧
    (∀ i : Fin m, F.val.2 i ≤ G.length) := by
  have hprefix : ∀ v : ℕ,
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ v), F.val.2 i) +
      (∑ idx ∈ Finset.univ.filter (fun idx : Fin G.length =>
        (G.get idx).val.1.val ≤ v ∧ v < (G.get idx).val.2.val), F.val.1 idx) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ v), multigraphIndeg G i := by
    intro v
    have hsum := Finset.sum_congr rfl fun (i : Fin m) (_ : i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ v)) =>
      F.prop i
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    have hout : (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ v),
          ∑ idx ∈ Finset.univ.filter (fun idx : Fin G.length => (G.get idx).val.1 = i), F.val.1 idx) =
        ∑ idx ∈ Finset.univ.filter (fun idx : Fin G.length => (G.get idx).val.1.val ≤ v), F.val.1 idx := by
      rw [← Finset.sum_biUnion]
      · refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext idx
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨i, hi, heq⟩ => heq ▸ hi, fun h => ⟨(G.get idx).val.1, h, rfl⟩⟩
      · intro i _ j _ hij
        exact Finset.disjoint_left.mpr fun idx h1 h2 =>
          hij (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
    have hin : (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ v),
          ∑ idx ∈ Finset.univ.filter (fun idx : Fin G.length => (G.get idx).val.2 = i), F.val.1 idx) =
        ∑ idx ∈ Finset.univ.filter (fun idx : Fin G.length => (G.get idx).val.2.val ≤ v), F.val.1 idx := by
      rw [← Finset.sum_biUnion]
      · refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext idx
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨i, hi, heq⟩ => heq ▸ hi, fun h => ⟨(G.get idx).val.2, h, rfl⟩⟩
      · intro i _ j _ hij
        exact Finset.disjoint_left.mpr fun idx h1 h2 =>
          hij (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
    have hsplit : (Finset.univ.filter fun idx : Fin G.length => (G.get idx).val.1.val ≤ v) =
        (Finset.univ.filter fun idx : Fin G.length => (G.get idx).val.2.val ≤ v) ∪
        (Finset.univ.filter fun idx : Fin G.length => (G.get idx).val.1.val ≤ v ∧ v < (G.get idx).val.2.val) := by
      ext idx
      have hlt : (G.get idx).val.1.val < (G.get idx).val.2.val := (G.get idx).prop
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hdisj : Disjoint
        (Finset.univ.filter fun idx : Fin G.length => (G.get idx).val.2.val ≤ v)
        (Finset.univ.filter fun idx : Fin G.length => (G.get idx).val.1.val ≤ v ∧ v < (G.get idx).val.2.val) := by
      rw [Finset.disjoint_left]
      intro idx h1 h2
      have := (Finset.mem_filter.mp h1).2
      have := (Finset.mem_filter.mp h2).2.2
      omega
    rw [hout, hin, hsplit, Finset.sum_union hdisj] at hsum
    omega
  have hindeg_le : ∀ v : ℕ,
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ v), multigraphIndeg G i ≤ G.length := by
    intro v
    have htot : ∑ i : Fin m, multigraphIndeg G i = G.length := by
      unfold multigraphIndeg
      rw [← Finset.card_biUnion]
      · have : (Finset.univ.biUnion fun i : Fin m =>
            Finset.univ.filter fun idx : Fin G.length => (G.get idx).val.2 = i) = Finset.univ := by
          ext idx; simp
        rw [this, Finset.card_fin]
      · intro i _ j _ hij
        exact Finset.disjoint_left.mpr fun idx h1 h2 =>
          hij (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
    calc ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ v), multigraphIndeg G i
        ≤ ∑ i : Fin m, multigraphIndeg G i :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      _ = G.length := htot
  constructor
  · intro idx
    have h1 := hprefix (G.get idx).val.1.val
    have hmem : idx ∈ Finset.univ.filter (fun idx' : Fin G.length =>
        (G.get idx').val.1.val ≤ (G.get idx).val.1.val ∧ (G.get idx).val.1.val < (G.get idx').val.2.val) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _, (G.get idx).prop⟩
    have hle := Finset.single_le_sum (f := F.val.1) (fun _ _ => Nat.zero_le _) hmem
    have h2 := hindeg_le (G.get idx).val.1.val
    omega
  · intro i
    have h1 := hprefix i.val
    have hmem : i ∈ Finset.univ.filter (fun j : Fin m => j.val ≤ i.val) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _⟩
    have hle := Finset.single_le_sum (f := F.val.2) (fun _ _ => Nat.zero_le _) hmem
    have h2 := hindeg_le i.val
    omega

private lemma graphFlow_finite {m : ℕ} (G : List (DirEdge m)) : Finite (GraphFlow G) := by
  let enc : GraphFlow G → (Fin G.length → Fin (G.length + 1)) × (Fin m → Fin (G.length + 1)) :=
    fun F => (fun idx => ⟨F.val.1 idx, Nat.lt_succ_of_le ((graphFlow_entry_le G F).1 idx)⟩,
              fun i => ⟨F.val.2 i, Nat.lt_succ_of_le ((graphFlow_entry_le G F).2 i)⟩)
  refine Finite.of_injective enc fun F₁ F₂ h => Subtype.ext (Prod.ext ?_ ?_)
  · funext idx; exact congrArg Fin.val (congrFun (congrArg Prod.fst h) idx)
  · funext i; exact congrArg Fin.val (congrFun (congrArg Prod.snd h) i)

private lemma twoExitFlow_entry_le {m k : ℕ} (F : TwoExitFlow m k) :
    (∀ e : DirEdge m, F.val.1 e ≤ m * m) ∧
    (∀ i : Fin m, F.val.2.1 i ≤ m * m) ∧
    (∀ i : Fin m, F.val.2.2 i ≤ m * m) := by
  have hprefix : ∀ v : ℕ,
      (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ v), (F.val.2.1 i + F.val.2.2 i)) +
      (∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.1.val ≤ v ∧ v < e.val.2.val), F.val.1 e) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ v), i.val := by
    intro v
    have hsum := Finset.sum_congr rfl fun (i : Fin m) (_ : i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ v)) =>
      F.prop.1 i
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    have hout : (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ v),
          ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.1 = i), F.val.1 e) =
        ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.1.val ≤ v), F.val.1 e := by
      rw [← Finset.sum_biUnion]
      · refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext e; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨i, hi, heq⟩ => heq ▸ hi, fun h => ⟨e.val.1, h, rfl⟩⟩
      · intro i _ j _ hij
        exact Finset.disjoint_left.mpr fun e h1 h2 =>
          hij (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
    have hin : (∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ v),
          ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.2 = i), F.val.1 e) =
        ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.2.val ≤ v), F.val.1 e := by
      rw [← Finset.sum_biUnion]
      · refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext e; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨i, hi, heq⟩ => heq ▸ hi, fun h => ⟨e.val.2, h, rfl⟩⟩
      · intro i _ j _ hij
        exact Finset.disjoint_left.mpr fun e h1 h2 =>
          hij (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
    have hsplit : (Finset.univ.filter fun e : DirEdge m => e.val.1.val ≤ v) =
        (Finset.univ.filter fun e : DirEdge m => e.val.2.val ≤ v) ∪
        (Finset.univ.filter fun e : DirEdge m => e.val.1.val ≤ v ∧ v < e.val.2.val) := by
      ext e; have hlt : e.val.1.val < e.val.2.val := e.prop
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hdisj : Disjoint
        (Finset.univ.filter fun e : DirEdge m => e.val.2.val ≤ v)
        (Finset.univ.filter fun e : DirEdge m => e.val.1.val ≤ v ∧ v < e.val.2.val) := by
      rw [Finset.disjoint_left]; intro e h1 h2
      have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2.2; omega
    rw [hout, hin, hsplit, Finset.sum_union hdisj] at hsum
    rw [Finset.sum_add_distrib]
    omega
  have hsum_le : ∀ v : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ v), i.val ≤ m * m := by
    intro v
    calc ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val ≤ v), i.val
        ≤ ∑ i : Fin m, i.val := Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      _ ≤ ∑ _i : Fin m, m := Finset.sum_le_sum fun i _ => le_of_lt i.isLt
      _ = m * m := by simp
  refine ⟨fun e => ?_, fun i => ?_, fun i => ?_⟩
  · have h1 := hprefix e.val.1.val
    have hmem : e ∈ Finset.univ.filter (fun e' : DirEdge m => e'.val.1.val ≤ e.val.1.val ∧ e.val.1.val < e'.val.2.val) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _, e.prop⟩
    have hle := Finset.single_le_sum (f := F.val.1) (fun _ _ => Nat.zero_le _) hmem
    have h2 := hsum_le e.val.1.val
    omega
  · have h1 := hprefix i.val
    have hmem : i ∈ Finset.univ.filter (fun j : Fin m => j.val ≤ i.val) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _⟩
    have hle := Finset.single_le_sum (f := fun j => F.val.2.1 j + F.val.2.2 j) (fun _ _ => Nat.zero_le _) hmem
    have h2 := hsum_le i.val
    omega
  · have h1 := hprefix i.val
    have hmem : i ∈ Finset.univ.filter (fun j : Fin m => j.val ≤ i.val) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _⟩
    have hle := Finset.single_le_sum (f := fun j => F.val.2.1 j + F.val.2.2 j) (fun _ _ => Nat.zero_le _) hmem
    have h2 := hsum_le i.val
    omega

private lemma twoExitFlow_finite (m k : ℕ) : Finite (TwoExitFlow m k) := by
  let enc : TwoExitFlow m k →
      (DirEdge m → Fin (m * m + 1)) × (Fin m → Fin (m * m + 1)) × (Fin m → Fin (m * m + 1)) :=
    fun F => (fun e => ⟨F.val.1 e, Nat.lt_succ_of_le ((twoExitFlow_entry_le F).1 e)⟩,
              fun i => ⟨F.val.2.1 i, Nat.lt_succ_of_le ((twoExitFlow_entry_le F).2.1 i)⟩,
              fun i => ⟨F.val.2.2 i, Nat.lt_succ_of_le ((twoExitFlow_entry_le F).2.2 i)⟩)
  refine Finite.of_injective enc fun F₁ F₂ h => Subtype.ext (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext e; exact congrArg Fin.val (congrFun (congrArg Prod.fst h) e)
  · funext i; exact congrArg Fin.val (congrFun (congrArg (fun x => x.2.1) h) i)
  · funext i; exact congrArg Fin.val (congrFun (congrArg (fun x => x.2.2) h) i)

/-! ### Part 2: Reduction Tree Existence and Lemma 2.1 (`lem:reduction`) -/

private def edgeLenSum {m : ℕ} (G : List (DirEdge m)) : ℕ :=
  ∑ idx : Fin G.length, ((G.get idx).val.2.val - (G.get idx).val.1.val)

private lemma edgeLenSum_le {m : ℕ} (G : List (DirEdge m)) :
    edgeLenSum G ≤ m * G.length := by
  unfold edgeLenSum
  calc ∑ idx : Fin G.length, ((G.get idx).val.2.val - (G.get idx).val.1.val)
      ≤ ∑ _idx : Fin G.length, m := Finset.sum_le_sum fun idx _ => by
        have := (G.get idx).val.2.isLt; omega
    _ = m * G.length := by simp [mul_comm]

private lemma edgeLenSum_set_gt {m : ℕ} (G : List (DirEdge m)) (idx : Fin G.length) (e' : DirEdge m)
    (hlt : (G.get idx).val.2.val - (G.get idx).val.1.val < e'.val.2.val - e'.val.1.val) :
    edgeLenSum G < edgeLenSum (G.set idx.val e') := by
  let G' := G.set idx.val e'
  have hlen : G'.length = G.length := List.length_set
  let eqIdx : Fin G.length ≃ Fin G'.length := finCongr hlen.symm
  unfold edgeLenSum
  rw [← eqIdx.sum_comp]
  refine Finset.sum_lt_sum (fun r _ => ?_) ⟨idx, Finset.mem_univ _, ?_⟩
  · by_cases hr : r = idx
    · subst hr
      have hget : G'.get (eqIdx r) = e' := by simp [G', eqIdx]
      rw [hget]; exact le_of_lt hlt
    · have hrval : r.val ≠ idx.val := fun h => hr (Fin.ext h)
      have hget : G'.get (eqIdx r) = G.get r := by simp [G', eqIdx, List.getElem_set_ne (Ne.symm hrval)]
      rw [hget]
  · have hget : G'.get (eqIdx idx) = e' := by simp [G', eqIdx]
    rw [hget]; exact hlt

private lemma redTree_exists {m : ℕ} (G : List (DirEdge m)) : Nonempty (RedTree m G) := by
  classical
  have hmain : ∀ d : ℕ, ∀ G : List (DirEdge m), m * G.length - edgeLenSum G = d → Nonempty (RedTree m G) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro G hd
      by_cases hred : ∃ p q : Fin G.length, (G.get p).val.2 = (G.get q).val.1
      · obtain ⟨p, q, hchain⟩ := hred
        have hne : p ≠ q := fun h => by
          rw [h] at hchain; exact ne_of_lt (G.get q).prop hchain.symm
        let eik : DirEdge m := ⟨((G.get p).val.1, (G.get q).val.2),
          lt_trans (G.get p).prop (hchain ▸ (G.get q).prop)⟩
        let G_L := G.set q.val eik
        let G_R := G.set p.val eik
        have hp_lt : (G.get p).val.1.val < (G.get p).val.2.val := (G.get p).prop
        have hq_lt : (G.get q).val.1.val < (G.get q).val.2.val := (G.get q).prop
        have hch_val : (G.get p).val.2.val = (G.get q).val.1.val := congrArg Fin.val hchain
        have hL_inc : edgeLenSum G < edgeLenSum G_L :=
          edgeLenSum_set_gt G q eik (by show (G.get q).val.2.val - (G.get q).val.1.val < (G.get q).val.2.val - (G.get p).val.1.val; omega)
        have hR_inc : edgeLenSum G < edgeLenSum G_R :=
          edgeLenSum_set_gt G p eik (by show (G.get p).val.2.val - (G.get p).val.1.val < (G.get q).val.2.val - (G.get p).val.1.val; omega)
        have hlenL : G_L.length = G.length := List.length_set
        have hlenR : G_R.length = G.length := List.length_set
        have hleG := edgeLenSum_le G
        have hleL := edgeLenSum_le G_L
        have hleR := edgeLenSum_le G_R
        obtain ⟨TL⟩ := ih (m * G_L.length - edgeLenSum G_L) (by rw [hlenL] at hleL ⊢; omega) G_L rfl
        obtain ⟨TR⟩ := ih (m * G_R.length - edgeLenSum G_R) (by rw [hlenR] at hleR ⊢; omega) G_R rfl
        exact ⟨RedTree.step G p q hne hchain TL TR⟩
      · refine ⟨RedTree.leaf G fun e₁ he₁ e₂ he₂ heq => ?_⟩
        obtain ⟨p, rfl⟩ := List.mem_iff_get.mp he₁
        obtain ⟨q, rfl⟩ := List.mem_iff_get.mp he₂
        exact hred ⟨p, q, heq⟩
  exact hmain (m * G.length - edgeLenSum G) G rfl

/-- Forward map of Lemma 2.1 reduction bijection `F(G) → F(G_L) ⊕ F(G_R)`. -/
private def reductionStepTo {m : ℕ} (G : List (DirEdge m)) (p q : Fin G.length)
    (hne : p ≠ q) (hchain : (G.get p).val.2 = (G.get q).val.1)
    (F : GraphFlow G) :
    GraphFlow (G.set q.val ⟨((G.get p).val.1, (G.get q).val.2),
      lt_trans (G.get p).prop (hchain ▸ (G.get q).prop)⟩) ⊕
    GraphFlow (G.set p.val ⟨((G.get p).val.1, (G.get q).val.2),
      lt_trans (G.get p).prop (hchain ▸ (G.get q).prop)⟩) := by
  let i : Fin m := (G.get p).val.1
  let j : Fin m := (G.get p).val.2
  let k : Fin m := (G.get q).val.2
  have hj_eq : (G.get q).val.1 = j := hchain.symm
  have hij : i < j := (G.get p).prop
  have hjk : j < k := by change (G.get p).val.2 < (G.get q).val.2; rw [hchain]; exact (G.get q).prop
  have hik : i < k := lt_trans hij hjk
  let eik : DirEdge m := ⟨(i, k), hik⟩
  let G_L := G.set q.val eik
  let G_R := G.set p.val eik
  let eqL : Fin G.length ≃ Fin G_L.length := finCongr List.length_set.symm
  let eqR : Fin G.length ≃ Fin G_R.length := finCongr List.length_set.symm
  have hGL_get : ∀ idx : Fin G.length, G_L.get (eqL idx) = if idx = q then eik else G.get idx := fun idx => by
    by_cases h : idx = q
    · subst h; simp [G_L, eqL]
    · have hv : idx.val ≠ q.val := fun e => h (Fin.ext e)
      simp [G_L, eqL, h, List.getElem_set_ne (Ne.symm hv)]
  have hGR_get : ∀ idx : Fin G.length, G_R.get (eqR idx) = if idx = p then eik else G.get idx := fun idx => by
    by_cases h : idx = p
    · subst h; simp [G_R, eqR]
    · have hv : idx.val ≠ p.val := fun e => h (Fin.ext e)
      simp [G_R, eqR, h, List.getElem_set_ne (Ne.symm hv)]
  let rest : Finset (Fin G.length) := (Finset.univ.erase p).erase q
  have hp_nrest : p ∉ rest := by simp [rest]
  have hq_nrest : q ∉ rest := by simp [rest]
  have hrest_split : ∀ (g : Fin G.length → ℕ),
      ∑ idx : Fin G.length, g idx = g p + g q + ∑ idx ∈ rest, g idx := fun g => by
    have h1 : ∑ idx : Fin G.length, g idx = g p + ∑ idx ∈ Finset.univ.erase p, g idx := by
      rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ p)]
    have hq_mem : q ∈ Finset.univ.erase p := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ q⟩
    have h2 : ∑ idx ∈ Finset.univ.erase p, g idx = g q + ∑ idx ∈ rest, g idx := by
      rw [add_comm, Finset.sum_erase_add _ _ hq_mem]
    omega
  have hsum_flt : ∀ (P : Fin G.length → Prop) [DecidablePred P] (f : Fin G.length → ℕ),
      ∑ idx ∈ Finset.univ.filter P, f idx =
        (if P p then f p else 0) + (if P q then f q else 0) +
        ∑ idx ∈ rest, (if P idx then f idx else 0) := fun P _ f => by
    rw [Finset.sum_filter, hrest_split]
  have hsum_L_out : ∀ (f : Fin G_L.length → ℕ) (v : Fin m),
      (∑ idx ∈ Finset.univ.filter (fun idx : Fin G_L.length => (G_L.get idx).val.1 = v), f idx) =
      (if i = v then f (eqL p) else 0) + (if i = v then f (eqL q) else 0) +
      ∑ idx ∈ rest, (if (G.get idx).val.1 = v then f (eqL idx) else 0) := fun f v => by
    rw [Finset.sum_filter, ← eqL.sum_comp, hrest_split]
    simp only [hGL_get, ↓reduceIte, if_neg hne, eik]
    congr 1; refine Finset.sum_congr rfl fun idx hidx => by
      have hnq : idx ≠ q := fun h => hq_nrest (h ▸ hidx); simp [hnq]
  have hsum_L_in : ∀ (f : Fin G_L.length → ℕ) (v : Fin m),
      (∑ idx ∈ Finset.univ.filter (fun idx : Fin G_L.length => (G_L.get idx).val.2 = v), f idx) =
      (if j = v then f (eqL p) else 0) + (if k = v then f (eqL q) else 0) +
      ∑ idx ∈ rest, (if (G.get idx).val.2 = v then f (eqL idx) else 0) := fun f v => by
    rw [Finset.sum_filter, ← eqL.sum_comp, hrest_split]
    simp only [hGL_get, ↓reduceIte, if_neg hne, eik]
    congr 1; refine Finset.sum_congr rfl fun idx hidx => by
      have hnq : idx ≠ q := fun h => hq_nrest (h ▸ hidx); simp [hnq]
  have hindeg_L : ∀ v : Fin m, multigraphIndeg G_L v = multigraphIndeg G v := fun v => by
    unfold multigraphIndeg
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, hsum_L_in (fun _ => 1) v,
        hsum_flt (fun idx => (G.get idx).val.2 = v) (fun _ => 1)]
  have hsum_R_out : ∀ (f : Fin G_R.length → ℕ) (v : Fin m),
      (∑ idx ∈ Finset.univ.filter (fun idx : Fin G_R.length => (G_R.get idx).val.1 = v), f idx) =
      (if i = v then f (eqR p) else 0) + (if j = v then f (eqR q) else 0) +
      ∑ idx ∈ rest, (if (G.get idx).val.1 = v then f (eqR idx) else 0) := fun f v => by
    rw [Finset.sum_filter, ← eqR.sum_comp, hrest_split]
    simp only [hGR_get, ↓reduceIte, if_neg hne.symm, eik, hj_eq]
    congr 1; refine Finset.sum_congr rfl fun idx hidx => by
      have hnp : idx ≠ p := fun h => hp_nrest (h ▸ hidx); simp [hnp]
  have hsum_R_in : ∀ (f : Fin G_R.length → ℕ) (v : Fin m),
      (∑ idx ∈ Finset.univ.filter (fun idx : Fin G_R.length => (G_R.get idx).val.2 = v), f idx) =
      (if k = v then f (eqR p) else 0) + (if k = v then f (eqR q) else 0) +
      ∑ idx ∈ rest, (if (G.get idx).val.2 = v then f (eqR idx) else 0) := fun f v => by
    rw [Finset.sum_filter, ← eqR.sum_comp, hrest_split]
    simp only [hGR_get, ↓reduceIte, if_neg hne.symm, eik]
    congr 1; refine Finset.sum_congr rfl fun idx hidx => by
      have hnp : idx ≠ p := fun h => hp_nrest (h ▸ hidx); simp [hnp]
  have hindeg_R : ∀ v : Fin m,
      multigraphIndeg G_R v =
        (if k = v then 1 else 0) + (if k = v then 1 else 0) +
        ∑ idx ∈ rest, (if (G.get idx).val.2 = v then 1 else 0) := fun v => by
    unfold multigraphIndeg; rw [Finset.card_eq_sum_ones]; exact hsum_R_in (fun _ => 1) v
  have hindeg_G : ∀ v : Fin m,
      multigraphIndeg G v =
        (if j = v then 1 else 0) + (if k = v then 1 else 0) +
        ∑ idx ∈ rest, (if (G.get idx).val.2 = v then 1 else 0) := fun v => by
    unfold multigraphIndeg; rw [Finset.card_eq_sum_ones]
    exact hsum_flt (fun idx => (G.get idx).val.2 = v) (fun _ => 1)
  have hsum_G_out : ∀ (f : Fin G.length → ℕ) (v : Fin m),
      (∑ idx ∈ Finset.univ.filter (fun idx : Fin G.length => (G.get idx).val.1 = v), f idx) =
      (if i = v then f p else 0) + (if j = v then f q else 0) +
      ∑ idx ∈ rest, (if (G.get idx).val.1 = v then f idx else 0) := fun f v => by
    have h := hsum_flt (fun idx => (G.get idx).val.1 = v) f; rw [hj_eq] at h; exact h
  have hsum_G_in : ∀ (f : Fin G.length → ℕ) (v : Fin m),
      (∑ idx ∈ Finset.univ.filter (fun idx : Fin G.length => (G.get idx).val.2 = v), f idx) =
      (if j = v then f p else 0) + (if k = v then f q else 0) +
      ∑ idx ∈ rest, (if (G.get idx).val.2 = v then f idx else 0) := fun f v =>
    hsum_flt (fun idx => (G.get idx).val.2 = v) f
  exact if hle : F.val.1 q ≤ F.val.1 p then
    Sum.inl ⟨(fun r => if eqL.symm r = p then F.val.1 p - F.val.1 q else F.val.1 (eqL.symm r), F.val.2), by
      intro v
      have hF := F.prop v
      rw [hsum_G_out, hsum_G_in] at hF
      rw [hsum_L_out, hsum_L_in, hindeg_L]
      simp only [Equiv.symm_apply_apply, ↓reduceIte, if_neg hne.symm]
      have hrest1 : ∑ idx ∈ rest, (if (G.get idx).val.1 = v then if idx = p then F.val.1 p - F.val.1 q else F.val.1 idx else 0) =
          ∑ idx ∈ rest, (if (G.get idx).val.1 = v then F.val.1 idx else 0) :=
        Finset.sum_congr rfl fun idx hidx => by have : idx ≠ p := fun h => hp_nrest (h ▸ hidx); simp [this]
      have hrest2 : ∑ idx ∈ rest, (if (G.get idx).val.2 = v then if idx = p then F.val.1 p - F.val.1 q else F.val.1 idx else 0) =
          ∑ idx ∈ rest, (if (G.get idx).val.2 = v then F.val.1 idx else 0) :=
        Finset.sum_congr rfl fun idx hidx => by have : idx ≠ p := fun h => hp_nrest (h ▸ hidx); simp [this]
      rw [hrest1, hrest2]
      split_ifs at hF ⊢ <;> omega⟩
  else
    Sum.inr ⟨(fun r => if eqR.symm r = q then F.val.1 q - F.val.1 p - 1 else F.val.1 (eqR.symm r), F.val.2), by
      intro v
      have hF := F.prop v
      rw [hsum_G_out, hsum_G_in, hindeg_G] at hF
      rw [hsum_R_out, hsum_R_in, hindeg_R]
      simp only [Equiv.symm_apply_apply, ↓reduceIte, if_neg hne]
      have hrest1 : ∑ idx ∈ rest, (if (G.get idx).val.1 = v then if idx = q then F.val.1 q - F.val.1 p - 1 else F.val.1 idx else 0) =
          ∑ idx ∈ rest, (if (G.get idx).val.1 = v then F.val.1 idx else 0) :=
        Finset.sum_congr rfl fun idx hidx => by have : idx ≠ q := fun h => hq_nrest (h ▸ hidx); simp [this]
      have hrest2 : ∑ idx ∈ rest, (if (G.get idx).val.2 = v then if idx = q then F.val.1 q - F.val.1 p - 1 else F.val.1 idx else 0) =
          ∑ idx ∈ rest, (if (G.get idx).val.2 = v then F.val.1 idx else 0) :=
        Finset.sum_congr rfl fun idx hidx => by have : idx ≠ q := fun h => hq_nrest (h ▸ hidx); simp [this]
      rw [hrest1, hrest2]
      split_ifs at hF ⊢ <;> omega⟩

/-- Inverse map of Lemma 2.1 reduction bijection `F(G_L) ⊕ F(G_R) → F(G)`. -/
private def reductionStepInv {m : ℕ} (G : List (DirEdge m)) (p q : Fin G.length)
    (hne : p ≠ q) (hchain : (G.get p).val.2 = (G.get q).val.1)
    (S : GraphFlow (G.set q.val ⟨((G.get p).val.1, (G.get q).val.2),
      lt_trans (G.get p).prop (hchain ▸ (G.get q).prop)⟩) ⊕
    GraphFlow (G.set p.val ⟨((G.get p).val.1, (G.get q).val.2),
      lt_trans (G.get p).prop (hchain ▸ (G.get q).prop)⟩)) :
    GraphFlow G := by
  let i : Fin m := (G.get p).val.1
  let j : Fin m := (G.get p).val.2
  let k : Fin m := (G.get q).val.2
  have hj_eq : (G.get q).val.1 = j := hchain.symm
  have hij : i < j := (G.get p).prop
  have hjk : j < k := by change (G.get p).val.2 < (G.get q).val.2; rw [hchain]; exact (G.get q).prop
  have hik : i < k := lt_trans hij hjk
  let eik : DirEdge m := ⟨(i, k), hik⟩
  let G_L := G.set q.val eik
  let G_R := G.set p.val eik
  let eqL : Fin G.length ≃ Fin G_L.length := finCongr List.length_set.symm
  let eqR : Fin G.length ≃ Fin G_R.length := finCongr List.length_set.symm
  have hGL_get : ∀ idx : Fin G.length, G_L.get (eqL idx) = if idx = q then eik else G.get idx := fun idx => by
    by_cases h : idx = q
    · subst h; simp [G_L, eqL]
    · have hv : idx.val ≠ q.val := fun e => h (Fin.ext e)
      simp [G_L, eqL, h, List.getElem_set_ne (Ne.symm hv)]
  have hGR_get : ∀ idx : Fin G.length, G_R.get (eqR idx) = if idx = p then eik else G.get idx := fun idx => by
    by_cases h : idx = p
    · subst h; simp [G_R, eqR]
    · have hv : idx.val ≠ p.val := fun e => h (Fin.ext e)
      simp [G_R, eqR, h, List.getElem_set_ne (Ne.symm hv)]
  let rest : Finset (Fin G.length) := (Finset.univ.erase p).erase q
  have hp_nrest : p ∉ rest := by simp [rest]
  have hq_nrest : q ∉ rest := by simp [rest]
  have hrest_split : ∀ (g : Fin G.length → ℕ),
      ∑ idx : Fin G.length, g idx = g p + g q + ∑ idx ∈ rest, g idx := fun g => by
    have h1 : ∑ idx : Fin G.length, g idx = g p + ∑ idx ∈ Finset.univ.erase p, g idx := by
      rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ p)]
    have hq_mem : q ∈ Finset.univ.erase p := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ q⟩
    have h2 : ∑ idx ∈ Finset.univ.erase p, g idx = g q + ∑ idx ∈ rest, g idx := by
      rw [add_comm, Finset.sum_erase_add _ _ hq_mem]
    omega
  have hsum_flt : ∀ (P : Fin G.length → Prop) [DecidablePred P] (f : Fin G.length → ℕ),
      ∑ idx ∈ Finset.univ.filter P, f idx =
        (if P p then f p else 0) + (if P q then f q else 0) +
        ∑ idx ∈ rest, (if P idx then f idx else 0) := fun P _ f => by
    rw [Finset.sum_filter, hrest_split]
  have hsum_L_out : ∀ (f : Fin G_L.length → ℕ) (v : Fin m),
      (∑ idx ∈ Finset.univ.filter (fun idx : Fin G_L.length => (G_L.get idx).val.1 = v), f idx) =
      (if i = v then f (eqL p) else 0) + (if i = v then f (eqL q) else 0) +
      ∑ idx ∈ rest, (if (G.get idx).val.1 = v then f (eqL idx) else 0) := fun f v => by
    rw [Finset.sum_filter, ← eqL.sum_comp, hrest_split]
    simp only [hGL_get, ↓reduceIte, if_neg hne, eik]
    congr 1; refine Finset.sum_congr rfl fun idx hidx => by
      have hnq : idx ≠ q := fun h => hq_nrest (h ▸ hidx); simp [hnq]
  have hsum_L_in : ∀ (f : Fin G_L.length → ℕ) (v : Fin m),
      (∑ idx ∈ Finset.univ.filter (fun idx : Fin G_L.length => (G_L.get idx).val.2 = v), f idx) =
      (if j = v then f (eqL p) else 0) + (if k = v then f (eqL q) else 0) +
      ∑ idx ∈ rest, (if (G.get idx).val.2 = v then f (eqL idx) else 0) := fun f v => by
    rw [Finset.sum_filter, ← eqL.sum_comp, hrest_split]
    simp only [hGL_get, ↓reduceIte, if_neg hne, eik]
    congr 1; refine Finset.sum_congr rfl fun idx hidx => by
      have hnq : idx ≠ q := fun h => hq_nrest (h ▸ hidx); simp [hnq]
  have hindeg_L : ∀ v : Fin m, multigraphIndeg G_L v = multigraphIndeg G v := fun v => by
    unfold multigraphIndeg
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, hsum_L_in (fun _ => 1) v,
        hsum_flt (fun idx => (G.get idx).val.2 = v) (fun _ => 1)]
  have hsum_R_out : ∀ (f : Fin G_R.length → ℕ) (v : Fin m),
      (∑ idx ∈ Finset.univ.filter (fun idx : Fin G_R.length => (G_R.get idx).val.1 = v), f idx) =
      (if i = v then f (eqR p) else 0) + (if j = v then f (eqR q) else 0) +
      ∑ idx ∈ rest, (if (G.get idx).val.1 = v then f (eqR idx) else 0) := fun f v => by
    rw [Finset.sum_filter, ← eqR.sum_comp, hrest_split]
    simp only [hGR_get, ↓reduceIte, if_neg hne.symm, eik, hj_eq]
    congr 1; refine Finset.sum_congr rfl fun idx hidx => by
      have hnp : idx ≠ p := fun h => hp_nrest (h ▸ hidx); simp [hnp]
  have hsum_R_in : ∀ (f : Fin G_R.length → ℕ) (v : Fin m),
      (∑ idx ∈ Finset.univ.filter (fun idx : Fin G_R.length => (G_R.get idx).val.2 = v), f idx) =
      (if k = v then f (eqR p) else 0) + (if k = v then f (eqR q) else 0) +
      ∑ idx ∈ rest, (if (G.get idx).val.2 = v then f (eqR idx) else 0) := fun f v => by
    rw [Finset.sum_filter, ← eqR.sum_comp, hrest_split]
    simp only [hGR_get, ↓reduceIte, if_neg hne.symm, eik]
    congr 1; refine Finset.sum_congr rfl fun idx hidx => by
      have hnp : idx ≠ p := fun h => hp_nrest (h ▸ hidx); simp [hnp]
  have hindeg_R : ∀ v : Fin m,
      multigraphIndeg G_R v =
        (if k = v then 1 else 0) + (if k = v then 1 else 0) +
        ∑ idx ∈ rest, (if (G.get idx).val.2 = v then 1 else 0) := fun v => by
    unfold multigraphIndeg; rw [Finset.card_eq_sum_ones]; exact hsum_R_in (fun _ => 1) v
  have hindeg_G : ∀ v : Fin m,
      multigraphIndeg G v =
        (if j = v then 1 else 0) + (if k = v then 1 else 0) +
        ∑ idx ∈ rest, (if (G.get idx).val.2 = v then 1 else 0) := fun v => by
    unfold multigraphIndeg; rw [Finset.card_eq_sum_ones]
    exact hsum_flt (fun idx => (G.get idx).val.2 = v) (fun _ => 1)
  have hsum_G_out : ∀ (f : Fin G.length → ℕ) (v : Fin m),
      (∑ idx ∈ Finset.univ.filter (fun idx : Fin G.length => (G.get idx).val.1 = v), f idx) =
      (if i = v then f p else 0) + (if j = v then f q else 0) +
      ∑ idx ∈ rest, (if (G.get idx).val.1 = v then f idx else 0) := fun f v => by
    have h := hsum_flt (fun idx => (G.get idx).val.1 = v) f; rw [hj_eq] at h; exact h
  have hsum_G_in : ∀ (f : Fin G.length → ℕ) (v : Fin m),
      (∑ idx ∈ Finset.univ.filter (fun idx : Fin G.length => (G.get idx).val.2 = v), f idx) =
      (if j = v then f p else 0) + (if k = v then f q else 0) +
      ∑ idx ∈ rest, (if (G.get idx).val.2 = v then f idx else 0) := fun f v =>
    hsum_flt (fun idx => (G.get idx).val.2 = v) f
  exact match S with
    | Sum.inl FL =>
      ⟨(fun idx => if idx = p then FL.val.1 (eqL p) + FL.val.1 (eqL q) else FL.val.1 (eqL idx), FL.val.2), by
        intro v
        have hFL := FL.prop v
        rw [hsum_L_out, hsum_L_in, hindeg_L] at hFL
        rw [hsum_G_out, hsum_G_in]
        simp only [↓reduceIte, if_neg hne.symm]
        have hrest1 : ∑ idx ∈ rest, (if (G.get idx).val.1 = v then if idx = p then FL.val.1 (eqL p) + FL.val.1 (eqL q) else FL.val.1 (eqL idx) else 0) =
            ∑ idx ∈ rest, (if (G.get idx).val.1 = v then FL.val.1 (eqL idx) else 0) :=
          Finset.sum_congr rfl fun idx hidx => by have : idx ≠ p := fun h => hp_nrest (h ▸ hidx); simp [this]
        have hrest2 : ∑ idx ∈ rest, (if (G.get idx).val.2 = v then if idx = p then FL.val.1 (eqL p) + FL.val.1 (eqL q) else FL.val.1 (eqL idx) else 0) =
            ∑ idx ∈ rest, (if (G.get idx).val.2 = v then FL.val.1 (eqL idx) else 0) :=
          Finset.sum_congr rfl fun idx hidx => by have : idx ≠ p := fun h => hp_nrest (h ▸ hidx); simp [this]
        rw [hrest1, hrest2]
        split_ifs at hFL ⊢ <;> omega⟩
    | Sum.inr FR =>
      ⟨(fun idx => if idx = q then FR.val.1 (eqR p) + FR.val.1 (eqR q) + 1 else FR.val.1 (eqR idx), FR.val.2), by
        intro v
        have hFR := FR.prop v
        rw [hsum_R_out, hsum_R_in, hindeg_R] at hFR
        rw [hsum_G_out, hsum_G_in, hindeg_G]
        simp only [↓reduceIte, if_neg hne]
        have hrest1 : ∑ idx ∈ rest, (if (G.get idx).val.1 = v then if idx = q then FR.val.1 (eqR p) + FR.val.1 (eqR q) + 1 else FR.val.1 (eqR idx) else 0) =
            ∑ idx ∈ rest, (if (G.get idx).val.1 = v then FR.val.1 (eqR idx) else 0) :=
          Finset.sum_congr rfl fun idx hidx => by have : idx ≠ q := fun h => hq_nrest (h ▸ hidx); simp [this]
        have hrest2 : ∑ idx ∈ rest, (if (G.get idx).val.2 = v then if idx = q then FR.val.1 (eqR p) + FR.val.1 (eqR q) + 1 else FR.val.1 (eqR idx) else 0) =
            ∑ idx ∈ rest, (if (G.get idx).val.2 = v then FR.val.1 (eqR idx) else 0) :=
          Finset.sum_congr rfl fun idx hidx => by have : idx ≠ q := fun h => hq_nrest (h ▸ hidx); simp [this]
        rw [hrest1, hrest2]
        split_ifs at hFR ⊢ <;> omega⟩

/-- Reduction step bijection `F(G) ≃ F(G_L) ⊕ F(G_R)` (Lemma 2.1 / Morales–Shi Lemma 16). -/
private def reductionStepEquiv {m : ℕ} (G : List (DirEdge m)) (p q : Fin G.length)
    (hne : p ≠ q) (hchain : (G.get p).val.2 = (G.get q).val.1) :
    GraphFlow G ≃
      GraphFlow (G.set q.val ⟨((G.get p).val.1, (G.get q).val.2),
        lt_trans (G.get p).prop (hchain ▸ (G.get q).prop)⟩) ⊕
      GraphFlow (G.set p.val ⟨((G.get p).val.1, (G.get q).val.2),
        lt_trans (G.get p).prop (hchain ▸ (G.get q).prop)⟩) where
  toFun := reductionStepTo G p q hne hchain
  invFun := reductionStepInv G p q hne hchain
  left_inv := fun F => by
    unfold reductionStepTo reductionStepInv
    dsimp only
    by_cases hle : F.val.1 q ≤ F.val.1 p
    · rw [dif_pos hle]
      apply Subtype.ext; refine Prod.ext ?_ rfl; funext idx
      dsimp only
      by_cases h1 : idx = p
      · rw [h1, if_pos rfl, Equiv.symm_apply_apply, if_pos rfl, Equiv.symm_apply_apply, if_neg hne.symm]
        omega
      · rw [if_neg h1, Equiv.symm_apply_apply, if_neg h1]
    · rw [dif_neg hle]
      apply Subtype.ext; refine Prod.ext ?_ rfl; funext idx
      dsimp only
      by_cases h1 : idx = q
      · rw [h1, if_pos rfl, Equiv.symm_apply_apply, if_neg hne, Equiv.symm_apply_apply, if_pos rfl]
        omega
      · rw [if_neg h1, Equiv.symm_apply_apply, if_neg h1]
  right_inv := fun S => by
    unfold reductionStepTo reductionStepInv
    cases S with
    | inl FL =>
      dsimp only
      have hcond : (if q = p then FL.val.1 ((finCongr List.length_set.symm) p) + FL.val.1 ((finCongr List.length_set.symm) q) else FL.val.1 ((finCongr List.length_set.symm) q)) ≤
          (if p = p then FL.val.1 ((finCongr List.length_set.symm) p) + FL.val.1 ((finCongr List.length_set.symm) q) else FL.val.1 ((finCongr List.length_set.symm) p)) := by
        rw [if_neg hne.symm, if_pos rfl]; omega
      rw [dif_pos hcond]
      congr 1; apply Subtype.ext; refine Prod.ext ?_ rfl; funext r
      dsimp only
      by_cases hr : (finCongr List.length_set.symm).symm r = p
      · have hreq : (finCongr List.length_set.symm) p = r := ((Equiv.symm_apply_eq _).mp hr).symm
        rw [if_pos hr, if_pos rfl, if_neg hne.symm, hreq]; omega
      · rw [if_neg hr, if_neg hr, Equiv.apply_symm_apply]
    | inr FR =>
      dsimp only
      have hcond : ¬ ((if q = q then FR.val.1 ((finCongr List.length_set.symm) p) + FR.val.1 ((finCongr List.length_set.symm) q) + 1 else FR.val.1 ((finCongr List.length_set.symm) q)) ≤
          (if p = q then FR.val.1 ((finCongr List.length_set.symm) p) + FR.val.1 ((finCongr List.length_set.symm) q) + 1 else FR.val.1 ((finCongr List.length_set.symm) p))) := by
        rw [if_pos rfl, if_neg hne]; omega
      rw [dif_neg hcond]
      congr 1; apply Subtype.ext; refine Prod.ext ?_ rfl; funext r
      dsimp only
      by_cases hr : (finCongr List.length_set.symm).symm r = q
      · have hreq : (finCongr List.length_set.symm) q = r := ((Equiv.symm_apply_eq _).mp hr).symm
        rw [if_pos hr, if_pos rfl, if_neg hne, hreq]; omega
      · rw [if_neg hr, if_neg hr, Equiv.apply_symm_apply]

private lemma redTree_leaves_eq_card {m : ℕ} {G : List (DirEdge m)} (T : RedTree m G) :
    T.leaves = Nat.card (GraphFlow G) := by
  induction T with
  | leaf G hterm =>
    let _ : Finite (GraphFlow G) := graphFlow_finite G
    let _ : Fintype (GraphFlow G) := Fintype.ofFinite _
    have huniq : ∀ F : GraphFlow G, F = ⟨(fun _ => 0, multigraphIndeg G), by
        intro i; simp⟩ := by
      intro F
      have hf0 : ∀ idx : Fin G.length, F.val.1 idx = 0 := by
        intro idx
        let u := (G.get idx).val.1
        have hnoin : ∀ idx' : Fin G.length, (G.get idx').val.2 ≠ u := fun idx' =>
          hterm (G.get idx') (List.get_mem _ _) (G.get idx) (List.get_mem _ _)
        have hFu := F.prop u
        have hflt_in : (Finset.univ.filter fun idx' : Fin G.length => (G.get idx').val.2 = u) = ∅ := by
          ext idx'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          exact hnoin idx'
        have hind0 : multigraphIndeg G u = 0 := by unfold multigraphIndeg; rw [hflt_in, Finset.card_empty]
        rw [hind0, hflt_in, Finset.sum_empty, add_zero] at hFu
        have hmem : idx ∈ Finset.univ.filter (fun idx' : Fin G.length => (G.get idx').val.1 = u) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
        have hle := Finset.single_le_sum (f := F.val.1) (fun _ _ => Nat.zero_le _) hmem
        omega
      apply Subtype.ext; apply Prod.ext
      · funext idx; exact hf0 idx
      · funext i
        have hFi := F.prop i
        have h0out : ∑ idx ∈ Finset.univ.filter (fun idx : Fin G.length => (G.get idx).val.1 = i), F.val.1 idx = 0 :=
          Finset.sum_eq_zero fun idx _ => hf0 idx
        have h0in : ∑ idx ∈ Finset.univ.filter (fun idx : Fin G.length => (G.get idx).val.2 = i), F.val.1 idx = 0 :=
          Finset.sum_eq_zero fun idx _ => hf0 idx
        rw [h0out, h0in] at hFi; omega
    have hcard1 : Fintype.card (GraphFlow G) = 1 := by
      refine Fintype.card_eq_one_iff.mpr ⟨⟨(fun _ => 0, multigraphIndeg G), by intro i; simp⟩, huniq⟩
    rw [RedTree.leaves, Nat.card_eq_fintype_card, hcard1]
  | step G p q hne hchain l r ihl ihr =>
    let _ := graphFlow_finite G
    let _ := graphFlow_finite (G.set q.val ⟨((G.get p).val.1, (G.get q).val.2), lt_trans (G.get p).prop (hchain ▸ (G.get q).prop)⟩)
    let _ := graphFlow_finite (G.set p.val ⟨((G.get p).val.1, (G.get q).val.2), lt_trans (G.get p).prop (hchain ▸ (G.get q).prop)⟩)
    let _ : Fintype (GraphFlow G) := Fintype.ofFinite _
    let _ : Fintype (GraphFlow (G.set q.val ⟨((G.get p).val.1, (G.get q).val.2), lt_trans (G.get p).prop (hchain ▸ (G.get q).prop)⟩)) := Fintype.ofFinite _
    let _ : Fintype (GraphFlow (G.set p.val ⟨((G.get p).val.1, (G.get q).val.2), lt_trans (G.get p).prop (hchain ▸ (G.get q).prop)⟩)) := Fintype.ofFinite _
    rw [RedTree.leaves, ihl, ihr, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rw [Fintype.card_congr (reductionStepEquiv G p q hne hchain), Fintype.card_sum]

/-! ### Part 3: Identification `F(K_m) ≃ A_{m,0}` -/

private lemma completeEdges_nodup (m : ℕ) : (completeEdges m).Nodup := by
  unfold completeEdges
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => ?_, ?_⟩
  · refine (List.nodup_finRange m).filterMap ?_
    intro j₁ j₂ e h1 h2
    by_cases c1 : i < j₁
    · rw [dif_pos c1] at h1
      by_cases c2 : i < j₂
      · rw [dif_pos c2] at h2
        simp only [Option.mem_def, Option.some.injEq] at h1 h2
        exact congrArg (fun x : DirEdge m => x.val.2) (h1.trans h2.symm)
      · rw [dif_neg c2] at h2; simp at h2
    · rw [dif_neg c1] at h1; simp at h1
  · refine (List.nodup_finRange m).imp_of_mem fun {i₁ i₂} _ _ hne e he₁ he₂ => ?_
    simp only [List.mem_filterMap, List.mem_finRange, true_and] at he₁ he₂
    obtain ⟨j₁, hj₁⟩ := he₁; obtain ⟨j₂, hj₂⟩ := he₂
    by_cases c1 : i₁ < j₁
    · rw [dif_pos c1] at hj₁
      by_cases c2 : i₂ < j₂
      · rw [dif_pos c2] at hj₂
        simp only [Option.some.injEq] at hj₁ hj₂
        exact hne (congrArg (fun x : DirEdge m => x.val.1) (hj₁.trans hj₂.symm))
      · rw [dif_neg c2] at hj₂; simp at hj₂
    · rw [dif_neg c1] at hj₁; simp at hj₁

private lemma mem_completeEdges {m : ℕ} (e : DirEdge m) : e ∈ completeEdges m := by
  unfold completeEdges
  rw [List.mem_flatMap]
  refine ⟨e.val.1, List.mem_finRange _, ?_⟩
  rw [List.mem_filterMap]
  refine ⟨e.val.2, List.mem_finRange _, ?_⟩
  rw [dif_pos e.prop]

private noncomputable def completeEdgeEquiv (m : ℕ) : Fin (completeEdges m).length ≃ DirEdge m :=
  Equiv.ofBijective (fun idx => (completeEdges m).get idx)
    ⟨fun a b h => by
        have hnd := completeEdges_nodup m
        exact (List.nodup_iff_injective_get.mp hnd) h,
     fun e => List.mem_iff_get.mp (mem_completeEdges e)⟩

private lemma multigraphIndeg_completeEdges (m : ℕ) (i : Fin m) :
    multigraphIndeg (completeEdges m) i = i.val := by
  unfold multigraphIndeg
  have hbij : (Finset.univ.filter fun idx : Fin (completeEdges m).length =>
      ((completeEdges m).get idx).val.2 = i).card =
      (Finset.univ.filter fun h : Fin m => h < i).card := by
    refine Finset.card_bij (fun idx _ => ((completeEdges m).get idx).val.1) ?_ ?_ ?_
    · intro idx hidx
      have h2 := (Finset.mem_filter.mp hidx).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2 ▸ ((completeEdges m).get idx).prop⟩
    · intro a ha b hb heq
      have ha2 := (Finset.mem_filter.mp ha).2
      have hb2 := (Finset.mem_filter.mp hb).2
      exact (completeEdgeEquiv m).injective (Subtype.ext (Prod.ext heq (ha2.trans hb2.symm)))
    · intro h hh
      have hlt : h < i := (Finset.mem_filter.mp hh).2
      refine ⟨(completeEdgeEquiv m).symm ⟨(h, i), hlt⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := (completeEdgeEquiv m).apply_symm_apply ⟨(h, i), hlt⟩
        exact congrArg (fun x : DirEdge m => x.val.2) this
      · have := (completeEdgeEquiv m).apply_symm_apply ⟨(h, i), hlt⟩
        exact congrArg (fun x : DirEdge m => x.val.1) this
  rw [hbij]
  have himg : ((Finset.univ.filter fun h : Fin m => h < i).image Fin.val) = Finset.range i.val := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    exact ⟨fun ⟨h, hh, hval⟩ => hval ▸ hh, fun hx => ⟨⟨x, lt_trans hx i.isLt⟩, hx, rfl⟩⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]

private noncomputable def completeGraphFlowEquivTwoExitZero (m : ℕ) :
    GraphFlow (completeEdges m) ≃ TwoExitFlow m 0 := by
  let e := completeEdgeEquiv m
  have hsum_out : ∀ (f : Fin (completeEdges m).length → ℕ) (i : Fin m),
      (∑ idx ∈ Finset.univ.filter (fun idx => ((completeEdges m).get idx).val.1 = i), f idx) =
      ∑ ed ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.1 = i), f (e.symm ed) := fun f i => by
    rw [Finset.sum_filter, Finset.sum_filter, ← e.sum_comp]
    refine Finset.sum_congr rfl fun idx _ => by simp only [e.symm_apply_apply]; rfl
  have hsum_in : ∀ (f : Fin (completeEdges m).length → ℕ) (i : Fin m),
      (∑ idx ∈ Finset.univ.filter (fun idx => ((completeEdges m).get idx).val.2 = i), f idx) =
      ∑ ed ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.2 = i), f (e.symm ed) := fun f i => by
    rw [Finset.sum_filter, Finset.sum_filter, ← e.sum_comp]
    refine Finset.sum_congr rfl fun idx _ => by simp only [e.symm_apply_apply]; rfl
  refine
    { toFun := fun F => ⟨(fun ed => F.val.1 (e.symm ed), F.val.2, fun _ => 0), by
        refine ⟨fun i => ?_, by simp⟩
        have hF := F.prop i
        rw [hsum_out, hsum_in, multigraphIndeg_completeEdges] at hF
        simpa using hF⟩
      invFun := fun F => ⟨(fun idx => F.val.1 (e idx), F.val.2.1), by
        intro i
        have hr0 : ∀ j : Fin m, F.val.2.2 j = 0 := by
          intro j
          have hcard := F.prop.2
          rw [Finset.card_eq_zero] at hcard
          by_contra hne
          have : j ∈ Finset.univ.filter (fun j : Fin m => 0 < F.val.2.2 j) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hne⟩
          rw [hcard] at this; exact Finset.notMem_empty _ this
        have hF := F.prop.1 i
        rw [hr0 i, add_zero] at hF
        rw [hsum_out, hsum_in, multigraphIndeg_completeEdges]
        simpa [e.apply_symm_apply] using hF⟩
      left_inv := fun F => by
        apply Subtype.ext; refine Prod.ext ?_ rfl; funext idx; simp
      right_inv := fun F => by
        have hr0 : ∀ j : Fin m, F.val.2.2 j = 0 := by
          intro j
          have hcard := F.prop.2
          rw [Finset.card_eq_zero] at hcard
          by_contra hne
          have : j ∈ Finset.univ.filter (fun j : Fin m => 0 < F.val.2.2 j) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hne⟩
          rw [hcard] at this; exact Finset.notMem_empty _ this
        apply Subtype.ext; refine Prod.ext ?_ (Prod.ext rfl ?_)
        · funext ed; simp
        · funext j; exact (hr0 j).symm }

/-! ### Part 4: Lemma 3.1 (Morales–Shi Recurrence) & Proposition 5.1 (Marked-Pair Bijection) -/

private lemma card_dirEdge_on_subset {m : ℕ} (S : Finset (Fin m)) :
    (Finset.univ.filter fun e : DirEdge m => e.val.1 ∈ S ∧ e.val.2 ∈ S).card =
      Nat.choose S.card 2 := by
  rw [← Finset.card_powersetCard 2 S]
  refine Finset.card_bij (fun e _ => ({e.val.1, e.val.2} : Finset (Fin m))) ?_ ?_ ?_
  · intro e he
    have ⟨h1, h2⟩ := (Finset.mem_filter.mp he).2
    refine Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair (ne_of_lt e.prop)⟩
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · intro e₁ _ e₂ _ heq
    have hlt1 : e₁.val.1 < e₁.val.2 := e₁.prop
    have hlt2 : e₂.val.1 < e₂.val.2 := e₂.prop
    have h1in : e₁.val.1 ∈ ({e₂.val.1, e₂.val.2} : Finset (Fin m)) := heq ▸ Finset.mem_insert_self _ _
    have h2in : e₁.val.2 ∈ ({e₂.val.1, e₂.val.2} : Finset (Fin m)) := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1in h2in
    have h1eq : e₁.val.1 = e₂.val.1 ∧ e₁.val.2 = e₂.val.2 := by
      rcases h1in with ha | ha <;> rcases h2in with hb | hb
      · exfalso; exact ne_of_lt hlt1 (ha.trans hb.symm)
      · exact ⟨ha, hb⟩
      · exfalso; exact not_lt_of_gt hlt1 (ha ▸ hb ▸ hlt2)
      · exfalso; exact ne_of_lt hlt1 (ha.trans hb.symm)
    exact Subtype.ext (Prod.ext h1eq.1 h1eq.2)
  · intro P hP
    obtain ⟨hPS, hP2⟩ := Finset.mem_powersetCard.mp hP
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hP2
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · refine ⟨⟨(a, b), hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPS (Finset.mem_insert_self _ _),
        hPS (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩, rfl⟩
    · refine ⟨⟨(b, a), hgt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hPS (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), hPS (Finset.mem_insert_self _ _)⟩,
        Finset.pair_comm b a⟩

/-- Ordinary exit bijection (Section 3): inactive exit slots in `A_{m,k-1}` biject with
    marked active vertices in `A_{m,k}`. -/
private def exitSlotEquiv (m k : ℕ) (hk : 1 ≤ k) :
    { x : TwoExitFlow m (k - 1) × Fin m × ℕ // x.1.val.2.2 x.2.1 = 0 ∧ x.2.2 < x.1.val.2.1 x.2.1 } ≃
    { y : TwoExitFlow m k × Fin m // 0 < y.1.val.2.2 y.2 } :=
  { toFun := fun ⟨⟨F, i, s⟩, hi0', hs'⟩ =>
      have hi0 : F.val.2.2 i = 0 := hi0'
      have hs : s < F.val.2.1 i := hs'
      let b' := Function.update F.val.2.1 i (F.val.2.1 i - (s + 1))
      let r' := Function.update F.val.2.2 i (s + 1)
      have hcons : ∀ v : Fin m,
          b' v + r' v + ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.1 = v), F.val.1 e =
          v.val + ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.2 = v), F.val.1 e := fun v => by
        have hF := F.prop.1 v
        by_cases hv : v = i
        · subst hv; simp only [b', r', Function.update_self]; rw [hi0] at hF; omega
        · simp only [b', r', Function.update_of_ne hv]; exact hF
      have hact : (Finset.univ.filter fun v : Fin m => 0 < r' v).card = k := by
        have heq : (Finset.univ.filter fun v : Fin m => 0 < r' v) =
            insert i (Finset.univ.filter fun v : Fin m => 0 < F.val.2.2 v) := by
          ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          by_cases hv : v = i
          · subst hv; simp [r']
          · simp [r', hv]
        have hni : i ∉ Finset.univ.filter (fun v : Fin m => 0 < F.val.2.2 v) := by simp [hi0]
        rw [heq, Finset.card_insert_of_notMem hni, F.prop.2]; omega
      ⟨(⟨(F.val.1, b', r'), hcons, hact⟩, i), by simp [r']⟩
    invFun := fun ⟨⟨F', i⟩, hi_pos'⟩ =>
      have hi_pos : 0 < F'.val.2.2 i := hi_pos'
      let b := Function.update F'.val.2.1 i (F'.val.2.1 i + F'.val.2.2 i)
      let r := Function.update F'.val.2.2 i 0
      have hcons : ∀ v : Fin m,
          b v + r v + ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.1 = v), F'.val.1 e =
          v.val + ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.2 = v), F'.val.1 e := fun v => by
        have hF := F'.prop.1 v
        by_cases hv : v = i
        · subst hv; simp only [b, r, Function.update_self]; omega
        · simp only [b, r, Function.update_of_ne hv]; exact hF
      have hact : (Finset.univ.filter fun v : Fin m => 0 < r v).card = k - 1 := by
        have heq : (Finset.univ.filter fun v : Fin m => 0 < r v) =
            (Finset.univ.filter fun v : Fin m => 0 < F'.val.2.2 v).erase i := by
          ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          by_cases hv : v = i
          · subst hv; simp [r]
          · simp [r, hv]
        have hi_mem : i ∈ Finset.univ.filter (fun v : Fin m => 0 < F'.val.2.2 v) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi_pos⟩
        rw [heq, Finset.card_erase_of_mem hi_mem, F'.prop.2]
      ⟨(⟨(F'.val.1, b, r), hcons, hact⟩, i, F'.val.2.2 i - 1),
        by simp [r], by simp only [b, Function.update_self]; omega⟩
    left_inv := fun ⟨⟨F, i, s⟩, hi0', hs'⟩ => by
      have hi0 : F.val.2.2 i = 0 := hi0'
      have hs : s < F.val.2.1 i := hs'
      apply Subtype.ext; refine Prod.ext ?_ (Prod.ext rfl ?_)
      · apply Subtype.ext; refine Prod.ext rfl (Prod.ext ?_ ?_)
        · funext v; by_cases hv : v = i
          · subst hv; simp only [Function.update_self]; omega
          · simp [hv]
        · funext v; by_cases hv : v = i
          · subst hv; simp [hi0]
          · simp [hv]
      · simp only [Function.update_self]; omega
    right_inv := fun ⟨⟨F', i⟩, hi_pos'⟩ => by
      have hi_pos : 0 < F'.val.2.2 i := hi_pos'
      apply Subtype.ext; refine Prod.ext ?_ rfl
      apply Subtype.ext; refine Prod.ext rfl (Prod.ext ?_ ?_)
      · funext v; by_cases hv : v = i
        · subst hv; simp only [Function.update_self]; omega
        · simp [hv]
      · funext v; by_cases hv : v = i
        · subst hv; simp only [Function.update_self]; omega
        · simp [hv] }

/-- Helper for updating a single edge `e₀ = (i, j)` and distinguished exits `r_i, r_j`
    by transferring `δ` units from `f_{e₀}` and `r_j` to `r_i`. -/
private lemma update_edge_sum_out {m : ℕ} (f : DirEdge m → ℕ) (e₀ : DirEdge m) (val : ℕ) (v : Fin m) :
    (∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.1 = v), Function.update f e₀ val e) =
    if e₀.val.1 = v then
      val + ∑ e ∈ (Finset.univ.filter (fun e : DirEdge m => e.val.1 = v)).erase e₀, f e
    else
      ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.1 = v), f e := by
  by_cases hv : e₀.val.1 = v
  · rw [if_pos hv]
    have hmem : e₀ ∈ Finset.univ.filter (fun e : DirEdge m => e.val.1 = v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    rw [← Finset.add_sum_erase _ _ hmem, Function.update_self]
    congr 1; refine Finset.sum_congr rfl fun e he => Function.update_of_ne (Finset.ne_of_mem_erase he) _ _
  · rw [if_neg hv]
    refine Finset.sum_congr rfl fun e he => Function.update_of_ne ?_ _ _
    intro h; exact hv (h ▸ (Finset.mem_filter.mp he).2)

private lemma update_edge_sum_in {m : ℕ} (f : DirEdge m → ℕ) (e₀ : DirEdge m) (val : ℕ) (v : Fin m) :
    (∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.2 = v), Function.update f e₀ val e) =
    if e₀.val.2 = v then
      val + ∑ e ∈ (Finset.univ.filter (fun e : DirEdge m => e.val.2 = v)).erase e₀, f e
    else
      ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.2 = v), f e := by
  by_cases hv : e₀.val.2 = v
  · rw [if_pos hv]
    have hmem : e₀ ∈ Finset.univ.filter (fun e : DirEdge m => e.val.2 = v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    rw [← Finset.add_sum_erase _ _ hmem, Function.update_self]
    congr 1; refine Finset.sum_congr rfl fun e he => Function.update_of_ne (Finset.ne_of_mem_erase he) _ _
  · rw [if_neg hv]
    refine Finset.sum_congr rfl fun e he => Function.update_of_ne ?_ _ _
    intro h; exact hv (h ▸ (Finset.mem_filter.mp he).2)

/-- Forward map of slot-pivoting bijection `U → V ⊕ W`. -/
private def pivotTo (m k : ℕ) (hk : 1 ≤ k)
    (x : { x : TwoExitFlow m (k - 1) × DirEdge m × ℕ //
      x.1.val.2.2 x.2.1.val.1 = 0 ∧ 0 < x.1.val.2.2 x.2.1.val.2 ∧ x.2.2 < x.1.val.1 x.2.1 }) :
    { y : TwoExitFlow m (k - 1) × DirEdge m × ℕ //
      0 < y.1.val.2.2 y.2.1.val.1 ∧ y.1.val.2.2 y.2.1.val.2 = 0 ∧ y.2.2 ≤ y.1.val.1 y.2.1 } ⊕
    { z : TwoExitFlow m k × DirEdge m //
      0 < z.1.val.2.2 z.2.val.1 ∧ 0 < z.1.val.2.2 z.2.val.2 } :=
    let F := x.val.1
    let e := x.val.2.1
    let s := x.val.2.2
    have hi0 : F.val.2.2 e.val.1 = 0 := x.prop.1
    have hjpos : 0 < F.val.2.2 e.val.2 := x.prop.2.1
    have hs : s < F.val.1 e := x.prop.2.2
    let i := e.val.1
    let j := e.val.2
    have hij : i ≠ j := ne_of_lt e.prop
    let p := F.val.1 e
    let t := F.val.2.2 j
    if hst : s + 1 < t then
      let f' := Function.update F.val.1 e (p - (s + 1))
      let r' := Function.update (Function.update F.val.2.2 i (s + 1)) j (t - (s + 1))
      have hcons : ∀ v : Fin m,
          F.val.2.1 v + r' v + ∑ ed ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.1 = v), f' ed =
          v.val + ∑ ed ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.2 = v), f' ed := fun v => by
        have hF := F.prop.1 v
        rw [update_edge_sum_out, update_edge_sum_in]
        by_cases hvi : v = i
        · subst hvi
          have hmem : e ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.1 = i) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
          rw [← Finset.add_sum_erase _ _ hmem] at hF
          have he1 : e.val.1 = i := rfl
          have he2 : e.val.2 ≠ i := hij.symm
          simp only [he1, he2, ↓reduceIte, r', Function.update_of_ne hij, Function.update_self]
          dsimp only [p] at *; rw [hi0] at hF; omega
        · by_cases hvj : v = j
          · subst hvj
            have hmem : e ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.2 = j) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
            rw [← Finset.add_sum_erase _ _ hmem] at hF
            have he1 : e.val.1 ≠ j := hij
            have he2 : e.val.2 = j := rfl
            simp only [he1, he2, ↓reduceIte, r', Function.update_self]
            dsimp only [p, t] at *; omega
          · have hni : e.val.1 ≠ v := fun h => hvi h.symm
            have hnj : e.val.2 ≠ v := fun h => hvj h.symm
            simp only [if_neg hni, if_neg hnj, r', Function.update_of_ne hvj, Function.update_of_ne hvi]
            exact hF
      have hact : (Finset.univ.filter fun v : Fin m => 0 < r' v).card = k := by
        have heq : (Finset.univ.filter fun v : Fin m => 0 < r' v) =
            insert i (Finset.univ.filter fun v : Fin m => 0 < F.val.2.2 v) := by
          ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          by_cases hvj : v = j
          · subst hvj; simp only [r', Function.update_self]; constructor
            · intro _; exact Or.inr hjpos
            · intro _; omega
          · by_cases hvi : v = i
            · subst hvi; simp [r', hij]
            · simp [r', hvj, hvi]
        have hni : i ∉ Finset.univ.filter (fun v : Fin m => 0 < F.val.2.2 v) := by simp [i, hi0]
        rw [heq, Finset.card_insert_of_notMem hni, F.prop.2]; omega
      Sum.inr ⟨(⟨(f', F.val.2.1, r'), hcons, hact⟩, e),
        by change 0 < r' i; simp only [r', Function.update_of_ne hij, Function.update_self]; omega,
        by change 0 < r' j; simp only [r', Function.update_self]; omega⟩
    else
      let f' := Function.update F.val.1 e (p - t)
      let r' := Function.update (Function.update F.val.2.2 i t) j 0
      have hcons : ∀ v : Fin m,
          F.val.2.1 v + r' v + ∑ ed ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.1 = v), f' ed =
          v.val + ∑ ed ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.2 = v), f' ed := fun v => by
        have hF := F.prop.1 v
        rw [update_edge_sum_out, update_edge_sum_in]
        by_cases hvi : v = i
        · subst hvi
          have hmem : e ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.1 = i) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
          rw [← Finset.add_sum_erase _ _ hmem] at hF
          have he1 : e.val.1 = i := rfl
          have he2 : e.val.2 ≠ i := hij.symm
          simp only [he1, he2, ↓reduceIte, r', Function.update_of_ne hij, Function.update_self]
          dsimp only [p, t] at *; rw [hi0] at hF; omega
        · by_cases hvj : v = j
          · subst hvj
            have hmem : e ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.2 = j) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
            rw [← Finset.add_sum_erase _ _ hmem] at hF
            have he1 : e.val.1 ≠ j := hij
            have he2 : e.val.2 = j := rfl
            simp only [he1, he2, ↓reduceIte, r', Function.update_self]
            dsimp only [p, t] at *; omega
          · have hni : e.val.1 ≠ v := fun h => hvi h.symm
            have hnj : e.val.2 ≠ v := fun h => hvj h.symm
            simp only [if_neg hni, if_neg hnj, r', Function.update_of_ne hvj, Function.update_of_ne hvi]
            exact hF
      have hact : (Finset.univ.filter fun v : Fin m => 0 < r' v).card = k - 1 := by
        have heq : (Finset.univ.filter fun v : Fin m => 0 < r' v) =
            insert i ((Finset.univ.filter fun v : Fin m => 0 < F.val.2.2 v).erase j) := by
          ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase]
          by_cases hvj : v = j
          · subst hvj; simp [r', hij.symm]
          · by_cases hvi : v = i
            · subst hvi; simp [r', hij, t, j, hjpos]
            · simp [r', hvj, hvi]
        have hni : i ∉ (Finset.univ.filter fun v : Fin m => 0 < F.val.2.2 v).erase j := by simp [i, hi0]
        have hjmem : j ∈ Finset.univ.filter (fun v : Fin m => 0 < F.val.2.2 v) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjpos⟩
        rw [heq, Finset.card_insert_of_notMem hni, Finset.card_erase_add_one hjmem, F.prop.2]
      Sum.inl ⟨(⟨(f', F.val.2.1, r'), hcons, hact⟩, e, s + 1 - t),
        by change 0 < r' i; simp only [r', Function.update_of_ne hij, Function.update_self]; exact hjpos,
        by change r' j = 0; simp [r'],
        by simp only [f', Function.update_self]; dsimp only [p, t] at *; omega⟩

/-- Inverse map of slot-pivoting bijection `V ⊕ W → U`. -/
private def pivotInv (m k : ℕ)
    (S : { y : TwoExitFlow m (k - 1) × DirEdge m × ℕ //
      0 < y.1.val.2.2 y.2.1.val.1 ∧ y.1.val.2.2 y.2.1.val.2 = 0 ∧ y.2.2 ≤ y.1.val.1 y.2.1 } ⊕
    { z : TwoExitFlow m k × DirEdge m //
      0 < z.1.val.2.2 z.2.val.1 ∧ 0 < z.1.val.2.2 z.2.val.2 }) :
    { x : TwoExitFlow m (k - 1) × DirEdge m × ℕ //
      x.1.val.2.2 x.2.1.val.1 = 0 ∧ 0 < x.1.val.2.2 x.2.1.val.2 ∧ x.2.2 < x.1.val.1 x.2.1 } :=
  match S with
  | Sum.inl y =>
    let F' := y.val.1
    let e := y.val.2.1
    let s' := y.val.2.2
    have hipos : 0 < F'.val.2.2 e.val.1 := y.prop.1
    have hj0 : F'.val.2.2 e.val.2 = 0 := y.prop.2.1
    have hs' : s' ≤ F'.val.1 e := y.prop.2.2
    let i := e.val.1
    let j := e.val.2
    have hij : i ≠ j := ne_of_lt e.prop
    let u := F'.val.2.2 i
    let f := Function.update F'.val.1 e (F'.val.1 e + u)
    let r := Function.update (Function.update F'.val.2.2 i 0) j u
    have hcons : ∀ v : Fin m,
        F'.val.2.1 v + r v + ∑ ed ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.1 = v), f ed =
        v.val + ∑ ed ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.2 = v), f ed := fun v => by
      have hF := F'.prop.1 v
      rw [update_edge_sum_out, update_edge_sum_in]
      by_cases hvi : v = i
      · subst hvi
        have hmem : e ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.1 = i) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
        rw [← Finset.add_sum_erase _ _ hmem] at hF
        have he1 : e.val.1 = i := rfl
        have he2 : e.val.2 ≠ i := hij.symm
        simp only [he1, he2, ↓reduceIte, r, Function.update_of_ne hij, Function.update_self]
        dsimp only [u] at *; omega
      · by_cases hvj : v = j
        · subst hvj
          have hmem : e ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.2 = j) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
          rw [← Finset.add_sum_erase _ _ hmem] at hF
          have he1 : e.val.1 ≠ j := hij
          have he2 : e.val.2 = j := rfl
          simp only [he1, he2, ↓reduceIte, r, Function.update_self]
          rw [hj0] at hF; dsimp only [u] at *; omega
        · have hni : e.val.1 ≠ v := fun h => hvi h.symm
          have hnj : e.val.2 ≠ v := fun h => hvj h.symm
          simp only [if_neg hni, if_neg hnj, r, Function.update_of_ne hvj, Function.update_of_ne hvi]
          exact hF
    have hact : (Finset.univ.filter fun v : Fin m => 0 < r v).card = k - 1 := by
      have heq : (Finset.univ.filter fun v : Fin m => 0 < r v) =
          insert j ((Finset.univ.filter fun v : Fin m => 0 < F'.val.2.2 v).erase i) := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase]
        by_cases hvj : v = j
        · subst hvj; simp [r, u, i, hipos]
        · by_cases hvi : v = i
          · subst hvi; simp [r, hij]
          · simp [r, hvj, hvi]
      have hnj : j ∉ (Finset.univ.filter fun v : Fin m => 0 < F'.val.2.2 v).erase i := by simp [j, hj0]
      have himem : i ∈ Finset.univ.filter (fun v : Fin m => 0 < F'.val.2.2 v) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hipos⟩
      rw [heq, Finset.card_insert_of_notMem hnj, Finset.card_erase_add_one himem, F'.prop.2]
    ⟨(⟨(f, F'.val.2.1, r), hcons, hact⟩, e, s' + u - 1),
      by change r i = 0; simp [r, hij],
      by change 0 < r j; simp [r, u, i, hipos],
      by simp only [f, Function.update_self]; dsimp only [u, i] at *; omega⟩
  | Sum.inr z =>
    let F' := z.val.1
    let e := z.val.2
    have hipos : 0 < F'.val.2.2 e.val.1 := z.prop.1
    have hjpos : 0 < F'.val.2.2 e.val.2 := z.prop.2
    let i := e.val.1
    let j := e.val.2
    have hij : i ≠ j := ne_of_lt e.prop
    let u := F'.val.2.2 i
    let v0 := F'.val.2.2 j
    let f := Function.update F'.val.1 e (F'.val.1 e + u)
    let r := Function.update (Function.update F'.val.2.2 i 0) j (u + v0)
    have hcons : ∀ w : Fin m,
        F'.val.2.1 w + r w + ∑ ed ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.1 = w), f ed =
        w.val + ∑ ed ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.2 = w), f ed := fun w => by
      have hF := F'.prop.1 w
      rw [update_edge_sum_out, update_edge_sum_in]
      by_cases hwi : w = i
      · subst hwi
        have hmem : e ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.1 = i) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
        rw [← Finset.add_sum_erase _ _ hmem] at hF
        have he1 : e.val.1 = i := rfl
        have he2 : e.val.2 ≠ i := hij.symm
        simp only [he1, he2, ↓reduceIte, r, Function.update_of_ne hij, Function.update_self]
        dsimp only [u] at *; omega
      · by_cases hwj : w = j
        · subst hwj
          have hmem : e ∈ Finset.univ.filter (fun ed : DirEdge m => ed.val.2 = j) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
          rw [← Finset.add_sum_erase _ _ hmem] at hF
          have he1 : e.val.1 ≠ j := hij
          have he2 : e.val.2 = j := rfl
          simp only [he1, he2, ↓reduceIte, r, Function.update_self]
          dsimp only [u, v0] at *; omega
        · have hni : e.val.1 ≠ w := fun h => hwi h.symm
          have hnj : e.val.2 ≠ w := fun h => hwj h.symm
          simp only [if_neg hni, if_neg hnj, r, Function.update_of_ne hwj, Function.update_of_ne hwi]
          exact hF
    have hact : (Finset.univ.filter fun w : Fin m => 0 < r w).card = k - 1 := by
      have heq : (Finset.univ.filter fun w : Fin m => 0 < r w) =
          (Finset.univ.filter fun w : Fin m => 0 < F'.val.2.2 w).erase i := by
        ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        by_cases hwj : w = j
        · subst hwj; simp only [r, Function.update_self]; constructor
          · intro _; exact ⟨hij.symm, hjpos⟩
          · intro _; dsimp only [u, v0]; omega
        · by_cases hwi : w = i
          · subst hwi; simp [r, hij]
          · simp [r, hwj, hwi]
      have himem : i ∈ Finset.univ.filter (fun w : Fin m => 0 < F'.val.2.2 w) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hipos⟩
      rw [heq, Finset.card_erase_of_mem himem, F'.prop.2]
    ⟨(⟨(f, F'.val.2.1, r), hcons, hact⟩, e, u - 1),
      by change r i = 0; simp [r, hij],
      by change 0 < r j; simp only [r, Function.update_self]; dsimp only [u, v0, i, j]; omega,
      by simp only [f, Function.update_self]; dsimp only [u, i]; omega⟩

/-- Slot-pivoting bijection `U ≃ V ⊕ W` (Section 3, eq. (3.3)). -/
private def pivotEquiv (m k : ℕ) (hk : 1 ≤ k) :
    { x : TwoExitFlow m (k - 1) × DirEdge m × ℕ //
      x.1.val.2.2 x.2.1.val.1 = 0 ∧ 0 < x.1.val.2.2 x.2.1.val.2 ∧ x.2.2 < x.1.val.1 x.2.1 } ≃
    { y : TwoExitFlow m (k - 1) × DirEdge m × ℕ //
      0 < y.1.val.2.2 y.2.1.val.1 ∧ y.1.val.2.2 y.2.1.val.2 = 0 ∧ y.2.2 ≤ y.1.val.1 y.2.1 } ⊕
    { z : TwoExitFlow m k × DirEdge m //
      0 < z.1.val.2.2 z.2.val.1 ∧ 0 < z.1.val.2.2 z.2.val.2 } where
  toFun := pivotTo m k hk
  invFun := pivotInv m k
  left_inv := fun ⟨⟨F, e, s⟩, hi0', hjpos', hs'⟩ => by
    have hi0 : F.val.2.2 e.val.1 = 0 := hi0'
    have hjpos : 0 < F.val.2.2 e.val.2 := hjpos'
    have hs : s < F.val.1 e := hs'
    have hij : e.val.1 ≠ e.val.2 := ne_of_lt e.prop
    unfold pivotTo pivotInv
    dsimp only
    by_cases hst : s + 1 < F.val.2.2 e.val.2
    · rw [dif_pos hst]; dsimp only
      apply Subtype.ext; refine Prod.ext ?_ (Prod.ext rfl ?_)
      · apply Subtype.ext; refine Prod.ext ?_ (Prod.ext rfl ?_)
        · funext ed; by_cases hed : ed = e
          · subst hed; simp only [Function.update_self, Function.update_of_ne hij]; omega
          · simp [hed]
        · funext v
          by_cases hvj : v = e.val.2
          · subst hvj; simp only [Function.update_self, Function.update_of_ne hij]; omega
          · by_cases hvi : v = e.val.1
            · subst hvi; simp [hij, hi0]
            · simp [hvj, hvi]
      · simp only [Function.update_of_ne hij, Function.update_self]; omega
    · rw [dif_neg hst]; dsimp only
      apply Subtype.ext; refine Prod.ext ?_ (Prod.ext rfl ?_)
      · apply Subtype.ext; refine Prod.ext ?_ (Prod.ext rfl ?_)
        · funext ed; by_cases hed : ed = e
          · subst hed; simp only [Function.update_self, Function.update_of_ne hij]; omega
          · simp [hed]
        · funext v
          by_cases hvj : v = e.val.2
          · subst hvj; simp only [Function.update_self, Function.update_of_ne hij]
          · by_cases hvi : v = e.val.1
            · subst hvi; simp [hij, hi0]
            · simp [hvj, hvi]
      · simp only [Function.update_of_ne hij, Function.update_self]; omega
  right_inv := fun S => by
    unfold pivotTo pivotInv
    cases S with
    | inl y =>
      rcases y with ⟨⟨F', e, s'⟩, hipos', hj0', hs''⟩
      have hipos : 0 < F'.val.2.2 e.val.1 := hipos'
      have hj0 : F'.val.2.2 e.val.2 = 0 := hj0'
      have hs' : s' ≤ F'.val.1 e := hs''
      have hij : e.val.1 ≠ e.val.2 := ne_of_lt e.prop
      dsimp only
      have hnot : ¬ (s' + F'.val.2.2 e.val.1 - 1 + 1 <
          Function.update (Function.update F'.val.2.2 e.val.1 0) e.val.2 (F'.val.2.2 e.val.1) e.val.2) := by
        simp only [Function.update_self]; omega
      rw [dif_neg hnot]
      congr 1; apply Subtype.ext; refine Prod.ext ?_ (Prod.ext rfl ?_)
      · apply Subtype.ext; refine Prod.ext ?_ (Prod.ext rfl ?_)
        · funext ed; by_cases hed : ed = e
          · subst hed; simp only [Function.update_self]; omega
          · simp [hed]
        · funext v
          by_cases hvj : v = e.val.2
          · subst hvj; simp [hj0]
          · by_cases hvi : v = e.val.1
            · subst hvi; simp [hij]
            · simp [hvj, hvi]
      · simp only [Function.update_self]; omega
    | inr z =>
      rcases z with ⟨⟨F', e⟩, hipos', hjpos'⟩
      have hipos : 0 < F'.val.2.2 e.val.1 := hipos'
      have hjpos : 0 < F'.val.2.2 e.val.2 := hjpos'
      have hij : e.val.1 ≠ e.val.2 := ne_of_lt e.prop
      dsimp only
      have hlt : F'.val.2.2 e.val.1 - 1 + 1 <
          Function.update (Function.update F'.val.2.2 e.val.1 0) e.val.2
            (F'.val.2.2 e.val.1 + F'.val.2.2 e.val.2) e.val.2 := by
        simp only [Function.update_self]; omega
      rw [dif_pos hlt]
      congr 1; apply Subtype.ext; refine Prod.ext ?_ rfl
      apply Subtype.ext; refine Prod.ext ?_ (Prod.ext rfl ?_)
      · funext ed; by_cases hed : ed = e
        · subst hed; simp only [Function.update_self]; omega
        · simp [hed]
      · funext v
        by_cases hvj : v = e.val.2
        · subst hvj; simp only [Function.update_self]; omega
        · by_cases hvi : v = e.val.1
          · subst hvi; simp only [Function.update_of_ne hij, Function.update_self]; omega
          · simp [hvj, hvi]

private lemma morales_shi_recurrence (m k : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ m - 1) :
    Nat.choose (k + 1) 2 * Nat.card (TwoExitFlow m k) =
      Nat.choose (m - k + 1) 2 * Nat.card (TwoExitFlow m (k - 1)) := by
  let _ := twoExitFlow_finite m k
  let _ := twoExitFlow_finite m (k - 1)
  let _ : Fintype (TwoExitFlow m k) := Fintype.ofFinite _
  let _ : Fintype (TwoExitFlow m (k - 1)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  -- Double count equation (3.2) over all `F ∈ A_{m,k-1}` and all inactive vertices `i` (`r_i = 0`).
  have hdouble :
      (∑ F : TwoExitFlow m (k - 1), ∑ i ∈ Finset.univ.filter (fun i : Fin m => F.val.2.2 i = 0),
        (F.val.2.1 i + ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.1 = i), F.val.1 e)) =
      ∑ F : TwoExitFlow m (k - 1), ∑ i ∈ Finset.univ.filter (fun i : Fin m => F.val.2.2 i = 0),
        ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.2 = i), (F.val.1 e + 1) := by
    refine Finset.sum_congr rfl fun F _ => Finset.sum_congr rfl fun i hi => ?_
    have hi0 : F.val.2.2 i = 0 := (Finset.mem_filter.mp hi).2
    have hF := F.prop.1 i
    rw [hi0, add_zero] at hF
    rw [hF, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, add_comm]
    congr 1
    have hcard_in : (Finset.univ.filter fun e : DirEdge m => e.val.2 = i).card = i.val := by
      have himg : ((Finset.univ.filter fun e : DirEdge m => e.val.2 = i).image fun e => e.val.1.val) =
          Finset.range i.val := by
        ext x; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
        constructor
        · rintro ⟨e, rfl, rfl⟩; exact e.prop
        · intro hx; exact ⟨⟨(⟨x, lt_trans hx i.isLt⟩, i), hx⟩, rfl, rfl⟩
      rw [← Finset.card_image_of_injOn (f := fun e : DirEdge m => e.val.1.val), himg, Finset.card_range]
      intro e₁ he₁ e₂ he₂ heq
      have h1 := (Finset.mem_filter.mp he₁).2
      have h2 := (Finset.mem_filter.mp he₂).2
      exact Subtype.ext (Prod.ext (Fin.ext heq) (h1.trans h2.symm))
    exact hcard_in.symm
  -- Split LHS into `S_exit + S_II + S_IA` and RHS into `S_II + C(m-k+1, 2) * a_{m,k-1} + S_AI`.
  let S_exit := ∑ F : TwoExitFlow m (k - 1), ∑ i ∈ Finset.univ.filter (fun i : Fin m => F.val.2.2 i = 0), F.val.2.1 i
  let S_II := ∑ F : TwoExitFlow m (k - 1), ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => F.val.2.2 e.val.1 = 0 ∧ F.val.2.2 e.val.2 = 0), F.val.1 e
  let S_IA := ∑ F : TwoExitFlow m (k - 1), ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => F.val.2.2 e.val.1 = 0 ∧ 0 < F.val.2.2 e.val.2), F.val.1 e
  let S_AI := ∑ F : TwoExitFlow m (k - 1), ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => 0 < F.val.2.2 e.val.1 ∧ F.val.2.2 e.val.2 = 0), (F.val.1 e + 1)
  have hLHS : (∑ F : TwoExitFlow m (k - 1), ∑ i ∈ Finset.univ.filter (fun i : Fin m => F.val.2.2 i = 0),
      (F.val.2.1 i + ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.1 = i), F.val.1 e)) =
      S_exit + S_II + S_IA := by
    simp only [Finset.sum_add_distrib, S_exit, S_II, S_IA, add_assoc]
    congr 1; rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [← Finset.sum_biUnion]
    · have hunion : ((Finset.univ.filter fun i : Fin m => F.val.2.2 i = 0).biUnion
          fun i => Finset.univ.filter fun e : DirEdge m => e.val.1 = i) =
          (Finset.univ.filter fun e : DirEdge m => F.val.2.2 e.val.1 = 0 ∧ F.val.2.2 e.val.2 = 0) ∪
          (Finset.univ.filter fun e : DirEdge m => F.val.2.2 e.val.1 = 0 ∧ 0 < F.val.2.2 e.val.2) := by
        ext e; simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, hi, rfl⟩; omega
        · intro h; exact ⟨e.val.1, by omega, rfl⟩
      have hdisj : Disjoint
          (Finset.univ.filter fun e : DirEdge m => F.val.2.2 e.val.1 = 0 ∧ F.val.2.2 e.val.2 = 0)
          (Finset.univ.filter fun e : DirEdge m => F.val.2.2 e.val.1 = 0 ∧ 0 < F.val.2.2 e.val.2) := by
        rw [Finset.disjoint_left]; intro e h1 h2
        have := (Finset.mem_filter.mp h1).2.2; have := (Finset.mem_filter.mp h2).2.2; omega
      rw [hunion, Finset.sum_union hdisj]
    · intro i _ j _ hij
      exact Finset.disjoint_left.mpr fun e h1 h2 =>
        hij (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
  have hRHS : (∑ F : TwoExitFlow m (k - 1), ∑ i ∈ Finset.univ.filter (fun i : Fin m => F.val.2.2 i = 0),
      ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.2 = i), (F.val.1 e + 1)) =
      S_II + Nat.choose (m - k + 1) 2 * Fintype.card (TwoExitFlow m (k - 1)) + S_AI := by
    have h1 : ∀ F : TwoExitFlow m (k - 1),
        (∑ i ∈ Finset.univ.filter (fun i : Fin m => F.val.2.2 i = 0),
          ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.2 = i), (F.val.1 e + 1)) =
        (∑ e ∈ Finset.univ.filter (fun e : DirEdge m => F.val.2.2 e.val.1 = 0 ∧ F.val.2.2 e.val.2 = 0), F.val.1 e) +
        Nat.choose (m - k + 1) 2 +
        (∑ e ∈ Finset.univ.filter (fun e : DirEdge m => 0 < F.val.2.2 e.val.1 ∧ F.val.2.2 e.val.2 = 0), (F.val.1 e + 1)) := by
      intro F
      rw [← Finset.sum_biUnion]
      · have hunion : ((Finset.univ.filter fun i : Fin m => F.val.2.2 i = 0).biUnion
            fun i => Finset.univ.filter fun e : DirEdge m => e.val.2 = i) =
            (Finset.univ.filter fun e : DirEdge m => F.val.2.2 e.val.1 = 0 ∧ F.val.2.2 e.val.2 = 0) ∪
            (Finset.univ.filter fun e : DirEdge m => 0 < F.val.2.2 e.val.1 ∧ F.val.2.2 e.val.2 = 0) := by
          ext e; simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨i, hi, rfl⟩; omega
          · intro h; exact ⟨e.val.2, by omega, rfl⟩
        have hdisj : Disjoint
            (Finset.univ.filter fun e : DirEdge m => F.val.2.2 e.val.1 = 0 ∧ F.val.2.2 e.val.2 = 0)
            (Finset.univ.filter fun e : DirEdge m => 0 < F.val.2.2 e.val.1 ∧ F.val.2.2 e.val.2 = 0) := by
          rw [Finset.disjoint_left]; intro e h1 h2
          have := (Finset.mem_filter.mp h1).2.1; have := (Finset.mem_filter.mp h2).2.1; omega
        rw [hunion, Finset.sum_union hdisj, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
        congr 2
        let Inact := Finset.univ.filter fun i : Fin m => F.val.2.2 i = 0
        have hInact_card : Inact.card = m - k + 1 := by
          let Act := Finset.univ.filter fun i : Fin m => 0 < F.val.2.2 i
          have hdisjA : Disjoint Act Inact := Finset.disjoint_left.mpr fun i h1 h2 => by
            have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
          have hunionA : Act ∪ Inact = Finset.univ := by
            ext i; simp only [Act, Inact, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; omega
          have hcomp := Finset.card_union_of_disjoint hdisjA
          rw [hunionA, Finset.card_univ, Fintype.card_fin] at hcomp
          have hAct : Act.card = k - 1 := F.prop.2
          omega
        have heq_f : (Finset.univ.filter fun e : DirEdge m => F.val.2.2 e.val.1 = 0 ∧ F.val.2.2 e.val.2 = 0) =
            (Finset.univ.filter fun e : DirEdge m => e.val.1 ∈ Inact ∧ e.val.2 ∈ Inact) := by
          ext e; simp [Inact]
        rw [heq_f, card_dirEdge_on_subset Inact, hInact_card]
      · intro i _ j _ hij
        exact Finset.disjoint_left.mpr fun e h1 h2 =>
          hij (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
    rw [Finset.sum_congr rfl fun F _ => h1 F, Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, S_II, S_AI]
  -- Evaluate `S_exit = k * |A_{m,k}|` via `exitSlotEquiv`!
  have hS_exit : S_exit = k * Fintype.card (TwoExitFlow m k) := by
    let LHS_t := { x : TwoExitFlow m (k - 1) × Fin m × ℕ // x.1.val.2.2 x.2.1 = 0 ∧ x.2.2 < x.1.val.2.1 x.2.1 }
    let RHS_t := { y : TwoExitFlow m k × Fin m // 0 < y.1.val.2.2 y.2 }
    have hL_fin : LHS_t ≃ Σ (F : TwoExitFlow m (k - 1)) (i : { i : Fin m // F.val.2.2 i = 0 }), Fin (F.val.2.1 i.val) :=
      { toFun := fun ⟨⟨F, i, s⟩, h1, h2⟩ => ⟨F, ⟨i, h1⟩, ⟨s, h2⟩⟩
        invFun := fun ⟨F, ⟨i, h1⟩, ⟨s, h2⟩⟩ => ⟨(F, i, s), h1, h2⟩
        left_inv := fun ⟨⟨_, _, _⟩, _, _⟩ => rfl
        right_inv := fun ⟨_, ⟨_, _⟩, ⟨_, _⟩⟩ => rfl }
    have hR_fin : RHS_t ≃ Σ (F' : TwoExitFlow m k), { i : Fin m // 0 < F'.val.2.2 i } :=
      { toFun := fun ⟨⟨F', i⟩, h⟩ => ⟨F', ⟨i, h⟩⟩
        invFun := fun ⟨F', ⟨i, h⟩⟩ => ⟨(F', i), h⟩
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
    let _ : Fintype LHS_t := Fintype.ofEquiv _ hL_fin.symm
    let _ : Fintype RHS_t := Fintype.ofEquiv _ hR_fin.symm
    have hcardL : Fintype.card LHS_t = S_exit := by
      rw [Fintype.card_congr hL_fin, Fintype.card_sigma]
      refine Finset.sum_congr rfl fun F _ => ?_
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      rw [← Finset.sum_coe_sort (Finset.univ.filter fun i : Fin m => F.val.2.2 i = 0) F.val.2.1]
      refine Finset.sum_bij (fun i _ => ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.prop⟩⟩)
        (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => Subtype.ext (Subtype.mk.inj h))
        (fun i _ => ⟨⟨i.val, (Finset.mem_filter.mp i.prop).2⟩, Finset.mem_univ _, Subtype.ext rfl⟩)
        (fun _ _ => rfl)
    have hcardR : Fintype.card RHS_t = k * Fintype.card (TwoExitFlow m k) := by
      rw [Fintype.card_congr hR_fin, Fintype.card_sigma]
      have hfib : ∀ F' : TwoExitFlow m k, Fintype.card { i : Fin m // 0 < F'.val.2.2 i } = k := fun F' => by
        rw [Fintype.card_subtype]; exact F'.prop.2
      simp_rw [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    rw [← hcardL, Fintype.card_congr (exitSlotEquiv m k hk1), hcardR]
  -- Evaluate `S_IA = S_AI + C(k, 2) * |A_{m,k}|` via `pivotEquiv`!
  have hS_piv : S_IA = S_AI + Nat.choose k 2 * Fintype.card (TwoExitFlow m k) := by
    let U_t := { x : TwoExitFlow m (k - 1) × DirEdge m × ℕ //
      x.1.val.2.2 x.2.1.val.1 = 0 ∧ 0 < x.1.val.2.2 x.2.1.val.2 ∧ x.2.2 < x.1.val.1 x.2.1 }
    let V_t := { y : TwoExitFlow m (k - 1) × DirEdge m × ℕ //
      0 < y.1.val.2.2 y.2.1.val.1 ∧ y.1.val.2.2 y.2.1.val.2 = 0 ∧ y.2.2 ≤ y.1.val.1 y.2.1 }
    let W_t := { z : TwoExitFlow m k × DirEdge m //
      0 < z.1.val.2.2 z.2.val.1 ∧ 0 < z.1.val.2.2 z.2.val.2 }
    have hU_eq : U_t ≃ Σ (F : TwoExitFlow m (k - 1))
        (e : { e : DirEdge m // F.val.2.2 e.val.1 = 0 ∧ 0 < F.val.2.2 e.val.2 }), Fin (F.val.1 e.val) :=
      { toFun := fun ⟨⟨F, e, s⟩, h1, h2, h3⟩ => ⟨F, ⟨e, h1, h2⟩, ⟨s, h3⟩⟩
        invFun := fun ⟨F, ⟨e, h1, h2⟩, ⟨s, h3⟩⟩ => ⟨(F, e, s), h1, h2, h3⟩
        left_inv := fun ⟨⟨_, _, _⟩, _, _, _⟩ => rfl
        right_inv := fun ⟨_, ⟨_, _, _⟩, ⟨_, _⟩⟩ => rfl }
    have hV_eq : V_t ≃ Σ (F : TwoExitFlow m (k - 1))
        (e : { e : DirEdge m // 0 < F.val.2.2 e.val.1 ∧ F.val.2.2 e.val.2 = 0 }), Fin (F.val.1 e.val + 1) :=
      { toFun := fun ⟨⟨F, e, s⟩, h1, h2, h3⟩ => ⟨F, ⟨e, h1, h2⟩, ⟨s, Nat.lt_succ_of_le h3⟩⟩
        invFun := fun ⟨F, ⟨e, h1, h2⟩, ⟨s, h3⟩⟩ => ⟨(F, e, s), h1, h2, Nat.le_of_lt_succ h3⟩
        left_inv := fun ⟨⟨_, _, _⟩, _, _, _⟩ => rfl
        right_inv := fun ⟨_, ⟨_, _, _⟩, ⟨_, _⟩⟩ => rfl }
    have hW_eq : W_t ≃ Σ (F' : TwoExitFlow m k),
        { e : DirEdge m // 0 < F'.val.2.2 e.val.1 ∧ 0 < F'.val.2.2 e.val.2 } :=
      { toFun := fun ⟨⟨F', e⟩, h⟩ => ⟨F', ⟨e, h⟩⟩
        invFun := fun ⟨F', ⟨e, h⟩⟩ => ⟨(F', e), h⟩
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
    let _ : Fintype U_t := Fintype.ofEquiv _ hU_eq.symm
    let _ : Fintype V_t := Fintype.ofEquiv _ hV_eq.symm
    let _ : Fintype W_t := Fintype.ofEquiv _ hW_eq.symm
    have hcardU : Fintype.card U_t = S_IA := by
      rw [Fintype.card_congr hU_eq, Fintype.card_sigma]
      refine Finset.sum_congr rfl fun F _ => ?_
      rw [Fintype.card_sigma]; simp only [Fintype.card_fin]
      rw [← Finset.sum_coe_sort (Finset.univ.filter fun e : DirEdge m => F.val.2.2 e.val.1 = 0 ∧ 0 < F.val.2.2 e.val.2) F.val.1]
      refine Finset.sum_bij (fun e _ => ⟨e.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.prop⟩⟩)
        (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => Subtype.ext (Subtype.mk.inj h))
        (fun e _ => ⟨⟨e.val, (Finset.mem_filter.mp e.prop).2⟩, Finset.mem_univ _, Subtype.ext rfl⟩)
        (fun _ _ => rfl)
    have hcardV : Fintype.card V_t = S_AI := by
      rw [Fintype.card_congr hV_eq, Fintype.card_sigma]
      refine Finset.sum_congr rfl fun F _ => ?_
      rw [Fintype.card_sigma]; simp only [Fintype.card_fin]
      rw [← Finset.sum_coe_sort (Finset.univ.filter fun e : DirEdge m => 0 < F.val.2.2 e.val.1 ∧ F.val.2.2 e.val.2 = 0) (fun e => F.val.1 e + 1)]
      refine Finset.sum_bij (fun e _ => ⟨e.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.prop⟩⟩)
        (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => Subtype.ext (Subtype.mk.inj h))
        (fun e _ => ⟨⟨e.val, (Finset.mem_filter.mp e.prop).2⟩, Finset.mem_univ _, Subtype.ext rfl⟩)
        (fun _ _ => rfl)
    have hcardW : Fintype.card W_t = Nat.choose k 2 * Fintype.card (TwoExitFlow m k) := by
      rw [Fintype.card_congr hW_eq, Fintype.card_sigma]
      have hfib : ∀ F' : TwoExitFlow m k,
          Fintype.card { e : DirEdge m // 0 < F'.val.2.2 e.val.1 ∧ 0 < F'.val.2.2 e.val.2 } = Nat.choose k 2 := fun F' => by
        rw [Fintype.card_subtype]
        let Act := Finset.univ.filter fun i : Fin m => 0 < F'.val.2.2 i
        have heq_f : (Finset.univ.filter fun e : DirEdge m => 0 < F'.val.2.2 e.val.1 ∧ 0 < F'.val.2.2 e.val.2) =
            (Finset.univ.filter fun e : DirEdge m => e.val.1 ∈ Act ∧ e.val.2 ∈ Act) := by
          ext e; simp [Act]
        rw [heq_f, card_dirEdge_on_subset Act, F'.prop.2]
      simp_rw [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    rw [← hcardU, Fintype.card_congr (pivotEquiv m k hk1), Fintype.card_sum, hcardV, hcardW]
  rw [hLHS, hRHS, hS_exit, hS_piv] at hdouble
  have hpas : Nat.choose (k + 1) 2 = k + Nat.choose k 2 := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
  rw [hpas, add_mul]; omega

private lemma marked_pair_bijection (m k : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ m - 1) :
    Nonempty (LeftMarkedFlow m k ≃ RightMarkedFlow m k) := by
  classical
  let _ := twoExitFlow_finite m k
  let _ := twoExitFlow_finite m (k - 1)
  let _ : Fintype (TwoExitFlow m k) := Fintype.ofFinite _
  let _ : Fintype (TwoExitFlow m (k - 1)) := Fintype.ofFinite _
  let _ : Fintype (LeftMarkedFlow m k) := Subtype.fintype _
  let _ : Fintype (RightMarkedFlow m k) := Subtype.fintype _
  apply Fintype.card_eq.mp
  have hL : Fintype.card (LeftMarkedFlow m k) = Nat.choose (k + 1) 2 * Nat.card (TwoExitFlow m k) := by
    rw [Nat.card_eq_fintype_card]
    let eqL : LeftMarkedFlow m k ≃ Σ F : TwoExitFlow m k,
        { P : Finset (Option (Fin m)) // P ∈ Finset.powersetCard 2
          (insert none ((Finset.univ.filter fun i : Fin m => 0 < F.val.2.2 i).image some)) } :=
      { toFun := fun ⟨⟨F, P⟩, hcard, hmem⟩ =>
          ⟨F, ⟨P, Finset.mem_powersetCard.mpr ⟨fun u hu => by
            cases u with
            | none => exact Finset.mem_insert_self _ _
            | some i => exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem _ hu⟩, rfl⟩),
            hcard⟩⟩⟩
        invFun := fun ⟨F, ⟨P, hP⟩⟩ =>
          ⟨(F, P), (Finset.mem_powersetCard.mp hP).2, fun u hu => by
            have hsub := (Finset.mem_powersetCard.mp hP).1 hu
            cases u with
            | none => trivial
            | some i =>
              simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
                Option.some.injEq, reduceCtorEq, false_or] at hsub
              obtain ⟨j, hj, rfl⟩ := hsub; exact hj⟩
        left_inv := fun ⟨⟨_, _⟩, _, _⟩ => rfl
        right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
    rw [Fintype.card_congr eqL, Fintype.card_sigma]
    have hfib : ∀ F : TwoExitFlow m k,
        Fintype.card { P : Finset (Option (Fin m)) // P ∈ Finset.powersetCard 2
          (insert none ((Finset.univ.filter fun i : Fin m => 0 < F.val.2.2 i).image some)) } =
        Nat.choose (k + 1) 2 := fun F => by
      rw [Fintype.card_coe, Finset.card_powersetCard]
      have hni : (none : Option (Fin m)) ∉ (Finset.univ.filter fun i : Fin m => 0 < F.val.2.2 i).image some := by
        simp
      rw [Finset.card_insert_of_notMem hni, Finset.card_image_of_injective _ (Option.some_injective (Fin m)), F.prop.2]
    exact (Finset.sum_congr rfl fun F _ => by convert hfib F).trans
      (by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm])
  have hR : Fintype.card (RightMarkedFlow m k) = Nat.choose (m - k + 1) 2 * Nat.card (TwoExitFlow m (k - 1)) := by
    rw [Nat.card_eq_fintype_card]
    let eqR : RightMarkedFlow m k ≃ Σ F : TwoExitFlow m (k - 1),
        { P : Finset (Fin m) // P ∈ Finset.powersetCard 2 (Finset.univ.filter fun i : Fin m => F.val.2.2 i = 0) } :=
      { toFun := fun ⟨⟨F, P⟩, hcard, hmem⟩ =>
          ⟨F, ⟨P, Finset.mem_powersetCard.mpr ⟨fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem i hi⟩, hcard⟩⟩⟩
        invFun := fun ⟨F, ⟨P, hP⟩⟩ =>
          ⟨(F, P), (Finset.mem_powersetCard.mp hP).2, fun i hi =>
            (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hP).1 hi)).2⟩
        left_inv := fun ⟨⟨_, _⟩, _, _⟩ => rfl
        right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
    rw [Fintype.card_congr eqR, Fintype.card_sigma]
    have hfib : ∀ F : TwoExitFlow m (k - 1),
        Fintype.card { P : Finset (Fin m) // P ∈ Finset.powersetCard 2 (Finset.univ.filter fun i : Fin m => F.val.2.2 i = 0) } =
        Nat.choose (m - k + 1) 2 := fun F => by
      rw [Fintype.card_coe, Finset.card_powersetCard]
      let Act := Finset.univ.filter fun i : Fin m => 0 < F.val.2.2 i
      let Inact := Finset.univ.filter fun i : Fin m => F.val.2.2 i = 0
      have hdisjA : Disjoint Act Inact := Finset.disjoint_left.mpr fun i h1 h2 => by
        have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
      have hunionA : Act ∪ Inact = Finset.univ := by
        ext i; simp only [Act, Inact, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; omega
      have hcomp := Finset.card_union_of_disjoint hdisjA
      rw [hunionA, Finset.card_univ, Fintype.card_fin] at hcomp
      have hAct : Act.card = k - 1 := F.prop.2
      have hcard : Inact.card = m - k + 1 := by omega
      change Nat.choose Inact.card 2 = _
      rw [hcard]
    exact (Finset.sum_congr rfl fun F _ => by convert hfib F).trans
      (by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm])
  rw [hL, hR]
  exact morales_shi_recurrence m k hk1 hkm

/-! ### Part 5: Narayana Refinement, Row Sum, Lemma 4.1 (Deletion), and Theorems 1.1 & 1.2 -/

private lemma two_mul_choose_two (n : ℕ) : 2 * Nat.choose n 2 = n * (n - 1) := by
  cases n with
  | zero => simp
  | succ k =>
    rw [Nat.choose_two_right]
    have hev : 2 ∣ (k + 1) * k := by
      rcases Nat.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · exact ⟨(2 * r + 1) * r, by ring⟩
      · exact ⟨(r + 1) * (2 * r + 1), by ring⟩
    simpa [Nat.add_sub_cancel] using Nat.mul_div_cancel' hev

private lemma narayana_formula (m k : ℕ) (hm : 1 ≤ m) (hkm : k ≤ m - 1) :
    m * Nat.card (TwoExitFlow m k) =
      Nat.card (GraphFlow (completeEdges m)) * Nat.choose m k * Nat.choose m (k + 1) := by
  induction k with
  | zero =>
    have h0 : Nat.card (TwoExitFlow m 0) = Nat.card (GraphFlow (completeEdges m)) :=
      (Nat.card_congr (completeGraphFlowEquivTwoExitZero m)).symm
    rw [h0, Nat.choose_zero_right, Nat.choose_one_right, mul_one, mul_comm]
  | succ k ih =>
    have hih := ih (by omega)
    have hrec := morales_shi_recurrence m (k + 1) (by omega) hkm
    simp only [Nat.add_sub_cancel] at hrec
    have hmul : 2 * Nat.choose (k + 2) 2 * (m * Nat.card (TwoExitFlow m (k + 1))) =
        2 * Nat.choose (k + 2) 2 * (Nat.card (GraphFlow (completeEdges m)) * Nat.choose m (k + 1) * Nat.choose m (k + 2)) := by
      have h1 : 2 * Nat.choose (k + 2) 2 * (m * Nat.card (TwoExitFlow m (k + 1))) =
          2 * Nat.choose (m - k) 2 * (m * Nat.card (TwoExitFlow m k)) := by
        have hsub : m - (k + 1) + 1 = m - k := by omega
        rw [hsub] at hrec
        calc 2 * Nat.choose (k + 2) 2 * (m * Nat.card (TwoExitFlow m (k + 1)))
            = 2 * m * (Nat.choose (k + 2) 2 * Nat.card (TwoExitFlow m (k + 1))) := by ring
          _ = 2 * m * (Nat.choose (m - k) 2 * Nat.card (TwoExitFlow m k)) := by rw [hrec]
          _ = 2 * Nat.choose (m - k) 2 * (m * Nat.card (TwoExitFlow m k)) := by ring
      rw [h1, hih, two_mul_choose_two, two_mul_choose_two]
      have hid1 : (k + 1) * Nat.choose m (k + 1) = (m - k) * Nat.choose m k := by
        linarith [Nat.choose_succ_right_eq m k]
      have hid2 : (k + 2) * Nat.choose m (k + 2) = (m - (k + 1)) * Nat.choose m (k + 1) := by
        linarith [Nat.choose_succ_right_eq m (k + 1)]
      have hmk : m - k - 1 = m - (k + 1) := by omega
      have hk2 : k + 2 - 1 = k + 1 := by omega
      rw [hmk, hk2]
      calc (m - k) * (m - (k + 1)) * (Nat.card (GraphFlow (completeEdges m)) * Nat.choose m k * Nat.choose m (k + 1))
          = Nat.card (GraphFlow (completeEdges m)) * ((m - k) * Nat.choose m k) * ((m - (k + 1)) * Nat.choose m (k + 1)) := by ring
        _ = Nat.card (GraphFlow (completeEdges m)) * ((k + 1) * Nat.choose m (k + 1)) * ((k + 2) * Nat.choose m (k + 2)) := by rw [← hid1, ← hid2]
        _ = (k + 2) * (k + 1) * (Nat.card (GraphFlow (completeEdges m)) * Nat.choose m (k + 1) * Nat.choose m (k + 2)) := by ring
    have hpos : 0 < 2 * Nat.choose (k + 2) 2 := by
      rw [two_mul_choose_two]; exact Nat.mul_pos (by omega) (by omega)
    exact Nat.eq_of_mul_eq_mul_left hpos hmul

private lemma row_sum_eq_catalan_mul (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.range m, Nat.card (TwoExitFlow m k) =
      catalanNum m * Nat.card (GraphFlow (completeEdges m)) := by
  apply Nat.eq_of_mul_eq_mul_left (show 0 < m by omega)
  rw [Finset.mul_sum]
  have hterm : ∀ k ∈ Finset.range m,
      m * Nat.card (TwoExitFlow m k) =
      Nat.card (GraphFlow (completeEdges m)) * (Nat.choose m k * Nat.choose m (m - 1 - k)) := by
    intro k hk
    have hkm : k < m := Finset.mem_range.mp hk
    rw [narayana_formula m k hm (by omega), mul_assoc]
    congr 2
    have hsym : Nat.choose m (k + 1) = Nat.choose m (m - (k + 1)) := (Nat.choose_symm (by omega)).symm
    rw [hsym, show m - (k + 1) = m - 1 - k by omega]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hvand : ∑ k ∈ Finset.range m, Nat.choose m k * Nat.choose m (m - 1 - k) = Nat.choose (2 * m) (m - 1) := by
    rw [show 2 * m = m + m by omega, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => Nat.choose m a * Nat.choose m b) (m - 1)]
    rw [show (m - 1).succ = m by omega]
  rw [hvand]
  have hcat_mul : m * catalanNum m = Nat.choose (2 * m) (m - 1) := by
    have h1 : (m + 1) * Nat.choose (2 * m) (m - 1) = m * Nat.choose (2 * m) m := by
      have h2 := Nat.choose_succ_right_eq (2 * m) (m - 1)
      have hsub1 : m - 1 + 1 = m := by omega
      have hsub2 : 2 * m - (m - 1) = m + 1 := by omega
      rw [hsub1, hsub2] at h2; linarith
    have hdvd : (m + 1) ∣ Nat.choose (2 * m) m := by
      have hcop : Nat.Coprime (m + 1) m := by simp
      exact hcop.dvd_of_dvd_mul_left ⟨Nat.choose (2 * m) (m - 1), h1.symm⟩
    have hdiv : (m + 1) * catalanNum m = Nat.choose (2 * m) m := by
      unfold catalanNum; exact Nat.mul_div_cancel' hdvd
    apply Nat.eq_of_mul_eq_mul_left (show 0 < m + 1 by omega)
    calc (m + 1) * (m * catalanNum m) = m * ((m + 1) * catalanNum m) := by ring
      _ = m * Nat.choose (2 * m) m := by rw [hdiv]
      _ = (m + 1) * Nat.choose (2 * m) (m - 1) := h1.symm
  calc Nat.card (GraphFlow (completeEdges m)) * Nat.choose (2 * m) (m - 1)
      = Nat.card (GraphFlow (completeEdges m)) * (m * catalanNum m) := by rw [hcat_mul]
    _ = m * (catalanNum m * Nat.card (GraphFlow (completeEdges m))) := by ring

/-- Lemma 4.1 (`lem:deletion`): Vertex-deletion bijection `A_{m+1,m} ≃ Σ k : Fin m, A_{m,k}`. -/
private def deletionEquiv (m : ℕ) (hm : 1 ≤ m) :
    TwoExitFlow (m + 1) m ≃ (k : Fin m) × TwoExitFlow m k.val := by
  have hzero_inact : ∀ (n k : ℕ) (hn : 1 ≤ n) (F : TwoExitFlow n k),
      F.val.2.1 ⟨0, hn⟩ = 0 ∧ F.val.2.2 ⟨0, hn⟩ = 0 ∧
      ∀ e : DirEdge n, e.val.1 = ⟨0, hn⟩ → F.val.1 e = 0 := by
    intro n k hn F
    have hF0 := F.prop.1 ⟨0, hn⟩
    have hnoin : (Finset.univ.filter fun e : DirEdge n => e.val.2 = ⟨0, hn⟩) = ∅ := by
      ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h; have := e.prop; rw [h] at this; exact Nat.not_lt_zero _ this
    rw [hnoin, Finset.sum_empty] at hF0
    dsimp only at hF0
    have hsum0 : ∑ e ∈ Finset.univ.filter (fun e : DirEdge n => e.val.1 = ⟨0, hn⟩), F.val.1 e = 0 := by omega
    refine ⟨by omega, by omega, fun e he => ?_⟩
    have hmem : e ∈ Finset.univ.filter (fun e : DirEdge n => e.val.1 = ⟨0, hn⟩) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
    have hle := Finset.single_le_sum (f := F.val.1) (fun _ _ => Nat.zero_le _) hmem
    omega
  have hsucc_pos : ∀ (F : TwoExitFlow (m + 1) m) (i : Fin m), 0 < F.val.2.2 i.succ := by
    intro F i
    have h0 := (hzero_inact (m + 1) m (by omega) F).2.1
    have hsub : (Finset.univ.filter fun v : Fin (m + 1) => 0 < F.val.2.2 v) ⊆ Finset.univ.erase (0 : Fin (m + 1)) := by
      intro v hv
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h; rw [h] at hv
      have := (Finset.mem_filter.mp hv).2; exact absurd this (by rw [show (0 : Fin (m + 1)) = ⟨0, by omega⟩ from rfl, h0]; omega)
    have hcard_er : (Finset.univ.erase (0 : Fin (m + 1))).card = m := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]; omega
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [F.prop.2, hcard_er])
    have hi_mem : i.succ ∈ Finset.univ.erase (0 : Fin (m + 1)) :=
      Finset.mem_erase.mpr ⟨Fin.succ_ne_zero i, Finset.mem_univ _⟩
    rw [← heq] at hi_mem
    exact (Finset.mem_filter.mp hi_mem).2
  let liftEdge : DirEdge m → DirEdge (m + 1) := fun e => ⟨(e.val.1.succ, e.val.2.succ), Fin.succ_lt_succ_iff.mpr e.prop⟩
  have hsum_out_succ : ∀ (f : DirEdge (m + 1) → ℕ) (i : Fin m),
      (∑ e ∈ Finset.univ.filter (fun e : DirEdge (m + 1) => e.val.1 = i.succ), f e) =
      ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.1 = i), f (liftEdge e) := fun f i => by
    symm
    refine Finset.sum_bij (fun e _ => liftEdge e) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro e he; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Fin.succ (Finset.mem_filter.mp he).2⟩
    · intro a _ b _ h
      exact Subtype.ext (Prod.ext (Fin.succ_injective _ (congrArg (fun x : DirEdge (m + 1) => x.val.1) h))
        (Fin.succ_injective _ (congrArg (fun x : DirEdge (m + 1) => x.val.2) h)))
    · intro e he
      have h1 := (Finset.mem_filter.mp he).2
      have h2pos : 0 < e.val.2.val := by have : i.succ.val < e.val.2.val := h1 ▸ e.prop; omega
      let j : Fin m := ⟨e.val.2.val - 1, by omega⟩
      have hj : j.succ = e.val.2 := Fin.ext (by dsimp [j]; omega)
      have hij : i < j := Fin.succ_lt_succ_iff.mp (by rw [← h1, hj]; exact e.prop)
      refine ⟨⟨(i, j), hij⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, Subtype.ext (Prod.ext h1.symm hj)⟩
  have hsum_in_succ : ∀ (f : DirEdge (m + 1) → ℕ) (hf0 : ∀ e : DirEdge (m + 1), e.val.1 = 0 → f e = 0) (i : Fin m),
      (∑ e ∈ Finset.univ.filter (fun e : DirEdge (m + 1) => e.val.2 = i.succ), f e) =
      ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.2 = i), f (liftEdge e) := fun f hf0 i => by
    let e0 : DirEdge (m + 1) := ⟨(0, i.succ), Fin.succ_pos i⟩
    have he0_mem : e0 ∈ Finset.univ.filter (fun e : DirEdge (m + 1) => e.val.2 = i.succ) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    rw [← Finset.add_sum_erase _ _ he0_mem, hf0 e0 rfl, zero_add]
    symm
    refine Finset.sum_bij (fun e _ => liftEdge e) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro e he
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Fin.succ (Finset.mem_filter.mp he).2⟩⟩
      intro h; exact Fin.succ_ne_zero e.val.1 (congrArg (fun x : DirEdge (m + 1) => x.val.1) h)
    · intro a _ b _ h
      exact Subtype.ext (Prod.ext (Fin.succ_injective _ (congrArg (fun x : DirEdge (m + 1) => x.val.1) h))
        (Fin.succ_injective _ (congrArg (fun x : DirEdge (m + 1) => x.val.2) h)))
    · intro e he
      have hne0 : e ≠ e0 := (Finset.mem_erase.mp he).1
      have h2 := (Finset.mem_filter.mp (Finset.mem_erase.mp he).2).2
      have h1ne0 : e.val.1 ≠ 0 := fun h => hne0 (Subtype.ext (Prod.ext h h2))
      have h1pos : 0 < e.val.1.val := Nat.pos_of_ne_zero (fun h => h1ne0 (Fin.ext h))
      let h : Fin m := ⟨e.val.1.val - 1, by have := e.val.1.isLt; have := e.prop; omega⟩
      have hh : h.succ = e.val.1 := Fin.ext (by dsimp [h]; omega)
      have hhi : h < i := Fin.succ_lt_succ_iff.mp (by rw [hh, ← h2]; exact e.prop)
      refine ⟨⟨(h, i), hhi⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, Subtype.ext (Prod.ext hh h2.symm)⟩
  refine
    { toFun := fun F =>
        let f' : DirEdge m → ℕ := fun e => F.val.1 (liftEdge e)
        let b' : Fin m → ℕ := fun i => F.val.2.1 i.succ
        let r' : Fin m → ℕ := fun i => F.val.2.2 i.succ - 1
        have hcons : ∀ i : Fin m,
            b' i + r' i + ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.1 = i), f' e =
            i.val + ∑ e ∈ Finset.univ.filter (fun e : DirEdge m => e.val.2 = i), f' e := fun i => by
          have hF := F.prop.1 i.succ
          have hf0 := (hzero_inact (m + 1) m (by omega) F).2.2
          rw [hsum_out_succ, hsum_in_succ _ hf0] at hF
          have hpos := hsucc_pos F i
          simp only [Fin.val_succ] at hF
          dsimp only [b', r', f']; omega
        have hklt : (Finset.univ.filter fun i : Fin m => 0 < r' i).card < m := by
          have h0inact : (⟨0, hm⟩ : Fin m) ∉ Finset.univ.filter (fun i : Fin m => 0 < r' i) := by
            have hF0 := hcons ⟨0, hm⟩
            have hnoin : (Finset.univ.filter fun e : DirEdge m => e.val.2 = ⟨0, hm⟩) = ∅ := by
              ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
              intro h; have := e.prop; rw [h] at this; exact Nat.not_lt_zero _ this
            rw [hnoin, Finset.sum_empty] at hF0; dsimp only at hF0
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
          calc (Finset.univ.filter fun i : Fin m => 0 < r' i).card
              < (Finset.univ : Finset (Fin m)).card :=
                Finset.card_lt_card (Finset.ssubset_univ_iff.mpr fun h => by rw [h] at h0inact; exact h0inact (Finset.mem_univ _))
            _ = m := Finset.card_fin m
        ⟨⟨(Finset.univ.filter fun i : Fin m => 0 < r' i).card, hklt⟩,
         ⟨(f', b', r'), hcons, rfl⟩⟩
      invFun := fun ⟨k, F'⟩ =>
        let f : DirEdge (m + 1) → ℕ := fun e =>
          if h : e.val.1.val = 0 then 0
          else F'.val.1 ⟨(⟨e.val.1.val - 1, by have := e.prop; omega⟩,
                          ⟨e.val.2.val - 1, by have := e.val.2.isLt; omega⟩), by
            show e.val.1.val - 1 < e.val.2.val - 1; have : e.val.1.val < e.val.2.val := e.prop; omega⟩
        let b : Fin (m + 1) → ℕ := Fin.cases 0 F'.val.2.1
        let r : Fin (m + 1) → ℕ := Fin.cases 0 (fun i => F'.val.2.2 i + 1)
        have hf0 : ∀ e : DirEdge (m + 1), e.val.1 = 0 → f e = 0 := fun e he => by
          simp [f, he]
        have hflift : ∀ e : DirEdge m, f (liftEdge e) = F'.val.1 e := fun e => by
          simp only [f, liftEdge, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
            Nat.add_sub_cancel, Fin.eta]
        have hcons : ∀ v : Fin (m + 1),
            b v + r v + ∑ e ∈ Finset.univ.filter (fun e : DirEdge (m + 1) => e.val.1 = v), f e =
            v.val + ∑ e ∈ Finset.univ.filter (fun e : DirEdge (m + 1) => e.val.2 = v), f e := fun v => by
          refine Fin.cases ?_ (fun i => ?_) v
          · have hnoin : (Finset.univ.filter fun e : DirEdge (m + 1) => e.val.2 = 0) = ∅ := by
              ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
              intro h; have := e.prop; rw [h] at this; exact Nat.not_lt_zero _ this
            have hout0 : ∑ e ∈ Finset.univ.filter (fun e : DirEdge (m + 1) => e.val.1 = 0), f e = 0 :=
              Finset.sum_eq_zero fun e he => hf0 e (Finset.mem_filter.mp he).2
            rw [hnoin, Finset.sum_empty, hout0]; simp [b, r]
          · rw [hsum_out_succ, hsum_in_succ _ hf0]
            simp only [b, r, Fin.cases_succ, hflift, Fin.val_succ]
            have hF := F'.prop.1 i; omega
        have hact : (Finset.univ.filter fun v : Fin (m + 1) => 0 < r v).card = m := by
          have heq : (Finset.univ.filter fun v : Fin (m + 1) => 0 < r v) = Finset.univ.erase (0 : Fin (m + 1)) := by
            ext v; refine Fin.cases ?_ (fun i => ?_) v <;> simp [r]
          rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]; omega
        ⟨(f, b, r), hcons, hact⟩
      left_inv := fun F => by
        apply Subtype.ext; apply Prod.ext
        · funext e; dsimp only
          by_cases h0 : e.val.1.val = 0
          · rw [dif_pos h0]
            exact ((hzero_inact (m + 1) m (by omega) F).2.2 e (Fin.ext h0)).symm
          · rw [dif_neg h0]
            exact congrArg F.val.1 (Subtype.ext (Prod.ext
              (Fin.ext (by dsimp [liftEdge]; omega))
              (Fin.ext (by dsimp [liftEdge]; have : e.val.1.val < e.val.2.val := e.prop; omega))))
        · apply Prod.ext
          · funext v; refine Fin.cases ?_ (fun i => ?_) v
            · exact ((hzero_inact (m + 1) m (by omega) F).1).symm
            · rfl
          · funext v; refine Fin.cases ?_ (fun i => ?_) v
            · exact ((hzero_inact (m + 1) m (by omega) F).2.1).symm
            · dsimp only [Fin.cases_succ]; have := hsucc_pos F i; omega
      right_inv := fun ⟨k, F'⟩ => by
        dsimp only
        have hsigma : ∀ {k₁ k₂ : Fin m} {a : TwoExitFlow m k₁.val} {b : TwoExitFlow m k₂.val},
            k₁ = k₂ → a.val = b.val → (⟨k₁, a⟩ : Σ k : Fin m, TwoExitFlow m k.val) = ⟨k₂, b⟩ := by
          rintro k₁ _ a b rfl hab; exact congrArg (Sigma.mk k₁) (Subtype.ext hab)
        refine hsigma ?_ ?_
        · apply Fin.ext; dsimp only [Fin.cases_succ]
          refine Eq.trans ?_ F'.prop.2
          congr 1
        · apply Prod.ext
          · funext e
            simp only [liftEdge, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
              Nat.add_sub_cancel, Fin.eta]
          · apply Prod.ext rfl; funext i; simp }

private lemma completeFlow_card_eq_catalan_prod (m : ℕ) (hm : 1 ≤ m) :
    Nat.card (GraphFlow (completeEdges m)) = ∏ j ∈ Finset.Ico 1 m, catalanNum j := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      simp only [Finset.Ico_self, Finset.prod_empty]
      have hemp : completeEdges 1 = [] := by decide
      rw [hemp]
      let htree : RedTree 1 ([] : List (DirEdge 1)) := RedTree.leaf [] (fun _ h => by cases h)
      exact (redTree_leaves_eq_card htree).symm
    | succ m =>
      have hm1 : 1 ≤ m + 1 := by omega
      have hih := ih hm1
      -- `u_{m+2} = a_{m+2, m+1} = ∑_{k=0}^m a_{m+1, k} = C_{m+1} * u_{m+1}`!
      have htop : Nat.card (TwoExitFlow (m + 2) (m + 1)) = Nat.card (GraphFlow (completeEdges (m + 2))) := by
        have hnar := narayana_formula (m + 2) (m + 1) (by omega) (by omega)
        have hch : Nat.choose (m + 2) (m + 1) = m + 2 := by
          rw [← Nat.choose_symm (by omega : m + 1 ≤ m + 2), show m + 2 - (m + 1) = 1 by omega, Nat.choose_one_right]
        rw [Nat.choose_self, mul_one, hch] at hnar
        apply Nat.eq_of_mul_eq_mul_left (show 0 < m + 2 by omega)
        linarith
      have hdel : Nat.card (TwoExitFlow (m + 2) (m + 1)) =
          ∑ k ∈ Finset.range (m + 1), Nat.card (TwoExitFlow (m + 1) k) := by
        let _ := twoExitFlow_finite (m + 2) (m + 1)
        let _ : Fintype (TwoExitFlow (m + 2) (m + 1)) := Fintype.ofFinite _
        let _ : ∀ k : Fin (m + 1), Fintype (TwoExitFlow (m + 1) k.val) := fun k =>
          @Fintype.ofFinite _ (twoExitFlow_finite (m + 1) k.val)
        rw [Nat.card_eq_fintype_card, Fintype.card_congr (deletionEquiv (m + 1) hm1), Fintype.card_sigma]
        rw [← Fin.sum_univ_eq_sum_range (fun k => Nat.card (TwoExitFlow (m + 1) k))]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact (Nat.card_eq_fintype_card).symm
      rw [← htop, hdel, row_sum_eq_catalan_mul (m + 1) hm1, hih,
          Finset.prod_Ico_succ_top (by omega : 1 ≤ m + 1), mul_comm]

theorem main_proof : type_of% @OMA.S_arxiv_2610_19119.main := by
  refine ⟨fun m G => ⟨graphFlow_finite G, redTree_exists G, fun T => redTree_leaves_eq_card T⟩,
    fun m k hk1 hkm => ⟨marked_pair_bijection m k hk1 hkm, morales_shi_recurrence m k hk1 hkm⟩,
    fun m k hm hkm => narayana_formula m k hm hkm,
    fun m hm => ⟨deletionEquiv m hm⟩,
    fun m hm => ⟨completeFlow_card_eq_catalan_prod m hm, fun T =>
      (redTree_leaves_eq_card T).trans (completeFlow_card_eq_catalan_prod m hm)⟩⟩

end OMA.P_arxiv_2610_19119

theorem OMA.solution : type_of% @OMA.S_arxiv_2610_19119.main :=
  OMA.P_arxiv_2610_19119.main_proof


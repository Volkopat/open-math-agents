import FormalConjectures.ErdosProblems.«743»

/-!
Reduction of Janzer and Montgomery, *Packing the largest trees in the tree packing
conjecture* (arXiv:2403.10515). The two inputs concern the few-leaf trees in
Theorem 2.1 and a single many-leaf tree as used in Section 5, respectively.
-/

namespace OMA.R_Erdos743_erdos_743_variants_largest_trees_R1

open Filter SimpleGraph
open scoped Classical

/-- Embed the few-leaf trees while reserving sufficiently many rightward neighbours
at distinct centres for the omitted orders. This is the information from Theorem 2.1
used here. The graph left after placing just the few-leaf trees is denoted by G. -/
def H1 : Prop :=
  ∃ L D : ℕ, 2 ≤ L ∧ 0 < D ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, D * r ≤ n →
    ∀ P B : Finset ℕ, Disjoint P B →
    (∀ k ∈ P ∪ B, 2 ≤ k ∧ k ≤ n ∧ n < k + r) →
    ∀ T : (k : ℕ) → SimpleGraph (Fin k),
    (∀ k ∈ P, (T k).IsTree ∧
      (Finset.univ.filter (fun v => (T k).degree v = 1)).card ≤ n / L) →
    ∃ (F : ℕ → SimpleGraph (Fin n)) (C : ℕ → Fin n),
      (∀ k ∈ P, ∃ f : Fin k ↪ Fin n, F k = (T k).map f) ∧
      (P : Set ℕ).Pairwise (fun i j => Disjoint (F i) (F j)) ∧
      Set.InjOn C (B : Set ℕ) ∧
      let G := (P.sup F)ᶜ
      (∀ v, n / 5 ≤ (G.neighborSet v).ncard) ∧
      ∀ i ∈ B, i - 1 ≤ (Finset.univ.filter (fun v => G.Adj (C i) v ∧ C i < v)).card

/-- Single-tree embedding used by Claim 5.3. The current reserve has vertex set A
and centre u. W consists of future centres. If too few edges remain at u to reuse it,
each new edge at a marked vertex must join that vertex to u. -/
def H2 : Prop :=
  ∀ L : ℕ, 2 ≤ L → ∃ D : ℕ, 0 < D ∧ ∀ᶠ n : ℕ in atTop, ∀ r k : ℕ,
    D * r ≤ n → 2 ≤ k → k ≤ n → n < k + r → ∀ T : SimpleGraph (Fin k), T.IsTree →
    n / L < (Finset.univ.filter (fun v => T.degree v = 1)).card →
    ∀ (G : SimpleGraph (Fin n)) (u : Fin n) (A W : Finset (Fin n)),
    Gᶜ.edgeSet.ncard ≤ r * n → A.card = k → u ∈ A →
    (∀ v ∈ A, v ≠ u → G.Adj u v) → (∀ v ∈ A, n / 8 ≤ (G.neighborSet v).ncard) →
    W.card ≤ r → u ∉ W → (∀ w ∈ W, n - r ≤ (G.neighborSet w).ncard) →
    ∃ f : Fin k ↪ Fin n, let U := T.map f
      (∀ x, f x ∈ A) ∧ U ≤ G ∧
      (∀ w ∈ W, ∀ x y, U.Adj w x → U.Adj w y → x = y) ∧
      (∀ v ≠ u, min ((G.neighborSet v).ncard - 1) (n / 5) ≤ ((G \ U).neighborSet v).ncard) ∧
      (n / 5 ≤ ((G \ U).neighborSet u).ncard ∨ ∀ w ∈ W, ∀ x, U.Adj w x → x = u)

/-- If an edge out of a future centre c is consumed, replace that leaf by the
current centre u. The new edge is free since c has at most one neighbour in U. -/
lemma reroute {V : Type*} [Fintype V] [DecidableEq V] (G U : SimpleGraph V)
    (u c : V) (F : Finset V) (q : ℕ) (hu : u ∉ F) (hF : ∀ x ∈ F, G.Adj c x)
    (hlink : ∀ x ∈ F, U.Adj c x → G.Adj c u)
    (huniq : ∀ x y, U.Adj c x → U.Adj c y → x = y)
    (hsafe : q ≤ ((G \ U).neighborSet u).ncard ∨ ∀ x, U.Adj c x → x = u) :
    ∃ F' : Finset V, F'.card = F.card ∧ F' ⊆ insert u F ∧
      (∀ x ∈ F', (G \ U).Adj c x) ∧ (u ∈ F' → q ≤ ((G \ U).neighborSet u).ncard) := by
  classical
  by_cases h : ∃ z ∈ F, U.Adj c z
  · obtain ⟨z, hz, he⟩ := h
    have hzu : z ≠ u := fun heq => hu (heq ▸ hz)
    refine ⟨insert u (F.erase z), ?_, Finset.insert_subset_insert _ (Finset.erase_subset ..),
      ?_, fun _ => hsafe.resolve_right (fun hall => hzu (hall z he))⟩
    · rw [Finset.card_insert_of_notMem (fun hmem => hu (Finset.mem_of_mem_erase hmem)),
        Finset.card_erase_add_one hz]
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨hlink z hz he, fun h' => hzu (huniq z _ he h')⟩
      · exact ⟨hF x (Finset.mem_of_mem_erase hx), fun h' =>
          (Finset.mem_erase.mp hx).1 (huniq x z h' he)⟩
  · exact ⟨F, rfl, Finset.subset_insert .., fun x hx => ⟨hF x hx, fun he => h ⟨x, hx, he⟩⟩,
      fun hx => (hu hx).elim⟩

lemma card_used_le {n : ℕ} (s : Finset ℕ) (F : ℕ → SimpleGraph (Fin n))
    (h : ∀ i ∈ s, (F i).edgeSet.ncard ≤ n) :
    (s.sup F).edgeSet.ncard ≤ s.card * n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sup_insert, SimpleGraph.edgeSet_sup, Finset.card_insert_of_notMem hi, Nat.add_mul]
    have h₁ := h i (Finset.mem_insert_self ..)
    have h₂ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    calc
      _ ≤ _ := Set.ncard_union_le _ _
      _ ≤ _ := by omega

lemma card_tree_image_le {k n : ℕ} {T : SimpleGraph (Fin k)} (ht : T.IsTree)
    (hkn : k ≤ n) (f : Fin k ↪ Fin n) : (T.map f).edgeSet.ncard ≤ n := by
  classical
  rw [SimpleGraph.edgeSet_map]
  apply (Set.ncard_image_le (Set.toFinite _)).trans
  have he := ht.card_edgeFinset
  rw [Fintype.card_fin] at he
  rw [Set.ncard_eq_toFinset_card']
  change T.edgeFinset.card ≤ n
  omega

lemma card_missing_after {n : ℕ} (G U : SimpleGraph (Fin n)) :
    (G \ U)ᶜ.edgeSet.ncard ≤ Gᶜ.edgeSet.ncard + U.edgeSet.ncard := by
  classical
  rw [sdiff_eq, compl_inf, compl_compl, SimpleGraph.edgeSet_sup]
  exact Set.ncard_union_le _ _

set_option maxHeartbeats 1800000 in
/-- Inductively replace ordered star reserves by their original trees. The variable t
counts replacements already made. Removing the next tree costs at most n edges and
reduces the guaranteed degree of each surviving reserve vertex by at most one. -/
lemma replace_reserves {n r : ℕ} (hr : 100 * r ≤ n) (B : Finset ℕ)
    (C : ℕ → Fin n) (hc : Set.InjOn C (B : Set ℕ))
    (T : (k : ℕ) → SimpleGraph (Fin k))
    (hT : ∀ i ∈ B, (T i).IsTree ∧ 2 ≤ i ∧ i ≤ n ∧ n < i + r)
    (place : ∀ i ∈ B, ∀ (G : SimpleGraph (Fin n)) (A W : Finset (Fin n)),
      Gᶜ.edgeSet.ncard ≤ r * n → A.card = i → C i ∈ A →
      (∀ v ∈ A, v ≠ C i → G.Adj (C i) v) → (∀ v ∈ A, n / 8 ≤ (G.neighborSet v).ncard) →
      W.card ≤ r → C i ∉ W → (∀ w ∈ W, n - r ≤ (G.neighborSet w).ncard) →
      ∃ f : Fin i ↪ Fin n, let U := (T i).map f
        (∀ x, f x ∈ A) ∧ U ≤ G ∧
        (∀ w ∈ W, ∀ x y, U.Adj w x → U.Adj w y → x = y) ∧
        (∀ v ≠ C i, min ((G.neighborSet v).ncard - 1) (n / 5) ≤ ((G \ U).neighborSet v).ncard) ∧
        (n / 5 ≤ ((G \ U).neighborSet (C i)).ncard ∨ ∀ w ∈ W, ∀ x, U.Adj w x → x = C i))
    (s : Finset ℕ) (hs : s ⊆ B) (G : SimpleGraph (Fin n)) (t : ℕ)
    (ht : t + s.card ≤ r) (hd : Gᶜ.edgeSet.ncard + s.card * n ≤ r * n)
    (reserve : ∀ i ∈ s, ∃ A : Finset (Fin n), A.card = i - 1 ∧
      (∀ v ∈ A, G.Adj (C i) v) ∧ (∀ j ∈ s, C j ≤ C i → C j ∉ A) ∧
      (∀ v ∈ insert (C i) A, n / 5 ≤ (G.neighborSet v).ncard + t)) :
    ∃ F : ℕ → SimpleGraph (Fin n),
      (∀ k ∈ s, (∃ f : Fin k ↪ Fin n, F k = (T k).map f) ∧ F k ≤ G) ∧
      (s : Set ℕ).Pairwise (fun i j => Disjoint (F i) (F j)) := by
  classical
  induction s using Finset.strongInductionOn generalizing G t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => ⊥, by simp, by simp⟩
    obtain ⟨i, hi, hmin⟩ := s.exists_min_image C hne
    let s' := s.erase i
    have hcard : s'.card + 1 = s.card := Finset.card_erase_add_one hi
    have hsub : s' ⊆ s := Finset.erase_subset ..
    have hCi (j : ℕ) (hj : j ∈ s') : C j ≠ C i :=
      fun he => (Finset.mem_erase.mp hj).1 (hc (hs (hsub hj)) (hs hi) he)
    let W := s'.image C
    obtain ⟨A, hsize, ha, hord, hgood⟩ := reserve i hi
    have hown : C i ∉ A := hord i hi le_rfl
    have hsize' : (insert (C i) A).card = i := by
      rw [Finset.card_insert_of_notMem hown, hsize]
      have := (hT i (hs hi)).2.1
      omega
    have hW : ∀ w ∈ W, n - r ≤ (G.neighborSet w).ncard := by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨A', hsz, ha', _, _⟩ := reserve j (hsub hj)
      have hh : (A' : Set (Fin n)) ⊆ G.neighborSet (C j) := fun x hx => ha' x hx
      have hbound := Set.ncard_le_ncard hh
      rw [Set.ncard_coe_finset, hsz] at hbound
      have := (hT j (hs (hsub hj))).2.2.2
      omega
    obtain ⟨f, hf, hle, huniq, hdeg, hcenter⟩ :=
      place i (hs hi) G (insert (C i) A) W (by omega) hsize' (Finset.mem_insert_self ..)
        (fun v hv hvne => ha v ((Finset.mem_insert.mp hv).resolve_left hvne))
        (fun v hv => by have := hgood v hv; omega)
        (Finset.card_image_le.trans (by omega)) (by
          intro hw
          obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hw
          exact hCi j hj heq) hW
    let U := (T i).map f
    have nextReserve : ∀ j ∈ s', ∃ A' : Finset (Fin n), A'.card = j - 1 ∧
        (∀ v ∈ A', (G \ U).Adj (C j) v) ∧ (∀ k ∈ s', C k ≤ C j → C k ∉ A') ∧
        (∀ v ∈ insert (C j) A', n / 5 ≤ ((G \ U).neighborSet v).ncard + (t + 1)) := by
      intro j hj
      obtain ⟨P, hp, hP, ho, hg⟩ := reserve j (hsub hj)
      have huP := ho i hi (hmin j (hsub hj))
      have hw : C j ∈ W := Finset.mem_image_of_mem C hj
      have link : ∀ x ∈ P, U.Adj (C j) x → G.Adj (C j) (C i) := by
        intro x _ hx
        obtain ⟨y, z, _, hy, _⟩ := (SimpleGraph.map_adj f _ ..).mp hx
        have hmem := hy ▸ hf y
        exact (ha _ ((Finset.mem_insert.mp hmem).resolve_left (hCi j hj))).symm
      obtain ⟨P', hcard', hsub', hP', hsafe⟩ :=
        reroute G U (C i) (C j) P (n / 5) huP hP link (huniq _ hw)
          (hcenter.imp_right (fun H => H _ hw))
      refine ⟨P', hcard'.trans hp, hP', ?_, ?_⟩
      · intro k hk hkj hmem
        exact (Finset.mem_insert.mp (hsub' hmem)).elim (hCi k hk) (ho k (hsub hk) hkj)
      · intro v hv
        by_cases he : v = C i
        · subst v
          have hh := hsafe ((Finset.mem_insert.mp hv).resolve_left (Ne.symm (hCi j hj)))
          omega
        · have hvold : v ∈ insert (C j) P := by
            rcases Finset.mem_insert.mp hv with h | h
            · exact Finset.mem_insert.mpr (.inl h)
            · exact Finset.mem_insert_of_mem ((Finset.mem_insert.mp (hsub' h)).resolve_left he)
          have h₁ := hg v hvold
          have h₂ := hdeg v he
          change min ((G.neighborSet v).ncard - 1) (n / 5) ≤ ((G \ U).neighborSet v).ncard at h₂
          omega
    have edges := card_missing_after G U
    have cost := card_tree_image_le (hT i (hs hi)).1 (hT i (hs hi)).2.2.1 f
    change U.edgeSet.ncard ≤ n at cost
    have hd' : (G \ U)ᶜ.edgeSet.ncard + s'.card * n ≤ r * n := by
      rw [← hcard, Nat.add_mul, one_mul] at hd
      omega
    obtain ⟨F, hF, hdis⟩ := ih s' (Finset.erase_ssubset hi) (hsub.trans hs)
      (G \ U) (t + 1) (by omega) hd' nextReserve
    let F' := Function.update F i U
    have hnew : F' i = U := Function.update_self ..
    have hold {j : ℕ} (hj : j ≠ i) : F' j = F j := Function.update_of_ne hj ..
    refine ⟨F', ?_, ?_⟩
    · intro k hk
      by_cases he : k = i
      · subst k
        exact ⟨⟨f, hnew⟩, hnew ▸ hle⟩
      · rw [hold he]
        have hh := hF k (Finset.mem_erase.mpr ⟨he, hk⟩)
        exact ⟨hh.1, hh.2.trans sdiff_le⟩
    · intro j hj k hk hjk
      by_cases hji : j = i
      · subst j
        rw [hnew, hold hjk.symm]
        exact disjoint_sdiff_self_right.mono_right (hF k (Finset.mem_erase.mpr ⟨hjk.symm, hk⟩)).2
      by_cases hki : k = i
      · subst k
        rw [hnew, hold hji]
        exact disjoint_sdiff_self_left.mono_left (hF j (Finset.mem_erase.mpr ⟨hji, hj⟩)).2
      rw [hold hji, hold hki]
      exact hdis (Finset.mem_erase.mpr ⟨hji, hj⟩) (Finset.mem_erase.mpr ⟨hki, hk⟩) hjk

/-- Combine copies packed in a leftover graph with the copies whose union it complements. -/
lemma assemble {n : ℕ} {S : Set ℕ} {P B : Finset ℕ}
    (hcover : ∀ i ∈ S, i ∈ P ∨ i ∈ B)
    (T : (k : ℕ) → SimpleGraph (Fin k)) (F H : ℕ → SimpleGraph (Fin n))
    (hF : ∀ i ∈ P, ∃ f : Fin i ↪ Fin n, F i = (T i).map f)
    (hp : (P : Set ℕ).Pairwise (fun i j => Disjoint (F i) (F j)))
    (hH : ∀ i ∈ B, (∃ f : Fin i ↪ Fin n, H i = (T i).map f) ∧ H i ≤ (P.sup F)ᶜ)
    (hb : (B : Set ℕ).Pairwise (fun i j => Disjoint (H i) (H j))) :
    Erdos743.IsPacking n S T := by
  classical
  let Q := fun i => if i ∈ P then F i else H i
  have copies (i : S) : ∃ f : Fin i.val ↪ Fin n, Q i = (T i).map f := by
    by_cases hi : i.val ∈ P
    · simpa [Q, hi] using hF i hi
    · simpa [Q, hi] using (hH i ((hcover i i.property).resolve_left hi)).1
  choose f hf using copies
  refine ⟨fun i => f i, fun i => (f i).injective, ?_⟩
  intro i j hij
  rw [← hf i, ← hf j, SimpleGraph.disjoint_edgeSet]
  have hcross {a b : ℕ} (ha : a ∈ P) (hb' : b ∈ B) : Disjoint (F a) (H b) :=
    (disjoint_compl_right (a := P.sup F)).mono (Finset.le_sup ha) (hH b hb').2
  by_cases hi : i.val ∈ P <;> by_cases hj : j.val ∈ P
  · simpa [Q, hi, hj] using hp hi hj hij.ne
  · simpa [Q, hi, hj] using hcross hi ((hcover j j.property).resolve_left hj)
  · simpa [Q, hi, hj] using (hcross hj ((hcover i i.property).resolve_left hi)).symm
  · simpa [Q, hi, hj] using
      hb ((hcover i i.property).resolve_left hi) ((hcover j j.property).resolve_left hj) hij.ne

lemma real_cutoff {D n k : ℕ} (hD : 0 < D) (hn : 2 * D ≤ n) (hk : k ≤ n)
    (h : (n : ℝ) - 1 / (2 * (D : ℝ)) * n < k) :
    n < k + n / D := by
  have hpos : 0 < 2 * (D : ℝ) := by positivity
  have hs : ((n - k : ℕ) : ℝ) < (n : ℝ) / (2 * (D : ℝ)) := by
    rw [Nat.cast_sub hk]
    rw [div_mul_eq_mul_div, one_mul] at h
    linarith
  have hm : (n - k) * (2 * D) < n := by exact_mod_cast (lt_div_iff₀ hpos).mp hs
  rw [two_mul, Nat.mul_add] at hm
  have : n - k + 1 ≤ n / D := (Nat.le_div_iff_mul_le hD).2 (by rw [Nat.add_mul, one_mul]; omega)
  omega

set_option maxHeartbeats 1200000 in
theorem main : H1 → H2 → type_of% @Erdos743.erdos_743.variants.largest_trees := by
  classical
  rintro ⟨L, D₁, hL, _, h₁⟩ h₂
  obtain ⟨D₂, _, h₂⟩ := h₂ L hL
  let D := max 100 (max D₁ D₂)
  have h₁D : D₁ ≤ D := (le_max_left ..).trans (le_max_right ..)
  have h₂D : D₂ ≤ D := (le_max_right ..).trans (le_max_right ..)
  have h₀D : 100 ≤ D := le_max_left ..
  have hD : 0 < D := by omega
  refine ⟨1 / (2 * (D : ℝ)), by positivity, ?_⟩
  filter_upwards [h₁, h₂, eventually_ge_atTop (2 * D)] with n low high hn
  intro T hT
  let r := n / D
  have hprod : D * r ≤ n := by simpa [r, Nat.mul_comm] using Nat.div_mul_le_self n D
  let S : Finset ℕ := (Finset.Icc 2 n).filter (fun (k : ℕ) => (n : ℝ) - 1 / (2 * (D : ℝ)) * n < k)
  have hS {k : ℕ} : k ∈ S ↔ 2 ≤ k ∧ k ≤ n ∧ (n : ℝ) - 1 / (2 * (D : ℝ)) * n < k := by
    simp [S, and_assoc]
  have hsizes (k : ℕ) (hk : k ∈ S) : 2 ≤ k ∧ k ≤ n ∧ n < k + r :=
    ⟨(hS.mp hk).1, (hS.mp hk).2.1, real_cutoff hD hn (hS.mp hk).2.1 (hS.mp hk).2.2⟩
  have htrees (k : ℕ) (hk : k ∈ S) : (T k).IsTree :=
    hT k (hS.mp hk).1 (hS.mp hk).2.1 (hS.mp hk).2.2
  let few := fun k => (Finset.univ.filter (fun v => (T k).degree v = 1)).card ≤ n / L
  let P := S.filter few
  let B := S.filter (fun k => ¬few k)
  have hPB : P ∪ B = S := Finset.filter_union_filter_not_eq ..
  have hsep : Disjoint P B := Finset.disjoint_filter_filter_not ..
  have hcount : P.card + B.card ≤ r := by
    rw [← Finset.card_union_of_disjoint hsep, hPB]
    have hsub : S ⊆ Finset.Ioc (n - r) n := by
      intro k hk
      obtain ⟨_, hkn, hrk⟩ := hsizes k hk
      exact Finset.mem_Ioc.mpr ⟨by have := (hS.mp hk).1; omega, hkn⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at hcard
    exact hcard.trans tsub_tsub_le
  obtain ⟨F, C, hF, hdisF, hinj, hdeg, hright⟩ :=
    low r ((Nat.mul_le_mul_right r h₁D).trans hprod) P B hsep
      (hPB ▸ hsizes) T (fun k hk => ⟨htrees k (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2⟩)
  let G := (P.sup F)ᶜ
  have hB (i : ℕ) (hi : i ∈ B) : (T i).IsTree ∧ 2 ≤ i ∧ i ≤ n ∧ n < i + r :=
    ⟨htrees i (Finset.mem_filter.mp hi).1, hsizes i (Finset.mem_filter.mp hi).1⟩
  have hmissing : Gᶜ.edgeSet.ncard + B.card * n ≤ r * n := by
    have bound := card_used_le P F (fun i hi => by
      obtain ⟨f, hf⟩ := hF i hi
      rw [hf]
      have hmem := (Finset.mem_filter.mp hi).1
      exact card_tree_image_le (htrees i hmem) (hsizes i hmem).2.1 f)
    simpa only [G, compl_compl, Nat.add_mul] using
      (calc (P.sup F).edgeSet.ncard + B.card * n ≤ P.card * n + B.card * n := by omega
            _ ≤ r * n := by simpa only [Nat.add_mul] using Nat.mul_le_mul_right n hcount)
  obtain ⟨H, hH, hdisH⟩ := replace_reserves ((Nat.mul_le_mul_right r h₀D).trans hprod)
    B C hinj T hB (fun i hi G' A W => high r i ((Nat.mul_le_mul_right r h₂D).trans hprod)
      (hB i hi).2.1 (hB i hi).2.2.1 (hB i hi).2.2.2 (T i) (hB i hi).1
      (lt_of_not_ge (Finset.mem_filter.mp hi).2) G' (C i) A W)
    B Finset.Subset.rfl G 0 (by omega) hmissing (by
      intro i hi
      obtain ⟨A, hA, hcard⟩ := Finset.exists_subset_card_eq (hright i hi)
      refine ⟨A, hcard, fun v hv => (Finset.mem_filter.mp (hA hv)).2.1,
        ?_, fun v _ => by simpa only [Nat.add_zero] using hdeg v⟩
      intro j _ hle hmem
      exact (not_lt_of_ge hle) (Finset.mem_filter.mp (hA hmem)).2.2)
  apply assemble (P := P) (B := B) _ T F H hF hdisF hH hdisH
  intro k hk
  apply Finset.mem_union.mp
  rw [hPB]
  exact hS.mpr hk

end OMA.R_Erdos743_erdos_743_variants_largest_trees_R1

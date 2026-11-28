import OMAReductions.R_wp_unfriendly_partition_conjecture_R2
import Mathlib

/-!
Countable graphs with finitely many vertices of infinite degree have unfriendly 2-partitions
(Aharoni, Milner and Prikry, JCTB 50, 1990); own proof via flip energies.

For a finite set D of finite-degree vertices, dl g D is the change in the number of monochromatic
adjacent pairs when the colours on D are flipped. Step 1 (Tychonoff): some colouring h has
dl h D nonnegative for every such D. Step 2: flip h on the finite set B of infinite-degree
vertices with only finitely many opposite neighbours; the flip energies are then bounded below.
Step 3: flip on a set D attaining the minimum. Finite-degree vertices are unfriendly by
minimality; infinite-degree vertices keep infinitely many opposite neighbours.
-/

namespace OMA.AMPH1

open SimpleGraph Classical

variable {V : Type*} (G : SimpleGraph V)

noncomputable def nb (u : V) : Finset V :=
  if h : (G.neighborSet u).Finite then h.toFinset else ∅

lemma mem_nb {u : V} (hu : (G.neighborSet u).Finite) (w : V) : w ∈ nb G u ↔ G.Adj u w := by
  simp [nb, hu]

noncomputable def flp (D : Finset V) (g : V → Bool) : V → Bool := fun x => if x ∈ D then !g x else g x

noncomputable def ind (f : V → Bool) (p : V × V) : ℤ :=
  if G.Adj p.1 p.2 ∧ f p.1 = f p.2 then 1 else 0

noncomputable def en (T : Finset V) (f : V → Bool) : ℤ := ∑ p ∈ T ×ˢ T, ind G f p

noncomputable def cl (D : Finset V) : Finset V := D ∪ D.biUnion (nb G)

noncomputable def dl (g : V → Bool) (D : Finset V) : ℤ :=
  en G (cl G D) (flp D g) - en G (cl G D) g

def Adm (D : Finset V) : Prop := ∀ u ∈ D, (G.neighborSet u).Finite

lemma loc {D T T' : Finset V} (hDT : D ⊆ T) (hN : ∀ x ∈ D, ∀ y, G.Adj x y → y ∈ T)
    (hTT : T ⊆ T') (g : V → Bool) :
    en G T' (flp D g) - en G T' g = en G T (flp D g) - en G T g := by
  unfold en
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset (Finset.product_subset_product hTT hTT)
  rintro ⟨x, y⟩ _ hnp
  simp only [Finset.mem_product] at hnp
  by_cases hxy : G.Adj x y
  · have hx : x ∉ D := fun hx => hnp ⟨hDT hx, hN x hx y hxy⟩
    have hy : y ∉ D := fun hy => hnp ⟨hN y hy x hxy.symm, hDT hy⟩
    simp [ind, flp, hx, hy]
  · simp [ind, hxy]

lemma dl_eq {D T : Finset V} (hD : Adm G D) (hT : cl G D ⊆ T) (g : V → Bool) :
    en G T (flp D g) - en G T g = dl G g D :=
  loc G Finset.subset_union_left
    (fun x hx y hxy => Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨x, hx, (mem_nb G (hD x hx) y).mpr hxy⟩)) hT g

lemma flp_flp (D E : Finset V) (g : V → Bool) : flp D (flp E g) = flp (symmDiff E D) g := by
  funext x
  simp only [flp, Finset.mem_symmDiff]
  by_cases hD : x ∈ D <;> by_cases hE : x ∈ E <;> simp [hD, hE]

lemma adm_symmDiff {D E : Finset V} (hD : Adm G D) (hE : Adm G E) : Adm G (symmDiff E D) :=
  fun u hu => by
    rcases Finset.mem_symmDiff.mp hu with ⟨h, _⟩ | ⟨h, _⟩
    · exact hE u h
    · exact hD u h

lemma cocycle {D E : Finset V} (hD : Adm G D) (hE : Adm G E) (g : V → Bool) :
    dl G (flp E g) D = dl G g (symmDiff E D) - dl G g E := by
  have hsub : cl G (symmDiff E D) ⊆ cl G D ∪ cl G E := by
    intro x hx
    simp only [cl, Finset.mem_union, Finset.mem_biUnion, Finset.mem_symmDiff] at hx ⊢
    rcases hx with (⟨h, _⟩ | ⟨h, _⟩) | ⟨a, (⟨ha, _⟩ | ⟨ha, _⟩), hxa⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr ⟨a, ha, hxa⟩)
    · exact Or.inl (Or.inr ⟨a, ha, hxa⟩)
  have h1 := dl_eq G hD (T := cl G D ∪ cl G E) Finset.subset_union_left (flp E g)
  have h2 := dl_eq G (adm_symmDiff G hD hE) hsub g
  have h3 := dl_eq G hE (T := cl G D ∪ cl G E) Finset.subset_union_right g
  rw [flp_flp] at h1
  linarith

lemma single {u : V} (hu : (G.neighborSet u).Finite) (g : V → Bool) :
    dl G g {u} = 2 * ((((nb G u).filter fun w => g w ≠ g u).card : ℤ) -
      ((nb G u).filter fun w => g w = g u).card) := by
  have huT : u ∈ cl G {u} := Finset.mem_union_left _ (Finset.mem_singleton_self u)
  have hNT : ∀ w, G.Adj u w → w ∈ cl G {u} := fun w hw =>
    Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨u, Finset.mem_singleton_self u, (mem_nb G hu w).mpr hw⟩)
  have hfu : flp {u} g u = !g u := by simp [flp]
  have hfo : ∀ x, x ≠ u → flp {u} g x = g x := fun x hx => by simp [flp, hx]
  obtain ⟨d, hd⟩ : ∃ d : V → V → ℤ, d = fun x y => ind G (flp {u} g) (x, y) - ind G g (x, y) :=
    ⟨_, rfl⟩
  have hsplit : ∀ x y, d x y = (if x = u then d u y else 0) + (if y = u then d x u else 0) := by
    intro x y
    by_cases hx : x = u <;> by_cases hy : y = u
    · subst hx; subst hy; simp [hd, ind]
    · simp [hx, hy]
    · simp [hx, hy]
    · simp [hd, ind, hfo x hx, hfo y hy, hx, hy]
  have hsum : dl G g {u} = ∑ x ∈ cl G {u}, ∑ y ∈ cl G {u}, d x y := by
    unfold dl en
    rw [← Finset.sum_sub_distrib, Finset.sum_product, hd]
  have e : ∀ x ∈ cl G {u}, ∑ y ∈ cl G {u}, d x y =
      (if x = u then ∑ y ∈ cl G {u}, d u y else 0) + d x u := by
    intro x _
    rw [Finset.sum_congr rfl (fun y _ => hsplit x y), Finset.sum_add_distrib,
      Finset.sum_ite_eq' (cl G {u}) u, if_pos huT]
    by_cases hx : x = u <;> simp [hx]
  have hsym : ∀ x, d x u = d u x := fun x => by
    simp only [hd, ind, G.adj_comm x u, @eq_comm _ (flp {u} g x), @eq_comm _ (g x)]
  have hA : ∀ h : V → Bool, ∑ y ∈ cl G {u}, ind G h (u, y) =
      (((nb G u).filter fun w => h w = h u).card : ℤ) := by
    intro h
    simp only [ind]
    rw [Finset.sum_boole]
    congr 2
    ext y
    simp only [Finset.mem_filter, mem_nb G hu]
    constructor
    · rintro ⟨_, ha, he⟩
      exact ⟨ha, he.symm⟩
    · rintro ⟨ha, he⟩
      exact ⟨hNT y ha, ha, he.symm⟩
  have hB : ((nb G u).filter fun w => flp {u} g w = flp {u} g u) =
      (nb G u).filter fun w => g w ≠ g u := by
    apply Finset.filter_congr
    intro w hw
    have hwv : w ≠ u := (G.ne_of_adj ((mem_nb G hu w).mp hw)).symm
    rw [hfo w hwv, hfu]
    cases g w <;> cases g u <;> simp
  have hdu : ∑ y ∈ cl G {u}, d u y =
      ∑ y ∈ cl G {u}, ind G (flp {u} g) (u, y) - ∑ y ∈ cl G {u}, ind G g (u, y) := by
    rw [hd, ← Finset.sum_sub_distrib]
  rw [hsum, Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_ite_eq' (cl G {u}) u,
    if_pos huT, Finset.sum_congr rfl (fun x _ => hsym x), hdu, hA, hA, hB]
  ring

lemma isClosed_of_local (T : Finset V) (P : (V → Bool) → Prop)
    (hP : ∀ f g, (∀ x ∈ T, f x = g x) → P f → P g) : IsClosed {f | P f} := by
  let r : (V → Bool) → (T → Bool) := fun f i => f i
  have hr : Continuous r := continuous_pi fun i => continuous_apply _
  have heq : {f | P f} = r ⁻¹' (r '' {f | P f}) := by
    ext g
    constructor
    · intro hg
      exact ⟨g, hg, rfl⟩
    · rintro ⟨f, hf, hfg⟩
      exact hP f g (fun x hx => congrFun hfg ⟨x, hx⟩) hf
  rw [heq]
  exact (isClosed_discrete _).preimage hr

lemma en_congr (T : Finset V) (f g : V → Bool) (h : ∀ x ∈ T, f x = g x) : en G T f = en G T g := by
  unfold en
  apply Finset.sum_congr rfl
  rintro ⟨x, y⟩ hp
  rw [Finset.mem_product] at hp
  simp only [ind, h x hp.1, h y hp.2]

lemma dl_congr (D : Finset V) (f g : V → Bool) (h : ∀ x ∈ cl G D, f x = g x) :
    dl G f D = dl G g D := by
  unfold dl
  rw [en_congr G _ f g h, en_congr G _ (flp D f) (flp D g) (fun x hx => by simp [flp, h x hx])]

lemma ground : ∃ h : V → Bool, ∀ D : Finset V, Adm G D → 0 ≤ dl G h D := by
  obtain ⟨h, -, hh⟩ := (isCompact_univ (X := V → Bool)).inter_iInter_nonempty
    (fun D : Finset V => {g : V → Bool | Adm G D → 0 ≤ dl G g D})
    (fun D => isClosed_of_local (cl G D) (fun g => Adm G D → 0 ≤ dl G g D)
      (fun f g hfg hf hD => by rw [← dl_congr G D f g hfg]; exact hf hD))
    (fun u => by
      obtain ⟨S, hSdef⟩ : ∃ S : Finset V, S = (u.filter (Adm G)).biUnion id := ⟨_, rfl⟩
      have hS : Adm G S := fun x hx => by
        rw [hSdef, Finset.mem_biUnion] at hx
        obtain ⟨D, hD, hxD⟩ := hx
        exact (Finset.mem_filter.mp hD).2 x hxD
      obtain ⟨E, hE, hmin⟩ := S.powerset.exists_min_image (dl G (fun _ => true))
        ⟨∅, Finset.empty_mem_powerset S⟩
      have hES : E ⊆ S := Finset.mem_powerset.mp hE
      have hEA : Adm G E := fun x hx => hS x (hES hx)
      refine ⟨flp E (fun _ => true), Set.mem_univ _, Set.mem_iInter₂.mpr fun D hDu => ?_⟩
      intro hD
      rw [cocycle G hD hEA]
      have hDS : D ⊆ S := fun x hx => by
        rw [hSdef]
        exact Finset.mem_biUnion.mpr ⟨D, Finset.mem_filter.mpr ⟨hDu, hD⟩, hx⟩
      have := hmin (symmDiff E D) (Finset.mem_powerset.mpr (fun x hx => by
        rcases Finset.mem_symmDiff.mp hx with ⟨h, _⟩ | ⟨h, _⟩
        · exact hES h
        · exact hDS h))
      linarith)
  exact ⟨h, fun D hD => Set.mem_iInter.mp hh D hD⟩

lemma mk_eq {v : V} (hv : (G.neighborSet v).Finite) (P : V → Prop) [DecidablePred P] :
    Cardinal.mk {w // G.Adj v w ∧ P w} = (((nb G v).filter P).card : Cardinal) := by
  rw [← Cardinal.mk_coe_finset]
  exact Cardinal.mk_congr (Equiv.subtypeEquivRight (fun w => by simp [mem_nb G hv]))

lemma bterm (A PX PY QX QY R : Prop) [Decidable A] [Decidable PX] [Decidable PY] [Decidable QX]
    [Decidable QY] [Decidable R] (a b : Bool) (hx : PX → ¬QX) (hy : PY → ¬QY)
    (hR : R ↔ A ∧ a ≠ b ∧ (PX ∨ PY)) :
    -(2 * (if R then (1 : ℤ) else 0)) ≤
      ((if A ∧ (if QX then !(if PX then !a else a) else (if PX then !a else a)) =
          (if QY then !(if PY then !b else b) else (if PY then !b else b)) then (1 : ℤ) else 0) -
        (if A ∧ (if PX then !a else a) = (if PY then !b else b) then (1 : ℤ) else 0)) -
      ((if A ∧ (if QX then !a else a) = (if QY then !b else b) then (1 : ℤ) else 0) -
        (if A ∧ a = b then (1 : ℤ) else 0)) := by
  by_cases hA : A
  · by_cases hPX : PX <;> by_cases hPY : PY <;> by_cases hQX : QX <;> by_cases hQY : QY <;>
      cases a <;> cases b <;> simp_all
  · simp only [hA, false_and, if_false, sub_self]
    split_ifs <;> norm_num

lemma lowbound (h : V → Bool) (hh : ∀ D : Finset V, Adm G D → 0 ≤ dl G h D) (B : Set V)
    (hBI : ∀ b ∈ B, ¬ (G.neighborSet b).Finite) (Q : Set (V × V)) (hQ : Q.Finite)
    (hQdef : ∀ x y, (x, y) ∈ Q ↔ G.Adj x y ∧ h x ≠ h y ∧ (x ∈ B ∨ y ∈ B)) :
    ∀ D, Adm G D → -(2 * (hQ.toFinset.card : ℤ)) ≤
      dl G (fun x => if x ∈ B then !h x else h x) D := by
  intro D hD
  have h0 := hh D hD
  have hterm : ∀ p : V × V, -(2 * (if p ∈ Q then (1 : ℤ) else 0)) ≤
      (ind G (flp D (fun x => if x ∈ B then !h x else h x)) p -
        ind G (fun x => if x ∈ B then !h x else h x) p) - (ind G (flp D h) p - ind G h p) := by
    rintro ⟨x, y⟩
    exact bterm (G.Adj x y) (x ∈ B) (y ∈ B) (x ∈ D) (y ∈ D) ((x, y) ∈ Q) (h x) (h y)
      (fun hx hxD => hBI x hx (hD x hxD)) (fun hy hyD => hBI y hy (hD y hyD)) (hQdef x y)
  have hdiff : dl G (fun x => if x ∈ B then !h x else h x) D - dl G h D =
      ∑ p ∈ cl G D ×ˢ cl G D, ((ind G (flp D (fun x => if x ∈ B then !h x else h x)) p -
        ind G (fun x => if x ∈ B then !h x else h x) p) - (ind G (flp D h) p - ind G h p)) := by
    unfold dl en
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hs1 := Finset.sum_le_sum (s := cl G D ×ˢ cl G D) (fun p _ => hterm p)
  have hs2 : ∑ p ∈ cl G D ×ˢ cl G D, (if p ∈ Q then (1 : ℤ) else 0) ≤ hQ.toFinset.card := by
    rw [Finset.sum_boole]
    exact_mod_cast Finset.card_le_card (fun p hp => by
      rw [Finset.mem_filter] at hp
      exact (Set.Finite.mem_toFinset hQ).mpr hp.2)
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at hs1
  linarith

theorem amp [Countable V] (hI : {v | (G.neighborSet v).Infinite}.Finite) :
    ∃ f : V → Bool, ∀ v : V,
      Cardinal.mk {w // G.Adj v w ∧ f w = f v} ≤ Cardinal.mk {w // G.Adj v w ∧ f w ≠ f v} := by
  obtain ⟨h, hh⟩ := ground G
  obtain ⟨B, hBdef⟩ : ∃ B : Set V, B = {v | (G.neighborSet v).Infinite ∧
      {w | G.Adj v w ∧ h w ≠ h v}.Finite} := ⟨_, rfl⟩
  have hB : B.Finite := hI.subset (fun v hv => by rw [hBdef] at hv; exact hv.1)
  obtain ⟨h', hh'⟩ : ∃ h' : V → Bool, h' = fun x => if x ∈ B then !h x else h x := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Set (V × V),
      Q = {p | G.Adj p.1 p.2 ∧ h p.1 ≠ h p.2 ∧ (p.1 ∈ B ∨ p.2 ∈ B)} := ⟨_, rfl⟩
  have hQ : Q.Finite := by
    have hopp : ∀ b ∈ B, {w | G.Adj b w ∧ h w ≠ h b}.Finite := fun b hb => by
      rw [hBdef] at hb
      exact hb.2
    refine ((hB.biUnion fun b hb => (Set.finite_singleton b).prod (hopp b hb)).union
      (hB.biUnion fun b hb => (hopp b hb).prod (Set.finite_singleton b))).subset ?_
    rintro ⟨x, y⟩ hp
    rw [hQdef] at hp
    obtain ⟨hxy, hne, hx | hy⟩ := hp
    · exact Or.inl (Set.mem_biUnion hx ⟨rfl, hxy, Ne.symm hne⟩)
    · exact Or.inr (Set.mem_biUnion hy ⟨⟨hxy.symm, hne⟩, rfl⟩)
  have hlow := lowbound G h hh B (fun b hb => by rw [hBdef] at hb; exact hb.1) Q hQ
    (fun x y => by rw [hQdef]; exact Iff.rfl)
  rw [← hh'] at hlow
  obtain ⟨m, ⟨D0, hD0, hm0⟩, hm⟩ := Int.exists_least_of_bdd
    (P := fun z => ∃ D, Adm G D ∧ dl G h' D = z)
    ⟨_, fun z ⟨D, hD, hz⟩ => hz ▸ hlow D hD⟩
    ⟨0, ∅, fun _ hx => absurd hx (Finset.notMem_empty _), by
      have e0 : flp ∅ h' = h' := by funext x; simp [flp]
      simp [dl, e0]⟩
  refine ⟨flp D0 h', fun v => ?_⟩
  by_cases hv : (G.neighborSet v).Finite
  · have hvA : Adm G {v} := fun x hx => by rw [Finset.mem_singleton.mp hx]; exact hv
    have h1 := cocycle G hvA hD0 h'
    have h2 := hm _ ⟨symmDiff D0 {v}, adm_symmDiff G hvA hD0, rfl⟩
    rw [single G hv] at h1
    rw [mk_eq G hv, mk_eq G hv]
    have : ((nb G v).filter fun w => flp D0 h' w = flp D0 h' v).card ≤
        ((nb G v).filter fun w => flp D0 h' w ≠ flp D0 h' v).card := by
      have : (((nb G v).filter fun w => flp D0 h' w = flp D0 h' v).card : ℤ) ≤
          ((nb G v).filter fun w => flp D0 h' w ≠ flp D0 h' v).card := by linarith
      exact_mod_cast this
    exact_mod_cast this
  · have hvD : v ∉ D0 := fun hvD => hv (hD0 v hvD)
    have hkv : flp D0 h' v = h' v := by simp [flp, hvD]
    have hkw : ∀ w, w ∉ B → w ∉ D0 → flp D0 h' w = h w := fun w hwB hwD => by
      simp [flp, hwD, hh', hwB]
    have hfin : (B ∪ (D0 : Set V)).Finite := hB.union D0.finite_toSet
    have hinf : {w | G.Adj v w ∧ flp D0 h' w ≠ flp D0 h' v}.Infinite := by
      by_cases hvB : v ∈ B
      · have hof : {w | G.Adj v w ∧ h w ≠ h v}.Finite := by
          rw [hBdef] at hvB
          exact hvB.2
        refine (((Set.not_finite.mp hv).diff hof).diff hfin).mono ?_
        rintro w ⟨⟨hw, hwo⟩, hwBD⟩
        simp only [Set.mem_union, Finset.mem_coe, not_or] at hwBD
        have hwv : h w = h v := by
          by_contra hne
          exact hwo ⟨hw, hne⟩
        refine ⟨hw, ?_⟩
        rw [hkv, hkw w hwBD.1 hwBD.2, hh']
        simp only [hvB, if_true, hwv]
        cases h v <;> simp
      · have hvI : ¬ {w | G.Adj v w ∧ h w ≠ h v}.Finite := fun hf =>
          hvB (by rw [hBdef]; exact ⟨hv, hf⟩)
        refine ((Set.not_finite.mp hvI).diff hfin).mono ?_
        rintro w ⟨⟨hw, hwo⟩, hwBD⟩
        simp only [Set.mem_union, Finset.mem_coe, not_or] at hwBD
        refine ⟨hw, ?_⟩
        rw [hkv, hkw w hwBD.1 hwBD.2, hh']
        simp only [hvB, if_false]
        exact hwo
    have : Infinite {w // G.Adj v w ∧ flp D0 h' w ≠ flp D0 h' v} := hinf.to_subtype
    exact Cardinal.mk_le_aleph0.trans (Cardinal.aleph0_le_mk _)

end OMA.AMPH1

theorem OMA.solution : OMA.R_wp_unfriendly_partition_conjecture_R2.H1 :=
  fun _ _ G _ hI => OMA.AMPH1.amp G hI

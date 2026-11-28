import OMAStatements.S_arxiv_2607_23462
import Mathlib

namespace OMA.P_arxiv_2607_23462

open OMA.S_arxiv_2607_23462

/-- Adjacency predicate for the 18-vertex diamond-free claw-free cubic graph `H` (the truncation
of the 6-vertex cubic multigraph with two parallel-edge lobes joined by a bridge):
triangles are `{0,1,2}`, `{3,4,5}`, `{6,7,8}`, `{9,10,11}`, `{12,13,14}`, `{15,16,17}`,
and inter-triangle edges are `0-3, 1-4, 2-6, 5-7, 8-17, 9-12, 10-13, 11-15, 14-16`. -/
def HAdj (u v : Fin 18) : Bool :=
  let a := u.val
  let b := v.val
  (a != b && a / 3 == b / 3) ||
  (a == 0 && b == 3) || (a == 3 && b == 0) ||
  (a == 1 && b == 4) || (a == 4 && b == 1) ||
  (a == 2 && b == 6) || (a == 6 && b == 2) ||
  (a == 5 && b == 7) || (a == 7 && b == 5) ||
  (a == 8 && b == 17) || (a == 17 && b == 8) ||
  (a == 9 && b == 12) || (a == 12 && b == 9) ||
  (a == 10 && b == 13) || (a == 13 && b == 10) ||
  (a == 11 && b == 15) || (a == 15 && b == 11) ||
  (a == 14 && b == 16) || (a == 16 && b == 14)

lemma HAdj_symm : ∀ u v : Fin 18, HAdj u v = true → HAdj v u = true := by decide
lemma HAdj_irrefl : ∀ u : Fin 18, HAdj u u = false := by decide

def H : SimpleGraph (Fin 18) where
  Adj u v := HAdj u v = true
  symm := ⟨HAdj_symm⟩
  loopless := ⟨fun u h => by rw [HAdj_irrefl u] at h; exact Bool.false_ne_true h⟩

instance : DecidableRel H.Adj := fun u v => inferInstanceAs (Decidable (HAdj u v = true))

lemma H_deg_decide : ∀ v : Fin 18, (Finset.univ.filter (fun u => HAdj v u = true)).card = 3 := by
  decide

lemma H_cubic : IsCubic H := by
  unfold IsCubic
  intro v
  rw [SimpleGraph.degree]
  convert H_deg_decide v using 1
  congr 1
  ext u
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rfl

/-- The two triangle neighbors and one external neighbor of each vertex in `H`. -/
def triNb1 (v : Fin 18) : Fin 18 :=
  ⟨3 * (v.val / 3) + (v.val % 3 + 1) % 3, by omega⟩

def triNb2 (v : Fin 18) : Fin 18 :=
  ⟨3 * (v.val / 3) + (v.val % 3 + 2) % 3, by omega⟩

def extNb (v : Fin 18) : Fin 18 :=
  match v.val with
  | 0 => 3 | 3 => 0 | 1 => 4 | 4 => 1 | 2 => 6 | 6 => 2 | 5 => 7 | 7 => 5
  | 8 => 17 | 17 => 8 | 9 => 12 | 12 => 9 | 10 => 13 | 13 => 10
  | 11 => 15 | 15 => 11 | 14 => 16 | 16 => 14 | _ => 0

lemma HAdj_mem_nbs : ∀ v u : Fin 18, HAdj v u = true →
    u = triNb1 v ∨ u = triNb2 v ∨ u = extNb v := by decide

lemma triNb_adj : ∀ v : Fin 18, HAdj (triNb1 v) (triNb2 v) = true := by decide

lemma three_in_three {α : Type*} {x y z a b c : α}
    (ha : a = x ∨ a = y ∨ a = z) (hb : b = x ∨ b = y ∨ b = z) (hc : c = x ∨ c = y ∨ c = z)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a = x ∧ b = y) ∨ (a = y ∧ b = x) ∨
    (a = x ∧ c = y) ∨ (a = y ∧ c = x) ∨
    (b = x ∧ c = y) ∨ (b = y ∧ c = x) := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> simp_all

lemma H_clawFree : IsClawFree H := by
  intro v a b c hva hvb hvc hab hac hbc
  have h12 : H.Adj (triNb1 v) (triNb2 v) := triNb_adj v
  have h21 : H.Adj (triNb2 v) (triNb1 v) := HAdj_symm _ _ h12
  rcases three_in_three (HAdj_mem_nbs v a hva) (HAdj_mem_nbs v b hvb) (HAdj_mem_nbs v c hvc)
      hab hac hbc with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl h12
  · exact Or.inl h21
  · exact Or.inr (Or.inl h12)
  · exact Or.inr (Or.inl h21)
  · exact Or.inr (Or.inr h12)
  · exact Or.inr (Or.inr h21)

lemma common_nb_card_le_one : ∀ u v : Fin 18, HAdj u v = true →
    (Finset.univ.filter (fun w : Fin 18 => HAdj u w = true ∧ HAdj v w = true)).card ≤ 1 := by
  decide

lemma H_diamondFree : IsDiamondFree H := by
  intro u v x y huv hux hvx huy hvy
  have hle := common_nb_card_le_one u v huv
  exact Finset.card_le_one.mp hle
    x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hux, hvx⟩)
    y (Finset.mem_filter.mpr ⟨Finset.mem_univ y, huy, hvy⟩)

/-- Explicit parent tree rooted at vertex 0 showing `H` is connected. -/
def parentVert (v : Fin 18) : Fin 18 :=
  match v.val with
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 3 | 5 => 3
  | 6 => 2 | 7 => 6 | 8 => 6 | 17 => 8 | 15 => 17 | 16 => 17
  | 11 => 15 | 9 => 11 | 10 => 11 | 12 => 9 | 13 => 12 | 14 => 12
  | _ => 0

def depthVert (v : Fin 18) : ℕ :=
  match v.val with
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2
  | 6 => 2 | 7 => 3 | 8 => 3 | 17 => 4 | 15 => 5 | 16 => 5
  | 11 => 6 | 9 => 7 | 10 => 7 | 12 => 8 | 13 => 9 | 14 => 9
  | _ => 0

lemma parent_step : ∀ v : Fin 18, v ≠ 0 →
    HAdj v (parentVert v) = true ∧ depthVert (parentVert v) < depthVert v := by decide

lemma H_reachable_zero : ∀ v : Fin 18, H.Reachable v 0 := by
  have haux : ∀ d (v : Fin 18), depthVert v ≤ d → H.Reachable v 0 := by
    intro d
    induction d with
    | zero =>
      intro v hv
      have h0 : v = 0 := by
        revert v hv; decide
      subst h0; exact SimpleGraph.Reachable.refl 0
    | succ d ih =>
      intro v hv
      by_cases h0 : v = 0
      · subst h0; exact SimpleGraph.Reachable.refl 0
      · obtain ⟨hadj, hlt⟩ := parent_step v h0
        exact SimpleGraph.Adj.reachable hadj |>.trans (ih (parentVert v) (by omega))
  intro v
  exact haux 9 v (by revert v; decide)

lemma H_connected : H.Connected := by
  refine ⟨fun u v => (H_reachable_zero u).trans (H_reachable_zero v).symm⟩

lemma H_not_prism : ¬ Nonempty (H ≃g triangularPrism) := by
  rintro ⟨e⟩
  have hc := Fintype.card_congr e.toEquiv
  norm_num at hc

/-- The 13 edges inside the left lobe `{0..8}` of `H`. -/
def lobeEdge : Fin 13 → Fin 18 × Fin 18
  | ⟨0, _⟩  => (0, 1)
  | ⟨1, _⟩  => (0, 2)
  | ⟨2, _⟩  => (1, 2)
  | ⟨3, _⟩  => (3, 4)
  | ⟨4, _⟩  => (3, 5)
  | ⟨5, _⟩  => (4, 5)
  | ⟨6, _⟩  => (6, 7)
  | ⟨7, _⟩  => (6, 8)
  | ⟨8, _⟩  => (7, 8)
  | ⟨9, _⟩  => (0, 3)
  | ⟨10, _⟩ => (1, 4)
  | ⟨11, _⟩ => (2, 6)
  | ⟨12, _⟩ => (5, 7)

def lobeSym2 (i : Fin 13) : Sym2 (Fin 18) :=
  let p := lobeEdge i
  s(p.1, p.2)

lemma lobeEdge_adj : ∀ i : Fin 13, HAdj (lobeEdge i).1 (lobeEdge i).2 = true := by decide

lemma lobeEdge_lt : ∀ i : Fin 13, (lobeEdge i).1 < (lobeEdge i).2 := by decide

lemma lobeEdge_inj : Function.Injective lobeEdge := by
  intro i j h
  revert i j h; decide

lemma lobeSym2_inj : Function.Injective lobeSym2 := by
  intro i j h
  have hi := lobeEdge_lt i
  have hj := lobeEdge_lt j
  simp only [lobeSym2, Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact lobeEdge_inj (Prod.ext h1 h2)
  · exfalso
    have : (lobeEdge i).1 < (lobeEdge i).1 := by
      calc (lobeEdge i).1 < (lobeEdge i).2 := hi
        _ = (lobeEdge j).1 := h2
        _ < (lobeEdge j).2 := hj
        _ = (lobeEdge i).1 := h1.symm
    exact lt_irrefl _ this

/-- Two lobe edges are strongly compatible (can receive the same color in a strong edge coloring). -/
def lobeCompat (i j : Fin 13) : Bool :=
  let a := (lobeEdge i).1
  let b := (lobeEdge i).2
  let c := (lobeEdge j).1
  let d := (lobeEdge j).2
  a != c && a != d && b != c && b != d &&
  !HAdj a c && !HAdj a d && !HAdj b c && !HAdj b d

/-- No 3 of the 13 lobe edges are pairwise strongly compatible (max induced matching size is 2). -/
lemma no_three_lobeCompat :
    ∀ i j k : Fin 13, i ≠ j → i ≠ k → j ≠ k →
      lobeCompat i j = true → lobeCompat i k = true → lobeCompat j k = false := by
  decide

lemma lobeCompat_of_same_color {c : Sym2 (Fin 18) → Fin 6}
    (hc : ∀ e₁ ∈ H.edgeSet, ∀ e₂ ∈ H.edgeSet, e₁ ≠ e₂ → c e₁ = c e₂ →
      ∀ u ∈ e₁, ∀ v ∈ e₂, u ≠ v ∧ ¬ H.Adj u v)
    {i j : Fin 13} (hij : i ≠ j) (hceq : c (lobeSym2 i) = c (lobeSym2 j)) :
    lobeCompat i j = true := by
  have hi : lobeSym2 i ∈ H.edgeSet := lobeEdge_adj i
  have hj : lobeSym2 j ∈ H.edgeSet := lobeEdge_adj j
  have hne : lobeSym2 i ≠ lobeSym2 j := fun h => hij (lobeSym2_inj h)
  have hdisj := hc (lobeSym2 i) hi (lobeSym2 j) hj hne hceq
  set a := (lobeEdge i).1
  set b := (lobeEdge i).2
  set p := (lobeEdge j).1
  set q := (lobeEdge j).2
  have ha : a ∈ lobeSym2 i := Sym2.mem_mk_left a b
  have hb : b ∈ lobeSym2 i := Sym2.mem_mk_right a b
  have hp : p ∈ lobeSym2 j := Sym2.mem_mk_left p q
  have hq : q ∈ lobeSym2 j := Sym2.mem_mk_right p q
  obtain ⟨hac, hHac⟩ := hdisj a ha p hp
  obtain ⟨had, hHad⟩ := hdisj a ha q hq
  obtain ⟨hbc, hHbc⟩ := hdisj b hb p hp
  obtain ⟨hbd, hHbd⟩ := hdisj b hb q hq
  have hHac' : HAdj a p = false := Bool.eq_false_iff.mpr hHac
  have hHad' : HAdj a q = false := Bool.eq_false_iff.mpr hHad
  have hHbc' : HAdj b p = false := Bool.eq_false_iff.mpr hHbc
  have hHbd' : HAdj b q = false := Bool.eq_false_iff.mpr hHbd
  simp only [lobeCompat, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true']
  exact ⟨⟨⟨⟨⟨⟨⟨hac, had⟩, hbc⟩, hbd⟩, hHac'⟩, hHad'⟩, hHbc'⟩, hHbd'⟩

lemma H_not_strong6 : ¬ IsStronglyEdgeColorable H 6 := by
  rintro ⟨c, hc⟩
  have hcard_le : ∀ col : Fin 6,
      (Finset.univ.filter (fun i : Fin 13 => c (lobeSym2 i) = col)).card ≤ 2 := by
    intro col
    by_contra hgt
    have h3 : 2 < (Finset.univ.filter (fun i : Fin 13 => c (lobeSym2 i) = col)).card :=
      Nat.lt_of_not_le hgt
    obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ :
        ∃ i ∈ Finset.univ.filter (fun i : Fin 13 => c (lobeSym2 i) = col),
        ∃ j ∈ Finset.univ.filter (fun i : Fin 13 => c (lobeSym2 i) = col),
        ∃ k ∈ Finset.univ.filter (fun i : Fin 13 => c (lobeSym2 i) = col),
        i ≠ j ∧ i ≠ k ∧ j ≠ k := by
      set S := Finset.univ.filter (fun i : Fin 13 => c (lobeSym2 i) = col)
      have h1 : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨i, hi⟩ := h1
      have h2 : (S.erase i).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hi]; omega
      obtain ⟨j, hj⟩ := h2
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hjS : j ∈ S := (Finset.mem_erase.mp hj).2
      have h3' : ((S.erase i).erase j).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hj, Finset.card_erase_of_mem hi]; omega
      obtain ⟨k, hk⟩ := h3'
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      have hkS : k ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).2
      exact ⟨i, hi, j, hjS, k, hkS, hji.symm, hki.symm, hkj.symm⟩
    have hci : c (lobeSym2 i) = col := (Finset.mem_filter.mp hi).2
    have hcj : c (lobeSym2 j) = col := (Finset.mem_filter.mp hj).2
    have hck : c (lobeSym2 k) = col := (Finset.mem_filter.mp hk).2
    have h12 := lobeCompat_of_same_color hc hij (hci.trans hcj.symm)
    have h13 := lobeCompat_of_same_color hc hik (hci.trans hck.symm)
    have h23 := lobeCompat_of_same_color hc hjk (hcj.trans hck.symm)
    have hbad := no_three_lobeCompat i j k hij hik hjk h12 h13
    rw [h23] at hbad
    exact Bool.false_ne_true hbad.symm
  have hsum : ∑ col : Fin 6,
      (Finset.univ.filter (fun i : Fin 13 => c (lobeSym2 i) = col)).card = 13 := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin 13)))
      (t := (Finset.univ : Finset (Fin 6)))
      (f := fun i => c (lobeSym2 i))
      (fun _ _ => Finset.mem_univ _)
    simpa using h.symm
  have hle : ∑ col : Fin 6,
      (Finset.univ.filter (fun i : Fin 13 => c (lobeSym2 i) = col)).card ≤
      ∑ _col : Fin 6, 2 := Finset.sum_le_sum (fun col _ => hcard_le col)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  omega

end OMA.P_arxiv_2607_23462

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2607_23462.main) := by
  intro h
  exact OMA.P_arxiv_2607_23462.H_not_strong6
    (h 18 OMA.P_arxiv_2607_23462.H
      OMA.P_arxiv_2607_23462.H_connected
      OMA.P_arxiv_2607_23462.H_cubic
      OMA.P_arxiv_2607_23462.H_clawFree
      OMA.P_arxiv_2607_23462.H_diamondFree
      OMA.P_arxiv_2607_23462.H_not_prism)

import OMAReductions.R_opg_seymours_r_graph_conjecture_R1
import Mathlib

/-! A maximum cut leaves a matching inside the two sides of a subcubic multigraph.
The crossing edges are coloured using a decomposition of their multiplicity matrix. -/

open Finset
open scoped Finset
open scoped Classical

namespace Shannon

variable {V E : Type}

def flip [DecidableEq V] (s : V → Bool) (v x : V) : Bool := if x = v then !(s x) else s x

lemma flip_identity [DecidableEq V] (s : V → Bool) (v : V) (z : Sym2 V) (hz : ¬ z.IsDiag) :
    (if ¬ (z.map s).IsDiag then 1 else 0 : ℕ) +
      2 * (if v ∈ z ∧ (z.map s).IsDiag then 1 else 0) =
    (if ¬ (z.map (flip s v)).IsDiag then 1 else 0) +
      (if v ∈ z then 1 else 0) := by
  induction z using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using hz
    simp only [Sym2.map_mk, Sym2.mk_isDiag_iff, Sym2.mem_iff, flip]
    by_cases ha : a = v <;> by_cases hb : b = v <;> cases sa : s a <;> cases sb : s b <;> grind

abbrev Crossing (ends : E → Sym2 V) (side : V → Bool) :=
  {e : E // ¬ ((ends e).map side).IsDiag}

theorem oriented_pair (side : V → Bool) (z : Sym2 V) (hz : ¬ (z.map side).IsDiag) :
    ∃ l r : V, z = s(l,r) ∧ side l = false ∧ side r = true := by
  induction z using Sym2.ind with
  | h a b =>
    have hne : side a ≠ side b := by simpa [Sym2.map_mk] using hz
    cases ha : side a <;> cases hb : side b <;> simp_all
    · exact ⟨a,b,Or.inl ⟨rfl,rfl⟩,ha,hb⟩
    · exact ⟨b,a,Or.inr ⟨rfl,rfl⟩,hb,ha⟩

variable [Fintype V] [DecidableEq V]

theorem exists_perm_decomposition (d : ℕ)
    (M : V → V → ℕ) (row : ∀ i, ∑ j, M i j = d) (col : ∀ j, ∑ i, M i j = d) :
    ∃ σ : Fin d → Equiv.Perm V, ∀ i j, #{c | σ c i = j} = M i j := by
  classical
  induction d generalizing M with
  | zero =>
    refine ⟨Fin.elim0, fun i j => ?_⟩
    have h := single_le_sum (f := M i) (fun a _ => Nat.zero_le (M i a)) (mem_univ j)
    simp [row] at h
    simp [h]
  | succ d ih =>
    let N (i : V) := univ.filter fun j => M i j ≠ 0
    have hall (A : Finset V) : A.card ≤ (A.biUnion N).card := by
      have rows (i : V) : ∑ j ∈ N i, M i j = d + 1 := by
        simp [N, sum_subset (filter_subset _ _), row]
      apply (Nat.mul_le_mul_right_iff (Nat.zero_lt_succ d)).mp
      calc
        _ = ∑ i ∈ A, ∑ j ∈ N i, M i j := by simp [rows]
        _ ≤ ∑ i ∈ A, ∑ j ∈ A.biUnion N, M i j :=
          sum_le_sum fun i hi => sum_le_sum_of_subset (subset_biUnion_of_mem N hi)
        _ ≤ ∑ i, ∑ j ∈ A.biUnion N, M i j := sum_le_sum_of_subset (subset_univ A)
        _ = _ := by rw [sum_comm]; simp [col]
    obtain ⟨f, hf, hN⟩ := (all_card_le_biUnion_card_iff_existsInjective' N).mp hall
    let π := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
    have hπ (i) : 0 < M i (π i) := Nat.pos_of_ne_zero (mem_filter.mp (hN i)).2
    let D (i j : V) := if π i = j then 1 else 0
    let R (i j : V) := M i j - D i j
    have add (i j : V) : R i j + D i j = M i j := by
      apply Nat.sub_add_cancel
      have := hπ i
      dsimp [D]
      split_ifs <;> grind
    obtain ⟨σ, hσ⟩ := ih R (fun i => by
      have := sum_congr (s₁ := univ) rfl (fun j _ => add i j)
      simpa [sum_add_distrib, D, row] using this) (fun j => by
      have := sum_congr (s₁ := univ) rfl (fun i _ => add i j)
      simpa [sum_add_distrib, D, col, ← Equiv.eq_symm_apply] using this)
    refine ⟨Fin.cons π σ, fun i j => ?_⟩
    rw [← add i j, ← hσ, card_filter, card_filter, Fin.sum_univ_succ]
    simp [D, Nat.add_comm]

end Shannon

open Shannon in
theorem OMA.solution : OMA.R_opg_seymours_r_graph_conjecture_R1.H1 := by
  classical
  intro V E _ _ _ ends hloop d hd hdeg
  let mono (s : V → Bool) (e : E) := ((ends e).map s).IsDiag
  let cut (s : V → Bool) := #{e | ¬ mono s e}
  obtain ⟨s, _, hs⟩ := exists_max_image univ cut univ_nonempty
  let internal (v : V) := univ.filter fun e => v ∈ ends e ∧ mono s e
  have hcut (v : V) : (internal v).card ≤ d / 2 := by
    have h := hs (flip s v) (mem_univ _)
    have hsum := sum_congr (s₁ := (univ : Finset E)) rfl (fun e _ => flip_identity s v (ends e) (hloop e))
    simp only [sum_add_distrib, ← mul_sum, ← card_filter] at hsum
    dsimp [internal, mono]
    dsimp [cut, mono] at h
    have := hdeg v
    omega
  choose left right h using fun e : Crossing ends s => oriented_pair s (ends e.val) e.property
  have incident (e : Crossing ends s) (v : V) : v ∈ ends e.val ↔ v = left e ∨ v = right e := by
    rw [(h e).1, Sym2.mem_iff]
  let deg (u : V) := #{e | left e = u} +
    #{e | right e = u}
  have degrees (v : V) : deg v ≤ d := by
    dsimp only [deg]
    refine le_trans ?_ (hdeg v)
    rw [← card_union_of_disjoint (disjoint_filter.mpr (by grind)), ← filter_or]
    apply card_le_card_of_injOn Subtype.val _ (fun _ _ _ _ => Subtype.ext)
    intro e he
    simpa [incident, eq_comm] using he

  let fiber (u v : V) := univ.filter (fun e => left e = u ∧ right e = v)
  let n (u v : V) := (fiber u v).card
  have out (a b : Crossing ends s → V) (u : V) : ∑ v, #{e | a e = u ∧ b e = v} =
      #{e | a e = u} := by
    simpa [filter_filter] using (card_eq_sum_card_fiberwise
      (s := univ.filter (fun e => a e = u)) (f := b) (t := univ) (by simp)).symm
  let M (u v : V) := n u v + n v u + if u = v then d - deg u else 0
  have reg (u : V) : ∑ v, M u v = d := by
    have inc : ∑ v, n v u = #{e | right e = u} := by
      simpa [n, fiber, and_comm] using out right left u
    simpa [M, sum_add_distrib, inc, n, fiber, out, deg] using Nat.add_sub_of_le (degrees u)
  have symm (u v : V) : M u v = M v u := by
    by_cases h : u = v
    · subst v; rfl
    · simp [M, h, Ne.symm h, add_comm]
  obtain ⟨σ, hσ⟩ := exists_perm_decomposition d M reg fun v =>
    (sum_congr rfl fun u _ => symm u v).trans (reg v)
  let palette (u v : V) := univ.filter (fun c => σ c u = v)
  have emb (u v : V) : Nonempty (↥(fiber u v) ↪ ↥(palette u v)) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_coe, palette, hσ]
    change n u v ≤ n u v + n v u + _
    omega
  let map (u v) := (emb u v).some
  let label e := map (left e) (right e) ⟨e, by simp [fiber]⟩
  let color e := (label e).val
  have matched (e) : σ (color e) (left e) = right e :=
    (mem_filter.mp (label e).prop).2
  have proper (e f : Crossing ends s) (hc : color e = color f)
      (h : left e = left f ∨ right e = right f) : e = f := by
    have eq := (σ (color f)).injective.eq_iff (a := left e) (b := left f)
    rw [← hc, matched e, hc, matched f] at eq
    have same {u v u' v' : V} (a : fiber u v) (b : fiber u' v')
        (hu : u = u') (hv : v = v') (hc' : (map u v a).val = (map u' v' b).val) : a.val = b.val := by
      subst u'
      subst v'
      exact congrArg Subtype.val ((map u v).injective (Subtype.ext hc'))
    exact same ⟨e, by simp [fiber]⟩ ⟨f, by simp [fiber]⟩ (by tauto) (by tauto) hc

  have hi (e : E) (he : mono s e) : d < 3 * d / 2 := by
    let v := (ends e).out.1
    have hv := Sym2.out_fst_mem (ends e)
    have hz : 0 < (internal v).card := card_pos.mpr ⟨e, by simp [internal,v,hv,he]⟩
    have := hcut v
    omega
  let col (e : E) : Fin (3 * d / 2) :=
    if h : mono s e then ⟨d, hi e h⟩ else (color ⟨e,h⟩).castLE (by omega)
  refine ⟨col, fun e f hne ⟨v, he, hf⟩ heq => ?_⟩
  have hval := congrArg Fin.val heq
  by_cases a : mono s e <;> by_cases b : mono s f
  · have hu : (internal v).card ≤ 1 := by
      have := hcut v
      omega
    exact hne (card_le_one_iff.mp hu (by simp [internal, he, a]) (by simp [internal, hf, b]))
  · simp [col, a, b] at hval
    exact (color ⟨f,b⟩).isLt.ne hval.symm
  · simp [col, a, b] at hval
    exact (color ⟨e,a⟩).isLt.ne hval
  · simp [col, a, b] at hval
    apply hne
    apply congrArg Subtype.val (proper ⟨e,a⟩ ⟨f,b⟩ (Fin.ext hval) ?_)
    have := (incident ⟨e,a⟩ v).mp he
    have := (incident ⟨f,b⟩ v).mp hf
    grind


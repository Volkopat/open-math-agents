import OMAReductions.R_Erdos64_erdos_64_R1_H2_R2
import Mathlib

/-!
# Structural reduction of the 4-regular C4-free branch of Erdős Problem 64

Step H2 of Erdos64.erdos_64.R1.H2.R2 reduces the equality case of the noncubic branch to
finite 4-regular C4-free graphs. This reduction proves four structural theorems in Lean
and splits the remaining 4-regular C4-free graphs into two constrained subproblems:

1. Connectedness and bridgelessness: by strong induction on vertex count, a minimal
   counterexample is connected, and every connected 4-regular graph is bridgeless
   by a degree-sum parity argument.
2. Claw-free / all-triangulated elimination (Shauger 1998; Nowbandegani et al. 2014):
   every finite 4-regular C4-free graph in which every edge lies in a triangle (equivalently,
   every claw-free 4-regular C4-free graph) contains a cycle of length 2^k (k ≥ 3), obtained
   by taking a shortest cycle of length s ≥ 5 (automatically chordless) and taking pairwise
   disjoint triangular detours along its edges to realize every length in [s, 2s].
3. Diameter ≤ 3 elimination (Temeller, October 2026): every finite connected 4-regular
   C4-free graph of diameter at most 3 contains a power-of-two cycle (specifically C8
   whenever there is a non-triangulated edge, via bridge star analysis, funnelling, and
   forced short connections). Hence any remaining graph has diameter at least 4, which
   immediately forces at least 22 vertices when triangle-free and at least 18 vertices
   in general.
4. Free non-adjacent involution / 2-cover elimination: by strong induction on order,
   a minimal 4-regular C4-free counterexample admits no graph automorphism σ of order 2
   with σ x ≠ x and ¬ H.Adj x (σ x) for all x (otherwise H / σ is a smaller 4-regular
   graph whose C4 or 2^k-cycle lifts to a C4, C8, 2^k-, or 2^(k+1)-cycle in H).

The remaining cases are split into H1 (triangle-free) and H2 (containing both a triangle
and an induced claw).
-/

namespace OMA.R_Erdos64_erdos_64_R1_H2_R2_H2_R1

open SimpleGraph Finset
open scoped Classical

/-- Connected bridgeless 4-regular triangle-free C4-free C8-free graphs of diameter
at least 4 (hence at least 22 vertices) admitting no free non-adjacent involution. -/
def H1 : Prop :=
  ∀ (W : Type) (H : SimpleGraph W) [Fintype W] [DecidableRel H.Adj],
    H.Connected → (∀ v, H.degree v = 4) →
    (∀ ⦃a b⦄, H.Adj a b → ¬ H.IsBridge s(a, b)) →
    (∀ a b c, H.Adj a b → H.Adj b c → ¬ H.Adj c a) →
    (∀ a x b y, H.Adj a x → H.Adj x b → H.Adj b y → H.Adj y a → a = b ∨ x = y) →
    ¬ cycleGraph 8 ⊑ H →
    (∃ u v : W, u ≠ v ∧ ¬ H.Adj u v ∧ (∀ w, ¬ (H.Adj u w ∧ H.Adj w v)) ∧
      (∀ w z, ¬ (H.Adj u w ∧ H.Adj w z ∧ H.Adj z v))) →
    22 ≤ Fintype.card W →
    (¬ ∃ σ : H ≃g H, (∀ x, σ (σ x) = x) ∧ (∀ x, σ x ≠ x) ∧ (∀ x, ¬ H.Adj x (σ x))) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ H

/-- Connected bridgeless 4-regular C4-free C8-free graphs of diameter at least 4
(hence at least 18 vertices) containing both a triangle and an induced claw (and an
edge in no triangle), admitting no free non-adjacent involution. -/
def H2 : Prop :=
  ∀ (W : Type) (H : SimpleGraph W) [Fintype W] [DecidableRel H.Adj],
    H.Connected → (∀ v, H.degree v = 4) →
    (∀ ⦃a b⦄, H.Adj a b → ¬ H.IsBridge s(a, b)) →
    (∃ a b c, H.Adj a b ∧ H.Adj b c ∧ H.Adj c a) →
    (∀ a x b y, H.Adj a x → H.Adj x b → H.Adj b y → H.Adj y a → a = b ∨ x = y) →
    ¬ cycleGraph 8 ⊑ H →
    (∃ u v : W, H.Adj u v ∧ ∀ w, ¬ (H.Adj u w ∧ H.Adj v w)) →
    (∃ v a b c : W, H.Adj v a ∧ H.Adj v b ∧ H.Adj v c ∧
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ ¬ H.Adj a b ∧ ¬ H.Adj b c ∧ ¬ H.Adj a c) →
    (∃ u v : W, u ≠ v ∧ ¬ H.Adj u v ∧ (∀ w, ¬ (H.Adj u w ∧ H.Adj w v)) ∧
      (∀ w z, ¬ (H.Adj u w ∧ H.Adj w z ∧ H.Adj z v))) →
    18 ≤ Fintype.card W →
    (¬ ∃ σ : H ≃g H, (∀ x, σ (σ x) = x) ∧ (∀ x, σ x ≠ x) ∧ (∀ x, ¬ H.Adj x (σ x))) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ H

section Helpers

private lemma common_eq {W : Type} {H : SimpleGraph W}
    (hc4 : ∀ a x b y, H.Adj a x → H.Adj x b → H.Adj b y → H.Adj y a → a = b ∨ x = y)
    {a b x y : W} (hab : a ≠ b) (hax : H.Adj a x) (hbx : H.Adj b x)
    (hay : H.Adj a y) (hby : H.Adj b y) : x = y := by
  rcases hc4 a x b y hax hbx.symm hby hay.symm with h | h
  · exact absurd h hab
  · exact h

private lemma no_c4_copy {W : Type} {H : SimpleGraph W}
    (hc4 : ∀ a x b y, H.Adj a x → H.Adj x b → H.Adj b y → H.Adj y a → a = b ∨ x = y) :
    ¬ cycleGraph 4 ⊑ H := by
  intro h
  obtain ⟨c, hper, hadj, hinj⟩ :=
    OMA.R_Erdos64_erdos_64_R1_H2_R2.seq_of_copy H 4 (by norm_num) h
  have h01 := hadj 0
  have h12 := hadj 1
  have h23 := hadj 2
  have h30 : H.Adj (c 3) (c 0) := by
    have := hadj 3
    simpa [hper 0] using this
  rcases hc4 (c 0) (c 1) (c 2) (c 3) h01 h12 h23 h30 with h02 | h13
  · exact absurd (hinj 0 2 (by omega) (by omega) h02) (by omega)
  · exact absurd (hinj 1 3 (by omega) (by omega) h13) (by omega)

private lemma copy_eight {W : Type} (H : SimpleGraph W)
    (v0 v1 v2 v3 v4 v5 v6 v7 : W)
    (h01 : H.Adj v0 v1) (h12 : H.Adj v1 v2) (h23 : H.Adj v2 v3) (h34 : H.Adj v3 v4)
    (h45 : H.Adj v4 v5) (h56 : H.Adj v5 v6) (h67 : H.Adj v6 v7) (h70 : H.Adj v7 v0)
    (hnodup : ([v0, v1, v2, v3, v4, v5, v6, v7] : List W).Nodup) :
    cycleGraph 8 ⊑ H := by
  let v : Fin 8 → W := ![v0, v1, v2, v3, v4, v5, v6, v7]
  have hget : ∀ i : Fin 8, ([v0, v1, v2, v3, v4, v5, v6, v7] : List W)[i.val]'(by simp) = v i := by
    intro i; fin_cases i <;> rfl
  have hinj : Function.Injective v := by
    intro i j hij
    have h' : ([v0, v1, v2, v3, v4, v5, v6, v7] : List W)[i.val]'(by simp) =
        ([v0, v1, v2, v3, v4, v5, v6, v7] : List W)[j.val]'(by simp) := by
      rw [hget i, hget j]; exact hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnodup).mp h')
  apply OMA.R_Erdos64_erdos_64_R1_H2_R2.copy_of_periodic H 8 (by norm_num)
    (fun n => v ⟨n % 8, Nat.mod_lt _ (by omega)⟩)
  · intro n; simp [Nat.add_mod_right]
  · intro n
    have hr : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨
        n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by omega
    have hnext : (n + 1) % 8 = (n % 8 + 1) % 8 := by omega
    rcases hr with hr | hr | hr | hr | hr | hr | hr | hr <;>
      simp [v, hnext, hr, h01, h12, h23, h34, h45, h56, h67, h70]
  · intro a b ha hb hab
    have := hinj hab
    simp [Fin.ext_iff, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact this

private lemma bipartite_star_of_no_M2 {α β : Type} (a0 : α) (R : α → β → Prop)
    (hno : ∀ a1 a2 b1 b2, a1 ≠ a2 → b1 ≠ b2 → R a1 b1 → ¬ R a2 b2) :
    (∃ a1 : α, ∀ a b, R a b → a = a1) ∨ (∃ b1 : β, ∀ a b, R a b → b = b1) := by
  by_cases h1 : ∃ a b, R a b
  · obtain ⟨a1, b1, hab1⟩ := h1
    by_cases h2 : ∃ a2 b2, R a2 b2 ∧ a2 ≠ a1
    · obtain ⟨a2, b2, hab2, hne⟩ := h2
      have hb2 : b2 = b1 := by
        by_contra hbne
        exact hno a1 a2 b1 b2 hne.symm (Ne.symm hbne) hab1 hab2
      rw [hb2] at hab2
      right
      refine ⟨b1, fun a b hab => ?_⟩
      by_contra hbb
      by_cases haa : a = a1
      · rw [haa] at hab
        exact hno a2 a1 b1 b hne (Ne.symm hbb) hab2 hab
      · exact hno a1 a b1 b (Ne.symm haa) (Ne.symm hbb) hab1 hab
    · push Not at h2
      left
      exact ⟨a1, fun a b hab => h2 a b hab⟩
  · push Not at h1
    left
    exact ⟨a0, fun a b hab => absurd hab (h1 a b)⟩

private lemma mod_succ_of_eq {n m : ℕ} (hm : 2 ≤ m) (h : n % m + 1 = m) : (n + 1) % m = 0 := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < m), h, Nat.mod_self]

private lemma mod_succ_of_lt {n m : ℕ} (h : n % m + 1 < m) : (n + 1) % m = n % m + 1 := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < m), Nat.mod_eq_of_lt h]

private lemma mod_of_lt_two_mul {x m : ℕ} (h : x < 2 * m) :
    x % m = if x < m then x else x - m := by
  split_ifs with hlt
  · exact Nat.mod_eq_of_lt hlt
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/- ### Part 1: Every 4-regular C4-free graph with all edges in triangles has a 2^k-cycle -/

private lemma exists_pow2_in_double_interval (s : ℕ) (hs : 5 ≤ s) :
    ∃ k : ℕ, 3 ≤ k ∧ s ≤ 2 ^ k ∧ 2 ^ k < 2 * s := by
  have hex : ∃ k : ℕ, s ≤ 2 ^ k := ⟨s, Nat.le_of_lt Nat.lt_two_pow_self⟩
  let k := Nat.find hex
  have hk_ge : s ≤ 2 ^ k := Nat.find_spec hex
  have hk_pos : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    rw [hk0] at hk_ge; omega
  have hk_pred : 2 ^ (k - 1) < s := by
    have := Nat.find_min hex (show k - 1 < k by omega)
    omega
  have hk_lt : 2 ^ k < 2 * s := by
    have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
      have hk1 : k = (k - 1) + 1 := by omega
      conv_lhs => rw [hk1]
      rw [pow_succ, mul_comm]
    omega
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have : k ≤ 2 := by omega
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) this
    omega
  exact ⟨k, hk3, hk_ge, hk_lt⟩

private lemma exists_cycle_ge_five {W : Type} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hne : Nonempty W) (hreg : ∀ v, H.degree v = 4) :
    ∃ s : ℕ, 5 ≤ s ∧ cycleGraph s ⊑ H := by
  let P : List W → Prop := fun L =>
    L ≠ [] ∧ L.Nodup ∧ ∀ i (hi : i + 1 < L.length), H.Adj (L[i]'(by omega)) L[i + 1]
  have hbdd : ∀ L, P L → L.length ≤ Fintype.card W := by
    intro L hL
    have hsub : L.toFinset.card ≤ Fintype.card W := Finset.card_le_univ _
    rwa [List.toFinset_card_of_nodup hL.2.1] at hsub
  have hex_len : ∃ n, ∃ L, P L ∧ L.length = n := by
    obtain ⟨w0⟩ := hne
    exact ⟨1, [w0], ⟨by simp, by simp, fun i hi => by simp at hi⟩, rfl⟩
  have hmax_ex : ∃ n, ∀ L, P L → L.length ≤ n := ⟨Fintype.card W, hbdd⟩
  let m := Nat.find hmax_ex
  have hm_ub : ∀ L, P L → L.length ≤ m := Nat.find_spec hmax_ex
  have hm_att : ∃ L, P L ∧ L.length = m := by
    by_contra hno
    push Not at hno
    have hm_pos : 0 < m := by
      obtain ⟨w0⟩ := hne
      have h1 := hm_ub [w0] ⟨by simp, by simp, fun i hi => by simp at hi⟩
      simp at h1; omega
    have hle : ∀ L, P L → L.length ≤ m - 1 := by
      intro L hL
      have h1 := hm_ub L hL
      have h2 := hno L hL
      omega
    exact Nat.find_min hmax_ex (show m - 1 < m by omega) hle
  obtain ⟨L, hPL, hLlen⟩ := hm_att
  have hLpos : 0 < L.length := List.length_pos_of_ne_nil hPL.1
  let v0 : W := L[0]'hLpos
  have hnhd_mem : ∀ w ∈ H.neighborFinset v0, w ∈ L := by
    intro w hw
    by_contra hnot
    have hadj : H.Adj w v0 := ((H.mem_neighborFinset v0 w).mp hw).symm
    have hP' : P (w :: L) := by
      refine ⟨by simp, List.nodup_cons.mpr ⟨hnot, hPL.2.1⟩, ?_⟩
      intro i hi
      cases i with
      | zero => exact hadj
      | succ j => exact hPL.2.2 j (by simp at hi; omega)
    have hle := hm_ub (w :: L) hP'
    simp [hLlen] at hle
  -- Indices of neighbors of v0 in L
  let idxFin : Finset ℕ := (Finset.range L.length).filter (fun i =>
    ∃ hi : i < L.length, H.Adj v0 (L[i]'hi))
  have hcard_idx : idxFin.card = 4 := by
    have heq : idxFin.image (fun i => L.getD i v0) = H.neighborFinset v0 := by
      ext w
      simp only [Finset.mem_image, idxFin, Finset.mem_filter, Finset.mem_range, mem_neighborFinset]
      constructor
      · rintro ⟨i, ⟨hi, _, hadj⟩, rfl⟩
        rwa [List.getD_eq_getElem _ _ hi]
      · intro hw
        have hmem := hnhd_mem w ((H.mem_neighborFinset v0 w).mpr hw)
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
        exact ⟨i, ⟨hi, hi, hw⟩, List.getD_eq_getElem _ _ hi⟩
    have hinj : Set.InjOn (fun i => L.getD i v0) idxFin := by
      intro i hi j hj hij
      dsimp only at hij
      simp only [Finset.mem_coe, idxFin, Finset.mem_filter, Finset.mem_range] at hi hj
      rw [List.getD_eq_getElem _ _ hi.1, List.getD_eq_getElem _ _ hj.1] at hij
      exact (List.Nodup.getElem_inj_iff hPL.2.1).mp hij
    rw [← Finset.card_image_of_injOn hinj, heq, card_neighborFinset_eq_degree, hreg v0]
  have hne_idx : idxFin.Nonempty := Finset.card_pos.mp (by omega)
  let mx := idxFin.max' hne_idx
  have hmx_mem : mx ∈ idxFin := Finset.max'_mem idxFin hne_idx
  have hmx_lt : mx < L.length := (Finset.mem_range.mp (Finset.mem_filter.mp hmx_mem).1)
  have hmx_adj : H.Adj v0 (L[mx]'hmx_lt) := by
    obtain ⟨_, hadj⟩ := (Finset.mem_filter.mp hmx_mem).2
    exact hadj
  have hzero_not : 0 ∉ idxFin := by
    intro h0
    obtain ⟨_, hadj⟩ := (Finset.mem_filter.mp h0).2
    exact H.loopless.irrefl v0 hadj
  have hsub_ico : idxFin ⊆ Finset.Ico 1 (mx + 1) := by
    intro i hi
    have hle := Finset.le_max' idxFin i hi
    have hne0 : i ≠ 0 := fun h => hzero_not (h ▸ hi)
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hmx_ge4 : 4 ≤ mx := by
    have := Finset.card_le_card hsub_ico
    rw [hcard_idx, Nat.card_Ico] at this
    omega
  refine ⟨mx + 1, by omega, ?_⟩
  apply OMA.R_Erdos64_erdos_64_R1_H2_R2.copy_of_periodic H (mx + 1) (by omega)
    (fun n => L[n % (mx + 1)]'(by have := Nat.mod_lt n (show 0 < mx + 1 by omega); omega))
  · intro n; simp [Nat.add_mod_right]
  · intro n
    have hr := Nat.mod_lt n (show 0 < mx + 1 by omega)
    by_cases hlast : n % (mx + 1) = mx
    · have hnext : (n + 1) % (mx + 1) = 0 := mod_succ_of_eq (by omega) (by omega)
      simp only [hlast, hnext]
      exact hmx_adj.symm
    · have hnext : (n + 1) % (mx + 1) = n % (mx + 1) + 1 := mod_succ_of_lt (by omega)
      simp only [hnext]
      exact hPL.2.2 (n % (mx + 1)) (by omega)
  · intro a b ha hb hab
    have ha' : a % (mx + 1) = a := Nat.mod_eq_of_lt ha
    have hb' : b % (mx + 1) = b := Nat.mod_eq_of_lt hb
    simp only [ha', hb'] at hab
    exact (List.Nodup.getElem_inj_iff hPL.2.1).mp hab

private lemma shortest_cycle_chordless {W : Type} {H : SimpleGraph W}
    (hc4 : ∀ a x b y, H.Adj a x → H.Adj x b → H.Adj b y → H.Adj y a → a = b ∨ x = y)
    {s : ℕ} (hs : 5 ≤ s) (hmin : ∀ t, 5 ≤ t → t < s → ¬ cycleGraph t ⊑ H)
    {c : ℕ → W} (hper : ∀ n, c (n + s) = c n) (hadj : ∀ n, H.Adj (c n) (c (n + 1)))
    (hinj : ∀ a b, a < s → b < s → c a = c b → a = b)
    {i j : ℕ} (hi : i < s) (hj : j < s) (hij : i < j) (hchord : H.Adj (c i) (c j)) :
    j = i + 1 ∨ (i = 0 ∧ j = s - 1) := by
  by_contra hnot
  push Not at hnot
  have hd_ge : 2 ≤ j - i := by omega
  have hd_le : j - i ≤ s - 2 := by omega
  have hper_mod : ∀ n, c (n % s) = c n := by
    intro n
    have hdiv : n = n % s + s * (n / s) := (Nat.mod_add_div n s).symm
    conv_rhs => rw [hdiv]
    generalize n / s = q
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, ← add_assoc, hper, ih]
  have hcyc1 : cycleGraph (j - i + 1) ⊑ H := by
    apply OMA.R_Erdos64_erdos_64_R1_H2_R2.copy_of_periodic H (j - i + 1) (by omega)
      (fun n => c (i + n % (j - i + 1)))
    · intro n; simp [Nat.add_mod_right]
    · intro n
      have hr := Nat.mod_lt n (show 0 < j - i + 1 by omega)
      by_cases hlast : n % (j - i + 1) = j - i
      · have hnext : (n + 1) % (j - i + 1) = 0 := mod_succ_of_eq (by omega) (by omega)
        rw [hlast, hnext, add_zero, show i + (j - i) = j by omega]
        exact hchord.symm
      · have hnext : (n + 1) % (j - i + 1) = n % (j - i + 1) + 1 := mod_succ_of_lt (by omega)
        rw [hnext, ← add_assoc]
        exact hadj _
    · intro a b ha hb hab
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab
      have := hinj (i + a) (i + b) (by omega) (by omega) hab
      omega
  have hcyc2 : cycleGraph (s - (j - i) + 1) ⊑ H := by
    apply OMA.R_Erdos64_erdos_64_R1_H2_R2.copy_of_periodic H (s - (j - i) + 1) (by omega)
      (fun n => c (j + n % (s - (j - i) + 1)))
    · intro n; simp [Nat.add_mod_right]
    · intro n
      have hr := Nat.mod_lt n (show 0 < s - (j - i) + 1 by omega)
      by_cases hlast : n % (s - (j - i) + 1) = s - (j - i)
      · have hnext : (n + 1) % (s - (j - i) + 1) = 0 := mod_succ_of_eq (by omega) (by omega)
        rw [hlast, hnext, add_zero, show j + (s - (j - i)) = i + s by omega, hper]
        exact hchord
      · have hnext : (n + 1) % (s - (j - i) + 1) = n % (s - (j - i) + 1) + 1 := mod_succ_of_lt (by omega)
        rw [hnext, ← add_assoc]
        exact hadj _
    · intro a b ha hb hab
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab
      rw [← hper_mod (j + a), ← hper_mod (j + b)] at hab
      have heq := hinj _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hab
      rw [mod_of_lt_two_mul (by omega), mod_of_lt_two_mul (by omega)] at heq
      split_ifs at heq <;> omega
  have hne4_1 : j - i + 1 ≠ 4 := by
    intro h4; rw [h4] at hcyc1; exact no_c4_copy hc4 hcyc1
  have hne4_2 : s - (j - i) + 1 ≠ 4 := by
    intro h4; rw [h4] at hcyc2; exact no_c4_copy hc4 hcyc2
  by_cases hge1 : 5 ≤ j - i + 1
  · exact hmin _ hge1 (by omega) hcyc1
  · exact hmin _ (by omega) (by omega) hcyc2

private lemma exists_pow2_of_all_triangulated {W : Type} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hne : Nonempty W) (hreg : ∀ v, H.degree v = 4)
    (hc4 : ∀ a x b y, H.Adj a x → H.Adj x b → H.Adj b y → H.Adj y a → a = b ∨ x = y)
    (htri : ∀ a b, H.Adj a b → ∃ z, H.Adj a z ∧ H.Adj b z) :
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ H := by
  have hex := exists_cycle_ge_five H hne hreg
  obtain ⟨s, hs5, hs_cyc, hmin⟩ :
      ∃ s : ℕ, 5 ≤ s ∧ cycleGraph s ⊑ H ∧ ∀ t, 5 ≤ t → t < s → ¬ cycleGraph t ⊑ H :=
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      fun t ht hlt hc => Nat.find_min hex hlt ⟨ht, hc⟩⟩
  obtain ⟨c, hper, hadj, hinj⟩ :=
    OMA.R_Erdos64_erdos_64_R1_H2_R2.seq_of_copy H s (by omega) hs_cyc
  have hper_mod : ∀ n, c (n % s) = c n := by
    intro n
    have hdiv : n = n % s + s * (n / s) := (Nat.mod_add_div n s).symm
    conv_rhs => rw [hdiv]
    generalize n / s = q
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, ← add_assoc, hper, ih]
  let z : ℕ → W := fun i => Classical.choose (htri (c (i % s)) (c (i % s + 1)) (hadj _))
  have hz1 : ∀ i, H.Adj (c i) (z i) := by
    intro i
    rw [← hper_mod i]
    exact (Classical.choose_spec (htri (c (i % s)) (c (i % s + 1)) (hadj _))).1
  have hz2 : ∀ i, H.Adj (c (i + 1)) (z i) := by
    intro i
    have heq : c (i + 1) = c (i % s + 1) := by
      rw [← hper_mod (i + 1), ← hper_mod (i % s + 1)]
      congr 1
      calc (i + 1) % s = (i % s + 1 % s) % s := Nat.add_mod i 1 s
        _ = (i % s % s + 1 % s) % s := by rw [Nat.mod_mod]
        _ = (i % s + 1) % s := (Nat.add_mod (i % s) 1 s).symm
    rw [heq]
    exact (Classical.choose_spec (htri (c (i % s)) (c (i % s + 1)) (hadj _))).2
  have hchord : ∀ i j, i < s → j < s → H.Adj (c i) (c j) →
      j = i + 1 ∨ i = j + 1 ∨ (i = 0 ∧ j = s - 1) ∨ (j = 0 ∧ i = s - 1) := by
    intro i j hi hj h
    rcases lt_trichotomy i j with hij | rfl | hji
    · rcases shortest_cycle_chordless hc4 hs5 hmin hper hadj hinj hi hj hij h with h1 | h2
      · left; exact h1
      · right; right; left; exact h2
    · exact absurd h (H.loopless.irrefl _)
    · rcases shortest_cycle_chordless hc4 hs5 hmin hper hadj hinj hj hi hji h.symm with h1 | h2
      · right; left; exact h1
      · right; right; right; exact h2
  have hz_not_c : ∀ i j, i < s → j < s → z i ≠ c j := by
    intro i j hi hj heq
    have ha1 : H.Adj (c i) (c j) := heq ▸ hz1 i
    have ha2 : H.Adj (c ((i + 1) % s)) (c j) := by
      rw [hper_mod]; exact heq ▸ hz2 i
    have h1 := hchord i j hi hj ha1
    have h2 := hchord ((i + 1) % s) j (Nat.mod_lt _ (by omega)) hj ha2
    rw [mod_of_lt_two_mul (by omega)] at h2
    split_ifs at h2 <;> rcases h1 with h1 | h1 | ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
      rcases h2 with h2 | h2 | ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ <;> omega
  have hz_inj : ∀ i j, i < s → j < s → z i = z j → i = j := by
    intro i j hi hj heq
    by_contra hne
    wlog hij : i < j generalizing i j
    · exact this j i hj hi heq.symm (Ne.symm hne) (by omega)
    let w := z i
    have hw_i : H.Adj (c i) w := hz1 i
    have hw_i1 : H.Adj (c (i + 1)) w := hz2 i
    have hw_j : H.Adj (c j) w := by rw [show w = z j from heq]; exact hz1 j
    have hw_j1 : H.Adj (c (j + 1)) w := by rw [show w = z j from heq]; exact hz2 j
    by_cases h1 : j = i + 1
    · subst h1
      have hci_ne : c i ≠ c ((i + 2) % s) := by
        intro h
        have hm := hinj i ((i + 2) % s) hi (Nat.mod_lt _ (by omega)) h
        rw [mod_of_lt_two_mul (by omega)] at hm
        split_ifs at hm <;> omega
      have hw_ne : w ≠ c (i + 1) := fun h => H.loopless.irrefl _ (h ▸ hw_i1)
      have hw_j1' : H.Adj (c ((i + 2) % s)) w := by
        rw [hper_mod]; exact hw_j1
      have ha2 : H.Adj (c (i + 1)) (c ((i + 2) % s)) := by
        rw [hper_mod]; exact hadj (i + 1)
      exact hci_ne (common_eq hc4 hw_ne hw_i.symm (hadj i).symm hw_j1'.symm ha2)
    by_cases h2 : i = 0 ∧ j = s - 1
    · rcases h2 with ⟨rfl, rfl⟩
      have hc1_ne : c 1 ≠ c (s - 1) := by
        intro h
        have := hinj 1 (s - 1) (by omega) (by omega) h
        omega
      have hw_ne : w ≠ c 0 := fun h => H.loopless.irrefl _ (h ▸ hw_i)
      have ha_last : H.Adj (c (s - 1)) (c 0) := by
        have := hadj (s - 1)
        rwa [show s - 1 + 1 = 0 + s by omega, hper] at this
      exact hc1_ne (common_eq hc4 hw_ne hw_i1.symm (hadj 0) hw_j.symm ha_last.symm)
    -- Non-consecutive edges: split into two arcs of lengths (j - i) + 1 and s - (j - i) + 1
    have hd_ge : 2 ≤ j - i := by omega
    have hd_le : j - i ≤ s - 2 := by omega
    have hcyc1 : cycleGraph (j - i + 1) ⊑ H := by
      apply OMA.R_Erdos64_erdos_64_R1_H2_R2.copy_of_periodic H (j - i + 1) (by omega)
        (fun n => if n % (j - i + 1) = j - i then w else c (i + 1 + n % (j - i + 1)))
      · intro n; simp [Nat.add_mod_right]
      · intro n
        have hr := Nat.mod_lt n (show 0 < j - i + 1 by omega)
        by_cases hl : n % (j - i + 1) = j - i
        · have hn : (n + 1) % (j - i + 1) = 0 := mod_succ_of_eq (by omega) (by omega)
          rw [if_pos hl, if_neg (by omega), hn, add_zero]
          exact hw_i1.symm
        · by_cases hl2 : n % (j - i + 1) + 1 = j - i
          · have hn : (n + 1) % (j - i + 1) = j - i := by
              rw [mod_succ_of_lt (by omega)]; exact hl2
            rw [if_neg hl, if_pos hn, show i + 1 + n % (j - i + 1) = j by omega]
            exact hw_j
          · have hn : (n + 1) % (j - i + 1) = n % (j - i + 1) + 1 := mod_succ_of_lt (by omega)
            rw [if_neg hl, if_neg (by omega), hn, ← add_assoc]
            exact hadj _
      · intro a b ha hb hab
        rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab
        split_ifs at hab
        · omega
        · exact absurd hab (hz_not_c i (i + 1 + b) hi (by omega))
        · exact absurd hab.symm (hz_not_c i (i + 1 + a) hi (by omega))
        · have := hinj (i + 1 + a) (i + 1 + b) (by omega) (by omega) hab
          omega
    have hcyc2 : cycleGraph (s - (j - i) + 1) ⊑ H := by
      apply OMA.R_Erdos64_erdos_64_R1_H2_R2.copy_of_periodic H (s - (j - i) + 1) (by omega)
        (fun n => if n % (s - (j - i) + 1) = s - (j - i) then w else c (j + 1 + n % (s - (j - i) + 1)))
      · intro n; simp [Nat.add_mod_right]
      · intro n
        have hr := Nat.mod_lt n (show 0 < s - (j - i) + 1 by omega)
        by_cases hl : n % (s - (j - i) + 1) = s - (j - i)
        · have hn : (n + 1) % (s - (j - i) + 1) = 0 := mod_succ_of_eq (by omega) (by omega)
          rw [if_pos hl, if_neg (by omega), hn, add_zero]
          exact hw_j1.symm
        · by_cases hl2 : n % (s - (j - i) + 1) + 1 = s - (j - i)
          · have hn : (n + 1) % (s - (j - i) + 1) = s - (j - i) := by
              rw [mod_succ_of_lt (by omega)]; exact hl2
            rw [if_neg hl, if_pos hn, show j + 1 + n % (s - (j - i) + 1) = i + s by omega, hper]
            exact hw_i
          · have hn : (n + 1) % (s - (j - i) + 1) = n % (s - (j - i) + 1) + 1 := mod_succ_of_lt (by omega)
            rw [if_neg hl, if_neg (by omega), hn, ← add_assoc]
            exact hadj _
      · intro a b ha hb hab
        rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab
        split_ifs at hab
        · omega
        · rw [← hper_mod (j + 1 + b)] at hab
          exact absurd hab (hz_not_c i _ hi (Nat.mod_lt _ (by omega)))
        · rw [← hper_mod (j + 1 + a)] at hab
          exact absurd hab.symm (hz_not_c i _ hi (Nat.mod_lt _ (by omega)))
        · rw [← hper_mod (j + 1 + a), ← hper_mod (j + 1 + b)] at hab
          have hm := hinj _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hab
          rw [mod_of_lt_two_mul (by omega), mod_of_lt_two_mul (by omega)] at hm
          split_ifs at hm <;> omega
    have hne4_1 : j - i + 1 ≠ 4 := fun h4 => no_c4_copy hc4 (h4 ▸ hcyc1)
    have hne4_2 : s - (j - i) + 1 ≠ 4 := fun h4 => no_c4_copy hc4 (h4 ▸ hcyc2)
    by_cases hge1 : 5 ≤ j - i + 1
    · exact hmin _ hge1 (by omega) hcyc1
    · exact hmin _ (by omega) (by omega) hcyc2
  -- Realize length 2^k in [s, 2s)
  obtain ⟨k, hk3, hk_ge, hk_lt⟩ := exists_pow2_in_double_interval s hs5
  let r := 2 ^ k - s
  have hr_lt : r < s := by omega
  have hN_eq : 2 ^ k = s + r := by omega
  refine ⟨k, by omega, ?_⟩
  apply OMA.R_Erdos64_erdos_64_R1_H2_R2.copy_of_periodic H (2 ^ k) (by omega)
    (fun n =>
      let t := n % 2 ^ k
      if t < 2 * r then (if t % 2 = 0 then c (t / 2) else z (t / 2)) else c (t - r))
  · intro n; simp [Nat.add_mod_right]
  · intro n
    dsimp only
    have ht := Nat.mod_lt n (show 0 < 2 ^ k by omega)
    by_cases hlast : n % 2 ^ k + 1 = 2 ^ k
    · have hnext : (n + 1) % 2 ^ k = 0 := mod_succ_of_eq (by omega) hlast
      have hnot : ¬ n % 2 ^ k < 2 * r := by omega
      rw [if_neg hnot, hnext]
      have hlast_c : c (n % 2 ^ k - r) = c (s - 1) := by congr 1; omega
      rw [hlast_c]
      have hadj_end : H.Adj (c (s - 1)) (c 0) := by
        have := hadj (s - 1); rwa [show s - 1 + 1 = 0 + s by omega, hper] at this
      by_cases hr0 : 0 < 2 * r
      · rw [if_pos hr0, if_pos (by omega)]; simpa using hadj_end
      · rw [if_neg hr0]; simpa [show r = 0 by omega] using hadj_end
    · have hnext : (n + 1) % 2 ^ k = n % 2 ^ k + 1 := mod_succ_of_lt (by omega)
      rw [hnext]
      by_cases hlt1 : n % 2 ^ k < 2 * r
      · rw [if_pos hlt1]
        rcases Nat.mod_two_eq_zero_or_one (n % 2 ^ k) with hev | hod
        · have hlt2 : n % 2 ^ k + 1 < 2 * r := by omega
          rw [if_pos hev, if_pos hlt2, if_neg (by omega),
            show (n % 2 ^ k + 1) / 2 = n % 2 ^ k / 2 by omega]
          exact hz1 _
        · rw [if_neg (by omega)]
          by_cases hlt2 : n % 2 ^ k + 1 < 2 * r
          · rw [if_pos hlt2, if_pos (by omega),
              show (n % 2 ^ k + 1) / 2 = n % 2 ^ k / 2 + 1 by omega]
            exact (hz2 _).symm
          · rw [if_neg hlt2, show n % 2 ^ k + 1 - r = n % 2 ^ k / 2 + 1 by omega]
            exact (hz2 _).symm
      · have hlt2 : ¬ n % 2 ^ k + 1 < 2 * r := by omega
        rw [if_neg hlt1, if_neg hlt2, show n % 2 ^ k + 1 - r = n % 2 ^ k - r + 1 by omega]
        exact hadj _
  · intro a b ha hb hab
    dsimp only at hab
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab
    split_ifs at hab
    · have := hinj (a / 2) (b / 2) (by omega) (by omega) hab; omega
    · exact absurd hab.symm (hz_not_c (b / 2) (a / 2) (by omega) (by omega))
    · have := hinj (a / 2) (b - r) (by omega) (by omega) hab; omega
    · exact absurd hab (hz_not_c (a / 2) (b / 2) (by omega) (by omega))
    · have := hz_inj (a / 2) (b / 2) (by omega) (by omega) hab; omega
    · exact absurd hab (hz_not_c (a / 2) (b - r) (by omega) (by omega))
    · have := hinj (a - r) (b / 2) (by omega) (by omega) hab; omega
    · exact absurd hab.symm (hz_not_c (b / 2) (a - r) (by omega) (by omega))
    · have := hinj (a - r) (b - r) (by omega) (by omega) hab; omega

private lemma exists_claw_of_non_triangulated {W : Type} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = 4)
    (hc4 : ∀ a x b y, H.Adj a x → H.Adj x b → H.Adj b y → H.Adj y a → a = b ∨ x = y)
    {u v : W} (huv : H.Adj u v) (hnt : ∀ w, ¬ (H.Adj u w ∧ H.Adj v w)) :
    ∃ a b c : W, H.Adj u a ∧ H.Adj u b ∧ H.Adj u c ∧
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ ¬ H.Adj a b ∧ ¬ H.Adj b c ∧ ¬ H.Adj a c := by
  let A := (H.neighborFinset u).erase v
  have hAcard : A.card = 3 := by
    rw [Finset.card_erase_of_mem ((H.mem_neighborFinset u v).mpr huv),
      card_neighborFinset_eq_degree, hreg u]
  obtain ⟨a1, a2, a3, h12, h13, h23, hAeq⟩ := Finset.card_eq_three.mp hAcard
  have hm1 : a1 ∈ (H.neighborFinset u).erase v := by change a1 ∈ A; rw [hAeq]; simp
  have hm2 : a2 ∈ (H.neighborFinset u).erase v := by change a2 ∈ A; rw [hAeq]; simp
  have hm3 : a3 ∈ (H.neighborFinset u).erase v := by change a3 ∈ A; rw [hAeq]; simp
  have ha1 : H.Adj u a1 := (H.mem_neighborFinset u a1).mp (Finset.mem_of_mem_erase hm1)
  have ha2 : H.Adj u a2 := (H.mem_neighborFinset u a2).mp (Finset.mem_of_mem_erase hm2)
  have ha3 : H.Adj u a3 := (H.mem_neighborFinset u a3).mp (Finset.mem_of_mem_erase hm3)
  have hv1 : a1 ≠ v := (Finset.mem_erase.mp hm1).1
  have hv2 : a2 ≠ v := (Finset.mem_erase.mp hm2).1
  have hv3 : a3 ≠ v := (Finset.mem_erase.mp hm3).1
  have hnv1 : ¬ H.Adj v a1 := fun h => hnt a1 ⟨ha1, h⟩
  have hnv2 : ¬ H.Adj v a2 := fun h => hnt a2 ⟨ha2, h⟩
  have hnv3 : ¬ H.Adj v a3 := fun h => hnt a3 ⟨ha3, h⟩
  by_cases h12e : H.Adj a1 a2
  · have h13e : ¬ H.Adj a1 a3 := fun h =>
      h23 (common_eq hc4 (H.ne_of_adj ha1) ha2 h12e ha3 h)
    exact ⟨v, a1, a3, huv, ha1, ha3, hv1.symm, h13, hv3.symm, hnv1, h13e, hnv3⟩
  · exact ⟨v, a1, a2, huv, ha1, ha2, hv1.symm, h12, hv2.symm, hnv1, h12e, hnv2⟩

/- ### Part 2: Diameter ≤ 3 elimination for 4-regular C4-free graphs (Temeller, 2026) -/

private lemma no_diam_le_three_of_non_triangulated_side {W : Type} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = 4)
    (hc4 : ∀ a x b y, H.Adj a x → H.Adj x b → H.Adj b y → H.Adj y a → a = b ∨ x = y)
    (hno8 : ¬ cycleGraph 8 ⊑ H)
    (hdiam : ∀ x y : W, x = y ∨ H.Adj x y ∨ (∃ w, H.Adj x w ∧ H.Adj w y) ∨
      (∃ w z, H.Adj x w ∧ H.Adj w z ∧ H.Adj z y))
    {u v : W} (huv : H.Adj u v) (hnt : ∀ w, ¬ (H.Adj u w ∧ H.Adj v w))
    {a2 : W} (ha2 : a2 ∈ (H.neighborFinset u).erase v)
    (hunbridged : ∀ b ∈ (H.neighborFinset v).erase u,
      ∀ x, H.Adj a2 x → x ≠ u → x ∉ (H.neighborFinset u).erase v →
        ¬ (H.Adj b x ∧ x ≠ v ∧ x ∉ (H.neighborFinset v).erase u)) :
    False := by
  let A := (H.neighborFinset u).erase v
  let B := (H.neighborFinset v).erase u
  let NstarA : W → Finset W := fun a => (H.neighborFinset a).filter (fun x => x ≠ u ∧ x ∉ A)
  let NstarB : W → Finset W := fun b => (H.neighborFinset b).filter (fun y => y ≠ v ∧ y ∉ B)
  have huv_ne : u ≠ v := H.ne_of_adj huv
  have hmemA : ∀ a ∈ A, H.Adj u a ∧ a ≠ v ∧ a ≠ u := by
    intro a ha
    have h1 := Finset.mem_erase.mp ha
    have h2 := (H.mem_neighborFinset u a).mp h1.2
    exact ⟨h2, h1.1, (H.ne_of_adj h2).symm⟩
  have hmemB : ∀ b ∈ B, H.Adj v b ∧ b ≠ u ∧ b ≠ v := by
    intro b hb
    have h1 := Finset.mem_erase.mp hb
    have h2 := (H.mem_neighborFinset v b).mp h1.2
    exact ⟨h2, h1.1, (H.ne_of_adj h2).symm⟩
  have hAB_disj : ∀ a ∈ A, a ∉ B := by
    intro a ha hb
    exact hnt a ⟨(hmemA a ha).1, (hmemB a hb).1⟩
  have hAB_nadj : ∀ a ∈ A, ∀ b ∈ B, ¬ H.Adj a b := by
    intro a ha b hb hab
    rcases hc4 u a b v (hmemA a ha).1 hab (hmemB b hb).1.symm huv.symm with h | h
    · exact (hmemB b hb).2.1 h.symm
    · exact (hmemA a ha).2.1 h
  have hNstarA_out : ∀ a ∈ A, ∀ x ∈ NstarA a,
      H.Adj a x ∧ x ≠ u ∧ x ≠ v ∧ x ∉ A ∧ x ∉ B := by
    intro a ha x hx
    simp only [NstarA, Finset.mem_filter, mem_neighborFinset] at hx
    refine ⟨hx.1, hx.2.1, ?_, hx.2.2, ?_⟩
    · intro hxv; subst hxv; exact hnt a ⟨(hmemA a ha).1, hx.1.symm⟩
    · intro hxB; exact hAB_nadj a ha x hxB hx.1
  have hNstarB_out : ∀ b ∈ B, ∀ y ∈ NstarB b,
      H.Adj b y ∧ y ≠ u ∧ y ≠ v ∧ y ∉ A ∧ y ∉ B := by
    intro b hb y hy
    simp only [NstarB, Finset.mem_filter, mem_neighborFinset] at hy
    refine ⟨hy.1, ?_, hy.2.1, ?_, hy.2.2⟩
    · intro hyu; subst hyu; exact hnt b ⟨hy.1.symm, (hmemB b hb).1⟩
    · intro hyA; exact hAB_nadj y hyA b hb hy.1.symm
  have hNstarB_disj : ∀ b1 ∈ B, ∀ b2 ∈ B, b1 ≠ b2 → ∀ y, y ∈ NstarB b1 → y ∉ NstarB b2 := by
    intro b1 hb1 b2 hb2 hne y hy1 hy2
    have h1 := hNstarB_out b1 hb1 y hy1
    have h2 := hNstarB_out b2 hb2 y hy2
    rcases hc4 v b1 y b2 (hmemB b1 hb1).1 h1.1 h2.1.symm (hmemB b2 hb2).1.symm with h | h
    · exact h1.2.2.1 h.symm
    · exact hne h
  have hA_max1 : ∀ a ∈ A, ((H.neighborFinset a).filter (fun z => z ∈ A)).card ≤ 1 := by
    intro a ha
    rw [Finset.card_le_one]
    intro z1 hz1 z2 hz2
    simp only [Finset.mem_filter, mem_neighborFinset] at hz1 hz2
    exact common_eq hc4 (hmemA a ha).2.2.symm (hmemA z1 hz1.2).1 hz1.1 (hmemA z2 hz2.2).1 hz2.1
  have hB_max1 : ∀ b ∈ B, ((H.neighborFinset b).filter (fun z => z ∈ B)).card ≤ 1 := by
    intro b hb
    rw [Finset.card_le_one]
    intro z1 hz1 z2 hz2
    simp only [Finset.mem_filter, mem_neighborFinset] at hz1 hz2
    exact common_eq hc4 (hmemB b hb).2.2.symm (hmemB z1 hz1.2).1 hz1.1 (hmemB z2 hz2.2).1 hz2.1
  have hNstarA_card : ∀ a ∈ A, (NstarA a).card + ((H.neighborFinset a).filter (fun z => z ∈ A)).card = 3 := by
    intro a ha
    have hu_mem : u ∈ H.neighborFinset a := (H.mem_neighborFinset a u).mpr (hmemA a ha).1.symm
    have hpart : (H.neighborFinset a).erase u = NstarA a ∪ (H.neighborFinset a).filter (fun z => z ∈ A) := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_union, NstarA, Finset.mem_filter, mem_neighborFinset]
      constructor
      · rintro ⟨hxu, hax⟩
        by_cases hxA : x ∈ A
        · right; exact ⟨hax, hxA⟩
        · left; exact ⟨hax, hxu, hxA⟩
      · rintro (⟨hax, hxu, _⟩ | ⟨hax, hxA⟩)
        · exact ⟨hxu, hax⟩
        · exact ⟨(hmemA x hxA).2.2, hax⟩
    have hdisj : Disjoint (NstarA a) ((H.neighborFinset a).filter (fun z => z ∈ A)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_filter.mp hx1).2.2 (Finset.mem_filter.mp hx2).2
    have hc := congrArg Finset.card hpart
    rw [Finset.card_erase_of_mem hu_mem, card_neighborFinset_eq_degree, hreg a,
      Finset.card_union_of_disjoint hdisj] at hc
    omega
  have hNstarB_card : ∀ b ∈ B, (NstarB b).card + ((H.neighborFinset b).filter (fun z => z ∈ B)).card = 3 := by
    intro b hb
    have hv_mem : v ∈ H.neighborFinset b := (H.mem_neighborFinset b v).mpr (hmemB b hb).1.symm
    have hpart : (H.neighborFinset b).erase v = NstarB b ∪ (H.neighborFinset b).filter (fun z => z ∈ B) := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_union, NstarB, Finset.mem_filter, mem_neighborFinset]
      constructor
      · rintro ⟨hxv, hbx⟩
        by_cases hxB : x ∈ B
        · right; exact ⟨hbx, hxB⟩
        · left; exact ⟨hbx, hxv, hxB⟩
      · rintro (⟨hbx, hxv, _⟩ | ⟨hbx, hxB⟩)
        · exact ⟨hxv, hbx⟩
        · exact ⟨(hmemB x hxB).2.2, hbx⟩
    have hdisj : Disjoint (NstarB b) ((H.neighborFinset b).filter (fun z => z ∈ B)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_filter.mp hx1).2.2 (Finset.mem_filter.mp hx2).2
    have hc := congrArg Finset.card hpart
    rw [Finset.card_erase_of_mem hv_mem, card_neighborFinset_eq_degree, hreg b,
      Finset.card_union_of_disjoint hdisj] at hc
    omega
  -- Properties of x ∈ NstarA a2
  have hx_no_u : ∀ x ∈ NstarA a2, ¬ H.Adj x u := by
    intro x hx hxu
    have hxo := hNstarA_out a2 ha2 x hx
    have : x ∈ A := Finset.mem_erase.mpr ⟨hxo.2.2.1, (H.mem_neighborFinset u x).mpr hxu.symm⟩
    exact hxo.2.2.2.1 this
  have hx_no_v : ∀ x ∈ NstarA a2, ¬ H.Adj x v := by
    intro x hx hxv
    have hxo := hNstarA_out a2 ha2 x hx
    rcases hc4 u a2 x v (hmemA a2 ha2).1 hxo.1 hxv huv.symm with h | h
    · exact hxo.2.1 h.symm
    · exact (hmemA a2 ha2).2.1 h
  have hx_no_B : ∀ x ∈ NstarA a2, ∀ b ∈ B, ¬ H.Adj x b := by
    intro x hx b hb hxb
    have hxo := hNstarA_out a2 ha2 x hx
    exact hunbridged b hb x hxo.1 hxo.2.1 hxo.2.2.2.1 ⟨hxb.symm, hxo.2.2.1, hxo.2.2.2.2⟩
  have hx_no_otherA : ∀ x ∈ NstarA a2, ∀ a ∈ A, H.Adj x a → a = a2 := by
    intro x hx a ha hxa
    have hxo := hNstarA_out a2 ha2 x hx
    rcases hc4 u a2 x a (hmemA a2 ha2).1 hxo.1 hxa (hmemA a ha).1.symm with h | h
    · exact absurd h.symm hxo.2.1
    · exact h.symm
  have hx_not_NstarB : ∀ x ∈ NstarA a2, ∀ b ∈ B, x ∉ NstarB b := by
    intro x hx b hb hxb
    exact hx_no_B x hx b hb (hNstarB_out b hb x hxb).1.symm
  -- Short path anatomy from x ∈ NstarA a2 to b ∈ B
  have hshort : ∀ x ∈ NstarA a2, ∀ b ∈ B,
      (∃ y ∈ NstarB b, H.Adj x y) ∨
      (∃ b' ∈ B, H.Adj b' b ∧ ∃ y' ∈ NstarB b', H.Adj x y') ∨
      (∃ w y, w ≠ u ∧ w ≠ v ∧ w ∉ A ∧ w ∉ B ∧ y ∈ NstarB b ∧ H.Adj x w ∧ H.Adj w y) := by
    intro x hx b hb
    have hxo := hNstarA_out a2 ha2 x hx
    rcases hdiam x b with rfl | h1 | ⟨y, hxy, hyb⟩ | ⟨w, y, hxw, hwy, hyb⟩
    · exact absurd hb hxo.2.2.2.2
    · exact absurd h1 (hx_no_B x hx b hb)
    · have hyv : y ≠ v := fun h => hx_no_v x hx (h ▸ hxy)
      have hyB : y ∉ B := fun h => hx_no_B x hx y h hxy
      left
      exact ⟨y, Finset.mem_filter.mpr ⟨(H.mem_neighborFinset b y).mpr hyb.symm, hyv, hyB⟩, hxy⟩
    · by_cases hyv : y = v
      · rw [hyv] at hwy
        have hwu : w ≠ u := fun h => hx_no_u x hx (h ▸ hxw)
        have hwB : w ∈ B := Finset.mem_erase.mpr ⟨hwu, (H.mem_neighborFinset v w).mpr hwy.symm⟩
        exact absurd hxw (hx_no_B x hx w hwB)
      · by_cases hyB : y ∈ B
        · have hwv : w ≠ v := fun h => hx_no_v x hx (h ▸ hxw)
          have hwB : w ∉ B := fun h => hx_no_B x hx w h hxw
          right; left
          exact ⟨y, hyB, hyb, w,
            Finset.mem_filter.mpr ⟨(H.mem_neighborFinset y w).mpr hwy.symm, hwv, hwB⟩, hxw⟩
        · have hyN : y ∈ NstarB b :=
            Finset.mem_filter.mpr ⟨(H.mem_neighborFinset b y).mpr hyb.symm, hyv, hyB⟩
          have hwu : w ≠ u := fun h => hx_no_u x hx (h ▸ hxw)
          have hwv : w ≠ v := fun h => hx_no_v x hx (h ▸ hxw)
          have hwB : w ∉ B := fun h => hx_no_B x hx w h hxw
          have hwA : w ∉ A := by
            intro hwA
            have hwa2 : w = a2 := hx_no_otherA x hx w hwA hxw
            subst hwa2
            have hyo := hNstarB_out b hb y hyN
            exact hunbridged b hb y hwy hyo.2.1 hyo.2.2.2.1 ⟨hyo.1, hyo.2.2.1, hyo.2.2.2.2⟩
          right; right
          exact ⟨w, y, hwu, hwv, hwA, hwB, hyN, hxw, hwy⟩
  -- Same-a2 funnel: no matching of size 2 between NstarA a2 and B via D2 edges
  have hsame_funnel : ∀ x1 ∈ NstarA a2, ∀ x2 ∈ NstarA a2, x1 ≠ x2 →
      ∀ b1 ∈ B, ∀ b2 ∈ B, b1 ≠ b2 →
      (∃ y1 ∈ NstarB b1, H.Adj x1 y1) → ¬ (∃ y2 ∈ NstarB b2, H.Adj x2 y2) := by
    intro x1 hx1 x2 hx2 hxne b1 hb1 b2 hb2 hbne ⟨y1, hy1, hxy1⟩ ⟨y2, hy2, hxy2⟩
    have hx1o := hNstarA_out a2 ha2 x1 hx1
    have hx2o := hNstarA_out a2 ha2 x2 hx2
    have hy1o := hNstarB_out b1 hb1 y1 hy1
    have hy2o := hNstarB_out b2 hb2 y2 hy2
    have hyne : y1 ≠ y2 := fun h => hNstarB_disj b1 hb1 b2 hb2 hbne y1 hy1 (h ▸ hy2)
    have hx1y1 : x1 ≠ y1 := H.ne_of_adj hxy1
    have hx1y2 : x1 ≠ y2 := fun h => hx_not_NstarB x1 hx1 b2 hb2 (h ▸ hy2)
    have hx2y1 : x2 ≠ y1 := fun h => hx_not_NstarB x2 hx2 b1 hb1 (h ▸ hy1)
    have hx2y2 : x2 ≠ y2 := H.ne_of_adj hxy2
    apply hno8
    apply copy_eight H a2 x1 y1 b1 v b2 y2 x2
      hx1o.1 hxy1 hy1o.1.symm (hmemB b1 hb1).1.symm (hmemB b2 hb2).1 hy2o.1 hxy2.symm hx2o.1.symm
    have hma2 := hmemA a2 ha2
    have hmb1 := hmemB b1 hb1
    have hmb2 := hmemB b2 hb2
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      not_false_eq_true, and_true]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · exact fun h => hx1o.2.2.2.1 (h ▸ ha2)
    · exact fun h => hy1o.2.2.2.1 (h ▸ ha2)
    · exact fun h => hAB_disj a2 ha2 (h ▸ hb1)
    · exact hma2.2.1
    · exact fun h => hAB_disj a2 ha2 (h ▸ hb2)
    · exact fun h => hy2o.2.2.2.1 (h ▸ ha2)
    · exact fun h => hx2o.2.2.2.1 (h ▸ ha2)
    · exact hx1y1
    · exact fun h => hx1o.2.2.2.2 (h ▸ hb1)
    · exact hx1o.2.2.1
    · exact fun h => hx1o.2.2.2.2 (h ▸ hb2)
    · exact hx1y2
    · exact hxne
    · exact fun h => hy1o.2.2.2.2 (h ▸ hb1)
    · exact hy1o.2.2.1
    · exact fun h => hy1o.2.2.2.2 (h ▸ hb2)
    · exact hyne
    · exact hx2y1.symm
    · exact hmb1.2.2
    · exact hbne
    · exact fun h => hy2o.2.2.2.2 (h ▸ hb1)
    · exact fun h => hx2o.2.2.2.2 (h ▸ hb1)
    · exact hmb2.2.2.symm
    · exact hy2o.2.2.1.symm
    · exact hx2o.2.2.1.symm
    · exact fun h => hy2o.2.2.2.2 (h ▸ hb2)
    · exact fun h => hx2o.2.2.2.2 (h ▸ hb2)
    · exact hx2y2.symm
  -- Step A: a2 has no neighbor in A
  have ha2_indep : ∀ a' ∈ A, ¬ H.Adj a2 a' := by
    intro a' ha' ha2a'
    have ha2_ne_a' : a2 ≠ a' := H.ne_of_adj ha2a'
    have hno_d3out : ∀ x ∈ NstarA a2, ∀ b ∈ B,
        ¬ ∃ w y, w ≠ u ∧ w ≠ v ∧ w ∉ A ∧ w ∉ B ∧ y ∈ NstarB b ∧ H.Adj x w ∧ H.Adj w y := by
      intro x hx b hb ⟨w, y, hwu, hwv, hwA, hwB, hy, hxw, hwy⟩
      have hxo := hNstarA_out a2 ha2 x hx
      have hyo := hNstarB_out b hb y hy
      have hma' := hmemA a' ha'
      have hma2 := hmemA a2 ha2
      have hmb := hmemB b hb
      apply hno8
      apply copy_eight H u a' a2 x w y b v
        hma'.1 ha2a'.symm hxo.1 hxw hwy hyo.1.symm hmb.1.symm huv.symm
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
        not_false_eq_true, and_true]
      refine ⟨⟨hma'.2.2.symm, hma2.2.2.symm, hxo.2.1.symm, hwu.symm, hyo.2.1.symm, hmb.2.1.symm, huv_ne⟩,
        ⟨ha2_ne_a'.symm, fun h => hxo.2.2.2.1 (h ▸ ha'), fun h => hwA (h ▸ ha'),
          fun h => hyo.2.2.2.1 (h ▸ ha'), fun h => hAB_disj a' ha' (h ▸ hb), hma'.2.1⟩,
        ⟨fun h => hxo.2.2.2.1 (h ▸ ha2), fun h => hwA (h ▸ ha2), fun h => hyo.2.2.2.1 (h ▸ ha2),
          fun h => hAB_disj a2 ha2 (h ▸ hb), hma2.2.1⟩,
        ⟨H.ne_of_adj hxw, fun h => hx_not_NstarB x hx b hb (h ▸ hy),
          fun h => hxo.2.2.2.2 (h ▸ hb), hxo.2.2.1⟩,
        ⟨H.ne_of_adj hwy, fun h => hwB (h ▸ hb), hwv⟩,
        ⟨fun h => hyo.2.2.2.2 (h ▸ hb), hyo.2.2.1⟩, hmb.2.2⟩
    -- Every x ∈ NstarA a2 has at least 2 neighbors in B via D2
    have hdom2 : ∀ x ∈ NstarA a2,
        ∃ b1 ∈ B, ∃ b2 ∈ B, b1 ≠ b2 ∧ (∃ y1 ∈ NstarB b1, H.Adj x y1) ∧ (∃ y2 ∈ NstarB b2, H.Adj x y2) := by
      intro x hx
      have hBcard : B.card = 3 := by
        rw [Finset.card_erase_of_mem ((H.mem_neighborFinset v u).mpr huv.symm),
          card_neighborFinset_eq_degree, hreg v]
      obtain ⟨b1, b2, b3, h12, h13, h23, hBeq⟩ := Finset.card_eq_three.mp hBcard
      have hb1 : b1 ∈ B := by rw [hBeq]; simp
      have hb2 : b2 ∈ B := by rw [hBeq]; simp
      have hb3 : b3 ∈ B := by rw [hBeq]; simp
      have hreach : ∀ b ∈ B, (∃ y ∈ NstarB b, H.Adj x y) ∨
          (∃ b' ∈ B, H.Adj b' b ∧ ∃ y' ∈ NstarB b', H.Adj x y') := by
        intro b hb
        rcases hshort x hx b hb with h | h | h
        · left; exact h
        · right; exact h
        · exact absurd h (hno_d3out x hx b hb)
      let S := B.filter (fun b => ∃ y ∈ NstarB b, H.Adj x y)
      have hS_ge2 : 2 ≤ S.card := by
        by_contra hlt
        have hle1 : S.card ≤ 1 := by omega
        have : Nonempty W := ⟨u⟩
        rcases Finset.card_le_one_iff_subset_singleton.mp hle1 with ⟨b0, hsub⟩
        -- Every b ∈ B must be b0 or adjacent to b0 in B
        have hall : ∀ b ∈ B, b = b0 ∨ H.Adj b0 b := by
          intro b hb
          rcases hreach b hb with hy | ⟨b', hb', hbb', hy'⟩
          · left; exact Finset.mem_singleton.mp (hsub (Finset.mem_filter.mpr ⟨hb, hy⟩))
          · right
            have : b' = b0 := Finset.mem_singleton.mp (hsub (Finset.mem_filter.mpr ⟨hb', hy'⟩))
            exact this ▸ hbb'
        have hS_nonempty : b0 ∈ B := by
          rcases hreach b1 hb1 with hy | ⟨b', hb', _, hy'⟩
          · have hb10 : b1 = b0 := Finset.mem_singleton.mp (hsub (Finset.mem_filter.mpr ⟨hb1, hy⟩))
            exact hb10 ▸ hb1
          · have hb'0 : b' = b0 := Finset.mem_singleton.mp (hsub (Finset.mem_filter.mpr ⟨hb', hy'⟩))
            exact hb'0 ▸ hb'
        -- Now B \ {b0} has card 2, both adjacent to b0, contradicting hB_max1 b0!
        have hsub2 : B.erase b0 ⊆ (H.neighborFinset b0).filter (fun z => z ∈ B) := by
          intro z hz
          have ⟨hne, hzB⟩ := Finset.mem_erase.mp hz
          rcases hall z hzB with rfl | hadj
          · exact absurd rfl hne
          · exact Finset.mem_filter.mpr ⟨(H.mem_neighborFinset b0 z).mpr hadj, hzB⟩
        have hc2 := Finset.card_le_card hsub2
        rw [Finset.card_erase_of_mem hS_nonempty, hBcard] at hc2
        have := hB_max1 b0 hS_nonempty
        omega
      obtain ⟨c1, hc1, c2, hc2, hcne⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
      exact ⟨c1, (Finset.mem_filter.mp hc1).1, c2, (Finset.mem_filter.mp hc2).1, hcne,
        (Finset.mem_filter.mp hc1).2, (Finset.mem_filter.mp hc2).2⟩
    have hcard_a2 : 2 ≤ (NstarA a2).card := by
      have h1 := hNstarA_card a2 ha2
      have h2 := hA_max1 a2 ha2
      omega
    obtain ⟨x1, hx1, x2, hx2, hxne⟩ := Finset.one_lt_card.mp (by omega : 1 < (NstarA a2).card)
    obtain ⟨b1, hb1, b2, hb2, hbne, h11, h12⟩ := hdom2 x1 hx1
    obtain ⟨c1, hc1, c2, hc2, hcne, h21, h22⟩ := hdom2 x2 hx2
    by_cases hbc : b1 = c1
    · exact hsame_funnel x1 hx1 x2 hx2 hxne b1 hb1 c2 hc2 (hbc ▸ hcne) h11 h22
    · exact hsame_funnel x1 hx1 x2 hx2 hxne b1 hb1 c1 hc1 hbc h11 h21
  -- Hence (NstarA a2).card = 3
  have ha2_card3 : (NstarA a2).card = 3 := by
    have hzero : ((H.neighborFinset a2).filter (fun z => z ∈ A)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro z hz hzA
      exact ha2_indep z hzA ((H.mem_neighborFinset a2 z).mp hz)
    have := hNstarA_card a2 ha2
    omega
  -- Step B: B is an independent set
  have hB_indep : ∀ b1 ∈ B, ∀ b2 ∈ B, ¬ H.Adj b1 b2 := by
    intro b1 hb1 b2 hb2 hb12
    have hb12_ne : b1 ≠ b2 := H.ne_of_adj hb12
    have hno_d3out : ∀ x ∈ NstarA a2,
        ¬ ∃ w y, w ≠ u ∧ w ≠ v ∧ w ∉ A ∧ w ∉ B ∧ y ∈ NstarB b1 ∧ H.Adj x w ∧ H.Adj w y := by
      intro x hx ⟨w, y, hwu, hwv, hwA, hwB, hy, hxw, hwy⟩
      have hxo := hNstarA_out a2 ha2 x hx
      have hyo := hNstarB_out b1 hb1 y hy
      have hma2 := hmemA a2 ha2
      have hmb1 := hmemB b1 hb1
      have hmb2 := hmemB b2 hb2
      apply hno8
      apply copy_eight H u a2 x w y b1 b2 v
        hma2.1 hxo.1 hxw hwy hyo.1.symm hb12 hmb2.1.symm huv.symm
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
        not_false_eq_true, and_true]
      refine ⟨⟨hma2.2.2.symm, hxo.2.1.symm, hwu.symm, hyo.2.1.symm, hmb1.2.1.symm, hmb2.2.1.symm, huv_ne⟩,
        ⟨fun h => hxo.2.2.2.1 (h ▸ ha2), fun h => hwA (h ▸ ha2), fun h => hyo.2.2.2.1 (h ▸ ha2),
          fun h => hAB_disj a2 ha2 (h ▸ hb1), fun h => hAB_disj a2 ha2 (h ▸ hb2), hma2.2.1⟩,
        ⟨H.ne_of_adj hxw, fun h => hx_not_NstarB x hx b1 hb1 (h ▸ hy),
          fun h => hxo.2.2.2.2 (h ▸ hb1), fun h => hxo.2.2.2.2 (h ▸ hb2), hxo.2.2.1⟩,
        ⟨H.ne_of_adj hwy, fun h => hwB (h ▸ hb1), fun h => hwB (h ▸ hb2), hwv⟩,
        ⟨fun h => hyo.2.2.2.2 (h ▸ hb1), fun h => hyo.2.2.2.2 (h ▸ hb2), hyo.2.2.1⟩,
        ⟨hb12_ne, hmb1.2.2⟩, hmb2.2.2⟩
    -- Every x ∈ NstarA a2 hits NstarB b1 or NstarB b2
    have hhit : ∀ x ∈ NstarA a2, (∃ y ∈ NstarB b1, H.Adj x y) ∨ (∃ y ∈ NstarB b2, H.Adj x y) := by
      intro x hx
      rcases hshort x hx b1 hb1 with h | ⟨b', hb', hb'1, y', hy', hxy'⟩ | h
      · left; exact h
      · have hb'eq : b' = b2 :=
          common_eq hc4 (hmemB b1 hb1).2.2.symm (hmemB b' hb').1 hb'1.symm (hmemB b2 hb2).1 hb12
        right; exact ⟨y', hb'eq ▸ hy', hxy'⟩
      · exact absurd h (hno_d3out x hx)
    -- By hsame_funnel, either all x ∈ NstarA a2 hit b1, or all hit b2
    have hall_one : (∀ x ∈ NstarA a2, ∃ y ∈ NstarB b1, H.Adj x y) ∨
        (∀ x ∈ NstarA a2, ∃ y ∈ NstarB b2, H.Adj x y) := by
      by_cases h1 : ∀ x ∈ NstarA a2, ∃ y ∈ NstarB b1, H.Adj x y
      · left; exact h1
      · push Not at h1
        obtain ⟨x0, hx0, hno1⟩ := h1
        have hx0_2 : ∃ y ∈ NstarB b2, H.Adj x0 y :=
          (hhit x0 hx0).resolve_left (fun ⟨y, hy, hxy⟩ => hno1 y hy hxy)
        right
        intro x hx
        by_cases hxx0 : x = x0
        · exact hxx0 ▸ hx0_2
        · rcases hhit x hx with hx1 | hx2
          · exact absurd hx0_2 (hsame_funnel x hx x0 hx0 hxx0 b1 hb1 b2 hb2 hb12_ne hx1)
          · exact hx2
    -- In either case, 3 vertices in NstarA a2 map into a 2-element NstarB bstar, giving a C4!
    have hpigeon : ∀ bstar ∈ B, (∃ b' ∈ B, H.Adj bstar b') →
        (∀ x ∈ NstarA a2, ∃ y ∈ NstarB bstar, H.Adj x y) → False := by
      intro bstar hbstar ⟨b', hb', hbb'⟩ hall
      have hge1 : 1 ≤ ((H.neighborFinset bstar).filter (fun z => z ∈ B)).card :=
        Finset.card_pos.mpr ⟨b', Finset.mem_filter.mpr ⟨(H.mem_neighborFinset bstar b').mpr hbb', hb'⟩⟩
      have hcard_lt : (NstarB bstar).card < (NstarA a2).card := by
        have := hNstarB_card bstar hbstar
        omega
      let f : W → W := fun x =>
        if h : x ∈ NstarA a2 then Classical.choose (hall x h) else x
      have hf_maps : ∀ x ∈ NstarA a2, f x ∈ NstarB bstar := by
        intro x hx
        simp only [f, dif_pos hx]
        exact (Classical.choose_spec (hall x hx)).1
      obtain ⟨x1, hx1, x2, hx2, hxne, hfeq⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard_lt hf_maps
      have hadj1 : H.Adj x1 (f x1) := by
        simp only [f, dif_pos hx1]; exact (Classical.choose_spec (hall x1 hx1)).2
      have hadj2 : H.Adj x2 (f x1) := by
        rw [hfeq]; simp only [f, dif_pos hx2]; exact (Classical.choose_spec (hall x2 hx2)).2
      have ha2_ne_y : a2 ≠ f x1 := fun h => (hNstarB_out bstar hbstar (f x1) (hf_maps x1 hx1)).2.2.2.1 (h ▸ ha2)
      exact hxne (common_eq hc4 ha2_ne_y (hNstarA_out a2 ha2 x1 hx1).1 hadj1.symm
        (hNstarA_out a2 ha2 x2 hx2).1 hadj2.symm)
    rcases hall_one with h1 | h2
    · exact hpigeon b1 hb1 ⟨b2, hb2, hb12⟩ h1
    · exact hpigeon b2 hb2 ⟨b1, hb1, hb12.symm⟩ h2
  -- Step C: Both NstarA a2 and B have card 3; extract 2x2 non-edges by bipartite_star_of_no_M2!
  have hBcard3 : B.card = 3 := by
    rw [Finset.card_erase_of_mem ((H.mem_neighborFinset v u).mpr huv.symm),
      card_neighborFinset_eq_degree, hreg v]
  obtain ⟨x0, hx0⟩ := Finset.card_pos.mp (by omega : 0 < (NstarA a2).card)
  let R : {x // x ∈ NstarA a2} → {b // b ∈ B} → Prop :=
    fun x b => ∃ y ∈ NstarB b.1, H.Adj x.1 y
  have hnoM2 : ∀ x1 x2 b1 b2, x1 ≠ x2 → b1 ≠ b2 → R x1 b1 → ¬ R x2 b2 := by
    intro x1 x2 b1 b2 hxne hbne
    exact hsame_funnel x1.1 x1.2 x2.1 x2.2 (fun h => hxne (Subtype.ext h))
      b1.1 b1.2 b2.1 b2.2 (fun h => hbne (Subtype.ext h))
  have h2x2 : ∃ x1 ∈ NstarA a2, ∃ x2 ∈ NstarA a2, x1 ≠ x2 ∧
      ∃ b1 ∈ B, ∃ b2 ∈ B, b1 ≠ b2 ∧
      (¬ ∃ y ∈ NstarB b1, H.Adj x1 y) ∧ (¬ ∃ y ∈ NstarB b2, H.Adj x1 y) ∧
      (¬ ∃ y ∈ NstarB b1, H.Adj x2 y) ∧ (¬ ∃ y ∈ NstarB b2, H.Adj x2 y) := by
    rcases bipartite_star_of_no_M2 ⟨x0, hx0⟩ R hnoM2 with ⟨⟨xa, hxa⟩, hcov⟩ | ⟨⟨ba, hba⟩, hcov⟩
    · have hlt : 1 < ((NstarA a2).erase xa).card := by
        rw [Finset.card_erase_of_mem hxa, ha2_card3]; omega
      obtain ⟨x1, hx1', x2, hx2', hxne⟩ := Finset.one_lt_card.mp hlt
      obtain ⟨b1, hb1, b2, hb2, hbne⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
      have hx1e := Finset.mem_erase.mp hx1'
      have hx2e := Finset.mem_erase.mp hx2'
      refine ⟨x1, hx1e.2, x2, hx2e.2, hxne, b1, hb1, b2, hb2, hbne, ?_, ?_, ?_, ?_⟩
      · intro h; exact hx1e.1 (congrArg Subtype.val (hcov ⟨x1, hx1e.2⟩ ⟨b1, hb1⟩ h))
      · intro h; exact hx1e.1 (congrArg Subtype.val (hcov ⟨x1, hx1e.2⟩ ⟨b2, hb2⟩ h))
      · intro h; exact hx2e.1 (congrArg Subtype.val (hcov ⟨x2, hx2e.2⟩ ⟨b1, hb1⟩ h))
      · intro h; exact hx2e.1 (congrArg Subtype.val (hcov ⟨x2, hx2e.2⟩ ⟨b2, hb2⟩ h))
    · obtain ⟨x1, hx1, x2, hx2, hxne⟩ := Finset.one_lt_card.mp (by omega : 1 < (NstarA a2).card)
      have hlt : 1 < (B.erase ba).card := by
        rw [Finset.card_erase_of_mem hba, hBcard3]; omega
      obtain ⟨b1, hb1', b2, hb2', hbne⟩ := Finset.one_lt_card.mp hlt
      have hb1e := Finset.mem_erase.mp hb1'
      have hb2e := Finset.mem_erase.mp hb2'
      refine ⟨x1, hx1, x2, hx2, hxne, b1, hb1e.2, b2, hb2e.2, hbne, ?_, ?_, ?_, ?_⟩
      · intro h; exact hb1e.1 (congrArg Subtype.val (hcov ⟨x1, hx1⟩ ⟨b1, hb1e.2⟩ h))
      · intro h; exact hb2e.1 (congrArg Subtype.val (hcov ⟨x1, hx1⟩ ⟨b2, hb2e.2⟩ h))
      · intro h; exact hb1e.1 (congrArg Subtype.val (hcov ⟨x2, hx2⟩ ⟨b1, hb1e.2⟩ h))
      · intro h; exact hb2e.1 (congrArg Subtype.val (hcov ⟨x2, hx2⟩ ⟨b2, hb2e.2⟩ h))
  obtain ⟨x1, hx1, x2, hx2, hxne, b1, hb1, b2, hb2, hbne, hn11, hn12, hn21, hn22⟩ := h2x2
  have hd3 : ∀ x ∈ NstarA a2, ∀ b ∈ B, (¬ ∃ y ∈ NstarB b, H.Adj x y) →
      ∃ w y, w ≠ u ∧ w ≠ v ∧ w ∉ A ∧ w ∉ B ∧ y ∈ NstarB b ∧ H.Adj x w ∧ H.Adj w y := by
    intro x hx b hb hno
    rcases hshort x hx b hb with h | ⟨b', hb', hbb', _⟩ | h
    · exact absurd h hno
    · exact absurd hbb' (hB_indep b' hb' b hb)
    · exact h
  obtain ⟨w11, y11, hw11u, hw11v, hw11A, hw11B, hy11, hxw11, hwy11⟩ := hd3 x1 hx1 b1 hb1 hn11
  obtain ⟨w12, y12, hw12u, hw12v, hw12A, hw12B, hy12, hxw12, hwy12⟩ := hd3 x1 hx1 b2 hb2 hn12
  obtain ⟨w21, y21, hw21u, hw21v, hw21A, hw21B, hy21, hxw21, hwy21⟩ := hd3 x2 hx2 b1 hb1 hn21
  obtain ⟨w22, y22, hw22u, hw22v, hw22A, hw22B, hy22, hxw22, hwy22⟩ := hd3 x2 hx2 b2 hb2 hn22
  have hx1o := hNstarA_out a2 ha2 x1 hx1
  have hx2o := hNstarA_out a2 ha2 x2 hx2
  -- Funneling y1j = y2j
  have hfun_y : ∀ b ∈ B, (¬ ∃ y ∈ NstarB b, H.Adj x1 y) → (¬ ∃ y ∈ NstarB b, H.Adj x2 y) →
      ∀ w1 y1 w2 y2, w1 ∉ A → w1 ∉ B → w2 ∉ A → w2 ∉ B →
      y1 ∈ NstarB b → y2 ∈ NstarB b →
      H.Adj x1 w1 → H.Adj w1 y1 → H.Adj x2 w2 → H.Adj w2 y2 → y1 = y2 := by
    intro b hb hn1 hn2 w1 y1 w2 y2 hw1A hw1B hw2A hw2B hy1 hy2 h1a h1b h2a h2b
    by_contra hyne
    have hy1o := hNstarB_out b hb y1 hy1
    have hy2o := hNstarB_out b hb y2 hy2
    have hw12 : w1 ≠ w2 := fun h =>
      hxne (common_eq hc4 (show a2 ≠ w1 from fun h' => hw1A (h' ▸ ha2)) hx1o.1 h1a.symm hx2o.1 (h ▸ h2a).symm)
    have hw1x2 : w1 ≠ x2 := fun h => hn2 ⟨y1, hy1, h ▸ h1b⟩
    have hw2x1 : w2 ≠ x1 := fun h => hn1 ⟨y2, hy2, h ▸ h2b⟩
    have hw1y2 : w1 ≠ y2 := fun h => hn1 ⟨y2, hy2, h ▸ h1a⟩
    have hw2y1 : w2 ≠ y1 := fun h => hn2 ⟨y1, hy1, h ▸ h2a⟩
    apply hno8
    apply copy_eight H a2 x1 w1 y1 b y2 w2 x2
      hx1o.1 h1a h1b hy1o.1.symm hy2o.1 h2b.symm h2a.symm hx2o.1.symm
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      not_false_eq_true, and_true]
    refine ⟨⟨fun h => hx1o.2.2.2.1 (h ▸ ha2), fun h => hw1A (h ▸ ha2), fun h => hy1o.2.2.2.1 (h ▸ ha2),
        fun h => hAB_disj a2 ha2 (h ▸ hb), fun h => hy2o.2.2.2.1 (h ▸ ha2),
        fun h => hw2A (h ▸ ha2), fun h => hx2o.2.2.2.1 (h ▸ ha2)⟩,
      ⟨H.ne_of_adj h1a, fun h => hx_not_NstarB x1 hx1 b hb (h ▸ hy1),
        fun h => hx1o.2.2.2.2 (h ▸ hb), fun h => hx_not_NstarB x1 hx1 b hb (h ▸ hy2),
        hw2x1.symm, hxne⟩,
      ⟨H.ne_of_adj h1b, fun h => hw1B (h ▸ hb), hw1y2, hw12, hw1x2⟩,
      ⟨fun h => hy1o.2.2.2.2 (h ▸ hb), hyne, hw2y1.symm,
        fun h => hx_not_NstarB x2 hx2 b hb (h ▸ hy1)⟩,
      ⟨fun h => hy2o.2.2.2.2 (h ▸ hb), fun h => hw2B (h ▸ hb), fun h => hx2o.2.2.2.2 (h ▸ hb)⟩,
      ⟨(H.ne_of_adj h2b).symm, fun h => hx_not_NstarB x2 hx2 b hb (h ▸ hy2)⟩,
      (H.ne_of_adj h2a).symm⟩
  have hy1_eq : y11 = y21 := hfun_y b1 hb1 hn11 hn21 w11 y11 w21 y21 hw11A hw11B hw21A hw21B hy11 hy21 hxw11 hwy11 hxw21 hwy21
  have hy2_eq : y12 = y22 := hfun_y b2 hb2 hn12 hn22 w12 y12 w22 y22 hw12A hw12B hw22A hw22B hy12 hy22 hxw12 hwy12 hxw22 hwy22
  -- Forcing w11 = w12 and w21 = w22
  have hfun_w : ∀ x ∈ NstarA a2, (¬ ∃ y ∈ NstarB b1, H.Adj x y) → (¬ ∃ y ∈ NstarB b2, H.Adj x y) →
      ∀ wa ya wb yb, wa ≠ v → wa ∉ B → wb ≠ v → wb ∉ B →
      ya ∈ NstarB b1 → yb ∈ NstarB b2 →
      H.Adj x wa → H.Adj wa ya → H.Adj x wb → H.Adj wb yb → wa = wb := by
    intro x hx hn1 hn2 wa ya wb yb hwav hwaB hwbv hwbB hya hyb hxa1 hwa1 hxb1 hwb1
    by_contra hwne
    have hxo := hNstarA_out a2 ha2 x hx
    have hyao := hNstarB_out b1 hb1 ya hya
    have hybo := hNstarB_out b2 hb2 yb hyb
    have hmb1 := hmemB b1 hb1
    have hmb2 := hmemB b2 hb2
    have hyne : ya ≠ yb := fun h => hNstarB_disj b1 hb1 b2 hb2 hbne ya hya (h ▸ hyb)
    have hwayb : wa ≠ yb := fun h => hn2 ⟨yb, hyb, h ▸ hxa1⟩
    have hwbya : wb ≠ ya := fun h => hn1 ⟨ya, hya, h ▸ hxb1⟩
    apply hno8
    apply copy_eight H ya wa x wb yb b2 v b1
      hwa1.symm hxa1.symm hxb1 hwb1 hybo.1.symm hmb2.1.symm hmb1.1 hyao.1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      not_false_eq_true, and_true]
    refine ⟨⟨(H.ne_of_adj hwa1).symm, fun h => hx_not_NstarB x hx b1 hb1 (h ▸ hya),
        hwbya.symm, hyne, fun h => hyao.2.2.2.2 (h ▸ hb2), hyao.2.2.1, fun h => hyao.2.2.2.2 (h ▸ hb1)⟩,
      ⟨(H.ne_of_adj hxa1).symm, hwne, hwayb, fun h => hwaB (h ▸ hb2), hwav, fun h => hwaB (h ▸ hb1)⟩,
      ⟨H.ne_of_adj hxb1, fun h => hx_not_NstarB x hx b2 hb2 (h ▸ hyb),
        fun h => hxo.2.2.2.2 (h ▸ hb2), hxo.2.2.1, fun h => hxo.2.2.2.2 (h ▸ hb1)⟩,
      ⟨H.ne_of_adj hwb1, fun h => hwbB (h ▸ hb2), hwbv, fun h => hwbB (h ▸ hb1)⟩,
      ⟨fun h => hybo.2.2.2.2 (h ▸ hb2), hybo.2.2.1, fun h => hybo.2.2.2.2 (h ▸ hb1)⟩,
      ⟨hmb2.2.2, hbne.symm⟩, hmb1.2.2.symm⟩
  have hw1_eq : w11 = w12 := hfun_w x1 hx1 hn11 hn12 w11 y11 w12 y12 hw11v hw11B hw12v hw12B hy11 hy12 hxw11 hwy11 hxw12 hwy12
  have hw2_eq : w21 = w22 := hfun_w x2 hx2 hn21 hn22 w21 y21 w22 y22 hw21v hw21B hw22v hw22B hy21 hy22 hxw21 hwy21 hxw22 hwy22
  -- Final C4: w11 - y11 - w21 - y12 - w11!
  have hw_ne : w11 ≠ w21 := fun h =>
    hxne (common_eq hc4 (show a2 ≠ w11 from fun h' => hw11A (h' ▸ ha2)) hx1o.1 hxw11.symm hx2o.1 (h ▸ hxw21).symm)
  have hy_ne : y11 ≠ y12 := fun h => hNstarB_disj b1 hb1 b2 hb2 hbne y11 hy11 (h ▸ hy12)
  have hwy21' : H.Adj w21 y11 := hy1_eq ▸ hwy21
  have hwy22' : H.Adj w21 y12 := by rw [hw2_eq, hy2_eq]; exact hwy22
  have hwy12' : H.Adj w11 y12 := hw1_eq ▸ hwy12
  rcases hc4 w11 y11 w21 y12 hwy11 hwy21'.symm hwy22' hwy12'.symm with h | h
  · exact hw_ne h
  · exact hy_ne h

private lemma exists_diam_ge_four {W : Type} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = 4)
    (hc4 : ∀ a x b y, H.Adj a x → H.Adj x b → H.Adj b y → H.Adj y a → a = b ∨ x = y)
    (hno8 : ¬ cycleGraph 8 ⊑ H)
    {u v : W} (huv : H.Adj u v) (hnt : ∀ w, ¬ (H.Adj u w ∧ H.Adj v w)) :
    ∃ x y : W, x ≠ y ∧ ¬ H.Adj x y ∧ (∀ w, ¬ (H.Adj x w ∧ H.Adj w y)) ∧
      (∀ w z, ¬ (H.Adj x w ∧ H.Adj w z ∧ H.Adj z y)) := by
  by_contra hno
  push Not at hno
  have hdiam : ∀ x y : W, x = y ∨ H.Adj x y ∨ (∃ w, H.Adj x w ∧ H.Adj w y) ∨
      (∃ w z, H.Adj x w ∧ H.Adj w z ∧ H.Adj z y) := by
    intro x y
    by_cases h1 : x = y
    · exact Or.inl h1
    by_cases h2 : H.Adj x y
    · exact Or.inr (Or.inl h2)
    by_cases h3 : ∃ w, H.Adj x w ∧ H.Adj w y
    · exact Or.inr (Or.inr (Or.inl h3))
    · push Not at h3
      exact Or.inr (Or.inr (Or.inr (hno x y h1 h2 h3)))
  let A := (H.neighborFinset u).erase v
  let B := (H.neighborFinset v).erase u
  have hAcard : A.card = 3 := by
    rw [Finset.card_erase_of_mem ((H.mem_neighborFinset u v).mpr huv),
      card_neighborFinset_eq_degree, hreg u]
  have hBcard : B.card = 3 := by
    rw [Finset.card_erase_of_mem ((H.mem_neighborFinset v u).mpr huv.symm),
      card_neighborFinset_eq_degree, hreg v]
  obtain ⟨a0, ha0⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
  let Bridged : {a // a ∈ A} → {b // b ∈ B} → Prop := fun a b =>
    ∃ x, H.Adj a.1 x ∧ x ≠ u ∧ x ∉ A ∧ H.Adj b.1 x ∧ x ≠ v ∧ x ∉ B
  have hnoM2 : ∀ a1 a2 b1 b2, a1 ≠ a2 → b1 ≠ b2 → Bridged a1 b1 → ¬ Bridged a2 b2 := by
    intro ⟨a1, ha1⟩ ⟨a2, ha2⟩ ⟨b1, hb1⟩ ⟨b2, hb2⟩ hane hbne
      ⟨x, hax1, hxu, hxA, hbx1, hxv, hxB⟩ ⟨y, hay2, hyu, hyA, hby2, hyv, hyB⟩
    have ha12 : a1 ≠ a2 := fun h => hane (Subtype.ext h)
    have hb12 : b1 ≠ b2 := fun h => hbne (Subtype.ext h)
    have hma1 := Finset.mem_erase.mp ha1
    have hma2 := Finset.mem_erase.mp ha2
    have hmb1 := Finset.mem_erase.mp hb1
    have hmb2 := Finset.mem_erase.mp hb2
    have hua1 : H.Adj u a1 := (H.mem_neighborFinset u a1).mp hma1.2
    have hua2 : H.Adj u a2 := (H.mem_neighborFinset u a2).mp hma2.2
    have hvb1 : H.Adj v b1 := (H.mem_neighborFinset v b1).mp hmb1.2
    have hvb2 : H.Adj v b2 := (H.mem_neighborFinset v b2).mp hmb2.2
    have hxy : x ≠ y := by
      intro heq; subst heq
      rcases hc4 u a1 x a2 hua1 hax1 hay2.symm hua2.symm with h | h
      · exact hxu h.symm
      · exact ha12 h
    have hAB_disj : ∀ a ∈ A, a ∉ B := fun a ha hb =>
      hnt a ⟨(H.mem_neighborFinset u a).mp (Finset.mem_of_mem_erase ha),
        (H.mem_neighborFinset v a).mp (Finset.mem_of_mem_erase hb)⟩
    apply hno8
    apply copy_eight H u a1 x b1 v b2 y a2
      hua1 hax1 hbx1.symm hvb1.symm hvb2 hby2 hay2.symm hua2.symm
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      not_false_eq_true, and_true]
    refine ⟨⟨H.ne_of_adj hua1, hxu.symm, hmb1.1.symm, H.ne_of_adj huv, hmb2.1.symm, hyu.symm, H.ne_of_adj hua2⟩,
      ⟨fun h => hxA (h ▸ ha1), fun h => hAB_disj a1 ha1 (h ▸ hb1), hma1.1,
        fun h => hAB_disj a1 ha1 (h ▸ hb2), fun h => hyA (h ▸ ha1), ha12⟩,
      ⟨fun h => hxB (h ▸ hb1), hxv, fun h => hxB (h ▸ hb2), hxy, fun h => hxA (h ▸ ha2)⟩,
      ⟨(H.ne_of_adj hvb1).symm, hb12, fun h => hyB (h ▸ hb1), fun h => hAB_disj a2 ha2 (h ▸ hb1)⟩,
      ⟨H.ne_of_adj hvb2, hyv.symm, hma2.1.symm⟩,
      ⟨fun h => hyB (h ▸ hb2), fun h => hAB_disj a2 ha2 (h ▸ hb2)⟩,
      fun h => hyA (h ▸ ha2)⟩
  rcases bipartite_star_of_no_M2 ⟨a0, ha0⟩ Bridged hnoM2 with ⟨⟨a1, ha1⟩, hcov⟩ | ⟨⟨b1, hb1⟩, hcov⟩
  · obtain ⟨a2, ha2'⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha1, hAcard]; omega : 0 < (A.erase a1).card)
    have ha2e := Finset.mem_erase.mp ha2'
    exact no_diam_le_three_of_non_triangulated_side H hreg hc4 hno8 hdiam huv hnt ha2e.2
      (fun b hb x h1 h2 h3 ⟨h4, h5, h6⟩ =>
        ha2e.1 (congrArg Subtype.val (hcov ⟨a2, ha2e.2⟩ ⟨b, hb⟩ ⟨x, h1, h2, h3, h4, h5, h6⟩)))
  · obtain ⟨b2, hb2'⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hb1, hBcard]; omega : 0 < (B.erase b1).card)
    have hb2e := Finset.mem_erase.mp hb2'
    exact no_diam_le_three_of_non_triangulated_side H hreg hc4 hno8 hdiam huv.symm
      (fun w ⟨h1, h2⟩ => hnt w ⟨h2, h1⟩) hb2e.2
      (fun a ha x h1 h2 h3 ⟨h4, h5, h6⟩ =>
        hb2e.1 (congrArg Subtype.val (hcov ⟨a, ha⟩ ⟨b2, hb2e.2⟩ ⟨x, h4, h5, h6, h1, h2, h3⟩)))

/- ### Part 3: Bridgelessness and cardinality lower bounds -/

private lemma no_bridge_of_four_regular {W : Type} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = 4) ⦃a b : W⦄ (hab : H.Adj a b) :
    ¬ H.IsBridge s(a, b) := by
  intro hbr
  let H' := H.deleteEdges {s(a, b)}
  have hnot_reach : ¬ H'.Reachable a b := by
    have h1 := SimpleGraph.isBridge_iff.mp hbr
    simpa [H'] using h1
  let C : Finset W := Finset.univ.filter (fun x => H'.Reachable a x)
  have haC : a ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl a⟩
  have hbC : b ∉ C := fun h => hnot_reach (Finset.mem_filter.mp h).2
  let K : SimpleGraph {x : W // x ∈ C} := H'.induce (C : Set W)
  have hKdeg : ∀ v : {x : W // x ∈ C}, K.degree v = H'.degree v.1 := by
    intro ⟨x, hx⟩
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree]
    refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
    · intro y hy
      exact (H'.mem_neighborFinset x y.1).mpr ((K.mem_neighborFinset ⟨x, hx⟩ y).mp hy)
    · intro y1 _ y2 _ heq; exact Subtype.ext heq
    · intro y hy
      have hadj : H'.Adj x y := (H'.mem_neighborFinset x y).mp hy
      have hyC : y ∈ C := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.trans hadj.reachable⟩
      exact ⟨⟨y, hyC⟩, (K.mem_neighborFinset ⟨x, hx⟩ ⟨y, hyC⟩).mpr hadj, rfl⟩
  have hdeg_a : H'.degree a = 3 := by
    have heq : H'.neighborFinset a = (H.neighborFinset a).erase b := by
      ext y
      simp only [mem_neighborFinset, Finset.mem_erase, H', SimpleGraph.deleteEdges_adj,
        Set.mem_singleton_iff, Sym2.eq_iff]
      constructor
      · rintro ⟨hay, hne⟩
        refine ⟨fun hyb => hne (Or.inl ⟨trivial, hyb⟩), hay⟩
      · rintro ⟨hyb, hay⟩
        refine ⟨hay, ?_⟩
        rintro (⟨_, rfl⟩ | ⟨rfl, _⟩)
        · exact hyb rfl
        · exact H.loopless.irrefl a hab
    rw [← card_neighborFinset_eq_degree, heq,
      Finset.card_erase_of_mem ((H.mem_neighborFinset a b).mpr hab),
      card_neighborFinset_eq_degree, hreg a]
  have hdeg_other : ∀ x ∈ C, x ≠ a → H'.degree x = 4 := by
    intro x hx hxa
    have hxb : x ≠ b := fun h => hbC (h ▸ hx)
    have heq : H'.neighborFinset x = H.neighborFinset x := by
      ext y
      simp only [mem_neighborFinset, H', SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff,
        Sym2.eq_iff]
      constructor
      · exact fun h => h.1
      · intro hxy
        refine ⟨hxy, ?_⟩
        rintro (⟨rfl, _⟩ | ⟨rfl, _⟩)
        · exact hxa rfl
        · exact hxb rfl
    rw [← card_neighborFinset_eq_degree, heq, card_neighborFinset_eq_degree, hreg x]
  have hsum_even : Even (∑ v : {x : W // x ∈ C}, K.degree v) := by
    rw [K.sum_degrees_eq_twice_card_edges]
    exact ⟨K.edgeFinset.card, by ring⟩
  have hsum_val : ∑ v : {x : W // x ∈ C}, K.degree v = 3 + 4 * (C.card - 1) := by
    have h1 : ∑ v : {x : W // x ∈ C}, K.degree v = ∑ x ∈ C, H'.degree x := by
      calc ∑ v : {x : W // x ∈ C}, K.degree v
          = ∑ v : {x : W // x ∈ C}, H'.degree v.1 := Finset.sum_congr rfl (fun v _ => hKdeg v)
        _ = ∑ x ∈ C, H'.degree x := Finset.sum_coe_sort C (fun x => H'.degree x)
    rw [h1, ← Finset.add_sum_erase C (fun x => H'.degree x) haC, hdeg_a]
    have hrest : ∑ x ∈ C.erase a, H'.degree x = ∑ _x ∈ C.erase a, 4 :=
      Finset.sum_congr rfl (fun x hx => hdeg_other x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx))
    rw [hrest, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem haC]
    ring
  rcases hsum_even with ⟨m, hm⟩
  omega

private lemma card_ge_of_diam_ge_four {W : Type} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hreg : ∀ v, H.degree v = 4)
    (hc4 : ∀ a x b y, H.Adj a x → H.Adj x b → H.Adj b y → H.Adj y a → a = b ∨ x = y)
    {u v : W} (huv_ne : u ≠ v) (huv_nadj : ¬ H.Adj u v)
    (hno2 : ∀ w, ¬ (H.Adj u w ∧ H.Adj w v))
    (hno3 : ∀ w z, ¬ (H.Adj u w ∧ H.Adj w z ∧ H.Adj z v)) :
    18 ≤ Fintype.card W ∧
      ((∀ a b c, H.Adj a b → H.Adj b c → ¬ H.Adj c a) → 22 ≤ Fintype.card W) := by
  let B1 : Finset W := insert u (H.neighborFinset u)
  have hB1_card : B1.card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [mem_neighborFinset]), card_neighborFinset_eq_degree, hreg u]
  let S1 : Finset W := H.neighborFinset v
  have hS1_card : S1.card = 4 := by rw [card_neighborFinset_eq_degree, hreg v]
  let F : W → Finset W := fun x => (H.neighborFinset x).filter (fun y => y ≠ v ∧ y ∉ S1)
  let S2 : Finset W := S1.biUnion F
  have hF_disj : Set.PairwiseDisjoint (S1 : Set W) F := by
    intro x1 hx1 x2 hx2 hne
    change Disjoint (F x1) (F x2)
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    have h1 := Finset.mem_filter.mp hy1
    have h2 := Finset.mem_filter.mp hy2
    have hx1v := (H.mem_neighborFinset v x1).mp hx1
    have hx2v := (H.mem_neighborFinset v x2).mp hx2
    rcases hc4 v x1 y x2 hx1v ((H.mem_neighborFinset x1 y).mp h1.1)
        ((H.mem_neighborFinset x2 y).mp h2.1).symm hx2v.symm with h | h
    · exact h1.2.1 h.symm
    · exact hne h
  have hS2_card : S2.card = ∑ x ∈ S1, (F x).card := Finset.card_biUnion hF_disj
  let B2 : Finset W := insert v (S1 ∪ S2)
  have hv_not : v ∉ S1 ∪ S2 := by
    simp only [Finset.mem_union, S1, S2, Finset.mem_biUnion, F, Finset.mem_filter, mem_neighborFinset]
    rintro (h | ⟨x, _, _, hne, _⟩)
    · exact H.loopless.irrefl v h
    · exact hne rfl
  have hS12_disj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    obtain ⟨x, _, hxy⟩ := Finset.mem_biUnion.mp hy2
    exact (Finset.mem_filter.mp hxy).2.2 hy1
  have hB2_card : B2.card = 5 + S2.card := by
    rw [Finset.card_insert_of_notMem hv_not, Finset.card_union_of_disjoint hS12_disj, hS1_card]
    omega
  have hB12_disj : Disjoint B1 B2 := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    have h1 : a = u ∨ H.Adj u a := by
      simpa [B1, mem_neighborFinset] using ha1
    have h2 : a = v ∨ H.Adj v a ∨ ∃ x, H.Adj v x ∧ H.Adj x a := by
      simp only [B2, Finset.mem_insert, Finset.mem_union, S1, S2, Finset.mem_biUnion, F,
        Finset.mem_filter, mem_neighborFinset] at ha2
      rcases ha2 with rfl | h | ⟨x, hvx, hxa, _, _⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨x, hvx, hxa⟩)
    rcases h1 with rfl | hua
    · rcases h2 with h | h | ⟨x, hvx, hxu⟩
      · exact huv_ne h
      · exact huv_nadj h.symm
      · exact hno2 x ⟨hxu.symm, hvx.symm⟩
    · rcases h2 with rfl | hva | ⟨x, hvx, hxa⟩
      · exact huv_nadj hua
      · exact hno2 a ⟨hua, hva.symm⟩
      · exact hno3 a x ⟨hua, hxa.symm, hvx.symm⟩
  have htot : 10 + S2.card ≤ Fintype.card W := by
    have := Finset.card_le_univ (B1 ∪ B2)
    rw [Finset.card_union_of_disjoint hB12_disj, hB1_card, hB2_card] at this
    omega
  constructor
  · have hFx_ge2 : ∀ x ∈ S1, 2 ≤ (F x).card := by
      intro x hx
      have hvx : H.Adj v x := (H.mem_neighborFinset v x).mp hx
      have hmax1 : ((H.neighborFinset x).filter (fun y => y ∈ S1)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro y1 hy1 y2 hy2
        simp only [Finset.mem_filter, mem_neighborFinset, S1] at hy1 hy2
        exact common_eq hc4 (H.ne_of_adj hvx) hy1.2 hy1.1 hy2.2 hy2.1
      have hsub : (H.neighborFinset x).erase v ⊆ F x ∪ (H.neighborFinset x).filter (fun y => y ∈ S1) := by
        intro y hy
        have ⟨hyv, hxy⟩ := Finset.mem_erase.mp hy
        by_cases hyS : y ∈ S1
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxy, hyS⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxy, hyv, hyS⟩)
      have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      rw [Finset.card_erase_of_mem ((H.mem_neighborFinset x v).mpr hvx.symm),
        card_neighborFinset_eq_degree, hreg x] at hc
      omega
    have hS2_ge8 : 8 ≤ S2.card := by
      rw [hS2_card]
      calc 8 = ∑ _x ∈ S1, 2 := by rw [Finset.sum_const, smul_eq_mul, hS1_card]
        _ ≤ ∑ x ∈ S1, (F x).card := Finset.sum_le_sum hFx_ge2
    omega
  · intro htf
    have hFx_ge3 : ∀ x ∈ S1, 3 ≤ (F x).card := by
      intro x hx
      have hvx : H.Adj v x := (H.mem_neighborFinset v x).mp hx
      have hsub : (H.neighborFinset x).erase v ⊆ F x := by
        intro y hy
        have ⟨hyv, hxy⟩ := Finset.mem_erase.mp hy
        refine Finset.mem_filter.mpr ⟨hxy, hyv, fun hyS => ?_⟩
        exact htf v x y hvx ((H.mem_neighborFinset x y).mp hxy) ((H.mem_neighborFinset v y).mp hyS).symm
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem ((H.mem_neighborFinset x v).mpr hvx.symm),
        card_neighborFinset_eq_degree, hreg x] at hc
      omega
    have hS2_ge12 : 12 ≤ S2.card := by
      rw [hS2_card]
      calc 12 = ∑ _x ∈ S1, 3 := by rw [Finset.sum_const, smul_eq_mul, hS1_card]
        _ ≤ ∑ x ∈ S1, (F x).card := Finset.sum_le_sum hFx_ge3
    omega

/- ### Part 4: Free non-adjacent involution quotient and cycle lifting -/

private lemma quotient_of_involution {W : Type} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hne : Nonempty W) (hreg : ∀ v, H.degree v = 4)
    (hc4 : ∀ a x b y, H.Adj a x → H.Adj x b → H.Adj b y → H.Adj y a → a = b ∨ x = y)
    (σ : H ≃g H) (hinv : ∀ x, σ (σ x) = x) (hfree : ∀ x, σ x ≠ x)
    (hnadj : ∀ x, ¬ H.Adj x (σ x))
    (ih : ∀ (Q : Type) (G : SimpleGraph Q) [Fintype Q] [DecidableRel G.Adj],
      Fintype.card Q < Fintype.card W → Nonempty Q → (∀ q, G.degree q = 4) →
      (∀ a x b y, G.Adj a x → G.Adj x b → G.Adj b y → G.Adj y a → a = b ∨ x = y) →
      ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ G) :
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ H := by
  let S : Setoid W := {
    r := fun x y => x = y ∨ x = σ y
    iseqv := ⟨fun _ => Or.inl rfl,
      fun {x y} h => h.elim (fun e => Or.inl e.symm) (fun e => Or.inr (by rw [e, hinv])),
      fun {x y z} h1 h2 => by
        rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inr rfl
        · exact Or.inl (hinv _)⟩
  }
  let Q := Quotient S
  have : Finite Q := Finite.of_surjective (Quotient.mk S) Quotient.mk_surjective
  let : Fintype Q := Fintype.ofFinite Q
  have : Nonempty W := hne
  have hQne : Nonempty Q := ⟨Quotient.mk S (Classical.arbitrary W)⟩
  have hσ_adj : ∀ x y, H.Adj (σ x) (σ y) ↔ H.Adj x y := fun x y => σ.map_rel_iff
  have hσ_adj_l : ∀ x y, H.Adj (σ x) y ↔ H.Adj x (σ y) := by
    intro x y; rw [← hσ_adj x (σ y), hinv]
  have hno_both : ∀ x y, H.Adj x y → ¬ H.Adj x (σ y) := by
    intro x y h1 h2
    have h3 : H.Adj (σ x) (σ y) := (hσ_adj x y).mpr h1
    have h4 : H.Adj (σ x) y := (hσ_adj_l x y).mpr h2
    rcases hc4 x y (σ x) (σ y) h1 h4.symm h3 h2.symm with h | h
    · exact hfree x h.symm
    · exact hfree y h.symm
  -- Cardinality: every fiber of Quotient.mk S has size 2, so 2 * |Q| = |W|
  have hcard_lt : Fintype.card Q < Fintype.card W := by
    have hfib : ∀ q : Q, (Finset.univ.filter (fun x : W => Quotient.mk S x = q)).card = 2 := by
      intro q
      induction q using Quotient.inductionOn with
      | h x =>
        have heq : Finset.univ.filter (fun y : W => Quotient.mk S y = Quotient.mk S x) = {x, σ x} := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, Quotient.eq]
          rfl
        rw [heq, Finset.card_pair (hfree x).symm]
    have hsum := Finset.card_eq_sum_card_fiberwise (f := Quotient.mk S) (s := Finset.univ)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    have h2 : Fintype.card W = 2 * Fintype.card Q := by
      calc Fintype.card W = (Finset.univ : Finset W).card := rfl
        _ = ∑ q ∈ (Finset.univ : Finset Q), (Finset.univ.filter (fun x => Quotient.mk S x = q)).card := hsum
        _ = ∑ _q ∈ (Finset.univ : Finset Q), 2 := Finset.sum_congr rfl (fun q _ => hfib q)
        _ = 2 * Fintype.card Q := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]; ring
    have hpos : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr hQne
    omega
  -- Quotient simple graph Gq
  let Gq : SimpleGraph Q := {
    Adj := Quotient.lift₂ (fun x y => H.Adj x y ∨ H.Adj x (σ y)) (by
      intro x1 y1 x2 y2 hx hy
      apply propext
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · rw [hinv]; exact or_comm
      · rw [hσ_adj_l, hσ_adj]; exact or_comm
      · rw [hσ_adj, hσ_adj_l, hinv])
    symm := ⟨by
      intro q1 q2
      induction q1 using Quotient.inductionOn with | h x =>
      induction q2 using Quotient.inductionOn with | h y =>
      rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr ((hσ_adj_l y x).mp h.symm)⟩
    loopless := ⟨by
      intro q
      induction q using Quotient.inductionOn with | h x =>
      rintro (h | h)
      · exact H.loopless.irrefl x h
      · exact hnadj x h⟩
  }
  have hGq_adj : ∀ x y : W, Gq.Adj (Quotient.mk S x) (Quotient.mk S y) ↔ H.Adj x y ∨ H.Adj x (σ y) :=
    fun _ _ => Iff.rfl
  -- Unique lifting of edges
  have hlift_edge : ∀ (x : W) (q : Q), Gq.Adj (Quotient.mk S x) q →
      ∃! y : W, Quotient.mk S y = q ∧ H.Adj x y := by
    intro x q hq
    induction q using Quotient.inductionOn with | h z =>
    rcases (hGq_adj x z).mp hq with h1 | h2
    · refine ⟨z, ⟨rfl, h1⟩, ?_⟩
      rintro y ⟨hyq, hxy⟩
      rcases Quotient.exact hyq with hyz | hyz
      · exact hyz
      · rw [hyz] at hxy
        exact absurd hxy (hno_both x z h1)
    · refine ⟨σ z, ⟨Quotient.sound (Or.inr rfl), h2⟩, ?_⟩
      rintro y ⟨hyq, hxy⟩
      rcases Quotient.exact hyq with hyz | hyz
      · rw [hyz] at hxy
        exact absurd hxy (fun h => hno_both x z h h2)
      · exact hyz
  -- Gq is 4-regular
  have hGq_reg : ∀ q : Q, Gq.degree q = 4 := by
    intro q
    induction q using Quotient.inductionOn with | h x =>
    rw [← card_neighborFinset_eq_degree, ← hreg x, ← card_neighborFinset_eq_degree]
    symm
    refine Finset.card_bij (fun y _ => Quotient.mk S y) ?_ ?_ ?_
    · intro y hy
      exact (Gq.mem_neighborFinset _ _).mpr ((hGq_adj x y).mpr (Or.inl ((H.mem_neighborFinset x y).mp hy)))
    · intro y1 hy1 y2 hy2 heq
      have h1 := (H.mem_neighborFinset x y1).mp hy1
      have h2 := (H.mem_neighborFinset x y2).mp hy2
      rcases Quotient.exact heq with hy12 | hy12
      · exact hy12
      · rw [hy12] at h1
        exact absurd h1 (hno_both x y2 h2)
    · intro q' hq'
      obtain ⟨y, ⟨hyq, hxy⟩, _⟩ := hlift_edge x q' ((Gq.mem_neighborFinset _ _).mp hq')
      exact ⟨y, (H.mem_neighborFinset x y).mpr hxy, hyq⟩
  -- Cycle lifting: any m-cycle (m ≥ 3) in Gq lifts to an m-cycle or 2m-cycle in H
  have hlift_cyc : ∀ m, 3 ≤ m → cycleGraph m ⊑ Gq →
      cycleGraph m ⊑ H ∨ cycleGraph (2 * m) ⊑ H := by
    intro m hm hcyc
    obtain ⟨c, hper, hadj, hinj⟩ :=
      OMA.R_Erdos64_erdos_64_R1_H2_R2.seq_of_copy Gq m (by omega) hcyc
    have hper_mod : ∀ n, c (n % m) = c n := by
      intro n
      have hdiv : n = n % m + m * (n / m) := (Nat.mod_add_div n m).symm
      conv_rhs => rw [hdiv]
      generalize n / m = q
      induction q with
      | zero => simp
      | succ q ih => rw [Nat.mul_succ, ← add_assoc, hper, ih]
    let x0 : W := Quotient.out (c 0)
    have hx0 : Quotient.mk S x0 = c 0 := Quotient.out_eq (c 0)
    -- Recursively lift the periodic walk c : ℕ → Q to H
    let step : ∀ (n : ℕ), {x : W // Quotient.mk S x = c n} → {x : W // Quotient.mk S x = c (n + 1)} :=
      fun n ⟨x, hx⟩ =>
        let hq : Gq.Adj (Quotient.mk S x) (c (n + 1)) := hx.symm ▸ hadj n
        let hex := hlift_edge x (c (n + 1)) hq
        ⟨Classical.choose hex, (Classical.choose_spec hex).1.1⟩
    let liftSub : ∀ n : ℕ, {x : W // Quotient.mk S x = c n} :=
      @Nat.rec (fun n => {x : W // Quotient.mk S x = c n}) ⟨x0, hx0⟩ step
    let d : ℕ → W := fun n => (liftSub n).1
    have hd_proj : ∀ n, Quotient.mk S (d n) = c n := fun n => (liftSub n).2
    have hd_adj : ∀ n, H.Adj (d n) (d (n + 1)) := by
      intro n
      change H.Adj (liftSub n).1 (step n (liftSub n)).1
      exact (Classical.choose_spec (hlift_edge (liftSub n).1 (c (n + 1)) ((liftSub n).2.symm ▸ hadj n))).1.2
    have hd_uniq : ∀ n y, Quotient.mk S y = c (n + 1) → H.Adj (d n) y → y = d (n + 1) := by
      intro n y hyq hadjy
      have hspec := Classical.choose_spec (hlift_edge (d n) (c (n + 1)) ((hd_proj n).symm ▸ hadj n))
      exact hspec.2 y ⟨hyq, hadjy⟩
    have hm_eq : Quotient.mk S (d m) = Quotient.mk S (d 0) := by
      rw [hd_proj m, hd_proj 0, ← Nat.zero_add m, hper 0]
    rcases Quotient.exact hm_eq with hsame | hflip
    · left
      have hd_per : ∀ n, d (n + m) = d n := by
        intro n
        induction n with
        | zero => simpa using hsame
        | succ n ih =>
          have hq : Quotient.mk S (d (n + 1 + m)) = c (n + 1) := by
            rw [hd_proj, show n + 1 + m = (n + 1) + m by omega, hper]
          have ha : H.Adj (d n) (d (n + 1 + m)) := by
            rw [← ih, show n + 1 + m = (n + m) + 1 by omega]
            exact hd_adj (n + m)
          exact hd_uniq n (d (n + 1 + m)) hq ha
      apply OMA.R_Erdos64_erdos_64_R1_H2_R2.copy_of_periodic H m (by omega) d hd_per hd_adj
      intro a b ha hb hab
      exact hinj a b ha hb (by rw [← hd_proj a, ← hd_proj b, hab])
    · right
      have hd_shift : ∀ n, d (n + m) = σ (d n) := by
        intro n
        induction n with
        | zero => simpa using hflip
        | succ n ih =>
          have hq : Quotient.mk S (σ (d (n + 1 + m))) = c (n + 1) := by
            have : Quotient.mk S (σ (d (n + 1 + m))) = Quotient.mk S (d (n + 1 + m)) :=
              Quotient.sound (Or.inr rfl)
            rw [this, hd_proj, show n + 1 + m = (n + 1) + m by omega, hper]
          have ha : H.Adj (d n) (σ (d (n + 1 + m))) := by
            rw [← hσ_adj_l, ← ih, show n + 1 + m = (n + m) + 1 by omega]
            exact hd_adj (n + m)
          have h1 : σ (d (n + 1 + m)) = d (n + 1) := hd_uniq n _ hq ha
          rw [← h1, hinv]
      have hd_per2 : ∀ n, d (n + 2 * m) = d n := by
        intro n
        rw [show n + 2 * m = (n + m) + m by omega, hd_shift, hd_shift, hinv]
      apply OMA.R_Erdos64_erdos_64_R1_H2_R2.copy_of_periodic H (2 * m) (by omega) d hd_per2 hd_adj
      intro a b ha hb hab
      have hproj : c (a % m) = c (b % m) := by
        rw [hper_mod, hper_mod, ← hd_proj a, ← hd_proj b, hab]
      have hmod : a % m = b % m := hinj _ _ (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hproj
      by_contra hne_ab
      rcases lt_or_gt_of_ne hne_ab with hlt | hgt
      · have hba : b = a + m := by
          rw [mod_of_lt_two_mul ha, mod_of_lt_two_mul hb] at hmod
          split_ifs at hmod <;> omega
        rw [hba, hd_shift] at hab
        exact hfree (d a) hab.symm
      · have hab' : a = b + m := by
          rw [mod_of_lt_two_mul ha, mod_of_lt_two_mul hb] at hmod
          split_ifs at hmod <;> omega
        rw [hab', hd_shift] at hab
        exact hfree (d b) hab
  -- Apply IH or C4 lifting
  by_cases hGqc4 : ∀ a x b y, Gq.Adj a x → Gq.Adj x b → Gq.Adj b y → Gq.Adj y a → a = b ∨ x = y
  · obtain ⟨k, hk, hcyc⟩ := ih Q Gq hcard_lt hQne hGq_reg hGqc4
    have h4 : 3 ≤ 2 ^ k := by
      calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rcases hlift_cyc (2 ^ k) h4 hcyc with h1 | h2
    · exact ⟨k, hk, h1⟩
    · exact ⟨k + 1, by omega, by rw [pow_succ, mul_comm]; exact h2⟩
  · push Not at hGqc4
    obtain ⟨a, x, b, y, h1, h2, h3, h4, hab, hxy⟩ := hGqc4
    have hc4_Gq : cycleGraph 4 ⊑ Gq :=
      OMA.R_Erdos64_erdos_64_R1_H2_R2.copy_four Gq a x b y h1 h2 h3 h4 hab hxy
    rcases hlift_cyc 4 (by norm_num) hc4_Gq with h4H | h8H
    · exact ⟨2, le_rfl, h4H⟩
    · exact ⟨3, by norm_num, h8H⟩

end Helpers

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H2_R2.H2 := by
  intro h1 h2 W0 H0 _ _ hne0 hreg0 hc40
  suffices hall : ∀ (n : ℕ) (W : Type) (H : SimpleGraph W) [Fintype W] [DecidableRel H.Adj],
      Fintype.card W = n → Nonempty W → (∀ v, H.degree v = 4) →
      (∀ a x b y, H.Adj a x → H.Adj x b → H.Adj b y → H.Adj y a → a = b ∨ x = y) →
      ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2 ^ k) ⊑ H by
    exact hall (Fintype.card W0) W0 H0 rfl hne0 hreg0 hc40
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W H _ _ hcard hne hreg hc4
    -- 1. Reduce to connected graphs
    by_cases hconn : H.Connected
    swap
    · obtain ⟨w0⟩ := hne
      let C := {x : W // H.Reachable w0 x}
      let : Fintype C := Subtype.fintype _
      let Hc : SimpleGraph C := H.induce {x : W | H.Reachable w0 x}
      have hC_ne : Nonempty C := ⟨⟨w0, SimpleGraph.Reachable.refl w0⟩⟩
      have hC_lt : Fintype.card C < n := by
        rw [← hcard]
        have hex_out : ∃ y : W, ¬ H.Reachable w0 y := by
          by_contra hall_r
          push Not at hall_r
          exact hconn { preconnected := fun x y => (hall_r x).symm.trans (hall_r y), nonempty := ⟨w0⟩ }
        obtain ⟨y, hy⟩ := hex_out
        have hlt := Fintype.card_subtype_lt hy
        exact hlt
      have hC_reg : ∀ v : C, Hc.degree v = 4 := by
        intro ⟨x, hx⟩
        rw [← card_neighborFinset_eq_degree, ← hreg x, ← card_neighborFinset_eq_degree]
        refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
        · intro y hy
          exact (H.mem_neighborFinset x y.1).mpr ((Hc.mem_neighborFinset ⟨x, hx⟩ y).mp hy)
        · intro y1 _ y2 _ heq; exact Subtype.ext heq
        · intro y hy
          have hxy := (H.mem_neighborFinset x y).mp hy
          exact ⟨⟨y, hx.trans hxy.reachable⟩, (Hc.mem_neighborFinset ⟨x, hx⟩ ⟨y, hx.trans hxy.reachable⟩).mpr hxy, rfl⟩
      have hC_c4 : ∀ a x b y : C, Hc.Adj a x → Hc.Adj x b → Hc.Adj b y → Hc.Adj y a → a = b ∨ x = y := by
        intro a x b y h1' h2' h3' h4'
        rcases hc4 a.1 x.1 b.1 y.1 h1' h2' h3' h4' with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
      obtain ⟨k, hk, hcyc⟩ := ih (Fintype.card C) hC_lt C Hc rfl hC_ne hC_reg hC_c4
      obtain ⟨f⟩ := hcyc
      exact ⟨k, hk, ⟨⟨⟨fun i => (f.toHom i).1, fun {_ _} h => f.toHom.map_adj h⟩,
        fun _ _ h => f.injective' (Subtype.ext h)⟩⟩⟩
    -- 2. Check for C8
    by_cases h8 : cycleGraph 8 ⊑ H
    · exact ⟨3, by norm_num, h8⟩
    -- 3. Check for free non-adjacent involution
    by_cases hinv_ex : ∃ σ : H ≃g H, (∀ x, σ (σ x) = x) ∧ (∀ x, σ x ≠ x) ∧ (∀ x, ¬ H.Adj x (σ x))
    · obtain ⟨σ, hinv, hfree, hnadj⟩ := hinv_ex
      exact quotient_of_involution H hne hreg hc4 σ hinv hfree hnadj
        (fun Q G _ _ hlt hQne hQreg hQc4 => ih (Fintype.card Q) (hcard ▸ hlt) Q G rfl hQne hQreg hQc4)
    -- 4. Check if all edges lie in triangles (claw-free / Shauger-Nowbandegani elimination)
    by_cases hall_tri : ∀ a b, H.Adj a b → ∃ z, H.Adj a z ∧ H.Adj b z
    · exact exists_pow2_of_all_triangulated H hne hreg hc4 hall_tri
    -- 5. Extract non-triangulated edge, induced claw, diameter ≥ 4, and bridgelessness
    push Not at hall_tri
    obtain ⟨u, v, huv, hnt⟩ := hall_tri
    have hnt' : ∀ w, ¬ (H.Adj u w ∧ H.Adj v w) := fun w ⟨h1, h2⟩ => hnt w h1 h2
    obtain ⟨a, b, c, hua, hub, huc, hab, hbc, hac, hnab, hnbc, hnac⟩ :=
      exists_claw_of_non_triangulated H hreg hc4 huv hnt'
    have hclaw : ∃ v0 a b c : W, H.Adj v0 a ∧ H.Adj v0 b ∧ H.Adj v0 c ∧
        a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ ¬ H.Adj a b ∧ ¬ H.Adj b c ∧ ¬ H.Adj a c :=
      ⟨u, a, b, c, hua, hub, huc, hab, hbc, hac, hnab, hnbc, hnac⟩
    have hdiam4 := exists_diam_ge_four H hreg hc4 h8 huv hnt'
    obtain ⟨dx, dy, hdxne, hdxnadj, hdxno2, hdxno3⟩ := hdiam4
    have hcards := card_ge_of_diam_ge_four H hreg hc4 hdxne hdxnadj hdxno2 hdxno3
    have hnobr : ∀ ⦃x y⦄, H.Adj x y → ¬ H.IsBridge s(x, y) := fun _ _ hxy =>
      no_bridge_of_four_regular H hreg hxy
    -- 6. Split by triangle-free vs has-a-triangle
    by_cases htf : ∀ x y z, H.Adj x y → H.Adj y z → ¬ H.Adj z x
    · exact h1 W H hconn hreg hnobr htf hc4 h8 ⟨dx, dy, hdxne, hdxnadj, hdxno2, hdxno3⟩
        (hcards.2 htf) hinv_ex
    · push Not at htf
      exact h2 W H hconn hreg hnobr htf hc4 h8 ⟨u, v, huv, hnt'⟩ hclaw
        ⟨dx, dy, hdxne, hdxnadj, hdxno2, hdxno3⟩ hcards.1 hinv_ex

end OMA.R_Erdos64_erdos_64_R1_H2_R2_H2_R1

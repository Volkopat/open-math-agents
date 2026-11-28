import OMAStatements.S_arxiv_1803_02550
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Broadcast domination versus multipacking

Proof of Conjecture 2 of Beaudou, Brewster, and Foucaud (arXiv:1803.02550):
for every finite connected graph `G`, `broadcastNumber G ≤ 2 * multipackingNumber G`.
Formalizes the constructive two-path proof of Sk Samim Islam (arXiv:2608.20036).
-/

namespace OMA.P_arxiv_1803_02550

open OMA.S_arxiv_1803_02550

section Core

variable {n : ℕ} {G : SimpleGraph (Fin n)}

private lemma bc_le (f : Fin n → ℕ) (hf : IsDominatingBroadcast G f) :
    broadcastNumber G ≤ ∑ v, f v := Nat.sInf_le ⟨f, hf, rfl⟩

private lemma le_mp (P : Finset (Fin n)) (hP : IsMultipacking G P) :
    P.card ≤ multipackingNumber G :=
  le_csSup ⟨n, by rintro _ ⟨Q, _, rfl⟩; exact (Finset.card_le_univ Q).trans (by simp)⟩ ⟨P, hP, rfl⟩

private lemma mp_of_pair (hc : G.Connected) (M : Finset (Fin n))
    (h : ∀ U ⊆ M, 2 ≤ U.card → ∃ u ∈ U, ∃ v ∈ U, 2 * U.card - 1 ≤ G.dist u v) :
    IsMultipacking G M := by
  intro v r hr
  set U := M.filter (fun u => G.dist v u ≤ r)
  by_contra hlt; push Not at hlt
  obtain ⟨u, hu, w, hw, hd⟩ := h U (Finset.filter_subset _ M) (by omega)
  have h1 := (Finset.mem_filter.mp hu).2
  have h2 := (Finset.mem_filter.mp hw).2
  have h3 : G.dist u w ≤ G.dist u v + G.dist v w := hc.dist_triangle
  have h4 : G.dist u v = G.dist v u := G.dist_comm
  omega

private noncomputable def ecc (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ :=
  Finset.univ.sup (fun u => G.dist v u)

private lemma dist_le_ecc (v u : Fin n) : G.dist v u ≤ ecc G v :=
  Finset.le_sup (f := fun u => G.dist v u) (Finset.mem_univ u)

private noncomputable def rad (G : SimpleGraph (Fin n)) (hc : G.Connected) : ℕ :=
  have : Nonempty (Fin n) := hc.nonempty
  Finset.univ.inf' Finset.univ_nonempty (ecc G)

private lemma rad_le_ecc (hc : G.Connected) (v : Fin n) : rad G hc ≤ ecc G v := by
  have : Nonempty (Fin n) := hc.nonempty
  exact Finset.inf'_le (f := ecc G) (Finset.mem_univ v)

private lemma sum_ite_one (c : Fin n) (a : ℕ) : (∑ v : Fin n, if v = c then a else 0) = a := by
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ h; simp [h]
  · intro h; exact (h (Finset.mem_univ c)).elim

private lemma exists_uncovered (u v : Fin n) (huv : u ≠ v) (r1 r2 : ℕ)
    (hr1 : 0 < r1) (hr2 : 0 < r2) (hbc : r1 + r2 < broadcastNumber G) :
    ∃ b : Fin n, r1 + 1 ≤ G.dist b u ∧ r2 + 1 ≤ G.dist b v := by
  let f : Fin n → ℕ := fun w => if w = u then r1 else if w = v then r2 else 0
  have hsum : ∑ w : Fin n, f w = r1 + r2 := by
    have h1 : ∀ w : Fin n, f w = (if w = u then r1 else 0) + (if w = v then r2 else 0) := by
      intro w; by_cases h : w = u
      · subst h; simp [f, huv]
      · simp [f, h]
    simp_rw [h1, Finset.sum_add_distrib, sum_ite_one]
  have hnot : ¬ IsDominatingBroadcast G f := fun hf => by have := bc_le f hf; omega
  unfold IsDominatingBroadcast at hnot; push Not at hnot
  obtain ⟨b, hb⟩ := hnot
  have h1 := hb u (by simp [f, hr1])
  have h2 := hb v (by simp [f, huv.symm, hr2])
  simp [f] at h1; simp [f, huv.symm] at h2
  exact ⟨b, by omega, by omega⟩

private lemma walk_dist_le (hc : G.Connected) {u v : Fin n} (p : G.Walk u v) :
    ∀ k i, i + k ≤ p.length → G.dist (p.getVert i) (p.getVert (i + k)) ≤ k := by
  intro k; induction k with
  | zero => intro i _; simp
  | succ k ih =>
    intro i hik
    have hstep : G.dist (p.getVert (i + k)) (p.getVert (i + k + 1)) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr (p.adj_getVert_succ (by omega))
    have htri : G.dist (p.getVert i) (p.getVert (i + k + 1)) ≤
        G.dist (p.getVert i) (p.getVert (i + k)) +
        G.dist (p.getVert (i + k)) (p.getVert (i + k + 1)) := hc.dist_triangle
    have := ih i (by omega)
    have heq : i + (k + 1) = i + k + 1 := by omega
    rw [heq]; omega

private lemma exists_iso (hc : G.Connected) (u : Fin n) (R : ℕ) (hR : R ≤ ecc G u) :
    ∃ x : ℕ → Fin n, x 0 = u ∧ ∀ i j, i ≤ j → j ≤ R → G.dist (x i) (x j) = j - i := by
  have : Nonempty (Fin n) := hc.nonempty
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (fun w => G.dist u w)
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
  refine ⟨p.getVert, p.getVert_zero, fun i j hij hj => ?_⟩
  have hL : R ≤ p.length := by change ecc G u = G.dist u v at hv; omega
  have h1 := walk_dist_le hc p (j - i) i (by omega)
  rw [Nat.add_sub_of_le hij] at h1
  have h2 := walk_dist_le hc p i 0 (by omega); simp only [zero_add, p.getVert_zero] at h2
  have h3 := walk_dist_le hc p (p.length - j) j (by omega)
  rw [Nat.add_sub_of_le (by omega), p.getVert_length] at h3
  have ht1 : G.dist u v ≤ G.dist u (p.getVert i) + G.dist (p.getVert i) v := hc.dist_triangle
  have ht2 : G.dist (p.getVert i) v ≤ G.dist (p.getVert i) (p.getVert j) + G.dist (p.getVert j) v :=
    hc.dist_triangle
  omega

private lemma iso_symm {x : ℕ → Fin n} {R : ℕ}
    (hx : ∀ i j, i ≤ j → j ≤ R → G.dist (x i) (x j) = j - i) {i j : ℕ} (hi : i ≤ R) (hj : j ≤ R) :
    G.dist (x i) (x j) = (i - j) + (j - i) := by
  rcases le_total i j with h | h
  · rw [hx i j h hj]; omega
  · rw [G.dist_comm, hx j i h hi]; omega

private lemma cross_lb (hc : G.Connected) {x z : ℕ → Fin n} {R h : ℕ}
    (hx : ∀ i j, i ≤ j → j ≤ R → G.dist (x i) (x j) = j - i)
    (hz : ∀ i j, i ≤ j → j ≤ R → G.dist (z i) (z j) = j - i)
    (hz0 : z 0 = x h) (hh : h ≤ R) {i j : ℕ} (hi : i ≤ R) (hj : j ≤ R) :
    j ≤ G.dist (x i) (z j) + ((i - h) + (h - i)) := by
  have h1 : G.dist (x h) (z j) = j := by rw [← hz0]; simpa using hz 0 j (Nat.zero_le _) hj
  have h2 : G.dist (x h) (x i) = (i - h) + (h - i) := by rw [iso_symm hx hh hi]; omega
  have ht : G.dist (x h) (z j) ≤ G.dist (x h) (x i) + G.dist (x i) (z j) := hc.dist_triangle
  omega

private lemma card_pair_le {α : Type*} [DecidableEq α] {T : Finset α} {a b : α} (h : T ⊆ {a, b}) :
    T.card ≤ 2 := by
  have := (Finset.card_le_card h).trans (Finset.card_insert_le a {b}); simp at this; exact this

private lemma straddle_span (I : Finset ℕ) (k s : ℕ) (hI : I.Nonempty)
    (hlt : ∃ i ∈ I, i < k) (hgt : ∃ i ∈ I, k < i) (hs : ∀ i ∈ I, s ≤ (i - k) + (k - i)) :
    2 * s + I.card - 2 ≤ I.max' hI - I.min' hI := by
  let L := I.filter (· < k); let U := I.filter (k < ·)
  have hd : Disjoint L U := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
  have hml : ∀ a ∈ I, I.min' hI ≤ a := fun a ha => Finset.min'_le I a ha
  have hmu : ∀ a ∈ I, a ≤ I.max' hI := fun a ha => Finset.le_max' I a ha
  obtain ⟨al, hal, halk⟩ := hlt; obtain ⟨ag, hag, hkag⟩ := hgt
  have hmin_lt : I.min' hI < k := lt_of_le_of_lt (hml al hal) halk
  have hmax_gt : k < I.max' hI := lt_of_lt_of_le hkag (hmu ag hag)
  by_cases hk : k ∈ I
  · have hs0 : s = 0 := by have := hs k hk; omega
    have hL : L.card ≤ k - I.min' hI := by
      have := Finset.card_le_card (show L ⊆ Finset.Icc (I.min' hI) (k - 1) from fun a ha =>
        Finset.mem_Icc.mpr ⟨hml a (Finset.mem_filter.mp ha).1, by have := (Finset.mem_filter.mp ha).2; omega⟩)
      rw [Nat.card_Icc] at this; omega
    have hU : U.card ≤ I.max' hI - k := by
      have := Finset.card_le_card (show U ⊆ Finset.Icc (k + 1) (I.max' hI) from fun a ha =>
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_filter.mp ha).2; omega, hmu a (Finset.mem_filter.mp ha).1⟩)
      rw [Nat.card_Icc] at this; omega
    have hc : I.card ≤ 1 + L.card + U.card := by
      have hcov : I ⊆ insert k (L ∪ U) := fun a ha => by
        simp only [Finset.mem_insert, Finset.mem_union, L, U, Finset.mem_filter]
        rcases lt_trichotomy a k with h | rfl | h
        · exact Or.inr (Or.inl ⟨ha, h⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨ha, h⟩)
      have h1 := (Finset.card_le_card hcov).trans (Finset.card_insert_le k (L ∪ U))
      rw [Finset.card_union_of_disjoint hd] at h1; omega
    omega
  · have hsal : s ≤ k - al := by have := hs al hal; omega
    have hsag : k + s ≤ ag := by have := hs ag hag; omega
    have hL : L.card ≤ (k - s) - I.min' hI + 1 := by
      have := Finset.card_le_card (show L ⊆ Finset.Icc (I.min' hI) (k - s) from fun a ha => by
        have hf := Finset.mem_filter.mp ha; have := hs a hf.1
        exact Finset.mem_Icc.mpr ⟨hml a hf.1, by omega⟩)
      rw [Nat.card_Icc] at this; have := hml al hal; omega
    have hU : U.card ≤ I.max' hI - (k + s) + 1 := by
      have := Finset.card_le_card (show U ⊆ Finset.Icc (k + s) (I.max' hI) from fun a ha => by
        have hf := Finset.mem_filter.mp ha; have := hs a hf.1
        exact Finset.mem_Icc.mpr ⟨by omega, hmu a hf.1⟩)
      rw [Nat.card_Icc] at this; have := hmu ag hag; omega
    have hc : I.card ≤ L.card + U.card := by
      have hcov : I ⊆ L ∪ U := fun a ha => by
        simp only [Finset.mem_union, L, U, Finset.mem_filter]
        rcases lt_trichotomy a k with h | rfl | h
        · exact Or.inl ⟨ha, h⟩
        · exact (hk ha).elim
        · exact Or.inr ⟨ha, h⟩
      have h1 := Finset.card_le_card hcov; rwa [Finset.card_union_of_disjoint hd] at h1
    have := hml al hal; have := hmu ag hag; omega

private lemma card_span (S : Finset ℕ) (hS : S.Nonempty) : S.card ≤ S.max' hS - S.min' hS + 1 := by
  have hle := Finset.min'_le S (S.max' hS) (Finset.max'_mem S hS)
  have := Finset.card_le_card (show S ⊆ Finset.Icc (S.min' hS) (S.max' hS) from fun a ha =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le S a ha, Finset.le_max' S a ha⟩)
  rw [Nat.card_Icc] at this; omega

end Core

section TwoPath

variable {n : ℕ} {G : SimpleGraph (Fin n)}

private def setA (x : ℕ → Fin n) (R : ℕ) : Finset (Fin n) :=
  (Finset.range (R / 3 + 1)).image (fun i => x (3 * i))

private def setB (z : ℕ → Fin n) (R : ℕ) : Finset (Fin n) :=
  (Finset.range ((R - 1) / 6)).image (fun j => z (R - 3 * j))

private def setM (x z : ℕ → Fin n) (R : ℕ) : Finset (Fin n) := setA x R ∪ setB z R

private lemma injA {x : ℕ → Fin n} {R : ℕ}
    (hx : ∀ i j, i ≤ j → j ≤ R → G.dist (x i) (x j) = j - i) :
    Set.InjOn (fun i => x (3 * i)) (Finset.range (R / 3 + 1)) := fun i₁ h₁ i₂ h₂ heq => by
  dsimp only at heq; simp only [Finset.coe_range, Set.mem_Iio] at h₁ h₂
  have h0 : G.dist (x (3 * i₁)) (x (3 * i₂)) = 0 := by rw [heq, G.dist_self]
  rw [iso_symm hx (by omega) (by omega)] at h0; omega

private lemma injB {z : ℕ → Fin n} {R : ℕ}
    (hz : ∀ i j, i ≤ j → j ≤ R → G.dist (z i) (z j) = j - i) :
    Set.InjOn (fun j => z (R - 3 * j)) (Finset.range ((R - 1) / 6)) := fun j₁ h₁ j₂ h₂ heq => by
  dsimp only at heq; simp only [Finset.coe_range, Set.mem_Iio] at h₁ h₂
  have h0 : G.dist (z (R - 3 * j₁)) (z (R - 3 * j₂)) = 0 := by rw [heq, G.dist_self]
  rw [iso_symm hz (by omega) (by omega)] at h0; omega

private lemma disjAB {x z : ℕ → Fin n} {R : ℕ} (hR : 1 ≤ R)
    (hx : ∀ i j, i ≤ j → j ≤ R → G.dist (x i) (x j) = j - i)
    (hz : ∀ i j, i ≤ j → j ≤ R → G.dist (z i) (z j) = j - i)
    (hz0 : z 0 = x (3 * (R / 6))) : Disjoint (setA x R) (setB z R) := by
  rw [Finset.disjoint_left]; intro v hA hB
  rcases Finset.mem_image.mp hA with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hB with ⟨j, hj, heq⟩
  rw [Finset.mem_range] at hi hj
  have h1 : G.dist (x (3 * (R / 6))) (x (3 * i)) = (3 * i - 3 * (R / 6)) + (3 * (R / 6) - 3 * i) := by
    rw [iso_symm hx (by omega) (by omega)]; omega
  have h2 : G.dist (z 0) (z (R - 3 * j)) = R - 3 * j := by simpa using hz 0 (R - 3 * j) (Nat.zero_le _) (by omega)
  rw [hz0, heq] at h2; omega

private lemma card_setM {x z : ℕ → Fin n} {R : ℕ} (hR : 1 ≤ R)
    (hx : ∀ i j, i ≤ j → j ≤ R → G.dist (x i) (x j) = j - i)
    (hz : ∀ i j, i ≤ j → j ≤ R → G.dist (z i) (z j) = j - i)
    (hz0 : z 0 = x (3 * (R / 6))) :
    (setM x z R).card = R / 3 + 1 + (R - 1) / 6 := by
  rw [setM, Finset.card_union_of_disjoint (disjAB hR hx hz hz0),
    setA, Finset.card_image_of_injOn (injA hx), Finset.card_range,
    setB, Finset.card_image_of_injOn (injB hz), Finset.card_range]

/-- Unified distance analysis for any bounded-diameter subset `U ⊆ setM x z R`. -/
private lemma setM_diam_cases (hc : G.Connected) {x z : ℕ → Fin n} {R bound : ℕ} (hR : 1 ≤ R)
    (hx : ∀ i j, i ≤ j → j ≤ R → G.dist (x i) (x j) = j - i)
    (hz : ∀ i j, i ≤ j → j ≤ R → G.dist (z i) (z j) = j - i)
    (hz0 : z 0 = x (3 * (R / 6)))
    {U : Finset (Fin n)} (hU : U ⊆ setM x z R) (hU1 : 1 ≤ U.card)
    (hb : ∀ u ∈ U, ∀ v ∈ U, G.dist u v ≤ bound) :
    3 * (U.card - 1) ≤ bound ∨
    (let I := (Finset.range (R / 3 + 1)).filter (fun i => x (3 * i) ∈ U)
     let J := (Finset.range ((R - 1) / 6)).filter (fun j => z (R - 3 * j) ∈ U)
     U.card = I.card + J.card ∧ 1 ≤ I.card ∧ 1 ≤ J.card ∧ I.card ≤ R / 3 + 1 ∧ J.card ≤ (R - 1) / 6 ∧
     ∃ s : ℕ, (∀ i ∈ I, s ≤ (i - R / 6) + (R / 6 - i)) ∧
       R + 3 * J.card ≤ 3 * ((R - 1) / 6) + bound + 3 * s ∧
       (I.card + s ≤ R / 3 - R / 6 + 1 ∨ 3 * (2 * s + I.card - 2) ≤ bound)) := by
  set k := R / 6; set p := R / 3; set l := (R - 1) / 6
  set I := (Finset.range (p + 1)).filter (fun i => x (3 * i) ∈ U)
  set J := (Finset.range l).filter (fun j => z (R - 3 * j) ∈ U)
  have hcard : U.card = I.card + J.card := by
    have hUA : U ∩ setA x R = I.image (fun i => x (3 * i)) := by
      ext v; simp only [Finset.mem_inter, setA, Finset.mem_image, I, Finset.mem_filter]
      exact ⟨fun ⟨h1, i, h2, h3⟩ => ⟨i, ⟨h2, h3 ▸ h1⟩, h3⟩, fun ⟨i, ⟨h2, h1⟩, h3⟩ => ⟨h3 ▸ h1, i, h2, h3⟩⟩
    have hUB : U ∩ setB z R = J.image (fun j => z (R - 3 * j)) := by
      ext v; simp only [Finset.mem_inter, setB, Finset.mem_image, J, Finset.mem_filter]
      exact ⟨fun ⟨h1, j, h2, h3⟩ => ⟨j, ⟨h2, h3 ▸ h1⟩, h3⟩, fun ⟨j, ⟨h2, h1⟩, h3⟩ => ⟨h3 ▸ h1, j, h2, h3⟩⟩
    have hUeq : U = (U ∩ setA x R) ∪ (U ∩ setB z R) := by
      ext v; simp only [Finset.mem_union, Finset.mem_inter]
      exact ⟨fun hv => (Finset.mem_union.mp (hU hv)).imp (⟨hv, ·⟩) (⟨hv, ·⟩), fun h => h.elim And.left And.left⟩
    have hdisj : Disjoint (U ∩ setA x R) (U ∩ setB z R) :=
      (disjAB hR hx hz hz0).mono Finset.inter_subset_right Finset.inter_subset_right
    have hcA : (U ∩ setA x R).card = I.card := by
      rw [hUA, Finset.card_image_of_injOn ((injA hx).mono fun a ha => (Finset.mem_filter.mp ha).1)]
    have hcB : (U ∩ setB z R).card = J.card := by
      rw [hUB, Finset.card_image_of_injOn ((injB hz).mono fun a ha => (Finset.mem_filter.mp ha).1)]
    rw [hUeq, Finset.card_union_of_disjoint hdisj, hcA, hcB]
  by_cases hJ : J = ∅
  · left
    have hIc : I.card = U.card := by rw [hJ, Finset.card_empty] at hcard; omega
    have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
    set imin := I.min' hIne; set imax := I.max' hIne
    have hm1 := Finset.mem_filter.mp (Finset.min'_mem I hIne)
    have hm2 := Finset.mem_filter.mp (Finset.max'_mem I hIne)
    have hsp := card_span I hIne
    have hd := hx (3 * imin) (3 * imax) (Nat.mul_le_mul_left 3 (Finset.min'_le I imax (Finset.max'_mem I hIne)))
      (by have := Finset.mem_range.mp hm2.1; omega)
    have hle : G.dist (x (3 * imin)) (x (3 * imax)) ≤ bound := hb _ hm1.2 _ hm2.2
    omega
  · by_cases hI : I = ∅
    · left
      have hJc : J.card = U.card := by rw [hI, Finset.card_empty] at hcard; omega
      have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
      set jmin := J.min' hJne; set jmax := J.max' hJne
      have hm1 := Finset.mem_filter.mp (Finset.min'_mem J hJne)
      have hm2 := Finset.mem_filter.mp (Finset.max'_mem J hJne)
      have hsp := card_span J hJne
      have hjle := Finset.min'_le J jmax (Finset.max'_mem J hJne)
      have hrm := Finset.mem_range.mp hm2.1
      have hd := hz (R - 3 * jmax) (R - 3 * jmin) (by omega) (by omega)
      have hle : G.dist (z (R - 3 * jmax)) (z (R - 3 * jmin)) ≤ bound := hb _ hm2.2 _ hm1.2
      omega
    · right
      have hIne := Finset.nonempty_iff_ne_empty.mpr hI
      have hJne := Finset.nonempty_iff_ne_empty.mpr hJ
      have hIpos := Finset.one_le_card.mpr hIne; have hJpos := Finset.one_le_card.mpr hJne
      have hIl : I.card ≤ p + 1 := (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
      have hJl : J.card ≤ l := (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
      set jmin := J.min' hJne
      have hjm := Finset.mem_filter.mp (Finset.min'_mem J hJne)
      have hjmlt : jmin < l := Finset.mem_range.mp hjm.1
      have hju : jmin + J.card ≤ l := by
        have := Finset.card_le_card (show J ⊆ Finset.Ico jmin l from fun a ha =>
          Finset.mem_Ico.mpr ⟨Finset.min'_le J a ha, Finset.mem_range.mp (Finset.mem_filter.mp ha).1⟩)
        rw [Nat.card_Ico] at this; omega
      obtain ⟨i₀, hi₀, hsmin⟩ := Finset.exists_min_image I (fun i => (i - k) + (k - i)) hIne
      set s := (i₀ - k) + (k - i₀)
      have hi₀f := Finset.mem_filter.mp hi₀
      have hi₀lt := Finset.mem_range.mp hi₀f.1
      have hcr : R - 3 * jmin ≤ G.dist (x (3 * i₀)) (z (R - 3 * jmin)) + 3 * s := by
        have := cross_lb hc hx hz hz0 (by omega) (i := 3 * i₀) (j := R - 3 * jmin) (by omega) (by omega); omega
      have hcr_ub : G.dist (x (3 * i₀)) (z (R - 3 * jmin)) ≤ bound := hb _ hi₀f.2 _ hjm.2
      refine ⟨hcard, hIpos, hJpos, hIl, hJl, s, hsmin, by omega, ?_⟩
      by_cases hng : ∀ i ∈ I, i ≤ k
      · left
        have hsub : I ⊆ Finset.range (k - s + 1) := fun i hi => by
          have := hng i hi; have := hsmin i hi; rw [Finset.mem_range]; omega
        have := (Finset.card_le_card hsub).trans (by rw [Finset.card_range])
        have := hng i₀ hi₀; omega
      · by_cases hnl : ∀ i ∈ I, k ≤ i
        · left
          have hsub : I ⊆ Finset.Icc (k + s) p := fun i hi => by
            have := hnl i hi; have := hsmin i hi; have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
            exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          have := Finset.card_le_card hsub; rw [Nat.card_Icc] at this
          have := hnl i₀ hi₀; omega
        · right
          push Not at hng hnl
          have hsp := straddle_span I k s hIne hnl hng hsmin
          set imin := I.min' hIne; set imax := I.max' hIne
          have hm1 := Finset.mem_filter.mp (Finset.min'_mem I hIne)
          have hm2 := Finset.mem_filter.mp (Finset.max'_mem I hIne)
          have hmlt := Finset.mem_range.mp hm2.1
          have hd := hx (3 * imin) (3 * imax) (Nat.mul_le_mul_left 3 (Finset.min'_le I imax (Finset.max'_mem I hIne))) (by omega)
          have hle : G.dist (x (3 * imin)) (x (3 * imax)) ≤ bound := hb _ hm1.2 _ hm2.2
          omega

private lemma isMultipacking_setM (hc : G.Connected) {x z : ℕ → Fin n} {R : ℕ} (hR : 1 ≤ R)
    (hx : ∀ i j, i ≤ j → j ≤ R → G.dist (x i) (x j) = j - i)
    (hz : ∀ i j, i ≤ j → j ≤ R → G.dist (z i) (z j) = j - i)
    (hz0 : z 0 = x (3 * (R / 6))) : IsMultipacking G (setM x z R) := by
  apply mp_of_pair hc; intro U hU hU2
  by_contra hbad; push Not at hbad
  have hb : ∀ u ∈ U, ∀ v ∈ U, G.dist u v ≤ 2 * U.card - 2 := fun u hu v hv => by have := hbad u hu v hv; omega
  rcases setM_diam_cases hc hR hx hz hz0 hU (by omega) hb with h | ⟨hcard, hI1, hJ1, hIl, hJl, s, _, hcr, hcase⟩
  · omega
  · rcases hcase with hside | hstr
    · omega
    · set I := (Finset.range (R / 3 + 1)).filter (fun i => x (3 * i) ∈ U)
      set J := (Finset.range ((R - 1) / 6)).filter (fun j => z (R - 3 * j) ∈ U)
      have hrem : R % 6 = 1 ∨ R % 6 = 3 := by omega
      have hIeq : I = Finset.range (R / 3 + 1) :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [Finset.card_range]; omega)
      have h0U : x 0 ∈ U := by
        have : 0 ∈ I := by rw [hIeq, Finset.mem_range]; omega
        simpa using (Finset.mem_filter.mp this).2
      have hpU : x (3 * (R / 3)) ∈ U := by
        have : R / 3 ∈ I := by rw [hIeq, Finset.mem_range]; omega
        exact (Finset.mem_filter.mp this).2
      have hd0p : G.dist (x 0) (x (3 * (R / 3))) = 3 * (R / 3) := by
        simpa using hx 0 (3 * (R / 3)) (Nat.zero_le _) (by omega)
      have h0p_ub := hb _ h0U _ hpU
      rcases hrem with h1 | h3
      · have hJeq : J = Finset.range ((R - 1) / 6) :=
          Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [Finset.card_range]; omega)
        have hkU : x (3 * (R / 6)) ∈ U := by
          have : R / 6 ∈ I := by rw [hIeq, Finset.mem_range]; omega
          exact (Finset.mem_filter.mp this).2
        have hzRU : z R ∈ U := by
          have : 0 ∈ J := by rw [hJeq, Finset.mem_range]; omega
          simpa using (Finset.mem_filter.mp this).2
        have hd0R : G.dist (x (3 * (R / 6))) (z R) = R := by
          rw [← hz0]; simpa using hz 0 R (Nat.zero_le _) (le_refl R)
        have := hb _ hkU _ hzRU; omega
      · omega

private lemma robust_setM (hc : G.Connected) {x z : ℕ → Fin n} {k : ℕ} (hk : 1 ≤ k)
    (hx : ∀ i j, i ≤ j → j ≤ 6 * k + 5 → G.dist (x i) (x j) = j - i)
    (hz : ∀ i j, i ≤ j → j ≤ 6 * k + 5 → G.dist (z i) (z j) = j - i)
    (hz0 : z 0 = x (3 * k)) {T : Finset (Fin n)} (hT : T ⊆ setM x z (6 * k + 5)) (hT4 : 4 ≤ T.card) :
    ∃ u ∈ T, ∃ v ∈ T, 2 * T.card + 1 ≤ G.dist u v := by
  set R := 6 * k + 5
  have hz0' : z 0 = x (3 * (R / 6)) := by
    have : R / 6 = k := by omega
    rwa [this]
  by_contra hbad; push Not at hbad
  have hb : ∀ u ∈ T, ∀ v ∈ T, G.dist u v ≤ 2 * T.card := fun u hu v hv => by have := hbad u hu v hv; omega
  rcases setM_diam_cases hc (by omega) hx hz hz0' hT (by omega) hb with h | ⟨hcard, hI1, hJ1, hIl, hJl, s, hsmin, hcr, hcase⟩
  · omega
  · rcases hcase with hside | hstr
    · omega
    · set I := (Finset.range (R / 3 + 1)).filter (fun i => x (3 * i) ∈ T)
      have hIeq : I = Finset.range (R / 3 + 1) :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [Finset.card_range]; omega)
      have hs0 : s = 0 := by have := hsmin k (by rw [hIeq, Finset.mem_range]; omega); omega
      have h0T : x 0 ∈ T := by simpa using (Finset.mem_filter.mp (show 0 ∈ I by rw [hIeq, Finset.mem_range]; omega)).2
      have hpT : x (6 * k + 3) ∈ T := by
        have hmem := (Finset.mem_filter.mp (show 2 * k + 1 ∈ I by rw [hIeq, Finset.mem_range]; omega)).2
        have h3 : 3 * (2 * k + 1) = 6 * k + 3 := by omega
        rwa [h3] at hmem
      have hd : G.dist (x 0) (x (6 * k + 3)) = 6 * k + 3 := by simpa using hx 0 (6 * k + 3) (Nat.zero_le _) (by omega)
      have := hb _ h0T _ hpT; omega

private lemma aug_setM (hc : G.Connected) {x z : ℕ → Fin n} {k : ℕ} (hk : 1 ≤ k)
    (hx : ∀ i j, i ≤ j → j ≤ 6 * k + 5 → G.dist (x i) (x j) = j - i)
    (hz : ∀ i j, i ≤ j → j ≤ 6 * k + 5 → G.dist (z i) (z j) = j - i)
    (hz0 : z 0 = x (3 * k)) {b : Fin n}
    (hb1 : 3 * k + 6 ≤ G.dist b (x (3 * k + 3))) (hb2 : 3 * k ≤ G.dist b (z (6 * k + 5))) :
    b ∉ setM x z (6 * k + 5) ∧ IsMultipacking G (insert b (setM x z (6 * k + 5))) := by
  set R := 6 * k + 5
  have hz0' : z 0 = x (3 * (R / 6)) := by
    have : R / 6 = k := by omega
    rwa [this]
  have hMmp := isMultipacking_setM hc (by omega) hx hz hz0'
  have hbX : ∀ i ≤ 2 * k + 1, 3 * k + 6 ≤ G.dist b (x (3 * i)) + 3 * ((i - (k + 1)) + ((k + 1) - i)) := fun i hi => by
    have ht : G.dist b (x (3 * k + 3)) ≤ G.dist b (x (3 * i)) + G.dist (x (3 * i)) (x (3 * k + 3)) := hc.dist_triangle
    have hd : G.dist (x (3 * i)) (x (3 * k + 3)) = 3 * ((i - (k + 1)) + ((k + 1) - i)) := by
      rw [iso_symm hx (by omega) (by omega)]; omega
    omega
  have hbZ : ∀ j < k, 3 * k ≤ G.dist b (z (R - 3 * j)) + 3 * j := fun j hj => by
    have ht : G.dist b (z R) ≤ G.dist b (z (R - 3 * j)) + G.dist (z (R - 3 * j)) (z R) := hc.dist_triangle
    have hd := hz (R - 3 * j) R (by omega) (le_refl R); omega
  have hb_nm : b ∉ setM x z R := fun hbM => by
    rcases Finset.mem_union.mp hbM with hA | hB
    · rcases Finset.mem_image.mp hA with ⟨i, hi, heq⟩; rw [Finset.mem_range] at hi
      have := hbX i (by omega); rw [heq, G.dist_self] at this; omega
    · rcases Finset.mem_image.mp hB with ⟨j, hj, heq⟩; rw [Finset.mem_range] at hj
      have := hbZ j (by omega); rw [heq, G.dist_self] at this; omega
  refine ⟨hb_nm, fun v r hr => ?_⟩
  by_cases hvb : G.dist v b ≤ r
  · set T := (setM x z R).filter (fun u => G.dist v u ≤ r)
    have hfilt : (insert b (setM x z R)).filter (fun u => G.dist v u ≤ r) = insert b T := by
      ext u; simp only [Finset.mem_filter, Finset.mem_insert, T]
      exact ⟨fun ⟨h1, h2⟩ => h1.elim Or.inl (fun h => Or.inr ⟨h, h2⟩), fun h => h.elim (fun h => ⟨Or.inl h, h ▸ hvb⟩) (fun ⟨h1, h2⟩ => ⟨Or.inr h1, h2⟩)⟩
    rw [hfilt, Finset.card_insert_of_notMem (fun h => hb_nm (Finset.mem_filter.mp h).1)]
    have hTle : T.card ≤ r := hMmp v r hr
    by_cases hTlt : T.card < r
    · exact Nat.succ_le_of_lt hTlt
    · exfalso
      have hpair : ∀ u ∈ T, ∀ w ∈ T, G.dist u w ≤ 2 * r := fun u hu w hw => by
        have h1 := (Finset.mem_filter.mp hu).2; have h2 := (Finset.mem_filter.mp hw).2
        have ht : G.dist u w ≤ G.dist u v + G.dist v w := hc.dist_triangle
        have hcm : G.dist u v = G.dist v u := G.dist_comm; omega
      have hbu : ∀ u ∈ T, G.dist b u ≤ 2 * r := fun u hu => by
        have h1 := (Finset.mem_filter.mp hu).2
        have ht : G.dist b u ≤ G.dist b v + G.dist v u := hc.dist_triangle
        have hcm : G.dist b v = G.dist v b := G.dist_comm; omega
      by_cases hr4 : 4 ≤ r
      · obtain ⟨u, hu, w, hw, hd⟩ := robust_setM hc hk hx hz hz0 (show T ⊆ setM x z (6 * k + 5) from Finset.filter_subset _ _) (by omega)
        have := hpair u hu w hw; omega
      · have hrc : r = 1 ∨ r = 2 ∨ r = 3 := by omega
        rcases hrc with rfl | rfl | rfl
        · obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
          have := hbu u hu
          rcases Finset.mem_union.mp (Finset.mem_filter.mp hu).1 with hA | hB
          · rcases Finset.mem_image.mp hA with ⟨i, hi, rfl⟩; rw [Finset.mem_range] at hi; have := hbX i (by omega); omega
          · rcases Finset.mem_image.mp hB with ⟨j, hj, rfl⟩; rw [Finset.mem_range] at hj; have := hbZ j (by omega); omega
        · have hsub : T ⊆ {x 0, z (R - 3 * (k - 1))} := fun u hu => by
            have := hbu u hu; simp only [Finset.mem_insert, Finset.mem_singleton]
            rcases Finset.mem_union.mp (Finset.mem_filter.mp hu).1 with hA | hB
            · rcases Finset.mem_image.mp hA with ⟨i, hi, rfl⟩; rw [Finset.mem_range] at hi
              have := hbX i (by omega)
              have hi0 : i = 0 := by omega
              left; simp [hi0]
            · rcases Finset.mem_image.mp hB with ⟨j, hj, rfl⟩; rw [Finset.mem_range] at hj
              have := hbZ j (by omega)
              have hjk : j = k - 1 := by omega
              right; rw [hjk]
          have h0T : x 0 ∈ T := by
            by_contra h0
            have := Finset.card_le_card (show T ⊆ {z (R - 3 * (k - 1))} from fun u hu =>
              (Finset.mem_insert.mp (hsub hu)).resolve_left (fun he => h0 (he ▸ hu)))
            simp at this; omega
          have hzT : z (R - 3 * (k - 1)) ∈ T := by
            by_contra hz1
            have := Finset.card_le_card (show T ⊆ {x 0} from fun u hu =>
              Finset.mem_singleton.mpr ((Finset.mem_insert.mp (hsub hu)).resolve_right
                (fun he => hz1 (Finset.mem_singleton.mp he ▸ hu))))
            simp at this; omega
          have := cross_lb hc hx hz hz0 (by omega) (i := 0) (j := R - 3 * (k - 1)) (by omega) (by omega)
          have := hpair _ h0T _ hzT; omega
        · have hcand : ∀ u ∈ T, u = x 0 ∨ u = x 3 ∨ u = x (6 * k + 3) ∨
              u = z (R - 3 * (k - 1)) ∨ (2 ≤ k ∧ u = z (R - 3 * (k - 2))) := fun u hu => by
            have := hbu u hu
            rcases Finset.mem_union.mp (Finset.mem_filter.mp hu).1 with hA | hB
            · rcases Finset.mem_image.mp hA with ⟨i, hi, rfl⟩; rw [Finset.mem_range] at hi
              have := hbX i (by omega)
              rcases (show i = 0 ∨ i = 1 ∨ i = 2 * k + 1 by omega) with rfl | rfl | rfl
              · left; simp
              · right; left; simp
              · right; right; left; congr 1; omega
            · rcases Finset.mem_image.mp hB with ⟨j, hj, rfl⟩; rw [Finset.mem_range] at hj
              have := hbZ j (by omega)
              by_cases hj1 : j = k - 1
              · right; right; right; left; rw [hj1]
              · right; right; right; right
                refine ⟨by omega, ?_⟩
                have hj2 : j = k - 2 := by omega
                rw [hj2]
          by_cases h0T : x 0 ∈ T
          · have hsub : T ⊆ {x 0, x 3} := fun u hu => by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              rcases hcand u hu with rfl | rfl | rfl | rfl | ⟨hk2, rfl⟩
              · exact Or.inl rfl
              · exact Or.inr rfl
              · exfalso; have := hx 0 (6 * k + 3) (Nat.zero_le _) (by omega); have := hpair _ h0T _ hu; omega
              · exfalso; have := cross_lb hc hx hz hz0 (by omega) (i := 0) (j := R - 3 * (k - 1)) (by omega) (by omega); have := hpair _ h0T _ hu; omega
              · exfalso; have := cross_lb hc hx hz hz0 (by omega) (i := 0) (j := R - 3 * (k - 2)) (by omega) (by omega); have := hpair _ h0T _ hu; omega
            have := card_pair_le hsub; omega
          · by_cases h3T : x 3 ∈ T
            · have hsub : T ⊆ {x 3, x (6 * k + 3)} := fun u hu => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                rcases hcand u hu with rfl | rfl | rfl | rfl | ⟨hk2, rfl⟩
                · exact (h0T hu).elim
                · exact Or.inl rfl
                · exact Or.inr rfl
                · exfalso; have := cross_lb hc hx hz hz0 (by omega) (i := 3) (j := R - 3 * (k - 1)) (by omega) (by omega); have := hpair _ h3T _ hu; omega
                · exfalso; have := cross_lb hc hx hz hz0 (by omega) (i := 3) (j := R - 3 * (k - 2)) (by omega) (by omega); have := hpair _ h3T _ hu; omega
              have := card_pair_le hsub; omega
            · by_cases hk2 : 2 ≤ k
              · have hlT : x (6 * k + 3) ∈ T := by
                  by_contra hno
                  have := card_pair_le (show T ⊆ {z (R - 3 * (k - 1)), z (R - 3 * (k - 2))} from fun u hu => by
                    simp only [Finset.mem_insert, Finset.mem_singleton]
                    rcases hcand u hu with rfl | rfl | rfl | rfl | ⟨_, rfl⟩
                    · exact (h0T hu).elim
                    · exact (h3T hu).elim
                    · exact (hno hu).elim
                    · exact Or.inl rfl
                    · exact Or.inr rfl)
                  omega
                have hz2T : z (R - 3 * (k - 2)) ∈ T := by
                  by_contra hno
                  have := card_pair_le (show T ⊆ {x (6 * k + 3), z (R - 3 * (k - 1))} from fun u hu => by
                    simp only [Finset.mem_insert, Finset.mem_singleton]
                    rcases hcand u hu with rfl | rfl | rfl | rfl | ⟨_, rfl⟩
                    · exact (h0T hu).elim
                    · exact (h3T hu).elim
                    · exact Or.inl rfl
                    · exact Or.inr rfl
                    · exact (hno hu).elim)
                  omega
                have := cross_lb hc hx hz hz0 (by omega) (i := 6 * k + 3) (j := R - 3 * (k - 2)) (by omega) (by omega)
                have := hpair _ hlT _ hz2T; omega
              · have := card_pair_le (show T ⊆ {x (6 * k + 3), z (R - 3 * (k - 1))} from fun u hu => by
                  simp only [Finset.mem_insert, Finset.mem_singleton]
                  rcases hcand u hu with rfl | rfl | rfl | rfl | ⟨h2, _⟩
                  · exact (h0T hu).elim
                  · exact (h3T hu).elim
                  · exact Or.inl rfl
                  · exact Or.inr rfl
                  · omega)
                omega
  · have hfilt : (insert b (setM x z R)).filter (fun u => G.dist v u ≤ r) =
        (setM x z R).filter (fun u => G.dist v u ≤ r) := by
      ext u; simp only [Finset.mem_filter, Finset.mem_insert]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1.resolve_left (fun he => hvb (he ▸ h2)), h2⟩, fun ⟨h1, h2⟩ => ⟨Or.inr h1, h2⟩⟩
    rw [hfilt]; exact hMmp v r hr

private lemma five_class (hc : G.Connected)
    (hmod : rad G hc % 6 = 5) (hbc : broadcastNumber G = rad G hc) :
    broadcastNumber G ≤ 2 * multipackingNumber G := by
  set R := rad G hc; set k := R / 6
  have : Nonempty (Fin n) := hc.nonempty
  let v₀ : Fin n := Classical.arbitrary (Fin n)
  obtain ⟨x, _, hx⟩ := exists_iso hc v₀ R (rad_le_ecc hc v₀)
  by_cases hk0 : k = 0
  · let u := x 0; let v := x 5
    have hduv : G.dist u v = 5 := by simpa [u, v] using hx 0 5 (Nat.zero_le _) (by omega)
    have huv : u ≠ v := fun h => by rw [h, G.dist_self] at hduv; omega
    obtain ⟨b, hbu, hbv⟩ := exists_uncovered (G := G) u v huv 2 2 (by omega) (by omega) (by omega)
    have hbu_ne : b ≠ u := fun h => by rw [h, G.dist_self] at hbu; omega
    have hbv_ne : b ≠ v := fun h => by rw [h, G.dist_self] at hbv; omega
    let P : Finset (Fin n) := {u, v, b}
    have hPcard : P.card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hbv_ne.symm]
      · simp [huv, hbu_ne.symm]
    have hPmp : IsMultipacking G P := fun w r hr => by
      by_cases hr3 : 3 ≤ r
      · exact (Finset.card_filter_le _ _).trans (by omega)
      · rcases (show r = 1 ∨ r = 2 by omega) with rfl | rfl
        · by_contra hgt; push Not at hgt
          obtain ⟨a, ha, c, hc', hac⟩ := Finset.one_lt_card.mp hgt
          have h1 := (Finset.mem_filter.mp ha).2; have h2 := (Finset.mem_filter.mp hc').2
          have ht : G.dist a c ≤ G.dist a w + G.dist w c := hc.dist_triangle
          have hcm : G.dist a w = G.dist w a := G.dist_comm
          have haP := (Finset.mem_filter.mp ha).1; have hcP := (Finset.mem_filter.mp hc').1
          simp only [P, Finset.mem_insert, Finset.mem_singleton] at haP hcP
          rcases haP with rfl | rfl | rfl <;> rcases hcP with rfl | rfl | rfl
          · exact hac rfl
          · omega
          · rw [G.dist_comm] at ht; omega
          · rw [G.dist_comm] at ht; omega
          · exact hac rfl
          · rw [G.dist_comm] at ht; omega
          · omega
          · omega
          · exact hac rfl
        · by_contra hgt; push Not at hgt
          have heq : P.filter (fun y => G.dist w y ≤ 2) = P :=
            Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
          have h1 : G.dist w u ≤ 2 :=
            (Finset.mem_filter.mp (show u ∈ P.filter (fun y => G.dist w y ≤ 2) by rw [heq]; simp [P])).2
          have h2 : G.dist w v ≤ 2 :=
            (Finset.mem_filter.mp (show v ∈ P.filter (fun y => G.dist w y ≤ 2) by rw [heq]; simp [P])).2
          have ht : G.dist u v ≤ G.dist u w + G.dist w v := hc.dist_triangle
          have hcm : G.dist u w = G.dist w u := G.dist_comm; omega
    have := le_mp P hPmp; omega
  · have hk1 : 1 ≤ k := by omega
    obtain ⟨z, hz0, hz⟩ := exists_iso hc (x (3 * k)) R (rad_le_ecc hc (x (3 * k)))
    have hx' : ∀ i j, i ≤ j → j ≤ 6 * k + 5 → G.dist (x i) (x j) = j - i := fun i j hij hj => hx i j hij (by omega)
    have hz' : ∀ i j, i ≤ j → j ≤ 6 * k + 5 → G.dist (z i) (z j) = j - i := fun i j hij hj => hz i j hij (by omega)
    have huv : x (3 * k + 3) ≠ z (6 * k + 5) := fun h => by
      have hd := cross_lb hc hx' hz' hz0 (by omega) (i := 3 * k + 3) (j := 6 * k + 5) (by omega) (le_refl _)
      rw [h, G.dist_self] at hd; omega
    obtain ⟨b, hb1, hb2⟩ := exists_uncovered (G := G) (x (3 * k + 3)) (z (6 * k + 5)) huv (3 * k + 5) (3 * k - 1)
      (by omega) (by omega) (by omega)
    obtain ⟨hnm, hmp⟩ := aug_setM hc hk1 hx' hz' hz0 (by omega) (by omega)
    have hz0' : z 0 = x (3 * ((6 * k + 5) / 6)) := by
      have hk6 : (6 * k + 5) / 6 = k := by omega
      rwa [hk6]
    have hcard := card_setM (by omega) hx' hz' hz0'
    have hle := le_mp (insert b (setM x z (6 * k + 5))) hmp
    rw [Finset.card_insert_of_notMem hnm, hcard] at hle; omega

end TwoPath

theorem prove_main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.Connected →
    broadcastNumber G ≤ 2 * multipackingNumber G := by
  intro n G hc
  have hn_pos : 0 < n := by obtain ⟨v⟩ := hc.nonempty; exact Nat.pos_of_ne_zero (fun h => by subst h; exact Fin.elim0 v)
  by_cases hn1 : n = 1
  · subst hn1
    have hbc : broadcastNumber G ≤ 1 := by
      have h1 := bc_le (G := G) (fun _ => 1) (fun u => ⟨u, Nat.zero_lt_one, by simp⟩); simpa using h1
    have hmp : 1 ≤ multipackingNumber G := by
      have := le_mp (G := G) (Finset.univ : Finset (Fin 1)) (fun _ r hr => (Finset.card_filter_le _ _).trans (by simpa))
      simpa using this
    omega
  · set R := rad G hc
    have : Nonempty (Fin n) := hc.nonempty
    obtain ⟨c, _, hce⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (ecc G)
    have hR1 : 1 ≤ R := by
      let u : Fin n := if c.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hcu : c ≠ u := fun h => by
        by_cases h0 : c.val = 0
        · have hc1 : c.val = 1 := by simpa [u, h0] using congrArg Fin.val h
          omega
        · exact h0 (by simpa [u, h0] using congrArg Fin.val h)
      have h1 := hc.pos_dist_of_ne hcu; have h2 := dist_le_ecc (G := G) c u
      change R = ecc G c at hce; omega
    have hbc_le : broadcastNumber G ≤ R := by
      have h1 := bc_le (G := G) (fun v => if v = c then R else 0) (fun u => ⟨c, by simp; omega, by
        simp only [↓reduceIte]; rw [G.dist_comm]
        have h2 := dist_le_ecc (G := G) c u; change R = ecc G c at hce; omega⟩)
      rwa [sum_ite_one] at h1
    let v₀ : Fin n := Classical.arbitrary (Fin n)
    obtain ⟨x, _, hx⟩ := exists_iso hc v₀ R (rad_le_ecc hc v₀)
    obtain ⟨z, hz0, hz⟩ := exists_iso hc (x (3 * (R / 6))) R (rad_le_ecc hc (x (3 * (R / 6))))
    have hmp_ge := le_mp (setM x z R) (isMultipacking_setM hc hR1 hx hz hz0)
    rw [card_setM hR1 hx hz hz0] at hmp_ge
    by_cases hmod : R % 6 = 5
    · by_cases hbc_eq : broadcastNumber G = R
      · exact five_class hc hmod hbc_eq
      · omega
    · omega

end OMA.P_arxiv_1803_02550

theorem OMA.solution : type_of% @OMA.S_arxiv_1803_02550.main :=
  OMA.P_arxiv_1803_02550.prove_main

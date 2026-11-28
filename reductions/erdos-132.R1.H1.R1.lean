import OMAReductions.R_erdos_132_R1
import Mathlib

-- Reduction erdos-132.R1.H1.R1 of step erdos-132.R1.H1
-- Credit: @JamesSlash

/-! # Sets that become convex after deleting one point

Step erdos-132.R1.H1 asks: an n-point planar set (n at least 5) with at most n/2 distinct
distances has two rare distances (each realised by at least one and at most n pairs).

This reduction removes from that step every set P with at least nine points such that P minus
one point q is in convex position. The method is due to @begcdn: delete a point so that what
remains is a convex polygon with the least possible number of distances, identify it, and show
the deleted points can only be its centre or its missing vertex.

* H1 is Altman's theorem: a convex polygon with h vertices has at least h/2 (rounded down)
  distinct distances (E. Altman, Amer. Math. Monthly 70 (1963)).
* H2 is the Hopf and Pannwitz theorem: the diameter occurs at most n times (1934).
* H3 identifies the extremal convex polygons and how one extra point can sit next to them.
  It follows from Altman's equality case for odd h, Fishburn's classification for even h at
  least 8 (Comput. Geom. 5 (1995), Theorems 1 and 2: the regular h-gon, or h vertices of the
  regular (h+1)-gon) and reflection lemmas for regular polygons.
* H4 is what is left: sets with at most eight points (Erdős and Fishburn 1995 for n = 5, 6;
  Kelly and Shinohara for n = 7, 8) and sets that are not convex after deleting any one point.

The proof of main is the case analysis. Write n = |P|, C = P minus q. Suppose at most one
distance is rare. If n is odd, Altman gives D(C) = D(P), and the even clause of H3 gives two
rare distances. If n is even and |D(P)| is less than n/2, again D(C) = D(P), so q sees all of
C at old distances, against the odd clause of H3. If |D(P)| = n/2, Hopf and Pannwitz make the
diameter rare, so every other distance occurs at least n+1 times, and counting the n(n-1)
ordered pairs leaves a unique diametral pair a, b. Deleting a removes the diameter, and the odd
clause (q = a or q = b) or the even clause applied to C minus a, with the extra points q and a
(otherwise), gives the contradiction.
-/

namespace OMA.R_erdos_132_R1_H1_R1

open scoped Classical
open OMA.S_erdos_132 (pairMultiplicity rareDistances)

/-- Altman: a planar set in convex position with h points has at least h/2 distances. -/
def H1 : Prop :=
  ∀ C : Finset (EuclideanSpace ℝ (Fin 2)),
    (∀ c ∈ C, c ∉ convexHull ℝ (↑(C.erase c) : Set (EuclideanSpace ℝ (Fin 2)))) →
    C.card / 2 ≤ (C.offDiag.image (fun p => dist p.1 p.2)).card

/-- Hopf and Pannwitz: the largest distance occurs between at most n pairs. -/
def H2 : Prop :=
  ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), ∀ d ∈ A.offDiag.image (fun p => dist p.1 p.2),
    (∀ e ∈ A.offDiag.image (fun p => dist p.1 p.2), e ≤ d) →
    pairMultiplicity A d ≤ A.card

/-- Extremal convex polygons and one or two extra points. Odd h: the polygon is regular and an
outside point sees at least two vertices at new distances. Even h at least 8: the polygon is the
regular h-gon or h vertices of the regular (h+1)-gon; a point x adding no distance is the centre
or the missing vertex, the result has two rare distances, and any further point sees at least two
points at new distances. -/
def H3 : Prop :=
  (∀ C : Finset (EuclideanSpace ℝ (Fin 2)),
    (∀ c ∈ C, c ∉ convexHull ℝ (↑(C.erase c) : Set (EuclideanSpace ℝ (Fin 2)))) →
    Odd C.card → 9 ≤ C.card →
    (C.offDiag.image (fun p => dist p.1 p.2)).card ≤ C.card / 2 →
    ∀ x ∉ C, 2 ≤ (C.filter (fun c => dist x c ∉ C.offDiag.image (fun p => dist p.1 p.2))).card) ∧
  (∀ C : Finset (EuclideanSpace ℝ (Fin 2)),
    (∀ c ∈ C, c ∉ convexHull ℝ (↑(C.erase c) : Set (EuclideanSpace ℝ (Fin 2)))) →
    Even C.card → 8 ≤ C.card →
    (C.offDiag.image (fun p => dist p.1 p.2)).card = C.card / 2 →
    ∀ x ∉ C, (∀ c ∈ C, dist x c ∈ C.offDiag.image (fun p => dist p.1 p.2)) →
      2 ≤ (rareDistances (insert x C)).card ∧
      ∀ y ∉ insert x C,
        2 ≤ ((insert x C).filter
          (fun z => dist y z ∉ C.offDiag.image (fun p => dist p.1 p.2))).card)

/-- What is left of step erdos-132.R1.H1: small sets, and sets that are not in convex position
after deleting any one point. -/
def H4 : Prop :=
  ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), 5 ≤ A.card →
    (A.offDiag.image (fun p => dist p.1 p.2)).card ≤ A.card / 2 →
    (A.card ≤ 8 ∨ ∀ q ∈ A, ∃ c ∈ A.erase q,
      c ∈ convexHull ℝ (↑((A.erase q).erase c) : Set (EuclideanSpace ℝ (Fin 2)))) →
    2 ≤ (rareDistances A).card

lemma mem_dists {α : Type*} [MetricSpace α] [DecidableEq α] {S : Finset α} {x y : α}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    dist x y ∈ S.offDiag.image (fun p => dist p.1 p.2) :=
  Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩, rfl⟩

lemma dists_mono {α : Type*} [MetricSpace α] [DecidableEq α] {S T : Finset α} (h : S ⊆ T) :
    S.offDiag.image (fun p => dist p.1 p.2) ⊆ T.offDiag.image (fun p => dist p.1 p.2) := by
  intro d hd
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hxy
  exact mem_dists (h hx) (h hy) hne

lemma convex_erase {S : Finset (EuclideanSpace ℝ (Fin 2))}
    (h : ∀ c ∈ S, c ∉ convexHull ℝ (↑(S.erase c) : Set (EuclideanSpace ℝ (Fin 2))))
    (a : EuclideanSpace ℝ (Fin 2)) :
    ∀ c ∈ S.erase a,
      c ∉ convexHull ℝ (↑((S.erase a).erase c) : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro c hc hmem
  apply h c (Finset.mem_of_mem_erase hc)
  refine convexHull_mono ?_ hmem
  rw [Finset.erase_right_comm]
  exact Finset.coe_subset.mpr (Finset.erase_subset _ _)

/-- Distances avoiding one endpoint of a unique diametral pair are not the diameter. -/
lemma dists_sub_erase {S A : Finset (EuclideanSpace ℝ (Fin 2))} {a b : EuclideanSpace ℝ (Fin 2)}
    {Δ : ℝ} (hSA : S ⊆ A) (haS : a ∉ S)
    (huniq : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → dist x y = Δ → (x = a ∧ y = b) ∨ (x = b ∧ y = a)) :
    S.offDiag.image (fun p => dist p.1 p.2) ⊆
      (A.offDiag.image (fun p => dist p.1 p.2)).erase Δ := by
  intro d hd
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hxy
  refine Finset.mem_erase.mpr ⟨fun hΔ => ?_, mem_dists (hSA hx) (hSA hy) hne⟩
  rcases huniq x (hSA hx) y (hSA hy) hne hΔ with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · exact haS hx
  · exact haS hy

/-- A filter contained in a singleton has at most one element. -/
lemma card_filter_le_one {S : Finset (EuclideanSpace ℝ (Fin 2))} {P : EuclideanSpace ℝ (Fin 2) → Prop}
    [DecidablePred P] (b : EuclideanSpace ℝ (Fin 2)) (h : ∀ z ∈ S, z ≠ b → ¬ P z) :
    (S.filter P).card ≤ 1 := by
  refine (Finset.card_le_card (t := {b}) ?_).trans (Finset.card_singleton b).le
  intro z hz
  obtain ⟨hzS, hPz⟩ := Finset.mem_filter.mp hz
  by_contra hzb
  exact h z hzS (by simpa using hzb) hPz

theorem main : H1 → H2 → H3 → H4 → OMA.R_erdos_132_R1.H1 := by
  intro hAlt hHP hRig hRest
  unfold H1 at hAlt
  unfold H2 at hHP
  unfold H3 at hRig
  unfold H4 at hRest
  unfold OMA.R_erdos_132_R1.H1
  intro A hA5 hD
  by_cases hsmall : A.card ≤ 8 ∨ ∀ q ∈ A, ∃ c ∈ A.erase q,
      c ∈ convexHull ℝ (↑((A.erase q).erase c) : Set (EuclideanSpace ℝ (Fin 2)))
  · exact hRest A hA5 hD hsmall
  push Not at hsmall
  obtain ⟨h9, q, hqA, hconv⟩ := hsmall
  by_contra hlt
  push Not at hlt
  have hqC : q ∉ A.erase q := Finset.notMem_erase q A
  have hAC : insert q (A.erase q) = A := Finset.insert_erase hqA
  have hCcard : (A.erase q).card = A.card - 1 := Finset.card_erase_of_mem hqA
  have hDsub := dists_mono (Finset.erase_subset q A)
  have hDle := Finset.card_le_card hDsub
  have hAltC := hAlt (A.erase q) hconv
  have hqdist : ∀ c ∈ A.erase q, dist q c ∈ A.offDiag.image (fun p => dist p.1 p.2) :=
    fun c hc => mem_dists hqA (Finset.mem_of_mem_erase hc) (Finset.ne_of_mem_erase hc).symm
  rcases Nat.even_or_odd A.card with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n = 2k is even and C = A.erase q has 2k - 1 points
    have hk5 : 5 ≤ k := by omega
    have hCodd : Odd (A.erase q).card := ⟨k - 1, by omega⟩
    by_cases hb1 : (A.offDiag.image (fun p => dist p.1 p.2)).card < k
    · -- fewer than n/2 distances: q adds no distance to C
      have hDeq := Finset.eq_of_subset_of_card_le hDsub (by omega)
      have h2 := hRig.1 (A.erase q) hconv hCodd (by omega) (by omega) q hqC
      have h0 : ((A.erase q).filter
          (fun c => dist q c ∉ (A.erase q).offDiag.image (fun p => dist p.1 p.2))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro c hc
        rw [hDeq]
        exact not_not.mpr (hqdist c hc)
      omega
    · -- exactly n/2 distances: the diametral pair is unique
      have hDk : (A.offDiag.image (fun p => dist p.1 p.2)).card = k := by omega
      have hne : (A.offDiag.image (fun p => dist p.1 p.2)).Nonempty := by
        rw [← Finset.card_pos]; omega
      set Δ := (A.offDiag.image (fun p => dist p.1 p.2)).max' hne with hΔdef
      have hΔmem : Δ ∈ A.offDiag.image (fun p => dist p.1 p.2) := Finset.max'_mem _ _
      have hΔmax : ∀ e ∈ A.offDiag.image (fun p => dist p.1 p.2), e ≤ Δ :=
        fun e he => Finset.le_max' _ e he
      have hΔrare : Δ ∈ rareDistances A :=
        Finset.mem_filter.mpr ⟨hΔmem, OMA.R_erdos_132_R1.multiplicity_pos hΔmem,
          hHP A Δ hΔmem hΔmax⟩
      have hheavy : ∀ d ∈ (A.offDiag.image (fun p => dist p.1 p.2)).erase Δ,
          2 * (A.card + 1) ≤ (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card := by
        intro d hd
        obtain ⟨hdΔ, hdmem⟩ := Finset.mem_erase.mp hd
        have hlarge : A.card < pairMultiplicity A d := by
          by_contra hsm
          push Not at hsm
          have hdrare : d ∈ rareDistances A :=
            Finset.mem_filter.mpr ⟨hdmem, OMA.R_erdos_132_R1.multiplicity_pos hdmem, hsm⟩
          have : 1 < (rareDistances A).card :=
            Finset.one_lt_card.mpr ⟨d, hdrare, Δ, hΔrare, hdΔ⟩
          omega
        unfold pairMultiplicity at hlarge
        omega
      have hsum : A.offDiag.card = ∑ d ∈ A.offDiag.image (fun p => dist p.1 p.2),
          (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card :=
        Finset.card_eq_sum_card_fiberwise (by
          intro p hp
          exact Finset.mem_image_of_mem _ (Finset.mem_coe.mp hp))
      rw [← Finset.add_sum_erase _ (fun d => (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card)
        hΔmem] at hsum
      have hlow := Finset.card_nsmul_le_sum _ _ _ hheavy
      rw [Finset.card_erase_of_mem hΔmem, smul_eq_mul, hDk] at hlow
      rw [Finset.offDiag_card] at hsum
      have hF : (A.offDiag.filter (fun p => dist p.1 p.2 = Δ)).card ≤ 2 := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [hk] at hsum hlow
        have hsq : (j + 1 + (j + 1)) * (j + 1 + (j + 1)) - (j + 1 + (j + 1))
            = 4 * j * j + 6 * j + 2 := by
          have : (j + 1 + (j + 1)) * (j + 1 + (j + 1)) = 4 * j * j + 6 * j + 2 + (j + 1 + (j + 1)) := by
            ring
          omega
        rw [hsq] at hsum
        simp only [Nat.add_sub_cancel] at hlow
        nlinarith
      obtain ⟨⟨a, b⟩, hab, hΔab⟩ := Finset.mem_image.mp hΔmem
      obtain ⟨haA, hbA, hab'⟩ := Finset.mem_offDiag.mp hab
      simp only at hΔab
      have huniq : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → dist x y = Δ →
          (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
        intro x hx y hy hxy hdist
        by_contra hcon
        push Not at hcon
        have h3 : 2 < (A.offDiag.filter (fun p => dist p.1 p.2 = Δ)).card := by
          rw [Finset.two_lt_card_iff]
          refine ⟨(a, b), (b, a), (x, y), ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨hab, hΔab⟩
          · exact Finset.mem_filter.mpr
              ⟨Finset.mem_offDiag.mpr ⟨hbA, haA, hab'.symm⟩, (dist_comm b a).trans hΔab⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩, hdist⟩
          · intro h; exact hab' (congrArg Prod.fst h)
          · intro h
            have h1 : a = x := congrArg Prod.fst h
            have h2 : b = y := congrArg Prod.snd h
            exact hcon.1 h1.symm h2.symm
          · intro h
            have h1 : b = x := congrArg Prod.fst h
            have h2 : a = y := congrArg Prod.snd h
            exact hcon.2 h1.symm h2.symm
        omega
      have hEcard : ((A.offDiag.image (fun p => dist p.1 p.2)).erase Δ).card = k - 1 := by
        rw [Finset.card_erase_of_mem hΔmem, hDk]
      -- put q in the first slot of the diametral pair when it is an endpoint
      have hcase : ∃ a' b', a' ∈ A ∧ b' ∈ A ∧ a' ≠ b' ∧
          (∀ x ∈ A, ∀ y ∈ A, x ≠ y → dist x y = Δ → (x = a' ∧ y = b') ∨ (x = b' ∧ y = a')) ∧
          (q = a' ∨ (q ≠ a' ∧ q ≠ b')) := by
        by_cases hqb : q = b
        · refine ⟨b, a, hbA, haA, hab'.symm, ?_, Or.inl hqb⟩
          intro x hx y hy hxy hd
          exact (huniq x hx y hy hxy hd).symm
        · by_cases hqa : q = a
          · exact ⟨a, b, haA, hbA, hab', huniq, Or.inl hqa⟩
          · exact ⟨a, b, haA, hbA, hab', huniq, Or.inr ⟨hqa, hqb⟩⟩
      obtain ⟨a, b, haA, hbA, hab', huniq, hqcase⟩ := hcase
      rcases hqcase with hqa | ⟨hqa, hqb⟩
      · -- q is an endpoint of the diameter: C = A.erase q has no diameter
        rw [← hqa] at huniq hab'
        have hsub := dists_sub_erase (Finset.erase_subset q A) hqC huniq
        have hsubc := Finset.card_le_card hsub
        have hDeq := Finset.eq_of_subset_of_card_le hsub (by omega)
        have h2 := hRig.1 (A.erase q) hconv hCodd (by omega) (by omega) q hqC
        have h1 : ((A.erase q).filter
            (fun c => dist q c ∉ (A.erase q).offDiag.image (fun p => dist p.1 p.2))).card ≤ 1 := by
          apply card_filter_le_one b
          intro z hz hzb hnot
          apply hnot
          rw [hDeq]
          refine Finset.mem_erase.mpr ⟨fun hzΔ => ?_, hqdist z hz⟩
          rcases huniq q hqA z (Finset.mem_of_mem_erase hz) (Finset.ne_of_mem_erase hz).symm hzΔ
            with ⟨-, h⟩ | ⟨h, -⟩
          · exact hzb h
          · exact hab' h
        omega
      · -- q is not an endpoint: apply the even clause to C' = (A.erase q).erase a
        have haC : a ∈ A.erase q := Finset.mem_erase.mpr (⟨fun h => hqa h.symm, haA⟩)
        have hconv' := convex_erase hconv a
        have hC'card : ((A.erase q).erase a).card = 2 * k - 2 := by
          rw [Finset.card_erase_of_mem haC]; omega
        have hKsub : insert q ((A.erase q).erase a) ⊆ A.erase a := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact Finset.mem_erase.mpr ⟨hqa, hqA⟩
          · exact Finset.mem_erase.mpr
              ⟨Finset.ne_of_mem_erase hz, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)⟩
        have hsubK := dists_sub_erase (Finset.erase_subset a A) (Finset.notMem_erase a A) huniq
        have hsubC' : ((A.erase q).erase a).offDiag.image (fun p => dist p.1 p.2) ⊆
            (A.offDiag.image (fun p => dist p.1 p.2)).erase Δ :=
          (dists_mono ((Finset.subset_insert _ _).trans hKsub)).trans hsubK
        have hAltC' := hAlt _ hconv'
        have hDeq := Finset.eq_of_subset_of_card_le hsubC' (by omega)
        have hDeqc := congrArg Finset.card hDeq
        have hqC' : q ∉ (A.erase q).erase a := fun h => hqC (Finset.mem_of_mem_erase h)
        have hnew : ∀ x ∈ A, x ≠ a → x ≠ b → ∀ z ∈ A, z ≠ a → x ≠ z →
            dist x z ∈ ((A.erase q).erase a).offDiag.image (fun p => dist p.1 p.2) := by
          intro x hx hxa hxb z hz hza hxz
          rw [hDeq]
          refine Finset.mem_erase.mpr ⟨fun hzΔ => ?_, mem_dists hx hz hxz⟩
          rcases huniq x hx z hz hxz hzΔ with ⟨h, -⟩ | ⟨h, -⟩
          · exact hxa h
          · exact hxb h
        have hqgood : ∀ c ∈ (A.erase q).erase a,
            dist q c ∈ ((A.erase q).erase a).offDiag.image (fun p => dist p.1 p.2) := by
          intro c hc
          have hcq : c ≠ q := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)
          exact hnew q hqA hqa hqb c (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc))
            (Finset.ne_of_mem_erase hc) hcq.symm
        have haK : a ∉ insert q ((A.erase q).erase a) := by
          intro h
          rcases Finset.mem_insert.mp h with h | h
          · exact hqa h.symm
          · exact Finset.notMem_erase a _ h
        have h2 := (hRig.2 _ hconv' ⟨k - 1, by omega⟩ (by omega) (by omega) q hqC' hqgood).2 a haK
        have h1 : ((insert q ((A.erase q).erase a)).filter (fun z =>
            dist a z ∉ ((A.erase q).erase a).offDiag.image (fun p => dist p.1 p.2))).card ≤ 1 := by
          apply card_filter_le_one b
          intro z hz hzb hnot
          have hzA : z ∈ A.erase a := hKsub hz
          apply hnot
          rw [hDeq]
          refine Finset.mem_erase.mpr ⟨fun hzΔ => ?_,
            mem_dists haA (Finset.mem_of_mem_erase hzA) (Finset.ne_of_mem_erase hzA).symm⟩
          rcases huniq a haA z (Finset.mem_of_mem_erase hzA) (Finset.ne_of_mem_erase hzA).symm hzΔ
            with ⟨-, h⟩ | ⟨h, -⟩
          · exact hzb h
          · exact hab' h
        omega
  · -- n = 2k + 1 is odd and C = A.erase q has 2k points: q adds no distance
    have hDeq := Finset.eq_of_subset_of_card_le hDsub (by omega)
    have hq : ∀ c ∈ A.erase q, dist q c ∈ (A.erase q).offDiag.image (fun p => dist p.1 p.2) := by
      intro c hc
      rw [hDeq]
      exact hqdist c hc
    have h2 := (hRig.2 (A.erase q) hconv ⟨k, by omega⟩ (by omega) (by omega) q hqC hq).1
    rw [hAC] at h2
    omega

end OMA.R_erdos_132_R1_H1_R1

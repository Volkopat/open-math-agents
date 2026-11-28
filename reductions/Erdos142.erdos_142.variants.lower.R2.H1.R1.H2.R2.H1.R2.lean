import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2
import Mathlib

/-!
# A relative progression bound from imperfect colorings and lattice models

Suppose a piece B of an interval is colored with q colors, and E contains
all genuine monochromatic three-term progressions. Fixed-size sampling followed by
deletion gives |B|³ ≤ 64 (q r₃(N))² (|B|+|E|). For an injective lattice
model, coloring by its actual squared norms makes every surviving triple a
midpoint error. A suitable overlapping family of models also suffices.

For affine mixed-radix boxes the centered spherical coloring has at most
1 + ∑ floor(Mᵢ²/4) colors. For caps between 1 and L and bases larger than twice
the caps, the exponential density loss absorbs the polynomial shell count,
uniformly in the dimension, radices, translate, dilation, and chosen subset.
The box population therefore satisfies the cubic estimate with constant
25(L²+1)² on every ambient interval containing a full radix period in length.
Each exceptional axis on which carries are allowed increases that constant by
at most a factor of six, for radices larger than their digit cap.

For the general 4-free set, intervals on which the cubic population per unit
length increases are handled by induction. Sets with at most N triples are
covered by one-color alteration. What remains is a structural extraction
problem for triple-rich sets on which every proper interval has smaller
cubic population per unit length. We distinguish the small-sumset and
large-sumset regimes. Both extraction assertions are open. Either a single
piece of sufficient efficiency or a suitably weighted cover gives what is
needed. No fixed positive relative size is assumed for the selected piece.

The proper-color proposal of @NonEstSpes (note #173573), the ternary-grid
case of @jacklarmer, and the base-19 obstruction of @npnelson (note #176840)
motivate the error term and mixed-radix theorem. The sampling calculation
uses the finite supersaturation idea also recorded by @dwilfand-sys.
The interval argument uses the merged translation and monotonicity lemmas.
-/

/- A fixed-size sampling estimate for colored three-term progressions. -/

open Finset

namespace Cross142

private theorem choose_three_factor (b : ℕ) :
    6 * b.choose 3 = b * (b - 1) * (b - 2) := by
  simpa [Nat.descFactorial_succ, Nat.factorial_succ, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using (Nat.descFactorial_eq_factorial_mul_choose b 3).symm

/-- A triple system with independence bound A and E indexed edges has b³ ≤ 64 A² (b+E).
The local hypothesis describes the deletion of one vertex from each retained edge. -/
theorem triple_alteration {α ι : Type*} [DecidableEq α]
    (B : Finset α) (G : Finset ι) (edge : ι → Finset α) (A : ℕ)
    (hsub : ∀ e ∈ G, edge e ⊆ B) (hcard : ∀ e ∈ G, (edge e).card = 3)
    (hremove : ∀ S ⊆ B, S.card ≤ A + (G.filter (fun e => edge e ⊆ S)).card) :
    B.card ^ 3 ≤ 64 * A ^ 2 * (B.card + G.card) := by
  classical
  by_cases hsmall : B.card ≤ 4 * A
  · have h := Nat.mul_le_mul_left B.card (Nat.pow_le_pow_left hsmall 2)
    nlinarith
  have ha : 0 < A := by
    by_contra! h
    have hz : A = 0 := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
    have hempty : G.filter (fun e => edge e ⊆ {v}) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨heg, hs⟩ := Finset.mem_filter.mp he
      have hle := Finset.card_le_card hs
      simp [hcard e heg] at hle
    have hbad := hremove {v} (Finset.singleton_subset_iff.mpr hv)
    rw [hempty, hz] at hbad
    simp at hbad
  let t := 3 * A
  have ht : 3 ≤ t := by dsimp [t]; omega
  have htb : t ≤ B.card := by dsimp [t]; omega
  have hdouble :
      ∑ S ∈ B.powersetCard t, (G.filter (fun e => edge e ⊆ S)).card =
      ∑ e ∈ G, ((B.powersetCard t).filter (fun S => edge e ⊆ S)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hmass : 2 * A * B.card.choose t ≤ G.card * (B.card - 3).choose (t - 3) := by
    calc
      _ = ∑ _S ∈ B.powersetCard t, 2 * A := by simp [Nat.mul_comm]
      _ ≤ ∑ S ∈ B.powersetCard t, (G.filter (fun e => edge e ⊆ S)).card := by
        apply Finset.sum_le_sum
        intro S hS
        obtain ⟨hs, hsize⟩ := Finset.mem_powersetCard.mp hS
        have hu := hremove S hs
        dsimp [t] at hsize
        omega
      _ = _ := by
        rw [hdouble]
        apply Finset.sum_const_nat
        intro e he
        rw [Finset.card_filter_powersetCard_subset _ _ _ (hsub e he) (by simpa [hcard e he] using ht)]
        rw [hcard e he]
  have htriple : 2 * A * B.card.choose 3 ≤ G.card * t.choose 3 := by
    refine Nat.le_of_mul_le_mul_right (c := (B.card - 3).choose (t-3)) ?_
      (Nat.choose_pos (by omega))
    calc
      _ = 2*A*(B.card.choose t * t.choose 3) := by rw [Nat.choose_mul ht]; ring
      _ ≤ _ := by
        have hi := Nat.mul_le_mul_right (t.choose 3) hmass
        simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hi
  have hfall : 2*A*(B.card*(B.card-1)*(B.card-2)) ≤ G.card*t^3 := by
    calc
      _ = 6*(2*A*B.card.choose 3) := by rw [←choose_three_factor]; ring
      _ ≤ 6*(G.card*t.choose 3) := Nat.mul_le_mul_left _ htriple
      _ = G.card*(t*(t-1)*(t-2)) := by rw [←choose_three_factor]; ring
      _ ≤ G.card*t^3 := by
        apply Nat.mul_le_mul_left
        rw [pow_succ, pow_two]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) (Nat.sub_le _ _)
  have hscale : B.card^3 ≤ 4*(B.card*(B.card-1)*(B.card-2)) := by
    have h1 : B.card ≤ 2*(B.card-1) := by omega
    have h2 : B.card ≤ 2*(B.card-2) := by omega
    have hh := Nat.mul_le_mul_left B.card (Nat.mul_le_mul h1 h2)
    nlinarith
  have hbound : B.card^3 ≤ 54*A^2*G.card := by
    refine Nat.le_of_mul_le_mul_left (c := 2*A) ?_ (by omega)
    calc
      _ ≤ 2*A*(4*(B.card*(B.card-1)*(B.card-2))) := Nat.mul_le_mul_left _ hscale
      _ = 4*(2*A*(B.card*(B.card-1)*(B.card-2))) := by ring
      _ ≤ 4*(G.card*t^3) := Nat.mul_le_mul_left _ hfall
      _ = _ := by dsimp [t]; ring
  nlinarith


/-- The short passage through the defining supremum follows the native r₃ bridge
in the proof of Erdos142.erdos_142.variants.lower.R3.H1. -/
theorem card_no_triple {N : ℕ} (X : Finset ℕ) (hX : X ⊆ Finset.Icc 1 N)
    (hfree : ∀ a d : ℕ, 0 < d → a ∈ X → a+d ∈ X → a+2*d ∉ X) :
    X.card ≤ Erdos142.r 3 N := by
  apply le_csSup
  · refine ⟨(Finset.Icc 1 N).card, ?_⟩
    rintro x ⟨s, hs, -, rfl⟩
    exact Finset.card_le_card hs
  refine ⟨X, hX, ?_, rfl⟩
  rintro s hs ⟨a, d, hsize, heq⟩
  exfalso
  have hin (j : ℕ) (hj : j < 3) : a + j*d ∈ s := by
    rw [heq]
    exact ⟨j, by exact_mod_cast hj, by simp [smul_eq_mul]⟩
  by_cases hd : d = 0
  · subst d
    have hone : s = {a} := by
      apply Set.Subset.antisymm
      · rw [heq]
        rintro z ⟨i, -, rfl⟩
        simp
      · simpa using hin 0 (by omega)
    rw [hone] at hsize
    norm_num at hsize
  apply hfree a d (by omega)
  · simpa using hs (hin 0 (by omega))
  · simpa using hs (hin 1 (by omega))
  · exact hs (hin 2 (by omega))

/-- E may include pairs which are not monochromatic progressions in B. -/
theorem alteration {N q : ℕ} (B : Finset ℕ) (c : ℕ → Fin q) (E : Finset (ℕ × ℕ))
    (hB : B ⊆ Finset.Icc 1 N)
    (hcover : ∀ a d : ℕ, 0 < d → a ∈ B → a+d ∈ B → a+2*d ∈ B →
      c a = c (a+d) → c (a+d) = c (a+2*d) → (a,d) ∈ E) :
    B.card ^ 3 ≤ 64 * (q * Erdos142.r 3 N) ^ 2 * (B.card + E.card) := by
  classical
  let edge (e : ℕ × ℕ) : Finset ℕ := {e.1, e.1+e.2, e.1+2*e.2}
  let G := E.filter fun e => 0 < e.2 ∧ edge e ⊆ B
  have hsub (e) (he : e ∈ G) : edge e ⊆ B := (Finset.mem_filter.mp he).2.2
  have hcard (e) (he : e ∈ G) : (edge e).card = 3 := by
    have hd : 0 < e.2 := (Finset.mem_filter.mp he).2.1
    have h1 : e.1 ≠ e.1+e.2 := by omega
    have h2 : e.1 ≠ e.1+2*e.2 := by omega
    have h3 : e.1+e.2 ≠ e.1+2*e.2 := by omega
    dsimp [edge]
    rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_insert, Finset.mem_singleton] using not_or_intro h1 h2),
      Finset.card_insert_of_notMem (by simpa only [Finset.mem_singleton] using h3)]
    simp
  have hremove (S : Finset ℕ) (hS : S ⊆ B) :
      S.card ≤ q * Erdos142.r 3 N + (G.filter (fun e => edge e ⊆ S)).card := by
    let bad := G.filter fun e => edge e ⊆ S
    let T := S \ bad.image Prod.fst
    have hTS : T ⊆ S := Finset.sdiff_subset
    have hfib (i : Fin q) : (T.filter (fun x => c x = i)).card ≤ Erdos142.r 3 N := by
      apply card_no_triple _ ((Finset.filter_subset _ _).trans (hTS.trans (hS.trans hB)))
      intro a d hd ha hb hc
      obtain ⟨haT, haI⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbT, hbI⟩ := Finset.mem_filter.mp hb
      obtain ⟨hcT, hcI⟩ := Finset.mem_filter.mp hc
      have hex : (a,d) ∈ E := hcover a d hd (hS (hTS haT)) (hS (hTS hbT))
        (hS (hTS hcT)) (haI.trans hbI.symm) (hbI.trans hcI.symm)
      have hsEdge : edge (a,d) ⊆ S := by
        simpa only [edge, Finset.insert_subset_iff, Finset.singleton_subset_iff] using
          (And.intro (hTS haT) (And.intro (hTS hbT) (hTS hcT)))
      have hbad : (a,d) ∈ bad := Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hex, hd, hsEdge.trans hS⟩, hsEdge⟩
      exact (Finset.mem_sdiff.mp haT).2 (Finset.mem_image.mpr ⟨(a,d), hbad, rfl⟩)
    have hT : T.card ≤ q * Erdos142.r 3 N := by
      calc
        _ = ∑ i : Fin q, (T.filter (fun x => c x = i)).card := by
          simpa using (Finset.sum_card_fiberwise_eq_card_filter T Finset.univ c).symm
        _ ≤ ∑ _i : Fin q, Erdos142.r 3 N := Finset.sum_le_sum fun i _ => hfib i
        _ = _ := by simp
    exact (Finset.card_le_card_sdiff_add_card (s := S) (t := bad.image Prod.fst)).trans
      (Nat.add_le_add hT Finset.card_image_le)
  exact (triple_alteration B G edge _ hsub hcard hremove).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (Finset.card_le_card (Finset.filter_subset _ _)) _))

end Cross142

/- A weighted selection lemma for finite overlapping covers, applied to colored progression charts. -/

open Finset

namespace Cross142

/-- In a weighted cover of a nonempty set, one nonempty chart captures at least its
budget share of the covered population. There is no restriction on chart overlap. -/
theorem chart_share {α ι : Type*} [DecidableEq α] (I : Finset ι) (A : Finset α)
    (B : ι → Finset α) (w : ι → ℕ) {m : ℕ}
    (hA : A.Nonempty) (cover : A ⊆ I.biUnion B) (budget : ∑ i ∈ I, w i ≤ m) :
    ∃ i ∈ I, (B i).Nonempty ∧ A.card * w i ≤ m * (B i).card := by
  classical
  obtain ⟨a, ha⟩ := hA
  obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.mp (cover ha)
  by_contra! h
  have le_sum : A.card ≤ ∑ i ∈ I, (B i).card :=
    (Finset.card_le_card cover).trans Finset.card_biUnion_le
  have hstrict := Finset.sum_lt_sum
    (f := fun i => m * (B i).card) (g := fun i => A.card * w i) (s := I)
    (fun i hi => (B i).eq_empty_or_nonempty.elim
      (fun hzero => by simp [hzero]) (fun hn => (h i hi hn).le))
    ⟨j, hj, h j hj ⟨a, haj⟩⟩
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hstrict
  have cycle := (Nat.mul_le_mul_left m le_sum).trans_lt (hstrict.trans_le
    (Nat.mul_le_mul_left A.card budget))
  simp [Nat.mul_comm] at cycle

/-- Cubic chart budgets combine even when all chart populations are small. -/
theorem productive_chart_of_cover {α ι : Type*} [DecidableEq α] (I : Finset ι)
    (A : Finset α) (B : ι → Finset α) (w cost : ι → ℕ) {m K : ℕ}
    (hA : A.Nonempty) (cover : A ⊆ I.biUnion B) (hm : 0 < m)
    (budget : ∑ i ∈ I, w i ≤ m)
    (costBound : ∀ i ∈ I, cost i * m^3 ≤ K * (w i)^3) :
    ∃ i ∈ I, (B i).Nonempty ∧ A.card^3 * cost i ≤ K * (B i).card^3 := by
  obtain ⟨i, hi, hnon, hshare⟩ := chart_share I A B w hA cover budget
  refine ⟨i, hi, hnon, Nat.le_of_mul_le_mul_right (c := m^3) ?_ (by positivity)⟩
  calc
    _ = A.card^3 * (cost i * m^3) := by ring
    _ ≤ A.card^3 * (K * (w i)^3) := Nat.mul_le_mul_left _ (costBound i hi)
    _ = K * (A.card * w i)^3 := by ring
    _ ≤ K * (m * (B i).card)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hshare 3)
    _ = _ := by ring

/-- A colored atlas with total weight at most m and cubic local cost bounds
gives a single cubic bound for the covered set. -/
theorem atlas_alteration {ι : Type*} (I : Finset ι) (A : Finset ℕ) (B : ι → Finset ℕ)
    (q w : ι → ℕ) (c : (i : ι) → ℕ → Fin (q i)) (E : ι → Finset (ℕ × ℕ))
    {N C m : ℕ} (cover : A ⊆ I.biUnion B) (hm : 0 < m)
    (budget : ∑ i ∈ I, w i ≤ m) (inside : ∀ i ∈ I, B i ⊆ Finset.Icc 1 N)
    (errors : ∀ i ∈ I, ∀ a d : ℕ, 0 < d → a ∈ B i → a+d ∈ B i → a+2*d ∈ B i →
      c i a = c i (a+d) → c i (a+d) = c i (a+2*d) → (a,d) ∈ E i)
    (costBound : ∀ i ∈ I, (q i)^2 * ((B i).card + (E i).card) * m^3 ≤ C*N*(w i)^3) :
    A.card^3 ≤ 64 * C * N * (Erdos142.r 3 N)^2 := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  obtain ⟨i, hi, hnon, hcost⟩ := productive_chart_of_cover I A B w
    (fun i => (q i)^2 * ((B i).card + (E i).card)) hA cover hm budget costBound
  let d := (q i)^2 * ((B i).card + (E i).card)
  have hchart : (B i).card^3 ≤ (64 * (Erdos142.r 3 N)^2) * d := by
    simpa only [d, mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      alteration (B i) (c i) (E i) (inside i hi) (errors i hi)
  have hd : 0 < d := by
    have hb := Finset.card_pos.mpr hnon
    have hq : 0 < q i := Nat.zero_lt_of_lt (c i 0).isLt
    dsimp [d]
    positivity
  refine Nat.le_of_mul_le_mul_right (c := d) ?_ hd
  calc
    _ ≤ C*N*(B i).card^3 := hcost
    _ ≤ C*N*((64*(Erdos142.r 3 N)^2)*d) := Nat.mul_le_mul_left _ hchart
    _ = _ := by ring

end Cross142

namespace Event142
open Finset

/-- Distinct lattice points on one Euclidean sphere do not form a midpoint triple. -/
theorem shell_midpoint {d : ℕ} (x y z : Fin d → ℤ)
    (xy : (∑ i, x i^2) = ∑ i, y i^2)
    (xz : (∑ i, x i^2) = ∑ i, z i^2)
    (mid : ∀ i, x i+z i=2*y i) : x=z := by
  have identity : (∑ i, (x i-z i)^2) =
      2*(∑ i, x i^2)+2*(∑ i, z i^2)-4*(∑ i, y i^2) := by
    simp only [mul_sum,← sum_add_distrib,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    nlinarith only [congrArg (·^2) (mid i)]
  rw [←xy,←xz] at identity
  have zero : ∑ i, (x i-z i)^2=0 := by linarith
  funext i
  have h := (sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j-z j))).mp zero i (mem_univ i)
  nlinarith only [h,sq_nonneg (x i-z i)]

/-- A squared-norm coloring of a partially midpoint-preserving map. Only the
listed failures can survive as monochromatic genuine progressions. -/
theorem shell_certificate (B : Finset ℕ) (E : Finset (ℕ×ℕ)) {d V : ℕ}
    (φ : ℕ → Fin d → ℤ) (inj : Set.InjOn φ (B : Set ℕ))
    (bound : ∀ x∈B, (∑ i, (φ x i)^2) ≤ (V:ℤ))
    (bad : ∀ a t : ℕ, 0<t → a∈B → a+t∈B → a+2*t∈B →
      (¬∀ i, φ a i+φ (a+2*t) i=2*φ (a+t) i) → (a,t)∈E) :
    ∃ c : ℕ → Fin (V+1), ∀ a t : ℕ, 0<t → a∈B → a+t∈B → a+2*t∈B →
      c a=c (a+t) → c a=c (a+2*t) → (a,t)∈E := by
  let w (x : ℕ) := ∑ i, (φ x i)^2
  let c (x : ℕ) : Fin (V+1) := ⟨(w x).toNat%(V+1),Nat.mod_lt _ (by omega)⟩
  have recover (x : ℕ) (hx : x∈B) : ((c x).val:ℤ) = w x := by
    have h := bound x hx
    have hz : 0≤w x := sum_nonneg (fun i _ => sq_nonneg _)
    change (((w x).toNat%(V+1):ℕ):ℤ)=w x
    rw [Nat.mod_eq_of_lt (show (w x).toNat<V+1 by change w x≤(V:ℤ) at h; omega)]
    exact Int.toNat_of_nonneg hz
  refine ⟨c,fun a t ht ha hb hc hab hac => bad a t ht ha hb hc ?_⟩
  intro mid
  have e := shell_midpoint (φ a) (φ (a+t)) (φ (a+2*t))
    ((recover a ha).symm.trans ((congrArg (fun k : Fin (V+1) => (k.val:ℤ)) hab).trans (recover _ hb)))
    ((recover a ha).symm.trans ((congrArg (fun k : Fin (V+1) => (k.val:ℤ)) hac).trans (recover _ hc))) mid
  have eq := inj ha hc e
  omega

/-- The color count can instead be the exact number of distinct norms
appearing in a nonempty input set. -/
theorem shell_certificate_palette (B : Finset ℕ) (nonempty : B.Nonempty) (E : Finset (ℕ×ℕ)) {d : ℕ}
    (φ : ℕ → Fin d → ℤ) (inj : Set.InjOn φ (B : Set ℕ))
    (bad : ∀ a t : ℕ, 0<t → a∈B → a+t∈B → a+2*t∈B →
      (¬∀ i, φ a i+φ (a+2*t) i=2*φ (a+t) i) → (a,t)∈E) :
    ∃ c : ℕ → Fin ((B.image (fun x => ∑ i, (φ x i)^2)).card),
      ∀ a t : ℕ, 0<t → a∈B → a+t∈B → a+2*t∈B →
        c a=c (a+t) → c a=c (a+2*t) → (a,t)∈E := by
  classical
  let w (x : ℕ) := ∑ i, (φ x i)^2
  let P := B.image w
  obtain ⟨b,hb⟩ := nonempty
  let elem (x : ℕ) : P := if hx : x∈B then ⟨w x,mem_image_of_mem _ hx⟩ else ⟨w b,mem_image_of_mem _ hb⟩
  let e : P ≃ Fin P.card := Fintype.equivFinOfCardEq (Fintype.card_coe P)
  let c (x : ℕ) := e (elem x)
  have recover {x y : ℕ} (hx : x∈B) (hy : y∈B) (h : c x=c y) : w x=w y := by
    simpa [elem,hx,hy] using congrArg Subtype.val (e.injective h)
  refine ⟨c,fun a t ht ha hm hz ham haz => bad a t ht ha hm hz ?_⟩
  intro mid
  have eq := inj ha hz (shell_midpoint _ _ _ (recover ha hm ham) (recover ha hz haz) mid)
  omega

end Event142

namespace Event142
open Finset

/-- Prefix values of a mixed-radix digit expansion lie below the next weight. -/
theorem mixed_radix_prefix (b v : ℕ→ℕ) (d : ℕ) (h : ∀ i<d, v i<b i) :
    (∑ i ∈ range d, (∏ j ∈ range i, b j)*v i) < ∏ j ∈ range d,b j := by
  induction d with
  | zero => simp
  | succ d ih =>
    have p := ih (fun i hi => h i (by omega))
    have hl := h d (by omega)
    rw [sum_range_succ,prod_range_succ]
    have t := Nat.mul_le_mul_left (∏ j ∈ range d,b j) (show v d+1≤b d by omega)
    rw [Nat.mul_succ] at t
    omega

theorem mixed_radix_injective (b u v : ℕ→ℕ) (d : ℕ)
    (hu : ∀ i<d, u i<b i) (hv : ∀ i<d, v i<b i)
    (eq : (∑ i ∈ range d, (∏ j ∈ range i,b j)*u i) =
          ∑ i ∈ range d, (∏ j ∈ range i,b j)*v i) :
    ∀ i<d, u i=v i := by
  induction d with
  | zero => omega
  | succ d ih =>
    let W := ∏ j ∈ range d,b j
    let a := ∑ i ∈ range d, (∏ j ∈ range i,b j)*u i
    let z := ∑ i ∈ range d, (∏ j ∈ range i,b j)*v i
    have pu : a<W := mixed_radix_prefix b u d (fun i hi => hu i (by omega))
    have pv : z<W := mixed_radix_prefix b v d (fun i hi => hv i (by omega))
    rw [sum_range_succ,sum_range_succ] at eq
    change a+W*u d=z+W*v d at eq
    have az : a=z := by
      simpa [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt pu,Nat.mod_eq_of_lt pv] using congrArg (·%W) eq
    have uv : u d=v d := by
      rw [az] at eq
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0<W) (Nat.add_left_cancel eq)
    intro i hi
    obtain h|h : i<d ∨ i=d := by omega
    · exact ih (fun k hk => hu k (by omega)) (fun k hk => hv k (by omega)) az i h
    · simpa [h] using uv

/-- A midpoint in a box with double digits below the local bases is a
coordinatewise midpoint. Bases and digit bounds need not be constant. -/
theorem mixed_radix_midpoint (b x y z : ℕ→ℕ) (d : ℕ)
    (hxz : ∀ i<d, x i+z i<b i) (hy : ∀ i<d, 2*y i<b i)
    (eq : (∑ i ∈ range d, (∏ j ∈ range i,b j)*x i)+
      (∑ i ∈ range d, (∏ j ∈ range i,b j)*z i) =
      2*(∑ i ∈ range d, (∏ j ∈ range i,b j)*y i)) :
    ∀ i<d, x i+z i=2*y i := by
  apply mixed_radix_injective b _ _ d hxz hy
  simpa only [mul_add,sum_add_distrib,mul_sum,mul_left_comm] using eq

/-- Every subset of a carry-free mixed-radix box admits a coloring by
concave digit scores. Each color class is free of genuine three-term
progressions. A digit restricted to zero or one needs no extra colors. -/
theorem affine_box_color (B : Finset ℕ) (d : ℕ) (b M : ℕ→ℕ) (v : ℕ→ℕ→ℕ)
    (offset step : ℕ) (hs : 0<step)
    (space : ∀ i<d, 2*M i<b i)
    (digits : ∀ x∈B, ∀ i<d, v x i≤M i)
    (repr : ∀ x∈B, offset+step*(∑ i ∈ range d, (∏ j ∈ range i,b j)*v x i)=x) :
    ∃ c : ℕ → Fin ((∑ i ∈ range d,(M i)^2/4)+1),
      ∀ a t : ℕ, 0<t → a∈B → a+t∈B → a+2*t∈B →
        c a=c (a+t) → c a≠c (a+2*t) := by
  let V := ∑ i ∈ range d,(M i)^2/4
  let score (x : ℕ) := ∑ i ∈ range d,v x i*(M i-v x i)
  let c (x : ℕ) : Fin (V+1) := ⟨score x%(V+1),Nat.mod_lt _ (by omega)⟩
  have bound (x : ℕ) (hx : x∈B) : score x≤V := by
    apply sum_le_sum
    intro i hi
    have u := digits x hx i (mem_range.mp hi)
    apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
    zify [u]
    nlinarith only [sq_nonneg ((M i:ℤ)-2*v x i)]
  have recovers (x : ℕ) (hx : x∈B) : (c x).val=score x :=
    Nat.mod_eq_of_lt (by have := bound x hx; omega)
  let φ (x : ℕ) (i : Fin d) : ℤ := 2*(v x i:ℤ)-(M i:ℤ)
  have identity (x : ℕ) (hx : x∈B) :
      (∑ i, (φ x i)^2) + 4*(score x:ℤ) = ∑ i ∈ range d,(M i:ℤ)^2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (2*(v x i:ℤ)-(M i:ℤ))^2)]
    dsimp only [score]
    push_cast
    rw [mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [Nat.cast_sub (digits x hx i (mem_range.mp hi))]
    ring
  refine ⟨c,fun a t ht ha hm hz e₁ e₂ => ?_⟩
  have p₁ : score a=score (a+t) := (recovers a ha).symm.trans ((congrArg Fin.val e₁).trans (recovers _ hm))
  have p₂ : score a=score (a+2*t) := (recovers a ha).symm.trans ((congrArg Fin.val e₂).trans (recovers _ hz))
  have norm₁ := identity a ha
  have norm₂ := identity (a+t) hm
  have norm₃ := identity (a+2*t) hz
  rw [←p₁] at norm₂
  rw [←p₂] at norm₃
  have mid := mixed_radix_midpoint b (v a) (v (a+t)) (v (a+2*t)) d
    (fun i hi => by have := digits a ha i hi; have := digits _ hz i hi; have := space i hi; omega)
    (fun i hi => by have := digits _ hm i hi; have := space i hi; omega)
    (by
      apply Nat.eq_of_mul_eq_mul_left hs
      rw [mul_add,mul_left_comm step 2]
      have ea := repr a ha
      have em := repr _ hm
      have ez := repr _ hz
      omega)
  have eq := shell_midpoint (φ a) (φ (a+t)) (φ (a+2*t))
    (by linarith only [norm₁,norm₂]) (by linarith only [norm₁,norm₃]) (fun i => by
      have e := mid i i.isLt
      dsimp only [φ]
      omega)
  have digit_eq (i : ℕ) (hi : i<d) : v a i=v (a+2*t) i := by
    have val := congrFun eq ⟨i,hi⟩
    dsimp [φ] at val
    omega
  have sv : (∑ i ∈ range d, (∏ j ∈ range i,b j)*v a i) =
      ∑ i ∈ range d, (∏ j ∈ range i,b j)*v (a+2*t) i := by
    apply sum_congr rfl
    intro i hi
    rw [digit_eq i (mem_range.mp hi)]
  have ea := repr a ha
  rw [sv,repr _ hz] at ea
  omega

theorem mixed_box_color (B : Finset ℕ) (d : ℕ) (b M : ℕ→ℕ) (v : ℕ→ℕ→ℕ)
    (space : ∀ i<d, 2*M i<b i)
    (digits : ∀ x∈B, ∀ i<d, v x i≤M i)
    (repr : ∀ x∈B, (∑ i ∈ range d, (∏ j ∈ range i,b j)*v x i)=x) :
    ∃ c : ℕ → Fin ((∑ i ∈ range d,(M i)^2/4)+1),
      ∀ a t : ℕ, 0<t → a∈B → a+t∈B → a+2*t∈B →
        c a=c (a+t) → c a≠c (a+2*t) :=
  affine_box_color B d b M v 0 1 (by decide) space digits (by simpa using repr)

end Event142

namespace Event142
open Finset

/-- A digit box contains at most the product of its coordinate alphabet sizes.
Injectivity follows from the recovery formula, for any weights and affine scale. -/
theorem affine_box_card (B : Finset ℕ) (d : ℕ) (b M : ℕ→ℕ) (v : ℕ→ℕ→ℕ)
    (offset step : ℕ) (digits : ∀ x∈B, ∀ i<d, v x i≤M i)
    (repr : ∀ x∈B, offset+step*(∑ i ∈ range d,(∏ j ∈ range i,b j)*v x i)=x) :
    B.card ≤ ∏ i ∈ range d,(M i+1) := by
  let f (x : B) (i : Fin d) : Fin (M i+1) := ⟨v x i,Nat.lt_succ_of_le (digits _ x.property _ i.isLt)⟩
  have inj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    calc
      _ = _ := (repr x x.property).symm
      _ = offset+step*(∑ i ∈ range d,(∏ j ∈ range i,b j)*v y i) := by
        congr 2
        apply sum_congr rfl
        intro i hi
        have eq := congrArg Fin.val (congrFun h ⟨i,mem_range.mp hi⟩)
        change v x i=v y i at eq
        rw [eq]
      _ = _ := repr y y.property
  have h := Fintype.card_le_of_injective f inj
  simpa only [Fintype.card_coe,Fintype.card_pi,Fintype.card_fin,Fin.prod_univ_eq_prod_range (fun i => M i+1)] using h

end Event142

namespace Event142
open Finset

/-- Split each digit alphabet into consecutive blocks of at most width mᵢ+1.
The first color records the block, the second the carry-free shell inside it.
Only coordinates wider than one block cost additional block colors. -/
theorem split_box_color (B : Finset ℕ) (d : ℕ) (b M m : ℕ→ℕ) (v : ℕ→ℕ→ℕ)
    (offset step : ℕ) (hs : 0<step) (space : ∀ i<d, 2*m i<b i)
    (digits : ∀ x∈B, ∀ i<d, v x i≤M i)
    (repr : ∀ x∈B, offset+step*(∑ i ∈ range d,(∏ j ∈ range i,b j)*v x i)=x) :
    ∃ c : ℕ→Fin ((∏ i ∈ range d,(M i/(m i+1)+1))*((∑ i ∈ range d,(m i)^2/4)+1)),
      ∀ a t : ℕ, 0<t → a∈B → a+t∈B → a+2*t∈B →
        c a=c (a+t) → c a≠c (a+2*t) := by
  classical
  let T := (i : Fin d)→Fin (M i/(m i+1)+1)
  let K := (∑ i ∈ range d,(m i)^2/4)+1
  let u (x i : ℕ) := v x i%(m i+1)
  let bin (x : ℕ) (i : Fin d) : Fin (M i/(m i+1)+1) :=
    ⟨(v x i/(m i+1))%(M i/(m i+1)+1),Nat.mod_lt _ (Nat.succ_pos _)⟩
  have right (x : ℕ) (hx : x∈B) (i : Fin d) : (bin x i).val=v x i/(m i+1) := by
    apply Nat.mod_eq_of_lt
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (digits _ hx _ i.isLt))
  let pieces (r : T) := B.filter fun x => bin x=r
  have localized (r : T) :
      ∃ c : ℕ→Fin K, ∀ a t : ℕ, 0<t → a∈pieces r → a+t∈pieces r → a+2*t∈pieces r →
        c a=c (a+t) → c a≠c (a+2*t) := by
    let high (i : ℕ) := if hi : i<d then (r ⟨i,hi⟩).val*(m i+1) else 0
    let off := offset+step*(∑ i ∈ range d,(∏ j ∈ range i,b j)*high i)
    apply affine_box_color (pieces r) d b m u off step hs space
    · intro x _ i _
      exact Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
    · intro x hx
      obtain ⟨inB,br⟩ := mem_filter.mp hx
      have expand (i : ℕ) (hi : i∈range d) : high i+u x i=v x i := by
        have hi' := mem_range.mp hi
        have cut := right x inB ⟨i,hi'⟩
        rw [br] at cut
        dsimp [high,u]
        rw [dif_pos hi',cut,mul_comm,add_comm]
        exact Nat.mod_add_div _ _
      calc
        _ = offset+step*(∑ i ∈ range d,(∏ j ∈ range i,b j)*(high i+u x i)) := by
          simp only [off,mul_add,sum_add_distrib,add_assoc]
        _ = x := by
          convert repr x inB using 3
          apply sum_congr rfl
          intro i hi
          rw [expand i hi]
  choose inside agood using localized
  let C := (∏ i ∈ range d,(M i/(m i+1)+1))*K
  have size : Fintype.card (T×Fin K)=C := by
    simp only [T,C,Fintype.card_prod,Fintype.card_pi,Fintype.card_fin,
      Fin.prod_univ_eq_prod_range (fun i => M i/(m i+1)+1)]
  let e : (T×Fin K) ≃ Fin C := Fintype.equivFinOfCardEq size
  let c (x : ℕ) := e (bin x,inside (bin x) x)
  refine ⟨c,fun a t ht ha hb hz h₁ h₂ => ?_⟩
  have h₁' := e.injective h₁
  have h₂' := e.injective h₂
  have ab := congrArg Prod.fst h₁'
  have az := congrArg Prod.fst h₂'
  change bin a=bin (a+t) at ab
  change bin a=bin (a+2*t) at az
  have y := congrArg Prod.snd h₁'
  have z := congrArg Prod.snd h₂'
  change inside (bin a) a=inside (bin (a+t)) (a+t) at y
  change inside (bin a) a=inside (bin (a+2*t)) (a+2*t) at z
  rw [←ab] at y
  rw [←az] at z
  exact agood (bin a) a t ht (mem_filter.mpr ⟨ha,rfl⟩) (mem_filter.mpr ⟨hb,ab.symm⟩)
    (mem_filter.mpr ⟨hz,az.symm⟩) y z

end Event142

namespace Event142
open Finset

/-- When only the axes in S may carry, splitting those axes in half
charges at most one binary decision per exceptional coordinate. -/
theorem half_split_color (B : Finset ℕ) (d : ℕ) (S : Finset ℕ) (b M : ℕ→ℕ) (v : ℕ→ℕ→ℕ)
    (offset step : ℕ) (hs : 0<step) (bounded : ∀ i<d, M i<b i)
    (guard : ∀ i<d, i∉S → 2*M i<b i)
    (digits : ∀ x∈B, ∀ i<d, v x i≤M i)
    (repr : ∀ x∈B, offset+step*(∑ i ∈ range d,(∏ j ∈ range i,b j)*v x i)=x) :
    let m := fun i => if i∈S then (b i-1)/2 else M i
    ∃ c : ℕ→Fin (2^S.card*((∑ i ∈ range d,(m i)^2/4)+1)),
      ∀ a t : ℕ, 0<t → a∈B → a+t∈B → a+2*t∈B →
        c a=c (a+t) → c a≠c (a+2*t) := by
  intro m
  have space (i : ℕ) (hi : i<d) : 2*m i<b i := by
    by_cases e : i∈S
    · have := bounded i hi
      dsimp [m]
      rw [if_pos e]
      omega
    · simpa [m,e] using guard i hi e
  have each (i : ℕ) (hi : i∈range d) :
      M i/(m i+1)+1 ≤ if i∈S then 2 else 1 := by
    have bd := bounded i (mem_range.mp hi)
    by_cases h : i∈S
    · dsimp [m]
      rw [if_pos h,if_pos h]
      have x : M i/((b i-1)/2+1)<2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
      omega
    · simp [m,h,Nat.div_eq_of_lt (Nat.lt_succ_self _)]
  have upper : (∏ i ∈ range d,(M i/(m i+1)+1))≤2^S.card := by
    have h := Finset.prod_le_prod' each
    rw [Finset.prod_ite_mem (range d) S (fun _ : ℕ => 2),Finset.prod_const] at h
    exact h.trans (Nat.pow_le_pow_right (by decide) (Finset.card_le_card Finset.inter_subset_right))
  obtain ⟨c,hc⟩ := split_box_color B d b M m v offset step hs space digits repr
  let emb := Fin.castLEEmb (Nat.mul_le_mul_right ((∑ i∈range d,(m i)^2/4)+1) upper)
  exact ⟨fun x => emb (c x),fun a t ht ha hm hz e f =>
    hc a t ht ha hm hz (emb.injective e) (emb.injective f)⟩

end Event142

namespace Cross142

/-- Polynomially many shell pairs fit inside the exponential loss in a carry-free box. -/
theorem shell_growth (d : ℕ) : (d+5)^2*2^d ≤ 25*3^d := by
  induction d with
  | zero => decide
  | succ d ih =>
    have step : (d+1+5)^2*2 ≤ 3*(d+5)^2 := by nlinarith only [Nat.zero_le d, Nat.zero_le (d^2)]
    calc (d+1+5)^2*2^(d+1) = ((d+1+5)^2*2)*2^d := by ring
         _ ≤ (3*(d+5)^2)*2^d := Nat.mul_le_mul_right _ step
         _ = 3*((d+5)^2*2^d) := by ring
         _ ≤ 3*(25*3^d) := Nat.mul_le_mul_left _ ih
         _ = 25*3^(d+1) := by ring

theorem box_shell_cost {d L q s N : ℕ} (hq : q ≤ 1+d*L^2) (hs : s*3^d ≤ N*2^d) :
    q^2*s ≤ 25*(L^2+1)^2*N := by
  have h1 : q ≤ (L^2+1)*(d+5) := hq.trans (by nlinarith only [Nat.zero_le d, Nat.zero_le (L^2)])
  have h2 := Nat.pow_le_pow_left h1 2
  have ha : q^2*2^d ≤ 25*(L^2+1)^2*3^d := calc
    _ ≤ ((L^2+1)*(d+5))^2*2^d := Nat.mul_le_mul_right _ h2
    _ = (L^2+1)^2*((d+5)^2*2^d) := by ring
    _ ≤ (L^2+1)^2*(25*3^d) := Nat.mul_le_mul_left _ (shell_growth d)
    _ = _ := by ring
  apply Nat.le_of_mul_le_mul_right (c:=3^d)
  · calc
      (q^2*s)*3^d = q^2*(s*3^d) := by ring
      _ ≤ q^2*(N*2^d) := Nat.mul_le_mul_left _ hs
      _ = N*(q^2*2^d) := by ring
      _ ≤ N*(25*(L^2+1)^2*3^d) := Nat.mul_le_mul_left _ ha
      _ = _ := by ring
  · positivity

/-- Product estimate for coordinate-dependent digit caps and radices. -/
theorem digit_box_density {d : ℕ} (m b : Fin d → ℕ)
    (hm : ∀ i, 1 ≤ m i) (hb : ∀ i, 2*m i < b i) :
    (∏ i, (m i+1))*3^d ≤ (∏ i, b i)*2^d := by
  have hc : ∀ i, (m i+1)*3 ≤ b i*2 := fun i => by have := hm i; have := hb i; omega
  simpa [Finset.prod_mul_distrib] using
    (Finset.prod_le_prod' (s := (Finset.univ : Finset (Fin d))) (fun i _ => hc i))

/-- A small chart suffices when its cubic gain pays for both its palette and its errors. -/
theorem productive_chart {s a e q K N R : ℕ} (hp : 0 < s)
    (alt : s^3 ≤ 64*(q*R)^2*(s+e))
    (hm : a^3*q^2*(s+e) ≤ K*N*s^3) : a^3 ≤ 64*K*N*R^2 := by
  apply Nat.le_of_mul_le_mul_right (c:=s^3) _ (pow_pos hp _)
  calc a^3*s^3 ≤ a^3*(64*(q*R)^2*(s+e)) := Nat.mul_le_mul_left _ alt
       _ = (64*R^2)*(a^3*q^2*(s+e)) := by ring
       _ ≤ (64*R^2)*(K*N*s^3) := Nat.mul_le_mul_left _ hm
       _ = _ := by ring

end Cross142

namespace Cross142

open Finset Erdos142

/-- A proper coloring gives the exact pigeonhole bound even for very small boxes. -/
theorem proper_color_bound {q N : ℕ} (B : Finset ℕ) (hB : B ⊆ Icc 1 N)
    (c : ℕ → Fin q) (hc : ∀ a t : ℕ, 0<t → a∈B → a+t∈B → a+2*t∈B →
      c a = c (a+t) → c a ≠ c (a+2*t)) : B.card ≤ q*r 3 N := by
  classical
  calc B.card = ∑ i : Fin q, (B.filter (fun x => c x=i)).card := by
         simpa using (sum_card_fiberwise_eq_card_filter B univ c).symm
       _ ≤ ∑ _i : Fin q, r 3 N := by
         apply sum_le_sum
         intro i _
         apply card_no_triple _ ((filter_subset _ _).trans hB)
         intro a t ht ha hm he
         obtain ⟨ha,ea⟩ := mem_filter.mp ha
         obtain ⟨hm,em⟩ := mem_filter.mp hm
         obtain ⟨he,ee⟩ := mem_filter.mp he
         exact hc a t ht ha hm he (ea.trans em.symm) (ea.trans ee.symm)
       _ = _ := by simp

/-- Uniform in dimension, the radices, translation, dilation, and the subset of
the box. The alphabet bound L alone determines the comparison constant. -/
theorem affine_digit_box_cubic (B : Finset ℕ) (d N L : ℕ) (b M : ℕ → ℕ)
    (v : ℕ → ℕ → ℕ) (offset step : ℕ) (hstep : 0 < step)
    (hB : B ⊆ Icc 1 N) (hN : (∏ i ∈ range d, b i) ≤ N)
    (caps : ∀ i<d, 1 ≤ M i ∧ M i ≤ L) (space : ∀ i<d, 2*M i < b i)
    (digits : ∀ x∈B, ∀ i<d, v x i ≤ M i)
    (repr : ∀ x∈B, offset+step*(∑ i ∈ range d,(∏ j ∈ range i,b j)*v x i)=x) :
    B.card^3 ≤ 25*(L^2+1)^2*N*(r 3 N)^2 := by
  classical
  let q := (∑ i ∈ range d, (M i)^2/4)+1
  obtain ⟨c,hc⟩ := Event142.affine_box_color B d b M v offset step hstep space digits repr
  have hq : q ≤ 1+d*L^2 := by
    have hh : (∑ i ∈ range d, (M i)^2/4) ≤ ∑ _i ∈ range d, L^2 :=
      sum_le_sum fun i hi => (Nat.div_le_self _ _).trans
        (Nat.pow_le_pow_left (caps i (mem_range.mp hi)).2 2)
    simpa [q, Nat.add_comm, Nat.succ_le_succ_iff] using Nat.succ_le_succ hh
  have hb : B.card ≤ ∏ i ∈ range d, (M i+1) :=
    Event142.affine_box_card B d b M v offset step digits repr
  have hd := digit_box_density (fun i : Fin d => M i) (fun i : Fin d => b i)
    (fun i => (caps i i.isLt).1) (fun i => space i i.isLt)
  have hd' : (∏ i ∈ range d,(M i+1))*3^d ≤ (∏ i ∈ range d,b i)*2^d := by
    simpa only [Fin.prod_univ_eq_prod_range (fun i => M i+1), Fin.prod_univ_eq_prod_range b] using hd
  have hcost := box_shell_cost hq (((Nat.mul_le_mul_right _ hb).trans hd').trans
    (Nat.mul_le_mul_right _ hN))
  have hcol : B.card ≤ q*r 3 N := proper_color_bound B hB c hc
  calc B.card^3 = B.card*B.card^2 := by ring
       _ ≤ B.card*(q*r 3 N)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcol 2)
       _ = (q^2*B.card)*(r 3 N)^2 := by ring
       _ ≤ _ := Nat.mul_le_mul_right _ hcost

end Cross142

/- Cubic comparison for mixed-radix boxes with exceptional carry coordinates. -/

namespace Cross142
open Finset Erdos142

/-- Each exceptional coordinate costs at most a factor of six in the cubic
comparison, independently of dimension and the radices. -/
theorem affine_hybrid_box_cubic (B : Finset ℕ) (d N L : ℕ) (S : Finset ℕ)
    (b M : ℕ → ℕ) (v : ℕ → ℕ → ℕ) (offset step : ℕ) (hstep : 0 < step)
    (hB : B ⊆ Icc 1 N) (hN : (∏ i ∈ range d, b i) ≤ N)
    (caps : ∀ i<d, 1 ≤ M i ∧ M i ≤ L) (bounded : ∀ i<d, M i < b i)
    (guard : ∀ i<d, i∉S → 2*M i < b i)
    (digits : ∀ x∈B, ∀ i<d, v x i ≤ M i)
    (repr : ∀ x∈B, offset+step*(∑ i ∈ range d,(∏ j ∈ range i,b j)*v x i)=x) :
    B.card^3 ≤ 25*6^S.card*(L^2+1)^2*N*(r 3 N)^2 := by
  classical
  let T := (range d).filter fun i => b i ≤ 2*M i
  have sub : T ⊆ S := by
    intro i hi
    obtain ⟨h₁,h₂⟩ := mem_filter.mp hi
    by_contra hout
    exact (not_lt_of_ge h₂) (guard i (mem_range.mp h₁) hout)
  have guard' : ∀ i<d, i∉T → 2*M i<b i := by
    intro i hi h
    simpa [T,hi] using h
  let m := fun i => if i∈T then (b i-1)/2 else M i
  let q := (∑ i ∈ range d, (m i)^2/4)+1
  obtain ⟨c,hc⟩ := Event142.half_split_color B d T b M v offset step hstep bounded guard' digits repr
  have hcol : B.card ≤ (2^T.card*q)*r 3 N := proper_color_bound B hB c hc
  have hm (i : ℕ) (hi : i<d) : m i ≤ L := by
    have cap := (caps i hi).2
    by_cases h : i∈T
    · have hb := (mem_filter.mp h).2
      simp only [m, if_pos h]
      omega
    · simpa [m,h] using cap
  have hq : q ≤ 1+d*L^2 := by
    have hh : (∑ i ∈ range d, (m i)^2/4) ≤ ∑ _i ∈ range d, L^2 :=
      sum_le_sum fun i hi => (Nat.div_le_self _ _).trans
        (Nat.pow_le_pow_left (hm i (mem_range.mp hi)) 2)
    simpa [q,Nat.add_comm,Nat.succ_le_succ_iff] using Nat.succ_le_succ hh
  have hT : range d ∩ T = T := inter_eq_right.mpr (filter_subset _ _)
  have factor (i : ℕ) (hi : i∈range d) :
      (M i+1)*3*(if i∈T then 2 else 1) ≤ b i*2*(if i∈T then 3 else 1) := by
    have hd := mem_range.mp hi
    have hm1 := (caps i hd).1
    have hlt := bounded i hd
    by_cases h : i∈T
    · simp only [if_pos h]; omega
    · have hs := guard' i hd h
      simp only [if_neg h, mul_one]; omega
  have den := Finset.prod_le_prod' factor
  simp only [prod_mul_distrib, prod_const, card_range,
    prod_ite_mem (range d) T (fun _ : ℕ => 2),
    prod_ite_mem (range d) T (fun _ : ℕ => 3), hT] at den
  have hb := Event142.affine_box_card B d b M v offset step digits repr
  have hdens : (2^T.card*B.card)*3^d ≤ (3^T.card*N)*2^d := calc
    _ ≤ ((∏ i ∈ range d,(M i+1))*3^d)*2^T.card := by
      rw [show (2^T.card*B.card)*3^d = B.card*3^d*2^T.card by ring]
      gcongr
    _ ≤ ((∏ i ∈ range d,b i)*2^d)*3^T.card := den
    _ ≤ _ := by
      rw [show 3^T.card*N*2^d = N*2^d*3^T.card by ring]
      gcongr
  have hcost := box_shell_cost hq hdens
  calc B.card^3 = B.card*B.card^2 := by ring
       _ ≤ B.card*((2^T.card*q)*r 3 N)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hcol 2)
       _ = (q^2*(2^T.card*B.card))*2^T.card*(r 3 N)^2 := by ring
       _ ≤ (25*(L^2+1)^2*(3^T.card*N))*2^T.card*(r 3 N)^2 := by gcongr
       _ = 25*6^T.card*(L^2+1)^2*N*(r 3 N)^2 := by
         rw [show (6:ℕ)=3*2 by decide, mul_pow]
         ring
       _ ≤ _ := by
         have hh : (6:ℕ)^T.card ≤ 6^S.card :=
           Nat.pow_le_pow_right (by decide) (card_le_card sub)
         exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
           (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 25 hh)))

end Cross142

/- Interval localization of the cubic bound for four-term-progression-free sets. -/

open Erdos142 Filter
open OMA.R_Erdos142_erdos_142_variants_lower_R2

namespace Cross142

theorem localize_cubic (K : ℕ)
    (h : ∀ (N : ℕ) (A : Finset ℕ), 0 < N → A ⊆ Finset.Icc 1 N →
      (A : Set ℕ).IsAPOfLengthFree 4 →
      (∀ t M : ℕ, 0 < M → M < N →
        N * (A ∩ Finset.Icc (t+1) (t+M)).card ^ 3 < M * A.card ^ 3) →
      A.card ^ 3 ≤ K * N * (r 3 N) ^ 2) :
    ∀ (N : ℕ) (A : Finset ℕ), 0 < N → A ⊆ Finset.Icc 1 N →
      (A : Set ℕ).IsAPOfLengthFree 4 → A.card ^ 3 ≤ K * N * (r 3 N) ^ 2 := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro A hN hsub hfree
    by_cases hs : ∀ t M : ℕ, 0 < M → M < N →
        N * (A ∩ Finset.Icc (t+1) (t+M)).card ^ 3 < M * A.card ^ 3
    · exact h N A hN hsub hfree hs
    push Not at hs
    obtain ⟨t, M, hM, hMN, hd⟩ := hs
    let J := A ∩ Finset.Icc (t+1) (t+M)
    let B := J.image (fun x ↦ x-t)
    have hB : B ⊆ Finset.Icc 1 M := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp (Finset.mem_inter.mp hy).2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hfB : (B : Set ℕ).IsAPOfLengthFree 4 := by
      intro U hU hAP
      apply hfree ((fun x : ℕ ↦ t+x) '' U) _ (isAPOfLength_translate hAP t)
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hU hx)
      obtain ⟨hyA, hyI⟩ := Finset.mem_inter.mp hy
      have hlo := (Finset.mem_Icc.mp hyI).1
      change t + (y-t) ∈ A
      rwa [Nat.add_sub_of_le (by omega : t ≤ y)]
    have hc : B.card = J.card := by
      apply Finset.card_image_of_injOn
      intro x hx y hy heq
      have hlo := (Finset.mem_Icc.mp (Finset.mem_inter.mp hx).2).1
      have hlo' := (Finset.mem_Icc.mp (Finset.mem_inter.mp hy).2).1
      change x-t = y-t at heq
      omega
    have hmono : r 3 M ≤ r 3 N := maxCard_monotone 3 hMN.le
    have hmul : M * A.card ^ 3 ≤ M * (K * N * (r 3 N)^2) := calc
      M * A.card ^ 3 ≤ N * J.card ^ 3 := hd
      _ = N * B.card ^ 3 := by rw [hc]
      _ ≤ N * (K * M * (r 3 M)^2) := Nat.mul_le_mul_left N (ih M hMN B hM hB hfB)
      _ ≤ N * (K * M * (r 3 N)^2) := by gcongr
      _ = M * (K * N * (r 3 N)^2) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hM

theorem target_of_cubic (K : ℕ)
    (h : ∀ (N : ℕ) (A : Finset ℕ), 0 < N → A ⊆ Finset.Icc 1 N →
      (A : Set ℕ).IsAPOfLengthFree 4 → A.card ^ 3 ≤ K * N * (r 3 N) ^ 2) :
    OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2.H1 := by
  classical
  refine ⟨2/3, (K:ℝ)+1, by norm_num, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  let C : Set ℕ := {m | ∃ S : Finset ℕ, ∃ _ : S ⊆ Finset.Icc 1 N,
    ∃ _ : (S : Set ℕ).IsAPOfLengthFree 4, S.card = m}
  have hz : 0 ∈ C := by
    refine ⟨∅, Finset.empty_subset _, ?_, rfl⟩
    intro S hs hap
    have he : S = ∅ := Set.subset_empty_iff.mp (by simpa using hs)
    subst S
    obtain ⟨_, _, hc, _⟩ := hap
    simp at hc
  have hb : BddAbove C := by
    refine ⟨N, ?_⟩
    rintro _ ⟨S, hS, -, rfl⟩
    simpa using Finset.card_le_card hS
  obtain ⟨A, hs, hf, ha⟩ := Nat.sSup_mem ⟨0, hz⟩ hb
  have he : r 4 N = A.card := ha.symm
  have hr : (r 4 N : ℝ)^3 ≤ (K:ℝ)*N*(r 3 N:ℝ)^2 := by
    rw [he]
    exact_mod_cast h N A hN hs hf
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hx : 0 ≤ (r 3 N:ℝ)/(N:ℝ) := by positivity
  have ht : (((r 3 N:ℝ)/N)^(2/3:ℝ))^3 = ((r 3 N:ℝ)/N)^2 := by
    calc
      _ = (((r 3 N:ℝ)/N)^(2/3:ℝ))^(3:ℝ) := (Real.rpow_natCast _ 3).symm
      _ = ((r 3 N:ℝ)/N)^((2/3:ℝ)*3) := (Real.rpow_mul hx _ _).symm
      _ = _ := by norm_num
  have hK : (K:ℝ) ≤ ((K:ℝ)+1)^3 := by nlinarith [sq_nonneg (K:ℝ), pow_nonneg (Nat.cast_nonneg (α:=ℝ) K) 3]
  have hcube : (r 4 N:ℝ)^3 ≤ (((K:ℝ)+1)*N*((r 3 N:ℝ)/N)^(2/3:ℝ))^3 := calc
    _ ≤ (K:ℝ)*N*(r 3 N:ℝ)^2 := hr
    _ ≤ ((K:ℝ)+1)^3*N*(r 3 N:ℝ)^2 := by gcongr
    _ = _ := by
      rw [mul_pow, mul_pow, ht]
      field_simp
  by_contra! hgt
  have hall : (((K:ℝ)+1)*N*((r 3 N:ℝ)/N)^(2/3:ℝ))^3 < (r 4 N:ℝ)^3 := by gcongr
  exact (not_lt_of_ge hcube) hall

end Cross142

namespace OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R2

open Finset Erdos142

/-- For an interval-flat, triple-rich set with small sumset, seek a piece with an
injective integer model. The cost counts its distinct squared norms and the
triples where the model fails to preserve the midpoint. -/
def H1 : Prop :=
  ∃ K : ℕ, ∀ (N : ℕ) (A : Finset ℕ), 0 < N → A ⊆ Finset.Icc 1 N →
    (A : Set ℕ).IsAPOfLengthFree 4 →
    (∀ t M : ℕ, 0 < M → M < N →
      N*(A ∩ Finset.Icc (t+1) (t+M)).card^3 < M*A.card^3) →
    N < ((A ×ˢ Finset.Icc 1 N).filter (fun p => p.1+p.2∈A ∧ p.1+2*p.2∈A)).card →
    ((A ×ˢ A).image (fun p => p.1+p.2)).card^2 ≤ N*A.card →
    ∃ B ⊆ A, B.Nonempty ∧ ∃ (d : ℕ) (φ : ℕ → Fin d → ℤ) (E : Finset (ℕ×ℕ)),
      Set.InjOn φ (B : Set ℕ) ∧
      (∀ a t : ℕ, 0<t → a∈B → a+t∈B → a+2*t∈B →
        (¬∀ i, φ a i + φ (a+2*t) i = 2*φ (a+t) i) → (a,t)∈E) ∧
      A.card^3 * ((B.image (fun x => ∑ i, (φ x i)^2)).card)^2 * (B.card+E.card)
        ≤ K*N*B.card^3

/-- In the complementary large-sumset regime, seek a piece and a coloring
with a quantitative budget for the monochromatic progressions. A piece may be
small if the resulting palette and error count are correspondingly cheap. -/
def H2 : Prop :=
  ∃ K : ℕ, ∀ (N : ℕ) (A : Finset ℕ), 0 < N → A ⊆ Finset.Icc 1 N →
    (A : Set ℕ).IsAPOfLengthFree 4 →
    (∀ t M : ℕ, 0 < M → M < N →
      N*(A ∩ Finset.Icc (t+1) (t+M)).card^3 < M*A.card^3) →
    N < ((A ×ˢ Finset.Icc 1 N).filter (fun p => p.1+p.2∈A ∧ p.1+2*p.2∈A)).card →
    N*A.card < ((A ×ˢ A).image (fun p => p.1+p.2)).card^2 →
    ∃ B ⊆ A, B.Nonempty ∧ ∃ (q : ℕ) (c : ℕ → Fin q) (E : Finset (ℕ×ℕ)),
      (∀ a t : ℕ, 0<t → a∈B → a+t∈B → a+2*t∈B →
        c a = c (a+t) → c (a+t) = c (a+2*t) → (a,t)∈E) ∧
      A.card^3*q^2*(B.card+E.card) ≤ K*N*B.card^3

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2.H1 := by
  classical
  rintro ⟨K, hsmall⟩ ⟨L, hlarge⟩
  let D := 64*(K+L+2)
  apply Cross142.target_of_cubic D
  apply Cross142.localize_cubic D
  intro N A hN hA hfree hflat
  let T := (A ×ˢ Finset.Icc 1 N).filter (fun p => p.1+p.2∈A ∧ p.1+2*p.2∈A)
  by_cases hs : T.card ≤ N
  · let c : ℕ → Fin 1 := fun _ => 0
    have h := Cross142.alteration A c T hA (by
      intro a t ht ha hm he _ _
      have hn := (Finset.mem_Icc.mp (hA he)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, Finset.mem_Icc.mpr ⟨ht, by omega⟩⟩, hm, he⟩)
    have ha : A.card ≤ N := by simpa using Finset.card_le_card hA
    calc A.card^3 ≤ 64*(r 3 N)^2*(A.card+T.card) := by simpa using h
         _ ≤ 64*(r 3 N)^2*(2*N) := Nat.mul_le_mul_left _ (by omega)
         _ = 128*N*(r 3 N)^2 := by ring
         _ ≤ D*N*(r 3 N)^2 := by
           apply Nat.mul_le_mul_right
           apply Nat.mul_le_mul_right
           dsimp [D]
           omega
  have hr : N < T.card := by omega
  by_cases hd : ((A ×ˢ A).image (fun p => p.1+p.2)).card^2 ≤ N*A.card
  · obtain ⟨B,hBA,hB,d,φ,E,hinj,hbad,hcost⟩ := hsmall N A hN hA hfree hflat hr hd
    obtain ⟨c,hc⟩ := Event142.shell_certificate_palette B hB E φ hinj hbad
    have ha := Cross142.alteration B c E (hBA.trans hA) (fun a t ht h₀ h₁ h₂ e₀ e₁ =>
      hc a t ht h₀ h₁ h₂ e₀ (e₀.trans e₁))
    exact (Cross142.productive_chart (Finset.card_pos.mpr hB) ha hcost).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (show 64*K ≤ D by dsimp [D]; omega)))
  · obtain ⟨B,hBA,hB,q,c,E,hc,hcost⟩ := hlarge N A hN hA hfree hflat hr (lt_of_not_ge hd)
    have ha := Cross142.alteration B c E (hBA.trans hA) hc
    exact (Cross142.productive_chart (Finset.card_pos.mpr hB) ha hcost).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (show 64*L ≤ D by dsimp [D]; omega)))

end OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R2

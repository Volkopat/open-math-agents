import OMAReductions.R_RamseyNumbers_ramsey_number_three_nine_R2
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.FinCases

/-!
# Minimum edge counts at orders 19, 20, 21 and 22 for (3,7)-graphs

A triangle-free graph with no independent seven-set has at least 37, 44, 51,
or 59 edges at the four respective orders. Summing the exact edge counts
outside closed neighborhoods forces any potential counterexample at orders
19 through 21 to contain a sparse (3,6)-graph on 14 or 15 vertices.
A budgeted enumeration classifies both graphs. Four integer weighted inequalities
on their independent sets rule out all the required extensions.

The smaller density bounds and enumeration adapt @dasante78's #12460,
@Deldor14's #5749 and budgeted traversal #6220, and @physbuzz's neighborhood identity. The coding
and contact lemmas adapt the parent reduction of @sturdy4days (#13293).
The two reference codes are from Brendan McKay's Ramsey graph catalogue:
https://users.cecs.anu.edu.au/~bdm/data/r36_14.g6.gz and
https://users.cecs.anu.edu.au/~bdm/data/r36_15.g6.gz .
The code checks the classifications and weighted certificates in Lean.
The numerical entries are also tabulated by Goedgebeur and Radziszowski,
Electronic Journal of Combinatorics 20(1), P30 (2013).
-/
/- Small triangle-free graph edge bounds. The Graver–Yackel lemma and lower-order
    estimates below adapt the checked framework of @dasante78 (#12460) and its
    use of @physbuzz's neighborhood degree identities. -/
namespace Ramsey39Children

open RamseyNumbers SimpleGraph Finset
open RamseyDeficiency (removed sum_neighbor_degrees)

lemma degree_lt {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree k) (v : Fin n) : G.degree v < k := by
  by_contra! h
  apply hc.mono h (G.neighborFinset v)
  refine ⟨?_, rfl⟩
  rw [G.coe_neighborFinset, G.isClique_compl]
  exact G.isIndepSet_neighborSet_of_triangleFree hG v

-- An independent k-set among non-neighbours extends to an independent (k+1)-set.
lemma nonneighbors_lt {n k m : ℕ} (hr : IsGraphRamsey m 3 k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hc : Gᶜ.CliqueFree (k + 1)) (v : Fin n) : Gᶜ.degree v < m := by
  classical
  by_contra! h
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin m) (s := Gᶜ.neighborFinset v) (by simpa using h)
  have hv (i : Fin m) : Gᶜ.Adj v (f i) :=
    (Gᶜ.mem_neighborFinset v (f i)).mp (hf ⟨i, rfl⟩)
  let H := G.comap f
  let e : H ↪g G := SimpleGraph.Embedding.comap f G
  let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
  apply hr H
  refine ⟨CliqueFree.comap e.isContained hG, ?_⟩
  intro t ht
  have hs : Gᶜ.IsNClique k (t.map f) := by
    refine ⟨?_, (Finset.card_map _).trans ht.card_eq⟩
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    exact ec.map_adj_iff.mpr (ht.isClique hi hj (fun he => hxy (congrArg f he)))
  apply hc _ (hs.insert (a := v) ?_)
  intro w hw
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
  exact hv i

lemma three_works : IsGraphRamsey 3 3 2 := by
  classical
  rintro G ⟨hG, hc⟩
  apply hG Finset.univ
  refine ⟨?_, by simp⟩
  intro u _ v _ hne
  by_contra h
  apply hc {u, v}
  refine ⟨?_, Finset.card_pair hne⟩
  intro a ha b hb hab
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  refine ⟨hab, ?_⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab rfl).elim
  · exact h
  · exact fun h' => h h'.symm
  · exact (hab rfl).elim

lemma six_works : IsGraphRamsey 6 3 3 := by
  classical
  rintro G ⟨hG, hc⟩
  have hd := degree_lt G hG hc 0
  have hdc := degree_lt Gᶜ hc (by simpa using hG : Gᶜᶜ.CliqueFree 3) 0
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

lemma nine_works : IsGraphRamsey 9 3 4 := by
  classical
  rintro G ⟨hG, hc⟩
  have hdegree (v : Fin 9) : G.degree v = 3 := by
    have hd := degree_lt G hG hc v
    have hdc := nonneighbors_lt six_works G hG hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp [hdegree] at hsum
  omega

lemma fourteen_works : IsGraphRamsey 14 3 5 := by
  classical
  rintro G ⟨hG, hc⟩
  have hd := degree_lt G hG hc 0
  have hdc := nonneighbors_lt nine_works G hG hc 0
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

lemma card_edgeFinset_ge_sub {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc : Gᶜ.CliqueFree k) : n + 1 - k ≤ G.edgeFinset.card := by
  classical
  let S : Finset (Fin n) := G.edgeFinset.image (fun e => e.out.1)
  have hS : S.card ≤ G.edgeFinset.card := Finset.card_image_le
  have hindep : Gᶜ.IsClique ((Sᶜ : Finset (Fin n)) : Set (Fin n)) := by
    intro u hu v hv hne
    refine ⟨hne, fun hadj => ?_⟩
    let e : Sym2 (Fin n) := s(u, v)
    have hmem : e ∈ G.edgeFinset := G.mem_edgeFinset.mpr hadj
    have hpt : e.out.1 ∈ e := by
      have hq : s(e.out.1, e.out.2) = e := Quot.out_eq e
      exact Eq.mp (congrArg (fun x => e.out.1 ∈ x) hq) (by simp)
    have hinS : e.out.1 ∈ S := Finset.mem_image.mpr ⟨e, hmem, rfl⟩
    rcases Sym2.mem_iff.mp hpt with heq | heq
    · rw [heq] at hinS
      exact (Finset.mem_compl.mp (Finset.mem_coe.mp hu)) hinS
    · rw [heq] at hinS
      exact (Finset.mem_compl.mp (Finset.mem_coe.mp hv)) hinS
  have hlt : Sᶜ.card < k := by
    by_contra! hge
    exact hc.mono hge Sᶜ ⟨hindep, rfl⟩
  have hcompl := Finset.card_compl_add_card S
  rw [Fintype.card_fin] at hcompl
  omega

lemma gy_step {n k m : ℕ} (hr : IsGraphRamsey m 3 k) (lb : ℕ → ℕ)
    (hlb : ∀ d, n - 1 - d < m → ∀ (H : SimpleGraph (Fin (n - 1 - d))) [DecidableRel H.Adj],
      H.CliqueFree 3 → Hᶜ.CliqueFree k → lb (n - 1 - d) ≤ H.edgeFinset.card)
    (a b : ℕ)
    (hstep : ∀ d, d ≤ k → n - 1 - d < m → a + b * d ≤ d ^ 2 + lb (n - 1 - d))
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree (k + 1)) :
    n * a + 2 * b * G.edgeFinset.card ≤ n * G.edgeFinset.card := by
  have hlocal (v : Fin n) :
      lb (n - 1 - G.degree v) + ∑ w ∈ G.neighborFinset v, G.degree w ≤ G.edgeFinset.card := by
    have hdc := nonneighbors_lt hr G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    obtain ⟨H,dec,htH,hiH,heH⟩ := RamseyDeficiency.extract_anti
      (m := n - 1 - G.degree v) G ht hc v (by rw [G.degree_compl,Fintype.card_fin])
    have he := @hlb (G.degree v) hdc H dec htH hiH
    exact (Nat.add_le_add_right (he.trans heH) _).trans (removed G ht v)
  have hsum_local := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun v _ => hlocal v)
  rw [Finset.sum_add_distrib, sum_neighbor_degrees, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hsum_local
  have hpoint (v : Fin n) : a + b * G.degree v ≤ G.degree v ^ 2 + lb (n - 1 - G.degree v) := by
    have hd := degree_lt G ht hc v
    have hdc := nonneighbors_lt hr G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    exact hstep (G.degree v) (by omega) hdc
  have hsum_pt := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun v _ => hpoint v)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum, G.sum_degrees_eq_twice_card_edges] at hsum_pt
  have hcomm : b * (2 * G.edgeFinset.card) = 2 * b * G.edgeFinset.card := by ring
  omega

/- Extremal edge bounds ladder. -/

lemma e33_3 (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj]
    (_ : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 3) : 1 ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_sub G hc

lemma e33_4 (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (_ : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 3) : 2 ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_sub G hc

lemma e33_5 (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 3) : 5 ≤ G.edgeFinset.card := by
  have hdeg (v : Fin 5) : 2 ≤ G.degree v := by
    have hdc := nonneighbors_lt three_works G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5))) (fun v _ => hdeg v)
  have htot := G.sum_degrees_eq_twice_card_edges
  simp at hsum
  omega

private abbrev lb33 : ℕ → ℕ := (fun m : ℕ => match m with
  | 3 => 1
  | 4 => 2
  | 5 => 5
  | _ => 0)

private lemma lb33_ok : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
    H.CliqueFree 3 → Hᶜ.CliqueFree 3 → lb33 m ≤ H.edgeFinset.card
  | 3, H, _, ht, hc => e33_3 H ht hc
  | 4, H, _, ht, hc => e33_4 H ht hc
  | 5, H, _, ht, hc => e33_5 H ht hc
  | 0, _, _, _, _ | 1, _, _, _, _ | 2, _, _, _, _ | _ + 6, _, _, _, _ => Nat.zero_le _

lemma e34_4 (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (_ : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 4) : 1 ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_sub G hc

lemma e34_5 (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (_ : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 4) : 2 ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_sub G hc

lemma e34_6 (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (_ : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 4) : 3 ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_sub G hc

lemma e34_7 (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 4) : 6 ≤ G.edgeFinset.card := by
  have h := gy_step six_works lb33 (fun _ _ => lb33_ok _) 6 0
    (fun d hd hlt => by interval_cases d <;> first | decide | omega) G ht hc
  omega

lemma e34_8 (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 4) : 10 ≤ G.edgeFinset.card := by
  have h := gy_step six_works lb33 (fun _ _ => lb33_ok _) 7 1
    (fun d hd hlt => by interval_cases d <;> first | decide | omega) G ht hc
  omega

private abbrev lb34 : ℕ → ℕ := (fun m : ℕ => match m with
  | 4 => 1
  | 5 => 2
  | 6 => 3
  | 7 => 6
  | 8 => 10
  | _ => 0)

private lemma lb34_ok : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
    H.CliqueFree 3 → Hᶜ.CliqueFree 4 → lb34 m ≤ H.edgeFinset.card
  | 4, H, _, ht, hc => e34_4 H ht hc
  | 5, H, _, ht, hc => e34_5 H ht hc
  | 6, H, _, ht, hc => e34_6 H ht hc
  | 7, H, _, ht, hc => e34_7 H ht hc
  | 8, H, _, ht, hc => e34_8 H ht hc
  | 0, _, _, _, _ | 1, _, _, _, _ | 2, _, _, _, _ | 3, _, _, _, _ | _ + 9, _, _, _, _ => Nat.zero_le _

lemma e35_9 (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 5) : 7 ≤ G.edgeFinset.card := by
  have h := gy_step nine_works lb34 (fun _ _ => lb34_ok _) 7 0
    (fun d hd hlt => by interval_cases d <;> decide) G ht hc
  omega

lemma e35_10 (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 5) : 10 ≤ G.edgeFinset.card := by
  have h := gy_step nine_works lb34 (fun _ _ => lb34_ok _) 10 0
    (fun d hd hlt => by interval_cases d <;> first | decide | omega) G ht hc
  omega

lemma e35_11 (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 5) : 15 ≤ G.edgeFinset.card := by
  have h := gy_step nine_works lb34 (fun _ _ => lb34_ok _) 12 1
    (fun d hd hlt => by interval_cases d <;> first | decide | omega) G ht hc
  omega

lemma e35_12 (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 5) : 20 ≤ G.edgeFinset.card := by
  have h := gy_step nine_works lb34 (fun _ _ => lb34_ok _) 16 1
    (fun d hd hlt => by interval_cases d <;> first | decide | omega) G ht hc
  omega

lemma e35_13 (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 5) : 26 ≤ G.edgeFinset.card := by
  have hdeg (v : Fin 13) : 4 ≤ G.degree v := by
    have hdc := nonneighbors_lt nine_works G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 13))) (fun v _ => hdeg v)
  have htot := G.sum_degrees_eq_twice_card_edges
  simp at hsum
  omega

private abbrev lb35 : ℕ → ℕ := (fun m : ℕ => match m with
  | 8 => 4
  | 9 => 7
  | 10 => 10
  | 11 => 15
  | 12 => 20
  | 13 => 26
  | _ => 0)

lemma lb35_ok : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
    H.CliqueFree 3 → Hᶜ.CliqueFree 5 → lb35 m ≤ H.edgeFinset.card
  | 8, H, _, _, hc => card_edgeFinset_ge_sub H hc
  | 9, H, _, ht, hc => e35_9 H ht hc
  | 10, H, _, ht, hc => e35_10 H ht hc
  | 11, H, _, ht, hc => e35_11 H ht hc
  | 12, H, _, ht, hc => e35_12 H ht hc
  | 13, H, _, ht, hc => e35_13 H ht hc
  | 0, _, _, _, _ | 1, _, _, _, _ | 2, _, _, _, _ | 3, _, _, _, _ | 4, _, _, _, _
  | 5, _, _, _, _ | 6, _, _, _, _ | 7, _, _, _, _ | _ + 14, _, _, _, _ => Nat.zero_le _

lemma e36_15 (G : SimpleGraph (Fin 15)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) : 25 ≤ G.edgeFinset.card := by
  have h := gy_step fourteen_works lb35 (fun _ _ => lb35_ok _) 21 1
    (fun d hd hlt => by interval_cases d <;> first | decide | omega) G ht hc
  omega

lemma e36_17 (G : SimpleGraph (Fin 17)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) : 38 ≤ G.edgeFinset.card := by
  have h := gy_step fourteen_works lb35 (fun _ _ => lb35_ok _) 24 3
    (fun d hd hlt => by interval_cases d <;> first | decide | omega) G ht hc
  omega


lemma e36_12 (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) : 11 ≤ G.edgeFinset.card := by
  have h := gy_step fourteen_works lb35 (fun _ _ => lb35_ok _) 11 0
    (fun d hd hlt => by interval_cases d <;> decide) G ht hc
  omega

lemma e36_13 (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) : 15 ≤ G.edgeFinset.card := by
  have h := gy_step fourteen_works lb35 (fun _ _ => lb35_ok _) 10 2
    (fun d hd hlt => by interval_cases d <;> decide) G ht hc
  omega

lemma e36_16_31 (G : SimpleGraph (Fin 16)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) : 31 ≤ G.edgeFinset.card := by
  have h := gy_step fourteen_works lb35 (fun _ _ => lb35_ok _) 23 2
    (fun d hd hlt => by interval_cases d <;> first | decide | omega) G ht hc
  omega

lemma e36_14 (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) : 19 ≤ G.edgeFinset.card := by
  have h := gy_step fourteen_works lb35 (fun _ _ => lb35_ok _) 19 0
    (fun d hd hlt => by interval_cases d <;> decide) G ht hc
  omega

end Ramsey39Children

namespace Ramsey39Small

open Ramsey39Children SimpleGraph

theorem child_table {p m : ℕ}
    (h16 : ∀ (K : SimpleGraph (Fin 16)) [DecidableRel K.Adj],
      K.CliqueFree 3 → Kᶜ.CliqueFree 6 → 32 ≤ K.edgeFinset.card)
    (hm : 12 ≤ m) (K : SimpleGraph (Fin m)) [DecidableRel K.Adj]
    (tri : K.CliqueFree 3) (ind : Kᶜ.CliqueFree 6) :
    ([0,0,0,0,0,0,1,2,3,4,5,8,11,15,19,25,if p=22 then 32 else 31,38] : List ℕ).getD m 41 ≤
      K.edgeFinset.card := by
  rcases lt_or_ge m 18 with hsmall | hbig
  · interval_cases m
    · exact e36_12 K tri ind
    · exact e36_13 K tri ind
    · exact e36_14 K tri ind
    · exact e36_15 K tri ind
    · change (if p=22 then 32 else 31) ≤ K.edgeFinset.card
      split
      · exact h16 K tri ind
      · exact e36_16_31 K tri ind
    · exact e36_17 K tri ind
  · rw [List.getD_eq_default _ _ (by simpa using hbig)]
    let H := K.comap (Fin.castLEEmb hbig)
    let emb : H ↪g K := Embedding.comap (Fin.castLEEmb hbig) K
    have ht := CliqueFree.comap emb.isContained tri
    have hi := CliqueFree.comap (Embedding.complEquiv emb).isContained ind
    have avg := RamseyDeficiency.delete_average (n := 17) (e := 38) e36_17 H ht hi
    have larger := Fintype.card_le_of_embedding emb.toCopy.mapEdgeSet
    rw [H.card_edgeSet, K.card_edgeSet] at larger
    omega

end Ramsey39Small


section RamseyFiniteSection
open SimpleGraph Finset
namespace OMA.RamseyFinite

def bits : List Bool → Nat
  | [] => 0
  | b::bs => 2 * bits bs + b.toNat

theorem bits_lt (b : List Bool) : bits b < 2 ^ b.length := by
  induction b with
  | nil => decide
  | cons a l ih => cases a <;> simp [bits, pow_succ] <;> omega

theorem bits_append (a b : List Bool) : bits (a ++ b) = bits a + 2 ^ a.length * bits b := by
  induction a with
  | nil => simp [bits]
  | cons c a ih => simp [bits, ih, pow_succ]; ring

theorem bits_replicate_false (n : Nat) : bits (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bits, ih]

theorem bits_replicate_true (n : Nat) : bits (List.replicate n true) + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bits, pow_succ]; omega

def encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] : List V → List Nat
  | [] => []
  | v::vs => bits (vs.map fun x => decide (G.Adj v x)) :: encode G vs

def shifted : List Nat → List Nat
  | [] => []
  | s::ss => 2 ^ ss.length * s :: shifted ss

def attach (blocks base : List Nat) : List Nat :=
  (2 ^ blocks.length - 1) :: (shifted blocks ++ base)

theorem contacts {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (front base : List V) (hi : ∀ x ∈ front, ∀ y ∈ front, ¬ G.Adj x y) :
    encode G (front ++ base) =
      shifted (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) ++ encode G base := by
  induction front with
  | nil => rfl
  | cons a as ih =>
    have nh (x) (hx : x∈as) := hi a (by simp) x (by simp [hx])
    have nils : as.map (fun x => decide (G.Adj a x)) = List.replicate as.length false := by
      apply List.eq_replicate_iff.mpr
      exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [nh b hb]⟩
    simp [encode, shifted, bits_append, nils, bits_replicate_false,
      ih (fun x hx y hy => hi x (by simp [hx]) y (by simp [hy]))]

theorem root_encoding {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (front base : List V) (hfront : ∀ x∈front, G.Adj r x)
    (hbase : ∀ x∈base, ¬ G.Adj r x) (ht : G.CliqueFree 3) :
    encode G (r::front++base) = attach
      (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) (encode G base) := by
  have hf : front.map (fun x => decide (G.Adj r x)) = List.replicate front.length true := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [hfront b hb]⟩
  have hb : base.map (fun x => decide (G.Adj r x)) = List.replicate base.length false := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [hbase b hb]⟩
  have hi (x) (hx : x ∈ front) (y) (hy : y ∈ front) (h : G.Adj x y) : False :=
    G.isIndepSet_neighborSet_of_triangleFree ht r (hfront x hx) (hfront y hy) h.ne h
  simp [encode, attach, bits_append, hf, hb, bits_replicate_false, contacts G front base hi]
  have := bits_replicate_true front.length
  omega

def mark {V : Type*} [DecidableEq V] (vs : List V) (s : Finset V) : Nat :=
  bits (vs.map fun x => decide (x ∈ s))

theorem bit_form (b : Bool) (n : Nat) : Nat.bit b n = 2 * n + b.toNat := by
  cases b <;> simp [Nat.bit, Nat.two_mul]

theorem and_mask {V : Type*} (vs : List V) (f g : V → Bool) :
    bits (vs.map f) &&& bits (vs.map g) = 0 ↔ ∀ x ∈ vs, f x = true → g x = false := by
  induction vs with
  | nil => simp [bits]
  | cons a l ih =>
    simp only [List.map_cons, bits, ← bit_form, Nat.land_bit, List.forall_mem_cons]
    rw [bit_form]
    cases f a <;> cases g a <;> simp [ih]

def ind0 (p : Nat × Nat) : Nat × Nat := (2*p.1,p.2)
def ind1 (p : Nat × Nat) : Nat × Nat := (2*p.1+1,p.2+1)

def inds : List Nat → List (Nat × Nat)
  | [] => [(0,0)]
  | m::rows =>
    let t := inds rows
    t.map ind0 ++ (t.filter fun p => m &&& p.1 == 0).map ind1

theorem mark_congr {V : Type*} [DecidableEq V] (vs : List V) (s t : Finset V)
    (h : ∀ x∈vs, x∈s ↔ x∈t) : mark vs s = mark vs t := by
  unfold mark
  congr 1
  exact List.map_congr_left (fun x hx => by simp only [h x hx])

theorem inds_sound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hn : vs.Nodup) {p : Nat × Nat} (hp : p ∈ inds (encode G vs)) :
    ∃ S : Finset V, S ⊆ vs.toFinset ∧ Gᶜ.IsClique (S : Set V) ∧ p = (mark vs S,S.card) := by
  induction vs generalizing p with
  | nil =>
    simp [encode,inds] at hp
    exact ⟨∅,by simp,by simp,by simp [hp,mark,bits]⟩
  | cons a l ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [encode,inds,List.mem_append,List.mem_map,List.mem_filter] at hp
    rcases hp with ⟨q,hq,rfl⟩ | ⟨q,⟨hq,hd⟩,rfl⟩
    · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
      have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
      exact ⟨S,by simpa using hS.trans (Finset.subset_insert a _),hI,by simp [ind0,mark,bits,ha]⟩
    · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
      have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
      have hz := (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈S))).mp (beq_iff_eq.mp hd)
      have hi : Gᶜ.IsClique (insert a S : Finset V) := by
        rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem ha]
        refine ⟨hI,fun x hx => ⟨?_,?_⟩⟩
        · exact fun e => ha (e ▸ hx)
        · intro adj
          have := hz x (List.mem_toFinset.mp (hS hx)) (by simpa using adj)
          exact (of_decide_eq_false this) hx
      have hm := mark_congr l (insert a S) S (by intro x hx; simp [show x ≠ a from fun e => hn'.1 (e ▸ hx)])
      refine ⟨insert a S, by simpa using Finset.insert_subset_insert a hS, hi, ?_⟩
      simp [ind1,mark,bits,Finset.card_insert_of_notMem ha] at hm ⊢
      omega

theorem inds_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hn : vs.Nodup) (S : Finset V) (hS : S ⊆ vs.toFinset) (hI : Gᶜ.IsClique (S : Set V)) :
    (mark vs S,S.card) ∈ inds (encode G vs) := by
  induction vs generalizing S with
  | nil =>
    have e : S=∅ := Finset.subset_empty.mp (by simpa using hS)
    simp [e,encode,inds,mark,bits]
  | cons a l ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [encode,inds,List.mem_append,List.mem_map,List.mem_filter]
    by_cases ha : a ∈ S
    · let T := S.erase a
      have hT : T ⊆ l.toFinset := by
        intro x hx
        have m := Finset.mem_erase.mp hx
        have h := List.mem_cons.mp (List.mem_toFinset.mp (hS m.2))
        exact List.mem_toFinset.mpr (h.resolve_left m.1)
      have hI' := hI.subset (show (T : Set V) ⊆ (S : Set V) from Finset.erase_subset ..)
      have hmark := mark_congr l S T (by intro x hx; simp [T,show x≠a from fun e => hn'.1 (e ▸ hx)])
      have hcard : T.card + 1 = S.card := Finset.card_erase_add_one ha
      right
      refine ⟨(mark l T,T.card),⟨ih hn'.2 T hT hI', ?_⟩,?_⟩
      · apply beq_iff_eq.mpr
        apply (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈T))).mpr
        intro x _ hx
        apply decide_eq_false
        intro hm
        have hmem := Finset.mem_erase.mp hm
        exact (hI ha hmem.2 hmem.1.symm).2 (of_decide_eq_true hx)
      · simp [ind1,mark,bits,ha,hcard] at hmark ⊢
        omega
    · have hT : S ⊆ l.toFinset := by
        intro x hx
        have h := List.mem_cons.mp (List.mem_toFinset.mp (hS hx))
        exact List.mem_toFinset.mpr (h.resolve_left (fun e => ha (e ▸ hx)))
      exact Or.inl ⟨_,ih hn'.2 S hT hI,by simp [ind0,mark,bits,ha]⟩


def countBits : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,x => (x%2) + countBits n (x/2)

def bump (m : Nat) : List Nat → List Nat
  | [] => []
  | x::xs => (x+m%2)::bump (m/2) xs

def degrees : List Nat → List Nat
  | [] => []
  | m::ms => countBits ms.length m :: bump m (degrees ms)

def sizeAt {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) (x : V) :=
  (vs.filter fun y => decide (G.Adj x y)).length

theorem half_step (x : Nat) : (2*x+1)/2=x := by omega

theorem count_map {V : Type*} (vs : List V) (f : V → Bool) :
    countBits vs.length (bits (vs.map f)) = (vs.filter f).length := by
  induction vs with
  | nil => rfl
  | cons a l ih =>
    cases ha : f a <;> simp [countBits,bits,ha,ih,half_step]
    omega

theorem bump_map {V : Type*} (vs : List V) (f : V → Bool) (d : V → Nat) :
    bump (bits (vs.map f)) (vs.map d) = vs.map (fun x => d x + (f x).toNat) := by
  induction vs with
  | nil => rfl
  | cons a l ih => cases ha : f a <;> simp [bump,bits,ha,ih,half_step]

theorem encode_length {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    (encode G vs).length=vs.length := by induction vs with | nil => rfl | cons a as ih => simp [encode,ih]

theorem degrees_encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    degrees (encode G vs) = vs.map (sizeAt G vs) := by
  induction vs with
  | nil => rfl
  | cons a l ih =>
    simp only [encode,degrees,encode_length,count_map,ih,bump_map,List.map_cons,List.cons.injEq]
    refine ⟨by simp [sizeAt], List.map_congr_left ?_⟩
    intro x _
    by_cases h : G.Adj a x <;> simp [sizeAt,h,G.adj_comm x a]

theorem sizeAt_finset {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {vs : List V} (hn : vs.Nodup) (x : V) :
    sizeAt G vs x = (vs.toFinset.filter (G.Adj x)).card := by
  have h := List.toFinset_filter vs (fun y => decide (G.Adj x y))
  simp only [decide_eq_true_eq] at h
  rw [← h, List.toFinset_card_of_nodup (hn.filter _)]
  rfl


def Small {V : Type*} (G : SimpleGraph V) (A : Finset V) (k : Nat) :=
  ∀ I ⊆ A, Gᶜ.IsClique (I : Set V) → I.card < k

theorem row_mark {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (base : List V) (x : V) :
    bits (base.map fun y => decide (G.Adj x y)) = mark base (base.toFinset.filter (G.Adj x)) := by
  unfold mark
  congr 1
  exact List.map_congr_left (fun y hy => by simp [hy])

theorem neighbors_small {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (A : Finset V) (x : V) :
    Gᶜ.IsClique ((A.filter (G.Adj x) : Finset V) : Set V) := by
  rw [G.isClique_compl]
  intro y hy z hz hn
  exact G.isIndepSet_neighborSet_of_triangleFree ht x (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2 hn

theorem degrees_bound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (A : Finset V) (k : Nat) (hs : Small G A k)
    (l : List V) (hn : l.Nodup) (hsub : l.toFinset ⊆ A) :
    (degrees (encode G l)).all (· < k) = true := by
  rw [degrees_encode, List.all_eq_true]
  intro y hy
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hy
  simp only [decide_eq_true_eq, sizeAt_finset G hn]
  exact hs _ ((Finset.filter_subset _ _).trans hsub) (neighbors_small G ht _ x)

def okContacts (k : Nat) (isets : List (Nat × Nat)) (cs : List Nat) : Bool :=
  isets.all fun p => p.2 + (cs.filter fun v => v &&& p.1 == 0).length < k

theorem ok_contacts {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : Nat) (hs : Small G A k) (front base : List V)
    (hn : (front++base).Nodup) (hsub : (front++base).toFinset ⊆ A)
    (hi : Gᶜ.IsClique (front.toFinset : Set V)) :
    okContacts k (inds (encode G base)) (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) := by
  rw [okContacts,List.all_eq_true]
  intro q hq
  obtain ⟨hh,hb,hd⟩ := List.nodup_append.mp hn
  obtain ⟨S,hS,hI,rfl⟩ := inds_sound G base hb hq
  let pred (v : V) : Bool := bits (base.map fun y => decide (G.Adj v y)) &&& mark base S == 0
  let F := front.filter pred
  have hF (x) (hx : x∈F) : x∈front := (List.mem_filter.mp hx).1
  have sep (x) (hx : x∈F) (y) (hy : y∈S) : Gᶜ.Adj x y := by
    have hx' := List.mem_filter.mp hx
    have hy' := List.mem_toFinset.mp (hS hy)
    have neq : x ≠ y := hd x hx'.1 y hy'
    exact ⟨neq,fun ha => by
      have e := (and_mask base (fun z => decide (G.Adj x z)) (fun z => decide (z ∈ S))).mp
        (beq_iff_eq.mp hx'.2) y hy' (by simpa using ha)
      exact of_decide_eq_false e hy⟩
  have sub : F.toFinset ∪ S ⊆ A := by
    apply Finset.union_subset
    · exact fun x hx => hsub (by simp [hF x (List.mem_toFinset.mp hx)])
    · exact fun x hx => hsub (by simp [List.mem_toFinset.mp (hS hx)])
  have together : Gᶜ.IsClique ((F.toFinset ∪ S : Finset V) : Set V) := by
    rw [Finset.coe_union, SimpleGraph.IsClique, Set.pairwise_union]
    refine ⟨hi.subset ?_,hI,?_⟩
    · exact fun x hx => List.mem_toFinset.mpr (hF x (List.mem_toFinset.mp hx))
    · intro x hx y hy _
      exact ⟨sep x (List.mem_toFinset.mp hx) y hy,(sep x (List.mem_toFinset.mp hx) y hy).symm⟩
  have dis : Disjoint F.toFinset S := Finset.disjoint_left.mpr fun x hx hy =>
    (sep x (List.mem_toFinset.mp hx) x hy).ne rfl
  have w := hs _ sub together
  rw [Finset.card_union_of_disjoint dis,List.toFinset_card_of_nodup (hh.filter _)] at w
  simp only [decide_eq_true_eq,List.filter_map,List.length_map]
  change S.card + F.length < k
  simpa only [F, Nat.add_comm S.card] using w


theorem bit_and {α : Type*} (l : List α) (f g : α → Bool) :
    bits (l.map f) &&& bits (l.map g) = bits (l.map fun x => f x && g x) := by
  induction l with
  | nil => simp [bits]
  | cons a l ih => simp only [List.map_cons,bits,← bit_form,Nat.land_bit,ih]

theorem bit_or {α : Type*} (l : List α) (f g : α → Bool) :
    bits (l.map f) ||| bits (l.map g) = bits (l.map fun x => f x || g x) := by
  induction l with
  | nil => simp [bits]
  | cons a l ih => simp only [List.map_cons,bits,← bit_form,Nat.lor_bit,ih]

def compat (I : List (Nat × Nat)) (a : Nat) := bits (I.map fun p => a &&& p.1 == 0)
def universal (I : List (Nat × Nat)) := bits (I.map fun _=>true)
def threshold (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (j : Nat) :=
  bits (I.map fun p => decide (k≤p.2 + (acc.filter fun a => a &&& p.1 == 0).length+j))

theorem saturated (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (j : Nat) (h : k≤j) :
    threshold k I acc j=universal I := by
  unfold threshold universal
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [decide_eq_true_eq]; omega

theorem threshold_cons (k : Nat) (I : List (Nat × Nat)) (a : Nat) (acc : List Nat) (j : Nat) :
    threshold k I (a::acc) j = threshold k I acc j ||| (compat I a &&& threshold k I acc (j+1)) := by
  unfold threshold compat
  rw [bit_and,bit_or]
  congr 1
  apply List.map_congr_left
  intro p _
  apply Bool.eq_iff_iff.mpr
  by_cases e : a &&& p.1=0 <;> simp [e]
  omega

def cells (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,j => threshold k I acc j :: cells k I acc n (j+1)

def tick (u m : Nat) : List Nat → List Nat
  | [] => []
  | a::as => (a ||| (m &&& as.headD u)) :: tick u m as

theorem tick_cells (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (a n j : Nat) (h : k ≤ j+n) :
    tick (universal I) (compat I a) (cells k I acc n j) = cells k I (a::acc) n j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [cells,tick,List.cons.injEq]
    refine ⟨?_,ih (j+1) (by omega)⟩
    rw [threshold_cons]
    cases n with
    | zero => simp [cells,saturated k I acc (j+1) (by omega)]
    | succ n => rfl

theorem can_add (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (a : Nat)
    (h : okContacts k I (a::acc)) : compat I a &&& threshold k I acc 1=0 := by
  apply (and_mask I _ _).mpr
  intro p hp e
  have b := List.all_eq_true.mp h p hp
  simp only [List.filter_cons,e,if_true,List.length_cons,decide_eq_true_eq] at b
  apply decide_eq_false
  omega

def traverse (opts : List (Nat × Nat)) (u : Nat) (ending : List (Nat × Nat) → Bool) :
    Nat → Nat → List (Nat × Nat) → List Nat → List (List (Nat × Nat))
  | 0,_,acc,_ => if ending acc then [acc] else []
  | fuel+1,lo,acc,st => opts.flatMap fun a =>
    if lo ≤ a.1 && a.2 &&& st.headD u == 0 then
      traverse opts u ending fuel a.1 (a::acc) (tick u a.2 st) else []

theorem traverse_complete (opts : List (Nat × Nat)) (I : List (Nat × Nat)) (k : Nat) (hk : 0<k)
    (ending : List (Nat × Nat) → Bool) (next acc : List (Nat × Nat)) (lo : Nat)
    (hc : ∀ a∈next,a∈opts) (vals : ∀ a∈next,a.2=compat I a.1)
    (hl : ∀ a∈next,lo≤a.1) (hs : next.Pairwise (fun a b => a.1 ≤ b.1))
    (hg : ∀ u w,next=u++w → okContacts k I ((u.reverse++acc).map Prod.fst)) (hf : ending (next.reverse++acc)) :
    next.reverse++acc ∈ traverse opts (universal I) ending next.length lo acc (cells k I (acc.map Prod.fst) k 1) := by
  induction next generalizing acc lo with
  | nil => simpa [traverse,hf] using hf
  | cons a rest ih =>
    simp only [List.length_cons,traverse,List.mem_flatMap]
    refine ⟨a,hc a (by simp),?_⟩
    have hd : (cells k I (acc.map Prod.fst) k 1).headD (universal I)=threshold k I (acc.map Prod.fst) 1 := by
      cases k with | zero => omega | succ k => rfl
    have an := vals a (by simp)
    have allow := can_add k I (acc.map Prod.fst) a.1 (by simpa using hg [a] rest rfl)
    simp only [hl a (by simp),decide_true,Bool.true_and,an,hd,allow,beq_self_eq_true,if_true,tick_cells k I (acc.map Prod.fst) a.1 k 1 (by omega)]
    simpa [List.append_assoc] using ih (a::acc) a.1 (fun x hx => hc x (by simp [hx]))
      (fun x hx => vals x (by simp [hx])) (List.pairwise_cons.mp hs).1 (List.pairwise_cons.mp hs).2
      (by intro u w h; simpa [List.append_assoc] using hg (a::u) w (by simp [h]))
      (by simpa [List.append_assoc] using hf)


def contactsOf {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (base front : List V) :=
  front.map fun x => bits (base.map fun y => decide (G.Adj x y))

def usable (k d : Nat) (base : List Nat) : List Nat :=
  ((inds base).filter fun p => d ≤ p.2+1 && p.2+1 < k).map Prod.fst

def guardRows (k : Nat) (base : List Nat) (isets : List (Nat × Nat)) (cs : List Nat) :=
  okContacts k isets cs && (degrees (shifted cs ++ base)).all (·<k)

def tagged (k d : Nat) (base : List Nat) :=
  (usable k d base).map fun x => (x,compat (inds base) x)

def assemble (_k d : Nat) (base : List Nat) (opts : List (Nat × Nat)) (bits0 : Nat) (lims : List Nat) :=
  let ending := fun cs : List (Nat × Nat) => (degrees (attach (cs.reverse.map Prod.fst) base)).all (d≤·)
  (traverse opts bits0 ending d 0 [] lims).map (fun cs => attach (cs.reverse.map Prod.fst) base)

def grow (k d : Nat) (base : List Nat) : List (List Nat) :=
  assemble k d base (tagged k d base) (universal (inds base)) (cells k (inds base) [] k 1)

theorem grow_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k d : Nat) (ht : G.CliqueFree 3) (hs : Small G A k)
    (r : V) (front base : List V) (hn : (r::front++base).Nodup)
    (hall : (r::front++base).toFinset=A) (hd : front.length=d)
    (ha : ∀ x∈front,G.Adj r x) (hb : ∀ x∈base,¬G.Adj r x)
    (hcount : ∀ x∈front,d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k)
    (hmin : ∀ x∈A,d≤(A.filter (G.Adj x)).card)
    (horder : (contactsOf G base front).Pairwise (·≤·)) :
    encode G (r::front++base) ∈ grow k d (encode G base) := by
  let cs := contactsOf G base front
  have split := root_encoding G r front base ha hb ht
  change encode G (r::front++base) = attach cs (encode G base) at split
  have hbnd := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have hc (s) (mem : s ∈ cs) : s ∈ usable k d (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    let S := base.toFinset.filter (G.Adj x)
    have row := inds_complete G base hbnd S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have m := hcount x hx
    rw [sizeAt_finset G hbnd] at m
    change bits (base.map fun y => decide (G.Adj x y)) ∈ _
    rw [row_mark]
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨row,by simpa [S] using m⟩,rfl⟩
  have guard_ (u w : List Nat) (h : cs=u++w) : guardRows k (encode G base) (inds (encode G base)) u := by
    let sl := front.take u.length
    have hu : contactsOf G base sl = u := by
      change (front.take u.length).map _=u
      rw [List.map_take, show front.map _=u++w from h, List.take_left]
    have ssub := (List.take_sublist u.length front).append (List.Sublist.refl base)
    have nodup : (sl++base).Nodup := (List.nodup_cons.mp hn).2.sublist ssub
    have sub : (sl++base).toFinset ⊆ A := by
      intro x hx
      rw [← hall]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (ssub.subset (List.mem_toFinset.mp hx)))
    have ha' (x) (hx : x∈sl) := ha x ((List.take_sublist u.length front).subset hx)
    have indep : Gᶜ.IsClique (sl.toFinset : Set V) := by
      rw [G.isClique_compl]
      intro x hx y hy hxy
      exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x (List.mem_toFinset.mp hx)) (ha' y (List.mem_toFinset.mp hy)) hxy
    have em := contacts G sl base (by intro x hx y hy adj; exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x hx) (ha' y hy) adj.ne adj)
    change encode G (sl++base)=shifted (contactsOf G base sl)++encode G base at em
    rw [← hu]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ok_contacts G A k hs sl base nodup sub indep,?_⟩
    rw [← em]
    exact degrees_bound G ht A k hs _ nodup sub
  have final_ : (degrees (attach cs (encode G base))).all (d≤·) = true := by
    rw [← split,degrees_encode,List.all_eq_true]
    intro n hh
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hh
    simpa only [decide_eq_true_eq,sizeAt_finset G hn,hall] using hmin x (hall ▸ List.mem_toFinset.mpr hx)
  have csl : cs.length=d := by simp [cs,contactsOf,hd]
  let base' := encode G base
  let tag (x : Nat) := (x,compat (inds base') x)
  let ts := cs.map tag
  have ret (ss : List Nat) : (ss.map tag).map Prod.fst = ss := by simp [tag,Function.comp_def]
  have tg (a) (ma : a∈ts) : a ∈ tagged k d base' := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ma
    exact List.mem_map.mpr ⟨x,hc x hx,rfl⟩
  have gg (u w : List (Nat × Nat)) (h : ts=u++w) : okContacts k (inds base') (u.reverse.map Prod.fst) := by
    let sl := cs.take u.length
    have split_ : cs=sl++cs.drop u.length := (List.take_append_drop u.length cs).symm
    have hu : sl.map tag=u := by
      change (cs.take u.length).map tag=u
      rw [List.map_take,show cs.map tag=u++w from h,List.take_left]
    have gh := Bool.and_eq_true_iff.mp (guard_ sl (cs.drop u.length) split_)
    rw [← hu,List.map_reverse,ret]
    simpa [okContacts] using gh.1
  have tslen : ts.length=d := by simp [ts,csl]
  have tsord : ts.Pairwise (fun a b => a.1 ≤ b.1) := List.pairwise_map.mpr horder
  rw [split]
  apply List.mem_map.mpr
  refine ⟨ts.reverse,?_,by simp [ts,ret]⟩
  have hk : 0<k := hs ∅ (by simp) (by simp)
  simpa only [List.append_nil,tslen,List.map_nil] using traverse_complete (tagged k d base') (inds base') k hk
    (fun u => (degrees (attach (u.reverse.map Prod.fst) base')).all (d≤·)) ts [] 0 tg
    (by intro a ha; obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha; rfl) (by simp) tsord
    (by simpa using gg) (by simpa only [List.append_nil,List.reverse_reverse,ts,ret,base'] using final_)

def levels (norm : List Nat → List Nat) : Nat → Nat → Nat → List (List Nat)
  | 0,_,_ => []
  | k+1,n,cap => if n=0 then [[]] else
    ((List.range (min cap (min k (n-1)) + 1)).flatMap fun d =>
      (levels norm k (n-1-d) (k-1)).flatMap fun base => (grow (k+1) d base).map norm).eraseDups

theorem sorted_neigh {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : Finset V) (base : List V) :
    ∃ l : List V, l.Nodup ∧ l.toFinset=N ∧ (contactsOf G base l).Pairwise (·≤·) := by
  let key (x : V) := bits (base.map fun y => decide (G.Adj x y))
  let ord (a b : V) := decide (key a ≤ key b)
  let l := N.toList.mergeSort ord
  have h := List.mergeSort_perm N.toList ord
  refine ⟨l,h.nodup_iff.mpr N.nodup_toList,?_,?_⟩
  · ext x
    simp [l]
  · have htr (a b c) : ord a b → ord b c → ord a c := by simp only [ord,decide_eq_true_eq]; omega
    have htot (a b) : ord a b || ord b a := by simp [ord,le_total]
    have sort_ := List.pairwise_mergeSort htr htot N.toList
    apply List.pairwise_map.mpr
    simpa only [ord,decide_eq_true_eq] using sort_

theorem levels_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (norm : List Nat → List Nat)
    (hnorm : ∀ l : List V, ∃ l' : List V, l'.Perm l ∧ encode G l'=norm (encode G l))
    (k : Nat) (A : Finset V) (cap : Nat) (hs : Small G A k)
    (hu : A.Nonempty → ∃ x∈A,(A.filter (G.Adj x)).card ≤ cap) :
    ∃ vs : List V, vs.Nodup ∧ vs.toFinset=A ∧ encode G vs ∈ levels norm k A.card cap := by
  induction k generalizing A cap with
  | zero => have h := hs ∅ (by simp) (by simp); simp at h
  | succ k ih =>
    by_cases empty : A=∅
    · subst A; exact ⟨[],by simp,by simp,by simp [encode,levels]⟩
    have non := Finset.nonempty_iff_ne_empty.mpr empty
    obtain ⟨r,hr,hmin⟩ := A.exists_min_image (fun x => (A.filter (G.Adj x)).card) non
    let N := A.filter (G.Adj r)
    let B := A \ insert r N
    let d := N.card
    have hNr : r∉N := by simp [N]
    have hNA : N⊆A := Finset.filter_subset ..
    have hBA : B⊆A := Finset.sdiff_subset
    have hu' : d≤cap := by obtain ⟨x,hx,hh⟩ := hu non; exact (hmin x hx).trans hh
    have hdk : d≤k := Nat.le_of_lt_succ (hs N hNA (neighbors_small G ht A r))
    have hBcard : B.card + d + 1 = A.card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hr hNA)
      rw [Finset.card_insert_of_notMem hNr] at hh
      omega
    have rB : r∉B := by simp [B]
    have hbase (x) (hx : x∈B) : ¬G.Adj r x := by
      have h := Finset.mem_sdiff.mp hx
      exact fun ha => h.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h.1,ha⟩))
    have noK : Small G B k := by
      intro S hS hI
      have rn : r∉S := fun h => rB (hS h)
      have indep : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
        exact ⟨hI,fun x hx => ⟨fun e => rn (e ▸ hx),hbase x (hS hx)⟩⟩
      have hh := hs (insert r S) (Finset.insert_subset hr (hS.trans hBA)) indep
      rw [Finset.card_insert_of_notMem rn] at hh
      omega
    obtain ⟨base,hbn,hb,cls⟩ := ih B (k-1) noK (by
      rintro ⟨x,hx⟩
      have mm := noK (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
      exact ⟨x,hx,by omega⟩)
    obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
    have ha (x) (hx : x∈front) : G.Adj r x := (Finset.mem_filter.mp (hf ▸ List.mem_toFinset.mpr hx)).2
    have hnot (x) (hx : x∈base) := hbase x (hb ▸ List.mem_toFinset.mpr hx)
    have dl : front.length=d := by rw [← List.toFinset_card_of_nodup hfn,hf]
    have nodup : (r::front++base).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · change r ∉ front++base
        rw [List.mem_append,not_or]
        exact ⟨fun h => hNr (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
      · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
    have cover : (r::front++base).toFinset=A := by
      ext x
      simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,Finset.mem_insert,Finset.mem_union,Finset.mem_sdiff]
      have h1 : x=r → x∈A := fun h => h ▸ hr
      have h2 : x∈N → x∈A := fun h => hNA h
      grind
    have hcount (x) (hx : x∈front) : d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k+1 := by
      have xN : x∈N := hf ▸ List.mem_toFinset.mpr hx
      have adj := ha x hx
      have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_sdiff,B]
        constructor
        · rintro ⟨yA,xy⟩
          by_cases yr : y=r
          · exact Or.inl yr
          · exact Or.inr ⟨⟨yA,not_or.mpr ⟨yr,fun yN => G.isIndepSet_neighborSet_of_triangleFree ht r adj (Finset.mem_filter.mp yN).2 xy.ne xy⟩⟩,xy⟩
        · rintro (rfl|⟨⟨yA,_⟩,xy⟩)
          · exact ⟨hr,adj.symm⟩
          · exact ⟨yA,xy⟩
      have mm := hmin x (hNA xN)
      have mx := hs (A.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht A x)
      have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
      rw [eq,Finset.card_insert_of_notMem rn] at mm mx
      rw [sizeAt_finset G hbn,hb]
      exact ⟨mm,mx⟩
    have grown := grow_complete G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    obtain ⟨l,hperm,heq⟩ := hnorm (r::front++base)
    refine ⟨l,hperm.nodup_iff.mpr nodup,?_,?_⟩
    · rw [← cover]
      ext x
      exact List.mem_toFinset.trans (hperm.mem_iff.trans List.mem_toFinset.symm)
    · rw [heq,levels,if_neg (Finset.card_ne_zero.mpr non)]
      apply List.mem_eraseDups.mpr
      apply List.mem_flatMap.mpr
      refine ⟨d,List.mem_range.mpr (by omega),List.mem_flatMap.mpr ⟨encode G base,?_,List.mem_map.mpr ⟨_,grown,rfl⟩⟩⟩
      simpa only [show A.card-1-d=B.card by omega] using cls


def swapAt {α : Type*} : Nat → List α → List α
  | 0,x::y::xs => y::x::xs
  | i+1,x::xs => x::swapAt i xs
  | _,l => l

theorem swap_perm {α : Type*} (i : Nat) (l : List α) : (swapAt i l).Perm l := by
  induction i generalizing l with
  | zero => cases l with | nil => rfl | cons a l => cases l with | nil => rfl | cons b l => exact List.Perm.swap a b l
  | succ i ih => cases l with | nil => rfl | cons a l => exact List.Perm.cons a (ih l)

def exchange : Nat → Nat → Nat
  | 0,x => 4*(x/4)+2*(x%2)+((x/2)%2)
  | i+1,x => 2*exchange i (x/2)+x%2

theorem bits_swap (i : Nat) (l : List Bool) (h : i+2≤l.length) :
    bits (swapAt i l)=exchange i (bits l) := by
  induction i generalizing l with
  | zero =>
    obtain ⟨a,b,l,rfl⟩ : ∃ a b t,l=a::b::t := by cases l with | nil => simp at h | cons a l => cases l with | nil => simp at h | cons b t => exact ⟨_,_,_,rfl⟩
    cases a <;> cases b <;> simp [swapAt,bits,exchange] <;> omega
  | succ i ih =>
    cases l with
    | nil => simp at h
    | cons a t =>
      have e := ih t (by simp at h; omega)
      cases a <;> simp [swapAt,bits,exchange,half_step,e]

theorem swap_map {α β : Type*} (f : α→β) (i : Nat) (l : List α) :
    (swapAt i l).map f=swapAt i (l.map f) := by
  induction i generalizing l with
  | zero => cases l with | nil => rfl | cons a l => cases l <;> rfl
  | succ i ih => cases l with | nil => rfl | cons a l => simp [swapAt,ih]

def swapCode : Nat → List Nat → List Nat
  | 0,p::q::rs => (p%2+2*q)::(p/2)::rs
  | i+1,p::rs => exchange i p :: swapCode i rs
  | _,l => l

theorem swap_encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Nat) (l : List V) (h : i+2≤l.length) : encode G (swapAt i l) = swapCode i (encode G l) := by
  induction i generalizing l with
  | zero =>
    obtain ⟨a,b,t,rfl⟩ : ∃ a b t,l=a::b::t := by cases l with | nil => simp at h | cons a l => cases l with | nil => simp at h | cons b t => exact ⟨_,_,_,rfl⟩
    by_cases adj : G.Adj a b <;> simp [swapAt,swapCode,encode,bits,adj,G.adj_comm b a,Nat.add_comm]
    omega
  | succ i ih =>
    cases l with
    | nil => simp at h
    | cons a t =>
      have hi : i+2≤t.length := by simp at h; omega
      simp only [swapAt,encode,swap_map,swapCode,List.cons.injEq]
      exact ⟨bits_swap i _ (by simpa using hi),ih t hi⟩

def relabel (swaps rows : List Nat) :=
  swaps.foldl (fun l i => if i+2≤l.length then swapCode i l else l) rows

theorem relabel_real {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (swaps : List Nat) (l : List V) : ∃ l', l'.Perm l ∧ encode G l'=relabel swaps (encode G l) := by
  induction swaps generalizing l with
  | nil => exact ⟨l,.refl _,rfl⟩
  | cons i is ih =>
    by_cases hi : i+2≤l.length
    · obtain ⟨t,ht,he⟩ := ih (swapAt i l)
      exact ⟨t,ht.trans (swap_perm ..),by simpa [relabel,encode_length,hi,swap_encode G i l hi] using he⟩
    · simpa [relabel,encode_length,hi] using ih l


def renumber : List Nat → List Nat
  | [1,2,1,0] => [2]
  | [1,2,3,2,2,1,0] => [2,4]
  | [1,4,3,2,2,1,0] => [3,2,5,4]
  | [1,8,3,2,2,1,0] => [4,3,2,3,5,4]
  | [1,9,3,2,2,1,0] => [2,4]
  | [1,12,3,2,2,1,0] => [5,4,3,2,4,3,5,4]
  | [1,16,3,2,2,1,0] => [5,4,3,2,4,3,5,4]
  | [1,17,3,2,2,1,0] => [3,2,5,4]
  | [1,18,3,2,2,1,0] => [4,3,2,3,5,4]
  | [3,2,2,3,2,1,0] => [5,4,3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,3,4]
  | [3,2,4,3,2,1,0] => [5,4,3,2,1,0,4,3,2,1,5,4,3,2,5,4,3,4]
  | [3,2,6,3,2,1,0] => [5,4,3,2,1,0,4,3,2,1,5,4,3,2,4,3]
  | [3,2,10,1,1,1,0] => [4,3,2,1,0,5,4,3,2,1,5,4,3,2,4,3]
  | [3,4,8,3,2,1,0] => [4,3,2,1,0,3,2,1,5,4,3,2,5,4,3,4]
  | [3,4,9,1,1,1,0] => [2,1,0,2,1,3,2,5]
  | [3,4,9,3,2,1,0] => [4,3,2,1,0,3,2,1,5,4,3,2,4,3]
  | [3,4,9,3,2,2,1,0] => [3,5]
  | [3,8,8,3,2,1,0] => [3,2,1,0,3,2,1,5,4,3,2,5,4,3,4]
  | [3,8,9,1,1,1,0] => [5,4,3,2,1,0,2,1,5,4,3,2]
  | [3,8,9,3,2,1,0] => [3,2,1,0,3,2,1,5,4,3,2,4,3]
  | [3,8,17,3,2,2,1,0] => [4,3,6,5]
  | [3,10,8,1,1,1,0] => [3,2,1,0,3,2,1,4,3,2,3]
  | [3,10,10,1,1,1,0] => [2,1,0,3,2,1,2,4,3,5,4,5]
  | [3,12,8,3,2,1,0] => [2,1,0,3,2,1,4,3,2,3]
  | [3,12,9,1,0,1,0] => [1,5]
  | [3,12,17,3,2,2,1,0] => [4,6]
  | [3,16,9,1,1,1,0] => [0,5,4,3,2]
  | [3,16,18,3,2,2,1,0] => [5,4,3,4,6,5]
  | [3,18,10,1,1,1,0] => [1,5,4,3,5,4,5]
  | [3,18,18,3,2,2,1,0] => [3,5,4,6]
  | [3,24,16,3,2,2,1,0] => [1,6,5,4,3,5,4,6,5]
  | [3,24,17,3,2,2,1,0] => [6,5,4,3,5,4,6,5]
  | [3,24,18,3,2,2,1,0] => [6,5,4,3,6,5,4,6,5,6]
  | [7,24,66,137,3,12,9,3,2,2,1,0] => [0,4,3,2,5,4,3,5,4,8,7,10,9]
  | [7,24,130,145,3,12,9,3,2,2,1,0] => [0,5,4,3,2,5,4,3,5,4,9,8,7,8,10,9]
  | [7,24,146,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,24,194,129,3,2,6,3,2,2,1,0] => [2,8,10]
  | [7,24,194,129,3,12,9,3,2,2,1,0] => [0,5,4,3,2,5,4,3,5,4,5,10,9,8,7,9,8,10,9]
  | [7,24,194,137,3,2,6,3,2,2,1,0] => [2,8,10]
  | [7,24,194,137,3,12,9,3,2,2,1,0] => [7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,7,6,8,7,9,8,10]
  | [7,24,194,145,3,12,9,3,2,2,1,0] => [6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,8,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,7,6,8,7,9,8,10]
  | [7,36,132,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,36,140,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,36,196,130,3,2,6,3,2,2,1,0] => [2,4,6,8,10]
  | [7,36,196,134,3,2,6,3,2,2,1,0] => [2,4,6,8,10]
  | [7,36,196,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,260,140,144,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,260,140,145,3,2,6,3,2,2,1,0] => [4,3,2,1,0,6,5,4,3,2,1,3,2,5,4,3,6,5,4,8,7,6,5,8,7,6,10,9,8,7,9,8,10,9]
  | [7,260,140,146,3,2,6,3,2,2,1,0] => [3,2,1,0,1,4,3,2,5,4,3,4,9,8,7,6,8,10,9]
  | [7,260,268,145,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,260,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,264,146,144,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,264,146,145,3,2,6,3,2,2,1,0] => [4,3,2,1,0,1,4,3,2,6,5,4,3,4,9,8,7,6,8,10,9]
  | [7,264,146,146,3,2,6,3,2,2,1,0] => [3,2,1,0,5,4,3,2,1,3,2,5,4,3,6,5,4,8,7,6,5,8,7,6,10,9,8,7,9,8,10,9]
  | [7,264,274,146,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,280,146,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,280,146,146,3,2,6,3,2,2,1,0] => [1,4,6]
  | [7,280,194,129,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,280,194,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,280,194,145,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,280,194,146,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,280,274,146,3,2,6,3,2,2,1,0] => [1,2,4,6,8,10]
  | [7,292,196,130,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,292,196,134,3,2,6,3,2,2,1,0] => [4,6]
  | [7,292,196,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,292,196,145,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,292,196,146,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,292,268,145,3,2,6,3,2,2,1,0] => [1,2,8,10]
  | [7,292,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,384,258,134,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,258,134,3,12,9,3,2,2,1,0] => [0,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,8]
  | [7,384,260,137,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,384,260,145,3,12,9,3,2,2,1,0] => [0,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,7,10,9,8,10]
  | [7,384,264,137,3,12,9,3,2,2,1,0] => [0,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,8,7,9,8,10]
  | [7,384,268,137,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,268,137,3,12,9,3,2,2,1,0] => [7,6,5,4,3,2,1,0,5,4,3,2,1,7,6,5,4,3,2,9,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,8,7,10,9,8,10]
  | [7,384,268,145,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,268,145,3,12,9,3,2,2,1,0] => [6,5,4,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,8,7,10,9,8,10]
  | [7,384,274,146,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,384,274,148,3,12,9,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,384,276,145,3,12,9,3,2,2,1,0] => [10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,388,258,134,3,2,6,3,2,2,1,0] => [4,3,2,1,0,6,5,4,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,9,8,7,8,10,9]
  | [7,388,260,137,3,2,6,3,2,2,1,0] => [4,3,2,1,0,2,1,4,3,2,6,5,4,3,5,4,10,9,8,7,6,9,8,10,9]
  | [7,388,260,145,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,388,264,137,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,388,268,137,3,2,6,3,2,2,1,0] => [1,2,8,10]
  | [7,388,268,145,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,388,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,388,274,146,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,388,274,148,3,12,9,3,2,2,1,0] => [2,1,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,388,276,145,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,392,258,134,3,2,6,3,2,2,1,0] => [3,2,1,0,2,1,4,3,2,5,4,3,5,4,10,9,8,7,6,9,8,10,9]
  | [7,392,260,137,3,2,6,3,2,2,1,0] => [3,2,1,0,5,4,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,9,8,7,8,10,9]
  | [7,392,268,137,3,2,6,3,2,2,1,0] => [2,1,2,4,6,8,10]
  | [7,392,268,145,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,392,274,146,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [15,304,164,162,82,3,2,9,1,1,1,0] => [2,1,0,10,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,6,5,4,3,6,5,7,6,8,7,9,10]
  | [15,304,196,138,73,1,6,3,2,2,1,0] => [2,1,3,2,8,10]
  | [15,584,392,268,145,3,2,6,3,2,2,1,0] => [5,7]
  | _ => []

def normalized (g : List Nat) := relabel (renumber g) g

def roots3 : List (List Nat) := [[15,560,388,274,146,3,2,6,3,2,2,1,0]]
def roots4 : List (List Nat) := [[7,24,130,145,3,2,6,3,2,2,1,0],
  [7,24,146,145,3,2,6,3,2,2,1,0],
  [7,24,194,145,3,2,6,3,2,2,1,0],
  [7,280,146,145,3,2,6,3,2,2,1,0],
  [7,280,194,137,3,2,6,3,2,2,1,0],
  [7,24,98,137,3,12,9,3,2,2,1,0],
  [7,132,268,137,3,12,9,3,2,2,1,0],
  [7,196,268,137,3,12,9,3,2,2,1,0],
  [7,388,258,134,3,12,9,3,2,2,1,0],
  [7,388,268,137,3,12,9,3,2,2,1,0],
  [15,296,196,140,73,1,6,3,2,2,1,0],
  [15,352,196,146,82,3,10,10,1,0,1,0]]

theorem degrees_length (g : List Nat) : (degrees g).length=g.length := by
  have step (xs : List Nat) (m : Nat) : (bump m xs).length=xs.length := by
    induction xs generalizing m with | nil => rfl | cons a xs ih => simp [bump,ih]
  induction g with | nil => rfl | cons a g ih => simp [degrees,step,ih]

theorem bump_sum (xs : List Nat) (m : Nat) : (bump m xs).sum=xs.sum+countBits xs.length m := by
  induction xs generalizing m with | nil => rfl | cons a xs ih => simp [bump,countBits,ih]; omega

def edges_ : List Nat → Nat
  | [] => 0
  | m::t => countBits t.length m + edges_ t

theorem energy (rows : List Nat) : (degrees rows).sum=2*edges_ rows := by
  induction rows with
  | nil => rfl
  | cons m t ih => simp [degrees,edges_,bump_sum,degrees_length,ih]; omega

theorem count_shift (n a j : Nat) : countBits (j+n) (2^j*a)=countBits n a := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : 2^(j+1)*a=2*(2^j*a) := by rw [pow_succ]; ring
    rw [Nat.succ_add,countBits,e]
    simp [ih]

theorem count_full (d n : Nat) : countBits (d+n) (2^d-1)=d := by
  induction d with
  | zero =>
    have h (t : Nat) : countBits t 0=0 := by induction t with | zero => rfl | succ k ih => simp [countBits,ih]
    simp [h]
  | succ d ih =>
    have hp : 0 < 2^d := Nat.two_pow_pos _
    have split : 2^(d+1)-1=2*(2^d-1)+1 := by rw [pow_succ]; omega
    rw [Nat.succ_add,countBits,split,half_step,ih]
    omega

theorem shifted_length (xs : List Nat) : (shifted xs).length=xs.length := by
  induction xs with | nil => rfl | cons a xs ih => simp [shifted,ih]

theorem edges_attached (xs b : List Nat) : edges_ (attach xs b) =
    xs.length + (xs.map (countBits b.length)).sum + edges_ b := by
  have h (ls : List Nat) : edges_ (shifted ls++b)=(ls.map (countBits b.length)).sum+edges_ b := by
    induction ls with
    | nil => simp [shifted]
    | cons a ls ih => simp [shifted,edges_,shifted_length,count_shift,ih,Nat.add_assoc]
  simp [attach,edges_,shifted_length,count_full,h,Nat.add_assoc]

def Extension (k d : Nat) (b cs : List Nat) : Prop :=
  cs.length = d ∧ (∀ x ∈ cs, x ∈ usable k d b) ∧ okContacts k (inds b) cs = true
theorem graphExtension {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k d : Nat) (ht : G.CliqueFree 3) (hs : Small G A k)
    (r : V) (front base : List V) (hn : (r::front++base).Nodup)
    (hall : (r::front++base).toFinset=A) (hd : front.length=d)
    (ha : ∀ x∈front,G.Adj r x) (hb : ∀ x∈base,¬G.Adj r x)
    (hcount : ∀ x∈front,d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k)
    (_hmin : ∀ x∈A,d≤(A.filter (G.Adj x)).card)
    (horder : (contactsOf G base front).Pairwise (·≤·)) :
    ∃ cs, Extension k d (encode G base) cs ∧ encode G (r::front++base) = attach cs (encode G base) ∧ cs.Pairwise (· ≤ ·) := by
  let cs := contactsOf G base front
  have split := root_encoding G r front base ha hb ht
  change encode G (r::front++base) = attach cs (encode G base) at split
  have hbnd := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have hc (s) (mem : s ∈ cs) : s ∈ usable k d (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    let S := base.toFinset.filter (G.Adj x)
    have row := inds_complete G base hbnd S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have m := hcount x hx
    rw [sizeAt_finset G hbnd] at m
    change bits (base.map fun y => decide (G.Adj x y)) ∈ _
    rw [row_mark]
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨row,by simpa [S] using m⟩,rfl⟩
  have guard_ (u w : List Nat) (h : cs=u++w) : guardRows k (encode G base) (inds (encode G base)) u := by
    let sl := front.take u.length
    have hu : contactsOf G base sl = u := by
      change (front.take u.length).map _=u
      rw [List.map_take, show front.map _=u++w from h, List.take_left]
    have ssub := (List.take_sublist u.length front).append (List.Sublist.refl base)
    have nodup : (sl++base).Nodup := (List.nodup_cons.mp hn).2.sublist ssub
    have sub : (sl++base).toFinset ⊆ A := by
      intro x hx
      rw [← hall]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (ssub.subset (List.mem_toFinset.mp hx)))
    have ha' (x) (hx : x∈sl) := ha x ((List.take_sublist u.length front).subset hx)
    have indep : Gᶜ.IsClique (sl.toFinset : Set V) := by
      rw [G.isClique_compl]
      intro x hx y hy hxy
      exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x (List.mem_toFinset.mp hx)) (ha' y (List.mem_toFinset.mp hy)) hxy
    have em := contacts G sl base (by intro x hx y hy adj; exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x hx) (ha' y hy) adj.ne adj)
    change encode G (sl++base)=shifted (contactsOf G base sl)++encode G base at em
    rw [← hu]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ok_contacts G A k hs sl base nodup sub indep,?_⟩
    rw [← em]
    exact degrees_bound G ht A k hs _ nodup sub
  exact ⟨cs, ⟨by simp [cs,contactsOf,hd], hc,
    (Bool.and_eq_true_iff.mp (guard_ cs [] (by simp))).1⟩, split,horder⟩

theorem rootSplitting {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (norm : List Nat → List Nat)
    (hnorm : ∀ l : List V, ∃ l' : List V, l'.Perm l ∧ encode G l'=norm (encode G l))
    (k : Nat) (A : Finset V) (non : A.Nonempty) (cap : Nat) (hs : Small G A (k+1))
    (hu : A.Nonempty → ∃ x∈A,(A.filter (G.Adj x)).card ≤ cap) :
    ∃ (vs : List V) (d : Nat) (b cs : List Nat), vs.Nodup ∧ vs.toFinset=A ∧ d≤cap ∧
      b∈levels norm k (A.card-1-d) (k-1) ∧ Extension (k+1) d b cs ∧ encode G vs=attach cs b ∧ attach cs b ∈ grow (k+1) d b ∧ cs.Pairwise (· ≤ ·) ∧ ∃ r ∈ A, (A.filter (G.Adj r)).card = d := by
    obtain ⟨r,hr,hmin⟩ := A.exists_min_image (fun x => (A.filter (G.Adj x)).card) non
    let N := A.filter (G.Adj r)
    let B := A \ insert r N
    let d := N.card
    have hNr : r∉N := by simp [N]
    have hNA : N⊆A := Finset.filter_subset ..
    have hBA : B⊆A := Finset.sdiff_subset
    have hu' : d≤cap := by obtain ⟨x,hx,hh⟩ := hu non; exact (hmin x hx).trans hh
    have hdk : d≤k := Nat.le_of_lt_succ (hs N hNA (neighbors_small G ht A r))
    have hBcard : B.card + d + 1 = A.card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hr hNA)
      rw [Finset.card_insert_of_notMem hNr] at hh
      omega
    have rB : r∉B := by simp [B]
    have hbase (x) (hx : x∈B) : ¬G.Adj r x := by
      have h := Finset.mem_sdiff.mp hx
      exact fun ha => h.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h.1,ha⟩))
    have noK : Small G B k := by
      intro S hS hI
      have rn : r∉S := fun h => rB (hS h)
      have indep : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
        exact ⟨hI,fun x hx => ⟨fun e => rn (e ▸ hx),hbase x (hS hx)⟩⟩
      have hh := hs (insert r S) (Finset.insert_subset hr (hS.trans hBA)) indep
      rw [Finset.card_insert_of_notMem rn] at hh
      omega
    obtain ⟨base,hbn,hb,cls⟩ := levels_complete G ht norm hnorm k B (k-1) noK (by
      rintro ⟨x,hx⟩
      have mm := noK (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
      exact ⟨x,hx,by omega⟩)
    obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
    have ha (x) (hx : x∈front) : G.Adj r x := (Finset.mem_filter.mp (hf ▸ List.mem_toFinset.mpr hx)).2
    have hnot (x) (hx : x∈base) := hbase x (hb ▸ List.mem_toFinset.mpr hx)
    have dl : front.length=d := by rw [← List.toFinset_card_of_nodup hfn,hf]
    have nodup : (r::front++base).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · change r ∉ front++base
        rw [List.mem_append,not_or]
        exact ⟨fun h => hNr (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
      · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
    have cover : (r::front++base).toFinset=A := by
      ext x
      simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,Finset.mem_insert,Finset.mem_union,Finset.mem_sdiff]
      have h1 : x=r → x∈A := fun h => h ▸ hr
      have h2 : x∈N → x∈A := fun h => hNA h
      grind
    have hcount (x) (hx : x∈front) : d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k+1 := by
      have xN : x∈N := hf ▸ List.mem_toFinset.mpr hx
      have adj := ha x hx
      have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_sdiff,B]
        constructor
        · rintro ⟨yA,xy⟩
          by_cases yr : y=r
          · exact Or.inl yr
          · exact Or.inr ⟨⟨yA,not_or.mpr ⟨yr,fun yN => G.isIndepSet_neighborSet_of_triangleFree ht r adj (Finset.mem_filter.mp yN).2 xy.ne xy⟩⟩,xy⟩
        · rintro (rfl|⟨⟨yA,_⟩,xy⟩)
          · exact ⟨hr,adj.symm⟩
          · exact ⟨yA,xy⟩
      have mm := hmin x (hNA xN)
      have mx := hs (A.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht A x)
      have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
      rw [eq,Finset.card_insert_of_notMem rn] at mm mx
      rw [sizeAt_finset G hbn,hb]
      exact ⟨mm,mx⟩
    obtain ⟨cs,hcs,enc,ord⟩ := graphExtension G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    have grown := grow_complete G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    exact ⟨r::front++base, d, encode G base, cs, nodup, cover, hu',
      by simpa only [show A.card-1-d=B.card by omega] using cls, hcs, enc, enc ▸ grown,ord, ⟨r, hr, rfl⟩⟩


private abbrev WeightedRow := (Nat × Nat) × Nat

private def rowScore (W : List WeightedRow) (x : Nat) : Nat :=
  ((W.filter (fun w => x &&& w.1.1 == 0)).map Prod.snd).sum

private def rowCapacity (W : List WeightedRow) : Nat :=
  (W.map fun w => (5-w.1.2)*w.2).sum

private def penalty (f : Nat → Bool) (x : Nat) := (f x).toNat

private theorem rowScore_cons (w : WeightedRow) (W : List WeightedRow) (cs : List Nat) :
    (cs.map (rowScore (w::W))).sum =
    (cs.filter (fun x => x &&& w.1.1 == 0)).length*w.2 + (cs.map (rowScore W)).sum := by
  induction cs with
  | nil => simp
  | cons x cs ih =>
    by_cases e : x &&& w.1.1 = 0
    · simp [rowScore,e,Nat.succ_mul] at ih ⊢
      omega
    · simp [rowScore,e] at ih ⊢
      omega

private theorem rowScore_le (b cs : List Nat) (W : List WeightedRow)
    (valid : ∀ w∈W,w.1∈inds b) (good : okContacts 6 (inds b) cs=true) :
    (cs.map (rowScore W)).sum ≤ rowCapacity W := by
  induction W with
  | nil =>
    have h : rowScore [] = fun _ => 0 := rfl
    simp [h,rowCapacity]
  | cons w W ih =>
    have sub := ih (fun t ht => valid t (.tail _ ht))
    have hm := of_decide_eq_true (List.all_eq_true.mp good w.1 (valid w (.head _)))
    have lecap : (cs.filter (fun x => x &&& w.1.1 == 0)).length ≤ 5-w.1.2 := by omega
    have lh := Nat.mul_le_mul_right w.2 lecap
    rw [rowScore_cons]
    change _ ≤ (5-w.1.2)*w.2 + rowCapacity W
    omega

private theorem rowScore_ge (b : List Nat) (f : Nat → Bool) (edgeWeight extraWeight low : Nat) (W : List WeightedRow)
    (cs : List Nat) (h : ∀ x∈cs, low ≤ countBits b.length x * edgeWeight + penalty f x * extraWeight + rowScore W x) :
    cs.length*low ≤ (cs.map (countBits b.length)).sum * edgeWeight +
      (cs.map (penalty f)).sum * extraWeight + (cs.map (rowScore W)).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hh := ih (fun x hx => h x (.tail _ hx))
    have hc := h c (.head _)
    simp only [List.length_cons,Nat.succ_mul,List.map_cons,List.sum_cons,Nat.add_mul]
    omega


private def dualCheckSimple (limit : Nat) (b : List Nat) (d edgeWeight low : Nat)
    (W : List WeightedRow) : Bool :=
  W.all (fun w => decide (w.1 ∈ inds b)) &&
  (usable 6 d b).all (fun x => decide (low ≤ countBits b.length x * edgeWeight + rowScore W x)) &&
  decide ((limit - edges_ b - d) * edgeWeight + rowCapacity W < d * low)

theorem viaDual {limit : Nat} (b cs : List Nat) (d edgeWeight low : Nat) (W : List WeightedRow)
    (ext : Extension 6 d b cs)
    (check : dualCheckSimple limit b d edgeWeight low W = true) :
    limit+1 ≤ edges_ (attach cs b) := by
  by_contra! small
  obtain ⟨len, mem, good⟩ := ext
  obtain ⟨both, last⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨valid, opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have lower := rowScore_ge b (fun _ => false) edgeWeight 0 low W cs (fun x hx => by
    have hx' := of_decide_eq_true (List.all_eq_true.mp opts x (mem x hx))
    simp only [Nat.mul_zero, Nat.add_zero]
    exact hx')
  simp only [Nat.mul_zero, Nat.add_zero] at lower
  rw [edges_attached, len] at small
  have e : (cs.map (countBits b.length)).sum ≤ limit - edges_ b - d := by omega
  have he := Nat.mul_le_mul_right edgeWeight e
  have hl := of_decide_eq_true last
  rw [len] at lower
  omega

private def allInd4 (b : List Nat) : List WeightedRow :=
  ((inds b).filter (fun p => p.2 == 4)).map (fun p => (p, 1))

private abbrev b3_0 : List Nat := [15,560,388,274,146,3,2,6,3,2,2,1,0]
private abbrev b4_0 : List Nat := [7,24,130,145,3,2,6,3,2,2,1,0]
private abbrev b4_1 : List Nat := [7,24,146,145,3,2,6,3,2,2,1,0]
private abbrev b4_2 : List Nat := [7,24,194,145,3,2,6,3,2,2,1,0]
private abbrev b4_3 : List Nat := [7,280,146,145,3,2,6,3,2,2,1,0]
private abbrev b4_4 : List Nat := [7,280,194,137,3,2,6,3,2,2,1,0]
private abbrev b4_5 : List Nat := [7,24,98,137,3,12,9,3,2,2,1,0]
private abbrev b4_6 : List Nat := [7,132,268,137,3,12,9,3,2,2,1,0]
private abbrev b4_7 : List Nat := [7,196,268,137,3,12,9,3,2,2,1,0]
private abbrev b4_8 : List Nat := [7,388,258,134,3,12,9,3,2,2,1,0]
private abbrev b4_9 : List Nat := [7,388,268,137,3,12,9,3,2,2,1,0]
private abbrev b4_10 : List Nat := [15,296,196,140,73,1,6,3,2,2,1,0]
private abbrev b4_11 : List Nat := [15,352,196,146,82,3,10,10,1,0,1,0]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
theorem smaller3 : (levels normalized 5 13 4).all (fun b => decide (b ∈ roots3)) = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
theorem smaller4 : (levels normalized 5 12 4).all (fun b => decide (b ∈ roots4)) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b3_0_32_cert : dualCheckSimple 31 b3_0 2 4 26 (allInd4 b3_0) = true := by
  decide +kernel

private def b4_0_32_w : List WeightedRow :=
  [((1224,4),3),((1576,4),2),((1128,4),1),((2244,4),2),((2340,4),2),((804,4),2),((204,4),1),
   ((108,4),3),((2322,4),1),((786,4),3),((2194,4),2),((1170,4),2),((1546,4),2),((2310,4),2),
   ((526,4),2),((142,4),2),((2241,4),2),((801,4),2),((2145,4),2),((1121,4),2),((1553,4),2),
   ((2321,4),3),((785,4),1),((1169,4),2)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_0_32_cert : dualCheckSimple 31 b4_0 3 5 30 b4_0_32_w = true := by
  decide +kernel

private def b4_1_32_w : List WeightedRow :=
  [((1224,4),2),((2340,4),1),((804,4),1),((108,4),2),((786,4),1),((2194,4),1),((1170,4),1),
   ((2310,4),1),((526,4),1),((2241,4),1),((2321,4),1),((785,4),1),((1169,4),1)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_1_32_cert : dualCheckSimple 31 b4_1 3 2 10 b4_1_32_w = true := by
  decide +kernel

private def b4_2_32_w : List WeightedRow :=
  [((1224,4),2),((1576,4),2),((2244,4),2),((2340,4),3),((204,4),1),((108,4),4),((786,4),4),
   ((2194,4),1),((1170,4),1),((1546,4),2),((2310,4),2),((142,4),2),((2241,4),1),((801,4),1),
   ((2145,4),1),((1121,4),1),((1553,4),3),((2321,4),3),((785,4),1),((1169,4),1)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_2_32_cert : dualCheckSimple 31 b4_2 3 5 25 b4_2_32_w = true := by
  decide +kernel

private def b4_3_32_w : List WeightedRow :=
  [((1224,4),2),((804,4),1),((108,4),2),((2322,4),1),((786,4),1),((2194,4),1),((2310,4),1),
   ((526,4),1),((1121,4),1),((2321,4),1),((1169,4),2)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_3_32_cert : dualCheckSimple 31 b4_3 3 3 11 b4_3_32_w = true := by
  decide +kernel

private def b4_4_32_w : List WeightedRow :=
  [((1576,4),1),((2244,4),1),((108,4),1),((786,4),1),((2194,4),1),((270,4),1),((1217,4),1),
   ((1553,4),1)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_4_32_cert : dualCheckSimple 31 b4_4 3 2 7 b4_4_32_w = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_5_32_cert : dualCheckSimple 31 b4_5 3 3 15 (allInd4 b4_5) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_6_32_cert : dualCheckSimple 31 b4_6 3 3 15 (allInd4 b4_6) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_7_32_cert : dualCheckSimple 31 b4_7 3 1 2 [] = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_8_32_cert : dualCheckSimple 31 b4_8 3 2 13 (allInd4 b4_8) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_9_32_cert : dualCheckSimple 31 b4_9 3 1 2 [] = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_10_32_cert : dualCheckSimple 31 b4_10 3 1 2 [] = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_11_32_cert : dualCheckSimple 31 b4_11 3 1 2 [] = true := by
  decide +kernel

theorem density16_of_min_deg (G : SimpleGraph (Fin 16)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 6)
    (hmin : ∀ v, 2 ≤ G.degree v) : 32 ≤ G.edgeFinset.card := by
  classical
  by_contra! hsmall
  let U : Finset (Fin 16) := Finset.univ
  have bounded : Small G U 6 := by
    intro I _ hI
    by_contra! hc
    exact (hi.mono hc) I ⟨hI, rfl⟩
  have low : U.Nonempty → ∃ x ∈ U, (U.filter (G.Adj x)).card ≤ 3 := by
    intro _
    by_contra! hn
    have h4 (x : Fin 16) : 4 ≤ G.degree x := by
      have hh := hn x (Finset.mem_univ _)
      simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree] at hh
      omega
    have w := Finset.sum_le_sum (s := U) (f := fun _ => 4) (g := fun x => G.degree x) (fun x _ => h4 x)
    have tot := G.sum_degrees_eq_twice_card_edges
    simp [U] at w
    omega
  have hn (l : List (Fin 16)) := relabel_real G (renumber (encode G l)) l
  obtain ⟨vs, d, b, cs, hv, cover, hd, hb, hcs, enc, _, _, ⟨r, _, hr⟩⟩ :=
    rootSplitting G ht normalized hn 5 U (by simp [U]) 3 bounded low
  have hdlb : 2 ≤ d := by
    have hmr := hmin r
    simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree] at hr
    omega
  have h32 : 32 ≤ edges_ (attach cs b) := by
    have hb' : b ∈ levels normalized 5 (15 - d) 4 := by simpa [U] using hb
    interval_cases d
    · have ok := of_decide_eq_true (List.all_eq_true.mp smaller3 b hb')
      simp only [roots3, List.mem_cons, List.not_mem_nil, or_false] at ok
      subst ok
      exact viaDual (limit:=31) b3_0 cs 2 4 26 (allInd4 b3_0) hcs b3_0_32_cert
    · have ok := of_decide_eq_true (List.all_eq_true.mp smaller4 b hb')
      simp only [roots4, List.mem_cons, List.not_mem_nil, or_false] at ok
      rcases ok with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact viaDual (limit:=31) b4_0 cs 3 5 30 b4_0_32_w hcs b4_0_32_cert
      · exact viaDual (limit:=31) b4_1 cs 3 2 10 b4_1_32_w hcs b4_1_32_cert
      · exact viaDual (limit:=31) b4_2 cs 3 5 25 b4_2_32_w hcs b4_2_32_cert
      · exact viaDual (limit:=31) b4_3 cs 3 3 11 b4_3_32_w hcs b4_3_32_cert
      · exact viaDual (limit:=31) b4_4 cs 3 2 7 b4_4_32_w hcs b4_4_32_cert
      · exact viaDual (limit:=31) b4_5 cs 3 3 15 (allInd4 b4_5) hcs b4_5_32_cert
      · exact viaDual (limit:=31) b4_6 cs 3 3 15 (allInd4 b4_6) hcs b4_6_32_cert
      · exact viaDual (limit:=31) b4_7 cs 3 1 2 [] hcs b4_7_32_cert
      · exact viaDual (limit:=31) b4_8 cs 3 2 13 (allInd4 b4_8) hcs b4_8_32_cert
      · exact viaDual (limit:=31) b4_9 cs 3 1 2 [] hcs b4_9_32_cert
      · exact viaDual (limit:=31) b4_10 cs 3 1 2 [] hcs b4_10_32_cert
      · exact viaDual (limit:=31) b4_11 cs 3 1 2 [] hcs b4_11_32_cert
  rw [← enc] at h32
  have dg : degrees (encode G vs) = vs.map (fun x => G.degree x) := by
    rw [degrees_encode]
    apply List.map_congr_left
    intro x _
    rw [sizeAt_finset G hv, cover]
    simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
  have w := List.sum_toFinset (fun x => G.degree x) hv
  rw [cover] at w
  have tot := G.sum_degrees_eq_twice_card_edges
  have hh : 64 ≤ (degrees (encode G vs)).sum := by rw [energy]; omega
  rw [dg, ← w] at hh
  exact (by change 64 ≤ ∑ i, G.degree i at hh; omega : False)

end OMA.RamseyFinite
end RamseyFiniteSection


namespace Ramsey39Full
open SimpleGraph Ramsey39Children
theorem density16 (G : SimpleGraph (Fin 16)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) : 32 ≤ G.edgeFinset.card := by
  have hmin (v : Fin 16) : 2 ≤ G.degree v := by
    have hdc := nonneighbors_lt fourteen_works G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  exact OMA.RamseyFinite.density16_of_min_deg G ht hc hmin

end Ramsey39Full


namespace OMA.RamseyFinite
open SimpleGraph Finset
/-- Reading the forward adjacency code counts each undirected edge exactly once. -/
theorem edges_encode_univ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (nd : vs.Nodup) (full : vs.toFinset=univ) :
    edges_ (encode G vs) = G.edgeFinset.card := by
  have dg : degrees (encode G vs) = vs.map (fun x => G.degree x) := by
    rw [degrees_encode]
    apply List.map_congr_left
    intro x _
    rw [sizeAt_finset G nd,full]
    simp only [← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
  have hs := List.sum_toFinset (fun x => G.degree x) nd
  rw [full] at hs
  have ht := G.sum_degrees_eq_twice_card_edges
  have he := energy (encode G vs)
  rw [dg, ← hs] at he
  omega

/-- A finite root-extension check returns an ordering of every sparse graph.
The cap on the least degree follows by averaging. -/
theorem classify_from_grow {V : Type} [Fintype V] [DecidableEq V]
    {n cap budget : Nat} (code : List Nat) (normal : List Nat → List Nat)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : Fintype.card V=n)
    (hp : 0<n) (cut : 2*budget<n*(cap+1)) (tri : G.CliqueFree 3) (ind : Gᶜ.CliqueFree 6)
    (small : G.edgeFinset.card ≤ budget)
    (canNormalize : ∀ l : List V, ∃ t : List V, t.Perm l ∧ encode G t=normal (encode G l))
    (check : ∀ d≤cap, ∀ b ∈ levels normalized 5 (n-1-d) 4, ∀ cs,
      Extension 6 d b cs → cs.Pairwise (· ≤ ·) → attach cs b ∈ grow 6 d b →
      edges_ (attach cs b)≤budget → normal (attach cs b)=code) :
    ∃ vs : List V, vs.Nodup ∧ (∀ x, x∈vs) ∧ encode G vs=code := by
  classical
  let U : Finset V := univ
  have hnU : U.card=n := by simpa [U] using hn
  have non : U.Nonempty := Finset.card_pos.mp (hnU ▸ hp)
  have bounded : Small G U 6 := by
    intro I _ hi
    by_contra! h
    exact ind.mono h I ⟨hi,rfl⟩
  have low : U.Nonempty → ∃ x∈U, (U.filter (G.Adj x)).card ≤ cap := by
    intro _
    by_contra! h
    have each (x : V) : cap+1≤G.degree x := by
      have l := h x (Finset.mem_univ _)
      simpa only [U,← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
        using (Nat.succ_le_of_lt l)
    have sum := Finset.sum_le_sum (s:=univ) (f:=fun _ : V => cap+1)
      (g:=fun x => G.degree x) (fun x _ => each x)
    rw [G.sum_degrees_eq_twice_card_edges] at sum
    simp only [Finset.sum_const,Finset.card_univ,hn,nsmul_eq_mul,Nat.cast_id] at sum
    omega
  have nearby (l : List V) := relabel_real G (renumber (encode G l)) l
  obtain ⟨vs,d,b,cs,nd,full,hd,hb,hcs,eq,grown,ord,_⟩ :=
    rootSplitting G tri normalized nearby 5 U non cap bounded low
  have ec := edges_encode_univ G vs nd full
  rw [eq] at ec
  have finalCode := check d hd b (hnU ▸ hb) cs hcs ord grown (ec ▸ small)
  obtain ⟨t,perm,te⟩ := canNormalize vs
  refine ⟨t,perm.nodup_iff.mpr nd,fun x => perm.mem_iff.mpr ?_,by rw [te,eq,finalCode]⟩
  exact List.mem_toFinset.mp (full ▸ Finset.mem_univ x)
end OMA.RamseyFinite


namespace OMA.RamseyFinite
open SimpleGraph Finset

/-- The list fold used by the row certificates reads the same forward bits
as the graph generator. The catalogue code also fixes the exact edge count. -/
theorem realize_sparse_label {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {code : List Nat} {e : Nat}
    (size : edges_ code=e)
    (found : ∃ vs : List V, vs.Nodup ∧ (∀ x, x∈vs) ∧ encode G vs=code) :
    let pack := fun bs : List Bool => bs.foldr (fun b k => 2*k+b.toNat) 0
    let label := fun (ws : List V) => (ws.foldr (fun v (p : List V × List ℕ) =>
      (v::p.1, pack (p.1.map fun x => decide (G.Adj v x)) :: p.2)) ([],[])).2
    G.edgeFinset.card=e ∧ ∃ vs : List V, vs.Nodup ∧ (∀ x, x∈vs) ∧ label vs=code := by
  intro pack label
  obtain ⟨vs,nd,full,eq⟩ := found
  have hcover : vs.toFinset=univ := by ext x; simp [full x]
  have count := edges_encode_univ G vs nd hcover
  rw [eq,size] at count
  have hp (bs : List Bool) : pack bs=bits bs := by
    induction bs with
    | nil => rfl
    | cons b l ih => change 2*pack l+b.toNat=2*bits l+b.toNat; rw [ih]
  let pair := fun (ws : List V) => ws.foldr (fun v (p : List V × List ℕ) =>
    (v::p.1, pack (p.1.map fun x => decide (G.Adj v x)) :: p.2)) ([],[])
  have agree (l : List V) : pair l=(l,encode G l) := by
    induction l with
    | nil => rfl
    | cons x xs ih =>
      change (x::(pair xs).1,pack ((pair xs).1.map fun y => decide (G.Adj x y))::(pair xs).2)=_
      rw [ih]
      simp only [hp,encode]
  have h := congrArg Prod.snd (agree vs)
  exact ⟨count.symm,vs,nd,full,h.trans eq⟩
end OMA.RamseyFinite


/- Budgeted traversal of neighbor contacts, from the checked Ramsey(3,7)
enumeration by @Deldor14 (PR 6220). The parent bound now allows arbitrary
edge budgets. Append to the finite graph enumeration of PR 12460. -/
namespace OMA.RamseyFinite

def weighted (cost : Nat × Nat → Nat) (xs : List (Nat × Nat)) := (xs.map cost).sum

theorem trace_size (opts : List (Nat × Nat)) (u : Nat) (ending : List (Nat × Nat) → Bool)
    (cost : Nat × Nat → Nat) (floor : Nat) (positive : ∀ a∈opts,floor≤cost a)
    (n lo : Nat) (acc : List (Nat × Nat)) (st : List Nat) {xs : List (Nat × Nat)}
    (hx : xs∈traverse opts u ending n lo acc st) :
    xs.length = acc.length+n ∧ weighted cost acc+n*floor≤weighted cost xs := by
  induction n generalizing lo acc st with
  | zero =>
    simp only [traverse] at hx
    split at hx
    · obtain rfl := List.mem_singleton.mp hx
      simp
    · contradiction
  | succ n ih =>
    obtain ⟨a,ha,mem⟩ := List.mem_flatMap.mp hx
    split at mem
    · obtain ⟨lh,wh⟩ := ih _ _ _ mem
      have h := positive a ha
      simp only [List.length_cons,weighted,List.map_cons,List.sum_cons] at lh wh ⊢
      rw [Nat.succ_mul]
      omega
    · contradiction

def trimmed (opts : List (Nat × Nat)) (u : Nat) (ending : List (Nat × Nat) → Bool)
    (cost : Nat × Nat → Nat) (floor : Nat) : Nat → Nat → Nat → List (Nat × Nat) → List Nat → List (List (Nat × Nat))
  | 0,_,_,acc,_ => if ending acc then [acc] else []
  | n+1,lo,budget,acc,st => if (n+1)*floor≤budget then opts.flatMap fun a =>
    if lo≤a.1 && a.2 &&& st.headD u == 0 && cost a ≤ budget then
      trimmed opts u ending cost floor n a.1 (budget-cost a) (a::acc) (tick u a.2 st) else []
    else []

theorem trace_trim (opts : List (Nat × Nat)) (u : Nat) (ending : List (Nat × Nat) → Bool)
    (cost : Nat × Nat → Nat) (floor : Nat) (positive : ∀ a∈opts,floor≤cost a)
    (n lo budget : Nat) (acc : List (Nat × Nat)) (st : List Nat) {xs : List (Nat × Nat)}
    (hx : xs∈traverse opts u ending n lo acc st) (hw : weighted cost xs≤budget+weighted cost acc) :
    xs∈trimmed opts u ending cost floor n lo budget acc st := by
  induction n generalizing lo budget acc st with
  | zero => exact hx
  | succ n ih =>
    have needed := (trace_size opts u ending cost floor positive _ _ _ _ hx).2
    have enough : (n+1)*floor ≤ budget := by omega
    simp only [trimmed,if_pos enough,List.mem_flatMap]
    obtain ⟨a,ha,mem⟩ := List.mem_flatMap.mp hx
    split at mem
    next hok =>
      have lower := (trace_size opts u ending cost floor positive _ _ _ _ mem).2
      have e : weighted cost (a::acc)=cost a+weighted cost acc := rfl
      rw [e] at lower
      have haff : cost a≤budget := by omega
      refine ⟨a,ha,?_⟩
      simp only [hok,Bool.true_and,haff,decide_true,if_true]
      exact ih _ (budget-cost a) _ _ mem (by rw [e]; omega)
    next => contradiction

def costAt (b : List Nat) (a : Nat × Nat) := countBits b.length a.1
def cutGrow (d edgeBound : Nat) (base : List Nat) (opts : List (Nat × Nat)) (u : Nat) (lims : List Nat) :=
  let ending := fun cs : List (Nat × Nat) => (degrees (attach (cs.reverse.map Prod.fst) base)).all (d≤·)
  (trimmed opts u ending (costAt base) (d-1) d 0 (edgeBound-edges_ base-d) [] lims).map
    (fun cs => attach (cs.reverse.map Prod.fst) base)

theorem cut_contains {k d edgeBound : Nat} {base : List Nat} {opts : List (Nat × Nat)} {u : Nat} {lims g : List Nat}
    (minimum : ∀ a∈opts,d-1≤costAt base a)
    (hg : g∈assemble k d base opts u lims) (he : edges_ g ≤ edgeBound) :
    g∈cutGrow d edgeBound base opts u lims := by
  obtain ⟨xs,hx,rfl⟩ := List.mem_map.mp hg
  have sz := (trace_size opts u _ (costAt base) (d-1) minimum _ _ _ _ hx).1
  have ln : xs.length=d := by simpa using sz
  rw [edges_attached] at he
  have sum' : ((xs.reverse.map Prod.fst).map (countBits base.length)).sum = weighted (costAt base) xs := by
    simp [weighted,List.map_reverse,List.sum_reverse,Function.comp_def]
    rfl
  rw [sum'] at he
  simp only [List.length_map,List.length_reverse,ln] at he
  apply List.mem_map.mpr
  refine ⟨xs,trace_trim _ _ _ _ _ minimum _ _ _ _ _ hx ?_,rfl⟩
  change weighted (costAt base) xs ≤ edgeBound-edges_ base-d+0
  omega


theorem point_weight (b : List Nat) {a : Nat × Nat} (ha : a∈inds b) :
    countBits b.length a.1=a.2 := by
  induction b generalizing a with
  | nil => obtain rfl := List.mem_singleton.mp ha; rfl
  | cons m b ih =>
    simp only [inds,List.mem_append,List.mem_map,List.mem_filter] at ha
    rcases ha with ⟨t,ht,rfl⟩|⟨t,⟨ht,_⟩,rfl⟩
    · simp [ind0,countBits,ih ht]
    · simp [ind1,countBits,half_step,ih ht]; omega
theorem tag_floor (k d : Nat) (b : List Nat) (a : Nat × Nat) (ha : a∈tagged k d b) :
    d-1 ≤ costAt b a := by
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
  obtain ⟨t,hh,rfl⟩ := List.mem_map.mp hx
  obtain ⟨ht,sz⟩ := List.mem_filter.mp hh
  have ds := of_decide_eq_true (Bool.and_eq_true_iff.mp sz).1
  change d-1≤countBits b.length t.1
  rw [point_weight b ht]
  omega
theorem parent_low {k d edgeBound : Nat} {b g : List Nat} (hg : g∈grow k d b) (he : edges_ g≤edgeBound) :
    edges_ b+d*(d-1)+d≤edgeBound := by
  obtain ⟨xs,hx,rfl⟩ := List.mem_map.mp hg
  have ⟨len,wt⟩ := trace_size _ _ _ (costAt b) (d-1) (tag_floor k d b) _ _ _ _ hx
  have e : xs.length=d := by simpa using len
  rw [edges_attached] at he
  have sum' : ((xs.reverse.map Prod.fst).map (countBits b.length)).sum=weighted (costAt b) xs := by
    simp [weighted,List.map_reverse,List.sum_reverse,Function.comp_def]
    rfl
  simp only [List.length_map,List.length_reverse,e,sum'] at he
  change 0+d*(d-1)≤weighted (costAt b) xs at wt
  omega

/-- Pruning by the remaining contact-edge budget preserves all sparse outputs. -/
theorem grow_to_trim {k d edgeBound : Nat} {b g : List Nat}
    (hg : g ∈ grow k d b) (he : edges_ g ≤ edgeBound) :
    g ∈ cutGrow d edgeBound b (tagged k d b) (universal (inds b)) (cells k (inds b) [] k 1) :=
  cut_contains (tag_floor k d b) hg he

end OMA.RamseyFinite


/- Relabeling consecutive vertices preserves the edge count of a forward
adjacency encoding, including when some high bits extend beyond its vertex set. -/
namespace OMA.RamseyFinite

private lemma count_pairbit (n x b : ℕ) (hb : b < 2) :
    countBits (n+1) (2*x + b) = b + countBits n x := by
  rw [countBits]
  have hmod : (2*x+b)%2 = b := by omega
  have hdiv : (2*x+b)/2 = x := by omega
  rw [hmod,hdiv]

private lemma count_exchange {i n : ℕ} (x : ℕ) (h : i+2 ≤ n) :
    countBits n (exchange i x) = countBits n x := by
  induction i generalizing n x with
  | zero =>
    obtain ⟨t, ht⟩ : ∃ t, n=t+2 := ⟨n-2, by omega⟩
    subst n
    have e : exchange 0 x = 2*(2*(x/4)+(x%2)) + ((x/2)%2) := by
      simp only [exchange]
      omega
    rw [e, count_pairbit _ _ _ (by omega), count_pairbit _ _ _ (by omega)]
    change _ = x%2 + (x/2%2 + countBits t (x/2/2))
    rw [show x/2/2 = x/4 by omega]
    omega
  | succ i ih =>
    obtain ⟨t, ht⟩ : ∃ t, n=t+1 := ⟨n-1, by omega⟩
    subst n
    rw [exchange, count_pairbit _ _ _ (by omega), ih (x/2) (by omega)]
    rfl

private lemma length_swap_code (i : ℕ) (g : List ℕ) : (swapCode i g).length = g.length := by
  induction i generalizing g with
  | zero => cases g with | nil => rfl | cons p t => cases t <;> rfl
  | succ i ih =>
    cases g with
    | nil => rfl
    | cons p t => simp [swapCode,ih]

lemma edges_swap_code (i : ℕ) (g : List ℕ) (h : i+2 ≤ g.length) :
    edges_ (swapCode i g) = edges_ g := by
  induction i generalizing g with
  | zero =>
    cases g with
    | nil => simp at h
    | cons p t =>
      cases t with
      | nil => simp at h
      | cons q t =>
        simp only [swapCode,edges_,List.length_cons]
        rw [Nat.add_comm (p%2), count_pairbit _ _ _ (by omega), countBits]
        omega
  | succ i ih =>
    cases g with
    | nil => simp at h
    | cons p t =>
      have ht : i+2 ≤ t.length := by simp only [List.length_cons] at h; omega
      simp only [swapCode,edges_,length_swap_code, count_exchange p ht, ih t ht]

theorem edges_relabel (swaps g : List ℕ) : edges_ (relabel swaps g) = edges_ g := by
  induction swaps generalizing g with
  | nil => rfl
  | cons i is ih =>
    by_cases hi : i+2 ≤ g.length
    · simpa only [relabel,List.foldl_cons,if_pos hi] using (ih (swapCode i g)).trans (edges_swap_code i g hi)
    · simpa only [relabel,List.foldl_cons,if_neg hi] using ih g

theorem edges_normalized (g : List ℕ) : edges_ (normalized g) = edges_ g :=
  edges_relabel _ _

theorem norm_edges_seed (g : List Nat) : edges_ (normalized g) = edges_ g :=
  edges_normalized g

end OMA.RamseyFinite


namespace OMA.RamseyFinite

def final14 : List Nat := [129,512,65,64,259,66,18,6,8,8,4,1,1,0]
def final15 : List Nat := [515,2112,260,67,528,64,131,34,4,4,3,2,2,1,0]

private def finalSwaps (g : List Nat) : List Nat :=
  ([([3,32,72,3,128,144,3,2,6,3,2,2,1,0], [2,3,7,6,5,4,10,9,8,7,6,5,7,6,12,11,10,9,8,7,12,11,10]),
    ([3,16,48,3,128,144,3,2,6,3,2,2,1,0], [2,3,8,7,6,5,4,10,9,8,7,6,5,8,7,6,12,11,10,9,8,7,12,11,10]),
    ([3,4,513,3,128,144,3,2,6,3,2,2,1,0], [5,4,3,2,6,5,4,3,6,5,4,12,11,10,9,8,7,6,5,6,11,10,9,8,7,9,10,12]),
    ([3,2,6,3,128,144,3,2,6,3,2,2,1,0], [5,4,3,2,6,5,4,3,11,10,9,8,7,6,5,4,12,11,10,9,8,7,6,5,7,6,12,11,10,9,8,7,10,9,11,10]),
    ([3,32,72,3,192,128,3,2,6,3,2,2,1,0], [2,4,3,7,6,5,4,9,8,7,6,5,7,6,11,10,9,8,7,12,11,10]),
    ([3,16,48,3,192,128,3,2,6,3,2,2,1,0], [2,4,3,8,7,6,5,4,9,8,7,6,5,8,7,6,11,10,9,8,7,12,11,10]),
    ([3,8,1025,3,192,128,3,2,6,3,2,2,1,0], [5,4,3,2,6,5,4,3,5,4,11,10,9,8,7,6,5,6,10,9,8,7,9,10,12]),
    ([3,2,6,3,192,128,3,2,6,3,2,2,1,0], [5,4,3,2,6,5,4,3,12,11,10,9,8,7,6,5,4,12,11,10,9,8,7,6,5,8,7,6,11,10,9,8,7,10,9,11,10]),
    ([3,1024,1152,3,4,9,3,2,6,3,2,2,1,0], [2,1,0,3,2,1,7,6,5,4,10,9,8,7,6,5,7,6,12,11,10,9,8,7,8,12,11,10]),
    ([3,1536,1024,3,4,9,3,2,6,3,2,2,1,0], [2,1,0,3,2,1,3,7,6,5,4,9,8,7,6,5,7,6,11,10,9,8,7,8,12,11,10]),
    ([3,4,17,3,4,9,3,2,6,3,2,2,1,0], [11,10,9,8,7,6,5,4,3,2,12,11,10,9,8,7,6,5,4,3,6,5,4,7,6,5,6,9,8,7,11,10,9,12,11,10]),
    ([3,2,6,3,4,9,3,2,6,3,2,2,1,0], [11,10,9,8,7,6,5,4,3,2,12,11,10,9,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,9,8,7,11,10,9,12,11,10]),
    ([3,1024,1152,3,2,6,3,2,6,3,2,2,1,0], [2,1,0,3,2,1,8,7,6,5,4,10,9,8,7,6,5,8,7,6,12,11,10,9,8,7,8,12,11,10]),
    ([3,1536,1024,3,2,6,3,2,6,3,2,2,1,0], [2,1,0,3,2,1,3,8,7,6,5,4,9,8,7,6,5,8,7,6,11,10,9,8,7,8,12,11,10]),
    ([3,4,9,3,2,6,3,2,6,3,2,2,1,0], [11,10,9,8,7,6,5,4,3,2,12,11,10,9,8,7,6,5,4,3,6,5,4,8,7,6,5,6,10,9,8,7,11,10,9,12,11,10]),
    ([3,2,6,3,2,6,3,2,6,3,2,2,1,0], [11,10,9,8,7,6,5,4,3,2,12,11,10,9,8,7,6,5,4,3,7,6,5,4,8,7,6,5,7,6,10,9,8,7,11,10,9,12,11,10]),
    ([7,72,144,529,3,128,144,3,2,6,3,2,2,1,0], [1,3,5,4,5,8,7,6,11,10,9,8,7,8,13,12,11,10,9,13,12]),
    ([7,72,148,513,3,128,144,3,2,6,3,2,2,1,0], [2,1,6,5,4,3,8,7,6,5,4,8,7,6,5,8,7,6,13,12,11,10,9,8,7,8,12,11,10,9,13]),
    ([7,40,96,521,3,128,144,3,2,6,3,2,2,1,0], [1,3,5,4,5,9,8,7,6,11,10,9,8,7,9,8,13,12,11,10,9,13,12]),
    ([7,40,100,513,3,128,144,3,2,6,3,2,2,1,0], [2,1,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,8,7,6,13,12,11,10,9,8,7,8,12,11,10,9,13]),
    ([7,24,34,73,3,128,144,3,2,6,3,2,2,1,0], [6,5,4,3,8,7,6,5,4,8,7,6,5,12,11,10,9,8,7,6,13,12,11,10,9,8,7,9,8,13,12,11,10,9,12]),
    ([7,24,18,49,3,128,144,3,2,6,3,2,2,1,0], [7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,12,11,10,9,8,7,6,13,12,11,10,9,8,7,9,8,13,12,11,10,9,12]),
    ([7,68,44,72,3,128,144,3,2,6,3,2,2,1,0], [2,1,4,3,12,11,10,9,8,7,6,5,4,5,9,8,7,6,12,11,10,9,8,7,9,8,13,12,11,10,9,11]),
    ([7,36,28,48,3,128,144,3,2,6,3,2,2,1,0], [2,1,4,3,12,11,10,9,8,7,6,5,4,5,10,9,8,7,6,12,11,10,9,8,7,10,9,8,13,12,11,10,9,11]),
    ([7,80,144,1041,3,192,128,3,2,6,3,2,2,1,0], [1,3,4,5,8,7,6,10,9,8,7,8,12,11,10,9,13,12]),
    ([7,80,152,1025,3,192,128,3,2,6,3,2,2,1,0], [2,1,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,12,11,10,9,8,7,8,11,10,9,13]),
    ([7,48,96,1033,3,192,128,3,2,6,3,2,2,1,0], [1,3,4,5,9,8,7,6,10,9,8,7,9,8,12,11,10,9,13,12]),
    ([7,48,104,1025,3,192,128,3,2,6,3,2,2,1,0], [2,1,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,7,6,12,11,10,9,8,7,8,11,10,9,13]),
    ([7,24,34,73,3,192,128,3,2,6,3,2,2,1,0], [6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,12,11,10,9,8,7,6,13,12,11,10,9,8,7,12,11,10,9,8,11,10,9,12,11,13]),
    ([7,24,18,49,3,192,128,3,2,6,3,2,2,1,0], [7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,12,11,10,9,8,7,6,13,12,11,10,9,8,7,12,11,10,9,8,11,10,9,12,11,13]),
    ([7,68,44,72,3,192,128,3,2,6,3,2,2,1,0], [2,1,5,4,3,13,12,11,10,9,8,7,6,5,4,5,9,8,7,6,11,10,9,8,7,9,8,13,12,11,10,9,11]),
    ([7,36,28,48,3,192,128,3,2,6,3,2,2,1,0], [2,1,5,4,3,13,12,11,10,9,8,7,6,5,4,5,10,9,8,7,6,11,10,9,8,7,10,9,8,13,12,11,10,9,11]),
    ([7,3072,2052,1041,3,4,9,3,2,6,3,2,2,1,0], [3,2,1,0,5,4,3,2,1,5,4,3,2,8,7,6,10,9,8,7,8,12,11,10,9,13,12]),
    ([7,3072,2050,1030,3,4,9,3,2,6,3,2,2,1,0], [4,3,2,1,0,7,6,5,4,3,2,1,5,4,3,2,8,7,6,10,9,8,7,9,8,12,11,10,9,13,12]),
    ([7,2056,1058,1152,3,4,9,3,2,6,3,2,2,1,0], [3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,8,7,6,11,10,9,8,7,8,13,12,11,10,9,13,12]),
    ([7,24,1026,1153,3,4,9,3,2,6,3,2,2,1,0], [13,12,11,10,9,8,7,6,5,4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,9,8,7,6,10,9,8,7,11,10,9,8,10,9,13,12,11,13]),
    ([7,24,1538,1025,3,4,9,3,2,6,3,2,2,1,0], [12,11,10,9,8,7,6,5,4,3,2,1,0,11,10,9,8,7,6,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,5,9,8,7,6,10,9,8,7,11,10,9,8,10,9,13,12,11,13]),
    ([7,2052,1036,1152,3,4,9,3,2,6,3,2,2,1,0], [4,3,2,1,0,7,6,5,4,3,2,1,5,4,3,2,5,4,8,7,6,11,10,9,8,7,9,8,13,12,11,10,9,13,12]),
    ([7,68,1028,1154,3,4,9,3,2,6,3,2,2,1,0], [13,12,11,10,9,8,7,6,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,8,7,6,9,8,7,8,11,10,9,13,12]),
    ([7,68,1540,1026,3,4,9,3,2,6,3,2,2,1,0], [2,12,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,8,7,6,9,8,7,8,11,10,9,13,12]),
    ([7,3072,2052,1033,3,2,6,3,2,6,3,2,2,1,0], [3,2,1,0,5,4,3,2,1,5,4,3,2,9,8,7,6,10,9,8,7,9,8,12,11,10,9,13,12]),
    ([7,3072,2050,1030,3,2,6,3,2,6,3,2,2,1,0], [4,3,2,1,0,6,5,4,3,2,1,5,4,3,2,9,8,7,6,10,9,8,7,9,8,12,11,10,9,13,12]),
    ([7,2056,1042,1152,3,2,6,3,2,6,3,2,2,1,0], [3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,9,8,7,6,11,10,9,8,7,9,8,13,12,11,10,9,13,12]),
    ([7,24,1026,1153,3,2,6,3,2,6,3,2,2,1,0], [13,12,11,10,9,8,7,6,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,12,11,10,9,13,12]),
    ([7,24,1538,1025,3,2,6,3,2,6,3,2,2,1,0], [2,12,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,12,11,10,9,13,12]),
    ([7,2052,1036,1152,3,2,6,3,2,6,3,2,2,1,0], [4,3,2,1,0,6,5,4,3,2,1,5,4,3,2,5,4,9,8,7,6,11,10,9,8,7,9,8,13,12,11,10,9,13,12]),
    ([7,36,1028,1154,3,2,6,3,2,6,3,2,2,1,0], [13,12,11,10,9,8,7,6,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,8,7,6,10,9,8,7,8,12,11,10,9,13,12]),
    ([7,36,1540,1026,3,2,6,3,2,6,3,2,2,1,0], [2,12,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,8,7,6,10,9,8,7,8,12,11,10,9,13,12])] : List (List Nat × List Nat)).lookup g |>.getD []

def normalizeFinal (g : List Nat) := relabel (finalSwaps g) g

theorem normalizeFinal_real {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (l : List V) :
    ∃ l', l'.Perm l ∧ encode G l'=normalizeFinal (encode G l) := relabel_real G _ l

private def narrow11 : List (List Nat) := [
  [3,128,144,3,2,6,3,2,2,1,0],
  [3,128,146,3,2,6,3,2,2,1,0],
  [3,128,145,3,2,6,3,2,2,1,0],
  [3,64,140,3,2,6,3,2,2,1,0],
  [3,192,128,3,2,6,3,2,2,1,0],
  [3,192,144,3,2,6,3,2,2,1,0],
  [3,192,136,3,2,6,3,2,2,1,0],
  [3,192,132,3,2,6,3,2,2,1,0],
  [3,192,130,3,2,6,3,2,2,1,0],
  [3,192,129,3,2,6,3,2,2,1,0],
  [3,32,76,3,2,6,3,2,2,1,0],
  [3,16,50,3,2,6,3,2,2,1,0],
  [3,144,144,3,2,6,3,2,2,1,0],
  [3,8,49,3,2,6,3,2,2,1,0],
  [3,136,144,3,2,6,3,2,2,1,0],
  [3,24,48,3,2,6,3,2,2,1,0],
  [3,4,9,3,2,6,3,2,2,1,0],
  [3,4,137,3,2,6,3,2,2,1,0],
  [3,4,73,3,2,6,3,2,2,1,0],
  [3,132,144,3,2,6,3,2,2,1,0],
  [3,132,129,3,2,6,3,2,2,1,0],
  [3,68,136,3,2,6,3,2,2,1,0],
  [3,196,128,3,2,6,3,2,2,1,0],
  [3,36,72,3,2,6,3,2,2,1,0],
  [3,12,129,3,2,6,3,2,2,1,0],
  [3,12,65,3,2,6,3,2,2,1,0],
  [3,12,33,3,2,6,3,2,2,1,0],
  [3,12,17,3,2,6,3,2,2,1,0],
  [3,12,9,3,2,6,3,2,2,1,0],
  [3,2,6,3,2,6,3,2,2,1,0],
  [3,2,134,3,2,6,3,2,2,1,0],
  [3,2,70,3,2,6,3,2,2,1,0],
  [3,130,144,3,2,6,3,2,2,1,0],
  [3,130,130,3,2,6,3,2,2,1,0],
  [3,66,132,3,2,6,3,2,2,1,0],
  [3,194,128,3,2,6,3,2,2,1,0],
  [3,34,68,3,2,6,3,2,2,1,0],
  [3,18,130,3,2,6,3,2,2,1,0],
  [3,18,66,3,2,6,3,2,2,1,0],
  [3,18,34,3,2,6,3,2,2,1,0],
  [3,18,18,3,2,6,3,2,2,1,0],
  [3,128,144,3,12,9,3,2,2,1,0],
  [3,64,136,3,12,9,3,2,2,1,0],
  [3,192,128,3,12,9,3,2,2,1,0],
  [3,8,9,3,12,9,3,2,2,1,0],
  [3,4,17,3,12,9,3,2,2,1,0],
  [3,2,6,3,12,9,3,2,2,1,0]]

private def narrow12 : List (List Nat) := [[7,24,130,145,3,2,6,3,2,2,1,0],[7,24,146,145,3,2,6,3,2,2,1,0],[7,24,194,145,3,2,6,3,2,2,1,0]]

private def lowerCut (d : Nat) (b : List Nat) :=
  cutGrow d 16 b (tagged 5 d b) (universal (inds b)) (cells 5 (inds b) [] 5 1)

private def sub0 : List (List Nat) := []
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem sub_fits0 : (levels normalized 4 10 3).all
  (fun z => decide (16 < edges_ z + 0 ∨ z ∈ sub0)) = true := by decide +kernel

private def sub1 : List (List Nat) := []
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem sub_fits1 : (levels normalized 4 9 3).all
  (fun z => decide (16 < edges_ z + 1 ∨ z ∈ sub1)) = true := by decide +kernel

private def sub2 : List (List Nat) := [[3,2,6,3,2,2,1,0],[3,12,9,3,2,2,1,0],[7,20,18,10,1,1,1,0]]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem sub_fits2 : (levels normalized 4 8 3).all
  (fun z => decide (16 < edges_ z + 4 ∨ z ∈ sub2)) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem lower2_0 : (lowerCut 2 [3,2,6,3,2,2,1,0]).all (fun t => decide (normalized t ∈ narrow11)) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem lower2_1 : (lowerCut 2 [3,12,9,3,2,2,1,0]).all (fun t => decide (normalized t ∈ narrow11)) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem lower2_2 : (lowerCut 2 [7,20,18,10,1,1,1,0]).all (fun t => decide (normalized t ∈ narrow11)) = true := by decide +kernel

private theorem sub_checked2 (z t : List Nat) (hz : z ∈ sub2) (ht : t ∈ lowerCut 2 z) : normalized t ∈ narrow11 := by
  simp only [sub2,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl
  · exact of_decide_eq_true (List.all_eq_true.mp lower2_0 _ ht)
  · exact of_decide_eq_true (List.all_eq_true.mp lower2_1 _ ht)
  · exact of_decide_eq_true (List.all_eq_true.mp lower2_2 _ ht)

private def sub3 : List (List Nat) := [[1,0,3,2,2,1,0],[1,1,3,2,2,1,0],[3,2,8,1,1,1,0]]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem sub_fits3 : (levels normalized 4 7 3).all
  (fun z => decide (16 < edges_ z + 9 ∨ z ∈ sub3)) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem lower3_0 : (lowerCut 3 [1,0,3,2,2,1,0]).all (fun t => decide (normalized t ∈ narrow11)) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem lower3_1 : (lowerCut 3 [1,1,3,2,2,1,0]).all (fun t => decide (normalized t ∈ narrow11)) = true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem lower3_2 : (lowerCut 3 [3,2,8,1,1,1,0]).all (fun t => decide (normalized t ∈ narrow11)) = true := by decide +kernel

private theorem sub_checked3 (z t : List Nat) (hz : z ∈ sub3) (ht : t ∈ lowerCut 3 z) : normalized t ∈ narrow11 := by
  simp only [sub3,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl
  · exact of_decide_eq_true (List.all_eq_true.mp lower3_0 _ ht)
  · exact of_decide_eq_true (List.all_eq_true.mp lower3_1 _ ht)
  · exact of_decide_eq_true (List.all_eq_true.mp lower3_2 _ ht)

private def sub4 : List (List Nat) := []
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem sub_fits4 : (levels normalized 4 6 3).all
  (fun z => decide (16 < edges_ z + 16 ∨ z ∈ sub4)) = true := by decide +kernel

private theorem inspect_seed_level {k n cap : Nat} {b : List Nat} (hn : n ≠ 0)
    (hb : b ∈ levels normalized (k+1) n cap) :
    ∃ d < min cap (min k (n-1)) + 1, ∃ z ∈ levels normalized k (n-1-d) (k-1),
      ∃ t ∈ grow (k+1) d z, normalized t = b := by
  rw [levels, if_neg hn] at hb
  simpa only [List.mem_eraseDups,List.mem_flatMap,List.mem_range,List.mem_map] using hb

private theorem base11_fits {b : List Nat} (h : b ∈ levels normalized 5 11 4) (he : edges_ b ≤ 16) : b ∈ narrow11 := by
  obtain ⟨d, hd, z, hz, t, ht, rfl⟩ := inspect_seed_level (k := 4) (n := 11) (cap := 4) (by decide) h
  change d < 5 at hd
  rw [norm_edges_seed] at he
  have hparent := parent_low ht he
  have hcut := grow_to_trim ht he
  interval_cases d
  · have good := of_decide_eq_true (List.all_eq_true.mp sub_fits0 z hz)
    have zs := good.resolve_left (by norm_num at hparent ⊢; omega)
    simp [sub0] at zs
  · have good := of_decide_eq_true (List.all_eq_true.mp sub_fits1 z hz)
    have zs := good.resolve_left (by norm_num at hparent ⊢; omega)
    simp [sub1] at zs
  · have good := of_decide_eq_true (List.all_eq_true.mp sub_fits2 z hz)
    have zs := good.resolve_left (by norm_num at hparent ⊢; omega)
    exact sub_checked2 z t zs hcut
  · have good := of_decide_eq_true (List.all_eq_true.mp sub_fits3 z hz)
    have zs := good.resolve_left (by norm_num at hparent ⊢; omega)
    exact sub_checked3 z t zs hcut
  · have good := of_decide_eq_true (List.all_eq_true.mp sub_fits4 z hz)
    have zs := good.resolve_left (by norm_num at hparent ⊢; omega)
    simp [sub4] at zs

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
private theorem base14_empty : levels normalized 5 14 4 = [] := by decide +kernel

private theorem base12_fits {b : List Nat} (h : b ∈ levels normalized 5 12 4) (he : edges_ b ≤ 21) : b ∈ narrow12 := by
  have hr := of_decide_eq_true (List.all_eq_true.mp smaller4 _ h)
  have chk : roots4.all (fun v => decide (21 < edges_ v ∨ v ∈ narrow12)) = true := by decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp chk _ hr)).resolve_left (by omega)

private theorem base12_floor {b : List Nat} (h : b ∈ levels normalized 5 12 4) : 20 ≤ edges_ b := by
  have hr := of_decide_eq_true (List.all_eq_true.mp smaller4 _ h)
  have chk : roots4.all (fun v => decide (20 ≤ edges_ v)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp chk _ hr)

private theorem base13_floor {b : List Nat} (h : b ∈ levels normalized 5 13 4) : 26 ≤ edges_ b := by
  have hr := of_decide_eq_true (List.all_eq_true.mp smaller3 _ h)
  have chk : roots3.all (fun v => decide (26 ≤ edges_ v)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp chk _ hr)

private def cutCatalog (d E : Nat) (b : List Nat) :=
  cutGrow d E b (tagged 6 d b) (universal (inds b)) (cells 6 (inds b) [] 6 1)

end OMA.RamseyFinite
namespace OMA.RamseyFinite

/-- Order-eleven bases that survive the contact inequalities. -/
def viable11 : List (List Nat) := [[3,128,144,3,2,6,3,2,2,1,0],[3,192,128,3,2,6,3,2,2,1,0],[3,4,9,3,2,6,3,2,2,1,0],[3,2,6,3,2,6,3,2,2,1,0]]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_1 : dualCheckSimple 25 [3,128,146,3,2,6,3,2,2,1,0] 3 14 54
    [((102,4),5),((270,4),5),((394,4),6),((401,4),6),((561,4),5),((612,4),10),((780,4),5),((785,4),5),((1074,4),4),((1097,4),3),((1161,4),9),((1170,4),11)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_2 : dualCheckSimple 25 [3,128,145,3,2,6,3,2,2,1,0] 3 14 54
    [((102,4),4),((278,4),5),((394,4),7),((401,4),5),((585,4),5),((612,4),10),((777,4),5),((788,4),5),((1098,4),4),((1121,4),4),((1161,4),7),((1162,4),5),((1169,4),5),((1170,4),6)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_3 : dualCheckSimple 25 [3,64,140,3,2,6,3,2,2,1,0] 3 9 35
    [((150,4),2),((393,4),3),((396,4),4),((401,4),2),((404,4),4),((534,4),3),((585,4),3),((609,4),3),((610,4),3),((780,4),3),((788,4),3),((1073,4),3),((1074,4),2),((1098,4),4),((1121,4),4),((1122,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_5 : dualCheckSimple 25 [3,192,144,3,2,6,3,2,2,1,0] 3 2 9
    [((54,4),1),((78,4),1),((393,4),1),((401,4),1),((609,4),1),((612,4),1),((780,4),1),((788,4),1),((1073,4),1),((1097,4),1),((1122,4),1),((1162,4),1),((1170,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_6 : dualCheckSimple 25 [3,192,136,3,2,6,3,2,2,1,0] 3 11 43
    [((54,4),4),((393,4),5),((396,4),4),((401,4),2),((404,4),7),((564,4),4),((585,4),4),((609,4),4),((780,4),6),((785,4),5),((1097,4),2),((1098,4),4),((1122,4),8),((1170,4),3)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_7 : dualCheckSimple 25 [3,192,132,3,2,6,3,2,2,1,0] 3 11 43
    [((78,4),4),((393,4),2),((396,4),7),((401,4),5),((404,4),4),((561,4),4),((588,4),4),((609,4),4),((777,4),5),((788,4),6),((1073,4),2),((1074,4),4),((1122,4),8),((1162,4),3)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_8 : dualCheckSimple 25 [3,192,130,3,2,6,3,2,2,1,0] 3 2 9
    [((102,4),1),((142,4),1),((388,3),1),((393,4),1),((401,4),1),((561,4),1),((585,4),1),((612,4),1),((780,4),1),((1074,4),1),((1098,4),1),((1121,4),1),((1170,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_9 : dualCheckSimple 25 [3,192,129,3,2,6,3,2,2,1,0] 3 2 9
    [((102,4),1),((150,4),1),((393,4),1),((561,4),1),((585,4),1),((612,4),1),((776,3),1),((788,4),1),((1074,4),1),((1098,4),1),((1121,4),1),((1162,4),1),((1169,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_10 : dualCheckSimple 25 [3,32,76,3,2,6,3,2,2,1,0] 3 12 50
    [((278,4),6),((393,4),6),((396,4),7),((404,4),7),((561,4),4),((562,4),2),((586,4),4),((609,4),6),((610,4),6),((1038,4),4),((1073,4),4),((1121,4),4),((1122,4),4),((1161,4),4),((1164,4),4),((1172,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_11 : dualCheckSimple 25 [3,16,50,3,2,6,3,2,2,1,0] 3 12 51
    [((393,4),4),((394,4),4),((401,4),7),((402,4),7),((550,4),6),((609,4),6),((612,4),7),((777,4),4),((778,4),4),((1038,4),4),((1062,4),3),((1097,4),4),((1100,4),4),((1124,4),7),((1169,4),4),((1170,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_12 : dualCheckSimple 25 [3,144,144,3,2,6,3,2,2,1,0] 3 11 43
    [((54,4),4),((270,4),3),((393,4),5),((394,4),4),((401,4),2),((402,4),7),((588,4),4),((612,4),8),((785,4),2),((1074,4),4),((1097,4),4),((1121,4),4),((1162,4),6),((1169,4),5)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_13 : dualCheckSimple 25 [3,8,49,3,2,6,3,2,2,1,0] 3 24 94
    [((393,4),14),((394,4),14),((402,4),8),((534,4),8),((564,4),8),((609,4),11),((612,4),14),((785,4),8),((1094,4),11),((1124,4),14),((1161,4),11),((1169,4),8),((1170,4),8)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_14 : dualCheckSimple 25 [3,136,144,3,2,6,3,2,2,1,0] 3 21 78
    [((78,4),7),((393,4),13),((402,4),12),((561,4),4),((564,4),8),((612,4),14),((777,4),4),((1073,4),7),((1098,4),7),((1121,4),7),((1162,4),9),((1169,4),4),((1170,4),7)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_15 : dualCheckSimple 25 [3,24,48,3,2,6,3,2,2,1,0] 3 12 48
    [((393,4),4),((394,4),6),((401,4),4),((402,4),6),((561,4),4),((585,4),4),((588,4),4),((612,4),6),((786,4),6),((1076,4),3),((1097,4),4),((1100,4),3),((1121,4),4),((1124,4),6),((1162,4),4),((1170,4),3)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_17 : dualCheckSimple 25 [3,4,137,3,2,6,3,2,2,1,0] 3 21 75
    [((393,4),5),((404,4),14),((550,4),13),((564,4),7),((585,4),13),((774,4),4),((1073,4),7),((1098,4),14),((1121,4),9),((1162,4),5),((1169,4),7)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_18 : dualCheckSimple 25 [3,4,73,3,2,6,3,2,2,1,0] 3 11 41
    [((393,4),3),((404,4),8),((561,4),4),((586,4),8),((609,4),5),((778,4),3),((785,4),4),((1062,4),7),((1076,4),4),((1097,4),7),((1158,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_19 : dualCheckSimple 25 [3,132,144,3,2,6,3,2,2,1,0] 3 2 9
    [((102,4),1),((270,4),1),((386,3),1),((401,4),1),((564,4),1),((588,4),1),((609,4),1),((777,4),1),((788,4),1),((1073,4),1),((1122,4),1),((1161,4),1),((1162,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_20 : dualCheckSimple 25 [3,132,129,3,2,6,3,2,2,1,0] 3 2 8
    [((102,4),1),((390,4),1),((564,4),1),((585,4),1),((777,4),1),((788,4),1),((1073,4),1),((1098,4),1),((1162,4),1),((1169,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_21 : dualCheckSimple 25 [3,68,136,3,2,6,3,2,2,1,0] 3 2 9
    [((142,4),1),((396,4),1),((401,4),1),((404,4),1),((564,4),1),((586,4),1),((609,4),1),((777,4),1),((788,4),1),((1097,4),1),((1122,4),2),((1169,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_22 : dualCheckSimple 25 [3,196,128,3,2,6,3,2,2,1,0] 3 10 38
    [((102,4),4),((142,4),8),((401,4),5),((564,4),3),((585,4),2),((777,4),6),((788,4),8),((1073,4),3),((1122,4),7),((1162,4),3),((1169,4),3)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_23 : dualCheckSimple 25 [3,36,72,3,2,6,3,2,2,1,0] 3 2 9
    [((270,4),1),((393,4),1),((404,4),2),((586,4),1),((609,4),1),((610,4),1),((785,4),1),((1076,4),1),((1097,4),1),((1122,4),1),((1164,4),1),((1169,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_24 : dualCheckSimple 25 [3,12,129,3,2,6,3,2,2,1,0] 3 2 9
    [((100,3),1),((390,4),1),((393,4),1),((404,4),1),((564,4),1),((582,4),1),((585,4),1),((778,4),1),((785,4),1),((1098,4),1),((1121,4),1),((1162,4),1),((1169,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_25 : dualCheckSimple 25 [3,12,65,3,2,6,3,2,2,1,0] 3 2 8
    [((390,4),1),((393,4),1),((404,4),1),((561,4),1),((586,4),1),((609,4),1),((778,4),1),((1076,4),1),((1124,4),1),((1161,4),1),((1162,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_26 : dualCheckSimple 25 [3,12,33,3,2,6,3,2,2,1,0] 3 11 43
    [((394,4),8),((401,4),4),((564,4),6),((609,4),5),((612,4),4),((777,4),2),((778,4),4),((785,4),4),((1073,4),5),((1098,4),3),((1121,4),2),((1124,4),7),((1158,4),4),((1172,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_27 : dualCheckSimple 25 [3,12,17,3,2,6,3,2,2,1,0] 3 11 43
    [((394,4),8),((401,4),4),((564,4),5),((586,4),3),((609,4),7),((612,4),2),((774,4),4),((788,4),4),((1076,4),4),((1121,4),3),((1124,4),6),((1161,4),2),((1162,4),4),((1169,4),6)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_28 : dualCheckSimple 25 [3,12,9,3,2,6,3,2,2,1,0] 3 2 9
    [((393,4),1),((394,4),1),((404,4),1),((561,4),1),((564,4),1),((586,4),1),((609,4),1),((774,4),1),((1076,4),1),((1098,4),1),((1121,4),1),((1158,4),1),((1169,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_30 : dualCheckSimple 25 [3,2,134,3,2,6,3,2,2,1,0] 3 11 43
    [((390,4),4),((396,4),8),((401,4),3),((561,4),2),((562,4),5),((582,4),4),((588,4),4),((609,4),5),((774,4),2),((1073,4),7),((1074,4),4),((1097,4),4),((1122,4),6),((1161,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_31 : dualCheckSimple 25 [3,2,70,3,2,6,3,2,2,1,0] 3 11 41
    [((390,4),3),((396,4),8),((562,4),8),((585,4),4),((609,4),5),((777,4),4),((786,4),3),((1073,4),7),((1094,4),7),((1100,4),4),((1158,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_32 : dualCheckSimple 25 [3,130,144,3,2,6,3,2,2,1,0] 3 2 9
    [((102,4),1),((278,4),1),((386,3),1),((393,4),1),((401,4),1),((564,4),1),((588,4),1),((609,4),1),((780,4),1),((1073,4),1),((1097,4),1),((1122,4),1),((1170,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_33 : dualCheckSimple 25 [3,130,130,3,2,6,3,2,2,1,0] 3 2 8
    [((102,4),1),((390,4),1),((561,4),1),((588,4),1),((780,4),1),((785,4),1),((1074,4),1),((1097,4),1),((1161,4),1),((1170,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_34 : dualCheckSimple 25 [3,66,132,3,2,6,3,2,2,1,0] 3 2 9
    [((150,4),1),((393,4),1),((396,4),1),((404,4),1),((562,4),1),((588,4),1),((609,4),1),((780,4),1),((785,4),1),((1073,4),1),((1122,4),2),((1161,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_35 : dualCheckSimple 25 [3,194,128,3,2,6,3,2,2,1,0] 3 11 43
    [((54,4),2),((102,4),4),((150,4),4),((393,4),3),((396,4),6),((401,4),2),((609,4),3),((777,4),4),((780,4),4),((785,4),5),((788,4),5),((1097,4),4),((1122,4),8),((1161,4),4),((1170,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_36 : dualCheckSimple 25 [3,34,68,3,2,6,3,2,2,1,0] 3 2 9
    [((278,4),1),((396,4),2),((401,4),1),((562,4),1),((609,4),1),((610,4),1),((777,4),1),((1100,4),1),((1122,4),1),((1161,4),1),((1169,4),1),((1172,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_37 : dualCheckSimple 25 [3,18,130,3,2,6,3,2,2,1,0] 3 2 9
    [((100,3),1),((390,4),1),((396,4),1),((401,4),1),((550,4),1),((561,4),1),((588,4),1),((777,4),1),((786,4),1),((1074,4),1),((1121,4),1),((1161,4),1),((1170,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_38 : dualCheckSimple 25 [3,18,66,3,2,6,3,2,2,1,0] 3 2 8
    [((390,4),1),((396,4),1),((401,4),1),((562,4),1),((585,4),1),((609,4),1),((786,4),1),((1100,4),1),((1124,4),1),((1169,4),1),((1170,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_39 : dualCheckSimple 25 [3,18,34,3,2,6,3,2,2,1,0] 3 14 54
    [((393,4),5),((402,4),10),((550,4),4),((588,4),7),((609,4),6),((612,4),5),((777,4),5),((786,4),4),((1074,4),4),((1097,4),5),((1121,4),5),((1124,4),7),((1158,4),5),((1164,4),5)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_40 : dualCheckSimple 25 [3,18,18,3,2,6,3,2,2,1,0] 3 11 43
    [((393,4),4),((402,4),8),((561,4),2),((562,4),3),((585,4),5),((612,4),7),((774,4),4),((780,4),4),((1100,4),6),((1121,4),5),((1124,4),4),((1161,4),4),((1169,4),2),((1170,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_41 : dualCheckSimple 25 [3,128,144,3,12,9,3,2,2,1,0] 3 11 43
    [((54,4),4),((294,4),4),((394,4),5),((417,4),6),((585,4),2),((593,4),4),((596,4),8),((777,4),4),((780,4),4),((1098,4),2),((1106,4),3),((1161,4),5),((1185,4),4),((1186,4),7)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_42 : dualCheckSimple 25 [3,64,136,3,12,9,3,2,2,1,0] 3 16 61
    [((54,4),5),((393,4),3),((417,4),6),((420,4),11),((534,4),5),((585,4),7),((594,4),7),((777,4),5),((780,4),5),((1098,4),10),((1105,4),13),((1106,4),3),((1186,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_43 : dualCheckSimple 25 [3,192,128,3,12,9,3,2,2,1,0] 3 32 69
    [((54,4),1),((396,4),1),((417,4),1),((420,4),1),((593,4),1),((596,4),1),((777,4),1),((780,4),1),((1073,4),1),((1098,4),1),((1106,4),1),((1161,4),1),((1186,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_44 : dualCheckSimple 25 [3,8,9,3,12,9,3,2,2,1,0] 3 10 38
    [((417,4),4),((420,4),7),((534,4),3),((585,4),8),((594,4),5),((774,4),3),((777,4),3),((1073,4),8),((1076,4),3),((1098,4),6),((1162,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_45 : dualCheckSimple 25 [3,4,17,3,12,9,3,2,2,1,0] 3 11 41
    [((294,4),4),((393,4),6),((417,4),4),((418,4),5),((593,4),4),((596,4),8),((774,4),4),((1073,4),6),((1076,4),4),((1098,4),2),((1105,4),2),((1162,4),7)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_3_46 : dualCheckSimple 25 [3,2,6,3,12,9,3,2,2,1,0] 3 2 9
    [((396,4),1),((417,4),1),((418,4),1),((588,4),1),((593,4),1),((594,4),1),((774,4),1),((777,4),1),((1073,4),1),((1074,4),1),((1100,4),1),((1161,4),1),((1186,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2500000 in
theorem prune11_3 {b : List Nat} (hb : b ∈ narrow11) :
    b ∈ viable11 ∨ ∃ (edgeWeight low : Nat) (W : List ((Nat × Nat) × Nat)),
      dualCheckSimple 25 b 3 edgeWeight low W = true := by
  simp only [narrow11, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inr ⟨_, _, _, cert11_3_1⟩
  · exact Or.inr ⟨_, _, _, cert11_3_2⟩
  · exact Or.inr ⟨_, _, _, cert11_3_3⟩
  · exact Or.inl (by decide)
  · exact Or.inr ⟨_, _, _, cert11_3_5⟩
  · exact Or.inr ⟨_, _, _, cert11_3_6⟩
  · exact Or.inr ⟨_, _, _, cert11_3_7⟩
  · exact Or.inr ⟨_, _, _, cert11_3_8⟩
  · exact Or.inr ⟨_, _, _, cert11_3_9⟩
  · exact Or.inr ⟨_, _, _, cert11_3_10⟩
  · exact Or.inr ⟨_, _, _, cert11_3_11⟩
  · exact Or.inr ⟨_, _, _, cert11_3_12⟩
  · exact Or.inr ⟨_, _, _, cert11_3_13⟩
  · exact Or.inr ⟨_, _, _, cert11_3_14⟩
  · exact Or.inr ⟨_, _, _, cert11_3_15⟩
  · exact Or.inl (by decide)
  · exact Or.inr ⟨_, _, _, cert11_3_17⟩
  · exact Or.inr ⟨_, _, _, cert11_3_18⟩
  · exact Or.inr ⟨_, _, _, cert11_3_19⟩
  · exact Or.inr ⟨_, _, _, cert11_3_20⟩
  · exact Or.inr ⟨_, _, _, cert11_3_21⟩
  · exact Or.inr ⟨_, _, _, cert11_3_22⟩
  · exact Or.inr ⟨_, _, _, cert11_3_23⟩
  · exact Or.inr ⟨_, _, _, cert11_3_24⟩
  · exact Or.inr ⟨_, _, _, cert11_3_25⟩
  · exact Or.inr ⟨_, _, _, cert11_3_26⟩
  · exact Or.inr ⟨_, _, _, cert11_3_27⟩
  · exact Or.inr ⟨_, _, _, cert11_3_28⟩
  · exact Or.inl (by decide)
  · exact Or.inr ⟨_, _, _, cert11_3_30⟩
  · exact Or.inr ⟨_, _, _, cert11_3_31⟩
  · exact Or.inr ⟨_, _, _, cert11_3_32⟩
  · exact Or.inr ⟨_, _, _, cert11_3_33⟩
  · exact Or.inr ⟨_, _, _, cert11_3_34⟩
  · exact Or.inr ⟨_, _, _, cert11_3_35⟩
  · exact Or.inr ⟨_, _, _, cert11_3_36⟩
  · exact Or.inr ⟨_, _, _, cert11_3_37⟩
  · exact Or.inr ⟨_, _, _, cert11_3_38⟩
  · exact Or.inr ⟨_, _, _, cert11_3_39⟩
  · exact Or.inr ⟨_, _, _, cert11_3_40⟩
  · exact Or.inr ⟨_, _, _, cert11_3_41⟩
  · exact Or.inr ⟨_, _, _, cert11_3_42⟩
  · exact Or.inr ⟨_, _, _, cert11_3_43⟩
  · exact Or.inr ⟨_, _, _, cert11_3_44⟩
  · exact Or.inr ⟨_, _, _, cert11_3_45⟩
  · exact Or.inr ⟨_, _, _, cert11_3_46⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_1 : dualCheckSimple 20 [3,128,146,3,2,6,3,2,2,1,0] 2 4 12
    [((102,4),2),((402,4),3),((612,4),2),((780,4),2),((785,4),2),((1161,4),2),((1162,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_2 : dualCheckSimple 20 [3,128,145,3,2,6,3,2,2,1,0] 2 4 12
    [((278,4),2),((585,4),2),((612,4),3),((788,4),2),((1073,4),2),((1122,4),2),((1162,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_3 : dualCheckSimple 20 [3,64,140,3,2,6,3,2,2,1,0] 2 3 7
    [((142,4),1),((401,4),1),((404,4),1),((609,4),1),((610,4),1),((1074,4),1),((1097,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_5 : dualCheckSimple 20 [3,192,144,3,2,6,3,2,2,1,0] 2 5 13
    [((78,4),2),((393,4),2),((401,4),2),((564,4),2),((609,4),2),((780,4),2),((1122,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_6 : dualCheckSimple 20 [3,192,136,3,2,6,3,2,2,1,0] 2 7 17
    [((393,4),2),((404,4),3),((609,4),4),((780,4),4),((1122,4),4),((1170,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_7 : dualCheckSimple 20 [3,192,132,3,2,6,3,2,2,1,0] 2 10 24
    [((78,4),4),((396,4),4),((609,4),7),((788,4),4),((1162,4),4),((1169,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_8 : dualCheckSimple 20 [3,192,130,3,2,6,3,2,2,1,0] 2 8 19
    [((102,4),3),((393,4),2),((396,4),3),((612,4),3),((785,4),3),((1074,4),2),((1098,4),2),((1169,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_9 : dualCheckSimple 20 [3,192,129,3,2,6,3,2,2,1,0] 2 6 15
    [((404,4),3),((609,4),2),((612,4),2),((788,4),2),((1074,4),2),((1097,4),2),((1162,4),3)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_10 : dualCheckSimple 20 [3,32,76,3,2,6,3,2,2,1,0] 2 7 18
    [((404,4),4),((562,4),2),((610,4),3),((778,4),2),((785,4),2),((1121,4),4),((1164,4),3)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_11 : dualCheckSimple 20 [3,16,50,3,2,6,3,2,2,1,0] 2 8 19
    [((394,4),3),((402,4),3),((612,4),4),((785,4),3),((1100,4),3),((1121,4),3),((1170,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_12 : dualCheckSimple 20 [3,144,144,3,2,6,3,2,2,1,0] 2 3 7
    [((278,4),1),((394,4),1),((612,4),2),((785,4),1),((1161,4),1),((1162,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_13 : dualCheckSimple 20 [3,8,49,3,2,6,3,2,2,1,0] 2 5 14
    [((394,4),3),((401,4),3),((609,4),2),((612,4),2),((786,4),1),((1076,4),2),((1124,4),2),((1161,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_14 : dualCheckSimple 20 [3,136,144,3,2,6,3,2,2,1,0] 2 11 24
    [((394,4),5),((612,4),7),((780,4),3),((1121,4),4),((1170,4),5)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_15 : dualCheckSimple 20 [3,24,48,3,2,6,3,2,2,1,0] 2 21 46
    [((393,4),7),((394,4),7),((402,4),7),((526,4),4),((612,4),11),((1121,4),11)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_17 : dualCheckSimple 20 [3,4,137,3,2,6,3,2,2,1,0] 2 9 20
    [((404,4),6),((564,4),3),((609,4),5),((778,4),2),((1098,4),5)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_18 : dualCheckSimple 20 [3,4,73,3,2,6,3,2,2,1,0] 2 9 20
    [((393,4),4),((404,4),3),((585,4),2),((610,4),5),((778,4),2),((1076,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_19 : dualCheckSimple 20 [3,132,144,3,2,6,3,2,2,1,0] 2 10 22
    [((393,4),4),((564,4),4),((588,4),4),((1122,4),7),((1169,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_20 : dualCheckSimple 20 [3,132,129,3,2,6,3,2,2,1,0] 2 5 13
    [((102,4),2),((394,4),2),((404,4),2),((564,4),2),((609,4),2),((777,4),2),((1098,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_21 : dualCheckSimple 20 [3,68,136,3,2,6,3,2,2,1,0] 2 6 13
    [((396,4),3),((586,4),2),((785,4),2),((1122,4),4),((1169,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_22 : dualCheckSimple 20 [3,196,128,3,2,6,3,2,2,1,0] 2 4 10
    [((142,4),2),((401,4),2),((564,4),1),((609,4),1),((777,4),2),((1122,4),3)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_23 : dualCheckSimple 20 [3,36,72,3,2,6,3,2,2,1,0] 2 5 13
    [((270,4),2),((586,4),2),((609,4),2),((785,4),2),((1076,4),2),((1122,4),2),((1164,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_24 : dualCheckSimple 20 [3,12,129,3,2,6,3,2,2,1,0] 2 10 22
    [((394,4),4),((404,4),4),((612,4),4),((1073,4),5),((1098,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_25 : dualCheckSimple 20 [3,12,65,3,2,6,3,2,2,1,0] 2 5 11
    [((390,4),1),((401,4),2),((561,4),2),((778,4),2),((1124,4),2),((1158,4),1),((1161,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_26 : dualCheckSimple 20 [3,12,33,3,2,6,3,2,2,1,0] 2 3 7
    [((401,4),1),((564,4),1),((582,4),1),((777,4),1),((1098,4),1),((1121,4),1),((1172,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_27 : dualCheckSimple 20 [3,12,17,3,2,6,3,2,2,1,0] 2 10 25
    [((394,4),7),((612,4),4),((788,4),4),((1073,4),4),((1094,4),4),((1161,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_28 : dualCheckSimple 20 [3,12,9,3,2,6,3,2,2,1,0] 2 13 33
    [((393,4),5),((404,4),5),((564,4),5),((609,4),9),((1098,4),9),((1172,4),5)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_30 : dualCheckSimple 20 [3,2,134,3,2,6,3,2,2,1,0] 2 6 12
    [((396,4),4),((562,4),2),((785,4),1),((1121,4),3),((1170,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_31 : dualCheckSimple 20 [3,2,70,3,2,6,3,2,2,1,0] 2 3 7
    [((401,4),1),((561,4),1),((610,4),1),((786,4),1),((1100,4),1),((1121,4),1),((1158,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_32 : dualCheckSimple 20 [3,130,144,3,2,6,3,2,2,1,0] 2 5 11
    [((393,4),2),((561,4),1),((612,4),2),((780,4),2),((1122,4),2),((1170,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_33 : dualCheckSimple 20 [3,130,130,3,2,6,3,2,2,1,0] 2 4 9
    [((102,4),1),((393,4),1),((402,4),1),((561,4),1),((588,4),1),((780,4),1),((1122,4),1),((1169,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_34 : dualCheckSimple 20 [3,66,132,3,2,6,3,2,2,1,0] 2 2 6
    [((396,4),1),((582,4),1),((610,4),1),((785,4),1),((1073,4),1),((1097,4),1),((1170,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_35 : dualCheckSimple 20 [3,194,128,3,2,6,3,2,2,1,0] 2 4 10
    [((393,4),2),((609,4),2),((788,4),2),((1122,4),3),((1170,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_36 : dualCheckSimple 20 [3,34,68,3,2,6,3,2,2,1,0] 2 4 9
    [((396,4),1),((401,4),1),((562,4),1),((585,4),1),((786,4),1),((1094,4),1),((1121,4),1),((1164,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_37 : dualCheckSimple 20 [3,18,130,3,2,6,3,2,2,1,0] 2 9 21
    [((393,4),2),((396,4),3),((401,4),2),((402,4),2),((612,4),5),((1074,4),3),((1097,4),5)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_38 : dualCheckSimple 20 [3,18,66,3,2,6,3,2,2,1,0] 2 7 16
    [((396,4),3),((402,4),3),((562,4),3),((585,4),4),((1124,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_39 : dualCheckSimple 20 [3,18,34,3,2,6,3,2,2,1,0] 2 8 19
    [((402,4),5),((562,4),2),((612,4),4),((777,4),4),((1074,4),2),((1100,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_40 : dualCheckSimple 20 [3,18,18,3,2,6,3,2,2,1,0] 2 10 22
    [((393,4),4),((402,4),7),((561,4),4),((1100,4),4),((1124,4),4)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_41 : dualCheckSimple 20 [3,128,144,3,12,9,3,2,2,1,0] 2 5 13
    [((294,4),2),((393,4),2),((593,4),2),((780,4),2),((1074,4),2),((1162,4),2),((1185,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_42 : dualCheckSimple 20 [3,64,136,3,12,9,3,2,2,1,0] 2 3 8
    [((420,4),2),((586,4),1),((594,4),1),((777,4),1),((780,4),1),((1105,4),2),((1185,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_43 : dualCheckSimple 20 [3,192,128,3,12,9,3,2,2,1,0] 2 4 10
    [((86,4),1),((420,4),2),((593,4),2),((780,4),2),((1106,4),2),((1186,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_44 : dualCheckSimple 20 [3,8,9,3,12,9,3,2,2,1,0] 2 3 8
    [((393,4),1),((420,4),2),((594,4),2),((1073,4),1),((1076,4),1),((1097,4),1),((1162,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_45 : dualCheckSimple 20 [3,4,17,3,12,9,3,2,2,1,0] 2 3 8
    [((393,4),1),((394,4),1),((593,4),1),((596,4),2),((778,4),1),((1076,4),1),((1185,4),2)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem cert11_2_46 : dualCheckSimple 20 [3,2,6,3,12,9,3,2,2,1,0] 2 4 9
    [((396,4),1),((418,4),1),((582,4),1),((593,4),1),((780,4),1),((1073,4),1),((1074,4),1),((1097,4),1),((1164,4),1)] = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2500000 in
theorem prune11_2 {b : List Nat} (hb : b ∈ narrow11) :
    b ∈ viable11 ∨ ∃ (edgeWeight low : Nat) (W : List ((Nat × Nat) × Nat)),
      dualCheckSimple 20 b 2 edgeWeight low W = true := by
  simp only [narrow11, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inr ⟨_, _, _, cert11_2_1⟩
  · exact Or.inr ⟨_, _, _, cert11_2_2⟩
  · exact Or.inr ⟨_, _, _, cert11_2_3⟩
  · exact Or.inl (by decide)
  · exact Or.inr ⟨_, _, _, cert11_2_5⟩
  · exact Or.inr ⟨_, _, _, cert11_2_6⟩
  · exact Or.inr ⟨_, _, _, cert11_2_7⟩
  · exact Or.inr ⟨_, _, _, cert11_2_8⟩
  · exact Or.inr ⟨_, _, _, cert11_2_9⟩
  · exact Or.inr ⟨_, _, _, cert11_2_10⟩
  · exact Or.inr ⟨_, _, _, cert11_2_11⟩
  · exact Or.inr ⟨_, _, _, cert11_2_12⟩
  · exact Or.inr ⟨_, _, _, cert11_2_13⟩
  · exact Or.inr ⟨_, _, _, cert11_2_14⟩
  · exact Or.inr ⟨_, _, _, cert11_2_15⟩
  · exact Or.inl (by decide)
  · exact Or.inr ⟨_, _, _, cert11_2_17⟩
  · exact Or.inr ⟨_, _, _, cert11_2_18⟩
  · exact Or.inr ⟨_, _, _, cert11_2_19⟩
  · exact Or.inr ⟨_, _, _, cert11_2_20⟩
  · exact Or.inr ⟨_, _, _, cert11_2_21⟩
  · exact Or.inr ⟨_, _, _, cert11_2_22⟩
  · exact Or.inr ⟨_, _, _, cert11_2_23⟩
  · exact Or.inr ⟨_, _, _, cert11_2_24⟩
  · exact Or.inr ⟨_, _, _, cert11_2_25⟩
  · exact Or.inr ⟨_, _, _, cert11_2_26⟩
  · exact Or.inr ⟨_, _, _, cert11_2_27⟩
  · exact Or.inr ⟨_, _, _, cert11_2_28⟩
  · exact Or.inl (by decide)
  · exact Or.inr ⟨_, _, _, cert11_2_30⟩
  · exact Or.inr ⟨_, _, _, cert11_2_31⟩
  · exact Or.inr ⟨_, _, _, cert11_2_32⟩
  · exact Or.inr ⟨_, _, _, cert11_2_33⟩
  · exact Or.inr ⟨_, _, _, cert11_2_34⟩
  · exact Or.inr ⟨_, _, _, cert11_2_35⟩
  · exact Or.inr ⟨_, _, _, cert11_2_36⟩
  · exact Or.inr ⟨_, _, _, cert11_2_37⟩
  · exact Or.inr ⟨_, _, _, cert11_2_38⟩
  · exact Or.inr ⟨_, _, _, cert11_2_39⟩
  · exact Or.inr ⟨_, _, _, cert11_2_40⟩
  · exact Or.inr ⟨_, _, _, cert11_2_41⟩
  · exact Or.inr ⟨_, _, _, cert11_2_42⟩
  · exact Or.inr ⟨_, _, _, cert11_2_43⟩
  · exact Or.inr ⟨_, _, _, cert11_2_44⟩
  · exact Or.inr ⟨_, _, _, cert11_2_45⟩
  · exact Or.inr ⟨_, _, _, cert11_2_46⟩

end OMA.RamseyFinite
namespace OMA.RamseyFinite
private def pair14_0base : List Nat := [3,128,144,3,2,6,3,2,2,1,0]
private def pair14_0ind : List (Nat × Nat) := [(0,0),(1024,1),(512,1),(256,1),(768,2),(128,1),(1152,2),(384,2),(64,1),(1088,2),(576,2),(32,1),(1056,2),(544,2),(96,2),(1120,3),(608,3),(16,1),(1040,2),(528,2),(272,2),(784,3),(144,2),(1168,3),(400,3),(48,2),(1072,3),(560,3),(8,1),(1032,2),(520,2),(264,2),(776,3),(136,2),(1160,3),(392,3),(72,2),(1096,3),(584,3),(4,1),(516,2),(260,2),(772,3),(68,2),(580,3),(36,2),(548,3),(100,3),(612,4),(20,2),(532,3),(276,3),(788,4),(52,3),(564,4),(12,2),(524,3),(268,3),(780,4),(76,3),(588,4),(2,1),(1026,2),(258,2),(130,2),(1154,3),(386,3),(66,2),(1090,3),(34,2),(1058,3),(98,3),(1122,4),(18,2),(1042,3),(274,3),(146,3),(1170,4),(402,4),(50,3),(1074,4),(10,2),(1034,3),(266,3),(138,3),(1162,4),(394,4),(74,3),(1098,4),(6,2),(262,3),(70,3),(38,3),(102,4),(22,3),(278,4),(54,4),(14,3),(270,4),(78,4),(1,1),(1025,2),(513,2),(257,2),(769,3),(129,2),(1153,3),(385,3),(65,2),(1089,3),(577,3),(33,2),(1057,3),(545,3),(97,3),(1121,4),(609,4),(17,2),(1041,3),(529,3),(273,3),(785,4),(145,3),(1169,4),(401,4),(49,3),(1073,4),(561,4),(9,2),(1033,3),(521,3),(265,3),(777,4),(137,3),(1161,4),(393,4),(73,3),(1097,4),(585,4)]
private def pair14_0use : List Nat := [1024,512,256,768,128,1152,384,64,1088,576,32,1056,544,96,1120,608,16,1040,528,272,784,144,1168,400,48,1072,560,8,1032,520,264,776,136,1160,392,72,1096,584,4,516,260,772,68,580,36,548,100,612,20,532,276,788,52,564,12,524,268,780,76,588,2,1026,258,130,1154,386,66,1090,34,1058,98,1122,18,1042,274,146,1170,402,50,1074,10,1034,266,138,1162,394,74,1098,6,262,70,38,102,22,278,54,14,270,78,1,1025,513,257,769,129,1153,385,65,1089,577,33,1057,545,97,1121,609,17,1041,529,273,785,145,1169,401,49,1073,561,9,1033,521,265,777,137,1161,393,73,1097,585]
private def pair14_0opt : List (Nat × Nat) := [(1024,500118995187709952982468170372289696329149),(512,341469937350401605530643813100049938177003),(256,645150112157138670036175890953694180540263),(768,295168938400467297244640272528837047671651),(128,620637818595955909332904621294151893253919),(1152,445647231717619907382406331282211550752029),(384,612467054075084642676138787499647293193991),(64,87112138275171663126913511232030682003711),(1088,64557460059732421315140102132662242257085),(576,80133016273356233262011843163361969051883),(32,696600376825581022905161561500543868602367),(1056,499906201881610965358781813997113471272381),(544,341342261366704578121443197799224684446699),(96,86814373030992655361655308754926597701887),(1120,64344770599580507910681783073259082350781),(608,80005402597231411798140603135733815181547),(16,696558171240521856131205030068556969148415),(1040,499874915696845297491430317478627101470141),(528,341303285390291420010271617613610375764971),(272,644835251275538080817242423026945867513703),(784,295024883316325069715374962949633309989731),(144,620334920766277770464464808021535708282655),(1168,445429736786670950586615873159326200851741),(400,612168143929433472674353756435365327142663),(48,696558007683155956994808869111477642987519),(1072,499874798870151125174385771399601794844093),(560,341303215294268974500772770557308696527851),(8,340282365811127636093400605481370648575),(1032,244198179741892333740225524945966034365),(520,166723327590515849510621053791067626475),(264,315026841167470638427537817822806671207),(776,144126279220838287242240812197991603043),(136,303063697975415011494534782615742840607),(1160,217613417002097601883892794327660457245),(392,299075983523593799313738179451823324935),(72,340134709856833644013588436068775901439),(1096,244092711199573942152409553865044273341),(584,166660046460173048379772804010985527531),(4,696898287452814941542780303466442585538559),(516,341469937349134573900434457774537531907051),(260,645150112156229403077318912406882054307687),(772,295168938399558030285784538471957401099107),(68,87112138274550836197211317012566967728383),(580,80133016272735406332310032951632790427883),(36,696600376824408074717936385396980836075519),(548,341342261365531629934219540557725726802923),(100,86814373030456008354624547521306904363263),(612,80005402596694764791110207825081403834603),(20,696558171239393473785394135571374025080831),(532,341303285389163037664462236700835693255659),(276,644835251274727849061528303612573295705959),(788,295024883315514837959662068884894801517411),(52,696558007682042429929469399705359069743103),(564,341303215293155447435434814383754663953387),(12,340282365653290281084478592184469159935),(524,166723327432678494501723059325674904555),(268,315026841050485304715040115594087104359),(780,144126279103852953529762620803106921315),(76,340134709711375689397520674121609787647),(588,166660046314715093763728761828165425387),(2,696898287452814322572765272461773807550463),(1026,500118995186442656773752198466389879254461),(258,645150112156228871490055851662899265142631),(130,620637818594688394661404667864048201629471),(1154,445647231716352708265637480896585875025181),(386,612467054074174902385187021121016862605063),(66,87112138274550681462235559776717119568127),(1090,64557460059111484551944766596818629437629),(34,696600376824407457570164493420273059366911),(1058,499906201880437753200465919851214103250365),(98,86814373030455855434808380011326054727935),(1122,64344770599043751675211059013781902983357),(18,696558171239392857223785975364377240535039),(1042,499874915695716651596590201429098642894269),(274,644835251274727319542661733655047485652839),(146,620334920765148906956866677364339513622303),(1170,445429736785542401405933560000500266528029),(402,612168143928622769428267748797888459833095),(50,696558007682041813376715676125977288640511),(1074,499874798869037334562968558965165654017469),(10,340282365653287863235181234182596591615),(1034,244198179584053946052630334515850210749),(266,315026841050483226959133110541852082023),(138,303063697817575767670488701233199578911),(1162,217613416844259592077849953837709487389),(394,299075983406606614574264882134967648007),(74,340134709711373279074494449592490146047),(1098,244092711054114957366425360208418711741),(6,696898287452814322572762966619314349670399),(262,645150112156228871490053984928000545652583),(70,87112138274550681462234983765115316091135),(38,696600376824407457570162215127176947042303),(102,86814373030455855434807831126875131740415),(22,696558171239392857223783704987764848197631),(278,644835251274727319542659895630596390649703),(54,696558007682041813376713406277130477635583),(14,340282365653287863235145205935333441535),(270,315026841050483226959103844291099754343),(78,340134709711373279074458869945971128575),(1,1267650600228229401496703205375),(1025,1267296208718277748753799278013),(513,1267650600226692172910014421995),(257,909798546121906026202568589159),(769,909798546120661535994002463587),(129,1267514671502259273052746415903),(1153,1267199116771156228436687285533),(385,909740290953633114012301393671),(65,620981664678527466984085272831),(1089,620936763195911547496343152829),(577,620981664678143459244044065003),(33,1173565334999346373916442363903),(1057,1173212158318172439389836805565),(545,1173565334997827511572118242283),(97,536799926847477628119950426367),(1121,536756235471272943978861428925),(609,536799926847111705147297104107),(17,1128998907421325081341608460287),(1041,1128645894842386426535182691773),(529,1128998907419811496653100211179),(273,810761274582527396858162184039),(785,810761274581302046948147125091),(145,1128863507600401034297944964895),(1169,1128549180684583535789708766493),(401,810703246087845662410877828871),(49,1114143618095462834896652732415),(1073,1113790611419482283677283517885),(561,1114143618093949602051865445355),(9,157839772858255399546305642495),(1033,157838387687631218677571612093),(521,157839772858231380714659961835),(265,116987411468433973531955429223),(777,116987411468414462697985727331),(137,157839243824082109630045486879),(1161,157838009806078868737385786653),(393,116987184739502563567843933959),(73,145460364939129566123073091839),(1097,145458984786019773303337134269),(585,145460364939105846358590232811)]
private def pair14_0lim : List Nat := [0,593742344229402307699423618385576942632960,696557835953414379060387876585318977208320,696898287452814322572760660775205355779792,696898287454081973172991196020261297061886,696898287454081973172991196020261297061887]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_0i : inds pair14_0base = pair14_0ind := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_0u : usable 6 2 pair14_0base = pair14_0use := by rw [usable,pair14_0i]; decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_0t : tagged 6 2 pair14_0base = pair14_0opt := by rw [tagged,pair14_0u,pair14_0i]; decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_0l : cells 6 pair14_0ind [] 6 1 = pair14_0lim := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_0v : universal pair14_0ind = 696898287454081973172991196020261297061887 := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pairScan14_0 : (cutCatalog 2 20 pair14_0base).all (fun g => decide (normalizeFinal g = final14)) = true := by
  rw [cutCatalog,pair14_0t,pair14_0i,pair14_0l,pair14_0v]
  decide +kernel

private def pair14_1base : List Nat := [3,192,128,3,2,6,3,2,2,1,0]
private def pair14_1ind : List (Nat × Nat) := [(0,0),(1024,1),(512,1),(256,1),(768,2),(128,1),(1152,2),(384,2),(64,1),(1088,2),(576,2),(32,1),(1056,2),(544,2),(96,2),(1120,3),(608,3),(16,1),(1040,2),(528,2),(272,2),(784,3),(144,2),(1168,3),(400,3),(48,2),(1072,3),(560,3),(8,1),(1032,2),(520,2),(264,2),(776,3),(136,2),(1160,3),(392,3),(72,2),(1096,3),(584,3),(4,1),(516,2),(260,2),(772,3),(132,2),(388,3),(68,2),(580,3),(36,2),(548,3),(100,3),(612,4),(20,2),(532,3),(276,3),(788,4),(148,3),(404,4),(52,3),(564,4),(12,2),(524,3),(268,3),(780,4),(140,3),(396,4),(76,3),(588,4),(2,1),(1026,2),(130,2),(1154,3),(66,2),(1090,3),(34,2),(1058,3),(98,3),(1122,4),(18,2),(1042,3),(146,3),(1170,4),(50,3),(1074,4),(10,2),(1034,3),(138,3),(1162,4),(74,3),(1098,4),(6,2),(134,3),(70,3),(38,3),(102,4),(22,3),(150,4),(54,4),(14,3),(142,4),(78,4),(1,1),(1025,2),(513,2),(257,2),(769,3),(129,2),(1153,3),(385,3),(65,2),(1089,3),(577,3),(33,2),(1057,3),(545,3),(97,3),(1121,4),(609,4),(17,2),(1041,3),(529,3),(273,3),(785,4),(145,3),(1169,4),(401,4),(49,3),(1073,4),(561,4),(9,2),(1033,3),(521,3),(265,3),(777,4),(137,3),(1161,4),(393,4),(73,3),(1097,4),(585,4)]
private def pair14_1use : List Nat := [1024,512,256,768,128,1152,384,64,1088,576,32,1056,544,96,1120,608,16,1040,528,272,784,144,1168,400,48,1072,560,8,1032,520,264,776,136,1160,392,72,1096,584,4,516,260,772,132,388,68,580,36,548,100,612,20,532,276,788,148,404,52,564,12,524,268,780,140,396,76,588,2,1026,130,1154,66,1090,34,1058,98,1122,18,1042,146,1170,50,1074,10,1034,138,1162,74,1098,6,134,70,38,102,22,150,54,14,142,78,1,1025,513,257,769,129,1153,385,65,1089,577,33,1057,545,97,1121,609,17,1041,529,273,785,145,1169,401,49,1073,561,9,1033,521,265,777,137,1161,393,73,1097,585]
private def pair14_1opt : List (Nat × Nat) := [(1024,500118995187709894727396742866512186666429),(512,341469937350401605530565486512922896554987),(256,645150112157496522090256750952465084448615),(768,295168938400825149298647142906922067745635),(128,620637818595598162718211038436779293146911),(1152,445647231717262142257221338882565551648029),(384,612467054075084670441986886244086217441031),(64,87112138275171663013910485072940646676735),(1088,64557460059732363022328364288529667860669),(576,80133016273356233149003125369136611727595),(32,696600376825581017332178408996740603447295),(1056,499906201881610905246049064385226068329917),(544,341342261366704572548381989979803182564331),(96,86814373030992649781922377223237709725951),(1120,64344770599580447795626473011176348975293),(608,80005402597231406218402250395993479971051),(16,696558171240521849019320568123765853126655),(1040,499874915696845237092403968006925240593853),(528,341303285390291412898309116186168462990315),(272,644835251275856311338171394469306789134183),(784,295024883316643300236230218364985710533475),(144,620334920765959632103627686815103319146271),(1168,445429736786352797625406790226686649658653),(400,612168143929433494575022273065188851842823),(48,696558007683155949750107848252681011333119),(1072,499874798870151064731087234567700266091965),(560,341303215294268967255993711271392430785515),(8,340282365811134889503590615631240626175),(1032,244198179741894524815051073002013420989),(520,166723327590523102920522851156971936747),(264,315026841208330253227450150605948976999),(776,144126279261697902041878442996050352995),(136,303063697934568957482755567810957541151),(1160,217613416961247544490539412799572634909),(392,299075983523599804386511482514402443015),(72,340134709856840784529703369313957591295),(1096,244092711199576095595875845751373965501),(584,166660046460180188895600421673689815275),(4,696898287452814941542635035356862122819583),(516,341469937349134573900289189664957069188075),(260,645150112156229490459926053665548318801767),(772,295168938399558117668391679730623665593187),(132,620637818594688895759236130901715866091295),(388,612467054074175403483018923266245265456903),(68,87112138274550836084171975171884049119487),(580,80133016272735406219270691110949871818987),(36,696600376824408069144808371690860315543551),(548,341342261365531624361091526851605206270955),(100,86814373030456002774855705948650945249535),(612,80005402596694759211341366252425444720875),(20,696558171239393466673364944260107870535679),(532,341303285389163030552433045389569538710507),(276,644835251274727928992241134902939412987751),(788,295024883315514917890374900175260918799203),(148,620334920765149400347796075824593254874911),(404,612168143928623262819197579610303498419975),(52,696558007682042422684623651063384143562751),(564,341303215293155440190589065741779737773035),(12,340282365653297534494128170379054678015),(524,166723327432685747911372637520260422635),(268,315026841050492898218086808734820990823),(780,144126279103860547032809313943840807779),(140,303063697817583623769818784409778650911),(396,299075983406614470673601727308057542407),(76,340134709711382829913096521213739415807),(588,166660046314722234279304608920295053547),(2,696898287452814322572910540571354270269439),(1026,500118995186442656773897466575970341973437),(130,620637818594688394661522157744738764062495),(1154,445647231716352708265754970777276437458205),(66,87112138274550681462271875458310002850047),(1090,64557460059111484551981082278411512719549),(34,696600376824407457570309354622590314743807),(1058,499906201880437753200610781053531358627261),(98,86814373030455855434844290052293125865727),(1122,64344770599043751675246969054748974121149),(18,696558171239392857223930704730852279058431),(1042,499874915695716651596734930795573681417661),(146,620334920765148906956983736588315708751647),(1170,445429736785542401406050619224476461657373),(50,696558007682041813376860403909155583166463),(1074,499874798869037334563113286748343948543421),(10,340282365653287863235721666137881051135),(1034,244198179584053946053170766471134670269),(138,303063697817575767670921020409148079903),(1162,217613416844259592078282273013657988381),(74,340134709711373279075033535745542207743),(1098,244092711054114957366964446361470773437),(6,696898287452814322572762966619314349670399),(134,620637818594688394661402362021588743749407),(70,87112138274550681462234983765115316091135),(38,696600376824407457570162215127176947042303),(102,86814373030455855434807831126875131740415),(22,696558171239392857223783704987764848197631),(150,620334920765148906956864406987727121284895),(54,696558007682041813376713406277130477635583),(14,340282365653287863235145205935333441535),(142,303063697817575767670452672985936428831),(78,340134709711373279074458869945971128575),(1,1267650600228229401496703205375),(1025,1267237953646850242976289615293),(513,1267650600148365585782972799979),(257,1267650600202766024973472497511),(769,1267650600127531914079022537571),(129,909768056808676415680146308895),(1153,909433991586163828790688181533),(385,909768056801731858451225640711),(65,620981551675501307894049945855),(1089,620878470384173703363768756413),(577,620981551669425665018686740715),(33,1173559762016193870113177208831),(1057,1173152045585422827502433863101),(545,1173559761936619692150616359915),(97,536794347114546096431062450431),(1121,536696120415962881896128053437),(609,536794347108758965406961893611),(17,1128991795536863136550492438527),(1041,1128585495816036954833321815485),(529,1128991795457310069211187436523),(273,1128991795511498839219083804519),(785,1128991795436557462300547668835),(145,810725146763279827865555828511),(1169,810396219475500603150157573405),(401,810725146756362292234402529031),(49,1114136373394441976100021078015),(1073,1113730168120945451775754765757),(561,1114136373314890316135599703019),(9,157847026268445409696175620095),(1033,157840578762456766733618998717),(521,157847026268133178080564272107),(265,157847026268346306315097735015),(777,157847026268052093496044477283),(137,116993189812302894825260187423),(1161,116987952412725487209297964317),(393,116993189812275866630423052039),(73,145467505455244499368254781695),(1097,145461138229486065189666826429),(585,145467505454933464021294520555)]
private def pair14_1lim : List Nat := [0,593742344229402273467084744946820497539072,696557835953414371653094945682696679030784,696898287452814322572615392665624893060816,696898287454081973172991196020261297061886,696898287454081973172991196020261297061887]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_1i : inds pair14_1base = pair14_1ind := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_1u : usable 6 2 pair14_1base = pair14_1use := by rw [usable,pair14_1i]; decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_1t : tagged 6 2 pair14_1base = pair14_1opt := by rw [tagged,pair14_1u,pair14_1i]; decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_1l : cells 6 pair14_1ind [] 6 1 = pair14_1lim := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_1v : universal pair14_1ind = 696898287454081973172991196020261297061887 := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pairScan14_1 : (cutCatalog 2 20 pair14_1base).all (fun g => decide (normalizeFinal g = final14)) = true := by
  rw [cutCatalog,pair14_1t,pair14_1i,pair14_1l,pair14_1v]
  decide +kernel

private def pair14_2base : List Nat := [3,4,9,3,2,6,3,2,2,1,0]
private def pair14_2ind : List (Nat × Nat) := [(0,0),(1024,1),(512,1),(256,1),(768,2),(128,1),(1152,2),(384,2),(64,1),(1088,2),(576,2),(32,1),(1056,2),(544,2),(96,2),(1120,3),(608,3),(16,1),(1040,2),(528,2),(272,2),(784,3),(144,2),(1168,3),(400,3),(48,2),(1072,3),(560,3),(8,1),(1032,2),(520,2),(264,2),(776,3),(136,2),(1160,3),(392,3),(72,2),(1096,3),(584,3),(4,1),(1028,2),(516,2),(260,2),(772,3),(132,2),(1156,3),(388,3),(36,2),(1060,3),(548,3),(20,2),(1044,3),(532,3),(276,3),(788,4),(148,3),(1172,4),(404,4),(52,3),(1076,4),(564,4),(2,1),(1026,2),(514,2),(258,2),(770,3),(130,2),(1154,3),(386,3),(66,2),(1090,3),(578,3),(34,2),(1058,3),(546,3),(98,3),(1122,4),(610,4),(10,2),(1034,3),(522,3),(266,3),(778,4),(138,3),(1162,4),(394,4),(74,3),(1098,4),(586,4),(6,2),(1030,3),(518,3),(262,3),(774,4),(134,3),(1158,4),(390,4),(38,3),(1062,4),(550,4),(1,1),(1025,2),(513,2),(257,2),(769,3),(129,2),(1153,3),(385,3),(65,2),(1089,3),(577,3),(33,2),(1057,3),(545,3),(97,3),(1121,4),(609,4),(17,2),(1041,3),(529,3),(273,3),(785,4),(145,3),(1169,4),(401,4),(49,3),(1073,4),(561,4),(9,2),(1033,3),(521,3),(265,3),(777,4),(137,3),(1161,4),(393,4),(73,3),(1097,4),(585,4)]
private def pair14_2use : List Nat := [1024,512,256,768,128,1152,384,64,1088,576,32,1056,544,96,1120,608,16,1040,528,272,784,144,1168,400,48,1072,560,8,1032,520,264,776,136,1160,392,72,1096,584,4,1028,516,260,772,132,1156,388,36,1060,548,20,1044,532,276,788,148,1172,404,52,1076,564,2,1026,514,258,770,130,1154,386,66,1090,578,34,1058,546,98,1122,610,10,1034,522,266,778,138,1162,394,74,1098,586,6,1030,518,262,774,134,1158,390,38,1062,550,1,1025,513,257,769,129,1153,385,65,1089,577,33,1057,545,97,1121,609,17,1041,529,273,785,145,1169,401,49,1073,561,9,1033,521,265,777,137,1161,393,73,1097,585]
private def pair14_2opt : List (Nat × Nat) := [(1024,500118995187352367926507687772631632407997),(512,341469937349755085128085792908270164696043),(256,645150112157402392707764720714397315497831),(768,295168938400094407869725262371444496980835),(128,620637818595817328276867969253724903178015),(1152,445647231717163335857848240082248493919517),(384,612467054075288973466569052100167432404743),(64,87112138275817790195111432098980923586815),(1088,64557460060020808656593570686002794211517),(576,80133016273356149566137322656292861778155),(32,696600376824565913597679636783231150196735),(1056,499906201880555182515570859746181527504317),(544,341342261365676773881523696092400101753835),(96,86814373030613769859425994756548126966015),(1120,64344770599160794131103972584265082339517),(608,80005402596840140850843563795250234654955),(16,696558171240660507824009629671602488737791),(1040,499874915696626362749344072254224309775805),(528,341303285389783551300519348820480821877739),(272,644835251275900840760368497836669693722471),(784,295024883316051217611998336126067268442979),(144,620334920766277840572327961704333106609951),(1168,445429736786353028998142880849031893970205),(400,612168143929736840509647782993554244239111),(48,696558007682200269404230540828708435920895),(1072,499874798869154763878073294509299986335165),(560,341303215293300591977756882173526227813355),(8,340282366920319795675186820402124947455),(1032,244198180493321120803135982405387251133),(520,166723328053503136171793285671850269675),(264,315026842223431716062797200116352548711),(776,144126279640498012308076256995106544483),(136,303063698945958415193770537875723517727),(1160,217613417654491563316410066315100515613),(392,299075984520133981570761650462180507399),(72,340134710978404942929906771201691105535),(1096,244092711963381940270793090119363078333),(584,166660046935539627852387550300235765995),(4,696898287452814941542780303466442585538559),(1028,500118995186443100967650921206163783249341),(516,341469937349134258198383044871396609416171),(260,645150112156229444520539688281819661205351),(772,295168938399557760862694073390418203433827),(132,620637818594688945931057291615419328626463),(1156,445647231716353104102134484169718599740701),(388,612467054074175446401229826059952551100167),(36,696600376824408076242670463553517534447615),(1060,499906201880438197181858178411217318184381),(548,341342261365531315926907399194428730377195),(20,696558171239393476193801041834893084065791),(1044,499874915695717095790488959634719612431805),(532,341303285389162724370817730061213829749739),(276,644835251274727892573145598984415506202471),(788,295024883315514570604968123300260207450979),(148,620334920765149458226519336581557706161951),(1172,445429736785542797242430598739480056786205),(404,612168143928623313444310582447271772815111),(52,696558007682042432049221654703471065040895),(1076,499874798869037778544360825969418170271165),(564,341303215293155134023140849862032964453355),(2,696898287452814322572765272461773807550463),(1026,500118995186442656773751547378484863790525),(514,341469937349133954930418250756420940520427),(258,645150112156228871490056119550111279742823),(770,295168938399557498698520587624933415639907),(130,620637818594688394661404415539323766570783),(1154,445647231716352708265636649576734834519325),(386,612467054074174902385187180869061262180103),(66,87112138274550681462237289607574773971199),(1090,64557460059111484551945845339771268376765),(578,80133016272735251597334829533192783272171),(34,696600376824407457570162502371840924452863),(1058,499906201880437753200463854457104233006525),(546,341342261365531012786445635003592562050027),(98,86814373030455855434808118371539109150975),(1122,64344770599043751675210723028317222076605),(610,80005402596694611871293756146320355492075),(10,340282365653287863237451048394791321599),(1034,244198179584053946054249060823029476797),(522,166723327432676076653519502088183667691),(266,315026841050483226961238466401833844583),(778,144126279103850875774802981357642767203),(138,303063697817575767672506190720959250207),(1162,217613416844259592079288448198863711517),(394,299075983406606614576262098827334385415),(74,340134709711373279076764712405429008639),(1098,244092711054114957368044535116342110397),(586,166660046314712683441796786664171247851),(6,696898287452814322572762966619314349670399),(1030,500118995186442656773749892623930421374397),(518,341469937349133954930417120927409296038891),(262,645150112156228871490053984928000545652583),(774,295168938399557498698519610993075892444003),(134,620637818594688394661402362021588743749407),(1158,445647231716352708265635175054126417145117),(390,612467054074174902385185154386118143115015),(38,696600376824407457570162215127176947042303),(1062,499906201880437753200463641558117990925757),(550,341342261365531012786445370287921837769707),(1,1267650600228229401496703205375),(1025,909711152757795149095735356861),(513,621130197668671981130240941035),(257,1173521217710735786905703546727),(769,536909171205651378601451772771),(129,1128933615465607232625756339999),(1153,810627592213065028473630453021),(385,1114071081383897714532440604423),(65,1267108732876448333934326855935),(1089,909324104649380100836895107261),(577,620897968803622952174936791275),(33,158456027517421656603723958271),(1057,117429315107218188457893037501),(545,145761095078325804747535549419),(97,157914424618163629741479690495),(1121,117042455893462454984861417661),(609,145528979550072364663716577515),(17,1267650600225924684387128049663),(1041,909711152756141202132390997437),(529,621130197667542703523546323947),(273,1173521217708602206581988392807),(785,536909171204675223382105578339),(145,1128933615463554717095343292191),(1169,810627592211591225495401884957),(401,1114071081381872220599794925319),(49,158456027517134552127445665791),(1073,117429315107005393375475008957),(561,145761095078061218269396730859),(9,1267031932440041614467059941375),(1033,909267174750541676136992828861),(521,620827059519403612595442605035),(265,1172948489103693355825501306727),(777,536647136534249907495100668771),(137,1128382647523317864890026163999),(1161,810231971238596140724825845021),(393,1113527366996526034578201116423),(73,1267031663855447901255988295935),(1097,909266982904403309557655939261),(585,620826944411720592647840471275)]
private def pair14_2lim : List Nat := [0,593742344229402407808871188357269489188864,696557835953414381180804249717184326107136,696898287452814322572760660775205355779792,696898287454081973172991196020261297061886,696898287454081973172991196020261297061887]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_2i : inds pair14_2base = pair14_2ind := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_2u : usable 6 2 pair14_2base = pair14_2use := by rw [usable,pair14_2i]; decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_2t : tagged 6 2 pair14_2base = pair14_2opt := by rw [tagged,pair14_2u,pair14_2i]; decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_2l : cells 6 pair14_2ind [] 6 1 = pair14_2lim := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_2v : universal pair14_2ind = 696898287454081973172991196020261297061887 := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pairScan14_2 : (cutCatalog 2 20 pair14_2base).all (fun g => decide (normalizeFinal g = final14)) = true := by
  rw [cutCatalog,pair14_2t,pair14_2i,pair14_2l,pair14_2v]
  decide +kernel

private def pair14_3base : List Nat := [3,2,6,3,2,6,3,2,2,1,0]
private def pair14_3ind : List (Nat × Nat) := [(0,0),(1024,1),(512,1),(256,1),(768,2),(128,1),(1152,2),(384,2),(64,1),(1088,2),(576,2),(32,1),(1056,2),(544,2),(96,2),(1120,3),(608,3),(16,1),(1040,2),(528,2),(272,2),(784,3),(144,2),(1168,3),(400,3),(48,2),(1072,3),(560,3),(8,1),(1032,2),(520,2),(264,2),(776,3),(136,2),(1160,3),(392,3),(72,2),(1096,3),(584,3),(4,1),(1028,2),(516,2),(260,2),(772,3),(132,2),(1156,3),(388,3),(68,2),(1092,3),(580,3),(12,2),(1036,3),(524,3),(268,3),(780,4),(140,3),(1164,4),(396,4),(76,3),(1100,4),(588,4),(2,1),(1026,2),(514,2),(258,2),(770,3),(130,2),(1154,3),(386,3),(66,2),(1090,3),(578,3),(34,2),(1058,3),(546,3),(98,3),(1122,4),(610,4),(18,2),(1042,3),(530,3),(274,3),(786,4),(146,3),(1170,4),(402,4),(50,3),(1074,4),(562,4),(6,2),(1030,3),(518,3),(262,3),(774,4),(134,3),(1158,4),(390,4),(70,3),(1094,4),(582,4),(1,1),(1025,2),(513,2),(257,2),(769,3),(129,2),(1153,3),(385,3),(65,2),(1089,3),(577,3),(33,2),(1057,3),(545,3),(97,3),(1121,4),(609,4),(17,2),(1041,3),(529,3),(273,3),(785,4),(145,3),(1169,4),(401,4),(49,3),(1073,4),(561,4),(9,2),(1033,3),(521,3),(265,3),(777,4),(137,3),(1161,4),(393,4),(73,3),(1097,4),(585,4)]
private def pair14_3use : List Nat := [1024,512,256,768,128,1152,384,64,1088,576,32,1056,544,96,1120,608,16,1040,528,272,784,144,1168,400,48,1072,560,8,1032,520,264,776,136,1160,392,72,1096,584,4,1028,516,260,772,132,1156,388,68,1092,580,12,1036,524,268,780,140,1164,396,76,1100,588,2,1026,514,258,770,130,1154,386,66,1090,578,34,1058,546,98,1122,610,18,1042,530,274,786,146,1170,402,50,1074,562,6,1030,518,262,774,134,1158,390,70,1094,582,1,1025,513,257,769,129,1153,385,65,1089,577,33,1057,545,97,1121,609,17,1041,529,273,785,145,1169,401,49,1073,561,9,1033,521,265,777,137,1161,393,73,1097,585]
private def pair14_3opt : List (Nat × Nat) := [(1024,500118995187352367926507687772631632407997),(512,341469937349755085128085792908270164696043),(256,645150112157402392707764720714397315497831),(768,295168938400094407869725262371444496980835),(128,620637818595817328276867969253724903178015),(1152,445647231717163335857848240082248493919517),(384,612467054075288973466569052100167432404743),(64,87112138274709137518676900128746096179455),(1088,64557460059228913887711762135835060349117),(576,80133016272881012704808237526192221460715),(32,696600376825674566274114168753465977604095),(1056,499906201881347077284452668296349261366717),(544,341342261366151910742852781222500742071275),(96,86814373030613769859425994756548126966015),(1120,64344770599160794131103972584265082339517),(608,80005402596840140850843563795250234654955),(16,696558171240659889156223746602231639703551),(1040,499874915696625918771338472728623050747325),(528,341303285389783248162371209729821827455979),(272,644835251275900268031763588986421643444071),(784,295024883316050955577327910810412883434339),(144,620334920766277289604387724852616908373791),(1168,445429736786352633377169885764612528368925),(400,612168143929736296795262436808015330017031),(48,696558007683308845011644359470809620678655),(1072,499874798869946601525210339063321608586685),(560,341303215293775657814694329530640962159595),(8,340282366920938463461069889772973981695),(1032,244198180493765098808735508006646279613),(520,166723328053806274319932376330844691435),(264,315026842224004444667706050364402827111),(776,144126279640760046978501572649491553123),(136,303063698946509383134007389591921753887),(1160,217613417654887184289405150734466116893),(392,299075984520677695956107836001094729479),(72,340134709869829335516088129100506347775),(1096,244092711171544293133748536097740826813),(584,166660046460473790914940193185501419755),(4,696898287452814941542780303466442585538559),(1028,500118995186443100967650921206163783249341),(516,341469937349134258198383044871396609416171),(260,645150112156229444520539688281819661205351),(772,295168938399557760862694073390418203433827),(132,620637818594688945931057291615419328626463),(1156,445647231716353104102134484169718599740701),(388,612467054074175446401229826059952551100167),(68,87112138274551300163667726899032480430335),(1092,64557460059111928553999080800870851029181),(580,80133016272735554750191940628220850084075),(12,340282365653906833252482053063569309695),(1036,244198179584498139953622888501948935613),(524,166723327432979344618313617063852563435),(268,315026841051056257444807198110215307111),(780,144126279104113039948288746842430561123),(140,303063697818127037325382266816521305887),(1164,217613416844655428577123041182628932893),(396,299075983407150630618907289718623305479),(76,340134709711991980507202003863135467775),(1100,244092711054558959421279996215924762813),(588,166660046315015836298907881692238059755),(2,696898287452814322572765272461773807550463),(1026,500118995186442656773751547378484863790525),(514,341469937349133954930418250756420940520427),(258,645150112156228871490056119550111279742823),(770,295168938399557498698520587624933415639907),(130,620637818594688394661404415539323766570783),(1154,445647231716352708265636649576734834519325),(386,612467054074174902385187180869061262180103),(66,87112138274550681462235271009779293501695),(1090,64557460059111484551944403484203068041405),(578,80133016272735251597333964419851863070955),(34,696600376824407457570164520969636404922367),(1058,499906201880437753200465296312672433341885),(546,341342261365531012786446500116933482251243),(98,86814373030455855434808118371539109150975),(1122,64344770599043751675210723028317222076605),(610,80005402596694611871293756146320355492075),(18,696558171239392857223786010830224306077695),(1042,499874915695716651596589585807040692972989),(530,341303285389162421102852935946238160853995),(274,644835251274727319542662030252707124739943),(786,295024883315514308440794637534775419657059),(146,620334920765148906956866460505462144106271),(1170,445429736785542401405932764146496291564829),(402,612168143928622769428267937256380483895047),(50,696558007682041813376715712119589935515647),(1074,499874798869037334562967943870873285428669),(562,341303215293154830882679950784537716327403),(6,696898287452814322572762966619314349670399),(1030,500118995186442656773749892623930421374397),(518,341469937349133954930417120927409296038891),(262,645150112156228871490053984928000545652583),(774,295168938399557498698519610993075892444003),(134,620637818594688394661402362021588743749407),(1158,445647231716352708265635175054126417145117),(390,612467054074174902385185154386118143115015),(70,87112138274550681462234983765115316091135),(1094,64557460059111484551944190585216825960637),(582,80133016272735251597333699704181138790635),(1,1267650600228229401496703205375),(1025,909711152757795149095735356861),(513,621130197668671981130240941035),(257,1173521217710735786905703546727),(769,536909171205651378601451772771),(129,1128933615465607232625756339999),(1153,810627592213065028473630453021),(385,1114071081383897714532440604423),(65,158456056441916363699499448575),(1089,117429335767571550669161244861),(577,145761107474537822074296473835),(33,1267108703951953626838551365631),(1057,909324083989026738625626899901),(545,620897956407410934848175866859),(97,157914424618163629741479690495),(1121,117042455893462454984861417661),(609,145528979550072364663716577515),(17,1267031932440041615016279015423),(1041,909267174750541676531131968957),(529,620827059519403612864551902187),(273,1172948489103693356333938114407),(785,536647136534249907727720569699),(145,1128382647523317865379145056031),(1169,810231971238596141076036283677),(401,1113527366996526035060880703239),(49,1267031634930953194228630423551),(1073,909266962244049947397097260477),(561,620826932015508575384131077099),(9,1267650600225924683837908975615),(1033,909711152756141201738251857341),(521,621130197667542703254437026795),(265,1173521217708602206073551585127),(777,536909171204675223149485677411),(137,1128933615463554716606224400159),(1161,810627592211591225144191446301),(393,1114071081381872220117115338503),(73,158456056441629259154803538175),(1097,117429335767358755536033687741),(585,145761107474273235533106125035)]
private def pair14_3lim : List Nat := [0,593742344229402407808871188357269489188864,696557835953414381180804249717184326107136,696898287452814322572760660775205355779792,696898287454081973172991196020261297061886,696898287454081973172991196020261297061887]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_3i : inds pair14_3base = pair14_3ind := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_3u : usable 6 2 pair14_3base = pair14_3use := by rw [usable,pair14_3i]; decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_3t : tagged 6 2 pair14_3base = pair14_3opt := by rw [tagged,pair14_3u,pair14_3i]; decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_3l : cells 6 pair14_3ind [] 6 1 = pair14_3lim := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair14_3v : universal pair14_3ind = 696898287454081973172991196020261297061887 := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pairScan14_3 : (cutCatalog 2 20 pair14_3base).all (fun g => decide (normalizeFinal g = final14)) = true := by
  rw [cutCatalog,pair14_3t,pair14_3i,pair14_3l,pair14_3v]
  decide +kernel

private theorem scan14_surviving {b g : List Nat} (hb : b ∈ viable11) (hg : g ∈ cutCatalog 2 20 b) : normalizeFinal g = final14 := by
  simp only [viable11,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · exact of_decide_eq_true (List.all_eq_true.mp pairScan14_0 _ hg)
  · exact of_decide_eq_true (List.all_eq_true.mp pairScan14_1 _ hg)
  · exact of_decide_eq_true (List.all_eq_true.mp pairScan14_2 _ hg)
  · exact of_decide_eq_true (List.all_eq_true.mp pairScan14_3 _ hg)

private def pair15_0base : List Nat := [7,24,130,145,3,2,6,3,2,2,1,0]
private def pair15_0ind : List (Nat × Nat) := [(0,0),(2048,1),(1024,1),(512,1),(1536,2),(256,1),(2304,2),(768,2),(128,1),(2176,2),(1152,2),(64,1),(2112,2),(1088,2),(192,2),(2240,3),(1216,3),(32,1),(2080,2),(1056,2),(544,2),(1568,3),(288,2),(2336,3),(800,3),(96,2),(2144,3),(1120,3),(16,1),(2064,2),(1040,2),(528,2),(1552,3),(272,2),(2320,3),(784,3),(144,2),(2192,3),(1168,3),(8,1),(1032,2),(520,2),(1544,3),(136,2),(1160,3),(72,2),(1096,3),(200,3),(1224,4),(40,2),(1064,3),(552,3),(1576,4),(104,3),(1128,4),(4,1),(2052,2),(516,2),(260,2),(2308,3),(772,3),(132,2),(2180,3),(68,2),(2116,3),(196,3),(2244,4),(36,2),(2084,3),(548,3),(292,3),(2340,4),(804,4),(100,3),(2148,4),(12,2),(524,3),(140,3),(76,3),(204,4),(44,3),(556,4),(108,4),(2,1),(2050,2),(1026,2),(514,2),(1538,3),(258,2),(2306,3),(770,3),(130,2),(2178,3),(1154,3),(18,2),(2066,3),(1042,3),(530,3),(1554,4),(274,3),(2322,4),(786,4),(146,3),(2194,4),(1170,4),(10,2),(1034,3),(522,3),(1546,4),(138,3),(1162,4),(6,2),(2054,3),(518,3),(262,3),(2310,4),(774,4),(134,3),(2182,4),(14,3),(526,4),(142,4),(1,1),(2049,2),(1025,2),(513,2),(1537,3),(257,2),(2305,3),(769,3),(129,2),(2177,3),(1153,3),(65,2),(2113,3),(1089,3),(193,3),(2241,4),(1217,4),(33,2),(2081,3),(1057,3),(545,3),(1569,4),(289,3),(2337,4),(801,4),(97,3),(2145,4),(1121,4),(17,2),(2065,3),(1041,3),(529,3),(1553,4),(273,3),(2321,4),(785,4),(145,3),(2193,4),(1169,4)]
private def pair15_0use : List Nat := [2048,1024,512,1536,256,2304,768,128,2176,1152,64,2112,1088,192,2240,1216,32,2080,1056,544,1568,288,2336,800,96,2144,1120,16,2064,1040,528,1552,272,2320,784,144,2192,1168,8,1032,520,1544,136,1160,72,1096,200,1224,40,1064,552,1576,104,1128,4,2052,516,260,2308,772,132,2180,68,2116,196,2244,36,2084,548,292,2340,804,100,2148,12,524,140,76,204,44,556,108,2,2050,1026,514,1538,258,2306,770,130,2178,1154,18,2066,1042,530,1554,274,2322,786,146,2194,1170,10,1034,522,1546,138,1162,6,2054,518,262,2310,774,134,2182,14,526,142,1,2049,1025,513,1537,257,2305,769,129,2177,1153,65,2113,1089,193,2241,1217,33,2081,1057,545,1569,289,2337,801,97,2145,1121,17,2065,1041,529,1553,273,2321,785,145,2193,1169]
private def pair15_0opt : List (Nat × Nat) := [(2048,2097651101991415043935173312760813778602009783741),(1024,1432228724108537131272553844056048793543329111019),(512,2705955696021213113460147294216460210723695361895),(1536,1238028259008909948299690483064814177242508090211),(256,2603143685088147435714055756818849331888546381599),(2304,1869179966581659043439949092322444701871067852061),(768,2568873014775359513163012761953438764685130202887),(128,365374790015659034330057856442123720940358351103),(2176,270773612957882816992807712112910181866936084669),(1152,336102230686956163541456627364342121979262146795),(64,2921753746921436408899495552175868951999962548223),(2112,2096758582176865452858118744881952597619888489917),(1088,1431693212219807376626318783591642581438962205675),(192,364125872061291129143910874126313845326400585983),(2240,269881528704762884716986981853350231222597058749),(1216,335566980135084204175962111345224829967214706923),(32,2921576723867387330608276052342181885817737314303),(2080,2096627358407144997516573710127526414230415830461),(1056,1431529735126220687053452833774333436741514484715),(544,2704635073766487628120978398952179414832882253671),(1568,1237424048193687259228943422750061350263625669475),(288,2601873239510118644276952902020515061946868956959),(2336,1868267726723381650137057174183478682894081289501),(800,2567619294756229619693268477385750776031081529095),(96,2921576037858135617996332803346257484082738890751),(2144,2096626868400536631365185416127609613562455000509),(1120,1431529441122255667362619494585957148247216620523),(16,1427247692705919336046119294674731090778783743),(2064,1024241406359949564008540275927441632407547325),(1040,699288324459350704631266246422519901047938027),(528,1321318343419101320353390976936991828258848615),(1552,604509432842714249452322585306720365281991523),(272,1271141285182536436565368636447839515786084127),(2320,912736829557533207236575520051090507412761885),(784,1254415597337651506290212123411181153261977351),(144,1426628375639259609399573948150939505880086783),(2192,1023799036456395729260985087965649744911018173),(1168,699022901055586838104876830680931245527275755),(8,2923003274657150982838502766139268214923722751999),(1032,1432228724103883981426093651503090599555803569131),(520,2705955696017887974664898291845666085299047890791),(1544,1238028259005586188708294529007628391064782953315),(136,365374790013664583864083495033631917352878487807),(1160,336102230684962118723674338989282517101154015467),(72,2921753746916781555330634395280241846463745624063),(1096,1431693212215154226779864333436336740061131703275),(200,364125872059296678677941650652582531063793713407),(1224,335566980133090159358184960904907629646725906667),(40,2921576723862732477039417615529656829680883466239),(1064,1431529735121567537207001103702124367107233733611),(552,2704635073763162489325735441210512073001732800359),(1576,1237424048190363499637553513321983207380982225763),(104,2921576037853480764427475273228097666683347404799),(1128,1431529441117602517516168671208112965506677343211),(4,2923003274656491520572649597948244188082529632255),(2052,2097651101986479765771126309336665656430780181949),(516,2705955696017321486964668268225818000582272614247),(260,2603143685082978504191374672774285292211370196767),(2308,1869179966576827611213072791355266445094237728029),(772,2568873014771530194229836157436978473780347141895),(132,365374790013501634985327719852183664092321298687),(2180,270773612955772148319804410536519239998669203645),(68,2921753746916122093064781255561739748029899868159),(2116,2096758582171930174694077493346297470860803048893),(196,364125872059133729799185903832976163980791644415),(2244,269881528702652216043988827665648989304467882173),(36,2921576723862073014773564484969955247360110100479),(2084,2096627358402209719352535185269676426738138181053),(548,2704635073762596001625505449909330894976467468135),(292,2601873239504949712754280309823904890019521888031),(2340,1868267726718550217910189345879640457209146600733),(804,2567619294752400300760097946275309313259072519943),(100,2921576037852821302161622142806746137149814343679),(2148,2096626868395601353201147798010241197226332259773),(12,2923003274656488964989039537837734742481604444159),(524,2705955696017319418158888695755405491711889112935),(140,365374790013501026513039610302035366028263700735),(76,2921753746916119537481171195451257851792320235519),(204,364125872059133121326897794282854993067614535935),(44,2921576723862070459189954424859481267606250455039),(556,2704635073762593932819725877438947096553708453735),(108,2921576037852818746578012082696272685161536030719),(2,2923003274656488924424239673347507728104141357055),(2050,2097651101986477181076775919393733021197261303229),(1026,1432228724103221943700477923379719588686830427115),(514,2705955696017319380606226561880405647875321626471),(1538,1238028259005017615021202771148793914680800631651),(258,2603143685082975912481908235774942195297575501599),(2306,1869179966576825029689396321127614783478285692189),(770,2568873014771528089773798802920734705243936259847),(130,365374790013501021459786957055991216193201387775),(2178,270773612955771536102166620493552546084462143677),(1154,336102230684798556715712041714078124812803643627),(18,1427247687389047897928293884391183379171639295),(2066,1024241401422115802153830272424665456674827709),(1042,699288319144182999017096021875966625694800875),(530,1321318339525406000774649773612363921331584871),(1554,604509428950398143668835636081631204225768291),(274,1271141280011049312652913468512561182470569759),(2322,912736824723545384099987118225649601888349469),(786,1254415593506263749942343881092954408459697927),(146,1426628373481251789924034846369956347149957375),(2194,1023799034345118582150572267597965257388730557),(1170,699022898897984667014838893446767699775854827),(10,2923003274656488924424230039719846645780642267135),(1034,1432228724103221943700468289752082525194840103915),(522,2705955696017319380606219421662254282721006190439),(1546,1238028259005017615021195630930662060360320080739),(138,365374790013501021459778079006967841613680621823),(1162,336102230684798556715703163665078469997628889323),(6,2923003274656488924424230001940986839867762671615),(2054,2097651101986477181076766269630503135786955402685),(518,2705955696017319380606219389197347044732649340775),(262,2603143685082975912481898572634580264716137922335),(2310,1869179966576825029689386677268784153535794867485),(774,2568873014771528089773791633780315655381953019655),(134,365374790013501021459778041345705580569955285247),(2182,270773612955771536102157726348159250974023231677),(14,2923003274656488924424230001940950811620499521535),(526,2705955696017319380606219389197317778481897013095),(142,365374790013501021459778041345670000923436267775),(1,5316911983139663491615228241121378303),(2049,4937862858407043130346671456841854397),(1025,5315187572085592082862102778004036587),(513,3893732853927905019142432750732050279),(1537,3892333278494884599088621354144422755),(257,5171523232157184184305095909268520735),(2305,4834013750562415053696576934089813277),(769,3831423389221128173152376037080825607),(129,2158012870279815096453720085641443583),(2177,2111280890649985764786510590358726845),(1153,2157606825753501360561492735091415275),(65,5316911983133892621395031618268039167),(2113,4937862858401291241826126681184273853),(1089,5315187572079821212660272397515359211),(193,2158012870274648799824217432097947903),(2241,2111280890644838376069683489172750525),(1217,2157606825748335063950074848935805163),(33,5316911983131163379484549622079291391),(2081,4937862858398564564013070930631814589),(1057,5315187572077091970755068057142483947),(545,3893732853921828071320032017851219815),(1569,3892333278488807651285360919814658915),(289,5171523232148692336315762312134917919),(2337,4834013750553942390321079994957262109),(801,3831423389215054767104837456446488327),(97,5316911983130256546768730331795163135),(2145,4937862858397657823530972008895481277),(1121,5315187572076185138039600610579317739),(17,5316871438127496816840464195517415423),(2065,4937833761864359766768689833494408637),(1041,5315167705623841631079450927617727467),(529,3893695319585913886412497300600389479),(1553,3892316105790659632293447720759647075),(273,5171487123922118308333237162255318815),(2321,4833987823146232260692099095450053917),(785,3831387756355037382766542857773776647),(145,2158007819484454812102198428763568383),(2193,2111277147119306965796559244672772285),(1169,2157602171098953647531659051302000875)]
private def pair15_0lim : List Nat := [0,2490335889370675805335505151976736006813272506368,2921575317570749713347003348213475796969007972352,2923003274656488924424220330534357864690302711504,2923003274661805836407369665432566039311865085950,2923003274661805836407369665432566039311865085951]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair15_0i : inds pair15_0base = pair15_0ind := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair15_0u : usable 6 2 pair15_0base = pair15_0use := by rw [usable,pair15_0i]; decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair15_0t : tagged 6 2 pair15_0base = pair15_0opt := by rw [tagged,pair15_0u,pair15_0i]; decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair15_0l : cells 6 pair15_0ind [] 6 1 = pair15_0lim := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair15_0v : universal pair15_0ind = 2923003274661805836407369665432566039311865085951 := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pairScan15_0 : (cutCatalog 2 25 pair15_0base).all (fun g => decide (normalizeFinal g = final15)) = true := by
  rw [cutCatalog,pair15_0t,pair15_0i,pair15_0l,pair15_0v]
  decide +kernel

private def pair15_1base : List Nat := [7,24,146,145,3,2,6,3,2,2,1,0]
private def pair15_1ind : List (Nat × Nat) := [(0,0),(2048,1),(1024,1),(512,1),(1536,2),(256,1),(2304,2),(768,2),(128,1),(2176,2),(1152,2),(64,1),(2112,2),(1088,2),(192,2),(2240,3),(1216,3),(32,1),(2080,2),(1056,2),(544,2),(1568,3),(288,2),(2336,3),(800,3),(96,2),(2144,3),(1120,3),(16,1),(2064,2),(1040,2),(528,2),(1552,3),(272,2),(2320,3),(784,3),(144,2),(2192,3),(1168,3),(8,1),(1032,2),(520,2),(1544,3),(136,2),(1160,3),(72,2),(1096,3),(200,3),(1224,4),(40,2),(1064,3),(552,3),(1576,4),(104,3),(1128,4),(4,1),(2052,2),(516,2),(260,2),(2308,3),(772,3),(68,2),(2116,3),(36,2),(2084,3),(548,3),(292,3),(2340,4),(804,4),(100,3),(2148,4),(12,2),(524,3),(76,3),(44,3),(556,4),(108,4),(2,1),(2050,2),(1026,2),(514,2),(1538,3),(258,2),(2306,3),(770,3),(130,2),(2178,3),(1154,3),(18,2),(2066,3),(1042,3),(530,3),(1554,4),(274,3),(2322,4),(786,4),(146,3),(2194,4),(1170,4),(10,2),(1034,3),(522,3),(1546,4),(138,3),(1162,4),(6,2),(2054,3),(518,3),(262,3),(2310,4),(774,4),(14,3),(526,4),(1,1),(2049,2),(1025,2),(513,2),(1537,3),(257,2),(2305,3),(769,3),(129,2),(2177,3),(1153,3),(65,2),(2113,3),(1089,3),(193,3),(2241,4),(1217,4),(33,2),(2081,3),(1057,3),(545,3),(1569,4),(289,3),(2337,4),(801,4),(97,3),(2145,4),(1121,4),(17,2),(2065,3),(1041,3),(529,3),(1553,4),(273,3),(2321,4),(785,4),(145,3),(2193,4),(1169,4)]
private def pair15_1use : List Nat := [2048,1024,512,1536,256,2304,768,128,2176,1152,64,2112,1088,192,2240,1216,32,2080,1056,544,1568,288,2336,800,96,2144,1120,16,2064,1040,528,1552,272,2320,784,144,2192,1168,8,1032,520,1544,136,1160,72,1096,200,1224,40,1064,552,1576,104,1128,4,2052,516,260,2308,772,68,2116,36,2084,548,292,2340,804,100,2148,12,524,76,44,556,108,2,2050,1026,514,1538,258,2306,770,130,2178,1154,18,2066,1042,530,1554,274,2322,786,146,2194,1170,10,1034,522,1546,138,1162,6,2054,518,262,2310,774,14,526,1,2049,1025,513,1537,257,2305,769,129,2177,1153,65,2113,1089,193,2241,1217,33,2081,1057,545,1569,289,2337,801,97,2145,1121,17,2065,1041,529,1553,273,2321,785,145,2193,1169]
private def pair15_1opt : List (Nat × Nat) := [(2048,4096974808576992492292215396416676378661580221),(1024,2797321726774463008584326844106779849429277675),(512,5285069718787551225645258864446942315040210791),(1536,2418023943372877471370868329091754204380715875),(256,5084265009935800223549176176389471343080374047),(2304,3650742122228392991803667038267741234053999901),(768,5017330106978391525352129849557581228275662599),(128,713622636755472797773356181310197620478458111),(2176,528854712813864709502536905352235854589470909),(1152,656449669316594451874361210136404740751628523),(64,5706550286955930486131751741145191747451488255),(2112,4095231605814200322219768832459647938524218813),(1088,2796275805116787706540823482457264537787040747),(192,711183343875847982956586166468957046052880639),(2240,527112360756989841776248999832148206337786045),(1216,655404258082469531238553043548941314250113259),(32,5706204538803490880094171188255473632047923199),(2080,4094975309388965057880771375578869094156430781),(1056,2795956513918376203468777206948551898177788907),(544,5282490378446290512092110017645765600024330087),(1568,2416843844124395656779480878695477218801408867),(288,5081783670916212740273467187004057357811580703),(2336,3648960403755194958008839946113571755416186141),(800,5014881435066028452168951159966587196780183303),(96,5706203198941671128898961849566934336947619839),(2144,4094974352344808092741333437798449178222790077),(1120,2795955939691882024385110660853231168276923371),(16,2787593149815694376876860490724816074047487),(2064,2000471496806363294239701045714646090870205),(1040,1365797508685821800821314864387325420821483),(528,2580699885609282519891987164455941165809511),(1552,1180682482120920083431346187313209051372387),(272,2482697820633910980551470697665190271385375),(2320,1782689118819375154007279764957770517540125),(784,2450030458817089635752534396001815821811463),(144,2786383552309106218227656926538504205121791),(2192,1999607498578679291088704926700274292762813),(1168,1365279109757324362772177861267908107573483),(8,5708990770816011147951285692548799013798805503),(1032,2797321726766661252965073451699048579973176299),(520,5285069718784922752125579377507808083174227815),(1544,2418023943370270547911392722071956250304109411),(136,713622636747674845105903473567100610367338751),(1160,656449669308802837459909643564034978502547691),(72,5706550286948102109849978558520251232678709247),(1096,2796275805108985950921655092655408043059971051),(200,711183343868050030289218461349678840436097279),(1224,655404258074677916824186479582305589241708779),(40,5706204538795662503812445229303278297447268351),(1064,2795956513910574447849656040814162927809518571),(552,5282490378443662038572524978064999208687107943),(1576,2416843844121788733320099719014906806837238627),(104,5706203198933842752617245335348232507218724863),(1128,2795955939684080268765998939451983859059524587),(4,5708990770813495495335130410190344415747244031),(2052,4096974808567378630139934740816824095490141629),(516,5285069718783859827097285979375136729939836775),(260,5084265009927727824526772214395764002370092831),(2308,3650742122220401722419678886677838085935033629),(772,5017330106975673682465132466891745124206771975),(68,5706550286945586457233825053939207375039629311),(2116,4095231605804586460067573772058140676885972413),(36,5706204538793146851196292298869227250297995263),(2084,4094975309379351195728623951588089178221538749),(548,5282490378442599113544233599822093479024131943),(292,5081783670908140341251197286722905701267668767),(2340,3648960403747203688624984657197859500342734109),(804,5014881435063310609282050023187955672296849159),(100,5706203198931327100001092411831182722129201151),(2148,4094974352335194230589195460846478010792019389),(12,5708990770813455564341223220928169022333124607),(524,5285069718783827502006980159496132313255772007),(76,5706550286945546526239917864704581344971065343),(44,5706204538793106920202385109642517703949418495),(556,5282490378442566788453927779971799509964554087),(108,5706203198931287169007185222605000941361956863),(2,5708990770813454930516225338268371381519384575),(2050,4096974808567338244290708884226935996492246461),(1026,2797321726764105358790128170338562972155567083),(514,5285069718783826915246630525609925230155792231),(1538,2418023943369175029338380934317773061475457891),(258,5084265009927687329066358746877849282455535391),(2306,3650742122220361386112232747519420211446639901),(770,5017330106975640800339544843585415759128428295),(130,713622636745119182538780102730264467285620991),(2178,528854712804241281449676573128160028969806013),(1154,656449669306247181085508783679417018507204843),(18,2787593139431734175773425254471331689267199),(2066,2000471487152569926212616411880220624907709),(1042,1365797498328482420087491905274379102510059),(530,2580699881885558595357259776344089741492071),(1554,1180682478418746374447466519506650531289955),(274,2482697812521580688906945498103414922411807),(2322,1782689110788174578450845157331708648582429),(786,2450030456066921386700197023614982555696903),(146,2786383541955569902329082789597875831453951),(2194,1999607488955309730895228936842437656717501),(1170,1365279099410126302897059420371336186697963),(10,5708990770813454930516076583688132740432003071),(1034,2797321726764105358789979415782343162576952299),(522,5285069718783826915246524272334794412386156391),(1546,2418023943369175029338274681062153077540707171),(138,713622636745119182538631348150474426942372095),(1162,656449669306247181085360029123346742509967595),(6,5708990770813454930516074222576948349891510271),(2054,4096974808567338244290559120408034710430379453),(518,5285069718783826915246522244555278044789473127),(262,5084265009927687329066208149712872947757088543),(2310,3650742122220361386112083354076552280334363933),(774,5017330106975640800339436784756388586731863815),(14,5708990770813454930516074222540920102628360191),(526,5285069718783826915246522244526011794037145447),(1,10384593717069655257060992658440191),(2049,9654248001656276044670310018674109),(1025,10357649794349789471649594028252139),(513,3724310398736619920931029936766823),(1537,3702442032595675838383978036255587),(257,8112894482968026712627132183346975),(2305,8031605691583684227217552536464669),(769,2750725012693064830459375447441159),(129,10353615234727194306935900059089151),(2177,9623428053010096078556809127405757),(1153,10347270789003542160270699259107563),(65,10384593716982874827859871705991167),(2113,9654248001570680818775924972062141),(1089,10357649794263009060814715440464875),(193,10353615234640413878156991571820799),(2241,9623428052924500853084636545941693),(1217,10347270788916761749576558159724779),(33,10384593716935077000205397290778623),(2081,9654248001523044400132095524040125),(1057,10357649794215211238437896841124843),(545,3724310398640152644087117963722599),(1569,3702442032499208580680364614277987),(289,8112894482833964964605600712490783),(2337,8031605691450821517560812253834525),(801,2750725012596818914544348001599239),(97,10384593716925625349182864777807871),(2145,9654248001513597360795581438494141),(1121,10357649794205759587767208049116139),(17,10383960201254550963704763544240127),(2065,9653793368176848488763958983617981),(1041,10357339380884938662545393832090603),(529,3723723924643008472025287791476583),(1553,3702173709092160732209160917539683),(273,8112330291795122400566357549645599),(2321,8031200575705828086522240416050461),(785,2750168249160396230680256650936071),(145,10353536316049689863943306788878591),(2193,9623369560343239844338769409484989),(1169,10347198060026234144179485853227243)]
private def pair15_1lim : List Nat := [0,4863937283925582375325759515957535172225662976,5706201792130334484756055684216778945445593088,5708990770813454930515923106777438377182361296,5708990770823839524233143877797980545530986494,5708990770823839524233143877797980545530986495]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair15_1i : inds pair15_1base = pair15_1ind := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair15_1u : usable 6 2 pair15_1base = pair15_1use := by rw [usable,pair15_1i]; decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair15_1t : tagged 6 2 pair15_1base = pair15_1opt := by rw [tagged,pair15_1u,pair15_1i]; decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair15_1l : cells 6 pair15_1ind [] 6 1 = pair15_1lim := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair15_1v : universal pair15_1ind = 5708990770823839524233143877797980545530986495 := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pairScan15_1 : (cutCatalog 2 25 pair15_1base).all (fun g => decide (normalizeFinal g = final15)) = true := by
  rw [cutCatalog,pair15_1t,pair15_1i,pair15_1l,pair15_1v]
  decide +kernel

private def pair15_2base : List Nat := [7,24,194,145,3,2,6,3,2,2,1,0]
private def pair15_2ind : List (Nat × Nat) := [(0,0),(2048,1),(1024,1),(512,1),(1536,2),(256,1),(2304,2),(768,2),(128,1),(2176,2),(1152,2),(64,1),(2112,2),(1088,2),(192,2),(2240,3),(1216,3),(32,1),(2080,2),(1056,2),(544,2),(1568,3),(288,2),(2336,3),(800,3),(96,2),(2144,3),(1120,3),(16,1),(2064,2),(1040,2),(528,2),(1552,3),(272,2),(2320,3),(784,3),(144,2),(2192,3),(1168,3),(8,1),(1032,2),(520,2),(1544,3),(136,2),(1160,3),(72,2),(1096,3),(200,3),(1224,4),(40,2),(1064,3),(552,3),(1576,4),(104,3),(1128,4),(4,1),(2052,2),(260,2),(2308,3),(132,2),(2180,3),(68,2),(2116,3),(196,3),(2244,4),(36,2),(2084,3),(292,3),(2340,4),(100,3),(2148,4),(12,2),(140,3),(76,3),(204,4),(44,3),(108,4),(2,1),(2050,2),(1026,2),(514,2),(1538,3),(258,2),(2306,3),(770,3),(130,2),(2178,3),(1154,3),(18,2),(2066,3),(1042,3),(530,3),(1554,4),(274,3),(2322,4),(786,4),(146,3),(2194,4),(1170,4),(10,2),(1034,3),(522,3),(1546,4),(138,3),(1162,4),(6,2),(2054,3),(262,3),(2310,4),(134,3),(2182,4),(14,3),(142,4),(1,1),(2049,2),(1025,2),(513,2),(1537,3),(257,2),(2305,3),(769,3),(129,2),(2177,3),(1153,3),(65,2),(2113,3),(1089,3),(193,3),(2241,4),(1217,4),(33,2),(2081,3),(1057,3),(545,3),(1569,4),(289,3),(2337,4),(801,4),(97,3),(2145,4),(1121,4),(17,2),(2065,3),(1041,3),(529,3),(1553,4),(273,3),(2321,4),(785,4),(145,3),(2193,4),(1169,4)]
private def pair15_2use : List Nat := [2048,1024,512,1536,256,2304,768,128,2176,1152,64,2112,1088,192,2240,1216,32,2080,1056,544,1568,288,2336,800,96,2144,1120,16,2064,1040,528,1552,272,2320,784,144,2192,1168,8,1032,520,1544,136,1160,72,1096,200,1224,40,1064,552,1576,104,1128,4,2052,260,2308,132,2180,68,2116,196,2244,36,2084,292,2340,100,2148,12,140,76,204,44,108,2,2050,1026,514,1538,258,2306,770,130,2178,1154,18,2066,1042,530,1554,274,2322,786,146,2194,1170,10,1034,522,1546,138,1162,6,2054,262,2310,134,2182,14,142,1,2049,1025,513,1537,257,2305,769,129,2177,1153,65,2113,1089,193,2241,1217,33,2081,1057,545,1569,289,2337,801,97,2145,1121,17,2065,1041,529,1553,273,2321,785,145,2193,1169]
private def pair15_2opt : List (Nat × Nat) := [(2048,4096974808576018936631239894010706897630096829),(1024,2797321726774463008584326844106779849429277675),(512,5285069718794203855995299446982772859723579239),(1536,2418023943379530101720908911627584749064084323),(256,5084265009937585075594297598759022064866164511),(2304,3650742122228879769634154678790261532312431901),(768,5017330106985530933532657851255003186702843655),(128,713622636748333389592847152089055472325114111),(2176,528854712807049819875686100231922427803347133),(1152,656449669309455043693852180915262592598284523),(64,5706550286955930486131732824009144158306306047),(2112,4095231605813226766558774431364374942057104829),(1088,2796275805116787706540804565321216948641858539),(192,711183343868708574776077137247814897899536639),(2240,527112360750174952149398194711834779551662269),(1216,655404258075330123058044014327799166096769259),(32,5706204538803490880094190105391521221193105407),(2080,4094975309387991502219814993223132013075197373),(1056,2795956513918376203468796124084599487322971115),(544,5282490378452943142442131406344387449919242087),(1568,2416843844131048287129502267394099068696320867),(288,5081783670917997592318607452722679373904346911),(2336,3648960403755681735839346485325395569110248733),(800,5014881435073167860349460189187729344933527303),(96,5706203198941671128898961849566934336947619839),(2144,4094974352343834537080358156753408581705926077),(1120,2795955939691882024385110660853231168276923371),(16,2787593149815694376876860490724816074047487),(2064,2000471495832807633264198639745165059386813),(1040,1365797508685821800821314864387325420821483),(528,2580699892261912869932569700286485849177959),(1552,1180682488773550433471928723143753734740835),(272,2482697822418763025672893067215912057175839),(2320,1782689119306152984494920287478068775972125),(784,2450030465956497816280536093423774248992519),(144,2786383545169698037718627705396356051777791),(2192,1999607491763789664237899806386847506639037),(1168,1365279102617916182263148640125759954229483),(8,5708990770816011147951285692548799013798805503),(1032,2797321726766661252965073451699048579973176299),(520,5285069718786383085617042631116762304721452903),(1544,2418023943371730881402855975680910471851334499),(136,713622636745727733783952883806903306769283327),(1160,656449669306855726137959053803837674904492267),(72,5706550286948102109849978530850135122114381823),(1096,2796275805108985950921655064985291932495643627),(200,711183343866102918967267871589481536838041855),(1224,655404258072730805502235889822108285643653355),(40,5706204538795662503812445256973394408011595775),(1064,2795956513910574447849656068484279038373845995),(552,5282490378445122372063987927302676214026731367),(1576,2416843844123249066811562668252583812176862051),(104,5706203198933842752617245335348232507218724863),(1128,2795955939684080268765998939451983859059524587),(4,5708990770813495495335130410190344415747244031),(2052,4096974808567378630139934740816824095490141629),(260,5084265009927727824526772214395764002370092831),(2308,3650742122220401722419678886677838085935033629),(132,713622636745128768875342713702561490694715647),(2180,528854712804250847350256249752383571418032317),(68,5706550286945586457233825053939207375039629311),(2116,4095231605804586460067573772058140676885972413),(196,711183343865503954058659479262972673641021695),(2244,527112360747375979624053939430640944699539645),(36,5706204538793146851196292298869227250297995263),(2084,4094975309379351195728623951588089178221538749),(292,5081783670908140341251197286722905701267668767),(2340,3648960403747203688624984657197859500342734109),(100,5706203198931327100001092411831182722129201151),(2148,4094974352335194230589195460846478010792019389),(12,5708990770813455564341223220928169022333124607),(140,713622636745119261495841001946470618901657855),(76,5706550286945546526239917864704581344971065343),(204,711183343865494446679157767534008952728453375),(44,5706204538793106920202385109642517703949418495),(108,5706203198931287169007185222605000941361956863),(2,5708990770813454930516225338268371381519384575),(2050,4096974808567338244290708662001315983522491837),(1026,2797321726764105358790128170338562972155567083),(514,5285069718783826915246673360246701076417347431),(1538,2418023943369175029338423768954548907737013091),(258,5084265009927687329066358822250092646128156447),(2306,3650742122220361386112232747951765775674207517),(770,5017330106975640800339587457293608285102931719),(130,713622636745119182538756461498351751584954623),(2178,528854712804241281449652729270292878615783613),(1154,656449669306247181085485142447504302806538475),(18,2787593139431734175773425254471331689267199),(2066,2000471487152569926212394186260207655153085),(1042,1365797498328482420087491905274379102510059),(530,2580699881885558595400094413119936003047271),(1554,1180682478418746374490301156282496792845155),(274,2482697812521580688907020870346778595032863),(2322,1782689110788174578450845589677272876150045),(786,2450030456066921386742810731807508530200327),(146,2786383541955569902305441557685160130787583),(2194,1999607488955309730871385078975287302695101),(1170,1365279099410126302873418188458620486031595),(10,5708990770813454930516076583688132740432003071),(1034,2797321726764105358789979415782343162576952299),(522,5285069718783826915246524605673224431840788327),(1546,2418023943369175029338275014400583096995339107),(138,713622636745119182538631318750976059467774207),(1162,656449669306247181085359999723848375035369707),(6,5708990770813454930516074222576948349891510271),(2054,4096974808567338244290559120408034710430379453),(262,5084265009927687329066208149712872947757088543),(2310,3650742122220361386112083354076552280334363933),(134,713622636745119182538628987038841435657746687),(2182,528854712804241281449526809309258742907939005),(14,5708990770813454930516074222540920102628360191),(142,713622636745119182538628987003261789138729215),(1,10384593717069655257060992658440191),(2049,8680692340680773638700828987190717),(1025,10357649794349789471649594028252139),(513,10376940748777202456761574620135271),(1537,10355072382636258374214522719624035),(257,9897746528089449082177853969137439),(2305,8518383522071324749737850794896669),(769,9890133193221066527881333874622215),(129,3214207054218165085793751905745151),(2177,2808538426159290958243382341281981),(1153,3207862608494512939128551105763563),(65,10384593716963957691812282560808959),(2113,8680692340576279723502928504948157),(1089,10357649794244091924767126295282667),(193,3214207054131384657014843418476799),(2241,2808538426073695732771209759817917),(1217,3207862608407732528434410006380779),(33,10384593716953994136252986435960831),(2081,8680692340566662044395014442806717),(1057,10357649794234128374485485986307051),(545,10376940748661541342708967858634599),(1569,10355072382520597279302214509189987),(289,9897746527974230683227616805256991),(2337,8518383521957360729384625947897117),(801,9890133193105848135686496154943239),(97,10384593716925625349182864777807871),(2145,8680692340538316315754984921630141),(1121,10357649794205759587767208049116139),(17,10383960201254550963704763544240127),(2065,8680237707201346082794477952134589),(1041,10357339380884938662545393832090603),(529,10376354274683591007855832474845031),(1553,10354804059132743268039705600908131),(273,9897182336916544770117079335436063),(2321,8517978406193468609042538674482461),(785,9889576429688397928102215078117127),(145,3214128135540660642801158635534591),(2193,2808479933492434724025342623361213),(1169,3207789879517204923037337699883243)]
private def pair15_2lim : List Nat := [0,4863937283925257856772082070637612021657370624,5706201792130334484756055656258432458729553920,5708990770813454930515923106777438377182361296,5708990770823839524233143877797980545530986494,5708990770823839524233143877797980545530986495]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair15_2i : inds pair15_2base = pair15_2ind := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair15_2u : usable 6 2 pair15_2base = pair15_2use := by rw [usable,pair15_2i]; decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair15_2t : tagged 6 2 pair15_2base = pair15_2opt := by rw [tagged,pair15_2u,pair15_2i]; decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair15_2l : cells 6 pair15_2ind [] 6 1 = pair15_2lim := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pair15_2v : universal pair15_2ind = 5708990770823839524233143877797980545530986495 := by decide +kernel
set_option maxRecDepth 50000 in
set_option maxHeartbeats 30000000 in
private theorem pairScan15_2 : (cutCatalog 2 25 pair15_2base).all (fun g => decide (normalizeFinal g = final15)) = true := by
  rw [cutCatalog,pair15_2t,pair15_2i,pair15_2l,pair15_2v]
  decide +kernel

private theorem scan15_twoneighbors {b g : List Nat} (hb : b ∈ narrow12) (hg : g ∈ cutCatalog 2 25 b) : normalizeFinal g = final15 := by
  simp only [narrow12,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact of_decide_eq_true (List.all_eq_true.mp pairScan15_0 _ hg)
  · exact of_decide_eq_true (List.all_eq_true.mp pairScan15_1 _ hg)
  · exact of_decide_eq_true (List.all_eq_true.mp pairScan15_2 _ hg)


end OMA.RamseyFinite
namespace OMA.RamseyFinite

/- Split a three-row extension at its first chosen contact. Each row certificate
   covers only the completions of the indicated initial contacts. -/
private def tailTriples (b : List Nat) (options : List (Nat × Nat)) (u : Nat)
    (st : List Nat) (a : Nat × Nat) : List (List (Nat × Nat)) :=
  let ending (cs : List (Nat × Nat)) := (degrees (attach (cs.reverse.map Prod.fst) b)).all (3≤·)
  if (0≤a.1 && a.2 &&& st.headD u == 0) && costAt b a ≤ 7 then
    trimmed options u ending (costAt b) 2 2 a.1 (7-costAt b a) [a] (tick u a.2 st)
  else []

private def tailAgrees (b : List Nat) (options : List (Nat × Nat)) (u : Nat)
    (st : List Nat) (a : Nat × Nat) :=
  (tailTriples b options u st a).all fun cs =>
    decide (normalizeFinal (attach (cs.reverse.map Prod.fst) b) = final15)

private theorem three_by_first {b g : List Nat} {options : List (Nat × Nat)}
    {u : Nat} {st : List Nat} (edgeB : edges_ b=15)
    (mem : g ∈ cutGrow 3 25 b options u st)
    (allRows : options.all (tailAgrees b options u st)=true) : normalizeFinal g=final15 := by
  obtain ⟨cs,hcs,rfl⟩ := List.mem_map.mp mem
  change cs ∈ trimmed options u _ (costAt b) 2 3 0 (25-edges_ b-3) [] st at hcs
  rw [edgeB] at hcs
  change cs ∈ options.flatMap (tailTriples b options u st) at hcs
  obtain ⟨a,ha,hc⟩ := List.mem_flatMap.mp hcs
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp allRows a ha) cs hc)

private abbrev triSeed0 : List Nat := [3,128,144,3,2,6,3,2,2,1,0]
private def triSeed0I : List (Nat × Nat) := [(0, 0),(1024, 1),(512, 1),(256, 1),(768, 2),(128, 1),(1152, 2),(384, 2),(64, 1),(1088, 2),(576, 2),(32, 1),(1056, 2),(544, 2),(96, 2),(1120, 3),(608, 3),(16, 1),(1040, 2),(528, 2),(272, 2),(784, 3),(144, 2),(1168, 3),(400, 3),(48, 2),(1072, 3),(560, 3),(8, 1),(1032, 2),(520, 2),(264, 2),(776, 3),(136, 2),(1160, 3),(392, 3),(72, 2),(1096, 3),(584, 3),(4, 1),(516, 2),(260, 2),(772, 3),(68, 2),(580, 3),(36, 2),(548, 3),(100, 3),(612, 4),(20, 2),(532, 3),(276, 3),(788, 4),(52, 3),(564, 4),(12, 2),(524, 3),(268, 3),(780, 4),(76, 3),(588, 4),(2, 1),(1026, 2),(258, 2),(130, 2),(1154, 3),(386, 3),(66, 2),(1090, 3),(34, 2),(1058, 3),(98, 3),(1122, 4),(18, 2),(1042, 3),(274, 3),(146, 3),(1170, 4),(402, 4),(50, 3),(1074, 4),(10, 2),(1034, 3),(266, 3),(138, 3),(1162, 4),(394, 4),(74, 3),(1098, 4),(6, 2),(262, 3),(70, 3),(38, 3),(102, 4),(22, 3),(278, 4),(54, 4),(14, 3),(270, 4),(78, 4),(1, 1),(1025, 2),(513, 2),(257, 2),(769, 3),(129, 2),(1153, 3),(385, 3),(65, 2),(1089, 3),(577, 3),(33, 2),(1057, 3),(545, 3),(97, 3),(1121, 4),(609, 4),(17, 2),(1041, 3),(529, 3),(273, 3),(785, 4),(145, 3),(1169, 4),(401, 4),(49, 3),(1073, 4),(561, 4),(9, 2),(1033, 3),(521, 3),(265, 3),(777, 4),(137, 3),(1161, 4),(393, 4),(73, 3),(1097, 4),(585, 4)]
private theorem triSeed0inds : inds triSeed0=triSeed0I := by decide +kernel
private def triSeed0O0 : List (Nat × Nat) := [(768,0x3636c6db63b7bb7b7fb68a2a8b636c6db63),(1152,0x51da3b6d1dffe8a8aa8bfffffd1da3b6d1d),(384,0x707e0fff07b7b8787f879e7f9f07e0fff07),(1088,0xbdb7a28bd7d65ada25a7fe678bdb7a28bd),(576,0xeb7d618eb7d67ffe67e2aa228eb7d618eb),(1056,0x5bd17a05bdeceda5a0dbf9e1fdbd17a05bd),(544,0x3eb1d603ebecffe7e1fea8a0abeb1d603eb),(96,0xff1fe00ff6c67e7e07e79e078ff1fe00ff)]
private def triSeed0O1 : List (Nat × Nat) := [(1120,0xbd17a00bd6c65a5a05a79e078bd17a00bd),(608,0xeb1d600eb6c67e7e07e28a028eb1d600eb),(1040,0x5bd0016dbde3eda00adbf81ffdbd0016dbd),(528,0x3eb000dbebe3ffe01ffea80aabeb000dbeb),(272,0x767001ff67a3bb601fb7981f9f67001ff67),(784,0x363000db63a3bb601fb6880a8b63000db63),(144,0x71f001ff1fe3f8e01f8ff81fff1f001ff1f),(1168,0x51d0016d1de3e8a00a8bf81ffd1d0016d1d)]
private def triSeed0O2 : List (Nat × Nat) := [(400,0x707001ff07a3b8601f87981f9f07001ff07),(48,0x7ff00007ffe0ffe001fff801ffff00007ff),(1072,0x5bd00005bde0eda000dbf801fdbd00005bd),(560,0x3eb00003ebe0ffe001fea800abeb00003eb),(1032,0xb7b6dbd1fe00daada07fff800b7b6dbd),(520,0x7d6dbeb1fe01ffffe02aaa8007d6dbeb),(264,0xecfff6717a01b7fb6067f9800ecfff67),(776,0x6c6db6317a01b7fb6022a88006c6db63)]
private def triSeed0O3 : List (Nat × Nat) := [(136,0xe3fff1f1fe018ff8e07fff800e3fff1f),(1160,0xa3b6d1d1fe008aa8a07fff800a3b6d1d),(392,0xe0fff0717a0187f86067f9800e0fff07),(72,0xffe38ff1d601fe67e07e67800ffe38ff),(1096,0xb7a28bd1d600da25a07e67800b7a28bd),(584,0x7d618eb1d601fe67e02a228007d618eb),(516,0x3eb7d6dbeb001ffffffe000003eb7d6dbeb),(260,0x767ecfff67001b7b7fb600000767ecfff67)]
private def triSeed0O4 : List (Nat × Nat) := [(772,0x3636c6db63001b7b7fb6000003636c6db63),(68,0xffffe38ff0007ffe67e000000ffffe38ff),(580,0xeb7d618eb0007ffe67e000000eb7d618eb),(36,0x7ff1fe07ff001fe7e1fe000007ff1fe07ff),(548,0x3eb1d603eb001fe7e1fe000003eb1d603eb),(100,0xff1fe00ff0007e7e07e000000ff1fe00ff),(612,0xeb1d600eb0007e7e07e000000eb1d600eb),(20,0x7ff001ffff001fe01ffe000007ff001ffff)]
private def triSeed0O5 : List (Nat × Nat) := [(532,0x3eb000dbeb001fe01ffe000003eb000dbeb),(276,0x767001ff67001b601fb600000767001ff67),(788,0x363000db63001b601fb600000363000db63),(52,0x7ff00007ff001fe001fe000007ff00007ff),(564,0x3eb00003eb001fe001fe000003eb00003eb),(12,0xfffffff00001ffffe00000000fffffff),(524,0x7d6dbeb00001ffffe000000007d6dbeb),(268,0xecfff6700001b7fb600000000ecfff67)]
private def triSeed0O6 : List (Nat × Nat) := [(780,0x6c6db6300001b7fb6000000006c6db63),(76,0xffe38ff00001fe67e00000000ffe38ff),(588,0x7d618eb00001fe67e000000007d618eb),(1026,0x5bdb7b6dbd0000000001fffffdbdb7b6dbd),(258,0x767ecfff6700000000019e7f9f67ecfff67),(130,0x71fe3fff1f0000000001ffffff1fe3fff1f),(1154,0x51da3b6d1d0000000001fffffd1da3b6d1d),(386,0x707e0fff0700000000019e7f9f07e0fff07)]
private def triSeed0O7 : List (Nat × Nat) := [(66,0xffffe38ff00000000007fe678ffffe38ff),(1090,0xbdb7a28bd00000000007fe678bdb7a28bd),(34,0x7ff1fe07ff0000000001f9e1ffff1fe07ff),(1058,0x5bd17a05bd0000000001f9e1fdbd17a05bd),(98,0xff1fe00ff000000000079e078ff1fe00ff),(1122,0xbd17a00bd000000000079e078bd17a00bd),(18,0x7ff001ffff0000000001f81fffff001ffff),(1042,0x5bd0016dbd0000000001f81ffdbd0016dbd)]
private def triSeed0O8 : List (Nat × Nat) := [(274,0x767001ff670000000001981f9f67001ff67),(146,0x71f001ff1f0000000001f81fff1f001ff1f),(1170,0x51d0016d1d0000000001f81ffd1d0016d1d),(402,0x707001ff070000000001981f9f07001ff07),(50,0x7ff00007ff0000000001f801ffff00007ff),(1074,0x5bd00005bd0000000001f801fdbd00005bd),(10,0xfffffff000000000007fff800fffffff),(1034,0xb7b6dbd000000000007fff800b7b6dbd)]
private def triSeed0O9 : List (Nat × Nat) := [(266,0xecfff670000000000067f9800ecfff67),(138,0xe3fff1f000000000007fff800e3fff1f),(1162,0xa3b6d1d000000000007fff800a3b6d1d),(394,0xe0fff070000000000067f9800e0fff07),(74,0xffe38ff000000000007e67800ffe38ff),(1098,0xb7a28bd000000000007e67800b7a28bd),(6,0x7fffffffff0000000000000007fffffffff),(262,0x767ecfff67000000000000000767ecfff67)]
private def triSeed0O10 : List (Nat × Nat) := [(70,0xffffe38ff0000000000000000ffffe38ff),(38,0x7ff1fe07ff0000000000000007ff1fe07ff),(102,0xff1fe00ff0000000000000000ff1fe00ff),(22,0x7ff001ffff0000000000000007ff001ffff),(278,0x767001ff67000000000000000767001ff67),(54,0x7ff00007ff0000000000000007ff00007ff),(14,0xfffffff000000000000000000fffffff),(270,0xecfff67000000000000000000ecfff67)]
private def triSeed0O11 : List (Nat × Nat) := [(78,0xffe38ff000000000000000000ffe38ff),(1025,0xffedadaadbfffffdbdb7b6dbd),(513,0xfffffffffeaaaaabeb7d6dbeb),(257,0xb7bb7b7fb79e7f9f67ecfff67),(769,0xb7bb7b7fb68a2a8b636c6db63),(129,0xfff8f8ff8fffffff1fe3fff1f),(1153,0xffe8a8aa8bfffffd1da3b6d1d),(385,0xb7b8787f879e7f9f07e0fff07)]
private def triSeed0O12 : List (Nat × Nat) := [(65,0x7d67ffe67e7fe678ffffe38ff),(1089,0x7d65ada25a7fe678bdb7a28bd),(577,0x7d67ffe67e2aa228eb7d618eb),(33,0xecffe7e1fff9e1ffff1fe07ff),(1057,0xeceda5a0dbf9e1fdbd17a05bd),(545,0xecffe7e1fea8a0abeb1d603eb),(97,0x6c67e7e07e79e078ff1fe00ff),(1121,0x6c65a5a05a79e078bd17a00bd)]
private def triSeed0O13 : List (Nat × Nat) := [(609,0x6c67e7e07e28a028eb1d600eb),(17,0xe3ffe01ffff81fffff001ffff),(1041,0xe3eda00adbf81ffdbd0016dbd),(529,0xe3ffe01ffea80aabeb000dbeb),(273,0xa3bb601fb7981f9f67001ff67),(785,0xa3bb601fb6880a8b63000db63),(145,0xe3f8e01f8ff81fff1f001ff1f),(1169,0xe3e8a00a8bf81ffd1d0016d1d)]
private def triSeed0O14 : List (Nat × Nat) := [(401,0xa3b8601f87981f9f07001ff07),(49,0xe0ffe001fff801ffff00007ff),(1073,0xe0eda000dbf801fdbd00005bd),(561,0xe0ffe001fea800abeb00003eb),(9,0x1fe01ffffe07fff800fffffff),(1033,0x1fe00daada07fff800b7b6dbd),(521,0x1fe01ffffe02aaa8007d6dbeb),(265,0x17a01b7fb6067f9800ecfff67)]
private def triSeed0O15 : List (Nat × Nat) := [(777,0x17a01b7fb6022a88006c6db63),(137,0x1fe018ff8e07fff800e3fff1f),(1161,0x1fe008aa8a07fff800a3b6d1d),(393,0x17a0187f86067f9800e0fff07),(73,0x1d601fe67e07e67800ffe38ff),(1097,0x1d600da25a07e67800b7a28bd),(585,0x1d601fe67e02a228007d618eb)]
private def triSeed0Opts := triSeed0O0 ++ triSeed0O1 ++ triSeed0O2 ++ triSeed0O3 ++ triSeed0O4 ++ triSeed0O5 ++ triSeed0O6 ++ triSeed0O7 ++ triSeed0O8 ++ triSeed0O9 ++ triSeed0O10 ++ triSeed0O11 ++ triSeed0O12 ++ triSeed0O13 ++ triSeed0O14 ++ triSeed0O15
private def triSeed0Cells : List Nat := [0x0,0x6d0da18000da16161001451000000000000,0x7feffdf6d0ffdfdfdd61f7dd46d0da18000,0x7ffffffffefffffffffdfffff7feffdf6d0,0x7fffffffffffffffffffffffffffffffffe,0x7ffffffffffffffffffffffffffffffffff]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op0 : ([768,1152,384,1088,576,1056,544,96] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O0 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op1 : ([1120,608,1040,528,272,784,144,1168] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O1 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op2 : ([400,48,1072,560,1032,520,264,776] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O2 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op3 : ([136,1160,392,72,1096,584,516,260] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O3 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op4 : ([772,68,580,36,548,100,612,20] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O4 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op5 : ([532,276,788,52,564,12,524,268] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O5 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op6 : ([780,76,588,1026,258,130,1154,386] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O6 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op7 : ([66,1090,34,1058,98,1122,18,1042] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O7 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op8 : ([274,146,1170,402,50,1074,10,1034] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O8 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op9 : ([266,138,1162,394,74,1098,6,262] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O9 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op10 : ([70,38,102,22,278,54,14,270] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O10 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op11 : ([78,1025,513,257,769,129,1153,385] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O11 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op12 : ([65,1089,577,33,1057,545,97,1121] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O12 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op13 : ([609,17,1041,529,273,785,145,1169] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O13 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op14 : ([401,49,1073,561,9,1033,521,265] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O14 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0op15 : ([777,137,1161,393,73,1097,585] : List Nat).map (fun x => (x,compat triSeed0I x)) = triSeed0O15 := by decide +kernel
private theorem triSeed0usable : usable 6 3 triSeed0=([768,1152,384,1088,576,1056,544,96] : List Nat) ++ ([1120,608,1040,528,272,784,144,1168] : List Nat) ++ ([400,48,1072,560,1032,520,264,776] : List Nat) ++ ([136,1160,392,72,1096,584,516,260] : List Nat) ++ ([772,68,580,36,548,100,612,20] : List Nat) ++ ([532,276,788,52,564,12,524,268] : List Nat) ++ ([780,76,588,1026,258,130,1154,386] : List Nat) ++ ([66,1090,34,1058,98,1122,18,1042] : List Nat) ++ ([274,146,1170,402,50,1074,10,1034] : List Nat) ++ ([266,138,1162,394,74,1098,6,262] : List Nat) ++ ([70,38,102,22,278,54,14,270] : List Nat) ++ ([78,1025,513,257,769,129,1153,385] : List Nat) ++ ([65,1089,577,33,1057,545,97,1121] : List Nat) ++ ([609,17,1041,529,273,785,145,1169] : List Nat) ++ ([401,49,1073,561,9,1033,521,265] : List Nat) ++ ([777,137,1161,393,73,1097,585] : List Nat) := by decide +kernel
private theorem triSeed0opts_eq : tagged 6 3 triSeed0=triSeed0Opts := by
  unfold tagged
  rw [triSeed0usable, triSeed0inds]
  simp only [List.map_append,triSeed0op0, triSeed0op1, triSeed0op2, triSeed0op3, triSeed0op4, triSeed0op5, triSeed0op6, triSeed0op7, triSeed0op8, triSeed0op9, triSeed0op10, triSeed0op11, triSeed0op12, triSeed0op13, triSeed0op14, triSeed0op15, triSeed0Opts]
private theorem triSeed0univ_eq : universal (inds triSeed0)=0x7ffffffffffffffffffffffffffffffffff := by decide +kernel
private theorem triSeed0cells_eq : cells 6 (inds triSeed0) [] 6 1=triSeed0Cells := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc0 : triSeed0O0.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc1 : triSeed0O1.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc2 : triSeed0O2.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc3 : triSeed0O3.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc4 : triSeed0O4.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc5 : triSeed0O5.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc6 : triSeed0O6.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc7 : triSeed0O7.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc8 : triSeed0O8.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc9 : triSeed0O9.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc10 : triSeed0O10.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc11 : triSeed0O11.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc12 : triSeed0O12.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc13 : triSeed0O13.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc14 : triSeed0O14.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed0sc15 : triSeed0O15.all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true := by decide +kernel

private theorem triSeed0ok {g : List Nat} (hg : g ∈ grow 6 3 triSeed0) (he : edges_ g ≤ 25) :
    normalizeFinal g = final15 := by
  have mem := grow_to_trim hg he
  rw [triSeed0opts_eq,triSeed0univ_eq,triSeed0cells_eq] at mem
  apply three_by_first (by decide +kernel) mem
  change (triSeed0O0 ++ triSeed0O1 ++ triSeed0O2 ++ triSeed0O3 ++ triSeed0O4 ++ triSeed0O5 ++ triSeed0O6 ++ triSeed0O7 ++ triSeed0O8 ++ triSeed0O9 ++ triSeed0O10 ++ triSeed0O11 ++ triSeed0O12 ++ triSeed0O13 ++ triSeed0O14 ++ triSeed0O15).all (tailAgrees triSeed0 triSeed0Opts 0x7ffffffffffffffffffffffffffffffffff triSeed0Cells)=true
  simp only [List.all_append, triSeed0sc0, triSeed0sc1, triSeed0sc2, triSeed0sc3, triSeed0sc4, triSeed0sc5, triSeed0sc6, triSeed0sc7, triSeed0sc8, triSeed0sc9, triSeed0sc10, triSeed0sc11, triSeed0sc12, triSeed0sc13, triSeed0sc14, triSeed0sc15, Bool.and_self]

private abbrev triSeed4 : List Nat := [3,192,128,3,2,6,3,2,2,1,0]
private def triSeed4I : List (Nat × Nat) := [(0, 0),(1024, 1),(512, 1),(256, 1),(768, 2),(128, 1),(1152, 2),(384, 2),(64, 1),(1088, 2),(576, 2),(32, 1),(1056, 2),(544, 2),(96, 2),(1120, 3),(608, 3),(16, 1),(1040, 2),(528, 2),(272, 2),(784, 3),(144, 2),(1168, 3),(400, 3),(48, 2),(1072, 3),(560, 3),(8, 1),(1032, 2),(520, 2),(264, 2),(776, 3),(136, 2),(1160, 3),(392, 3),(72, 2),(1096, 3),(584, 3),(4, 1),(516, 2),(260, 2),(772, 3),(132, 2),(388, 3),(68, 2),(580, 3),(36, 2),(548, 3),(100, 3),(612, 4),(20, 2),(532, 3),(276, 3),(788, 4),(148, 3),(404, 4),(52, 3),(564, 4),(12, 2),(524, 3),(268, 3),(780, 4),(140, 3),(396, 4),(76, 3),(588, 4),(2, 1),(1026, 2),(130, 2),(1154, 3),(66, 2),(1090, 3),(34, 2),(1058, 3),(98, 3),(1122, 4),(18, 2),(1042, 3),(146, 3),(1170, 4),(50, 3),(1074, 4),(10, 2),(1034, 3),(138, 3),(1162, 4),(74, 3),(1098, 4),(6, 2),(134, 3),(70, 3),(38, 3),(102, 4),(22, 3),(150, 4),(54, 4),(14, 3),(142, 4),(78, 4),(1, 1),(1025, 2),(513, 2),(257, 2),(769, 3),(129, 2),(1153, 3),(385, 3),(65, 2),(1089, 3),(577, 3),(33, 2),(1057, 3),(545, 3),(97, 3),(1121, 4),(609, 4),(17, 2),(1041, 3),(529, 3),(273, 3),(785, 4),(145, 3),(1169, 4),(401, 4),(49, 3),(1073, 4),(561, 4),(9, 2),(1033, 3),(521, 3),(265, 3),(777, 4),(137, 3),(1161, 4),(393, 4),(73, 3),(1097, 4),(585, 4)]
private theorem triSeed4inds : inds triSeed4=triSeed4I := by decide +kernel
private def triSeed4O0 : List (Nat × Nat) := [(768,0x3636c6db63ffffffffa8a8aa8b636c6db63),(1152,0x51da3b6d1db7a8a2a8e7e7fe7d1da3b6d1d),(384,0x707e0fff07b7b9e7f9e1e1fe1f07e0fff07),(1088,0xbdb7a28bd7d62aa229fff99f8bdb7a28bd),(576,0xeb7d618eb7d67fe679aba89a8eb7d618eb),(1056,0x5bd17a05bdecea8a0aff9f87fdbd17a05bd),(544,0x3eb1d603ebecff9e1fba9a83abeb1d603eb),(96,0xff1fe00ff6c679e079f9f81f8ff1fe00ff)]
private def triSeed4O1 : List (Nat × Nat) := [(1120,0xbd17a00bd6c628a029f9f81f8bd17a00bd),(608,0xeb1d600eb6c679e079a9a81a8eb1d600eb),(1040,0x5bd0016dbde3ea80aaff807ffdbd0016dbd),(528,0x3eb000dbebe3ff81ffba802babeb000dbeb),(272,0x767001ff67e3ff81ffe9807e9f67001ff67),(784,0x363000db63e3ff81ffa8802a8b63000db63),(144,0x71f001ff1fa3b981f9e7807e7f1f001ff1f),(1168,0x51d0016d1da3a880a8e7807e7d1d0016d1d)]
private def triSeed4O2 : List (Nat × Nat) := [(400,0x707001ff07a3b981f9e1807e1f07001ff07),(48,0x7ff00007ffe0ff801fff8007ffff00007ff),(1072,0x5bd00005bde0ea800aff8007fdbd00005bd),(560,0x3eb00003ebe0ff801fba8003abeb00003eb),(1032,0xb7b6dbd1fe02aaa807ffff800b7b6dbd),(520,0x7d6dbeb1fe07fff803aaba8007d6dbeb),(264,0xecfff671fe07fff8069fe9800ecfff67),(776,0x6c6db631fe07fff8028aa88006c6db63)]
private def triSeed4O3 : List (Nat × Nat) := [(136,0xe3fff1f17a067f98067fe7800e3fff1f),(1160,0xa3b6d1d17a022a88067fe7800a3b6d1d),(392,0xe0fff0717a067f98061fe1800e0fff07),(72,0xffe38ff1d607e67807f99f800ffe38ff),(1096,0xb7a28bd1d602a22807f99f800b7a28bd),(584,0x7d618eb1d607e67803a89a8007d618eb),(516,0x3eb7d6dbeb001fffff80000003eb7d6dbeb),(260,0x767ecfff67001fffff8000000767ecfff67)]
private def triSeed4O4 : List (Nat × Nat) := [(772,0x3636c6db63001fffff80000003636c6db63),(132,0x71fe3fff1f0019e7f9800000071fe3fff1f),(388,0x707e0fff070019e7f98000000707e0fff07),(68,0xffffe38ff0007fe6780000000ffffe38ff),(580,0xeb7d618eb0007fe6780000000eb7d618eb),(36,0x7ff1fe07ff001f9e1f80000007ff1fe07ff),(548,0x3eb1d603eb001f9e1f80000003eb1d603eb),(100,0xff1fe00ff00079e0780000000ff1fe00ff)]
private def triSeed4O5 : List (Nat × Nat) := [(612,0xeb1d600eb00079e0780000000eb1d600eb),(20,0x7ff001ffff001f81ff80000007ff001ffff),(532,0x3eb000dbeb001f81ff80000003eb000dbeb),(276,0x767001ff67001f81ff8000000767001ff67),(788,0x363000db63001f81ff8000000363000db63),(148,0x71f001ff1f001981f9800000071f001ff1f),(404,0x707001ff07001981f98000000707001ff07),(52,0x7ff00007ff001f801f80000007ff00007ff)]
private def triSeed4O6 : List (Nat × Nat) := [(564,0x3eb00003eb001f801f80000003eb00003eb),(12,0xfffffff00007fff8000000000fffffff),(524,0x7d6dbeb00007fff80000000007d6dbeb),(268,0xecfff6700007fff8000000000ecfff67),(780,0x6c6db6300007fff80000000006c6db63),(140,0xe3fff1f000067f98000000000e3fff1f),(396,0xe0fff07000067f98000000000e0fff07),(76,0xffe38ff00007e678000000000ffe38ff)]
private def triSeed4O7 : List (Nat × Nat) := [(588,0x7d618eb00007e6780000000007d618eb),(1026,0x5bdb7b6dbd000000007ffffffdbdb7b6dbd),(130,0x71fe3fff1f0000000067e7fe7f1fe3fff1f),(1154,0x51da3b6d1d0000000067e7fe7d1da3b6d1d),(66,0xffffe38ff000000001fff99f8ffffe38ff),(1090,0xbdb7a28bd000000001fff99f8bdb7a28bd),(34,0x7ff1fe07ff000000007f9f87ffff1fe07ff),(1058,0x5bd17a05bd000000007f9f87fdbd17a05bd)]
private def triSeed4O8 : List (Nat × Nat) := [(98,0xff1fe00ff000000001f9f81f8ff1fe00ff),(1122,0xbd17a00bd000000001f9f81f8bd17a00bd),(18,0x7ff001ffff000000007f807fffff001ffff),(1042,0x5bd0016dbd000000007f807ffdbd0016dbd),(146,0x71f001ff1f0000000067807e7f1f001ff1f),(1170,0x51d0016d1d0000000067807e7d1d0016d1d),(50,0x7ff00007ff000000007f8007ffff00007ff),(1074,0x5bd00005bd000000007f8007fdbd00005bd)]
private def triSeed4O9 : List (Nat × Nat) := [(10,0xfffffff00000000007ffff800fffffff),(1034,0xb7b6dbd00000000007ffff800b7b6dbd),(138,0xe3fff1f000000000067fe7800e3fff1f),(1162,0xa3b6d1d000000000067fe7800a3b6d1d),(74,0xffe38ff00000000007f99f800ffe38ff),(1098,0xb7a28bd00000000007f99f800b7a28bd),(6,0x7fffffffff0000000000000007fffffffff),(134,0x71fe3fff1f00000000000000071fe3fff1f)]
private def triSeed4O10 : List (Nat × Nat) := [(70,0xffffe38ff0000000000000000ffffe38ff),(38,0x7ff1fe07ff0000000000000007ff1fe07ff),(102,0xff1fe00ff0000000000000000ff1fe00ff),(22,0x7ff001ffff0000000000000007ff001ffff),(150,0x71f001ff1f00000000000000071f001ff1f),(54,0x7ff00007ff0000000000000007ff00007ff),(14,0xfffffff000000000000000000fffffff),(142,0xe3fff1f000000000000000000e3fff1f)]
private def triSeed4O11 : List (Nat × Nat) := [(78,0xffe38ff000000000000000000ffe38ff),(1025,0xffeaaaaafffffffdbdb7b6dbd),(513,0xffffffffbabaababeb7d6dbeb),(257,0xffffffffe9e9fe9f67ecfff67),(769,0xffffffffa8a8aa8b636c6db63),(129,0xb7b9e7f9e7e7fe7f1fe3fff1f),(1153,0xb7a8a2a8e7e7fe7d1da3b6d1d),(385,0xb7b9e7f9e1e1fe1f07e0fff07)]
private def triSeed4O12 : List (Nat × Nat) := [(65,0x7d67fe679fff99f8ffffe38ff),(1089,0x7d62aa229fff99f8bdb7a28bd),(577,0x7d67fe679aba89a8eb7d618eb),(33,0xecff9e1fff9f87ffff1fe07ff),(1057,0xecea8a0aff9f87fdbd17a05bd),(545,0xecff9e1fba9a83abeb1d603eb),(97,0x6c679e079f9f81f8ff1fe00ff),(1121,0x6c628a029f9f81f8bd17a00bd)]
private def triSeed4O13 : List (Nat × Nat) := [(609,0x6c679e079a9a81a8eb1d600eb),(17,0xe3ff81ffff807fffff001ffff),(1041,0xe3ea80aaff807ffdbd0016dbd),(529,0xe3ff81ffba802babeb000dbeb),(273,0xe3ff81ffe9807e9f67001ff67),(785,0xe3ff81ffa8802a8b63000db63),(145,0xa3b981f9e7807e7f1f001ff1f),(1169,0xa3a880a8e7807e7d1d0016d1d)]
private def triSeed4O14 : List (Nat × Nat) := [(401,0xa3b981f9e1807e1f07001ff07),(49,0xe0ff801fff8007ffff00007ff),(1073,0xe0ea800aff8007fdbd00005bd),(561,0xe0ff801fba8003abeb00003eb),(9,0x1fe07fff807ffff800fffffff),(1033,0x1fe02aaa807ffff800b7b6dbd),(521,0x1fe07fff803aaba8007d6dbeb),(265,0x1fe07fff8069fe9800ecfff67)]
private def triSeed4O15 : List (Nat × Nat) := [(777,0x1fe07fff8028aa88006c6db63),(137,0x17a067f98067fe7800e3fff1f),(1161,0x17a022a88067fe7800a3b6d1d),(393,0x17a067f98061fe1800e0fff07),(73,0x1d607e67807f99f800ffe38ff),(1097,0x1d602a22807f99f800b7a28bd),(585,0x1d607e67803a89a8007d618eb)]
private def triSeed4Opts := triSeed4O0 ++ triSeed4O1 ++ triSeed4O2 ++ triSeed4O3 ++ triSeed4O4 ++ triSeed4O5 ++ triSeed4O6 ++ triSeed4O7 ++ triSeed4O8 ++ triSeed4O9 ++ triSeed4O10 ++ triSeed4O11 ++ triSeed4O12 ++ triSeed4O13 ++ triSeed4O14 ++ triSeed4O15
private def triSeed4Cells : List Nat := [0x0,0x6d0da18000da14510054544000000000000,0x7feffdf6d0ffdf7dd47f7f7546d0da18000,0x7ffffffffeffffffff7ffffff7feffdf6d0,0x7fffffffffffffffffffffffffffffffffe,0x7ffffffffffffffffffffffffffffffffff]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op0 : ([768,1152,384,1088,576,1056,544,96] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O0 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op1 : ([1120,608,1040,528,272,784,144,1168] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O1 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op2 : ([400,48,1072,560,1032,520,264,776] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O2 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op3 : ([136,1160,392,72,1096,584,516,260] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O3 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op4 : ([772,132,388,68,580,36,548,100] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O4 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op5 : ([612,20,532,276,788,148,404,52] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O5 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op6 : ([564,12,524,268,780,140,396,76] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O6 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op7 : ([588,1026,130,1154,66,1090,34,1058] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O7 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op8 : ([98,1122,18,1042,146,1170,50,1074] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O8 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op9 : ([10,1034,138,1162,74,1098,6,134] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O9 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op10 : ([70,38,102,22,150,54,14,142] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O10 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op11 : ([78,1025,513,257,769,129,1153,385] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O11 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op12 : ([65,1089,577,33,1057,545,97,1121] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O12 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op13 : ([609,17,1041,529,273,785,145,1169] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O13 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op14 : ([401,49,1073,561,9,1033,521,265] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O14 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4op15 : ([777,137,1161,393,73,1097,585] : List Nat).map (fun x => (x,compat triSeed4I x)) = triSeed4O15 := by decide +kernel
private theorem triSeed4usable : usable 6 3 triSeed4=([768,1152,384,1088,576,1056,544,96] : List Nat) ++ ([1120,608,1040,528,272,784,144,1168] : List Nat) ++ ([400,48,1072,560,1032,520,264,776] : List Nat) ++ ([136,1160,392,72,1096,584,516,260] : List Nat) ++ ([772,132,388,68,580,36,548,100] : List Nat) ++ ([612,20,532,276,788,148,404,52] : List Nat) ++ ([564,12,524,268,780,140,396,76] : List Nat) ++ ([588,1026,130,1154,66,1090,34,1058] : List Nat) ++ ([98,1122,18,1042,146,1170,50,1074] : List Nat) ++ ([10,1034,138,1162,74,1098,6,134] : List Nat) ++ ([70,38,102,22,150,54,14,142] : List Nat) ++ ([78,1025,513,257,769,129,1153,385] : List Nat) ++ ([65,1089,577,33,1057,545,97,1121] : List Nat) ++ ([609,17,1041,529,273,785,145,1169] : List Nat) ++ ([401,49,1073,561,9,1033,521,265] : List Nat) ++ ([777,137,1161,393,73,1097,585] : List Nat) := by decide +kernel
private theorem triSeed4opts_eq : tagged 6 3 triSeed4=triSeed4Opts := by
  unfold tagged
  rw [triSeed4usable, triSeed4inds]
  simp only [List.map_append,triSeed4op0, triSeed4op1, triSeed4op2, triSeed4op3, triSeed4op4, triSeed4op5, triSeed4op6, triSeed4op7, triSeed4op8, triSeed4op9, triSeed4op10, triSeed4op11, triSeed4op12, triSeed4op13, triSeed4op14, triSeed4op15, triSeed4Opts]
private theorem triSeed4univ_eq : universal (inds triSeed4)=0x7ffffffffffffffffffffffffffffffffff := by decide +kernel
private theorem triSeed4cells_eq : cells 6 (inds triSeed4) [] 6 1=triSeed4Cells := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc0 : triSeed4O0.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc1 : triSeed4O1.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc2 : triSeed4O2.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc3 : triSeed4O3.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc4 : triSeed4O4.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc5 : triSeed4O5.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc6 : triSeed4O6.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc7 : triSeed4O7.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc8 : triSeed4O8.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc9 : triSeed4O9.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc10 : triSeed4O10.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc11 : triSeed4O11.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc12 : triSeed4O12.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc13 : triSeed4O13.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc14 : triSeed4O14.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed4sc15 : triSeed4O15.all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true := by decide +kernel

private theorem triSeed4ok {g : List Nat} (hg : g ∈ grow 6 3 triSeed4) (he : edges_ g ≤ 25) :
    normalizeFinal g = final15 := by
  have mem := grow_to_trim hg he
  rw [triSeed4opts_eq,triSeed4univ_eq,triSeed4cells_eq] at mem
  apply three_by_first (by decide +kernel) mem
  change (triSeed4O0 ++ triSeed4O1 ++ triSeed4O2 ++ triSeed4O3 ++ triSeed4O4 ++ triSeed4O5 ++ triSeed4O6 ++ triSeed4O7 ++ triSeed4O8 ++ triSeed4O9 ++ triSeed4O10 ++ triSeed4O11 ++ triSeed4O12 ++ triSeed4O13 ++ triSeed4O14 ++ triSeed4O15).all (tailAgrees triSeed4 triSeed4Opts 0x7ffffffffffffffffffffffffffffffffff triSeed4Cells)=true
  simp only [List.all_append, triSeed4sc0, triSeed4sc1, triSeed4sc2, triSeed4sc3, triSeed4sc4, triSeed4sc5, triSeed4sc6, triSeed4sc7, triSeed4sc8, triSeed4sc9, triSeed4sc10, triSeed4sc11, triSeed4sc12, triSeed4sc13, triSeed4sc14, triSeed4sc15, Bool.and_self]

private abbrev triSeed16 : List Nat := [3,4,9,3,2,6,3,2,2,1,0]
private def triSeed16I : List (Nat × Nat) := [(0, 0),(1024, 1),(512, 1),(256, 1),(768, 2),(128, 1),(1152, 2),(384, 2),(64, 1),(1088, 2),(576, 2),(32, 1),(1056, 2),(544, 2),(96, 2),(1120, 3),(608, 3),(16, 1),(1040, 2),(528, 2),(272, 2),(784, 3),(144, 2),(1168, 3),(400, 3),(48, 2),(1072, 3),(560, 3),(8, 1),(1032, 2),(520, 2),(264, 2),(776, 3),(136, 2),(1160, 3),(392, 3),(72, 2),(1096, 3),(584, 3),(4, 1),(1028, 2),(516, 2),(260, 2),(772, 3),(132, 2),(1156, 3),(388, 3),(36, 2),(1060, 3),(548, 3),(20, 2),(1044, 3),(532, 3),(276, 3),(788, 4),(148, 3),(1172, 4),(404, 4),(52, 3),(1076, 4),(564, 4),(2, 1),(1026, 2),(514, 2),(258, 2),(770, 3),(130, 2),(1154, 3),(386, 3),(66, 2),(1090, 3),(578, 3),(34, 2),(1058, 3),(546, 3),(98, 3),(1122, 4),(610, 4),(10, 2),(1034, 3),(522, 3),(266, 3),(778, 4),(138, 3),(1162, 4),(394, 4),(74, 3),(1098, 4),(586, 4),(6, 2),(1030, 3),(518, 3),(262, 3),(774, 4),(134, 3),(1158, 4),(390, 4),(38, 3),(1062, 4),(550, 4),(1, 1),(1025, 2),(513, 2),(257, 2),(769, 3),(129, 2),(1153, 3),(385, 3),(65, 2),(1089, 3),(577, 3),(33, 2),(1057, 3),(545, 3),(97, 3),(1121, 4),(609, 4),(17, 2),(1041, 3),(529, 3),(273, 3),(785, 4),(145, 3),(1169, 4),(401, 4),(49, 3),(1073, 4),(561, 4),(9, 2),(1033, 3),(521, 3),(265, 3),(777, 4),(137, 3),(1161, 4),(393, 4),(73, 3),(1097, 4),(585, 4)]
private theorem triSeed16inds : inds triSeed16=triSeed16I := by decide +kernel
private def triSeed16O0 : List (Nat × Nat) := [(768,0x3636c6db636c6d8db6c6d8db1b636c6db63),(1152,0x51da3b6d1da3b476da3b4768ed1da3b6d1d),(384,0x707e0fff07e0fc1ffe0fc1f83f07e0fff07),(1088,0xbdb7a28bdb7a2f4517b6f6de8bdb7a28bd),(576,0xeb7d618eb7d63ac31d6fadf58eb7d618eb),(1056,0x5bd17a05bd17b6f40b7a2f45edbd17a05bd),(544,0x3eb1d603eb1d6fac07d63ac75beb1d603eb),(96,0xff1fe00ff1fe3fc01fe3fc7f8ff1fe00ff)]
private def triSeed16O1 : List (Nat × Nat) := [(1120,0xbd17a00bd17a2f4017a2f45e8bd17a00bd),(608,0xeb1d600eb1d63ac01d63ac758eb1d600eb),(1040,0x5bd0016dbdb7b6f6db7a002dedbd0016dbd),(528,0x3eb000dbeb7d6fadb7d6001f5beb000dbeb),(272,0x767001ff67ecfd9ffece003b3f67001ff67),(784,0x363000db636c6d8db6c6001b1b63000db63),(144,0x71f001ff1fe3fc7ffe3e0038ff1f001ff1f),(1168,0x51d0016d1da3b476da3a0028ed1d0016d1d)]
private def triSeed16O2 : List (Nat × Nat) := [(400,0x707001ff07e0fc1ffe0e00383f07001ff07),(48,0x7ff00007ff1ffffc0ffe0007ffff00007ff),(1072,0x5bd00005bd17b6f40b7a0005edbd00005bd),(560,0x3eb00003eb1d6fac07d600075beb00003eb),(1032,0xb7b6dbdb7a002db7b6f6de800b7b6dbd),(520,0x7d6dbeb7d6001b7d6fadf58007d6dbeb),(264,0xecfff67ece003fecfd9fb3800ecfff67),(776,0x6c6db636c6001b6c6d8db18006c6db63)]
private def triSeed16O3 : List (Nat × Nat) := [(136,0xe3fff1fe3e003fe3fc7f8f800e3fff1f),(1160,0xa3b6d1da3a002da3b4768e800a3b6d1d),(392,0xe0fff07e0e003fe0fc1f83800e0fff07),(72,0xffe38ffffe00071fffffff800ffe38ff),(1096,0xb7a28bdb7a000517b6f6de800b7a28bd),(584,0x7d618eb7d600031d6fadf58007d618eb),(1028,0x5bdb7b6dbd0016f6db7a000005bdb7b6dbd),(516,0x3eb7d6dbeb000fadb7d6000003eb7d6dbeb)]
private def triSeed16O4 : List (Nat × Nat) := [(260,0x767ecfff67001d9ffece00000767ecfff67),(772,0x3636c6db63000d8db6c6000003636c6db63),(132,0x71fe3fff1f001c7ffe3e0000071fe3fff1f),(1156,0x51da3b6d1d001476da3a0000051da3b6d1d),(388,0x707e0fff07001c1ffe0e00000707e0fff07),(36,0x7ff1fe07ff001ffc0ffe000007ff1fe07ff),(1060,0x5bd17a05bd0016f40b7a000005bd17a05bd),(548,0x3eb1d603eb000fac07d6000003eb1d603eb)]
private def triSeed16O5 : List (Nat × Nat) := [(20,0x7ff001ffff001ffffffe000007ff001ffff),(1044,0x5bd0016dbd0016f6db7a000005bd0016dbd),(532,0x3eb000dbeb000fadb7d6000003eb000dbeb),(276,0x767001ff67001d9ffece00000767001ff67),(788,0x363000db63000d8db6c600000363000db63),(148,0x71f001ff1f001c7ffe3e0000071f001ff1f),(1172,0x51d0016d1d001476da3a0000051d0016d1d),(404,0x707001ff07001c1ffe0e00000707001ff07)]
private def triSeed16O6 : List (Nat × Nat) := [(52,0x7ff00007ff001ffc0ffe000007ff00007ff),(1076,0x5bd00005bd0016f40b7a000005bd00005bd),(564,0x3eb00003eb000fac07d6000003eb00003eb),(1026,0x5bdb7b6dbd00000000016f6dedbdb7b6dbd),(514,0x3eb7d6dbeb0000000000fadf5beb7d6dbeb),(258,0x767ecfff670000000001d9fb3f67ecfff67),(770,0x3636c6db630000000000d8db1b636c6db63),(130,0x71fe3fff1f0000000001c7f8ff1fe3fff1f)]
private def triSeed16O7 : List (Nat × Nat) := [(1154,0x51da3b6d1d00000000014768ed1da3b6d1d),(386,0x707e0fff070000000001c1f83f07e0fff07),(66,0xffffe38ff0000000001fffff8ffffe38ff),(1090,0xbdb7a28bd00000000016f6de8bdb7a28bd),(578,0xeb7d618eb0000000000fadf58eb7d618eb),(34,0x7ff1fe07ff00000000003fc7ffff1fe07ff),(1058,0x5bd17a05bd00000000002f45edbd17a05bd),(546,0x3eb1d603eb00000000003ac75beb1d603eb)]
private def triSeed16O8 : List (Nat × Nat) := [(98,0xff1fe00ff00000000003fc7f8ff1fe00ff),(1122,0xbd17a00bd00000000002f45e8bd17a00bd),(610,0xeb1d600eb00000000003ac758eb1d600eb),(10,0xfffffff0000000001fffff800fffffff),(1034,0xb7b6dbd00000000016f6de800b7b6dbd),(522,0x7d6dbeb0000000000fadf58007d6dbeb),(266,0xecfff670000000001d9fb3800ecfff67),(778,0x6c6db630000000000d8db18006c6db63)]
private def triSeed16O9 : List (Nat × Nat) := [(138,0xe3fff1f0000000001c7f8f800e3fff1f),(1162,0xa3b6d1d00000000014768e800a3b6d1d),(394,0xe0fff070000000001c1f83800e0fff07),(74,0xffe38ff0000000001fffff800ffe38ff),(1098,0xb7a28bd00000000016f6de800b7a28bd),(586,0x7d618eb0000000000fadf58007d618eb),(6,0x7fffffffff0000000000000007fffffffff),(1030,0x5bdb7b6dbd0000000000000005bdb7b6dbd)]
private def triSeed16O10 : List (Nat × Nat) := [(518,0x3eb7d6dbeb0000000000000003eb7d6dbeb),(262,0x767ecfff67000000000000000767ecfff67),(774,0x3636c6db630000000000000003636c6db63),(134,0x71fe3fff1f00000000000000071fe3fff1f),(1158,0x51da3b6d1d00000000000000051da3b6d1d),(390,0x707e0fff07000000000000000707e0fff07),(38,0x7ff1fe07ff0000000000000007ff1fe07ff),(1062,0x5bd17a05bd0000000000000005bd17a05bd)]
private def triSeed16O11 : List (Nat × Nat) := [(550,0x3eb1d603eb0000000000000003eb1d603eb),(1025,0xb7b6f6db7b6f6dedbdb7b6dbd),(513,0x7d6fadb7d6fadf5beb7d6dbeb),(257,0xecfd9ffecfd9fb3f67ecfff67),(769,0x6c6d8db6c6d8db1b636c6db63),(129,0xe3fc7ffe3fc7f8ff1fe3fff1f),(1153,0xa3b476da3b4768ed1da3b6d1d),(385,0xe0fc1ffe0fc1f83f07e0fff07)]
private def triSeed16O12 : List (Nat × Nat) := [(65,0xffe3fc71fffffff8ffffe38ff),(1089,0xb7a2f4517b6f6de8bdb7a28bd),(577,0x7d63ac31d6fadf58eb7d618eb),(33,0x1ffffc0ffe3fc7ffff1fe07ff),(1057,0x17b6f40b7a2f45edbd17a05bd),(545,0x1d6fac07d63ac75beb1d603eb),(97,0x1fe3fc01fe3fc7f8ff1fe00ff),(1121,0x17a2f4017a2f45e8bd17a00bd)]
private def triSeed16O13 : List (Nat × Nat) := [(609,0x1d63ac01d63ac758eb1d600eb),(17,0xfffffffffe003fffff001ffff),(1041,0xb7b6f6db7a002dedbd0016dbd),(529,0x7d6fadb7d6001f5beb000dbeb),(273,0xecfd9ffece003b3f67001ff67),(785,0x6c6d8db6c6001b1b63000db63),(145,0xe3fc7ffe3e0038ff1f001ff1f),(1169,0xa3b476da3a0028ed1d0016d1d)]
private def triSeed16O14 : List (Nat × Nat) := [(401,0xe0fc1ffe0e00383f07001ff07),(49,0x1ffffc0ffe0007ffff00007ff),(1073,0x17b6f40b7a0005edbd00005bd),(561,0x1d6fac07d600075beb00003eb),(9,0xffe003fffffffff800fffffff),(1033,0xb7a002db7b6f6de800b7b6dbd),(521,0x7d6001b7d6fadf58007d6dbeb),(265,0xece003fecfd9fb3800ecfff67)]
private def triSeed16O15 : List (Nat × Nat) := [(777,0x6c6001b6c6d8db18006c6db63),(137,0xe3e003fe3fc7f8f800e3fff1f),(1161,0xa3a002da3b4768e800a3b6d1d),(393,0xe0e003fe0fc1f83800e0fff07),(73,0xffe00071fffffff800ffe38ff),(1097,0xb7a000517b6f6de800b7a28bd),(585,0x7d600031d6fadf58007d618eb)]
private def triSeed16Opts := triSeed16O0 ++ triSeed16O1 ++ triSeed16O2 ++ triSeed16O3 ++ triSeed16O4 ++ triSeed16O5 ++ triSeed16O6 ++ triSeed16O7 ++ triSeed16O8 ++ triSeed16O9 ++ triSeed16O10 ++ triSeed16O11 ++ triSeed16O12 ++ triSeed16O13 ++ triSeed16O14 ++ triSeed16O15
private def triSeed16Cells : List Nat := [0x0,0x6d0da18000da1b430001b40000000000000,0x7feffdf6d0ffdffbeda1ffb686d0da18000,0x7ffffffffefffffffffdfffff7feffdf6d0,0x7fffffffffffffffffffffffffffffffffe,0x7ffffffffffffffffffffffffffffffffff]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op0 : ([768,1152,384,1088,576,1056,544,96] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O0 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op1 : ([1120,608,1040,528,272,784,144,1168] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O1 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op2 : ([400,48,1072,560,1032,520,264,776] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O2 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op3 : ([136,1160,392,72,1096,584,1028,516] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O3 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op4 : ([260,772,132,1156,388,36,1060,548] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O4 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op5 : ([20,1044,532,276,788,148,1172,404] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O5 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op6 : ([52,1076,564,1026,514,258,770,130] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O6 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op7 : ([1154,386,66,1090,578,34,1058,546] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O7 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op8 : ([98,1122,610,10,1034,522,266,778] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O8 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op9 : ([138,1162,394,74,1098,586,6,1030] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O9 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op10 : ([518,262,774,134,1158,390,38,1062] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O10 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op11 : ([550,1025,513,257,769,129,1153,385] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O11 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op12 : ([65,1089,577,33,1057,545,97,1121] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O12 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op13 : ([609,17,1041,529,273,785,145,1169] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O13 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op14 : ([401,49,1073,561,9,1033,521,265] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O14 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16op15 : ([777,137,1161,393,73,1097,585] : List Nat).map (fun x => (x,compat triSeed16I x)) = triSeed16O15 := by decide +kernel
private theorem triSeed16usable : usable 6 3 triSeed16=([768,1152,384,1088,576,1056,544,96] : List Nat) ++ ([1120,608,1040,528,272,784,144,1168] : List Nat) ++ ([400,48,1072,560,1032,520,264,776] : List Nat) ++ ([136,1160,392,72,1096,584,1028,516] : List Nat) ++ ([260,772,132,1156,388,36,1060,548] : List Nat) ++ ([20,1044,532,276,788,148,1172,404] : List Nat) ++ ([52,1076,564,1026,514,258,770,130] : List Nat) ++ ([1154,386,66,1090,578,34,1058,546] : List Nat) ++ ([98,1122,610,10,1034,522,266,778] : List Nat) ++ ([138,1162,394,74,1098,586,6,1030] : List Nat) ++ ([518,262,774,134,1158,390,38,1062] : List Nat) ++ ([550,1025,513,257,769,129,1153,385] : List Nat) ++ ([65,1089,577,33,1057,545,97,1121] : List Nat) ++ ([609,17,1041,529,273,785,145,1169] : List Nat) ++ ([401,49,1073,561,9,1033,521,265] : List Nat) ++ ([777,137,1161,393,73,1097,585] : List Nat) := by decide +kernel
private theorem triSeed16opts_eq : tagged 6 3 triSeed16=triSeed16Opts := by
  unfold tagged
  rw [triSeed16usable, triSeed16inds]
  simp only [List.map_append,triSeed16op0, triSeed16op1, triSeed16op2, triSeed16op3, triSeed16op4, triSeed16op5, triSeed16op6, triSeed16op7, triSeed16op8, triSeed16op9, triSeed16op10, triSeed16op11, triSeed16op12, triSeed16op13, triSeed16op14, triSeed16op15, triSeed16Opts]
private theorem triSeed16univ_eq : universal (inds triSeed16)=0x7ffffffffffffffffffffffffffffffffff := by decide +kernel
private theorem triSeed16cells_eq : cells 6 (inds triSeed16) [] 6 1=triSeed16Cells := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc0 : triSeed16O0.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc1 : triSeed16O1.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc2 : triSeed16O2.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc3 : triSeed16O3.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc4 : triSeed16O4.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc5 : triSeed16O5.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc6 : triSeed16O6.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc7 : triSeed16O7.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc8 : triSeed16O8.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc9 : triSeed16O9.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc10 : triSeed16O10.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc11 : triSeed16O11.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc12 : triSeed16O12.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc13 : triSeed16O13.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc14 : triSeed16O14.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed16sc15 : triSeed16O15.all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true := by decide +kernel

private theorem triSeed16ok {g : List Nat} (hg : g ∈ grow 6 3 triSeed16) (he : edges_ g ≤ 25) :
    normalizeFinal g = final15 := by
  have mem := grow_to_trim hg he
  rw [triSeed16opts_eq,triSeed16univ_eq,triSeed16cells_eq] at mem
  apply three_by_first (by decide +kernel) mem
  change (triSeed16O0 ++ triSeed16O1 ++ triSeed16O2 ++ triSeed16O3 ++ triSeed16O4 ++ triSeed16O5 ++ triSeed16O6 ++ triSeed16O7 ++ triSeed16O8 ++ triSeed16O9 ++ triSeed16O10 ++ triSeed16O11 ++ triSeed16O12 ++ triSeed16O13 ++ triSeed16O14 ++ triSeed16O15).all (tailAgrees triSeed16 triSeed16Opts 0x7ffffffffffffffffffffffffffffffffff triSeed16Cells)=true
  simp only [List.all_append, triSeed16sc0, triSeed16sc1, triSeed16sc2, triSeed16sc3, triSeed16sc4, triSeed16sc5, triSeed16sc6, triSeed16sc7, triSeed16sc8, triSeed16sc9, triSeed16sc10, triSeed16sc11, triSeed16sc12, triSeed16sc13, triSeed16sc14, triSeed16sc15, Bool.and_self]

private abbrev triSeed29 : List Nat := [3,2,6,3,2,6,3,2,2,1,0]
private def triSeed29I : List (Nat × Nat) := [(0, 0),(1024, 1),(512, 1),(256, 1),(768, 2),(128, 1),(1152, 2),(384, 2),(64, 1),(1088, 2),(576, 2),(32, 1),(1056, 2),(544, 2),(96, 2),(1120, 3),(608, 3),(16, 1),(1040, 2),(528, 2),(272, 2),(784, 3),(144, 2),(1168, 3),(400, 3),(48, 2),(1072, 3),(560, 3),(8, 1),(1032, 2),(520, 2),(264, 2),(776, 3),(136, 2),(1160, 3),(392, 3),(72, 2),(1096, 3),(584, 3),(4, 1),(1028, 2),(516, 2),(260, 2),(772, 3),(132, 2),(1156, 3),(388, 3),(68, 2),(1092, 3),(580, 3),(12, 2),(1036, 3),(524, 3),(268, 3),(780, 4),(140, 3),(1164, 4),(396, 4),(76, 3),(1100, 4),(588, 4),(2, 1),(1026, 2),(514, 2),(258, 2),(770, 3),(130, 2),(1154, 3),(386, 3),(66, 2),(1090, 3),(578, 3),(34, 2),(1058, 3),(546, 3),(98, 3),(1122, 4),(610, 4),(18, 2),(1042, 3),(530, 3),(274, 3),(786, 4),(146, 3),(1170, 4),(402, 4),(50, 3),(1074, 4),(562, 4),(6, 2),(1030, 3),(518, 3),(262, 3),(774, 4),(134, 3),(1158, 4),(390, 4),(70, 3),(1094, 4),(582, 4),(1, 1),(1025, 2),(513, 2),(257, 2),(769, 3),(129, 2),(1153, 3),(385, 3),(65, 2),(1089, 3),(577, 3),(33, 2),(1057, 3),(545, 3),(97, 3),(1121, 4),(609, 4),(17, 2),(1041, 3),(529, 3),(273, 3),(785, 4),(145, 3),(1169, 4),(401, 4),(49, 3),(1073, 4),(561, 4),(9, 2),(1033, 3),(521, 3),(265, 3),(777, 4),(137, 3),(1161, 4),(393, 4),(73, 3),(1097, 4),(585, 4)]
private theorem triSeed29inds : inds triSeed29=triSeed29I := by decide +kernel
private def triSeed29O0 : List (Nat × Nat) := [(768,0x3636c6db636c6d8db6c6d8db1b636c6db63),(1152,0x51da3b6d1da3b476da3b4768ed1da3b6d1d),(384,0x707e0fff07e0fc1ffe0fc1f83f07e0fff07),(1088,0xbdb7a28bd17b6f4517a2f45e8bdb7a28bd),(576,0xeb7d618eb1d6fac31d63ac758eb7d618eb),(1056,0x5bd17a05bdb7a2f40b7b6f6dedbd17a05bd),(544,0x3eb1d603eb7d63ac07d6fadf5beb1d603eb),(96,0xff1fe00ff1fe3fc01fe3fc7f8ff1fe00ff)]
private def triSeed29O1 : List (Nat × Nat) := [(1120,0xbd17a00bd17a2f4017a2f45e8bd17a00bd),(608,0xeb1d600eb1d63ac01d63ac758eb1d600eb),(1040,0x5bd0016dbdb7a002db7b6f6dedbd0016dbd),(528,0x3eb000dbeb7d6001b7d6fadf5beb000dbeb),(272,0x767001ff67ece003fecfd9fb3f67001ff67),(784,0x363000db636c6001b6c6d8db1b63000db63),(144,0x71f001ff1fe3e003fe3fc7f8ff1f001ff1f),(1168,0x51d0016d1da3a002da3b4768ed1d0016d1d)]
private def triSeed29O2 : List (Nat × Nat) := [(400,0x707001ff07e0e003fe0fc1f83f07001ff07),(48,0x7ff00007ffffe0000fffffffffff00007ff),(1072,0x5bd00005bdb7a0000b7b6f6dedbd00005bd),(560,0x3eb00003eb7d600007d6fadf5beb00003eb),(1032,0xb7b6dbdb7b6f6db7a002de800b7b6dbd),(520,0x7d6dbeb7d6fadb7d6001f58007d6dbeb),(264,0xecfff67ecfd9ffece003b3800ecfff67),(776,0x6c6db636c6d8db6c6001b18006c6db63)]
private def triSeed29O3 : List (Nat × Nat) := [(136,0xe3fff1fe3fc7ffe3e0038f800e3fff1f),(1160,0xa3b6d1da3b476da3a0028e800a3b6d1d),(392,0xe0fff07e0fc1ffe0e00383800e0fff07),(72,0xffe38ff1ffffc71fe0007f800ffe38ff),(1096,0xb7a28bd17b6f4517a0005e800b7a28bd),(584,0x7d618eb1d6fac31d6000758007d618eb),(1028,0x5bdb7b6dbd0016f6db7a000005bdb7b6dbd),(516,0x3eb7d6dbeb000fadb7d6000003eb7d6dbeb)]
private def triSeed29O4 : List (Nat × Nat) := [(260,0x767ecfff67001d9ffece00000767ecfff67),(772,0x3636c6db63000d8db6c6000003636c6db63),(132,0x71fe3fff1f001c7ffe3e0000071fe3fff1f),(1156,0x51da3b6d1d001476da3a0000051da3b6d1d),(388,0x707e0fff07001c1ffe0e00000707e0fff07),(68,0xffffe38ff001ffc71fe000000ffffe38ff),(1092,0xbdb7a28bd0016f4517a000000bdb7a28bd),(580,0xeb7d618eb000fac31d6000000eb7d618eb)]
private def triSeed29O5 : List (Nat × Nat) := [(12,0xfffffff001ffffffe00000000fffffff),(1036,0xb7b6dbd0016f6db7a00000000b7b6dbd),(524,0x7d6dbeb000fadb7d6000000007d6dbeb),(268,0xecfff67001d9ffece00000000ecfff67),(780,0x6c6db63000d8db6c6000000006c6db63),(140,0xe3fff1f001c7ffe3e00000000e3fff1f),(1164,0xa3b6d1d001476da3a00000000a3b6d1d),(396,0xe0fff07001c1ffe0e00000000e0fff07)]
private def triSeed29O6 : List (Nat × Nat) := [(76,0xffe38ff001ffc71fe00000000ffe38ff),(1100,0xb7a28bd0016f4517a00000000b7a28bd),(588,0x7d618eb000fac31d6000000007d618eb),(1026,0x5bdb7b6dbd00000000016f6dedbdb7b6dbd),(514,0x3eb7d6dbeb0000000000fadf5beb7d6dbeb),(258,0x767ecfff670000000001d9fb3f67ecfff67),(770,0x3636c6db630000000000d8db1b636c6db63),(130,0x71fe3fff1f0000000001c7f8ff1fe3fff1f)]
private def triSeed29O7 : List (Nat × Nat) := [(1154,0x51da3b6d1d00000000014768ed1da3b6d1d),(386,0x707e0fff070000000001c1f83f07e0fff07),(66,0xffffe38ff00000000003fc7f8ffffe38ff),(1090,0xbdb7a28bd00000000002f45e8bdb7a28bd),(578,0xeb7d618eb00000000003ac758eb7d618eb),(34,0x7ff1fe07ff0000000001ffffffff1fe07ff),(1058,0x5bd17a05bd00000000016f6dedbd17a05bd),(546,0x3eb1d603eb0000000000fadf5beb1d603eb)]
private def triSeed29O8 : List (Nat × Nat) := [(98,0xff1fe00ff00000000003fc7f8ff1fe00ff),(1122,0xbd17a00bd00000000002f45e8bd17a00bd),(610,0xeb1d600eb00000000003ac758eb1d600eb),(18,0x7ff001ffff0000000001ffffffff001ffff),(1042,0x5bd0016dbd00000000016f6dedbd0016dbd),(530,0x3eb000dbeb0000000000fadf5beb000dbeb),(274,0x767001ff670000000001d9fb3f67001ff67),(786,0x363000db630000000000d8db1b63000db63)]
private def triSeed29O9 : List (Nat × Nat) := [(146,0x71f001ff1f0000000001c7f8ff1f001ff1f),(1170,0x51d0016d1d00000000014768ed1d0016d1d),(402,0x707001ff070000000001c1f83f07001ff07),(50,0x7ff00007ff0000000001ffffffff00007ff),(1074,0x5bd00005bd00000000016f6dedbd00005bd),(562,0x3eb00003eb0000000000fadf5beb00003eb),(6,0x7fffffffff0000000000000007fffffffff),(1030,0x5bdb7b6dbd0000000000000005bdb7b6dbd)]
private def triSeed29O10 : List (Nat × Nat) := [(518,0x3eb7d6dbeb0000000000000003eb7d6dbeb),(262,0x767ecfff67000000000000000767ecfff67),(774,0x3636c6db630000000000000003636c6db63),(134,0x71fe3fff1f00000000000000071fe3fff1f),(1158,0x51da3b6d1d00000000000000051da3b6d1d),(390,0x707e0fff07000000000000000707e0fff07),(70,0xffffe38ff0000000000000000ffffe38ff),(1094,0xbdb7a28bd0000000000000000bdb7a28bd)]
private def triSeed29O11 : List (Nat × Nat) := [(582,0xeb7d618eb0000000000000000eb7d618eb),(1025,0xb7b6f6db7b6f6dedbdb7b6dbd),(513,0x7d6fadb7d6fadf5beb7d6dbeb),(257,0xecfd9ffecfd9fb3f67ecfff67),(769,0x6c6d8db6c6d8db1b636c6db63),(129,0xe3fc7ffe3fc7f8ff1fe3fff1f),(1153,0xa3b476da3b4768ed1da3b6d1d),(385,0xe0fc1ffe0fc1f83f07e0fff07)]
private def triSeed29O12 : List (Nat × Nat) := [(65,0x1ffffc71fe3fc7f8ffffe38ff),(1089,0x17b6f4517a2f45e8bdb7a28bd),(577,0x1d6fac31d63ac758eb7d618eb),(33,0xffe3fc0fffffffffff1fe07ff),(1057,0xb7a2f40b7b6f6dedbd17a05bd),(545,0x7d63ac07d6fadf5beb1d603eb),(97,0x1fe3fc01fe3fc7f8ff1fe00ff),(1121,0x17a2f4017a2f45e8bd17a00bd)]
private def triSeed29O13 : List (Nat × Nat) := [(609,0x1d63ac01d63ac758eb1d600eb),(17,0xffe003ffffffffffff001ffff),(1041,0xb7a002db7b6f6dedbd0016dbd),(529,0x7d6001b7d6fadf5beb000dbeb),(273,0xece003fecfd9fb3f67001ff67),(785,0x6c6001b6c6d8db1b63000db63),(145,0xe3e003fe3fc7f8ff1f001ff1f),(1169,0xa3a002da3b4768ed1d0016d1d)]
private def triSeed29O14 : List (Nat × Nat) := [(401,0xe0e003fe0fc1f83f07001ff07),(49,0xffe0000fffffffffff00007ff),(1073,0xb7a0000b7b6f6dedbd00005bd),(561,0x7d600007d6fadf5beb00003eb),(9,0xfffffffffe003ff800fffffff),(1033,0xb7b6f6db7a002de800b7b6dbd),(521,0x7d6fadb7d6001f58007d6dbeb),(265,0xecfd9ffece003b3800ecfff67)]
private def triSeed29O15 : List (Nat × Nat) := [(777,0x6c6d8db6c6001b18006c6db63),(137,0xe3fc7ffe3e0038f800e3fff1f),(1161,0xa3b476da3a0028e800a3b6d1d),(393,0xe0fc1ffe0e00383800e0fff07),(73,0x1ffffc71fe0007f800ffe38ff),(1097,0x17b6f4517a0005e800b7a28bd),(585,0x1d6fac31d6000758007d618eb)]
private def triSeed29Opts := triSeed29O0 ++ triSeed29O1 ++ triSeed29O2 ++ triSeed29O3 ++ triSeed29O4 ++ triSeed29O5 ++ triSeed29O6 ++ triSeed29O7 ++ triSeed29O8 ++ triSeed29O9 ++ triSeed29O10 ++ triSeed29O11 ++ triSeed29O12 ++ triSeed29O13 ++ triSeed29O14 ++ triSeed29O15
private def triSeed29Cells : List Nat := [0x0,0x6d0da18000da1b430001b40000000000000,0x7feffdf6d0ffdffbeda1ffb686d0da18000,0x7ffffffffefffffffffdfffff7feffdf6d0,0x7fffffffffffffffffffffffffffffffffe,0x7ffffffffffffffffffffffffffffffffff]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op0 : ([768,1152,384,1088,576,1056,544,96] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O0 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op1 : ([1120,608,1040,528,272,784,144,1168] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O1 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op2 : ([400,48,1072,560,1032,520,264,776] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O2 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op3 : ([136,1160,392,72,1096,584,1028,516] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O3 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op4 : ([260,772,132,1156,388,68,1092,580] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O4 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op5 : ([12,1036,524,268,780,140,1164,396] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O5 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op6 : ([76,1100,588,1026,514,258,770,130] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O6 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op7 : ([1154,386,66,1090,578,34,1058,546] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O7 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op8 : ([98,1122,610,18,1042,530,274,786] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O8 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op9 : ([146,1170,402,50,1074,562,6,1030] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O9 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op10 : ([518,262,774,134,1158,390,70,1094] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O10 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op11 : ([582,1025,513,257,769,129,1153,385] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O11 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op12 : ([65,1089,577,33,1057,545,97,1121] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O12 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op13 : ([609,17,1041,529,273,785,145,1169] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O13 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op14 : ([401,49,1073,561,9,1033,521,265] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O14 := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29op15 : ([777,137,1161,393,73,1097,585] : List Nat).map (fun x => (x,compat triSeed29I x)) = triSeed29O15 := by decide +kernel
private theorem triSeed29usable : usable 6 3 triSeed29=([768,1152,384,1088,576,1056,544,96] : List Nat) ++ ([1120,608,1040,528,272,784,144,1168] : List Nat) ++ ([400,48,1072,560,1032,520,264,776] : List Nat) ++ ([136,1160,392,72,1096,584,1028,516] : List Nat) ++ ([260,772,132,1156,388,68,1092,580] : List Nat) ++ ([12,1036,524,268,780,140,1164,396] : List Nat) ++ ([76,1100,588,1026,514,258,770,130] : List Nat) ++ ([1154,386,66,1090,578,34,1058,546] : List Nat) ++ ([98,1122,610,18,1042,530,274,786] : List Nat) ++ ([146,1170,402,50,1074,562,6,1030] : List Nat) ++ ([518,262,774,134,1158,390,70,1094] : List Nat) ++ ([582,1025,513,257,769,129,1153,385] : List Nat) ++ ([65,1089,577,33,1057,545,97,1121] : List Nat) ++ ([609,17,1041,529,273,785,145,1169] : List Nat) ++ ([401,49,1073,561,9,1033,521,265] : List Nat) ++ ([777,137,1161,393,73,1097,585] : List Nat) := by decide +kernel
private theorem triSeed29opts_eq : tagged 6 3 triSeed29=triSeed29Opts := by
  unfold tagged
  rw [triSeed29usable, triSeed29inds]
  simp only [List.map_append,triSeed29op0, triSeed29op1, triSeed29op2, triSeed29op3, triSeed29op4, triSeed29op5, triSeed29op6, triSeed29op7, triSeed29op8, triSeed29op9, triSeed29op10, triSeed29op11, triSeed29op12, triSeed29op13, triSeed29op14, triSeed29op15, triSeed29Opts]
private theorem triSeed29univ_eq : universal (inds triSeed29)=0x7ffffffffffffffffffffffffffffffffff := by decide +kernel
private theorem triSeed29cells_eq : cells 6 (inds triSeed29) [] 6 1=triSeed29Cells := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc0 : triSeed29O0.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc1 : triSeed29O1.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc2 : triSeed29O2.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc3 : triSeed29O3.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc4 : triSeed29O4.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc5 : triSeed29O5.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc6 : triSeed29O6.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc7 : triSeed29O7.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc8 : triSeed29O8.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc9 : triSeed29O9.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc10 : triSeed29O10.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc11 : triSeed29O11.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc12 : triSeed29O12.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc13 : triSeed29O13.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc14 : triSeed29O14.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 30000000 in
private theorem triSeed29sc15 : triSeed29O15.all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true := by decide +kernel

private theorem triSeed29ok {g : List Nat} (hg : g ∈ grow 6 3 triSeed29) (he : edges_ g ≤ 25) :
    normalizeFinal g = final15 := by
  have mem := grow_to_trim hg he
  rw [triSeed29opts_eq,triSeed29univ_eq,triSeed29cells_eq] at mem
  apply three_by_first (by decide +kernel) mem
  change (triSeed29O0 ++ triSeed29O1 ++ triSeed29O2 ++ triSeed29O3 ++ triSeed29O4 ++ triSeed29O5 ++ triSeed29O6 ++ triSeed29O7 ++ triSeed29O8 ++ triSeed29O9 ++ triSeed29O10 ++ triSeed29O11 ++ triSeed29O12 ++ triSeed29O13 ++ triSeed29O14 ++ triSeed29O15).all (tailAgrees triSeed29 triSeed29Opts 0x7ffffffffffffffffffffffffffffffffff triSeed29Cells)=true
  simp only [List.all_append, triSeed29sc0, triSeed29sc1, triSeed29sc2, triSeed29sc3, triSeed29sc4, triSeed29sc5, triSeed29sc6, triSeed29sc7, triSeed29sc8, triSeed29sc9, triSeed29sc10, triSeed29sc11, triSeed29sc12, triSeed29sc13, triSeed29sc14, triSeed29sc15, Bool.and_self]
theorem viable_three_contacts {b g : List Nat}
    (viable : b ∈ viable11) (hg : g ∈ grow 6 3 b) (he : edges_ g ≤ 25) :
    normalizeFinal g = final15 := by
  simp only [viable11, List.mem_cons, List.not_mem_nil, or_false] at viable
  rcases viable with rfl|rfl|rfl|rfl
  · exact triSeed0ok hg he
  · exact triSeed4ok hg he
  · exact triSeed16ok hg he
  · exact triSeed29ok hg he

end OMA.RamseyFinite
namespace OMA.RamseyFinite

theorem class14 (d : Nat) (hd : d ≤ 2) (b cs : List Nat) (hb : b ∈ levels normalized 5 (13-d) 4)
    (ext : Extension 6 d b cs) (_hs : cs.Pairwise (· ≤ ·)) (hg : attach cs b ∈ grow 6 d b)
    (he : edges_ (attach cs b) ≤ 20) : normalizeFinal (attach cs b) = final14 := by
  have low := parent_low hg he
  have hcut := grow_to_trim hg he
  interval_cases d
  · have h := base13_floor hb
    norm_num at low
    omega
  · have h := base12_floor hb
    norm_num at low
    omega
  · have hbb := base11_fits hb (by norm_num at low; omega)
    rcases prune11_2 hbb with viable | ⟨w,l,W,valid⟩
    · exact scan14_surviving viable hcut
    · have bound := viaDual b cs 2 w l W ext valid
      omega

theorem class15 (d : Nat) (hd : d ≤ 3) (b cs : List Nat) (hb : b ∈ levels normalized 5 (14-d) 4)
    (ext : Extension 6 d b cs) (hs : cs.Pairwise (· ≤ ·)) (hg : attach cs b ∈ grow 6 d b)
    (he : edges_ (attach cs b) ≤ 25) : normalizeFinal (attach cs b) = final15 := by
  have low := parent_low hg he
  have hcut := grow_to_trim hg he
  interval_cases d
  · change b ∈ levels normalized 5 14 4 at hb
    rw [base14_empty] at hb
    simp at hb
  · have h := base13_floor hb
    norm_num at low
    omega
  · have hbb := base12_fits hb (by norm_num at low; omega)
    exact scan15_twoneighbors hbb hcut
  · have hbb := base11_fits hb (by norm_num at low; omega)
    rcases prune11_3 hbb with viable | ⟨w,l,W,valid⟩
    · exact viable_three_contacts viable hg he
    · have bound := viaDual b cs 3 w l W ext valid
      omega

end OMA.RamseyFinite


/- The anti-neighborhood of a vertex in a triangle-free graph with no independent
set of size k+1 has no independent set of size k. Summing the resulting local
edge bounds uses the neighborhood identities already proved in reduction R2. -/

namespace Ramsey39Small

open SimpleGraph Finset

lemma degree_cap {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : G.CliqueFree 3) (ind : Gᶜ.CliqueFree (k+1)) (v : Fin n) : G.degree v ≤ k := by
  by_contra! h
  apply ind.mono h (G.neighborFinset v)
  refine ⟨?_, rfl⟩
  rw [G.coe_neighborFinset, G.isClique_compl]
  exact G.isIndepSet_neighborSet_of_triangleFree tri v

/-- A lower bound may depend on the vertex as well as its degree. -/
theorem deficiency_of_local {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (val : Fin n → ℕ)
    (localBound : ∀ v, val v + (∑ w ∈ G.neighborFinset v, G.degree w) ≤ G.edgeFinset.card) :
    (∑ v, (val v + G.degree v ^ 2)) ≤ n * G.edgeFinset.card := by
  have h := Finset.sum_le_sum (s := (univ : Finset (Fin n))) (fun v _ => localBound v)
  rw [Finset.sum_add_distrib, RamseyDeficiency.sum_neighbor_degrees] at h
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using h


end Ramsey39Small


/- The contact-set argument specializes the proof by @sturdy4days in
open-math-agents #13293 to a maximum independent set of six vertices. -/
namespace Ramsey39Contacts
open SimpleGraph Finset

private lemma lift_card {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hi : Gᶜ.CliqueFree 7) (S : Finset (Gᶜ.neighborFinset v))
    (cl : ((G.induce ((Gᶜ.neighborFinset v : Finset V) : Set V))ᶜ).IsClique S) :
    S.card ≤ 5 := by
  classical
  let B := Gᶜ.neighborFinset v
  let f : B ↪ V := Function.Embedding.subtype _
  have free : Gᶜ.IsClique (S.map f) := by
    intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact ⟨hxy,(cl ha hb (fun h => hxy (congrArg f h))).2⟩
  have hv : v ∉ S.map f := by
    intro hm
    obtain ⟨b,_,eq⟩ := mem_map.mp hm
    exact ((Gᶜ.mem_neighborFinset _ _).mp b.2).ne eq.symm
  have ext : Gᶜ.IsClique (insert v (S.map f)) := free.insert (by
    intro b hb _
    obtain ⟨i,_,rfl⟩ := mem_map.mp hb
    exact (Gᶜ.mem_neighborFinset _ _).mp i.2)
  have lim : (insert v (S.map f)).card < 7 := lt_of_not_ge (fun h =>
    hi.mono h _ ⟨by simpa only [Finset.coe_insert] using ext,rfl⟩)
  rw [card_insert_of_notMem hv,card_map] at lim
  omega

theorem neighborhood_data {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 7) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set V)
    let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
    D.CliqueFree 3 ∧ Dᶜ.CliqueFree 6 ∧
      (∀ i, Dᶜ.IsClique (A i)) ∧
      (∀ (J : Finset N) (S : Finset B), Dᶜ.IsClique S → (∀ a ∈ J, Disjoint (A a) S) → J.card+S.card≤6) ∧
      N.card + (∑ a, (A a).card) ≤ ∑ a ∈ N, G.degree a := by
  classical
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set V)
  let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
  let f : B ↪ V := Function.Embedding.subtype _
  let g : N ↪ V := Function.Embedding.subtype _
  let em : D ↪g G := SimpleGraph.Embedding.comap f G
  have nd (a : N) := (G.mem_neighborFinset v a.val).mp a.2
  have bd (a : B) := (Gᶜ.mem_neighborFinset v a.val).mp a.2
  have split (a : N) (b : B) : a.val≠b.val := fun eq => (bd b).2 (eq ▸ nd a)
  have nr (a b : N) : ¬G.Adj a.val b.val := by
    intro h
    exact G.isIndepSet_neighborSet_of_triangleFree ht v (nd a) (nd b) h.ne h
  change D.CliqueFree 3 ∧ Dᶜ.CliqueFree 6 ∧ (∀ i, Dᶜ.IsClique (A i)) ∧ _ ∧ _
  refine ⟨CliqueFree.comap em.isContained ht,?_,?_,?_,?_⟩
  · intro S hS
    have h := lift_card G v hi S hS.isClique
    have eq := hS.card_eq
    omega
  · intro i a ha b hb hne
    refine ⟨hne,?_⟩
    intro h
    exact G.isIndepSet_neighborSet_of_triangleFree ht i.val (mem_filter.mp ha).2 (mem_filter.mp hb).2
      (Subtype.val_injective.ne hne) h
  · intro J S cl dis
    let X := J.map g
    let Y := S.map f
    have apart : Disjoint X Y := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨a,_,rfl⟩ := mem_map.mp hx
      obtain ⟨b,_,eq⟩ := mem_map.mp hy
      exact split a b eq.symm
    have sx : Gᶜ.IsClique X := by
      intro u hu w hw hne
      obtain ⟨a,_,rfl⟩ := mem_map.mp hu
      obtain ⟨b,_,rfl⟩ := mem_map.mp hw
      exact ⟨hne,nr a b⟩
    have sy : Gᶜ.IsClique Y := by
      intro u hu w hw hne
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
      exact ⟨hne,(cl ha hb (fun h => hne (congrArg f h))).2⟩
    have cross (u : V) (hu : u∈X) (w : V) (hw : w∈Y) : Gᶜ.Adj u w := by
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
      exact ⟨split a b,fun h => Finset.disjoint_left.mp (dis a ha) (mem_filter.mpr ⟨mem_univ _,h⟩) hb⟩
    have full : Gᶜ.IsClique (X ∪ Y) := by
      intro u hu w hw hne
      rcases hu with hu|hu <;> rcases hw with hw|hw
      · exact sx hu hw hne
      · exact cross _ hu _ hw
      · exact (cross _ hw _ hu).symm
      · exact sy hu hw hne
    have lim : (X ∪ Y).card < 7 := lt_of_not_ge (fun h =>
      hi.mono h _ ⟨by simpa only [Finset.coe_union] using full,rfl⟩)
    rw [card_union_of_disjoint apart,card_map,card_map] at lim
    omega
  · have each (a : N) : 1 + (A a).card ≤ G.degree a.val := by
      let Y := (A a).map f
      have nv : v ∉ Y := by
        rintro mem
        obtain ⟨b,_,eq⟩ := mem_map.mp mem
        exact (bd b).1 eq.symm
      have sub : insert v Y ⊆ G.neighborFinset a.val := by
        intro w hw
        rcases mem_insert.mp hw with rfl|mem
        · exact (G.mem_neighborFinset _ _).mpr (nd a).symm
        · obtain ⟨b,hb,rfl⟩ := mem_map.mp mem
          exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp hb).2
      have le := card_le_card sub
      rw [card_insert_of_notMem nv,card_map,G.card_neighborFinset_eq_degree] at le
      omega
    have total := Finset.sum_le_sum (s := (univ : Finset N)) (fun a _ => each a)
    change N.card + (∑ a : N,(A a).card) ≤ ∑ a ∈ N,G.degree a
    rw [← Finset.sum_coe_sort N (fun i => G.degree i)]
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.mul_one,
      Fintype.card_coe,Nat.cast_id] using total





end Ramsey39Contacts
/- Independent-set bit-mask enumeration, adapted from the soundness and
completeness proof of GlueSeed.graph_rows in @sturdy4days' #13293. -/
namespace Ramsey39Contacts
open SimpleGraph Finset
theorem mask_rows {V W : Type} [Fintype W] [DecidableEq W] [DecidableEq V] {d : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) (nodup : vs.Nodup)
    (full : ∀ x : V, x∈vs) (A : W → Finset V) (hw : Fintype.card W=d)
    (rows : ∀ i, Gᶜ.IsClique (A i))
    (obstruction : ∀ (J : Finset W) (S : Finset V), Gᶜ.IsClique S →
      (∀ i ∈ J, Disjoint (A i) S) → J.card+S.card≤6) :
    let bits := fun bs : List Bool => bs.foldr (fun b k => 2*k+b.toNat) 0
    let enc := fun (ws : List V) => (ws.foldr (fun v (p : List V × List ℕ) =>
      (v::p.1, bits (p.1.map fun x => decide (G.Adj v x)) :: p.2)) ([],[])).2
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∃ R K : Fin d → Nat, (∀ i, (R i,K i)∈enum (enc vs)) ∧
      (∀ s t, (s,t)∈enum (enc vs) →
        ((univ : Finset (Fin d)).filter fun i => R i &&& s=0).card+t≤6) ∧
      (∑ i, K i) = ∑ i, (A i).card := by
  intro bits enc enum
  let mark (ws : List V) (S : Finset V) := bits (ws.map fun x => decide (x∈S))
  let ind0 (p : Nat × Nat) := (2*p.1,p.2)
  let ind1 (p : Nat × Nat) := (2*p.1+1,p.2+1)
  have enum_nil : enum [] = [(0,0)] := rfl
  have enum_cons (m : ℕ) (b : List ℕ) : enum (m::b) =
      (enum b).map ind0 ++ ((enum b).filter fun p=>m &&& p.1 == 0).map ind1 := rfl
  have enc_nil : enc [] = [] := rfl
  let foldPair (ws : List V) : List V × List ℕ :=
    ws.foldr (fun v (p : List V × List ℕ) =>
      (v::p.1,bits (p.1.map fun x => decide (G.Adj v x))::p.2)) ([],[])
  have prefix_eq (ws : List V) : (foldPair ws).1 = ws := by
    induction ws with
    | nil => rfl
    | cons x ws ih => exact congrArg (x :: ·) ih
  have enc_cons (a : V) (ws : List V) :
      enc (a::ws) = bits (ws.map fun x => decide (G.Adj a x)) :: enc ws := by
    change bits ((foldPair ws).1.map fun x => decide (G.Adj a x)) :: (foldPair ws).2 = _
    rw [prefix_eq]
  have bits_nil : bits [] = 0 := rfl
  have bits_cons (a : Bool) (l : List Bool) : bits (a::l) = 2*bits l+a.toNat := rfl
  have bit_form (b : Bool) (n : Nat) : Nat.bit b n = 2*n+b.toNat := by
    cases b <;> simp [Nat.bit, Nat.two_mul]
  have and_bit (a : Bool) (x : ℕ) (b : Bool) (y : ℕ) :
      Nat.bit a x &&& Nat.bit b y = Nat.bit (a && b) (x &&& y) := by
    apply Nat.eq_of_testBit_eq
    intro i
    cases i with
    | zero => cases a <;> cases b <;> simp [Nat.testBit_zero,bit_form]
    | succ i =>
      have half (c : Bool) (t : ℕ) : Nat.bit c t / 2 = t := by
        cases c <;> simp [bit_form]
        omega
      rw [Nat.testBit_and,Nat.testBit_succ,Nat.testBit_succ,Nat.testBit_succ,half,half,half,Nat.testBit_and]
  have and_mask (vs : List V) (f g : V → Bool) :
      bits (vs.map f) &&& bits (vs.map g) = 0 ↔ ∀ x∈vs, f x = true → g x = false := by
    induction vs with
    | nil => simp [bits_nil]
    | cons a l ih =>
      simp only [List.map_cons, bits_cons, ← bit_form, and_bit, List.forall_mem_cons]
      rw [bit_form]
      cases f a <;> cases g a <;> simp [ih]
  have mark_congr (vs : List V) (s t : Finset V)
      (h : ∀ x∈vs, x∈s ↔ x∈t) : mark vs s = mark vs t := by
    dsimp only [mark]
    congr 1
    exact List.map_congr_left (fun x hx => by simp only [h x hx])
  have sound (vs : List V) (hn : vs.Nodup) {p : Nat × Nat} (hp : p ∈ enum (enc vs)) :
      ∃ S : Finset V, S ⊆ vs.toFinset ∧ Gᶜ.IsClique (S : Set V) ∧ p = (mark vs S,S.card) := by
    induction vs generalizing p with
    | nil =>
      simp [enc_nil,enum_nil] at hp
      exact ⟨∅,by simp,by simp,by simp [hp,mark,bits_nil]⟩
    | cons a l ih =>
      have hn' := List.nodup_cons.mp hn
      simp only [enc_cons,enum_cons,List.mem_append,List.mem_map,List.mem_filter] at hp
      rcases hp with ⟨q,hq,rfl⟩ | ⟨q,⟨hq,hd⟩,rfl⟩
      · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
        have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
        exact ⟨S,by simpa using hS.trans (Finset.subset_insert a _),hI,by simp [ind0,mark,bits_cons,ha]⟩
      · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
        have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
        have hz := (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈S))).mp (beq_iff_eq.mp hd)
        have hi : Gᶜ.IsClique (insert a S : Finset V) := by
          rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem ha]
          refine ⟨hI,fun x hx => ⟨?_,?_⟩⟩
          · exact fun e => ha (e ▸ hx)
          · intro adj
            have := hz x (List.mem_toFinset.mp (hS hx)) (by simpa using adj)
            exact (of_decide_eq_false this) hx
        have hm := mark_congr l (insert a S) S (by intro x hx; simp [show x ≠ a from fun e => hn'.1 (e ▸ hx)])
        refine ⟨insert a S, by simpa using Finset.insert_subset_insert a hS, hi, ?_⟩
        simp [ind1,mark,bits_cons,Finset.card_insert_of_notMem ha] at hm ⊢
        omega
  have complete (vs : List V) (hn : vs.Nodup) (S : Finset V)
      (hS : S ⊆ vs.toFinset) (hI : Gᶜ.IsClique (S : Set V)) :
      (mark vs S,S.card) ∈ enum (enc vs) := by
    induction vs generalizing S with
    | nil =>
      have e : S=∅ := Finset.subset_empty.mp (by simpa using hS)
      simp [e,enc_nil,enum_nil,mark,bits_nil]
    | cons a l ih =>
      have hn' := List.nodup_cons.mp hn
      simp only [enc_cons,enum_cons,List.mem_append,List.mem_map,List.mem_filter]
      by_cases ha : a ∈ S
      · let T := S.erase a
        have hT : T ⊆ l.toFinset := by
          intro x hx
          have m := Finset.mem_erase.mp hx
          have h := List.mem_cons.mp (List.mem_toFinset.mp (hS m.2))
          exact List.mem_toFinset.mpr (h.resolve_left m.1)
        have hI' := hI.subset (show (T : Set V) ⊆ (S : Set V) from Finset.erase_subset ..)
        have hmark := mark_congr l S T (by intro x hx; simp [T,show x≠a from fun e => hn'.1 (e ▸ hx)])
        have hcard : T.card + 1 = S.card := Finset.card_erase_add_one ha
        right
        refine ⟨(mark l T,T.card),⟨ih hn'.2 T hT hI', ?_⟩,?_⟩
        · apply beq_iff_eq.mpr
          apply (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈T))).mpr
          intro x _ hx
          apply decide_eq_false
          intro hm
          have hmem := Finset.mem_erase.mp hm
          exact (hI ha hmem.2 hmem.1.symm).2 (of_decide_eq_true hx)
        · simp [ind1,mark,bits_cons,ha,hcard] at hmark ⊢
          omega
      · have hT : S ⊆ l.toFinset := by
          intro x hx
          have h := List.mem_cons.mp (List.mem_toFinset.mp (hS hx))
          exact List.mem_toFinset.mpr (h.resolve_left (fun e => ha (e ▸ hx)))
        exact Or.inl ⟨_,ih hn'.2 S hT hI,by simp [ind0,mark,bits_cons,ha]⟩
  let e := (Fintype.equivFinOfCardEq hw).symm
  refine ⟨fun i => mark vs (A (e i)), fun i => (A (e i)).card, ?_, ?_,
    e.sum_comp (fun i => (A i).card)⟩
  · intro i
    exact complete vs nodup _ (fun x _ => List.mem_toFinset.mpr (full x)) (rows _)
  · intro s t hm
    obtain ⟨S,_,cl,eq⟩ := sound vs nodup hm
    have val := congrArg Prod.fst eq
    have size := congrArg Prod.snd eq
    change s=mark vs S at val
    change t=S.card at size
    subst s t
    let J := (univ : Finset (Fin d)).filter fun i => mark vs (A (e i)) &&& mark vs S=0
    have dis (i) (hi : i∈J) : Disjoint (A (e i)) S := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (of_decide_eq_false ((and_mask vs _ _).mp (mem_filter.mp hi).2 x (full x) (by simpa using hx))) hy
    have bound := obstruction (J.map e.toEmbedding) S cl (by
      intro i hi
      obtain ⟨j,hj,rfl⟩ := mem_map.mp hi
      exact dis j hj)
    simpa only [Finset.card_map] using bound
end Ramsey39Contacts
namespace Ramsey39Contacts
open SimpleGraph Finset

/-- A classified anti-neighborhood and a row-cost certificate give an edge bound on the extension. -/
theorem encoded_extension {n m d threshold q : Nat} (code : List Nat)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (tri : G.CliqueFree 3)
    (ind : Gᶜ.CliqueFree 7) (v : Fin n) (hc : n-1-G.degree v=m) (hd : G.degree v=d)
    (small : (G.induce ((Gᶜ.neighborFinset v : Finset (Fin n)) : Set (Fin n))).edgeFinset.card≤threshold)
    (classify : ∀ (V : Type) [Fintype V] [DecidableEq V] (D : SimpleGraph V) [DecidableRel D.Adj],
      Fintype.card V=m → D.CliqueFree 3 → Dᶜ.CliqueFree 6 → D.edgeFinset.card≤threshold →
      let bits := fun bs : List Bool => bs.foldr (fun b k => 2*k+b.toNat) 0
      let enc := fun (ws : List V) => (ws.foldr (fun v (p : List V × List ℕ) =>
      (v::p.1, bits (p.1.map fun x => decide (D.Adj v x)) :: p.2)) ([],[])).2
      D.edgeFinset.card=threshold ∧ ∃ vs : List V, vs.Nodup ∧ (∀ x, x∈vs) ∧ enc vs=code)
    (numeric :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin d → Nat), (∀ i,(R i,K i)∈enum code) →
      (∀ s t, (s,t)∈enum code →
        ((univ : Finset (Fin d)).filter fun i => R i &&& s=0).card+t≤6) → q≤∑ i,K i) :
    threshold+d+q≤G.edgeFinset.card := by
  classical
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set (Fin n))
  let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
  have hn : Fintype.card N=d := by rw [Fintype.card_coe]; exact hd
  have hb : Fintype.card B=m := by
    rw [Fintype.card_coe]
    change Gᶜ.degree v=m
    simpa only [G.degree_compl,Fintype.card_fin] using hc
  obtain ⟨td, idc, rows, avoid, tot⟩ := neighborhood_data G v tri ind
  obtain ⟨size, vs, nd, full, labels⟩ := classify B D hb td idc small
  obtain ⟨R,K,eligible,disjointRows,totalRows⟩ := mask_rows D vs nd full A hn rows avoid
  have lower := numeric R K (labels ▸ eligible) (labels ▸ disjointRows)
  have removed := RamseyDeficiency.removed_eq G tri v
  change D.edgeFinset.card + (∑ i ∈ N, G.degree i) = _ at removed
  change N.card + (∑ i : N,(A i).card) ≤ ∑ i ∈ N, G.degree i at tot
  rw [Fintype.card_coe] at hn
  omega
end Ramsey39Contacts


/- Degree-profile arithmetic for the sparse triangle-free Ramsey graphs on 19 to 22 vertices. -/

namespace Ramsey39Small

/-- The child values are lower bounds for the number of edges outside a closed neighborhood.
    A child on at least 18 vertices only needs 41 edges. The 16-vertex bound 32 is used
    only at order 22. The two alternatives select a 14-vertex child with at most 20 edges
    or a 15-vertex child with at most 25 edges, respectively. -/
lemma seed_or_bound (n e : Nat) (hn : 19 ≤ n) (hn' : n ≤ 22)
    (deg child : Fin n → Nat) (hdeg : ∀ v, deg v ≤ 6)
    (hand : ∑ v, deg v = 2*e) (budget : ∑ v, (child v + (deg v)^2) ≤ n*e)
    (small : ∀ v, ([0,0,0,0,0,0,1,2,3,4,5,8,11,15,19,25,
      if n=22 then 32 else 31,38] : List Nat).getD (n-1-deg v) 41 ≤ child v) :
    (if n=22 then 59 else if n=21 then 51 else if n=20 then 44 else 37) ≤ e ∨
    ∃ v, (((n=19 ∧ deg v=4) ∨ (n=20 ∧ deg v=5)) ∧ child v ≤ 20) ∨
         (((n=20 ∧ deg v=4) ∨ (n=21 ∧ deg v=5)) ∧ child v ≤ 25) := by
  classical
  by_cases hs : ∃ v, (((n=19 ∧ deg v=4) ∨ (n=20 ∧ deg v=5)) ∧ child v ≤ 20) ∨
                      (((n=20 ∧ deg v=4) ∨ (n=21 ∧ deg v=5)) ∧ child v ≤ 25)
  · exact Or.inr hs
  left
  let lo (N d : Nat) := ([0,0,0,0,0,0,1,2,3,4,5,8,11,15,19,25,
    if N=22 then 32 else 31,38] : List Nat).getD (N-1-d) 41
  let raise (N d : Nat) := if (N=19 ∧ d=4) ∨ (N=20 ∧ d=5) then 21 else
    if (N=20 ∧ d=4) ∨ (N=21 ∧ d=5) then 26 else 0
  let base (N : Nat) := if N=22 then 37 else if N=21 then 31 else if N=20 then 26 else 25
  let slope (N : Nat) := if N=19 then 3 else 4
  have high (v : Fin n) : raise n (deg v) ≤ child v := by
    dsimp only [raise]
    split_ifs with h1 h2
    · by_contra! hh
      exact hs ⟨v, Or.inl ⟨h1, by omega⟩⟩
    · by_contra! hh
      exact hs ⟨v, Or.inr ⟨h2, by omega⟩⟩
    · omega
  have cert : ∀ i : Fin 4, ∀ t : Fin 7,
      base (19+i.val) + slope (19+i.val)*t.val ≤
      max (lo (19+i.val) t.val) (raise (19+i.val) t.val) + t.val^2 := by
    dsimp only [base, slope, lo, raise]
    decide
  have hcost (v : Fin n) : base n + slope n * deg v ≤ child v + (deg v)^2 := by
    have c := cert ⟨n-19, by omega⟩ ⟨deg v, by have := hdeg v; omega⟩
    change base (19+(n-19)) + slope (19+(n-19))*deg v ≤
      max (lo (19+(n-19)) (deg v)) (raise (19+(n-19)) (deg v)) + (deg v)^2 at c
    rw [show 19+(n-19)=n by omega] at c
    exact c.trans (Nat.add_le_add_right (max_le (small v) (high v)) _)
  have hsum : n * base n + slope n * (2*e) ≤ n*e := calc
    _ = ∑ v : Fin n, (base n + slope n * deg v) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hand]
      simp
    _ ≤ ∑ v, (child v + (deg v)^2) := Finset.sum_le_sum (fun v _ => hcost v)
    _ ≤ _ := budget
  interval_cases n <;> norm_num [base, slope] at hsum ⊢ <;> omega

end Ramsey39Small


/- The dual certificate assigns a weight to each test independent set.
A row earns its own cardinality contribution and the weights of tests that
it misses. The contact inequalities cap the total missed weight. -/

namespace Ramsey39Contacts
open Finset

lemma weighted_cost {d m c q : ℕ} (rows : List (ℕ × ℕ))
    (tests : List ((ℕ × ℕ) × ℕ)) (R K : Fin d → ℕ)
    (memRows : ∀ i, (R i,K i) ∈ rows)
    (cap : ∀ s t, (s,t) ∈ rows →
      ((univ : Finset (Fin d)).filter fun i => R i &&& s = 0).card + t ≤ 6)
    (valid : ∀ z ∈ tests, z.1 ∈ rows)
    (each : ∀ p ∈ rows, c ≤ m*p.2 +
      (tests.map (fun z => if p.1 &&& z.1.1 = 0 then z.2 else 0)).sum)
    (gap : (tests.map (fun z => (6-z.1.2)*z.2)).sum + m*(q-1) < d*c) :
    q ≤ ∑ i, K i := by
  have bound (xs : List ((ℕ × ℕ) × ℕ)) (hx : ∀ z ∈ xs, z.1 ∈ rows) :
      (∑ i, (xs.map (fun z => if R i &&& z.1.1 = 0 then z.2 else 0)).sum) ≤
      (xs.map (fun z => (6-z.1.2)*z.2)).sum := by
    induction xs with
    | nil => simp
    | cons z xs ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      have hc := cap z.1.1 z.1.2 (hx z (by simp))
      have eq : (∑ i : Fin d, if R i &&& z.1.1 = 0 then z.2 else 0) =
          ((univ : Finset (Fin d)).filter fun i => R i &&& z.1.1 = 0).card * z.2 := by
        rw [← Finset.sum_filter]
        simp
      rw [eq]
      exact Nat.add_le_add (Nat.mul_le_mul_right _ (by omega))
        (ih (fun w hw => hx w (List.mem_cons_of_mem _ hw)))
  have h := Finset.sum_le_sum (s := (univ : Finset (Fin d)))
    (fun i _ => each (R i,K i) (memRows i))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at h
  have hb := bound tests valid
  by_contra! no
  have bad := Nat.mul_le_mul_left m (show (∑ i, K i) ≤ q-1 by omega)
  omega


set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem cost14_four :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 4 → Nat), (∀ i, (R i,K i) ∈ enum [129,512,65,64,259,66,18,6,8,8,4,1,1,0]) →
      (∀ s t, (s,t) ∈ enum [129,512,65,64,259,66,18,6,8,8,4,1,1,0] →
        ((Finset.univ : Finset (Fin 4)).filter fun i => R i &&& s = 0).card + t ≤ 6) →
        13 ≤ ∑ i,K i := by
  intro enum R K hr hc
  let tests : List ((ℕ × ℕ) × ℕ) := [((794,5),12),((810,5),12),((1302,5),12),((1318,5),12),((1810,5),17),((1826,5),14),((2585,5),12),((2601,5),12),((2840,5),14),((2856,5),17),((3093,5),12),((3109,5),12),((3348,5),14),((3364,5),17),((3601,5),16),((3617,5),14),((3856,5),20),((3872,5),20),((4240,3),14),((4245,5),14),((4246,5),14),((4249,5),14),((4250,5),14),((4288,3),9),((4293,5),4),((4294,5),4),((4297,5),4),((4298,5),4),((4633,5),9),((4634,5),9),((4681,5),21),((4682,5),21),((5141,5),9),((5142,5),9),((5189,5),21),((5190,5),21),((5649,5),6),((5650,5),5),((5697,5),28),((5698,5),28),((8288,3),14),((8293,5),14),((8294,5),14),((8297,5),14),((8298,5),14),((8384,3),11),((8389,5),3),((8390,5),3),((8393,5),3),((8394,5),3),((8486,5),9),((8490,5),9),((8582,5),21),((8586,5),21),((10277,5),9),((10281,5),9),((10373,5),21),((10377,5),21),((10532,5),5),((10536,5),5),((10628,5),28),((10632,5),28)]
  apply weighted_cost (m := 76) (c := 458) (enum [129,512,65,64,259,66,18,6,8,8,4,1,1,0]) tests R K hr hc
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem cost14_five :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [129,512,65,64,259,66,18,6,8,8,4,1,1,0]) →
      (∀ s t, (s,t) ∈ enum [129,512,65,64,259,66,18,6,8,8,4,1,1,0] →
        ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card + t ≤ 6) →
        19 ≤ ∑ i,K i := by
  intro enum R K hr hc
  let tests : List ((ℕ × ℕ) × ℕ) := [((794,5),4),((810,5),4),((1302,5),4),((1318,5),4),((1810,5),2),((1826,5),6),((2585,5),4),((2601,5),4),((2840,5),6),((2856,5),2),((3093,5),4),((3109,5),4),((3348,5),6),((3364,5),2),((3601,5),2),((3617,5),6),((3856,5),6),((3872,5),6),((4240,3),4),((4245,5),4),((4246,5),4),((4249,5),4),((4250,5),4),((4288,3),2),((4293,5),1),((4294,5),1),((4297,5),1),((4298,5),1),((4633,5),2),((4634,5),2),((4681,5),7),((4682,5),7),((5141,5),2),((5142,5),2),((5189,5),7),((5190,5),7),((5649,5),4),((5650,5),4),((5696,4),2),((5697,5),6),((5698,5),6),((8288,3),4),((8293,5),4),((8294,5),4),((8297,5),4),((8298,5),4),((8389,5),2),((8390,5),2),((8393,5),2),((8394,5),2),((8486,5),2),((8490,5),2),((8582,5),7),((8586,5),7),((10277,5),2),((10281,5),2),((10373,5),7),((10377,5),7),((10532,5),4),((10536,5),4),((10624,4),2),((10628,5),6),((10632,5),6)]
  apply weighted_cost (m := 18) (c := 119) (enum [129,512,65,64,259,66,18,6,8,8,4,1,1,0]) tests R K hr hc
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem cost15_four :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 4 → Nat), (∀ i, (R i,K i) ∈ enum [515,2112,260,67,528,64,131,34,4,4,3,2,2,1,0]) →
      (∀ s t, (s,t) ∈ enum [515,2112,260,67,528,64,131,34,4,4,3,2,2,1,0] →
        ((Finset.univ : Finset (Fin 4)).filter fun i => R i &&& s = 0).card + t ≤ 6) →
        15 ≤ ∑ i,K i := by
  intro enum R K hr hc
  let tests : List ((ℕ × ℕ) × ℕ) := [((433,5),4),((1138,5),2),((1174,5),2),((1606,5),2),((2162,5),2),((2634,5),2),((2657,5),2),((4174,5),2),((4246,5),2),((4492,5),2),((6217,5),5),((6218,5),4),((6225,5),1),((6226,5),5),((6281,5),4),((6289,5),5),((6290,5),6),((8780,5),2),((8801,5),2),((8969,5),2),((9328,5),6),((9492,5),4),((9520,5),5),((9796,5),4),((9824,5),5),((9988,5),5),((10016,5),1),((12364,5),4),((12369,5),4),((12372,5),5),((12553,5),6),((12556,5),5),((12561,5),5),((12564,5),1),((16780,5),2),((16910,5),2),((17161,5),2),((17542,5),5),((17570,5),1),((17796,5),6),((17824,5),5),((17926,5),4),((17954,5),5),((18208,5),4),((18569,5),1),((18570,5),5),((18593,5),5),((18594,5),4),((18953,5),5),((18954,5),4),((18977,5),6)]
  apply weighted_cost (m := 13) (c := 92) (enum [515,2112,260,67,528,64,131,34,4,4,3,2,2,1,0]) tests R K hr hc
  · decide +kernel
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem cost15_five :
    let enum : List Nat → List (Nat × Nat) := List.foldr (fun m t =>
      t.map (fun p => (2*p.1,p.2)) ++
      (t.filter fun p => m &&& p.1 == 0).map (fun p => (2*p.1+1,p.2+1))) [(0,0)]
    ∀ (R K : Fin 5 → Nat), (∀ i, (R i,K i) ∈ enum [515,2112,260,67,528,64,131,34,4,4,3,2,2,1,0]) →
      (∀ s t, (s,t) ∈ enum [515,2112,260,67,528,64,131,34,4,4,3,2,2,1,0] →
        ((Finset.univ : Finset (Fin 5)).filter fun i => R i &&& s = 0).card + t ≤ 6) →
        21 ≤ ∑ i,K i := by
  intro enum R K hr hc
  let tests : List ((ℕ × ℕ) × ℕ) := [((1110,5),3),((1138,5),2),((1174,5),2),((1202,5),3),((1456,5),4),((1606,5),4),((2161,5),3),((2162,5),2),((2225,5),4),((2634,5),4),((2657,5),2),((2658,5),3),((4174,5),4),((4238,5),3),((4246,5),2),((4492,5),2),((4497,5),4),((4500,5),3),((6217,5),4),((6218,5),4),((6226,5),8),((6281,5),4),((6289,5),4),((6290,5),8),((8497,5),4),((8777,5),3),((8780,5),4),((8801,5),2),((8969,5),2),((8993,5),3),((9328,5),8),((9492,5),4),((9520,5),4),((9796,5),4),((9824,5),8),((9988,5),4),((12364,5),4),((12369,5),4),((12372,5),4),((12553,5),8),((12556,5),8),((12561,5),4),((16777,5),3),((16780,5),2),((16801,5),4),((16910,5),4),((17161,5),2),((17164,5),3),((17542,5),8),((17796,5),8),((17824,5),4),((17926,5),4),((17954,5),4),((18208,5),4),((18570,5),4),((18593,5),4),((18594,5),4),((18953,5),8),((18954,5),4),((18977,5),8)]
  apply weighted_cost (m := 14) (c := 109) (enum [515,2112,260,67,528,64,131,34,4,4,3,2,2,1,0]) tests R K hr hc
  · decide +kernel
  · decide +kernel
  · decide +kernel

end Ramsey39Contacts


namespace Ramsey39Checked
open SimpleGraph Finset OMA.RamseyFinite

def catalogue (m threshold : Nat) (code : List Nat) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (D : SimpleGraph V) [DecidableRel D.Adj],
      Fintype.card V=m → D.CliqueFree 3 → Dᶜ.CliqueFree 6 → D.edgeFinset.card≤threshold →
      let bits := fun bs : List Bool => bs.foldr (fun b k => 2*k+b.toNat) 0
      let enc := fun (ws : List V) => (ws.foldr (fun v (p : List V × List ℕ) =>
      (v::p.1, bits (p.1.map fun x => decide (D.Adj v x)) :: p.2)) ([],[])).2
      D.edgeFinset.card=threshold ∧ ∃ vs : List V, vs.Nodup ∧ (∀ x, x∈vs) ∧ enc vs=code

theorem classify14 : catalogue 14 20 final14 := by
  intro V ft de G di hn tri ind small
  apply realize_sparse_label G (code:=final14) (by decide)
  apply classify_from_grow (n:=14) (cap:=2) (budget:=20) final14 normalizeFinal G hn
    (by decide) (by decide) tri ind small
  · exact normalizeFinal_real G
  · intro d hd b hb cs ext ord grown size
    exact class14 d hd b cs hb ext ord grown size

theorem classify15 : catalogue 15 25 final15 := by
  intro V ft de G di hn tri ind small
  apply realize_sparse_label G (code:=final15) (by decide)
  apply classify_from_grow (n:=15) (cap:=3) (budget:=25) final15 normalizeFinal G hn
    (by decide) (by decide) tri ind small
  · exact normalizeFinal_real G
  · intro d hd b hb cs ext ord grown size
    exact class15 d hd b cs hb ext ord grown size

end Ramsey39Checked

open Ramsey39Small Ramsey39Contacts Ramsey39Checked


theorem OMA.solution : OMA.R_RamseyNumbers_ramsey_number_three_nine_R2.H1 := by
  intro n hn hn' G dec tri ind
  classical
  let child (v : Fin n) :=
    (G.induce ((Gᶜ.neighborFinset v : Finset (Fin n)) : Set (Fin n))).edgeFinset.card
  have cap (v : Fin n) : G.degree v≤6 := degree_cap G tri ind v
  have budget := deficiency_of_local G child (fun v => (RamseyDeficiency.removed_eq G tri v).le)
  have small (v : Fin n) : ([0,0,0,0,0,0,1,2,3,4,5,8,11,15,19,25,
      if n=22 then 32 else 31,38] : List Nat).getD (n-1-G.degree v) 41 ≤ child v := by
    obtain ⟨K, di, tk, ik, sub⟩ :=
      RamseyDeficiency.extract_anti (m:=n-1-G.degree v) G tri ind v
        (by rw [G.degree_compl, Fintype.card_fin])
    have hm : 12≤n-1-G.degree v := by have := cap v; omega
    exact (@child_table n _ Ramsey39Full.density16 hm K di tk ik).trans sub
  obtain bound | ⟨v, alternatives⟩ := seed_or_bound n G.edgeFinset.card hn hn' (fun v => G.degree v) child cap
    G.sum_degrees_eq_twice_card_edges budget small
  · exact bound
  rcases alternatives with ⟨casesN,cut⟩ | ⟨casesN,cut⟩
  · rcases casesN with ⟨rfl,hd⟩ | ⟨rfl,hd⟩
    · exact encoded_extension (d:=4) (q:=13) _ G tri ind v (by omega) hd cut classify14 cost14_four
    · exact encoded_extension (d:=5) (q:=19) _ G tri ind v (by omega) hd cut classify14 cost14_five
  · rcases casesN with ⟨rfl,hd⟩ | ⟨rfl,hd⟩
    · exact encoded_extension (d:=4) (q:=15) _ G tri ind v (by omega) hd cut classify15 cost15_four
    · exact encoded_extension (d:=5) (q:=21) _ G tri ind v (by omega) hd cut classify15 cost15_five

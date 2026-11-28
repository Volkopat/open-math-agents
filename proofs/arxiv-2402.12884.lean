import OMAStatements.S_arxiv_2402_12884
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace AkbariRandic
open SimpleGraph Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def weight : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => (Real.sqrt ((G.degree u : ℝ) * G.degree v))⁻¹,
    fun _ _ => by dsimp; rw [mul_comm]⟩

noncomputable def randic : ℝ := ∑ e ∈ G.edgeFinset, weight G e

omit [DecidableEq V] in
theorem weight_nonneg (e : Sym2 V) : 0 ≤ weight G e := by
  induction e using Sym2.ind with
  | h a b => exact inv_nonneg.mpr (Real.sqrt_nonneg _)

omit [DecidableEq V] in
theorem randic_nonneg : 0 ≤ randic G := sum_nonneg (fun e _ => weight_nonneg G e)

omit [DecidableEq V] in
theorem real_degree_sum :
    (∑ v : V, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

def dartProd (d : G.Dart) : ℝ := (G.degree d.fst : ℝ) * G.degree d.snd

omit [DecidableEq V] in
theorem dartProd_pos (d : G.Dart) : 0 < dartProd G d := by
  unfold dartProd
  exact mul_pos (by exact_mod_cast (G.degree_pos_iff_exists_adj _).mpr ⟨_,d.adj⟩)
    (by exact_mod_cast (G.degree_pos_iff_exists_adj _).mpr ⟨_,d.adj.symm⟩)

omit [DecidableEq V] in
theorem sum_dart_prod :
    (∑ d : G.Dart, dartProd G d) ≤ (2 * (G.edgeFinset.card : ℝ))^2 := by
  let f : V × V → ℝ := fun p => (G.degree p.1 : ℝ) * G.degree p.2
  let emb : G.Dart ↪ V × V := ⟨fun d => d.toProd, by
    intro a b h
    cases a
    cases b
    congr⟩
  calc
    _ = ∑ p ∈ (univ : Finset G.Dart).map emb, f p := (sum_map _ _ _).symm
    _ ≤ ∑ p : V × V, f p := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun p _ _ => by
      dsimp [f]; positivity)
    _ = (2 * (G.edgeFinset.card : ℝ))^2 := by
      rw [← univ_product_univ, sum_product]
      change (∑ a : V, ∑ b : V, (G.degree a : ℝ) * G.degree b) = _
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, real_degree_sum]
      ring

theorem sum_dart_recip :
    (∑ d : G.Dart, (Real.sqrt (dartProd G d))⁻¹) = 2 * randic G := by
  have hm (d : G.Dart) (_ : d ∈ (univ : Finset G.Dart)) :
      d.edge ∈ G.edgeFinset := mem_edgeFinset.mpr d.edge_mem
  have h := Finset.sum_fiberwise_of_maps_to' hm (weight G)
  change (∑ d : G.Dart, weight G d.edge) = _
  rw [← h,randic,Finset.mul_sum]
  apply sum_congr rfl
  intro e he
  rw [sum_const, G.dart_edge_fiber_card e (mem_edgeFinset.mp he)]
  norm_num

theorem edge_count_le_two_randic_sq :
    (G.edgeFinset.card : ℝ) ≤ 2 * randic G ^ 2 := by
  let N : ℝ := 2 * (G.edgeFinset.card : ℝ)
  let s := ∑ d : G.Dart, Real.sqrt (dartProd G d)
  have n_card : (Fintype.card G.Dart : ℝ) = N := by
    dsimp [N]; exact_mod_cast G.dart_card_eq_twice_card_edges
  have hs : 0 ≤ s := sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hR := randic_nonneg G
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have A : N^2 ≤ s * (2 * randic G) := by
    have c := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset G.Dart)
      (r := fun _ => (1:ℝ)) (f := fun d => Real.sqrt (dartProd G d))
      (g := fun d => (Real.sqrt (dartProd G d))⁻¹)
      (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
      (fun d _ => by rw [mul_inv_cancel₀ (Real.sqrt_pos_of_pos (dartProd_pos G d)).ne']; norm_num)
    simpa [s, sum_dart_recip, n_card] using c
  have B : s^2 ≤ N^3 := by
    have c := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset G.Dart)
      (r := fun d => Real.sqrt (dartProd G d)) (f := fun _ => (1:ℝ)) (g := dartProd G)
      (fun _ _ => zero_le_one) (fun d _ => (dartProd_pos G d).le)
      (fun d _ => by rw [Real.sq_sqrt (dartProd_pos G d).le, one_mul])
    have c' : s^2 ≤ N * (∑ d : G.Dart, dartProd G d) := by simpa [s,n_card] using c
    calc
      _ ≤ N * N^2 := c'.trans (mul_le_mul_of_nonneg_left (sum_dart_prod G) hN)
      _ = _ := by ring
  by_cases bz : N = 0
  · dsimp [N] at bz; nlinarith [sq_nonneg (randic G)]
  have hn : 0 < N := lt_of_le_of_ne hN (Ne.symm bz)
  have C : N^2 * N^2 ≤ (s * (2*randic G)) * (s * (2*randic G)) :=
    mul_le_mul A A (sq_nonneg _) (by positivity)
  have D := mul_le_mul_of_nonneg_right B (sq_nonneg (2*randic G))
  have E : N^3 * N ≤ N^3 * (2*randic G)^2 := by
    calc
      _ = N^2 * N^2 := by ring
      _ ≤ (s * (2*randic G)) * (s * (2*randic G)) := C
      _ = s^2 * (2*randic G)^2 := by ring
      _ ≤ _ := D
  have e := le_of_mul_le_mul_left E (pow_pos hn 3)
  dsimp [N] at e
  nlinarith
end AkbariRandic

namespace LtSAkbari
open SimpleGraph Finset
open scoped BigOperators
variable {n : ℕ} (G : SimpleGraph (Fin n))

open OMA.S_arxiv_2402_12884

section
open Classical
noncomputable local instance : DecidableRel G.Adj := Classical.decRel _

private def dst : G.Dart ↪ Fin n × Fin n :=
  ⟨fun d => d.toProd, by
    intro a b h
    cases a
    cases b
    congr⟩

private theorem darts_eq : darts G = (univ : Finset G.Dart).map (dst G) := by
  ext e
  rcases e with ⟨u,v⟩
  constructor
  · intro h
    have ha : G.Adj u v := (mem_filter.mp h).2
    exact mem_map.mpr ⟨⟨(u,v),ha⟩,mem_univ _,rfl⟩
  · intro h
    obtain ⟨d,_,hd⟩ := mem_map.mp h
    have ha := d.adj
    change d.toProd = (u,v) at hd
    exact mem_filter.mpr ⟨mem_univ _, hd ▸ ha⟩

private theorem randic_eq : randic G = AkbariRandic.randic G := by
  unfold randic
  rw [darts_eq, sum_map]
  have he := AkbariRandic.sum_dart_recip G
  change (∑ d : G.Dart, (Real.sqrt (AkbariRandic.dartProd G d))⁻¹) / 2 = _
  linarith

private theorem matched_bound {M : Finset (Fin n × Fin n)} (hM : isMatching G M) :
    ((M.card / 2 : ℕ) : ℝ)^2 ≤ (G.edgeFinset.card : ℝ) * AkbariRandic.randic G := by
  let p (e : Fin n × Fin n) : ℝ := (G.degree e.1 : ℝ) * G.degree e.2
  let s (e : Fin n × Fin n) := Real.sqrt (p e)
  have hp (e) (he : e ∈ M) : 0 < p e := by
    have ha : G.Adj e.1 e.2 := (mem_filter.mp (hM.1 he)).2
    exact AkbariRandic.dartProd_pos G (⟨e,ha⟩ : G.Dart)
  have hweight : (∑ e ∈ M, (s e)⁻¹) ≤ 2 * AkbariRandic.randic G := by
    have w := sum_le_sum_of_subset_of_nonneg hM.1 (fun e _ _ => inv_nonneg.mpr (Real.sqrt_nonneg (p e)))
    rw [darts_eq, sum_map] at w
    exact w.trans_eq (AkbariRandic.sum_dart_recip G)
  have hfst : (∑ e ∈ M, (G.degree e.1 : ℝ)) ≤ 2 * (G.edgeFinset.card : ℝ) := by
    rw [← AkbariRandic.real_degree_sum]
    calc
      _ = ∑ v ∈ M.image Prod.fst, (G.degree v : ℝ) := by
        rw [sum_image (fun a ha b hb hab => hM.2.2 ha hb hab)]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
  have hsnd : (∑ e ∈ M, (G.degree e.2 : ℝ)) = ∑ e ∈ M, (G.degree e.1 : ℝ) := by
    apply Finset.sum_bij (fun e _ => e.swap)
    · exact hM.2.1
    · intro a _ b _ eq
      exact congrArg Prod.swap eq
    · intro b hb
      exact ⟨b.swap,hM.2.1 b hb,rfl⟩
    · intro a _
      rfl
  have hs : (∑ e ∈ M, s e) ≤ 2 * (G.edgeFinset.card : ℝ) := by
    have hterm (e) (he : e ∈ M) : 2 * s e ≤ (G.degree e.1 : ℝ) + G.degree e.2 :=
      two_mul_le_add_of_sq_le_mul (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Real.sq_sqrt (hp e he).le).le
    have h := sum_le_sum hterm
    rw [← mul_sum, sum_add_distrib, hsnd] at h
    linarith
  have c := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul M
    (r := fun _ => (1:ℝ)) (f := s) (g := fun e => (s e)⁻¹)
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
    (fun e he => by rw [mul_inv_cancel₀ (Real.sqrt_pos_of_pos (hp e he)).ne']; norm_num)
  have c' : (M.card : ℝ)^2 ≤ (∑ e ∈ M, s e) * ∑ e ∈ M, (s e)⁻¹ := by simpa using c
  have hs0 : 0 ≤ ∑ e ∈ M, (s e)⁻¹ := sum_nonneg (fun e _ => inv_nonneg.mpr (Real.sqrt_nonneg (p e)))
  have bd := c'.trans (mul_le_mul hs hweight hs0 (by positivity))
  have hd : 2 * ((M.card / 2 : ℕ) : ℝ) ≤ M.card := by
    exact_mod_cast (show 2 * (M.card / 2) ≤ M.card by omega)
  have sq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * ((M.card / 2 : ℕ) : ℝ)) hd 2
  nlinarith

theorem matching_cube_bound :
    (matchingNumber G : ℝ)^2 ≤ 2 * (AkbariRandic.randic G)^3 := by
  classical
  have hR : 0 ≤ AkbariRandic.randic G := AkbariRandic.randic_nonneg G
  have hed := AkbariRandic.edge_count_le_two_randic_sq G
  let S := (darts G).powerset.filter (isMatching G)
  have hbound : ∀ M ∈ S, ((M.card / 2 : ℕ) : ℝ)^2 ≤
      (G.edgeFinset.card : ℝ) * AkbariRandic.randic G := by
    intro M hM
    exact matched_bound G (mem_filter.mp hM).2
  have hm : (matchingNumber G : ℝ)^2 ≤
      (G.edgeFinset.card : ℝ) * AkbariRandic.randic G := by
    by_cases hS : S.Nonempty
    · obtain ⟨M,hM,hmax⟩ := exists_max_image S (fun M => M.card/2) hS
      have he : matchingNumber G = M.card / 2 := by
        change S.sup _ = _
        exact le_antisymm (Finset.sup_le (fun N hN => hmax N hN)) (Finset.le_sup (f := fun M => M.card / 2) hM)
      rw [he]
      exact hbound M hM
    · have e : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      change ((S.sup (fun M => M.card / 2) : ℕ) : ℝ)^2 ≤ _
      rw [e]
      simp
      positivity
  calc
    _ ≤ _ := hm
    _ ≤ (2 * AkbariRandic.randic G ^ 2) * AkbariRandic.randic G := mul_le_mul_of_nonneg_right hed hR
    _ = _ := by ring

theorem explicit_bound :
    (2 : ℝ) ^ (-(1/3) : ℝ) * (matchingNumber G : ℝ) ^ (2/3 : ℝ) ≤ randic G := by
  let x : ℝ := matchingNumber G
  let c : ℝ := (2 : ℝ) ^ (-(1/3) : ℝ)
  have hx : 0 ≤ x := Nat.cast_nonneg _
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  rw [randic_eq G]
  have hr := AkbariRandic.randic_nonneg G
  have cube (u : ℝ) (hu : 0 ≤ u) (a : ℝ) :
      (u ^ a)^3 = u ^ (a * 3 : ℝ) := by
    rw [Real.rpow_mul hu, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  have cx : (x ^ (2/3 : ℝ))^3 = x^2 := by
    rw [cube _ hx, show (2/3 : ℝ)*3 = (2 : ℕ) by norm_num, Real.rpow_natCast]
  have cc : c^3 = 1/2 := by
    dsimp [c]
    rw [cube _ (by norm_num),show (-(1/3) : ℝ)*3 = -1 by norm_num,Real.rpow_neg (by norm_num), Real.rpow_one]
    norm_num
  change c * x ^ (2/3 : ℝ) ≤ AkbariRandic.randic G
  apply (pow_le_pow_iff_left₀ (mul_nonneg hc.le (Real.rpow_nonneg hx _)) hr (by decide : (3:ℕ) ≠ 0)).mp
  rw [mul_pow, cc, cx]
  have h : x ^ 2 ≤ 2 * AkbariRandic.randic G ^ 3 := matching_cube_bound G
  linarith

theorem exact_target :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      c * (matchingNumber G : ℝ) ^ (2/3 : ℝ) ≤ randic G :=
  ⟨_,Real.rpow_pos_of_pos (by norm_num) _, fun _ G => explicit_bound G⟩

end
end LtSAkbari

theorem OMA.solution : type_of% @OMA.S_arxiv_2402_12884.main :=
  LtSAkbari.exact_target

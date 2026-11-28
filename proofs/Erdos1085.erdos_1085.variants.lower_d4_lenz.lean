import FormalConjectures.ErdosProblems.«1085»
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-! Shorter proof of `Erdos1085.erdos_1085.variants.lower_d4_lenz`. -/

open scoped EuclideanGeometry Finset Sym2

theorem OMA.solution : type_of% @Erdos1085.erdos_1085.variants.lower_d4_lenz := by
  classical
  intro d hd
  let p := d / 2
  have hp : 0 < p := by omega
  have hpd : 2 * p ≤ d := by omega
  refine ⟨(p : ℝ) ^ 2 + 1, fun n => ?_⟩
  let a (i : Fin n) : Fin d := ⟨2 * ((i : ℕ) % p), by have := Nat.mod_lt (i : ℕ) hp; omega⟩
  let b (i : Fin n) : Fin d := ⟨2 * ((i : ℕ) % p) + 1, by have := Nat.mod_lt (i : ℕ) hp; omega⟩
  have hab (i j : Fin n) : a i ≠ b j := fun h => by
    have := congrArg Fin.val h; dsimp [a, b] at this; omega
  have ha (i j : Fin n) : a i = a j ↔ (i : ℕ) % p = (j : ℕ) % p := by
    rw [← Fin.val_inj]; dsimp [a]; omega
  have hb (i j : Fin n) : b i = b j ↔ (i : ℕ) % p = (j : ℕ) % p := by
    rw [← Fin.val_inj]; dsimp [b]; omega
  let x (i : Fin n) : ℝ := 1 / ((i.val : ℝ) + 4)
  let y (i : Fin n) : ℝ := Real.sqrt (1 / 2 - x i ^ 2)
  have hx (i : Fin n) : 0 < x i := by dsimp [x]; positivity
  have hxy (i : Fin n) : x i ^ 2 + y i ^ 2 = 1 / 2 := by
    have h1 : x i ≤ 1 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (by linarith [Nat.cast_nonneg (α := ℝ) i.val])
    rw [show y i ^ 2 = 1 / 2 - x i ^ 2 from Real.sq_sqrt (by nlinarith [hx i])]; ring
  let v (i : Fin n) : ℝ^d :=
    WithLp.toLp 2 fun c => if c = a i then x i else if c = b i then y i else 0
  have hv (i : Fin n) (c : Fin d) :
      v i c = if c = a i then x i else if c = b i then y i else 0 := rfl
  have hnorm (i : Fin n) : ∑ c, (v i c) ^ 2 = 1 / 2 := by
    have ht (c : Fin d) :
        (v i c) ^ 2 = (if c = a i then x i ^ 2 else 0) + (if c = b i then y i ^ 2 else 0) := by
      rw [hv]; by_cases h : c = a i
      · subst c; simp [hab]
      · by_cases h' : c = b i <;> simp [h, h', (hab i i).symm]
    simp_rw [ht]; rw [Finset.sum_add_distrib]; simpa using hxy i
  have hinj : Function.Injective v := fun i j hij => by
    have hc := congrArg (fun z : ℝ^d => z (a i)) hij; rw [hv, hv, if_pos rfl] at hc
    by_cases h : a i = a j
    · rw [if_pos h] at hc
      have hm := (div_eq_div_iff (by positivity) (by positivity)).mp hc
      have hval : (i.val : ℝ) + 4 = j.val + 4 := by simpa [x] using hm.symm
      exact Fin.ext (by exact_mod_cast add_right_cancel hval)
    · rw [if_neg h, if_neg (hab i j)] at hc; exact ((hx i).ne' hc).elim
  have hdist (i j : Fin n) (h : (i : ℕ) % p ≠ (j : ℕ) % p) : dist (v i) (v j) = 1 := by
    have ht (c : Fin d) : (v i c - v j c) ^ 2 = (v i c) ^ 2 + (v j c) ^ 2 := by
      by_cases h1 : c = a i
      · subst c; rw [show v j (a i) = 0 by simp [hv, (ha i j).not.mpr h, hab]]; ring
      · by_cases h2 : c = b i
        · subst c; rw [show v j (b i) = 0 by simp [hv, (hab j i).symm, (hb i j).not.mpr h]]; ring
        · rw [show v i c = 0 by simp [hv, h1, h2]]; ring
    have hsq : dist (v i) (v j) ^ 2 = 1 := by
      rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]; simp_rw [PiLp.sub_apply, ht]
      rw [Finset.sum_add_distrib, hnorm i, hnorm j]; norm_num
    nlinarith [dist_nonneg (x := v i) (y := v j)]
  let ve : Fin n ↪ (ℝ^d) := ⟨v, hinj⟩
  let S : Finset (ℝ^d) := Finset.univ.map ve
  have hedge : (SimpleGraph.turanGraph n p).edgeFinset.card ≤ unitDistNum S := by
    unfold unitDistNum
    refine Finset.card_le_card_of_injOn (Sym2.map ve) (fun e he => ?_)
      (Sym2.map.injective hinj).injOn
    induction e using Sym2.inductionOn with
    | _ i j =>
      have hij : (i : ℕ) % p ≠ (j : ℕ) % p := SimpleGraph.turanGraph_adj.mp
        ((SimpleGraph.mem_edgeSet (G := SimpleGraph.turanGraph n p)).mp
          ((SimpleGraph.mem_edgeFinset (G := SimpleGraph.turanGraph n p)).mp he))
      change s(ve i, ve j) ∈ _
      refine Finset.mem_filter.mpr ⟨Finset.mk_mem_sym2_iff.mpr
        ⟨Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩,
         Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩, ?_⟩
      have hout : s((Quot.out s(ve i, ve j)).1, (Quot.out s(ve i, ve j)).2) = s(ve i, ve j) :=
        Quot.out_eq _
      rcases Sym2.eq_iff.mp hout with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂]; exact hdist i j hij
      · rw [h₁, h₂, dist_comm]; exact hdist i j hij
  have hle : (SimpleGraph.turanGraph n p).edgeFinset.card ≤ Erdos1085.f d n := hedge.trans <| by
    unfold Erdos1085.f
    refine le_ciSup₂ (f := fun (T : Finset (ℝ^d)) (_ : T.card = n) => unitDistNum T)
      ⟨n.choose 2, fun k hk => ?_⟩ S (by simp [S])
    rcases Set.mem_iUnion.mp hk with ⟨T, hT⟩
    obtain ⟨hc, rfl⟩ := Set.mem_range.mp hT
    simpa only [hc] using unitDistNum_le_choose_two T
  refine le_trans ?_ (by exact_mod_cast hle :
    ((SimpleGraph.turanGraph n p).edgeFinset.card : ℝ) ≤ Erdos1085.f d n)
  let r := n % p; let A := (n ^ 2 - r ^ 2) * (p - 1); let B := 2 * p
  have hB : 0 < B := by omega
  have hsub : r ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (Nat.mod_le _ _) _
  have hflR : (A : ℝ) < ((A / B : ℕ) + (1 : ℝ)) * B := by
    exact_mod_cast (Nat.div_lt_iff_lt_mul hB).mp (by omega : A / B < A / B + 1)
  have hdiv : (A : ℝ) / B - 1 ≤ (A / B : ℕ) := by
    linarith [(div_lt_iff₀ (by exact_mod_cast hB : (0 : ℝ) < B)).mpr hflR]
  have hcoef : ((p - 1 : ℕ) : ℝ) / (2 * (p : ℝ)) ≤ 1 :=
    (div_le_iff₀ (by positivity)).mpr
      (by linarith [show ((p - 1 : ℕ) : ℝ) ≤ p by exact_mod_cast Nat.sub_le p 1])
  have herr : ((p - 1 : ℕ) : ℝ) / (2 * (p : ℝ)) * (r : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)).trans <| by
      simpa using (show (r : ℝ) ^ 2 ≤ p ^ 2 by
        exact_mod_cast Nat.pow_le_pow_left (Nat.mod_lt _ hp).le 2)
  rw [show (A : ℝ) = ((n : ℝ) ^ 2 - (r : ℝ) ^ 2) * ((p - 1 : ℕ) : ℝ) by
      simp only [A, Nat.cast_mul, Nat.cast_sub hsub, Nat.cast_pow],
    show (B : ℝ) = 2 * (p : ℝ) by simp [B], sub_mul, sub_div,
    mul_div_assoc, mul_comm ((n : ℝ) ^ 2), mul_div_assoc, mul_comm ((r : ℝ) ^ 2)] at hdiv
  rw [SimpleGraph.card_edgeFinset_turanGraph]
  change _ ≤ ((A / B + r.choose 2 : ℕ) : ℝ); push_cast
  linarith [Nat.cast_nonneg (α := ℝ) (r.choose 2)]

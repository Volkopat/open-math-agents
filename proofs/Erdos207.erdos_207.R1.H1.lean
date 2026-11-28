import OMAReductions.R_Erdos207_erdos_207_R1
import Mathlib

/-!
Proof of `Erdos207.erdos_207.R1.H1`: existence of a Steiner triple system `STS(n)`
(`IsBlockDesign 2 3`) for every sufficiently large `n` with `n % 6 = 1` or `n % 6 = 3`.

We prove a general double-counting criterion (`isBlockDesign_of_exists_of_card_le`): a 3-uniform
hypergraph `H` on a finite type `V` in which every pair of distinct vertices is covered by at least
one triple and `3 * H.card ≤ (Fintype.card V).choose 2` automatically covers every pair uniquely.
We then instantiate it via:
* Bose's construction (1939) on `ZMod (2k + 1) × Fin 3` for `n = 6k + 3`, and
* Skolem's construction (1958) on `Option (Fin (2k) × Fin 3)` for `n = 6k + 1` (`k ≥ 1`).
-/

namespace OMA207H1

open Finset

/- ### General double-counting criterion and transport -/

private lemma isBlockDesign_of_exists_of_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V))
    (hunif : H.IsUniform 3)
    (hcard : 3 * H.card ≤ (Fintype.card V).choose 2)
    (hcov : ∀ u v : V, u ≠ v → ∃ e ∈ H, u ∈ e ∧ v ∈ e) :
    H.IsBlockDesign 2 3 := by
  refine ⟨hunif, ?_⟩
  let P : Finset (Finset V) := (Finset.univ : Finset V).powersetCard 2
  have hPcard : P.card = (Fintype.card V).choose 2 := by
    simp [P, Finset.card_powersetCard]
  have hge1 : ∀ S ∈ P, 1 ≤ (H.filter (fun e => S ⊆ e)).card := by
    intro S hS
    have hS2 : S.card = 2 := (Finset.mem_powersetCard.mp hS).2
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hS2
    obtain ⟨e, heH, hu, hv⟩ := hcov u v huv
    refine Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heH, ?_⟩⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  have hsum_eq : ∑ S ∈ P, (H.filter (fun e => S ⊆ e)).card = 3 * H.card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    have heach : ∀ e ∈ H, (∑ S ∈ P, if S ⊆ e then 1 else 0) = 3 := by
      intro e heH
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      have hfilt : P.filter (fun S => S ⊆ e) = e.powersetCard 2 := by
        ext S
        simp only [P, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
        exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
      rw [hfilt, Finset.card_powersetCard, hunif e heH]
      decide
    rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    simp
  have hsum_le : ∑ S ∈ P, (H.filter (fun e => S ⊆ e)).card ≤ ∑ _S ∈ P, 1 := by
    rw [hsum_eq, Finset.sum_const, smul_eq_mul, mul_one, hPcard]
    exact hcard
  have heq1 : ∀ S ∈ P, (H.filter (fun e => S ⊆ e)).card = 1 := by
    intro S hS
    have hle : (H.filter (fun e => S ⊆ e)).card ≤ 1 := by
      by_contra hgt
      have h2 : 2 ≤ (H.filter (fun e => S ⊆ e)).card := by omega
      have hrest : (P.erase S).card ≤ ∑ T ∈ P.erase S, (H.filter (fun e => T ⊆ e)).card := by
        calc (P.erase S).card = ∑ _T ∈ P.erase S, 1 := by simp
          _ ≤ ∑ T ∈ P.erase S, (H.filter (fun e => T ⊆ e)).card :=
              Finset.sum_le_sum fun T hT => hge1 T (Finset.mem_of_mem_erase hT)
      have htot := Finset.add_sum_erase P (fun T => (H.filter (fun e => T ⊆ e)).card) hS
      have hP1 : (P.erase S).card + 1 = P.card := by
        rw [Finset.card_erase_of_mem hS]
        have := Finset.card_pos.mpr ⟨S, hS⟩
        omega
      have hsum1 : ∑ _T ∈ P, 1 = P.card := by simp
      rw [hsum1] at hsum_le
      omega
    have := hge1 S hS
    omega
  intro S hS
  have hSP : S ∈ P := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hS⟩
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp (heq1 S hSP)
  refine ⟨e, ?_, ?_⟩
  · have hmem : e ∈ H.filter (fun x => S ⊆ x) := by rw [he]; exact Finset.mem_singleton_self e
    exact Finset.mem_filter.mp hmem
  · intro y hy
    have hmem : y ∈ H.filter (fun x => S ⊆ x) := Finset.mem_filter.mpr hy
    rw [he] at hmem
    exact Finset.mem_singleton.mp hmem

private lemma isBlockDesign_transport {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (e : V ≃ W)
    {H : Finset (Finset V)} (hH : H.IsBlockDesign 2 3) :
    (H.image (Finset.map e.toEmbedding)).IsBlockDesign 2 3 := by
  refine ⟨?_, ?_⟩
  · intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
    rw [Finset.card_map]
    exact hH.1 A hA
  · intro S hS
    let S' : Finset V := S.map e.symm.toEmbedding
    have hS'card : S'.card = 2 := by rw [Finset.card_map]; exact hS
    obtain ⟨A, ⟨hAH, hS'A⟩, huniq⟩ := hH.2 S' hS'card
    refine ⟨A.map e.toEmbedding, ⟨Finset.mem_image.mpr ⟨A, hAH, rfl⟩, ?_⟩, ?_⟩
    · intro w hw
      have hw' : e.symm w ∈ S' := Finset.mem_map.mpr ⟨w, hw, rfl⟩
      exact Finset.mem_map.mpr ⟨e.symm w, hS'A hw', e.apply_symm_apply w⟩
    · rintro B ⟨hBH, hSB⟩
      obtain ⟨A', hA'H, rfl⟩ := Finset.mem_image.mp hBH
      have hS'A' : S' ⊆ A' := by
        intro v hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
        obtain ⟨u, hu, huw⟩ := Finset.mem_map.mp (hSB hw)
        have : e.symm w = u := by
          apply e.injective
          rw [e.apply_symm_apply]
          exact huw.symm
        change e.symm w ∈ A'
        rwa [this]
      rw [huniq A' ⟨hA'H, hS'A'⟩]

private lemma card_triple_of_ne {V : Type*} [DecidableEq V] {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset V).card = 3 := by
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp [hbc]
  · simp [hab, hac]

/- ### Case 1: Bose construction for `n = 6 * k + 3` -/

private def boseOp (k : ℕ) (x y : ZMod (2 * k + 1)) : ZMod (2 * k + 1) :=
  ((k + 1 : ℕ) : ZMod (2 * k + 1)) * (x + y)

private lemma boseOp_comm (k : ℕ) (x y : ZMod (2 * k + 1)) :
    boseOp k x y = boseOp k y x := by
  unfold boseOp
  rw [add_comm x y]

private lemma two_mul_k_add_one (k : ℕ) :
    (2 : ZMod (2 * k + 1)) * ((k + 1 : ℕ) : ZMod (2 * k + 1)) = 1 := by
  have h1 : (2 * (k + 1) : ℕ) = (2 * k + 1) + 1 := by omega
  calc (2 : ZMod (2 * k + 1)) * ((k + 1 : ℕ) : ZMod (2 * k + 1))
      = ((2 * (k + 1) : ℕ) : ZMod (2 * k + 1)) := by push_cast; rfl
    _ = (((2 * k + 1) + 1 : ℕ) : ZMod (2 * k + 1)) := by rw [h1]
    _ = 1 := by rw [Nat.cast_add, ZMod.natCast_self, Nat.cast_one, zero_add]

private lemma boseOp_solve (k : ℕ) (a b : ZMod (2 * k + 1)) :
    boseOp k a (2 * b - a) = b := by
  unfold boseOp
  have hsum : a + (2 * b - a) = 2 * b := by ring
  rw [hsum, ← mul_assoc, mul_comm ((k + 1 : ℕ) : ZMod (2 * k + 1)) 2, two_mul_k_add_one, one_mul]

private lemma boseOp_solve_ne (k : ℕ) {a b : ZMod (2 * k + 1)} (hab : a ≠ b) :
    a ≠ 2 * b - a := by
  intro heq
  apply hab
  have h2 : (2 : ZMod (2 * k + 1)) * a = 2 * b := by linear_combination heq
  have h3 := congrArg (fun z => ((k + 1 : ℕ) : ZMod (2 * k + 1)) * z) h2
  rw [← mul_assoc, ← mul_assoc, mul_comm ((k + 1 : ℕ) : ZMod (2 * k + 1)) 2,
    two_mul_k_add_one, one_mul, one_mul] at h3
  exact h3

private lemma bose_sts (k : ℕ) :
    ∃ H : Finset (Finset (ZMod (2 * k + 1) × Fin 3)), H.IsBlockDesign 2 3 := by
  classical
  let m := 2 * k + 1
  have : NeZero m := ⟨by omega⟩
  let Q := ZMod m
  let H1 : Finset (Finset (Q × Fin 3)) :=
    Finset.univ.image fun x : Q => ({(x, 0), (x, 1), (x, 2)} : Finset (Q × Fin 3))
  let pairs : Finset (Finset Q) := (Finset.univ : Finset Q).powersetCard 2
  let mkH2 (p : Finset Q × Fin 3) : Finset (Q × Fin 3) :=
    if h : p.1.card = 2 then
      let x := (Finset.card_eq_two.mp h).choose
      let y := (Finset.card_eq_two.mp h).choose_spec.choose
      {(x, p.2), (y, p.2), (boseOp k x y, p.2 + 1)}
    else ∅
  let H2 : Finset (Finset (Q × Fin 3)) := (pairs ×ˢ (Finset.univ : Finset (Fin 3))).image mkH2
  let H := H1 ∪ H2
  have hmkH2_eq : ∀ (x y : Q) (j : Fin 3), x ≠ y →
      mkH2 ({x, y}, j) = {(x, j), (y, j), (boseOp k x y, j + 1)} := by
    intro x y j hxy
    have hcard2 : ({x, y} : Finset Q).card = 2 := Finset.card_pair hxy
    dsimp only [mkH2]
    rw [dif_pos hcard2]
    let x' := (Finset.card_eq_two.mp hcard2).choose
    let y' := (Finset.card_eq_two.mp hcard2).choose_spec.choose
    change {(x', j), (y', j), (boseOp k x' y', j + 1)} = {(x, j), (y, j), (boseOp k x y, j + 1)}
    have hspec := (Finset.card_eq_two.mp hcard2).choose_spec.choose_spec
    have hset : ({x, y} : Finset Q) = {x', y'} := hspec.2
    have hx' : x' = x ∨ x' = y := by
      have : x' ∈ ({x, y} : Finset Q) := by rw [hset]; simp
      simpa using this
    have hy' : y' = x ∨ y' = y := by
      have : y' ∈ ({x, y} : Finset Q) := by rw [hset]; simp
      simpa using this
    have hne' : x' ≠ y' := hspec.1
    rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
    · exact absurd (hx'.trans hy'.symm) hne'
    · rw [hx', hy']
    · rw [hx', hy', boseOp_comm]
      ext z; simp [or_left_comm]
    · exact absurd (hx'.trans hy'.symm) hne'
  refine ⟨H, isBlockDesign_of_exists_of_card_le H ?_ ?_ ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with he1 | he2
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he1
      exact card_triple_of_ne
        (fun h => (by decide : (0 : Fin 3) ≠ 1) (congrArg Prod.snd h))
        (fun h => (by decide : (0 : Fin 3) ≠ 2) (congrArg Prod.snd h))
        (fun h => (by decide : (1 : Fin 3) ≠ 2) (congrArg Prod.snd h))
    · obtain ⟨⟨S, j⟩, hSj, rfl⟩ := Finset.mem_image.mp he2
      have hS2 : S.card = 2 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hSj).1).2
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hS2
      rw [hmkH2_eq x y j hxy]
      have hjne : j ≠ j + 1 := by fin_cases j <;> decide
      exact card_triple_of_ne
        (fun h => hxy (congrArg Prod.fst h))
        (fun h => hjne (congrArg Prod.snd h))
        (fun h => hjne (congrArg Prod.snd h))
  · have hH1 : H1.card ≤ m := by
      calc H1.card ≤ (Finset.univ : Finset Q).card := Finset.card_image_le
        _ = m := by rw [Finset.card_univ, ZMod.card]
    have hH2 : H2.card ≤ 3 * m.choose 2 := by
      calc H2.card ≤ (pairs ×ˢ (Finset.univ : Finset (Fin 3))).card := Finset.card_image_le
        _ = pairs.card * 3 := by rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        _ = 3 * m.choose 2 := by
            rw [Nat.mul_comm, Finset.card_powersetCard, Finset.card_univ, ZMod.card]
    have hH : H.card ≤ m + 3 * m.choose 2 := (Finset.card_union_le H1 H2).trans (Nat.add_le_add hH1 hH2)
    have hV : Fintype.card (Q × Fin 3) = 3 * m := by
      rw [Fintype.card_prod, ZMod.card, Fintype.card_fin, Nat.mul_comm]
    rw [hV]
    rw [Nat.choose_two_right] at hH ⊢
    have h1 : m = 2 * k + 1 := rfl
    have hm1 : m - 1 = 2 * k := by omega
    rw [hm1] at hH
    rw [h1] at hH ⊢
    have h2 : (2 * k + 1) * (2 * k) / 2 = (2 * k + 1) * k := by
      have : (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) := by ring
      rw [this, Nat.mul_div_cancel_left _ (by decide)]
    have h3 : 3 * (2 * k + 1) * (3 * (2 * k + 1) - 1) / 2 = 3 * (2 * k + 1) * (3 * k + 1) := by
      have : 3 * (2 * k + 1) * (3 * (2 * k + 1) - 1) = 2 * (3 * (2 * k + 1) * (3 * k + 1)) := by
        have : 3 * (2 * k + 1) - 1 = 6 * k + 2 := by omega
        rw [this]; ring
      rw [this, Nat.mul_div_cancel_left _ (by decide)]
    rw [h2] at hH
    rw [h3]
    nlinarith
  · intro u v huv
    rcases u with ⟨a, i⟩
    rcases v with ⟨b, j⟩
    by_cases hij : i = j
    · subst hij
      have hab : a ≠ b := fun h => huv (by rw [h])
      refine ⟨mkH2 ({a, b}, i), Finset.mem_union_right _ ?_, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨({a, b}, i),
          Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair hab⟩,
            Finset.mem_univ _⟩, rfl⟩
      · rw [hmkH2_eq a b i hab]; simp
      · rw [hmkH2_eq a b i hab]; simp
    · by_cases hab : a = b
      · subst hab
        refine ⟨{(a, 0), (a, 1), (a, 2)}, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩), ?_, ?_⟩
        · fin_cases i <;> simp
        · fin_cases j <;> simp
      · have hstep : j = i + 1 ∨ i = j + 1 := by
          fin_cases i <;> fin_cases j <;> simp_all
        rcases hstep with rfl | rfl
        · let y := 2 * b - a
          have hay : a ≠ y := boseOp_solve_ne k hab
          refine ⟨mkH2 ({a, y}, i), Finset.mem_union_right _ ?_, ?_, ?_⟩
          · exact Finset.mem_image.mpr ⟨({a, y}, i),
              Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair hay⟩,
                Finset.mem_univ _⟩, rfl⟩
          · rw [hmkH2_eq a y i hay]; simp
          · rw [hmkH2_eq a y i hay, boseOp_solve k a b]; simp
        · let y := 2 * a - b
          have hby : b ≠ y := boseOp_solve_ne k (Ne.symm hab)
          refine ⟨mkH2 ({b, y}, j), Finset.mem_union_right _ ?_, ?_, ?_⟩
          · exact Finset.mem_image.mpr ⟨({b, y}, j),
              Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair hby⟩,
                Finset.mem_univ _⟩, rfl⟩
          · rw [hmkH2_eq b y j hby, boseOp_solve k b a]; simp
          · rw [hmkH2_eq b y j hby]; simp

/- ### Case 2: Skolem construction for `n = 6 * k + 1` (`k ≥ 1`) -/

private def skolemOp (k : ℕ) (hk : 0 < k) (a b : Fin (2 * k)) : Fin (2 * k) :=
  if (a.val + b.val) % 2 = 0 then
    ⟨((a.val + b.val) / 2) % k, Nat.lt_trans (Nat.mod_lt _ hk) (by omega)⟩
  else
    ⟨k + ((a.val + b.val) / 2) % k, by have := Nat.mod_lt ((a.val + b.val) / 2) hk; omega⟩

private lemma skolemOp_comm (k : ℕ) (hk : 0 < k) (a b : Fin (2 * k)) :
    skolemOp k hk a b = skolemOp k hk b a := by
  unfold skolemOp
  simp only [Nat.add_comm a.val b.val]

private lemma skolem_solve (k : ℕ) (hk : 0 < k) (a b : Fin (2 * k))
    (h1 : ¬ (a.val = b.val ∧ b.val < k))
    (h2 : ¬ (a.val = b.val + k ∧ b.val < k)) :
    ∃ y : Fin (2 * k), a ≠ y ∧ skolemOp k hk a y = b := by
  by_cases hbk : b.val < k
  · let s := 2 * b.val + 2 * k - a.val
    let y : Fin (2 * k) := ⟨s % (2 * k), Nat.mod_lt _ (by omega)⟩
    have hay : a ≠ y := by
      intro heq
      have hval : a.val = s % (2 * k) := congrArg Fin.val heq
      by_cases hs : s < 2 * k
      · rw [Nat.mod_eq_of_lt hs] at hval
        have : a.val = b.val + k := by omega
        exact h2 ⟨this, hbk⟩
      · have hs' : s - 2 * k < 2 * k := by omega
        have hmod : s % (2 * k) = s - 2 * k := by
          have : s = (s - 2 * k) + 2 * k := by omega
          conv_lhs => rw [this]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hs']
        rw [hmod] at hval
        have : a.val = b.val := by omega
        exact h1 ⟨this, hbk⟩
    refine ⟨y, hay, ?_⟩
    apply Fin.ext
    dsimp only [skolemOp]
    by_cases hs : s < 2 * k
    · have hy : y.val = s := Nat.mod_eq_of_lt hs
      have hsum : a.val + y.val = 2 * b.val + 2 * k := by omega
      have heven : (a.val + y.val) % 2 = 0 := by omega
      rw [if_pos heven]
      dsimp only
      have hdiv : (a.val + y.val) / 2 = b.val + k := by omega
      rw [hdiv, Nat.add_mod_right, Nat.mod_eq_of_lt hbk]
    · have hs' : s - 2 * k < 2 * k := by omega
      have hy : y.val = s - 2 * k := by
        dsimp only [y]
        have : s = (s - 2 * k) + 2 * k := by omega
        conv_lhs => rw [this]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hs']
      have hsum : a.val + y.val = 2 * b.val := by omega
      have heven : (a.val + y.val) % 2 = 0 := by omega
      rw [if_pos heven]
      dsimp only
      have hdiv : (a.val + y.val) / 2 = b.val := by omega
      rw [hdiv, Nat.mod_eq_of_lt hbk]
  · let r := b.val - k
    have hrk : r < k := by omega
    let s := 2 * r + 1 + 2 * k - a.val
    let y : Fin (2 * k) := ⟨s % (2 * k), Nat.mod_lt _ (by omega)⟩
    have hsum_odd : (a.val + y.val) % 2 = 1 ∧ (a.val + y.val) / 2 % k = r := by
      by_cases hs : s < 2 * k
      · have hy : y.val = s := Nat.mod_eq_of_lt hs
        have hsum : a.val + y.val = 2 * r + 1 + 2 * k := by omega
        have hdiv : (a.val + y.val) / 2 = r + k := by omega
        refine ⟨by omega, ?_⟩
        rw [hdiv, Nat.add_mod_right, Nat.mod_eq_of_lt hrk]
      · have hs' : s - 2 * k < 2 * k := by omega
        have hy : y.val = s - 2 * k := by
          dsimp only [y]
          have : s = (s - 2 * k) + 2 * k := by omega
          conv_lhs => rw [this]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hs']
        have hsum : a.val + y.val = 2 * r + 1 := by omega
        have hdiv : (a.val + y.val) / 2 = r := by omega
        refine ⟨by omega, ?_⟩
        rw [hdiv, Nat.mod_eq_of_lt hrk]
    have hay : a ≠ y := by
      intro heq
      have hval : a.val = y.val := congrArg Fin.val heq
      omega
    refine ⟨y, hay, ?_⟩
    apply Fin.ext
    dsimp only [skolemOp]
    rw [if_neg (by omega)]
    dsimp only
    rw [hsum_odd.2]
    omega

private lemma skolem_sts (k : ℕ) (hk : 0 < k) :
    ∃ H : Finset (Finset (Option (Fin (2 * k) × Fin 3))), H.IsBlockDesign 2 3 := by
  classical
  let Q := Fin (2 * k)
  let V := Option (Q × Fin 3)
  let emb (x : Fin k) : Q := ⟨x.val, by omega⟩
  let embHi (x : Fin k) : Q := ⟨x.val + k, by omega⟩
  let H1 : Finset (Finset V) :=
    (Finset.univ : Finset (Fin k)).image fun x =>
      ({some (emb x, 0), some (emb x, 1), some (emb x, 2)} : Finset V)
  let H2 : Finset (Finset V) :=
    ((Finset.univ : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin 3))).image fun p =>
      ({none, some (embHi p.1, p.2), some (emb p.1, p.2 + 1)} : Finset V)
  let pairs : Finset (Finset Q) := (Finset.univ : Finset Q).powersetCard 2
  let mkH3 (p : Finset Q × Fin 3) : Finset V :=
    if h : p.1.card = 2 then
      let x := (Finset.card_eq_two.mp h).choose
      let y := (Finset.card_eq_two.mp h).choose_spec.choose
      {some (x, p.2), some (y, p.2), some (skolemOp k hk x y, p.2 + 1)}
    else ∅
  let H3 : Finset (Finset V) := (pairs ×ˢ (Finset.univ : Finset (Fin 3))).image mkH3
  let H := (H1 ∪ H2) ∪ H3
  have hmkH3_eq : ∀ (x y : Q) (j : Fin 3), x ≠ y →
      mkH3 ({x, y}, j) = {some (x, j), some (y, j), some (skolemOp k hk x y, j + 1)} := by
    intro x y j hxy
    have hcard2 : ({x, y} : Finset Q).card = 2 := Finset.card_pair hxy
    dsimp only [mkH3]
    rw [dif_pos hcard2]
    let x' := (Finset.card_eq_two.mp hcard2).choose
    let y' := (Finset.card_eq_two.mp hcard2).choose_spec.choose
    change {some (x', j), some (y', j), some (skolemOp k hk x' y', j + 1)} =
      {some (x, j), some (y, j), some (skolemOp k hk x y, j + 1)}
    have hspec := (Finset.card_eq_two.mp hcard2).choose_spec.choose_spec
    have hset : ({x, y} : Finset Q) = {x', y'} := hspec.2
    have hx' : x' = x ∨ x' = y := by
      have : x' ∈ ({x, y} : Finset Q) := by rw [hset]; simp
      simpa using this
    have hy' : y' = x ∨ y' = y := by
      have : y' ∈ ({x, y} : Finset Q) := by rw [hset]; simp
      simpa using this
    have hne' : x' ≠ y' := hspec.1
    rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
    · exact absurd (hx'.trans hy'.symm) hne'
    · rw [hx', hy']
    · rw [hx', hy', skolemOp_comm]
      ext z; simp [or_left_comm]
    · exact absurd (hx'.trans hy'.symm) hne'
  refine ⟨H, isBlockDesign_of_exists_of_card_le H ?_ ?_ ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with he12 | he3
    · rcases Finset.mem_union.mp he12 with he1 | he2
      · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he1
        exact card_triple_of_ne
          (fun h => (by decide : (0 : Fin 3) ≠ 1) (congrArg Prod.snd (Option.some.inj h)))
          (fun h => (by decide : (0 : Fin 3) ≠ 2) (congrArg Prod.snd (Option.some.inj h)))
          (fun h => (by decide : (1 : Fin 3) ≠ 2) (congrArg Prod.snd (Option.some.inj h)))
      · obtain ⟨⟨x, j⟩, _, rfl⟩ := Finset.mem_image.mp he2
        have hjne : j ≠ j + 1 := by fin_cases j <;> decide
        exact card_triple_of_ne
          (by simp)
          (by simp)
          (fun h => hjne (congrArg Prod.snd (Option.some.inj h)))
    · obtain ⟨⟨S, j⟩, hSj, rfl⟩ := Finset.mem_image.mp he3
      have hS2 : S.card = 2 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hSj).1).2
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hS2
      rw [hmkH3_eq x y j hxy]
      have hjne : j ≠ j + 1 := by fin_cases j <;> decide
      exact card_triple_of_ne
        (fun h => hxy (congrArg Prod.fst (Option.some.inj h)))
        (fun h => hjne (congrArg Prod.snd (Option.some.inj h)))
        (fun h => hjne (congrArg Prod.snd (Option.some.inj h)))
  · have hH1 : H1.card ≤ k := by
      calc H1.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
        _ = k := by simp
    have hH2 : H2.card ≤ 3 * k := by
      calc H2.card ≤ ((Finset.univ : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin 3))).card :=
            Finset.card_image_le
        _ = 3 * k := by simp [Nat.mul_comm]
    have hH3 : H3.card ≤ 3 * (2 * k).choose 2 := by
      calc H3.card ≤ (pairs ×ˢ (Finset.univ : Finset (Fin 3))).card := Finset.card_image_le
        _ = pairs.card * 3 := by rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        _ = 3 * (2 * k).choose 2 := by
            rw [Nat.mul_comm, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    have hH : H.card ≤ k + 3 * k + 3 * (2 * k).choose 2 :=
      (Finset.card_union_le (H1 ∪ H2) H3).trans
        (Nat.add_le_add ((Finset.card_union_le H1 H2).trans (Nat.add_le_add hH1 hH2)) hH3)
    have hV : Fintype.card V = 6 * k + 1 := by
      simp [V, Q]; omega
    rw [hV]
    have hc1 : (2 * k).choose 2 = k * (2 * k - 1) := by
      rw [Nat.choose_two_right]
      have : 2 * k * (2 * k - 1) = 2 * (k * (2 * k - 1)) := by ring
      rw [this, Nat.mul_div_cancel_left _ (by decide)]
    have hc2 : (6 * k + 1).choose 2 = (6 * k + 1) * (3 * k) := by
      rw [Nat.choose_two_right]
      have : (6 * k + 1) * (6 * k + 1 - 1) = 2 * ((6 * k + 1) * (3 * k)) := by
        have : 6 * k + 1 - 1 = 6 * k := by omega
        rw [this]; ring
      rw [this, Nat.mul_div_cancel_left _ (by decide)]
    rw [hc1] at hH
    rw [hc2]
    have hk1 : 2 * k - 1 + 1 = 2 * k := by omega
    nlinarith
  · intro u v huv
    have hcov_none : ∀ (a : Q) (j : Fin 3), ∃ e ∈ H, (none : V) ∈ e ∧ some (a, j) ∈ e := by
      intro a j
      by_cases hak : a.val < k
      · let x : Fin k := ⟨a.val, hak⟩
        have hax : emb x = a := Fin.ext rfl
        refine ⟨{none, some (embHi x, j - 1), some (emb x, (j - 1) + 1)},
          Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨(x, j - 1), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩)),
          by simp, ?_⟩
        rw [hax, sub_add_cancel]; simp
      · let x : Fin k := ⟨a.val - k, by omega⟩
        have hax : embHi x = a := Fin.ext (by dsimp [embHi, x]; omega)
        refine ⟨{none, some (embHi x, j), some (emb x, j + 1)},
          Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨(x, j), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩)),
          by simp, ?_⟩
        rw [hax]; simp
    have hcov_step : ∀ (a b : Q) (i : Fin 3),
        ∃ e ∈ H, (some (a, i) : V) ∈ e ∧ (some (b, i + 1) : V) ∈ e := by
      intro a b i
      by_cases h1 : a.val = b.val ∧ b.val < k
      · let x : Fin k := ⟨b.val, h1.2⟩
        have hax : emb x = a := Fin.ext h1.1.symm
        have hbx : emb x = b := Fin.ext rfl
        refine ⟨{some (emb x, 0), some (emb x, 1), some (emb x, 2)},
          Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)),
          ?_, ?_⟩
        · rw [hax]; fin_cases i <;> simp
        · rw [hbx]; fin_cases i <;> simp
      · by_cases h2 : a.val = b.val + k ∧ b.val < k
        · let x : Fin k := ⟨b.val, h2.2⟩
          have hax : embHi x = a := Fin.ext h2.1.symm
          have hbx : emb x = b := Fin.ext rfl
          refine ⟨{none, some (embHi x, i), some (emb x, i + 1)},
            Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
              ⟨(x, i), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩)),
            ?_, ?_⟩
          · rw [hax]; simp
          · rw [hbx]; simp
        · obtain ⟨y, hay, hop⟩ := skolem_solve k hk a b h1 h2
          refine ⟨mkH3 ({a, y}, i), Finset.mem_union_right _ ?_, ?_, ?_⟩
          · exact Finset.mem_image.mpr ⟨({a, y}, i),
              Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair hay⟩,
                Finset.mem_univ _⟩, rfl⟩
          · rw [hmkH3_eq a y i hay]; simp
          · rw [hmkH3_eq a y i hay, hop]; simp
    cases u with
    | none =>
      cases v with
      | none => exact absurd rfl huv
      | some p => exact hcov_none p.1 p.2
    | some p =>
      cases v with
      | none =>
        obtain ⟨e, he, h1, h2⟩ := hcov_none p.1 p.2
        exact ⟨e, he, h2, h1⟩
      | some q =>
        rcases p with ⟨a, i⟩
        rcases q with ⟨b, j⟩
        by_cases hij : i = j
        · subst hij
          have hab : a ≠ b := fun h => huv (by rw [h])
          refine ⟨mkH3 ({a, b}, i), Finset.mem_union_right _ ?_, ?_, ?_⟩
          · exact Finset.mem_image.mpr ⟨({a, b}, i),
              Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_pair hab⟩,
                Finset.mem_univ _⟩, rfl⟩
          · rw [hmkH3_eq a b i hab]; simp
          · rw [hmkH3_eq a b i hab]; simp
        · have hstep : j = i + 1 ∨ i = j + 1 := by
            fin_cases i <;> fin_cases j <;> simp_all
          rcases hstep with rfl | rfl
          · exact hcov_step a b i
          · obtain ⟨e, he, h1, h2⟩ := hcov_step b a j
            exact ⟨e, he, h2, h1⟩

end OMA207H1

theorem OMA.solution : OMA.R_Erdos207_erdos_207_R1.H1 := by
  intro _g _hg
  filter_upwards [Filter.eventually_ge_atTop 7] with n hn hmod
  rcases hmod with h1 | h3
  · let k := n / 6
    have hk : 0 < k := by omega
    have hcard : Fintype.card (Option (Fin (2 * k) × Fin 3)) = n := by
      simp [k]; omega
    obtain ⟨H, hH⟩ := OMA207H1.skolem_sts k hk
    exact ⟨_, OMA207H1.isBlockDesign_transport (Fintype.equivFinOfCardEq hcard) hH⟩
  · let k := n / 6
    have hcard : Fintype.card (ZMod (2 * k + 1) × Fin 3) = n := by
      rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]
      omega
    obtain ⟨H, hH⟩ := OMA207H1.bose_sts k
    exact ⟨_, OMA207H1.isBlockDesign_transport (Fintype.equivFinOfCardEq hcard) hH⟩

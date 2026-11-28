import OMAStatements.S_oeis_a250896
import Mathlib

namespace OMA.S_oeis_a250896

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def BB : ℕ := 243

section fastvec
/-! Fast transfer-vector kit.  States are `Fin N`; the (sparse) transition relation is given by an explicit
adjacency list `adj : List (List ℕ)`; vectors are `List ℕ`; one step is a fold over the lists.  Only Nat.add
on literals is evaluated by the kernel. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def Chain {S : Type} (R : S → S → Prop) (n : ℕ) :=
  {y : Fin (n + 1) → S // ∀ i : Fin n, R (y i.castSucc) (y i.succ)}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def chainEquiv {S S' : Type} {R : S → S → Prop} {R' : S' → S' → Prop} (e : S ≃ S')
    (h : ∀ a b, R a b ↔ R' (e a) (e b)) (n : ℕ) : Chain R n ≃ Chain R' n where
  toFun y := ⟨fun i => e (y.1 i), fun i => (h _ _).1 (y.2 i)⟩
  invFun y := ⟨fun i => e.symm (y.1 i), fun i => (h _ _).2 (by simpa using y.2 i)⟩
  left_inv y := by apply Subtype.ext; funext i; simp
  right_inv y := by apply Subtype.ext; funext i; simp

section generic
variable {S : Type} [Fintype S] [DecidableEq S] (R : S → S → Prop) [DecidableRel R]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
instance (n : ℕ) : Fintype (Chain R n) := by unfold Chain; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def V : ℕ → S → ℕ
  | 0, _ => 1
  | n + 1, s => ∑ t, if R s t then V n t else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem cardStart (n : ℕ) (s : S) :
    Fintype.card {y : Chain R n // y.1 0 = s} = V R n s := by
  induction n generalizing s with
  | zero =>
    simp only [V]
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨fun _ => s, fun i => i.elim0⟩, rfl⟩, ?_⟩
    rintro ⟨⟨y, hy⟩, h0⟩
    apply Subtype.ext; apply Subtype.ext
    funext j
    have : j = 0 := Fin.ext (by have := j.2; omega)
    subst this; exact h0
  | succ n ih =>
    have e : {y : Chain R (n + 1) // y.1 0 = s} ≃
        Σ t : S, {z : Chain R n // z.1 0 = t ∧ R s t} :=
      { toFun := fun y => ⟨y.1.1 1, ⟨⟨fun j => y.1.1 j.succ, fun i => y.1.2 i.succ⟩, rfl, by
          have h := y.1.2 0
          have h0 : y.1.1 (Fin.castSucc 0) = s := y.2
          rw [h0] at h
          exact h⟩⟩
        invFun := fun p => ⟨⟨Fin.cons s p.2.1.1, by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · have h2 := p.2.2.2
            rw [← p.2.2.1] at h2
            simpa using h2
          · simpa using p.2.1.2 j⟩, rfl⟩
        left_inv := by
          rintro ⟨⟨y, hy⟩, h0⟩
          apply Subtype.ext; apply Subtype.ext
          funext j
          refine Fin.cases ?_ (fun k => ?_) j
          · simpa using h0.symm
          · simp
        right_inv := by
          rintro ⟨t, ⟨⟨z, hz⟩, h1, h2⟩⟩
          simp only [Fin.cons_succ]
          have : (Fin.cons s z : Fin (n + 2) → S) 1 = t := by
            have : (1 : Fin (n + 2)) = Fin.succ 0 := rfl
            rw [this, Fin.cons_succ]; exact h1
          subst this
          rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [V]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : R s t
    · simp only [h, if_true, and_true]
      exact ih t
    · simp only [h, if_false, and_false]
      simp [Fintype.card_eq_zero_iff]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem cardChain (n : ℕ) : Fintype.card (Chain R n) = ∑ s, V R n s := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun y : Chain R n => y.1 0)), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  exact cardStart R n s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem rec_gen (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) :
    ∀ n s, ∑ j ∈ Finset.range (m + 1), c j * (V R (n + j) s : ℤ) = 0 := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    intro s
    have : ∀ j, (V R (n + 1 + j) s : ℤ) = ∑ t, if R s t then (V R (n + j) t : ℤ) else 0 := by
      intro j
      rw [show n + 1 + j = (n + j) + 1 by omega]
      simp [V]
    simp only [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t _
    by_cases h : R s t
    · have := ih t
      simp only [h, if_true]
      simpa [← Finset.mul_sum] using this
    · simp [h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem rec_total (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) (n : ℕ) :
    ∑ j ∈ Finset.range (m + 1), c j * (∑ s, (V R (n + j) s : ℤ)) = 0 := by
  have h := Finset.sum_eq_zero (s := (Finset.univ : Finset S)) (fun s _ => rec_gen R m c h0 n s)
  rw [Finset.sum_comm] at h
  simpa [Finset.mul_sum] using h
end generic

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- one transfer step: new[s] = sum of old[t] over the neighbours t of s -/
def stepL (adj : List (List ℕ)) (v : List ℕ) : List ℕ :=
  adj.map fun l => (l.map fun t => v.getD t 0).sum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def iterL (adj : List (List ℕ)) (N : ℕ) : ℕ → List ℕ
  | 0 => List.replicate N 1
  | n + 1 => stepL adj (iterL adj N n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem length_iterL (adj : List (List ℕ)) (N : ℕ) (hlen : adj.length = N) (n : ℕ) :
    (iterL adj N n).length = N := by
  cases n <;> simp [iterL, stepL, hlen]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem V_eq_iterL (N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (adj : List (List ℕ))
    (hlen : adj.length = N) (hnd : ∀ s : Fin N, (adj.getD s []).Nodup)
    (hmem : ∀ s t : Fin N, R s t ↔ t.val ∈ adj.getD s [])
    (hlt : ∀ s : Fin N, ∀ t ∈ adj.getD s [], t < N) :
    ∀ n (s : Fin N), V R n s = (iterL adj N n).getD s 0 := by
  intro n
  induction n with
  | zero => intro s; simp [V, iterL, List.getD_eq_getElem?_getD]
  | succ n ih =>
    intro s
    have hs : (s : ℕ) < adj.length := by rw [hlen]; exact s.2
    have e1 : (iterL adj N (n + 1)).getD s 0 =
        ((adj.getD s []).map fun t => (iterL adj N n).getD t 0).sum := by
      simp [iterL, stepL, List.getD_eq_getElem?_getD, List.getElem?_map, hs,
        List.getElem?_eq_getElem hs]
    rw [e1, ← List.sum_toFinset _ (hnd s)]
    simp only [V]
    have : ∀ t : Fin N, (if R s t then V R n t else 0) =
        if t.val ∈ (adj.getD s []).toFinset then (iterL adj N n).getD t 0 else 0 := by
      intro t
      by_cases h : R s t
      · have := (hmem s t).1 h
        rw [if_pos h, if_pos (List.mem_toFinset.2 this), ih t]
      · rw [if_neg h, if_neg (by rw [List.mem_toFinset]; exact mt (hmem s t).2 h)]
    simp only [this]
    set F := (adj.getD s []).toFinset with hF
    set g : ℕ → ℕ := fun x => (iterL adj N n).getD x 0 with hg
    rw [show (∑ t : Fin N, if t.val ∈ F then (iterL adj N n).getD t 0 else 0) =
        ∑ t : Fin N, (fun x : ℕ => if x ∈ F then g x else 0) t.val from rfl,
      Fin.sum_univ_eq_sum_range (fun x : ℕ => if x ∈ F then g x else 0) N,
      Finset.sum_ite_mem, Finset.inter_eq_right.2]
    intro t ht
    exact Finset.mem_range.2 (hlt s t (List.mem_toFinset.1 ht))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem sum_getD (l : List ℕ) (N : ℕ) (h : l.length = N) : ∑ s : Fin N, l.getD s 0 = l.sum := by
  subst h
  rw [← Fin.sum_univ_getElem l]
  apply Finset.sum_congr rfl
  intro i _
  simp [List.getD_eq_getElem?_getD]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem testBit_foldl_land (l : List ℕ) : ∀ (init t : ℕ),
    (l.foldl (· &&& ·) init).testBit t = true ↔ (init.testBit t = true ∧ ∀ x ∈ l, x.testBit t = true) := by
  induction l with
  | nil => intro init t; simp
  | cons x l ih =>
    intro init t
    simp only [List.foldl_cons, ih, Nat.testBit_and, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    tauto

/-- the adjacency lists `adj` describe the relation `R` on `Fin N` (sorted/duplicate-free not needed, only nodup) -/
structure AdjOK (N : ℕ) (R : Fin N → Fin N → Prop) (adj : List (List ℕ)) : Prop where
  len : adj.length = N
  nodup : ∀ s : Fin N, (adj.getD s []).Nodup
  mem : ∀ s t : Fin N, R s t ↔ t.val ∈ adj.getD s []
  lt : ∀ s : Fin N, ∀ t ∈ adj.getD s [], t < N

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem testBit_foldl_lor (l : List ℕ) : ∀ (init t : ℕ),
    (l.foldl (fun a x => a ||| 2 ^ x) init).testBit t = true ↔ (init.testBit t = true ∨ t ∈ l) := by
  induction l with
  | nil => intro init t; simp
  | cons x l ih =>
    intro init t
    simp only [List.foldl_cons, ih, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq,
      List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h.symm)
      · exact Or.inr h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- build `AdjOK` from a bitmask description of the relation and an explicit literal adjacency list -/
theorem adjOK_of_mask (N : ℕ) (R : Fin N → Fin N → Prop) (mask : ℕ → ℕ) (adj : List (List ℕ))
    (hR : ∀ s t : Fin N, R s t ↔ (mask s).testBit t = true)
    (hlen : adj.length = N)
    (hadj : ∀ s < N, (adj.getD s []).foldl (fun a x => a ||| 2 ^ x) 0 = mask s)
    (hnd : ∀ s < N, (adj.getD s []).Nodup)
    (hlt : ∀ s < N, ∀ t ∈ adj.getD s [], t < N) : AdjOK N R adj where
  len := hlen
  nodup := fun s => hnd s s.2
  mem := fun s t => by
    rw [hR, ← hadj s s.2, testBit_foldl_lor]
    simp
  lt := fun s => hlt s s.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem V_eq_iterL' (N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (adj : List (List ℕ))
    (H : AdjOK N R adj) (n : ℕ) (s : Fin N) :
    V R n s = (iterL adj N n).getD s 0 :=
  V_eq_iterL N R adj H.len H.nodup H.mem H.lt n s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem sum_V_eq (N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (adj : List (List ℕ))
    (H : AdjOK N R adj) (n : ℕ) :
    ∑ s, V R n s = (iterL adj N n).sum := by
  simp only [V_eq_iterL' N R adj H n]
  exact sum_getD _ N (length_iterL _ N H.len n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- linear combination of the vectors `f j` (j in L) with natural coefficients `c j`, as a list fold -/
def comb (N : ℕ) (c : ℕ → ℕ) (f : ℕ → List ℕ) (L : List ℕ) : List ℕ :=
  L.foldl (fun acc j => List.zipWith (· + ·) acc ((f j).map (c j * ·))) (List.replicate N 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem foldl_comb_getD (N : ℕ) (c : ℕ → ℕ) (f : ℕ → List ℕ) (hf : ∀ j, (f j).length = N) (L : List ℕ) :
    ∀ (acc : List ℕ), acc.length = N → ∀ s < N,
      (L.foldl (fun acc j => List.zipWith (· + ·) acc ((f j).map (c j * ·))) acc).getD s 0 =
        acc.getD s 0 + (L.map fun j => c j * (f j).getD s 0).sum := by
  induction L with
  | nil => intro acc _ s _; simp
  | cons j L ih =>
    intro acc hacc s hs
    have hl : (List.zipWith (· + ·) acc ((f j).map (c j * ·))).length = N := by simp [hacc, hf]
    rw [List.foldl_cons, ih _ hl s hs]
    have h1 : s < acc.length := by omega
    have h2 : s < (f j).length := by rw [hf]; exact hs
    simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_map, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2]
    ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem comb_getD (N : ℕ) (c : ℕ → ℕ) (f : ℕ → List ℕ) (hf : ∀ j, (f j).length = N) (L : List ℕ)
    (s : ℕ) (hs : s < N) :
    (comb N c f L).getD s 0 = (L.map fun j => c j * (f j).getD s 0).sum := by
  unfold comb
  rw [foldl_comb_getD N c f hf L _ (by simp) s hs]
  simp [List.getD_eq_getElem?_getD, hs]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem sum_range_eq_list (K : ℕ) (g : ℕ → ℕ) :
    ∑ j ∈ Finset.range K, g j = ((List.range K).map g).sum := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- componentwise recurrence from a kernel-checked equality of two Nat vectors (positive/negative parts) -/
theorem h0_of_chk (N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (adj : List (List ℕ))
    (H : AdjOK N R adj) (K : ℕ) (cp cn : ℕ → ℕ)
    (chk : comb N cp (iterL adj N) (List.range (K + 1)) = comb N cn (iterL adj N) (List.range (K + 1)))
    (s : Fin N) :
    ∑ j ∈ Finset.range (K + 1), ((cp j : ℤ) - cn j) * (V R j s : ℤ) = 0 := by
  have hf : ∀ j, (iterL adj N j).length = N := length_iterL adj N H.len
  have h := congrArg (fun l => l.getD s 0) chk
  simp only [comb_getD N _ _ hf _ s s.2] at h
  simp only [V_eq_iterL' N R adj H, sub_mul, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  have h' : ∑ j ∈ Finset.range (K + 1), cp j * (iterL adj N j).getD s 0 =
      ∑ j ∈ Finset.range (K + 1), cn j * (iterL adj N j).getD s 0 := by
    rw [sum_range_eq_list, sum_range_eq_list]; exact h
  exact_mod_cast h'
/-! Packed vectors: a vector of N naturals below 2^128 is one big Nat (digit t = bits 128t..128t+127), so a lookup is
two GMP operations instead of a linear list walk. -/
def dg (v t : ℕ) : ℕ := (v >>> (128 * t)) % 2 ^ 128

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def pack : List ℕ → ℕ
  | [] => 0
  | x :: l => x + 2 ^ 128 * pack l

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem dg_pack (l : List ℕ) (h : ∀ x ∈ l, x < 2 ^ 128) : ∀ t, dg (pack l) t = l.getD t 0 := by
  induction l with
  | nil => intro t; simp [dg, pack]
  | cons x l ih =>
    intro t
    have hx : x < 2 ^ 128 := h x (by simp)
    have hl : ∀ y ∈ l, y < 2 ^ 128 := fun y hy => h y (by simp [hy])
    have hd : (x + 2 ^ 128 * pack l) / 2 ^ 128 = pack l := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add]
    cases t with
    | zero =>
      simp only [dg, pack, Nat.mul_zero, Nat.shiftRight_zero, Nat.add_mul_mod_self_left]
      rw [Nat.mod_eq_of_lt hx]; simp
    | succ t =>
      have : dg (pack (x :: l)) (t + 1) = dg (pack l) t := by
        simp only [dg, pack, show 128 * (t + 1) = 128 + 128 * t by ring, Nat.shiftRight_add]
        rw [show (x + 2 ^ 128 * pack l) >>> 128 = pack l by rw [Nat.shiftRight_eq_div_pow]; exact hd]
      rw [this, ih hl t]; simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def stepP (adj : List (List ℕ)) (v : ℕ) : ℕ := pack (adj.map fun l => (l.map fun t => dg v t).sum)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def iterP (adj : List (List ℕ)) (N : ℕ) : ℕ → ℕ
  | 0 => pack (List.replicate N 1)
  | n + 1 => stepP adj (iterP adj N n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def unpackN (N v : ℕ) : List ℕ := (List.range N).map (dg v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem iterL_bound (adj : List (List ℕ)) (N Δ : ℕ) (hΔ : ∀ l ∈ adj, l.length ≤ Δ) (h1 : 1 ≤ Δ) :
    ∀ n, ∀ x ∈ iterL adj N n, x ≤ Δ ^ n := by
  intro n
  induction n with
  | zero =>
    intro x hx
    have := List.eq_of_mem_replicate (show x ∈ List.replicate N 1 from hx)
    rw [this]; simp
  | succ n ih =>
    intro x hx
    simp only [iterL, stepL, List.mem_map] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    have hv : ∀ t, (iterL adj N n).getD t 0 ≤ Δ ^ n := by
      intro t
      by_cases ht : t < (iterL adj N n).length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
        exact ih _ (List.getElem_mem ht)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp
    calc (l.map fun t => (iterL adj N n).getD t 0).sum
        ≤ (l.map fun t => (iterL adj N n).getD t 0).length • Δ ^ n :=
          List.sum_le_card_nsmul _ _ (by intro y hy; obtain ⟨t, _, rfl⟩ := List.mem_map.1 hy; exact hv t)
      _ ≤ Δ * Δ ^ n := by
          simp only [List.length_map, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (hΔ l hl)
      _ = Δ ^ (n + 1) := by ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem iterP_eq (adj : List (List ℕ)) (N Δ : ℕ) (hΔ : ∀ l ∈ adj, l.length ≤ Δ) (h1 : 1 ≤ Δ) (K : ℕ)
    (hK : Δ ^ K < 2 ^ 128) : ∀ n ≤ K, iterP adj N n = pack (iterL adj N n) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hb : ∀ x ∈ iterL adj N n, x < 2 ^ 128 := fun x hx =>
      lt_of_le_of_lt ((iterL_bound adj N Δ hΔ h1 n x hx).trans (Nat.pow_le_pow_right h1 (by omega))) hK
    simp only [iterP, stepP, iterL, stepL, ih (by omega)]
    congr 1
    apply List.map_congr_left
    intro l _
    congr 1
    apply List.map_congr_left
    intro t _
    exact dg_pack _ hb t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem unpack_iterP (adj : List (List ℕ)) (N Δ : ℕ) (hlen : adj.length = N) (hΔ : ∀ l ∈ adj, l.length ≤ Δ)
    (h1 : 1 ≤ Δ) (K : ℕ) (hK : Δ ^ K < 2 ^ 128) (n : ℕ) (hn : n ≤ K) :
    unpackN N (iterP adj N n) = iterL adj N n := by
  have hb : ∀ x ∈ iterL adj N n, x < 2 ^ 128 := fun x hx =>
    lt_of_le_of_lt ((iterL_bound adj N Δ hΔ h1 n x hx).trans (Nat.pow_le_pow_right h1 hn)) hK
  apply List.ext_getElem
  · simp [unpackN, length_iterL adj N hlen n]
  · intro i h1' h2'
    simp only [unpackN, List.getElem_map, List.getElem_range]
    rw [iterP_eq adj N Δ hΔ h1 K hK n hn, dg_pack _ hb, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2']
    simp
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- same as `h0_of_chk`, with the vectors computed in packed form (fast kernel evaluation) -/
theorem h0_of_chkP (N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (adj : List (List ℕ))
    (H : AdjOK N R adj) (Δ : ℕ) (hΔ : ∀ l ∈ adj, l.length ≤ Δ) (h1 : 1 ≤ Δ) (Kb : ℕ) (hKb : Δ ^ Kb < 2 ^ 128)
    (K : ℕ) (hle : K ≤ Kb) (cp cn : ℕ → ℕ)
    (chk : comb N cp (fun j => unpackN N (iterP adj N j)) (List.range (K + 1)) =
      comb N cn (fun j => unpackN N (iterP adj N j)) (List.range (K + 1)))
    (s : Fin N) :
    ∑ j ∈ Finset.range (K + 1), ((cp j : ℤ) - cn j) * (V R j s : ℤ) = 0 := by
  have hf : ∀ j, (unpackN N (iterP adj N j)).length = N := by intro j; simp [unpackN]
  have h := congrArg (fun l => l.getD s 0) chk
  simp only [comb_getD N _ _ hf _ s s.2] at h
  have e : ∀ c : ℕ → ℕ, ((List.range (K + 1)).map fun j => c j * (unpackN N (iterP adj N j)).getD s 0).sum =
      ((List.range (K + 1)).map fun j => c j * (iterL adj N j).getD s 0).sum := by
    intro c
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [unpack_iterP adj N Δ H.len hΔ h1 Kb hKb j (by simp at hj; omega)]
  rw [e, e] at h
  simp only [V_eq_iterL' N R adj H, sub_mul, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  have h' : ∑ j ∈ Finset.range (K + 1), cp j * (iterL adj N j).getD s 0 =
      ∑ j ∈ Finset.range (K + 1), cn j * (iterL adj N j).getD s 0 := by
    rw [sum_range_eq_list, sum_range_eq_list]; exact h
  exact_mod_cast h'
end fastvec

open PowerSeries in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem gf_gen (b : ℕ → ℚ) (m q : ℕ) (d p : ℕ → ℚ) (D N : PowerSeries ℚ)
    (hD : D = ∑ j ∈ Finset.range (m + 1), C (d j) * X ^ j)
    (hN : N = ∑ j ∈ Finset.range (q + 1), C (p j) * X ^ j) (hD0 : d 0 ≠ 0) (hp : ∀ n, q < n → p n = 0)
    (hb : ∀ n, ∑ j ∈ Finset.range (m + 1), d j * (if j ≤ n then b (n - j) else 0) =
      if n ≤ q then p n else 0) :
    mk b = N * D⁻¹ := by
  have hc : constantCoeff D ≠ 0 := by
    rw [hD]
    simp only [map_sum, map_mul, map_pow, constantCoeff_C, constantCoeff_X]
    rw [Finset.sum_eq_single 0]
    · simpa using hD0
    · intro j _ hj; simp [hj]
    · intro h; exfalso; exact h (by simp)
  rw [eq_mul_inv_iff_mul_eq hc, hD, hN]
  ext n
  simp only [Finset.mul_sum, map_sum]
  have : ∀ j ∈ Finset.range (m + 1), coeff n (mk b * (C (d j) * X ^ j)) =
      d j * (if j ≤ n then b (n - j) else 0) := by
    intro j _
    rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow']
    simp
  rw [Finset.sum_congr rfl this, hb n]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single n]
  · by_cases h : n ≤ q
    · simp [h]
    · simp [h, hp n (by omega)]
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; simp at h; simp [hp n (by omega)]

section fastvec2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def incB : ℕ → List ℕ → Bool
  | _, [] => true
  | p, x :: r => decide (p ≤ x) && incB (x + 1) r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem incB_ge : ∀ (l : List ℕ) (p : ℕ), incB p l = true → ∀ y ∈ l, p ≤ y
  | [], p, _, y, hy => by simp at hy
  | x :: r, p, h, y, hy => by
    simp only [incB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h.1
    · have := incB_ge r (x + 1) h.2 y hy
      omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem incB_nodup : ∀ (l : List ℕ) (p : ℕ), incB p l = true → l.Nodup
  | [], p, _ => List.nodup_nil
  | x :: r, p, h => by
    simp only [incB, Bool.and_eq_true, decide_eq_true_eq] at h
    refine List.nodup_cons.2 ⟨?_, incB_nodup r _ h.2⟩
    intro hx
    have := incB_ge r (x + 1) h.2 x hx
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def chkA (N : ℕ) (mask : ℕ → ℕ) : ℕ → List (List ℕ) → Bool
  | _, [] => true
  | s, l :: r => (l.foldl (fun a x => a ||| 2 ^ x) 0 == mask s) && incB 0 l &&
      l.all (fun x => decide (x < N)) && chkA N mask (s + 1) r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem chkA_sound (N : ℕ) (mask : ℕ → ℕ) : ∀ (adj : List (List ℕ)) (s0 : ℕ), chkA N mask s0 adj = true →
    ∀ i < adj.length, (adj.getD i []).foldl (fun a x => a ||| 2 ^ x) 0 = mask (s0 + i) ∧
      (adj.getD i []).Nodup ∧ ∀ t ∈ adj.getD i [], t < N := by
  intro adj
  induction adj with
  | nil => intro s0 _ i hi; simp at hi
  | cons l r ih =>
    intro s0 h i hi
    simp only [chkA, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    cases i with
    | zero =>
      simp only [List.getD_cons_zero, Nat.add_zero]
      exact ⟨h1, incB_nodup _ _ h2, h3⟩
    | succ i =>
      have := ih (s0 + 1) h4 i (by simpa using hi)
      simp only [List.getD_cons_succ]
      rw [show s0 + (i + 1) = s0 + 1 + i by omega]
      exact this

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem adjOK_of_chk (N : ℕ) (R : Fin N → Fin N → Prop) (mask : ℕ → ℕ) (adj : List (List ℕ))
    (hR : ∀ s t : Fin N, R s t ↔ (mask s).testBit t = true)
    (hlen : adj.length = N) (hc : chkA N mask 0 adj = true) : AdjOK N R adj where
  len := hlen
  nodup := fun s => (chkA_sound N mask adj 0 hc s (by rw [hlen]; exact s.2)).2.1
  mem := fun s t => by
    have h := (chkA_sound N mask adj 0 hc s (by rw [hlen]; exact s.2)).1
    rw [zero_add] at h
    rw [hR, ← h, testBit_foldl_lor]
    simp
  lt := fun s => (chkA_sound N mask adj 0 hc s (by rw [hlen]; exact s.2)).2.2
end fastvec2

section fastvec3
/-! Chunked packed vectors: chunk c is one Nat holding the BB digits (128 bits each) of states c*BB .. c*BB+BB-1. -/
def dgC (v : List ℕ) (t : ℕ) : ℕ := dg (v.getD (t / BB) 0) (t % BB)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def stepC (adjC : List (List (List ℕ))) (v : List ℕ) : List ℕ :=
  adjC.map fun ch => pack (ch.map fun l => (l.map fun t => dgC v t).sum)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def iterC (adjC : List (List (List ℕ))) (N : ℕ) : ℕ → List ℕ
  | 0 => List.replicate (N / BB) (pack (List.replicate BB 1))
  | n + 1 => stepC adjC (iterC adjC N n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def unpackC (N : ℕ) (v : List ℕ) : List ℕ := (List.range N).map (dgC v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem getD_map_zero {α : Type} (f : α → ℕ) (d : α) (hd : f d = 0) (l : List α) (i : ℕ) :
    (l.map f).getD i 0 = f (l.getD i d) := by
  rw [← hd, List.getD_map]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem flatten_getD {α : Type} (d : α) : ∀ (cs : List (List α)) (hB : 0 < BB), (∀ c ∈ cs, c.length = BB) →
    ∀ t, cs.flatten.getD t d = (cs.getD (t / BB) []).getD (t % BB) d
  | [], _, _, t => by simp
  | c :: r, hB, h, t => by
    have hc : c.length = BB := h c (by simp)
    have hr : ∀ x ∈ r, x.length = BB := fun x hx => h x (by simp [hx])
    by_cases ht : t < BB
    · rw [List.flatten_cons, List.getD_append _ _ _ _ (by omega), Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht]
      simp
    · have e : t = (t - BB) + BB := by omega
      have h1 : t / BB = (t - BB) / BB + 1 := by
        conv_lhs => rw [e]
        rw [Nat.add_div_right _ hB]
      have h2 : t % BB = (t - BB) % BB := by
        conv_lhs => rw [e]
        rw [Nat.add_mod_right]
      rw [List.flatten_cons, List.getD_append_right _ _ _ _ (by omega), h1, h2, hc]
      simp only [List.getD_cons_succ]
      exact flatten_getD d r hB hr (t - BB)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem iterC_eq (adjC : List (List (List ℕ))) (N Δ : ℕ) (hB : 0 < BB) (hNB : N = N / BB * BB)
    (hch : ∀ ch ∈ adjC, ch.length = BB) (hΔ : ∀ l ∈ adjC.flatten, l.length ≤ Δ) (h1 : 1 ≤ Δ) (K : ℕ)
    (hK : Δ ^ K < 2 ^ 128) : ∀ n ≤ K, ∀ t, dgC (iterC adjC N n) t = (iterL adjC.flatten N n).getD t 0 := by
  intro n
  induction n with
  | zero =>
    intro _ t
    simp only [iterC, iterL, dgC]
    by_cases ht : t < N
    · have h1' : t / BB < N / BB := by
        rw [Nat.div_lt_iff_lt_mul hB]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos h1', List.getD_eq_getElem?_getD,
        List.getElem?_replicate, if_pos ht]
      rw [Option.getD_some]
      have hb : ∀ x ∈ List.replicate BB 1, x < 2 ^ 128 := by
        intro x hx; rw [List.eq_of_mem_replicate hx]; norm_num
      rw [dg_pack _ hb, List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (Nat.mod_lt _ hB)]
    · have h2 : ¬ t / BB < N / BB := by
        rw [Nat.div_lt_iff_lt_mul hB]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_neg h2, List.getD_eq_getElem?_getD,
        List.getElem?_replicate, if_neg ht]
      simp [dg]
  | succ n ih =>
    intro hn t
    have ih' := ih (by omega)
    have hb : ∀ ch ∈ adjC, ∀ x ∈ ch.map (fun l => (l.map fun t => dgC (iterC adjC N n) t).sum), x < 2 ^ 128 := by
      intro ch hch' x hx
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      have hl' : l ∈ adjC.flatten := List.mem_flatten.2 ⟨ch, hch', hl⟩
      have hmem : (l.map fun t => dgC (iterC adjC N n) t).sum ∈ iterL adjC.flatten N (n + 1) := by
        simp only [iterL, stepL, List.mem_map]
        exact ⟨l, hl', by simp [ih']⟩
      have := iterL_bound adjC.flatten N Δ hΔ h1 (n + 1) _ hmem
      exact lt_of_le_of_lt (this.trans (Nat.pow_le_pow_right h1 hn)) hK
    show dg ((stepC adjC (iterC adjC N n)).getD (t / BB) 0) (t % BB) = _
    simp only [stepC]
    rw [getD_map_zero _ [] (by simp [pack]) _ _]
    set ch := adjC.getD (t / BB) [] with hch0
    have hchm : ch ∈ adjC ∨ ch = [] := by
      by_cases hh : t / BB < adjC.length
      · left
        rw [hch0, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh]
        exact List.getElem_mem hh
      · right
        rw [hch0, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have hbc : ∀ x ∈ ch.map (fun l => (l.map fun t => dgC (iterC adjC N n) t).sum), x < 2 ^ 128 := by
      rcases hchm with h | h
      · exact hb ch h
      · intro x hx; rw [h] at hx; simp at hx
    rw [dg_pack _ hbc, getD_map_zero _ [] (by simp) _ _, hch0]
    rw [← flatten_getD [] adjC hB hch t]
    simp only [iterL, stepL]
    rw [getD_map_zero _ [] (by simp) _ _]
    congr 2
    funext s
    exact ih' s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem unpack_iterC (adjC : List (List (List ℕ))) (N Δ : ℕ) (hB : 0 < BB) (hNB : N = N / BB * BB)
    (hch : ∀ ch ∈ adjC, ch.length = BB) (hlen : adjC.flatten.length = N)
    (hΔ : ∀ l ∈ adjC.flatten, l.length ≤ Δ) (h1 : 1 ≤ Δ) (K : ℕ)
    (hK : Δ ^ K < 2 ^ 128) (n : ℕ) (hn : n ≤ K) :
    unpackC N (iterC adjC N n) = iterL adjC.flatten N n := by
  apply List.ext_getElem
  · simp [unpackC, length_iterL adjC.flatten N hlen n]
  · intro i h1' h2'
    simp only [unpackC, List.getElem_map, List.getElem_range]
    rw [iterC_eq adjC N Δ hB hNB hch hΔ h1 K hK n hn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2']
    simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem h0_of_chkC (N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (adjC : List (List (List ℕ)))
    (H : AdjOK N R adjC.flatten) (hB : 0 < BB) (hNB : N = N / BB * BB)
    (hch : ∀ ch ∈ adjC, ch.length = BB) (Δ : ℕ)
    (hΔ : ∀ l ∈ adjC.flatten, l.length ≤ Δ) (h1 : 1 ≤ Δ) (Kb : ℕ) (hKb : Δ ^ Kb < 2 ^ 128)
    (K : ℕ) (hle : K ≤ Kb) (cp cn : ℕ → ℕ)
    (chk : comb N cp (fun j => unpackC N (iterC adjC N j)) (List.range (K + 1)) =
      comb N cn (fun j => unpackC N (iterC adjC N j)) (List.range (K + 1)))
    (s : Fin N) :
    ∑ j ∈ Finset.range (K + 1), ((cp j : ℤ) - cn j) * (V R j s : ℤ) = 0 := by
  have hf : ∀ j, (unpackC N (iterC adjC N j)).length = N := by intro j; simp [unpackC]
  have h := congrArg (fun l => l.getD s 0) chk
  simp only [comb_getD N _ _ hf _ s s.2] at h
  have e : ∀ c : ℕ → ℕ, ((List.range (K + 1)).map fun j => c j * (unpackC N (iterC adjC N j)).getD s 0).sum =
      ((List.range (K + 1)).map fun j => c j * (iterL adjC.flatten N j).getD s 0).sum := by
    intro c
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [unpack_iterC adjC N Δ hB hNB hch H.len hΔ h1 Kb hKb j (by simp at hj; omega)]
  rw [e, e] at h
  simp only [V_eq_iterL' N R adjC.flatten H, sub_mul, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  have h' : ∑ j ∈ Finset.range (K + 1), cp j * (iterL adjC.flatten N j).getD s 0 =
      ∑ j ∈ Finset.range (K + 1), cn j * (iterL adjC.flatten N j).getD s 0 := by
    rw [sum_range_eq_list, sum_range_eq_list]; exact h
  exact_mod_cast h'
end fastvec3


set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def PO (u v : Fin 7 → Fin 3) : Prop :=
  ∀ j : Fin 6, (((u j.succ : Fin 3) : ℕ) : ℤ) - ((u j.castSucc : Fin 3) : ℕ) ≤ (((v j.succ : Fin 3) : ℕ) : ℤ) - ((v j.castSucc : Fin 3) : ℕ) ∧ |(((v j.castSucc : Fin 3) : ℕ) : ℤ) - ((u j.castSucc : Fin 3) : ℕ)| ≤ |(((v j.succ : Fin 3) : ℕ) : ℤ) - ((u j.succ : Fin 3) : ℕ)|

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem aeq (n : ℕ) : a n = Nat.card (Chain PO n) := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
abbrev St := Fin 7 → Fin 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def N : ℕ := 3 ^ 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def e0 : St ≃ Fin N := finFunctionFinEquiv
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def RN : Fin N → Fin N → Prop := fun i j => PO (e0.symm i) (e0.symm j)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
instance : DecidableRel RN := fun i j => by unfold RN PO; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def dig (x j : ℕ) : ℕ := x / 3 ^ j % 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
abbrev loc (a b c d : ℕ) : Prop := (b : ℤ) - a ≤ (d : ℤ) - c ∧ |(c : ℤ) - a| ≤ |(d : ℤ) - b|
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
instance (a b c d : ℕ) : Decidable (loc a b c d) := by unfold loc; infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def tabL : List ℕ := [20846865178723934380970846233771981055320763238734095732654064959154334347012554342057548580411881415202222374317679366490732876614792037268957482856443445990428070490190314551271960486748792107708227833696222973366670409518110100589375614759969024874004340405176960413375784002659110760362582327585345719561408632996186352791510108372910553780486464114411680069633389228954159500933304323148675449283357578516881545170303121291336198391926659296082619235698799408395847393230155713111534520507078003426408117262298984207107739022224364735509936359236025809272438808141208149071765886163448849643943250390648942419437318431438540244767760229158687357815731161, 8814742147451980710769913840918385224237109191853740267507004211058915157299177311652240414550478399662673308379568442490796142331835956561927054061921118812020325788663980782778841643445578058227580479364153477110642879288841480164640851906963646881185767613182647109249802960955226537151197601516002418419200267651664419784993703328926238384983705756622274870880925678204718605045794639809165094834400667448998539184060516402256320673119094839781234349132684739279428073247423134508048423047390276290235990385750099030489530241955333926219846240691765669882637973844062642313643080830210930082005602702177142672066519421327078327597361619094582392311091400, 2820717487184633827446372429093883271755874941393196885602241347538852850335736739728716932656153087892055458681461901597054765546187506099816657299814758019846504252372473850489229325902584978632825753396529112675405721372429273652685072610228367001979445636218447074959936947505672491888383232485120773894144085648532614331197985065256396283194785842119127958681896217025509953614654284738932830347008213583679532538899365248722022615398110348729994991722459116569416983439175403042575495375164888412875516923440031689756649677425706856390350797021365014362444151630100045540365785865667497626241792864696685655061286214824665064831155718110266365539549248, 22301297633053511198247882017523514617319886255389962876792720653979055347966918598480168248812710351146563470200308159501714240099544970101675446776660430594411424245319871380430469357917312487315778612791308297089926484600768944816541355324618026609399992061352097186402001491216723138992529931835486118600576677158710982056034069422183383114008775564254355423328741965857938070765860438717187689931033688645966304135673106497708491302991309944646522903305692390376953025315980530305362510309897399014297055675947750547138511512146994833336210988950167144803074073825478485053516994500433653107474174836508170960328294135957508168821324896309293452547061242, 20494275492825855152540049680135245646351278871059946121953784790711977740720587249591458963829862279215715441982496628791101030921518599006480400693966601237947257458643755319960806821010968985379124614521656834282244694346556441382789980683690478998756909700649654529005791884220901698876534423524705622824640622290119776000110360239753504245087115884146789074798152201825970756731472537556308845489981551818921603602940700635245945565001895502491369861733492018824670270300258787731212583585182392374798677646868980245888157812546151378461142509608355182477133289187445643379220162930240412440663026282561856712554657654585457111663865764394904062123287505, 5994024660267346883323541411824501952481234250460543381904762863520062306963440571923523481894325311770617849698106540893741376785648450462110396762106360792173821536291506932289612317542993079594754725967624364435237157916412206511955779296735279879206321976964200034289866013449554045262814369030881644525056182003131805453795718263669842101788919914503146912199029461179208651431140355070232264487392453865319006645161151153534298057720984491051239357410225622710011089808247731465472927672225387877360473462310067340732880564529627069829495443670400655520193822213962596773277294964543432455763809837480457017005233206502413262766205900984316026771542152, 22036855368629951776924784602295963060592772979634350668767510527647287893247943279130601036376195999156683270948921106226990355829589891404817635154802797030050814471659951956947104108613945145568951198410383692776607198222103700411602129767409117202964419032956617773124507402388066342877994003790006046048000669129161049462484258322315595962459264391555687177202314195511796512614486599522912737086001668622496347960151291005640801682797737099453085872831711848198570183118557836270121057618475690725589975964375247576223825604888334815549615601729414174706594934610156605784107702075527325205014006755442856680166298553317695818993404047736455980777728500, 18422811088174639685509119927519425118655558210974317159089638801113132678755280581353182466410499855294987214513298044805763937473537149214427542989415138317122480898307719836007779034801258141695643201871080767161243617713678693544099380485554021981678254311551732458332088188396423462646002987168445054496128559391978637350636839957455838224615945031340554480141134667447861884545710797201155048203897394968406946894686479280715710206818908215142779789687311105094004673087114351121821204169045677446593219906217706973723118205686647905799478643045790250054713365334090922435514038935140843871391709647550228184619025590573593704678485783907677199930181026, 12032123031271953670200932392853595831083654046880355465147060748095419189713377030405308165861403015539549065938110923999936734282956080707030428794522327178407744701526333768493118843303214049480647354332069496256027530229268620424734762853005377992818572791994313304125981041703884223211384726069343301142208365344521933006516405043984315395502758357789405198752463550749440895887509683339510354448956911067883005986242604889079877718807564456301384886566114669116419319982732578603486097459687727136172126876548885176618208780269030809290090118544260139389800834297145506758122805333237919561937647688471799747370799010111461917170398610064104965504639761, 22483092439897802672717469321589657593594354578792733438295334821834514825079535341900876539974302485576381418620966401018916161133117704399999393597151711042420365203700335257273015167294507012802897780170162100679190354374579033712283192057700791391022242116765814425832071559345760195048189846428861596888371285068935181120158785366458146994230571894358890153156744822899543342285363805117901329955268029537653604728170300247975693568662139066750506200914781360211357377221633615146841934078760552524087830777389432779862701415933789370552736962299376615435480584865590240822367862400144200945633738069080541528343428464638313616525186197644022129809456647, 2771822058092122918480065292144689263843256969634731566116573709305931599321758016999131015683129467698523481603460188191467287018937930740041493338123058985499956725137136991234469463721738972595616557924052091122539731699933697738315095280119632968772592531288052722126041056964040908280987241296975189030462409462640865803460500718743216081344517774109638816584489053020297273888595124090572568954508000772117331982091022771737090293137871343419770374836892174292072174332246725679882529909012736606741196389236022414224445982183169085391880292984395602123698531972631006042673794321385852299095442746813042691852637535611483234382409817621963968259821056, 307913407190967006782771410192684075306519324897587884975414566969979817498967260729779796057661594155270996437615885518340475364221353989781133562403776567710127542475637695706671374577029801251671876254526940910119406081658939735738192402564819284012056275986001951340536563498717497296564432098947992359209536481855526858618306870903997967812625971001114140614289085516683055810579454010495368909678476110940350178960859982453762254303881563860039581669882576098403331147344396517270526212500438520861682046276598714706642730066778600937436040357563581750343599125620975286146448837611099235655644757294050305538847997013035238881274425389986016868958208, 22521589837971700773178686564666230853208044653230898885263677459592545100495065172720649385493520391568656683010930926805749386688775491253847189665372932115596556267408217281949476022022298424149423146931339623293971404233917304852720582408019936410681265952693553431703600512397023874453001321274911937348473719449248348283211210780329448772623588008401406922408123167541454990670189479576191375563844659384364076747806233879586266604416570670203237513816203484813198995486229457873944372038869125951369178544520153005671837674928611562347035005446346015428871665574445783825463297964767857323230073506551216038399106805939667948321198195981412234877206072, 22482491046524382815282346721179125007509771533236292836957492215258401583248482671469763688810127365275296904956049182492513152392171959567988102320662641166311556360843937527398588074766036251472328108536852477747725277409575793595611828400664531978358156069351779265770859573870176762436282494022418339090794703942994057044263046485850912623199687859259278602100857539529393570691983767121787081187866313763999424356727017318322463564259201798071092061106832370804915183215486458122394140082251762605101772804642798797998040004351627693597781032533053249064874445023548012355012107617258241767439098137913951586340422902144147532074246208531932313370259463, 2463908650901155911697293881952005188536737644737143681141159142335951781822790756269351219625467873543252485165844302673126811654716576750260359775719282417789829182661499295527798089144709171343944681669525150212420325618274758002576902877554813684760536255302050770785504493465323410984422809198027196671252872980785338944842193847839218113531891803108524675970199967503614218078015670080077200044829524661176981803130162789283328038833989779559730793167009598193668843184902329162612003696512298085879514342959423699517803252116390484454444252626832020373354932847010030756527345483774753063439797989518992386313789538598447995501135392231977951390862848, 22521054221998498712650530498675600268726462878282193974697161388110694244489283888117939502425426925050503288028114029055671707028870687262837133372249854257187148391739238053780064392739129152339384533132923240370635320061961294123810149150972017871277314316715428367274083587832832379783021335537923410872507076883957034653116568339788630660924206914640815384748973555789915350344835383235902122755377506273453322354489560020363858631745204665285634295549748916123086416449504646149045555510728484929772220662542682115573623605238248818809027380498214267255050572277626924096724578861260049930150472317855971871302679976843301279357079768178457242111046080, 22208263890419955049479811750778753503140277918325345588247679433437546106516623878110853928958282714703625063589060074549781832656042433775964434614567526662907149139225000017372960814689031770922624225977026076000666305467229204066940117092128782412692435249981235039812156079618055483649270717517974624811074952833922704741531253983960341465533005721503788822290848531693423990519189683600667767747550741310536103225855827530253434310486253688228470673874780004056815918283560648136643699857789578159632974743523848454183242240622377868814995597191872136343072807870444752333115056081183125483822669368757856254833208746479137949381463868582617870055473208, 19711270381805679754237404029444968329751097609158001872178761112528583225757777324901745524291173017877857937017506212827448874114179773659957900259028652056920408478563198266038545703572768040207281222246110009556650622674645335973968096777581158422249649585477761703706030502381719286767202605131886407857908875606294315316698284647714930912886054120249251336572255769879246068396768681027328761000760028765536272746079277476238603275524267723330735826077889185919285202889386889466959404169747815917346634388153410365638255433750620285160856669314981013311782052892959234779694068078758348646538295322267498836490790929026830382142776380022058161549635591, 22521666019268053741650200330368375777701162350795322160475813150696438562012601053253336278437794396275054384141150489634381451760575278610886057917518441287149530254960464321345171985290758562474748438689796045564778721758264218933327199166637728459681268056471665019193712985119163731452581715259858626696459520196048804849891460714522171721094651437093386774785608160061102914171765975675394109535099461206344233303015777427670796675303109713976523503341369408900798918726216312957908249322359407276500985102456846479554026083492662609541827409836187932313321932646606983124127215235738835693281068305767982321715285605021385189544896770914607571853640191, 43987461472125945534256510236048276975245744938970889214576545039659577473055972649857471223545707500880617809992714285813811812070180905441424703180640181877382722644848788063994960322243843148841627558059478656216315288245338606130014482217235069405488323072251388256617403310551812133495531469296940838048416839287503379919449001112178893326245143895071191350796324181614928278845319506729451919257929225487409562240710137897883461408362494479913264471072390980264811577702995337568909968152247905202798927842893223254606403624354345144911590007641550505063501668192267199254746109396162448329741280584633048564727809233508587237861894712459932404285440, 85745538930774057476854012311293388400929810983617077990590121303998184549319867289331942334282482788496431651767544816450430572195188853724653375344191108497972790948418939534139087650504862265503549151709724659897331690986618931392114028231523356319395046034405427407432128378558788070408633111558586235889273602046647163090746258348159418431621931772104012710324121638369881543720433210123865025752161817998676420760201597342429753075793711652746243009757109638326447183583113966796670993447280547883075039812376309963486532700635756252703561760767626039496582147982725107543658311378199417200078481044800091716784067466799278416259767014400037224448, 22521666186739809468250556298713731650756775598390875213088266892474909923019010630653956142487773898045422717546289021989278470995428415138682429715897772955485304277681734378223791772692903111920961340761400071804481595071668910339361239255356802344133789779688828142134475360108110972612516705399812340142185012054895455491424252761199718777931753083827416964248738427544337177583427364933167779880346659891063336772598312615746999748981954951368043593350126604977024765918004886918973963470640850371649539838669749761289278370089525123693244164604046895524151099070053288431847232253779891787975126127362119701454962145125143333851697120163884521572531712, 22521666019267414887601569928448021008975593598890946832270409337885730053213346172522906093631735602444672435768514525839406710832041229587405380395889371143931607574072154449262190376933223713668110131846563655659089737627495015839001339180903264872067629392015063615197108263666812577599205812576791240597422300714611231464637564543942598609423828344197404941955208110279971735124849238405458200374052390993490144744625050709209579677222629393574469061534302415164995574553691455085306031573845614292362203670037702303310688271143734407354552747011820173966520177620329853905042365840079689545974967285959331720201268022398344632134576136680534858545496575, 43901715933195171476779656223736983586844815127987272136585954918355579288506652782568139281211425018092121378340946740997361381497985716587700049805295990768884749853900369124460821234593338286576124008907768931556417956554351987198622368189003546049168928026216982829209971182173253345425122836185382251812527565685456732756358254853830733907813521963299087338086000059976558397301599073519328054232177063669410885819949936300541031655286700768260518228062633870626485130519412223602113297158800624654915852803080846944642917091653709388658886445880782879024005086044284474147202451084784248912541202103588248473011025166041787959445634945445532367060992, 22521666186739171859526704835603272593116788685598679205381188280120234251316910059173607019328885728160838976172929856356761127881128073158090388311111172809075183257292745209054607175145727074713063391030277406902003850072410720515532512579759936072854954007373711278380799200868368733857785345739934679668363735029340963923796793743265890607438541496823120032528325005057510495425598207210140963620839564092572225964044841990704414044717160381712622489783734245159216857494046313998050592971232474823022900272217273457185147808801503531275095239361707533495843056266136494040303552436830087924609429685270762726563616311558805862244739041792595664299622400, 22521580440873146567245683259559424001151604941635348226638120330460140910816707496075982005037278380576694705952387827622419924226889070904241136466809445293582471009187821580714692546189875169253244426634032340461372838655376736331263674459548750374980835518406273486448845822923590487042608220353131712749855528803818262209012426507620364331381074806256964618240802565702403956633597425022836256398173888535097907641734745843545337303942474791402462200081749061400270878965569215160069461812071602227906781932608974972147017148556656765865089432141626095988811274007738016316211948622326540020528102887043316324672225475437870583078795498317568194457632256, 22477678557795927796115943820132327500725916605856351271261236605656778984539545080603478807214248688774173766331157775348567639948505097705444633214337801105272147532315615533281177024968514719325906811131736566908562406470018880327197184684420493390275779733399413630937095581808611919319086183790561685858411103356761301469972011713409992827768406293198315583434811835879487985892920656168664657615841531980856823740775067289772913213894747219496610238870297017920534107148513317620339339354207159371298186174613953256299419679868308264396915819828546381808258430978414715924872469126342673244951327025183349273150557795787876602307034876202147639449354751, 22521666186739810716017120548803727617044105281317293832801043101295390147903042879997698559476673313839136197245171175848418762501840300941284959666366100760083851095993723633261258305587320320392793052927295452134715309226440413309256357582080657538932515382065845807525036037516686020270023374291683590158240461553988803205899394803658972367564770837141450893329554334533042277865004709184213718275223001007026273249077922549972574564729784093614022974549296036283095376747264286718135873520524599120661566448214414023854933859172902857940844598880549625614831818364002994106340953012050138698693316258656178003363766921592266524457337061975707448684576767, 167799489101319085551899017330461219236649435811977675183447735426194286093589374750415495656285034053851119087174716001893456485962759785671781127695839504674386621556447430209666450445602141282628857795762568165832616672288626033802805455997573597682840480761214929268896673068405803160462564796443072042436227576028295347122647603572456045331858360337744116776215042222003632371212827710057746098806230425247936245162213332677269814336737703844620741021070132692136143225134032870141361185518269576164693733005032949100534949026724043559406774753878524807313945213757834350588658885858018321106326392524828598153631103252562636070046169822864080896, 1250203608357276597578990606602058526594174062676884012952559516204782043905330192982573075043353691392306094125261235541585216820709557348420965916309319758379451818468286667596131474998491665685493982827442320166914981745751498806544232055234659650125424523072338441902937266958696920730087930593692054603111585318285406988772823148273021413868775497952088608872048303846107996443121048615694558268353154972276014467706775778236170661714987507164784582232982057921404821541778694771248518656056974774093615889066577579178618955427299083054890920217458036891757616116162888746313621541690970339088815914969138195765669562614233765346214412288, 22521666186739810716017129863546474247925813985182453896174929756945122289193368765659211596192083922847023091503918630096747521013203918631346285137784951905112838918300342412957187030126614365506008225081810366514756000362483034562375267324353665505026960697965502957507605696993861779741362996706943217492879042088252351703079470933545874469977394334771608036134973302786439467102707447323756447633977737605964439701655525719538401953197398539297636761148292377658525673116375382922363222063970187473967528947516198552877673279139839372768775218284835335259674365062600147394513711702854620232737054099866763920384679052850491721492620678146064089173983232, 22521666186739810716017120548803727617043588209224005344018400932746777724053301659360033306313872366419611145836224115026507326734036676626762129894908754337685305926125845416547523141651525634508481564032668274636454234688053527011851891939852366043957498026994409693987475160230691352527257713514542808310137713291394542187613547554828188674943931643119241901558921447893574976387953109307170825514594270637328878365086300414506524754526421628689187604957170416737563396568536698571918036160314082232491239072653839047653957238309875385021108570883616526043710875459983833913689724033262657931915853871190586884750002490786748130400460051817334790185549823, 167799487851115477194622419751470612634590909217803612506563722473634769888807330845085302673711959010497427694868621876632220944377542964962223779274873588365066863176995611741379782849470666284137192110268585338390296505373644288051306649453341542448180830635790406196558231165468536201765644066355141448744172972916710028837240614799632897058836946468968618824126433349955328525104831266936697483111672156894781272886198864970494036100567042129633233856285550459154085303729211328362666414269750920107718958911417060033957369848105088132107691698987604589855908322000218234425770139544396779415356053436012683184492907486893073455812404476649668608, 22521666186739810716017129863546474247925296913093017894669050323325059441537187397069825432227224905882808324176274810733197846932385392017049001793826246301398039531085625901049235291363177326671929594445721093634341477917534114329434004615561664949540182366884032457842281945662342894298284396943863591537299579766112811798228758296452347648904739943718300055595917563079433807029820373432168069407848319455459562105613655406578181048697891887468933812588382242729440200667710692088289219085468886912788032620811831628344807645839675879908159704400217634333252815402150372387218398564895698298012959632762177067700116420165205664564190382990127028261355520, 22521666186739809465813521506269807268693116926017679095518637094430811632762177198735446480420193877615230923365485411442769421978503941115550870371046996018543336764684696656694463497290286124606487646524648178147131161717944021674435113788849297219661630675378255254934508736844876313635403827157085713574484351033890194700915186955625082602458394795311360132422011607723822383703090224913837875710555007152860597370452169881397557908215566744121444289222665898397481609143684783447762869746629047919914602415301500329627454645082364225192591011396385553427838030951018405194305750697817824269086962703313515741525069764194254826687291355352866797826080768, 22521666018940321614698034996904710286582886044667858020823367917847654721708756786408323809061177657554102143394052088673702760608383814978525173994584973064244346421607102076813828095920869874790651770298437656372147143393823741020630323779275201541358917699225365046310106768620012951864220213829118793715168419117761227177604047681011368795108725505283090555585437558318000055861372337971386008217476902200795848001141677387759241887459969756876319129928555015212962684611121061584103003379163413602391990283520681018821984758637953831216801039473774871736307011050057780348506602423391252840674995152329785478535168767961163271894700991929537625820495871, 22521666186739810716017129863546474247925813985186306383480395759255528225306046614806015783362361485416410192288555793883220956582899125251605005129562725882506601950552937130743037028613724942945206774074565731722509018203621859086694891702505789149248379492764128954658177686367005786564097351730220857248896795753594553827344860774239089415009209001036929184038180532171405934621876998933332616071502869343069751680296070828942660768296524318514575998050877711725996291934336543312236856918570839024953618674935867373165920916007713633262067920865159997905023997638198207988434118122436006439382305640378426735238587143494206140670760986215130628161011711, 9314742816031123799160975260757161582643804291788298254724052151428144728593699020136727752430233745574105183356989588791059861856386336107801792800783986574950428848392030127205309640816410244454770771873752347448778717277455105866499503520221314472989203264014225852585786452350769173552016198124252440079272321730612406423565147600725660467459964949822487589768574441263170625446226377640202746169834122004403205830942304923766897673315179487784623426334993385771720007997224583414124383988566261845215011163618147139600709426002908866327704030313548771754880890484343555864078641696554212458736702290816860141237049167400717516800, 3852487334169269478406293788274468539591718767601653390894890385945837574809155922324104483281472823337927400648512737365040060859762818786666312098091227335164062614108375350575376316177349367269227191473729154191380896475435893355724686580329527646551385644360886841082906351259795938985057314863287039619915398850473909471038936365706917965847578041229406184574939177770181889226977152819118342049616263123026275444069875109299704529067702992299252920142496111756685404866797369557043035336023248598459776069201176023730084123500626302255731456421657369051403046254917943231898047067669313605981227867701248, 22521666186739810716017129863546474247925813985186306383480395759255528226899398031271474259176472311138130302909797370563984143657840869015723623015482840695140367148725687187281708456306454595286381308491001860560120053020109794236158160574998420702148373934968273587836299078621375318714397882031014019340985914035785896197781177484917445000145216994364139753251430577960306883046741408142907408619769529658550024270260670759857174438943370353523425101724167876509879451269469179917427636907940985306732073575804959694328321423810276907915871758130590533836884775226709067671811808211892868834859144487836140205471098531016483900680454608103444594863112192, 22521666186739810716017129863546474247925813985186306383480395759255528225306046614806015783362361485416410192288555793882948402762950050665269240912290233329318511005002771125238786591550624799069448964655095087136522127276026394473416411379471576965192776938242860153325561869189289368227531098663026755124302916796791390362144958207987882940053235252125468194870568464665805216062476953666040810956674717719140195681784645065598399763635682206012755272703108601405347870209120561930158836098880906140851672298785474774674773632135943720802631878897931130920324803500932046378734321256525681390026913741708041819268993194517436242885558203793759877208211455, 9314742816031123799160971408269827413374325885494509980255512559709377126940308125246341806592658936418182859252506307318236523928985687595064427760723126812131642182079932035977974476753796136079420196497436170099411448050263632137345312139324839037095847539327645523058139900965124812665175115217901180283333336673297543136525527685326809993550493910886121882850608593685129396040041802701024975987944895027250386712600255307503774647039735417909514126630464318068727708744304440918012627303161395047845454120582811116352110966226839665151680300229425271128578634752887134206709590293507957540793470392769792471923443186172849815552, 22521666186739810716017129863546474247925813985186306383480395759255528226899398031271474259176472311138130302909797370563711589837891794429387858910935966011523841444486258272272870076575420316144884751420136664962057874183447157903538098307062934417834036805714935240219093264102650389179077076918123739200891023129541037668825827128234494592369621366905979038030346301539212276853685304846134371826957366953204614535029972791695918320210981428233745241390017782902948425061738370665095492789258892443146557389458016133184402048066538840693170661405277017408442991859061025779448524468488413268141429572817109302761803971869798683207083705006996326449152000, 22521666186739810716017129863546474247925813985182453896146226489777121933111123562731882540408869998752535070457727540258168879231270418931766027002973359310730366651360804680661792821553124703459208984109536947004007405229656358280324752973034950271685981081524407057756533863824939910231556641770899389997399092905560124942801127095380913910461955998105040888374788194119271161981619272753293748954490890726250927536805310198973214261829265984593173122579205721151741084801660695741447276954918536235325401063743021459152653216377741917213018375881806224449149099788978018342275577116621285426777167031240253729718994163781578413298555946256578389607448576, 22521666186739810716017120548803658216802014824211045626318813115451236437007791890753864355217632891717390055560803363649475382477715768262016214069700869496170494148760136346756462078184876550915079568764924915312264563432849985334347442923788511694142512993260608733343704697163741772338244765943768506479723243737396429574904781501917358802602785435889328458377713072206456112134287230358891352900877423116692111477549900994820656365090693376209652231153204396546508507310910208318851085198562841800370204550551878806904075700996550015114928320155733994996157669934167894439662363241545522095826441561736730181026128406791915323810619749165963227443494911, 22521666186739810716017129863546474247925813985186306383480395759255528226899398031271474259176472311138130302909797370563984143657840869015723623128208458564711932390036470899999940399003451938771468124775412134017692548607935142841799418752508522702391487435752528490558874298001456800328367068599759687791009060710220417866067689806090036461309280278768036484487498315967820710844982760117604609439431154591959023140487277469586674955895706586183093741496034738506097218587683082574586533217875707440590201909122309349605789368263576415508966466808423651885875092018102366872146133715236017731771383511035532926276383065269697701003680530695757822687182847, 1593351416465458475814111484716420452687365569411769295579188089364794741187817286665966818199483376215017056186356390575574624947162515513945828735692417856298057331268262488403009171954762944302239451538427841928525548698360422550791889731885003376267283698188211206998903531736603997842586586754097946045113573801955050661257851748847983599156195077441114681234150570485195462420528354646223329696587979504150026284791790370061137890944794316418653480149207907355036750106487688548162987323234621280929380450114948276965042432359138170353298639271111263147328174048704309722618003456, 112725617869571565241310830334941051828061928822216629880804846837218579370161655872963901225925706751726982007711565924839718431632465932287846753501911611685326862389246590270876501998377943589651665170378622413724783336955014236617406837421655293422836545843000251758410318353829648518292420746035183525929969967164141102184893769710969790937803635162482462100840682746566901628979828562092649741699125173714345866910732613256534091919377161362808403241127041630638528442764858333648898229265248072175617835008, 22521666186739810716017129863546474247925813985186306383480395759255528226899398031271474259176472311138130302909797370563984143657840869015723623128208458564711932390036470899999940399003451938771468124775412134017692556582989981820657376622292117781429636251681663364133246565240603802421309871873386179061056683850002592550658912005406539073633368208169912295100765107813056035892005304712416817301893705332191267615274619407764899319816463301682345544537060400016734099283814754756212143361398753990690261605430096430215099350009070407227571923037087571102574879960687705579755309703032203422566034771976989554842900514148134289591220355809424131250716672, 22521666186739810716017129863546474247925813985186306383480395759255528226899398031271474259176472311138130302909797370563984143657840869015723623128208458564711932390036470899999940399003451938771468124775412134017692548607935142841799418752508522702391487435752528490558874298001456800328367068599759687791009060710220417866067689806090036461309280278768036484487458399161630016448749632663343872668109805566750313989657226524737930718061151318826102799683131133326514997514150586581558661982791237498238112303517811221105263175799784698949513577877820388720345321749089879339906070594620546430424402497149288163698872719624886107894590720269985472854360063, 1593351416465458475814111484716420452687365569411769295579188089364794741075091668796395252958172545880076004358294461753357995066357668676727249365530761983334156105342555736676027164243197019462521019905961909640678795196448810865465027342638413105390781699810267617347238361357981584117803249799083709427706736380299757238421305905847731840745876723611466162941729824450011936490558387482082227511694209793180235346988155207578675790104111569851751851169379345262387008407362514833817120412502008024395288530737786914156639191232096539714770196506252929498429944783456237547000168448, 22521666186739810716017129863546474247925813985186306383480395759255528226899398031271474259176472311138130302909797370563984143657840869015723623128208458564711932390036470899999940399003451938771468124775412134017692556582989981820657376622292117781429636251681663364133246565240603802421309871873386179061056683850002592550658912005406539073633368208169912295100725191006865341495772177258156080530572356306982558464444568462916155081984732048284062820221105903679356506073633612675035849650997685979200865829787212987180000072923664242225491612468947742254052099247581518163094217116108455370477743294112868610323523184075849668593498682886435402919444480, 22521666186739810716017129863546474247925813985186306383480395759255528226899398031271474259176472311138130302909797370563984143657840869015723623015482840695140367148725640565058888570941523116554838243970565296799113186421334108856756150696585366054447628540115738524414814932774671514574555805746639666885918041771579977421397387680488890559296842474843498750846457543278363001711851732296117146663073023014630852854058800097767914102325904025847578029454283121208651713062547228531972615969680109794839305859693678656247474531318572779459679486908234423562216746782788376434443979428725239155040139163814805216867837310531488278228512436107117009785847808, 22521666186739810716017129863546474247925813985186306383480395759255528225306046614806015783362360826421709850222431801152214848078652779650928881940391171898745114190553094684982884212647061363196843177612896620071863812915517286543742087484246034299382315480989584188319422759573614871802818370239337136999119328825217041598783991617878829462405748542164038641900911561869874665731408958162553948181579405743975423984292200028471993721745136100987631320967680092282767521999703578424560248426085337379452310964327992930952309219055669060472216360320735103722887768783481085942765683600287740766728951151897362572977743794158434553675506481991448100069179391]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def tab (j a b : ℕ) : ℕ := tabL.getD ((j * 3 + a) * 3 + b) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
/-- bitmask (over the 2187 states) of the neighbours of s: AND of the per-column-pair masks -/
def mask (s : ℕ) : ℕ := ((List.range 6).map fun j => tab j (dig s j) (dig s (j + 1))).foldl (· &&& ·) (2 ^ N - 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def adjC : List (List (List ℕ)) := [[[0, 729, 972, 1053, 1080, 1089, 1092, 1093, 1458, 1701, 1782, 1809, 1818, 1821, 1822, 1944, 2025, 2052, 2061, 2064, 2065, 2106, 2133, 2142, 2145, 2146, 2160, 2169, 2172, 2173, 2178, 2181, 2182, 2184, 2185, 2186], [1, 730, 973, 1054, 1081, 1090, 1092, 1093, 1094, 1459, 1702, 1783, 1810, 1819, 1821, 1822, 1823, 1945, 2026, 2053, 2062, 2064, 2065, 2066, 2107, 2134, 2143, 2145, 2146, 2147, 2161, 2170, 2172, 2173, 2174, 2179, 2181, 2182, 2183, 2184, 2185, 2186], [2, 731, 974, 1055, 1082, 1091, 1093, 1094, 1460, 1703, 1784, 1811, 1820, 1822, 1823, 1946, 2027, 2054, 2063, 2065, 2066, 2108, 2135, 2144, 2146, 2147, 2162, 2171, 2173, 2174, 2180, 2182, 2183, 2184, 2185, 2186], [3, 732, 975, 1056, 1083, 1092, 1095, 1096, 1461, 1704, 1785, 1812, 1821, 1824, 1825, 1947, 2028, 2055, 2064, 2067, 2068, 2109, 2136, 2145, 2148, 2149, 2163, 2172, 2175, 2176, 2181, 2184, 2185], [4, 733, 976, 1057, 1084, 1089, 1093, 1095, 1096, 1097, 1462, 1705, 1786, 1813, 1818, 1822, 1824, 1825, 1826, 1948, 2029, 2056, 2061, 2065, 2067, 2068, 2069, 2110, 2137, 2142, 2146, 2148, 2149, 2150, 2164, 2169, 2173, 2175, 2176, 2177, 2178, 2182, 2184, 2185, 2186], [5, 734, 977, 1058, 1085, 1090, 1094, 1096, 1097, 1463, 1706, 1787, 1814, 1819, 1823, 1825, 1826, 1949, 2030, 2057, 2062, 2066, 2068, 2069, 2111, 2138, 2143, 2147, 2149, 2150, 2165, 2170, 2174, 2176, 2177, 2179, 2183, 2185, 2186], [6, 735, 978, 1059, 1086, 1095, 1464, 1707, 1788, 1815, 1824, 1950, 2031, 2058, 2067, 2112, 2139, 2148, 2166, 2175, 2184], [7, 736, 979, 1060, 1087, 1092, 1096, 1465, 1708, 1789, 1816, 1821, 1825, 1951, 2032, 2059, 2064, 2068, 2113, 2140, 2145, 2149, 2167, 2172, 2176, 2181, 2185], [8, 737, 980, 1061, 1088, 1093, 1097, 1466, 1709, 1790, 1817, 1822, 1826, 1952, 2033, 2060, 2065, 2069, 2114, 2141, 2146, 2150, 2168, 2173, 2177, 2178, 2182, 2186], [9, 738, 981, 1062, 1089, 1098, 1101, 1102, 1467, 1710, 1791, 1818, 1827, 1830, 1831, 1953, 2034, 2061, 2070, 2073, 2074, 2115, 2142, 2151, 2154, 2155, 2169, 2178, 2181, 2182], [10, 739, 982, 1063, 1090, 1099, 1101, 1102, 1103, 1468, 1711, 1792, 1819, 1828, 1830, 1831, 1832, 1954, 2035, 2062, 2071, 2073, 2074, 2075, 2116, 2143, 2152, 2154, 2155, 2156, 2170, 2179, 2181, 2182, 2183], [11, 740, 983, 1064, 1091, 1100, 1102, 1103, 1469, 1712, 1793, 1820, 1829, 1831, 1832, 1955, 2036, 2063, 2072, 2074, 2075, 2117, 2144, 2153, 2155, 2156, 2171, 2180, 2182, 2183], [12, 741, 984, 1065, 1092, 1101, 1104, 1105, 1470, 1713, 1794, 1821, 1830, 1833, 1834, 1956, 2037, 2064, 2073, 2076, 2077, 2118, 2145, 2154, 2157, 2158, 2172, 2181, 2184, 2185], [13, 742, 985, 1066, 1080, 1093, 1098, 1102, 1104, 1105, 1106, 1471, 1714, 1795, 1809, 1822, 1827, 1831, 1833, 1834, 1835, 1957, 2038, 2052, 2065, 2070, 2074, 2076, 2077, 2078, 2119, 2133, 2146, 2151, 2155, 2157, 2158, 2159, 2160, 2173, 2178, 2182, 2184, 2185, 2186], [14, 743, 986, 1067, 1081, 1094, 1099, 1103, 1105, 1106, 1472, 1715, 1796, 1810, 1823, 1828, 1832, 1834, 1835, 1958, 2039, 2053, 2066, 2071, 2075, 2077, 2078, 2120, 2134, 2147, 2152, 2156, 2158, 2159, 2161, 2174, 2179, 2183, 2185, 2186], [15, 744, 987, 1068, 1095, 1104, 1473, 1716, 1797, 1824, 1833, 1959, 2040, 2067, 2076, 2121, 2148, 2157, 2175, 2184], [16, 745, 988, 1069, 1083, 1096, 1101, 1105, 1474, 1717, 1798, 1812, 1825, 1830, 1834, 1960, 2041, 2055, 2068, 2073, 2077, 2122, 2136, 2149, 2154, 2158, 2163, 2176, 2181, 2185], [17, 746, 989, 1070, 1084, 1097, 1102, 1106, 1475, 1718, 1799, 1813, 1826, 1831, 1835, 1961, 2042, 2056, 2069, 2074, 2078, 2123, 2137, 2150, 2155, 2159, 2164, 2177, 2182, 2186], [18, 747, 990, 1071, 1098, 1476, 1719, 1800, 1827, 1962, 2043, 2070, 2124, 2151, 2178], [19, 748, 991, 1072, 1099, 1477, 1720, 1801, 1828, 1963, 2044, 2071, 2125, 2152, 2179], [20, 749, 992, 1073, 1100, 1478, 1721, 1802, 1829, 1964, 2045, 2072, 2126, 2153, 2180], [21, 750, 993, 1074, 1101, 1479, 1722, 1803, 1830, 1965, 2046, 2073, 2127, 2154, 2181], [22, 751, 994, 1075, 1089, 1102, 1480, 1723, 1804, 1818, 1831, 1966, 2047, 2061, 2074, 2128, 2142, 2155, 2169, 2182], [23, 752, 995, 1076, 1090, 1103, 1481, 1724, 1805, 1819, 1832, 1967, 2048, 2062, 2075, 2129, 2143, 2156, 2170, 2183], [24, 753, 996, 1077, 1104, 1482, 1725, 1806, 1833, 1968, 2049, 2076, 2130, 2157, 2184], [25, 754, 997, 1078, 1092, 1105, 1483, 1726, 1807, 1821, 1834, 1969, 2050, 2064, 2077, 2131, 2145, 2158, 2172, 2185], [26, 755, 998, 1079, 1093, 1106, 1484, 1727, 1808, 1822, 1835, 1970, 2051, 2065, 2078, 2132, 2146, 2159, 2160, 2173, 2186], [27, 756, 999, 1080, 1107, 1116, 1119, 1120, 1485, 1728, 1809, 1836, 1845, 1848, 1849, 1971, 2052, 2079, 2088, 2091, 2092, 2133, 2160, 2169, 2172, 2173], [28, 757, 1000, 1081, 1108, 1117, 1119, 1120, 1121, 1486, 1729, 1810, 1837, 1846, 1848, 1849, 1850, 1972, 2053, 2080, 2089, 2091, 2092, 2093, 2134, 2161, 2170, 2172, 2173, 2174], [29, 758, 1001, 1082, 1109, 1118, 1120, 1121, 1487, 1730, 1811, 1838, 1847, 1849, 1850, 1973, 2054, 2081, 2090, 2092, 2093, 2135, 2162, 2171, 2173, 2174], [30, 759, 1002, 1083, 1110, 1119, 1122, 1123, 1488, 1731, 1812, 1839, 1848, 1851, 1852, 1974, 2055, 2082, 2091, 2094, 2095, 2136, 2163, 2172, 2175, 2176], [31, 760, 1003, 1084, 1111, 1116, 1120, 1122, 1123, 1124, 1489, 1732, 1813, 1840, 1845, 1849, 1851, 1852, 1853, 1975, 2056, 2083, 2088, 2092, 2094, 2095, 2096, 2137, 2164, 2169, 2173, 2175, 2176, 2177], [32, 761, 1004, 1085, 1112, 1117, 1121, 1123, 1124, 1490, 1733, 1814, 1841, 1846, 1850, 1852, 1853, 1976, 2057, 2084, 2089, 2093, 2095, 2096, 2138, 2165, 2170, 2174, 2176, 2177], [33, 762, 1005, 1086, 1113, 1122, 1491, 1734, 1815, 1842, 1851, 1977, 2058, 2085, 2094, 2139, 2166, 2175], [34, 763, 1006, 1087, 1114, 1119, 1123, 1492, 1735, 1816, 1843, 1848, 1852, 1978, 2059, 2086, 2091, 2095, 2140, 2167, 2172, 2176], [35, 764, 1007, 1088, 1115, 1120, 1124, 1493, 1736, 1817, 1844, 1849, 1853, 1979, 2060, 2087, 2092, 2096, 2141, 2168, 2173, 2177], [36, 765, 1008, 1089, 1116, 1125, 1128, 1129, 1494, 1737, 1818, 1845, 1854, 1857, 1858, 1980, 2061, 2088, 2097, 2100, 2101, 2142, 2169, 2178, 2181, 2182], [37, 766, 1009, 1090, 1117, 1126, 1128, 1129, 1130, 1495, 1738, 1819, 1846, 1855, 1857, 1858, 1859, 1981, 2062, 2089, 2098, 2100, 2101, 2102, 2143, 2170, 2179, 2181, 2182, 2183], [38, 767, 1010, 1091, 1118, 1127, 1129, 1130, 1496, 1739, 1820, 1847, 1856, 1858, 1859, 1982, 2063, 2090, 2099, 2101, 2102, 2144, 2171, 2180, 2182, 2183], [39, 768, 1011, 1092, 1119, 1128, 1131, 1132, 1497, 1740, 1821, 1848, 1857, 1860, 1861, 1983, 2064, 2091, 2100, 2103, 2104, 2145, 2172, 2181, 2184, 2185], [40, 769, 1012, 1053, 1093, 1107, 1120, 1125, 1129, 1131, 1132, 1133, 1498, 1741, 1782, 1822, 1836, 1849, 1854, 1858, 1860, 1861, 1862, 1984, 2025, 2065, 2079, 2092, 2097, 2101, 2103, 2104, 2105, 2106, 2146, 2160, 2173, 2178, 2182, 2184, 2185, 2186], [41, 770, 1013, 1054, 1094, 1108, 1121, 1126, 1130, 1132, 1133, 1499, 1742, 1783, 1823, 1837, 1850, 1855, 1859, 1861, 1862, 1985, 2026, 2066, 2080, 2093, 2098, 2102, 2104, 2105, 2107, 2147, 2161, 2174, 2179, 2183, 2185, 2186], [42, 771, 1014, 1095, 1122, 1131, 1500, 1743, 1824, 1851, 1860, 1986, 2067, 2094, 2103, 2148, 2175, 2184], [43, 772, 1015, 1056, 1096, 1110, 1123, 1128, 1132, 1501, 1744, 1785, 1825, 1839, 1852, 1857, 1861, 1987, 2028, 2068, 2082, 2095, 2100, 2104, 2109, 2149, 2163, 2176, 2181, 2185], [44, 773, 1016, 1057, 1097, 1111, 1124, 1129, 1133, 1502, 1745, 1786, 1826, 1840, 1853, 1858, 1862, 1988, 2029, 2069, 2083, 2096, 2101, 2105, 2110, 2150, 2164, 2177, 2182, 2186], [45, 774, 1017, 1098, 1125, 1503, 1746, 1827, 1854, 1989, 2070, 2097, 2151, 2178], [46, 775, 1018, 1099, 1126, 1504, 1747, 1828, 1855, 1990, 2071, 2098, 2152, 2179], [47, 776, 1019, 1100, 1127, 1505, 1748, 1829, 1856, 1991, 2072, 2099, 2153, 2180], [48, 777, 1020, 1101, 1128, 1506, 1749, 1830, 1857, 1992, 2073, 2100, 2154, 2181], [49, 778, 1021, 1062, 1102, 1116, 1129, 1507, 1750, 1791, 1831, 1845, 1858, 1993, 2034, 2074, 2088, 2101, 2115, 2155, 2169, 2182], [50, 779, 1022, 1063, 1103, 1117, 1130, 1508, 1751, 1792, 1832, 1846, 1859, 1994, 2035, 2075, 2089, 2102, 2116, 2156, 2170, 2183], [51, 780, 1023, 1104, 1131, 1509, 1752, 1833, 1860, 1995, 2076, 2103, 2157, 2184], [52, 781, 1024, 1065, 1105, 1119, 1132, 1510, 1753, 1794, 1834, 1848, 1861, 1996, 2037, 2077, 2091, 2104, 2118, 2158, 2172, 2185], [53, 782, 1025, 1066, 1106, 1120, 1133, 1511, 1754, 1795, 1835, 1849, 1862, 1997, 2038, 2078, 2092, 2105, 2119, 2159, 2173, 2186], [54, 783, 1026, 1107, 1512, 1755, 1836, 1998, 2079, 2160], [55, 784, 1027, 1108, 1513, 1756, 1837, 1999, 2080, 2161], [56, 785, 1028, 1109, 1514, 1757, 1838, 2000, 2081, 2162], [57, 786, 1029, 1110, 1515, 1758, 1839, 2001, 2082, 2163], [58, 787, 1030, 1111, 1516, 1759, 1840, 2002, 2083, 2164], [59, 788, 1031, 1112, 1517, 1760, 1841, 2003, 2084, 2165], [60, 789, 1032, 1113, 1518, 1761, 1842, 2004, 2085, 2166], [61, 790, 1033, 1114, 1519, 1762, 1843, 2005, 2086, 2167], [62, 791, 1034, 1115, 1520, 1763, 1844, 2006, 2087, 2168], [63, 792, 1035, 1116, 1521, 1764, 1845, 2007, 2088, 2169], [64, 793, 1036, 1117, 1522, 1765, 1846, 2008, 2089, 2170], [65, 794, 1037, 1118, 1523, 1766, 1847, 2009, 2090, 2171], [66, 795, 1038, 1119, 1524, 1767, 1848, 2010, 2091, 2172], [67, 796, 1039, 1080, 1120, 1525, 1768, 1809, 1849, 2011, 2052, 2092, 2133, 2173], [68, 797, 1040, 1081, 1121, 1526, 1769, 1810, 1850, 2012, 2053, 2093, 2134, 2174], [69, 798, 1041, 1122, 1527, 1770, 1851, 2013, 2094, 2175], [70, 799, 1042, 1083, 1123, 1528, 1771, 1812, 1852, 2014, 2055, 2095, 2136, 2176], [71, 800, 1043, 1084, 1124, 1529, 1772, 1813, 1853, 2015, 2056, 2096, 2137, 2177], [72, 801, 1044, 1125, 1530, 1773, 1854, 2016, 2097, 2178], [73, 802, 1045, 1126, 1531, 1774, 1855, 2017, 2098, 2179], [74, 803, 1046, 1127, 1532, 1775, 1856, 2018, 2099, 2180], [75, 804, 1047, 1128, 1533, 1776, 1857, 2019, 2100, 2181], [76, 805, 1048, 1089, 1129, 1534, 1777, 1818, 1858, 2020, 2061, 2101, 2142, 2182], [77, 806, 1049, 1090, 1130, 1535, 1778, 1819, 1859, 2021, 2062, 2102, 2143, 2183], [78, 807, 1050, 1131, 1536, 1779, 1860, 2022, 2103, 2184], [79, 808, 1051, 1092, 1132, 1537, 1780, 1821, 1861, 2023, 2064, 2104, 2145, 2185], [80, 809, 1052, 1093, 1133, 1538, 1781, 1822, 1862, 2024, 2065, 2105, 2106, 2146, 2186], [81, 810, 1053, 1134, 1161, 1170, 1173, 1174, 1539, 1782, 1863, 1890, 1899, 1902, 1903, 2025, 2106, 2133, 2142, 2145, 2146], [82, 811, 1054, 1135, 1162, 1171, 1173, 1174, 1175, 1540, 1783, 1864, 1891, 1900, 1902, 1903, 1904, 2026, 2107, 2134, 2143, 2145, 2146, 2147], [83, 812, 1055, 1136, 1163, 1172, 1174, 1175, 1541, 1784, 1865, 1892, 1901, 1903, 1904, 2027, 2108, 2135, 2144, 2146, 2147], [84, 813, 1056, 1137, 1164, 1173, 1176, 1177, 1542, 1785, 1866, 1893, 1902, 1905, 1906, 2028, 2109, 2136, 2145, 2148, 2149], [85, 814, 1057, 1138, 1165, 1170, 1174, 1176, 1177, 1178, 1543, 1786, 1867, 1894, 1899, 1903, 1905, 1906, 1907, 2029, 2110, 2137, 2142, 2146, 2148, 2149, 2150], [86, 815, 1058, 1139, 1166, 1171, 1175, 1177, 1178, 1544, 1787, 1868, 1895, 1900, 1904, 1906, 1907, 2030, 2111, 2138, 2143, 2147, 2149, 2150], [87, 816, 1059, 1140, 1167, 1176, 1545, 1788, 1869, 1896, 1905, 2031, 2112, 2139, 2148], [88, 817, 1060, 1141, 1168, 1173, 1177, 1546, 1789, 1870, 1897, 1902, 1906, 2032, 2113, 2140, 2145, 2149], [89, 818, 1061, 1142, 1169, 1174, 1178, 1547, 1790, 1871, 1898, 1903, 1907, 2033, 2114, 2141, 2146, 2150], [90, 819, 1062, 1143, 1170, 1179, 1182, 1183, 1548, 1791, 1872, 1899, 1908, 1911, 1912, 2034, 2115, 2142, 2151, 2154, 2155], [91, 820, 1063, 1144, 1171, 1180, 1182, 1183, 1184, 1549, 1792, 1873, 1900, 1909, 1911, 1912, 1913, 2035, 2116, 2143, 2152, 2154, 2155, 2156], [92, 821, 1064, 1145, 1172, 1181, 1183, 1184, 1550, 1793, 1874, 1901, 1910, 1912, 1913, 2036, 2117, 2144, 2153, 2155, 2156], [93, 822, 1065, 1146, 1173, 1182, 1185, 1186, 1551, 1794, 1875, 1902, 1911, 1914, 1915, 2037, 2118, 2145, 2154, 2157, 2158], [94, 823, 1066, 1147, 1161, 1174, 1179, 1183, 1185, 1186, 1187, 1552, 1795, 1876, 1890, 1903, 1908, 1912, 1914, 1915, 1916, 2038, 2119, 2133, 2146, 2151, 2155, 2157, 2158, 2159], [95, 824, 1067, 1148, 1162, 1175, 1180, 1184, 1186, 1187, 1553, 1796, 1877, 1891, 1904, 1909, 1913, 1915, 1916, 2039, 2120, 2134, 2147, 2152, 2156, 2158, 2159], [96, 825, 1068, 1149, 1176, 1185, 1554, 1797, 1878, 1905, 1914, 2040, 2121, 2148, 2157], [97, 826, 1069, 1150, 1164, 1177, 1182, 1186, 1555, 1798, 1879, 1893, 1906, 1911, 1915, 2041, 2122, 2136, 2149, 2154, 2158], [98, 827, 1070, 1151, 1165, 1178, 1183, 1187, 1556, 1799, 1880, 1894, 1907, 1912, 1916, 2042, 2123, 2137, 2150, 2155, 2159], [99, 828, 1071, 1152, 1179, 1557, 1800, 1881, 1908, 2043, 2124, 2151], [100, 829, 1072, 1153, 1180, 1558, 1801, 1882, 1909, 2044, 2125, 2152], [101, 830, 1073, 1154, 1181, 1559, 1802, 1883, 1910, 2045, 2126, 2153], [102, 831, 1074, 1155, 1182, 1560, 1803, 1884, 1911, 2046, 2127, 2154], [103, 832, 1075, 1156, 1170, 1183, 1561, 1804, 1885, 1899, 1912, 2047, 2128, 2142, 2155], [104, 833, 1076, 1157, 1171, 1184, 1562, 1805, 1886, 1900, 1913, 2048, 2129, 2143, 2156], [105, 834, 1077, 1158, 1185, 1563, 1806, 1887, 1914, 2049, 2130, 2157], [106, 835, 1078, 1159, 1173, 1186, 1564, 1807, 1888, 1902, 1915, 2050, 2131, 2145, 2158], [107, 836, 1079, 1160, 1174, 1187, 1565, 1808, 1889, 1903, 1916, 2051, 2132, 2146, 2159], [108, 837, 1080, 1161, 1188, 1197, 1200, 1201, 1566, 1809, 1890, 1917, 1926, 1929, 1930, 2052, 2133, 2160, 2169, 2172, 2173], [109, 838, 1081, 1162, 1189, 1198, 1200, 1201, 1202, 1567, 1810, 1891, 1918, 1927, 1929, 1930, 1931, 2053, 2134, 2161, 2170, 2172, 2173, 2174], [110, 839, 1082, 1163, 1190, 1199, 1201, 1202, 1568, 1811, 1892, 1919, 1928, 1930, 1931, 2054, 2135, 2162, 2171, 2173, 2174], [111, 840, 1083, 1164, 1191, 1200, 1203, 1204, 1569, 1812, 1893, 1920, 1929, 1932, 1933, 2055, 2136, 2163, 2172, 2175, 2176], [112, 841, 1084, 1165, 1192, 1197, 1201, 1203, 1204, 1205, 1570, 1813, 1894, 1921, 1926, 1930, 1932, 1933, 1934, 2056, 2137, 2164, 2169, 2173, 2175, 2176, 2177], [113, 842, 1085, 1166, 1193, 1198, 1202, 1204, 1205, 1571, 1814, 1895, 1922, 1927, 1931, 1933, 1934, 2057, 2138, 2165, 2170, 2174, 2176, 2177], [114, 843, 1086, 1167, 1194, 1203, 1572, 1815, 1896, 1923, 1932, 2058, 2139, 2166, 2175], [115, 844, 1087, 1168, 1195, 1200, 1204, 1573, 1816, 1897, 1924, 1929, 1933, 2059, 2140, 2167, 2172, 2176], [116, 845, 1088, 1169, 1196, 1201, 1205, 1574, 1817, 1898, 1925, 1930, 1934, 2060, 2141, 2168, 2173, 2177], [117, 846, 1089, 1170, 1197, 1206, 1209, 1210, 1575, 1818, 1899, 1926, 1935, 1938, 1939, 2061, 2142, 2169, 2178, 2181, 2182], [118, 847, 1090, 1171, 1198, 1207, 1209, 1210, 1211, 1576, 1819, 1900, 1927, 1936, 1938, 1939, 1940, 2062, 2143, 2170, 2179, 2181, 2182, 2183], [119, 848, 1091, 1172, 1199, 1208, 1210, 1211, 1577, 1820, 1901, 1928, 1937, 1939, 1940, 2063, 2144, 2171, 2180, 2182, 2183], [120, 849, 1092, 1173, 1200, 1209, 1212, 1213, 1578, 1821, 1902, 1929, 1938, 1941, 1942, 2064, 2145, 2172, 2181, 2184, 2185], [121, 850, 972, 1093, 1134, 1174, 1188, 1201, 1206, 1210, 1212, 1213, 1214, 1579, 1701, 1822, 1863, 1903, 1917, 1930, 1935, 1939, 1941, 1942, 1943, 1944, 2065, 2106, 2146, 2160, 2173, 2178, 2182, 2184, 2185, 2186], [122, 851, 973, 1094, 1135, 1175, 1189, 1202, 1207, 1211, 1213, 1214, 1580, 1702, 1823, 1864, 1904, 1918, 1931, 1936, 1940, 1942, 1943, 1945, 2066, 2107, 2147, 2161, 2174, 2179, 2183, 2185, 2186], [123, 852, 1095, 1176, 1203, 1212, 1581, 1824, 1905, 1932, 1941, 2067, 2148, 2175, 2184], [124, 853, 975, 1096, 1137, 1177, 1191, 1204, 1209, 1213, 1582, 1704, 1825, 1866, 1906, 1920, 1933, 1938, 1942, 1947, 2068, 2109, 2149, 2163, 2176, 2181, 2185], [125, 854, 976, 1097, 1138, 1178, 1192, 1205, 1210, 1214, 1583, 1705, 1826, 1867, 1907, 1921, 1934, 1939, 1943, 1948, 2069, 2110, 2150, 2164, 2177, 2182, 2186], [126, 855, 1098, 1179, 1206, 1584, 1827, 1908, 1935, 2070, 2151, 2178], [127, 856, 1099, 1180, 1207, 1585, 1828, 1909, 1936, 2071, 2152, 2179], [128, 857, 1100, 1181, 1208, 1586, 1829, 1910, 1937, 2072, 2153, 2180], [129, 858, 1101, 1182, 1209, 1587, 1830, 1911, 1938, 2073, 2154, 2181], [130, 859, 981, 1102, 1143, 1183, 1197, 1210, 1588, 1710, 1831, 1872, 1912, 1926, 1939, 1953, 2074, 2115, 2155, 2169, 2182], [131, 860, 982, 1103, 1144, 1184, 1198, 1211, 1589, 1711, 1832, 1873, 1913, 1927, 1940, 1954, 2075, 2116, 2156, 2170, 2183], [132, 861, 1104, 1185, 1212, 1590, 1833, 1914, 1941, 2076, 2157, 2184], [133, 862, 984, 1105, 1146, 1186, 1200, 1213, 1591, 1713, 1834, 1875, 1915, 1929, 1942, 1956, 2077, 2118, 2158, 2172, 2185], [134, 863, 985, 1106, 1147, 1187, 1201, 1214, 1592, 1714, 1835, 1876, 1916, 1930, 1943, 1957, 2078, 2119, 2159, 2173, 2186], [135, 864, 1107, 1188, 1593, 1836, 1917, 2079, 2160], [136, 865, 1108, 1189, 1594, 1837, 1918, 2080, 2161], [137, 866, 1109, 1190, 1595, 1838, 1919, 2081, 2162], [138, 867, 1110, 1191, 1596, 1839, 1920, 2082, 2163], [139, 868, 1111, 1192, 1597, 1840, 1921, 2083, 2164], [140, 869, 1112, 1193, 1598, 1841, 1922, 2084, 2165], [141, 870, 1113, 1194, 1599, 1842, 1923, 2085, 2166], [142, 871, 1114, 1195, 1600, 1843, 1924, 2086, 2167], [143, 872, 1115, 1196, 1601, 1844, 1925, 2087, 2168], [144, 873, 1116, 1197, 1602, 1845, 1926, 2088, 2169], [145, 874, 1117, 1198, 1603, 1846, 1927, 2089, 2170], [146, 875, 1118, 1199, 1604, 1847, 1928, 2090, 2171], [147, 876, 1119, 1200, 1605, 1848, 1929, 2091, 2172], [148, 877, 999, 1120, 1161, 1201, 1606, 1728, 1849, 1890, 1930, 1971, 2092, 2133, 2173], [149, 878, 1000, 1121, 1162, 1202, 1607, 1729, 1850, 1891, 1931, 1972, 2093, 2134, 2174], [150, 879, 1122, 1203, 1608, 1851, 1932, 2094, 2175], [151, 880, 1002, 1123, 1164, 1204, 1609, 1731, 1852, 1893, 1933, 1974, 2095, 2136, 2176], [152, 881, 1003, 1124, 1165, 1205, 1610, 1732, 1853, 1894, 1934, 1975, 2096, 2137, 2177], [153, 882, 1125, 1206, 1611, 1854, 1935, 2097, 2178], [154, 883, 1126, 1207, 1612, 1855, 1936, 2098, 2179], [155, 884, 1127, 1208, 1613, 1856, 1937, 2099, 2180], [156, 885, 1128, 1209, 1614, 1857, 1938, 2100, 2181], [157, 886, 1008, 1129, 1170, 1210, 1615, 1737, 1858, 1899, 1939, 1980, 2101, 2142, 2182], [158, 887, 1009, 1130, 1171, 1211, 1616, 1738, 1859, 1900, 1940, 1981, 2102, 2143, 2183], [159, 888, 1131, 1212, 1617, 1860, 1941, 2103, 2184], [160, 889, 1011, 1132, 1173, 1213, 1618, 1740, 1861, 1902, 1942, 1983, 2104, 2145, 2185], [161, 890, 1012, 1133, 1174, 1214, 1619, 1741, 1862, 1903, 1943, 1984, 2105, 2146, 2186], [162, 891, 1134, 1620, 1863, 2106], [163, 892, 1135, 1621, 1864, 2107], [164, 893, 1136, 1622, 1865, 2108], [165, 894, 1137, 1623, 1866, 2109], [166, 895, 1138, 1624, 1867, 2110], [167, 896, 1139, 1625, 1868, 2111], [168, 897, 1140, 1626, 1869, 2112], [169, 898, 1141, 1627, 1870, 2113], [170, 899, 1142, 1628, 1871, 2114], [171, 900, 1143, 1629, 1872, 2115], [172, 901, 1144, 1630, 1873, 2116], [173, 902, 1145, 1631, 1874, 2117], [174, 903, 1146, 1632, 1875, 2118], [175, 904, 1147, 1633, 1876, 2119], [176, 905, 1148, 1634, 1877, 2120], [177, 906, 1149, 1635, 1878, 2121], [178, 907, 1150, 1636, 1879, 2122], [179, 908, 1151, 1637, 1880, 2123], [180, 909, 1152, 1638, 1881, 2124], [181, 910, 1153, 1639, 1882, 2125], [182, 911, 1154, 1640, 1883, 2126], [183, 912, 1155, 1641, 1884, 2127], [184, 913, 1156, 1642, 1885, 2128], [185, 914, 1157, 1643, 1886, 2129], [186, 915, 1158, 1644, 1887, 2130], [187, 916, 1159, 1645, 1888, 2131], [188, 917, 1160, 1646, 1889, 2132], [189, 918, 1161, 1647, 1890, 2133], [190, 919, 1162, 1648, 1891, 2134], [191, 920, 1163, 1649, 1892, 2135], [192, 921, 1164, 1650, 1893, 2136], [193, 922, 1165, 1651, 1894, 2137], [194, 923, 1166, 1652, 1895, 2138], [195, 924, 1167, 1653, 1896, 2139], [196, 925, 1168, 1654, 1897, 2140], [197, 926, 1169, 1655, 1898, 2141], [198, 927, 1170, 1656, 1899, 2142], [199, 928, 1171, 1657, 1900, 2143], [200, 929, 1172, 1658, 1901, 2144], [201, 930, 1173, 1659, 1902, 2145], [202, 931, 1053, 1174, 1660, 1782, 1903, 2025, 2146], [203, 932, 1054, 1175, 1661, 1783, 1904, 2026, 2147], [204, 933, 1176, 1662, 1905, 2148], [205, 934, 1056, 1177, 1663, 1785, 1906, 2028, 2149], [206, 935, 1057, 1178, 1664, 1786, 1907, 2029, 2150], [207, 936, 1179, 1665, 1908, 2151], [208, 937, 1180, 1666, 1909, 2152], [209, 938, 1181, 1667, 1910, 2153], [210, 939, 1182, 1668, 1911, 2154], [211, 940, 1062, 1183, 1669, 1791, 1912, 2034, 2155], [212, 941, 1063, 1184, 1670, 1792, 1913, 2035, 2156], [213, 942, 1185, 1671, 1914, 2157], [214, 943, 1065, 1186, 1672, 1794, 1915, 2037, 2158], [215, 944, 1066, 1187, 1673, 1795, 1916, 2038, 2159], [216, 945, 1188, 1674, 1917, 2160], [217, 946, 1189, 1675, 1918, 2161], [218, 947, 1190, 1676, 1919, 2162], [219, 948, 1191, 1677, 1920, 2163], [220, 949, 1192, 1678, 1921, 2164], [221, 950, 1193, 1679, 1922, 2165], [222, 951, 1194, 1680, 1923, 2166], [223, 952, 1195, 1681, 1924, 2167], [224, 953, 1196, 1682, 1925, 2168], [225, 954, 1197, 1683, 1926, 2169], [226, 955, 1198, 1684, 1927, 2170], [227, 956, 1199, 1685, 1928, 2171], [228, 957, 1200, 1686, 1929, 2172], [229, 958, 1080, 1201, 1687, 1809, 1930, 2052, 2173], [230, 959, 1081, 1202, 1688, 1810, 1931, 2053, 2174], [231, 960, 1203, 1689, 1932, 2175], [232, 961, 1083, 1204, 1690, 1812, 1933, 2055, 2176], [233, 962, 1084, 1205, 1691, 1813, 1934, 2056, 2177], [234, 963, 1206, 1692, 1935, 2178], [235, 964, 1207, 1693, 1936, 2179], [236, 965, 1208, 1694, 1937, 2180], [237, 966, 1209, 1695, 1938, 2181], [238, 967, 1089, 1210, 1696, 1818, 1939, 2061, 2182], [239, 968, 1090, 1211, 1697, 1819, 1940, 2062, 2183], [240, 969, 1212, 1698, 1941, 2184], [241, 970, 1092, 1213, 1699, 1821, 1942, 2064, 2185], [242, 971, 1093, 1214, 1700, 1822, 1943, 1944, 2065, 2186]], [[243, 972, 1215, 1296, 1323, 1332, 1335, 1336, 1701, 1944, 2025, 2052, 2061, 2064, 2065], [244, 973, 1216, 1297, 1324, 1333, 1335, 1336, 1337, 1702, 1945, 2026, 2053, 2062, 2064, 2065, 2066], [245, 974, 1217, 1298, 1325, 1334, 1336, 1337, 1703, 1946, 2027, 2054, 2063, 2065, 2066], [246, 975, 1218, 1299, 1326, 1335, 1338, 1339, 1704, 1947, 2028, 2055, 2064, 2067, 2068], [247, 976, 1219, 1300, 1327, 1332, 1336, 1338, 1339, 1340, 1705, 1948, 2029, 2056, 2061, 2065, 2067, 2068, 2069], [248, 977, 1220, 1301, 1328, 1333, 1337, 1339, 1340, 1706, 1949, 2030, 2057, 2062, 2066, 2068, 2069], [249, 978, 1221, 1302, 1329, 1338, 1707, 1950, 2031, 2058, 2067], [250, 979, 1222, 1303, 1330, 1335, 1339, 1708, 1951, 2032, 2059, 2064, 2068], [251, 980, 1223, 1304, 1331, 1336, 1340, 1709, 1952, 2033, 2060, 2065, 2069], [252, 981, 1224, 1305, 1332, 1341, 1344, 1345, 1710, 1953, 2034, 2061, 2070, 2073, 2074], [253, 982, 1225, 1306, 1333, 1342, 1344, 1345, 1346, 1711, 1954, 2035, 2062, 2071, 2073, 2074, 2075], [254, 983, 1226, 1307, 1334, 1343, 1345, 1346, 1712, 1955, 2036, 2063, 2072, 2074, 2075], [255, 984, 1227, 1308, 1335, 1344, 1347, 1348, 1713, 1956, 2037, 2064, 2073, 2076, 2077], [256, 985, 1228, 1309, 1323, 1336, 1341, 1345, 1347, 1348, 1349, 1714, 1957, 2038, 2052, 2065, 2070, 2074, 2076, 2077, 2078], [257, 986, 1229, 1310, 1324, 1337, 1342, 1346, 1348, 1349, 1715, 1958, 2039, 2053, 2066, 2071, 2075, 2077, 2078], [258, 987, 1230, 1311, 1338, 1347, 1716, 1959, 2040, 2067, 2076], [259, 988, 1231, 1312, 1326, 1339, 1344, 1348, 1717, 1960, 2041, 2055, 2068, 2073, 2077], [260, 989, 1232, 1313, 1327, 1340, 1345, 1349, 1718, 1961, 2042, 2056, 2069, 2074, 2078], [261, 990, 1233, 1314, 1341, 1719, 1962, 2043, 2070], [262, 991, 1234, 1315, 1342, 1720, 1963, 2044, 2071], [263, 992, 1235, 1316, 1343, 1721, 1964, 2045, 2072], [264, 993, 1236, 1317, 1344, 1722, 1965, 2046, 2073], [265, 994, 1237, 1318, 1332, 1345, 1723, 1966, 2047, 2061, 2074], [266, 995, 1238, 1319, 1333, 1346, 1724, 1967, 2048, 2062, 2075], [267, 996, 1239, 1320, 1347, 1725, 1968, 2049, 2076], [268, 997, 1240, 1321, 1335, 1348, 1726, 1969, 2050, 2064, 2077], [269, 998, 1241, 1322, 1336, 1349, 1727, 1970, 2051, 2065, 2078], [270, 999, 1242, 1323, 1350, 1359, 1362, 1363, 1728, 1971, 2052, 2079, 2088, 2091, 2092], [271, 1000, 1243, 1324, 1351, 1360, 1362, 1363, 1364, 1729, 1972, 2053, 2080, 2089, 2091, 2092, 2093], [272, 1001, 1244, 1325, 1352, 1361, 1363, 1364, 1730, 1973, 2054, 2081, 2090, 2092, 2093], [273, 1002, 1245, 1326, 1353, 1362, 1365, 1366, 1731, 1974, 2055, 2082, 2091, 2094, 2095], [274, 1003, 1246, 1327, 1354, 1359, 1363, 1365, 1366, 1367, 1732, 1975, 2056, 2083, 2088, 2092, 2094, 2095, 2096], [275, 1004, 1247, 1328, 1355, 1360, 1364, 1366, 1367, 1733, 1976, 2057, 2084, 2089, 2093, 2095, 2096], [276, 1005, 1248, 1329, 1356, 1365, 1734, 1977, 2058, 2085, 2094], [277, 1006, 1249, 1330, 1357, 1362, 1366, 1735, 1978, 2059, 2086, 2091, 2095], [278, 1007, 1250, 1331, 1358, 1363, 1367, 1736, 1979, 2060, 2087, 2092, 2096], [279, 1008, 1251, 1332, 1359, 1368, 1371, 1372, 1737, 1980, 2061, 2088, 2097, 2100, 2101], [280, 1009, 1252, 1333, 1360, 1369, 1371, 1372, 1373, 1738, 1981, 2062, 2089, 2098, 2100, 2101, 2102], [281, 1010, 1253, 1334, 1361, 1370, 1372, 1373, 1739, 1982, 2063, 2090, 2099, 2101, 2102], [282, 1011, 1254, 1335, 1362, 1371, 1374, 1375, 1740, 1983, 2064, 2091, 2100, 2103, 2104], [283, 1012, 1255, 1296, 1336, 1350, 1363, 1368, 1372, 1374, 1375, 1376, 1741, 1984, 2025, 2065, 2079, 2092, 2097, 2101, 2103, 2104, 2105], [284, 1013, 1256, 1297, 1337, 1351, 1364, 1369, 1373, 1375, 1376, 1742, 1985, 2026, 2066, 2080, 2093, 2098, 2102, 2104, 2105], [285, 1014, 1257, 1338, 1365, 1374, 1743, 1986, 2067, 2094, 2103], [286, 1015, 1258, 1299, 1339, 1353, 1366, 1371, 1375, 1744, 1987, 2028, 2068, 2082, 2095, 2100, 2104], [287, 1016, 1259, 1300, 1340, 1354, 1367, 1372, 1376, 1745, 1988, 2029, 2069, 2083, 2096, 2101, 2105], [288, 1017, 1260, 1341, 1368, 1746, 1989, 2070, 2097], [289, 1018, 1261, 1342, 1369, 1747, 1990, 2071, 2098], [290, 1019, 1262, 1343, 1370, 1748, 1991, 2072, 2099], [291, 1020, 1263, 1344, 1371, 1749, 1992, 2073, 2100], [292, 1021, 1264, 1305, 1345, 1359, 1372, 1750, 1993, 2034, 2074, 2088, 2101], [293, 1022, 1265, 1306, 1346, 1360, 1373, 1751, 1994, 2035, 2075, 2089, 2102], [294, 1023, 1266, 1347, 1374, 1752, 1995, 2076, 2103], [295, 1024, 1267, 1308, 1348, 1362, 1375, 1753, 1996, 2037, 2077, 2091, 2104], [296, 1025, 1268, 1309, 1349, 1363, 1376, 1754, 1997, 2038, 2078, 2092, 2105], [297, 1026, 1269, 1350, 1755, 1998, 2079], [298, 1027, 1270, 1351, 1756, 1999, 2080], [299, 1028, 1271, 1352, 1757, 2000, 2081], [300, 1029, 1272, 1353, 1758, 2001, 2082], [301, 1030, 1273, 1354, 1759, 2002, 2083], [302, 1031, 1274, 1355, 1760, 2003, 2084], [303, 1032, 1275, 1356, 1761, 2004, 2085], [304, 1033, 1276, 1357, 1762, 2005, 2086], [305, 1034, 1277, 1358, 1763, 2006, 2087], [306, 1035, 1278, 1359, 1764, 2007, 2088], [307, 1036, 1279, 1360, 1765, 2008, 2089], [308, 1037, 1280, 1361, 1766, 2009, 2090], [309, 1038, 1281, 1362, 1767, 2010, 2091], [310, 1039, 1282, 1323, 1363, 1768, 2011, 2052, 2092], [311, 1040, 1283, 1324, 1364, 1769, 2012, 2053, 2093], [312, 1041, 1284, 1365, 1770, 2013, 2094], [313, 1042, 1285, 1326, 1366, 1771, 2014, 2055, 2095], [314, 1043, 1286, 1327, 1367, 1772, 2015, 2056, 2096], [315, 1044, 1287, 1368, 1773, 2016, 2097], [316, 1045, 1288, 1369, 1774, 2017, 2098], [317, 1046, 1289, 1370, 1775, 2018, 2099], [318, 1047, 1290, 1371, 1776, 2019, 2100], [319, 1048, 1291, 1332, 1372, 1777, 2020, 2061, 2101], [320, 1049, 1292, 1333, 1373, 1778, 2021, 2062, 2102], [321, 1050, 1293, 1374, 1779, 2022, 2103], [322, 1051, 1294, 1335, 1375, 1780, 2023, 2064, 2104], [323, 1052, 1295, 1336, 1376, 1781, 2024, 2065, 2105], [324, 1053, 1296, 1377, 1404, 1413, 1416, 1417, 1782, 2025, 2106, 2133, 2142, 2145, 2146], [325, 1054, 1297, 1378, 1405, 1414, 1416, 1417, 1418, 1783, 2026, 2107, 2134, 2143, 2145, 2146, 2147], [326, 1055, 1298, 1379, 1406, 1415, 1417, 1418, 1784, 2027, 2108, 2135, 2144, 2146, 2147], [327, 1056, 1299, 1380, 1407, 1416, 1419, 1420, 1785, 2028, 2109, 2136, 2145, 2148, 2149], [328, 1057, 1300, 1381, 1408, 1413, 1417, 1419, 1420, 1421, 1786, 2029, 2110, 2137, 2142, 2146, 2148, 2149, 2150], [329, 1058, 1301, 1382, 1409, 1414, 1418, 1420, 1421, 1787, 2030, 2111, 2138, 2143, 2147, 2149, 2150], [330, 1059, 1302, 1383, 1410, 1419, 1788, 2031, 2112, 2139, 2148], [331, 1060, 1303, 1384, 1411, 1416, 1420, 1789, 2032, 2113, 2140, 2145, 2149], [332, 1061, 1304, 1385, 1412, 1417, 1421, 1790, 2033, 2114, 2141, 2146, 2150], [333, 1062, 1305, 1386, 1413, 1422, 1425, 1426, 1791, 2034, 2115, 2142, 2151, 2154, 2155], [334, 1063, 1306, 1387, 1414, 1423, 1425, 1426, 1427, 1792, 2035, 2116, 2143, 2152, 2154, 2155, 2156], [335, 1064, 1307, 1388, 1415, 1424, 1426, 1427, 1793, 2036, 2117, 2144, 2153, 2155, 2156], [336, 1065, 1308, 1389, 1416, 1425, 1428, 1429, 1794, 2037, 2118, 2145, 2154, 2157, 2158], [337, 1066, 1309, 1390, 1404, 1417, 1422, 1426, 1428, 1429, 1430, 1795, 2038, 2119, 2133, 2146, 2151, 2155, 2157, 2158, 2159], [338, 1067, 1310, 1391, 1405, 1418, 1423, 1427, 1429, 1430, 1796, 2039, 2120, 2134, 2147, 2152, 2156, 2158, 2159], [339, 1068, 1311, 1392, 1419, 1428, 1797, 2040, 2121, 2148, 2157], [340, 1069, 1312, 1393, 1407, 1420, 1425, 1429, 1798, 2041, 2122, 2136, 2149, 2154, 2158], [341, 1070, 1313, 1394, 1408, 1421, 1426, 1430, 1799, 2042, 2123, 2137, 2150, 2155, 2159], [342, 1071, 1314, 1395, 1422, 1800, 2043, 2124, 2151], [343, 1072, 1315, 1396, 1423, 1801, 2044, 2125, 2152], [344, 1073, 1316, 1397, 1424, 1802, 2045, 2126, 2153], [345, 1074, 1317, 1398, 1425, 1803, 2046, 2127, 2154], [346, 1075, 1318, 1399, 1413, 1426, 1804, 2047, 2128, 2142, 2155], [347, 1076, 1319, 1400, 1414, 1427, 1805, 2048, 2129, 2143, 2156], [348, 1077, 1320, 1401, 1428, 1806, 2049, 2130, 2157], [349, 1078, 1321, 1402, 1416, 1429, 1807, 2050, 2131, 2145, 2158], [350, 1079, 1322, 1403, 1417, 1430, 1808, 2051, 2132, 2146, 2159], [351, 1080, 1323, 1404, 1431, 1440, 1443, 1444, 1809, 2052, 2133, 2160, 2169, 2172, 2173], [352, 1081, 1324, 1405, 1432, 1441, 1443, 1444, 1445, 1810, 2053, 2134, 2161, 2170, 2172, 2173, 2174], [353, 1082, 1325, 1406, 1433, 1442, 1444, 1445, 1811, 2054, 2135, 2162, 2171, 2173, 2174], [354, 1083, 1326, 1407, 1434, 1443, 1446, 1447, 1812, 2055, 2136, 2163, 2172, 2175, 2176], [355, 1084, 1327, 1408, 1435, 1440, 1444, 1446, 1447, 1448, 1813, 2056, 2137, 2164, 2169, 2173, 2175, 2176, 2177], [356, 1085, 1328, 1409, 1436, 1441, 1445, 1447, 1448, 1814, 2057, 2138, 2165, 2170, 2174, 2176, 2177], [357, 1086, 1329, 1410, 1437, 1446, 1815, 2058, 2139, 2166, 2175], [358, 1087, 1330, 1411, 1438, 1443, 1447, 1816, 2059, 2140, 2167, 2172, 2176], [359, 1088, 1331, 1412, 1439, 1444, 1448, 1817, 2060, 2141, 2168, 2173, 2177], [360, 1089, 1332, 1413, 1440, 1449, 1452, 1453, 1818, 2061, 2142, 2169, 2178, 2181, 2182], [361, 1090, 1333, 1414, 1441, 1450, 1452, 1453, 1454, 1819, 2062, 2143, 2170, 2179, 2181, 2182, 2183], [362, 1091, 1334, 1415, 1442, 1451, 1453, 1454, 1820, 2063, 2144, 2171, 2180, 2182, 2183], [363, 1092, 1335, 1416, 1443, 1452, 1455, 1456, 1821, 2064, 2145, 2172, 2181, 2184, 2185], [364, 729, 1093, 1215, 1336, 1377, 1417, 1431, 1444, 1449, 1453, 1455, 1456, 1457, 1458, 1822, 1944, 2065, 2106, 2146, 2160, 2173, 2178, 2182, 2184, 2185, 2186], [365, 730, 1094, 1216, 1337, 1378, 1418, 1432, 1445, 1450, 1454, 1456, 1457, 1459, 1823, 1945, 2066, 2107, 2147, 2161, 2174, 2179, 2183, 2185, 2186], [366, 1095, 1338, 1419, 1446, 1455, 1824, 2067, 2148, 2175, 2184], [367, 732, 1096, 1218, 1339, 1380, 1420, 1434, 1447, 1452, 1456, 1461, 1825, 1947, 2068, 2109, 2149, 2163, 2176, 2181, 2185], [368, 733, 1097, 1219, 1340, 1381, 1421, 1435, 1448, 1453, 1457, 1462, 1826, 1948, 2069, 2110, 2150, 2164, 2177, 2182, 2186], [369, 1098, 1341, 1422, 1449, 1827, 2070, 2151, 2178], [370, 1099, 1342, 1423, 1450, 1828, 2071, 2152, 2179], [371, 1100, 1343, 1424, 1451, 1829, 2072, 2153, 2180], [372, 1101, 1344, 1425, 1452, 1830, 2073, 2154, 2181], [373, 738, 1102, 1224, 1345, 1386, 1426, 1440, 1453, 1467, 1831, 1953, 2074, 2115, 2155, 2169, 2182], [374, 739, 1103, 1225, 1346, 1387, 1427, 1441, 1454, 1468, 1832, 1954, 2075, 2116, 2156, 2170, 2183], [375, 1104, 1347, 1428, 1455, 1833, 2076, 2157, 2184], [376, 741, 1105, 1227, 1348, 1389, 1429, 1443, 1456, 1470, 1834, 1956, 2077, 2118, 2158, 2172, 2185], [377, 742, 1106, 1228, 1349, 1390, 1430, 1444, 1457, 1471, 1835, 1957, 2078, 2119, 2159, 2173, 2186], [378, 1107, 1350, 1431, 1836, 2079, 2160], [379, 1108, 1351, 1432, 1837, 2080, 2161], [380, 1109, 1352, 1433, 1838, 2081, 2162], [381, 1110, 1353, 1434, 1839, 2082, 2163], [382, 1111, 1354, 1435, 1840, 2083, 2164], [383, 1112, 1355, 1436, 1841, 2084, 2165], [384, 1113, 1356, 1437, 1842, 2085, 2166], [385, 1114, 1357, 1438, 1843, 2086, 2167], [386, 1115, 1358, 1439, 1844, 2087, 2168], [387, 1116, 1359, 1440, 1845, 2088, 2169], [388, 1117, 1360, 1441, 1846, 2089, 2170], [389, 1118, 1361, 1442, 1847, 2090, 2171], [390, 1119, 1362, 1443, 1848, 2091, 2172], [391, 756, 1120, 1242, 1363, 1404, 1444, 1485, 1849, 1971, 2092, 2133, 2173], [392, 757, 1121, 1243, 1364, 1405, 1445, 1486, 1850, 1972, 2093, 2134, 2174], [393, 1122, 1365, 1446, 1851, 2094, 2175], [394, 759, 1123, 1245, 1366, 1407, 1447, 1488, 1852, 1974, 2095, 2136, 2176], [395, 760, 1124, 1246, 1367, 1408, 1448, 1489, 1853, 1975, 2096, 2137, 2177], [396, 1125, 1368, 1449, 1854, 2097, 2178], [397, 1126, 1369, 1450, 1855, 2098, 2179], [398, 1127, 1370, 1451, 1856, 2099, 2180], [399, 1128, 1371, 1452, 1857, 2100, 2181], [400, 765, 1129, 1251, 1372, 1413, 1453, 1494, 1858, 1980, 2101, 2142, 2182], [401, 766, 1130, 1252, 1373, 1414, 1454, 1495, 1859, 1981, 2102, 2143, 2183], [402, 1131, 1374, 1455, 1860, 2103, 2184], [403, 768, 1132, 1254, 1375, 1416, 1456, 1497, 1861, 1983, 2104, 2145, 2185], [404, 769, 1133, 1255, 1376, 1417, 1457, 1498, 1862, 1984, 2105, 2146, 2186], [405, 1134, 1377, 1863, 2106], [406, 1135, 1378, 1864, 2107], [407, 1136, 1379, 1865, 2108], [408, 1137, 1380, 1866, 2109], [409, 1138, 1381, 1867, 2110], [410, 1139, 1382, 1868, 2111], [411, 1140, 1383, 1869, 2112], [412, 1141, 1384, 1870, 2113], [413, 1142, 1385, 1871, 2114], [414, 1143, 1386, 1872, 2115], [415, 1144, 1387, 1873, 2116], [416, 1145, 1388, 1874, 2117], [417, 1146, 1389, 1875, 2118], [418, 1147, 1390, 1876, 2119], [419, 1148, 1391, 1877, 2120], [420, 1149, 1392, 1878, 2121], [421, 1150, 1393, 1879, 2122], [422, 1151, 1394, 1880, 2123], [423, 1152, 1395, 1881, 2124], [424, 1153, 1396, 1882, 2125], [425, 1154, 1397, 1883, 2126], [426, 1155, 1398, 1884, 2127], [427, 1156, 1399, 1885, 2128], [428, 1157, 1400, 1886, 2129], [429, 1158, 1401, 1887, 2130], [430, 1159, 1402, 1888, 2131], [431, 1160, 1403, 1889, 2132], [432, 1161, 1404, 1890, 2133], [433, 1162, 1405, 1891, 2134], [434, 1163, 1406, 1892, 2135], [435, 1164, 1407, 1893, 2136], [436, 1165, 1408, 1894, 2137], [437, 1166, 1409, 1895, 2138], [438, 1167, 1410, 1896, 2139], [439, 1168, 1411, 1897, 2140], [440, 1169, 1412, 1898, 2141], [441, 1170, 1413, 1899, 2142], [442, 1171, 1414, 1900, 2143], [443, 1172, 1415, 1901, 2144], [444, 1173, 1416, 1902, 2145], [445, 810, 1174, 1296, 1417, 1539, 1903, 2025, 2146], [446, 811, 1175, 1297, 1418, 1540, 1904, 2026, 2147], [447, 1176, 1419, 1905, 2148], [448, 813, 1177, 1299, 1420, 1542, 1906, 2028, 2149], [449, 814, 1178, 1300, 1421, 1543, 1907, 2029, 2150], [450, 1179, 1422, 1908, 2151], [451, 1180, 1423, 1909, 2152], [452, 1181, 1424, 1910, 2153], [453, 1182, 1425, 1911, 2154], [454, 819, 1183, 1305, 1426, 1548, 1912, 2034, 2155], [455, 820, 1184, 1306, 1427, 1549, 1913, 2035, 2156], [456, 1185, 1428, 1914, 2157], [457, 822, 1186, 1308, 1429, 1551, 1915, 2037, 2158], [458, 823, 1187, 1309, 1430, 1552, 1916, 2038, 2159], [459, 1188, 1431, 1917, 2160], [460, 1189, 1432, 1918, 2161], [461, 1190, 1433, 1919, 2162], [462, 1191, 1434, 1920, 2163], [463, 1192, 1435, 1921, 2164], [464, 1193, 1436, 1922, 2165], [465, 1194, 1437, 1923, 2166], [466, 1195, 1438, 1924, 2167], [467, 1196, 1439, 1925, 2168], [468, 1197, 1440, 1926, 2169], [469, 1198, 1441, 1927, 2170], [470, 1199, 1442, 1928, 2171], [471, 1200, 1443, 1929, 2172], [472, 837, 1201, 1323, 1444, 1566, 1930, 2052, 2173], [473, 838, 1202, 1324, 1445, 1567, 1931, 2053, 2174], [474, 1203, 1446, 1932, 2175], [475, 840, 1204, 1326, 1447, 1569, 1933, 2055, 2176], [476, 841, 1205, 1327, 1448, 1570, 1934, 2056, 2177], [477, 1206, 1449, 1935, 2178], [478, 1207, 1450, 1936, 2179], [479, 1208, 1451, 1937, 2180], [480, 1209, 1452, 1938, 2181], [481, 846, 1210, 1332, 1453, 1575, 1939, 2061, 2182], [482, 847, 1211, 1333, 1454, 1576, 1940, 2062, 2183], [483, 1212, 1455, 1941, 2184], [484, 849, 1213, 1335, 1456, 1578, 1942, 2064, 2185], [485, 850, 1214, 1336, 1457, 1579, 1943, 2065, 2186]], [[486, 1215, 1944], [487, 1216, 1945], [488, 1217, 1946], [489, 1218, 1947], [490, 1219, 1948], [491, 1220, 1949], [492, 1221, 1950], [493, 1222, 1951], [494, 1223, 1952], [495, 1224, 1953], [496, 1225, 1954], [497, 1226, 1955], [498, 1227, 1956], [499, 1228, 1957], [500, 1229, 1958], [501, 1230, 1959], [502, 1231, 1960], [503, 1232, 1961], [504, 1233, 1962], [505, 1234, 1963], [506, 1235, 1964], [507, 1236, 1965], [508, 1237, 1966], [509, 1238, 1967], [510, 1239, 1968], [511, 1240, 1969], [512, 1241, 1970], [513, 1242, 1971], [514, 1243, 1972], [515, 1244, 1973], [516, 1245, 1974], [517, 1246, 1975], [518, 1247, 1976], [519, 1248, 1977], [520, 1249, 1978], [521, 1250, 1979], [522, 1251, 1980], [523, 1252, 1981], [524, 1253, 1982], [525, 1254, 1983], [526, 1255, 1984], [527, 1256, 1985], [528, 1257, 1986], [529, 1258, 1987], [530, 1259, 1988], [531, 1260, 1989], [532, 1261, 1990], [533, 1262, 1991], [534, 1263, 1992], [535, 1264, 1993], [536, 1265, 1994], [537, 1266, 1995], [538, 1267, 1996], [539, 1268, 1997], [540, 1269, 1998], [541, 1270, 1999], [542, 1271, 2000], [543, 1272, 2001], [544, 1273, 2002], [545, 1274, 2003], [546, 1275, 2004], [547, 1276, 2005], [548, 1277, 2006], [549, 1278, 2007], [550, 1279, 2008], [551, 1280, 2009], [552, 1281, 2010], [553, 1282, 2011], [554, 1283, 2012], [555, 1284, 2013], [556, 1285, 2014], [557, 1286, 2015], [558, 1287, 2016], [559, 1288, 2017], [560, 1289, 2018], [561, 1290, 2019], [562, 1291, 2020], [563, 1292, 2021], [564, 1293, 2022], [565, 1294, 2023], [566, 1295, 2024], [567, 1296, 2025], [568, 1297, 2026], [569, 1298, 2027], [570, 1299, 2028], [571, 1300, 2029], [572, 1301, 2030], [573, 1302, 2031], [574, 1303, 2032], [575, 1304, 2033], [576, 1305, 2034], [577, 1306, 2035], [578, 1307, 2036], [579, 1308, 2037], [580, 1309, 2038], [581, 1310, 2039], [582, 1311, 2040], [583, 1312, 2041], [584, 1313, 2042], [585, 1314, 2043], [586, 1315, 2044], [587, 1316, 2045], [588, 1317, 2046], [589, 1318, 2047], [590, 1319, 2048], [591, 1320, 2049], [592, 1321, 2050], [593, 1322, 2051], [594, 1323, 2052], [595, 1324, 2053], [596, 1325, 2054], [597, 1326, 2055], [598, 1327, 2056], [599, 1328, 2057], [600, 1329, 2058], [601, 1330, 2059], [602, 1331, 2060], [603, 1332, 2061], [604, 1333, 2062], [605, 1334, 2063], [606, 1335, 2064], [607, 972, 1336, 1701, 2065], [608, 973, 1337, 1702, 2066], [609, 1338, 2067], [610, 975, 1339, 1704, 2068], [611, 976, 1340, 1705, 2069], [612, 1341, 2070], [613, 1342, 2071], [614, 1343, 2072], [615, 1344, 2073], [616, 981, 1345, 1710, 2074], [617, 982, 1346, 1711, 2075], [618, 1347, 2076], [619, 984, 1348, 1713, 2077], [620, 985, 1349, 1714, 2078], [621, 1350, 2079], [622, 1351, 2080], [623, 1352, 2081], [624, 1353, 2082], [625, 1354, 2083], [626, 1355, 2084], [627, 1356, 2085], [628, 1357, 2086], [629, 1358, 2087], [630, 1359, 2088], [631, 1360, 2089], [632, 1361, 2090], [633, 1362, 2091], [634, 999, 1363, 1728, 2092], [635, 1000, 1364, 1729, 2093], [636, 1365, 2094], [637, 1002, 1366, 1731, 2095], [638, 1003, 1367, 1732, 2096], [639, 1368, 2097], [640, 1369, 2098], [641, 1370, 2099], [642, 1371, 2100], [643, 1008, 1372, 1737, 2101], [644, 1009, 1373, 1738, 2102], [645, 1374, 2103], [646, 1011, 1375, 1740, 2104], [647, 1012, 1376, 1741, 2105], [648, 1377, 2106], [649, 1378, 2107], [650, 1379, 2108], [651, 1380, 2109], [652, 1381, 2110], [653, 1382, 2111], [654, 1383, 2112], [655, 1384, 2113], [656, 1385, 2114], [657, 1386, 2115], [658, 1387, 2116], [659, 1388, 2117], [660, 1389, 2118], [661, 1390, 2119], [662, 1391, 2120], [663, 1392, 2121], [664, 1393, 2122], [665, 1394, 2123], [666, 1395, 2124], [667, 1396, 2125], [668, 1397, 2126], [669, 1398, 2127], [670, 1399, 2128], [671, 1400, 2129], [672, 1401, 2130], [673, 1402, 2131], [674, 1403, 2132], [675, 1404, 2133], [676, 1405, 2134], [677, 1406, 2135], [678, 1407, 2136], [679, 1408, 2137], [680, 1409, 2138], [681, 1410, 2139], [682, 1411, 2140], [683, 1412, 2141], [684, 1413, 2142], [685, 1414, 2143], [686, 1415, 2144], [687, 1416, 2145], [688, 1053, 1417, 1782, 2146], [689, 1054, 1418, 1783, 2147], [690, 1419, 2148], [691, 1056, 1420, 1785, 2149], [692, 1057, 1421, 1786, 2150], [693, 1422, 2151], [694, 1423, 2152], [695, 1424, 2153], [696, 1425, 2154], [697, 1062, 1426, 1791, 2155], [698, 1063, 1427, 1792, 2156], [699, 1428, 2157], [700, 1065, 1429, 1794, 2158], [701, 1066, 1430, 1795, 2159], [702, 1431, 2160], [703, 1432, 2161], [704, 1433, 2162], [705, 1434, 2163], [706, 1435, 2164], [707, 1436, 2165], [708, 1437, 2166], [709, 1438, 2167], [710, 1439, 2168], [711, 1440, 2169], [712, 1441, 2170], [713, 1442, 2171], [714, 1443, 2172], [715, 1080, 1444, 1809, 2173], [716, 1081, 1445, 1810, 2174], [717, 1446, 2175], [718, 1083, 1447, 1812, 2176], [719, 1084, 1448, 1813, 2177], [720, 1449, 2178], [721, 1450, 2179], [722, 1451, 2180], [723, 1452, 2181], [724, 1089, 1453, 1818, 2182], [725, 1090, 1454, 1819, 2183], [726, 1455, 2184], [727, 1092, 1456, 1821, 2185], [728, 1093, 1457, 1458, 1822, 2186]], [[729, 1458, 1701, 1782, 1809, 1818, 1821, 1822], [730, 1459, 1702, 1783, 1810, 1819, 1821, 1822, 1823], [731, 1460, 1703, 1784, 1811, 1820, 1822, 1823], [732, 1461, 1704, 1785, 1812, 1821, 1824, 1825], [733, 1462, 1705, 1786, 1813, 1818, 1822, 1824, 1825, 1826], [734, 1463, 1706, 1787, 1814, 1819, 1823, 1825, 1826], [735, 1464, 1707, 1788, 1815, 1824], [736, 1465, 1708, 1789, 1816, 1821, 1825], [737, 1466, 1709, 1790, 1817, 1822, 1826], [738, 1467, 1710, 1791, 1818, 1827, 1830, 1831], [739, 1468, 1711, 1792, 1819, 1828, 1830, 1831, 1832], [740, 1469, 1712, 1793, 1820, 1829, 1831, 1832], [741, 1470, 1713, 1794, 1821, 1830, 1833, 1834], [742, 1471, 1714, 1795, 1809, 1822, 1827, 1831, 1833, 1834, 1835], [743, 1472, 1715, 1796, 1810, 1823, 1828, 1832, 1834, 1835], [744, 1473, 1716, 1797, 1824, 1833], [745, 1474, 1717, 1798, 1812, 1825, 1830, 1834], [746, 1475, 1718, 1799, 1813, 1826, 1831, 1835], [747, 1476, 1719, 1800, 1827], [748, 1477, 1720, 1801, 1828], [749, 1478, 1721, 1802, 1829], [750, 1479, 1722, 1803, 1830], [751, 1480, 1723, 1804, 1818, 1831], [752, 1481, 1724, 1805, 1819, 1832], [753, 1482, 1725, 1806, 1833], [754, 1483, 1726, 1807, 1821, 1834], [755, 1484, 1727, 1808, 1822, 1835], [756, 1485, 1728, 1809, 1836, 1845, 1848, 1849], [757, 1486, 1729, 1810, 1837, 1846, 1848, 1849, 1850], [758, 1487, 1730, 1811, 1838, 1847, 1849, 1850], [759, 1488, 1731, 1812, 1839, 1848, 1851, 1852], [760, 1489, 1732, 1813, 1840, 1845, 1849, 1851, 1852, 1853], [761, 1490, 1733, 1814, 1841, 1846, 1850, 1852, 1853], [762, 1491, 1734, 1815, 1842, 1851], [763, 1492, 1735, 1816, 1843, 1848, 1852], [764, 1493, 1736, 1817, 1844, 1849, 1853], [765, 1494, 1737, 1818, 1845, 1854, 1857, 1858], [766, 1495, 1738, 1819, 1846, 1855, 1857, 1858, 1859], [767, 1496, 1739, 1820, 1847, 1856, 1858, 1859], [768, 1497, 1740, 1821, 1848, 1857, 1860, 1861], [769, 1498, 1741, 1782, 1822, 1836, 1849, 1854, 1858, 1860, 1861, 1862], [770, 1499, 1742, 1783, 1823, 1837, 1850, 1855, 1859, 1861, 1862], [771, 1500, 1743, 1824, 1851, 1860], [772, 1501, 1744, 1785, 1825, 1839, 1852, 1857, 1861], [773, 1502, 1745, 1786, 1826, 1840, 1853, 1858, 1862], [774, 1503, 1746, 1827, 1854], [775, 1504, 1747, 1828, 1855], [776, 1505, 1748, 1829, 1856], [777, 1506, 1749, 1830, 1857], [778, 1507, 1750, 1791, 1831, 1845, 1858], [779, 1508, 1751, 1792, 1832, 1846, 1859], [780, 1509, 1752, 1833, 1860], [781, 1510, 1753, 1794, 1834, 1848, 1861], [782, 1511, 1754, 1795, 1835, 1849, 1862], [783, 1512, 1755, 1836], [784, 1513, 1756, 1837], [785, 1514, 1757, 1838], [786, 1515, 1758, 1839], [787, 1516, 1759, 1840], [788, 1517, 1760, 1841], [789, 1518, 1761, 1842], [790, 1519, 1762, 1843], [791, 1520, 1763, 1844], [792, 1521, 1764, 1845], [793, 1522, 1765, 1846], [794, 1523, 1766, 1847], [795, 1524, 1767, 1848], [796, 1525, 1768, 1809, 1849], [797, 1526, 1769, 1810, 1850], [798, 1527, 1770, 1851], [799, 1528, 1771, 1812, 1852], [800, 1529, 1772, 1813, 1853], [801, 1530, 1773, 1854], [802, 1531, 1774, 1855], [803, 1532, 1775, 1856], [804, 1533, 1776, 1857], [805, 1534, 1777, 1818, 1858], [806, 1535, 1778, 1819, 1859], [807, 1536, 1779, 1860], [808, 1537, 1780, 1821, 1861], [809, 1538, 1781, 1822, 1862], [810, 1539, 1782, 1863, 1890, 1899, 1902, 1903], [811, 1540, 1783, 1864, 1891, 1900, 1902, 1903, 1904], [812, 1541, 1784, 1865, 1892, 1901, 1903, 1904], [813, 1542, 1785, 1866, 1893, 1902, 1905, 1906], [814, 1543, 1786, 1867, 1894, 1899, 1903, 1905, 1906, 1907], [815, 1544, 1787, 1868, 1895, 1900, 1904, 1906, 1907], [816, 1545, 1788, 1869, 1896, 1905], [817, 1546, 1789, 1870, 1897, 1902, 1906], [818, 1547, 1790, 1871, 1898, 1903, 1907], [819, 1548, 1791, 1872, 1899, 1908, 1911, 1912], [820, 1549, 1792, 1873, 1900, 1909, 1911, 1912, 1913], [821, 1550, 1793, 1874, 1901, 1910, 1912, 1913], [822, 1551, 1794, 1875, 1902, 1911, 1914, 1915], [823, 1552, 1795, 1876, 1890, 1903, 1908, 1912, 1914, 1915, 1916], [824, 1553, 1796, 1877, 1891, 1904, 1909, 1913, 1915, 1916], [825, 1554, 1797, 1878, 1905, 1914], [826, 1555, 1798, 1879, 1893, 1906, 1911, 1915], [827, 1556, 1799, 1880, 1894, 1907, 1912, 1916], [828, 1557, 1800, 1881, 1908], [829, 1558, 1801, 1882, 1909], [830, 1559, 1802, 1883, 1910], [831, 1560, 1803, 1884, 1911], [832, 1561, 1804, 1885, 1899, 1912], [833, 1562, 1805, 1886, 1900, 1913], [834, 1563, 1806, 1887, 1914], [835, 1564, 1807, 1888, 1902, 1915], [836, 1565, 1808, 1889, 1903, 1916], [837, 1566, 1809, 1890, 1917, 1926, 1929, 1930], [838, 1567, 1810, 1891, 1918, 1927, 1929, 1930, 1931], [839, 1568, 1811, 1892, 1919, 1928, 1930, 1931], [840, 1569, 1812, 1893, 1920, 1929, 1932, 1933], [841, 1570, 1813, 1894, 1921, 1926, 1930, 1932, 1933, 1934], [842, 1571, 1814, 1895, 1922, 1927, 1931, 1933, 1934], [843, 1572, 1815, 1896, 1923, 1932], [844, 1573, 1816, 1897, 1924, 1929, 1933], [845, 1574, 1817, 1898, 1925, 1930, 1934], [846, 1575, 1818, 1899, 1926, 1935, 1938, 1939], [847, 1576, 1819, 1900, 1927, 1936, 1938, 1939, 1940], [848, 1577, 1820, 1901, 1928, 1937, 1939, 1940], [849, 1578, 1821, 1902, 1929, 1938, 1941, 1942], [850, 1579, 1701, 1822, 1863, 1903, 1917, 1930, 1935, 1939, 1941, 1942, 1943], [851, 1580, 1702, 1823, 1864, 1904, 1918, 1931, 1936, 1940, 1942, 1943], [852, 1581, 1824, 1905, 1932, 1941], [853, 1582, 1704, 1825, 1866, 1906, 1920, 1933, 1938, 1942], [854, 1583, 1705, 1826, 1867, 1907, 1921, 1934, 1939, 1943], [855, 1584, 1827, 1908, 1935], [856, 1585, 1828, 1909, 1936], [857, 1586, 1829, 1910, 1937], [858, 1587, 1830, 1911, 1938], [859, 1588, 1710, 1831, 1872, 1912, 1926, 1939], [860, 1589, 1711, 1832, 1873, 1913, 1927, 1940], [861, 1590, 1833, 1914, 1941], [862, 1591, 1713, 1834, 1875, 1915, 1929, 1942], [863, 1592, 1714, 1835, 1876, 1916, 1930, 1943], [864, 1593, 1836, 1917], [865, 1594, 1837, 1918], [866, 1595, 1838, 1919], [867, 1596, 1839, 1920], [868, 1597, 1840, 1921], [869, 1598, 1841, 1922], [870, 1599, 1842, 1923], [871, 1600, 1843, 1924], [872, 1601, 1844, 1925], [873, 1602, 1845, 1926], [874, 1603, 1846, 1927], [875, 1604, 1847, 1928], [876, 1605, 1848, 1929], [877, 1606, 1728, 1849, 1890, 1930], [878, 1607, 1729, 1850, 1891, 1931], [879, 1608, 1851, 1932], [880, 1609, 1731, 1852, 1893, 1933], [881, 1610, 1732, 1853, 1894, 1934], [882, 1611, 1854, 1935], [883, 1612, 1855, 1936], [884, 1613, 1856, 1937], [885, 1614, 1857, 1938], [886, 1615, 1737, 1858, 1899, 1939], [887, 1616, 1738, 1859, 1900, 1940], [888, 1617, 1860, 1941], [889, 1618, 1740, 1861, 1902, 1942], [890, 1619, 1741, 1862, 1903, 1943], [891, 1620, 1863], [892, 1621, 1864], [893, 1622, 1865], [894, 1623, 1866], [895, 1624, 1867], [896, 1625, 1868], [897, 1626, 1869], [898, 1627, 1870], [899, 1628, 1871], [900, 1629, 1872], [901, 1630, 1873], [902, 1631, 1874], [903, 1632, 1875], [904, 1633, 1876], [905, 1634, 1877], [906, 1635, 1878], [907, 1636, 1879], [908, 1637, 1880], [909, 1638, 1881], [910, 1639, 1882], [911, 1640, 1883], [912, 1641, 1884], [913, 1642, 1885], [914, 1643, 1886], [915, 1644, 1887], [916, 1645, 1888], [917, 1646, 1889], [918, 1647, 1890], [919, 1648, 1891], [920, 1649, 1892], [921, 1650, 1893], [922, 1651, 1894], [923, 1652, 1895], [924, 1653, 1896], [925, 1654, 1897], [926, 1655, 1898], [927, 1656, 1899], [928, 1657, 1900], [929, 1658, 1901], [930, 1659, 1902], [931, 1660, 1782, 1903], [932, 1661, 1783, 1904], [933, 1662, 1905], [934, 1663, 1785, 1906], [935, 1664, 1786, 1907], [936, 1665, 1908], [937, 1666, 1909], [938, 1667, 1910], [939, 1668, 1911], [940, 1669, 1791, 1912], [941, 1670, 1792, 1913], [942, 1671, 1914], [943, 1672, 1794, 1915], [944, 1673, 1795, 1916], [945, 1674, 1917], [946, 1675, 1918], [947, 1676, 1919], [948, 1677, 1920], [949, 1678, 1921], [950, 1679, 1922], [951, 1680, 1923], [952, 1681, 1924], [953, 1682, 1925], [954, 1683, 1926], [955, 1684, 1927], [956, 1685, 1928], [957, 1686, 1929], [958, 1687, 1809, 1930], [959, 1688, 1810, 1931], [960, 1689, 1932], [961, 1690, 1812, 1933], [962, 1691, 1813, 1934], [963, 1692, 1935], [964, 1693, 1936], [965, 1694, 1937], [966, 1695, 1938], [967, 1696, 1818, 1939], [968, 1697, 1819, 1940], [969, 1698, 1941], [970, 1699, 1821, 1942], [971, 1700, 1822, 1943]], [[972, 1701, 1944, 2025, 2052, 2061, 2064, 2065], [973, 1702, 1945, 2026, 2053, 2062, 2064, 2065, 2066], [974, 1703, 1946, 2027, 2054, 2063, 2065, 2066], [975, 1704, 1947, 2028, 2055, 2064, 2067, 2068], [976, 1705, 1948, 2029, 2056, 2061, 2065, 2067, 2068, 2069], [977, 1706, 1949, 2030, 2057, 2062, 2066, 2068, 2069], [978, 1707, 1950, 2031, 2058, 2067], [979, 1708, 1951, 2032, 2059, 2064, 2068], [980, 1709, 1952, 2033, 2060, 2065, 2069], [981, 1710, 1953, 2034, 2061, 2070, 2073, 2074], [982, 1711, 1954, 2035, 2062, 2071, 2073, 2074, 2075], [983, 1712, 1955, 2036, 2063, 2072, 2074, 2075], [984, 1713, 1956, 2037, 2064, 2073, 2076, 2077], [985, 1714, 1957, 2038, 2052, 2065, 2070, 2074, 2076, 2077, 2078], [986, 1715, 1958, 2039, 2053, 2066, 2071, 2075, 2077, 2078], [987, 1716, 1959, 2040, 2067, 2076], [988, 1717, 1960, 2041, 2055, 2068, 2073, 2077], [989, 1718, 1961, 2042, 2056, 2069, 2074, 2078], [990, 1719, 1962, 2043, 2070], [991, 1720, 1963, 2044, 2071], [992, 1721, 1964, 2045, 2072], [993, 1722, 1965, 2046, 2073], [994, 1723, 1966, 2047, 2061, 2074], [995, 1724, 1967, 2048, 2062, 2075], [996, 1725, 1968, 2049, 2076], [997, 1726, 1969, 2050, 2064, 2077], [998, 1727, 1970, 2051, 2065, 2078], [999, 1728, 1971, 2052, 2079, 2088, 2091, 2092], [1000, 1729, 1972, 2053, 2080, 2089, 2091, 2092, 2093], [1001, 1730, 1973, 2054, 2081, 2090, 2092, 2093], [1002, 1731, 1974, 2055, 2082, 2091, 2094, 2095], [1003, 1732, 1975, 2056, 2083, 2088, 2092, 2094, 2095, 2096], [1004, 1733, 1976, 2057, 2084, 2089, 2093, 2095, 2096], [1005, 1734, 1977, 2058, 2085, 2094], [1006, 1735, 1978, 2059, 2086, 2091, 2095], [1007, 1736, 1979, 2060, 2087, 2092, 2096], [1008, 1737, 1980, 2061, 2088, 2097, 2100, 2101], [1009, 1738, 1981, 2062, 2089, 2098, 2100, 2101, 2102], [1010, 1739, 1982, 2063, 2090, 2099, 2101, 2102], [1011, 1740, 1983, 2064, 2091, 2100, 2103, 2104], [1012, 1741, 1984, 2025, 2065, 2079, 2092, 2097, 2101, 2103, 2104, 2105], [1013, 1742, 1985, 2026, 2066, 2080, 2093, 2098, 2102, 2104, 2105], [1014, 1743, 1986, 2067, 2094, 2103], [1015, 1744, 1987, 2028, 2068, 2082, 2095, 2100, 2104], [1016, 1745, 1988, 2029, 2069, 2083, 2096, 2101, 2105], [1017, 1746, 1989, 2070, 2097], [1018, 1747, 1990, 2071, 2098], [1019, 1748, 1991, 2072, 2099], [1020, 1749, 1992, 2073, 2100], [1021, 1750, 1993, 2034, 2074, 2088, 2101], [1022, 1751, 1994, 2035, 2075, 2089, 2102], [1023, 1752, 1995, 2076, 2103], [1024, 1753, 1996, 2037, 2077, 2091, 2104], [1025, 1754, 1997, 2038, 2078, 2092, 2105], [1026, 1755, 1998, 2079], [1027, 1756, 1999, 2080], [1028, 1757, 2000, 2081], [1029, 1758, 2001, 2082], [1030, 1759, 2002, 2083], [1031, 1760, 2003, 2084], [1032, 1761, 2004, 2085], [1033, 1762, 2005, 2086], [1034, 1763, 2006, 2087], [1035, 1764, 2007, 2088], [1036, 1765, 2008, 2089], [1037, 1766, 2009, 2090], [1038, 1767, 2010, 2091], [1039, 1768, 2011, 2052, 2092], [1040, 1769, 2012, 2053, 2093], [1041, 1770, 2013, 2094], [1042, 1771, 2014, 2055, 2095], [1043, 1772, 2015, 2056, 2096], [1044, 1773, 2016, 2097], [1045, 1774, 2017, 2098], [1046, 1775, 2018, 2099], [1047, 1776, 2019, 2100], [1048, 1777, 2020, 2061, 2101], [1049, 1778, 2021, 2062, 2102], [1050, 1779, 2022, 2103], [1051, 1780, 2023, 2064, 2104], [1052, 1781, 2024, 2065, 2105], [1053, 1782, 2025, 2106, 2133, 2142, 2145, 2146], [1054, 1783, 2026, 2107, 2134, 2143, 2145, 2146, 2147], [1055, 1784, 2027, 2108, 2135, 2144, 2146, 2147], [1056, 1785, 2028, 2109, 2136, 2145, 2148, 2149], [1057, 1786, 2029, 2110, 2137, 2142, 2146, 2148, 2149, 2150], [1058, 1787, 2030, 2111, 2138, 2143, 2147, 2149, 2150], [1059, 1788, 2031, 2112, 2139, 2148], [1060, 1789, 2032, 2113, 2140, 2145, 2149], [1061, 1790, 2033, 2114, 2141, 2146, 2150], [1062, 1791, 2034, 2115, 2142, 2151, 2154, 2155], [1063, 1792, 2035, 2116, 2143, 2152, 2154, 2155, 2156], [1064, 1793, 2036, 2117, 2144, 2153, 2155, 2156], [1065, 1794, 2037, 2118, 2145, 2154, 2157, 2158], [1066, 1795, 2038, 2119, 2133, 2146, 2151, 2155, 2157, 2158, 2159], [1067, 1796, 2039, 2120, 2134, 2147, 2152, 2156, 2158, 2159], [1068, 1797, 2040, 2121, 2148, 2157], [1069, 1798, 2041, 2122, 2136, 2149, 2154, 2158], [1070, 1799, 2042, 2123, 2137, 2150, 2155, 2159], [1071, 1800, 2043, 2124, 2151], [1072, 1801, 2044, 2125, 2152], [1073, 1802, 2045, 2126, 2153], [1074, 1803, 2046, 2127, 2154], [1075, 1804, 2047, 2128, 2142, 2155], [1076, 1805, 2048, 2129, 2143, 2156], [1077, 1806, 2049, 2130, 2157], [1078, 1807, 2050, 2131, 2145, 2158], [1079, 1808, 2051, 2132, 2146, 2159], [1080, 1809, 2052, 2133, 2160, 2169, 2172, 2173], [1081, 1810, 2053, 2134, 2161, 2170, 2172, 2173, 2174], [1082, 1811, 2054, 2135, 2162, 2171, 2173, 2174], [1083, 1812, 2055, 2136, 2163, 2172, 2175, 2176], [1084, 1813, 2056, 2137, 2164, 2169, 2173, 2175, 2176, 2177], [1085, 1814, 2057, 2138, 2165, 2170, 2174, 2176, 2177], [1086, 1815, 2058, 2139, 2166, 2175], [1087, 1816, 2059, 2140, 2167, 2172, 2176], [1088, 1817, 2060, 2141, 2168, 2173, 2177], [1089, 1818, 2061, 2142, 2169, 2178, 2181, 2182], [1090, 1819, 2062, 2143, 2170, 2179, 2181, 2182, 2183], [1091, 1820, 2063, 2144, 2171, 2180, 2182, 2183], [1092, 1821, 2064, 2145, 2172, 2181, 2184, 2185], [0, 1093, 1458, 1822, 1944, 2065, 2106, 2146, 2160, 2173, 2178, 2182, 2184, 2185, 2186], [1, 1094, 1459, 1823, 1945, 2066, 2107, 2147, 2161, 2174, 2179, 2183, 2185, 2186], [1095, 1824, 2067, 2148, 2175, 2184], [3, 1096, 1461, 1825, 1947, 2068, 2109, 2149, 2163, 2176, 2181, 2185], [4, 1097, 1462, 1826, 1948, 2069, 2110, 2150, 2164, 2177, 2182, 2186], [1098, 1827, 2070, 2151, 2178], [1099, 1828, 2071, 2152, 2179], [1100, 1829, 2072, 2153, 2180], [1101, 1830, 2073, 2154, 2181], [9, 1102, 1467, 1831, 1953, 2074, 2115, 2155, 2169, 2182], [10, 1103, 1468, 1832, 1954, 2075, 2116, 2156, 2170, 2183], [1104, 1833, 2076, 2157, 2184], [12, 1105, 1470, 1834, 1956, 2077, 2118, 2158, 2172, 2185], [13, 1106, 1471, 1835, 1957, 2078, 2119, 2159, 2173, 2186], [1107, 1836, 2079, 2160], [1108, 1837, 2080, 2161], [1109, 1838, 2081, 2162], [1110, 1839, 2082, 2163], [1111, 1840, 2083, 2164], [1112, 1841, 2084, 2165], [1113, 1842, 2085, 2166], [1114, 1843, 2086, 2167], [1115, 1844, 2087, 2168], [1116, 1845, 2088, 2169], [1117, 1846, 2089, 2170], [1118, 1847, 2090, 2171], [1119, 1848, 2091, 2172], [27, 1120, 1485, 1849, 1971, 2092, 2133, 2173], [28, 1121, 1486, 1850, 1972, 2093, 2134, 2174], [1122, 1851, 2094, 2175], [30, 1123, 1488, 1852, 1974, 2095, 2136, 2176], [31, 1124, 1489, 1853, 1975, 2096, 2137, 2177], [1125, 1854, 2097, 2178], [1126, 1855, 2098, 2179], [1127, 1856, 2099, 2180], [1128, 1857, 2100, 2181], [36, 1129, 1494, 1858, 1980, 2101, 2142, 2182], [37, 1130, 1495, 1859, 1981, 2102, 2143, 2183], [1131, 1860, 2103, 2184], [39, 1132, 1497, 1861, 1983, 2104, 2145, 2185], [40, 1133, 1498, 1862, 1984, 2105, 2146, 2186], [1134, 1863, 2106], [1135, 1864, 2107], [1136, 1865, 2108], [1137, 1866, 2109], [1138, 1867, 2110], [1139, 1868, 2111], [1140, 1869, 2112], [1141, 1870, 2113], [1142, 1871, 2114], [1143, 1872, 2115], [1144, 1873, 2116], [1145, 1874, 2117], [1146, 1875, 2118], [1147, 1876, 2119], [1148, 1877, 2120], [1149, 1878, 2121], [1150, 1879, 2122], [1151, 1880, 2123], [1152, 1881, 2124], [1153, 1882, 2125], [1154, 1883, 2126], [1155, 1884, 2127], [1156, 1885, 2128], [1157, 1886, 2129], [1158, 1887, 2130], [1159, 1888, 2131], [1160, 1889, 2132], [1161, 1890, 2133], [1162, 1891, 2134], [1163, 1892, 2135], [1164, 1893, 2136], [1165, 1894, 2137], [1166, 1895, 2138], [1167, 1896, 2139], [1168, 1897, 2140], [1169, 1898, 2141], [1170, 1899, 2142], [1171, 1900, 2143], [1172, 1901, 2144], [1173, 1902, 2145], [81, 1174, 1539, 1903, 2025, 2146], [82, 1175, 1540, 1904, 2026, 2147], [1176, 1905, 2148], [84, 1177, 1542, 1906, 2028, 2149], [85, 1178, 1543, 1907, 2029, 2150], [1179, 1908, 2151], [1180, 1909, 2152], [1181, 1910, 2153], [1182, 1911, 2154], [90, 1183, 1548, 1912, 2034, 2155], [91, 1184, 1549, 1913, 2035, 2156], [1185, 1914, 2157], [93, 1186, 1551, 1915, 2037, 2158], [94, 1187, 1552, 1916, 2038, 2159], [1188, 1917, 2160], [1189, 1918, 2161], [1190, 1919, 2162], [1191, 1920, 2163], [1192, 1921, 2164], [1193, 1922, 2165], [1194, 1923, 2166], [1195, 1924, 2167], [1196, 1925, 2168], [1197, 1926, 2169], [1198, 1927, 2170], [1199, 1928, 2171], [1200, 1929, 2172], [108, 1201, 1566, 1930, 2052, 2173], [109, 1202, 1567, 1931, 2053, 2174], [1203, 1932, 2175], [111, 1204, 1569, 1933, 2055, 2176], [112, 1205, 1570, 1934, 2056, 2177], [1206, 1935, 2178], [1207, 1936, 2179], [1208, 1937, 2180], [1209, 1938, 2181], [117, 1210, 1575, 1939, 2061, 2182], [118, 1211, 1576, 1940, 2062, 2183], [1212, 1941, 2184], [120, 1213, 1578, 1942, 2064, 2185], [121, 1214, 1579, 1943, 2065, 2186]], [[1215, 1944], [1216, 1945], [1217, 1946], [1218, 1947], [1219, 1948], [1220, 1949], [1221, 1950], [1222, 1951], [1223, 1952], [1224, 1953], [1225, 1954], [1226, 1955], [1227, 1956], [1228, 1957], [1229, 1958], [1230, 1959], [1231, 1960], [1232, 1961], [1233, 1962], [1234, 1963], [1235, 1964], [1236, 1965], [1237, 1966], [1238, 1967], [1239, 1968], [1240, 1969], [1241, 1970], [1242, 1971], [1243, 1972], [1244, 1973], [1245, 1974], [1246, 1975], [1247, 1976], [1248, 1977], [1249, 1978], [1250, 1979], [1251, 1980], [1252, 1981], [1253, 1982], [1254, 1983], [1255, 1984], [1256, 1985], [1257, 1986], [1258, 1987], [1259, 1988], [1260, 1989], [1261, 1990], [1262, 1991], [1263, 1992], [1264, 1993], [1265, 1994], [1266, 1995], [1267, 1996], [1268, 1997], [1269, 1998], [1270, 1999], [1271, 2000], [1272, 2001], [1273, 2002], [1274, 2003], [1275, 2004], [1276, 2005], [1277, 2006], [1278, 2007], [1279, 2008], [1280, 2009], [1281, 2010], [1282, 2011], [1283, 2012], [1284, 2013], [1285, 2014], [1286, 2015], [1287, 2016], [1288, 2017], [1289, 2018], [1290, 2019], [1291, 2020], [1292, 2021], [1293, 2022], [1294, 2023], [1295, 2024], [1296, 2025], [1297, 2026], [1298, 2027], [1299, 2028], [1300, 2029], [1301, 2030], [1302, 2031], [1303, 2032], [1304, 2033], [1305, 2034], [1306, 2035], [1307, 2036], [1308, 2037], [1309, 2038], [1310, 2039], [1311, 2040], [1312, 2041], [1313, 2042], [1314, 2043], [1315, 2044], [1316, 2045], [1317, 2046], [1318, 2047], [1319, 2048], [1320, 2049], [1321, 2050], [1322, 2051], [1323, 2052], [1324, 2053], [1325, 2054], [1326, 2055], [1327, 2056], [1328, 2057], [1329, 2058], [1330, 2059], [1331, 2060], [1332, 2061], [1333, 2062], [1334, 2063], [1335, 2064], [243, 1336, 1701, 2065], [244, 1337, 1702, 2066], [1338, 2067], [246, 1339, 1704, 2068], [247, 1340, 1705, 2069], [1341, 2070], [1342, 2071], [1343, 2072], [1344, 2073], [252, 1345, 1710, 2074], [253, 1346, 1711, 2075], [1347, 2076], [255, 1348, 1713, 2077], [256, 1349, 1714, 2078], [1350, 2079], [1351, 2080], [1352, 2081], [1353, 2082], [1354, 2083], [1355, 2084], [1356, 2085], [1357, 2086], [1358, 2087], [1359, 2088], [1360, 2089], [1361, 2090], [1362, 2091], [270, 1363, 1728, 2092], [271, 1364, 1729, 2093], [1365, 2094], [273, 1366, 1731, 2095], [274, 1367, 1732, 2096], [1368, 2097], [1369, 2098], [1370, 2099], [1371, 2100], [279, 1372, 1737, 2101], [280, 1373, 1738, 2102], [1374, 2103], [282, 1375, 1740, 2104], [283, 1376, 1741, 2105], [1377, 2106], [1378, 2107], [1379, 2108], [1380, 2109], [1381, 2110], [1382, 2111], [1383, 2112], [1384, 2113], [1385, 2114], [1386, 2115], [1387, 2116], [1388, 2117], [1389, 2118], [1390, 2119], [1391, 2120], [1392, 2121], [1393, 2122], [1394, 2123], [1395, 2124], [1396, 2125], [1397, 2126], [1398, 2127], [1399, 2128], [1400, 2129], [1401, 2130], [1402, 2131], [1403, 2132], [1404, 2133], [1405, 2134], [1406, 2135], [1407, 2136], [1408, 2137], [1409, 2138], [1410, 2139], [1411, 2140], [1412, 2141], [1413, 2142], [1414, 2143], [1415, 2144], [1416, 2145], [324, 1417, 1782, 2146], [325, 1418, 1783, 2147], [1419, 2148], [327, 1420, 1785, 2149], [328, 1421, 1786, 2150], [1422, 2151], [1423, 2152], [1424, 2153], [1425, 2154], [333, 1426, 1791, 2155], [334, 1427, 1792, 2156], [1428, 2157], [336, 1429, 1794, 2158], [337, 1430, 1795, 2159], [1431, 2160], [1432, 2161], [1433, 2162], [1434, 2163], [1435, 2164], [1436, 2165], [1437, 2166], [1438, 2167], [1439, 2168], [1440, 2169], [1441, 2170], [1442, 2171], [1443, 2172], [351, 1444, 1809, 2173], [352, 1445, 1810, 2174], [1446, 2175], [354, 1447, 1812, 2176], [355, 1448, 1813, 2177], [1449, 2178], [1450, 2179], [1451, 2180], [1452, 2181], [360, 1453, 1818, 2182], [361, 1454, 1819, 2183], [1455, 2184], [363, 1456, 1821, 2185], [364, 1457, 1822, 2186]], [[1458], [1459], [1460], [1461], [1462], [1463], [1464], [1465], [1466], [1467], [1468], [1469], [1470], [1471], [1472], [1473], [1474], [1475], [1476], [1477], [1478], [1479], [1480], [1481], [1482], [1483], [1484], [1485], [1486], [1487], [1488], [1489], [1490], [1491], [1492], [1493], [1494], [1495], [1496], [1497], [1498], [1499], [1500], [1501], [1502], [1503], [1504], [1505], [1506], [1507], [1508], [1509], [1510], [1511], [1512], [1513], [1514], [1515], [1516], [1517], [1518], [1519], [1520], [1521], [1522], [1523], [1524], [1525], [1526], [1527], [1528], [1529], [1530], [1531], [1532], [1533], [1534], [1535], [1536], [1537], [1538], [1539], [1540], [1541], [1542], [1543], [1544], [1545], [1546], [1547], [1548], [1549], [1550], [1551], [1552], [1553], [1554], [1555], [1556], [1557], [1558], [1559], [1560], [1561], [1562], [1563], [1564], [1565], [1566], [1567], [1568], [1569], [1570], [1571], [1572], [1573], [1574], [1575], [1576], [1577], [1578], [1579], [1580], [1581], [1582], [1583], [1584], [1585], [1586], [1587], [1588], [1589], [1590], [1591], [1592], [1593], [1594], [1595], [1596], [1597], [1598], [1599], [1600], [1601], [1602], [1603], [1604], [1605], [1606], [1607], [1608], [1609], [1610], [1611], [1612], [1613], [1614], [1615], [1616], [1617], [1618], [1619], [1620], [1621], [1622], [1623], [1624], [1625], [1626], [1627], [1628], [1629], [1630], [1631], [1632], [1633], [1634], [1635], [1636], [1637], [1638], [1639], [1640], [1641], [1642], [1643], [1644], [1645], [1646], [1647], [1648], [1649], [1650], [1651], [1652], [1653], [1654], [1655], [1656], [1657], [1658], [1659], [1660], [1661], [1662], [1663], [1664], [1665], [1666], [1667], [1668], [1669], [1670], [1671], [1672], [1673], [1674], [1675], [1676], [1677], [1678], [1679], [1680], [1681], [1682], [1683], [1684], [1685], [1686], [1687], [1688], [1689], [1690], [1691], [1692], [1693], [1694], [1695], [1696], [1697], [1698], [1699], [1700]], [[1701], [1702], [1703], [1704], [1705], [1706], [1707], [1708], [1709], [1710], [1711], [1712], [1713], [1714], [1715], [1716], [1717], [1718], [1719], [1720], [1721], [1722], [1723], [1724], [1725], [1726], [1727], [1728], [1729], [1730], [1731], [1732], [1733], [1734], [1735], [1736], [1737], [1738], [1739], [1740], [1741], [1742], [1743], [1744], [1745], [1746], [1747], [1748], [1749], [1750], [1751], [1752], [1753], [1754], [1755], [1756], [1757], [1758], [1759], [1760], [1761], [1762], [1763], [1764], [1765], [1766], [1767], [1768], [1769], [1770], [1771], [1772], [1773], [1774], [1775], [1776], [1777], [1778], [1779], [1780], [1781], [1782], [1783], [1784], [1785], [1786], [1787], [1788], [1789], [1790], [1791], [1792], [1793], [1794], [1795], [1796], [1797], [1798], [1799], [1800], [1801], [1802], [1803], [1804], [1805], [1806], [1807], [1808], [1809], [1810], [1811], [1812], [1813], [1814], [1815], [1816], [1817], [1818], [1819], [1820], [1821], [729, 1822], [730, 1823], [1824], [732, 1825], [733, 1826], [1827], [1828], [1829], [1830], [738, 1831], [739, 1832], [1833], [741, 1834], [742, 1835], [1836], [1837], [1838], [1839], [1840], [1841], [1842], [1843], [1844], [1845], [1846], [1847], [1848], [756, 1849], [757, 1850], [1851], [759, 1852], [760, 1853], [1854], [1855], [1856], [1857], [765, 1858], [766, 1859], [1860], [768, 1861], [769, 1862], [1863], [1864], [1865], [1866], [1867], [1868], [1869], [1870], [1871], [1872], [1873], [1874], [1875], [1876], [1877], [1878], [1879], [1880], [1881], [1882], [1883], [1884], [1885], [1886], [1887], [1888], [1889], [1890], [1891], [1892], [1893], [1894], [1895], [1896], [1897], [1898], [1899], [1900], [1901], [1902], [810, 1903], [811, 1904], [1905], [813, 1906], [814, 1907], [1908], [1909], [1910], [1911], [819, 1912], [820, 1913], [1914], [822, 1915], [823, 1916], [1917], [1918], [1919], [1920], [1921], [1922], [1923], [1924], [1925], [1926], [1927], [1928], [1929], [837, 1930], [838, 1931], [1932], [840, 1933], [841, 1934], [1935], [1936], [1937], [1938], [846, 1939], [847, 1940], [1941], [849, 1942], [850, 1943]], [[1944], [1945], [1946], [1947], [1948], [1949], [1950], [1951], [1952], [1953], [1954], [1955], [1956], [1957], [1958], [1959], [1960], [1961], [1962], [1963], [1964], [1965], [1966], [1967], [1968], [1969], [1970], [1971], [1972], [1973], [1974], [1975], [1976], [1977], [1978], [1979], [1980], [1981], [1982], [1983], [1984], [1985], [1986], [1987], [1988], [1989], [1990], [1991], [1992], [1993], [1994], [1995], [1996], [1997], [1998], [1999], [2000], [2001], [2002], [2003], [2004], [2005], [2006], [2007], [2008], [2009], [2010], [2011], [2012], [2013], [2014], [2015], [2016], [2017], [2018], [2019], [2020], [2021], [2022], [2023], [2024], [2025], [2026], [2027], [2028], [2029], [2030], [2031], [2032], [2033], [2034], [2035], [2036], [2037], [2038], [2039], [2040], [2041], [2042], [2043], [2044], [2045], [2046], [2047], [2048], [2049], [2050], [2051], [2052], [2053], [2054], [2055], [2056], [2057], [2058], [2059], [2060], [2061], [2062], [2063], [2064], [972, 2065], [973, 2066], [2067], [975, 2068], [976, 2069], [2070], [2071], [2072], [2073], [981, 2074], [982, 2075], [2076], [984, 2077], [985, 2078], [2079], [2080], [2081], [2082], [2083], [2084], [2085], [2086], [2087], [2088], [2089], [2090], [2091], [999, 2092], [1000, 2093], [2094], [1002, 2095], [1003, 2096], [2097], [2098], [2099], [2100], [1008, 2101], [1009, 2102], [2103], [1011, 2104], [1012, 2105], [2106], [2107], [2108], [2109], [2110], [2111], [2112], [2113], [2114], [2115], [2116], [2117], [2118], [2119], [2120], [2121], [2122], [2123], [2124], [2125], [2126], [2127], [2128], [2129], [2130], [2131], [2132], [2133], [2134], [2135], [2136], [2137], [2138], [2139], [2140], [2141], [2142], [2143], [2144], [2145], [1053, 2146], [1054, 2147], [2148], [1056, 2149], [1057, 2150], [2151], [2152], [2153], [2154], [1062, 2155], [1063, 2156], [2157], [1065, 2158], [1066, 2159], [2160], [2161], [2162], [2163], [2164], [2165], [2166], [2167], [2168], [2169], [2170], [2171], [2172], [1080, 2173], [1081, 2174], [2175], [1083, 2176], [1084, 2177], [2178], [2179], [2180], [2181], [1089, 2182], [1090, 2183], [2184], [1092, 2185], [0, 1093, 2186]]]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
abbrev adjLit : List (List ℕ) := adjC.flatten

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def Tt : ℕ := 1293125767983857140780343
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem T_ok : ∀ a < 3, ∀ b < 3, ∀ c < 3, ∀ d < 3,
    (Tt.testBit (((a * 3 + b) * 3 + c) * 3 + d) = true ↔ loc a b c d) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def tabF (j a b : ℕ) : ℕ := ((List.range N).filter (fun t => Tt.testBit (((a * 3 + b) * 3 + dig t j) * 3 + dig t (j + 1)))).foldl (fun m x => m ||| 2 ^ x) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem tabL_eq : ∀ j < 6, ∀ a < 3, ∀ b < 3, tab j a b = tabF j a b := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem tab_ok : ∀ j < 6, ∀ a < 3, ∀ b < 3, ∀ t < N,
    ((tab j a b).testBit t = true ↔ loc a b (dig t j) (dig t (j + 1))) := by
  intro j hj a ha b hb t ht
  rw [tabL_eq j hj a ha b hb]
  unfold tabF
  rw [testBit_foldl_lor]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, List.mem_filter, List.mem_range, decide_eq_true_eq]
  rw [← T_ok a ha b hb (dig t j) (Nat.mod_lt _ (by norm_num)) (dig t (j + 1)) (Nat.mod_lt _ (by norm_num))]
  simp [ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem RN_iff (s t : Fin N) :
    RN s t ↔ ∀ j < 6, loc (dig s j) (dig s (j + 1)) (dig t j) (dig t (j + 1)) := by
  constructor
  · intro h j hj
    exact h ⟨j, hj⟩
  · intro h j
    exact h j.1 j.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem hR : ∀ s t : Fin N, RN s t ↔ (mask s).testBit t = true := by
  intro s t
  rw [RN_iff]
  unfold mask
  rw [testBit_foldl_land]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rw [Nat.testBit_two_pow_sub_one]
  simp only [decide_eq_true_eq, t.2, true_and]
  apply forall_congr'; intro j; apply forall_congr'; intro hj
  exact (tab_ok j hj _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) t t.2).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem hAdj : AdjOK N RN adjLit :=
  adjOK_of_chk _ RN mask adjLit hR (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem a_eq (n : ℕ) : a n = ∑ s, V RN n s := by
  rw [aeq n]
  rw [Nat.card_congr (chainEquiv e0 (R' := RN) (fun a b => by simp [RN]) n), Nat.card_eq_fintype_card, cardChain]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def Dg : ℕ := 45
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem hDg : ∀ l ∈ adjLit, l.length ≤ Dg := by
  intro l hl
  revert l
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem hKb : Dg ^ 10 < 2 ^ 128 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem hlenA : adjLit.length = N := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem a_iter (n : ℕ) : a n = (iterL adjLit N n).sum := by
  rw [a_eq, sum_V_eq _ RN adjLit hAdj]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def cpf : ℕ → ℕ := fun j => [0, 0, 0, 0, 116, 0, 255, 0, 60, 0, 1].getD j 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def cnf : ℕ → ℕ := fun j => [0, 0, 0, 24, 0, 234, 0, 162, 0, 12, 0].getD j 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem hBpos : 0 < BB := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem hNB : N = N / BB * BB := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem hchA : ∀ ch ∈ adjC, ch.length = BB := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem chkv : (comb N cpf (fun j => unpackC N (iterC adjC N j)) (List.range (10 + 1)) =
    comb N cnf (fun j => unpackC N (iterC adjC N j)) (List.range (10 + 1))) ∧
    ∀ i ∈ List.range (9 + 1), (unpackC N (iterC adjC N i)).sum = [2187, 10875, 31215, 91030, 265546, 764315, 2168405, 6060594, 16732140, 45832201].getD i 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
def cc : ℕ → ℤ := fun j => (cpf j : ℤ) - cnf j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem hrec (k : ℕ) : (a (k + 10) : ℤ) = (24 : ℤ) * a (k + 3) + (-116 : ℤ) * a (k + 4) + (234 : ℤ) * a (k + 5) + (-255 : ℤ) * a (k + 6) + (162 : ℤ) * a (k + 7) + (-60 : ℤ) * a (k + 8) + (12 : ℤ) * a (k + 9) := by
  have h := rec_total RN 10 cc (h0_of_chkC _ RN adjC hAdj hBpos hNB hchA Dg hDg (by decide +kernel) 10 hKb 10 (by omega) cpf cnf chkv.1) k
  have e0 : cc 0 = 0 := by simp [cc, cpf, cnf]
  have e1 : cc 1 = 0 := by simp [cc, cpf, cnf]
  have e2 : cc 2 = 0 := by simp [cc, cpf, cnf]
  have e3 : cc 3 = -24 := by simp [cc, cpf, cnf]
  have e4 : cc 4 = 116 := by simp [cc, cpf, cnf]
  have e5 : cc 5 = -234 := by simp [cc, cpf, cnf]
  have e6 : cc 6 = 255 := by simp [cc, cpf, cnf]
  have e7 : cc 7 = -162 := by simp [cc, cpf, cnf]
  have e8 : cc 8 = 60 := by simp [cc, cpf, cnf]
  have e9 : cc 9 = -12 := by simp [cc, cpf, cnf]
  have e10 : cc 10 = 1 := by simp [cc, cpf, cnf]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10] at h
  simp only [a_eq]
  push_cast
  simp only [Nat.add_zero, zero_mul, zero_add] at h ⊢
  linarith

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem v1 : a 1 = 10875 := by
  rw [a_iter, ← unpack_iterC adjC N Dg hBpos hNB hchA hlenA hDg (by decide +kernel) 10 hKb 1 (by omega)]
  exact (chkv.2 1 (by simp)).trans (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem v2 : a 2 = 31215 := by
  rw [a_iter, ← unpack_iterC adjC N Dg hBpos hNB hchA hlenA hDg (by decide +kernel) 10 hKb 2 (by omega)]
  exact (chkv.2 2 (by simp)).trans (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem v3 : a 3 = 91030 := by
  rw [a_iter, ← unpack_iterC adjC N Dg hBpos hNB hchA hlenA hDg (by decide +kernel) 10 hKb 3 (by omega)]
  exact (chkv.2 3 (by simp)).trans (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem v4 : a 4 = 265546 := by
  rw [a_iter, ← unpack_iterC adjC N Dg hBpos hNB hchA hlenA hDg (by decide +kernel) 10 hKb 4 (by omega)]
  exact (chkv.2 4 (by simp)).trans (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem v5 : a 5 = 764315 := by
  rw [a_iter, ← unpack_iterC adjC N Dg hBpos hNB hchA hlenA hDg (by decide +kernel) 10 hKb 5 (by omega)]
  exact (chkv.2 5 (by simp)).trans (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem v6 : a 6 = 2168405 := by
  rw [a_iter, ← unpack_iterC adjC N Dg hBpos hNB hchA hlenA hDg (by decide +kernel) 10 hKb 6 (by omega)]
  exact (chkv.2 6 (by simp)).trans (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem v7 : a 7 = 6060594 := by
  rw [a_iter, ← unpack_iterC adjC N Dg hBpos hNB hchA hlenA hDg (by decide +kernel) 10 hKb 7 (by omega)]
  exact (chkv.2 7 (by simp)).trans (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem v8 : a 8 = 16732140 := by
  rw [a_iter, ← unpack_iterC adjC N Dg hBpos hNB hchA hlenA hDg (by decide +kernel) 10 hKb 8 (by omega)]
  exact (chkv.2 8 (by simp)).trans (by decide)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem v9 : a 9 = 45832201 := by
  rw [a_iter, ← unpack_iterC adjC N Dg hBpos hNB hchA hlenA hDg (by decide +kernel) 10 hKb 9 (by omega)]
  exact (chkv.2 9 (by simp)).trans (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem closed (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = (-8787 + 3389 * 2 ^ n + 169 * 3 ^ (3 + n) + (14186 - 99 * 2 ^ (4 + n)) * (n : ℚ) + 36 * (145 + 33 * 2 ^ (1 + n)) * (n : ℚ) ^ 2) / 4 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ 9
    · interval_cases n
      · rw [v3]; norm_num
      · rw [v4]; norm_num
      · rw [v5]; norm_num
      · rw [v6]; norm_num
      · rw [v7]; norm_num
      · rw [v8]; norm_num
      · rw [v9]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
      have r : (a (k + 10) : ℚ) = (24 : ℚ) * a (k + 3) + (-116 : ℚ) * a (k + 4) + (234 : ℚ) * a (k + 5) + (-255 : ℚ) * a (k + 6) + (162 : ℚ) * a (k + 7) + (-60 : ℚ) * a (k + 8) + (12 : ℚ) * a (k + 9) := by exact_mod_cast hrec k
      have i3 := ih (k + 3) (by omega) (by omega)
      have i4 := ih (k + 4) (by omega) (by omega)
      have i5 := ih (k + 5) (by omega) (by omega)
      have i6 := ih (k + 6) (by omega) (by omega)
      have i7 := ih (k + 7) (by omega) (by omega)
      have i8 := ih (k + 8) (by omega) (by omega)
      have i9 := ih (k + 9) (by omega) (by omega)
      rw [r, i3, i4, i5, i6, i7, i8, i9]
      push_cast
      ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  apply gf_gen _ 7 9 (fun j => [(1 : ℚ), (-12 : ℚ), (60 : ℚ), (-162 : ℚ), (255 : ℚ), (-234 : ℚ), (116 : ℚ), (-24 : ℚ)].getD j 0) (fun j => [(0 : ℚ), (10875 : ℚ), (-99285 : ℚ), (368950 : ℚ), (-715664 : ℚ), (755858 : ℚ), (-402400 : ℚ), (50022 : ℚ), (63432 : ℚ), (-26568 : ℚ)].getD j 0)
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · norm_num
  · intro n hn
    simp only [List.getD_eq_getElem?_getD]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp_all
  · intro n
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · simp [Finset.sum_range_succ]
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      have c0 := closed (k + 10) (by omega)
      have c1 := closed (k + 9) (by omega)
      have c2 := closed (k + 8) (by omega)
      have c3 := closed (k + 7) (by omega)
      have c4 := closed (k + 6) (by omega)
      have c5 := closed (k + 5) (by omega)
      have c6 := closed (k + 4) (by omega)
      have c7 := closed (k + 3) (by omega)
      simp [c0, c1, c2, c3, c4, c5, c6, c7]
      ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem recS (n : ℕ) (hn : 10 ≤ n) : (a n : ℤ) = 12 * (a (n - 1) : ℤ) - 60 * (a (n - 2) : ℤ) + 162 * (a (n - 3) : ℤ) - 255 * (a (n - 4) : ℤ) + 234 * (a (n - 5) : ℤ) - 116 * (a (n - 6) : ℤ) + 24 * (a (n - 7) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
  have e1 : k + 10 - 1 = k + 9 := by omega
  have e2 : k + 10 - 2 = k + 8 := by omega
  have e3 : k + 10 - 3 = k + 7 := by omega
  have e4 : k + 10 - 4 = k + 6 := by omega
  have e5 : k + 10 - 5 = k + 5 := by omega
  have e6 : k + 10 - 6 = k + 4 := by omega
  have e7 : k + 10 - 7 = k + 3 := by omega
  rw [e1, e2, e3, e4, e5, e6, e7]
  have h : (a (k + 10) : ℚ) = 12 * (a (k + 9) : ℚ) - 60 * (a (k + 8) : ℚ) + 162 * (a (k + 7) : ℚ) - 255 * (a (k + 6) : ℚ) + 234 * (a (k + 5) : ℚ) - 116 * (a (k + 4) : ℚ) + 24 * (a (k + 3) : ℚ) := by
    rw [closed (k + 10) (by omega), closed (k + 9) (by omega), closed (k + 8) (by omega), closed (k + 7) (by omega), closed (k + 6) (by omega), closed (k + 5) (by omega), closed (k + 4) (by omega), closed (k + 3) (by omega)]
    push_cast
    ring_nf
  exact_mod_cast h

end OMA.S_oeis_a250896

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a250896.main := ⟨OMA.S_oeis_a250896.recS, OMA.S_oeis_a250896.gf, OMA.S_oeis_a250896.closed⟩

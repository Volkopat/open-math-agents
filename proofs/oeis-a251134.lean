import OMAStatements.S_oeis_a251134
import Mathlib

namespace OMA.S_oeis_a251134

section fastvec
/-! Fast transfer-vector kit.  States are `Fin N`; the (sparse) transition relation is given by an explicit
adjacency list `adj : List (List ℕ)`; vectors are `List ℕ`; one step is a fold over the lists.  Only Nat.add
on literals is evaluated by the kernel. -/

def Chain {S : Type} (R : S → S → Prop) (n : ℕ) :=
  {y : Fin (n + 1) → S // ∀ i : Fin n, R (y i.castSucc) (y i.succ)}

def chainEquiv {S S' : Type} {R : S → S → Prop} {R' : S' → S' → Prop} (e : S ≃ S')
    (h : ∀ a b, R a b ↔ R' (e a) (e b)) (n : ℕ) : Chain R n ≃ Chain R' n where
  toFun y := ⟨fun i => e (y.1 i), fun i => (h _ _).1 (y.2 i)⟩
  invFun y := ⟨fun i => e.symm (y.1 i), fun i => (h _ _).2 (by simpa using y.2 i)⟩
  left_inv y := by apply Subtype.ext; funext i; simp
  right_inv y := by apply Subtype.ext; funext i; simp

section generic
variable {S : Type} [Fintype S] [DecidableEq S] (R : S → S → Prop) [DecidableRel R]

instance (n : ℕ) : Fintype (Chain R n) := by unfold Chain; infer_instance

def V : ℕ → S → ℕ
  | 0, _ => 1
  | n + 1, s => ∑ t, if R s t then V n t else 0

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

theorem cardChain (n : ℕ) : Fintype.card (Chain R n) = ∑ s, V R n s := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun y : Chain R n => y.1 0)), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  exact cardStart R n s

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

theorem rec_total (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) (n : ℕ) :
    ∑ j ∈ Finset.range (m + 1), c j * (∑ s, (V R (n + j) s : ℤ)) = 0 := by
  have h := Finset.sum_eq_zero (s := (Finset.univ : Finset S)) (fun s _ => rec_gen R m c h0 n s)
  rw [Finset.sum_comm] at h
  simpa [Finset.mul_sum] using h
end generic

/-- one transfer step: new[s] = sum of old[t] over the neighbours t of s -/
def stepL (adj : List (List ℕ)) (v : List ℕ) : List ℕ :=
  adj.map fun l => (l.map fun t => v.getD t 0).sum

def iterL (adj : List (List ℕ)) (N : ℕ) : ℕ → List ℕ
  | 0 => List.replicate N 1
  | n + 1 => stepL adj (iterL adj N n)

theorem length_iterL (adj : List (List ℕ)) (N : ℕ) (hlen : adj.length = N) (n : ℕ) :
    (iterL adj N n).length = N := by
  cases n <;> simp [iterL, stepL, hlen]

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
theorem sum_getD (l : List ℕ) (N : ℕ) (h : l.length = N) : ∑ s : Fin N, l.getD s 0 = l.sum := by
  subst h
  rw [← Fin.sum_univ_getElem l]
  apply Finset.sum_congr rfl
  intro i _
  simp [List.getD_eq_getElem?_getD]

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

theorem V_eq_iterL' (N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (adj : List (List ℕ))
    (H : AdjOK N R adj) (n : ℕ) (s : Fin N) :
    V R n s = (iterL adj N n).getD s 0 :=
  V_eq_iterL N R adj H.len H.nodup H.mem H.lt n s

theorem sum_V_eq (N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R] (adj : List (List ℕ))
    (H : AdjOK N R adj) (n : ℕ) :
    ∑ s, V R n s = (iterL adj N n).sum := by
  simp only [V_eq_iterL' N R adj H n]
  exact sum_getD _ N (length_iterL _ N H.len n)

/-- linear combination of the vectors `f j` (j in L) with natural coefficients `c j`, as a list fold -/
def comb (N : ℕ) (c : ℕ → ℕ) (f : ℕ → List ℕ) (L : List ℕ) : List ℕ :=
  L.foldl (fun acc j => List.zipWith (· + ·) acc ((f j).map (c j * ·))) (List.replicate N 0)

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

theorem comb_getD (N : ℕ) (c : ℕ → ℕ) (f : ℕ → List ℕ) (hf : ∀ j, (f j).length = N) (L : List ℕ)
    (s : ℕ) (hs : s < N) :
    (comb N c f L).getD s 0 = (L.map fun j => c j * (f j).getD s 0).sum := by
  unfold comb
  rw [foldl_comb_getD N c f hf L _ (by simp) s hs]
  simp [List.getD_eq_getElem?_getD, hs]

theorem sum_range_eq_list (K : ℕ) (g : ℕ → ℕ) :
    ∑ j ∈ Finset.range K, g j = ((List.range K).map g).sum := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

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

def pack : List ℕ → ℕ
  | [] => 0
  | x :: l => x + 2 ^ 128 * pack l

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

def stepP (adj : List (List ℕ)) (v : ℕ) : ℕ := pack (adj.map fun l => (l.map fun t => dg v t).sum)

def iterP (adj : List (List ℕ)) (N : ℕ) : ℕ → ℕ
  | 0 => pack (List.replicate N 1)
  | n + 1 => stepP adj (iterP adj N n)

def unpackN (N v : ℕ) : List ℕ := (List.range N).map (dg v)

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


abbrev St := Fin 6 → Fin 3
def N : ℕ := 3 ^ 6
def e0 : St ≃ Fin N := finFunctionFinEquiv
def RN : Fin N → Fin N → Prop := fun i j => PairOK (e0.symm i) (e0.symm j)
instance : DecidableRel RN := fun i j => by unfold RN PairOK; infer_instance

def dig (x j : ℕ) : ℕ := x / 3 ^ j % 3
abbrev loc (a b c d : ℕ) : Prop := ¬ (a + d > max b c)
instance (a b c d : ℕ) : Decidable (loc a b c d) := by unfold loc; infer_instance
def tabL : List ℕ := [1718724738078778163505230626077571948145344553005558924024536204497647321413566993093398805145824910093834121663339183827390108268665713473017334658550763677299369049806506288645965899305735415111719254007666416719654711, 1762936306903955736842985754722654184753584927359399668050890833552249181771472253365897809779801113568916671416736976337419435812554220572001703395748210974464626131473554681923032546233214139616200778226513141265497919, 2824013958708217496949108842204627863351353911851577524683401930862693830361198499905873920995229996970897865498283996578123296865878390947626553088486946106430796091482716120572632072492703527723757359478834530365734911, 210004951919593473354336861064140623889141778180743534125184488009358836700049986294370272011386966506642111328639514422639305833470408720175751501687874661534971137918479868066066572905523941396287240039521941592755238, 215531398022740670021556252144775903465171824974973627128478816641184069244788143828432647590633991941027430047814238486392971776456472107548797593837555573680628273126860917225699903771458781959347430566877782160985639, 348166104498273390034821638080022613289892948036495859207542703804989650318503924645929661492562602366275079308007616016480954408121993404501903805429897465176399518128006097056899844553894955472792003223417955798515263, 22105784412588786668877564322541118304120187176920372013177314527300930178952630136249502316988101737541274876698896255014663771944253549492184368598723648582628540833524196638533323463739362252240762109423362272921604, 22105784412588786668877564322541118304120187176920372013177314527300930178952630136249502316988101737541274876698896255014663771944253549492184368598723648582628540833524196638533323463739362252240762109423362272921604, 38685122722030376670535737564446957032210327559610651023060300422776627813167102738436629054729178040697231034223068446275661600902443711611322645047766385019599946458667344117433316061543883941421333691490883977612807, 2476452454234972698180587166443150176557298590052464266063125747779541016895217260574789408736343494140736661447343527814416727267115007941614560001057791362790489111456541802023832388080866989287555032429299509645013503, 2476527863543819138796505700111139214892467619195835737805069830266649533452706082713936964499471913863633203257725593440097722400462537423716103067468602635245173491361082087187327462865942241302837350139659573654716415, 2824013958708217496949108842204627863351353911851577524683401930862693830361198499905873920995229996970897865498283996578123296865878390947626553088486946106430796091482716120572632072492703527723757359478834530365734911, 4836800200228730130399698548359411966701009899060804698132165774694694820181482518761193869408796288911002056537178022195078474868883187919285744005941772288740304814654228064801281136467336292717409391063480622350840, 4836947484035070834727664434429703057199386909106452103878150310802328641582827874501716439258656483682284364760580494120236668488702581439015320307525388055253360244155283309261232454406936394309757667841527622369791, 5515631263653036377994467446331048073720649199449697781374892694778977658982227126829718307414433989751160658199171125249192868616467920352902918004826840147412779385017849780716905520084204531850617061082103709695999, 9426163605805076989816708498629791896128642921433967743010310888564569686102767393444470391052465362067726297758203210124391668441185262692883301351409056835547488067535645436884348134406501910289713795008001212864, 9426163605805076989816708498629791896128642921433967743010310888564569686102767393444470391052465362067726297758203210124391668441185262692883301351409056835547488067535645436884348134406501910289713795008001212864, 10751717862871415941509683131249606381521733332260619456871135857268962298210969058147599039794218303608500308380450536548134246815726940259070015603950955453046353577032845576446209590807416241424204797431001383423, 2818498327485579009303978271816415903147142153554312481811991565317636746867743828113354323920097252332308106950708392016618049621440724372505992186932353673024958371974264791187191978147102960207002432550153816209620991, 2818498327485659115843874140679944874430037161535409807499223518309273654895276742334204254776345890915439402760088455302486868462627436680092807261040818375603130949534963119933122856779810473766646839751924364324372479, 2824013958708217496949108842204627863351353911851577524683401930862693830361198499905873920995229996970897865498283996578123296865878390947626553088486946106430796091482716120572632072492703527723757359478834530365734911, 20999448951226315293756972989188552141918543313901837900657609812750108331166782070928224947794637880639266080636900159579546288758959112422520016251686430656802058442381727321335622151728993347789511451434024448, 20999448951226912133988807854278273905670161937494522510005429744492932259966507500797295081780579280147468870430660215522892452696309566660478917434311610413817261214706247139954000780763061884247261706316677119, 21040543606193492860979170122403412999973090015044514394715163562617317255262522030052846674926934030359441336081364281051675866488345699678121309856914142702455503861368787878532955236860642778755552889184190463, 156458085734118874080022036904312463080714232874908186790835991275223087597521203610622232678312127695436105212536799192797475755498191618095122222993315548238923331896247329506862421180482815958101786624, 156458085734118874080022036904312463080714232874908186790835991275223087597521203610622232678312127695436105212536799192797475755498191618095122222993315548238923331896247329506862421180482815958101786624, 156764264773050159871049301708892816983761437470339811774904666749482233120354182345410170626020158859635013911473381292658258779571107924781839438342114570441401998847475566201339580383308696712902606847, 2824013937667673890755615981225466443112750385609868674340686066456284818310994038447928085237254700297991684286721927239445662034963242524717755189171370196511840462492419702648476853397925203382685407949563318851600383, 2824013937667673890755615981225466443112815221790149372665285665536068073717612109502269507397603828068935946330473401033644766754984503881153051785487244115483570904470571110164653392387586343036002717215061100489342975, 2824013958708217496949108842204627863351353911851577524683401930862693830361198499905873920995229996970897865498283996578123296865878390947626553088486946106430796091482716120572632072492703527723757359478834530365734911, 1167984789409117101662228269196251780174286778990704182692801144198441484224761355091200509362271690290010391496284110464163738166435935469230107827089344389861660431551965392068664903241228615680, 1167984789409117101662228269196251780174313594606364275979780068745629473694309551179273783867896579259242848978930130904408806327372162397871140367327813065673739899278498136156496119385452183551, 1167984798111281975972139931059274579172666497855431550321053061079406020665346644400726844285105933693773825183974729850772861043047284871620675342073639337946383719375064141926802075096836997119, 483067186778026257452361880118067611888580429117546680190621099950835434730900780849938988844017359877352389066472045866626813844974395008210383278587010900060156475736064, 483067186778026257452361880118067611888580429117546680190621099950835434730900780849938988844017359877352389066472045866626813844974395008210383278587010900060156475736064, 483067190377157293086918786574591197813863107791081668069510838521158762262217190655713366117269370944244579910915811775010918979511320792228338885469377085883904398721023, 2824013958708217496949107674219829752069377939711646465408822758196195974929648178852812841589209414256249563552514580461568931395858450962163752503479600806411690499173577987538918932646806416197061997909973791787712511, 2824013958708217496949107674219829752069377939711646465408822758196195974929648178852812841589209414256249563552514580461603107188433185523482072836643537122018259134864904425914723471752090756804600581737491574837739519, 2824013958708217496949108842204627863351353911851577524683401930862693830361198499905873920995229996970897865498283996578123296865878390947626553088486946106430796091482716120572632072492703527723757359478834530365734911, 199791907220223502808422140074766544786835412141144649558606066865438420763447365624827255932005961621254043569738590075900598307906567483674329088, 199791907220223502808422140074766544786835412141144649558606066865438420763447365624827255932005961621254043569738590075903016159545796742023741439, 199791907220223502808422222706762643567910281130558153654986045416023791284464999687699590596063486154228923591770023865308670443474450259602571263, 14134776518227074636666374159936798803008198360265620799840770986610786304, 14134776518227074636666374159936798803008198360265620799840770986610786304, 14134776518227074636666380005943348126619871175004951664972849610340958207]
def tab (j a b : ℕ) : ℕ := tabL.getD ((j * 3 + a) * 3 + b) 0
/-- bitmask (over the 729 states) of the neighbours of s: AND of the per-column-pair masks -/
def mask (s : ℕ) : ℕ := ((List.range 5).map fun j => tab j (dig s j) (dig s (j + 1))).foldl (· &&& ·) (2 ^ N - 1)
def adjLit : List (List ℕ) := [[0, 1, 2, 4, 5, 8, 13, 14, 17, 26, 40, 41, 44, 53, 80, 121, 122, 125, 134, 161, 242, 364, 365, 368, 377, 404, 485, 728], [1, 2, 5, 14, 41, 122, 365], [2], [3, 4, 5, 8, 17, 44, 125, 368], [5], [], [6, 7, 8], [], [], [9, 10, 11, 13, 14, 17, 26, 53, 134, 377], [10, 11, 14], [11], [17], [], [], [], [], [], [18, 19, 20, 22, 23, 26], [19, 20, 23], [20], [], [], [], [], [], [], [27, 28, 29, 31, 32, 35, 40, 41, 44, 53, 80, 161, 404], [28, 29, 32, 41], [29], [30, 31, 32, 35, 44], [32], [], [33, 34, 35], [], [], [53], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [54, 55, 56, 58, 59, 62, 67, 68, 71, 80], [55, 56, 59, 68], [56], [57, 58, 59, 62, 71], [59], [], [60, 61, 62], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [81, 82, 83, 85, 86, 89, 94, 95, 98, 107, 121, 122, 125, 134, 161, 242, 485], [82, 83, 86, 95, 122], [83], [84, 85, 86, 89, 98, 125], [86], [], [87, 88, 89], [], [], [90, 91, 92, 94, 95, 98, 107, 134], [91, 92, 95], [92], [98], [], [], [], [], [], [99, 100, 101, 103, 104, 107], [100, 101, 104], [101], [], [], [], [], [], [], [161], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [162, 163, 164, 166, 167, 170, 175, 176, 179, 188, 202, 203, 206, 215, 242], [163, 164, 167, 176, 203], [164], [165, 166, 167, 170, 179, 206], [167], [], [168, 169, 170], [], [], [171, 172, 173, 175, 176, 179, 188, 215], [172, 173, 176], [173], [179], [], [], [], [], [], [180, 181, 182, 184, 185, 188], [181, 182, 185], [182], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0, 1, 2, 4, 5, 8, 13, 14, 17, 26, 40, 41, 44, 53, 80, 121, 122, 125, 134, 161, 242, 243, 244, 245, 247, 248, 251, 256, 257, 260, 269, 283, 284, 287, 296, 323, 364, 365, 368, 377, 404, 485, 728], [1, 2, 5, 14, 41, 122, 244, 245, 248, 257, 284, 365], [2, 245], [3, 4, 5, 8, 17, 44, 125, 246, 247, 248, 251, 260, 287, 368], [5, 248], [], [6, 7, 8, 249, 250, 251], [], [], [9, 10, 11, 13, 14, 17, 26, 53, 134, 252, 253, 254, 256, 257, 260, 269, 296, 377], [10, 11, 14, 253, 254, 257], [11, 254], [17, 260], [], [], [], [], [], [18, 19, 20, 22, 23, 26, 261, 262, 263, 265, 266, 269], [19, 20, 23, 262, 263, 266], [20, 263], [], [], [], [], [], [], [27, 28, 29, 31, 32, 35, 40, 41, 44, 53, 80, 161, 270, 271, 272, 274, 275, 278, 283, 284, 287, 296, 323, 404], [28, 29, 32, 41, 271, 272, 275, 284], [29, 272], [30, 31, 32, 35, 44, 273, 274, 275, 278, 287], [32, 275], [], [33, 34, 35, 276, 277, 278], [], [], [53, 296], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [54, 55, 56, 58, 59, 62, 67, 68, 71, 80, 297, 298, 299, 301, 302, 305, 310, 311, 314, 323], [55, 56, 59, 68, 298, 299, 302, 311], [56, 299], [57, 58, 59, 62, 71, 300, 301, 302, 305, 314], [59, 302], [], [60, 61, 62, 303, 304, 305], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0, 1, 2, 4, 5, 8, 13, 14, 17, 26, 40, 41, 44, 53, 80, 81, 82, 83, 85, 86, 89, 94, 95, 98, 107, 121, 122, 125, 134, 161, 242, 485], [1, 2, 5, 14, 41, 82, 83, 86, 95, 122], [2, 83], [3, 4, 5, 8, 17, 44, 84, 85, 86, 89, 98, 125], [5, 86], [], [6, 7, 8, 87, 88, 89], [], [], [9, 10, 11, 13, 14, 17, 26, 53, 90, 91, 92, 94, 95, 98, 107, 134], [10, 11, 14, 91, 92, 95], [11, 92], [17, 98], [], [], [], [], [], [18, 19, 20, 22, 23, 26, 99, 100, 101, 103, 104, 107], [19, 20, 23, 100, 101, 104], [20, 101], [], [], [], [], [], [], [0, 1, 2, 4, 5, 8, 13, 14, 17, 26, 27, 28, 29, 31, 32, 35, 40, 41, 44, 53, 80, 161], [1, 2, 5, 14, 28, 29, 32, 41], [2, 29], [3, 4, 5, 8, 17, 30, 31, 32, 35, 44], [5, 32], [], [6, 7, 8, 33, 34, 35], [], [], [0, 1, 2, 4, 5, 8, 9, 10, 11, 13, 14, 17, 26, 53], [1, 2, 5, 10, 11, 14], [2, 11], [0, 1, 2, 3, 4, 5, 8, 17], [0, 1, 2, 5], [2], [6, 7, 8], [], [], [18, 19, 20, 22, 23, 26], [19, 20, 23], [20], [], [], [], [], [], [], [54, 55, 56, 58, 59, 62, 67, 68, 71, 80], [55, 56, 59, 68], [56], [57, 58, 59, 62, 71], [59], [], [60, 61, 62], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [162, 163, 164, 166, 167, 170, 175, 176, 179, 188, 202, 203, 206, 215, 242], [163, 164, 167, 176, 203], [164], [165, 166, 167, 170, 179, 206], [167], [], [168, 169, 170], [], [], [171, 172, 173, 175, 176, 179, 188, 215], [172, 173, 176], [173], [179], [], [], [], [], [], [180, 181, 182, 184, 185, 188], [181, 182, 185], [182], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0, 1, 2, 4, 5, 8, 13, 14, 17, 26, 40, 41, 44, 53, 80, 121, 122, 125, 134, 161, 242, 243, 244, 245, 247, 248, 251, 256, 257, 260, 269, 283, 284, 287, 296, 323, 364, 365, 368, 377, 404, 485, 486, 487, 488, 490, 491, 494, 499, 500, 503, 512, 526, 527, 530, 539, 566, 607, 608, 611, 620, 647, 728], [1, 2, 5, 14, 41, 122, 244, 245, 248, 257, 284, 365, 487, 488, 491, 500, 527, 608], [2, 245, 488], [3, 4, 5, 8, 17, 44, 125, 246, 247, 248, 251, 260, 287, 368, 489, 490, 491, 494, 503, 530, 611], [5, 248, 491], [], [6, 7, 8, 249, 250, 251, 492, 493, 494], [], [], [9, 10, 11, 13, 14, 17, 26, 53, 134, 252, 253, 254, 256, 257, 260, 269, 296, 377, 495, 496, 497, 499, 500, 503, 512, 539, 620], [10, 11, 14, 253, 254, 257, 496, 497, 500], [11, 254, 497], [17, 260, 503], [], [], [], [], [], [18, 19, 20, 22, 23, 26, 261, 262, 263, 265, 266, 269, 504, 505, 506, 508, 509, 512], [19, 20, 23, 262, 263, 266, 505, 506, 509], [20, 263, 506], [], [], [], [], [], [], [27, 28, 29, 31, 32, 35, 40, 41, 44, 53, 80, 161, 270, 271, 272, 274, 275, 278, 283, 284, 287, 296, 323, 404, 513, 514, 515, 517, 518, 521, 526, 527, 530, 539, 566, 647], [28, 29, 32, 41, 271, 272, 275, 284, 514, 515, 518, 527], [29, 272, 515], [30, 31, 32, 35, 44, 273, 274, 275, 278, 287, 516, 517, 518, 521, 530], [32, 275, 518], [], [33, 34, 35, 276, 277, 278, 519, 520, 521], [], [], [53, 296, 539], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [54, 55, 56, 58, 59, 62, 67, 68, 71, 80, 297, 298, 299, 301, 302, 305, 310, 311, 314, 323, 540, 541, 542, 544, 545, 548, 553, 554, 557, 566], [55, 56, 59, 68, 298, 299, 302, 311, 541, 542, 545, 554], [56, 299, 542], [57, 58, 59, 62, 71, 300, 301, 302, 305, 314, 543, 544, 545, 548, 557], [59, 302, 545], [], [60, 61, 62, 303, 304, 305, 546, 547, 548], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0, 1, 2, 4, 5, 8, 13, 14, 17, 26, 40, 41, 44, 53, 80, 81, 82, 83, 85, 86, 89, 94, 95, 98, 107, 121, 122, 125, 134, 161, 242, 243, 244, 245, 247, 248, 251, 256, 257, 260, 269, 283, 284, 287, 296, 323, 324, 325, 326, 328, 329, 332, 337, 338, 341, 350, 364, 365, 368, 377, 404, 485], [1, 2, 5, 14, 41, 82, 83, 86, 95, 122, 244, 245, 248, 257, 284, 325, 326, 329, 338, 365], [2, 83, 245, 326], [3, 4, 5, 8, 17, 44, 84, 85, 86, 89, 98, 125, 246, 247, 248, 251, 260, 287, 327, 328, 329, 332, 341, 368], [5, 86, 248, 329], [], [6, 7, 8, 87, 88, 89, 249, 250, 251, 330, 331, 332], [], [], [9, 10, 11, 13, 14, 17, 26, 53, 90, 91, 92, 94, 95, 98, 107, 134, 252, 253, 254, 256, 257, 260, 269, 296, 333, 334, 335, 337, 338, 341, 350, 377], [10, 11, 14, 91, 92, 95, 253, 254, 257, 334, 335, 338], [11, 92, 254, 335], [17, 98, 260, 341], [], [], [], [], [], [18, 19, 20, 22, 23, 26, 99, 100, 101, 103, 104, 107, 261, 262, 263, 265, 266, 269, 342, 343, 344, 346, 347, 350], [19, 20, 23, 100, 101, 104, 262, 263, 266, 343, 344, 347], [20, 101, 263, 344], [], [], [], [], [], [], [0, 1, 2, 4, 5, 8, 13, 14, 17, 26, 27, 28, 29, 31, 32, 35, 40, 41, 44, 53, 80, 161, 243, 244, 245, 247, 248, 251, 256, 257, 260, 269, 270, 271, 272, 274, 275, 278, 283, 284, 287, 296, 323, 404], [1, 2, 5, 14, 28, 29, 32, 41, 244, 245, 248, 257, 271, 272, 275, 284], [2, 29, 245, 272], [3, 4, 5, 8, 17, 30, 31, 32, 35, 44, 246, 247, 248, 251, 260, 273, 274, 275, 278, 287], [5, 32, 248, 275], [], [6, 7, 8, 33, 34, 35, 249, 250, 251, 276, 277, 278], [], [], [0, 1, 2, 4, 5, 8, 9, 10, 11, 13, 14, 17, 26, 53, 243, 244, 245, 247, 248, 251, 252, 253, 254, 256, 257, 260, 269, 296], [1, 2, 5, 10, 11, 14, 244, 245, 248, 253, 254, 257], [2, 11, 245, 254], [0, 1, 2, 3, 4, 5, 8, 17, 243, 244, 245, 246, 247, 248, 251, 260], [0, 1, 2, 5, 243, 244, 245, 248], [2, 245], [6, 7, 8, 249, 250, 251], [], [], [18, 19, 20, 22, 23, 26, 261, 262, 263, 265, 266, 269], [19, 20, 23, 262, 263, 266], [20, 263], [], [], [], [], [], [], [54, 55, 56, 58, 59, 62, 67, 68, 71, 80, 297, 298, 299, 301, 302, 305, 310, 311, 314, 323], [55, 56, 59, 68, 298, 299, 302, 311], [56, 299], [57, 58, 59, 62, 71, 300, 301, 302, 305, 314], [59, 302], [], [60, 61, 62, 303, 304, 305], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [0, 1, 2, 4, 5, 8, 13, 14, 17, 26, 40, 41, 44, 53, 80, 81, 82, 83, 85, 86, 89, 94, 95, 98, 107, 121, 122, 125, 134, 161, 162, 163, 164, 166, 167, 170, 175, 176, 179, 188, 202, 203, 206, 215, 242], [1, 2, 5, 14, 41, 82, 83, 86, 95, 122, 163, 164, 167, 176, 203], [2, 83, 164], [3, 4, 5, 8, 17, 44, 84, 85, 86, 89, 98, 125, 165, 166, 167, 170, 179, 206], [5, 86, 167], [], [6, 7, 8, 87, 88, 89, 168, 169, 170], [], [], [9, 10, 11, 13, 14, 17, 26, 53, 90, 91, 92, 94, 95, 98, 107, 134, 171, 172, 173, 175, 176, 179, 188, 215], [10, 11, 14, 91, 92, 95, 172, 173, 176], [11, 92, 173], [17, 98, 179], [], [], [], [], [], [18, 19, 20, 22, 23, 26, 99, 100, 101, 103, 104, 107, 180, 181, 182, 184, 185, 188], [19, 20, 23, 100, 101, 104, 181, 182, 185], [20, 101, 182], [], [], [], [], [], [], [0, 1, 2, 4, 5, 8, 13, 14, 17, 26, 27, 28, 29, 31, 32, 35, 40, 41, 44, 53, 80, 81, 82, 83, 85, 86, 89, 94, 95, 98, 107, 108, 109, 110, 112, 113, 116, 121, 122, 125, 134, 161], [1, 2, 5, 14, 28, 29, 32, 41, 82, 83, 86, 95, 109, 110, 113, 122], [2, 29, 83, 110], [3, 4, 5, 8, 17, 30, 31, 32, 35, 44, 84, 85, 86, 89, 98, 111, 112, 113, 116, 125], [5, 32, 86, 113], [], [6, 7, 8, 33, 34, 35, 87, 88, 89, 114, 115, 116], [], [], [0, 1, 2, 4, 5, 8, 9, 10, 11, 13, 14, 17, 26, 53, 81, 82, 83, 85, 86, 89, 90, 91, 92, 94, 95, 98, 107, 134], [1, 2, 5, 10, 11, 14, 82, 83, 86, 91, 92, 95], [2, 11, 83, 92], [0, 1, 2, 3, 4, 5, 8, 17, 81, 82, 83, 84, 85, 86, 89, 98], [0, 1, 2, 5, 81, 82, 83, 86], [2, 83], [6, 7, 8, 87, 88, 89], [], [], [18, 19, 20, 22, 23, 26, 99, 100, 101, 103, 104, 107], [19, 20, 23, 100, 101, 104], [20, 101], [], [], [], [], [], [], [0, 1, 2, 4, 5, 8, 13, 14, 17, 26, 27, 28, 29, 31, 32, 35, 40, 41, 44, 53, 54, 55, 56, 58, 59, 62, 67, 68, 71, 80], [1, 2, 5, 14, 28, 29, 32, 41, 55, 56, 59, 68], [2, 29, 56], [3, 4, 5, 8, 17, 30, 31, 32, 35, 44, 57, 58, 59, 62, 71], [5, 32, 59], [], [6, 7, 8, 33, 34, 35, 60, 61, 62], [], [], [0, 1, 2, 4, 5, 8, 9, 10, 11, 13, 14, 17, 26, 27, 28, 29, 31, 32, 35, 36, 37, 38, 40, 41, 44, 53], [1, 2, 5, 10, 11, 14, 28, 29, 32, 37, 38, 41], [2, 11, 29, 38], [0, 1, 2, 3, 4, 5, 8, 17, 27, 28, 29, 30, 31, 32, 35, 44], [0, 1, 2, 5, 27, 28, 29, 32], [2, 29], [6, 7, 8, 33, 34, 35], [], [], [0, 1, 2, 4, 5, 8, 9, 10, 11, 13, 14, 17, 18, 19, 20, 22, 23, 26], [1, 2, 5, 10, 11, 14, 19, 20, 23], [2, 11, 20], [0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 14, 17], [0, 1, 2, 5, 9, 10, 11, 14], [2, 11], [0, 1, 2, 3, 4, 5, 6, 7, 8], [0, 1, 2, 3, 4, 5], [0, 1, 2]]

theorem tab_ok : ∀ j < 5, ∀ a < 3, ∀ b < 3, ∀ t < N,
    ((tab j a b).testBit t = true ↔ loc a b (dig t j) (dig t (j + 1))) := by decide +kernel

theorem RN_iff (s t : Fin N) :
    RN s t ↔ ∀ j < 5, loc (dig s j) (dig s (j + 1)) (dig t j) (dig t (j + 1)) := by
  constructor
  · intro h j hj
    exact h ⟨j, hj⟩
  · intro h j
    exact h j.1 j.2

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

theorem hAdj : AdjOK N RN adjLit :=
  adjOK_of_mask _ RN mask adjLit hR (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem a_eq (n : ℕ) : a n = ∑ s, V RN n s := by
  show Nat.card (Chain PairOK n) = _
  rw [Nat.card_congr (chainEquiv e0 (R' := RN) (fun a b => by simp [RN]) n), Nat.card_eq_fintype_card, cardChain]

def Dg : ℕ := 63
theorem hDg : ∀ l ∈ adjLit, l.length ≤ Dg := by
  intro l hl
  revert l
  decide +kernel
theorem hKb : Dg ^ 11 < 2 ^ 128 := by decide +kernel
theorem hlenA : adjLit.length = N := by decide +kernel

theorem a_iter (n : ℕ) : a n = (iterL adjLit N n).sum := by
  rw [a_eq, sum_V_eq _ RN adjLit hAdj]

def cpf : ℕ → ℕ := fun j => [0, 0, 0, 0, 2, 0, 14, 0, 0, 13, 0, 1].getD j 0
def cnf : ℕ → ℕ := fun j => [0, 0, 0, 0, 0, 9, 0, 5, 10, 0, 6, 0].getD j 0

theorem chk : comb N cpf (fun j => unpackN N (iterP adjLit N j)) (List.range (11 + 1)) =
    comb N cnf (fun j => unpackN N (iterP adjLit N j)) (List.range (11 + 1)) := by
  decide +kernel

def cc : ℕ → ℤ := fun j => (cpf j : ℤ) - cnf j

theorem hrec (k : ℕ) : (a (k + 11) : ℤ) = (-2 : ℤ) * a (k + 4) + (9 : ℤ) * a (k + 5) + (-14 : ℤ) * a (k + 6) + (5 : ℤ) * a (k + 7) + (10 : ℤ) * a (k + 8) + (-13 : ℤ) * a (k + 9) + (6 : ℤ) * a (k + 10) := by
  have h := rec_total RN 11 cc (h0_of_chkP _ RN adjLit hAdj Dg hDg (by decide +kernel) 11 hKb 11 (by omega) cpf cnf chk) k
  have e0 : cc 0 = 0 := by simp [cc, cpf, cnf]
  have e1 : cc 1 = 0 := by simp [cc, cpf, cnf]
  have e2 : cc 2 = 0 := by simp [cc, cpf, cnf]
  have e3 : cc 3 = 0 := by simp [cc, cpf, cnf]
  have e4 : cc 4 = 2 := by simp [cc, cpf, cnf]
  have e5 : cc 5 = -9 := by simp [cc, cpf, cnf]
  have e6 : cc 6 = 14 := by simp [cc, cpf, cnf]
  have e7 : cc 7 = -5 := by simp [cc, cpf, cnf]
  have e8 : cc 8 = -10 := by simp [cc, cpf, cnf]
  have e9 : cc 9 = 13 := by simp [cc, cpf, cnf]
  have e10 : cc 10 = -6 := by simp [cc, cpf, cnf]
  have e11 : cc 11 = 1 := by simp [cc, cpf, cnf]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] at h
  simp only [a_eq]
  push_cast
  simp only [Nat.add_zero, zero_mul, zero_add] at h ⊢
  linarith

theorem v1 : a 1 = 2129 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 11 hKb 1 (by omega)]
  decide +kernel
theorem v2 : a 2 = 4786 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 11 hKb 2 (by omega)]
  decide +kernel
theorem v3 : a 3 = 8050 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 11 hKb 3 (by omega)]
  decide +kernel
theorem v4 : a 4 = 14753 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 11 hKb 4 (by omega)]
  decide +kernel
theorem v5 : a 5 = 25597 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 11 hKb 5 (by omega)]
  decide +kernel
theorem v6 : a 6 = 46023 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 11 hKb 6 (by omega)]
  decide +kernel
theorem v7 : a 7 = 82431 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 11 hKb 7 (by omega)]
  decide +kernel
theorem v8 : a 8 = 151567 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 11 hKb 8 (by omega)]
  decide +kernel
theorem v9 : a 9 = 282371 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 11 hKb 9 (by omega)]
  decide +kernel
theorem v10 : a 10 = 536601 := by
  rw [a_iter, ← unpack_iterP adjLit N Dg hlenA hDg (by decide +kernel) 11 hKb 10 (by omega)]
  decide +kernel

theorem closed (n : ℕ) (hn : 4 ≤ n) : (a n : ℚ) = (2 * (5472 + 1058 * (-1 : ℚ) ^ n + 2809 * (2 : ℚ) ^ n) + 6142 * (n : ℚ) + 1759 * (n : ℚ) ^ 2 + 266 * (n : ℚ) ^ 3 + 17 * (n : ℚ) ^ 4) / 12 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ 10
    · interval_cases n
      · rw [v4]; norm_num
      · rw [v5]; norm_num
      · rw [v6]; norm_num
      · rw [v7]; norm_num
      · rw [v8]; norm_num
      · rw [v9]; norm_num
      · rw [v10]; norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
      have r : (a (k + 11) : ℚ) = (-2 : ℚ) * a (k + 4) + (9 : ℚ) * a (k + 5) + (-14 : ℚ) * a (k + 6) + (5 : ℚ) * a (k + 7) + (10 : ℚ) * a (k + 8) + (-13 : ℚ) * a (k + 9) + (6 : ℚ) * a (k + 10) := by exact_mod_cast hrec k
      have i4 := ih (k + 4) (by omega) (by omega)
      have i5 := ih (k + 5) (by omega) (by omega)
      have i6 := ih (k + 6) (by omega) (by omega)
      have i7 := ih (k + 7) (by omega) (by omega)
      have i8 := ih (k + 8) (by omega) (by omega)
      have i9 := ih (k + 9) (by omega) (by omega)
      have i10 := ih (k + 10) (by omega) (by omega)
      rw [r, i4, i5, i6, i7, i8, i9, i10]
      push_cast
      ring

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  apply gf_gen _ 7 10 (fun j => [(1 : ℚ), (-6 : ℚ), (13 : ℚ), (-10 : ℚ), (-5 : ℚ), (14 : ℚ), (-9 : ℚ), (2 : ℚ)].getD j 0) (fun j => [(0 : ℚ), (2129 : ℚ), (-7988 : ℚ), (7011 : ℚ), (7381 : ℚ), (-16776 : ℚ), (9606 : ℚ), (-883 : ℚ), (-571 : ℚ), (21 : ℚ), (2 : ℚ)].getD j 0)
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
    ring
  · norm_num
  · intro n hn
    simp only [List.getD_eq_getElem?_getD]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp_all
  · intro n
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
    · simp [Finset.sum_range_succ]
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
    · simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
    · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      have c0 := closed (k + 11) (by omega)
      have c1 := closed (k + 10) (by omega)
      have c2 := closed (k + 9) (by omega)
      have c3 := closed (k + 8) (by omega)
      have c4 := closed (k + 7) (by omega)
      have c5 := closed (k + 6) (by omega)
      have c6 := closed (k + 5) (by omega)
      have c7 := closed (k + 4) (by omega)
      simp [c0, c1, c2, c3, c4, c5, c6, c7]
      ring


theorem rec7 (n : ℕ) (hn : 11 ≤ n) : (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 13 * (a (n - 2) : ℤ) + 10 * (a (n - 3) : ℤ) + 5 * (a (n - 4) : ℤ) - 14 * (a (n - 5) : ℤ) + 9 * (a (n - 6) : ℤ) - 2 * (a (n - 7) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
  have e1 : k + 11 - 1 = k + 10 := by omega
  have e2 : k + 11 - 2 = k + 9 := by omega
  have e3 : k + 11 - 3 = k + 8 := by omega
  have e4 : k + 11 - 4 = k + 7 := by omega
  have e5 : k + 11 - 5 = k + 6 := by omega
  have e6 : k + 11 - 6 = k + 5 := by omega
  have e7 : k + 11 - 7 = k + 4 := by omega
  rw [e1, e2, e3, e4, e5, e6, e7]
  have h : (a (k + 11) : ℚ) = 6 * (a (k + 10) : ℚ) - 13 * (a (k + 9) : ℚ) + 10 * (a (k + 8) : ℚ) + 5 * (a (k + 7) : ℚ) - 14 * (a (k + 6) : ℚ) + 9 * (a (k + 5) : ℚ) - 2 * (a (k + 4) : ℚ) := by
    rw [closed (k + 11) (by omega), closed (k + 10) (by omega), closed (k + 9) (by omega), closed (k + 8) (by omega), closed (k + 7) (by omega), closed (k + 6) (by omega), closed (k + 5) (by omega), closed (k + 4) (by omega)]
    push_cast
    ring_nf
  exact_mod_cast h

end OMA.S_oeis_a251134

theorem OMA.solution : type_of% @OMA.S_oeis_a251134.main := ⟨OMA.S_oeis_a251134.rec7, OMA.S_oeis_a251134.gf, OMA.S_oeis_a251134.closed⟩

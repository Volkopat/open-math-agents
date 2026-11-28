import FormalConjectures.ErdosProblems.«78»

/-! Xin Li's two-source disperser on w-bit strings hits both colors on
rectangles whose sides have cardinality polynomial in w (arXiv:2303.06802).
Embed arbitrary vertex sets into the next binary cube and orient each queried
edge by its smaller endpoint. The ordered splitting lemma and final clique
argument follow the project's earlier reduction for the Cohen variant. -/
open Filter Real ComplexityTheory Erdos78

namespace OMA.R_Erdos78_erdos_78_variants_li_R1

def H1 : Prop :=
  ∃ D : ℕ, ∃ f : List Bool × ℕ × ℕ → Bool, IsPolyTime f ∧
    ∀ᶠ w : ℕ in atTop, ∀ A B : Finset ℕ,
      (∀ a ∈ A, a < 2^w) → (∀ b ∈ B, b < 2^w) →
      w^D ≤ A.card → w^D ≤ B.card →
      ∀ c : Bool, ∃ u ∈ A, ∃ v ∈ B, f (List.replicate w true,u,v) = c

def H2 : Prop :=
  ∀ f : List Bool × ℕ × ℕ → Bool, IsPolyTime f →
    ∃ g : List Bool × ℕ × ℕ → Bool, IsPolyTime g ∧ ∀ s u v,
      g (s,u,v) = f (List.replicate (Nat.log 2 s.length + 1) true, min u v, max u v)

lemma ordered_rectangles {n m k : ℕ} (s : Finset (Fin n)) (hs : s.card = m)
    (hm : 2 * k ≤ m) :
    ∃ A B : Finset (Fin n), A ⊆ s ∧ B ⊆ s ∧ A.card = k ∧ B.card = k ∧
      ∀ u ∈ A, ∀ v ∈ B, u < v := by
  let e := s.orderEmbOfFin hs
  let lo (i : Fin k) : Fin m := ⟨i.val, by have := i.isLt; omega⟩
  let hi (i : Fin k) : Fin m := ⟨k + i.val, by have := i.isLt; omega⟩
  have hlo : Function.Injective lo := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin m => x.val) h)
  have hhi : Function.Injective hi := by
    intro i j h
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg (fun x : Fin m => x.val) h)
  let a : Fin k ↪ Fin n := ⟨e ∘ lo, e.injective.comp hlo⟩
  let b : Fin k ↪ Fin n := ⟨e ∘ hi, e.injective.comp hhi⟩
  refine ⟨Finset.univ.map a, Finset.univ.map b, ?_, ?_, by simp, by simp, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact s.orderEmbOfFin_mem hs (lo i)
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    exact s.orderEmbOfFin_mem hs (hi i)
  · intro u hu v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hv
    change e (lo i) < e (hi j)
    apply e.strictMono
    change i.val < k + j.val
    have := i.isLt
    omega


lemma threshold (D : ℕ) : ∀ᶠ n : ℕ in atTop,
    2 * (Nat.log 2 n + 1)^D ≤ ⌈(log n) ^ ((2*D+1:ℕ):ℝ)⌉₊ := by
  have grow : Tendsto (fun n : ℕ => log n) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [grow.eventually_ge_atTop (max 2 (1 / log 2 + 1))] with n hn
  let L := log (n:ℝ)
  have hL : 2 ≤ L := (le_max_left ..).trans hn
  have hlarge : 1 / log 2 + 1 ≤ L := (le_max_right ..).trans hn
  have hlog := Real.natLog_le_logb n 2
  have hw : (Nat.log 2 n : ℝ) ≤ L * (1 / log 2) := by simpa [Real.logb,L,div_eq_mul_inv] using hlog
  have hs : (Nat.log 2 n : ℝ) + 1 ≤ L^2 := by
    nlinarith [mul_nonneg (show 0 ≤ L by linarith) (sub_nonneg.mpr hlarge)]
  rw [Real.rpow_natCast]
  apply (Nat.cast_le (α := ℝ)).mp
  refine le_trans ?_ (Nat.le_ceil _)
  push_cast
  change 2 * ((Nat.log 2 n : ℝ) + 1)^D ≤ L^(2*D+1)
  rw [pow_succ, pow_mul]
  calc
    _ ≤ 2 * (L^2)^D := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hL) (show 0 ≤ (L^2)^D by positivity)]

theorem main : H1 → H2 → type_of% @Erdos78.erdos_78.variants.li := by
  intro h₁ h₂
  obtain ⟨D,f,hf,rect⟩ := h₁
  obtain ⟨g,hg,hsort⟩ := h₂ f hf
  obtain ⟨w₀,rect⟩ := eventually_atTop.mp rect
  refine ⟨((2*D+1:ℕ):ℝ),by positivity,g,hg,?_⟩
  filter_upwards [eventually_ge_atTop (2^w₀),threshold D] with n hn hsize
  let w := Nat.log 2 n + 1
  let k := w^D
  let m := ⌈(log n) ^ ((2*D+1:ℕ):ℝ)⌉₊
  have hw0 : w₀ ≤ w := (Nat.le_log_of_pow_le (by decide) hn).trans (Nat.le_succ _)
  have hnw : n ≤ 2^w := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  change 2*k ≤ m at hsize
  have hrectn (A B : Finset (Fin n)) (hA : k ≤ A.card) (hB : k ≤ B.card) (c : Bool) :
      ∃ u ∈ A, ∃ v ∈ B, f (List.replicate w true,u.val,v.val) = c := by
    let e : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
    have bound (T : Finset (Fin n)) : ∀ u ∈ T.map e, u < 2^w := by
      intro u hu
      obtain ⟨v,_,rfl⟩ := Finset.mem_map.mp hu
      exact v.isLt.trans_le hnw
    obtain ⟨u,hu,v,hv,eq⟩ := rect w hw0 (A.map e) (B.map e) (bound A) (bound B)
      (by simpa using hA) (by simpa using hB) c
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hv
    exact ⟨a,ha,b,hb,eq⟩
  have hadj (u v : Fin n) (huv : u < v) :
      (explicitGraph g n).Adj u v ↔ f (List.replicate w true, u.val, v.val) = true := by
    have hval : u.val ≤ v.val := huv.le
    simp [w,explicitGraph, hsort, min_eq_left hval, max_eq_right hval,
      min_eq_right hval, max_eq_left hval, huv.ne]
  change (explicitGraph g n).CliqueFree m ∧ (explicitGraph g n)ᶜ.CliqueFree m
  constructor
  · intro s hs
    obtain ⟨A, B, hA, hB, hAk, hBk, hlt⟩ := ordered_rectangles s hs.card_eq hsize
    obtain ⟨u, hu, v, hv, hfalse⟩ := hrectn A B hAk.ge hBk.ge false
    have huv := hlt u hu v hv
    have htrue := (hadj u v huv).mp (hs.isClique (hA hu) (hB hv) huv.ne)
    rw [hfalse] at htrue
    contradiction
  · intro s hs
    obtain ⟨A, B, hA, hB, hAk, hBk, hlt⟩ := ordered_rectangles s hs.card_eq hsize
    obtain ⟨u, hu, v, hv, htrue⟩ := hrectn A B hAk.ge hBk.ge true
    have huv := hlt u hu v hv
    have hnAdj := (SimpleGraph.compl_adj _ _ _).mp (hs.isClique (hA hu) (hB hv) huv.ne)
    exact hnAdj.2 ((hadj u v huv).mpr htrue)

end OMA.R_Erdos78_erdos_78_variants_li_R1

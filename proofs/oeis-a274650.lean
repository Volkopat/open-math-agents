import OMAStatements.S_oeis_a274650

open Finset

namespace A274650Proof
open OMA.S_oeis_a274650

lemma mex_not_mem (s : Finset ℕ) : mex s ∉ s := by
  unfold mex
  exact Nat.find_spec (p := fun m => m ∉ s) _

lemma mem_of_lt_mex (s : Finset ℕ) {m : ℕ} (h : m < mex s) : m ∈ s := by
  by_contra hn
  unfold mex at h
  exact Nat.find_min _ h hn

lemma previous_iff (n k r c : ℕ) : (r,c) ∈ previous n k ↔
    c ≤ r ∧ (r < n ∨ r = n ∧ c < k) ∧ attacks n k r c := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, h⟩

lemma different {n k r c : ℕ} (h : (r,c) ∈ previous n k) :
    triangle r c ≠ triangle n k := by
  intro heq
  have hm := mex_not_mem ((previous n k).attach.image fun p => triangle p.val.1 p.val.2)
  apply hm
  rw [← triangle.eq_1, ← heq]
  exact mem_image.mpr ⟨⟨(r,c),h⟩, by simp, rfl⟩

lemma blocker {n k m : ℕ} (h : m < triangle n k) :
    ∃ r c, (r,c) ∈ previous n k ∧ triangle r c = m := by
  rw [triangle.eq_1] at h
  obtain ⟨p, _, hp⟩ := mem_image.mp (mem_of_lt_mex _ h)
  exact ⟨p.val.1, p.val.2, p.property, hp⟩

lemma attacks_symm {n k r c : ℕ} (h : attacks n k r c) : attacks r c n k := by
  unfold attacks at *
  omega

lemma same_cell {n k r c : ℕ} (hk : k ≤ n) (hc : c ≤ r)
    (he : triangle n k = triangle r c) (ha : attacks n k r c) : n = r ∧ k = c := by
  by_contra h
  rcases lt_trichotomy n r with hnr | hnr | hnr
  · exact different ((previous_iff r c n k).mpr ⟨hk, Or.inl hnr, attacks_symm ha⟩) he
  · subst r
    rcases lt_trichotomy k c with hkc | hkc | hkc
    · exact different ((previous_iff n c n k).mpr ⟨hk, Or.inr ⟨rfl,hkc⟩, attacks_symm ha⟩) he
    · exact h ⟨rfl,hkc⟩
    · exact different ((previous_iff n k n c).mpr ⟨hc, Or.inr ⟨rfl,hkc⟩, ha⟩) he.symm
  · exact different ((previous_iff n k r c).mpr ⟨hc, Or.inl hnr, ha⟩) he.symm

lemma column_injective (c : ℕ) : Function.Injective (fun t => triangle (c+t) c) := by
  intro i j h
  have := same_cell (by omega) (by omega) h (Or.inr (Or.inl rfl))
  omega

lemma diagonal_injective (d : ℕ) : Function.Injective (fun t => triangle (d+t) t) := by
  intro i j h
  have := same_cell (by omega) (by omega) h (Or.inr (Or.inr (Or.inl (by omega))))
  omega

lemma bound_unique (P : ℕ → Prop) (h : ∀ i j, P i → P j → i = j) :
    ∃ B, ∀ i, P i → i < B := by
  classical
  by_cases he : ∃ i, P i
  · obtain ⟨i,hi⟩ := he
    exact ⟨i+1, fun j hj => by have := h j i hj hi; omega⟩
  · exact ⟨0, fun i hi => False.elim (he ⟨i,hi⟩)⟩

lemma finite_strip (P : ℕ → ℕ → Prop)
    (h : ∀ l i j, P l i → P l j → i = j) (c : ℕ) :
    ∃ B, ∀ l ≤ c, ∀ i, P l i → i < B := by
  induction c with
  | zero =>
    obtain ⟨B,hB⟩ := bound_unique (P 0) (h 0)
    refine ⟨B, fun l hl i hi => hB i ?_⟩
    have he : l = 0 := by omega
    simpa only [he] using hi
  | succ c ih =>
    obtain ⟨B,hB⟩ := ih
    obtain ⟨C,hC⟩ := bound_unique (P (c+1)) (h (c+1))
    refine ⟨max B C, fun l hl i hi => ?_⟩
    by_cases hc : l ≤ c
    · exact lt_of_lt_of_le (hB l hc i hi) (le_max_left _ _)
    · have he : l = c+1 := by omega
      subst l
      exact lt_of_lt_of_le (hC i hi) (le_max_right _ _)

lemma eventually_large (f : ℕ → ℕ) (hf : Function.Injective f) (m : ℕ) :
    ∃ B, ∀ i ≥ B, m < f i := by
  obtain ⟨B,hB⟩ := finite_strip (fun l i => f i = l)
    (fun l i j hi hj => hf (hi.trans hj.symm)) m
  refine ⟨B, fun i hi => ?_⟩
  by_contra hn
  have := hB (f i) (by omega) i rfl
  omega

lemma column_strip (m c : ℕ) : ∃ B, ∀ r k, k ≤ r → k ≤ c → triangle r k = m → r < B := by
  obtain ⟨B,hB⟩ := finite_strip (fun k r => k ≤ r ∧ triangle r k = m)
    (fun k r s hr hs => (same_cell hr.1 hs.1 (hr.2.trans hs.2.symm)
      (Or.inr (Or.inl rfl))).1) c
  exact ⟨B, fun r k hkr hkc he => hB k hkc r ⟨hkr,he⟩⟩

lemma diagonal_strip (m d : ℕ) : ∃ B, ∀ r k, k ≤ r → r-k ≤ d → triangle r k = m → r < B := by
  obtain ⟨B,hB⟩ := finite_strip (fun l r => ∃ k, k ≤ r ∧ r-k = l ∧ triangle r k = m)
    (fun l r s hr hs => by
      obtain ⟨k,hk,hkl,hkm⟩ := hr
      obtain ⟨c,hc,hcl,hcm⟩ := hs
      exact (same_cell hk hc (hkm.trans hcm.symm) (Or.inr (Or.inr (Or.inl (by omega))))).1) d
  exact ⟨B, fun r k hkr hkd he => hB (r-k) hkd r ⟨k,hkr,rfl,he⟩⟩

lemma sum_injective_min (q : ℕ) (f : ℕ → ℕ) (hf : Set.InjOn f (range q)) :
    (∑ i ∈ range q, (i : ℤ)) ≤ ∑ i ∈ range q, (f i : ℤ) := by
  have hi : Set.InjOn (fun i => (f i : ℤ)) (range q) := by
    intro i hi j hj hij
    change (f i : ℤ) = (f j : ℤ) at hij
    exact hf hi hj (by exact_mod_cast hij)
  have hc : ((range q).image fun i => (f i : ℤ)).card = q := by
    rw [card_image_of_injOn hi, card_range]
  have hs := Finset.sum_range_le_sum (s := (range q).image fun i => (f i : ℤ))
    (c := 0) (by intro x hx; obtain ⟨i,_,rfl⟩ := mem_image.mp hx; exact Nat.cast_nonneg _)
  rw [hc, Finset.sum_image hi] at hs
  simpa only [zero_add] using hs

lemma impossible_packing (B : ℕ) (r c : ℕ → ℕ)
    (hv : ∀ i < 2*B+2, c i ≤ r i)
    (hr : ∀ i < 2*B+2, r i ≤ B+i)
    (hc : Set.InjOn c (range (2*B+2)))
    (hd : Set.InjOn (fun i => r i-c i) (range (2*B+2))) : False := by
  let q := 2*B+2
  have h1 := sum_injective_min q c hc
  have h2 := sum_injective_min q (fun i => r i-c i) hd
  have h3 : (∑ i ∈ range q, (c i : ℤ)) + (∑ i ∈ range q, ((r i-c i : ℕ) : ℤ)) ≤
      (q : ℤ)*B + ∑ i ∈ range q, (i : ℤ) := by
    rw [← sum_add_distrib]
    calc
      _ ≤ ∑ i ∈ range q, ((B : ℤ) + i) := by
        apply sum_le_sum
        intro i hi
        have hvi := hv i (mem_range.mp hi)
        have hri := hr i (mem_range.mp hi)
        rw [Nat.cast_sub hvi]
        have hri' : (r i : ℤ) ≤ (B : ℤ)+i := by exact_mod_cast hri
        omega
      _ = _ := by simp [sum_add_distrib, mul_comm]
  have h4 : (∑ i ∈ range q, (i : ℤ))*2 = (q : ℤ)*(q-1) := by
    have hq : 1 ≤ q := by dsimp [q]; omega
    have ht := Finset.sum_range_id_mul_two q
    have ht' := congrArg (fun n : ℕ => (n : ℤ)) ht
    simpa [Nat.cast_sub hq] using ht'
  have hq : (q : ℤ) = 2*(B : ℤ)+2 := by simp [q]
  nlinarith

lemma column_blocker (m c R n : ℕ)
    (missing : ∀ t, triangle (c+t) c ≠ m)
    (strip : ∀ r k, k ≤ r → k ≤ c → triangle r k = m → r < R)
    (hn : R+c+1 ≤ n) (hm : m < triangle n c) :
    ∃ r k, k ≤ r ∧ r ≤ n ∧ triangle r k = m ∧ n+c = r+k := by
  obtain ⟨r,k,hprev,he⟩ := blocker hm
  obtain ⟨hv,hprior,ha⟩ := (previous_iff n c r k).mp hprev
  have hrn : r ≤ n := by omega
  have hkc : k ≠ c := by
    intro heq
    subst k
    exact missing (r-c) (by simpa [Nat.add_sub_of_le hv] using he)
  have hkc' : c < k := by
    by_contra h
    have hr := strip r k hv (by omega) he
    unfold attacks at ha
    omega
  refine ⟨r,k,hv,hrn,he,?_⟩
  unfold attacks at ha
  omega

lemma diagonal_blocker (m d R n : ℕ)
    (missing : ∀ t, triangle (d+t) t ≠ m)
    (strip : ∀ r k, k ≤ r → r-k ≤ d → triangle r k = m → r < R)
    (hn : 2*R+d+1 ≤ n) (hm : m < triangle n (n-d)) :
    ∃ r k, k ≤ r ∧ r ≤ n ∧ triangle r k = m ∧ r = n := by
  obtain ⟨r,k,hprev,he⟩ := blocker hm
  obtain ⟨hv,hprior,ha⟩ := (previous_iff n (n-d) r k).mp hprev
  have hrn : r ≤ n := by omega
  have hdiff : r-k ≠ d := by
    intro hd
    apply missing k
    have heq : d+k = r := by omega
    simpa only [heq] using he
  have hdiff' : d < r-k := by
    by_contra h
    have hr := strip r k hv (by omega) he
    unfold attacks at ha
    omega
  refine ⟨r,k,hv,hrn,he,?_⟩
  unfold attacks at ha
  omega

lemma column_surjective (c : ℕ) : Function.Surjective (fun t => triangle (c+t) c) := by
  classical
  intro m
  by_contra missing
  have hmiss : ∀ t, triangle (c+t) c ≠ m := by simpa only [not_exists] using missing
  obtain ⟨R,hR⟩ := column_strip m c
  obtain ⟨L,hL⟩ := eventually_large (fun t => triangle (c+t) c) (column_injective c) m
  let B := R+c+L+c+1
  have hb : ∀ i, ∃ r k, k ≤ r ∧ r ≤ B+i ∧ triangle r k = m ∧ B+i+c = r+k := by
    intro i
    apply column_blocker m c R (B+i) hmiss hR (by dsimp [B]; omega)
    have h := hL (B+i-c) (by dsimp [B]; omega)
    have heq : c+(B+i-c) = B+i := by dsimp [B]; omega
    simpa only [heq] using h
  choose r k hv hr hm he using hb
  have hk : Function.Injective k := by
    intro i j hij
    have hh := same_cell (hv i) (hv j) ((hm i).trans (hm j).symm) (Or.inr (Or.inl hij))
    have h1 := he i
    have h2 := he j
    omega
  have hd : Function.Injective (fun i => r i-k i) := by
    intro i j hij
    change r i-k i = r j-k j at hij
    have hh := same_cell (hv i) (hv j) ((hm i).trans (hm j).symm)
      (Or.inr (Or.inr (Or.inl (by have := hv i; have := hv j; omega))))
    have h1 := he i
    have h2 := he j
    omega
  exact impossible_packing B r k (fun i _ => hv i) (fun i _ => hr i) hk.injOn hd.injOn

lemma diagonal_surjective (d : ℕ) : Function.Surjective (fun t => triangle (d+t) t) := by
  classical
  intro m
  by_contra missing
  have hmiss : ∀ t, triangle (d+t) t ≠ m := by simpa only [not_exists] using missing
  obtain ⟨R,hR⟩ := diagonal_strip m d
  obtain ⟨L,hL⟩ := eventually_large (fun t => triangle (d+t) t) (diagonal_injective d) m
  let B := 2*R+d+L+d+1
  have hb : ∀ i, ∃ r k, k ≤ r ∧ r ≤ B+i ∧ triangle r k = m ∧ r = B+i := by
    intro i
    apply diagonal_blocker m d R (B+i) hmiss hR (by dsimp [B]; omega)
    have h := hL (B+i-d) (by dsimp [B]; omega)
    have heq : d+(B+i-d) = B+i := by dsimp [B]; omega
    simpa only [heq] using h
  choose r k hv hr hm he using hb
  have hk : Function.Injective k := by
    intro i j hij
    have hh := same_cell (hv i) (hv j) ((hm i).trans (hm j).symm) (Or.inr (Or.inl hij))
    have h1 := he i
    have h2 := he j
    omega
  have hd : Function.Injective (fun i => r i-k i) := by
    intro i j hij
    change r i-k i = r j-k j at hij
    have hh := same_cell (hv i) (hv j) ((hm i).trans (hm j).symm)
      (Or.inr (Or.inr (Or.inl (by have := hv i; have := hv j; omega))))
    have h1 := he i
    have h2 := he j
    omega
  exact impossible_packing B r k (fun i _ => hv i) (fun i _ => hr i) hk.injOn hd.injOn

end A274650Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a274650.main :=
  ⟨fun c => ⟨A274650Proof.column_injective c, A274650Proof.column_surjective c⟩,
   fun d => ⟨A274650Proof.diagonal_injective d, A274650Proof.diagonal_surjective d⟩⟩


import OMAStatements.S_oeis_a230498

/-!
# Prescribing the binary digit-sum parities of powers

We prove the mixed-parity conjecture in OEIS A230498 (Shevelev and Moses, 2013).
The induction realizes any prescribed finite pattern, even in the presence of
lower-degree digit-weight terms. Two distant powers of two give a single
controlled carry in the new highest degree.

Stoll, Thue–Morse Along Two Polynomial Subsequences (2015), treats two degrees.
Coons and Tachiya (arXiv:2312.06981, §2) also compare isolated binary carries.
-/

namespace A230498Proof

def wt (x : ℕ) : ℕ := (Nat.digits 2 x).count 1

theorem wt_add_blocks (x y k : ℕ) (h : x < 2^k) :
    wt (x + y * 2^k) = wt x + wt y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [wt]
  have he : (Nat.digits 2 x).length + (k - (Nat.digits 2 x).length) = k :=
    Nat.add_sub_of_le ((Nat.digits_length_le_iff (by decide : 1 < 2) x).mpr h)
  have hd := Nat.digits_append_zeroes_append_digits
    (n := x) (k := k - (Nat.digits 2 x).length) (by decide : 1 < 2) (Nat.pos_of_ne_zero hy)
  rw [he, Nat.mul_comm] at hd
  simp [wt, ← hd, List.count_replicate]

theorem wt_mul_pow_two (x k : ℕ) : wt (x * 2^k) = wt x := by
  simpa [wt] using wt_add_blocks 0 x k (by positivity)

theorem wt_sum_blocks {α : Type*} (s : Finset α) (f e : α → ℕ) (B : ℕ)
    (hinj : Set.InjOn e (↑s : Set α)) (hfit : ∀ u ∈ s, f u < 2^B) :
    wt (∑ u ∈ s, f u * 2^(B*e u)) = ∑ u ∈ s, wt (f u) := by
  classical
  suffices both : wt (∑ u ∈ s, f u * 2^(B * e u)) = ∑ u ∈ s, wt (f u) ∧
      ∀ M, (∀ u ∈ s, e u < M) → ∑ u ∈ s, f u * 2^(B * e u) < 2^(B*M) from both.1
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨u, hu, hmax⟩ := s.exists_max_image e hs
      obtain ⟨hw, hb⟩ := ih (s.erase u) (Finset.erase_ssubset hu)
        (hinj.mono (Finset.erase_subset u s)) (fun i hi => hfit i (Finset.mem_of_mem_erase hi))
      have hlow := hb (e u) (by
        intro i hi
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hi
        exact lt_of_le_of_ne (hmax i hmem) (fun h => hne (hinj hmem hu h)))
      rw [← Finset.sum_erase_add s (fun i => f i * 2^(B * e i)) hu,
          ← Finset.sum_erase_add s (fun i => wt (f i)) hu]
      constructor
      · rw [wt_add_blocks _ _ _ hlow, hw]
      · intro M hM
        calc
          _ < 2^(B * e u) + f u * 2^(B * e u) := Nat.add_lt_add_right hlow _
          _ = (f u + 1) * 2^(B * e u) := by ring
          _ ≤ 2^B * 2^(B * e u) := Nat.mul_le_mul_right _ (hfit u hu)
          _ = 2^(B * (e u + 1)) := by rw [← pow_add]; congr 1; ring
          _ ≤ 2^(B*M) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left B (hM u hu))
    · have he := Finset.not_nonempty_iff_eq_empty.mp hs
      simp [he, wt]

open Finset Filter

def shapeSum (r c x : ℕ) : ℕ :=
  ∑ j ∈ range (r+1), ∑ b ∈ range (r-j+1),
    wt ((c * r.choose j * (r-j).choose b) * x^(r-j-b))

private abbrev Exponents := (_ : ℕ) × ℕ

private def triangle (r : ℕ) : Finset Exponents :=
  (range (r+1)).sigma (fun j => range (r-j+1))

private def factor (r c x : ℕ) (u : Exponents) : ℕ :=
  (c * r.choose u.1 * (r-u.1).choose u.2) * x^(r-u.1-u.2)

private def band (n : ℕ) (u : Exponents) : ℕ := u.2 + n*u.1

private def offsetFactor (r c x H V : ℕ) (u : Exponents) : ℕ :=
  factor r c x u * 2^(u.2*H + u.1*V)

private def corner (n : ℕ) : Exponents := ⟨0,n⟩
private def upper : Exponents := ⟨1,0⟩

def exceptSum (n c x : ℕ) : ℕ :=
  ∑ u ∈ ((triangle n).erase (corner n)).erase upper, wt (factor n c x u)

private theorem expansion (n r c x H V B : ℕ) :
    c*(x + 2^(B+H) + 2^(n*B+V))^r =
      ∑ u ∈ triangle r, offsetFactor r c x H V u * 2^(B*band n u) := by
  let z := 2^(n*B+V)
  let y := 2^(B+H)
  change c*(x+y+z)^r = _
  rw [show x+y+z=z+(y+x) by omega, add_pow, triangle, sum_sigma]
  simp only [add_pow y x, mul_sum, sum_mul, Nat.cast_id]
  refine sum_congr rfl fun j _ => sum_congr rfl fun b _ => ?_
  have hp : z^j * y^b = 2^(b*H+j*V) * 2^(B*(b+n*j)) := by
    dsimp [z,y]
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    ring
  simp only [offsetFactor, factor, band]
  calc
    _ = (c*r.choose j*(r-j).choose b*x^(r-j-b)) * (z^j*y^b) := by ring
    _ = _ := by rw [hp]; ring

private theorem band_inj {n : ℕ} {s : Finset Exponents}
    (hs : ∀ u ∈ s, u.2 < n) : Set.InjOn (band n) (↑s : Set Exponents) := by
  intro u hu v hv h
  have h1 := hs u hu
  have h2 := hs v hv
  change u.2 + n*u.1 = v.2 + n*v.1 at h
  have he := congrArg (· % n) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at he
  have hm : n*u.1=n*v.1 := by omega
  exact Sigma.ext (Nat.eq_of_mul_eq_mul_left (by omega : 0<n) hm) (heq_of_eq he)

private theorem eventual_blocks {α : Type*} (s : Finset α) (f e : α → ℕ)
    (hinj : Set.InjOn e (↑s : Set α)) :
    ∀ᶠ B : ℕ in atTop, wt (∑ u ∈ s, f u * 2^(B*e u)) = ∑ u ∈ s, wt (f u) := by
  filter_upwards [eventually_ge_atTop (s.sup f)] with B hB
  apply wt_sum_blocks _ _ _ _ hinj
  intro u hu
  exact lt_of_le_of_lt ((le_sup hu).trans hB) Nat.lt_two_pow_self

theorem small_expansion (n r c x H V : ℕ) (hr : r < n) :
    ∀ᶠ B : ℕ in atTop,
      wt (c * (x + 2^(B+H) + 2^(n*B+V))^r) = shapeSum r c x := by
  have hi : Set.InjOn (band n) (↑(triangle r) : Set Exponents) := by
    apply band_inj
    intro u hu
    simp only [triangle, mem_sigma, mem_range] at hu
    omega
  filter_upwards [eventual_blocks _ (offsetFactor r c x H V) _ hi] with B hB
  rw [expansion, hB, triangle, sum_sigma, shapeSum]
  simp only [offsetFactor, wt_mul_pow_two, factor]

theorem last_expansion (n c x H V : ℕ) (hn : 2 ≤ n) :
    ∀ᶠ B : ℕ in atTop, wt (c * (x + 2^(B+H) + 2^(n*B+V))^n) =
      exceptSum n c x + wt (c*2^(n*H) + (c*n*x^(n-1))*2^V) := by
  let s := (triangle n).erase (corner n)
  let f := offsetFactor n c x H V
  let g (u : Exponents) := if u=upper then f (corner n) + f upper else f u
  have hc : corner n ∈ triangle n := by simp [corner, triangle]
  have hu : upper ∈ s := by
    simp [s, triangle, corner, upper]
    omega
  have hi : Set.InjOn (band n) (↑s : Set Exponents) := by
    apply band_inj
    intro u h
    simp only [s, mem_erase, triangle, mem_sigma, mem_range] at h
    by_contra! hh
    have h1 : u.1=0 := by omega
    have h2 : u.2=n := by omega
    exact h.1 (Sigma.ext h1 (heq_of_eq h2))
  have hsame {u : Exponents} (h : u ∈ s.erase upper) : g u = f u :=
    if_neg (mem_erase.mp h).1
  have hband : band n (corner n) = band n upper := by simp [band, corner, upper]
  have regroup (B : ℕ) :
      ∑ u ∈ triangle n, f u * 2^(B*band n u) =
      ∑ u ∈ s, g u * 2^(B*band n u) := by
    let k (u : Exponents) := 2^(B*band n u)
    change (∑ u ∈ triangle n, f u*k u) = ∑ u ∈ s, g u*k u
    rw [← sum_erase_add _ (fun u => f u*k u) hc]
    change (∑ u ∈ s, f u*k u) + f (corner n)*k (corner n) = _
    rw [← sum_erase_add _ (fun u => f u*k u) hu, ← sum_erase_add _ (fun u => g u*k u) hu]
    have hs : (∑ u ∈ s.erase upper, g u*k u) = ∑ u ∈ s.erase upper, f u*k u :=
      sum_congr rfl fun u h => by rw [hsame h]
    rw [hs, show k (corner n) = k upper by simp only [k, hband]]
    simp only [g, if_pos rfl]
    ring
  filter_upwards [eventual_blocks s g _ hi] with B hB
  rw [expansion]
  change wt (∑ u ∈ triangle n, f u * 2^(B*band n u)) = _
  rw [regroup, hB, ← sum_erase_add _ (fun u => wt (g u)) hu]
  congr 1
  · apply sum_congr rfl
    intro u h
    rw [hsame h]
    exact wt_mul_pow_two _ _
  · simp [g, f, offsetFactor, corner, upper, factor]

/-- Aligning the highest set bit of `y` with bit `L` creates exactly one carry. -/
theorem wt_one_carry (y L : ℕ) (hy : 0 < y) (hL : y.log2 ≤ L) :
    wt (2^L + y * 2^(L+1)) = wt (2^L + y * 2^(L-y.log2)) + 1 := by
  let d := y.log2
  let z := y - 2^d
  have lo : 2^d ≤ y := Nat.log2_self_le (by omega)
  have hi : y < 2^d * 2 := by simpa [d, pow_succ] using Nat.lt_log2_self (n := y)
  have hz : z < 2^d := by dsimp [z]; omega
  have hyz : y = z + 2^d := by dsimp [z]; omega
  have base : wt 1 = 1 := by decide
  have top (m : ℕ) : wt (2^m) = 1 := by
    simpa [base] using wt_mul_pow_two 1 m
  have bridge : 2^L = 2^d * 2^(L-d) := by
    rw [← pow_add, Nat.add_sub_of_le (show d ≤ L from hL)]
  have align : 2^L + y*2^(L-d) = (z + 2^(d+1))*2^(L-d) := by
    rw [bridge, hyz, pow_succ]
    ring
  have wz (m : ℕ) (hm : z < 2^m) : wt (z + 2^m) = wt z + 1 := by
    simpa [base] using wt_add_blocks z 1 m hm
  have step (m : ℕ) : 2^m < 2^(m+1) := by
    rw [pow_succ]
    have : 0 < 2^m := by positivity
    omega
  change wt (2^L + y * 2^(L+1)) = wt (2^L + y * 2^(L-d)) + 1
  rw [wt_add_blocks _ _ _ (step L), top, align, wt_mul_pow_two,
    wz _ (hz.trans (step d)), hyz, wz d hz]
  omega

/-- Finite sums of binary weights of scaled powers of degree less than r. -/
inductive IsLow (r : ℕ) : (ℕ → ℕ) → Prop where
  | zero : IsLow r (fun _ => 0)
  | atom (c j : ℕ) (h : j < r) : IsLow r (fun x => wt (c * x^j))
  | add {f g : ℕ → ℕ} : IsLow r f → IsLow r g → IsLow r (fun x => f x + g x)

private theorem low_finset {α : Type*} (r : ℕ) (s : Finset α) (f : α → ℕ → ℕ)
    (h : ∀ t ∈ s, IsLow r (f t)) : IsLow r (fun x => ∑ t ∈ s, f t x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IsLow.zero (r := r))
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact IsLow.add (h a (by simp)) (ih (fun t ht => h t (by simp [ht])))

theorem low_one_const {f : ℕ → ℕ} (hf : IsLow 1 f) (x : ℕ) : f x = f 0 := by
  induction hf with
  | zero => rfl
  | atom c j hj =>
    obtain rfl : j = 0 := by omega
    simp
  | add _ _ ih₁ ih₂ => exact congrArg₂ (·+·) ih₁ ih₂

private theorem low_shape (r j c : ℕ) (hj : j < r) : IsLow r (shapeSum j c) := by
  unfold shapeSum
  apply low_finset
  intro t ht
  apply low_finset
  intro b hb
  apply IsLow.atom
  omega

theorem low_expand {n r : ℕ} {f : ℕ → ℕ} (hf : IsLow r f) (hr : r ≤ n) :
    ∃ g : ℕ → ℕ, IsLow r g ∧ ∀ x H V : ℕ, ∀ᶠ B : ℕ in atTop,
      f (x+2^(B+H)+2^(n*B+V)) = g x := by
  induction hf with
  | zero => exact ⟨_, IsLow.zero, fun _ _ _ => Filter.Eventually.of_forall (fun _ => rfl)⟩
  | atom c j hj =>
    exact ⟨_, low_shape r j c hj, fun x H V => small_expansion n j c x H V (by omega)⟩
  | add hf hg ihf ihg =>
    obtain ⟨f', h₁, e₁⟩ := ihf
    obtain ⟨g', h₂, e₂⟩ := ihg
    refine ⟨_, IsLow.add h₁ h₂, fun x H V => ?_⟩
    filter_upwards [e₁ x H V, e₂ x H V] with B hb₁ hb₂ using congrArg₂ (·+·) hb₁ hb₂

theorem main_expand (n r : ℕ) (hr : r < n) :
    ∃ g : ℕ → ℕ, IsLow r g ∧ ∀ x H V : ℕ, ∀ᶠ B : ℕ in atTop,
      wt ((x+2^(B+H)+2^(n*B+V))^r) = wt (x^r) + g x := by
  let o : Exponents := ⟨0,0⟩
  let s := (triangle r).erase o
  let g := fun x => ∑ u ∈ s, wt (factor r 1 x u)
  have ho : o ∈ triangle r := by simp [triangle, o]
  refine ⟨g, ?_, fun x H V => ?_⟩
  · apply low_finset
    rintro ⟨j,b⟩ hu
    change Sigma.mk j b ∈ (triangle r).erase o at hu
    have hn := (Finset.mem_erase.mp hu).1
    change IsLow r (fun x => wt ((1 * r.choose j * (r-j).choose b) * x^(r-j-b)))
    apply IsLow.atom
    have hm := (Finset.mem_erase.mp hu).2
    simp [triangle] at hm
    by_cases hz : j = 0
    · subst j
      have : b ≠ 0 := by rintro rfl; exact hn rfl
      omega
    · omega
  · filter_upwards [small_expansion n r 1 x H V hr] with B h
    rw [one_mul] at h
    rw [h]
    change (∑ j ∈ range (r+1), ∑ b ∈ range (r-j+1), wt (factor r 1 x ⟨j,b⟩)) = _
    rw [Finset.sum_sigma']
    change (∑ u ∈ triangle r, wt (factor r 1 x u)) = _
    rw [← Finset.add_sum_erase (triangle r) _ ho]
    simp [o, factor, g, s]

/-- A new pair of widely separated bits can repair the last parity while the
lower parities reduce to constraints on the original integer. -/
private theorem realize_parities (n : ℕ) :
    ∀ (f : ℕ → ℕ → ℕ) (target : ℕ → ℕ), (∀ i, IsLow i (f i)) →
      ∃ x : ℕ, Odd x ∧ 1 < x ∧ ∀ i, 1 ≤ i → i ≤ n+1 →
        (wt (x^i) + f i x) % 2 = target i % 2 := by
  classical
  induction n with
  | zero =>
    intro f target hf
    have hc := low_one_const (hf 1)
    by_cases h : (2 + f 1 0) % 2 = target 1 % 2
    · refine ⟨3, by decide, by decide, ?_⟩
      intro i h₁ h₂
      obtain rfl : i = 1 := by omega
      simpa [pow_one, hc 3, show wt 3 = 2 by decide] using h
    · refine ⟨7, by decide, by decide, ?_⟩
      intro i h₁ h₂
      obtain rfl : i = 1 := by omega
      rw [pow_one, hc 7, show wt 7 = 3 by decide]
      omega
  | succ n ih =>
    intro f target hf
    let N := n+2
    have hN : 2 ≤ N := by dsimp [N]; omega
    have transform (i : ℕ) : ∃ g : ℕ → ℕ, IsLow i g ∧ (i < N →
        ∀ x H V : ℕ, ∀ᶠ B : ℕ in atTop,
          wt ((x+2^(B+H)+2^(N*B+V))^i) + f i (x+2^(B+H)+2^(N*B+V)) =
            wt (x^i) + g x) := by
      by_cases hi : i < N
      · obtain ⟨u,hu,eu⟩ := main_expand N i hi
        obtain ⟨v,hv,ev⟩ := low_expand (hf i) hi.le
        refine ⟨_, IsLow.add hu hv, fun _ x H V => ?_⟩
        filter_upwards [eu x H V, ev x H V] with B e₁ e₂
        rw [e₁, e₂, Nat.add_assoc]
      · exact ⟨_, IsLow.zero, fun hi' => (hi hi').elim⟩
    choose g hg eg using transform
    obtain ⟨x, ox, hx, px⟩ := ih g target hg
    obtain ⟨v, _, ev⟩ := low_expand (n := N) (hf N) le_rfl
    let y := N*x^(N-1)
    let H := y.log2
    let L := N*H
    have hy : 0 < y := Nat.mul_pos (by omega) (pow_pos (by omega) _)
    have hL : y.log2 ≤ L := Nat.le_mul_of_pos_left H (by omega)
    have toggle := wt_one_carry y L hy hL
    obtain ⟨V,hV⟩ : ∃ V : ℕ,
        (exceptSum N 1 x + wt (2^L + y*2^V) + v x) % 2 = target N % 2 := by
      by_cases hit : (exceptSum N 1 x + wt (2^L+y*2^(L+1)) + v x) % 2 = target N % 2
      · exact ⟨L+1,hit⟩
      · exact ⟨L-y.log2, by omega⟩
    let K (B : ℕ) := x+2^(B+H)+2^(N*B+V)
    have prev : ∀ᶠ B : ℕ in atTop, ∀ i : Fin N,
        wt ((K B)^i.val) + f i.val (K B) = wt (x^i.val) + g i.val x :=
      Filter.eventually_all.mpr (fun i => eg i.val i.isLt x H V)
    have last : ∀ᶠ B : ℕ in atTop,
        wt ((K B)^N) + f N (K B) = exceptSum N 1 x + wt (2^L+y*2^V) + v x := by
      filter_upwards [last_expansion N 1 x H V hN, ev x H V] with B e₁ e₂
      simpa only [K, L, y, one_mul, e₂] using congrArg (· + v x) e₁
    obtain ⟨B,hB,hprev,hlast⟩ := ((eventually_ge_atTop 1).and (prev.and last)).exists
    have e₂ : Even (2 : ℕ) := by decide
    have hb₁ := e₂.pow_of_ne_zero (show B+H ≠ 0 by omega)
    have hb₂ := e₂.pow_of_ne_zero (show N*B+V ≠ 0 by
      have := Nat.mul_pos (show 0<N by omega) (show 0<B by omega)
      omega)
    refine ⟨K B, (ox.add_even hb₁).add_even hb₂, hx.trans_le ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)), ?_⟩
    intro i hi hiN
    by_cases e : i = N
    · subst i
      rw [hlast]
      exact hV
    · have ltN : i < N := by dsimp [N] at *; omega
      rw [hprev ⟨i,ltN⟩]
      exact px i hi (by dsimp [N] at ltN; omega)

end A230498Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a230498.main := by
  intro n hn
  let target (i : ℕ) := if i = 1 then 1 else 0
  obtain ⟨x,ox,hx,p⟩ := A230498Proof.realize_parities (n-1)
    (fun _ _ => 0) target (fun _ => .zero)
  refine ⟨x,ox,hx,?_,?_⟩
  · apply Nat.odd_iff.mpr
    simpa [target, A230498Proof.wt] using p 1 (by decide) (by omega)
  · intro i hi hin
    apply Nat.even_iff.mpr
    simpa [target, show i ≠ 1 by omega, A230498Proof.wt] using p i (by omega) (by omega)

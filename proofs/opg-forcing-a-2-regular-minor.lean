import OMAStatements.S_opg_forcing_a_2_regular_minor
import Mathlib
/- Density splitting follows Csóka, Lo, Norin, Wu and Yepremyan, The extremal function for disconnected minors, Theorems 1 and 7. arXiv:1509.01185. The Erdős–Gallai long-cycle proof is adapted from the merged R1.H1 proofs by @gertjanvdgoot and @dasante78. -/
open Matrix
open scoped Matrix

namespace Wave10G

/-- Undirected edge score in the fractional-split proof, counted by an adjacency matrix. -/
noncomputable def energy {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) : ℝ :=
  (x ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ x))/2

/-- The two-coordinate update is exactly affine when the vertices are nonadjacent. -/
theorem nonedgePivot {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V → ℝ) (i j : V) (hij : ¬ G.Adj i j) (u v : ℝ) :
    energy G (x+(Pi.single i u + Pi.single j v)) = energy G x +
      u*((G.adjMatrix ℝ)*ᵥ x) i + v*((G.adjMatrix ℝ)*ᵥ x) j := by
  let A := G.adjMatrix ℝ
  let d : V → ℝ := Pi.single i u + Pi.single j v
  have symm : x ⬝ᵥ (A *ᵥ d) = d ⬝ᵥ (A *ᵥ x) := by
    simpa [A] using dotProduct_transpose_mulVec A x d
  have row (l k : V) (a : ℝ) : (A *ᵥ Pi.single k a) l = A l k * a :=
    dotProduct_single _ _ _
  have hzero : d ⬝ᵥ (A *ᵥ d) = 0 := by
    have hji : ¬ G.Adj j i := fun h => hij h.symm
    simp only [d, mulVec_add, add_dotProduct, single_dotProduct, Pi.add_apply, row]
    simp [A, SimpleGraph.adjMatrix_apply, hij, hji]
  change ((x+d) ⬝ᵥ (A *ᵥ (x+d)))/2 = (x ⬝ᵥ (A *ᵥ x))/2 + _ + _
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, symm, hzero]
  simp only [d, add_dotProduct, single_dotProduct, A]
  ring

end Wave10G

namespace Wave10G

/-- The original non-strict threshold gives a strict surplus on a nonempty host. -/
theorem threshold {k n e : ℝ} (hk : 3 ≤ k) (hn : 0 < n)
    (h : 4/3*k-2 ≤ 2*e/n) : (2/3*k-1)*(n-1) < e := by
  have h' := (le_div_iff₀ hn).mp h
  nlinarith

/-- The induction budget is additive with the splitting theorem's surcharge of one. -/
theorem splitBudget (a b : ℝ) :
    (2/3*a-1) + (2/3*b-1) + 1 = 2/3*(a+b)-1 := by ring

/-- A common nondecreasing direction for two affine functionals on a plane. -/
theorem twoSlopes (a b c d : ℝ) : ∃ u v : ℝ, (u ≠ 0 ∨ v ≠ 0) ∧
    0 ≤ a*u+b*v ∧ 0 ≤ c*u+d*v := by
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    by_cases hc : 0 ≤ c
    · exact ⟨1, 0, by simp, by simp, by simpa using hc⟩
    · exact ⟨-1, 0, by simp, by simp, by simpa using (le_of_not_ge hc)⟩
  · by_cases h : 0 ≤ c*b-d*a
    · refine ⟨b, -a, ?_, by linarith only [show a*b+b*(-a)=0 by ring], by linarith⟩
      by_contra! hh
      exact hab ⟨neg_eq_zero.mp hh.2, hh.1⟩
    · refine ⟨-b, a, ?_, by linarith only [show a*(-b)+b*a=0 by ring], by linarith⟩
      by_contra! hh
      exact hab ⟨hh.2, neg_eq_zero.mp hh.1⟩

/-- At mass s+1 the quadratic edge bound prevents crossing the balance barrier. -/
theorem massBarrier {s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    (s+1)^2/2 - (s+1/2)*(s+1) ≤ -(s+1/2)^2/(s+t+1) := by
  apply (le_div_iff₀ (by linarith : 0 < s+t+1)).mpr
  have h1 : 0 ≤ s*(s+1)*(s+t+1-3) := by
    have : 0 ≤ s+t+1-3 := by linarith
    positivity
  nlinarith [sq_nonneg s]

theorem baseBound {s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    (s+1/2)^2/(s+t+1) ≤ s := by
  apply (div_le_iff₀ (by linarith : 0 < s+t+1)).mpr
  nlinarith [mul_le_mul hs ht (by linarith) (by linarith)]

/-- On integral assignments the affine replacement underestimates the clique's edges. -/
theorem chordOnInteger (r p : ℤ) :
    2*r*p-r*(r+1) ≤ p*(p-1) := by
  by_cases h : p ≤ r
  · nlinarith [mul_nonneg (show 0 ≤ r-p by omega) (show 0 ≤ r+1-p by omega)]
  · nlinarith [mul_nonneg (show 0 ≤ p-r by omega) (show 0 ≤ p-r-1 by omega)]

/-- Difference between the affine surrogate and the balanced objective on a fractional clique. -/
theorem cliqueGain {r q a squares c : ℝ} (hc : 0 < c)
    (hr : r ≤ q) (hr' : q ≤ r+1) (hcs : q^2 ≤ c*squares) :
    a/2 + q^2/(2*c) ≤
      (a+q)/2 + r*q-r*(r+1)/2 - (q^2-squares)/2 := by
  have h := (div_le_iff₀ (by linarith : 0 < 2*c)).mpr
    (show q^2 ≤ (squares/2)*(2*c) by linarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hr')]

/-- uv/(u+v) is increasing in both coordinates, including zero boundary values. -/
theorem harmonicBound {u v a b : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ha : u ≤ a) (hb : v ≤ b) (huv : 0 < u+v) :
    u*v/(u+v) ≤ a*b/(a+b) := by
  apply (div_le_div_iff₀ huv (by linarith)).mpr
  nlinarith [mul_nonneg (mul_nonneg hu (by linarith : 0 ≤ a)) (sub_nonneg.mpr hb),
    mul_nonneg (mul_nonneg hv (by linarith : 0 ≤ b)) (sub_nonneg.mpr ha)]

/-- Bound the loss in the rounded-down color (the delicate final rounding inequality). -/
theorem downBound {s t q v : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hq : 0 ≤ q) (hv : 0 ≤ v) (hc : 0 < q+v)
    (hq' : q ≤ 2*s+1) (hv' : v ≤ 2*t+1) :
    -s ≤ (s-q)/2 + q^2/(2*(q+v)) - (s+1/2)^2/(s+t+1) := by
  have h := harmonicBound hq hv hq' hv' hc
  have hd : s+t+1 ≠ 0 := by linarith
  have heq : (s-q)/2 + q^2/(2*(q+v)) = s/2 - (q*v/(q+v))/2 := by
    field_simp [ne_of_gt hc]; ring
  rw [heq]
  have h' : ((2*s+1)*(2*t+1)/(2*s+1+(2*t+1)))/2 + (s+1/2)^2/(s+t+1) = s+1/2 := by
    have h2 : 2*s+1+(2*t+1) ≠ 0 := by linarith
    field_simp [hd, h2]; ring
  linarith


/-- Convert the seed edge surplus to the strict lower bound for a constant coloring. -/
theorem seedScore {s t n e : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hedges : (s+t+1)*(n-1) < e) :
    -(s+1/2)^2/(s+t+1) <
      ((s+1/2)/(s+t+1))^2*e - (s+1/2)*((s+1/2)/(s+t+1))*n := by
  have hd : 0 < s+t+1 := by linarith
  have hw : 0 < (s+1/2)/(s+t+1) := div_pos (by linarith) hd
  have h := mul_lt_mul_of_pos_left hedges (sq_pos_of_pos hw)
  calc
    -(s+1/2)^2/(s+t+1) =
        ((s+1/2)/(s+t+1))^2*((s+t+1)*(n-1)) -
          (s+1/2)*((s+1/2)/(s+t+1))*n := by field_simp [hd.ne']; ring
    _ < _ := sub_lt_sub_right h _

/-- Common-pivot primitive: after orienting a moving coordinate toward its upper endpoint,
    bound its positive time to the boundary. Used once for each nonzero velocity. -/
theorem timeToEnd {x u : ℝ} (hx : 0 < x) (hx' : x < 1) (hu : u ≠ 0) :
    ∃ T : ℝ, 0 < T ∧ (x+T*u=0 ∨ x+T*u=1) ∧
      ∀ z ∈ Set.Icc 0 T, 0 ≤ x+z*u ∧ x+z*u ≤ 1 := by
  rcases lt_or_gt_of_ne hu with h | h
  · refine ⟨-x/u, div_pos_of_neg_of_neg (by linarith) h, Or.inl ?_, ?_⟩
    · field_simp; ring
    · intro z hz
      have low := mul_le_mul_of_nonpos_right hz.2 h.le
      have upp := mul_nonpos_of_nonneg_of_nonpos hz.1 h.le
      rw [div_mul_cancel₀ _ hu] at low
      constructor <;> linarith
  · refine ⟨(1-x)/u, div_pos (by linarith) h, Or.inr ?_, ?_⟩
    · field_simp; ring
    · intro z hz
      have upp := mul_le_mul_of_nonneg_right hz.2 h.le
      have low := mul_nonneg hz.1 h.le
      rw [div_mul_cancel₀ _ hu] at upp
      constructor <;> linarith

/-- Transfer the pre-rounding affine score to the color which loses its fraction x. -/
theorem lastDown {s t q v r a x d F F' : ℝ}
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hq : 0 ≤ q) (hv : 0 ≤ v) (hc : 0 < q+v)
    (hq' : q ≤ 2*s+1) (hv' : v ≤ 2*t+1) (hr : r ≤ q)
    (hsa : s ≤ r+a) (hda : d ≤ a) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hF : a/2+q^2/(2*(q+v))-(s+1/2)^2/(s+t+1) < F)
    (change : F' = F-(r+d-s)*x) : -s < F' := by
  have h := downBound hs ht hq hv hc hq' hv'
  have hd := mul_le_mul_of_nonneg_right hda hx
  have hh := mul_le_mul_of_nonneg_left hx' (show 0 ≤ r+a-s by linarith)
  linarith

/-- The other color gains y=1-x with 0≤y≤1/2 when its own coordinate rounds up. -/
theorem lastUp {s t q c r a y d F F' : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hc : 0 < c) (ha : 0 ≤ a) (hd : 0 ≤ d) (hsa : s ≤ r+a)
    (hy : 0 ≤ y) (hy' : y ≤ 1/2)
    (hF : a/2+q^2/(2*c)-(s+1/2)^2/(s+t+1) < F)
    (change : F' = F+(r+d-s)*y) : -s < F' := by
  have hb := baseBound hs ht
  have hp : 0 ≤ q^2/(2*c) := by positivity
  have hdy := mul_nonneg hd hy
  by_cases h : s ≤ r
  · have hh := mul_nonneg (sub_nonneg.mpr h) hy
    linarith
  · have hh := mul_le_mul_of_nonpos_left hy' (show r-s ≤ 0 by linarith)
    linarith

end Wave10G

namespace Wave10G

open Finset Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

def mass (x : V → ℝ) := ∑ i, x i
def flip (x : V → ℝ) := fun i => 1-x i
def Box (x : V → ℝ) := ∀ i, x i ∈ Set.Icc (0 : ℝ) 1
noncomputable def fracs (x : V → ℝ) : Finset V := by
  classical exact univ.filter fun i => 0 < x i ∧ x i < 1

@[simp] theorem mem_fracs {x : V → ℝ} {i : V} : i ∈ fracs x ↔ 0 < x i ∧ x i < 1 := by
  classical simp [fracs]

def move (x : V → ℝ) (i j : V) (u v : ℝ) := x + (Pi.single i u + Pi.single j v)

theorem mass_move (x : V → ℝ) (i j : V) (u v : ℝ) :
    mass (move x i j u v) = mass x + u + v := by
  simp [move, mass, Pi.single_apply, Finset.sum_add_distrib, add_assoc]

theorem flip_move (x : V → ℝ) (i j : V) (u v : ℝ) :
    flip (move x i j u v) = move (flip x) i j (-u) (-v) := by
  ext k
  by_cases hi : i=k <;> by_cases hj : j=k <;> simp [move,flip,Pi.single_apply, *, sub_eq_add_neg] <;> ring

theorem box_flip {x : V → ℝ} (hx : Box x) : Box (flip x) := by
  intro i
  obtain ⟨h,h'⟩ := hx i
  change 0 ≤ 1-x i ∧ 1-x i ≤ 1
  constructor <;> linarith

theorem pairTime {x y u v : ℝ} (hx : 0<x ∧ x<1) (hy : 0<y ∧ y<1) (hn : u ≠ 0 ∨ v ≠ 0) :
    ∃ T : ℝ, 0 < T ∧ (x+T*u=0 ∨ x+T*u=1 ∨ y+T*v=0 ∨ y+T*v=1) ∧
      ∀ z ∈ Set.Icc 0 T, x+z*u ∈ Set.Icc (0:ℝ) 1 ∧ y+z*v ∈ Set.Icc (0:ℝ) 1 := by
  by_cases hu : u=0
  · subst u
    obtain ⟨T,hT,he,hb⟩ := timeToEnd hy.1 hy.2 (hn.resolve_left (by simp))
    exact ⟨T,hT,Or.inr (Or.inr he),fun z hz => ⟨by simpa using And.intro hx.1.le hx.2.le,hb z hz⟩⟩
  obtain ⟨U,hU,eu,bu⟩ := timeToEnd hx.1 hx.2 hu
  by_cases hv : v=0
  · subst v
    exact ⟨U,hU,eu.imp_right Or.inl,fun z hz => ⟨bu z hz,by simpa using And.intro hy.1.le hy.2.le⟩⟩
  obtain ⟨W,hW,ew,bw⟩ := timeToEnd hy.1 hy.2 hv
  rcases le_total U W with h | h
  · exact ⟨U,hU,eu.imp_right Or.inl, fun z hz => ⟨bu z hz, bw z ⟨hz.1,hz.2.trans h⟩⟩⟩
  · exact ⟨W,hW,Or.inr (Or.inr ew), fun z hz => ⟨bu z ⟨hz.1,hz.2.trans h⟩, bw z hz⟩⟩

theorem pivotBox {x : V → ℝ} (hx : Box x) {i j : V} (hne : i ≠ j)
    (hi : i ∈ fracs x) (hj : j ∈ fracs x) {u v : ℝ} (hn : u ≠ 0 ∨ v ≠ 0) :
    ∃ T : ℝ, 0 < T ∧ (fracs (move x i j (T*u) (T*v))).card < (fracs x).card ∧
      ∀ z ∈ Set.Icc 0 T, Box (move x i j (z*u) (z*v)) := by
  obtain ⟨T,hT,he,hb⟩ := pairTime (mem_fracs.mp hi) (mem_fracs.mp hj) hn
  have ei (z : ℝ) : move x i j (z*u) (z*v) i = x i+z*u := by simp [move,hne.symm,Pi.single_apply]
  have ej (z : ℝ) : move x i j (z*u) (z*v) j = x j+z*v := by simp [move,hne,Pi.single_apply]
  have ek (z : ℝ) (k : V) (hik : i ≠ k) (hjk : j ≠ k) :
      move x i j (z*u) (z*v) k = x k := by simp [move,hik,hjk,Pi.single_apply]
  refine ⟨T,hT,Finset.card_lt_card ?_,?_⟩
  · apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro k hk
      by_cases hik : i=k
      · exact hik ▸ hi
      by_cases hjk : j=k
      · exact hjk ▸ hj
      simpa [mem_fracs,ek T k hik hjk] using hk
    · intro h
      have hi' := mem_fracs.mp (h.symm ▸ hi)
      have hj' := mem_fracs.mp (h.symm ▸ hj)
      rw [ei] at hi'
      rw [ej] at hj'
      rcases he with h|h|h|h <;> linarith
  · intro z hz k
    by_cases hik : i=k
    · subst k; rw [ei]; exact (hb z hz).1
    by_cases hjk : j=k
    · subst k; rw [ej]; exact (hb z hz).2
    rw [ek z k hik hjk]
    exact hx k

theorem energyBound (G : SimpleGraph V) [DecidableRel G.Adj] {x : V → ℝ} (hx : Box x) :
    energy G x ≤ (mass x)^2/2 := by
  unfold energy
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [pow_two, mass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hx i).1
  rw [G.adjMatrix_mulVec_apply]
  exact Finset.sum_le_univ_sum_of_nonneg (fun j => (hx j).1)

noncomputable def score (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℝ) (x : V → ℝ) :=
  energy G x - (s+1/2)*mass x

theorem score_move (G : SimpleGraph V) [DecidableRel G.Adj] (s : ℝ) (x : V → ℝ)
    {i j : V} (hn : ¬ G.Adj i j) (u v : ℝ) :
    score G s (move x i j u v) = score G s x +
      (((G.adjMatrix ℝ)*ᵥ x) i-(s+1/2))*u + (((G.adjMatrix ℝ)*ᵥ x) j-(s+1/2))*v := by
  unfold score
  rw [mass_move]
  unfold move
  rw [nonedgePivot G x i j hn]
  ring

theorem keepsMass (G : SimpleGraph V) [DecidableRel G.Adj] {s t : ℝ} (hs : 1 ≤ s)
    (ht : 1 ≤ t) {x : V → ℝ} (hm : s+1 < mass x) {i j : V} {u v T : ℝ}
    (hT : 0 ≤ T) (hb : ∀ z ∈ Set.Icc 0 T, Box (move x i j (z*u) (z*v)))
    (hf : ∀ z ∈ Set.Icc 0 T, -(s+1/2)^2/(s+t+1) < score G s (move x i j (z*u) (z*v))) :
    s+1 < mass (move x i j (T*u) (T*v)) := by
  by_contra! h
  let f := fun z : ℝ => mass x + z*u + z*v
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hI : s+1 ∈ Set.Icc (f T) (f 0) := ⟨by simpa [f,mass_move] using h, by simpa [f] using hm.le⟩
  obtain ⟨z,hz,hz'⟩ := intermediate_value_Icc' hT hc.continuousOn hI
  have hm' : mass (move x i j (z*u) (z*v)) = s+1 := (mass_move ..).trans hz'
  have h1 := energyBound G (hb z hz)
  have h2 := hf z hz
  unfold score at h2
  rw [hm'] at h1 h2
  linarith [massBarrier hs ht]


def Good (G : SimpleGraph V) [DecidableRel G.Adj] (s t : ℝ) (x : V → ℝ) : Prop :=
  s+1 < mass x ∧ -(s+1/2)^2/(s+t+1) < score G s x

theorem goodMove (G : SimpleGraph V) [DecidableRel G.Adj] {s t : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    {x : V → ℝ} (hg : Good G s t x) {i j : V} (hn : ¬ G.Adj i j) {u v T : ℝ}
    (hT : 0 ≤ T) (hb : ∀ z ∈ Set.Icc 0 T, Box (move x i j (z*u) (z*v)))
    (hdir : 0 ≤ (((G.adjMatrix ℝ)*ᵥ x) i-(s+1/2))*u + (((G.adjMatrix ℝ)*ᵥ x) j-(s+1/2))*v) :
    Good G s t (move x i j (T*u) (T*v)) := by
  have hf (z : ℝ) (hz : z ∈ Set.Icc 0 T) :
      -(s+1/2)^2/(s+t+1) < score G s (move x i j (z*u) (z*v)) := by
    rw [score_move G s x hn]
    linarith only [hg.2,mul_nonneg hz.1 hdir]
  exact ⟨keepsMass G hs ht hg.1 hT hb hf,hf T ⟨hT,le_rfl⟩⟩

theorem constantEnergy (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℝ) :
    energy G (fun _ => a) = a^2*G.edgeFinset.card := by
  have h : ∑ i, (G.degree i : ℝ) = 2*(G.edgeFinset.card : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  simp only [energy,dotProduct,SimpleGraph.adjMatrix_mulVec_apply,Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree,nsmul_eq_mul]
  simp_rw [show ∀ z : ℝ, a*(z*a)=a^2*z by intro; ring]
  rw [← Finset.mul_sum,h]
  ring

noncomputable def Dense {W : Type} [Fintype W] (G : SimpleGraph W) (s : ℝ) : Prop := by
  classical exact s * ((Fintype.card W : ℝ)-1) < G.edgeFinset.card

theorem dense_order [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℝ}
    (hd : Dense G d) : 2*d < Fintype.card V := by
  have he : d*((Fintype.card V : ℝ)-1) < G.edgeFinset.card := by
    simpa only [Dense, ← SimpleGraph.card_edgeSet, ← Nat.card_eq_fintype_card] using hd
  let n := Fintype.card V
  have hn : 1 ≤ n := Fintype.card_pos
  have hmax : G.edgeFinset.card * 2 ≤ n*(n-1) := by
    calc
      _ ≤ n.choose 2 * 2 := Nat.mul_le_mul_right 2 G.card_edgeFinset_le_card_choose_two
      _ = _ := by rw [Nat.choose_two_right,Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]
  have hR : (G.edgeFinset.card : ℝ)*2 ≤ (n : ℝ)*(n-1) := by
    exact_mod_cast (by simpa [Nat.cast_sub hn] using
      (show (G.edgeFinset.card : ℝ)*2 ≤ (n : ℝ)*((n-1:ℕ):ℝ) by exact_mod_cast hmax) :
      (G.edgeFinset.card : ℝ)*2 ≤ (n : ℝ)*(n-1))
  change d*((n : ℝ)-1) < _ at he
  have hnp : (0 : ℝ) < n-1 := by
    rcases eq_or_lt_of_le hn with h|h
    · have hz : G.edgeFinset.card = 0 := by rw [← h] at hmax; omega
      rw [← h,hz] at he
      norm_num at he
    · have : (1 : ℝ) < n := by exact_mod_cast h
      linarith
  exact lt_of_mul_lt_mul_right (show 2*d*((n : ℝ)-1) < (n : ℝ)*(n-1) by linarith) hnp.le

theorem seedGood [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {s t : ℝ}
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hd : Dense G (s+t+1)) :
    Good G s t (fun _ => (s+1/2)/(s+t+1)) := by
  have he : (s+t+1)*((Fintype.card V : ℝ)-1) < G.edgeFinset.card := by
    simpa only [Dense, ← SimpleGraph.card_edgeSet, ← Nat.card_eq_fintype_card] using hd
  have hn := dense_order G hd
  have hD : 0 < s+t+1 := by linarith
  have ha : 0 < (s+1/2)/(s+t+1) := div_pos (by linarith) hD
  have hmul := mul_lt_mul_of_pos_left hn ha
  have hcancel := div_mul_cancel₀ (s+1/2) hD.ne'
  constructor
  · simp only [mass,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    nlinarith only [hmul,hcancel,hs]
  · rw [score,constantEnergy]
    simp only [mass,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    linarith only [seedScore hs ht he]

theorem fractionalClique [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] {s t : ℝ}
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hd : Dense G (s+t+1)) :
    ∃ x : V → ℝ, Box x ∧ Good G s t x ∧ Good G t s (flip x) ∧
      ∀ i ∈ fracs x, ∀ j ∈ fracs x, i ≠ j → G.Adj i j := by
  classical
  let P := fun x : V → ℝ => Box x ∧ Good G s t x ∧ Good G t s (flip x)
  have hD : 0 < s+t+1 := by linarith
  have seed : ∃ x, P x := by
    let a := (s+1/2)/(s+t+1)
    refine ⟨fun _ => a,fun _ => ⟨div_nonneg (by linarith) hD.le,(div_le_one hD).mpr (by linarith)⟩,
      seedGood G hs ht hd,?_⟩
    have e : flip (fun _ : V => a) = (fun _ => (t+1/2)/(t+s+1)) := by
      ext; dsimp [flip,a]; rw [add_comm t s]; field_simp; ring
    rw [e]
    exact seedGood G ht hs (by rwa [add_comm t s])
  obtain ⟨x,hx,minimal⟩ := exists_minimalFor_of_wellFoundedLT P (fun x => (fracs x).card) seed
  refine ⟨x,hx.1,hx.2.1,hx.2.2,?_⟩
  intro i hi j hj hij
  by_contra hn
  let a := fun (s : ℝ) (x : V → ℝ) k => ((G.adjMatrix ℝ)*ᵥ x) k-(s+1/2)
  obtain ⟨u,v,hnz,d1,d2⟩ := twoSlopes (a s x i) (a s x j) (-a t (flip x) i) (-a t (flip x) j)
  obtain ⟨T,hT,hlt,hb⟩ := pivotBox hx.1 hij hi hj hnz
  let y := move x i j (T*u) (T*v)
  have fbe (z : ℝ) : move (flip x) i j (z*(-u)) (z*(-v)) = flip (move x i j (z*u) (z*v)) := by
    rw [flip_move]; simp
  have hy : P y := by
    refine ⟨hb T ⟨hT.le,le_rfl⟩,goodMove G hs ht hx.2.1 hn hT.le hb d1,?_⟩
    rw [show flip y = _ from (fbe T).symm]
    apply goodMove G ht hs hx.2.2 hn hT.le
    · intro z hz; rw [fbe]; exact box_flip (hb z hz)
    · dsimp [a] at d2
      linarith only [d2]
  exact hlt.not_ge (minimal hy hlt.le)


def extend (C : Finset V) (w : C → ℝ) (i : V) := if hi : i∈C then w ⟨i,hi⟩ else 0
def indic (A : Finset V) (i : V) : ℝ := if i∈A then 1 else 0

theorem sum_extend (C : Finset V) (w : C → ℝ) :
    ∑ i, extend C w i = ∑ i, w i := by
  calc
    _ = ∑ i ∈ C, extend C w i := by
      symm; apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi; simp [extend,hi]
    _ = _ := by rw [← Finset.sum_coe_sort]; simp [extend]

theorem extend_dot (C : Finset V) (w : C → ℝ) (f : V → ℝ) :
    (extend C w) ⬝ᵥ f = ∑ i : C, w i*f i := by
  rw [← sum_extend C (fun i => w i*f i)]
  unfold dotProduct
  apply sum_congr rfl
  intro i _
  by_cases hi : i∈C <;> simp [extend,hi]

theorem mass_indic (A : Finset V) : mass (indic A) = A.card := by
  simp [mass,indic,Finset.sum_boole]

theorem degreeIndic (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (i : V) :
    ((G.adjMatrix ℝ)*ᵥ indic A) i = ((G.neighborFinset i ∩ A).card : ℝ) := by
  simp [SimpleGraph.adjMatrix_mulVec_apply,indic,Finset.sum_boole]

theorem energy_indic (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    energy G (indic A) = ((G.induce (A : Set V)).edgeFinset.card : ℝ) := by
  have e : indic A = extend A (fun _ => 1) := by ext i; by_cases h : i∈A <;> simp [indic,extend,h]
  unfold energy
  rw [e,extend_dot,← e]
  have row (i : A) : ((G.adjMatrix ℝ)*ᵥ indic A) i =
      (((G.induce (A:Set V)).adjMatrix ℝ)*ᵥ fun _ => (1 : ℝ)) i := by
    rw [e,show ((G.adjMatrix ℝ)*ᵥ extend A (fun _ => 1)) i =
        extend A (fun _ => 1) ⬝ᵥ (G.adjMatrix ℝ i) from dotProduct_comm ..,extend_dot]
    unfold Matrix.mulVec dotProduct
    apply sum_congr rfl
    intro j _
    simp only [one_mul,mul_one,SimpleGraph.adjMatrix_apply,SimpleGraph.induce_adj]
  simp_rw [row]
  change energy (G.induce (A:Set V)) (fun _ => 1) = _
  rw [constantEnergy]
  ring

theorem energy_add (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V → ℝ) :
    energy G (x+y) = energy G x + y ⬝ᵥ ((G.adjMatrix ℝ)*ᵥ x) + energy G y := by
  have h := dotProduct_transpose_mulVec (G.adjMatrix ℝ) x y
  simp only [SimpleGraph.transpose_adjMatrix] at h
  simp only [energy,mulVec_add,add_dotProduct,dotProduct_add]
  linarith

theorem energy_clique (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V)
    (hc : ∀ i∈C, ∀ j∈C, i≠j → G.Adj i j) (w : C → ℝ) :
    energy G (extend C w) = ((mass w)^2-∑ i, (w i)^2)/2 := by
  have hrow (i : C) : ((G.adjMatrix ℝ)*ᵥ extend C w) i = mass w - w i := by
    have hdot : ((G.adjMatrix ℝ)*ᵥ extend C w) i = extend C w ⬝ᵥ (G.adjMatrix ℝ i) :=
      dotProduct_comm ..
    rw [hdot, extend_dot]
    have e : ∀ j : C, w j * (G.adjMatrix ℝ) i j = if j=i then 0 else w j := by
      intro j
      by_cases h : j=i
      · subst j; simp
      · have adj := hc i i.prop j j.prop (fun e => h (Subtype.ext e.symm))
        simp [h,SimpleGraph.adjMatrix_apply,adj]
    simp_rw [e]
    rw [← Finset.sum_erase_add _ (fun j => if j=i then 0 else w j) (Finset.mem_univ i)]
    have eh := Finset.sum_erase_add (Finset.univ : Finset C) w (Finset.mem_univ i)
    have hh : ∑ j ∈ (Finset.univ.erase i), (if j=i then 0 else w j) = ∑ j ∈ Finset.univ.erase i,w j :=
      Finset.sum_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)
    simp only [hh,ite_true,add_zero,mass]
    linarith
  simp only [energy,extend_dot,hrow,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul, mass,pow_two]

noncomputable def affine (k : ℝ) (a w : V → ℝ) := k + a ⬝ᵥ w

noncomputable def fixedScore (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (s r : ℝ) :=
    energy G (indic A) - s*A.card - r*(r+1)/2

noncomputable def weight (G : SimpleGraph V) [DecidableRel G.Adj] (A C : Finset V) (s r : ℝ) (i : C) :=
    r + ((G.adjMatrix ℝ)*ᵥ indic A) i - s

noncomputable def surrogate (G : SimpleGraph V) [DecidableRel G.Adj] (A C : Finset V) (s r : ℝ) :=
  affine (fixedScore G A s r) (weight G A C s r)

theorem affine_identity (G : SimpleGraph V) [DecidableRel G.Adj] (A C : Finset V) (s r : ℝ)
    (w : C → ℝ) (hc : ∀ i∈C, ∀ j∈C, i≠j → G.Adj i j) :
    surrogate G A C s r w =
    energy G (indic A+extend C w)-s*((A.card:ℝ)+mass w) +
    r*mass w-r*(r+1)/2-((mass w)^2-∑ i, (w i)^2)/2 := by
  rw [energy_add,energy_clique G C hc,extend_dot]
  simp only [surrogate,affine,fixedScore,weight,dotProduct,sub_mul,add_mul,
    Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,mass]
  simp_rw [mul_comm (((G.adjMatrix ℝ)*ᵥ indic A) _) (w _)]
  ring


def Integral (w : V → ℝ) := ∀ i, w i = 0 ∨ w i = 1
def Almost (w : V → ℝ) := ∀ i ∈ fracs w, ∀ j ∈ fracs w, i=j

theorem integral_of_no_frac {w : V → ℝ} (hw : Box w) (i : V) (hi : i ∉ fracs w) :
    w i=0 ∨ w i=1 := by
  have := hw i
  simp only [mem_fracs] at hi
  rcases eq_or_lt_of_le this.1 with e|h
  · exact Or.inl e.symm
  · exact Or.inr (this.2.antisymm (le_of_not_gt (fun h' => hi ⟨h,h'⟩)))

theorem affine_move (k : ℝ) (a x : V → ℝ) (i j : V) (u v : ℝ) :
    affine k a (move x i j u v) = affine k a x + a i*u + a j*v := by
  simp [affine,move,dotProduct_add,dotProduct_single,add_assoc]

theorem pivotAffine (a b x : V → ℝ) (hx : Box x) :
    ∃ y, Box y ∧ Almost y ∧ a ⬝ᵥ x ≤ a ⬝ᵥ y ∧ b ⬝ᵥ x ≤ b ⬝ᵥ y := by
  let P := fun y => Box y ∧ a ⬝ᵥ x ≤ a ⬝ᵥ y ∧ b ⬝ᵥ x ≤ b ⬝ᵥ y
  obtain ⟨y,hy,hm⟩ := exists_minimalFor_of_wellFoundedLT P (fun y => (fracs y).card)
    (show ∃ y, P y from ⟨x,hx,le_rfl,le_rfl⟩)
  refine ⟨y,hy.1,?_,hy.2⟩
  intro i hi j hj
  by_contra hn
  obtain ⟨u,v,hv,da,db⟩ := twoSlopes (a i) (a j) (b i) (b j)
  obtain ⟨T,hT,hl,hB⟩ := pivotBox hy.1 hn hi hj hv
  have inc (c : V → ℝ) (hc : 0 ≤ c i*u+c j*v) :
      c ⬝ᵥ y ≤ c ⬝ᵥ move y i j (T*u) (T*v) := by
    have h := affine_move 0 c y i j (T*u) (T*v)
    simp only [affine,zero_add] at h
    linarith only [h,mul_nonneg hT.le hc]
  have hp : P (move y i j (T*u) (T*v)) :=
    ⟨hB T ⟨hT.le,le_rfl⟩,hy.2.1.trans (inc a da),hy.2.2.trans (inc b db)⟩
  exact hl.not_ge (hm hp hl.le)

theorem dot_flip (a x : V → ℝ) : a ⬝ᵥ flip x = (∑ i, a i) - a ⬝ᵥ x := by
  simp [dotProduct,flip,mul_sub,Finset.sum_sub_distrib]

theorem flip_flip (x : V → ℝ) : flip (flip x) = x := by ext i; simp [flip]

def adjust (w : V → ℝ) (i : V) (d : ℝ) := w + Pi.single i d

theorem adjust_affine (k : ℝ) (a w : V → ℝ) (i : V) (d : ℝ) :
    affine k a (adjust w i d) = affine k a w + a i*d := by
  simp [adjust,affine,dotProduct_add,dotProduct_single,add_assoc]

theorem adjust_mass (w : V → ℝ) (i : V) (d : ℝ) :
    mass (adjust w i d) = mass w + d := by
  simp [mass,adjust,Finset.sum_add_distrib,Pi.single_apply]

theorem adjust_flip (w : V → ℝ) (i : V) (d : ℝ) :
    flip (adjust w i d) = adjust (flip w) i (-d) := by
  ext j; by_cases h : i=j <;> simp [flip,adjust,h] <;> ring

theorem adjust_integral {w : V → ℝ} (hw : Box w) (ha : Almost w) {i : V}
    (hi : i∈fracs w) {d : ℝ} (h : w i+d=0 ∨ w i+d=1) : Integral (adjust w i d) := by
  intro j
  by_cases e : i=j
  · subst j; simpa [adjust] using h
  · simpa [adjust,e] using integral_of_no_frac hw j (fun hj => e (ha i hi j hj))

theorem integral_flip {w : V → ℝ} (hw : Integral w) : Integral (flip w) := by
  intro i
  rcases hw i with h|h <;> simp [flip,h]

noncomputable def ones (w : V → ℝ) : Finset V := by classical exact univ.filter fun i => w i=1

@[simp] theorem mem_ones {w : V → ℝ} {i : V} : i∈ones w ↔ w i=1 := by classical simp [ones]

theorem integral_eq_indic {w : V → ℝ} (hw : Integral w) : w = indic (ones w) := by
  ext i; rcases hw i with h|h <;> simp [indic,h]

theorem mass_ones {w : V → ℝ} (hw : Integral w) : mass w = (ones w).card := by
  calc mass w = mass (indic (ones w)) := congrArg mass (integral_eq_indic hw)
       _ = _ := mass_indic _

theorem mass_flip (w : V → ℝ) : mass (flip w) = (Fintype.card V : ℝ) - mass w := by
  simp [mass,flip,Finset.sum_sub_distrib]

theorem mass_box {w : V → ℝ} (hw : Box w) : 0 ≤ mass w ∧ mass w ≤ Fintype.card V := by
  refine ⟨Finset.sum_nonneg fun i _ => (hw i).1,?_⟩
  simpa [mass] using sum_le_sum (s := (univ : Finset V)) (fun i _ => (hw i).2)

theorem colorDecomp {x : V → ℝ} (hx : Box x) (C : Finset V)
    (he : ∀ i, i∈C ↔ 0<x i ∧ x i<1) :
    x = indic (ones x) + extend C (fun i => x i) := by
  ext i
  by_cases hi : i ∈ C
  · have h := (he i).mp hi
    simp [extend,indic,hi,ne_of_lt h.2]
  · have h := integral_of_no_frac hx i (fun hm => hi ((he i).mpr (mem_fracs.mp hm)))
    rcases h with h|h <;> simp [extend,indic,hi,h]

theorem mass_parts (A C : Finset V) (w : C → ℝ) :
    mass (indic A + extend C w) = (A.card:ℝ)+mass w := by
  simp only [mass,Pi.add_apply,Finset.sum_add_distrib,sum_extend]
  rw [← mass, mass_indic]

theorem initial_surrogate (G : SimpleGraph V) [DecidableRel G.Adj] {s t r : ℝ}
    (A C : Finset V) (w : C → ℝ) (hC : C.Nonempty)
    (hcl : ∀ i∈C, ∀ j∈C, i≠j → G.Adj i j)
    (hg : Good G s t (indic A + extend C w)) (hr : r ≤ mass w) (hr' : mass w ≤ r+1) :
    (A.card:ℝ)/2+(mass w)^2/(2*C.card)-(s+1/2)^2/(s+t+1) < surrogate G A C s r w := by
  have hscore := hg.2
  simp only [score,mass_parts] at hscore
  have hpos : (0:ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hcs : (mass w)^2 ≤ C.card * ∑ i, (w i)^2 := by
    simpa [mass] using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := w))
  have h := cliqueGain (a := A.card) hpos hr hr' hcs
  rw [affine_identity G A C s r w hcl]
  convert add_lt_add_of_le_of_lt h hscore using 1 <;> first | rfl | ring


structure Side (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) (w : C → ℝ) (s t : ℝ) where
  fixed : Finset V
  dis : Disjoint fixed C
  index : ℤ
  lo : (index : ℝ) ≤ mass w
  hi : mass w ≤ (index : ℝ)+1
  good : Good G s t (indic fixed + extend C w)

namespace Side
variable {G : SimpleGraph V} [DecidableRel G.Adj] {C : Finset V} {w : C → ℝ} {s t : ℝ}

noncomputable def val (S : Side G C w s t) := surrogate G S.fixed C s S.index

theorem sum_bound (S : Side G C w s t) : s ≤ (S.index : ℝ)+S.fixed.card := by
  have h := S.good.1
  rw [mass_parts] at h
  linarith only [S.hi,h]

theorem lower (S : Side G C w s t) (hc : C.Nonempty) (hcl : ∀ i∈C, ∀ j∈C, i≠j → G.Adj i j) :
    (S.fixed.card : ℝ)/2+(mass w)^2/(2*C.card)-(s+1/2)^2/(s+t+1) < S.val w :=
  initial_surrogate G S.fixed C w hc hcl S.good S.lo S.hi

theorem lower_simple (S : Side G C w s t) (hs : 1 ≤ s) (ht : 1 ≤ t) (hc : C.Nonempty)
    (hcl : ∀ i∈C, ∀ j∈C, i≠j → G.Adj i j) : -s < S.val w := by
  have h := S.lower hc hcl
  have e : 0 ≤ (mass w)^2/(2*C.card) := by positivity
  have ea : 0 ≤ (S.fixed.card:ℝ) := by positivity
  linarith only [h,e,ea,baseBound hs ht]

theorem near (S : Side G C w s t) (hs : 1 ≤ s) (ht : 1 ≤ t) (hc : C.Nonempty)
    (hcl : ∀ i∈C, ∀ j∈C, i≠j → G.Adj i j) (hw : Box w)
    (hq : mass w ≤ 2*s+1) (hv : mass (flip w) ≤ 2*t+1)
    (y : C → ℝ) (hy : S.val w ≤ S.val y) (i : C) {d : ℝ} (hd : -(1/2) ≤ d ∧ d ≤ 1/2) :
    -s < S.val (adjust y i d) := by
  let q := mass w
  let v := mass (flip w)
  have he : q+v = C.card := by dsimp [q,v]; rw [mass_flip,Fintype.card_coe]; ring
  have hc' : (0 : ℝ) < C.card := by exact_mod_cast hc.card_pos
  have hc2 := he.trans_gt hc'
  let a := (S.fixed.card : ℝ)
  let deg := ((G.adjMatrix ℝ)*ᵥ indic S.fixed) i.val
  have hdeg : 0 ≤ deg := by dsimp [deg]; rw [degreeIndic]; positivity
  have hda : deg ≤ a := by
    dsimp [deg,a]; rw [degreeIndic]; exact_mod_cast Finset.card_le_card (Finset.inter_subset_right)
  have change : S.val (adjust y i d) = S.val y+((S.index:ℝ)+deg-s)*d := adjust_affine .. 
  have hF := (S.lower hc hcl).trans_le hy
  rcases le_total d 0 with h|h
  · apply lastDown (r := (S.index : ℝ)) (a := a) (x := -d) (d := deg) hs ht
      (mass_box hw).1 (mass_box (box_flip hw)).1 hc2 hq hv S.lo S.sum_bound hda
      (by linarith) (by linarith [hd.1]) (he.symm ▸ hF)
    linarith only [change]
  · exact lastUp hs ht hc' (show 0 ≤ a by dsimp [a]; positivity) hdeg S.sum_bound h hd.2 hF change

noncomputable def chosen (S : Side G C w s t) (y : C → ℝ) :=
  S.fixed ∪ (ones y).map (Function.Embedding.subtype fun i => i∈C)

theorem selected_eq (S : Side G C w s t) {y : C → ℝ} (iy : Integral y) :
    indic (S.chosen y) = indic S.fixed + extend C y := by
  ext i
  by_cases hi : i∈C
  · have hf : i ∉ S.fixed := fun h => Finset.disjoint_left.mp S.dis h hi
    have eq : i ∈ S.chosen y ↔ y ⟨i,hi⟩=1 := by
      simp only [chosen,Finset.mem_union,hf,false_or,Finset.mem_map]
      constructor
      · rintro ⟨⟨k,hk⟩,hm,rfl⟩; exact mem_ones.mp hm
      · intro h; exact ⟨⟨i,hi⟩,mem_ones.mpr h,rfl⟩
    rcases iy ⟨i,hi⟩ with h|h <;> simp [indic,extend,hi,hf,eq,h]
  · have eq : i∈S.chosen y ↔ i∈S.fixed := by
      simp only [chosen,Finset.mem_union,Finset.mem_map]
      constructor
      · rintro (h|⟨⟨k,hk⟩,_,rfl⟩)
        · exact h
        · exact False.elim (hi hk)
      · exact Or.inl
    simp [indic,extend,hi,eq]

theorem denseChosen (S : Side G C w s t) (hs : 1 ≤ s)
    (hcl : ∀ i∈C, ∀ j∈C, i≠j → G.Adj i j) {y : C → ℝ} (iy : Integral y) (hle : -s < S.val y) :
    (S.chosen y).Nonempty ∧ Dense (G.induce (S.chosen y : Set V)) s := by
  let A := S.fixed
  let P := S.chosen y
  have eq := S.selected_eq iy
  have hm : (P.card : ℝ) = A.card+mass y := by
    rw [← mass_indic,eq,mass_parts]
  have hi : S.val y = energy G (indic P)-s*P.card+
      (S.index:ℝ)*mass y-(S.index:ℝ)*(S.index+1)/2-((mass y)^2-∑ i, (y i)^2)/2 := by
    rw [val,affine_identity G _ _ _ _ _ hcl,← eq,hm]
  have he : ∑ i, (y i)^2 = mass y := by
    apply Finset.sum_congr rfl; intro i _; rcases iy i with h|h <;> simp [h]
  have hp : 2*(S.index : ℝ)*mass y-(S.index:ℝ)*(S.index+1) ≤ mass y*(mass y-1) := by
    rw [mass_ones iy]
    exact_mod_cast chordOnInteger S.index ((ones y).card : ℤ)
  have hed : s*((P.card:ℝ)-1) < energy G (indic P) := by
    rw [he] at hi
    linarith only [hi,hp,hle]
  constructor
  · by_contra! hem
    have hp0 : P = ∅ := hem
    have hA : A = ∅ := Finset.subset_empty.mp (hp0 ▸ Finset.subset_union_left (s₂ := (ones y).map _))
    have hm0 : mass y = 0 := by rw [hA,hp0] at hm; simpa using hm.symm
    have hS := S.sum_bound
    change s ≤ (S.index:ℝ)+A.card at hS
    rw [hA] at hS
    simp only [Finset.card_empty,Nat.cast_zero,add_zero] at hS
    have hz : energy G (indic P) = 0 := by rw [hp0]; simp [energy,indic,dotProduct]
    rw [he,hm0,hz,hp0] at hi
    simp at hi
    nlinarith only [hi,hle,hS,hs,mul_nonneg (show 0 ≤ (S.index:ℝ) by linarith)
      (show 0 ≤ (S.index:ℝ)-1 by linarith)]
  · rw [energy_indic] at hed
    simpa only [Dense,← SimpleGraph.card_edgeSet,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Set.ncard_coe_finset] using hed
end Side


theorem roundPair (G : SimpleGraph V) [DecidableRel G.Adj] {C : Finset V} {w : C → ℝ}
    {s t : ℝ} (S : Side G C w s t) (T : Side G C (flip w) t s)
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hc : C.Nonempty)
    (hcl : ∀ i∈C, ∀ j∈C, i≠j → G.Adj i j) (hw : Box w)
    (h1 : mass w ≤ 2*s+1) (h2 : mass (flip w) ≤ 2*t+1) :
    ∃ y, Integral y ∧ -s < S.val y ∧ -t < T.val (flip y) := by
  let a := weight G S.fixed C s S.index
  let b := weight G T.fixed C t T.index
  obtain ⟨y,hy,hay,ha,hb⟩ := pivotAffine a (-b) w hw
  have hS : S.val w ≤ S.val y := add_le_add_right ha _
  have hb' : b ⬝ᵥ flip w ≤ b ⬝ᵥ flip y := by
    simp only [neg_dotProduct] at hb
    simp only [dot_flip]; linarith
  have hT : T.val (flip w) ≤ T.val (flip y) := add_le_add_right hb' _
  by_cases hf : (fracs y).Nonempty
  · obtain ⟨i,hi⟩ := hf
    let d := if y i ≤ 1/2 then -y i else 1-y i
    have hx := mem_fracs.mp hi
    have hd : -(1/2) ≤ d ∧ d ≤ 1/2 := by dsimp [d]; split <;> constructor <;> linarith
    have hend : y i+d=0 ∨ y i+d=1 := by dsimp [d]; split <;> simp
    refine ⟨adjust y i d,adjust_integral hy hay hi hend,S.near hs ht hc hcl hw h1 h2 y hS i hd,?_⟩
    rw [adjust_flip]
    exact T.near ht hs hc hcl (box_flip hw) h2 (by simpa [flip_flip] using h1) _ hT i
      ⟨by linarith [hd.2], by linarith [hd.1]⟩
  · exact ⟨y,fun i => integral_of_no_frac hy i (fun h => hf ⟨i,h⟩),
      (S.lower_simple hs ht hc hcl).trans_le hS,(T.lower_simple ht hs hc hcl).trans_le hT⟩

theorem roundSparse (G : SimpleGraph V) [DecidableRel G.Adj] {C : Finset V} {w : C → ℝ}
    {s t : ℝ} (S : Side G C w s t) (hs : 1 ≤ s) (ht : 1 ≤ t) (hc : C.Nonempty)
    (hcl : ∀ i∈C, ∀ j∈C, i≠j → G.Adj i j) (hw : Box w) :
    ∃ y, Integral y ∧ -s < S.val y ∧ mass y ≤ (S.index:ℝ)+1 := by
  let a := weight G S.fixed C s S.index
  obtain ⟨y,hy,hay,ha,hb⟩ := pivotAffine a (fun _ => -1) w hw
  have hS : S.val w ≤ S.val y := add_le_add_right ha _
  have leM : mass y ≤ mass w := by simpa [mass,dotProduct] using hb
  have hF := (S.lower_simple hs ht hc hcl).trans_le hS
  by_cases hf : (fracs y).Nonempty
  · obtain ⟨i,hi⟩ := hf
    let d := if 0 ≤ a i then 1-y i else -y i
    have hx := mem_fracs.mp hi
    have hd : d < 1 ∧ 0 ≤ a i*d := by
      dsimp [d]; split
      · exact ⟨by linarith,mul_nonneg ‹_› (by linarith)⟩
      · exact ⟨by linarith,mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)⟩
    have hend : y i+d=0 ∨ y i+d=1 := by dsimp [d]; split <;> simp
    let z := adjust y i d
    have iz : Integral z := adjust_integral hy hay hi hend
    refine ⟨z,iz,?_,?_⟩
    · have e : S.val z = S.val y+a i*d := adjust_affine ..
      linarith [hd.2]
    · have hm : mass z = mass y + d := adjust_mass .. 
      have h : mass z < (S.index:ℝ)+2 := by linarith only [hm,hd.1,S.hi,leM]
      rw [mass_ones iz] at h ⊢
      have hz : ((ones z).card : ℤ) < S.index+2 := by exact_mod_cast h
      exact_mod_cast (show ((ones z).card : ℤ) ≤ S.index+1 by omega)
  · exact ⟨y,fun i => integral_of_no_frac hy i (fun h => hf ⟨i,h⟩),hF,leM.trans S.hi⟩

noncomputable def pixels (C : Finset V) (y : C → ℝ) : Finset V :=
    (ones y).map (Function.Embedding.subtype fun i => i∈C)

theorem pix_sub (C : Finset V) (y : C → ℝ) : pixels C y ⊆ C := by
  intro i hi; obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi; exact j.property

theorem pix_dis (C : Finset V) (y : C → ℝ) : Disjoint (pixels C y) (pixels C (flip y)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨j,hj1,rfl⟩ := Finset.mem_map.mp hi
  obtain ⟨k,hk,he⟩ := Finset.mem_map.mp hj
  have eq : k=j := Subtype.ext he
  subst k
  have h := mem_ones.mp hj1
  have h' := mem_ones.mp hk
  simp [flip,h] at h'

def SplitAt (G : SimpleGraph V) (s t : ℝ) : Prop :=
    ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      Dense (G.induce (A : Set V)) s ∧ Dense (G.induce (B : Set V)) t

theorem splitSwap (G : SimpleGraph V) {s t : ℝ} (h : SplitAt G s t) : SplitAt G t s := by
  obtain ⟨A,B,ha,hb,hd,h1,h2⟩ := h
  exact ⟨B,A,hb,ha,hd.symm,h2,h1⟩

theorem largeCliqueDense (G : SimpleGraph V) [DecidableRel G.Adj] {K : Finset V} {t : ℝ}
    (ht : 1 ≤ t) (hk : 2*t < K.card) (hcl : ∀ i∈K, ∀ j∈K, i≠j → G.Adj i j) :
    K.Nonempty ∧ Dense (G.induce (K : Set V)) t := by
  have h : (1 : ℝ) < K.card := by linarith
  have h0 : 0 < K.card := by exact_mod_cast (show (0:ℝ) < K.card by linarith)
  refine ⟨Finset.card_pos.mp h0,?_⟩
  have eq : indic K = extend K (fun _ => 1) := by ext i; by_cases hi : i∈K <;> simp [indic,extend,hi]
  have he := energy_clique G K hcl (fun _ => 1)
  rw [← eq,energy_indic] at he
  simp [mass] at he
  have hed : t*((K.card:ℝ)-1) < ((G.induce (K:Set V)).edgeFinset.card : ℝ) := by
    nlinarith only [he,mul_lt_mul_of_pos_right hk (sub_pos.mpr h)]
  simpa only [Dense,← SimpleGraph.card_edgeSet,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Set.ncard_coe_finset] using hed

theorem largeSplit (G : SimpleGraph V) [DecidableRel G.Adj] {C : Finset V} {w : C → ℝ}
    {s t : ℝ} (S : Side G C w s t) (hs : 1 ≤ s) (ht : 1 ≤ t) (hc : C.Nonempty)
    (hcl : ∀ i∈C, ∀ j∈C, i≠j → G.Adj i j) (hw : Box w)
    (hlarge : 2*t < (C.card:ℝ)-S.index-1) : SplitAt G s t := by
  obtain ⟨y,iy,hF,hm⟩ := roundSparse G S hs ht hc hcl hw
  obtain ⟨hA,hD⟩ := S.denseChosen hs hcl iy hF
  let K := pixels C (flip y)
  have hk : (K.card:ℝ) = C.card-mass y := by
    rw [show K.card = (ones (flip y)).card from Finset.card_map _,← mass_ones (integral_flip iy),
      mass_flip,Fintype.card_coe]
  have hsub := pix_sub C (flip y)
  obtain ⟨hK,hDK⟩ := largeCliqueDense G ht (show 2*t < (K.card:ℝ) by linarith)
    (fun i hi j hj => hcl i (hsub hi) j (hsub hj))
  exact ⟨S.chosen y,K,hA,hK,Finset.disjoint_union_left.mpr ⟨S.dis.mono_right hsub,pix_dis C y⟩,hD,hDK⟩


theorem goodIntegral (G : SimpleGraph V) [DecidableRel G.Adj] {s t : ℝ}
    (hs : 1 ≤ s) (ht : 1 ≤ t) {x : V → ℝ} (hg : Good G s t x) (ix : Integral x) :
    (ones x).Nonempty ∧ Dense (G.induce (ones x : Set V)) s := by
  have hm := hg.1
  have he := hg.2
  unfold score at he
  rw [mass_ones ix] at he hm
  have e : energy G x = ((G.induce (ones x : Set V)).edgeFinset.card : ℝ) :=
    (congrArg (energy G) (integral_eq_indic ix)).trans (energy_indic G _)
  rw [e,neg_div] at he
  have hp : (0:ℝ) < (ones x).card := by linarith
  have hh : s*(((ones x).card:ℝ)-1) < ((G.induce (ones x:Set V)).edgeFinset.card:ℝ) := by
    linarith only [he,hp,baseBound hs ht]
  exact ⟨Finset.card_pos.mp (by exact_mod_cast hp),by
    simpa only [Dense,← SimpleGraph.card_edgeSet,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Set.ncard_coe_finset] using hh⟩

theorem densitySplit [Nonempty V] (G : SimpleGraph V) (s t : ℝ) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hd : Dense G (s+t+1)) : SplitAt G s t := by
  classical
  obtain ⟨x,hx,hg,hg',hcl⟩ := fractionalClique G hs ht hd
  let C := fracs x
  have hAB : Disjoint (ones x) (ones (flip x)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h := mem_ones.mp hi
    have e := mem_ones.mp hj
    simp [flip,h] at e
  by_cases hc : C.Nonempty
  · let w : C → ℝ := fun i => x i
    have hw : Box w := fun i => hx i
    have eq := colorDecomp hx C (fun _ => mem_fracs)
    have memflip (i : V) : i∈C ↔ 0 < flip x i ∧ flip x i < 1 := by
      change i∈fracs x ↔ _
      rw [mem_fracs]; dsimp [flip]; constructor <;> rintro ⟨h,h'⟩ <;> constructor <;> linarith
    have eq' := colorDecomp (box_flip hx) C memflip
    let r := ⌊mass w⌋
    let r' : ℤ := C.card-r-1
    have lo : (r:ℝ) ≤ mass w := Int.floor_le _
    have hi : mass w ≤ (r:ℝ)+1 := (Int.lt_floor_add_one _).le
    have he : (r':ℝ) = (C.card:ℝ)-r-1 := by dsimp [r']; push_cast; ring
    have hm : mass (flip w) = (C.card:ℝ)-mass w := by rw [mass_flip,Fintype.card_coe]
    let S : Side G C w s t := {
      fixed := ones x
      dis := Finset.disjoint_left.mpr fun i h h' =>
        (mem_fracs.mp h').2.ne (mem_ones.mp h)
      index := r
      lo := lo
      hi := hi
      good := eq ▸ hg }
    let T : Side G C (flip w) t s := {
      fixed := ones (flip x)
      dis := Finset.disjoint_left.mpr fun i h h' =>
        ((memflip i).mp h').2.ne (mem_ones.mp h)
      index := r'
      lo := by rw [he,hm]; linarith
      hi := by rw [he,hm]; linarith
      good := eq' ▸ hg' }
    by_cases hlar : 2*t < (r':ℝ)
    · exact largeSplit G S hs ht hc hcl hw (he ▸ hlar)
    by_cases hlar' : 2*s < (r:ℝ)
    · apply splitSwap G
      apply largeSplit G T ht hs hc hcl (box_flip hw)
      change 2*s < (C.card:ℝ)-r'-1
      linarith
    obtain ⟨y,iy,hS,hT⟩ := roundPair G S T hs ht hc hcl hw (by linarith) (by linarith)
    obtain ⟨ha,hda⟩ := S.denseChosen hs hcl iy hS
    obtain ⟨hb,hdb⟩ := T.denseChosen ht hcl (integral_flip iy) hT
    refine ⟨_,_,ha,hb,Finset.disjoint_union_left.mpr ⟨?_,?_⟩,hda,hdb⟩
    · exact Finset.disjoint_union_right.mpr ⟨hAB,S.dis.mono_right (pix_sub C _)⟩
    · exact Finset.disjoint_union_right.mpr ⟨(T.dis.mono_right (pix_sub C _)).symm,pix_dis C y⟩
  · have ix : Integral x := fun i => integral_of_no_frac hx i (fun h => hc ⟨i,h⟩)
    obtain ⟨ha,hda⟩ := goodIntegral G hs ht hg ix
    obtain ⟨hb,hdb⟩ := goodIntegral G ht hs hg' (integral_flip ix)
    exact ⟨_,_,ha,hb,hAB,hda,hdb⟩
end Wave10G


namespace Wave10G
open SimpleGraph

theorem cycleMinor (t : ℕ) (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (hr : H.IsRegularOfDegree 2) (hH : H.Connected) (V : Type) (G : SimpleGraph V)
    (u : V) (c : G.Walk u u) (hcy : c.IsCycle) (hsize : t ≤ c.length) :
    ∃ B : Fin t → Set V, (∀ i, (G.induce (B i)).Connected) ∧
      (Pairwise fun i j => Disjoint (B i) (B j)) ∧
      ∀ i j, H.Adj i j → ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y := by
  classical
  obtain ⟨b⟩ := hH.nonempty
  have hcycles : H.IsCycles := by
    intro i _
    rw [Set.ncard_eq_toFinset_card',← H.neighborFinset_def,H.card_neighborFinset_eq_degree,hr]
  obtain ⟨p,hp,hverts⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := H.connectedComponentMk b) (v := b) (by rfl)
    (H.degree_pos_iff_nonempty.mp (show 0 < H.degree b by rw [hr]; decide))
  have hall (i : Fin t) : i∈p.toSubgraph.verts := hverts ▸ ConnectedComponent.sound (hH i b)
  have hpos := hp.three_le_length
  have cover (i : Fin t) : ∃ n < p.length, p.getVert n = i := by
    obtain ⟨n,e,h⟩ := Walk.mem_support_iff_exists_getVert.mp (p.mem_verts_toSubgraph.mp (hall i))
    rcases lt_or_eq_of_le h with h|rfl
    · exact ⟨n,h,e⟩
    · exact ⟨0,by omega,by simpa using e⟩
  have hbij : Function.Bijective (fun n : Fin p.length => p.getVert n.val) := by
    constructor
    · intro i j e
      apply Fin.ext
      exact hp.getVert_injOn' (show i.val ≤ p.length-1 by omega) (show j.val ≤ p.length-1 by omega) e
    · intro i; obtain ⟨n,h,e⟩ := cover i; exact ⟨⟨n,h⟩,e⟩
  have hlen : p.length=t := by simpa using Fintype.card_congr (Equiv.ofBijective _ hbij)
  let idx := fun n : ℕ => min n (p.length-1)
  let lab := fun n : ℕ => p.getVert (idx n)
  let B := fun i : Fin t => {z : V | ∃ n < c.length, lab n=i ∧ c.getVert n=z}
  have mem (n : ℕ) (hn : n<c.length) : c.getVert n ∈ B (lab n) := ⟨n,hn,rfl,rfl⟩
  have basic (n : ℕ) (hn : n<p.length) : lab n=p.getVert n := by
    dsimp [lab,idx]; rw [min_eq_left (by omega)]
  refine ⟨B,?_,?_,?_⟩
  · intro i
    obtain ⟨k,hk,hki⟩ := cover i
    let z := c.getVert k
    have start : z ∈ B i := ⟨k,by omega,(basic k hk).trans hki,rfl⟩
    apply (connected_iff_exists_forall_reachable _).mpr
    refine ⟨⟨z,start⟩,?_⟩
    rintro ⟨v,n,hn,hi,rfl⟩
    have ei : idx n=k := hp.getVert_injOn' (show idx n ≤ p.length-1 from min_le_right ..)
      (show k ≤ p.length-1 by omega) (hi.trans hki.symm)
    have hkn : k≤n := ei ▸ min_le_left ..
    have inside (j : ℕ) (h1 : k≤j) (h2 : j≤n) : c.getVert j ∈ B i := by
      refine ⟨j,by omega,?_,rfl⟩
      have e : idx j=k := by dsimp [idx] at ei ⊢; omega
      exact (congrArg p.getVert e).trans hki
    have path (j : ℕ) (h1 : k≤j) (h2 : j≤n) : (G.induce (B i)).Reachable
        ⟨z,start⟩ ⟨c.getVert j,inside j h1 h2⟩ := by
      induction j, h1 using Nat.le_induction with
      | base => exact Reachable.refl _
      | succ j h ih =>
        have edge : (G.induce (B i)).Adj ⟨c.getVert j,inside j h (by omega)⟩
            ⟨c.getVert (j+1),inside _ (by omega) h2⟩ := c.adj_getVert_succ (by omega)
        exact (ih (by omega)).trans edge.reachable
    exact path n hkn le_rfl
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨m,hm,hmi,rfl⟩ ⟨n,hn,hnj,eq⟩
    have e : n=m := hcy.getVert_injOn' (show n ≤ c.length-1 by omega)
      (show m ≤ c.length-1 by omega) eq
    exact hij (hmi.symm.trans (e ▸ hnj))
  · intro i j hij
    obtain ⟨n,he,hn⟩ := p.toSubgraph_adj_iff.mp ((hp.adj_toSubgraph_iff_of_isCycles hcycles (hall i) j).mpr hij)
    have along : ∃ x ∈ B (p.getVert n), ∃ y ∈ B (p.getVert (n+1)), G.Adj x y := by
      by_cases h : n+1<p.length
      · rw [← basic n hn,← basic (n+1) h]
        exact ⟨_,mem n (by omega),_,mem _ (by omega),c.adj_getVert_succ (by omega)⟩
      · have last : n+1=p.length := by omega
        have el : idx (c.length-1)=n := by dsimp [idx]; omega
        rw [last,p.getVert_length]
        refine ⟨c.getVert (c.length-1),⟨_,by omega,congrArg p.getVert el,rfl⟩,c.getVert 0,?_,?_⟩
        · exact ⟨0,by omega,by simp [lab,idx],rfl⟩
        · simpa [Nat.sub_add_cancel (show 1 ≤ c.length by omega)] using
            c.adj_getVert_succ (i := c.length-1) (by omega)
    obtain ⟨x,hx,y,hy,hxy⟩ := along
    rcases Sym2.eq_iff.mp he with ⟨ei,ej⟩|⟨ei,ej⟩
    · exact ⟨x,ei ▸ hx,y,ej ▸ hy,hxy⟩
    · exact ⟨y,ej ▸ hy,x,ei ▸ hx,hxy.symm⟩
end Wave10G


namespace OMA.S_opg_forcing_a_2_regular_minor
/-- Transport a connected branch set out of the induced host. -/
theorem connected_image_val {V : Type*} (G : SimpleGraph V) (A : Set V) (P : Set A)
    (h : ((G.induce A).induce P).Connected) :
    (G.induce (Subtype.val '' P : Set V)).Connected := by
  let f : (G.induce A).induce P →g G.induce (Subtype.val '' P : Set V) :=
    { toFun := fun x => ⟨x.val.val, x.val, x.property, rfl⟩
      map_rel' := fun hxy => hxy }
  apply h.map f
  rintro ⟨w, x, hx, rfl⟩
  exact ⟨⟨x,hx⟩, rfl⟩

/-- Glue two real minor models. The target cut has no edges across it, while the
    two host sets need only be disjoint. -/
theorem joinMinor {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V)
    (S : Set W) (A B : Set V) (hAB : Disjoint A B)
    (hcut : ∀ {u v}, H.Adj u v → (u ∈ S ↔ v ∈ S))
    (ha : IsMinor (H.induce S) (G.induce A))
    (hb : IsMinor (H.induce Sᶜ) (G.induce B)) : IsMinor H G := by
  classical
  obtain ⟨P,hP,dP,eP⟩ := ha
  obtain ⟨Q,hQ,dQ,eQ⟩ := hb
  let F (i : W) : Set V := if hi : i ∈ S then Subtype.val '' P ⟨i,hi⟩
    else Subtype.val '' Q ⟨i,hi⟩
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ S
    · rw [show F i = Subtype.val '' P ⟨i,hi⟩ from dif_pos hi]
      exact connected_image_val G A _ (hP ⟨i,hi⟩)
    · rw [show F i = Subtype.val '' Q ⟨i,hi⟩ from dif_neg hi]
      exact connected_image_val G B _ (hQ ⟨i,hi⟩)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro w hw₁ hw₂
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp only [F, hi, hj, dif_pos, dif_neg, not_false_eq_true] at hw₁ hw₂ <;>
      obtain ⟨u,hu,rfl⟩ := hw₁ <;> obtain ⟨v,hv,he⟩ := hw₂
    · have h := Subtype.ext he
      subst v
      exact Set.disjoint_left.mp (dP (show (⟨i,hi⟩ : S) ≠ ⟨j,hj⟩ from
        fun e => hij (congrArg Subtype.val e))) hu hv
    · exact Set.disjoint_left.mp hAB u.property (he ▸ v.property)
    · exact Set.disjoint_left.mp hAB (he ▸ v.property) u.property
    · have h := Subtype.ext he
      subst v
      exact Set.disjoint_left.mp (dQ (show (⟨i,hi⟩ : ↥(Sᶜ)) ≠ ⟨j,hj⟩ from
        fun e => hij (congrArg Subtype.val e))) hu hv
  · intro i j hij
    by_cases hi : i ∈ S
    · have hj := (hcut hij).mp hi
      obtain ⟨x,hx,y,hy,hxy⟩ := eP ⟨i,hi⟩ ⟨j,hj⟩ hij
      simp only [F, dif_pos hi, dif_pos hj]
      exact ⟨x.val, ⟨x,hx,rfl⟩, y.val, ⟨y,hy,rfl⟩, hxy⟩
    · have hj : j ∉ S := fun h => hi ((hcut hij).mpr h)
      obtain ⟨x,hx,y,hy,hxy⟩ := eQ ⟨i,hi⟩ ⟨j,hj⟩ hij
      simp only [F, dif_neg hi, dif_neg hj]
      exact ⟨x.val, ⟨x,hx,rfl⟩, y.val, ⟨y,hy,rfl⟩, hxy⟩

end OMA.S_opg_forcing_a_2_regular_minor

/-!
Long-cycle proof from GuillaumeBAUD-coder/open-math-agents, R1.H1,
revision 016e777030b158db1cd0abcfe230fa5d1b44006f (#11527, over #11322).
The final adapter exposes the stronger internal induction theorem.

Dirac (1952): a 2-connected graph with minimum degree at least d has a cycle of length at least
min(n, 2d). Take a longest path x 0, ..., x m; S and T index the chords at its two ends.
A crossing pair of chords closes the path into a cycle through all vertices (this part and the
list-cycle lemmas are adapted from philipsaint's proof of Dirac's Hamiltonicity theorem).
If a neighbour of x m precedes a neighbour of x 0, a closest such pair gives a cycle of length at
least |S| + |T|. Otherwise every neighbour of x 0 precedes every neighbour of x m, and a chain of
bridges of the path, each chosen with maximal reach, gives such a cycle.
-/

namespace OMA.EG

open SimpleGraph

/-- Core (Dirac 1952): a 2-connected graph with minimum degree d has a cycle of length
at least min(n, 2d). 2-connectivity is stated as: any two vertices other than v are joined by
a walk avoiding v. -/
def CoreStatement : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ),
    2 ≤ d → 3 ≤ Fintype.card V → G.Connected →
    (∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support) →
    (∀ v, d ≤ G.degree v) →
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ min (Fintype.card V) (2 * d) ≤ c.length

namespace C1


open SimpleGraph

variable {V : Type} {G : SimpleGraph V}

def PL (G : SimpleGraph V) (a : V) (L : List V) (b : V) : Prop :=
  L.IsChain G.Adj ∧ L.head? = some a ∧ L.getLast? = some b

lemma PL.eq_cons {a b : V} {L : List V} (h : PL G a L b) : L = a :: L.tail := by
  obtain ⟨-, h2, -⟩ := h
  cases L with
  | nil => simp at h2
  | cons y L => simp at h2; simp [h2]

lemma PL.length_pos {a b : V} {L : List V} (h : PL G a L b) : 1 ≤ L.length := by
  rw [h.eq_cons]; simp

lemma PL.single (a : V) : PL G a [a] a := ⟨List.isChain_singleton _, rfl, rfl⟩

lemma PL.cons {a b c : V} {L : List V} (hab : G.Adj a b) (h : PL G b L c) :
    PL G a (a :: L) c := by
  obtain ⟨c1, hd, hl⟩ := h
  refine ⟨List.isChain_cons.2 ⟨?_, c1⟩, rfl, ?_⟩
  · intro y hy; rw [hd] at hy; cases hy; exact hab
  · rw [List.getLast?_cons, hl]; rfl

lemma PL.edge {a b : V} (hab : G.Adj a b) : PL G a [a, b] b := PL.cons hab (PL.single b)

lemma PL.append {a b c : V} {L M : List V} (h1 : PL G a L b) (h2 : PL G b M c) :
    PL G a (L ++ M.tail) c := by
  have hM := h2.eq_cons
  have hL := h1.eq_cons
  obtain ⟨c1, hd1, l1⟩ := h1
  obtain ⟨c2, hd2, l2⟩ := h2
  rw [hM] at c2 l2
  rw [List.isChain_cons] at c2
  refine ⟨?_, ?_, ?_⟩
  · rw [List.isChain_append]
    refine ⟨c1, c2.2, ?_⟩
    intro x hx y hy
    rw [l1] at hx; cases hx; exact c2.1 y hy
  · rw [hL]; simp
  · rw [List.getLast?_cons] at l2
    rw [List.getLast?_append]
    rcases h : M.tail.getLast? with _ | z
    · rw [h] at l2; simp at l2; simp [l1, l2]
    · rw [h] at l2; simp at l2; simp [l2]

lemma PL.reverse {a b : V} {L : List V} (h : PL G a L b) : PL G b L.reverse a := by
  obtain ⟨c1, hd, hl⟩ := h
  refine ⟨?_, by rw [List.head?_reverse, hl], by rw [List.getLast?_reverse, hd]⟩
  rw [List.isChain_reverse]
  exact c1.imp (fun _ _ h => h.symm)

lemma length_append_tail {L M : List V} (hM : 1 ≤ M.length) :
    (L ++ M.tail).length = L.length + M.length - 1 := by
  rw [List.length_append, List.length_tail]; omega

lemma mem_append_tail {L M : List V} {v : V} (h : v ∈ L ++ M.tail) : v ∈ L ∨ v ∈ M := by
  rcases List.mem_append.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_of_mem_tail h)

lemma nodup_append_tail {b c : V} {L M : List V} (hL : L.Nodup) (hM : M.Nodup)
    (h2 : PL G b M c) (hcap : ∀ v ∈ L, v ∈ M → v = b) : (L ++ M.tail).Nodup := by
  have hMe := h2.eq_cons
  rw [hMe, List.nodup_cons] at hM
  rw [List.nodup_append]
  refine ⟨hL, hM.2, ?_⟩
  intro v hv w hw hvw
  subst hvw
  have := hcap v hv (by rw [hMe]; exact List.mem_cons_of_mem _ hw)
  subst this
  exact hM.1 hw

/-! Closing a cyclic list into a cycle (adapted from philipsaint's Dirac proof). -/

lemma edge_not_mem {u v : V} (p : G.Walk u v) (hp : p.IsPath) (hlen : 2 ≤ p.length) :
    s(u, v) ∉ p.edges := by
  cases p with
  | nil => simp at hlen
  | @cons _ w _ hadj p' =>
    intro hmem
    rw [Walk.edges_cons, List.mem_cons] at hmem
    have hnd := hp.support_nodup
    rw [Walk.support_cons, List.nodup_cons] at hnd
    rcases hmem with h | h
    · rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · subst h2
        have hp' : p'.IsPath := hp.of_cons
        have : p'.length = 0 := by
          rcases p' with _ | ⟨h'', p''⟩
          · rfl
          · exfalso
            have := hp'.support_nodup
            simp at this
        simp [this] at hlen
      · subst h1
        exact hadj.ne rfl
    · exact hnd.1 (Walk.fst_mem_support_of_mem_edges p' h)

lemma cycle_of_PL {a b : V} {c : List V} (hc : PL G a c b) (hba : G.Adj b a) (hnd : c.Nodup)
    (h3 : 3 ≤ c.length) : ∃ (u : V) (w : G.Walk u u), w.IsCycle ∧ w.length = c.length := by
  have hne : c ≠ [] := by
    rintro rfl
    simp at h3
  obtain ⟨hch, hhd, hlt⟩ := hc
  set W := Walk.ofSupport c hne hch
  have hW : W.support = c := Walk.support_ofSupport hne hch
  have hWl : W.length = c.length - 1 := Walk.length_ofSupport hne hch
  have hpath : W.IsPath := Walk.IsPath.mk' (by rw [hW]; exact hnd)
  have hadj : G.Adj (c.head hne) (c.getLast hne) := by
    have e1 : c.head hne = a := by
      rw [List.head?_eq_some_head hne] at hhd; exact Option.some.inj hhd
    have e2 : c.getLast hne = b := by
      rw [List.getLast?_eq_some_getLast hne] at hlt; exact Option.some.inj hlt
    rw [e1, e2]; exact hba.symm
  refine ⟨c.head hne, Walk.cons hadj W.reverse, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨hpath.reverse, ?_⟩
    rw [Walk.edges_reverse, List.mem_reverse]
    exact edge_not_mem W hpath (by omega)
  · rw [Walk.length_cons, Walk.length_reverse, hWl]
    omega

/-! Segments of the path `x 0, x 1, ..., x m`. -/

def seg (x : ℕ → V) (c d : ℕ) : List V := (List.range' c (d + 1 - c)).map x

variable (x : ℕ → V) (m : ℕ)

lemma mem_seg {c d : ℕ} {v : V} : v ∈ seg x c d ↔ ∃ k, c ≤ k ∧ k ≤ d ∧ x k = v := by
  simp only [seg, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨k, ⟨h1, h2⟩, h3⟩; exact ⟨k, h1, by omega, h3⟩
  · rintro ⟨k, h1, h2, h3⟩; exact ⟨k, ⟨h1, by omega⟩, h3⟩

lemma length_seg (c d : ℕ) : (seg x c d).length = d + 1 - c := by simp [seg]

lemma nodup_seg (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j) {c d : ℕ} (hd : d ≤ m) :
    (seg x c d).Nodup := by
  apply List.Nodup.map_on _ (List.nodup_range' _)
  intro i hi j hj hij
  rw [List.mem_range'_1] at hi hj
  exact hinj i j (by omega) (by omega) hij

lemma PL_range (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1))) :
    ∀ n c, c + n ≤ m → PL G (x c) ((List.range' c (n+1)).map x) (x (c+n)) := by
  intro n
  induction n with
  | zero => intro c _; simpa using PL.single (G := G) (x c)
  | succ n ih =>
    intro c hc
    rw [List.range'_succ, List.map_cons]
    have := ih (c+1) (by omega)
    rw [show c + 1 + n = c + (n+1) by omega] at this
    exact PL.cons (hadj c (by omega)) this

lemma PL_seg (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1))) {c d : ℕ} (hcd : c ≤ d)
    (hd : d ≤ m) : PL G (x c) (seg x c d) (x d) := by
  have := PL_range x m hadj (d - c) c (by omega)
  rw [show c + (d - c) = d by omega] at this
  unfold seg
  rw [show d + 1 - c = d - c + 1 by omega]
  exact this


/-! Bridges of the path. -/

def OnP (v : V) : Prop := ∃ k, k ≤ m ∧ x k = v

def Br (G : SimpleGraph V) (s t : ℕ) : Prop :=
  s ≤ m ∧ t ≤ m ∧ ∃ q : G.Walk (x s) (x t), ∀ z ∈ q.support, z = x s ∨ z = x t ∨ ¬ OnP x m z

def AT (G : SimpleGraph V) (p : ℕ) (v : V) : Prop :=
  ∃ q : G.Walk (x p) v, ∀ z ∈ q.support, z = x p ∨ ¬ OnP x m z

def AT' (G : SimpleGraph V) (v : V) (t : ℕ) : Prop :=
  ∃ q : G.Walk v (x t), ∀ z ∈ q.support, z = x t ∨ ¬ OnP x m z

lemma br_of_AT {p t : ℕ} {v : V} (h1 : AT x m G p v) (h2 : AT' x m G v t) (hp : p ≤ m)
    (ht : t ≤ m) : Br x m G p t := by
  obtain ⟨q1, hq1⟩ := h1
  obtain ⟨q2, hq2⟩ := h2
  refine ⟨hp, ht, q1.append q2, ?_⟩
  intro z hz
  rw [Walk.support_append] at hz
  rcases List.mem_append.1 hz with hz | hz
  · rcases hq1 z hz with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rcases hq2 z (List.mem_of_mem_tail hz) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

lemma bridge_aux (w : ℕ) (hwm : w < m) :
    ∀ (y y2 : V) (p : G.Walk y y2), y2 = x m → x w ∉ p.support →
      (∃ s t, s < w ∧ w < t ∧ Br x m G s t) ∨
      (∃ t, w < t ∧ t ≤ m ∧ ∃ q : G.Walk y (x t), ∀ z ∈ q.support, z = x t ∨ ¬ OnP x m z) := by
  intro y y2 p
  induction p with
  | nil =>
    intro he _
    subst he
    right
    exact ⟨m, hwm, le_rfl, Walk.nil, by simp⟩
  | @cons y y' _ hadj p ih =>
    intro he hw
    rw [Walk.support_cons, List.mem_cons, not_or] at hw
    rcases ih he hw.2 with h | ⟨t, hwt, htm, q, hq⟩
    · exact Or.inl h
    · by_cases hy : OnP x m y
      · obtain ⟨k, hkm, rfl⟩ := hy
        rcases Nat.lt_or_ge k w with hk | hk
        · left
          refine ⟨k, t, hk, hwt, by omega, htm, Walk.cons hadj q, ?_⟩
          intro z hz
          rw [Walk.support_cons, List.mem_cons] at hz
          rcases hz with hz | hz
          · exact Or.inl hz
          · exact Or.inr (hq z hz)
        · right
          have hkw : k ≠ w := by rintro rfl; exact hw.1 rfl
          exact ⟨k, by omega, hkm, Walk.nil, by simp⟩
      · right
        refine ⟨t, hwt, htm, Walk.cons hadj q, ?_⟩
        intro z hz
        rw [Walk.support_cons, List.mem_cons] at hz
        rcases hz with hz | hz
        · subst hz; exact Or.inr hy
        · exact hq z hz

lemma bridge_exists (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hconn : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support)
    {w : ℕ} (hw0 : 0 < w) (hwm : w < m) : ∃ s t, s < w ∧ w < t ∧ Br x m G s t := by
  obtain ⟨p, hp⟩ := hconn (x w) (x 0) (x m)
    (fun h => by have := hinj _ _ (by omega) (by omega) h; omega)
    (fun h => by have := hinj _ _ (by omega) (by omega) h; omega)
  rcases bridge_aux x m w hwm (x 0) _ p rfl hp with h | ⟨t, hwt, htm, q, hq⟩
  · exact h
  · exfalso
    rcases hq (x 0) (Walk.start_mem_support q) with h | h
    · have := hinj _ _ (by omega) htm h; omega
    · exact h ⟨0, by omega, rfl⟩

lemma max_bridge (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hconn : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support)
    {w : ℕ} (hw0 : 0 < w) (hwm : w < m) :
    ∃ s t, s < w ∧ w < t ∧ Br x m G s t ∧ ∀ p t', p < w → Br x m G p t' → t' ≤ t := by
  classical
  let P : ℕ → Prop := fun t => w < t ∧ ∃ s, s < w ∧ Br x m G s t
  obtain ⟨s0, t0, hs0, ht0, hb0⟩ := bridge_exists x m hinj hconn hw0 hwm
  have hP0 : P t0 := ⟨ht0, s0, hs0, hb0⟩
  have hspec : P (Nat.findGreatest P m) := Nat.findGreatest_spec hb0.2.1 hP0
  obtain ⟨h1, s, hs, hb⟩ := hspec
  refine ⟨s, _, hs, h1, hb, ?_⟩
  intro p t' hp hb'
  rcases Nat.lt_or_ge w t' with h | h
  · exact Nat.le_findGreatest hb'.2.1 ⟨h, p, hp, hb'⟩
  · omega

lemma path_of_br {s t : ℕ} (hb : Br x m G s t) :
    ∃ Q : List V, PL G (x s) Q (x t) ∧ Q.Nodup ∧
      (∀ v ∈ Q, v = x s ∨ v = x t ∨ ¬ OnP x m v) ∧
      (∀ v ∈ Q, ¬ OnP x m v → AT x m G s v ∧ AT' x m G v t) := by
  classical
  obtain ⟨hs, ht, q, hq⟩ := hb
  set q' := q.bypass with hq'
  have hpath : q'.IsPath := Walk.bypass_isPath q
  have hsub : q'.support ⊆ q.support := Walk.support_bypass_subset_support q
  have hmem : ∀ z ∈ q'.support, z = x s ∨ z = x t ∨ ¬ OnP x m z := fun z hz => hq z (hsub hz)
  refine ⟨q'.support, ⟨Walk.isChain_adj_support q', ?_, ?_⟩, hpath.support_nodup, hmem, ?_⟩
  · rw [← Walk.cons_tail_support]; rfl
  · rw [List.getLast?_eq_some_getLast (Walk.support_ne_nil q'), Walk.getLast_support]
  · intro v hv hoff
    have hvs : x s ≠ v := fun h => hoff ⟨s, hs, h⟩
    have hvt : x t ≠ v := fun h => hoff ⟨t, ht, h⟩
    constructor
    · refine ⟨q'.takeUntil v hv, ?_⟩
      intro z hz
      have hz' := Walk.support_takeUntil_subset_support q' hv hz
      rcases hmem z hz' with h | h | h
      · exact Or.inl h
      · subst h
        exact absurd hz (Walk.endpoint_notMem_support_takeUntil hpath hv hvt)
      · exact Or.inr h
    · have hv' : v ∈ q'.reverse.support := by
        rw [Walk.support_reverse]; exact List.mem_reverse.2 hv
      refine ⟨(q'.reverse.takeUntil v hv').reverse, ?_⟩
      intro z hz
      rw [Walk.support_reverse, List.mem_reverse] at hz
      have hz' := Walk.support_takeUntil_subset_support q'.reverse hv' hz
      rw [Walk.support_reverse, List.mem_reverse] at hz'
      rcases hmem z hz' with h | h | h
      · subst h
        exact absurd hz (Walk.endpoint_notMem_support_takeUntil hpath.reverse hv' hvs)
      · exact Or.inl h
      · exact Or.inr h


/-! The chain of bridges (case where every neighbour of `x 0` precedes every neighbour of `x m`). -/

def Inv (G : SimpleGraph V) (S T : Finset ℕ) (u w : ℕ) (L : List V) : Prop :=
  u < w ∧ w ≤ m ∧ (∀ k ∈ T, u ≤ k) ∧ (∀ p t, p < u → Br x m G p t → t ≤ w) ∧
  PL G (x u) L (x w) ∧ L.Nodup ∧
  (∀ v ∈ L, (∃ k, k ≤ u ∧ x k = v) ∨ v = x w ∨ (¬ OnP x m v ∧ ∃ p, p < u ∧ AT x m G p v)) ∧
  S.card + 1 ≤ L.length

lemma close_cycle (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1)))
    {S T : Finset ℕ} (hT : ∀ k ∈ T, k < m ∧ G.Adj (x k) (x m))
    {u w : ℕ} {L : List V} (hI : Inv x m G S T u w L) (hk : ∃ k ∈ T, k < w)
    (h3 : 3 ≤ S.card + T.card) :
    ∃ (y : V) (c : G.Walk y y), c.IsCycle ∧ S.card + T.card ≤ c.length := by
  classical
  obtain ⟨huw, hwm, hTu, -, hPL, hnd, hmem, hlen⟩ := hI
  obtain ⟨k0, hk0T, hk0w⟩ := hk
  have hne : (T.filter (· < w)).Nonempty := ⟨k0, Finset.mem_filter.2 ⟨hk0T, hk0w⟩⟩
  set j := (T.filter (· < w)).max' hne with hjdef
  have hjT : j ∈ T ∧ j < w := Finset.mem_filter.1 (Finset.max'_mem _ _)
  have hjmax : ∀ k ∈ T, k < w → k ≤ j := fun k hk hkw =>
    Finset.le_max' _ k (Finset.mem_filter.2 ⟨hk, hkw⟩)
  have huj : u ≤ j := hTu j hjT.1
  have P1 : PL G (x j) (seg x u j).reverse (x u) := (PL_seg x m hadj huj (by omega)).reverse
  have P3 : PL G (x w) (seg x w m) (x m) := PL_seg x m hadj hwm le_rfl
  have Q1 := P1.append hPL
  have Q2 := Q1.append P3
  have hnd1 : ((seg x u j).reverse ++ L.tail).Nodup := by
    refine nodup_append_tail (List.nodup_reverse.2 (nodup_seg x m hinj (by omega))) hnd hPL ?_
    intro v hv hvL
    obtain ⟨k, hk1, hk2, rfl⟩ := (mem_seg x).1 (List.mem_reverse.1 hv)
    rcases hmem _ hvL with ⟨k', hk', he⟩ | he | ⟨hoff, -⟩
    · have := hinj _ _ (by omega) (by omega) he
      have : k = u := by omega
      rw [this]
    · have := hinj _ _ (by omega) (by omega) he; omega
    · exact absurd ⟨k, by omega, rfl⟩ hoff
  have hnd2 : ((seg x u j).reverse ++ L.tail ++ (seg x w m).tail).Nodup := by
    refine nodup_append_tail hnd1 (nodup_seg x m hinj le_rfl) P3 ?_
    intro v hv hvs
    obtain ⟨k, hk1, hk2, rfl⟩ := (mem_seg x).1 hvs
    rcases mem_append_tail hv with hv | hvL
    · obtain ⟨k', hk1', hk2', he⟩ := (mem_seg x).1 (List.mem_reverse.1 hv)
      have := hinj _ _ (by omega) (by omega) he; omega
    · rcases hmem _ hvL with ⟨k', hk', he⟩ | he | ⟨hoff, -⟩
      · have := hinj _ _ (by omega) (by omega) he; omega
      · exact he
      · exact absurd ⟨k, by omega, rfl⟩ hoff
  have hTsub : T ⊆ Finset.Icc u j ∪ Finset.Ico w m := by
    intro k hk
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico]
    have := hTu k hk
    have := (hT k hk).1
    rcases Nat.lt_or_ge k w with h | h
    · have := hjmax k hk h; left; omega
    · right; omega
  have hTc := (Finset.card_le_card hTsub).trans (Finset.card_union_le _ _)
  rw [Nat.card_Icc, Nat.card_Ico] at hTc
  have hl1 := length_append_tail (L := (seg x u j).reverse) hPL.length_pos
  have hl2 := length_append_tail (L := (seg x u j).reverse ++ L.tail) P3.length_pos
  rw [List.length_reverse, length_seg] at hl1
  rw [length_seg] at hl2
  obtain ⟨y, c, hc, hcl⟩ := cycle_of_PL Q2 (hT j hjT.1).2.symm hnd2 (by omega)
  exact ⟨y, c, hc, by omega⟩

lemma chain_step (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1)))
    (hconn : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support)
    {S T : Finset ℕ} (hT : ∀ k ∈ T, k < m ∧ G.Adj (x k) (x m))
    {u w : ℕ} {L : List V} (hI : Inv x m G S T u w L) (hk : ∀ k ∈ T, w ≤ k)
    (hTne : T.Nonempty) : ∃ t L', w < t ∧ Inv x m G S T w t L' := by
  obtain ⟨huw, hwm, hTu, hRB, hPL, hnd, hmem, hlen⟩ := hI
  obtain ⟨k0, hk0⟩ := hTne
  have hwm' : w < m := lt_of_le_of_lt (hk k0 hk0) (hT k0 hk0).1
  obtain ⟨s, t, hsw, hwt, hb, hmax⟩ := max_bridge x m hinj hconn (by omega : 0 < w) hwm'
  have hus : u ≤ s := by
    by_contra h
    have := hRB s t (by omega) hb
    omega
  have htm : t ≤ m := hb.2.1
  obtain ⟨Q, hQPL, hQnd, hQmem, hQat⟩ := path_of_br x m hb
  have P2 : PL G (x u) (seg x u s) (x s) := PL_seg x m hadj hus (by omega)
  have D1 := hPL.reverse.append P2
  have D := D1.append hQPL
  have hnd1 : (L.reverse ++ (seg x u s).tail).Nodup := by
    refine nodup_append_tail (List.nodup_reverse.2 hnd) (nodup_seg x m hinj (by omega)) P2 ?_
    intro v hv hvs
    obtain ⟨k, hk1, hk2, rfl⟩ := (mem_seg x).1 hvs
    rcases hmem _ (List.mem_reverse.1 hv) with ⟨k', hk', he⟩ | he | ⟨hoff, -⟩
    · have := hinj _ _ (by omega) (by omega) he
      have : k = u := by omega
      rw [this]
    · have := hinj _ _ (by omega) (by omega) he; omega
    · exact absurd ⟨k, by omega, rfl⟩ hoff
  have hnd2 : (L.reverse ++ (seg x u s).tail ++ Q.tail).Nodup := by
    refine nodup_append_tail hnd1 hQnd hQPL ?_
    intro v hv hvQ
    rcases hQmem v hvQ with he | he | hoff
    · exact he
    · exfalso
      subst he
      rcases mem_append_tail hv with hv | hv
      · rcases hmem _ (List.mem_reverse.1 hv) with ⟨k', hk', he⟩ | he | ⟨hoff, -⟩
        · have := hinj _ _ (by omega) (by omega) he; omega
        · have := hinj _ _ (by omega) (by omega) he; omega
        · exact hoff ⟨t, htm, rfl⟩
      · obtain ⟨k, hk1, hk2, he⟩ := (mem_seg x).1 hv
        have := hinj _ _ (by omega) (by omega) he; omega
    · exfalso
      rcases mem_append_tail hv with hv | hv
      · rcases hmem _ (List.mem_reverse.1 hv) with ⟨k', hk', he⟩ | he | ⟨-, p, hp, hat⟩
        · exact hoff ⟨k', by omega, he⟩
        · exact hoff ⟨w, hwm, he.symm⟩
        · have := hRB p t hp (br_of_AT x m hat (hQat v hvQ hoff).2 (by omega) htm)
          omega
      · obtain ⟨k, hk1, hk2, he⟩ := (mem_seg x).1 hv
        exact hoff ⟨k, by omega, he⟩
  refine ⟨t, _, hwt, hwt, htm, hk, hmax, D, hnd2, ?_, ?_⟩
  · intro v hv
    rcases mem_append_tail hv with hv | hvQ
    · rcases mem_append_tail hv with hv | hv
      · rcases hmem _ (List.mem_reverse.1 hv) with ⟨k', hk', he⟩ | he | ⟨hoff, p, hp, hat⟩
        · exact Or.inl ⟨k', by omega, he⟩
        · exact Or.inl ⟨w, le_rfl, he.symm⟩
        · exact Or.inr (Or.inr ⟨hoff, p, by omega, hat⟩)
      · obtain ⟨k, hk1, hk2, he⟩ := (mem_seg x).1 hv
        exact Or.inl ⟨k, by omega, he⟩
    · rcases hQmem v hvQ with he | he | hoff
      · exact Or.inl ⟨s, by omega, he.symm⟩
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr ⟨hoff, s, hsw, (hQat v hvQ hoff).1⟩)
  · have hl1 := length_append_tail (L := L.reverse) P2.length_pos
    have hl2 := length_append_tail (L := L.reverse ++ (seg x u s).tail) hQPL.length_pos
    rw [List.length_reverse, length_seg] at hl1
    have := hQPL.length_pos
    omega

lemma chain_base (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1)))
    (hconn : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support)
    {S T : Finset ℕ} (hS : ∀ k ∈ S, k < m ∧ G.Adj (x 0) (x (k+1)))
    (hT : ∀ k ∈ T, k < m ∧ G.Adj (x k) (x m))
    (hsep : ∀ i ∈ S, ∀ j ∈ T, i < j) (hSne : S.Nonempty) (hTne : T.Nonempty) :
    ∃ u w L, Inv x m G S T u w L := by
  classical
  set a' := S.max' hSne with ha'def
  have ha'S : a' ∈ S := Finset.max'_mem _ _
  have ha'max : ∀ k ∈ S, k ≤ a' := fun k hk => Finset.le_max' _ k hk
  obtain ⟨j0, hj0⟩ := hTne
  have h1 := hsep a' ha'S j0 hj0
  have h2 := (hT j0 hj0).1
  obtain ⟨s, t, hsa, hat, hb, hmax⟩ :=
    max_bridge x m hinj hconn (by omega : 0 < a' + 1) (by omega : a' + 1 < m)
  have htm : t ≤ m := hb.2.1
  obtain ⟨Q, hQPL, hQnd, hQmem, hQat⟩ := path_of_br x m hb
  have hne : (S.filter (fun k => s ≤ k)).Nonempty := ⟨a', Finset.mem_filter.2 ⟨ha'S, by omega⟩⟩
  set i' := (S.filter (fun k => s ≤ k)).min' hne with hi'def
  have hi'S : i' ∈ S ∧ s ≤ i' := Finset.mem_filter.1 (Finset.min'_mem _ _)
  have hi'min : ∀ k ∈ S, s ≤ k → i' ≤ k := fun k hk hsk =>
    Finset.min'_le _ k (Finset.mem_filter.2 ⟨hk, hsk⟩)
  have hi'a : i' ≤ a' := ha'max i' hi'S.1
  have P1 : PL G (x (a'+1)) (seg x (i'+1) (a'+1)).reverse (x (i'+1)) :=
    (PL_seg x m hadj (by omega) (by omega)).reverse
  have P2 : PL G (x (i'+1)) [x (i'+1), x 0] (x 0) := PL.edge (hS i' hi'S.1).2.symm
  have P3 : PL G (x 0) (seg x 0 s) (x s) := PL_seg x m hadj (Nat.zero_le _) (by omega)
  have E1 := P1.append P2
  have E2 := E1.append P3
  have E := E2.append hQPL
  have hx0 : ∀ k, k ≤ m → x k = x 0 → k = 0 := fun k hk he => hinj _ _ hk (by omega) he
  have hnd1 : ((seg x (i'+1) (a'+1)).reverse ++ [x (i'+1), x 0].tail).Nodup := by
    refine nodup_append_tail (List.nodup_reverse.2 (nodup_seg x m hinj (by omega))) ?_ P2 ?_
    · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_true]
      intro he; have := hx0 _ (by omega) he; omega
    · intro v hv hv2
      obtain ⟨k, hk1, hk2, rfl⟩ := (mem_seg x).1 (List.mem_reverse.1 hv)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv2
      rcases hv2 with he | he
      · exact he
      · have := hx0 _ (by omega) he; omega
  have hmem1 : ∀ v ∈ (seg x (i'+1) (a'+1)).reverse ++ [x (i'+1), x 0].tail,
      v = x 0 ∨ ∃ k, i' + 1 ≤ k ∧ k ≤ a' + 1 ∧ x k = v := by
    intro v hv
    rcases mem_append_tail hv with hv | hv
    · exact Or.inr ((mem_seg x).1 (List.mem_reverse.1 hv))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact Or.inr ⟨i'+1, le_rfl, by omega, rfl⟩
      · exact Or.inl rfl
  have hnd2 : ((seg x (i'+1) (a'+1)).reverse ++ [x (i'+1), x 0].tail ++
      (seg x 0 s).tail).Nodup := by
    refine nodup_append_tail hnd1 (nodup_seg x m hinj (by omega)) P3 ?_
    intro v hv hvs
    obtain ⟨k, hk1, hk2, rfl⟩ := (mem_seg x).1 hvs
    rcases hmem1 _ hv with he | ⟨k', hk1', hk2', he⟩
    · exact he
    · have := hinj _ _ (by omega) (by omega) he; omega
  have hmem2 : ∀ v ∈ (seg x (i'+1) (a'+1)).reverse ++ [x (i'+1), x 0].tail ++
      (seg x 0 s).tail, ∃ k, k ≤ a' + 1 ∧ x k = v := by
    intro v hv
    rcases mem_append_tail hv with hv | hv
    · rcases hmem1 _ hv with he | ⟨k', hk1', hk2', he⟩
      · exact ⟨0, by omega, he.symm⟩
      · exact ⟨k', hk2', he⟩
    · obtain ⟨k, hk1, hk2, he⟩ := (mem_seg x).1 hv
      exact ⟨k, by omega, he⟩
  have hnd3 : ((seg x (i'+1) (a'+1)).reverse ++ [x (i'+1), x 0].tail ++
      (seg x 0 s).tail ++ Q.tail).Nodup := by
    refine nodup_append_tail hnd2 hQnd hQPL ?_
    intro v hv hvQ
    obtain ⟨k, hk, rfl⟩ := hmem2 v hv
    rcases hQmem _ hvQ with he | he | hoff
    · exact he
    · have := hinj _ _ (by omega) htm he; omega
    · exact absurd ⟨k, by omega, rfl⟩ hoff
  refine ⟨a' + 1, t, _, hat, htm, fun k hk => hsep a' ha'S k hk, hmax, E, hnd3, ?_, ?_⟩
  · intro v hv
    rcases mem_append_tail hv with hv | hvQ
    · exact Or.inl (hmem2 v hv)
    · rcases hQmem v hvQ with he | he | hoff
      · exact Or.inl ⟨s, by omega, he.symm⟩
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr ⟨hoff, s, hsa, (hQat v hvQ hoff).1⟩)
  · have hSsub : S ⊆ Finset.range s ∪ Finset.Icc i' a' := by
      intro k hk
      rw [Finset.mem_union, Finset.mem_range, Finset.mem_Icc]
      rcases Nat.lt_or_ge k s with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hi'min k hk h, ha'max k hk⟩
    have hSc := (Finset.card_le_card hSsub).trans (Finset.card_union_le _ _)
    rw [Finset.card_range, Nat.card_Icc] at hSc
    have hl1 := length_append_tail (L := (seg x (i'+1) (a'+1)).reverse) P2.length_pos
    have hl2 := length_append_tail
      (L := (seg x (i'+1) (a'+1)).reverse ++ [x (i'+1), x 0].tail) P3.length_pos
    have hl3 := length_append_tail
      (L := (seg x (i'+1) (a'+1)).reverse ++ [x (i'+1), x 0].tail ++ (seg x 0 s).tail)
      hQPL.length_pos
    rw [List.length_reverse, length_seg] at hl1
    rw [length_seg] at hl2
    simp only [List.length_cons, List.length_nil] at hl1
    have := hQPL.length_pos
    omega

lemma chain_iter (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1)))
    (hconn : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support)
    {S T : Finset ℕ} (hT : ∀ k ∈ T, k < m ∧ G.Adj (x k) (x m))
    (h3 : 3 ≤ S.card + T.card) (hTne : T.Nonempty) :
    ∀ N u w L, m - w = N → Inv x m G S T u w L →
      ∃ (y : V) (c : G.Walk y y), c.IsCycle ∧ S.card + T.card ≤ c.length := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro u w L hN hI
    by_cases hk : ∃ k ∈ T, k < w
    · exact close_cycle x m hinj hadj hT hI hk h3
    · push Not at hk
      obtain ⟨t, L', hwt, hI'⟩ := chain_step x m hinj hadj hconn hT hI hk hTne
      have htm : t ≤ m := hI'.2.1
      exact ih (m - t) (by omega) w t L' rfl hI'


/-! Case of a neighbour of `x m` preceding a neighbour of `x 0`, and the combined lemma. -/

lemma case_two (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1)))
    {S T : Finset ℕ} (hS : ∀ k ∈ S, k < m ∧ G.Adj (x 0) (x (k+1)))
    (hT : ∀ k ∈ T, k < m ∧ G.Adj (x k) (x m)) (hdisj : ∀ k ∈ S, k ∉ T)
    (h : ∃ j ∈ T, ∃ i ∈ S, j < i) (h3 : 3 ≤ S.card + T.card) :
    ∃ (y : V) (c : G.Walk y y), c.IsCycle ∧ S.card + T.card ≤ c.length := by
  classical
  obtain ⟨j0, hj0T, i0, hi0S, hji⟩ := h
  have hne : (S.filter (fun k => j0 < k)).Nonempty := ⟨i0, Finset.mem_filter.2 ⟨hi0S, hji⟩⟩
  set i1 := (S.filter (fun k => j0 < k)).min' hne with hi1def
  have hi1 : i1 ∈ S ∧ j0 < i1 := Finset.mem_filter.1 (Finset.min'_mem _ _)
  have hi1min : ∀ k ∈ S, j0 < k → i1 ≤ k := fun k hk h =>
    Finset.min'_le _ k (Finset.mem_filter.2 ⟨hk, h⟩)
  have hne2 : (T.filter (fun k => k < i1)).Nonempty := ⟨j0, Finset.mem_filter.2 ⟨hj0T, hi1.2⟩⟩
  set j1 := (T.filter (fun k => k < i1)).max' hne2 with hj1def
  have hj1 : j1 ∈ T ∧ j1 < i1 := Finset.mem_filter.1 (Finset.max'_mem _ _)
  have hj1max : ∀ k ∈ T, k < i1 → k ≤ j1 := fun k hk h =>
    Finset.le_max' _ k (Finset.mem_filter.2 ⟨hk, h⟩)
  have hj0j1 : j0 ≤ j1 := hj1max j0 hj0T hi1.2
  have hi1m := (hS i1 hi1.1).1
  have P1 : PL G (x 0) (seg x 0 j1) (x j1) := PL_seg x m hadj (Nat.zero_le _) (by omega)
  have P2 : PL G (x j1) [x j1, x m] (x m) := PL.edge (hT j1 hj1.1).2
  have P3 : PL G (x m) (seg x (i1+1) m).reverse (x (i1+1)) :=
    (PL_seg x m hadj (by omega) le_rfl).reverse
  have F := (P1.append P2).append P3
  have hnd1 : (seg x 0 j1 ++ [x j1, x m].tail).Nodup := by
    refine nodup_append_tail (nodup_seg x m hinj (by omega)) ?_ P2 ?_
    · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
        List.nodup_nil, and_true]
      intro he; have := hinj _ _ (by omega) le_rfl he; omega
    · intro v hv hv2
      obtain ⟨k, hk1, hk2, rfl⟩ := (mem_seg x).1 hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv2
      rcases hv2 with he | he
      · exact he
      · have := hinj _ _ (by omega) le_rfl he; omega
  have hnd2 : (seg x 0 j1 ++ [x j1, x m].tail ++ (seg x (i1+1) m).reverse.tail).Nodup := by
    refine nodup_append_tail hnd1 (List.nodup_reverse.2 (nodup_seg x m hinj le_rfl)) P3 ?_
    intro v hv hvs
    obtain ⟨k, hk1, hk2, rfl⟩ := (mem_seg x).1 (List.mem_reverse.1 hvs)
    rcases mem_append_tail hv with hv | hv
    · obtain ⟨k', hk1', hk2', he⟩ := (mem_seg x).1 hv
      have := hinj _ _ (by omega) (by omega) he; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with he | he
      · have := hinj _ _ (by omega) (by omega) he; omega
      · exact he
  have hsub : S ∪ T ⊆ Finset.range (j1 + 1) ∪ Finset.Ico i1 m := by
    intro k hk
    rw [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    rcases Finset.mem_union.1 hk with hk | hk
    · have := (hS k hk).1
      rcases Nat.lt_or_ge j1 k with h | h
      · have := hi1min k hk (by omega); right; omega
      · left; omega
    · have := (hT k hk).1
      rcases Nat.lt_or_ge k i1 with h | h
      · have := hj1max k hk h; left; omega
      · right; omega
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_left.2 hdisj), Finset.card_range,
    Nat.card_Ico] at hc
  have hl1 := length_append_tail (L := seg x 0 j1) P2.length_pos
  have hl2 := length_append_tail (L := seg x 0 j1 ++ [x j1, x m].tail) P3.length_pos
  rw [length_seg] at hl1
  rw [List.length_reverse, length_seg] at hl2
  simp only [List.length_cons, List.length_nil] at hl1
  obtain ⟨y, c, hcyc, hcl⟩ := cycle_of_PL F (hS i1 hi1.1).2.symm hnd2 (by omega)
  exact ⟨y, c, hcyc, by omega⟩

/-- Bondy-type lemma: a path `x 0, ..., x m` in a 2-connected graph, with no crossing pair of
end chords, yields a cycle of length at least `|S| + |T|`. -/
lemma long_cycle (hinj : ∀ i j, i ≤ m → j ≤ m → x i = x j → i = j)
    (hadj : ∀ i, i < m → G.Adj (x i) (x (i+1)))
    (hconn : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support)
    {S T : Finset ℕ} (hS : ∀ k ∈ S, k < m ∧ G.Adj (x 0) (x (k+1)))
    (hT : ∀ k ∈ T, k < m ∧ G.Adj (x k) (x m)) (hdisj : ∀ k ∈ S, k ∉ T)
    (hS1 : 1 ≤ S.card) (hT1 : 1 ≤ T.card) (h3 : 3 ≤ S.card + T.card) :
    ∃ (y : V) (c : G.Walk y y), c.IsCycle ∧ S.card + T.card ≤ c.length := by
  by_cases h : ∃ j ∈ T, ∃ i ∈ S, j < i
  · exact case_two x m hinj hadj hS hT hdisj h h3
  · have hsep : ∀ i ∈ S, ∀ j ∈ T, i < j := by
      intro i hi j hj
      rcases Nat.lt_trichotomy i j with h' | h' | h'
      · exact h'
      · subst h'; exact absurd hj (hdisj i hi)
      · exact absurd ⟨j, hj, i, hi, h'⟩ h
    have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
    have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨u, w, L, hI⟩ := chain_base x m hinj hadj hconn hS hT hsep hSne hTne
    exact chain_iter x m hinj hadj hconn hT h3 hTne _ u w L rfl hI


/-! Longest paths (adapted from philipsaint's proof of Dirac's Hamiltonicity theorem). -/

def Cyc (G : SimpleGraph V) (c : List V) : Prop :=
  c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b

lemma rot {c : List V} (hc : Cyc G c) {q : V} (hq : q ∈ c) :
    ∃ c' : List V, c'.Perm c ∧ c'.IsChain G.Adj ∧ c'.head? = some q := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hq
  refine ⟨(q :: B) ++ A, List.perm_append_comm, ?_, by simp⟩
  obtain ⟨hch, hcl⟩ := hc
  rw [List.isChain_append] at hch
  refine List.isChain_append.2 ⟨hch.2.1, hch.1, ?_⟩
  intro x hx y hy
  apply hcl
  · rw [List.getLast?_append]
    have : (q :: B).getLast? = some x := hx
    simp [this]
  · rw [List.head?_append, hy]
    rfl

lemma getD_zero (l : List V) (hl : l ≠ []) (d : V) : l.getD 0 d = l.head hl := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => rfl

lemma getD_last (l : List V) (hl : l ≠ []) (d : V) : l.getD (l.length - 1) d = l.getLast hl := by
  rw [List.getLast_eq_getElem, List.getD_eq_getElem]

theorem dirac_core [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (d : ℕ) (hd : 2 ≤ d)
    (h3 : 3 ≤ Fintype.card V)
    (hconn : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support)
    (hreach : ∀ a b : V, G.Reachable a b) (hdeg : ∀ v, d ≤ G.degree v) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ min (Fintype.card V) (2 * d) ≤ c.length := by
  classical
  set n := Fintype.card V with hn
  obtain ⟨v0⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let PP : ℕ → Prop := fun k => ∃ l : List V, (l.Nodup ∧ l.IsChain G.Adj) ∧ l.length = k
  have h1 : PP 1 := ⟨[v0], ⟨by simp, List.isChain_singleton _⟩, rfl⟩
  set M := Nat.findGreatest PP n
  obtain ⟨l, ⟨hlnd, hlch⟩, hlM⟩ : PP M := Nat.findGreatest_spec (by omega) h1
  have hmax : ∀ l' : List V, l'.Nodup → l'.IsChain G.Adj → l'.length ≤ M :=
    fun l' h1 h2 => Nat.le_findGreatest h1.length_le_card ⟨l', ⟨h1, h2⟩, rfl⟩
  have hM1 : 1 ≤ M := Nat.le_findGreatest (by omega) h1
  have hl_ne : l ≠ [] := by
    rintro rfl
    simp at hlM
    omega
  set q0 := l.head hl_ne
  set z := l.getLast hl_ne
  have hmn : l.length ≤ n := hlnd.length_le_card
  have ext_head : ∀ y, G.Adj q0 y → y ∈ l := by
    intro y hy
    by_contra hyl
    have := hmax (y :: l) (List.nodup_cons.2 ⟨hyl, hlnd⟩)
      (List.IsChain.cons_of_ne_nil hl_ne hlch ((hy).symm))
    simp at this
    omega
  have ext_last : ∀ y, G.Adj z y → y ∈ l := by
    intro y hy
    by_contra hyl
    have hch : (l ++ [y]).IsChain G.Adj := by
      refine List.isChain_append.2 ⟨hlch, List.isChain_singleton _, ?_⟩
      intro x hx y' hy'
      rw [List.getLast?_eq_some_getLast hl_ne] at hx
      simp at hx hy'
      subst hx hy'
      exact hy
    have hnd : (l ++ [y]).Nodup := by
      rw [List.nodup_append]
      refine ⟨hlnd, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp at hb
      subst hb
      rintro rfl
      exact hyl ha
    have := hmax _ hnd hch
    simp at this
    omega
  set m := l.length with hm
  have hq0 : l.getD 0 q0 = q0 := getD_zero l hl_ne q0
  have hz : l.getD (m - 1) q0 = z := getD_last l hl_ne q0
  let S := (Finset.range (m - 1)).filter (fun j => G.Adj q0 (l.getD (j + 1) q0))
  let T := (Finset.range (m - 1)).filter (fun j => G.Adj (l.getD j q0) z)
  have hS : G.degree q0 ≤ S.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := S)
      (f := fun j => l.getD (j + 1) q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_head y hy)
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hq0]
    rw [Finset.mem_image]
    refine ⟨k - 1, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
      exact hy
    · rw [show k - 1 + 1 = k by omega, List.getD_eq_getElem _ _ hk]
  have hT : G.degree z ≤ T.card := by
    rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := T)
      (f := fun j => l.getD j q0))
    intro y hy
    rw [mem_neighborFinset] at hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (ext_last y hy)
    have hkm : k ≠ m - 1 := by
      rintro rfl
      apply hy.ne
      rw [← List.getD_eq_getElem (d := q0), hz]
    rw [Finset.mem_image]
    refine ⟨k, ?_, List.getD_eq_getElem _ _ hk⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [List.getD_eq_getElem _ _ hk]
    exact (hy).symm
  have hdq := hdeg q0
  have hdz := hdeg z
  by_cases hcross : ∃ j, j ∈ S ∧ j ∈ T
  · obtain ⟨j, hjS, hjT⟩ := hcross
    rw [Finset.mem_filter, Finset.mem_range] at hjS hjT
    obtain ⟨hjm, hA⟩ := hjS
    obtain ⟨-, hB⟩ := hjT
    set c := l.take (j + 1) ++ (l.drop (j + 1)).reverse with hcdef
    have hperm : c.Perm l := by
      have := (List.Perm.append_left (l.take (j + 1)) (List.reverse_perm (l.drop (j + 1))))
      rw [List.take_append_drop] at this
      exact this
    have hcnd : c.Nodup := hperm.nodup_iff.mpr hlnd
    have hj1 : j < m := by omega
    have hj2 : j + 1 < m := by omega
    have e1 : (l.take (j + 1)).getLast? = some (l.getD j q0) := by
      rw [List.getLast?_take, List.getD_eq_getElem _ _ hj1]
      simp [List.getElem?_eq_getElem hj1]
    have e2 : (l.drop (j + 1)).reverse.head? = some z := by
      rw [List.head?_reverse, List.getLast?_drop, if_neg (by omega),
        List.getLast?_eq_some_getLast hl_ne]
    have e3 : c.getLast? = some (l.getD (j + 1) q0) := by
      rw [hcdef, List.getLast?_append, List.getLast?_reverse, List.head?_drop,
        List.getElem?_eq_getElem hj2, List.getD_eq_getElem _ _ hj2]
      rfl
    have e4 : c.head? = some q0 := by
      rw [hcdef, List.head?_append, List.head?_take]
      simp [List.head?_eq_some_head hl_ne, q0]
    have hchain : c.IsChain G.Adj := by
      refine List.isChain_append.2 ⟨hlch.take _, ?_, ?_⟩
      · rw [List.isChain_reverse]
        exact (hlch.drop _).imp (fun a b h => h.symm)
      · intro x hx y hy
        rw [e1] at hx
        rw [e2] at hy
        simp at hx hy
        subst hx hy
        exact hB
    have hcyc : Cyc G c := by
      refine ⟨hchain, ?_⟩
      intro a ha b hb
      rw [e3] at ha
      rw [e4] at hb
      simp at ha hb
      subst ha hb
      exact (hA).symm
    have hall : ∀ w, w ∈ l := by
      intro w
      by_contra hw
      obtain ⟨p⟩ := hreach q0 w
      obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {x | x ∈ l} (List.head_mem hl_ne) hw
      have hqc : d.fst ∈ c := hperm.mem_iff.mpr hd1
      obtain ⟨c', hc'p, hc'ch, hc'h⟩ := rot hcyc hqc
      have hnd' : (d.snd :: c').Nodup := by
        refine List.nodup_cons.2 ⟨?_, (hc'p.trans hperm).nodup_iff.mpr hlnd⟩
        intro hmem
        exact hd2 ((hc'p.trans hperm).mem_iff.mp hmem)
      have hch' : (d.snd :: c').IsChain G.Adj := by
        refine List.isChain_cons.2 ⟨?_, hc'ch⟩
        intro y hy
        rw [hc'h] at hy
        simp at hy
        subst hy
        exact (d.adj).symm
      have := hmax _ hnd' hch'
      rw [List.length_cons, (hc'p.trans hperm).length_eq] at this
      omega
    have hmn' : m = n := by
      have h1 : l.toFinset = Finset.univ := by
        ext w
        simp [hall w]
      have h2 := List.toFinset_card_of_nodup hlnd
      rw [h1, Finset.card_univ] at h2
      omega
    have hclen : c.length = n := by rw [hperm.length_eq]; exact hmn'
    obtain ⟨y, w, hw, hwl⟩ := cycle_of_PL (G := G) ⟨hchain, e4, e3⟩ hA.symm hcnd (by omega)
    exact ⟨y, w, hw, by rw [hwl, hclen]; exact min_le_left _ _⟩
  · push Not at hcross
    let x : ℕ → V := fun k => l.getD k q0
    have hinj : ∀ i j, i ≤ m - 1 → j ≤ m - 1 → x i = x j → i = j := by
      intro i j hi hj he
      simp only [x] at he
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at he
      exact (hlnd.getElem_inj_iff).1 he
    have hadj : ∀ i, i < m - 1 → G.Adj (x i) (x (i+1)) := by
      intro i hi
      simp only [x]
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      exact List.isChain_iff_getElem.1 hlch i (by omega)
    have hx0 : x 0 = q0 := hq0
    have hxm : x (m - 1) = z := hz
    have hS' : ∀ k ∈ S, k < m - 1 ∧ G.Adj (x 0) (x (k+1)) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      exact ⟨hk.1, by rw [hx0]; exact hk.2⟩
    have hT' : ∀ k ∈ T, k < m - 1 ∧ G.Adj (x k) (x (m - 1)) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      exact ⟨hk.1, by rw [hxm]; exact hk.2⟩
    obtain ⟨y, w, hw, hwl⟩ := long_cycle x (m - 1) hinj hadj hconn hS' hT'
      (fun k hk hkT => hcross k hk hkT) (by omega) (by omega) (by omega)
    exact ⟨y, w, hw, le_trans (min_le_right _ _) (by omega)⟩

end C1

theorem core : CoreStatement := by
  intro V _ _ G _ d hd h3 hG hconn hdeg
  exact C1.dirac_core d hd h3 hconn (fun a b => hG.preconnected a b) hdeg

end OMA.EG


namespace OMA.EG
open SimpleGraph Finset

/-- The target step H1 (copied verbatim from reductions/opg-forcing-a-2-regular-minor.R1.lean). -/
def H1Statement : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
    3 ≤ k → (k - 1) * Fintype.card V ≤ 2 * G.edgeFinset.card →
      ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length

lemma lift_cycle {V : Type} (G : SimpleGraph V) (S : Set V) {k : ℕ}
    (h : ∃ (u : S) (c : (G.induce S).Walk u u), c.IsCycle ∧ k ≤ c.length) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length := by
  obtain ⟨u, c, hc, hk⟩ := h
  refine ⟨_, c.map (Embedding.induce (G := G) S).toHom, ?_, ?_⟩
  · exact (Walk.isCycle_map_iff_of_injective (Embedding.induce (G := G) S).injective).2 hc
  · rw [Walk.length_map]; exact hk

lemma edges_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) [Fintype (G.induce (s : Set V)).edgeSet] :
    #(G.edgeFinset ∩ s.sym2) ≤ #(G.induce (s : Set V)).edgeFinset := by
  let f : Sym2 (s : Set V) ↪ Sym2 V :=
    ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩
  rw [← Finset.card_map f]
  apply Finset.card_le_card
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    rw [Finset.mem_inter, mem_edgeFinset, mem_edgeSet, Finset.mem_sym2_iff] at he
    obtain ⟨hxy, hs⟩ := he
    have hx : x ∈ (s : Set V) := hs x (Sym2.mem_mk_left x y)
    have hy : y ∈ (s : Set V) := hs y (Sym2.mem_mk_right x y)
    rw [Finset.mem_map]
    refine ⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_, ?_⟩
    · rw [mem_edgeFinset, mem_edgeSet]; exact hxy
    · rfl

lemma card_sub {V : Type} [Fintype V] (s : Finset V) [Fintype (s : Set V)] :
    Fintype.card (s : Set V) = #s := by simp

def EGP (n : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ),
    Fintype.card V = n → 3 ≤ k → (k - 1) * (n - 1) < 2 * #G.edgeFinset →
      ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length

lemma apply_sub {n : ℕ} (ih : ∀ m < n, EGP m) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k) (s : Finset V) (hs : #s < n)
    (he : (k - 1) * (#s - 1) < 2 * #(G.edgeFinset ∩ s.sym2)) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length := by
  classical
  apply lift_cycle G (s : Set V)
  apply ih #s hs (s : Set V) (G.induce (s : Set V)) k (card_sub s) hk
  have := edges_le G s
  omega

lemma sep_case {n : ℕ} (ih : ∀ m < n, EGP m) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k) (hn : Fintype.card V = n)
    (he : (k - 1) * (n - 1) < 2 * #G.edgeFinset) (V1 V2 : Finset V) (hU : V1 ∪ V2 = univ)
    (hI : #(V1 ∩ V2) ≤ 1) (h1 : #V1 < n) (h2 : #V2 < n)
    (hE : ∀ x y, G.Adj x y → (x ∈ V1 ∧ y ∈ V1) ∨ (x ∈ V2 ∧ y ∈ V2)) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length := by
  have hsub : G.edgeFinset ⊆ (G.edgeFinset ∩ V1.sym2) ∪ (G.edgeFinset ∩ V2.sym2) := by
    intro e he'
    induction e using Sym2.ind with
    | h x y =>
      have hxy : G.Adj x y := by rwa [mem_edgeFinset, mem_edgeSet] at he'
      rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter, Finset.mem_sym2_iff,
        Finset.mem_sym2_iff]
      rcases hE x y hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · left
        refine ⟨he', fun a ha => ?_⟩
        rcases Sym2.mem_iff.1 ha with rfl | rfl <;> assumption
      · right
        refine ⟨he', fun a ha => ?_⟩
        rcases Sym2.mem_iff.1 ha with rfl | rfl <;> assumption
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hUI := Finset.card_union_add_card_inter V1 V2
  rw [hU, Finset.card_univ, hn] at hUI
  by_cases c1 : (k - 1) * (#V1 - 1) < 2 * #(G.edgeFinset ∩ V1.sym2)
  · exact apply_sub ih G hk V1 h1 c1
  by_cases c2 : (k - 1) * (#V2 - 1) < 2 * #(G.edgeFinset ∩ V2.sym2)
  · exact apply_sub ih G hk V2 h2 c2
  exfalso
  have h3 : (#V1 - 1) + (#V2 - 1) ≤ n - 1 := by omega
  have h4 := Nat.mul_le_mul_left (k - 1) h3
  rw [Nat.mul_add] at h4
  omega

lemma del_case {n : ℕ} (ih : ∀ m < n, EGP m) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 3 ≤ k) (hn : Fintype.card V = n)
    (hkn : k ≤ n) (he : (k - 1) * (n - 1) < 2 * #G.edgeFinset) (v : V)
    (hv : 2 * G.degree v ≤ k - 1) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ k ≤ c.length := by
  have hsub : G.edgeFinset ⊆ (G.edgeFinset ∩ (univ.erase v).sym2) ∪ G.incidenceFinset v := by
    intro e he'
    rw [Finset.mem_union, Finset.mem_inter, Finset.mem_sym2_iff, mem_incidenceFinset]
    by_cases hve : v ∈ e
    · right
      exact ⟨by rwa [mem_edgeFinset] at he', hve⟩
    · left
      refine ⟨he', fun a ha => ?_⟩
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ a⟩
      rintro rfl
      exact hve ha
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [card_incidenceFinset_eq_degree] at hc
  have hs : #(univ.erase v) = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hn]
  apply apply_sub ih G hk (univ.erase v) (by omega)
  rw [hs]
  have h5 : (k - 1) * (n - 1) = (k - 1) * (n - 1 - 1) + (k - 1) := by
    conv_lhs => rw [show n - 1 = (n - 1 - 1) + 1 by omega]
    rw [Nat.mul_add, Nat.mul_one]
  omega

lemma cut_sep {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v a b : V)
    (ha : a ≠ v) (hb : b ≠ v) (hcut : ∀ p : G.Walk a b, v ∈ p.support) :
    ∃ V1 V2 : Finset V, V1 ∪ V2 = univ ∧ #(V1 ∩ V2) ≤ 1 ∧ #V1 < Fintype.card V ∧
      #V2 < Fintype.card V ∧ ∀ x y, G.Adj x y → (x ∈ V1 ∧ y ∈ V1) ∨ (x ∈ V2 ∧ y ∈ V2) := by
  classical
  obtain ⟨R, hR⟩ : ∃ R : Finset V, ∀ w, w ∈ R ↔ ∃ p : G.Walk a w, v ∉ p.support :=
    ⟨univ.filter (fun w => ∃ p : G.Walk a w, v ∉ p.support), fun w => by simp⟩
  have hext : ∀ x y, G.Adj x y → x ∈ R → y ≠ v → y ∈ R := by
    intro x y hxy hx hy
    obtain ⟨p, hp⟩ := (hR x).1 hx
    refine (hR y).2 ⟨p.concat hxy, ?_⟩
    rw [Walk.support_concat, List.mem_append, List.mem_singleton]
    rintro (h | h)
    · exact hp h
    · exact hy h.symm
  refine ⟨insert v R, univ \ R, ?_, ?_, ?_, ?_, ?_⟩
  · apply Finset.eq_univ_iff_forall.2
    intro x
    by_cases hx : x ∈ R
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hx)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨Finset.mem_univ x, hx⟩)
  · have : insert v R ∩ (univ \ R) ⊆ {v} := by
      intro x hx
      rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_sdiff] at hx
      rw [Finset.mem_singleton]
      rcases hx with ⟨h | h, -, h'⟩
      · exact h
      · exact absurd h h'
    exact (Finset.card_le_card this).trans (Finset.card_singleton v).le
  · apply Finset.card_lt_univ_of_notMem (x := b)
    rw [Finset.mem_insert, not_or]
    refine ⟨hb, fun h => ?_⟩
    obtain ⟨p, hp⟩ := (hR b).1 h
    exact hp (hcut p)
  · apply Finset.card_lt_univ_of_notMem (x := a)
    rw [Finset.mem_sdiff, not_and, not_not]
    intro _
    refine (hR a).2 ⟨Walk.nil, ?_⟩
    rw [Walk.support_nil, List.mem_singleton]
    exact fun h => ha h.symm
  · intro x y hxy
    by_cases hx : x ∈ R
    · left
      refine ⟨Finset.mem_insert_of_mem hx, ?_⟩
      by_cases hyv : y = v
      · rw [hyv]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hext x y hxy hx hyv)
    · by_cases hy : y ∈ R
      · left
        refine ⟨?_, Finset.mem_insert_of_mem hy⟩
        by_cases hxv : x = v
        · rw [hxv]; exact Finset.mem_insert_self _ _
        · exact absurd (hext y x hxy.symm hy hxv) hx
      · right
        exact ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ x, hx⟩,
          Finset.mem_sdiff.2 ⟨Finset.mem_univ y, hy⟩⟩

lemma conn_of {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (h3 : 3 ≤ Fintype.card V)
    (h2c : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support) : G.Connected := by
  have hne : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  refine { preconnected := fun a b => ?_, nonempty := hne }
  by_cases hab : a = b
  · rw [hab]
  · have hcard : 1 < #(univ.erase a) := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
      omega
    obtain ⟨v, hv, hvb⟩ := Finset.exists_mem_ne hcard b
    obtain ⟨p, -⟩ := h2c v a b (Finset.ne_of_mem_erase hv).symm hvb.symm
    exact ⟨p⟩

lemma two_e_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * #G.edgeFinset ≤ Fintype.card V * (Fintype.card V - 1) := by
  have h := G.card_edgeFinset_le_card_choose_two
  rw [Nat.choose_two_right] at h
  have := Nat.mul_div_le (Fintype.card V * (Fintype.card V - 1)) 2
  omega

theorem main_ind (core : CoreStatement) (n : ℕ) : EGP n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ G _ k hn hk he
  have hkn : k ≤ n := by
    have h := two_e_le G
    rw [hn] at h
    have h' : (k - 1) * (n - 1) < n * (n - 1) := lt_of_lt_of_le he h
    have := Nat.lt_of_mul_lt_mul_right h'
    omega
  by_cases hA : ∃ v, 2 * G.degree v ≤ k - 1
  · obtain ⟨v, hv⟩ := hA
    exact del_case ih G hk hn hkn he v hv
  push Not at hA
  by_cases h2c : ∀ v a b : V, a ≠ v → b ≠ v → ∃ p : G.Walk a b, v ∉ p.support
  · have h3 : 3 ≤ Fintype.card V := by omega
    obtain ⟨u, c, hc, hlen⟩ := core G ((k + 1) / 2) (by omega) h3 (conn_of G h3 h2c) h2c
      (fun v => by have := hA v; omega)
    refine ⟨u, c, hc, le_trans ?_ hlen⟩
    rw [hn]
    exact Nat.le_min.2 ⟨hkn, by omega⟩
  · push Not at h2c
    obtain ⟨v, a, b, ha, hb, hcut⟩ := h2c
    obtain ⟨V1, V2, hU, hI, h1, h2, hE⟩ := cut_sep G v a b ha hb hcut
    rw [hn] at h1 h2
    exact sep_case ih G hk hn he V1 V2 hU hI h1 h2 hE

theorem frame : CoreStatement → H1Statement := by
  intro core V _ _ G _ k hk he
  classical
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  apply main_ind core (Fintype.card V) V G k rfl hk
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 1 := ⟨Fintype.card V - 1, by omega⟩
  rw [hm] at he ⊢
  rw [Nat.add_sub_cancel]
  rw [Nat.mul_add, Nat.mul_one] at he
  convert (show (k - 1) * m < 2 * #G.edgeFinset by omega) using 4

end OMA.EG


/-- The strict (n-1) form needed recursively on the parts, rather than the weaker public step. -/
theorem Wave10G.longCycle {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 3 ≤ k)
    (he : (k-1)*(Fintype.card V-1) < 2*G.edgeFinset.card) :
    ∃ (u : V) (w : G.Walk u u), w.IsCycle ∧ k ≤ w.length :=
  OMA.EG.main_ind OMA.EG.core (Fintype.card V) V G k rfl hk he


namespace Wave10G

open SimpleGraph OMA.S_opg_forcing_a_2_regular_minor

noncomputable def Budget (k : ℕ) : ℝ := 2/3*(k : ℝ)-1

/-- Csóka–Lo–Norin–Wu–Yepremyan, Theorem 7, induced-subset version. -/
def Split : Prop := ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (s t : ℝ), 1 ≤ s → 1 ≤ t → Dense G (s+t+1) →
    ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      Dense (G.induce (A : Set V)) s ∧ Dense (G.induce (B : Set V)) t

theorem three_le {W : Type} [Fintype W] [Nonempty W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (h : H.IsRegularOfDegree 2) : 3 ≤ Fintype.card W := by
  classical
  obtain ⟨w⟩ := ‹Nonempty W›
  have hw : w ∉ H.neighborFinset w := by simp
  have hcard := Finset.card_le_univ (insert w (H.neighborFinset w))
  rwa [Finset.card_insert_of_notMem hw, card_neighborFinset_eq_degree, h w] at hcard

theorem connectedCase {W V : Type} [Fintype W] [Fintype V] [Nonempty V]
    (H : SimpleGraph W) [DecidableRel H.Adj] (G : SimpleGraph V)
    (hreg : H.IsRegularOfDegree 2) (hc : H.Connected)
    (hd : Dense G (Budget (Fintype.card W))) : IsMinor H G := by
  classical
  let _ := hc.nonempty
  let k := Fintype.card W
  have hk : 3 ≤ k := three_le H hreg
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos
  have he : (k-1)*(Fintype.card V-1) < 2*G.edgeFinset.card := by
    change Budget k * ((Fintype.card V : ℝ)-1) < _ at hd
    have hkr : 3 ≤ (k : ℝ) := by exact_mod_cast hk
    have hnr : 1 ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
    have hsub : (k : ℝ)-1 ≤ 2*Budget k := by unfold Budget; linarith
    have hr := mul_le_mul_of_nonneg_right hsub (sub_nonneg.mpr hnr)
    have hz : ((k : ℝ)-1)*((Fintype.card V : ℝ)-1) < 2*(G.edgeFinset.card : ℝ) := by linarith
    exact_mod_cast (by simpa [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_sub hn] using hz :
      (((k-1 : ℕ) : ℝ))*((Fintype.card V-1 : ℕ) : ℝ) < 2*(G.edgeFinset.card : ℝ))
  obtain ⟨u,w,hw,hl⟩ := longCycle G k hk he
  let e := (Fintype.equivFin W).symm
  let I := SimpleGraph.Iso.comap e H
  have hreg' : (H.comap e).IsRegularOfDegree 2 := fun i => (I.degree_eq i).symm.trans (hreg _)
  obtain ⟨P,hP,dP,eP⟩ := cycleMinor k (H.comap e) hreg' (I.connected_iff.mpr hc) V G u w hw hl
  exact ⟨P ∘ I.symm, fun i => hP _, fun i j hij => dP (I.symm.injective.ne hij),
    fun i j h => eP _ _ (I.symm.map_rel_iff.mpr h)⟩

theorem pack (split : Split) (k : ℕ) : ∀ (W : Type) [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj], Fintype.card W = k → H.IsRegularOfDegree 2 →
    ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V),
    Dense G (Budget k) → IsMinor H G := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro W _ H _ hcard hreg V _ _ G hd
    classical
    cases isEmpty_or_nonempty W with
    | inl hempty => exact ⟨fun _ => ∅, isEmptyElim, fun i => isEmptyElim i, isEmptyElim⟩
    | inr hne =>
      have := hne
      by_cases hconn : H.Connected
      · exact connectedCase H G hreg hconn (hcard ▸ hd)
      obtain ⟨w⟩ := hne
      obtain ⟨v,hv⟩ : ∃ v, ¬ H.Reachable w v := by
        by_contra! h
        exact hconn ((connected_iff_exists_forall_reachable H).mpr ⟨w,h⟩)
      let S : Set W := {z | H.Reachable w z}
      let T : Set W := Sᶜ
      have hw : w ∈ S := Reachable.refl _
      have hv' : v ∈ T := hv
      let _ : Nonempty S := ⟨⟨w,hw⟩⟩
      let _ : Nonempty T := ⟨⟨v,hv'⟩⟩
      have cut : ∀ {i j}, H.Adj i j → (i ∈ S ↔ j ∈ S) := fun h =>
        ⟨fun p => p.trans h.reachable, fun p => p.trans h.symm.reachable⟩
      have regS : (H.induce S).IsRegularOfDegree 2 := fun x =>
        (degree_induce_of_neighborSet_subset (fun _ hy => (cut hy).mp x.property)).trans (hreg _)
      have regT : (H.induce T).IsRegularOfDegree 2 := fun x =>
        (degree_induce_of_neighborSet_subset (fun _ hy h => x.property ((cut hy).mpr h))).trans (hreg _)
      have hsum : Fintype.card S + Fintype.card T = k := by
        rw [← hcard]
        have hz := Fintype.card_congr (Equiv.sumCompl (fun i => i ∈ S))
        rw [Fintype.card_sum] at hz
        simp only [← Nat.card_eq_fintype_card] at hz ⊢
        exact hz
      have hS := three_le _ regS
      have hT := three_le _ regT
      have ds : 1 ≤ Budget (Fintype.card S) := by
        unfold Budget; have : (3 : ℝ) ≤ Fintype.card S := by exact_mod_cast hS
        linarith
      have dt : 1 ≤ Budget (Fintype.card T) := by
        unfold Budget; have : (3 : ℝ) ≤ Fintype.card T := by exact_mod_cast hT
        linarith
      have hb : Budget (Fintype.card S) + Budget (Fintype.card T) + 1 = Budget k := by
        rw [← hsum]; simp only [Budget, Nat.cast_add]; ring
      obtain ⟨A,B,ha,hb',dis,hA,hB⟩ := split V G _ _ ds dt (hb.symm ▸ hd)
      let _ : Nonempty ↥A := ha.to_subtype
      let _ : Nonempty ↥B := hb'.to_subtype
      exact joinMinor H G S _ _ (Finset.disjoint_coe.mpr dis) cut
        (ih _ (by omega) S _ rfl regS _ _ hA) (ih _ (by omega) T _ rfl regT _ _ hB)

theorem wholeRootOfSplit (h : Split) :
    ∀ (t : ℕ) (H : SimpleGraph (Fin t)) [DecidableRel H.Adj],
    H.IsRegularOfDegree 2 → ∀ (V : Type) [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    (4/3 : ℝ)*t-2 ≤ 2*(G.edgeFinset.card : ℝ)/Fintype.card V → IsMinor H G := by
  intro t H _ hreg V _ _ G _ havg
  cases isEmpty_or_nonempty (Fin t) with
  | inl hempty => exact ⟨fun _ => ∅, isEmptyElim, fun i => isEmptyElim i, isEmptyElim⟩
  | inr hne =>
    have := hne
    have h3 := three_le _ hreg
    rw [Fintype.card_fin] at h3
    apply pack h t _ H (Fintype.card_fin t) hreg V G
    unfold Dense Budget
    simp only [← SimpleGraph.card_edgeSet, ← Nat.card_eq_fintype_card] at havg ⊢
    exact threshold (by exact_mod_cast h3) (by exact_mod_cast Nat.card_pos) havg

end Wave10G

theorem OMA.solution : type_of% @OMA.S_opg_forcing_a_2_regular_minor.main := by
  apply Wave10G.wholeRootOfSplit
  intro V _ _ G s t hs ht hd
  classical
  exact Wave10G.densitySplit G s t hs ht hd

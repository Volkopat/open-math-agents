import OMAReductions.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1
import Mathlib

/-! Far-cut bound for Erdős problem 1186. The two finite certificates are due to Carlos Toledo.
The analytic discretization and polynomial soundness proofs adapt Chandler Snively's
Quana Labs formalization at revision 0b0155ead09841892690b9f9c469d1ff0edaff4c.
Apache License 2.0, copyright 2026 Chandler Snively. The two 146-cell inputs are the files
slab-2_5-9_20-g8_4_0.json and slab-9_20-1_2-g8_4_0.json from cert-machine,
revision 47a01c2e076d3b0e5e95262bb1030f5ed5873382. Each matrix identity and
inequality in this file is checked using exact arithmetic. -/

section
namespace Erdos1186Day

def c1 (x : ℕ) : Bool :=
  bif Nat.ble x 28 then true else bif Nat.ble x 34 then false else bif Nat.ble x 62 then true else
  bif Nat.ble x 99 then false else bif Nat.ble x 158 then true else bif Nat.ble x 274 then false else
  bif Nat.ble x 390 then true else bif Nat.ble x 449 then false else bif Nat.ble x 486 then true else
  bif Nat.ble x 514 then false else bif Nat.ble x 520 then true else false
def ck (k x : ℕ) : Bool := c1 ((x + (k - 1)) / k)

end Erdos1186Day

namespace Erdos1186Night2

open Finset
def sg (c : ℕ → Bool) (x : ℕ) : ℤ := if c x then 1 else -1
def pre (s : ℕ → ℤ) (t : ℕ) : ℤ := ∑ x ∈ Ioc 0 t, s x

lemma pre_zero (s : ℕ → ℤ) : pre s 0 = 0 := by simp [pre]

lemma pre_succ (s : ℕ → ℤ) (t : ℕ) : pre s (t+1) = pre s t + s (t+1) := by
  unfold pre
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le t)]

lemma sum_Ioc_eq (s : ℕ → ℤ) {a b : ℕ} (h : a ≤ b) : ∑ x ∈ Ioc a b, s x = pre s b - pre s a := by
  unfold pre
  rw [← Finset.sum_Ioc_consecutive s (Nat.zero_le a) h]; ring

end Erdos1186Night2

namespace Erdos1186Night2M2

def K4 (L p q : ℕ) : ℕ :=
  if 1 ≤ 2 * (q : ℤ) - p - 1 ∧ 2 * (q : ℤ) - p - 1 ≤ (L : ℤ) - 2 then 4
  else if 2 * (q : ℤ) - p - 1 = 0 ∨ 2 * (q : ℤ) - p - 1 = (L : ℤ) - 1 then 3
  else if 2 * (q : ℤ) - p - 1 = -1 ∨ 2 * (q : ℤ) - p - 1 = (L : ℤ) then 1
  else 0

end Erdos1186Night2M2
end

section
namespace Erdos1186Ex

structure Grid where
  pts : List ℕ
  a : List ℚ
  b : List ℚ

def G8 : Grid where
  pts := [0, 8, 16, 24, 32, 40, 48, 56, 64, 68, 72, 80, 88, 96, 104, 112, 120, 124, 128, 136, 144, 152, 160, 168, 176, 184, 192, 198, 200, 208, 216, 224, 232, 240, 248, 256, 264, 272, 280, 288, 296, 304, 312, 316, 320, 328, 336, 344, 352, 360, 368, 376, 384, 392, 400, 408, 416, 424, 432, 440, 448, 456, 464, 472, 480, 488, 496, 504, 512, 520, 528, 536, 544, 548, 552, 560, 568, 576, 584, 592, 600, 608, 616, 624, 632, 640, 648, 656, 664, 672, 680, 688, 696, 704, 712, 720, 728, 736, 744, 752, 760, 768, 776, 780, 784, 792, 800, 808, 816, 824, 832, 840, 848, 856, 864, 872, 880, 888, 896, 898, 904, 912, 920, 928, 936, 944, 952, 960, 968, 972, 976, 984, 992, 1000, 1008, 1016, 1024, 1028, 1032, 1040, 1048, 1056, 1064, 1072, 1080, 1088, 1096]
  a := [(9 / 37538 : ℚ), (7 / 37538 : ℚ), (5 / 37538 : ℚ), (2 / 18769 : ℚ), (2 / 18769 : ℚ), (1 / 18769 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 37538 : ℚ), (3 / 37538 : ℚ), (5 / 37538 : ℚ), (13 / 75076 : ℚ), (9 / 75076 : ℚ), (3 / 75076 : ℚ), (0 : ℚ), (0 : ℚ), (3 / 75076 : ℚ), (9 / 75076 : ℚ), (13 / 75076 : ℚ), (17 / 75076 : ℚ), (15 / 75076 : ℚ), (11 / 75076 : ℚ), (7 / 75076 : ℚ), (3 / 75076 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 75076 : ℚ), (5 / 75076 : ℚ), (9 / 75076 : ℚ), (13 / 75076 : ℚ), (17 / 75076 : ℚ), (21 / 75076 : ℚ), (25 / 75076 : ℚ), (27 / 75076 : ℚ), (29 / 75076 : ℚ), (27 / 75076 : ℚ), (21 / 75076 : ℚ), (15 / 75076 : ℚ), (9 / 75076 : ℚ), (3 / 75076 : ℚ), (0 : ℚ), (0 : ℚ), (3 / 75076 : ℚ), (9 / 75076 : ℚ), (15 / 75076 : ℚ), (21 / 75076 : ℚ), (27 / 75076 : ℚ), (33 / 75076 : ℚ), (39 / 75076 : ℚ), (45 / 75076 : ℚ), (51 / 75076 : ℚ), (13 / 18769 : ℚ), (12 / 18769 : ℚ), (11 / 18769 : ℚ), (10 / 18769 : ℚ), (9 / 18769 : ℚ), (8 / 18769 : ℚ), (7 / 18769 : ℚ), (55 / 150152 : ℚ), (31 / 75076 : ℚ), (35 / 75076 : ℚ), (37 / 75076 : ℚ), (39 / 75076 : ℚ), (33 / 75076 : ℚ), (27 / 75076 : ℚ), (21 / 75076 : ℚ), (39 / 150152 : ℚ), (15 / 75076 : ℚ), (9 / 75076 : ℚ), (3 / 75076 : ℚ), (0 : ℚ), (0 : ℚ), (3 / 75076 : ℚ), (9 / 75076 : ℚ), (15 / 75076 : ℚ), (39 / 150152 : ℚ), (21 / 75076 : ℚ), (27 / 75076 : ℚ), (33 / 75076 : ℚ), (39 / 75076 : ℚ), (37 / 75076 : ℚ), (35 / 75076 : ℚ), (31 / 75076 : ℚ), (55 / 150152 : ℚ), (7 / 18769 : ℚ), (8 / 18769 : ℚ), (9 / 18769 : ℚ), (10 / 18769 : ℚ), (11 / 18769 : ℚ), (12 / 18769 : ℚ), (13 / 18769 : ℚ), (51 / 75076 : ℚ), (45 / 75076 : ℚ), (39 / 75076 : ℚ), (33 / 75076 : ℚ), (27 / 75076 : ℚ), (21 / 75076 : ℚ), (15 / 75076 : ℚ), (9 / 75076 : ℚ), (3 / 75076 : ℚ), (0 : ℚ), (0 : ℚ), (3 / 75076 : ℚ), (9 / 75076 : ℚ), (15 / 75076 : ℚ), (21 / 75076 : ℚ), (27 / 75076 : ℚ), (29 / 75076 : ℚ), (27 / 75076 : ℚ), (25 / 75076 : ℚ), (21 / 75076 : ℚ), (17 / 75076 : ℚ), (13 / 75076 : ℚ), (9 / 75076 : ℚ), (5 / 75076 : ℚ), (1 / 75076 : ℚ), (0 : ℚ), (0 : ℚ), (3 / 75076 : ℚ), (7 / 75076 : ℚ), (11 / 75076 : ℚ), (15 / 75076 : ℚ), (17 / 75076 : ℚ), (13 / 75076 : ℚ), (9 / 75076 : ℚ), (3 / 75076 : ℚ), (0 : ℚ), (0 : ℚ), (3 / 75076 : ℚ), (9 / 75076 : ℚ), (13 / 75076 : ℚ), (5 / 37538 : ℚ), (3 / 37538 : ℚ), (1 / 37538 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1 / 18769 : ℚ), (2 / 18769 : ℚ), (2 / 18769 : ℚ), (5 / 37538 : ℚ), (7 / 37538 : ℚ), (9 / 37538 : ℚ)]
  b := [(1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 75076 : ℚ), (1 / 75076 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 75076 : ℚ), (1 / 150152 : ℚ), (1 / 150152 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 75076 : ℚ), (1 / 37538 : ℚ), (3 / 75076 : ℚ), (3 / 300304 : ℚ), (3 / 300304 : ℚ), (3 / 75076 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 75076 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (9 / 600608 : ℚ), (1 / 600608 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 75076 : ℚ), (1 / 75076 : ℚ), (1 / 75076 : ℚ), (3 / 300304 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 300304 : ℚ), (3 / 300304 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 300304 : ℚ), (1 / 75076 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 75076 : ℚ), (1 / 37538 : ℚ), (1 / 75076 : ℚ), (1 / 75076 : ℚ), (3 / 300304 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 300304 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 300304 : ℚ), (3 / 300304 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 300304 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 300304 : ℚ), (1 / 75076 : ℚ), (1 / 75076 : ℚ), (1 / 37538 : ℚ), (1 / 75076 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 75076 : ℚ), (3 / 300304 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 300304 : ℚ), (3 / 300304 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 75076 : ℚ), (3 / 300304 : ℚ), (1 / 75076 : ℚ), (1 / 75076 : ℚ), (1 / 75076 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 600608 : ℚ), (9 / 600608 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 75076 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (3 / 75076 : ℚ), (3 / 300304 : ℚ), (3 / 300304 : ℚ), (3 / 75076 : ℚ), (1 / 37538 : ℚ), (1 / 75076 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 150152 : ℚ), (1 / 150152 : ℚ), (1 / 75076 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 75076 : ℚ), (1 / 75076 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ), (1 / 37538 : ℚ)]

end Erdos1186Ex
end

section
namespace Erdos1186Ex

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

def nn (w : ℕ) : ℕ := 1096 * w

def sstar (w x : ℕ) : ℤ := sg (ck (2 * w)) x

def rdI (n x y : ℕ) : ℤ := if 1 ≤ 2 * (y : ℤ) - x ∧ 2 * (y : ℤ) - x ≤ n then 1 else 0

def Qd (n : ℕ) (u : ℕ → ℤ) : ℤ := ∑ x ∈ Icc 1 n, ∑ y ∈ Icc 1 n, rdI n x y * u x * u y

def H2 (w x : ℕ) : ℤ :=
  -sstar w x * (∑ y ∈ Icc 1 (nn w), rdI (nn w) x y * sstar w y + ∑ e ∈ Icc 1 (nn w), rdI (nn w) e x * sstar w e)

def IsInd (σ : ℕ → ℤ) : Prop := ∀ x, σ x = 0 ∨ σ x = 1

namespace Grid

def N (G : Grid) : ℕ := G.pts.length - 1

def lo (G : Grid) (i : ℕ) : ℕ := G.pts.getD i 0
def hi (G : Grid) (i : ℕ) : ℕ := G.pts.getD (i + 1) 0

def len (G : Grid) (i : ℕ) : ℕ := G.hi i - G.lo i

def wt (G : Grid) (i : ℕ) : ℚ := (G.len i : ℚ) / 1096
def ai (G : Grid) (i : ℕ) : ℚ := G.a.getD i 0
def bi (G : Grid) (i : ℕ) : ℚ := G.b.getD i 0

def sgn (G : Grid) (i : ℕ) : ℤ := sg c1 (G.lo i / 2 + 1)

def A4 (G : Grid) (i j : ℕ) : ℕ := ∑ p ∈ Ioc (G.lo i) (G.hi i), ∑ q ∈ Ioc (G.lo j) (G.hi j), K4 1096 p q

def cell (G : Grid) (w i : ℕ) : Finset ℕ := Ioc (G.lo i * w) (G.hi i * w)

noncomputable def yv (G : Grid) (w : ℕ) (σ : ℕ → ℤ) (i : ℕ) : ℝ :=
  ((∑ x ∈ G.cell w i, σ x : ℤ) : ℝ) / ((G.len i * w : ℕ) : ℝ)

noncomputable def pterm (G : Grid) (i j : ℕ) (yi yj : ℝ) : ℝ :=
  let P : ℝ := (G.wt i : ℝ) * G.wt j * yi * yj
  let Ain : ℝ := (G.A4 i j : ℝ) / (4 * 1096 ^ 2)
  let Aout : ℝ := (G.wt i : ℝ) * G.wt j - Ain
  if G.sgn i * G.sgn j = 1 then max 0 (P - Aout) else max (-Ain) (-P)

noncomputable def Lval (G : Grid) (y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range G.N, ((G.ai i : ℝ) * y i + (G.bi i : ℝ) * y i ^ 2)
    + ∑ i ∈ range G.N, ∑ j ∈ range G.N, G.pterm i j (y i) (y j)

noncomputable def mval (G : Grid) (y : ℕ → ℝ) : ℝ := ∑ i ∈ range G.N, (G.wt i : ℝ) * y i

def WF (G : Grid) : Prop :=
  G.pts.head? = some 0 ∧ G.pts.getLast? = some 1096 ∧ G.pts.Pairwise (· < ·) ∧
    G.a.length = G.N ∧ G.b.length = G.N ∧
    ∀ i < G.N, ∀ k ∈ Ico (G.lo i) (G.hi i), c1 (k / 2 + 1) = c1 (G.lo i / 2 + 1)

instance (G : Grid) : Decidable G.WF := by unfold WF; infer_instance

end Grid

def BathOK (G : Grid) : Prop :=
  ∃ C : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ σ : ℕ → ℤ, IsInd σ → ∀ i < G.N,
    2 * (nn w : ℝ) ^ 2 * ((G.ai i : ℝ) * G.yv w σ i + (G.bi i : ℝ) * G.yv w σ i ^ 2) - C * w
      ≤ ((∑ x ∈ G.cell w i, H2 w x * σ x : ℤ) : ℝ)

def PairOK (G : Grid) : Prop :=
  ∃ C : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ σ : ℕ → ℤ, IsInd σ →
    (nn w : ℝ) ^ 2 * ∑ i ∈ range G.N, ∑ j ∈ range G.N, G.pterm i j (G.yv w σ i) (G.yv w σ j) - C * w
      ≤ (Qd (nn w) (fun x => sstar w x * σ x) : ℝ)

def RegionLB (G : Grid) (lo hi : ℚ) : Prop :=
  ∀ y : ℕ → ℝ, (∀ i < G.N, 0 ≤ y i ∧ y i ≤ 1) → (lo : ℝ) ≤ G.mval y → G.mval y ≤ hi → 0 ≤ G.Lval y

end Erdos1186Ex
end

section
open Finset Filter

namespace Erdos1186Ex

open Erdos1186Day Erdos1186Night2 Erdos1186Night2M2
def crossA (n : ℕ) (s σ : ℕ → ℤ) : ℤ := ∑ x ∈ Icc 1 n, ∑ y ∈ Icc 1 n, rdI n x y * (s x * σ x) * s y
def crossB (n : ℕ) (s σ : ℕ → ℤ) : ℤ := ∑ x ∈ Icc 1 n, ∑ y ∈ Icc 1 n, rdI n x y * s x * (s y * σ y)

lemma expansion_gen (n : ℕ) (s σ : ℕ → ℤ) :
    Qd n (fun x => s x * (1 - 2 * σ x))
      = Qd n s - 2 * (crossA n s σ + crossB n s σ) + 4 * Qd n (fun x => s x * σ x) := by
  unfold Qd crossA crossB
  have e : ∀ x y : ℕ, rdI n x y * (s x * (1 - 2 * σ x)) * (s y * (1 - 2 * σ y))
      = rdI n x y * s x * s y - 2 * (rdI n x y * (s x * σ x) * s y + rdI n x y * s x * (s y * σ y))
        + 4 * (rdI n x y * (s x * σ x) * (s y * σ y)) := by
    intro x y; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

lemma H2_sum (n : ℕ) (s σ : ℕ → ℤ) :
    ∑ x ∈ Icc 1 n, (-s x * (∑ y ∈ Icc 1 n, rdI n x y * s y + ∑ e ∈ Icc 1 n, rdI n e x * s e)) * σ x
      = -(crossA n s σ + crossB n s σ) := by
  have hA : crossA n s σ = ∑ x ∈ Icc 1 n, (s x * σ x) * ∑ y ∈ Icc 1 n, rdI n x y * s y := by
    unfold crossA
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
  have hB : crossB n s σ = ∑ x ∈ Icc 1 n, (s x * σ x) * ∑ e ∈ Icc 1 n, rdI n e x * s e := by
    unfold crossB
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
  rw [hA, hB, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro x _
  ring

lemma expansion (w : ℕ) (σ : ℕ → ℤ) :
    Qd (nn w) (fun x => sstar w x * (1 - 2 * σ x))
      = Qd (nn w) (sstar w) + 2 * ∑ x ∈ Icc 1 (nn w), H2 w x * σ x
        + 4 * Qd (nn w) (fun x => sstar w x * σ x) := by
  have h1 := expansion_gen (nn w) (sstar w) σ
  have h2 := H2_sum (nn w) (sstar w) σ
  have h3 : ∑ x ∈ Icc 1 (nn w), H2 w x * σ x
      = -(crossA (nn w) (sstar w) σ + crossB (nn w) (sstar w) σ) := by
    unfold H2; exact h2
  rw [h1, h3]; ring

namespace Grid

lemma length_eq (G : Grid) (hG : G.WF) : G.pts.length = G.N + 1 := by
  obtain ⟨h0, _⟩ := hG
  unfold N
  rcases h : G.pts with _ | ⟨a, t⟩
  · simp [h] at h0
  · simp

lemma lo_zero (G : Grid) (hG : G.WF) : G.lo 0 = 0 := by
  obtain ⟨h0, _⟩ := hG
  unfold lo
  rcases h : G.pts with _ | ⟨a, t⟩
  · simp [h] at h0
  · simp [h] at h0 ⊢; exact h0

lemma lo_N (G : Grid) (hG : G.WF) : G.lo G.N = 1096 := by
  have hlen := length_eq G hG
  obtain ⟨_, h1, _⟩ := hG
  unfold lo
  rw [List.getLast?_eq_getElem?] at h1
  rw [List.getD_eq_getElem?_getD]
  simp only [hlen, Nat.add_sub_cancel] at h1
  rw [h1]; rfl

lemma lo_lt_hi (G : Grid) (hG : G.WF) {i : ℕ} (hiN : i < G.N) : G.lo i < G.hi i := by
  have hlen := length_eq G hG
  obtain ⟨_, _, hp, _⟩ := hG
  unfold lo hi
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  exact List.pairwise_iff_getElem.mp hp i (i + 1) (by omega) (by omega) (by omega)

lemma cells_sum (G : Grid) (hG : G.WF) (w : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ range G.N, ∑ x ∈ G.cell w i, f x = ∑ x ∈ Icc 1 (nn w), f x := by
  have e1 : ∀ i ∈ range G.N,
      ∑ x ∈ G.cell w i, f x = pre f (G.lo (i + 1) * w) - pre f (G.lo i * w) := by
    intro i hi
    have h := (G.lo_lt_hi hG (mem_range.mp hi)).le
    unfold cell
    exact sum_Ioc_eq f (Nat.mul_le_mul_right w h)
  rw [Finset.sum_congr rfl e1, Finset.sum_range_sub (fun i => pre f (G.lo i * w)), G.lo_N hG, G.lo_zero hG]
  unfold pre nn
  have : Ioc 0 (1096 * w) = Icc 1 (1096 * w) := by
    ext x; simp only [mem_Ioc, mem_Icc]; omega
  rw [this]; simp

lemma cell_card (G : Grid) (w i : ℕ) : (G.cell w i).card = G.len i * w := by
  unfold cell len; rw [Nat.card_Ioc, Nat.sub_mul]

lemma yv_mem (G : Grid) (hG : G.WF) (w : ℕ) (hw : 1 ≤ w) (σ : ℕ → ℤ) (hσ : IsInd σ) {i : ℕ}
    (hiN : i < G.N) : 0 ≤ G.yv w σ i ∧ G.yv w σ i ≤ 1 := by
  have hlen : 0 < G.len i := by have := G.lo_lt_hi hG hiN; unfold len; omega
  have hpos : (0 : ℝ) < ((G.len i * w : ℕ) : ℝ) := by
    have : 0 < G.len i * w := Nat.mul_pos hlen (by omega)
    exact_mod_cast this
  have h0 : 0 ≤ ∑ x ∈ G.cell w i, σ x :=
    Finset.sum_nonneg (fun x _ => by rcases hσ x with h | h <;> simp [h])
  have h1 : ∑ x ∈ G.cell w i, σ x ≤ ((G.len i * w : ℕ) : ℤ) := by
    have : ∑ x ∈ G.cell w i, σ x ≤ ∑ _x ∈ G.cell w i, (1 : ℤ) :=
      Finset.sum_le_sum (fun x _ => by rcases hσ x with h | h <;> simp [h])
    simpa [cell_card] using this
  unfold yv
  constructor
  · exact div_nonneg (by exact_mod_cast h0) hpos.le
  · rw [div_le_one hpos]; exact_mod_cast h1

lemma mval_yv (G : Grid) (hG : G.WF) (w : ℕ) (hw : 1 ≤ w) (σ : ℕ → ℤ) :
    G.mval (G.yv w σ) = ((∑ x ∈ Icc 1 (nn w), σ x : ℤ) : ℝ) / (nn w : ℝ) := by
  have hn : (0 : ℝ) < (nn w : ℝ) := by
    have : 0 < nn w := by unfold nn; omega
    exact_mod_cast this
  have e : ∀ i ∈ range G.N, (G.wt i : ℝ) * G.yv w σ i
      = ((∑ x ∈ G.cell w i, σ x : ℤ) : ℝ) / (nn w : ℝ) := by
    intro i hi
    have hlen : 0 < G.len i := by have := G.lo_lt_hi hG (mem_range.mp hi); unfold len; omega
    have hlenR : (0 : ℝ) < (G.len i : ℝ) := by exact_mod_cast hlen
    have hwR : (0 : ℝ) < (w : ℝ) := by exact_mod_cast (by omega : 0 < w)
    unfold wt yv nn
    push_cast
    field_simp
  unfold mval
  rw [Finset.sum_congr rfl e, ← Finset.sum_div]
  congr 1
  rw [← cells_sum G hG w σ]
  push_cast
  rfl

end Grid
noncomputable def msum (w : ℕ) (σ : ℕ → ℤ) : ℝ := ((∑ x ∈ Icc 1 (nn w), σ x : ℤ) : ℝ) / (nn w : ℝ)

lemma lval_nonneg (G : Grid) (hG : G.WF) (lo hi : ℚ) (r : RegionLB G lo hi) (w : ℕ) (hw : 1 ≤ w)
    (σ : ℕ → ℤ) (hσ : IsInd σ) (hlo : (lo : ℝ) ≤ msum w σ) (hhi : msum w σ ≤ hi) :
    0 ≤ G.Lval (G.yv w σ) :=
  r (G.yv w σ) (fun i hi => Grid.yv_mem G hG w hw σ hσ hi)
    (by rw [Grid.mval_yv G hG w hw σ]; exact hlo) (by rw [Grid.mval_yv G hG w hw σ]; exact hhi)
end Erdos1186Ex
end

section
namespace Erdos1186Ex
namespace Pair

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

def Qc (w : ℕ) : ℕ := ((range w ×ˢ range w).filter fun ab : ℕ × ℕ => 2 * ab.2 + 1 ≤ ab.1).card

def Rc (w : ℕ) : ℕ := ((range w ×ˢ range w).filter fun ab : ℕ × ℕ => w + ab.1 ≤ 2 * ab.2).card

theorem Qc_succ (w : ℕ) : Qc (w + 1) = Qc w + (w + 1) / 2 := by
  unfold Qc
  have h : (range (w + 1) ×ˢ range (w + 1)).filter (fun ab : ℕ × ℕ => 2 * ab.2 + 1 ≤ ab.1) =
      (range w ×ˢ range w).filter (fun ab : ℕ × ℕ => 2 * ab.2 + 1 ≤ ab.1) ∪
        (range ((w + 1) / 2)).image (fun b => (w, b)) := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product, mem_range, mem_union, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨ha, hb⟩, h⟩
      by_cases haw : a < w
      · left; exact ⟨⟨haw, by omega⟩, h⟩
      · right; exact ⟨b, by omega, by omega, rfl⟩
    · rintro (⟨⟨ha, hb⟩, h⟩ | ⟨b', hb', h1, h2⟩)
      · exact ⟨⟨by omega, by omega⟩, h⟩
      · subst h2; subst h1
        exact ⟨⟨by omega, by omega⟩, by omega⟩
  rw [h, card_union_of_disjoint, card_image_of_injective _ (fun b b' hbb => by simpa using hbb), card_range]
  rw [disjoint_left]
  rintro ⟨a, b⟩ h1 h2
  simp only [mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq] at h1 h2
  obtain ⟨b', _, h3, _⟩ := h2
  omega

theorem Qc_eq (w : ℕ) : 4 * Qc w + w % 2 = w * w := by
  induction w with
  | zero => simp [Qc]
  | succ w ih =>
    rw [Qc_succ]
    have h : (w + 1) * (w + 1) = w * w + 2 * w + 1 := by ring
    rw [h]
    generalize w * w = s at *
    omega

theorem Rc_eq (w : ℕ) : Rc w = Qc w := by
  unfold Rc Qc
  refine card_nbij' (fun ab => (w - 1 - ab.1, w - 1 - ab.2)) (fun ab => (w - 1 - ab.1, w - 1 - ab.2)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at h ⊢
    omega
  · rintro ⟨a, b⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at h ⊢
    omega
  · rintro ⟨a, b⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at h ⊢
    ext <;> simp <;> omega
  · rintro ⟨a, b⟩ h
    simp only [coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at h ⊢
    ext <;> simp <;> omega

theorem sum_Ioc_shift {M : Type*} [AddCommMonoid M] (c w : ℕ) (f : ℕ → M) :
    ∑ x ∈ Ioc c (c + w), f x = ∑ a ∈ range w, f (c + a + 1) := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [← Nat.add_assoc, Finset.sum_Ioc_succ_top (by omega), ih, Finset.sum_range_succ]

def Npq (w p q : ℕ) : ℤ :=
  ∑ x ∈ Ioc ((p - 1) * w) (p * w), ∑ y ∈ Ioc ((q - 1) * w) (q * w), rdI (nn w) x y

theorem unit_mul (w p : ℕ) (hp : 1 ≤ p) : p * w = (p - 1) * w + w := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  simp [Nat.add_mul]

theorem Npq_eq (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    Npq w p q = (((range w ×ˢ range w).filter fun ab : ℕ × ℕ =>
      0 ≤ ((2 * (q : ℤ) - p - 1) * w) + 2 * ab.2 - ab.1 ∧
        ((2 * (q : ℤ) - p - 1) * w) + 2 * ab.2 - ab.1 + 1 ≤ 1096 * w).card : ℤ) := by
  unfold Npq
  rw [unit_mul w p hp, unit_mul w q hq]
  simp_rw [sum_Ioc_shift]
  rw [← sum_product']
  simp only [rdI]
  rw [sum_boole]
  congr 2
  apply filter_congr
  intro ab _
  simp only [nn]
  push_cast [Nat.cast_sub hp, Nat.cast_sub hq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

theorem Npq_full (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (h1 : 1 ≤ 2 * (q : ℤ) - p - 1)
    (h2 : 2 * (q : ℤ) - p - 1 ≤ 1094) : Npq w p q = (w : ℤ) * w := by
  rw [Npq_eq w p q hp hq]
  have e1 : (2 * (q : ℤ) - p - 1) * w ≥ w := by nlinarith [(Nat.cast_nonneg w : (0 : ℤ) ≤ w)]
  have e2 : (2 * (q : ℤ) - p - 1) * w ≤ 1094 * w := by nlinarith [(Nat.cast_nonneg w : (0 : ℤ) ≤ w)]
  generalize (2 * (q : ℤ) - p - 1) * w = D at *
  rw [filter_true_of_mem, card_product, card_range]
  · push_cast; ring
  · rintro ⟨a, b⟩ hab
    simp only [mem_product, mem_range] at hab
    constructor <;> omega

theorem Npq_zero (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (h : 2 * (q : ℤ) - p - 1 ≤ -2 ∨ 1097 ≤ 2 * (q : ℤ) - p - 1) : Npq w p q = 0 := by
  rw [Npq_eq w p q hp hq]
  have hw : (0 : ℤ) ≤ w := Nat.cast_nonneg w
  have e : (2 * (q : ℤ) - p - 1) * w ≤ -2 * w ∨ 1097 * w ≤ (2 * (q : ℤ) - p - 1) * w := by
    rcases h with h | h
    · left; nlinarith
    · right; nlinarith
  generalize (2 * (q : ℤ) - p - 1) * w = D at *
  rw [filter_false_of_mem]
  · simp
  · rintro ⟨a, b⟩ hab
    simp only [mem_product, mem_range] at hab
    omega

theorem Npq_m0 (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hm : 2 * (q : ℤ) - p - 1 = 0) :
    Npq w p q = (w : ℤ) * w - Qc w := by
  rw [Npq_eq w p q hp hq, hm]
  have h := card_filter_add_card_filter_not (s := range w ×ˢ range w)
    (fun ab : ℕ × ℕ => 2 * ab.2 + 1 ≤ ab.1)
  rw [card_product, card_range] at h
  have e : (range w ×ˢ range w).filter (fun ab : ℕ × ℕ =>
      0 ≤ (0 : ℤ) * w + 2 * ab.2 - ab.1 ∧ (0 : ℤ) * w + 2 * ab.2 - ab.1 + 1 ≤ 1096 * w) =
      (range w ×ˢ range w).filter (fun ab : ℕ × ℕ => ¬ (2 * ab.2 + 1 ≤ ab.1)) := by
    apply filter_congr
    rintro ⟨a, b⟩ hab
    simp only [mem_product, mem_range] at hab
    omega
  rw [e]
  unfold Qc
  have h' : ((filter (fun ab : ℕ × ℕ => 2 * ab.2 + 1 ≤ ab.1) (range w ×ˢ range w)).card : ℤ) +
      ((filter (fun ab : ℕ × ℕ => ¬ (2 * ab.2 + 1 ≤ ab.1)) (range w ×ˢ range w)).card : ℤ) = (w : ℤ) * w := by
    exact_mod_cast h
  linarith

theorem Npq_m1096 (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hm : 2 * (q : ℤ) - p - 1 = 1096) :
    Npq w p q = Qc w := by
  rw [Npq_eq w p q hp hq, hm]
  unfold Qc
  congr 2
  apply filter_congr
  rintro ⟨a, b⟩ hab
  simp only [mem_product, mem_range] at hab
  omega

theorem Npq_mm1 (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hm : 2 * (q : ℤ) - p - 1 = -1) :
    Npq w p q = Qc w := by
  rw [Npq_eq w p q hp hq, hm, ← Rc_eq]
  unfold Rc
  congr 2
  apply filter_congr
  rintro ⟨a, b⟩ hab
  simp only [mem_product, mem_range] at hab
  omega

theorem Npq_m1095 (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hm : 2 * (q : ℤ) - p - 1 = 1095) :
    Npq w p q = (w : ℤ) * w - Qc w := by
  rw [Npq_eq w p q hp hq, hm, ← Rc_eq]
  have h := card_filter_add_card_filter_not (s := range w ×ˢ range w)
    (fun ab : ℕ × ℕ => w + ab.1 ≤ 2 * ab.2)
  rw [card_product, card_range] at h
  have e : (range w ×ˢ range w).filter (fun ab : ℕ × ℕ =>
      0 ≤ (1095 : ℤ) * w + 2 * ab.2 - ab.1 ∧ (1095 : ℤ) * w + 2 * ab.2 - ab.1 + 1 ≤ 1096 * w) =
      (range w ×ˢ range w).filter (fun ab : ℕ × ℕ => ¬ (w + ab.1 ≤ 2 * ab.2)) := by
    apply filter_congr
    rintro ⟨a, b⟩ hab
    simp only [mem_product, mem_range] at hab
    omega
  rw [e]
  unfold Rc
  have h' : ((filter (fun ab : ℕ × ℕ => w + ab.1 ≤ 2 * ab.2) (range w ×ˢ range w)).card : ℤ) +
      ((filter (fun ab : ℕ × ℕ => ¬ (w + ab.1 ≤ 2 * ab.2)) (range w ×ˢ range w)).card : ℤ) = (w : ℤ) * w := by
    exact_mod_cast h
  linarith

theorem Npq_bound (w p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    |4 * Npq w p q - (w : ℤ) ^ 2 * (K4 1096 p q : ℤ)| ≤ 3 := by
  have hQ := Qc_eq w
  have hQ' : 4 * (Qc w : ℤ) + ((w % 2 : ℕ) : ℤ) = (w : ℤ) * w := by exact_mod_cast hQ
  have hw2 : ((w % 2 : ℕ) : ℤ) ≤ 1 := by have := Nat.mod_lt w (show 2 > 0 by norm_num); omega
  have hw0 : (0 : ℤ) ≤ ((w % 2 : ℕ) : ℤ) := Nat.cast_nonneg _
  by_cases hA : 1 ≤ 2 * (q : ℤ) - p - 1 ∧ 2 * (q : ℤ) - p - 1 ≤ 1094
  · have hK : K4 1096 p q = 4 := by unfold K4; split_ifs <;> omega
    rw [Npq_full w p q hp hq hA.1 hA.2, hK]
    have : 4 * ((w : ℤ) * w) - (w : ℤ) ^ 2 * ((4 : ℕ) : ℤ) = 0 := by push_cast; ring
    rw [this]; norm_num
  by_cases hB : 2 * (q : ℤ) - p - 1 = 0 ∨ 2 * (q : ℤ) - p - 1 = 1095
  · have hK : K4 1096 p q = 3 := by unfold K4; split_ifs <;> omega
    have hN : Npq w p q = (w : ℤ) * w - Qc w := by
      rcases hB with hB | hB
      · exact Npq_m0 w p q hp hq hB
      · exact Npq_m1095 w p q hp hq hB
    rw [hN, hK, abs_le]
    push_cast
    constructor <;> nlinarith
  by_cases hC : 2 * (q : ℤ) - p - 1 = -1 ∨ 2 * (q : ℤ) - p - 1 = 1096
  · have hK : K4 1096 p q = 1 := by unfold K4; split_ifs <;> omega
    have hN : Npq w p q = Qc w := by
      rcases hC with hC | hC
      · exact Npq_mm1 w p q hp hq hC
      · exact Npq_m1096 w p q hp hq hC
    rw [hN, hK, abs_le]
    push_cast
    constructor <;> nlinarith
  · have hK : K4 1096 p q = 0 := by unfold K4; split_ifs <;> omega
    have hN : Npq w p q = 0 := Npq_zero w p q hp hq (by omega)
    rw [hN, hK]
    simp

section GridFacts

variable (G : Grid)

theorem lo_zero (hG : G.WF) : G.lo 0 = 0 := by
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.1 hG.1
  simp [Grid.lo, hys]

theorem lo_N (hG : G.WF) : G.lo G.N = 1096 := by
  unfold Grid.lo Grid.N
  rw [List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?, hG.2.1]
  rfl

theorem pts_pos (hG : G.WF) : 0 < G.pts.length := by
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.1 hG.1
  simp [hys]

theorem lo_lt (hG : G.WF) {i j : ℕ} (hij : i < j) (hj : j ≤ G.N) : G.lo i < G.lo j := by
  have hl := pts_pos G hG
  have hjl : j < G.pts.length := by unfold Grid.N at hj; omega
  have hil : i < G.pts.length := by omega
  unfold Grid.lo
  rw [List.getD_eq_getElem _ _ hil, List.getD_eq_getElem _ _ hjl]
  exact List.pairwise_iff_getElem.1 hG.2.2.1 i j hil hjl hij

theorem lo_mono (hG : G.WF) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ G.N) : G.lo i ≤ G.lo j := by
  rcases Nat.eq_or_lt_of_le hij with rfl | h
  · exact le_rfl
  · exact (lo_lt G hG h hj).le

theorem hi_eq (i : ℕ) : G.hi i = G.lo (i + 1) := rfl

theorem len_pos (hG : G.WF) {i : ℕ} (hi : i < G.N) : 0 < G.len i := by
  have := lo_lt G hG (show i < i + 1 by omega) hi
  unfold Grid.len
  rw [hi_eq]
  omega

theorem cell_card (i w : ℕ) : (G.cell w i).card = G.len i * w := by
  unfold Grid.cell Grid.len
  rw [Nat.card_Ioc, Nat.sub_mul]

theorem sum_cells_aux {M : Type*} [AddCommMonoid M] (hG : G.WF) (w : ℕ) (f : ℕ → M) (m : ℕ) (hm : m ≤ G.N) :
    ∑ i ∈ range m, ∑ x ∈ G.cell w i, f x = ∑ x ∈ Ioc 0 (G.lo m * w), f x := by
  induction m with
  | zero => simp [lo_zero G hG]
  | succ m ih =>
    rw [sum_range_succ, ih (by omega)]
    unfold Grid.cell
    rw [hi_eq]
    exact sum_Ioc_consecutive f (Nat.zero_le _) (Nat.mul_le_mul_right w (lo_mono G hG (Nat.le_succ m) hm))

theorem sum_cells {M : Type*} [AddCommMonoid M] (hG : G.WF) (w : ℕ) (f : ℕ → M) :
    ∑ x ∈ Icc 1 (nn w), f x = ∑ i ∈ range G.N, ∑ x ∈ G.cell w i, f x := by
  rw [sum_cells_aux G hG w f G.N le_rfl, lo_N G hG]
  have : Icc 1 (nn w) = Ioc 0 (1096 * w) := by
    ext x; simp only [mem_Icc, mem_Ioc, nn]; omega
  rw [this]

theorem sum_len (hG : G.WF) : ∑ i ∈ range G.N, G.len i = 1096 := by
  have h := sum_cells G hG 1 (fun _ => (1 : ℕ))
  simp only [sum_const, smul_eq_mul, mul_one, Nat.card_Icc] at h
  have h2 : ∀ i ∈ range G.N, (G.cell 1 i).card = G.len i := by
    intro i _
    rw [cell_card G i 1, mul_one]
  rw [sum_congr rfl h2] at h
  simpa [nn] using h.symm

theorem sg_pm (c : ℕ → Bool) (x : ℕ) : sg c x = 1 ∨ sg c x = -1 := by
  unfold sg; split_ifs <;> simp

theorem sgn_pm (i : ℕ) : G.sgn i = 1 ∨ G.sgn i = -1 := sg_pm _ _

theorem sstar_cell (hG : G.WF) (w : ℕ) (hw : 1 ≤ w) {i : ℕ} (hi : i < G.N) {x : ℕ} (hx : x ∈ G.cell w i) :
    sstar w x = G.sgn i := by
  unfold Grid.cell at hx
  rw [mem_Ioc, hi_eq] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hlo : G.lo i ≤ (x - 1) / w := by
    rw [Nat.le_div_iff_mul_le (by omega)]; omega
  have hhi : (x - 1) / w < G.lo (i + 1) := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  have hc := hG.2.2.2.2.2 i hi ((x - 1) / w) (mem_Ico.2 ⟨hlo, hhi⟩)
  have hck : ck (2 * w) x = c1 (G.lo i / 2 + 1) := by
    rw [← hc]
    unfold ck
    have e1 : x + (2 * w - 1) = (x - 1) + 2 * w := by omega
    rw [e1, Nat.add_div_right _ (by omega : 0 < 2 * w), Nat.div_div_eq_div_mul, mul_comm w 2]
  unfold sstar Grid.sgn sg
  rw [hck]

theorem Qd_cells (hG : G.WF) (w : ℕ) (hw : 1 ≤ w) (σ : ℕ → ℤ) :
    Qd (nn w) (fun x => sstar w x * σ x) =
      ∑ i ∈ range G.N, ∑ j ∈ range G.N, G.sgn i * G.sgn j *
        ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y * σ x * σ y := by
  unfold Qd
  rw [sum_cells G hG w]
  have step : ∀ i ∈ range G.N,
      ∑ x ∈ G.cell w i, ∑ y ∈ Icc 1 (nn w), rdI (nn w) x y * (sstar w x * σ x) * (sstar w y * σ y)
      = ∑ j ∈ range G.N, G.sgn i * G.sgn j *
          ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y * σ x * σ y := by
    intro i hi
    rw [mem_range] at hi
    calc ∑ x ∈ G.cell w i, ∑ y ∈ Icc 1 (nn w), rdI (nn w) x y * (sstar w x * σ x) * (sstar w y * σ y)
        = ∑ x ∈ G.cell w i, ∑ j ∈ range G.N, ∑ y ∈ G.cell w j,
            rdI (nn w) x y * (sstar w x * σ x) * (sstar w y * σ y) := by
          apply sum_congr rfl; intro x _; exact sum_cells G hG w _
      _ = ∑ x ∈ G.cell w i, ∑ j ∈ range G.N, ∑ y ∈ G.cell w j,
            G.sgn i * G.sgn j * (rdI (nn w) x y * σ x * σ y) := by
          apply sum_congr rfl; intro x hx
          apply sum_congr rfl; intro j hj
          rw [mem_range] at hj
          apply sum_congr rfl; intro y hy
          rw [sstar_cell G hG w hw hi hx, sstar_cell G hG w hw hj hy]; ring
      _ = ∑ j ∈ range G.N, ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j,
            G.sgn i * G.sgn j * (rdI (nn w) x y * σ x * σ y) := sum_comm
      _ = _ := by
          apply sum_congr rfl; intro j _
          simp only [mul_sum]
  rw [sum_congr rfl step]

end GridFacts

theorem rdI_01 (n x y : ℕ) : rdI n x y = 0 ∨ rdI n x y = 1 := by
  unfold rdI; split_ifs <;> simp

theorem ind_aux (r a b : ℤ) (hr : r = 0 ∨ r = 1) (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    0 ≤ r * a * b ∧ r * a * b ≤ a * b ∧ r * a * b ≤ r ∧ a * b - 1 + r ≤ r * a * b := by
  rcases hr with rfl | rfl <;> rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem pair_int (A B : Finset ℕ) (σ : ℕ → ℤ) (hσ : IsInd σ) (n : ℕ) :
    0 ≤ ∑ x ∈ A, ∑ y ∈ B, rdI n x y * σ x * σ y ∧
    ∑ x ∈ A, ∑ y ∈ B, rdI n x y * σ x * σ y ≤ (∑ x ∈ A, σ x) * (∑ y ∈ B, σ y) ∧
    ∑ x ∈ A, ∑ y ∈ B, rdI n x y * σ x * σ y ≤ ∑ x ∈ A, ∑ y ∈ B, rdI n x y ∧
    (∑ x ∈ A, σ x) * (∑ y ∈ B, σ y) - (A.card : ℤ) * B.card + ∑ x ∈ A, ∑ y ∈ B, rdI n x y
      ≤ ∑ x ∈ A, ∑ y ∈ B, rdI n x y * σ x * σ y := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply sum_nonneg; intro x _; apply sum_nonneg; intro y _
    exact (ind_aux _ _ _ (rdI_01 n x y) (hσ x) (hσ y)).1
  · rw [sum_mul_sum]
    apply sum_le_sum; intro x _; apply sum_le_sum; intro y _
    exact (ind_aux _ _ _ (rdI_01 n x y) (hσ x) (hσ y)).2.1
  · apply sum_le_sum; intro x _; apply sum_le_sum; intro y _
    exact (ind_aux _ _ _ (rdI_01 n x y) (hσ x) (hσ y)).2.2.1
  · have h1 : ∑ x ∈ A, ∑ y ∈ B, (σ x * σ y - 1 + rdI n x y) ≤ ∑ x ∈ A, ∑ y ∈ B, rdI n x y * σ x * σ y := by
      apply sum_le_sum; intro x _; apply sum_le_sum; intro y _
      exact (ind_aux _ _ _ (rdI_01 n x y) (hσ x) (hσ y)).2.2.2
    have h2 : ∑ x ∈ A, ∑ y ∈ B, (σ x * σ y - 1 + rdI n x y) =
        (∑ x ∈ A, σ x) * (∑ y ∈ B, σ y) - (A.card : ℤ) * B.card + ∑ x ∈ A, ∑ y ∈ B, rdI n x y := by
      simp only [sum_add_distrib, sum_sub_distrib, sum_mul_sum, sum_const]
      simp
    linarith

theorem sum_cell_units {M : Type*} [AddCommMonoid M] (f : ℕ → M) (lo hi w : ℕ) (h : lo ≤ hi) :
    ∑ x ∈ Ioc (lo * w) (hi * w), f x = ∑ p ∈ Ioc lo hi, ∑ x ∈ Ioc ((p - 1) * w) (p * w), f x := by
  induction hi, h using Nat.le_induction with
  | base => simp
  | succ hi h ih =>
    rw [sum_Ioc_succ_top h, ← ih,
      ← sum_Ioc_consecutive f (Nat.mul_le_mul_right w h) (Nat.mul_le_mul_right w (Nat.le_succ hi))]
    simp

section CellPair

variable (G : Grid)

theorem Nc_unit (hG : G.WF) (w : ℕ) {i j : ℕ} (hi : i < G.N) (hj : j < G.N) :
    ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y =
      ∑ p ∈ Ioc (G.lo i) (G.hi i), ∑ q ∈ Ioc (G.lo j) (G.hi j), Npq w p q := by
  have hi' : G.lo i ≤ G.hi i := by
    have := len_pos G hG hi; unfold Grid.len at this; omega
  have hj' : G.lo j ≤ G.hi j := by
    have := len_pos G hG hj; unfold Grid.len at this; omega
  unfold Grid.cell
  rw [sum_cell_units _ _ _ _ hi']
  apply sum_congr rfl
  intro p _
  have : ∀ x ∈ Ioc ((p - 1) * w) (p * w), ∑ y ∈ Ioc (G.lo j * w) (G.hi j * w), rdI (nn w) x y =
      ∑ q ∈ Ioc (G.lo j) (G.hi j), ∑ y ∈ Ioc ((q - 1) * w) (q * w), rdI (nn w) x y := by
    intro x _
    exact sum_cell_units _ _ _ _ hj'
  rw [sum_congr rfl this, sum_comm]
  rfl

theorem Nc_bound (hG : G.WF) (w : ℕ) {i j : ℕ} (hi : i < G.N) (hj : j < G.N) :
    |4 * (∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y) - (w : ℤ) ^ 2 * (G.A4 i j : ℤ)|
      ≤ 3 * ((G.len i : ℤ) * G.len j) := by
  have e : 4 * (∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y) - (w : ℤ) ^ 2 * (G.A4 i j : ℤ) =
      ∑ p ∈ Ioc (G.lo i) (G.hi i), ∑ q ∈ Ioc (G.lo j) (G.hi j),
        (4 * Npq w p q - (w : ℤ) ^ 2 * (K4 1096 p q : ℤ)) := by
    rw [Nc_unit G hG w hi hj]
    unfold Grid.A4
    push_cast
    simp only [mul_sum, ← sum_sub_distrib]
  rw [e]
  calc |∑ p ∈ Ioc (G.lo i) (G.hi i), ∑ q ∈ Ioc (G.lo j) (G.hi j),
          (4 * Npq w p q - (w : ℤ) ^ 2 * (K4 1096 p q : ℤ))|
      ≤ ∑ p ∈ Ioc (G.lo i) (G.hi i), |∑ q ∈ Ioc (G.lo j) (G.hi j),
          (4 * Npq w p q - (w : ℤ) ^ 2 * (K4 1096 p q : ℤ))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Ioc (G.lo i) (G.hi i), ∑ q ∈ Ioc (G.lo j) (G.hi j),
          |(4 * Npq w p q - (w : ℤ) ^ 2 * (K4 1096 p q : ℤ))| := by
        apply sum_le_sum; intro p _; exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Ioc (G.lo i) (G.hi i), ∑ q ∈ Ioc (G.lo j) (G.hi j), (3 : ℤ) := by
        apply sum_le_sum; intro p hp
        apply sum_le_sum; intro q hq
        rw [mem_Ioc] at hp hq
        exact Npq_bound w p q (by omega) (by omega)
    _ = 3 * ((G.len i : ℤ) * G.len j) := by
        simp only [sum_const, Nat.card_Ioc]
        unfold Grid.len
        simp
        ring

end CellPair

section Final

variable (G : Grid)

theorem pair_term (hG : G.WF) (w : ℕ) (hw : 1 ≤ w) (σ : ℕ → ℤ) (hσ : IsInd σ) {i j : ℕ}
    (hi : i < G.N) (hj : j < G.N) :
    (nn w : ℝ) ^ 2 * G.pterm i j (G.yv w σ i) (G.yv w σ j) ≤
      ((G.sgn i * G.sgn j * ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y * σ x * σ y : ℤ) : ℝ)
        + (3 / 4 : ℝ) * ((G.len i : ℝ) * G.len j) := by
  obtain ⟨hTa, hTb, hTc, hTd⟩ := pair_int (G.cell w i) (G.cell w j) σ hσ (nn w)
  have hNb := Nc_bound G hG w hi hj
  rw [cell_card, cell_card] at hTd
  have hLi : (0 : ℝ) < G.len i := by exact_mod_cast len_pos G hG hi
  have hLj : (0 : ℝ) < G.len j := by exact_mod_cast len_pos G hG hj
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hyi : G.yv w σ i = ((∑ x ∈ G.cell w i, σ x : ℤ) : ℝ) / ((G.len i * w : ℕ) : ℝ) := rfl
  have hyj : G.yv w σ j = ((∑ y ∈ G.cell w j, σ y : ℤ) : ℝ) / ((G.len j * w : ℕ) : ℝ) := rfl
  have hnn : (nn w : ℝ) = 1096 * w := by simp [nn]
  have hwi : ((G.wt i : ℚ) : ℝ) = (G.len i : ℝ) / 1096 := by simp [Grid.wt]
  have hwj : ((G.wt j : ℚ) : ℝ) = (G.len j : ℝ) / 1096 := by simp [Grid.wt]
  unfold Grid.pterm
  dsimp only
  rw [hyi, hyj]
  generalize ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y * σ x * σ y = T at *
  generalize ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y = Nc at *
  generalize ∑ x ∈ G.cell w i, σ x = ki at *
  generalize ∑ y ∈ G.cell w j, σ y = kj at *
  have hU : (nn w : ℝ) ^ 2 * (((G.wt i : ℚ) : ℝ) * ((G.wt j : ℚ) : ℝ) *
      ((ki : ℝ) / ((G.len i * w : ℕ) : ℝ)) * ((kj : ℝ) / ((G.len j * w : ℕ) : ℝ))) = (ki : ℝ) * kj := by
    rw [hnn, hwi, hwj]; push_cast; field_simp
  have hV : (nn w : ℝ) ^ 2 * ((G.A4 i j : ℝ) / (4 * 1096 ^ 2)) = (w : ℝ) ^ 2 * (G.A4 i j : ℝ) / 4 := by
    rw [hnn]; field_simp
  have hZ : (nn w : ℝ) ^ 2 * (((G.wt i : ℚ) : ℝ) * ((G.wt j : ℚ) : ℝ)) =
      (w : ℝ) ^ 2 * ((G.len i : ℝ) * G.len j) := by
    rw [hnn, hwi, hwj]; field_simp
  have hn0 : (0 : ℝ) ≤ (nn w : ℝ) ^ 2 := by positivity
  have hTa' : (0 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hTa
  have hTb' : (T : ℝ) ≤ (ki : ℝ) * kj := by exact_mod_cast hTb
  have hTc' : (T : ℝ) ≤ (Nc : ℝ) := by exact_mod_cast hTc
  have hTd' : (ki : ℝ) * kj - (G.len i : ℝ) * w * ((G.len j : ℝ) * w) + Nc ≤ T := by
    exact_mod_cast hTd
  have hNb' := abs_le.1 hNb
  have hNb1 : 4 * (Nc : ℝ) - (w : ℝ) ^ 2 * (G.A4 i j : ℝ) ≤ 3 * ((G.len i : ℝ) * G.len j) := by
    exact_mod_cast hNb'.2
  have hNb2 : -(3 * ((G.len i : ℝ) * G.len j)) ≤ 4 * (Nc : ℝ) - (w : ℝ) ^ 2 * (G.A4 i j : ℝ) := by
    exact_mod_cast hNb'.1
  have hLL : (0 : ℝ) ≤ (G.len i : ℝ) * G.len j := by positivity
  split_ifs with hs
  · rw [hs, one_mul, mul_max_of_nonneg _ _ hn0]
    apply max_le
    · linarith
    · have : (nn w : ℝ) ^ 2 * (((G.wt i : ℚ) : ℝ) * ((G.wt j : ℚ) : ℝ) *
          ((ki : ℝ) / ((G.len i * w : ℕ) : ℝ)) * ((kj : ℝ) / ((G.len j * w : ℕ) : ℝ)) -
          (((G.wt i : ℚ) : ℝ) * ((G.wt j : ℚ) : ℝ) - (G.A4 i j : ℝ) / (4 * 1096 ^ 2))) =
          (ki : ℝ) * kj - (w : ℝ) ^ 2 * ((G.len i : ℝ) * G.len j) + (w : ℝ) ^ 2 * (G.A4 i j : ℝ) / 4 := by
        linear_combination hU - hZ + hV
      rw [this]
      linarith
  · have hs' : G.sgn i * G.sgn j = -1 := by
      have key : G.sgn i * G.sgn j = 1 ∨ G.sgn i * G.sgn j = -1 := by
        rcases sgn_pm G i with h | h <;> rcases sgn_pm G j with h' | h' <;> norm_num [h, h']
      exact key.resolve_left hs
    rw [hs', mul_max_of_nonneg _ _ hn0]
    apply max_le
    · have : (nn w : ℝ) ^ 2 * (-((G.A4 i j : ℝ) / (4 * 1096 ^ 2))) = -((w : ℝ) ^ 2 * (G.A4 i j : ℝ) / 4) := by
        linear_combination (-1 : ℝ) * hV
      rw [this]; push_cast; linarith
    · have : (nn w : ℝ) ^ 2 * (-(((G.wt i : ℚ) : ℝ) * ((G.wt j : ℚ) : ℝ) *
          ((ki : ℝ) / ((G.len i * w : ℕ) : ℝ)) * ((kj : ℝ) / ((G.len j * w : ℕ) : ℝ)))) = -((ki : ℝ) * kj) := by
        linear_combination (-1 : ℝ) * hU
      rw [this]; push_cast; linarith

end Final

theorem G8_WF : G8.WF := by decide +kernel

end Pair

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2 Pair

theorem pairOK_of_WF (G : Grid) (hG : G.WF) : PairOK G := by
  refine ⟨3 * 1096 ^ 2 / 4, fun w hw σ hσ => ?_⟩
  have hL : ∑ i ∈ range G.N, (G.len i : ℝ) = 1096 := by exact_mod_cast sum_len G hG
  have hE : ∑ i ∈ range G.N, ∑ j ∈ range G.N, (3 / 4 : ℝ) * ((G.len i : ℝ) * G.len j) = 3 * 1096 ^ 2 / 4 := by
    have : ∑ i ∈ range G.N, ∑ j ∈ range G.N, (3 / 4 : ℝ) * ((G.len i : ℝ) * G.len j) =
        (3 / 4 : ℝ) * ((∑ i ∈ range G.N, (G.len i : ℝ)) * ∑ j ∈ range G.N, (G.len j : ℝ)) := by
      rw [sum_mul_sum, mul_sum]
      apply sum_congr rfl; intro i _
      rw [mul_sum]
    rw [this, hL]; ring
  have hsum : (nn w : ℝ) ^ 2 * ∑ i ∈ range G.N, ∑ j ∈ range G.N, G.pterm i j (G.yv w σ i) (G.yv w σ j) ≤
      ∑ i ∈ range G.N, ∑ j ∈ range G.N,
        (((G.sgn i * G.sgn j * ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y * σ x * σ y : ℤ)) : ℝ) +
      ∑ i ∈ range G.N, ∑ j ∈ range G.N, (3 / 4 : ℝ) * ((G.len i : ℝ) * G.len j) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum; intro i hi
    rw [mem_range] at hi
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum; intro j hj
    rw [mem_range] at hj
    exact pair_term G hG w hw σ hσ hi hj
  have hQ : ((Qd (nn w) (fun x => sstar w x * σ x) : ℤ) : ℝ) =
      ∑ i ∈ range G.N, ∑ j ∈ range G.N,
        (((G.sgn i * G.sgn j * ∑ x ∈ G.cell w i, ∑ y ∈ G.cell w j, rdI (nn w) x y * σ x * σ y : ℤ)) : ℝ) := by
    rw [Qd_cells G hG w hw σ]
    simp only [Int.cast_sum]
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  rw [hQ]
  rw [hE] at hsum
  nlinarith

theorem pairOK8 : PairOK G8 := pairOK_of_WF G8 Pair.G8_WF

end Erdos1186Ex
end

section
namespace Erdos1186Ex

open Finset Erdos1186Day Erdos1186Night2

def Usg (k : ℕ) : ℤ := sg c1 (k / 2 + 1)

def segN (a b k : ℕ) : ℕ := (bif Nat.ble k b then k else b) - (bif Nat.ble k a then k else a)

def FU (k : ℕ) : ℤ :=
  (segN 0 56 k : ℤ) - segN 56 68 k + segN 68 124 k - segN 124 198 k + segN 198 316 k - segN 316 548 k
    + segN 548 780 k - segN 780 898 k + segN 898 972 k - segN 972 1028 k + segN 1028 1040 k - segN 1040 1096 k

theorem FU_zero : FU 0 = 0 := by decide +kernel

def chkFU (a b : ℕ) : Bool := (List.range' a (b - a)).all (fun k => decide (FU (k + 1) = FU k + Usg k))

theorem chkFU_a : chkFU 0 366 = true := by decide +kernel
theorem chkFU_b : chkFU 366 731 = true := by decide +kernel
theorem chkFU_c : chkFU 731 1096 = true := by decide +kernel

theorem FU_succ : ∀ k < 1096, FU (k + 1) = FU k + Usg k := by
  intro k hk
  have h : ∀ a b : ℕ, chkFU a b = true → a ≤ k → k < b → FU (k + 1) = FU k + Usg k := by
    intro a b hc hak hkb
    unfold chkFU at hc
    rw [List.all_eq_true] at hc
    have := hc k (by rw [List.mem_range']; exact ⟨k - a, by omega, by omega⟩)
    exact of_decide_eq_true this
  by_cases h1 : k < 366
  · exact h 0 366 chkFU_a (Nat.zero_le _) h1
  · by_cases h2 : k < 731
    · exact h 366 731 chkFU_b (by omega) h2
    · exact h 731 1096 chkFU_c (by omega) hk

theorem FU_1096 : FU 1096 = 0 := by decide +kernel

lemma Usg_pm (k : ℕ) : Usg k = 1 ∨ Usg k = -1 := by
  unfold Usg sg; split_ifs <;> simp

lemma Usg_pair (k : ℕ) : Usg (2 * k + 1) = Usg (2 * k) := by
  unfold Usg; congr 2; omega

end Erdos1186Ex
end

section
namespace Erdos1186Ex

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

lemma sstar_eq (w y : ℕ) (hw : 1 ≤ w) (hy : 1 ≤ y) : sstar w y = Usg ((y - 1) / w) := by
  unfold sstar Usg ck sg
  have h1 : (y + (2 * w - 1)) / (2 * w) = (y - 1) / w / 2 + 1 := by
    have e : y + (2 * w - 1) = (y - 1) + 2 * w := by omega
    rw [e, Nat.add_div_right _ (by omega : 0 < 2 * w), Nat.div_div_eq_div_mul, mul_comm w 2]
  show (if c1 ((y + (2 * w - 1)) / (2 * w)) = true then (1 : ℤ) else -1) = _
  rw [h1]

lemma pre_sstar (w : ℕ) (hw : 1 ≤ w) :
    ∀ m, m ≤ 1096 * w → pre (sstar w) m = w * FU (m / w) + ((m % w : ℕ) : ℤ) * Usg (m / w) := by
  intro m
  induction m with
  | zero => intro _; simp [pre_zero, FU_zero]
  | succ m ih =>
    intro hm
    have hm' : m ≤ 1096 * w := by omega
    rw [pre_succ, ih hm', sstar_eq w (m + 1) hw (by omega)]
    simp only [Nat.add_sub_cancel]
    have hqm : m = w * (m / w) + m % w := (Nat.div_add_mod m w).symm
    have hr : m % w < w := Nat.mod_lt _ (by omega)
    have hq : m / w < 1096 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    by_cases hlt : m % w + 1 < w
    · have h1 : (m + 1) / w = m / w ∧ (m + 1) % w = m % w + 1 :=
        (Nat.div_mod_unique (by omega)).2 ⟨by omega, hlt⟩
      rw [h1.1, h1.2]; push_cast; ring
    · have hw1 : m % w + 1 = w := by omega
      have h1 : (m + 1) / w = m / w + 1 ∧ (m + 1) % w = 0 :=
        (Nat.div_mod_unique (by omega)).2 ⟨by rw [Nat.mul_add]; omega, by omega⟩
      rw [h1.1, h1.2, FU_succ _ hq]
      have : ((m % w : ℕ) : ℤ) = (w : ℤ) - 1 := by omega
      rw [this]; push_cast; ring

lemma pre_lin (w : ℕ) (hw : 1 ≤ w) (k r : ℕ) (hk : k ≤ 1095) (hr : r ≤ w) :
    pre (sstar w) (k * w + r) = w * FU k + r * Usg k := by
  rcases Nat.lt_or_ge r w with h | h
  · have h1 : (k * w + r) / w = k ∧ (k * w + r) % w = r :=
      (Nat.div_mod_unique (by omega)).2 ⟨by rw [mul_comm]; omega, h⟩
    rw [pre_sstar w hw _ (by nlinarith), h1.1, h1.2]
  · have hrw : r = w := le_antisymm hr h
    subst hrw
    have h1 : (k * r + r) / r = k + 1 ∧ (k * r + r) % r = 0 :=
      (Nat.div_mod_unique (by omega)).2 ⟨by rw [mul_comm]; ring, by omega⟩
    rw [pre_sstar r hw _ (by nlinarith), h1.1, h1.2, FU_succ k (by omega)]
    push_cast; ring

lemma pre_lin2 (w : ℕ) (hw : 1 ≤ w) (k r : ℕ) (hk : k ≤ 547) (hr : r ≤ 2 * w) :
    pre (sstar w) (2 * k * w + r) = w * FU (2 * k) + r * Usg (2 * k) := by
  rcases le_or_gt r w with h | h
  · exact pre_lin w hw (2 * k) r (by omega) h
  · have e : 2 * k * w + r = (2 * k + 1) * w + (r - w) := by
      have : r = w + (r - w) := by omega
      nlinarith
    rw [e, pre_lin w hw (2 * k + 1) (r - w) (by omega) (by omega), Usg_pair, FU_succ (2 * k) (by omega)]
    have : ((r - w : ℕ) : ℤ) = (r : ℤ) - w := by omega
    rw [this]; ring

lemma rowsum (w x : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ nn w) :
    ∑ y ∈ Icc 1 (nn w), rdI (nn w) x y * sstar w y
      = pre (sstar w) ((x + nn w) / 2) - pre (sstar w) (x / 2) := by
  have h1 : ∀ y ∈ Icc 1 (nn w), rdI (nn w) x y * sstar w y
      = if (x / 2 < y ∧ y ≤ (x + nn w) / 2) then sstar w y else 0 := by
    intro y _
    unfold rdI
    have hiff : (1 ≤ 2 * (y : ℤ) - x ∧ 2 * (y : ℤ) - x ≤ (nn w : ℤ)) ↔ (x / 2 < y ∧ y ≤ (x + nn w) / 2) := by
      omega
    by_cases h : x / 2 < y ∧ y ≤ (x + nn w) / 2
    · rw [if_pos (hiff.2 h), if_pos h]; ring
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]; ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  have h2 : (Icc 1 (nn w)).filter (fun y => x / 2 < y ∧ y ≤ (x + nn w) / 2)
      = Ioc (x / 2) ((x + nn w) / 2) := by
    ext y; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h2, sum_Ioc_eq _ (by omega)]

lemma colsum (w x : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ nn w) :
    ∑ e ∈ Icc 1 (nn w), rdI (nn w) e x * sstar w e
      = pre (sstar w) (min (nn w) (2 * x - 1)) - pre (sstar w) (2 * x - nn w - 1) := by
  have h1 : ∀ e ∈ Icc 1 (nn w), rdI (nn w) e x * sstar w e
      = if (2 * x - nn w - 1 < e ∧ e ≤ min (nn w) (2 * x - 1)) then sstar w e else 0 := by
    intro e he
    unfold rdI
    have hiff : (1 ≤ 2 * (x : ℤ) - e ∧ 2 * (x : ℤ) - e ≤ (nn w : ℤ))
        ↔ (2 * x - nn w - 1 < e ∧ e ≤ min (nn w) (2 * x - 1)) := by
      rw [Finset.mem_Icc] at he
      omega
    by_cases h : 2 * x - nn w - 1 < e ∧ e ≤ min (nn w) (2 * x - 1)
    · rw [if_pos (hiff.2 h), if_pos h]; ring
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]; ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
  have h2 : (Icc 1 (nn w)).filter (fun e => 2 * x - nn w - 1 < e ∧ e ≤ min (nn w) (2 * x - 1))
      = Ioc (2 * x - nn w - 1) (min (nn w) (2 * x - 1)) := by
    ext y; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h2, sum_Ioc_eq _ (by omega)]

theorem H2_formula (w : ℕ) (hw : 1 ≤ w) (p' j : ℕ) (hp : p' ≤ 1095) (hj1 : 1 ≤ j) (hj2 : j ≤ w) :
    H2 w (p' * w + j)
      = - Usg p' * ((w : ℤ) * (FU (p' / 2 + 548) - FU (p' / 2))
          + ((((p' % 2) * w + j) / 2 : ℕ) : ℤ) * (Usg (p' / 2 + 548) - Usg (p' / 2))
          + (if p' < 548 then ((w : ℤ) * FU (2 * p') + (2 * (j : ℤ) - 1) * Usg (2 * p'))
             else -((w : ℤ) * FU (2 * (p' - 548)) + (2 * (j : ℤ) - 1) * Usg (2 * (p' - 548))))) := by
  have hnn : nn w = 1096 * w := rfl
  have hx1 : 1 ≤ p' * w + j := by omega
  have hpw : p' * w ≤ 1095 * w := Nat.mul_le_mul_right _ hp
  have hx2 : p' * w + j ≤ nn w := by rw [hnn]; nlinarith
  
  have hs : sstar w (p' * w + j) = Usg p' := by
    rw [sstar_eq w _ hw hx1]
    congr 1
    have : p' * w + j - 1 = p' * w + (j - 1) := by omega
    rw [this]
    exact Nat.div_eq_of_lt_le (by omega) (by rw [Nat.succ_mul]; omega)
  unfold H2
  rw [rowsum w _ hx1 hx2, colsum w _ hx1 hx2, hs]
  
  obtain ⟨k2, e, he, rfl⟩ : ∃ k2 e, e ≤ 1 ∧ p' = 2 * k2 + e := ⟨p' / 2, p' % 2, by omega, by omega⟩
  have hk2 : k2 ≤ 547 := by omega
  have hk2' : (2 * k2 + e) / 2 = k2 := by omega
  have he2 : (2 * k2 + e) % 2 = e := by omega
  rw [hk2', he2]
  set r := (e * w + j) / 2 with hr
  have hrw : r ≤ w := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · subst h0; omega
    · have : e = 1 := by omega
      subst this; omega
  have ea1 : ((2 * k2 + e) * w + j + nn w) / 2 = (k2 + 548) * w + r := by
    have : (2 * k2 + e) * w + j + nn w = 2 * ((k2 + 548) * w) + (e * w + j) := by rw [hnn]; ring
    rw [this]; omega
  have ea2 : ((2 * k2 + e) * w + j) / 2 = k2 * w + r := by
    have : (2 * k2 + e) * w + j = 2 * (k2 * w) + (e * w + j) := by ring
    rw [this]; omega
  rw [ea1, ea2, pre_lin w hw (k2 + 548) r (by omega) hrw, pre_lin w hw k2 r (by omega) hrw]
  by_cases hlt : 2 * k2 + e < 548
  · rw [if_pos hlt]
    have hx : 2 * ((2 * k2 + e) * w + j) ≤ nn w := by
      have : (2 * k2 + e) * w ≤ 547 * w := Nat.mul_le_mul_right _ (by omega)
      rw [hnn]; nlinarith
    have e2 : 2 * (2 * k2 + e) * w = 2 * ((2 * k2 + e) * w) := by ring
    have ea3 : min (nn w) (2 * ((2 * k2 + e) * w + j) - 1) = 2 * (2 * k2 + e) * w + (2 * j - 1) := by
      rw [e2]
      have h : 2 * ((2 * k2 + e) * w + j) - 1 = 2 * ((2 * k2 + e) * w) + (2 * j - 1) := by omega
      rw [h]; exact min_eq_right (by omega)
    have ea4 : 2 * ((2 * k2 + e) * w + j) - nn w - 1 = 0 := by omega
    rw [ea3, ea4, pre_zero, pre_lin2 w hw (2 * k2 + e) (2 * j - 1) (by omega) (by omega)]
    have : ((2 * j - 1 : ℕ) : ℤ) = 2 * (j : ℤ) - 1 := by omega
    rw [this]; ring
  · rw [if_neg hlt]
    obtain ⟨q, hq⟩ : ∃ q, 2 * k2 + e = 548 + q := ⟨2 * k2 + e - 548, by omega⟩
    have hq547 : q ≤ 547 := by omega
    have hx' : (2 * k2 + e) * w + j = 548 * w + (q * w + j) := by rw [hq]; ring
    have ea3 : min (nn w) (2 * ((2 * k2 + e) * w + j) - 1) = nn w := by
      apply min_eq_left; rw [hnn, hx']; omega
    have ea4 : 2 * ((2 * k2 + e) * w + j) - nn w - 1 = 2 * q * w + (2 * j - 1) := by
      rw [hx', hnn]
      have : 2 * (548 * w + (q * w + j)) = 1096 * w + 2 * q * w + 2 * j := by ring
      omega
    have hpre : pre (sstar w) (nn w) = 0 := by
      rw [hnn, pre_sstar w hw _ le_rfl, Nat.mul_div_cancel _ (by omega : 0 < w), Nat.mul_mod_left]
      simp [FU_1096]
    rw [ea3, ea4, hpre, pre_lin2 w hw q (2 * j - 1) hq547 (by omega)]
    have : ((2 * j - 1 : ℕ) : ℤ) = 2 * (j : ℤ) - 1 := by omega
    rw [this, show 2 * k2 + e - 548 = q by omega]; ring

def Dd (p' : ℕ) : ℤ := (Usg (p' / 2 + 548) - Usg (p' / 2)) / 2
def Qa (p' : ℕ) : ℤ := if p' < 548 then FU (2 * p') else -FU (2 * (p' - 548))
def Qb (p' : ℕ) : ℤ := if p' < 548 then Usg (2 * p') else -Usg (2 * (p' - 548))

def alphaF (p' : ℕ) : ℤ :=
  - Usg p' * (FU (p' / 2 + 548) - FU (p' / 2) + ((p' % 2 : ℕ) : ℤ) * Dd p' + Qa p')

def betaF (p' : ℕ) : ℤ := - Usg p' * (Dd p' + 2 * Qb p')

lemma Dd_two (p' : ℕ) : Usg (p' / 2 + 548) - Usg (p' / 2) = 2 * Dd p' := by
  unfold Dd
  rcases Usg_pm (p' / 2 + 548) with h | h <;> rcases Usg_pm (p' / 2) with h' | h' <;> rw [h, h'] <;> norm_num

lemma Dd_bd (p' : ℕ) : -1 ≤ Dd p' ∧ Dd p' ≤ 1 := by
  have := Dd_two p'
  rcases Usg_pm (p' / 2 + 548) with h | h <;> rcases Usg_pm (p' / 2) with h' | h' <;> constructor <;> omega

lemma Qb_pm (p' : ℕ) : Qb p' = 1 ∨ Qb p' = -1 := by
  unfold Qb; split_ifs
  · exact Usg_pm _
  · rcases Usg_pm (2 * (p' - 548)) with h | h <;> simp [h]

theorem H2_lin (w : ℕ) (hw : 1 ≤ w) (p' j : ℕ) (hp : p' ≤ 1095) (hj1 : 1 ≤ j) (hj2 : j ≤ w) :
    |(H2 w (p' * w + j) : ℤ) - (alphaF p' * w + betaF p' * j)| ≤ 2 := by
  rw [H2_formula w hw p' j hp hj1 hj2]
  have hQ : (if p' < 548 then ((w : ℤ) * FU (2 * p') + (2 * (j : ℤ) - 1) * Usg (2 * p'))
             else -((w : ℤ) * FU (2 * (p' - 548)) + (2 * (j : ℤ) - 1) * Usg (2 * (p' - 548))))
      = (w : ℤ) * Qa p' + (2 * (j : ℤ) - 1) * Qb p' := by
    unfold Qa Qb; split_ifs <;> ring
  rw [hQ]
  have hr2 : 2 * ((((p' % 2) * w + j) / 2 : ℕ) : ℤ) + ((((p' % 2) * w + j) % 2 : ℕ) : ℤ)
      = ((p' % 2 : ℕ) : ℤ) * w + j := by
    have hX : ∀ X : ℕ, 2 * ((X / 2 : ℕ) : ℤ) + ((X % 2 : ℕ) : ℤ) = (X : ℤ) := fun X => by omega
    have h := hX ((p' % 2) * w + j)
    rw [Nat.cast_add, Nat.cast_mul] at h
    exact h
  have hD := Dd_two p'
  have key : -Usg p' * ((w : ℤ) * (FU (p' / 2 + 548) - FU (p' / 2))
        + ((((p' % 2) * w + j) / 2 : ℕ) : ℤ) * (Usg (p' / 2 + 548) - Usg (p' / 2))
        + ((w : ℤ) * Qa p' + (2 * (j : ℤ) - 1) * Qb p'))
      - (alphaF p' * w + betaF p' * j)
      = Usg p' * ((((p' % 2) * w + j) % 2 : ℕ) * Dd p' + Qb p') := by
    unfold alphaF betaF
    rw [hD]
    linear_combination (-(Usg p') * Dd p') * hr2
  rw [key]
  have hδ : ((((p' % 2) * w + j) % 2 : ℕ) : ℤ) = 0 ∨ ((((p' % 2) * w + j) % 2 : ℕ) : ℤ) = 1 := by omega
  have hb := Dd_bd p'
  rw [abs_le]
  rcases Usg_pm p' with hU | hU <;> rcases Qb_pm p' with hQb | hQb <;> rcases hδ with hd | hd <;>
    rw [hU, hQb, hd] <;> constructor <;> linarith [hb.1, hb.2]

end Erdos1186Ex
end

section
namespace Erdos1186Ex

open Finset

theorem bathtub {ι : Type*} [DecidableEq ι] (I : Finset ι) (g : ι → ℝ) (hg : ∀ x ∈ I, 0 ≤ g x)
    (ρ κ : ℝ) (hρ : 0 < ρ) (hκ : 0 ≤ κ)
    (hcount : ∀ t : ℝ, 0 ≤ t → ((I.filter fun x => g x < t).card : ℝ) ≤ ρ * t + κ) :
    ∀ S : Finset ι, S ⊆ I → (max ((S.card : ℝ) - κ) 0) ^ 2 / (2 * ρ) ≤ ∑ x ∈ S, g x := by
  intro S
  induction' hk : S.card with k ih generalizing S
  · intro _
    have hS : S = ∅ := Finset.card_eq_zero.mp hk
    subst hS
    simp only [Nat.cast_zero, zero_sub, Finset.sum_empty]
    have : max (-κ) 0 = 0 := max_eq_right (by linarith)
    rw [this]; simp
  · intro hSI
    have hne : S.Nonempty := by
      rw [← Finset.card_pos, hk]; exact Nat.succ_pos k
    obtain ⟨xs, hxs, hmax⟩ := Finset.exists_max_image S g hne
    have hcard' : (S.erase xs).card = k := by
      rw [Finset.card_erase_of_mem hxs, hk]; rfl
    have hsub' : S.erase xs ⊆ I := (Finset.erase_subset _ _).trans hSI
    have ih' := ih (S.erase xs) hcard' hsub'
    have hgx : 0 ≤ g xs := hg xs (hSI hxs)
    
    have hlow : ((k + 1 : ℕ) : ℝ) ≤ ρ * g xs + κ := by
      by_contra hcon
      push Not at hcon
      set η : ℝ := (((k + 1 : ℕ) : ℝ) - (ρ * g xs + κ)) / (2 * ρ) with hη
      have hηpos : 0 < η := by
        rw [hη]; apply div_pos; linarith; linarith
      have ht0 : 0 ≤ g xs + η := by linarith
      have hc := hcount (g xs + η) ht0
      have hsubf : S ⊆ I.filter fun x => g x < g xs + η := by
        intro x hx
        rw [Finset.mem_filter]
        exact ⟨hSI hx, by have := hmax x hx; linarith⟩
      have h1 : ((S.card : ℕ) : ℝ) ≤ ((I.filter fun x => g x < g xs + η).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubf
      rw [hk] at h1
      have h2 : ρ * (g xs + η) + κ < ((k + 1 : ℕ) : ℝ) := by
        have : ρ * η = (((k + 1 : ℕ) : ℝ) - (ρ * g xs + κ)) / 2 := by
          rw [hη]; field_simp
        nlinarith
      linarith
    rw [← Finset.add_sum_erase S g hxs]
    set A := max (((k + 1 : ℕ) : ℝ) - κ) 0 with hA
    set B := max ((k : ℝ) - κ) 0 with hB
    have hAle : A ≤ ρ * g xs := by
      rw [hA]; apply max_le; linarith; positivity
    have hAB : A ^ 2 ≤ B ^ 2 + 2 * A := by
      rcases le_total ((k : ℝ) - κ) 0 with h | h
      · have hB0 : B = 0 := by rw [hB]; exact max_eq_right h
        rw [hB0]
        rcases le_total ((k : ℝ) + 1 - κ) 0 with h' | h'
        · have : A = 0 := by rw [hA]; push_cast; exact max_eq_right h'
          rw [this]; norm_num
        · have : A = (k : ℝ) + 1 - κ := by rw [hA]; push_cast; exact max_eq_left h'
          rw [this]; nlinarith
      · have hB' : B = (k : ℝ) - κ := by rw [hB]; exact max_eq_left h
        have hA' : A = (k : ℝ) + 1 - κ := by rw [hA]; push_cast; exact max_eq_left (by linarith)
        rw [hB', hA']; nlinarith
    have hfin : A ^ 2 / (2 * ρ) ≤ B ^ 2 / (2 * ρ) + g xs := by
      have h3 : A ^ 2 / (2 * ρ) ≤ (B ^ 2 + 2 * A) / (2 * ρ) :=
        div_le_div_of_nonneg_right hAB (by positivity)
      have h4 : (B ^ 2 + 2 * A) / (2 * ρ) = B ^ 2 / (2 * ρ) + A / ρ := by field_simp
      have h5 : A / ρ ≤ g xs := by rw [div_le_iff₀ hρ]; linarith
      linarith
    linarith

theorem card_ap_le (w : ℕ) (u : ℕ → ℝ) (s lo hi : ℝ) (hs : 0 < s)
    (hu : ∀ j j', |u j - u j'| = s * |(j : ℝ) - j'|) :
    (((Icc 1 w).filter (fun j => lo ≤ u j ∧ u j < hi)).card : ℝ) ≤ max 0 ((hi - lo) / s) + 1 := by
  set T := (Icc 1 w).filter (fun j => lo ≤ u j ∧ u j < hi) with hT
  rcases T.eq_empty_or_nonempty with h | h
  · rw [h]; simp only [Finset.card_empty, Nat.cast_zero]
    have : (0 : ℝ) ≤ max 0 ((hi - lo) / s) := le_max_left _ _
    linarith
  · have ha := T.min'_mem h
    have hb := T.max'_mem h
    set a := T.min' h with ha_def
    set b := T.max' h with hb_def
    have hab : a ≤ b := T.min'_le _ hb
    have hsub : T ⊆ Icc a b := fun x hx => mem_Icc.2 ⟨T.min'_le x hx, T.le_max' x hx⟩
    have hcard : T.card ≤ b + 1 - a := by
      have := Finset.card_le_card hsub
      simpa using this
    have hcardR : (T.card : ℝ) ≤ (b : ℝ) + 1 - a := by
      have : ((b + 1 - a : ℕ) : ℝ) = (b : ℝ) + 1 - a := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [← this]; exact_mod_cast hcard
    have hmb := (Finset.mem_filter.mp hb).2
    have hma := (Finset.mem_filter.mp ha).2
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    have hd : s * ((b : ℝ) - a) = |u b - u a| := by
      rw [hu b a, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (b : ℝ) - a)]
    have hlt : |u b - u a| < hi - lo := by
      rw [abs_lt]; constructor <;> linarith [hmb.1, hmb.2, hma.1, hma.2]
    have hpos : 0 < hi - lo := by
      have := abs_nonneg (u b - u a); linarith
    have : ((b : ℝ) - a) < (hi - lo) / s := by
      rw [lt_div_iff₀ hs]; linarith
    have h2 : (hi - lo) / s ≤ max 0 ((hi - lo) / s) := le_max_right _ _
    linarith

noncomputable def ramp (d s z : ℝ) : ℝ := min 1 (max 0 ((z - d) / s))

theorem ramp_interp (d s : ℤ) (hs : 0 < s) (c : ℕ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ramp d s ((c : ℝ) + θ) = (1 - θ) * ramp d s (c : ℝ) + θ * ramp d s ((c : ℝ) + 1) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  unfold ramp
  by_cases ha : (c : ℤ) + 1 ≤ d
  · have haR : (c : ℝ) + 1 ≤ d := by exact_mod_cast ha
    have e1 : max 0 (((c : ℝ) + θ - d) / s) = 0 := by
      apply max_eq_left; apply div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le
    have e2 : max 0 (((c : ℝ) - d) / s) = 0 := by
      apply max_eq_left; apply div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le
    have e3 : max 0 (((c : ℝ) + 1 - d) / s) = 0 := by
      apply max_eq_left; apply div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le
    rw [e1, e2, e3]; simp
  · by_cases hb : d + s ≤ (c : ℤ)
    · have hbR : (d : ℝ) + s ≤ c := by exact_mod_cast hb
      have e1 : min 1 (max 0 (((c : ℝ) + θ - d) / s)) = 1 := by
        apply min_eq_left
        apply le_max_of_le_right
        rw [le_div_iff₀ hsR]; linarith
      have e2 : min 1 (max 0 (((c : ℝ) - d) / s)) = 1 := by
        apply min_eq_left
        apply le_max_of_le_right
        rw [le_div_iff₀ hsR]; linarith
      have e3 : min 1 (max 0 (((c : ℝ) + 1 - d) / s)) = 1 := by
        apply min_eq_left
        apply le_max_of_le_right
        rw [le_div_iff₀ hsR]; linarith
      rw [e1, e2, e3]; ring
    · have hd : d ≤ (c : ℤ) := by omega
      have hcs : (c : ℤ) + 1 ≤ d + s := by omega
      have hdR : (d : ℝ) ≤ c := by exact_mod_cast hd
      have hcsR : (c : ℝ) + 1 ≤ d + s := by exact_mod_cast hcs
      have key : ∀ z : ℝ, (c : ℝ) ≤ z → z ≤ (c : ℝ) + 1 →
          min 1 (max 0 ((z - d) / s)) = (z - d) / s := by
        intro z hz1 hz2
        have hnn : 0 ≤ (z - d) / s := div_nonneg (by linarith) hsR.le
        have hle : (z - d) / s ≤ 1 := by rw [div_le_iff₀ hsR]; linarith
        rw [max_eq_right hnn, min_eq_right hle]
      rw [key _ (by linarith) (by linarith), key _ le_rfl (by linarith), key _ (by linarith) le_rfl]
      field_simp
      ring

theorem ramp_sum_le {ι : Type*} (I : Finset ι) (d s : ι → ℤ) (hs : ∀ p ∈ I, 0 < s p) (ρ : ℝ)
    (h : ∀ c : ℕ, ∑ p ∈ I, ramp (d p) (s p) (c : ℝ) ≤ ρ * c) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∑ p ∈ I, ramp (d p) (s p) τ ≤ ρ * τ := by
  set c := ⌊τ⌋₊ with hc
  set θ := τ - c with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; have := Nat.floor_le hτ; linarith
  have hθ1 : θ ≤ 1 := by rw [hθ]; have := Nat.lt_floor_add_one τ; linarith
  have hτ' : τ = (c : ℝ) + θ := by rw [hθ]; ring
  have e : ∑ p ∈ I, ramp (d p) (s p) τ
      = (1 - θ) * ∑ p ∈ I, ramp (d p) (s p) (c : ℝ) + θ * ∑ p ∈ I, ramp (d p) (s p) ((c : ℝ) + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hτ']; exact ramp_interp (d p) (s p) (hs p hp) c θ hθ0 hθ1
  rw [e]
  have h1 := h c
  have h2 := h (c + 1)
  push_cast at h2
  nlinarith

theorem ramp_nonneg (d s z : ℝ) : 0 ≤ ramp d s z := by
  unfold ramp; exact le_min zero_le_one (le_max_left _ _)

theorem ramp_le_one (d s z : ℝ) : ramp d s z ≤ 1 := by
  unfold ramp; exact min_le_left _ _

theorem ramp_zero_of (d s : ℤ) (hs : 0 < s) (hd : 0 ≤ d) : ramp d s 0 = 0 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd
  unfold ramp
  have : max 0 (((0 : ℝ) - d) / s) = 0 :=
    max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le)
  rw [this]; norm_num

theorem ramp_one_of (d s : ℤ) (hs : 0 < s) (z : ℝ) (h : (d : ℝ) + s ≤ z) : ramp d s z = 1 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  unfold ramp
  apply min_eq_left
  apply le_max_of_le_right
  rw [le_div_iff₀ hsR]; linarith

theorem ramp_succ (d s : ℤ) (hs : 0 < s) (c : ℕ) :
    ramp d s ((c : ℝ) + 1) = ramp d s (c : ℝ) + (if d ≤ (c : ℤ) ∧ (c : ℤ) < d + s then 1 / (s : ℝ) else 0) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  by_cases ha : (c : ℤ) + 1 ≤ d
  · have haR : (c : ℝ) + 1 ≤ d := by exact_mod_cast ha
    have e1 : ramp d s ((c : ℝ) + 1) = 0 := by
      unfold ramp
      have : max 0 ((((c : ℝ) + 1) - d) / s) = 0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le)
      rw [this]; norm_num
    have e2 : ramp d s (c : ℝ) = 0 := by
      unfold ramp
      have : max 0 (((c : ℝ) - d) / s) = 0 :=
        max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le)
      rw [this]; norm_num
    have e3 : ¬ (d ≤ (c : ℤ) ∧ (c : ℤ) < d + s) := by omega
    rw [e1, e2, if_neg e3]; ring
  · by_cases hb : d + s ≤ (c : ℤ)
    · have hbR : (d : ℝ) + s ≤ c := by exact_mod_cast hb
      rw [ramp_one_of d s hs _ (by linarith), ramp_one_of d s hs _ hbR]
      have e3 : ¬ (d ≤ (c : ℤ) ∧ (c : ℤ) < d + s) := by omega
      rw [if_neg e3]; ring
    · have hd : d ≤ (c : ℤ) := by omega
      have hcs : (c : ℤ) + 1 ≤ d + s := by omega
      have hdR : (d : ℝ) ≤ c := by exact_mod_cast hd
      have hcsR : (c : ℝ) + 1 ≤ d + s := by exact_mod_cast hcs
      have key : ∀ z : ℝ, (c : ℝ) ≤ z → z ≤ (c : ℝ) + 1 →
          ramp d s z = (z - d) / s := by
        intro z hz1 hz2
        unfold ramp
        have hnn : 0 ≤ (z - d) / s := div_nonneg (by linarith) hsR.le
        have hle : (z - d) / s ≤ 1 := by rw [div_le_iff₀ hsR]; linarith
        rw [max_eq_right hnn, min_eq_right hle]
      rw [key _ (by linarith) le_rfl, key _ le_rfl (by linarith), if_pos ⟨hd, by omega⟩]
      field_simp
      ring

theorem level_count {ι : Type*} (I : Finset ι) (d s : ι → ℤ) (hs : ∀ p ∈ I, 0 < s p) (hd : ∀ p ∈ I, 0 ≤ d p)
    (K : ℕ) (hK : ∀ p ∈ I, d p + s p ≤ (K : ℤ)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hinc : ∀ c : ℕ, c < K →
      ∑ p ∈ I, (if d p ≤ (c : ℤ) ∧ (c : ℤ) < d p + s p then 1 / (s p : ℝ) else 0) ≤ ρ) :
    ∀ c : ℕ, ∑ p ∈ I, ramp (d p) (s p) (c : ℝ) ≤ ρ * c := by
  have step : ∀ c : ℕ, c ≤ K → ∑ p ∈ I, ramp (d p) (s p) (c : ℝ) ≤ ρ * c := by
    intro c
    induction c with
    | zero =>
      intro _
      have : ∑ p ∈ I, ramp (d p) (s p) ((0 : ℕ) : ℝ) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        push_cast
        exact ramp_zero_of _ _ (hs p hp) (hd p hp)
      rw [this]; simp
    | succ c ih =>
      intro hc
      have h1 := ih (by omega)
      have h2 := hinc c (by omega)
      have e : ∑ p ∈ I, ramp (d p) (s p) (((c + 1 : ℕ)) : ℝ)
          = ∑ p ∈ I, ramp (d p) (s p) (c : ℝ)
            + ∑ p ∈ I, (if d p ≤ (c : ℤ) ∧ (c : ℤ) < d p + s p then 1 / (s p : ℝ) else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        push_cast
        exact ramp_succ (d p) (s p) (hs p hp) c
      rw [e]; push_cast; nlinarith
  intro c
  by_cases hc : c ≤ K
  · exact step c hc
  · push Not at hc
    have hall : ∀ c' : ℕ, K ≤ c' → ∑ p ∈ I, ramp (d p) (s p) (c' : ℝ) = (I.card : ℝ) := by
      intro c' hc'
      have : ∀ p ∈ I, ramp (d p) (s p) (c' : ℝ) = 1 := by
        intro p hp
        apply ramp_one_of _ _ (hs p hp)
        have h1 := hK p hp
        have h2 : ((d p + s p : ℤ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast h1
        have h3 : (K : ℝ) ≤ c' := by exact_mod_cast hc'
        push_cast at h2
        linarith
      rw [Finset.sum_congr rfl this]; simp
    rw [hall c hc.le]
    have := step K le_rfl
    rw [hall K le_rfl] at this
    have hKc : (K : ℝ) ≤ c := by exact_mod_cast hc.le
    nlinarith

theorem piece_count (w : ℕ) (hw : 1 ≤ w) (u : ℕ → ℝ) (d s : ℤ) (hs : 0 < s)
    (hu : ∀ j j', |u j - u j'| = (s : ℝ) * |(j : ℝ) - j'|)
    (hlo : ∀ j ∈ Icc 1 w, (d : ℝ) * w ≤ u j) (t : ℝ) :
    (((Icc 1 w).filter (fun j => u j < t)).card : ℝ) ≤ (w : ℝ) * ramp d s (t / w) + 1 := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  set F := (Icc 1 w).filter (fun j => u j < t) with hF
  have h1 : (F.card : ℝ) ≤ w := by
    have : F.card ≤ (Icc 1 w).card := Finset.card_filter_le _ _
    have h' : F.card ≤ w := by simpa using this
    exact_mod_cast h'
  have h2 : (F.card : ℝ) ≤ max 0 ((t - d * w) / s) + 1 := by
    have hsub : F ⊆ (Icc 1 w).filter (fun j => (d : ℝ) * w ≤ u j ∧ u j < t) := by
      intro j hj
      rw [hF, Finset.mem_filter] at hj
      rw [Finset.mem_filter]
      exact ⟨hj.1, hlo j hj.1, hj.2⟩
    have hc : (F.card : ℝ) ≤ (((Icc 1 w).filter (fun j => (d : ℝ) * w ≤ u j ∧ u j < t)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have := card_ap_le w u (s : ℝ) ((d : ℝ) * w) t hsR hu
    linarith
  have hr0 : 0 ≤ ramp d s (t / w) := ramp_nonneg _ _ _
  have hY : ((t / w) - d) / s = ((t - d * w) / s) / w := by field_simp
  rcases le_or_gt ((t - d * w) / s) 0 with hY0 | hY0
  · have : max 0 ((t - d * w) / s) = 0 := max_eq_left hY0
    rw [this] at h2
    nlinarith
  · rw [max_eq_right hY0.le] at h2
    by_cases hYw : (t - d * w) / s ≤ w
    · have hr : ramp d s (t / w) = ((t - d * w) / s) / w := by
        unfold ramp
        rw [hY]
        have hnn : 0 ≤ ((t - d * w) / s) / w := div_nonneg hY0.le hwR.le
        have hle : ((t - d * w) / s) / w ≤ 1 := by rw [div_le_iff₀ hwR]; linarith
        rw [max_eq_right hnn, min_eq_right hle]
      rw [hr]
      have : (w : ℝ) * (((t - d * w) / s) / w) = (t - d * w) / s := by field_simp
      rw [this]; exact h2
    · push Not at hYw
      have hr : ramp d s (t / w) = 1 := by
        unfold ramp
        rw [hY]
        have : 1 ≤ ((t - d * w) / s) / w := by rw [le_div_iff₀ hwR]; linarith
        rw [max_eq_right (by linarith)]
        exact min_eq_left this
      rw [hr]; linarith

end Erdos1186Ex
end

section
namespace Erdos1186Ex

def nuTab8 : List ℤ := [72, 56, 40, 32, 32, 16, 0, 0, 0, 0, 8, 24, 40, 52, 36, 12, 0, 0, 12, 36, 52, 68, 60, 44, 28, 12, 0, 0, 4, 20, 36, 52, 68, 84, 100, 108, 116, 108, 84, 60, 36, 12, 0, 0, 12, 36, 60, 84, 108, 132, 156, 180, 204, 208, 192, 176, 160, 144, 128, 112, 110, 124, 140, 148, 156, 132, 108, 84, 78, 60, 36, 12, 0, 0, 12, 36, 60, 78, 84, 108, 132, 156, 148, 140, 124, 110, 112, 128, 144, 160, 176, 192, 208, 204, 180, 156, 132, 108, 84, 60, 36, 12, 0, 0, 12, 36, 60, 84, 108, 116, 108, 100, 84, 68, 52, 36, 20, 4, 0, 0, 12, 28, 44, 60, 68, 52, 36, 12, 0, 0, 12, 36, 52, 40, 24, 8, 0, 0, 0, 0, 16, 32, 32, 40, 56, 72]
def tTab8 : List ℕ := [3, 3, 3, 6, 6, 3, 3, 6, 3, 3, 3, 3, 3, 6, 3, 2, 2, 2, 2, 3, 3, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 6, 6, 6, 8, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 8, 6, 3, 3, 3, 3, 3, 3, 6, 3, 6, 6, 8, 2, 2, 2, 8, 2, 2, 2, 2, 2, 2, 2, 2, 8, 2, 2, 2, 8, 6, 6, 3, 6, 3, 3, 3, 3, 3, 3, 6, 8, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 8, 6, 6, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 6, 3, 3, 2, 2, 2, 2, 3, 6, 3, 3, 3, 3, 3, 6, 3, 3, 6, 6, 3, 3, 3]

end Erdos1186Ex
end

section
namespace Erdos1186Ex

def dd (p' : ℕ) : ℤ := if alphaF p' ≤ alphaF p' + betaF p' then alphaF p' else alphaF p' + betaF p'

def ss (p' : ℕ) : ℕ := (betaF p').natAbs

def pcsL (ν : ℤ) (lo : ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => []
  | n + 1 => ((dd lo - ν).toNat, ss lo) :: pcsL ν (lo + 1) n

def S6 (l : List (ℕ × ℕ)) (c : ℕ) : ℕ :=
  (l.map (fun q => bif Nat.ble q.1 c && Nat.blt c (q.1 + q.2) then 6 / q.2 else 0)).sum

def allBelow (P : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => allBelow P n && P n

def cellChk (G : Grid) (nuT : List ℤ) (tT : List ℕ) (i : ℕ) : Bool :=
  decide (0 < G.len i) && decide (G.hi i ≤ 1096) && decide (0 < tT.getD i 0) &&
  decide (G.ai i * (1096 * 2192) ≤ ((G.len i : ℕ) : ℚ) * (nuT.getD i 0)) &&
  decide (G.bi i * (4 * 1096 ^ 2) * ((tT.getD i 0 : ℕ) : ℚ) ≤ 6 * ((G.len i : ℕ) : ℚ) ^ 2) &&
  (List.range' (G.lo i) (G.len i)).all
    (fun p' => decide (nuT.getD i 0 ≤ dd p') && decide (0 < ss p') && (6 % ss p' == 0) &&
      Nat.ble ((dd p' - nuT.getD i 0).toNat + ss p') (3 * G.len i)) &&
  allBelow (fun c => Nat.ble (S6 (pcsL (nuT.getD i 0) (G.lo i) (G.len i)) c) (tT.getD i 0)) (3 * G.len i)

def chkRange (G : Grid) (nuT : List ℤ) (tT : List ℕ) (a b : ℕ) : Bool :=
  (List.range' a (b - a)).all (cellChk G nuT tT)

end Erdos1186Ex
end

section
namespace Erdos1186Ex

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

noncomputable def linX (w x : ℕ) : ℝ :=
  (alphaF ((x - 1) / w) : ℝ) * w + (betaF ((x - 1) / w) : ℝ) * (((x - 1) % w + 1 : ℕ) : ℝ)

lemma split_pt (w : ℕ) (hw : 1 ≤ w) (x : ℕ) (hx : 1 ≤ x) :
    x = ((x - 1) / w) * w + ((x - 1) % w + 1) ∧ (x - 1) % w + 1 ≤ w := by
  have h1 := Nat.div_add_mod (x - 1) w
  have h2 : (x - 1) % w < w := Nat.mod_lt _ (by omega)
  have h3 : (x - 1) / w * w = w * ((x - 1) / w) := Nat.mul_comm _ _
  constructor <;> omega

lemma H2_linX (w : ℕ) (hw : 1 ≤ w) (x : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ 1096 * w) :
    |(H2 w x : ℝ) - linX w x| ≤ 2 := by
  obtain ⟨hxe, hj⟩ := split_pt w hw x hx1
  have hp : (x - 1) / w ≤ 1095 := by
    have : (x - 1) / w < 1096 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    omega
  have h := H2_lin w hw ((x - 1) / w) ((x - 1) % w + 1) hp (by omega) hj
  rw [← hxe] at h
  unfold linX
  have h2 : |((H2 w x : ℤ) : ℝ) - ((alphaF ((x - 1) / w) * w
      + betaF ((x - 1) / w) * (((x - 1) % w + 1 : ℕ) : ℤ) : ℤ) : ℝ)| ≤ 2 := by exact_mod_cast h
  push_cast at h2 ⊢
  exact h2

noncomputable def uP (w : ℕ) (ν : ℤ) (p' : ℕ) (j : ℕ) : ℝ :=
  (alphaF p' : ℝ) * w + (betaF p' : ℝ) * j - (ν : ℝ) * w

lemma ss_cast (p' : ℕ) : (((ss p' : ℕ) : ℤ) : ℝ) = |(betaF p' : ℝ)| := by
  unfold ss; rw [Int.natCast_natAbs, Int.cast_abs]

lemma uP_dist (w : ℕ) (ν : ℤ) (p' j j' : ℕ) :
    |uP w ν p' j - uP w ν p' j'| = (((ss p' : ℕ) : ℤ) : ℝ) * |(j : ℝ) - j'| := by
  unfold uP
  have : (alphaF p' : ℝ) * w + betaF p' * j - ν * w - ((alphaF p' : ℝ) * w + betaF p' * j' - ν * w)
      = (betaF p' : ℝ) * ((j : ℝ) - j') := by ring
  rw [this, abs_mul, ss_cast]

lemma uP_lo (w : ℕ) (ν : ℤ) (p' j : ℕ) (hj2 : j ≤ w) :
    (((dd p' - ν : ℤ)) : ℝ) * w ≤ uP w ν p' j := by
  unfold uP dd
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hjw : (j : ℝ) ≤ w := by exact_mod_cast hj2
  split_ifs with h
  · have hb : (0 : ℝ) ≤ betaF p' := by
      have : 0 ≤ betaF p' := by omega
      exact_mod_cast this
    push_cast
    nlinarith
  · have hb : (betaF p' : ℝ) < 0 := by
      have : betaF p' < 0 := by omega
      exact_mod_cast this
    push_cast
    nlinarith

lemma piece_count' (w : ℕ) (hw : 1 ≤ w) (ν : ℤ) (p' : ℕ) (hs : 0 < ss p') (t : ℝ) :
    (((Icc 1 w).filter (fun j => uP w ν p' j < t)).card : ℝ)
      ≤ (w : ℝ) * ramp ((dd p' - ν : ℤ) : ℝ) (((ss p' : ℕ) : ℤ) : ℝ) (t / w) + 1 :=
  piece_count w hw (uP w ν p') (dd p' - ν) ((ss p' : ℕ) : ℤ) (by exact_mod_cast hs) (uP_dist w ν p')
    (fun j hj => uP_lo w ν p' j (Finset.mem_Icc.1 hj).2) t

lemma mem_piece (w : ℕ) (hw : 1 ≤ w) (lo L x : ℕ) (hx : x ∈ Ioc (lo * w) ((lo + L) * w)) :
    (x - 1) / w ∈ Ico lo (lo + L) := by
  rw [Finset.mem_Ioc] at hx
  obtain ⟨h1, h2⟩ := hx
  rw [Finset.mem_Ico]
  constructor
  · rw [Nat.le_div_iff_mul_le (by omega)]; omega
  · rw [Nat.div_lt_iff_lt_mul (by omega)]; omega

lemma inc_eq (p' : ℕ) (ν : ℤ) (hnu : ν ≤ dd p') (hs : 0 < ss p') (h6 : 6 % ss p' = 0) (c : ℕ) :
    (if dd p' - ν ≤ (c : ℤ) ∧ (c : ℤ) < (dd p' - ν) + ((ss p' : ℕ) : ℤ)
        then 1 / (((ss p' : ℕ) : ℤ) : ℝ) else 0)
      = (((if (dd p' - ν).toNat ≤ c ∧ c < (dd p' - ν).toNat + ss p' then 6 / ss p' else 0 : ℕ)) : ℝ) / 6 := by
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) = dd p' - ν := ⟨(dd p' - ν).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hte : (dd p' - ν).toNat = e := by omega
  rw [hte, ← he]
  have hcond : ((e : ℤ) ≤ (c : ℤ) ∧ (c : ℤ) < (e : ℤ) + ((ss p' : ℕ) : ℤ)) ↔ (e ≤ c ∧ c < e + ss p') := by
    constructor <;> (intro h; omega)
  by_cases h : e ≤ c ∧ c < e + ss p'
  · rw [if_pos (hcond.2 h), if_pos h]
    have hdvd : ss p' ∣ 6 := Nat.dvd_of_mod_eq_zero h6
    have hsR : (ss p' : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    rw [Nat.cast_div hdvd hsR, Int.cast_natCast]
    push_cast
    field_simp
  · rw [if_neg (fun h' => h (hcond.1 h')), if_neg h]
    simp

lemma cell_count (w : ℕ) (hw : 1 ≤ w) (lo L : ℕ) (ν : ℤ) (T : ℕ)
    (hnu : ∀ p' ∈ Ico lo (lo + L), ν ≤ dd p')
    (hpc : ∀ p' ∈ Ico lo (lo + L), 0 < ss p' ∧ 6 % ss p' = 0 ∧ (dd p' - ν).toNat + ss p' ≤ 3 * L)
    (hlev : ∀ c < 3 * L, ∑ p' ∈ Ico lo (lo + L),
        (if (dd p' - ν).toNat ≤ c ∧ c < (dd p' - ν).toNat + ss p' then 6 / ss p' else 0) ≤ T)
    (t : ℝ) (ht : 0 ≤ t) :
    (((Ioc (lo * w) ((lo + L) * w)).filter (fun x => linX w x - ν * w < t)).card : ℝ)
      ≤ (T / 6 : ℝ) * t + L := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hsub : (Ioc (lo * w) ((lo + L) * w)).filter (fun x => linX w x - ν * w < t) ⊆
      (Ico lo (lo + L)).biUnion (fun p' =>
        ((Icc 1 w).filter (fun j => uP w ν p' j < t)).image (fun j => p' * w + j)) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxI, h3⟩ := hx
    have hxI' := Finset.mem_Ioc.1 hxI
    obtain ⟨hxe, hj⟩ := split_pt w hw x (by omega)
    rw [Finset.mem_biUnion]
    refine ⟨(x - 1) / w, mem_piece w hw lo L x hxI, ?_⟩
    rw [Finset.mem_image]
    refine ⟨(x - 1) % w + 1, ?_, hxe.symm⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, hj⟩, ?_⟩
    have : uP w ν ((x - 1) / w) ((x - 1) % w + 1) = linX w x - ν * w := by unfold uP linX; ring
    rw [this]; exact h3
  have hcardN : ((Ioc (lo * w) ((lo + L) * w)).filter (fun x => linX w x - ν * w < t)).card
      ≤ ∑ p' ∈ Ico lo (lo + L), ((Icc 1 w).filter (fun j => uP w ν p' j < t)).card :=
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum (fun p' _ => Finset.card_image_le)
  have hcardR : (((Ioc (lo * w) ((lo + L) * w)).filter (fun x => linX w x - ν * w < t)).card : ℝ)
      ≤ ∑ p' ∈ Ico lo (lo + L), (((Icc 1 w).filter (fun j => uP w ν p' j < t)).card : ℝ) := by
    exact_mod_cast hcardN
  have hpiece : ∀ p' ∈ Ico lo (lo + L), (((Icc 1 w).filter (fun j => uP w ν p' j < t)).card : ℝ)
      ≤ (w : ℝ) * ramp ((dd p' - ν : ℤ) : ℝ) (((ss p' : ℕ) : ℤ) : ℝ) (t / w) + 1 :=
    fun p' hp => piece_count' w hw ν p' (hpc p' hp).1 t
  have hsum := Finset.sum_le_sum hpiece
  have hinc : ∀ c : ℕ, c < 3 * L → ∑ p' ∈ Ico lo (lo + L),
      (if dd p' - ν ≤ (c : ℤ) ∧ (c : ℤ) < (dd p' - ν) + ((ss p' : ℕ) : ℤ)
        then 1 / (((ss p' : ℕ) : ℤ) : ℝ) else 0) ≤ (T : ℝ) / 6 := by
    intro c hc
    have e : ∑ p' ∈ Ico lo (lo + L),
        (if dd p' - ν ≤ (c : ℤ) ∧ (c : ℤ) < (dd p' - ν) + ((ss p' : ℕ) : ℤ)
          then 1 / (((ss p' : ℕ) : ℤ) : ℝ) else 0)
        = ((∑ p' ∈ Ico lo (lo + L),
            (if (dd p' - ν).toNat ≤ c ∧ c < (dd p' - ν).toNat + ss p' then 6 / ss p' else 0) : ℕ) : ℝ) / 6 := by
      rw [Nat.cast_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p' hp
      exact inc_eq p' ν (hnu p' hp) (hpc p' hp).1 (hpc p' hp).2.1 c
    rw [e]
    have h1 := hlev c hc
    have h2 : ((∑ p' ∈ Ico lo (lo + L),
            (if (dd p' - ν).toNat ≤ c ∧ c < (dd p' - ν).toNat + ss p' then 6 / ss p' else 0) : ℕ) : ℝ)
        ≤ T := by exact_mod_cast h1
    linarith
  have hramp : ∑ p' ∈ Ico lo (lo + L), ramp ((dd p' - ν : ℤ) : ℝ) (((ss p' : ℕ) : ℤ) : ℝ) (t / w)
      ≤ ((T : ℝ) / 6) * (t / w) := by
    apply ramp_sum_le (Ico lo (lo + L)) (fun p' => dd p' - ν) (fun p' => ((ss p' : ℕ) : ℤ))
      (fun p' hp => by show (0 : ℤ) < ((ss p' : ℕ) : ℤ); exact_mod_cast (hpc p' hp).1) ((T : ℝ) / 6)
      (level_count (Ico lo (lo + L)) (fun p' => dd p' - ν) (fun p' => ((ss p' : ℕ) : ℤ))
        (fun p' hp => by show (0 : ℤ) < ((ss p' : ℕ) : ℤ); exact_mod_cast (hpc p' hp).1)
        (fun p' hp => by have := hnu p' hp; omega)
        (3 * L)
        (fun p' hp => by have := (hpc p' hp).2.2; have := hnu p' hp; omega)
        ((T : ℝ) / 6) (by positivity) hinc)
      (t / w) (div_nonneg ht hwR.le)
  have hconst : ∑ p' ∈ Ico lo (lo + L), (1 : ℝ) = L := by simp
  have hexp : ∑ p' ∈ Ico lo (lo + L),
      ((w : ℝ) * ramp ((dd p' - ν : ℤ) : ℝ) (((ss p' : ℕ) : ℤ) : ℝ) (t / w) + 1)
      = (w : ℝ) * ∑ p' ∈ Ico lo (lo + L), ramp ((dd p' - ν : ℤ) : ℝ) (((ss p' : ℕ) : ℤ) : ℝ) (t / w) + L := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hconst]
  have hmul : (w : ℝ) * ∑ p' ∈ Ico lo (lo + L), ramp ((dd p' - ν : ℤ) : ℝ) (((ss p' : ℕ) : ℤ) : ℝ) (t / w)
      ≤ (T / 6 : ℝ) * t := by
    have h1 := mul_le_mul_of_nonneg_left hramp hwR.le
    have h2 : (w : ℝ) * (((T : ℝ) / 6) * (t / w)) = (T / 6 : ℝ) * t := by field_simp
    linarith
  linarith

lemma cell_core (w : ℕ) (hw : 1 ≤ w) (lo L : ℕ) (hL : lo + L ≤ 1096) (ν : ℤ) (T : ℕ) (hT : 0 < T)
    (hnu : ∀ p' ∈ Ico lo (lo + L), ν ≤ dd p')
    (hpc : ∀ p' ∈ Ico lo (lo + L), 0 < ss p' ∧ 6 % ss p' = 0 ∧ (dd p' - ν).toNat + ss p' ≤ 3 * L)
    (hlev : ∀ c < 3 * L, ∑ p' ∈ Ico lo (lo + L),
        (if (dd p' - ν).toNat ≤ c ∧ c < (dd p' - ν).toNat + ss p' then 6 / ss p' else 0) ≤ T)
    (σ : ℕ → ℤ) (hσ : IsInd σ) :
    (ν : ℝ) * w * (((Ioc (lo * w) ((lo + L) * w)).filter (fun x => σ x = 1)).card : ℝ)
      + 3 * (((Ioc (lo * w) ((lo + L) * w)).filter (fun x => σ x = 1)).card : ℝ) ^ 2 / T
      - (6 * (L : ℝ) ^ 2 + 2 * L) * w
      ≤ ((∑ x ∈ Ioc (lo * w) ((lo + L) * w), H2 w x * σ x : ℤ) : ℝ) := by
  set I := Ioc (lo * w) ((lo + L) * w) with hI
  set S := I.filter (fun x => σ x = 1) with hS
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hSI : S ⊆ I := Finset.filter_subset _ _
  have hsum : ∑ x ∈ I, H2 w x * σ x = ∑ x ∈ S, H2 w x := by
    rw [hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    rcases hσ x with h | h <;> simp [h]
  have hpt : ∀ x ∈ I, 1 ≤ x ∧ x ≤ 1096 * w := by
    intro x hx
    have hx' := Finset.mem_Ioc.1 hx
    refine ⟨by omega, ?_⟩
    calc x ≤ (lo + L) * w := hx'.2
      _ ≤ 1096 * w := Nat.mul_le_mul_right w hL
  have hg : ∀ x ∈ I, 0 ≤ linX w x - ν * w := by
    intro x hx
    have hx' := Finset.mem_Ioc.1 hx
    obtain ⟨hxe, hj⟩ := split_pt w hw x (by omega)
    have hp := mem_piece w hw lo L x hx
    have h1 := uP_lo w ν ((x - 1) / w) ((x - 1) % w + 1) hj
    have h2 : uP w ν ((x - 1) / w) ((x - 1) % w + 1) = linX w x - ν * w := by unfold uP linX; ring
    have h3 : (0 : ℝ) ≤ ((dd ((x - 1) / w) - ν : ℤ) : ℝ) := by
      have := hnu _ hp
      have : (0 : ℤ) ≤ dd ((x - 1) / w) - ν := by omega
      exact_mod_cast this
    have : 0 ≤ ((dd ((x - 1) / w) - ν : ℤ) : ℝ) * w := mul_nonneg h3 hwR.le
    linarith
  have hb := bathtub I (fun x => linX w x - ν * w) hg ((T : ℝ) / 6) (L : ℝ) (by positivity)
    (Nat.cast_nonneg L)
    (fun t ht => cell_count w hw lo L ν T hnu hpc hlev t ht) S hSI
  
  have hpoint : ∀ x ∈ S, (linX w x - ν * w) + ((ν : ℝ) * w - 2) ≤ (H2 w x : ℝ) := by
    intro x hx
    have hxI := hSI hx
    obtain ⟨h1, h2⟩ := hpt x hxI
    have := H2_linX w hw x h1 h2
    rw [abs_le] at this
    linarith [this.1]
  have hS1 : ∑ x ∈ S, ((linX w x - ν * w) + ((ν : ℝ) * w - 2)) ≤ ∑ x ∈ S, (H2 w x : ℝ) :=
    Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hS1
  have hcast : ((∑ x ∈ I, H2 w x * σ x : ℤ) : ℝ) = ∑ x ∈ S, (H2 w x : ℝ) := by
    rw [hsum]; push_cast; rfl
  rw [hcast]
  
  have hcard : (S.card : ℝ) ≤ L * w := by
    have h1 : S.card ≤ I.card := Finset.card_le_card hSI
    have h2 : I.card = L * w := by
      rw [hI, Nat.card_Ioc, Nat.add_mul]; omega
    have : S.card ≤ L * w := by omega
    exact_mod_cast this
  set m : ℝ := (S.card : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  
  have hMx : m ^ 2 - 2 * L * m ≤ (max (m - L) 0) ^ 2 := by
    rcases le_total (m - L) 0 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have hA : (max (m - L) 0) ^ 2 / (2 * ((T : ℝ) / 6)) = 3 * (max (m - L) 0) ^ 2 / T := by
    field_simp; ring
  rw [hA] at hb
  have hq : 0 < (1 : ℝ) / T := by positivity
  have hq1 : (1 : ℝ) / T ≤ 1 := by rw [div_le_one (by positivity)]; exact hTR
  have e1 : 3 * (max (m - L) 0) ^ 2 / T = 3 * (max (m - L) 0) ^ 2 * (1 / T) := by ring
  have e2 : 3 * m ^ 2 / T = 3 * m ^ 2 * (1 / T) := by ring
  have h5 : 3 * (m ^ 2 - 2 * L * m) * (1 / T) ≤ 3 * (max (m - L) 0) ^ 2 * (1 / T) := by
    apply mul_le_mul_of_nonneg_right _ hq.le
    linarith
  have h6 : 6 * L * m * (1 / T) ≤ 6 * L * m := by
    have : 0 ≤ 6 * L * m := by positivity
    nlinarith
  have h7 : 6 * L * m ≤ 6 * L * (L * w) := by
    apply mul_le_mul_of_nonneg_left hcard; positivity
  rw [e1] at hb
  rw [e2]
  nlinarith

lemma allBelow_iff (P : ℕ → Bool) (n : ℕ) : allBelow P n = true ↔ ∀ c < n, P c = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ c hc
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with h | h
      · exact h1 c h
      · rw [h]; exact h2
    · intro h; exact ⟨fun c hc => h c (by omega), h n (by omega)⟩

lemma S6_cons (q : ℕ × ℕ) (l : List (ℕ × ℕ)) (c : ℕ) :
    S6 (q :: l) c = (if q.1 ≤ c ∧ c < q.1 + q.2 then 6 / q.2 else 0) + S6 l c := by
  unfold S6
  rw [List.map_cons, List.sum_cons]
  congr 1
  by_cases h : q.1 ≤ c ∧ c < q.1 + q.2
  · have : (Nat.ble q.1 c && Nat.blt c (q.1 + q.2)) = true := by
      simp [Nat.ble_eq, Nat.blt_eq, h.1, h.2]
    simp [this, h]
  · have : (Nat.ble q.1 c && Nat.blt c (q.1 + q.2)) = false := by
      by_contra hc
      apply h
      have hc' : (Nat.ble q.1 c && Nat.blt c (q.1 + q.2)) = true := by simpa using hc
      simpa [Nat.ble_eq, Nat.blt_eq] using hc'
    simp [this, h]

lemma S6_pcsL (ν : ℤ) (c : ℕ) : ∀ (n lo : ℕ), S6 (pcsL ν lo n) c
    = ∑ k ∈ range n, (if (dd (lo + k) - ν).toNat ≤ c ∧ c < (dd (lo + k) - ν).toNat + ss (lo + k)
        then 6 / ss (lo + k) else 0)
  | 0, lo => by simp [S6, pcsL]
  | n + 1, lo => by
    have ih := S6_pcsL ν c n (lo + 1)
    rw [pcsL, S6_cons, ih, Finset.sum_range_succ', add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [show lo + (k + 1) = lo + 1 + k by omega]

lemma cellChk_spec (G : Grid) (nuT : List ℤ) (tT : List ℕ) (i : ℕ) (h : cellChk G nuT tT i = true) :
    0 < G.len i ∧ G.hi i ≤ 1096 ∧ 0 < tT.getD i 0 ∧
    G.ai i * (1096 * 2192) ≤ ((G.len i : ℕ) : ℚ) * (nuT.getD i 0) ∧
    G.bi i * (4 * 1096 ^ 2) * ((tT.getD i 0 : ℕ) : ℚ) ≤ 6 * ((G.len i : ℕ) : ℚ) ^ 2 ∧
    (∀ p' ∈ Ico (G.lo i) (G.lo i + G.len i), nuT.getD i 0 ≤ dd p') ∧
    (∀ p' ∈ Ico (G.lo i) (G.lo i + G.len i), 0 < ss p' ∧ 6 % ss p' = 0 ∧
        (dd p' - nuT.getD i 0).toNat + ss p' ≤ 3 * G.len i) ∧
    (∀ c < 3 * G.len i, ∑ p' ∈ Ico (G.lo i) (G.lo i + G.len i),
        (if (dd p' - nuT.getD i 0).toNat ≤ c ∧ c < (dd p' - nuT.getD i 0).toNat + ss p'
          then 6 / ss p' else 0) ≤ tT.getD i 0) := by
  unfold cellChk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  simp only [decide_eq_true_eq] at h1 h2 h3 h4 h5
  rw [List.all_eq_true] at h6
  rw [allBelow_iff] at h7
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_⟩
  · intro p' hp
    have hp' : p' ∈ List.range' (G.lo i) (G.len i) := by
      rw [List.mem_range'_1]; rw [Finset.mem_Ico] at hp; omega
    have := h6 p' hp'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1
  · intro p' hp
    have hp' : p' ∈ List.range' (G.lo i) (G.len i) := by
      rw [List.mem_range'_1]; rw [Finset.mem_Ico] at hp; omega
    have := h6 p' hp'
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Nat.ble_eq] at this
    exact ⟨this.1.1.2, this.1.2, this.2⟩
  · intro c hc
    have := h7 c hc
    rw [Nat.ble_eq, S6_pcsL] at this
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    exact this

lemma cell_eq (G : Grid) (i w : ℕ) (hL : 0 < G.len i) :
    G.cell w i = Ioc (G.lo i * w) ((G.lo i + G.len i) * w) := by
  have hhi' : G.hi i = G.lo i + G.len i := by unfold Grid.len at hL ⊢; omega
  unfold Grid.cell; rw [hhi']

theorem cell_sound (G : Grid) (nuT : List ℤ) (tT : List ℕ) (i : ℕ) (h : cellChk G nuT tT i = true)
    (w : ℕ) (hw : 1 ≤ w) (σ : ℕ → ℤ) (hσ : IsInd σ) :
    2 * (nn w : ℝ) ^ 2 * ((G.ai i : ℝ) * G.yv w σ i + (G.bi i : ℝ) * G.yv w σ i ^ 2)
      - (6 * (G.len i : ℝ) ^ 2 + 2 * (G.len i : ℝ)) * w
      ≤ ((∑ x ∈ G.cell w i, H2 w x * σ x : ℤ) : ℝ) := by
  obtain ⟨hL, hhi, hT, ha, hb, hnu, hpc, hlev⟩ := cellChk_spec G nuT tT i h
  have hhi' : G.hi i = G.lo i + G.len i := by unfold Grid.len at hL ⊢; omega
  have hL1096 : G.lo i + G.len i ≤ 1096 := by rw [← hhi']; exact hhi
  have core := cell_core w hw (G.lo i) (G.len i) hL1096 (nuT.getD i 0) (tT.getD i 0) hT hnu hpc hlev σ hσ
  have hcell := cell_eq G i w hL
  rw [hcell]
  set S := (Ioc (G.lo i * w) ((G.lo i + G.len i) * w)).filter (fun x => σ x = 1) with hS
  have hsumσ : (∑ x ∈ Ioc (G.lo i * w) ((G.lo i + G.len i) * w), σ x) = (S.card : ℤ) := by
    rw [hS, Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    rcases hσ x with h | h <;> simp [h]
  have hy : G.yv w σ i = (S.card : ℝ) / ((G.len i : ℝ) * w) := by
    unfold Grid.yv
    rw [hcell, hsumσ]
    push_cast
    rfl
  rw [hy]
  have haR : (G.ai i : ℝ) * (1096 * 2192) ≤ (G.len i : ℝ) * (nuT.getD i 0 : ℤ) := by exact_mod_cast ha
  have hbR : (G.bi i : ℝ) * (4 * 1096 ^ 2) * (tT.getD i 0 : ℕ) ≤ 6 * (G.len i : ℝ) ^ 2 := by
    exact_mod_cast hb
  have hLR : (0 : ℝ) < G.len i := by exact_mod_cast hL
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hTR : (0 : ℝ) < (tT.getD i 0 : ℕ) := by exact_mod_cast hT
  have hnn : (nn w : ℝ) = 1096 * w := by unfold nn; push_cast; ring
  rw [hnn]
  set m : ℝ := (S.card : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  set a : ℝ := (G.ai i : ℝ)
  set b : ℝ := (G.bi i : ℝ)
  set Lr : ℝ := (G.len i : ℝ)
  set ν : ℝ := ((nuT.getD i 0 : ℤ) : ℝ)
  set T : ℝ := ((tT.getD i 0 : ℕ) : ℝ)
  have key1 : 2 * (1096 * (w : ℝ)) ^ 2 * (a * (m / (Lr * w))) ≤ ν * w * m := by
    have e : 2 * (1096 * (w : ℝ)) ^ 2 * (a * (m / (Lr * w))) = (a * (1096 * 2192)) * (w * m / Lr) := by
      field_simp; ring
    rw [e]
    have h1 : (a * (1096 * 2192)) * (w * m / Lr) ≤ (Lr * ν) * (w * m / Lr) :=
      mul_le_mul_of_nonneg_right haR (by positivity)
    have h2 : (Lr * ν) * (w * m / Lr) = ν * w * m := by field_simp
    linarith
  have key2 : 2 * (1096 * (w : ℝ)) ^ 2 * (b * (m / (Lr * w)) ^ 2) ≤ 3 * m ^ 2 / T := by
    have e : 2 * (1096 * (w : ℝ)) ^ 2 * (b * (m / (Lr * w)) ^ 2)
        = (b * (4 * 1096 ^ 2) * T) * (m ^ 2 / (2 * Lr ^ 2 * T)) := by
      field_simp; ring
    rw [e]
    have h1 : (b * (4 * 1096 ^ 2) * T) * (m ^ 2 / (2 * Lr ^ 2 * T))
        ≤ (6 * Lr ^ 2) * (m ^ 2 / (2 * Lr ^ 2 * T)) :=
      mul_le_mul_of_nonneg_right hbR (by positivity)
    have h2 : (6 * Lr ^ 2) * (m ^ 2 / (2 * Lr ^ 2 * T)) = 3 * m ^ 2 / T := by field_simp; ring
    linarith
  have hcore : ν * w * m + 3 * m ^ 2 / T - (6 * Lr ^ 2 + 2 * Lr) * w
      ≤ ((∑ x ∈ Ioc (G.lo i * w) ((G.lo i + G.len i) * w), H2 w x * σ x : ℤ) : ℝ) := core
  nlinarith

theorem bathOK_of_chk (G : Grid) (nuT : List ℤ) (tT : List ℕ)
    (h : ∀ i < G.N, cellChk G nuT tT i = true) : BathOK G := by
  refine ⟨∑ i ∈ range G.N, (6 * (G.len i : ℝ) ^ 2 + 2 * (G.len i : ℝ)), ?_⟩
  intro w hw σ hσ i hi
  have h1 := cell_sound G nuT tT i (h i hi) w hw σ hσ
  have h2 : (6 * (G.len i : ℝ) ^ 2 + 2 * (G.len i : ℝ))
      ≤ ∑ i ∈ range G.N, (6 * (G.len i : ℝ) ^ 2 + 2 * (G.len i : ℝ)) :=
    Finset.single_le_sum (f := fun i => (6 * (G.len i : ℝ) ^ 2 + 2 * (G.len i : ℝ)))
      (fun i _ => by positivity) (Finset.mem_range.2 hi)
  have hwR : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  nlinarith

end Erdos1186Ex
end

section
namespace Erdos1186Ex

theorem chk8a : chkRange G8 nuTab8 tTab8 0 37 = true := by decide +kernel

end Erdos1186Ex
end

section
namespace Erdos1186Ex

theorem chk8b : chkRange G8 nuTab8 tTab8 37 74 = true := by decide +kernel

end Erdos1186Ex
end

section
namespace Erdos1186Ex

theorem chk8c : chkRange G8 nuTab8 tTab8 74 110 = true := by decide +kernel

end Erdos1186Ex
end

section
namespace Erdos1186Ex

theorem chk8d : chkRange G8 nuTab8 tTab8 110 146 = true := by decide +kernel

end Erdos1186Ex
end

section
namespace Erdos1186Ex

theorem chkRange_sound {G : Grid} {nuT : List ℤ} {tT : List ℕ} {a b i : ℕ}
    (h : chkRange G nuT tT a b = true) (h1 : a ≤ i) (h2 : i < b) : cellChk G nuT tT i = true := by
  unfold chkRange at h
  rw [List.all_eq_true] at h
  exact h i (List.mem_range'_1.2 ⟨h1, by omega⟩)

theorem bathOK8 : BathOK G8 := by
  apply bathOK_of_chk G8 nuTab8 tTab8
  intro i hi
  have hN : G8.N = 146 := by decide +kernel
  rw [hN] at hi
  by_cases c1 : i < 37
  · exact chkRange_sound chk8a (by omega) c1
  by_cases c2 : i < 74
  · exact chkRange_sound chk8b (by omega) c2
  by_cases c3 : i < 110
  · exact chkRange_sound chk8c (by omega) c3
  · exact chkRange_sound chk8d (by omega) hi

end Erdos1186Ex
end

section
namespace Erdos1186Ex.FarCut
open Finset Erdos1186Day Erdos1186Night2

def refBlock (a : ℕ) : Bool :=
  a < 28 || (34 ≤ a && a < 62) || (99 ≤ a && a < 158) ||
  (274 ≤ a && a < 390) || (449 ≤ a && a < 486) || (514 ≤ a && a < 520)

def arcs (n : ℕ) := (Icc 1 n ×ˢ Icc 1 n).filter fun p : ℕ × ℕ =>
  p.1+1 ≤ 2*p.2 ∧ 2*p.2 ≤ p.1+n

def signedCut (w : ℕ) (d : ℕ → Bool) : ℤ :=
  ∑ p ∈ arcs (nn w), if d p.1 = d p.2 then 0 else
    if refBlock ((p.1-1)/(2*w)) = refBlock ((p.2-1)/(2*w)) then 1 else -1

def mark (d : ℕ → Bool) (x : ℕ) : ℤ := if d x then 1 else 0

def mass (n : ℕ) (d : ℕ → Bool) := ((Icc 1 n).filter fun x => d x = true).card

theorem coarse (a : ℕ) : c1 (a+1) = refBlock a := by
  by_cases h : a < 520
  · have tab : (List.range 520).all (fun k => c1 (k+1) == refBlock k) = true := by decide +kernel
    exact beq_iff_eq.mp (List.all_eq_true.mp tab a (List.mem_range.mpr h))
  · simp only [c1, Bool.cond_eq_ite, Nat.ble_eq, refBlock]
    simp_all only [show ¬ a+1 ≤ 28 by omega, show ¬ a+1 ≤ 34 by omega,
      show ¬ a+1 ≤ 62 by omega, show ¬ a+1 ≤ 99 by omega, show ¬ a+1 ≤ 158 by omega,
      show ¬ a+1 ≤ 274 by omega, show ¬ a+1 ≤ 390 by omega, show ¬ a+1 ≤ 449 by omega,
      show ¬ a+1 ≤ 486 by omega, show ¬ a+1 ≤ 514 by omega, show ¬ a+1 ≤ 520 by omega,
      show ¬ a < 28 by omega, show ¬ a < 62 by omega, show ¬ a < 158 by omega,
      show ¬ a < 390 by omega, show ¬ a < 486 by omega, if_false, decide_false,
      Bool.and_false, Bool.or_false]

theorem star_sign (w x : ℕ) (hw : 1 ≤ w) (hx : 1 ≤ x) :
    sstar w x = if refBlock ((x-1)/(2*w)) then 1 else -1 := by
  unfold sstar sg ck
  rw [show x+(2*w-1) = (x-1)+2*w by omega, Nat.add_div_right _ (by omega : 0 < 2*w), coarse]

theorem cut_identity (w : ℕ) (hw : 1 ≤ w) (d : ℕ → Bool) :
    Qd (nn w) (fun x => sstar w x * (1-2*mark d x)) - Qd (nn w) (sstar w) = -2 * signedCut w d := by
  unfold Qd signedCut arcs
  rw [sum_filter, sum_product, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro x hx
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro y hy
  have hx' := (mem_Icc.mp hx).1
  have hy' := (mem_Icc.mp hy).1
  simp only [star_sign w x hw hx', star_sign w y hw hy']
  have e : (1 ≤ 2*(y:ℤ)-x ∧ 2*(y:ℤ)-x ≤ nn w) ↔ (x+1 ≤ 2*y ∧ 2*y ≤ x+nn w) := by omega
  unfold rdI mark
  simp only [e]
  by_cases hp : x+1 ≤ 2*y ∧ 2*y ≤ x+nn w
  · simp only [if_pos hp]
    cases d x <;> cases d y <;> cases refBlock ((x-1)/(2*w)) <;> cases refBlock ((y-1)/(2*w)) <;> decide
  · simp only [if_neg hp, zero_mul, sub_self, mul_zero]

theorem mark_sum (n : ℕ) (d : ℕ → Bool) : ∑ x ∈ Icc 1 n, mark d x = (mass n d : ℤ) := by
  unfold mass mark
  rw [card_filter]
  push_cast
  apply sum_congr rfl
  intro x _
  cases d x <;> rfl

theorem mass_complement (n : ℕ) (d : ℕ → Bool) : mass n (fun x => !d x) = n-mass n d := by
  have h : (Icc 1 n).filter (fun x => (!d x) = true) = (Icc 1 n).filter (fun x => ¬ d x = true) := by
    ext x
    cases e : d x <;> simp [e]
  unfold mass
  rw [h]
  have he := Finset.card_filter_add_card_filter_not (s := Icc 1 n) (p := fun x => d x = true)
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at he
  omega

theorem cut_complement (w : ℕ) (d : ℕ → Bool) : signedCut w (fun x => !d x) = signedCut w d := by
  unfold signedCut
  simp

theorem bound (r4 : RegionLB G8 (2/5) (9/20)) (r5 : RegionLB G8 (9/20) (1/2)) :
    OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1.H2 := by
  obtain ⟨CB, hCB⟩ := bathOK8
  obtain ⟨CP, hCP⟩ := pairOK8
  let A : ℝ := 2*(G8.N:ℝ)*CB + 4*CP
  let B : ℝ := max A 0
  have hB : 0 ≤ B := le_max_right _ _
  have estimate (w : ℕ) (hw : 1 ≤ w) (d : ℕ → Bool)
      (hlo : 2*nn w ≤ 5*mass (nn w) d) (hhi : 2*mass (nn w) d ≤ nn w) :
      (signedCut w d : ℝ) ≤ B*nn w := by
    have hs : IsInd (mark d) := by intro x; cases e : d x <;> simp [mark,e]
    have hn : (0:ℝ) < nn w := by exact_mod_cast (by unfold nn; omega : 0 < nn w)
    have hm1 : (2/5:ℝ) ≤ msum w (mark d) := by
      unfold msum
      rw [mark_sum, le_div_iff₀ hn]
      have h : 2*(nn w:ℝ) ≤ 5*(mass (nn w) d:ℝ) := by exact_mod_cast hlo
      push_cast
      linarith
    have hm2 : msum w (mark d) ≤ (1/2:ℝ) := by
      unfold msum
      rw [mark_sum, div_le_iff₀ hn]
      have : 2*(mass (nn w) d : ℝ) ≤ nn w := by exact_mod_cast hhi
      push_cast
      linarith
    have hL : 0 ≤ G8.Lval (G8.yv w (mark d)) := by
      rcases le_or_gt (msum w (mark d)) (9/20) with h|h
      · exact lval_nonneg G8 Pair.G8_WF (2/5) (9/20) r4 w hw _ hs (by push_cast; linarith) (by push_cast; linarith)
      · exact lval_nonneg G8 Pair.G8_WF (9/20) (1/2) r5 w hw _ hs (by push_cast; linarith) (by push_cast; linarith)
    have hlin : ∑ i ∈ range G8.N, (2*(nn w:ℝ)^2 * ((G8.ai i:ℝ) * G8.yv w (mark d) i +
        (G8.bi i:ℝ) * G8.yv w (mark d) i ^ 2) - CB*w) ≤
        ((∑ x ∈ Icc 1 (nn w), H2 w x * mark d x : ℤ) : ℝ) := by
      rw [← Grid.cells_sum G8 Pair.G8_WF w (fun x => H2 w x * mark d x), Int.cast_sum]
      exact sum_le_sum fun i hi => hCB w hw _ hs i (mem_range.mp hi)
    rw [sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul] at hlin
    have hex := expansion w (mark d)
    have hid := cut_identity w hw d
    have he : -(2:ℝ)*(signedCut w d:ℝ) = 2*((∑ x ∈ Icc 1 (nn w), H2 w x * mark d x : ℤ):ℝ) +
        4*(Qd (nn w) (fun x => sstar w x * mark d x) : ℝ) := by
      exact_mod_cast (by omega : -(2:ℤ)*signedCut w d = 2*(∑ x ∈ Icc 1 (nn w), H2 w x * mark d x) +
          4*Qd (nn w) (fun x => sstar w x * mark d x))
    have hprod := mul_nonneg (sq_nonneg (nn w:ℝ)) hL
    unfold Grid.Lval at hprod
    have hpair := hCP w hw _ hs
    have hsmall : (signedCut w d:ℝ) ≤ B*w := by
      have hAB := mul_le_mul_of_nonneg_right (le_max_left A 0) (Nat.cast_nonneg w : (0:ℝ) ≤ w)
      change A*(w:ℝ) ≤ B*w at hAB
      dsimp [A] at hAB
      have hBw := mul_nonneg hB (Nat.cast_nonneg w : (0:ℝ) ≤ w)
      nlinarith only [hlin,hpair,hprod,he,hAB,hBw]
    apply le_trans hsmall (mul_le_mul_of_nonneg_left _ hB)
    exact_mod_cast (by unfold nn; omega : w ≤ nn w)
  refine ⟨B,hB,?_⟩
  intro w hw d
  change 2*nn w ≤ 5*min (mass (nn w) d) (nn w-mass (nn w) d) → (signedCut w d : ℝ) ≤ B*nn w
  intro hfar
  by_cases hm : 2*mass (nn w) d ≤ nn w
  · exact estimate w hw d (by omega) hm
  · rw [← cut_complement w d]
    apply estimate w hw (fun x => !d x) <;> rw [mass_complement] <;> omega

end Erdos1186Ex.FarCut
end

namespace Erdos1186Night2

open Finset
def dotL : List ℤ → List ℤ → ℤ
  | a :: as, b :: bs => a * b + dotL as bs
  | _, _ => 0

theorem dotL_comm : ∀ a b : List ℤ, dotL a b = dotL b a
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
      simp only [dotL]
      rw [dotL_comm as bs, mul_comm]

theorem dotL_eq_sum : ∀ (a b : List ℤ) (n : ℕ), a.length ≤ n →
    dotL a b = ∑ k ∈ range n, a.getD k 0 * b.getD k 0
  | [], b, n, _ => by
      cases b <;> simp [dotL]
  | x :: as, b, n, h => by
      cases n with
      | zero => simp at h
      | succ m =>
        cases b with
        | nil => simp [dotL]
        | cons y bs =>
          have ih := dotL_eq_sum as bs m (by simpa using h)
          rw [Finset.sum_range_succ']
          simp [dotL, ih]
          ring
theorem psd_of_dom (L : ℕ) (E : ℕ → ℕ → ℝ) (hsym : ∀ i j, E i j = E j i)
    (hdom : ∀ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, |E i j| ≤ 2 * E i i) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, E i j * x i * x j := by
  have key : ∀ i j, 0 ≤ E i j * x i * x j + |E i j| / 2 * (x i ^ 2 + x j ^ 2)
      - (if i = j then (E i i + |E i i|) * x i ^ 2 else 0) := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
      ring_nf
      exact le_refl _
    · simp only [h, if_false, sub_zero]
      rcases abs_cases (E i j) with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1]
        nlinarith [sq_nonneg (x i + x j), abs_nonneg (E i j)]
      · rw [h1]
        have := abs_nonneg (E i j)
        rw [h1] at this
        nlinarith [sq_nonneg (x i - x j)]
  have h1 : 0 ≤ ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (E i j * x i * x j + |E i j| / 2 * (x i ^ 2 + x j ^ 2)
      - (if i = j then (E i i + |E i i|) * x i ^ 2 else 0)) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => key i j
  
  have hA : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, |E i j| / 2 * x i ^ 2 =
      ∑ i ∈ Icc 1 L, (∑ j ∈ Icc 1 L, |E i j|) / 2 * x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, ← Finset.sum_div]
  have hB : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, |E i j| / 2 * x j ^ 2 =
      ∑ i ∈ Icc 1 L, (∑ j ∈ Icc 1 L, |E i j|) / 2 * x i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, ← Finset.sum_div]
    congr 2
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym]
  have hC : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (if i = j then (E i i + |E i i|) * x i ^ 2 else 0) =
      ∑ i ∈ Icc 1 L, (E i i + |E i i|) * x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_ite_eq]
    simp [hi]
  have hsplit : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (E i j * x i * x j + |E i j| / 2 * (x i ^ 2 + x j ^ 2)
      - (if i = j then (E i i + |E i i|) * x i ^ 2 else 0)) =
      (∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, E i j * x i * x j)
      + (∑ i ∈ Icc 1 L, (∑ j ∈ Icc 1 L, |E i j|) / 2 * x i ^ 2) * 2
      - ∑ i ∈ Icc 1 L, (E i i + |E i i|) * x i ^ 2 := by
    have e1 : ∀ i j, E i j * x i * x j + |E i j| / 2 * (x i ^ 2 + x j ^ 2)
        - (if i = j then (E i i + |E i i|) * x i ^ 2 else 0)
        = E i j * x i * x j + (|E i j| / 2 * x i ^ 2 + |E i j| / 2 * x j ^ 2)
          - (if i = j then (E i i + |E i i|) * x i ^ 2 else 0) := fun i j => by ring
    simp only [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib, hA, hB, hC]
    ring
  rw [hsplit] at h1
  have h2 : ∑ i ∈ Icc 1 L, (∑ j ∈ Icc 1 L, |E i j|) / 2 * x i ^ 2 ≤
      ∑ i ∈ Icc 1 L, E i i * x i ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have := hdom i hi
    have hx := sq_nonneg (x i)
    nlinarith
  have h3 : 0 ≤ ∑ i ∈ Icc 1 L, (|E i i| - E i i) * x i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (by linarith [le_abs_self (E i i)]) (sq_nonneg _)
  have h4 : ∑ i ∈ Icc 1 L, (E i i + |E i i|) * x i ^ 2 =
      ∑ i ∈ Icc 1 L, E i i * x i ^ 2 + ∑ i ∈ Icc 1 L, |E i i| * x i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h5 : ∑ i ∈ Icc 1 L, (|E i i| - E i i) * x i ^ 2 =
      ∑ i ∈ Icc 1 L, |E i i| * x i ^ 2 - ∑ i ∈ Icc 1 L, E i i * x i ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

theorem gram_nonneg (L n : ℕ) (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (∑ k ∈ range n, c i k * c j k) * x i * x j := by
  have e : ∀ i j, (∑ k ∈ range n, c i k * c j k) * x i * x j =
      ∑ k ∈ range n, (c i k * x i) * (c j k * x j) := by
    intro i j
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (∑ k ∈ range n, c i k * c j k) * x i * x j =
      ∑ k ∈ range n, (∑ i ∈ Icc 1 L, c i k * x i) ^ 2 := by
    simp only [e, sq, Finset.sum_mul_sum]
    calc _ = ∑ i ∈ Icc 1 L, ∑ k ∈ range n, ∑ j ∈ Icc 1 L, (c i k * x i) * (c j k * x j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [this]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

end Erdos1186Night2

section

namespace Erdos1186Ex

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

def dec (W r j : ℕ) : ℤ := (((r / 2 ^ (W * j)) % 2 ^ W : ℕ) : ℤ) - ((2 ^ (W - 1) : ℕ) : ℤ)

def tb (W : ℕ) (rows : List ℕ) (i j : ℕ) : ℤ := dec W (rows.getD i 0) j

def vc (W : ℕ) (v : ℕ) (i : ℕ) : ℤ := dec W v i

theorem sum_Icc_one {β : Type*} [AddCommMonoid β] (L : ℕ) (f : ℕ → β) :
    ∑ a ∈ Icc 1 L, f a = ∑ t ∈ range L, f (1 + t) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]

noncomputable def evq (n : ℕ) (c0 : ℤ) (l : ℕ → ℤ) (q : ℕ → ℕ → ℤ) (y : ℕ → ℝ) : ℝ :=
  (c0 : ℝ) + ∑ i ∈ range n, (l i : ℝ) * y i + ∑ i ∈ range n, ∑ j ∈ range n, (q i j : ℝ) * (y i * y j)

theorem evq_add (n : ℕ) (c0 c0' : ℤ) (l l' : ℕ → ℤ) (q q' : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    evq n (c0 + c0') (fun i => l i + l' i) (fun i j => q i j + q' i j) y
      = evq n c0 l q y + evq n c0' l' q' y := by
  unfold evq
  push_cast
  simp only [add_mul, Finset.sum_add_distrib]
  ring

theorem evq_neg (n : ℕ) (c0 : ℤ) (l : ℕ → ℤ) (q : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    evq n (-c0) (fun i => -l i) (fun i j => -q i j) y = -evq n c0 l q y := by
  unfold evq
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

theorem evq_smul (n : ℕ) (u c0 : ℤ) (l : ℕ → ℤ) (q : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    (u : ℝ) * evq n c0 l q y = evq n (u * c0) (fun i => u * l i) (fun i j => u * q i j) y := by
  unfold evq
  have h1 : (u : ℝ) * ∑ i ∈ range n, (l i : ℝ) * y i = ∑ i ∈ range n, ((u * l i : ℤ) : ℝ) * y i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  have h2 : (u : ℝ) * ∑ i ∈ range n, ∑ j ∈ range n, (q i j : ℝ) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, ((u * q i j : ℤ) : ℝ) * (y i * y j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [mul_add, mul_add, h1, h2]
  push_cast
  ring

theorem sum_sym (n : ℕ) (q q' : ℕ → ℕ → ℤ) (y : ℕ → ℝ)
    (hq : ∀ i < n, ∀ j < n, q i j + q j i = q' i j + q' j i) :
    ∑ i ∈ range n, ∑ j ∈ range n, (q i j : ℝ) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, (q' i j : ℝ) * (y i * y j) := by
  have e1 : ∑ i ∈ range n, ∑ j ∈ range n, (q i j : ℝ) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, (q j i : ℝ) * (y i * y j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have e2 : ∑ i ∈ range n, ∑ j ∈ range n, (q' i j : ℝ) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, (q' j i : ℝ) * (y i * y j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have e3 : ∑ i ∈ range n, ∑ j ∈ range n, ((q i j : ℝ) + (q j i : ℝ)) * (y i * y j)
      = ∑ i ∈ range n, ∑ j ∈ range n, ((q' i j : ℝ) + (q' j i : ℝ)) * (y i * y j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have := hq i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
    have : ((q i j : ℝ) + (q j i : ℝ)) = ((q' i j : ℝ) + (q' j i : ℝ)) := by exact_mod_cast this
    rw [this]
  simp only [add_mul, Finset.sum_add_distrib] at e3
  linarith

theorem evq_congr (n : ℕ) (c0 c0' : ℤ) (l l' : ℕ → ℤ) (q q' : ℕ → ℕ → ℤ) (y : ℕ → ℝ)
    (h0 : c0 = c0') (hl : ∀ i < n, l i = l' i) (hq : ∀ i < n, ∀ j < n, q i j + q j i = q' i j + q' j i) :
    evq n c0 l q y = evq n c0' l' q' y := by
  unfold evq
  rw [h0, sum_sym n q q' y hq]
  have : ∑ i ∈ range n, (l i : ℝ) * y i = ∑ i ∈ range n, (l' i : ℝ) * y i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hl i (Finset.mem_range.mp hi)]
  rw [this]

theorem sum_Icc_split {β : Type*} [AddCommMonoid β] (n : ℕ) (F : ℕ → β) :
    ∑ a ∈ Icc 1 (n + 1), F a = F 1 + ∑ i ∈ range n, F (i + 2) := by
  rw [sum_Icc_one, Finset.sum_range_succ', add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show 1 + (i + 1) = i + 2 by omega]

theorem gram_ev (n : ℕ) (M : ℕ → ℕ → ℤ) (x y : ℕ → ℝ) (h1 : x 1 = 1) (h2 : ∀ i, x (i + 2) = y i) :
    ∑ a ∈ Icc 1 (n + 1), ∑ b ∈ Icc 1 (n + 1), (M a b : ℝ) * x a * x b =
      evq n (M 1 1) (fun i => M 1 (i + 2) + M (i + 2) 1) (fun i j => M (i + 2) (j + 2)) y := by
  have hs : ∀ a : ℕ, ∑ b ∈ Icc 1 (n + 1), (M a b : ℝ) * x a * x b
      = (M a 1 : ℝ) * x a * x 1 + ∑ j ∈ range n, (M a (j + 2) : ℝ) * x a * x (j + 2) :=
    fun a => sum_Icc_split n (fun b => (M a b : ℝ) * x a * x b)
  simp only [hs]
  rw [sum_Icc_split n (fun a => (M a 1 : ℝ) * x a * x 1 + ∑ j ∈ range n, (M a (j + 2) : ℝ) * x a * x (j + 2))]
  simp only [h1, h2]
  unfold evq
  push_cast
  simp only [Finset.sum_add_distrib, add_mul, mul_one, mul_assoc]
  ring

def A4v (G : Grid) (i j : ℕ) : ℕ :=
  if 1 ≤ 2 * ((G.lo j : ℤ) + 1) - G.hi i - 1 ∧ 2 * (G.hi j : ℤ) - ((G.lo i : ℤ) + 1) - 1 ≤ 1094 then
    4 * G.len i * G.len j
  else if 2 * (G.hi j : ℤ) - ((G.lo i : ℤ) + 1) - 1 ≤ -2 ∨ 1097 ≤ 2 * ((G.lo j : ℤ) + 1) - G.hi i - 1 then 0
  else G.A4 i j

theorem A4v_eq (G : Grid) (i j : ℕ) : A4v G i j = G.A4 i j := by
  unfold A4v
  split_ifs with h1 h2
  · unfold Grid.A4
    have hk : ∀ p ∈ Ioc (G.lo i) (G.hi i), ∀ q ∈ Ioc (G.lo j) (G.hi j), K4 1096 p q = 4 := by
      intro p hp q hq
      rw [Finset.mem_Ioc] at hp hq
      unfold K4
      rw [if_pos]
      push_cast
      omega
    rw [Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (hk p hp))]
    simp only [Finset.sum_const, Nat.card_Ioc, smul_eq_mul]
    unfold Grid.len
    ring
  · unfold Grid.A4
    have hk : ∀ p ∈ Ioc (G.lo i) (G.hi i), ∀ q ∈ Ioc (G.lo j) (G.hi j), K4 1096 p q = 0 := by
      intro p hp q hq
      rw [Finset.mem_Ioc] at hp hq
      unfold K4
      rw [if_neg, if_neg, if_neg]
      · push_cast
        omega
      · push_cast
        omega
      · push_cast
        omega
    rw [Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (hk p hp))]
    simp
  · rfl

def Qn : ℤ := 1099511627776

def Dz : ℤ := Qn * 360364800

def sgnP (G : Grid) (i j : ℕ) : ℤ := if G.sgn i * G.sgn j = 1 then 1 else -1

def Kp (G : Grid) (θ : ℤ) (i j : ℕ) : ℤ := 300 * (Qn - θ) * (G.len i : ℤ) * (G.len j : ℤ)

def cp (G : Grid) (θ : ℤ) (i j : ℕ) : ℤ :=
  if G.sgn i * G.sgn j = 1 then 75 * (Qn - θ) * (4 * (G.len i : ℤ) * (G.len j : ℤ) - (A4v G i j : ℤ))
  else 75 * θ * (A4v G i j : ℤ)

theorem pterm_scaled (G : Grid) (i j : ℕ) (θ : ℤ) (h0 : 0 ≤ θ) (h1 : θ ≤ Qn) (yi yj : ℝ) :
    ((sgnP G i j * Kp G θ i j : ℤ) : ℝ) * (yi * yj) - (cp G θ i j : ℝ)
      ≤ (Dz : ℝ) * G.pterm i j yi yj := by
  have hA := A4v_eq G i j
  unfold Grid.pterm sgnP Kp cp Grid.wt
  rw [hA]
  simp only [Qn, Dz] at *
  have hθ0 : (0 : ℝ) ≤ (θ : ℝ) := by exact_mod_cast h0
  have hθ1 : (θ : ℝ) ≤ 1099511627776 := by exact_mod_cast h1
  push_cast
  set a : ℝ := (G.len i : ℝ) with ha
  set b : ℝ := (G.len j : ℝ) with hb
  set A : ℝ := (G.A4 i j : ℝ) with hAd
  by_cases hs : G.sgn i * G.sgn j = 1
  · simp only [hs, if_true]
    set u : ℝ := a / 1096 * (b / 1096) * yi * yj - (a / 1096 * (b / 1096) - A / (4 * 1096 ^ 2)) with hu
    have hm1 : u ≤ max 0 u := le_max_right _ _
    have hm2 : 0 ≤ max 0 u := le_max_left _ _
    have key : (1099511627776 * 360364800 : ℝ) * ((1 - (θ : ℝ) / 1099511627776) * u)
        = 1 * (300 * (1099511627776 - (θ : ℝ)) * a * b) * (yi * yj)
          - 75 * (1099511627776 - (θ : ℝ)) * (4 * a * b - A) := by
      rw [hu]
      field_simp
      ring
    have hq : 0 ≤ 1 - (θ : ℝ) / 1099511627776 := by
      rw [sub_nonneg, div_le_one (by norm_num)]; exact hθ1
    have ht : 0 ≤ (θ : ℝ) / 1099511627776 := by positivity
    have hle : (1 - (θ : ℝ) / 1099511627776) * u ≤ max 0 u := by
      nlinarith [mul_nonneg hq (sub_nonneg.mpr hm1), mul_nonneg ht hm2]
    have hD : (0 : ℝ) ≤ 1099511627776 * 360364800 := by norm_num
    have hh := mul_le_mul_of_nonneg_left hle hD
    rw [← key]
    linarith
  · simp only [hs, if_false]
    set P : ℝ := a / 1096 * (b / 1096) * yi * yj with hP
    set Ain : ℝ := A / (4 * 1096 ^ 2) with hAin
    have hm1 : -Ain ≤ max (-Ain) (-P) := le_max_left _ _
    have hm2 : -P ≤ max (-Ain) (-P) := le_max_right _ _
    have key : (1099511627776 * 360364800 : ℝ) * ((θ : ℝ) / 1099511627776 * (-Ain)
          + (1 - (θ : ℝ) / 1099511627776) * (-P))
        = (-1 * (300 * (1099511627776 - (θ : ℝ)) * a * b)) * (yi * yj) - 75 * (θ : ℝ) * A := by
      rw [hP, hAin]
      field_simp
      ring
    have hq : 0 ≤ 1 - (θ : ℝ) / 1099511627776 := by
      rw [sub_nonneg, div_le_one (by norm_num)]; exact hθ1
    have ht : 0 ≤ (θ : ℝ) / 1099511627776 := by positivity
    have hle : (θ : ℝ) / 1099511627776 * (-Ain) + (1 - (θ : ℝ) / 1099511627776) * (-P)
        ≤ max (-Ain) (-P) := by
      nlinarith [mul_nonneg ht (sub_nonneg.mpr hm1), mul_nonneg hq (sub_nonneg.mpr hm2)]
    have hD : (0 : ℝ) ≤ 1099511627776 * 360364800 := by norm_num
    have hh := mul_le_mul_of_nonneg_left hle hD
    rw [← key]
    linarith

end Erdos1186Ex

end

section

namespace Erdos1186Ex

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

noncomputable def afn (n : ℕ) (c : ℤ) (e : ℕ → ℤ) (y : ℕ → ℝ) : ℝ := (c : ℝ) + ∑ k ∈ range n, (e k : ℝ) * y k

theorem afn_mul (n : ℕ) (c d : ℤ) (e f : ℕ → ℤ) (y : ℕ → ℝ) :
    afn n c e y * afn n d f y = evq n (c * d) (fun i => c * f i + d * e i) (fun i j => e i * f j) y := by
  unfold afn evq
  have h1 : ∑ i ∈ range n, (((c * f i + d * e i : ℤ) : ℝ)) * y i
      = (c : ℝ) * ∑ i ∈ range n, (f i : ℝ) * y i + (d : ℝ) * ∑ i ∈ range n, (e i : ℝ) * y i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  have h2 : (∑ i ∈ range n, (e i : ℝ) * y i) * ∑ j ∈ range n, (f j : ℝ) * y j
      = ∑ i ∈ range n, ∑ j ∈ range n, ((e i * f j : ℤ) : ℝ) * (y i * y j) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [h1, ← h2]
  push_cast
  ring

theorem sum2_aff (n : ℕ) (u t u' t' : ℤ) (C : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, (C i j : ℝ) * (((u : ℝ) + t * y i) * ((u' : ℝ) + t' * y j))
      = evq n (u * u' * ∑ i ∈ range n, ∑ j ∈ range n, C i j)
          (fun a => u * t' * (∑ i ∈ range n, C i a) + t * u' * (∑ j ∈ range n, C a j))
          (fun i j => t * t' * C i j) y := by
  unfold evq
  have key : ∀ i j, (C i j : ℝ) * (((u : ℝ) + t * y i) * ((u' : ℝ) + t' * y j))
      = ((u * u' : ℤ) : ℝ) * (C i j : ℝ) + ((u * t' : ℤ) : ℝ) * (C i j : ℝ) * y j
        + ((t * u' : ℤ) : ℝ) * (C i j : ℝ) * y i + ((t * t' * C i j : ℤ) : ℝ) * (y i * y j) := by
    intro i j
    push_cast
    ring
  simp only [key, Finset.sum_add_distrib]
  have e1 : ∑ i ∈ range n, ∑ j ∈ range n, ((u * u' : ℤ) : ℝ) * (C i j : ℝ)
      = ((u * u' * ∑ i ∈ range n, ∑ j ∈ range n, C i j : ℤ) : ℝ) := by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have e2 : ∑ i ∈ range n, ∑ j ∈ range n, ((u * t' : ℤ) : ℝ) * (C i j : ℝ) * y j
      = ∑ a ∈ range n, ((u * t' * ∑ i ∈ range n, C i a : ℤ) : ℝ) * y a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  have e3 : ∑ i ∈ range n, ∑ j ∈ range n, ((t * u' : ℤ) : ℝ) * (C i j : ℝ) * y i
      = ∑ a ∈ range n, ((t * u' * ∑ j ∈ range n, C a j : ℤ) : ℝ) * y a := by
    apply Finset.sum_congr rfl
    intro a _
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [e1, e2, e3]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib]
  ring

structure FD where
  n : ℕ
  Yv : ℕ → ℤ
  Ov : ℕ → ℤ
  A1 : ℕ → ℤ
  A2 : ℕ → ℤ
  A3 : ℕ → ℤ
  A4 : ℕ → ℤ
  YY : ℕ → ℕ → ℤ
  OO : ℕ → ℕ → ℤ
  YO : ℕ → ℕ → ℤ
  pp : ℤ
  rr : ℤ
  ss : ℤ
  om : ℕ → ℤ
  Lo : ℤ
  Hi : ℤ

def Rr : ℤ := 21920
def Uu : ℤ := 21920 * 21920

namespace FD

noncomputable def FSr (d : FD) (m lo hi : ℝ) (y : ℕ → ℝ) : ℝ :=
  (∑ i ∈ range d.n, ((d.Yv i : ℝ) * y i + (d.Ov i : ℝ) * (1 - y i)))
  + ((d.pp : ℝ) * (m - lo) + (d.rr : ℝ) * (hi - m))
  + ∑ i ∈ range d.n, ∑ j ∈ range d.n, ((d.YY i j : ℝ) * (y i * y j)
      + (d.OO i j : ℝ) * ((1 - y i) * (1 - y j)) + (d.YO i j : ℝ) * (y i * (1 - y j)))
  + ∑ i ∈ range d.n, ((d.A1 i : ℝ) * (y i * (m - lo)) + (d.A2 i : ℝ) * ((1 - y i) * (m - lo))
      + (d.A3 i : ℝ) * (y i * (hi - m)) + (d.A4 i : ℝ) * ((1 - y i) * (hi - m)))
  + (d.ss : ℝ) * ((m - lo) * (hi - m))

structure Nonneg (d : FD) : Prop where
  Yv : ∀ i < d.n, 0 ≤ d.Yv i
  Ov : ∀ i < d.n, 0 ≤ d.Ov i
  A1 : ∀ i < d.n, 0 ≤ d.A1 i
  A2 : ∀ i < d.n, 0 ≤ d.A2 i
  A3 : ∀ i < d.n, 0 ≤ d.A3 i
  A4 : ∀ i < d.n, 0 ≤ d.A4 i
  YY : ∀ i < d.n, ∀ j < d.n, 0 ≤ d.YY i j
  OO : ∀ i < d.n, ∀ j < d.n, 0 ≤ d.OO i j
  YO : ∀ i < d.n, ∀ j < d.n, 0 ≤ d.YO i j
  pp : 0 ≤ d.pp
  rr : 0 ≤ d.rr
  ss : 0 ≤ d.ss

theorem FSr_nonneg (d : FD) (h : d.Nonneg) (m lo hi : ℝ) (y : ℕ → ℝ) (hy : ∀ i < d.n, 0 ≤ y i ∧ y i ≤ 1)
    (hl : lo ≤ m) (hh : m ≤ hi) : 0 ≤ d.FSr m lo hi y := by
  have ml : 0 ≤ m - lo := by linarith
  have hm : 0 ≤ hi - m := by linarith
  have c : ∀ z : ℤ, 0 ≤ z → (0 : ℝ) ≤ (z : ℝ) := fun z hz => by exact_mod_cast hz
  unfold FSr
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_) ?_
  · refine Finset.sum_nonneg fun i hi' => ?_
    have hi'' := Finset.mem_range.mp hi'
    obtain ⟨h0, h1⟩ := hy i hi''
    exact add_nonneg (mul_nonneg (c _ (h.Yv i hi'')) h0) (mul_nonneg (c _ (h.Ov i hi'')) (by linarith))
  · exact add_nonneg (mul_nonneg (c _ h.pp) ml) (mul_nonneg (c _ h.rr) hm)
  · refine Finset.sum_nonneg fun i hi' => Finset.sum_nonneg fun j hj' => ?_
    have hi'' := Finset.mem_range.mp hi'
    have hj'' := Finset.mem_range.mp hj'
    obtain ⟨a0, a1⟩ := hy i hi''
    obtain ⟨b0, b1⟩ := hy j hj''
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact mul_nonneg (c _ (h.YY i hi'' j hj'')) (mul_nonneg a0 b0)
    · exact mul_nonneg (c _ (h.OO i hi'' j hj'')) (mul_nonneg (by linarith) (by linarith))
    · exact mul_nonneg (c _ (h.YO i hi'' j hj'')) (mul_nonneg a0 (by linarith))
  · refine Finset.sum_nonneg fun i hi' => ?_
    have hi'' := Finset.mem_range.mp hi'
    obtain ⟨a0, a1⟩ := hy i hi''
    refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
    · exact mul_nonneg (c _ (h.A1 i hi'')) (mul_nonneg a0 ml)
    · exact mul_nonneg (c _ (h.A2 i hi'')) (mul_nonneg (by linarith) ml)
    · exact mul_nonneg (c _ (h.A3 i hi'')) (mul_nonneg a0 hm)
    · exact mul_nonneg (c _ (h.A4 i hi'')) (mul_nonneg (by linarith) hm)
  · exact mul_nonneg (c _ h.ss) (mul_nonneg ml hm)

def u1 (d : FD) (i : ℕ) : ℤ := d.A1 i - d.A2 i
def u2 (d : FD) (i : ℕ) : ℤ := d.A3 i - d.A4 i
def u10 (d : FD) : ℤ := (∑ i ∈ range d.n, d.A2 i) + d.pp
def u20 (d : FD) : ℤ := (∑ i ∈ range d.n, d.A4 i) + d.rr

def cF (d : FD) : ℤ :=
  Uu * ((∑ i ∈ range d.n, d.Ov i) + ∑ i ∈ range d.n, ∑ j ∈ range d.n, d.OO i j)
    + Rr * (-d.Lo * d.u10 + d.Hi * d.u20) - d.ss * d.Lo * d.Hi

def lF (d : FD) (a : ℕ) : ℤ :=
  Uu * (d.Yv a - d.Ov a - (∑ j ∈ range d.n, d.OO a j) - (∑ i ∈ range d.n, d.OO i a) + ∑ j ∈ range d.n, d.YO a j)
    + Rr * (d.om a * d.u10 - d.Lo * d.u1 a - d.om a * d.u20 + d.Hi * d.u2 a)
    + d.ss * d.om a * (d.Lo + d.Hi)

def qF (d : FD) (i j : ℕ) : ℤ :=
  Uu * (d.YY i j + d.OO i j - d.YO i j) + Rr * d.om j * (d.u1 i - d.u2 i) - d.ss * d.om i * d.om j

theorem evq_zero (n : ℕ) (y : ℕ → ℝ) : evq n 0 (fun _ => 0) (fun _ _ => 0) y = 0 := by
  simp [evq]

theorem evq_afn (n : ℕ) (c : ℤ) (e : ℕ → ℤ) (y : ℕ → ℝ) :
    afn n c e y = evq n c e (fun _ _ => 0) y := by
  simp [afn, evq]

theorem FSr_evq (d : FD) (m lo hi : ℝ) (y : ℕ → ℝ)
    (hm : (Rr : ℝ) * m = ∑ k ∈ range d.n, (d.om k : ℝ) * y k)
    (hlo : (Rr : ℝ) * lo = d.Lo) (hhi : (Rr : ℝ) * hi = d.Hi) :
    (Uu : ℝ) * d.FSr m lo hi y = evq d.n d.cF d.lF d.qF y := by
  have hUR : (Uu : ℝ) = (Rr : ℝ) * (Rr : ℝ) := by norm_num [Uu, Rr]
  have hml : (Rr : ℝ) * (m - lo) = afn d.n (-d.Lo) d.om y := by
    unfold afn
    push_cast
    rw [mul_sub, hm, hlo]
    ring
  have hhm : (Rr : ℝ) * (hi - m) = afn d.n d.Hi (fun k => - d.om k) y := by
    unfold afn
    push_cast
    rw [mul_sub, hm, hhi]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring
  
  have g1 : ∑ i ∈ range d.n, ((d.Yv i : ℝ) * y i + (d.Ov i : ℝ) * (1 - y i))
      = evq d.n (∑ i ∈ range d.n, d.Ov i) (fun a => d.Yv a - d.Ov a) (fun _ _ => 0) y := by
    unfold evq
    simp only [Int.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]
    have : ∀ i, (d.Yv i : ℝ) * y i + (d.Ov i : ℝ) * (1 - y i)
        = (d.Ov i : ℝ) + ((d.Yv i - d.Ov i : ℤ) : ℝ) * y i := by
      intro i
      push_cast
      ring
    simp only [this, Finset.sum_add_distrib]
    push_cast
    rfl
  have hGml : afn d.n d.u10 d.u1 y
      = (d.pp : ℝ) + ∑ i ∈ range d.n, ((d.A1 i : ℝ) * y i + (d.A2 i : ℝ) * (1 - y i)) := by
    unfold afn FD.u10 FD.u1
    have : ∀ i, (d.A1 i : ℝ) * y i + (d.A2 i : ℝ) * (1 - y i)
        = (d.A2 i : ℝ) + ((d.A1 i - d.A2 i : ℤ) : ℝ) * y i := by
      intro i
      push_cast
      ring
    simp only [this, Finset.sum_add_distrib]
    push_cast
    ring
  have hGhm : afn d.n d.u20 d.u2 y
      = (d.rr : ℝ) + ∑ i ∈ range d.n, ((d.A3 i : ℝ) * y i + (d.A4 i : ℝ) * (1 - y i)) := by
    unfold afn FD.u20 FD.u2
    have : ∀ i, (d.A3 i : ℝ) * y i + (d.A4 i : ℝ) * (1 - y i)
        = (d.A4 i : ℝ) + ((d.A3 i - d.A4 i : ℤ) : ℝ) * y i := by
      intro i
      push_cast
      ring
    simp only [this, Finset.sum_add_distrib]
    push_cast
    ring
  have g2 : (d.pp : ℝ) * (m - lo) + (d.rr : ℝ) * (hi - m)
      + ∑ i ∈ range d.n, ((d.A1 i : ℝ) * (y i * (m - lo)) + (d.A2 i : ℝ) * ((1 - y i) * (m - lo))
        + (d.A3 i : ℝ) * (y i * (hi - m)) + (d.A4 i : ℝ) * ((1 - y i) * (hi - m)))
      = afn d.n d.u10 d.u1 y * (m - lo) + afn d.n d.u20 d.u2 y * (hi - m) := by
    rw [hGml, hGhm]
    have e : ∀ i, (d.A1 i : ℝ) * (y i * (m - lo)) + (d.A2 i : ℝ) * ((1 - y i) * (m - lo))
        + (d.A3 i : ℝ) * (y i * (hi - m)) + (d.A4 i : ℝ) * ((1 - y i) * (hi - m))
        = ((d.A1 i : ℝ) * y i + (d.A2 i : ℝ) * (1 - y i)) * (m - lo)
          + ((d.A3 i : ℝ) * y i + (d.A4 i : ℝ) * (1 - y i)) * (hi - m) := by
      intro i
      ring
    simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  have g3 : ∑ i ∈ range d.n, ∑ j ∈ range d.n, ((d.YY i j : ℝ) * (y i * y j)
      + (d.OO i j : ℝ) * ((1 - y i) * (1 - y j)) + (d.YO i j : ℝ) * (y i * (1 - y j)))
      = evq d.n (0 * 0 * ∑ i ∈ range d.n, ∑ j ∈ range d.n, d.YY i j)
          (fun a => 0 * 1 * (∑ i ∈ range d.n, d.YY i a) + 1 * 0 * (∑ j ∈ range d.n, d.YY a j))
          (fun i j => 1 * 1 * d.YY i j) y
        + evq d.n (1 * 1 * ∑ i ∈ range d.n, ∑ j ∈ range d.n, d.OO i j)
          (fun a => 1 * (-1) * (∑ i ∈ range d.n, d.OO i a) + (-1) * 1 * (∑ j ∈ range d.n, d.OO a j))
          (fun i j => (-1) * (-1) * d.OO i j) y
        + evq d.n (0 * 1 * ∑ i ∈ range d.n, ∑ j ∈ range d.n, d.YO i j)
          (fun a => 0 * (-1) * (∑ i ∈ range d.n, d.YO i a) + 1 * 1 * (∑ j ∈ range d.n, d.YO a j))
          (fun i j => 1 * (-1) * d.YO i j) y := by
    rw [← sum2_aff d.n 0 1 0 1 d.YY y, ← sum2_aff d.n 1 (-1) 1 (-1) d.OO y,
      ← sum2_aff d.n 0 1 1 (-1) d.YO y]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  have g5 : (d.ss : ℝ) * ((m - lo) * (hi - m)) * (Uu : ℝ)
      = (d.ss : ℝ) * (afn d.n (-d.Lo) d.om y * afn d.n d.Hi (fun k => - d.om k) y) := by
    rw [← hml, ← hhm, hUR]
    ring
  
  have hFS : d.FSr m lo hi y
      = ∑ i ∈ range d.n, ((d.Yv i : ℝ) * y i + (d.Ov i : ℝ) * (1 - y i))
        + ∑ i ∈ range d.n, ∑ j ∈ range d.n, ((d.YY i j : ℝ) * (y i * y j)
          + (d.OO i j : ℝ) * ((1 - y i) * (1 - y j)) + (d.YO i j : ℝ) * (y i * (1 - y j)))
        + (afn d.n d.u10 d.u1 y * (m - lo) + afn d.n d.u20 d.u2 y * (hi - m))
        + (d.ss : ℝ) * ((m - lo) * (hi - m)) := by
    rw [← g2]
    unfold FD.FSr
    ring
  have hG2 : (Uu : ℝ) * (afn d.n d.u10 d.u1 y * (m - lo) + afn d.n d.u20 d.u2 y * (hi - m))
      = (Rr : ℝ) * (afn d.n d.u10 d.u1 y * afn d.n (-d.Lo) d.om y
          + afn d.n d.u20 d.u2 y * afn d.n d.Hi (fun k => - d.om k) y) := by
    rw [← hml, ← hhm, hUR]
    ring
  rw [hFS, mul_add, mul_add, mul_add, hG2, g1, g3, mul_comm (Uu : ℝ) ((d.ss : ℝ) * _), g5,
    afn_mul, afn_mul, afn_mul]
  simp only [mul_add, evq_smul, ← evq_add]
  apply evq_congr
  · unfold FD.cF FD.u10 FD.u20
    ring
  · intro a _
    unfold FD.lF FD.u10 FD.u20 FD.u1 FD.u2
    ring
  · intro i _ j _
    unfold FD.qF FD.u1 FD.u2
    ring

end FD

structure PD where
  G : Grid
  lenz : ℕ → ℤ
  sgz : ℕ → ℤ
  alz : ℕ → ℤ
  btz : ℕ → ℤ
  a4z : ℕ → ℕ → ℤ
  th : ℕ → ℕ → ℤ

namespace PD

def sz (d : PD) (i j : ℕ) : ℤ := if d.sgz i * d.sgz j = 1 then 1 else -1

def Kz (d : PD) (i j : ℕ) : ℤ := 300 * (Qn - d.th i j) * d.lenz i * d.lenz j

def cz (d : PD) (i j : ℕ) : ℤ :=
  if d.sgz i * d.sgz j = 1 then 75 * (Qn - d.th i j) * (4 * d.lenz i * d.lenz j - d.a4z i j)
  else 75 * d.th i j * d.a4z i j

noncomputable def PS (d : PD) (y : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range d.G.N, ((d.alz i : ℝ) * y i + (d.btz i : ℝ) * y i ^ 2)
    + ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((d.sz i j * d.Kz i j : ℤ) : ℝ) * (y i * y j) - (d.cz i j : ℝ))

structure Ok (d : PD) : Prop where
  len : ∀ i < d.G.N, d.lenz i = (d.G.len i : ℤ)
  sg : ∀ i < d.G.N, d.sgz i = d.G.sgn i
  al : ∀ i < d.G.N, d.G.ai i * (Dz : ℚ) = (d.alz i : ℚ)
  bt : ∀ i < d.G.N, d.G.bi i * (Dz : ℚ) = (d.btz i : ℚ)
  a4 : ∀ i < d.G.N, ∀ j < d.G.N, d.a4z i j = (d.G.A4 i j : ℤ)
  th : ∀ i < d.G.N, ∀ j < d.G.N, 0 ≤ d.th i j ∧ d.th i j ≤ Qn

theorem PS_le (d : PD) (h : d.Ok) (y : ℕ → ℝ) : d.PS y ≤ (Dz : ℝ) * d.G.Lval y := by
  unfold PS Grid.Lval
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  apply add_le_add
  · apply le_of_eq
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have ha : (d.G.ai i : ℝ) * (Dz : ℝ) = (d.alz i : ℝ) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) (h.al i hi')
      simpa using this
    have hb : (d.G.bi i : ℝ) * (Dz : ℝ) = (d.btz i : ℝ) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) (h.bt i hi')
      simpa using this
    rw [← ha, ← hb]
    ring
  · apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have key := pterm_scaled d.G i j (d.th i j) (h.th i hi' j hj').1 (h.th i hi' j hj').2 (y i) (y j)
    have e1 : sgnP d.G i j * Kp d.G (d.th i j) i j = d.sz i j * d.Kz i j := by
      unfold sgnP Kp sz Kz
      rw [h.len i hi', h.len j hj', h.sg i hi', h.sg j hj']
    have e2 : cp d.G (d.th i j) i j = d.cz i j := by
      unfold cp cz
      rw [A4v_eq, h.len i hi', h.len j hj', h.sg i hi', h.sg j hj', h.a4 i hi' j hj']
    rw [e1, e2] at key
    exact key

def cP (d : PD) : ℤ := -Uu * ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, d.cz i j
def lP (d : PD) (a : ℕ) : ℤ := Uu * d.alz a
def qP (d : PD) (i j : ℕ) : ℤ := Uu * (d.sz i j * d.Kz i j + if i = j then d.btz i else 0)

theorem PS_evq (d : PD) (y : ℕ → ℝ) : (Uu : ℝ) * d.PS y = evq d.G.N d.cP d.lP d.qP y := by
  have e : d.PS y = evq d.G.N (-∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, d.cz i j) d.alz
      (fun i j => d.sz i j * d.Kz i j + if i = j then d.btz i else 0) y := by
    unfold PS evq
    have hb : ∀ i ∈ range d.G.N, (d.btz i : ℝ) * y i ^ 2
        = ∑ j ∈ range d.G.N, (((if i = j then d.btz i else 0 : ℤ)) : ℝ) * (y i * y j) := by
      intro i hi
      rw [Finset.sum_eq_single_of_mem i hi]
      · simp [sq]
      · intro j _ hji
        simp [Ne.symm hji]
    have hb' : ∑ i ∈ range d.G.N, (d.btz i : ℝ) * y i ^ 2
        = ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((if i = j then d.btz i else 0 : ℤ)) : ℝ) * (y i * y j) :=
      Finset.sum_congr rfl hb
    have hc : ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((d.sz i j * d.Kz i j : ℤ) : ℝ) * (y i * y j) - (d.cz i j : ℝ))
        = ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((d.sz i j * d.Kz i j : ℤ) : ℝ) * (y i * y j))
          - ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (d.cz i j : ℝ) := by
      simp only [Finset.sum_sub_distrib]
    rw [hc, Finset.sum_add_distrib, hb']
    have hq : ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((d.sz i j * d.Kz i j + if i = j then d.btz i else 0 : ℤ)) : ℝ) * (y i * y j)
        = ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((d.sz i j * d.Kz i j : ℤ) : ℝ) * (y i * y j))
          + ∑ i ∈ range d.G.N, ∑ j ∈ range d.G.N, (((if i = j then d.btz i else 0 : ℤ)) : ℝ) * (y i * y j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    rw [hq]
    push_cast
    ring
  rw [e, evq_smul]
  apply evq_congr
  · unfold cP
    ring
  · intro i _
    rfl
  · intro i _ j _
    rfl

end PD

theorem evq_sub3 (n : ℕ) (c c' c'' : ℤ) (l l' l'' : ℕ → ℤ) (q q' q'' : ℕ → ℕ → ℤ) (y : ℕ → ℝ) :
    evq n (c - c' - c'') (fun i => l i - l' i - l'' i) (fun i j => q i j - q' i j - q'' i j) y
      = evq n c l q y - evq n c' l' q' y - evq n c'' l'' q'' y := by
  unfold evq
  push_cast
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

theorem region_of_data (pd : PD) (fd : FD) (loN hiN : ℤ)
    (hok : pd.Ok) (hfn : fd.Nonneg) (hn : fd.n = pd.G.N)
    (hom : ∀ i < pd.G.N, fd.om i = 20 * pd.lenz i) (hLo : fd.Lo = 1096 * loN) (hHi : fd.Hi = 1096 * hiN)
    (cT : ℤ) (lT : ℕ → ℤ) (qT : ℕ → ℕ → ℤ)
    (hT : ∀ y : ℕ → ℝ, (∀ i < pd.G.N, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq pd.G.N cT lT qT y)
    (Nm : ℕ → ℕ → ℤ)
    (hpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ a ∈ Icc 1 (pd.G.N + 1), ∑ b ∈ Icc 1 (pd.G.N + 1), (Nm a b : ℝ) * x a * x b)
    (h00 : Uu * Nm 1 1 = pd.cP - fd.cF - cT)
    (h0i : ∀ i < pd.G.N, 2 * Uu * Nm 1 (i + 2) = pd.lP i - fd.lF i - lT i)
    (hi0 : ∀ i < pd.G.N, 2 * Uu * Nm (i + 2) 1 = pd.lP i - fd.lF i - lT i)
    (hij : ∀ i < pd.G.N, ∀ j < pd.G.N, 2 * Uu * Nm (i + 2) (j + 2)
      = (pd.qP i j - fd.qF i j - qT i j) + (pd.qP j i - fd.qF j i - qT j i)) :
    RegionLB pd.G ((loN : ℚ) / 20) ((hiN : ℚ) / 20) := by
  intro y hy hlo hhi
  have hy' : ∀ i < fd.n, 0 ≤ y i ∧ y i ≤ 1 := by
    rw [hn]; exact hy
  
  have hRm : (Rr : ℝ) * pd.G.mval y = ∑ k ∈ range fd.n, (fd.om k : ℝ) * y k := by
    unfold Grid.mval
    rw [Finset.mul_sum, hn]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [hom k hk', hok.len k hk']
    unfold Grid.wt Rr
    push_cast
    ring
  have hRlo : (Rr : ℝ) * (((loN : ℚ) / 20 : ℚ) : ℝ) = fd.Lo := by
    rw [hLo]; unfold Rr; push_cast; ring
  have hRhi : (Rr : ℝ) * (((hiN : ℚ) / 20 : ℚ) : ℝ) = fd.Hi := by
    rw [hHi]; unfold Rr; push_cast; ring
  have hFS := fd.FSr_nonneg hfn (pd.G.mval y) (((loN : ℚ) / 20 : ℚ) : ℝ) (((hiN : ℚ) / 20 : ℚ) : ℝ) y hy' hlo hhi
  have hFSe := FD.FSr_evq fd (pd.G.mval y) (((loN : ℚ) / 20 : ℚ) : ℝ) (((hiN : ℚ) / 20 : ℚ) : ℝ) y hRm hRlo hRhi
  have hFSe' : (Uu : ℝ) * fd.FSr (pd.G.mval y) (((loN : ℚ) / 20 : ℚ) : ℝ) (((hiN : ℚ) / 20 : ℚ) : ℝ) y
      = evq pd.G.N fd.cF fd.lF fd.qF y := by
    rw [← hn]; exact hFSe
  have hPS := PD.PS_evq pd y
  have hPSle := PD.PS_le pd hok y
  have hTy := hT y hy
  
  set x : ℕ → ℝ := fun a => if a = 1 then 1 else y (a - 2) with hx
  have hx1 : x 1 = 1 := by simp [hx]
  have hx2 : ∀ i, x (i + 2) = y i := by
    intro i
    simp [hx]
  have hg := gram_ev pd.G.N Nm x y hx1 hx2
  have hpos := hpsd x
  rw [hg] at hpos
  have hmat : (Uu : ℝ) * evq pd.G.N (Nm 1 1) (fun i => Nm 1 (i + 2) + Nm (i + 2) 1) (fun i j => Nm (i + 2) (j + 2)) y
      = evq pd.G.N (pd.cP - fd.cF - cT) (fun i => pd.lP i - fd.lF i - lT i)
          (fun i j => pd.qP i j - fd.qF i j - qT i j) y := by
    rw [evq_smul]
    apply evq_congr
    · exact h00
    · intro i hi
      have a := h0i i hi
      have b := hi0 i hi
      linarith
    · intro i hi j hj
      have a := hij i hi j hj
      have b := hij j hj i hi
      linarith
  rw [evq_sub3, ← hPS, ← hFSe'] at hmat
  have hU : (0 : ℝ) < Uu := by norm_num [Uu]
  have hD : (0 : ℝ) < Dz := by norm_num [Dz, Qn]
  have hprod : 0 ≤ (Uu : ℝ) * evq pd.G.N (Nm 1 1) (fun i => Nm 1 (i + 2) + Nm (i + 2) 1)
      (fun i j => Nm (i + 2) (j + 2)) y := mul_nonneg hU.le hpos
  have h1 : 0 ≤ (Uu : ℝ) * pd.PS y := by
    have := mul_nonneg hU.le hFS
    linarith
  have h2 : 0 ≤ pd.PS y := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg hU hneg
    linarith
  have h3 : 0 ≤ (Dz : ℝ) * pd.G.Lval y := le_trans h2 hPSle
  exact (mul_nonneg_iff_of_pos_left hD).mp h3

end Erdos1186Ex

end

section

namespace Erdos1186Ex

open Finset Erdos1186Day Erdos1186Night2 Erdos1186Night2M2

structure Tabs where
  n : ℕ
  loN : ℤ
  hiN : ℤ
  Zn : ℤ
  ppn : ℤ
  rrn : ℤ
  ssn : ℤ
  vlo : ℕ → ℤ
  vhi : ℕ → ℤ
  vlen : ℕ → ℤ
  vsg : ℕ → ℤ
  vAl : ℕ → ℤ
  vBt : ℕ → ℤ
  vYv : ℕ → ℤ
  vOv : ℕ → ℤ
  vA1 : ℕ → ℤ
  vA2 : ℕ → ℤ
  vA3 : ℕ → ℤ
  vA4 : ℕ → ℤ
  YYT : ℕ → ℕ → ℤ
  OOT : ℕ → ℕ → ℤ
  YOT : ℕ → ℕ → ℤ
  thT : ℕ → ℕ → ℤ
  NT : ℕ → ℕ → ℤ
  crows : List (List ℤ)
  czr : List ℤ

def a4acc (G : Grid) (lo hi len : ℕ → ℤ) (i j : ℕ) : ℤ :=
  if 1 ≤ 2 * (lo j + 1) - hi i - 1 ∧ 2 * hi j - (lo i + 1) - 1 ≤ 1094 then 4 * len i * len j
  else if 2 * hi j - (lo i + 1) - 1 ≤ -2 ∨ 1097 ≤ 2 * (lo j + 1) - hi i - 1 then 0
  else (G.A4 i j : ℤ)

theorem a4acc_eq (G : Grid) (lo hi len : ℕ → ℤ) (i j : ℕ) (hi1 : lo i = G.lo i) (hi2 : hi i = G.hi i)
    (hi3 : len i = G.len i) (hj1 : lo j = G.lo j) (hj2 : hi j = G.hi j) (hj3 : len j = G.len j) :
    a4acc G lo hi len i j = (G.A4 i j : ℤ) := by
  have h := A4v_eq G i j
  unfold a4acc
  rw [hi1, hi2, hi3, hj1, hj2, hj3]
  unfold A4v at h
  split_ifs at h ⊢ with c1 c2
  · rw [← h]
    push_cast
    ring
  · rw [← h]
    simp
  · exact_mod_cast h.symm

def mkPD (T : Tabs) (G : Grid) : PD where
  G := G
  lenz := T.vlen
  sgz := T.vsg
  alz := T.vAl
  btz := T.vBt
  a4z := a4acc G (T.vlo) (T.vhi) (T.vlen)
  th := T.thT

def mkFD (T : Tabs) : FD where
  n := T.n
  Yv := fun i => T.Zn * T.vYv i
  Ov := fun i => T.Zn * T.vOv i
  A1 := fun i => T.Zn * T.vA1 i
  A2 := fun i => T.Zn * T.vA2 i
  A3 := fun i => T.Zn * T.vA3 i
  A4 := fun i => T.Zn * T.vA4 i
  YY := fun i j => T.Zn * T.YYT i j
  OO := fun i j => T.Zn * T.OOT i j
  YO := fun i j => T.Zn * T.YOT i j
  pp := T.Zn * T.ppn
  rr := T.Zn * T.rrn
  ss := T.Zn * T.ssn
  om := fun i => 20 * T.vlen i
  Lo := 1096 * T.loN
  Hi := 1096 * T.hiN

def Nmat (T : Tabs) (a b : ℕ) : ℤ := T.NT (a - 1) (b - 1)

def gridChk (T : Tabs) (G : Grid) (i : ℕ) : Bool :=
  decide (T.vlo i = (G.lo i : ℤ) ∧ T.vhi i = (G.hi i : ℤ) ∧ T.vlen i = (G.len i : ℤ) ∧
    T.vsg i = G.sgn i ∧ G.ai i * (Dz : ℚ) = ((T.vAl i : ℤ) : ℚ) ∧
    G.bi i * (Dz : ℚ) = ((T.vBt i : ℤ) : ℚ))

def vecChk (T : Tabs) (i : ℕ) : Bool :=
  decide (0 ≤ T.vYv i ∧ 0 ≤ T.vOv i ∧ 0 ≤ T.vA1 i ∧ 0 ≤ T.vA2 i ∧
    0 ≤ T.vA3 i ∧ 0 ≤ T.vA4 i)

def scalChk (T : Tabs) : Bool := decide (0 ≤ T.ppn ∧ 0 ≤ T.rrn ∧ 0 ≤ T.ssn ∧ 0 < T.Zn)

structure Tri where
  cT : ℤ
  lT : ℕ → ℤ
  qT : ℕ → ℕ → ℤ

def Tri.zero : Tri := ⟨0, fun _ => 0, fun _ _ => 0⟩

def pairChk (T : Tabs) (G : Grid) (tr : Tri) (i j : ℕ) : Bool :=
  decide ((0 ≤ T.thT i j ∧ T.thT i j ≤ Qn) ∧ 0 ≤ T.YYT i j ∧ 0 ≤ T.OOT i j ∧
    0 ≤ T.YOT i j ∧
    2 * Uu * Nmat T (i + 2) (j + 2) =
      ((mkPD T G).qP i j - (mkFD T).qF i j - tr.qT i j) + ((mkPD T G).qP j i - (mkFD T).qF j i - tr.qT j i))

def linChk (T : Tabs) (G : Grid) (tr : Tri) (i : ℕ) : Bool :=
  decide (2 * Uu * Nmat T 1 (i + 2) = (mkPD T G).lP i - (mkFD T).lF i - tr.lT i ∧
    2 * Uu * Nmat T (i + 2) 1 = (mkPD T G).lP i - (mkFD T).lF i - tr.lT i)

def czRowChk (T : Tabs) (G : Grid) (i : ℕ) : Bool :=
  decide ((∑ j ∈ range G.N, (mkPD T G).cz i j) = T.czr.getD i 0)

def constChk (T : Tabs) (G : Grid) (tr : Tri) : Bool :=
  decide (Uu * Nmat T 1 1 = -Uu * (∑ i ∈ range G.N, T.czr.getD i 0) - (mkFD T).cF - tr.cT)

def absSumRow (row : ℕ → ℤ) (ri : List ℤ) : ℕ → List (List ℤ) → ℕ
  | _, [] => 0
  | j, rj :: rest => (row j - dotL ri rj).natAbs + absSumRow row ri (j + 1) rest

def domRow (T : Tabs) (a : ℕ) : Bool :=
  decide (((absSumRow (T.NT a) (T.crows.getD a []) 0 T.crows : ℕ) : ℤ)
    ≤ 2 * (T.NT a a - dotL (T.crows.getD a []) (T.crows.getD a [])))

def lenChk (T : Tabs) : Bool :=
  decide (T.crows.length = T.n + 1) && T.crows.all (fun r => decide (r.length ≤ T.n + 1))

theorem absSumRow_eq (row : ℕ → ℤ) (ri : List ℤ) :
    ∀ (rows : List (List ℤ)) (j0 : ℕ),
      ((absSumRow row ri j0 rows : ℕ) : ℤ) =
        ∑ t ∈ range rows.length, |row (j0 + t) - dotL ri (rows.getD t [])|
  | [], j0 => by simp [absSumRow]
  | rj :: rest, j0 => by
      have ih := absSumRow_eq row ri rest (j0 + 1)
      have hsum : ∑ t ∈ range rest.length, |row (j0 + 1 + t) - dotL ri (rest.getD t [])| =
          ∑ t ∈ range rest.length, |row (j0 + (t + 1)) - dotL ri (rest.getD t [])| := by
        apply Finset.sum_congr rfl
        intro t _
        rw [show j0 + 1 + t = j0 + (t + 1) by omega]
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [absSumRow, List.getD_cons_succ, List.getD_cons_zero, add_zero]
      push_cast
      rw [ih, hsum, add_comm]

theorem domRow_sound (T : Tabs) (hrows : T.crows.length = T.n + 1) (a : ℕ) (h : domRow T a = true) :
    ∑ b ∈ Icc 1 (T.n + 1), |Nmat T (a + 1) b - dotL (T.crows.getD a []) (T.crows.getD (b - 1) [])|
      ≤ 2 * (Nmat T (a + 1) (a + 1) - dotL (T.crows.getD a []) (T.crows.getD a [])) := by
  unfold domRow at h
  have h' := of_decide_eq_true h
  rw [absSumRow_eq, hrows] at h'
  have e : ∑ b ∈ Icc 1 (T.n + 1), |Nmat T (a + 1) b - dotL (T.crows.getD a []) (T.crows.getD (b - 1) [])|
      = ∑ t ∈ range (T.n + 1), |T.NT a (0 + t) - dotL (T.crows.getD a []) (T.crows.getD t [])| := by
    rw [sum_Icc_one]
    apply Finset.sum_congr rfl
    intro t _
    unfold Nmat
    simp
  rw [e]
  unfold Nmat
  simpa using h'

theorem psd_of_rows (L : ℕ) (Nm : ℕ → ℕ → ℤ) (crow : ℕ → List ℤ)
    (hlen : ∀ i ∈ Icc 1 L, (crow i).length ≤ L)
    (hsym : ∀ i ∈ Icc 1 L, ∀ j ∈ Icc 1 L, Nm i j = Nm j i)
    (hdom : ∀ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, |Nm i j - dotL (crow i) (crow j)|
      ≤ 2 * (Nm i i - dotL (crow i) (crow i))) (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (Nm i j : ℝ) * x i * x j := by
  set c : ℕ → ℕ → ℝ := fun i k => (((crow i).getD k 0 : ℤ) : ℝ) with hc
  set Er : ℕ → ℕ → ℝ := fun i j =>
    if i ∈ Icc 1 L ∧ j ∈ Icc 1 L then ((Nm i j - dotL (crow i) (crow j) : ℤ) : ℝ) else 0 with hEr
  have hG := gram_nonneg L L c x
  have hEs : ∀ i j, Er i j = Er j i := by
    intro i j
    simp only [hEr]
    by_cases h : i ∈ Icc 1 L ∧ j ∈ Icc 1 L
    · have h' : j ∈ Icc 1 L ∧ i ∈ Icc 1 L := ⟨h.2, h.1⟩
      rw [if_pos h, if_pos h', hsym i h.1 j h.2, dotL_comm (crow i) (crow j)]
    · have h' : ¬ (j ∈ Icc 1 L ∧ i ∈ Icc 1 L) := fun hh => h ⟨hh.2, hh.1⟩
      rw [if_neg h, if_neg h']
  have hE := psd_of_dom L Er hEs
    (fun i hi => by
      have hd := hdom i hi
      have e : ∀ j ∈ Icc 1 L, |Er i j| = |((Nm i j - dotL (crow i) (crow j) : ℤ) : ℝ)| := by
        intro j hj
        simp only [hEr]
        rw [if_pos ⟨hi, hj⟩]
      have e2 : Er i i = ((Nm i i - dotL (crow i) (crow i) : ℤ) : ℝ) := by
        simp only [hEr]
        rw [if_pos ⟨hi, hi⟩]
      rw [Finset.sum_congr rfl e, e2]
      have hcast : (∑ j ∈ Icc 1 L, |((Nm i j - dotL (crow i) (crow j) : ℤ) : ℝ)|)
          = ((∑ j ∈ Icc 1 L, |Nm i j - dotL (crow i) (crow j)| : ℤ) : ℝ) := by
        push_cast
        rfl
      rw [hcast]
      exact_mod_cast hd) x
  have hsum : ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (Nm i j : ℝ) * x i * x j =
      (∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, (∑ k ∈ range L, c i k * c j k) * x i * x j)
      + ∑ i ∈ Icc 1 L, ∑ j ∈ Icc 1 L, Er i j * x i * x j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hd : dotL (crow i) (crow j) = ∑ k ∈ range L, (crow i).getD k 0 * (crow j).getD k 0 :=
      dotL_eq_sum _ _ _ (hlen i hi)
    have e : (Nm i j : ℝ) = (∑ k ∈ range L, c i k * c j k) + Er i j := by
      simp only [hEr, hc]
      rw [if_pos ⟨hi, hj⟩]
      have : (Nm i j : ℤ) = (∑ k ∈ range L, (crow i).getD k 0 * (crow j).getD k 0) + (Nm i j - dotL (crow i) (crow j)) := by
        rw [← hd]; ring
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) this
      simp only [Int.cast_add, Int.cast_sum, Int.cast_mul] at h2
      exact h2
    rw [e]
    ring
  rw [hsum]
  exact add_nonneg hG hE

theorem gridChk_spec (T : Tabs) (G : Grid) (i : ℕ) (h : gridChk T G i = true) :
    T.vlo i = (G.lo i : ℤ) ∧ T.vhi i = (G.hi i : ℤ) ∧ T.vlen i = (G.len i : ℤ) ∧
    T.vsg i = G.sgn i ∧ G.ai i * (Dz : ℚ) = ((T.vAl i : ℤ) : ℚ) ∧
    G.bi i * (Dz : ℚ) = ((T.vBt i : ℤ) : ℚ) := of_decide_eq_true h

theorem vecChk_spec (T : Tabs) (i : ℕ) (h : vecChk T i = true) :
    0 ≤ T.vYv i ∧ 0 ≤ T.vOv i ∧ 0 ≤ T.vA1 i ∧ 0 ≤ T.vA2 i ∧
    0 ≤ T.vA3 i ∧ 0 ≤ T.vA4 i := of_decide_eq_true h

theorem scalChk_spec (T : Tabs) (h : scalChk T = true) : 0 ≤ T.ppn ∧ 0 ≤ T.rrn ∧ 0 ≤ T.ssn ∧ 0 < T.Zn :=
  of_decide_eq_true h

theorem pairChk_spec (T : Tabs) (G : Grid) (tr : Tri) (i j : ℕ) (h : pairChk T G tr i j = true) :
    (0 ≤ T.thT i j ∧ T.thT i j ≤ Qn) ∧ 0 ≤ T.YYT i j ∧ 0 ≤ T.OOT i j ∧
    0 ≤ T.YOT i j ∧
    2 * Uu * Nmat T (i + 2) (j + 2) =
      ((mkPD T G).qP i j - (mkFD T).qF i j - tr.qT i j) + ((mkPD T G).qP j i - (mkFD T).qF j i - tr.qT j i) :=
  of_decide_eq_true h

theorem linChk_spec (T : Tabs) (G : Grid) (tr : Tri) (i : ℕ) (h : linChk T G tr i = true) :
    2 * Uu * Nmat T 1 (i + 2) = (mkPD T G).lP i - (mkFD T).lF i - tr.lT i ∧
    2 * Uu * Nmat T (i + 2) 1 = (mkPD T G).lP i - (mkFD T).lF i - tr.lT i := of_decide_eq_true h

theorem cP_eq (T : Tabs) (G : Grid) (hcz : ∀ i < G.N, czRowChk T G i = true) :
    (mkPD T G).cP = -Uu * ∑ i ∈ range G.N, T.czr.getD i 0 := by
  unfold PD.cP
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact of_decide_eq_true (hcz i (Finset.mem_range.mp hi))

theorem constChk_spec (T : Tabs) (G : Grid) (tr : Tri) (hcz : ∀ i < G.N, czRowChk T G i = true)
    (h : constChk T G tr = true) :
    Uu * Nmat T 1 1 = (mkPD T G).cP - (mkFD T).cF - tr.cT := by
  rw [cP_eq T G hcz]
  exact of_decide_eq_true h

theorem two_Uu_ne : (2 * Uu : ℤ) ≠ 0 := by unfold Uu; norm_num

theorem Nsym (T : Tabs) (G : Grid) (tr : Tri)
    (hlin : ∀ i < G.N, linChk T G tr i = true)
    (hpair : ∀ i < G.N, ∀ j < G.N, pairChk T G tr i j = true) :
    ∀ a ∈ Icc 1 (G.N + 1), ∀ b ∈ Icc 1 (G.N + 1), Nmat T a b = Nmat T b a := by
  intro a ha b hb
  rw [Finset.mem_Icc] at ha hb
  by_cases h1 : a = 1
  · subst h1
    by_cases h2 : b = 1
    · subst h2; rfl
    · obtain ⟨j, rfl⟩ : ∃ j, b = j + 2 := ⟨b - 2, by omega⟩
      have hl := linChk_spec T G tr j (hlin j (by omega))
      exact mul_left_cancel₀ two_Uu_ne (hl.1.trans hl.2.symm)
  · obtain ⟨i, rfl⟩ : ∃ i, a = i + 2 := ⟨a - 2, by omega⟩
    by_cases h2 : b = 1
    · subst h2
      have hl := linChk_spec T G tr i (hlin i (by omega))
      exact mul_left_cancel₀ two_Uu_ne (hl.2.trans hl.1.symm)
    · obtain ⟨j, rfl⟩ : ∃ j, b = j + 2 := ⟨b - 2, by omega⟩
      have e1 := (pairChk_spec T G tr i j (hpair i (by omega) j (by omega))).2.2.2.2
      have e2 := (pairChk_spec T G tr j i (hpair j (by omega) i (by omega))).2.2.2.2
      refine mul_left_cancel₀ two_Uu_ne ?_
      rw [e1, e2]
      ring

theorem lenChk_spec (T : Tabs) (h : lenChk T = true) :
    T.crows.length = T.n + 1 ∧ ∀ r ∈ T.crows, r.length ≤ T.n + 1 := by
  unfold lenChk at h
  rw [Bool.and_eq_true] at h
  refine ⟨of_decide_eq_true h.1, ?_⟩
  intro r hr
  have := List.all_eq_true.mp h.2 r hr
  exact of_decide_eq_true this

theorem region_of_tabs_aux (T : Tabs) (G : Grid) (tr : Tri) (hn : T.n = G.N)
    (hgrid : ∀ i < G.N, gridChk T G i = true)
    (hvec : ∀ i < G.N, vecChk T i = true)
    (hscal : scalChk T = true)
    (hpair : ∀ i < G.N, ∀ j < G.N, pairChk T G tr i j = true)
    (hlin : ∀ i < G.N, linChk T G tr i = true)
    (hcz : ∀ i < G.N, czRowChk T G i = true)
    (hconst : constChk T G tr = true)
    (hlen : lenChk T = true)
    (hdom : ∀ a < G.N + 1, domRow T a = true)
    (hT : ∀ y : ℕ → ℝ, (∀ i < T.n, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq T.n tr.cT tr.lT tr.qT y) :
    RegionLB G ((T.loN : ℚ) / 20) ((T.hiN : ℚ) / 20) := by
  have hT' : ∀ y : ℕ → ℝ, (∀ i < G.N, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq G.N tr.cT tr.lT tr.qT y := by
    intro y hy
    rw [← hn]
    rw [← hn] at hy
    exact hT y hy
  obtain ⟨hppn, hrrn, hssn, hZn⟩ := scalChk_spec T hscal
  have hok : (mkPD T G).Ok := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi; exact (gridChk_spec T G i (hgrid i hi)).2.2.1
    · intro i hi; exact (gridChk_spec T G i (hgrid i hi)).2.2.2.1
    · intro i hi; exact (gridChk_spec T G i (hgrid i hi)).2.2.2.2.1
    · intro i hi; exact (gridChk_spec T G i (hgrid i hi)).2.2.2.2.2
    · intro i hi j hj
      have a := gridChk_spec T G i (hgrid i hi)
      have b := gridChk_spec T G j (hgrid j hj)
      exact a4acc_eq G _ _ _ i j a.1 a.2.1 a.2.2.1 b.1 b.2.1 b.2.2.1
    · intro i hi j hj
      exact (pairChk_spec T G tr i j (hpair i hi j hj)).1
  have hfn : (mkFD T).Nonneg := by
    have hz : ∀ x : ℤ, 0 ≤ x → 0 ≤ T.Zn * x := fun x hx => mul_nonneg hZn.le hx
    have hn' : (mkFD T).n = G.N := hn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).1
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).2.1
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).2.2.1
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).2.2.2.1
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).2.2.2.2.1
    · intro i hi; exact hz _ (vecChk_spec T i (hvec i (hn' ▸ hi))).2.2.2.2.2
    · intro i hi j hj
      exact hz _ (pairChk_spec T G tr i j (hpair i (hn' ▸ hi) j (hn' ▸ hj))).2.1
    · intro i hi j hj
      exact hz _ (pairChk_spec T G tr i j (hpair i (hn' ▸ hi) j (hn' ▸ hj))).2.2.1
    · intro i hi j hj
      exact hz _ (pairChk_spec T G tr i j (hpair i (hn' ▸ hi) j (hn' ▸ hj))).2.2.2.1
    · exact hz _ hppn
    · exact hz _ hrrn
    · exact hz _ hssn
  obtain ⟨hcl, hrl⟩ := lenChk_spec T hlen
  have hpsd : ∀ x : ℕ → ℝ, 0 ≤ ∑ a ∈ Icc 1 (G.N + 1), ∑ b ∈ Icc 1 (G.N + 1), (Nmat T a b : ℝ) * x a * x b := by
    intro x
    refine psd_of_rows (G.N + 1) (Nmat T) (fun i => T.crows.getD (i - 1) []) ?_ (Nsym T G tr hlin hpair) ?_ x
    · intro i hi
      rw [Finset.mem_Icc] at hi
      have hlt : i - 1 < T.crows.length := by omega
      have hmem : T.crows.getD (i - 1) [] ∈ T.crows := by
        rw [List.getD_eq_getElem _ _ hlt]
        exact List.getElem_mem hlt
      show (T.crows.getD (i - 1) []).length ≤ G.N + 1
      rw [← hn]
      exact hrl _ hmem
    · intro i hi
      rw [Finset.mem_Icc] at hi
      obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
      have h := domRow_sound T (by omega) a (hdom a (by omega))
      simp only [Nat.add_sub_cancel]
      rw [hn] at h
      exact h
  exact region_of_data (mkPD T G) (mkFD T) T.loN T.hiN hok hfn hn (fun _ _ => rfl) rfl rfl tr.cT tr.lT tr.qT hT'
    (Nmat T) hpsd (constChk_spec T G tr hcz hconst)
    (fun i hi => (linChk_spec T G tr i (hlin i hi)).1)
    (fun i hi => (linChk_spec T G tr i (hlin i hi)).2)
    (fun i hi j hj => (pairChk_spec T G tr i j (hpair i hi j hj)).2.2.2.2)

theorem region_of_tabs (T : Tabs) (G : Grid) (tr : Tri) (m : ℕ) (hm : G.N = m) (hn : T.n = m)
    (hgrid : ∀ i < m, gridChk T G i = true)
    (hvec : ∀ i < m, vecChk T i = true)
    (hscal : scalChk T = true)
    (hpair : ∀ i < m, ∀ j < m, pairChk T G tr i j = true)
    (hlin : ∀ i < m, linChk T G tr i = true)
    (hcz : ∀ i < m, czRowChk T G i = true)
    (hconst : constChk T G tr = true)
    (hlen : lenChk T = true)
    (hdom : ∀ a < m + 1, domRow T a = true)
    (hT : ∀ y : ℕ → ℝ, (∀ i < T.n, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq T.n tr.cT tr.lT tr.qT y) :
    RegionLB G ((T.loN : ℚ) / 20) ((T.hiN : ℚ) / 20) := by
  subst hm
  exact region_of_tabs_aux T G tr hn hgrid hvec hscal hpair hlin hcz hconst hlen hdom hT

theorem all_range_of {f : ℕ → Bool} {a k : ℕ} (h : (List.range' a k).all f = true) :
    ∀ i, a ≤ i → i < a + k → f i = true := by
  intro i h1 h2
  have := List.all_eq_true.mp h i (by rw [List.mem_range']; exact ⟨i - a, by omega, by omega⟩)
  exact this

theorem all_range0_of {f : ℕ → Bool} {n : ℕ} (h : (List.range n).all f = true) : ∀ i, i < n → f i = true := by
  intro i hi
  exact List.all_eq_true.mp h i (List.mem_range.mpr hi)

theorem all_range_of2 {f : ℕ → ℕ → Bool} {a k n : ℕ}
    (h : (List.range' a k).all (fun i => (List.range n).all (fun j => f i j)) = true) :
    ∀ i, a ≤ i → i < a + k → ∀ j, j < n → f i j = true := by
  intro i h1 h2 j hj
  have h3 := all_range_of h i h1 h2
  exact all_range0_of h3 j hj

theorem all_range_of2c {f : ℕ → ℕ → Bool} {g : ℕ → Bool} {a k n : ℕ}
    (h : (List.range' a k).all (fun i => (List.range n).all (fun j => f i j) && g i) = true) :
    ∀ i, a ≤ i → i < a + k → (∀ j, j < n → f i j = true) ∧ g i = true := by
  intro i h1 h2
  have h3 := all_range_of h i h1 h2
  rw [Bool.and_eq_true] at h3
  exact ⟨fun j hj => all_range0_of h3.1 j hj, h3.2⟩

theorem Tri.zero_ok (n : ℕ) :
    ∀ y : ℕ → ℝ, (∀ i < n, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq n Tri.zero.cT Tri.zero.lT Tri.zero.qT y := by
  intro y _
  exact le_of_eq (FD.evq_zero n y).symm

end Erdos1186Ex

end

section

namespace Erdos1186Ex

open Finset Erdos1186Night2M2

structure TriT where
  i : ℕ
  j : ℕ
  k : ℕ
  s1 : ℤ
  s2 : ℤ
  s3 : ℤ
  w : ℤ

def TriT.ok (n : ℕ) (t : TriT) : Bool :=
  decide (t.i < n ∧ t.j < n ∧ t.k < n ∧ (t.s1 = 1 ∨ t.s1 = -1) ∧ (t.s2 = 1 ∨ t.s2 = -1) ∧
    (t.s3 = 1 ∨ t.s3 = -1) ∧ t.s1 * t.s2 * t.s3 = 1 ∧ 0 ≤ t.w)

noncomputable def triv (t : TriT) (y : ℕ → ℝ) : ℝ :=
  1 + (t.s1 : ℝ) * ((1 - 2 * y t.i) * (1 - 2 * y t.j)) + (t.s2 : ℝ) * ((1 - 2 * y t.j) * (1 - 2 * y t.k))
    + (t.s3 : ℝ) * ((1 - 2 * y t.i) * (1 - 2 * y t.k))

theorem tri_ineq (u v w : ℝ) (s1 s2 s3 : ℤ) (hu1 : -1 ≤ u) (hu2 : u ≤ 1) (hv1 : -1 ≤ v) (hv2 : v ≤ 1)
    (hw1 : -1 ≤ w) (hw2 : w ≤ 1) (h1 : s1 = 1 ∨ s1 = -1) (h2 : s2 = 1 ∨ s2 = -1) (h3 : s3 = 1 ∨ s3 = -1)
    (hp : s1 * s2 * s3 = 1) :
    0 ≤ 1 + (s1 : ℝ) * (u * v) + (s2 : ℝ) * (v * w) + (s3 : ℝ) * (u * w) := by
  have pu : 0 ≤ 1 + u := by linarith
  have mu : 0 ≤ 1 - u := by linarith
  have pv : 0 ≤ 1 + v := by linarith
  have mv : 0 ≤ 1 - v := by linarith
  have pw : 0 ≤ 1 + w := by linarith
  have mw : 0 ≤ 1 - w := by linarith
  have A := mul_nonneg (mul_nonneg pu pv) pw
  have B := mul_nonneg (mul_nonneg mu mv) mw
  have C := mul_nonneg (mul_nonneg pu pv) mw
  have D := mul_nonneg (mul_nonneg mu mv) pw
  have E := mul_nonneg (mul_nonneg pu mv) mw
  have F := mul_nonneg (mul_nonneg mu pv) pw
  have G := mul_nonneg (mul_nonneg pu mv) pw
  have H := mul_nonneg (mul_nonneg mu pv) mw
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl <;>
    first
    | (exfalso; norm_num at hp; done)
    | (push_cast; nlinarith [A, B, C, D, E, F, G, H])

theorem triv_nonneg (t : TriT) (n : ℕ) (ht : t.ok n = true) (y : ℕ → ℝ) (hy : ∀ i < n, 0 ≤ y i ∧ y i ≤ 1) :
    0 ≤ triv t y := by
  unfold TriT.ok at ht
  obtain ⟨hi, hj, hk, h1, h2, h3, hp, _⟩ := of_decide_eq_true ht
  obtain ⟨a0, a1⟩ := hy t.i hi
  obtain ⟨b0, b1⟩ := hy t.j hj
  obtain ⟨c0, c1⟩ := hy t.k hk
  unfold triv
  exact tri_ineq (1 - 2 * y t.i) (1 - 2 * y t.j) (1 - 2 * y t.k) t.s1 t.s2 t.s3 (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) h1 h2 h3 hp

def tc (t : TriT) : ℤ := 1 + t.s1 + t.s2 + t.s3

def tl (t : TriT) (a : ℕ) : ℤ :=
  -2 * ((if a = t.i then t.s1 + t.s3 else 0) + (if a = t.j then t.s1 + t.s2 else 0)
    + (if a = t.k then t.s2 + t.s3 else 0))

def tq (t : TriT) (a b : ℕ) : ℤ :=
  4 * ((if a = t.i ∧ b = t.j then t.s1 else 0) + (if a = t.j ∧ b = t.k then t.s2 else 0)
    + (if a = t.i ∧ b = t.k then t.s3 else 0))

theorem sum_if_eq (n i : ℕ) (hi : i < n) (f : ℕ → ℝ) :
    ∑ a ∈ range n, (if a = i then f a else 0) = f i := by
  rw [Finset.sum_ite_eq']
  simp [hi]

theorem sum2_if (n i j : ℕ) (hi : i < n) (hj : j < n) (f : ℕ → ℕ → ℝ) :
    ∑ a ∈ range n, ∑ b ∈ range n, (if a = i ∧ b = j then f a b else 0) = f i j := by
  have : ∀ a b : ℕ, (if a = i ∧ b = j then f a b else 0) = if a = i then (if b = j then f a b else 0) else 0 := by
    intro a b
    by_cases h1 : a = i <;> by_cases h2 : b = j <;> simp [h1, h2]
  simp only [this]
  have e : ∀ a ∈ range n, ∑ b ∈ range n, (if a = i then (if b = j then f a b else 0) else 0)
      = if a = i then f a j else 0 := by
    intro a _
    by_cases h1 : a = i
    · simp only [h1, if_true]
      rw [Finset.sum_ite_eq']
      simp [hj]
    · simp [h1]
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq']
  simp [hi]

theorem evq_tri (n : ℕ) (t : TriT) (hi : t.i < n) (hj : t.j < n) (hk : t.k < n) (y : ℕ → ℝ) :
    evq n (tc t) (tl t) (tq t) y = triv t y := by
  unfold evq
  have hl : ∑ a ∈ range n, ((tl t a : ℤ) : ℝ) * y a
      = (∑ a ∈ range n, (if a = t.i then -2 * ((t.s1 : ℝ) + t.s3) * y a else 0))
        + (∑ a ∈ range n, (if a = t.j then -2 * ((t.s1 : ℝ) + t.s2) * y a else 0))
        + (∑ a ∈ range n, (if a = t.k then -2 * ((t.s2 : ℝ) + t.s3) * y a else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    unfold tl
    push_cast
    split_ifs <;> ring
  have hq : ∑ a ∈ range n, ∑ b ∈ range n, ((tq t a b : ℤ) : ℝ) * (y a * y b)
      = (∑ a ∈ range n, ∑ b ∈ range n, (if a = t.i ∧ b = t.j then 4 * (t.s1 : ℝ) * (y a * y b) else 0))
        + (∑ a ∈ range n, ∑ b ∈ range n, (if a = t.j ∧ b = t.k then 4 * (t.s2 : ℝ) * (y a * y b) else 0))
        + (∑ a ∈ range n, ∑ b ∈ range n, (if a = t.i ∧ b = t.k then 4 * (t.s3 : ℝ) * (y a * y b) else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    unfold tq
    push_cast
    split_ifs <;> ring
  rw [hl, hq, sum_if_eq n t.i hi, sum_if_eq n t.j hj, sum_if_eq n t.k hk,
    sum2_if n t.i t.j hi hj (fun a b => 4 * (t.s1 : ℝ) * (y a * y b)),
    sum2_if n t.j t.k hj hk (fun a b => 4 * (t.s2 : ℝ) * (y a * y b)),
    sum2_if n t.i t.k hi hk (fun a b => 4 * (t.s3 : ℝ) * (y a * y b))]
  unfold triv tc
  push_cast
  ring

def cS (ts : List TriT) : ℤ := (ts.map (fun t => t.w * tc t)).sum
def lS (ts : List TriT) (a : ℕ) : ℤ := (ts.map (fun t => t.w * tl t a)).sum
def qS (ts : List TriT) (a b : ℕ) : ℤ := (ts.map (fun t => t.w * tq t a b)).sum

theorem evq_triS (n : ℕ) (y : ℕ → ℝ) : ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) →
    evq n (cS ts) (lS ts) (qS ts) y = (ts.map (fun t => (t.w : ℝ) * triv t y)).sum
  | [], _ => by simp [cS, lS, qS, evq]
  | t :: ts, h => by
      have ht : t.ok n = true := h t (by simp)
      have hts : ∀ s ∈ ts, s.ok n = true := fun s hs => h s (by simp [hs])
      have ih := evq_triS n y ts hts
      unfold TriT.ok at ht
      obtain ⟨hi, hj, hk, _⟩ := of_decide_eq_true ht
      have e1 := evq_tri n t hi hj hk y
      have e2 := evq_smul n t.w (tc t) (tl t) (tq t) y
      have e3 := evq_add n (t.w * tc t) (cS ts) (fun a => t.w * tl t a) (lS ts) (fun a b => t.w * tq t a b)
        (qS ts) y
      have hc : cS (t :: ts) = t.w * tc t + cS ts := by simp [cS]
      have hl : lS (t :: ts) = fun a => t.w * tl t a + lS ts a := by funext a; simp [lS]
      have hq : qS (t :: ts) = fun a b => t.w * tq t a b + qS ts a b := by funext a b; simp [qS]
      rw [hc, hl, hq, e3, ← e2, e1, ih]
      simp

theorem list_sum_nonneg_of (n : ℕ) (y : ℕ → ℝ) (hy : ∀ i < n, 0 ≤ y i ∧ y i ≤ 1) :
    ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) → 0 ≤ (ts.map (fun t => (t.w : ℝ) * triv t y)).sum
  | [], _ => by simp
  | t :: ts, h => by
      have ht : t.ok n = true := h t (by simp)
      have hts : ∀ s ∈ ts, s.ok n = true := fun s hs => h s (by simp [hs])
      have ih := list_sum_nonneg_of n y hy ts hts
      have hw : (0 : ℝ) ≤ t.w := by
        unfold TriT.ok at ht
        obtain ⟨_, _, _, _, _, _, _, hw⟩ := of_decide_eq_true ht
        exact_mod_cast hw
      have := mul_nonneg hw (triv_nonneg t n ht y hy)
      simp only [List.map_cons, List.sum_cons]
      linarith

end Erdos1186Ex

end

section

namespace Erdos1186Ex

open Finset Erdos1186Night2M2

theorem digit_pack (B : ℕ) (hB : 0 < B) : ∀ (n : ℕ) (d : ℕ → ℕ), (∀ a < n, d a < B) →
    ∀ a < n, ((∑ c ∈ range n, d c * B ^ c) / B ^ a) % B = d a := by
  intro n
  induction n with
  | zero => intro d _ a ha; exact absurd ha (Nat.not_lt_zero _)
  | succ n ih =>
    intro d hd a ha
    have hd0 : d 0 < B := hd 0 (Nat.succ_pos n)
    have e : ∑ c ∈ range (n + 1), d c * B ^ c = d 0 + B * ∑ c ∈ range n, d (c + 1) * B ^ c := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero, mul_one]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [e]
    have hdiv : (d 0 + B * ∑ c ∈ range n, d (c + 1) * B ^ c) / B = ∑ c ∈ range n, d (c + 1) * B ^ c := by
      rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hd0, zero_add]
    cases a with
    | zero =>
      simp only [pow_zero, Nat.div_one]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd0]
    | succ a =>
      have ha' : a < n := by omega
      rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv]
      exact ih (fun c => d (c + 1)) (fun c hc => hd (c + 1) (by omega)) a ha'

theorem pack_lt (B : ℕ) : ∀ (n : ℕ) (d : ℕ → ℕ), (∀ a < n, d a < B) → ∑ c ∈ range n, d c * B ^ c < B ^ n
  | 0, d, _ => by simp
  | n + 1, d, hd => by
    rw [Finset.sum_range_succ]
    have ih := pack_lt B n d (fun a ha => hd a (by omega))
    have h2 := hd n (by omega)
    calc ∑ c ∈ range n, d c * B ^ c + d n * B ^ n < B ^ n + d n * B ^ n := Nat.add_lt_add_right ih _
      _ = (d n + 1) * B ^ n := by ring
      _ ≤ B * B ^ n := Nat.mul_le_mul_right _ h2
      _ = B ^ (n + 1) := by ring

def bp (W p : ℕ) : ℤ := ((2 ^ (W * p) : ℕ) : ℤ)

theorem bp_eq (W a : ℕ) : bp W a = ((2 ^ W : ℕ) : ℤ) ^ a := by
  unfold bp
  push_cast
  rw [pow_mul]

theorem bp_add (W n a b : ℕ) : bp W (n * a + b) = bp (W * n) a * bp W b := by
  unfold bp
  push_cast
  rw [← pow_add]
  congr 1
  ring

theorem two_pow_eq (W : ℕ) (hW : 1 ≤ W) : 2 ^ W = 2 * 2 ^ (W - 1) := by
  rw [← pow_succ']
  congr 1
  omega

theorem dec_of_pack (W : ℕ) (hW : 1 ≤ W) (n : ℕ) (v : ℕ → ℤ) (P : ℕ)
    (hv : ∀ a < n, -((2 ^ (W - 1) : ℕ) : ℤ) ≤ v a ∧ v a < ((2 ^ (W - 1) : ℕ) : ℤ))
    (hP : (P : ℤ) = ∑ a ∈ range n, (v a + ((2 ^ (W - 1) : ℕ) : ℤ)) * bp W a) : ∀ a < n, dec W P a = v a := by
  have hB : 2 ^ W = 2 * 2 ^ (W - 1) := two_pow_eq W hW
  generalize hH : 2 ^ (W - 1) = H at hB hv hP
  have hBi : ((2 ^ W : ℕ) : ℤ) = 2 * (H : ℤ) := by exact_mod_cast hB
  have hd : ∀ a < n, (((v a + (H : ℤ)).toNat : ℕ) : ℤ) = v a + H := by
    intro a ha
    exact Int.toNat_of_nonneg (by have := (hv a ha).1; omega)
  have hdlt : ∀ a < n, (v a + (H : ℤ)).toNat < 2 ^ W := by
    intro a ha
    have h1 := hd a ha
    have h2 := (hv a ha).2
    have : (((v a + (H : ℤ)).toNat : ℕ) : ℤ) < ((2 ^ W : ℕ) : ℤ) := by rw [h1, hBi]; omega
    exact_mod_cast this
  have hsum : (∑ c ∈ range n, (v c + (H : ℤ)).toNat * (2 ^ W) ^ c) = P := by
    have : ((∑ c ∈ range n, (v c + (H : ℤ)).toNat * (2 ^ W) ^ c : ℕ) : ℤ) = (P : ℤ) := by
      rw [hP]
      push_cast
      apply Finset.sum_congr rfl
      intro c hc
      rw [hd c (Finset.mem_range.mp hc), bp_eq]
      push_cast
      ring
    exact_mod_cast this
  intro a ha
  have h := digit_pack (2 ^ W) (by positivity) n (fun c => (v c + (H : ℤ)).toNat) hdlt a ha
  rw [hsum] at h
  unfold dec
  rw [hH, pow_mul, h, hd a ha]
  ring

theorem tb_of_pack (W n : ℕ) (hW : 1 ≤ W) (v : ℕ → ℕ → ℤ) (QR : List ℕ)
    (hv : ∀ a < n, ∀ b < n, -((2 ^ (W - 1) : ℕ) : ℤ) ≤ v a b ∧ v a b < ((2 ^ (W - 1) : ℕ) : ℤ))
    (hQR : ∀ a < n, QR.getD a 0 < 2 ^ (W * n))
    (hX : ((∑ a ∈ range n, QR.getD a 0 * (2 ^ (W * n)) ^ a : ℕ) : ℤ) =
        ∑ a ∈ range n, (∑ b ∈ range n, (v a b + ((2 ^ (W - 1) : ℕ) : ℤ)) * bp W b) * bp (W * n) a) :
    ∀ a < n, ∀ b < n, tb W QR a b = v a b := by
  have hB : 2 ^ W = 2 * 2 ^ (W - 1) := two_pow_eq W hW
  generalize hH : 2 ^ (W - 1) = H at hB hv hX
  have hBi : ((2 ^ W : ℕ) : ℤ) = 2 * (H : ℤ) := by exact_mod_cast hB
  have hd : ∀ a < n, ∀ b < n, (((v a b + (H : ℤ)).toNat : ℕ) : ℤ) = v a b + H := by
    intro a ha b hb
    exact Int.toNat_of_nonneg (by have := (hv a ha b hb).1; omega)
  have hdlt : ∀ a < n, ∀ b < n, (v a b + (H : ℤ)).toNat < 2 ^ W := by
    intro a ha b hb
    have h1 := hd a ha b hb
    have h2 := (hv a ha b hb).2
    have : (((v a b + (H : ℤ)).toNat : ℕ) : ℤ) < ((2 ^ W : ℕ) : ℤ) := by rw [h1, hBi]; omega
    exact_mod_cast this
  
  let e : ℕ → ℕ := fun a => ∑ b ∈ range n, (v a b + (H : ℤ)).toNat * (2 ^ W) ^ b
  have he_lt : ∀ a < n, e a < 2 ^ (W * n) := by
    intro a ha
    have := pack_lt (2 ^ W) n (fun b => (v a b + (H : ℤ)).toNat) (fun b hb => hdlt a ha b hb)
    rw [← pow_mul] at this
    exact this
  have he_cast : ∀ a < n, (e a : ℤ) = ∑ b ∈ range n, (v a b + (H : ℤ)) * bp W b := by
    intro a ha
    simp only [e]
    push_cast
    apply Finset.sum_congr rfl
    intro b hb
    rw [hd a ha b (Finset.mem_range.mp hb), bp_eq]
    push_cast
    ring
  have hsum : (∑ a ∈ range n, e a * (2 ^ (W * n)) ^ a) = ∑ a ∈ range n, QR.getD a 0 * (2 ^ (W * n)) ^ a := by
    have : ((∑ a ∈ range n, e a * (2 ^ (W * n)) ^ a : ℕ) : ℤ) = ((∑ a ∈ range n, QR.getD a 0 * (2 ^ (W * n)) ^ a : ℕ) : ℤ) := by
      rw [hX]
      push_cast
      apply Finset.sum_congr rfl
      intro a ha
      rw [he_cast a (Finset.mem_range.mp ha), bp_eq (W * n) a]
      push_cast
      ring
    exact_mod_cast this
  have hCpos : 0 < 2 ^ (W * n) := by positivity
  intro a ha b hb
  have h1 := digit_pack (2 ^ (W * n)) hCpos n e he_lt a ha
  have h2 := digit_pack (2 ^ (W * n)) hCpos n (fun a => QR.getD a 0) hQR a ha
  rw [← hsum] at h2
  have hrow : QR.getD a 0 = e a := by rw [← h1, ← h2]
  have hpack : (e a : ℤ) = ∑ b ∈ range n, (v a b + (H : ℤ)) * bp W b := he_cast a ha
  have hvr : ∀ b < n, -(2 ^ (W - 1) : ℕ) ≤ v a b ∧ v a b < ((2 ^ (W - 1) : ℕ) : ℤ) := by
    intro b hb; rw [hH]; exact hv a ha b hb
  have := dec_of_pack W hW n (v a) (e a) (by intro b hb; have := hv a ha b hb; rw [hH]; exact this)
    (by rw [hH]; exact hpack) b hb
  unfold tb
  rw [hrow]
  exact this

def cterm (t : TriT) : ℤ := t.w * tc t

def lterm (W : ℕ) (t : TriT) : ℤ :=
  (t.w * (-2 * (t.s1 + t.s3))) * bp W t.i + (t.w * (-2 * (t.s1 + t.s2))) * bp W t.j
    + (t.w * (-2 * (t.s2 + t.s3))) * bp W t.k

def qterm (W n : ℕ) (t : TriT) : ℤ :=
  (t.w * (4 * t.s1)) * bp W (n * t.i + t.j) + (t.w * (4 * t.s2)) * bp W (n * t.j + t.k)
    + (t.w * (4 * t.s3)) * bp W (n * t.i + t.k)

def wterm (t : TriT) : ℤ := t.w

theorem sumI_if (n i : ℕ) (hi : i < n) (f : ℕ → ℤ) :
    ∑ a ∈ range n, (if a = i then f a else 0) = f i := by
  rw [Finset.sum_ite_eq']
  simp [hi]

theorem sumI_if2 (n i j : ℕ) (hi : i < n) (hj : j < n) (f : ℕ → ℕ → ℤ) :
    ∑ a ∈ range n, ∑ b ∈ range n, (if a = i ∧ b = j then f a b else 0) = f i j := by
  have : ∀ a b : ℕ, (if a = i ∧ b = j then f a b else 0) = if a = i then (if b = j then f a b else 0) else 0 := by
    intro a b
    by_cases h1 : a = i <;> by_cases h2 : b = j <;> simp [h1, h2]
  simp only [this]
  have e : ∀ a ∈ range n, ∑ b ∈ range n, (if a = i then (if b = j then f a b else 0) else 0)
      = if a = i then f a j else 0 := by
    intro a _
    by_cases h1 : a = i
    · simp only [h1, if_true]
      rw [Finset.sum_ite_eq']
      simp [hj]
    · simp [h1]
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq']
  simp [hi]

theorem sum_tl (W n : ℕ) (t : TriT) (hi : t.i < n) (hj : t.j < n) (hk : t.k < n) :
    ∑ a ∈ range n, (t.w * tl t a) * bp W a = lterm W t := by
  have h : ∀ a, (t.w * tl t a) * bp W a = (if a = t.i then (t.w * (-2 * (t.s1 + t.s3))) * bp W a else 0)
      + (if a = t.j then (t.w * (-2 * (t.s1 + t.s2))) * bp W a else 0)
      + (if a = t.k then (t.w * (-2 * (t.s2 + t.s3))) * bp W a else 0) := by
    intro a
    unfold tl
    split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib]
  rw [sumI_if n t.i hi (fun a => (t.w * (-2 * (t.s1 + t.s3))) * bp W a),
    sumI_if n t.j hj (fun a => (t.w * (-2 * (t.s1 + t.s2))) * bp W a),
    sumI_if n t.k hk (fun a => (t.w * (-2 * (t.s2 + t.s3))) * bp W a)]
  rfl

theorem sum_tq (W n : ℕ) (t : TriT) (hi : t.i < n) (hj : t.j < n) (hk : t.k < n) :
    ∑ a ∈ range n, ∑ b ∈ range n, (t.w * tq t a b) * bp W (n * a + b) = qterm W n t := by
  have h : ∀ a b, (t.w * tq t a b) * bp W (n * a + b) =
      (if a = t.i ∧ b = t.j then (t.w * (4 * t.s1)) * bp W (n * a + b) else 0)
      + (if a = t.j ∧ b = t.k then (t.w * (4 * t.s2)) * bp W (n * a + b) else 0)
      + (if a = t.i ∧ b = t.k then (t.w * (4 * t.s3)) * bp W (n * a + b) else 0) := by
    intro a b
    unfold tq
    split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib]
  rw [sumI_if2 n t.i t.j hi hj (fun a b => (t.w * (4 * t.s1)) * bp W (n * a + b)),
    sumI_if2 n t.j t.k hj hk (fun a b => (t.w * (4 * t.s2)) * bp W (n * a + b)),
    sumI_if2 n t.i t.k hi hk (fun a b => (t.w * (4 * t.s3)) * bp W (n * a + b))]
  rfl

theorem ok_idx (n : ℕ) (t : TriT) (ht : t.ok n = true) : t.i < n ∧ t.j < n ∧ t.k < n := by
  unfold TriT.ok at ht
  obtain ⟨hi, hj, hk, _⟩ := of_decide_eq_true ht
  exact ⟨hi, hj, hk⟩

theorem ok_w (n : ℕ) (t : TriT) (ht : t.ok n = true) : 0 ≤ t.w := by
  unfold TriT.ok at ht
  obtain ⟨_, _, _, _, _, _, _, hw⟩ := of_decide_eq_true ht
  exact hw

theorem sum_lS (W n : ℕ) : ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) →
    ∑ a ∈ range n, lS ts a * bp W a = (ts.map (lterm W)).sum
  | [], _ => by simp [lS]
  | t :: ts, h => by
      have ht := h t (by simp)
      have ih := sum_lS W n ts (fun s hs => h s (by simp [hs]))
      obtain ⟨hi, hj, hk⟩ := ok_idx n t ht
      have e : ∀ a, lS (t :: ts) a * bp W a = (t.w * tl t a) * bp W a + lS ts a * bp W a := by
        intro a
        simp only [lS, List.map_cons, List.sum_cons]
        ring
      simp only [e, Finset.sum_add_distrib, ih, sum_tl W n t hi hj hk, List.map_cons, List.sum_cons]

theorem sum_qS (W n : ℕ) : ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) →
    ∑ a ∈ range n, ∑ b ∈ range n, qS ts a b * bp W (n * a + b) = (ts.map (qterm W n)).sum
  | [], _ => by simp [qS]
  | t :: ts, h => by
      have ht := h t (by simp)
      have ih := sum_qS W n ts (fun s hs => h s (by simp [hs]))
      obtain ⟨hi, hj, hk⟩ := ok_idx n t ht
      have e : ∀ a b, qS (t :: ts) a b * bp W (n * a + b)
          = (t.w * tq t a b) * bp W (n * a + b) + qS ts a b * bp W (n * a + b) := by
        intro a b
        simp only [qS, List.map_cons, List.sum_cons]
        ring
      simp only [e, Finset.sum_add_distrib, ih, sum_tq W n t hi hj hk, List.map_cons, List.sum_cons]

theorem abs_tl_le (n : ℕ) (t : TriT) (ht : t.ok n = true) (a : ℕ) : |tl t a| ≤ 12 := by
  unfold TriT.ok at ht
  obtain ⟨_, _, _, h1, h2, h3, _, _⟩ := of_decide_eq_true ht
  rw [abs_le]
  unfold tl
  constructor <;> split_ifs <;> omega

theorem abs_tq_le (n : ℕ) (t : TriT) (ht : t.ok n = true) (a b : ℕ) : |tq t a b| ≤ 12 := by
  unfold TriT.ok at ht
  obtain ⟨_, _, _, h1, h2, h3, _, _⟩ := of_decide_eq_true ht
  rw [abs_le]
  unfold tq
  constructor <;> split_ifs <;> omega

theorem abs_lS_le (n : ℕ) : ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) → ∀ a,
    |lS ts a| ≤ 12 * (ts.map (fun t => t.w)).sum
  | [], _, a => by simp [lS]
  | t :: ts, h, a => by
      have ht := h t (by simp)
      have ih := abs_lS_le n ts (fun s hs => h s (by simp [hs])) a
      have hw := ok_w n t ht
      have hl := abs_tl_le n t ht a
      have e : lS (t :: ts) a = t.w * tl t a + lS ts a := by simp [lS]
      have h1 : |t.w * tl t a| ≤ 12 * t.w := by
        rw [abs_mul, abs_of_nonneg hw]
        nlinarith [abs_nonneg (tl t a)]
      rw [e, List.map_cons, List.sum_cons]
      calc |t.w * tl t a + lS ts a| ≤ |t.w * tl t a| + |lS ts a| := abs_add_le _ _
        _ ≤ 12 * t.w + 12 * (ts.map (fun t => t.w)).sum := by linarith
        _ = 12 * (t.w + (ts.map (fun t => t.w)).sum) := by ring

theorem abs_qS_le (n : ℕ) : ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) → ∀ a b,
    |qS ts a b| ≤ 12 * (ts.map (fun t => t.w)).sum
  | [], _, a, b => by simp [qS]
  | t :: ts, h, a, b => by
      have ht := h t (by simp)
      have ih := abs_qS_le n ts (fun s hs => h s (by simp [hs])) a b
      have hw := ok_w n t ht
      have hl := abs_tq_le n t ht a b
      have e : qS (t :: ts) a b = t.w * tq t a b + qS ts a b := by simp [qS]
      have h1 : |t.w * tq t a b| ≤ 12 * t.w := by
        rw [abs_mul, abs_of_nonneg hw]
        nlinarith [abs_nonneg (tq t a b)]
      rw [e, List.map_cons, List.sum_cons]
      calc |t.w * tq t a b + qS ts a b| ≤ |t.w * tq t a b| + |qS ts a b| := abs_add_le _ _
        _ ≤ 12 * t.w + 12 * (ts.map (fun t => t.w)).sum := by linarith
        _ = 12 * (t.w + (ts.map (fun t => t.w)).sum) := by ring

def gsum (f : TriT → ℤ) (cs : List (List TriT)) : ℤ := (cs.map (fun ch => (ch.map f).sum)).sum

theorem gsum_eq (f : TriT → ℤ) : ∀ cs : List (List TriT), gsum f cs = (cs.flatten.map f).sum
  | [] => by simp [gsum]
  | ch :: cs => by
      have ih := gsum_eq f cs
      simp only [gsum, List.map_cons, List.sum_cons, List.flatten_cons, List.map_append, List.sum_append] at ih ⊢
      rw [ih]

theorem gsum_append (f : TriT → ℤ) (A B : List (List TriT)) : gsum f (A ++ B) = gsum f A + gsum f B := by
  simp [gsum, List.map_append, List.sum_append]

theorem list_sum_range (f : ℕ → ℤ) : ∀ n : ℕ, ((List.range n).map f).sum = ∑ a ∈ range n, f a
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, list_sum_range f n]
      simp

theorem list_sum_range_nat (f : ℕ → ℕ) : ∀ n : ℕ, ((List.range n).map f).sum = ∑ a ∈ range n, f a
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, list_sum_range_nat f n]
      simp

def offL (W n : ℕ) : ℤ := ((List.range n).map (fun a => ((2 ^ (W - 1) : ℕ) : ℤ) * bp W a)).sum

def offQ (W n : ℕ) : ℤ := ((List.range n).map (fun a => offL W n * bp (W * n) a)).sum

def packRows (W n : ℕ) (QR : List ℕ) : ℕ := ((List.range n).map (fun a => QR.getD a 0 * (2 ^ (W * n)) ^ a)).sum

theorem offL_eq (W n : ℕ) : offL W n = ∑ a ∈ range n, ((2 ^ (W - 1) : ℕ) : ℤ) * bp W a := by
  unfold offL
  exact list_sum_range _ n

theorem offQ_eq (W n : ℕ) : offQ W n = ∑ a ∈ range n, offL W n * bp (W * n) a := by
  unfold offQ
  exact list_sum_range _ n

theorem packRows_eq (W n : ℕ) (QR : List ℕ) :
    packRows W n QR = ∑ a ∈ range n, QR.getD a 0 * (2 ^ (W * n)) ^ a := by
  unfold packRows
  exact list_sum_range_nat _ n

def Tri.ofPacked (W : ℕ) (c : ℤ) (L : ℕ) (QR : List ℕ) : Tri :=
  ⟨Uu * c, fun a => Uu * dec W L a, fun a b => Uu * tb W QR a b⟩

theorem Tri.coef_ok (n : ℕ) (tr : Tri) (ts : List TriT) (hok : ∀ t ∈ ts, t.ok n = true)
    (hc : tr.cT = Uu * cS ts) (hl : ∀ a < n, tr.lT a = Uu * lS ts a)
    (hq : ∀ a < n, ∀ b < n, tr.qT a b = Uu * qS ts a b) :
    ∀ y : ℕ → ℝ, (∀ i < n, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq n tr.cT tr.lT tr.qT y := by
  intro y hy
  have h1 := evq_triS n y ts hok
  have h2 := evq_smul n Uu (cS ts) (lS ts) (qS ts) y
  have h3 : evq n tr.cT tr.lT tr.qT y
      = evq n (Uu * cS ts) (fun a => Uu * lS ts a) (fun a b => Uu * qS ts a b) y := by
    apply evq_congr
    · exact hc
    · intro a ha
      exact hl a ha
    · intro a ha b hb
      rw [hq a ha b hb, hq b hb a ha]
  rw [h3, ← h2, h1]
  have := list_sum_nonneg_of n y hy ts hok
  have hU : (0 : ℝ) ≤ (Uu : ℝ) := by
    have : (0 : ℤ) ≤ Uu := by unfold Uu; norm_num
    exact_mod_cast this
  exact mul_nonneg hU this

theorem wsum_nonneg (n : ℕ) : ∀ ts : List TriT, (∀ t ∈ ts, t.ok n = true) → 0 ≤ (ts.map (fun t => t.w)).sum
  | [], _ => by simp
  | t :: ts, h => by
      simp only [List.map_cons, List.sum_cons]
      have h1 := ok_w n t (h t (by simp))
      have h2 := wsum_nonneg n ts (fun s hs => h s (by simp [hs]))
      linarith

theorem tri_hT_packed (n W : ℕ) (hW : 1 ≤ W) (cs : List (List TriT))
    (hok : cs.all (fun ch => ch.all (TriT.ok n)) = true)
    (hbd : 12 * gsum wterm cs < ((2 ^ (W - 1) : ℕ) : ℤ))
    (cF : ℤ) (hc : gsum cterm cs = cF)
    (LF : ℕ) (hl : gsum (lterm W) cs + offL W n = (LF : ℤ))
    (QR : List ℕ) (hq : gsum (qterm W n) cs + offQ W n = (packRows W n QR : ℤ))
    (hQR : (List.range n).all (fun a => decide (QR.getD a 0 < 2 ^ (W * n))) = true) :
    ∀ y : ℕ → ℝ, (∀ i < n, 0 ≤ y i ∧ y i ≤ 1) →
      0 ≤ evq n (Tri.ofPacked W cF LF QR).cT (Tri.ofPacked W cF LF QR).lT (Tri.ofPacked W cF LF QR).qT y := by
  have hok' : ∀ ch ∈ cs, ∀ t ∈ ch, t.ok n = true := by
    intro ch hch t ht
    have h1 := List.all_eq_true.mp hok ch hch
    exact List.all_eq_true.mp h1 t ht
  obtain ⟨ts, hts⟩ : ∃ ts, ts = cs.flatten := ⟨_, rfl⟩
  have hok'' : ∀ t ∈ ts, t.ok n = true := by
    intro t ht
    rw [hts] at ht
    obtain ⟨ch, hch, hmem⟩ := List.mem_flatten.mp ht
    exact hok' ch hch t hmem
  have hg : ∀ f : TriT → ℤ, gsum f cs = (ts.map f).sum := by
    intro f
    rw [gsum_eq, hts]
  have hbd' : 12 * (ts.map (fun t => t.w)).sum < ((2 ^ (W - 1) : ℕ) : ℤ) := by
    have := hg wterm
    unfold wterm at this
    rw [← this]
    exact hbd
  have hw0 := wsum_nonneg n ts hok''
  refine Tri.coef_ok n (Tri.ofPacked W cF LF QR) ts hok'' ?_ ?_ ?_
  · show Uu * cF = Uu * cS ts
    have : cS ts = gsum cterm cs := by rw [hg]; rfl
    rw [this, hc]
  · 
    have hv : ∀ a < n, -((2 ^ (W - 1) : ℕ) : ℤ) ≤ lS ts a ∧ lS ts a < ((2 ^ (W - 1) : ℕ) : ℤ) := by
      intro a _
      have := abs_lS_le n ts hok'' a
      rw [abs_le] at this
      constructor <;> linarith [this.1, this.2]
    have hP : (LF : ℤ) = ∑ a ∈ range n, (lS ts a + ((2 ^ (W - 1) : ℕ) : ℤ)) * bp W a := by
      have e1 := sum_lS W n ts hok''
      have e2 := offL_eq W n
      rw [← hl, hg, ← e1, e2]
      simp only [add_mul, Finset.sum_add_distrib]
    intro a ha
    show Uu * dec W LF a = Uu * lS ts a
    rw [dec_of_pack W hW n (lS ts) LF hv hP a ha]
  · 
    have hv : ∀ a < n, ∀ b < n, -((2 ^ (W - 1) : ℕ) : ℤ) ≤ qS ts a b ∧ qS ts a b < ((2 ^ (W - 1) : ℕ) : ℤ) := by
      intro a _ b _
      have := abs_qS_le n ts hok'' a b
      rw [abs_le] at this
      constructor <;> linarith [this.1, this.2]
    have hQR' : ∀ a < n, QR.getD a 0 < 2 ^ (W * n) := fun a ha =>
      of_decide_eq_true (List.all_eq_true.mp hQR a (List.mem_range.mpr ha))
    have key : ∀ a, (∑ b ∈ range n, (qS ts a b + ((2 ^ (W - 1) : ℕ) : ℤ)) * bp W b) * bp (W * n) a
        = ∑ b ∈ range n, qS ts a b * bp W (n * a + b) + offL W n * bp (W * n) a := by
      intro a
      rw [offL_eq, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      rw [bp_add]
      ring
    have hX : ((∑ a ∈ range n, QR.getD a 0 * (2 ^ (W * n)) ^ a : ℕ) : ℤ) =
        ∑ a ∈ range n, (∑ b ∈ range n, (qS ts a b + ((2 ^ (W - 1) : ℕ) : ℤ)) * bp W b) * bp (W * n) a := by
      have e1 := sum_qS W n ts hok''
      have e3 := offQ_eq W n
      have h := hq
      rw [packRows_eq] at h
      rw [← h, hg, ← e1, e3]
      simp only [key, Finset.sum_add_distrib]
    intro a ha b hb
    show Uu * tb W QR a b = Uu * qS ts a b
    rw [tb_of_pack W n hW (qS ts) QR hv hQR' hX a ha b hb]

end Erdos1186Ex

end

namespace Erdos1186Ex

theorem join_ranges {a b c : ℕ} {f : ℕ → Bool}
    (left : ∀ i, a ≤ i → i < b → f i = true) (right : ∀ i, b ≤ i → i < c → f i = true) :
    ∀ i, a ≤ i → i < c → f i = true := by
  intro i ha hc
  rcases lt_or_ge i b with hb|hb
  · exact left i ha hb
  · exact right i hb hc

end Erdos1186Ex

section
namespace Erdos1186Ex
open Finset Erdos1186Night2

/- The middle digit of a product of two polynomials, with the second list of
coefficients in reverse order, is their dot product. The bound on the base
makes carry into this digit impossible. -/
def convolution (n : ℕ) (x y : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ range n, ∑ j ∈ range n, if i+(n-1-j)=k then x i*y j else 0

theorem middle_digit (n base bound : ℕ) (hn : 0 < n) (hb : n*n*(bound*bound) < base)
    (x y : ℕ → ℕ) (hx : ∀ i < n, x i ≤ bound) (hy : ∀ i < n, y i ≤ bound) :
    ((∑ i ∈ range n, x i * base^i) * (∑ j ∈ range n, y j * base^(n-1-j)) / base^(n-1)) % base =
      ∑ i ∈ range n, x i*y i := by
  have hd (k : ℕ) : convolution n x y k < base := by
    apply lt_of_le_of_lt _ hb
    unfold convolution
    calc _ ≤ ∑ _i ∈ range n, ∑ _j ∈ range n, bound*bound := by
           apply sum_le_sum; intro i hi; apply sum_le_sum; intro j hj
           split_ifs
           · exact Nat.mul_le_mul (hx i (mem_range.mp hi)) (hy j (mem_range.mp hj))
           · exact Nat.zero_le _
         _ = _ := by simp; ring
  have he : ∑ k ∈ range (2*n), convolution n x y k * base^k =
      (∑ i ∈ range n, x i * base^i) * (∑ j ∈ range n, y j * base^(n-1-j)) := by
    unfold convolution
    simp only [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [sum_comm, mul_sum]
    apply sum_congr rfl
    intro j hj
    have hik : i+(n-1-j) ∈ range (2*n) := by have := mem_range.mp hi; simp; omega
    simp only [ite_mul, zero_mul]
    rw [sum_ite_eq, if_pos hik, pow_add]
    ring
  have hdigit := digit_pack base (by omega) (2*n) (convolution n x y) (fun k _ => hd k) (n-1) (by omega)
  rw [← he, hdigit]
  unfold convolution
  apply sum_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  have e (j : ℕ) (hj : j ∈ range n) : (i+(n-1-j)=n-1) ↔ j=i := by have := mem_range.mp hj; omega
  calc _ = ∑ j ∈ range n, if j=i then x i*y j else 0 := by
         apply sum_congr rfl
         intro j hj
         by_cases hji : j=i
         · simp only [if_pos hji,if_pos ((e j hj).2 hji)]
         · simp only [if_neg hji,if_neg (fun h => hji ((e j hj).1 h))]
       _ = _ := by simp [hi]

structure GramPacking where
  n : ℕ
  width : ℕ
  offset : ℕ
  scale : ℤ
  value : ℕ → ℕ → ℤ
  forward : ℕ → ℕ
  backward : ℕ → ℕ
  total : ℕ → ℕ

def GramPacking.digit (p : GramPacking) (i k : ℕ) : ℕ := (p.value i k + (p.offset:ℤ)).toNat

def GramPacking.readDot (p : GramPacking) (i j : ℕ) : ℤ :=
  let v := ((p.forward i * p.backward j) >>> (p.width*(p.n-1))) % (2^p.width)
  p.scale^2 * ((v:ℤ) - p.offset*((p.total i:ℤ)+p.total j) + p.n*(p.offset:ℤ)^2)

def packFold (base : ℕ) (coeff : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => packFold base coeff k + coeff k*base^k

theorem packFold_eq (b : ℕ) (f : ℕ → ℕ) (n : ℕ) : packFold b f n = ∑ k ∈ range n, f k*b^k := by
  induction n with
  | zero => simp [packFold]
  | succ n ih => rw [packFold,sum_range_succ,ih]

def packSum (coeff : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => packSum coeff k + coeff k

theorem packSum_eq (f : ℕ → ℕ) (n : ℕ) : packSum f n = ∑ k ∈ range n, f k := by
  induction n with
  | zero => simp [packSum]
  | succ n ih => rw [packSum,sum_range_succ,ih]

def GramPacking.check (p : GramPacking) (i : ℕ) : Bool :=
  let b := 2^p.width
  let digit := p.digit i
  (List.range p.n).all (fun k => decide (- (p.offset:ℤ) ≤ p.value i k ∧ digit k ≤ 2*p.offset)) &&
    decide (p.forward i = packFold b digit p.n ∧
      p.backward i = packSum (fun k => digit k * b^(p.n-1-k)) p.n ∧ p.total i = packSum digit p.n)

theorem GramPacking.dot_correct (p : GramPacking) (hn : 0 < p.n)
    (hb : p.n*p.n*(2*p.offset*(2*p.offset)) < 2^p.width)
    (i j : ℕ) (hi : p.check i = true) (hj : p.check j = true) :
    p.readDot i j = p.scale^2 * ∑ k ∈ range p.n, p.value i k * p.value j k := by
  unfold GramPacking.check at hi hj
  dsimp only at hi hj
  rw [Bool.and_eq_true] at hi hj
  obtain ⟨hib,hiw⟩ := hi
  obtain ⟨hjb,hjw⟩ := hj
  have Bi (k : ℕ) (hk : k < p.n) := of_decide_eq_true (List.all_eq_true.mp hib k (List.mem_range.mpr hk))
  have Bj (k : ℕ) (hk : k < p.n) := of_decide_eq_true (List.all_eq_true.mp hjb k (List.mem_range.mpr hk))
  obtain ⟨hif,_,hit⟩ := of_decide_eq_true hiw
  obtain ⟨_,hjr,hjt⟩ := of_decide_eq_true hjw
  simp only [packFold_eq,packSum_eq] at hif hjr hit hjt
  have h := middle_digit p.n (2^p.width) (2*p.offset) hn hb (p.digit i) (p.digit j)
    (fun k hk => (Bi k hk).2) (fun k hk => (Bj k hk).2)
  unfold GramPacking.readDot
  rw [Nat.shiftRight_eq_div_pow, pow_mul, hif, hjr, h, hit, hjt]
  apply congrArg (fun z : ℤ => p.scale^2 * z)
  push_cast
  rw [mul_add, mul_sum, mul_sum]
  have he (a b : ℕ) (hb' : - (p.offset:ℤ) ≤ p.value a b) :
      (p.digit a b:ℤ) = p.value a b + p.offset := Int.toNat_of_nonneg (by omega)
  have hconst : (p.n:ℤ)*(p.offset:ℤ)^2 = ∑ _k ∈ range p.n, (p.offset:ℤ)^2 := by simp
  rw [hconst, ← sum_add_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  rw [he i k (Bi k (mem_range.mp hk)).1, he j k (Bj k (mem_range.mp hk)).1]
  ring

end Erdos1186Ex
end

section
namespace Erdos1186Ex
open Finset Erdos1186Night2

def GramPacking.row (p : GramPacking) (i : ℕ) : List ℤ :=
  (List.range p.n).map (p.value i)

theorem GramPacking.row_value (p : GramPacking) (i k : ℕ) (hk : k < p.n) :
    (p.row i).getD k 0 = p.value i k := by
  simp [row, List.getD_eq_getElem?_getD, List.getElem?_range hk]

theorem gram_scale (s : ℤ) : ∀ a b : List ℤ,
    dotL (a.map (fun z => s*z)) (b.map (fun z => s*z)) = s^2 * dotL a b
  | [], b => by cases b <;> simp [dotL]
  | a::as, [] => by simp [dotL]
  | a::as,b::bs => by simp only [List.map_cons,dotL,gram_scale s as bs]; ring

def quickDominance (t : Tabs) (p : GramPacking) (i : ℕ) : Bool :=
  decide ((packSum (fun j => (t.NT i j - p.readDot i j).natAbs) p.n : ℤ) ≤
     2*(t.NT i i-p.readDot i i))

theorem dominance_of_packing (t : Tabs) (p : GramPacking) (hn : 0 < p.n)
    (hb : p.n*p.n*(2*p.offset*(2*p.offset)) < 2^p.width)
    (hl : t.crows.length = p.n) (hr : ∀ i < p.n,
       t.crows.getD i [] = (p.row i).map (fun z => p.scale*z) ∧ (p.row i).length ≤ p.n)
    (hp : ∀ i < p.n, p.check i = true) (i : ℕ) (hi : i < p.n) (h : quickDominance t p i = true) :
    domRow t i = true := by
  have dot (j : ℕ) (hj : j < p.n) : dotL (t.crows.getD i []) (t.crows.getD j []) = p.readDot i j := by
    rw [(hr i hi).1,(hr j hj).1,gram_scale,dotL_eq_sum (p.row i) (p.row j) p.n (hr i hi).2]
    rw [p.dot_correct hn hb i j (hp i hi) (hp j hj)]
    apply congrArg (fun z : ℤ => p.scale^2 * z)
    apply sum_congr rfl
    intro k hk
    rw [p.row_value i k (mem_range.mp hk),p.row_value j k (mem_range.mp hk)]
  have hh := of_decide_eq_true h
  change ((packSum (fun j => (t.NT i j - p.readDot i j).natAbs) p.n:ℕ):ℤ) ≤ _ at hh
  rw [packSum_eq,Nat.cast_sum] at hh
  unfold domRow
  apply decide_eq_true
  rw [absSumRow_eq,hl,dot i hi]
  simp only [zero_add]
  convert hh using 1
  apply sum_congr rfl
  intro j hj
  rw [dot j (mem_range.mp hj)]
  simp

end Erdos1186Ex

namespace Erdos1186Ex

def GramPacking.scaledRows (p : GramPacking) :=
  (List.range p.n).map (fun i => (p.row i).map (fun z => p.scale*z))

theorem GramPacking.row_eq (p : GramPacking) {i : ℕ} (hi : i < p.n) :
    p.scaledRows.getD i [] = (p.row i).map (fun z => p.scale*z) := by
  simp [scaledRows, List.getD_eq_getElem?_getD, List.getElem?_range hi]

def readGram (bits bias word i k : ℕ) : ℤ :=
  if i < k then 0 else ((word >>> (k*bits)) &&& ((1 <<< bits)-1) : ℕ) - (bias : ℤ)

end Erdos1186Ex

namespace Erdos1186Ex

/- The chunked tables are proposed witnesses. Only natural or integer data
are materialized here. The coefficient identities, triangle sums, row
encodings and Gram bounds below are all independently checked in the kernel. -/
def natTable (n : ℕ) (f : ℕ → ℕ) : List (List ℕ) :=
  (List.range ((n+11)/12)).map fun a =>
    (List.range 12).map fun b => f (12*a+b)

def tableAt (t : List (List ℕ)) (i : ℕ) : ℕ := (t.getD (i/12) []).getD (i%12) 0

def natWord (n w : ℕ) (f : ℕ → ℕ) : ℕ :=
  (List.range n).foldr (fun k v => (v <<< w) + f k) 0

end Erdos1186Ex

namespace Erdos1186Ex

/-- Coefficients of the symmetric Gram-matrix proposal. The finite coefficient
checks below compare each entry to the polynomial before any division. -/
def proposedEntry (t : Tabs) (g : Grid) (tr : Tri) (a b : ℕ) : ℤ :=
  let p := mkPD t g
  let f := mkFD t
  let linear := fun i => (p.lP i - f.lF i - tr.lT i) / (2 * Uu)
  let quad := fun i j => p.qP i j - f.qF i j - tr.qT i j
  if a=0 then
    if b=0 then (-Uu * (∑ i ∈ Finset.range t.n, t.czr.getD i 0) - f.cF - tr.cT) / Uu
    else linear (b-1)
  else if b=0 then linear (a-1)
  else (quad (a-1) (b-1) + quad (b-1) (a-1)) / (2*Uu)

/-- Accumulate the three off-diagonal coefficients of each signed triangle
at its proposed row. The packed-polynomial identity checks every coefficient. -/
def triangleRow (w : ℕ) (basis : ℤ) (ts : List TriT) (i : ℕ) : ℕ :=
  (ts.foldl (fun z t => z + (if i=t.i then
      4*t.w*(t.s1*bp w t.j+t.s3*bp w t.k) else 0) +
      (if i=t.j then 4*t.w*t.s2*bp w t.k else 0)) basis).toNat

end Erdos1186Ex
namespace Erdos1186Ex
open Finset

def sumInt (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | k+1 => sumInt f k + f k

theorem sumInt_eq (f : ℕ → ℤ) (n : ℕ) : sumInt f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp [sumInt]
  | succ k ih => rw [sumInt, sum_range_succ, ih]

def sparseCz (d : PD) (i j : ℕ) : ℤ :=
  if d.sgz i * d.sgz j = 1 then
    if Qn = d.th i j then 0 else 75*(Qn-d.th i j)*(4*d.lenz i*d.lenz j-d.a4z i j)
  else if d.th i j = 0 then 0 else 75*d.th i j*d.a4z i j

theorem sparseCz_eq (d : PD) (i j : ℕ) : sparseCz d i j = d.cz i j := by
  unfold sparseCz PD.cz
  split <;> split <;> simp_all

def czQuick (t : Tabs) (g : Grid) (i : ℕ) : Bool :=
  decide (sumInt (sparseCz (mkPD t g) i) g.N = t.czr.getD i 0)

theorem czQuick_eq (t : Tabs) (g : Grid) (i : ℕ) : czQuick t g i = czRowChk t g i := by
  simp only [czQuick, czRowChk, sumInt_eq, sparseCz_eq]

def fastU10 (d : FD) := sumInt d.A2 d.n + d.pp
def fastU20 (d : FD) := sumInt d.A4 d.n + d.rr
def fastLinear (d : FD) (a : ℕ) : ℤ :=
  Uu * (d.Yv a - d.Ov a - sumInt (d.OO a) d.n - sumInt (fun i => d.OO i a) d.n
      + sumInt (d.YO a) d.n)
    + Rr*(d.om a*fastU10 d - d.Lo*d.u1 a - d.om a*fastU20 d + d.Hi*d.u2 a)
    + d.ss*d.om a*(d.Lo+d.Hi)
def fastConst (d : FD) : ℤ :=
  Uu * (sumInt d.Ov d.n + sumInt (fun i => sumInt (d.OO i) d.n) d.n)
    + Rr*(-d.Lo*fastU10 d + d.Hi*fastU20 d) - d.ss*d.Lo*d.Hi
theorem fastLinear_eq (d : FD) (a : ℕ) : fastLinear d a = d.lF a := by
  simp only [fastLinear, FD.lF, fastU10, fastU20, FD.u10, FD.u20, sumInt_eq]
theorem fastConst_eq (d : FD) : fastConst d = d.cF := by
  simp only [fastConst, FD.cF, fastU10, fastU20, FD.u10, FD.u20, sumInt_eq]

def linearQuick (t : Tabs) (g : Grid) (tr : Tri) (i : ℕ) : Bool :=
  decide (2*Uu*Nmat t 1 (i+2) = (mkPD t g).lP i - fastLinear (mkFD t) i - tr.lT i ∧
    2*Uu*Nmat t (i+2) 1 = (mkPD t g).lP i - fastLinear (mkFD t) i - tr.lT i)
def constantQuick (t : Tabs) (g : Grid) (tr : Tri) : Bool :=
  decide (Uu*Nmat t 1 1 = -Uu*sumInt (fun i => t.czr.getD i 0) g.N - fastConst (mkFD t) - tr.cT)
theorem linearQuick_eq (t : Tabs) (g : Grid) (tr : Tri) (i : ℕ) :
    linearQuick t g tr i = linChk t g tr i := by simp only [linearQuick, linChk, fastLinear_eq]
theorem constantQuick_eq (t : Tabs) (g : Grid) (tr : Tri) :
    constantQuick t g tr = constChk t g tr := by simp only [constantQuick, constChk, fastConst_eq, sumInt_eq]

def quadCoeff (t : Tabs) (g : Grid) (tr : Tri) (i j : ℕ) :=
  (mkPD t g).qP i j - (mkFD t).qF i j - tr.qT i j
def quadQuick (t : Tabs) (g : Grid) (tr : Tri) (i j : ℕ) : Bool :=
  decide (2*Uu*Nmat t (i+2) (j+2) = quadCoeff t g tr i j + quadCoeff t g tr j i)

theorem quadQuick_swap (t : Tabs) (g : Grid) (tr : Tri) (s : ∀ a b, t.NT a b = t.NT b a)
    (i j : ℕ) (h : quadQuick t g tr j i = true) : quadQuick t g tr i j = true := by
  unfold quadQuick at h ⊢
  have he : Nmat t (i+2) (j+2) = Nmat t (j+2) (i+2) := s _ _
  rw [he, add_comm (quadCoeff t g tr i j) (quadCoeff t g tr j i)]
  exact h

theorem pair_from_upper (t : Tabs) (g : Grid) (tr : Tri) (n : ℕ)
    (s : ∀ a b, t.NT a b = t.NT b a)
    (weights : ∀ i j, (0 ≤ t.thT i j ∧ t.thT i j ≤ Qn) ∧
       0 ≤ t.YYT i j ∧ 0 ≤ t.OOT i j ∧ 0 ≤ t.YOT i j)
    (rows : ∀ i < n, (List.range' i (n-i)).all (quadQuick t g tr i) = true) :
    ∀ i < n, ∀ j < n, pairChk t g tr i j = true := by
  have upper (a b : ℕ) (ha : a<n) (hb : b<n) (hab : a≤b) : quadQuick t g tr a b = true := by
    apply List.all_eq_true.mp (rows a ha)
    rw [List.mem_range']
    exact ⟨b-a, by omega, by omega⟩
  intro i hi j hj
  have he : quadQuick t g tr i j = true := by
    rcases le_total i j with h|h
    · exact upper i j hi hj h
    · exact quadQuick_swap t g tr s i j (upper j i hj hi h)
  have hw := weights i j
  exact decide_eq_true ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, of_decide_eq_true he⟩

end Erdos1186Ex
end

section
namespace Erdos1186Ex.R4

open Erdos1186Ex
def lowWords : List ℕ := [0xe0340c02c0a0240882007018050100300801000,0x1c06c1a06418c60170581505013048110400f83c,0x2b0a8290a02789c260942408c220842007c1e074,0x3b0e8390e0370d8350d0330c8310c02f0b82d0b0,0x4a1244811c461144491043108411003f0f83d0f0,0x5a1645815c561545414c521445013c4e1344c12c,0x691a0671986519063188619846017c5e1745c16c,0x781dc761d4741cc721c4705c06f1b86d1b06b1a8,0x862148420c8220480a007f1f87d1f07b1e8799e4,0x8821c]
def low (i : ℕ) : ℤ := 2 * (((lowWords.getD (i/16) 0 >>> (10*(i%16))) &&& 1023 : ℕ) : ℤ) + 0
def highWords : List ℕ := [0xe0340c02c0a0240801e07018050100300801000,0x1c06c1a0641805f170581505013048110400f03a,0x2b0a8290a02709a260942408c220842007c1e074,0x3b0e8390e0370d8350d0330c8310c02f0b82d0b0,0x4a1244811c461144410e43108411003f0f83d0f0,0x5a1645815c561545414c521445013c4e1344c12c,0x691a0671986519063188611826017c5e1745c16c,0x781dc761d4741cc721c4701bd6f1b86d1b06b1a8,0x862148420c82204801fe7f1f87d1f07b1e8791e2,0x8821c]
def high (i : ℕ) : ℤ := 2 * (((highWords.getD (i/16) 0 >>> (10*(i%16))) &&& 1023 : ℕ) : ℤ) + 8
def lengthOfWords : List ℕ := [0xfff5ffff,0xff2ffff5,0xff5fffff,0xffffffff,0xfff5ffff,0xffffffff,0xffff5fff,0xffff8fff,0xfff5fff5,15]
def lengthOf (i : ℕ) : ℤ := 2 * (((lengthOfWords.getD (i/16) 0 >>> (2*(i%16))) &&& 3 : ℕ) : ℤ) + 2
def signOfWords : List ℕ := [0xaaa82aaa,0xaa800002,0x2aaaaa,0,0xaaa80000,0xaaaaaaaa,0x2aaa,0xaaaa8000,0x280002,0]
def signOf (i : ℕ) : ℤ := 1 * (((signOfWords.getD (i/16) 0 >>> (2*(i%16))) &&& 3 : ℕ) : ℤ) + -1
def alphaWords : List ℕ := [0xc48d14181000000004102050e24,0x3448502000030e2c7911a2418000,0x547890600003123ca9b3a6cc9522,0x9519f377102450b183466b53a136,0x6ca939e24180000c48f2754da14e,0x9d6b368c16284880e1bbe8d2a742,0x64d9d36547890600003123ca9b42,0xc48d223c58706000010a246912a,0x284080800000000830a1a2418000,0x121c]
def alpha (i : ℕ) : ℤ := 2638827906662400 * (((alphaWords.getD (i/16) 0 >>> (7*(i%16))) &&& 127 : ℕ) : ℤ) + 0
def betaWords : List ℕ := [0xbbcef7bc633bde73bdef,0x7bdef021ef7bcef7dca5,0xbdef7296f7bdca739def,0x39de77bdef7bce5bdef7,0xbdcb7bdca5bdee5bdee5,0xbdca77bdef7bcef39cb7,0x39ce5bdef7296f7bdef7,0xbbde77bdef401ef7bdef,0x79cef79c637bde77dca5,495]
def beta (i : ℕ) : ℤ := 659706976665600 * (((betaWords.getD (i/16) 0 >>> (5*(i%16))) &&& 31 : ℕ) : ℤ) + 659706976665600
def yv (_ : ℕ) : ℤ := 0
def ov (_ : ℕ) : ℤ := 0
def a1 (_ : ℕ) : ℤ := 0
def a2 (_ : ℕ) : ℤ := 0
def a3Words : List ℕ := [0,0,0,(0x9f8000000000000000b02c31668e98e031 <<< 59),0,(0x62131ccd1d8621604000000000000013f <<< 60),0,0,0,0]
def a3 (i : ℕ) : ℤ := 131072 * (((a3Words.getD (i/16) 0 >>> (14*(i%16))) &&& 16383 : ℕ) : ℤ) + 0
def a4Words : List ℕ := [(0x470fc99 <<< 98),0,0,0,0,0,0,0,(0xf2651c3 <<< 126),0]
def a4 (i : ℕ) : ℤ := 131072 * (((a4Words.getD (i/16) 0 >>> (14*(i%16))) &&& 16383 : ℕ) : ℤ) + 0
def yyValWords : List ℕ := [0x1320280b01b25813c3580b0b80180382c02a02410800,0x1282841312f1aa338a080c1a43c81f85d2a61b08684c,0x1c82482d04a1900045496e2466d55800f36008818066,0x2aa3a5768a70a46844d8104a23fc400c52d26b4098ac,0x10c73422034112050639e52ee628ef81e03a4c84d1f4,0x1da6806d0e22de9601a8bf71102ca80f71847980d17f,0x92064a789e1182203c93d1de214981100e018c3a8fb,0x1596c90521c4ad2a84e05016060802]
def yyVal (i : ℕ) : ℤ := 131072 * (((yyValWords.getD (i/16) 0 >>> (11*(i%16))) &&& 2047 : ℕ) : ℤ) + 0
def yyRowsChunks : List (List ℕ) := [[(0x6000000000001200000000000000004172c1c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000015 <<< 399),(0xa000000000000000000000000000000019 <<< 812),0,0x1400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000,(0x7000000000000000000000000000000000000600000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003 <<< 42),(653 <<< 64),(27 <<< 77),(0x27000b <<< 616),(0x7cf1d <<< 616),(0x108000000000000000000000000000000000000000000000000000000000000002000000000000000003 <<< 100),(0xc0500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002a2080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d <<< 112),0],[(0x6000000000000000090000000000000000000018000000000000000000000000000000000000000000023 <<< 595),(37 <<< 602),(0x13800000000000000000000000000000000000000987 <<< 603),(0x140f <<< 609),(0x2b00000000000000000000000000000000000000000000000000000000000000000a949 <<< 347),(0x2400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b968002b <<< 457),(0x182f <<< 455),0,(49 <<< 791),(25 <<< 792),(0x90000000000000000730000000000000000d198d <<< 777),(0x6c0000000000000000000000000000000000000035 <<< 616)],[(0x1c37 <<< 609),(457 <<< 613),(0x4400000000000000000000000000000000000000000000000000000000000000000e743 <<< 338),(0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000023b <<< 434),(0xb80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003e00000007af <<< 436),(0x2c6400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001f008bf <<< 434),(0x1c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002141 <<< 441),(7 <<< 987),(0xc59340000000000000000000000000000000000000000000000000000000000000000002243 <<< 581),(0x6600000000000000000000000000000000000000000000000000000000000000000045 <<< 588),(0x300000000000000001ad800000000000000000e80000000000000000000000000000000000000000011e3 <<< 596),(0x1380000000000000000000000000000000000759 <<< 766)],[(0x91d800000000000000000000000000000000000049 <<< 609),(0x4c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000025 <<< 330),(0x4d000000000000000000000000000000000000000000000000000000000000000000264b <<< 329),(0x13c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009c1 <<< 317),(0x9fdc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005 <<< 333),(0x1e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000051 <<< 322),(0x1e4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000029 <<< 323),(0x2a53 <<< 672),(0xab55 <<< 672),(0x2c57 <<< 686),(11 <<< 703),(0x55c00000000000000000000000000000000000000000000000000000002d59 <<< 462)],[(0x152b000000000000000000000000000000000000000000000000000000005cb64c9001 <<< 444),(0x29d50000000000000000000000000000000000000000000000000004b000be02f5d <<< 455),(0x299726301885e1 <<< 448),(0x35ead3a0000019f3 <<< 449),(0xc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000037ee01b4000d80c1 <<< 449),(87 <<< 445),(0x200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009 <<< 441),(0xe1f <<< 959),(0x1e0000000000002b <<< 903),(0x16740000000000500000000000006ae1c91000000000000000000000000000000000000000000000000000000000000071 <<< 581),(0x261e00000000000000dc80000000000000000012404d <<< 749),(0x4a380000000000000000000000000000000011c000000000000000000000000000000000000000003d <<< 603)],[(0x4600000000000000000000000000000000000023 <<< 778),(0x2245 <<< 784),(0x2180000000000000000000000000000000000000000071 <<< 616),0,0,0,0,0,0,0,0,(57 <<< 512)],[(0xe45 <<< 513),(0x35ef <<< 651),(0x1229ab7 <<< 652),(0x1832e9 <<< 658),(0x1400000000005c000000000000000000000000000000000000000000000000000000019346d <<< 651),(0x22000000000016800000000000000000f800000000000000000000000000000000172fe3 <<< 665),(0x10000000000000000000000000000000000000000000000000000000000000002d5b <<< 679),(0xb00000000000000000000000000000000000000000000000000b24ef6201b <<< 653),(0x58bc000000000000000001e000000000000000000000000000000012ba2f383 <<< 651),(0x204200000000000000000000000000000000061cc085 <<< 645),(0x180000000000000000000000000000000000000008f48c1000000000000000000000000000000200000003809 <<< 637),(0xede3f <<< 812)],[(33 <<< 952),0,0,0,(21 <<< 1015),(1 <<< 995),0,0,0,0,(21 <<< 904),(0x5200000000000000007 <<< 834)],[(0x200000000000000001d <<< 834),(0x3000000000000000000013 <<< 751),(0x952c05 <<< 739),(0x4e01469 <<< 722),(1 <<< 744),0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,(1 <<< 957),0,0,0,0,0,0,0,(13 <<< 945),0,(3 <<< 954)],[0,0,(27 <<< 973),(5 <<< 981),(13 <<< 981),0,0,(3 <<< 987),(1 <<< 994),0,0,0],[0,0]]
def yyRows (i : ℕ) : ℕ := ((yyRowsChunks.getD (i/12) []).getD (i%12) 0)
def proposed_yy (i j : ℕ) : ℤ := yyVal (((yyRows i) >>> (7*j)) &&& 127)
def yyPacked : List (List ℕ) := eval% natTable 146 (fun i => natWord 146 64 (fun j => (proposed_yy i j).toNat))
def yy (i j : ℕ) : ℤ := Int.ofNat ((tableAt yyPacked i >>> (64*j)) &&& 18446744073709551615)

def ooValWords : List ℕ := [2]
def ooVal (i : ℕ) : ℤ := 25296896 * (((ooValWords.getD (i/16) 0 >>> (1*(i%16))) &&& 1 : ℕ) : ℤ) + 0
def ooRowsChunks : List (List ℕ) := [[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0x10000000,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,(1 <<< 119),0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0]]
def ooRows (i : ℕ) : ℕ := ((ooRowsChunks.getD (i/12) []).getD (i%12) 0)
def proposed_oo (i j : ℕ) : ℤ := ooVal (((ooRows i) >>> (1*j)) &&& 1)
def ooPacked : List (List ℕ) := eval% natTable 146 (fun i => natWord 146 64 (fun j => (proposed_oo i j).toNat))
def oo (i j : ℕ) : ℤ := Int.ofNat ((tableAt ooPacked i >>> (64*j)) &&& 18446744073709551615)

def yoValWords : List ℕ := [0x930be06b1a83030c302e0461a625828c0a500b00c01f000,0x2563b635914f3a51fe21039a1be1080d20511320a112b00d,0xdf28725918c3e202a1932e306c3ea0142421d8033187008,0x2a054007a2e752b2d638311e21d0f504424529430105e3e6,0x1eb480581a9ced2e6ecc200172e37f4459612297c7718182,0xd110904c23d36f0fe02f0ab22d1bb1253af1ed1b1453118,0x38800506e0ae39813632d0d52070e51fa30a02434f0d7018,0x5cc0a75231980e139b1c81aa2612400af0cb28f00f2d7096,0x6a23501c1d913741c095643022578]
def yoVal (i : ℕ) : ℤ := 131072 * (((yoValWords.getD (i/16) 0 >>> (12*(i%16))) &&& 4095 : ℕ) : ℤ) + 0
def yoRowsChunks : List (List ℕ) := [[0x80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001,256,0x200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000,0x1000000,0x3000000000000000000000000090000000100000000,(1 <<< 40),(5 <<< 49),(11 <<< 56),(3 <<< 66),(13 <<< 72),(0x8880000000000000000000780000000000007 <<< 81),(0xa00098000000000000009 <<< 89)],[(0x585400000000000000081 <<< 98),(23 <<< 104),(5 <<< 112),(3 <<< 123),(25 <<< 128),(13 <<< 137),(27 <<< 144),(0x747 <<< 146),(15 <<< 161),(31 <<< 168),(265 <<< 173),(0x1180000000000000000011 <<< 105)],[(9 <<< 194),(0x272600000000000000000025 <<< 120),(5 <<< 211),(0x2a29 <<< 216),(43 <<< 224),(11 <<< 234),(0x2e2d <<< 232),(0x302f <<< 240),(0x3231 <<< 248),(51 <<< 264),(0xd800000000000000000000000000000000000000000000d4d <<< 274),(0x3837 <<< 280)],[(0x3a39 <<< 288),(0x3d3c3b <<< 296),(0x201f9f <<< 305),(0x541 <<< 312),(0x21a1 <<< 321),(0x1151 <<< 330),(35 <<< 337),(0x4847 <<< 344),(73 <<< 352),(37 <<< 361),(75 <<< 368),(19 <<< 378)],[(0x2683 <<< 377),(0x4f4e03 <<< 376),(0x52515 <<< 388),(0x45453 <<< 392),(0x7575655 <<< 392),(0xb8b6b40000000000000000000000000000000000000000b2b <<< 235),(0x661605f00000000000000000000000000000000000000005e5d <<< 232),(0x31b1 <<< 441),(0x198000000000000000000000000000000000000000000000000000000000000000000000001959 <<< 450),(0x6867 <<< 456),(105 <<< 464),(0x35800000000000000000000000000000000000000000000035 <<< 281)],[(0x1bdb800000000000000000000000000000000000000000001b40000000000000000000001b <<< 194),(0x717 <<< 484),(0x3a3980000000000000000000000000000000000000000000000000000000000000000000000039 <<< 201),(0x7507 <<< 504),(0x3bbb <<< 513),(0xf2f <<< 523),(0x3d800000003d <<< 529),(0x1f400000000000000000000000000000000000000000000000001f <<< 330),(0x3f8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003f <<< 129),(259 <<< 559),(0x41c1 <<< 561),(0x21e1800000000000000000000000000000000000000000000000000000002161 <<< 570)],[(0x11200000000000000000000000000000000000000000000000000000000011 <<< 579),(0x88000000000000000000000000000000000000000000000000000000000089 <<< 344),(0x8485000000000000000000000000000000000000000000000000000000008687 <<< 344),(0x8283 <<< 592),(0x8081 <<< 600),(0x7e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007f <<< 616),(0x7c000000000000000000000000000000000000000000000000007d <<< 624),(0x7a000000007b <<< 592),(0x7879 <<< 632),(0x7677 <<< 640),(0x775 <<< 648),(0x1c8000000000000000000000000000000000000000000000000000000000000000000000001cdd <<< 658)],[(0x7071 <<< 672),(0x6c00000000000000000000006d000000000000000000000000000000000000000000006e6f <<< 680),(0x6a00000000000000000000000000000000000000000000006b <<< 688),(105 <<< 696),(0xced <<< 699),(0x323280000000000000000000000000000000000000000000000000000000000000000000000033 <<< 409),(0x6263 <<< 712),(0x2eaf00000000000000000000000000000000000000002fb03083 <<< 729),(0x161640000000000000000000000000000000000000001696d7 <<< 738),(0x55565707 <<< 744),(0x14d501 <<< 754),(0x2828a9 <<< 761)],[(0x34e4f <<< 768),(0x64d <<< 776),(19 <<< 786),(75 <<< 792),(37 <<< 801),(73 <<< 808),(0x8e9 <<< 811),(35 <<< 825),(0x4445 <<< 824),(0x4243 <<< 832),(0x4105 <<< 840),(0xf8fd <<< 846)],[(0x3b3c3d <<< 848),(0x1c9d <<< 865),(0x6e7 <<< 875),(0x1a1a800000000000000000000000000000000000000000001b <<< 697),(51 <<< 896),(0x1899 <<< 905),(755 <<< 916),(0x1697 <<< 921),(11 <<< 930),(43 <<< 936),(0x1495 <<< 937),(5 <<< 955)],[(0x250000000000000000002627 <<< 952),(9 <<< 970),(0x2200000000000000000023 <<< 976),(0x2021 <<< 984),(31 <<< 992),(15 <<< 1001),(0x1c1d <<< 1008),(27 <<< 1016),(13 <<< 1025),(25 <<< 1032),(3 <<< 1043),(5 <<< 1048)],[(23 <<< 1056),(0x201000000000000000a8b <<< 985),(0x48000000000000004c005 <<< 994),(0xe0000000000000f0000000000000000001011 <<< 936),(13 <<< 1088),(3 <<< 1098),(11 <<< 1104),(5 <<< 1113),(1 <<< 1120),(0x10000000900000000000000000000000003 <<< 992),(1 <<< 1136),(0x8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001 <<< 49)],[(1 <<< 1152),(0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001 <<< 547)]]
def yoRows (i : ℕ) : ℕ := ((yoRowsChunks.getD (i/12) []).getD (i%12) 0)
def proposed_yo (i j : ℕ) : ℤ := yoVal (((yoRows i) >>> (8*j)) &&& 255)
def yoPacked : List (List ℕ) := eval% natTable 146 (fun i => natWord 146 64 (fun j => (proposed_yo i j).toNat))
def yo (i j : ℕ) : ℤ := Int.ofNat ((tableAt yoPacked i >>> (64*j)) &&& 18446744073709551615)

def thetaLoWords : List ℕ := [0xc183050a10203040c1020204000,0x1e3870d1a3060b16285091020386,0x2e5cb162a50a132648911224080f,0x3e7cf1e3a74e1c366cd1a3264c18,0x509d3a64c952a4488d1a24485020,0x60bd7ae5cb56ad58b15aa54a54a8,0x70e1bb76cd9ab568cd9b264c58b0,0x7efdf3d7af1e3b76eddba74e9cb9,0x8f1a3458b121c3870e1428306040,0x2447]
def thetaLo (i : ℕ) : ℤ := 1 * (((thetaLoWords.getD (i/16) 0 >>> (7*(i%16))) &&& 127 : ℕ) : ℤ) + 1
def thetaHiWords : List ℕ := [0xe1c3060a14285080c1820404080,0x1c3870d1a3468c182c58a1224408,0x2e58b152a509932448891204078f,0x3e78f1d3870d9b3668d193260c17,0x4e993254a912234689121428101f,0x5ebd72e5ab562c56ad52a52a5428,0x70ddbb66cd5ab468cd93262c5830,0x8101fbe7cf5ebc78eddba74e5cb8,0x8f1e3468b1a2c4890e1c2850a141,0x2448]
def thetaHi (i : ℕ) : ℤ := 1 * (((thetaHiWords.getD (i/16) 0 >>> (7*(i%16))) &&& 127 : ℕ) : ℤ) + 73
def thetaEdgeValueWords : List ℕ := [0x1e035d3c06b2f570b9bd27a55d75eeae89451f8409c3b7cf37eb1bbb4bb441a562cc24a0cca121dd1800000]
def thetaEdgeValue (i : ℕ) : ℤ := 131072 * (((thetaEdgeValueWords.getD (i/16) 0 >>> (23*(i%16))) &&& 8388607 : ℕ) : ℤ) + 68267933696
def thetaIndex0Words : List ℕ := [0xffff06ff4effffff4d03ff4bff4aff00,0xffffffffffff0cff0bff0aff52ff51ff,0xffffffffffff5cff5bffffffffffffff,0xffffffffffffffffffffffffffffffff,0xff6fffffffffffffffffffff22ffffff,0xffffffffffffffffffffffffffffffff,0xffffffffff36ff35ffffffffffffffff,0xff3fff87ff86ff85ffffffffffffffff,0x47ff46ff8e44ffffff43ff8bffffff40,0x91ff]
def thetaIndex0 (i : ℕ) : ℤ := 1 * (((thetaIndex0Words.getD (i/16) 0 >>> (8*(i%16))) &&& 255 : ℕ) : ℤ) + 0
def thetaCode0Words : List ℕ := [0x903000ba010604,0x80702050d0,0xe0000000,0,0xc0000000000c000,0,(7 <<< 41),0x502070800000000,0x6010ab000309000d,64]
def thetaCode0 (i : ℕ) : ℤ := 1 * (((thetaCode0Words.getD (i/16) 0 >>> (4*(i%16))) &&& 15 : ℕ) : ℤ) + 0
def proposed_theta (i j : ℕ) : ℤ :=
  bif (thetaIndex0 i).toNat == j then thetaEdgeValue (thetaCode0 i).toNat else
  bif (thetaLo i).toNat.ble j && j.blt (thetaHi i).toNat then 0 else 1099511627776
def thetaPacked : List (List ℕ) := eval% natTable 146 (fun i => natWord 146 41 (fun j => (proposed_theta i j).toNat))
def theta (i j : ℕ) : ℤ := Int.ofNat (min 1099511627776 ((tableAt thetaPacked i >>> (41*j)) &&& 2199023255551))

def gramWordChunks : List (List ℕ) := [[0x7c957,0x224af3f763,0x113d4612173f54d,0x89aab041e611f13f2c2,0x43525858050418611df3f196,0x2150ac3513819e30416a11dabf145,0x10df0206cdc318e81975040b611ba3ef1c,0x87d3306e9a186dc12fa818c903f9e11873ebba,0x4591a7d0dafe139fb663cb407e71afc0edeec140f35,0x22184409528098efb4b5f24ebfbee7f33cfe101f7c0bff64,0x10a989fb82bf641824b300fda0242c03b780c6301fca08c33f5cf,0x884c503bb9fc083eb8a82cd909f960479407568188903f3211743ea73],[0x4460d82bb5043b1f7953e7c382829012de0498c0797819230403211a1bed7c,0x22073c0c5782585027c1f6b43ec9684d0d0138a04ac407c181983040ce11be3ef64,0x113d8a080640e878304905591f8643e5228156b0149204cbc080281a1d041ca11eb3f262,0x8c1710135609b5c0f8a834c105655f8bd3e272800410135204a6407b3819650409a11b53eec4,0x4735c801530118e098540e8a8321b0617df8713e27b7ff5101182046fc07428185b03eea1166be98e,0x22807400038012f00a4e04f1407b8815390301dfc25bf1407ff6d0084e022ac038580beb01f0a089fbf37a,0x1138e9fe6b3fbf17f79efea85f94a3f1ec7f532fbf8a0482401f27fc7eff23dfd7f3fb857f2c2fe1b9f8463f394,0x8e13effe55fd993fae87f6cafe4fdf38c3e8787b8bef710a0032c03df7f96afe549fb16bf73d7e5fafc431f0afbe97e,0x4681c81adf00c55fce3bf8ff7f184fd741f15bc001b7b93af72260053c03db7f9d4fe615fb2ebf76f7e670fc4edf0d1bebc6,0x237604054d800d30129dfc873f7cf7f0a0fd295f2df3e41a7ad4efe53e008bc03d47fa84fe765fb563f7c27e732fc62df10b3ef97,0x116cb6033440cb1811f3020e5faef3f2d37e3b4fb4d5f9aabe6717ca00fe8ea0114403aa7f96efe791fc37bf8227e812fc79df14dbf404,0x89f15025560505c12b3818d901a61fa383eff47dc82fa399f9b7bd92a7f686fe75600ca403cd7fb4afe8e5fb82bf81f7e80cfc791f14bbf3e1],[0x455b4810b7035da04e240b0c8154f01795fa893f0f97df00fb5f9ec8cbeff37f5dafe5ca009c403d27fab8fe7c9fb61bf7da7e76afc689f11c3f0b8,0x22c89bffdd81a590426e062dc06458119b01305fab3bf1867df92faa15ebca3fd2b7fb14fb0c20073403d77fa38fe6d5fb453f79e7e6defc5a1f0f23edf0,0x11c51e0148c050e80f8b0318a06c240c3c81bdd021c9f86a3ec627d25cf8d49f8523fa837f416fe1c20022c03e17f938fe4e9fb0bbf7267e5c4fc3d5f09f3e867,0x8bba300d5a0227405f9809eb023ba05c740ae48182d01df1f9d83ef527daa4fa345fe5f3fbe87f720fe976001e402e87faf6febc5fc4bbf9627ec60fd2f9f47bbee94,0x441217fe38ff915fe593fcc27f9d6ff021fd7bbfad17f428fef0201bd404ee80c6b001ae0084c00a68035b00475ffc93ff5e7ff89003ce010ac01ad805c300f3204413f8bc,0x235ccc00677dfbefdd61f7fc3ef1f7da84fc719f8a23f1627dc1cfbd9e06814118782b5aff63dffe1bfcd8836a5014bdff7cbfd6c7ff370114e0469c07368183d03eba115e3e8fd,0x113d45ffabbfed77f57afdf45f9873f2a17e488fba8df6423ec3a7d556fc2f607914152f8020d0094e02bec04c48074701705ffc1bfd6380011012f2049b4079c8192f0404211a53edb5,0x8ac4b09429ff3abfe637f500fddddf94dbf2437e3f8fb8f5f5f23eb867d3a2fc09e077cc1506801eb0097a02b4c0496806cd015f1ffa13fd677ffa90122a0483c076c818bb03f8a11833eb76,0x46fce81958fff9e0007bff807f0b4fd5b5f890bf0457de40fb0a9f598beb1a7d3bcfbf0a079540068802130094a02c0c04cc8075b01735ffc73fd638002301316049ec07a5819410406211aabee17,0x2335c403b380041008e600e8c00687f1a4fd881f903bf1017df5efb3d1f6383ec817d720fc3b207be400bb80257008f602d5405278084f019620008bfd5b800f1014a204cd4080581a25041d611edbf28c,0x11867e0149400fc803410145e01c3401627efe6fd551f8dd3f0607dd22fb0ddf6493ecd87d892fc50a0060400fd8028d008b202e5c05708091301b22003d3fd5480197015e204f2c085481add043021223bf626,0x8adad009e2017c4016c803f9016d201fec019f7f026fd611f8fbbf0927dd6efb1b1f6733ed377d978fc642006ac01138029f0089a02eb405888095301bb2004e3fd52801cf0164a04ff4086d81b19043661235bf754],[0x453e4811d5010620264c034e80717022160316c02aa7eeccfd3edf8fabf0327dbf2fadb5f65d3ed427dacf0054e0079c0130802b70087e02f2c05a9809ab01c7a0065bfd4f80219016da050fc089081b6b043ea124dbf8f0,0x232ffc14948078d00c9a01dbc021f8052701b760276402057ee20fd1edf8a93efac7db26fab75f5eb3ec427d865001fa005cc00f680287008ba02e440568808fd01aee00373fd5580185015be04eec084b81ac7042e2121e3f5c1,0x11ca6a13b4c02bd808a500e92022b4029c8063f020420269c02697e968fc7c1f79b3ed2b7d514fa181f5563e8237ffb4ffd6e0034c00a5802450090a02cfc050f8080f018d1fff7bfd5d800bb0143a04c1407ec819eb0417611dcbf166,0x8ffa907e320023c0204805c7008ba0158400c980347016120172c016b7e860fc4adf71cbec5d7d3daf9e09f4a73e6987fbfcff85200084004b801fb0096602b9404ab8070501671ffb03fd657ffd901286048e40782818f103fde1192bec7f,0x4927a8302500cde005c402b48071b00b2201afc01528045f01af20123401bf7e3eafbbc1f69f3e9d27c900f8e9df3883fc5d7f8e2ff40dffe2c0000801bf009b202a6c04588062701475ff74bfd6d7ff1d0111e0464407298182103e8a1155be86b,0x24c2ac0ed6818f2ff3e9fff9c0218804af0063200fdbffc8801dd0125a0052c00e97e30cfb929f634be9247c7f8f8bb1f2f43fb107f5befefbdffbcbffb48017f009fe0293404048054501271ff383fd747fe5d00fae0439406d08174f03d321117be449,0x12901605b0bf9077f70eff30dffddc0274803db0040600a13feaf8001b00dadff24400407dcfefab21f4213e5af7c09af7f3dfc893f83d7eeeefe65dff6abff0f800f900aa6026a4034d8035b00e19feb53fd847fcbd00c9203dbc060d8158503a461090bdb4f,0x8be2b07b11fe79bfd427fd5affb6e0049401c9804270068a00f4400c18025b00eba0051c00e57ef4cfd7f1fa723f3777e140fc24dfecc3fd507fa58ff725ffd83ffcd800b50050e0146c01f48027d008e5ff923febb7ff0f0079a02154035980b8501e5e08813f172,0x48bd67fed6ff049fe6bbfe1f7f8b8ffa9dfe38bfcda7f396fe761fc323f84a7f188fca5dfc11bfabf80ddd0200a053640cec821c3004cdff57bfdc87f8ceff689ff10bfe0d7fdecfff3dfec43fc9e7f858fed01ff9cc01ff7fb2afefadfd32bfae57f14cfdf51f7d7bec37,0x25da13f5507fa6efd5adfbb03f9d17ee12fee09fb993f7237e238fc5cdf7783ef0b7e1aef8e31f70cbf55781edd04a020d12c1d778083300c85ff433fcde7f4c0ff165fe473fc677fc14ffe31fd9bbf9917f190fdc01ff75c03f67f714fe0cdfa90bf6257e368fbffdefed3dc92,0x131bf5f7243f5b77fab0fd751fbf1bf8787eeb8feeb5fbb93f7557e302fc769f7b23ef8b7e27ef90fdf750bf59c81f2704ada0d3541daf8088b00d79ff733fd4a7f5c4ff2cdfe53bfc807fc28ffe15fda1bf9ad7f1dafdca9ff89403f37f752fe145fa9e3f6427e3aefc06df001bddea,0x98ae6fbf39f7ddbf6e67c122fc56dfb90be70b7eaa0fe729fac13f4af7dd32fbc9df673bed467dfa4f8569f5ebbf4ea8234b051d60d80c02338095500fb5ffe43fe497f82aff619fe70bfcba7fc58ffdddfdb03f9ed7f286fde31ffb7c03ee7f7e4fe25dfabf3f6867e44efc171f0313e113],[0x4ae347e3c0fd5a9fa9bbfa2a7f86cfdd59f5733fac57e43cfe845fba83f61c7e2e0fc829f8153f0e07e584f998df7d4bf6e182557057e60e7a403ca80bc301692013e401557ff8700035fec93fd6c7fceaffd25fddd3fab37f496fe2e60044c03dd7f9a4fe5b9fb23bf7597e63cfc499f0c2beac2,0x2428cc0cfd7ef40feb89fd4dbfd407f85efd625fbc4bf9637e962fe7adfb38bf4837e05afc3ddf7b2bf06d7e572f97c9f754bf7128264705f1e01c5c050b80dad01bfa024ec03bc805510082dff0ebfdf97fd5cffc99fe003fb4e7f636fe69a00b4403cf7fb06fe861fb733f7ff7e7c0fc715f1353f264,0x1142ae1704bfee67f696ff951ff01bff7a7f6e0fd33dfb623f82c7ecc2fe3f5faf4bf3557df28fc20df80e3f1437e77ef9ee5f6d3bf8007f9fb060d6022b4058f80e0901e1e02f3c05408093100d49fcb63fe617fdb2ffc2dfe1a3fbc27f76cfe95e0107403c57fc0cfea59fbae3f87a7e8e2fc8edf18abf812,0x8670d1296e064cc001b7f9c6fff6dffc3400727f6ccfd459fb71bf8297ecc0fe315fadb3f2c57de88fc12df87a3f22a7e8f4fa40df8633f870829a100b92023cc058380d6d01dce0329405cc80ac700f31f9b13fe957fddcffbf9fe273fbfb7f804feaba0130403c07fc8efeb51fbcb3f8b77e970fc9d9f1b4bfadd,0x42b0685fd30af660219c031d8010500a3e0122402097f902fe015fc923fa037f0f6fe8e1fbc73f4c77e43cfcc49f9153f3b17eb60fab75f94b3f94282db1012be031dc073d811070256e042d407f280f7b01629ff80bfef07fe26ffb9dfe3e3fc607f910fed1e0178403b87fd72fed05fbfebf9227ea6afcb71f1febffca,0x21cbf42921831d906f5a035940567804d90117a0204403297f7b8fdc11fc36bf9397efeafe60dfb953f4197e36cfcae1f902bf39a7ebbcfac9df86fbf993807df0147a036ec07cc812010280204a2c08ef811d50194dffa0bff227fe60ffbb5fe573fcad7f9c6feec601adc04077fdd8fede5fc1c3f95d7eafefcc85f239401e5,0x10b5de209142eae8117502ade043840634805390118e0200c02da7f64afd555fbb3bf8557eeb2fe411fb8b3f44e7e3d8fcb4df902bf3a47e6a2fd95df806bf8f480693011a6036ac08408140f02bda04dac08f28116f017b9ff683fecb7fed2fff6dfecfbfd487fa44ff0560205c07d57fbf0feb71fbf9bf8f47ea82fcd35f2bc3f624,0x8a4c506181fbb642da7816830363a050b40672803df00d920178401ac7f516fcd2dfb363f7aa7ee4afe485fc033f6707e7cefd1bdf990bf1fd8069efc061f78bc01538047f00d660389c095381833033ee05764096c811d50165dff0e3fe477ffbd00619ffb3bfe817fb7aff3e602bcc0ec87f8b6fe775fbca3f8547e9e8fcef1f3c23e219,0x46e9f80da701c3e02e540ee68115f0293e03e9c0585803bd00e6e019c402497f6c4fd5d9fbd23f8ac7ef76fe619fbdfbf5827e5fcfcefdf9523f3bb7eb3efad25f813c022d806630116a0382c088c814ed02db2050ec09418120f01845ff603fec37ff0500075fef8bfd8a7fa9eff146022ec08f77fb8afeb09fbf9bf8ea7ea8efcdb9f2f23f397,0x233f640a1781315024760287c0e4e80cbf02446035fc04cb8029f00dfe0191402777f5c4fd379fb573f7ab7ec52fe021faacbf1b27de1cfc0e9f7e23f1797e914fa23a0275c01928062d0102202f54071e8110f0249a03ee4074e80dd30135dff4dbfe747fdacffc5dfe90bfc7f7f832fed9201cac04537fab4fed85fc6d3f7e37e9c6fcaddf202bf9ac,0x1152860e42408eb8170902c7e028fc0d4680d85028e604134067b806bd014f60272403a17f6aafd939fbd93f86e7ee0afe1f5faf83f2177dfe0fc499f86f3f2bc7eb3cfa976031dc0252806ab0116e030a4070f810930247a0421407d980f73015d9ff8fbff047fe6effcbdfe97bfd017fa10ff0360176c03637fd88fef8dfc963fa1f7eda6fd39defa53ff09,0x8c903046da02c740af681d7100e82033fc105c811cf0375a05c54092e80b4701dfe038f404f77f3b2fd091fae9bf6667ea18fd8f1f9d1bed4b7f7e6fb94df749bf2917ce8b018e60244401768068d0107602bfc06a38101d022da03aa406cb80cb101255ff67bfeac7fdeeffbe1fe2d3fc157f848feb520142403be7fcc8febbdfbd83f8d27e9aefca41f1c73fc1c],[0x46aaa7fa71012a6025cc09e98197f005ce0303410fc80f5102c8e04494060a8042701206020dc03087f2acfc91dfa453f5797e726fdbf5f77dc020a7d6ccfb399f67bbf0c97cba300ef201524007d8058b00d760244c05da80ee901f7602ff405498090f00d55ff3bbfe547fda6ffc3dfe173fbb37f742fe90200fc403c77fbeafea15fba6bf86a7e8bcfc8b1f17f3f753,0x232da4020c8015b0140602e3c0b17810d500f5e0333411a3811d7034e605a7c06fa8070f0167a02a2403f57f3acfcf85fac23f6387eab2fd169fc9a3ee3a7d838fb6c9f7233eed5805150156e0209400fd8049300c720780c05d680ee301f6602fb40541808fb00d39ff3abfe527fda6ffc3dfe16bfbb17f73cfe8f200fac03c77fbe4fea0dfba5bf8687e8b6fc8a9f17dbf738,0x118a0e031bc023a802f901c5603a4c0b4080bd50050a03c4c1369813b103b2a05e7408cf8094d0195202f3403ce7f34cfcbc1fab83f6517e9fefda81fa163efc07db00fbb71f77d3ef29804b9015de019540084805cd00e7e0246c078f8148f02b66044540590809d900d29ff6b3ff057ffd5003f9fedfbfdc87fb7efd49a01a14080f7fa8cfe8d5fbadbf8537e90efcae9f256bee69,0x8af8f015560211c0a948126b014de037840afc8117702dca02f9c0f26811910332a0576408ee80b5701d9e0385404f97f51efd5ddfb77bf7767ec68fdd75fa643effb7dc60fbea1f7954045b81ab6fbf55fe703fb07806d30144202e6c06e38107f023ee03e0c074580ddb013edff75bfec87fe06ffbc5fe343fc347f89afec120158c03bb7fd0efec45fbe83f8f37e9fcfcabdf1de3fda2,0x444b781a2b0267e0475c0bba814e10283e05f9409db80555024260252c0d4f810f302a860460407a6808fd0198e0304404727f612fd815fbcbbf8337ee4afe1a1fb0ebf2327e044fc579f832406b780418fd749f06bbfeaa807a30136603254075181159025f60435c07fb80f9901695ff9abff1e7fe82ffc0dfe27bfc697f8e4fec960159c03c97fe96fedfdfba2bf92f7ea8afcba5f207c0067,0x2251541671802250272e0461c0ae4812590126a034b40c5982681002fa06a4c0cdc7f98703a920637c0a3980e09021d2040c405867f520fd729fb8ebf7867ec86fdcf5fa52bef877dc10fbe4e035e406347fe98f963a02b6c01eb80707011e202fa40703810af0247603fb4078280e6b014b5ff7c3fed67fe10ffbb9fe37bfc437f8c4fec6e0163c03ba7fd30fec89fbefbf9037ea22fcafdf1e93fe62,0x1130fa11ccc0972804050153e022b408e180df301d3e04bc40f118292b0053e09fe40fac7fa730132a04eac0b6380fcf02466045bc05bc7f466fd491fb56bf70a7ebfafdeb5f96e3ece27d4e2fb14e020a402f380cb2fe64601a44009f8091b015760324407cd813550283a03c9c086c7f718ffe41ff69bfeb07fdf2ffbddfe2e3fc1a7f854feb720145c03be7fcd2febd5fbdabf8d77e9bafca55f1cabfc59,0x8ca1907e86042f40747805f301522025c4096a80e3702062052e40ea580e0f06f11fee2c11fa84290ffa320111c0aa6810b30270604acc06127f19cfcaf9fa593f50f7e7e8fd5e5f879be9f87d03500d56014bc0208801810081a00dcbffdc80739010b202834069c81111022be0302c065c7f88500419ff3a3fe517fda4ffc41fe163fbb07f73afe8ee00fa403c77fbe2fea05fba4bf8667e8b2fc8a1f17cbf729,0x47e337fde9007e2011140b5280da50130602d540a2e8073902a3e0611c0f68816310185a05424194b80b8506d7e01da3f9f180f7d0270204a9c05d27e628ff57df9353f2f17e2f6fca71f7cebe651804650092a00ac4008e7fefefffea00703ff04804d300af601eac059180fb301a0e01ae4025080279006c9ff19bfe497fe6cfff99fe5f3fc3f7eea4fe5920095403d37faa2fe7a1fb5d3f7d07e754fc665f1153f042,0x23ded3fa697f56b0061604274056280ebd0174e03b340acb809db03016069c40d5b8124700c2e04dd417a18264f01d5e0255409eb80b3101d26036fc04467f026fc319f9a33f3f27e536fcfc9f894be8fe807f700d46002ebff817fce0ff855f9fbbfe718071700f82023b406738121701ff202224031980342fef2604a7bfe247fe1effefdfe44bfbf47f024fe552008dc03d47fa8afe771fb57bf7c57e738fc639f10d3efbb,0x11f5c1fffabfd027fd830150202f1c0a5580f0f0242a052b408cc810a902c2a06944104380c71094fdfea1c0f5b7e1b704fc207e7c0b4d80cf50211e03ea404ce7eda8fba59f8cc3f2397e0fafd02df503c03cb8027900321ffddbfedb7fc60ff6a1ff163fe27804d700a120182c04e780e4101c3e01ddc0295801d2fdbcdfeecbfdbe7fd4cffd5dfdfd3fb257f42cfe48e0076403d77fa42fe6e5fb473f7a27e6e8fc5b5f0f53ee25,0x91030ff581fd08bfc4f805e500256028d40c8a814790105e03964040e80a730320e0622c0e0a8105afdd5606b9c2221808d50029606b8c08ec80769018fe02e3403a37ebd8fb165f7e6bf0b57dd6efcae9f42b401a1800befff81ff5abfda57fa76ff079fe6ebfd85802750044a00cbc037280b3d0151600f3c00ad7fdf0ffe09feb5bfd467fccaffd4dfdd33fa887f424fe1e20026c03e07f944fe501fb0e3f72c7e5d2fc3edf0a33e8ac],[0x471117f8c8ff345fe1cbfdea81b2b00d3e033c40c8a814c7016820395c063680cf10318a0626c0dae819b1005be08f740e3481939025c60639c079a804090138a0233402b57ea7efaae1f72ebef9a7df3cfa861ff87c00fe7fe32ffa55fea03fc087f7d6fe775fd943fca48018b00192005c402bc80a27012060058bff507faa6ff981fe8e3fcf67fc8affd9dfdbf3fa307f338fdfc9ffe7403e87f87cfe37dfae13f6cd7e4f4fc281f0623e456,0x226f1c077c7fd90fefb5ff9ebff7b7ffa1008d201584061e80961010d6023dc04288078d01712032fc07648146902a420549bfac980c350226a0342c041c802b700aea013e401887f55cfd631fba93f7e77efdefd471ffd0400927ff68ffdc9ff663fe357fc3aff4d1fee43fe6d800e30011e003b401748053500962003ebffd27fdb8ffd4dff4c3fe857fe4cffec5fee23fd227f9b8ff025fffb401f37fc56ff1edfd763fb727f294fe16df838bf2b0,0x113d11fc7bbf9787fbf8ffdedff3b3fec27feb0ff8e1ff70bfd267fbe2ff4b9fe3dbfbdd7fbeafed45fd67bfa777f624fee15fe3e3f8ce7f590fdb69fbf23f8d27f480fe4b5fcaa3ff42808bf01b020326406a681375001c600924021b804390073e00cdc010680151007ca0049400367fa4eff3ddff14bfe137fbaeff63dff2c3fe2e7fd2affa1200134005e801f1008c6029740481806e3015c5ffc73fd8980015011ea0458c072f817c303c9e0066bf2b0,0x8decf03a89fae9bf88f7f39eff1d5fd4dbfb7c7fa74feca1fe6cbf90c7f634fe509fc3c3f7247f5a2fdca5fb3c3f4bf7eb9efda91fc933f0667eb94fb9c1f82e3f2ba7ebaafcd8200043f75a812f103ae606f4c0e9982a070094602284074680f3301ab602e8c0435804fd01a5a008ec00ae7f3e6fe37dfcacbf9907f512febd9fdef3fa9e7f702ff0660151c03ea80bc301fbe0479c0b3981a6f02fa1fb0bc00d8816ed017fa04e04201681ad4fffde00bd3e456,0x481fc80a32fed55fdf0bf92e7f380feeb5fd4f3f9b67f7f8fe9e9fd3a3fc327f4a4fe62dfb4b3f68a7f2eafd9d5fa6e3f64c7eff2fe2bdfcc1bf2047ee42fc1c9f9543f38b7ef38fcfbdfa20bf76e813c7040a2081e4124c806350097e0266c071a8110f01ef603e140664809df02b86047dc02ee7ef7afe16dff90bfe627f8f4fe215fdfbbfc547fd58ff805ffd140019802950171e0b0e411558024304eb604f7beaf87f09f082da1266bff2d7feff0014600fe3e8ac,0x240853fbb57fb8f002e1fd02bf64c7eec4fe5c9fc9abf9307f53cfe559fd7cbf8f17f294fe585fae73f5047f072fda75facabf6917f294fe60dfc2dbf2c17ecacfbd25f90d3f3f37eefefd3f9fa9f3f8c3811df0385607834112780579008320292c07f3812870214a0446c06bb80b4f0334a0204c03507eadcfd2d1fc0b3f6767e646fdc4dfdf13fca47fb6aff1a9ff953feb47ff1d00b0a0730409fd82a0f04a5df90b3e5ad7fd32ffd01fff33ffa4800170030e0150bee25,0x11e955fb5c3ff587fc7500de5fcf73f65e7ee84fe429fc3bbf88c7f418fe685fd4f3f82f7f1e4fe089fafc3f5fa7efe8fdea1fb6e3f5d67eceafe035fc2f3f19a7ef28fc4d9fa2cbf67e7f1c6fdc91fbc63fa298127103c420911401d9808b700b660366409a98183902c5a0597c097b80ef30401e0295404327eb4efd54dfcc43f7f47ea32fe835ffe2c004280460ffdb20056400ab803ad0146a082040d63833bd05899f797bfb9d7fd3cffa75ff523fe9b7fca4ffa3a03f83efbb,0x8ee6cfeeb5ff723fa287fd4f009d1fc63bf6947f0defe161fb81bf6147f4dafe22dfc333fccd7f516fe0f9fbe1bf89d7f324fe221fc67bf7fc7f498fe6a1fee2bef0b7f48cfd735fae2bf6387f432fd251fa92bf6e581bc905f0a0c82c08af81343021360573c0f51823cf041e6077d40d398105b044da0760403ae7f85eff736015d405ba8075cff515febdbf88c7f2a4ff4a203b8c0b4381bdf0530a1111412f77fecaffeea003e400997fd94ffdbe00093ffd280083003be01703f042,0x4694f7f90101bf6026a4046c8198900e91fc5abf5d27f18afe6fdfc173f9827f9defe50dfda73f8327f5c8ff119fcb0bf61f7f5aefdd4dfab23f6107fb52fea91fdcdbec7e7e7d6fb211f5dcbed247e304fbd61f7e6bf490818fb0575203274069e80d0d01c1603c1c0bdf816d5028d603c8c0612803770136200763fed8802d8ffd79fcfe3fa8f7f800fdfddf9a33f2db7e0f4fd6f20738c145a831c10026e00804009a800410024600a2c008d7fed500022005140068801e1005fe01d83f729,0x228b440ee280c3901d8201fa405c780a69012bdfcacbf62e7f0b2fe86dfc89bf9c67f778fe069fd54bf9fb7f2e4fe801fad8bf2ba7f00afd325f920bf59c7fa2cfec95fc873ede17e6ecfab49f5da3eda47e282fc25df87b3f622814bf0476a01774035d8066b00f76020f4070480c590159601b1c02128044b016be026a401907f87efe8d5fb24bf5c87ea62fcc4df8dcbf1b47e0fefd2ca0780400108006f0020e0098401048015d004ca00eec00847ffc5001ee0086c00d9802e9007ae0225bfc59,0x1113820feb3fde9812a101c16020bc068980e3f01811fcd33f5437ec18fe745fcacbf90e7f3fafdb55fc583f9ab7ef96fdef1f9a53f1467eb9afcfd1f8b63f55c7f5d0fe505fb733f1747e358fa841f6723ef367e61afc94df9573f79881c5f008fa00eb4020a803bb0089e01254039f80c41015da02fec04928087d026e203bc402f17f4bcfe189faac3f4427e5defc31df865bf1167e15f00fda0013c00358008d001ea00a1c012e801cb005c6010c4008080023002a2009c4010580351008560244bfe62,0x8855901505ff984056d815290156e027040819813bb02379fc61bf5237eb9cfde95fc223f78e7f0b8fe12dfb433f8b97ebe2fdb01f924bf1a37e818fce2df94cbf5f07f52efea49fb2ebf1377e7aefb709f8ed3f46a7f0c4fdf09fc0f3fb8d8197b005a200433ffee80394ffef60231405ab812ed0230604e34087380f3903f8e0530c05327ef92fd831fa37bf1df7dc88fb775f86ebfa6580d85011f600264005a800ab001c200ab4015780239006c20129c007c800810035600b140131803b9008fe0262c0067],[0x44c58800e2feb9a019940a3c8167300b7601e34085a81359024b1fc32bf48b7ea2cfda71fbedbf7017ee90fe095fb40bf8f17eae8fd6f1f90abf1b17ea1ef9d71f97cbf5567eff2fe5f9faa23f1627e9cefbb61f9ff3f6ff7f20cfea75fd783fdd47fc8affa820035bff5a806c5003f202fbc07ad817b702c12055540ab38130904e8a057b406617e904fcad5f8b9bee7e7d1c4fa91a029a4052880b6d00f12000d4002780081001f6009e4011e801a30056a0101c008180001002620094400f58032b0081a02393fda2,0x229483f3807fdc901302064ec0dca80c4300a7202c2c082c80ef702379fc143f1e57e652fd8d1fbbf3f6b87f636fd4fdfb48bf9927ebecfc2bdf8e7bf0db7e45cfd879fa95bf5007e404fd379fb243f3227eedafcc0dfbc7bfb787fa98ff7b1ff0f3fc36802a100d660272c041c80f150153e058840fb78275afdc5a081640f5e8183f066060726c073c7e140fb585f40ebe7ec809cd0156a0296c04928098b00b4dffbbbffa2800e90064e011ec01a7801cb00646014a404d57fd7effeee0059c00558023d0084202b1bee69,0x1154e9fe01bfc3a8016f009fe032a4021d80d4f01c7e03e9c0ac480f7b0253dfbe3bf4ad7eb68fd635fbe6bf7097e9c2fcd29fa4bbf8097ea98fcf7df8d33f1a97ed8cfd5edfac8bf63c7f024fe3d9fc013f00e7ec7cfce0dfb723f87d7f7a2fe509fcd3c01aa809f30283e04bc408bc8153b023760658413937f83904ba209394103f817870622206f3c065e7e9c0fb9d1fbf03f90f80d3d01359feb33fbe77f8fcff51a01e2c054780dc301f55eea1c009c800450024e00a3c008d7fed7000260051c0069801e50060201d8bf738,0x8b486fd689fe1dbfc17802fd010ea0402c049b8154b0165e02f5c0950811df023ddfc01bf53d7ed52fdb99fb713f8f17ebd2fd17dfd423ef8b7eb9cfdf09fa36bf0077f252fe2ddfc75bf5df7f28afe105fbdebed567ed08fbec1f9cb3f5977f2dafdcb201aa40167808b9023e6044dc07c881523022920692c143b7fc4904eaa09ae410e98191506945fcc0bfe607f2ccfe4d9fdf03fd147f326fefadffaabff5e80174ffcae009140176803acf484200814009e8004b0025a00a54008c7fedd000320052c006b801e90060a01da3f753,0x458547fe79006c1fe5d3feac80931019ca02e240b58815f501ed2039bc09cf810c102175fb893f4f97ebbafcf25fbe43f9337f51eff669faa33f75a7f54eff345ff0dbf5bd7f1b8fd139f9b63f28b7f23cff031fb5cbe9907e1fcfb009f6e3bf61b7f2b4fdc720196c0074808e10207e04654088b80d970320601ab4143682def053b60a453fd147fe34ffa4e00c7401af7fd22fe9f9ee0bbff817fd050010a0161402bf807a7006da00163f9107cfe5002120097400ff8014f004ae00eb400847ffb9001da0084c00d3802dd0079a02223fc1c,0x22420c0719805610128a0044c04b2812cd022d203a0c0acc818bb02b76033a407af8147302009fd1b3f9b37f998fe9d5fee33ff287fd44ff755fe533f7dd7d898fede9fb1fbf2f97ebaafcae9f901bf26c7f330ffb65f9e2be8477ee80fa379f7b9bf2127ecd70003a0013bfed980c7d02ce6055540a438198702dd2080c417d783486ffaf5ffadbff18804830130a00d5401ad7e1bafe3b1fffb3f8ba8000b001be00894016f802e9003d1ff72bed7f7fc74ff865ff3c3fd567f894ff50200d23ee6a80041002de00a2c0113803730088e024e3ff09,0x1137e60ec4c0578805b500b86038440b8c820230230e070c40b6f81557025ba0470c09cd80dbf01c4e02d4c016d7fb26ff985fe9abfc3c7f1fcfef11fe6b3f2fa7eac6fd94df92dbf5287ef3cfca91f8473f00b7ccc2fe2b1f0b2c05a47de68fa059f5f7bef2c7e924ff259fe673fcaf8125104142076b40e77822cf037ba0ceb402de808b50105202fa4055b8079f01f320266c0205800030011e00ae401b68044b00b8e0178402a98058d00bf5f92ebffd68004500101ff763ff237ffdeffad5faa6401b37ff5b001820086c00ce802f500836025e3f9ac,0x8be96fd891fb514045580c51019ee07d2c1152826a702e960591c07e0812c5030d2041d4079680e3b01611feb83fdbc7fb96ff79dfe503fc017f93efe1bdfbde3f6437eda6fe211fa61bf4767eecefcc8df8aebf22d7f306fe4d1fb9bbe7a87e172fa2e9f5b23ee577e71cfeda1fdcd3fbcf813ad043d20793c0f3f82b3b008c601ca404f680cad0175202ca404e0806cd01caa02b1c01c68028d00696015a4037580859010c60190402cf8048700a0dff40bfe447fd14ffba1ff143fd0f7f8f0ff1edfd2ebf37a7fe7d0012600a5c00eb803bd00b16034d3f397,0x44ef17ebc6fd47a01e54049b80bc5014a202414118b81c3b042720958c0b358063d020a605c2c075480f0f01a79fdc33f8407f142fee71fc7f3f8f77f7befe625fcb53f7897f0d6fd279fa6a3f4eb7ef42fd8e1f9b2bf05e7e06afc7ddfbc8be9337e59afac81f6b2befa07fd90febf5fda23fb2a8134303e52094c40270808a100cb6031e408ef8160b0284e0493c07de809e902ade0312c02137ffbf0032602574060c80f570216e04064070180ea301081ff943ff77801c700b4e01fec030c8038700ba60289409907fba6ffd8e0076c00568031700c4a041d3e219,0x2251fbfce17ec36fdf1dff38c01e880417007820279407f48187b00eb205cd407cc80bd10233e0559408008120501f15fe313fc297f75efef19fd43bf9967f4fcfdd95faec3f47a7e96afd59df94fbf2cc7e9fefc6e1f817bef9d7e9bafdaa5fa803e4a87e072f9f8df5f43ee5b7ff4eff0e9fe47bfc998134b0482e01fec03288095900c1a02b1406b881271022ba0439407f380b3302be20396402fe801c7007720245c051580b8101a4e0394c06d480f01012ddffffc002a8014f0059e0139c02338034b009ae01aec049a7fee10018a00a6400f6803b100a8e03173f624,0x1088a616bfbfa3b7f1f6fedc9fe82c010280092fff660203c027e80fb901636059940196811b7023fdfe9940a27814d9012a9fe103fd3a7f8a2fea15fd463fbbe7f24efd509f96fbf2287e386fd299f837bf07b7e4cefb9cdf6cebee727ece2fe311f948be1727da5ef9945f4743fb867fca8ff1fdfe6ebfd2f803f5017b60271c03d280a1f00c920285405ab810cb0204a04164081c80bf702ca203f8c037c803b700b22022b40488809fd016b2032b4064380e29013a60062c00fc801ff0039600684018e801bf0053600ccc010e804650069dff714015e8042d009e20294401e5,0x8505d0827201b2c0a6d7f646ff6cdfe73bffd97ffb70069e01f7400b780f6f01151fe5440c738148302449fedbc051b809f2ffffdfdc0bfc387f646fe58dfcb6bfac47eff6fcfa5f8fbbf01d7e04efcba1f76b3eee07e2b0fa565fc0fbed287e9b0fdfc5f885be04c7d860f92c9f40c3fb497fc5aff2fa0464404fa803190131201ff403178088300a6a022e404f680ea501c12038f4070280a6502712036b40309802890089201f9404138087b013ea02e7c05d680d0f011520020c004f800a3001ce00a84014a802190067601214007d800650032200aac012380399008ce0259bffca],[0x423f28528509e01f844bfc477fa71002c5fde9c0169801830063a00f53fff780c9f01831fcb8408bf815a900f05ff793fdd680b9302545fd5a3fa417f2acfec55fc4b3fd087ea66fce0df966bf00d7dea8fc41df6a9bed197def2faf81f5323eabc7e45cfd639f7f23dc5d7ea92f6051fc35bfa2c8100f0186e0308c03488020900bee0157c022080625007f201b8c043c80bc10163202bb4052c8076901cd60272402098017f0057e017ac03448073f0106e0237404498095100c2dfff3bfff4800590022a0091400e68010b0041200d9400867ff810016a0077c00b88029f00732020fbfadd,0x2180fc20c081d8704321f9813fbfb7fcf100969fefec0507804870058a014d401dc80df30274a00433f7ba81536ffa2e04c63ff5480a530228dfcf13f8127ef36ff391fbdec01117e6cefcd91fa3ebefd87de80fbf9df641bec087de18fae5df4b9be95a7e12cfce11f7f6bda1a7fc1cf347a03754053e809c500d2dfd3c3fadf8016f007e200f8c0194804cd0068a0176403d280a1f012de0242c0422805b70170601e540178800e9003be0132c02ce8068b00e7201d3c03688073300941ffda3ffc18002f0025e0084c00ad80073002b600b04008b7feff00072005ac007c8020f0064a01e5bf812,0x111c8e24c541af48021af962dfb233fd2f8003d0247e0255c06908103500696026f4040b80e31016e201e5bf5a47f2d4ffdb6049dc086a8164701c69fa173f6f47f97efc1adff9ebfaf2807e4fe161f6f63f0847de36fbc2df5e0beab67ddccfa9c1f3a9be7aa7e140fec99f8323cb337aae1015320161c004b7fe5aff921f1973f6e180034fffa200374007780211003ae00ef402fc806cb00c1a014dc02058024300b3600c6c00517ffb70002e00a0c01df8051f00a6e0108c019e802e300351ffa63ff587ffd9002ca006a400397ff3effff6005d400957fdf8ffe7a001f40000800ef0046e01903f264,0x919c501401fb123f5ee7f170fdce5fc383f49f80988fbf4e07ecc088480bf300511fc724004480d4aff94603cbc062b7e42701ce6036c406d780b170125e01cd3ef787d43aff985fc253f53381e34fd319f6563f1867e29af942df2793e24d7d360fadddf22a3e2947c092ef09df849402c97a69b004b9ff7b3fcc27f67af9379fe783fdbe7fe90ff491ff333fef97fe64fffda0039401dc802530030200053ff2e7fda2ffb55ff45bfec57fe1affb65ffdc4009f8033500505fff7bff377fd18ffb5dff60bfecc7ff650035600473ff9d7fd9effc3dffedc00a37fc96ffbd1ffd03ff5b7ff6b001f6011dbeac2,0x4b0e67cc76f8865f023be6dc7e01cfa59dfde5404d38088305091ffa44016d8033effbe9ff13bf9a87fc40fecb1fe3dc02fa8170901de602b7c06e280ac100f15f6a9beccc7eda4fd6b1faef3f7cb7eb1cfd42df8003ed8e7d344f988df1bdbdfe67cefef8a9dee2b3dba37f711003f1ffa4bce8c7fe44fefa5fd11bf8597ecbcfcb4dfbeebfa697fc78fe685fde9bfd137f9baffafdff52c006e7fca4ff775fe643fb937f7c0fe735fd5cbfcce7fc10ff555fee33ff08800c6ffe29fe9dbfc2b7f5bcff13dff083fe197fed50040a001abfed87fb8eff78dff60400b47fad6ff875ff6b3fe887fd7cffece008c3e113,0x252873c2897da3afa69df6053e8997de90feba1ffa1c05bf80b15057f2012fc04ba80052ffe35ffecbfd4d7fab2fe1f5fc9e3ff63814d10192e01ddc06418080f00a89f534be6f07e330fcc65f8a6bf1227e6c8fc5c5f844be8c37cf9ef8961f000bdc167c4a8fdb6df8a2bf16f7f6f2ffe720012bd01b800cafe06dfd79bda8a7def6fd901fb103f9527fbcafe1f1fd7e3fc757f834ff969ff073fff77facaff3b1fddc3fa667f5d6fe0a1fcbd3fc2a7fb66ff359fe91bfe837fffaffbedfe2cbfb2d7f356fedf1feeb3fddf7fea500446000bbfe977fae2ff601ff32400b97fa44ff75dff4abfe447fcdcffdc6005cbddea,0x125f99e8cfbe0b57d3a2fe61dfcbec00b87e68efde59fec23fe2d806a8fb95602f2c071b8083d00f720099bff4180458fec5dffd5c06bd822df024e6035f4094480d2f0178df97f402b87da20fb73df431bed7a7c618fd2ddfbd33de987c28cf7971eee63f23e7f54efdb05f7c4beef67b9e100f99ede43ffff80c04feb89e7023f5c17e78efd60dfab13f8dc7fb80fdffdfd50bfc327f790ff8bdfee73ffc47fa02ff219fda23f9e67f506fddd5fc793fbe57fb1eff281fe6f3fe4a7ffa4ffaf9fdfcbfac17f252fec89fedebfdc67fe910045e0005bfe7c7fa98ff55dff1ec00bc7fa06ff6e5ff3cbfe267fc96ffd560048bdc92,0x8eae8f4219f31f3ef897ea97033a1fb48bf5847f6e6ffeda007ac000b805f6fe6ea017f4035c804a900ace005cbffe0802e6ff52dffa6402da811e9011be018ac04978068500a4200403f5857ea26fdf8df96a3f8317de12fe8adfe2a3edbb7dffefb759fd15bf86e7fa0afec6dfb8fbf6977dc07003edf72b3fd6981686fd161f85cbf9ca7f104fe67dfcc6bfbb87fd4efecfdfe61bfdb17fac8ffb55ff42bff947fbcaff695fe783fc2e7f940fea9dfdd43fd877fd20ff7f5ff023fece7ff4effc05feb4bfcba7f796ff41dff5cbfebd7ff2900255fff93ff147fcdcff9adff71400627fca2ffabdff88bfee67fde2ffdfe00053ec37,0x44da2801dafff1dff5f3f64e81d80ff0c6013a40a3f80911000fa031ec03eb7fd7700631fd203fbce801a1005aa007c3fd2e803faffd2dfbdebf8347f3f0fe515fc013f7907ed0cfdbea00984053b80f590051a04b04074d808af0341609a84173080cf301d6603ba4068d80f6d01dd20357407e6807330593dffcc403007fda6ff241fe173fb5e7eaacfef7dfde7bfd587ac16ff495ff13bfeb77fd4cffdf5ffbf400597fedaffcd1ff593fe207fc6eff57dfedc3fe967fe3affb3dff88bffaa8009efffb9ff6f3fe5f7fb90ff991ff8c3ff1d7ff79001f60011bff7e7fdf8ffc35ffbdc00587fd94ffc8dffbf3ff587feecfffb20053bf172,0x242c0c158d80132ffef60180406a1834c0ff276020b40c1480385022c6033d404fc7f0e4ff9bdfa5ebf8a78072d01b0e0518c009c7f144fc4f9f42bbea14803b8fb9f5f5cfbeafc7cef6fa7aa038c410d782991024920bac417fe816c10a706095740c5181e0303e820850c0e0a822c30408606dfc0f9d80ebf0a141ffd9c06807fa56fe009fb35bf4d57e550fd179fa1e3f832800c2fbbf9fd25bfbf27f6f4ff819fec93ff947f944ff099fd6bbf96e7f440fdb35fc39bfba37fadaff1b5fe4ebfe157ff54ffa15fdcfbfa5b7f15cfeb39fed33fdaf7fe7d00475ffffbfe627fa54ff4bdff0c400be7f9caff675ff2fbfe0b7fc56ffcee0035bdb4f,0x1216fdf9b3be8d48176302e1e02f1c08c67ee8700f7e0092c07777ff0301f5e00d6c01317f4cd004f9fe1ebfd0c7fecd0059e028b401bc7f5f6fd4cdf658beaea7d9c4fb84df69abebd77d278fb146065dc12608240d05a660ba6416878116b01c720579410568243503dba085f40dec81e2704c16091a413d083334fea460068c05a67fed2ff245fdb03f92e7ef7afe489fc873fb417fc08fecd9f9d23f8cb7fb46ffc99ff9f400e77fe86ffb49feee3fcc57f9b4fede1fdfebfd757fcbeff755ff35bff8f8019500071ff10bfd2e7f82cff499ff253fe547ff05003ce00293ff197fc3cff919ff8f400ae7fb6aff995ff8cbfece7fe20fffda00bc3e449,0x90154fc87df1ba3eb40812ab025520519c037a8082b01b7601c7c054b7fef10248dffb2bfb327f530fe74dfecf3fb5b7f8e6ffade0073402307fa08fe2b9f89bbed117d318fb0a5f647bead97d0c4fb33a07a04153282613057360205404f980eeb028de07ec40e9a825ed04466098fc1278824e5058020b03416ea7fd62ff38a00e24054f801beffe75ff23bfc6d7f6dcfef35fdd9bfcd67fd8aff27dfc873fe837fd44ffeae0001c0183800f300039ffa0bfe4f7fc36ff679fecf3fe4c7fd9cff9edff9fc003c8029f0035dffa43fe7b7fb50ff8e9ff4b3fea17ff4300382003c3ff6e7fd1effb1dffcbc00a77fc2affb01ffb7bff287fef30013200fabe86b],[0x46dc37e510fba99f52a3f0c281fb50377e077940fb7800beffe5a01e5c072a7fefb01902007b3fcbe7fc4aff381feff3f7fa7f09efe799fde6bff2f7f5b6fe4c5f9733ed9f7cc76fa85df5c83ea4d7d0dcfb736073cc15ef8051b00a9e02424050580e45027fa0775c0efd82573046da09bbc137581d37057ce0b8ec180780142ffbba0142404f3804410091a00703ff737fcdaff8f5ff143fe577fef0ff715ff6ebff507ff3b000ba0062c021d803570051600503ffd47feb0ffef5ff9d3ff1f7fe78ffc7e0008c00e8803a50064200363ffc47fe6affd2dff703feec7ff8100336004f3ffc17fdfcffd1a0007400a07fce6ffc6dffe23ff807ffc3002860137bec7f,0x22d3b3f4a47c5aaf996df7e33f2e8822730433a05ff40b9880925005520030c06837f9c300bfe0059bfd0c7ff9700781fef6bf5ef7ea80fdc65fbfebfc6b7f15cfe699f9f2bedc37c7f6fa0c5f54f3e99d7cd56fad7a008e401ac8090f00d3a02b5405c380e6902d3e076ac0f2b825df04e3e0a56c15d48265b05bca0cd64030b8043f0026e01594044b805ff010b6019ac01f58028d002b2004dbfff37ffc6ffd7dffc7bfffa8096cfc3a600d7402d68063700aea0123401a6801a9009260094c001e7ff80fff8e0087401b6804df009ba00e54014e8022300249ff9d3ff467ffc9002da0065c00257ff08fff7a004ec00977fdcaffe2200153ffeb800bd0041e01813f166,0x113cf601e03e6d47de0afd3b1fdd4bfe33815db026d60353405d9801c8ff569fe23bff5e7f30cfe459fc6ebfac37f9a2fede1ffb7bf5927ec5aff4d1fb85bf7b67e640fd791f976becfa7ca20fa3fdf5e03e97c7f840ff072033040ab18111701d1e019340288809890212a062140f05822430487e0983418a280b19053c20c0c402bc80687005ce00d7c02b1803dd00da2018140277804a1005ee00b8c00a5802090068e00e7401bc802bb01561fc81be46f808c30101e01dec03468044f012360170c01008006d0024a00f74026d805f700cce0180c02ad80571006d5ffc53ff968000b0028a0079c007e7fff500196008e4008f7fe92fffa60042400498019b0058a01c2bf5c1,0x86bdefe209fe6bbfdd27fcad001ae00d1403ce800a3000460010bfe3b7f974fed25fcf6bf6a27f5a6fddb9fa5ebfb757f66cfe811ff0c3edc680f60fd4f5fa703f1b97d6acfc331f6a63ef867d56cfacedff613fbc87faa0ff08a044a40e3781355021b20200c02c7807ef021060510c101b81f8b0485209434188c81c8506b39ff68c021b806950084e000fc026c802110076a012b4024a8040b0071200da40134801450036a0096401197ffd301dfdf7e23dbde805f700b1201594026c8037f00e4e027cc025a7fcccffb1e0064c00dc801330068e016fc02ad8068d006bdfff13ffe87dfeb0024e0088c00bf800a30032200bcc008a7ff27000be0063c008f8023d0069201f2bf8f0,0x43c717f436ff93dfdd0c001e800d2ffe51ff993fe5d8060f00629fdf73fc2c80068ffdc5fcd0bfb197f6b4fd2c9fc14c010a7fd56ffcadf820bfc737d0dcfa67df5fabedd97cee6fbb09f552be9877f932ff699ff1ebfc4a7f73afef1e02b94085a8124301fde05acc0a6a8134d034ea08d74159782cb105d0200c0c03d0827170782a015ac03ac8090700aae01674037f805870137a01f1c02f8805230101a01f4402217ff32ffcf9ffedbffcb8010f0010e00a3c02467fb37008d20103401ae8023b009f20074400768030b006a601263f2b88037b00dfe01ae403128067300835ffdabffc780053002d20041c009e8004b0025a00a54008c7fedd000320052c006c801eb0060a01dabf754,0x2216c3e55e7eb7700351ff1fc018d80235001ddfecd3fc97802bf003fdfffd3fc4b801d2ff659ff55401687e0a2fde45fc16c013b7fe0cff959f8d1beafb7d750fc055f8333e59b7c9f0fc455f309c00497f978ff569feeabfbba7f6fefeb8a0303c0932814010234205d8c0ac9814f903c7608cfc16c582cbeff8160bb141865831070087a0161c03be808eb009d2017240436805dd0108201994016e801b7001520027c027d7fdacff771ff573fe977ff8affe1a004ac00f9803090055e00a1c00ee80165006cdfffac0048802570087602cf404de7d55100d16018ec02cd805bd00741ffc8bff9d8001100282007bc00868000b001c600944008f7fea4fffc60046c0052801af005aa01c8bf626,0x110999e9ef3ee2f7f5f5005e1fe64c000d7fd9cffbb9fdf73fac3803230051600ee3fcfb7fe88ff471fe0dbff607f70efcfd5fa41bf93f7f1b0fea91f7353ea167d910fced1fa1b3e69b7c47b008edff173fbce7fad4ff949fe90bfa237f4ecfe3fa02ad4078b811d5022ea05a440ae2815f703f120856c14d48284f05ad60b83c17398323f007ee008e402c4806f10026a0140c04af80209001f5ff963fcd57f7d6fefc5fdf83fe6a7fc24fee55fe5f3fd0b7fbcaff94dff6bbff107fddcffb45ff493fe347fd08ff6cdff5cbfef38046700d0e03d0c06f67f0b4fa5ba0098401ab803010037dffa7bff5b7ffdb002c6006b4003c7ff4700006005fc00957fdfeffe86002140004800f70047e0192bf28c,0x89654fa391fb733fb818071d011e602d2404b2804af0118a023cc02487fbceffa41ff0ebf96d7eb76ff2b5fb26bf0267f03cfbdddf1573e2117ce98fbb39f24f3e2a07d31afa13df67940b3a813e100fa5ff733f8be7f00eff125fe1bbfd0c7ee84fe5fa022ec05bf80f0101df604d4c096c8163d03dda09394176c8316f05d660c314171b802ab00c520154402e780474fff2201ae4047c8043900b5a00653ff827fd4aff8c5ff0ebfe1680064ffc15ffecc0056800ad0040a00ab402f7804fb008120089c003c7fe98ffeb5ffcf3fee1801930012dffad400c18066b00861ff98bfdd17fa2affb5a0037401228049500a7dfed1bffb57f9b4ff129fdc3c01bd80cfd00871fa143ffa3800130030a014fbee17,0x439f47bbb4fce3dffbb408bf80d6b0021e000fc00257f87cff4d5fd423fd337f5eafed39fe27bf91a7ef28fee7dfaafbfb517de1efc8ddf3c5bf6817ce72fc0e9f3353e5647de63024de0477c07b87fdcafb1c5ffec3fb457eeacfe92dfce23f6b07eb76fd7f2023f4056880df701e0204cfc0963815bd03eea0956c179d8313705b220be4c16c1802450096e011140252800e6ffb1e0141404f6804810098e0084bff917fd1cff925ff1abfe587ff0eff799ff82bff737ffb30016e008fc02a0804930075200964004a7ff5f001edffcf3ff4f7fd84ffa95ffedc00a6802fb004de00263ffa27fe66ffcc5ff7abff0b7ffeb004da00d2c00ae7ff79001a60006c00247fd0d0002200c0c00f38047f00e75fdca3eb76,0x21782c0c5a7ebb4feb3dff28c04578016aff3e1fe0a3fe877fbe0ff771fe8ebfc1b80401001cdff04bf9777f4bcfd261fc09400797f66ef9e7dfc53bf4f17e348fe035f4674020780fb101a9201753edc27ecf0f93d1fcc4bfd577e340fd955fb6bbf19c7e19efd9d201b5c052e80d7f01666043fc07a58124d03a7e084bc17a282edb05a6e0b97c173e8002f005d601a240379803e700216019bc048480829016aa024a40309804f500536009f400258009d000f20079400f3803db0067e01aa4053280bf30156a026dc03d7804ed017360184c01027fb3eff716001240098801f5003a200a7c00ce8024b000b9ffcdbffd8801b100a4a02bb4045e805cd0143e004fbfe687fe7d00f060408c068381640fcc4df86ebedb5,0x112d61f341beeae7fffaff6d203f8406a1805bd01d62033cc05e8800daff765feb5bfe497ea08fde65f7c9bf1557e386fe03dfa08bf14e7f4e0fd745f8f43ece57ed2b029ca04c6c01f980ff701fde0184bfbbe796d100a29fee83fa227e898fb549fb31bf2d47e3bafc8a20259c04be80c830203a055540a44817d1042f60a7f41af9836b705bca0bfabffda802350068a00f34020a7ff7eff856012bc0514804390079a004b3ff097fbeaff6e5fed23fdf57fef8ff699ff753ff677ffc1001be00ae4031d80579008d600bf400737ff8d0035dffd53ff4f7fc0eff769ffacc0022801db00245ffe93ff1b7fd84ffb09ff7d3ff1e800630070a0175c01c78011f006edfff4bff887fd050047e01d2402b680a5701d69f953be8fd,0x876fafcb05ff2c3fa4280227011f60221c040a809ed017020261c0348800b2ffca9ff3cbfdcf7f11efe69dfc8b3fa837f52aff941fd84bfe6a7f4f2ff891fdb2401b6802a300302007cbffc180425008ce00993fc0d7fb9cffce9fedb3fd5e7fbb2ff79dfeb9bfcfa7f8ceff24a00a1c00c38027100966015dc02dc806c1011ce02f4406c580e690168203033ffa1800fb002fe0006c000f7fe68ffae20027c01727ffe4ffd4dff78bfe8a7fc38ff94dff263fece7ff42ffa8dff913ff677fec6fff21ffe8400427ffa8ffed9ffbb3ff2b7fe60ffb65ff7b3ff587ff06ffd79ffc4bffd380044fffcdffbabff377fde2ffce1ffc8bff957ffcb0012a00193ffde7ff30ffeb9ffe0c001d7fed6ffec5fffbbffdb8000f00151ffc33f8bc],[0x43a5880d1cff2be00f4c0afc804eafd7adfec93fb9f7fa56fe111f8d03f69c7f13efeb29fe8e3fe647f88b012ee04f44095d8085d0b5c9f4df3ff2e858f3013f2032c4042280e0d00b660387c04b480200ffcfdff6bbffc9807f50098202c6405fa80c67015e6027ac05a680b47011d9fc403f32b7e910fdd85fa683f5c97ef3afd78dfa013f1ca7e068fc071f7d34008f80858fc4fa00804011b7fea4ff7e200bf403f8801b5000a1ff873fdf07f9e8ff499fe8a3fdcb7fe9aff545ff33bfef07fe14fff260007c012d800df00079ffc3bfed57fd52ff969ff293fec77fe44ffb9dffbec003880209002b5ffc4bfef27fcb0ffaf5ff7abfefd7ff770029e002ebff987fde4ffc75ffdcc007d7fd2cffc59ffccbff647ff45000fa00bfbee94,0x22a3a4102b819ad0306dfd584077a807eafb31df8c3bf9e07edeefc04df5023ef2d7ec6efe6c5fc343f944804c4ffa1e0262c0a0d81582fbc1e18c3c00c08037d020da046cc04d08130700fd204ffc06c08022affc3dff24402e280a8f00c2a03b8407ee8107b01caa0348407af80f2d01859fac4bedd47df6efd005f813bf1ac7e93cfc7b9f8493ec6f7d620fa7fdf4ce3fff17fe84fe50a00a0c01637fde2ff48a00f8405548021300005ff43bfd077f760feff9fdf33fcee7fe0eff125fee33fe837fd42ffeae000140183800f100031ff9fbfe4e7fc34ff671fecebfe4b7fd9cff9e9ff9fc003c8029d00359ffa3bfe7a7fb4eff8e5ff4b3fea07ff4300382003c3ff6d7fd1cffb19ffcb400a77fc28ffb01ffb7bff277fef30012e00fa3e867,0x114249fb9c3fc788071effc9dfb1dbfe8180130ffd55fe91c025a7eba8fc3fdfa7fbf7ec7fcb9001c600654000680715019160247408718174b0055a01374004b807ef01ffe0424c03ed81307017aa043e404898033102565fe254041e80d7301b62062e40b3e81129023360494c0a048154702465fa93beeaf7e040fcb49f7aa3f06b7e81afc70df7c33ec777d7a2fa37e0092bffe57c3390078a0137c02aa80270ffe3e015c404d28050500c4a00d9c004d7fec6ffc19ff79bfed67ff3eff92dff9fbff987ffeb001720084c02548042f006ca008e4005d7ff8f001f1ffe5bff6a7fec6ffd62002dc012480401007460069c00377ff80ffeadff7dbff067ff950031a0055bffde7fe4affdca001c4009d7fd28ffcedfff13ffa08000d002fe014d3edf0,0x89a8cffdddfe8d3fdb28073f014b6012abfa7e7ede2fcd35fb1f3fff77f666ff669ff3b3feef803a900bee026c403e37fc63001a602553fc427fbb5008ee0130403188073101b6e0338c032c80e8d004d205dac07447fb68ff16600d94059b813c502462070f40ccb8159902c0e058340b34817d1026c9fb193f1927e52efcee1f8f63f2cb7e378fbe05f5a63e8377ce9cfa0ae00023ffcc8076cfe73e00d7c0284803a0ffffe011ec0403803ff00aa200cec008b7ffc2ffd99ffaabff2980066ffdea0015c0071801af004ba00e6c046a7e64700a1e0105c01668013f007ba00723fffa7ff5cfff220075c0199804b30093e00ccc01178019f00195ff973ff397ffbf002e60062c00177fee2fff260044c00987fdaaffde6000e3ffdc80099003e601773f0b8,0x446bf7fe9101a420347c0c087fb80ffea1ffeebf73c7f17afee42008abffde7f8ed005f60177401768050900e5a00f7c02b27f9e6fd479fdf8400b680699008860265403ea80b5701f0a0338403d9808b700ffa00c8c0905809bd012b60093c094f817f502b46077fc0d9181be5035920678c0d1181b8b02b29fb20bf1fa7e756fceedf949bf3a97ed10fbdedf5c43e4127c9cafff29ff64bfe947fe290046e007fc02598053f0023e00f7c02ed8030d0086a00954005f7ffd2ffdb5ffb03ff8780129000fe005fc00fb802e30069e0145c0478805e0fbdd5fc2fc02268028700bde00c5c006a800b70022a00cc4020c8005500bae0123401d68038d00435ffc63ffa580069003adffd2400577ff8f000ae0073400937fe3cffefe002ec00218013b004ee01a6bf3e1,0x22546bf0ce7fbe500aee02924075a7fe6d00592002f3f8537f474ffc6601f6c01c47f826ffdc200203fff5804030128a01154022d7ed1afe3f5ffb0c036f80c5900dba031dc039d80eb30266a035fc02a9809710134e0171407798073d00f8e02be409e381a91033120860c0df2818af03492069e40d3c81c2f02d99fa773f0c87e554fc7d9f831bf1ff7e782fc889f7c1be4437ca630014dffdbbffd87ff09006ce0105402ed806170052a015ac02dc805ad00fa20159401b88029b001fa0038bffd58014f002aa00894013080367006de015a404658093f01065f65d402a08034100e960118c00a68000f0013200ca402248058700b920142c02218041f00505ffb53ff767fff1002aa0071c005a7ff97000be0075400927fe42fff0a00304002480141004f601a8bf404,0x117d3df8a4bf8e47f0aafe9d5fe463fba9807b90111a01633ff277f608fefea00263feab7e952fe549fd3ebfd20805390135207f1c11517f346ff2b201484076380c5d0152a056b40546817fd0427605d0c03ff812ed015ee071ec0402803ad00a4601f7409ff81a5502ec20829c0c878166103062061c40ce181a5f02b21f91c3ebbd7dc10fbb01f625bee817e30afbebdf5d2bdfbf803ed00336006e400e8801d900b2e015b402ff803bf000fa01754049b805c900f820144c012f800cafff65ffe3bff5b7ffa2ffb99ffd93ffef800bd0026200af4029f80537008de0056400fa800910056200393ffc07ff1effe6e0058c016a8046b0087200a4c00bd800c300065ff8cbff257ffaf002fe005d400007fea4ffe9a00344009a7fd76ffd8200023ffc4800610038601663ef97,0x8a54ef8829fa6bbf9c17f412ff5d5ff36bff647fb3cfe625ff563fa457ee52fd41dfd983fbd27e4f8ff311ff893fd3d824c9046f6065740ad77ef94fed660011c066c808bf0137a063e4051981b7705132072640548815f501d7e081a404308092700d3e0209c097c8184b0255606c440ad58153d02df2057fc0ba2817dd02585f873be8c07d6e4fb6d1f5be3ed227e212fc111f39fbf13380541001f200684003e8029900be600fcc022a800a8ffa72013540504803df0077e003abff067fbe2ff75dfee13fe177fec8ff609ff563ff2c7fee10005e005140202802eb0043600313ff8f7fe3effd75ff78bfefa7fe52ffc09fff6400c980375005be001c3ff897fddcffc69ff69bfede7ff7500346004bbffb27fdd4ffcbdfffcc00a17fcc4ffc2dffdabff717ff9d0024a012cbebc6,0x456f57ccdcfb47dff00bff898010f00c1600f4c00fe7f0a2fc6b1fec53fc967f1a0fc1e1fae1bf72e7dcd8fe67a07bec0a84815eb028ae03c5c02da7f102ff2d1ff5ac065280a050159a0619c04eb81de1060be098b408ca819dd02bb2098fc0623811c10146e03ccc0b49817410376dff35401308144d02d360530c0ada816b902271f7d6be6507d2a8fb281f56d3ebc47e0dcfc339f14bc02e68060300116005fbffca802fd00c3a00be401a47fec8ff672010c4053a802a700271ff93bfdad7f8d6ff25dfe403fd4e7fe4aff2bdff083feb97fdc8fff3a001b401ac8019500181ffcebfeb67fcdcff8b5ff05bfe847fdd6ffa99ffbbc006a802e300421ffcabfed27fc22ffa09ff553feb47ff530036e00413ff847fd58ffba1ffdb400a57fc5cffb61ffc33ff3f7ff290018a010abe97e,0x21efb3eddc7ecaeffa6a02a5c06b480fdb00c4601613fda87ef60fc5fdfbb93fe0280312ff966003a3fee481ea70109dfe433fe068012d00702019cbfdad7fd8d0044a01034059f807d10126a042340350811c10359a05fdc05298106b0181e053cc04c7808dd00ef20181c05ce80e5f01b8600f5c039e806bf00045fecac0366806f5007a1fb93bf1aa7e708fd5a1fa06bf54a7f1d8fc2ba00a44018d802cefffce0013bffbf801410035a0061400d07ff00ffa960085c029f801a5001d5ffe4bfefe7fcc4ff981ff2abfeac7ff4cffa05ff9cbff877ff75000720042c01708023f00366003abffe77ff40fffe1ffbebff7a7fdd2ffb1dffbebffea800b100079ffd43ff457fe14ffc95ffb6bff7f80027003a200b9c00d68006700321ffedbffc37fe5b0020600e4c01508051900eadfc893f394,0x10f35603873ffcd800ccff87dfef4bfe6d7f60afe849f836bf70280165019060749c08d6809a1021d9fdb1bf9a27f5b7003b1ff6e3fd667f194fe17dfb203fd0e7ee88fe685fbf03f91e7f006ff63e03cabe0c480120ffa85fe78bfcdb7f702fef55fd8dbfe89802470038e005f400877fd5eff1edfd19bfa717f64f00721fd0ebf9327f0d6fe57e0302c071f80e2d023be04bc408f780f7504446010b402838047d001fe00603fff2801a101439fb11c00877fe58ff902006f402bb800a6ffe69ff6cbfe167fab8ff669fec6bfe377fedeff785ff593ff1d7fe48ffef9ffef400a68000cfff3dffb0bfee27fdaaff9b9ff42bff007fea6ffc81ffbd3ffff8012100129ffb83ff037fd1affbb1ff9f3ff437ff97001ce001abffa87fe68ffd35ffdb400557fdf2ffd41ffd43ff847ff550005e00723f37a,0x8ac16fa1ce054f405c58008cfea99fdec3fac37d362fb811f3aebe33680a2903caa07b3c00f47e272fd54dfd6f401f88079afe0d1f9bdbf50b7e15cfb509f94ebf8ad7f2a2fe16dfae93f4877e202fe481fb08bfe537ecbcfe121fd03bfc8d7f2c2fe685fbef3fe797ffe4ffbf9fed13fb1e7fa1afe6b9fae5bf60a7e824fd0edf9ee3f2067e1acfcc9a06cfc100081f9d04e820a53c12cd8326d00b4e01b44061780915007aa00f3400b57facefaf5200c0401a77fed4ff68e010d40539802b100291ff983fdb67f8eaff281fe44bfd547fe4cff2d1ff0abfebc7fdd0fff42001cc01ae8019d00191ffd1bfebb7fce6ff8d5ff08bfe877fddaffaa5ffbd4006c802e700429ffccbfed77fc2effa19ff55bfeb67ff530036e0041bff857fd5cffba9ffdc400a57fc5effb69ffc3bff407ff2d0018e010bbe98e],[0x4441b7d0e2fe7de03c83fe357ef80fd899f8543f12e7dfd8f8b39f955bf7f1802a1016b9f8f43edb97f6d5039ba041bc04027ee14fd84a00833fd787f0f8fd37dfd68400727f608fe5adfad23f6047e176fe695fb4cbfa9d7ee98fd5bdfb69bfa037effafd60dfd43401cb80072ffc91fe49bfde47f8befebc9fc7d3f94c7e954fd431fab5bf3517e61afd52a075ec1273823e10561208eb40f6d82e1b0000e010c4050d806a4fffcdff99401a27d03900742009cc021880222ffd2a00ee40413803270073a006fbffd07fe18ffb29ff5cbfed17ffeaffb81ffd2400058014effe7a0279befd3804ab007ca00b1c00ac80011003ae000fbff957fef2ffde600434014780435007da00874007a80022fff89ff853ff157ffa30030e0059bffef7fe78ffe3200284009c7fd50ffd35fff9bffb280037003420159beec4,0x21cfcbf6a07f3f700905fce43fa4f7ee56fdeadf963bf2f07e25afbfa5fc6a3ee8e7f072fcde9ffe93fc127f8d90114e00383f558811c8fff0dff00bfd087f3e8fd931fe72bff837fd7aff725fbf93f7707eebaff8cdfaf93fb827ef58fcfddfc78bfd287f732fea2dfbfb3fda57f012fe155fc97bfbe97f7aaff25dfd42bf9b87e570fd181fabc3f39c7e788fda8206abc144d8221704a3e0a3ac129a80209007be01d54078b80b410076200d8bdeea8017900af601b1403b18061b0060a01acc0469807610162a021fc02ee804b9005d600b2c005d80034fffa20036c00778020f003ae00eec02fc806c900c16014dc02048024300b3200c6400517ffb70002e00a0401df8051f00a6a01084019d802e100351ffa63ff587ffd9002ca006a400397ff3cffff2005d400957fdf6ffe7a001f40000800ef0046e01903f262,0x10d599fd233fa307fef300cb9fc70bf80b7ee74fe1a1ff103ff347d7cefbdddfedb402a67f374fe1c1ff2f3fa547fbd30141200d43f8b68075aff841ff05bfca57f062fd62dfd633ff0f7f162fd871fbadbf77f7ec82ffaedfafebfb117ef94fd551fc6ebfc627f5bafe17dfcacc00317f4c2fe5d9fd773fc257f75efedd1fca53f8d77e5f0fd025fa6c3f3227e5f6fd7160699413af821cf04b6a0989c11938007300292017c40536806090092df509c00dc8021b00b3a0151402ef803a70008e016f404a88057300e7e0121c00e88002cffe79ffc5bff517ff72ffaadffc1bffc780069001e6009ac0275803f5007e200b7400bd80031004060011bffa17ff58ffeb200544015880271008620092c00938006afffedff923ff357ffdd00366001d3fffc7fe9affe7e0031c009a7fd6cffd6e00003ffbf800570037601633ef64,0x8680b01a0a001fc0317810b10204df9403f07a7fab8fb9b9f4eb3e5f87f6f50099600263fdec7f4dafde55fdfdbf8757ff2101606017abffc48002cfe1e5fb153f73c7e8b8fcf89fc6b3fe1b7f296fe391fcfdbfa287efdcffb5dfc7bbfbfd7f37cfe425fd273fc3b7f6e0fe5ddfd543fe2a7f684febb5fdf6bfd6e7f9b2feeb9fc8bbf7d77e556fd015fa5cbf3217e516fd5b2060bc11e281e77044f208b5c085f7ffa50031600e2402c5804af00296006e400958024d00baa012b4028f80212ffd720154404dc804c700b4a00b8400097fe2affb1dff59bfeae7ff26ff885ff903ff817ffb50013a007a40243803eb00642007ac00327ff4900101ffcf3ff537feaeffd1a002240111803e3006f20059400137ff28ffe35ff793fefe7ff8f003260053bffd57fe32ffd920015c009e7fd14ffcc5ffecbff967fff5002d60146bed7c,0x4334b7fde50225206c1c038d8031100081fb88bec817de7cfcb55fc87c09d08090900269fc7ebfd0a7f725014f5fc7fbf74e801bb0103600e0bfed27f772fd851f9c8bf55a7e3c0fca49fbbe3fc277e632fccb5faa4bf7bf7e98cff4f1fca23fbc17f2d2fea6dfdb8bfccd7f94afe765fe3e3fe517f758fec59fdc33fc897f726fe655fb473f5a37de84fc319f932bf1587e0d2fced605ef4109a81c1d0448e085e3fdfa8005b00426014c402e08059d00162005f3fffc802bf00bca00dd401e57ffa4ff84e0120405208034b004fdffe93fe5b7fa60ff4d9fe903fdb17fe8cff471ff31bfef77fe66fffe6003dc01ed8027300336000b3ff347fda8ffb8dff46bfec67fde8ffaf9ffd3c008d8030f004adffefbff267fcfaffb21ff60bfece7ff77003a2005d3ffc37fdd6ffcf5ffebc008e7fc96ffc69fff4bff97800330018e00a8bea73,0x20faebf94a80ce1014fa04684075480a9f010edfa4b3f8707f7af01b8a0323c047180370fe661ff0e3fe1d7f89afe98dfef83fc3c7fdbf0018dffc13fe4a7fc80fef71fd7c3fb937f3e6fe8e5fe46bfe9e7f47cfe8c5fd8e3fc197f5a0ffb81fe69bfe197f974ff421fee3bfeab7fd74ff49dfefb3fed47fac6ff47dfd41bfe2a7fb6cff3d5fdc4bfb197f198fe589fcd53f8ff7f136fe8c602fdc088480e69022460436bfefe80015001ee0094c016a802a7000f20033c001b80151005f6007c4011180044ffd16009940284801e5003960017bff777fdd6ffb85ff6b3ff057ff60ffae9ffa8bff927ff67000260027400fe8016b0020600153ffc07ff14ffe91ffb8bff797ff24ffdf9fff940061801b7002d2000b3ffbe7fee0ffe21ffb43ff6e7ffb9001a60025bffd77fee6ffe55fffd400517fe5effe11ffecbffb77ffcb0011e00953f5cf,0x10e23e01bdbf7327e7a0fe49dfbfdbfb327fa8afd7a9fd58bf5367ef7efea3dfdbd3fe6a80875005e201443fea57fea90176e02dac0aaa814cf024c6044ec06ed810a5022ba01de403bc807f500a41ff593fc09805ef00fd6018cc02af80b170029e02dd40252810d701b7203cec06e380597011a20134c01fe80b150158e0379404b6809a300c7201f34048a810a701da202de4065f80dd1012c1fc663f4ee7ee98fdc05fbaac00fc801150038600374013f8017100882005340015801470006dfbcbbf97c8057500719fff24003b7fec0ffba9ff70bfee67fd84ffc1dff82bff6d7ffa8ffd75ffbdbffa07feeaffee5ffbbbff737fe3cffc91ff913ff197feb4ffb5dffaf3ffa27fffafff65ffc1bff8b7ff0effd4dff803ff037fd86ffd55ffd83ff9b7ff22ffe0dffa13ff0c7fdeaffba5ff82bfc7d7ffe2fffc1fff73ffef7ffd4fffadffee3ff64,0x86c74f80e20349bfc8d7d784fb86df641bf88d7ec3f00a65faab3fb957fed1003a1fe5fbfd6180abb01d7e016940663803c902ab1fec7408d281d64fedb20051c0a2c824ef03512037040828813a900fa9fdbf3f5fb81b790303e041bc03f6822ccff02e022641393809bd006fe07154164d807a902741ff78c02e3812fb026360823c02d580a890110a02e140905825cb040f605dc40db781fed02bc1f983bef3e7e650fb976000b4032f7ffe100119fee53ffc47fc7f016ee0024bffc5804c0fa529ff173f2e08105102165ff2c3fcf97fa9cff291fec9bfeb67fe72fff69fff24006f80055002b9fffcbffe57fe8effd75ff253fd267f9b2ff4e1fee53fe5d7fea2ff839ffe340016801bd00299ff803fe627fb16ff4e1fea43fde77fb5affc8dfffe3ffac7fd98ff6d9fe93bfd357fb0eff4e1fe823f38e8026f002e2001bc006b80048ffe45ff1cc0f35,0x42ead7ff9b006fe072e4121f819910624dfe25bf0c67e2f4fdcadfff24047880f9301f6a02bec02a78006cffec9fe5abfef07ea26fc6d9fe643fc4480039008edff34bfcb07f65afeb4dfdc3bfb007f268fecb1fe28bfdda7da3efb4f5f82f3f4947ea34feb69fbfc3fd3a7eefcfdf3dfe39bfee97ff90ff269fe8f3fae77ef62fdcd5fbd73f8ef7f030fe071fa93bf40f7dd1afc0f1f88f3f0197dfa4fce660575c0fea81a8cff819fec3bfe0180025003da0122c02df80541001f60064c003b8029700bca00f5c02288009cffa7201314050d803df00766003bbff037fbdaff751fedfbfe177feb8ff5d9ff4fbff1f7fec70002a004a401ec802bb003e200293ff817fe36ffd49ff7ebfefc7fe3affbfa0005400e18037b00596001ebff9a7fe04ffc89ff5c3feba7ff1f002c600663ffb57fd64ffd220036400477fba6ffd420028bfebf8014700246012c3ebba,0x21291bfd707c84efe67601c041e1480416fd141fc24bf71e7ed6efea9e02564077080e170135201e3c02637fd76ff9ddfe83bff9a7f640feb4dffd5c02c2802e10182e00363fe1c7fa80fee2dfeadbfc827f7feff80dffd1c00707e632fc961fa303f6de7ef84feb2dfc51bfe097efe4fda65fde63feb97ffb2ff2e5fe583fa9c7ed6efd801fb76bf91f7f1b2fe8a9fbdd3f5c27dd16fc3c5f935bf1877e240fd4d2057dc10f981c4cff6ddfed33fdc77ff2f0026e00a4402b780425003320073c00e78020700b6e0157c02ef803690004e0171c04b6805a500ee6012fc00ff80058ffeadffcc3ff3d7ff80ffae1ffc7bffd38007d0020a00a0c0280804df0083200c0c00cd800470046600213ffa77ff04ffe1e004c401568044d0081a00934009680064fffe5ff883ff1c7ffa700306005b3fff67fe8affe5e002d4009b7fd60ffd55fffd3ffb9800470035e015f3ef1c,0x108a320514c13557c8fefeb4dfcbdbfb7f80b48fe655fe753fcd57f56eff5f602aac077e80cc9010e202184027b7fc7eff8b9fe8e4002f7fa46ff5820005403a08021101631ffecbfe107fbbeff07dff273fd087fb5efffce00354006c7e950fce41fb0fbf7d67f364febcdfc5dbfe587ef9cfd73dfdd1bfefc80018ff1e5fde83f97f7ed00fd67dfb4d3f8d67f0b2feb7dfc4c3f6877dd14fc495f968bf1dc7e364fd732057ec11fb81258ff3adff103fe137fd69004d20104c036e804c3003be006340143801e700a2e0165c03358029100e920088c044e8064d011ba018fc01d680257001e20033bffc18000affdde000f40046801870036600dac02fa8064500aee01323fd2f80195008e2008e400177ff7afff7a0083c01b0804d7009a200e0c01448020900229ff9c3ff447ffc7002de0065400227ff00fff6a004d400977fdc4ffe160013bffe8800b500412017fbf145,0x83f4f047ca06853f6c67ce970136dfda83faba806f8fe505fdc43fefe7fb80ff89600af400a87feeeffe26007d400b57f6deff39dfeefbfe137fb5affdc60143c09618055b01eb60020bfde27fc88ff706008e3ff218028b009a20237403ad7e75afcc5dfa5c3f7237ee48ff069fc33bfdf87ef46fd761fe3ebffa3803daff719fe9abf94e7e93afcf79fa11bf7507ef24fe8f5fc573f6547da8afc0bdf907bf0d57e32cfd6ea056ec11487fa6cff625fee63fd9f7fe730016e0041402b1803490041a0076c01628018d00afa0195403848056d004ba019ac0484807050147e01ed40280803bd0043a007ec001e7fffcffe620018c0046801a30032200d8c02d18064100b06012b401ba801d7009be00adc00327ff5cfff7e009dc01d8804e90099a00f0c017580285002adff8fbff217ff6f002620092400427feaf000760097c001f7fc7efffd600893ff3a800c50042e01843f196],[0x41faa853e6ff3b1fb5dbf1cc81cc3005d9fdecbfc0a80840ff0f1feb240407802970008dff063fc307f6baff3e1ffcfbffd07f38aff0cdfef8bfd327fce7004fa0209c0cad8057502099fff0bfd0b8002effede010a401c380789010d60327c04757e7fafd1edf9bd3f6727ee74fef4dfc11bfe607f034fd659feadc008580680ffed1fecd3f89a7e706fc885f9683f69c7edc2fe7e9fc413f59e7d8e4fbf1df8fb3f1777e25afd5ee05fac06377fb14ff5c5feea3fd947fe43000f2001c4029580303004be008a401a78018300afe01bec03ca8069b006ca01bc4044f8077d016e6022e40313805170065e00c3c006c8006900082004c4009e802510042200fa403168070900c920159c02208025900b6e00cfc00528003300106009ec01ea8058f00b020107c0188802b300349ffc0bffa0800750038e0034c002e7fef2ffe820054400da80018ffe9a002340008801010048e0195bf2c2,0x21b803f6937dd710012e00d1bf94f80c9f0015dffe73fc09801e700a6602404037380249006c60059bfe3e7f71cff175fd73bfc857f404ff2f5febcbff337fe090081200e7c02c3801a7021d601d840325801dcffd45fef03fff5802b300b8a0097c02227ece0fdd9dfb53bf7fc7f7e0fe819fc173fe927f044fd505fd8ebfe767fe2cffafdfcab3f48d7ef44fd875fc5e3fa0f7f3a6fef09fc753f4b37d9e6fc48df975bf1ac7e346fd4020698bfed5800eeff499fffb3ff9b7ff0900cbdfd6dc00b17fa7b015820273c080e80f63005c2010ac02df802c901ea60187c028980619011ca0189402118039d002ee0058bffe58020b005da00da401c280493008ce019fc051680aed01392020cc020a816b4fba46016e400e7800730024e00fa4027d8064100c6a01634026a804e70067dffc5bffa180035003060088400a27febb0015e0087c00907fe7efff7e003dc0040801830056201bc3f54d,0x1076a9f5f5400b07f0d7004ca0342bfe62801e10009200013fc147ff110131201e9c0447801b101045ff43c016a7f93cfef25fd0dbfcb87f79efec71fe63bfefb7fee9009e6004ebfc4d7fcd9023c602a34022880c3aff595fba83fd2e7fe2d00195ff5b3ffec7f37cfe801fb5abf8ba7feeafea09fbebbff397f156fd8a1fdbebfe4d7fb4900831f9a9bf3df7ead0fdc91fdb63fd2f7f910ff81dfc5c3f3237d9befc4bdf96e3f2147e10efcee9fef9bfef4801d6ff5ae0115c00b18011500e31ff9b3fd578008101c020348c071180d7f00d4e021cc02d3806a9018fa0183c01eb806ad010020156c01c4803350018e002d3ffa4802fb008c60137402808065b00c6a022e406ea80bb1014ea0220403258068cfcfc5fc4a40012801c900556014e4033d807f90104e01ca403358064afeb65ffdc3ffd58007700332009dc00ed7fe5d0026200a64008c7fedf0003600534006d801ed0061201db3f763]]
def gramWord (i : ℕ) : ℕ := ((gramWordChunks.getD (i/12) []).getD (i%12) 0)
def digitTotalWords : List ℕ := [0x65c7ac8dc986922f7906139eaa2312e3ea294164c10c0d0577272e3bd5a2a6b16b54ed162638,0x56780a4c6d5a8a2983b4afe08d86d08eda11724170681a98f7719ed6a3ad3e8ee0d6efbb3811,0x3299a7f498fc4126dc955c9c9f2ad59652cecc589a8b8b61640aabc4c531a2a65ad50b829ab4,0x5657aa33b53e1c24a8252c36a23692a9ca73fd501ce9ebc531022531b3fb64781d8f7b39ec4b,0x60fa296f6d081faa78651c4ea007d4c61a889d532e2b8e556b9e2e5c960750b9c8d6d5baa7f6,0x439ee8f2893be82c2df53c08b194d3014249fa46a74947bd19599d44f3a0b6667f8d7dba3080,0x4dcacabbed5ba1af12b5d8f8bb8157d092b029250fe0626800000552c1c7186c538e9991f00f,0x53a12c05657c7fad4844f7a89634cf6bd2416f4d59e95361529c2272f4735c8b93146d9aaf08,0x394fe74a90cfc317188632deb6849034a15abf332686acf8e1c1177662a9e684981568e2844b,0x7947d010b1fe4c]
def digitTotal (i : ℕ) : ℤ := 1 * (((digitTotalWords.getD (i/16) 0 >>> (19*(i%16))) &&& 524287 : ℕ) : ℤ) + 38380319
def gramValue (i k : ℕ) : ℤ := readGram 19 262144 (gramWord i) i k
def gramDigit (i k : ℕ) : ℕ := (gramValue i k+262144).toNat
def forwardWords : List (List ℕ) := eval% natTable 147 (fun i => natWord 147 56 (gramDigit i))
def backwardWords : List (List ℕ) := eval% natTable 147 (fun i => natWord 147 56 (fun k => gramDigit i (146-k)))
def gram : GramPacking where
  n := 147
  width := 56
  offset := 262144
  scale := 8192
  value := gramValue
  forward := tableAt forwardWords
  backward := tableAt backwardWords
  total := fun i => (digitTotal i).toNat
def inputs : Tabs where
  n := 146
  loN := 8
  hiN := 9
  Zn := 360364800
  ppn := 0
  rrn := 0
  ssn := 79384543232
  vlo := low
  vhi := high
  vlen := lengthOf
  vsg := signOf
  vAl := alpha
  vBt := beta
  vYv := yv
  vOv := ov
  vA1 := a1
  vA2 := a2
  vA3 := a3
  vA4 := a4
  YYT := yy
  OOT := oo
  YOT := yo
  thT := theta
  NT := fun _ _ => 0
  crows := gram.scaledRows
  czr := [2795349265612800,0,2440043692032000,0,3456023868211200,0,1347756962611200,4227272697446400,0,1319413953331200,0,2913177541017600,0,1411589446041600,0,0,0,3958234310246400,0,2614529045299200,0,1985192814182400,0,3548547907584000,0,3707436112281600,0,329853488332800,0,5277655813324800,0,0,0,0,0,0,0,0,0,629145600,0,4949969731584000,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5277655813324800,0,5277655813324800,0,0,0,0,0,0,0,5169948603187200,0,5277655813324800,0,5277655813324800,0,0,5277655813324800,0,5277655813324800,0,5169948603187200,0,0,0,0,0,0,0,5277655813324800,0,5277655813324800,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4949969731584000,0,629145600,0,0,0,0,0,0,0,0,0,5277655813324800,0,329853488332800,0,3707436112281600,0,3548547907584000,0,1985192814182400,0,2614529045299200,0,3958234310246400,0,0,0,1411589446041600,0,2913177541017600,0,1319413953331200,0,4227272697446400,1347756962611200,0,3456023868211200,0,2440043692032000,0,2795349265612800]

def tri : Tri := Tri.zero


def matWords : List (List ℕ) := eval% natTable 147 (fun i => natWord 147 39
  (fun j => (proposedEntry inputs G8 tri i j / 12582912 - (-12431963120)).toNat))
def matrixAt (i j : ℕ) : ℤ := 12582912 * Int.ofNat ((tableAt matWords i >>> (39*j)) &&& 549755813887) + (-156430297926205440)
def mat (i j : ℕ) : ℤ := matrixAt (min i j) (max i j)
def tabs : Tabs := { inputs with NT := mat }
end Erdos1186Ex.R4
end

section
namespace Erdos1186Ex.R4

open Erdos1186Ex
theorem grid_ok : (List.range 146).all (gridChk tabs G8) = true := by decide +kernel

theorem vec_ok : (List.range 146).all (vecChk tabs) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair0 : (List.range' 0 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair6 : (List.range' 6 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair12 : (List.range' 12 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair18 : (List.range' 18 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair24 : (List.range' 24 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair30 : (List.range' 30 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair36 : (List.range' 36 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair42 : (List.range' 42 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair48 : (List.range' 48 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair54 : (List.range' 54 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair60 : (List.range' 60 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair66 : (List.range' 66 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair72 : (List.range' 72 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair78 : (List.range' 78 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair84 : (List.range' 84 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair90 : (List.range' 90 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair96 : (List.range' 96 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair102 : (List.range' 102 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair108 : (List.range' 108 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair114 : (List.range' 114 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair120 : (List.range' 120 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair126 : (List.range' 126 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair132 : (List.range' 132 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair138 : (List.range' 138 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair144 : (List.range' 144 2).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

theorem pairAll : ∀ i < 146, (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) i = true :=
  fun i hi => (join_ranges (join_ranges (join_ranges (join_ranges (all_range_of pair0) (join_ranges (all_range_of pair6) (all_range_of pair12))) (join_ranges (all_range_of pair18) (join_ranges (all_range_of pair24) (all_range_of pair30)))) (join_ranges (join_ranges (all_range_of pair36) (join_ranges (all_range_of pair42) (all_range_of pair48))) (join_ranges (all_range_of pair54) (join_ranges (all_range_of pair60) (all_range_of pair66))))) (join_ranges (join_ranges (join_ranges (all_range_of pair72) (join_ranges (all_range_of pair78) (all_range_of pair84))) (join_ranges (all_range_of pair90) (join_ranges (all_range_of pair96) (all_range_of pair102)))) (join_ranges (join_ranges (all_range_of pair108) (join_ranges (all_range_of pair114) (all_range_of pair120))) (join_ranges (join_ranges (all_range_of pair126) (all_range_of pair132)) (join_ranges (all_range_of pair138) (all_range_of pair144)))))) i (Nat.zero_le i) hi

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear0 : (List.range' 0 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear8 : (List.range' 8 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear16 : (List.range' 16 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear24 : (List.range' 24 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear32 : (List.range' 32 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear40 : (List.range' 40 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear48 : (List.range' 48 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear56 : (List.range' 56 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear64 : (List.range' 64 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear72 : (List.range' 72 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear80 : (List.range' 80 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear88 : (List.range' 88 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear96 : (List.range' 96 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear104 : (List.range' 104 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear112 : (List.range' 112 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear120 : (List.range' 120 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear128 : (List.range' 128 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear136 : (List.range' 136 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear144 : (List.range' 144 2).all (linearQuick tabs G8 tri) = true := by decide +kernel

theorem linearAll : ∀ i < 146, (linearQuick tabs G8 tri) i = true :=
  fun i hi => (join_ranges (join_ranges (join_ranges (join_ranges (all_range_of linear0) (all_range_of linear8)) (join_ranges (all_range_of linear16) (all_range_of linear24))) (join_ranges (join_ranges (all_range_of linear32) (all_range_of linear40)) (join_ranges (all_range_of linear48) (join_ranges (all_range_of linear56) (all_range_of linear64))))) (join_ranges (join_ranges (join_ranges (all_range_of linear72) (all_range_of linear80)) (join_ranges (all_range_of linear88) (join_ranges (all_range_of linear96) (all_range_of linear104)))) (join_ranges (join_ranges (all_range_of linear112) (all_range_of linear120)) (join_ranges (all_range_of linear128) (join_ranges (all_range_of linear136) (all_range_of linear144)))))) i (Nat.zero_le i) hi

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance0 : (List.range' 0 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance3 : (List.range' 3 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance6 : (List.range' 6 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance9 : (List.range' 9 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance12 : (List.range' 12 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance15 : (List.range' 15 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance18 : (List.range' 18 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance21 : (List.range' 21 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance24 : (List.range' 24 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance27 : (List.range' 27 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance30 : (List.range' 30 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance33 : (List.range' 33 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance36 : (List.range' 36 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance39 : (List.range' 39 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance42 : (List.range' 42 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance45 : (List.range' 45 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance48 : (List.range' 48 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance51 : (List.range' 51 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance54 : (List.range' 54 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance57 : (List.range' 57 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance60 : (List.range' 60 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance63 : (List.range' 63 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance66 : (List.range' 66 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance69 : (List.range' 69 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance72 : (List.range' 72 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance75 : (List.range' 75 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance78 : (List.range' 78 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance81 : (List.range' 81 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance84 : (List.range' 84 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance87 : (List.range' 87 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance90 : (List.range' 90 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance93 : (List.range' 93 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance96 : (List.range' 96 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance99 : (List.range' 99 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance102 : (List.range' 102 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance105 : (List.range' 105 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance108 : (List.range' 108 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance111 : (List.range' 111 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance114 : (List.range' 114 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance117 : (List.range' 117 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance120 : (List.range' 120 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance123 : (List.range' 123 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance126 : (List.range' 126 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance129 : (List.range' 129 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance132 : (List.range' 132 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance135 : (List.range' 135 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance138 : (List.range' 138 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance141 : (List.range' 141 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance144 : (List.range' 144 3).all (quickDominance tabs gram) = true := by decide +kernel

theorem dominanceAll : ∀ i < 147, (quickDominance tabs gram) i = true :=
  fun i hi => (join_ranges (join_ranges (join_ranges (join_ranges (join_ranges (all_range_of dominance0) (join_ranges (all_range_of dominance3) (all_range_of dominance6))) (join_ranges (all_range_of dominance9) (join_ranges (all_range_of dominance12) (all_range_of dominance15)))) (join_ranges (join_ranges (all_range_of dominance18) (join_ranges (all_range_of dominance21) (all_range_of dominance24))) (join_ranges (all_range_of dominance27) (join_ranges (all_range_of dominance30) (all_range_of dominance33))))) (join_ranges (join_ranges (join_ranges (all_range_of dominance36) (join_ranges (all_range_of dominance39) (all_range_of dominance42))) (join_ranges (all_range_of dominance45) (join_ranges (all_range_of dominance48) (all_range_of dominance51)))) (join_ranges (join_ranges (all_range_of dominance54) (join_ranges (all_range_of dominance57) (all_range_of dominance60))) (join_ranges (all_range_of dominance63) (join_ranges (all_range_of dominance66) (all_range_of dominance69)))))) (join_ranges (join_ranges (join_ranges (join_ranges (all_range_of dominance72) (join_ranges (all_range_of dominance75) (all_range_of dominance78))) (join_ranges (all_range_of dominance81) (join_ranges (all_range_of dominance84) (all_range_of dominance87)))) (join_ranges (join_ranges (all_range_of dominance90) (join_ranges (all_range_of dominance93) (all_range_of dominance96))) (join_ranges (all_range_of dominance99) (join_ranges (all_range_of dominance102) (all_range_of dominance105))))) (join_ranges (join_ranges (join_ranges (all_range_of dominance108) (join_ranges (all_range_of dominance111) (all_range_of dominance114))) (join_ranges (all_range_of dominance117) (join_ranges (all_range_of dominance120) (all_range_of dominance123)))) (join_ranges (join_ranges (all_range_of dominance126) (join_ranges (all_range_of dominance129) (all_range_of dominance132))) (join_ranges (join_ranges (all_range_of dominance135) (all_range_of dominance138)) (join_ranges (all_range_of dominance141) (all_range_of dominance144))))))) i (Nat.zero_le i) hi

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput0 : (List.range' 0 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput10 : (List.range' 10 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput20 : (List.range' 20 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput30 : (List.range' 30 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput40 : (List.range' 40 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput50 : (List.range' 50 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput60 : (List.range' 60 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput70 : (List.range' 70 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput80 : (List.range' 80 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput90 : (List.range' 90 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput100 : (List.range' 100 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput110 : (List.range' 110 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput120 : (List.range' 120 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput130 : (List.range' 130 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput140 : (List.range' 140 7).all gram.check = true := by decide +kernel

theorem gramInputs : ∀ i < 147, gram.check i = true := fun i hi => (join_ranges (join_ranges (join_ranges (all_range_of gramInput0) (join_ranges (all_range_of gramInput10) (all_range_of gramInput20))) (join_ranges (join_ranges (all_range_of gramInput30) (all_range_of gramInput40)) (join_ranges (all_range_of gramInput50) (all_range_of gramInput60)))) (join_ranges (join_ranges (join_ranges (all_range_of gramInput70) (all_range_of gramInput80)) (join_ranges (all_range_of gramInput90) (all_range_of gramInput100))) (join_ranges (join_ranges (all_range_of gramInput110) (all_range_of gramInput120)) (join_ranges (all_range_of gramInput130) (all_range_of gramInput140))))) i (Nat.zero_le i) hi

theorem soundDominance (i : ℕ) (hi : i < 147) : domRow tabs i = true := by
  apply dominance_of_packing tabs gram (by decide +kernel) (by decide +kernel) (by change gram.scaledRows.length = gram.n; simp [GramPacking.scaledRows]) _ gramInputs i hi (dominanceAll i hi)
  intro j hj
  refine ⟨gram.row_eq hj,?_⟩
  simp [GramPacking.row]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem constant_ok : constantQuick tabs G8 tri = true := by decide +kernel

theorem region : RegionLB G8 (2/5) (9/20) := by
  have hp (i : ℕ) (hi : i < 146) :
      ((List.range' i (146-i)).all (quadQuick tabs G8 tri i) = true) ∧ czQuick tabs G8 i = true := by
    simpa only [Bool.and_eq_true] using pairAll i hi
  have hs (a b : ℕ) : tabs.NT a b = tabs.NT b a := by
    change matrixAt (min a b) (max a b) = matrixAt (min b a) (max b a)
    rw [min_comm a b, max_comm a b]
  have hw (i j : ℕ) : (0 ≤ tabs.thT i j ∧ tabs.thT i j ≤ Qn) ∧
      0 ≤ tabs.YYT i j ∧ 0 ≤ tabs.OOT i j ∧ 0 ≤ tabs.YOT i j := by
    refine ⟨⟨Int.ofNat_nonneg _,?_⟩, Int.ofNat_nonneg _, Int.ofNat_nonneg _, Int.ofNat_nonneg _⟩
    change Int.ofNat (min 1099511627776 _) ≤ Int.ofNat 1099511627776
    exact Int.ofNat_le.mpr (Nat.min_le_left _ _)
  have h := region_of_tabs tabs G8 tri 146 (by decide +kernel) (by decide +kernel)
    (all_range0_of grid_ok) (all_range0_of vec_ok) (by decide +kernel)
    (pair_from_upper tabs G8 tri 146 hs hw fun i hi => (hp i hi).1)
    (fun i hi => (linearQuick_eq tabs G8 tri i) ▸ linearAll i hi)
    (fun i hi => (czQuick_eq tabs G8 i) ▸ (hp i hi).2)
    ((constantQuick_eq tabs G8 tri) ▸ constant_ok) (by decide +kernel) soundDominance (Tri.zero_ok 146)
  have leq : ((tabs.loN : ℤ) : ℚ) / 20 = (2/5 : ℚ) := by change ((8:ℚ)/20) = _; norm_num
  have heq : ((tabs.hiN : ℤ) : ℚ) / 20 = (9/20 : ℚ) := by change ((9:ℚ)/20) = _; norm_num
  rwa [leq, heq] at h

end Erdos1186Ex.R4
end

section
namespace Erdos1186Ex.R5

open Erdos1186Ex
def yv (_ : ℕ) : ℤ := 0
def ov (_ : ℕ) : ℤ := 0
def a1 (_ : ℕ) : ℤ := 0
def a2 (_ : ℕ) : ℤ := 0
def a3Words : List ℕ := [0,0,0,(0x8271f <<< 60),0,(0xc7e09 <<< 100),0,0,0,0]
def a3 (i : ℕ) : ℤ := 655360 * (((a3Words.getD (i/16) 0 >>> (10*(i%16))) &&& 1023 : ℕ) : ℤ) + 0
def a4Words : List ℕ := [(0x3b5a803 <<< 98),0,0,0,0,0,0,0,(0x500676b <<< 127),0]
def a4 (i : ℕ) : ℤ := 131072 * (((a4Words.getD (i/16) 0 >>> (14*(i%16))) &&& 16383 : ℕ) : ℤ) + 0
def yyValWords : List ℕ := [0x6b83cbe42238641c3c098b95c295f0343400,0x101519b41912052246c46]
def yyVal (i : ℕ) : ℤ := 131072 * (((yyValWords.getD (i/16) 0 >>> (9*(i%16))) &&& 511 : ℕ) : ℤ) + 0
def yyRowsChunks : List (List ℕ) := [[(0x2800000000000831 <<< 581),(0x40000000000003 <<< 586),0,0,0,0,(7 <<< 55),0,0,(0x4800000000001 <<< 78),0,0],[0,0,(5 <<< 436),(11 <<< 435),0,(0x284000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003 <<< 322),0,0,0,0,0,0],[(0x1c000000000000000000000000000000d <<< 430),0,0,(1 <<< 727),(0xcc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f <<< 315),(1 <<< 726),0,0,0,0,(0x7000000000002e088000000000000000000000000001 <<< 434),(393 <<< 546)],[(281 <<< 551),0,0,0,0,0,0,(19 <<< 495),(5 <<< 497),0,(157 <<< 507),0],[0,(21 <<< 340),0,0,0,0,0,0,0,0,(331 <<< 650),(0x3400000000001 <<< 559)],[0,0,0,0,0,0,0,0,0,0,(1 <<< 365),(11 <<< 366)],[(27 <<< 371),0,0,0,0,(21 <<< 480),0,0,0,(3 <<< 642),(15 <<< 585),0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[(9 <<< 680),0,0,0,0,0,0,0,0,0,(1 <<< 683),0],[0,0,(7 <<< 695),0,0,0,0,0,0,0,0,0],[0,0]]
def yyRows (i : ℕ) : ℕ := ((yyRowsChunks.getD (i/12) []).getD (i%12) 0)
def proposed_yy (i j : ℕ) : ℤ := yyVal (((yyRows i) >>> (5*j)) &&& 31)
def yyPacked : List (List ℕ) := eval% natTable 146 (fun i => natWord 146 64 (fun j => (proposed_yy i j).toNat))
def yy (i j : ℕ) : ℤ := Int.ofNat ((tableAt yyPacked i >>> (64*j)) &&& 18446744073709551615)

def ooValWords : List ℕ := [0x3f2cec143822eb271a00]
def ooVal (i : ℕ) : ℤ := 131072 * (((ooValWords.getD (i/16) 0 >>> (8*(i%16))) &&& 255 : ℕ) : ℤ) + 0
def ooRowsChunks : List (List ℕ) := [[0,0,0,0,0,0,0,0,0,0,0,0],[0,(0x80000000000000000000000000000000000000000000001 <<< 344),(1 <<< 437),(0x40000000000000000000003 <<< 112),0,0,0,0,0,0,0,(9 <<< 488)],[0,0,(0x76000000000000000000005 <<< 112),0,0,0,0,0,0,0,0,0],[(1 <<< 525),0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,(1 <<< 528)],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,(0x400000000007 <<< 476)],[(3 <<< 477),0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,(0x300000000005 <<< 476),0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0],[0,0]]
def ooRows (i : ℕ) : ℕ := ((ooRowsChunks.getD (i/12) []).getD (i%12) 0)
def proposed_oo (i j : ℕ) : ℤ := ooVal (((ooRows i) >>> (4*j)) &&& 15)
def ooPacked : List (List ℕ) := eval% natTable 146 (fun i => natWord 146 64 (fun j => (proposed_oo i j).toNat))
def oo (i j : ℕ) : ℤ := Int.ofNat ((tableAt ooPacked i >>> (64*j)) &&& 18446744073709551615)

def yoValWords : List ℕ := [0x8510a0321f507606900d07f0c70131fa2da231044035000,0x781192a903403e20d2740740af06e02111701600703b0b1,0x3f1ef0252240d42c94d153712d2e90c308d3431771240a4,0xeebf44f7e05484481cd2411ac299db05f1217ef6fd06241e,0x22511202b10c02028106d3bc42f1226a2a6bbb9083dff0cd,0x3c00ee2c30c63442ef3640dc0092a53180cf02c30915c2ca,0x8b5ef02e02904c61200201b0635ba6cc0285a00f5101051,0x2b1001]
def yoVal (i : ℕ) : ℤ := 131072 * (((yoValWords.getD (i/16) 0 >>> (12*(i%16))) &&& 4095 : ℕ) : ℤ) + 0
def yoRowsChunks : List (List ℕ) := [[1,128,0x4000,0x1400000,0x20000000,(11 <<< 35),(1 <<< 42),(3 <<< 51),(0x70d <<< 49),(15 <<< 63),(0x2600000000000000000122200000000001 <<< 74),0xa8000000000000000280000000000010000000],[(0x305c00000000000000b <<< 85),(3 <<< 91),(25 <<< 98),(1 <<< 107),(0x360000000000000000d <<< 113),(0xe05 <<< 119),(29 <<< 126),(0x783 <<< 127),(31 <<< 140),(1 <<< 152),(33 <<< 154),(17 <<< 162)],[(3 <<< 168),(35 <<< 175),(0x132500000000000000009 <<< 107),(39 <<< 189),(5 <<< 199),(41 <<< 203),(21 <<< 211),(43 <<< 217),(7 <<< 224),(11 <<< 233),(0x5a1 <<< 240),(0x5eb8000000000000000001 <<< 171)],[(395 <<< 256),(25 <<< 260),(51 <<< 266),(0x366ad <<< 261),(55 <<< 280),(919 <<< 283),(29 <<< 295),(0x3c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003b <<< 301),(0x43d <<< 308),(351 <<< 316),(0x203f <<< 322),(0x2141 <<< 329)],[(67 <<< 336),(0x1103 <<< 337),(0x2345 <<< 350),(967 <<< 357),(9 <<< 367),(0x2549 <<< 364),(0x9a000000000000000000000000000000000000000000000000000000000004c04000000000000000000000000000000000000004b <<< 210),(39 <<< 386),(79 <<< 392),(5 <<< 403),(0xa40000000000000000000000000000000000000051 <<< 245),(0xab5000000000000000000000000000000000000000000000000000000000053 <<< 168)],[(0x15eb <<< 421),(11 <<< 430),(89 <<< 434),(0x2d09 <<< 434),(0x2e5b <<< 448),(0x2f5d <<< 455),(0xc0000000000000000000000000000000000000000000000000000000000005f <<< 462),(0x630000000000000000000000000000000000000000000188061 <<< 273),(0x194000000000000000000000000000000000000000000000000000000000000000000000000000000000000000019 <<< 114),(0x19f3 <<< 484),(0x6cd600000000000000000000000000000000000000000000000000006a0000000000000000000000000000000000000000000000069d <<< 290),(0x70000000000000000000000000000000000000000000000000001bf76d0000000000000000000000000000000000000000000000009 <<< 294)],[(113 <<< 504),(113 <<< 511),(0x9000000000000000000000000000000000000000000000006dddbc000000000000000000000000000000000000000000000000007 <<< 305),(0xd1a400000000000000000000000000000000000000000000001a80000000000000000000000000000000000000000000000000000d7b <<< 303),(0x3367 <<< 525),(0x640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000065 <<< 539),(0x610188000000000000000000000000000000000000000000063 <<< 546),(0x5f000000000000000000000000000000000000000000000000000000000003 <<< 313),(0x176f <<< 554),(0xb77 <<< 562),(621 <<< 575),(89 <<< 581)],[(11 <<< 591),(0x2b57 <<< 588),(0xa60000000000000000000000000000000000000000000000000000000002a55 <<< 602),(0x510000000000000000000000000000000000000029 <<< 610),(5 <<< 620),(79 <<< 623),(39 <<< 631),(0x96000000000000000000000000000000000000000298000000000000000000000000000000000000000000000000000000000004d <<< 392),(0x1265 <<< 645),(9 <<< 654),(0x2387 <<< 651),(0x1163 <<< 659)],[(209 <<< 674),(67 <<< 679),(0x1061 <<< 680),(127 <<< 692),(0x1f05 <<< 693),(977 <<< 703),(0xec0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f <<< 296),(29 <<< 722),(0x1c39 <<< 728),(55 <<< 735),(0x68d5b <<< 743),(51 <<< 749)],[(25 <<< 757),(0x1831 <<< 756),(0x800000000000000000172f <<< 763),(557 <<< 770),(11 <<< 786),(7 <<< 791),(43 <<< 798),(21 <<< 806),(41 <<< 812),(5 <<< 822),(39 <<< 826),(0x240000000000000000953 <<< 834)],[(35 <<< 840),(3 <<< 847),(17 <<< 855),(33 <<< 861),(1 <<< 873),(31 <<< 875),(399 <<< 883),(29 <<< 889),(167 <<< 891),(0x680000000000000001b <<< 833),(1 <<< 912),(25 <<< 917)],[(3 <<< 924),(0xb00000000000000173 <<< 864),(0x800000000005000000000000000015 <<< 868),(0x20000000000011240000000000000000013 <<< 812),(15 <<< 952),(839 <<< 960),(3 <<< 968),(1 <<< 973),(11 <<< 980),(1 <<< 988),(5 <<< 995),(1 <<< 1001)],[(1 <<< 1008),(1 <<< 1015)]]
def yoRows (i : ℕ) : ℕ := ((yoRowsChunks.getD (i/12) []).getD (i%12) 0)
def proposed_yo (i j : ℕ) : ℤ := yoVal (((yoRows i) >>> (7*j)) &&& 127)
def yoPacked : List (List ℕ) := eval% natTable 146 (fun i => natWord 146 64 (fun j => (proposed_yo i j).toNat))
def yo (i j : ℕ) : ℤ := Int.ofNat ((tableAt yoPacked i >>> (64*j)) &&& 18446744073709551615)

def thetaLoWords : List ℕ := [0xc183050a10203060c1020204000,0x1e3870d1a3060b16285091020386,0x2e5cb162a50a132648911224080f,0x407cf9e3a74e1c386cd1a3264c18,0x509d3a64c952a4488d1a244850a0,0x60bd7ae5cb96ad58b15aa54a54a8,0x70e1bb76cd9ab468cd9b264c58b0,0x7efdf3e7af1e3b76eddba74e9cb9,0x8f1a3458b121c3870e1428306040,0x2447]
def thetaLo (i : ℕ) : ℤ := 1 * (((thetaLoWords.getD (i/16) 0 >>> (7*(i%16))) &&& 127 : ℕ) : ℤ) + 1
def thetaHiWords : List ℕ := [0xe1c3060a14285080c1820404080,0x1c3870d1a3468c182c50a1224408,0x2e58b152a50a132448891204078f,0x3e78f1d3870d9b3468d193260c17,0x4e993254a912234689121428101f,0x5ebd72e5ab162c56ad52952a1427,0x70ddbb66cd5ab468cd93262c5830,0x8101fbe7cf5ebc78eddba74e5cb8,0x8f1e3468b162c4890e1c2850a141,0x2448]
def thetaHi (i : ℕ) : ℤ := 1 * (((thetaHiWords.getD (i/16) 0 >>> (7*(i%16))) &&& 127 : ℕ) : ℤ) + 73
def thetaEdgeValueWords : List ℕ := [0x9b7edf2d94221e304c2d7738266f8d95f256ac47a676674b544692fb8c9a3009191f418d61c303fc40426e800000,0x3fffff7b4189eae993cb1d5b911715f26f6]
def thetaEdgeValue (i : ℕ) : ℤ := 131072 * (((thetaEdgeValueWords.getD (i/16) 0 >>> (23*(i%16))) &&& 8388607 : ℕ) : ℤ) + 131072
def thetaIndex0Words : List ℕ := [0xffff06ff4effffff0303ff02ff01ff00,0xfffffffffffffff0bff0aff52ff51ff,0xffffff16ffffffff5bff5affffffffff,0x20ff1fffffffffff1cffffffffffffff,0xffffffffffffffffffffffffffff21ff,0xffffffffff2effffffffff72ff71ff70,0xffffff37ff36ffffffff7bffffffffff,0xff3fff3eff86ffffffffffffff3affff,0x47ff46ff8e44ffffff43ff8bffffff40,0x91ff]
def thetaIndex0 (i : ℕ) : ℤ := 1 * (((thetaIndex0Words.getD (i/16) 0 >>> (8*(i%16))) &&& 255 : ℕ) : ℤ) + 0
def thetaCode0Words : List ℕ := [0x140300000381102c01,0xa000000000901a0a82a0,0x15000001026000000,(0xa020000001 <<< 38),384,0x1c00000040140c,0x1300800002a000000,0x5400048000000000c00,0x78120740000180a00015,32]
def thetaCode0 (i : ℕ) : ℤ := 1 * (((thetaCode0Words.getD (i/16) 0 >>> (5*(i%16))) &&& 31 : ℕ) : ℤ) + 0
def thetaIndex1Words : List ℕ := [0xb5b5b5b5b5b5b5b503b5b501b500b5b5,0xdb5b5b5b5b5b5b5b5b509b5b5b5b5b5,0xb5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5,0xb5b5b5b5b5b5b5b519b5b5b5b5b5b5b5,0xb5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5,0xb5b5b5b5b52bb5b5b5b5b5b5b5b5b5b5,0xb5b5b5b5b5b5b5b5b5b5b5b5b5b5b5b5,0xb5b5b53db5b5b5b5b5b5b5b5b538b5b5,0x46b545b5b544b5b5b5b5b5b5b5b5b5b5,0xb5b5]
def thetaIndex1 (i : ℕ) : ℤ := 1 * (((thetaIndex1Words.getD (i/16) 0 >>> (8*(i%16))) &&& 255 : ℕ) : ℤ) + 74
def thetaCode1Words : List ℕ := [0x8000903c00,(3 <<< 75),0,(7 <<< 35),0,(1 <<< 53),0,0xd000000000005000,(0x2c11 <<< 65),0]
def thetaCode1 (i : ℕ) : ℤ := 1 * (((thetaCode1Words.getD (i/16) 0 >>> (5*(i%16))) &&& 31 : ℕ) : ℤ) + 0
def proposed_theta (i j : ℕ) : ℤ :=
  bif (thetaIndex0 i).toNat == j then thetaEdgeValue (thetaCode0 i).toNat else
  bif (thetaIndex1 i).toNat == j then thetaEdgeValue (thetaCode1 i).toNat else
  bif (thetaLo i).toNat.ble j && j.blt (thetaHi i).toNat then 0 else 1099511627776
def thetaPacked : List (List ℕ) := eval% natTable 146 (fun i => natWord 146 41 (fun j => (proposed_theta i j).toNat))
def theta (i j : ℕ) : ℤ := Int.ofNat (min 1099511627776 ((tableAt thetaPacked i >>> (41*j)) &&& 2199023255551))

def gramWordChunks : List (List ℕ) := [[0xc3bcb,0x858197f5a9,0x852bb81dc07f372,0x84ad5822a381d7e7f13c,0x83cf582cb78144181d557efde,0x834e382f95810228144681d5a7f00d,0x83f1f81360831e680c6c8140481d137edb0,0x83a2d814908282c81a9e80c55813ea81cf77ecc4,0x84d1b7e8e97f6e87eccc7ce237f3cb7eced7e4c4804fe,0x8361280b697fcc77f1377e4ac7fab57f9e17f6917f2a37ffa0,0x82a3f7fbfa7eed97f9798156b804b08053c8062e809f980e807f688,0x8411d8088e7f7a27e79e814c182ab28093d80a4a80c2e813c081ccb7eb47],[0x840ff81b97820677f6407eab28288c8032d80ec380a7980c5f813f581d037ed28,0x83f7180d8481a817fb177ee7c7e41c816fd804e58097280a8f80c758140d81d1d7ee06,0x85436815998019e80aa281bd17eeb27e5e381c2c8050f8099980ac280ca98144681d5a7f00d,0x85f03807cb8117e80a4881aff814f47ee907de8380443804e78097380a9180c778140f81d207ee1a,0x86b078025d80a9180fd780daa81c1380d687ee9e7de958044e804f18097d80a9e80c848141d81d2f7ee9b,0x84f70800e480077803e1808548051d80d1280a047f6f77eede801e2802398048380502805f3809b880e3b7f438,0x84d657fca77fc2f7fb9b7f8c77f2e57f5417f0a67f7ee80c168018b7fcac7fc937fafc7fa1f7f95e7f65c7f2d47f2dc,0x865a1807ed7f8497f3f77f2627eb347fb717e9777e4da7eb7a7fa9d813807ffc77e8117f6397f4927f3137ed167e60d7e919,0x8489e8073a803c67ed817f75e7f78c7f1587f8587f5e37da2d7de5a8074f805ce7fa8b7fa407f6ff7f5947f41b7ee367e7417f35c,0x83a058154480d6d8051a7f5fa7f2f17f0ab807f77e1ca7e0d97e9097f9e280364804d27fa737fa2a7f6eb7f5797f3ff7ee187e7217f249,0x83886814518123e80bce80c9d7f6d17f3c2803967eb0c7ee907e7a57eaf07f16d803df805697fad37fa827f73d7f5e47f46d7ee907e7a17f68f,0x841a480a6d8089d8106d825448052e7f5ff7f59b7f3697ed7b7e7fb7e4fb7f2c27f087807a7804f17f44280b777f6de7f5687f3ef7ee057e70d7f1a1],[0x849578027c80d5981822816a980fd3806a17f51a7f1267ef1e7ec467d7f17fe387f1f37f9fd80376804e87fa817fa377f6f77f5897f4107ee297e7347f2ec,0x851547f3f580d058163580d2b81846809048055e7f3b77ef327ed117ec157d3877fe577f9b67f91e802dc8042b7fa097f9c87f68f7f5027f3867ed937e6937ed8d,0x8642a7fbc67fd6e807ea810b481d3e815cd80beb809cd7f03d7ea977e7027e3017f8827ff197f97c7f6d980285803c17f9c57f9897f6557f4b67f3387ed3e7e6387ea89,0x85c68803037fd757fe898060c80d128167c81198809408074e7f80a7f6e17ecf57e9c17fa647feb67faa37fa26801ab8028a7fb277fafe7f8997f7577f6377f1b77ec6e7edea,0x836527fd977fda47fe4e7fceb7fcea7f666803577f88f7f9c67fb7a804088066d8072b7fbbb801818007f8011c801577ff527ff21800e3801108023680271802ea804cb8070b7f980,0x87c6f7f8be7f8277fb987fa657f89f7f57b7e2a57f9fc7e5467e8e97eee680f7f80c4981b4b8000380618801ff80488805747fd577fc998039a8044b808e2809d480bb58133c81c3d7e691,0x879d27ff417feb57fb777fcc07f7727fad37f4be7eff67e76f7e4c57e8c67ef3e80f6e81849801ae80244805f180141806cd805ef7fdad7fd03803dd804898091b80a1f80c028139081c977e98d,0x85e7f7fdb6801ac816047f2937f0f17fbca7fccd7f6b57f0437ebe07e6097e9f87f13880f718171d8014d800e280d0080213805b6806b57fe367fdab80448804ec8097880a9780c7d8141581d267ee52,0x8450d8038b802ac80d71803667fb4c7fa1c7f6cd7f92e7f5657f48c7e76e7e5937e9e27f51d80cde8038a80292802678083480223806b2807c27fef17fe8f804da80572809f580b3a80d23814cb81de97f4cd,0x841c2804d380ff280974804b0803377fb287fa167f7b17f9067f45d7f47c7e6f87e5af7e9507f7038108e802a28027e80264807fb8021f80677807847fec57fe5a804b880552809d880b1480cfc814a181dbc7f34b,0x853cd7fe4a80e1b81fdf8018f7fe9d802407fbd77fd817f7b27f9c67f5837edfa7e73b7e2537e8c87f0488016f803a28027d80264807f88021f80674807817fec37fe58804b680551809d680b1280cfb8149f81db97f33a,0x858f47fd60803b1820e1803f7802ef803048046c7fa2c7f7ff7f3df7f7607f29a7fd0c7e6957e2a77e8fb7f07780209802aa80286802658081380221806908079e7fed87fe71804c680560809e480b2480d0d814b381dcf7f3f0],[0x8495d8007e800ae81b2e815c3805c4804cf80652803f27fc4f7faa58011a7fa157f55b7ebc57e6aa7e32e7e8f6800e3801b9802d4802b08026b8088c802298070d808237ff347fee28050e805a280a2280b7480d5f8150d81e2f7f723,0x8640b7f4db801178023f82f8e8068b804878034d80509803317fbe17fa097f8397f9e27f52d7eb977e5fa7e2347e811800358018f802b680292802678083480223806b2807c37fef17fe90804da80572809f580b3a80d23814cc81de97f4d1,0x88507801627feff804e38262980c868095f7ed70804648062c803db7fb017f8e37fa687f93f7ebe37e9347e3c77df027fae980013800df801ec8018c800ff80d368021c80646807507fea17fe2e8049c80539809c080af480cdc8147e81d967f20b,0x89cf37fe6d7fdf97fef68030780223806a2807af80301803e58049d802367f82e7f5397fdb37fcf37f28e7e9c07eab77dded7efac800807ff4d8000b7ff0d7fd6781a6c8021180597806947fe1f7fd8f80436804db8096880a8380c68813ff81d0e7ed86,0x8a93b80367809267ff3f801cd80319801ef805cd8071f803f28023f8056a804917f8447f5c77f1ab7f2d67e3977e2177d33f7f7f17f9c07fc328003880197801508018680909801fd8046d805567fd437fc808038a8043d808d4809c280ba38132881c287e5dc,0x8bbcd7f8347fcd67fc537fe358005e8020f801148051780616801888013e80359802957f6a57f3917f66f7f6bc7e7357e3a77db1b7ec067f7647fc5f7fedf7ffff7ff367fe8a813e8801f2803c4804a27fcc67fbe780328803e3808808095580b33812ae81ba67e185,0x8c21e8011e7f8637ff507fe077ff4180268802f9801a1807418091c803e0801ec8018d801307f57b7f2177f0317ef1c7e3967de977e7847edec7f80b7fa647fee17ffd37ffb280d8780842801e4802ee803be7fc287fb26802ad8037180816808cb80aa68121581b017dc08,0x8948e7fa907fc8d7fcea7ff167ff067ff5780141801718004d803e8805118014a800297fd7b7fcf47f8517f60b7f61e7f3f57f07f7ea3f7fdcf7f3147fa617fbec7ffc4800a28008f8011b801ff800ee80130801937fddf7fd528012d80193803e88043880524808d780d497ec30,0x894747fdfa7fce87fbbf7fdbc7fb377fdaf7fcaa7fb9f7fb487f88d7f6c07f5337f5cf7f5317f5437fb028077180a3080b2980f4b81364802cc7ff70800087fccb7fcfa7fe067fe517fe547ff5d7fafc7ff0f7fb1e7fab480025800827fc037fbf77fa6a7f9627f89d7f5897f1f27eb56,0x8c9d37f1017f9697f6447f3fe7f73e7f4f27f81f7f8d17f5ac7f4ff7efb07ead67e8237eab77e8dd7e9387f53181179817b381c9081fc2802128056b7feed803497faa57fac27fc3e7fcc77fccb7febf7f6607fe247f6a77f5db80098801657f8447f8277f50a7f3087f1807eb5e7e4367d96b,0x8c9e97ec587f2eb7f9037f6467f4bc7f79d7f5d07f8ea7f9777f66e7f67e7f1267ed017eac57ec7f7eab07e9c97f4de81017815fa81b8781d83800f2802508047c808767fb517fb467fc5e7fcdd7fce27fec27f6a37fe287f6eb7f623800cb801a37f86c7f84b7f52c7f3347f1ad7eb907e46a7db2c,0x8ca787fca17eef07f6cf7f71d7f4247f3917f50d7f6657f8a67f9927f6be7f50b7f0377eacb7e8887ecd07ea5d7e9927f46081032815dc817487fd7a800f880321801a680d237fce37fc7a7fca87fd127fd187fec87f73d7fe337f78a7f6cd80140802337f8c77f8a07f57b7f39b7f2167ec027e4e57df41],[0x8c6277f7b17f39b7f3767f98d7f6e77f4f67f5437f6f77f6fb7f9467fa077f7057f6127f1467ec767eaa27eecd7ec5a7e9ec7f38580fa581509817777f54b8019e8021380b0980b3b7feee7fe0a7fd097fd577fd5d7fed17f8077fe407f8597f7a9801d9802ee7f93f7f90e7f5e17f4207f29f7ec977e5857e492,0x8b7457fd317fa797fc6d7fca37feab7f3d27f4947f7ec7fa5b7f7bc7faca7facf7fab97f6bb7f2407ef1b7edb07f1687ee817e7a97ef3280bc980fc57fb0a7f2e6801e87fbff8270d804ec801467ffd57fd787fda67fdac7fedc7f8ee7fe507f9467f8a680289803c57f9c87f98c7f6577f4ba7f33c7ed427e63c7eaac,0x8b0af7fda07fa717f9347f9857f8b17fc357f9257f6e57f6b37f7e07f7e27f9767fa6c7f98e7f4f67f15a7eb797e8e17f01b7ed807ed877f66c810eb817a37ff34800e680457808fb80814807108041a8019d7fd6d7fd1f7fd44800337f9a4800d87fb207f84180320803267f5cc7f9f67f6ba7f53a7f3bf7edd17e6d57efc5,0x893688026a801f7800597ff2b7ff6e7fe967ffd57f8bc7f6fb7f6657f7f97f6a57f8037f7e17e5ce7f13f7f24c7eb797f41c7ede17ef7d7ee987f6568066280129801b08027580560808c880a0280aaa8067d803e27fe7e7fca87fe647fef37fb047fe737fb697faee8041e805b67fb047faaf7f7677f61b7f4a57eecd7e7e37f8be,0x8798f80f768035f803f680214800e5801ca800c68024e7f9437f6ee7f67d7f6d97f8577f7157f9eb7efef7f6b47f4bf7ee397ebb57f2237f1be7f1e17f8688154b80276801a3800207fd3b806468062680974814e7803417fdc77fcc67fd077fd637f6617fea97f7277f5618044a7f6757fb977fb377f7e67f6c07f54e7ef847e8a87ff4b,0x86a19812cd80744807cc80685805f3804ea8051e80443803487fa0d7f8897f7f67f9377f77d7f7567e9337f3767f68f7f6eb7ff547ec2d7effd7f2587f14f7f7a48016780249803a98034f8060f8099880cc080e5b809e58066d7ff117fec97fed17ff027fc417fe887fcae7fc498050e806dc7fbc07fb5c7f8097f6ed7f57c7efb77e8de80119,0x85bc380e5480902806ba8066f8059e804f3805968047080354802d07fa6b7f8ee7f8357f9a47ed6d7f7c77fa6c7f91e7f7097f6a57f0217ebe07efc67f2467f1e07f80680115801de8030a802d88059b809e180bfc80ee4809c3806437ff0e7fec47fc807fefc7fc107fe8e7fc7d7fc0680546806137fbc87fb637f8107f6f67f5867efc17e8e980177,0x8471980d53809f880a41808048079080f7081110807568047e80390802ae7f8297f7237efb57f4a27f7257f6047fb2e7fa8a7f6a4800637ef0c7ec3f7ef607f23b7f179802717ff407ff727ffa1800b1806c780bb680dd180dc680952806247fdc97fc617fd647fff07f991805807fc317fa3080052805617f7c67fad07f7cd7f6867f52b7efbd7e9537f5dd,0x84013803b08049a8175881ab281ac380e1d805d98047380307803338023d801e67f9a77f79f7f7177f86f7f78b7f6d67fa937f98b7f8697f8f17ee327e9ec7ebe67f0e17f609801be8007780150802998033b8063980a3280c2780d8280813805107fead7fec87fec67ff477fc3e7fe8e7fc667fc2280526807fa7fb147fac77f7ac7f6647f5007ef6c7e8d77f6fa,0x849ba7ffed81b298315a80bf380b7f80a2a807c6807b88067f8050b8055d80439803187fa4a7f7d87fd4d7fa457f73d7fb7f7fafc801db7f6947f71d7ec787e6197eb3b7f09f8035b801ab800ef801b880294802de805ac8093280b3e80c37807f0804ee7feb57fe877fe8f7fef97fb807fe7c7fbe87fb768047c806297fb4e7faf37f7a77f66d7f4fa7ef287e8457fc04,0x851ae7e95c808248144d8300c80f9380b4a807a3807088064480533803d78042a8032c8027b7f8fd7f6977f81e7f886802ef7fbf2804287f5cf7ef257ec897e6fa7f6c67fd047ef188014e7ea89801668024c8022580341805b280b028092e80b72807898004d7fe417fdf27fe09803087faf57fe727fb5a7fade80413805a87fafb7faa77f7607f6117f49b7eec27e7d77f859,0x863a9808b88007b80e8280ebf80e658096d80ecd80cc180b0780a0a808f48073e806ca805b5804017f81a7f53c7f4cd7f6277f4b37f3b27ee1e8046d7ee6b7f38b804a67f22d7e9ab8022d80172800a8800bc8019e802168058680547809f880a5980aa8806c27fd877fe5f7ff1a7fe537fef17fad47fe707fb387fab9803f9805897fae87fa957f74f7f5fb7f4857eea97e7bc7f777],[0x8669c80dd4805fa801ef8073980bc880b9f80a3880a8d8069580722806e5804ad8031f8033d801c7802017f8237f55d7f4947f6317f4977f47c7f3927f07c7ef7d7f3077f20e7f0a77e953800a3800f0800638006180114804058024480525808a8809328095080549802e77fe377fe2e7fe357feed7fa7b7fe6a7fadc7fa58803b5805367fab37fa647f7217f5c07f4487ee677e7767f51d,0x859d7804e9807e68079a805ae808ae80f6f803bd80c9580b6d809e48086d80841806e180564805d8802dd803a57f9487f69b7f6077f6977f5f67fc0a7f74a7f5b97f4947eca27ed2e7e32b803e77fde28023f80112800a980163801f28029b80572808f680a5c80af6806cb8040e7fe7e7fe617fe687fef47fb0f7fe747fb757fafa80426805c07fb0b7fab57f76d7f6227f4ad7eed57e7ec7f909,0x84448807aa803d1802aa80a3d802a3808f380a9480d0a808f780c9d80a6080afc80a948091a807ff8022d80596802877fa577f7ec7f7157f8187f6697f5a17f1707f1157f4b77f67d7fcfa7eb917ef047fd6b804af80263801448021e803578032d805f28097980c4e80db980951805fc7fef67feb67febe7feff7fc087fe857fc747fc0b804e3806a87fb9e7fb3d7f7ec7f6c77f5567ef8d7e8b17ff99,0x85ea680bcb800ed8080d808467fb6c802d480aec80ffd80e508108880d9a8099e80b4f80a6680994808368089c80776805437f93b7f6867f6237f68c7f5927fd127fb427f1e97eadc7e7fc7e11b7ffd7804b6803e9802ef8016d800e4801a98027d802df805b38093c80b2e80b3b80794804a77fea47fe7b7fe827fef77fb5d7fe797fbc47fb4f80461806087fb397fadf7f7957f6567f4e17ef0e7e8297fb13,0x859d57f97180d50800348102280b4e80141802e6808f280ee180d2f8102a80d0980b4480aa7809bc8090b807c480837807278050c7f9c87f75a7f6fe7f7437f6967fd767fd627f7647febc7eadc7e1677f0d780580804847fa51801cc800fe801ca802b7802ec805b88093f80b6f80c7c808308051f7fec07fe907fe977fefa7fb997fe7d7fc017fb918048f806407fb5c7fb007f7b37f67e7f50a7ef3b7e8587fca8,0x852827f95d7f16981b6e813c0803b9806187fba18056a80dd28129e810c2810cc80f1b80a4e80d1480bc0809fd808a6808ad8079f805637f8bc7f5dc7f59a7f63f7f4cc7fb96801a37ea247e7867e6f47f15c806738042a80363802518012a80104801e580843802a980577809d980ad780b04807457ff8a7fe987fe6b7fe917ff537fadd7fee87fba07fa008042d805c97fb107faba7f7727f6297f4b37eedc7e7f37f947,0x86408804b78015c7ff4c80f7d806b18064980681804928057580d038124e8108480f4e80e8d80c9180be080999807ed806af805e880550803bc7f69e7f3c17f37e7f4837f2ab7f4e27fe7e7f2947f1867f6a67f8e67f347803a8801e97fd667fda7804898064680bfb807588099d7f05d80b2b80b8880771804697fe847fe55801d37fef57fb257fe757fb8b7fb1280437805d47fb187fac17f7787f6317f4bc7eee57e7fd7f99b,0x86894804e38087d7ffb78048180d1780290805608183381091803a6808c280ba880df780fec80be880c09807b5806c18042e802c8801b28012b8010e7f73e7f47b7f3d87f4d27f3b97f3247f8db7fe777f9b38056b7e4117e2c6804158013c7fa197fbe580762809dd80d3480aa680bb57e9a08090e80bef8083a8048f7fe587fe0480c997fef27faeb7fe727fb4f7fad28040a8059e7faf57faa17f75a7f60a7f4947eeba7e7cf7f811,0x8808d7fdb68025d80d378082880c3d805b0805098042c80e3f80f52806cb80b2080d4e810e4809ae80e5680c9580bdb80aa9808e680724806cc805ab803d07f62a7f9057f1e17fb527f17d7eef37e7477e92080c2a805da803467e5828003a7ff197fea57ff5d8000b800a67ffe58021d804cb808d0805ed806ad802e88010b7fdb67fdc67fdcf7ffa67f9837fe5a7f9de7f949802f98044f7fa207f9dd7f6a37f51c7f3a07edb07e6b17ee94,0x886847f570801668021e80710807ab8084c80702807728063a8040d80bfb806da80b3280ced8114680bb780f2b80cd880b8180ac0808da806f2806be805a4803f17f5717f1747f11e7f2887f1417ef447e9b67f328804d7803527fe8d7f3c87ffaa7fe8b7fe5e7ff528003a8010e800038027f804eb809458045280706802c9800f48006b7fdd37fdd97fee17f9707fe587f9cb7f934802eb8043e7fa157f9d37f69a7f5107f3947eda27e6a37ee18,0x8848580013803c37ffdc802727fd87800c880166813d680b068096f8093180549804287fbd780c7381163814e1811e080fc980c6a80a6480925807588074e80645804537f4d47f1047f14b7f2997f19f7f0f08035380a348006a8003b7eaba801917ff917fe787fda97fe9f7ff9280019802248018080479807f7806958059a801e58004f7fd967fdbb7fdc27fede7f92c7fe547f9857f8ea802b8803ff7f9ec7f9ae7f6777f4e27f3657ed707e66d7ec4b,0x8890b7fd647fa837fc7e800838046b80620806458069980e908099a8071d8045e80944804587ffcd80c168110f80f9e80ff080e0c80a2080a3f807668050a804c98037f8028a7f4db7f0d77ef897f0ce7f07f7ef527eee880763800517ffe27f3787f9517fdb87fc787fd5e7ff57800bb8018e7ff7280354804df80a947fe1e804a0801017ffa07fd6c7fd9d7fda37feda7f8d47fe4e7f92b7f88980275803ad7f9b87f97d7f64a7f4a87f32a7ed2e7e6277e9f7],[0x886637fa147f8c57fa967fcad802358010a80270807aa8078980f0d80ab480783803dc807d98063c8093b80c6f811e181188810e580e6a80abc8088c8073c8053780504803ff802cd7f3137ee607eece7f08b7ef957ede2800ad8031a7ff7e7ff777fedc7f9bc7fce37fb877fae07fd1d7ff0b7ff707fe08801248041a806ce80431802bd7ff487fe4e7fd1a7fd637fd697fed37f82a7fe437f87c7f7cf801f48030f7f9537f9217f5f37f4377f2b77ecb17e5a07e57c,0x8572a800097fc877fa9b7ff4a801238003f800817fe688016380148809a8805538044d803a5801f980295803e880615808a880a6c808798070f805248042980339802408022b801ab8013d7f99d7f7927f7c17f89c7f81e7f7af803ff8036d7ff4d7ff607f8537ffaf7fe9c7fdfe7fd9f7feaa7ff7f7ffb58010580076801fb803b98024d801657ffaa7ff2c7fe8e7feb27feb57ff6a7fc177ff217fc417fbea800fc801897fcab7fc927fafb7fa1d7f95d7f65a7f2d27f2ce,0x8579a7fe447fa057fd837fed97ff797ff8a7ff4a7ff8b7fe017fe987fd517fcdd7fc607faec7fd677f79a7fd737fb277fa967f99d7f9c37f9c87f8447f89f7f87a7f8ed7f9897f9467f9f27fbc0803968057180633806c3807778009e8008e8009c7ff708006b80195805808011e8011080027800157fd367fc557fda87fe457fdd37fd807ff127fd197fc6b7fdc2800aa7fd3380183801b7804ee8017f803cb804807fe647fdec802ea80367806c180785808e880e77800717f2ce,0x88541803747f5c67fb7f7fb3d7fd6f7fcbd7fc067fc977fee28003b7fe1a7fd297f7017f7e07f5a77f8667f5387f94c7f41b7f45b7f25f7f2177f4767f0fe7f1a07f2787f21d7f3017f22b7f3837f710808d980c5a80d2080df48102980199801f0803a1802f0804b3806f4807d98020c8026b8026f801507fa5c7f6357fc747fedb7fce57fade7f7897fd237f7aa7fc67801e2804cc804208034d80e508017780d86810a47f81b7fe3b80aad805f680dcd81d1b80bbf7ffe7800de7e57c,0x885197fd5f7fe4b7f9277f9517f9af7fbbc7fb6b7fb567fda27fe147fe397fd9a7fc327f6267f6c87f52a7f2e57f7327f9c47f46f7f45b7efda7f84c7f08e7f1087f0ba7f1de7f1ac7f2d17f1ad7f4b97f8a48092880ca880d9880f91801228015a80310804c48036e805858086e8099b803ad803d7804c0802f67fab37f9e17fe967fea57f6637fcb17f8bd7f37d7fc247f946803c6804277ff5480894810c180beb8038b805c28047c7ef2b80a2c81a5b81d047ff697ff9b80065801657e9f7,0x882bd800037fd6e800c77f92c7f6e67f78e7f9a67f9837f9b47ff7b7fed97fcc57fc297fa8d7f54a7f5c77f4f07f6097f7187f9ab7f4fc7f1637f18c7f3667f0df7f7b97f2737f3e17f4627f5257f5427f6607f8de8091480c3f80dc880e408033d80351803b0806ba8039d806e980aa880c378074b806ab80889805827f6e77f47e7f3e47f89f7f9237feb07f2847fa0b7f8b57fb927feb67ffb57feef8060b80a5780867814c880ded7f0ba7e1917ff037ff387ffe47ffa37ffd7800a6801ab7ec4b,0x883307f5498005c7fc7c801ed7fa3e7f8017f86f7f9f07f92e7fa3a7fe3a7fc937fc2f7fb497f9f77f25b7f5a37f5787f38e7f8937fa5d7f3de7efda7f0d97f1367f60a7f3197f4857f5697f6207f7117f71b7f88e7fa1a80a4d80d7a80eae8016d803cb80417804108067d8066d8097980d6a80f5e808f58092080a0f806097f68b7f4847f7127fb277fd027fbca7f670802a87f90780021800468024480120806af8115d807e881beb817267ec0c7f8f47ff2c7ff5d800067ffd080005800d9801e17ee18,0x87d7e7fb557fe7a7fbac7ff688022a7f9f37f7fa7f9537f9b07f9cb7fa4b7fb677fb2a7fb777fc2f7fb437f3ba7f7d97f6a57f57b7f7ad7fa757f4737f2797f1df7f1627f76e7f3877f33c7f3047f5367f6cd7f4507f5e07f6e280cd18116f81331808978043f8061c805f28085e808fd80bea8113f813d3808e78096d806508036e7faa27fa977fc91804c7807b27fe09804587f4787f7f27fce78084e80c3080ef7813d88209e81a897ffcf800048009b801027ff377ff67800107ffdc80012800e6801f07ee94,0x86ec77fefa805d6804c5801d680271803427fa387f8f77f9467fbaa7fb697fc397f6207f9bf7fd3e7fc3e7fb927f7657f6177f5467f2a77f53d7fa7a7f6967f65d7f0397f3f57f0427ef217ed737ef9b7eea77efd67eee07f2117f53080ad4810398045e803fe8053f805328041b805b48057e8046a8080680ab1806a18035f7fff67ffb08007d8017f7fe157fe6e7fabc7f3b67f2dc7eebf7f1b67f51380f08805b2815f6800af801cd8004e801408018e801ad802508000c8002b800c7800cb80106801f08030d7f811,0x8605d806d4800ec803918025b80304803738035c7fa1a7f8527f88c7fb0c7fac17fbb27fbdd7fc1b7fdd07fb6b7fa667f5be7f47e7f4f17ee817f59d7f90f7f4db7f29d7ef8d7f1cb7f2e37eff17efd37f1167f2567f3787f3ae7f47a7f4f880b23810c9804fc8055a804998068680423807048048c8043680635807de8064c80572805f8803ad7f9d57f77e7f2b37f7958112e7f44c7f2c27eb597ed507f35b80f747f7597fc1a800b280207800528017c801ce801d9802878002f8004b800e5800f28012d8021b8033b7f99b,0x85be080779803768019d80305801fc804aa805aa804a57f8f37f67c7f7fd7f8fc7f8eb7fa1b8017a7fed67faba7f9a27f7a87f2757f30f7f3567f4a07f6897f9e77f4667efab7ef207f0047f37d7f0b77f2a37f0267f54d7f7607f8bb7f9bd7fa798094d803fa8060e806e1804bd8061280366806998037c8077f80b3280d49809cd8092d808be803677f4f77f1627eea27f0837fd8580351802c17e8397ec87802d280031800aa8009c800b1801fb800528016f801c0801cf8027b8002780044800df800e98012580212803317f947,0x84e3f8072c806f5802d080b98802838041d8073f80790807fb7f9b17f6f87f68c7f9fc7f7207f94c7f6ca7f6827fad77f92b7f7c07f0047f21f7f2a97f4857f8477fb4a7f7457f0e37ef3a7f0ac7ec537f0947f2107f62e7f39d7f3e37f6337f79f7fcda807b67fd187fd237f8ec8044780028801d98036e8078d806f980b4880dc180b988098180c4c808697fbc57fa407f5647f4b57e7a07e8837dcd38085880571803d18006f800d5800c8800b78027b8005a801f28024c80231802f2800738008a801208013e8017c80271803977fca8],[0x84a8b7e7827ffcb80a3d8078d80891802d2805d18090980985807b17f82b7f4d27f89b7f7827f6a97f8ec7f69b7f2477f7d07f7de7f6e27f0687f3c27f4af7f3d37f9987fdf87f7ed7f05a7ef8e7ef797efa17f2377f6287eec87f5cb7f8957fbfd7fec4801607fa907fbd6800467fd818051c8029180377805ba80b8080a2e811c9816b580fa480da1807e7801407f3e97f0497f14e7e9c57e4707d985805b9807ae804d58035a80052800c1800b3800b48023f80056801b58020b80203802ba800508006980101801168015380245803677fb13,0x8388380246803b88080b805ba807508078c8079080671807d580a1f808877fa037f7bc7f8557f9687f8797f9d5800967fce27f8cf7f85f7f6547efb97f2a97f3fe7f3777f73b7f9ab7f6577f0a77efa17f05a7f0ee7f27d7f50c7f4cd7f8937feb97fb5e7fd9b7fba38033180515805bc8067c804738030b80396805ff804cb8085780c8c80e8080be980b1880c6f806747f8747f5cb7f3057f37c7ffca803c67f8a77de8b8053e8040880102801be8018f7fed2802257fd0d8003d8038a801b88032c8069e800c78015980188801c7802c3803ef7ff99,0x845b77f7b2805fc80a56813c68040d8049080508808d88086a806c4807fc8085f7f94a7f61f7f7e37f8f97f6357f5977f4a17f3177fb237f9ab7fa747ef207f3697f4bc7f2967f90e7f8f27f4777f5117f1317efd77f2b57f9467f8387f5167f9467f7c37f8a87f4977fde2801038058e8089180ae8804d7804cc803628055380f6b80c96814a580c2580de880dc280adf804667f6837f3d28101980e9d80ae07ef608038b7e18a802148009e7fffd800cd800447fb787fbda7f3a08048080214803727fd1080fa48003f800da800e38011e8020b8032a7f909,0x8468d802b38048c81b148009880d2f8085e805fa808258037b80480809cf8082e809f07f7bb7f6387f4a57f6cf7f7917fb6e7ff187fa3b7f1227f5db7f3f77f1ed7f3ec7f6af7f3247f3fa7fbd97f8b97f2ae7f2a27f2b07f1477f4367f28e8084f7f8f97f60c7f29b7fdfe7fd8280c1e809c8807288035d80b8180a2f8087a809e9804ac80b47812e9818f7816b480f8a80606808dc808da80ba97ff9080f3c80234812077cffd807198018b8012c7ff888002f7ffb77fe75800767f4fc808b88011380158801e87ffca7ffee8008e80081800ba8019d802b47f51d,0x852da7fe187f71e80e6d7fc977fe4080d6f807e0810c7808c6806348081f807fe8075d808127f9657f4347f4127fa0c7f4937f71d7f6fd7eed17fee28032a801eb7f1337feeb7f8a47f35f7f6e07fca77f8817f7d47f2267ee717f27c7f3787f3757f5187f3db7f5407f2bc7ffa77fe0f80778808e5809aa8087780b50804ce805248087081190817638238d8215380196800ac800f5801c7804c78061e807978088e8062a7f4167f506805a9802dd8020a8001d7fd0a7ff1a800ae801b68004d80129801758019b8023b7ffff8001f800bc800bc800f6801df802fb7f777,0x8502b7fbbe7f9448054980c9e809db80a9b80936808d680dcd805c080855808a680920807e6807a67f60a7f9717fba97f7447feac7fec07f8877fc977fddb7f1607f9817f6577f1927f9397f4d37f6ef80a4d7fd027eeb17eaf67f21f7ee6b7f2977ef1b7efb07f20f7f3a57fece7ffc27fe8580a0680d5580fb080df28125c8094581d0681a7081bb380251803fb805c48086c8037f803538020880074801147ff7d80020800f0803c78022f8068d80422801d2800a58014d801808022a7fc168004f8014b8019a801b58025a8001280031800cd800d28010d801f8803157f859,0x84a047ef80800467ffc2805ce80bef80b7b80a6680881809d280875804d48072f808cf807bb8075880768800318003d7fee57ff7f7fd3e7fbb47f9837fc547fd547f6de7f8197eba77ee327f1b67f4ab80adc805d87f1657f10c7e7c77ea687eb2b7ebdc7edb07ee7d7f08b7f5837fd6a7fe1a7fdac80b4080f3380f8780ec0809da80eaf8082b80280803aa8051c8069f808e5805dc8059c804fd802a57ffe8800528025d801df801588040e806008081380532803a080063800cd800bf800b68026380058801d9802328021e802db800658007d801148012e8016b8025f803837fc04,0x836777efff7ff2980258802c38023b80c7380542806f4808c580c0e80ad7806138063f8038880499806f2806a17fed27fde37fc687fe097fb0f7faa37f94a7f9457fa927f8947f6c47e9b77efcb7efbb7f2517ffa57f9df7ec667e9767e72c7ec5a7e9947ef767fce27f92d7efd17f3fc7fb1b7fc427fc7e808ac80c8e80dc18050680f4c8020f7fe0e7fcf1800c78032f8099a80e41805ed805548033e800dd7ffb47ff3e80358802958034c7faa480704804858035f802ad7ef3f801738014d7fcef803218006b80257802de802c8804ac8002b80051801198012580171802a3804157f6fa,0x835747f57180a4e8019a7ffb08027980335809ae80a5680ba48096180b57808678039d80653808ca807618075e806f07fc577fb837fa3e7fa207f9da7f8957f9217fa377fb757f5797f7037eabf7f0587f0fa7f64c7f2d87f6617e42f7e7a17ed2f7fe477fa747ecd77eec77ee9d7f0b17fdc17fc797fe287fd9480a3480e1380fa080eb78026e801be800848014e80d5b8066b80c50809b980699805f2804838022480003800a58034f80046803368009a80771809f8805d68040680046800fb800e580103802ec80073802208029d80288803e8800308005a8013a801478019d802f3804927f5dd,0x837c37f26180219828cd81ca5800557fc557fa4e809058098d807718086c8090e807fe807e88095d80941809338098b807327fec5800697ffde7fdd77ffd58002c7fcc67fae57f6947f3e47f3df7ee847f01a7f2677f59b7eb807f0727f1d77f79a7ef437eb987e9077ec5f7edfd7ef337f1127f6267fde47fed17fe5a80bfb80f72805148030880bee80ef380c39802bd8054d80558807278088a80734806a3806318035d800cb80128802248014a80197803b8805a8806a7806b3803bd7fff07ffb57ffca800087ff4a800647ff327feca8007a7f994800df800ed8017d801b7801f7802f88042780177,0x8530c7fa017fefa8195e7f48f7f8097ff967ffb98036280615803fd8058780727809608090f80939807908092280a9680918807b37fc427fc687ff937fb187fc487fe267fc8b7f7e87f7297f2ab7f2557ea917ec097efcb7ed8d7eb3b7eb947f70880c4e7e5497e8b37ea4b7ec8e7ed2e7edc27efb17fd6a7fcff7fe087fdd3802ae803378040280c4280380803078042a8112980490805928071d8088d8072d806b780644803528003b8008780145801078036e803628058d808fa80424806267ffe27ffdc7ffb57fefb7ff3b7ff77800988015b7f1368038f800d7800e680176801ae801ee802ed8041c80119,0x85bc27e4387f03d7f9d481aa27f39f7fcb27f73680f6d7fe2980a017f54d7fd71808508074c804fe808498075480a74809c580875807517fd947fcbb7fbdf7fd1c7f9f27f9d17f43c7f4c97faef7f4157f58c7eade7ed057eedf7f2657f1837f2bf7f02f8025d7e4487e67f7e7147e8af7eb1e7d59a7f9517faa17f9e4806108033b800de8012d801b78012580170801178005c7ffa280f1b803eb80661807da805bc804d6802c1801038026480349805d380432805b47f3d1804c480887804338055c7fff8800127fff17ff697fff17ffae800d48017a7f5618034f800ae800c18015380180801bf802bb803e67ff4b],[0x87a077e9a67e5757fa1c803b2824e47f20b7fb998041b80320806158011e7fe1e7ff7780434807b28084f80a19809d3807718074680aef807ce7fca87fb057fac1803397f9017fa407fa617fa7c7f9097f6317f4f77e8ac7f43b7ed3a7ef927f6537fb517fef37e08f7e1067e4d67e1dd7e5497d99f7f6d57f84a8042b803d2803b780227800588006a80137800fa801d580181801e68025c801f0802bc8043d8052a803e6802ff802b98018a800478007980064800738000280308802be80167804307fff37ff307fef87ff2a800437fd58800a97fcb97fba58050b7f2ce8001b80039800d4800dc8011780203803217f8be,0x8920a7d09b7e6937ec3f80410803e280bc77f0ee7f655803657fd48809a18034c7fcc27fdeb8040680451805a8806ab805a4808c7807d980841806cb7fb967f9987fb657ff177f7047f8fe7f98d7f8e67f7e97f4357f2bd7e4b17ec1c7eab77eafe7f4077fbff81b637d8b67ddf27e1e07e4e47d1237e793801d6801b68016b800f58011e80045800428005680126800e18025e801dc8042a8051180371804b7801fe80390800e9800787fff97fffb7fee38001f8006b8014e801fc803db803148072b801bf800c6810d28002e80020800a180092800397fffd80036800be8012c7ff527ff80800277fffa8003080108802137efc5,0x897517d54a7e9527ff2d7feb180b1282a3e7e9157f8847fc70806967f9268062f8010f7fd537f89b803ea8051b80649809da8068780567806bf8086f806fa7f9e37f75e7f7e77fcdc7f5d07f78d7f8127f8cd7f94c7f1b07f1bd7e3b77e6767fb327ea997f41d7fb2b80ddc7d6af7dc347e3c67bc917f0a67fef6800417fe147fd2f7fc897fc5d7fd577ff067fe107fe057fe377ffc48001a800af801967ff21800348001f8003a7fed37fe257ff4c800707ffa2800107ff2f802448018e8055c7f974800c77fe877fe877ff277ffec7ffdd800997ffd18002d7ff377ff628002b800787fedf7ff167ffc47ff7a7ffad800798017a7eaac,0x8b22c7d8d87ed3b7f6e78050a809a3808a081bb37e6f17fc5b806fa80b598078e800828001a80372802627fc4b7ff0480334802fa8022c8023b802cc8034b803737f7627f41b7f2b57f6bc7f5497f6847f7cc7fb4e7fd0e7f6277f56e7e4cb7eef87ece07ec927f6137f9877dbb07d0ca7d7e37d8f37effa7ee627fc3c7fb8b7faee7fa827f9977f9887fb5c7fcdb7fcdb7fd937ff347fe3e7ff8b7ffe98011a7fdc47fe8b7feed7fef07fcc07fbf97fb6f7fd427fe367fe397fe9c800f1801dd803b1801de7f6867fc2f7fcbc7feb87ff9d7ff8d8008e7feea8001d7fe4a7fe657ff7b7ffa17fe567fe987ff4e7fee17ff107ffce800c37e492,0x8b9b57e0237e8067f6087f8027f6c97fc2d7f9127fe067f57c80a3080ad980d7f8032b802ba805b0800047fd7b7fd687fd5c8000b803a7801ba7ffe4800bd802388019f7f1067ee857ede77ef557f3d47f7057f46f7f4247f0b87edcb7ec877ef557e2277e41d7e7137e59f7f0db7d2da7ebc87daa37f0157ece17fd227fa037f9f07f83c7f76d7f6d67f0587fa077fb977faf37fbcc7fcd67fe147ff4e7ffc78016c7fd267fde87fe007fde57fb887fa977fa607fced7fd347fd0b7fc167ff5780023801ce7fd797fbfa7fa247fb2c7fe577ff587ff48800857fe20800107fd7b7fd897fee27fee57fdde7fe2a7fee87fe5b7fe887ff39800237df41,0x8b3b07dfa37d85f7e49c7f3827f79d8020f8061e7fe5f800c77fe0480bed811078135b80ad17f7707ea33808d18055e7fbe77fc2a7feea803b7804db80177800a780404802fd7efc97ea9a7ec2b7f13f7ee757f1437f17e7f2007f1b87ef237ecdd7d9757e9d17dcb57dfde7f9a37fe577ebcd7e7537ec0c7ef757eb487fa9f7f6d67f64a7f5577f4e57f36e7f33b7f72b7facc7fb0e7fbc47feeb7fbda7fe1b7fe757fff77fab77fb3e7fb397faa07f8867f78d7f6da7fa7f7fdf97fde27fe478017b802b9804b5802727e9667f8927f9f87fe0c7ff237ff138007f7fd85800057fcdc7fcdf7fe6d7fe557fd837fdd57fe997fdf57fe1f7fec67ffa97db2c,0x8ae337c6e07d2ea7de657edbd7f9297fd8d800878064d7fe187fb717fe3f80adb80c0d80f22800467fa9a802d28051b7fe8f800387ff718007e807228055380335803b0803c18038d7ed3c7e8d97ec597ed2d7ed437ef1d7edcd7eed57efc97e6fc7e83b7de197d93e7efcc7f6fc7f82e7fba57e45c7e74f7eab47ec377feaa7fa317f62a7f7557f4447ec387f28c7f2747f7067fae57f9f87fa147fbb47fc827fe2b7fe98800447faea7fb467fa977f9da7f7f67f6d67f76a7fb957fe497fe987fcd08014b8011d802947f7e07f6477f6be7f9147fe78800197ffe17febe7fd537fcb17fb287fe377fe357ffdc803447fdb17fe777fdc97fdf27fe957ff747d96b,0x883717d3e47dffa7eb017ef467f93c7fe4d7feee802d4805207ff237fdff8015680759808068084a803c57fe277fc9e80572803007ff7b7ffc3800768024e802ea8016b801938023c801af7f6017f3877f5cf7f5fc7f6167f7247f5847f77b7f6497f4557f49a7eaaf7fa097f7cb7fb627fc277fe117f22d7f3157f53c7f6067ff497fce77fad37faef7fa057f9597f8b67f8a77fb07800127fcea7fd407feab7fdd57fef87ff2b800157fd2f7fd6b7fd597fd007fbc47fb407fb0d7fd2e7fe9f7fe887fe69801e3800b5801a47ff877f6917fb6c7fc537fedd7ff747ff6c8003b7fe6d7fffd7fe177fe127fef67fedb7fe8f7febc7ff217fec27fed67ff247ff917eb56,0x88bad805648058c801f5803f4801228000080167801d0804e68019a8061e80cb88087e8014a800a5801b68033d8052d802aa805568000e7f8ad7f4d27f45d7f6a77f73e7f4f47f3807f31e7f4d280625806be807a180a7480893807d780c3b80e98813bd81420805c880d9180228804688059a7ffb1801a780ff180dc880ea78011c7ff527fd577fba17fb937fabe7fa557fa227fa317ff107fd047fc967fd0a7fdbd7fe797ff477ff898008c7fdbf7fe117fdf37fdbc7fc867fbf87fbe97fdc67fe497fe247fd507ff5f7ffce800a27fdb87fc8b7fbc07fc937feed7ff7f7ff778003d7fe8e7ffff7fe387fe367ff0e7fef97fea27fece7ff317fed77feec7ff3c7ffaa7ec30,0x8a7a37d9d98079c807f38020780575801bd7faee7fd9d7ff8e806137fce0807b481b3880d717ff9b7fd34804d87fefc808a67ffbb805737fe1d7f08d7eadf7ea397f7677ee6b7eac97e9607e6f97ea3580ca28106e812978145b814ad814a781b1281e8e806d880d5d80b96819ce80aa7809c880b5d80176804b5820ad81cec81bb5802a27ffb57fc047f8d67f8b17f71d7f6537f5d17f5e97f94b7fadc7fa1e7fafd7fc337fd8c7fef47ff73801457fc5f7fd137fd047fcc27fa5d7f9587f92e7fc487fce97fcaf7fb677ff107ffe48018e7fc857fa9f7f8e77fa397fe1c7ff2e7ff1e800807fda6800087fcfe7fd037fe867fe737fd967fde77fea97fe0a7fe357fede7ffc27dc08,0x8a57d7daf17e51180d0580d6280780808918082c801ba7fc357ff677fd9d7fd55800f17fd78806cc804cb7fb277fbaf801ba802278017a7fea77fc0a7f3f37ed757ea997ecf77ef687ed987ea677e9687ed3180eff812f4815078166281548813f6804b3806ed808c580e2b80da0818ca80e7380bdc80c3a812408106f822f18225480471802e1801177fe097fb7c7fb1e7f9f57f94c7f8ce7f8e37fb287fc1a7fb897fc5c7fd487fe737ff8d80002801887fdb17fe7e7feb17feb27fc597fb767fb387fd617fd697fd4b7fc917ff8a8004f801fc7fe257fcee7fb037fbd67fe807ff757ff66800897fe76800157fdd37fde67ff247ff357fe117fe597ff137fe947fec27ff78800677e185,0x896ee7d9717e35d7edf480990809f8807158057c805f1808a98074e805d3800ad803488092a7faa17fd877fa357fd1e7f74b8004b7fd327fd6d7f9b97f91f7f23f7eda87eba97f5f17ed527ec647e97d7e9487ee2380f1a8128b812ab8139d8035880256804338084b80a5980dd180e6d81a2080fa480da280fd5815fe811ad804f481e338026d81276802307ffa27fd957fd097fc357fba67fb2b7fb3e7fca27fd167fca97fd727fe247ff2a8000780074801bd7febd7ff9d800058003b7fdea7fd237fcd47fe407fdcf7fdc77fd7e7ffea800a4802527ff6f7fec27fcae7fd1d7fecf7ffae7ff9e800917ff1b800207fe7c7fe9b7ffa17ffce7fe737feb37ff677ff017ff327fff2800ea7e5dc],[0x8837f7e5c67e1bc7e6d17f05280bc880d188066f809d7802997fd207fd2b800c7804a9808a47e3af809db802497fd9480e3e7f3197fb497fb857f9467f6467f9697f2097f06c7efb07eaa87ecd67ed5f7ecee7ebcb7f01381035813b68051c80643803cc802d3806f98092380a0e80f1e80f358188e814cd8112380f348128b80636825e180043812548036b8041f80273801488006c8002d7ffcc7ff577ff667ff3e7fed37fea57ff5c7ffa78006c800de8013c8021b80095801978025c802ef800ae800187ffad7ffc97fe837fea07ff1e8009580139802ec801b4801fb7ffa07ff5e7ff5b80011800028009e8003d800347ffa67ffd88007d800dc7ff1f7ff517fffb7ffc27fff7800c9801d07ed86,0x8720f7dd2d7ef807eb467ee167f35080ea78105280c0e808f08046a8091c80930807b480956809ca801ec800778034d804727f5bd7f0ae7f86a7f9707f7137f4be7f9bf7efd47efec7efd77e8027ea847ebb07ebce7e9f97ee3a80351804298053c803aa806c9805bc809bb80b6480a3080f7680fcb81caa8189a81446814e08041380b6d803ef8004e816b78039f805438041d803778026c802848023f801cd801da800c77ffd97ffd08007e8008b8012b8015c801b280252801ac802c2803be8048880250801d68015b800b17feed7ff2180014800f980191803468030b803e18015d800b27ffae8004c8003d800a5800e98003f8005680094800ff8017c7ff857ffaf80053800348006b80147802587f20b,0x853ff7eeda7ee697f5197f8957fb8c7fbb5806a38063d80435801e07fc247faf27fd157fcee7f8d77fb61800eb8011e7f5d17f8d7807cf7eed97fe0f7fa8f7f23a7e0a37e8977fda4805c07edb97eec87eb997f6537ebf07fb5f7fc32805a3806128066c8073d8067380417808d080d1080df08123c811f381b70816b28118c816228175380305803a6801d280e0a8030b800778005d8008f800117fee17fe887fe597fe8a8024c7fd707fcbb7fd507fcf77ff957feb37ff767f6867fc45800908003e80120800c57ffa68001a7ffe5800b080132802d78009e7e625802e18017f803997ff248026a7ff057ff497fce07fee67fd697ff587feba7ff5d7efd4801de7ffc37ffe88008880079800b280195802ab7f4d1,0x838b47f56c800347ffa77ff5b8002e802c0801577fec77fede7fe1f7fc947fa987f9a77f8ca7f03a7f32a8023a7f92f7f8c57f5527fb997f663809727fbd57f38b7edce7ebe47f15e7ed7b7f3c77f3627ee857f64c7fcdb7fd197fcd47fbe58053d808ae807ac80557809928070c804aa80c8a80ab580c9280da1820058153b8128281b608113580091801338031f8028c80fc17ff8580053800c58008d7fffb7ffae7ff777ff5e7ff6f7ffc07fff98008e8006d801a68028e7ffc47f487801fa800c67f26b80393802b580165800f58007680089800ac7ff7b7fffa800f77feaf800cd7ffcd801518003f7fe6c7fdfe7fe1c7feee7fa2d7fff27faf67fa237f7c17f2967fff780018800b5800b4800ee801d6802f17f723,0x84a277f58d7f83b7fb047fe3b7fc387fe9a7fff580046805d4804ea803aa800537fd437fda67fafe7fb207f99e7f6e77fd8b7fa2e7f5207eecf7f41c7eeeb7e6f67f02b7e7eb7f5e57fc227ed3c7ea867eb457ff167fdf27fd947fd037fa787fc0a8068e8086c806a0806d0809b7808d980abd80d5480ac88102380e3281a50813a180dfe81220811aa7f7f47feb080e42804708023080a8a802c6801a48046f801b9800ae800127ffa37ff6a801f7800cd800067ff628016c8039d7ff77802727f6ee7f967800488010c8017180117809098031e8016c80246800a28046d802a5807f27f705804ad80217801417ffd08006480056800a880131800448009f800e380136801bf7ffaf7ffd680077800638009b8017c802917f3f0,0x8333b7e3ca7ea7a7f8e780c847fc2a7fff27ff9d7fd357ff0580197803007fdf07feb27f7ba7f7237fb0e7f9217f9c27fa337fb3f808237f3dc7f5ee7f48d7ed167f7e57e8147de447effa7f7a77e5857f5868004a7fb727ff8b7fd657fb5c7f9f47f959806098085a809288077e80b9c80a7480dbe80d8a808d8811ac80eea82016818328140a815cc7fc7e7ff3a80566805db80462802f0804988020f8018a8004c801038010e7ffd17ff7d7fef67ffbd8008c800e8802df7ff0b801917ff3b7ff437f6737fc3b8036680335801be80150801457ffb77fffc7ff9580280802fe803d8805cc808267f23e800ea800817f3538005b8004d800a7801158004280084800c580121801a57ff9f7ffc78006a8005180089801688027b7f33a,0x826127f58e7fcef80a27811857f90c7fcc27fc877fe4a7fe3c7fe73802be802108028b7fc167f8ee7f9327faf67fd0d7fa9d809ca7fb767f52e7ee207f3a07f66b801ed7fe197fdb67fb207e80c7ec487f3fb7f9477efa37fe247fb037f12a7f6787fa2e7f49f806a380848808ab807e88089a8065a80f3280e9580a2c8109480ee881d6781722812dc817e77fd9f7ff5e80387806258034b8021a80329800f3802a28024c8020b801a58019c80174800af7ffba7ff5c7ff947ffee80035800947ffd27f3b47ff4f8021e801a1801c1800f080174803f4802987fd237fc657fd397ff1d8006b805c0800848021e7ffb6800227ffe37fc3b7f36b800a7801188004280086800c880123801a87ffa17ffc88006b800538008b8016a8027d7f34b,0x825977f67980549810f5804167fce57fecc7fd56802238005e8002d7ff067feef7fe9f7fdf47fc147fa697fa8d7fa027ff227f8c87fb667f25e7f7b97f72b7f737800167fda37fa877ecac7e7317ffcc7f45c800377efb97eca27f1977f5bf7fb977fb947f8b57f9b880782806d580733805d4809898086f80bb080e5880d4a80e0980e6f8210780dcc814c8814a57febf8008a806fb800a88032180392803b18029a80335801e8803cb8033c803cd80393801d97fdc67fd557fdbd7fdc17fef1800e2800e08023a7fea27fea07fd607feb0803cf803d3801b7802167fd887f6d37f2c97fe0c800a78001e7ff4b801b47fda97ff9e800407e40f7fd0d7fc958011b7ff258017f801ef800e2801d88005d7fe348008880079800b280195802ab7f4cd,0x83ae77fa6b8184c811b97f09d7fa797f59c7f5778064d80412802ba800a27ffc17fe227fe417fb237f8be7f46c7f2647f24c7f56c7f85c7f6db7fc2c7ef897e7c37ea6c7f5987ed3c7ef77810467e0127fe02801657fc917ff6b7fcbe7fdcb7fb867f9c87f88b7f7bd7f86c804908055c806508065e80961809e5810858110a81089814898142b822c681a438170c800a7803308008b801a48020b8026d802df800a28006b7fefa7fc707fcde7fd5580095800b48021a7fb937fb137fcab7fc447ff777fef9800b1801647fe2c7ff787feea7ff887ff5c7fe057fd4f7fde37ff367ff597fe937eb347f1e8802fc801f1802517ffef7ff9a7ff6a8001b8000d8009f8005b800367ffc57fffa80094800f97ff317ff628000b7ffd68000b800df801e87ee52,0x8553f7d5a27f8fb7ff267f0627fd6b7fb03807ea80bab80a797ff757ff9d802137ff197f9a27f9797fa467f6307f4507f7507f4dc7fa5c7f04a7f850800497e2587da2e7e4907e62d7f847808457f7b67fe378063880471802557f94b7f6c37f8767faf47f9e97f67c7f4b17f6758043b804c3805fd806e88090880919808a480aa9810f88160f815898241981bb9816ea801227fef58012580231804b580381802f7801e67ff927fd997fc557fb417fae77f9cb7fa387fbea7fc537fc127fccd7fd877fe207ff327fe997fec98014a7fe80800d6801637fe5b7fd237fad07fc998008c801338032c80365803bd7f0ba80083800537fe197fe347ff187ffe77ffd78009f7ffc4800317ff237ff4f800078004c7fed77ff127ffd27ff867ffbf800a28008e7e98d,0x856b67d84b7eb7280efb7fbfe80c1b80aaa802c0807f2808787ff85802777fdd3800947fd777f3597f3ff7f5ae7f0047f94a7ffe87f3307f33f7ebbb7f5be7d8357dc777f24180924800927fb1b8046a8090180984805957f7a27fb737f8237f7d57f4807f5f17f4b17f2907f0fe7f42780352803078040280583807708072380f1d810f3812d58190481797824c881ce3800368005e7ff1c800198001d801f8803a18035d8034d8012e7ff367fe5d7fdba7fd387fca37fcc57fd8f7fd907fd277fdfb7fe9d7ff8b7ffd7800df80242807ff80221801b48022c7ff377fe7d7fe1e7fef67fd737fd667fdc98000b8003f802067ff687ff337fd057fd5e7ff418005e8004d8013e80135800d280015800667ffb67ff5d7ff8e80051802328014f80349801337f56a7e691,0x82e577f9e77fd2b80efd804267ff9e7ff78801af8015f803d180192801e27ff4e7fd8a7fb847fd447fd127fcf97fcbf7fc067fada7f9d47f8817f9787fadd7fa388032d803ff801d77fddc7f0407ff90800998021480223802fb801a97fec27fdd37fdc77fd437fd8e7fd267fca17fc397fcd2800fa8010680144801a08024180251803f68043a80455806718059f80935807197ffd17fff37ff747fffc800098006e800c5800bf800a7800017ff897ff607ff307ff0e7feed7fef47ff3e7ff5c7ff437ff757ffa07ffe18001680033800897ffd98001b80048800607ffae7ff7f7ff697ffad7ff607ff5d7ff667fffe80019800847ffd27ffc27ff2f7ff4f7ffc68000a800058003f80024800207ffeb7ffff7ffde7ffe67ffd47ffea800498003e8005f800e37fdbc7f980],[0x8517880cc28083680b9a7f6e47fe9580118806387ff387fef47f7637f2407f7537f6f67fa877fa9a7fdcb7fe7a7feb28035a805dc80b6b80cd880e918069a812a87ff308022b8035d808d48084e8040680700803ff80555803cf7fc50800af80267805ed80694806b980545804948064f806538046d7f5b17f39a7f5c27f58f7f5df7f70d7f5cc7f5377f2ec7eff67f1237ebcd7ecf87ff6b800867fe8d8003280045800d2801da8021a801387ffae7fe4f7fcea7fd077fd107fe967fe9a7fedc7fd187fcda7fddd7fe0d7ff867fff68005f801647fe9c7ff6b7ff657ff947fe9c7fdd27fd627fe497fe497fe257fccb7f4f080098801dc800067ffb57fe187fe487ff377ffd67ffca8006f7ff8d8001c7ff187ff337ffe4800107fef87ff257ffab7ff677ff8c80020800dd7edea,0x85d397f56480c7c8023d800e87ee247fc4e7fffc802227f9887f7107f6887f5707f9967f8407fba97fda88002b8007b7ffe5805b58075980f9980e9380cd97feca7fe437fdf98035e8024480a59808e4802b08071980340803de8059c7fce4801f1804ed8096780a0880924807aa807358096980952807037f3267ed9a7f2b67f2a97f2467f3097f1427f16b7f0aa7ea657ed5c7e4217e65080033800937ff2c7ff8e8001880153802a8802bd80247800fb7fede7fd5c7fd727fd667feca7fed07fee57fd417fd097fe2a7fe5e8000880055801128034c800ed800ff800c27fbcd7ff3d7fe567fdc97fe7f7fe087fdf37fce17f57c800ff802b0800d1800b97fe7a7fe7d7ff257ffea7ffdb800987ffcc8002c7ff327ff5c80027800737fedc7ff137ffc27ff777ffaa80075801767ea89,0x84f5b7f8587fc5d802667ff7e7fd737fe4a7fec97fec37face7f863802437f2797fc637fcff7fe4d80051803c08045f8015e802ba805e2808ca80dc77fe387fec37ffa77fd447ff408026e80130809d4808e48021c7fd99800847fe0780ad57fedb80005810b98105d80a6280aa380a2e80ba680a8a80a7b80aa27f3227ef647f1c07f2a97f0c67ebc37ee427ef3e7ee807ec277efbd7e086800ec7fbca800a3800637fed980048802a3802c5802c1801c1801bd7fed97ff107fd997fd0d7fc6f7fc887fe737fe707fddc7fe2e7fe5a7fff27ffac800fe803b68034980231801bc7f6947ffb17fed37fe9a7ff608002b800b9801d68025c7fa417ffcf7fec0801fe7ffa37ff607ff5c80011800038009e8003e800347ffa77ffda8007e800dd7ff207ff527fffc7ffc37fff7800c9801d17ed8d,0x842e97fcf880593803b5801227ff307fd467ff827fc747fa347f3897fa857fd507fe8d7feb87ffd780293804c98042d803ee7fade7feba800217fdfd7fc277ffe480542804e380adb805d3804668029d80ae280a5e80811801c88003f7fd798043580b1b80a8d8097680e8080f9e80a8880ae180b2280c4480c3780a2c7f3fd7efae7f1f17f32c7f0757f1ab7f5e07f3c57f0977f1c17f2707dc05806597fef67fd618052d800657fec77fc96801c08005f803d6801418022d8020380132800c1800507fff3800207ff877ff8e7ff50800d57ff547fad87ff31800907ffab807e9804cb801847ed647ffaa800138003b7f8707f9b5802017ffde803d6807f27ff007fac9801b3800f47ffbe8005780049800a78010a8004180078800b8801188019b7ff987ffc1800648004a8008180160802727f2ec,0x8385e7f2eb803708012680181800957f7957fa757fad47fac67f9cc7f5ef7fa017f9cc7faca7fdac7ff2e8021680484802cf803927fb747f4f57fb2c8006d8042380478805c9804c98076e804038051c8042a80d3680cb4808f67ffb47ff9f8048f809c3805918089380b39810808108f80bf080b8f80bd980e0980d3b80a6a7f2e17ee087ee347f0ed7ed117eebc7f1337ffb87f08d7ec507ed827ef13804167ff827fb668041b7ff158015a800df803437fe9780399801e3801ba800ba8018a8012c800d0800d5800157ff327ff2f7ffd180027800d27fe8a7ee428029e8014f806458058f804297f72d80137800e2800647feb97fed07f9a7800f0801898033e802ec803b580134800937ffa68004680038800a4800d98003e8004580083800f38016d7ff7b7ffa68004b80029800608013c8024b7f1a1,0x82b787ff48807ba808a5802d6802e4801937fe8e7fa5c7fa5d7f84a8036b7faa47fee97f8447fdb27fb647ff878001f8031880366803947fb537fb21800bc801ff80733803648062f8059e805df8016f804e68055080d728082e8014d8022f7fc5d8023f80ba78073e809f180ee8805198028680d0380c8080daf80f9480ed480bf87f4717f1187f31e7f3207f2297f3fd7f5667eefe7f7937e8f37eb437f67a7f3b38055b7f69a801c0801ad7fdb3800b08050c804177fdfd8045c8048b8034c80410803e08038780394801dd8008f800c98015f80135801e3801c9801738001d80294803dc805f8805fc803727fafa802ba8014b7ff147ff4c7fe1a80142801cb8034980471805ea802f1801f87fff480092800627ff8a801cf7ffd7800e380254801818021b7ffea8000c800aa800a5800df801c6802df7f68f,0x82d5080d988039a80e0a801fb80228801738099d7fe677fd6a7fb0d7fd8e7fe7a7fbc07f91f7fd427fb197fcb47ff7780015802c780aab809897fb457fd288006f8037c80ae6812818039180340804658012180439804a280c5a80a18806048011b80216804a7809f880410807b580a8380eee80cea80aca8098380b1d8097280c4e809c77f58f7ef387f1ed7f2957f0fc7f2777f3117f2567f89f7efc3804a37ec317fdc47e7377f6b67fe437ffd4802308035a80416803558041b8030e802617febc801c6801b18026180138801317ff427ff468003980018801508018d801bc8029a7f8e48024f80304803bc802188016f800e5800477fec77fede7fd1c7fad8801968034b8031d803fb80174800c47ffb28004f80040800a6800f2800408005f8009e80106801847ff8a7ffb4800578003a800718014e8025f7f249,0x8336c7ff778128f80bec8061a8042180270804f6802e97fe697f9887fcdc7f89f7fa787f7977fa137fe36801e7805d5805c58111e80ad880aca8043f7fcd17fc9180303806e880916802f8803bb80479803d07fe4c803ff8020c808d7806cb80380801ac8020e8041480902802798067380a9280ecf80e6b80bbf80b0e80b8080d0280c52809c37f6077f21a7f4a87f5b77f2757f4007f4d37f14b7f3d6804a7802e07d9997e2678017b8005a7fc577ff10802b9806538047b8040c8047a80317801f7800817fdfb8012c7fc578015c7fe9a7ff557ff758007f8000d801908052380260802c3800f37f56f802948040c8027a801d38012b8005c7fedf7fef97fef97f7b7801ab803618036f8046f801de801157ffc68005d8004e800a78011b8004380089800cb80125801aa7ffa27ffca8006c800558008d8016c8027f7f35c,0x8415f7f5757f5a87fcad80d2d7f3bb7f425804307ff137faef7f8ad7fba0803607f7a77faee7f21b7fcca7fb2e7fed9809648086780df580da28099f805007f58f7f89e7ffc1803158094180c728104080b9d819d0808538096680ea381aac81406805c07fd037fec8803f08115f8086f809e380d2c80ecb80c4380b8c80c8580aef80c2a80bd48088b7ebdc7e6eb7eb657eacf7ecf87ef2c7ed647ea197e275802038013e80469801de7ffed800147fe4c8000a800a7802368036b8033880301800d27ff257fe777fde27fd677fcee7fcff7fdbc7fdd27fd7f7fe417fec77ffb280062800c8801e57ff8580073801028015f7ff157fe637fe087fee67fe1b7fe227fe2e80032800e380293800648001e7fded7fe107ff0a7ffd87ffc8800967ff95800297fefa7ff217fffe800407febc7fef57ffa67ff537ff858004c8014b7e919,0x837f27e5f57fef27fbd880f277fc6f801b380269806d6803617f5fe7f3fb7fb6e7ffc27ff667fc23800167feac81272806e47fef4803d48017d802e8801c47ff077fc2a7fd79800be80208804268066a807eb806358076d8062780a9f808d880f1180a657ffce7f8878020b802f680a738046e804ec8024d806638050d8040a80459803b5803b680320802707f59b7f2567f4647f52b7f5257f5bd7f56e7f4197ff7b800ff8007e8020f800cb7ffa67ff9c7fecd7ffde80004800da801968016d8017f8002e7ff517fef07fe9b7fe5a7fe127fe247fea27fee47feb67ff1e7ff737fff58005b8009f8015680014800b2801408018b7ffd57ff797ff467ff9a7fe877fe7c7fed8800027fff5800d87ff7c7ff857fe5a7fe987ffbc800668005a800d5801418009a8008d800cb7ffbe7ff7f800278009d801f28018c802c9802177f5d87f2dc,0x837b080bfc807187f2877fec37fd71800477fee38012d7f7677f783800b3802eb806b0806248145f80ea97fa677fb2b7fbbb7fe507f9247fe037f64c7fa6c7f7a77fbb97f94a7f9497fb7c7f8447fb20805c0807a8804dd8016c800947fac37f74a7f5137fa7e7ffce807ea8010c802b87fe168025f801107f8f37f87f7f9db7f9677fa9f7f8c27f7f77f7447f8898066280950807b58063780b4080baa80d6480e117ff75800378001180430800887fff8802517fed17ff2d7e9da80203800a2800b58007e7ff06806127fdb97fda17fd777fd567fd697fe367fe877febb7fefe7ff387ffba8036a8007d800ed7ff3b7f4248003a800607ff0a7febb7fe307fe937fe7f7fe657febd7ff938002880031800fd7ff787fe4f7feaf7ffa480034800207fd3b7ffbe800137ff707ff837fff5800157ff567ff747ffcd7ffa17ffba8001d8009c7f438,0x8480d7fc22802dd7fcda7f82e7f94e7f2b7805457f4397ea947eeb07fb367f85f80dad80daa819937f80f7f9fa803727fb067fc2d7ff3d7fac57fb507f2617f4297f87a7fa357f9e27f7e97f9827f7f57f6c37f9b57f7877faa57f7917f95c807037f2317f2f27edf87ec0d802668054d7f8328007a802097fd6a7f8797f2097f3627f2c57f3787f3f77f1ae7f0117f629809218113c80d8b811318109c80a9a7fc007f9cd816bf8015780ccb803ee7fd198041b7ff2c8044b7f9b47fa3b7fe777ffff8026b8015c804937fdd17fe447fdab7fd407fd1d7fd157fdcd80091800bf8011780144802b3801cb807628109f811ab809477fec57d6d6801128008380014800017fe9c7febf7ff59800ad8014e80301802068026f8000b7ffaf7ff6f8001f800108009f80066800377ffd0800058009c801037ff377ff67800107ffdd80012800e7801f17ee9b],[0x83eec7f4127f8647f9977f19e7eb487e8d280b7a7f1fc7edd27e9b07e3ba7ebad8048980ac37ee617f8957fbfe7f6957f7857fd0e7fb5e8029d7fa397f9af7f6c47f4817f46d7fbf17fcc07fb1f7fc0c7f8317fa757fa7a7f8447fbb37fb0c7f6157fa4c7f8eb7f4ad7f3697f0848044a7faa5801987fad97fe7e7fe6a7f5bd7f69c801ef7f3b47f3937f40b7f3527f21a7f42680a148116e80b2280b548158d816a3810817fd587fec17fbe07fde38088b800a3801da803187fbc87fd507fe10800ee80232806a880315802297ff647ff1b7febd7fe547fe207fe207fe747ff767ff788001e8003280194802bb808e780a268030d801e87effb7fe2e800c38001b7ffbd7ffd07fe8c7fea17fec9800598016e802b98016e801f17ff2a7ffc57ff337ffd37ffbe800387ff707ffff7ff467ff907fc95800f17ff2c7ff5d800077ffd180005800d9801e17ee1a,0x836927fc5a7fae87fd3f802eb7fb467f9fb824947e5377e5d17ea5b7e6547e6a77ed357f6d87f8357fb74801607fd627fa307fd947fd2f8004f7fb697f87f7f7e37f60f7f6a67ff497fd017feda7fe1a7fd807fb1e7fc327ff897fe097ff927fa517fd027f9677f7597f2547f7527ff137fcf87ff187fb2b7fb6e7f9c67fcbe7f7377f6627f69c7f3bc7f4107f5907f4527f33b7f5df80cf8811348107f80ee08119481086800428004380126801b0802318033c8020d8005380095800787ffae7fbf48032b803e8803088043180314801da800a0800bf8007b80013800277ffbe7feeb7ff147ff987fff98005b800ce800ee80289802618022c803737ff4b80148800c07ffda7ff747fe657fe4d7ff908007780141800e180310801d57ffe17ffbd7fc6c800788005e7fdd48009d8003a8000880041800c6801357ff587ff858002c80001800388010f8021c7f00d,0x82d108096d8003880498809a37fa84807c38073c7ec287f8237f02a7e7497ebd88051b8040d7f8b97fca07fcc7807557fc217f6f37fb7c7fd638019e7fed47fb407feb97f6487f8147f6647fb677fea67fdc87fd397fac77fc1d7fc8b7faad7fded7fbb17fae77faa57f9da7f5c77f8357fa1e7fd557fb487fd557fb627fae57fce07f6dd7f5b57f5eb7f2437f38d7f4d87f3ad7f2ce7f4f780c20810db810aa80e70811fb8124c80223800397fdb2800e380022803ce802688014b8003d7fa667fff58015e803058041f803718043f802a280186800a58006f800127ff9d7ffab7ff697fef07fec67ff7c7ffc080081800ec8014980221800b4801b8802838031d800dc800497ffdc7ffe37fe8f7feae7ff3a800a080143802f6801da802307ffd17ff837ff6480018800098009e80050800357ffb97ffed8008b800ee7ff2a7ff5b800057ffcf80003800d7801df7ee06,0x831187fdc680cc88078180669800a27fabb7fb5e7f9507e6ce7dba97e8ff80847807ed801597ff377f9817fe447fdaa801567ff017f8b47fa1a7fc2b7fff67f82a7f4047f2e07f2977f2967f4067fa9a7faf97fa377f9bf7f9457f8f07fa197fa807fe4e7fcfa7fc977fe3e8002f7f4497f7647fb407fd0e7fc4e7fcb77fb1a7fa117fbf37f60d7f4ce7f5197f1a07f2d37f4037f2da7f2227f4ba80c40810748103480ed78113280c5a8019e8007c7fec28021780102803aa8024f7fbdb7ffe37fec57fff98013e802e1803ff8036780407802518011b800437fffc7ff997ff247ff337ff1e7febe7fe8c7ff457ff948005d800d380133802168007f8017f80240802ce8008c7fff37ff8a7ffb67fe7a7fe967ff0b8008c80132802e480198801d37ff7c7ff427ff548000c7fffd8009d8002f800337ff987ffc980073800cf7ff177ff497fff47ffb97ffed800be801c57ed28,0x82e968022d817b6801c78036f80632804357f15d7e9ca7ea007f9317f12c806a17fc568004e7fc467fb367fb8d7fb987fc997fff17fd217f75a7fa397fc4c7fdae7f6267f1ff7f2247f1d27f3887f59b7fb4e7f84e7f8857f9537f98d7f9ef7fbd67fbdc7fed97fd797fe697fe1c7fb367f71e7f9c77fc4f7fbc17fcb47fc377fba37f9c37fbbc7f5ba7f4327f4637f1227f2797f3597f24c7f1ae7f47880b3980ebf80ec080e0c80f847fec9801147fff07fd59800c98008a802d2808db805767fffa7fe8d80001800f880292803ba803518038e801a0800337ff6e7ff037fe957fe1e7fe2e7fe7a7fe517fe107fecd7ff358000e8009f80101801ff8000b80103801ad802247ffdf7ff3a7fed77ff567fe4e7fe607fea4800638010d802bf8010a801097fec37feb57ff327fff47ffe58009a7ffe88002e7ff4e7ff7b8003c8008d7feed7ff237ffd07ff8a7ffbd8008a8018d7eb47,0x824897fc5f802227f8bd807d980779800a67fff27ffcf7f9357f0948064f7fc898070980434802157fe757fefa7fde47fdde7fe1f800307fea67fc027fd8d7fe1f7ff7c7fc967fa947fa2c7f9cf7fa857fb8b7fe0c7fccc7fc767fcbc7fc9f7fcf47fdaf7fd587ff347fe717fe807feba7fcc47fa8c7fbf87fdc17fe567fdde7fe0b7fd017fcca7fde37fa227fa507fa9a7f88c7f91f7f9b37f94e7f9017fa6c80614807ee807cd80769808037ff8780101800587ff3d8009280044801af80100800737ffe67ff5a7fff08008d80154801fd801b68020e801348009b80036800177ffe47ffb17ffb47ffa07ff6e7ff547ffb17ffd78003f80076800b18012d8002b800d380120801658004c800057ffe67fff37ff227ff287ff4d800238007980234800c8800e47ffb97ff9d7ffa9800067fffe8004e80016800197ffca7ffe380038800667ff8a7ffa47fff97ffdb7fff58005e800e17f688,0x82e0f7ff417fdd27ff0b7f62a7f6007fd657ff14801557fec97f7f58039e7fede800cd7f7467fd8c7ffcb8025c7ffff800428004a805ba7ff6a8040e805e880a778075d804e58012e8052680100803d8801797ff947fecc800e680192800988037c800fe7fda2800707ffdb80119803d88027e806408064d804c3807f4801a58032d8041280561805a3803a38064e80776807a4808c7807958062d806ed806eb805357fb677f8207f7fa7fbb37f5267fcdb801b08015080230802678013e7fd197ff587fea27ffd18031d802fa8076b8026a7ff357f5e37f8b17fe057ff627ff9c7ff547ff4c7ff547ff4a7ff9c7ffed7ffea7ffc87ffea7ffcc7fffb7f5847f67f7ffd2800037ffe87ffd17ffe27ffed80089800587ffc07ffa87ff617ff967ffb6800977ff8d7ff877ffea7ffd07ffd77ffca7fd817ffe07ff43800037ff567ff317ff737fdff800068000880013800158001a8002c800427ffa0,0x834f17ef627fc657ff6c7f6c67efa27edca7ef317f4197f7ec7f74e801b47f7817fd0d7fc1d7fe08800b68005080289802527ff06804838094c8012880ba680eed8131780bd680444809fd80e9780965808508047e802ec8008780711806e8806b6807bc805da8015e800467ff797f97c8058a805ed80b1c80cf08055280680806f6804c28089b80af780c8d808e480d8c80f5280e39811b68104880dc980e3780f0e80b1c7f4847f0577f20c7f3c87fb627fe01800b88004e80164800ca7ffcf7fcaf7f54e7fe158020a8058a807458075d802fe7f7917ff107fdd67f4f77ff5c7ffc57ff787ff8e7ffa87ff977ffeb800528007080036800357fff97ffc97fdec7ef367ffd37ff817ff8d7ff7f800518002b8005c8003c800b2800a37ffd57ff787ff567ff467ff377fe71800807ffec7ffbb7ff417ff577ff727fddd7fff57fe457fdcc7fe4c7fa3c80055800498002d800438003d8002480002804fe,0x828897f58a7f8147f6118121a81cb8805af80ae37f8a67fa967f9f1801de8062980cc57ffed801847fbfc7fe5d7fc7b7fc327fcf97fbde7f7f47fcae8007f7fe757fb347fb047fdb07fce47fa177f7527f7b57f86a7faf27fc847ff607f4797f4fc7f6b97f76d7fa467fce87f9bb7fec87fc067fe147fd837f7887f9a67fc8f7fc2a7f88b7fa847f9c37f8d47f5357f9af7f3ce7f3817f40a7ef8d7f0f27f21f7f1d07f19f7f48e8099d80cd780da27fb4d7fdaa7feea8011b7ff2a7faaa800867fffc8074880c06800ca7ffd07feb87fff380121802af803dd8034a803e98023080101800217ffe87ff897ff18800b17fefc7fea77fe737ff2c7ff818004d800c88012880212800678016580221802ab800687ffcd7ff657ffa27fe717fe8b7fef5800848012a802dd8017b801a97ff567ff257ff4d800077fff88009c80021800327ff887ffb980067800c27ff0e7ff417ffed7ffaf7ffe3800b3801b97ecc4,0x82b7a80c677eba77f87f8100e8170a7fb7e8018c7fe227f77d7f2af7f88b7ff947f86e800908019a80422816c480266800727fd747fe987fb877f9bf7fc84801397fdda7fd1b7fc8c7feb37fe037fc267fac17f96d7f9427fbd47fcb77ff037f3517f2b27f5527f63b7f8797fa967f9fa7fe6c7fad97fcff7fe4c7f8e77f6ae7fa2e7fb647f9237fafd7f88e7f7d17f4ac7f8ca7f32e7f2df7f3b57ef137f04c7f1b27f1607f12a7f48c80b1680e4580de57fcfe7fe207feb38011f8004d7ff4c8012c801038033c801e3801157ffe97ff127ffc68011b802d3803f28035680411802948013f8006b8002b7ffcb7ff587ff677ff3e7fee87febe7ff727ffba80083800e3801558028680134801e68028680170800be800287ffbd7ffd27fe877fea57ff27800988013c802ef801c18020c7ffb07ff6a7ff5e80013800048009e80043800347ffac7ffdf80082800e27ff237ff547ffff7ffc67fffb800cd801d57edb0,0x8231d806e8812067e2907f2a47f8f87fe0b8010f7fd477fb4d7ff227f9a87f76e8090480be38027d801108018a802d78011c7ff1d7fd517fe147fe537feca80096802b0800a67ff5d7fe017fef6800547fe3c7fc777fb797fc347fe557ff92800d67f61a7f56b7f75a7f7a87f9e57fb4a7fa317fe937faba7fc877fd987f86d7f68d7fa2e7fb1a7f7a47f9487f7cf7f6bd7f3ae7f8cb7f3957f4117f4f87ef507f0937f2687f25a7f22b7f54780b3780e9f8090c7fcfc7fe5f7ff30801d17ffe97fdd38009f8002a802b380228801907ffc07ff1b7ffec801a98035b8046980388804c380361802818018a8017c8012b800b7800c58001a7ff667ff4c7fffe80027800d7801248017e8023a801318023e80322803d480198801118009d8004b7febe7fee87ffa8800cd8016a8031e802748030b800998001c7ff898003280023800a28009d8003a8000880041800c6801367ff587ff858002c80001800388010f8021c7f00d,0x828de80a38814087fbbf7e69c809247faf67fc0a7fa237fd317fa927fe3f7fae27f9dd8040080706802478004b7ff987feec7ff317fe6e7fce97fddd7fdda7fd82800908026a8006a8007c7fe0c7ff677fff37fec47fd6a7fc6a7fdda7ffda80068801307f36c7f2ce7f5677f6497f9087faea7fa367fe8e7fade7fd3d7fe067f8aa7f7707fb3b7fb687f6a77f8907f74e7f6067f2a57f7c67f2aa7f3287f4367ee8e7efc17f1877f1a97f1a37f4d780abb80e137fdb37fcfa7fe5c7ff2e801cb7ffee7fdde800a880031802bf80226801857ffc27ff157ffed801a2803538046280386804b7803508026a8017680164801128009e800ac8000a7ff5b7ff407fff28001d800cf8011f8017980237801268023280314803c480187800ff8008c800417feba7fee37ff9e800c9801678031b80266802f7800878000e7ff868003080021800a1800968003a800018003a800c18012f7ff547ff82800297fffd800338010a802167efde],[0x82bc08249e801627f8417f41c80fc0806477fdc17fc917fb8e7fec37fd5f8006b7fd8c7fd998001980209800217fe6a7fcf87fc807fd397fcfb7fc447fd9e7fe967ff58802848031f801bc802997ff028003880123800677ff2b7ff468006f8020780264802527f33b7f2a67f5547f6577f9557faf87fa147fe737faad7fcfd7fe487f8c77f8487fbf67fb147f5457f7cc7f64a7f50c7f1297f7517f2447f34c7f47e7ee2a7ef697f1637f1cc7f1f17f4a580aff803927fdff7fd0c7fe717ff42801f77ffc67fd88800627fffb8026980235801d77ffb27ff3e7ffe7801d58038c80494803968050f803d1803138021080219801cf8015c80169800817ffaa7ff9b8004a8006280109801468019d802488017a8028c8037f8043f80205801868010e800877feda7ff0a7ffe8800e78018280336802ce8038a8010d800757ff9f8004180033800a4800ca8003d8003680072800e88015f7ff737ff9e800438001f80056801318023f7f13c,0x839af804147f0d97fdb67fcd77fa1180c85804ef800ee7ff2e7fe3f8017b801df803b0800a4800657fe757ff687fe697fc967fab87fc357fc5e7fba07fbb97fd0c8001a802b8804b38036d8043a804c4800e3800998038c801ef7ffde8014b8023f8038e80431803647f57d7f4e57f71b7f7b47fa797fb8d7fa4d7feb77faf07fc997fedc7f8a37f86a7fb8e7f9e87f3d77f6927f5c17f4d67f0e27f7ec7f2cc7f41e7f5397ee3f7efbb7f1ed7f2757f2ab7f4e780b567fd0b7fe827fd287febf7ff9d8025e7ffac7fcf48000a7ffdc802698029a8028e7ffb77ffae8004780249803fa804d8803ae8058180475803e3802bb802f4802ba8024580255801148002580038800f0800eb80190801c080215802b0801c3802e68044780556802bb802397ffc4800e77ff197ff598005d8011d801a8803b28038f8048d8020b7ff4e7ffc78005e80050800a88011e800438008c800ce80128801ad7ffa47ffcc8006e800578008f8016f802827f372,0x8341a7e9bc7f11c7f689801e9800437ffda807988037d803217fde47fe43803e88044380481802f3801c27f9317fc73800de7fc947f7c57fda37fdea7fa9f7fa597fac67fea8803a0804278013880810806d18048e800dc80793802fa7fc7d80128800ea801e78026f8027a7f7fa7f7787f9857f9557fc037fc837fafc7ff8f7fcd07fbf58018f7f9a87f9737fa187f5a67f2e17f4457f7117f7597f3cf7fb237f4417f4317f4767ee127f0917f2507f2497f21f7f4ae7fd797fd4a7ff3b7fd247ffde801118035f800197fbc87fff88003e804bf803ed80429800407fef4801bb803a78056780501803eb8059480495803bd8022d802b580298802158023b800fd800868010d80206801e3802d18036c803b480491801308023a8055a8071b803dc8019c7f96a7fce67ff8f7fff4800bf8016c801b6805a6804c4805f0803b27f5b07fff08007b8006c800ab8017280048800e28012a80167801fb7ffd67fff9800998008e800c8801ad802c47f5a9]]
def gramWord (i : ℕ) : ℕ := ((gramWordChunks.getD (i/12) []).getD (i%12) 0)
def digitTotalWords : List ℕ := [0x65ec4cc4ed7bc3b343d6157eaa7ad2c34a192f644b6c59c97e90af1fa5c618b2b1d5a4e6a2a5,0x5a8a8b369d68b7297314dc2e920d90fc9a2ef144cba85c30fa3e9da663c71290e5972d033cc3,0x3aa7c7d1f4f87827929548bcb3ad16719ae78760b42c48197b14af7c65a394b2b5d64b22be14,0x58c60a78f94283a51ef53e549bbe54fc62630b48864918fd2d56211ab3fc44808ecfc159e552,0x58d9c949fd026725c5f4ff1a9e8d54cc8aa4045614cbbf656919ae8da5c296b971d6c71ada42,0x3b32a953d156aca810546334af3ad806a2d2bc598b89822916ef9bdc43822c79330e5a09fa22,0x4c8869a0658a1bafe6f5d8c2c437d8a1db1f2b28834000001ebd87088231f45a104d9829e3cd,0x6250ebccad779d2824a52f228f05109e2251c24ece4907a10170243e74d5d0a6ce9326b2b083,0x32bd66a0d8c42d191d667d68b40fd0b5e9657730ee276254ca679343f37c5e9075157daace43,0x7b54cf9fc1ce2d]
def digitTotal (i : ℕ) : ℤ := 1 * (((digitTotalWords.getD (i/16) 0 >>> (19*(i%16))) &&& 524287 : ℕ) : ℤ) + 76912934
def gramValue (i k : ℕ) : ℤ := readGram 20 524288 (gramWord i) i k
def gramDigit (i k : ℕ) : ℕ := (gramValue i k+524288).toNat
def forwardWords : List (List ℕ) := eval% natTable 147 (fun i => natWord 147 56 (gramDigit i))
def backwardWords : List (List ℕ) := eval% natTable 147 (fun i => natWord 147 56 (fun k => gramDigit i (146-k)))
def gram : GramPacking where
  n := 147
  width := 56
  offset := 524288
  scale := 8192
  value := gramValue
  forward := tableAt forwardWords
  backward := tableAt backwardWords
  total := fun i => (digitTotal i).toNat
def inputs : Tabs where
  n := 146
  loN := 9
  hiN := 10
  Zn := 360364800
  ppn := 0
  rrn := 0
  ssn := 80329310208
  vlo := R4.low
  vhi := R4.high
  vlen := R4.lengthOf
  vsg := R4.signOf
  vAl := R4.alpha
  vBt := R4.beta
  vYv := yv
  vOv := ov
  vA1 := a1
  vA2 := a2
  vA3 := a3
  vA4 := a4
  YYT := yy
  OOT := oo
  YOT := yo
  thT := theta
  NT := fun _ _ => 0
  crows := gram.scaledRows
  czr := [5256256054886400,0,4661286273024000,0,3979590657638400,0,2169006509260800,3923286530457600,0,1319413953331200,0,3762570028646400,0,3037005348864000,0,0,0,3958241388134400,0,5277655184179200,0,2794420017561600,0,4732518137856000,0,5277655813324800,0,329853488332800,0,5277655813324800,0,4961235212697600,0,0,0,0,0,434738351308800,0,4780307408486400,0,5277655813324800,0,0,629145600,0,0,0,0,0,0,0,0,0,0,3138850180300800,0,5277655813324800,0,5277655813324800,0,724446688051200,0,794677582233600,0,2755992433459200,0,5277655813324800,0,5277655813324800,0,5277655813324800,0,0,5277655813324800,0,5277655813324800,0,5277655813324800,0,2755992433459200,0,794677582233600,0,724446688051200,0,5277655813324800,0,5277655813324800,0,3138850180300800,0,0,0,0,0,0,0,0,0,0,629145600,0,0,5277655813324800,0,4780307408486400,0,434738351308800,0,0,0,0,0,4961235212697600,0,5277655813324800,0,329853488332800,0,5277655813324800,0,4732518137856000,0,2794420017561600,0,5277655184179200,0,3958241388134400,0,0,0,3037005348864000,0,3762570028646400,0,1319413953331200,0,3923286530457600,2169006509260800,0,3979590657638400,0,4661286273024000,0,5256256054886400]

def triWidth : ℕ := 65
def basisRow : ℕ := 0x200000000000000010000000000000000800000000000000040000000000000002000000000000000100000000000000008000000000000000400000000000000020000000000000001000000000000000080000000000000004000000000000000200000000000000010000000000000000800000000000000040000000000000002000000000000000100000000000000008000000000000000400000000000000020000000000000001000000000000000080000000000000004000000000000000200000000000000010000000000000000800000000000000040000000000000002000000000000000100000000000000008000000000000000400000000000000020000000000000001000000000000000080000000000000004000000000000000200000000000000010000000000000000800000000000000040000000000000002000000000000000100000000000000008000000000000000400000000000000020000000000000001000000000000000080000000000000004000000000000000200000000000000010000000000000000800000000000000040000000000000002000000000000000100000000000000008000000000000000400000000000000020000000000000001000000000000000080000000000000004000000000000000200000000000000010000000000000000800000000000000040000000000000002000000000000000100000000000000008000000000000000400000000000000020000000000000001000000000000000080000000000000004000000000000000200000000000000010000000000000000800000000000000040000000000000002000000000000000100000000000000008000000000000000400000000000000020000000000000001000000000000000080000000000000004000000000000000200000000000000010000000000000000800000000000000040000000000000002000000000000000100000000000000008000000000000000400000000000000020000000000000001000000000000000080000000000000004000000000000000200000000000000010000000000000000800000000000000040000000000000002000000000000000100000000000000008000000000000000400000000000000020000000000000001000000000000000080000000000000004000000000000000200000000000000010000000000000000800000000000000040000000000000002000000000000000100000000000000008000000000000000400000000000000020000000000000001000000000000000080000000000000004000000000000000200000000000000010000000000000000800000000000000040000000000000002000000000000000100000000000000008000000000000000400000000000000020000000000000001000000000000000080000000000000004000000000000000200000000000000010000000000000000800000000000000040000000000000002000000000000000100000000000000008000000000000000400000000000000020000000000000001000000000000000080000000000000004000000000000000200000000000000010000000000000000
def triLinear : ℕ := 0x2000000000000000100000000000000008000000000000000400000000000000020000000000000000fffca4d2c80000007fede072380000003fede072380000001ff85d5f870000000ffd70e0b8800000080080e06200000004002af576000000020064af4c900000010016d266b00000007ffea854500000003fe44fcaf20000001ffb2231a20000001000c15093000000080137739780000003fdef11c3200000020012cb63a0000000ffbc34a1c80000008014230f500000003feb8705c40000001ffde703bd0000000ffdc6cba480000007ff33f20f80000004000000000000000200345b27d0000000ffe073bd580000007ff08fc9980000003fe92d995000000020049d5e2d00000010037b655080000008022e76fe000000040033037c2000000200721c017000000100000000000000008000000000000000400000000000000020000000000000000ffefe3f3c00000007ff79c0ef40000003ffdd189020000001fffaa15140000000fffca4d2c800000080121f8dc8000000400533b94a0000002005ca14670000001002a49a028000000800508c3d40000003ff9f57b680000002009fc0ced00000010078d25be00000008050365254000000402ed1839a000000200e43802e0000001008796bc70000000800abd5d80000000400b13486c0000001ffab6cbfb0000000ff872da4200000007fff542a280000004000000000000000200d573a250000000fffdfc7e780000007fd8bba2240000003ffacc46b60000001fff542a28000000100076230480000007fe78002b40000003ffccfc83e0000001ffefe3f3c0000000fff7f1f9e00000007ff99f907c0000003ff3c0015a0000002000ec46090000000fffaa151400000007ff5988d6c0000003fec5dd1120000001fffbf8fcf0000001006ab9d12800000080000000000000003fffaa15140000001ff0e5b4840000000ffd5b65fd800000080162690d800000040055eaec00000002010f2d78e000000100721c0170000000805da3073400000040281b292a000000200f1a4b7c0000001004fe067680000007ff3eaf6d000000040028461ea00000020054934050000001002e50a338000000800a67729400000040090fc6e40000001fff949a590000000fffd50a8a00000007ffba312040000003ffbce077a0000001ffdfc7e7800000010000000000000000800000000000000040000000000000002000000000000000100390e00b80000008006606f84000000401173b7f00000002006f6caa100000010024eaf1680000007fd25b32a00000003ff847e4cc0000001ffc0e77ab0000001001a2d93e800000080000000000000003ff99f907c0000001ffb8d97490000000ffef381de80000007fd70e0b88000000400a1187a80000001ff78694390000001000965b1d00000007fbde238640000004009bb9cbc000000200182a1260000000ffd9118d100000007fc89f95e40000003fff542a280000002002da4cd60000001003257a64800000080055eaec000000040040703100000001ffae1c1710000000ffc2eafc380000007fdbc0e4700000003ff6f0391c0000001fff949a590000001000000000000000080000000000000004000000000000000200000000000000010000000000000000
def triangles : List (List TriT) := [[⟨20,80,84,-1,-1,1,850207231180800⟩,⟨61,65,125,-1,-1,1,850207231180800⟩,⟨40,89,92,1,-1,-1,425103615590400⟩,⟨53,56,105,-1,1,-1,425103615590400⟩,⟨38,89,92,1,-1,-1,2881257839001600⟩,⟨53,56,107,-1,1,-1,2881257839001600⟩,⟨32,53,111,-1,-1,1,188934940262400⟩,⟨34,92,113,-1,-1,1,188934940262400⟩,⟨28,31,34,-1,-1,1,944674701312000⟩,⟨111,114,117,-1,-1,1,944674701312000⟩,⟨37,89,92,1,-1,-1,425103615590400⟩,⟨53,56,108,-1,1,-1,425103615590400⟩,⟨39,89,92,1,-1,-1,377869880524800⟩,⟨53,56,106,-1,1,-1,377869880524800⟩,⟨38,54,57,1,-1,-1,377869880524800⟩,⟨88,91,107,-1,1,-1,377869880524800⟩,⟨16,31,34,1,-1,-1,94467470131200⟩,⟨111,114,129,-1,1,-1,94467470131200⟩,⟨6,84,101,-1,1,-1,755739761049600⟩,⟨44,61,139,1,-1,-1,755739761049600⟩,⟨31,58,67,-1,-1,1,2172751813017600⟩,⟨78,87,114,-1,-1,1,2172751813017600⟩,⟨13,114,129,1,1,1,566804820787200⟩,⟨16,31,132,1,1,1,566804820787200⟩,⟨5,18,22,1,-1,-1,2408920488345600⟩,⟨123,127,140,-1,1,-1,2408920488345600⟩,⟨20,81,84,-1,-1,1,2834024103936000⟩,⟨61,64,125,-1,-1,1,2834024103936000⟩,⟨46,89,92,-1,-1,1,1464245787033600⟩,⟨53,56,99,-1,-1,1,1464245787033600⟩],[⟨31,59,63,-1,-1,1,1039142171443200⟩,⟨82,86,114,-1,-1,1,1039142171443200⟩,⟨46,53,92,-1,-1,1,708506025984000⟩,⟨53,92,99,-1,-1,1,708506025984000⟩,⟨7,19,53,-1,-1,1,141701205196800⟩,⟨92,126,138,-1,-1,1,141701205196800⟩,⟨14,80,113,1,1,1,236168675328000⟩,⟨32,65,131,1,1,1,236168675328000⟩,⟨32,35,65,-1,-1,1,1700414462361600⟩,⟨80,110,113,-1,-1,1,1700414462361600⟩,⟨6,10,85,1,-1,-1,1417012051968000⟩,⟨60,135,139,-1,1,-1,1417012051968000⟩,⟨19,42,85,1,1,1,1180843376640000⟩,⟨60,103,126,1,1,1,1180843376640000⟩,⟨19,46,85,-1,-1,1,94467470131200⟩,⟨60,99,126,-1,-1,1,94467470131200⟩,⟨12,18,37,-1,1,-1,755739761049600⟩,⟨108,127,133,1,-1,-1,755739761049600⟩,⟨29,32,60,-1,-1,1,1417012051968000⟩,⟨85,113,116,-1,-1,1,1417012051968000⟩,⟨13,20,67,-1,1,-1,141701205196800⟩,⟨78,125,132,1,-1,-1,141701205196800⟩,⟨55,58,88,-1,1,-1,850207231180800⟩,⟨57,87,90,1,-1,-1,850207231180800⟩,⟨19,41,85,1,1,1,1133609641574400⟩,⟨60,104,126,1,1,1,1133609641574400⟩,⟨7,11,54,-1,-1,1,47233735065600⟩,⟨91,134,138,-1,-1,1,47233735065600⟩,⟨12,19,39,-1,1,-1,425103615590400⟩,⟨106,126,133,1,-1,-1,425103615590400⟩],[⟨19,85,101,1,1,1,519571085721600⟩,⟨44,60,126,1,1,1,519571085721600⟩,⟨14,79,113,1,1,1,802973496115200⟩,⟨32,66,131,1,1,1,802973496115200⟩,⟨12,18,38,-1,1,-1,2692322898739200⟩,⟨107,127,133,1,-1,-1,2692322898739200⟩,⟨15,18,22,1,-1,-1,661272290918400⟩,⟨123,127,130,-1,1,-1,661272290918400⟩,⟨33,55,112,-1,-1,1,330636145459200⟩,⟨33,90,112,-1,-1,1,330636145459200⟩,⟨42,54,92,1,-1,-1,236168675328000⟩,⟨53,91,103,-1,1,-1,236168675328000⟩,⟨19,45,85,-1,-1,1,1605946992230400⟩,⟨60,100,126,-1,-1,1,1605946992230400⟩,⟨20,96,122,1,1,1,47233735065600⟩,⟨23,49,125,1,1,1,47233735065600⟩,⟨15,79,114,1,1,1,3967633745510400⟩,⟨31,66,130,1,1,1,3967633745510400⟩,⟨39,54,57,1,-1,-1,566804820787200⟩,⟨88,91,106,-1,1,-1,566804820787200⟩,⟨37,53,56,1,-1,-1,236168675328000⟩,⟨89,92,108,-1,1,-1,236168675328000⟩,⟨32,58,66,-1,-1,1,2928491574067200⟩,⟨79,87,113,-1,-1,1,2928491574067200⟩,⟨24,78,114,1,1,1,1653180727296000⟩,⟨31,67,121,1,1,1,1653180727296000⟩,⟨33,54,87,-1,-1,1,94467470131200⟩,⟨58,91,112,-1,-1,1,94467470131200⟩,⟨8,11,54,-1,-1,1,708506025984000⟩,⟨91,134,137,-1,-1,1,708506025984000⟩],[⟨15,80,114,1,1,1,2219985548083200⟩,⟨31,65,130,1,1,1,2219985548083200⟩,⟨19,47,85,-1,-1,1,1417012051968000⟩,⟨60,98,126,-1,-1,1,1417012051968000⟩,⟨21,31,90,-1,-1,1,802973496115200⟩,⟨55,114,124,-1,-1,1,802973496115200⟩,⟨19,78,84,-1,-1,1,283402410393600⟩,⟨61,67,126,-1,-1,1,283402410393600⟩,⟨21,65,87,1,1,1,1794881932492800⟩,⟨58,80,124,1,1,1,1794881932492800⟩,⟨32,36,64,-1,-1,1,2881257839001600⟩,⟨81,109,113,-1,-1,1,2881257839001600⟩,⟨14,75,113,1,1,1,1653180727296000⟩,⟨32,70,131,1,1,1,1653180727296000⟩,⟨7,85,92,1,1,1,1700414462361600⟩,⟨53,60,138,1,1,1,1700414462361600⟩,⟨13,57,90,-1,-1,1,755739761049600⟩,⟨55,88,132,-1,-1,1,755739761049600⟩,⟨12,19,40,-1,1,-1,2031050607820800⟩,⟨105,126,133,1,-1,-1,2031050607820800⟩,⟨22,31,89,-1,-1,1,141701205196800⟩,⟨56,114,123,-1,-1,1,141701205196800⟩,⟨34,55,88,-1,-1,1,377869880524800⟩,⟨57,90,111,-1,-1,1,377869880524800⟩,⟨5,75,114,1,1,1,236168675328000⟩,⟨31,70,140,1,1,1,236168675328000⟩,⟨21,66,87,1,1,1,708506025984000⟩,⟨58,79,124,1,1,1,708506025984000⟩,⟨6,49,85,1,-1,-1,566804820787200⟩,⟨60,96,139,-1,1,-1,566804820787200⟩],[⟨15,75,114,1,1,1,566804820787200⟩,⟨31,70,130,1,1,1,566804820787200⟩,⟨21,84,116,1,1,1,2219985548083200⟩,⟨29,61,124,1,1,1,2219985548083200⟩,⟨21,81,85,-1,-1,1,3164660249395200⟩,⟨60,64,124,-1,-1,1,3164660249395200⟩,⟨6,7,54,1,1,1,425103615590400⟩,⟨91,138,139,1,1,1,425103615590400⟩,⟨20,86,101,1,1,1,188934940262400⟩,⟨44,59,125,1,1,1,188934940262400⟩,⟨19,44,84,-1,-1,1,897440966246400⟩,⟨61,101,126,-1,-1,1,897440966246400⟩,⟨37,56,89,-1,-1,1,1228077111705600⟩,⟨56,89,108,-1,-1,1,1228077111705600⟩,⟨39,54,56,1,-1,-1,944674701312000⟩,⟨89,91,106,-1,1,-1,944674701312000⟩,⟨17,21,24,-1,-1,1,94467470131200⟩,⟨121,124,128,-1,-1,1,94467470131200⟩,⟨31,50,85,-1,-1,1,1653180727296000⟩,⟨60,95,114,-1,-1,1,1653180727296000⟩,⟨33,54,111,-1,-1,1,1653180727296000⟩,⟨34,91,112,-1,-1,1,1653180727296000⟩,⟨21,71,87,1,1,1,94467470131200⟩,⟨58,74,124,1,1,1,94467470131200⟩,⟨9,17,21,-1,-1,1,850207231180800⟩,⟨124,128,136,-1,-1,1,850207231180800⟩,⟨40,54,56,1,-1,-1,2550621693542400⟩,⟨89,91,105,-1,1,-1,2550621693542400⟩,⟨20,66,87,1,1,1,472337350656000⟩,⟨58,79,125,1,1,1,472337350656000⟩],[⟨14,80,114,1,1,1,708506025984000⟩,⟨31,65,131,1,1,1,708506025984000⟩,⟨21,79,110,-1,-1,1,425103615590400⟩,⟨35,66,124,-1,-1,1,425103615590400⟩,⟨35,56,88,-1,-1,1,1464245787033600⟩,⟨57,89,110,-1,-1,1,1464245787033600⟩,⟨46,54,92,-1,-1,1,1558713257164800⟩,⟨53,91,99,-1,-1,1,1558713257164800⟩,⟨32,35,66,-1,-1,1,1369778316902400⟩,⟨79,110,113,-1,-1,1,1369778316902400⟩,⟨10,20,23,-1,-1,1,1228077111705600⟩,⟨122,125,135,-1,-1,1,1228077111705600⟩,⟨45,53,91,-1,-1,1,94467470131200⟩,⟨54,92,100,-1,-1,1,94467470131200⟩,⟨18,22,24,-1,-1,1,1417012051968000⟩,⟨121,123,127,-1,-1,1,1417012051968000⟩,⟨20,33,94,-1,-1,1,94467470131200⟩,⟨51,112,125,-1,-1,1,94467470131200⟩,⟨25,30,33,1,-1,-1,708506025984000⟩,⟨112,115,120,-1,1,-1,708506025984000⟩,⟨40,54,57,1,-1,-1,566804820787200⟩,⟨88,91,105,-1,1,-1,566804820787200⟩,⟨23,115,120,1,1,1,1747648197427200⟩,⟨25,30,122,1,1,1,1747648197427200⟩,⟨36,89,92,1,-1,-1,2078284342886400⟩,⟨53,56,109,-1,1,-1,2078284342886400⟩,⟨31,34,63,-1,-1,1,2597855428608000⟩,⟨82,111,114,-1,-1,1,2597855428608000⟩,⟨14,18,22,1,-1,-1,566804820787200⟩,⟨123,127,131,-1,1,-1,566804820787200⟩],[⟨17,31,57,-1,-1,1,661272290918400⟩,⟨88,114,128,-1,-1,1,661272290918400⟩,⟨13,78,114,1,1,1,94467470131200⟩,⟨31,67,132,1,1,1,94467470131200⟩,⟨21,80,85,-1,-1,1,283402410393600⟩,⟨60,65,124,-1,-1,1,283402410393600⟩,⟨50,76,90,-1,1,-1,1700414462361600⟩,⟨55,69,95,1,-1,-1,1700414462361600⟩,⟨8,94,110,1,1,1,1558713257164800⟩,⟨35,51,137,1,1,1,1558713257164800⟩,⟨23,58,91,-1,-1,1,472337350656000⟩,⟨54,87,122,-1,-1,1,472337350656000⟩,⟨20,70,87,1,1,1,991908436377600⟩,⟨58,75,125,1,1,1,991908436377600⟩,⟨8,84,91,1,1,1,141701205196800⟩,⟨54,61,137,1,1,1,141701205196800⟩,⟨20,45,85,-1,-1,1,850207231180800⟩,⟨60,100,125,-1,-1,1,850207231180800⟩,⟨20,71,87,1,1,1,47233735065600⟩,⟨58,74,125,1,1,1,47233735065600⟩,⟨31,35,68,-1,-1,1,2031050607820800⟩,⟨77,110,114,-1,-1,1,2031050607820800⟩,⟨31,34,67,-1,-1,1,377869880524800⟩,⟨78,111,114,-1,-1,1,377869880524800⟩,⟨22,84,115,1,1,1,2219985548083200⟩,⟨30,61,123,1,1,1,2219985548083200⟩,⟨39,90,93,1,-1,-1,3589763864985600⟩,⟨52,55,106,-1,1,-1,3589763864985600⟩,⟨50,55,95,-1,-1,1,141701205196800⟩,⟨50,90,95,-1,-1,1,141701205196800⟩],[⟨21,24,65,-1,-1,1,472337350656000⟩,⟨80,121,124,-1,-1,1,472337350656000⟩,⟨8,93,109,1,1,1,2078284342886400⟩,⟨36,52,137,1,1,1,2078284342886400⟩,⟨28,31,33,-1,-1,1,1322544581836800⟩,⟨112,114,117,-1,-1,1,1322544581836800⟩,⟨10,13,20,1,-1,-1,1558713257164800⟩,⟨125,132,135,-1,1,-1,1558713257164800⟩,⟨48,90,94,-1,-1,1,4959542181888000⟩,⟨51,55,97,-1,-1,1,4959542181888000⟩,⟨31,57,66,-1,-1,1,1511479522099200⟩,⟨79,88,114,-1,-1,1,1511479522099200⟩,⟨32,52,110,-1,-1,1,2361686753280000⟩,⟨35,93,113,-1,-1,1,2361686753280000⟩,⟨16,90,96,1,-1,-1,3022959044198400⟩,⟨49,55,129,-1,1,-1,3022959044198400⟩,⟨20,47,86,-1,-1,1,1275310846771200⟩,⟨59,98,125,-1,-1,1,1275310846771200⟩,⟨15,73,113,1,1,1,1039142171443200⟩,⟨32,72,130,1,1,1,1039142171443200⟩,⟨32,58,68,-1,-1,1,236168675328000⟩,⟨77,87,113,-1,-1,1,236168675328000⟩,⟨46,53,91,-1,-1,1,94467470131200⟩,⟨54,92,99,-1,-1,1,94467470131200⟩,⟨8,85,92,1,1,1,47233735065600⟩,⟨53,60,137,1,1,1,47233735065600⟩,⟨20,73,121,-1,-1,1,377869880524800⟩,⟨24,72,125,-1,-1,1,377869880524800⟩,⟨22,81,109,-1,-1,1,377869880524800⟩,⟨36,64,123,-1,-1,1,377869880524800⟩],[⟨8,19,51,-1,-1,1,472337350656000⟩,⟨94,126,137,-1,-1,1,472337350656000⟩,⟨15,30,33,1,-1,-1,236168675328000⟩,⟨112,115,130,-1,1,-1,236168675328000⟩,⟨20,97,122,1,1,1,944674701312000⟩,⟨23,48,125,1,1,1,944674701312000⟩,⟨31,57,73,-1,1,-1,472337350656000⟩,⟨72,88,114,1,-1,-1,472337350656000⟩,⟨16,19,112,1,1,1,2172751813017600⟩,⟨33,126,129,1,1,1,2172751813017600⟩,⟨10,11,86,-1,1,-1,1133609641574400⟩,⟨59,134,135,1,-1,-1,1133609641574400⟩,⟨21,76,121,-1,-1,1,519571085721600⟩,⟨24,69,124,-1,-1,1,519571085721600⟩,⟨22,33,91,-1,-1,1,94467470131200⟩,⟨54,112,123,-1,-1,1,94467470131200⟩,⟨52,79,91,-1,1,-1,472337350656000⟩,⟨54,66,93,1,-1,-1,472337350656000⟩,⟨47,90,93,-1,-1,1,425103615590400⟩,⟨52,55,98,-1,-1,1,425103615590400⟩,⟨20,48,86,-1,-1,1,4203802420838400⟩,⟨59,97,125,-1,-1,1,4203802420838400⟩,⟨32,36,69,-1,-1,1,3211893984460800⟩,⟨76,109,113,-1,-1,1,3211893984460800⟩,⟨20,46,86,-1,-1,1,472337350656000⟩,⟨59,99,125,-1,-1,1,472337350656000⟩,⟨15,54,58,1,-1,-1,188934940262400⟩,⟨87,91,130,-1,1,-1,188934940262400⟩,⟨19,43,122,-1,-1,1,283402410393600⟩,⟨23,102,126,-1,-1,1,283402410393600⟩],[⟨38,53,57,1,-1,-1,3778698805248000⟩,⟨88,92,107,-1,1,-1,3778698805248000⟩,⟨19,46,84,-1,-1,1,1983816872755200⟩,⟨61,99,126,-1,-1,1,1983816872755200⟩,⟨12,30,88,-1,-1,1,802973496115200⟩,⟨57,115,133,-1,-1,1,802973496115200⟩,⟨7,18,51,-1,-1,1,2739556633804800⟩,⟨94,127,138,-1,-1,1,2739556633804800⟩,⟨45,89,91,-1,-1,1,141701205196800⟩,⟨54,56,100,-1,-1,1,141701205196800⟩,⟨19,98,122,1,1,1,1228077111705600⟩,⟨23,47,126,1,1,1,1228077111705600⟩,⟨47,54,93,-1,-1,1,5101243387084800⟩,⟨52,91,98,-1,-1,1,5101243387084800⟩,⟨31,59,62,-1,-1,1,991908436377600⟩,⟨83,86,114,-1,-1,1,991908436377600⟩,⟨12,19,41,-1,1,-1,519571085721600⟩,⟨104,126,133,1,-1,-1,519571085721600⟩,⟨25,74,114,1,1,1,755739761049600⟩,⟨31,71,120,1,1,1,755739761049600⟩,⟨49,90,95,-1,-1,1,6093151823462400⟩,⟨50,55,96,-1,-1,1,6093151823462400⟩,⟨20,85,101,1,1,1,377869880524800⟩,⟨44,60,125,1,1,1,377869880524800⟩,⟨8,92,131,1,1,1,472337350656000⟩,⟨14,53,137,1,1,1,472337350656000⟩,⟨23,115,119,1,1,1,1794881932492800⟩,⟨26,30,122,1,1,1,1794881932492800⟩,⟨19,62,113,1,1,1,94467470131200⟩,⟨32,83,126,1,1,1,94467470131200⟩],[⟨36,57,89,-1,-1,1,1983816872755200⟩,⟨56,88,109,-1,-1,1,1983816872755200⟩,⟨30,33,37,-1,-1,1,4959542181888000⟩,⟨108,112,115,-1,-1,1,4959542181888000⟩,⟨48,54,94,-1,-1,1,3778698805248000⟩,⟨51,91,97,-1,-1,1,3778698805248000⟩,⟨30,32,61,-1,-1,1,2597855428608000⟩,⟨84,113,115,-1,-1,1,2597855428608000⟩,⟨17,32,58,-1,-1,1,1039142171443200⟩,⟨87,113,128,-1,-1,1,1039142171443200⟩,⟨22,81,121,-1,-1,1,1133609641574400⟩,⟨24,64,123,-1,-1,1,1133609641574400⟩,⟨19,84,100,1,1,1,2692322898739200⟩,⟨45,61,126,1,1,1,2692322898739200⟩,⟨14,21,66,-1,1,-1,2975725309132800⟩,⟨79,124,131,1,-1,-1,2975725309132800⟩,⟨6,9,12,1,1,1,2881257839001600⟩,⟨133,136,139,1,1,1,2881257839001600⟩,⟨20,28,111,-1,-1,1,1605946992230400⟩,⟨34,117,125,-1,-1,1,1605946992230400⟩,⟨21,34,94,-1,-1,1,1842115667558400⟩,⟨51,111,124,-1,-1,1,1842115667558400⟩,⟨13,20,28,-1,-1,1,425103615590400⟩,⟨117,125,132,-1,-1,1,425103615590400⟩,⟨32,59,68,-1,-1,1,188934940262400⟩,⟨77,86,113,-1,-1,1,188934940262400⟩,⟨29,32,59,-1,-1,1,330636145459200⟩,⟨86,113,116,-1,-1,1,330636145459200⟩,⟨24,29,32,1,-1,-1,188934940262400⟩,⟨113,116,121,-1,1,-1,188934940262400⟩],[⟨21,73,86,-1,-1,1,94467470131200⟩,⟨59,72,124,-1,-1,1,94467470131200⟩,⟨7,95,110,1,1,1,2645089163673600⟩,⟨35,50,138,1,1,1,2645089163673600⟩,⟨19,84,102,1,1,1,897440966246400⟩,⟨43,61,126,1,1,1,897440966246400⟩,⟨14,21,65,-1,1,-1,708506025984000⟩,⟨80,124,131,1,-1,-1,708506025984000⟩,⟨21,32,90,-1,-1,1,236168675328000⟩,⟨55,113,124,-1,-1,1,236168675328000⟩,⟨9,64,124,1,-1,-1,94467470131200⟩,⟨21,81,136,-1,1,-1,94467470131200⟩,⟨19,28,112,-1,-1,1,236168675328000⟩,⟨33,117,126,-1,-1,1,236168675328000⟩,⟨37,88,92,1,-1,-1,3211893984460800⟩,⟨53,57,108,-1,1,-1,3211893984460800⟩,⟨21,32,91,-1,-1,1,614038555852800⟩,⟨54,113,124,-1,-1,1,614038555852800⟩,⟨13,51,124,1,1,1,141701205196800⟩,⟨21,94,132,1,1,1,141701205196800⟩,⟨7,84,91,1,1,1,330636145459200⟩,⟨54,61,138,1,1,1,330636145459200⟩,⟨27,30,57,-1,-1,1,2786790368870400⟩,⟨88,115,118,-1,-1,1,2786790368870400⟩,⟨22,80,109,-1,-1,1,3684231335116800⟩,⟨36,65,123,-1,-1,1,3684231335116800⟩,⟨13,20,27,-1,-1,1,897440966246400⟩,⟨118,125,132,-1,-1,1,897440966246400⟩,⟨13,20,41,-1,1,-1,2267219283148800⟩,⟨104,125,132,1,-1,-1,2267219283148800⟩],[⟨20,68,87,1,1,1,377869880524800⟩,⟨58,77,125,1,1,1,377869880524800⟩,⟨32,59,63,-1,-1,1,1086375906508800⟩,⟨82,86,113,-1,-1,1,1086375906508800⟩,⟨52,75,90,-1,1,-1,1275310846771200⟩,⟨55,70,93,1,-1,-1,1275310846771200⟩]]
def triRows : List ℕ := eval% (List.range 146).map (triangleRow triWidth basisRow triangles.flatten)

def tri : Tri := Tri.ofPacked triWidth (406965861325209600) triLinear triRows
set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem triangle_sound : ∀ y : ℕ → ℝ, (∀ i < 146, 0 ≤ y i ∧ y i ≤ 1) → 0 ≤ evq 146 tri.cT tri.lT tri.qT y := by
  apply tri_hT_packed 146 triWidth (by decide +kernel) triangles (by decide +kernel) (by decide +kernel)
    406965861325209600 (by decide +kernel) triLinear (by decide +kernel) triRows (by decide +kernel) (by decide +kernel)


def matWords : List (List ℕ) := eval% natTable 147 (fun i => natWord 147 37
  (fun j => (proposedEntry inputs G8 tri i j / 62914560 - (-2922935452)).toNat))
def matrixAt (i j : ℕ) : ℤ := 62914560 * Int.ofNat ((tableAt matWords i >>> (37*j)) &&& 137438953471) + (-183895197870981120)
def mat (i j : ℕ) : ℤ := matrixAt (min i j) (max i j)
def tabs : Tabs := { inputs with NT := mat }
end Erdos1186Ex.R5
end

section
namespace Erdos1186Ex.R5

open Erdos1186Ex
theorem grid_ok : (List.range 146).all (gridChk tabs G8) = true := by decide +kernel

theorem vec_ok : (List.range 146).all (vecChk tabs) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair0 : (List.range' 0 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair6 : (List.range' 6 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair12 : (List.range' 12 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair18 : (List.range' 18 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair24 : (List.range' 24 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair30 : (List.range' 30 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair36 : (List.range' 36 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair42 : (List.range' 42 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair48 : (List.range' 48 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair54 : (List.range' 54 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair60 : (List.range' 60 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair66 : (List.range' 66 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair72 : (List.range' 72 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair78 : (List.range' 78 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair84 : (List.range' 84 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair90 : (List.range' 90 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair96 : (List.range' 96 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair102 : (List.range' 102 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair108 : (List.range' 108 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair114 : (List.range' 114 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair120 : (List.range' 120 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair126 : (List.range' 126 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair132 : (List.range' 132 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair138 : (List.range' 138 6).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem pair144 : (List.range' 144 2).all (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) = true := by decide +kernel

theorem pairAll : ∀ i < 146, (fun i => (List.range' i (146-i)).all (quadQuick tabs G8 tri i) && czQuick tabs G8 i) i = true :=
  fun i hi => (join_ranges (join_ranges (join_ranges (join_ranges (all_range_of pair0) (join_ranges (all_range_of pair6) (all_range_of pair12))) (join_ranges (all_range_of pair18) (join_ranges (all_range_of pair24) (all_range_of pair30)))) (join_ranges (join_ranges (all_range_of pair36) (join_ranges (all_range_of pair42) (all_range_of pair48))) (join_ranges (all_range_of pair54) (join_ranges (all_range_of pair60) (all_range_of pair66))))) (join_ranges (join_ranges (join_ranges (all_range_of pair72) (join_ranges (all_range_of pair78) (all_range_of pair84))) (join_ranges (all_range_of pair90) (join_ranges (all_range_of pair96) (all_range_of pair102)))) (join_ranges (join_ranges (all_range_of pair108) (join_ranges (all_range_of pair114) (all_range_of pair120))) (join_ranges (join_ranges (all_range_of pair126) (all_range_of pair132)) (join_ranges (all_range_of pair138) (all_range_of pair144)))))) i (Nat.zero_le i) hi

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear0 : (List.range' 0 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear8 : (List.range' 8 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear16 : (List.range' 16 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear24 : (List.range' 24 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear32 : (List.range' 32 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear40 : (List.range' 40 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear48 : (List.range' 48 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear56 : (List.range' 56 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear64 : (List.range' 64 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear72 : (List.range' 72 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear80 : (List.range' 80 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear88 : (List.range' 88 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear96 : (List.range' 96 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear104 : (List.range' 104 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear112 : (List.range' 112 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear120 : (List.range' 120 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear128 : (List.range' 128 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear136 : (List.range' 136 8).all (linearQuick tabs G8 tri) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem linear144 : (List.range' 144 2).all (linearQuick tabs G8 tri) = true := by decide +kernel

theorem linearAll : ∀ i < 146, (linearQuick tabs G8 tri) i = true :=
  fun i hi => (join_ranges (join_ranges (join_ranges (join_ranges (all_range_of linear0) (all_range_of linear8)) (join_ranges (all_range_of linear16) (all_range_of linear24))) (join_ranges (join_ranges (all_range_of linear32) (all_range_of linear40)) (join_ranges (all_range_of linear48) (join_ranges (all_range_of linear56) (all_range_of linear64))))) (join_ranges (join_ranges (join_ranges (all_range_of linear72) (all_range_of linear80)) (join_ranges (all_range_of linear88) (join_ranges (all_range_of linear96) (all_range_of linear104)))) (join_ranges (join_ranges (all_range_of linear112) (all_range_of linear120)) (join_ranges (all_range_of linear128) (join_ranges (all_range_of linear136) (all_range_of linear144)))))) i (Nat.zero_le i) hi

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance0 : (List.range' 0 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance3 : (List.range' 3 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance6 : (List.range' 6 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance9 : (List.range' 9 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance12 : (List.range' 12 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance15 : (List.range' 15 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance18 : (List.range' 18 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance21 : (List.range' 21 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance24 : (List.range' 24 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance27 : (List.range' 27 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance30 : (List.range' 30 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance33 : (List.range' 33 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance36 : (List.range' 36 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance39 : (List.range' 39 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance42 : (List.range' 42 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance45 : (List.range' 45 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance48 : (List.range' 48 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance51 : (List.range' 51 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance54 : (List.range' 54 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance57 : (List.range' 57 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance60 : (List.range' 60 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance63 : (List.range' 63 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance66 : (List.range' 66 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance69 : (List.range' 69 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance72 : (List.range' 72 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance75 : (List.range' 75 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance78 : (List.range' 78 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance81 : (List.range' 81 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance84 : (List.range' 84 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance87 : (List.range' 87 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance90 : (List.range' 90 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance93 : (List.range' 93 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance96 : (List.range' 96 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance99 : (List.range' 99 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance102 : (List.range' 102 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance105 : (List.range' 105 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance108 : (List.range' 108 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance111 : (List.range' 111 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance114 : (List.range' 114 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance117 : (List.range' 117 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance120 : (List.range' 120 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance123 : (List.range' 123 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance126 : (List.range' 126 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance129 : (List.range' 129 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance132 : (List.range' 132 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance135 : (List.range' 135 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance138 : (List.range' 138 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance141 : (List.range' 141 3).all (quickDominance tabs gram) = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem dominance144 : (List.range' 144 3).all (quickDominance tabs gram) = true := by decide +kernel

theorem dominanceAll : ∀ i < 147, (quickDominance tabs gram) i = true :=
  fun i hi => (join_ranges (join_ranges (join_ranges (join_ranges (join_ranges (all_range_of dominance0) (join_ranges (all_range_of dominance3) (all_range_of dominance6))) (join_ranges (all_range_of dominance9) (join_ranges (all_range_of dominance12) (all_range_of dominance15)))) (join_ranges (join_ranges (all_range_of dominance18) (join_ranges (all_range_of dominance21) (all_range_of dominance24))) (join_ranges (all_range_of dominance27) (join_ranges (all_range_of dominance30) (all_range_of dominance33))))) (join_ranges (join_ranges (join_ranges (all_range_of dominance36) (join_ranges (all_range_of dominance39) (all_range_of dominance42))) (join_ranges (all_range_of dominance45) (join_ranges (all_range_of dominance48) (all_range_of dominance51)))) (join_ranges (join_ranges (all_range_of dominance54) (join_ranges (all_range_of dominance57) (all_range_of dominance60))) (join_ranges (all_range_of dominance63) (join_ranges (all_range_of dominance66) (all_range_of dominance69)))))) (join_ranges (join_ranges (join_ranges (join_ranges (all_range_of dominance72) (join_ranges (all_range_of dominance75) (all_range_of dominance78))) (join_ranges (all_range_of dominance81) (join_ranges (all_range_of dominance84) (all_range_of dominance87)))) (join_ranges (join_ranges (all_range_of dominance90) (join_ranges (all_range_of dominance93) (all_range_of dominance96))) (join_ranges (all_range_of dominance99) (join_ranges (all_range_of dominance102) (all_range_of dominance105))))) (join_ranges (join_ranges (join_ranges (all_range_of dominance108) (join_ranges (all_range_of dominance111) (all_range_of dominance114))) (join_ranges (all_range_of dominance117) (join_ranges (all_range_of dominance120) (all_range_of dominance123)))) (join_ranges (join_ranges (all_range_of dominance126) (join_ranges (all_range_of dominance129) (all_range_of dominance132))) (join_ranges (join_ranges (all_range_of dominance135) (all_range_of dominance138)) (join_ranges (all_range_of dominance141) (all_range_of dominance144))))))) i (Nat.zero_le i) hi

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput0 : (List.range' 0 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput10 : (List.range' 10 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput20 : (List.range' 20 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput30 : (List.range' 30 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput40 : (List.range' 40 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput50 : (List.range' 50 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput60 : (List.range' 60 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput70 : (List.range' 70 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput80 : (List.range' 80 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput90 : (List.range' 90 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput100 : (List.range' 100 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput110 : (List.range' 110 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput120 : (List.range' 120 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput130 : (List.range' 130 10).all gram.check = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem gramInput140 : (List.range' 140 7).all gram.check = true := by decide +kernel

theorem gramInputs : ∀ i < 147, gram.check i = true := fun i hi => (join_ranges (join_ranges (join_ranges (all_range_of gramInput0) (join_ranges (all_range_of gramInput10) (all_range_of gramInput20))) (join_ranges (join_ranges (all_range_of gramInput30) (all_range_of gramInput40)) (join_ranges (all_range_of gramInput50) (all_range_of gramInput60)))) (join_ranges (join_ranges (join_ranges (all_range_of gramInput70) (all_range_of gramInput80)) (join_ranges (all_range_of gramInput90) (all_range_of gramInput100))) (join_ranges (join_ranges (all_range_of gramInput110) (all_range_of gramInput120)) (join_ranges (all_range_of gramInput130) (all_range_of gramInput140))))) i (Nat.zero_le i) hi

theorem soundDominance (i : ℕ) (hi : i < 147) : domRow tabs i = true := by
  apply dominance_of_packing tabs gram (by decide +kernel) (by decide +kernel) (by change gram.scaledRows.length = gram.n; simp [GramPacking.scaledRows]) _ gramInputs i hi (dominanceAll i hi)
  intro j hj
  refine ⟨gram.row_eq hj,?_⟩
  simp [GramPacking.row]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem constant_ok : constantQuick tabs G8 tri = true := by decide +kernel

theorem region : RegionLB G8 (9/20) (1/2) := by
  have hp (i : ℕ) (hi : i < 146) :
      ((List.range' i (146-i)).all (quadQuick tabs G8 tri i) = true) ∧ czQuick tabs G8 i = true := by
    simpa only [Bool.and_eq_true] using pairAll i hi
  have hs (a b : ℕ) : tabs.NT a b = tabs.NT b a := by
    change matrixAt (min a b) (max a b) = matrixAt (min b a) (max b a)
    rw [min_comm a b, max_comm a b]
  have hw (i j : ℕ) : (0 ≤ tabs.thT i j ∧ tabs.thT i j ≤ Qn) ∧
      0 ≤ tabs.YYT i j ∧ 0 ≤ tabs.OOT i j ∧ 0 ≤ tabs.YOT i j := by
    refine ⟨⟨Int.ofNat_nonneg _,?_⟩, Int.ofNat_nonneg _, Int.ofNat_nonneg _, Int.ofNat_nonneg _⟩
    change Int.ofNat (min 1099511627776 _) ≤ Int.ofNat 1099511627776
    exact Int.ofNat_le.mpr (Nat.min_le_left _ _)
  have h := region_of_tabs tabs G8 tri 146 (by decide +kernel) (by decide +kernel)
    (all_range0_of grid_ok) (all_range0_of vec_ok) (by decide +kernel)
    (pair_from_upper tabs G8 tri 146 hs hw fun i hi => (hp i hi).1)
    (fun i hi => (linearQuick_eq tabs G8 tri i) ▸ linearAll i hi)
    (fun i hi => (czQuick_eq tabs G8 i) ▸ (hp i hi).2)
    ((constantQuick_eq tabs G8 tri) ▸ constant_ok) (by decide +kernel) soundDominance triangle_sound
  have leq : ((tabs.loN : ℤ) : ℚ) / 20 = (9/20 : ℚ) := by change ((9:ℚ)/20) = _; norm_num
  have heq : ((tabs.hiN : ℤ) : ℚ) / 20 = (1/2 : ℚ) := by change ((10:ℚ)/20) = _; norm_num
  rwa [leq, heq] at h

end Erdos1186Ex.R5
end

theorem OMA.solution : OMA.R_Erdos1186_erdos_1186_variants_prs_conjecture_R1.H2 :=
  Erdos1186Ex.FarCut.bound Erdos1186Ex.R4.region Erdos1186Ex.R5.region

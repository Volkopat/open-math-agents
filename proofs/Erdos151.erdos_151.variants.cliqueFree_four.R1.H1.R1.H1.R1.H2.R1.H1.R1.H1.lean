import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H2_R1_H1_R1
import Mathlib

/-! Pure-kernel proof of R(3,6) <= 18 (R1.H1.R1.H1.R1.H2.R1.H1.R1.H1).
Uses R(3,3)<=6, R(3,4)<=9, R(3,5)<=14, e(3,4,8)>=10, Cariolaro's 5-line
elimination of degree-4 vertices, structural characterization of 5-regular
18-vertex graphs (S4 = C4, S3 2-regular), and a tiny pure-kernel decision
tree verifying uniqueness of the (3,5,12,20)-graph H0 and impossibility of
extending H0 by 5 vertices. -/
-- Step: Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H2.R1.H1.R1.H1
-- Credit: @SanskarX10

open Finset SimpleGraph
open scoped Classical

-- === BEGIN HELPERS ===

private def baseAdj12 : Array Nat :=
  #[58, 197, 778, 3077, 1, 1, 2, 2, 4, 4, 8, 8]

private def candEdges24 : Array (Nat × Nat) :=
  #[(4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (6, 8), (6, 9), (6, 10), (6, 11), (7, 8), (7, 9), (7, 10), (7, 11), (8, 10), (8, 11), (9, 10), (9, 11)]

private def h0Adj12 : Array Nat :=
  #[58, 197, 778, 3077, 321, 1537, 1042, 2306, 148, 2084, 104, 648]

private def swapMasks16 : Array Nat :=
  #[8996357, 8995160, 8689158, 8688024, 2770185, 2769492, 2401546, 2400916, 4557317, 4555112, 4741638, 4739496, 1476873, 1475172, 1599754, 1598116]

private def ind4H0List : List Nat :=
  [197, 2117, 1157, 3077, 705, 833, 2369, 1665, 1793, 3329, 58, 538, 298, 778, 2098, 1554, 3090, 2338, 1794, 3330, 180, 2100, 1172, 3092, 228, 2148, 184, 664, 232, 360, 712, 840, 1680, 2400]

private def indAllH0List : List Nat :=
  [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 5, 65, 129, 257, 513, 1025, 2049, 10, 18, 34, 258, 514, 1026, 2050, 20, 36, 68, 132, 1028, 2052, 24, 40, 72, 136, 264, 520, 48, 144, 528, 1040, 2064, 96, 160, 288, 2080, 192, 320, 576, 2112, 640, 1152, 768, 1280, 2304, 1536, 3072, 69, 133, 1029, 2053, 193, 321, 577, 2113, 641, 1153, 769, 1281, 2305, 1537, 3073, 26, 42, 266, 522, 50, 530, 1042, 2066, 290, 2082, 770, 1282, 2306, 1538, 3074, 52, 148, 1044, 2068, 100, 164, 2084, 196, 2116, 1156, 3076, 56, 152, 536, 104, 168, 296, 200, 328, 584, 648, 776, 176, 2096, 656, 1168, 1552, 3088, 224, 352, 2144, 2336, 704, 832, 2368, 1664, 1792, 3328, 197, 2117, 1157, 3077, 705, 833, 2369, 1665, 1793, 3329, 58, 538, 298, 778, 2098, 1554, 3090, 2338, 1794, 3330, 180, 2100, 1172, 3092, 228, 2148, 184, 664, 232, 360, 712, 840, 1680, 2400]

private def swapVert (bits v : Nat) : Nat :=
  if v < 4 then v
  else if bits.testBit ((v - 4) / 2) then v ^^^ 1 else v

private def incMask12 : Array Nat :=
  #[0, 0, 0, 0, 63, 4032, 61505, 983170, 3215620, 12722696, 5522448, 11044896]

private def edgeBit144 : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 8, 16, 32, 0, 0, 0, 0, 0, 0, 64, 128, 256, 512, 1024, 2048, 0, 0, 0, 0, 1, 64, 0, 0, 4096, 8192, 16384, 32768, 0, 0, 0, 0, 2, 128, 0, 0, 65536, 131072, 262144, 524288, 0, 0, 0, 0, 4, 256, 4096, 65536, 0, 0, 1048576, 2097152, 0, 0, 0, 0, 8, 512, 8192, 131072, 0, 0, 4194304, 8388608, 0, 0, 0, 0, 16, 1024, 16384, 262144, 1048576, 4194304, 0, 0, 0, 0, 0, 0, 32, 2048, 32768, 524288, 2097152, 8388608, 0, 0]

private def isAdjYes (yes a b : Nat) : Bool :=
  (baseAdj12.getD a 0).testBit b || ((yes &&& edgeBit144.getD (a * 12 + b) 0) != 0)

private def isAdjPoss (_yes no a b : Nat) : Bool :=
  (baseAdj12.getD a 0).testBit b || ((((16777215 - no) &&& edgeBit144.getD (a * 12 + b) 0)) != 0)

private def pop24 (m : Nat) : Nat :=
  (List.range 24).countP fun i => m.testBit i

private def degYes (yes u : Nat) : Nat :=
  pop24 (yes &&& incMask12.getD u 0)

private def degPoss (_yes no u : Nat) : Nat :=
  pop24 ((16777215 - no) &&& incMask12.getD u 0)

private def checkInd5 (adjFn : Nat → Nat → Bool) (a b c d e : Nat) : Bool :=
  a < b && b < c && c < d && d < e && e < 12 &&
  !(adjFn a b) && !(adjFn a c) && !(adjFn a d) && !(adjFn a e) &&
  !(adjFn b c) && !(adjFn b d) && !(adjFn b e) &&
  !(adjFn c d) && !(adjFn c e) && !(adjFn d e)

private inductive S3Tree where
  | degHi (u : Nat)
  | degLo (u : Nat)
  | tri (a b c : Nat)
  | ind5 (a b c d e : Nat)
  | ind5Full (a b c d e : Nat)
  | valid (bits : Nat)
  | branch (idx : Nat) (withE : S3Tree) (withoutE : S3Tree)

private def checkS3Tree : S3Tree → Nat → Nat → Bool
  | S3Tree.degHi u, yes, _ => 4 ≤ u && u < 12 && degYes yes u > 2
  | S3Tree.degLo u, yes, no => 4 ≤ u && u < 12 && degPoss yes no u < 2
  | S3Tree.tri a b c, yes, _ =>
      a < 12 && b < 12 && c < 12 &&
      isAdjYes yes a b && isAdjYes yes a c && isAdjYes yes b c
  | S3Tree.ind5 a b c d e, yes, no => checkInd5 (isAdjPoss yes no) a b c d e
  | S3Tree.ind5Full a b c d e, yes, _ =>
      (List.range 8).all (fun i => degYes yes (i + 4) == 2) &&
      checkInd5 (isAdjYes yes) a b c d e
  | S3Tree.valid bits, yes, _ =>
      bits < 16 &&
      (List.range 8).all (fun i => degYes yes (i + 4) == 2) &&
      yes == swapMasks16.getD bits 0
  | S3Tree.branch idx t1 t2, yes, no =>
      idx < 24 && !(yes.testBit idx) && !(no.testBit idx) &&
      checkS3Tree t1 (yes ||| (1 <<< idx)) no &&
      checkS3Tree t2 yes (no ||| (1 <<< idx))

private def s3TreeCert : S3Tree :=
  S3Tree.branch 0 (S3Tree.branch 1 (S3Tree.branch 6 (S3Tree.branch 7 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 8 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 8))) (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 17 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 12 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 8 9)) (S3Tree.branch 21 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 8 9)) (S3Tree.degLo 8))))) (S3Tree.branch 18 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 12 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 8 9)) (S3Tree.branch 21 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 8 9)) (S3Tree.degLo 10))))) (S3Tree.degLo 8))))) (S3Tree.branch 19 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 12 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 21 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.degLo 10)))) (S3Tree.degLo 8))))) (S3Tree.degLo 7))))) (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 17 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 18 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 19 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 7))))) (S3Tree.ind5 1 3 5 8 9)))) (S3Tree.branch 12 (S3Tree.branch 7 (S3Tree.branch 8 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 9 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 8 (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))))) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.degLo 10))))) (S3Tree.degLo 9))))) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.degLo 10)))) (S3Tree.degLo 9))))) (S3Tree.degLo 7))))) (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 7))))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 7))))) (S3Tree.degLo 5)))) (S3Tree.branch 9 (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.tri 5 9 10) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.degLo 9)))))) (S3Tree.branch 17 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 18 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 19 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 7))))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 23 (S3Tree.tri 5 9 11) (S3Tree.degLo 9)))))) (S3Tree.branch 17 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 18 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 19 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 7))))) (S3Tree.degLo 5))) (S3Tree.ind5 1 3 5 8 9)))) (S3Tree.branch 13 (S3Tree.branch 7 (S3Tree.branch 8 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 16 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 8 9)) (S3Tree.branch 21 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 8 9)) (S3Tree.degLo 8))))) (S3Tree.branch 9 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 8 (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))))) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 20 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 21 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.degLo 8)))) (S3Tree.branch 19 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 20 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 21 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.degLo 10)))) (S3Tree.degLo 8)))) (S3Tree.degLo 7))))) (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 17 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 20 (S3Tree.tri 5 8 10) (S3Tree.branch 21 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.degLo 8)))) (S3Tree.branch 18 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 20 (S3Tree.degHi 10) (S3Tree.branch 21 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 8)))) (S3Tree.branch 19 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 20 (S3Tree.tri 5 8 10) (S3Tree.branch 21 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 8)))) (S3Tree.degLo 7))))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 17 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 20 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 21 (S3Tree.tri 5 8 11) (S3Tree.degLo 8)))) (S3Tree.branch 18 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 20 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 21 (S3Tree.tri 5 8 11) (S3Tree.degLo 8)))) (S3Tree.branch 19 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 20 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 21 (S3Tree.degHi 11) (S3Tree.degLo 8)))) (S3Tree.degLo 7))))) (S3Tree.degLo 5)))) (S3Tree.branch 9 (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.degLo 5))) (S3Tree.ind5 1 3 5 8 9)))) (S3Tree.branch 14 (S3Tree.branch 7 (S3Tree.branch 8 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 16 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 8 9)) (S3Tree.branch 21 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 8 9)) (S3Tree.degLo 10))))) (S3Tree.degLo 8))))) (S3Tree.branch 9 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 8 (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.degLo 10))))) (S3Tree.degLo 9))))) (S3Tree.branch 17 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 20 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 21 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.degLo 8)))) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 17 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 20 (S3Tree.degHi 10) (S3Tree.branch 21 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 8)))) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 17 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 20 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 21 (S3Tree.tri 5 8 11) (S3Tree.degLo 8)))) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.degLo 5)))) (S3Tree.branch 9 (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.degLo 5))) (S3Tree.ind5 1 3 5 8 9)))) (S3Tree.branch 15 (S3Tree.branch 7 (S3Tree.branch 8 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 16 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 21 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.degLo 10)))) (S3Tree.degLo 8))))) (S3Tree.branch 9 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 8 (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.degLo 10)))) (S3Tree.degLo 9))))) (S3Tree.branch 17 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 20 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 21 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.degLo 10)))) (S3Tree.degLo 8)))) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 17 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 20 (S3Tree.tri 5 8 10) (S3Tree.branch 21 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 8)))) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 17 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.branch 20 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 21 (S3Tree.degHi 11) (S3Tree.degLo 8)))) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.degLo 5)))) (S3Tree.branch 9 (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.branch 2 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.degLo 5))) (S3Tree.ind5 1 3 5 8 9)))) (S3Tree.degLo 6)))))) (S3Tree.branch 2 (S3Tree.branch 6 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 17 (S3Tree.branch 8 (S3Tree.degHi 5) (S3Tree.branch 12 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 21 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.degLo 8))))) (S3Tree.branch 18 (S3Tree.branch 8 (S3Tree.degHi 5) (S3Tree.branch 12 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 21 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.degLo 10))))) (S3Tree.degLo 8))))) (S3Tree.branch 19 (S3Tree.branch 8 (S3Tree.degHi 5) (S3Tree.branch 12 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 21 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.degLo 10)))) (S3Tree.degLo 8))))) (S3Tree.degLo 7))))) (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.degLo 7))) (S3Tree.branch 18 (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.degLo 7)) (S3Tree.degLo 7)))) (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))))) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.degLo 10))))) (S3Tree.degLo 9))))) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.degLo 9))))) (S3Tree.degLo 7)))) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.branch 12 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 21 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.degLo 8)))) (S3Tree.branch 19 (S3Tree.branch 12 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.branch 21 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.degLo 8)))) (S3Tree.degLo 7))) (S3Tree.branch 18 (S3Tree.branch 19 (S3Tree.branch 12 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 21 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.degLo 8)))) (S3Tree.degLo 7)) (S3Tree.degLo 7)))) (S3Tree.ind5 1 3 5 8 9)))) (S3Tree.branch 12 (S3Tree.tri 4 6 8) (S3Tree.branch 13 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))))) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.degLo 7))))) (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10)))))) (S3Tree.degLo 7)) (S3Tree.degLo 7)))) (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 7))) (S3Tree.branch 18 (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 7)) (S3Tree.degLo 7)))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.ind5 2 4 5 7 10)) (S3Tree.degLo 7))) (S3Tree.branch 18 (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 7)) (S3Tree.degLo 7)))) (S3Tree.degLo 5))))) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))))) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.branch 9 (S3Tree.branch 10 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 7)))) (S3Tree.branch 11 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.ind5 2 4 5 7 10)) (S3Tree.degLo 7)))) (S3Tree.degLo 5))) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.degLo 7)))) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.degLo 10)))) (S3Tree.degLo 7)))) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.degLo 8))))) (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.degLo 7))) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 7))) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 7))) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.degLo 5))))) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.degLo 10))))) (S3Tree.degLo 9))))) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.branch 9 (S3Tree.branch 10 (S3Tree.branch 17 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 22 (S3Tree.degHi 10) (S3Tree.branch 23 (S3Tree.valid 0) (S3Tree.degLo 9)))) (S3Tree.degLo 7)))) (S3Tree.branch 11 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 22 (S3Tree.degHi 10) (S3Tree.branch 23 (S3Tree.tri 5 9 11) (S3Tree.degLo 9)))) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 22 (S3Tree.ind5Full 0 6 8 9 11) (S3Tree.branch 23 (S3Tree.degHi 11) (S3Tree.degLo 9)))) (S3Tree.degLo 7)))) (S3Tree.degLo 5))) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.tri 5 7 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.tri 5 7 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.degLo 8))))) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.ind5 0 2 6 7 10)) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 0 2 6 7 10)) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 0 2 6 7 10)) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.degLo 5))))) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.degLo 10)))) (S3Tree.degLo 9))))) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.branch 9 (S3Tree.branch 10 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 22 (S3Tree.degHi 10) (S3Tree.branch 23 (S3Tree.ind5Full 0 6 8 9 10) (S3Tree.degLo 9)))) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.branch 11 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 22 (S3Tree.valid 8) (S3Tree.branch 23 (S3Tree.degHi 11) (S3Tree.degLo 9)))) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 5))) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.tri 5 7 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.tri 5 7 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.degLo 8))))) (S3Tree.degLo 6)))))) (S3Tree.branch 3 (S3Tree.branch 6 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.branch 8 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 17 (S3Tree.branch 8 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 18 (S3Tree.branch 8 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 19 (S3Tree.branch 8 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 7))))) (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))))) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.degLo 10))))) (S3Tree.degLo 9))))) (S3Tree.branch 19 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.degLo 9))))) (S3Tree.degLo 7)))) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.branch 12 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 21 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.degLo 8)))) (S3Tree.branch 19 (S3Tree.branch 12 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.branch 21 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.degLo 8)))) (S3Tree.degLo 7))) (S3Tree.branch 18 (S3Tree.branch 19 (S3Tree.branch 12 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 21 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.degLo 8)))) (S3Tree.degLo 7)) (S3Tree.degLo 7)))) (S3Tree.ind5 1 3 4 5 8))) (S3Tree.branch 12 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))))) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.degLo 10))))) (S3Tree.degLo 9))))) (S3Tree.branch 19 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.degLo 10)))) (S3Tree.degLo 9))))) (S3Tree.degLo 7))))) (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10)))))) (S3Tree.degLo 7)) (S3Tree.degLo 7)))) (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 7))) (S3Tree.branch 18 (S3Tree.branch 19 (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.ind5 3 5 6 7 9)) (S3Tree.degLo 7)) (S3Tree.degLo 7)))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.ind5 2 4 5 7 10)) (S3Tree.degLo 7))) (S3Tree.branch 18 (S3Tree.branch 19 (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.ind5 3 5 6 7 9)) (S3Tree.degLo 7)) (S3Tree.degLo 7)))) (S3Tree.degLo 5))))) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 13 (S3Tree.tri 4 6 9) (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.tri 5 7 8) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.degLo 7)))) (S3Tree.branch 10 (S3Tree.branch 17 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.ind5 3 5 6 7 9)) (S3Tree.branch 11 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.ind5 3 5 6 7 9)) (S3Tree.degLo 5))))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 10 (S3Tree.degHi 10) (S3Tree.branch 11 (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.branch 19 (S3Tree.ind5Full 0 6 8 9 11) (S3Tree.degLo 7))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.degLo 5))))) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 10 (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.branch 19 (S3Tree.valid 4) (S3Tree.degLo 7))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 11 (S3Tree.tri 5 8 11) (S3Tree.degLo 5))))) (S3Tree.degLo 8)))) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.tri 5 7 8) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.branch 10 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.ind5 3 5 6 7 9)) (S3Tree.branch 11 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.ind5 3 5 6 7 9)) (S3Tree.degLo 5))))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 10 (S3Tree.tri 5 8 10) (S3Tree.branch 11 (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.valid 12) (S3Tree.ind5 0 2 6 7 10)) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.degLo 5))))) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.degLo 10)))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 10 (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.ind5Full 0 6 8 9 10) (S3Tree.ind5 0 2 6 7 10)) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 11 (S3Tree.degHi 11) (S3Tree.degLo 5))))) (S3Tree.degLo 8)))) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 6)))))) (S3Tree.ind5 1 3 4 8 9)))) (S3Tree.branch 1 (S3Tree.branch 2 (S3Tree.branch 6 (S3Tree.branch 12 (S3Tree.branch 7 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))))) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.degLo 10))))) (S3Tree.degLo 9))))) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.degLo 10)))) (S3Tree.degLo 9))))) (S3Tree.degLo 7))))) (S3Tree.ind5 1 3 5 8 9)))) (S3Tree.branch 13 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))))) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.degLo 7)))))) (S3Tree.branch 16 (S3Tree.tri 4 7 8) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 9 (S3Tree.tri 5 6 9) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 9 (S3Tree.tri 5 6 9) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.degLo 8))))) (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.ind5 0 6 7 8 9)))) (S3Tree.branch 16 (S3Tree.tri 4 7 8) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.degLo 10))))) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.degLo 8))))) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.ind5 0 6 7 8 9)))) (S3Tree.branch 16 (S3Tree.tri 4 7 8) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.degLo 10)))) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.degLo 10)))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.degLo 8))))) (S3Tree.degLo 6))))) (S3Tree.branch 12 (S3Tree.branch 13 (S3Tree.branch 7 (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.branch 9 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 10)))) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.branch 9 (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 7))))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 7))))) (S3Tree.degLo 5))) (S3Tree.ind5 1 3 5 8 9)))) (S3Tree.branch 14 (S3Tree.branch 7 (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.branch 9 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.degLo 10))))) (S3Tree.degLo 9))))) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.branch 9 (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 22 (S3Tree.degHi 10) (S3Tree.branch 23 (S3Tree.ind5Full 0 7 8 9 10) (S3Tree.degLo 9)))) (S3Tree.degLo 7))))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 22 (S3Tree.degHi 10) (S3Tree.branch 23 (S3Tree.tri 5 9 11) (S3Tree.degLo 9)))) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 22 (S3Tree.valid 10) (S3Tree.branch 23 (S3Tree.degHi 11) (S3Tree.degLo 9)))) (S3Tree.degLo 7))))) (S3Tree.degLo 5))) (S3Tree.ind5 1 3 5 8 9)))) (S3Tree.branch 15 (S3Tree.branch 7 (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.branch 9 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.degLo 9))))) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.branch 9 (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 22 (S3Tree.degHi 10) (S3Tree.branch 23 (S3Tree.valid 2) (S3Tree.degLo 9)))) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.ind5 2 4 5 6 10)) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 22 (S3Tree.ind5Full 0 7 8 9 11) (S3Tree.branch 23 (S3Tree.degHi 11) (S3Tree.degLo 9)))) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.degLo 5))) (S3Tree.ind5 1 3 5 8 9)))) (S3Tree.degLo 6)))) (S3Tree.branch 13 (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.degLo 7))))) (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 7))))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 19 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 7))))) (S3Tree.degLo 5))))) (S3Tree.branch 16 (S3Tree.tri 4 7 8) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.degLo 8))))) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.ind5 2 4 5 6 10)) (S3Tree.branch 18 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.degLo 5))))) (S3Tree.branch 16 (S3Tree.tri 4 7 8) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.degLo 8))))) (S3Tree.degLo 6))) (S3Tree.branch 14 (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10)))))) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.degLo 5))))) (S3Tree.branch 16 (S3Tree.tri 4 7 8) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 3 (S3Tree.degHi 4) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 3 5 6 7 8)) (S3Tree.degLo 8))))) (S3Tree.degLo 6)) (S3Tree.degLo 6))))) (S3Tree.branch 3 (S3Tree.branch 6 (S3Tree.branch 12 (S3Tree.branch 8 (S3Tree.tri 5 6 8) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 13 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.degLo 7))))) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.degLo 10)))) (S3Tree.degLo 7))))) (S3Tree.degLo 8)))) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.degLo 10))))) (S3Tree.degLo 9))))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.tri 4 7 9) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.tri 4 7 9) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.degLo 8)))) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.degLo 10)))) (S3Tree.degLo 9))))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.tri 4 7 9) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.tri 4 7 9) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.degLo 8)))) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 6))))) (S3Tree.branch 12 (S3Tree.branch 13 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 10)))) (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.branch 10 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 7))))) (S3Tree.branch 11 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 7))))) (S3Tree.degLo 5))))) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.degLo 10))))) (S3Tree.degLo 9))))) (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.degLo 7))))) (S3Tree.branch 10 (S3Tree.branch 17 (S3Tree.tri 4 7 9) (S3Tree.ind5 3 5 6 7 9)) (S3Tree.branch 11 (S3Tree.branch 17 (S3Tree.tri 4 7 9) (S3Tree.ind5 3 5 6 7 9)) (S3Tree.degLo 5))))) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.degLo 9))))) (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 10 (S3Tree.branch 17 (S3Tree.tri 4 7 9) (S3Tree.ind5 3 5 6 7 9)) (S3Tree.branch 11 (S3Tree.branch 17 (S3Tree.tri 4 7 9) (S3Tree.ind5 3 5 6 7 9)) (S3Tree.degLo 5))))) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 6)))) (S3Tree.branch 13 (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.degHi 7) (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.branch 10 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 11 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.degLo 5))))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.branch 10 (S3Tree.degHi 10) (S3Tree.branch 11 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.branch 19 (S3Tree.valid 14) (S3Tree.degLo 7)))) (S3Tree.degLo 5))))) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.branch 10 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.branch 19 (S3Tree.ind5Full 0 7 8 9 10) (S3Tree.degLo 7)))) (S3Tree.branch 11 (S3Tree.tri 5 8 11) (S3Tree.degLo 5))))) (S3Tree.degLo 8)))) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.degHi 7) (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.branch 10 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.branch 11 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.ind5 2 4 5 6 10)) (S3Tree.degLo 5))))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.branch 10 (S3Tree.tri 5 8 10) (S3Tree.branch 11 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.ind5Full 0 7 8 9 11) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 5))))) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.branch 10 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.valid 6) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.branch 11 (S3Tree.degHi 11) (S3Tree.degLo 5))))) (S3Tree.degLo 8)))) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 6))) (S3Tree.branch 14 (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.degHi 7) (S3Tree.branch 9 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10)))))) (S3Tree.branch 10 (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.ind5 3 5 6 7 9)) (S3Tree.branch 11 (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.ind5 3 5 6 7 9)) (S3Tree.degLo 5))))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 10 (S3Tree.degHi 10) (S3Tree.branch 11 (S3Tree.branch 17 (S3Tree.tri 4 7 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.degLo 5))))) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 10 (S3Tree.branch 17 (S3Tree.tri 4 7 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 11 (S3Tree.degHi 11) (S3Tree.degLo 5))))) (S3Tree.degLo 8)))) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 6)) (S3Tree.degLo 6))))) (S3Tree.ind5 1 3 4 8 9))) (S3Tree.branch 2 (S3Tree.branch 3 (S3Tree.branch 6 (S3Tree.branch 12 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))))) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.degLo 10))))) (S3Tree.degLo 9))))) (S3Tree.branch 19 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 23 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.degLo 10)))) (S3Tree.degLo 9))))) (S3Tree.degLo 7))))) (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10)))))) (S3Tree.degLo 7)) (S3Tree.degLo 7)))) (S3Tree.ind5 1 3 5 8 9)))) (S3Tree.branch 13 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10)))))) (S3Tree.degLo 7)) (S3Tree.degLo 7))))) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))))) (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.degLo 7)))) (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.degLo 10)))) (S3Tree.degLo 7)))) (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.degLo 8))))) (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.degLo 7))))) (S3Tree.branch 22 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 23 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.degLo 9))))) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.degLo 7)))) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.degLo 8))))) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 22 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 23 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.degLo 9))))) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.degLo 10)))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.degLo 8))))) (S3Tree.degLo 6))))) (S3Tree.branch 12 (S3Tree.branch 13 (S3Tree.branch 7 (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.ind5 1 3 5 8 9))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 14 (S3Tree.branch 9 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.degLo 7))))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 17 (S3Tree.branch 7 (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 22 (S3Tree.branch 7 (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 23 (S3Tree.branch 7 (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.degLo 9))))) (S3Tree.branch 15 (S3Tree.branch 9 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 17 (S3Tree.branch 7 (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 22 (S3Tree.branch 7 (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 23 (S3Tree.branch 7 (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.degLo 9))))) (S3Tree.degLo 6)))) (S3Tree.branch 13 (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 19 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.degLo 7))))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.degLo 8))))) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 9) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.degLo 8))))) (S3Tree.degLo 6))) (S3Tree.branch 14 (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10)))))) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 4 (S3Tree.degHi 4) (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10)))))) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 5 8 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.degLo 8))))) (S3Tree.degLo 6)) (S3Tree.degLo 6))))) (S3Tree.branch 4 (S3Tree.branch 6 (S3Tree.branch 12 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 19 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 7))))) (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 19 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 7))) (S3Tree.branch 18 (S3Tree.branch 19 (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.ind5 3 4 6 7 9)) (S3Tree.degLo 7)) (S3Tree.degLo 7)))) (S3Tree.ind5 1 3 4 5 9)))) (S3Tree.branch 13 (S3Tree.branch 8 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 9 (S3Tree.tri 5 6 9) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 20 (S3Tree.tri 4 8 10) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 19 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 7)))) (S3Tree.branch 9 (S3Tree.tri 5 6 9) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.degLo 8))))) (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.ind5 3 4 6 7 9)) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 20 (S3Tree.degHi 10) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.branch 19 (S3Tree.valid 5) (S3Tree.degLo 7))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.degLo 8))))) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.ind5 3 4 6 7 9)) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 20 (S3Tree.tri 4 8 10) (S3Tree.branch 21 (S3Tree.branch 10 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.ind5 0 2 6 7 10)) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 18 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.ind5Full 0 6 8 9 10) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 8))))) (S3Tree.degLo 6))))) (S3Tree.branch 12 (S3Tree.branch 13 (S3Tree.branch 9 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 19 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 7))))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 14 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.branch 7 (S3Tree.tri 5 7 9) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 3 4 6 7 9)) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 15 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.branch 7 (S3Tree.tri 5 7 9) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 3 4 6 7 9)) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 6)))) (S3Tree.branch 13 (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.branch 19 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 7))))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 20 (S3Tree.degHi 10) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.branch 19 (S3Tree.ind5Full 0 7 8 9 10) (S3Tree.degLo 7)))) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.degLo 8))))) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 20 (S3Tree.tri 4 8 10) (S3Tree.branch 21 (S3Tree.branch 10 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.ind5Full 0 2 6 7 10) (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 18 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.valid 7) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 8))))) (S3Tree.degLo 6))) (S3Tree.branch 14 (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.ind5 3 4 6 7 9)) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 20 (S3Tree.degHi 10) (S3Tree.branch 21 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.tri 5 7 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.degLo 8))))) (S3Tree.degLo 6)) (S3Tree.degLo 6))))) (S3Tree.branch 5 (S3Tree.branch 6 (S3Tree.branch 12 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 19 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 7))))) (S3Tree.branch 8 (S3Tree.degHi 8) (S3Tree.branch 9 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.branch 19 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 7 10)) (S3Tree.degLo 7))) (S3Tree.branch 18 (S3Tree.branch 19 (S3Tree.branch 13 (S3Tree.degHi 6) (S3Tree.ind5 3 4 6 7 9)) (S3Tree.degLo 7)) (S3Tree.degLo 7)))) (S3Tree.ind5 1 3 4 5 9)))) (S3Tree.branch 13 (S3Tree.branch 8 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 9 (S3Tree.tri 5 6 9) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 19 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 7)))) (S3Tree.branch 9 (S3Tree.tri 5 6 9) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 21 (S3Tree.tri 4 8 11) (S3Tree.degLo 8))))) (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.ind5 3 4 6 7 9)) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.branch 19 (S3Tree.ind5Full 0 6 8 9 11) (S3Tree.degLo 7))) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 21 (S3Tree.tri 4 8 11) (S3Tree.degLo 8))))) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.ind5 3 4 6 7 9)) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.branch 20 (S3Tree.branch 10 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.ind5 0 2 6 7 10)) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.branch 18 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.valid 13) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 4 5 9))) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.branch 21 (S3Tree.degHi 11) (S3Tree.degLo 8))))) (S3Tree.degLo 6))))) (S3Tree.branch 12 (S3Tree.branch 13 (S3Tree.branch 9 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.branch 19 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 7))))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 14 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.branch 7 (S3Tree.tri 5 7 9) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 3 4 6 7 9)) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 15 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.branch 7 (S3Tree.tri 5 7 9) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 3 4 6 7 9)) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 6)))) (S3Tree.branch 13 (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.branch 19 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.degLo 7))))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.branch 19 (S3Tree.valid 15) (S3Tree.degLo 7)))) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 21 (S3Tree.tri 4 8 11) (S3Tree.degLo 8))))) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 6 10)) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 6 10)) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 20 (S3Tree.branch 10 (S3Tree.branch 7 (S3Tree.branch 17 (S3Tree.ind5Full 0 2 6 7 10) (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 2 4 5 6 10)) (S3Tree.branch 21 (S3Tree.degHi 11) (S3Tree.degLo 8))))) (S3Tree.degLo 6))) (S3Tree.branch 14 (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 0 6 7 8 9))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.degHi 7) (S3Tree.ind5 3 4 6 7 9)) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 20 (S3Tree.branch 7 (S3Tree.branch 9 (S3Tree.branch 17 (S3Tree.tri 5 7 9) (S3Tree.ind5 0 6 7 8 9)) (S3Tree.ind5 1 3 4 5 9)) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.branch 21 (S3Tree.degHi 11) (S3Tree.degLo 8))))) (S3Tree.degLo 6)) (S3Tree.degLo 6))))) (S3Tree.degLo 4)))) (S3Tree.branch 3 (S3Tree.branch 4 (S3Tree.branch 6 (S3Tree.branch 12 (S3Tree.branch 8 (S3Tree.tri 5 6 8) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 13 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 19 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 7))))) (S3Tree.ind5 3 4 6 7 8)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.branch 19 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 11))))) (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.branch 19 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 22 (S3Tree.degHi 10) (S3Tree.branch 23 (S3Tree.valid 1) (S3Tree.degLo 9)))) (S3Tree.degLo 7))))) (S3Tree.ind5 3 4 6 7 8)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 22 (S3Tree.degHi 10) (S3Tree.branch 23 (S3Tree.ind5Full 0 6 8 9 10) (S3Tree.degLo 9)))) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.ind5 3 4 6 7 8)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 6))))) (S3Tree.branch 12 (S3Tree.branch 13 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 19 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 7))))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 5 (S3Tree.degHi 4) (S3Tree.branch 11 (S3Tree.degHi 5) (S3Tree.branch 15 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 11)))) (S3Tree.branch 18 (S3Tree.degHi 10) (S3Tree.branch 19 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 22 (S3Tree.degHi 10) (S3Tree.branch 23 (S3Tree.ind5Full 0 7 8 9 10) (S3Tree.degLo 9)))) (S3Tree.degLo 7))))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 22 (S3Tree.degHi 10) (S3Tree.branch 23 (S3Tree.valid 3) (S3Tree.degLo 9)))) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 6)))) (S3Tree.branch 13 (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.tri 5 7 8) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 3 4 6 7 8)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.tri 5 7 8) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 3 4 6 7 8)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 6))) (S3Tree.branch 14 (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.tri 5 7 8) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 3 4 6 7 8)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 6)) (S3Tree.degLo 6))))) (S3Tree.branch 5 (S3Tree.branch 6 (S3Tree.branch 12 (S3Tree.branch 8 (S3Tree.tri 5 6 8) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 13 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.branch 19 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 7 10)) (S3Tree.degLo 7))))) (S3Tree.ind5 3 4 6 7 8)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 2 4 5 7 10))) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 22 (S3Tree.degHi 10) (S3Tree.branch 23 (S3Tree.tri 4 9 11) (S3Tree.degLo 9)))) (S3Tree.branch 19 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 22 (S3Tree.ind5Full 0 6 8 9 11) (S3Tree.branch 23 (S3Tree.degHi 11) (S3Tree.degLo 9)))) (S3Tree.degLo 7))))) (S3Tree.ind5 3 4 6 7 8)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.degHi 5) (S3Tree.branch 17 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 22 (S3Tree.valid 9) (S3Tree.branch 23 (S3Tree.degHi 11) (S3Tree.degLo 9)))) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.ind5 3 4 6 7 8)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 6))))) (S3Tree.branch 12 (S3Tree.branch 13 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.degHi 9) (S3Tree.branch 18 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 2 4 5 6 10))) (S3Tree.branch 19 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 14 (S3Tree.degHi 6) (S3Tree.ind5 0 2 6 7 10))) (S3Tree.degLo 7))))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.branch 18 (S3Tree.degHi 7) (S3Tree.branch 20 (S3Tree.degHi 8) (S3Tree.branch 22 (S3Tree.degHi 9) (S3Tree.degLo 10))))) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 22 (S3Tree.degHi 10) (S3Tree.branch 23 (S3Tree.tri 4 9 11) (S3Tree.degLo 9)))) (S3Tree.branch 19 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 22 (S3Tree.valid 11) (S3Tree.branch 23 (S3Tree.degHi 11) (S3Tree.degLo 9)))) (S3Tree.degLo 7))))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 7 (S3Tree.branch 16 (S3Tree.degHi 8) (S3Tree.branch 17 (S3Tree.branch 10 (S3Tree.degHi 5) (S3Tree.ind5 2 4 5 6 10)) (S3Tree.branch 18 (S3Tree.branch 9 (S3Tree.degHi 5) (S3Tree.branch 22 (S3Tree.ind5Full 0 7 8 9 11) (S3Tree.branch 23 (S3Tree.degHi 11) (S3Tree.degLo 9)))) (S3Tree.ind5 0 2 6 7 10)))) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 6)))) (S3Tree.branch 13 (S3Tree.branch 14 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.tri 5 7 8) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 3 4 6 7 8)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.tri 5 7 8) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 3 4 6 7 8)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 6))) (S3Tree.branch 14 (S3Tree.branch 15 (S3Tree.branch 8 (S3Tree.branch 16 (S3Tree.branch 7 (S3Tree.tri 5 7 8) (S3Tree.ind5 2 4 5 6 7)) (S3Tree.ind5 3 4 6 7 8)) (S3Tree.ind5 1 3 4 5 8)) (S3Tree.degLo 6)) (S3Tree.degLo 6))))) (S3Tree.degLo 4))) (S3Tree.ind5 1 3 4 8 9))))

private def popcount (n m : Nat) : Nat :=
  (List.range n).countP fun i => m.testBit i

private def isIndH0 (m : Nat) : Bool :=
  (List.range 12).all fun i =>
    !(m.testBit i) || ((h0Adj12.getD i 0) &&& m == 0)

private def hasInd6 (chosen : List Nat) : Bool :=
  (List.range' 1 31).any fun yMask =>
    let need := 6 - popcount 5 yMask
    indAllH0List.any fun iMask =>
      popcount 12 iMask == need &&
      (List.range 5).all fun k =>
        !(yMask.testBit k) || ((chosen.getD k 0) &&& iMask == 0)

private def targetCnt : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2]

private def fitsCnt (cnt : List Nat) (m : Nat) : Bool :=
  (List.range 12).all fun i =>
    (cnt.getD i 0) + (if m.testBit i then 1 else 0) ≤ targetCnt.getD i 0

private def addCnt (cnt : List Nat) (m : Nat) : List Nat :=
  (List.range 12).map fun i =>
    (cnt.getD i 0) + (if m.testBit i then 1 else 0)

private def nonEmptyTails : List Nat → List (List Nat)
  | [] => []
  | x :: xs => (x :: xs) :: nonEmptyTails xs

private def check5Ext : Nat → List Nat → List Nat → List Nat → Bool
  | 0, _, cnt, chosen => if cnt == targetCnt then hasInd6 chosen else true
  | k + 1, cands, cnt, chosen =>
      (nonEmptyTails cands).all fun l =>
        match l with
        | [] => true
        | m :: rest =>
            if fitsCnt cnt m then check5Ext k (m :: rest) (addCnt cnt m) (m :: chosen)
            else true

private def checkSwapMasks : Bool :=
  (List.range 16).all fun bits =>
    (List.range 12).all fun a =>
      (List.range 12).all fun b =>
        isAdjYes (swapMasks16.getD bits 0) a b ==
          (h0Adj12.getD (swapVert bits a) 0).testBit (swapVert bits b)

private def checkInd4Complete : Bool :=
  (List.range 4096).all fun m =>
    if popcount 12 m == 4 && isIndH0 m then ind4H0List.contains m else true

private def checkIndAllValid : Bool :=
  indAllH0List.all fun m => m < 4096 && isIndH0 m

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem r36_cert_verify :
    checkS3Tree s3TreeCert 0 0 = true ∧
    checkSwapMasks = true ∧
    checkInd4Complete = true ∧
    checkIndAllValid = true ∧
    check5Ext 5 ind4H0List (List.replicate 12 0) [] = true := by
  exact ⟨by rfl, by rfl, by rfl, by rfl, by rfl⟩

private theorem r36_vertex_step {n m k : Nat} (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) (v : Fin n)
    (hm : ∀ Q : SimpleGraph (Fin m), Q.CliqueFree 3 → ∃ s, Q.IsNIndepSet k s)
    (hv : k + 1 ≤ (univ.filter (G.Adj v)).card ∨
      m + (univ.filter (G.Adj v)).card < n) :
    ∃ s, G.IsNIndepSet (k + 1) s := by
  classical
  rcases hv with hd | hd
  · obtain ⟨s, hs, hsc⟩ := Finset.exists_subset_card_eq hd
    refine ⟨s, ⟨?_, hsc⟩⟩
    intro x hx y hy _ hxy
    exact hG {v, x, y} (SimpleGraph.is3Clique_iff.mpr
      ⟨v, x, y, (Finset.mem_filter.mp (hs hx)).2,
        (Finset.mem_filter.mp (hs hy)).2, hxy, rfl⟩)
  · let A : Finset (Fin n) := univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)
    let N : Finset (Fin n) := univ.filter (G.Adj v)
    change m + N.card < n at hd
    have hdisj : Disjoint A N := by
      rw [Finset.disjoint_left]
      intro u huA huN
      exact (Finset.mem_filter.mp huA).2.2 (Finset.mem_filter.mp huN).2
    have hnot : v ∉ A ∪ N := by
      intro h
      rcases Finset.mem_union.mp h with h | h
      · exact (Finset.mem_filter.mp h).2.1 rfl
      · exact G.irrefl (Finset.mem_filter.mp h).2
    have hU : insert v (A ∪ N) = univ := by
      ext u
      simp only [A, N, Finset.mem_insert, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and, iff_true]
      by_cases huv : u = v
      · exact Or.inl huv
      · by_cases h : G.Adj v u
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl ⟨huv, h⟩)
    have hc := congrArg Finset.card hU
    rw [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdisj,
      Finset.card_univ, Fintype.card_fin] at hc
    have hmA : m ≤ A.card := by omega
    obtain ⟨T, hTA, hTc⟩ := Finset.exists_subset_card_eq hmA
    let e : Fin m ≃ T := (Fintype.equivFinOfCardEq (by simp [hTc])).symm
    let Q : SimpleGraph (Fin m) :=
      { Adj := fun i j => G.Adj (e i).val (e j).val
        symm := ⟨fun _ _ h => h.symm⟩
        loopless := ⟨fun _ h => G.irrefl h⟩ }
    have hQ : Q.CliqueFree 3 := by
      intro t ht
      obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.mp ht
      exact hG {(e a).val, (e b).val, (e c).val}
        (SimpleGraph.is3Clique_iff.mpr ⟨(e a).val, (e b).val, (e c).val, hab, hac, hbc, rfl⟩)
    obtain ⟨I, hI⟩ := hm Q hQ
    let S := I.image (fun i => (e i).val)
    have hmem (i : Fin m) : (e i).val ≠ v ∧ ¬ G.Adj v (e i).val :=
      (Finset.mem_filter.mp (hTA (e i).property)).2
    have hvS : v ∉ S := by
      intro hv
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
      exact (hmem i).1 hi
    have hSc : S.card = k := by
      change (I.image (fun i => (e i).val)).card = k
      rw [Finset.card_image_of_injective _ (fun i j hij => e.injective (Subtype.ext hij)), hI.card_eq]
    refine ⟨insert v S, ⟨?_, by rw [Finset.card_insert_of_notMem hvS, hSc]⟩⟩
    intro x hx y hy hxy hadj
    simp only [Finset.mem_coe, Finset.mem_insert] at hx hy
    rcases hx with rfl | hxS <;> rcases hy with rfl | hyS
    · exact hxy rfl
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyS
      exact (hmem j).2 hadj
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxS
      exact (hmem i).2 hadj.symm
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxS
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hyS
      exact hI.isIndepSet hi hj (fun h => hxy (by rw [h])) hadj

private theorem r36_no_cubic_nine (G : SimpleGraph (Fin 9)) :
    ¬ (∀ v : Fin 9, (univ.filter (G.Adj v)).card = 3) := by
  intro h
  have hdegree : ∑ v : Fin 9, G.degree v = 27 := by
    simp [SimpleGraph.degree, SimpleGraph.neighborFinset, h]
  have hhand : ∑ v : Fin 9, G.degree v = 2 * G.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  omega

private theorem r36_eight_internal_min (G : SimpleGraph (Fin 8))
    (hG : G.CliqueFree 3) (hno4 : ∀ s, ¬ G.IsNIndepSet 4 s)
    (v : Fin 8) (A : Finset (Fin 8)) (hA : A.card = 5)
    (hAv : ∀ x ∈ A, x ≠ v ∧ ¬ G.Adj v x)
    (w : Fin 8) (hw : w ∈ A) :
    2 ≤ (A.filter (G.Adj w)).card := by
  classical
  by_contra hgoal
  have hsmall : (A.filter (G.Adj w)).card ≤ 1 := by omega
  let C : Finset (Fin 8) := A.filter (G.Adj w)
  let B : Finset (Fin 8) := A.filter (fun x => x ≠ w ∧ ¬ G.Adj w x)
  have hwC : w ∉ C := by
    intro h
    have hh : w ∈ A.filter (G.Adj w) := by simpa [C] using h
    exact G.irrefl (Finset.mem_filter.mp hh).2
  have hcover : A ⊆ insert w C ∪ B := by
    intro x hx
    by_cases hEq : x = w
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_insert.mpr (Or.inl hEq)))
    · by_cases hadj : G.Adj w x
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_insert.mpr (Or.inr
            (Finset.mem_filter.mpr ⟨hx, hadj⟩))))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨hx, hEq, hadj⟩))
  have hcard : A.card ≤ C.card + 1 + B.card := by
    calc
      A.card ≤ (insert w C ∪ B).card := Finset.card_le_card hcover
      _ ≤ (insert w C).card + B.card := Finset.card_union_le _ _
      _ = C.card + 1 + B.card := by
        rw [Finset.card_insert_of_notMem hwC]
  have hBcard : 3 ≤ B.card := by
    have hsmall' : C.card ≤ 1 := by simpa [C] using hsmall
    omega
  obtain ⟨x, hxB⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
  let D := B.erase x
  have hDcard : 2 ≤ D.card := by
    dsimp [D]
    rw [Finset.card_erase_of_mem hxB]
    omega
  obtain ⟨y, hyD⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
  have hyD' : y ∈ B.erase x := by simpa [D] using hyD
  rcases Finset.mem_erase.mp hyD' with ⟨hyx, hyB⟩
  let E := D.erase y
  have hEcard : E.card = D.card - 1 := by
    dsimp [E]
    rw [Finset.card_erase_of_mem hyD]
  obtain ⟨z, hzE⟩ := Finset.card_pos.mp (by omega : 0 < E.card)
  have hzE' : z ∈ (B.erase x).erase y := by simpa [E, D] using hzE
  rcases Finset.mem_erase.mp hzE' with ⟨hzy, hzD⟩
  rcases Finset.mem_erase.mp hzD with ⟨hzx, hzB⟩
  have hpair : ∃ a b : Fin 8, a ∈ B ∧ b ∈ B ∧ a ≠ b ∧ ¬ G.Adj a b := by
    by_cases hxy : G.Adj x y
    · by_cases hxz : G.Adj x z
      · by_cases hyz : G.Adj y z
        · exact (hG {x, y, z} (SimpleGraph.is3Clique_iff.mpr
            ⟨x, y, z, hxy, hxz, hyz, rfl⟩)).elim
        · exact ⟨y, z, hyB, hzB, Ne.symm hzy, hyz⟩
      · exact ⟨x, z, hxB, hzB, Ne.symm hzx, hxz⟩
    · exact ⟨x, y, hxB, hyB, Ne.symm hyx, hxy⟩
  obtain ⟨p, q, hpB, hqB, hpqne, hnpq⟩ := hpair
  have hpA : p ∈ A := (Finset.mem_filter.mp hpB).1
  have hqA : q ∈ A := (Finset.mem_filter.mp hqB).1
  have hvw : ¬ G.Adj v w := (hAv w hw).2
  have hvp : ¬ G.Adj v p := (hAv p hpA).2
  have hvq : ¬ G.Adj v q := (hAv q hqA).2
  have hwp : ¬ G.Adj w p := (Finset.mem_filter.mp hpB).2.2
  have hwq : ¬ G.Adj w q := (Finset.mem_filter.mp hqB).2.2
  have hnqp : ¬ G.Adj q p := fun h => hnpq h.symm
  have hwv : ¬ G.Adj w v := fun h => hvw h.symm
  have hpv : ¬ G.Adj p v := fun h => hvp h.symm
  have hqv : ¬ G.Adj q v := fun h => hvq h.symm
  have hpw : ¬ G.Adj p w := fun h => hwp h.symm
  have hqw : ¬ G.Adj q w := fun h => hwq h.symm
  have hvwne : v ≠ w := Ne.symm (hAv w hw).1
  have hvpne : v ≠ p := Ne.symm (hAv p hpA).1
  have hvqne : v ≠ q := Ne.symm (hAv q hqA).1
  have hwpne : w ≠ p := Ne.symm (Finset.mem_filter.mp hpB).2.1
  have hwqne : w ≠ q := Ne.symm (Finset.mem_filter.mp hqB).2.1
  let S : Finset (Fin 8) := insert v (insert w (insert p ({q} : Finset (Fin 8))))
  have hInd : G.IsIndepSet (S : Set (Fin 8)) := by
    intro a ha b hb hab hadj
    simp only [S, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl <;> simp_all
  have hvnot : v ∉ insert w (insert p ({q} : Finset (Fin 8))) := by
    simp [hvwne, hvpne, hvqne]
  have hwpqnot : w ∉ insert p ({q} : Finset (Fin 8)) := by
    simp [hwpne, hwqne]
  have hpnot : p ∉ ({q} : Finset (Fin 8)) := by
    simp [hpqne]
  have hScard : S.card = 4 := by
    dsimp [S]
    rw [Finset.card_insert_of_notMem hvnot,
      Finset.card_insert_of_notMem hwpqnot,
      Finset.card_insert_of_notMem hpnot, Finset.card_singleton]
  exact hno4 S ⟨hInd, hScard⟩

private theorem r36_eight_cross_targets (G : SimpleGraph (Fin 8))
    (hG : G.CliqueFree 3) (hno4 : ∀ s, ¬ G.IsNIndepSet 4 s)
    (A N : Finset (Fin 8)) (hA : A.card = 5) (hN : N.card = 2)
    (hdisj : Disjoint A N) (hNI : G.IsIndepSet (N : Set (Fin 8))) :
    3 ≤ (A.filter (fun w => ∃ z ∈ N, G.Adj w z)).card := by
  classical
  let T : Finset (Fin 8) := A.filter (fun w => ∃ z ∈ N, G.Adj w z)
  let B : Finset (Fin 8) := A.filter (fun w => ¬ ∃ z ∈ N, G.Adj w z)
  by_contra hgoal
  have hT : T.card ≤ 2 := by
    change ¬ 3 ≤ T.card at hgoal
    omega
  have hcover : A ⊆ B ∪ T := by
    intro w hw
    by_cases h : ∃ z ∈ N, G.Adj w z
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hw, h⟩))
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hw, h⟩))
  have hAB : A.card ≤ B.card + T.card := by
    calc
      A.card ≤ (B ∪ T).card := Finset.card_le_card hcover
      _ ≤ B.card + T.card := Finset.card_union_le _ _
  have hB : 3 ≤ B.card := by
    omega
  obtain ⟨x, hxB⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
  let D : Finset (Fin 8) := B.erase x
  have hD : 2 ≤ D.card := by
    dsimp [D]
    rw [Finset.card_erase_of_mem hxB]
    omega
  obtain ⟨y, hyD⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
  have hyD' : y ∈ B.erase x := by
    simpa [D] using hyD
  rcases Finset.mem_erase.mp hyD' with ⟨hyx, hyB⟩
  let E : Finset (Fin 8) := D.erase y
  have hEcard : E.card = D.card - 1 := by
    dsimp [E]
    rw [Finset.card_erase_of_mem hyD]
  obtain ⟨z, hzE⟩ := Finset.card_pos.mp (by omega : 0 < E.card)
  have hzE' : z ∈ (B.erase x).erase y := by
    simpa [E, D] using hzE
  rcases Finset.mem_erase.mp hzE' with ⟨hzy, hzD⟩
  rcases Finset.mem_erase.mp hzD with ⟨hzx, hzB⟩
  have hpair : ∃ p q : Fin 8, p ∈ B ∧ q ∈ B ∧ p ≠ q ∧ ¬ G.Adj p q := by
    by_cases hxy : G.Adj x y
    · by_cases hxz : G.Adj x z
      · by_cases hyz : G.Adj y z
        · exact (hG {x, y, z} (SimpleGraph.is3Clique_iff.mpr
            ⟨x, y, z, hxy, hxz, hyz, rfl⟩)).elim
        · exact ⟨y, z, hyB, hzB, Ne.symm hzy, hyz⟩
      · exact ⟨x, z, hxB, hzB, Ne.symm hzx, hxz⟩
    · exact ⟨x, y, hxB, hyB, Ne.symm hyx, hxy⟩
  obtain ⟨p, q, hpB, hqB, hpqne, hpq⟩ := hpair
  have hpA : p ∈ A := (Finset.mem_filter.mp hpB).1
  have hqA : q ∈ A := (Finset.mem_filter.mp hqB).1
  have hpNo : ¬ ∃ z ∈ N, G.Adj p z := (Finset.mem_filter.mp hpB).2
  have hqNo : ¬ ∃ z ∈ N, G.Adj q z := (Finset.mem_filter.mp hqB).2
  have hpN : ∀ z ∈ N, ¬ G.Adj p z := by
    intro z hz hadj
    exact hpNo ⟨z, hz, hadj⟩
  have hqN : ∀ z ∈ N, ¬ G.Adj q z := by
    intro z hz hadj
    exact hqNo ⟨z, hz, hadj⟩
  have hpNotN : p ∉ N := by
    intro hp
    exact (Finset.disjoint_left.mp hdisj) hpA hp
  have hqNotN : q ∉ N := by
    intro hq
    exact (Finset.disjoint_left.mp hdisj) hqA hq
  let S : Finset (Fin 8) := insert p (insert q N)
  have hInd : G.IsIndepSet (S : Set (Fin 8)) := by
    intro a ha b hb hab hadj
    simp only [S, Finset.mem_coe, Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact hab rfl
      · rcases hb with rfl | hb
        · exact hpq hadj
        · exact hpN _ hb hadj
    · rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact hpq hadj.symm
        · rcases hb with rfl | hb
          · exact hab rfl
          · exact hqN _ hb hadj
      · rcases hb with rfl | hb
        · exact hpN _ ha hadj.symm
        · rcases hb with rfl | hb
          · exact hqN _ ha hadj.symm
          · exact hNI ha hb hab hadj
  have hpNotInner : p ∉ insert q N := by
    simp [hpqne, hpNotN]
  have hScard : S.card = 4 := by
    dsimp [S]
    rw [Finset.card_insert_of_notMem hpNotInner,
      Finset.card_insert_of_notMem hqNotN]
    simp [hN]
  exact hno4 S ⟨hInd, hScard⟩

private theorem r36_eight_degree_sum (G : SimpleGraph (Fin 8))
    (hG : G.CliqueFree 3) (hno4 : ∀ s, ¬ G.IsNIndepSet 4 s)
    (hdeg : ∀ v : Fin 8, 2 ≤ (univ.filter (G.Adj v)).card ∧
      (univ.filter (G.Adj v)).card ≤ 3) :
    20 ≤ ∑ v : Fin 8, (univ.filter (G.Adj v)).card := by
  classical
  let d (x : Fin 8) : Nat := (univ.filter (G.Adj x)).card
  have hhigh : 3 ≤ (univ.filter (fun x : Fin 8 => 3 ≤ d x)).card := by
    by_cases hex : ∃ v : Fin 8, d v = 2
    · obtain ⟨v, hv⟩ := hex
      let A : Finset (Fin 8) := univ.filter (fun x => x ≠ v ∧ ¬ G.Adj v x)
      let N : Finset (Fin 8) := univ.filter (G.Adj v)
      have hN : N.card = 2 := hv
      have hAmem (x : Fin 8) (hx : x ∈ A) : x ≠ v ∧ ¬ G.Adj v x :=
        (Finset.mem_filter.mp hx).2
      have hNmem (x : Fin 8) (hx : x ∈ N) : G.Adj v x :=
        (Finset.mem_filter.mp hx).2
      have hdisj : Disjoint A N := by
        rw [Finset.disjoint_left]
        intro x hxA hxN
        exact (hAmem x hxA).2 (hNmem x hxN)
      have hvout : v ∉ A ∪ N := by
        intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact (hAmem v hx).1 rfl
        · exact G.irrefl (hNmem v hx)
      have hU : insert v (A ∪ N) = univ := by
        ext x
        simp only [A, N, Finset.mem_insert, Finset.mem_union, Finset.mem_filter,
          Finset.mem_univ, true_and, iff_true]
        by_cases hx : x = v
        · exact Or.inl hx
        · by_cases he : G.Adj v x
          · exact Or.inr (Or.inr he)
          · exact Or.inr (Or.inl ⟨hx, he⟩)
      have hcard := congrArg Finset.card hU
      rw [Finset.card_insert_of_notMem hvout, Finset.card_union_of_disjoint hdisj,
        Finset.card_univ, Fintype.card_fin] at hcard
      have hA : A.card = 5 := by omega
      have hNI : G.IsIndepSet (N : Set (Fin 8)) := by
        intro a ha b hb _ hab
        exact hG {v, a, b} (SimpleGraph.is3Clique_iff.mpr
          ⟨v, a, b, hNmem a ha, hNmem b hb, hab, rfl⟩)
      have hcross := r36_eight_cross_targets G hG hno4 A N hA hN hdisj hNI
      refine le_trans hcross (Finset.card_le_card ?_)
      intro w hw
      obtain ⟨hwA, z, hzN, hwz⟩ := Finset.mem_filter.mp hw
      have hinside := r36_eight_internal_min G hG hno4 v A hA hAmem w hwA
      have hzout : z ∉ A.filter (G.Adj w) := by
        intro hz
        exact (Finset.disjoint_left.mp hdisj) (Finset.mem_filter.mp hz).1 hzN
      have hsub : insert z (A.filter (G.Adj w)) ⊆ univ.filter (G.Adj w) := by
        intro x hx
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hwz
        · exact (Finset.mem_filter.mp hx).2
      have hle := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hzout] at hle
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      change 3 ≤ (univ.filter (G.Adj w)).card
      omega
    · have hall (x : Fin 8) : 3 ≤ d x := by
        have hlo : 2 ≤ d x := (hdeg x).1
        have hne : d x ≠ 2 := fun hx => hex ⟨x, hx⟩
        omega
      simp [hall]
  have hpoint (x : Fin 8) : 2 + (if 3 ≤ d x then 1 else 0) ≤ d x := by
    have hlo : 2 ≤ d x := (hdeg x).1
    split <;> omega
  have hcount : (∑ x : Fin 8, (if 3 ≤ d x then (1 : Nat) else 0)) =
      (univ.filter (fun x : Fin 8 => 3 ≤ d x)).card := by
    rw [← Finset.sum_filter] <;> simp
  have hconst : (∑ _x : Fin 8, (2 : Nat)) = 16 := by simp
  have hle := Finset.sum_le_sum (s := (univ : Finset (Fin 8)))
    (fun x _ => hpoint x)
  rw [Finset.sum_add_distrib, hconst, hcount] at hle
  have hd_eq (x : Fin 8) : G.degree x = d x := by
    have hn : G.neighborFinset x = univ.filter (G.Adj x) := by
      ext y
      simp
    change (G.neighborFinset x).card = (univ.filter (G.Adj x)).card
    rw [hn]
  have heven : (∑ x : Fin 8, d x) = 2 * G.edgeFinset.card := by
    simpa only [hd_eq] using SimpleGraph.sum_degrees_eq_twice_card_edges G
  change 20 ≤ ∑ x : Fin 8, d x
  omega

private lemma r36_small_ramsey :
    (∀ G : SimpleGraph (Fin 6), G.CliqueFree 3 → ∃ s, G.IsNIndepSet 3 s) ∧
    (∀ G : SimpleGraph (Fin 9), G.CliqueFree 3 → ∃ s, G.IsNIndepSet 4 s) ∧
    (∀ G : SimpleGraph (Fin 14), G.CliqueFree 3 → ∃ s, G.IsNIndepSet 5 s) ∧
    (∀ G : SimpleGraph (Fin 8), G.CliqueFree 3 → (∀ s, ¬ G.IsNIndepSet 4 s) →
      20 ≤ ∑ v : Fin 8, (univ.filter (G.Adj v)).card) := by
  classical
  have hThree : ∀ Q : SimpleGraph (Fin 3), Q.CliqueFree 3 → ∃ s, Q.IsNIndepSet 2 s := by
    intro Q hQ
    have mkPair (a b : Fin 3) (hab : a ≠ b) (hn : ¬ Q.Adj a b) :
        ∃ s, Q.IsNIndepSet 2 s := by
      refine ⟨{a, b}, ⟨?_, ?_⟩⟩
      · intro x hx y hy hxy hEdge
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact hxy rfl
        · exact hn hEdge
        · exact hn hEdge.symm
        · exact hxy rfl
      · have ha : a ∉ ({b} : Finset (Fin 3)) := by simpa using hab
        rw [Finset.card_insert_of_notMem ha, Finset.card_singleton]
    by_cases h01 : Q.Adj 0 1
    · by_cases h02 : Q.Adj 0 2
      · by_cases h12 : Q.Adj 1 2
        · exact (hQ {0, 1, 2} (SimpleGraph.is3Clique_iff.mpr
            ⟨0, 1, 2, h01, h02, h12, rfl⟩)).elim
        · exact mkPair 1 2 (by decide) h12
      · exact mkPair 0 2 (by decide) h02
    · exact mkPair 0 1 (by decide) h01
  have hSix : ∀ G : SimpleGraph (Fin 6), G.CliqueFree 3 → ∃ s, G.IsNIndepSet 3 s := by
    intro G hG
    refine r36_vertex_step G hG 0 hThree ?_
    change 3 ≤ (univ.filter (G.Adj (0 : Fin 6))).card ∨
      3 + (univ.filter (G.Adj (0 : Fin 6))).card < 6
    omega
  have hNine : ∀ G : SimpleGraph (Fin 9), G.CliqueFree 3 → ∃ s, G.IsNIndepSet 4 s := by
    intro G hG
    by_cases he : ∀ v : Fin 9, (univ.filter (G.Adj v)).card = 3
    · exact (r36_no_cubic_nine G he).elim
    · have hv : ∃ v : Fin 9, (univ.filter (G.Adj v)).card ≠ 3 := by
        by_contra hn
        apply he
        intro v
        by_contra hv
        exact hn ⟨v, hv⟩
      obtain ⟨v, hv⟩ := hv
      refine r36_vertex_step G hG v hSix ?_
      change 4 ≤ (univ.filter (G.Adj v)).card ∨ 6 + (univ.filter (G.Adj v)).card < 9
      omega
  refine ⟨hSix, hNine, ?_, ?_⟩
  · intro G hG
    refine r36_vertex_step G hG 0 hNine ?_
    change 5 ≤ (univ.filter (G.Adj (0 : Fin 14))).card ∨
      9 + (univ.filter (G.Adj (0 : Fin 14))).card < 14
    omega
  · intro G hG hno4
    apply r36_eight_degree_sum G hG hno4
    intro v
    by_contra hn
    have hv : 4 ≤ (univ.filter (G.Adj v)).card ∨ 6 + (univ.filter (G.Adj v)).card < 8 := by
      omega
    obtain ⟨s, hs⟩ := r36_vertex_step G hG v hSix hv
    exact hno4 s hs

private lemma r36_no_deg4 (G : SimpleGraph (Fin 18)) (hG : G.CliqueFree 3)
    (hno6 : ∀ s, ¬ G.IsNIndepSet 6 s)
    (hdeg : ∀ v : Fin 18, 4 ≤ (univ.filter (G.Adj v)).card ∧ (univ.filter (G.Adj v)).card ≤ 5)
    (hv : ∃ v : Fin 18, (univ.filter (G.Adj v)).card = 4) : False := by
  obtain ⟨v, hv⟩ := hv
  let N : Finset (Fin 18) := univ.filter (G.Adj v)
  let A : Finset (Fin 18) := univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)
  have hN : N.card = 4 := hv
  have hdisj : Disjoint A N := by
    rw [Finset.disjoint_left]
    intro u huA huN
    exact (Finset.mem_filter.mp huA).2.2 (Finset.mem_filter.mp huN).2
  have hvout : v ∉ A ∪ N := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact (Finset.mem_filter.mp h).2.1 rfl
    · exact G.irrefl (Finset.mem_filter.mp h).2
  have hU : insert v (A ∪ N) = univ := by
    ext u
    simp only [A, N, Finset.mem_insert, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    by_cases huv : u = v
    · exact Or.inl huv
    · by_cases h : G.Adj v u
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl ⟨huv, h⟩)
  have hcard := congrArg Finset.card hU
  rw [Finset.card_insert_of_notMem hvout, Finset.card_union_of_disjoint hdisj,
    Finset.card_univ, Fintype.card_fin] at hcard
  have hA : A.card = 13 := by omega
  have hA_mem (x : Fin 18) (hx : x ∈ A) : x ≠ v ∧ ¬ G.Adj v x :=
    (Finset.mem_filter.mp hx).2
  have hN_mem (x : Fin 18) (hx : x ∈ N) : G.Adj v x :=
    (Finset.mem_filter.mp hx).2
  have hnoInd5 (S : Finset (Fin 18)) (hSA : S ⊆ A)
      (hSi : G.IsIndepSet (S : Set (Fin 18))) (hSc : S.card = 5) : False := by
    let U : Finset (Fin 18) := insert v S
    have hvS : v ∉ S := by
      intro hvS
      exact (hA_mem v (hSA hvS)).1 rfl
    have hUi : G.IsIndepSet (U : Set (Fin 18)) := by
      intro a ha b hb hab hadj
      simp only [U, Finset.mem_coe, Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact hab rfl
      · exact (hA_mem b (hSA hb)).2 hadj
      · exact (hA_mem a (hSA ha)).2 hadj.symm
      · exact hSi ha hb hab hadj
    apply hno6 U
    refine ⟨hUi, ?_⟩
    dsimp [U]
    rw [Finset.card_insert_of_notMem hvS, hSc]
  have hNind : G.IsIndepSet (N : Set (Fin 18)) := by
    intro a ha b hb hab hadj
    exact hG {v, a, b} (SimpleGraph.is3Clique_iff.mpr
      ⟨v, a, b, hN_mem a ha, hN_mem b hb, hadj, rfl⟩)
  have hinternal (x : Fin 18) (hx : x ∈ A) :
      4 ≤ (A.filter (G.Adj x)).card := by
    let C : Finset (Fin 18) := A.filter (G.Adj x)
    let B : Finset (Fin 18) := A.filter (fun y => y ≠ x ∧ ¬ G.Adj x y)
    have hCind : G.IsIndepSet (C : Set (Fin 18)) := by
      intro a ha b hb hab hadj
      exact hG {x, a, b} (SimpleGraph.is3Clique_iff.mpr
        ⟨x, a, b, (Finset.mem_filter.mp ha).2,
          (Finset.mem_filter.mp hb).2, hadj, rfl⟩)
    have hCcard : C.card ≤ 4 := by
      by_contra hn
      have hfive : 5 ≤ C.card := by omega
      obtain ⟨T, hTC, hTc⟩ := Finset.exists_subset_card_eq hfive
      have hTi : G.IsIndepSet (T : Set (Fin 18)) := by
        intro a ha b hb hab hadj
        exact hCind (hTC ha) (hTC hb) hab hadj
      exact hnoInd5 T
        (hTC.trans (fun _ hy => (Finset.mem_filter.mp hy).1)) hTi hTc
    have hcover : A ⊆ insert x C ∪ B := by
      intro y hy
      by_cases hxy : y = x
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_insert.mpr (Or.inl hxy)))
      · by_cases hAdj : G.Adj x y
        · exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_insert.mpr (Or.inr
              (Finset.mem_filter.mpr ⟨hy, hAdj⟩))))
        · exact Finset.mem_union.mpr
            (Or.inr (Finset.mem_filter.mpr ⟨hy, hxy, hAdj⟩))
    have hxC : x ∉ C := by
      intro h
      exact G.irrefl (Finset.mem_filter.mp h).2
    have hineq : A.card ≤ C.card + 1 + B.card := by
      calc
        A.card ≤ (insert x C ∪ B).card := Finset.card_le_card hcover
        _ ≤ (insert x C).card + B.card := Finset.card_union_le _ _
        _ = C.card + 1 + B.card := by
          rw [Finset.card_insert_of_notMem hxC]
    by_contra hn
    have hCne : ¬ 4 ≤ C.card := hn
    have hCsmall : C.card ≤ 3 := by omega
    have hineq' := hineq
    rw [hA] at hineq'
    have hCB : 12 ≤ C.card + B.card := by omega
    have hB : 9 ≤ B.card := by omega
    obtain ⟨T, hTB, hTc⟩ := Finset.exists_subset_card_eq hB
    let e : Fin 9 ≃ T := (Fintype.equivFinOfCardEq (by simp [hTc])).symm
    let Q : SimpleGraph (Fin 9) :=
      { Adj := fun i j => G.Adj (e i).val (e j).val
        symm := ⟨fun _ _ h => h.symm⟩
        loopless := ⟨fun _ h => G.irrefl h⟩ }
    have hQ : Q.CliqueFree 3 := by
      intro t ht
      obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.mp ht
      exact hG {(e a).val, (e b).val, (e c).val}
        (SimpleGraph.is3Clique_iff.mpr
          ⟨(e a).val, (e b).val, (e c).val, hab, hac, hbc, rfl⟩)
    obtain ⟨I, hI⟩ := r36_small_ramsey.2.1 Q hQ
    let S : Finset (Fin 18) := I.image (fun i => (e i).val)
    have hSB : S ⊆ B := by
      intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact hTB (e i).property
    have hSi : G.IsIndepSet (S : Set (Fin 18)) := by
      intro a ha b hb hab hadj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      exact hI.isIndepSet hi hj (fun h => hab (by rw [h])) hadj
    have hSc : S.card = 4 := by
      rw [Finset.card_image_of_injective _
        (fun i j hij => e.injective (Subtype.ext hij)), hI.card_eq]
    have hxS : x ∉ S := by
      intro hxS
      exact (Finset.mem_filter.mp (hSB hxS)).2.1 rfl
    have hXS : G.IsIndepSet ((insert x S : Finset (Fin 18)) : Set (Fin 18)) := by
      intro a ha b hb hab hadj
      simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact hab rfl
      · exact (Finset.mem_filter.mp (hSB hb)).2.2 hadj
      · exact (Finset.mem_filter.mp (hSB ha)).2.2 hadj.symm
      · exact hSi ha hb hab hadj
    have hXsub : insert x S ⊆ A := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact (Finset.mem_filter.mp (hSB hy)).1
    have hXcard : (insert x S).card = 5 := by
      rw [Finset.card_insert_of_notMem hxS, hSc]
    exact hnoInd5 (insert x S) hXsub hXS hXcard
  have hinternal_eq (x : Fin 18) (hx : x ∈ A) :
      (A.filter (G.Adj x)).card = 4 := by
    have hlow := hinternal x hx
    have hhi : (A.filter (G.Adj x)).card ≤ 4 := by
      by_contra hn
      have hfive : 5 ≤ (A.filter (G.Adj x)).card := by omega
      obtain ⟨T, hTC, hTc⟩ := Finset.exists_subset_card_eq hfive
      have hTi : G.IsIndepSet (T : Set (Fin 18)) := by
        intro a ha b hb hab hadj
        exact hG {x, a, b} (SimpleGraph.is3Clique_iff.mpr
          ⟨x, a, b, (Finset.mem_filter.mp (hTC ha)).2,
            (Finset.mem_filter.mp (hTC hb)).2, hadj, rfl⟩)
      exact hnoInd5 T
        (hTC.trans (fun _ hy => (Finset.mem_filter.mp hy).1)) hTi hTc
    omega
  have hcross (a : Fin 18) (ha : a ∈ A) :
      (N.filter (G.Adj a)).card ≤ 1 := by
    let C : Finset (Fin 18) := A.filter (G.Adj a)
    let E : Finset (Fin 18) := N.filter (G.Adj a)
    let D : Finset (Fin 18) := univ.filter (G.Adj a)
    have hdisjCE : Disjoint C E := by
      rw [Finset.disjoint_left]
      intro y hyC hyE
      exact (Finset.disjoint_left.mp hdisj)
        (Finset.mem_filter.mp hyC).1 (Finset.mem_filter.mp hyE).1
    have hsub : C ∪ E ⊆ D := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisjCE] at hle
    have hCe : C.card = 4 := hinternal_eq a ha
    have hDl : D.card ≤ 5 := (hdeg a).2
    change C.card + E.card ≤ D.card at hle
    change E.card ≤ 1
    omega
  obtain ⟨w, hwN⟩ := Finset.card_pos.mp (by omega : 0 < N.card)
  have hvw : G.Adj v w := hN_mem w hwN
  let Cw : Finset (Fin 18) := A.filter (G.Adj w)
  have hNbrSub : (univ.filter (G.Adj w)) ⊆ insert v Cw := by
    intro y hy
    have hwy : G.Adj w y := (Finset.mem_filter.mp hy).2
    by_cases hyv : y = v
    · exact Finset.mem_insert.mpr (Or.inl hyv)
    · have hnot : ¬ G.Adj v y := by
        intro hvy
        exact hG {v, w, y} (SimpleGraph.is3Clique_iff.mpr
          ⟨v, w, y, hvw, hvy, hwy, rfl⟩)
      exact Finset.mem_insert.mpr (Or.inr
        (Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, ⟨Ne.symm (Ne.symm hyv), hnot⟩⟩, hwy⟩))
  have hvCw : v ∉ Cw := by
    intro hvCw
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hvCw).1).2.1 rfl
  have hCwcard : 3 ≤ Cw.card := by
    have hle := Finset.card_le_card hNbrSub
    rw [Finset.card_insert_of_notMem hvCw] at hle
    have hlow := (hdeg w).1
    change 4 ≤ (univ.filter (G.Adj w)).card at hlow
    omega
  have hCwind : G.IsIndepSet (Cw : Set (Fin 18)) := by
    intro a ha b hb hab hadj
    exact hG {w, a, b} (SimpleGraph.is3Clique_iff.mpr
      ⟨w, a, b, (Finset.mem_filter.mp ha).2,
        (Finset.mem_filter.mp hb).2, hadj, rfl⟩)
  obtain ⟨T, hTCw, hTc⟩ := Finset.exists_subset_card_eq hCwcard
  let D : Finset (Fin 18) := N.erase w
  have hDcard : D.card = 3 := by
    dsimp [D]
    rw [Finset.card_erase_of_mem hwN, hN]
  have hdisjTD : Disjoint T D := by
    rw [Finset.disjoint_left]
    intro y hyT hyD
    exact (Finset.disjoint_left.mp hdisj)
      ((Finset.mem_filter.mp (hTCw hyT)).1)
      (Finset.mem_erase.mp hyD).2
  have hTind : G.IsIndepSet (T : Set (Fin 18)) := by
    intro a ha b hb hab hadj
    exact hCwind (hTCw ha) (hTCw hb) hab hadj
  have hcrossFalse (a b : Fin 18) (ha : a ∈ T) (hb : b ∈ D)
      (hab : G.Adj a b) : False := by
    have haA : a ∈ A := (Finset.mem_filter.mp (hTCw ha)).1
    have hbN : b ∈ N := (Finset.mem_erase.mp hb).2
    have haw : G.Adj a w := ((Finset.mem_filter.mp (hTCw ha)).2).symm
    let E : Finset (Fin 18) := N.filter (G.Adj a)
    have hwE : w ∈ E := Finset.mem_filter.mpr ⟨hwN, haw⟩
    have hbE : b ∈ E := Finset.mem_filter.mpr ⟨hbN, hab⟩
    have hwb : b ≠ w := (Finset.mem_erase.mp hb).1
    have hpairs : insert w ({b} : Finset (Fin 18)) ⊆ E := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hwE
      · have : y = b := Finset.mem_singleton.mp hy
        subst y
        exact hbE
    have hpairsCard : (insert w ({b} : Finset (Fin 18))).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hwb]),
        Finset.card_singleton]
    have htwo : 2 ≤ E.card := by
      calc
        2 = (insert w ({b} : Finset (Fin 18))).card := hpairsCard.symm
        _ ≤ E.card := Finset.card_le_card hpairs
    have hone := hcross a haA
    change E.card ≤ 1 at hone
    omega
  let U : Finset (Fin 18) := T ∪ D
  have hUi : G.IsIndepSet (U : Set (Fin 18)) := by
    intro a ha b hb hab hadj
    simp only [Finset.mem_coe, U, Finset.mem_union] at ha hb
    rcases ha with haT | haD
    · rcases hb with hbT | hbD
      · exact hTind haT hbT hab hadj
      · exact (hcrossFalse a b haT hbD hadj).elim
    · rcases hb with hbT | hbD
      · exact (hcrossFalse b a hbT haD hadj.symm).elim
      · exact hNind (Finset.mem_erase.mp haD).2
          (Finset.mem_erase.mp hbD).2 hab hadj
  have hUcard : U.card = 6 := by
    dsimp [U]
    rw [Finset.card_union_of_disjoint hdisjTD, hTc, hDcard]
  exact hno6 U ⟨hUi, hUcard⟩

private theorem r36_extract_antineighborhood (G : SimpleGraph (Fin 18))
    (hG : G.CliqueFree 3) (hno6 : ∀ s, ¬ G.IsNIndepSet 6 s)
    (h5 : ∀ v : Fin 18, (univ.filter (G.Adj v)).card = 5) :
    ∃ (H : SimpleGraph (Fin 12)) (M : Fin 5 → Finset (Fin 12)),
      H.CliqueFree 3 ∧ (∀ s, ¬ H.IsNIndepSet 5 s) ∧
      (∀ y : Fin 5, H.IsNIndepSet 4 (M y)) ∧
      (∀ w : Fin 12, (univ.filter (H.Adj w)).card +
        (univ.filter (fun y : Fin 5 => w ∈ M y)).card = 5) ∧
      (∀ (Y : Finset (Fin 5)) (I : Finset (Fin 12)),
        Y.Nonempty → H.IsIndepSet (I : Set (Fin 12)) →
        (∀ y ∈ Y, ∀ w ∈ I, w ∉ M y) → Y.card + I.card ≤ 5) := by
  classical
  let v : Fin 18 := 0
  let N : Finset (Fin 18) := univ.filter (G.Adj v)
  let A : Finset (Fin 18) := univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)
  have hNcard : N.card = 5 := h5 v
  have hdisj : Disjoint A N := by
    rw [Finset.disjoint_left]
    intro u huA huN
    exact (Finset.mem_filter.mp huA).2.2 (Finset.mem_filter.mp huN).2
  have hvout : v ∉ A ∪ N := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact (Finset.mem_filter.mp h).2.1 rfl
    · exact G.irrefl (Finset.mem_filter.mp h).2
  have hU : insert v (A ∪ N) = univ := by
    ext u
    simp only [A, N, Finset.mem_insert, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    by_cases huv : u = v
    · exact Or.inl huv
    · by_cases hadj : G.Adj v u
      · exact Or.inr (Or.inr hadj)
      · exact Or.inr (Or.inl ⟨huv, hadj⟩)
  have hcard := congrArg Finset.card hU
  rw [Finset.card_insert_of_notMem hvout, Finset.card_union_of_disjoint hdisj,
    Finset.card_univ, Fintype.card_fin] at hcard
  have hAcard : A.card = 12 := by omega
  have hAprop (x : Fin 18) (hx : x ∈ A) : x ≠ v ∧ ¬ G.Adj v x :=
    (Finset.mem_filter.mp hx).2
  have hNprop (x : Fin 18) (hx : x ∈ N) : G.Adj v x :=
    (Finset.mem_filter.mp hx).2
  let eN : Fin 5 ≃ N := (Fintype.equivFinOfCardEq (by simp [hNcard])).symm
  let eA : Fin 12 ≃ A := (Fintype.equivFinOfCardEq (by simp [hAcard])).symm
  let H : SimpleGraph (Fin 12) :=
    { Adj := fun i j => G.Adj (eA i).val (eA j).val
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun _ h => G.irrefl h⟩ }
  let M : Fin 5 → Finset (Fin 12) :=
    fun y => univ.filter (fun i => G.Adj (eN y).val (eA i).val)
  have hMmem (y : Fin 5) (i : Fin 12) :
      i ∈ M y ↔ G.Adj (eN y).val (eA i).val := by
    simp [M]
  have hNind : G.IsIndepSet (N : Set (Fin 18)) := by
    intro a ha b hb hab hadj
    exact hG {v, a, b} (SimpleGraph.is3Clique_iff.mpr
      ⟨v, a, b, hNprop a ha, hNprop b hb, hadj, rfl⟩)
  have hHclique : H.CliqueFree 3 := by
    intro t ht
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact hG {(eA a).val, (eA b).val, (eA c).val}
      (SimpleGraph.is3Clique_iff.mpr
        ⟨(eA a).val, (eA b).val, (eA c).val, hab, hac, hbc, rfl⟩)
  have hinjA : Function.Injective (fun i : Fin 12 => (eA i).val) :=
    fun i j hij => eA.injective (Subtype.ext hij)
  have hinjN : Function.Injective (fun y : Fin 5 => (eN y).val) :=
    fun i j hij => eN.injective (Subtype.ext hij)
  have hMcard (y : Fin 5) : (M y).card = 4 := by
    let z := (eN y).val
    let C : Finset (Fin 18) := univ.filter (G.Adj z)
    have hvC : v ∈ C := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (hNprop z (eN y).property).symm⟩
    have hImg : (M y).image (fun i => (eA i).val) = C.erase v := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        have hzi : G.Adj z (eA i).val := (hMmem y i).mp hi
        have hne : (eA i).val ≠ v := (hAprop _ (eA i).property).1
        exact Finset.mem_erase.mpr
          ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzi⟩⟩
      · intro hx
        have hxne : x ≠ v := (Finset.mem_erase.mp hx).1
        have hxadj : G.Adj z x :=
          (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2
        have hnot : ¬ G.Adj v x := by
          intro hvx
          exact hG {v, z, x} (SimpleGraph.is3Clique_iff.mpr
            ⟨v, z, x, hNprop z (eN y).property, hvx, hxadj, rfl⟩)
        let a : A := ⟨x, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hxne, hnot⟩⟩
        let i : Fin 12 := eA.symm a
        have hia : (eA i).val = x := by
          change (eA (eA.symm a)).val = x
          rw [eA.apply_symm_apply]
        have hi : i ∈ M y := by
          apply (hMmem y i).mpr
          rw [hia]
          exact hxadj
        exact Finset.mem_image.mpr ⟨i, hi, hia⟩
    have hErasecard : (C.erase v).card = 4 := by
      calc
        (C.erase v).card = C.card - 1 := Finset.card_erase_of_mem hvC
        _ = 4 := by have hc : C.card = 5 := h5 z; omega
    have hc := congrArg Finset.card hImg
    rw [Finset.card_image_of_injective _ hinjA, hErasecard] at hc
    exact hc
  have hMsets (y : Fin 5) : H.IsNIndepSet 4 (M y) := by
    refine ⟨?_, hMcard y⟩
    intro a ha b hb hab hadj
    have haa : G.Adj (eN y).val (eA a).val := (hMmem y a).mp ha
    have hbb : G.Adj (eN y).val (eA b).val := (hMmem y b).mp hb
    exact hG {(eN y).val, (eA a).val, (eA b).val}
      (SimpleGraph.is3Clique_iff.mpr
        ⟨(eN y).val, (eA a).val, (eA b).val, haa, hbb, hadj, rfl⟩)
  have hno5 : ∀ s, ¬ H.IsNIndepSet 5 s := by
    intro s hs
    let S : Finset (Fin 18) := s.image (fun i => (eA i).val)
    have hSi : G.IsIndepSet (S : Set (Fin 18)) := by
      intro a ha b hb hab hadj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      exact hs.isIndepSet hi hj (fun h => hab (by rw [h])) hadj
    have hScard : S.card = 5 := by
      rw [Finset.card_image_of_injective _ hinjA, hs.card_eq]
    have hvS : v ∉ S := by
      intro hv
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
      exact (hAprop _ (eA i).property).1 hi
    have hSi' : G.IsIndepSet ((insert v S : Finset (Fin 18)) : Set (Fin 18)) := by
      intro a ha b hb hab hadj
      simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact hab rfl
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
        exact (hAprop _ (eA i).property).2 hadj
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        exact (hAprop _ (eA i).property).2 hadj.symm
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
        exact hs.isIndepSet hi hj (fun h => hab (by rw [h])) hadj
    have hScard' : (insert v S).card = 6 := by
      rw [Finset.card_insert_of_notMem hvS, hScard]
    exact hno6 (insert v S) ⟨hSi', hScard'⟩
  have hbudget : ∀ w : Fin 12,
      (univ.filter (H.Adj w)).card +
        (univ.filter (fun y : Fin 5 => w ∈ M y)).card = 5 := by
    intro w
    let x := (eA w).val
    let C : Finset (Fin 18) := univ.filter (G.Adj x)
    let CA : Finset (Fin 18) := univ.filter (fun z => z ∈ A ∧ G.Adj x z)
    let CN : Finset (Fin 18) := univ.filter (fun z => z ∈ N ∧ G.Adj x z)
    have hCeq : C = CA ∪ CN := by
      ext z
      constructor
      · intro hz
        have hxz : G.Adj x z := (Finset.mem_filter.mp hz).2
        have hzv : z ≠ v := by
          intro hzv
          subst z
          exact (hAprop x (eA w).property).2 hxz.symm
        by_cases hvz : G.Adj v z
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, hvz⟩, hxz⟩))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, hzv, hvz⟩, hxz⟩))
      · intro hz
        rcases Finset.mem_union.mp hz with hz | hz
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2.2⟩
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2.2⟩
    have hdisjCA : Disjoint CA CN := by
      rw [Finset.disjoint_left]
      intro z hzA hzN
      exact (Finset.disjoint_left.mp hdisj)
        (Finset.mem_filter.mp hzA).2.1
        (Finset.mem_filter.mp hzN).2.1
    have hCAimg :
        (univ.filter (H.Adj w)).image (fun i => (eA i).val) = CA := by
      ext z
      constructor
      · intro hz
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, ⟨(eA i).property, (Finset.mem_filter.mp hi).2⟩⟩
      · intro hz
        have hza : z ∈ A := (Finset.mem_filter.mp hz).2.1
        have hzad : G.Adj x z := (Finset.mem_filter.mp hz).2.2
        let a : A := ⟨z, hza⟩
        let i : Fin 12 := eA.symm a
        have hia : (eA i).val = z := by
          change (eA (eA.symm a)).val = z
          rw [eA.apply_symm_apply]
        have hi : i ∈ univ.filter (H.Adj w) := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          change G.Adj (eA w).val (eA i).val
          rw [hia]
          exact hzad
        exact Finset.mem_image.mpr ⟨i, hi, hia⟩
    have hCNimg :
        (univ.filter (fun y : Fin 5 => w ∈ M y)).image
          (fun y => (eN y).val) = CN := by
      ext z
      constructor
      · intro hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
        have hyM : w ∈ M y := (Finset.mem_filter.mp hy).2
        have hyAdj : G.Adj (eN y).val x := (hMmem y w).mp hyM
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, ⟨(eN y).property, hyAdj.symm⟩⟩
      · intro hz
        have hzN : z ∈ N := (Finset.mem_filter.mp hz).2.1
        have hxz : G.Adj x z := (Finset.mem_filter.mp hz).2.2
        let a : N := ⟨z, hzN⟩
        let y : Fin 5 := eN.symm a
        have hya : (eN y).val = z := by
          change (eN (eN.symm a)).val = z
          rw [eN.apply_symm_apply]
        have hy : w ∈ M y := by
          apply (hMmem y w).mpr
          rw [hya]
          exact hxz.symm
        exact Finset.mem_image.mpr
          ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, hya⟩
    have hCAcard : CA.card = (univ.filter (H.Adj w)).card := by
      have hc := congrArg Finset.card hCAimg
      rw [Finset.card_image_of_injective _ hinjA] at hc
      exact hc.symm
    have hCNcard : CN.card =
        (univ.filter (fun y : Fin 5 => w ∈ M y)).card := by
      have hc := congrArg Finset.card hCNimg
      rw [Finset.card_image_of_injective _ hinjN] at hc
      exact hc.symm
    have hCcard : C.card = CA.card + CN.card := by
      rw [hCeq, Finset.card_union_of_disjoint hdisjCA]
    have hxdegree : C.card = 5 := h5 x
    calc
      (univ.filter (H.Adj w)).card +
          (univ.filter (fun y : Fin 5 => w ∈ M y)).card =
          CA.card + CN.card := by rw [hCAcard, hCNcard]
      _ = C.card := hCcard.symm
      _ = 5 := hxdegree
  have hmix : ∀ (Y : Finset (Fin 5)) (I : Finset (Fin 12)),
      Y.Nonempty → H.IsIndepSet (I : Set (Fin 12)) →
      (∀ y ∈ Y, ∀ w ∈ I, w ∉ M y) → Y.card + I.card ≤ 5 := by
    intro Y I hY hI havoid
    let P : Finset (Fin 18) := Y.image (fun y => (eN y).val)
    let Q : Finset (Fin 18) := I.image (fun i => (eA i).val)
    have hPQdisj : Disjoint P Q := by
      rw [Finset.disjoint_left]
      intro z hzP hzQ
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hzP
      obtain ⟨i, hi, hiz⟩ := Finset.mem_image.mp hzQ
      have hiN : (eA i).val ∈ N := by
        rw [hiz]
        exact (eN y).property
      exact (Finset.disjoint_left.mp hdisj) (eA i).property hiN
    have hPcard : P.card = Y.card := by
      rw [Finset.card_image_of_injective _ hinjN]
    have hQcard : Q.card = I.card := by
      rw [Finset.card_image_of_injective _ hinjA]
    have hPind : G.IsIndepSet (P : Set (Fin 18)) := by
      intro a ha b hb hab hadj
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
      exact hNind (eN y).property (eN z).property hab hadj
    have hQind : G.IsIndepSet (Q : Set (Fin 18)) := by
      intro a ha b hb hab hadj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      exact hI hi hj (fun h => hab (by rw [h])) hadj
    have hUind : G.IsIndepSet ((P ∪ Q : Finset (Fin 18)) : Set (Fin 18)) := by
      intro a ha b hb hab hadj
      simp only [Finset.mem_coe, Finset.mem_union] at ha hb
      rcases ha with haP | haQ
      · rcases hb with hbP | hbQ
        · exact hPind haP hbP hab hadj
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp haP
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hbQ
          have hm : i ∈ M y := (hMmem y i).mpr hadj
          exact havoid y hy i hi hm
      · rcases hb with hbP | hbQ
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hbP
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp haQ
          have hm : i ∈ M y := (hMmem y i).mpr hadj.symm
          exact havoid y hy i hi hm
        · exact hQind haQ hbQ hab hadj
    have hUcard : (P ∪ Q).card = Y.card + I.card := by
      rw [Finset.card_union_of_disjoint hPQdisj, hPcard, hQcard]
    by_contra hn
    have hlarge : 6 ≤ (P ∪ Q).card := by rw [hUcard]; omega
    obtain ⟨T, hTU, hTc⟩ := Finset.exists_subset_card_eq hlarge
    have hTi : G.IsIndepSet (T : Set (Fin 18)) := by
      intro a ha b hb hab hadj
      exact hUind (hTU ha) (hTU hb) hab hadj
    exact hno6 T ⟨hTi, hTc⟩
  exact ⟨H, M, hHclique, hno5, hMsets, hbudget, hmix⟩

private theorem r36_count_indicator {α : Type} (A : Finset α) (P : α → Prop)
    [DecidablePred P] :
    (∑ x ∈ A, (if P x then (1 : Nat) else 0)) = (A.filter P).card := by
  calc
    _ = ∑ _x ∈ A.filter P, (1 : Nat) := by rw [Finset.sum_filter]
    _ = _ := by simp

private theorem r36_swap_neighbor_counts (H : SimpleGraph (Fin 12))
    (P Q : Finset (Fin 12)) :
    (∑ x ∈ P, (Q.filter (H.Adj x)).card) =
      ∑ y ∈ Q, (P.filter (H.Adj y)).card := by
  classical
  calc
    _ = ∑ x ∈ P, ∑ y ∈ Q, (if H.Adj x y then (1 : Nat) else 0) := by
      exact Finset.sum_congr rfl (fun x _ => (r36_count_indicator Q (H.Adj x)).symm)
    _ = ∑ y ∈ Q, ∑ x ∈ P, (if H.Adj x y then (1 : Nat) else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← r36_count_indicator P (H.Adj y)]
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : H.Adj x y
      · have h' : H.Adj y x := h.symm
        rw [if_pos h, if_pos h']
      · have h' : ¬ H.Adj y x := fun ha => h ha.symm
        rw [if_neg h, if_neg h']

set_option maxHeartbeats 2000000 in
private theorem r36_antineighbor_eight_sum (H : SimpleGraph (Fin 12))
    (hH : H.CliqueFree 3) (hno5 : ∀ S, ¬ H.IsNIndepSet 5 S)
    (w : Fin 12) (A : Finset (Fin 12)) (hA : A.card = 8)
    (hAm : ∀ x ∈ A, x ≠ w ∧ ¬ H.Adj w x) :
    20 ≤ ∑ x ∈ A, (A.filter (H.Adj x)).card := by
  classical
  let e : Fin 8 ≃ A := (Fintype.equivFinOfCardEq (by simp [hA])).symm
  let f (i : Fin 8) : Fin 12 := (e i).val
  have hf : Function.Injective f := fun i j hij => e.injective (Subtype.ext hij)
  let K : SimpleGraph (Fin 8) :=
    { Adj := fun i j => H.Adj (f i) (f j)
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun _ h => H.irrefl h⟩ }
  have hK : K.CliqueFree 3 := by
    intro T hT
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.mp hT
    exact hH {f a, f b, f c}
      (SimpleGraph.is3Clique_iff.mpr ⟨f a, f b, f c, hab, hac, hbc, rfl⟩)
  have hK4 : ∀ S, ¬ K.IsNIndepSet 4 S := by
    intro S hS
    let T := S.image f
    have hwT : w ∉ T := by
      intro ht
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ht
      exact (hAm (f i) (e i).property).1 hi
    have hTc : T.card = 4 := by
      change (S.image f).card = 4
      rw [Finset.card_image_of_injective _ hf, hS.card_eq]
    apply hno5 (insert w T)
    refine ⟨?_, by rw [Finset.card_insert_of_notMem hwT, hTc]⟩
    intro a ha b hb hab hadj
    simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact hab rfl
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
      exact (hAm (f j) (e j).property).2 hadj
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact (hAm (f i) (e i).property).2 hadj.symm
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
      exact hS.isIndepSet hi hj (fun h => hab (congrArg f h)) hadj
  have hcard (i : Fin 8) : (univ.filter (K.Adj i)).card =
      (A.filter (H.Adj (f i))).card := by
    have he : (univ.filter (K.Adj i)).image f = A.filter (H.Adj (f i)) := by
      ext x
      constructor
      · intro hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_filter.mpr ⟨(e j).property, (Finset.mem_filter.mp hj).2⟩
      · intro hx
        obtain ⟨hxA, hxadj⟩ := Finset.mem_filter.mp hx
        let a : A := ⟨x, hxA⟩
        let j := e.symm a
        have hj : f j = x := congrArg Subtype.val (e.apply_symm_apply a)
        refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hj⟩
        change H.Adj (f i) (f j)
        rw [hj]
        exact hxadj
    have hh := congrArg Finset.card he
    rw [Finset.card_image_of_injective _ hf] at hh
    exact hh
  have hs : (∑ i : Fin 8, (univ.filter (K.Adj i)).card) =
      ∑ x ∈ A, (A.filter (H.Adj x)).card := by
    refine Finset.sum_bij (fun i _ => f i) ?_ ?_ ?_ ?_
    · intro i _
      exact (e i).property
    · intro i _ j _ hij
      exact hf hij
    · intro x hx
      let a : A := ⟨x, hx⟩
      exact ⟨e.symm a, Finset.mem_univ _, congrArg Subtype.val (e.apply_symm_apply a)⟩
    · intro i _
      exact hcard i
  exact (r36_small_ramsey.2.2.2 K hK hK4).trans_eq hs

set_option maxHeartbeats 2000000 in
private theorem r36_disjoint_degree_lower (H : SimpleGraph (Fin 12))
    (A N : Finset (Fin 12)) (hdisj : Disjoint A N)
    (hNI : H.IsIndepSet (N : Set (Fin 12))) :
    (∑ x ∈ A, (A.filter (H.Adj x)).card) +
      2 * (∑ x ∈ N, (univ.filter (H.Adj x)).card) ≤
      ∑ x : Fin 12, (univ.filter (H.Adj x)).card := by
  classical
  let d (x : Fin 12) := (univ.filter (H.Adj x)).card
  let a (x : Fin 12) := (A.filter (H.Adj x)).card
  let n (x : Fin 12) := (N.filter (H.Adj x)).card
  have hp (x : Fin 12) :
      (if x ∈ N then d x else 0) + n x + (if x ∈ A then a x else 0) ≤ d x := by
    by_cases hxN : x ∈ N
    · have hxA : x ∉ A := fun hx => (Finset.disjoint_left.mp hdisj) hx hxN
      have he : N.filter (H.Adj x) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        obtain ⟨hyN, hxy⟩ := Finset.mem_filter.mp hy
        exact hNI hxN hyN (fun heq => H.irrefl (heq ▸ hxy)) hxy
      have hz : n x = 0 := by simp [n, he]
      simp [hxN, hxA, hz]
    · have hsub (S : Finset (Fin 12)) : S.filter (H.Adj x) ⊆ univ.filter (H.Adj x) := by
        intro y hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
      have hsep : Disjoint (N.filter (H.Adj x)) (A.filter (H.Adj x)) := by
        rw [Finset.disjoint_left]
        intro y hyN hyA
        exact (Finset.disjoint_left.mp hdisj) (Finset.mem_filter.mp hyA).1
          (Finset.mem_filter.mp hyN).1
      have hu : N.filter (H.Adj x) ∪ A.filter (H.Adj x) ⊆ univ.filter (H.Adj x) :=
        Finset.union_subset (hsub N) (hsub A)
      have ha := Finset.card_le_card hu
      rw [Finset.card_union_of_disjoint hsep] at ha
      change n x + a x ≤ d x at ha
      have hn : n x ≤ d x := Finset.card_le_card (hsub N)
      by_cases hxA : x ∈ A
      · simpa [hxN, hxA] using ha
      · simpa [hxN, hxA] using hn
  have hsum := Finset.sum_le_sum (s := (univ : Finset (Fin 12))) (fun x _ => hp x)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hN : (∑ x : Fin 12, (if x ∈ N then d x else 0)) = ∑ x ∈ N, d x := by
    rw [← Finset.sum_filter]
    have he : (univ.filter (fun x : Fin 12 => x ∈ N)) = N := by ext x; simp
    rw [he]
  have hA : (∑ x : Fin 12, (if x ∈ A then a x else 0)) = ∑ x ∈ A, a x := by
    rw [← Finset.sum_filter]
    have he : (univ.filter (fun x : Fin 12 => x ∈ A)) = A := by ext x; simp
    rw [he]
  have hs : (∑ x : Fin 12, n x) = ∑ x ∈ N, d x :=
    r36_swap_neighbor_counts H univ N
  rw [hN, hA, hs] at hsum
  change (∑ x ∈ A, a x) + 2 * (∑ x ∈ N, d x) ≤ ∑ x : Fin 12, d x
  omega

private theorem r36_degree_three_cross_bound (H : SimpleGraph (Fin 12))
    (D : Finset (Fin 12)) (hH : H.CliqueFree 3)
    (hno5 : ∀ S, ¬ H.IsNIndepSet 5 S)
    (htotal : (∑ x : Fin 12, (univ.filter (H.Adj x)).card) = 40)
    (hclass : ∀ x : Fin 12,
      (x ∈ D → (univ.filter (H.Adj x)).card = 4) ∧
      (x ∉ D → (univ.filter (H.Adj x)).card = 3))
    (w : Fin 12) (hw : w ∉ D) : (D.filter (H.Adj w)).card ≤ 1 := by
  classical
  let N : Finset (Fin 12) := univ.filter (H.Adj w)
  let A : Finset (Fin 12) := univ.filter (fun x => x ≠ w ∧ ¬ H.Adj w x)
  have hN : N.card = 3 := (hclass w).2 hw
  have hNm (x : Fin 12) (hx : x ∈ N) : H.Adj w x :=
    (Finset.mem_filter.mp hx).2
  have hAm (x : Fin 12) (hx : x ∈ A) : x ≠ w ∧ ¬ H.Adj w x :=
    (Finset.mem_filter.mp hx).2
  have hdisj : Disjoint A N := by
    rw [Finset.disjoint_left]
    intro x hxA hxN
    exact (hAm x hxA).2 (hNm x hxN)
  have hwout : w ∉ A ∪ N := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact (hAm w h).1 rfl
    · exact H.irrefl (hNm w h)
  have hU : insert w (A ∪ N) = univ := by
    ext x
    simp only [A, N, Finset.mem_insert, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    by_cases hx : x = w
    · exact Or.inl hx
    · by_cases he : H.Adj w x
      · exact Or.inr (Or.inr he)
      · exact Or.inr (Or.inl ⟨hx, he⟩)
  have hc := congrArg Finset.card hU
  rw [Finset.card_insert_of_notMem hwout, Finset.card_union_of_disjoint hdisj,
    Finset.card_univ, Fintype.card_fin] at hc
  have hA : A.card = 8 := by omega
  have hNI : H.IsIndepSet (N : Set (Fin 12)) := by
    intro x hx y hy _ hxy
    exact hH {w, x, y} (SimpleGraph.is3Clique_iff.mpr
      ⟨w, x, y, hNm x hx, hNm y hy, hxy, rfl⟩)
  have hlow := r36_antineighbor_eight_sum H hH hno5 w A hA hAm
  have hupper := r36_disjoint_degree_lower H A N hdisj hNI
  rw [htotal] at hupper
  have hNs : (∑ x ∈ N, (univ.filter (H.Adj x)).card) =
      9 + (D.filter (H.Adj w)).card := by
    calc
      _ = ∑ x ∈ N, (3 + (if x ∈ D then (1 : Nat) else 0)) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ D
        · rw [if_pos hx, (hclass x).1 hx]
        · rw [if_neg hx, (hclass x).2 hx]
      _ = _ := by
        rw [Finset.sum_add_distrib, r36_count_indicator]
        have h₃ : (∑ _x ∈ N, (3 : Nat)) = 9 := by simp [hN]
        have he : N.filter (fun x => x ∈ D) = D.filter (H.Adj w) := by
          ext x
          simp [N, and_comm]
        rw [h₃, he]
  rw [hNs] at hupper
  omega

private theorem r36_four_internal_saturation (H : SimpleGraph (Fin 12))
    (D : Finset (Fin 12)) (hH : H.CliqueFree 3) (hD : D.card = 4)
    (hsum : 8 ≤ ∑ w ∈ D, (D.filter (H.Adj w)).card) :
    ∀ w ∈ D, (D.filter (H.Adj w)).card = 2 := by
  classical
  let c (w : Fin 12) : Nat := (D.filter (H.Adj w)).card
  change 8 ≤ ∑ w ∈ D, c w at hsum
  change ∀ w ∈ D, c w = 2
  have hupper (x : Fin 12) (hx : x ∈ D) : c x ≤ 2 := by
    by_contra hn
    let A : Finset (Fin 12) := D.filter (H.Adj x)
    have hxA : x ∉ A := fun h => H.irrefl (Finset.mem_filter.mp h).2
    have hsub : insert x A ⊆ D := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact (Finset.mem_filter.mp hy).1
    have hi : (insert x A).card = A.card + 1 := Finset.card_insert_of_notMem hxA
    have hle := Finset.card_le_card hsub
    have hn' : ¬ A.card ≤ 2 := hn
    have hA : A.card = 3 := by omega
    have he : insert x A = D := Finset.eq_of_subset_of_card_le hsub (by omega)
    have hy (y : Fin 12) (hyA : y ∈ A) : c y ≤ 1 := by
      have hxy : H.Adj x y := (Finset.mem_filter.mp hyA).2
      have hs : D.filter (H.Adj y) ⊆ ({x} : Finset (Fin 12)) := by
        intro z hz
        have hzD := (Finset.mem_filter.mp hz).1
        have hyz := (Finset.mem_filter.mp hz).2
        apply Finset.mem_singleton.mpr
        by_contra hzx
        have hzA : z ∈ A := by
          have hh : z ∈ insert x A := he.symm ▸ hzD
          exact (Finset.mem_insert.mp hh).resolve_left hzx
        exact hH {x, y, z} (SimpleGraph.is3Clique_iff.mpr
          ⟨x, y, z, hxy, (Finset.mem_filter.mp hzA).2, hyz, rfl⟩)
      simpa only [Finset.card_singleton] using Finset.card_le_card hs
    have hsmall : (∑ y ∈ A, c y) ≤ 3 := by
      calc
        _ ≤ ∑ _y ∈ A, (1 : Nat) := Finset.sum_le_sum hy
        _ = 3 := by simp [hA]
    have hcx : c x = 3 := hA
    have hh : 8 ≤ c x + (∑ y ∈ A, c y) := by
      rw [← Finset.sum_insert hxA, he]
      exact hsum
    omega
  intro x hx
  have hd := hupper x hx
  have hn : x ∉ D.erase x := by simp
  have hc : (D.erase x).card = 3 := by rw [Finset.card_erase_of_mem hx, hD]
  have hsmall : (∑ y ∈ D.erase x, c y) ≤ 6 := by
    calc
      _ ≤ ∑ _y ∈ D.erase x, (2 : Nat) :=
        Finset.sum_le_sum (fun y hy => hupper y (Finset.mem_erase.mp hy).2)
      _ = 6 := by simp [hc]
  have hh : 8 ≤ c x + (∑ y ∈ D.erase x, c y) := by
    rw [← Finset.sum_insert hn, Finset.insert_erase hx]
    exact hsum
  omega

private theorem r36_degree_partition (H : SimpleGraph (Fin 12))
    (M : Fin 5 → Finset (Fin 12)) (hH : H.CliqueFree 3)
    (hno5 : ∀ s, ¬ H.IsNIndepSet 5 s)
    (hM : ∀ y : Fin 5, H.IsNIndepSet 4 (M y))
    (hbudget : ∀ w : Fin 12, (univ.filter (H.Adj w)).card +
      (univ.filter (fun y : Fin 5 => w ∈ M y)).card = 5) :
    ∃ D : Finset (Fin 12), D.card = 4 ∧
      (∀ w : Fin 12, (w ∈ D → (univ.filter (H.Adj w)).card = 4) ∧
        (w ∉ D → (univ.filter (H.Adj w)).card = 3)) ∧
      (∀ w ∈ D, (D.filter (H.Adj w)).card = 2) ∧
      (∀ w ∉ D, (D.filter (H.Adj w)).card = 1) ∧
      (∀ w ∉ D, (univ.filter (fun z : Fin 12 => z ∉ D ∧ H.Adj w z)).card = 2) := by
  classical
  let d (w : Fin 12) : Nat := (univ.filter (H.Adj w)).card
  let m (w : Fin 12) : Nat := (univ.filter (fun y : Fin 5 => w ∈ M y)).card
  have hrange (w : Fin 12) : 3 ≤ d w ∧ d w ≤ 4 := by
    by_contra hn
    have hv : 5 ≤ d w ∨ 9 + d w < 12 := by omega
    obtain ⟨S, hS⟩ := r36_vertex_step H hH w r36_small_ramsey.2.1 hv
    exact hno5 S hS
  have hm : (∑ w : Fin 12, m w) = 20 := by
    calc
      (∑ w : Fin 12, m w) =
          ∑ w : Fin 12, ∑ y : Fin 5, (if w ∈ M y then (1 : Nat) else 0) := by
        apply Finset.sum_congr rfl
        intro w _
        exact (r36_count_indicator univ (fun y : Fin 5 => w ∈ M y)).symm
      _ = ∑ y : Fin 5, ∑ w : Fin 12, (if w ∈ M y then (1 : Nat) else 0) :=
        Finset.sum_comm
      _ = ∑ y : Fin 5, (M y).card := by
        apply Finset.sum_congr rfl
        intro y _
        rw [r36_count_indicator]
        have he : (univ.filter (fun w : Fin 12 => w ∈ M y)) = M y := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [he]
      _ = 20 := by
        simp only [fun y => (hM y).card_eq]
        simp
  have htotal : (∑ w : Fin 12, d w) = 40 := by
    have hs : (∑ w : Fin 12, (d w + m w)) = 60 := by
      calc
        _ = ∑ _w : Fin 12, (5 : Nat) := Finset.sum_congr rfl (fun w _ => hbudget w)
        _ = 60 := by simp
    rw [Finset.sum_add_distrib, hm] at hs
    omega
  let D : Finset (Fin 12) := univ.filter (fun w => d w = 4)
  have hclass (w : Fin 12) : (w ∈ D → d w = 4) ∧ (w ∉ D → d w = 3) := by
    have he : w ∈ D ↔ d w = 4 := by
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨he.mp, ?_⟩
    intro hw
    have hn : d w ≠ 4 := fun hd => hw (he.mpr hd)
    obtain ⟨hl, hh⟩ := hrange w
    omega
  have hD : D.card = 4 := by
    have hs : (∑ w : Fin 12, d w) = 36 + D.card := by
      calc
        _ = ∑ w : Fin 12, (3 + (if w ∈ D then (1 : Nat) else 0)) := by
          apply Finset.sum_congr rfl
          intro w _
          by_cases hw : w ∈ D
          · rw [if_pos hw, (hclass w).1 hw]
          · rw [if_neg hw, (hclass w).2 hw]
        _ = _ := by
          rw [Finset.sum_add_distrib, r36_count_indicator]
          have he : (univ.filter (fun w : Fin 12 => w ∈ D)) = D := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have h36 : (∑ _w : Fin 12, (3 : Nat)) = 36 := by simp
          rw [he, h36]
    omega
  let B : Finset (Fin 12) := univ.filter (fun w => w ∉ D)
  let c (w : Fin 12) : Nat := (D.filter (H.Adj w)).card
  let o (w : Fin 12) : Nat := (B.filter (H.Adj w)).card
  have hBmem (w : Fin 12) : w ∈ B ↔ w ∉ D := by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
  have hDB : Disjoint D B := by
    rw [Finset.disjoint_left]
    intro w hwD hwB
    exact (hBmem w).mp hwB hwD
  have hB : B.card = 8 := by
    have hu : D ∪ B = univ := by
      ext w
      simp only [Finset.mem_union, hBmem, Finset.mem_univ, iff_true]
      exact em _
    have hc := congrArg Finset.card hu
    rw [Finset.card_union_of_disjoint hDB, Finset.card_univ, Fintype.card_fin] at hc
    omega
  have hpart (w : Fin 12) : c w + o w = d w := by
    have hs : Disjoint (D.filter (H.Adj w)) (B.filter (H.Adj w)) := by
      rw [Finset.disjoint_left]
      intro z hzD hzB
      exact (Finset.disjoint_left.mp hDB) (Finset.mem_filter.mp hzD).1
        (Finset.mem_filter.mp hzB).1
    have hu : D.filter (H.Adj w) ∪ B.filter (H.Adj w) = univ.filter (H.Adj w) := by
      ext z
      by_cases hz : z ∈ D <;> simp only [Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, hBmem, hz, not_true_eq_false, not_false_eq_true,
        true_and, false_and, false_or, or_false]
    have hc := Finset.card_union_of_disjoint hs
    rw [hu] at hc
    exact hc.symm
  have hbound (w : Fin 12) (hw : w ∈ B) : c w ≤ 1 :=
    r36_degree_three_cross_bound H D hH hno5 htotal hclass w ((hBmem w).mp hw)
  have hswap : (∑ w ∈ D, o w) = ∑ z ∈ B, c z := by
    calc
      _ = ∑ w ∈ D, ∑ z ∈ B, (if H.Adj w z then (1 : Nat) else 0) := by
        exact Finset.sum_congr rfl (fun w _ => (r36_count_indicator B (H.Adj w)).symm)
      _ = ∑ z ∈ B, ∑ w ∈ D, (if H.Adj w z then (1 : Nat) else 0) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z _
        change (∑ w ∈ D, (if H.Adj w z then (1 : Nat) else 0)) =
          (D.filter (H.Adj z)).card
        rw [← r36_count_indicator D (H.Adj z)]
        apply Finset.sum_congr rfl
        intro w _
        by_cases h : H.Adj w z
        · have h' : H.Adj z w := h.symm
          rw [if_pos h, if_pos h']
        · have h' : ¬ H.Adj z w := fun ha => h ha.symm
          rw [if_neg h, if_neg h']
  have hleB : (∑ w ∈ B, c w) ≤ 8 := by
    calc
      _ ≤ ∑ _w ∈ B, (1 : Nat) := Finset.sum_le_sum hbound
      _ = 8 := by simp [hB]
  have hDsum : (∑ w ∈ D, c w) + (∑ w ∈ D, o w) = 16 := by
    calc
      _ = ∑ w ∈ D, (c w + o w) := (Finset.sum_add_distrib).symm
      _ = ∑ w ∈ D, (4 : Nat) := by
        exact Finset.sum_congr rfl (fun w hw => (hpart w).trans ((hclass w).1 hw))
      _ = 16 := by simp [hD]
  have hgeD : 8 ≤ ∑ w ∈ D, c w := by omega
  have hinside : ∀ w ∈ D, c w = 2 := r36_four_internal_saturation H D hH hD hgeD
  have hsD : (∑ w ∈ D, c w) = 8 := by
    calc
      _ = ∑ _w ∈ D, (2 : Nat) := Finset.sum_congr rfl hinside
      _ = 8 := by simp [hD]
  have hsB : (∑ w ∈ B, c w) = 8 := by omega
  have hOne (w : Fin 12) (hw : w ∈ B) : c w = 1 := by
    have hle := hbound w hw
    have he := Finset.insert_erase hw
    have hn : w ∉ B.erase w := by simp
    have hsmall : (∑ z ∈ B.erase w, c z) ≤ 7 := by
      have hc : (B.erase w).card = 7 := by rw [Finset.card_erase_of_mem hw, hB]
      calc
        _ ≤ ∑ _z ∈ B.erase w, (1 : Nat) :=
          Finset.sum_le_sum (fun z hz => hbound z (Finset.mem_erase.mp hz).2)
        _ = 7 := by simp [hc]
    have hs : c w + (∑ z ∈ B.erase w, c z) = 8 := by
      rw [← Finset.sum_insert hn, he, hsB]
    omega
  refine ⟨D, hD, hclass, hinside, ?_, ?_⟩
  · intro w hw
    exact hOne w ((hBmem w).mpr hw)
  · intro w hw
    have he : univ.filter (fun z : Fin 12 => z ∉ D ∧ H.Adj w z) = B.filter (H.Adj w) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hBmem]
    rw [he]
    change o w = 2
    have hp := hpart w
    have hc := hOne w ((hBmem w).mpr hw)
    have hd := (hclass w).2 hw
    omega

set_option maxHeartbeats 800000 in
private theorem r36_label_degree_partition (H : SimpleGraph (Fin 12))
    (D : Finset (Fin 12)) (hH : H.CliqueFree 3) (hD : D.card = 4)
    (hclass : ∀ w : Fin 12, (w ∈ D → (univ.filter (H.Adj w)).card = 4) ∧
      (w ∉ D → (univ.filter (H.Adj w)).card = 3))
    (hinside : ∀ w ∈ D, (D.filter (H.Adj w)).card = 2)
    (hcross : ∀ w ∉ D, (D.filter (H.Adj w)).card = 1) :
    ∃ e : Fin 12 ≃ Fin 12,
      (∀ i : Fin 12, e i ∈ D ↔ i.val < 4) ∧
      (∀ a b : Fin 12, (a.val < 4 ∨ b.val < 4) →
        (H.Adj (e a) (e b) ↔ (baseAdj12.getD a.val 0).testBit b.val = true)) ∧
      (¬ H.Adj (e 4) (e 5)) ∧ (¬ H.Adj (e 6) (e 7)) ∧
      (¬ H.Adj (e 8) (e 9)) ∧ (¬ H.Adj (e 10) (e 11)) := by
  classical
  have hDpos : 0 < D.card := by omega
  obtain ⟨d0, hd0⟩ := Finset.card_pos.mp hDpos
  obtain ⟨d1, d3, h13, hN0⟩ := Finset.card_eq_two.mp (hinside d0 hd0)
  have hd1D : d1 ∈ D := (Finset.mem_filter.mp (by rw [hN0]; simp)).1
  have hd3D : d3 ∈ D := (Finset.mem_filter.mp (by rw [hN0]; simp)).1
  have h01 : H.Adj d0 d1 := (Finset.mem_filter.mp (by rw [hN0]; simp)).2
  have h03 : H.Adj d0 d3 := (Finset.mem_filter.mp (by rw [hN0]; simp)).2
  have h01_ne : d0 ≠ d1 := h01.ne
  have h03_ne : d0 ≠ d3 := h03.ne
  have hnot13 : ¬ H.Adj d1 d3 := fun h =>
    hH {d0, d1, d3} (SimpleGraph.is3Clique_iff.mpr ⟨d0, d1, d3, h01, h03, h, rfl⟩)
  have hsub3 : ({d0, d1, d3} : Finset (Fin 12)) ⊆ D := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard3 : ({d0, d1, d3} : Finset (Fin 12)).card = 3 := by
    have h1 : d0 ∉ ({d1, d3} : Finset (Fin 12)) := by simp [h01_ne, h03_ne]
    rw [Finset.card_insert_of_notMem h1, Finset.card_pair h13]
  have hrem1 : (D \ ({d0, d1, d3} : Finset (Fin 12))).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub3, hD, hcard3]
  obtain ⟨d2, hd2eq⟩ := Finset.card_eq_one.mp hrem1
  have hd2mem : d2 ∈ D \ ({d0, d1, d3} : Finset (Fin 12)) := by rw [hd2eq]; simp
  obtain ⟨hd2D, hd2not⟩ := Finset.mem_sdiff.mp hd2mem
  have h20_ne : d2 ≠ d0 := fun h => hd2not (by simp [h])
  have h21_ne : d2 ≠ d1 := fun h => hd2not (by simp [h])
  have h23_ne : d2 ≠ d3 := fun h => hd2not (by simp [h])
  have hnot02 : ¬ H.Adj d0 d2 := by
    intro h
    have hm : d2 ∈ D.filter (H.Adj d0) := Finset.mem_filter.mpr ⟨hd2D, h⟩
    rw [hN0] at hm
    simp [h21_ne, h23_ne] at hm
  have hD_eq : D = {d0, d1, d2, d3} := by
    ext x
    constructor
    · intro hx
      by_cases h3 : x ∈ ({d0, d1, d3} : Finset (Fin 12))
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h3 ⊢
        rcases h3 with rfl | rfl | rfl <;> simp
      · have : x ∈ D \ ({d0, d1, d3} : Finset (Fin 12)) := Finset.mem_sdiff.mpr ⟨hx, h3⟩
        rw [hd2eq, Finset.mem_singleton] at this
        simp [this]
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hN2_sub : D.filter (H.Adj d2) ⊆ {d1, d3} := by
    intro x hx
    obtain ⟨hxD, hxA⟩ := Finset.mem_filter.mp hx
    rw [hD_eq] at hxD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxD ⊢
    rcases hxD with rfl | rfl | rfl | rfl
    · exact (hnot02 hxA.symm).elim
    · exact Or.inl rfl
    · exact (H.irrefl hxA).elim
    · exact Or.inr rfl
  have hN2_eq : D.filter (H.Adj d2) = {d1, d3} :=
    Finset.eq_of_subset_of_card_le hN2_sub (by rw [hinside d2 hd2D, Finset.card_pair h13])
  have h21 : H.Adj d2 d1 := (Finset.mem_filter.mp (by rw [hN2_eq]; simp)).2
  have h23 : H.Adj d2 d3 := (Finset.mem_filter.mp (by rw [hN2_eq]; simp)).2
  have hpair_out : ∀ w ∈ D, ((univ \ D).filter (H.Adj w)).card = 2 := by
    intro w hw
    have hdisj : Disjoint (D.filter (H.Adj w)) ((univ \ D).filter (H.Adj w)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx2).1).2 (Finset.mem_filter.mp hx1).1
    have hunion : D.filter (H.Adj w) ∪ (univ \ D).filter (H.Adj w) = univ.filter (H.Adj w) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      by_cases hxD : x ∈ D <;> simp [hxD]
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hunion, (hclass w).1 hw, hinside w hw] at hc
    omega
  obtain ⟨p0, p1, hp01, hP0⟩ := Finset.card_eq_two.mp (hpair_out d0 hd0)
  obtain ⟨p2, p3, hp23, hP1⟩ := Finset.card_eq_two.mp (hpair_out d1 hd1D)
  obtain ⟨p4, p5, hp45, hP2⟩ := Finset.card_eq_two.mp (hpair_out d2 hd2D)
  obtain ⟨p6, p7, hp67, hP3⟩ := Finset.card_eq_two.mp (hpair_out d3 hd3D)
  have hmemP : ∀ {w a b : Fin 12}, (univ \ D).filter (H.Adj w) = {a, b} →
      a ∉ D ∧ b ∉ D ∧ H.Adj w a ∧ H.Adj w b ∧ ¬ H.Adj a b := by
    intro w a b hP
    have ha := Finset.mem_filter.mp (by rw [hP]; simp : a ∈ (univ \ D).filter (H.Adj w))
    have hb := Finset.mem_filter.mp (by rw [hP]; simp : b ∈ (univ \ D).filter (H.Adj w))
    refine ⟨(Finset.mem_sdiff.mp ha.1).2, (Finset.mem_sdiff.mp hb.1).2, ha.2, hb.2, ?_⟩
    intro hab
    exact hH {w, a, b} (SimpleGraph.is3Clique_iff.mpr ⟨w, a, b, ha.2, hb.2, hab, rfl⟩)
  obtain ⟨hp0D, hp1D, h0p0, h0p1, hnp01⟩ := hmemP hP0
  obtain ⟨hp2D, hp3D, h1p2, h1p3, hnp23⟩ := hmemP hP1
  obtain ⟨hp4D, hp5D, h2p4, h2p5, hnp45⟩ := hmemP hP2
  obtain ⟨hp6D, hp7D, h3p6, h3p7, hnp67⟩ := hmemP hP3
  have huniqD : ∀ {x u v : Fin 12}, x ∉ D → u ∈ D → v ∈ D → H.Adj u x → H.Adj v x → u = v := by
    intro x u v hxD huD hvD hux hvx
    have h1 := hcross x hxD
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp h1
    have hu : u ∈ D.filter (H.Adj x) := Finset.mem_filter.mpr ⟨huD, hux.symm⟩
    have hv : v ∈ D.filter (H.Adj x) := Finset.mem_filter.mpr ⟨hvD, hvx.symm⟩
    rw [hz, Finset.mem_singleton] at hu hv
    exact hu.trans hv.symm
  let f : Fin 12 → Fin 12 := fun i =>
    match i.val with
    | 0 => d0 | 1 => d1 | 2 => d2 | 3 => d3
    | 4 => p0 | 5 => p1 | 6 => p2 | 7 => p3
    | 8 => p4 | 9 => p5 | 10 => p6 | _ => p7
  have hfD : ∀ i : Fin 12, f i ∈ D ↔ i.val < 4 := by
    intro i
    fin_cases i <;> simp [f, hd0, hd1D, hd2D, hd3D, hp0D, hp1D, hp2D, hp3D, hp4D, hp5D, hp6D, hp7D]
  let owner : Fin 12 → Fin 12 := fun i =>
    match i.val with
    | 4 | 5 => d0 | 6 | 7 => d1 | 8 | 9 => d2 | _ => d3
  have hownD : ∀ i : Fin 12, owner i ∈ D := by
    intro i; fin_cases i <;> simp [owner, hd0, hd1D, hd2D, hd3D]
  have hownAdj : ∀ i : Fin 12, 4 ≤ i.val → H.Adj (owner i) (f i) := by
    intro i hi
    fin_cases i <;> simp only [Fin.val_mk, owner, f] at hi ⊢ <;>
      first | omega | assumption
  have hd_inj : ∀ i j : Fin 12, i.val < 4 → j.val < 4 → f i = f j → i = j := by
    intro ⟨i, _⟩ ⟨j, _⟩ hi hj hij
    dsimp only at hi hj
    apply Fin.ext
    dsimp only
    interval_cases i <;> interval_cases j <;> simp only [f] at hij <;>
      first
      | rfl
      | exact (h01_ne hij).elim | exact (h01_ne hij.symm).elim
      | exact (h20_ne hij).elim | exact (h20_ne hij.symm).elim
      | exact (h03_ne hij).elim | exact (h03_ne hij.symm).elim
      | exact (h21_ne hij).elim | exact (h21_ne hij.symm).elim
      | exact (h13 hij).elim | exact (h13 hij.symm).elim
      | exact (h23_ne hij).elim | exact (h23_ne hij.symm).elim
  have hown_eq_imp : ∀ i j : Fin 12, 4 ≤ i.val → 4 ≤ j.val → owner i = owner j → f i = f j → i = j := by
    intro ⟨i, hi12⟩ ⟨j, hj12⟩ hi hj ho hij
    dsimp only at hi hj
    apply Fin.ext
    dsimp only
    interval_cases i <;> interval_cases j <;> simp only [owner, f] at ho hij <;>
      first
      | rfl
      | exact (hp01 hij).elim | exact (hp01 hij.symm).elim
      | exact (hp23 hij).elim | exact (hp23 hij.symm).elim
      | exact (hp45 hij).elim | exact (hp45 hij.symm).elim
      | exact (hp67 hij).elim | exact (hp67 hij.symm).elim
      | exact (h01_ne ho).elim | exact (h01_ne ho.symm).elim
      | exact (h20_ne ho).elim | exact (h20_ne ho.symm).elim
      | exact (h03_ne ho).elim | exact (h03_ne ho.symm).elim
      | exact (h21_ne ho).elim | exact (h21_ne ho.symm).elim
      | exact (h13 ho).elim | exact (h13 ho.symm).elim
      | exact (h23_ne ho).elim | exact (h23_ne ho.symm).elim
  have hf_inj : Function.Injective f := by
    intro i j hij
    by_cases hi : i.val < 4 <;> by_cases hj : j.val < 4
    · exact hd_inj i j hi hj hij
    · exact (((hfD j).mp (hij ▸ (hfD i).mpr hi)) |> fun h => (hj h).elim)
    · exact (((hfD i).mp (hij.symm ▸ (hfD j).mpr hj)) |> fun h => (hi h).elim)
    · have ho : owner i = owner j :=
        huniqD (fun h => hi ((hfD i).mp h)) (hownD i) (hownD j)
          (hownAdj i (by omega)) (hij ▸ hownAdj j (by omega))
      exact hown_eq_imp i j (by omega) (by omega) ho hij
  have hbase_symm : ∀ a b : Fin 12,
      (baseAdj12.getD a.val 0).testBit b.val = (baseAdj12.getD b.val 0).testBit a.val := by
    decide
  have hbase_left : ∀ a b : Fin 12, a.val < 4 →
      (H.Adj (f a) (f b) ↔ (baseAdj12.getD a.val 0).testBit b.val = true) := by
    intro ⟨a, ha12⟩ ⟨b, hb12⟩ ha
    dsimp only at ha ⊢
    by_cases hb : b < 4
    · interval_cases a <;> interval_cases b <;> simp only [f] <;>
        first
        | exact iff_of_true h01 (by decide) | exact iff_of_true h01.symm (by decide)
        | exact iff_of_true h03 (by decide) | exact iff_of_true h03.symm (by decide)
        | exact iff_of_true h21 (by decide) | exact iff_of_true h21.symm (by decide)
        | exact iff_of_true h23 (by decide) | exact iff_of_true h23.symm (by decide)
        | exact iff_of_false (fun h => H.irrefl h) (by decide)
        | exact iff_of_false hnot02 (by decide) | exact iff_of_false (fun h => hnot02 h.symm) (by decide)
        | exact iff_of_false hnot13 (by decide) | exact iff_of_false (fun h => hnot13 h.symm) (by decide)
    · have hb4 : 4 ≤ b := by omega
      have hiff : H.Adj (f ⟨a, ha12⟩) (f ⟨b, hb12⟩) ↔ f ⟨a, ha12⟩ = owner ⟨b, hb12⟩ := by
        constructor
        · intro hadj
          exact huniqD (fun h => hb ((hfD ⟨b, hb12⟩).mp h)) ((hfD ⟨a, ha12⟩).mpr ha) (hownD ⟨b, hb12⟩) hadj (hownAdj ⟨b, hb12⟩ hb4)
        · intro heq; rw [heq]; exact hownAdj ⟨b, hb12⟩ hb4
      rw [hiff]
      interval_cases a <;> interval_cases b <;> simp only [f, owner] <;>
        first
        | exact iff_of_true trivial (by decide)
        | exact iff_of_false h01_ne (by decide) | exact iff_of_false h01_ne.symm (by decide)
        | exact iff_of_false h20_ne (by decide) | exact iff_of_false h20_ne.symm (by decide)
        | exact iff_of_false h03_ne (by decide) | exact iff_of_false h03_ne.symm (by decide)
        | exact iff_of_false h21_ne (by decide) | exact iff_of_false h21_ne.symm (by decide)
        | exact iff_of_false h13 (by decide) | exact iff_of_false h13.symm (by decide)
        | exact iff_of_false h23_ne (by decide) | exact iff_of_false h23_ne.symm (by decide)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj), hfD, ?_, hnp01, hnp23, hnp45, hnp67⟩
  intro a b hab
  simp only [Equiv.ofBijective_apply]
  rcases hab with ha | hb
  · exact hbase_left a b ha
  · rw [H.adj_comm, hbase_symm a b]
    exact hbase_left b a hb

private lemma r36_5reg_frame (G : SimpleGraph (Fin 18)) (hG : G.CliqueFree 3)
    (hno6 : ∀ s, ¬ G.IsNIndepSet 6 s)
    (h5 : ∀ v : Fin 18, (univ.filter (G.Adj v)).card = 5) :
    ∃ (H : SimpleGraph (Fin 12)) (M : Fin 5 → Finset (Fin 12)),
      H.CliqueFree 3 ∧
      (∀ s, ¬ H.IsNIndepSet 5 s) ∧
      (∀ a b : Fin 12, (a.val < 4 ∨ b.val < 4) →
        (H.Adj a b ↔ (baseAdj12.getD a.val 0).testBit b.val = true)) ∧
      (¬ H.Adj ⟨4, by decide⟩ ⟨5, by decide⟩) ∧
      (¬ H.Adj ⟨6, by decide⟩ ⟨7, by decide⟩) ∧
      (¬ H.Adj ⟨8, by decide⟩ ⟨9, by decide⟩) ∧
      (¬ H.Adj ⟨10, by decide⟩ ⟨11, by decide⟩) ∧
      (∀ u : Fin 12, 4 ≤ u.val →
        (univ.filter (fun v : Fin 12 => 4 ≤ v.val ∧ H.Adj u v)).card = 2) ∧
      (∀ y : Fin 5, H.IsNIndepSet 4 (M y)) ∧
      (∀ w : Fin 12, (univ.filter (fun y : Fin 5 => w ∈ M y)).card = if w.val < 4 then 1 else 2) ∧
      (∀ (Y : Finset (Fin 5)) (I : Finset (Fin 12)),
        Y.Nonempty → H.IsIndepSet (I : Set (Fin 12)) →
        (∀ y ∈ Y, ∀ w ∈ I, w ∉ M y) →
        Y.card + I.card ≤ 5) := by
  classical
  obtain ⟨H, M, hH, hno5, hM, hbudget, hmix⟩ :=
    r36_extract_antineighborhood G hG hno6 h5
  obtain ⟨D, hD, hclass, hinside, hcross, houtside⟩ :=
    r36_degree_partition H M hH hno5 hM hbudget
  obtain ⟨e, heD, hbase, hf1, hf2, hf3, hf4⟩ :=
    r36_label_degree_partition H D hH hD hclass hinside hcross
  let K : SimpleGraph (Fin 12) :=
    { Adj := fun a b => H.Adj (e a) (e b)
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun _ h => H.irrefl h⟩ }
  let F (S : Finset (Fin 12)) : Finset (Fin 12) := S.map e.toEmbedding
  let L (y : Fin 5) : Finset (Fin 12) := (M y).map e.symm.toEmbedding
  have hF (S : Finset (Fin 12)) (i : Fin 12) (hi : i ∈ S) : e i ∈ F S :=
    Finset.mem_map.mpr ⟨i, hi, rfl⟩
  have hL (y : Fin 5) (i : Fin 12) : i ∈ L y ↔ e i ∈ M y := by
    change i ∈ (M y).map e.symm.toEmbedding ↔ e i ∈ M y
    constructor
    · intro hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
      change e.symm j = i at hji
      rwa [← hji, e.apply_symm_apply]
    · intro hi
      exact Finset.mem_map.mpr ⟨e i, hi, e.symm_apply_apply i⟩
  have hmapInd (S : Finset (Fin 12)) (hS : K.IsIndepSet (S : Set (Fin 12))) :
      H.IsIndepSet (F S : Set (Fin 12)) := by
    intro a ha b hb hab hadj
    change a ∈ S.map e.toEmbedding at ha
    change b ∈ S.map e.toEmbedding at hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
    exact hS hi hj (fun hij => hab (congrArg (fun k => e k) hij)) hadj
  have hcount (P Q : Fin 12 → Prop) [DecidablePred P] [DecidablePred Q]
      (hPQ : ∀ i, P i ↔ Q (e i)) :
      (univ.filter P).card = (univ.filter Q).card := by
    have heq : F (univ.filter P) = univ.filter Q := by
      ext j
      constructor
      · intro hj
        change j ∈ (univ.filter P).map e.toEmbedding at hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hPQ i).mp (Finset.mem_filter.mp hi).2⟩
      · intro hj
        have hq : Q (e (e.symm j)) := by
          rw [e.apply_symm_apply]
          exact (Finset.mem_filter.mp hj).2
        change j ∈ (univ.filter P).map e.toEmbedding
        exact Finset.mem_map.mpr ⟨e.symm j,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hPQ _).mpr hq⟩,
          e.apply_symm_apply j⟩
    simpa only [F, Finset.card_map] using congrArg Finset.card heq
  have hlow (i : Fin 12) : 4 ≤ i.val ↔ e i ∉ D := by
    constructor
    · intro hi hd
      have := (heD i).mp hd
      omega
    · intro hi
      by_contra hn
      apply hi
      apply (heD i).mpr
      omega
  refine ⟨K, L, ?_, ?_, hbase, hf1, hf2, hf3, hf4, ?_, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.mp hT
    exact hH {e a, e b, e c}
      (SimpleGraph.is3Clique_iff.mpr ⟨e a, e b, e c, hab, hac, hbc, rfl⟩)
  · intro S hS
    exact hno5 (F S) ⟨hmapInd S hS.isIndepSet, by simpa [F] using hS.card_eq⟩
  · intro u hu
    change (univ.filter (fun v : Fin 12 => 4 ≤ v.val ∧ H.Adj (e u) (e v))).card = 2
    exact (hcount _ _ (fun i => and_congr (hlow i) Iff.rfl)).trans
      (houtside (e u) ((hlow u).mp hu))
  · intro y
    refine ⟨?_, by simpa [L] using (hM y).card_eq⟩
    intro a ha b hb hab hadj
    exact (hM y).isIndepSet ((hL y a).mp ha) ((hL y b).mp hb)
      (fun h => hab (e.injective h)) hadj
  · intro w
    have heq : (univ.filter (fun y : Fin 5 => w ∈ L y)) =
        univ.filter (fun y : Fin 5 => e w ∈ M y) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hL y w
    rw [heq]
    have hb := hbudget (e w)
    split
    · rename_i hw
      have hd := (hclass (e w)).1 ((heD w).mpr hw)
      omega
    · rename_i hw
      have hn : e w ∉ D := fun h => hw ((heD w).mp h)
      have hd := (hclass (e w)).2 hn
      omega
  · intro Y I hY hI havoid
    have hh := hmix Y (F I) hY (hmapInd I hI) (by
      intro y hy w hw
      change w ∈ I.map e.toEmbedding at hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hw
      exact fun hm => havoid y hy i hi ((hL y i).mpr hm))
    simpa [F] using hh

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 32768 in
private lemma r36_cert_sound (H : SimpleGraph (Fin 12)) (M : Fin 5 → Finset (Fin 12))
    (hH : H.CliqueFree 3)
    (hno5 : ∀ s, ¬ H.IsNIndepSet 5 s)
    (hbase : ∀ a b : Fin 12, (a.val < 4 ∨ b.val < 4) →
      (H.Adj a b ↔ (baseAdj12.getD a.val 0).testBit b.val = true))
    (hf1 : ¬ H.Adj ⟨4, by decide⟩ ⟨5, by decide⟩)
    (hf2 : ¬ H.Adj ⟨6, by decide⟩ ⟨7, by decide⟩)
    (hf3 : ¬ H.Adj ⟨8, by decide⟩ ⟨9, by decide⟩)
    (hf4 : ¬ H.Adj ⟨10, by decide⟩ ⟨11, by decide⟩)
    (hdeg2 : ∀ u : Fin 12, 4 ≤ u.val →
      (univ.filter (fun v : Fin 12 => 4 ≤ v.val ∧ H.Adj u v)).card = 2)
    (hM : ∀ y : Fin 5, H.IsNIndepSet 4 (M y))
    (hcov : ∀ w : Fin 12, (univ.filter (fun y : Fin 5 => w ∈ M y)).card = if w.val < 4 then 1 else 2)
    (hno6 : ∀ (Y : Finset (Fin 5)) (I : Finset (Fin 12)),
      Y.Nonempty → H.IsIndepSet (I : Set (Fin 12)) →
      (∀ y ∈ Y, ∀ w ∈ I, w ∉ M y) →
      Y.card + I.card ≤ 5) : False := by
  classical
  -- Finite lookup-table properties verified by `decide`
  have hcand_lt : ∀ idx : Fin 24,
      (candEdges24.getD idx.val (0, 0)).1 < 12 ∧ (candEdges24.getD idx.val (0, 0)).2 < 12 := by
    decide
  have hedgeBit_spec : ∀ (a b : Fin 12) (idx : Fin 24),
      (edgeBit144.getD (a.val * 12 + b.val) 0).testBit idx.val = true ↔
        ((candEdges24.getD idx.val (0, 0)).1 = a.val ∧ (candEdges24.getD idx.val (0, 0)).2 = b.val) ∨
        ((candEdges24.getD idx.val (0, 0)).1 = b.val ∧ (candEdges24.getD idx.val (0, 0)).2 = a.val) := by
    decide
  have hedgeBit_lt : ∀ a b : Fin 12, edgeBit144.getD (a.val * 12 + b.val) 0 < 2 ^ 24 := by
    decide
  have hedgeBit_zero_iff : ∀ a b : Fin 12,
      4 ≤ a.val → 4 ≤ b.val → a ≠ b →
      (edgeBit144.getD (a.val * 12 + b.val) 0 = 0 ↔
        (a.val = 4 ∧ b.val = 5) ∨ (a.val = 5 ∧ b.val = 4) ∨
        (a.val = 6 ∧ b.val = 7) ∨ (a.val = 7 ∧ b.val = 6) ∨
        (a.val = 8 ∧ b.val = 9) ∨ (a.val = 9 ∧ b.val = 8) ∨
        (a.val = 10 ∧ b.val = 11) ∨ (a.val = 11 ∧ b.val = 10)) := by
    decide
  have hinc_spec : ∀ (u : Fin 12) (idx : Fin 24),
      (incMask12.getD u.val 0).testBit idx.val = true ↔
        (candEdges24.getD idx.val (0, 0)).1 = u.val ∨ (candEdges24.getD idx.val (0, 0)).2 = u.val := by
    decide
  have hbase_ge4 : ∀ a b : Fin 12, 4 ≤ a.val → 4 ≤ b.val → (baseAdj12.getD a.val 0).testBit b.val = false := by
    decide
  have hcand_ge4 : ∀ idx : Fin 24,
      4 ≤ (candEdges24.getD idx.val (0, 0)).1 ∧ 4 ≤ (candEdges24.getD idx.val (0, 0)).2 ∧
      (candEdges24.getD idx.val (0, 0)).1 ≠ (candEdges24.getD idx.val (0, 0)).2 := by
    decide
  have hcand_inj : ∀ i j : Fin 24,
      (candEdges24.getD i.val (0, 0)).1 = (candEdges24.getD j.val (0, 0)).1 ∧
      (candEdges24.getD i.val (0, 0)).2 = (candEdges24.getD j.val (0, 0)).2 → i = j := by
    decide
  have hcand_lt_pair : ∀ idx : Fin 24,
      (candEdges24.getD idx.val (0, 0)).1 < (candEdges24.getD idx.val (0, 0)).2 := by
    decide
  have hbit1 : ∀ n : Nat, (1 : Nat).testBit n = decide (n = 0) := by
    intro n
    cases n with
    | zero => rfl
    | succ m =>
        simp only [Nat.succ_ne_zero, decide_false]
        exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
  have hadd_of_and_zero : ∀ a b : Nat, a &&& b = 0 → a + b = a ^^^ b := by
    intro a
    induction a using Nat.binaryRec with
    | zero => intro b _; simp
    | bit b1 a ih =>
        intro b h
        induction b using Nat.binaryRec with
        | zero => simp
        | bit b2 b _ =>
            have h0 := congrArg (fun x => x.testBit 0) h
            rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_bit_zero, Nat.testBit_bit_zero] at h0
            have hrest : a &&& b = 0 := by
              apply Nat.eq_of_testBit_eq; intro k
              have hk := congrArg (fun x => x.testBit (k + 1)) h
              rw [Nat.testBit_and, Nat.zero_testBit, Nat.testBit_bit_succ, Nat.testBit_bit_succ] at hk
              rwa [Nat.testBit_and, Nat.zero_testBit]
            have ihab := ih b hrest
            have hxor : Nat.bit b1 a ^^^ Nat.bit b2 b = Nat.bit (xor b1 b2) (a ^^^ b) := by
              apply Nat.eq_of_testBit_eq; intro k
              cases k with
              | zero => simp [Nat.testBit_xor, Nat.testBit_bit_zero]
              | succ k => simp [Nat.testBit_xor, Nat.testBit_bit_succ]
            rw [hxor, Nat.bit_val, Nat.bit_val, Nat.bit_val]
            cases b1 <;> cases b2 <;> simp at h0 ⊢ <;> omega
  -- Exact edge mask of H on candEdges24
  let hMask : Nat := (List.finRange 24).foldl (fun acc idx =>
    let p := candEdges24.getD idx.val (0, 0)
    if H.Adj ⟨p.1, (hcand_lt idx).1⟩ ⟨p.2, (hcand_lt idx).2⟩ then acc ||| (1 <<< idx.val) else acc) 0
  have hhMask_bit : ∀ idx : Fin 24,
      hMask.testBit idx.val = true ↔
        H.Adj ⟨(candEdges24.getD idx.val (0, 0)).1, (hcand_lt idx).1⟩
              ⟨(candEdges24.getD idx.val (0, 0)).2, (hcand_lt idx).2⟩ := by
    intro idx
    have hfold : ∀ (l : List (Fin 24)) (acc : Nat),
        (l.foldl (fun acc i =>
          let p := candEdges24.getD i.val (0, 0)
          if H.Adj ⟨p.1, (hcand_lt i).1⟩ ⟨p.2, (hcand_lt i).2⟩ then acc ||| (1 <<< i.val) else acc) acc).testBit idx.val =
        (acc.testBit idx.val ||
          (idx ∈ l && decide (H.Adj ⟨(candEdges24.getD idx.val (0, 0)).1, (hcand_lt idx).1⟩
                                    ⟨(candEdges24.getD idx.val (0, 0)).2, (hcand_lt idx).2⟩))) := by
      intro l
      induction l with
      | nil => intro acc; simp
      | cons j rest ih =>
          intro acc
          simp only [List.foldl_cons, ih]
          by_cases hji : j = idx
          · subst hji
            by_cases hadj : H.Adj ⟨(candEdges24.getD j.val (0, 0)).1, (hcand_lt j).1⟩
                                  ⟨(candEdges24.getD j.val (0, 0)).2, (hcand_lt j).2⟩
            · rw [if_pos hadj, Nat.testBit_or, Nat.testBit_shiftLeft, hbit1]
              simp only [Nat.le_refl, decide_true, Nat.sub_self, Bool.and_true, Bool.or_true, Bool.true_or, List.mem_cons, true_or, hadj]
            · rw [if_neg hadj]
              simp only [List.mem_cons, true_or, decide_true, Bool.true_and, decide_eq_false_iff_not.mpr hadj, Bool.and_false, Bool.or_false]
          · have hne : j.val ≠ idx.val := fun h => hji (Fin.ext h)
            by_cases hadj : H.Adj ⟨(candEdges24.getD j.val (0, 0)).1, (hcand_lt j).1⟩
                                  ⟨(candEdges24.getD j.val (0, 0)).2, (hcand_lt j).2⟩
            · rw [if_pos hadj, Nat.testBit_or, Nat.testBit_shiftLeft, hbit1]
              have : (decide (j.val ≤ idx.val) && decide (idx.val - j.val = 0)) = false := by
                by_cases hle : j.val ≤ idx.val
                · simp [hle, show idx.val - j.val ≠ 0 by omega]
                · simp [hle]
              rw [this, Bool.or_false]; simp [hji, Ne.symm hji]
            · rw [if_neg hadj]; simp [hji, Ne.symm hji]
    have h := hfold (List.finRange 24) 0
    simp only [Nat.zero_testBit, Bool.false_or, List.mem_finRange, decide_true, Bool.true_and] at h
    change hMask.testBit idx.val = true ↔ _
    rw [h, decide_eq_true_eq]
  have hhMask_hi : ∀ k : Nat, 24 ≤ k → hMask.testBit k = false := by
    intro k hk
    have hfold : ∀ (l : List (Fin 24)) (acc : Nat),
        acc.testBit k = false →
        (l.foldl (fun acc i =>
          let p := candEdges24.getD i.val (0, 0)
          if H.Adj ⟨p.1, (hcand_lt i).1⟩ ⟨p.2, (hcand_lt i).2⟩ then acc ||| (1 <<< i.val) else acc) acc).testBit k = false := by
      intro l
      induction l with
      | nil => intro acc h; exact h
      | cons j rest ih =>
          intro acc h
          simp only [List.foldl_cons]
          apply ih
          by_cases hadj : H.Adj ⟨(candEdges24.getD j.val (0, 0)).1, (hcand_lt j).1⟩
                                ⟨(candEdges24.getD j.val (0, 0)).2, (hcand_lt j).2⟩
          · rw [if_pos hadj, Nat.testBit_or, h, Bool.false_or, Nat.testBit_shiftLeft]
            have hlt : j.val < k := lt_of_lt_of_le j.isLt hk
            have : decide (j.val ≤ k) = true := by simp [Nat.le_of_lt hlt]
            rw [hbit1]; simp [this, show k - j.val ≠ 0 by omega]
          · rw [if_neg hadj]; exact h
    exact hfold (List.finRange 24) 0 (by simp)
  -- Helper: pop24 m equals card of Fin 24 with m.testBit i = true
  have hpop24 : ∀ m : Nat, pop24 m = (univ.filter (fun i : Fin 24 => m.testBit i.val = true)).card := by
    intro m
    dsimp [pop24]
    rw [List.countP_eq_length_filter]
    have h1 : ((List.range 24).filter (fun i => m.testBit i)).length =
        ((List.finRange 24).filter (fun i : Fin 24 => m.testBit i.val)).length := by
      have : List.range 24 = (List.finRange 24).map Fin.val := by
        apply List.ext_getElem <;> simp
      rw [this, List.filter_map, List.length_map]
      rfl
    rw [h1]
    have hnd : ((List.finRange 24).filter (fun i : Fin 24 => m.testBit i.val)).Nodup :=
      (List.nodup_finRange 24).filter _
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext i
    simp [List.mem_toFinset, List.mem_filter]
  -- Helper: for u >= 4, the Fin 24 indices incident to u with H.Adj have card = 2
  have hhMask_deg : ∀ u : Fin 12, 4 ≤ u.val →
      (univ.filter (fun idx : Fin 24 => (hMask &&& incMask12.getD u.val 0).testBit idx.val = true)).card = 2 := by
    intro u hu
    let S := univ.filter (fun v : Fin 12 => 4 ≤ v.val ∧ H.Adj u v)
    let T := univ.filter (fun idx : Fin 24 => (hMask &&& incMask12.getD u.val 0).testBit idx.val = true)
    have hcardS : S.card = 2 := hdeg2 u hu
    rw [← hcardS]
    refine Finset.card_bij (fun idx _ =>
      let p := candEdges24.getD idx.val (0, 0)
      if p.1 = u.val then ⟨p.2, (hcand_lt idx).2⟩ else ⟨p.1, (hcand_lt idx).1⟩) ?_ ?_ ?_
    · intro idx hidx
      have hbit := (Finset.mem_filter.mp hidx).2
      rw [Nat.testBit_and, Bool.and_eq_true] at hbit
      have hadj := (hhMask_bit idx).mp hbit.1
      have hinc := (hinc_spec u idx).mp hbit.2
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hinc with h1 | h2
      · rw [if_pos h1]
        refine ⟨(hcand_ge4 idx).2.1, ?_⟩
        have hu1 : (⟨(candEdges24.getD idx.val (0, 0)).1, (hcand_lt idx).1⟩ : Fin 12) = u := Fin.ext h1
        rwa [hu1] at hadj
      · have hne1 : (candEdges24.getD idx.val (0, 0)).1 ≠ u.val := by
          rw [← h2]; exact (hcand_ge4 idx).2.2
        rw [if_neg hne1]
        refine ⟨(hcand_ge4 idx).1, ?_⟩
        have hu2 : (⟨(candEdges24.getD idx.val (0, 0)).2, (hcand_lt idx).2⟩ : Fin 12) = u := Fin.ext h2
        rw [hu2] at hadj
        exact hadj.symm
    · intro i hi j hj heq
      have hbi := (Finset.mem_filter.mp hi).2
      have hbj := (Finset.mem_filter.mp hj).2
      rw [Nat.testBit_and, Bool.and_eq_true] at hbi hbj
      have hinci := (hinc_spec u i).mp hbi.2
      have hincj := (hinc_spec u j).mp hbj.2
      have hlti := hcand_lt_pair i
      have hltj := hcand_lt_pair j
      apply hcand_inj
      rcases hinci with hi1 | hi2 <;> rcases hincj with hj1 | hj2
      · rw [if_pos hi1, if_pos hj1] at heq
        exact ⟨hi1.trans hj1.symm, congrArg Fin.val heq⟩
      · have hnej : (candEdges24.getD j.val (0, 0)).1 ≠ u.val := by rw [← hj2]; exact (hcand_ge4 j).2.2
        rw [if_pos hi1, if_neg hnej] at heq
        have hval := congrArg Fin.val heq
        dsimp at hval
        omega
      · have hnei : (candEdges24.getD i.val (0, 0)).1 ≠ u.val := by rw [← hi2]; exact (hcand_ge4 i).2.2
        rw [if_neg hnei, if_pos hj1] at heq
        have hval := congrArg Fin.val heq
        dsimp at hval
        omega
      · have hnei : (candEdges24.getD i.val (0, 0)).1 ≠ u.val := by rw [← hi2]; exact (hcand_ge4 i).2.2
        have hnej : (candEdges24.getD j.val (0, 0)).1 ≠ u.val := by rw [← hj2]; exact (hcand_ge4 j).2.2
        rw [if_neg hnei, if_neg hnej] at heq
        exact ⟨congrArg Fin.val heq, hi2.trans hj2.symm⟩
    · intro v hv
      obtain ⟨hv4, huv⟩ := (Finset.mem_filter.mp hv).2
      have hne : u ≠ v := huv.ne
      have hnz : edgeBit144.getD (u.val * 12 + v.val) 0 ≠ 0 := by
        intro hz
        have hforb := (hedgeBit_zero_iff u v hu hv4 hne).mp hz
        rcases hforb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hf1 (by rwa [show u = ⟨4, by decide⟩ from Fin.ext h1, show v = ⟨5, by decide⟩ from Fin.ext h2] at huv)
        · exact hf1 (by have h := huv.symm; rwa [show v = ⟨4, by decide⟩ from Fin.ext h2, show u = ⟨5, by decide⟩ from Fin.ext h1] at h)
        · exact hf2 (by rwa [show u = ⟨6, by decide⟩ from Fin.ext h1, show v = ⟨7, by decide⟩ from Fin.ext h2] at huv)
        · exact hf2 (by have h := huv.symm; rwa [show v = ⟨6, by decide⟩ from Fin.ext h2, show u = ⟨7, by decide⟩ from Fin.ext h1] at h)
        · exact hf3 (by rwa [show u = ⟨8, by decide⟩ from Fin.ext h1, show v = ⟨9, by decide⟩ from Fin.ext h2] at huv)
        · exact hf3 (by have h := huv.symm; rwa [show v = ⟨8, by decide⟩ from Fin.ext h2, show u = ⟨9, by decide⟩ from Fin.ext h1] at h)
        · exact hf4 (by rwa [show u = ⟨10, by decide⟩ from Fin.ext h1, show v = ⟨11, by decide⟩ from Fin.ext h2] at huv)
        · exact hf4 (by have h := huv.symm; rwa [show v = ⟨10, by decide⟩ from Fin.ext h2, show u = ⟨11, by decide⟩ from Fin.ext h1] at h)
      have hex : ∃ idx : Fin 24, (edgeBit144.getD (u.val * 12 + v.val) 0).testBit idx.val = true := by
        by_contra hall
        push Not at hall
        apply hnz
        apply Nat.eq_of_testBit_eq
        intro k
        simp only [Nat.zero_testBit]
        by_cases hk : k < 24
        · exact Bool.eq_false_iff.mpr (hall ⟨k, hk⟩)
        · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (hedgeBit_lt u v) (Nat.pow_le_pow_right (by omega) (by omega)))
      obtain ⟨idx, hidx⟩ := hex
      have hsp := (hedgeBit_spec u v idx).mp hidx
      refine ⟨idx, ?_, ?_⟩
      · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Nat.testBit_and, Bool.and_eq_true]
        constructor
        · rw [hhMask_bit idx]
          rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · convert huv <;> exact Fin.ext ‹_›
          · convert huv.symm <;> exact Fin.ext ‹_›
        · rw [hinc_spec u idx]
          rcases hsp with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact Or.inl h1
          · exact Or.inr h2
      · rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [if_pos h1]; exact Fin.ext h2
        · have hne1 : (candEdges24.getD idx.val (0, 0)).1 ≠ u.val := by
            rw [h1]; exact fun h => hne (Fin.ext h.symm)
          rw [if_neg hne1]; exact Fin.ext h1
  -- Soundness of isAdjYes and isAdjPoss under yes <= hMask and no disjoint from hMask
  have hisAdjYes_imp : ∀ (yes : Nat), (∀ i : Fin 24, yes.testBit i.val = true → hMask.testBit i.val = true) →
      ∀ a b : Fin 12, isAdjYes yes a.val b.val = true → H.Adj a b := by
    intro yes hyes a b h
    simp only [isAdjYes, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    rcases h with hb | he
    · by_cases hab : a.val < 4 ∨ b.val < 4
      · exact (hbase a b hab).mpr hb
      · rw [hbase_ge4 a b (by omega) (by omega)] at hb; cases hb
    · have hex : ∃ idx : Fin 24, (yes &&& edgeBit144.getD (a.val * 12 + b.val) 0).testBit idx.val = true := by
        by_contra hall
        push Not at hall
        apply he
        apply Nat.eq_of_testBit_eq
        intro k
        simp only [Nat.zero_testBit]
        by_cases hk : k < 24
        · exact Bool.eq_false_iff.mpr (hall ⟨k, hk⟩)
        · rw [Nat.testBit_and, Nat.testBit_lt_two_pow (lt_of_lt_of_le (hedgeBit_lt a b) (Nat.pow_le_pow_right (by omega) (by omega))), Bool.and_false]
      obtain ⟨idx, hidx⟩ := hex
      rw [Nat.testBit_and, Bool.and_eq_true] at hidx
      have hadj := (hhMask_bit idx).mp (hyes idx hidx.1)
      have hsp := (hedgeBit_spec a b idx).mp hidx.2
      rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [show a = ⟨(candEdges24.getD idx.val (0, 0)).1, (hcand_lt idx).1⟩ from Fin.ext h1.symm,
            show b = ⟨(candEdges24.getD idx.val (0, 0)).2, (hcand_lt idx).2⟩ from Fin.ext h2.symm]; exact hadj
      · rw [show b = ⟨(candEdges24.getD idx.val (0, 0)).1, (hcand_lt idx).1⟩ from Fin.ext h1.symm,
            show a = ⟨(candEdges24.getD idx.val (0, 0)).2, (hcand_lt idx).2⟩ from Fin.ext h2.symm]; exact hadj.symm
  have hisAdjPoss_of_adj : ∀ (yes no : Nat),
      (∀ i : Fin 24, no.testBit i.val = true → hMask.testBit i.val = false) →
      (∀ k, 24 ≤ k → no.testBit k = false) →
      ∀ a b : Fin 12, H.Adj a b → isAdjPoss yes no a.val b.val = true := by
    intro yes no hno hno_hi a b hadj
    simp only [isAdjPoss, Bool.or_eq_true, bne_iff_ne, ne_eq]
    by_cases hab : a.val < 4 ∨ b.val < 4
    · exact Or.inl ((hbase a b hab).mp hadj)
    · right
      have ha4 : 4 ≤ a.val := by omega
      have hb4 : 4 ≤ b.val := by omega
      have hne : a ≠ b := hadj.ne
      have hnz : edgeBit144.getD (a.val * 12 + b.val) 0 ≠ 0 := by
        intro hz
        have hforb := (hedgeBit_zero_iff a b ha4 hb4 hne).mp hz
        rcases hforb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hf1 (by rwa [show a = ⟨4, by decide⟩ from Fin.ext h1, show b = ⟨5, by decide⟩ from Fin.ext h2] at hadj)
        · exact hf1 (by have h := hadj.symm; rwa [show b = ⟨4, by decide⟩ from Fin.ext h2, show a = ⟨5, by decide⟩ from Fin.ext h1] at h)
        · exact hf2 (by rwa [show a = ⟨6, by decide⟩ from Fin.ext h1, show b = ⟨7, by decide⟩ from Fin.ext h2] at hadj)
        · exact hf2 (by have h := hadj.symm; rwa [show b = ⟨6, by decide⟩ from Fin.ext h2, show a = ⟨7, by decide⟩ from Fin.ext h1] at h)
        · exact hf3 (by rwa [show a = ⟨8, by decide⟩ from Fin.ext h1, show b = ⟨9, by decide⟩ from Fin.ext h2] at hadj)
        · exact hf3 (by have h := hadj.symm; rwa [show b = ⟨8, by decide⟩ from Fin.ext h2, show a = ⟨9, by decide⟩ from Fin.ext h1] at h)
        · exact hf4 (by rwa [show a = ⟨10, by decide⟩ from Fin.ext h1, show b = ⟨11, by decide⟩ from Fin.ext h2] at hadj)
        · exact hf4 (by have h := hadj.symm; rwa [show b = ⟨10, by decide⟩ from Fin.ext h2, show a = ⟨11, by decide⟩ from Fin.ext h1] at h)
      have hex : ∃ idx : Fin 24, (edgeBit144.getD (a.val * 12 + b.val) 0).testBit idx.val = true := by
        by_contra hall; push Not at hall; apply hnz; apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.zero_testBit]
        by_cases hk : k < 24
        · exact Bool.eq_false_iff.mpr (hall ⟨k, hk⟩)
        · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (hedgeBit_lt a b) (Nat.pow_le_pow_right (by omega) (by omega)))
      obtain ⟨idx, hidx⟩ := hex
      have hsp := (hedgeBit_spec a b idx).mp hidx
      have hhm : hMask.testBit idx.val = true := by
        rw [hhMask_bit idx]
        rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · convert hadj <;> exact Fin.ext ‹_›
        · convert hadj.symm <;> exact Fin.ext ‹_›
      have hno0 : no.testBit idx.val = false := by
        by_cases hb : no.testBit idx.val = true
        · have := hno idx hb; rw [hhm] at this; cases this
        · exact Bool.eq_false_iff.mpr hb
      have hno_le : no < 2 ^ 24 := by
        by_contra hge
        have hlt : 0 < no / 2 ^ 24 := Nat.div_pos (by omega) (by decide)
        have hexk : ∃ k, (no / 2 ^ 24).testBit k = true := by
          by_contra h0; push Not at h0
          have : no / 2 ^ 24 = 0 := Nat.eq_of_testBit_eq fun k => by simpa using Bool.eq_false_iff.mpr (h0 k)
          omega
        obtain ⟨k, hk⟩ := hexk
        rw [Nat.testBit_div_two_pow] at hk
        have := hno_hi (k + 24) (by omega)
        rw [hk] at this; cases this
      have hsub_bit : (16777215 - no).testBit idx.val = true := by
        have hsum : no + (16777215 - no) = 16777215 := by omega
        have hxor : 16777215 - no = 16777215 ^^^ no := by
          have : (16777215 ^^^ no) + no = 16777215 := by
            have hdisj : (16777215 ^^^ no) &&& no = 0 := by
              apply Nat.eq_of_testBit_eq; intro k
              rw [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
              by_cases hk : k < 24
              · have h1 : (16777215 : Nat).testBit k = true := by
                  have : ∀ j : Fin 24, (16777215 : Nat).testBit j.val = true := by decide
                  exact this ⟨k, hk⟩
                rw [h1]; cases no.testBit k <;> rfl
              · rw [hno_hi k (by omega)]; simp
            rw [hadd_of_and_zero _ _ hdisj]
            apply Nat.eq_of_testBit_eq; intro k
            rw [Nat.testBit_xor, Nat.testBit_xor]
            cases no.testBit k <;> simp
          omega
        rw [hxor, Nat.testBit_xor, hno0]
        have h1 : (16777215 : Nat).testBit idx.val = true := by
          have : ∀ j : Fin 24, (16777215 : Nat).testBit j.val = true := by decide
          exact this idx
        simp [h1]
      intro hz
      have := congrArg (fun x => x.testBit idx.val) hz
      rw [Nat.testBit_and, hsub_bit, hidx] at this
      simp at this
  -- Helper: when degYes yes u == 2 for all u in 4..11, yes = hMask!
  have hyes_eq_hMask : ∀ yes : Nat,
      (∀ i : Fin 24, yes.testBit i.val = true → hMask.testBit i.val = true) →
      (∀ k, 24 ≤ k → yes.testBit k = false) →
      ((List.range 8).all (fun i => degYes yes (i + 4) == 2)) = true →
      yes = hMask := by
    intro yes hyes hyes_hi hall
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 24
    · let idx : Fin 24 := ⟨k, hk⟩
      by_cases hy : yes.testBit k = true
      · rw [hy, hyes idx hy]
      · have hyf : yes.testBit k = false := Bool.eq_false_iff.mpr hy
        rw [hyf]
        symm
        by_contra hhm
        have hhmt : hMask.testBit k = true := Bool.eq_true_of_not_eq_false hhm
        let u : Fin 12 := ⟨(candEdges24.getD k (0, 0)).1, (hcand_lt idx).1⟩
        have hu4 : 4 ≤ u.val := (hcand_ge4 idx).1
        have hu_deg2 : degYes yes u.val = 2 := by
          simp only [List.all_eq_true, beq_iff_eq] at hall
          have hmem : u.val - 4 ∈ List.range 8 := List.mem_range.mpr (by omega)
          have := hall (u.val - 4) hmem
          rwa [show u.val - 4 + 4 = u.val by omega] at this
        have hsub : univ.filter (fun i : Fin 24 => (yes &&& incMask12.getD u.val 0).testBit i.val = true) ⊂
            univ.filter (fun i : Fin 24 => (hMask &&& incMask12.getD u.val 0).testBit i.val = true) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨idx, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.testBit_and, Bool.and_eq_true]
              exact ⟨hhmt, (hinc_spec u idx).mpr (Or.inl rfl)⟩
            · simp [idx, hyf]
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.testBit_and, Bool.and_eq_true] at hi ⊢
            exact ⟨hyes i hi.1, hi.2⟩
        have hlt := Finset.card_lt_card hsub
        rw [← hpop24, show pop24 (yes &&& incMask12.getD u.val 0) = degYes yes u.val from rfl,
            hu_deg2, hhMask_deg u hu4] at hlt
        omega
    · rw [hyes_hi k (by omega), hhMask_hi k (by omega)]
  -- Part 1: Walk s3TreeCert to prove hMask = swapMasks16[bits] for some bits < 16!
  have hs3_walk : ∀ (t : S3Tree) (yes no : Nat),
      checkS3Tree t yes no = true →
      (∀ i : Fin 24, yes.testBit i.val = true → hMask.testBit i.val = true) →
      (∀ i : Fin 24, no.testBit i.val = true → hMask.testBit i.val = false) →
      (∀ k, 24 ≤ k → yes.testBit k = false) →
      (∀ k, 24 ≤ k → no.testBit k = false) →
      ∃ bits : Fin 16, hMask = swapMasks16.getD bits.val 0 := by
    intro t
    induction t with
    | degHi u =>
        intro yes no hchk hyes _ _ _
        simp only [checkS3Tree, Bool.and_eq_true, decide_eq_true_eq] at hchk
        rcases hchk with ⟨⟨hu4, hu12⟩, hgt⟩
        have hle : degYes yes u ≤ 2 := by
          dsimp [degYes]
          rw [hpop24, ← hhMask_deg ⟨u, hu12⟩ hu4]
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.testBit_and, Bool.and_eq_true] at hi ⊢
          exact ⟨hyes i hi.1, hi.2⟩
        omega
    | degLo u =>
        intro yes no hchk _ hno _ hno_hi
        simp only [checkS3Tree, Bool.and_eq_true, decide_eq_true_eq] at hchk
        rcases hchk with ⟨⟨hu4, hu12⟩, hlt⟩
        have hge : 2 ≤ degPoss yes no u := by
          dsimp [degPoss]
          rw [hpop24, ← hhMask_deg ⟨u, hu12⟩ hu4]
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.testBit_and, Bool.and_eq_true] at hi ⊢
          refine ⟨?_, hi.2⟩
          have hno0 : no.testBit i.val = false := by
            by_cases hb : no.testBit i.val = true
            · have := hno i hb; rw [hi.1] at this; cases this
            · exact Bool.eq_false_iff.mpr hb
          have hno_le : no < 2 ^ 24 := by
            by_contra hge2
            have hpos : 0 < no / 2 ^ 24 := Nat.div_pos (by omega) (by decide)
            have hexk : ∃ k, (no / 2 ^ 24).testBit k = true := by
              by_contra h0; push Not at h0
              have : no / 2 ^ 24 = 0 := Nat.eq_of_testBit_eq fun k => by simpa using Bool.eq_false_iff.mpr (h0 k)
              omega
            obtain ⟨k, hk⟩ := hexk; rw [Nat.testBit_div_two_pow] at hk
            have := hno_hi (k + 24) (by omega); rw [hk] at this; cases this
          have hxor : 16777215 - no = 16777215 ^^^ no := by
            have : (16777215 ^^^ no) + no = 16777215 := by
              have hdisj : (16777215 ^^^ no) &&& no = 0 := by
                apply Nat.eq_of_testBit_eq; intro k
                rw [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
                by_cases hk : k < 24
                · have h1 : (16777215 : Nat).testBit k = true := by
                    have : ∀ j : Fin 24, (16777215 : Nat).testBit j.val = true := by decide
                    exact this ⟨k, hk⟩
                  rw [h1]; cases no.testBit k <;> rfl
                · rw [hno_hi k (by omega)]; simp
              rw [hadd_of_and_zero _ _ hdisj]
              apply Nat.eq_of_testBit_eq; intro k; rw [Nat.testBit_xor, Nat.testBit_xor]; cases no.testBit k <;> simp
            omega
          rw [hxor, Nat.testBit_xor, hno0]
          have h1 : (16777215 : Nat).testBit i.val = true := by
            have : ∀ j : Fin 24, (16777215 : Nat).testBit j.val = true := by decide
            exact this i
          simp [h1]
        omega
    | tri a b c =>
        intro yes _ hchk hyes _ _ _
        simp only [checkS3Tree, Bool.and_eq_true, decide_eq_true_eq] at hchk
        rcases hchk with ⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hab⟩, hac⟩, hbc⟩
        exact (hH {⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩} (SimpleGraph.is3Clique_iff.mpr
          ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩,
            hisAdjYes_imp yes hyes ⟨a, ha⟩ ⟨b, hb⟩ hab,
            hisAdjYes_imp yes hyes ⟨a, ha⟩ ⟨c, hc⟩ hac,
            hisAdjYes_imp yes hyes ⟨b, hb⟩ ⟨c, hc⟩ hbc, rfl⟩)).elim
    | ind5 a b c d e =>
        intro yes no hchk _ hno _ hno_hi
        simp only [checkS3Tree, checkInd5, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hchk
        rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hab, hbc⟩, hcd⟩, hde⟩, he12⟩, nab⟩, nac⟩, nad⟩, nae⟩, nbc⟩, nbd⟩, nbe⟩, ncd⟩, nce⟩, nde⟩
        let va : Fin 12 := ⟨a, by omega⟩
        let vb : Fin 12 := ⟨b, by omega⟩
        let vc : Fin 12 := ⟨c, by omega⟩
        let vd : Fin 12 := ⟨d, by omega⟩
        let ve : Fin 12 := ⟨e, by omega⟩
        have hnot : ∀ x y : Fin 12, isAdjPoss yes no x.val y.val = false → ¬ H.Adj x y := fun x y hf hadj => by
          have := hisAdjPoss_of_adj yes no hno hno_hi x y hadj; rw [hf] at this; cases this
        refine (hno5 {va, vb, vc, vd, ve} ⟨?_, ?_⟩).elim
        · intro x hx y hy hxy hadj
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl
          · exact hxy rfl
          · exact hnot va vb nab hadj
          · exact hnot va vc nac hadj
          · exact hnot va vd nad hadj
          · exact hnot va ve nae hadj
          · exact hnot va vb nab hadj.symm
          · exact hxy rfl
          · exact hnot vb vc nbc hadj
          · exact hnot vb vd nbd hadj
          · exact hnot vb ve nbe hadj
          · exact hnot va vc nac hadj.symm
          · exact hnot vb vc nbc hadj.symm
          · exact hxy rfl
          · exact hnot vc vd ncd hadj
          · exact hnot vc ve nce hadj
          · exact hnot va vd nad hadj.symm
          · exact hnot vb vd nbd hadj.symm
          · exact hnot vc vd ncd hadj.symm
          · exact hxy rfl
          · exact hnot vd ve nde hadj
          · exact hnot va ve nae hadj.symm
          · exact hnot vb ve nbe hadj.symm
          · exact hnot vc ve nce hadj.symm
          · exact hnot vd ve nde hadj.symm
          · exact hxy rfl
        · have hne : va ≠ vb ∧ va ≠ vc ∧ va ≠ vd ∧ va ≠ ve ∧ vb ≠ vc ∧ vb ≠ vd ∧ vb ≠ ve ∧ vc ≠ vd ∧ vc ≠ ve ∧ vd ≠ ve := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; have := congrArg Fin.val h; dsimp [va, vb, vc, vd, ve] at this; omega)
          simp [Finset.card_insert_of_notMem, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1,
            hne.2.2.2.2.2.1, hne.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.2.2]
    | ind5Full a b c d e =>
        intro yes _ hchk hyes _ hyes_hi _
        simp only [checkS3Tree, checkInd5, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hchk
        rcases hchk with ⟨hall, hchk5⟩
        rcases hchk5 with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hab, hbc⟩, hcd⟩, hde⟩, he12⟩, nab⟩, nac⟩, nad⟩, nae⟩, nbc⟩, nbd⟩, nbe⟩, ncd⟩, nce⟩, nde⟩
        have heqM : yes = hMask := hyes_eq_hMask yes hyes hyes_hi hall
        have hnot : ∀ x y : Fin 12, isAdjYes yes x.val y.val = false → ¬ H.Adj x y := fun x y hf hadj => by
          have : isAdjYes hMask x.val y.val = true := by
            simp only [isAdjYes, Bool.or_eq_true, bne_iff_ne, ne_eq]
            by_cases hxy : x.val < 4 ∨ y.val < 4
            · exact Or.inl ((hbase x y hxy).mp hadj)
            · right
              have hx4 : 4 ≤ x.val := by omega
              have hy4 : 4 ≤ y.val := by omega
              have hne : x ≠ y := hadj.ne
              have hnz : edgeBit144.getD (x.val * 12 + y.val) 0 ≠ 0 := by
                intro hz
                have hforb := (hedgeBit_zero_iff x y hx4 hy4 hne).mp hz
                rcases hforb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact hf1 (by rwa [show x = ⟨4, by decide⟩ from Fin.ext h1, show y = ⟨5, by decide⟩ from Fin.ext h2] at hadj)
                · exact hf1 (by have h := hadj.symm; rwa [show y = ⟨4, by decide⟩ from Fin.ext h2, show x = ⟨5, by decide⟩ from Fin.ext h1] at h)
                · exact hf2 (by rwa [show x = ⟨6, by decide⟩ from Fin.ext h1, show y = ⟨7, by decide⟩ from Fin.ext h2] at hadj)
                · exact hf2 (by have h := hadj.symm; rwa [show y = ⟨6, by decide⟩ from Fin.ext h2, show x = ⟨7, by decide⟩ from Fin.ext h1] at h)
                · exact hf3 (by rwa [show x = ⟨8, by decide⟩ from Fin.ext h1, show y = ⟨9, by decide⟩ from Fin.ext h2] at hadj)
                · exact hf3 (by have h := hadj.symm; rwa [show y = ⟨8, by decide⟩ from Fin.ext h2, show x = ⟨9, by decide⟩ from Fin.ext h1] at h)
                · exact hf4 (by rwa [show x = ⟨10, by decide⟩ from Fin.ext h1, show y = ⟨11, by decide⟩ from Fin.ext h2] at hadj)
                · exact hf4 (by have h := hadj.symm; rwa [show y = ⟨10, by decide⟩ from Fin.ext h2, show x = ⟨11, by decide⟩ from Fin.ext h1] at h)
              have hex : ∃ idx : Fin 24, (edgeBit144.getD (x.val * 12 + y.val) 0).testBit idx.val = true := by
                by_contra h0; push Not at h0; apply hnz; apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.zero_testBit]
                by_cases hk : k < 24
                · exact Bool.eq_false_iff.mpr (h0 ⟨k, hk⟩)
                · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (hedgeBit_lt x y) (Nat.pow_le_pow_right (by omega) (by omega)))
              obtain ⟨idx, hidx⟩ := hex
              have hsp := (hedgeBit_spec x y idx).mp hidx
              have hhm : hMask.testBit idx.val = true := by
                rw [hhMask_bit idx]
                rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · convert hadj <;> exact Fin.ext ‹_›
                · convert hadj.symm <;> exact Fin.ext ‹_›
              intro hz
              have := congrArg (fun z => z.testBit idx.val) hz
              rw [Nat.testBit_and, hhm, hidx] at this; simp at this
          rw [heqM, this] at hf; cases hf
        let va : Fin 12 := ⟨a, by omega⟩
        let vb : Fin 12 := ⟨b, by omega⟩
        let vc : Fin 12 := ⟨c, by omega⟩
        let vd : Fin 12 := ⟨d, by omega⟩
        let ve : Fin 12 := ⟨e, by omega⟩
        refine (hno5 {va, vb, vc, vd, ve} ⟨?_, ?_⟩).elim
        · intro x hx y hy hxy hadj
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl | rfl
          · exact hxy rfl
          · exact hnot va vb nab hadj
          · exact hnot va vc nac hadj
          · exact hnot va vd nad hadj
          · exact hnot va ve nae hadj
          · exact hnot va vb nab hadj.symm
          · exact hxy rfl
          · exact hnot vb vc nbc hadj
          · exact hnot vb vd nbd hadj
          · exact hnot vb ve nbe hadj
          · exact hnot va vc nac hadj.symm
          · exact hnot vb vc nbc hadj.symm
          · exact hxy rfl
          · exact hnot vc vd ncd hadj
          · exact hnot vc ve nce hadj
          · exact hnot va vd nad hadj.symm
          · exact hnot vb vd nbd hadj.symm
          · exact hnot vc vd ncd hadj.symm
          · exact hxy rfl
          · exact hnot vd ve nde hadj
          · exact hnot va ve nae hadj.symm
          · exact hnot vb ve nbe hadj.symm
          · exact hnot vc ve nce hadj.symm
          · exact hnot vd ve nde hadj.symm
          · exact hxy rfl
        · have hne : va ≠ vb ∧ va ≠ vc ∧ va ≠ vd ∧ va ≠ ve ∧ vb ≠ vc ∧ vb ≠ vd ∧ vb ≠ ve ∧ vc ≠ vd ∧ vc ≠ ve ∧ vd ≠ ve := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; have := congrArg Fin.val h; dsimp [va, vb, vc, vd, ve] at this; omega)
          simp [Finset.card_insert_of_notMem, hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1,
            hne.2.2.2.2.2.1, hne.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.2.2]
    | valid bits =>
        intro yes _ hchk hyes _ hyes_hi _
        simp only [checkS3Tree, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
        rcases hchk with ⟨⟨hbits, hall⟩, heq⟩
        exact ⟨⟨bits, hbits⟩, (hyes_eq_hMask yes hyes hyes_hi hall).symm.trans heq⟩
    | branch idx t1 t2 ih1 ih2 =>
        intro yes no hchk hyes hno hyes_hi hno_hi
        simp only [checkS3Tree, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hchk
        rcases hchk with ⟨⟨⟨⟨hidx, _⟩, _⟩, ht1⟩, ht2⟩
        by_cases hbit : hMask.testBit idx = true
        · refine ih1 (yes ||| (1 <<< idx)) no ht1 ?_ hno ?_ hno_hi
          · intro i hi
            rw [Nat.testBit_or, Bool.or_eq_true] at hi
            rcases hi with h1 | h2
            · exact hyes i h1
            · rw [Nat.testBit_shiftLeft] at h2
              have hieq : i.val = idx := by
                simp only [Bool.and_eq_true, decide_eq_true_eq, hbit1] at h2
                omega
              rwa [hieq]
          · intro k hk
            rw [Nat.testBit_or, hyes_hi k hk, Bool.false_or, Nat.testBit_shiftLeft]
            have : decide (idx ≤ k) = true := by simp [show idx ≤ k by omega]
            rw [hbit1]; simp [this, show k - idx ≠ 0 by omega]
        · have hbitf : hMask.testBit idx = false := Bool.eq_false_iff.mpr hbit
          refine ih2 yes (no ||| (1 <<< idx)) ht2 hyes ?_ hyes_hi ?_
          · intro i hi
            rw [Nat.testBit_or, Bool.or_eq_true] at hi
            rcases hi with h1 | h2
            · exact hno i h1
            · rw [Nat.testBit_shiftLeft] at h2
              have hieq : i.val = idx := by
                simp only [Bool.and_eq_true, decide_eq_true_eq, hbit1] at h2
                omega
              rwa [hieq]
          · intro k hk
            rw [Nat.testBit_or, hno_hi k hk, Bool.false_or, Nat.testBit_shiftLeft]
            have : decide (idx ≤ k) = true := by simp [show idx ≤ k by omega]
            rw [hbit1]; simp [this, show k - idx ≠ 0 by omega]
  obtain ⟨bits, hMask_eq⟩ := hs3_walk s3TreeCert 0 0 r36_cert_verify.1
    (fun _ h => by simp at h) (fun _ h => by simp at h) (fun _ _ => by simp) (fun _ _ => by simp)
  -- Transport along swapVert bits : Fin 12 ≃ Fin 12 to canonical H0!
  have hswap_lt : ∀ (b : Fin 16) (v : Fin 12), swapVert b.val v.val < 12 := by decide
  have hswap_inv : ∀ (b : Fin 16) (v : Fin 12), swapVert b.val (swapVert b.val v.val) = v.val := by decide
  have hswap_lt4 : ∀ (b : Fin 16) (v : Fin 12), swapVert b.val v.val < 4 ↔ v.val < 4 := by decide
  let sw : Fin 12 ≃ Fin 12 :=
    { toFun := fun v => ⟨swapVert bits.val v.val, hswap_lt bits v⟩
      invFun := fun v => ⟨swapVert bits.val v.val, hswap_lt bits v⟩
      left_inv := fun v => Fin.ext (hswap_inv bits v)
      right_inv := fun v => Fin.ext (hswap_inv bits v) }
  have hH_iff_H0 : ∀ a b : Fin 12,
      H.Adj a b ↔ (h0Adj12.getD (sw a).val 0).testBit (sw b).val = true := by
    intro a b
    have hchkS := r36_cert_verify.2.1
    simp only [checkSwapMasks, List.all_eq_true, beq_iff_eq] at hchkS
    have hswEq := hchkS bits.val (List.mem_range.mpr bits.isLt) a.val (List.mem_range.mpr a.isLt) b.val (List.mem_range.mpr b.isLt)
    rw [← hMask_eq] at hswEq
    change H.Adj a b ↔ (h0Adj12.getD (swapVert bits.val a.val) 0).testBit (swapVert bits.val b.val) = true
    rw [← hswEq]
    constructor
    · intro hadj
      simp only [isAdjYes, Bool.or_eq_true, bne_iff_ne, ne_eq]
      by_cases hab : a.val < 4 ∨ b.val < 4
      · exact Or.inl ((hbase a b hab).mp hadj)
      · right
        have ha4 : 4 ≤ a.val := by omega
        have hb4 : 4 ≤ b.val := by omega
        have hne : a ≠ b := hadj.ne
        have hnz : edgeBit144.getD (a.val * 12 + b.val) 0 ≠ 0 := by
          intro hz
          have hforb := (hedgeBit_zero_iff a b ha4 hb4 hne).mp hz
          rcases hforb with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hf1 (by rwa [show a = ⟨4, by decide⟩ from Fin.ext h1, show b = ⟨5, by decide⟩ from Fin.ext h2] at hadj)
          · exact hf1 (by have h := hadj.symm; rwa [show b = ⟨4, by decide⟩ from Fin.ext h2, show a = ⟨5, by decide⟩ from Fin.ext h1] at h)
          · exact hf2 (by rwa [show a = ⟨6, by decide⟩ from Fin.ext h1, show b = ⟨7, by decide⟩ from Fin.ext h2] at hadj)
          · exact hf2 (by have h := hadj.symm; rwa [show b = ⟨6, by decide⟩ from Fin.ext h2, show a = ⟨7, by decide⟩ from Fin.ext h1] at h)
          · exact hf3 (by rwa [show a = ⟨8, by decide⟩ from Fin.ext h1, show b = ⟨9, by decide⟩ from Fin.ext h2] at hadj)
          · exact hf3 (by have h := hadj.symm; rwa [show b = ⟨8, by decide⟩ from Fin.ext h2, show a = ⟨9, by decide⟩ from Fin.ext h1] at h)
          · exact hf4 (by rwa [show a = ⟨10, by decide⟩ from Fin.ext h1, show b = ⟨11, by decide⟩ from Fin.ext h2] at hadj)
          · exact hf4 (by have h := hadj.symm; rwa [show b = ⟨10, by decide⟩ from Fin.ext h2, show a = ⟨11, by decide⟩ from Fin.ext h1] at h)
        have hex : ∃ idx : Fin 24, (edgeBit144.getD (a.val * 12 + b.val) 0).testBit idx.val = true := by
          by_contra h0; push Not at h0; apply hnz; apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.zero_testBit]
          by_cases hk : k < 24
          · exact Bool.eq_false_iff.mpr (h0 ⟨k, hk⟩)
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (hedgeBit_lt a b) (Nat.pow_le_pow_right (by omega) (by omega)))
        obtain ⟨idx, hidx⟩ := hex
        have hsp := (hedgeBit_spec a b idx).mp hidx
        have hhm : hMask.testBit idx.val = true := by
          rw [hhMask_bit idx]
          rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · convert hadj <;> exact Fin.ext ‹_›
          · convert hadj.symm <;> exact Fin.ext ‹_›
        intro hz
        have := congrArg (fun z => z.testBit idx.val) hz
        rw [Nat.testBit_and, hhm, hidx] at this; simp at this
    · exact hisAdjYes_imp hMask (fun _ h => h) a b
  -- Map M y to 12-bit masks on H0
  let M0 : Fin 5 → Finset (Fin 12) := fun y => (M y).map sw.toEmbedding
  let toMask : Finset (Fin 12) → Nat := fun s =>
    (List.finRange 12).foldl (fun acc w => if w ∈ s then acc ||| (1 <<< w.val) else acc) 0
  have htoMask_bit : ∀ (s : Finset (Fin 12)) (w : Fin 12), (toMask s).testBit w.val = true ↔ w ∈ s := by
    intro s w
    have hfold : ∀ (l : List (Fin 12)) (acc : Nat),
        (l.foldl (fun acc i => if i ∈ s then acc ||| (1 <<< i.val) else acc) acc).testBit w.val =
        (acc.testBit w.val || (w ∈ l && decide (w ∈ s))) := by
      intro l
      induction l with
      | nil => intro acc; simp
      | cons j rest ih =>
          intro acc; simp only [List.foldl_cons, ih]
          by_cases hjw : j = w
          · subst hjw; by_cases hs : j ∈ s <;> simp [hs, Nat.testBit_or, Nat.testBit_shiftLeft, hbit1]
          · have hne : j.val ≠ w.val := fun h => hjw (Fin.ext h)
            by_cases hs : j ∈ s
            · rw [if_pos hs, Nat.testBit_or, Nat.testBit_shiftLeft, hbit1]
              have : (decide (j.val ≤ w.val) && decide (w.val - j.val = 0)) = false := by
                by_cases hle : j.val ≤ w.val
                · simp [hle, show w.val - j.val ≠ 0 by omega]
                · simp [hle]
              rw [this, Bool.or_false]; simp [hjw, Ne.symm hjw]
            · rw [if_neg hs]; simp [hjw, Ne.symm hjw]
    have h := hfold (List.finRange 12) 0
    simp only [Nat.zero_testBit, Bool.false_or, List.mem_finRange, decide_true, Bool.true_and] at h
    change (toMask s).testBit w.val = true ↔ _
    rw [h, decide_eq_true_eq]
  have htoMask_hi : ∀ (s : Finset (Fin 12)) (k : Nat), 12 ≤ k → (toMask s).testBit k = false := by
    intro s k hk
    have hfold : ∀ (l : List (Fin 12)) (acc : Nat), acc.testBit k = false →
        (l.foldl (fun acc i => if i ∈ s then acc ||| (1 <<< i.val) else acc) acc).testBit k = false := by
      intro l
      induction l with
      | nil => intro acc h; exact h
      | cons j rest ih =>
          intro acc h; simp only [List.foldl_cons]; apply ih
          by_cases hs : j ∈ s
          · rw [if_pos hs, Nat.testBit_or, h, Bool.false_or, Nat.testBit_shiftLeft]
            have hlt : j.val < k := lt_of_lt_of_le j.isLt hk
            have : decide (j.val ≤ k) = true := by simp [Nat.le_of_lt hlt]
            rw [hbit1]; simp [this, show k - j.val ≠ 0 by omega]
          · rw [if_neg hs]; exact h
    exact hfold (List.finRange 12) 0 (by simp)
  have htoMask_lt : ∀ s : Finset (Fin 12), toMask s < 4096 := by
    intro s
    by_contra hge
    have hpos : 0 < toMask s / 2 ^ 12 := Nat.div_pos (by omega) (by decide)
    have hexk : ∃ k, (toMask s / 2 ^ 12).testBit k = true := by
      by_contra h0; push Not at h0
      have : toMask s / 2 ^ 12 = 0 := Nat.eq_of_testBit_eq fun k => by simpa using Bool.eq_false_iff.mpr (h0 k)
      omega
    obtain ⟨k, hk⟩ := hexk; rw [Nat.testBit_div_two_pow] at hk
    have := htoMask_hi s (k + 12) (by omega); rw [hk] at this; cases this
  have hpop_eq : ∀ (n : Nat) (m : Nat), popcount n m = (univ.filter (fun i : Fin n => m.testBit i.val = true)).card := by
    intro n m
    dsimp [popcount]
    rw [List.countP_eq_length_filter]
    have h1 : ((List.range n).filter (fun i => m.testBit i)).length =
        ((List.finRange n).filter (fun i : Fin n => m.testBit i.val)).length := by
      have hrf : List.range n = (List.finRange n).map Fin.val := by apply List.ext_getElem <;> simp
      rw [hrf, List.filter_map, List.length_map]; rfl
    rw [h1, ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
    congr 1; ext i; simp [List.mem_toFinset, List.mem_filter]
  have hM0_in_ind4 : ∀ y : Fin 5, toMask (M0 y) ∈ ind4H0List := by
    intro y
    have hchk4 := r36_cert_verify.2.2.1
    simp only [checkInd4Complete, List.all_eq_true] at hchk4
    have hmem := hchk4 (toMask (M0 y)) (List.mem_range.mpr (htoMask_lt (M0 y)))
    have hpc : popcount 12 (toMask (M0 y)) = 4 := by
      rw [hpop_eq]
      have : univ.filter (fun i : Fin 12 => (toMask (M0 y)).testBit i.val = true) = M0 y := by
        ext i; simp [htoMask_bit]
      rw [this, Finset.card_map, (hM y).card_eq]
    have hind0 : isIndH0 (toMask (M0 y)) = true := by
      simp only [isIndH0, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
      intro i hi
      have hi12 : i < 12 := List.mem_range.mp hi
      by_cases hbi : (toMask (M0 y)).testBit i = true
      · right
        apply Nat.eq_of_testBit_eq; intro j
        rw [Nat.testBit_and, Nat.zero_testBit]
        by_cases hj : j < 12
        · by_cases hbj : (toMask (M0 y)).testBit j = true
          · have hwi : ⟨i, hi12⟩ ∈ M0 y := (htoMask_bit (M0 y) ⟨i, hi12⟩).mp hbi
            have hwj : ⟨j, hj⟩ ∈ M0 y := (htoMask_bit (M0 y) ⟨j, hj⟩).mp hbj
            obtain ⟨a, haM, haeq⟩ := Finset.mem_map.mp hwi
            obtain ⟨b, hbM, hbeq⟩ := Finset.mem_map.mp hwj
            have hnotadj : ¬ H.Adj a b := by
              by_cases hab : a = b
              · subst hab; exact H.irrefl
              · exact (hM y).isIndepSet haM hbM hab
            have h0f : (h0Adj12.getD i 0).testBit j = false := by
              by_contra ht
              have htt : (h0Adj12.getD i 0).testBit j = true := Bool.eq_true_of_not_eq_false ht
              apply hnotadj
              rw [hH_iff_H0 a b]
              have h1 : (sw a).val = i := congrArg Fin.val haeq
              have h2 : (sw b).val = j := congrArg Fin.val hbeq
              rwa [h1, h2]
            rw [h0f, Bool.false_and]
          · simp [Bool.eq_false_iff.mpr hbj]
        · rw [htoMask_hi (M0 y) j (by omega), Bool.and_false]
      · exact Or.inl (Bool.eq_false_iff.mpr hbi)
    simp only [hpc, hind0, beq_self_eq_true, Bool.and_self, ↓reduceIte, List.contains_eq_mem] at hmem
    exact of_decide_eq_true hmem
  -- Sort the 5 masks into ind4H0List order via a permutation π : Fin 5 ≃ Fin 5
  let pos : Fin 5 → Nat := fun y => ind4H0List.idxOf (toMask (M0 y))
  let π : Fin 5 ≃ Fin 5 := Tuple.sort pos
  have hmono : Monotone (fun i : Fin 5 => pos (π i)) := Tuple.monotone_sort pos
  -- Helper: check5Ext soundness!
  have haddCnt_getD : ∀ (cnt : List Nat) (m : Nat) (i : Nat), i < 12 →
      (addCnt cnt m).getD i 0 = cnt.getD i 0 + (if m.testBit i then 1 else 0) := by
    intro cnt m i hi
    simp [addCnt, List.getD_eq_getElem?_getD, hi]
  have hcheck5_sound : ∀ (k : Nat) (cands : List Nat) (cnt chosen : List Nat)
      (ms : List Nat),
      check5Ext k cands cnt chosen = true →
      cnt.length = 12 →
      ms.length = k →
      (∀ x ∈ ms, x ∈ cands) →
      ms.Pairwise (fun a b => cands.idxOf a ≤ cands.idxOf b) →
      (∀ i < 12, cnt.getD i 0 + (ms.countP fun m => m.testBit i) = targetCnt.getD i 0) →
      hasInd6 (ms.reverse ++ chosen) = true := by
    intro k
    induction k with
    | zero =>
        intro cands cnt chosen ms hchk hclen hlen _ _ hcnt
        cases ms with
        | nil =>
            simp only [List.reverse_nil, List.nil_append]
            have hcnt_eq : cnt = targetCnt := by
              refine List.ext_getElem (by rw [hclen]; rfl) fun i hi1 hi2 => ?_
              have hi12 : i < 12 := by omega
              have hci := hcnt i hi12
              simp only [List.countP_nil, Nat.add_zero] at hci
              rwa [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2] at hci
            simp only [check5Ext, hcnt_eq, beq_self_eq_true, ↓reduceIte] at hchk
            exact hchk
        | cons _ _ => simp at hlen
    | succ k ih =>
        intro cands cnt chosen ms hchk hclen hlen hmem hpw hcnt
        cases ms with
        | nil => simp at hlen
        | cons m rest =>
            have htail : ∃ pref, cands = pref ++ (m :: (cands.drop (cands.idxOf m + 1))) ∧
                (m :: (cands.drop (cands.idxOf m + 1))) ∈ nonEmptyTails cands := by
              have hlt : cands.idxOf m < cands.length := List.idxOf_lt_length_iff.mpr (hmem m (by simp))
              have hm_eq : cands[cands.idxOf m] = m := List.getElem_idxOf hlt
              have hdrop : cands.drop (cands.idxOf m) = m :: cands.drop (cands.idxOf m + 1) := by
                rw [List.drop_eq_getElem_cons hlt, hm_eq]
              refine ⟨cands.take (cands.idxOf m), by rw [← hdrop, List.take_append_drop], ?_⟩
              have hmem_tails : ∀ (l : List Nat) (n : Nat), n < l.length → l.drop n ∈ nonEmptyTails l := by
                intro l
                induction l with
                | nil => intro n hn; simp at hn
                | cons x xs ihx =>
                    intro n hn
                    cases n with
                    | zero => simp [nonEmptyTails]
                    | succ n =>
                        simp only [nonEmptyTails, List.drop_succ_cons, List.mem_cons]
                        exact Or.inr (ihx n (by simpa using hn))
              rw [← hdrop]
              exact hmem_tails cands (cands.idxOf m) hlt
            obtain ⟨_, _, hmemT⟩ := htail
            let tailM := m :: cands.drop (cands.idxOf m + 1)
            have hchk' := (List.all_eq_true.mp hchk) tailM hmemT
            have hfits : fitsCnt cnt m = true := by
              simp only [fitsCnt, List.all_eq_true, decide_eq_true_eq]
              intro i hi
              have hi12 : i < 12 := List.mem_range.mp hi
              have hci := hcnt i hi12
              simp only [List.countP_cons] at hci
              omega
            simp only [tailM, hfits, ↓reduceIte] at hchk'
            have hrest_mem : ∀ x ∈ rest, x ∈ tailM := by
              intro x hx
              have hx_c : x ∈ cands := hmem x (by simp [hx])
              have hle : cands.idxOf m ≤ cands.idxOf x := (List.pairwise_cons.mp hpw).1 x hx
              have hx_lt : cands.idxOf x < cands.length := List.idxOf_lt_length_iff.mpr hx_c
              have hdrop : cands.drop (cands.idxOf m) = tailM := by
                have hmlt : cands.idxOf m < cands.length := List.idxOf_lt_length_iff.mpr (hmem m (by simp))
                rw [List.drop_eq_getElem_cons hmlt, List.getElem_idxOf hmlt]
              rw [← hdrop]
              have hge : cands.idxOf x - cands.idxOf m < (cands.drop (cands.idxOf m)).length := by
                simp; omega
              have helem : (cands.drop (cands.idxOf m))[cands.idxOf x - cands.idxOf m] = x := by
                rw [List.getElem_drop]; convert List.getElem_idxOf hx_lt using 2; omega
              rw [← helem]
              exact List.getElem_mem hge
            have hrest_pw : rest.Pairwise (fun a b => tailM.idxOf a ≤ tailM.idxOf b) := by
              have hdrop : cands.drop (cands.idxOf m) = tailM := by
                have hmlt : cands.idxOf m < cands.length := List.idxOf_lt_length_iff.mpr (hmem m (by simp))
                rw [List.drop_eq_getElem_cons hmlt, List.getElem_idxOf hmlt]
              refine (List.pairwise_cons.mp hpw).2.imp_of_mem fun {a b} ha hb hab => ?_
              have hma : cands.idxOf m ≤ cands.idxOf a := (List.pairwise_cons.mp hpw).1 a ha
              have hmb : cands.idxOf m ≤ cands.idxOf b := (List.pairwise_cons.mp hpw).1 b hb
              have hidx_le : ∀ (l : List Nat) (x : Nat) (k : Nat) (hk : k < l.length), l[k] = x → l.idxOf x ≤ k := by
                intro l
                induction l with
                | nil => intro _ _ hk; simp at hk
                | cons a t ih =>
                    intro x k hk he
                    cases k with
                    | zero => simp at he; subst he; simp
                    | succ k' =>
                        simp only [List.idxOf_cons]
                        cases hax : (a == x)
                        · simp only [cond_false]
                          exact Nat.succ_le_succ (ih x k' (by simp at hk; omega) (by simpa using he))
                        · simp only [cond_true]
                          exact Nat.zero_le _
              have hidx_drop : ∀ x, x ∈ cands → cands.idxOf m ≤ cands.idxOf x →
                  (cands.drop (cands.idxOf m)).idxOf x = cands.idxOf x - cands.idxOf m := by
                intro x hxc hmx
                have hlt : cands.idxOf x < cands.length := List.idxOf_lt_length_iff.mpr hxc
                apply le_antisymm
                · have hge : cands.idxOf x - cands.idxOf m < (cands.drop (cands.idxOf m)).length := by simp; omega
                  have he : (cands.drop (cands.idxOf m))[cands.idxOf x - cands.idxOf m] = x := by
                    rw [List.getElem_drop]; convert List.getElem_idxOf hlt using 2; omega
                  exact hidx_le _ x _ hge he
                · by_contra hlt2
                  have hlt3 : (cands.drop (cands.idxOf m)).idxOf x < (cands.drop (cands.idxOf m)).length := by simp; omega
                  have he := List.getElem_idxOf hlt3
                  rw [List.getElem_drop] at he
                  have hle2 := hidx_le cands x _ (by simp at hlt3; omega) he
                  omega
              rw [← hdrop, hidx_drop a (hmem a (by simp [ha])) hma, hidx_drop b (hmem b (by simp [hb])) hmb]
              omega
            have hcnt' : ∀ i < 12, (addCnt cnt m).getD i 0 + (rest.countP fun x => x.testBit i) = targetCnt.getD i 0 := by
              intro i hi
              rw [haddCnt_getD cnt m i hi]
              have hci := hcnt i hi
              simp only [List.countP_cons] at hci
              omega
            have hres := ih tailM (addCnt cnt m) (m :: chosen) rest hchk' (by simp [addCnt]) (by simpa using hlen) hrest_mem hrest_pw hcnt'
            simpa [List.reverse_cons, List.append_assoc] using hres
  let ms : List Nat := (List.finRange 5).map (fun i => toMask (M0 (π i)))
  have hms_ind6 : hasInd6 ms.reverse = true := by
    have hres := hcheck5_sound 5 ind4H0List (List.replicate 12 0) [] ms r36_cert_verify.2.2.2.2
      (by simp)
      (by simp [ms])
      (by intro x hx; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx; exact hM0_in_ind4 (π i))
      (by
        rw [List.pairwise_map]
        exact (List.pairwise_lt_finRange 5).imp fun {a b} hab => hmono (le_of_lt hab))
      (by
        intro i hi
        have hrep : (List.replicate 12 0).getD i 0 = 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi]; rfl
        rw [hrep, Nat.zero_add]
        have hcnt_ms : (ms.countP fun m => m.testBit i) =
            (univ.filter (fun y : Fin 5 => (⟨i, hi⟩ : Fin 12) ∈ M0 y)).card := by
          dsimp [ms]
          rw [List.countP_map, List.countP_eq_length_filter]
          dsimp only [Function.comp_def]
          have hnd : ((List.finRange 5).filter (fun k : Fin 5 => (toMask (M0 (π k))).testBit i)).Nodup :=
            (List.nodup_finRange 5).filter _
          rw [← List.toFinset_card_of_nodup hnd]
          refine Finset.card_bij (fun k _ => π k) ?_ (fun _ _ _ _ h => π.injective h) ?_
          · intro k hk
            simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, Function.comp_apply] at hk
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (htoMask_bit (M0 (π k)) ⟨i, hi⟩).mp hk⟩
          · intro y hy
            refine ⟨π.symm y, ?_, π.apply_symm_apply y⟩
            simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, Function.comp_apply, π.apply_symm_apply]
            exact (htoMask_bit (M0 y) ⟨i, hi⟩).mpr (Finset.mem_filter.mp hy).2
        rw [hcnt_ms]
        have hM0_cov : (univ.filter (fun y : Fin 5 => (⟨i, hi⟩ : Fin 12) ∈ M0 y)).card =
            (univ.filter (fun y : Fin 5 => sw.symm ⟨i, hi⟩ ∈ M y)).card := by
          congr 1; ext y; simp [M0, sw.symm_apply_eq]
        rw [hM0_cov, hcov (sw.symm ⟨i, hi⟩)]
        have hlt4 : (sw.symm ⟨i, hi⟩).val < 4 ↔ i < 4 := hswap_lt4 bits ⟨i, hi⟩
        have htgt : targetCnt.getD i 0 = if i < 4 then 1 else 2 := by
          have : ∀ j : Fin 12, targetCnt.getD j.val 0 = if j.val < 4 then 1 else 2 := by decide
          exact this ⟨i, hi⟩
        rw [htgt]
        by_cases h4 : i < 4 <;> simp [h4, hlt4])
    simpa using hres
  -- Unpack hasInd6 ms.reverse = true to contradict hno6!
  simp only [hasInd6, List.any_eq_true, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at hms_ind6
  obtain ⟨yMask, hyM_mem, iMask, hiM_mem, hpc_eq, hdisj_all⟩ := hms_ind6
  have hyM_range : 1 ≤ yMask ∧ yMask < 32 := by
    simp only [List.mem_range'] at hyM_mem; omega
  let Y : Finset (Fin 5) := univ.filter (fun k : Fin 5 => yMask.testBit (4 - k.val) = true) |>.map π.toEmbedding
  let I0 : Finset (Fin 12) := univ.filter (fun w : Fin 12 => iMask.testBit w.val = true)
  let I : Finset (Fin 12) := I0.map sw.symm.toEmbedding
  have hY_card : Y.card = popcount 5 yMask := by
    rw [Finset.card_map, hpop_eq]
    refine Finset.card_bij (fun k _ => ⟨4 - k.val, by omega⟩) ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢; exact hk
    · intro a _ b _ h; have := congrArg Fin.val h; dsimp at this; exact Fin.ext (by omega)
    · intro k hk; refine ⟨⟨4 - k.val, by omega⟩, ?_, Fin.ext (by dsimp; omega)⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢; simpa [show 4 - (4 - k.val) = k.val by omega] using hk
  have hY_ne : Y.Nonempty := by
    rw [← Finset.card_pos, hY_card, hpop_eq, Finset.card_pos]
    by_contra h0; push Not at h0
    have : yMask = 0 := by
      apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.zero_testBit]
      by_cases hk : k < 5
      · exact Bool.eq_false_iff.mpr (fun ht => Finset.eq_empty_iff_forall_notMem.mp h0 ⟨k, hk⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩))
      · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hyM_range.2 (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 5 ≤ k)))
    omega
  have hI_card : I.card = popcount 12 iMask := by
    rw [Finset.card_map, hpop_eq]
  have hY_le5 : popcount 5 yMask ≤ 5 := by
    rw [← hY_card]; exact (Finset.card_le_univ Y).trans (by simp)
  have hI_ind : H.IsIndepSet (I : Set (Fin 12)) := by
    have hvalid := List.all_eq_true.mp r36_cert_verify.2.2.2.1 iMask hiM_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq, isIndH0, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', beq_iff_eq] at hvalid
    intro a ha b hb _ hadj
    obtain ⟨wa, hwa, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨wb, hwb, rfl⟩ := Finset.mem_map.mp hb
    have hba := (Finset.mem_filter.mp hwa).2
    have hbb := (Finset.mem_filter.mp hwb).2
    have h0adj : (h0Adj12.getD wa.val 0).testBit wb.val = true := by
      have := (hH_iff_H0 (sw.symm wa) (sw.symm wb)).mp hadj
      simpa using this
    rcases hvalid.2 wa.val (List.mem_range.mpr wa.isLt) with hfa | hzero
    · rw [hba] at hfa; cases hfa
    · have := congrArg (fun x => x.testBit wb.val) hzero
      rw [Nat.testBit_and, h0adj, hbb] at this; simp at this
  have hY_I_disj : ∀ y ∈ Y, ∀ w ∈ I, w ∉ M y := by
    intro y hy w hw hwM
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨w0, hw0, rfl⟩ := Finset.mem_map.mp hw
    have hky : yMask.testBit (4 - k.val) = true := (Finset.mem_filter.mp hk).2
    have hwi : iMask.testBit w0.val = true := (Finset.mem_filter.mp hw0).2
    have hmem0 : w0 ∈ M0 (π k) := by
      simp only [M0, Finset.mem_map, Equiv.coe_toEmbedding]
      exact ⟨sw.symm w0, hwM, sw.apply_symm_apply w0⟩
    have hmbit : (toMask (M0 (π k))).testBit w0.val = true := (htoMask_bit (M0 (π k)) w0).mpr hmem0
    have hget : ms.reverse.getD (4 - k.val) 0 = toMask (M0 (π k)) := by
      have hlen : ms.length = 5 := by simp [ms]
      have hlt : 4 - k.val < ms.reverse.length := by simp [hlen]; omega
      rw [List.getD_eq_getElem _ _ hlt, List.getElem_reverse]
      simp [ms, hlen, show 5 - 1 - (4 - k.val) = k.val by omega]
    rcases hdisj_all (4 - k.val) (List.mem_range.mpr (by omega)) with hfk | hzero
    · rw [hky] at hfk; cases hfk
    · rw [hget] at hzero
      have := congrArg (fun x => x.testBit w0.val) hzero
      rw [Nat.testBit_and, hmbit, hwi] at this; simp at this
  have hle5 := hno6 Y I hY_ne hI_ind hY_I_disj
  rw [hY_card, hI_card, hpc_eq] at hle5
  omega
-- === END HELPERS ===

theorem OMA.solution : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H2_R1_H1_R1.H1 := by
  classical
  change 6 ≤ sSup {k | ∀ G : SimpleGraph (Fin 18), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s}
  have hbdd : BddAbove {k | ∀ G : SimpleGraph (Fin 18), G.CliqueFree 3 → ∃ s, G.IsNIndepSet k s} := by
    refine ⟨18, fun k hk => ?_⟩
    obtain ⟨s, hs⟩ := hk (⊥ : SimpleGraph (Fin 18)) (fun t ht => by
      obtain ⟨a, b, _, hab, _, _, -⟩ := SimpleGraph.is3Clique_iff.mp ht
      exact hab)
    simpa [hs.card_eq] using Finset.card_le_univ s
  apply le_csSup hbdd
  intro G hG
  by_contra hno6
  push Not at hno6
  have hdeg : ∀ v : Fin 18, 4 ≤ (univ.filter (G.Adj v)).card ∧ (univ.filter (G.Adj v)).card ≤ 5 := by
    intro v
    constructor
    · by_contra hlt
      have hM : 14 ≤ (univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)).card := by
        have hdisj : Disjoint (univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)) (univ.filter (G.Adj v)) := by
          rw [Finset.disjoint_left]
          intro u huM huN
          exact (Finset.mem_filter.mp huM).2.2 (Finset.mem_filter.mp huN).2
        have hvMN : v ∉ univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) ∪ univ.filter (G.Adj v) := by
          intro hv
          rcases Finset.mem_union.mp hv with hvM | hvN
          · exact (Finset.mem_filter.mp hvM).2.1 rfl
          · exact G.irrefl (Finset.mem_filter.mp hvN).2
        have huniv : insert v (univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) ∪ univ.filter (G.Adj v)) = univ := by
          ext u
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          by_cases huv : u = v
          · exact Or.inl huv
          · by_cases hadj : G.Adj v u
            · exact Or.inr (Or.inr hadj)
            · exact Or.inr (Or.inl ⟨huv, hadj⟩)
        have hcard : (insert v (univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u) ∪ univ.filter (G.Adj v))).card = 18 := by
          rw [huniv, Finset.card_univ, Fintype.card_fin]
        rw [Finset.card_insert_of_notMem hvMN, Finset.card_union_of_disjoint hdisj] at hcard
        omega
      obtain ⟨T, hTM, hTc⟩ := Finset.exists_subset_card_eq hM
      let e : Fin 14 ≃ T := (Fintype.equivFinOfCardEq (by simp [hTc])).symm
      let Q : SimpleGraph (Fin 14) :=
        { Adj := fun i j => G.Adj (e i).val (e j).val
          symm := ⟨fun _ _ h => h.symm⟩
          loopless := ⟨fun _ h => G.irrefl h⟩ }
      have hQ : Q.CliqueFree 3 := by
        intro t ht
        obtain ⟨a, b, c, hab, hac, hbc, -⟩ := SimpleGraph.is3Clique_iff.mp ht
        exact hG {(e a).val, (e b).val, (e c).val}
          (SimpleGraph.is3Clique_iff.mpr ⟨(e a).val, (e b).val, (e c).val, hab, hac, hbc, rfl⟩)
      obtain ⟨I, hI⟩ := r36_small_ramsey.2.2.1 Q hQ
      let S := I.image (fun i => (e i).val)
      have hvS : v ∉ S := by
        intro hv
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp (hTM (e i).property)).2.1 hi
      have hScard : S.card = 5 := by
        rw [Finset.card_image_of_injective _ (fun i j hij => e.injective (Subtype.ext hij)), hI.card_eq]
      refine hno6 (insert v S) ⟨?_, by rw [Finset.card_insert_of_notMem hvS, hScard]⟩
      intro x hx y hy hxy hadj
      simp only [Finset.mem_coe, Finset.mem_insert] at hx hy
      rcases hx with rfl | hxS <;> rcases hy with rfl | hyS
      · exact hxy rfl
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyS
        exact (Finset.mem_filter.mp (hTM (e j).property)).2.2 hadj
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxS
        exact (Finset.mem_filter.mp (hTM (e i).property)).2.2 hadj.symm
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxS
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hyS
        exact hI.isIndepSet hi hj (fun h => hxy (by rw [h])) hadj
    · by_contra hgt
      have h6 : 6 ≤ (univ.filter (G.Adj v)).card := by omega
      obtain ⟨s, hs, hsc⟩ := Finset.exists_subset_card_eq h6
      refine hno6 s ⟨?_, hsc⟩
      intro x hx y hy _ hadj
      exact hG {v, x, y} (SimpleGraph.is3Clique_iff.mpr
        ⟨v, x, y, (Finset.mem_filter.mp (hs hx)).2, (Finset.mem_filter.mp (hs hy)).2, hadj, rfl⟩)
  by_cases h4 : ∃ v : Fin 18, (univ.filter (G.Adj v)).card = 4
  · exact r36_no_deg4 G hG hno6 hdeg h4
  · push Not at h4
    have h5 : ∀ v : Fin 18, (univ.filter (G.Adj v)).card = 5 := by
      intro v; have := hdeg v; have := h4 v; omega
    obtain ⟨H, M, hH, hno5, hbase, hf1, hf2, hf3, hf4, hdeg2, hM, hcov, hno6H⟩ :=
      r36_5reg_frame G hG hno6 h5
    exact r36_cert_sound H M hH hno5 hbase hf1 hf2 hf3 hf4 hdeg2 hM hcov hno6H

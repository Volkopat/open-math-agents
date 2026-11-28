import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H1_R1_H1_R1
import Mathlib

/-!
The 52-vertex adjacency matrix is from the Google Research Ramsey number bounds
dataset, distributed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). The license supplies the data
on an "AS IS" basis, without warranties or conditions of any kind.

Source at commit 0d94f8c4d92678ce5f7a0eacae725f79174cfb03:
https://github.com/google-research/google-research/blob/0d94f8c4d92678ce5f7a0eacae725f79174cfb03/ramsey_number_bounds/improved_bounds/R(3%2C%2012)%20%3E%3D%2053.txt

The numerical bound R(3,12) ≥ 53 is due to M. Kolodyazhny (2015), as reported
in Table Ia of Stanisław Radziszowski's Small Ramsey Numbers. The proof uses
the matching-cover certificate method also used by @SanskarX10 for R(3,11).
-/
-- Credit: @grp06

namespace Ramsey151Witness

private def rows : Array Nat :=
#[44017215603840,90164472848640,4400659583488,290293904098304,582788038264832,1161177761715200,2322356060299264,145510543392769,612571054082,400508388356,148030347018793,2328164340858896,152729039667236,6409199550530,1128889273417740,658951196639496,51267212673536,384004989665312,767460223486272,1254544981889544,2509227402731776,2854343191581186,3141304720557190,1990667412703237,2990783296831502,3729685175607317,2815033772425251,1407941820317783,1214995247464588,175990923985232,2322306005476024,141012368949621,1649302045418,291370667345360,582741296950184,285873308455761,290271623441056,580543247899712,1161086493702784,2322172995532032,140750646585344,17189688338,34362600580,1125977221959689,2251954710282258,275439747105,551133284418,1408477097628800,140849337991176,154717683728,149808904421408,18143140382784]

private def edge (a b : Nat) : Bool := (rows.getD a 0).testBit b

private def matrixOK : Bool :=
  (List.range 52).all fun a =>
    !(edge a a) && (List.range 52).all fun b => edge a b == edge b a

private def triangleOK : Bool :=
  (List.range 52).all fun a =>
    (List.range 52).all fun b =>
      !(edge a b) || ((rows.getD a 0 &&& rows.getD b 0) == 0)

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem matrix_checked : matrixOK = true := by rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem triangle_checked : triangleOK = true := by rfl

private inductive Tree where
  | leaf (matching : List (Nat × Nat))
  | branch (vertex : Nat) (take skip : Tree)

private def kept (v : Nat) (pool : List Nat) : List Nat :=
  (pool.erase v).filter fun w => !(edge v w)

private def pairOK (a b : Nat) (pool : List Nat) (need : Nat) : Bool :=
  (pool.contains a && pool.contains b) && (edge a b && decide (0 < need))

private def matchOK : List (Nat × Nat) → List Nat → Nat → Bool
  | [], pool, need => decide (pool.length < need)
  | (a, b) :: rest, pool, need =>
      pairOK a b pool need && matchOK rest ((pool.erase a).erase b) (need - 1)

private def pivotOK (v : Nat) (pool : List Nat) (need : Nat) : Bool :=
  pool.contains v && decide (0 < need)

private def treeOK : Tree → List Nat → Nat → Bool
  | .leaf matching, pool, need => matchOK matching pool need
  | .branch v take skip, pool, need =>
      pivotOK v pool need &&
        (treeOK take (kept v pool) (need - 1) && treeOK skip (pool.erase v) need)

private theorem joinChecks (v : Nat) (take skip : Tree) (pool : List Nat) (need : Nat)
    (hv : pivotOK v pool need = true)
    (ht : treeOK take (kept v pool) (need - 1) = true)
    (hs : treeOK skip (pool.erase v) need = true) :
    treeOK (.branch v take skip) pool need = true := by
  rw [treeOK, hv, ht, hs] <;> rfl

-- Closed certificate subtrees and their incoming candidate lists.
set_option maxRecDepth 32768 in
private def treeRootTTTT : Tree :=
  (.leaf [(7, 33), (9, 35), (12, 39), (17, 29), (20, 45), (25, 50)])
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootTTTT : treeOK treeRootTTTT ([7, 9, 12, 17, 20, 25, 29, 33, 35, 39, 45, 49, 50]) 8 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootTTTST : Tree :=
  (.leaf [(9, 16), (17, 29), (6, 33), (7, 0), (20, 45), (25, 50)])
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootTTTST : treeOK treeRootTTTST ([0, 6, 7, 9, 16, 17, 20, 25, 29, 33, 45, 49, 50]) 8 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootTTTSS : Tree :=
  (.branch 45
    (.branch 2
      (.leaf [(35, 6), (33, 7), (47, 50)])
      (.leaf [(9, 35), (6, 33), (7, 47), (25, 50)]))
    (.branch 47
      (.leaf [(5, 17), (33, 6), (39, 16), (0, 25), (2, 9)])
      (.branch 0
        (.leaf [(2, 9), (16, 39), (33, 6), (29, 17), (5, 50)])
        (.branch 6
          (.leaf [(17, 5), (39, 16), (9, 2), (25, 50)])
          (.leaf [(7, 33), (29, 17), (5, 50), (25, 2), (35, 9), (16, 39)])))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootTTTSS : treeOK treeRootTTTSS ([0, 2, 5, 6, 7, 9, 16, 17, 20, 25, 29, 33, 35, 39, 45, 47, 49, 50]) 9 = true := by rfl

private def treeRootTTTS : Tree := .branch 12 treeRootTTTST treeRootTTTSS
private theorem checkedRootTTTS : treeOK treeRootTTTS ([0, 2, 5, 6, 7, 9, 12, 16, 17, 20, 25, 29, 33, 35, 39, 45, 47, 49, 50]) 9 = true := by
  exact joinChecks 12 treeRootTTTST treeRootTTTSS ([0, 2, 5, 6, 7, 9, 12, 16, 17, 20, 25, 29, 33, 35, 39, 45, 47, 49, 50]) 9
    (by rfl) checkedRootTTTST checkedRootTTTSS

private def treeRootTTT : Tree := .branch 31 treeRootTTTT treeRootTTTS
private theorem checkedRootTTT : treeOK treeRootTTT ([0, 2, 5, 6, 7, 9, 12, 16, 17, 20, 25, 29, 31, 33, 35, 39, 45, 47, 49, 50]) 9 = true := by
  exact joinChecks 31 treeRootTTTT treeRootTTTS ([0, 2, 5, 6, 7, 9, 12, 16, 17, 20, 25, 29, 31, 33, 35, 39, 45, 47, 49, 50]) 9
    (by rfl) checkedRootTTTT checkedRootTTTS

set_option maxRecDepth 32768 in
private def treeRootTTSTT : Tree :=
  (.leaf [(6, 33), (15, 49), (25, 0), (39, 14), (43, 17), (5, 45)])
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootTTSTT : treeOK treeRootTTSTT ([0, 5, 6, 14, 15, 17, 25, 28, 33, 39, 43, 45, 49]) 8 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootTTSTS : Tree :=
  (.branch 0
    (.leaf [(6, 33), (15, 49), (30, 5), (17, 14), (2, 28), (16, 39)])
    (.branch 14
      (.leaf [(6, 33), (15, 49), (19, 45), (5, 30), (28, 16)])
      (.leaf [(15, 49), (19, 45), (25, 2), (30, 5), (17, 43), (33, 6), (35, 28), (16, 39)])))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootTTSTS : treeOK treeRootTTSTS ([0, 2, 5, 6, 14, 15, 16, 17, 19, 25, 28, 30, 33, 35, 39, 43, 45, 49]) 9 = true := by rfl

private def treeRootTTST : Tree := .branch 9 treeRootTTSTT treeRootTTSTS
private theorem checkedRootTTST : treeOK treeRootTTST ([0, 2, 5, 6, 9, 14, 15, 16, 17, 19, 25, 28, 30, 33, 35, 39, 43, 45, 49]) 9 = true := by
  exact joinChecks 9 treeRootTTSTT treeRootTTSTS ([0, 2, 5, 6, 9, 14, 15, 16, 17, 19, 25, 28, 30, 33, 35, 39, 43, 45, 49]) 9
    (by rfl) checkedRootTTSTT checkedRootTTSTS

set_option maxRecDepth 32768 in
private def treeRootTTSST : Tree :=
  (.branch 2
    (.branch 5
      (.leaf [(15, 49), (16, 39), (29, 6), (33, 48)])
      (.branch 6
        (.leaf [(15, 49), (16, 39), (17, 48), (19, 50)])
        (.leaf [(15, 49), (16, 39), (19, 50), (29, 17), (33, 48)])))
    (.branch 5
      (.leaf [(14, 39), (15, 49), (19, 9), (16, 28), (29, 6), (33, 48)])
      (.branch 9
        (.leaf [(12, 39), (15, 49), (6, 33), (48, 17), (14, 50), (28, 29)])
        (.branch 14
          (.leaf [(12, 19), (15, 49), (16, 28), (29, 6), (33, 48)])
          (.branch 28
            (.leaf [(6, 33), (15, 49), (17, 48), (19, 12)])
            (.branch 6
              (.leaf [(15, 49), (16, 39), (12, 19), (17, 48)])
              (.leaf [(15, 49), (16, 39), (12, 19), (29, 17), (33, 48)])))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootTTSST : treeOK treeRootTTSST ([2, 5, 6, 9, 12, 14, 15, 16, 17, 19, 20, 28, 29, 30, 33, 39, 48, 49, 50]) 9 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootTTSSS : Tree :=
  (.branch 5
    (.branch 28
      (.leaf [(6, 33), (9, 19), (14, 39), (15, 49), (20, 43)])
      (.branch 9
        (.leaf [(7, 33), (6, 29), (14, 39), (15, 49), (20, 43)])
        (.branch 33
          (.leaf [(15, 49), (16, 39), (25, 2), (14, 35)])
          (.branch 14
            (.leaf [(6, 29), (15, 49), (16, 43), (25, 48)])
            (.leaf [(2, 25), (15, 49), (20, 43), (16, 39), (29, 6), (35, 48)])))))
    (.branch 2
      (.branch 33
        (.leaf [(15, 49), (17, 29), (20, 45), (16, 39), (19, 50)])
        (.branch 43
          (.leaf [(7, 30), (10, 39), (15, 49), (19, 45), (29, 6)])
          (.branch 45
            (.leaf [(6, 35), (7, 30), (10, 39), (15, 49)])
            (.branch 6
              (.leaf [(7, 30), (10, 39), (15, 49), (17, 48), (19, 50)])
              (.leaf [(7, 30), (10, 39), (15, 49), (19, 50), (29, 17), (35, 48)])))))
      (.branch 16
        (.branch 33
          (.leaf [(15, 49), (25, 50), (19, 12), (29, 17), (14, 35)])
          (.branch 35
            (.leaf [(7, 30), (15, 49), (17, 29), (19, 50)])
            (.branch 17
              (.leaf [(7, 30), (12, 19), (15, 49), (25, 50)])
              (.leaf [(6, 29), (7, 30), (12, 19), (14, 50), (15, 49), (25, 48)]))))
        (.branch 35
          (.leaf [(15, 49), (25, 50), (30, 7), (31, 19), (39, 10), (33, 43), (17, 29), (20, 45)])
          (.branch 19
            (.leaf [(15, 49), (20, 43), (25, 48), (30, 7), (28, 29), (6, 33), (10, 39), (14, 17)])
            (.branch 33
              (.leaf [(9, 30), (12, 39), (15, 49), (20, 45), (25, 50), (14, 17), (28, 29)])
              (.branch 17
                (.leaf [(6, 31), (12, 39), (10, 9), (15, 49), (20, 45), (25, 50), (28, 7)])
                (.branch 50
                  (.leaf [(7, 30), (9, 10), (12, 39), (15, 49), (20, 45), (29, 6)])
                  (.leaf [(14, 39), (10, 9), (12, 43), (15, 49), (20, 45), (25, 48), (30, 7), (28, 29), (6, 31)])))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootTTSSS : treeOK treeRootTTSSS ([2, 5, 6, 7, 9, 10, 12, 14, 15, 16, 17, 19, 20, 25, 28, 29, 30, 31, 33, 35, 39, 43, 45, 48, 49, 50]) 10 = true := by rfl

private def treeRootTTSS : Tree := .branch 0 treeRootTTSST treeRootTTSSS
private theorem checkedRootTTSS : treeOK treeRootTTSS ([0, 2, 5, 6, 7, 9, 10, 12, 14, 15, 16, 17, 19, 20, 25, 28, 29, 30, 31, 33, 35, 39, 43, 45, 48, 49, 50]) 10 = true := by
  exact joinChecks 0 treeRootTTSST treeRootTTSSS ([0, 2, 5, 6, 7, 9, 10, 12, 14, 15, 16, 17, 19, 20, 25, 28, 29, 30, 31, 33, 35, 39, 43, 45, 48, 49, 50]) 10
    (by rfl) checkedRootTTSST checkedRootTTSSS

private def treeRootTTS : Tree := .branch 47 treeRootTTST treeRootTTSS
private theorem checkedRootTTS : treeOK treeRootTTS ([0, 2, 5, 6, 7, 9, 10, 12, 14, 15, 16, 17, 19, 20, 25, 28, 29, 30, 31, 33, 35, 39, 43, 45, 47, 48, 49, 50]) 10 = true := by
  exact joinChecks 47 treeRootTTST treeRootTTSS ([0, 2, 5, 6, 7, 9, 10, 12, 14, 15, 16, 17, 19, 20, 25, 28, 29, 30, 31, 33, 35, 39, 43, 45, 47, 48, 49, 50]) 10
    (by rfl) checkedRootTTST checkedRootTTSS

private def treeRootTT : Tree := .branch 3 treeRootTTT treeRootTTS
private theorem checkedRootTT : treeOK treeRootTT ([0, 2, 3, 5, 6, 7, 9, 10, 12, 14, 15, 16, 17, 19, 20, 25, 28, 29, 30, 31, 33, 35, 39, 43, 45, 47, 48, 49, 50]) 10 = true := by
  exact joinChecks 3 treeRootTTT treeRootTTS ([0, 2, 3, 5, 6, 7, 9, 10, 12, 14, 15, 16, 17, 19, 20, 25, 28, 29, 30, 31, 33, 35, 39, 43, 45, 47, 48, 49, 50]) 10
    (by rfl) checkedRootTTT checkedRootTTS

set_option maxRecDepth 32768 in
private def treeRootTSTTT : Tree :=
  (.leaf [(34, 49), (39, 10), (6, 35), (48, 47), (29, 45), (19, 40), (15, 38)])
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootTSTTT : treeOK treeRootTSTTT ([6, 10, 15, 19, 29, 34, 35, 38, 39, 40, 45, 47, 48, 49]) 8 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootTSTTS : Tree :=
  (.branch 47
    (.leaf [(19, 45), (5, 34), (38, 15), (39, 51), (4, 35), (6, 37)])
    (.branch 6
      (.leaf [(4, 49), (39, 10), (5, 34), (7, 38), (15, 40), (19, 45)])
      (.branch 45
        (.leaf [(7, 34), (40, 15), (48, 35), (4, 49), (37, 10)])
        (.leaf [(19, 40), (29, 4), (35, 48), (51, 39), (5, 10), (37, 49), (15, 38), (7, 34)]))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootTSTTS : treeOK treeRootTSTTS ([4, 5, 6, 7, 10, 15, 19, 29, 34, 35, 37, 38, 39, 40, 45, 47, 48, 49, 51]) 9 = true := by rfl

private def treeRootTSTT : Tree := .branch 30 treeRootTSTTT treeRootTSTTS
private theorem checkedRootTSTT : treeOK treeRootTSTT ([4, 5, 6, 7, 10, 15, 19, 29, 30, 34, 35, 37, 38, 39, 40, 45, 47, 48, 49, 51]) 9 = true := by
  exact joinChecks 30 treeRootTSTTT treeRootTSTTS ([4, 5, 6, 7, 10, 15, 19, 29, 30, 34, 35, 37, 38, 39, 40, 45, 47, 48, 49, 51]) 9
    (by rfl) checkedRootTSTTT checkedRootTSTTS

set_option maxRecDepth 32768 in
private def treeRootTSTST : Tree :=
  (.branch 35
    (.leaf [(34, 49), (39, 10), (15, 38), (29, 45), (19, 31), (40, 47)])
    (.branch 47
      (.branch 15
        (.leaf [(14, 39), (19, 45)])
        (.leaf [(14, 39), (34, 49), (38, 45), (19, 42)]))
      (.branch 15
        (.leaf [(10, 39), (25, 48), (28, 29), (6, 31), (19, 45)])
        (.leaf [(14, 39), (10, 42), (25, 48), (34, 49), (6, 29), (28, 40), (19, 31), (38, 45)]))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootTSTST : treeOK treeRootTSTST ([6, 10, 14, 15, 19, 25, 28, 29, 31, 34, 35, 38, 39, 40, 42, 45, 47, 48, 49]) 9 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootTSTSS : Tree :=
  (.branch 35
    (.branch 47
      (.leaf [(19, 45), (5, 34), (38, 15), (23, 39), (49, 37)])
      (.branch 5
        (.leaf [(7, 38), (19, 40), (15, 49), (29, 23), (37, 25)])
        (.leaf [(7, 34), (10, 37), (25, 51), (39, 23), (29, 45), (49, 15), (38, 31), (19, 40)])))
    (.branch 10
      (.branch 29
        (.leaf [(48, 25), (7, 34), (49, 15), (38, 31), (19, 40)])
        (.branch 31
          (.leaf [(51, 25), (48, 23), (7, 28), (34, 49), (15, 40)])
          (.branch 49
            (.leaf [(6, 51), (25, 48), (7, 28), (38, 45)])
            (.leaf [(4, 25), (6, 51), (23, 48), (34, 7), (28, 40), (15, 38), (19, 45)]))))
      (.branch 29
        (.branch 15
          (.leaf [(7, 34), (5, 31), (9, 19), (48, 25), (37, 14)])
          (.leaf [(40, 19), (42, 7), (48, 25), (51, 39), (14, 37), (49, 34), (5, 31), (9, 38)]))
        (.branch 31
          (.branch 49
            (.leaf [(14, 39), (40, 28), (7, 42), (48, 25)])
            (.branch 7
              (.leaf [(15, 40), (14, 37), (23, 39), (48, 25)])
              (.leaf [(9, 34), (28, 40), (15, 42), (14, 37), (23, 39), (48, 25)])))
          (.branch 7
            (.leaf [(5, 45), (9, 19), (40, 15), (4, 49), (6, 37), (14, 39), (23, 48), (25, 51)])
            (.branch 49
              (.leaf [(5, 45), (6, 51), (14, 39), (25, 48), (28, 40), (38, 9), (19, 42)])
              (.branch 19
                (.leaf [(4, 25), (5, 34), (15, 38), (47, 48), (23, 39), (14, 37), (6, 51)])
                (.branch 25
                  (.branch 15
                    (.leaf [(9, 34), (5, 45), (14, 39)])
                    (.branch 5
                      (.leaf [(9, 38), (14, 39), (28, 40)])
                      (.leaf [(14, 39), (28, 40), (34, 9), (38, 45)])))
                  (.branch 15
                    (.leaf [(9, 34), (5, 45), (47, 48), (23, 39), (14, 37), (6, 51)])
                    (.branch 39
                      (.leaf [(6, 37), (28, 40), (47, 48), (5, 34), (9, 38)])
                      (.branch 5
                        (.leaf [(9, 38), (14, 37), (6, 51), (23, 48), (28, 40)])
                        (.leaf [(14, 37), (6, 51), (23, 48), (28, 40), (34, 9), (38, 45)]))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootTSTSS : treeOK treeRootTSTSS ([4, 5, 6, 7, 9, 10, 14, 15, 19, 23, 25, 28, 29, 31, 34, 35, 37, 38, 39, 40, 42, 45, 47, 48, 49, 51]) 10 = true := by rfl

private def treeRootTSTS : Tree := .branch 30 treeRootTSTST treeRootTSTSS
private theorem checkedRootTSTS : treeOK treeRootTSTS ([4, 5, 6, 7, 9, 10, 14, 15, 19, 23, 25, 28, 29, 30, 31, 34, 35, 37, 38, 39, 40, 42, 45, 47, 48, 49, 51]) 10 = true := by
  exact joinChecks 30 treeRootTSTST treeRootTSTSS ([4, 5, 6, 7, 9, 10, 14, 15, 19, 23, 25, 28, 29, 30, 31, 34, 35, 37, 38, 39, 40, 42, 45, 47, 48, 49, 51]) 10
    (by rfl) checkedRootTSTST checkedRootTSTSS

private def treeRootTST : Tree := .branch 2 treeRootTSTT treeRootTSTS
private theorem checkedRootTST : treeOK treeRootTST ([2, 4, 5, 6, 7, 9, 10, 14, 15, 19, 23, 25, 28, 29, 30, 31, 34, 35, 37, 38, 39, 40, 42, 45, 47, 48, 49, 51]) 10 = true := by
  exact joinChecks 2 treeRootTSTT treeRootTSTS ([2, 4, 5, 6, 7, 9, 10, 14, 15, 19, 23, 25, 28, 29, 30, 31, 34, 35, 37, 38, 39, 40, 42, 45, 47, 48, 49, 51]) 10
    (by rfl) checkedRootTSTT checkedRootTSTS

set_option maxRecDepth 32768 in
private def treeRootTSSTT : Tree :=
  (.branch 14
    (.leaf [(5, 45), (42, 15), (0, 23), (49, 4), (25, 51), (6, 33)])
    (.branch 25
      (.leaf [(6, 33), (28, 3), (39, 23), (45, 5), (17, 42)])
      (.leaf [(28, 3), (0, 45), (5, 17), (42, 15), (4, 33), (6, 37), (49, 23), (39, 51)])))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootTSSTT : treeOK treeRootTSSTT ([0, 3, 4, 5, 6, 14, 15, 17, 23, 25, 28, 33, 37, 39, 42, 45, 49, 51]) 9 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootTSSTS : Tree :=
  (.branch 14
    (.branch 45
      (.leaf [(34, 49), (15, 42), (23, 30), (4, 25), (33, 6)])
      (.branch 4
        (.leaf [(0, 23), (5, 34), (6, 51), (19, 42), (15, 38)])
        (.leaf [(19, 42), (16, 28), (33, 6), (38, 15), (0, 25), (51, 30), (5, 34), (23, 49)])))
    (.branch 30
      (.branch 42
        (.leaf [(6, 33), (25, 0), (34, 49), (38, 45)])
        (.branch 45
          (.leaf [(25, 2), (28, 35), (6, 33), (34, 49), (15, 36)])
          (.branch 15
            (.branch 28
              (.leaf [(0, 25), (6, 33)])
              (.leaf [(2, 25), (0, 35), (6, 33), (16, 39)]))
            (.branch 28
              (.leaf [(0, 25), (6, 33), (17, 38), (34, 49)])
              (.leaf [(2, 25), (0, 35), (6, 33), (16, 39), (17, 38), (34, 49)])))))
      (.branch 42
        (.branch 25
          (.leaf [(6, 33), (28, 3), (36, 5), (34, 49), (23, 39)])
          (.leaf [(28, 3), (36, 5), (34, 49), (4, 33), (37, 6), (38, 45), (0, 23), (39, 51)]))
        (.branch 25
          (.branch 3
            (.leaf [(33, 6), (36, 5), (17, 38), (45, 16), (39, 23)])
            (.leaf [(19, 45), (33, 6), (35, 28), (16, 39), (23, 49), (34, 5), (17, 38), (15, 36)]))
          (.branch 45
            (.branch 49
              (.leaf [(2, 28), (33, 6), (39, 51)])
              (.leaf [(34, 3), (15, 36), (37, 6), (33, 4), (35, 28), (2, 23), (39, 51)]))
            (.branch 49
              (.leaf [(0, 35), (2, 28), (3, 19), (16, 39), (33, 6), (36, 5), (17, 38)])
              (.branch 3
                (.leaf [(2, 23), (0, 35), (4, 33), (36, 5), (17, 38), (6, 37), (16, 39)])
                (.branch 6
                  (.leaf [(0, 23), (2, 28), (16, 39), (34, 5), (17, 38), (15, 36)])
                  (.branch 5
                    (.leaf [(15, 38), (33, 4), (37, 16), (51, 39), (0, 23), (2, 28)])
                    (.branch 16
                      (.leaf [(2, 23), (0, 35), (4, 33), (17, 38), (15, 36)])
                      (.branch 23
                        (.leaf [(17, 38), (15, 36), (28, 35), (4, 33)])
                        (.leaf [(0, 35), (2, 28), (4, 33), (17, 38), (15, 36), (39, 51)]))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootTSSTS : treeOK treeRootTSSTS ([0, 2, 3, 4, 5, 6, 14, 15, 16, 17, 19, 23, 25, 28, 30, 33, 34, 35, 36, 37, 38, 39, 42, 45, 49, 51]) 10 = true := by rfl

private def treeRootTSST : Tree := .branch 9 treeRootTSSTT treeRootTSSTS
private theorem checkedRootTSST : treeOK treeRootTSST ([0, 2, 3, 4, 5, 6, 9, 14, 15, 16, 17, 19, 23, 25, 28, 30, 33, 34, 35, 36, 37, 38, 39, 42, 45, 49, 51]) 10 = true := by
  exact joinChecks 9 treeRootTSSTT treeRootTSSTS ([0, 2, 3, 4, 5, 6, 9, 14, 15, 16, 17, 19, 23, 25, 28, 30, 33, 34, 35, 36, 37, 38, 39, 42, 45, 49, 51]) 10
    (by rfl) checkedRootTSSTT checkedRootTSSTS

set_option maxRecDepth 32768 in
private def treeRootTSSST : Tree :=
  (.branch 35
    (.branch 15
      (.branch 25
        (.leaf [(7, 33), (16, 39)])
        (.branch 23
          (.leaf [(7, 33), (16, 37)])
          (.branch 16
            (.leaf [(7, 33), (20, 51)])
            (.leaf [(7, 33), (37, 20), (39, 51)]))))
      (.branch 23
        (.leaf [(3, 19), (16, 37), (18, 25), (20, 51), (38, 7)])
        (.branch 25
          (.leaf [(3, 19), (16, 39), (38, 7), (33, 40)])
          (.branch 37
            (.leaf [(3, 19), (38, 7), (33, 40), (39, 51)])
            (.leaf [(3, 19), (16, 39), (18, 49), (20, 51), (38, 7), (33, 40)])))))
    (.branch 25
      (.branch 15
        (.leaf [(14, 39), (19, 9), (16, 28), (7, 33), (6, 29)])
        (.branch 28
          (.leaf [(6, 33), (14, 39), (23, 49), (38, 9)])
          (.branch 19
            (.leaf [(14, 39), (38, 7), (33, 6), (29, 23)])
            (.leaf [(3, 14), (40, 33), (6, 29), (49, 23), (39, 16), (9, 38), (7, 42)]))))
      (.branch 23
        (.branch 3
          (.leaf [(4, 33), (18, 6), (51, 20), (37, 16), (9, 38), (7, 42)])
          (.branch 6
            (.branch 42
              (.leaf [(9, 38)])
              (.leaf [(7, 28), (16, 9), (19, 40), (15, 38)]))
            (.branch 7
              (.leaf [(14, 37), (15, 40), (16, 9), (20, 51)])
              (.leaf [(4, 33), (14, 37), (20, 51), (28, 16), (9, 38), (15, 40), (19, 42)]))))
        (.branch 28
          (.branch 6
            (.branch 15
              (.leaf [(9, 19), (14, 39)])
              (.leaf [(4, 49), (14, 39), (38, 9), (19, 42)]))
            (.branch 49
              (.leaf [(14, 39), (20, 51), (33, 48), (38, 9)])
              (.branch 9
                (.branch 14
                  (.leaf [(4, 33), (15, 42), (20, 51)])
                  (.leaf [(4, 33), (15, 42), (37, 20), (39, 51)]))
                (.branch 14
                  (.leaf [(4, 33), (19, 42), (15, 38), (20, 51)])
                  (.leaf [(4, 33), (19, 42), (15, 38), (37, 20), (39, 51)])))))
          (.branch 6
            (.branch 15
              (.leaf [(0, 7), (19, 9), (2, 14), (16, 39)])
              (.branch 9
                (.leaf [(0, 7), (4, 49), (39, 14), (3, 48)])
                (.branch 42
                  (.leaf [(4, 49), (39, 14), (3, 48)])
                  (.leaf [(0, 7), (2, 14), (4, 49), (16, 39), (40, 19), (3, 48)]))))
            (.branch 15
              (.branch 9
                (.leaf [(0, 7), (29, 4), (33, 48), (14, 37), (20, 51)])
                (.branch 14
                  (.leaf [(0, 7), (20, 51), (29, 4), (33, 48)])
                  (.branch 33
                    (.branch 16
                      (.leaf [(20, 51)])
                      (.leaf [(37, 20), (39, 51)]))
                    (.branch 16
                      (.leaf [(0, 7), (4, 29), (20, 51)])
                      (.leaf [(0, 7), (4, 29), (37, 20), (39, 51)])))))
              (.branch 7
                (.leaf [(18, 49), (4, 29), (40, 19), (48, 3), (2, 9), (14, 37), (16, 39), (20, 51)])
                (.branch 9
                  (.branch 4
                    (.branch 14
                      (.leaf [(20, 51)])
                      (.leaf [(3, 48), (37, 20), (39, 51)]))
                    (.branch 14
                      (.leaf [(18, 49), (20, 51), (40, 33)])
                      (.leaf [(3, 48), (18, 49), (33, 40), (37, 20), (39, 51)])))
                  (.branch 14
                    (.leaf [(16, 42), (18, 49), (19, 40), (20, 51), (29, 4), (33, 48)])
                    (.branch 4
                      (.branch 16
                        (.leaf [(20, 51), (40, 19), (3, 48)])
                        (.leaf [(2, 42), (37, 20), (39, 51), (40, 19), (3, 48)]))
                      (.branch 16
                        (.branch 3
                          (.leaf [(18, 49), (20, 51), (33, 40)])
                          (.leaf [(18, 49), (19, 40), (20, 51), (33, 48)]))
                        (.branch 19
                          (.leaf [(18, 49), (33, 48), (37, 20), (39, 51)])
                          (.leaf [(2, 42), (3, 48), (18, 49), (33, 40), (37, 20), (39, 51)])))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootTSSST : treeOK treeRootTSSST ([0, 2, 3, 4, 6, 7, 9, 14, 15, 16, 18, 19, 20, 23, 25, 28, 29, 33, 35, 37, 38, 39, 40, 42, 48, 49, 51]) 10 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootTSSSS : Tree :=
  (.branch 9
    (.branch 25
      (.branch 29
        (.leaf [(12, 39), (14, 3), (49, 15), (40, 33), (7, 42)])
        (.branch 15
          (.leaf [(12, 39), (14, 17), (20, 45), (28, 7), (31, 6)])
          (.leaf [(12, 39), (20, 45), (23, 49), (31, 6), (3, 14), (17, 42), (7, 28), (33, 40)])))
      (.branch 6
        (.branch 23
          (.leaf [(20, 45), (7, 28), (3, 14), (15, 40), (17, 42)])
          (.branch 3
            (.leaf [(4, 49), (12, 39), (20, 45), (0, 7), (40, 17)])
            (.leaf [(4, 49), (12, 39), (20, 45), (0, 7), (48, 17), (14, 50), (28, 40), (15, 42)])))
        (.branch 23
          (.branch 40
            (.leaf [(3, 14), (4, 31), (7, 42), (12, 37), (18, 45)])
            (.leaf [(12, 37), (18, 45), (20, 51), (31, 4), (33, 7), (28, 3), (14, 17), (15, 42)]))
          (.branch 14
            (.branch 4
              (.leaf [(18, 45), (0, 7), (20, 51), (28, 40), (15, 42)])
              (.branch 7
                (.leaf [(29, 45), (18, 49), (15, 40), (20, 51)])
                (.leaf [(31, 0), (42, 15), (48, 33), (40, 28), (29, 45), (18, 49), (20, 51)])))
            (.branch 28
              (.leaf [(0, 31), (4, 33), (48, 17), (42, 15), (12, 39), (51, 20), (37, 49), (18, 45)])
              (.branch 4
                (.branch 15
                  (.leaf [(7, 0), (17, 48), (18, 45), (12, 37), (20, 51)])
                  (.branch 17
                    (.leaf [(7, 0), (18, 45), (12, 37), (20, 51)])
                    (.branch 20
                      (.leaf [(0, 7), (3, 48), (12, 39)])
                      (.leaf [(3, 48), (18, 45), (0, 7), (37, 12), (39, 51)]))))
                (.branch 15
                  (.branch 45
                    (.leaf [(7, 33), (17, 48), (37, 12)])
                    (.branch 0
                      (.leaf [(29, 17), (33, 48), (12, 37), (20, 51)])
                      (.branch 12
                        (.leaf [(7, 33), (20, 51), (29, 17)])
                        (.leaf [(7, 33), (29, 17), (37, 20), (39, 51)]))))
                  (.branch 17
                    (.leaf [(31, 0), (7, 33), (12, 39), (51, 20), (37, 49), (18, 45)])
                    (.branch 45
                      (.leaf [(3, 48), (40, 33), (7, 42), (49, 37), (12, 39)])
                      (.branch 7
                        (.branch 37
                          (.leaf [(3, 48), (39, 51)])
                          (.leaf [(3, 48), (12, 39), (18, 49), (20, 51)]))
                        (.branch 37
                          (.leaf [(0, 31), (3, 48), (33, 40), (39, 51)])
                          (.leaf [(0, 31), (3, 48), (12, 39), (18, 49), (20, 51), (33, 40)]))))))))))))
    (.branch 37
      (.branch 7
        (.branch 19
          (.leaf [(2, 23), (39, 51), (4, 29), (17, 48)])
          (.leaf [(18, 45), (50, 23), (2, 31), (39, 51), (3, 15), (40, 17), (29, 4), (35, 48)]))
        (.branch 19
          (.branch 23
            (.leaf [(17, 38), (15, 36), (28, 35), (4, 33)])
            (.branch 29
              (.leaf [(0, 35), (15, 38), (33, 48), (39, 51)])
              (.branch 35
                (.leaf [(17, 38), (15, 36), (39, 51)])
                (.branch 48
                  (.leaf [(2, 28), (15, 38), (39, 51)])
                  (.leaf [(2, 28), (4, 33), (17, 38), (15, 36), (39, 51)])))))
          (.branch 23
            (.branch 15
              (.leaf [(18, 45), (28, 35), (31, 4)])
              (.branch 4
                (.leaf [(18, 45), (34, 3), (28, 40), (38, 17)])
                (.leaf [(18, 45), (31, 38), (33, 40), (17, 42), (34, 3), (28, 35)])))
            (.branch 28
              (.leaf [(18, 45), (0, 31), (4, 33), (39, 51), (36, 48), (15, 38), (17, 42)])
              (.branch 15
                (.branch 4
                  (.leaf [(0, 45), (17, 48), (39, 51)])
                  (.leaf [(2, 31), (18, 45), (0, 35), (29, 17), (33, 48), (39, 51)]))
                (.branch 17
                  (.leaf [(2, 31), (3, 34), (18, 45), (0, 35), (4, 33), (39, 51)])
                  (.branch 4
                    (.leaf [(0, 45), (2, 42), (34, 3), (36, 48), (38, 50), (39, 51)])
                    (.leaf [(18, 45), (29, 36), (34, 3), (39, 51), (40, 33), (48, 35), (0, 31), (2, 42), (38, 50)]))))))))
      (.branch 3
        (.branch 0
          (.branch 6
            (.branch 12
              (.leaf [(4, 49), (16, 42), (17, 40)])
              (.leaf [(2, 42), (4, 49), (16, 39), (40, 17), (38, 50)]))
            (.branch 17
              (.leaf [(2, 12), (16, 39), (18, 49), (4, 33), (20, 51)])
              (.branch 4
                (.branch 12
                  (.leaf [(16, 42), (20, 51)])
                  (.leaf [(2, 42), (16, 39), (20, 51), (38, 50)]))
                (.leaf [(18, 49), (20, 51), (29, 36), (33, 40), (50, 38), (2, 12), (39, 16)]))))
          (.branch 4
            (.branch 38
              (.leaf [(18, 6), (20, 51), (2, 23), (39, 16)])
              (.leaf [(36, 7), (40, 17), (50, 23), (2, 12), (42, 16), (39, 51), (6, 18), (20, 45)]))
            (.branch 6
              (.leaf [(20, 45), (36, 7), (40, 17), (49, 23), (16, 39), (42, 2), (12, 38), (25, 50)])
              (.branch 38
                (.leaf [(20, 51), (33, 40), (35, 42), (16, 39), (36, 29), (2, 23), (25, 18)])
                (.branch 2
                  (.branch 45
                    (.leaf [(17, 40), (33, 7), (39, 51)])
                    (.leaf [(16, 39), (18, 49), (20, 51), (7, 33), (36, 29), (17, 40)]))
                  (.branch 16
                    (.leaf [(12, 35), (20, 51), (7, 33), (36, 29), (17, 40), (18, 25), (49, 23)])
                    (.branch 23
                      (.leaf [(12, 35), (36, 7), (33, 40), (17, 42), (18, 25), (45, 20)])
                      (.branch 7
                        (.leaf [(35, 12), (39, 51), (20, 45), (29, 17), (49, 18), (25, 50)])
                        (.leaf [(33, 40), (36, 29), (17, 42), (35, 12), (39, 51), (20, 45), (49, 18), (25, 50)])))))))))
        (.branch 7
          (.branch 23
            (.branch 6
              (.leaf [(4, 25), (12, 19), (14, 17), (15, 40), (16, 45)])
              (.branch 19
                (.leaf [(17, 14), (18, 25), (4, 35), (20, 51)])
                (.leaf [(12, 35), (14, 17), (15, 40), (4, 31), (16, 45), (18, 25), (20, 51)])))
            (.branch 25
              (.leaf [(10, 39), (20, 45), (16, 31), (49, 15), (6, 29), (12, 19), (35, 14), (17, 40)])
              (.branch 6
                (.branch 14
                  (.leaf [(4, 49), (12, 19), (15, 40), (16, 45)])
                  (.leaf [(2, 12), (4, 49), (10, 39), (15, 40), (16, 45), (17, 48), (19, 50)]))
                (.branch 14
                  (.branch 45
                    (.leaf [(31, 4), (40, 15)])
                    (.leaf [(12, 19), (16, 31), (18, 49), (4, 29), (15, 40), (20, 51)]))
                  (.branch 19
                    (.branch 4
                      (.leaf [(10, 39), (17, 48), (20, 51)])
                      (.leaf [(10, 39), (15, 49), (20, 51), (29, 17), (35, 48)]))
                    (.branch 4
                      (.leaf [(2, 12), (10, 39), (15, 40), (16, 45), (17, 48), (20, 51)])
                      (.branch 39
                        (.leaf [(2, 31), (20, 45), (18, 49), (15, 40), (29, 17)])
                        (.branch 45
                          (.leaf [(31, 2), (12, 35), (48, 17), (40, 15)])
                          (.leaf [(16, 31), (2, 12), (18, 49), (15, 40), (20, 51), (29, 17), (35, 48)])))))))))
          (.branch 23
            (.branch 35
              (.branch 45
                (.leaf [(10, 33), (17, 40), (15, 36)])
                (.leaf [(10, 33), (16, 31), (18, 25), (19, 40), (17, 38), (15, 36), (20, 51)]))
              (.branch 19
                (.branch 6
                  (.branch 14
                    (.leaf [(4, 25), (15, 38), (16, 28)])
                    (.leaf [(4, 25), (16, 28), (17, 38), (15, 36)]))
                  (.branch 25
                    (.leaf [(10, 33), (16, 28), (14, 17), (36, 15)])
                    (.branch 14
                      (.leaf [(4, 33), (15, 38), (16, 28), (20, 51)])
                      (.leaf [(4, 33), (16, 28), (17, 38), (15, 36), (20, 51)]))))
                (.branch 38
                  (.leaf [(14, 36), (20, 51), (4, 25), (18, 6), (10, 33), (40, 28), (16, 42)])
                  (.branch 6
                    (.branch 42
                      (.leaf [(4, 25), (14, 36), (20, 45)])
                      (.branch 40
                        (.leaf [(4, 25), (14, 36), (16, 45)])
                        (.leaf [(4, 25), (15, 36), (14, 17), (20, 45), (16, 28)])))
                    (.branch 16
                      (.branch 25
                        (.leaf [(10, 33), (14, 17), (36, 15)])
                        (.branch 33
                          (.leaf [(15, 36), (14, 17)])
                          (.branch 14
                            (.leaf [(15, 40), (20, 51)])
                            (.leaf [(17, 40), (15, 36), (20, 51)]))))
                      (.branch 40
                        (.leaf [(10, 42), (14, 36), (31, 4), (18, 25), (45, 20)])
                        (.branch 4
                          (.leaf [(10, 42), (15, 36), (14, 17), (18, 45), (20, 51)])
                          (.branch 42
                            (.branch 18
                              (.leaf [(14, 36), (20, 51)])
                              (.leaf [(14, 36), (25, 51), (20, 45)]))
                            (.branch 14
                              (.branch 18
                                (.leaf [(10, 33), (20, 51)])
                                (.leaf [(10, 33), (25, 51), (20, 45)]))
                              (.branch 18
                                (.leaf [(10, 33), (15, 36), (20, 51)])
                                (.leaf [(10, 33), (15, 36), (25, 51), (20, 45)])))))))))))
            (.branch 35
              (.branch 45
                (.leaf [(17, 40), (30, 51), (31, 2), (25, 50), (33, 10), (34, 49), (15, 36)])
                (.branch 15
                  (.branch 25
                    (.leaf [(17, 29), (19, 31), (16, 39), (10, 33)])
                    (.leaf [(2, 31), (16, 39), (10, 33), (17, 29), (18, 30), (19, 50), (20, 51)]))
                  (.branch 25
                    (.branch 17
                      (.leaf [(19, 31), (16, 39), (10, 33), (34, 49)])
                      (.leaf [(29, 36), (34, 49), (38, 31), (16, 39), (10, 33), (19, 40)]))
                    (.branch 31
                      (.leaf [(20, 51), (30, 18), (34, 49), (36, 29), (17, 40), (33, 10)])
                      (.branch 17
                        (.leaf [(16, 39), (10, 33), (19, 50), (20, 51), (30, 18), (34, 49)])
                        (.leaf [(16, 39), (10, 33), (20, 51), (29, 36), (30, 18), (34, 49), (38, 50), (19, 40)]))))))
              (.branch 25
                (.branch 15
                  (.branch 16
                    (.leaf [(10, 33), (6, 29), (12, 19), (14, 17)])
                    (.branch 29
                      (.leaf [(14, 39), (10, 33), (12, 19)])
                      (.branch 19
                        (.leaf [(6, 33), (10, 39), (14, 17)])
                        (.leaf [(12, 39), (10, 33), (6, 31), (14, 17), (20, 45)]))))
                  (.branch 16
                    (.branch 17
                      (.leaf [(6, 33), (12, 19), (34, 49)])
                      (.leaf [(10, 33), (6, 29), (14, 36), (34, 49), (38, 12), (19, 40)]))
                    (.branch 17
                      (.branch 19
                        (.leaf [(6, 33), (10, 39), (34, 49)])
                        (.leaf [(12, 39), (10, 33), (6, 31), (20, 45), (34, 49)]))
                      (.branch 19
                        (.leaf [(28, 29), (6, 33), (10, 39), (14, 36), (34, 49)])
                        (.branch 29
                          (.leaf [(14, 39), (12, 38), (34, 49), (40, 33), (10, 42)])
                          (.leaf [(20, 45), (28, 40), (34, 49), (36, 14), (42, 10), (33, 6), (31, 38), (12, 39)]))))))
                (.branch 31
                  (.branch 17
                    (.leaf [(12, 39), (10, 33), (28, 50), (34, 49), (15, 36), (18, 30), (45, 20)])
                    (.branch 15
                      (.branch 39
                        (.leaf [(20, 45), (18, 30), (29, 28)])
                        (.branch 45
                          (.leaf [(10, 33), (14, 50), (30, 51)])
                          (.leaf [(10, 33), (14, 50), (18, 30), (20, 51), (28, 29)])))
                      (.branch 39
                        (.leaf [(20, 45), (30, 18), (34, 49), (50, 28), (29, 36), (40, 33)])
                        (.branch 18
                          (.leaf [(20, 51), (42, 10), (14, 50), (28, 29), (36, 48), (33, 40)])
                          (.leaf [(30, 51), (20, 45), (34, 49), (42, 10), (14, 50), (28, 29), (36, 48), (33, 40)])))))
                  (.branch 45
                    (.branch 14
                      (.leaf [(28, 40), (34, 49), (15, 42), (10, 33), (4, 30), (6, 51)])
                      (.branch 33
                        (.leaf [(17, 42), (30, 51), (34, 49), (15, 36), (39, 12)])
                        (.leaf [(6, 51), (30, 4), (34, 49), (50, 28), (2, 12), (39, 10), (36, 48), (15, 40), (17, 42)])))
                    (.branch 17
                      (.branch 39
                        (.branch 49
                          (.leaf [(2, 28), (6, 33), (19, 50)])
                          (.branch 4
                            (.leaf [(2, 28), (6, 18), (15, 36), (19, 50)])
                            (.leaf [(2, 28), (15, 36), (19, 50), (30, 18), (6, 33)])))
                        (.branch 49
                          (.leaf [(0, 10), (16, 28), (2, 12), (19, 50), (20, 51), (6, 33)])
                          (.branch 6
                            (.leaf [(0, 10), (4, 30), (15, 36), (16, 28), (2, 12), (19, 50)])
                            (.leaf [(0, 10), (15, 36), (16, 28), (2, 12), (18, 30), (4, 33), (19, 50), (20, 51)]))))
                      (.branch 15
                        (.branch 39
                          (.branch 4
                            (.leaf [(2, 28), (6, 18), (19, 50)])
                            (.leaf [(2, 28), (19, 50), (29, 6), (18, 30), (33, 48)]))
                          (.branch 6
                            (.branch 2
                              (.leaf [(0, 10), (4, 30), (19, 50)])
                              (.leaf [(0, 10), (4, 30), (12, 19), (14, 50), (16, 28)]))
                            (.branch 28
                              (.leaf [(0, 10), (12, 19), (18, 30), (4, 33), (20, 51)])
                              (.branch 4
                                (.branch 2
                                  (.leaf [(0, 10), (19, 50), (20, 51)])
                                  (.leaf [(0, 10), (12, 19), (14, 50), (20, 51)]))
                                (.branch 2
                                  (.leaf [(0, 10), (18, 30), (19, 50), (20, 51), (33, 48)])
                                  (.leaf [(0, 10), (12, 19), (14, 50), (18, 30), (20, 51), (33, 48)]))))))
                        (.branch 28
                          (.branch 10
                            (.leaf [(14, 36), (19, 12), (20, 51), (6, 18), (30, 4), (34, 49)])
                            (.branch 51
                              (.leaf [(14, 36), (18, 49), (4, 33), (38, 12), (19, 42)])
                              (.branch 4
                                (.leaf [(6, 18), (38, 12), (19, 42), (39, 14), (36, 48)])
                                (.leaf [(30, 18), (6, 33), (34, 49), (38, 12), (19, 42), (39, 14), (36, 48)]))))
                          (.branch 33
                            (.branch 12
                              (.leaf [(16, 42), (20, 51), (29, 36), (14, 50), (30, 18)])
                              (.leaf [(20, 51), (29, 36), (30, 18), (34, 49), (38, 50), (19, 42), (2, 14), (16, 39)]))
                            (.branch 39
                              (.branch 4
                                (.leaf [(2, 42), (6, 18), (36, 48), (38, 50), (19, 40)])
                                (.leaf [(2, 42), (30, 18), (6, 29), (34, 49), (36, 48), (38, 50), (19, 40)]))
                              (.branch 19
                                (.branch 4
                                  (.leaf [(0, 10), (2, 14), (18, 6), (20, 51), (36, 48)])
                                  (.leaf [(0, 10), (2, 14), (20, 51), (30, 18), (6, 29), (34, 49), (36, 48)]))
                                (.branch 2
                                  (.branch 4
                                    (.leaf [(0, 10), (18, 6), (20, 51), (36, 48), (38, 50)])
                                    (.leaf [(0, 10), (20, 51), (30, 18), (6, 29), (34, 49), (36, 48), (38, 50)]))
                                  (.branch 4
                                    (.leaf [(0, 10), (12, 38), (16, 42), (18, 6), (20, 51), (48, 36), (14, 50)])
                                    (.leaf [(0, 10), (12, 38), (16, 42), (20, 51), (30, 18), (6, 29), (34, 49), (48, 36), (14, 50)]))))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootTSSSS : treeOK treeRootTSSSS ([0, 2, 3, 4, 6, 7, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 23, 25, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 42, 45, 48, 49, 50, 51]) 11 = true := by rfl

private def treeRootTSSS : Tree := .branch 5 treeRootTSSST treeRootTSSSS
private theorem checkedRootTSSS : treeOK treeRootTSSS ([0, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 23, 25, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 42, 45, 48, 49, 50, 51]) 11 = true := by
  exact joinChecks 5 treeRootTSSST treeRootTSSSS ([0, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 23, 25, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 42, 45, 48, 49, 50, 51]) 11
    (by rfl) checkedRootTSSST checkedRootTSSSS

private def treeRootTSS : Tree := .branch 47 treeRootTSST treeRootTSSS
private theorem checkedRootTSS : treeOK treeRootTSS ([0, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 23, 25, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 42, 45, 47, 48, 49, 50, 51]) 11 = true := by
  exact joinChecks 47 treeRootTSST treeRootTSSS ([0, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 23, 25, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 42, 45, 47, 48, 49, 50, 51]) 11
    (by rfl) checkedRootTSST checkedRootTSSS

private def treeRootTS : Tree := .branch 43 treeRootTST treeRootTSS
private theorem checkedRootTS : treeOK treeRootTS ([0, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 23, 25, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 45, 47, 48, 49, 50, 51]) 11 = true := by
  exact joinChecks 43 treeRootTST treeRootTSS ([0, 2, 3, 4, 5, 6, 7, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 23, 25, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 45, 47, 48, 49, 50, 51]) 11
    (by rfl) checkedRootTST checkedRootTSS

private def treeRootT : Tree := .branch 11 treeRootTT treeRootTS
private theorem checkedRootT : treeOK treeRootT ([0, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 23, 25, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 45, 47, 48, 49, 50, 51]) 11 = true := by
  exact joinChecks 11 treeRootTT treeRootTS ([0, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 23, 25, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 45, 47, 48, 49, 50, 51]) 11
    (by rfl) checkedRootTT checkedRootTS

set_option maxRecDepth 32768 in
private def treeRootSTTTT : Tree :=
  (.branch 13
    (.leaf [(4, 35), (17, 46)])
    (.leaf [(4, 35), (7, 36), (37, 20), (39, 46), (17, 40)]))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSTTTT : treeOK treeRootSTTTT ([4, 7, 13, 17, 20, 21, 35, 36, 37, 39, 40, 46, 50]) 8 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootSTTTS : Tree :=
  (.branch 13
    (.leaf [(4, 35), (7, 32), (10, 37), (15, 46), (17, 48)])
    (.branch 32
      (.branch 48
        (.leaf [(10, 37), (15, 46)])
        (.leaf [(4, 35), (10, 37), (17, 46), (15, 36)]))
      (.branch 46
        (.leaf [(4, 35), (10, 37), (34, 7), (36, 48)])
        (.branch 36
          (.leaf [(4, 35), (17, 40), (20, 37), (10, 39)])
          (.leaf [(4, 35), (7, 34), (15, 40), (17, 48), (20, 37), (10, 39)])))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSTTTS : treeOK treeRootSTTTS ([4, 7, 10, 13, 15, 17, 20, 21, 32, 34, 35, 36, 37, 39, 40, 46, 48, 50]) 9 = true := by rfl

private def treeRootSTTT : Tree := .branch 3 treeRootSTTTT treeRootSTTTS
private theorem checkedRootSTTT : treeOK treeRootSTTT ([3, 4, 7, 10, 13, 15, 17, 20, 21, 32, 34, 35, 36, 37, 39, 40, 46, 48, 50]) 9 = true := by
  exact joinChecks 3 treeRootSTTTT treeRootSTTTS ([3, 4, 7, 10, 13, 15, 17, 20, 21, 32, 34, 35, 36, 37, 39, 40, 46, 48, 50]) 9
    (by rfl) checkedRootSTTTT checkedRootSTTTS

set_option maxRecDepth 32768 in
private def treeRootSTTST : Tree :=
  (.branch 13
    (.leaf [(16, 37), (46, 17), (5, 50), (29, 4), (35, 0), (7, 33), (21, 51)])
    (.branch 17
      (.leaf [(36, 7), (0, 35), (4, 33), (21, 51), (20, 37), (16, 39)])
      (.branch 7
        (.branch 20
          (.leaf [(5, 50), (16, 39), (29, 4)])
          (.leaf [(5, 50), (21, 51), (29, 4), (37, 16), (39, 46)]))
        (.branch 4
          (.branch 20
            (.leaf [(16, 39), (36, 5), (38, 50)])
            (.leaf [(21, 51), (36, 5), (37, 16), (38, 50), (39, 46)]))
          (.branch 20
            (.leaf [(0, 35), (16, 39), (21, 33), (29, 36), (5, 50)])
            (.leaf [(0, 35), (29, 36), (5, 50), (37, 16), (40, 33), (21, 51), (39, 46)]))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSTTST : treeOK treeRootSTTST ([0, 4, 5, 7, 13, 16, 17, 20, 21, 29, 33, 35, 36, 37, 38, 39, 40, 46, 50, 51]) 9 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootSTTSS : Tree :=
  (.branch 5
    (.branch 33
      (.leaf [(0, 35), (19, 46), (15, 38), (13, 20), (37, 16), (39, 51)])
      (.branch 13
        (.leaf [(7, 0), (15, 46), (16, 37), (21, 51), (29, 4), (35, 48)])
        (.branch 46
          (.leaf [(16, 37), (21, 51), (29, 4), (38, 7), (0, 35)])
          (.leaf [(19, 40), (15, 38), (7, 0), (21, 51), (20, 37), (16, 39), (29, 4), (35, 48)]))))
    (.branch 7
      (.branch 39
        (.leaf [(15, 40), (19, 50), (20, 37), (4, 29), (17, 48)])
        (.branch 17
          (.leaf [(4, 35), (10, 37), (13, 20), (19, 50), (21, 51)])
          (.branch 20
            (.leaf [(15, 40), (19, 50), (29, 4), (35, 48)])
            (.leaf [(10, 37), (13, 40), (15, 46), (19, 50), (21, 51), (29, 4), (35, 48)]))))
      (.branch 13
        (.branch 33
          (.leaf [(0, 35), (15, 46), (16, 37), (17, 29), (19, 50)])
          (.branch 17
            (.leaf [(4, 35), (0, 10), (16, 37), (19, 50), (21, 51)])
            (.leaf [(15, 46), (16, 37), (10, 0), (19, 50), (21, 51), (29, 4), (35, 48)])))
        (.branch 17
          (.branch 10
            (.leaf [(4, 35), (15, 36), (19, 50), (21, 51), (20, 32)])
            (.branch 20
              (.leaf [(0, 35), (4, 33), (15, 36), (16, 39), (19, 50)])
              (.leaf [(0, 35), (4, 33), (15, 36), (19, 50), (21, 51), (32, 39), (16, 37)])))
          (.branch 33
            (.branch 20
              (.leaf [(0, 35), (16, 39), (19, 50), (29, 36)])
              (.branch 39
                (.leaf [(0, 35), (19, 50), (29, 36)])
                (.branch 15
                  (.leaf [(0, 35), (16, 37), (19, 50)])
                  (.leaf [(0, 35), (16, 37), (29, 36), (38, 50), (19, 46)]))))
            (.branch 39
              (.branch 15
                (.leaf [(0, 35), (4, 29), (19, 50), (20, 37)])
                (.leaf [(0, 35), (4, 29), (20, 37), (36, 48), (38, 50), (19, 40)]))
              (.branch 15
                (.leaf [(16, 37), (10, 0), (19, 50), (21, 51), (20, 32), (29, 4), (35, 48)])
                (.branch 20
                  (.branch 35
                    (.leaf [(29, 36), (38, 50), (19, 40)])
                    (.leaf [(0, 10), (4, 29), (36, 48), (38, 50), (19, 40)]))
                  (.branch 19
                    (.branch 35
                      (.leaf [(10, 37), (21, 51), (29, 36)])
                      (.leaf [(0, 10), (4, 29), (16, 37), (21, 51), (36, 48)]))
                    (.branch 35
                      (.leaf [(10, 37), (21, 51), (29, 36), (32, 40), (38, 50)])
                      (.leaf [(0, 10), (4, 29), (16, 37), (21, 51), (32, 40), (36, 48), (38, 50)])))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSTTSS : treeOK treeRootSTTSS ([0, 4, 5, 7, 10, 13, 15, 16, 17, 19, 20, 21, 29, 32, 33, 34, 35, 36, 37, 38, 39, 40, 46, 48, 50, 51]) 10 = true := by rfl

private def treeRootSTTS : Tree := .branch 3 treeRootSTTST treeRootSTTSS
private theorem checkedRootSTTS : treeOK treeRootSTTS ([0, 3, 4, 5, 7, 10, 13, 15, 16, 17, 19, 20, 21, 29, 32, 33, 34, 35, 36, 37, 38, 39, 40, 46, 48, 50, 51]) 10 = true := by
  exact joinChecks 3 treeRootSTTST treeRootSTTSS ([0, 3, 4, 5, 7, 10, 13, 15, 16, 17, 19, 20, 21, 29, 32, 33, 34, 35, 36, 37, 38, 39, 40, 46, 48, 50, 51]) 10
    (by rfl) checkedRootSTTST checkedRootSTTSS

private def treeRootSTT : Tree := .branch 26 treeRootSTTT treeRootSTTS
private theorem checkedRootSTT : treeOK treeRootSTT ([0, 3, 4, 5, 7, 10, 13, 15, 16, 17, 19, 20, 21, 26, 29, 32, 33, 34, 35, 36, 37, 38, 39, 40, 46, 48, 50, 51]) 10 = true := by
  exact joinChecks 26 treeRootSTTT treeRootSTTS ([0, 3, 4, 5, 7, 10, 13, 15, 16, 17, 19, 20, 21, 26, 29, 32, 33, 34, 35, 36, 37, 38, 39, 40, 46, 48, 50, 51]) 10
    (by rfl) checkedRootSTTT checkedRootSTTS

set_option maxRecDepth 32768 in
private def treeRootSTSTT : Tree :=
  (.branch 3
    (.branch 4
      (.leaf [(7, 36), (17, 40)])
      (.leaf [(6, 35), (7, 36), (11, 40), (17, 44)]))
    (.branch 4
      (.branch 36
        (.leaf [(10, 39), (17, 40)])
        (.leaf [(7, 34), (10, 39), (15, 40), (17, 48)]))
      (.branch 36
        (.leaf [(6, 35), (10, 39), (34, 44), (17, 40)])
        (.branch 17
          (.leaf [(6, 35), (10, 39), (11, 34), (7, 30)])
          (.branch 34
            (.leaf [(6, 35), (10, 39), (15, 40)])
            (.leaf [(6, 35), (7, 30), (10, 39), (11, 40), (15, 44)]))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSTSTT : treeOK treeRootSTSTT ([3, 4, 6, 7, 10, 11, 15, 17, 21, 30, 34, 35, 36, 39, 40, 44, 48, 50]) 9 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootSTSTS : Tree :=
  (.branch 4
    (.branch 3
      (.leaf [(0, 7), (16, 39), (36, 5), (40, 17), (38, 50)])
      (.branch 5
        (.leaf [(0, 7), (16, 39), (19, 40), (15, 38)])
        (.branch 7
          (.leaf [(10, 39), (15, 40), (17, 48), (19, 50)])
          (.branch 15
            (.leaf [(0, 10), (16, 39), (17, 48), (19, 50)])
            (.branch 17
              (.leaf [(0, 10), (16, 39), (19, 50)])
              (.leaf [(0, 10), (16, 39), (36, 48), (38, 50), (19, 40)]))))))
    (.branch 3
      (.branch 17
        (.leaf [(11, 36), (16, 39), (49, 21), (0, 7), (33, 6)])
        (.branch 7
          (.leaf [(5, 50), (11, 40), (16, 39), (21, 49), (29, 6)])
          (.branch 6
            (.leaf [(16, 39), (21, 49), (40, 11), (36, 5), (38, 50)])
            (.leaf [(0, 35), (16, 39), (29, 36), (5, 50), (38, 11), (40, 33), (21, 49)]))))
      (.branch 5
        (.branch 33
          (.leaf [(0, 35), (11, 38), (16, 39), (19, 44)])
          (.leaf [(16, 39), (21, 49), (29, 6), (48, 35), (0, 7), (11, 38), (15, 40), (19, 44)]))
        (.branch 7
          (.branch 17
            (.leaf [(6, 35), (10, 39), (15, 49), (19, 50)])
            (.leaf [(10, 39), (11, 40), (21, 49), (15, 44), (19, 50), (29, 6), (35, 48)]))
          (.branch 15
            (.branch 33
              (.leaf [(0, 35), (11, 34), (16, 39), (17, 29)])
              (.branch 35
                (.leaf [(10, 39), (11, 34), (17, 29), (19, 50)])
                (.leaf [(0, 10), (6, 29), (11, 34), (16, 39), (17, 48), (19, 50)])))
            (.branch 17
              (.leaf [(16, 39), (19, 50), (36, 11), (34, 49), (21, 33), (6, 35), (0, 10)])
              (.branch 33
                (.leaf [(0, 35), (16, 39), (29, 36), (49, 34), (11, 38), (44, 19)])
                (.branch 11
                  (.leaf [(16, 39), (10, 0), (21, 49), (29, 6), (35, 48), (44, 19)])
                  (.branch 19
                    (.branch 35
                      (.leaf [(10, 39), (21, 49), (29, 36)])
                      (.leaf [(0, 10), (6, 29), (16, 39), (21, 49), (36, 48)]))
                    (.branch 35
                      (.leaf [(10, 39), (21, 49), (29, 36), (34, 44), (38, 50)])
                      (.leaf [(0, 10), (6, 29), (16, 39), (21, 49), (34, 44), (36, 48), (38, 50)])))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSTSTS : treeOK treeRootSTSTS ([0, 3, 4, 5, 6, 7, 10, 11, 15, 16, 17, 19, 21, 29, 30, 33, 34, 35, 36, 38, 39, 40, 44, 48, 49, 50]) 10 = true := by rfl

private def treeRootSTST : Tree := .branch 26 treeRootSTSTT treeRootSTSTS
private theorem checkedRootSTST : treeOK treeRootSTST ([0, 3, 4, 5, 6, 7, 10, 11, 15, 16, 17, 19, 21, 26, 29, 30, 33, 34, 35, 36, 38, 39, 40, 44, 48, 49, 50]) 10 = true := by
  exact joinChecks 26 treeRootSTSTT treeRootSTSTS ([0, 3, 4, 5, 6, 7, 10, 11, 15, 16, 17, 19, 21, 26, 29, 30, 33, 34, 35, 36, 38, 39, 40, 44, 48, 49, 50]) 10
    (by rfl) checkedRootSTSTT checkedRootSTSTS

set_option maxRecDepth 32768 in
private def treeRootSTSST : Tree :=
  (.branch 5
    (.branch 15
      (.leaf [(0, 35), (13, 39), (16, 37), (11, 51)])
      (.branch 11
        (.leaf [(0, 35), (3, 19), (13, 39), (16, 41), (29, 47)])
        (.leaf [(0, 35), (3, 19), (29, 47), (38, 13), (41, 16), (46, 39), (49, 37), (44, 51)])))
    (.branch 15
      (.branch 39
        (.leaf [(17, 29), (30, 37), (11, 34), (35, 0), (45, 19)])
        (.branch 45
          (.leaf [(47, 50), (13, 34), (11, 37), (30, 51)])
          (.branch 11
            (.leaf [(0, 35), (13, 30), (17, 29), (19, 50)])
            (.leaf [(0, 35), (16, 37), (17, 29), (19, 50), (34, 13), (30, 51)]))))
      (.branch 11
        (.branch 19
          (.leaf [(0, 35), (17, 29), (30, 13), (32, 39), (16, 41)])
          (.branch 16
            (.leaf [(0, 35), (13, 30), (3, 32), (44, 17), (29, 47)])
            (.branch 29
              (.branch 3
                (.leaf [(0, 35), (13, 39)])
                (.leaf [(0, 35), (30, 13), (32, 39)]))
              (.branch 0
                (.leaf [(17, 44), (47, 50), (3, 30), (13, 39)])
                (.branch 3
                  (.leaf [(13, 39), (17, 44), (47, 50)])
                  (.leaf [(17, 44), (30, 13), (32, 39), (47, 50)]))))))
        (.branch 13
          (.branch 19
            (.leaf [(0, 35), (17, 29), (41, 16), (37, 49)])
            (.leaf [(3, 32), (35, 0), (41, 16), (45, 29), (46, 17), (47, 50), (49, 37), (44, 51)]))
          (.branch 19
            (.branch 16
              (.leaf [(0, 35), (30, 51), (34, 49), (36, 29), (17, 38)])
              (.leaf [(0, 35), (32, 39), (36, 29), (17, 38), (41, 34), (49, 37), (30, 51)]))
            (.branch 16
              (.leaf [(0, 35), (32, 3), (36, 29), (47, 50), (38, 17), (46, 30), (49, 34), (44, 51)])
              (.branch 17
                (.branch 3
                  (.leaf [(35, 0), (37, 49), (39, 51), (47, 50)])
                  (.leaf [(32, 39), (35, 0), (41, 34), (47, 50), (49, 37), (30, 51)]))
                (.branch 30
                  (.leaf [(32, 39), (35, 0), (36, 29), (41, 34), (45, 38), (47, 50)])
                  (.leaf [(35, 0), (36, 29), (41, 34), (3, 32), (45, 38), (46, 39), (47, 50), (49, 37), (44, 51)])))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSTSST : treeOK treeRootSTSST ([0, 3, 5, 11, 13, 15, 16, 17, 19, 29, 30, 32, 34, 35, 36, 37, 38, 39, 41, 44, 45, 46, 47, 49, 50, 51]) 10 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootSTSSS : Tree :=
  (.branch 5
    (.branch 15
      (.branch 6
        (.leaf [(4, 11), (39, 16), (43, 0), (7, 47)])
        (.branch 0
          (.leaf [(13, 39), (16, 37), (21, 51), (11, 4), (29, 47)])
          (.leaf [(7, 47), (13, 39), (21, 51), (29, 4), (11, 37), (16, 43), (35, 48)])))
      (.branch 4
        (.branch 39
          (.leaf [(6, 37), (38, 7), (0, 43), (3, 19), (40, 47)])
          (.branch 6
            (.branch 3
              (.leaf [(0, 7), (40, 47)])
              (.leaf [(16, 43), (0, 7), (19, 40), (47, 48)]))
            (.branch 3
              (.leaf [(0, 7), (16, 37), (21, 51), (38, 13), (40, 47)])
              (.leaf [(21, 51), (37, 16), (43, 0), (46, 19), (48, 47), (7, 38), (13, 40)]))))
        (.branch 6
          (.branch 3
            (.leaf [(0, 7), (8, 39), (16, 41), (21, 49), (38, 11), (40, 47)])
            (.leaf [(8, 39), (21, 49), (41, 16), (43, 0), (44, 19), (48, 47), (7, 38), (11, 40)]))
          (.branch 11
            (.branch 0
              (.leaf [(13, 39), (8, 29), (16, 41), (21, 49), (44, 19), (3, 48)])
              (.leaf [(7, 47), (13, 39), (21, 49), (29, 8), (35, 48), (41, 16), (43, 3), (19, 44)]))
            (.branch 39
              (.branch 47
                (.leaf [(21, 49), (35, 0), (37, 44), (19, 3)])
                (.branch 0
                  (.leaf [(21, 49), (37, 44), (40, 19), (3, 48)])
                  (.leaf [(7, 38), (21, 49), (35, 48), (37, 44), (40, 19), (3, 43)])))
              (.branch 19
                (.leaf [(13, 38), (41, 16), (37, 49), (21, 51), (43, 0), (7, 47), (29, 8), (35, 48)])
                (.branch 47
                  (.branch 16
                    (.leaf [(0, 35), (13, 38), (44, 51), (21, 49)])
                    (.branch 0
                      (.branch 21
                        (.leaf [(13, 38), (37, 44)])
                        (.leaf [(13, 38), (49, 37), (44, 51)]))
                      (.leaf [(3, 43), (8, 35), (13, 38), (21, 49), (37, 44)])))
                  (.branch 0
                    (.branch 37
                      (.leaf [(3, 48), (8, 29), (21, 51), (38, 13)])
                      (.leaf [(3, 48), (8, 29), (16, 41), (38, 13), (44, 51), (21, 49)]))
                    (.branch 16
                      (.leaf [(3, 48), (7, 38), (13, 40), (29, 8), (44, 51), (21, 49)])
                      (.branch 3
                        (.branch 8
                          (.leaf [(7, 38), (13, 40), (21, 49), (37, 44)])
                          (.branch 13
                            (.branch 21
                              (.leaf [(37, 44)])
                              (.leaf [(49, 37), (44, 51)]))
                            (.branch 21
                              (.leaf [(7, 38), (37, 44)])
                              (.leaf [(7, 38), (49, 37), (44, 51)]))))
                        (.branch 8
                          (.branch 13
                            (.branch 21
                              (.leaf [(37, 44)])
                              (.leaf [(49, 37), (44, 51)]))
                            (.branch 21
                              (.leaf [(7, 38), (37, 44)])
                              (.leaf [(7, 38), (49, 37), (44, 51)])))
                          (.branch 13
                            (.branch 21
                              (.leaf [(35, 48), (37, 44)])
                              (.leaf [(35, 48), (49, 37), (44, 51)]))
                            (.branch 21
                              (.leaf [(7, 38), (35, 48), (37, 44)])
                              (.leaf [(7, 38), (35, 48), (49, 37), (44, 51)]))))))))))))))
    (.branch 15
      (.branch 0
        (.branch 6
          (.leaf [(16, 39), (17, 48), (19, 50), (30, 4), (11, 34)])
          (.branch 11
            (.leaf [(16, 39), (13, 30), (19, 50), (17, 29), (47, 48)])
            (.leaf [(19, 50), (21, 51), (32, 39), (16, 37), (34, 13), (30, 4), (17, 29), (47, 48)])))
        (.branch 6
          (.branch 16
            (.leaf [(10, 47), (17, 48), (19, 50), (4, 11), (30, 7)])
            (.branch 47
              (.leaf [(17, 43), (21, 45), (19, 26), (30, 4)])
              (.leaf [(10, 39), (21, 45), (26, 19), (48, 17), (43, 50), (4, 11), (30, 7)])))
          (.branch 16
            (.branch 47
              (.leaf [(21, 51), (35, 4), (11, 34), (13, 30)])
              (.branch 4
                (.leaf [(13, 34), (7, 32), (17, 48), (19, 50)])
                (.leaf [(19, 50), (21, 51), (11, 34), (13, 30), (7, 32), (29, 17), (35, 48)])))
            (.branch 29
              (.branch 30
                (.leaf [(10, 39), (11, 34), (19, 50), (35, 48)])
                (.leaf [(19, 50), (21, 51), (35, 48), (7, 32), (10, 37), (11, 34), (13, 39)]))
              (.branch 30
                (.leaf [(11, 34), (21, 45), (26, 19), (32, 39), (10, 47), (35, 48), (17, 43)])
                (.branch 11
                  (.leaf [(13, 39), (10, 47), (7, 32), (21, 45), (26, 19), (35, 48), (17, 43)])
                  (.branch 39
                    (.leaf [(4, 35), (21, 45), (26, 19), (34, 7), (17, 43), (48, 47)])
                    (.leaf [(4, 35), (13, 34), (32, 7), (37, 10), (17, 43), (48, 47), (50, 19), (26, 51), (21, 45)]))))))))
      (.branch 11
        (.branch 0
          (.branch 3
            (.leaf [(21, 49), (41, 16), (44, 17), (50, 47), (6, 13), (29, 8)])
            (.branch 29
              (.leaf [(21, 49), (30, 13), (32, 39), (16, 41), (44, 19)])
              (.leaf [(8, 39), (16, 41), (21, 49), (30, 13), (6, 32), (17, 44), (19, 50), (47, 48)])))
          (.branch 3
            (.branch 29
              (.leaf [(13, 39), (16, 41), (21, 49)])
              (.branch 16
                (.leaf [(7, 47), (8, 35), (6, 13), (17, 44)])
                (.branch 6
                  (.leaf [(7, 47), (8, 39), (17, 44), (26, 49), (21, 45)])
                  (.leaf [(7, 47), (13, 39), (8, 35), (17, 44), (26, 49), (21, 45)]))))
            (.branch 29
              (.branch 39
                (.leaf [(7, 30), (21, 49), (35, 48), (43, 50)])
                (.leaf [(10, 41), (13, 30), (7, 32), (16, 43), (21, 49), (35, 48), (44, 19)]))
              (.branch 16
                (.branch 47
                  (.leaf [(8, 35), (17, 44), (21, 49), (30, 13)])
                  (.branch 6
                    (.leaf [(7, 30), (21, 49), (48, 17), (44, 19)])
                    (.leaf [(8, 35), (13, 30), (7, 32), (21, 49), (48, 17), (44, 19)])))
                (.branch 19
                  (.leaf [(21, 49), (41, 10), (43, 17), (8, 35), (48, 47), (6, 13), (30, 7), (32, 39)])
                  (.branch 39
                    (.leaf [(6, 35), (26, 49), (21, 45), (30, 7), (44, 17), (43, 50), (47, 48)])
                    (.branch 47
                      (.leaf [(8, 35), (26, 49), (21, 45), (30, 13), (6, 32), (43, 17)])
                      (.branch 6
                        (.leaf [(7, 30), (10, 41), (26, 49), (21, 45), (44, 17), (43, 50)])
                        (.leaf [(8, 35), (10, 41), (13, 30), (7, 32), (26, 49), (21, 45), (44, 17), (43, 50)])))))))))
        (.branch 29
          (.branch 3
            (.branch 39
              (.leaf [(21, 49), (35, 0), (7, 38), (37, 44)])
              (.branch 37
                (.leaf [(21, 51), (35, 0), (7, 38), (13, 40)])
                (.leaf [(16, 41), (35, 0), (7, 38), (13, 40), (44, 51), (21, 49)])))
            (.branch 39
              (.leaf [(21, 49), (40, 19), (41, 34), (44, 37), (30, 7), (38, 50), (43, 0), (35, 48)])
              (.branch 7
                (.leaf [(13, 40), (35, 48), (46, 19), (50, 43), (10, 41), (16, 37), (44, 51), (21, 49)])
                (.branch 37
                  (.leaf [(21, 51), (32, 40), (41, 34), (13, 38), (46, 19), (48, 35), (0, 43)])
                  (.branch 13
                    (.leaf [(46, 19), (44, 51), (21, 49), (48, 35), (50, 43), (0, 10), (16, 41)])
                    (.branch 19
                      (.leaf [(30, 51), (21, 49), (34, 41), (10, 0), (16, 43), (35, 48)])
                      (.leaf [(32, 40), (38, 50), (46, 30), (48, 35), (0, 10), (43, 16), (41, 34), (44, 51), (21, 49)])))))))
          (.branch 3
            (.branch 38
              (.branch 4
                (.leaf [(8, 39), (16, 37), (21, 51), (6, 46), (40, 47)])
                (.branch 6
                  (.leaf [(8, 39), (16, 41), (21, 49), (40, 47)])
                  (.branch 39
                    (.leaf [(0, 35), (21, 49), (37, 44)])
                    (.branch 37
                      (.leaf [(0, 35), (21, 51), (40, 47)])
                      (.leaf [(0, 35), (16, 41), (40, 47), (44, 51), (21, 49)])))))
              (.branch 6
                (.branch 16
                  (.leaf [(0, 7), (21, 49), (4, 44), (17, 40), (47, 50)])
                  (.branch 0
                    (.leaf [(8, 39), (21, 49), (41, 4), (44, 17), (40, 47)])
                    (.leaf [(8, 39), (26, 49), (21, 45), (36, 7), (41, 4), (44, 17), (40, 47)])))
                (.branch 16
                  (.branch 4
                    (.leaf [(0, 7), (21, 51), (36, 13), (46, 17), (40, 47)])
                    (.leaf [(8, 35), (0, 7), (36, 13), (46, 17), (40, 47), (44, 51), (21, 49)]))
                  (.branch 0
                    (.branch 39
                      (.leaf [(21, 49), (37, 44), (4, 41), (17, 40)])
                      (.branch 44
                        (.leaf [(21, 49), (36, 13), (40, 47)])
                        (.leaf [(36, 13), (37, 49), (4, 41), (21, 51), (46, 17), (40, 47)])))
                    (.branch 4
                      (.leaf [(8, 39), (26, 51), (21, 45), (46, 17), (50, 47), (7, 36), (13, 40)])
                      (.branch 39
                        (.leaf [(26, 49), (21, 45), (36, 7), (37, 44), (17, 40), (47, 50)])
                        (.branch 17
                          (.leaf [(8, 35), (13, 36), (7, 47), (37, 49), (26, 51), (21, 45)])
                          (.branch 21
                            (.leaf [(8, 35), (37, 44), (50, 47), (7, 36), (13, 40)])
                            (.branch 47
                              (.leaf [(8, 35), (13, 36), (26, 49), (37, 44)])
                              (.branch 13
                                (.branch 26
                                  (.leaf [(8, 35), (37, 44)])
                                  (.leaf [(8, 35), (49, 37), (44, 51)]))
                                (.branch 26
                                  (.leaf [(7, 36), (8, 35), (37, 44)])
                                  (.leaf [(7, 36), (8, 35), (49, 37), (44, 51)]))))))))))))
            (.branch 7
              (.branch 16
                (.branch 6
                  (.leaf [(21, 49), (4, 44), (48, 17), (40, 19)])
                  (.branch 17
                    (.leaf [(8, 35), (4, 49), (19, 50)])
                    (.branch 19
                      (.leaf [(8, 35), (4, 49)])
                      (.branch 4
                        (.leaf [(13, 40), (21, 51)])
                        (.leaf [(8, 35), (13, 40), (44, 51), (21, 49)])))))
                (.branch 19
                  (.leaf [(43, 17), (48, 35), (8, 39), (13, 6), (51, 21), (4, 41), (10, 37)])
                  (.branch 6
                    (.leaf [(8, 39), (10, 41), (26, 49), (4, 44), (21, 45), (40, 17), (43, 50)])
                    (.branch 17
                      (.leaf [(13, 39), (8, 35), (45, 21), (51, 26), (4, 41), (10, 37)])
                      (.branch 39
                        (.leaf [(26, 49), (21, 45), (37, 44), (41, 4), (35, 48)])
                        (.branch 4
                          (.leaf [(10, 37), (13, 40), (26, 51), (21, 45), (43, 50)])
                          (.branch 21
                            (.leaf [(8, 35), (13, 40), (41, 10), (37, 44), (43, 50)])
                            (.branch 37
                              (.leaf [(8, 35), (13, 40), (26, 51), (43, 50)])
                              (.leaf [(8, 35), (10, 41), (13, 40), (43, 50), (44, 51), (26, 49)])))))))))
              (.branch 13
                (.branch 0
                  (.branch 44
                    (.leaf [(16, 41), (21, 49), (48, 47)])
                    (.branch 49
                      (.leaf [(16, 41), (17, 46), (19, 50), (47, 48)])
                      (.leaf [(4, 41), (16, 37), (21, 51), (17, 46), (19, 50), (47, 48)])))
                  (.branch 16
                    (.branch 44
                      (.leaf [(8, 35), (10, 47), (21, 49)])
                      (.leaf [(8, 35), (4, 49), (10, 47), (21, 51), (48, 17), (46, 19)]))
                    (.branch 19
                      (.leaf [(8, 35), (43, 17), (48, 47), (51, 21), (4, 41), (10, 37)])
                      (.branch 4
                        (.leaf [(26, 51), (21, 45), (37, 10), (46, 17), (43, 50), (47, 48)])
                        (.branch 17
                          (.leaf [(8, 35), (41, 10), (37, 49), (26, 51), (21, 45)])
                          (.branch 10
                            (.leaf [(8, 35), (43, 50), (44, 51), (26, 49), (21, 45)])
                            (.branch 21
                              (.leaf [(8, 35), (37, 44), (43, 50), (47, 48)])
                              (.branch 26
                                (.leaf [(8, 35), (37, 44), (43, 50), (47, 48)])
                                (.leaf [(8, 35), (43, 50), (47, 48), (49, 37), (44, 51)])))))))))
                (.branch 16
                  (.branch 17
                    (.branch 35
                      (.leaf [(10, 47), (19, 50), (30, 51), (21, 49)])
                      (.branch 49
                        (.leaf [(0, 10), (19, 50), (30, 51), (6, 32)])
                        (.leaf [(0, 10), (4, 30), (8, 34), (19, 50), (21, 51), (6, 32)])))
                    (.branch 35
                      (.leaf [(10, 47), (32, 40), (38, 50), (19, 46), (30, 51), (21, 49), (34, 44)])
                      (.branch 19
                        (.branch 49
                          (.leaf [(0, 10), (30, 51), (6, 32), (36, 48)])
                          (.leaf [(0, 10), (4, 30), (8, 34), (21, 51), (6, 32), (36, 48)]))
                        (.branch 47
                          (.branch 51
                            (.leaf [(4, 49), (8, 34)])
                            (.leaf [(8, 34), (21, 49), (32, 6), (44, 4), (30, 46)]))
                          (.leaf [(0, 10), (8, 34), (36, 48), (38, 50), (40, 32), (6, 46), (21, 49), (4, 30), (44, 51)])))))
                  (.branch 17
                    (.branch 10
                      (.leaf [(32, 6), (50, 19), (45, 21), (8, 34), (35, 4), (30, 51), (26, 49)])
                      (.branch 49
                        (.leaf [(30, 51), (47, 50), (19, 45), (0, 35), (6, 32), (8, 39)])
                        (.branch 51
                          (.leaf [(47, 50), (19, 45), (0, 35), (4, 41), (8, 34)])
                          (.branch 35
                            (.leaf [(21, 45), (26, 19), (30, 37), (32, 39), (34, 41)])
                            (.branch 19
                              (.branch 4
                                (.leaf [(34, 8), (37, 6), (32, 39)])
                                (.leaf [(30, 37), (6, 32), (39, 8), (34, 41)]))
                              (.leaf [(21, 45), (0, 26), (47, 50), (4, 30), (37, 6), (32, 39), (8, 34)]))))))
                    (.branch 19
                      (.branch 10
                        (.leaf [(32, 6), (43, 36), (48, 35), (8, 34), (4, 30), (49, 21)])
                        (.branch 35
                          (.leaf [(32, 39), (36, 43), (41, 34), (21, 49), (37, 30)])
                          (.branch 49
                            (.leaf [(0, 43), (8, 39), (30, 51), (6, 32), (36, 48)])
                            (.branch 51
                              (.leaf [(0, 43), (4, 41), (8, 34), (36, 48)])
                              (.branch 4
                                (.leaf [(0, 43), (34, 8), (36, 48), (37, 6), (32, 39)])
                                (.leaf [(0, 43), (30, 37), (6, 32), (36, 48), (39, 8), (34, 41)]))))))
                      (.branch 51
                        (.branch 0
                          (.leaf [(8, 34), (32, 40), (36, 48), (37, 49), (4, 41), (38, 50)])
                          (.branch 47
                            (.leaf [(36, 43), (37, 49), (38, 45), (4, 35), (8, 34)])
                            (.leaf [(32, 40), (45, 38), (50, 43), (36, 48), (8, 35), (4, 41), (10, 37), (34, 49)])))
                        (.branch 0
                          (.branch 4
                            (.leaf [(34, 8), (36, 48), (37, 6), (38, 50), (46, 39), (32, 40)])
                            (.leaf [(21, 49), (36, 48), (38, 50), (41, 34), (8, 39), (44, 37), (30, 46), (6, 32), (40, 47)]))
                          (.branch 4
                            (.branch 39
                              (.leaf [(6, 37), (21, 45), (26, 38), (40, 47), (48, 36)])
                              (.leaf [(8, 34), (21, 45), (26, 38), (46, 6), (32, 40), (37, 10), (36, 43), (48, 47)]))
                            (.branch 37
                              (.leaf [(21, 45), (26, 38), (41, 34), (46, 39), (8, 35), (32, 40), (36, 43), (48, 47)])
                              (.branch 34
                                (.leaf [(21, 45), (26, 38), (30, 46), (6, 35), (10, 39), (32, 40), (36, 43), (48, 47)])
                                (.branch 39
                                  (.branch 38
                                    (.leaf [(6, 35), (21, 49), (40, 47), (43, 36)])
                                    (.leaf [(6, 35), (26, 49), (21, 45), (40, 47), (48, 36), (43, 50)]))
                                  (.branch 47
                                    (.leaf [(8, 35), (30, 46), (6, 32), (36, 43), (21, 45), (38, 26)])
                                    (.branch 6
                                      (.branch 38
                                        (.leaf [(10, 41), (21, 49), (43, 36)])
                                        (.leaf [(10, 41), (26, 49), (21, 45), (48, 36), (43, 50)]))
                                      (.leaf [(8, 35), (10, 41), (30, 46), (32, 40), (48, 36), (43, 50), (21, 45), (38, 26)])))))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSTSSS : treeOK treeRootSTSSS ([0, 3, 4, 5, 6, 7, 8, 10, 11, 13, 15, 16, 17, 19, 21, 26, 29, 30, 32, 34, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 11 = true := by rfl

private def treeRootSTSS : Tree := .branch 33 treeRootSTSST treeRootSTSSS
private theorem checkedRootSTSS : treeOK treeRootSTSS ([0, 3, 4, 5, 6, 7, 8, 10, 11, 13, 15, 16, 17, 19, 21, 26, 29, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 11 = true := by
  exact joinChecks 33 treeRootSTSST treeRootSTSSS ([0, 3, 4, 5, 6, 7, 8, 10, 11, 13, 15, 16, 17, 19, 21, 26, 29, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 11
    (by rfl) checkedRootSTSST checkedRootSTSSS

private def treeRootSTS : Tree := .branch 20 treeRootSTST treeRootSTSS
private theorem checkedRootSTS : treeOK treeRootSTS ([0, 3, 4, 5, 6, 7, 8, 10, 11, 13, 15, 16, 17, 19, 20, 21, 26, 29, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 11 = true := by
  exact joinChecks 20 treeRootSTST treeRootSTSS ([0, 3, 4, 5, 6, 7, 8, 10, 11, 13, 15, 16, 17, 19, 20, 21, 26, 29, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 11
    (by rfl) checkedRootSTST checkedRootSTSS

private def treeRootST : Tree := .branch 18 treeRootSTT treeRootSTS
private theorem checkedRootST : treeOK treeRootST ([0, 3, 4, 5, 6, 7, 8, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 26, 29, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 11 = true := by
  exact joinChecks 18 treeRootSTT treeRootSTS ([0, 3, 4, 5, 6, 7, 8, 10, 11, 13, 15, 16, 17, 18, 19, 20, 21, 26, 29, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 11
    (by rfl) checkedRootSTT checkedRootSTS

set_option maxRecDepth 32768 in
private def treeRootSSTTT : Tree :=
  (.branch 20
    (.leaf [(0, 23), (5, 36), (6, 18), (21, 42), (16, 39)])
    (.branch 39
      (.leaf [(5, 36), (21, 42), (22, 40), (37, 6)])
      (.leaf [(0, 23), (5, 36), (8, 18), (46, 6), (37, 16), (42, 21), (47, 40), (22, 51)])))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSSTTT : treeOK treeRootSSTTT ([0, 5, 6, 8, 16, 18, 20, 21, 22, 23, 36, 37, 39, 40, 42, 46, 47, 51]) 9 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootSSTTS : Tree :=
  (.branch 20
    (.branch 5
      (.leaf [(6, 18), (40, 22), (0, 7), (23, 39), (9, 16)])
      (.branch 7
        (.leaf [(6, 18), (17, 40), (26, 16), (9, 21), (12, 39)])
        (.leaf [(6, 18), (22, 40), (17, 42), (36, 9), (21, 12), (50, 23), (0, 26), (16, 39)])))
    (.branch 39
      (.branch 5
        (.leaf [(0, 7), (9, 21), (22, 40), (37, 6)])
        (.leaf [(26, 0), (37, 6), (50, 47), (18, 45), (9, 21), (36, 7), (22, 40), (17, 42)]))
      (.branch 5
        (.branch 6
          (.leaf [(23, 0), (9, 16), (21, 42), (7, 22)])
          (.branch 7
            (.leaf [(8, 18), (13, 40), (37, 16), (9, 21)])
            (.leaf [(0, 23), (8, 18), (37, 16), (9, 21), (42, 13), (47, 40), (22, 51)])))
        (.branch 6
          (.branch 7
            (.leaf [(12, 21), (9, 16), (17, 40), (23, 50)])
            (.branch 16
              (.leaf [(0, 23), (17, 40), (21, 12), (47, 50)])
              (.leaf [(26, 0), (23, 50), (36, 9), (12, 47), (17, 40), (22, 45), (21, 42)])))
          (.branch 7
            (.leaf [(8, 18), (13, 40), (17, 46), (23, 50), (9, 16), (26, 51), (37, 12), (21, 45)])
            (.branch 16
              (.leaf [(0, 23), (8, 18), (36, 13), (46, 17), (50, 47), (12, 21), (40, 22)])
              (.branch 21
                (.leaf [(8, 18), (22, 40), (13, 36), (17, 46), (26, 0), (23, 50)])
                (.branch 40
                  (.leaf [(8, 18), (9, 36), (12, 37), (45, 0), (23, 50), (26, 51)])
                  (.leaf [(8, 18), (9, 36), (13, 42), (17, 46), (37, 12), (47, 50), (23, 0), (26, 51), (22, 45)])))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSSTTS : treeOK treeRootSSTTS ([0, 5, 6, 7, 8, 9, 12, 13, 16, 17, 18, 20, 21, 22, 23, 26, 36, 37, 39, 40, 42, 45, 46, 47, 50, 51]) 10 = true := by rfl

private def treeRootSSTT : Tree := .branch 38 treeRootSSTTT treeRootSSTTS
private theorem checkedRootSSTT : treeOK treeRootSSTT ([0, 5, 6, 7, 8, 9, 12, 13, 16, 17, 18, 20, 21, 22, 23, 26, 36, 37, 38, 39, 40, 42, 45, 46, 47, 50, 51]) 10 = true := by
  exact joinChecks 38 treeRootSSTTT treeRootSSTTS ([0, 5, 6, 7, 8, 9, 12, 13, 16, 17, 18, 20, 21, 22, 23, 26, 36, 37, 38, 39, 40, 42, 45, 46, 47, 50, 51]) 10
    (by rfl) checkedRootSSTTT checkedRootSSTTS

set_option maxRecDepth 32768 in
private def treeRootSSTST : Tree :=
  (.branch 38
    (.branch 23
      (.leaf [(5, 36), (8, 20), (16, 42), (22, 40)])
      (.branch 16
        (.leaf [(0, 25), (5, 36), (8, 20), (21, 49), (22, 40)])
        (.leaf [(0, 25), (5, 36), (39, 8), (41, 20), (42, 21), (47, 40), (22, 49)])))
    (.branch 23
      (.branch 5
        (.leaf [(8, 20), (9, 16), (21, 42), (7, 22)])
        (.branch 7
          (.leaf [(8, 20), (12, 21), (9, 16), (17, 40)])
          (.leaf [(8, 20), (26, 16), (36, 9), (12, 47), (17, 40), (22, 45), (21, 42)])))
      (.branch 5
        (.branch 7
          (.leaf [(11, 40), (49, 21), (9, 16), (39, 8), (20, 41)])
          (.branch 16
            (.leaf [(0, 25), (8, 20), (11, 40), (21, 49)])
            (.leaf [(0, 25), (9, 21), (39, 8), (41, 20), (42, 11), (47, 40), (22, 49)])))
        (.branch 16
          (.leaf [(8, 20), (44, 17), (0, 25), (50, 47), (12, 21), (49, 22), (7, 36), (11, 40)])
          (.branch 7
            (.leaf [(9, 21), (11, 40), (17, 44), (25, 50), (26, 49), (45, 20), (8, 39), (12, 41)])
            (.branch 21
              (.leaf [(22, 40), (11, 36), (17, 44), (26, 0), (25, 50), (39, 8), (41, 20)])
              (.branch 20
                (.leaf [(9, 36), (12, 39), (44, 17), (42, 11), (40, 22), (49, 26), (0, 25)])
                (.branch 40
                  (.leaf [(8, 39), (9, 36), (12, 41), (45, 0), (25, 50), (26, 49)])
                  (.leaf [(8, 39), (9, 36), (11, 42), (17, 44), (41, 12), (47, 50), (25, 0), (26, 49), (22, 45)])))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSSTST : treeOK treeRootSSTST ([0, 5, 7, 8, 9, 11, 12, 16, 17, 20, 21, 22, 23, 25, 26, 36, 38, 39, 40, 41, 42, 44, 45, 47, 49, 50]) 10 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootSSTSS : Tree :=
  (.branch 38
    (.branch 20
      (.branch 23
        (.leaf [(5, 36), (16, 42), (18, 25), (21, 33)])
        (.branch 18
          (.leaf [(0, 35), (5, 36), (22, 40), (33, 21), (39, 16)])
          (.branch 21
            (.leaf [(5, 36), (16, 39), (22, 40), (25, 0)])
            (.leaf [(5, 36), (25, 0), (33, 40), (22, 49), (35, 42), (16, 39)]))))
      (.branch 18
        (.branch 39
          (.leaf [(0, 35), (5, 36), (22, 40), (33, 21)])
          (.branch 0
            (.leaf [(5, 36), (37, 16), (42, 21), (33, 40), (22, 51)])
            (.branch 21
              (.leaf [(5, 36), (16, 37), (22, 40), (23, 29)])
              (.leaf [(5, 36), (23, 29), (33, 40), (22, 51), (35, 42), (16, 37)]))))
        (.branch 23
          (.branch 21
            (.leaf [(5, 36), (8, 35), (16, 37), (22, 40), (25, 46)])
            (.leaf [(5, 36), (46, 25), (37, 16), (42, 35), (8, 33), (47, 40), (22, 51)]))
          (.branch 39
            (.branch 21
              (.leaf [(5, 36), (22, 40), (29, 47), (35, 0), (25, 37)])
              (.leaf [(5, 36), (29, 47), (33, 40), (22, 49), (42, 35), (0, 25), (37, 44)]))
            (.branch 21
              (.leaf [(5, 36), (22, 40), (27, 0), (35, 8), (29, 47), (41, 16), (44, 37), (25, 46)])
              (.branch 25
                (.branch 8
                  (.leaf [(5, 36), (41, 16), (47, 40), (22, 49)])
                  (.leaf [(5, 36), (29, 47), (33, 40), (22, 49), (35, 42), (16, 41)]))
                (.branch 8
                  (.branch 16
                    (.leaf [(0, 27), (5, 36), (44, 51), (47, 40)])
                    (.branch 22
                      (.leaf [(0, 27), (5, 36), (37, 44)])
                      (.leaf [(0, 27), (5, 36), (40, 47), (49, 37), (44, 51)])))
                  (.branch 16
                    (.leaf [(5, 36), (27, 0), (29, 47), (33, 40), (44, 51), (22, 49)])
                    (.branch 22
                      (.leaf [(5, 36), (27, 0), (29, 47), (35, 42), (37, 44)])
                      (.leaf [(5, 36), (27, 0), (29, 47), (33, 40), (35, 42), (49, 37), (44, 51)]))))))))))
    (.branch 20
      (.branch 23
        (.branch 5
          (.leaf [(18, 25), (16, 9), (35, 42), (21, 33)])
          (.leaf [(18, 25), (12, 35), (17, 40), (22, 7), (36, 9), (26, 33), (16, 31), (21, 42)]))
        (.branch 5
          (.branch 42
            (.leaf [(0, 25), (33, 40), (22, 49), (18, 44)])
            (.branch 18
              (.leaf [(39, 16), (0, 35), (9, 21), (7, 22)])
              (.branch 0
                (.leaf [(11, 40), (22, 49), (33, 21), (9, 16)])
                (.branch 9
                  (.leaf [(11, 40), (33, 7), (22, 49)])
                  (.branch 22
                    (.leaf [(16, 39), (21, 33)])
                    (.leaf [(7, 33), (11, 40), (16, 39), (21, 49)]))))))
          (.branch 21
            (.leaf [(35, 0), (39, 16), (26, 29), (50, 25), (7, 22), (36, 11), (18, 44), (17, 40)])
            (.branch 0
              (.branch 11
                (.leaf [(9, 16), (12, 39), (22, 49), (29, 17)])
                (.leaf [(12, 39), (33, 40), (22, 49), (18, 44), (9, 16), (36, 29), (17, 42)]))
              (.branch 16
                (.leaf [(12, 35), (50, 25), (29, 17), (44, 18), (49, 22), (7, 33), (36, 11)])
                (.branch 7
                  (.leaf [(9, 35), (12, 39), (50, 25), (11, 40), (17, 29), (26, 49), (18, 44)])
                  (.branch 11
                    (.leaf [(9, 35), (12, 39), (22, 49), (25, 50), (33, 26), (29, 17)])
                    (.branch 17
                      (.leaf [(22, 49), (18, 25), (26, 33), (36, 9), (35, 12)])
                      (.leaf [(39, 12), (42, 35), (9, 36), (29, 26), (33, 40), (22, 49), (44, 18), (25, 50)])))))))))
      (.branch 0
        (.branch 11
          (.branch 12
            (.leaf [(9, 16), (22, 49), (33, 8), (29, 17)])
            (.leaf [(13, 39), (22, 49), (41, 16), (9, 21), (33, 8), (44, 17), (5, 50), (29, 47)]))
          (.branch 12
            (.branch 17
              (.leaf [(13, 36), (9, 16), (33, 8), (18, 49)])
              (.branch 8
                (.leaf [(44, 51), (49, 22), (40, 13), (36, 9), (16, 42)])
                (.branch 13
                  (.branch 18
                    (.leaf [(9, 16), (22, 51)])
                    (.leaf [(9, 16), (44, 51), (22, 49)]))
                  (.branch 22
                    (.leaf [(18, 44), (29, 36), (9, 16)])
                    (.leaf [(29, 36), (9, 16), (33, 40), (49, 18), (44, 51)])))))
            (.branch 17
              (.leaf [(50, 47), (13, 36), (9, 16), (37, 49), (22, 51), (21, 33), (39, 8), (18, 41)])
              (.branch 16
                (.branch 18
                  (.leaf [(29, 36), (5, 50), (13, 40), (22, 51)])
                  (.leaf [(44, 51), (5, 50), (8, 29), (36, 13), (47, 40), (22, 49), (21, 33)]))
                (.branch 18
                  (.leaf [(29, 36), (5, 50), (9, 21), (33, 40), (22, 51), (42, 13), (39, 46)])
                  (.branch 21
                    (.leaf [(22, 40), (37, 44), (46, 39), (8, 29), (13, 36), (5, 50)])
                    (.branch 13
                      (.branch 8
                        (.branch 22
                          (.leaf [(5, 50), (37, 44)])
                          (.leaf [(5, 50), (49, 37), (44, 51)]))
                        (.branch 22
                          (.leaf [(5, 50), (29, 47), (37, 44)])
                          (.leaf [(5, 50), (29, 47), (49, 37), (44, 51)])))
                      (.branch 8
                        (.branch 22
                          (.leaf [(9, 36), (5, 50), (37, 44)])
                          (.leaf [(9, 36), (5, 50), (40, 47), (49, 37), (44, 51)]))
                        (.branch 22
                          (.leaf [(9, 36), (5, 50), (29, 47), (37, 44), (39, 46)])
                          (.leaf [(9, 36), (5, 50), (29, 47), (33, 40), (46, 39), (49, 37), (44, 51)]))))))))))
        (.branch 11
          (.branch 5
            (.branch 8
              (.leaf [(13, 25), (41, 16), (9, 21), (47, 7), (22, 49)])
              (.branch 7
                (.leaf [(25, 13), (27, 39), (35, 9), (16, 41), (21, 49)])
                (.leaf [(22, 49), (25, 13), (27, 39), (29, 47), (33, 21), (35, 9), (16, 41)])))
            (.branch 16
              (.leaf [(13, 25), (27, 50), (44, 17), (22, 49), (7, 33), (21, 12), (35, 8), (29, 47)])
              (.branch 21
                (.leaf [(22, 7), (26, 29), (17, 44), (35, 8), (47, 50), (25, 13), (27, 39)])
                (.branch 8
                  (.leaf [(13, 25), (17, 44), (26, 49), (27, 50), (41, 12), (45, 22), (7, 47)])
                  (.branch 47
                    (.leaf [(9, 35), (17, 44), (25, 13), (27, 39), (33, 26), (45, 22)])
                    (.branch 12
                      (.branch 22
                        (.leaf [(13, 25), (27, 50), (33, 26), (29, 17)])
                        (.leaf [(7, 33), (13, 25), (27, 50), (44, 17), (45, 29), (26, 49)]))
                      (.branch 22
                        (.branch 13
                          (.leaf [(9, 35), (27, 50), (33, 26), (29, 17)])
                          (.leaf [(9, 35), (25, 50), (27, 39), (33, 26), (29, 17)]))
                        (.branch 26
                          (.branch 13
                            (.leaf [(9, 35), (17, 44), (27, 50)])
                            (.leaf [(9, 35), (17, 44), (25, 50), (27, 39)]))
                          (.branch 13
                            (.leaf [(7, 33), (9, 35), (27, 50), (44, 17), (29, 45)])
                            (.leaf [(7, 33), (9, 35), (25, 50), (27, 39), (44, 17), (29, 45)]))))))))))
          (.branch 16
            (.branch 47
              (.branch 51
                (.leaf [(13, 36), (5, 17), (23, 49), (33, 8)])
                (.leaf [(22, 49), (21, 33), (8, 35), (23, 44), (5, 17), (36, 13), (25, 46)]))
              (.branch 17
                (.leaf [(27, 50), (23, 49), (12, 35), (8, 18), (13, 25), (36, 7), (22, 51), (21, 33)])
                (.branch 25
                  (.leaf [(44, 23), (5, 12), (35, 8), (29, 36), (7, 22), (40, 33), (21, 49)])
                  (.branch 8
                    (.leaf [(27, 50), (5, 12), (7, 36), (13, 40), (21, 49), (22, 51), (23, 44)])
                    (.branch 21
                      (.leaf [(18, 44), (27, 50), (5, 36), (7, 22), (13, 40), (23, 29)])
                      (.branch 22
                        (.leaf [(13, 36), (18, 44), (27, 50), (5, 12), (23, 29)])
                        (.leaf [(27, 50), (35, 12), (5, 36), (7, 33), (13, 40), (29, 23), (49, 18), (44, 51)])))))))
            (.branch 21
              (.branch 29
                (.leaf [(5, 50), (7, 22), (27, 39), (40, 13), (41, 18), (44, 37), (25, 46)])
                (.branch 18
                  (.branch 5
                    (.leaf [(7, 22), (23, 39), (13, 40)])
                    (.branch 39
                      (.leaf [(17, 40), (22, 7)])
                      (.branch 40
                        (.leaf [(7, 36), (23, 50)])
                        (.leaf [(13, 36), (7, 22), (17, 46), (23, 50)]))))
                  (.branch 39
                    (.leaf [(26, 5), (36, 7), (22, 40), (17, 44), (37, 25), (47, 50)])
                    (.branch 50
                      (.leaf [(8, 35), (37, 44), (46, 17), (7, 22), (36, 13)])
                      (.branch 17
                        (.leaf [(8, 35), (22, 7), (23, 41), (36, 13), (25, 37)])
                        (.leaf [(8, 35), (26, 5), (41, 23), (44, 37), (46, 25), (13, 36), (7, 22), (40, 47)]))))))
              (.branch 5
                (.branch 18
                  (.branch 39
                    (.leaf [(9, 35), (42, 7)])
                    (.branch 7
                      (.leaf [(9, 35), (13, 40), (23, 29)])
                      (.leaf [(9, 35), (23, 29), (33, 40), (13, 42), (22, 51)])))
                  (.branch 39
                    (.leaf [(9, 35), (25, 37), (29, 47), (42, 7), (33, 40), (22, 49)])
                    (.branch 7
                      (.leaf [(9, 35), (8, 29), (40, 13), (41, 23), (46, 25), (49, 37), (44, 51)])
                      (.branch 23
                        (.leaf [(9, 35), (8, 33), (37, 25), (42, 13), (47, 40), (22, 51)])
                        (.branch 25
                          (.branch 8
                            (.leaf [(47, 40), (22, 49)])
                            (.leaf [(9, 35), (29, 47), (33, 40), (22, 49)]))
                          (.branch 40
                            (.leaf [(9, 35), (8, 29), (49, 37), (44, 51)])
                            (.branch 8
                              (.branch 22
                                (.leaf [(13, 42), (37, 44)])
                                (.leaf [(13, 42), (49, 37), (44, 51)]))
                              (.branch 22
                                (.leaf [(9, 35), (13, 42), (29, 47), (37, 44)])
                                (.leaf [(9, 35), (13, 42), (29, 47), (49, 37), (44, 51)])))))))))
                (.branch 18
                  (.branch 39
                    (.branch 7
                      (.leaf [(9, 35), (26, 29)])
                      (.leaf [(22, 40), (33, 26), (9, 35), (36, 29), (17, 42)]))
                    (.branch 7
                      (.leaf [(9, 35), (12, 37), (13, 40), (27, 50), (23, 29), (17, 46), (26, 51)])
                      (.branch 17
                        (.leaf [(13, 36), (9, 35), (12, 37), (22, 51), (23, 50), (26, 33)])
                        (.branch 13
                          (.leaf [(9, 35), (12, 37), (22, 51), (27, 50), (23, 29), (26, 33)])
                          (.branch 26
                            (.leaf [(22, 40), (23, 50), (36, 9), (37, 12), (35, 42)])
                            (.leaf [(27, 50), (23, 29), (33, 40), (22, 51), (36, 9), (37, 12), (35, 42)]))))))
                  (.branch 29
                    (.branch 25
                      (.leaf [(9, 35), (27, 39), (12, 41), (42, 7), (33, 40), (22, 49)])
                      (.branch 39
                        (.leaf [(9, 35), (42, 7), (33, 40), (22, 49), (37, 44)])
                        (.branch 22
                          (.leaf [(9, 35), (13, 42), (27, 50), (41, 12), (37, 44)])
                          (.branch 12
                            (.branch 7
                              (.leaf [(13, 40), (27, 50), (44, 51)])
                              (.leaf [(27, 50), (33, 40), (13, 42), (44, 51)]))
                            (.branch 42
                              (.leaf [(27, 50), (33, 40), (49, 37), (44, 51)])
                              (.leaf [(7, 33), (9, 35), (13, 40), (27, 50), (49, 37), (44, 51)]))))))
                    (.branch 39
                      (.branch 7
                        (.leaf [(9, 35), (26, 49), (40, 17), (44, 37), (25, 50)])
                        (.branch 40
                          (.leaf [(26, 49), (36, 9), (35, 42), (44, 37), (25, 50)])
                          (.leaf [(31, 47), (33, 26), (36, 9), (35, 42), (17, 44), (45, 22), (49, 37), (25, 50)])))
                      (.branch 7
                        (.branch 25
                          (.leaf [(9, 35), (8, 31), (12, 41), (26, 49), (23, 44), (17, 40)])
                          (.branch 23
                            (.leaf [(9, 35), (8, 31), (12, 37), (13, 40), (17, 46), (26, 51)])
                            (.branch 12
                              (.leaf [(8, 31), (13, 40), (27, 50), (46, 17), (44, 51), (26, 49)])
                              (.branch 17
                                (.leaf [(9, 35), (8, 31), (27, 50), (37, 49), (26, 51)])
                                (.branch 8
                                  (.branch 26
                                    (.leaf [(13, 40), (27, 50), (37, 44)])
                                    (.leaf [(13, 40), (27, 50), (49, 37), (44, 51)]))
                                  (.branch 26
                                    (.leaf [(9, 35), (13, 40), (27, 50), (37, 44)])
                                    (.leaf [(9, 35), (13, 40), (27, 50), (49, 37), (44, 51)])))))))
                        (.branch 25
                          (.branch 35
                            (.leaf [(31, 47), (41, 23), (44, 17), (45, 22), (40, 33), (26, 49)])
                            (.branch 40
                              (.leaf [(8, 31), (9, 36), (12, 41), (26, 49), (23, 44)])
                              (.leaf [(9, 36), (42, 17), (44, 23), (41, 12), (45, 22), (47, 31), (8, 33), (26, 49)])))
                          (.branch 40
                            (.branch 23
                              (.leaf [(26, 51), (31, 8), (36, 9), (37, 12), (35, 42)])
                              (.branch 35
                                (.branch 26
                                  (.leaf [(27, 50), (37, 44)])
                                  (.leaf [(27, 50), (49, 37), (44, 51)]))
                                (.branch 37
                                  (.leaf [(8, 31), (9, 36), (26, 51), (27, 50)])
                                  (.leaf [(8, 31), (9, 36), (12, 41), (27, 50), (44, 51), (26, 49)]))))
                            (.branch 12
                              (.leaf [(9, 36), (13, 42), (27, 50), (31, 8), (33, 26), (45, 22), (46, 17), (49, 23), (44, 51)])
                              (.branch 23
                                (.branch 8
                                  (.leaf [(9, 36), (13, 42), (17, 46), (26, 51), (22, 45)])
                                  (.branch 42
                                    (.leaf [(9, 36), (31, 47), (33, 26), (45, 22)])
                                    (.leaf [(13, 36), (9, 35), (17, 46), (31, 47), (33, 26), (45, 22)])))
                                (.branch 8
                                  (.branch 17
                                    (.leaf [(9, 36), (27, 50), (37, 49), (26, 51), (22, 45)])
                                    (.branch 22
                                      (.leaf [(9, 36), (13, 42), (27, 50), (37, 44)])
                                      (.branch 13
                                        (.branch 26
                                          (.leaf [(27, 50), (37, 44)])
                                          (.leaf [(27, 50), (49, 37), (44, 51)]))
                                        (.branch 26
                                          (.leaf [(9, 36), (27, 50), (37, 44)])
                                          (.leaf [(9, 36), (27, 50), (49, 37), (44, 51)])))))
                                  (.branch 17
                                    (.leaf [(13, 36), (9, 35), (27, 50), (31, 47), (33, 26), (37, 49), (45, 22)])
                                    (.branch 22
                                      (.leaf [(26, 33), (27, 50), (31, 47), (37, 44), (9, 35), (36, 13)])
                                      (.branch 26
                                        (.leaf [(27, 50), (31, 47), (37, 44), (9, 35), (36, 13)])
                                        (.branch 9
                                          (.leaf [(13, 42), (27, 50), (31, 47), (49, 37), (44, 51)])
                                          (.leaf [(27, 50), (31, 47), (35, 42), (13, 36), (49, 37), (44, 51)])))))))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSSTSS : treeOK treeRootSSTSS ([0, 5, 7, 8, 9, 11, 12, 13, 16, 17, 18, 20, 21, 22, 23, 25, 26, 27, 29, 31, 33, 35, 36, 37, 38, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51]) 11 = true := by rfl

private def treeRootSSTS : Tree := .branch 6 treeRootSSTST treeRootSSTSS
private theorem checkedRootSSTS : treeOK treeRootSSTS ([0, 5, 6, 7, 8, 9, 11, 12, 13, 16, 17, 18, 20, 21, 22, 23, 25, 26, 27, 29, 31, 33, 35, 36, 37, 38, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51]) 11 = true := by
  exact joinChecks 6 treeRootSSTST treeRootSSTSS ([0, 5, 6, 7, 8, 9, 11, 12, 13, 16, 17, 18, 20, 21, 22, 23, 25, 26, 27, 29, 31, 33, 35, 36, 37, 38, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51]) 11
    (by rfl) checkedRootSSTST checkedRootSSTSS

private def treeRootSST : Tree := .branch 4 treeRootSSTT treeRootSSTS
private theorem checkedRootSST : treeOK treeRootSST ([0, 4, 5, 6, 7, 8, 9, 11, 12, 13, 16, 17, 18, 20, 21, 22, 23, 25, 26, 27, 29, 31, 33, 35, 36, 37, 38, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51]) 11 = true := by
  exact joinChecks 4 treeRootSSTT treeRootSSTS ([0, 4, 5, 6, 7, 8, 9, 11, 12, 13, 16, 17, 18, 20, 21, 22, 23, 25, 26, 27, 29, 31, 33, 35, 36, 37, 38, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51]) 11
    (by rfl) checkedRootSSTT checkedRootSSTS

set_option maxRecDepth 32768 in
private def treeRootSSSTT : Tree :=
  (.branch 45
    (.branch 7
      (.leaf [(6, 37), (15, 40), (48, 17)])
      (.leaf [(6, 37), (34, 9), (28, 50), (42, 15), (36, 43), (17, 40), (47, 48)]))
    (.branch 7
      (.branch 17
        (.leaf [(18, 6), (20, 37), (21, 9)])
        (.branch 19
          (.branch 6
            (.leaf [(20, 43)])
            (.leaf [(18, 43), (20, 37)]))
          (.leaf [(9, 21), (15, 40), (26, 5), (50, 43), (18, 6), (20, 37)])))
      (.branch 17
        (.branch 9
          (.leaf [(0, 26), (28, 50), (6, 18), (37, 20)])
          (.branch 47
            (.leaf [(0, 26), (6, 37), (15, 36), (21, 28)])
            (.leaf [(0, 26), (15, 36), (18, 6), (19, 50), (20, 37), (21, 28)])))
        (.branch 36
          (.branch 19
            (.branch 6
              (.leaf [(20, 47), (21, 28)])
              (.leaf [(18, 47), (20, 37), (21, 28)]))
            (.branch 47
              (.leaf [(0, 26), (6, 37), (28, 21)])
              (.leaf [(0, 26), (18, 6), (20, 37), (22, 40), (38, 50), (28, 21)])))
          (.branch 47
            (.leaf [(6, 37), (22, 43), (0, 26), (5, 34), (28, 21), (9, 19), (38, 15)])
            (.branch 19
              (.leaf [(0, 43), (5, 34), (15, 38), (18, 6), (20, 37), (21, 28), (22, 48)])
              (.branch 43
                (.leaf [(6, 37), (5, 26), (34, 9), (38, 15), (40, 28), (21, 42)])
                (.branch 38
                  (.leaf [(5, 34), (18, 6), (20, 37), (42, 21), (28, 40), (22, 48)])
                  (.branch 5
                    (.leaf [(9, 21), (18, 6), (20, 37), (28, 40), (15, 42), (22, 48)])
                    (.leaf [(0, 26), (18, 6), (20, 37), (34, 9), (48, 22), (50, 28), (21, 42), (15, 40)]))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSSSTT : treeOK treeRootSSSTT ([0, 5, 6, 7, 9, 15, 17, 18, 19, 20, 21, 22, 24, 26, 28, 34, 36, 37, 38, 40, 42, 43, 45, 47, 48, 50]) 10 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootSSSTS : Tree :=
  (.branch 45
    (.branch 36
      (.branch 6
        (.leaf [(8, 34), (12, 47), (10, 42), (17, 40), (23, 50)])
        (.leaf [(8, 34), (23, 50), (26, 51), (32, 40), (28, 46), (17, 42), (10, 37), (12, 47)]))
      (.branch 17
        (.branch 6
          (.leaf [(12, 47), (10, 9), (15, 8), (23, 50), (28, 7)])
          (.leaf [(13, 34), (8, 15), (23, 50), (26, 51), (28, 7), (32, 9), (10, 37), (12, 47)]))
        (.branch 47
          (.branch 6
            (.leaf [(9, 34), (8, 15), (14, 26)])
            (.branch 15
              (.leaf [(13, 34), (9, 32), (37, 14), (26, 51)])
              (.leaf [(8, 34), (9, 32), (13, 42), (28, 46), (37, 14), (26, 51)])))
          (.branch 6
            (.leaf [(12, 43), (26, 14), (48, 23), (50, 28), (40, 15), (8, 34), (7, 42), (9, 10)])
            (.branch 7
              (.branch 14
                (.leaf [(8, 15), (9, 10), (12, 43), (13, 40), (23, 48)])
                (.leaf [(8, 15), (9, 10), (13, 40), (26, 51), (37, 12), (43, 50), (23, 48)]))
              (.branch 15
                (.leaf [(13, 34), (28, 50), (23, 48), (32, 9), (10, 37), (12, 43), (14, 26)])
                (.branch 50
                  (.leaf [(8, 34), (12, 37), (26, 51), (9, 10), (32, 40), (13, 42)])
                  (.leaf [(8, 34), (23, 48), (43, 12), (46, 28), (51, 26), (14, 37), (9, 10), (32, 40), (13, 42)]))))))))
    (.branch 7
      (.branch 17
        (.branch 37
          (.leaf [(15, 8), (23, 50), (9, 19), (21, 51)])
          (.leaf [(10, 9), (15, 8), (16, 26), (18, 6), (13, 20), (23, 50), (19, 12), (21, 51)]))
        (.branch 19
          (.branch 20
            (.leaf [(5, 10), (6, 18), (14, 21), (23, 48)])
            (.leaf [(5, 10), (13, 6), (15, 8), (18, 43), (16, 37), (14, 21), (23, 48), (24, 51)]))
          (.branch 20
            (.branch 5
              (.leaf [(6, 18), (14, 21), (9, 16), (15, 40)])
              (.leaf [(6, 18), (10, 9), (12, 21), (15, 40), (16, 26), (14, 50), (23, 48)]))
            (.branch 6
              (.branch 5
                (.leaf [(8, 15), (14, 21), (9, 16), (23, 48)])
                (.branch 9
                  (.leaf [(8, 15), (12, 43), (26, 14), (48, 23)])
                  (.branch 14
                    (.leaf [(8, 15), (12, 43), (23, 48)])
                    (.leaf [(8, 15), (21, 12), (26, 16), (43, 50), (23, 48)]))))
              (.branch 5
                (.leaf [(13, 40), (23, 48), (24, 51), (46, 15), (8, 18), (43, 16), (9, 21), (14, 37)])
                (.branch 14
                  (.leaf [(10, 9), (12, 43), (13, 40), (18, 8), (15, 46), (23, 48), (24, 51)])
                  (.branch 16
                    (.leaf [(12, 21), (13, 40), (18, 8), (15, 46), (24, 51), (48, 23)])
                    (.branch 12
                      (.leaf [(9, 10), (13, 40), (18, 8), (15, 46), (24, 51), (48, 23)])
                      (.leaf [(13, 40), (24, 51), (21, 9), (10, 37), (46, 15), (8, 18), (43, 50), (23, 48)])))))))))
      (.branch 17
        (.branch 9
          (.branch 20
            (.leaf [(6, 18), (26, 0), (23, 50)])
            (.leaf [(13, 6), (15, 8), (18, 47), (12, 37), (22, 51), (26, 0), (23, 50)]))
          (.branch 20
            (.branch 0
              (.leaf [(6, 18), (15, 36), (16, 28), (21, 12), (19, 50)])
              (.leaf [(6, 18), (10, 22), (15, 36), (23, 50), (12, 19), (21, 28), (16, 26)]))
            (.branch 6
              (.leaf [(22, 10), (34, 8), (15, 36), (0, 23), (16, 26), (19, 12), (21, 28), (47, 50)])
              (.branch 10
                (.branch 8
                  (.leaf [(13, 36), (23, 50), (12, 19), (16, 26), (28, 21)])
                  (.branch 19
                    (.leaf [(15, 36), (13, 34), (16, 28), (21, 51)])
                    (.leaf [(12, 21), (15, 36), (13, 34), (23, 50), (28, 16), (26, 51)])))
                (.branch 12
                  (.leaf [(18, 8), (15, 36), (13, 34), (22, 51), (0, 23), (26, 16), (28, 50)])
                  (.branch 26
                    (.branch 8
                      (.leaf [(13, 36), (21, 28), (23, 50)])
                      (.leaf [(15, 36), (13, 34), (18, 47), (21, 28), (23, 50)]))
                    (.branch 50
                      (.leaf [(16, 37), (18, 8), (15, 36), (13, 34), (21, 51)])
                      (.branch 8
                        (.leaf [(0, 23), (13, 36), (22, 51), (21, 28), (16, 37)])
                        (.leaf [(0, 23), (15, 36), (13, 34), (18, 47), (22, 51), (21, 28), (16, 37)])))))))))
        (.branch 9
          (.branch 20
            (.branch 50
              (.leaf [(0, 26), (6, 18), (42, 15), (40, 22)])
              (.leaf [(6, 18), (12, 5), (14, 26), (0, 23), (28, 40), (15, 42), (22, 48)]))
            (.branch 47
              (.leaf [(5, 26), (8, 15), (14, 37), (23, 0), (28, 46), (42, 13), (6, 51), (22, 43)])
              (.branch 6
                (.branch 50
                  (.leaf [(0, 26), (8, 15), (40, 22)])
                  (.branch 0
                    (.leaf [(5, 12), (8, 15), (28, 40), (22, 48)])
                    (.leaf [(8, 15), (14, 26), (5, 12), (23, 48), (28, 40), (22, 43)])))
                (.branch 43
                  (.leaf [(5, 26), (8, 15), (14, 37), (23, 48), (24, 51), (42, 13), (40, 28)])
                  (.branch 15
                    (.branch 26
                      (.leaf [(12, 37), (22, 48), (23, 50)])
                      (.leaf [(0, 23), (24, 51), (22, 48), (28, 50), (5, 12), (14, 37)]))
                    (.branch 26
                      (.leaf [(8, 18), (12, 37), (42, 13), (46, 28), (40, 22), (48, 23)])
                      (.branch 50
                        (.leaf [(8, 18), (12, 37), (24, 51), (42, 13), (40, 22)])
                        (.leaf [(0, 23), (5, 12), (8, 18), (14, 37), (24, 51), (42, 13), (46, 28), (40, 22)]))))))))
          (.branch 20
            (.branch 5
              (.branch 40
                (.leaf [(0, 23), (6, 18), (14, 21), (16, 42)])
                (.leaf [(0, 23), (6, 18), (14, 21), (19, 42), (15, 38), (16, 28), (22, 48)]))
              (.branch 19
                (.branch 36
                  (.leaf [(6, 18), (16, 28), (22, 10), (0, 23)])
                  (.branch 0
                    (.leaf [(6, 18), (14, 21), (15, 38), (16, 28), (22, 48)])
                    (.leaf [(6, 18), (10, 22), (14, 21), (15, 38), (16, 28), (23, 48)])))
                (.branch 14
                  (.branch 10
                    (.leaf [(6, 18), (12, 38), (15, 40), (16, 28), (23, 48)])
                    (.branch 15
                      (.leaf [(0, 23), (6, 18), (16, 28), (22, 48)])
                      (.leaf [(0, 23), (6, 18), (12, 38), (42, 16), (28, 40), (22, 48)])))
                  (.branch 15
                    (.branch 0
                      (.leaf [(6, 18), (12, 21), (16, 28), (22, 48)])
                      (.leaf [(6, 18), (10, 22), (12, 21), (26, 16), (28, 50), (23, 48)]))
                    (.branch 28
                      (.leaf [(6, 18), (12, 38), (24, 36), (26, 0), (23, 48), (22, 10)])
                      (.branch 0
                        (.leaf [(6, 18), (16, 42), (21, 12), (24, 36), (38, 50), (40, 22)])
                        (.leaf [(6, 18), (24, 36), (40, 22), (10, 42), (16, 26), (21, 12), (38, 50), (23, 48)])))))))
            (.branch 50
              (.branch 6
                (.leaf [(12, 21), (24, 36), (34, 8), (48, 22), (40, 15), (0, 10), (26, 16)])
                (.branch 15
                  (.branch 51
                    (.leaf [(0, 10), (12, 37), (13, 34)])
                    (.branch 10
                      (.leaf [(12, 21), (13, 34), (16, 26)])
                      (.leaf [(0, 26), (13, 34), (16, 37), (12, 21), (22, 48)])))
                  (.branch 10
                    (.leaf [(12, 21), (16, 26), (18, 8), (32, 40), (34, 13), (48, 36), (24, 51)])
                    (.branch 13
                      (.leaf [(0, 26), (8, 18), (16, 37), (12, 21), (24, 51), (22, 48)])
                      (.branch 51
                        (.leaf [(12, 37), (16, 42), (18, 8), (32, 40), (36, 48)])
                        (.branch 16
                          (.leaf [(12, 21), (18, 8), (24, 36), (32, 40), (22, 48)])
                          (.leaf [(0, 26), (18, 8), (24, 36), (32, 40), (22, 48), (37, 12), (21, 42)])))))))
              (.branch 12
                (.branch 6
                  (.leaf [(24, 36), (14, 26), (34, 8), (0, 23), (48, 22), (10, 42), (15, 40), (16, 28)])
                  (.branch 15
                    (.branch 26
                      (.leaf [(10, 22), (13, 34), (23, 48)])
                      (.branch 22
                        (.leaf [(0, 23), (13, 34), (16, 28)])
                        (.leaf [(10, 0), (13, 34), (16, 28), (23, 48), (24, 51)])))
                    (.branch 13
                      (.branch 26
                        (.leaf [(8, 18), (10, 22), (23, 48)])
                        (.branch 22
                          (.leaf [(0, 23), (8, 18), (16, 28)])
                          (.leaf [(8, 18), (10, 0), (16, 28), (23, 48), (24, 51)])))
                      (.branch 22
                        (.leaf [(18, 8), (23, 0), (24, 36), (14, 26), (42, 16), (28, 46)])
                        (.branch 26
                          (.leaf [(10, 42), (18, 8), (23, 48), (24, 36), (32, 40)])
                          (.leaf [(14, 36), (18, 8), (24, 51), (32, 40), (46, 28), (16, 42), (10, 0), (23, 48)]))))))
                (.branch 26
                  (.branch 40
                    (.leaf [(21, 42), (10, 37), (23, 48), (24, 36), (34, 8), (43, 18)])
                    (.branch 6
                      (.leaf [(23, 48), (28, 21), (34, 8), (15, 42), (10, 22), (43, 36)])
                      (.branch 36
                        (.leaf [(22, 10), (34, 8), (18, 47), (42, 21), (28, 46)])
                        (.branch 10
                          (.leaf [(13, 34), (21, 28), (23, 48), (43, 18), (8, 15)])
                          (.branch 8
                            (.leaf [(13, 42), (21, 28), (23, 48), (22, 43), (24, 47)])
                            (.branch 42
                              (.leaf [(23, 48), (22, 43), (18, 47), (28, 46)])
                              (.leaf [(13, 34), (15, 46), (21, 28), (23, 48), (22, 43), (18, 47)])))))))
                  (.branch 36
                    (.branch 6
                      (.leaf [(8, 34), (23, 0), (16, 28), (21, 42), (19, 40), (22, 10)])
                      (.branch 10
                        (.leaf [(16, 28), (18, 8), (21, 51), (32, 40), (19, 46)])
                        (.branch 40
                          (.leaf [(0, 23), (18, 8), (37, 16), (42, 21)])
                          (.branch 16
                            (.leaf [(0, 23), (19, 46), (21, 51), (34, 8), (18, 47)])
                            (.branch 21
                              (.leaf [(0, 23), (19, 46), (34, 8), (18, 47)])
                              (.leaf [(0, 23), (22, 51), (28, 46), (19, 42), (34, 8), (18, 47)]))))))
                    (.branch 40
                      (.branch 6
                        (.leaf [(8, 34), (5, 10), (14, 21), (42, 16), (43, 0), (23, 48)])
                        (.branch 10
                          (.leaf [(14, 21), (16, 43), (18, 8), (23, 48), (24, 51)])
                          (.branch 16
                            (.leaf [(0, 23), (5, 34), (8, 18), (14, 21), (24, 51)])
                            (.leaf [(5, 34), (8, 18), (24, 51), (37, 14), (21, 42), (43, 0), (23, 48)]))))
                      (.branch 6
                        (.branch 10
                          (.leaf [(14, 21), (23, 48), (28, 16), (34, 8), (15, 38)])
                          (.branch 42
                            (.branch 48
                              (.leaf [(0, 43), (5, 34)])
                              (.leaf [(5, 34), (22, 43), (0, 23), (24, 47)]))
                            (.branch 43
                              (.leaf [(5, 34), (8, 15), (14, 21), (23, 48), (24, 47)])
                              (.leaf [(0, 23), (5, 34), (8, 15), (14, 21), (16, 28), (22, 48), (24, 47)]))))
                        (.branch 10
                          (.branch 8
                            (.leaf [(13, 38), (14, 21), (19, 46), (23, 48), (24, 51), (28, 16)])
                            (.leaf [(14, 21), (18, 43), (16, 28), (19, 46), (15, 38), (13, 34), (23, 48), (24, 51)]))
                          (.branch 42
                            (.branch 18
                              (.leaf [(0, 23), (14, 37), (24, 51), (22, 48), (28, 46), (32, 5)])
                              (.leaf [(8, 34), (5, 32), (14, 37), (28, 46), (0, 23), (43, 22), (48, 47), (24, 51)]))
                            (.branch 43
                              (.branch 15
                                (.leaf [(13, 34), (5, 32), (23, 48), (28, 21), (14, 37), (47, 24)])
                                (.leaf [(8, 34), (5, 32), (13, 38), (19, 46), (23, 48), (28, 21), (14, 37), (47, 24)]))
                              (.branch 8
                                (.leaf [(0, 23), (5, 32), (13, 38), (19, 46), (14, 37), (16, 28), (21, 51), (22, 48), (24, 47)])
                                (.branch 21
                                  (.leaf [(0, 23), (16, 37), (18, 47), (19, 46), (15, 38), (13, 34), (5, 32), (22, 48)])
                                  (.leaf [(0, 23), (14, 37), (16, 28), (18, 47), (19, 46), (15, 38), (13, 34), (5, 32), (24, 51), (22, 48)])))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSSSTS : treeOK treeRootSSSTS ([0, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 28, 32, 34, 36, 37, 38, 40, 42, 43, 45, 46, 47, 48, 50, 51]) 11 = true := by rfl

private def treeRootSSST : Tree := .branch 39 treeRootSSSTT treeRootSSSTS
private theorem checkedRootSSST : treeOK treeRootSSST ([0, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 28, 32, 34, 36, 37, 38, 39, 40, 42, 43, 45, 46, 47, 48, 50, 51]) 11 = true := by
  exact joinChecks 39 treeRootSSSTT treeRootSSSTS ([0, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 28, 32, 34, 36, 37, 38, 39, 40, 42, 43, 45, 46, 47, 48, 50, 51]) 11
    (by rfl) checkedRootSSSTT checkedRootSSSTS

set_option maxRecDepth 32768 in
private def treeRootSSSST : Tree :=
  (.branch 6
    (.branch 15
      (.branch 0
        (.branch 9
          (.leaf [(14, 39), (20, 47), (22, 48)])
          (.branch 47
            (.leaf [(14, 21), (28, 16)])
            (.branch 14
              (.leaf [(16, 28), (22, 48)])
              (.leaf [(21, 28), (16, 39), (22, 48)]))))
        (.branch 16
          (.leaf [(11, 23), (14, 21), (20, 47), (7, 22), (25, 48)])
          (.leaf [(11, 23), (19, 9), (24, 47), (20, 43), (25, 48), (22, 7), (28, 21), (14, 39)])))
      (.branch 23
        (.branch 7
          (.leaf [(8, 20), (14, 21), (40, 19), (9, 16)])
          (.branch 9
            (.leaf [(8, 20), (24, 47), (28, 40), (22, 43)])
            (.branch 40
              (.leaf [(8, 20), (14, 21), (42, 16)])
              (.leaf [(8, 20), (14, 21), (19, 42), (22, 43), (16, 28), (24, 47)]))))
        (.branch 7
          (.branch 16
            (.leaf [(8, 20), (11, 40), (14, 21), (19, 44), (24, 49)])
            (.leaf [(11, 40), (24, 49), (25, 48), (43, 20), (8, 39), (41, 14), (21, 9), (19, 44)]))
          (.branch 16
            (.leaf [(0, 25), (8, 20), (14, 21), (38, 11), (44, 19), (24, 49), (22, 40), (47, 48)])
            (.branch 21
              (.leaf [(24, 47), (38, 11), (39, 8), (41, 20), (44, 19), (40, 22), (43, 0), (25, 48)])
              (.branch 40
                (.branch 20
                  (.leaf [(0, 25), (9, 38), (14, 39), (24, 49)])
                  (.leaf [(8, 39), (9, 38), (14, 41), (24, 49), (43, 0), (25, 48)]))
                (.branch 20
                  (.leaf [(0, 25), (14, 39), (24, 49), (22, 48), (28, 44), (9, 19), (38, 11)])
                  (.branch 19
                    (.leaf [(8, 39), (11, 38), (14, 41), (0, 25), (43, 22), (48, 47), (24, 49)])
                    (.leaf [(8, 39), (9, 38), (11, 42), (14, 41), (28, 44), (0, 25), (43, 22), (48, 47), (24, 49)])))))))))
    (.branch 15
      (.branch 51
        (.branch 35
          (.leaf [(23, 29), (37, 16), (7, 33), (43, 18)])
          (.branch 7
            (.leaf [(14, 37), (18, 43), (16, 9), (29, 23)])
            (.leaf [(14, 37), (19, 9), (0, 23), (16, 28), (29, 47), (18, 43), (33, 48)])))
        (.branch 35
          (.branch 43
            (.leaf [(7, 47), (29, 23), (11, 37), (25, 13)])
            (.branch 37
              (.leaf [(13, 39), (18, 47), (21, 33), (7, 22)])
              (.leaf [(16, 39), (21, 33), (22, 7), (11, 23), (29, 47), (18, 25), (13, 20)])))
          (.branch 43
            (.leaf [(19, 9), (24, 47), (7, 28), (21, 14), (29, 23), (11, 37), (39, 13), (25, 48)])
            (.branch 47
              (.leaf [(19, 9), (33, 21), (28, 16), (0, 23), (11, 37), (14, 39), (13, 25)])
              (.branch 23
                (.leaf [(18, 25), (13, 20), (19, 9), (22, 7), (24, 33), (14, 21), (28, 16)])
                (.branch 25
                  (.leaf [(19, 9), (22, 7), (24, 33), (29, 28), (16, 39), (14, 21)])
                  (.branch 7
                    (.branch 37
                      (.leaf [(13, 39), (19, 9)])
                      (.leaf [(11, 18), (19, 9), (16, 39), (13, 20), (14, 21)]))
                    (.branch 16
                      (.leaf [(11, 18), (13, 20), (14, 21), (22, 48), (24, 33)])
                      (.leaf [(18, 11), (19, 9), (22, 48), (24, 33), (29, 28), (21, 14), (37, 20), (13, 39)])))))))))
      (.branch 20
        (.branch 23
          (.leaf [(18, 25), (14, 21), (22, 40), (19, 9), (38, 7), (33, 24), (16, 28), (35, 42)])
          (.branch 28
            (.leaf [(0, 25), (14, 39), (9, 19), (38, 11), (18, 49), (22, 48), (24, 33)])
            (.branch 35
              (.leaf [(16, 39), (25, 18), (44, 19), (11, 38), (7, 22), (40, 33), (21, 49)])
              (.branch 7
                (.branch 18
                  (.leaf [(40, 19), (9, 16), (21, 14)])
                  (.leaf [(11, 40), (24, 49), (25, 48), (44, 19), (9, 16), (21, 14)]))
                (.branch 21
                  (.leaf [(0, 25), (16, 39), (38, 11), (18, 44), (19, 40), (22, 48)])
                  (.branch 11
                    (.leaf [(0, 25), (14, 39), (16, 9), (19, 44), (22, 48), (33, 24)])
                    (.branch 19
                      (.leaf [(0, 25), (14, 39), (18, 49), (22, 48), (24, 33)])
                      (.leaf [(0, 25), (14, 39), (38, 9), (16, 42), (44, 18), (24, 49), (22, 40), (33, 48)]))))))))
        (.branch 11
          (.branch 35
            (.leaf [(19, 44), (25, 13), (27, 39), (29, 47), (41, 16), (7, 22), (43, 33), (21, 49)])
            (.branch 33
              (.branch 16
                (.leaf [(13, 25), (0, 27), (19, 44), (22, 49)])
                (.leaf [(9, 19), (22, 49), (41, 14), (44, 28), (29, 47), (0, 25), (13, 39)]))
              (.branch 16
                (.leaf [(8, 29), (13, 25), (14, 21), (19, 44), (0, 27), (7, 22), (48, 47), (24, 49)])
                (.branch 0
                  (.leaf [(13, 39), (8, 29), (41, 14), (9, 19), (44, 28), (21, 49), (22, 48), (24, 47)])
                  (.branch 21
                    (.branch 47
                      (.leaf [(8, 39), (13, 25), (19, 44)])
                      (.branch 22
                        (.leaf [(19, 44), (25, 13), (27, 39)])
                        (.branch 39
                          (.leaf [(19, 44), (25, 48)])
                          (.leaf [(8, 29), (13, 25), (19, 44), (27, 48)]))))
                    (.branch 22
                      (.leaf [(9, 19), (24, 47), (25, 13), (27, 39), (8, 29), (14, 41)])
                      (.branch 39
                        (.leaf [(9, 19), (25, 48), (44, 28), (7, 47), (24, 49)])
                        (.leaf [(8, 29), (9, 19), (13, 25), (14, 41), (27, 48), (44, 28), (7, 47), (24, 49)]))))))))
          (.branch 28
            (.branch 18
              (.branch 39
                (.leaf [(22, 48), (24, 33), (38, 9)])
                (.leaf [(14, 37), (0, 23), (27, 48), (22, 51), (24, 33), (9, 19), (38, 13)]))
              (.branch 39
                (.leaf [(38, 9), (19, 42), (0, 25), (37, 49), (22, 43), (24, 33), (47, 48)])
                (.branch 48
                  (.leaf [(0, 43), (41, 14), (37, 49), (24, 51), (9, 19), (38, 13)])
                  (.branch 0
                    (.leaf [(8, 33), (41, 14), (37, 49), (22, 51), (24, 47), (9, 19), (38, 13)])
                    (.branch 24
                      (.leaf [(22, 43), (23, 41), (14, 37), (25, 13), (38, 9), (19, 42)])
                      (.branch 13
                        (.branch 22
                          (.leaf [(8, 33), (9, 19), (23, 41)])
                          (.branch 14
                            (.leaf [(8, 33), (9, 19), (23, 49)])
                            (.leaf [(8, 33), (9, 19), (37, 49), (23, 41)])))
                        (.branch 22
                          (.leaf [(8, 33), (23, 41), (14, 37), (38, 9), (19, 42)])
                          (.branch 37
                            (.leaf [(8, 33), (23, 41), (38, 9), (19, 42)])
                            (.leaf [(8, 33), (14, 41), (23, 49), (25, 51), (38, 9), (19, 42)])))))))))
            (.branch 39
              (.branch 7
                (.branch 18
                  (.leaf [(21, 9), (19, 40)])
                  (.branch 9
                    (.leaf [(24, 49), (44, 37), (25, 48)])
                    (.leaf [(21, 49), (24, 35), (40, 19), (44, 37), (25, 48)])))
                (.branch 18
                  (.leaf [(0, 35), (24, 33), (38, 9), (21, 42), (19, 40), (22, 48)])
                  (.branch 33
                    (.leaf [(22, 49), (29, 47), (38, 9), (0, 25), (35, 42), (19, 44)])
                    (.branch 35
                      (.leaf [(21, 49), (25, 37), (29, 47), (43, 22), (40, 19)])
                      (.branch 19
                        (.leaf [(21, 49), (24, 47), (37, 25), (0, 43), (22, 48)])
                        (.leaf [(29, 47), (24, 49), (38, 9), (21, 42), (40, 22), (43, 0), (44, 37), (25, 48)]))))))
              (.branch 18
                (.branch 35
                  (.leaf [(16, 37), (23, 29), (46, 19), (13, 38), (7, 22), (40, 33), (21, 51)])
                  (.branch 7
                    (.leaf [(13, 40), (24, 51), (27, 48), (23, 29), (46, 19), (9, 16), (21, 14)])
                    (.branch 21
                      (.leaf [(16, 37), (29, 23), (0, 27), (38, 13), (46, 19), (40, 22)])
                      (.branch 19
                        (.leaf [(13, 38), (14, 37), (29, 23), (0, 27), (22, 48), (33, 24)])
                        (.branch 48
                          (.leaf [(14, 37), (24, 51), (40, 13), (38, 9), (16, 42)])
                          (.branch 13
                            (.leaf [(9, 16), (14, 37), (22, 51), (24, 33), (27, 0)])
                            (.leaf [(14, 37), (27, 0), (23, 29), (38, 9), (16, 42), (22, 40), (33, 24)])))))))
                (.branch 33
                  (.branch 23
                    (.branch 9
                      (.leaf [(14, 37), (22, 51), (42, 13)])
                      (.leaf [(22, 51), (38, 13), (14, 35), (16, 37), (25, 46), (19, 42)]))
                    (.branch 25
                      (.leaf [(22, 49), (29, 47), (38, 9), (44, 19), (14, 35), (41, 16)])
                      (.branch 9
                        (.leaf [(0, 27), (13, 42), (29, 47), (41, 14), (22, 49), (37, 44)])
                        (.leaf [(27, 0), (29, 47), (38, 13), (46, 19), (22, 49), (51, 44), (35, 42), (14, 37), (16, 41)]))))
                  (.branch 35
                    (.branch 22
                      (.leaf [(38, 13), (47, 29), (16, 41), (23, 44), (19, 46), (25, 37)])
                      (.branch 23
                        (.leaf [(21, 51), (43, 16), (37, 25), (46, 19), (7, 38), (13, 40)])
                        (.branch 25
                          (.leaf [(21, 49), (29, 47), (7, 38), (40, 19), (41, 16)])
                          (.branch 16
                            (.leaf [(29, 47), (7, 38), (13, 40), (46, 19), (44, 51)])
                            (.branch 19
                              (.leaf [(13, 38), (7, 47), (37, 49), (21, 51)])
                              (.branch 47
                                (.leaf [(13, 38), (21, 49), (37, 44)])
                                (.branch 13
                                  (.branch 21
                                    (.leaf [(37, 44)])
                                    (.leaf [(49, 37), (44, 51)]))
                                  (.branch 21
                                    (.leaf [(7, 38), (37, 44)])
                                    (.leaf [(7, 38), (49, 37), (44, 51)])))))))))
                    (.branch 22
                      (.branch 9
                        (.leaf [(8, 29), (24, 47), (27, 0), (42, 13), (46, 25), (14, 37), (41, 23)])
                        (.branch 23
                          (.leaf [(24, 47), (38, 13), (14, 21), (16, 37), (25, 46), (19, 42)])
                          (.leaf [(8, 29), (24, 47), (27, 0), (38, 13), (21, 14), (41, 16), (42, 19), (44, 37), (25, 46)])))
                      (.branch 23
                        (.branch 42
                          (.leaf [(9, 38), (14, 37), (40, 47), (24, 51), (25, 46)])
                          (.branch 9
                            (.leaf [(7, 47), (14, 37), (24, 51), (40, 13), (25, 46)])
                            (.branch 25
                              (.leaf [(14, 21), (16, 43), (19, 40), (24, 47)])
                              (.leaf [(43, 16), (37, 14), (21, 51), (24, 47), (7, 38), (13, 40), (19, 46)]))))
                        (.branch 25
                          (.branch 9
                            (.leaf [(8, 29), (14, 41), (40, 47), (7, 42), (24, 49)])
                            (.leaf [(8, 29), (38, 7), (43, 16), (41, 14), (44, 19), (40, 47), (24, 49), (21, 42)]))
                          (.branch 16
                            (.leaf [(8, 29), (14, 21), (46, 19), (44, 51), (49, 24), (0, 27), (48, 47), (7, 38), (13, 40)])
                            (.branch 19
                              (.leaf [(8, 29), (13, 38), (41, 14), (37, 49), (21, 51), (24, 47), (7, 0), (27, 48)])
                              (.branch 21
                                (.leaf [(8, 29), (24, 47), (37, 44), (40, 13), (38, 7), (43, 0), (27, 48)])
                                (.branch 47
                                  (.leaf [(9, 38), (13, 42), (27, 0), (41, 14), (49, 37), (44, 51)])
                                  (.branch 0
                                    (.branch 13
                                      (.leaf [(8, 29), (41, 14), (24, 49), (37, 44)])
                                      (.branch 37
                                        (.leaf [(8, 29), (9, 38), (24, 51)])
                                        (.leaf [(8, 29), (9, 38), (14, 41), (44, 51), (24, 49)])))
                                    (.branch 13
                                      (.branch 37
                                        (.leaf [(8, 29), (24, 51), (27, 48)])
                                        (.leaf [(8, 29), (14, 41), (27, 48), (44, 51), (24, 49)]))
                                      (.branch 37
                                        (.leaf [(8, 29), (9, 38), (7, 42), (24, 51), (27, 48)])
                                        (.leaf [(8, 29), (9, 38), (7, 42), (14, 41), (27, 48), (44, 51), (24, 49)]))))))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSSSST : treeOK treeRootSSSST ([0, 6, 7, 8, 9, 11, 13, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 29, 33, 35, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 49, 51]) 11 = true := by rfl

set_option maxRecDepth 32768 in
private def treeRootSSSSS : Tree :=
  (.branch 6
    (.branch 7
      (.branch 19
        (.branch 41
          (.leaf [(8, 39), (21, 49), (24, 17)])
          (.leaf [(10, 39), (11, 23), (16, 43), (20, 8), (15, 49), (21, 14), (24, 17), (25, 48)]))
        (.branch 23
          (.branch 16
            (.leaf [(12, 21), (14, 17), (20, 8), (15, 40)])
            (.leaf [(10, 9), (26, 14), (8, 15), (40, 17), (24, 45), (20, 43), (12, 21)]))
          (.branch 14
            (.leaf [(10, 9), (11, 40), (12, 43), (16, 45), (20, 8), (24, 49), (15, 44), (25, 48)])
            (.branch 16
              (.leaf [(11, 40), (12, 21), (20, 8), (50, 25), (48, 17), (24, 49), (15, 44)])
              (.branch 15
                (.branch 43
                  (.leaf [(24, 45), (21, 9), (10, 39)])
                  (.branch 21
                    (.leaf [(10, 39), (24, 17), (48, 25)])
                    (.leaf [(9, 10), (12, 39), (20, 45), (24, 17), (48, 25)])))
                (.branch 17
                  (.leaf [(25, 50), (26, 49), (8, 20), (45, 21), (9, 10), (39, 12)])
                  (.branch 12
                    (.leaf [(8, 20), (9, 10), (11, 40), (26, 49), (24, 45), (48, 25)])
                    (.branch 20
                      (.leaf [(11, 40), (24, 49), (21, 9), (10, 39), (48, 25)])
                      (.leaf [(8, 39), (11, 40), (26, 49), (24, 45), (21, 9), (10, 41), (43, 50), (25, 48)])))))))))
      (.branch 23
        (.branch 9
          (.branch 17
            (.leaf [(12, 47), (15, 8), (20, 45)])
            (.leaf [(14, 26), (28, 40), (42, 15), (8, 20), (12, 43), (22, 45), (24, 47)]))
          (.branch 45
            (.leaf [(26, 14), (28, 40), (34, 8), (10, 47), (12, 43), (17, 42), (15, 36)])
            (.branch 17
              (.leaf [(22, 10), (34, 8), (15, 36), (20, 47), (12, 19), (21, 28), (16, 26)])
              (.branch 12
                (.branch 15
                  (.leaf [(10, 22), (14, 26), (16, 28)])
                  (.leaf [(20, 8), (24, 36), (14, 26), (10, 22), (40, 28), (16, 42)]))
                (.branch 15
                  (.leaf [(19, 26), (14, 21), (24, 47), (10, 22), (20, 43), (16, 28)])
                  (.branch 16
                    (.leaf [(19, 40), (21, 14), (22, 10), (34, 8), (20, 47), (24, 36)])
                    (.branch 40
                      (.leaf [(10, 42), (21, 14), (24, 36), (26, 38), (34, 8)])
                      (.leaf [(28, 21), (34, 8), (38, 26), (14, 36), (19, 42), (24, 47), (10, 22), (20, 43)]))))))))
        (.branch 9
          (.branch 17
            (.branch 20
              (.leaf [(12, 39), (15, 49), (26, 0), (25, 50)])
              (.leaf [(28, 50), (25, 0), (26, 49), (22, 45), (47, 12), (39, 8), (15, 41)]))
            (.branch 15
              (.branch 43
                (.leaf [(25, 48), (26, 14), (45, 24)])
                (.leaf [(28, 50), (12, 39), (14, 26), (0, 25), (20, 45), (22, 48), (24, 47)]))
              (.branch 47
                (.leaf [(8, 39), (11, 42), (25, 0), (28, 44), (41, 14), (26, 49), (43, 22)])
                (.branch 22
                  (.branch 14
                    (.leaf [(0, 25), (8, 20), (11, 42)])
                    (.leaf [(11, 42), (26, 0), (25, 50), (28, 44), (8, 20), (39, 12)]))
                  (.branch 0
                    (.branch 14
                      (.leaf [(8, 20), (24, 49), (42, 11), (40, 28)])
                      (.branch 28
                        (.leaf [(11, 42), (24, 49), (8, 20)])
                        (.branch 8
                          (.leaf [(12, 41), (24, 49), (40, 11)])
                          (.leaf [(20, 41), (12, 39), (24, 49), (40, 11)]))))
                    (.branch 14
                      (.leaf [(8, 20), (12, 43), (25, 48), (42, 11), (40, 28), (45, 24)])
                      (.branch 20
                        (.leaf [(12, 39), (24, 49), (42, 11), (40, 28), (48, 25)])
                        (.leaf [(8, 39), (26, 49), (24, 45), (41, 12), (42, 11), (40, 28), (43, 50), (25, 48)]))))))))
          (.branch 15
            (.branch 43
              (.leaf [(11, 34), (25, 48), (28, 21), (10, 39), (14, 26), (19, 45), (24, 47)])
              (.branch 45
                (.leaf [(11, 34), (26, 14), (17, 48), (25, 50), (10, 39), (12, 47)])
                (.branch 47
                  (.leaf [(11, 34), (17, 14), (19, 26), (0, 25), (21, 28), (16, 39)])
                  (.branch 14
                    (.branch 0
                      (.leaf [(11, 34), (12, 19), (16, 28), (22, 48)])
                      (.leaf [(10, 22), (11, 34), (12, 19), (16, 28), (25, 48)]))
                    (.branch 0
                      (.branch 12
                        (.leaf [(11, 34), (16, 28), (22, 48), (17, 24)])
                        (.leaf [(11, 34), (19, 50), (21, 28), (16, 39), (22, 48), (17, 24)]))
                      (.branch 12
                        (.leaf [(10, 22), (11, 34), (24, 17), (26, 16), (28, 50), (25, 48)])
                        (.branch 16
                          (.leaf [(10, 22), (11, 34), (19, 50), (24, 17), (25, 48)])
                          (.leaf [(11, 34), (21, 28), (24, 17), (26, 19), (39, 10), (22, 48), (25, 50)]))))))))
            (.branch 17
              (.branch 45
                (.branch 34
                  (.leaf [(25, 50), (10, 39), (12, 47)])
                  (.leaf [(8, 39), (11, 36), (25, 50), (26, 49), (10, 41), (12, 47)]))
                (.branch 10
                  (.leaf [(20, 8), (25, 50), (36, 11), (34, 49), (12, 19), (21, 28), (16, 26)])
                  (.branch 12
                    (.leaf [(20, 8), (22, 49), (34, 11), (0, 25), (26, 16), (28, 50)])
                    (.branch 16
                      (.leaf [(0, 25), (19, 50), (21, 49), (36, 11), (34, 8), (20, 47)])
                      (.branch 34
                        (.branch 50
                          (.leaf [(0, 26)])
                          (.leaf [(19, 26), (0, 25), (20, 47), (21, 28)]))
                        (.leaf [(11, 36), (22, 49), (21, 28), (39, 8), (41, 20), (47, 50), (19, 26), (0, 25)]))))))
              (.branch 45
                (.branch 14
                  (.branch 34
                    (.leaf [(25, 48), (28, 40), (42, 10)])
                    (.branch 47
                      (.leaf [(11, 42), (28, 44)])
                      (.leaf [(10, 42), (11, 40), (12, 43), (25, 48), (28, 44)])))
                  (.branch 34
                    (.leaf [(42, 10), (39, 12), (25, 48), (36, 43), (28, 40), (47, 50)])
                    (.branch 47
                      (.leaf [(8, 39), (26, 49), (28, 44), (42, 11), (36, 43)])
                      (.branch 10
                        (.leaf [(12, 43), (26, 49), (44, 28), (40, 11), (36, 48), (25, 50)])
                        (.branch 11
                          (.leaf [(8, 39), (26, 49), (41, 12), (43, 50), (25, 48)])
                          (.branch 12
                            (.leaf [(26, 49), (36, 48), (25, 50), (40, 28)])
                            (.branch 28
                              (.leaf [(8, 39), (25, 48), (26, 49)])
                              (.branch 25
                                (.leaf [(8, 39), (26, 49), (36, 43)])
                                (.leaf [(8, 39), (26, 49), (48, 36), (43, 50)])))))))))
                (.branch 12
                  (.branch 11
                    (.branch 26
                      (.leaf [(8, 20), (10, 22), (44, 28), (48, 25)])
                      (.branch 22
                        (.leaf [(0, 25), (8, 20), (14, 50), (16, 28)])
                        (.leaf [(8, 20), (10, 0), (14, 50), (16, 28), (24, 49), (25, 48)])))
                    (.branch 22
                      (.leaf [(20, 8), (24, 36), (34, 44), (42, 16), (28, 50), (14, 26), (0, 25)])
                      (.branch 26
                        (.leaf [(10, 42), (20, 8), (24, 36), (34, 44), (40, 28), (48, 25)])
                        (.branch 28
                          (.leaf [(14, 36), (20, 8), (24, 49), (42, 10), (0, 25)])
                          (.branch 25
                            (.leaf [(10, 42), (14, 36), (20, 8), (24, 49), (34, 44)])
                            (.leaf [(0, 10), (16, 42), (20, 8), (44, 34), (48, 36), (14, 50), (24, 49)]))))))
                  (.branch 50
                    (.branch 10
                      (.leaf [(16, 26), (20, 8), (21, 49), (24, 36), (40, 11), (34, 44)])
                      (.branch 34
                        (.leaf [(0, 26), (21, 42), (16, 39), (24, 36), (40, 22)])
                        (.branch 16
                          (.leaf [(8, 20), (21, 49), (24, 36), (11, 40), (22, 48)])
                          (.branch 49
                            (.leaf [(39, 8), (20, 41), (40, 11), (36, 48)])
                            (.leaf [(0, 26), (21, 42), (24, 36), (11, 40), (22, 48), (39, 8), (20, 41)])))))
                    (.branch 10
                      (.branch 26
                        (.leaf [(21, 28), (24, 36), (25, 48), (40, 11), (43, 20), (8, 34)])
                        (.branch 36
                          (.leaf [(16, 28), (20, 8), (21, 49), (34, 44), (19, 40)])
                          (.branch 28
                            (.leaf [(24, 49), (25, 48), (38, 11), (34, 8), (20, 43)])
                            (.leaf [(14, 21), (16, 43), (20, 8), (24, 49), (25, 48), (38, 11), (34, 44), (19, 40)]))))
                      (.branch 16
                        (.branch 11
                          (.leaf [(0, 25), (8, 20), (14, 21), (19, 44), (22, 48), (47, 24)])
                          (.branch 47
                            (.leaf [(0, 25), (8, 34), (19, 44), (22, 49), (21, 14)])
                            (.branch 49
                              (.leaf [(0, 25), (8, 20), (14, 36), (40, 19)])
                              (.leaf [(0, 25), (20, 8), (21, 14), (24, 36), (34, 44), (19, 40), (22, 48)]))))
                        (.branch 11
                          (.branch 14
                            (.leaf [(8, 20), (19, 44), (0, 25), (43, 22), (48, 47), (24, 49)])
                            (.branch 20
                              (.leaf [(24, 49), (21, 28), (22, 48), (25, 0), (26, 19)])
                              (.branch 49
                                (.leaf [(8, 39), (19, 44), (43, 0), (25, 48)])
                                (.leaf [(8, 39), (21, 28), (24, 47), (44, 19), (26, 0), (25, 48), (22, 43)]))))
                          (.branch 14
                            (.branch 22
                              (.leaf [(0, 25), (24, 47), (20, 8), (28, 44), (19, 42)])
                              (.branch 47
                                (.leaf [(8, 34), (25, 0), (28, 44), (19, 42)])
                                (.leaf [(24, 49), (42, 19), (40, 28), (44, 34), (8, 20), (43, 0), (25, 48)])))
                            (.branch 49
                              (.branch 20
                                (.leaf [(0, 25), (36, 48), (42, 19), (40, 28)])
                                (.branch 19
                                  (.leaf [(8, 39), (47, 48), (25, 0), (36, 43)])
                                  (.branch 48
                                    (.leaf [(0, 43), (8, 39), (40, 28)])
                                    (.leaf [(8, 39), (25, 0), (36, 43), (44, 28), (40, 47)]))))
                              (.branch 19
                                (.branch 20
                                  (.leaf [(0, 25), (21, 28), (22, 48), (24, 36)])
                                  (.leaf [(21, 28), (39, 8), (34, 41), (0, 25), (22, 43), (24, 36), (47, 48)]))
                                (.branch 20
                                  (.leaf [(24, 36), (34, 44), (38, 26), (0, 25), (42, 21), (28, 40), (22, 48)])
                                  (.branch 48
                                    (.leaf [(38, 26), (0, 43), (39, 8), (40, 28), (21, 42), (41, 34)])
                                    (.leaf [(25, 0), (26, 38), (39, 8), (41, 34), (42, 21), (44, 28), (22, 40), (43, 36), (24, 47)])))))))))))))))))
    (.branch 7
      (.branch 39
        (.branch 18
          (.leaf [(15, 40), (20, 37), (50, 19), (26, 29), (31, 21), (9, 35), (24, 17)])
          (.branch 19
            (.leaf [(11, 37), (21, 49), (15, 41), (20, 43), (25, 48), (29, 17)])
            (.branch 17
              (.leaf [(11, 37), (25, 50), (26, 49), (15, 41), (20, 45), (31, 21)])
              (.branch 37
                (.leaf [(26, 29), (31, 21), (9, 35), (24, 45), (40, 15), (43, 50)])
                (.branch 15
                  (.leaf [(26, 29), (31, 21), (9, 35), (24, 45), (20, 43), (48, 25)])
                  (.branch 21
                    (.leaf [(11, 40), (24, 35), (26, 29), (41, 20), (43, 50)])
                    (.branch 20
                      (.leaf [(9, 35), (11, 40), (24, 49), (26, 29), (48, 25)])
                      (.branch 24
                        (.leaf [(11, 40), (26, 29), (43, 50), (25, 48)])
                        (.leaf [(9, 35), (11, 40), (43, 50), (25, 48), (45, 29), (26, 49)])))))))))
        (.branch 19
          (.branch 20
            (.branch 49
              (.leaf [(25, 48), (29, 17)])
              (.branch 17
                (.leaf [(23, 11), (18, 25)])
                (.leaf [(21, 14), (24, 35), (29, 23), (11, 18), (25, 48)])))
            (.branch 18
              (.branch 14
                (.leaf [(15, 27), (24, 51), (29, 23)])
                (.leaf [(10, 37), (15, 27), (21, 51), (23, 29), (17, 24), (35, 48)]))
              (.branch 37
                (.leaf [(21, 51), (43, 17), (24, 35), (8, 29), (15, 27), (41, 23)])
                (.branch 17
                  (.leaf [(10, 41), (13, 25), (27, 15), (8, 35), (11, 23), (49, 21)])
                  (.branch 23
                    (.leaf [(13, 25), (16, 43), (27, 15), (8, 35), (14, 21)])
                    (.leaf [(10, 41), (11, 51), (13, 25), (16, 43), (29, 8), (14, 21), (15, 27), (48, 35), (24, 49)]))))))
          (.branch 20
            (.branch 17
              (.leaf [(10, 9), (15, 49), (26, 16), (31, 21), (12, 35), (11, 18), (23, 50)])
              (.branch 23
                (.leaf [(10, 9), (15, 40), (18, 25), (24, 35), (12, 21), (14, 26)])
                (.branch 21
                  (.branch 18
                    (.leaf [(15, 40), (16, 26), (24, 35)])
                    (.leaf [(11, 40), (15, 44), (16, 26), (24, 35), (48, 25)]))
                  (.branch 35
                    (.leaf [(29, 26), (16, 31), (50, 25), (11, 40), (15, 44)])
                    (.branch 18
                      (.leaf [(10, 9), (15, 40), (29, 26), (14, 50), (16, 31)])
                      (.leaf [(10, 9), (11, 40), (24, 49), (15, 44), (29, 26), (14, 50), (16, 31), (25, 48)]))))))
            (.branch 17
              (.branch 16
                (.leaf [(13, 25), (12, 35), (8, 15), (27, 50), (18, 11), (23, 49), (21, 51)])
                (.branch 18
                  (.leaf [(15, 27), (23, 50), (26, 51), (31, 21), (9, 10), (35, 12)])
                  (.branch 21
                    (.leaf [(13, 25), (35, 8), (10, 37), (11, 23), (41, 15)])
                    (.branch 37
                      (.leaf [(9, 35), (26, 51), (31, 8), (15, 27), (41, 23)])
                      (.branch 15
                        (.leaf [(10, 9), (12, 35), (13, 25), (26, 51), (11, 23)])
                        (.leaf [(13, 25), (27, 50), (31, 8), (9, 10), (35, 12), (41, 23), (11, 51), (26, 49)]))))))
              (.branch 18
                (.branch 14
                  (.leaf [(10, 9), (13, 40), (16, 31), (24, 51), (29, 23), (46, 15), (27, 48)])
                  (.branch 9
                    (.leaf [(12, 37), (13, 40), (24, 51), (26, 29), (46, 15), (23, 48), (27, 50)])
                    (.branch 12
                      (.leaf [(13, 40), (24, 51), (31, 16), (26, 29), (46, 15), (23, 48), (27, 50)])
                      (.leaf [(10, 37), (13, 40), (46, 15), (16, 31), (21, 51), (24, 35), (26, 29), (23, 48), (27, 50)]))))
                (.branch 37
                  (.branch 15
                    (.leaf [(31, 21), (9, 35), (43, 50), (48, 23), (24, 45), (29, 26)])
                    (.branch 21
                      (.leaf [(13, 40), (24, 35), (8, 29), (41, 23), (43, 50), (27, 48)])
                      (.branch 23
                        (.leaf [(9, 35), (8, 31), (13, 40), (26, 51), (24, 45)])
                        (.branch 35
                          (.leaf [(13, 40), (27, 50), (45, 29), (26, 51)])
                          (.branch 29
                            (.leaf [(13, 40), (24, 51), (43, 50), (27, 48)])
                            (.leaf [(8, 31), (13, 40), (26, 51), (24, 45), (43, 50), (27, 48)]))))))
                  (.branch 15
                    (.branch 21
                      (.leaf [(11, 23), (13, 25), (24, 35), (29, 26), (16, 43)])
                      (.branch 16
                        (.leaf [(12, 35), (13, 25), (14, 50), (24, 51), (11, 23)])
                        (.branch 35
                          (.leaf [(13, 25), (43, 50), (45, 29), (23, 11)])
                          (.leaf [(9, 10), (12, 43), (13, 25), (48, 23), (11, 51), (24, 45), (29, 26), (14, 50)]))))
                    (.branch 21
                      (.branch 23
                        (.leaf [(8, 35), (26, 16), (40, 13), (25, 46)])
                        (.branch 25
                          (.leaf [(10, 41), (11, 40), (24, 35), (8, 29), (26, 16)])
                          (.leaf [(10, 41), (13, 40), (11, 46), (24, 35), (8, 29), (26, 16), (43, 50), (27, 48)])))
                      (.branch 23
                        (.branch 16
                          (.leaf [(8, 35), (24, 51), (40, 13), (25, 46)])
                          (.leaf [(10, 9), (31, 8), (40, 13), (43, 12), (45, 24), (35, 14), (26, 51), (25, 46)]))
                        (.branch 16
                          (.branch 25
                            (.leaf [(11, 40), (12, 35), (8, 29), (24, 49)])
                            (.leaf [(12, 35), (8, 29), (13, 40), (14, 50), (27, 48), (44, 51), (11, 46), (24, 49)]))
                          (.branch 35
                            (.branch 25
                              (.leaf [(10, 41), (11, 40), (45, 29), (26, 49)])
                              (.leaf [(10, 41), (13, 40), (27, 50), (44, 51), (11, 46), (45, 29), (26, 49)]))
                            (.branch 25
                              (.branch 26
                                (.leaf [(8, 31), (9, 10), (11, 40), (24, 45), (41, 12)])
                                (.leaf [(9, 10), (11, 40), (14, 41), (12, 43), (31, 8), (29, 45), (24, 49)]))
                              (.branch 26
                                (.leaf [(8, 31), (9, 10), (13, 40), (11, 46), (24, 45), (41, 12), (43, 50), (27, 48)])
                                (.branch 11
                                  (.branch 41
                                    (.leaf [(31, 8), (29, 45), (24, 49), (43, 50), (27, 48)])
                                    (.leaf [(9, 10), (12, 43), (14, 50), (27, 48), (31, 8), (29, 45), (24, 49)]))
                                  (.branch 24
                                    (.branch 41
                                      (.leaf [(13, 40), (29, 8), (43, 50), (27, 48)])
                                      (.leaf [(9, 10), (12, 43), (13, 40), (14, 50), (27, 48), (29, 8)]))
                                    (.branch 41
                                      (.leaf [(13, 40), (31, 8), (29, 45), (43, 50), (27, 48), (44, 51)])
                                      (.leaf [(9, 10), (12, 43), (13, 40), (14, 50), (27, 48), (31, 8), (29, 45), (44, 51)])))))))))))))))))
      (.branch 20
        (.branch 9
          (.branch 23
            (.branch 40
              (.leaf [(14, 26)])
              (.branch 17
                (.leaf [(18, 25), (26, 33)])
                (.leaf [(14, 26), (15, 42), (18, 25), (24, 33)])))
            (.branch 17
              (.leaf [(11, 18), (12, 39), (15, 49), (28, 50), (25, 0), (26, 33)])
              (.branch 26
                (.branch 40
                  (.leaf [(12, 39), (44, 18), (48, 25)])
                  (.leaf [(12, 39), (22, 48), (11, 42), (15, 44), (18, 25), (28, 50)]))
                (.branch 40
                  (.leaf [(12, 39), (14, 50), (24, 49), (31, 0), (44, 18), (25, 48)])
                  (.branch 18
                    (.leaf [(0, 31), (12, 39), (14, 50), (15, 42), (22, 48), (24, 33)])
                    (.leaf [(11, 42), (12, 39), (14, 50), (29, 28), (31, 0), (25, 48), (22, 49), (15, 44), (24, 33)]))))))
          (.branch 23
            (.branch 42
              (.branch 26
                (.leaf [(18, 25), (22, 40), (24, 36)])
                (.leaf [(12, 38), (14, 36), (18, 25), (22, 40), (24, 33)]))
              (.branch 40
                (.leaf [(18, 25), (16, 26), (24, 36), (14, 35), (12, 21), (31, 38)])
                (.branch 14
                  (.leaf [(15, 38), (12, 19), (18, 25), (22, 10), (24, 33), (28, 16)])
                  (.branch 38
                    (.leaf [(16, 28), (18, 25), (21, 33), (10, 22), (35, 24)])
                    (.branch 21
                      (.leaf [(10, 22), (15, 36), (16, 26), (17, 24), (18, 25)])
                      (.leaf [(15, 36), (17, 24), (18, 25), (22, 10), (33, 26), (12, 19), (31, 16), (28, 35)]))))))
            (.branch 17
              (.branch 49
                (.leaf [(11, 36), (33, 10), (25, 0), (31, 16), (39, 12), (19, 50), (28, 35)])
                (.branch 0
                  (.leaf [(15, 36), (30, 18), (11, 34), (33, 21), (12, 19), (39, 16), (28, 50)])
                  (.branch 12
                    (.leaf [(15, 36), (22, 10), (30, 18), (11, 34), (25, 50), (28, 16), (26, 33)])
                    (.branch 16
                      (.leaf [(15, 36), (19, 50), (21, 33), (10, 22), (25, 18), (11, 34)])
                      (.branch 10
                        (.leaf [(15, 36), (26, 19), (30, 18), (11, 34), (25, 50), (31, 21)])
                        (.branch 11
                          (.branch 19
                            (.leaf [(33, 21), (28, 35)])
                            (.leaf [(25, 50), (26, 33), (31, 21), (28, 35)]))
                          (.branch 19
                            (.leaf [(15, 36), (25, 18), (33, 21), (28, 35)])
                            (.leaf [(15, 36), (26, 33), (30, 18), (25, 50), (31, 21), (28, 35)]))))))))
              (.branch 26
                (.branch 11
                  (.leaf [(15, 44), (24, 35), (31, 21), (12, 39), (10, 22), (28, 50), (25, 48)])
                  (.branch 28
                    (.leaf [(12, 39), (24, 36), (15, 42), (10, 22), (30, 18), (25, 48)])
                    (.branch 15
                      (.leaf [(24, 35), (30, 18), (31, 21), (12, 39), (10, 22), (48, 25)])
                      (.branch 35
                        (.leaf [(21, 31), (30, 18), (25, 50), (34, 44), (39, 10)])
                        (.leaf [(24, 36), (30, 18), (31, 21), (12, 39), (34, 44), (40, 22), (10, 42), (48, 25)])))))
                (.branch 21
                  (.branch 11
                    (.branch 0
                      (.leaf [(15, 44), (16, 39), (19, 50), (22, 48)])
                      (.leaf [(15, 44), (16, 39), (10, 22), (19, 50), (24, 35), (25, 48)]))
                    (.branch 15
                      (.branch 25
                        (.leaf [(16, 39), (10, 22), (24, 35)])
                        (.leaf [(16, 39), (18, 30), (19, 50), (24, 35), (0, 10), (22, 48)]))
                      (.branch 25
                        (.leaf [(16, 39), (10, 22), (29, 36), (24, 35), (34, 44), (19, 40)])
                        (.leaf [(16, 39), (29, 36), (24, 35), (0, 10), (30, 18), (34, 44), (38, 50), (19, 40), (22, 48)]))))
                  (.branch 35
                    (.branch 11
                      (.leaf [(25, 50), (33, 10), (22, 49), (15, 44), (19, 31), (16, 39)])
                      (.branch 15
                        (.leaf [(22, 10), (30, 18), (25, 50), (19, 31), (16, 39)])
                        (.leaf [(29, 36), (30, 18), (25, 50), (38, 31), (16, 39), (10, 33), (19, 40), (22, 49), (34, 44)])))
                    (.branch 11
                      (.branch 10
                        (.leaf [(12, 19), (14, 50), (24, 49), (15, 44), (25, 48), (29, 28), (16, 31)])
                        (.branch 19
                          (.leaf [(0, 25), (14, 39), (15, 49), (16, 28), (22, 48), (24, 33)])
                          (.branch 28
                            (.leaf [(12, 39), (15, 49), (22, 48), (24, 33), (25, 0)])
                            (.branch 25
                              (.leaf [(12, 39), (16, 31), (22, 49), (15, 44), (24, 33)])
                              (.branch 39
                                (.leaf [(0, 31), (44, 15), (22, 48), (33, 24)])
                                (.branch 49
                                  (.leaf [(0, 31), (14, 50), (33, 48)])
                                  (.leaf [(0, 31), (14, 50), (15, 44), (22, 48), (24, 33)])))))))
                      (.branch 15
                        (.branch 10
                          (.leaf [(12, 19), (14, 50), (29, 28), (16, 31), (30, 18), (25, 48)])
                          (.branch 25
                            (.leaf [(14, 39), (12, 19), (24, 33), (29, 28), (16, 31)])
                            (.leaf [(0, 31), (18, 30), (22, 48), (24, 33), (29, 28), (16, 39), (12, 19), (14, 50)])))
                        (.branch 19
                          (.branch 10
                            (.leaf [(14, 36), (16, 28), (24, 49), (30, 18), (25, 48)])
                            (.leaf [(0, 25), (30, 18), (34, 49), (22, 48), (33, 24), (14, 36), (29, 28), (16, 39)]))
                          (.branch 10
                            (.leaf [(12, 38), (30, 18), (31, 16), (40, 28), (29, 36), (14, 50), (24, 49), (25, 48), (34, 44)])
                            (.branch 28
                              (.leaf [(30, 18), (34, 49), (22, 48), (25, 0), (31, 38), (12, 39), (14, 36), (24, 33)])
                              (.branch 18
                                (.branch 36
                                  (.leaf [(0, 31), (22, 40), (42, 16), (39, 12)])
                                  (.branch 16
                                    (.leaf [(12, 38), (14, 50), (24, 33), (40, 22)])
                                    (.branch 33
                                      (.leaf [(0, 31), (12, 38), (39, 14)])
                                      (.branch 38
                                        (.leaf [(14, 39), (40, 22)])
                                        (.leaf [(0, 31), (12, 39), (14, 50), (40, 22)])))))
                                (.branch 36
                                  (.leaf [(33, 40), (22, 49), (34, 44), (42, 16), (39, 12), (0, 25), (31, 38)])
                                  (.branch 16
                                    (.leaf [(0, 25), (12, 38), (14, 50), (44, 34), (24, 49), (22, 40), (33, 48)])
                                    (.branch 22
                                      (.leaf [(24, 33), (34, 44), (0, 25), (31, 38), (12, 39), (14, 50)])
                                      (.branch 25
                                        (.leaf [(14, 39), (12, 38), (40, 33), (24, 49), (34, 44)])
                                        (.branch 33
                                          (.leaf [(0, 31), (44, 34), (12, 38), (39, 14)])
                                          (.branch 38
                                            (.leaf [(14, 39), (24, 49), (34, 44)])
                                            (.leaf [(0, 31), (12, 39), (14, 50), (24, 49), (34, 44)])))))))))))))))))))
        (.branch 39
          (.branch 18
            (.branch 9
              (.leaf [(31, 0), (50, 28), (15, 42), (22, 40), (24, 17), (29, 26), (33, 48)])
              (.branch 17
                (.branch 0
                  (.leaf [(15, 36), (19, 50), (28, 21)])
                  (.leaf [(15, 36), (35, 28), (50, 19), (26, 33), (21, 31)]))
                (.branch 19
                  (.leaf [(0, 35), (22, 48), (38, 15), (21, 28), (29, 36), (24, 33)])
                  (.branch 28
                    (.leaf [(22, 48), (42, 15), (36, 24), (33, 26), (0, 31)])
                    (.branch 33
                      (.leaf [(29, 36), (50, 38), (15, 42), (31, 0)])
                      (.branch 15
                        (.leaf [(21, 31), (22, 48), (24, 35), (0, 26)])
                        (.branch 35
                          (.leaf [(21, 31), (22, 40), (36, 29)])
                          (.leaf [(24, 36), (29, 26), (0, 31), (21, 42), (38, 50), (40, 22)]))))))))
            (.branch 17
              (.branch 9
                (.leaf [(11, 37), (28, 50), (25, 0), (31, 47), (33, 26), (41, 15), (45, 22)])
                (.branch 49
                  (.branch 0
                    (.leaf [(11, 36), (19, 50)])
                    (.leaf [(11, 36), (25, 50), (28, 35), (45, 19), (31, 47)]))
                  (.branch 0
                    (.branch 11
                      (.leaf [(15, 41), (19, 50), (28, 21)])
                      (.leaf [(19, 50), (28, 21), (30, 37), (34, 41), (15, 36)]))
                    (.branch 19
                      (.branch 11
                        (.leaf [(15, 41), (33, 21), (28, 35)])
                        (.leaf [(25, 37), (33, 21), (28, 35), (34, 41), (15, 36)]))
                      (.branch 21
                        (.branch 11
                          (.leaf [(15, 41), (25, 50)])
                          (.leaf [(30, 37), (25, 50), (34, 41), (15, 36)]))
                        (.leaf [(22, 45), (26, 33), (30, 37), (25, 50), (28, 35), (31, 47), (11, 34), (36, 15)]))))))
              (.branch 19
                (.branch 36
                  (.leaf [(22, 49), (30, 37), (25, 0), (33, 21), (28, 35), (34, 41)])
                  (.branch 49
                    (.leaf [(11, 38), (25, 0), (43, 33), (28, 29), (35, 48)])
                    (.branch 48
                      (.leaf [(0, 43), (21, 28), (30, 37), (11, 34), (38, 15)])
                      (.branch 0
                        (.leaf [(30, 37), (11, 34), (38, 15), (21, 28), (29, 47), (24, 33)])
                        (.branch 11
                          (.leaf [(15, 41), (22, 43), (21, 33), (24, 35), (28, 29)])
                          (.leaf [(22, 43), (25, 37), (34, 41), (15, 38), (21, 33), (24, 35), (28, 29)]))))))
                (.branch 15
                  (.branch 0
                    (.leaf [(22, 48), (11, 34), (37, 30), (9, 21), (33, 24), (28, 29)])
                    (.branch 21
                      (.leaf [(26, 29), (30, 37), (11, 34), (22, 43), (24, 35), (25, 48)])
                      (.branch 47
                        (.leaf [(25, 37), (11, 34), (26, 33), (28, 35), (9, 30)])
                        (.branch 33
                          (.leaf [(22, 45), (29, 28), (35, 9), (30, 37), (11, 34)])
                          (.leaf [(26, 29), (11, 34), (9, 30), (37, 25), (24, 45), (22, 43), (48, 35), (28, 50)])))))
                  (.branch 21
                    (.branch 11
                      (.branch 0
                        (.leaf [(22, 48), (24, 47)])
                        (.leaf [(26, 29), (22, 43), (24, 35), (25, 48), (47, 50)]))
                      (.branch 47
                        (.leaf [(22, 43), (30, 37), (25, 0), (26, 38), (41, 34)])
                        (.branch 0
                          (.leaf [(24, 36), (30, 37), (38, 50), (40, 22), (41, 34)])
                          (.leaf [(30, 37), (40, 22), (41, 34), (24, 35), (25, 48), (26, 29), (36, 43), (38, 50)]))))
                    (.branch 0
                      (.branch 11
                        (.leaf [(9, 30), (44, 28), (29, 47), (22, 48), (33, 24)])
                        (.branch 47
                          (.leaf [(22, 49), (28, 44), (36, 9), (30, 37), (34, 41)])
                          (.branch 9
                            (.leaf [(29, 28), (44, 37), (24, 49), (22, 40), (33, 48)])
                            (.leaf [(30, 37), (38, 50), (41, 34), (44, 28), (29, 36), (24, 49), (22, 40), (33, 48)]))))
                      (.branch 11
                        (.branch 24
                          (.leaf [(9, 30), (26, 29), (44, 28), (22, 43), (48, 25)])
                          (.branch 48
                            (.leaf [(9, 30), (43, 50), (44, 28), (45, 29)])
                            (.branch 28
                              (.leaf [(9, 30), (31, 47), (45, 22), (43, 33)])
                              (.branch 22
                                (.leaf [(25, 50), (30, 9), (31, 47), (29, 26)])
                                (.leaf [(25, 50), (30, 9), (31, 47), (43, 33), (45, 29), (26, 49)])))))
                        (.branch 24
                          (.branch 28
                            (.leaf [(26, 38), (41, 34), (9, 30), (37, 25), (43, 22)])
                            (.leaf [(29, 26), (31, 38), (40, 22), (41, 34), (9, 30), (43, 50), (44, 37), (25, 48)]))
                          (.branch 48
                            (.leaf [(31, 38), (40, 28), (41, 34), (9, 30), (43, 50), (44, 37), (45, 29), (26, 49)])
                            (.branch 9
                              (.branch 22
                                (.leaf [(31, 47), (33, 26), (29, 28), (44, 37)])
                                (.leaf [(31, 47), (45, 29), (25, 37), (44, 28), (40, 33), (26, 49), (43, 50)]))
                              (.branch 28
                                (.leaf [(25, 37), (36, 43), (33, 26), (41, 34), (47, 31), (38, 45), (22, 49)])
                                (.branch 22
                                  (.leaf [(30, 37), (25, 50), (33, 26), (35, 42), (36, 29), (38, 31), (41, 34)])
                                  (.branch 26
                                    (.leaf [(30, 37), (25, 50), (31, 47), (35, 42), (36, 43), (41, 34)])
                                    (.branch 37
                                      (.leaf [(34, 41), (35, 42), (31, 38), (45, 29), (36, 43)])
                                      (.branch 47
                                        (.leaf [(33, 43), (35, 42), (38, 45), (41, 34)])
                                        (.leaf [(25, 50), (31, 38), (35, 42), (40, 33), (41, 34), (43, 36), (29, 45)]))))))))))))))))
          (.branch 9
            (.branch 17
              (.branch 18
                (.leaf [(12, 37), (15, 27), (22, 51), (28, 50), (23, 0), (26, 33)])
                (.branch 0
                  (.leaf [(28, 50), (33, 8), (47, 12), (41, 15), (11, 37), (49, 22)])
                  (.branch 49
                    (.leaf [(11, 51), (13, 25), (27, 50), (33, 8), (31, 47), (12, 41)])
                    (.branch 50
                      (.leaf [(31, 8), (15, 41), (12, 37), (11, 51), (22, 45)])
                      (.branch 51
                        (.leaf [(23, 41), (27, 15), (33, 8), (31, 47), (12, 37)])
                        (.leaf [(13, 25), (22, 45), (26, 33), (27, 15), (8, 31), (47, 12), (37, 11), (23, 41)]))))))
              (.branch 18
                (.branch 26
                  (.branch 15
                    (.leaf [(12, 37), (22, 48), (23, 50)])
                    (.leaf [(12, 37), (42, 13), (46, 28), (40, 22), (23, 48), (27, 50)]))
                  (.branch 40
                    (.leaf [(12, 37), (14, 50), (24, 51), (29, 23), (31, 0), (27, 48)])
                    (.branch 23
                      (.leaf [(12, 37), (13, 42), (22, 51), (24, 33), (27, 15), (28, 46)])
                      (.leaf [(12, 37), (13, 42), (14, 50), (29, 28), (31, 0), (46, 15), (27, 48), (22, 51), (24, 33)]))))
                (.branch 15
                  (.branch 0
                    (.leaf [(11, 37), (12, 47), (14, 50), (28, 29), (22, 48), (33, 24)])
                    (.branch 47
                      (.leaf [(13, 25), (23, 11), (37, 14), (45, 22), (43, 33)])
                      (.branch 25
                        (.leaf [(11, 23), (12, 43), (14, 26), (22, 45), (24, 33)])
                        (.branch 22
                          (.leaf [(12, 37), (11, 23), (24, 33), (14, 26), (29, 28)])
                          (.branch 23
                            (.leaf [(45, 24), (51, 26), (14, 37), (12, 43)])
                            (.leaf [(48, 33), (11, 37), (12, 43), (14, 50), (28, 29), (26, 51), (24, 45)]))))))
                  (.branch 23
                    (.branch 33
                      (.leaf [(14, 37), (12, 47), (28, 46), (42, 13), (25, 51), (22, 45)])
                      (.branch 22
                        (.leaf [(8, 31), (24, 47), (12, 37), (14, 26), (28, 46), (25, 13)])
                        (.branch 25
                          (.leaf [(8, 31), (14, 26), (28, 40), (43, 12), (45, 24)])
                          (.leaf [(8, 31), (42, 13), (43, 12), (37, 14), (26, 51), (45, 24), (46, 28), (40, 47)]))))
                    (.branch 25
                      (.branch 29
                        (.branch 22
                          (.leaf [(11, 42), (12, 41), (24, 33)])
                          (.leaf [(14, 41), (12, 43), (42, 11), (40, 33), (24, 49)]))
                        (.branch 33
                          (.leaf [(11, 42), (14, 41), (12, 47), (28, 44), (45, 22)])
                          (.branch 22
                            (.leaf [(8, 31), (11, 42), (24, 47), (12, 41), (14, 26)])
                            (.leaf [(8, 31), (42, 11), (43, 12), (41, 14), (26, 49), (44, 28), (40, 47), (24, 45)]))))
                      (.branch 47
                        (.branch 26
                          (.branch 11
                            (.leaf [(28, 44), (43, 22)])
                            (.leaf [(13, 42), (37, 44), (28, 46), (43, 22)]))
                          (.branch 11
                            (.leaf [(8, 33), (14, 41), (27, 0), (28, 44), (43, 22)])
                            (.leaf [(8, 33), (13, 42), (27, 0), (41, 14), (43, 22), (46, 28), (49, 37), (44, 51)])))
                        (.branch 22
                          (.branch 14
                            (.leaf [(13, 42), (11, 46), (24, 33), (27, 0), (31, 8), (29, 28)])
                            (.leaf [(13, 42), (24, 33), (41, 12), (8, 31), (0, 26), (27, 50), (29, 28), (44, 37), (11, 46)]))
                          (.branch 26
                            (.leaf [(8, 31), (24, 45), (41, 12), (43, 50), (27, 48), (13, 42), (37, 44), (11, 40), (28, 46)])
                            (.branch 11
                              (.branch 0
                                (.leaf [(12, 41), (14, 50), (44, 28), (29, 8), (48, 33)])
                                (.leaf [(31, 8), (44, 28), (29, 45), (49, 24), (12, 41), (14, 50), (27, 48), (33, 43)]))
                              (.branch 28
                                (.leaf [(13, 42), (51, 24), (45, 0), (27, 48), (31, 8), (33, 43), (49, 37), (12, 41)])
                                (.branch 33
                                  (.leaf [(13, 42), (29, 45), (31, 0), (27, 50), (49, 37), (12, 41), (44, 51)])
                                  (.branch 0
                                    (.branch 37
                                      (.leaf [(8, 29), (24, 51), (40, 13)])
                                      (.leaf [(8, 29), (12, 41), (14, 50), (40, 13), (44, 51), (24, 49)]))
                                    (.branch 37
                                      (.leaf [(31, 8), (29, 45), (24, 51), (40, 13), (43, 50), (27, 48)])
                                      (.branch 24
                                        (.branch 50
                                          (.leaf [(12, 41), (29, 8), (40, 13)])
                                          (.leaf [(14, 41), (12, 43), (27, 48), (29, 8), (40, 13)]))
                                        (.branch 50
                                          (.leaf [(12, 41), (31, 8), (29, 45), (40, 13), (44, 51)])
                                          (.leaf [(14, 41), (12, 43), (27, 48), (31, 8), (29, 45), (40, 13), (44, 51)]))))))))))))))))
            (.branch 11
              (.branch 0
                (.branch 17
                  (.branch 12
                    (.leaf [(13, 30), (16, 28), (22, 49), (15, 8)])
                    (.branch 15
                      (.leaf [(13, 30), (16, 28), (19, 50), (21, 33)])
                      (.leaf [(8, 33), (13, 30), (19, 50), (22, 49), (21, 28), (16, 41)])))
                  (.branch 21
                    (.leaf [(13, 30), (16, 41), (22, 48), (24, 47), (29, 8), (15, 44), (19, 50)])
                    (.branch 47
                      (.leaf [(13, 30), (14, 41), (16, 28), (19, 44), (22, 49), (15, 8)])
                      (.branch 15
                        (.leaf [(12, 19), (13, 30), (14, 50), (16, 28), (22, 48), (24, 33)])
                        (.branch 28
                          (.leaf [(8, 33), (13, 30), (14, 41), (12, 19), (24, 49)])
                          (.branch 19
                            (.leaf [(13, 30), (14, 41), (29, 8), (22, 48), (33, 24)])
                            (.branch 33
                              (.leaf [(12, 41), (13, 30), (14, 50), (22, 49)])
                              (.leaf [(8, 29), (12, 41), (13, 30), (14, 50), (24, 49), (22, 48)]))))))))
                (.branch 21
                  (.branch 48
                    (.branch 15
                      (.leaf [(13, 30), (29, 26), (16, 43), (19, 50)])
                      (.leaf [(8, 29), (10, 41), (13, 30), (44, 19), (26, 16), (43, 50)]))
                    (.branch 50
                      (.leaf [(13, 30), (22, 10), (16, 26), (41, 15), (44, 17), (24, 35), (8, 29)])
                      (.branch 15
                        (.leaf [(19, 26), (16, 43), (22, 10), (30, 13), (25, 32), (35, 24), (17, 29)])
                        (.branch 17
                          (.leaf [(8, 35), (19, 26), (16, 41), (22, 10), (30, 13), (25, 32)])
                          (.branch 10
                            (.leaf [(24, 35), (8, 29), (30, 13), (25, 32), (43, 16), (26, 19)])
                            (.leaf [(22, 43), (30, 13), (25, 32), (41, 16), (44, 19), (26, 29), (8, 35), (24, 47)]))))))
                  (.branch 47
                    (.branch 15
                      (.leaf [(30, 13), (25, 32), (17, 14), (35, 28), (19, 26), (33, 43), (16, 45)])
                      (.branch 16
                        (.leaf [(19, 44), (17, 14), (22, 49), (30, 13), (25, 32), (33, 8)])
                        (.branch 14
                          (.leaf [(8, 33), (28, 44), (19, 45), (30, 13), (25, 32), (43, 22)])
                          (.branch 19
                            (.leaf [(17, 43), (22, 49), (28, 35), (8, 33), (30, 13), (25, 32)])
                            (.branch 22
                              (.leaf [(17, 44), (26, 33), (8, 35), (30, 13), (25, 32)])
                              (.branch 33
                                (.leaf [(17, 44), (28, 35), (30, 13), (25, 32)])
                                (.leaf [(8, 35), (26, 49), (28, 44), (17, 43), (30, 13), (25, 32)])))))))
                    (.branch 16
                      (.branch 48
                        (.leaf [(12, 19), (13, 30), (14, 50), (24, 49), (29, 8), (15, 44)])
                        (.branch 8
                          (.leaf [(10, 22), (12, 19), (27, 50), (14, 17), (24, 49), (30, 13), (25, 32)])
                          (.branch 17
                            (.leaf [(30, 13), (32, 25), (33, 10), (22, 49), (15, 27), (35, 12)])
                            (.branch 50
                              (.leaf [(12, 35), (13, 30), (44, 15), (10, 22), (33, 24)])
                              (.branch 15
                                (.leaf [(14, 35), (12, 19), (22, 10), (24, 33), (30, 13)])
                                (.branch 24
                                  (.leaf [(10, 22), (12, 19), (30, 13), (25, 32)])
                                  (.leaf [(14, 35), (12, 19), (30, 13), (25, 32), (33, 10), (22, 49)])))))))
                      (.branch 17
                        (.branch 19
                          (.leaf [(27, 15), (28, 35), (8, 33), (30, 13), (25, 32), (41, 10)])
                          (.branch 8
                            (.leaf [(12, 41), (10, 22), (26, 49), (27, 50), (30, 13), (25, 32)])
                            (.branch 10
                              (.leaf [(12, 35), (26, 49), (15, 27), (28, 50), (30, 13), (25, 32)])
                              (.leaf [(30, 13), (32, 25), (33, 26), (45, 22), (49, 15), (27, 50), (28, 35), (12, 41)]))))
                        (.branch 19
                          (.branch 33
                            (.leaf [(22, 49), (27, 15), (29, 28), (30, 13), (25, 32)])
                            (.leaf [(30, 13), (32, 25), (43, 22), (10, 41), (14, 35), (24, 49), (28, 29), (8, 15), (27, 48)]))
                          (.branch 33
                            (.branch 15
                              (.leaf [(12, 35), (14, 50), (22, 45), (28, 29), (30, 13)])
                              (.leaf [(27, 50), (30, 13), (25, 32), (44, 28), (29, 45), (22, 49), (12, 35), (14, 41)]))
                            (.branch 35
                              (.leaf [(30, 13), (32, 25), (44, 15), (27, 50), (41, 10), (43, 22), (45, 29), (26, 49)])
                              (.branch 15
                                (.branch 22
                                  (.leaf [(30, 13), (32, 25), (14, 26), (29, 28)])
                                  (.branch 25
                                    (.leaf [(12, 43), (14, 26), (24, 45)])
                                    (.branch 29
                                      (.leaf [(12, 43), (13, 30), (14, 50)])
                                      (.leaf [(12, 43), (13, 30), (24, 45), (26, 14), (28, 50)]))))
                                (.branch 22
                                  (.leaf [(12, 41), (27, 50), (14, 26), (30, 13), (25, 32), (31, 8), (29, 28)])
                                  (.branch 50
                                    (.branch 29
                                      (.leaf [(10, 41), (13, 30), (24, 49)])
                                      (.leaf [(8, 31), (10, 41), (13, 30), (26, 49), (24, 45)]))
                                    (.leaf [(10, 41), (12, 43), (14, 26), (27, 48), (30, 13), (25, 32), (31, 8), (44, 28), (29, 45), (24, 49)]))))))))))))
              (.branch 15
                (.branch 0
                  (.branch 47
                    (.leaf [(17, 14), (22, 51), (33, 21), (28, 16), (34, 13), (30, 37)])
                    (.branch 21
                      (.leaf [(16, 37), (18, 30), (13, 34), (19, 50), (22, 48), (24, 17)])
                      (.branch 17
                        (.leaf [(18, 30), (13, 34), (22, 51), (12, 19), (37, 16), (28, 50)])
                        (.branch 30
                          (.leaf [(12, 19), (14, 50), (16, 28), (22, 48), (24, 33)])
                          (.branch 28
                            (.leaf [(13, 34), (14, 37), (12, 19), (22, 48), (33, 24)])
                            (.branch 37
                              (.leaf [(13, 34), (19, 50), (22, 48), (33, 24)])
                              (.branch 19
                                (.branch 22
                                  (.leaf [(13, 34), (24, 33)])
                                  (.leaf [(13, 34), (48, 33), (24, 51)]))
                                (.branch 22
                                  (.leaf [(13, 34), (14, 50), (24, 33)])
                                  (.leaf [(13, 34), (14, 50), (48, 33), (24, 51)])))))))))
                  (.branch 47
                    (.branch 14
                      (.leaf [(19, 45), (23, 30), (28, 16), (32, 25), (13, 34), (33, 43)])
                      (.branch 16
                        (.leaf [(22, 51), (21, 33), (23, 30), (32, 25), (13, 34)])
                        (.branch 51
                          (.leaf [(13, 34), (17, 43), (19, 45), (28, 35)])
                          (.leaf [(17, 43), (22, 45), (19, 26), (23, 30), (32, 25), (13, 34), (33, 21), (28, 35)]))))
                    (.branch 21
                      (.branch 25
                        (.leaf [(10, 22), (19, 26), (16, 43), (30, 23), (29, 17)])
                        (.branch 43
                          (.leaf [(10, 37), (19, 26), (24, 35), (29, 23), (30, 13)])
                          (.branch 23
                            (.leaf [(13, 34), (17, 24), (19, 26), (16, 37), (10, 22)])
                            (.leaf [(18, 30), (13, 34), (50, 19), (10, 22), (37, 16), (26, 29), (17, 24), (35, 48)]))))
                      (.branch 25
                        (.branch 16
                          (.leaf [(19, 12), (22, 10), (30, 23), (29, 17), (14, 35)])
                          (.branch 29
                            (.leaf [(14, 35), (24, 33), (10, 22), (31, 19)])
                            (.leaf [(23, 30), (28, 35), (31, 19), (12, 43), (10, 22), (45, 24), (17, 14), (26, 33)])))
                        (.branch 43
                          (.branch 26
                            (.leaf [(10, 37), (28, 35), (24, 45), (34, 13), (30, 23)])
                            (.leaf [(10, 37), (14, 35), (28, 29), (31, 19), (34, 13), (45, 24), (48, 23), (30, 51)]))
                          (.branch 26
                            (.branch 30
                              (.leaf [(10, 22), (12, 35), (28, 50), (45, 24), (17, 48)])
                              (.branch 35
                                (.leaf [(13, 34), (18, 45), (22, 10), (23, 50)])
                                (.leaf [(12, 37), (10, 22), (13, 34), (18, 45), (24, 17), (28, 50), (23, 48)])))
                            (.branch 45
                              (.branch 14
                                (.leaf [(10, 33), (34, 13), (48, 23), (30, 51)])
                                (.leaf [(17, 48), (33, 10), (34, 13), (51, 30), (23, 50), (28, 35), (12, 37)]))
                              (.branch 30
                                (.branch 35
                                  (.leaf [(16, 31), (17, 29), (19, 50)])
                                  (.leaf [(12, 19), (31, 16), (10, 22), (14, 50), (28, 29), (17, 24), (33, 48)]))
                                (.branch 35
                                  (.leaf [(13, 34), (17, 29), (23, 50), (19, 31), (16, 37), (33, 10), (22, 51)])
                                  (.branch 17
                                    (.leaf [(13, 34), (23, 50), (28, 16), (31, 19), (12, 37), (33, 10), (22, 51)])
                                    (.branch 37
                                      (.leaf [(13, 34), (31, 19), (22, 51), (24, 33), (48, 23), (29, 28)])
                                      (.branch 50
                                        (.leaf [(13, 34), (16, 31), (10, 22), (48, 33), (24, 51)])
                                        (.branch 22
                                          (.leaf [(12, 19), (13, 34), (23, 29), (24, 33), (28, 16)])
                                          (.leaf [(10, 33), (12, 19), (13, 34), (24, 51), (31, 16), (28, 29), (23, 48)]))))))))))))))
                (.branch 17
                  (.branch 0
                    (.branch 12
                      (.leaf [(16, 28), (33, 8), (36, 13), (34, 49), (18, 30), (22, 51)])
                      (.branch 18
                        (.leaf [(19, 50), (22, 51), (33, 21), (28, 16), (34, 13)])
                        (.branch 21
                          (.leaf [(8, 34), (19, 50), (36, 13), (30, 37), (16, 41)])
                          (.branch 34
                            (.leaf [(19, 50), (22, 51), (28, 16), (30, 37)])
                            (.branch 16
                              (.leaf [(8, 33), (19, 50), (36, 13), (30, 51)])
                              (.branch 30
                                (.leaf [(8, 33), (19, 50), (22, 49)])
                                (.leaf [(8, 33), (13, 36), (19, 50), (37, 49), (22, 51)])))))))
                    (.branch 18
                      (.branch 21
                        (.leaf [(22, 10), (23, 50), (19, 26), (16, 37), (27, 34), (13, 36)])
                        (.branch 16
                          (.leaf [(23, 50), (19, 12), (27, 34), (13, 36), (33, 10), (22, 51)])
                          (.branch 19
                            (.leaf [(27, 34), (13, 36), (28, 35), (33, 10), (22, 51)])
                            (.branch 10
                              (.leaf [(12, 35), (23, 50), (26, 51), (27, 34), (13, 36)])
                              (.leaf [(22, 51), (23, 50), (26, 33), (27, 34), (13, 36), (28, 35), (12, 37)])))))
                      (.branch 21
                        (.branch 50
                          (.leaf [(22, 10), (26, 16), (35, 8), (36, 13), (30, 37)])
                          (.branch 10
                            (.leaf [(16, 26), (23, 30), (27, 34), (8, 35), (32, 25)])
                            (.branch 13
                              (.leaf [(8, 35), (19, 26), (23, 41), (16, 37)])
                              (.branch 16
                                (.leaf [(23, 30), (25, 32), (27, 34), (8, 35)])
                                (.leaf [(19, 26), (27, 34), (8, 35), (32, 25), (37, 30), (23, 41)])))))
                        (.branch 16
                          (.branch 50
                            (.leaf [(12, 35), (36, 13), (30, 51), (8, 33), (10, 22)])
                            (.branch 13
                              (.leaf [(19, 12), (23, 49), (35, 8), (33, 10), (22, 51)])
                              (.branch 8
                                (.leaf [(19, 12), (32, 25), (47, 10), (22, 49), (23, 30)])
                                (.branch 10
                                  (.leaf [(19, 12), (27, 34), (32, 25), (49, 23)])
                                  (.branch 12
                                    (.leaf [(27, 34), (32, 25), (22, 49)])
                                    (.branch 49
                                      (.leaf [(30, 51), (25, 32)])
                                      (.leaf [(22, 51), (23, 30), (25, 32), (27, 34)])))))))
                          (.branch 50
                            (.branch 8
                              (.leaf [(36, 13), (45, 22), (10, 41), (12, 37), (30, 51)])
                              (.branch 10
                                (.leaf [(12, 35), (36, 13), (30, 51), (26, 49)])
                                (.leaf [(33, 26), (35, 12), (36, 13), (41, 34), (45, 22), (49, 37), (30, 51)])))
                            (.branch 10
                              (.branch 13
                                (.leaf [(23, 49), (28, 35), (8, 31), (12, 19), (26, 51)])
                                (.branch 19
                                  (.leaf [(27, 34), (8, 35), (32, 25), (49, 23)])
                                  (.branch 8
                                    (.branch 51
                                      (.leaf [(23, 49)])
                                      (.leaf [(25, 32), (26, 49), (23, 30)]))
                                    (.branch 49
                                      (.leaf [(12, 35), (30, 51), (25, 32)])
                                      (.leaf [(12, 35), (23, 30), (26, 51), (25, 32), (27, 34)])))))
                              (.branch 12
                                (.leaf [(27, 34), (31, 8), (32, 25), (33, 26), (36, 13), (45, 22), (49, 23), (30, 51)])
                                (.branch 34
                                  (.leaf [(23, 30), (28, 35), (32, 25), (33, 26), (47, 31), (19, 45), (22, 51)])
                                  (.branch 25
                                    (.branch 8
                                      (.branch 23
                                        (.leaf [(22, 45)])
                                        (.branch 19
                                          (.leaf [(22, 49)])
                                          (.leaf [(26, 49), (22, 45)])))
                                      (.leaf [(28, 35), (30, 23), (33, 26), (47, 31), (19, 45), (22, 49)]))
                                    (.branch 26
                                      (.leaf [(22, 45), (28, 35), (8, 31), (36, 13), (37, 30), (23, 41)])
                                      (.branch 30
                                        (.leaf [(28, 35), (33, 8), (47, 31), (19, 45), (22, 49)])
                                        (.leaf [(13, 36), (28, 35), (33, 8), (37, 49), (23, 41), (47, 31), (19, 45), (22, 51)]))))))))))))
                  (.branch 0
                    (.branch 21
                      (.branch 47
                        (.branch 13
                          (.leaf [(41, 16), (37, 44)])
                          (.branch 34
                            (.leaf [(16, 37), (19, 46)])
                            (.branch 37
                              (.leaf [(19, 46)])
                              (.leaf [(16, 41), (30, 46), (19, 44)]))))
                        (.branch 13
                          (.branch 18
                            (.leaf [(16, 37), (22, 48), (46, 19)])
                            (.leaf [(8, 29), (22, 48), (41, 16), (37, 44), (46, 19)]))
                          (.branch 18
                            (.leaf [(16, 37), (24, 36), (32, 40), (22, 48), (38, 50), (19, 46)])
                            (.leaf [(24, 36), (29, 8), (32, 40), (22, 48), (38, 50), (16, 41), (34, 44), (19, 46), (30, 37)]))))
                      (.branch 40
                        (.branch 37
                          (.leaf [(38, 50), (48, 36), (24, 51), (29, 8), (18, 41)])
                          (.branch 18
                            (.leaf [(12, 38), (16, 42), (29, 36), (14, 50), (24, 51)])
                            (.leaf [(42, 16), (46, 30), (48, 36), (29, 8), (12, 38), (50, 14), (41, 34), (44, 51), (24, 49)])))
                        (.branch 18
                          (.branch 36
                            (.branch 19
                              (.leaf [(22, 51), (28, 16)])
                              (.leaf [(22, 51), (42, 16), (37, 12), (38, 50), (28, 46)]))
                            (.branch 19
                              (.branch 13
                                (.leaf [(14, 37), (16, 28), (22, 48), (33, 24)])
                                (.branch 16
                                  (.branch 22
                                    (.leaf [(24, 33)])
                                    (.leaf [(48, 33), (24, 51)]))
                                  (.leaf [(14, 37), (28, 29), (22, 48), (33, 24)])))
                              (.branch 28
                                (.leaf [(14, 37), (12, 38), (34, 13), (22, 48), (33, 24)])
                                (.branch 13
                                  (.branch 37
                                    (.leaf [(22, 48), (33, 24)])
                                    (.branch 22
                                      (.leaf [(14, 50), (24, 33)])
                                      (.leaf [(14, 50), (48, 33), (24, 51)])))
                                  (.branch 37
                                    (.branch 22
                                      (.leaf [(24, 33), (38, 50)])
                                      (.leaf [(38, 50), (48, 33), (24, 51)]))
                                    (.branch 22
                                      (.leaf [(12, 38), (14, 50), (16, 42), (24, 33)])
                                      (.leaf [(12, 38), (14, 50), (16, 42), (48, 33), (24, 51)])))))))
                          (.branch 37
                            (.branch 13
                              (.leaf [(8, 29), (19, 46), (28, 50), (22, 51), (24, 33), (47, 48)])
                              (.branch 24
                                (.leaf [(22, 48), (38, 50), (41, 34), (8, 29), (28, 46)])
                                (.leaf [(38, 50), (41, 34), (42, 19), (46, 28), (51, 22), (8, 33), (29, 36), (47, 48)])))
                            (.branch 13
                              (.branch 28
                                (.leaf [(8, 33), (14, 41), (19, 12), (47, 48), (22, 49)])
                                (.branch 47
                                  (.leaf [(8, 33), (14, 41), (46, 19), (44, 51)])
                                  (.branch 19
                                    (.leaf [(14, 41), (29, 8), (33, 48), (22, 49)])
                                    (.branch 22
                                      (.leaf [(12, 41), (14, 50), (24, 33), (8, 29)])
                                      (.leaf [(12, 41), (14, 50), (29, 8), (44, 51), (48, 33), (24, 49)])))))
                              (.branch 19
                                (.branch 24
                                  (.leaf [(14, 41), (16, 28), (22, 48), (29, 8)])
                                  (.branch 29
                                    (.leaf [(14, 41), (30, 51), (33, 48), (22, 49)])
                                    (.leaf [(28, 16), (30, 51), (47, 48), (22, 49), (33, 8), (34, 41), (14, 36)])))
                                (.branch 24
                                  (.leaf [(22, 48), (30, 46), (42, 16), (8, 29), (12, 38), (14, 41), (34, 44), (28, 50)])
                                  (.branch 28
                                    (.leaf [(30, 51), (38, 12), (47, 48), (22, 49), (33, 8), (34, 41), (14, 36)])
                                    (.branch 34
                                      (.leaf [(16, 42), (33, 48), (22, 51), (30, 46), (12, 38), (14, 36), (29, 47)])
                                      (.branch 47
                                        (.leaf [(8, 33), (36, 14), (41, 16), (44, 51), (22, 49), (30, 46)])
                                        (.leaf [(42, 16), (44, 51), (30, 46), (49, 22), (8, 29), (33, 48), (36, 14), (41, 12), (38, 50)])))))))))))
                    (.branch 18
                      (.branch 19
                        (.branch 48
                          (.leaf [(10, 37), (14, 21), (16, 28), (24, 51), (34, 13)])
                          (.branch 14
                            (.leaf [(16, 28), (23, 29), (27, 34), (13, 38), (10, 22), (33, 24)])
                            (.branch 24
                              (.leaf [(21, 28), (16, 37), (10, 22), (23, 29), (27, 34)])
                              (.branch 28
                                (.leaf [(27, 34), (33, 10), (22, 51), (36, 13)])
                                (.branch 10
                                  (.leaf [(21, 51), (23, 29), (27, 34), (36, 13)])
                                  (.leaf [(16, 37), (22, 51), (21, 33), (23, 29), (27, 34), (36, 13)]))))))
                        (.branch 21
                          (.branch 48
                            (.leaf [(10, 37), (16, 26), (32, 40), (34, 13), (38, 50)])
                            (.branch 13
                              (.leaf [(22, 10), (24, 35), (27, 50), (23, 29), (26, 16)])
                              (.leaf [(32, 40), (22, 10), (34, 27), (35, 24), (36, 29), (23, 50), (37, 16), (26, 38)])))
                          (.branch 26
                            (.branch 35
                              (.leaf [(23, 50), (27, 34), (32, 40), (13, 36), (22, 10)])
                              (.branch 13
                                (.leaf [(12, 37), (10, 22), (46, 28), (23, 48), (27, 50)])
                                (.leaf [(12, 37), (24, 36), (32, 40), (34, 27), (42, 10), (22, 48), (23, 50), (28, 46)])))
                            (.branch 28
                              (.branch 48
                                (.leaf [(14, 37), (10, 42), (12, 38), (13, 34)])
                                (.branch 10
                                  (.leaf [(12, 38), (14, 36), (13, 34), (24, 51)])
                                  (.leaf [(22, 51), (27, 34), (31, 38), (12, 37), (14, 36), (13, 42), (24, 33)])))
                              (.branch 48
                                (.branch 13
                                  (.leaf [(10, 37), (14, 50), (16, 31), (24, 51)])
                                  (.branch 37
                                    (.leaf [(24, 51), (31, 38), (32, 40)])
                                    (.leaf [(10, 42), (12, 38), (14, 50), (16, 31), (24, 51), (32, 40)])))
                                (.branch 13
                                  (.branch 37
                                    (.leaf [(22, 51), (27, 50), (23, 29), (33, 24)])
                                    (.branch 24
                                      (.leaf [(10, 22), (14, 50), (16, 31), (23, 29)])
                                      (.leaf [(12, 35), (14, 50), (16, 31), (23, 29), (33, 10), (22, 51)])))
                                  (.branch 10
                                    (.leaf [(16, 31), (32, 40), (34, 27), (51, 24), (12, 35), (38, 50), (14, 36), (23, 29)])
                                    (.branch 14
                                      (.leaf [(12, 38), (23, 29), (27, 34), (31, 16), (32, 40), (22, 51), (24, 33)])
                                      (.branch 24
                                        (.leaf [(22, 40), (29, 23), (34, 27), (42, 16), (31, 38), (12, 37)])
                                        (.branch 12
                                          (.leaf [(31, 16), (32, 40), (22, 51), (34, 27), (36, 29), (23, 50)])
                                          (.leaf [(32, 40), (22, 51), (34, 27), (35, 42), (36, 29), (23, 50), (37, 16), (31, 38)])))))))))))
                      (.branch 19
                        (.branch 48
                          (.branch 37
                            (.leaf [(24, 51), (21, 28), (29, 8), (38, 13)])
                            (.leaf [(10, 41), (14, 21), (38, 13), (30, 51), (24, 49), (34, 8), (29, 28), (16, 43)]))
                          (.branch 24
                            (.branch 37
                              (.leaf [(21, 28), (22, 43), (27, 34), (8, 29), (13, 38)])
                              (.leaf [(27, 34), (8, 29), (32, 25), (38, 13), (30, 23), (10, 22), (43, 16), (28, 21), (14, 41)]))
                            (.branch 37
                              (.branch 29
                                (.leaf [(27, 34), (13, 38), (21, 33), (43, 22)])
                                (.branch 34
                                  (.leaf [(35, 28), (36, 43), (22, 51), (21, 33)])
                                  (.branch 21
                                    (.leaf [(8, 35), (22, 43), (23, 41), (36, 13)])
                                    (.leaf [(23, 41), (28, 35), (8, 33), (38, 13), (36, 43), (22, 51)]))))
                              (.branch 13
                                (.branch 21
                                  (.leaf [(35, 8), (16, 43), (22, 10), (41, 23)])
                                  (.branch 10
                                    (.leaf [(14, 35), (8, 29), (23, 49), (28, 16)])
                                    (.leaf [(47, 29), (51, 22), (49, 23), (8, 33), (43, 16), (28, 35), (14, 41)])))
                                (.branch 21
                                  (.leaf [(25, 32), (27, 34), (30, 23), (35, 8), (16, 41), (10, 22), (43, 36), (29, 47)])
                                  (.branch 29
                                    (.leaf [(27, 34), (30, 51), (25, 32), (35, 14), (49, 22), (10, 33), (41, 16)])
                                    (.branch 41
                                      (.leaf [(28, 35), (8, 33), (30, 51), (25, 32), (36, 43), (22, 49)])
                                      (.branch 22
                                        (.leaf [(16, 28), (23, 30), (25, 32), (27, 34), (33, 8), (35, 14)])
                                        (.leaf [(27, 34), (32, 25), (47, 10), (49, 23), (30, 51), (8, 33), (14, 35), (28, 16), (36, 43)])))))))))
                        (.branch 21
                          (.branch 48
                            (.branch 13
                              (.leaf [(8, 29), (26, 16), (41, 10), (37, 44), (43, 50)])
                              (.leaf [(32, 40), (46, 30), (8, 29), (10, 37), (44, 34), (41, 16), (26, 38), (43, 50)]))
                            (.branch 13
                              (.branch 10
                                (.leaf [(24, 35), (8, 29), (26, 16), (27, 50), (23, 44)])
                                (.branch 16
                                  (.leaf [(27, 50), (44, 23), (8, 29), (35, 24)])
                                  (.leaf [(22, 43), (26, 29), (8, 35), (24, 47), (27, 50), (37, 44), (23, 41)])))
                              (.branch 50
                                (.leaf [(32, 40), (22, 10), (46, 30), (24, 35), (36, 29), (8, 34), (26, 16), (37, 44)])
                                (.branch 29
                                  (.leaf [(24, 35), (27, 34), (44, 37), (30, 46), (25, 32), (40, 22), (10, 41), (16, 43)])
                                  (.branch 37
                                    (.leaf [(23, 41), (26, 38), (27, 34), (8, 35), (32, 40), (22, 43), (36, 24)])
                                    (.branch 34
                                      (.leaf [(23, 30), (35, 24), (36, 43), (16, 26), (46, 25), (32, 40), (22, 10)])
                                      (.branch 10
                                        (.leaf [(8, 35), (24, 36), (38, 26), (16, 43), (40, 32), (25, 46), (30, 23)])
                                        (.leaf [(8, 35), (38, 26), (44, 23), (30, 46), (25, 32), (41, 16), (22, 40), (43, 36), (24, 47)]))))))))
                          (.branch 16
                            (.branch 48
                              (.leaf [(12, 38), (14, 50), (29, 8), (32, 40), (46, 30), (13, 34), (44, 51), (24, 49)])
                              (.branch 13
                                (.branch 24
                                  (.leaf [(8, 29), (10, 22), (14, 50), (23, 44)])
                                  (.branch 23
                                    (.leaf [(14, 35), (8, 33), (12, 47), (10, 22)])
                                    (.leaf [(27, 50), (14, 35), (12, 47), (29, 8), (33, 10), (44, 51), (22, 49)])))
                                (.branch 24
                                  (.leaf [(10, 22), (12, 38), (14, 50), (27, 34), (8, 29), (40, 32), (25, 46), (30, 23)])
                                  (.branch 50
                                    (.leaf [(12, 35), (32, 40), (36, 29), (46, 30), (8, 33), (10, 22), (49, 34)])
                                    (.branch 8
                                      (.leaf [(14, 36), (38, 12), (10, 47), (32, 40), (22, 49), (23, 44), (25, 46), (30, 51)])
                                      (.branch 22
                                        (.leaf [(27, 34), (32, 25), (38, 12), (35, 14), (36, 29), (44, 23), (30, 46)])
                                        (.leaf [(27, 34), (38, 12), (35, 14), (36, 29), (49, 23), (44, 51), (30, 46), (25, 32), (10, 33), (40, 47)])))))))
                            (.branch 47
                              (.branch 13
                                (.branch 14
                                  (.leaf [(8, 33), (43, 22), (46, 28), (49, 23), (44, 51)])
                                  (.branch 22
                                    (.leaf [(26, 33), (8, 35), (37, 44), (23, 41)])
                                    (.branch 44
                                      (.leaf [(35, 8), (43, 33), (26, 49)])
                                      (.leaf [(37, 49), (23, 41), (43, 33), (8, 35), (26, 51), (28, 46)]))))
                                (.branch 14
                                  (.branch 22
                                    (.leaf [(27, 34), (8, 33), (32, 25), (23, 30), (44, 28)])
                                    (.branch 34
                                      (.leaf [(23, 30), (28, 46), (32, 25), (33, 43)])
                                      (.branch 23
                                        (.leaf [(8, 33), (28, 46), (32, 25), (38, 45)])
                                        (.branch 25
                                          (.leaf [(8, 33), (28, 44), (38, 45)])
                                          (.branch 28
                                            (.leaf [(8, 33), (30, 51), (38, 45)])
                                            (.leaf [(8, 33), (38, 45), (44, 51), (30, 46)]))))))
                                  (.branch 34
                                    (.leaf [(23, 30), (32, 25), (36, 43), (33, 26), (38, 45), (22, 51), (42, 35), (28, 46)])
                                    (.branch 51
                                      (.leaf [(36, 43), (33, 8), (37, 49), (23, 41), (38, 45), (42, 35), (28, 46)])
                                      (.branch 23
                                        (.leaf [(32, 25), (36, 43), (22, 45), (38, 26), (33, 8), (42, 35), (28, 46)])
                                        (.branch 37
                                          (.leaf [(36, 43), (22, 45), (38, 26), (33, 8), (42, 35), (28, 46)])
                                          (.branch 22
                                            (.leaf [(30, 46), (25, 32), (38, 26), (33, 8), (42, 35), (28, 44)])
                                            (.leaf [(30, 46), (25, 32), (36, 43), (42, 35), (8, 33), (28, 44), (45, 38), (26, 49)]))))))))
                              (.branch 13
                                (.branch 22
                                  (.branch 14
                                    (.leaf [(24, 33), (31, 8), (46, 28), (29, 23)])
                                    (.leaf [(27, 50), (31, 8), (46, 28), (24, 33), (26, 29), (35, 12), (37, 44), (23, 41)]))
                                  (.branch 23
                                    (.branch 33
                                      (.leaf [(46, 28), (12, 35), (14, 37)])
                                      (.leaf [(10, 37), (31, 8), (43, 12), (45, 24), (46, 28), (35, 14), (26, 51)]))
                                    (.branch 33
                                      (.leaf [(27, 50), (45, 29), (46, 28), (49, 37), (44, 51), (12, 35), (14, 41)])
                                      (.branch 35
                                        (.branch 26
                                          (.leaf [(27, 50), (41, 10), (37, 44)])
                                          (.leaf [(27, 50), (29, 45), (41, 10), (49, 37), (44, 51)]))
                                        (.branch 37
                                          (.leaf [(31, 8), (43, 50), (27, 48), (46, 28), (24, 45), (29, 26)])
                                          (.branch 26
                                            (.leaf [(8, 31), (10, 41), (12, 43), (24, 45), (44, 28), (48, 27)])
                                            (.leaf [(10, 41), (12, 43), (14, 50), (27, 48), (31, 8), (46, 28), (29, 45), (44, 51), (24, 49)])))))))
                                (.branch 22
                                  (.branch 14
                                    (.leaf [(12, 38), (24, 33), (27, 34), (31, 8), (32, 25), (29, 23), (30, 46), (28, 44)])
                                    (.branch 8
                                      (.leaf [(24, 36), (26, 38), (27, 50), (32, 25), (12, 41), (23, 30), (37, 44), (28, 46)])
                                      (.branch 23
                                        (.leaf [(27, 34), (31, 38), (26, 33), (32, 25), (36, 24), (37, 12), (42, 35)])
                                        (.branch 28
                                          (.leaf [(27, 34), (30, 37), (25, 32), (31, 38), (12, 41), (26, 33)])
                                          (.branch 12
                                            (.leaf [(30, 46), (32, 25), (44, 34), (27, 50), (24, 33), (26, 29)])
                                            (.leaf [(31, 38), (32, 25), (41, 34), (27, 50), (42, 35), (44, 37), (30, 46), (24, 33), (26, 29)]))))))
                                  (.branch 23
                                    (.branch 33
                                      (.leaf [(27, 34), (31, 38), (32, 25), (36, 14), (37, 12), (42, 35), (28, 46)])
                                      (.branch 35
                                        (.leaf [(10, 37), (27, 34), (31, 38), (26, 51), (36, 43), (40, 32)])
                                        (.branch 25
                                          (.leaf [(10, 42), (27, 34), (8, 31), (28, 40), (12, 43), (14, 26), (36, 24)])
                                          (.leaf [(27, 34), (8, 31), (32, 40), (28, 46), (42, 10), (37, 12), (43, 36), (14, 26), (38, 45), (24, 51)]))))
                                    (.branch 33
                                      (.branch 37
                                        (.leaf [(31, 38), (36, 29), (41, 34), (27, 50), (42, 35), (28, 46)])
                                        (.branch 28
                                          (.leaf [(27, 34), (30, 51), (25, 32), (31, 38), (12, 41), (14, 36)])
                                          (.leaf [(31, 38), (32, 25), (42, 35), (12, 41), (45, 29), (36, 14), (46, 30), (49, 34), (27, 50), (44, 51)])))
                                      (.branch 35
                                        (.branch 25
                                          (.leaf [(10, 41), (27, 34), (31, 38), (43, 36), (45, 29), (26, 49)])
                                          (.leaf [(31, 38), (32, 40), (45, 29), (36, 43), (46, 30), (50, 27), (10, 41), (26, 51), (34, 44), (37, 49)]))
                                        (.branch 37
                                          (.branch 29
                                            (.leaf [(24, 51), (31, 38), (32, 40), (41, 34), (43, 50)])
                                            (.leaf [(32, 40), (41, 34), (8, 31), (46, 28), (26, 51), (24, 45), (38, 50), (27, 48), (36, 43)]))
                                          (.branch 50
                                            (.leaf [(12, 41), (10, 42), (31, 8), (32, 40), (46, 30), (48, 36), (29, 45), (24, 49), (26, 51), (34, 44)])
                                            (.branch 26
                                              (.leaf [(30, 46), (31, 8), (42, 10), (45, 24), (12, 41), (43, 36), (25, 32), (40, 28), (44, 34), (27, 48)])
                                              (.branch 34
                                                (.leaf [(10, 42), (14, 36), (31, 38), (12, 43), (48, 25), (32, 40), (24, 45), (29, 28), (46, 30)])
                                                (.branch 36
                                                  (.leaf [(8, 31), (42, 10), (41, 12), (38, 45), (30, 46), (25, 32), (40, 28), (44, 51)])
                                                  (.branch 25
                                                    (.branch 12
                                                      (.leaf [(10, 42), (31, 8), (40, 28), (29, 45), (24, 49)])
                                                      (.branch 28
                                                        (.leaf [(8, 31), (14, 41), (10, 42), (38, 45)])
                                                        (.branch 45
                                                          (.leaf [(8, 31), (14, 41), (10, 42)])
                                                          (.leaf [(14, 41), (10, 42), (24, 49), (29, 8), (31, 38)]))))
                                                    (.leaf [(14, 41), (10, 42), (27, 48), (32, 40), (43, 12), (49, 24), (8, 31), (38, 45), (29, 28), (44, 51), (30, 46)]))))))))))))))))))))))))))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
private theorem checkedRootSSSSS : treeOK treeRootSSSSS ([0, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 12 = true := by rfl

private def treeRootSSSS : Tree := .branch 5 treeRootSSSST treeRootSSSSS
private theorem checkedRootSSSS : treeOK treeRootSSSS ([0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 12 = true := by
  exact joinChecks 5 treeRootSSSST treeRootSSSSS ([0, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 12
    (by rfl) checkedRootSSSST checkedRootSSSSS

private def treeRootSSS : Tree := .branch 4 treeRootSSST treeRootSSSS
private theorem checkedRootSSS : treeOK treeRootSSS ([0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 12 = true := by
  exact joinChecks 4 treeRootSSST treeRootSSSS ([0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 12
    (by rfl) checkedRootSSST checkedRootSSSS

private def treeRootSS : Tree := .branch 3 treeRootSST treeRootSSS
private theorem checkedRootSS : treeOK treeRootSS ([0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 12 = true := by
  exact joinChecks 3 treeRootSST treeRootSSS ([0, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 12
    (by rfl) checkedRootSST checkedRootSSS

private def treeRootS : Tree := .branch 2 treeRootST treeRootSS
private theorem checkedRootS : treeOK treeRootS ([0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 12 = true := by
  exact joinChecks 2 treeRootST treeRootSS ([0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51]) 12
    (by rfl) checkedRootST checkedRootSS

private def treeRoot : Tree := .branch 1 treeRootT treeRootS
private theorem checkedRoot : treeOK treeRoot (List.range 52) 12 = true := by
  exact joinChecks 1 treeRootT treeRootS (List.range 52) 12
    (by rfl) checkedRootT checkedRootS

private def Independent (S : Finset Nat) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, edge a b = false

private def InPool (S : Finset Nat) (pool : List Nat) : Prop :=
  ∀ a ∈ S, a ∈ pool

private theorem independent_subset {S T : Finset Nat}
    (h : Independent S) (hst : T ⊆ S) : Independent T :=
  fun a ha b hb => h a (hst ha) b (hst hb)

private theorem erase_pool {S : Finset Nat} {pool : List Nat}
    (h : InPool S pool) (v : Nat) : InPool (S.erase v) (pool.erase v) := by
  intro w hw
  obtain ⟨hne, hwS⟩ := Finset.mem_erase.mp hw
  exact (List.mem_erase_of_ne hne).mpr (h w hwS)

private theorem avoid_pool {S : Finset Nat} {pool : List Nat} {v : Nat}
    (h : InPool S pool) (hv : v ∉ S) : InPool S (pool.erase v) := by
  simpa only [Finset.erase_eq_of_notMem hv] using erase_pool h v

private theorem pair_cost {S : Finset Nat} {a b : Nat}
    (hS : Independent S) (hab : edge a b = true) :
    S.card ≤ ((S.erase a).erase b).card + 1 := by
  by_cases ha : a ∈ S
  · have hb : b ∉ S := by
      intro hb
      rw [hS a ha b hb] at hab
      contradiction
    have hb' : b ∉ S.erase a := fun h => hb (Finset.mem_of_mem_erase h)
    rw [Finset.erase_eq_of_notMem hb', Finset.card_erase_add_one ha] <;> exact le_rfl
  · rw [Finset.erase_eq_of_notMem ha]
    by_cases hb : b ∈ S
    · rw [Finset.card_erase_add_one hb] <;> exact le_rfl
    · rw [Finset.erase_eq_of_notMem hb]
      omega

private theorem matching_bound (matching : List (Nat × Nat)) :
    ∀ (pool : List Nat) (need : Nat) (S : Finset Nat),
      matchOK matching pool need = true → InPool S pool → Independent S →
      S.card < need := by
  induction matching with
  | nil =>
      intro pool need S hok hPool _
      have hlt : pool.length < need := by
        simpa only [matchOK, decide_eq_true_eq] using hok
      have hsub : S ⊆ pool.toFinset :=
        fun a ha => List.mem_toFinset.mpr (hPool a ha)
      exact (Finset.card_le_card hsub).trans_lt ((List.toFinset_card_le pool).trans_lt hlt)
  | cons p rest ih =>
      obtain ⟨a, b⟩ := p
      intro pool need S hok hPool hS
      simp only [matchOK, pairOK, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨_, hab, hpos⟩, hrest⟩ := hok
      have hsub : (S.erase a).erase b ⊆ S :=
        (Finset.erase_subset b (S.erase a)).trans (Finset.erase_subset a S)
      have hsmall := ih _ _ _ hrest (erase_pool (erase_pool hPool a) b)
        (independent_subset hS hsub)
      have hcost := pair_cost hS hab
      omega

private theorem tree_bound (tree : Tree) :
    ∀ (pool : List Nat) (need : Nat) (S : Finset Nat),
      treeOK tree pool need = true → InPool S pool → Independent S →
      S.card < need := by
  induction tree with
  | leaf pairs => exact matching_bound pairs
  | branch v take skip ihTake ihSkip =>
      intro pool need S hok hPool hS
      simp only [treeOK, pivotOK, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨_, hpos⟩, htake, hskip⟩ := hok
      by_cases hv : v ∈ S
      · have hKept : InPool (S.erase v) (kept v pool) := by
          intro w hw
          apply List.mem_filter.mpr
          exact ⟨erase_pool hPool v w hw, by simp [hS v hv w (Finset.mem_of_mem_erase hw)]⟩
        have hb := ihTake _ _ _ htake hKept
          (independent_subset hS (Finset.erase_subset v S))
        have hc := Finset.card_erase_add_one hv
        omega
      · exact ihSkip _ _ _ hskip (avoid_pool hPool hv) hS

private theorem matrix_properties {a : Nat} (ha : a < 52) :
    edge a a = false ∧ ∀ b < 52, edge a b = edge b a := by
  have h := matrix_checked
  simp only [matrixOK, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨hdiag, hsym⟩ := h a (List.mem_range.mpr ha)
  exact ⟨hdiag, fun b hb => hsym b (List.mem_range.mpr hb)⟩

private theorem no_triangle {a b c : Nat} (ha : a < 52) (hb : b < 52)
    (hab : edge a b = true) (hac : edge a c = true) (hbc : edge b c = true) : False := by
  have h := triangle_checked
  simp only [triangleOK, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  rcases h a (List.mem_range.mpr ha) b (List.mem_range.mpr hb) with hfalse | hzero
  · rw [hab] at hfalse
    contradiction
  · change (rows.getD a 0).testBit c = true at hac
    change (rows.getD b 0).testBit c = true at hbc
    have hbit : (rows.getD a 0 &&& rows.getD b 0).testBit c = true := by
      rw [Nat.testBit_and, hac, hbc] <;> rfl
    rw [hzero] at hbit
    simp at hbit

private def restrictedGraph (n : Nat) (hn : n ≤ 52) : SimpleGraph (Fin n) where
  Adj x y := edge x.val y.val = true
  symm := ⟨fun x y h =>
    ((matrix_properties (x.isLt.trans_le hn)).2 y.val (y.isLt.trans_le hn)).symm.trans h⟩
  loopless := ⟨fun x h => by
    have hdiag := (matrix_properties (x.isLt.trans_le hn)).1
    change edge x.val x.val = true at h
    rw [hdiag] at h
    contradiction⟩

private theorem restricted_triangle_free (n : Nat) (hn : n ≤ 52) :
    (restrictedGraph n hn).CliqueFree 3 := by
  intro s hs
  obtain ⟨a, b, _, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact no_triangle (a.isLt.trans_le hn) (b.isLt.trans_le hn) hab hac hbc

private theorem restricted_independent_bound (n : Nat) (hn : n ≤ 52)
    {k : Nat} {S : Finset (Fin n)} (hS : (restrictedGraph n hn).IsNIndepSet k S) :
    k < 12 := by
  let T := S.image Fin.val
  have hPool : InPool T (List.range 52) := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hw
    exact List.mem_range.mpr (x.isLt.trans_le hn)
  have hT : Independent T := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    by_cases hxy : x = y
    · subst y
      exact (matrix_properties (x.isLt.trans_le hn)).1
    · have hno := hS.isIndepSet hx hy hxy
      cases he : edge x.val y.val
      · rfl
      · exact (hno he).elim
  have hcard : T.card = k :=
    (Finset.card_image_of_injective S Fin.val_injective).trans hS.card_eq
  rw [← hcard]
  exact tree_bound treeRoot _ _ _ checkedRoot hPool hT

private theorem H_le_eleven (n : Nat) (hn : n ≤ 52) : Erdos151.H n ≤ 11 := by
  unfold Erdos151.H
  apply csSup_le
  · refine ⟨0, ?_⟩
    intro G _
    exact ⟨∅, by simp [SimpleGraph.isNIndepSet_iff]⟩
  · intro k hk
    obtain ⟨S, hS⟩ := hk (restrictedGraph n hn) (restricted_triangle_free n hn)
    have hlt := restricted_independent_bound n hn hS
    omega

end Ramsey151Witness

theorem OMA.solution : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H1_R1_H1_R1.H3 := by
  change ∀ n, 12 ≤ Erdos151.H n → 53 ≤ n
  intro n hn
  by_contra hsmall
  have h := Ramsey151Witness.H_le_eleven n (by omega)
  omega

import OMAStatements.S_opg_grunbaums_conjecture

namespace OMA.GrunbaumCounterexample

open Equiv

/-!
The rotation system is transcribed from Figure 6 of Martin Kochol,
*3-Regular Non 3-Edge-Colorable Graphs with Polyhedral Embeddings in Orientable Surfaces*,
https://doi.org/10.1007/978-3-642-00219-9_31.

Even and odd darts represent the two ends of the same edge. The table `rotation`
rotates the three incident darts of each vertex of Kochol's cubic graph. Its dual
has the required simple triangular embedding. The color obstruction is certified
on two capped 22-vertex pieces and the contracted 26-vertex graph.
-/

private abbrev D := Fin 222
private abbrev Triangle := ℕ × ℕ × ℕ
private abbrev Color := Fin 3
private abbrev Flow := ZMod 2 × ZMod 2
private def rotation : Array (Array D) := #[
  #[80, 128, 1, 142, 3, 130, 5, 8, 82, 10, 84, 12, 86, 70, 13, 73],
  #[132, 18, 153, 20, 134, 64, 21, 66, 63, 208, 25, 196, 27, 30, 65, 79],
  #[76, 34, 78, 50, 35, 85, 37, 52, 39, 42, 198, 44, 219, 46, 200, 54],
  #[32, 81, 36, 57, 40, 87, 77, 59, 49, 83, 53, 89, 16, 74, 61, 194],
  #[22, 29, 71, 68, 75, 31, 14, 23, 0, 88, 62, 67, 48, 47, 33, 69],
  #[72, 56, 7, 51, 9, 38, 11, 58, 15, 55, 136, 92, 138, 94, 124, 96],
  #[114, 98, 126, 100, 148, 133, 131, 139, 103, 141, 105, 123, 107, 151, 109, 149],
  #[111, 155, 95, 154, 115, 118, 145, 147, 119, 122, 137, 108, 93, 143, 97, 150],
  #[2, 90, 6, 144, 60, 146, 19, 113, 129, 121, 91, 104, 125, 106, 4, 140],
  #[102, 117, 101, 120, 99, 112, 152, 110, 127, 17, 116, 135, 202, 158, 204, 160],
  #[190, 162, 180, 164, 192, 166, 214, 199, 197, 205, 169, 207, 171, 189, 173, 217],
  #[175, 215, 177, 221, 161, 220, 181, 184, 211, 213, 185, 188, 203, 174, 159, 209],
  #[163, 216, 24, 156, 28, 210, 41, 212, 45, 179, 195, 187, 157, 170, 191, 172],
  #[26, 206, 168, 183, 167, 186, 165, 178, 218, 176, 193, 43, 182, 201]
]
private def faceLabels : Array (Array ℕ) := #[
  #[0, 1, 2, 1, 3, 1, 4, 1, 4, 5, 4, 6, 4, 7, 0, 7],
  #[8, 9, 8, 10, 8, 4, 11, 4, 12, 8, 13, 8, 14, 8, 14, 11],
  #[15, 14, 15, 16, 5, 16, 6, 16, 17, 16, 17, 18, 17, 19, 17, 14],
  #[20, 15, 15, 5, 6, 17, 17, 20, 1, 15, 7, 17, 0, 8, 16, 8],
  #[8, 11, 11, 0, 11, 16, 4, 0, 20, 0, 0, 16, 14, 20, 16, 14],
  #[1, 20, 5, 1, 6, 5, 7, 6, 20, 7, 0, 21, 0, 22, 0, 3],
  #[0, 10, 0, 23, 0, 24, 21, 4, 22, 4, 2, 4, 9, 4, 23, 4],
  #[24, 4, 10, 3, 24, 3, 24, 21, 9, 21, 9, 2, 3, 22, 23, 10],
  #[0, 2, 3, 4, 9, 0, 4, 10, 21, 2, 22, 21, 2, 22, 2, 3],
  #[3, 21, 9, 24, 24, 23, 23, 9, 9, 10, 10, 24, 16, 25, 16, 26],
  #[16, 13, 16, 19, 16, 27, 16, 28, 25, 14, 26, 14, 12, 14, 18, 14],
  #[27, 14, 28, 14, 19, 13, 28, 13, 28, 25, 18, 25, 18, 12, 13, 26],
  #[27, 19, 16, 12, 13, 14, 18, 16, 14, 19, 25, 12, 26, 25, 12, 26],
  #[12, 13, 13, 25, 18, 28, 28, 27, 27, 18, 18, 19, 19, 28]
]
private def dartRecovery : Array (Array ℕ) := #[
  #[0, 0, 128, 94, 71, 0, 0, 14, 60, 133, 96, 67, 0, 0, 0, 0],
  #[74, 0, 0, 0, 73, 90, 92, 98, 100, 0, 0, 0, 0, 1, 0, 3],
  #[5, 7, 83, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56, 0, 0, 0],
  #[0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 129, 2, 0, 142, 106, 0],
  #[0, 0, 0, 123, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 137],
  #[140, 0, 0, 0, 0, 0, 0, 95, 4, 143, 0, 130, 0, 0, 0, 0],
  #[0, 115, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 144, 124, 0, 117],
  #[0, 0, 0, 0, 70, 6, 107, 131, 0, 8, 10, 12, 21, 109, 134, 23],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 103, 105, 111, 113, 0, 0, 0],
  #[0, 0, 82, 0, 0, 9, 0, 85, 0, 0, 0, 0, 0, 0, 0, 0],
  #[51, 36, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 11, 84, 0, 87, 0, 0, 0, 0, 0, 0, 0, 0, 38, 52],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 13],
  #[0, 86, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58, 0, 0, 89],
  #[0, 0, 0, 0, 0, 0, 0, 0, 61, 0, 0, 0, 20, 0, 0, 0],
  #[0, 16, 18, 64, 25, 27, 29, 0, 63, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 132, 0, 122, 0, 108, 0, 0, 0, 17, 0, 152],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 120, 0, 151, 146, 0, 0],
  #[0, 0, 97, 0, 0, 114, 135, 0, 0, 0, 19, 153, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 127, 154, 0, 0, 0, 0, 66],
  #[0, 0, 0, 22, 0, 0, 0, 65, 0, 0, 0, 0, 0, 31, 0, 68],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 24, 0, 0, 0, 0, 208, 172, 0, 195, 0, 189, 0],
  #[0, 0, 0, 0, 0, 203, 206, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 26, 0, 0, 0, 209, 0, 196, 0, 161, 0, 0, 181, 0, 0, 0],
  #[0, 0, 210, 190, 0, 183, 0, 0, 0, 0, 0, 0, 0, 0, 28, 0],
  #[0, 30, 173, 197, 0, 33, 79, 47, 175, 200, 76, 0, 0, 0, 0, 169],
  #[171, 177, 179, 0, 57, 0, 0, 0, 50, 0, 0, 0, 0, 0, 0, 0],
  #[0, 32, 0, 34, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 0, 0],
  #[75, 0, 0, 0, 0, 37, 39, 0, 62, 0, 0, 69, 194, 160, 78, 35],
  #[0, 41, 199, 162, 0, 0, 0, 0, 0, 156, 158, 164, 166, 0, 0, 0],
  #[0, 0, 0, 53, 59, 0, 0, 0, 0, 0, 0, 46, 0, 40, 0, 42],
  #[44, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 188, 0, 174, 0, 198, 43, 0, 218, 0, 0],
  #[0, 0, 0, 186, 0, 217, 212, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 180, 201, 0, 163, 45, 219, 0, 0, 0, 0, 0, 0],
  #[0, 0, 193, 220, 72, 81, 0, 0, 0, 0, 0, 88, 0, 0, 0, 0],
  #[0, 0, 77, 48, 0, 55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 91, 0, 136, 145, 102, 0, 0, 0, 0, 121, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 139, 0, 119, 0, 0, 0, 0, 93, 0],
  #[141, 125, 104, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 138, 0, 0, 0, 0, 0, 0, 0, 99, 0, 0, 0, 110],
  #[0, 0, 0, 0, 150, 126, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 149, 0, 0, 0, 0, 101, 0, 0, 116, 112, 0, 0, 0],
  #[0, 147, 155, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 118, 0, 148],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 202, 211, 168, 0, 157, 0, 187, 0, 0, 0, 0, 0, 0, 0, 205],
  #[0, 185, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 207, 191],
  #[170, 0, 159, 0, 0, 0, 0, 0, 0, 0, 0, 204, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 176, 0, 165],
  #[0, 216, 192, 0, 0, 0, 0, 0, 0, 0, 0, 215, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 182, 178, 0, 167, 0, 213, 221],
  #[0, 0, 0, 0, 0, 184, 0, 214, 0]
]
private def faceSeeds : List D := [72, 1, 3, 5, 7, 9, 11, 13, 15, 90, 131, 92, 139, 94, 141, 125, 96, 115, 117, 119, 137, 123, 127, 98, 151, 100, 149, 133, 155, 132, 153, 19, 21, 71, 74, 68, 194, 25, 27, 29, 31, 156, 197, 158, 205, 160, 207, 191, 162, 181, 183, 185, 203, 189, 193, 164, 217, 166, 215, 199, 221, 76, 78, 35, 37, 39, 198, 219, 45, 47, 81, 57, 87, 59]
private def rootParents : Array (Array (D × Bool × ℕ)) := #[
  #[(0, false, 0), (0, false, 1), (129, true, 3), (2, false, 4), (143, true, 6), (7, true, 6), (7, false, 6), (83, true, 5), (6, true, 7), (8, false, 8), (8, true, 8), (10, false, 9), (13, false, 9), (15, true, 8), (15, false, 8), (89, true, 7)],
  #[(61, true, 11), (152, true, 11), (19, false, 11), (135, true, 10), (18, true, 12), (23, true, 12), (23, false, 12), (70, true, 11), (195, true, 15), (24, false, 16), (27, false, 16), (29, true, 15), (29, false, 15), (64, true, 14), (31, false, 13), (68, true, 12)],
  #[(49, true, 6), (32, false, 7), (32, true, 7), (34, false, 8), (51, true, 7), (36, false, 8), (84, true, 10), (38, false, 11), (53, true, 10), (40, false, 11), (40, true, 11), (42, false, 12), (42, true, 12), (201, true, 12), (47, false, 10), (76, true, 9)],
  #[(49, false, 6), (57, true, 5), (51, false, 7), (82, true, 6), (53, false, 10), (59, true, 9), (55, false, 7), (88, true, 6), (80, true, 3), (56, false, 4), (59, false, 9), (54, true, 8), (133, true, 9), (60, false, 10), (75, true, 12), (62, false, 13)],
  #[(20, true, 13), (31, true, 13), (67, false, 12), (74, true, 11), (69, false, 11), (78, true, 10), (12, true, 10), (70, false, 11), (81, true, 4), (72, false, 5), (60, true, 10), (69, true, 11), (77, false, 8), (55, true, 7), (35, true, 9), (78, false, 10)],
  #[(1, true, 2), (80, false, 3), (83, false, 5), (56, true, 4), (85, false, 9), (36, true, 8), (13, true, 9), (86, false, 10), (72, true, 5), (88, false, 6), (128, true, 2), (90, false, 3), (90, true, 3), (92, false, 4), (92, true, 4), (94, false, 5)],
  #[(94, true, 5), (96, false, 6), (96, true, 6), (98, false, 7), (98, true, 7), (100, false, 8), (145, true, 8), (105, true, 8), (138, true, 6), (104, false, 7), (140, true, 6), (106, false, 7), (122, true, 8), (108, false, 9), (150, true, 10), (110, false, 11)],
  #[(148, true, 10), (134, true, 11), (97, true, 7), (114, false, 8), (117, false, 10), (144, true, 9), (119, false, 7), (121, true, 6), (121, false, 6), (136, true, 5), (120, true, 7), (106, true, 7), (95, true, 6), (141, true, 7), (99, true, 8), (126, false, 9)],
  #[(0, true, 1), (128, false, 2), (4, true, 7), (130, false, 8), (133, false, 9), (100, true, 8), (135, false, 10), (154, true, 9), (91, true, 4), (136, false, 5), (93, true, 5), (138, false, 6), (142, true, 5), (140, false, 6), (2, true, 4), (142, false, 5)],
  #[(130, true, 8), (119, true, 7), (147, false, 9), (118, true, 8), (101, true, 9), (148, false, 10), (126, true, 9), (108, true, 9), (151, true, 10), (152, false, 11), (114, true, 8), (154, false, 9), (194, true, 14), (156, false, 15), (156, true, 15), (158, false, 16)],
  #[(158, true, 16), (181, true, 17), (163, false, 16), (193, true, 15), (165, false, 16), (215, true, 15), (167, false, 17), (213, true, 16), (169, false, 17), (171, true, 16), (171, false, 16), (173, true, 15), (173, false, 15), (175, true, 14), (175, false, 14), (177, true, 13)],
  #[(177, false, 13), (179, true, 12), (179, false, 12), (200, true, 11), (163, true, 16), (183, true, 16), (221, true, 14), (182, false, 15), (182, true, 15), (184, false, 16), (212, true, 15), (186, false, 16), (186, true, 16), (172, true, 16), (161, true, 18), (207, true, 18)],
  #[(193, false, 15), (219, true, 14), (62, true, 13), (194, false, 14), (26, true, 17), (169, true, 17), (43, true, 13), (198, false, 14), (47, true, 10), (200, false, 11), (157, true, 16), (189, true, 17), (159, true, 17), (168, true, 18), (208, true, 17), (170, true, 17)],
  #[(24, true, 16), (208, false, 17), (211, false, 18), (185, true, 17), (198, true, 14), (212, false, 15), (215, false, 15), (176, true, 14), (192, true, 16), (174, true, 15), (219, false, 14), (45, true, 13), (221, false, 14), (178, true, 13)]
]
private def core1 : List Triangle := [
  (45, 68, 64), (65, 72, 51), (46, 69, 45), (69, 52, 51), (47, 62, 46), (70, 53, 52),
  (62, 71, 70), (48, 57, 47), (57, 77, 58), (58, 59, 72), (59, 73, 60), (68, 60, 61),
  (61, 54, 53), (63, 75, 76), (49, 63, 48), (75, 55, 54), (50, 74, 49), (74, 56, 55),
  (66, 73, 50), (77, 67, 56)
]
private def wires1a : Triangle := (64, 71, 65)
private def wires1b : Triangle := (66, 76, 67)
private def coreInternal1 : List ℕ := [45, 68, 72, 51, 46, 69, 52, 47, 62, 70, 53, 48, 57, 77, 58, 59, 73, 60, 61, 54, 63, 75, 49, 55, 50, 74, 56]
private def coreSearch1 : List Triangle := [
  (46, 69, 45), (47, 62, 46), (69, 52, 51), (65, 72, 51), (62, 71, 70), (70, 53, 52),
  (64, 71, 65), (45, 68, 64), (68, 60, 61), (61, 54, 53), (59, 73, 60), (58, 59, 72),
  (57, 77, 58), (48, 57, 47), (66, 73, 50), (77, 67, 56), (66, 76, 67), (74, 56, 55),
  (50, 74, 49), (49, 63, 48), (63, 75, 76), (75, 55, 54)
]
private def cap1a : List Triangle := [
  (0, 64, 1), (1, 71, 2), (2, 65, 3)
]
private def cap1aBase : Triangle := (0, 3, 111)
private def cap1aInternal : List ℕ := [1, 2]
private def cap1b : List Triangle := [
  (66, 30, 8), (76, 8, 9), (9, 10, 67)
]
private def cap1bBase : Triangle := (30, 10, 111)
private def cap1bInternal : List ℕ := [8, 9]
private def core2 : List Triangle := [
  (78, 101, 97), (98, 105, 84), (79, 102, 78), (102, 85, 84), (80, 95, 79), (103, 86, 85),
  (95, 104, 103), (81, 90, 80), (90, 110, 91), (91, 92, 105), (92, 106, 93), (101, 93, 94),
  (94, 87, 86), (96, 108, 109), (82, 96, 81), (108, 88, 87), (83, 107, 82), (107, 89, 88),
  (99, 106, 83), (110, 100, 89)
]
private def wires2a : Triangle := (97, 104, 98)
private def wires2b : Triangle := (99, 109, 100)
private def coreInternal2 : List ℕ := [78, 101, 105, 84, 79, 102, 85, 80, 95, 103, 86, 81, 90, 110, 91, 92, 106, 93, 94, 87, 96, 108, 82, 88, 83, 107, 89]
private def coreSearch2 : List Triangle := [
  (79, 102, 78), (80, 95, 79), (102, 85, 84), (98, 105, 84), (95, 104, 103), (103, 86, 85),
  (97, 104, 98), (78, 101, 97), (101, 93, 94), (94, 87, 86), (92, 106, 93), (91, 92, 105),
  (90, 110, 91), (81, 90, 80), (99, 106, 83), (110, 100, 89), (99, 109, 100), (107, 89, 88),
  (83, 107, 82), (82, 96, 81), (96, 108, 109), (108, 88, 87)
]
private def cap2a : List Triangle := [
  (97, 12, 31), (12, 104, 13), (13, 98, 14)
]
private def cap2aBase : Triangle := (31, 14, 112)
private def cap2aInternal : List ℕ := [12, 13]
private def cap2b : List Triangle := [
  (99, 20, 21), (109, 21, 22), (22, 23, 100)
]
private def cap2bBase : Triangle := (20, 23, 112)
private def cap2bInternal : List ℕ := [21, 22]
private def baseKeep : List Triangle := [
  (36, 0, 40), (3, 4, 41), (4, 5, 42), (5, 6, 43), (6, 35, 7), (7, 36, 44),
  (10, 32, 11), (35, 11, 33), (37, 31, 30), (34, 37, 33), (14, 15, 32), (15, 39, 34),
  (38, 24, 16), (39, 16, 17), (17, 25, 18), (18, 42, 19), (19, 26, 20), (23, 27, 38),
  (40, 28, 24), (28, 41, 25), (43, 29, 26), (29, 44, 27)
]
private def baseSearch : List Triangle := [
  (15, 39, 34), (34, 37, 33), (37, 31, 30), (30, 10, 111), (31, 14, 112), (14, 15, 32),
  (10, 32, 11), (35, 11, 33), (0, 3, 111), (36, 0, 40), (7, 36, 44), (6, 35, 7),
  (3, 4, 41), (40, 28, 24), (28, 41, 25), (17, 25, 18), (39, 16, 17), (38, 24, 16),
  (18, 42, 19), (4, 5, 42), (5, 6, 43), (19, 26, 20), (43, 29, 26), (20, 23, 112),
  (23, 27, 38), (29, 44, 27)
]

private def alphaFn (x : D) : D := Fin.ofNat 222
  (if x.val % 2 = 0 then x.val + 1 else x.val - 1)

private theorem alpha_inv : ∀ x : D, alphaFn (alphaFn x) = x := by decide +kernel

private def alpha : Perm D where
  toFun := alphaFn
  invFun := alphaFn
  left_inv := alpha_inv
  right_inv := alpha_inv

private def lookup {A : Type} [Inhabited A] (table : Array (Array A)) (i : ℕ) : A :=
  (table[i / 16]!)[i % 16]!

private def rotate (x : D) : D := lookup rotation x.val

private theorem rotate_cube : ∀ x : D, rotate (rotate (rotate x)) = x := by decide +kernel

private def rho : Perm D where
  toFun := rotate
  invFun x := rotate (rotate x)
  left_inv := rotate_cube
  right_inv := rotate_cube

private def sigma : Perm D := rho * alpha

private theorem triangle_cube : ∀ x : D, (sigma * alpha) ((sigma * alpha) ((sigma * alpha) x)) = x := by
  decide +kernel

private theorem triangle_no_fixed : ∀ x : D, (sigma * alpha) x ≠ x := by decide +kernel

private theorem alpha_no_fixed : ∀ x : D, alpha x ≠ x := by decide +kernel

private def label (x : D) : ℕ := lookup faceLabels x.val

private theorem label_rotation : ∀ x : D, label (sigma x) = label x := by decide +kernel

private theorem label_inverse (x : D) : label (sigma⁻¹ x) = label x := by
  simpa using (label_rotation (sigma⁻¹ x)).symm

private theorem label_same_cycle {x y : D} (h : sigma.SameCycle x y) : label x = label y := by
  rcases h with ⟨j, rfl⟩
  induction j using Int.induction_on generalizing x with
  | zero => simp
  | succ j ih =>
    rw [zpow_add_one, Equiv.Perm.mul_apply, ← ih, label_rotation]
  | pred j ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ← ih, label_inverse]

private theorem no_loop_labels : ∀ x : D, label x ≠ label (alpha x) := by decide +kernel

private theorem recover_dart : ∀ x : D, lookup dartRecovery (29 * label x + label (alpha x)) = x.val := by
  decide +kernel

private theorem no_parallel {x y : D} (h : sigma.SameCycle x y)
    (h' : sigma.SameCycle (alpha x) (alpha y)) : x = y := by
  apply Fin.ext
  rw [← recover_dart x, ← recover_dart y, label_same_cycle h, label_same_cycle h']

private def stepPerm (b : Bool) : Perm D := if b then sigma else alpha

private def parentData (x : D) : D × Bool × ℕ := lookup rootParents x.val

private theorem parent_works : ∀ x : D, x ≠ 0 →
    stepPerm (parentData x).2.1 (parentData x).1 = x ∧
    (parentData (parentData x).1).2.2 < (parentData x).2.2 := by
  decide +kernel

private theorem root_route (x : D) :
    ∃ p ∈ Subgroup.closure ({sigma, alpha} : Set (Perm D)), p 0 = x := by
  generalize hv : (parentData x).2.2 = v
  induction v using Nat.strong_induction_on generalizing x with
  | h v ih =>
    by_cases hx : x = 0
    · exact ⟨1, Subgroup.one_mem _, hx.symm⟩
    have hparent := parent_works x hx
    obtain ⟨p, hm, hp⟩ := ih _ (hparent.2.trans_eq hv) (parentData x).1 rfl
    have hs : stepPerm (parentData x).2.1 ∈ Subgroup.closure ({sigma, alpha} : Set (Perm D)) :=
      Subgroup.subset_closure (by
        cases (parentData x).2.1 <;> simp [stepPerm])
    exact ⟨stepPerm (parentData x).2.1 * p, Subgroup.mul_mem _ hs hm, by
      rw [Equiv.Perm.mul_apply, hp, hparent.1]⟩

private theorem connected (x y : D) :
    ∃ g ∈ Subgroup.closure ({sigma, alpha} : Set (Perm D)), g x = y := by
  obtain ⟨p, hp, hx⟩ := root_route x
  obtain ⟨q, hq, hy⟩ := root_route y
  refine ⟨q * p⁻¹, Subgroup.mul_mem _ hq (Subgroup.inv_mem _ hp), ?_⟩
  rw [Equiv.Perm.mul_apply, ← hx]
  change q (p.symm (p 0)) = y
  rwa [Equiv.symm_apply_apply]

private def distinct (q : Color × Color × Color) : Prop :=
  q.1 ≠ q.2.1 ∧ q.2.1 ≠ q.2.2 ∧ q.1 ≠ q.2.2

private instance (q : Color × Color × Color) : Decidable (distinct q) := by
  unfold distinct
  infer_instance

private def value (c : ℕ → Color) (t : Triangle) : Color × Color × Color :=
  (c t.1, c t.2.1, c t.2.2)

private def Valid (c : ℕ → Color) (rows : List Triangle) : Prop :=
  ∀ t ∈ rows, distinct (value c t)

private def possibilities : List (Color × Color × Color) :=
  [(0,1,2), (0,2,1), (1,0,2), (1,2,0), (2,0,1), (2,1,0)]

private theorem possible : ∀ q : Color × Color × Color, distinct q → q ∈ possibilities := by
  decide +kernel

private def agrees (c : ℕ → Color) (assigned : List (ℕ × Color)) : Prop :=
  ∀ p ∈ assigned, c p.1 = p.2

private def accepts : List (ℕ × Color) → ℕ → Color → Bool
  | [], _, _ => true
  | (i,b) :: tail, j, c => if i = j then b == c else accepts tail j c

private theorem accepts_of_agrees (c : ℕ → Color) (assigned : List (ℕ × Color))
    (ha : agrees c assigned) (j : ℕ) : accepts assigned j (c j) = true := by
  induction assigned with
  | nil => rfl
  | cons p tail ih =>
    obtain ⟨i,b⟩ := p
    by_cases h : i = j
    · subst i
      have hp := ha (j,b) List.mem_cons_self
      simp only [accepts, if_true, beq_iff_eq]
      exact hp.symm
    · simp only [accepts, if_neg h]
      exact ih (fun p hp => ha p (List.mem_cons_of_mem _ hp))

private def put (assigned : List (ℕ × Color)) (t : Triangle) (q : Color × Color × Color) :
    List (ℕ × Color) := (t.1,q.1) :: (t.2.1,q.2.1) :: (t.2.2,q.2.2) :: assigned

/-- Branch over the six possible color orders at each cubic vertex. -/
private def search : List Triangle → List (ℕ × Color) → Bool
  | [], _ => true
  | t :: rows, assigned => possibilities.any fun q =>
      accepts assigned t.1 q.1 && accepts assigned t.2.1 q.2.1 &&
        accepts assigned t.2.2 q.2.2 && search rows (put assigned t q)

private theorem search_complete (c : ℕ → Color) (rows : List Triangle)
    (hc : Valid c rows) (assigned : List (ℕ × Color))
    (ha : agrees c assigned) : search rows assigned = true := by
  induction rows generalizing assigned with
  | nil => rfl
  | cons t rows ih =>
    rw [search, List.any_eq_true]
    refine ⟨value c t, possible _ (hc _ List.mem_cons_self), ?_⟩
    have hagree : agrees c (put assigned t (value c t)) := by
      intro p hp
      simp only [put, List.mem_cons] at hp
      rcases hp with h | h | h | h
      · subst p
        rfl
      · subst p
        rfl
      · subst p
        rfl
      · exact ha p h
    simp only [value, accepts_of_agrees c assigned ha, Bool.true_and]
    exact ih (fun r hr => hc r (List.mem_cons_of_mem _ hr)) _ hagree

private def rebase (q : Color × Color × Color) (x : Color) : Color :=
  if x = q.1 then 0 else if x = q.2.1 then 1 else 2

private theorem rebase_inj_check :
    ∀ q, distinct q → ∀ x y : Color, rebase q x = rebase q y → x = y := by
  decide +kernel

private theorem rebase_first :
    ∀ q, distinct q → (rebase q q.1, rebase q q.2.1, rebase q q.2.2) =
      ((0,1,2) : Color × Color × Color) := by
  decide +kernel

private def normalizedSearch : List Triangle → Bool
  | [] => true
  | t :: rows => search rows (put [] t (0,1,2))

private theorem normalized_complete (c : ℕ → Color) (rows : List Triangle)
    (hc : Valid c rows) : normalizedSearch rows = true := by
  cases rows with
  | nil => rfl
  | cons t rows =>
    let d (i : ℕ) := rebase (value c t) (c i)
    have hfirst := hc t List.mem_cons_self
    have hinj : Function.Injective (rebase (value c t)) := rebase_inj_check _ hfirst
    have htail : Valid d rows := by
      intro u hu
      have ⟨h₁,h₂,h₃⟩ := hc u (List.mem_cons_of_mem _ hu)
      exact ⟨fun h => h₁ (hinj h), fun h => h₂ (hinj h), fun h => h₃ (hinj h)⟩
    have heq : value d t = (0,1,2) := rebase_first _ hfirst
    change search rows (put [] t (0,1,2)) = true
    rw [← heq]
    apply search_complete d rows htail
    intro p hp
    simp only [put, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> rfl

private def encode (c : Color) : Flow :=
  if c = 0 then (1,0) else if c = 1 then (0,1) else (1,1)

private theorem color_good :
    ∀ q : Color × Color × Color, distinct q ↔ encode q.1 + encode q.2.1 + encode q.2.2 = 0 := by
  decide +kernel

private theorem encode_ne_zero : ∀ a : Color, encode a ≠ 0 := by decide +kernel

private theorem flow_exists : ∀ v : Flow, v ≠ 0 → ∃ a : Color, encode a = v := by decide +kernel

private theorem flow_double : ∀ v : Flow, v + v = 0 := by decide +kernel

private theorem flow_neg (x : Flow) : -x = x := by
  rw [eq_comm, ← add_eq_zero_iff_eq_neg]
  exact flow_double x

private def triList (t : Triangle) : List ℕ := [t.1,t.2.1,t.2.2]

private theorem sum_incidence (c : ℕ → Color) (rows : List Triangle)
    (hc : Valid c rows) : ((rows.flatMap triList).map fun i => encode (c i)).sum = 0 := by
  induction rows with
  | nil => rfl
  | cons t rows ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append,
      ih (fun r hr => hc r (List.mem_cons_of_mem _ hr)), add_zero]
    have ht := (color_good (value c t)).mp (hc t List.mem_cons_self)
    simpa [triList, value, add_assoc] using ht

private def dup (a : ℕ) : List ℕ := [a,a]

private theorem sum_dup (c : ℕ → Color) (internal : List ℕ) :
    ((internal.flatMap dup).map fun i => encode (c i)).sum = 0 := by
  induction internal with
  | nil => rfl
  | cons t ts ih =>
    simp [dup, ih, flow_double]

/-- Contributions from both incidences of any internal edge cancel. -/
private theorem boundary_sum (c : ℕ → Color) (rows : List Triangle)
    (hc : Valid c rows) (boundary internal : List ℕ)
    (hp : (rows.flatMap triList).Perm (boundary ++ internal.flatMap dup)) :
    (boundary.map fun i => encode (c i)).sum = 0 := by
  have h := (hp.map fun i => encode (c i)).sum_eq
  rw [sum_incidence c rows hc, List.map_append, List.sum_append, sum_dup, add_zero] at h
  exact h.symm

private def flowOn (c : ℕ → Color) (t : Triangle) : Flow :=
  encode (c t.1) + encode (c t.2.1) + encode (c t.2.2)

private theorem capped_obstruction (c : ℕ → Color) (rows test : List Triangle)
    (w₁ w₂ : Triangle) (internal : List ℕ) (hc : Valid c rows)
    (hp : (rows.flatMap triList).Perm (triList w₁ ++ triList w₂ ++ internal.flatMap dup))
    (hsub : ∀ t ∈ test, t = w₁ ∨ t = w₂ ∨ t ∈ rows)
    (hbad : normalizedSearch test = false) :
    ∃ b : Color, encode b = flowOn c w₁ ∧ encode b = flowOn c w₂ := by
  have hsum : flowOn c w₁ + flowOn c w₂ = 0 := by
    have := boundary_sum c rows hc (triList w₁ ++ triList w₂) internal hp
    simpa [triList, flowOn, List.sum_append, add_assoc] using this
  have heq : flowOn c w₁ = flowOn c w₂ := by
    rw [add_eq_zero_iff_eq_neg, flow_neg] at hsum
    exact hsum
  have hnonzero : flowOn c w₁ ≠ 0 := by
    intro hz
    have hc' : Valid c test := by
      intro t ht
      rcases hsub t ht with h | h | h
      · subst t
        exact (color_good _).mpr hz
      · subst t
        exact (color_good _).mpr (heq.symm.trans hz)
      · exact hc t h
    have hdone := normalized_complete c test hc'
    simp [hbad] at hdone
  obtain ⟨b,hb⟩ := flow_exists _ hnonzero
  exact ⟨b,hb,hb.trans heq⟩

private def cover (c : D → Color) (e : ℕ) : Color := c (Fin.ofNat 222 (2*e))

private theorem representative : ∀ x : D,
    Fin.ofNat 222 (2*(x.val/2)) = x ∨ Fin.ofNat 222 (2*(x.val/2)) = alpha x := by
  decide +kernel

private theorem cover_rep (c : D → Color) (ha : ∀ x, c (alpha x) = c x) (x : D) :
    cover c (x.val/2) = c x := by
  unfold cover
  rcases representative x with h | h
  · rw [h]
  · rw [h, ha]

private def dartRow (x : D) : Triangle :=
  (x.val / 2, ((sigma * alpha) x).val / 2,
    ((sigma * alpha) ((sigma * alpha) x)).val / 2)

private def originalRows : List Triangle := faceSeeds.map dartRow

private theorem cover_valid (c : D → Color) (ha : ∀ x, c (alpha x) = c x)
    (ht : ∀ x, c x ≠ c ((sigma * alpha) x) ∧
      c ((sigma * alpha) x) ≠ c ((sigma * alpha) ((sigma * alpha) x)) ∧
      c x ≠ c ((sigma * alpha) ((sigma * alpha) x))) :
    Valid (cover c) originalRows := by
  intro t ht'
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht'
  simpa only [distinct, value, dartRow, cover_rep c ha] using ht x

private theorem cap_promote (c c' : ℕ → Color) (rows : List Triangle) (w t : Triangle)
    (internal : List ℕ) (b : Color) (hc : Valid c rows)
    (hp : (rows.flatMap triList).Perm ([t.1,t.2.1] ++ triList w ++ internal.flatMap dup))
    (hflow : encode b = flowOn c w)
    (h₁ : c' t.1 = c t.1) (h₂ : c' t.2.1 = c t.2.1) (h₃ : c' t.2.2 = b) :
    distinct (value c' t) := by
  have hsum := boundary_sum c rows hc ([t.1,t.2.1] ++ triList w) internal hp
  refine (color_good _).mpr ?_
  change encode (c' t.1) + encode (c' t.2.1) + encode (c' t.2.2) = 0
  rw [h₁,h₂,h₃,hflow]
  simpa [triList, flowOn, List.sum_append, add_assoc] using hsum

private theorem valid_subset {c : ℕ → Color} {rows small : List Triangle}
    (h : Valid c rows) (hs : ∀ t ∈ small, t ∈ rows) : Valid c small := fun t ht => h t (hs t ht)

private theorem capped1_check : normalizedSearch coreSearch1 = false := by decide +kernel

private theorem capped2_check : normalizedSearch coreSearch2 = false := by decide +kernel

private theorem base_check : normalizedSearch baseSearch = false := by decide +kernel

private theorem kept_edges :
    ∀ t ∈ baseKeep, t.1 < 111 ∧ t.2.1 < 111 ∧ t.2.2 < 111 := by decide +kernel

private theorem base_cases :
    ∀ t ∈ baseSearch, t = cap1aBase ∨ t = cap1bBase ∨ t = cap2aBase ∨ t = cap2bBase ∨
      t ∈ baseKeep := by
  decide +kernel

private theorem no_original_color (c : ℕ → Color) (hc : Valid c originalRows) : False := by
  obtain ⟨b₁, h₁a, h₁b⟩ := capped_obstruction c core1 coreSearch1 wires1a wires1b
    coreInternal1 (valid_subset hc (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) capped1_check
  obtain ⟨b₂, h₂a, h₂b⟩ := capped_obstruction c core2 coreSearch2 wires2a wires2b
    coreInternal2 (valid_subset hc (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) capped2_check
  let c' (e : ℕ) := if e = 111 then b₁ else if e = 112 then b₂ else c e
  have stable (e : ℕ) (he : e < 111) : c' e = c e := by
    simp [c', show e ≠ 111 by omega, show e ≠ 112 by omega]
  have h₁a' : distinct (value c' cap1aBase) := by
    apply cap_promote c c' cap1a wires1a cap1aBase cap1aInternal b₁
      (valid_subset hc (by decide +kernel)) (by decide +kernel) h₁a
    · exact stable _ (by decide +kernel)
    · exact stable _ (by decide +kernel)
    · rfl
  have h₁b' : distinct (value c' cap1bBase) := by
    apply cap_promote c c' cap1b wires1b cap1bBase cap1bInternal b₁
      (valid_subset hc (by decide +kernel)) (by decide +kernel) h₁b
    · exact stable _ (by decide +kernel)
    · exact stable _ (by decide +kernel)
    · rfl
  have h₂a' : distinct (value c' cap2aBase) := by
    apply cap_promote c c' cap2a wires2a cap2aBase cap2aInternal b₂
      (valid_subset hc (by decide +kernel)) (by decide +kernel) h₂a
    · exact stable _ (by decide +kernel)
    · exact stable _ (by decide +kernel)
    · rfl
  have h₂b' : distinct (value c' cap2bBase) := by
    apply cap_promote c c' cap2b wires2b cap2bBase cap2bInternal b₂
      (valid_subset hc (by decide +kernel)) (by decide +kernel) h₂b
    · exact stable _ (by decide +kernel)
    · exact stable _ (by decide +kernel)
    · rfl
  have hkeep : Valid c baseKeep := valid_subset hc (by decide +kernel)
  have hbase : Valid c' baseSearch := by
    intro t ht
    rcases base_cases t ht with rfl | rfl | rfl | rfl | hk
    · exact h₁a'
    · exact h₁b'
    · exact h₂a'
    · exact h₂b'
    · obtain ⟨hs₁,hs₂,hs₃⟩ := kept_edges t hk
      simpa only [value, stable _ hs₁, stable _ hs₂, stable _ hs₃] using hkeep t hk
  have hdone := normalized_complete c' baseSearch hbase
  rw [base_check] at hdone
  contradiction

theorem counterexample : ¬ (type_of% @OMA.S_opg_grunbaums_conjecture.main) := by
  intro h
  obtain ⟨c, ha, ht⟩ := h D sigma alpha alpha_inv alpha_no_fixed connected
    triangle_cube triangle_no_fixed
    (fun x hx => no_loop_labels x (label_same_cycle hx)) (fun _ _ => no_parallel)
  exact no_original_color (cover c) (cover_valid c ha ht)

end OMA.GrunbaumCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_grunbaums_conjecture.main) :=
  OMA.GrunbaumCounterexample.counterexample

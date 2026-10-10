/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Corollary12DirectCoverage
public import PseudoPrime.LLS.ResidueCoverageTrees

/-! Direct and divisor coverage routes for the remaining moduli.
Regenerate with generate_corollary12_routes.py --part divisors. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.Corollary12DivisorRoutes

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree0 : BinaryTree (ℕ × ℕ) :=
  (.node (16, 16)
    (.node (10, 30)
      (.node (7, 28) (.node (5, 30) (.node (4, 4) .nil .nil) (.node (6, 6) .nil .nil))
        (.node (9, 18) (.node (8, 16) .nil .nil) .nil))
      (.node (13, 130) (.node (12, 12) (.node (11, 22) .nil .nil) .nil)
        (.node (15, 30) (.node (14, 28) .nil .nil) .nil)))
    (.node (23, 138)
      (.node (20, 20) (.node (18, 18) (.node (17, 34) .nil .nil) (.node (19, 76) .nil .nil))
        (.node (22, 22) (.node (21, 126) .nil .nil) .nil))
      (.node (26, 130) (.node (25, 150) (.node (24, 24) .nil .nil) .nil)
        (.node (28, 28) (.node (27, 108) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree1 : BinaryTree (ℕ × ℕ) :=
  (.node (42, 126)
    (.node (36, 108)
      (.node (33, 132) (.node (31, 124) (.node (30, 30) .nil .nil) (.node (32, 64) .nil .nil))
        (.node (35, 210) (.node (34, 34) .nil .nil) .nil))
      (.node (39, 156) (.node (38, 76) (.node (37, 74) .nil .nil) .nil)
        (.node (41, 82) (.node (40, 120) .nil .nil) .nil)))
    (.node (49, 98)
      (.node (46, 138) (.node (44, 88) (.node (43, 86) .nil .nil) (.node (45, 180) .nil .nil))
        (.node (48, 96) (.node (47, 94) .nil .nil) .nil))
      (.node (52, 104) (.node (51, 204) (.node (50, 150) .nil .nil) .nil)
        (.node (54, 108) (.node (53, 106) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree2 : BinaryTree (ℕ × ℕ) :=
  .node (29, 174) routeSubtree0 routeSubtree1

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree3 : BinaryTree (ℕ × ℕ) :=
  (.node (68, 204)
    (.node (62, 124)
      (.node (59, 1062) (.node (57, 114) (.node (56, 168) .nil .nil) (.node (58, 174) .nil .nil))
        (.node (61, 122) (.node (60, 120) .nil .nil) .nil))
      (.node (65, 130) (.node (64, 64) (.node (63, 126) .nil .nil) .nil)
        (.node (67, 1206) (.node (66, 132) .nil .nil) .nil)))
    (.node (75, 150)
      (.node (72, 144) (.node (70, 210) (.node (69, 138) .nil .nil) (.node (71, 142) .nil .nil))
        (.node (74, 74) (.node (73, 146) .nil .nil) .nil))
      (.node (78, 156) (.node (77, 154) (.node (76, 76) .nil .nil) .nil)
        (.node (80, 80) (.node (79, 1422) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree4 : BinaryTree (ℕ × ℕ) :=
  (.node (94, 94)
    (.node (88, 88)
      (.node (85, 170) (.node (83, 1660) (.node (82, 82) .nil .nil) (.node (84, 168) .nil .nil))
        (.node (87, 174) (.node (86, 86) .nil .nil) .nil))
      (.node (91, 182) (.node (90, 180) (.node (89, 1068) .nil .nil) .nil)
        (.node (93, 186) (.node (92, 92) .nil .nil) .nil)))
    (.node (101, 808)
      (.node (98, 98) (.node (96, 96) (.node (95, 190) .nil .nil) (.node (97, 1164) .nil .nil))
        (.node (100, 100) (.node (99, 198) .nil .nil) .nil))
      (.node (104, 104) (.node (103, 1236) (.node (102, 204) .nil .nil) .nil)
        (.node (106, 106) (.node (105, 210) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree5 : BinaryTree (ℕ × ℕ) :=
  .node (81, 162) routeSubtree3 routeSubtree4

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree6 : BinaryTree (ℕ × ℕ) :=
  .node (55, 110) routeSubtree2 routeSubtree5

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree7 : BinaryTree (ℕ × ℕ) :=
  (.node (120, 120)
    (.node (114, 114)
      (.node (111, 1332)
        (.node (109, 872) (.node (108, 108) .nil .nil) (.node (110, 110) .nil .nil))
        (.node (113, 1130) (.node (112, 112) .nil .nil) .nil))
      (.node (117, 1404) (.node (116, 116) (.node (115, 1150) .nil .nil) .nil)
        (.node (119, 1666) (.node (118, 1062) .nil .nil) .nil)))
    (.node (127, 1016)
      (.node (124, 124)
        (.node (122, 122) (.node (121, 1210) .nil .nil) (.node (123, 1722) .nil .nil))
        (.node (126, 126) (.node (125, 1500) .nil .nil) .nil))
      (.node (130, 130) (.node (129, 1806) (.node (128, 512) .nil .nil) .nil)
        (.node (132, 132) (.node (131, 1048) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree8 : BinaryTree (ℕ × ℕ) :=
  (.node (146, 146)
    (.node (140, 140)
      (.node (137, 1644)
        (.node (135, 1080) (.node (134, 1206) .nil .nil) (.node (136, 136) .nil .nil))
        (.node (139, 1112) (.node (138, 138) .nil .nil) .nil))
      (.node (143, 1716) (.node (142, 142) (.node (141, 1128) .nil .nil) .nil)
        (.node (145, 1740) (.node (144, 144) .nil .nil) .nil)))
    (.node (153, 1224)
      (.node (150, 150)
        (.node (148, 1332) (.node (147, 1176) .nil .nil) (.node (149, 1490) .nil .nil))
        (.node (152, 1368) (.node (151, 1510) .nil .nil) .nil))
      (.node (156, 156) (.node (155, 1240) (.node (154, 154) .nil .nil) .nil)
        (.node (158, 1422) (.node (157, 1256) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree9 : BinaryTree (ℕ × ℕ) :=
  .node (133, 3990) routeSubtree7 routeSubtree8

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree10 : BinaryTree (ℕ × ℕ) :=
  (.node (172, 1204)
    (.node (166, 1660)
      (.node (163, 1630)
        (.node (161, 1288) (.node (160, 1120) .nil .nil) (.node (162, 162) .nil .nil))
        (.node (165, 1650) (.node (164, 1148) .nil .nil) .nil))
      (.node (169, 1690) (.node (168, 168) (.node (167, 1670) .nil .nil) .nil)
        (.node (171, 1368) (.node (170, 170) .nil .nil) .nil)))
    (.node (179, 1074)
      (.node (176, 704)
        (.node (174, 174) (.node (173, 1730) .nil .nil) (.node (175, 1400) .nil .nil))
        (.node (178, 1068) (.node (177, 1062) .nil .nil) .nil))
      (.node (182, 182) (.node (181, 1086) (.node (180, 180) .nil .nil) .nil)
        (.node (184, 736) (.node (183, 1098) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree11 : BinaryTree (ℕ × ℕ) :=
  (.node (198, 198)
    (.node (192, 768)
      (.node (189, 1134)
        (.node (187, 2244) (.node (186, 186) .nil .nil) (.node (188, 752) .nil .nil))
        (.node (191, 764) (.node (190, 190) .nil .nil) .nil))
      (.node (195, 1950) (.node (194, 1164) (.node (193, 772) .nil .nil) .nil)
        (.node (197, 1182) (.node (196, 784) .nil .nil) .nil)))
    (.node (205, 1640)
      (.node (202, 808)
        (.node (200, 1200) (.node (199, 1194) .nil .nil) (.node (201, 1206) .nil .nil))
        (.node (204, 204) (.node (203, 1624) .nil .nil) .nil))
      (.node (208, 832) (.node (207, 1242) (.node (206, 1236) .nil .nil) .nil)
        (.node (210, 210) (.node (209, 2508) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree12 : BinaryTree (ℕ × ℕ) :=
  .node (185, 2220) routeSubtree10 routeSubtree11

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree13 : BinaryTree (ℕ × ℕ) :=
  .node (159, 1272) routeSubtree9 routeSubtree12

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree14 : BinaryTree (ℕ × ℕ) :=
  .node (107, 856) routeSubtree6 routeSubtree13

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree15 : BinaryTree (ℕ × ℕ) :=
  (.node (224, 1120)
    (.node (218, 872)
      (.node (215, 1720)
        (.node (213, 1704) (.node (212, 1272) .nil .nil) (.node (214, 856) .nil .nil))
        (.node (217, 2170) (.node (216, 1080) .nil .nil) .nil))
      (.node (221, 2210) (.node (220, 1980) (.node (219, 1752) .nil .nil) .nil)
        (.node (223, 1338) (.node (222, 1332) .nil .nil) .nil)))
    (.node (231, 1848)
      (.node (228, 1368)
        (.node (226, 1130) (.node (225, 1800) .nil .nil) (.node (227, 908) .nil .nil))
        (.node (230, 1150) (.node (229, 1374) .nil .nil) .nil))
      (.node (234, 1404) (.node (233, 932) (.node (232, 1160) .nil .nil) .nil)
        (.node (236, 1416) (.node (235, 2820) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree16 : BinaryTree (ℕ × ℕ) :=
  (.node (250, 1500)
    (.node (244, 1464)
      (.node (241, 1446)
        (.node (239, 956) (.node (238, 1666) .nil .nil) (.node (240, 1200) .nil .nil))
        (.node (243, 972) (.node (242, 1210) .nil .nil) .nil))
      (.node (247, 1976) (.node (246, 1722) (.node (245, 2940) .nil .nil) .nil)
        (.node (249, 2490) (.node (248, 992) .nil .nil) .nil)))
    (.node (257, 1542)
      (.node (254, 1016)
        (.node (252, 1512) (.node (251, 1004) .nil .nil) (.node (253, 2024) .nil .nil))
        (.node (256, 512) (.node (255, 2040) .nil .nil) .nil))
      (.node (260, 1300) (.node (259, 2072) (.node (258, 1806) .nil .nil) .nil)
        (.node (262, 1048) (.node (261, 1566) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree17 : BinaryTree (ℕ × ℕ) :=
  .node (237, 1422) routeSubtree15 routeSubtree16

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree18 : BinaryTree (ℕ × ℕ) :=
  (.node (276, 1104)
    (.node (270, 1080)
      (.node (267, 1068)
        (.node (265, 3180) (.node (264, 1056) .nil .nil) (.node (266, 3990) .nil .nil))
        (.node (269, 1614) (.node (268, 1072) .nil .nil) .nil))
      (.node (273, 2184) (.node (272, 1632) (.node (271, 1626) .nil .nil) .nil)
        (.node (275, 1650) (.node (274, 1644) .nil .nil) .nil)))
    (.node (283, 1698)
      (.node (280, 1120)
        (.node (278, 1112) (.node (277, 1662) .nil .nil) (.node (279, 1116) .nil .nil))
        (.node (282, 1128) (.node (281, 1686) .nil .nil) .nil))
      (.node (286, 1716) (.node (285, 1710) (.node (284, 1704) .nil .nil) .nil)
        (.node (288, 864) (.node (287, 1148) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree19 : BinaryTree (ℕ × ℕ) :=
  (.node (302, 1510)
    (.node (296, 1184)
      (.node (293, 1172)
        (.node (291, 1164) (.node (290, 1740) .nil .nil) (.node (292, 1168) .nil .nil))
        (.node (295, 1180) (.node (294, 1176) .nil .nil) .nil))
      (.node (299, 1196) (.node (298, 1490) (.node (297, 1188) .nil .nil) .nil)
        (.node (301, 1806) (.node (300, 1200) .nil .nil) .nil)))
    (.node (309, 1236)
      (.node (306, 1224)
        (.node (304, 1216) (.node (303, 1818) .nil .nil) (.node (305, 1220) .nil .nil))
        (.node (308, 1848) (.node (307, 1842) .nil .nil) .nil))
      (.node (312, 1248) (.node (311, 1244) (.node (310, 1240) .nil .nil) .nil)
        (.node (314, 1256) (.node (313, 1252) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree20 : BinaryTree (ℕ × ℕ) :=
  .node (289, 1156) routeSubtree18 routeSubtree19

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree21 : BinaryTree (ℕ × ℕ) :=
  .node (263, 1052) routeSubtree17 routeSubtree20

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree22 : BinaryTree (ℕ × ℕ) :=
  (.node (328, 1640)
    (.node (322, 1288)
      (.node (319, 1276)
        (.node (317, 1902) (.node (316, 1580) .nil .nil) (.node (318, 1272) .nil .nil))
        (.node (321, 1284) (.node (320, 1280) .nil .nil) .nil))
      (.node (325, 1950) (.node (324, 972) (.node (323, 1938) .nil .nil) .nil)
        (.node (327, 1308) (.node (326, 1630) .nil .nil) .nil)))
    (.node (335, 2010)
      (.node (332, 1660)
        (.node (330, 1650) (.node (329, 1974) .nil .nil) (.node (331, 1986) .nil .nil))
        (.node (334, 1670) (.node (333, 1332) .nil .nil) .nil))
      (.node (338, 1690) (.node (337, 2022) (.node (336, 1680) .nil .nil) .nil)
        (.node (340, 2040) (.node (339, 1356) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree23 : BinaryTree (ℕ × ℕ) :=
  (.node (354, 1062)
    (.node (348, 1740)
      (.node (345, 2070)
        (.node (343, 2058) (.node (342, 1368) .nil .nil) (.node (344, 1720) .nil .nil))
        (.node (347, 2082) (.node (346, 1730) .nil .nil) .nil))
      (.node (351, 1404) (.node (350, 1400) (.node (349, 2094) .nil .nil) .nil)
        (.node (353, 706) (.node (352, 704) .nil .nil) .nil)))
    (.node (361, 722)
      (.node (358, 1074)
        (.node (356, 1068) (.node (355, 2130) .nil .nil) (.node (357, 2142) .nil .nil))
        (.node (360, 1080) (.node (359, 718) .nil .nil) .nil))
      (.node (364, 2184) (.node (363, 1452) (.node (362, 1086) .nil .nil) .nil)
        (.node (366, 1098) (.node (365, 2190) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree24 : BinaryTree (ℕ × ℕ) :=
  .node (341, 1364) routeSubtree22 routeSubtree23

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree25 : BinaryTree (ℕ × ℕ) :=
  (.node (380, 2280)
    (.node (374, 2244)
      (.node (371, 1484)
        (.node (369, 1476) (.node (368, 736) .nil .nil) (.node (370, 2220) .nil .nil))
        (.node (373, 746) (.node (372, 1116) .nil .nil) .nil))
      (.node (377, 1508) (.node (376, 752) (.node (375, 1500) .nil .nil) .nil)
        (.node (379, 758) (.node (378, 1134) .nil .nil) .nil)))
    (.node (387, 1548)
      (.node (384, 768)
        (.node (382, 764) (.node (381, 1524) .nil .nil) (.node (383, 766) .nil .nil))
        (.node (386, 772) (.node (385, 4620) .nil .nil) .nil))
      (.node (390, 1950) (.node (389, 778) (.node (388, 1164) .nil .nil) .nil)
        (.node (392, 784) (.node (391, 2346) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree26 : BinaryTree (ℕ × ℕ) :=
  (.node (406, 1624)
    (.node (400, 1200)
      (.node (397, 794)
        (.node (395, 1580) (.node (394, 1182) .nil .nil) (.node (396, 1188) .nil .nil))
        (.node (399, 3990) (.node (398, 1194) .nil .nil) .nil))
      (.node (403, 2418) (.node (402, 1206) (.node (401, 802) .nil .nil) .nil)
        (.node (405, 1620) (.node (404, 808) .nil .nil) .nil)))
    (.node (412, 1236)
      (.node (409, 818) (.node (408, 1224) (.node (407, 2442) .nil .nil) .nil)
        (.node (411, 1644) (.node (410, 1640) .nil .nil) .nil))
      (.node (415, 1660) (.node (414, 1242) (.node (413, 1652) .nil .nil) .nil)
        (.node (417, 1668) (.node (416, 832) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree27 : BinaryTree (ℕ × ℕ) :=
  .node (393, 1572) routeSubtree25 routeSubtree26

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree28 : BinaryTree (ℕ × ℕ) :=
  .node (367, 734) routeSubtree24 routeSubtree27

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree29 : BinaryTree (ℕ × ℕ) :=
  .node (315, 1890) routeSubtree21 routeSubtree28

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree30 : BinaryTree (ℕ × ℕ) :=
  .node (211, 844) routeSubtree14 routeSubtree29

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree31 : BinaryTree (ℕ × ℕ) :=
  (.node (431, 862)
    (.node (425, 1700)
      (.node (422, 844)
        (.node (420, 1680) (.node (419, 838) .nil .nil) (.node (421, 842) .nil .nil))
        (.node (424, 1272) (.node (423, 1692) .nil .nil) .nil))
      (.node (428, 856) (.node (427, 2562) (.node (426, 1704) .nil .nil) .nil)
        (.node (430, 1720) (.node (429, 1716) .nil .nil) .nil)))
    (.node (438, 1752)
      (.node (435, 1740)
        (.node (433, 866) (.node (432, 864) .nil .nil) (.node (434, 2170) .nil .nil))
        (.node (437, 1748) (.node (436, 872) .nil .nil) .nil))
      (.node (441, 1764) (.node (440, 1760) (.node (439, 878) .nil .nil) .nil)
        (.node (443, 886) (.node (442, 2210) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree32 : BinaryTree (ℕ × ℕ) :=
  (.node (457, 914)
    (.node (451, 1804)
      (.node (448, 1344)
        (.node (446, 1338) (.node (445, 1780) .nil .nil) (.node (447, 1788) .nil .nil))
        (.node (450, 1800) (.node (449, 898) .nil .nil) .nil))
      (.node (454, 908) (.node (453, 1812) (.node (452, 904) .nil .nil) .nil)
        (.node (456, 1368) (.node (455, 5460) .nil .nil) .nil)))
    (.node (464, 1392)
      (.node (461, 922)
        (.node (459, 1836) (.node (458, 1374) .nil .nil) (.node (460, 2760) .nil .nil))
        (.node (463, 926) (.node (462, 1848) .nil .nil) .nil))
      (.node (467, 934) (.node (466, 932) (.node (465, 2790) .nil .nil) .nil)
        (.node (469, 1876) (.node (468, 1404) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree33 : BinaryTree (ℕ × ℕ) :=
  .node (444, 1332) routeSubtree31 routeSubtree32

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree34 : BinaryTree (ℕ × ℕ) :=
  (.node (483, 1932)
    (.node (477, 1908)
      (.node (474, 1422)
        (.node (472, 1416) (.node (471, 1884) .nil .nil) (.node (473, 1892) .nil .nil))
        (.node (476, 2856) (.node (475, 2850) .nil .nil) .nil))
      (.node (480, 1440) (.node (479, 958) (.node (478, 956) .nil .nil) .nil)
        (.node (482, 1446) (.node (481, 1924) .nil .nil) .nil)))
    (.node (490, 2940)
      (.node (487, 974)
        (.node (485, 2910) (.node (484, 968) .nil .nil) (.node (486, 972) .nil .nil))
        (.node (489, 1956) (.node (488, 1464) .nil .nil) .nil))
      (.node (493, 1972) (.node (492, 1476) (.node (491, 982) .nil .nil) .nil)
        (.node (495, 1980) (.node (494, 1976) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree35 : BinaryTree (ℕ × ℕ) :=
  (.node (509, 1018)
    (.node (503, 1006)
      (.node (500, 1500)
        (.node (498, 2490) (.node (497, 1988) .nil .nil) (.node (499, 998) .nil .nil))
        (.node (502, 1004) (.node (501, 2004) .nil .nil) .nil))
      (.node (506, 2024) (.node (505, 3030) (.node (504, 1512) .nil .nil) .nil)
        (.node (508, 1016) (.node (507, 2028) .nil .nil) .nil)))
    (.node (516, 1548)
      (.node (513, 2052)
        (.node (511, 3066) (.node (510, 2040) .nil .nil) (.node (512, 512) .nil .nil))
        (.node (515, 2060) (.node (514, 1542) .nil .nil) .nil))
      (.node (519, 2076) (.node (518, 2072) (.node (517, 3102) .nil .nil) .nil)
        (.node (521, 1042) (.node (520, 3120) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree36 : BinaryTree (ℕ × ℕ) :=
  .node (496, 992) routeSubtree34 routeSubtree35

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree37 : BinaryTree (ℕ × ℕ) :=
  .node (470, 2820) routeSubtree33 routeSubtree36

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree38 : BinaryTree (ℕ × ℕ) :=
  (.node (535, 3210)
    (.node (529, 1058)
      (.node (526, 1052)
        (.node (524, 1048) (.node (523, 1046) .nil .nil) (.node (525, 2100) .nil .nil))
        (.node (528, 1056) (.node (527, 3162) .nil .nil) .nil))
      (.node (532, 2660) (.node (531, 1062) (.node (530, 3180) .nil .nil) .nil)
        (.node (534, 1068) (.node (533, 3198) .nil .nil) .nil)))
    (.node (542, 1626)
      (.node (539, 3234)
        (.node (537, 1074) (.node (536, 1072) .nil .nil) (.node (538, 1614) .nil .nil))
        (.node (541, 1082) (.node (540, 1080) .nil .nil) .nil))
      (.node (545, 3270) (.node (544, 1632) (.node (543, 1086) .nil .nil) .nil)
        (.node (547, 1094) (.node (546, 2184) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree39 : BinaryTree (ℕ × ℕ) :=
  (.node (561, 2244)
    (.node (555, 2220)
      (.node (552, 1104)
        (.node (550, 1650) (.node (549, 1098) .nil .nil) (.node (551, 1102) .nil .nil))
        (.node (554, 1662) (.node (553, 1106) .nil .nil) .nil))
      (.node (558, 1116) (.node (557, 1114) (.node (556, 1112) .nil .nil) .nil)
        (.node (560, 1120) (.node (559, 1118) .nil .nil) .nil)))
    (.node (568, 1704)
      (.node (565, 1130)
        (.node (563, 1126) (.node (562, 1686) .nil .nil) (.node (564, 1128) .nil .nil))
        (.node (567, 1134) (.node (566, 1698) .nil .nil) .nil))
      (.node (571, 1142) (.node (570, 1710) (.node (569, 1138) .nil .nil) .nil)
        (.node (573, 1146) (.node (572, 1716) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree40 : BinaryTree (ℕ × ℕ) :=
  .node (548, 1644) routeSubtree38 routeSubtree39

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree41 : BinaryTree (ℕ × ℕ) :=
  (.node (587, 1174)
    (.node (581, 1162)
      (.node (578, 1156)
        (.node (576, 1152) (.node (575, 1150) .nil .nil) (.node (577, 1154) .nil .nil))
        (.node (580, 1740) (.node (579, 1158) .nil .nil) .nil))
      (.node (584, 1168) (.node (583, 1166) (.node (582, 1164) .nil .nil) .nil)
        (.node (586, 1172) (.node (585, 2340) .nil .nil) .nil)))
    (.node (594, 1188)
      (.node (591, 1182)
        (.node (589, 1178) (.node (588, 1176) .nil .nil) (.node (590, 1180) .nil .nil))
        (.node (593, 1186) (.node (592, 1184) .nil .nil) .nil))
      (.node (597, 1194) (.node (596, 1788) (.node (595, 2380) .nil .nil) .nil)
        (.node (599, 1198) (.node (598, 1196) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree42 : BinaryTree (ℕ × ℕ) :=
  (.node (613, 1226)
    (.node (607, 1214)
      (.node (604, 1812)
        (.node (602, 1806) (.node (601, 1202) .nil .nil) (.node (603, 1206) .nil .nil))
        (.node (606, 1818) (.node (605, 1210) .nil .nil) .nil))
      (.node (610, 1220) (.node (609, 2436) (.node (608, 1216) .nil .nil) .nil)
        (.node (612, 1224) (.node (611, 1222) .nil .nil) .nil)))
    (.node (619, 1238)
      (.node (616, 1848) (.node (615, 2460) (.node (614, 1842) .nil .nil) .nil)
        (.node (618, 1236) (.node (617, 1234) .nil .nil) .nil))
      (.node (622, 1244) (.node (621, 1242) (.node (620, 1240) .nil .nil) .nil)
        (.node (624, 1248) (.node (623, 1246) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree43 : BinaryTree (ℕ × ℕ) :=
  .node (600, 1200) routeSubtree41 routeSubtree42

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree44 : BinaryTree (ℕ × ℕ) :=
  .node (574, 1148) routeSubtree40 routeSubtree43

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree45 : BinaryTree (ℕ × ℕ) :=
  .node (522, 1566) routeSubtree37 routeSubtree44

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree46 : BinaryTree (ℕ × ℕ) :=
  (.node (638, 1276)
    (.node (632, 1896)
      (.node (629, 1258)
        (.node (627, 2508) (.node (626, 1252) .nil .nil) (.node (628, 1256) .nil .nil))
        (.node (631, 1262) (.node (630, 1890) .nil .nil) .nil))
      (.node (635, 1270) (.node (634, 1902) (.node (633, 1266) .nil .nil) .nil)
        (.node (637, 1274) (.node (636, 1272) .nil .nil) .nil)))
    (.node (645, 2580)
      (.node (642, 1284)
        (.node (640, 1280) (.node (639, 1278) .nil .nil) (.node (641, 1282) .nil .nil))
        (.node (644, 1288) (.node (643, 1286) .nil .nil) .nil))
      (.node (648, 1296) (.node (647, 1294) (.node (646, 1938) .nil .nil) .nil)
        (.node (650, 1950) (.node (649, 1298) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree47 : BinaryTree (ℕ × ℕ) :=
  (.node (664, 1992)
    (.node (658, 1974)
      (.node (655, 1310)
        (.node (653, 653) (.node (652, 1956) .nil .nil) (.node (654, 1308) .nil .nil))
        (.node (657, 1314) (.node (656, 1968) .nil .nil) .nil))
      (.node (661, 661) (.node (660, 1980) (.node (659, 659) .nil .nil) .nil)
        (.node (663, 2652) (.node (662, 1986) .nil .nil) .nil)))
    (.node (671, 1342)
      (.node (668, 2004)
        (.node (666, 1332) (.node (665, 3990) .nil .nil) (.node (667, 1334) .nil .nil))
        (.node (670, 2010) (.node (669, 1338) .nil .nil) .nil))
      (.node (674, 2022) (.node (673, 673) (.node (672, 1344) .nil .nil) .nil)
        (.node (676, 2028) (.node (675, 1350) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree48 : BinaryTree (ℕ × ℕ) :=
  .node (651, 2604) routeSubtree46 routeSubtree47

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree49 : BinaryTree (ℕ × ℕ) :=
  (.node (690, 2070)
    (.node (684, 1368)
      (.node (681, 1362)
        (.node (679, 1358) (.node (678, 1356) .nil .nil) (.node (680, 2040) .nil .nil))
        (.node (683, 683) (.node (682, 1364) .nil .nil) .nil))
      (.node (687, 1374) (.node (686, 2058) (.node (685, 1370) .nil .nil) .nil)
        (.node (689, 1378) (.node (688, 2064) .nil .nil) .nil)))
    (.node (697, 1394)
      (.node (694, 2082)
        (.node (692, 2076) (.node (691, 691) .nil .nil) (.node (693, 2772) .nil .nil))
        (.node (696, 1392) (.node (695, 1390) .nil .nil) .nil))
      (.node (700, 1400) (.node (699, 1398) (.node (698, 2094) .nil .nil) .nil)
        (.node (702, 1404) (.node (701, 701) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree50 : BinaryTree (ℕ × ℕ) :=
  (.node (716, 716)
    (.node (710, 2130)
      (.node (707, 1414)
        (.node (705, 2820) (.node (704, 704) .nil .nil) (.node (706, 706) .nil .nil))
        (.node (709, 709) (.node (708, 1416) .nil .nil) .nil))
      (.node (713, 1426) (.node (712, 712) (.node (711, 1422) .nil .nil) .nil)
        (.node (715, 4290) (.node (714, 2142) .nil .nil) .nil)))
    (.node (723, 1446)
      (.node (720, 1440)
        (.node (718, 718) (.node (717, 1434) .nil .nil) (.node (719, 719) .nil .nil))
        (.node (722, 722) (.node (721, 1442) .nil .nil) .nil))
      (.node (726, 1452) (.node (725, 1450) (.node (724, 724) .nil .nil) .nil)
        (.node (728, 2184) (.node (727, 727) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree51 : BinaryTree (ℕ × ℕ) :=
  .node (703, 1406) routeSubtree49 routeSubtree50

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree52 : BinaryTree (ℕ × ℕ) :=
  .node (677, 677) routeSubtree48 routeSubtree51

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree53 : BinaryTree (ℕ × ℕ) :=
  (.node (742, 1484)
    (.node (736, 736)
      (.node (733, 733)
        (.node (731, 1462) (.node (730, 2190) .nil .nil) (.node (732, 1464) .nil .nil))
        (.node (735, 2940) (.node (734, 734) .nil .nil) .nil))
      (.node (739, 739) (.node (738, 1476) (.node (737, 1474) .nil .nil) .nil)
        (.node (741, 2964) (.node (740, 2220) .nil .nil) .nil)))
    (.node (749, 1498)
      (.node (746, 746)
        (.node (744, 1488) (.node (743, 743) .nil .nil) (.node (745, 1490) .nil .nil))
        (.node (748, 2244) (.node (747, 1494) .nil .nil) .nil))
      (.node (752, 752) (.node (751, 751) (.node (750, 1500) .nil .nil) .nil)
        (.node (754, 1508) (.node (753, 1506) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree54 : BinaryTree (ℕ × ℕ) :=
  (.node (768, 768)
    (.node (762, 1524)
      (.node (759, 3036)
        (.node (757, 757) (.node (756, 1512) .nil .nil) (.node (758, 758) .nil .nil))
        (.node (761, 761) (.node (760, 2280) .nil .nil) .nil))
      (.node (765, 3060) (.node (764, 764) (.node (763, 1526) .nil .nil) .nil)
        (.node (767, 1534) (.node (766, 766) .nil .nil) .nil)))
    (.node (775, 1550)
      (.node (772, 772)
        (.node (770, 4620) (.node (769, 769) .nil .nil) (.node (771, 1542) .nil .nil))
        (.node (774, 1548) (.node (773, 773) .nil .nil) .nil))
      (.node (778, 778) (.node (777, 3108) (.node (776, 776) .nil .nil) .nil)
        (.node (780, 2340) (.node (779, 1558) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree55 : BinaryTree (ℕ × ℕ) :=
  .node (755, 1510) routeSubtree53 routeSubtree54

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree56 : BinaryTree (ℕ × ℕ) :=
  (.node (794, 794)
    (.node (788, 788)
      (.node (785, 1570)
        (.node (783, 1566) (.node (782, 2346) .nil .nil) (.node (784, 784) .nil .nil))
        (.node (787, 787) (.node (786, 1572) .nil .nil) .nil))
      (.node (791, 1582) (.node (790, 1580) (.node (789, 1578) .nil .nil) .nil)
        (.node (793, 1586) (.node (792, 1584) .nil .nil) .nil)))
    (.node (801, 1602)
      (.node (798, 3990)
        (.node (796, 796) (.node (795, 3180) .nil .nil) (.node (797, 797) .nil .nil))
        (.node (800, 800) (.node (799, 1598) .nil .nil) .nil))
      (.node (804, 1608) (.node (803, 1606) (.node (802, 802) .nil .nil) .nil)
        (.node (806, 2418) (.node (805, 3220) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree57 : BinaryTree (ℕ × ℕ) :=
  (.node (824, 824)
    (.node (816, 1632)
      (.node (813, 1626)
        (.node (810, 1620) (.node (808, 808) .nil .nil) (.node (812, 1624) .nil .nil))
        (.node (815, 1630) (.node (814, 2442) .nil .nil) .nil))
      (.node (819, 3276) (.node (818, 818) (.node (817, 1634) .nil .nil) .nil)
        (.node (822, 1644) (.node (820, 1640) .nil .nil) .nil)))
    (.node (832, 832)
      (.node (828, 1656) (.node (826, 1652) (.node (825, 1650) .nil .nil) .nil)
        (.node (831, 1662) (.node (830, 1660) .nil .nil) .nil))
      (.node (835, 1670) (.node (834, 1668) (.node (833, 1666) .nil .nil) .nil)
        (.node (837, 1674) (.node (836, 2508) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree58 : BinaryTree (ℕ × ℕ) :=
  .node (807, 1614) routeSubtree56 routeSubtree57

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree59 : BinaryTree (ℕ × ℕ) :=
  .node (781, 1562) routeSubtree55 routeSubtree58

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree60 : BinaryTree (ℕ × ℕ) :=
  .node (729, 729) routeSubtree52 routeSubtree59

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree61 : BinaryTree (ℕ × ℕ) :=
  .node (625, 1250) routeSubtree45 routeSubtree60

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree62 : BinaryTree (ℕ × ℕ) :=
  .node (418, 2508) routeSubtree30 routeSubtree61

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree63 : BinaryTree (ℕ × ℕ) :=
  (.node (854, 2562)
    (.node (847, 1694)
      (.node (844, 844)
        (.node (842, 842) (.node (840, 1680) .nil .nil) (.node (843, 1686) .nil .nil))
        (.node (846, 1692) (.node (845, 1690) .nil .nil) .nil))
      (.node (850, 1700) (.node (849, 1698) (.node (848, 848) .nil .nil) .nil)
        (.node (852, 1704) (.node (851, 1702) .nil .nil) .nil)))
    (.node (864, 864)
      (.node (860, 1720)
        (.node (856, 856) (.node (855, 1710) .nil .nil) (.node (858, 1716) .nil .nil))
        (.node (862, 862) (.node (861, 1722) .nil .nil) .nil))
      (.node (867, 1734) (.node (866, 866) (.node (865, 1730) .nil .nil) .nil)
        (.node (869, 1738) (.node (868, 1736) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree64 : BinaryTree (ℕ × ℕ) :=
  (.node (886, 886)
    (.node (878, 878)
      (.node (874, 1748)
        (.node (872, 872) (.node (871, 1742) .nil .nil) (.node (873, 1746) .nil .nil))
        (.node (876, 1752) (.node (875, 1750) .nil .nil) .nil))
      (.node (882, 1764) (.node (880, 1760) (.node (879, 1758) .nil .nil) .nil)
        (.node (885, 1770) (.node (884, 1768) .nil .nil) .nil)))
    (.node (894, 1788)
      (.node (891, 1782)
        (.node (889, 1778) (.node (888, 1776) .nil .nil) (.node (890, 1780) .nil .nil))
        (.node (893, 1786) (.node (892, 892) .nil .nil) .nil))
      (.node (897, 1794) (.node (896, 896) (.node (895, 1790) .nil .nil) .nil)
        (.node (899, 1798) (.node (898, 898) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree65 : BinaryTree (ℕ × ℕ) :=
  .node (870, 1740) routeSubtree63 routeSubtree64

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree66 : BinaryTree (ℕ × ℕ) :=
  (.node (915, 1830)
    (.node (908, 908)
      (.node (904, 904)
        (.node (902, 1804) (.node (901, 1802) .nil .nil) (.node (903, 1806) .nil .nil))
        (.node (906, 1812) (.node (905, 1810) .nil .nil) .nil))
      (.node (912, 1824) (.node (910, 5460) (.node (909, 1818) .nil .nil) .nil)
        (.node (914, 914) (.node (913, 1826) .nil .nil) .nil)))
    (.node (923, 1846)
      (.node (920, 2760)
        (.node (917, 1834) (.node (916, 916) .nil .nil) (.node (918, 1836) .nil .nil))
        (.node (922, 922) (.node (921, 1842) .nil .nil) .nil))
      (.node (926, 926) (.node (925, 1850) (.node (924, 1848) .nil .nil) .nil)
        (.node (928, 928) (.node (927, 1854) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree67 : BinaryTree (ℕ × ℕ) :=
  (.node (945, 1890)
    (.node (938, 1876)
      (.node (934, 934)
        (.node (932, 932) (.node (931, 1862) .nil .nil) (.node (933, 1866) .nil .nil))
        (.node (936, 1872) (.node (935, 5610) .nil .nil) .nil))
      (.node (942, 1884) (.node (940, 2820) (.node (939, 1878) .nil .nil) .nil)
        (.node (944, 944) (.node (943, 1886) .nil .nil) .nil)))
    (.node (954, 1908)
      (.node (950, 2850)
        (.node (948, 1896) (.node (946, 1892) .nil .nil) (.node (949, 1898) .nil .nil))
        (.node (952, 2856) (.node (951, 1902) .nil .nil) .nil))
      (.node (957, 1914) (.node (956, 956) (.node (955, 1910) .nil .nil) .nil)
        (.node (959, 1918) (.node (958, 958) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree68 : BinaryTree (ℕ × ℕ) :=
  .node (930, 2790) routeSubtree66 routeSubtree67

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree69 : BinaryTree (ℕ × ℕ) :=
  .node (900, 1800) routeSubtree65 routeSubtree68

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree70 : BinaryTree (ℕ × ℕ) :=
  (.node (976, 976)
    (.node (969, 1938)
      (.node (965, 1930)
        (.node (963, 1926) (.node (962, 1924) .nil .nil) (.node (964, 964) .nil .nil))
        (.node (968, 968) (.node (966, 1932) .nil .nil) .nil))
      (.node (973, 1946) (.node (972, 972) (.node (970, 2910) .nil .nil) .nil)
        (.node (975, 1950) (.node (974, 974) .nil .nil) .nil)))
    (.node (985, 1970)
      (.node (981, 1962)
        (.node (979, 1958) (.node (978, 1956) .nil .nil) (.node (980, 2940) .nil .nil))
        (.node (984, 1968) (.node (982, 982) .nil .nil) .nil))
      (.node (988, 1976) (.node (987, 1974) (.node (986, 1972) .nil .nil) .nil)
        (.node (990, 1980) (.node (989, 1978) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree71 : BinaryTree (ℕ × ℕ) :=
  (.node (1006, 1006)
    (.node (1000, 1000)
      (.node (996, 1992)
        (.node (994, 1988) (.node (993, 1986) .nil .nil) (.node (995, 1990) .nil .nil))
        (.node (999, 1998) (.node (998, 998) .nil .nil) .nil))
      (.node (1003, 2006) (.node (1002, 2004) (.node (1001, 2002) .nil .nil) .nil)
        (.node (1005, 2010) (.node (1004, 1004) .nil .nil) .nil)))
    (.node (1015, 2030)
      (.node (1011, 2022)
        (.node (1008, 2016) (.node (1007, 2014) .nil .nil) (.node (1010, 3030) .nil .nil))
        (.node (1014, 2028) (.node (1012, 2024) .nil .nil) .nil))
      (.node (1018, 1018) (.node (1017, 2034) (.node (1016, 1016) .nil .nil) .nil)
        (.node (1022, 3066) (.node (1020, 2040) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree72 : BinaryTree (ℕ × ℕ) :=
  .node (992, 992) routeSubtree70 routeSubtree71

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree73 : BinaryTree (ℕ × ℕ) :=
  (.node (1040, 3120)
    (.node (1032, 2064)
      (.node (1028, 1028)
        (.node (1026, 2052) (.node (1025, 2050) .nil .nil) (.node (1027, 2054) .nil .nil))
        (.node (1030, 2060) (.node (1029, 2058) .nil .nil) .nil))
      (.node (1036, 2072) (.node (1035, 2070) (.node (1034, 3102) .nil .nil) .nil)
        (.node (1038, 2076) (.node (1037, 2074) .nil .nil) .nil)))
    (.node (1047, 2094)
      (.node (1044, 2088)
        (.node (1042, 1042) (.node (1041, 2082) .nil .nil) (.node (1043, 2086) .nil .nil))
        (.node (1046, 1046) (.node (1045, 2090) .nil .nil) .nil))
      (.node (1052, 1052) (.node (1050, 2100) (.node (1048, 1048) .nil .nil) .nil)
        (.node (1054, 3162) (.node (1053, 1053) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree74 : BinaryTree (ℕ × ℕ) :=
  (.node (1071, 2142)
    (.node (1064, 3192)
      (.node (1059, 1059)
        (.node (1057, 1057) (.node (1056, 1056) .nil .nil) (.node (1058, 1058) .nil .nil))
        (.node (1062, 1062) (.node (1060, 3180) .nil .nil) .nil))
      (.node (1067, 1067) (.node (1066, 3198) (.node (1065, 2130) .nil .nil) .nil)
        (.node (1070, 3210) (.node (1068, 1068) .nil .nil) .nil)))
    (.node (1078, 3234)
      (.node (1075, 1075)
        (.node (1073, 1073) (.node (1072, 1072) .nil .nil) (.node (1074, 1074) .nil .nil))
        (.node (1077, 1077) (.node (1076, 1076) .nil .nil) .nil))
      (.node (1081, 1081) (.node (1080, 1080) (.node (1079, 1079) .nil .nil) .nil)
        (.node (1083, 1083) (.node (1082, 1082) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree75 : BinaryTree (ℕ × ℕ) :=
  .node (1055, 1055) routeSubtree73 routeSubtree74

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree76 : BinaryTree (ℕ × ℕ) :=
  .node (1023, 2046) routeSubtree72 routeSubtree75

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree77 : BinaryTree (ℕ × ℕ) :=
  .node (960, 1920) routeSubtree69 routeSubtree76

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree78 : BinaryTree (ℕ × ℕ) :=
  (.node (1101, 1101)
    (.node (1094, 1094)
      (.node (1089, 1089)
        (.node (1086, 1086) (.node (1085, 2170) .nil .nil) (.node (1088, 1088) .nil .nil))
        (.node (1092, 2184) (.node (1090, 3270) .nil .nil) .nil))
      (.node (1098, 1098) (.node (1096, 1096) (.node (1095, 2190) .nil .nil) .nil)
        (.node (1100, 1100) (.node (1099, 1099) .nil .nil) .nil)))
    (.node (1110, 2220)
      (.node (1106, 1106)
        (.node (1104, 1104) (.node (1102, 1102) .nil .nil) (.node (1105, 2210) .nil .nil))
        (.node (1108, 1108) (.node (1107, 1107) .nil .nil) .nil))
      (.node (1113, 2226) (.node (1112, 1112) (.node (1111, 1111) .nil .nil) .nil)
        (.node (1115, 1115) (.node (1114, 1114) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree79 : BinaryTree (ℕ × ℕ) :=
  (.node (1132, 1132)
    (.node (1125, 1125)
      (.node (1121, 1121)
        (.node (1119, 1119) (.node (1118, 1118) .nil .nil) (.node (1120, 1120) .nil .nil))
        (.node (1124, 1124) (.node (1122, 2244) .nil .nil) .nil))
      (.node (1128, 1128) (.node (1127, 1127) (.node (1126, 1126) .nil .nil) .nil)
        (.node (1131, 2262) (.node (1130, 1130) .nil .nil) .nil)))
    (.node (1139, 1139)
      (.node (1136, 1136)
        (.node (1134, 1134) (.node (1133, 1133) .nil .nil) (.node (1135, 1135) .nil .nil))
        (.node (1138, 1138) (.node (1137, 1137) .nil .nil) .nil))
      (.node (1142, 1142) (.node (1141, 1141) (.node (1140, 2280) .nil .nil) .nil)
        (.node (1144, 1144) (.node (1143, 1143) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree80 : BinaryTree (ℕ × ℕ) :=
  .node (1116, 1116) routeSubtree78 routeSubtree79

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree81 : BinaryTree (ℕ × ℕ) :=
  (.node (1160, 1160)
    (.node (1154, 1154)
      (.node (1149, 1149)
        (.node (1147, 1147) (.node (1146, 1146) .nil .nil) (.node (1148, 1148) .nil .nil))
        (.node (1152, 1152) (.node (1150, 1150) .nil .nil) .nil))
      (.node (1157, 1157) (.node (1156, 1156) (.node (1155, 4620) .nil .nil) .nil)
        (.node (1159, 1159) (.node (1158, 1158) .nil .nil) .nil)))
    (.node (1168, 1168)
      (.node (1165, 1165)
        (.node (1162, 1162) (.node (1161, 1161) .nil .nil) (.node (1164, 1164) .nil .nil))
        (.node (1167, 1167) (.node (1166, 1166) .nil .nil) .nil))
      (.node (1172, 1172) (.node (1170, 2340) (.node (1169, 1169) .nil .nil) .nil)
        (.node (1174, 1174) (.node (1173, 2346) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree82 : BinaryTree (ℕ × ℕ) :=
  (.node (1190, 2380)
    (.node (1183, 1183)
      (.node (1179, 1179)
        (.node (1177, 1177) (.node (1176, 1176) .nil .nil) (.node (1178, 1178) .nil .nil))
        (.node (1182, 1182) (.node (1180, 1180) .nil .nil) .nil))
      (.node (1186, 1186) (.node (1185, 2370) (.node (1184, 1184) .nil .nil) .nil)
        (.node (1189, 1189) (.node (1188, 1188) .nil .nil) .nil)))
    (.node (1198, 1198)
      (.node (1195, 1195)
        (.node (1192, 1192) (.node (1191, 1191) .nil .nil) (.node (1194, 1194) .nil .nil))
        (.node (1197, 2394) (.node (1196, 1196) .nil .nil) .nil))
      (.node (1202, 1202) (.node (1200, 1200) (.node (1199, 1199) .nil .nil) .nil)
        (.node (1204, 1204) (.node (1203, 1203) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree83 : BinaryTree (ℕ × ℕ) :=
  .node (1175, 1175) routeSubtree81 routeSubtree82

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree84 : BinaryTree (ℕ × ℕ) :=
  .node (1145, 1145) routeSubtree80 routeSubtree83

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree85 : BinaryTree (ℕ × ℕ) :=
  (.node (1220, 1220)
    (.node (1212, 1212)
      (.node (1209, 2418)
        (.node (1207, 1207) (.node (1206, 1206) .nil .nil) (.node (1208, 1208) .nil .nil))
        (.node (1211, 1211) (.node (1210, 1210) .nil .nil) .nil))
      (.node (1216, 1216) (.node (1215, 1215) (.node (1214, 1214) .nil .nil) .nil)
        (.node (1219, 1219) (.node (1218, 2436) .nil .nil) .nil)))
    (.node (1228, 1228)
      (.node (1225, 1225)
        (.node (1222, 1222) (.node (1221, 2442) .nil .nil) (.node (1224, 1224) .nil .nil))
        (.node (1227, 1227) (.node (1226, 1226) .nil .nil) .nil))
      (.node (1233, 1233) (.node (1232, 1232) (.node (1230, 2460) .nil .nil) .nil)
        (.node (1235, 2470) (.node (1234, 1234) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree86 : BinaryTree (ℕ × ℕ) :=
  (.node (1251, 1251)
    (.node (1244, 1244)
      (.node (1241, 1241)
        (.node (1239, 2478) (.node (1238, 1238) .nil .nil) (.node (1240, 1240) .nil .nil))
        (.node (1243, 1243) (.node (1242, 1242) .nil .nil) .nil))
      (.node (1247, 1247) (.node (1246, 1246) (.node (1245, 2490) .nil .nil) .nil)
        (.node (1250, 1250) (.node (1248, 1248) .nil .nil) .nil)))
    (.node (1258, 1258)
      (.node (1255, 1255)
        (.node (1253, 1253) (.node (1252, 1252) .nil .nil) (.node (1254, 2508) .nil .nil))
        (.node (1257, 1257) (.node (1256, 1256) .nil .nil) .nil))
      (.node (1262, 1262) (.node (1261, 1261) (.node (1260, 2520) .nil .nil) .nil)
        (.node (1264, 1264) (.node (1263, 1263) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree87 : BinaryTree (ℕ × ℕ) :=
  .node (1236, 1236) routeSubtree85 routeSubtree86

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree88 : BinaryTree (ℕ × ℕ) :=
  (.node (1280, 1280)
    (.node (1272, 1272)
      (.node (1269, 1269)
        (.node (1267, 1267) (.node (1266, 1266) .nil .nil) (.node (1268, 1268) .nil .nil))
        (.node (1271, 1271) (.node (1270, 1270) .nil .nil) .nil))
      (.node (1275, 2550) (.node (1274, 1274) (.node (1273, 1273) .nil .nil) .nil)
        (.node (1278, 1278) (.node (1276, 1276) .nil .nil) .nil)))
    (.node (1288, 1288)
      (.node (1285, 1285)
        (.node (1282, 1282) (.node (1281, 2562) .nil .nil) (.node (1284, 1284) .nil .nil))
        (.node (1287, 2574) (.node (1286, 1286) .nil .nil) .nil))
      (.node (1293, 1293) (.node (1292, 1292) (.node (1290, 2580) .nil .nil) .nil)
        (.node (1295, 2590) (.node (1294, 1294) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree89 : BinaryTree (ℕ × ℕ) :=
  (.node (1326, 2652)
    (.node (1309, 2618)
      (.node (1302, 2604)
        (.node (1299, 1299) (.node (1298, 1298) .nil .nil) (.node (1300, 1300) .nil .nil))
        (.node (1308, 1308) (.node (1305, 2610) .nil .nil) .nil))
      (.node (1314, 1314) (.node (1311, 2622) (.node (1310, 1310) .nil .nil) .nil)
        (.node (1320, 2640) (.node (1316, 1316) .nil .nil) .nil)))
    (.node (1340, 1340)
      (.node (1334, 1334) (.node (1332, 1332) (.node (1330, 3990) .nil .nil) .nil)
        (.node (1338, 1338) (.node (1335, 2670) .nil .nil) .nil))
      (.node (1350, 1350) (.node (1344, 1344) (.node (1342, 1342) .nil .nil) .nil)
        (.node (1356, 1356) (.node (1353, 2706) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree90 : BinaryTree (ℕ × ℕ) :=
  .node (1296, 1296) routeSubtree88 routeSubtree89

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree91 : BinaryTree (ℕ × ℕ) :=
  .node (1265, 2530) routeSubtree87 routeSubtree90

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree92 : BinaryTree (ℕ × ℕ) :=
  .node (1205, 1205) routeSubtree84 routeSubtree91

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree93 : BinaryTree (ℕ × ℕ) :=
  .node (1084, 1084) routeSubtree77 routeSubtree92

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree94 : BinaryTree (ℕ × ℕ) :=
  (.node (1394, 1394)
    (.node (1374, 1374)
      (.node (1365, 5460)
        (.node (1362, 1362) (.node (1360, 1360) .nil .nil) (.node (1364, 1364) .nil .nil))
        (.node (1370, 1370) (.node (1368, 1368) .nil .nil) .nil))
      (.node (1386, 2772) (.node (1380, 2760) (.node (1378, 1378) .nil .nil) .nil)
        (.node (1392, 1392) (.node (1390, 1390) .nil .nil) .nil)))
    (.node (1410, 2820)
      (.node (1404, 1404)
        (.node (1398, 1398) (.node (1395, 2790) .nil .nil) (.node (1400, 1400) .nil .nil))
        (.node (1407, 2814) (.node (1406, 1406) .nil .nil) .nil))
      (.node (1419, 2838) (.node (1416, 1416) (.node (1414, 1414) .nil .nil) .nil)
        (.node (1422, 1422) (.node (1420, 1420) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree95 : BinaryTree (ℕ × ℕ) :=
  (.node (1455, 2910)
    (.node (1442, 1442)
      (.node (1434, 1434)
        (.node (1428, 2856) (.node (1426, 1426) .nil .nil) (.node (1430, 4290) .nil .nil))
        (.node (1440, 1440) (.node (1435, 2870) .nil .nil) .nil))
      (.node (1449, 2898) (.node (1446, 1446) (.node (1443, 2886) .nil .nil) .nil)
        (.node (1452, 1452) (.node (1450, 1450) .nil .nil) .nil)))
    (.node (1474, 1474)
      (.node (1463, 2926)
        (.node (1460, 1460) (.node (1456, 1456) .nil .nil) (.node (1462, 1462) .nil .nil))
        (.node (1470, 2940) (.node (1464, 1464) .nil .nil) .nil))
      (.node (1480, 1480) (.node (1479, 2958) (.node (1476, 1476) .nil .nil) .nil)
        (.node (1484, 1484) (.node (1482, 2964) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree96 : BinaryTree (ℕ × ℕ) :=
  .node (1425, 2850) routeSubtree94 routeSubtree95

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree97 : BinaryTree (ℕ × ℕ) :=
  (.node (1512, 1512)
    (.node (1498, 1498)
      (.node (1494, 1494)
        (.node (1490, 1490) (.node (1488, 1488) .nil .nil) (.node (1491, 2982) .nil .nil))
        (.node (1496, 1496) (.node (1495, 2990) .nil .nil) .nil))
      (.node (1506, 1506) (.node (1505, 3010) (.node (1500, 1500) .nil .nil) .nil)
        (.node (1510, 1510) (.node (1508, 1508) .nil .nil) .nil)))
    (.node (1533, 3066)
      (.node (1524, 1524)
        (.node (1518, 3036) (.node (1515, 3030) .nil .nil) (.node (1520, 1520) .nil .nil))
        (.node (1530, 3060) (.node (1526, 1526) .nil .nil) .nil))
      (.node (1542, 1542) (.node (1540, 4620) (.node (1534, 1534) .nil .nil) .nil)
        (.node (1547, 3094) (.node (1545, 3090) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree98 : BinaryTree (ℕ × ℕ) :=
  (.node (1580, 1580)
    (.node (1564, 1564)
      (.node (1558, 1558)
        (.node (1551, 3102) (.node (1550, 1550) .nil .nil) (.node (1554, 3108) .nil .nil))
        (.node (1562, 1562) (.node (1560, 3120) .nil .nil) .nil))
      (.node (1572, 1572) (.node (1570, 1570) (.node (1566, 1566) .nil .nil) .nil)
        (.node (1578, 1578) (.node (1575, 3150) .nil .nil) .nil)))
    (.node (1596, 3192)
      (.node (1586, 1586)
        (.node (1582, 1582) (.node (1581, 3162) .nil .nil) (.node (1584, 1584) .nil .nil))
        (.node (1595, 3190) (.node (1590, 3180) .nil .nil) .nil))
      (.node (1602, 1602) (.node (1599, 3198) (.node (1598, 1598) .nil .nil) .nil)
        (.node (1606, 1606) (.node (1605, 3210) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree99 : BinaryTree (ℕ × ℕ) :=
  .node (1548, 1548) routeSubtree97 routeSubtree98

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree100 : BinaryTree (ℕ × ℕ) :=
  .node (1485, 2970) routeSubtree96 routeSubtree99

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree101 : BinaryTree (ℕ × ℕ) :=
  (.node (1635, 3270)
    (.node (1624, 1624)
      (.node (1615, 3230)
        (.node (1612, 1612) (.node (1610, 3220) .nil .nil) (.node (1614, 1614) .nil .nil))
        (.node (1620, 1620) (.node (1617, 3234) .nil .nil) .nil))
      (.node (1630, 1630) (.node (1628, 1628) (.node (1626, 1626) .nil .nil) .nil)
        (.node (1634, 1634) (.node (1632, 1632) .nil .nil) .nil)))
    (.node (1653, 1653)
      (.node (1645, 3290)
        (.node (1640, 1640) (.node (1638, 3276) .nil .nil) (.node (1644, 1644) .nil .nil))
        (.node (1652, 1652) (.node (1650, 1650) .nil .nil) .nil))
      (.node (1660, 1660) (.node (1659, 1659) (.node (1656, 1656) .nil .nil) .nil)
        (.node (1665, 1665) (.node (1662, 1662) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree102 : BinaryTree (ℕ × ℕ) :=
  (.node (1698, 1698)
    (.node (1683, 1683)
      (.node (1674, 1674)
        (.node (1670, 1670) (.node (1668, 1668) .nil .nil) (.node (1672, 1672) .nil .nil))
        (.node (1680, 1680) (.node (1677, 1677) .nil .nil) .nil))
      (.node (1692, 1692) (.node (1690, 1690) (.node (1686, 1686) .nil .nil) .nil)
        (.node (1695, 1695) (.node (1694, 1694) .nil .nil) .nil)))
    (.node (1716, 1716)
      (.node (1705, 1705)
        (.node (1702, 1702) (.node (1700, 1700) .nil .nil) (.node (1704, 1704) .nil .nil))
        (.node (1710, 1710) (.node (1708, 1708) .nil .nil) .nil))
      (.node (1725, 1725) (.node (1722, 1722) (.node (1720, 1720) .nil .nil) .nil)
        (.node (1730, 1730) (.node (1729, 1729) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree103 : BinaryTree (ℕ × ℕ) :=
  .node (1666, 1666) routeSubtree101 routeSubtree102

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree104 : BinaryTree (ℕ × ℕ) :=
  (.node (1760, 1760)
    (.node (1748, 1748)
      (.node (1742, 1742)
        (.node (1738, 1738) (.node (1736, 1736) .nil .nil) (.node (1740, 1740) .nil .nil))
        (.node (1746, 1746) (.node (1743, 1743) .nil .nil) .nil))
      (.node (1752, 1752) (.node (1750, 1750) (.node (1749, 1749) .nil .nil) .nil)
        (.node (1758, 1758) (.node (1755, 1755) .nil .nil) .nil)))
    (.node (1778, 1778)
      (.node (1770, 1770)
        (.node (1767, 1767) (.node (1764, 1764) .nil .nil) (.node (1768, 1768) .nil .nil))
        (.node (1776, 1776) (.node (1771, 1771) .nil .nil) .nil))
      (.node (1785, 3570) (.node (1782, 1782) (.node (1780, 1780) .nil .nil) .nil)
        (.node (1788, 1788) (.node (1786, 1786) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree105 : BinaryTree (ℕ × ℕ) :=
  (.node (1826, 1826)
    (.node (1810, 1810)
      (.node (1802, 1802)
        (.node (1798, 1798) (.node (1794, 1794) .nil .nil) (.node (1800, 1800) .nil .nil))
        (.node (1806, 1806) (.node (1804, 1804) .nil .nil) .nil))
      (.node (1818, 1818) (.node (1815, 1815) (.node (1812, 1812) .nil .nil) .nil)
        (.node (1824, 1824) (.node (1820, 5460) .nil .nil) .nil)))
    (.node (1840, 1840)
      (.node (1833, 1833) (.node (1830, 1830) (.node (1827, 1827) .nil .nil) .nil)
        (.node (1836, 1836) (.node (1834, 1834) .nil .nil) .nil))
      (.node (1846, 1846) (.node (1845, 1845) (.node (1842, 1842) .nil .nil) .nil)
        (.node (1850, 1850) (.node (1848, 1848) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree106 : BinaryTree (ℕ × ℕ) :=
  .node (1790, 1790) routeSubtree104 routeSubtree105

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree107 : BinaryTree (ℕ × ℕ) :=
  .node (1734, 1734) routeSubtree103 routeSubtree106

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree108 : BinaryTree (ℕ × ℕ) :=
  .node (1608, 1608) routeSubtree100 routeSubtree107

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree109 : BinaryTree (ℕ × ℕ) :=
  (.node (1885, 1885)
    (.node (1872, 1872)
      (.node (1866, 1866)
        (.node (1860, 1860) (.node (1855, 1855) .nil .nil) (.node (1862, 1862) .nil .nil))
        (.node (1870, 5610) (.node (1869, 1869) .nil .nil) .nil))
      (.node (1880, 1880) (.node (1878, 1878) (.node (1876, 1876) .nil .nil) .nil)
        (.node (1884, 1884) (.node (1881, 1881) .nil .nil) .nil)))
    (.node (1900, 1900)
      (.node (1892, 1892)
        (.node (1887, 1887) (.node (1886, 1886) .nil .nil) (.node (1890, 1890) .nil .nil))
        (.node (1898, 1898) (.node (1896, 1896) .nil .nil) .nil))
      (.node (1905, 1905) (.node (1904, 1904) (.node (1902, 1902) .nil .nil) .nil)
        (.node (1910, 1910) (.node (1908, 1908) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree110 : BinaryTree (ℕ × ℕ) :=
  (.node (1947, 1947)
    (.node (1930, 1930)
      (.node (1924, 1924)
        (.node (1918, 1918) (.node (1914, 1914) .nil .nil) (.node (1920, 1920) .nil .nil))
        (.node (1926, 1926) (.node (1925, 1925) .nil .nil) .nil))
      (.node (1938, 1938) (.node (1935, 1935) (.node (1932, 1932) .nil .nil) .nil)
        (.node (1946, 1946) (.node (1940, 1940) .nil .nil) .nil)))
    (.node (1962, 1962)
      (.node (1956, 1956)
        (.node (1953, 1953) (.node (1950, 1950) .nil .nil) (.node (1955, 1955) .nil .nil))
        (.node (1960, 1960) (.node (1958, 1958) .nil .nil) .nil))
      (.node (1970, 1970) (.node (1968, 1968) (.node (1965, 1965) .nil .nil) .nil)
        (.node (1974, 1974) (.node (1972, 1972) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree111 : BinaryTree (ℕ × ℕ) :=
  .node (1911, 1911) routeSubtree109 routeSubtree110

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree112 : BinaryTree (ℕ × ℕ) :=
  (.node (2006, 2006)
    (.node (1992, 1992)
      (.node (1988, 1988)
        (.node (1980, 1980) (.node (1978, 1978) .nil .nil) (.node (1986, 1986) .nil .nil))
        (.node (1990, 1990) (.node (1989, 1989) .nil .nil) .nil))
      (.node (2001, 2001) (.node (1998, 1998) (.node (1995, 3990) .nil .nil) .nil)
        (.node (2004, 2004) (.node (2002, 2002) .nil .nil) .nil)))
    (.node (2022, 2022)
      (.node (2015, 2015)
        (.node (2013, 2013) (.node (2010, 2010) .nil .nil) (.node (2014, 2014) .nil .nil))
        (.node (2020, 2020) (.node (2016, 2016) .nil .nil) .nil))
      (.node (2030, 2030) (.node (2028, 2028) (.node (2024, 2024) .nil .nil) .nil)
        (.node (2035, 2035) (.node (2034, 2034) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree113 : BinaryTree (ℕ × ℕ) :=
  (.node (2068, 2068)
    (.node (2055, 2055)
      (.node (2050, 2050)
        (.node (2044, 2044) (.node (2040, 2040) .nil .nil) (.node (2046, 2046) .nil .nil))
        (.node (2054, 2054) (.node (2052, 2052) .nil .nil) .nil))
      (.node (2064, 2064) (.node (2060, 2060) (.node (2058, 2058) .nil .nil) .nil)
        (.node (2067, 2067) (.node (2065, 2065) .nil .nil) .nil)))
    (.node (2082, 2082)
      (.node (2076, 2076)
        (.node (2072, 2072) (.node (2070, 2070) .nil .nil) (.node (2074, 2074) .nil .nil))
        (.node (2080, 2080) (.node (2079, 2079) .nil .nil) .nil))
      (.node (2088, 2088) (.node (2086, 2086) (.node (2085, 2085) .nil .nil) .nil)
        (.node (2091, 2091) (.node (2090, 2090) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree114 : BinaryTree (ℕ × ℕ) :=
  .node (2037, 2037) routeSubtree112 routeSubtree113

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree115 : BinaryTree (ℕ × ℕ) :=
  .node (1976, 1976) routeSubtree111 routeSubtree114

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree116 : BinaryTree (ℕ × ℕ) :=
  (.node (2262, 2262)
    (.node (2184, 2184)
      (.node (2142, 2142)
        (.node (2100, 2100) (.node (2094, 2094) .nil .nil) (.node (2130, 2130) .nil .nil))
        (.node (2170, 2170) (.node (2145, 4290) .nil .nil) .nil))
      (.node (2220, 2220) (.node (2210, 2210) (.node (2190, 2190) .nil .nil) .nil)
        (.node (2244, 2244) (.node (2226, 2226) .nil .nil) .nil)))
    (.node (2394, 2394)
      (.node (2346, 2346)
        (.node (2310, 4620) (.node (2280, 2280) .nil .nil) (.node (2340, 2340) .nil .nil))
        (.node (2380, 2380) (.node (2370, 2370) .nil .nil) .nil))
      (.node (2436, 2436) (.node (2418, 2418) (.node (2415, 4830) .nil .nil) .nil)
        (.node (2460, 2460) (.node (2442, 2442) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree117 : BinaryTree (ℕ × ℕ) :=
  (.node (2618, 2618)
    (.node (2562, 2562)
      (.node (2520, 2520)
        (.node (2490, 2490) (.node (2478, 2478) .nil .nil) (.node (2508, 2508) .nil .nil))
        (.node (2550, 2550) (.node (2530, 2530) .nil .nil) .nil))
      (.node (2590, 2590) (.node (2580, 2580) (.node (2574, 2574) .nil .nil) .nil)
        (.node (2610, 2610) (.node (2604, 2604) .nil .nil) .nil)))
    (.node (2730, 5460)
      (.node (2660, 2660)
        (.node (2640, 2640) (.node (2622, 2622) .nil .nil) (.node (2652, 2652) .nil .nil))
        (.node (2706, 2706) (.node (2670, 2670) .nil .nil) .nil))
      (.node (2790, 2790) (.node (2772, 2772) (.node (2760, 2760) .nil .nil) .nil)
        (.node (2814, 2814) (.node (2805, 5610) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree118 : BinaryTree (ℕ × ℕ) :=
  .node (2470, 2470) routeSubtree116 routeSubtree117

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree119 : BinaryTree (ℕ × ℕ) :=
  (.node (2970, 2970)
    (.node (2898, 2898)
      (.node (2860, 2860)
        (.node (2850, 2850) (.node (2838, 2838) .nil .nil) (.node (2856, 2856) .nil .nil))
        (.node (2886, 2886) (.node (2870, 2870) .nil .nil) .nil))
      (.node (2940, 2940) (.node (2926, 2926) (.node (2910, 2910) .nil .nil) .nil)
        (.node (2964, 2964) (.node (2958, 2958) .nil .nil) .nil)))
    (.node (3045, 3045)
      (.node (3010, 3010)
        (.node (2990, 2990) (.node (2982, 2982) .nil .nil) (.node (3003, 3003) .nil .nil))
        (.node (3036, 3036) (.node (3030, 3030) .nil .nil) .nil))
      (.node (3080, 3080) (.node (3066, 3066) (.node (3060, 3060) .nil .nil) .nil)
        (.node (3094, 3094) (.node (3090, 3090) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree120 : BinaryTree (ℕ × ℕ) :=
  (.node (3234, 3234)
    (.node (3190, 3190)
      (.node (3150, 3150)
        (.node (3120, 3120) (.node (3108, 3108) .nil .nil) (.node (3135, 3135) .nil .nil))
        (.node (3180, 3180) (.node (3162, 3162) .nil .nil) .nil))
      (.node (3210, 3210) (.node (3198, 3198) (.node (3192, 3192) .nil .nil) .nil)
        (.node (3230, 3230) (.node (3220, 3220) .nil .nil) .nil)))
    (.node (3990, 3990)
      (.node (3276, 3276) (.node (3270, 3270) (.node (3255, 3255) .nil .nil) .nil)
        (.node (3570, 3570) (.node (3290, 3290) .nil .nil) .nil))
      (.node (4830, 4830) (.node (4620, 4620) (.node (4290, 4290) .nil .nil) .nil)
        (.node (5610, 5610) (.node (5460, 5460) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree121 : BinaryTree (ℕ × ℕ) :=
  .node (3102, 3102) routeSubtree119 routeSubtree120

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree122 : BinaryTree (ℕ × ℕ) :=
  .node (2820, 2820) routeSubtree118 routeSubtree121

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree123 : BinaryTree (ℕ × ℕ) :=
  .node (2093, 2093) routeSubtree115 routeSubtree122

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree124 : BinaryTree (ℕ × ℕ) :=
  .node (1854, 1854) routeSubtree108 routeSubtree123

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree125 : BinaryTree (ℕ × ℕ) :=
  .node (1358, 1358) routeSubtree93 routeSubtree124

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree126 : BinaryTree (ℕ × ℕ) :=
  .node (838, 838) routeSubtree62 routeSubtree125

/-- Balanced target-source modulus entries.
Direct entries use the target itself; other targets divide their checked source.
The checked source cap is compared with the target's integer bound. -/
def routes : BinaryTree (ℕ × ℕ) :=
  routeSubtree126

/-- Kernel verification of all divisibilities, source lookups and target caps.
The source coverage proofs are shared and are not reevaluated by this check. -/
theorem routes_checked :
    NumberTheory.certificateTreeAllCheck
        (residueDivisorRouteCheck Corollary12DirectCoverage.coreTree) routes =
      true := by
  decide +kernel

/-- Successful finite route lookup gives the least-prime estimate at the target.
Transfer the source coverage and retain its integer bound before minimization. -/
theorem leastPrime {q : ℕ} [NeZero q] {e : ℕ × ℕ}
    (hl : NumberTheory.certificateTreeLookup Prod.fst routes q = some e) (a : (ZMod q)ˣ) :
    ∃ p : ℕ,
      IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  exact
    exists_least_prime_in_residue_le_of_route_lookup Corollary12DirectCoverage.coreTree_checked
      routes_checked hl a

end PseudoPrime.LLS.PaperStatements.Corollary12DivisorRoutes

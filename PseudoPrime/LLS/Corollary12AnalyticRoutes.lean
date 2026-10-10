/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Corollary12PrimeCatalog
public import PseudoPrime.LLS.ResidueFactorRoutes

/-! Factor-certified analytic routes below the shared large interval.
Regenerate with generate_corollary12_routes.py --part factors. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.Corollary12AnalyticRoutes

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree0 : BinaryTree (ℕ × List ℕ) :=
  (.node (887, [887])
    (.node (841, [29, 29])
      (.node (823, [823])
        (.node (811, [811]) (.node (809, [809]) .nil .nil) (.node (821, [821]) .nil .nil))
        (.node (829, [829]) (.node (827, [827]) .nil .nil) (.node (839, [839]) .nil .nil)))
      (.node (863, [863])
        (.node (857, [857]) (.node (853, [853]) .nil .nil) (.node (859, [859]) .nil .nil))
        (.node (881, [881]) (.node (877, [877]) .nil .nil) (.node (883, [883]) .nil .nil))))
    (.node (953, [953])
      (.node (929, [929])
        (.node (911, [911]) (.node (907, [907]) .nil .nil) (.node (919, [919]) .nil .nil))
        (.node (941, [941]) (.node (937, [937]) .nil .nil) (.node (947, [947]) .nil .nil)))
      (.node (977, [977])
        (.node (967, [967]) (.node (961, [31, 31]) .nil .nil) (.node (971, [971]) .nil .nil))
        (.node (991, [991]) (.node (983, [983]) .nil .nil) (.node (997, [997]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree1 : BinaryTree (ℕ × List ℕ) :=
  (.node (1097, [1097])
    (.node (1049, [1049])
      (.node (1024, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2])
        (.node (1019, [1019]) (.node (1013, [1013]) .nil .nil) (.node (1021, [1021]) .nil .nil))
        (.node (1033, [1033]) (.node (1031, [1031]) .nil .nil) (.node (1039, [1039]) .nil .nil)))
      (.node (1069, [1069])
        (.node (1061, [1061]) (.node (1051, [1051]) .nil .nil) (.node (1063, [1063]) .nil .nil))
        (.node (1091, [1091]) (.node (1087, [1087]) .nil .nil) (.node (1093, [1093]) .nil .nil))))
    (.node (1163, [1163])
      (.node (1123, [1123])
        (.node (1109, [1109]) (.node (1103, [1103]) .nil .nil) (.node (1117, [1117]) .nil .nil))
        (.node (1151, [1151]) (.node (1129, [1129]) .nil .nil) (.node (1153, [1153]) .nil .nil)))
      (.node (1193, [1193])
        (.node (1181, [1181]) (.node (1171, [1171]) .nil .nil) (.node (1187, [1187]) .nil .nil))
        (.node (1213, [1213]) (.node (1201, [1201]) .nil .nil) (.node (1217, [1217]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree2 : BinaryTree (ℕ × List ℕ) :=
  .node (1009, [1009]) routeSubtree0 routeSubtree1

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree3 : BinaryTree (ℕ × List ℕ) :=
  (.node (1307, [1307])
    (.node (1283, [1283])
      (.node (1249, [1249])
        (.node (1231, [1231]) (.node (1229, [1229]) .nil .nil) (.node (1237, [1237]) .nil .nil))
        (.node (1277, [1277]) (.node (1259, [1259]) .nil .nil) (.node (1279, [1279]) .nil .nil)))
      (.node (1301, [1301])
        (.node (1291, [1291]) (.node (1289, [1289]) .nil .nil) (.node (1297, [1297]) .nil .nil))
        (.node (1304, [2, 2, 2, 163]) (.node (1303, [1303]) .nil .nil)
          (.node (1306, [2, 653]) .nil .nil))))
    (.node (1322, [2, 661])
      (.node (1317, [3, 439])
        (.node (1313, [13, 101]) (.node (1312, [2, 2, 2, 2, 2, 41]) .nil .nil)
          (.node (1315, [5, 263]) .nil .nil))
        (.node (1319, [1319]) (.node (1318, [2, 659]) .nil .nil) (.node (1321, [1321]) .nil .nil)))
      (.node (1327, [1327])
        (.node (1324, [2, 2, 331]) (.node (1323, [3, 3, 3, 7, 7]) .nil .nil)
          (.node (1325, [5, 5, 53]) .nil .nil))
        (.node (1329, [3, 443]) (.node (1328, [2, 2, 2, 2, 83]) .nil .nil)
          (.node (1331, [11, 11, 11]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree4 : BinaryTree (ℕ × List ℕ) :=
  (.node (1359, [3, 3, 151])
    (.node (1347, [3, 449])
      (.node (1341, [3, 3, 149])
        (.node (1337, [7, 191]) (.node (1336, [2, 2, 2, 167]) .nil .nil)
          (.node (1339, [13, 103]) .nil .nil))
        (.node (1345, [5, 269]) (.node (1343, [17, 79]) .nil .nil)
          (.node (1346, [2, 673]) .nil .nil)))
      (.node (1352, [2, 2, 2, 13, 13])
        (.node (1349, [19, 71]) (.node (1348, [2, 2, 337]) .nil .nil)
          (.node (1351, [7, 193]) .nil .nil))
        (.node (1355, [5, 271]) (.node (1354, [2, 677]) .nil .nil)
          (.node (1357, [23, 59]) .nil .nil))))
    (.node (1373, [1373])
      (.node (1367, [1367])
        (.node (1363, [29, 47]) (.node (1361, [1361]) .nil .nil) (.node (1366, [2, 683]) .nil .nil))
        (.node (1371, [3, 457]) (.node (1369, [37, 37]) .nil .nil)
          (.node (1372, [2, 2, 7, 7, 7]) .nil .nil)))
      (.node (1379, [7, 197])
        (.node (1376, [2, 2, 2, 2, 2, 43]) (.node (1375, [5, 5, 5, 11]) .nil .nil)
          (.node (1377, [3, 3, 3, 3, 17]) .nil .nil))
        (.node (1382, [2, 691]) (.node (1381, [1381]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree5 : BinaryTree (ℕ × List ℕ) :=
  .node (1333, [31, 43]) routeSubtree3 routeSubtree4

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree6 : BinaryTree (ℕ × List ℕ) :=
  .node (1223, [1223]) routeSubtree2 routeSubtree5

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree7 : BinaryTree (ℕ × List ℕ) :=
  (.node (1409, [1409])
    (.node (1396, [2, 2, 349])
      (.node (1388, [2, 2, 347])
        (.node (1385, [5, 277]) (.node (1384, [2, 2, 2, 173]) .nil .nil)
          (.node (1387, [19, 73]) .nil .nil))
        (.node (1391, [13, 107]) (.node (1389, [3, 463]) .nil .nil)
          (.node (1393, [7, 199]) .nil .nil)))
      (.node (1402, [2, 701])
        (.node (1399, [1399]) (.node (1397, [11, 127]) .nil .nil)
          (.node (1401, [3, 467]) .nil .nil))
        (.node (1405, [5, 281]) (.node (1403, [23, 61]) .nil .nil)
          (.node (1408, [2, 2, 2, 2, 2, 2, 2, 11]) .nil .nil))))
    (.node (1423, [1423])
      (.node (1415, [5, 283])
        (.node (1412, [2, 2, 353]) (.node (1411, [17, 83]) .nil .nil)
          (.node (1413, [3, 3, 157]) .nil .nil))
        (.node (1418, [2, 709]) (.node (1417, [13, 109]) .nil .nil)
          (.node (1421, [7, 7, 29]) .nil .nil)))
      (.node (1431, [3, 3, 3, 53])
        (.node (1427, [1427]) (.node (1424, [2, 2, 2, 2, 89]) .nil .nil)
          (.node (1429, [1429]) .nil .nil))
        (.node (1433, [1433]) (.node (1432, [2, 2, 2, 179]) .nil .nil)
          (.node (1436, [2, 2, 359]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree8 : BinaryTree (ℕ × List ℕ) :=
  (.node (1466, [2, 733])
    (.node (1451, [1451])
      (.node (1444, [2, 2, 19, 19])
        (.node (1439, [1439]) (.node (1438, [2, 719]) .nil .nil)
          (.node (1441, [11, 131]) .nil .nil))
        (.node (1447, [1447]) (.node (1445, [5, 17, 17]) .nil .nil)
          (.node (1448, [2, 2, 2, 181]) .nil .nil)))
      (.node (1458, [2, 3, 3, 3, 3, 3, 3])
        (.node (1454, [2, 727]) (.node (1453, [1453]) .nil .nil) (.node (1457, [31, 47]) .nil .nil))
        (.node (1461, [3, 487]) (.node (1459, [1459]) .nil .nil)
          (.node (1465, [5, 293]) .nil .nil))))
    (.node (1477, [7, 211])
      (.node (1471, [1471])
        (.node (1468, [2, 2, 367]) (.node (1467, [3, 3, 163]) .nil .nil)
          (.node (1469, [13, 113]) .nil .nil))
        (.node (1473, [3, 491]) (.node (1472, [2, 2, 2, 2, 2, 2, 23]) .nil .nil)
          (.node (1475, [5, 5, 59]) .nil .nil)))
      (.node (1486, [2, 743])
        (.node (1481, [1481]) (.node (1478, [2, 739]) .nil .nil) (.node (1483, [1483]) .nil .nil))
        (.node (1489, [1489]) (.node (1487, [1487]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree9 : BinaryTree (ℕ × List ℕ) :=
  .node (1437, [3, 479]) routeSubtree7 routeSubtree8

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree10 : BinaryTree (ℕ × List ℕ) :=
  (.node (1521, [3, 3, 13, 13])
    (.node (1507, [11, 137])
      (.node (1501, [19, 79])
        (.node (1497, [3, 499]) (.node (1493, [1493]) .nil .nil) (.node (1499, [1499]) .nil .nil))
        (.node (1503, [3, 3, 167]) (.node (1502, [2, 751]) .nil .nil)
          (.node (1504, [2, 2, 2, 2, 2, 47]) .nil .nil)))
      (.node (1514, [2, 757])
        (.node (1511, [1511]) (.node (1509, [3, 503]) .nil .nil) (.node (1513, [17, 89]) .nil .nil))
        (.node (1517, [37, 41]) (.node (1516, [2, 2, 379]) .nil .nil)
          (.node (1519, [7, 7, 31]) .nil .nil))))
    (.node (1532, [2, 2, 383])
      (.node (1527, [3, 509])
        (.node (1523, [1523]) (.node (1522, [2, 761]) .nil .nil)
          (.node (1525, [5, 5, 61]) .nil .nil))
        (.node (1529, [11, 139]) (.node (1528, [2, 2, 2, 191]) .nil .nil)
          (.node (1531, [1531]) .nil .nil)))
      (.node (1538, [2, 769])
        (.node (1536, [2, 2, 2, 2, 2, 2, 2, 2, 2, 3]) (.node (1535, [5, 307]) .nil .nil)
          (.node (1537, [29, 53]) .nil .nil))
        (.node (1541, [23, 67]) (.node (1539, [3, 3, 3, 3, 19]) .nil .nil)
          (.node (1543, [1543]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree11 : BinaryTree (ℕ × List ℕ) :=
  (.node (1573, [11, 11, 13])
    (.node (1559, [1559])
      (.node (1553, [1553])
        (.node (1549, [1549]) (.node (1546, [2, 773]) .nil .nil)
          (.node (1552, [2, 2, 2, 2, 97]) .nil .nil))
        (.node (1556, [2, 2, 389]) (.node (1555, [5, 311]) .nil .nil)
          (.node (1557, [3, 3, 173]) .nil .nil)))
      (.node (1567, [1567])
        (.node (1563, [3, 521]) (.node (1561, [7, 223]) .nil .nil)
          (.node (1565, [5, 313]) .nil .nil))
        (.node (1569, [3, 523]) (.node (1568, [2, 2, 2, 2, 2, 7, 7]) .nil .nil)
          (.node (1571, [1571]) .nil .nil))))
    (.node (1588, [2, 2, 397])
      (.node (1579, [1579])
        (.node (1576, [2, 2, 2, 197]) (.node (1574, [2, 787]) .nil .nil)
          (.node (1577, [19, 83]) .nil .nil))
        (.node (1585, [5, 317]) (.node (1583, [1583]) .nil .nil)
          (.node (1587, [3, 23, 23]) .nil .nil)))
      (.node (1593, [3, 3, 3, 59])
        (.node (1591, [37, 43]) (.node (1589, [7, 227]) .nil .nil)
          (.node (1592, [2, 2, 2, 199]) .nil .nil))
        (.node (1597, [1597]) (.node (1594, [2, 797]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree12 : BinaryTree (ℕ × List ℕ) :=
  .node (1544, [2, 2, 2, 193]) routeSubtree10 routeSubtree11

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree13 : BinaryTree (ℕ × List ℕ) :=
  .node (1492, [2, 2, 373]) routeSubtree9 routeSubtree12

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree14 : BinaryTree (ℕ × List ℕ) :=
  .node (1383, [3, 461]) routeSubtree6 routeSubtree13

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree15 : BinaryTree (ℕ × List ℕ) :=
  (.node (1629, [3, 3, 181])
    (.node (1616, [2, 2, 2, 2, 101])
      (.node (1607, [1607])
        (.node (1603, [7, 229]) (.node (1601, [1601]) .nil .nil)
          (.node (1604, [2, 2, 401]) .nil .nil))
        (.node (1611, [3, 3, 179]) (.node (1609, [1609]) .nil .nil)
          (.node (1613, [1613]) .nil .nil)))
      (.node (1622, [2, 811])
        (.node (1619, [1619]) (.node (1618, [2, 809]) .nil .nil) (.node (1621, [1621]) .nil .nil))
        (.node (1625, [5, 5, 5, 13]) (.node (1623, [3, 541]) .nil .nil)
          (.node (1627, [1627]) .nil .nil))))
    (.node (1643, [31, 53])
      (.node (1637, [1637])
        (.node (1633, [23, 71]) (.node (1631, [7, 233]) .nil .nil)
          (.node (1636, [2, 2, 409]) .nil .nil))
        (.node (1641, [3, 547]) (.node (1639, [11, 149]) .nil .nil)
          (.node (1642, [2, 821]) .nil .nil)))
      (.node (1649, [17, 97])
        (.node (1647, [3, 3, 3, 61]) (.node (1646, [2, 823]) .nil .nil)
          (.node (1648, [2, 2, 2, 2, 103]) .nil .nil))
        (.node (1654, [2, 827]) (.node (1651, [13, 127]) .nil .nil)
          (.node (1655, [5, 331]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree16 : BinaryTree (ℕ × List ℕ) :=
  (.node (1685, [5, 337])
    (.node (1673, [7, 239])
      (.node (1664, [2, 2, 2, 2, 2, 2, 2, 13])
        (.node (1661, [11, 151]) (.node (1658, [2, 829]) .nil .nil)
          (.node (1663, [1663]) .nil .nil))
        (.node (1669, [1669]) (.node (1667, [1667]) .nil .nil) (.node (1671, [3, 557]) .nil .nil)))
      (.node (1679, [23, 73])
        (.node (1676, [2, 2, 419]) (.node (1675, [5, 5, 67]) .nil .nil)
          (.node (1678, [2, 839]) .nil .nil))
        (.node (1682, [2, 29, 29]) (.node (1681, [41, 41]) .nil .nil)
          (.node (1684, [2, 2, 421]) .nil .nil))))
    (.node (1699, [1699])
      (.node (1691, [19, 89])
        (.node (1688, [2, 2, 2, 211]) (.node (1687, [7, 241]) .nil .nil)
          (.node (1689, [3, 563]) .nil .nil))
        (.node (1696, [2, 2, 2, 2, 2, 53]) (.node (1693, [1693]) .nil .nil)
          (.node (1697, [1697]) .nil .nil)))
      (.node (1707, [3, 569])
        (.node (1703, [13, 131]) (.node (1701, [3, 3, 3, 3, 3, 7]) .nil .nil)
          (.node (1706, [2, 853]) .nil .nil))
        (.node (1711, [29, 59]) (.node (1709, [1709]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree17 : BinaryTree (ℕ × List ℕ) :=
  .node (1657, [1657]) routeSubtree15 routeSubtree16

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree18 : BinaryTree (ℕ × List ℕ) :=
  (.node (1735, [5, 347])
    (.node (1723, [1723])
      (.node (1717, [17, 101])
        (.node (1714, [2, 857]) (.node (1713, [3, 571]) .nil .nil)
          (.node (1715, [5, 7, 7, 7]) .nil .nil))
        (.node (1719, [3, 3, 191]) (.node (1718, [2, 859]) .nil .nil)
          (.node (1721, [1721]) .nil .nil)))
      (.node (1728, [2, 2, 2, 2, 2, 2, 3, 3, 3])
        (.node (1726, [2, 863]) (.node (1724, [2, 2, 431]) .nil .nil)
          (.node (1727, [11, 157]) .nil .nil))
        (.node (1732, [2, 2, 433]) (.node (1731, [3, 577]) .nil .nil)
          (.node (1733, [1733]) .nil .nil))))
    (.node (1753, [1753])
      (.node (1744, [2, 2, 2, 2, 109])
        (.node (1739, [37, 47]) (.node (1737, [3, 3, 193]) .nil .nil)
          (.node (1741, [1741]) .nil .nil))
        (.node (1747, [1747]) (.node (1745, [5, 349]) .nil .nil)
          (.node (1751, [17, 103]) .nil .nil)))
      (.node (1759, [1759])
        (.node (1756, [2, 2, 439]) (.node (1754, [2, 877]) .nil .nil)
          (.node (1757, [7, 251]) .nil .nil))
        (.node (1762, [2, 881]) (.node (1761, [3, 587]) .nil .nil)
          (.node (1763, [41, 43]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree19 : BinaryTree (ℕ × List ℕ) :=
  (.node (1793, [11, 163])
    (.node (1779, [3, 593])
      (.node (1773, [3, 3, 197])
        (.node (1769, [29, 61]) (.node (1766, [2, 883]) .nil .nil)
          (.node (1772, [2, 2, 443]) .nil .nil))
        (.node (1775, [5, 5, 71]) (.node (1774, [2, 887]) .nil .nil)
          (.node (1777, [1777]) .nil .nil)))
      (.node (1787, [1787])
        (.node (1783, [1783]) (.node (1781, [13, 137]) .nil .nil)
          (.node (1784, [2, 2, 2, 223]) .nil .nil))
        (.node (1791, [3, 3, 199]) (.node (1789, [1789]) .nil .nil)
          (.node (1792, [2, 2, 2, 2, 2, 2, 2, 2, 7]) .nil .nil))))
    (.node (1807, [13, 139])
      (.node (1799, [7, 257])
        (.node (1796, [2, 2, 449]) (.node (1795, [5, 359]) .nil .nil)
          (.node (1797, [3, 599]) .nil .nil))
        (.node (1803, [3, 601]) (.node (1801, [1801]) .nil .nil)
          (.node (1805, [5, 19, 19]) .nil .nil)))
      (.node (1813, [7, 7, 37])
        (.node (1809, [3, 3, 3, 67]) (.node (1808, [2, 2, 2, 2, 113]) .nil .nil)
          (.node (1811, [1811]) .nil .nil))
        (.node (1816, [2, 2, 2, 227]) (.node (1814, [2, 907]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree20 : BinaryTree (ℕ × List ℕ) :=
  .node (1765, [5, 353]) routeSubtree18 routeSubtree19

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree21 : BinaryTree (ℕ × List ℕ) :=
  .node (1712, [2, 2, 2, 2, 107]) routeSubtree17 routeSubtree20

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree22 : BinaryTree (ℕ × List ℕ) :=
  (.node (1844, [2, 2, 461])
    (.node (1831, [1831])
      (.node (1823, [1823])
        (.node (1821, [3, 607]) (.node (1819, [17, 107]) .nil .nil)
          (.node (1822, [2, 911]) .nil .nil))
        (.node (1828, [2, 2, 457]) (.node (1825, [5, 5, 73]) .nil .nil)
          (.node (1829, [31, 59]) .nil .nil)))
      (.node (1838, [2, 919])
        (.node (1835, [5, 367]) (.node (1832, [2, 2, 2, 229]) .nil .nil)
          (.node (1837, [11, 167]) .nil .nil))
        (.node (1841, [7, 263]) (.node (1839, [3, 613]) .nil .nil)
          (.node (1843, [19, 97]) .nil .nil))))
    (.node (1858, [2, 929])
      (.node (1852, [2, 2, 463])
        (.node (1849, [43, 43]) (.node (1847, [1847]) .nil .nil) (.node (1851, [3, 617]) .nil .nil))
        (.node (1856, [2, 2, 2, 2, 2, 2, 29]) (.node (1853, [17, 109]) .nil .nil)
          (.node (1857, [3, 619]) .nil .nil)))
      (.node (1864, [2, 2, 2, 233])
        (.node (1861, [1861]) (.node (1859, [11, 13, 13]) .nil .nil)
          (.node (1863, [3, 3, 3, 3, 23]) .nil .nil))
        (.node (1867, [1867]) (.node (1865, [5, 373]) .nil .nil)
          (.node (1868, [2, 2, 467]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree23 : BinaryTree (ℕ × List ℕ) :=
  (.node (1901, [1901])
    (.node (1888, [2, 2, 2, 2, 2, 59])
      (.node (1877, [1877])
        (.node (1874, [2, 937]) (.node (1873, [1873]) .nil .nil)
          (.node (1875, [3, 5, 5, 5, 5]) .nil .nil))
        (.node (1882, [2, 941]) (.node (1879, [1879]) .nil .nil)
          (.node (1883, [7, 269]) .nil .nil)))
      (.node (1894, [2, 947])
        (.node (1891, [31, 61]) (.node (1889, [1889]) .nil .nil) (.node (1893, [3, 631]) .nil .nil))
        (.node (1897, [7, 271]) (.node (1895, [5, 379]) .nil .nil)
          (.node (1899, [3, 3, 211]) .nil .nil))))
    (.node (1916, [2, 2, 479])
      (.node (1909, [23, 83])
        (.node (1906, [2, 953]) (.node (1903, [11, 173]) .nil .nil)
          (.node (1907, [1907]) .nil .nil))
        (.node (1913, [1913]) (.node (1912, [2, 2, 2, 239]) .nil .nil)
          (.node (1915, [5, 383]) .nil .nil)))
      (.node (1922, [2, 31, 31])
        (.node (1919, [19, 101]) (.node (1917, [3, 3, 3, 71]) .nil .nil)
          (.node (1921, [17, 113]) .nil .nil))
        (.node (1927, [41, 47]) (.node (1923, [3, 641]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree24 : BinaryTree (ℕ × List ℕ) :=
  .node (1871, [1871]) routeSubtree22 routeSubtree23

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree25 : BinaryTree (ℕ × List ℕ) :=
  (.node (1952, [2, 2, 2, 2, 2, 61])
    (.node (1941, [3, 647])
      (.node (1934, [2, 967])
        (.node (1931, [1931]) (.node (1929, [3, 643]) .nil .nil) (.node (1933, [1933]) .nil .nil))
        (.node (1937, [13, 149]) (.node (1936, [2, 2, 2, 2, 11, 11]) .nil .nil)
          (.node (1939, [7, 277]) .nil .nil)))
      (.node (1945, [5, 389])
        (.node (1943, [29, 67]) (.node (1942, [2, 971]) .nil .nil)
          (.node (1944, [2, 2, 2, 3, 3, 3, 3, 3]) .nil .nil))
        (.node (1949, [1949]) (.node (1948, [2, 2, 487]) .nil .nil)
          (.node (1951, [1951]) .nil .nil))))
    (.node (1967, [7, 281])
      (.node (1961, [37, 53])
        (.node (1957, [19, 103]) (.node (1954, [2, 977]) .nil .nil)
          (.node (1959, [3, 653]) .nil .nil))
        (.node (1964, [2, 2, 491]) (.node (1963, [13, 151]) .nil .nil)
          (.node (1966, [2, 983]) .nil .nil)))
      (.node (1975, [5, 5, 79])
        (.node (1971, [3, 3, 3, 73]) (.node (1969, [11, 179]) .nil .nil)
          (.node (1973, [1973]) .nil .nil))
        (.node (1979, [1979]) (.node (1977, [3, 659]) .nil .nil)
          (.node (1981, [7, 283]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree26 : BinaryTree (ℕ × List ℕ) :=
  (.node (2009, [7, 7, 41])
    (.node (1996, [2, 2, 499])
      (.node (1987, [1987])
        (.node (1984, [2, 2, 2, 2, 2, 2, 31]) (.node (1983, [3, 661]) .nil .nil)
          (.node (1985, [5, 397]) .nil .nil))
        (.node (1993, [1993]) (.node (1991, [11, 181]) .nil .nil)
          (.node (1994, [2, 997]) .nil .nil)))
      (.node (2003, [2003])
        (.node (1999, [1999]) (.node (1997, [1997]) .nil .nil)
          (.node (2000, [2, 2, 2, 2, 5, 5, 5]) .nil .nil))
        (.node (2007, [3, 3, 223]) (.node (2005, [5, 401]) .nil .nil)
          (.node (2008, [2, 2, 2, 251]) .nil .nil))))
    (.node (2025, [3, 3, 3, 3, 5, 5])
      (.node (2018, [2, 1009])
        (.node (2012, [2, 2, 503]) (.node (2011, [2011]) .nil .nil)
          (.node (2017, [2017]) .nil .nil))
        (.node (2021, [43, 47]) (.node (2019, [3, 673]) .nil .nil)
          (.node (2023, [7, 17, 17]) .nil .nil)))
      (.node (2031, [3, 677])
        (.node (2027, [2027]) (.node (2026, [2, 1013]) .nil .nil) (.node (2029, [2029]) .nil .nil))
        (.node (2033, [19, 107]) (.node (2032, [2, 2, 2, 2, 127]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree27 : BinaryTree (ℕ × List ℕ) :=
  .node (1982, [2, 991]) routeSubtree25 routeSubtree26

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree28 : BinaryTree (ℕ × List ℕ) :=
  .node (1928, [2, 2, 2, 241]) routeSubtree24 routeSubtree27

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree29 : BinaryTree (ℕ × List ℕ) :=
  .node (1817, [23, 79]) routeSubtree21 routeSubtree28

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree30 : BinaryTree (ℕ × List ℕ) :=
  .node (1600, [2, 2, 2, 2, 2, 2, 5, 5]) routeSubtree14 routeSubtree29

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree31 : BinaryTree (ℕ × List ℕ) :=
  (.node (2062, [2, 1031])
    (.node (2048, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])
      (.node (2042, [2, 1021])
        (.node (2039, [2039]) (.node (2038, [2, 1019]) .nil .nil)
          (.node (2041, [13, 157]) .nil .nil))
        (.node (2045, [5, 409]) (.node (2043, [3, 3, 227]) .nil .nil)
          (.node (2047, [23, 89]) .nil .nil)))
      (.node (2056, [2, 2, 2, 257])
        (.node (2051, [7, 293]) (.node (2049, [3, 683]) .nil .nil) (.node (2053, [2053]) .nil .nil))
        (.node (2059, [29, 71]) (.node (2057, [11, 11, 17]) .nil .nil)
          (.node (2061, [3, 3, 229]) .nil .nil))))
    (.node (2078, [2, 1039])
      (.node (2071, [19, 109])
        (.node (2066, [2, 1033]) (.node (2063, [2063]) .nil .nil) (.node (2069, [2069]) .nil .nil))
        (.node (2075, [5, 5, 83]) (.node (2073, [3, 691]) .nil .nil)
          (.node (2077, [31, 67]) .nil .nil)))
      (.node (2087, [2087])
        (.node (2083, [2083]) (.node (2081, [2081]) .nil .nil)
          (.node (2084, [2, 2, 521]) .nil .nil))
        (.node (2092, [2, 2, 523]) (.node (2089, [2089]) .nil .nil)
          (.node (2095, [5, 419]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree32 : BinaryTree (ℕ × List ℕ) :=
  (.node (2113, [2113])
    (.node (2105, [5, 421])
      (.node (2101, [11, 191])
        (.node (2098, [2, 1049]) (.node (2097, [3, 3, 233]) .nil .nil)
          (.node (2099, [2099]) .nil .nil))
        (.node (2103, [3, 701]) (.node (2102, [2, 1051]) .nil .nil)
          (.node (2104, [2, 2, 2, 263]) .nil .nil)))
      (.node (2109, [3, 19, 37])
        (.node (2107, [7, 7, 43]) (.node (2106, [2, 3, 3, 3, 3, 13]) .nil .nil)
          (.node (2108, [2, 2, 17, 31]) .nil .nil))
        (.node (2111, [2111]) (.node (2110, [2, 5, 211]) .nil .nil)
          (.node (2112, [2, 2, 2, 2, 2, 2, 3, 11]) .nil .nil))))
    (.node (2121, [3, 7, 101])
      (.node (2117, [29, 73])
        (.node (2115, [3, 3, 5, 47]) (.node (2114, [2, 7, 151]) .nil .nil)
          (.node (2116, [2, 2, 23, 23]) .nil .nil))
        (.node (2119, [13, 163]) (.node (2118, [2, 3, 353]) .nil .nil)
          (.node (2120, [2, 2, 2, 5, 53]) .nil .nil)))
      (.node (2125, [5, 5, 5, 17])
        (.node (2123, [11, 193]) (.node (2122, [2, 1061]) .nil .nil)
          (.node (2124, [2, 2, 3, 3, 59]) .nil .nil))
        (.node (2127, [3, 709]) (.node (2126, [2, 1063]) .nil .nil)
          (.node (2128, [2, 2, 2, 2, 7, 19]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree33 : BinaryTree (ℕ × List ℕ) :=
  .node (2096, [2, 2, 2, 2, 131]) routeSubtree31 routeSubtree32

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree34 : BinaryTree (ℕ × List ℕ) :=
  (.node (2148, [2, 2, 3, 179])
    (.node (2138, [2, 1069])
      (.node (2134, [2, 11, 97])
        (.node (2132, [2, 2, 13, 41]) (.node (2131, [2131]) .nil .nil)
          (.node (2133, [3, 3, 3, 79]) .nil .nil))
        (.node (2136, [2, 2, 2, 3, 89]) (.node (2135, [5, 7, 61]) .nil .nil)
          (.node (2137, [2137]) .nil .nil)))
      (.node (2143, [2143])
        (.node (2140, [2, 2, 5, 107]) (.node (2139, [3, 23, 31]) .nil .nil)
          (.node (2141, [2141]) .nil .nil))
        (.node (2146, [2, 29, 37]) (.node (2144, [2, 2, 2, 2, 2, 67]) .nil .nil)
          (.node (2147, [19, 113]) .nil .nil))))
    (.node (2156, [2, 2, 7, 7, 11])
      (.node (2152, [2, 2, 2, 269])
        (.node (2150, [2, 5, 5, 43]) (.node (2149, [7, 307]) .nil .nil)
          (.node (2151, [3, 3, 239]) .nil .nil))
        (.node (2154, [2, 3, 359]) (.node (2153, [2153]) .nil .nil)
          (.node (2155, [5, 431]) .nil .nil)))
      (.node (2160, [2, 2, 2, 2, 3, 3, 3, 5])
        (.node (2158, [2, 13, 83]) (.node (2157, [3, 719]) .nil .nil)
          (.node (2159, [17, 127]) .nil .nil))
        (.node (2162, [2, 23, 47]) (.node (2161, [2161]) .nil .nil)
          (.node (2163, [3, 7, 103]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree35 : BinaryTree (ℕ × List ℕ) :=
  (.node (2181, [3, 727])
    (.node (2173, [41, 53])
      (.node (2168, [2, 2, 2, 271])
        (.node (2166, [2, 3, 19, 19]) (.node (2165, [5, 433]) .nil .nil)
          (.node (2167, [11, 197]) .nil .nil))
        (.node (2171, [13, 167]) (.node (2169, [3, 3, 241]) .nil .nil)
          (.node (2172, [2, 2, 3, 181]) .nil .nil)))
      (.node (2177, [7, 311])
        (.node (2175, [3, 5, 5, 29]) (.node (2174, [2, 1087]) .nil .nil)
          (.node (2176, [2, 2, 2, 2, 2, 2, 2, 17]) .nil .nil))
        (.node (2179, [2179]) (.node (2178, [2, 3, 3, 11, 11]) .nil .nil)
          (.node (2180, [2, 2, 5, 109]) .nil .nil))))
    (.node (2191, [7, 313])
      (.node (2186, [2, 1093])
        (.node (2183, [37, 59]) (.node (2182, [2, 1091]) .nil .nil)
          (.node (2185, [5, 19, 23]) .nil .nil))
        (.node (2188, [2, 2, 547]) (.node (2187, [3, 3, 3, 3, 3, 3, 3]) .nil .nil)
          (.node (2189, [11, 199]) .nil .nil)))
      (.node (2195, [5, 439])
        (.node (2193, [3, 17, 43]) (.node (2192, [2, 2, 2, 2, 137]) .nil .nil)
          (.node (2194, [2, 1097]) .nil .nil))
        (.node (2197, [13, 13, 13]) (.node (2196, [2, 2, 3, 3, 61]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree36 : BinaryTree (ℕ × List ℕ) :=
  .node (2164, [2, 2, 541]) routeSubtree34 routeSubtree35

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree37 : BinaryTree (ℕ × List ℕ) :=
  .node (2129, [2129]) routeSubtree33 routeSubtree36

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree38 : BinaryTree (ℕ × List ℕ) :=
  (.node (2215, [5, 443])
    (.node (2206, [2, 1103])
      (.node (2202, [2, 3, 367])
        (.node (2200, [2, 2, 2, 5, 5, 11]) (.node (2199, [3, 733]) .nil .nil)
          (.node (2201, [31, 71]) .nil .nil))
        (.node (2204, [2, 2, 19, 29]) (.node (2203, [2203]) .nil .nil)
          (.node (2205, [3, 3, 5, 7, 7]) .nil .nil)))
      (.node (2211, [3, 11, 67])
        (.node (2208, [2, 2, 2, 2, 2, 3, 23]) (.node (2207, [2207]) .nil .nil)
          (.node (2209, [47, 47]) .nil .nil))
        (.node (2213, [2213]) (.node (2212, [2, 2, 7, 79]) .nil .nil)
          (.node (2214, [2, 3, 3, 3, 41]) .nil .nil))))
    (.node (2224, [2, 2, 2, 2, 139])
      (.node (2219, [7, 317])
        (.node (2217, [3, 739]) (.node (2216, [2, 2, 2, 277]) .nil .nil)
          (.node (2218, [2, 1109]) .nil .nil))
        (.node (2222, [2, 11, 101]) (.node (2221, [2221]) .nil .nil)
          (.node (2223, [3, 3, 13, 19]) .nil .nil)))
      (.node (2229, [3, 743])
        (.node (2227, [17, 131]) (.node (2225, [5, 5, 89]) .nil .nil)
          (.node (2228, [2, 2, 557]) .nil .nil))
        (.node (2231, [23, 97]) (.node (2230, [2, 5, 223]) .nil .nil)
          (.node (2232, [2, 2, 2, 3, 3, 31]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree39 : BinaryTree (ℕ × List ℕ) :=
  (.node (2250, [2, 3, 3, 5, 5, 5])
    (.node (2241, [3, 3, 3, 83])
      (.node (2237, [2237])
        (.node (2235, [3, 5, 149]) (.node (2234, [2, 1117]) .nil .nil)
          (.node (2236, [2, 2, 13, 43]) .nil .nil))
        (.node (2239, [2239]) (.node (2238, [2, 3, 373]) .nil .nil)
          (.node (2240, [2, 2, 2, 2, 2, 2, 5, 7]) .nil .nil)))
      (.node (2246, [2, 1123])
        (.node (2243, [2243]) (.node (2242, [2, 19, 59]) .nil .nil)
          (.node (2245, [5, 449]) .nil .nil))
        (.node (2248, [2, 2, 2, 281]) (.node (2247, [3, 7, 107]) .nil .nil)
          (.node (2249, [13, 173]) .nil .nil))))
    (.node (2258, [2, 1129])
      (.node (2254, [2, 7, 7, 23])
        (.node (2252, [2, 2, 563]) (.node (2251, [2251]) .nil .nil)
          (.node (2253, [3, 751]) .nil .nil))
        (.node (2256, [2, 2, 2, 2, 3, 47]) (.node (2255, [5, 11, 41]) .nil .nil)
          (.node (2257, [37, 61]) .nil .nil)))
      (.node (2263, [31, 73])
        (.node (2260, [2, 2, 5, 113]) (.node (2259, [3, 3, 251]) .nil .nil)
          (.node (2261, [7, 17, 19]) .nil .nil))
        (.node (2265, [3, 5, 151]) (.node (2264, [2, 2, 2, 283]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree40 : BinaryTree (ℕ × List ℕ) :=
  .node (2233, [7, 11, 29]) routeSubtree38 routeSubtree39

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree41 : BinaryTree (ℕ × List ℕ) :=
  (.node (2283, [3, 761])
    (.node (2274, [2, 3, 379])
      (.node (2270, [2, 5, 227])
        (.node (2268, [2, 2, 3, 3, 3, 3, 7]) (.node (2267, [2267]) .nil .nil)
          (.node (2269, [2269]) .nil .nil))
        (.node (2272, [2, 2, 2, 2, 2, 71]) (.node (2271, [3, 757]) .nil .nil)
          (.node (2273, [2273]) .nil .nil)))
      (.node (2278, [2, 17, 67])
        (.node (2276, [2, 2, 569]) (.node (2275, [5, 5, 7, 13]) .nil .nil)
          (.node (2277, [3, 3, 11, 23]) .nil .nil))
        (.node (2281, [2281]) (.node (2279, [43, 53]) .nil .nil)
          (.node (2282, [2, 7, 163]) .nil .nil))))
    (.node (2291, [29, 79])
      (.node (2287, [2287])
        (.node (2285, [5, 457]) (.node (2284, [2, 2, 571]) .nil .nil)
          (.node (2286, [2, 3, 3, 127]) .nil .nil))
        (.node (2289, [3, 7, 109]) (.node (2288, [2, 2, 2, 2, 11, 13]) .nil .nil)
          (.node (2290, [2, 5, 229]) .nil .nil)))
      (.node (2295, [3, 3, 3, 5, 17])
        (.node (2293, [2293]) (.node (2292, [2, 2, 3, 191]) .nil .nil)
          (.node (2294, [2, 31, 37]) .nil .nil))
        (.node (2297, [2297]) (.node (2296, [2, 2, 2, 7, 41]) .nil .nil)
          (.node (2298, [2, 3, 383]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree42 : BinaryTree (ℕ × List ℕ) :=
  (.node (2316, [2, 2, 3, 193])
    (.node (2307, [3, 769])
      (.node (2303, [7, 7, 47])
        (.node (2301, [3, 13, 59]) (.node (2300, [2, 2, 5, 5, 23]) .nil .nil)
          (.node (2302, [2, 1151]) .nil .nil))
        (.node (2305, [5, 461]) (.node (2304, [2, 2, 2, 2, 2, 2, 2, 2, 3, 3]) .nil .nil)
          (.node (2306, [2, 1153]) .nil .nil)))
      (.node (2312, [2, 2, 2, 17, 17])
        (.node (2309, [2309]) (.node (2308, [2, 2, 577]) .nil .nil)
          (.node (2311, [2311]) .nil .nil))
        (.node (2314, [2, 13, 89]) (.node (2313, [3, 3, 257]) .nil .nil)
          (.node (2315, [5, 463]) .nil .nil))))
    (.node (2324, [2, 2, 7, 83])
      (.node (2320, [2, 2, 2, 2, 5, 29])
        (.node (2318, [2, 19, 61]) (.node (2317, [7, 331]) .nil .nil)
          (.node (2319, [3, 773]) .nil .nil))
        (.node (2322, [2, 3, 3, 3, 43]) (.node (2321, [11, 211]) .nil .nil)
          (.node (2323, [23, 101]) .nil .nil)))
      (.node (2328, [2, 2, 2, 3, 97])
        (.node (2326, [2, 1163]) (.node (2325, [3, 5, 5, 31]) .nil .nil)
          (.node (2327, [13, 179]) .nil .nil))
        (.node (2330, [2, 5, 233]) (.node (2329, [17, 137]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree43 : BinaryTree (ℕ × List ℕ) :=
  .node (2299, [11, 11, 19]) routeSubtree41 routeSubtree42

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree44 : BinaryTree (ℕ × List ℕ) :=
  .node (2266, [2, 11, 103]) routeSubtree40 routeSubtree43

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree45 : BinaryTree (ℕ × List ℕ) :=
  .node (2198, [2, 7, 157]) routeSubtree37 routeSubtree44

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree46 : BinaryTree (ℕ × List ℕ) :=
  (.node (2349, [3, 3, 3, 3, 29])
    (.node (2339, [2339])
      (.node (2335, [5, 467])
        (.node (2333, [2333]) (.node (2332, [2, 2, 11, 53]) .nil .nil)
          (.node (2334, [2, 3, 389]) .nil .nil))
        (.node (2337, [3, 19, 41]) (.node (2336, [2, 2, 2, 2, 2, 73]) .nil .nil)
          (.node (2338, [2, 7, 167]) .nil .nil)))
      (.node (2344, [2, 2, 2, 293])
        (.node (2342, [2, 1171]) (.node (2341, [2341]) .nil .nil)
          (.node (2343, [3, 11, 71]) .nil .nil))
        (.node (2347, [2347]) (.node (2345, [5, 7, 67]) .nil .nil)
          (.node (2348, [2, 2, 587]) .nil .nil))))
    (.node (2357, [2357])
      (.node (2353, [13, 181])
        (.node (2351, [2351]) (.node (2350, [2, 5, 5, 47]) .nil .nil)
          (.node (2352, [2, 2, 2, 2, 3, 7, 7]) .nil .nil))
        (.node (2355, [3, 5, 157]) (.node (2354, [2, 11, 107]) .nil .nil)
          (.node (2356, [2, 2, 19, 31]) .nil .nil)))
      (.node (2361, [3, 787])
        (.node (2359, [7, 337]) (.node (2358, [2, 3, 3, 131]) .nil .nil)
          (.node (2360, [2, 2, 2, 5, 59]) .nil .nil))
        (.node (2363, [17, 139]) (.node (2362, [2, 1181]) .nil .nil)
          (.node (2364, [2, 2, 3, 197]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree47 : BinaryTree (ℕ × List ℕ) :=
  (.node (2383, [2383])
    (.node (2374, [2, 1187])
      (.node (2369, [23, 103])
        (.node (2367, [3, 3, 263]) (.node (2366, [2, 7, 13, 13]) .nil .nil)
          (.node (2368, [2, 2, 2, 2, 2, 2, 37]) .nil .nil))
        (.node (2372, [2, 2, 593]) (.node (2371, [2371]) .nil .nil)
          (.node (2373, [3, 7, 113]) .nil .nil)))
      (.node (2378, [2, 29, 41])
        (.node (2376, [2, 2, 2, 3, 3, 3, 11]) (.node (2375, [5, 5, 5, 19]) .nil .nil)
          (.node (2377, [2377]) .nil .nil))
        (.node (2381, [2381]) (.node (2379, [3, 13, 61]) .nil .nil)
          (.node (2382, [2, 3, 397]) .nil .nil))))
    (.node (2391, [3, 797])
      (.node (2387, [7, 11, 31])
        (.node (2385, [3, 3, 5, 53]) (.node (2384, [2, 2, 2, 2, 149]) .nil .nil)
          (.node (2386, [2, 1193]) .nil .nil))
        (.node (2389, [2389]) (.node (2388, [2, 2, 3, 199]) .nil .nil)
          (.node (2390, [2, 5, 239]) .nil .nil)))
      (.node (2396, [2, 2, 599])
        (.node (2393, [2393]) (.node (2392, [2, 2, 2, 13, 23]) .nil .nil)
          (.node (2395, [5, 479]) .nil .nil))
        (.node (2398, [2, 11, 109]) (.node (2397, [3, 17, 47]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree48 : BinaryTree (ℕ × List ℕ) :=
  .node (2365, [5, 11, 43]) routeSubtree46 routeSubtree47

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree49 : BinaryTree (ℕ × List ℕ) :=
  (.node (2416, [2, 2, 2, 2, 151])
    (.node (2407, [29, 83])
      (.node (2403, [3, 3, 3, 89])
        (.node (2401, [7, 7, 7, 7]) (.node (2400, [2, 2, 2, 2, 2, 3, 5, 5]) .nil .nil)
          (.node (2402, [2, 1201]) .nil .nil))
        (.node (2405, [5, 13, 37]) (.node (2404, [2, 2, 601]) .nil .nil)
          (.node (2406, [2, 3, 401]) .nil .nil)))
      (.node (2411, [2411])
        (.node (2409, [3, 11, 73]) (.node (2408, [2, 2, 2, 7, 43]) .nil .nil)
          (.node (2410, [2, 5, 241]) .nil .nil))
        (.node (2413, [19, 127]) (.node (2412, [2, 2, 3, 3, 67]) .nil .nil)
          (.node (2414, [2, 17, 71]) .nil .nil))))
    (.node (2425, [5, 5, 97])
      (.node (2421, [3, 3, 269])
        (.node (2419, [41, 59]) (.node (2417, [2417]) .nil .nil)
          (.node (2420, [2, 2, 5, 11, 11]) .nil .nil))
        (.node (2423, [2423]) (.node (2422, [2, 7, 173]) .nil .nil)
          (.node (2424, [2, 2, 2, 3, 101]) .nil .nil)))
      (.node (2429, [7, 347])
        (.node (2427, [3, 809]) (.node (2426, [2, 1213]) .nil .nil)
          (.node (2428, [2, 2, 607]) .nil .nil))
        (.node (2431, [11, 13, 17]) (.node (2430, [2, 3, 3, 3, 3, 3, 5]) .nil .nil)
          (.node (2432, [2, 2, 2, 2, 2, 2, 2, 19]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree50 : BinaryTree (ℕ × List ℕ) :=
  (.node (2451, [3, 19, 43])
    (.node (2443, [7, 349])
      (.node (2438, [2, 23, 53])
        (.node (2435, [5, 487]) (.node (2434, [2, 1217]) .nil .nil)
          (.node (2437, [2437]) .nil .nil))
        (.node (2440, [2, 2, 2, 5, 61]) (.node (2439, [3, 3, 271]) .nil .nil)
          (.node (2441, [2441]) .nil .nil)))
      (.node (2447, [2447])
        (.node (2445, [3, 5, 163]) (.node (2444, [2, 2, 13, 47]) .nil .nil)
          (.node (2446, [2, 1223]) .nil .nil))
        (.node (2449, [31, 79]) (.node (2448, [2, 2, 2, 2, 3, 3, 17]) .nil .nil)
          (.node (2450, [2, 5, 5, 7, 7]) .nil .nil))))
    (.node (2459, [2459])
      (.node (2455, [5, 491])
        (.node (2453, [11, 223]) (.node (2452, [2, 2, 613]) .nil .nil)
          (.node (2454, [2, 3, 409]) .nil .nil))
        (.node (2457, [3, 3, 3, 7, 13]) (.node (2456, [2, 2, 2, 307]) .nil .nil)
          (.node (2458, [2, 1229]) .nil .nil)))
      (.node (2464, [2, 2, 2, 2, 2, 7, 11])
        (.node (2462, [2, 1231]) (.node (2461, [23, 107]) .nil .nil)
          (.node (2463, [3, 821]) .nil .nil))
        (.node (2466, [2, 3, 3, 137]) (.node (2465, [5, 17, 29]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree51 : BinaryTree (ℕ × List ℕ) :=
  .node (2433, [3, 811]) routeSubtree49 routeSubtree50

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree52 : BinaryTree (ℕ × List ℕ) :=
  .node (2399, [2399]) routeSubtree48 routeSubtree51

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree53 : BinaryTree (ℕ × List ℕ) :=
  (.node (2485, [5, 7, 71])
    (.node (2476, [2, 2, 619])
      (.node (2472, [2, 2, 2, 3, 103])
        (.node (2469, [3, 823]) (.node (2468, [2, 2, 617]) .nil .nil)
          (.node (2471, [7, 353]) .nil .nil))
        (.node (2474, [2, 1237]) (.node (2473, [2473]) .nil .nil)
          (.node (2475, [3, 3, 5, 5, 11]) .nil .nil)))
      (.node (2481, [3, 827])
        (.node (2479, [37, 67]) (.node (2477, [2477]) .nil .nil)
          (.node (2480, [2, 2, 2, 2, 5, 31]) .nil .nil))
        (.node (2483, [13, 191]) (.node (2482, [2, 17, 73]) .nil .nil)
          (.node (2484, [2, 2, 3, 3, 3, 23]) .nil .nil))))
    (.node (2494, [2, 29, 43])
      (.node (2489, [19, 131])
        (.node (2487, [3, 829]) (.node (2486, [2, 11, 113]) .nil .nil)
          (.node (2488, [2, 2, 2, 311]) .nil .nil))
        (.node (2492, [2, 2, 7, 89]) (.node (2491, [47, 53]) .nil .nil)
          (.node (2493, [3, 3, 277]) .nil .nil)))
      (.node (2498, [2, 1249])
        (.node (2496, [2, 2, 2, 2, 2, 2, 3, 13]) (.node (2495, [5, 499]) .nil .nil)
          (.node (2497, [11, 227]) .nil .nil))
        (.node (2500, [2, 2, 5, 5, 5, 5]) (.node (2499, [3, 7, 7, 17]) .nil .nil)
          (.node (2501, [41, 61]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree54 : BinaryTree (ℕ × List ℕ) :=
  (.node (2519, [11, 229])
    (.node (2511, [3, 3, 3, 3, 31])
      (.node (2506, [2, 7, 179])
        (.node (2504, [2, 2, 2, 313]) (.node (2503, [2503]) .nil .nil)
          (.node (2505, [3, 5, 167]) .nil .nil))
        (.node (2509, [13, 193]) (.node (2507, [23, 109]) .nil .nil)
          (.node (2510, [2, 5, 251]) .nil .nil)))
      (.node (2515, [5, 503])
        (.node (2513, [7, 359]) (.node (2512, [2, 2, 2, 2, 157]) .nil .nil)
          (.node (2514, [2, 3, 419]) .nil .nil))
        (.node (2517, [3, 839]) (.node (2516, [2, 2, 17, 37]) .nil .nil)
          (.node (2518, [2, 1259]) .nil .nil))))
    (.node (2528, [2, 2, 2, 2, 2, 79])
      (.node (2524, [2, 2, 631])
        (.node (2522, [2, 13, 97]) (.node (2521, [2521]) .nil .nil)
          (.node (2523, [3, 29, 29]) .nil .nil))
        (.node (2526, [2, 3, 421]) (.node (2525, [5, 5, 101]) .nil .nil)
          (.node (2527, [7, 19, 19]) .nil .nil)))
      (.node (2533, [17, 149])
        (.node (2531, [2531]) (.node (2529, [3, 3, 281]) .nil .nil)
          (.node (2532, [2, 2, 3, 211]) .nil .nil))
        (.node (2535, [3, 5, 13, 13]) (.node (2534, [2, 7, 181]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree55 : BinaryTree (ℕ × List ℕ) :=
  .node (2502, [2, 3, 3, 139]) routeSubtree53 routeSubtree54

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree56 : BinaryTree (ℕ × List ℕ) :=
  (.node (2553, [3, 23, 37])
    (.node (2544, [2, 2, 2, 2, 3, 53])
      (.node (2540, [2, 2, 5, 127])
        (.node (2538, [2, 3, 3, 3, 47]) (.node (2537, [43, 59]) .nil .nil)
          (.node (2539, [2539]) .nil .nil))
        (.node (2542, [2, 31, 41]) (.node (2541, [3, 7, 11, 11]) .nil .nil)
          (.node (2543, [2543]) .nil .nil)))
      (.node (2548, [2, 2, 7, 7, 13])
        (.node (2546, [2, 19, 67]) (.node (2545, [5, 509]) .nil .nil)
          (.node (2547, [3, 3, 283]) .nil .nil))
        (.node (2551, [2551]) (.node (2549, [2549]) .nil .nil)
          (.node (2552, [2, 2, 2, 11, 29]) .nil .nil))))
    (.node (2561, [13, 197])
      (.node (2557, [2557])
        (.node (2555, [5, 7, 73]) (.node (2554, [2, 1277]) .nil .nil)
          (.node (2556, [2, 2, 3, 3, 71]) .nil .nil))
        (.node (2559, [3, 853]) (.node (2558, [2, 1279]) .nil .nil)
          (.node (2560, [2, 2, 2, 2, 2, 2, 2, 2, 2, 5]) .nil .nil)))
      (.node (2566, [2, 1283])
        (.node (2564, [2, 2, 641]) (.node (2563, [11, 233]) .nil .nil)
          (.node (2565, [3, 3, 3, 5, 19]) .nil .nil))
        (.node (2568, [2, 2, 2, 3, 107]) (.node (2567, [17, 151]) .nil .nil)
          (.node (2569, [7, 367]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree57 : BinaryTree (ℕ × List ℕ) :=
  (.node (2588, [2, 2, 647])
    (.node (2579, [2579])
      (.node (2575, [5, 5, 103])
        (.node (2572, [2, 2, 643]) (.node (2571, [3, 857]) .nil .nil)
          (.node (2573, [31, 83]) .nil .nil))
        (.node (2577, [3, 859]) (.node (2576, [2, 2, 2, 2, 7, 23]) .nil .nil)
          (.node (2578, [2, 1289]) .nil .nil)))
      (.node (2584, [2, 2, 2, 17, 19])
        (.node (2582, [2, 1291]) (.node (2581, [29, 89]) .nil .nil)
          (.node (2583, [3, 3, 7, 41]) .nil .nil))
        (.node (2586, [2, 3, 431]) (.node (2585, [5, 11, 47]) .nil .nil)
          (.node (2587, [13, 199]) .nil .nil))))
    (.node (2597, [7, 7, 53])
      (.node (2593, [2593])
        (.node (2591, [2591]) (.node (2589, [3, 863]) .nil .nil)
          (.node (2592, [2, 2, 2, 2, 2, 3, 3, 3, 3]) .nil .nil))
        (.node (2595, [3, 5, 173]) (.node (2594, [2, 1297]) .nil .nil)
          (.node (2596, [2, 2, 11, 59]) .nil .nil)))
      (.node (2601, [3, 3, 17, 17])
        (.node (2599, [23, 113]) (.node (2598, [2, 3, 433]) .nil .nil)
          (.node (2600, [2, 2, 2, 5, 5, 13]) .nil .nil))
        (.node (2603, [19, 137]) (.node (2602, [2, 1301]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree58 : BinaryTree (ℕ × List ℕ) :=
  .node (2570, [2, 5, 257]) routeSubtree56 routeSubtree57

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree59 : BinaryTree (ℕ × List ℕ) :=
  .node (2536, [2, 2, 2, 317]) routeSubtree55 routeSubtree58

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree60 : BinaryTree (ℕ × List ℕ) :=
  .node (2467, [2467]) routeSubtree52 routeSubtree59

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree61 : BinaryTree (ℕ × List ℕ) :=
  .node (2331, [3, 3, 7, 37]) routeSubtree45 routeSubtree60

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree62 : BinaryTree (ℕ × List ℕ) :=
  .node (2036, [2, 2, 509]) routeSubtree30 routeSubtree61

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree63 : BinaryTree (ℕ × List ℕ) :=
  (.node (2624, [2, 2, 2, 2, 2, 2, 41])
    (.node (2614, [2, 1307])
      (.node (2609, [2609])
        (.node (2607, [3, 11, 79]) (.node (2606, [2, 1303]) .nil .nil)
          (.node (2608, [2, 2, 2, 2, 163]) .nil .nil))
        (.node (2612, [2, 2, 653]) (.node (2611, [7, 373]) .nil .nil)
          (.node (2613, [3, 13, 67]) .nil .nil)))
      (.node (2619, [3, 3, 3, 97])
        (.node (2616, [2, 2, 2, 3, 109]) (.node (2615, [5, 523]) .nil .nil)
          (.node (2617, [2617]) .nil .nil))
        (.node (2621, [2621]) (.node (2620, [2, 2, 5, 131]) .nil .nil)
          (.node (2623, [43, 61]) .nil .nil))))
    (.node (2632, [2, 2, 2, 7, 47])
      (.node (2628, [2, 2, 3, 3, 73])
        (.node (2626, [2, 13, 101]) (.node (2625, [3, 5, 5, 5, 7]) .nil .nil)
          (.node (2627, [37, 71]) .nil .nil))
        (.node (2630, [2, 5, 263]) (.node (2629, [11, 239]) .nil .nil)
          (.node (2631, [3, 877]) .nil .nil)))
      (.node (2636, [2, 2, 659])
        (.node (2634, [2, 3, 439]) (.node (2633, [2633]) .nil .nil)
          (.node (2635, [5, 17, 31]) .nil .nil))
        (.node (2638, [2, 1319]) (.node (2637, [3, 3, 293]) .nil .nil)
          (.node (2639, [7, 13, 29]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree64 : BinaryTree (ℕ × List ℕ) :=
  (.node (2658, [2, 3, 443])
    (.node (2649, [3, 883])
      (.node (2645, [5, 23, 23])
        (.node (2643, [3, 881]) (.node (2642, [2, 1321]) .nil .nil)
          (.node (2644, [2, 2, 661]) .nil .nil))
        (.node (2647, [2647]) (.node (2646, [2, 3, 3, 3, 7, 7]) .nil .nil)
          (.node (2648, [2, 2, 2, 331]) .nil .nil)))
      (.node (2654, [2, 1327])
        (.node (2651, [11, 241]) (.node (2650, [2, 5, 5, 53]) .nil .nil)
          (.node (2653, [7, 379]) .nil .nil))
        (.node (2656, [2, 2, 2, 2, 2, 83]) (.node (2655, [3, 3, 5, 59]) .nil .nil)
          (.node (2657, [2657]) .nil .nil))))
    (.node (2667, [3, 7, 127])
      (.node (2663, [2663])
        (.node (2661, [3, 887]) (.node (2659, [2659]) .nil .nil)
          (.node (2662, [2, 11, 11, 11]) .nil .nil))
        (.node (2665, [5, 13, 41]) (.node (2664, [2, 2, 2, 3, 3, 37]) .nil .nil)
          (.node (2666, [2, 31, 43]) .nil .nil)))
      (.node (2672, [2, 2, 2, 2, 167])
        (.node (2669, [17, 157]) (.node (2668, [2, 2, 23, 29]) .nil .nil)
          (.node (2671, [2671]) .nil .nil))
        (.node (2674, [2, 7, 191]) (.node (2673, [3, 3, 3, 3, 3, 11]) .nil .nil)
          (.node (2675, [5, 5, 107]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree65 : BinaryTree (ℕ × List ℕ) :=
  .node (2641, [19, 139]) routeSubtree63 routeSubtree64

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree66 : BinaryTree (ℕ × List ℕ) :=
  (.node (2692, [2, 2, 673])
    (.node (2684, [2, 2, 11, 61])
      (.node (2680, [2, 2, 2, 5, 67])
        (.node (2678, [2, 13, 103]) (.node (2677, [2677]) .nil .nil)
          (.node (2679, [3, 19, 47]) .nil .nil))
        (.node (2682, [2, 3, 3, 149]) (.node (2681, [7, 383]) .nil .nil)
          (.node (2683, [2683]) .nil .nil)))
      (.node (2688, [2, 2, 2, 2, 2, 2, 2, 3, 7])
        (.node (2686, [2, 17, 79]) (.node (2685, [3, 5, 179]) .nil .nil)
          (.node (2687, [2687]) .nil .nil))
        (.node (2690, [2, 5, 269]) (.node (2689, [2689]) .nil .nil)
          (.node (2691, [3, 3, 13, 23]) .nil .nil))))
    (.node (2700, [2, 2, 3, 3, 3, 5, 5])
      (.node (2696, [2, 2, 2, 337])
        (.node (2694, [2, 3, 449]) (.node (2693, [2693]) .nil .nil)
          (.node (2695, [5, 7, 7, 11]) .nil .nil))
        (.node (2698, [2, 19, 71]) (.node (2697, [3, 29, 31]) .nil .nil)
          (.node (2699, [2699]) .nil .nil)))
      (.node (2704, [2, 2, 2, 2, 13, 13])
        (.node (2702, [2, 7, 193]) (.node (2701, [37, 73]) .nil .nil)
          (.node (2703, [3, 17, 53]) .nil .nil))
        (.node (2707, [2707]) (.node (2705, [5, 541]) .nil .nil)
          (.node (2708, [2, 2, 677]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree67 : BinaryTree (ℕ × List ℕ) :=
  (.node (2725, [5, 5, 109])
    (.node (2717, [11, 13, 19])
      (.node (2713, [2713])
        (.node (2711, [2711]) (.node (2710, [2, 5, 271]) .nil .nil)
          (.node (2712, [2, 2, 2, 3, 113]) .nil .nil))
        (.node (2715, [3, 5, 181]) (.node (2714, [2, 23, 59]) .nil .nil)
          (.node (2716, [2, 2, 7, 97]) .nil .nil)))
      (.node (2721, [3, 907])
        (.node (2719, [2719]) (.node (2718, [2, 3, 3, 151]) .nil .nil)
          (.node (2720, [2, 2, 2, 2, 2, 5, 17]) .nil .nil))
        (.node (2723, [7, 389]) (.node (2722, [2, 1361]) .nil .nil)
          (.node (2724, [2, 2, 3, 227]) .nil .nil))))
    (.node (2734, [2, 1367])
      (.node (2729, [2729])
        (.node (2727, [3, 3, 3, 101]) (.node (2726, [2, 29, 47]) .nil .nil)
          (.node (2728, [2, 2, 2, 11, 31]) .nil .nil))
        (.node (2732, [2, 2, 683]) (.node (2731, [2731]) .nil .nil)
          (.node (2733, [3, 911]) .nil .nil)))
      (.node (2738, [2, 37, 37])
        (.node (2736, [2, 2, 2, 2, 3, 3, 19]) (.node (2735, [5, 547]) .nil .nil)
          (.node (2737, [7, 17, 23]) .nil .nil))
        (.node (2740, [2, 2, 5, 137]) (.node (2739, [3, 11, 83]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree68 : BinaryTree (ℕ × List ℕ) :=
  .node (2709, [3, 3, 7, 43]) routeSubtree66 routeSubtree67

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree69 : BinaryTree (ℕ × List ℕ) :=
  .node (2676, [2, 2, 3, 223]) routeSubtree65 routeSubtree68

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree70 : BinaryTree (ℕ × List ℕ) :=
  (.node (2757, [3, 919])
    (.node (2749, [2749])
      (.node (2745, [3, 3, 5, 61])
        (.node (2743, [13, 211]) (.node (2742, [2, 3, 457]) .nil .nil)
          (.node (2744, [2, 2, 2, 7, 7, 7]) .nil .nil))
        (.node (2747, [41, 67]) (.node (2746, [2, 1373]) .nil .nil)
          (.node (2748, [2, 2, 3, 229]) .nil .nil)))
      (.node (2753, [2753])
        (.node (2751, [3, 7, 131]) (.node (2750, [2, 5, 5, 5, 11]) .nil .nil)
          (.node (2752, [2, 2, 2, 2, 2, 2, 43]) .nil .nil))
        (.node (2755, [5, 19, 29]) (.node (2754, [2, 3, 3, 3, 3, 17]) .nil .nil)
          (.node (2756, [2, 2, 13, 53]) .nil .nil))))
    (.node (2766, [2, 3, 461])
      (.node (2762, [2, 1381])
        (.node (2759, [31, 89]) (.node (2758, [2, 7, 197]) .nil .nil)
          (.node (2761, [11, 251]) .nil .nil))
        (.node (2764, [2, 2, 691]) (.node (2763, [3, 3, 307]) .nil .nil)
          (.node (2765, [5, 7, 79]) .nil .nil)))
      (.node (2770, [2, 5, 277])
        (.node (2768, [2, 2, 2, 2, 173]) (.node (2767, [2767]) .nil .nil)
          (.node (2769, [3, 13, 71]) .nil .nil))
        (.node (2773, [47, 59]) (.node (2771, [17, 163]) .nil .nil)
          (.node (2774, [2, 19, 73]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree71 : BinaryTree (ℕ × List ℕ) :=
  (.node (2792, [2, 2, 2, 349])
    (.node (2783, [11, 11, 23])
      (.node (2779, [7, 397])
        (.node (2777, [2777]) (.node (2776, [2, 2, 2, 347]) .nil .nil)
          (.node (2778, [2, 3, 463]) .nil .nil))
        (.node (2781, [3, 3, 3, 103]) (.node (2780, [2, 2, 5, 139]) .nil .nil)
          (.node (2782, [2, 13, 107]) .nil .nil)))
      (.node (2787, [3, 929])
        (.node (2785, [5, 557]) (.node (2784, [2, 2, 2, 2, 2, 3, 29]) .nil .nil)
          (.node (2786, [2, 7, 199]) .nil .nil))
        (.node (2789, [2789]) (.node (2788, [2, 2, 17, 41]) .nil .nil)
          (.node (2791, [2791]) .nil .nil))))
    (.node (2800, [2, 2, 2, 2, 5, 5, 7])
      (.node (2796, [2, 2, 3, 233])
        (.node (2794, [2, 11, 127]) (.node (2793, [3, 7, 7, 19]) .nil .nil)
          (.node (2795, [5, 13, 43]) .nil .nil))
        (.node (2798, [2, 1399]) (.node (2797, [2797]) .nil .nil)
          (.node (2799, [3, 3, 311]) .nil .nil)))
      (.node (2804, [2, 2, 701])
        (.node (2802, [2, 3, 467]) (.node (2801, [2801]) .nil .nil)
          (.node (2803, [2803]) .nil .nil))
        (.node (2807, [7, 401]) (.node (2806, [2, 23, 61]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree72 : BinaryTree (ℕ × List ℕ) :=
  .node (2775, [3, 5, 5, 37]) routeSubtree70 routeSubtree71

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree73 : BinaryTree (ℕ × List ℕ) :=
  (.node (2826, [2, 3, 3, 157])
    (.node (2817, [3, 3, 313])
      (.node (2812, [2, 2, 19, 37])
        (.node (2810, [2, 5, 281]) (.node (2809, [53, 53]) .nil .nil)
          (.node (2811, [3, 937]) .nil .nil))
        (.node (2815, [5, 563]) (.node (2813, [29, 97]) .nil .nil)
          (.node (2816, [2, 2, 2, 2, 2, 2, 2, 2, 11]) .nil .nil)))
      (.node (2822, [2, 17, 83])
        (.node (2819, [2819]) (.node (2818, [2, 1409]) .nil .nil)
          (.node (2821, [7, 13, 31]) .nil .nil))
        (.node (2824, [2, 2, 2, 353]) (.node (2823, [3, 941]) .nil .nil)
          (.node (2825, [5, 5, 113]) .nil .nil))))
    (.node (2834, [2, 13, 109])
      (.node (2830, [2, 5, 283])
        (.node (2828, [2, 2, 7, 101]) (.node (2827, [11, 257]) .nil .nil)
          (.node (2829, [3, 23, 41]) .nil .nil))
        (.node (2832, [2, 2, 2, 2, 3, 59]) (.node (2831, [19, 149]) .nil .nil)
          (.node (2833, [2833]) .nil .nil)))
      (.node (2839, [17, 167])
        (.node (2836, [2, 2, 709]) (.node (2835, [3, 3, 3, 3, 5, 7]) .nil .nil)
          (.node (2837, [2837]) .nil .nil))
        (.node (2841, [3, 947]) (.node (2840, [2, 2, 2, 5, 71]) .nil .nil)
          (.node (2842, [2, 7, 7, 29]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree74 : BinaryTree (ℕ × List ℕ) :=
  (.node (2862, [2, 3, 3, 3, 53])
    (.node (2852, [2, 2, 23, 31])
      (.node (2847, [3, 13, 73])
        (.node (2845, [5, 569]) (.node (2844, [2, 2, 3, 3, 79]) .nil .nil)
          (.node (2846, [2, 1423]) .nil .nil))
        (.node (2849, [7, 11, 37]) (.node (2848, [2, 2, 2, 2, 2, 89]) .nil .nil)
          (.node (2851, [2851]) .nil .nil)))
      (.node (2857, [2857])
        (.node (2854, [2, 1427]) (.node (2853, [3, 3, 317]) .nil .nil)
          (.node (2855, [5, 571]) .nil .nil))
        (.node (2859, [3, 953]) (.node (2858, [2, 1429]) .nil .nil)
          (.node (2861, [2861]) .nil .nil))))
    (.node (2871, [3, 3, 11, 29])
      (.node (2866, [2, 1433])
        (.node (2864, [2, 2, 2, 2, 179]) (.node (2863, [7, 409]) .nil .nil)
          (.node (2865, [3, 5, 191]) .nil .nil))
        (.node (2868, [2, 2, 3, 239]) (.node (2867, [47, 61]) .nil .nil)
          (.node (2869, [19, 151]) .nil .nil)))
      (.node (2875, [5, 5, 5, 23])
        (.node (2873, [13, 13, 17]) (.node (2872, [2, 2, 2, 359]) .nil .nil)
          (.node (2874, [2, 3, 479]) .nil .nil))
        (.node (2877, [3, 7, 137]) (.node (2876, [2, 2, 719]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree75 : BinaryTree (ℕ × List ℕ) :=
  .node (2843, [2843]) routeSubtree73 routeSubtree74

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree76 : BinaryTree (ℕ × List ℕ) :=
  .node (2808, [2, 2, 2, 3, 3, 3, 13]) routeSubtree72 routeSubtree75

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree77 : BinaryTree (ℕ × List ℕ) :=
  .node (2741, [2741]) routeSubtree69 routeSubtree76

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree78 : BinaryTree (ℕ × List ℕ) :=
  (.node (2895, [3, 5, 193])
    (.node (2887, [2887])
      (.node (2882, [2, 11, 131])
        (.node (2880, [2, 2, 2, 2, 2, 2, 3, 3, 5]) (.node (2879, [2879]) .nil .nil)
          (.node (2881, [43, 67]) .nil .nil))
        (.node (2884, [2, 2, 7, 103]) (.node (2883, [3, 31, 31]) .nil .nil)
          (.node (2885, [5, 577]) .nil .nil)))
      (.node (2891, [7, 7, 59])
        (.node (2889, [3, 3, 3, 107]) (.node (2888, [2, 2, 2, 19, 19]) .nil .nil)
          (.node (2890, [2, 5, 17, 17]) .nil .nil))
        (.node (2893, [11, 263]) (.node (2892, [2, 2, 3, 241]) .nil .nil)
          (.node (2894, [2, 1447]) .nil .nil))))
    (.node (2904, [2, 2, 2, 3, 11, 11])
      (.node (2900, [2, 2, 5, 5, 29])
        (.node (2897, [2897]) (.node (2896, [2, 2, 2, 2, 181]) .nil .nil)
          (.node (2899, [13, 223]) .nil .nil))
        (.node (2902, [2, 1451]) (.node (2901, [3, 967]) .nil .nil)
          (.node (2903, [2903]) .nil .nil)))
      (.node (2908, [2, 2, 727])
        (.node (2906, [2, 1453]) (.node (2905, [5, 7, 83]) .nil .nil)
          (.node (2907, [3, 3, 17, 19]) .nil .nil))
        (.node (2911, [41, 71]) (.node (2909, [2909]) .nil .nil)
          (.node (2912, [2, 2, 2, 2, 2, 7, 13]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree79 : BinaryTree (ℕ × List ℕ) :=
  (.node (2930, [2, 5, 293])
    (.node (2921, [23, 127])
      (.node (2917, [2917])
        (.node (2915, [5, 11, 53]) (.node (2914, [2, 31, 47]) .nil .nil)
          (.node (2916, [2, 2, 3, 3, 3, 3, 3, 3]) .nil .nil))
        (.node (2919, [3, 7, 139]) (.node (2918, [2, 1459]) .nil .nil)
          (.node (2920, [2, 2, 2, 5, 73]) .nil .nil)))
      (.node (2925, [3, 3, 5, 5, 13])
        (.node (2923, [37, 79]) (.node (2922, [2, 3, 487]) .nil .nil)
          (.node (2924, [2, 2, 17, 43]) .nil .nil))
        (.node (2928, [2, 2, 2, 2, 3, 61]) (.node (2927, [2927]) .nil .nil)
          (.node (2929, [29, 101]) .nil .nil))))
    (.node (2938, [2, 13, 113])
      (.node (2934, [2, 3, 3, 163])
        (.node (2932, [2, 2, 733]) (.node (2931, [3, 977]) .nil .nil)
          (.node (2933, [7, 419]) .nil .nil))
        (.node (2936, [2, 2, 2, 367]) (.node (2935, [5, 587]) .nil .nil)
          (.node (2937, [3, 11, 89]) .nil .nil)))
      (.node (2943, [3, 3, 3, 109])
        (.node (2941, [17, 173]) (.node (2939, [2939]) .nil .nil)
          (.node (2942, [2, 1471]) .nil .nil))
        (.node (2945, [5, 19, 31]) (.node (2944, [2, 2, 2, 2, 2, 2, 2, 23]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree80 : BinaryTree (ℕ × List ℕ) :=
  .node (2913, [3, 971]) routeSubtree78 routeSubtree79

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree81 : BinaryTree (ℕ × List ℕ) :=
  (.node (2963, [2963])
    (.node (2954, [2, 7, 211])
      (.node (2950, [2, 5, 5, 59])
        (.node (2948, [2, 2, 11, 67]) (.node (2947, [7, 421]) .nil .nil)
          (.node (2949, [3, 983]) .nil .nil))
        (.node (2952, [2, 2, 2, 3, 3, 41]) (.node (2951, [13, 227]) .nil .nil)
          (.node (2953, [2953]) .nil .nil)))
      (.node (2959, [11, 269])
        (.node (2956, [2, 2, 739]) (.node (2955, [3, 5, 197]) .nil .nil)
          (.node (2957, [2957]) .nil .nil))
        (.node (2961, [3, 3, 7, 47]) (.node (2960, [2, 2, 2, 2, 5, 37]) .nil .nil)
          (.node (2962, [2, 1481]) .nil .nil))))
    (.node (2973, [3, 991])
      (.node (2968, [2, 2, 2, 7, 53])
        (.node (2966, [2, 1483]) (.node (2965, [5, 593]) .nil .nil)
          (.node (2967, [3, 23, 43]) .nil .nil))
        (.node (2971, [2971]) (.node (2969, [2969]) .nil .nil)
          (.node (2972, [2, 2, 743]) .nil .nil)))
      (.node (2977, [13, 229])
        (.node (2975, [5, 5, 7, 17]) (.node (2974, [2, 1487]) .nil .nil)
          (.node (2976, [2, 2, 2, 2, 2, 3, 31]) .nil .nil))
        (.node (2979, [3, 3, 331]) (.node (2978, [2, 1489]) .nil .nil)
          (.node (2980, [2, 2, 5, 149]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree82 : BinaryTree (ℕ × List ℕ) :=
  (.node (2999, [2999])
    (.node (2991, [3, 997])
      (.node (2986, [2, 1493])
        (.node (2984, [2, 2, 2, 373]) (.node (2983, [19, 157]) .nil .nil)
          (.node (2985, [3, 5, 199]) .nil .nil))
        (.node (2988, [2, 2, 3, 3, 83]) (.node (2987, [29, 103]) .nil .nil)
          (.node (2989, [7, 7, 61]) .nil .nil)))
      (.node (2995, [5, 599])
        (.node (2993, [41, 73]) (.node (2992, [2, 2, 2, 2, 11, 17]) .nil .nil)
          (.node (2994, [2, 3, 499]) .nil .nil))
        (.node (2997, [3, 3, 3, 3, 37]) (.node (2996, [2, 2, 7, 107]) .nil .nil)
          (.node (2998, [2, 1499]) .nil .nil))))
    (.node (3008, [2, 2, 2, 2, 2, 2, 47])
      (.node (3004, [2, 2, 751])
        (.node (3001, [3001]) (.node (3000, [2, 2, 2, 3, 5, 5, 5]) .nil .nil)
          (.node (3002, [2, 19, 79]) .nil .nil))
        (.node (3006, [2, 3, 3, 167]) (.node (3005, [5, 601]) .nil .nil)
          (.node (3007, [31, 97]) .nil .nil)))
      (.node (3013, [23, 131])
        (.node (3011, [3011]) (.node (3009, [3, 17, 59]) .nil .nil)
          (.node (3012, [2, 2, 3, 251]) .nil .nil))
        (.node (3015, [3, 3, 5, 67]) (.node (3014, [2, 11, 137]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree83 : BinaryTree (ℕ × List ℕ) :=
  .node (2981, [11, 271]) routeSubtree81 routeSubtree82

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree84 : BinaryTree (ℕ × List ℕ) :=
  .node (2946, [2, 3, 491]) routeSubtree80 routeSubtree83

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree85 : BinaryTree (ℕ × List ℕ) :=
  (.node (3033, [3, 3, 337])
    (.node (3024, [2, 2, 2, 2, 3, 3, 3, 7])
      (.node (3020, [2, 2, 5, 151])
        (.node (3018, [2, 3, 503]) (.node (3017, [7, 431]) .nil .nil)
          (.node (3019, [3019]) .nil .nil))
        (.node (3022, [2, 1511]) (.node (3021, [3, 19, 53]) .nil .nil)
          (.node (3023, [3023]) .nil .nil)))
      (.node (3028, [2, 2, 757])
        (.node (3026, [2, 17, 89]) (.node (3025, [5, 5, 11, 11]) .nil .nil)
          (.node (3027, [3, 1009]) .nil .nil))
        (.node (3031, [7, 433]) (.node (3029, [13, 233]) .nil .nil)
          (.node (3032, [2, 2, 2, 379]) .nil .nil))))
    (.node (3042, [2, 3, 3, 13, 13])
      (.node (3038, [2, 7, 7, 31])
        (.node (3035, [5, 607]) (.node (3034, [2, 37, 41]) .nil .nil)
          (.node (3037, [3037]) .nil .nil))
        (.node (3040, [2, 2, 2, 2, 2, 5, 19]) (.node (3039, [3, 1013]) .nil .nil)
          (.node (3041, [3041]) .nil .nil)))
      (.node (3047, [11, 277])
        (.node (3044, [2, 2, 761]) (.node (3043, [17, 179]) .nil .nil)
          (.node (3046, [2, 1523]) .nil .nil))
        (.node (3049, [3049]) (.node (3048, [2, 2, 2, 3, 127]) .nil .nil)
          (.node (3050, [2, 5, 5, 61]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree86 : BinaryTree (ℕ × List ℕ) :=
  (.node (3069, [3, 3, 11, 31])
    (.node (3059, [7, 19, 23])
      (.node (3055, [5, 13, 47])
        (.node (3053, [43, 71]) (.node (3052, [2, 2, 7, 109]) .nil .nil)
          (.node (3054, [2, 3, 509]) .nil .nil))
        (.node (3057, [3, 1019]) (.node (3056, [2, 2, 2, 2, 191]) .nil .nil)
          (.node (3058, [2, 11, 139]) .nil .nil)))
      (.node (3064, [2, 2, 2, 383])
        (.node (3062, [2, 1531]) (.node (3061, [3061]) .nil .nil)
          (.node (3063, [3, 1021]) .nil .nil))
        (.node (3067, [3067]) (.node (3065, [5, 613]) .nil .nil)
          (.node (3068, [2, 2, 13, 59]) .nil .nil))))
    (.node (3077, [17, 181])
      (.node (3073, [7, 439])
        (.node (3071, [37, 83]) (.node (3070, [2, 5, 307]) .nil .nil)
          (.node (3072, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3]) .nil .nil))
        (.node (3075, [3, 5, 5, 41]) (.node (3074, [2, 29, 53]) .nil .nil)
          (.node (3076, [2, 2, 769]) .nil .nil)))
      (.node (3082, [2, 23, 67])
        (.node (3079, [3079]) (.node (3078, [2, 3, 3, 3, 3, 19]) .nil .nil)
          (.node (3081, [3, 13, 79]) .nil .nil))
        (.node (3084, [2, 2, 3, 257]) (.node (3083, [3083]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree87 : BinaryTree (ℕ × List ℕ) :=
  .node (3051, [3, 3, 3, 113]) routeSubtree85 routeSubtree86

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree88 : BinaryTree (ℕ × List ℕ) :=
  (.node (3104, [2, 2, 2, 2, 2, 97])
    (.node (3095, [5, 619])
      (.node (3089, [3089])
        (.node (3087, [3, 3, 7, 7, 7]) (.node (3086, [2, 1543]) .nil .nil)
          (.node (3088, [2, 2, 2, 2, 193]) .nil .nil))
        (.node (3092, [2, 2, 773]) (.node (3091, [11, 281]) .nil .nil)
          (.node (3093, [3, 1031]) .nil .nil)))
      (.node (3099, [3, 1033])
        (.node (3097, [19, 163]) (.node (3096, [2, 2, 2, 3, 3, 43]) .nil .nil)
          (.node (3098, [2, 1549]) .nil .nil))
        (.node (3101, [7, 443]) (.node (3100, [2, 2, 5, 5, 31]) .nil .nil)
          (.node (3103, [29, 107]) .nil .nil))))
    (.node (3113, [11, 283])
      (.node (3109, [3109])
        (.node (3106, [2, 1553]) (.node (3105, [3, 3, 3, 5, 23]) .nil .nil)
          (.node (3107, [13, 239]) .nil .nil))
        (.node (3111, [3, 17, 61]) (.node (3110, [2, 5, 311]) .nil .nil)
          (.node (3112, [2, 2, 2, 389]) .nil .nil)))
      (.node (3117, [3, 1039])
        (.node (3115, [5, 7, 89]) (.node (3114, [2, 3, 3, 173]) .nil .nil)
          (.node (3116, [2, 2, 19, 41]) .nil .nil))
        (.node (3119, [3119]) (.node (3118, [2, 1559]) .nil .nil)
          (.node (3121, [3121]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree89 : BinaryTree (ℕ × List ℕ) :=
  (.node (3139, [43, 73])
    (.node (3130, [2, 5, 313])
      (.node (3126, [2, 3, 521])
        (.node (3124, [2, 2, 11, 71]) (.node (3123, [3, 3, 347]) .nil .nil)
          (.node (3125, [5, 5, 5, 5, 5]) .nil .nil))
        (.node (3128, [2, 2, 2, 17, 23]) (.node (3127, [53, 59]) .nil .nil)
          (.node (3129, [3, 7, 149]) .nil .nil)))
      (.node (3134, [2, 1567])
        (.node (3132, [2, 2, 3, 3, 3, 29]) (.node (3131, [31, 101]) .nil .nil)
          (.node (3133, [13, 241]) .nil .nil))
        (.node (3137, [3137]) (.node (3136, [2, 2, 2, 2, 2, 2, 7, 7]) .nil .nil)
          (.node (3138, [2, 3, 523]) .nil .nil))))
    (.node (3147, [3, 1049])
      (.node (3143, [7, 449])
        (.node (3141, [3, 3, 349]) (.node (3140, [2, 2, 5, 157]) .nil .nil)
          (.node (3142, [2, 1571]) .nil .nil))
        (.node (3145, [5, 17, 37]) (.node (3144, [2, 2, 2, 3, 131]) .nil .nil)
          (.node (3146, [2, 11, 11, 13]) .nil .nil)))
      (.node (3152, [2, 2, 2, 2, 197])
        (.node (3149, [47, 67]) (.node (3148, [2, 2, 787]) .nil .nil)
          (.node (3151, [23, 137]) .nil .nil))
        (.node (3154, [2, 19, 83]) (.node (3153, [3, 1051]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree90 : BinaryTree (ℕ × List ℕ) :=
  .node (3122, [2, 7, 223]) routeSubtree88 routeSubtree89

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree91 : BinaryTree (ℕ × List ℕ) :=
  .node (3085, [5, 617]) routeSubtree87 routeSubtree90

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree92 : BinaryTree (ℕ × List ℕ) :=
  .node (3016, [2, 2, 2, 13, 29]) routeSubtree84 routeSubtree91

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree93 : BinaryTree (ℕ × List ℕ) :=
  .node (2878, [2, 1439]) routeSubtree77 routeSubtree92

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree94 : BinaryTree (ℕ × List ℕ) :=
  (.node (3172, [2, 2, 13, 61])
    (.node (3164, [2, 2, 7, 113])
      (.node (3159, [3, 3, 3, 3, 3, 13])
        (.node (3157, [7, 11, 41]) (.node (3156, [2, 2, 3, 263]) .nil .nil)
          (.node (3158, [2, 1579]) .nil .nil))
        (.node (3161, [29, 109]) (.node (3160, [2, 2, 2, 5, 79]) .nil .nil)
          (.node (3163, [3163]) .nil .nil)))
      (.node (3168, [2, 2, 2, 2, 2, 3, 3, 11])
        (.node (3166, [2, 1583]) (.node (3165, [3, 5, 211]) .nil .nil)
          (.node (3167, [3167]) .nil .nil))
        (.node (3170, [2, 5, 317]) (.node (3169, [3169]) .nil .nil)
          (.node (3171, [3, 7, 151]) .nil .nil))))
    (.node (3181, [3181])
      (.node (3176, [2, 2, 2, 397])
        (.node (3174, [2, 3, 23, 23]) (.node (3173, [19, 167]) .nil .nil)
          (.node (3175, [5, 5, 127]) .nil .nil))
        (.node (3178, [2, 7, 227]) (.node (3177, [3, 3, 353]) .nil .nil)
          (.node (3179, [11, 17, 17]) .nil .nil)))
      (.node (3185, [5, 7, 7, 13])
        (.node (3183, [3, 1061]) (.node (3182, [2, 37, 43]) .nil .nil)
          (.node (3184, [2, 2, 2, 2, 199]) .nil .nil))
        (.node (3187, [3187]) (.node (3186, [2, 3, 3, 3, 59]) .nil .nil)
          (.node (3188, [2, 2, 797]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree95 : BinaryTree (ℕ × List ℕ) :=
  (.node (3208, [2, 2, 2, 401])
    (.node (3200, [2, 2, 2, 2, 2, 2, 2, 5, 5])
      (.node (3195, [3, 3, 5, 71])
        (.node (3193, [31, 103]) (.node (3191, [3191]) .nil .nil)
          (.node (3194, [2, 1597]) .nil .nil))
        (.node (3197, [23, 139]) (.node (3196, [2, 2, 17, 47]) .nil .nil)
          (.node (3199, [7, 457]) .nil .nil)))
      (.node (3204, [2, 2, 3, 3, 89])
        (.node (3202, [2, 1601]) (.node (3201, [3, 11, 97]) .nil .nil)
          (.node (3203, [3203]) .nil .nil))
        (.node (3206, [2, 7, 229]) (.node (3205, [5, 641]) .nil .nil)
          (.node (3207, [3, 1069]) .nil .nil))))
    (.node (3217, [3217])
      (.node (3213, [3, 3, 3, 7, 17])
        (.node (3211, [13, 13, 19]) (.node (3209, [3209]) .nil .nil)
          (.node (3212, [2, 2, 11, 73]) .nil .nil))
        (.node (3215, [5, 643]) (.node (3214, [2, 1607]) .nil .nil)
          (.node (3216, [2, 2, 2, 2, 3, 67]) .nil .nil)))
      (.node (3222, [2, 3, 3, 179])
        (.node (3219, [3, 29, 37]) (.node (3218, [2, 1609]) .nil .nil)
          (.node (3221, [3221]) .nil .nil))
        (.node (3224, [2, 2, 2, 13, 31]) (.node (3223, [11, 293]) .nil .nil)
          (.node (3225, [3, 5, 5, 43]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree96 : BinaryTree (ℕ × List ℕ) :=
  .node (3189, [3, 1063]) routeSubtree94 routeSubtree95

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree97 : BinaryTree (ℕ × List ℕ) :=
  (.node (3244, [2, 2, 811])
    (.node (3236, [2, 2, 809])
      (.node (3231, [3, 3, 359])
        (.node (3228, [2, 2, 3, 269]) (.node (3227, [7, 461]) .nil .nil)
          (.node (3229, [3229]) .nil .nil))
        (.node (3233, [53, 61]) (.node (3232, [2, 2, 2, 2, 2, 101]) .nil .nil)
          (.node (3235, [5, 647]) .nil .nil)))
      (.node (3240, [2, 2, 2, 3, 3, 3, 3, 5])
        (.node (3238, [2, 1619]) (.node (3237, [3, 13, 83]) .nil .nil)
          (.node (3239, [41, 79]) .nil .nil))
        (.node (3242, [2, 1621]) (.node (3241, [7, 463]) .nil .nil)
          (.node (3243, [3, 23, 47]) .nil .nil))))
    (.node (3252, [2, 2, 3, 271])
      (.node (3248, [2, 2, 2, 2, 7, 29])
        (.node (3246, [2, 3, 541]) (.node (3245, [5, 11, 59]) .nil .nil)
          (.node (3247, [17, 191]) .nil .nil))
        (.node (3250, [2, 5, 5, 5, 13]) (.node (3249, [3, 3, 19, 19]) .nil .nil)
          (.node (3251, [3251]) .nil .nil)))
      (.node (3257, [3257])
        (.node (3254, [2, 1627]) (.node (3253, [3253]) .nil .nil)
          (.node (3256, [2, 2, 2, 11, 37]) .nil .nil))
        (.node (3259, [3259]) (.node (3258, [2, 3, 3, 181]) .nil .nil)
          (.node (3260, [2, 2, 5, 163]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree98 : BinaryTree (ℕ × List ℕ) :=
  (.node (3279, [3, 1093])
    (.node (3269, [7, 467])
      (.node (3265, [5, 653])
        (.node (3263, [13, 251]) (.node (3262, [2, 7, 233]) .nil .nil)
          (.node (3264, [2, 2, 2, 2, 2, 2, 3, 17]) .nil .nil))
        (.node (3267, [3, 3, 3, 11, 11]) (.node (3266, [2, 23, 71]) .nil .nil)
          (.node (3268, [2, 2, 19, 43]) .nil .nil)))
      (.node (3274, [2, 1637])
        (.node (3272, [2, 2, 2, 409]) (.node (3271, [3271]) .nil .nil)
          (.node (3273, [3, 1091]) .nil .nil))
        (.node (3277, [29, 113]) (.node (3275, [5, 5, 131]) .nil .nil)
          (.node (3278, [2, 11, 149]) .nil .nil))))
    (.node (3287, [19, 173])
      (.node (3283, [7, 7, 67])
        (.node (3281, [17, 193]) (.node (3280, [2, 2, 2, 2, 5, 41]) .nil .nil)
          (.node (3282, [2, 3, 547]) .nil .nil))
        (.node (3285, [3, 3, 5, 73]) (.node (3284, [2, 2, 821]) .nil .nil)
          (.node (3286, [2, 31, 53]) .nil .nil)))
      (.node (3292, [2, 2, 823])
        (.node (3289, [11, 13, 23]) (.node (3288, [2, 2, 2, 3, 137]) .nil .nil)
          (.node (3291, [3, 1097]) .nil .nil))
        (.node (3294, [2, 3, 3, 3, 61]) (.node (3293, [37, 89]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree99 : BinaryTree (ℕ × List ℕ) :=
  .node (3261, [3, 1087]) routeSubtree97 routeSubtree98

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree100 : BinaryTree (ℕ × List ℕ) :=
  .node (3226, [2, 1613]) routeSubtree96 routeSubtree99

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree101 : BinaryTree (ℕ × List ℕ) :=
  (.node (3311, [7, 11, 43])
    (.node (3303, [3, 3, 367])
      (.node (3299, [3299])
        (.node (3297, [3, 7, 157]) (.node (3296, [2, 2, 2, 2, 2, 103]) .nil .nil)
          (.node (3298, [2, 17, 97]) .nil .nil))
        (.node (3301, [3301]) (.node (3300, [2, 2, 3, 5, 5, 11]) .nil .nil)
          (.node (3302, [2, 13, 127]) .nil .nil)))
      (.node (3307, [3307])
        (.node (3305, [5, 661]) (.node (3304, [2, 2, 2, 7, 59]) .nil .nil)
          (.node (3306, [2, 3, 19, 29]) .nil .nil))
        (.node (3309, [3, 1103]) (.node (3308, [2, 2, 827]) .nil .nil)
          (.node (3310, [2, 5, 331]) .nil .nil))))
    (.node (3319, [3319])
      (.node (3315, [3, 5, 13, 17])
        (.node (3313, [3313]) (.node (3312, [2, 2, 2, 2, 3, 3, 23]) .nil .nil)
          (.node (3314, [2, 1657]) .nil .nil))
        (.node (3317, [31, 107]) (.node (3316, [2, 2, 829]) .nil .nil)
          (.node (3318, [2, 3, 7, 79]) .nil .nil)))
      (.node (3323, [3323])
        (.node (3321, [3, 3, 3, 3, 41]) (.node (3320, [2, 2, 2, 5, 83]) .nil .nil)
          (.node (3322, [2, 11, 151]) .nil .nil))
        (.node (3325, [5, 5, 7, 19]) (.node (3324, [2, 2, 3, 277]) .nil .nil)
          (.node (3326, [2, 1663]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree102 : BinaryTree (ℕ × List ℕ) :=
  (.node (3343, [3343])
    (.node (3335, [5, 23, 29])
      (.node (3331, [3331])
        (.node (3329, [3329]) (.node (3328, [2, 2, 2, 2, 2, 2, 2, 2, 13]) .nil .nil)
          (.node (3330, [2, 3, 3, 5, 37]) .nil .nil))
        (.node (3333, [3, 11, 101]) (.node (3332, [2, 2, 7, 7, 17]) .nil .nil)
          (.node (3334, [2, 1667]) .nil .nil)))
      (.node (3339, [3, 3, 7, 53])
        (.node (3337, [47, 71]) (.node (3336, [2, 2, 2, 3, 139]) .nil .nil)
          (.node (3338, [2, 1669]) .nil .nil))
        (.node (3341, [13, 257]) (.node (3340, [2, 2, 5, 167]) .nil .nil)
          (.node (3342, [2, 3, 557]) .nil .nil))))
    (.node (3351, [3, 1117])
      (.node (3347, [3347])
        (.node (3345, [3, 5, 223]) (.node (3344, [2, 2, 2, 2, 11, 19]) .nil .nil)
          (.node (3346, [2, 7, 239]) .nil .nil))
        (.node (3349, [17, 197]) (.node (3348, [2, 2, 3, 3, 3, 31]) .nil .nil)
          (.node (3350, [2, 5, 5, 67]) .nil .nil)))
      (.node (3355, [5, 11, 61])
        (.node (3353, [7, 479]) (.node (3352, [2, 2, 2, 419]) .nil .nil)
          (.node (3354, [2, 3, 13, 43]) .nil .nil))
        (.node (3357, [3, 3, 373]) (.node (3356, [2, 2, 839]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree103 : BinaryTree (ℕ × List ℕ) :=
  .node (3327, [3, 1109]) routeSubtree101 routeSubtree102

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree104 : BinaryTree (ℕ × List ℕ) :=
  (.node (3374, [2, 7, 241])
    (.node (3366, [2, 3, 3, 11, 17])
      (.node (3362, [2, 41, 41])
        (.node (3360, [2, 2, 2, 2, 2, 3, 5, 7]) (.node (3359, [3359]) .nil .nil)
          (.node (3361, [3361]) .nil .nil))
        (.node (3364, [2, 2, 29, 29]) (.node (3363, [3, 19, 59]) .nil .nil)
          (.node (3365, [5, 673]) .nil .nil)))
      (.node (3370, [2, 5, 337])
        (.node (3368, [2, 2, 2, 421]) (.node (3367, [7, 13, 37]) .nil .nil)
          (.node (3369, [3, 1123]) .nil .nil))
        (.node (3372, [2, 2, 3, 281]) (.node (3371, [3371]) .nil .nil)
          (.node (3373, [3373]) .nil .nil))))
    (.node (3382, [2, 19, 89])
      (.node (3378, [2, 3, 563])
        (.node (3376, [2, 2, 2, 2, 211]) (.node (3375, [3, 3, 3, 5, 5, 5]) .nil .nil)
          (.node (3377, [11, 307]) .nil .nil))
        (.node (3380, [2, 2, 5, 13, 13]) (.node (3379, [31, 109]) .nil .nil)
          (.node (3381, [3, 7, 7, 23]) .nil .nil)))
      (.node (3386, [2, 1693])
        (.node (3384, [2, 2, 2, 3, 3, 47]) (.node (3383, [17, 199]) .nil .nil)
          (.node (3385, [5, 677]) .nil .nil))
        (.node (3388, [2, 2, 7, 11, 11]) (.node (3387, [3, 1129]) .nil .nil)
          (.node (3389, [3389]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree105 : BinaryTree (ℕ × List ℕ) :=
  (.node (3406, [2, 13, 131])
    (.node (3398, [2, 1699])
      (.node (3394, [2, 1697])
        (.node (3392, [2, 2, 2, 2, 2, 2, 53]) (.node (3391, [3391]) .nil .nil)
          (.node (3393, [3, 3, 13, 29]) .nil .nil))
        (.node (3396, [2, 2, 3, 283]) (.node (3395, [5, 7, 97]) .nil .nil)
          (.node (3397, [43, 79]) .nil .nil)))
      (.node (3402, [2, 3, 3, 3, 3, 3, 7])
        (.node (3400, [2, 2, 2, 5, 5, 17]) (.node (3399, [3, 11, 103]) .nil .nil)
          (.node (3401, [19, 179]) .nil .nil))
        (.node (3404, [2, 2, 23, 37]) (.node (3403, [41, 83]) .nil .nil)
          (.node (3405, [3, 5, 227]) .nil .nil))))
    (.node (3414, [2, 3, 569])
      (.node (3410, [2, 5, 11, 31])
        (.node (3408, [2, 2, 2, 2, 3, 71]) (.node (3407, [3407]) .nil .nil)
          (.node (3409, [7, 487]) .nil .nil))
        (.node (3412, [2, 2, 853]) (.node (3411, [3, 3, 379]) .nil .nil)
          (.node (3413, [3413]) .nil .nil)))
      (.node (3418, [2, 1709])
        (.node (3416, [2, 2, 2, 7, 61]) (.node (3415, [5, 683]) .nil .nil)
          (.node (3417, [3, 17, 67]) .nil .nil))
        (.node (3420, [2, 2, 3, 3, 5, 19]) (.node (3419, [13, 263]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree106 : BinaryTree (ℕ × List ℕ) :=
  .node (3390, [2, 3, 5, 113]) routeSubtree104 routeSubtree105

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree107 : BinaryTree (ℕ × List ℕ) :=
  .node (3358, [2, 23, 73]) routeSubtree103 routeSubtree106

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree108 : BinaryTree (ℕ × List ℕ) :=
  .node (3295, [5, 659]) routeSubtree100 routeSubtree107

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree109 : BinaryTree (ℕ × List ℕ) :=
  (.node (3437, [7, 491])
    (.node (3429, [3, 3, 3, 127])
      (.node (3425, [5, 5, 137])
        (.node (3423, [3, 7, 163]) (.node (3422, [2, 29, 59]) .nil .nil)
          (.node (3424, [2, 2, 2, 2, 2, 107]) .nil .nil))
        (.node (3427, [23, 149]) (.node (3426, [2, 3, 571]) .nil .nil)
          (.node (3428, [2, 2, 857]) .nil .nil)))
      (.node (3433, [3433])
        (.node (3431, [47, 73]) (.node (3430, [2, 5, 7, 7, 7]) .nil .nil)
          (.node (3432, [2, 2, 2, 3, 11, 13]) .nil .nil))
        (.node (3435, [3, 5, 229]) (.node (3434, [2, 17, 101]) .nil .nil)
          (.node (3436, [2, 2, 859]) .nil .nil))))
    (.node (3445, [5, 13, 53])
      (.node (3441, [3, 31, 37])
        (.node (3439, [19, 181]) (.node (3438, [2, 3, 3, 191]) .nil .nil)
          (.node (3440, [2, 2, 2, 2, 5, 43]) .nil .nil))
        (.node (3443, [11, 313]) (.node (3442, [2, 1721]) .nil .nil)
          (.node (3444, [2, 2, 3, 7, 41]) .nil .nil)))
      (.node (3449, [3449])
        (.node (3447, [3, 3, 383]) (.node (3446, [2, 1723]) .nil .nil)
          (.node (3448, [2, 2, 2, 431]) .nil .nil))
        (.node (3451, [7, 17, 29]) (.node (3450, [2, 3, 5, 5, 23]) .nil .nil)
          (.node (3452, [2, 2, 863]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree110 : BinaryTree (ℕ × List ℕ) :=
  (.node (3469, [3469])
    (.node (3461, [3461])
      (.node (3457, [3457])
        (.node (3455, [5, 691]) (.node (3454, [2, 11, 157]) .nil .nil)
          (.node (3456, [2, 2, 2, 2, 2, 2, 2, 3, 3, 3]) .nil .nil))
        (.node (3459, [3, 1153]) (.node (3458, [2, 7, 13, 19]) .nil .nil)
          (.node (3460, [2, 2, 5, 173]) .nil .nil)))
      (.node (3465, [3, 3, 5, 7, 11])
        (.node (3463, [3463]) (.node (3462, [2, 3, 577]) .nil .nil)
          (.node (3464, [2, 2, 2, 433]) .nil .nil))
        (.node (3467, [3467]) (.node (3466, [2, 1733]) .nil .nil)
          (.node (3468, [2, 2, 3, 17, 17]) .nil .nil))))
    (.node (3477, [3, 19, 61])
      (.node (3473, [23, 151])
        (.node (3471, [3, 13, 89]) (.node (3470, [2, 5, 347]) .nil .nil)
          (.node (3472, [2, 2, 2, 2, 7, 31]) .nil .nil))
        (.node (3475, [5, 5, 139]) (.node (3474, [2, 3, 3, 193]) .nil .nil)
          (.node (3476, [2, 2, 11, 79]) .nil .nil)))
      (.node (3481, [59, 59])
        (.node (3479, [7, 7, 71]) (.node (3478, [2, 37, 47]) .nil .nil)
          (.node (3480, [2, 2, 2, 3, 5, 29]) .nil .nil))
        (.node (3483, [3, 3, 3, 3, 43]) (.node (3482, [2, 1741]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree111 : BinaryTree (ℕ × List ℕ) :=
  .node (3453, [3, 1151]) routeSubtree109 routeSubtree110

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree112 : BinaryTree (ℕ × List ℕ) :=
  (.node (3500, [2, 2, 5, 5, 5, 7])
    (.node (3492, [2, 2, 3, 3, 97])
      (.node (3488, [2, 2, 2, 2, 2, 109])
        (.node (3486, [2, 3, 7, 83]) (.node (3485, [5, 17, 41]) .nil .nil)
          (.node (3487, [11, 317]) .nil .nil))
        (.node (3490, [2, 5, 349]) (.node (3489, [3, 1163]) .nil .nil)
          (.node (3491, [3491]) .nil .nil)))
      (.node (3496, [2, 2, 2, 19, 23])
        (.node (3494, [2, 1747]) (.node (3493, [7, 499]) .nil .nil)
          (.node (3495, [3, 5, 233]) .nil .nil))
        (.node (3498, [2, 3, 11, 53]) (.node (3497, [13, 269]) .nil .nil)
          (.node (3499, [3499]) .nil .nil))))
    (.node (3508, [2, 2, 877])
      (.node (3504, [2, 2, 2, 2, 3, 73])
        (.node (3502, [2, 17, 103]) (.node (3501, [3, 3, 389]) .nil .nil)
          (.node (3503, [31, 113]) .nil .nil))
        (.node (3506, [2, 1753]) (.node (3505, [5, 701]) .nil .nil)
          (.node (3507, [3, 7, 167]) .nil .nil)))
      (.node (3512, [2, 2, 2, 439])
        (.node (3510, [2, 3, 3, 3, 5, 13]) (.node (3509, [11, 11, 29]) .nil .nil)
          (.node (3511, [3511]) .nil .nil))
        (.node (3514, [2, 7, 251]) (.node (3513, [3, 1171]) .nil .nil)
          (.node (3515, [5, 19, 37]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree113 : BinaryTree (ℕ × List ℕ) :=
  (.node (3532, [2, 2, 883])
    (.node (3524, [2, 2, 881])
      (.node (3520, [2, 2, 2, 2, 2, 2, 5, 11])
        (.node (3518, [2, 1759]) (.node (3517, [3517]) .nil .nil)
          (.node (3519, [3, 3, 17, 23]) .nil .nil))
        (.node (3522, [2, 3, 587]) (.node (3521, [7, 503]) .nil .nil)
          (.node (3523, [13, 271]) .nil .nil)))
      (.node (3528, [2, 2, 2, 3, 3, 7, 7])
        (.node (3526, [2, 41, 43]) (.node (3525, [3, 5, 5, 47]) .nil .nil)
          (.node (3527, [3527]) .nil .nil))
        (.node (3530, [2, 5, 353]) (.node (3529, [3529]) .nil .nil)
          (.node (3531, [3, 11, 107]) .nil .nil))))
    (.node (3540, [2, 2, 3, 5, 59])
      (.node (3536, [2, 2, 2, 2, 13, 17])
        (.node (3534, [2, 3, 19, 31]) (.node (3533, [3533]) .nil .nil)
          (.node (3535, [5, 7, 101]) .nil .nil))
        (.node (3538, [2, 29, 61]) (.node (3537, [3, 3, 3, 131]) .nil .nil)
          (.node (3539, [3539]) .nil .nil)))
      (.node (3544, [2, 2, 2, 443])
        (.node (3542, [2, 7, 11, 23]) (.node (3541, [3541]) .nil .nil)
          (.node (3543, [3, 1181]) .nil .nil))
        (.node (3546, [2, 3, 3, 197]) (.node (3545, [5, 709]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree114 : BinaryTree (ℕ × List ℕ) :=
  .node (3516, [2, 2, 3, 293]) routeSubtree112 routeSubtree113

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree115 : BinaryTree (ℕ × List ℕ) :=
  .node (3484, [2, 2, 13, 67]) routeSubtree111 routeSubtree114

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree116 : BinaryTree (ℕ × List ℕ) :=
  (.node (3563, [7, 509])
    (.node (3555, [3, 3, 5, 79])
      (.node (3551, [53, 67])
        (.node (3549, [3, 7, 13, 13]) (.node (3548, [2, 2, 887]) .nil .nil)
          (.node (3550, [2, 5, 5, 71]) .nil .nil))
        (.node (3553, [11, 17, 19]) (.node (3552, [2, 2, 2, 2, 2, 3, 37]) .nil .nil)
          (.node (3554, [2, 1777]) .nil .nil)))
      (.node (3559, [3559])
        (.node (3557, [3557]) (.node (3556, [2, 2, 7, 127]) .nil .nil)
          (.node (3558, [2, 3, 593]) .nil .nil))
        (.node (3561, [3, 1187]) (.node (3560, [2, 2, 2, 5, 89]) .nil .nil)
          (.node (3562, [2, 13, 137]) .nil .nil))))
    (.node (3572, [2, 2, 19, 47])
      (.node (3567, [3, 29, 41])
        (.node (3565, [5, 23, 31]) (.node (3564, [2, 2, 3, 3, 3, 3, 11]) .nil .nil)
          (.node (3566, [2, 1783]) .nil .nil))
        (.node (3569, [43, 83]) (.node (3568, [2, 2, 2, 2, 223]) .nil .nil)
          (.node (3571, [3571]) .nil .nil)))
      (.node (3576, [2, 2, 2, 3, 149])
        (.node (3574, [2, 1787]) (.node (3573, [3, 3, 397]) .nil .nil)
          (.node (3575, [5, 5, 11, 13]) .nil .nil))
        (.node (3578, [2, 1789]) (.node (3577, [7, 7, 73]) .nil .nil)
          (.node (3579, [3, 1193]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree117 : BinaryTree (ℕ × List ℕ) :=
  (.node (3596, [2, 2, 29, 31])
    (.node (3588, [2, 2, 3, 13, 23])
      (.node (3584, [2, 2, 2, 2, 2, 2, 2, 2, 2, 7])
        (.node (3582, [2, 3, 3, 199]) (.node (3581, [3581]) .nil .nil)
          (.node (3583, [3583]) .nil .nil))
        (.node (3586, [2, 11, 163]) (.node (3585, [3, 5, 239]) .nil .nil)
          (.node (3587, [17, 211]) .nil .nil)))
      (.node (3592, [2, 2, 2, 449])
        (.node (3590, [2, 5, 359]) (.node (3589, [37, 97]) .nil .nil)
          (.node (3591, [3, 3, 3, 7, 19]) .nil .nil))
        (.node (3594, [2, 3, 599]) (.node (3593, [3593]) .nil .nil)
          (.node (3595, [5, 719]) .nil .nil))))
    (.node (3604, [2, 2, 17, 53])
      (.node (3600, [2, 2, 2, 2, 3, 3, 5, 5])
        (.node (3598, [2, 7, 257]) (.node (3597, [3, 11, 109]) .nil .nil)
          (.node (3599, [59, 61]) .nil .nil))
        (.node (3602, [2, 1801]) (.node (3601, [13, 277]) .nil .nil)
          (.node (3603, [3, 1201]) .nil .nil)))
      (.node (3608, [2, 2, 2, 11, 41])
        (.node (3606, [2, 3, 601]) (.node (3605, [5, 7, 103]) .nil .nil)
          (.node (3607, [3607]) .nil .nil))
        (.node (3610, [2, 5, 19, 19]) (.node (3609, [3, 3, 401]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree118 : BinaryTree (ℕ × List ℕ) :=
  .node (3580, [2, 2, 5, 179]) routeSubtree116 routeSubtree117

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree119 : BinaryTree (ℕ × List ℕ) :=
  (.node (3627, [3, 3, 13, 31])
    (.node (3619, [7, 11, 47])
      (.node (3615, [3, 5, 241])
        (.node (3613, [3613]) (.node (3612, [2, 2, 3, 7, 43]) .nil .nil)
          (.node (3614, [2, 13, 139]) .nil .nil))
        (.node (3617, [3617]) (.node (3616, [2, 2, 2, 2, 2, 113]) .nil .nil)
          (.node (3618, [2, 3, 3, 3, 67]) .nil .nil)))
      (.node (3623, [3623])
        (.node (3621, [3, 17, 71]) (.node (3620, [2, 2, 5, 181]) .nil .nil)
          (.node (3622, [2, 1811]) .nil .nil))
        (.node (3625, [5, 5, 5, 29]) (.node (3624, [2, 2, 2, 3, 151]) .nil .nil)
          (.node (3626, [2, 7, 7, 37]) .nil .nil))))
    (.node (3635, [5, 727])
      (.node (3631, [3631])
        (.node (3629, [19, 191]) (.node (3628, [2, 2, 907]) .nil .nil)
          (.node (3630, [2, 3, 5, 11, 11]) .nil .nil))
        (.node (3633, [3, 7, 173]) (.node (3632, [2, 2, 2, 2, 227]) .nil .nil)
          (.node (3634, [2, 23, 79]) .nil .nil)))
      (.node (3639, [3, 1213])
        (.node (3637, [3637]) (.node (3636, [2, 2, 3, 3, 101]) .nil .nil)
          (.node (3638, [2, 17, 107]) .nil .nil))
        (.node (3641, [11, 331]) (.node (3640, [2, 2, 2, 5, 7, 13]) .nil .nil)
          (.node (3642, [2, 3, 607]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree120 : BinaryTree (ℕ × List ℕ) :=
  (.node (3659, [3659])
    (.node (3651, [3, 1217])
      (.node (3647, [7, 521])
        (.node (3645, [3, 3, 3, 3, 3, 3, 5]) (.node (3644, [2, 2, 911]) .nil .nil)
          (.node (3646, [2, 1823]) .nil .nil))
        (.node (3649, [41, 89]) (.node (3648, [2, 2, 2, 2, 2, 2, 3, 19]) .nil .nil)
          (.node (3650, [2, 5, 5, 73]) .nil .nil)))
      (.node (3655, [5, 17, 43])
        (.node (3653, [13, 281]) (.node (3652, [2, 2, 11, 83]) .nil .nil)
          (.node (3654, [2, 3, 3, 7, 29]) .nil .nil))
        (.node (3657, [3, 23, 53]) (.node (3656, [2, 2, 2, 457]) .nil .nil)
          (.node (3658, [2, 31, 59]) .nil .nil))))
    (.node (3667, [19, 193])
      (.node (3663, [3, 3, 11, 37])
        (.node (3661, [7, 523]) (.node (3660, [2, 2, 3, 5, 61]) .nil .nil)
          (.node (3662, [2, 1831]) .nil .nil))
        (.node (3665, [5, 733]) (.node (3664, [2, 2, 2, 2, 229]) .nil .nil)
          (.node (3666, [2, 3, 13, 47]) .nil .nil)))
      (.node (3671, [3671])
        (.node (3669, [3, 1223]) (.node (3668, [2, 2, 7, 131]) .nil .nil)
          (.node (3670, [2, 5, 367]) .nil .nil))
        (.node (3673, [3673]) (.node (3672, [2, 2, 2, 3, 3, 3, 17]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree121 : BinaryTree (ℕ × List ℕ) :=
  .node (3643, [3643]) routeSubtree119 routeSubtree120

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree122 : BinaryTree (ℕ × List ℕ) :=
  .node (3611, [23, 157]) routeSubtree118 routeSubtree121

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree123 : BinaryTree (ℕ × List ℕ) :=
  .node (3547, [3547]) routeSubtree115 routeSubtree122

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree124 : BinaryTree (ℕ × List ℕ) :=
  .node (3421, [11, 311]) routeSubtree108 routeSubtree123

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree125 : BinaryTree (ℕ × List ℕ) :=
  .node (3155, [5, 631]) routeSubtree93 routeSubtree124

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree126 : BinaryTree (ℕ × List ℕ) :=
  .node (2605, [5, 521]) routeSubtree62 routeSubtree125

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree127 : BinaryTree (ℕ × List ℕ) :=
  (.node (3690, [2, 3, 3, 5, 41])
    (.node (3682, [2, 7, 263])
      (.node (3678, [2, 3, 613])
        (.node (3676, [2, 2, 919]) (.node (3675, [3, 5, 5, 7, 7]) .nil .nil)
          (.node (3677, [3677]) .nil .nil))
        (.node (3680, [2, 2, 2, 2, 2, 5, 23]) (.node (3679, [13, 283]) .nil .nil)
          (.node (3681, [3, 3, 409]) .nil .nil)))
      (.node (3686, [2, 19, 97])
        (.node (3684, [2, 2, 3, 307]) (.node (3683, [29, 127]) .nil .nil)
          (.node (3685, [5, 11, 67]) .nil .nil))
        (.node (3688, [2, 2, 2, 461]) (.node (3687, [3, 1229]) .nil .nil)
          (.node (3689, [7, 17, 31]) .nil .nil))))
    (.node (3698, [2, 43, 43])
      (.node (3694, [2, 1847])
        (.node (3692, [2, 2, 13, 71]) (.node (3691, [3691]) .nil .nil)
          (.node (3693, [3, 1231]) .nil .nil))
        (.node (3696, [2, 2, 2, 2, 3, 7, 11]) (.node (3695, [5, 739]) .nil .nil)
          (.node (3697, [3697]) .nil .nil)))
      (.node (3702, [2, 3, 617])
        (.node (3700, [2, 2, 5, 5, 37]) (.node (3699, [3, 3, 3, 137]) .nil .nil)
          (.node (3701, [3701]) .nil .nil))
        (.node (3704, [2, 2, 2, 463]) (.node (3703, [7, 23, 23]) .nil .nil)
          (.node (3705, [3, 5, 13, 19]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree128 : BinaryTree (ℕ × List ℕ) :=
  (.node (3722, [2, 1861])
    (.node (3714, [2, 3, 619])
      (.node (3710, [2, 5, 7, 53])
        (.node (3708, [2, 2, 3, 3, 103]) (.node (3707, [11, 337]) .nil .nil)
          (.node (3709, [3709]) .nil .nil))
        (.node (3712, [2, 2, 2, 2, 2, 2, 2, 29]) (.node (3711, [3, 1237]) .nil .nil)
          (.node (3713, [47, 79]) .nil .nil)))
      (.node (3718, [2, 11, 13, 13])
        (.node (3716, [2, 2, 929]) (.node (3715, [5, 743]) .nil .nil)
          (.node (3717, [3, 3, 7, 59]) .nil .nil))
        (.node (3720, [2, 2, 2, 3, 5, 31]) (.node (3719, [3719]) .nil .nil)
          (.node (3721, [61, 61]) .nil .nil))))
    (.node (3730, [2, 5, 373])
      (.node (3726, [2, 3, 3, 3, 3, 23])
        (.node (3724, [2, 2, 7, 7, 19]) (.node (3723, [3, 17, 73]) .nil .nil)
          (.node (3725, [5, 5, 149]) .nil .nil))
        (.node (3728, [2, 2, 2, 2, 233]) (.node (3727, [3727]) .nil .nil)
          (.node (3729, [3, 11, 113]) .nil .nil)))
      (.node (3734, [2, 1867])
        (.node (3732, [2, 2, 3, 311]) (.node (3731, [7, 13, 41]) .nil .nil)
          (.node (3733, [3733]) .nil .nil))
        (.node (3736, [2, 2, 2, 467]) (.node (3735, [3, 3, 5, 83]) .nil .nil)
          (.node (3737, [37, 101]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree129 : BinaryTree (ℕ × List ℕ) :=
  .node (3706, [2, 17, 109]) routeSubtree127 routeSubtree128

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree130 : BinaryTree (ℕ × List ℕ) :=
  (.node (3754, [2, 1877])
    (.node (3746, [2, 1873])
      (.node (3742, [2, 1871])
        (.node (3740, [2, 2, 5, 11, 17]) (.node (3739, [3739]) .nil .nil)
          (.node (3741, [3, 29, 43]) .nil .nil))
        (.node (3744, [2, 2, 2, 2, 2, 3, 3, 13]) (.node (3743, [19, 197]) .nil .nil)
          (.node (3745, [5, 7, 107]) .nil .nil)))
      (.node (3750, [2, 3, 5, 5, 5, 5])
        (.node (3748, [2, 2, 937]) (.node (3747, [3, 1249]) .nil .nil)
          (.node (3749, [23, 163]) .nil .nil))
        (.node (3752, [2, 2, 2, 7, 67]) (.node (3751, [11, 11, 31]) .nil .nil)
          (.node (3753, [3, 3, 3, 139]) .nil .nil))))
    (.node (3762, [2, 3, 3, 11, 19])
      (.node (3758, [2, 1879])
        (.node (3756, [2, 2, 3, 313]) (.node (3755, [5, 751]) .nil .nil)
          (.node (3757, [13, 17, 17]) .nil .nil))
        (.node (3760, [2, 2, 2, 2, 5, 47]) (.node (3759, [3, 7, 179]) .nil .nil)
          (.node (3761, [3761]) .nil .nil)))
      (.node (3766, [2, 7, 269])
        (.node (3764, [2, 2, 941]) (.node (3763, [53, 71]) .nil .nil)
          (.node (3765, [3, 5, 251]) .nil .nil))
        (.node (3768, [2, 2, 2, 3, 157]) (.node (3767, [3767]) .nil .nil)
          (.node (3769, [3769]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree131 : BinaryTree (ℕ × List ℕ) :=
  (.node (3786, [2, 3, 631])
    (.node (3778, [2, 1889])
      (.node (3774, [2, 3, 17, 37])
        (.node (3772, [2, 2, 23, 41]) (.node (3771, [3, 3, 419]) .nil .nil)
          (.node (3773, [7, 7, 7, 11]) .nil .nil))
        (.node (3776, [2, 2, 2, 2, 2, 2, 59]) (.node (3775, [5, 5, 151]) .nil .nil)
          (.node (3777, [3, 1259]) .nil .nil)))
      (.node (3782, [2, 31, 61])
        (.node (3780, [2, 2, 3, 3, 3, 5, 7]) (.node (3779, [3779]) .nil .nil)
          (.node (3781, [19, 199]) .nil .nil))
        (.node (3784, [2, 2, 2, 11, 43]) (.node (3783, [3, 13, 97]) .nil .nil)
          (.node (3785, [5, 757]) .nil .nil))))
    (.node (3794, [2, 7, 271])
      (.node (3790, [2, 5, 379])
        (.node (3788, [2, 2, 947]) (.node (3787, [7, 541]) .nil .nil)
          (.node (3789, [3, 3, 421]) .nil .nil))
        (.node (3792, [2, 2, 2, 2, 3, 79]) (.node (3791, [17, 223]) .nil .nil)
          (.node (3793, [3793]) .nil .nil)))
      (.node (3798, [2, 3, 3, 211])
        (.node (3796, [2, 2, 13, 73]) (.node (3795, [3, 5, 11, 23]) .nil .nil)
          (.node (3797, [3797]) .nil .nil))
        (.node (3800, [2, 2, 2, 5, 5, 19]) (.node (3799, [29, 131]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree132 : BinaryTree (ℕ × List ℕ) :=
  .node (3770, [2, 5, 13, 29]) routeSubtree130 routeSubtree131

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree133 : BinaryTree (ℕ × List ℕ) :=
  .node (3738, [2, 3, 7, 89]) routeSubtree129 routeSubtree132

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree134 : BinaryTree (ℕ × List ℕ) :=
  (.node (3817, [11, 347])
    (.node (3809, [13, 293])
      (.node (3805, [5, 761])
        (.node (3803, [3803]) (.node (3802, [2, 1901]) .nil .nil)
          (.node (3804, [2, 2, 3, 317]) .nil .nil))
        (.node (3807, [3, 3, 3, 3, 47]) (.node (3806, [2, 11, 173]) .nil .nil)
          (.node (3808, [2, 2, 2, 2, 2, 7, 17]) .nil .nil)))
      (.node (3813, [3, 31, 41])
        (.node (3811, [37, 103]) (.node (3810, [2, 3, 5, 127]) .nil .nil)
          (.node (3812, [2, 2, 953]) .nil .nil))
        (.node (3815, [5, 7, 109]) (.node (3814, [2, 1907]) .nil .nil)
          (.node (3816, [2, 2, 2, 3, 3, 53]) .nil .nil))))
    (.node (3825, [3, 3, 5, 5, 17])
      (.node (3821, [3821])
        (.node (3819, [3, 19, 67]) (.node (3818, [2, 23, 83]) .nil .nil)
          (.node (3820, [2, 2, 5, 191]) .nil .nil))
        (.node (3823, [3823]) (.node (3822, [2, 3, 7, 7, 13]) .nil .nil)
          (.node (3824, [2, 2, 2, 2, 239]) .nil .nil)))
      (.node (3829, [7, 547])
        (.node (3827, [43, 89]) (.node (3826, [2, 1913]) .nil .nil)
          (.node (3828, [2, 2, 3, 11, 29]) .nil .nil))
        (.node (3831, [3, 1277]) (.node (3830, [2, 5, 383]) .nil .nil)
          (.node (3832, [2, 2, 2, 479]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree135 : BinaryTree (ℕ × List ℕ) :=
  (.node (3849, [3, 1283])
    (.node (3841, [23, 167])
      (.node (3837, [3, 1279])
        (.node (3835, [5, 13, 59]) (.node (3834, [2, 3, 3, 3, 71]) .nil .nil)
          (.node (3836, [2, 2, 7, 137]) .nil .nil))
        (.node (3839, [11, 349]) (.node (3838, [2, 19, 101]) .nil .nil)
          (.node (3840, [2, 2, 2, 2, 2, 2, 2, 2, 3, 5]) .nil .nil)))
      (.node (3845, [5, 769])
        (.node (3843, [3, 3, 7, 61]) (.node (3842, [2, 17, 113]) .nil .nil)
          (.node (3844, [2, 2, 31, 31]) .nil .nil))
        (.node (3847, [3847]) (.node (3846, [2, 3, 641]) .nil .nil)
          (.node (3848, [2, 2, 2, 13, 37]) .nil .nil))))
    (.node (3857, [7, 19, 29])
      (.node (3853, [3853])
        (.node (3851, [3851]) (.node (3850, [2, 5, 5, 7, 11]) .nil .nil)
          (.node (3852, [2, 2, 3, 3, 107]) .nil .nil))
        (.node (3855, [3, 5, 257]) (.node (3854, [2, 41, 47]) .nil .nil)
          (.node (3856, [2, 2, 2, 2, 241]) .nil .nil)))
      (.node (3861, [3, 3, 3, 11, 13])
        (.node (3859, [17, 227]) (.node (3858, [2, 3, 643]) .nil .nil)
          (.node (3860, [2, 2, 5, 193]) .nil .nil))
        (.node (3863, [3863]) (.node (3862, [2, 1931]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree136 : BinaryTree (ℕ × List ℕ) :=
  .node (3833, [3833]) routeSubtree134 routeSubtree135

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree137 : BinaryTree (ℕ × List ℕ) :=
  (.node (3880, [2, 2, 2, 5, 97])
    (.node (3872, [2, 2, 2, 2, 2, 11, 11])
      (.node (3868, [2, 2, 967])
        (.node (3866, [2, 1933]) (.node (3865, [5, 773]) .nil .nil)
          (.node (3867, [3, 1289]) .nil .nil))
        (.node (3870, [2, 3, 3, 5, 43]) (.node (3869, [53, 73]) .nil .nil)
          (.node (3871, [7, 7, 79]) .nil .nil)))
      (.node (3876, [2, 2, 3, 17, 19])
        (.node (3874, [2, 13, 149]) (.node (3873, [3, 1291]) .nil .nil)
          (.node (3875, [5, 5, 5, 31]) .nil .nil))
        (.node (3878, [2, 7, 277]) (.node (3877, [3877]) .nil .nil)
          (.node (3879, [3, 3, 431]) .nil .nil))))
    (.node (3888, [2, 2, 2, 2, 3, 3, 3, 3, 3])
      (.node (3884, [2, 2, 971])
        (.node (3882, [2, 3, 647]) (.node (3881, [3881]) .nil .nil)
          (.node (3883, [11, 353]) .nil .nil))
        (.node (3886, [2, 29, 67]) (.node (3885, [3, 5, 7, 37]) .nil .nil)
          (.node (3887, [13, 13, 23]) .nil .nil)))
      (.node (3892, [2, 2, 7, 139])
        (.node (3890, [2, 5, 389]) (.node (3889, [3889]) .nil .nil)
          (.node (3891, [3, 1297]) .nil .nil))
        (.node (3894, [2, 3, 11, 59]) (.node (3893, [17, 229]) .nil .nil)
          (.node (3895, [5, 19, 41]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree138 : BinaryTree (ℕ × List ℕ) :=
  (.node (3912, [2, 2, 2, 3, 163])
    (.node (3904, [2, 2, 2, 2, 2, 2, 61])
      (.node (3900, [2, 2, 3, 5, 5, 13])
        (.node (3898, [2, 1949]) (.node (3897, [3, 3, 433]) .nil .nil)
          (.node (3899, [7, 557]) .nil .nil))
        (.node (3902, [2, 1951]) (.node (3901, [47, 83]) .nil .nil)
          (.node (3903, [3, 1301]) .nil .nil)))
      (.node (3908, [2, 2, 977])
        (.node (3906, [2, 3, 3, 7, 31]) (.node (3905, [5, 11, 71]) .nil .nil)
          (.node (3907, [3907]) .nil .nil))
        (.node (3910, [2, 5, 17, 23]) (.node (3909, [3, 1303]) .nil .nil)
          (.node (3911, [3911]) .nil .nil))))
    (.node (3920, [2, 2, 2, 2, 5, 7, 7])
      (.node (3916, [2, 2, 11, 89])
        (.node (3914, [2, 19, 103]) (.node (3913, [7, 13, 43]) .nil .nil)
          (.node (3915, [3, 3, 3, 5, 29]) .nil .nil))
        (.node (3918, [2, 3, 653]) (.node (3917, [3917]) .nil .nil)
          (.node (3919, [3919]) .nil .nil)))
      (.node (3924, [2, 2, 3, 3, 109])
        (.node (3922, [2, 37, 53]) (.node (3921, [3, 1307]) .nil .nil)
          (.node (3923, [3923]) .nil .nil))
        (.node (3926, [2, 13, 151]) (.node (3925, [5, 5, 157]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree139 : BinaryTree (ℕ × List ℕ) :=
  .node (3896, [2, 2, 2, 487]) routeSubtree137 routeSubtree138

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree140 : BinaryTree (ℕ × List ℕ) :=
  .node (3864, [2, 2, 2, 3, 7, 23]) routeSubtree136 routeSubtree139

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree141 : BinaryTree (ℕ × List ℕ) :=
  .node (3801, [3, 7, 181]) routeSubtree133 routeSubtree140

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree142 : BinaryTree (ℕ × List ℕ) :=
  (.node (3943, [3943])
    (.node (3935, [5, 787])
      (.node (3931, [3931])
        (.node (3929, [3929]) (.node (3928, [2, 2, 2, 491]) .nil .nil)
          (.node (3930, [2, 3, 5, 131]) .nil .nil))
        (.node (3933, [3, 3, 19, 23]) (.node (3932, [2, 2, 983]) .nil .nil)
          (.node (3934, [2, 7, 281]) .nil .nil)))
      (.node (3939, [3, 13, 101])
        (.node (3937, [31, 127]) (.node (3936, [2, 2, 2, 2, 2, 3, 41]) .nil .nil)
          (.node (3938, [2, 11, 179]) .nil .nil))
        (.node (3941, [7, 563]) (.node (3940, [2, 2, 5, 197]) .nil .nil)
          (.node (3942, [2, 3, 3, 3, 73]) .nil .nil))))
    (.node (3951, [3, 3, 439])
      (.node (3947, [3947])
        (.node (3945, [3, 5, 263]) (.node (3944, [2, 2, 2, 17, 29]) .nil .nil)
          (.node (3946, [2, 1973]) .nil .nil))
        (.node (3949, [11, 359]) (.node (3948, [2, 2, 3, 7, 47]) .nil .nil)
          (.node (3950, [2, 5, 5, 79]) .nil .nil)))
      (.node (3955, [5, 7, 113])
        (.node (3953, [59, 67]) (.node (3952, [2, 2, 2, 2, 13, 19]) .nil .nil)
          (.node (3954, [2, 3, 659]) .nil .nil))
        (.node (3957, [3, 1319]) (.node (3956, [2, 2, 23, 43]) .nil .nil)
          (.node (3958, [2, 1979]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree143 : BinaryTree (ℕ × List ℕ) :=
  (.node (3975, [3, 5, 5, 53])
    (.node (3967, [3967])
      (.node (3963, [3, 1321])
        (.node (3961, [17, 233]) (.node (3960, [2, 2, 2, 3, 3, 5, 11]) .nil .nil)
          (.node (3962, [2, 7, 283]) .nil .nil))
        (.node (3965, [5, 13, 61]) (.node (3964, [2, 2, 991]) .nil .nil)
          (.node (3966, [2, 3, 661]) .nil .nil)))
      (.node (3971, [11, 19, 19])
        (.node (3969, [3, 3, 3, 3, 7, 7]) (.node (3968, [2, 2, 2, 2, 2, 2, 2, 31]) .nil .nil)
          (.node (3970, [2, 5, 397]) .nil .nil))
        (.node (3973, [29, 137]) (.node (3972, [2, 2, 3, 331]) .nil .nil)
          (.node (3974, [2, 1987]) .nil .nil))))
    (.node (3983, [7, 569])
      (.node (3979, [23, 173])
        (.node (3977, [41, 97]) (.node (3976, [2, 2, 2, 7, 71]) .nil .nil)
          (.node (3978, [2, 3, 3, 13, 17]) .nil .nil))
        (.node (3981, [3, 1327]) (.node (3980, [2, 2, 5, 199]) .nil .nil)
          (.node (3982, [2, 11, 181]) .nil .nil)))
      (.node (3987, [3, 3, 443])
        (.node (3985, [5, 797]) (.node (3984, [2, 2, 2, 2, 3, 83]) .nil .nil)
          (.node (3986, [2, 1993]) .nil .nil))
        (.node (3989, [3989]) (.node (3988, [2, 2, 997]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree144 : BinaryTree (ℕ × List ℕ) :=
  .node (3959, [37, 107]) routeSubtree142 routeSubtree143

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree145 : BinaryTree (ℕ × List ℕ) :=
  (.node (4007, [4007])
    (.node (3999, [3, 31, 43])
      (.node (3995, [5, 17, 47])
        (.node (3993, [3, 11, 11, 11]) (.node (3992, [2, 2, 2, 499]) .nil .nil)
          (.node (3994, [2, 1997]) .nil .nil))
        (.node (3997, [7, 571]) (.node (3996, [2, 2, 3, 3, 3, 37]) .nil .nil)
          (.node (3998, [2, 1999]) .nil .nil)))
      (.node (4003, [4003])
        (.node (4001, [4001]) (.node (4000, [2, 2, 2, 2, 2, 5, 5, 5]) .nil .nil)
          (.node (4002, [2, 3, 23, 29]) .nil .nil))
        (.node (4005, [3, 3, 5, 89]) (.node (4004, [2, 2, 7, 11, 13]) .nil .nil)
          (.node (4006, [2, 2003]) .nil .nil))))
    (.node (4015, [5, 11, 73])
      (.node (4011, [3, 7, 191])
        (.node (4009, [19, 211]) (.node (4008, [2, 2, 2, 3, 167]) .nil .nil)
          (.node (4010, [2, 5, 401]) .nil .nil))
        (.node (4013, [4013]) (.node (4012, [2, 2, 17, 59]) .nil .nil)
          (.node (4014, [2, 3, 3, 223]) .nil .nil)))
      (.node (4019, [4019])
        (.node (4017, [3, 13, 103]) (.node (4016, [2, 2, 2, 2, 251]) .nil .nil)
          (.node (4018, [2, 7, 7, 41]) .nil .nil))
        (.node (4021, [4021]) (.node (4020, [2, 2, 3, 5, 67]) .nil .nil)
          (.node (4022, [2, 2011]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree146 : BinaryTree (ℕ × List ℕ) :=
  (.node (4039, [7, 577])
    (.node (4031, [29, 139])
      (.node (4027, [4027])
        (.node (4025, [5, 5, 7, 23]) (.node (4024, [2, 2, 2, 503]) .nil .nil)
          (.node (4026, [2, 3, 11, 61]) .nil .nil))
        (.node (4029, [3, 17, 79]) (.node (4028, [2, 2, 19, 53]) .nil .nil)
          (.node (4030, [2, 5, 13, 31]) .nil .nil)))
      (.node (4035, [3, 5, 269])
        (.node (4033, [37, 109]) (.node (4032, [2, 2, 2, 2, 2, 2, 3, 3, 7]) .nil .nil)
          (.node (4034, [2, 2017]) .nil .nil))
        (.node (4037, [11, 367]) (.node (4036, [2, 2, 1009]) .nil .nil)
          (.node (4038, [2, 3, 673]) .nil .nil))))
    (.node (4047, [3, 19, 71])
      (.node (4043, [13, 311])
        (.node (4041, [3, 3, 449]) (.node (4040, [2, 2, 2, 5, 101]) .nil .nil)
          (.node (4042, [2, 43, 47]) .nil .nil))
        (.node (4045, [5, 809]) (.node (4044, [2, 2, 3, 337]) .nil .nil)
          (.node (4046, [2, 7, 17, 17]) .nil .nil)))
      (.node (4051, [4051])
        (.node (4049, [4049]) (.node (4048, [2, 2, 2, 2, 11, 23]) .nil .nil)
          (.node (4050, [2, 3, 3, 3, 3, 5, 5]) .nil .nil))
        (.node (4053, [3, 7, 193]) (.node (4052, [2, 2, 1013]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree147 : BinaryTree (ℕ × List ℕ) :=
  .node (4023, [3, 3, 3, 149]) routeSubtree145 routeSubtree146

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree148 : BinaryTree (ℕ × List ℕ) :=
  .node (3991, [13, 307]) routeSubtree144 routeSubtree147

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree149 : BinaryTree (ℕ × List ℕ) :=
  (.node (4070, [2, 5, 11, 37])
    (.node (4062, [2, 3, 677])
      (.node (4058, [2, 2029])
        (.node (4056, [2, 2, 2, 3, 13, 13]) (.node (4055, [5, 811]) .nil .nil)
          (.node (4057, [4057]) .nil .nil))
        (.node (4060, [2, 2, 5, 7, 29]) (.node (4059, [3, 3, 11, 41]) .nil .nil)
          (.node (4061, [31, 131]) .nil .nil)))
      (.node (4066, [2, 19, 107])
        (.node (4064, [2, 2, 2, 2, 2, 127]) (.node (4063, [17, 239]) .nil .nil)
          (.node (4065, [3, 5, 271]) .nil .nil))
        (.node (4068, [2, 2, 3, 3, 113]) (.node (4067, [7, 7, 83]) .nil .nil)
          (.node (4069, [13, 313]) .nil .nil))))
    (.node (4078, [2, 2039])
      (.node (4074, [2, 3, 7, 97])
        (.node (4072, [2, 2, 2, 509]) (.node (4071, [3, 23, 59]) .nil .nil)
          (.node (4073, [4073]) .nil .nil))
        (.node (4076, [2, 2, 1019]) (.node (4075, [5, 5, 163]) .nil .nil)
          (.node (4077, [3, 3, 3, 151]) .nil .nil)))
      (.node (4082, [2, 13, 157])
        (.node (4080, [2, 2, 2, 2, 3, 5, 17]) (.node (4079, [4079]) .nil .nil)
          (.node (4081, [7, 11, 53]) .nil .nil))
        (.node (4084, [2, 2, 1021]) (.node (4083, [3, 1361]) .nil .nil)
          (.node (4085, [5, 19, 43]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree150 : BinaryTree (ℕ × List ℕ) :=
  (.node (4102, [2, 7, 293])
    (.node (4094, [2, 23, 89])
      (.node (4090, [2, 5, 409])
        (.node (4088, [2, 2, 2, 7, 73]) (.node (4087, [61, 67]) .nil .nil)
          (.node (4089, [3, 29, 47]) .nil .nil))
        (.node (4092, [2, 2, 3, 11, 31]) (.node (4091, [4091]) .nil .nil)
          (.node (4093, [4093]) .nil .nil)))
      (.node (4098, [2, 3, 683])
        (.node (4096, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2])
          (.node (4095, [3, 3, 5, 7, 13]) .nil .nil) (.node (4097, [17, 241]) .nil .nil))
        (.node (4100, [2, 2, 5, 5, 41]) (.node (4099, [4099]) .nil .nil)
          (.node (4101, [3, 1367]) .nil .nil))))
    (.node (4110, [2, 3, 5, 137])
      (.node (4106, [2, 2053])
        (.node (4104, [2, 2, 2, 3, 3, 3, 19]) (.node (4103, [11, 373]) .nil .nil)
          (.node (4105, [5, 821]) .nil .nil))
        (.node (4108, [2, 2, 13, 79]) (.node (4107, [3, 37, 37]) .nil .nil)
          (.node (4109, [7, 587]) .nil .nil)))
      (.node (4114, [2, 11, 11, 17])
        (.node (4112, [2, 2, 2, 2, 257]) (.node (4111, [4111]) .nil .nil)
          (.node (4113, [3, 3, 457]) .nil .nil))
        (.node (4116, [2, 2, 3, 7, 7, 7]) (.node (4115, [5, 823]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree151 : BinaryTree (ℕ × List ℕ) :=
  .node (4086, [2, 3, 3, 227]) routeSubtree149 routeSubtree150

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree152 : BinaryTree (ℕ × List ℕ) :=
  (.node (4133, [4133])
    (.node (4125, [3, 5, 5, 5, 11])
      (.node (4121, [13, 317])
        (.node (4119, [3, 1373]) (.node (4118, [2, 29, 71]) .nil .nil)
          (.node (4120, [2, 2, 2, 5, 103]) .nil .nil))
        (.node (4123, [7, 19, 31]) (.node (4122, [2, 3, 3, 229]) .nil .nil)
          (.node (4124, [2, 2, 1031]) .nil .nil)))
      (.node (4129, [4129])
        (.node (4127, [4127]) (.node (4126, [2, 2063]) .nil .nil)
          (.node (4128, [2, 2, 2, 2, 2, 3, 43]) .nil .nil))
        (.node (4131, [3, 3, 3, 3, 3, 17]) (.node (4130, [2, 5, 7, 59]) .nil .nil)
          (.node (4132, [2, 2, 1033]) .nil .nil))))
    (.node (4141, [41, 101])
      (.node (4137, [3, 7, 197])
        (.node (4135, [5, 827]) (.node (4134, [2, 3, 13, 53]) .nil .nil)
          (.node (4136, [2, 2, 2, 11, 47]) .nil .nil))
        (.node (4139, [4139]) (.node (4138, [2, 2069]) .nil .nil)
          (.node (4140, [2, 2, 3, 3, 5, 23]) .nil .nil)))
      (.node (4145, [5, 829])
        (.node (4143, [3, 1381]) (.node (4142, [2, 19, 109]) .nil .nil)
          (.node (4144, [2, 2, 2, 2, 7, 37]) .nil .nil))
        (.node (4147, [11, 13, 29]) (.node (4146, [2, 3, 691]) .nil .nil)
          (.node (4148, [2, 2, 17, 61]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree153 : BinaryTree (ℕ × List ℕ) :=
  (.node (4165, [5, 7, 7, 17])
    (.node (4157, [4157])
      (.node (4153, [4153])
        (.node (4151, [7, 593]) (.node (4150, [2, 5, 5, 83]) .nil .nil)
          (.node (4152, [2, 2, 2, 3, 173]) .nil .nil))
        (.node (4155, [3, 5, 277]) (.node (4154, [2, 31, 67]) .nil .nil)
          (.node (4156, [2, 2, 1039]) .nil .nil)))
      (.node (4161, [3, 19, 73])
        (.node (4159, [4159]) (.node (4158, [2, 3, 3, 3, 7, 11]) .nil .nil)
          (.node (4160, [2, 2, 2, 2, 2, 2, 5, 13]) .nil .nil))
        (.node (4163, [23, 181]) (.node (4162, [2, 2081]) .nil .nil)
          (.node (4164, [2, 2, 3, 347]) .nil .nil))))
    (.node (4173, [3, 13, 107])
      (.node (4169, [11, 379])
        (.node (4167, [3, 3, 463]) (.node (4166, [2, 2083]) .nil .nil)
          (.node (4168, [2, 2, 2, 521]) .nil .nil))
        (.node (4171, [43, 97]) (.node (4170, [2, 3, 5, 139]) .nil .nil)
          (.node (4172, [2, 2, 7, 149]) .nil .nil)))
      (.node (4177, [4177])
        (.node (4175, [5, 5, 167]) (.node (4174, [2, 2087]) .nil .nil)
          (.node (4176, [2, 2, 2, 2, 3, 3, 29]) .nil .nil))
        (.node (4179, [3, 7, 199]) (.node (4178, [2, 2089]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree154 : BinaryTree (ℕ × List ℕ) :=
  .node (4149, [3, 3, 461]) routeSubtree152 routeSubtree153

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree155 : BinaryTree (ℕ × List ℕ) :=
  .node (4117, [23, 179]) routeSubtree151 routeSubtree154

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree156 : BinaryTree (ℕ × List ℕ) :=
  .node (4054, [2, 2027]) routeSubtree148 routeSubtree155

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree157 : BinaryTree (ℕ × List ℕ) :=
  .node (3927, [3, 7, 11, 17]) routeSubtree141 routeSubtree156

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree158 : BinaryTree (ℕ × List ℕ) :=
  (.node (4196, [2, 2, 1049])
    (.node (4188, [2, 2, 3, 349])
      (.node (4184, [2, 2, 2, 523])
        (.node (4182, [2, 3, 17, 41]) (.node (4181, [37, 113]) .nil .nil)
          (.node (4183, [47, 89]) .nil .nil))
        (.node (4186, [2, 7, 13, 23]) (.node (4185, [3, 3, 3, 5, 31]) .nil .nil)
          (.node (4187, [53, 79]) .nil .nil)))
      (.node (4192, [2, 2, 2, 2, 2, 131])
        (.node (4190, [2, 5, 419]) (.node (4189, [59, 71]) .nil .nil)
          (.node (4191, [3, 11, 127]) .nil .nil))
        (.node (4194, [2, 3, 3, 233]) (.node (4193, [7, 599]) .nil .nil)
          (.node (4195, [5, 839]) .nil .nil))))
    (.node (4204, [2, 2, 1051])
      (.node (4200, [2, 2, 2, 3, 5, 5, 7])
        (.node (4198, [2, 2099]) (.node (4197, [3, 1399]) .nil .nil)
          (.node (4199, [13, 17, 19]) .nil .nil))
        (.node (4202, [2, 11, 191]) (.node (4201, [4201]) .nil .nil)
          (.node (4203, [3, 3, 467]) .nil .nil)))
      (.node (4208, [2, 2, 2, 2, 263])
        (.node (4206, [2, 3, 701]) (.node (4205, [5, 29, 29]) .nil .nil)
          (.node (4207, [7, 601]) .nil .nil))
        (.node (4210, [2, 5, 421]) (.node (4209, [3, 23, 61]) .nil .nil)
          (.node (4211, [4211]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree159 : BinaryTree (ℕ × List ℕ) :=
  (.node (4228, [2, 2, 7, 151])
    (.node (4220, [2, 2, 5, 211])
      (.node (4216, [2, 2, 2, 17, 31])
        (.node (4214, [2, 7, 7, 43]) (.node (4213, [11, 383]) .nil .nil)
          (.node (4215, [3, 5, 281]) .nil .nil))
        (.node (4218, [2, 3, 19, 37]) (.node (4217, [4217]) .nil .nil)
          (.node (4219, [4219]) .nil .nil)))
      (.node (4224, [2, 2, 2, 2, 2, 2, 2, 3, 11])
        (.node (4222, [2, 2111]) (.node (4221, [3, 3, 7, 67]) .nil .nil)
          (.node (4223, [41, 103]) .nil .nil))
        (.node (4226, [2, 2113]) (.node (4225, [5, 5, 13, 13]) .nil .nil)
          (.node (4227, [3, 1409]) .nil .nil))))
    (.node (4236, [2, 2, 3, 353])
      (.node (4232, [2, 2, 2, 23, 23])
        (.node (4230, [2, 3, 3, 5, 47]) (.node (4229, [4229]) .nil .nil)
          (.node (4231, [4231]) .nil .nil))
        (.node (4234, [2, 29, 73]) (.node (4233, [3, 17, 83]) .nil .nil)
          (.node (4235, [5, 7, 11, 11]) .nil .nil)))
      (.node (4240, [2, 2, 2, 2, 5, 53])
        (.node (4238, [2, 13, 163]) (.node (4237, [19, 223]) .nil .nil)
          (.node (4239, [3, 3, 3, 157]) .nil .nil))
        (.node (4242, [2, 3, 7, 101]) (.node (4241, [4241]) .nil .nil)
          (.node (4243, [4243]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree160 : BinaryTree (ℕ × List ℕ) :=
  .node (4212, [2, 2, 3, 3, 3, 3, 13]) routeSubtree158 routeSubtree159

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree161 : BinaryTree (ℕ × List ℕ) :=
  (.node (4260, [2, 2, 3, 5, 71])
    (.node (4252, [2, 2, 1063])
      (.node (4248, [2, 2, 2, 3, 3, 59])
        (.node (4246, [2, 11, 193]) (.node (4245, [3, 5, 283]) .nil .nil)
          (.node (4247, [31, 137]) .nil .nil))
        (.node (4250, [2, 5, 5, 5, 17]) (.node (4249, [7, 607]) .nil .nil)
          (.node (4251, [3, 13, 109]) .nil .nil)))
      (.node (4256, [2, 2, 2, 2, 2, 7, 19])
        (.node (4254, [2, 3, 709]) (.node (4253, [4253]) .nil .nil)
          (.node (4255, [5, 23, 37]) .nil .nil))
        (.node (4258, [2, 2129]) (.node (4257, [3, 3, 11, 43]) .nil .nil)
          (.node (4259, [4259]) .nil .nil))))
    (.node (4268, [2, 2, 11, 97])
      (.node (4264, [2, 2, 2, 13, 41])
        (.node (4262, [2, 2131]) (.node (4261, [4261]) .nil .nil)
          (.node (4263, [3, 7, 7, 29]) .nil .nil))
        (.node (4266, [2, 3, 3, 3, 79]) (.node (4265, [5, 853]) .nil .nil)
          (.node (4267, [17, 251]) .nil .nil)))
      (.node (4272, [2, 2, 2, 2, 3, 89])
        (.node (4270, [2, 5, 7, 61]) (.node (4269, [3, 1423]) .nil .nil)
          (.node (4271, [4271]) .nil .nil))
        (.node (4274, [2, 2137]) (.node (4273, [4273]) .nil .nil)
          (.node (4275, [3, 3, 5, 5, 19]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree162 : BinaryTree (ℕ × List ℕ) :=
  (.node (4293, [3, 3, 3, 3, 53])
    (.node (4284, [2, 2, 3, 3, 7, 17])
      (.node (4280, [2, 2, 2, 5, 107])
        (.node (4278, [2, 3, 23, 31]) (.node (4277, [7, 13, 47]) .nil .nil)
          (.node (4279, [11, 389]) .nil .nil))
        (.node (4282, [2, 2141]) (.node (4281, [3, 1427]) .nil .nil)
          (.node (4283, [4283]) .nil .nil)))
      (.node (4288, [2, 2, 2, 2, 2, 2, 67])
        (.node (4286, [2, 2143]) (.node (4285, [5, 857]) .nil .nil)
          (.node (4287, [3, 1429]) .nil .nil))
        (.node (4291, [7, 613]) (.node (4289, [4289]) .nil .nil)
          (.node (4292, [2, 2, 29, 37]) .nil .nil))))
    (.node (4301, [11, 17, 23])
      (.node (4297, [4297])
        (.node (4295, [5, 859]) (.node (4294, [2, 19, 113]) .nil .nil)
          (.node (4296, [2, 2, 2, 3, 179]) .nil .nil))
        (.node (4299, [3, 1433]) (.node (4298, [2, 7, 307]) .nil .nil)
          (.node (4300, [2, 2, 5, 5, 43]) .nil .nil)))
      (.node (4305, [3, 5, 7, 41])
        (.node (4303, [13, 331]) (.node (4302, [2, 3, 3, 239]) .nil .nil)
          (.node (4304, [2, 2, 2, 2, 269]) .nil .nil))
        (.node (4307, [59, 73]) (.node (4306, [2, 2153]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree163 : BinaryTree (ℕ × List ℕ) :=
  .node (4276, [2, 2, 1069]) routeSubtree161 routeSubtree162

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree164 : BinaryTree (ℕ × List ℕ) :=
  .node (4244, [2, 2, 1061]) routeSubtree160 routeSubtree163

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree165 : BinaryTree (ℕ × List ℕ) :=
  (.node (4324, [2, 2, 23, 47])
    (.node (4316, [2, 2, 13, 83])
      (.node (4312, [2, 2, 2, 7, 7, 11])
        (.node (4310, [2, 5, 431]) (.node (4309, [31, 139]) .nil .nil)
          (.node (4311, [3, 3, 479]) .nil .nil))
        (.node (4314, [2, 3, 719]) (.node (4313, [19, 227]) .nil .nil)
          (.node (4315, [5, 863]) .nil .nil)))
      (.node (4320, [2, 2, 2, 2, 2, 3, 3, 3, 5])
        (.node (4318, [2, 17, 127]) (.node (4317, [3, 1439]) .nil .nil)
          (.node (4319, [7, 617]) .nil .nil))
        (.node (4322, [2, 2161]) (.node (4321, [29, 149]) .nil .nil)
          (.node (4323, [3, 11, 131]) .nil .nil))))
    (.node (4332, [2, 2, 3, 19, 19])
      (.node (4328, [2, 2, 2, 541])
        (.node (4326, [2, 3, 7, 103]) (.node (4325, [5, 5, 173]) .nil .nil)
          (.node (4327, [4327]) .nil .nil))
        (.node (4330, [2, 5, 433]) (.node (4329, [3, 3, 13, 37]) .nil .nil)
          (.node (4331, [61, 71]) .nil .nil)))
      (.node (4336, [2, 2, 2, 2, 271])
        (.node (4334, [2, 11, 197]) (.node (4333, [7, 619]) .nil .nil)
          (.node (4335, [3, 5, 17, 17]) .nil .nil))
        (.node (4338, [2, 3, 3, 241]) (.node (4337, [4337]) .nil .nil)
          (.node (4339, [4339]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree166 : BinaryTree (ℕ × List ℕ) :=
  (.node (4356, [2, 2, 3, 3, 11, 11])
    (.node (4348, [2, 2, 1087])
      (.node (4344, [2, 2, 2, 3, 181])
        (.node (4342, [2, 13, 167]) (.node (4341, [3, 1447]) .nil .nil)
          (.node (4343, [43, 101]) .nil .nil))
        (.node (4346, [2, 41, 53]) (.node (4345, [5, 11, 79]) .nil .nil)
          (.node (4347, [3, 3, 3, 7, 23]) .nil .nil)))
      (.node (4352, [2, 2, 2, 2, 2, 2, 2, 2, 17])
        (.node (4350, [2, 3, 5, 5, 29]) (.node (4349, [4349]) .nil .nil)
          (.node (4351, [19, 229]) .nil .nil))
        (.node (4354, [2, 7, 311]) (.node (4353, [3, 1451]) .nil .nil)
          (.node (4355, [5, 13, 67]) .nil .nil))))
    (.node (4364, [2, 2, 1091])
      (.node (4360, [2, 2, 2, 5, 109])
        (.node (4358, [2, 2179]) (.node (4357, [4357]) .nil .nil)
          (.node (4359, [3, 1453]) .nil .nil))
        (.node (4362, [2, 3, 727]) (.node (4361, [7, 7, 89]) .nil .nil)
          (.node (4363, [4363]) .nil .nil)))
      (.node (4368, [2, 2, 2, 2, 3, 7, 13])
        (.node (4366, [2, 37, 59]) (.node (4365, [3, 3, 5, 97]) .nil .nil)
          (.node (4367, [11, 397]) .nil .nil))
        (.node (4370, [2, 5, 19, 23]) (.node (4369, [17, 257]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree167 : BinaryTree (ℕ × List ℕ) :=
  .node (4340, [2, 2, 5, 7, 31]) routeSubtree165 routeSubtree166

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree168 : BinaryTree (ℕ × List ℕ) :=
  (.node (4387, [41, 107])
    (.node (4379, [29, 151])
      (.node (4375, [5, 5, 5, 5, 7])
        (.node (4373, [4373]) (.node (4372, [2, 2, 1093]) .nil .nil)
          (.node (4374, [2, 3, 3, 3, 3, 3, 3, 3]) .nil .nil))
        (.node (4377, [3, 1459]) (.node (4376, [2, 2, 2, 547]) .nil .nil)
          (.node (4378, [2, 11, 199]) .nil .nil)))
      (.node (4383, [3, 3, 487])
        (.node (4381, [13, 337]) (.node (4380, [2, 2, 3, 5, 73]) .nil .nil)
          (.node (4382, [2, 7, 313]) .nil .nil))
        (.node (4385, [5, 877]) (.node (4384, [2, 2, 2, 2, 2, 137]) .nil .nil)
          (.node (4386, [2, 3, 17, 43]) .nil .nil))))
    (.node (4395, [3, 5, 293])
      (.node (4391, [4391])
        (.node (4389, [3, 7, 11, 19]) (.node (4388, [2, 2, 1097]) .nil .nil)
          (.node (4390, [2, 5, 439]) .nil .nil))
        (.node (4393, [23, 191]) (.node (4392, [2, 2, 2, 3, 3, 61]) .nil .nil)
          (.node (4394, [2, 13, 13, 13]) .nil .nil)))
      (.node (4399, [53, 83])
        (.node (4397, [4397]) (.node (4396, [2, 2, 7, 157]) .nil .nil)
          (.node (4398, [2, 3, 733]) .nil .nil))
        (.node (4401, [3, 3, 3, 163]) (.node (4400, [2, 2, 2, 2, 5, 5, 11]) .nil .nil)
          (.node (4402, [2, 31, 71]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree169 : BinaryTree (ℕ × List ℕ) :=
  (.node (4419, [3, 3, 491])
    (.node (4411, [11, 401])
      (.node (4407, [3, 13, 113])
        (.node (4405, [5, 881]) (.node (4404, [2, 2, 3, 367]) .nil .nil)
          (.node (4406, [2, 2203]) .nil .nil))
        (.node (4409, [4409]) (.node (4408, [2, 2, 2, 19, 29]) .nil .nil)
          (.node (4410, [2, 3, 3, 5, 7, 7]) .nil .nil)))
      (.node (4415, [5, 883])
        (.node (4413, [3, 1471]) (.node (4412, [2, 2, 1103]) .nil .nil)
          (.node (4414, [2, 2207]) .nil .nil))
        (.node (4417, [7, 631]) (.node (4416, [2, 2, 2, 2, 2, 2, 3, 23]) .nil .nil)
          (.node (4418, [2, 47, 47]) .nil .nil))))
    (.node (4427, [19, 233])
      (.node (4423, [4423])
        (.node (4421, [4421]) (.node (4420, [2, 2, 5, 13, 17]) .nil .nil)
          (.node (4422, [2, 3, 11, 67]) .nil .nil))
        (.node (4425, [3, 5, 5, 59]) (.node (4424, [2, 2, 2, 7, 79]) .nil .nil)
          (.node (4426, [2, 2213]) .nil .nil)))
      (.node (4431, [3, 7, 211])
        (.node (4429, [43, 103]) (.node (4428, [2, 2, 3, 3, 3, 41]) .nil .nil)
          (.node (4430, [2, 5, 443]) .nil .nil))
        (.node (4433, [11, 13, 31]) (.node (4432, [2, 2, 2, 2, 277]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree170 : BinaryTree (ℕ × List ℕ) :=
  .node (4403, [7, 17, 37]) routeSubtree168 routeSubtree169

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree171 : BinaryTree (ℕ × List ℕ) :=
  .node (4371, [3, 31, 47]) routeSubtree167 routeSubtree170

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree172 : BinaryTree (ℕ × List ℕ) :=
  .node (4308, [2, 2, 3, 359]) routeSubtree164 routeSubtree171

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree173 : BinaryTree (ℕ × List ℕ) :=
  (.node (4450, [2, 5, 5, 89])
    (.node (4442, [2, 2221])
      (.node (4438, [2, 7, 317])
        (.node (4436, [2, 2, 1109]) (.node (4435, [5, 887]) .nil .nil)
          (.node (4437, [3, 3, 17, 29]) .nil .nil))
        (.node (4440, [2, 2, 2, 3, 5, 37]) (.node (4439, [23, 193]) .nil .nil)
          (.node (4441, [4441]) .nil .nil)))
      (.node (4446, [2, 3, 3, 13, 19])
        (.node (4444, [2, 2, 11, 101]) (.node (4443, [3, 1481]) .nil .nil)
          (.node (4445, [5, 7, 127]) .nil .nil))
        (.node (4448, [2, 2, 2, 2, 2, 139]) (.node (4447, [4447]) .nil .nil)
          (.node (4449, [3, 1483]) .nil .nil))))
    (.node (4458, [2, 3, 743])
      (.node (4454, [2, 17, 131])
        (.node (4452, [2, 2, 3, 7, 53]) (.node (4451, [4451]) .nil .nil)
          (.node (4453, [61, 73]) .nil .nil))
        (.node (4456, [2, 2, 2, 557]) (.node (4455, [3, 3, 3, 3, 5, 11]) .nil .nil)
          (.node (4457, [4457]) .nil .nil)))
      (.node (4462, [2, 23, 97])
        (.node (4460, [2, 2, 5, 223]) (.node (4459, [7, 7, 7, 13]) .nil .nil)
          (.node (4461, [3, 1487]) .nil .nil))
        (.node (4464, [2, 2, 2, 2, 3, 3, 31]) (.node (4463, [4463]) .nil .nil)
          (.node (4465, [5, 19, 47]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree174 : BinaryTree (ℕ × List ℕ) :=
  (.node (4482, [2, 3, 3, 3, 83])
    (.node (4474, [2, 2237])
      (.node (4470, [2, 3, 5, 149])
        (.node (4468, [2, 2, 1117]) (.node (4467, [3, 1489]) .nil .nil)
          (.node (4469, [41, 109]) .nil .nil))
        (.node (4472, [2, 2, 2, 13, 43]) (.node (4471, [17, 263]) .nil .nil)
          (.node (4473, [3, 3, 7, 71]) .nil .nil)))
      (.node (4478, [2, 2239])
        (.node (4476, [2, 2, 3, 373]) (.node (4475, [5, 5, 179]) .nil .nil)
          (.node (4477, [11, 11, 37]) .nil .nil))
        (.node (4480, [2, 2, 2, 2, 2, 2, 2, 5, 7]) (.node (4479, [3, 1493]) .nil .nil)
          (.node (4481, [4481]) .nil .nil))))
    (.node (4490, [2, 5, 449])
      (.node (4486, [2, 2243])
        (.node (4484, [2, 2, 19, 59]) (.node (4483, [4483]) .nil .nil)
          (.node (4485, [3, 5, 13, 23]) .nil .nil))
        (.node (4488, [2, 2, 2, 3, 11, 17]) (.node (4487, [7, 641]) .nil .nil)
          (.node (4489, [67, 67]) .nil .nil)))
      (.node (4494, [2, 3, 7, 107])
        (.node (4492, [2, 2, 1123]) (.node (4491, [3, 3, 499]) .nil .nil)
          (.node (4493, [4493]) .nil .nil))
        (.node (4496, [2, 2, 2, 2, 281]) (.node (4495, [5, 29, 31]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree175 : BinaryTree (ℕ × List ℕ) :=
  .node (4466, [2, 7, 11, 29]) routeSubtree173 routeSubtree174

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree176 : BinaryTree (ℕ × List ℕ) :=
  (.node (4513, [4513])
    (.node (4505, [5, 17, 53])
      (.node (4501, [7, 643])
        (.node (4499, [11, 409]) (.node (4498, [2, 13, 173]) .nil .nil)
          (.node (4500, [2, 2, 3, 3, 5, 5, 5]) .nil .nil))
        (.node (4503, [3, 19, 79]) (.node (4502, [2, 2251]) .nil .nil)
          (.node (4504, [2, 2, 2, 563]) .nil .nil)))
      (.node (4509, [3, 3, 3, 167])
        (.node (4507, [4507]) (.node (4506, [2, 3, 751]) .nil .nil)
          (.node (4508, [2, 2, 7, 7, 23]) .nil .nil))
        (.node (4511, [13, 347]) (.node (4510, [2, 5, 11, 41]) .nil .nil)
          (.node (4512, [2, 2, 2, 2, 2, 3, 47]) .nil .nil))))
    (.node (4521, [3, 11, 137])
      (.node (4517, [4517])
        (.node (4515, [3, 5, 7, 43]) (.node (4514, [2, 37, 61]) .nil .nil)
          (.node (4516, [2, 2, 1129]) .nil .nil))
        (.node (4519, [4519]) (.node (4518, [2, 3, 3, 251]) .nil .nil)
          (.node (4520, [2, 2, 2, 5, 113]) .nil .nil)))
      (.node (4525, [5, 5, 181])
        (.node (4523, [4523]) (.node (4522, [2, 7, 17, 19]) .nil .nil)
          (.node (4524, [2, 2, 3, 13, 29]) .nil .nil))
        (.node (4527, [3, 3, 503]) (.node (4526, [2, 31, 73]) .nil .nil)
          (.node (4528, [2, 2, 2, 2, 283]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree177 : BinaryTree (ℕ × List ℕ) :=
  (.node (4545, [3, 3, 5, 101])
    (.node (4537, [13, 349])
      (.node (4533, [3, 1511])
        (.node (4531, [23, 197]) (.node (4530, [2, 3, 5, 151]) .nil .nil)
          (.node (4532, [2, 2, 11, 103]) .nil .nil))
        (.node (4535, [5, 907]) (.node (4534, [2, 2267]) .nil .nil)
          (.node (4536, [2, 2, 2, 3, 3, 3, 3, 7]) .nil .nil)))
      (.node (4541, [19, 239])
        (.node (4539, [3, 17, 89]) (.node (4538, [2, 2269]) .nil .nil)
          (.node (4540, [2, 2, 5, 227]) .nil .nil))
        (.node (4543, [7, 11, 59]) (.node (4542, [2, 3, 757]) .nil .nil)
          (.node (4544, [2, 2, 2, 2, 2, 2, 71]) .nil .nil))))
    (.node (4553, [29, 157])
      (.node (4549, [4549])
        (.node (4547, [4547]) (.node (4546, [2, 2273]) .nil .nil)
          (.node (4548, [2, 2, 3, 379]) .nil .nil))
        (.node (4551, [3, 37, 41]) (.node (4550, [2, 5, 5, 7, 13]) .nil .nil)
          (.node (4552, [2, 2, 2, 569]) .nil .nil)))
      (.node (4557, [3, 7, 7, 31])
        (.node (4555, [5, 911]) (.node (4554, [2, 3, 3, 11, 23]) .nil .nil)
          (.node (4556, [2, 2, 17, 67]) .nil .nil))
        (.node (4559, [47, 97]) (.node (4558, [2, 43, 53]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree178 : BinaryTree (ℕ × List ℕ) :=
  .node (4529, [7, 647]) routeSubtree176 routeSubtree177

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree179 : BinaryTree (ℕ × List ℕ) :=
  .node (4497, [3, 1499]) routeSubtree175 routeSubtree178

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree180 : BinaryTree (ℕ × List ℕ) :=
  (.node (4576, [2, 2, 2, 2, 2, 11, 13])
    (.node (4568, [2, 2, 2, 571])
      (.node (4564, [2, 2, 7, 163])
        (.node (4562, [2, 2281]) (.node (4561, [4561]) .nil .nil)
          (.node (4563, [3, 3, 3, 13, 13]) .nil .nil))
        (.node (4566, [2, 3, 761]) (.node (4565, [5, 11, 83]) .nil .nil)
          (.node (4567, [4567]) .nil .nil)))
      (.node (4572, [2, 2, 3, 3, 127])
        (.node (4570, [2, 5, 457]) (.node (4569, [3, 1523]) .nil .nil)
          (.node (4571, [7, 653]) .nil .nil))
        (.node (4574, [2, 2287]) (.node (4573, [17, 269]) .nil .nil)
          (.node (4575, [3, 5, 5, 61]) .nil .nil))))
    (.node (4584, [2, 2, 2, 3, 191])
      (.node (4580, [2, 2, 5, 229])
        (.node (4578, [2, 3, 7, 109]) (.node (4577, [23, 199]) .nil .nil)
          (.node (4579, [19, 241]) .nil .nil))
        (.node (4582, [2, 29, 79]) (.node (4581, [3, 3, 509]) .nil .nil)
          (.node (4583, [4583]) .nil .nil)))
      (.node (4588, [2, 2, 31, 37])
        (.node (4586, [2, 2293]) (.node (4585, [5, 7, 131]) .nil .nil)
          (.node (4587, [3, 11, 139]) .nil .nil))
        (.node (4590, [2, 3, 3, 3, 5, 17]) (.node (4589, [13, 353]) .nil .nil)
          (.node (4591, [4591]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree181 : BinaryTree (ℕ × List ℕ) :=
  (.node (4608, [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3])
    (.node (4600, [2, 2, 2, 5, 5, 23])
      (.node (4596, [2, 2, 3, 383])
        (.node (4594, [2, 2297]) (.node (4593, [3, 1531]) .nil .nil)
          (.node (4595, [5, 919]) .nil .nil))
        (.node (4598, [2, 11, 11, 19]) (.node (4597, [4597]) .nil .nil)
          (.node (4599, [3, 3, 7, 73]) .nil .nil)))
      (.node (4604, [2, 2, 1151])
        (.node (4602, [2, 3, 13, 59]) (.node (4601, [43, 107]) .nil .nil)
          (.node (4603, [4603]) .nil .nil))
        (.node (4606, [2, 7, 7, 47]) (.node (4605, [3, 5, 307]) .nil .nil)
          (.node (4607, [17, 271]) .nil .nil))))
    (.node (4616, [2, 2, 2, 577])
      (.node (4612, [2, 2, 1153])
        (.node (4610, [2, 5, 461]) (.node (4609, [11, 419]) .nil .nil)
          (.node (4611, [3, 29, 53]) .nil .nil))
        (.node (4614, [2, 3, 769]) (.node (4613, [7, 659]) .nil .nil)
          (.node (4615, [5, 13, 71]) .nil .nil)))
      (.node (4621, [4621])
        (.node (4618, [2, 2309]) (.node (4617, [3, 3, 3, 3, 3, 19]) .nil .nil)
          (.node (4619, [31, 149]) .nil .nil))
        (.node (4623, [3, 23, 67]) (.node (4622, [2, 2311]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree182 : BinaryTree (ℕ × List ℕ) :=
  .node (4592, [2, 2, 2, 2, 7, 41]) routeSubtree180 routeSubtree181

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree183 : BinaryTree (ℕ × List ℕ) :=
  (.node (4640, [2, 2, 2, 2, 2, 5, 29])
    (.node (4632, [2, 2, 2, 3, 193])
      (.node (4628, [2, 2, 13, 89])
        (.node (4626, [2, 3, 3, 257]) (.node (4625, [5, 5, 5, 37]) .nil .nil)
          (.node (4627, [7, 661]) .nil .nil))
        (.node (4630, [2, 5, 463]) (.node (4629, [3, 1543]) .nil .nil)
          (.node (4631, [11, 421]) .nil .nil)))
      (.node (4636, [2, 2, 19, 61])
        (.node (4634, [2, 7, 331]) (.node (4633, [41, 113]) .nil .nil)
          (.node (4635, [3, 3, 5, 103]) .nil .nil))
        (.node (4638, [2, 3, 773]) (.node (4637, [4637]) .nil .nil)
          (.node (4639, [4639]) .nil .nil))))
    (.node (4648, [2, 2, 2, 7, 83])
      (.node (4644, [2, 2, 3, 3, 3, 43])
        (.node (4642, [2, 11, 211]) (.node (4641, [3, 7, 13, 17]) .nil .nil)
          (.node (4643, [4643]) .nil .nil))
        (.node (4646, [2, 23, 101]) (.node (4645, [5, 929]) .nil .nil)
          (.node (4647, [3, 1549]) .nil .nil)))
      (.node (4652, [2, 2, 1163])
        (.node (4650, [2, 3, 5, 5, 31]) (.node (4649, [4649]) .nil .nil)
          (.node (4651, [4651]) .nil .nil))
        (.node (4654, [2, 13, 179]) (.node (4653, [3, 3, 11, 47]) .nil .nil)
          (.node (4655, [5, 7, 7, 19]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree184 : BinaryTree (ℕ × List ℕ) :=
  (.node (4672, [2, 2, 2, 2, 2, 2, 73])
    (.node (4664, [2, 2, 2, 11, 53])
      (.node (4660, [2, 2, 5, 233])
        (.node (4658, [2, 17, 137]) (.node (4657, [4657]) .nil .nil)
          (.node (4659, [3, 1553]) .nil .nil))
        (.node (4662, [2, 3, 3, 7, 37]) (.node (4661, [59, 79]) .nil .nil)
          (.node (4663, [4663]) .nil .nil)))
      (.node (4668, [2, 2, 3, 389])
        (.node (4666, [2, 2333]) (.node (4665, [3, 5, 311]) .nil .nil)
          (.node (4667, [13, 359]) .nil .nil))
        (.node (4670, [2, 5, 467]) (.node (4669, [7, 23, 29]) .nil .nil)
          (.node (4671, [3, 3, 3, 173]) .nil .nil))))
    (.node (4680, [2, 2, 2, 3, 3, 5, 13])
      (.node (4676, [2, 2, 7, 167])
        (.node (4674, [2, 3, 19, 41]) (.node (4673, [4673]) .nil .nil)
          (.node (4675, [5, 5, 11, 17]) .nil .nil))
        (.node (4678, [2, 2339]) (.node (4677, [3, 1559]) .nil .nil)
          (.node (4679, [4679]) .nil .nil)))
      (.node (4684, [2, 2, 1171])
        (.node (4682, [2, 2341]) (.node (4681, [31, 151]) .nil .nil)
          (.node (4683, [3, 7, 223]) .nil .nil))
        (.node (4686, [2, 3, 11, 71]) (.node (4685, [5, 937]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree185 : BinaryTree (ℕ × List ℕ) :=
  .node (4656, [2, 2, 2, 2, 3, 97]) routeSubtree183 routeSubtree184

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree186 : BinaryTree (ℕ × List ℕ) :=
  .node (4624, [2, 2, 2, 2, 17, 17]) routeSubtree182 routeSubtree185

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree187 : BinaryTree (ℕ × List ℕ) :=
  .node (4560, [2, 2, 2, 2, 3, 5, 19]) routeSubtree179 routeSubtree186

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree188 : BinaryTree (ℕ × List ℕ) :=
  .node (4434, [2, 3, 739]) routeSubtree172 routeSubtree187

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree189 : BinaryTree (ℕ × List ℕ) :=
  .node (4180, [2, 2, 5, 11, 19]) routeSubtree157 routeSubtree188

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree190 : BinaryTree (ℕ × List ℕ) :=
  (.node (4703, [4703])
    (.node (4695, [3, 5, 313])
      (.node (4691, [4691])
        (.node (4689, [3, 3, 521]) (.node (4688, [2, 2, 2, 2, 293]) .nil .nil)
          (.node (4690, [2, 5, 7, 67]) .nil .nil))
        (.node (4693, [13, 19, 19]) (.node (4692, [2, 2, 3, 17, 23]) .nil .nil)
          (.node (4694, [2, 2347]) .nil .nil)))
      (.node (4699, [37, 127])
        (.node (4697, [7, 11, 61]) (.node (4696, [2, 2, 2, 587]) .nil .nil)
          (.node (4698, [2, 3, 3, 3, 3, 29]) .nil .nil))
        (.node (4701, [3, 1567]) (.node (4700, [2, 2, 5, 5, 47]) .nil .nil)
          (.node (4702, [2, 2351]) .nil .nil))))
    (.node (4711, [7, 673])
      (.node (4707, [3, 3, 523])
        (.node (4705, [5, 941]) (.node (4704, [2, 2, 2, 2, 2, 3, 7, 7]) .nil .nil)
          (.node (4706, [2, 13, 181]) .nil .nil))
        (.node (4709, [17, 277]) (.node (4708, [2, 2, 11, 107]) .nil .nil)
          (.node (4710, [2, 3, 5, 157]) .nil .nil)))
      (.node (4715, [5, 23, 41])
        (.node (4713, [3, 1571]) (.node (4712, [2, 2, 2, 19, 31]) .nil .nil)
          (.node (4714, [2, 2357]) .nil .nil))
        (.node (4717, [53, 89]) (.node (4716, [2, 2, 3, 3, 131]) .nil .nil)
          (.node (4718, [2, 7, 337]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree191 : BinaryTree (ℕ × List ℕ) :=
  (.node (4735, [5, 947])
    (.node (4727, [29, 163])
      (.node (4723, [4723])
        (.node (4721, [4721]) (.node (4720, [2, 2, 2, 2, 5, 59]) .nil .nil)
          (.node (4722, [2, 3, 787]) .nil .nil))
        (.node (4725, [3, 3, 3, 5, 5, 7]) (.node (4724, [2, 2, 1181]) .nil .nil)
          (.node (4726, [2, 17, 139]) .nil .nil)))
      (.node (4731, [3, 19, 83])
        (.node (4729, [4729]) (.node (4728, [2, 2, 2, 3, 197]) .nil .nil)
          (.node (4730, [2, 5, 11, 43]) .nil .nil))
        (.node (4733, [4733]) (.node (4732, [2, 2, 7, 13, 13]) .nil .nil)
          (.node (4734, [2, 3, 3, 263]) .nil .nil))))
    (.node (4743, [3, 3, 17, 31])
      (.node (4739, [7, 677])
        (.node (4737, [3, 1579]) (.node (4736, [2, 2, 2, 2, 2, 2, 2, 37]) .nil .nil)
          (.node (4738, [2, 23, 103]) .nil .nil))
        (.node (4741, [11, 431]) (.node (4740, [2, 2, 3, 5, 79]) .nil .nil)
          (.node (4742, [2, 2371]) .nil .nil)))
      (.node (4747, [47, 101])
        (.node (4745, [5, 13, 73]) (.node (4744, [2, 2, 2, 593]) .nil .nil)
          (.node (4746, [2, 3, 7, 113]) .nil .nil))
        (.node (4749, [3, 1583]) (.node (4748, [2, 2, 1187]) .nil .nil)
          (.node (4750, [2, 5, 5, 5, 19]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree192 : BinaryTree (ℕ × List ℕ) :=
  .node (4719, [3, 11, 11, 13]) routeSubtree190 routeSubtree191

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree193 : BinaryTree (ℕ × List ℕ) :=
  (.node (4767, [3, 7, 227])
    (.node (4759, [4759])
      (.node (4755, [3, 5, 317])
        (.node (4753, [7, 7, 97]) (.node (4752, [2, 2, 2, 2, 3, 3, 3, 11]) .nil .nil)
          (.node (4754, [2, 2377]) .nil .nil))
        (.node (4757, [67, 71]) (.node (4756, [2, 2, 29, 41]) .nil .nil)
          (.node (4758, [2, 3, 13, 61]) .nil .nil)))
      (.node (4763, [11, 433])
        (.node (4761, [3, 3, 23, 23]) (.node (4760, [2, 2, 2, 5, 7, 17]) .nil .nil)
          (.node (4762, [2, 2381]) .nil .nil))
        (.node (4765, [5, 953]) (.node (4764, [2, 2, 3, 397]) .nil .nil)
          (.node (4766, [2, 2383]) .nil .nil))))
    (.node (4775, [5, 5, 191])
      (.node (4771, [13, 367])
        (.node (4769, [19, 251]) (.node (4768, [2, 2, 2, 2, 2, 149]) .nil .nil)
          (.node (4770, [2, 3, 3, 5, 53]) .nil .nil))
        (.node (4773, [3, 37, 43]) (.node (4772, [2, 2, 1193]) .nil .nil)
          (.node (4774, [2, 7, 11, 31]) .nil .nil)))
      (.node (4779, [3, 3, 3, 3, 59])
        (.node (4777, [17, 281]) (.node (4776, [2, 2, 2, 3, 199]) .nil .nil)
          (.node (4778, [2, 2389]) .nil .nil))
        (.node (4781, [7, 683]) (.node (4780, [2, 2, 5, 239]) .nil .nil)
          (.node (4782, [2, 3, 797]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree194 : BinaryTree (ℕ × List ℕ) :=
  (.node (4799, [4799])
    (.node (4791, [3, 1597])
      (.node (4787, [4787])
        (.node (4785, [3, 5, 11, 29]) (.node (4784, [2, 2, 2, 2, 13, 23]) .nil .nil)
          (.node (4786, [2, 2393]) .nil .nil))
        (.node (4789, [4789]) (.node (4788, [2, 2, 3, 3, 7, 19]) .nil .nil)
          (.node (4790, [2, 5, 479]) .nil .nil)))
      (.node (4795, [5, 7, 137])
        (.node (4793, [4793]) (.node (4792, [2, 2, 2, 599]) .nil .nil)
          (.node (4794, [2, 3, 17, 47]) .nil .nil))
        (.node (4797, [3, 3, 13, 41]) (.node (4796, [2, 2, 11, 109]) .nil .nil)
          (.node (4798, [2, 2399]) .nil .nil))))
    (.node (4807, [11, 19, 23])
      (.node (4803, [3, 1601])
        (.node (4801, [4801]) (.node (4800, [2, 2, 2, 2, 2, 2, 3, 5, 5]) .nil .nil)
          (.node (4802, [2, 7, 7, 7, 7]) .nil .nil))
        (.node (4805, [5, 31, 31]) (.node (4804, [2, 2, 1201]) .nil .nil)
          (.node (4806, [2, 3, 3, 3, 89]) .nil .nil)))
      (.node (4811, [17, 283])
        (.node (4809, [3, 7, 229]) (.node (4808, [2, 2, 2, 601]) .nil .nil)
          (.node (4810, [2, 5, 13, 37]) .nil .nil))
        (.node (4813, [4813]) (.node (4812, [2, 2, 3, 401]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree195 : BinaryTree (ℕ × List ℕ) :=
  .node (4783, [4783]) routeSubtree193 routeSubtree194

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree196 : BinaryTree (ℕ × List ℕ) :=
  .node (4751, [4751]) routeSubtree192 routeSubtree195

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree197 : BinaryTree (ℕ × List ℕ) :=
  (.node (4831, [4831])
    (.node (4822, [2, 2411])
      (.node (4818, [2, 3, 11, 73])
        (.node (4816, [2, 2, 2, 2, 7, 43]) (.node (4815, [3, 3, 5, 107]) .nil .nil)
          (.node (4817, [4817]) .nil .nil))
        (.node (4820, [2, 2, 5, 241]) (.node (4819, [61, 79]) .nil .nil)
          (.node (4821, [3, 1607]) .nil .nil)))
      (.node (4826, [2, 19, 127])
        (.node (4824, [2, 2, 2, 3, 3, 67]) (.node (4823, [7, 13, 53]) .nil .nil)
          (.node (4825, [5, 5, 193]) .nil .nil))
        (.node (4828, [2, 2, 17, 71]) (.node (4827, [3, 1609]) .nil .nil)
          (.node (4829, [11, 439]) .nil .nil))))
    (.node (4839, [3, 1613])
      (.node (4835, [5, 967])
        (.node (4833, [3, 3, 3, 179]) (.node (4832, [2, 2, 2, 2, 2, 151]) .nil .nil)
          (.node (4834, [2, 2417]) .nil .nil))
        (.node (4837, [7, 691]) (.node (4836, [2, 2, 3, 13, 31]) .nil .nil)
          (.node (4838, [2, 41, 59]) .nil .nil)))
      (.node (4843, [29, 167])
        (.node (4841, [47, 103]) (.node (4840, [2, 2, 2, 5, 11, 11]) .nil .nil)
          (.node (4842, [2, 3, 3, 269]) .nil .nil))
        (.node (4845, [3, 5, 17, 19]) (.node (4844, [2, 2, 7, 173]) .nil .nil)
          (.node (4846, [2, 2423]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree198 : BinaryTree (ℕ × List ℕ) :=
  (.node (4863, [3, 1621])
    (.node (4855, [5, 971])
      (.node (4851, [3, 3, 7, 7, 11])
        (.node (4849, [13, 373]) (.node (4848, [2, 2, 2, 2, 3, 101]) .nil .nil)
          (.node (4850, [2, 5, 5, 97]) .nil .nil))
        (.node (4853, [23, 211]) (.node (4852, [2, 2, 1213]) .nil .nil)
          (.node (4854, [2, 3, 809]) .nil .nil)))
      (.node (4859, [43, 113])
        (.node (4857, [3, 1619]) (.node (4856, [2, 2, 2, 607]) .nil .nil)
          (.node (4858, [2, 7, 347]) .nil .nil))
        (.node (4861, [4861]) (.node (4860, [2, 2, 3, 3, 3, 3, 3, 5]) .nil .nil)
          (.node (4862, [2, 11, 13, 17]) .nil .nil))))
    (.node (4871, [4871])
      (.node (4867, [31, 157])
        (.node (4865, [5, 7, 139]) (.node (4864, [2, 2, 2, 2, 2, 2, 2, 2, 19]) .nil .nil)
          (.node (4866, [2, 3, 811]) .nil .nil))
        (.node (4869, [3, 3, 541]) (.node (4868, [2, 2, 1217]) .nil .nil)
          (.node (4870, [2, 5, 487]) .nil .nil)))
      (.node (4875, [3, 5, 5, 5, 13])
        (.node (4873, [11, 443]) (.node (4872, [2, 2, 2, 3, 7, 29]) .nil .nil)
          (.node (4874, [2, 2437]) .nil .nil))
        (.node (4877, [4877]) (.node (4876, [2, 2, 23, 53]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree199 : BinaryTree (ℕ × List ℕ) :=
  .node (4847, [37, 131]) routeSubtree197 routeSubtree198

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree200 : BinaryTree (ℕ × List ℕ) :=
  (.node (4894, [2, 2447])
    (.node (4886, [2, 7, 349])
      (.node (4882, [2, 2441])
        (.node (4880, [2, 2, 2, 2, 5, 61]) (.node (4879, [7, 17, 41]) .nil .nil)
          (.node (4881, [3, 1627]) .nil .nil))
        (.node (4884, [2, 2, 3, 11, 37]) (.node (4883, [19, 257]) .nil .nil)
          (.node (4885, [5, 977]) .nil .nil)))
      (.node (4890, [2, 3, 5, 163])
        (.node (4888, [2, 2, 2, 13, 47]) (.node (4887, [3, 3, 3, 181]) .nil .nil)
          (.node (4889, [4889]) .nil .nil))
        (.node (4892, [2, 2, 1223]) (.node (4891, [67, 73]) .nil .nil)
          (.node (4893, [3, 7, 233]) .nil .nil))))
    (.node (4902, [2, 3, 19, 43])
      (.node (4898, [2, 31, 79])
        (.node (4896, [2, 2, 2, 2, 2, 3, 3, 17]) (.node (4895, [5, 11, 89]) .nil .nil)
          (.node (4897, [59, 83]) .nil .nil))
        (.node (4900, [2, 2, 5, 5, 7, 7]) (.node (4899, [3, 23, 71]) .nil .nil)
          (.node (4901, [13, 13, 29]) .nil .nil)))
      (.node (4906, [2, 11, 223])
        (.node (4904, [2, 2, 2, 613]) (.node (4903, [4903]) .nil .nil)
          (.node (4905, [3, 3, 5, 109]) .nil .nil))
        (.node (4908, [2, 2, 3, 409]) (.node (4907, [7, 701]) .nil .nil)
          (.node (4909, [4909]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree201 : BinaryTree (ℕ × List ℕ) :=
  (.node (4926, [2, 3, 821])
    (.node (4918, [2, 2459])
      (.node (4914, [2, 3, 3, 3, 7, 13])
        (.node (4912, [2, 2, 2, 2, 307]) (.node (4911, [3, 1637]) .nil .nil)
          (.node (4913, [17, 17, 17]) .nil .nil))
        (.node (4916, [2, 2, 1229]) (.node (4915, [5, 983]) .nil .nil)
          (.node (4917, [3, 11, 149]) .nil .nil)))
      (.node (4922, [2, 23, 107])
        (.node (4920, [2, 2, 2, 3, 5, 41]) (.node (4919, [4919]) .nil .nil)
          (.node (4921, [7, 19, 37]) .nil .nil))
        (.node (4924, [2, 2, 1231]) (.node (4923, [3, 3, 547]) .nil .nil)
          (.node (4925, [5, 5, 197]) .nil .nil))))
    (.node (4934, [2, 2467])
      (.node (4930, [2, 5, 17, 29])
        (.node (4928, [2, 2, 2, 2, 2, 2, 7, 11]) (.node (4927, [13, 379]) .nil .nil)
          (.node (4929, [3, 31, 53]) .nil .nil))
        (.node (4932, [2, 2, 3, 3, 137]) (.node (4931, [4931]) .nil .nil)
          (.node (4933, [4933]) .nil .nil)))
      (.node (4938, [2, 3, 823])
        (.node (4936, [2, 2, 2, 617]) (.node (4935, [3, 5, 7, 47]) .nil .nil)
          (.node (4937, [4937]) .nil .nil))
        (.node (4940, [2, 2, 5, 13, 19]) (.node (4939, [11, 449]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree202 : BinaryTree (ℕ × List ℕ) :=
  .node (4910, [2, 5, 491]) routeSubtree200 routeSubtree201

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree203 : BinaryTree (ℕ × List ℕ) :=
  .node (4878, [2, 3, 3, 271]) routeSubtree199 routeSubtree202

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree204 : BinaryTree (ℕ × List ℕ) :=
  .node (4814, [2, 29, 83]) routeSubtree196 routeSubtree203

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree205 : BinaryTree (ℕ × List ℕ) :=
  (.node (4957, [4957])
    (.node (4949, [7, 7, 101])
      (.node (4945, [5, 23, 43])
        (.node (4943, [4943]) (.node (4942, [2, 7, 353]) .nil .nil)
          (.node (4944, [2, 2, 2, 2, 3, 103]) .nil .nil))
        (.node (4947, [3, 17, 97]) (.node (4946, [2, 2473]) .nil .nil)
          (.node (4948, [2, 2, 1237]) .nil .nil)))
      (.node (4953, [3, 13, 127])
        (.node (4951, [4951]) (.node (4950, [2, 3, 3, 5, 5, 11]) .nil .nil)
          (.node (4952, [2, 2, 2, 619]) .nil .nil))
        (.node (4955, [5, 991]) (.node (4954, [2, 2477]) .nil .nil)
          (.node (4956, [2, 2, 3, 7, 59]) .nil .nil))))
    (.node (4965, [3, 5, 331])
      (.node (4961, [11, 11, 41])
        (.node (4959, [3, 3, 19, 29]) (.node (4958, [2, 37, 67]) .nil .nil)
          (.node (4960, [2, 2, 2, 2, 2, 5, 31]) .nil .nil))
        (.node (4963, [7, 709]) (.node (4962, [2, 3, 827]) .nil .nil)
          (.node (4964, [2, 2, 17, 73]) .nil .nil)))
      (.node (4969, [4969])
        (.node (4967, [4967]) (.node (4966, [2, 13, 191]) .nil .nil)
          (.node (4968, [2, 2, 2, 3, 3, 3, 23]) .nil .nil))
        (.node (4971, [3, 1657]) (.node (4970, [2, 5, 7, 71]) .nil .nil)
          (.node (4972, [2, 2, 11, 113]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree206 : BinaryTree (ℕ × List ℕ) :=
  (.node (4989, [3, 1663])
    (.node (4981, [17, 293])
      (.node (4977, [3, 3, 7, 79])
        (.node (4975, [5, 5, 199]) (.node (4974, [2, 3, 829]) .nil .nil)
          (.node (4976, [2, 2, 2, 2, 311]) .nil .nil))
        (.node (4979, [13, 383]) (.node (4978, [2, 19, 131]) .nil .nil)
          (.node (4980, [2, 2, 3, 5, 83]) .nil .nil)))
      (.node (4985, [5, 997])
        (.node (4983, [3, 11, 151]) (.node (4982, [2, 47, 53]) .nil .nil)
          (.node (4984, [2, 2, 2, 7, 89]) .nil .nil))
        (.node (4987, [4987]) (.node (4986, [2, 3, 3, 277]) .nil .nil)
          (.node (4988, [2, 2, 29, 43]) .nil .nil))))
    (.node (4997, [19, 263])
      (.node (4993, [4993])
        (.node (4991, [7, 23, 31]) (.node (4990, [2, 5, 499]) .nil .nil)
          (.node (4992, [2, 2, 2, 2, 2, 2, 2, 3, 13]) .nil .nil))
        (.node (4995, [3, 3, 3, 5, 37]) (.node (4994, [2, 11, 227]) .nil .nil)
          (.node (4996, [2, 2, 1249]) .nil .nil)))
      (.node (5001, [3, 1667])
        (.node (4999, [4999]) (.node (4998, [2, 3, 7, 7, 17]) .nil .nil)
          (.node (5000, [2, 2, 2, 5, 5, 5, 5]) .nil .nil))
        (.node (5003, [5003]) (.node (5002, [2, 41, 61]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree207 : BinaryTree (ℕ × List ℕ) :=
  .node (4973, [4973]) routeSubtree205 routeSubtree206

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree208 : BinaryTree (ℕ × List ℕ) :=
  (.node (5020, [2, 2, 5, 251])
    (.node (5012, [2, 2, 7, 179])
      (.node (5008, [2, 2, 2, 2, 313])
        (.node (5006, [2, 2503]) (.node (5005, [5, 7, 11, 13]) .nil .nil)
          (.node (5007, [3, 1669]) .nil .nil))
        (.node (5010, [2, 3, 5, 167]) (.node (5009, [5009]) .nil .nil)
          (.node (5011, [5011]) .nil .nil)))
      (.node (5016, [2, 2, 2, 3, 11, 19])
        (.node (5014, [2, 23, 109]) (.node (5013, [3, 3, 557]) .nil .nil)
          (.node (5015, [5, 17, 59]) .nil .nil))
        (.node (5018, [2, 13, 193]) (.node (5017, [29, 173]) .nil .nil)
          (.node (5019, [3, 7, 239]) .nil .nil))))
    (.node (5028, [2, 2, 3, 419])
      (.node (5024, [2, 2, 2, 2, 2, 157])
        (.node (5022, [2, 3, 3, 3, 3, 31]) (.node (5021, [5021]) .nil .nil)
          (.node (5023, [5023]) .nil .nil))
        (.node (5026, [2, 7, 359]) (.node (5025, [3, 5, 5, 67]) .nil .nil)
          (.node (5027, [11, 457]) .nil .nil)))
      (.node (5032, [2, 2, 2, 17, 37])
        (.node (5030, [2, 5, 503]) (.node (5029, [47, 107]) .nil .nil)
          (.node (5031, [3, 3, 13, 43]) .nil .nil))
        (.node (5034, [2, 3, 839]) (.node (5033, [7, 719]) .nil .nil)
          (.node (5035, [5, 19, 53]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree209 : BinaryTree (ℕ × List ℕ) :=
  (.node (5052, [2, 2, 3, 421])
    (.node (5044, [2, 2, 13, 97])
      (.node (5040, [2, 2, 2, 2, 3, 3, 5, 7])
        (.node (5038, [2, 11, 229]) (.node (5037, [3, 23, 73]) .nil .nil)
          (.node (5039, [5039]) .nil .nil))
        (.node (5042, [2, 2521]) (.node (5041, [71, 71]) .nil .nil)
          (.node (5043, [3, 41, 41]) .nil .nil)))
      (.node (5048, [2, 2, 2, 631])
        (.node (5046, [2, 3, 29, 29]) (.node (5045, [5, 1009]) .nil .nil)
          (.node (5047, [7, 7, 103]) .nil .nil))
        (.node (5050, [2, 5, 5, 101]) (.node (5049, [3, 3, 3, 11, 17]) .nil .nil)
          (.node (5051, [5051]) .nil .nil))))
    (.node (5060, [2, 2, 5, 11, 23])
      (.node (5056, [2, 2, 2, 2, 2, 2, 79])
        (.node (5054, [2, 7, 19, 19]) (.node (5053, [31, 163]) .nil .nil)
          (.node (5055, [3, 5, 337]) .nil .nil))
        (.node (5058, [2, 3, 3, 281]) (.node (5057, [13, 389]) .nil .nil)
          (.node (5059, [5059]) .nil .nil)))
      (.node (5064, [2, 2, 2, 3, 211])
        (.node (5062, [2, 2531]) (.node (5061, [3, 7, 241]) .nil .nil)
          (.node (5063, [61, 83]) .nil .nil))
        (.node (5066, [2, 17, 149]) (.node (5065, [5, 1013]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree210 : BinaryTree (ℕ × List ℕ) :=
  .node (5036, [2, 2, 1259]) routeSubtree208 routeSubtree209

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree211 : BinaryTree (ℕ × List ℕ) :=
  .node (5004, [2, 2, 3, 3, 139]) routeSubtree207 routeSubtree210

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree212 : BinaryTree (ℕ × List ℕ) :=
  (.node (5083, [13, 17, 23])
    (.node (5075, [5, 5, 7, 29])
      (.node (5071, [11, 461])
        (.node (5069, [37, 137]) (.node (5068, [2, 2, 7, 181]) .nil .nil)
          (.node (5070, [2, 3, 5, 13, 13]) .nil .nil))
        (.node (5073, [3, 19, 89]) (.node (5072, [2, 2, 2, 2, 317]) .nil .nil)
          (.node (5074, [2, 43, 59]) .nil .nil)))
      (.node (5079, [3, 1693])
        (.node (5077, [5077]) (.node (5076, [2, 2, 3, 3, 3, 47]) .nil .nil)
          (.node (5078, [2, 2539]) .nil .nil))
        (.node (5081, [5081]) (.node (5080, [2, 2, 2, 5, 127]) .nil .nil)
          (.node (5082, [2, 3, 7, 11, 11]) .nil .nil))))
    (.node (5091, [3, 1697])
      (.node (5087, [5087])
        (.node (5085, [3, 3, 5, 113]) (.node (5084, [2, 2, 31, 41]) .nil .nil)
          (.node (5086, [2, 2543]) .nil .nil))
        (.node (5089, [7, 727]) (.node (5088, [2, 2, 2, 2, 2, 3, 53]) .nil .nil)
          (.node (5090, [2, 5, 509]) .nil .nil)))
      (.node (5095, [5, 1019])
        (.node (5093, [11, 463]) (.node (5092, [2, 2, 19, 67]) .nil .nil)
          (.node (5094, [2, 3, 3, 283]) .nil .nil))
        (.node (5097, [3, 1699]) (.node (5096, [2, 2, 2, 7, 7, 13]) .nil .nil)
          (.node (5098, [2, 2549]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree213 : BinaryTree (ℕ × List ℕ) :=
  (.node (5115, [3, 5, 11, 31])
    (.node (5107, [5107])
      (.node (5103, [3, 3, 3, 3, 3, 3, 7])
        (.node (5101, [5101]) (.node (5100, [2, 2, 3, 5, 5, 17]) .nil .nil)
          (.node (5102, [2, 2551]) .nil .nil))
        (.node (5105, [5, 1021]) (.node (5104, [2, 2, 2, 2, 11, 29]) .nil .nil)
          (.node (5106, [2, 3, 23, 37]) .nil .nil)))
      (.node (5111, [19, 269])
        (.node (5109, [3, 13, 131]) (.node (5108, [2, 2, 1277]) .nil .nil)
          (.node (5110, [2, 5, 7, 73]) .nil .nil))
        (.node (5113, [5113]) (.node (5112, [2, 2, 2, 3, 3, 71]) .nil .nil)
          (.node (5114, [2, 2557]) .nil .nil))))
    (.node (5123, [47, 109])
      (.node (5119, [5119])
        (.node (5117, [7, 17, 43]) (.node (5116, [2, 2, 1279]) .nil .nil)
          (.node (5118, [2, 3, 853]) .nil .nil))
        (.node (5121, [3, 3, 569]) (.node (5120, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5]) .nil .nil)
          (.node (5122, [2, 13, 197]) .nil .nil)))
      (.node (5127, [3, 1709])
        (.node (5125, [5, 5, 5, 41]) (.node (5124, [2, 2, 3, 7, 61]) .nil .nil)
          (.node (5126, [2, 11, 233]) .nil .nil))
        (.node (5129, [23, 223]) (.node (5128, [2, 2, 2, 641]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree214 : BinaryTree (ℕ × List ℕ) :=
  .node (5099, [5099]) routeSubtree212 routeSubtree213

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree215 : BinaryTree (ℕ × List ℕ) :=
  (.node (5146, [2, 31, 83])
    (.node (5138, [2, 7, 367])
      (.node (5134, [2, 17, 151])
        (.node (5132, [2, 2, 1283]) (.node (5131, [7, 733]) .nil .nil)
          (.node (5133, [3, 29, 59]) .nil .nil))
        (.node (5136, [2, 2, 2, 2, 3, 107]) (.node (5135, [5, 13, 79]) .nil .nil)
          (.node (5137, [11, 467]) .nil .nil)))
      (.node (5142, [2, 3, 857])
        (.node (5140, [2, 2, 5, 257]) (.node (5139, [3, 3, 571]) .nil .nil)
          (.node (5141, [53, 97]) .nil .nil))
        (.node (5144, [2, 2, 2, 643]) (.node (5143, [37, 139]) .nil .nil)
          (.node (5145, [3, 5, 7, 7, 7]) .nil .nil))))
    (.node (5154, [2, 3, 859])
      (.node (5150, [2, 5, 5, 103])
        (.node (5148, [2, 2, 3, 3, 11, 13]) (.node (5147, [5147]) .nil .nil)
          (.node (5149, [19, 271]) .nil .nil))
        (.node (5152, [2, 2, 2, 2, 2, 7, 23]) (.node (5151, [3, 17, 101]) .nil .nil)
          (.node (5153, [5153]) .nil .nil)))
      (.node (5158, [2, 2579])
        (.node (5156, [2, 2, 1289]) (.node (5155, [5, 1031]) .nil .nil)
          (.node (5157, [3, 3, 3, 191]) .nil .nil))
        (.node (5160, [2, 2, 2, 3, 5, 43]) (.node (5159, [7, 11, 67]) .nil .nil)
          (.node (5161, [13, 397]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree216 : BinaryTree (ℕ × List ℕ) :=
  (.node (5178, [2, 3, 863])
    (.node (5170, [2, 5, 11, 47])
      (.node (5166, [2, 3, 3, 7, 41])
        (.node (5164, [2, 2, 1291]) (.node (5163, [3, 1721]) .nil .nil)
          (.node (5165, [5, 1033]) .nil .nil))
        (.node (5168, [2, 2, 2, 2, 17, 19]) (.node (5167, [5167]) .nil .nil)
          (.node (5169, [3, 1723]) .nil .nil)))
      (.node (5174, [2, 13, 199])
        (.node (5172, [2, 2, 3, 431]) (.node (5171, [5171]) .nil .nil)
          (.node (5173, [7, 739]) .nil .nil))
        (.node (5176, [2, 2, 2, 647]) (.node (5175, [3, 3, 5, 5, 23]) .nil .nil)
          (.node (5177, [31, 167]) .nil .nil))))
    (.node (5186, [2, 2593])
      (.node (5182, [2, 2591])
        (.node (5180, [2, 2, 5, 7, 37]) (.node (5179, [5179]) .nil .nil)
          (.node (5181, [3, 11, 157]) .nil .nil))
        (.node (5184, [2, 2, 2, 2, 2, 2, 3, 3, 3, 3]) (.node (5183, [71, 73]) .nil .nil)
          (.node (5185, [5, 17, 61]) .nil .nil)))
      (.node (5190, [2, 3, 5, 173])
        (.node (5188, [2, 2, 1297]) (.node (5187, [3, 7, 13, 19]) .nil .nil)
          (.node (5189, [5189]) .nil .nil))
        (.node (5192, [2, 2, 2, 11, 59]) (.node (5191, [29, 179]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree217 : BinaryTree (ℕ × List ℕ) :=
  .node (5162, [2, 29, 89]) routeSubtree215 routeSubtree216

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree218 : BinaryTree (ℕ × List ℕ) :=
  .node (5130, [2, 3, 3, 3, 5, 19]) routeSubtree214 routeSubtree217

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree219 : BinaryTree (ℕ × List ℕ) :=
  .node (5067, [3, 3, 563]) routeSubtree211 routeSubtree218

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree220 : BinaryTree (ℕ × List ℕ) :=
  .node (4941, [3, 3, 3, 3, 61]) routeSubtree204 routeSubtree219

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree221 : BinaryTree (ℕ × List ℕ) :=
  (.node (5209, [5209])
    (.node (5201, [7, 743])
      (.node (5197, [5197])
        (.node (5195, [5, 1039]) (.node (5194, [2, 7, 7, 53]) .nil .nil)
          (.node (5196, [2, 2, 3, 433]) .nil .nil))
        (.node (5199, [3, 1733]) (.node (5198, [2, 23, 113]) .nil .nil)
          (.node (5200, [2, 2, 2, 2, 5, 5, 13]) .nil .nil)))
      (.node (5205, [3, 5, 347])
        (.node (5203, [11, 11, 43]) (.node (5202, [2, 3, 3, 17, 17]) .nil .nil)
          (.node (5204, [2, 2, 1301]) .nil .nil))
        (.node (5207, [41, 127]) (.node (5206, [2, 19, 137]) .nil .nil)
          (.node (5208, [2, 2, 2, 3, 7, 31]) .nil .nil))))
    (.node (5217, [3, 37, 47])
      (.node (5213, [13, 401])
        (.node (5211, [3, 3, 3, 193]) (.node (5210, [2, 5, 521]) .nil .nil)
          (.node (5212, [2, 2, 1303]) .nil .nil))
        (.node (5215, [5, 7, 149]) (.node (5214, [2, 3, 11, 79]) .nil .nil)
          (.node (5216, [2, 2, 2, 2, 2, 163]) .nil .nil)))
      (.node (5221, [23, 227])
        (.node (5219, [17, 307]) (.node (5218, [2, 2609]) .nil .nil)
          (.node (5220, [2, 2, 3, 3, 5, 29]) .nil .nil))
        (.node (5223, [3, 1741]) (.node (5222, [2, 7, 373]) .nil .nil)
          (.node (5224, [2, 2, 2, 653]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree222 : BinaryTree (ℕ × List ℕ) :=
  (.node (5241, [3, 1747])
    (.node (5233, [5233])
      (.node (5229, [3, 3, 7, 83])
        (.node (5227, [5227]) (.node (5226, [2, 3, 13, 67]) .nil .nil)
          (.node (5228, [2, 2, 1307]) .nil .nil))
        (.node (5231, [5231]) (.node (5230, [2, 5, 523]) .nil .nil)
          (.node (5232, [2, 2, 2, 2, 3, 109]) .nil .nil)))
      (.node (5237, [5237])
        (.node (5235, [3, 5, 349]) (.node (5234, [2, 2617]) .nil .nil)
          (.node (5236, [2, 2, 7, 11, 17]) .nil .nil))
        (.node (5239, [13, 13, 31]) (.node (5238, [2, 3, 3, 3, 97]) .nil .nil)
          (.node (5240, [2, 2, 2, 5, 131]) .nil .nil))))
    (.node (5249, [29, 181])
      (.node (5245, [5, 1049])
        (.node (5243, [7, 7, 107]) (.node (5242, [2, 2621]) .nil .nil)
          (.node (5244, [2, 2, 3, 19, 23]) .nil .nil))
        (.node (5247, [3, 3, 11, 53]) (.node (5246, [2, 43, 61]) .nil .nil)
          (.node (5248, [2, 2, 2, 2, 2, 2, 2, 41]) .nil .nil)))
      (.node (5253, [3, 17, 103])
        (.node (5251, [59, 89]) (.node (5250, [2, 3, 5, 5, 5, 7]) .nil .nil)
          (.node (5252, [2, 2, 13, 101]) .nil .nil))
        (.node (5255, [5, 1051]) (.node (5254, [2, 37, 71]) .nil .nil)
          (.node (5256, [2, 2, 2, 3, 3, 73]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree223 : BinaryTree (ℕ × List ℕ) :=
  .node (5225, [5, 5, 11, 19]) routeSubtree221 routeSubtree222

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree224 : BinaryTree (ℕ × List ℕ) :=
  (.node (5273, [5273])
    (.node (5265, [3, 3, 3, 3, 5, 13])
      (.node (5261, [5261])
        (.node (5259, [3, 1753]) (.node (5258, [2, 11, 239]) .nil .nil)
          (.node (5260, [2, 2, 5, 263]) .nil .nil))
        (.node (5263, [19, 277]) (.node (5262, [2, 3, 877]) .nil .nil)
          (.node (5264, [2, 2, 2, 2, 7, 47]) .nil .nil)))
      (.node (5269, [11, 479])
        (.node (5267, [23, 229]) (.node (5266, [2, 2633]) .nil .nil)
          (.node (5268, [2, 2, 3, 439]) .nil .nil))
        (.node (5271, [3, 7, 251]) (.node (5270, [2, 5, 17, 31]) .nil .nil)
          (.node (5272, [2, 2, 2, 659]) .nil .nil))))
    (.node (5281, [5281])
      (.node (5277, [3, 1759])
        (.node (5275, [5, 5, 211]) (.node (5274, [2, 3, 3, 293]) .nil .nil)
          (.node (5276, [2, 2, 1319]) .nil .nil))
        (.node (5279, [5279]) (.node (5278, [2, 7, 13, 29]) .nil .nil)
          (.node (5280, [2, 2, 2, 2, 2, 3, 5, 11]) .nil .nil)))
      (.node (5285, [5, 7, 151])
        (.node (5283, [3, 3, 587]) (.node (5282, [2, 19, 139]) .nil .nil)
          (.node (5284, [2, 2, 1321]) .nil .nil))
        (.node (5287, [17, 311]) (.node (5286, [2, 3, 881]) .nil .nil)
          (.node (5288, [2, 2, 2, 661]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree225 : BinaryTree (ℕ × List ℕ) :=
  (.node (5305, [5, 1061])
    (.node (5297, [5297])
      (.node (5293, [67, 79])
        (.node (5291, [11, 13, 37]) (.node (5290, [2, 5, 23, 23]) .nil .nil)
          (.node (5292, [2, 2, 3, 3, 3, 7, 7]) .nil .nil))
        (.node (5295, [3, 5, 353]) (.node (5294, [2, 2647]) .nil .nil)
          (.node (5296, [2, 2, 2, 2, 331]) .nil .nil)))
      (.node (5301, [3, 3, 19, 31])
        (.node (5299, [7, 757]) (.node (5298, [2, 3, 883]) .nil .nil)
          (.node (5300, [2, 2, 5, 5, 53]) .nil .nil))
        (.node (5303, [5303]) (.node (5302, [2, 11, 241]) .nil .nil)
          (.node (5304, [2, 2, 2, 3, 13, 17]) .nil .nil))))
    (.node (5313, [3, 7, 11, 23])
      (.node (5309, [5309])
        (.node (5307, [3, 29, 61]) (.node (5306, [2, 7, 379]) .nil .nil)
          (.node (5308, [2, 2, 1327]) .nil .nil))
        (.node (5311, [47, 113]) (.node (5310, [2, 3, 3, 5, 59]) .nil .nil)
          (.node (5312, [2, 2, 2, 2, 2, 2, 83]) .nil .nil)))
      (.node (5317, [13, 409])
        (.node (5315, [5, 1063]) (.node (5314, [2, 2657]) .nil .nil)
          (.node (5316, [2, 2, 3, 443]) .nil .nil))
        (.node (5319, [3, 3, 3, 197]) (.node (5318, [2, 2659]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree226 : BinaryTree (ℕ × List ℕ) :=
  .node (5289, [3, 41, 43]) routeSubtree224 routeSubtree225

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree227 : BinaryTree (ℕ × List ℕ) :=
  .node (5257, [7, 751]) routeSubtree223 routeSubtree226

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree228 : BinaryTree (ℕ × List ℕ) :=
  (.node (5336, [2, 2, 2, 23, 29])
    (.node (5328, [2, 2, 2, 2, 3, 3, 37])
      (.node (5324, [2, 2, 11, 11, 11])
        (.node (5322, [2, 3, 887]) (.node (5321, [17, 313]) .nil .nil)
          (.node (5323, [5323]) .nil .nil))
        (.node (5326, [2, 2663]) (.node (5325, [3, 5, 5, 71]) .nil .nil)
          (.node (5327, [7, 761]) .nil .nil)))
      (.node (5332, [2, 2, 31, 43])
        (.node (5330, [2, 5, 13, 41]) (.node (5329, [73, 73]) .nil .nil)
          (.node (5331, [3, 1777]) .nil .nil))
        (.node (5334, [2, 3, 7, 127]) (.node (5333, [5333]) .nil .nil)
          (.node (5335, [5, 11, 97]) .nil .nil))))
    (.node (5344, [2, 2, 2, 2, 2, 167])
      (.node (5340, [2, 2, 3, 5, 89])
        (.node (5338, [2, 17, 157]) (.node (5337, [3, 3, 593]) .nil .nil)
          (.node (5339, [19, 281]) .nil .nil))
        (.node (5342, [2, 2671]) (.node (5341, [7, 7, 109]) .nil .nil)
          (.node (5343, [3, 13, 137]) .nil .nil)))
      (.node (5348, [2, 2, 7, 191])
        (.node (5346, [2, 3, 3, 3, 3, 3, 11]) (.node (5345, [5, 1069]) .nil .nil)
          (.node (5347, [5347]) .nil .nil))
        (.node (5350, [2, 5, 5, 107]) (.node (5349, [3, 1783]) .nil .nil)
          (.node (5351, [5351]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree229 : BinaryTree (ℕ × List ℕ) :=
  (.node (5368, [2, 2, 2, 11, 61])
    (.node (5360, [2, 2, 2, 2, 5, 67])
      (.node (5356, [2, 2, 13, 103])
        (.node (5354, [2, 2677]) (.node (5353, [53, 101]) .nil .nil)
          (.node (5355, [3, 3, 5, 7, 17]) .nil .nil))
        (.node (5358, [2, 3, 19, 47]) (.node (5357, [11, 487]) .nil .nil)
          (.node (5359, [23, 233]) .nil .nil)))
      (.node (5364, [2, 2, 3, 3, 149])
        (.node (5362, [2, 7, 383]) (.node (5361, [3, 1787]) .nil .nil)
          (.node (5363, [31, 173]) .nil .nil))
        (.node (5366, [2, 2683]) (.node (5365, [5, 29, 37]) .nil .nil)
          (.node (5367, [3, 1789]) .nil .nil))))
    (.node (5376, [2, 2, 2, 2, 2, 2, 2, 2, 3, 7])
      (.node (5372, [2, 2, 17, 79])
        (.node (5370, [2, 3, 5, 179]) (.node (5369, [7, 13, 59]) .nil .nil)
          (.node (5371, [41, 131]) .nil .nil))
        (.node (5374, [2, 2687]) (.node (5373, [3, 3, 3, 199]) .nil .nil)
          (.node (5375, [5, 5, 5, 43]) .nil .nil)))
      (.node (5380, [2, 2, 5, 269])
        (.node (5378, [2, 2689]) (.node (5377, [19, 283]) .nil .nil)
          (.node (5379, [3, 11, 163]) .nil .nil))
        (.node (5382, [2, 3, 3, 13, 23]) (.node (5381, [5381]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree230 : BinaryTree (ℕ × List ℕ) :=
  .node (5352, [2, 2, 2, 3, 223]) routeSubtree228 routeSubtree229

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree231 : BinaryTree (ℕ × List ℕ) :=
  (.node (5399, [5399])
    (.node (5391, [3, 3, 599])
      (.node (5387, [5387])
        (.node (5385, [3, 5, 359]) (.node (5384, [2, 2, 2, 673]) .nil .nil)
          (.node (5386, [2, 2693]) .nil .nil))
        (.node (5389, [17, 317]) (.node (5388, [2, 2, 3, 449]) .nil .nil)
          (.node (5390, [2, 5, 7, 7, 11]) .nil .nil)))
      (.node (5395, [5, 13, 83])
        (.node (5393, [5393]) (.node (5392, [2, 2, 2, 2, 337]) .nil .nil)
          (.node (5394, [2, 3, 29, 31]) .nil .nil))
        (.node (5397, [3, 7, 257]) (.node (5396, [2, 2, 19, 71]) .nil .nil)
          (.node (5398, [2, 2699]) .nil .nil))))
    (.node (5407, [5407])
      (.node (5403, [3, 1801])
        (.node (5401, [11, 491]) (.node (5400, [2, 2, 2, 3, 3, 3, 5, 5]) .nil .nil)
          (.node (5402, [2, 37, 73]) .nil .nil))
        (.node (5405, [5, 23, 47]) (.node (5404, [2, 2, 7, 193]) .nil .nil)
          (.node (5406, [2, 3, 17, 53]) .nil .nil)))
      (.node (5411, [7, 773])
        (.node (5409, [3, 3, 601]) (.node (5408, [2, 2, 2, 2, 2, 13, 13]) .nil .nil)
          (.node (5410, [2, 5, 541]) .nil .nil))
        (.node (5413, [5413]) (.node (5412, [2, 2, 3, 11, 41]) .nil .nil)
          (.node (5414, [2, 2707]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree232 : BinaryTree (ℕ × List ℕ) :=
  (.node (5431, [5431])
    (.node (5423, [11, 17, 29])
      (.node (5419, [5419])
        (.node (5417, [5417]) (.node (5416, [2, 2, 2, 677]) .nil .nil)
          (.node (5418, [2, 3, 3, 7, 43]) .nil .nil))
        (.node (5421, [3, 13, 139]) (.node (5420, [2, 2, 5, 271]) .nil .nil)
          (.node (5422, [2, 2711]) .nil .nil)))
      (.node (5427, [3, 3, 3, 3, 67])
        (.node (5425, [5, 5, 7, 31]) (.node (5424, [2, 2, 2, 2, 3, 113]) .nil .nil)
          (.node (5426, [2, 2713]) .nil .nil))
        (.node (5429, [61, 89]) (.node (5428, [2, 2, 23, 59]) .nil .nil)
          (.node (5430, [2, 3, 5, 181]) .nil .nil))))
    (.node (5439, [3, 7, 7, 37])
      (.node (5435, [5, 1087])
        (.node (5433, [3, 1811]) (.node (5432, [2, 2, 2, 7, 97]) .nil .nil)
          (.node (5434, [2, 11, 13, 19]) .nil .nil))
        (.node (5437, [5437]) (.node (5436, [2, 2, 3, 3, 151]) .nil .nil)
          (.node (5438, [2, 2719]) .nil .nil)))
      (.node (5443, [5443])
        (.node (5441, [5441]) (.node (5440, [2, 2, 2, 2, 2, 2, 5, 17]) .nil .nil)
          (.node (5442, [2, 3, 907]) .nil .nil))
        (.node (5445, [3, 3, 5, 11, 11]) (.node (5444, [2, 2, 1361]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree233 : BinaryTree (ℕ × List ℕ) :=
  .node (5415, [3, 5, 19, 19]) routeSubtree231 routeSubtree232

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree234 : BinaryTree (ℕ × List ℕ) :=
  .node (5383, [7, 769]) routeSubtree230 routeSubtree233

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree235 : BinaryTree (ℕ × List ℕ) :=
  .node (5320, [2, 2, 2, 5, 7, 19]) routeSubtree227 routeSubtree234

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree236 : BinaryTree (ℕ × List ℕ) :=
  (.node (5463, [3, 3, 607])
    (.node (5454, [2, 3, 3, 3, 101])
      (.node (5450, [2, 5, 5, 109])
        (.node (5448, [2, 2, 2, 3, 227]) (.node (5447, [13, 419]) .nil .nil)
          (.node (5449, [5449]) .nil .nil))
        (.node (5452, [2, 2, 29, 47]) (.node (5451, [3, 23, 79]) .nil .nil)
          (.node (5453, [7, 19, 41]) .nil .nil)))
      (.node (5458, [2, 2729])
        (.node (5456, [2, 2, 2, 2, 11, 31]) (.node (5455, [5, 1091]) .nil .nil)
          (.node (5457, [3, 17, 107]) .nil .nil))
        (.node (5461, [43, 127]) (.node (5459, [53, 103]) .nil .nil)
          (.node (5462, [2, 2731]) .nil .nil))))
    (.node (5471, [5471])
      (.node (5467, [7, 11, 71])
        (.node (5465, [5, 1093]) (.node (5464, [2, 2, 2, 683]) .nil .nil)
          (.node (5466, [2, 3, 911]) .nil .nil))
        (.node (5469, [3, 1823]) (.node (5468, [2, 2, 1367]) .nil .nil)
          (.node (5470, [2, 5, 547]) .nil .nil)))
      (.node (5475, [3, 5, 5, 73])
        (.node (5473, [13, 421]) (.node (5472, [2, 2, 2, 2, 2, 3, 3, 19]) .nil .nil)
          (.node (5474, [2, 7, 17, 23]) .nil .nil))
        (.node (5477, [5477]) (.node (5476, [2, 2, 37, 37]) .nil .nil)
          (.node (5478, [2, 3, 11, 83]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree237 : BinaryTree (ℕ × List ℕ) :=
  (.node (5495, [5, 7, 157])
    (.node (5487, [3, 31, 59])
      (.node (5483, [5483])
        (.node (5481, [3, 3, 3, 7, 29]) (.node (5480, [2, 2, 2, 5, 137]) .nil .nil)
          (.node (5482, [2, 2741]) .nil .nil))
        (.node (5485, [5, 1097]) (.node (5484, [2, 2, 3, 457]) .nil .nil)
          (.node (5486, [2, 13, 211]) .nil .nil)))
      (.node (5491, [17, 17, 19])
        (.node (5489, [11, 499]) (.node (5488, [2, 2, 2, 2, 7, 7, 7]) .nil .nil)
          (.node (5490, [2, 3, 3, 5, 61]) .nil .nil))
        (.node (5493, [3, 1831]) (.node (5492, [2, 2, 1373]) .nil .nil)
          (.node (5494, [2, 41, 67]) .nil .nil))))
    (.node (5503, [5503])
      (.node (5499, [3, 3, 13, 47])
        (.node (5497, [23, 239]) (.node (5496, [2, 2, 2, 3, 229]) .nil .nil)
          (.node (5498, [2, 2749]) .nil .nil))
        (.node (5501, [5501]) (.node (5500, [2, 2, 5, 5, 5, 11]) .nil .nil)
          (.node (5502, [2, 3, 7, 131]) .nil .nil)))
      (.node (5507, [5507])
        (.node (5505, [3, 5, 367]) (.node (5504, [2, 2, 2, 2, 2, 2, 2, 43]) .nil .nil)
          (.node (5506, [2, 2753]) .nil .nil))
        (.node (5509, [7, 787]) (.node (5508, [2, 2, 3, 3, 3, 3, 17]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree238 : BinaryTree (ℕ × List ℕ) :=
  .node (5479, [5479]) routeSubtree236 routeSubtree237

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree239 : BinaryTree (ℕ × List ℕ) :=
  (.node (5526, [2, 3, 3, 307])
    (.node (5518, [2, 31, 89])
      (.node (5514, [2, 3, 919])
        (.node (5512, [2, 2, 2, 13, 53]) (.node (5511, [3, 11, 167]) .nil .nil)
          (.node (5513, [37, 149]) .nil .nil))
        (.node (5516, [2, 2, 7, 197]) (.node (5515, [5, 1103]) .nil .nil)
          (.node (5517, [3, 3, 613]) .nil .nil)))
      (.node (5522, [2, 11, 251])
        (.node (5520, [2, 2, 2, 2, 3, 5, 23]) (.node (5519, [5519]) .nil .nil)
          (.node (5521, [5521]) .nil .nil))
        (.node (5524, [2, 2, 1381]) (.node (5523, [3, 7, 263]) .nil .nil)
          (.node (5525, [5, 5, 13, 17]) .nil .nil))))
    (.node (5534, [2, 2767])
      (.node (5530, [2, 5, 7, 79])
        (.node (5528, [2, 2, 2, 691]) (.node (5527, [5527]) .nil .nil)
          (.node (5529, [3, 19, 97]) .nil .nil))
        (.node (5532, [2, 2, 3, 461]) (.node (5531, [5531]) .nil .nil)
          (.node (5533, [11, 503]) .nil .nil)))
      (.node (5538, [2, 3, 13, 71])
        (.node (5536, [2, 2, 2, 2, 2, 173]) (.node (5535, [3, 3, 3, 5, 41]) .nil .nil)
          (.node (5537, [7, 7, 113]) .nil .nil))
        (.node (5540, [2, 2, 5, 277]) (.node (5539, [29, 191]) .nil .nil)
          (.node (5541, [3, 1847]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree240 : BinaryTree (ℕ × List ℕ) :=
  (.node (5558, [2, 7, 397])
    (.node (5550, [2, 3, 5, 5, 37])
      (.node (5546, [2, 47, 59])
        (.node (5544, [2, 2, 2, 3, 3, 7, 11]) (.node (5543, [23, 241]) .nil .nil)
          (.node (5545, [5, 1109]) .nil .nil))
        (.node (5548, [2, 2, 19, 73]) (.node (5547, [3, 43, 43]) .nil .nil)
          (.node (5549, [31, 179]) .nil .nil)))
      (.node (5554, [2, 2777])
        (.node (5552, [2, 2, 2, 2, 347]) (.node (5551, [7, 13, 61]) .nil .nil)
          (.node (5553, [3, 3, 617]) .nil .nil))
        (.node (5556, [2, 2, 3, 463]) (.node (5555, [5, 11, 101]) .nil .nil)
          (.node (5557, [5557]) .nil .nil))))
    (.node (5566, [2, 11, 11, 23])
      (.node (5562, [2, 3, 3, 3, 103])
        (.node (5560, [2, 2, 2, 5, 139]) (.node (5559, [3, 17, 109]) .nil .nil)
          (.node (5561, [67, 83]) .nil .nil))
        (.node (5564, [2, 2, 13, 107]) (.node (5563, [5563]) .nil .nil)
          (.node (5565, [3, 5, 7, 53]) .nil .nil)))
      (.node (5570, [2, 5, 557])
        (.node (5568, [2, 2, 2, 2, 2, 2, 3, 29]) (.node (5567, [19, 293]) .nil .nil)
          (.node (5569, [5569]) .nil .nil))
        (.node (5572, [2, 2, 7, 199]) (.node (5571, [3, 3, 619]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree241 : BinaryTree (ℕ × List ℕ) :=
  .node (5542, [2, 17, 163]) routeSubtree239 routeSubtree240

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree242 : BinaryTree (ℕ × List ℕ) :=
  .node (5510, [2, 5, 19, 29]) routeSubtree238 routeSubtree241

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree243 : BinaryTree (ℕ × List ℕ) :=
  (.node (5589, [3, 3, 3, 3, 3, 23])
    (.node (5581, [5581])
      (.node (5577, [3, 11, 13, 13])
        (.node (5575, [5, 5, 223]) (.node (5574, [2, 3, 929]) .nil .nil)
          (.node (5576, [2, 2, 2, 17, 41]) .nil .nil))
        (.node (5579, [7, 797]) (.node (5578, [2, 2789]) .nil .nil)
          (.node (5580, [2, 2, 3, 3, 5, 31]) .nil .nil)))
      (.node (5585, [5, 1117])
        (.node (5583, [3, 1861]) (.node (5582, [2, 2791]) .nil .nil)
          (.node (5584, [2, 2, 2, 2, 349]) .nil .nil))
        (.node (5587, [37, 151]) (.node (5586, [2, 3, 7, 7, 19]) .nil .nil)
          (.node (5588, [2, 2, 11, 127]) .nil .nil))))
    (.node (5597, [29, 193])
      (.node (5593, [7, 17, 47])
        (.node (5591, [5591]) (.node (5590, [2, 5, 13, 43]) .nil .nil)
          (.node (5592, [2, 2, 2, 3, 233]) .nil .nil))
        (.node (5595, [3, 5, 373]) (.node (5594, [2, 2797]) .nil .nil)
          (.node (5596, [2, 2, 1399]) .nil .nil)))
      (.node (5601, [3, 1867])
        (.node (5599, [11, 509]) (.node (5598, [2, 3, 3, 311]) .nil .nil)
          (.node (5600, [2, 2, 2, 2, 2, 5, 5, 7]) .nil .nil))
        (.node (5603, [13, 431]) (.node (5602, [2, 2801]) .nil .nil)
          (.node (5604, [2, 2, 3, 467]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree244 : BinaryTree (ℕ × List ℕ) :=
  (.node (5622, [2, 3, 937])
    (.node (5614, [2, 7, 401])
      (.node (5609, [71, 79])
        (.node (5607, [3, 3, 7, 89]) (.node (5606, [2, 2803]) .nil .nil)
          (.node (5608, [2, 2, 2, 701]) .nil .nil))
        (.node (5612, [2, 2, 23, 61]) (.node (5611, [31, 181]) .nil .nil)
          (.node (5613, [3, 1871]) .nil .nil)))
      (.node (5618, [2, 53, 53])
        (.node (5616, [2, 2, 2, 2, 3, 3, 3, 13]) (.node (5615, [5, 1123]) .nil .nil)
          (.node (5617, [41, 137]) .nil .nil))
        (.node (5620, [2, 2, 5, 281]) (.node (5619, [3, 1873]) .nil .nil)
          (.node (5621, [7, 11, 73]) .nil .nil))))
    (.node (5630, [2, 5, 563])
      (.node (5626, [2, 29, 97])
        (.node (5624, [2, 2, 2, 19, 37]) (.node (5623, [5623]) .nil .nil)
          (.node (5625, [3, 3, 5, 5, 5, 5]) .nil .nil))
        (.node (5628, [2, 2, 3, 7, 67]) (.node (5627, [17, 331]) .nil .nil)
          (.node (5629, [13, 433]) .nil .nil)))
      (.node (5634, [2, 3, 3, 313])
        (.node (5632, [2, 2, 2, 2, 2, 2, 2, 2, 2, 11]) (.node (5631, [3, 1877]) .nil .nil)
          (.node (5633, [43, 131]) .nil .nil))
        (.node (5636, [2, 2, 1409]) (.node (5635, [5, 7, 7, 23]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree245 : BinaryTree (ℕ × List ℕ) :=
  .node (5605, [5, 19, 59]) routeSubtree243 routeSubtree244

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree246 : BinaryTree (ℕ × List ℕ) :=
  (.node (5653, [5653])
    (.node (5645, [5, 1129])
      (.node (5641, [5641])
        (.node (5639, [5639]) (.node (5638, [2, 2819]) .nil .nil)
          (.node (5640, [2, 2, 2, 3, 5, 47]) .nil .nil))
        (.node (5643, [3, 3, 3, 11, 19]) (.node (5642, [2, 7, 13, 31]) .nil .nil)
          (.node (5644, [2, 2, 17, 83]) .nil .nil)))
      (.node (5649, [3, 7, 269])
        (.node (5647, [5647]) (.node (5646, [2, 3, 941]) .nil .nil)
          (.node (5648, [2, 2, 2, 2, 353]) .nil .nil))
        (.node (5651, [5651]) (.node (5650, [2, 5, 5, 113]) .nil .nil)
          (.node (5652, [2, 2, 3, 3, 157]) .nil .nil))))
    (.node (5661, [3, 3, 17, 37])
      (.node (5657, [5657])
        (.node (5655, [3, 5, 13, 29]) (.node (5654, [2, 11, 257]) .nil .nil)
          (.node (5656, [2, 2, 2, 7, 101]) .nil .nil))
        (.node (5659, [5659]) (.node (5658, [2, 3, 23, 41]) .nil .nil)
          (.node (5660, [2, 2, 5, 283]) .nil .nil)))
      (.node (5665, [5, 11, 103])
        (.node (5663, [7, 809]) (.node (5662, [2, 19, 149]) .nil .nil)
          (.node (5664, [2, 2, 2, 2, 2, 3, 59]) .nil .nil))
        (.node (5667, [3, 1889]) (.node (5666, [2, 2833]) .nil .nil)
          (.node (5668, [2, 2, 13, 109]) .nil .nil)))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree247 : BinaryTree (ℕ × List ℕ) :=
  (.node (5685, [3, 5, 379])
    (.node (5677, [7, 811])
      (.node (5673, [3, 31, 61])
        (.node (5671, [53, 107]) (.node (5670, [2, 3, 3, 3, 3, 5, 7]) .nil .nil)
          (.node (5672, [2, 2, 2, 709]) .nil .nil))
        (.node (5675, [5, 5, 227]) (.node (5674, [2, 2837]) .nil .nil)
          (.node (5676, [2, 2, 3, 11, 43]) .nil .nil)))
      (.node (5681, [13, 19, 23])
        (.node (5679, [3, 3, 631]) (.node (5678, [2, 17, 167]) .nil .nil)
          (.node (5680, [2, 2, 2, 2, 5, 71]) .nil .nil))
        (.node (5683, [5683]) (.node (5682, [2, 3, 947]) .nil .nil)
          (.node (5684, [2, 2, 7, 7, 29]) .nil .nil))))
    (.node (5693, [5693])
      (.node (5689, [5689])
        (.node (5687, [11, 11, 47]) (.node (5686, [2, 2843]) .nil .nil)
          (.node (5688, [2, 2, 2, 3, 3, 79]) .nil .nil))
        (.node (5691, [3, 7, 271]) (.node (5690, [2, 5, 569]) .nil .nil)
          (.node (5692, [2, 2, 1423]) .nil .nil)))
      (.node (5697, [3, 3, 3, 211])
        (.node (5695, [5, 17, 67]) (.node (5694, [2, 3, 13, 73]) .nil .nil)
          (.node (5696, [2, 2, 2, 2, 2, 2, 89]) .nil .nil))
        (.node (5699, [41, 139]) (.node (5698, [2, 7, 11, 37]) .nil .nil) .nil))))

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree248 : BinaryTree (ℕ × List ℕ) :=
  .node (5669, [5669]) routeSubtree246 routeSubtree247

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree249 : BinaryTree (ℕ × List ℕ) :=
  .node (5637, [3, 1879]) routeSubtree245 routeSubtree248

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree250 : BinaryTree (ℕ × List ℕ) :=
  .node (5573, [5573]) routeSubtree242 routeSubtree249

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree251 : BinaryTree (ℕ × List ℕ) :=
  .node (5446, [2, 7, 389]) routeSubtree235 routeSubtree250

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree252 : BinaryTree (ℕ × List ℕ) :=
  .node (5193, [3, 3, 577]) routeSubtree220 routeSubtree251

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree253 : BinaryTree (ℕ × List ℕ) :=
  .node (4687, [43, 109]) routeSubtree189 routeSubtree252

/-- A bounded-size subtree of supplied route entries. -/
def routeSubtree254 : BinaryTree (ℕ × List ℕ) :=
  .node (3674, [2, 11, 167]) routeSubtree126 routeSubtree253

/-- Balanced modulus-factor entries for the analytic part below 5700.
Each full factor list includes multiplicities; its checked distinct cardinality
selects a certified interval. Ordering permits efficient lookup. -/
def routes : BinaryTree (ℕ × List ℕ) :=
  routeSubtree254

/-- All supplied factorizations and analytic interval conditions pass kernel checks.
Primality uses the shared catalog and the separate prime-two case. -/
theorem routes_checked :
    NumberTheory.certificateTreeAllCheck (residueFactorRouteCheck Corollary12PrimeCatalog.catalog)
        routes =
      true := by
  decide +kernel

/-- A successful analytic route lookup gives the least-prime estimate under GRH.
Use the certified factor count and the corresponding common interval theorem. -/
theorem leastPrime {q : ℕ} [NeZero q] {e : ℕ × List ℕ}
    (hl : NumberTheory.certificateTreeLookup Prod.fst routes q = some e) (hu : q ≤ 20000)
    (a : (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  exact
    exists_least_prime_in_residue_le_of_factor_route_lookup Corollary12PrimeCatalog.catalog_checked
      routes_checked hl hu a hGRH

end PseudoPrime.LLS.PaperStatements.Corollary12AnalyticRoutes

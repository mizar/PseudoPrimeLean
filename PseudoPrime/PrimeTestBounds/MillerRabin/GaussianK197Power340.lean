/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridgePowers663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerNumerics656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPowerGain663
import all PseudoPrime.Analysis.LogTaylorBounds

/-! # Retained K197 prime powers at radius 340 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private def powers340_0 : List PowerRow656 :=
  [⟨7, 6, 3, 1945910148, 1945910150, 2868173358, 56802583, 343000, 2084981⟩,
    ⟨347, 2, 9, 5849324777, 5849324783, 2842665825, 58270114, 347000, 6077568⟩,
    ⟨349, 2, 9, 5855071919, 5855071925, 2830022113, 59011542, 349000, 5990617⟩,
    ⟨353, 2, 9, 5866468054, 5866468060, 2804950616, 60509753, 353000, 5820122⟩]

private theorem powers340_0_valid :
    powers340_0.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_1 : List PowerRow656 :=
  [⟨359, 2, 9, 5883322386, 5883322391, 2767871088, 62795542, 359000, 5572691⟩,
    ⟨19, 4, 4, 2944438978, 2944438981, 2755648831, 63567755, 361000, 2746187⟩,
    ⟨2, 17, 1, 693147180, 693147181, 2749328063, 63970824, 362039, 641302⟩,
    ⟨367, 2, 9, 5905361845, 5905361851, 2719384276, 65915321, 367000, 5257731⟩]

private theorem powers340_1_valid :
    powers340_1.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_2 : List PowerRow656 :=
  [⟨373, 2, 9, 5921578417, 5921578422, 2683707819, 68309398, 373000, 5032269⟩,
    ⟨379, 2, 9, 5937536202, 5937536208, 2648600690, 70750138, 379000, 4815655⟩,
    ⟨383, 2, 9, 5948034986, 5948034992, 2625503365, 72403296, 383000, 4676001⟩,
    ⟨53, 3, 6, 3970291911, 3970291915, 2609217028, 73592135, 385846, 3052596⟩]

private theorem powers340_2_valid :
    powers340_2.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_3 : List PowerRow656 :=
  [⟨389, 2, 9, 5963579341, 5963579346, 2591305787, 74922137, 389000, 4473418⟩,
    ⟨397, 2, 9, 5983936278, 5983936283, 2546520525, 78353816, 397000, 4215714⟩,
    ⟨401, 2, 9, 5993961424, 5993961430, 2524465202, 80101132, 401000, 4091982⟩,
    ⟨11, 5, 4, 2397895271, 2397895274, 2522756341, 80238131, 401312, 1632991⟩]

private theorem powers340_3_valid :
    powers340_3.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_4 : List PowerRow656 :=
  [⟨409, 2, 9, 6013715153, 6013715159, 2481006998, 83658932, 409000, 3854343⟩,
    ⟨419, 2, 9, 6037870917, 6037870923, 2427864317, 88225045, 419000, 3574887⟩,
    ⟨3, 11, 2, 1098612288, 1098612290, 2417971639, 89102159, 420889, 640765⟩,
    ⟨421, 2, 9, 6042632831, 6042632836, 2417388109, 89154168, 421000, 3521245⟩]

private theorem powers340_4_valid :
    powers340_4.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_5 : List PowerRow656 :=
  [⟨431, 2, 9, 6066108087, 6066108093, 2365742543, 93879558, 431000, 3263772⟩,
    ⟨433, 2, 9, 6070737725, 6070737731, 2355557340, 94840626, 433000, 3214363⟩,
    ⟨439, 2, 9, 6084499410, 6084499416, 2325281633, 97755902, 439000, 3070150⟩,
    ⟨443, 2, 9, 6093569767, 6093569773, 2305326847, 99726193, 443000, 2977271⟩]

private theorem powers340_5_valid :
    powers340_5.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_6 : List PowerRow656 :=
  [⟨449, 2, 9, 6107022885, 6107022890, 2275729990, 102721888, 449000, 2842683⟩,
    ⟨59, 3, 6, 4077537442, 4077537446, 2255306776, 104841369, 453188, 1834673⟩,
    ⟨457, 2, 9, 6124683388, 6124683394, 2236876881, 106791500, 457000, 2671733⟩,
    ⟨461, 2, 9, 6133398040, 6133398046, 2217704647, 108858684, 461000, 2589765⟩]

private theorem powers340_6_valid :
    powers340_6.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_7 : List PowerRow656 :=
  [⟨463, 2, 9, 6137727051, 6137727057, 2208180822, 109900388, 463000, 2549632⟩,
    ⟨467, 2, 9, 6146329255, 6146329260, 2189255976, 112000041, 467000, 2471032⟩,
    ⟨61, 3, 6, 4110873862, 4110873866, 2145296590, 117033314, 476426, 1529548⟩,
    ⟨479, 2, 9, 6171700595, 6171700600, 2133439028, 118429304, 479000, 2248061⟩]

private theorem powers340_7_valid :
    powers340_7.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_8 : List PowerRow656 :=
  [⟨487, 2, 9, 6188264120, 6188264126, 2096999271, 122824432, 487000, 2109573⟩,
    ⟨491, 2, 9, 6196444125, 6196444130, 2079003262, 125054790, 491000, 2043223⟩,
    ⟨499, 2, 9, 6212606093, 6212606098, 2043446932, 129581275, 499000, 1916067⟩,
    ⟨503, 2, 9, 6220590167, 6220590173, 2025881967, 131877473, 503000, 1855168⟩]

private theorem powers340_8_valid :
    powers340_8.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_9 : List PowerRow656 :=
  [⟨509, 2, 9, 6232448014, 6232448019, 1999794706, 135363062, 509000, 1767041⟩,
    ⟨2, 18, 1, 693147180, 693147181, 1986866164, 137124471, 512000, 191597⟩,
    ⟨521, 2, 9, 6255750039, 6255750044, 1948530251, 142483325, 521000, 1601843⟩,
    ⟨523, 2, 9, 6259581461, 6259581467, 1940101120, 143689412, 523000, 1575682⟩]

private theorem powers340_9_valid :
    powers340_9.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_10 : List PowerRow656 :=
  [⟨23, 4, 5, 3135494214, 3135494218, 1915005789, 147340972, 529000, 749725⟩,
    ⟨541, 2, 9, 6293419276, 6293419282, 1865657927, 154794326, 541000, 1356697⟩,
    ⟨547, 2, 9, 6304448800, 6304448805, 1841392977, 158596344, 547000, 1289923⟩,
    ⟨67, 3, 6, 4204692617, 4204692621, 1835694698, 159502650, 548419, 849708⟩]

private theorem powers340_10_valid :
    powers340_10.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_11 : List PowerRow656 :=
  [⟨557, 2, 9, 6322565237, 6322565243, 1801536813, 165045043, 557000, 1185044⟩,
    ⟨563, 2, 9, 6333279625, 6333279631, 1777965160, 168981641, 563000, 1125782⟩,
    ⟨569, 2, 9, 6343880431, 6343880437, 1754643386, 172968907, 569000, 1069137⟩,
    ⟨571, 2, 9, 6347389207, 6347389212, 1746924081, 174309274, 571000, 1050819⟩]

private theorem powers340_11_valid :
    powers340_11.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_12 : List PowerRow656 :=
  [⟨577, 2, 9, 6357842264, 6357842269, 1723927356, 178364263, 577000, 997504⟩,
    ⟨587, 2, 9, 6375024817, 6375024822, 1686125739, 185235780, 587000, 913895⟩,
    ⟨593, 2, 9, 6385194396, 6385194402, 1663752663, 189426782, 593000, 866728⟩,
    ⟨71, 3, 6, 4262679875, 4262679879, 1644336747, 193140614, 598257, 551442⟩]

private theorem powers340_12_valid :
    powers340_12.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_13 : List PowerRow656 :=
  [⟨599, 2, 9, 6395261595, 6395261601, 1641604826, 193668980, 599000, 821699⟩,
    ⟨601, 2, 9, 6398594932, 6398594937, 1634271486, 195094441, 601000, 807150⟩,
    ⟨607, 2, 9, 6408528788, 6408528794, 1612417001, 199405061, 607000, 764840⟩,
    ⟨13, 5, 4, 2564949356, 2564949359, 1603958873, 201098808, 609339, 299552⟩]

private theorem powers340_13_valid :
    powers340_13.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_14 : List PowerRow656 :=
  [⟨613, 2, 9, 6418364933, 6418364939, 1590777482, 203767117, 613000, 724474⟩,
    ⟨617, 2, 9, 6424869021, 6424869027, 1576468488, 206703780, 617000, 698605⟩,
    ⟨619, 2, 9, 6428105270, 6428105275, 1569348743, 208180710, 619000, 685974⟩,
    ⟨73, 3, 6, 4290459439, 4290459443, 1552664186, 211683251, 623713, 437996⟩]

private theorem powers340_14_valid :
    powers340_14.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_15 : List PowerRow656 :=
  [⟨5, 8, 2, 1609437911, 1609437913, 1548126713, 212645940, 625000, 162315⟩,
    ⟨631, 2, 9, 6447305860, 6447305865, 1527107445, 217162908, 631000, 614271⟩,
    ⟨641, 2, 9, 6463029454, 6463029460, 1492515536, 224806427, 641000, 559576⟩,
    ⟨643, 2, 9, 6466144721, 6466144727, 1485661948, 226352450, 643000, 549158⟩]

private theorem powers340_15_valid :
    powers340_15.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_16 : List PowerRow656 :=
  [⟨647, 2, 9, 6472346292, 6472346297, 1472018494, 229461842, 647000, 528825⟩,
    ⟨653, 2, 9, 6481577126, 6481577132, 1451710657, 234169354, 653000, 499546⟩,
    ⟨659, 2, 9, 6490723532, 6490723537, 1431588566, 238929058, 659000, 471677⟩,
    ⟨661, 2, 9, 6493753837, 6493753843, 1424921893, 240527242, 661000, 462691⟩]

private theorem powers340_16_valid :
    powers340_16.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_17 : List PowerRow656 :=
  [⟨673, 2, 9, 6511745327, 6511745332, 1385340617, 250238542, 673000, 411810⟩,
    ⟨677, 2, 9, 6517671270, 6517671276, 1372303541, 253522280, 677000, 395957⟩,
    ⟨683, 2, 10, 6526494856, 6526494862, 1352891651, 258491703, 683000, 373163⟩,
    ⟨691, 2, 10, 6538139821, 6538139827, 1327272728, 265199539, 691000, 344530⟩]

private theorem powers340_17_valid :
    powers340_17.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_18 : List PowerRow656 :=
  [⟨701, 2, 10, 6552507884, 6552507890, 1295662990, 273716325, 701000, 311406⟩,
    ⟨79, 3, 6, 4369447850, 4369447854, 1292002430, 274720116, 702168, 205148⟩,
    ⟨709, 2, 10, 6563855523, 6563855529, 1270698184, 280635610, 709000, 286909⟩,
    ⟨719, 2, 10, 6577861355, 6577861361, 1239885354, 289417389, 719000, 258621⟩]

private theorem powers340_18_valid :
    powers340_18.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_19 : List PowerRow656 :=
  [⟨2, 19, 1, 693147180, 693147181, 1224404265, 293932746, 724078, 25809⟩,
    ⟨727, 2, 10, 6588926474, 6588926480, 1215542092, 296549206, 727000, 237740⟩,
    ⟨3, 12, 2, 1098612288, 1098612290, 1209498120, 298346968, 729000, 38791⟩,
    ⟨733, 2, 10, 6597145699, 6597145705, 1197459797, 301960271, 733000, 223040⟩]

private theorem powers340_19_valid :
    powers340_19.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_20 : List PowerRow656 :=
  [⟨739, 2, 10, 6605297918, 6605297924, 1179524915, 307424749, 739000, 209121⟩,
    ⟨743, 2, 10, 6610696042, 6610696048, 1167649042, 311097451, 743000, 200259⟩,
    ⟨751, 2, 10, 6621405649, 6621405655, 1144087907, 318514292, 751000, 183490⟩,
    ⟨83, 3, 6, 4418840606, 4418840610, 1129006335, 323354395, 756166, 115538⟩]

private theorem powers340_20_valid :
    powers340_20.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_21 : List PowerRow656 :=
  [⟨757, 2, 10, 6629363250, 6629363256, 1126581185, 324139529, 757000, 171710⟩,
    ⟨761, 2, 10, 6634633355, 6634633361, 1114986954, 327919549, 761000, 164219⟩,
    ⟨769, 2, 10, 6645090966, 6645090972, 1091980209, 335551365, 769000, 150066⟩,
    ⟨773, 2, 10, 6650279045, 6650279051, 1080566436, 339403213, 773000, 143386⟩]

private theorem powers340_21_valid :
    powers340_21.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_22 : List PowerRow656 :=
  [⟨787, 2, 10, 6668228245, 6668228251, 1041078196, 353073786, 787000, 121953⟩,
    ⟨797, 2, 10, 6680854676, 6680854682, 1013300047, 363019013, 797000, 108359⟩,
    ⟨809, 2, 10, 6695798914, 6695798920, 980422724, 375152471, 809000, 93756⟩,
    ⟨811, 2, 10, 6698268051, 6698268057, 974990622, 377195883, 811000, 91492⟩]

private theorem powers340_22_valid :
    powers340_22.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_23 : List PowerRow656 :=
  [⟨821, 2, 10, 6710523106, 6710523112, 948029501, 387503839, 821000, 80848⟩,
    ⟨823, 2, 10, 6712956198, 6712956204, 942676699, 389583632, 823000, 78850⟩,
    ⟨827, 2, 10, 6717804692, 6717804698, 932010012, 393761441, 827000, 74977⟩,
    ⟨829, 2, 10, 6720220152, 6720220158, 926696000, 395859463, 829000, 73102⟩]

private theorem powers340_23_valid :
    powers340_23.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_24 : List PowerRow656 :=
  [⟨839, 2, 10, 6732210703, 6732210709, 900316788, 406440875, 839000, 64304⟩,
    ⟨89, 3, 7, 4488636367, 4488636372, 898680320, 407106547, 839625, 42523⟩,
    ⟨29, 4, 5, 3367295828, 3367295832, 895078687, 408575439, 841000, 31327⟩,
    ⟨853, 2, 10, 6748759544, 6748759550, 863909338, 421511019, 853000, 53492⟩]

private theorem powers340_24_valid :
    powers340_24.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_25 : List PowerRow656 :=
  [⟨857, 2, 10, 6753437915, 6753437921, 853616922, 425871789, 857000, 50700⟩,
    ⟨859, 2, 10, 6755768919, 6755768925, 848488713, 428061358, 859000, 49350⟩,
    ⟨863, 2, 10, 6760414688, 6760414694, 838268021, 432458876, 863000, 46740⟩,
    ⟨877, 2, 10, 6776506989, 6776506995, 802864959, 448043489, 877000, 38495⟩]

private theorem powers340_25_valid :
    powers340_25.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_26 : List PowerRow656 :=
  [⟨881, 2, 10, 6781057623, 6781057629, 792853564, 452551557, 881000, 36376⟩,
    ⟨883, 2, 10, 6783325198, 6783325204, 787864899, 454814826, 883000, 35354⟩,
    ⟨887, 2, 10, 6787844979, 6787844985, 777921381, 459359845, 887000, 33381⟩,
    ⟨907, 2, 10, 6810142447, 6810142453, 728866951, 482455317, 907000, 24837⟩]

private theorem powers340_26_valid :
    powers340_26.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_27 : List PowerRow656 :=
  [⟨7, 7, 3, 1945910148, 1945910150, 727672193, 483032079, 907493, 7042⟩,
    ⟨911, 2, 10, 6814542894, 6814542900, 719185968, 487148640, 911000, 23369⟩,
    ⟨919, 2, 10, 6823286119, 6823286125, 699950873, 496609691, 919000, 20648⟩,
    ⟨929, 2, 10, 6834108736, 6834108742, 676141115, 508575737, 929000, 17622⟩]

private theorem powers340_27_valid :
    powers340_27.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_28 : List PowerRow656 :=
  [⟨937, 2, 10, 6842683279, 6842683285, 657277121, 518260567, 937000, 15474⟩,
    ⟨941, 2, 10, 6846943136, 6846943142, 647905435, 523140372, 941000, 14485⟩,
    ⟨947, 2, 10, 6853299090, 6853299096, 633922337, 530506879, 947000, 13099⟩,
    ⟨953, 2, 10, 6859614901, 6859614907, 620027552, 537929607, 953000, 11825⟩]

private theorem powers340_28_valid :
    powers340_28.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_29 : List PowerRow656 :=
  [⟨97, 3, 7, 4574710976, 4574710981, 614634110, 540838737, 955340, 7571⟩,
    ⟨31, 4, 5, 3433987203, 3433987206, 601636641, 547914154, 961000, 5143⟩,
    ⟨967, 2, 10, 6874198492, 6874198498, 587943652, 555468338, 967000, 9246⟩,
    ⟨971, 2, 10, 6878326465, 6878326471, 578862112, 560535822, 971000, 8601⟩]

private theorem powers340_29_valid :
    powers340_29.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_30 : List PowerRow656 :=
  [⟨977, 2, 10, 6884486649, 6884486655, 565309707, 568184140, 977000, 7704⟩,
    ⟨983, 2, 10, 6890609117, 6890609123, 551840277, 575889030, 983000, 6885⟩,
    ⟨991, 2, 10, 6898714531, 6898714537, 534008366, 586250338, 991000, 5906⟩,
    ⟨997, 2, 10, 6904750767, 6904750773, 520728647, 594087501, 997000, 5249⟩]

private theorem powers340_30_valid :
    powers340_30.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_31 : List PowerRow656 :=
  [⟨1009, 2, 10, 6916715017, 6916715023, 494407297, 609932299, 1009000, 4116⟩,
    ⟨1013, 2, 10, 6920671501, 6920671507, 485703032, 615264484, 1013000, 3786⟩,
    ⟨101, 3, 7, 4615120515, 4615120519, 481282635, 617990218, 1015038, 2417⟩,
    ⟨1019, 2, 10, 6926577030, 6926577036, 472710869, 623310254, 1019000, 3332⟩]

private theorem powers340_31_valid :
    powers340_31.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_32 : List PowerRow656 :=
  [⟨1021, 2, 10, 6928537815, 6928537821, 468397142, 626004852, 1021000, 3191⟩,
    ⟨2, 20, 1, 693147180, 693147181, 461942366, 630058642, 1024000, 298⟩,
    ⟨1031, 2, 10, 6938284481, 6938284487, 446954476, 639573014, 1031000, 2558⟩,
    ⟨1033, 2, 10, 6940222466, 6940222472, 442690909, 642305698, 1033000, 2444⟩]

private theorem powers340_32_valid :
    powers340_32.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_33 : List PowerRow656 :=
  [⟨1039, 2, 10, 6946013988, 6946013994, 429949561, 650541897, 1039000, 2128⟩,
    ⟨103, 3, 7, 4634728986, 4634728990, 416574681, 659301264, 1045336, 1221⟩,
    ⟨1049, 2, 10, 6955592605, 6955592611, 408876604, 664396201, 1049000, 1677⟩,
    ⟨1051, 2, 10, 6957497368, 6957497374, 404686125, 667186181, 1051000, 1596⟩]

private theorem powers340_33_valid :
    powers340_33.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_34 : List PowerRow656 :=
  [⟨1061, 2, 10, 6966967136, 6966967142, 383852635, 681231800, 1061000, 1241⟩,
    ⟨1063, 2, 10, 6968850375, 6968850381, 379709510, 684060083, 1063000, 1178⟩,
    ⟨1069, 2, 10, 6974478908, 6974478914, 367326737, 692583306, 1069000, 1006⟩,
    ⟨1087, 2, 10, 6991176884, 6991176890, 330591190, 718498828, 1087000, 607⟩]

private theorem powers340_34_valid :
    powers340_34.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_35 : List PowerRow656 :=
  [⟨1091, 2, 10, 6994849983, 6994849989, 322510372, 724328409, 1091000, 539⟩,
    ⟨1093, 2, 10, 6996681485, 6996681491, 318481068, 727252836, 1093000, 507⟩,
    ⟨1097, 2, 10, 7000334457, 7000334463, 310444529, 733120980, 1097000, 448⟩,
    ⟨1103, 2, 10, 7005789016, 7005789022, 298444499, 741971451, 1103000, 370⟩]

private theorem powers340_35_valid :
    powers340_35.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_36 : List PowerRow656 :=
  [⟨107, 3, 7, 4672828832, 4672828837, 290845186, 747631403, 1106817, 217⟩,
    ⟨1109, 2, 10, 7011213984, 7011213990, 286509570, 750879882, 1109000, 304⟩,
    ⟨1117, 2, 10, 7018401796, 7018401802, 270696383, 762848065, 1117000, 231⟩,
    ⟨1123, 2, 10, 7023758952, 7023758958, 258910640, 771891986, 1123000, 186⟩]

private theorem powers340_36_valid :
    powers340_36.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_37 : List PowerRow656 :=
  [⟨1129, 2, 10, 7029087561, 7029087567, 247187700, 780994077, 1129000, 148⟩,
    ⟨109, 3, 7, 4691347880, 4691347884, 229732331, 794746293, 1137994, 68⟩,
    ⟨1151, 2, 10, 7048386406, 7048386412, 204730241, 814867094, 1151000, 58⟩,
    ⟨1153, 2, 10, 7050122517, 7050122523, 200910797, 817985384, 1153000, 53⟩]

private theorem powers340_37_valid :
    powers340_37.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_38 : List PowerRow656 :=
  [⟨1163, 2, 10, 7058758149, 7058758155, 181912407, 833674351, 1163000, 32⟩,
    ⟨1171, 2, 10, 7065613360, 7065613366, 166830943, 846342669, 1171000, 20⟩,
    ⟨1181, 2, 10, 7074116813, 7074116819, 148123346, 862324733, 1181000, 11⟩,
    ⟨1187, 2, 10, 7079184392, 7079184398, 136974672, 871992301, 1187000, 7⟩]

private theorem powers340_38_valid :
    powers340_38.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340_39 : List PowerRow656 :=
  [⟨17, 5, 4, 2833213343, 2833213346, 128506945, 879407444, 1191578, 1⟩,
    ⟨1193, 2, 10, 7084226419, 7084226425, 125882213, 881718685, 1193000, 4⟩,
    ⟨1201, 2, 10, 7090909819, 7090909825, 111178733, 894778797, 1201000, 1⟩,
    ⟨113, 3, 7, 4727387816, 4727387821, 110800538, 895117262, 1201207, 0⟩]

private theorem powers340_39_valid :
    powers340_39.all (fun a ↦ decide (a.Valid 340 (5828945614 / 1000000000))) = true := by
  decide +kernel

private def powers340 : List PowerRow656 :=
  powers340_0 ++ powers340_1 ++ powers340_2 ++ powers340_3 ++ powers340_4 ++ powers340_5 ++
    powers340_6 ++
    powers340_7 ++
    powers340_8 ++
    powers340_9 ++
    powers340_10 ++
    powers340_11 ++
    powers340_12 ++
    powers340_13 ++
    powers340_14 ++
    powers340_15 ++
    powers340_16 ++
    powers340_17 ++
    powers340_18 ++
    powers340_19 ++
    powers340_20 ++
    powers340_21 ++
    powers340_22 ++
    powers340_23 ++
    powers340_24 ++
    powers340_25 ++
    powers340_26 ++
    powers340_27 ++
    powers340_28 ++
    powers340_29 ++
    powers340_30 ++
    powers340_31 ++
    powers340_32 ++
    powers340_33 ++
    powers340_34 ++
    powers340_35 ++
    powers340_36 ++
    powers340_37 ++
    powers340_38 ++
    powers340_39

private theorem powers340_valid (a : PowerRow656) (ha : a ∈ powers340) :
    a.Valid 340 (5828945614 / 1000000000) := by
  have hc : powers340.all (fun b ↦ decide (b.Valid 340 (5828945614 / 1000000000))) = true := by
    simp only [powers340, List.all_append, powers340_0_valid, powers340_1_valid, powers340_2_valid,
      powers340_3_valid, powers340_4_valid, powers340_5_valid, powers340_6_valid, powers340_7_valid,
      powers340_8_valid, powers340_9_valid, powers340_10_valid, powers340_11_valid,
      powers340_12_valid, powers340_13_valid, powers340_14_valid, powers340_15_valid,
      powers340_16_valid, powers340_17_valid, powers340_18_valid, powers340_19_valid,
      powers340_20_valid, powers340_21_valid, powers340_22_valid, powers340_23_valid,
      powers340_24_valid, powers340_25_valid, powers340_26_valid, powers340_27_valid,
      powers340_28_valid, powers340_29_valid, powers340_30_valid, powers340_31_valid,
      powers340_32_valid, powers340_33_valid, powers340_34_valid, powers340_35_valid,
      powers340_36_valid, powers340_37_valid, powers340_38_valid, powers340_39_valid, Bool.and_self]
  exact of_decide_eq_true (List.all_eq_true.mp hc a ha)

private theorem powers340_set :
    (powers340.toFinset.image (fun a ↦ a.p ^ a.k)) = fixedPowers663.erase (337 ^ 2) := by
  decide +kernel

private theorem powers340_card :
    (powers340.toFinset.image (fun a ↦ a.p ^ a.k)).card = powers340.toFinset.card := by
  decide +kernel

private theorem powers340_credit : (∑ a ∈ powers340.toFinset, a.credit) = 149087494 := by
  decide +kernel

private def power340Removed : PowerRow656 :=
  ⟨7, 6, 3, 1945910148, 1945910150, 2868173358, 56802583, 343000, 2084981⟩

private theorem powers340_without_set :
    (powers340.toFinset.erase power340Removed).image (fun a ↦ a.p ^ a.k) =
      (fixedPowers663.erase (337 ^ 2)).erase (7 ^ 6) := by
  decide +kernel

private theorem powers340_without_credit :
    (∑ a ∈ powers340.toFinset.erase power340Removed, a.credit) = 147002513 := by
  have hm : power340Removed ∈ powers340.toFinset := by decide +kernel
  have h := Finset.sum_erase_add powers340.toFinset PowerRow656.credit hm
  rw [powers340_credit] at h
  exact Nat.add_right_cancel (h.trans (by decide +kernel))

/-- Removing the power of seven that enters the tested cutoff leaves
a radius-340 forward contribution of at least 0.147. -/
theorem gaussian_power_gain_340_without343 :
    (0.147 : ℝ) ≤
      ∑ k ∈ (fixedPowers663.erase (337 ^ 2)).erase (7 ^ 6),
        4 * (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) ((340 : ℝ) ^ 2) k).re := by
  have hL :=
    (Analysis.rationalLogIntervalCheck_sound (N := 340) (j := 8) (n := 27) (lo :=
        5828945614 / 1000000000) (hi := 5828945626 / 1000000000) (by decide +kernel)).1
  simp only [Rat.cast_ofNat] at hL
  have h :=
    Finset.sum_le_sum (s := powers340.toFinset.erase power340Removed)
      (fun a ha ↦
        PowerRow656.sound a (by norm_num only : (0 : ℝ) < (340 : ℕ)) hL
          (powers340_valid a (List.mem_toFinset.mp (Finset.mem_of_mem_erase ha))))
  rw [← Finset.sum_div, ← Nat.cast_sum, powers340_without_credit, Nat.cast_ofNat] at h
  have hinj := Finset.injOn_of_card_image_eq powers340_card
  rw [← powers340_without_set,
    Finset.sum_image
      (fun _ ha _ hb hab ↦ hinj (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab)]
  exact (by norm_num only : (0.147 : ℝ) ≤ 147002513 / 1000000000).trans h

/-- The radius-340 forward contribution of the retained K197 powers is at least
0.14908. Rational endpoint checks certify the individual weights. -/
theorem gaussian_power_gain_340 :
    (0.14908 : ℝ) ≤
      ∑ k ∈ fixedPowers663.erase (337 ^ 2),
        4 * (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) ((340 : ℝ) ^ 2) k).re := by
  have hL :=
    (Analysis.rationalLogIntervalCheck_sound (N := 340) (j := 8) (n := 27) (lo :=
        5828945614 / 1000000000) (hi := 5828945626 / 1000000000) (by decide +kernel)).1
  simp only [Rat.cast_ofNat] at hL
  have h :=
    Finset.sum_le_sum (s := powers340.toFinset)
      (fun a ha ↦
        PowerRow656.sound a (by norm_num only : (0 : ℝ) < (340 : ℕ)) hL
          (powers340_valid a (List.mem_toFinset.mp ha)))
  rw [← Finset.sum_div, ← Nat.cast_sum, powers340_credit, Nat.cast_ofNat] at h
  have hinj := Finset.injOn_of_card_image_eq powers340_card
  rw [← powers340_set, Finset.sum_image (fun _ ha _ hb hab ↦ hinj ha hb hab)]
  exact (by norm_num only : (0.14908 : ℝ) ≤ 149087494 / 1000000000).trans h

end PseudoPrime.PrimeTestBounds.MillerRabin

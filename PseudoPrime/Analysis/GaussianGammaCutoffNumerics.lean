/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianGammaCutoffPartition

/-! # Kernel verification of the Gaussian cutoff integer certificate

Each computation covers 250 nodes, preventing a large normalization cache for
all 16,000 nodes at once. The partition theorem combines the exact block values.
-/

@[expose] public section

namespace PseudoPrime.Analysis

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 0, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_00 :
    gaussianCutoffMidpointBlock 0 = 19016257375463677731807994571942 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 1, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_01 :
    gaussianCutoffMidpointBlock 1 = 53191991914307130744192838881725 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 2, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_02 :
    gaussianCutoffMidpointBlock 2 = 144221270880347123890023216951370 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 3, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_03 :
    gaussianCutoffMidpointBlock 3 = 379030659835212713247020844271654 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 4, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_04 :
    gaussianCutoffMidpointBlock 4 = 965564795168289314701171553318109 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 5, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_05 :
    gaussianCutoffMidpointBlock 5 = 2384243781491533111772462853667311 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 6, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_06 :
    gaussianCutoffMidpointBlock 6 = 5706661892944407503240350401567661 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 7, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_07 :
    gaussianCutoffMidpointBlock 7 = 13239633550600750108141750912743227 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 8, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_08 :
    gaussianCutoffMidpointBlock 8 = 29773659256565823159808939420288063 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 9, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_09 :
    gaussianCutoffMidpointBlock 9 = 64900938107505127434594943411653568 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 10, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_10 :
    gaussianCutoffMidpointBlock 10 = 137129953387404367119259150329688666 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 11, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_11 :
    gaussianCutoffMidpointBlock 11 = 280851245992602712614288565377317619 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 12, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_12 :
    gaussianCutoffMidpointBlock 12 = 557549114004186101406616558036698426 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 13, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_13 :
    gaussianCutoffMidpointBlock 13 = 1072883895040700265366503759193556936 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 14, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_14 :
    gaussianCutoffMidpointBlock 14 = 2001175650915343480830616864623968673 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 15, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_15 :
    gaussianCutoffMidpointBlock 15 = 3618100473584027901769844039296447164 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 16, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_16 :
    gaussianCutoffMidpointBlock 16 = 6340724443762163922575360808832291980 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 17, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_17 :
    gaussianCutoffMidpointBlock 17 = 10771082605499234565793773353924886600 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 18, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_18 :
    gaussianCutoffMidpointBlock 18 = 17735341984034348474258757815484249820 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 19, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_19 :
    gaussianCutoffMidpointBlock 19 = 28305563112271967975443472069323379195 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 20, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_20 :
    gaussianCutoffMidpointBlock 20 = 43786094161889237037126737180176846793 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 21, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_21 :
    gaussianCutoffMidpointBlock 21 = 65643140709566217864447025045262186055 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 22, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_22 :
    gaussianCutoffMidpointBlock 22 = 95356206308446335982589808135311520072 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 23, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_23 :
    gaussianCutoffMidpointBlock 23 = 134177079013521923409439530814841063163 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 24, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_24 :
    gaussianCutoffMidpointBlock 24 = 182799813798105725538473198810584018397 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 25, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_25 :
    gaussianCutoffMidpointBlock 25 = 240976246064905312252766791845722944375 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 26, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_26 :
    gaussianCutoffMidpointBlock 26 = 307152444985098822000038859755489404007 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 27, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_27 :
    gaussianCutoffMidpointBlock 27 = 378238503384806527086018822750374433965 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 28, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_28 :
    gaussianCutoffMidpointBlock 28 = 449634985297559447218065721355365016970 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 29, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_29 :
    gaussianCutoffMidpointBlock 29 = 515603897560661344427684149524723924085 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 30, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_30 :
    gaussianCutoffMidpointBlock 30 = 569986673046234880956214324539235109154 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 31, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_31 :
    gaussianCutoffMidpointBlock 31 = 607158741944948938517678368671674981493 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 32, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_32 :
    gaussianCutoffMidpointBlock 32 = 623012757129897709699302826610863735838 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 33, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_33 :
    gaussianCutoffMidpointBlock 33 = 615724437617584632811842081192949475849 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 34, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_34 :
    gaussianCutoffMidpointBlock 34 = 586098521188458273167121356972800367770 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 35, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_35 :
    gaussianCutoffMidpointBlock 35 = 537405360312891124423691536903014635009 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 36, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_36 :
    gaussianCutoffMidpointBlock 36 = 474759947815118265772026288868213916172 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 37, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_37 :
    gaussianCutoffMidpointBlock 37 = 404213535134091908037609804918914595123 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 38, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_38 :
    gaussianCutoffMidpointBlock 38 = 331785187649255609830686990504492799707 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 39, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_39 :
    gaussianCutoffMidpointBlock 39 = 262645263416207586365757784098065951591 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 40, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_40 :
    gaussianCutoffMidpointBlock 40 = 200590970153600476704778209992928457526 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 41, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_41 :
    gaussianCutoffMidpointBlock 41 = 147858297782789254501964403275566120212 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 42, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_42 :
    gaussianCutoffMidpointBlock 42 = 105228274773527267280633398393635308037 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 43, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_43 :
    gaussianCutoffMidpointBlock 43 = 72331150548547624734317780953537669688 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 44, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_44 :
    gaussianCutoffMidpointBlock 44 = 48036371992632476526500626990512876250 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 45, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_45 :
    gaussianCutoffMidpointBlock 45 = 30832126858518695962928243294699539840 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 46, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_46 :
    gaussianCutoffMidpointBlock 46 = 19131631772558077503641857803617977659 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 47, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_47 :
    gaussianCutoffMidpointBlock 47 = 11479754853496153661780934740728878872 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 48, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_48 :
    gaussianCutoffMidpointBlock 48 = 6662730785947135911408233191747555759 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 49, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_49 :
    gaussianCutoffMidpointBlock 49 = 3741178420778671266260799614983395610 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 50, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_50 :
    gaussianCutoffMidpointBlock 50 = 2032775719351146759277488307779239603 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 51, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_51 :
    gaussianCutoffMidpointBlock 51 = 1068993987090500624234065409580972826 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 52, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_52 :
    gaussianCutoffMidpointBlock 52 = 544173955966004116033645981779515536 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 53, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_53 :
    gaussianCutoffMidpointBlock 53 = 268189370049932601183929261325152372 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 54, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_54 :
    gaussianCutoffMidpointBlock 54 = 127980736304114247155538401338075451 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 55, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_55 :
    gaussianCutoffMidpointBlock 55 = 59142365693545586410461383429568328 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 56, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_56 :
    gaussianCutoffMidpointBlock 56 = 26469764813226527802084344436555734 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 57, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_57 :
    gaussianCutoffMidpointBlock 57 = 11474665069685852158074008689623839 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 58, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_58 :
    gaussianCutoffMidpointBlock 58 = 4818426297772330228315745529683795 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 59, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_59 :
    gaussianCutoffMidpointBlock 59 = 1960100544326459492787023704346194 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 60, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_60 :
    gaussianCutoffMidpointBlock 60 = 772482092384343144837418963041214 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 61, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_61 :
    gaussianCutoffMidpointBlock 61 = 294958685932679932114711597016572 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 62, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_62 :
    gaussianCutoffMidpointBlock 62 = 109123804984967365563495815306358 := by decide +kernel

-- Kernel reduction checks 250 nodes, each with 121 outward-rounded Taylor terms.
/-- Exact integer value of midpoint block 63, verified by kernel reduction.
The node specification equality transfers this executable value to the analytic bound. -/
theorem gaussianCutoffMidpointBlock_value_63 :
    gaussianCutoffMidpointBlock 63 = 39118626605623478129357320813785 := by decide +kernel

/-- The full execution sum equals the stated fixed-point value.
Combine the 64 kernel-verified blocks using the finite partition identity.
This completes the arithmetic part of the Gaussian cutoff certificate. -/
theorem gaussianCutoffMidpointLowerFast_value :
    gaussianCutoffMidpointLowerFast = 8147136487896092080199149897249194016357 := by
  rw [gaussianCutoffMidpointLowerFast_eq_blocks]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, gaussianCutoffMidpointBlock_value_00,
    gaussianCutoffMidpointBlock_value_01, gaussianCutoffMidpointBlock_value_02,
    gaussianCutoffMidpointBlock_value_03, gaussianCutoffMidpointBlock_value_04,
    gaussianCutoffMidpointBlock_value_05, gaussianCutoffMidpointBlock_value_06,
    gaussianCutoffMidpointBlock_value_07, gaussianCutoffMidpointBlock_value_08,
    gaussianCutoffMidpointBlock_value_09, gaussianCutoffMidpointBlock_value_10,
    gaussianCutoffMidpointBlock_value_11, gaussianCutoffMidpointBlock_value_12,
    gaussianCutoffMidpointBlock_value_13, gaussianCutoffMidpointBlock_value_14,
    gaussianCutoffMidpointBlock_value_15, gaussianCutoffMidpointBlock_value_16,
    gaussianCutoffMidpointBlock_value_17, gaussianCutoffMidpointBlock_value_18,
    gaussianCutoffMidpointBlock_value_19, gaussianCutoffMidpointBlock_value_20,
    gaussianCutoffMidpointBlock_value_21, gaussianCutoffMidpointBlock_value_22,
    gaussianCutoffMidpointBlock_value_23, gaussianCutoffMidpointBlock_value_24,
    gaussianCutoffMidpointBlock_value_25, gaussianCutoffMidpointBlock_value_26,
    gaussianCutoffMidpointBlock_value_27, gaussianCutoffMidpointBlock_value_28,
    gaussianCutoffMidpointBlock_value_29, gaussianCutoffMidpointBlock_value_30,
    gaussianCutoffMidpointBlock_value_31, gaussianCutoffMidpointBlock_value_32,
    gaussianCutoffMidpointBlock_value_33, gaussianCutoffMidpointBlock_value_34,
    gaussianCutoffMidpointBlock_value_35, gaussianCutoffMidpointBlock_value_36,
    gaussianCutoffMidpointBlock_value_37, gaussianCutoffMidpointBlock_value_38,
    gaussianCutoffMidpointBlock_value_39, gaussianCutoffMidpointBlock_value_40,
    gaussianCutoffMidpointBlock_value_41, gaussianCutoffMidpointBlock_value_42,
    gaussianCutoffMidpointBlock_value_43, gaussianCutoffMidpointBlock_value_44,
    gaussianCutoffMidpointBlock_value_45, gaussianCutoffMidpointBlock_value_46,
    gaussianCutoffMidpointBlock_value_47, gaussianCutoffMidpointBlock_value_48,
    gaussianCutoffMidpointBlock_value_49, gaussianCutoffMidpointBlock_value_50,
    gaussianCutoffMidpointBlock_value_51, gaussianCutoffMidpointBlock_value_52,
    gaussianCutoffMidpointBlock_value_53, gaussianCutoffMidpointBlock_value_54,
    gaussianCutoffMidpointBlock_value_55, gaussianCutoffMidpointBlock_value_56,
    gaussianCutoffMidpointBlock_value_57, gaussianCutoffMidpointBlock_value_58,
    gaussianCutoffMidpointBlock_value_59, gaussianCutoffMidpointBlock_value_60,
    gaussianCutoffMidpointBlock_value_61, gaussianCutoffMidpointBlock_value_62,
    gaussianCutoffMidpointBlock_value_63]

end PseudoPrime.Analysis

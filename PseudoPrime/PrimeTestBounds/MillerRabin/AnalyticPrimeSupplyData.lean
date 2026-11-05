/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.AnalyticPrimeSupplies

/-! # RH prime supplies for the counting envelope

The rational data are grouped into small batches so each finite reduction is separately checked.
- a cutoff is the square of the recorded root;
- the count and relative width are shared across all product degrees;
- the last two fields specify the logarithm certificate.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Batch 1 of square cutoffs and their RH prime-supply certificate parameters. -/
def analyticSupplies01 : List AnalyticPrimeSupply :=
  [⟨40, 189, 16, 11, 737777 / 100000⟩, ⟨41, 198, 16, 11, 742716 / 100000⟩,
    ⟨42, 207, 17, 11, 747535 / 100000⟩, ⟨43, 216, 17, 11, 752242 / 100000⟩,
    ⟨45, 235, 18, 11, 761334 / 100000⟩, ⟨46, 244, 18, 12, 765730 / 100000⟩,
    ⟨47, 254, 18, 12, 770031 / 100000⟩, ⟨49, 274, 19, 12, 778366 / 100000⟩]

set_option maxRecDepth 16384 in
/-- Every rational certificate in batch 1 passes the finite checker. -/
theorem analyticSupplies01_checked : analyticSupplies01.all AnalyticPrimeSupply.check = true := by
  decide +kernel

/-- Under RH, every supply in batch 1 has its recorded prime count. -/
theorem analyticSupplies01_sound (hRH : RiemannHypothesis) (c : AnalyticPrimeSupply)
    (hc : c ∈ analyticSupplies01) : c.count ≤ (c.root ^ 2).primeCounting := by
  exact c.sound hRH (List.all_eq_true.mp analyticSupplies01_checked c hc)

/-- Batch 2 of square cutoffs and their RH prime-supply certificate parameters. -/
def analyticSupplies02 : List AnalyticPrimeSupply :=
  [⟨51, 295, 19, 12, 786367 / 100000⟩, ⟨52, 306, 19, 12, 790250 / 100000⟩,
    ⟨54, 328, 20, 12, 797798 / 100000⟩, ⟨57, 362, 20, 12, 808612 / 100000⟩,
    ⟨58, 373, 21, 12, 812090 / 100000⟩, ⟨59, 385, 21, 12, 815509 / 100000⟩,
    ⟨60, 397, 21, 12, 818870 / 100000⟩, ⟨61, 409, 21, 12, 822176 / 100000⟩]

set_option maxRecDepth 16384 in
/-- Every rational certificate in batch 2 passes the finite checker. -/
theorem analyticSupplies02_checked : analyticSupplies02.all AnalyticPrimeSupply.check = true := by
  decide +kernel

/-- Under RH, every supply in batch 2 has its recorded prime count. -/
theorem analyticSupplies02_sound (hRH : RiemannHypothesis) (c : AnalyticPrimeSupply)
    (hc : c ∈ analyticSupplies02) : c.count ≤ (c.root ^ 2).primeCounting := by
  exact c.sound hRH (List.all_eq_true.mp analyticSupplies02_checked c hc)

/-- Batch 3 of square cutoffs and their RH prime-supply certificate parameters. -/
def analyticSupplies03 : List AnalyticPrimeSupply :=
  [⟨63, 434, 22, 12, 828628 / 100000⟩, ⟨64, 447, 22, 13, 831778 / 100000⟩,
    ⟨66, 473, 22, 13, 837932 / 100000⟩, ⟨67, 486, 23, 13, 840940 / 100000⟩,
    ⟨69, 513, 23, 13, 846823 / 100000⟩, ⟨71, 540, 23, 13, 852537 / 100000⟩,
    ⟨72, 554, 24, 13, 855335 / 100000⟩, ⟨73, 568, 24, 13, 858093 / 100000⟩]

set_option maxRecDepth 16384 in
/-- Every rational certificate in batch 3 passes the finite checker. -/
theorem analyticSupplies03_checked : analyticSupplies03.all AnalyticPrimeSupply.check = true := by
  decide +kernel

/-- Under RH, every supply in batch 3 has its recorded prime count. -/
theorem analyticSupplies03_sound (hRH : RiemannHypothesis) (c : AnalyticPrimeSupply)
    (hc : c ∈ analyticSupplies03) : c.count ≤ (c.root ^ 2).primeCounting := by
  exact c.sound hRH (List.all_eq_true.mp analyticSupplies03_checked c hc)

/-- Batch 4 of square cutoffs and their RH prime-supply certificate parameters. -/
def analyticSupplies04 : List AnalyticPrimeSupply :=
  [⟨78, 641, 25, 13, 871343 / 100000⟩, ⟨80, 672, 25, 13, 876407 / 100000⟩,
    ⟨81, 687, 25, 13, 878891 / 100000⟩, ⟨82, 702, 26, 13, 881345 / 100000⟩,
    ⟨85, 750, 26, 13, 888532 / 100000⟩, ⟨87, 783, 26, 13, 893183 / 100000⟩,
    ⟨91, 850, 27, 14, 902173 / 100000⟩, ⟨93, 884, 28, 14, 906521 / 100000⟩]

set_option maxRecDepth 16384 in
/-- Every rational certificate in batch 4 passes the finite checker. -/
theorem analyticSupplies04_checked : analyticSupplies04.all AnalyticPrimeSupply.check = true := by
  decide +kernel

/-- Under RH, every supply in batch 4 has its recorded prime count. -/
theorem analyticSupplies04_sound (hRH : RiemannHypothesis) (c : AnalyticPrimeSupply)
    (hc : c ∈ analyticSupplies04) : c.count ≤ (c.root ^ 2).primeCounting := by
  exact c.sound hRH (List.all_eq_true.mp analyticSupplies04_checked c hc)

/-- Batch 5 of square cutoffs and their RH prime-supply certificate parameters. -/
def analyticSupplies05 : List AnalyticPrimeSupply :=
  [⟨96, 937, 28, 14, 912871 / 100000⟩, ⟨103, 1066, 29, 14, 926947 / 100000⟩,
    ⟨105, 1104, 30, 14, 930794 / 100000⟩, ⟨106, 1123, 30, 14, 932689 / 100000⟩,
    ⟨110, 1202, 30, 14, 940098 / 100000⟩, ⟨114, 1283, 31, 14, 947241 / 100000⟩,
    ⟨118, 1366, 32, 14, 954138 / 100000⟩, ⟨120, 1409, 32, 14, 957500 / 100000⟩]

set_option maxRecDepth 16384 in
/-- Every rational certificate in batch 5 passes the finite checker. -/
theorem analyticSupplies05_checked : analyticSupplies05.all AnalyticPrimeSupply.check = true := by
  decide +kernel

/-- Under RH, every supply in batch 5 has its recorded prime count. -/
theorem analyticSupplies05_sound (hRH : RiemannHypothesis) (c : AnalyticPrimeSupply)
    (hc : c ∈ analyticSupplies05) : c.count ≤ (c.root ^ 2).primeCounting := by
  exact c.sound hRH (List.all_eq_true.mp analyticSupplies05_checked c hc)

/-- Batch 6 of square cutoffs and their RH prime-supply certificate parameters. -/
def analyticSupplies06 : List AnalyticPrimeSupply :=
  [⟨126, 1541, 33, 14, 967258 / 100000⟩, ⟨135, 1748, 34, 15, 981056 / 100000⟩,
    ⟨138, 1820, 35, 15, 985452 / 100000⟩, ⟨139, 1844, 35, 15, 986896 / 100000⟩,
    ⟨140, 1869, 35, 15, 988330 / 100000⟩, ⟨144, 1968, 35, 15, 993964 / 100000⟩,
    ⟨153, 2199, 37, 15, 1006089 / 100000⟩, ⟨156, 2279, 37, 15, 1009973 / 100000⟩]

set_option maxRecDepth 16384 in
/-- Every rational certificate in batch 6 passes the finite checker. -/
theorem analyticSupplies06_checked : analyticSupplies06.all AnalyticPrimeSupply.check = true := by
  decide +kernel

/-- Under RH, every supply in batch 6 has its recorded prime count. -/
theorem analyticSupplies06_sound (hRH : RiemannHypothesis) (c : AnalyticPrimeSupply)
    (hc : c ∈ analyticSupplies06) : c.count ≤ (c.root ^ 2).primeCounting := by
  exact c.sound hRH (List.all_eq_true.mp analyticSupplies06_checked c hc)

/-- Batch 7 of square cutoffs and their RH prime-supply certificate parameters. -/
def analyticSupplies07 : List AnalyticPrimeSupply :=
  [⟨159, 2360, 37, 15, 1013782 / 100000⟩, ⟨174, 2785, 39, 15, 1031813 / 100000⟩,
    ⟨178, 2903, 40, 15, 1036358 / 100000⟩, ⟨181, 2994, 40, 15, 1039701 / 100000⟩,
    ⟨188, 3210, 41, 16, 1047290 / 100000⟩, ⟨196, 3466, 42, 16, 1055624 / 100000⟩,
    ⟨201, 3630, 43, 16, 1060662 / 100000⟩, ⟨204, 3730, 43, 16, 1063625 / 100000⟩]

set_option maxRecDepth 16384 in
/-- Every rational certificate in batch 7 passes the finite checker. -/
theorem analyticSupplies07_checked : analyticSupplies07.all AnalyticPrimeSupply.check = true := by
  decide +kernel

/-- Under RH, every supply in batch 7 has its recorded prime count. -/
theorem analyticSupplies07_sound (hRH : RiemannHypothesis) (c : AnalyticPrimeSupply)
    (hc : c ∈ analyticSupplies07) : c.count ≤ (c.root ^ 2).primeCounting := by
  exact c.sound hRH (List.all_eq_true.mp analyticSupplies07_checked c hc)

/-- The 56 analytic prime supplies used by the repeated-product counting envelope. -/
def analyticSupplies : List AnalyticPrimeSupply :=
  analyticSupplies01 ++ analyticSupplies02 ++ analyticSupplies03 ++ analyticSupplies04 ++
    analyticSupplies05 ++
    analyticSupplies06 ++
    analyticSupplies07

/-- All 56 rational prime-supply certificates pass, by combining the seven batch checks. -/
theorem analyticSupplies_checked : analyticSupplies.all AnalyticPrimeSupply.check = true := by
  simp only [analyticSupplies, List.all_append, analyticSupplies01_checked,
    analyticSupplies02_checked, analyticSupplies03_checked, analyticSupplies04_checked,
    analyticSupplies05_checked, analyticSupplies06_checked, analyticSupplies07_checked,
    Bool.true_and]

/-- Under RH, every entry in the full supply list has its recorded prime count. The proof
selects the checked entry and applies the soundness of the relative Chebyshev bound. -/
theorem analyticSupplies_sound (hRH : RiemannHypothesis) (c : AnalyticPrimeSupply)
    (hc : c ∈ analyticSupplies) : c.count ≤ (c.root ^ 2).primeCounting := by
  exact c.sound hRH (List.all_eq_true.mp analyticSupplies_checked c hc)

end PseudoPrime.PrimeTestBounds.MillerRabin

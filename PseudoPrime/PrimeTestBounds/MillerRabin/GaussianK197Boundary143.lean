/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Boundary
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Psi641539
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Psi681539
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Psi721539
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Psi761539
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Psi801539
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Psi841539
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Psi881539
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Psi921539
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Psi961539

/-! # Signed Chebyshev bounds for K197 cells 133 through 143 -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- The signed Chebyshev bound on the entire squared cutoff for K197 cell 133. -/
public theorem psi_gaussian_k197_cell133 {x : ℝ} (hl : 673799 ≤ x) (hu : x ≤ 700957) :
    -379 ≤ Chebyshev.psi x - x := by
  by_cases h671539 : x ≤ 676539
  · exact psi_cell133_671539 hl h671539
  by_cases h676539 : x ≤ 681539
  · exact psi_cell133_676539 (le_of_not_ge h671539) h676539
  by_cases h681539 : x ≤ 686539
  · exact psi_cell133_681539 (le_of_not_ge h676539) h681539
  by_cases h686539 : x ≤ 691539
  · exact psi_cell133_686539 (le_of_not_ge h681539) h686539
  by_cases h691539 : x ≤ 696539
  · exact psi_cell133_691539 (le_of_not_ge h686539) h691539
  exact psi_cell133_696539 (le_of_not_ge h691539) hu

/-- The signed Chebyshev bound on the entire squared cutoff for K197 cell 134. -/
public theorem psi_gaussian_k197_cell134 {x : ℝ} (hl : 701397 ≤ x) (hu : x ≤ 729110) :
    -271 ≤ Chebyshev.psi x - x := by
  by_cases h696539 : x ≤ 701539
  · exact psi_cell134_696539 hl h696539
  by_cases h701539 : x ≤ 706539
  · exact psi_cell134_701539 (le_of_not_ge h696539) h701539
  by_cases h706539 : x ≤ 711539
  · exact psi_cell134_706539 (le_of_not_ge h701539) h706539
  by_cases h711539 : x ≤ 716539
  · exact psi_cell134_711539 (le_of_not_ge h706539) h711539
  by_cases h716539 : x ≤ 721539
  · exact psi_cell134_716539 (le_of_not_ge h711539) h716539
  by_cases h721539 : x ≤ 726539
  · exact psi_cell134_721539 (le_of_not_ge h716539) h721539
  exact psi_cell134_726539 (le_of_not_ge h721539) hu

/-- The signed Chebyshev bound on the entire squared cutoff for K197 cell 135. -/
public theorem psi_gaussian_k197_cell135 {x : ℝ} (hl : 729550 ≤ x) (hu : x ≤ 757816) :
    -412 ≤ Chebyshev.psi x - x := by
  by_cases h726539 : x ≤ 731539
  · exact psi_cell135_726539 hl h726539
  by_cases h731539 : x ≤ 736539
  · exact psi_cell135_731539 (le_of_not_ge h726539) h731539
  by_cases h736539 : x ≤ 741539
  · exact psi_cell135_736539 (le_of_not_ge h731539) h736539
  by_cases h741539 : x ≤ 746539
  · exact psi_cell135_741539 (le_of_not_ge h736539) h741539
  by_cases h746539 : x ≤ 751539
  · exact psi_cell135_746539 (le_of_not_ge h741539) h746539
  by_cases h751539 : x ≤ 756539
  · exact psi_cell135_751539 (le_of_not_ge h746539) h751539
  exact psi_cell135_756539 (le_of_not_ge h751539) hu

/-- The signed Chebyshev bound on the entire squared cutoff for K197 cell 136. -/
public theorem psi_gaussian_k197_cell136 {x : ℝ} (hl : 758257 ≤ x) (hu : x ≤ 787078) :
    -396 ≤ Chebyshev.psi x - x := by
  by_cases h756539 : x ≤ 761539
  · exact psi_cell136_756539 hl h756539
  by_cases h761539 : x ≤ 766539
  · exact psi_cell136_761539 (le_of_not_ge h756539) h761539
  by_cases h766539 : x ≤ 771539
  · exact psi_cell136_766539 (le_of_not_ge h761539) h766539
  by_cases h771539 : x ≤ 776539
  · exact psi_cell136_771539 (le_of_not_ge h766539) h771539
  by_cases h776539 : x ≤ 781539
  · exact psi_cell136_776539 (le_of_not_ge h771539) h776539
  by_cases h781539 : x ≤ 786539
  · exact psi_cell136_781539 (le_of_not_ge h776539) h781539
  exact psi_cell136_786539 (le_of_not_ge h781539) hu

/-- The signed Chebyshev bound on the entire squared cutoff for K197 cell 137. -/
public theorem psi_gaussian_k197_cell137 {x : ℝ} (hl : 787519 ≤ x) (hu : x ≤ 816893) :
    -103 ≤ Chebyshev.psi x - x := by
  by_cases h786539 : x ≤ 791539
  · exact psi_cell137_786539 hl h786539
  by_cases h791539 : x ≤ 796539
  · exact psi_cell137_791539 (le_of_not_ge h786539) h791539
  by_cases h796539 : x ≤ 801539
  · exact psi_cell137_796539 (le_of_not_ge h791539) h796539
  by_cases h801539 : x ≤ 806539
  · exact psi_cell137_801539 (le_of_not_ge h796539) h801539
  by_cases h806539 : x ≤ 811539
  · exact psi_cell137_806539 (le_of_not_ge h801539) h806539
  by_cases h811539 : x ≤ 816539
  · exact psi_cell137_811539 (le_of_not_ge h806539) h811539
  exact psi_cell137_816539 (le_of_not_ge h811539) hu

/-- The signed Chebyshev bound on the entire squared cutoff for K197 cell 138. -/
public theorem psi_gaussian_k197_cell138 {x : ℝ} (hl : 817334 ≤ x) (hu : x ≤ 847262) :
    -154 ≤ Chebyshev.psi x - x := by
  by_cases h816539 : x ≤ 821539
  · exact psi_cell138_816539 hl h816539
  by_cases h821539 : x ≤ 826539
  · exact psi_cell138_821539 (le_of_not_ge h816539) h821539
  by_cases h826539 : x ≤ 831539
  · exact psi_cell138_826539 (le_of_not_ge h821539) h826539
  by_cases h831539 : x ≤ 836539
  · exact psi_cell138_831539 (le_of_not_ge h826539) h831539
  by_cases h836539 : x ≤ 841539
  · exact psi_cell138_836539 (le_of_not_ge h831539) h836539
  by_cases h841539 : x ≤ 846539
  · exact psi_cell138_841539 (le_of_not_ge h836539) h841539
  exact psi_cell138_846539 (le_of_not_ge h841539) hu

/-- The signed Chebyshev bound on the entire squared cutoff for K197 cell 139. -/
public theorem psi_gaussian_k197_cell139 {x : ℝ} (hl : 847704 ≤ x) (hu : x ≤ 878186) :
    -139 ≤ Chebyshev.psi x - x := by
  by_cases h846539 : x ≤ 851539
  · exact psi_cell139_846539 hl h846539
  by_cases h851539 : x ≤ 856539
  · exact psi_cell139_851539 (le_of_not_ge h846539) h851539
  by_cases h856539 : x ≤ 861539
  · exact psi_cell139_856539 (le_of_not_ge h851539) h856539
  by_cases h861539 : x ≤ 866539
  · exact psi_cell139_861539 (le_of_not_ge h856539) h861539
  by_cases h866539 : x ≤ 871539
  · exact psi_cell139_866539 (le_of_not_ge h861539) h866539
  by_cases h871539 : x ≤ 876539
  · exact psi_cell139_871539 (le_of_not_ge h866539) h871539
  exact psi_cell139_876539 (le_of_not_ge h871539) hu

/-- The signed Chebyshev bound on the entire squared cutoff for K197 cell 140. -/
public theorem psi_gaussian_k197_cell140 {x : ℝ} (hl : 878628 ≤ x) (hu : x ≤ 909664) :
    -119 ≤ Chebyshev.psi x - x := by
  by_cases h876539 : x ≤ 881539
  · exact psi_cell140_876539 hl h876539
  by_cases h881539 : x ≤ 886539
  · exact psi_cell140_881539 (le_of_not_ge h876539) h881539
  by_cases h886539 : x ≤ 891539
  · exact psi_cell140_886539 (le_of_not_ge h881539) h886539
  by_cases h891539 : x ≤ 896539
  · exact psi_cell140_891539 (le_of_not_ge h886539) h891539
  by_cases h896539 : x ≤ 901539
  · exact psi_cell140_896539 (le_of_not_ge h891539) h896539
  by_cases h901539 : x ≤ 906539
  · exact psi_cell140_901539 (le_of_not_ge h896539) h901539
  exact psi_cell140_906539 (le_of_not_ge h901539) hu

/-- The signed Chebyshev bound on the entire squared cutoff for K197 cell 141. -/
public theorem psi_gaussian_k197_cell141 {x : ℝ} (hl : 910106 ≤ x) (hu : x ≤ 941696) :
    0 ≤ Chebyshev.psi x - x := by
  by_cases h906539 : x ≤ 911539
  · exact psi_cell141_906539 hl h906539
  by_cases h911539 : x ≤ 916539
  · exact psi_cell141_911539 (le_of_not_ge h906539) h911539
  by_cases h916539 : x ≤ 921539
  · exact psi_cell141_916539 (le_of_not_ge h911539) h916539
  by_cases h921539 : x ≤ 926539
  · exact psi_cell141_921539 (le_of_not_ge h916539) h921539
  by_cases h926539 : x ≤ 931539
  · exact psi_cell141_926539 (le_of_not_ge h921539) h926539
  by_cases h931539 : x ≤ 936539
  · exact psi_cell141_931539 (le_of_not_ge h926539) h931539
  by_cases h936539 : x ≤ 941539
  · exact psi_cell141_936539 (le_of_not_ge h931539) h936539
  exact psi_cell141_941539 (le_of_not_ge h936539) hu

/-- The signed Chebyshev bound on the entire squared cutoff for K197 cell 142. -/
public theorem psi_gaussian_k197_cell142 {x : ℝ} (hl : 942138 ≤ x) (hu : x ≤ 974282) :
    -272 ≤ Chebyshev.psi x - x := by
  by_cases h941539 : x ≤ 946539
  · exact psi_cell142_941539 hl h941539
  by_cases h946539 : x ≤ 951539
  · exact psi_cell142_946539 (le_of_not_ge h941539) h946539
  by_cases h951539 : x ≤ 956539
  · exact psi_cell142_951539 (le_of_not_ge h946539) h951539
  by_cases h956539 : x ≤ 961539
  · exact psi_cell142_956539 (le_of_not_ge h951539) h956539
  by_cases h961539 : x ≤ 966539
  · exact psi_cell142_961539 (le_of_not_ge h956539) h961539
  by_cases h966539 : x ≤ 971539
  · exact psi_cell142_966539 (le_of_not_ge h961539) h966539
  exact psi_cell142_971539 (le_of_not_ge h966539) hu

/-- The signed Chebyshev bound on the entire squared cutoff for K197 cell 143. -/
public theorem psi_gaussian_k197_cell143 {x : ℝ} (hl : 974725 ≤ x) (hu : x ≤ 991007) :
    -483 ≤ Chebyshev.psi x - x := by
  by_cases h971539 : x ≤ 976539
  · exact psi_cell143_971539 hl h971539
  by_cases h976539 : x ≤ 981539
  · exact psi_cell143_976539 (le_of_not_ge h971539) h976539
  by_cases h981539 : x ≤ 986539
  · exact psi_cell143_981539 (le_of_not_ge h976539) h981539
  exact psi_cell143_986539 (le_of_not_ge h981539) hu

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

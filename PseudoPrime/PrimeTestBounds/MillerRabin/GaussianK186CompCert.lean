/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186CompCells
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCompCellCaps
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186CompCells
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensationPartition

/-! # Kernel-checked scalar caps for the K186 Abel compensation -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Outward-rounded main and variation caps, in order of the dyadic cells. -/
private def k186CertCells : List CompCellCap :=
  [⟨3983, 0, 0⟩, ⟨1, 21, 8590816⟩, ⟨4728, 345434065, 81232624199⟩, ⟨1, 3, 15177559⟩, ⟨5686, 0, 0⟩,
    ⟨1, 19, 6537294⟩, ⟨6383, 355653273, 41726449852⟩, ⟨1, 3, 5529494⟩, ⟨8048, 0, 0⟩,
    ⟨1, 5, 4477222⟩, ⟨7954, 239435281, 35610889237⟩, ⟨1, 2, 3634148⟩, ⟨21455, 0, 0⟩,
    ⟨1, 1, 2070249⟩, ⟨9201, 300468185, 57143566567⟩, ⟨1, 1, 4879042⟩, ⟨38399, 0, 0⟩,
    ⟨1, 2, 3564472⟩, ⟨9492, 569982329, 135332320524⟩, ⟨1, 1, 11115566⟩, ⟨27589, 0, 0⟩,
    ⟨1, 182, 117034190⟩, ⟨12183, 22342265284, 4586610871077⟩, ⟨1, 327, 273511381⟩, ⟨39522, 0, 0⟩,
    ⟨1, 557, 2012083717⟩, ⟨10056, 172955408957, 47800291893190⟩, ⟨1, 6353, 3652638269⟩,
    ⟨59016, 0, 0⟩, ⟨1, 121674, 158534767603⟩, ⟨36676, 225783939352161, 74598074243944206⟩,
    ⟨1, 683615, 777441378256⟩, ⟨223901, 0, 0⟩]

/-- Check the zero compensation charge at dyadic start 0. -/
private theorem k186_comp_cert_01 : CompCellCaps .k186 [⟨3983, 0, 0⟩] 0 := by
  exact k186_cell_zero_caps 0 3983 k186_first_sign

/-- Check the mean compensation charge at dyadic start 3983. -/
private theorem k186_comp_cert_02 : CompCellCaps .k186 [⟨1, 21, 8590816⟩] 3983 := by
  exact
    k186_comp_check_sound 3983 ⟨1, 21, 8590816⟩ 1 false (by decide) (by decide) (by decide +kernel)

/-- Check the signed compensation charge at dyadic start 3984. -/
private theorem k186_comp_cert_03 : CompCellCaps .k186 [⟨4728, 345434065, 81232624199⟩] 3984 := by
  exact
    k186_comp_check_sound 3984 ⟨4728, 345434065, 81232624199⟩ 2 true (by decide) (by decide)
      (by decide +kernel)

/-- Check the mean compensation charge at dyadic start 8712. -/
private theorem k186_comp_cert_04 : CompCellCaps .k186 [⟨1, 3, 15177559⟩] 8712 := by
  exact
    k186_comp_check_sound 8712 ⟨1, 3, 15177559⟩ 2 false (by decide) (by decide) (by decide +kernel)

/-- Check the zero compensation charge at dyadic start 8713. -/
private theorem k186_comp_cert_05 : CompCellCaps .k186 [⟨5686, 0, 0⟩] 8713 := by
  exact k186_cell_zero_caps 8713 5686 (by decide +kernel)

/-- Check the mean compensation charge at dyadic start 14399. -/
private theorem k186_comp_cert_06 : CompCellCaps .k186 [⟨1, 19, 6537294⟩] 14399 := by
  exact
    k186_comp_check_sound 14399 ⟨1, 19, 6537294⟩ 1 false (by decide) (by decide) (by decide +kernel)

/-- Check the signed compensation charge at dyadic start 14400. -/
private theorem k186_comp_cert_07 : CompCellCaps .k186 [⟨6383, 355653273, 41726449852⟩] 14400 := by
  exact
    k186_comp_check_sound 14400 ⟨6383, 355653273, 41726449852⟩ 1 true (by decide) (by decide)
      (by decide +kernel)

/-- Check the mean compensation charge at dyadic start 20783. -/
private theorem k186_comp_cert_08 : CompCellCaps .k186 [⟨1, 3, 5529494⟩] 20783 := by
  exact
    k186_comp_check_sound 20783 ⟨1, 3, 5529494⟩ 1 false (by decide) (by decide) (by decide +kernel)

/-- Check the zero compensation charge at dyadic start 20784. -/
private theorem k186_comp_cert_09 : CompCellCaps .k186 [⟨8048, 0, 0⟩] 20784 := by
  exact k186_cell_zero_caps 20784 8048 (by decide +kernel)

/-- Check the mean compensation charge at dyadic start 28832. -/
private theorem k186_comp_cert_10 : CompCellCaps .k186 [⟨1, 5, 4477222⟩] 28832 := by
  exact
    k186_comp_check_sound 28832 ⟨1, 5, 4477222⟩ 1 false (by decide) (by decide) (by decide +kernel)

/-- Check the signed compensation charge at dyadic start 28833. -/
private theorem k186_comp_cert_11 : CompCellCaps .k186 [⟨7954, 239435281, 35610889237⟩] 28833 := by
  exact
    k186_comp_check_sound 28833 ⟨7954, 239435281, 35610889237⟩ 1 true (by decide) (by decide)
      (by decide +kernel)

/-- Check the mean compensation charge at dyadic start 36787. -/
private theorem k186_comp_cert_12 : CompCellCaps .k186 [⟨1, 2, 3634148⟩] 36787 := by
  exact
    k186_comp_check_sound 36787 ⟨1, 2, 3634148⟩ 1 false (by decide) (by decide) (by decide +kernel)

/-- Check the zero compensation charge at dyadic start 36788. -/
private theorem k186_comp_cert_13 : CompCellCaps .k186 [⟨21455, 0, 0⟩] 36788 := by
  exact k186_cell_zero_caps 36788 21455 (by decide +kernel)

/-- Check the mean compensation charge at dyadic start 58243. -/
private theorem k186_comp_cert_14 : CompCellCaps .k186 [⟨1, 1, 2070249⟩] 58243 := by
  exact
    k186_comp_check_sound 58243 ⟨1, 1, 2070249⟩ 1 false (by decide) (by decide) (by decide +kernel)

/-- Check the signed compensation charge at dyadic start 58244. -/
private theorem k186_comp_cert_15 : CompCellCaps .k186 [⟨9201, 300468185, 57143566567⟩] 58244 := by
  exact
    k186_comp_check_sound 58244 ⟨9201, 300468185, 57143566567⟩ 3 true (by decide) (by decide)
      (by decide +kernel)

/-- Check the mean compensation charge at dyadic start 67445. -/
private theorem k186_comp_cert_16 : CompCellCaps .k186 [⟨1, 1, 4879042⟩] 67445 := by
  exact
    k186_comp_check_sound 67445 ⟨1, 1, 4879042⟩ 3 false (by decide) (by decide) (by decide +kernel)

/-- Check the zero compensation charge at dyadic start 67446. -/
private theorem k186_comp_cert_17 : CompCellCaps .k186 [⟨38399, 0, 0⟩] 67446 := by
  exact k186_cell_zero_caps 67446 38399 (by decide +kernel)

/-- Check the mean compensation charge at dyadic start 105845. -/
private theorem k186_comp_cert_18 : CompCellCaps .k186 [⟨1, 2, 3564472⟩] 105845 := by
  exact
    k186_comp_check_sound 105845 ⟨1, 2, 3564472⟩ 6 false (by decide) (by decide) (by decide +kernel)

/-- Check the signed compensation charge at dyadic start 105846. -/
private theorem k186_comp_cert_19 :
    CompCellCaps .k186 [⟨9492, 569982329, 135332320524⟩] 105846 := by
  exact
    k186_comp_check_sound 105846 ⟨9492, 569982329, 135332320524⟩ 24 true (by decide) (by decide)
      (by decide +kernel)

/-- Check the mean compensation charge at dyadic start 115338. -/
private theorem k186_comp_cert_20 : CompCellCaps .k186 [⟨1, 1, 11115566⟩] 115338 := by
  exact
    k186_comp_check_sound 115338 ⟨1, 1, 11115566⟩ 24 false (by decide) (by decide)
      (by decide +kernel)

/-- Check the zero compensation charge at dyadic start 115339. -/
private theorem k186_comp_cert_21 : CompCellCaps .k186 [⟨27589, 0, 0⟩] 115339 := by
  exact k186_cell_zero_caps 115339 27589 (by decide +kernel)

/-- Check the mean compensation charge at dyadic start 142928. -/
private theorem k186_comp_cert_22 : CompCellCaps .k186 [⟨1, 182, 117034190⟩] 142928 := by
  exact
    k186_comp_check_sound 142928 ⟨1, 182, 117034190⟩ 521 false (by decide) (by decide)
      (by decide +kernel)

/-- Check the signed compensation charge at dyadic start 142929. -/
private theorem k186_comp_cert_23 :
    CompCellCaps .k186 [⟨12183, 22342265284, 4586610871077⟩] 142929 := by
  exact
    k186_comp_check_sound 142929 ⟨12183, 22342265284, 4586610871077⟩ 1676 true (by decide)
      (by decide) (by decide +kernel)

/-- Check the mean compensation charge at dyadic start 155112. -/
private theorem k186_comp_cert_24 : CompCellCaps .k186 [⟨1, 327, 273511381⟩] 155112 := by
  exact
    k186_comp_check_sound 155112 ⟨1, 327, 273511381⟩ 1676 false (by decide) (by decide)
      (by decide +kernel)

/-- Check the zero compensation charge at dyadic start 155113. -/
private theorem k186_comp_cert_25 : CompCellCaps .k186 [⟨39522, 0, 0⟩] 155113 := by
  exact k186_cell_zero_caps 155113 39522 (by decide +kernel)

/-- Check the mean compensation charge at dyadic start 194635. -/
private theorem k186_comp_cert_26 : CompCellCaps .k186 [⟨1, 557, 2012083717⟩] 194635 := by
  exact
    k186_comp_check_sound 194635 ⟨1, 557, 2012083717⟩ 34762 false (by decide) (by decide)
      (by decide +kernel)

/-- Check the signed compensation charge at dyadic start 194636. -/
private theorem k186_comp_cert_27 :
    CompCellCaps .k186 [⟨10056, 172955408957, 47800291893190⟩] 194636 := by
  exact
    k186_comp_check_sound 194636 ⟨10056, 172955408957, 47800291893190⟩ 82125 true (by decide)
      (by decide) (by decide +kernel)

/-- Check the mean compensation charge at dyadic start 204692. -/
private theorem k186_comp_cert_28 : CompCellCaps .k186 [⟨1, 6353, 3652638269⟩] 204692 := by
  exact
    k186_comp_check_sound 204692 ⟨1, 6353, 3652638269⟩ 82151 false (by decide) (by decide)
      (by decide +kernel)

/-- Check the zero compensation charge at dyadic start 204693. -/
private theorem k186_comp_cert_29 : CompCellCaps .k186 [⟨59016, 0, 0⟩] 204693 := by
  exact k186_cell_zero_caps 204693 59016 (by decide +kernel)

/-- Check the mean compensation charge at dyadic start 263709. -/
private theorem k186_comp_cert_30 : CompCellCaps .k186 [⟨1, 121674, 158534767603⟩] 263709 := by
  exact
    k186_comp_check_sound 263709 ⟨1, 121674, 158534767603⟩ 16761932 false (by decide) (by decide)
      (by decide +kernel)

/-- Check the signed compensation charge at dyadic start 263710. -/
private theorem k186_comp_cert_31 :
    CompCellCaps .k186 [⟨36676, 225783939352161, 74598074243944206⟩] 263710 := by
  exact
    k186_comp_check_sound 263710 ⟨36676, 225783939352161, 74598074243944206⟩ 215058492 true
      (by decide) (by decide) (by decide +kernel)

/-- Check the mean compensation charge at dyadic start 300386. -/
private theorem k186_comp_cert_32 : CompCellCaps .k186 [⟨1, 683615, 777441378256⟩] 300386 := by
  exact
    k186_comp_check_sound 300386 ⟨1, 683615, 777441378256⟩ 215085858 false (by decide) (by decide)
      (by decide +kernel)

/-- Check the zero compensation charge at dyadic start 300387. -/
private theorem k186_comp_cert_33 : CompCellCaps .k186 [⟨223901, 0, 0⟩] 300387 := by
  exact k186_cell_zero_caps 300387 223901 (by decide +kernel)

/-- Attach an accepted cell to an accepted tail beginning at its right endpoint. -/
private theorem join_comp_cells {c : CompCellCap} {cs : List CompCellCap} {i : ℕ}
    (h : CompCellCaps .k186 [c] i) (ht : CompCellCaps .k186 cs (i + c.width)) :
    CompCellCaps .k186 (c :: cs) i :=
  ⟨h.1, h.2.1, ht⟩

/-- Assemble the checked list with a proof at each consecutive cell. -/
private theorem k186_cert_cells_valid : CompCellCaps .k186 k186CertCells 0 := by
  unfold k186CertCells
  exact
    join_comp_cells k186_comp_cert_01
      (join_comp_cells k186_comp_cert_02
        (join_comp_cells k186_comp_cert_03
          (join_comp_cells k186_comp_cert_04
            (join_comp_cells k186_comp_cert_05
              (join_comp_cells k186_comp_cert_06
                (join_comp_cells k186_comp_cert_07
                  (join_comp_cells k186_comp_cert_08
                    (join_comp_cells k186_comp_cert_09
                      (join_comp_cells k186_comp_cert_10
                        (join_comp_cells k186_comp_cert_11
                          (join_comp_cells k186_comp_cert_12
                            (join_comp_cells k186_comp_cert_13
                              (join_comp_cells k186_comp_cert_14
                                (join_comp_cells k186_comp_cert_15
                                  (join_comp_cells k186_comp_cert_16
                                    (join_comp_cells k186_comp_cert_17
                                      (join_comp_cells k186_comp_cert_18
                                        (join_comp_cells k186_comp_cert_19
                                          (join_comp_cells k186_comp_cert_20
                                            (join_comp_cells k186_comp_cert_21
                                              (join_comp_cells k186_comp_cert_22
                                                (join_comp_cells k186_comp_cert_23
                                                  (join_comp_cells k186_comp_cert_24
                                                    (join_comp_cells k186_comp_cert_25
                                                      (join_comp_cells k186_comp_cert_26
                                                        (join_comp_cells k186_comp_cert_27
                                                          (join_comp_cells k186_comp_cert_28
                                                            (join_comp_cells k186_comp_cert_29
                                                              (join_comp_cells k186_comp_cert_30
                                                                (join_comp_cells k186_comp_cert_31
                                                                  (join_comp_cells k186_comp_cert_32
                                                                    (join_comp_cells
                                                                      k186_comp_cert_33
                                                                      True.intro))))))))))))))))))))))))))))))))

/-- The certified main and variation compensation integrals fit the K186
far comparison's two scalar budgets. -/
public theorem k186_comp_cert_caps :
    highCompensationMain .k186 ≤ (225981048812301 : ℝ) / 10 ^ 20 ∧
      highCompensationVariation .k186 ≤ (74651754289548130 : ℝ) / 10 ^ 20 := by
  have h := comp_integrals_of_cells .k186 k186CertCells (by decide +kernel) k186_cert_cells_valid
  have hm : (k186CertCells.map CompCellCap.main).sum = 225981048812301 := by decide +kernel
  have hv : (k186CertCells.map CompCellCap.variation).sum = 74651754289548130 := by decide +kernel
  simpa only [hm, hv, Int.cast_ofNat] using h

end PseudoPrime.PrimeTestBounds.MillerRabin

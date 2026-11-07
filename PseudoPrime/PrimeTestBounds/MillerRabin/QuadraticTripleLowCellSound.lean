/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleLowCells

/-! # Soundness of a low triple bridge cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked low-bridge cell bounds a rejecting prime by `3 log(n)^2 / 10`
for an ordered uniform Korselt triple with smallest prime at least five. The
endpoint budgets bound the shifted even radius, and the squared radius slope
is below `3/10`. This is the per-cell step of the low-range cover. -/
theorem LowBridgeCell.sound (c : LowBridgeCell) (hc : c.check = true) {n p q r : ℕ} (hn : 1 < n)
    (ho : Odd n) (hnp : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpO : Odd p)
    (hqO : Odd q) (hrO : Odd r) (hpq : p < q) (hqr : q < r) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp5 : 5 ≤ (p : ℝ))
    (hU : Real.log n ≤ 988 / 25) (hlo : (c.lo : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (c.hi : ℝ)) :
    ∃ a : ℕ,
      a.Prime ∧
        (a : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (a : ZMod n) := by
  have hpairs := Bool.and_eq_true_iff.mp hc
  have htest := hpairs.1
  have hbudget := of_decide_eq_true hpairs.2
  have hbq : (8 : ℚ) ≤ c.radius := (of_decide_eq_true htest).1
  have hb : (8 : ℝ) ≤ c.radius := by exact_mod_cast hbq
  have hd0 := localCorrectionCheck_sound htest
  have hd : (c.correction : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection c.radius := by
    norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hd0
    linarith only [hd0]
  have hbr : (c.radius : ℝ) ≤ (10954451 / 20000000 : ℝ) * c.lo := by
    have h := (Rat.cast_le (K := ℝ)).mpr hbudget.1
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using h
  have hdr : (2 / 3 - 10954451 / 20000000 : ℝ) * c.hi ≤ (c.correction : ℝ) + 54753 / 30000000 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hbudget.2
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_sub, Rat.cast_add] using h
  obtain ⟨a, ha, hab, haf⟩ :=
    uniformKorselt_reject_low_shift hn ho hnp hp hq hr hpO hqO hrO hpq hqr hu hGRH hp5 hU hb hd
  have hm1 : (c.radius : ℝ) ≤ (10954451 / 20000000 : ℝ) * Real.log n := by
    have h := mul_le_mul_of_nonneg_left hlo (by norm_num only : (0 : ℝ) ≤ 10954451 / 20000000)
    linarith only [hbr, h]
  have hm2 :
    (2 / 3 : ℝ) * Real.log n - 54753 / 30000000 - c.correction ≤
      (10954451 / 20000000 : ℝ) * Real.log n := by
    have h :=
      mul_le_mul_of_nonneg_left hhi (by norm_num only : (0 : ℝ) ≤ 2 / 3 - 10954451 / 20000000)
    linarith only [hdr, h]
  have hmax := max_le hm1 hm2
  have hnonneg :
    0 ≤ max (c.radius : ℝ) ((2 / 3 : ℝ) * Real.log n - 54753 / 30000000 - c.correction) :=
    (by linarith only [hb] : 0 ≤ (c.radius : ℝ)).trans (le_max_left _ _)
  have hsq := mul_self_le_mul_self hnonneg hmax
  have hLsq := sq_nonneg (Real.log n)
  have hfinal :
    (max (c.radius : ℝ) ((2 / 3 : ℝ) * Real.log n - 54753 / 30000000 - c.correction)) ^ 2 ≤
      (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
    nlinarith only [hsq, hLsq]
  exact ⟨a, ha, hab.trans hfinal, haf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin

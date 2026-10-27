/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeightRatioPowerBounds

/-! # Finite adjacent layers for canonical heights -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- A value between two endpoint cutoffs lies in one adjacent half-open layer.
This finite interval interface converts endpoint bounds into the cover required
by `height_tail_weight_sum_le_layers`, without assuming that intermediate
cutoffs are monotone. -/
theorem exists_adjacent_nat_layer {f : ℕ → ℕ} {lo hi x : ℕ} (hlo : lo ≤ hi) (hbot : f hi < x)
    (htop : x ≤ f lo) : ∃ j, lo ≤ j ∧ j < hi ∧ f (j + 1) < x ∧ x ≤ f j := by
  induction hi generalizing lo x with
  | zero =>
    have hlo0 : lo = 0 := Nat.eq_zero_of_le_zero hlo
    rw [hlo0] at htop
    exact False.elim ((Nat.not_lt_of_ge htop) hbot)
  | succ n ih =>
    by_cases htopn : x ≤ f n
    · have hne : lo ≠ n + 1 := by
        intro heq
        subst lo
        exact (Nat.not_lt_of_ge htop) hbot
      have hlo' : lo ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hlo hne)
      exact ⟨n, hlo', Nat.lt_succ_self n, hbot, htopn⟩
    · have hmid : f n < x := Nat.lt_of_not_ge htopn
      have hne : lo ≠ n + 1 := by
        intro heq
        subst lo
        exact (Nat.not_lt_of_ge htop) hbot
      have hlo' : lo ≤ n := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hlo hne)
      obtain ⟨j, hlow, hlt, hbot', htop'⟩ := ih hlo' hmid htop
      exact ⟨j, hlow, Nat.lt_succ_of_lt hlt, hbot', htop'⟩

/-- The shifted power cutoff `floor(p^(1/j - theta))` used as the upper height
of the degree-j product-growth layer. The shift keeps every degree-j cutoff
strictly below `p^(1/j)`, leaving room in the short-modulus hypothesis. -/
noncomputable def shiftedHeightCutoff (p : ℕ) (theta : ℝ) (j : ℕ) : ℕ :=
  Nat.floor ((p : ℝ) ^ (1 / (j : ℝ) - theta))

/-- The natural cutoff lies below its defining real power. This is the upper
endpoint estimate used in each degree-specific product-growth hypothesis. -/
theorem shiftedHeightCutoff_cast_le {p j : ℕ} {theta : ℝ} :
    (shiftedHeightCutoff p theta j : ℝ) ≤ (p : ℝ) ^ (1 / (j : ℝ) - theta) := by
  unfold shiftedHeightCutoff
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg p) _)

/-- The next integer above the cutoff lies strictly above the defining real
power. This is the denominator lower bound for the adjacent layer. -/
theorem shiftedHeightCutoff_add_one_cast_gt {p j : ℕ} {theta : ℝ} :
    (p : ℝ) ^ (1 / (j : ℝ) - theta) < ((shiftedHeightCutoff p theta j + 1 : ℕ) : ℝ) := by
  unfold shiftedHeightCutoff
  simpa only [Nat.cast_add, Nat.cast_one] using
    (Nat.lt_floor_add_one ((p : ℝ) ^ (1 / (j : ℝ) - theta)))

/-- If the shifted exponent is positive and p>1, its natural floor cutoff is
positive. This makes the degree-j ratio-growth estimate applicable to a layer. -/
theorem shiftedHeightCutoff_pos {p j : ℕ} {theta : ℝ} (hp : 1 < p) (htheta : theta < 1 / (j : ℝ)) :
    0 < shiftedHeightCutoff p theta j := by
  rw [shiftedHeightCutoff, Nat.floor_pos]
  have hpR : (1 : ℝ) < (p : ℝ) := by simpa only [Nat.cast_one] using (Nat.cast_lt.mpr hp)
  exact (Real.one_lt_rpow hpR (sub_pos.mpr htheta)).le

/-- The degree-j cutoff is strictly below p^(1/j), so its j-th natural power
is less than p. The positive shift creates the strict margin for the subgroup
product-set injectivity hypothesis. -/
theorem shiftedHeightCutoff_pow_lt {p j : ℕ} {theta : ℝ} (hp : 1 < p) (hj : 0 < j)
    (htheta0 : 0 < theta) : shiftedHeightCutoff p theta j ^ j < p := by
  have hInv : (1 / (j : ℝ)) * (j : ℝ) = 1 := one_div_mul_cancel (Nat.cast_ne_zero.mpr (ne_of_gt hj))
  have hexp : (1 / (j : ℝ) - theta) * (j : ℝ) < 1 := by
    rw [sub_mul, hInv]
    exact sub_lt_self 1 (mul_pos htheta0 (Nat.cast_pos.mpr hj))
  have hpR : (1 : ℝ) < (p : ℝ) := by simpa only [Nat.cast_one] using (Nat.cast_lt.mpr hp)
  have hpowReal : ((p : ℝ) ^ (1 / (j : ℝ) - theta)) ^ j < (p : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p) (1 / (j : ℝ) - theta) j]
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hpR hexp
  have hcutR : (shiftedHeightCutoff p theta j : ℝ) ≤ (p : ℝ) ^ (1 / (j : ℝ) - theta) :=
    shiftedHeightCutoff_cast_le
  have hpowLe : (shiftedHeightCutoff p theta j : ℝ) ^ j ≤ ((p : ℝ) ^ (1 / (j : ℝ) - theta)) ^ j :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hcutR j
  have hnatCast : (shiftedHeightCutoff p theta j : ℝ) ^ j < (p : ℝ) := hpowLe.trans_lt hpowReal
  have hcast : ((shiftedHeightCutoff p theta j ^ j : ℕ) : ℝ) < (p : ℝ) := by
    rw [Nat.cast_pow]
    exact hnatCast
  exact Nat.cast_lt.mp hcast

/-- The cutoff satisfies the degree-j short-modulus condition required by the
restricted ratio-set product-growth estimate. -/
theorem shiftedHeightCutoff_modulus {p j : ℕ} {theta : ℝ} (hp : 1 < p) (hj : 0 < j)
    (htheta0 : 0 < theta) : shiftedHeightCutoff p theta j ^ (2 * j) < p ^ 2 := by
  have hpow := shiftedHeightCutoff_pow_lt hp hj htheta0
  have hsquare : (shiftedHeightCutoff p theta j ^ j) ^ 2 < p ^ 2 :=
    (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mpr hpow
  rw [Nat.mul_comm 2 j, pow_mul]
  exact hsquare

/-- Apply the uniform small-power ratio estimate at a shifted cutoff. The
cutoff positivity and short-modulus hypotheses are discharged by the preceding
cutoff lemmas, leaving only the degree and exponent parameters. -/
theorem exists_shiftedHeight_ratio_small_power_bound {p H j : ℕ} [Fact p.Prime] {theta δ : ℝ}
    (hj : 0 < j) (hδ : 0 < δ) (htheta0 : 0 < theta) (htheta : theta < 1 / (j : ℝ)) (hHp : H < p) :
    ∃ C : ℝ,
      0 < C ∧
        ((heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card : ℝ) ≤
          C * (shiftedHeightCutoff p theta j : ℝ) ^ δ * (p : ℝ) ^ (1 / (j : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_height_ratio_small_power_bound (m := j) hj hδ
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  refine ⟨C, hC, ?_⟩
  apply hbound
  · exact hHp
  · exact shiftedHeightCutoff_pos hp1 htheta
  · exact shiftedHeightCutoff_modulus hp1 hj htheta0

/-- At a shifted degree-j cutoff, the exact integer product-growth estimate
applies to every restricted ratio layer. -/
theorem shiftedHeightCutoff_ratio_power_growth_bound {p H j n : ℕ} [Fact p.Prime] {theta : ℝ}
    (hHp : H < p) (hj : 0 < j) (hn : 0 < n) (htheta0 : 0 < theta) (htheta : theta < 1 / (j : ℝ)) :
    (heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card ^ (n * j) ≤
      quotientPowerConstant (shiftedHeightCutoff p theta j ^ (2 * j)) ^ (n ^ 2 * (j - 1)) *
        shiftedHeightCutoff p theta j ^ ((j - 1) * j) *
        (p - 1) ^ n := by
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  exact
    heightRestrictedRatioSet_power_growth_bound hHp (shiftedHeightCutoff_pos hp1 htheta) hj hn
      (shiftedHeightCutoff_modulus hp1 hj htheta0)

/-- The geometric loss between adjacent degree-j layers is at most 1/42 for
j≥6. A shift theta and the small ratio-count loss delta fit within eta when
theta + delta/6 ≤ eta. -/
theorem shiftedHeightLayer_exponent_le {j : ℕ} {theta delta eta : ℝ} (hj : 6 ≤ j)
    (hdelta : 0 ≤ delta) (hbudget : theta + delta / 6 ≤ eta) :
    1 / (j : ℝ) + delta / (j : ℝ) - (1 / ((j + 1 : ℕ) : ℝ) - theta) ≤ 1 / 42 + eta := by
  have hjR : (6 : ℝ) ≤ (j : ℝ) := by simpa only [Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hj
  have hjpos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by decide : 0 < 6) hj)
  have hj1pos : (0 : ℝ) < (j + 1 : ℕ) := by exact_mod_cast Nat.succ_pos j
  have hj1cast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by simp only [Nat.cast_add, Nat.cast_one]
  have hprod : (42 : ℝ) ≤ (j : ℝ) * ((j + 1 : ℕ) : ℝ) := by
    rw [hj1cast]
    nlinarith only [hjR]
  have hgap : 1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ) = 1 / ((j : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
    rw [← inv_eq_one_div, ← inv_eq_one_div]
    rw [inv_sub_inv (ne_of_gt hjpos) (ne_of_gt hj1pos), hj1cast]
    ring
  have hgeom : 1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ) ≤ 1 / 42 := by
    rw [hgap]
    exact one_div_le_one_div_of_le (by norm_num only) hprod
  have hdelta' : delta / (j : ℝ) ≤ delta / 6 :=
    div_le_div_of_nonneg_left hdelta (by norm_num only) hjR
  have hthetaDelta : theta + delta / (j : ℝ) ≤ theta + delta / 6 := by
    simpa only [add_comm] using add_le_add_right hdelta' theta
  calc
    _ = (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ)) + (theta + delta / (j : ℝ)) := by ring
    _ ≤ 1 / 42 + (theta + delta / 6) := add_le_add hgeom hthetaDelta
    _ ≤ 1 / 42 + eta := by simpa only [add_comm] using add_le_add_left hbudget (1 / 42)

/-- Raising a shifted degree-j cutoff to a nonnegative exponent delta costs at
most p^(delta/j). -/
theorem shiftedHeightCutoff_rpow_delta_le {p j : ℕ} {theta delta : ℝ} (hp : 1 < p) (hj : 0 < j)
    (hdelta : 0 ≤ delta) (htheta0 : 0 < theta) :
    (shiftedHeightCutoff p theta j : ℝ) ^ delta ≤ (p : ℝ) ^ (delta / (j : ℝ)) := by
  have hjR : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj
  have hcutR : (shiftedHeightCutoff p theta j : ℝ) ≤ (p : ℝ) ^ (1 / (j : ℝ) - theta) :=
    shiftedHeightCutoff_cast_le
  have hcutpow := Real.rpow_le_rpow (Nat.cast_nonneg _) hcutR hdelta
  have hdiv : (1 / (j : ℝ)) * delta = delta / (j : ℝ) := by
    rw [div_eq_mul_inv]
    ring
  have hexp : (1 / (j : ℝ) - theta) * delta ≤ delta / (j : ℝ) := by
    rw [← hdiv]
    exact mul_le_mul_of_nonneg_right (sub_le_self _ htheta0.le) hdelta
  have hppow : (p : ℝ) ^ ((1 / (j : ℝ) - theta) * delta) ≤ (p : ℝ) ^ (delta / (j : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hp.le) hexp
  calc
    _ ≤ ((p : ℝ) ^ (1 / (j : ℝ) - theta)) ^ delta := hcutpow
    _ = (p : ℝ) ^ ((1 / (j : ℝ) - theta) * delta) := (Real.rpow_mul (Nat.cast_nonneg p) _ _).symm
    _ ≤ (p : ℝ) ^ (delta / (j : ℝ)) := hppow

/-- Bound one shifted layer's weighted ratio contribution by the common target
exponent, assuming its degree-j ratio estimate and the corresponding exponent
budget. This is the local estimate summed over degrees 6 through 41. -/
theorem shiftedHeightLayer_weighted_term_le {p H j : ℕ} [Fact p.Prime] {theta delta eta C : ℝ}
    (hp : 1 < p) (hj : 6 ≤ j) (hdelta : 0 ≤ delta) (htheta0 : 0 < theta) (hC : 0 ≤ C)
    (hcard :
      ((heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card : ℝ) ≤
        C * (shiftedHeightCutoff p theta j : ℝ) ^ delta * (p : ℝ) ^ (1 / (j : ℝ)))
    (hExp : 1 / (j : ℝ) + delta / (j : ℝ) - (1 / ((j + 1 : ℕ) : ℝ) - theta) ≤ 1 / 42 + eta) :
    ((heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card : ℝ) *
        (H / (shiftedHeightCutoff p theta (j + 1) + 1) : ℕ) ≤
      C * H * (p : ℝ) ^ (1 / 42 + eta) := by
  have hjpos : 0 < j := Nat.lt_of_lt_of_le (by decide : 0 < 6) hj
  have hp0 : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Fact.out : Nat.Prime p).pos
  have hcutpow := shiftedHeightCutoff_rpow_delta_le hp hjpos hdelta htheta0
  let alpha : ℝ := 1 / ((j + 1 : ℕ) : ℝ) - theta
  let d : ℕ := shiftedHeightCutoff p theta (j + 1) + 1
  have hden : (p : ℝ) ^ alpha < (d : ℝ) := by
    simpa only [alpha, d] using
      shiftedHeightCutoff_add_one_cast_gt (p := p) (j := j + 1) (theta := theta)
  have hcastdiv : ((H / d : ℕ) : ℝ) ≤ (H : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hdivden : (H : ℝ) / (d : ℝ) ≤ (H : ℝ) / (p : ℝ) ^ alpha :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg H) (Real.rpow_pos_of_pos hp0 alpha) (le_of_lt hden)
  have hweight : ((H / d : ℕ) : ℝ) ≤ (H : ℝ) / (p : ℝ) ^ alpha := hcastdiv.trans hdivden
  have hfactor_nonneg :
    0 ≤ C * (shiftedHeightCutoff p theta j : ℝ) ^ delta * (p : ℝ) ^ (1 / (j : ℝ)) :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) delta))
      (Real.rpow_nonneg (Nat.cast_nonneg p) (1 / (j : ℝ)))
  have hcount :
    ((heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card : ℝ) * ((H / d : ℕ) : ℝ) ≤
      (C * (shiftedHeightCutoff p theta j : ℝ) ^ delta * (p : ℝ) ^ (1 / (j : ℝ))) *
        ((H : ℝ) / (p : ℝ) ^ alpha) :=
    mul_le_mul hcard hweight (Nat.cast_nonneg _) hfactor_nonneg
  have hcutpow' : (shiftedHeightCutoff p theta j : ℝ) ^ delta ≤ (p : ℝ) ^ (delta / (j : ℝ)) :=
    hcutpow
  have hratio : (H : ℝ) / (p : ℝ) ^ alpha = (H : ℝ) * (p : ℝ) ^ (-alpha) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg p)]
  have hExp' : delta / (j : ℝ) + 1 / (j : ℝ) - alpha ≤ 1 / 42 + eta := by
    dsimp only [alpha]
    linarith only [hExp]
  calc
    _ ≤
        (C * (shiftedHeightCutoff p theta j : ℝ) ^ delta * (p : ℝ) ^ (1 / (j : ℝ))) *
          ((H : ℝ) / (p : ℝ) ^ alpha) :=
      hcount
    _ ≤ (C * (p : ℝ) ^ (delta / (j : ℝ)) * (p : ℝ) ^ (1 / (j : ℝ))) * ((H : ℝ) / (p : ℝ) ^ alpha) :=
      by
      have hA := mul_le_mul_of_nonneg_left hcutpow' hC
      have hB := mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (Nat.cast_nonneg p) (1 / (j : ℝ)))
      have hC' :=
        mul_le_mul_of_nonneg_right hB
          (div_nonneg (Nat.cast_nonneg H) (Real.rpow_nonneg (Nat.cast_nonneg p) alpha))
      simpa only [mul_assoc] using hC'
    _ = C * H * (p : ℝ) ^ (delta / (j : ℝ) + 1 / (j : ℝ) - alpha) := by
      rw [hratio]
      calc
        _ = C * H * ((p : ℝ) ^ (delta / (j : ℝ)) * (p : ℝ) ^ (1 / (j : ℝ)) * (p : ℝ) ^ (-alpha)) :=
          by ring
        _ = C * H * (p : ℝ) ^ (delta / (j : ℝ) + 1 / (j : ℝ) - alpha) := by
          rw [← Real.rpow_add hp0 (delta / (j : ℝ)) (1 / (j : ℝ))]
          rw [sub_eq_add_neg, ← Real.rpow_add hp0 (delta / (j : ℝ) + 1 / (j : ℝ)) (-alpha)]
    _ ≤ C * H * (p : ℝ) ^ (1 / 42 + eta) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hp.le) hExp')
        (mul_nonneg hC (Nat.cast_nonneg H))

/-- Sum the degree-specific weighted bounds over all 36 layers. Once each
layer has its own ratio-count constant, the exponent budget makes every term
share the same factor H*p^(1/42+eta); the constants then add. -/
theorem shiftedHeightLayers_weighted_sum_le {p H : ℕ} [Fact p.Prime] {theta delta eta : ℝ}
    (hdelta : 0 ≤ delta) (htheta0 : 0 < theta) (hbudget : theta + delta / 6 ≤ eta) (C : ℕ → ℝ)
    (hC : ∀ j ∈ Finset.Icc 6 41, 0 ≤ C j)
    (hcard :
      ∀ j ∈ Finset.Icc 6 41,
        ((heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card : ℝ) ≤
          C j * (shiftedHeightCutoff p theta j : ℝ) ^ delta * (p : ℝ) ^ (1 / (j : ℝ))) :
    ∑ j ∈ Finset.Icc 6 41,
        ((heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card : ℝ) *
          (H / (shiftedHeightCutoff p theta (j + 1) + 1) : ℕ) ≤
      (∑ j ∈ Finset.Icc 6 41, C j) * H * (p : ℝ) ^ (1 / 42 + eta) := by
  have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hterm :
    ∀ j ∈ Finset.Icc 6 41,
      ((heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card : ℝ) *
          (H / (shiftedHeightCutoff p theta (j + 1) + 1) : ℕ) ≤
        C j * H * (p : ℝ) ^ (1 / 42 + eta) := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    exact
      shiftedHeightLayer_weighted_term_le hp hj'.1 hdelta htheta0 (hC j hj) (hcard j hj)
        (shiftedHeightLayer_exponent_le hj'.1 hdelta hbudget)
  have hsum := Finset.sum_le_sum hterm
  calc
    _ ≤ ∑ j ∈ Finset.Icc 6 41, C j * H * (p : ℝ) ^ (1 / 42 + eta) := hsum
    _ = (∑ j ∈ Finset.Icc 6 41, C j) * H * (p : ℝ) ^ (1 / 42 + eta) := by
      rw [← Finset.sum_mul]
      rw [← Finset.sum_mul]

/-- The uniform small-power ratio estimates supply one constant per degree,
independent of p and H. Combining these finitely many constants gives the
height-layer bound with exponent 1/42+eta. -/
theorem exists_uniform_shiftedHeightLayers_weighted_sum_bound {p H : ℕ} [Fact p.Prime]
    {theta delta eta : ℝ} (hp : 1 < p) (hHp : H < p) (hdelta : 0 < delta) (htheta0 : 0 < theta)
    (htheta : theta < 1 / 42) (hbudget : theta + delta / 6 ≤ eta) :
    ∃ C : ℝ,
      0 < C ∧
        ∑ j ∈ Finset.Icc 6 41,
            ((heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card : ℝ) *
              (H / (shiftedHeightCutoff p theta (j + 1) + 1) : ℕ) ≤
          C * H * (p : ℝ) ^ (1 / 42 + eta) := by
  have hUniform :
    ∀ (j : ℕ),
      j ∈ Finset.Icc 6 41 →
        ∃ Cj : ℝ,
          0 < Cj ∧
            ∀ (p' H' T : ℕ) [Fact p'.Prime],
              H' < p' →
                0 < T →
                T ^ (2 * j) < p' ^ 2 →
                ((heightRestrictedRatioSet p' H' T).card : ℝ) ≤
                  Cj * (T : ℝ) ^ delta * (p' : ℝ) ^ (1 / (j : ℝ)) := by
    intro j hj
    have hjpos : 0 < j := Nat.lt_of_lt_of_le (by decide : 0 < 6) (Finset.mem_Icc.mp hj).1
    exact exists_uniform_height_ratio_small_power_bound hjpos hdelta
  let layerConst : ℕ → ℝ := fun j =>
    if hj : j ∈ Finset.Icc 6 41 then Classical.choose (hUniform j hj) else 1
  have hspec :
    ∀ (j : ℕ),
      j ∈ Finset.Icc 6 41 →
        0 < layerConst j ∧
          ((heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card : ℝ) ≤
            layerConst j * (shiftedHeightCutoff p theta j : ℝ) ^ delta *
              (p : ℝ) ^ (1 / (j : ℝ)) := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have hjpos : 0 < j := Nat.lt_of_lt_of_le (by decide : 0 < 6) hj'.1
    have hjCast : (j : ℝ) ≤ 41 := Nat.cast_le.mpr hj'.2
    have hinv : (1 : ℝ) / 41 ≤ 1 / (j : ℝ) :=
      one_div_le_one_div_of_le (Nat.cast_pos.mpr hjpos) hjCast
    have hsmall : (1 : ℝ) / 42 < 1 / 41 := by norm_num only
    have htheta_j : theta < 1 / (j : ℝ) := lt_trans htheta (hsmall.trans_le hinv)
    have hU := Classical.choose_spec (hUniform j hj)
    have hcutpos := shiftedHeightCutoff_pos hp htheta_j
    have hmod := shiftedHeightCutoff_modulus hp hjpos htheta0
    have hconst : layerConst j = Classical.choose (hUniform j hj) := by
      dsimp only [layerConst]
      exact dite_eq_left hj
    rw [hconst]
    exact ⟨hU.1, hU.2 p H (shiftedHeightCutoff p theta j) hHp hcutpos hmod⟩
  have hsum :=
    shiftedHeightLayers_weighted_sum_le hdelta.le htheta0 hbudget layerConst
      (fun j hj ↦ (hspec j hj).1.le) (fun j hj ↦ (hspec j hj).2)
  let K : ℝ := ∑ j ∈ Finset.Icc 6 41, layerConst j
  have hKnonneg : 0 ≤ K := Finset.sum_nonneg fun j hj ↦ (hspec j hj).1.le
  have hKle : K ≤ K + 1 := le_add_of_nonneg_right (by norm_num only : (0 : ℝ) ≤ 1)
  have hBnonneg : 0 ≤ (H : ℝ) * (p : ℝ) ^ (1 / 42 + eta) :=
    mul_nonneg (Nat.cast_nonneg H) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  refine ⟨K + 1, add_pos_of_nonneg_of_pos hKnonneg (by norm_num only : (0 : ℝ) < 1), ?_⟩
  calc
    _ ≤ K * H * (p : ℝ) ^ (1 / 42 + eta) := by simpa only [K] using hsum
    _ ≤ (K + 1) * H * (p : ℝ) ^ (1 / 42 + eta) := by
      calc
        _ = K * ((H : ℝ) * (p : ℝ) ^ (1 / 42 + eta)) := by ring
        _ ≤ (K + 1) * ((H : ℝ) * (p : ℝ) ^ (1 / 42 + eta)) :=
          mul_le_mul_of_nonneg_right hKle hBnonneg
        _ = (K + 1) * H * (p : ℝ) ^ (1 / 42 + eta) := by ring

/-- Shifted power cutoffs decrease with the layer index for p≥1 and positive j.
This supplies the nesting needed when interpreting the adjacent intervals. -/
theorem shiftedHeightCutoff_succ_le {p j : ℕ} {theta : ℝ} (hp : 1 ≤ p) (hj : 0 < j) :
    shiftedHeightCutoff p theta (j + 1) ≤ shiftedHeightCutoff p theta j := by
  unfold shiftedHeightCutoff
  apply Nat.floor_mono
  exact
    Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hp)
      (sub_le_sub_right
        (one_div_le_one_div_of_le (Nat.cast_pos.mpr hj) (Nat.cast_le.mpr (Nat.le_succ j))) theta)

/-- The 36 adjacent shifted-power intervals cover every height between the
degree-42 cutoff and the degree-6 cutoff. The general crossing lemma supplies
an index even before floor-cutoff monotonicity is used by the estimates. -/
theorem shiftedHeightCutoff_Icc_cover {p H : ℕ} {theta : ℝ}
    (hbot : shiftedHeightCutoff p theta 42 < H) (htop : H ≤ shiftedHeightCutoff p theta 6) :
    ∃ j ∈ Finset.Icc 6 41,
      shiftedHeightCutoff p theta (j + 1) < H ∧ H ≤ shiftedHeightCutoff p theta j := by
  obtain ⟨j, h6j, hj42, hlow, hhigh⟩ :=
    exists_adjacent_nat_layer (f := shiftedHeightCutoff p theta) (lo := 6) (hi := 42) (x := H)
      (by decide) hbot htop
  exact ⟨j, Finset.mem_Icc.mpr ⟨h6j, Nat.le_of_lt_succ hj42⟩, hlow, hhigh⟩

/-- Instantiate the generic height-layer count with the 36 shifted power
cutoffs. The small-height divisor term stops at degree 42, while every tail
ratio is counted at the upper cutoff of its own product-growth degree. -/
theorem boundedCongruenceCount_le_shiftedHeightLayers {p H : ℕ} [Fact p.Prime] {theta : ℝ}
    (hodd : Odd p) (hHp : H < p) (htop : H ≤ shiftedHeightCutoff p theta 6) :
    boundedCongruenceCount p H ≤
      4 *
        (shiftedHeightCutoff p theta 42 * H * maxDivisorCount H +
          ∑ j ∈ Finset.Icc 6 41,
            (heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card *
              (H / (shiftedHeightCutoff p theta (j + 1) + 1))) := by
  apply
    boundedCongruenceCount_le_height_layers (I := Finset.Icc 6 41) (lower := fun j ↦
      shiftedHeightCutoff p theta (j + 1)) (upper := fun j ↦ shiftedHeightCutoff p theta j) hodd hHp
  intro q hq hJ
  have hqheight := positiveRatioSet_canonical_height q hq
  have hqH : rationalPairHeight q ≤ H := max_le hqheight.2.1 hqheight.2.2
  exact shiftedHeightCutoff_Icc_cover hJ (hqH.trans htop)

/-- Inputs: `p>1`, a height below the degree-6 cutoff, and positive `delta, theta`.
Claim: the degree-42 small-height term is at most `C*H*p^(1/42+eta)` if
`theta+delta/6≤eta`. Proof: combine the uniform `H^delta` bound for the divisor maximum
with the degree-42 and degree-6 cutoff bounds. Role: absorb the non-layered part of the
height decomposition. -/
theorem shiftedHeightSmallTerm_rpow_bound {p H : ℕ} {theta delta eta : ℝ} (hp : 1 < p)
    (htop : H ≤ shiftedHeightCutoff p theta 6) (hdelta : 0 < delta) (htheta0 : 0 < theta)
    (hbudget : theta + delta / 6 ≤ eta) :
    ∃ C : ℝ,
      0 < C ∧
        ((shiftedHeightCutoff p theta 42 * H * maxDivisorCount H : ℕ) : ℝ) ≤
          C * H * (p : ℝ) ^ (1 / 42 + eta) := by
  obtain ⟨C, hC, hdiv⟩ := exists_uniform_maxDivisorCount_rpow_bound hdelta
  refine ⟨C, hC, ?_⟩
  by_cases hH : H = 0
  · subst H
    simp only [Nat.cast_zero, zero_mul, mul_zero]
    exact le_refl (0 : ℝ)
  · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
    have hcut42 : (shiftedHeightCutoff p theta 42 : ℝ) ≤ (p : ℝ) ^ (1 / (42 : ℝ) - theta) :=
      shiftedHeightCutoff_cast_le
    have hHcut : (H : ℝ) ≤ (p : ℝ) ^ (1 / (6 : ℝ) - theta) := by
      exact (Nat.cast_le.mpr htop).trans shiftedHeightCutoff_cast_le
    have hpR : (1 : ℝ) ≤ (p : ℝ) := Nat.one_le_cast.mpr hp.le
    have hp0 : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Nat.lt_trans Nat.zero_lt_one hp)
    have hHcut' : (H : ℝ) ≤ (p : ℝ) ^ (1 / (6 : ℝ)) := by
      apply hHcut.trans
      exact Real.rpow_le_rpow_of_exponent_le hpR (by linarith only [htheta0.le])
    have hHdelta : (H : ℝ) ^ delta ≤ (p : ℝ) ^ (delta / 6) := by
      calc
        _ ≤ ((p : ℝ) ^ (1 / (6 : ℝ))) ^ delta :=
          Real.rpow_le_rpow (Nat.cast_nonneg H) hHcut' hdelta.le
        _ = (p : ℝ) ^ ((1 / (6 : ℝ)) * delta) := (Real.rpow_mul (Nat.cast_nonneg p) _ _).symm
        _ = (p : ℝ) ^ (delta / 6) := by
          congr 1
          ring
    have hExp : 1 / (42 : ℝ) - theta + delta / 6 ≤ 1 / 42 + eta := by
      linarith only [hbudget, htheta0.le]
    have hprod :
      ((shiftedHeightCutoff p theta 42 : ℝ) * H) * (maxDivisorCount H : ℝ) ≤
        ((shiftedHeightCutoff p theta 42 : ℝ) * H) * (C * (H : ℝ) ^ delta) :=
      mul_le_mul_of_nonneg_left (hdiv H) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hJP :
      (shiftedHeightCutoff p theta 42 : ℝ) * (H : ℝ) ^ delta ≤
        (p : ℝ) ^ (1 / (42 : ℝ) - theta + delta / 6) := by
      calc
        _ ≤ (p : ℝ) ^ (1 / (42 : ℝ) - theta) * (p : ℝ) ^ (delta / 6) :=
          mul_le_mul hcut42 hHdelta (Real.rpow_nonneg (Nat.cast_nonneg H) delta)
            (Real.rpow_nonneg (Nat.cast_nonneg p) _)
        _ = (p : ℝ) ^ (1 / (42 : ℝ) - theta + delta / 6) := by rw [← Real.rpow_add hp0]
    calc
      _ = ((shiftedHeightCutoff p theta 42 : ℝ) * H) * (maxDivisorCount H : ℝ) := by
        simp only [Nat.cast_mul]
      _ ≤ ((shiftedHeightCutoff p theta 42 : ℝ) * H) * (C * (H : ℝ) ^ delta) := hprod
      _ = C * H * ((shiftedHeightCutoff p theta 42 : ℝ) * (H : ℝ) ^ delta) := by ring
      _ ≤ C * H * (p : ℝ) ^ (1 / (42 : ℝ) - theta + delta / 6) :=
        mul_le_mul_of_nonneg_left hJP (mul_nonneg hC.le (Nat.cast_nonneg H))
      _ ≤ C * H * (p : ℝ) ^ (1 / 42 + eta) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hpR hExp)
          (mul_nonneg hC.le (Nat.cast_nonneg H))

/-- Inputs: an odd prime `p`, `H<p`, and a degree-6 cutoff containing `H`.
Claim: the complete signed short-congruence count is at most `C*H*p^(1/42+eta)`
when `theta+delta/6≤eta`. Proof: combine the small-height divisor estimate with
the uniform sum over the 36 adjacent layers. Role: provide the pointwise count
bound for the subsequent Heilbronn energy and Miller--Rabin transfer. -/
theorem exists_uniform_boundedCongruenceCount_rpow_bound {p H : ℕ} [Fact p.Prime]
    {theta delta eta : ℝ} (hodd : Odd p) (hHp : H < p) (htop : H ≤ shiftedHeightCutoff p theta 6)
    (hdelta : 0 < delta) (htheta0 : 0 < theta) (htheta : theta < 1 / 42)
    (hbudget : theta + delta / 6 ≤ eta) :
    ∃ C : ℝ, 0 < C ∧ (boundedCongruenceCount p H : ℝ) ≤ C * H * (p : ℝ) ^ (1 / 42 + eta) := by
  have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
  obtain ⟨Csmall, hCsmall, hsmall⟩ :=
    shiftedHeightSmallTerm_rpow_bound hp htop hdelta htheta0 hbudget
  obtain ⟨Clayer, hClayer, hlayer⟩ :=
    exists_uniform_shiftedHeightLayers_weighted_sum_bound hp hHp hdelta htheta0 htheta hbudget
  let small : ℝ := ((shiftedHeightCutoff p theta 42 * H * maxDivisorCount H : ℕ) : ℝ)
  let tail : ℝ :=
    ∑ j ∈ Finset.Icc 6 41,
      ((heightRestrictedRatioSet p H (shiftedHeightCutoff p theta j)).card : ℝ) *
        (H / (shiftedHeightCutoff p theta (j + 1) + 1) : ℕ)
  have hcountNat := boundedCongruenceCount_le_shiftedHeightLayers hodd hHp htop
  have hcount : (boundedCongruenceCount p H : ℝ) ≤ 4 * (small + tail) := by
    have hc := Nat.cast_le (α := ℝ).mpr hcountNat
    simpa only [small, tail, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_sum] using hc
  have hpieces :
    small + tail ≤ Csmall * H * (p : ℝ) ^ (1 / 42 + eta) + Clayer * H * (p : ℝ) ^ (1 / 42 + eta) :=
    add_le_add hsmall hlayer
  refine ⟨4 * (Csmall + Clayer), mul_pos (by norm_num only) (add_pos hCsmall hClayer), ?_⟩
  calc
    _ ≤ 4 * (small + tail) := hcount
    _ ≤ 4 * (Csmall * H * (p : ℝ) ^ (1 / 42 + eta) + Clayer * H * (p : ℝ) ^ (1 / 42 + eta)) :=
      mul_le_mul_of_nonneg_left hpieces (by norm_num only)
    _ = 4 * (Csmall + Clayer) * H * (p : ℝ) ^ (1 / 42 + eta) := by ring

/-- Inputs: a real count estimate `N≤C*H*p^(g/a)` with `a>0`. Claim: the natural count
raised to `a` is bounded by a fixed natural coefficient times `H^a*p^g`. Proof: round `C`
up to a natural number, raise the real inequality to `a`, and use `(p^(g/a))^a=p^g`.
Role: put the height-layer estimate into the integer-power format required by the existing
Heilbronn energy budget. -/
theorem natural_count_power_le_rational_rpow_bound {N H p a g : ℕ} {C : ℝ}
    (hcount : (N : ℝ) ≤ C * H * (p : ℝ) ^ ((g : ℝ) / a)) (ha : 0 < a) :
    ∃ D : ℕ, N ^ a ≤ D ^ a * H ^ a * p ^ g := by
  let D : ℕ := Nat.ceil C
  have hCD : C ≤ (D : ℝ) := Nat.le_ceil C
  have hfactor : 0 ≤ (H : ℝ) * (p : ℝ) ^ ((g : ℝ) / a) :=
    mul_nonneg (Nat.cast_nonneg H) (Real.rpow_nonneg (Nat.cast_nonneg p) ((g : ℝ) / a))
  have hcount' : (N : ℝ) ≤ (D : ℝ) * H * (p : ℝ) ^ ((g : ℝ) / a) :=
    hcount.trans
      (calc
        C * H * (p : ℝ) ^ ((g : ℝ) / a) = C * ((H : ℝ) * (p : ℝ) ^ ((g : ℝ) / a)) := by ring
        _ ≤ (D : ℝ) * ((H : ℝ) * (p : ℝ) ^ ((g : ℝ) / a)) := mul_le_mul_of_nonneg_right hCD hfactor
        _ = (D : ℝ) * H * (p : ℝ) ^ ((g : ℝ) / a) := by ring)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg N) hcount' a
  have hpid : ((p : ℝ) ^ ((g : ℝ) / a)) ^ a = (p : ℝ) ^ g := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p) ((g : ℝ) / a) a,
      div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (ne_of_gt ha)), Real.rpow_natCast]
  refine ⟨D, ?_⟩
  apply Nat.cast_le (α := ℝ).mp
  have hreal : (N : ℝ) ^ a ≤ (D : ℝ) ^ a * (H : ℝ) ^ a * (p : ℝ) ^ g := by
    calc
      _ ≤ ((D : ℝ) * H * (p : ℝ) ^ ((g : ℝ) / a)) ^ a := hpow
      _ = (D : ℝ) ^ a * (H : ℝ) ^ a * (p : ℝ) ^ g := by rw [mul_pow, mul_pow, hpid]
  simpa only [Nat.cast_mul, Nat.cast_pow] using hreal

end PseudoPrime.NumberTheory.Heilbronn

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointEightNinthsRange
public import PseudoPrime.Analysis.BernsteinQuartic

/-! # Four small quartic certificates for continuous midscale endpoint radii -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For 24<=y<=32, the full endpoint polynomial is positive on the affine
level and logarithm lower chord stated below. An exact Bernstein identity
reduces the whole interval to five positive rational coefficients.
This is a continuous real certificate, not an enumeration of input moduli. -/
theorem midscaleEndpoint_base_pos_one {y : ℝ} (hlo : 24 ≤ y) (hhi : y ≤ 32) :
    0 <
      fullEndpointPolynomial ((837 / 800 : ℝ) * y + 167 / 100) (2096 / 1831) y
        ((719 / 20000 : ℝ) * y + 23151 / 10000) := by
  have ht₀ : 0 ≤ (y - 24) / 8 := by linarith only [hlo]
  have ht₁ : (y - 24) / 8 ≤ 1 := by linarith only [hhi]
  have hp :=
    Analysis.bernsteinQuartic_pos (c₀ := (2959535280219 / 9155000000 : ℝ)) (c₁ :=
      (9700792370963 / 22887500000 : ℝ)) (c₂ := (100639765117567 / 137325000000 : ℝ)) (c₃ :=
      (16375089123221 / 11443750000 : ℝ)) (c₄ := (25737114679559 / 9155000000 : ℝ))
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      ht₀ ht₁
  convert hp using 1
  dsimp only [fullEndpointPolynomial, Analysis.bernsteinQuartic]
  ring

/-- For 32<=y<=64, the full endpoint polynomial is positive at the certified
affine level and logarithm chord. Five positive Bernstein coefficients certify
the continuous interval by an exact rational identity. -/
theorem midscaleEndpoint_base_pos_two {y : ℝ} (hlo : 32 ≤ y) (hhi : y ≤ 64) :
    0 <
      fullEndpointPolynomial ((3309 / 3200 : ℝ) * y + 103 / 50) (2096 / 1831) y
        ((6931 / 320000 : ℝ) * y + 6931 / 2500) := by
  have ht₀ : 0 ≤ (y - 32) / 32 := by linarith only [hlo]
  have ht₁ : (y - 32) / 32 ≤ 1 := by linarith only [hhi]
  have hp :=
    Analysis.bernsteinQuartic_pos (c₀ := (25737114679559 / 9155000000 : ℝ)) (c₁ :=
      (363416241687299 / 183100000000 : ℝ)) (c₂ := (144414780694199 / 274650000000 : ℝ)) (c₃ :=
      (283780758380593 / 183100000000 : ℝ)) (c₄ := (418814661005741 / 22887500000 : ℝ))
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      ht₀ ht₁
  convert hp using 1
  dsimp only [fullEndpointPolynomial, Analysis.bernsteinQuartic]
  ring

/-- On 32<=y<=48, the first half of the refined middle interval satisfies
the endpoint polynomial at its proposed affine level and logarithmic chord.
Five positive Bernstein coefficients verify the whole real interval. -/
theorem midscaleEndpoint_base_pos_two_left {y : ℝ} (hlo : 32 ≤ y) (hhi : y ≤ 48) :
    0 <
      fullEndpointPolynomial ((3337 / 3200 : ℝ) * y + 89 / 50) (2096 / 1831) y
        ((811 / 32000 : ℝ) * y + 26547 / 10000) := by
  have ht₀ : 0 ≤ (y - 32) / 16 := by linarith only [hlo]
  have ht₁ : (y - 32) / 16 ≤ 1 := by linarith only [hhi]
  have hp :=
    Analysis.bernsteinQuartic_pos (c₀ := (129511169221789 / 45775000000 : ℝ)) (c₁ :=
      (85291861795931 / 36620000000 : ℝ)) (c₂ := (424733344942967 / 274650000000 : ℝ)) (c₃ :=
      (221043183277 / 292960000 : ℝ)) (c₄ := (2199283449089 / 2860937500 : ℝ)) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) ht₀ ht₁
  convert hp using 1
  dsimp only [fullEndpointPolynomial, Analysis.bernsteinQuartic]
  ring

/-- On 48<=y<=64, the second half of the refined middle interval satisfies
the endpoint polynomial at its proposed affine level and logarithmic chord.
The five positive Bernstein coefficients cover the entire interval. -/
theorem midscaleEndpoint_base_pos_two_right {y : ℝ} (hlo : 48 ≤ y) (hhi : y ≤ 64) :
    0 <
      fullEndpointPolynomial ((3281 / 3200 : ℝ) * y + 131 / 50) (2096 / 1831) y
        ((719 / 40000 : ℝ) * y + 7521 / 2500) := by
  have ht₀ : 0 ≤ (y - 48) / 16 := by linarith only [hlo]
  have ht₁ : (y - 48) / 16 ≤ 1 := by linarith only [hhi]
  have hp :=
    Analysis.bernsteinQuartic_pos (c₀ := (2199283449089 / 2860937500 : ℝ)) (c₁ :=
      (74582397179633 / 45775000000 : ℝ)) (c₂ := (271208476103803 / 68662500000 : ℝ)) (c₃ :=
      (3264174037503 / 366200000 : ℝ)) (c₄ := (210863233714933 / 11443750000 : ℝ))
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      ht₀ ht₁
  convert hp using 1
  dsimp only [fullEndpointPolynomial, Analysis.bernsteinQuartic]
  ring

/-- On 64<=y<=128, five positive Bernstein coefficients certify the endpoint
polynomial at the affine level and lower logarithmic chord. The proof is an
exact rational identity on a real interval, for subsequent witness extraction. -/
theorem midscaleEndpoint_base_pos_three {y : ℝ} (hlo : 64 ≤ y) (hhi : y ≤ 128) :
    0 <
      fullEndpointPolynomial ((3259 / 3200 : ℝ) * y + 153 / 50) (2096 / 1831) y
        ((6931 / 640000 : ℝ) * y + 6931 / 2000) := by
  have ht₀ : 0 ≤ (y - 64) / 64 := by linarith only [hlo]
  have ht₁ : (y - 64) / 64 ≤ 1 := by linarith only [hhi]
  have hp :=
    Analysis.bernsteinQuartic_pos (c₀ := (418814661005741 / 22887500000 : ℝ)) (c₁ :=
      (604317392644227 / 36620000000 : ℝ)) (c₂ := (1180431171396699 / 91550000000 : ℝ)) (c₃ :=
      (4565823560137437 / 183100000000 : ℝ)) (c₄ := (5736406141904129 / 45775000000 : ℝ))
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      ht₀ ht₁
  convert hp using 1
  dsimp only [fullEndpointPolynomial, Analysis.bernsteinQuartic]
  ring

/-- On 128<=y<=256, five positive Bernstein coefficients certify the endpoint
polynomial at the affine level and lower logarithmic chord. This continuous
certificate supplies the last interval of the midscale witness radius. -/
theorem midscaleEndpoint_base_pos_four {y : ℝ} (hlo : 128 ≤ y) (hhi : y ≤ 256) :
    0 <
      fullEndpointPolynomial ((12927 / 12800 : ℝ) * y + 83 / 20) (2096 / 1831) y
        ((6931 / 1280000 : ℝ) * y + 20793 / 5000) := by
  have ht₀ : 0 ≤ (y - 128) / 128 := by linarith only [hlo]
  have ht₁ : (y - 128) / 128 ≤ 1 := by linarith only [hhi]
  have hp :=
    Analysis.bernsteinQuartic_pos (c₀ := (5736406141904129 / 45775000000 : ℝ)) (c₁ :=
      (24148081528110619 / 183100000000 : ℝ)) (c₂ := (11630489436256537 / 91550000000 : ℝ)) (c₃ :=
      (32960345910879049 / 183100000000 : ℝ)) (c₄ := (3469527942695459 / 5721875000 : ℝ))
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      ht₀ ht₁
  convert hp using 1
  dsimp only [fullEndpointPolynomial, Analysis.bernsteinQuartic]
  ring

end PseudoPrime.LLS.PaperStatements

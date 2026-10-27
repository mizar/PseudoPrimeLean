/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MidscaleEndpointLogBounds

/-! # A five-piece affine radius for the full endpoint witness criterion -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The radius is the inverse of five affine level functions, joined at
L=703/20, 10367/200, 1706/25 and 6671/50. Its certified domain is
1339/50<=L<=26269/100; the endpoint radii are 24 and 256.
Outside this domain the definition is total but carries no bound theorem. -/
noncomputable def midscaleEndpointRadius (L : ℝ) : ℝ :=
  if L ≤ 703 / 20 then (800 / 837) * (L - 167 / 100)
  else
    if L ≤ 10367 / 200 then (3200 / 3337) * (L - 89 / 50)
    else
      if L ≤ 1706 / 25 then (3200 / 3281) * (L - 131 / 50)
      else if L ≤ 6671 / 50 then (3200 / 3259) * (L - 153 / 50) else (12800 / 12927) * (L - 83 / 20)

/-- The former four-piece radius is retained as a comparison baseline for
the two refined middle pieces. -/
noncomputable def midscaleEndpointRadiusOriginal (L : ℝ) : ℝ :=
  if L ≤ 703 / 20 then (800 / 837) * (L - 167 / 100)
  else
    if L ≤ 1706 / 25 then (3200 / 3309) * (L - 103 / 50)
    else if L ≤ 6671 / 50 then (3200 / 3259) * (L - 153 / 50) else (12800 / 12927) * (L - 83 / 20)

/-- The refined radius is no larger than the former radius. On the changed
pieces the difference factors as a nonnegative distance from an endpoint;
all other pieces agree. -/
theorem midscaleEndpointRadius_le_original {L : ℝ} :
    midscaleEndpointRadius L ≤ midscaleEndpointRadiusOriginal L := by
  by_cases h₁ : L ≤ 703 / 20
  · simp only [midscaleEndpointRadius, midscaleEndpointRadiusOriginal, ite_eq_left h₁]
    exact le_rfl
  · by_cases h₂ : L ≤ 10367 / 200
    · have hOld : L ≤ 1706 / 25 := by linarith only [h₂]
      simp only [midscaleEndpointRadius, midscaleEndpointRadiusOriginal, ite_eq_right h₁,
        ite_eq_left h₂, ite_eq_left hOld]
      have hd :
        (3200 / 3309 : ℝ) * (L - 103 / 50) - (3200 / 3337 : ℝ) * (L - 89 / 50) =
          (89600 / (3309 * 3337 : ℝ)) * (L - 703 / 20) := by
        ring
      have hn : 0 ≤ (89600 / (3309 * 3337 : ℝ)) * (L - 703 / 20) :=
        mul_nonneg (by norm_num only) (by linarith only [h₁])
      have hdiff : 0 ≤ (3200 / 3309 : ℝ) * (L - 103 / 50) - (3200 / 3337 : ℝ) * (L - 89 / 50) := by
        rw [hd]; exact hn
      exact sub_nonneg.mp hdiff
    · by_cases h₃ : L ≤ 1706 / 25
      · simp only [midscaleEndpointRadius, midscaleEndpointRadiusOriginal, ite_eq_right h₁,
          ite_eq_right h₂, ite_eq_left h₃]
        have hd :
          (3200 / 3309 : ℝ) * (L - 103 / 50) - (3200 / 3281 : ℝ) * (L - 131 / 50) =
            (89600 / (3309 * 3281 : ℝ)) * (1706 / 25 - L) := by
          ring
        have hn : 0 ≤ (89600 / (3309 * 3281 : ℝ)) * (1706 / 25 - L) :=
          mul_nonneg (by norm_num only) (by linarith only [h₃])
        have hdiff :
          0 ≤ (3200 / 3309 : ℝ) * (L - 103 / 50) - (3200 / 3281 : ℝ) * (L - 131 / 50) := by
          rw [hd]; exact hn
        exact sub_nonneg.mp hdiff
      · by_cases h₄ : L ≤ 6671 / 50
        · simp only [midscaleEndpointRadius, midscaleEndpointRadiusOriginal, ite_eq_right h₁,
            ite_eq_right h₂, ite_eq_right h₃, ite_eq_left h₄]
          exact le_rfl
        · simp only [midscaleEndpointRadius, midscaleEndpointRadiusOriginal, ite_eq_right h₁,
            ite_eq_right h₂, ite_eq_right h₃, ite_eq_right h₄]
          exact le_rfl

/-- The refined radius is strictly smaller throughout the interior of the
replaced interval. Its two affine differences vanish only at the outer ends. -/
theorem midscaleEndpointRadius_lt_original {L : ℝ} (hlo : 703 / 20 < L) (hhi : L < 1706 / 25) :
    midscaleEndpointRadius L < midscaleEndpointRadiusOriginal L := by
  by_cases h₂ : L ≤ 10367 / 200
  · simp only [midscaleEndpointRadius, midscaleEndpointRadiusOriginal,
      ite_eq_right (not_le_of_gt hlo), ite_eq_left h₂, ite_eq_left (le_of_lt hhi)]
    have hd :
      (3200 / 3309 : ℝ) * (L - 103 / 50) - (3200 / 3337 : ℝ) * (L - 89 / 50) =
        (89600 / (3309 * 3337 : ℝ)) * (L - 703 / 20) := by
      ring
    have hp : 0 < (89600 / (3309 * 3337 : ℝ)) * (L - 703 / 20) :=
      mul_pos (by norm_num only) (by linarith only [hlo])
    have hd' : 0 < (3200 / 3309 : ℝ) * (L - 103 / 50) - (3200 / 3337 : ℝ) * (L - 89 / 50) := by
      rw [hd]; exact hp
    exact sub_pos.mp hd'
  · simp only [midscaleEndpointRadius, midscaleEndpointRadiusOriginal,
      ite_eq_right (not_le_of_gt hlo), ite_eq_right h₂, ite_eq_left (le_of_lt hhi)]
    have hd :
      (3200 / 3309 : ℝ) * (L - 103 / 50) - (3200 / 3281 : ℝ) * (L - 131 / 50) =
        (89600 / (3309 * 3281 : ℝ)) * (1706 / 25 - L) := by
      ring
    have hp : 0 < (89600 / (3309 * 3281 : ℝ)) * (1706 / 25 - L) :=
      mul_pos (by norm_num only) (by linarith only [hhi])
    have hd' : 0 < (3200 / 3309 : ℝ) * (L - 103 / 50) - (3200 / 3281 : ℝ) * (L - 131 / 50) := by
      rw [hd]; exact hp
    exact sub_pos.mp hd'

/-- Throughout the certified real level interval, the radius is at least 24
and satisfies the full endpoint polynomial criterion. Split only at the three
affine junctions and apply the four continuous logarithmic certificates.
This supplies the analytic input for nonprincipal-character witnesses. -/
theorem midscaleEndpointRadius_data {L : ℝ} (hlo : 1339 / 50 ≤ L) (hhi : L ≤ 26269 / 100) :
    24 ≤ midscaleEndpointRadius L ∧
      0 <
        fullEndpointPolynomial L (2096 / 1831) (midscaleEndpointRadius L)
          (Real.log (midscaleEndpointRadius L)) := by
  by_cases h₁ : L ≤ 703 / 20
  · rw [midscaleEndpointRadius, ite_eq_left h₁]
    have ha : 24 ≤ (800 / 837 : ℝ) * (L - 167 / 100) := by linarith only [hlo]
    have hb : (800 / 837 : ℝ) * (L - 167 / 100) ≤ 32 := by linarith only [h₁]
    have hp := midscaleEndpoint_log_pos_one ha hb
    have he : (837 / 800 : ℝ) * ((800 / 837) * (L - 167 / 100)) + 167 / 100 = L := by ring
    rw [he] at hp
    exact ⟨ha, hp⟩
  · by_cases h₂ : L ≤ 10367 / 200
    · rw [midscaleEndpointRadius, ite_eq_right h₁, ite_eq_left h₂]
      have ha : 32 ≤ (3200 / 3337 : ℝ) * (L - 89 / 50) := by linarith only [h₁]
      have hb : (3200 / 3337 : ℝ) * (L - 89 / 50) ≤ 48 := by linarith only [h₂]
      have hp := midscaleEndpoint_log_pos_two_left ha hb
      have he : (3337 / 3200 : ℝ) * ((3200 / 3337) * (L - 89 / 50)) + 89 / 50 = L := by ring
      rw [he] at hp
      exact ⟨by linarith only [ha], hp⟩
    · by_cases h₃ : L ≤ 1706 / 25
      · rw [midscaleEndpointRadius, ite_eq_right h₁, ite_eq_right h₂, ite_eq_left h₃]
        have ha : 48 ≤ (3200 / 3281 : ℝ) * (L - 131 / 50) := by linarith only [h₂]
        have hb : (3200 / 3281 : ℝ) * (L - 131 / 50) ≤ 64 := by linarith only [h₃]
        have hp := midscaleEndpoint_log_pos_two_right ha hb
        have he : (3281 / 3200 : ℝ) * ((3200 / 3281) * (L - 131 / 50)) + 131 / 50 = L := by ring
        rw [he] at hp
        exact ⟨by linarith only [ha], hp⟩
      · by_cases h₄ : L ≤ 6671 / 50
        · rw [midscaleEndpointRadius, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃,
            ite_eq_left h₄]
          have ha : 64 ≤ (3200 / 3259 : ℝ) * (L - 153 / 50) := by linarith only [h₃]
          have hb : (3200 / 3259 : ℝ) * (L - 153 / 50) ≤ 128 := by linarith only [h₄]
          have hp := midscaleEndpoint_log_pos_three ha hb
          have he : (3259 / 3200 : ℝ) * ((3200 / 3259) * (L - 153 / 50)) + 153 / 50 = L := by ring
          rw [he] at hp
          exact ⟨by linarith only [ha], hp⟩
        · rw [midscaleEndpointRadius, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃,
            ite_eq_right h₄]
          have ha : 128 ≤ (12800 / 12927 : ℝ) * (L - 83 / 20) := by linarith only [h₄]
          have hb : (12800 / 12927 : ℝ) * (L - 83 / 20) ≤ 256 := by linarith only [hhi]
          have hp := midscaleEndpoint_log_pos_four ha hb
          have he : (12927 / 12800 : ℝ) * ((12800 / 12927) * (L - 83 / 20)) + 83 / 20 = L := by ring
          rw [he] at hp
          exact ⟨by linarith only [ha], hp⟩

/-- Up to the fourth join, the five-piece endpoint radius remains at most
128. This is the range required by the certified three-band `7/4` shift. -/
theorem midscaleEndpointRadius_le_128 {L : ℝ} (hhi : L ≤ 6671 / 50) :
    midscaleEndpointRadius L ≤ 128 := by
  by_cases h₁ : L ≤ 703 / 20
  · simp only [midscaleEndpointRadius, ite_eq_left h₁]
    nlinarith only [h₁]
  · by_cases h₂ : L ≤ 10367 / 200
    · simp only [midscaleEndpointRadius, ite_eq_right h₁, ite_eq_left h₂]
      nlinarith only [h₁, h₂]
    · by_cases h₃ : L ≤ 1706 / 25
      · simp only [midscaleEndpointRadius, ite_eq_right h₁, ite_eq_right h₂, ite_eq_left h₃]
        nlinarith only [h₁, h₂, h₃]
      · simp only [midscaleEndpointRadius, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃,
          ite_eq_left hhi]
        nlinarith only [hhi]

/-- Under GRH, every nonprincipal character of level q with
1339/50<=log q<=26269/100 has a non-one prime through the squared midscale
radius. Apply the continuous polynomial criterion at the original level.
The prime may be 2 or a divisor of q; no odd-prime assertion is made. -/
theorem exists_prime_ne_one_le_midscale_radius_sq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : 1339 / 50 ≤ Real.log q) (hhi : Real.log q ≤ 26269 / 100) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (midscaleEndpointRadius (Real.log q)) ^ 2 ∧ χ p ≠ 1 := by
  obtain ⟨hy, hp⟩ := midscaleEndpointRadius_data hlo hhi
  exact exists_prime_ne_one_of_fullEndpointPolynomial_original χ hne hGRH (by linarith only [hy]) hp

end PseudoPrime.LLS.PaperStatements

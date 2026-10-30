/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CubicSquareFactorLinearBounds
public import PseudoPrime.LLS.ParameterizedCubicSquareFactorRadius

/-! # Cubic envelopes retaining the improved constant and squarefree logarithm -/

@[expose] public section
namespace PseudoPrime.LLS.PaperStatements
/-- For nonnegative B,D and Y>0, the inequality 2B sqrt(Y)+D<=Y bounds the
squared positive quadratic root by Y. Compare the radicand with (sqrt(Y)-B)^2.
This permits direct coefficient absorption without the coarser displayed envelope. -/
private theorem root_le_budget {B D Y : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (hY : 0 < Y)
    (hc : 2 * B * Real.sqrt Y + D ≤ Y) :
    (B + Real.sqrt (B ^ 2 + D)) ^ 2 ≤ Y := by
  have hs := Real.sq_sqrt hY.le
  have hm : B * Real.sqrt Y ≤ Real.sqrt Y * Real.sqrt Y := by
    nlinarith only [hc,hD,hs,mul_nonneg hB (Real.sqrt_nonneg Y)]
  have hb := le_of_mul_le_mul_right hm (Real.sqrt_pos.mpr hY)
  have hrad : B ^ 2 + D ≤ (Real.sqrt Y - B) ^ 2 := by nlinarith only [hc,hs]
  have ht := (Real.sqrt_le_left (sub_nonneg.mpr hb)).mpr hrad
  have hroot : B + Real.sqrt (B ^ 2 + D) ≤ Real.sqrt Y := by linarith only [ht]
  have hsq := pow_le_pow_left₀ (add_nonneg hB (Real.sqrt_nonneg _)) hroot 2
  exact hsq.trans_eq hs

/-- The squared cubic root with B=(10/13)G+2434/75 and D=(4/3)(L-d).
Applications use d=log(squarefree part), G=log(4 times that part), and d<=L.
Keeping the subtracted logarithm improves the full square-factor envelope. -/
noncomputable def cubic2434RootEnvelope (G d L : ℝ) : ℝ :=
  (((10 / 13 : ℝ) * G + 2434 / 75) +
    Real.sqrt ((((10 / 13 : ℝ) * G + 2434 / 75) ^ 2) + (4 / 3 : ℝ) * (L - d))) ^ 2
/-- The displayed envelope D+4B^2+2B sqrt(D), with the improved affine B
and D=(4/3)(L-d). For fixed squarefree part its leading coefficient is 4/3.
The exact root below remains the input to sharper coefficient cutoffs. -/
noncomputable def cubic2434LinearEnvelope (G d L : ℝ) : ℝ :=
  (4 / 3 : ℝ) * (L - d) + 4 * ((10 / 13 : ℝ) * G + 2434 / 75) ^ 2 +
    2 * ((10 / 13 : ℝ) * G + 2434 / 75) * Real.sqrt ((4 / 3 : ℝ) * (L - d))
/-- A square-factor budget E<=(L-d)/2 bounds the improved squared radius
by the root envelope. Compare radicands and square the nonnegative roots.
This is the arithmetic-to-real interface for actual Jacobi witness bounds. -/
theorem cubic2434_radius_le_root {G d L E : ℝ} (hG : 0 ≤ G)
    (hc : E ≤ (L - d) / 2) :
    (cubicSquareFactorRadius2434 G E) ^ 2 ≤ cubic2434RootEnvelope G d L := by
  have hB : 0 ≤ (10 / 13 : ℝ) * G + 2434 / 75 := by linarith only [hG]
  have hs := Real.sqrt_le_sqrt (by linarith only [hc] :
    (((10 / 13 : ℝ) * G + 2434 / 75) ^ 2) + (8 / 3 : ℝ) * E ≤
      (((10 / 13 : ℝ) * G + 2434 / 75) ^ 2) + (4 / 3 : ℝ) * (L - d))
  exact pow_le_pow_left₀ (add_nonneg hB (Real.sqrt_nonneg _)) (add_le_add_right hs _) 2
/-- For G>=0,d<=L, the exact root envelope is at most the displayed envelope.
Apply the existing nonnegative quadratic-root estimate, retaining L-d.
This supplies a simpler formula without changing the leading coefficient. -/
theorem cubic2434_root_le_linear {G d L : ℝ} (hG : 0 ≤ G) (hd : d ≤ L) :
    cubic2434RootEnvelope G d L ≤ cubic2434LinearEnvelope G d L := by
  exact root_radius_sq_le_linear_sqrt (by linarith only [hG])
    (mul_nonneg (by norm_num only) (sub_nonneg.mpr hd))
/-- For G,d>=0, the new displayed envelope is strictly below the old one.
The affine constant drops from 35 to 2434/75 and the square-root budget decreases.
Compare the positive square and mixed terms; no large-conductor threshold is needed. -/
theorem cubic2434_linear_lt_old {G d L : ℝ} (hG : 0 ≤ G) (hd : 0 ≤ d) :
    cubic2434LinearEnvelope G d L < cubicSquareFactorLinearEnvelope G L := by
  have hB : 0 ≤ (10 / 13 : ℝ) * G + 2434 / 75 := by linarith only [hG]
  have hBB : (10 / 13 : ℝ) * G + 2434 / 75 < (10 / 13 : ℝ) * G + 35 := by linarith only
  have hsq := (sq_lt_sq₀ hB (hB.trans hBB.le)).mpr hBB
  have hs := Real.sqrt_le_sqrt (by linarith only [hd] :
    (4 / 3 : ℝ) * (L - d) ≤ (4 / 3 : ℝ) * L)
  have hm := mul_le_mul hBB.le hs (Real.sqrt_nonneg _) (hB.trans hBB.le)
  dsimp only [cubic2434LinearEnvelope,cubicSquareFactorLinearEnvelope]
  nlinarith only [hsq,hm,hd]
/-- For G>=0,d<=L, the root envelope is at least (4868/75)^2.
Compare with the zero-cost improved radius and its existing lower bound.
This absorbs the exceptional Selfridge stopping magnitudes below 27. -/
theorem cubic2434_root_ge {G d L : ℝ} (hG : 0 ≤ G) (hdL : d ≤ L) :
    (4868 / 75 : ℝ) ^ 2 ≤ cubic2434RootEnvelope G d L := by
  have h := cubic2434_radius_le_root (d := d) (L := L) (E := 0) hG
    (by linarith only [hdL])
  have hr := (cubicSquareFactorRadius2434_data (E := 0) hG le_rfl).1
  nlinarith only [h,hr]
/-- For L>0,delta>0,d<=L and G>=0, the stated direct quadratic condition
bounds the root by (4/3+delta)L. Apply the generic positive-root criterion.
The squarefree logarithm remains in this sharper sufficient condition. -/
theorem cubic2434_root_le_coefficient {G d L δ : ℝ} (hG : 0 ≤ G) (hdL : d ≤ L)
    (hL : 0 < L) (hδ : 0 < δ)
    (hc : δ * L + (4 / 3 : ℝ) * d ≥
      2 * ((10 / 13 : ℝ) * G + 2434 / 75) * Real.sqrt ((4 / 3 + δ) * L)) :
    cubic2434RootEnvelope G d L ≤ (4 / 3 + δ) * L := by
  apply root_le_budget (by linarith only [hG])
    (mul_nonneg (by norm_num only) (sub_nonneg.mpr hdL))
    (mul_pos (by linarith only [hδ]) hL)
  linarith only [hc]
/-- For G,d>=0,d<=L,L>0 and delta>0, a single explicit cutoff
4(4/3+delta)B^2/delta^2<=L bounds the root by (4/3+delta)L.
Square the nonnegative mixed term and use the direct quadratic criterion;
the proof does not pass through the coarser displayed envelope. -/
theorem cubic2434_single_cutoff {G d L δ : ℝ} (hG : 0 ≤ G) (hd : 0 ≤ d) (hdL : d ≤ L)
    (hL : 0 < L) (hδ : 0 < δ)
    (hc : 4 * (4 / 3 + δ) * ((10 / 13 : ℝ) * G + 2434 / 75) ^ 2 / δ ^ 2 ≤ L) :
    cubic2434RootEnvelope G d L ≤ (4 / 3 + δ) * L := by
  have hB : 0 ≤ (10 / 13 : ℝ) * G + 2434 / 75 := by linarith only [hG]
  have hC : 0 ≤ (4 / 3 + δ) * L := mul_nonneg (by linarith only [hδ]) hL.le
  have hm := mul_le_mul_of_nonneg_right ((div_le_iff₀ (sq_pos_of_pos hδ)).mp hc) hL.le
  have hsq := Real.sq_sqrt hC
  have hb : 2 * ((10 / 13 : ℝ) * G + 2434 / 75) * Real.sqrt ((4 / 3 + δ) * L) ≤ δ * L := by
    apply (sq_le_sq₀
      (mul_nonneg (mul_nonneg (by norm_num only) hB) (Real.sqrt_nonneg _))
      (mul_nonneg hδ.le hL.le)).mp
    nlinarith only [hm,hsq]
  exact cubic2434_root_le_coefficient hG hdL hL hδ (by linarith only [hb,hd])
end PseudoPrime.LLS.PaperStatements

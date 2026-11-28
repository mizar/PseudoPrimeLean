/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleCompensation
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCompensationAbel

/-! # Centered Abel bounds for middle Gaussian compensation cells -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Express the unit-cell compensation polynomial in the log coordinate. -/
private noncomputable def middleCellLogPoly (P : Polynomial ℚ) (N : ℕ) (l h : ℚ) : Polynomial ℝ :=
  (Analysis.bernsteinCompensation (P.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)) N).comp
    (Polynomial.C ((h : ℝ)⁻¹) * (Polynomial.X - Polynomial.C (l : ℝ)))

/-- The log-coordinate polynomial evaluates to the cell correction. -/
private theorem middle_cell_log_eval (P : Polynomial ℚ) (N : ℕ) (l h : ℚ) (v : ℝ) :
    (middleCellLogPoly P N l h).eval v = middleCompCell P N l h v := by
  simp only [middleCellLogPoly, middleCompCell, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X, div_eq_mul_inv]
  rw [mul_comm]

/-- Differentiation in the log coordinate introduces the reciprocal cell width. -/
private theorem middle_cell_log_derivative (P : Polynomial ℚ) (N : ℕ) (l h : ℚ) (v : ℝ) :
    let C :=
      Analysis.bernsteinCompensation (P.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)) N
    (middleCellLogPoly P N l h).derivative.eval v =
      (h : ℝ)⁻¹ * C.derivative.eval ((v - (l : ℝ)) / (h : ℝ)) := by
  simp only [middleCellLogPoly, Polynomial.derivative_comp, Polynomial.derivative_C_mul,
    Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, mul_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X, div_eq_mul_inv]
  rw [mul_comm ((h : ℝ)⁻¹) (v - (l : ℝ))]

/-- Under RH, bound the Mangoldt sum on a middle cell using its main integral,
absolute variation and endpoint terms. -/
public theorem middle_comp_cell_abel (hRH : RiemannHypothesis) (P : Polynomial ℚ) (N : ℕ)
    {X b a : ℝ} (hX : 0 < X) (l h : ℚ) (hh : 0 ≤ h)
    (hA : 1000000 ≤ X * Real.exp (b - ((l + h : ℚ) : ℝ))) :
    let A := X * Real.exp (b - ((l + h : ℚ) : ℝ))
    let B := X * Real.exp (b - (l : ℝ))
    let v := fun t : ℝ ↦ b - Real.log (t / X)
    let f := fun t : ℝ ↦ t ^ (-(1 / 2) : ℝ) * Real.exp (-a * v t) * middleCompCell P N l h (v t)
    let C :=
      Analysis.bernsteinCompensation (P.comp (Polynomial.C h * Polynomial.X + Polynomial.C l)) N
    let u := fun t : ℝ ↦ (t - (l : ℝ)) / (h : ℝ)
    (∑ m ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, ArithmeticFunction.vonMangoldt m * f m) ≤
      (Real.sqrt X * Real.exp (b / 2)) *
              (∫ t in (l : ℝ)..((l + h : ℚ) : ℝ),
                Real.exp (-(a + 1 / 2) * t) * middleCompCell P N l h t) +
            (Chebyshev.psi B - B) * f B -
          (Chebyshev.psi A - A) * f A +
        Real.log B ^ 2 / 24 *
          (∫ t in (l : ℝ)..((l + h : ℚ) : ℝ),
            Real.exp (-a * t) *
              |(a - 1 / 2) * middleCompCell P N l h t - (h : ℝ)⁻¹ * C.derivative.eval (u t)|) := by
  have hlr : (l : ℝ) ≤ ((l + h : ℚ) : ℝ) := Rat.cast_le.mpr (le_add_of_nonneg_right hh)
  have hc := gaussian_compensation_log_piece hRH (middleCellLogPoly P N l h) (a := a) hX hlr hA
  simpa only [gaussianCompensationWeight, middle_cell_log_eval, middle_cell_log_derivative] using hc

/-- The reversed logarithm maps a physical interval back to its log cell. -/
private theorem middle_log_mem {X b l r t : ℝ} (hX : 0 < X)
    (ht : t ∈ Set.Icc (X * Real.exp (b - r)) (X * Real.exp (b - l))) :
    b - Real.log (t / X) ∈ Set.Icc l r := by
  have hp : 0 < t / X := div_pos ((mul_pos hX (Real.exp_pos _)).trans_le ht.1) hX
  have hu :=
    (Real.log_le_iff_le_exp hp).mpr ((div_le_iff₀ hX).mpr (by simpa only [mul_comm] using ht.2))
  have hl :=
    (Real.le_log_iff_exp_le hp).mpr ((le_div_iff₀ hX).mpr (by simpa only [mul_comm] using ht.1))
  exact ⟨by linarith only [hu], by linarith only [hl]⟩

/-- Sum the RH Abel bound over matching log polynomial pieces with vanishing
outer endpoints and one common variation coefficient. -/
public theorem middle_comp_poly_partition (hRH : RiemannHypothesis) (k : ℕ) (u : ℕ → ℝ)
    (hu : Antitone u) (Q : ℕ → Polynomial ℝ) {X b a : ℝ} (hX : 0 < X)
    (ha : 1000000 ≤ X * Real.exp (b - u 0)) (C : ℝ → ℝ)
    (hm : ∀ j < k, ∀ v ∈ Set.Icc (u (j + 1)) (u j), (Q j).eval v = C v) (h0 : C (u 0) = 0)
    (hk : C (u k) = 0) :
    let x := fun j ↦ X * Real.exp (b - u j)
    let F := fun t : ℝ ↦
      t ^ (-(1 / 2) : ℝ) * Real.exp (-a * (b - Real.log (t / X))) * C (b - Real.log (t / X))
    (∑ n ∈ Finset.Ioc ⌊x 0⌋₊ ⌊x k⌋₊, ArithmeticFunction.vonMangoldt n * F n) ≤
      ∑ j ∈ Finset.range k,
        ((Real.sqrt X * Real.exp (b / 2)) *
            (∫ v in u (j + 1)..u j, Real.exp (-(a + 1 / 2) * v) * (Q j).eval v) +
          Real.log (x k) ^ 2 / 24 *
            (∫ v in u (j + 1)..u j,
              Real.exp (-a * v) * |(a - 1 / 2) * (Q j).eval v - (Q j).derivative.eval v|)) := by
  intro x F
  let f := fun j ↦ gaussianCompensationWeight (Q j) X b a
  have hx : Monotone x := fun i j hij ↦
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_left (hu hij) b)) hX.le
  have hp (j : ℕ) : 0 < x j := mul_pos hX (Real.exp_pos _)
  have he (j : ℕ) : b - Real.log (x j / X) = u j := by
    dsimp only [x]
    rw [mul_div_cancel_left₀ _ hX.ne', Real.log_exp, sub_sub_cancel]
  have hm' : ∀ j < k, ∀ t ∈ Set.Icc (x j) (x (j + 1)), f j t = F t := by
    intro j hj t ht
    simp only [f, F, gaussianCompensationWeight, hm j hj _ (middle_log_mem hX ht)]
  have hz (j : ℕ) (hj : C (u j) = 0) : F (x j) = 0 := by simp only [F, he, hj, mul_zero]
  have H :=
    gaussian_compensation_partition hRH k x hx ha F f hm'
      (fun j _ t ht ↦
        (gaussian_compensation_hasDerivAt (Q j) (b := b) (a := a) hX
            ((hp j).trans_le ht.1)).differentiableAt)
      (fun j _ ↦ gaussian_compensation_deriv_integrable (Q j) hX (hp j)) (hz 0 h0) (hz k hk)
  refine H.trans (Finset.sum_le_sum fun j hj ↦ ?_)
  have hstep := hu (Nat.le_succ j)
  have hB := hx (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
  have h1 : 1 ≤ x (j + 1) :=
    (by norm_num only : (1 : ℝ) ≤ 1000000).trans (ha.trans (hx (Nat.zero_le _)))
  have hlog0 := Real.log_nonneg h1
  have hlog := Real.log_le_log (hp _) hB
  have hsq := (sq_le_sq₀ hlog0 (hlog0.trans hlog)).mpr hlog
  have hv :
    0 ≤
      ∫ v in u (j + 1)..u j,
        Real.exp (-a * v) * |(a - 1 / 2) * (Q j).eval v - (Q j).derivative.eval v| :=
    intervalIntegral.integral_nonneg hstep (fun v _ ↦ mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
  dsimp only [x, f] at hsq ⊢
  rw [gaussian_compensation_main_cell _ hX hstep, gaussian_compensation_variation_cell _ hX hstep]
  exact
    add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsq (by norm_num only)) hv)

/-- The physical Mangoldt weight of a log-coordinate compensation function. -/
@[expose]
public noncomputable def middleCompWeight (C : ℝ → ℝ) (X b a t : ℝ) : ℝ :=
  let v := b - Real.log (t / X)
  t ^ (-(1 / 2) : ℝ) * Real.exp (-a * v) * C v

/-- Agreement on a log cell transfers to its physical interval. -/
private theorem middle_comp_weight_match {C D : ℝ → ℝ} {X b a l r : ℝ} (hX : 0 < X)
    (h : ∀ v ∈ Set.Icc l r, C v = D v) {t : ℝ}
    (ht : t ∈ Set.Icc (X * Real.exp (b - r)) (X * Real.exp (b - l))) :
    middleCompWeight C X b a t = middleCompWeight D X b a t := by
  simp only [middleCompWeight, h _ (middle_log_mem hX ht)]

/-- Locally equal log corrections have the same Mangoldt sum over the cell. -/
private theorem middle_comp_weight_sum_congr {C D : ℝ → ℝ} {X b a l r : ℝ} (hX : 0 < X)
    (hlr : l ≤ r) (h : ∀ v ∈ Set.Icc l r, C v = D v) :
    let A := X * Real.exp (b - r)
    let B := X * Real.exp (b - l)
    (∑ m ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, ArithmeticFunction.vonMangoldt m * middleCompWeight C X b a m) =
      ∑ m ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,
        ArithmeticFunction.vonMangoldt m * middleCompWeight D X b a m := by
  intro A B
  have hA : 0 < A := mul_pos hX (Real.exp_pos _)
  have hAB : A ≤ B := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_left hlr b)) hX.le
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨hmL, hmR⟩ := Finset.mem_Ioc.mp hm
  have ht : (m : ℝ) ∈ Set.Icc A B :=
    ⟨((Nat.floor_lt hA.le).mp hmL).le, (Nat.le_floor_iff (hA.le.trans hAB)).mp hmR⟩
  rw [middle_comp_weight_match hX h ht]

/-- Evaluate the physical weight at the point corresponding to a log endpoint. -/
public theorem middle_comp_weight_at {C : ℝ → ℝ} {X b a l : ℝ} (hX : 0 < X) :
    middleCompWeight C X b a (X * Real.exp (b - l)) =
      (X * Real.exp (b - l)) ^ (-(1 / 2) : ℝ) * Real.exp (-a * l) * C l := by
  simp only [middleCompWeight, mul_div_cancel_left₀ _ hX.ne', Real.log_exp, sub_sub_cancel]

/-- Separate the Mangoldt sum into the first cell and the joined tail. -/
public theorem middle_comp_sum_cons {P : Polynomial ℚ} {N : ℕ} (hN : P.natDegree ≤ N) (hs : List ℚ)
    (hw : ∀ w ∈ hs, 0 < w) (l h : ℚ) (hh : 0 < h) {X b a : ℝ} (hX : 0 < X) :
    let A := X * Real.exp (b - ((l + h + hs.sum : ℚ) : ℝ))
    let M := X * Real.exp (b - ((l + h : ℚ) : ℝ))
    let B := X * Real.exp (b - (l : ℝ))
    (∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,
        ArithmeticFunction.vonMangoldt n *
          middleCompWeight (middleCompOn P N (h :: hs) l) X b a n) =
      (∑ n ∈ Finset.Ioc ⌊M⌋₊ ⌊B⌋₊,
          ArithmeticFunction.vonMangoldt n * middleCompWeight (middleCompCell P N l h) X b a n) +
        ∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊M⌋₊,
          ArithmeticFunction.vonMangoldt n *
            middleCompWeight (middleCompOn P N hs (l + h)) X b a n := by
  intro A M B
  have hLM : (l : ℝ) ≤ ((l + h : ℚ) : ℝ) := Rat.cast_le.mpr (le_add_of_nonneg_right hh.le)
  have hMR : ((l + h : ℚ) : ℝ) ≤ ((l + h + hs.sum : ℚ) : ℝ) :=
    Rat.cast_le.mpr (le_add_of_nonneg_right (List.sum_nonneg fun w hm ↦ (hw w hm).le))
  have hAM : A ≤ M := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_left hMR b)) hX.le
  have hMB : M ≤ B := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_left hLM b)) hX.le
  have hd : Disjoint (Finset.Ioc ⌊A⌋₊ ⌊M⌋₊) (Finset.Ioc ⌊M⌋₊ ⌊B⌋₊) :=
    Finset.disjoint_left.mpr
      (fun n h₁ h₂ ↦ (not_lt_of_ge (Finset.mem_Ioc.mp h₁).2) (Finset.mem_Ioc.mp h₂).1)
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.floor_mono hAM) (Nat.floor_mono hMB), Finset.sum_union hd,
    add_comm]
  have hleft :=
    middle_comp_weight_sum_congr (b := b) (a := a) hX hLM (C := middleCompOn P N (h :: hs) l) (D :=
      middleCompCell P N l h) (fun _ hv ↦ middle_comp_on_cons_left P N hs l h hv.2)
  have hright :=
    middle_comp_weight_sum_congr (b := b) (a := a) hX hMR (C := middleCompOn P N (h :: hs) l) (D :=
      middleCompOn P N hs (l + h)) (fun v hv ↦ middle_comp_on_cons_right hN hs hw l h hh hv.1)
  exact congrArg₂ (· + ·) hleft hright

/-- Positive cell widths make the sum of absolute variation integrals nonnegative. -/
private theorem middle_comp_var_nonneg (P : Polynomial ℚ) (N : ℕ) (a d : ℚ) (hs : List ℚ)
    (hw : ∀ w ∈ hs, 0 < w) (l : ℚ) : 0 ≤ middleCompVariation P N a d hs l := by
  induction hs generalizing l with
  | nil => exact le_rfl
  | cons w ws ih =>
    rw [middleCompVariation]
    have hwp := (hw w List.mem_cons_self).le
    exact
      add_nonneg
        (intervalIntegral.integral_nonneg (Rat.cast_le.mpr (le_add_of_nonneg_right hwp))
          (fun _ _ ↦ mul_nonneg (Real.exp_pos _).le (abs_nonneg _)))
        (ih (fun w hm ↦ hw w (List.mem_cons_of_mem _ hm)) _)

/-- Sum the cellwise centered Abel estimates, canceling every internal boundary term. -/
public theorem middle_comp_abel (hRH : RiemannHypothesis) (P : Polynomial ℚ) (N : ℕ)
    (hN : P.natDegree ≤ N) (hs : List ℚ) (hw : ∀ w ∈ hs, 0 < w) (l : ℚ) {X b : ℝ} (a : ℚ)
    (hX : 0 < X) (ha : 1000000 ≤ X * Real.exp (b - ((l + hs.sum : ℚ) : ℝ))) :
    let A := X * Real.exp (b - ((l + hs.sum : ℚ) : ℝ))
    let B := X * Real.exp (b - (l : ℝ))
    let F := middleCompWeight (middleCompOn P N hs l) X b (a : ℝ)
    (∑ m ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, ArithmeticFunction.vonMangoldt m * F m) ≤
      (Real.sqrt X * Real.exp (b / 2)) *
              (∫ v in (l : ℝ)..((l + hs.sum : ℚ) : ℝ),
                Real.exp (-(a + (1 / 2 : ℝ)) * v) * middleCompOn P N hs l v) +
            (Chebyshev.psi B - B) * F B -
          (Chebyshev.psi A - A) * F A +
        Real.log B ^ 2 / 24 * middleCompVariation P N a (a - 1 / 2) hs l := by
  induction hs generalizing l with
  | nil =>
    simp only [List.sum_nil, add_zero, Finset.Ioc_self, Finset.sum_empty,
      intervalIntegral.integral_same, mul_zero, zero_add, sub_self, middleCompVariation, le_refl]
  | cons h hs ih =>
    have hh := hw h List.mem_cons_self
    have ht : ∀ w ∈ hs, 0 < w := fun w hm ↦ hw w (List.mem_cons_of_mem h hm)
    simp only [List.sum_cons, ← add_assoc] at ha ⊢
    let A := X * Real.exp (b - ((l + h + hs.sum : ℚ) : ℝ))
    let M := X * Real.exp (b - ((l + h : ℚ) : ℝ))
    let B := X * Real.exp (b - (l : ℝ))
    have hlr : (l : ℝ) ≤ ((l + h : ℚ) : ℝ) := Rat.cast_le.mpr (le_add_of_nonneg_right hh.le)
    have hMR : ((l + h : ℚ) : ℝ) ≤ ((l + h + hs.sum : ℚ) : ℝ) :=
      Rat.cast_le.mpr (le_add_of_nonneg_right (List.sum_nonneg fun w hm ↦ (ht w hm).le))
    have hAM : A ≤ M :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_left hMR b)) hX.le
    have hMB : M ≤ B :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_left hlr b)) hX.le
    have hm1 : 1 ≤ M := (by norm_num only : (1 : ℝ) ≤ 1000000).trans (ha.trans hAM)
    have hlog := Real.log_le_log (zero_lt_one.trans_le hm1) hMB
    have hsq := (sq_le_sq₀ (Real.log_nonneg hm1) ((Real.log_nonneg hm1).trans hlog)).mpr hlog
    have hg : Continuous (fun v : ℝ ↦ Real.exp (-(a + (1 / 2 : ℝ)) * v)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hc := middle_comp_cell_abel hRH P N (a := (a : ℝ)) hX l h hh.le (ha.trans hAM)
    have htail := ih ht (l + h) ha
    have hB := middle_comp_on_cons_left P N hs l h (v := (l : ℝ)) hlr
    have hM :=
      (middle_comp_on_cons_left P N hs l h (v := ((l + h : ℚ) : ℝ)) le_rfl).symm.trans
        (middle_comp_on_cons_right hN hs ht l h hh le_rfl)
    have hA := middle_comp_on_cons_right hN hs ht l h hh (v := ((l + h + hs.sum : ℚ) : ℝ)) hMR
    have hvar := middle_comp_var_nonneg P N a (a - 1 / 2) hs ht (l + h)
    have hmajor :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsq (by norm_num only : (0 : ℝ) ≤ 24))
        hvar
    rw [middle_comp_sum_cons hN hs ht l h hh hX, middle_comp_integral_cons P N hN hs ht l h hh _ hg,
      middleCompVariation]
    dsimp only [A, M, B] at hmajor
    simp only [mul_div_cancel_left₀ _ hX.ne', Real.log_exp, sub_sub_cancel] at hc
    rw [hM] at hc
    simp only [middleCompWeight, mul_div_cancel_left₀ _ hX.ne', Real.log_exp, sub_sub_cancel, hB,
      hA, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, middleCompCell,
      mul_add] at hc htail hmajor ⊢
    linarith only [hc, htail, hmajor]

/-- With nonnegative source values at both ends, the RH compensation sum is
bounded by the supplied main-integral and absolute-variation caps. -/
public theorem middle_comp_mangoldt_le (hRH : RiemannHypothesis) (P : Polynomial ℚ) (N : ℕ)
    (hN : P.natDegree ≤ N) (hs : List ℚ) (hw : ∀ w ∈ hs, 0 < w) (a : ℚ) {X I V : ℝ}
    (hX : 1000000 ≤ X) (h0 : 0 ≤ P.eval₂ (Rat.castHom ℝ) 0)
    (hr : 0 ≤ P.eval₂ (Rat.castHom ℝ) (hs.sum : ℝ))
    (hI :
      (∫ v in (0 : ℝ)..(hs.sum : ℝ), Real.exp (-(a + (1 / 2 : ℝ)) * v) * middleCompOn P N hs 0 v) ≤
        I)
    (hV : middleCompVariation P N a (a - 1 / 2) hs 0 ≤ V) :
    let b := (hs.sum : ℝ)
    let F := middleCompWeight (middleCompOn P N hs 0) X b (a : ℝ)
    (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp b⌋₊, ArithmeticFunction.vonMangoldt n * F n) ≤
      Real.sqrt X * Real.exp (b / 2) * I + Real.log (X * Real.exp b) ^ 2 / 24 * V := by
  intro b F
  have hb : (hs.sum : ℝ) = b := rfl
  have hp : 0 < X := (by norm_num only : (0 : ℝ) < 1000000).trans_le hX
  have hzero : middleCompOn P N hs 0 0 = 0 := by
    simpa only [Rat.cast_zero, max_eq_left (neg_nonpos.mpr h0)] using
      middle_comp_on_start P N hN hs hw 0
  have hend : middleCompOn P N hs 0 b = 0 := by
    have he := middle_comp_on_end hN hw 0 (v := b) (by rw [zero_add, hb])
    simpa only [zero_add, max_eq_left (neg_nonpos.mpr hr)] using he
  have ha : 1000000 ≤ X * Real.exp (b - ((0 + hs.sum : ℚ) : ℝ)) := by
    simpa only [b, zero_add, sub_self, Real.exp_zero, mul_one] using hX
  have h := middle_comp_abel hRH P N hN hs hw 0 (b := b) a hp ha
  simp only [zero_add, Rat.cast_zero, hb] at h
  rw [middle_comp_weight_at hp (l := (0 : ℝ)), middle_comp_weight_at hp (l := b), hzero, hend] at h
  simp only [mul_zero, add_zero, sub_zero, sub_self, Real.exp_zero, mul_one] at h
  exact
    h.trans
      (add_le_add
        (mul_le_mul_of_nonneg_left hI (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le))
        (mul_le_mul_of_nonneg_left hV (div_nonneg (sq_nonneg _) (by norm_num only))))

/-- For character weights between `-1` and `3`, a compensation sum cap bounds
the signed Euler contribution from below. -/
public theorem middle_comp_signed_lower (P : Polynomial ℚ) (N : ℕ) (hN : P.natDegree ≤ N)
    (hs : List ℚ) (hw : ∀ w ∈ hs, 0 < w) (a : ℚ) {X U : ℝ} (hX : 0 < X) (τ : ℕ → ℝ)
    (hτ : ∀ m, -1 ≤ τ m ∧ τ m ≤ 3)
    (hU :
      (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp (hs.sum : ℝ)⌋₊,
          ArithmeticFunction.vonMangoldt n *
            middleCompWeight (middleCompOn P N hs 0) X (hs.sum : ℝ) (a : ℝ) n) ≤
        U) :
    let b := (hs.sum : ℝ)
    let F := middleCompWeight (P.eval₂ (Rat.castHom ℝ) ·) X b (a : ℝ)
    (-(∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp b⌋₊, ArithmeticFunction.vonMangoldt n * F n) - 4 * U ≤
      (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp b⌋₊,
        ArithmeticFunction.vonMangoldt n * (τ n * F n))) := by
  intro b F
  let C := middleCompWeight (middleCompOn P N hs 0) X b (a : ℝ)
  let cells := Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp b⌋₊
  have hb : 0 ≤ b := Rat.cast_nonneg.mpr (List.sum_nonneg fun w hm ↦ (hw w hm).le)
  have hXB : X ≤ X * Real.exp b := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_exp hb) hX.le
  have hp :
    ∀ m ∈ cells,
      -(ArithmeticFunction.vonMangoldt m * F m) - 4 * (ArithmeticFunction.vonMangoldt m * C m) ≤
        ArithmeticFunction.vonMangoldt m * (τ m * F m) := by
    intro m hm
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hm
    have hmem : (m : ℝ) ∈ Set.Icc (X * Real.exp (b - b)) (X * Real.exp (b - 0)) := by
      simp only [sub_self, Real.exp_zero, mul_one, sub_zero]
      exact ⟨((Nat.floor_lt hX.le).mp hlo).le, (Nat.le_floor_iff (hX.le.trans hXB)).mp hhi⟩
    have hv := middle_log_mem hX hmem
    have hc :=
      middle_comp_on_nonneg (l := (0 : ℚ)) hN hw (by simpa only [Rat.cast_zero, zero_add] using hv)
    let v := b - Real.log ((m : ℝ) / X)
    let p := P.eval₂ (Rat.castHom ℝ) v
    let c := middleCompOn P N hs 0 v
    have h1 : 0 ≤ (τ m + 1) * (p + c) := mul_nonneg (by linarith only [(hτ m).1]) hc.2
    have h2 : 0 ≤ (3 - τ m) * c := mul_nonneg (by linarith only [(hτ m).2]) hc.1
    have ht : -p - 4 * c ≤ τ m * p := by nlinarith only [h1, h2]
    let w := (m : ℝ) ^ (-(1 / 2) : ℝ) * Real.exp (-(a : ℝ) * v)
    have hw0 : 0 ≤ w := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le
    change
      -(ArithmeticFunction.vonMangoldt m * (w * p)) -
          4 * (ArithmeticFunction.vonMangoldt m * (w * c)) ≤
        ArithmeticFunction.vonMangoldt m * (τ m * (w * p))
    nlinarith only [mul_le_mul_of_nonneg_left ht
        (mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg : 0 ≤ ArithmeticFunction.vonMangoldt m)
          hw0)]
  have H := Finset.sum_le_sum hp
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at H
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_left hU (by norm_num only)) _).trans H

/-- Join the known Euler terms with the compensated terms above the cutoff. -/
public theorem middle_comp_euler_lower (P : Polynomial ℚ) (N : ℕ) (hN : P.natDegree ≤ N)
    (hs : List ℚ) (hw : ∀ w ∈ hs, 0 < w) (a : ℚ) {X U : ℝ} (hX : 0 < X) (τ : ℕ → ℝ)
    (hτ : ∀ m, -1 ≤ τ m ∧ τ m ≤ 3)
    (hknown : ∀ m ≤ ⌊X⌋₊, ArithmeticFunction.vonMangoldt m ≠ 0 → τ m = 3)
    (hU :
      (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp (hs.sum : ℝ)⌋₊,
          ArithmeticFunction.vonMangoldt n *
            middleCompWeight (middleCompOn P N hs 0) X (hs.sum : ℝ) (a : ℝ) n) ≤
        U) :
    let b := (hs.sum : ℝ)
    let F := middleCompWeight (P.eval₂ (Rat.castHom ℝ) ·) X b (a : ℝ)
    (4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * F n) -
        (∑ n ∈ Finset.Ioc 0 ⌊X * Real.exp b⌋₊, ArithmeticFunction.vonMangoldt n * F n) -
        4 * U ≤
      ∑ n ∈ Finset.Ioc 0 ⌊X * Real.exp b⌋₊, ArithmeticFunction.vonMangoldt n * (τ n * F n)) := by
  intro b F
  have hb : 0 ≤ b := Rat.cast_nonneg.mpr (List.sum_nonneg fun w hm ↦ (hw w hm).le)
  have hx : X ≤ X * Real.exp b := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.one_le_exp hb) hX.le
  have hd : Disjoint (Finset.Ioc 0 ⌊X⌋₊) (Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp b⌋₊) :=
    Finset.disjoint_left.mpr
      (fun _ h₁ h₂ ↦ (not_lt_of_ge (Finset.mem_Ioc.mp h₁).2) (Finset.mem_Ioc.mp h₂).1)
  have hknownSum :
    (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * (τ n * F n)) =
      3 * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * F n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hz : ArithmeticFunction.vonMangoldt n = 0
    · simp only [hz, zero_mul, mul_zero]
    · rw [hknown n (Finset.mem_Ioc.mp hn).2 hz, mul_left_comm]
  have ht := middle_comp_signed_lower P N hN hs hw a hX τ hτ hU
  change
    -(∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * Real.exp b⌋₊, ArithmeticFunction.vonMangoldt n * F n) - 4 * U ≤
      _ at ht
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (Nat.floor_mono hx), Finset.sum_union hd,
    Finset.sum_union hd, hknownSum]
  linarith only [ht]

/-- The middle log range lies above the analytic Chebyshev cutoff. -/
private theorem middle_exp_cutoff_ge_million {s : ℝ} (hs : 20 ≤ s) : 1000000 ≤ Real.exp s := by
  have h := Real.pow_div_factorial_le_exp 20 (by norm_num only : (0 : ℝ) ≤ 20) 9
  exact
    ((by norm_num only [Nat.factorial] : (1000000 : ℝ) ≤ 20 ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)).trans
          h).trans
      (Real.exp_le_exp.mpr hs)

/-- Under RH, combine the known Euler terms and analytic compensation charges
for a cutoff with logarithm at least `20`. -/
public theorem middle_comp_rh_euler_lower (hRH : RiemannHypothesis) (P : Polynomial ℚ) (N : ℕ)
    (hN : P.natDegree ≤ N) (hs : List ℚ) (hw : ∀ w ∈ hs, 0 < w) (a : ℚ) {s I V : ℝ} (hs0 : 20 ≤ s)
    (h0 : 0 ≤ P.eval₂ (Rat.castHom ℝ) 0) (hr : 0 ≤ P.eval₂ (Rat.castHom ℝ) (hs.sum : ℝ))
    (hI :
      (∫ v in (0 : ℝ)..(hs.sum : ℝ), Real.exp (-(a + (1 / 2 : ℝ)) * v) * middleCompOn P N hs 0 v) ≤
        I)
    (hV : middleCompVariation P N a (a - 1 / 2) hs 0 ≤ V) (τ : ℕ → ℝ) (hτ : ∀ m, -1 ≤ τ m ∧ τ m ≤ 3)
    (hknown : ∀ m ≤ ⌊Real.exp s⌋₊, ArithmeticFunction.vonMangoldt m ≠ 0 → τ m = 3) :
    let b := (hs.sum : ℝ)
    let X := Real.exp s
    let F := middleCompWeight (P.eval₂ (Rat.castHom ℝ) ·) X b (a : ℝ)
    (4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * F n) -
        (∑ n ∈ Finset.Ioc 0 ⌊X * Real.exp b⌋₊, ArithmeticFunction.vonMangoldt n * F n) -
        4 * (Real.exp ((s + b) / 2) * I + (s + b) ^ 2 / 24 * V) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊X * Real.exp b⌋₊, ArithmeticFunction.vonMangoldt n * (τ n * F n)) := by
  intro b X F
  have hcap :=
    middle_comp_mangoldt_le hRH P N hN hs hw a (middle_exp_cutoff_ge_million hs0) h0 hr hI hV
  have hlog : Real.log (X * Real.exp b) = s + b := by
    rw [show X = Real.exp s from rfl, ← Real.exp_add, Real.log_exp]
  have hsqrt : Real.sqrt X * Real.exp (b / 2) = Real.exp ((s + b) / 2) := by
    rw [show X = Real.exp s from rfl, ← Real.exp_half, ← Real.exp_add, add_div]
  dsimp only at hcap
  rw [show Real.exp s = X from rfl, show (hs.sum : ℝ) = b from rfl, hlog, hsqrt] at hcap
  exact middle_comp_euler_lower P N hN hs hw a (Real.exp_pos s) τ hτ hknown hcap

end PseudoPrime.PrimeTestBounds.MillerRabin

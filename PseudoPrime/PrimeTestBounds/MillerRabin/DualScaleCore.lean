/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularDualScaleNumeric
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedContourBounds
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Dual-scale budgets and all-factor witness reduction -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A dual-scale quadratic cutoff with certified entrance, roots, logarithm and strict margin.
The fields control the local and large-index branches for every scale above the entrance;
a separate Gaussian witness handles the remaining three-factor branch. -/
structure DualScaleCore where
  C : ℝ
  T : ℝ
  a : ℝ
  v : ℝ
  ell : ℝ
  entry : 1000000 ≤ T
  root : 1 / 2 < a
  localBudget : 14 < (a - 1 / 2) * T
  square : a ^ 2 ≤ C
  upper : C ≤ 1
  fourth : 0 < v ∧ v ^ 2 ≤ T
  logLower : ell ≤ Real.log (C * T ^ 2)
  margin :
    (36 + max 0 (36 - ell) + (1456 + 13 / 10000000) / v) * T + 12065 < (68 - 3 / 10000) * a * T

/-- The cutoff has the certified square-root and fourth-root bounds above its entrance. -/
theorem dualCore_roots (f : DualScaleCore) {L : ℝ} (hL : f.T ≤ L) :
    let x := f.C * L ^ 2;
    1 < x ∧ f.a * L ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / f.v := by
  have hLp : 0 < L := by linarith only [f.entry, hL]
  have ha : 0 < f.a := by linarith only [f.root]
  have hC : 0 ≤ f.C := (sq_nonneg f.a).trans f.square
  have hl : f.a * L ≤ Real.sqrt (f.C * L ^ 2) := by
    apply (Real.le_sqrt (mul_nonneg ha.le hLp.le) (mul_nonneg hC (sq_nonneg L))).2
    nlinarith only [mul_le_mul_of_nonneg_right f.square (sq_nonneg L)]
  have hh : L / 2 ≤ Real.sqrt (f.C * L ^ 2) := by
    nlinarith only [hl, mul_le_mul_of_nonneg_right f.root.le hLp.le]
  have hx : 1 < f.C * L ^ 2 := by
    nlinarith only [Real.sq_sqrt (mul_nonneg hC (sq_nonneg L)), hh, hL, f.entry]
  have hu : Real.sqrt (f.C * L ^ 2) ≤ L := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hLp.le, by nlinarith only [mul_le_mul_of_nonneg_right f.upper (sq_nonneg L)]⟩
  have ht : ((f.C * L ^ 2) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (f.C * L ^ 2) := by
    have he := Real.rpow_mul (zero_lt_one.trans hx).le (1 / 4) 2
    norm_num only [Real.rpow_two] at he
    rw [Real.sqrt_eq_rpow]
    exact he.symm
  have hv : f.v ^ 2 ≤ L := f.fourth.2.trans hL
  have hquarter : (f.C * L ^ 2) ^ (1 / 4 : ℝ) ≤ L / f.v := by
    apply (le_div_iff₀ f.fourth.1).2
    have hmul := mul_le_mul_of_nonneg_right hu (sq_nonneg f.v)
    have hmul' := mul_le_mul_of_nonneg_left hv hLp.le
    have hp := Real.rpow_nonneg (zero_lt_one.trans hx).le (1 / 4)
    nlinarith only [hmul, hmul', ht, mul_nonneg hp f.fourth.1.le, hLp]
  exact ⟨hx, hl, hu, hquarter⟩

/-- At large index, the core's strict margin implies the complete dual-scale gap.
Both inverse-scale terms and the nonnegative triangular profile are retained. -/
theorem dualCore_gap (f : DualScaleCore) {L h : ℝ} (hL : f.T ≤ L) (hh : 1000000000000 ≤ h) :
    let x := f.C * L ^ 2;
    300000000 * (Real.sqrt x + Real.sqrt x⁻¹) + 1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        (h - 1) * ((36 + LLS.PaperStatements.triangularKernelProfile 18 x) * L + 11964) <
      h *
        (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
          36 * L / (Real.sqrt x - 1)) := by
  let x := f.C * L ^ 2
  have hLp : 0 < L := by linarith only [f.entry, hL]
  have hhp : 0 < h := by linarith only [hh]
  have hb := dualCore_roots f hL
  change 1 < x ∧ f.a * L ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / f.v at hb
  have hT : 0 ≤ f.T := by linarith only [f.entry]
  have hC : 0 ≤ f.C := (sq_nonneg f.a).trans f.square
  have hbase : f.C * f.T ^ 2 ≤ x := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hT hLp.le).mpr hL) hC
  have hbase0 : 0 < f.C * f.T ^ 2 := by
    have ha : 0 < f.a := by linarith only [f.root]
    have hc : 0 < f.C := lt_of_lt_of_le (sq_pos_of_pos ha) f.square
    exact mul_pos hc (sq_pos_of_pos (by linarith only [f.entry]))
  have hlog : f.ell ≤ Real.log x := f.logLower.trans (Real.log_le_log hbase0 hbase)
  have hp : LLS.PaperStatements.triangularKernelProfile 18 x ≤ max 0 (36 - f.ell) := by
    unfold LLS.PaperStatements.triangularKernelProfile
    rw [abs_of_nonneg (Real.log_nonneg (le_of_lt hb.1))]
    norm_num only
    exact max_le_max_left 0 (sub_le_sub_left hlog 36)
  have hp0 : 0 ≤ LLS.PaperStatements.triangularKernelProfile 18 x :=
    LLS.PaperStatements.triangularKernelProfile_nonneg 18 x
  have hinv : x⁻¹ ≤ 1 := (inv_le_one₀ (zero_lt_one.trans hb.1)).2 hb.1.le
  have hinv0 : 0 ≤ x⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hb.1).le
  have hsInv : Real.sqrt x⁻¹ ≤ 1 := Real.sqrt_le_one.mpr hinv
  have hrInv : (x⁻¹) ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hinv0 hinv (by norm_num only)
  have hden : 0 < Real.sqrt x - 1 := by
    have hh' : L / 2 ≤ Real.sqrt x := by
      nlinarith only [hb.2.1, mul_le_mul_of_nonneg_right f.root.le hLp.le]
    linarith only [hh', hL, f.entry]
  have hpole : 36 * L / (Real.sqrt x - 1) ≤ 100 := by
    apply (div_le_iff₀ hden).mpr
    have hh' : L / 2 ≤ Real.sqrt x := by
      nlinarith only [hb.2.1, mul_le_mul_of_nonneg_right f.root.le hLp.le]
    linarith only [hh', hL, f.entry]
  have hS : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hQ : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg (zero_lt_one.trans hb.1).le _
  have hM : 0 ≤ max 0 (36 - f.ell) := le_max_left _ _
  have hpc : 0 ≤ (36 + LLS.PaperStatements.triangularKernelProfile 18 x) * L + 11964 :=
    add_nonneg (mul_nonneg (add_nonneg (by norm_num only) hp0) hLp.le) (by norm_num only)
  have hprofile := mul_le_mul_of_nonneg_right hp hLp.le
  have hidx := mul_le_mul_of_nonneg_right (by linarith only [] : h - 1 ≤ h) hpc
  have hbound :=
    mul_le_mul_of_nonneg_left
      (show
        (36 + LLS.PaperStatements.triangularKernelProfile 18 x) * L + 11964 ≤
          (36 + max 0 (36 - f.ell)) * L + 11964
        by nlinarith only [hprofile])
      hhp.le
  have hpr := mul_le_mul_of_nonneg_right hh hS
  have hpq := mul_le_mul_of_nonneg_right hh hQ
  have hu :
    300000000 * (Real.sqrt x + Real.sqrt x⁻¹) + 1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        (h - 1) * ((36 + LLS.PaperStatements.triangularKernelProfile 18 x) * L + 11964) ≤
      h *
        ((3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) +
          (36 + max 0 (36 - f.ell)) * L +
          11965) := by
    nlinarith only [hidx, hbound, hpr, hpq, hsInv, hrInv, hh]
  let d := (68 - 3 / 10000 : ℝ) * f.a - (36 + max 0 (36 - f.ell) + (1456 + 13 / 10000000 : ℝ) / f.v)
  have hmargin : 12065 < d * f.T := by
    dsimp only [d]
    nlinarith only [f.margin]
  have hd : 0 < d := by
    by_contra hn
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hT
    linarith only [hm, hmargin]
  have hmul := mul_le_mul_of_nonneg_left hL hd.le
  have hE := mul_nonneg hS (Real.exp_pos (-18)).le
  have hg :
    (3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) +
        (36 + max 0 (36 - f.ell)) * L +
        11965 <
      Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
        36 * L / (Real.sqrt x - 1) := by
    have hm : 12065 < d * L := hmargin.trans_le hmul
    dsimp only [d] at hm
    have hquarter := hb.2.2.2
    simp only [div_eq_mul_inv] at hm hquarter
    nlinarith only [hb.2.1, hquarter, hpole, hm, hE]
  exact hu.trans_lt (mul_lt_mul_of_pos_left hg hhp)

/-- The core's local margin bounds the local subgroup cutoff above its entrance. -/
theorem dualCore_local (f : DualScaleCore) {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hsize : q ^ 2 ≤ 10 ^ 12 * n) (hL : f.T ≤ Real.log n) :
    max (3000 : ℝ) (Real.log q ^ 2) ≤ f.C * Real.log n ^ 2 := by
  have hR : (q : ℝ) ^ 2 ≤ (10 : ℝ) ^ 12 * n := by exact_mod_cast hsize
  have hl := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hq) 2) hR
  rw [Real.log_pow, Real.log_mul (pow_ne_zero _ (by norm_num only)) (Nat.cast_pos.mpr hn).ne',
    Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hLp : 0 < Real.log n := by linarith only [hL, f.entry]
  have ha : 0 < f.a := by linarith only [f.root]
  have hmul := mul_le_mul_of_nonneg_left hL (by linarith only [f.root] : (0 : ℝ) ≤ f.a - 1 / 2)
  have hcap : Real.log q ≤ f.a * Real.log n := by
    nlinarith only [hl, log_ten_lt_seven_thirds, f.localBudget, hmul]
  have hp : 0 ≤ f.a * Real.log n := mul_nonneg ha.le hLp.le
  have hs := (sq_le_sq₀ (Real.log_natCast_nonneg q) hp).mpr hcap
  have hsq := mul_le_mul_of_nonneg_right f.square (sq_nonneg (Real.log n))
  have hbase : (1 / 4 : ℝ) ≤ f.C := by nlinarith only [f.root, f.square]
  have hc := mul_le_mul_of_nonneg_right hbase (sq_nonneg (Real.log n))
  apply max_le
  · nlinarith only [hc, hL, f.entry]
  · nlinarith only [hs, hsq]

/-- Under GRH and a large Fermat-subgroup index, the dual gap gives a rejecting prime.
A prime factor is nonunit and an outside prime cannot pass the strong test. -/
theorem exists_prime_dualCoreIndex (f : DualScaleCore) {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hi : 1000000000000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : f.T ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.C * Real.log n ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hiR : (1000000000000 : ℝ) ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by exact_mod_cast hi
  obtain ⟨p, hp, hb, hout⟩ :=
    LLS.PaperStatements.exists_prime_dual_gap (PrimeTest.fermatSubgroup n) hGRH
      (dualCore_roots f hL).1 (dualCore_gap f hL hiR)
  refine ⟨p, hp, hb, ?_⟩
  intro hpass
  rcases hout with hd | hout
  · have hcop :=
      (ZMod.isUnit_iff_coprime p n).mp (PrimeTest.strongMillerRabinPass_isUnit hn ho hpass)
    exact (hp.coprime_iff_not_dvd.mp hcop) hd
  · exact hout (PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn ho hpass)

/-- Under GRH, the dual core gives a rejecting prime for every odd composite once
the same-cutoff witness for the exceptional triple case is supplied. -/
theorem exists_prime_dualCore (f : DualScaleCore) {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : f.T ≤ Real.log n)
    (htriple :
      Squarefree n →
        n.primeFactors.card = 3 →
        (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) →
        (∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1)) →
        ∃ p : ℕ,
          p.Prime ∧
            (p : ℝ) ≤ f.C * Real.log n ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.C * Real.log n ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 12
  · have h36 : 10 ^ 36 ≤ n :=
      decimal_le_of_log_upper (Nat.zero_lt_of_lt hn)
        (by
          norm_num only [Nat.cast_ofNat]; linarith only [hL, f.entry])
    have hJ : (10 ^ 12 : ℕ) ^ 3 ≤ n := by simpa only [← pow_mul, Nat.reduceMul] using h36
    rcases
      localSubgroup_or_uniformKorseltTriple hn ho hc (PrimeTest.fermatSubgroup n) le_rfl
        (by norm_num only : 1 ≤ 10 ^ 12) hJ hi with
      hl | ht
    · obtain ⟨q, hq, hqn, hsize, K, hK, hpass⟩ := hl
      have hqp : 0 < q := (by norm_num only : 0 < 2).trans_le hq
      let : NeZero q := ⟨hqp.ne'⟩
      obtain ⟨p, hp, hb, hr⟩ :=
        exists_prime_witness_le_local_subgroup_envelope hn ho hq hqn K hK hpass hGRH
      exact ⟨p, hp, hb.trans (dualCore_local f (Nat.zero_lt_of_lt hn) hqp hsize hL), hr⟩
    · exact htriple ht.1 ht.2.1 ht.2.2.1 ht.2.2.2
  · exact exists_prime_dualCoreIndex f hn ho (by exact_mod_cast (lt_of_not_ge hi).le) hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin

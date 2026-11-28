/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleCommonMass
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterIdentity576

/-! # Sixth-pole mass saving from common-sign primes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Equal nonzero local Jacobi signs make the pair character equal to one. -/
private theorem pair_one_of_equal_sign {p q b : ℕ} [NeZero p] [NeZero q] (hp : Odd p) (hq : Odd q)
    (hc : (b : ℤ).gcd p = 1) (he : jacobiSym b p = jacobiSym b q) :
    NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq) (b : ZMod (p * q)) = 1 := by
  have h := NumberTheory.complexJacobiNumeratorCharacter_apply_int (p * q) (hp.mul hq) (b : ℤ)
  rw [jacobiSym.mul_right, ← he] at h
  rw [Int.cast_natCast] at h
  rcases jacobiSym.eq_one_or_neg_one hc with ht | ht <;> rw [ht] at h <;>
    simpa only [Int.cast_mul, Int.cast_neg, Int.cast_one, neg_mul_neg, mul_one] using h

/-- The entire identity-prime Euler series above the quarter-log-square cutoff
retains the certified saving of the common-sign window. -/
private theorem identity_euler_saving_of_window {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] (hp : Odd p) (hq : Odd q) (hr : Odd r) {R : ℝ} (hR : 287 ≤ R)
    (hP : R ^ 4 < p) (hQ : R ^ 4 < q) {c₀ : ℝ}
    (hsave :
      let v := 2 * Real.log R
      let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
      let w :=
        s.filter
          (fun (l : ℕ) => (jacobiSym l p = jacobiSym l q ∧ jacobiSym l q = jacobiSym l r) ∧ l.Prime)
      c₀ < 4 * ∑ l ∈ w, Real.log l * quarterEulerWeight570 l) :
    let a := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter _ (hq.mul hr)
    c₀ < 4 * ∑' l : ℕ, identityWeight576 a b c (R ^ 2) l := by
  intro a b c
  let v := 2 * Real.log R
  let s := Finset.Ioc ⌊Real.exp v⌋₊ ⌊Real.exp (v + 5)⌋₊
  let w :=
    s.filter
      (fun (l : ℕ) => (jacobiSym l p = jacobiSym l q ∧ jacobiSym l q = jacobiSym l r) ∧ l.Prime)
  have hpos (l : ℕ) : 0 ≤ identityWeight576 a b c (R ^ 2) l := by
    unfold identityWeight576
    split
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (quarter_euler_weight_nonneg_570_all l)
    · exact le_rfl
  have hsum : Summable (identityWeight576 a b c (R ^ 2)) := by
    apply quarter_euler_weight_summable_570.of_nonneg_of_le hpos
    intro l
    unfold identityWeight576
    split
    · exact le_rfl
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (quarter_euler_weight_nonneg_570_all l)
  have hx : Real.exp v = R ^ 2 := by
    dsimp only [v]
    rw [two_mul, Real.exp_add, Real.exp_log (by linarith only [hR] : 0 < R), sq]
  have hEq (l : ℕ) (hl : l ∈ w) :
    identityWeight576 a b c (R ^ 2) l = Real.log l * quarterEulerWeight570 l := by
    obtain ⟨hl', ⟨h₁, h₂⟩, hpr⟩ := Finset.mem_filter.mp hl
    have hcut := (Nat.floor_lt (Real.exp_pos v).le).mp (Finset.mem_Ioc.mp hl').1
    rw [hx] at hcut
    have hcp := triangle_window_gcd_of_large hR (Fact.out : p.Prime) hP hl'
    have hcq := triangle_window_gcd_of_large hR (Fact.out : q.Prime) hQ hl'
    unfold identityWeight576
    rw [ite_eq_left
        ⟨hcut, hpr, pair_one_of_equal_sign hp hq hcp h₁,
          pair_one_of_equal_sign hp hr hcp (h₁.trans h₂), pair_one_of_equal_sign hq hr hcq h₂⟩,
      ArithmeticFunction.vonMangoldt_apply_prime hpr]
  apply hsave.trans_le
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  exact (Finset.sum_congr (s₁ := w) rfl hEq).symm.trans_le (hsum.sum_le_tsum w (fun l _ => hpos l))

/-- The section 86 window yields the certified identity-prime saving 1119/50000. -/
theorem identity_euler_saving_576 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 287 ≤ R)
    (hU : R ≤ 288) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter _ (hq.mul hr)
    1119 / 50000 < 4 * ∑' l : ℕ, identityWeight576 a b c (R ^ 2) l := by
  exact
    identity_euler_saving_of_window hp hq hr hR hP hQ
      (common_prime_euler_saving_576 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR hU hL hRH hP hQ hT
        hb)

/-- The section 99 window yields a saving in the full identity-prime Euler series. -/
theorem identity_euler_saving_600 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 292 ≤ R)
    (hU : R ≤ 300) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter _ (hq.mul hr)
    (if R ≤ 299 then 0.02169 else 0.02179) < 4 * ∑' l : ℕ, identityWeight576 a b c (R ^ 2) l := by
  exact
    identity_euler_saving_of_window hp hq hr (by linarith only [hR]) hP hQ
      (common_prime_euler_saving_600 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR hU hL hRH hP hQ hT
        hb)

/-- On radii 300 through 316, the full identity-prime Euler series preserves the
strict saving 0.02085 certified in the common-sign prime window. -/
theorem identity_euler_saving_to632 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 300 ≤ R)
    (hU : R ≤ 316) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter _ (hq.mul hr)
    0.02085 < 4 * ∑' l : ℕ, identityWeight576 a b c (R ^ 2) l := by
  exact
    identity_euler_saving_of_window hp hq hr (by linarith only [hR]) hP hQ
      (common_prime_euler_saving_to632 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR hU hL hRH hP hQ
        hT hb)

/-- The section 107 window yields a saving in the full identity-prime Euler series. -/
theorem identity_euler_saving_626 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 300 ≤ R)
    (hU : R ≤ 313) (hL : Real.log n = 2 * R) (hRH : RiemannHypothesis) (hP : R ^ 4 < p)
    (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb :
      ∀ b : ℕ, b.Prime → b ≤ ⌊Real.exp (5 / 2)⌋₊ → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter _ (hq.mul hr)
    0.02085 < 4 * ∑' l : ℕ, identityWeight576 a b c (R ^ 2) l := by
  exact
    identity_euler_saving_to632 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR
      (hU.trans (by norm_num only)) hL hRH hP hQ hT hb

/-- For the three pair characters of a uniform triple the sixth-pole mass
retains both the prefix tail bound and the strict common-prime saving. -/
theorem common_triple_mass_upper_576 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 287 ≤ R)
    (hU : R ≤ 288) (hL : Real.log n = 2 * R) (hP : R ^ 4 < p) (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb : ∀ b : ℕ, b.Prime → (b : ℝ) ≤ R ^ 2 → PrimeTest.StrongMillerRabinPass n (b : ZMod n))
    (s : Finset ℕ) (hS : ∀ k ∈ s, (k : ℝ) ≤ R ^ 2) {T : ℝ}
    (htail :
      (∑' k : ℕ, ArithmeticFunction.vonMangoldt k * quarterEulerWeight570 k) -
          (∑ k ∈ s, ArithmeticFunction.vonMangoldt k * quarterEulerWeight570 k) ≤
        T) :
    let a := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter _ (hq.mul hr)
    quarterMass570 a + quarterMass570 b + quarterMass570 c <
      3 / 4 * R - 13386 / 1000 + 4 * T - 1119 / 50000 := by
  intro a b c
  have hcut : Real.exp (5 / 2) ≤ R ^ 2 := by
    have hh := pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by decide : 3 ≠ 0)
    rw [← Real.exp_natCast_mul] at hh
    norm_num only [Nat.cast_ofNat, mul_one] at hh
    exact
      (Real.exp_le_exp.mpr (by norm_num only : (5 / 2 : ℝ) ≤ 3)).trans
        (hh.le.trans
          (le_trans (b := (287 : ℝ) ^ 2) (by norm_num only)
            (pow_le_pow_left₀ (by norm_num only) hR 2)))
  have hsave :=
    identity_euler_saving_576 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR hU hL hGRH.riemann hP hQ
      hT (fun l hl h => hb l hl (((Nat.le_floor_iff (Real.exp_pos _).le).mp h).trans hcut))
  have d₁ : p * q ∣ n := he ▸ dvd_mul_right _ _
  have d₂ : p * r ∣ n := by
    rw [he, mul_right_comm]; exact dvd_mul_right _ _
  have d₃ : q * r ∣ n := by
    rw [he, Nat.mul_assoc]; exact dvd_mul_left _ _
  have pa := pair_character_primitive hs d₁ (hp.mul hq)
  have pb := pair_character_primitive hs d₂ (hp.mul hr)
  have pc := pair_character_primitive hs d₃ (hq.mul hr)
  have bound (i j : ℕ) [Fact i.Prime] [Fact j.Prime] : 1 < i * j :=
    (Fact.out : i.Prime).one_lt.trans_le (Nat.le_mul_of_pos_right i (Fact.out : j.Prime).pos)
  have na := pair_character_ne_one hs d₁ (hp.mul hq) (bound p q)
  have nb := pair_character_ne_one hs d₂ (hp.mul hr) (bound p r)
  have nc := pair_character_ne_one hs d₃ (hq.mul hr) (bound q r)
  have hmain :=
    mass_identity_series_576 a b c (bound p q) (bound p r) (bound q r) (hGRH _ a pa) (hGRH _ b pb)
      (hGRH _ c pc) pa pb pc na nb nc (inv_ne_one.mpr na) (inv_ne_one.mpr nb) (inv_ne_one.mpr nc) s
      hS
      (fun l => by
        simpa only [a, b, c, Int.cast_natCast] using
          pair_character_sum_ge_neg_one (l : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr))
      (fun l hl h =>
        pair_character_nat_eq_one hn ho hp hq ((dvd_mul_right _ _).trans d₁)
          ((dvd_mul_left _ _).trans d₁) d₁ hk hj hv l (hb l hl h))
      (fun l hl h =>
        pair_character_nat_eq_one hn ho hp hr ((dvd_mul_right _ _).trans d₂)
          ((dvd_mul_left _ _).trans d₂) d₂ hk hm hw l (hb l hl h))
      (fun l hl h =>
        pair_character_nat_eq_one hn ho hq hr ((dvd_mul_right _ _).trans d₃)
          ((dvd_mul_left _ _).trans d₃) d₃ hj hm (hw.trans hv.symm) l (hb l hl h))
      (R := R)
      (by
        rw [pair_level_log_sum he, hL]; linarith only)
      hGRH.riemann (pair_character_even_of_korselt hn ho hp hq hk hj hv)
      (pair_character_even_of_korselt hn ho hp hr hk hm hw)
      (pair_character_even_of_korselt hn ho hq hr hj hm (hw.trans hv.symm)) htail
  exact hmain.trans_lt (sub_lt_sub_left hsave _)

/-- The actual three pair characters have sixth-pole mass strictly below three quarters
of the radius minus 12.78998 throughout the section 86 interval. -/
theorem common_triple_mass_numeric_576 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hs : Squarefree n) (he : n = p * q * r) (hp : Odd p) (hq : Odd q)
    (hr : Odd r) (hk : p - 1 ∣ n - 1) (hj : q - 1 ∣ n - 1) (hm : r - 1 ∣ n - 1)
    (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hw : padicValNat 2 (r - 1) = padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {R : ℝ} (hR : 287 ≤ R)
    (hU : R ≤ 288) (hL : Real.log n = 2 * R) (hP : R ^ 4 < p) (hQ : R ^ 4 < q) (hT : R ^ 4 < r)
    (hb : ∀ b : ℕ, b.Prime → (b : ℝ) ≤ R ^ 2 → PrimeTest.StrongMillerRabinPass n (b : ZMod n)) :
    let a := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter _ (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter _ (hq.mul hr)
    quarterMass570 a + quarterMass570 b + quarterMass570 c < 3 / 4 * R - 639499 / 50000 := by
  intro a b c
  have hx : 2701 ≤ R ^ 2 :=
    (by norm_num only : (2701 : ℝ) ≤ 287 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hR 2)
  have hy : R ^ 2 ≤ 1000000 :=
    (pow_le_pow_left₀ (by linarith only [hR]) hU 2).trans (by norm_num only)
  have hm0 :=
    common_triple_mass_upper_576 hn ho hs he hp hq hr hk hj hm hv hw hGRH hR hU hL hP hQ hT hb
      (Finset.Ioc 0 ⌊R ^ 2⌋₊)
      (fun k h => (Nat.le_floor_iff (sq_nonneg R)).mp (Finset.mem_Ioc.mp h).2)
      (positive_tail_upper_570 hGRH.riemann hx hy)
  dsimp only at hm0
  linarith only [hm0, radius_tail_numeric_576 hR hU]

end PseudoPrime.PrimeTestBounds.MillerRabin

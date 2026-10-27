/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.LogarithmicEuler
public import Mathlib.Algebra.Prime.Lemmas

/-! # Truncated logarithm independence modulo X^p -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The truncated logarithm has constant coefficient zero for every modulus. Each summand has
positive exponent. -/
theorem truncatedLog_coeff_zero {p : ℕ} : (truncatedLog p).coeff 0 = 0 := by
  rw [truncatedLog, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [ite_eq_right (Nat.succ_ne_zero j).symm, mul_zero]

/-- For prime p the truncated logarithm has linear coefficient one. Only the first summand
contributes, and p>=2 ensures its presence. -/
theorem truncatedLog_coeff_one {p : ℕ} [Fact p.Prime] : (truncatedLog p).coeff 1 = 1 := by
  rw [truncatedLog, Polynomial.finsetSum_coeff, Finset.sum_eq_single 0]
  · simp only [Nat.zero_add, Nat.cast_one, inv_one, Polynomial.C_1, pow_one, one_mul,
      Polynomial.coeff_X_one]
  · intro j _ hj
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have hn : j + 1 ≠ 1 := by
      intro h
      exact hj (Nat.add_right_cancel (show j + 1 = 0 + 1 from h))
    rw [ite_eq_right hn.symm, mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.sub_pos_of_lt (Nat.Prime.one_lt Fact.out)))).elim

/-- Over a field, G with constant coefficient zero and nonzero linear coefficient preserves
order at zero. If deg(F)<B and X^B divides F(G), then F=0. Exhibit a nonzero coefficient using
the factorization at zero. -/
theorem eq_zero_of_X_pow_dvd_comp {K : Type*} [Field K] (G F : Polynomial K) (hG0 : G.coeff 0 = 0)
    (hG1 : G.coeff 1 ≠ 0) {B : ℕ} (hF : F.natDegree < B) (hdiv : Polynomial.X ^ B ∣ F.comp G) :
    F = 0 := by
  by_contra hF0
  obtain ⟨U, hU⟩ := Polynomial.X_dvd_iff.mpr hG0
  have hU0 : U.coeff 0 ≠ 0 := by
    have he := Polynomial.coeff_X_mul U 0
    rw [← hU] at he
    exact he ▸ hG1
  obtain ⟨H, hH, hH0⟩ := F.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hF0 0
  simp only [Polynomial.C_0, sub_zero] at hH hH0
  let t := F.rootMultiplicity 0
  have hHc : H.coeff 0 ≠ 0 := fun hz ↦ hH0 (Polynomial.X_dvd_iff.mpr hz)
  have ht : t ≤ F.natDegree := by
    have hd := Polynomial.natDegree_le_of_dvd (show Polynomial.X ^ t ∣ F from ⟨H, hH⟩) hF0
    simpa only [Polynomial.natDegree_X_pow] using hd
  have hf : F.comp G = Polynomial.X ^ t * (U ^ t * H.comp G) := by
    rw [hH, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp, hU, mul_pow]
    ring
  have hcoeff := (Polynomial.X_pow_dvd_iff.mp hdiv) t (ht.trans_lt hF)
  rw [hf] at hcoeff
  have he := Polynomial.coeff_X_pow_mul (U ^ t * H.comp G) t 0
  simp only [Nat.zero_add] at he
  have hgEval : G.eval 0 = 0 := by rw [← Polynomial.coeff_zero_eq_eval_zero, hG0]
  rw [he, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_comp, hgEval, ← Polynomial.coeff_zero_eq_eval_zero, ←
    Polynomial.coeff_zero_eq_eval_zero] at hcoeff
  exact (mul_ne_zero (pow_ne_zero t hU0) hHc) hcoeff

/-- For prime p and deg(F)<B, divisibility of (1-X)^a F(f) by X^B forces F=0. Cancel the factor
with nonzero constant term and use the simple zero of f. -/
theorem eq_zero_of_X_pow_dvd_logarithmicBlock {p : ℕ} [Fact p.Prime] (a : ℕ)
    (F : Polynomial (ZMod p)) {B : ℕ} (hF : F.natDegree < B)
    (hdiv : Polynomial.X ^ B ∣ logarithmicBlock a F) : F = 0 := by
  have hnd : ¬(Polynomial.X : Polynomial (ZMod p)) ∣ (1 - Polynomial.X) ^ a := by
    intro h
    have hz := Polynomial.X_dvd_iff.mp h
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_X, sub_zero, one_pow] at hz
    exact one_ne_zero hz
  have hc := Polynomial.prime_X.pow_dvd_of_dvd_mul_left B hnd hdiv
  exact
    eq_zero_of_X_pow_dvd_comp (truncatedLog p) F truncatedLog_coeff_zero
      ((truncatedLog_coeff_one (p := p)) ▸ one_ne_zero) hF hc

/-- For prime p, distinct exponents below p and B times their count<=p, a block sum divisible by
X^(B times count) has all coefficients zero if their degrees are below B. Erase one eigenvalue
with B Euler steps and induct; other shifts preserve nonzero coefficients. -/
theorem logarithmicSum_coefficients_eq_zero {p : ℕ} [Fact p.Prime] (S : Finset ℕ) (B : ℕ) :
    (∀ a ∈ S, a < p) →
      B * S.card ≤ p →
      ∀ F : ℕ → Polynomial (ZMod p),
        (∀ a ∈ S, (F a).natDegree < B) →
          Polynomial.X ^ (B * S.card) ∣ (∑ a ∈ S, logarithmicBlock a (F a)) → ∀ a ∈ S, F a = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro _ _ F _ _ a ha
    exact (Finset.notMem_empty a ha).elim
  | @insert a S ha ih =>
    intro hbounds hbudget F hF hdiv
    have haS : a ∈ insert a S := Finset.mem_insert_self a S
    have hsbudget : B * S.card + B ≤ p := by
      simpa only [Finset.card_insert_of_notMem ha, Nat.mul_add, Nat.mul_one] using hbudget
    have hd :=
      X_pow_dvd_logarithmicSum_erase (insert a S) F a (B * S.card) B haS hsbudget (hF a haS)
        (by simpa only [Finset.card_insert_of_notMem ha, Nat.mul_add, Nat.mul_one] using hdiv)
    rw [Finset.erase_insert ha] at hd
    have hrest : ∀ b ∈ S, F b = 0 := by
      intro b hb
      have hdeg : ∀ b ∈ S, ((affineDerivative ((a : ZMod p) - b) ^ B) (F b)).natDegree < B :=
        fun b hb ↦
        (natDegree_affineDerivative_pow_le _ B _).trans_lt (hF b (Finset.mem_insert_of_mem hb))
      have hz :=
        ih (fun b hb ↦ hbounds b (Finset.mem_insert_of_mem hb)) (by linarith only [hsbudget])
          (fun b ↦ (affineDerivative ((a : ZMod p) - b) ^ B) (F b)) hdeg hd b hb
      have hab : a ≠ b := fun h ↦ ha (h.symm ▸ hb)
      have hc : (a : ZMod p) - b ≠ 0 := by
        apply sub_ne_zero.mpr
        intro he
        have he' := (ZMod.natCast_eq_natCast_iff' a b p).mp he
        rw [Nat.mod_eq_of_lt (hbounds a haS),
          Nat.mod_eq_of_lt (hbounds b (Finset.mem_insert_of_mem hb))] at he'
        exact hab he'
      exact (affineDerivative_pow_eq_zero_iff hc B (F b)).mp hz
    have hsum : ∑ b ∈ S, logarithmicBlock b (F b) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [hrest b hb, logarithmicBlock, Polynomial.zero_comp, mul_zero]
    rw [Finset.sum_insert ha, hsum, add_zero] at hdiv
    have hBa : B ≤ B * (insert a S).card := by
      rw [Finset.card_insert_of_notMem ha, Nat.mul_add, Nat.mul_one]
      exact Nat.le_add_left _ _
    have hFa :=
      eq_zero_of_X_pow_dvd_logarithmicBlock a (F a) (hF a haS)
        ((pow_dvd_pow Polynomial.X hBa).trans hdiv)
    intro b hb
    rcases Finset.mem_insert.mp hb with he | hb
    · exact he ▸ hFa
    · exact hrest b hb

/-- Over a nontrivial commutative ring, composing with 1-X does not increase natural degree. Use
the composition degree bound and linearity of the substitution. -/
theorem natDegree_comp_one_sub_X_le {R : Type*} [CommRing R] [Nontrivial R] (F : Polynomial R) :
    (F.comp (1 - Polynomial.X)).natDegree ≤ F.natDegree := by
  have hd := Polynomial.natDegree_sub_le (1 : Polynomial R) Polynomial.X
  rw [Polynomial.natDegree_one, Polynomial.natDegree_X] at hd
  have hc := Polynomial.natDegree_comp_le (p := F) (q := 1 - Polynomial.X)
  exact
    hc.trans
      (by
        simpa only [max_eq_right (by decide : (0 : ℕ) ≤ 1), mul_one] using
          Nat.mul_le_mul_left F.natDegree hd)

/-- The substitution X maps to 1-X is an involution over any commutative ring. This returns
shifted-basis independence to the original variables. -/
theorem comp_one_sub_X_twice {R : Type*} [CommRing R] (F : Polynomial R) :
    (F.comp (1 - Polynomial.X)).comp (1 - Polynomial.X) = F := by
  rw [Polynomial.comp_assoc, Polynomial.sub_comp, Polynomial.one_comp, Polynomial.X_comp,
    sub_sub_cancel, Polynomial.comp_X]

/-- If every inner coefficient of a nested polynomial has degree below positive B, outer
substitution X maps to 1-X preserves this bound. Each new coefficient is a scalar linear
combination of the old ones. -/
theorem natDegree_coeff_comp_one_sub_X_lt {K : Type*} [Field K] (F : Polynomial (Polynomial K))
    {B : ℕ} (hB : 0 < B) (hF : ∀ a : ℕ, (F.coeff a).natDegree < B) (j : ℕ) :
    ((F.comp (1 - Polynomial.X)).coeff j).natDegree < B := by
  have he (a : ℕ) :
    ((1 - Polynomial.X : Polynomial (Polynomial K)) ^ a).coeff j =
      Polynomial.C (((1 - Polynomial.X : Polynomial K) ^ a).coeff j) := by
    rw [← Polynomial.coeff_map]
    congr 1
    simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X]
  rw [Polynomial.comp, Polynomial.eval₂_eq_sum_range, Polynomial.finsetSum_coeff]
  have hd :=
    Polynomial.natDegree_sum_le_of_forall_le (Finset.range (F.natDegree + 1))
      (fun a ↦ (Polynomial.C (F.coeff a) * (1 - Polynomial.X) ^ a).coeff j)
      (fun a _ ↦
        show ((Polynomial.C (F.coeff a) * (1 - Polynomial.X) ^ a).coeff j).natDegree ≤ B - 1
          by
          rw [Polynomial.coeff_C_mul, he a]
          exact (Polynomial.natDegree_mul_C_le _ _).trans (Nat.le_sub_one_of_lt (hF a)))
  exact hd.trans_lt (Nat.sub_lt hB (by decide : 0 < 1))

/-- For F in (ZMod p)[Y][X], substitute the truncated logarithm f(X) for Y and evaluate the
outer variable at X. The result is a univariate polynomial. -/
noncomputable def logarithmicSubstitution {p : ℕ} (F : Polynomial (Polynomial (ZMod p))) :
    Polynomial (ZMod p) :=
  F.eval₂ (Polynomial.compRingHom (truncatedLog p)) Polynomial.X

/-- Under the bivariate degree hypotheses with AB<=p, X^(AB) does not divide the nonzero
substitution F(X,f(X)). Prove the sharper order bound by Euler elimination; the X^p form follows
immediately. -/
theorem X_pow_product_not_dvd_logarithmicSubstitution {p : ℕ} [Fact p.Prime]
    (F : Polynomial (Polynomial (ZMod p))) {A B : ℕ} (hB : 0 < B) (hA : F.natDegree < A)
    (hF : ∀ a : ℕ, (F.coeff a).natDegree < B) (hAB : A * B ≤ p) (hF0 : F ≠ 0) :
    ¬(Polynomial.X : Polynomial (ZMod p)) ^ (A * B) ∣ logarithmicSubstitution F := by
  intro hdiv
  let G := F.comp (1 - Polynomial.X)
  have hG : G.natDegree < A := (natDegree_comp_one_sub_X_le F).trans_lt hA
  have hGF : ∀ a : ℕ, (G.coeff a).natDegree < B := natDegree_coeff_comp_one_sub_X_lt F hB hF
  have he : logarithmicSubstitution F = ∑ a ∈ Finset.range A, logarithmicBlock a (G.coeff a) := by
    have hc :
      G.eval₂ (Polynomial.compRingHom (truncatedLog p)) (1 - Polynomial.X) =
        logarithmicSubstitution F := by
      dsimp only [G, logarithmicSubstitution]
      rw [Polynomial.eval₂_comp, Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_X,
        sub_sub_cancel]
    rw [← hc, Polynomial.eval₂_eq_sum_range' _ hG]
    apply Finset.sum_congr rfl
    intro a _
    exact mul_comm _ _
  have hAp : A ≤ p := (Nat.le_mul_of_pos_right A hB).trans hAB
  have hzero :=
    logarithmicSum_coefficients_eq_zero (Finset.range A) B
      (fun a ha ↦ (Finset.mem_range.mp ha).trans_le hAp)
      (by simpa only [Finset.card_range, Nat.mul_comm] using hAB) G.coeff (fun a _ ↦ hGF a)
      (by
        rw [← he]
        simpa only [Finset.card_range, Nat.mul_comm] using hdiv)
  have hG0 : G = 0 := by
    apply Polynomial.ext
    intro a
    rw [Polynomial.coeff_zero]
    by_cases ha : a < A
    · exact hzero a (Finset.mem_range.mpr ha)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hG.trans_le (Nat.le_of_not_gt ha))
  apply hF0
  have hi := comp_one_sub_X_twice F
  change G.comp (1 - Polynomial.X) = F at hi
  rw [hG0, Polynomial.zero_comp] at hi
  exact hi.symm

/-- For prime p, nonzero F with outer degree<A and inner coefficient degrees<B, B>0 and AB<=p,
X^p does not divide F(X,f(X)). Shift by 1-X, apply block elimination and invert the shift. This
proves Lemma 17 of arXiv:1302.3839v3. -/
theorem X_pow_not_dvd_logarithmicSubstitution {p : ℕ} [Fact p.Prime]
    (F : Polynomial (Polynomial (ZMod p))) {A B : ℕ} (hB : 0 < B) (hA : F.natDegree < A)
    (hF : ∀ a : ℕ, (F.coeff a).natDegree < B) (hAB : A * B ≤ p) (hF0 : F ≠ 0) :
    ¬(Polynomial.X : Polynomial (ZMod p)) ^ p ∣ logarithmicSubstitution F := by
  intro hdiv
  exact
    X_pow_product_not_dvd_logarithmicSubstitution F hB hA hF hAB hF0
      ((pow_dvd_pow Polynomial.X hAB).trans hdiv)

end PseudoPrime.NumberTheory.Heilbronn

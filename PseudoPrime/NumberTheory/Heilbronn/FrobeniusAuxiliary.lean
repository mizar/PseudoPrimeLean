/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.TruncatedLogIndependence
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.RingTheory.Coprime.Lemmas

/-! # Nonzero Frobenius auxiliary polynomials and multiplicity bounds -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Let a ring homomorphism send every nonzero coefficient of F to a polynomial not divisible by
X^p. If evaluation of F at X^p vanishes, then F=0. Extract the constant coefficient modulo X^p
and induct using divX. -/
theorem eq_zero_of_eval₂_X_pow_eq_zero {R K : Type*} [CommRing R] [Field K] (f : R →+* Polynomial K)
    (p n : ℕ) :
    ∀ F : Polynomial R,
      F.natDegree < n →
        (∀ a : ℕ, F.coeff a ≠ 0 → ¬(Polynomial.X : Polynomial K) ^ p ∣ f (F.coeff a)) →
        F.eval₂ f (Polynomial.X ^ p) = 0 → F = 0 := by
  induction n with
  | zero =>
    intro F hF _ _
    exact (Nat.not_lt_zero _ hF).elim
  | succ n ih =>
    intro F hF hres hval
    have he := congrArg (Polynomial.eval₂ f (Polynomial.X ^ p)) (Polynomial.X_mul_divX_add F)
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C,
      hval] at he
    have h0 : F.coeff 0 = 0 := by
      by_contra hn
      apply hres 0 hn
      refine ⟨-(F.divX.eval₂ f (Polynomial.X ^ p)), ?_⟩
      linear_combination he
    by_cases hd : F.natDegree = 0
    · rw [Polynomial.eq_C_of_natDegree_eq_zero hd, h0, Polynomial.C_0]
    · have hDval : F.divX.eval₂ f (Polynomial.X ^ p) = 0 := by
        rw [h0, map_zero, add_zero] at he
        exact
          (mul_eq_zero.mp he).resolve_left
            (pow_ne_zero p (Polynomial.X_ne_zero : (Polynomial.X : Polynomial K) ≠ 0))
      have hDdeg : F.divX.natDegree < n := by
        rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
        have hcancel := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)
        linarith only [hF, hcancel]
      have hD :=
        ih F.divX hDdeg
          (fun a ha ↦ by
            simpa only [Polynomial.coeff_divX] using
              hres (a + 1) (by simpa only [Polynomial.coeff_divX] using ha))
          hDval
      have he' := Polynomial.X_mul_divX_add F
      rw [hD, h0, mul_zero, Polynomial.C_0, zero_add] at he'
      exact he'.symm

/-- For prime p and AB<=p, a nonzero trivariate polynomial remains nonzero after Y=f(X), Z=X^p,
if each Z-coefficient has X-degree<A and Y-degree<B. Apply bivariate nondivisibility to every
coefficient. -/
theorem frobenius_logarithmic_substitution_ne_zero {p : ℕ} [Fact p.Prime]
    (F : Polynomial (Polynomial (Polynomial (ZMod p)))) {A B : ℕ} (hB : 0 < B) (hAB : A * B ≤ p)
    (hF0 : F ≠ 0) (hX : ∀ c : ℕ, (F.coeff c).natDegree < A)
    (hY : ∀ c a : ℕ, ((F.coeff c).coeff a).natDegree < B) :
    F.eval₂ (Polynomial.eval₂RingHom (Polynomial.compRingHom (truncatedLog p)) Polynomial.X)
        (Polynomial.X ^ p) ≠
      0 := by
  intro hv
  apply hF0
  exact
    eq_zero_of_eval₂_X_pow_eq_zero
      (Polynomial.eval₂RingHom (Polynomial.compRingHom (truncatedLog p)) Polynomial.X) p
      (F.natDegree + 1) F (Nat.lt_succ_self _)
      (fun c hc ↦ X_pow_not_dvd_logarithmicSubstitution (F.coeff c) hB (hX c) (hY c) hAB hc) hv

/-- For every modulus p the truncated logarithm has natural degree at most p-1. Bound each
summand of its defining finite sum. -/
theorem natDegree_truncatedLog_le {p : ℕ} : (truncatedLog p).natDegree ≤ p - 1 := by
  rw [truncatedLog]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact
    (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.natDegree_X_pow_le _).trans (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))

/-- For X-degree<A and Y-degree<B, substitution Y=f(X) has natural degree at most
A-1+(B-1)(p-1). Expand the evaluation and bound each term. -/
theorem natDegree_logarithmicSubstitution_le {p : ℕ} [Fact p.Prime]
    (F : Polynomial (Polynomial (ZMod p))) {A B : ℕ} (hA : F.natDegree < A)
    (hF : ∀ a : ℕ, (F.coeff a).natDegree < B) :
    (logarithmicSubstitution F).natDegree ≤ (A - 1) + (B - 1) * (p - 1) := by
  rw [logarithmicSubstitution, Polynomial.eval₂_eq_sum_range' _ hA]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a ha
  have hc := Polynomial.natDegree_comp_le (p := F.coeff a) (q := truncatedLog p)
  have hcomp : ((F.coeff a).comp (truncatedLog p)).natDegree ≤ (B - 1) * (p - 1) :=
    hc.trans (Nat.mul_le_mul (Nat.le_sub_one_of_lt (hF a)) natDegree_truncatedLog_le)
  have hx : (Polynomial.X ^ a : Polynomial (ZMod p)).natDegree ≤ A - 1 :=
    (Polynomial.natDegree_X_pow_le a).trans (Nat.le_sub_one_of_lt (Finset.mem_range.mp ha))
  have hd := Polynomial.natDegree_mul_le.trans (Nat.add_le_add hcomp hx)
  simpa only [Polynomial.coe_compRingHom_apply, Nat.add_comm] using hd

/-- For a nested trivariate polynomial over ZMod p, substitute Y=f(X), Z=X^p. This is the
univariate auxiliary polynomial used by the Heilbronn Stepanov method. -/
noncomputable def frobeniusLogarithmicSubstitution {p : ℕ}
    (F : Polynomial (Polynomial (Polynomial (ZMod p)))) : Polynomial (ZMod p) :=
  F.eval₂ (Polynomial.eval₂RingHom (Polynomial.compRingHom (truncatedLog p)) Polynomial.X)
    (Polynomial.X ^ p)

/-- For tridegrees<A,B,C the auxiliary substitution has natural degree at most
A-1+(B-1)(p-1)+p(C-1). Bound each coefficient substitution and outer power. -/
theorem natDegree_frobeniusLogarithmicSubstitution_le {p : ℕ} [Fact p.Prime]
    (F : Polynomial (Polynomial (Polynomial (ZMod p)))) {A B C : ℕ} (hZ : F.natDegree < C)
    (hX : ∀ c : ℕ, (F.coeff c).natDegree < A)
    (hY : ∀ c a : ℕ, ((F.coeff c).coeff a).natDegree < B) :
    (frobeniusLogarithmicSubstitution F).natDegree ≤ (A - 1) + (B - 1) * (p - 1) + p * (C - 1) := by
  rw [frobeniusLogarithmicSubstitution, Polynomial.eval₂_eq_sum_range' _ hZ]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro c hc
  have hcoef := natDegree_logarithmicSubstitution_le (F.coeff c) (hX c) (hY c)
  have hp : ((Polynomial.X ^ p : Polynomial (ZMod p)) ^ c).natDegree ≤ p * (C - 1) :=
    Polynomial.natDegree_pow_le.trans
      ((Nat.mul_le_mul_left c (Polynomial.natDegree_X_pow_le p)).trans
        (by
          simpa only [Nat.mul_comm] using
            Nat.mul_le_mul_left p (Nat.le_sub_one_of_lt (Finset.mem_range.mp hc))))
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hcoef hp)

/-- For a nonzero polynomial P over a field, if (X-x)^D divides P for all x in a finite set S,
then card(S)D<=natDegree(P). The coprime powered linear factors have product dividing P. -/
theorem card_mul_le_natDegree_of_pow_dvd {K : Type*} [Field K] (P : Polynomial K) (hP : P ≠ 0)
    (S : Finset K) (D : ℕ) (hroot : ∀ x ∈ S, (Polynomial.X - Polynomial.C x) ^ D ∣ P) :
    S.card * D ≤ P.natDegree := by
  have hd :=
    Finset.prod_dvd_of_coprime
      (fun a _ b _ hab ↦ (Polynomial.pairwise_coprime_X_sub_C Function.injective_id hab).pow) hroot
  have hn := Polynomial.natDegree_le_of_dvd hd hP
  rw [Polynomial.natDegree_prod _ _ (fun x _ ↦ pow_ne_zero D (Polynomial.X_sub_C_ne_zero x))] at hn
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one, Finset.sum_const,
    smul_eq_mul] at hn
  exact hn

/-- For prime p, AB<=p and a nonzero trivariate polynomial of tridegrees<A,B,C, root
multiplicities at least D after Y=f(X), Z=X^p give card(S)D<=A-1+(B-1)(p-1)+p(C-1). Combine
nonvanishing, degree and root bounds. Multiplicity hypotheses remain explicit. -/
theorem card_mul_le_of_frobenius_logarithmic_roots {p : ℕ} [Fact p.Prime]
    (F : Polynomial (Polynomial (Polynomial (ZMod p)))) {A B C : ℕ} (hB : 0 < B) (hAB : A * B ≤ p)
    (hF0 : F ≠ 0) (hZ : F.natDegree < C) (hX : ∀ c : ℕ, (F.coeff c).natDegree < A)
    (hY : ∀ c a : ℕ, ((F.coeff c).coeff a).natDegree < B) (S : Finset (ZMod p)) (D : ℕ)
    (hroot : ∀ x ∈ S, (Polynomial.X - Polynomial.C x) ^ D ∣ frobeniusLogarithmicSubstitution F) :
    S.card * D ≤ (A - 1) + (B - 1) * (p - 1) + p * (C - 1) := by
  have hn := frobenius_logarithmic_substitution_ne_zero F hB hAB hF0 hX hY
  exact
    (card_mul_le_natDegree_of_pow_dvd (frobeniusLogarithmicSubstitution F) hn S D hroot).trans
      (natDegree_frobeniusLogarithmicSubstitution_le F hZ hX hY)

end PseudoPrime.NumberTheory.Heilbronn

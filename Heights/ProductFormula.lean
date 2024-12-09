import Heights.FinitePlaces
import Mathlib.LinearAlgebra.Projectivization.Basic

open Classical

/- namespace Ideal
variable {R : Type*} [CommRing R]

open IsDedekindDomain.HeightOneSpectrum Classical

include R
theorem foo' {n : ℕ} {I : Ideal R} (hI : I ≠ 0) : I ^ n = ⊤ ↔ I = ⊤ ∨ n = 0 := by
  simp_all only [Submodule.zero_eq_bot, ne_eq]
  apply Iff.intro
  · intro a
    by_cases h : n = 0
    · right
      exact h
    · left
      ext x
      simp_all only [Submodule.mem_top, iff_true]
      have h1 : x ∈ I ^ n := by simp_all only [Submodule.mem_top]
      exact (pow_le_self h) h1
  · intro a
    cases a with
    | inl h =>
      subst h
      exact Ideal.top_pow R n
    | inr h_1 =>
      subst h_1
      simp_all only [pow_zero, one_eq_top]

variable [IsDedekindDomain R] (v : IsDedekindDomain.HeightOneSpectrum R)

theorem foo {x : R} (h_x_nezero : x ≠ 0) :
    v.maxPowDividing (Ideal.span {x}) = ⊤ ↔ x ∉ v.asIdeal := by
  simp only [maxPowDividing]
  rw [foo' (by rw [Submodule.zero_eq_bot]; exact v.ne_bot)]
  constructor
  · intro a
    cases a with
    | inl h => exact fun _ ↦ (@IsPrime.ne_top' _ _ v.asIdeal) h
    | inr h_1 =>
      intro h
      have : (Associates.mk v.asIdeal).count (Associates.mk (span {x})).factors ≠ 0 := by
        apply (Associates.count_ne_zero_iff_dvd ?ha0 ?hp).mpr (dvd_span_singleton.mpr h)
        simp_all only [ne_eq, Submodule.zero_eq_bot, span_singleton_eq_bot, not_false_eq_true, Associates.factors_mk]
        exact irreducible v
      exact this h_1
  · intro a
    right
    by_contra!
    rw [Associates.count_ne_zero_iff_dvd] at this
    simp_all only [ne_eq, dvd_span_singleton]
    simp_all only [ne_eq, Submodule.zero_eq_bot, span_singleton_eq_bot, not_false_eq_true, Associates.factors_mk]
    exact irreducible v

end Ideal
 -/


namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

open Algebra FinitePlace Function Ideal IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem FinitePlace.prod_eq_inv_abs_norm_int {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ w : FinitePlace K, w x = (|norm ℤ x| : ℝ)⁻¹ := by
  convert_to ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖embedding v x‖ = |↑(norm ℤ x)|⁻¹
  exact (finprod_eq_of_bijective maximal_ideal ((bijective_iff_existsUnique _).mpr
    <| fun v ↦ ⟨mk v, max_ideal_mk v, fun _ a ↦ by rw [← a, mk_max_ideal]⟩)
    (fun w ↦ Eq.symm (norm_embedding_eq w (x : K))))
  apply Eq.symm (inv_eq_of_mul_eq_one_left _)
  norm_cast
  have h_span_nezero : span {x} ≠ 0 := by
    simp_all only [ne_eq, Submodule.zero_eq_bot, span_singleton_eq_bot, not_false_eq_true]
  let t₀ := {v : HeightOneSpectrum (𝓞 K) | x ∈ v.asIdeal}
  have h_fin₀ : t₀.Finite := by
    simp only [← dvd_span_singleton, finite_factors h_span_nezero, t₀]
  let s : Finset (HeightOneSpectrum (𝓞 K)) := h_fin₀.toFinset
  let t₁ := (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(embedding v) x‖).mulSupport
  let t₂ := (fun v : HeightOneSpectrum (𝓞 K) ↦ v.maxPowDividing (span {x})).mulSupport
  have h_subs₁ : t₁ ⊆ t₀ := fun _ ↦ by simp [t₁, t₀, norm_eq_one_iff_not_mem]
  have h_subs₂ : t₂ ⊆ t₀ := by
    simp only [Set.le_eq_subset, mulSupport_subset_iff, Set.mem_setOf_eq, t₂, t₀,
      maxPowDividing, ← dvd_span_singleton]
    intro v hv
    rw [← pow_zero v.asIdeal] at hv
    replace hv := fun h ↦ hv (congrArg (HPow.hPow v.asIdeal) h)
    rwa [imp_false, ← ne_eq, Associates.count_ne_zero_iff_dvd h_span_nezero (irreducible v)] at hv
  have h_fin₁ : t₁.Finite := h_fin₀.subset h_subs₁
  have h_fin₂ : t₂.Finite := h_fin₀.subset h_subs₂
  have h_sub₁ : h_fin₁.toFinset ⊆ s := Set.Finite.toFinset_subset_toFinset.mpr h_subs₁
  have h_sub₂ : h_fin₂.toFinset ⊆ s := Set.Finite.toFinset_subset_toFinset.mpr h_subs₂
  rw [Int.abs_eq_natAbs, ← Ideal.absNorm_span_singleton,
    ← Ideal.finprod_heightOneSpectrum_factorization h_span_nezero, Int.cast_natCast,
    finprod_eq_prod_of_mulSupport_toFinset_subset (s:=s) _ h_fin₁ h_sub₁,
    finprod_eq_prod_of_mulSupport_toFinset_subset (s:=s) _ h_fin₂ h_sub₂, map_prod, Nat.cast_prod,
    ← Finset.prod_mul_distrib, Finset.prod_eq_one]
  intro v _
  --rivedere dopo merge
  rw [maxPowDividing, map_pow, Nat.cast_pow, norm_def, vadic_abv_def,
    WithZeroMulInt.toNNReal_neg_apply _ ((Valuation.ne_zero_iff v.valuation).mpr
    (RingOfIntegers.coe_ne_zero_iff.mpr h_x_nezero)), Ideal.absNorm_apply, Submodule.cardQuot_apply]
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_intCast, ← Real.rpow_add (mod_cast Nat.zero_lt_of_lt
    (mod_cast one_lt_norm v))]
  norm_cast
  rw [zpow_eq_one_iff_right₀ (Nat.cast_nonneg' (Nat.card (𝓞 K ⧸ v.asIdeal)))
    (by exact Ne.symm (ne_of_lt (one_lt_norm v)))]
  simp only [valuation_eq_intValuationDef v x, intValuationDef_if_neg v h_x_nezero, ofAdd_neg,
    WithZero.coe_inv, WithZero.unzero_coe, toAdd_inv, toAdd_ofAdd, neg_add_cancel]


theorem FinitePlace.prod_eq_inv_abs_norm {x : K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ w : FinitePlace K, w x = |(Algebra.norm ℚ) x|⁻¹ := by
  --reduce to 𝓞 K
  rcases @IsFractionRing.div_surjective (𝓞 K) _ K _ _ _ x with ⟨a, b, _, rfl⟩
  have hb : b ≠ 0 := by
    simp_all only [ne_eq, div_eq_zero_iff, NoZeroSMulDivisors.algebraMap_eq_zero_iff, not_or,
      not_false_eq_true]
  have ha : a ≠ 0 := by
    simp_all only [ne_eq, div_eq_zero_iff, NoZeroSMulDivisors.algebraMap_eq_zero_iff, or_false,
      not_false_eq_true]
  simp_rw [map_div₀, Rat.cast_inv, Rat.cast_abs, finprod_div_distrib (mulSupport_Finite_int ha)
    (mulSupport_Finite_int hb), prod_eq_inv_abs_norm_int ha, prod_eq_inv_abs_norm_int hb,
    ← inv_eq_iff_eq_inv, div_inv_eq_mul, mul_inv_rev, inv_inv, inv_mul_eq_div, ← abs_div]
  congr
  apply Eq.symm (eq_div_of_mul_eq (by simp_all only [ne_eq, div_eq_zero_iff,
    NoZeroSMulDivisors.algebraMap_eq_zero_iff, or_self, not_false_eq_true, Int.cast_eq_zero,
    Algebra.norm_eq_zero_iff]) ?_)
  norm_cast
  rw [Algebra.coe_norm_int a, Algebra.coe_norm_int b, ← MonoidHom.map_mul, div_mul_cancel₀]
  exact RingOfIntegers.coe_ne_zero_iff.mpr hb

theorem product_places_eq_one {x : K} (h_x_nezero : x ≠ 0) :
    (∏ w : InfinitePlace K, w x ^ w.mult) * ∏ᶠ w : FinitePlace K, w x = 1 := by
  simp_all only [FinitePlace.prod_eq_inv_abs_norm h_x_nezero, InfinitePlace.prod_eq_abs_norm,
    ne_eq, Rat.cast_abs, Rat.cast_inv, isUnit_iff_ne_zero, abs_eq_zero, Rat.cast_eq_zero,
    Algebra.norm_eq_zero_iff, not_false_eq_true, IsUnit.mul_inv_cancel]

open LinearAlgebra.Projectivization

--#check ℙ K (Fin 2 → K)

--variable (v w : Fin 2 → K)



noncomputable def HeightProj {n : ℕ} : ℙ K (Fin n → K) → ℝ := by
  by_cases h_n : n = 0; exact fun x ↦ (1 : ℝ)
  let supinf : (w : InfinitePlace K) → (Fin n → K) → NNReal :=
    fun w x ↦ Finset.univ.sup (fun i : Fin n ↦ (w (x i)).toNNReal ^ w.mult)
  let supfin : (w : FinitePlace K) → (Fin n → K) → NNReal :=
    fun w x ↦ Finset.univ.sup (fun i : Fin n ↦ (w (x i)).toNNReal)
  have hinf (t : K) (w : InfinitePlace K) (x : Fin n → K) : supinf w (t • x) = (w t).toNNReal ^ w.mult * supinf w x := by
    simp only [Pi.smul_apply, smul_eq_mul, _root_.map_mul, supinf, NNReal.mul_finset_sup]
    conv => lhs; rhs; simp only [apply_nonneg, Real.toNNReal_mul, mul_pow]
  have hfin (t : K) (w : FinitePlace K) (x : Fin n → K) : supfin w (t • x) = (w t).toNNReal * supfin w x := by
    simp only [Pi.smul_apply, smul_eq_mul, _root_.map_mul, supfin]
    rw [mul_comm, NNReal.finset_sup_mul]
    congr
    ext i
    simp only [apply_nonneg, Real.toNNReal_mul, NNReal.coe_mul, Real.coe_toNNReal', sup_of_le_left, mul_comm]
  let f : {v : Fin n → K // v ≠ 0} → ℝ :=
    fun x ↦ ((∏ w : InfinitePlace K, supinf w x : ℝ) * (∏ᶠ w : FinitePlace K, supfin w x : ℝ)) ^
    ((Module.finrank ℚ K) : ℝ)⁻¹
  have hfproj : ∀ (x y : { v : Fin n → K // v ≠ 0 }) (t : K), x = t • (y : Fin n → K) → f x = f y := by
    intro x y t hxyt
    have hsupp : (mulSupport fun w ↦ (supfin w y : ℝ)).Finite := by

      sorry
    have h_t_nezero : t ≠ 0 := by
      intro h
      subst h
      simp only [ne_eq, zero_smul] at hxyt
      obtain ⟨val, property⟩ := x
      simp_all only [ne_eq, not_true_eq_false]
    simp only [ne_eq, NNReal.coe_prod, f, hxyt]
    congr 1
    --norm_cast
    simp_rw [hinf, hfin]
    norm_cast
    simp only [NNReal.coe_prod, NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal', apply_nonneg,
      sup_of_le_left]
    rw [Finset.prod_mul_distrib, finprod_mul_distrib (mulSupport_Finite h_t_nezero) hsupp, mul_mul_mul_comm,
      product_places_eq_one h_t_nezero, one_mul]
  exact Projectivization.lift f hfproj


end NumberField

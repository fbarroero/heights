import Heights.FinitePlaces

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

open FinitePlace IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem FinitePlace.prod_eq_inv_abs_norm_int {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ w : FinitePlace K, w x = (|(Algebra.norm ℤ) x| : ℝ)⁻¹ := by
  have : ∏ᶠ w : FinitePlace K, w x = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      ‖(embedding v) x‖ := by
    refine finprod_eq_of_bijective (fun a ↦ a.maximal_ideal) ?_
      (fun w ↦ Eq.symm (norm_embedding_eq w x))
    rw [Function.bijective_iff_existsUnique]
    exact fun v ↦ ⟨mk v, max_ideal_mk v, fun _ a ↦ by rw [← a, mk_max_ideal]⟩
  rw [this]
  apply Eq.symm (inv_eq_of_mul_eq_one_left _)
  norm_cast
  have h_span_nezero : Ideal.span {x} ≠ 0 := by
    simp_all only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot, not_false_eq_true]
  let t₀ := {v : HeightOneSpectrum (𝓞 K) | x ∈ v.asIdeal}
  have h_fin₀ : t₀.Finite := by
    simp_rw [t₀, ← Ideal.dvd_span_singleton]
    exact Ideal.finite_factors h_span_nezero
  let s : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := Set.Finite.toFinset h_fin₀
  let t₁ := (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) ↦
    ‖(embedding v) ↑x‖)
  let t₂ := (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) ↦
    v.maxPowDividing (Ideal.span {x}))
  have h_subs₁ : t₁ ⊆ t₀ := by
    simp only [Function.mulSupport_subset_iff, ne_eq, Set.mem_setOf_eq, t₁, t₀]
    intro v
    contrapose!
    exact (norm_eq_one_iff_not_mem v x).mpr
  have h_subs₂ : t₂ ⊆ t₀ := by
    simp only [Function.mulSupport_subset_iff, Set.mem_setOf_eq, t₂, t₀, maxPowDividing, Ideal.one_eq_top]
    intro v
    contrapose!
    intro hv
    have h : ⊤ = v.asIdeal ^ 0:= by
      rw [pow_zero]
      exact Eq.symm Ideal.one_eq_top
    rw [h]
    congr
    by_contra!
    apply hv
    rw [Associates.count_ne_zero_iff_dvd h_span_nezero (irreducible v)] at this
    exact Ideal.dvd_span_singleton.mp this
/-
  have h_subs₂' : t₂ ⊆ t₁ := by
    simp only [Function.mulSupport_subset_iff, ne_eq, Set.mem_setOf_eq, t₂, t₁, maxPowDividing,
      Ideal.one_eq_top, Function.mem_mulSupport, ne_eq]
    intro v
    contrapose!
    rw [norm_def, WithZeroMulInt.toNNReal_neg_apply _
    (by
      simp only [ne_eq, map_eq_zero, NoZeroSMulDivisors.algebraMap_eq_zero_iff]
      exact h_x_nezero),
    Ideal.absNorm_apply, Submodule.cardQuot_apply]
    push_cast
    rw [zpow_eq_one_iff_right₀ (Nat.cast_nonneg' (Nat.card (𝓞 K ⧸ v.asIdeal)))
    (by exact Ne.symm (ne_of_lt (one_lt_norm v)))]
    simp_rw [valuation_eq_intValuationDef v x, intValuationDef_if_neg v h_x_nezero]
    simp only [ofAdd_neg, WithZero.coe_inv, WithZero.unzero_coe, toAdd_inv, toAdd_ofAdd,
      neg_eq_zero, Nat.cast_eq_zero]
    intro hv
    rw [hv]
    simp only [pow_zero, Ideal.one_eq_top] -/
  have h_fin₁ : t₁.Finite := Set.Finite.subset h_fin₀ h_subs₁
  have h_fin₂ : t₂.Finite := Set.Finite.subset h_fin₀ h_subs₂
  have h_sub₁ : h_fin₁.toFinset ⊆ s := Set.Finite.toFinset_subset_toFinset.mpr h_subs₁
  have h_sub₂ : h_fin₂.toFinset ⊆ s := Set.Finite.toFinset_subset_toFinset.mpr h_subs₂
  rw [Int.abs_eq_natAbs, ← Ideal.absNorm_span_singleton,
    ← Ideal.finprod_heightOneSpectrum_factorization h_span_nezero, Int.cast_natCast,
    finprod_eq_prod_of_mulSupport_toFinset_subset (s:=s) _ h_fin₁ h_sub₁,
    finprod_eq_prod_of_mulSupport_toFinset_subset (s:=s) _ h_fin₂ h_sub₂, map_prod, Nat.cast_prod,
    ← Finset.prod_mul_distrib, Finset.prod_eq_one]
  intro v _
  rw [maxPowDividing, map_pow, Nat.cast_pow, norm_def, vadic_abv, AbsoluteValue.coe_mk,
    MulHom.coe_mk, WithZeroMulInt.toNNReal_neg_apply _ ((Valuation.ne_zero_iff v.valuation).mpr
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
  have hfrac : ∃ a b : 𝓞 K, b ≠ 0 ∧  x = a / b := by --maybe make a general lemma???
    rcases @IsFractionRing.div_surjective (𝓞 K) _ K _ _ _ x with ⟨a, b, _, hfrac⟩
    use a, b
    subst hfrac
    simp_all only [ne_eq, div_eq_zero_iff, NoZeroSMulDivisors.algebraMap_eq_zero_iff, not_or,
      not_false_eq_true, and_self]
  rcases hfrac with ⟨a, b, hb, hx⟩
  have ha : a ≠ 0 := by
    simp_all only [ne_eq, div_eq_zero_iff, NoZeroSMulDivisors.algebraMap_eq_zero_iff, or_false,
      not_false_eq_true]
  simp_rw [hx, map_div₀, Rat.cast_inv, Rat.cast_abs, finprod_div_distrib (mulSupport_Finite_int ha)
    (mulSupport_Finite_int hb), prod_eq_inv_abs_norm_int ha, prod_eq_inv_abs_norm_int hb,
    ← inv_eq_iff_eq_inv, div_inv_eq_mul, mul_inv_rev, inv_inv, inv_mul_eq_div, ← abs_div]
  congr
  apply Eq.symm (eq_div_of_mul_eq (by simp_all only [hx, ne_eq, div_eq_zero_iff,
    NoZeroSMulDivisors.algebraMap_eq_zero_iff, or_self, not_false_eq_true, Int.cast_eq_zero,
    Algebra.norm_eq_zero_iff]) ?_)
  norm_cast
  rw [Algebra.coe_norm_int a, Algebra.coe_norm_int b, ← MonoidHom.map_mul, div_mul_cancel₀]
  exact RingOfIntegers.coe_ne_zero_iff.mpr hb

theorem product_formula {x : K} (h_x_nezero : x ≠ 0) :
    (∏ w : InfinitePlace K, w x ^ w.mult) * ∏ᶠ w : FinitePlace K, w x = 1 := by
  rw [FinitePlace.prod_eq_inv_abs_norm h_x_nezero, InfinitePlace.prod_eq_abs_norm x]
  simp_all only [ne_eq, Rat.cast_abs, Rat.cast_inv, isUnit_iff_ne_zero, abs_eq_zero,
    Rat.cast_eq_zero, Algebra.norm_eq_zero_iff, not_false_eq_true, IsUnit.mul_inv_cancel]

end NumberField

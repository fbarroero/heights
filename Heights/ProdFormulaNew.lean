import Heights.Embeddings

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

open FinitePlace IsDedekindDomain

theorem product_formula_int {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ w : FinitePlace K, w x = (|(Algebra.norm ℤ) x| : ℝ)⁻¹ := by
  have : ∏ᶠ w : FinitePlace K, w x = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(embedding v) ↑x‖ := by
    refine finprod_eq_of_bijective (fun a ↦ a.maximal_ideal) ?he₀ (fun w ↦ Eq.symm (norm_embedding_eq w ↑x) )
    rw [Function.bijective_iff_existsUnique]
    intro v
    refine ⟨NumberField.FinitePlace.mk v, max_ideal_mk v, ?_⟩
    intro y a
    simp only [← a, mk_max_ideal y]
  rw [this]
  apply Eq.symm (inv_eq_of_mul_eq_one_left _)
  norm_cast
  have h_span_nezero : Ideal.span {x} ≠ 0 := by
    simp_all only [ne_eq, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot, not_false_eq_true]
  rw [Int.abs_eq_natAbs, ← Ideal.absNorm_span_singleton,
    ← Ideal.finprod_heightOneSpectrum_factorization h_span_nezero]
  simp only [Int.cast_natCast]
  have h_fin : {v : HeightOneSpectrum (𝓞 K) | x ∈ v.asIdeal}.Finite := by
    simp_rw [← Ideal.dvd_span_singleton]
    exact Ideal.finite_factors h_span_nezero
  let s : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := Set.Finite.toFinset h_fin
  let t₁ := (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) ↦ ‖(embedding v) ↑x‖)
  let t₂ := (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) ↦ v.maxPowDividing (Ideal.span {x}))
  have h_fin₁ : t₁.Finite := by
    sorry
  have h_fin₂ : t₂.Finite := by sorry
  have h_sub₁ : h_fin₁.toFinset ⊆ s := by sorry
  have h_sub₂ : h_fin₂.toFinset ⊆ s := by sorry
  rw [finprod_eq_prod_of_mulSupport_toFinset_subset (s:=s) _ h_fin₁ h_sub₁,
    finprod_eq_prod_of_mulSupport_toFinset_subset (s:=s) _ h_fin₂ h_sub₂, map_prod]
  push_cast
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro v _
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing]
  simp only [map_pow, Nat.cast_pow]

  sorry




theorem product_formula_finite {x : K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ w : FinitePlace K, w x = |(Algebra.norm ℚ) x|⁻¹ := by
  --reduce to 𝓞 K
  have hfrac : ∃ a b : 𝓞 K, b ≠ 0 ∧  x = a / b := by --maybe make a general lemma???
    rcases @IsFractionRing.div_surjective (𝓞 K) _ K _ _ _ x with ⟨a, b, _, hfrac⟩
    use a, b
    subst hfrac
    simp_all only [ne_eq, div_eq_zero_iff, NoZeroSMulDivisors.algebraMap_eq_zero_iff, not_or, not_false_eq_true,
      and_self]
  rcases hfrac with ⟨a, b, hb, hx⟩
  subst hx
  have ha : a ≠ 0 := by
    simp_all only [ne_eq, div_eq_zero_iff, NoZeroSMulDivisors.algebraMap_eq_zero_iff, or_false,
      not_false_eq_true]
  simp_rw [map_div₀]
  simp only [Rat.cast_inv, Rat.cast_abs]
  rw [finprod_div_distrib (mulSupport_Finite ha) (mulSupport_Finite hb),
    product_formula_int ha, product_formula_int hb]
  rw [← inv_eq_iff_eq_inv, div_inv_eq_mul, mul_inv_rev, inv_inv, inv_mul_eq_div, ← abs_div]
  congr
  apply IsUnit.div_eq_of_eq_mul
  · simp_all only [ne_eq, div_eq_zero_iff, NoZeroSMulDivisors.algebraMap_eq_zero_iff, or_self, not_false_eq_true,
    isUnit_iff_ne_zero, Int.cast_eq_zero, Algebra.norm_eq_zero_iff]
  · norm_cast
    rw [Algebra.coe_norm_int a, Algebra.coe_norm_int b, ← @MonoidHom.map_mul, IsUnit.div_mul_cancel]
    rw [isUnit_iff_ne_zero]
    norm_cast

theorem product_formula {x : K} (h_x_nezero : x ≠ 0) :
    (∏ w : InfinitePlace K, w x ^ w.mult) * ∏ᶠ w : FinitePlace K, w x = 1 := by
  rw [product_formula_finite h_x_nezero, NumberField.InfinitePlace.prod_eq_abs_norm x]
  simp_all only [ne_eq, Rat.cast_abs, Rat.cast_inv, isUnit_iff_ne_zero, abs_eq_zero, Rat.cast_eq_zero,
    Algebra.norm_eq_zero_iff, not_false_eq_true, IsUnit.mul_inv_cancel]

end NumberField

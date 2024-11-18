import Heights.Embeddings

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

--move to Embeddings
theorem mulSupport_FinitePlace_Finite {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    (Function.mulSupport fun w : FinitePlace K => w x).Finite := by sorry

theorem product_formula_int {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ w : FinitePlace K, w x = (|(Algebra.norm ℤ) x| : ℝ)⁻¹ := by sorry

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
  rw [finprod_div_distrib (mulSupport_FinitePlace_Finite ha) (mulSupport_FinitePlace_Finite hb),
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

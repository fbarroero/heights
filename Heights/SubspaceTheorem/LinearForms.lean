module

public import Heights.SubspaceTheorem.Defs

/-!
# A Liouville-type inequality for linear forms with algebraic coefficients

If `α₁, …, αₙ` are real algebraic numbers, then there are `c > 0` and `D` such that
`|α₁ x₁ + ⋯ + αₙ xₙ| ≥ c ‖x‖ ^ (-D)` for all integer points `x` at which the linear form
does not vanish. This is used in [evertse1993], proof that Theorem 3.2.1 implies Theorem 1.5, and
in the proof of Lemma 3.4.5.
-/

@[expose] public section

namespace Schmidt

variable {ι : Type*} [Fintype ι]

/-- Liouville's inequality for linear forms over a number field: if `a₁, …, aₙ` lie in a finite
extension `K` of `ℚ` and `τ₀` is an embedding of `K` into `ℂ`, then there are `c > 0` and `D` such
that `c * ‖x‖ ^ (-D) ≤ ‖τ₀ (a₁ x₁ + ⋯ + aₙ xₙ)‖` for all integer points `x` such that
`a₁ x₁ + ⋯ + aₙ xₙ ≠ 0`. The proof bounds the norm of a common integral multiple of the `aᵢ`
evaluated at `x`, which is a nonzero integer, by the product of its conjugates. -/
lemma exists_le_norm_algHom_linearForm {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] (a : ι → K) (τ₀ : K →ₐ[ℚ] ℂ) :
    ∃ c : ℝ, 0 < c ∧ ∃ D : ℕ, ∀ x : ι → ℤ, ∑ i, a i * x i ≠ 0 →
      c * ‖x‖ ^ (-(D : ℝ)) ≤ ‖τ₀ (∑ i, a i * x i)‖ := by
  classical
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have : Algebra.IsAlgebraic ℤ K := Algebra.IsAlgebraic.trans ℤ ℚ K
  obtain ⟨q, hq0, hq⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image a)
  replace hq : ∀ i, IsIntegral ℤ (q • a i) := fun i ↦
    hq _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hqpos : 0 < |(q : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hq0)
  set B : ℝ := ∑ σ : K →ₐ[ℚ] ℂ, ∑ i, ‖σ (a i)‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun σ _ ↦ Finset.sum_nonneg fun i _ ↦ norm_nonneg _
  set M : ℝ := |(q : ℝ)| * (B + 1) with hM
  have hMpos : 0 < M := by positivity
  set D : ℕ := (Finset.univ.erase τ₀).card with hD
  refine ⟨(|(q : ℝ)| * M ^ D)⁻¹, by positivity, D, fun x hx ↦ ?_⟩
  set β : K := ∑ i, a i * x i with hβ
  have hqβ (σ : K →ₐ[ℚ] ℂ) : ‖σ (q • β)‖ = |(q : ℝ)| * ‖σ β‖ := by
    rw [zsmul_eq_mul, map_mul, map_intCast, norm_mul, Complex.norm_intCast]
  have hσ (σ : K →ₐ[ℚ] ℂ) : ‖σ (q • β)‖ ≤ M * ‖x‖ := by
    have h1 : ‖σ β‖ ≤ (B + 1) * ‖x‖ := by
      calc ‖σ β‖ = ‖∑ i, σ (a i) * (x i : ℂ)‖ := by simp [hβ, map_sum]
        _ ≤ ∑ i, ‖σ (a i) * (x i : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ i, ‖σ (a i)‖ * ‖x‖ := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            rw [norm_mul]
            gcongr
            rw [Complex.norm_intCast, ← Int.norm_eq_abs]
            exact norm_le_pi_norm x i
        _ = (∑ i, ‖σ (a i)‖) * ‖x‖ := by rw [Finset.sum_mul]
        _ ≤ (B + 1) * ‖x‖ := by
            gcongr
            have := Finset.single_le_sum (f := fun σ : K →ₐ[ℚ] ℂ ↦ ∑ i, ‖σ (a i)‖)
              (fun σ _ ↦ Finset.sum_nonneg fun i _ ↦ norm_nonneg _) (Finset.mem_univ σ)
            linarith
    calc ‖σ (q • β)‖ = |(q : ℝ)| * ‖σ β‖ := hqβ σ
      _ ≤ |(q : ℝ)| * ((B + 1) * ‖x‖) := by gcongr
      _ = M * ‖x‖ := by rw [hM, mul_assoc]
  have hint : IsIntegral ℤ (q • β) := by
    rw [hβ, Finset.smul_sum]
    refine IsIntegral.sum _ fun i _ ↦ ?_
    have : q • (a i * (x i : K)) = x i • (q • a i) := by
      simp only [zsmul_eq_mul]; ring
    rw [this]
    exact (hq i).smul _
  have hne : q • β ≠ 0 := by
    rw [zsmul_eq_mul]
    exact mul_ne_zero (Int.cast_ne_zero.mpr hq0) hx
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm ℚ hint)
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [map_zero] at hn
    exact hne (Algebra.norm_eq_zero_iff.mp hn.symm)
  have h1 : (1 : ℝ) ≤ ‖algebraMap ℚ ℂ (Algebra.norm ℚ (q • β))‖ := by
    rw [← hn]
    simp only [eq_intCast, map_intCast, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hn0
  rw [Algebra.norm_eq_prod_embeddings, norm_prod,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ₀)] at h1
  have h2 : ∏ σ ∈ Finset.univ.erase τ₀, ‖σ (q • β)‖ ≤ (M * ‖x‖) ^ D := by
    rw [hD, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun σ _ ↦ norm_nonneg _) fun σ _ ↦ hσ σ
  have h4 : 1 ≤ ‖τ₀ β‖ * (|(q : ℝ)| * M ^ D * ‖x‖ ^ D) := by
    calc 1 ≤ ‖τ₀ (q • β)‖ * ∏ σ ∈ Finset.univ.erase τ₀, ‖σ (q • β)‖ := h1
      _ ≤ |(q : ℝ)| * ‖τ₀ β‖ * (M * ‖x‖) ^ D := by rw [hqβ]; gcongr
      _ = ‖τ₀ β‖ * (|(q : ℝ)| * M ^ D * ‖x‖ ^ D) := by rw [mul_pow]; ring
  have hP : 0 < |(q : ℝ)| * M ^ D * ‖x‖ ^ D := by
    by_contra h
    have : ‖τ₀ β‖ * (|(q : ℝ)| * M ^ D * ‖x‖ ^ D) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (not_lt.mp h)
    linarith
  rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, ← mul_inv, inv_le_iff_one_le_mul₀ hP]
  exact h4

/-- **Liouville's inequality for linear forms.** If `α₁, …, αₙ` are real algebraic numbers,
then there are `c > 0` and `D` such that `c * ‖x‖ ^ (-D) ≤ |α₁ x₁ + ⋯ + αₙ xₙ|` for all integer
points `x` such that `α₁ x₁ + ⋯ + αₙ xₙ ≠ 0`. -/
theorem exists_le_abs_linearForm (α : ι → ℝ) (hα : ∀ i, IsAlgebraic ℚ (α i)) :
    ∃ c : ℝ, 0 < c ∧ ∃ D : ℕ, ∀ x : ι → ℤ, ∑ i, α i * x i ≠ 0 →
      c * ‖x‖ ^ (-(D : ℝ)) ≤ |∑ i, α i * x i| := by
  let K := IntermediateField.adjoin ℚ (Set.range α)
  have : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨i, rfl⟩
    exact (hα i).isIntegral)
  let a : ι → K := fun i ↦ ⟨α i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩
  let τ₀ : K →ₐ[ℚ] ℂ := (IsScalarTower.toAlgHom ℚ ℝ ℂ).comp K.val
  obtain ⟨c, hc, D, h⟩ := exists_le_norm_algHom_linearForm a τ₀
  refine ⟨c, hc, D, fun x hx ↦ ?_⟩
  have key : τ₀ (∑ i, a i * x i) = ((∑ i, α i * x i : ℝ) : ℂ) := by
    simp [τ₀, a]
  have hne : ∑ i, a i * x i ≠ 0 := by
    intro h0
    rw [h0, map_zero] at key
    exact hx (by exact_mod_cast key.symm)
  have := h x hne
  rwa [key, Complex.norm_real, Real.norm_eq_abs] at this

end Schmidt

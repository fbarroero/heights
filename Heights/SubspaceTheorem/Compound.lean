module

public import Mathlib

/-!
# Compound matrices

For a square matrix `L` indexed by a linearly ordered finite type `ι`, its `m`-th compound matrix
is the matrix of the `m × m` minors of `L`, indexed by the subsets of `ι` of cardinality `m`.
It is the matrix of the `m`-th exterior power of the linear map defined by `L`.

In the proof of the Subspace Theorem ([evertse1993], Section 3.3) the rows of the `m`-th compound
of `L` are the coefficient vectors of the linear forms `L_σ = l_{i₁} ∧ ⋯ ∧ l_{iₘ}`, where
`σ = {i₁ < ⋯ < iₘ}`.
-/

@[expose] public section

open Matrix Set.powersetCard

namespace Schmidt

variable {ι R : Type*} [Fintype ι] [LinearOrder ι] [CommRing R]

/-- The `m`-th compound matrix of the square matrix `L`: its entries are the `m × m` minors
of `L`. -/
noncomputable def compound (L : Matrix ι ι R) (m : ℕ) :
    Matrix (Set.powersetCard ι m) (Set.powersetCard ι m) R :=
  Matrix.of fun s t ↦ (L.submatrix (ofFinEmbEquiv.symm s) (ofFinEmbEquiv.symm t)).det

omit [Fintype ι] in
lemma compound_apply (L : Matrix ι ι R) (m : ℕ) (s t : Set.powersetCard ι m) :
    compound L m s t = (L.submatrix (ofFinEmbEquiv.symm s) (ofFinEmbEquiv.symm t)).det := rfl

/-- The `m`-th compound matrix of `L` is the matrix of the `m`-th exterior power of the linear map
`Matrix.toLin' L`, in the basis of `⋀[R]^m (ι → R)` induced by the standard basis of `ι → R`. -/
theorem compound_eq_toMatrix_map (L : Matrix ι ι R) (m : ℕ) :
    compound L m = LinearMap.toMatrix ((Pi.basisFun R ι).exteriorPower m)
      ((Pi.basisFun R ι).exteriorPower m) (exteriorPower.map m (Matrix.toLin' L)) := by
  ext s t
  rw [LinearMap.toMatrix_apply, exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family,
    exteriorPower.basis_repr_apply, exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti, compound_apply, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Matrix.toLin'_apply]

/-- The compound matrix of the identity is the identity. -/
theorem compound_one (m : ℕ) : compound (1 : Matrix ι ι R) m = 1 := by
  rw [compound_eq_toMatrix_map, Matrix.toLin'_one, exteriorPower.map_id, LinearMap.toMatrix_id]

/-- **Cauchy–Binet formula**: taking compound matrices is multiplicative. -/
theorem compound_mul (L M : Matrix ι ι R) (m : ℕ) :
    compound (L * M) m = compound L m * compound M m := by
  simp only [compound_eq_toMatrix_map, Matrix.toLin'_mul, exteriorPower.map_comp,
    LinearMap.toMatrix_comp _ ((Pi.basisFun R ι).exteriorPower m)]

/-- The compound matrices of an invertible matrix are invertible. -/
theorem compound_det_ne_zero {K : Type*} [Field K] (L : Matrix ι ι K) (hL : L.det ≠ 0) (m : ℕ) :
    (compound L m).det ≠ 0 := by
  refine Matrix.det_ne_zero_of_right_inverse (B := compound L⁻¹ m) ?_
  rw [← compound_mul, Matrix.mul_nonsing_inv L (Ne.isUnit hL), compound_one]

omit [Fintype ι] in
/-- The entries of the compound matrices of a real matrix with algebraic entries are algebraic. -/
theorem isAlgebraic_compound (L : Matrix ι ι ℝ) (hL : ∀ i j, IsAlgebraic ℚ (L i j)) (m : ℕ)
    (s t : Set.powersetCard ι m) : IsAlgebraic ℚ (compound L m s t) := by
  rw [isAlgebraic_iff_isIntegral, ← mem_integralClosure_iff, compound_apply, Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun σ _ ↦ ?_
  rw [Units.smul_def]
  refine Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun i _ ↦ ?_) _
  rw [mem_integralClosure_iff, ← isAlgebraic_iff_isIntegral]
  exact hL _ _

end Schmidt

import Mathlib

namespace Polynomial

variable {p : ℤ[X]}

lemma abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one
    (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1) : |p.leadingCoeff| = 1 := by
  rcases eq_or_ne p 0 with hp | hp
  · have : (map (Int.castRingHom ℂ) p) = 0 := by simp [hp]
    simp [this] at h
  have h_ineq := leading_coeff_le_mahlerMeasure <| p.map (Int.castRingHom ℂ)
  rw [h, leadingCoeff_map_of_injective <| RingHom.injective_int (Int.castRingHom ℂ)] at h_ineq
  simp only [eq_intCast, Complex.norm_intCast] at h_ineq
  norm_cast at h_ineq
  have : 0 < |p.leadingCoeff| := by simp_all
  exact (Int.le_antisymm this h_ineq).symm


private lemma aa (n : ℕ):
    ((cyclotomic n ℤ).map (Int.castRingHom ℂ)).mahlerMeasure = 1 := by
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  simp only [map_cyclotomic, mahlerMeasure_eq_leadingCoeff_mul_prod_roots, cyclotomic.monic n ℂ,
    Monic.leadingCoeff, one_mem, CStarRing.norm_of_mem_unitary, one_mul]
  apply Multiset.prod_eq_one
  have : NeZero n := { out := hn }
  have : NeZero (n : ℂ) := NeZero.charZero
  conv => enter [2,1,1,2]; rw [Polynomial.cyclotomic.roots_eq_primitiveRoots_val]
  simp only [Multiset.mem_map, Finset.mem_val, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, sup_eq_left]
  exact fun _ hz ↦ le_of_eq <|
    IsPrimitiveRoot.norm'_eq_one (isPrimitiveRoot_of_mem_primitiveRoots hz) hn

--falseee, it can also be -cyclotomic

private lemma bb (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1) : p = cyclotomic p.natDegree ℤ := by
  refine int_cyclotomic_unique ?_
  rw [(IsAlgClosed.splits (map (Int.castRingHom ℂ) p)).eq_prod_roots,
   (IsAlgClosed.splits (cyclotomic' p.natDegree ℂ)).eq_prod_roots]

  have : (map (Int.castRingHom ℂ) p).leadingCoeff = 1 := by
    refine Monic.leadingCoeff ?_

    refine Monic.map (Int.castRingHom ℂ) ?_

    sorry
  simp [this]
  sorry

theorem Kr : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1 ↔ p = cyclotomic p.natDegree ℤ := by
  constructor
  · intro hMM
    exact bb hMM
  · intro h
    rw [h]
    exact aa p.natDegree

end Polynomial

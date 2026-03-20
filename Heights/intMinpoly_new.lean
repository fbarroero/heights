import Mathlib

namespace Polynomial

section eraseDen

variable {R S : Type*}
[CommRing R]
[IsDomain R]
[NormalizedGCDMonoid R]
(M : Submonoid R)
[CommRing S] [Algebra R S] [IsLocalization M S]
(p : Polynomial S)

noncomputable def eraseDen : R[X] :=
  letI := Classical.decEq S
  if p = 0 then 0 else
  normalize (IsLocalization.integerNormalization M p).primPart

#find_home! eraseDen

end eraseDen

section intMinpoly

--change setting to isLocalization

variable {R K L : Type*}
[CommRing R] [IsDomain R]
[NormalizedGCDMonoid R]
[Field K] [Algebra R K] [IsFractionRing R K]
[Field L] [Algebra K L]
(x : L) (hx : IsIntegral K x)

variable (R K) in
noncomputable def intMinpoly : Polynomial R := (minpoly K x).eraseDen (nonZeroDivisors R)

include hx in
theorem intMinpoly_ne_zero : (intMinpoly R K x) ≠ 0 := by
  simp [intMinpoly, eraseDen, normalize, primPart_ne_zero]
  exact minpoly.ne_zero hx

include hx in
theorem degree_eq : (intMinpoly R K x).degree = (minpoly K x).degree := by
  have : (minpoly K x).degree = (minpoly K x).natDegree := by
    refine degree_eq_natDegree ?_
    exact minpoly.ne_zero hx

  simp [intMinpoly, eraseDen, normalize]

  sorry

include hx in
theorem prim : (intMinpoly R K x).IsPrimitive := by
 /-  intro r hr
  simp_all [C_dvd_iff_dvd_coeff]
  specialize hr
 -/
 --make a lemma in Mathlib
  simp [intMinpoly, eraseDen, minpoly.ne_zero hx]
  have h_normalized_primitive : ∀ p : Polynomial R, p.IsPrimitive → (normalize p).IsPrimitive := by
    intro p hp r hr; specialize hp r; simp_all only [dvd_normalize_iff, C_dvd_iff_dvd_coeff,
      implies_true, forall_const] ;
  apply h_normalized_primitive
  exact isPrimitive_primPart (IsLocalization.integerNormalization (nonZeroDivisors R) (minpoly K x))

variable [Algebra R L] [IsScalarTower R K L]

open IsLocalization in
include hx in
theorem foo : x ∈ (intMinpoly R K x).aroots L := by
  simp only [aroots, mem_roots', ne_eq, IsRoot.def, eval_map_algebraMap]
  constructor
  · rw [Polynomial.map_eq_zero_iff]
    · exact intMinpoly_ne_zero x hx
    · -- The composition of injective maps is injective.
      have h_comp_inj : Function.Injective (algebraMap K L ∘ algebraMap R K) :=
        ((algebraMap K L).injective).comp (IsFractionRing.injective R K)
      convert h_comp_inj using 1
      ext
      simp [IsScalarTower.algebraMap_apply R K L]
  · simp [intMinpoly, eraseDen, aeval_def]
    let q := integerNormalization (nonZeroDivisors R) (minpoly K x)
    have : q ≠ 0 := by
      simp [q, IsFractionRing.integerNormalization_eq_zero_iff]
      exact minpoly.ne_zero hx
    have h_int_root : q.eval₂ (algebraMap R L) x = 0 :=
      integerNormalization_aeval_eq_zero _ (minpoly K x) <| minpoly.aeval K x
    rw [q.eq_C_content_mul_primPart] at h_int_root
    simp_all [normalize, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.content]
    rcases h_int_root with h_int_root | h_int_root
    · rw [_root_.map_eq_zero_iff _ (fun a b hab => IsFractionRing.injective R K
        <| by simpa [IsScalarTower.algebraMap_apply R K L] using hab), Finset.gcd_eq_zero_iff] at h_int_root
      specialize h_int_root q.natDegree
      simp_all [q]
    · simp [minpoly.ne_zero hx]
      exact Or.inl h_int_root


include hx in
theorem irred : Irreducible (intMinpoly R K x) := by
  rw [@irreducible_iff]
  constructor
  · refine not_isUnit_of_natDegree_pos (intMinpoly R K x) ?_
    sorry
  have : Irreducible (minpoly K x) := minpoly.irreducible hx
  rw [intMinpoly, eraseDen, normalize_apply, ]



  sorry

end intMinpoly

end Polynomial

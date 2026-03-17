import Mathlib

namespace Polynomial

section eraseDen

variable {R S : Type*} --[DecidableEq R]
[CommRing R] --[CommMonoidWithZero R] [IsCancelMulZero R]
[NormalizedGCDMonoid R] --[IsDomain R]
(M : Submonoid R)
[CommRing S] [Algebra R S] [IsLocalization M S]
(p : Polynomial S)

noncomputable def eraseDen : Polynomial R :=
  normalize (IsLocalization.integerNormalization M p).primPart

end eraseDen

section intMinpoly

variable {R K L : Type*} --[DecidableEq R]
[CommRing R] --[CommMonoidWithZero R] [IsCancelMulZero R]
[NormalizedGCDMonoid R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] --[DecidableEq K]
[Field L] [Algebra K L]
(x : L) (hx : IsIntegral K x)

variable (R K) in
noncomputable def intMinpoly : Polynomial R := (minpoly K x).eraseDen (nonZeroDivisors R)

theorem intMinpoly_ne_zero : (intMinpoly R K x) ≠ 0 := by
  simp [intMinpoly, eraseDen, normalize, primPart_ne_zero]

variable [Algebra R L] [IsScalarTower R K L]

open IsLocalization in
include hx in
theorem foo : x ∈ (intMinpoly R K x).aroots L := by
  simp only [aroots, mem_roots', ne_eq, IsRoot.def, eval_map_algebraMap]
  constructor
  · rw [Polynomial.map_eq_zero_iff]
    · exact intMinpoly_ne_zero x;
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
    simp_all [normalize, q, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.content]
    rcases h_int_root with h_int_root | h_int_root
    rw [_root_.map_eq_zero_iff _ (fun a b hab => IsFractionRing.injective R K
      <| by simpa [IsScalarTower.algebraMap_apply R K L] using hab), Finset.gcd_eq_zero_iff] at h_int_root
    specialize h_int_root q.natDegree
    simp_all [q]
    exact Or.inl h_int_root

theorem prim : (intMinpoly R K x).IsPrimitive := by
 /-  intro r hr
  simp_all [C_dvd_iff_dvd_coeff]
  specialize hr
 -/
 --make a lemma in Mathlib
  have h_normalized_primitive : ∀ p : Polynomial R, p.IsPrimitive → (normalize p).IsPrimitive := by
    intro p hp r hr; specialize hp r; simp_all only [dvd_normalize_iff, C_dvd_iff_dvd_coeff,
      implies_true, forall_const] ;
  apply h_normalized_primitive;
  exact isPrimitive_primPart (IsLocalization.integerNormalization (nonZeroDivisors R) (minpoly K x))


theorem irred : Irreducible (intMinpoly R K x) := sorry

end intMinpoly

end Polynomial

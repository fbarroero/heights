import Mathlib

variable {R K : Type*} [DecidableEq R] [CommSemiring R] [CommMonoidWithZero R] [IsCancelMulZero R]
[NormalizedGCDMonoid R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

namespace Finset

variable (s : Finset K)

variable (R) in
noncomputable def lcmDen : R := s.lcm (fun x ↦
  let q := (IsLocalization.sec (nonZeroDivisors R) x)
  --normalize <|
  Classical.choose (GCDMonoid.gcd_dvd_right q.1 q.2))

--#eval ((singleton 1 : Finset ℚ)).lcmDen ℤ

theorem aa (x : ℤ) : normalize x = x.natAbs := by
  simp [normalize, normUnit, abs]
  by_cases h : 0 ≤ x
  simp [h]
  simp [h]
  omega

theorem foo (s : Finset ℚ) : s.lcmDen ℤ = s.lcm (fun x ↦ (x.den : ℤ)) := by
  induction s using Finset.induction_on with
  | empty =>
    simp [lcmDen]
  | insert a s has hind =>
    --simp [lcmDen]
    simp [← hind, lcmDen]
    apply lcm_eq_of_associated_left
    let q := (IsLocalization.sec (nonZeroDivisors ℤ) a)
    let ad := Classical.choose (GCDMonoid.gcd_dvd_right q.1 q.2)
    have ha' := Classical.choose_spec (GCDMonoid.gcd_dvd_right q.1 q.2)
    have : a * q.2 = q.1 := IsLocalization.sec_spec (nonZeroDivisors ℤ) a

    apply associated_of_dvd_dvd


    sorry

    /-
    rw [associated_of_dvd_dvd]
    rw [@Int.associated_iff]
  -/


    sorry

  /-
  suffices (s.lcmDen ℤ).natAbs = (s.lcm (fun x ↦ (x.den : ℤ))).natAbs by
    convert this
    refine Iff.symm (Int.natAbs_inj_of_nonneg_of_nonneg ?_ ?_)
    simp [lcmDen, lcm_eq_normalize]

    sorry
    sorry
  apply Nat.dvd_antisymm
  sorry -/
  /- simp [lcmDen, Finset.lcm_def, lcm]


  congr
  ext x -/

  --sorry


end Finset

/- namespace Polynomial

variable (p : K[X])

variable (R) in
noncomputable def lcmDen := p.coeffs.lcmDen R

theorem foo : p.lcmDen R = p.support.lcm (α := R) fun i ↦ (IsLocalization.sec (nonZeroDivisors R) (p.coeff i)).2 := by
  simp [lcmDen, Finset.lcmDen]
  simp [Finset.lcm_def]
  congr

  sorry

end Polynomial -/

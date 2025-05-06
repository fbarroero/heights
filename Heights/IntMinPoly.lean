import Mathlib

namespace Polynomial

open Int

def lcmDen (p : ℚ[X]) : ℕ := p.support.lcm fun i ↦ (p.coeff i).den

--Useless?
theorem lcmDen_poly_int (p : ℤ[X]) : lcmDen (p.map (castRingHom ℚ)) = 1 := by
  simp [lcmDen, coeff_map, eq_intCast, Rat.intCast_den, Nat.cast_one]
  apply dvd_antisymm_of_normalize_eq Finset.normalize_lcm rfl _
    <| one_dvd ((map (castRingHom ℚ) p).support.lcm fun i ↦ 1)
  apply Finset.lcm_dvd
  exact fun b a ↦ one_dvd 1

def erase_den (p : ℚ[X]) : ℤ[X] :=
  ofFn (p.natDegree + 1) (fun i ↦ (p.lcmDen) / (p.coeff i).den * (p.coeff i).num)

theorem erase_denom_eq_sum (p : ℚ[X]) : p.erase_den = ∑ i : Fin (p.natDegree + 1), monomial i ((lcmDen p) / (p.coeff i).den * (p.coeff i).num) := by
  simp [erase_den, ofFn_eq_sum_monomial]

theorem erase_denom_coeff (p : ℚ[X]) (i : ℕ) (h : i ≤ p.natDegree) : p.erase_den.coeff i = (lcmDen p) / (p.coeff i).den * (p.coeff i).num := by
  rw [erase_den, ofFn_coeff_eq_val_of_lt _ <|Order.lt_add_one_iff.mpr h]

theorem erase_denom_support (p : ℚ[X]) : p.erase_den.support = p.support := by
  ext i
  simp only [mem_support_iff]
  rw [not_iff_not]
  by_cases h : i ≤ p.natDegree
  · rw [erase_denom_coeff p i h]
    constructor
    · contrapose!
      intro h
      rw [mul_ne_zero_iff_right (Rat.num_ne_zero.mpr h), lcmDen]
      norm_cast
      refine (Nat.div_ne_zero_iff_of_dvd ?_).mpr ?_
      apply Finset.dvd_lcm <| mem_support_iff.mpr h
      refine ⟨?_, (p.coeff i).den_nz⟩
      simp [ne_eq, Finset.lcm_eq_zero_iff]
    · intro h
      simp [h]
  · rw [not_le] at h
    simp [erase_den, ofFn_coeff_eq_zero_of_ge _ h]
    exact coeff_eq_zero_of_natDegree_lt h

theorem erase_denom_natDegree_eq (p : ℚ[X]) : p.erase_den.natDegree = p.natDegree := by
  apply natDegree_eq_natDegree
  simp [degree]
  congr 1
  exact erase_denom_support p


theorem erase_denom_coeff' (p : ℚ[X]) : p.erase_den.coeff = fun i ↦ (p.lcmDen) / (p.coeff i).den * (p.coeff i).num := by
  ext i
  by_cases h : i ≤ p.natDegree
  · exact erase_denom_coeff p i h
  · rw [not_le] at h
    simp [erase_den, ofFn_coeff_eq_zero_of_ge _ h]
    right
    exact coeff_eq_zero_of_natDegree_lt h

theorem foo (s : Finset β) (f : β → ℚ) : (s.gcd fun i ↦ (s.lcm fun i ↦ (f i).den) / (f i).den * (f i).num) = s.gcd fun i ↦ (f i).num := by

  sorry

  --apply Finset.induction_on

theorem primitive (p : ℚ[X]) (hp : p.Monic) : p.erase_den.IsPrimitive := by
  rw [isPrimitive_iff_isUnit_of_C_dvd]
  by_contra! h
  simp only [C_dvd_iff_dvd_coeff] at h
  obtain ⟨r, hr1, hr2⟩ := h
  let P := (r.natAbs).minFac
  have hlcm (i : ℕ) : (p.coeff i).den ∣ p.lcmDen := by
    by_cases h : i ∈ p.support
    · exact Finset.dvd_lcm h
    · simp [not_mem_support_iff.mp h]
  have hP1 (i : ℕ) : P ∣ (p.erase_den.coeff i).natAbs := by
    specialize hr1 i
    zify
    simp only [dvd_abs]
    apply dvd_trans _ <| natAbs_dvd.mpr hr1
    simp only [dvd_abs, P]
    norm_cast
    exact Nat.minFac_dvd r.natAbs
  have hP2 : P.Prime := by
    apply Nat.minFac_prime
    rw [ne_eq, ← isUnit_iff_natAbs_eq]
    exact hr2
  have hP3 : P ∣ p.lcmDen := by
    specialize hP1 p.natDegree
    simp only [Monic, P] at hp
    simp only [erase_den, lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt,
      ofFn_coeff_eq_val_of_lt, coeff_natDegree, hp, Rat.den_ofNat, Nat.cast_one,
      EuclideanDomain.div_one, Rat.num_ofNat, mul_one, natAbs_ofNat, P] at hP1
    exact hP1
  simp only [erase_denom_coeff', natAbs_mul] at hP1
  norm_cast at hP1
  conv at hP1 => ext i; norm_cast; rw [Nat.Prime.dvd_mul hP2]
  have hP4 (i : ℕ): ¬(P ∣ p.lcmDen / (p.coeff i).den) → P ∣ (p.coeff i).num.natAbs := by
    intro h
    specialize hP1 i
    simp_all
  have hP5 (i : ℕ) : ¬(P ∣ p.lcmDen / (p.coeff i).den) → P ∣ (p.coeff i).den := by
    specialize hlcm i
    contrapose!
    intro h
    refine (Nat.dvd_div_iff_mul_dvd hlcm).mpr ?_
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ hlcm hP3
    rw [Nat.Prime.dvd_iff_not_coprime hP2, Decidable.not_not] at h
    exact Nat.coprime_comm.mp h
  have hP6 (i : ℕ) : P ∣ p.lcmDen / (p.coeff i).den := by
    by_contra! h
    specialize hP4 i h
    specialize hP5 i h
    simp_all [Nat.Coprime.coprime_dvd_left hP4 (p.coeff i).reduced, Nat.Prime.dvd_iff_not_coprime hP2]

  have hP7 (i : ℕ) : (p.coeff i).den ∣ p.lcmDen / P := by
    specialize hP6 i
    refine Nat.dvd_div_of_mul_dvd ?_
    rw [mul_comm, ← Nat.dvd_div_iff_mul_dvd (hlcm i)]
    exact hP6
  have hP8 : p.lcmDen ∣ p.lcmDen / P := by
    apply Finset.lcm_dvd
    intro i hi
    exact hP7 i
  have hlcm_pos : 0 < p.lcmDen := by
    simp [lcmDen, Nat.pos_iff_ne_zero, Finset.lcm_eq_zero_iff]
  rw [Nat.dvd_div_iff_mul_dvd hP3, mul_comm, ← Nat.dvd_div_iff_mul_dvd (Nat.dvd_refl p.lcmDen), Nat.div_self hlcm_pos] at hP8
  simp_all [Nat.Prime.ne_one]

end Polynomial

namespace NumberField

variable {K : Type*} [Field K] [Algebra ℚ K] (x : K) (hx : IsIntegral ℚ x)

open Polynomial

noncomputable def intMinpoly : ℤ[X] := erase_den (minpoly ℚ x)

variable [NumberField K]

theorem equal {x : K} (hpol : ((minpoly ℚ x).map (algebraMap ℚ K)).Splits (RingHom.id K)) :
    (intMinpoly x).leadingCoeff =  ∏ᶠ w : FinitePlace K, max 1 (w x) := by
  have h_poleq := eq_prod_roots_of_splits_id hpol
  simp at h_poleq
  have h (w : FinitePlace K) : w ((intMinpoly x).leadingCoeff) *
    (Multiset.map (fun a ↦ max 1 (w a) ) (map (algebraMap ℚ K) (minpoly ℚ x)).roots).prod = 1 := by

    sorry

  sorry


end NumberField

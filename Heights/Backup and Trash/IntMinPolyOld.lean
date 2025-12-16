import Mathlib

namespace Finset

open Multiset

variable {β : Type*} [CancelCommMonoidWithZero α] [NormalizedGCDMonoid α]

--add this and more to Mathlib? Maybe not

theorem auxc (s : Finset β) (h : s ≠ ∅) (n : α) : s.lcm (fun _ ↦ n) = normalize n := by
  apply dvd_antisymm_of_normalize_eq normalize_lcm (normalize_idem n)
  · exact lcm_dvd <|fun _ _ ↦ Dvd.intro (↑(normUnit n)) rfl
  · rw [normalize_dvd_iff]
    apply Finset.nonempty_of_ne_empty at h
    obtain ⟨b, hb⟩ := h
    exact dvd_lcm hb

theorem aux1 (s : Finset β) : s.lcm (fun _ ↦ (1 : α)) = 1 := by
  apply dvd_antisymm_of_normalize_eq normalize_lcm normalize_one _ <| one_dvd (s.lcm fun _ ↦ 1)
  exact Finset.lcm_dvd <| fun _ _ ↦ one_dvd 1

end Finset


-- define int minpoly and prove stuff about it

open Finset in
theorem aux1 (s : Finset ℕ) : s.lcm (fun _ ↦ 1) = 1 := by
  refine Nat.eq_one_of_dvd_one ?_
  apply Finset.lcm_dvd
  exact fun b a ↦ Nat.one_dvd 1
/-
open Finset in
theorem auxc (s : Finset ℕ) (h : s ≠ ∅) (n : ℕ) : s.lcm (fun _ ↦ (n : ℤ)) = n := by
  rw [Finset.auxc s h n]
  exact Int.normalize_coe_nat n -/

namespace Polynomial

/- section GCD

variable {R : Type u_1} [CommRing R] [IsDomain R] {K : Type u_2} [Field K] [Algebra R K]
    [IsFractionRing R K]  [NormalizedGCDMonoid R]

noncomputable def denom (x : K) : R :=
  let ⟨a, b, h⟩ := IsFractionRing.div_surjective (A := R) x

  sorry


def gcd_poly (p : K[X]) : R := p.support.gcd (fun i ↦ (IsLocalization.surj (p.coeff i)))


end GCD -/

open Int

--theorem foo (p : ℤ[X]) :

def lcmDen_poly (p : ℚ[X]) : ℕ := p.support.lcm fun i ↦ (p.coeff i).den



theorem lcmDen_poly_int (p : ℤ[X]) : lcmDen_poly (p.map (castRingHom ℚ)) = 1 := by
  simp only [lcmDen_poly, coeff_map, eq_intCast, Rat.intCast_den, Nat.cast_one]
  --exact Finset.aux1 (map (castRingHom ℚ) p).support
  exact aux1 (map (castRingHom ℚ) p).support/-
  apply dvd_antisymm_of_normalize_eq Finset.normalize_lcm rfl _
    <| Int.one_dvd ((map (castRingHom ℚ) p).support.lcm fun i ↦ 1)
  apply Finset.lcm_dvd
  exact fun b a ↦ Int.one_dvd 1 -/

def erase_denom (p : ℚ[X]) : ℤ[X] :=
  ofFn (p.natDegree + 1) (fun i ↦ (p.lcmDen_poly) / (p.coeff i).den * (p.coeff i).num)

--theorem erase_denom_eq (p : ℚ[X]) : erase_denom p =  (C (p.lcmDen_poly : ℚ)) * p := by

theorem erase_denom_eq_sum (p : ℚ[X]) : erase_denom p = ∑ i : Fin (p.natDegree + 1), monomial i ((lcmDen_poly p) / (p.coeff i).den * (p.coeff i).num) := by
  simp [erase_denom, ofFn_eq_sum_monomial]

theorem erase_denom_coeff (p : ℚ[X]) (i : ℕ) (h : i ≤ p.natDegree) : p.erase_denom.coeff i = (lcmDen_poly p) / (p.coeff i).den * (p.coeff i).num := by
  rw [erase_denom, ofFn_coeff_eq_val_of_lt _ <|Order.lt_add_one_iff.mpr h]

theorem erase_denom_support (p : ℚ[X]) : p.erase_denom.support = p.support := by
  ext i
  simp only [mem_support_iff]
  rw [not_iff_not]
  by_cases h : i ≤ p.natDegree
  · rw [erase_denom_coeff p i h]
    constructor
    · contrapose!
      intro h
      rw [mul_ne_zero_iff_right (Rat.num_ne_zero.mpr h), lcmDen_poly]
      norm_cast
      refine (Nat.div_ne_zero_iff_of_dvd ?_).mpr ?_
      apply Finset.dvd_lcm <| mem_support_iff.mpr h
      refine ⟨?_, (p.coeff i).den_nz⟩
      simp [ne_eq, Finset.lcm_eq_zero_iff]
    · intro h
      simp [h]
  · rw [not_le] at h
    simp [erase_denom, ofFn_coeff_eq_zero_of_ge _ h]
    exact coeff_eq_zero_of_natDegree_lt h

theorem erase_denom_natDegree_eq (p : ℚ[X]) : p.erase_denom.natDegree = p.natDegree := by
  apply natDegree_eq_natDegree
  simp [degree]
  congr 1
  exact erase_denom_support p


theorem erase_denom_coeff' (p : ℚ[X]) : p.erase_denom.coeff = fun i ↦ (p.lcmDen_poly) / (p.coeff i).den * (p.coeff i).num := by
  ext i
  by_cases h : i ≤ p.natDegree
  · exact erase_denom_coeff p i h
  · rw [not_le] at h
    simp [erase_denom, ofFn_coeff_eq_zero_of_ge _ h]
    right
    exact coeff_eq_zero_of_natDegree_lt h

theorem foo (s : Finset β) (f : β → ℚ) : (s.gcd fun i ↦ (s.lcm fun i ↦ (f i).den) / (f i).den * (f i).num) = s.gcd fun i ↦ (f i).num := by

  sorry

  --apply Finset.induction_on

theorem primitive (p : ℚ[X]) (hp : p.Monic) : p.erase_denom.IsPrimitive := by
  rw [isPrimitive_iff_isUnit_of_C_dvd]
  by_contra! h
  simp only [C_dvd_iff_dvd_coeff] at h
  obtain ⟨r, hr1, hr2⟩ := h
  let P := (r.natAbs).minFac
  have hlcm (i : ℕ) : (p.coeff i).den ∣ p.lcmDen_poly := by
    by_cases h : i ∈ p.support
    · exact Finset.dvd_lcm h
    · simp [not_mem_support_iff.mp h]
  have hP1 (i : ℕ) : P ∣ (p.erase_denom.coeff i).natAbs := by
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
  have hP3 : P ∣ p.lcmDen_poly := by
    specialize hP1 p.natDegree
    simp only [Monic, P] at hp
    simp only [erase_denom, lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt,
      ofFn_coeff_eq_val_of_lt, coeff_natDegree, hp, Rat.den_ofNat, Nat.cast_one,
      EuclideanDomain.div_one, Rat.num_ofNat, mul_one, natAbs_ofNat, P] at hP1
    exact hP1
  simp only [erase_denom_coeff', natAbs_mul] at hP1
  norm_cast at hP1
  conv at hP1 => ext i; norm_cast; rw [Nat.Prime.dvd_mul hP2]
  have hP4 (i : ℕ): ¬(P ∣ p.lcmDen_poly / (p.coeff i).den) → P ∣ (p.coeff i).num.natAbs := by
    intro h
    specialize hP1 i
    simp_all
  have hP5 (i : ℕ) : ¬(P ∣ p.lcmDen_poly / (p.coeff i).den) → P ∣ (p.coeff i).den := by
    specialize hlcm i
    contrapose!
    intro h
    refine (Nat.dvd_div_iff_mul_dvd hlcm).mpr ?_
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ hlcm hP3
    rw [Nat.Prime.dvd_iff_not_coprime hP2, Decidable.not_not] at h
    exact Nat.coprime_comm.mp h
  have hP6 (i : ℕ) : P ∣ p.lcmDen_poly / (p.coeff i).den := by
    by_contra! h
    specialize hP4 i h
    specialize hP5 i h
    simp_all [Nat.Coprime.coprime_dvd_left hP4 (p.coeff i).reduced, Nat.Prime.dvd_iff_not_coprime hP2]

  have hP7 (i : ℕ) : (p.coeff i).den ∣ p.lcmDen_poly / P := by
    specialize hP6 i
    refine Nat.dvd_div_of_mul_dvd ?_
    rw [mul_comm, ← Nat.dvd_div_iff_mul_dvd (hlcm i)]
    exact hP6
  have hP8 : p.lcmDen_poly ∣ p.lcmDen_poly / P := by
    apply Finset.lcm_dvd
    intro i hi
    exact hP7 i
  have hlcm_pos : 0 < p.lcmDen_poly := by
    simp [lcmDen_poly, Nat.pos_iff_ne_zero, Finset.lcm_eq_zero_iff]
  rw [Nat.dvd_div_iff_mul_dvd hP3, mul_comm, ← Nat.dvd_div_iff_mul_dvd (Nat.dvd_refl p.lcmDen_poly), Nat.div_self hlcm_pos] at hP8
  simp_all [Nat.Prime.ne_one]

end Polynomial

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] [Algebra ℚ K] (x : K) (hx : IsIntegral ℚ x)

open Polynomial

noncomputable def Intminpoly : ℤ[X] := erase_denom (minpoly ℚ x)

theorem equal {x : K} (hpol : ((minpoly ℚ x).map (algebraMap ℚ K)).Splits (RingHom.id K)) :
    (Intminpoly x).leadingCoeff =  ∏ᶠ w : FinitePlace K, max 1 (w x) := by
  have h_poleq := eq_prod_roots_of_splits_id hpol
  simp at h_poleq
  have h (w : FinitePlace K) : w ((Intminpoly x).leadingCoeff) *
    (Multiset.map (fun a ↦ max 1 (w a) ) (map (algebraMap ℚ K) (minpoly ℚ x)).roots).prod = 1 := by

    sorry

  sorry


end NumberField

--import Heights.IntMinPoly
import Mathlib

namespace Polynomial

variable {p : ℤ[X]} {K : Type*} [Field K]

open NumberField

theorem _root_.InfinitePlace.pow_le_one_of_le_one {x : K} {v : InfinitePlace K}
    (h : v x ≤ 1) (n : ℕ) : v (x ^ n) ≤ 1 := by
  rw [map_pow]
  exact pow_le_one₀ (apply_nonneg v x) h

variable [NumberField K]


theorem minpoly_mahlerMeasure_eq_one_of_le_one {x : K} (h_int : IsIntegral ℤ x)
    (h : ∀ v : InfinitePlace K, v x ≤ 1) :
    ((minpoly ℤ x).map (algebraMap ℤ ℂ)).mahlerMeasure = 1 := by
  have : (map (Int.castRingHom ℂ) (minpoly ℤ x)).leadingCoeff = 1 :=
    Monic.map (algebraMap ℤ ℂ) (minpoly.monic h_int)
  simp only [algebraMap_int_eq, mahlerMeasure_eq_leadingCoeff_mul_prod_roots, this, one_mem,
    CStarRing.norm_of_mem_unitary, one_mul]
  apply Multiset.prod_eq_one
  simp only [Multiset.mem_map, forall_exists_index, and_imp]
  intro _ z _ rfl
  have : z ∈ (Set.range fun (φ : K →+* ℂ) => φ x) := by
    rw [Embeddings.range_eval_eq_rootSet_minpoly K ℂ x,
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ h_int, rootSet]
    refine Multiset.mem_toFinset.mpr ?_
    rw [aroots_def, map_map]
    aesop
  have : ∃ v : InfinitePlace K, v x = ‖z‖ := by
    obtain ⟨φ, rfl⟩ := this
    use InfinitePlace.mk φ
    simp
  grind

private lemma box_finite (d : ℕ) :
    {p : ℤ[X] | p ≠ 0 ∧ p.natDegree ≤ d ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 1}.Finite := by
  have hfin := finite_mahlerMeasure_le d 1
  have : {p : ℤ[X] | p ≠ 0 ∧ p.natDegree ≤ d ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 1} ⊆
    {p : ℤ[X] | p.natDegree ≤ d ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 1} := by
    gcongr 1
    grind
  exact Set.Finite.subset hfin this

variable {x : Kˣ}

private lemma degZQ {z : K} (h_int : IsIntegral ℤ z) :
    (minpoly ℤ z).natDegree = (minpoly ℚ z).natDegree := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ h_int]
  refine (natDegree_map_of_leadingCoeff_ne_zero (algebraMap ℤ ℚ) ?_).symm
  rw [Algebra.algebraMap_eq_smul_one, Int.smul_one_eq_cast]
  norm_cast
  rw [leadingCoeff_eq_zero]
  exact minpoly.ne_zero h_int

open IntermediateField in
theorem natDegree_minpoly_pow_le (h_int : IsIntegral ℤ (x : K)) {n : ℕ} :
    (minpoly ℤ (x ^ n : K)).natDegree ≤ (minpoly ℤ (x : K)).natDegree := by
  have h_intn : IsIntegral ℤ ((x : K) ^ n) := IsIntegral.pow h_int n
  convert_to (minpoly ℚ ((x : K) ^ n)).natDegree ≤ (minpoly ℚ (x : K)).natDegree
  · exact degZQ h_intn
  · exact degZQ h_int
  · rw [← adjoin.finrank <| Algebra.IsIntegral.isIntegral ((x : K) ^ n),
      ← adjoin.finrank <| Algebra.IsIntegral.isIntegral (x : K)]
    apply finrank_le_of_le_right
    rw [adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    refine pow_mem ?_ _
    rw [← adjoin_simple_le_iff]

open Set in
theorem finite_closure_of_le_one (h : ∀ v : InfinitePlace K, v x ≤ 1) (hx : IsIntegral ℤ (x : K)) :
    Finite (Submonoid.closure {x}) := by
  have  hmp (n : ℕ) : ((minpoly ℤ ((x : K) ^ n)).map (algebraMap ℤ ℂ)).mahlerMeasure = 1 :=
    minpoly_mahlerMeasure_eq_one_of_le_one (IsIntegral.pow hx n)
    <| fun v ↦ InfinitePlace.pow_le_one_of_le_one (h v) n
  let d := (minpoly ℤ (x : K)).natDegree
  let Box :=
    {p : ℤ[X] | p ≠ 0 ∧ p.natDegree ≤ d ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 1}
  let f : Kˣ → ℤ[X] := fun y ↦ minpoly ℤ (y : K)
  have hsubs : f '' (Submonoid.closure {x}) ⊆ Box := by
    rintro p ⟨y, hy, hpy⟩
    obtain ⟨n, h⟩ := Submonoid.mem_closure_singleton.mp hy
    rw [← hpy, ← h]
    refine ⟨minpoly.ne_zero <| IsIntegral.pow hx n, ?_, le_of_eq <| hmp n⟩
    simp_rw [f]
    exact natDegree_minpoly_pow_le hx
  apply Finite.of_finite_fibers f <| Finite.subset (box_finite d) hsubs
  intro p hp
  apply Finite.inter_of_right
  have : {x | f x = p} ⊆ {x | (x : K) ∈ p.aroots K} := by
    intro z hz
    simp only [mem_roots', algebraMap_int_eq, IsRoot.def,
      Polynomial.map_ne_zero_iff <| RingHom.injective_int (Int.castRingHom K)]
    refine ⟨(hsubs hp).1, ?_⟩
    rw [← hz]
    have := minpoly.aeval ℤ (z : K)
    rw [aeval_def, eval₂_eq_eval_map] at this
    aesop
  simp_rw [preimage, mem_singleton_iff]
  apply Finite.subset _ this
  apply Finite.of_injOn (f := Units.val) (fun _ a ↦ a) (injOn_of_injective Units.val_injective)
    <| Multiset.finite_toSet (p.aroots K)

theorem IsOfFinOrder_of_InfinitePlace_le_one (h : ∀ v : InfinitePlace K, v x ≤ 1)
    (hx : IsIntegral ℤ (x : K)) : IsOfFinOrder x := by
  rw [isOfFinOrder_iff_pow_eq_one]
  let S : Submonoid Kˣ := Submonoid.closure {x}
  let f : ℕ → S := fun n ↦ ⟨x ^ n, by
      rw [Submonoid.mem_closure_singleton]
      exact ⟨n, rfl⟩⟩
  have := finite_closure_of_le_one h hx
  have : ¬ f.Injective := by
    apply not_injective_infinite_finite f
  have : ∃ n m, f n = f m ∧ n < m := by
    simp only [Function.Injective] at this
    grind
  obtain ⟨n, m, hxm, hne⟩ := this
  use m - n
  have : x ^ (m - n) = x ^ m / x ^ n := by
    refine Eq.symm (div_eq_of_eq_mul'' ?_)
    rw [← pow_add]
    rw [Nat.sub_add_eq_max]
    rw [max_eq_left <| le_of_lt hne]
  simp only [Subtype.mk.injEq, f] at hxm
  simp [this, hxm, hne]

open IntermediateField in
theorem Kronecker (hd : p.natDegree ≠ 0) (h_irr : Irreducible p) (h_mon : p.Monic)
    (hp : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1) : p = cyclotomic p.natDegree ℤ := by
  let K := SplittingField (p.map (algebraMap ℤ ℚ))
  have : NumberField K := by
    exact
      { to_charZero := SplittingField.instCharZero (map (algebraMap ℤ ℚ) p),
        to_finiteDimensional :=
          IsSplittingField.instFiniteDimensionalSplittingField (map (algebraMap ℤ ℚ) p) }


  sorry




-- ConjRootClass.minpoly.map_eq_prod
open ConjRootClass




theorem t2 {c : ConjRootClass ℚ ℂ} (h : ∀ x ∈ c.carrier, ‖x‖ = 1) :
    (c.minpoly.map (algebraMap ℚ ℂ)).mahlerMeasure = 1 := by
  have : Fintype c.carrier := {
    elems := by

      sorry,
    complete := sorry
  }

  --rw [ConjRootClass.minpoly.map_eq_prod]
  sorry

theorem t1 {c : ConjRootClass ℚ ℂ} (h : ∀ x ∈ c.carrier, ‖x‖ = 1) {x : ℂ} (hx : x ∈ c.carrier) :
    ∃ n, 0 < n ∧ x ^ n = 1 := by

  sorry


theorem Kronecker' (hd : p.natDegree ≠ 0) (h_irr : Irreducible p) (h_mon : p.Monic)
    (hp : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1) :
    ∃ k, (p.map (Int.castRingHom ℂ)).roots.toFinset = primitiveRoots k ℂ := by

  sorry




end Polynomial

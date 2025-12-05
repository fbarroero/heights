import Heights.IntMahlerMeasureofFn
import Heights.IntMinPoly

namespace Polynomial

variable {p : ℤ[X]} {K : Type*} [Field K]

open NumberField

theorem bb {x : K} (h : ∀ v : InfinitePlace K, v x ≤ 1) (n : ℕ) (v : InfinitePlace K) :
    v (x ^ n) ≤ 1 := by
  specialize h v
  simp
  refine pow_le_one₀ ?_ h
  exact apply_nonneg v x

variable [NumberField K]

theorem aa {x : K} (h : ∀ v : InfinitePlace K, v x ≤ 1) :
    ((minpoly ℚ x).map (algebraMap ℚ ℂ)).mahlerMeasure = 1 := by
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  have h1 : (minpoly ℚ x).leadingCoeff = 1 :=
    Monic.leadingCoeff <| minpoly.monic <| Algebra.IsIntegral.isIntegral x
  have hb (z : ℂ) (hz : z ∈ (minpoly ℚ x).aroots ℂ) : z ∈ (Set.range fun (φ : K →+* ℂ) => φ x) := by
    have := NumberField.Embeddings.range_eval_eq_rootSet_minpoly K ℂ x
    rw [rootSet] at this
    aesop
  have ha (z : ℂ) (hz : z ∈ (minpoly ℚ x).aroots ℂ) : ∃ v : InfinitePlace K, v x = ‖z‖ := by
    specialize hb z hz
    obtain ⟨φ, rfl⟩ := hb
    use InfinitePlace.mk φ
    simp
  have hm1 : ∀ z ∈ (minpoly ℚ x).aroots ℂ, max 1 ‖z‖ = 1 := by
    intro z hz
    obtain ⟨v, hv⟩ := ha z hz
    specialize h v
    rw [hv] at h
    simp [h]
  simp [h1]
  apply Multiset.prod_eq_one
  simp only [Multiset.mem_map, forall_exists_index, and_imp]
  intro _ z hx rfl
  exact hm1 z hx

--lemma (α β : Type*) (f :α → β)


section card

open Set

variable {A B : Type _} (f : A → B)

lemma finite_of_finite_image_finite_fibers
    {S : Set A} {T : Set B}
    (hMap : ∀ a ∈ S, f a ∈ T)
    (hT : T.Finite)
    (hFibers : ∀ b ∈ T, (S ∩ {a | f a = b}).Finite) :
    S.Finite := by
  --classical
  have : S = ⋃ b ∈ T, S ∩ {a | f a = b} := by
    ext a
    constructor
    · intro ha
      have hb : f a ∈ T := hMap a ha
      refine mem_iUnion.mpr ⟨f a, mem_iUnion.mpr ⟨hb, ?_⟩⟩
      simp [ha]
    · intro ha
      rcases mem_iUnion.mp ha with ⟨b, hb⟩
      rcases mem_iUnion.mp hb with ⟨hbT, hab⟩
      simpa using hab.1
  rw [this]
  exact Finite.biUnion' hT hFibers

end card

variable {x : Kˣ}

local notation3 "d" => (minpoly ℚ (x : K)).natDegree

local notation3 "BoxPoly" =>
  {p : ℤ[X] | p.natDegree ≤ d ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 1}

open Nat in
lemma bpcard : Set.Finite BoxPoly := by
  have : Set.ncard BoxPoly ≤
      ∏ i : Fin (d + 1), (2 * ⌊choose d i⌋₊ + 1) := by
    have := Polynomial.card_mahlerMeasure_le_prod d 1
    simp_all

  sorry

theorem dd (h : ∀ v : InfinitePlace K, v x ≤ 1) (hx : IsIntegral ℤ (x : K)) :
    Finite ↥(Subgroup.closure {x}) := by
  have (n : ℕ) : ((minpoly ℚ ((x : K) ^ n)).map (algebraMap ℚ ℂ)).mahlerMeasure = 1 := by
    refine aa ?_
    exact fun v ↦ bb h n v
  let f : (Subgroup.closure {x}).carrier → ℚ[X] := fun y ↦ minpoly ℚ ((y : Kˣ): K)
  --let s :=
  have : (Subgroup.closure {x}).carrier.Finite := by

    sorry
  --apply finite_of_finite_image_finite_fibers
  exact this

theorem cc (h : ∀ v : InfinitePlace K, v x ≤ 1) (hx : IsIntegral ℤ (x : K)) :
    ∃ k, 0 < k ∧ x ∈ rootsOfUnity k K := by
  simp_rw [mem_rootsOfUnity]
  let S : Subgroup Kˣ := Subgroup.closure {x}
  let f : ℕ → S := fun n ↦ ⟨x ^ n, by
      rw [Subgroup.mem_closure_singleton]
      exact ⟨n, rfl⟩⟩
  --let S := {y : K | ∃ n, y = x ^ n}
  have := dd h hx
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
 /-

  let f := fun v : InfinitePlace K => v x
  have : finprod (fun v : InfinitePlace K => v x) = 1 := finprod_eq_one_of_forall_eq_one h
  nth_rw 2 [← this] -/


  --rw [finprod_eq_prod_of_mulSupport_subset]






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


theorem Kronecker (hd : p.natDegree ≠ 0) (h_irr : Irreducible p) (h_mon : p.Monic)
    (hp : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1) : p = cyclotomic p.natDegree ℤ := by
  obtain ⟨k, hk⟩ := Kronecker' hd h_irr h_mon hp

  sorry



end Polynomial

import Mathlib

open Ideal IsDedekindDomain HeightOneSpectrum NumberField WithZeroMulInt


namespace NumberField.FinitePlace

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
variable {k : Type*} [Field k] [NumberField k] {F : Type*} [Field F]

instance [Algebra k K]: Algebra (𝓞 k) (𝓞 K) := inst_ringOfIntegersAlgebra k K

instance : FunLike (k →+* K) (𝓞 k) (𝓞 K) where

  coe := fun f ↦ by
    have : Algebra k K := f.toAlgebra
    have := inst_ringOfIntegersAlgebra k K
    intro a
    apply RingOfIntegers.restrict (M := 𝓞 k) (fun x ↦ f x) _ a
    intro x
    refine map_isIntegral_int f ?_
    exact RingOfIntegers.isIntegral_coe x
    --(algebraMap (𝓞 k) (𝓞 K)).comp f
  coe_injective' := fun f g h => by

    sorry

/-- The restriction of a finite place along an embedding. -/
def comap (w : FinitePlace K) (f : k →+* K) : FinitePlace k :=
  --have : FunLike F k K := by exact?
  have : (𝓞 k) →+* (𝓞 K) := by
    have : FunLike (k →+* K) k K := by
      exact RingHom.instFunLike
      --RingHom.instRingHomClass f k K

    have : RingHomClass (k →+* K) k K := by

      sorry
      --f.instRingHomClass k K
    apply NumberField.RingOfIntegers.mapRingHom (K := k) (L := K)
    sorry
  ⟨w.1.comp f.injective, by
    let a := Ideal.comap (R := 𝓞 k) f w.maximalIdeal.asIdeal
    sorry,
    by sorry⟩

end NumberField.FinitePlace


open NumberField Fintype Module

namespace NumberField.InfinitePlace

open scoped Finset

variable {k : Type*} [Field k] {K : Type*} [Field K] {F : Type*} [Field F]

/-- The restriction of an infinite place along an embedding. -/
def comap (w : InfinitePlace K) (f : k →+* K) : InfinitePlace k :=
  ⟨w.1.comp f.injective, w.embedding.comp f,
    by { ext x; show _ = w.1 (f x); rw [← w.2.choose_spec]; rfl }⟩

@[simp]
lemma comap_mk (φ : K →+* ℂ) (f : k →+* K) : (mk φ).comap f = mk (φ.comp f) := rfl

lemma comap_id (w : InfinitePlace K) : w.comap (RingHom.id K) = w := rfl

lemma comap_comp (w : InfinitePlace K) (f : F →+* K) (g : k →+* F) :
    w.comap (f.comp g) = (w.comap f).comap g := rfl

@[simp]
lemma comap_apply (w : InfinitePlace K) (f : k →+* K) (x : k) :
    w.comap f x = w (f x) := rfl

lemma comp_of_comap_eq {v : InfinitePlace k} {w : InfinitePlace K} {f : k →+* K}
    (h : w.comap f = v) (x : k) : w (f x) = v x := by
  simp [← h]

lemma comap_mk_lift [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k →+* ℂ) :
    (mk (ComplexEmbedding.lift K φ)).comap (algebraMap k K) = mk φ := by simp

lemma IsReal.comap (f : k →+* K) {w : InfinitePlace K} (hφ : IsReal w) :
    IsReal (w.comap f) := by
  rw [← mk_embedding w, comap_mk, isReal_mk_iff]
  rw [← mk_embedding w, isReal_mk_iff] at hφ
  exact hφ.comp f

lemma isReal_comap_iff (f : k ≃+* K) {w : InfinitePlace K} :
    IsReal (w.comap (f : k →+* K)) ↔ IsReal w := by
  rw [← mk_embedding w, comap_mk, isReal_mk_iff, isReal_mk_iff, ComplexEmbedding.isReal_comp_iff]

lemma comap_surjective [Algebra k K] [Algebra.IsAlgebraic k K] :
    Function.Surjective (comap · (algebraMap k K)) := fun w ↦
  ⟨(mk (ComplexEmbedding.lift K  w.embedding)), by simp⟩

lemma mult_comap_le (f : k →+* K) (w : InfinitePlace K) : mult (w.comap f) ≤ mult w := by
  rw [mult, mult]
  split_ifs with h₁ h₂ h₂
  pick_goal 3
  · exact (h₁ (h₂.comap _)).elim
  all_goals decide

variable [Algebra k K] (σ : K ≃ₐ[k] K) (w : InfinitePlace K)
variable (k K)

lemma card_mono [NumberField k] [NumberField K] :
    card (InfinitePlace k) ≤ card (InfinitePlace K) :=
  have := Module.Finite.of_restrictScalars_finite ℚ k K
  Fintype.card_le_of_surjective _ comap_surjective

variable {k K}

/-- The action of the galois group on infinite places. -/
@[simps! smul_coe_apply]
instance : MulAction (K ≃ₐ[k] K) (InfinitePlace K) where
  smul := fun σ w ↦ w.comap σ.symm
  one_smul := fun _ ↦ rfl
  mul_smul := fun _ _ _ ↦ rfl

lemma smul_eq_comap : σ • w = w.comap σ.symm := rfl

@[simp] lemma smul_apply (x) : (σ • w) x = w (σ.symm x) := rfl

@[simp] lemma smul_mk (φ : K →+* ℂ) : σ • mk φ = mk (φ.comp σ.symm) := rfl

lemma comap_smul {f : F →+* K} : (σ • w).comap f = w.comap (RingHom.comp σ.symm f) := rfl

variable {σ w}

lemma isReal_smul_iff : IsReal (σ • w) ↔ IsReal w := isReal_comap_iff (f := σ.symm.toRingEquiv)

lemma isComplex_smul_iff : IsComplex (σ • w) ↔ IsComplex w := by
  rw [← not_isReal_iff_isComplex, ← not_isReal_iff_isComplex, isReal_smul_iff]

lemma ComplexEmbedding.exists_comp_symm_eq_of_comp_eq [IsGalois k K] (φ ψ : K →+* ℂ)
    (h : φ.comp (algebraMap k K) = ψ.comp (algebraMap k K)) :
    ∃ σ : K ≃ₐ[k] K, φ.comp σ.symm = ψ := by
  letI := (φ.comp (algebraMap k K)).toAlgebra
  letI := φ.toAlgebra
  have : IsScalarTower k K ℂ := IsScalarTower.of_algebraMap_eq' rfl
  let ψ' : K →ₐ[k] ℂ := { ψ with commutes' := fun r ↦ (RingHom.congr_fun h r).symm }
  use (AlgHom.restrictNormal' ψ' K).symm
  ext1 x
  exact AlgHom.restrictNormal_commutes ψ' K x

lemma exists_smul_eq_of_comap_eq [IsGalois k K] {w w' : InfinitePlace K}
    (h : w.comap (algebraMap k K) = w'.comap (algebraMap k K)) : ∃ σ : K ≃ₐ[k] K, σ • w = w' := by
  rw [← mk_embedding w, ← mk_embedding w', comap_mk, comap_mk, mk_eq_iff] at h
  cases h with
  | inl h =>
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq w.embedding w'.embedding h
    use σ
    rw [← mk_embedding w, ← mk_embedding w', smul_mk, hσ]
  | inr h =>
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq
      ((starRingEnd ℂ).comp (embedding w)) w'.embedding h
    use σ
    rw [← mk_embedding w, ← mk_embedding w', smul_mk, mk_eq_iff]
    exact Or.inr hσ

lemma mem_orbit_iff [IsGalois k K] {w w' : InfinitePlace K} :
    w' ∈ MulAction.orbit (K ≃ₐ[k] K) w ↔ w.comap (algebraMap k K) = w'.comap (algebraMap k K) := by
  refine ⟨?_, exists_smul_eq_of_comap_eq⟩
  rintro ⟨σ, rfl : σ • w = w'⟩
  rw [← mk_embedding w, comap_mk, smul_mk, comap_mk]
  congr 1; ext1; simp

/-- The orbits of infinite places under the action of the galois group are indexed by
the infinite places of the base field. -/
noncomputable
def orbitRelEquiv [IsGalois k K] :
    Quotient (MulAction.orbitRel (K ≃ₐ[k] K) (InfinitePlace K)) ≃ InfinitePlace k := by
  refine Equiv.ofBijective (Quotient.lift (comap · (algebraMap k K))
    fun _ _ e ↦ (mem_orbit_iff.mp e).symm) ⟨?_, ?_⟩
  · rintro ⟨w⟩ ⟨w'⟩ e
    exact Quotient.sound (mem_orbit_iff.mpr e.symm)
  · intro w
    obtain ⟨w', hw⟩ := comap_surjective (K := K) w
    exact ⟨⟦w'⟧, hw⟩

lemma orbitRelEquiv_apply_mk'' [IsGalois k K] (w : InfinitePlace K) :
    orbitRelEquiv (Quotient.mk'' w) = comap w (algebraMap k K) := rfl

variable (k w)

/--
An infinite place is unramified in a field extension if the restriction has the same multiplicity.
-/
def IsUnramified : Prop := mult (w.comap (algebraMap k K)) = mult w

/--
An infinite place is ramified in a field extension if it is not unramified.
-/
abbrev IsRamified : Prop := ¬w.IsUnramified k

variable {k}

lemma isUnramified_self : IsUnramified K w := rfl

variable {w}

lemma IsUnramified.eq (h : IsUnramified k w) : mult (w.comap (algebraMap k K)) = mult w := h

lemma isUnramified_iff_mult_le :
    IsUnramified k w ↔ mult w ≤ mult (w.comap (algebraMap k K)) := by
  rw [IsUnramified, le_antisymm_iff, and_iff_right]
  exact mult_comap_le _ _

variable [Algebra k F]

lemma IsUnramified.comap_algHom {w : InfinitePlace F} (h : IsUnramified k w) (f : K →ₐ[k] F) :
    IsUnramified k (w.comap (f : K →+* F)) := by
  rw [InfinitePlace.isUnramified_iff_mult_le, ← InfinitePlace.comap_comp, f.comp_algebraMap, h.eq]
  exact InfinitePlace.mult_comap_le _ _

variable (K)
variable [Algebra K F] [IsScalarTower k K F]

lemma IsUnramified.of_restrictScalars {w : InfinitePlace F} (h : IsUnramified k w) :
    IsUnramified K w := by
  rw [InfinitePlace.isUnramified_iff_mult_le, ← h.eq, IsScalarTower.algebraMap_eq k K F,
    InfinitePlace.comap_comp]
  exact InfinitePlace.mult_comap_le _ _

lemma IsUnramified.comap {w : InfinitePlace F} (h : IsUnramified k w) :
    IsUnramified k (w.comap (algebraMap K F)) :=
  h.comap_algHom (IsScalarTower.toAlgHom k K F)

variable {K}

/--
An infinite place is not unramified (ie. ramified) iff it is a complex place above a real place.
-/
lemma not_isUnramified_iff :
    ¬ IsUnramified k w ↔ IsComplex w ∧ IsReal (w.comap (algebraMap k K)) := by
  rw [IsUnramified, mult, mult, ← not_isReal_iff_isComplex]
  split_ifs with h₁ h₂ h₂ <;>
    simp only [not_true_eq_false, false_iff, and_self, forall_true_left, IsEmpty.forall_iff,
      not_and, OfNat.one_ne_ofNat, not_false_eq_true, true_iff, OfNat.ofNat_ne_one, h₁, h₂]
  exact h₁ (h₂.comap _)

lemma isUnramified_iff :
    IsUnramified k w ↔ IsReal w ∨ IsComplex (w.comap (algebraMap k K)) := by
  rw [← not_iff_not, not_isUnramified_iff, not_or,
    not_isReal_iff_isComplex, not_isComplex_iff_isReal]

theorem isRamified_iff : w.IsRamified k ↔ w.IsComplex ∧ (w.comap (algebraMap k K)).IsReal :=
  not_isUnramified_iff

theorem IsRamified.ne_conjugate {w₁ w₂ : InfinitePlace K} (h : w₂.IsRamified k) :
    w₁.embedding ≠ ComplexEmbedding.conjugate w₂.embedding := by
  by_cases h_eq : w₁ = w₂
  · rw [isRamified_iff, isComplex_iff] at h
    exact Ne.symm (h_eq ▸ h.1)
  · contrapose! h_eq
    rw [← mk_embedding w₁, h_eq, mk_conjugate_eq, mk_embedding]

variable (k)

lemma IsReal.isUnramified (h : IsReal w) : IsUnramified k w := isUnramified_iff.mpr (Or.inl h)

variable {k}

lemma _root_.NumberField.ComplexEmbedding.IsConj.isUnramified_mk_iff
    {φ : K →+* ℂ} (h : ComplexEmbedding.IsConj φ σ) :
    IsUnramified k (mk φ) ↔ σ = 1 := by
  rw [h.ext_iff, ComplexEmbedding.isConj_one_iff, ← not_iff_not, not_isUnramified_iff,
    ← not_isReal_iff_isComplex, comap_mk, isReal_mk_iff, isReal_mk_iff, eq_true h.isReal_comp,
    and_true]

lemma isUnramified_mk_iff_forall_isConj [IsGalois k K] {φ : K →+* ℂ} :
    IsUnramified k (mk φ) ↔ ∀ σ : K ≃ₐ[k] K, ComplexEmbedding.IsConj φ σ → σ = 1 := by
  refine ⟨fun H σ hσ ↦ hσ.isUnramified_mk_iff.mp H,
    fun H ↦ ?_⟩
  by_contra hφ
  rw [not_isUnramified_iff] at hφ
  rw [comap_mk, isReal_mk_iff, ← not_isReal_iff_isComplex, isReal_mk_iff,
    ← ComplexEmbedding.isConj_one_iff (k := k)] at hφ
  letI := (φ.comp (algebraMap k K)).toAlgebra
  letI := φ.toAlgebra
  have : IsScalarTower k K ℂ := IsScalarTower.of_algebraMap_eq' rfl
  let φ' : K →ₐ[k] ℂ := { star φ with commutes' := fun r ↦ by simpa using RingHom.congr_fun hφ.2 r }
  have : ComplexEmbedding.IsConj φ (AlgHom.restrictNormal' φ' K) :=
    (RingHom.ext <| AlgHom.restrictNormal_commutes φ' K).symm
  exact hφ.1 (H _ this ▸ this)

local notation "Stab" => MulAction.stabilizer (K ≃ₐ[k] K)

lemma mem_stabilizer_mk_iff (φ : K →+* ℂ) (σ : K ≃ₐ[k] K) :
    σ ∈ Stab (mk φ) ↔ σ = 1 ∨ ComplexEmbedding.IsConj φ σ := by
  simp only [MulAction.mem_stabilizer_iff, smul_mk, mk_eq_iff]
  rw [← ComplexEmbedding.isConj_symm, ComplexEmbedding.conjugate, star_eq_iff_star_eq]
  refine or_congr ⟨fun H ↦ ?_, fun H ↦ H ▸ rfl⟩ Iff.rfl
  exact congr_arg AlgEquiv.symm
    (AlgEquiv.ext (g := AlgEquiv.refl) fun x ↦ φ.injective (RingHom.congr_fun H x))

lemma IsUnramified.stabilizer_eq_bot (h : IsUnramified k w) : Stab w = ⊥ := by
  rw [eq_bot_iff, ← mk_embedding w, SetLike.le_def]
  simp only [mem_stabilizer_mk_iff, Subgroup.mem_bot, forall_eq_or_imp, true_and]
  exact fun σ hσ ↦ hσ.isUnramified_mk_iff.mp ((mk_embedding w).symm ▸ h)

lemma _root_.NumberField.ComplexEmbedding.IsConj.coe_stabilzer_mk
    {φ : K →+* ℂ} (h : ComplexEmbedding.IsConj φ σ) :
    (Stab (mk φ) : Set (K ≃ₐ[k] K)) = {1, σ} := by
  ext
  rw [SetLike.mem_coe, mem_stabilizer_mk_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    ← h.ext_iff, eq_comm (a := σ)]

variable (k w)

lemma nat_card_stabilizer_eq_one_or_two :
    Nat.card (Stab w) = 1 ∨ Nat.card (Stab w) = 2 := by
  classical
  rw [← SetLike.coe_sort_coe, ← mk_embedding w]
  by_cases h : ∃ σ, ComplexEmbedding.IsConj (k := k) (embedding w) σ
  · obtain ⟨σ, hσ⟩ := h
    simp only [hσ.coe_stabilzer_mk, Nat.card_eq_fintype_card, card_ofFinset, Set.toFinset_singleton]
    by_cases 1 = σ
    · left; simp [*]
    · right; simp [*]
  · push_neg at h
    left
    trans Nat.card ({1} : Set (K ≃ₐ[k] K))
    · congr with x
      simp only [SetLike.mem_coe, mem_stabilizer_mk_iff, Set.mem_singleton_iff, or_iff_left_iff_imp,
        h x, IsEmpty.forall_iff]
    · simp

variable {k w}

lemma isUnramified_iff_stabilizer_eq_bot [IsGalois k K] : IsUnramified k w ↔ Stab w = ⊥ := by
  rw [← mk_embedding w, isUnramified_mk_iff_forall_isConj]
  simp only [eq_bot_iff, SetLike.le_def, mem_stabilizer_mk_iff,
    Subgroup.mem_bot, forall_eq_or_imp, true_and]

lemma isUnramified_iff_card_stabilizer_eq_one [IsGalois k K] :
    IsUnramified k w ↔ Nat.card (Stab w) = 1 := by
  rw [isUnramified_iff_stabilizer_eq_bot, Subgroup.card_eq_one]

lemma not_isUnramified_iff_card_stabilizer_eq_two [IsGalois k K] :
    ¬ IsUnramified k w ↔ Nat.card (Stab w) = 2 := by
  rw [isUnramified_iff_card_stabilizer_eq_one]
  obtain (e|e) := nat_card_stabilizer_eq_one_or_two k w <;> rw [e] <;> decide

lemma isRamified_iff_card_stabilizer_eq_two [IsGalois k K] :
    IsRamified k w ↔ Nat.card (Stab w) = 2 :=
  not_isUnramified_iff_card_stabilizer_eq_two

lemma exists_isConj_of_isRamified [IsGalois k K] {φ : K →+* ℂ} (h : IsRamified k (mk φ)) :
    ∃ σ : K ≃ₐ[k] K, ComplexEmbedding.IsConj φ σ := by
  rw [isRamified_iff_card_stabilizer_eq_two, Nat.card_eq_two_iff] at h
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, h₁, -⟩ := h
  rw [mem_stabilizer_mk_iff] at hx hy
  by_cases h : x = 1
  · exact ⟨y, hy.resolve_left (by rwa [ne_eq, Subtype.mk_eq_mk.not, h, eq_comm] at h₁)⟩
  · exact ⟨x, hx.resolve_left h⟩

open scoped Classical in
lemma card_stabilizer [IsGalois k K] :
    Nat.card (Stab w) = if IsUnramified k w then 1 else 2 := by
  split
  · rwa [← isUnramified_iff_card_stabilizer_eq_one]
  · rwa [← not_isUnramified_iff_card_stabilizer_eq_two]

lemma even_nat_card_aut_of_not_isUnramified [IsGalois k K] (hw : ¬ IsUnramified k w) :
    Even (Nat.card <| K ≃ₐ[k] K) := by
  by_cases H : Finite (K ≃ₐ[k] K)
  · cases nonempty_fintype (K ≃ₐ[k] K)
    rw [even_iff_two_dvd, ← not_isUnramified_iff_card_stabilizer_eq_two.mp hw]
    exact Subgroup.card_subgroup_dvd_card (Stab w)
  · convert Even.zero
    by_contra e
    exact H (Nat.finite_of_card_ne_zero e)

lemma even_card_aut_of_not_isUnramified [IsGalois k K] [FiniteDimensional k K]
    (hw : ¬ IsUnramified k w) :
    Even (Fintype.card <| K ≃ₐ[k] K) :=
  Nat.card_eq_fintype_card (α := K ≃ₐ[k] K) ▸ even_nat_card_aut_of_not_isUnramified hw

lemma even_finrank_of_not_isUnramified [IsGalois k K]
    (hw : ¬ IsUnramified k w) : Even (finrank k K) := by
  by_cases FiniteDimensional k K
  · exact IsGalois.card_aut_eq_finrank k K ▸ even_card_aut_of_not_isUnramified hw
  · exact finrank_of_not_finite ‹_› ▸ Even.zero

lemma isUnramified_smul_iff :
    IsUnramified k (σ • w) ↔ IsUnramified k w := by
  rw [isUnramified_iff, isUnramified_iff, isReal_smul_iff, comap_smul,
    ← AlgEquiv.toAlgHom_toRingHom, AlgHom.comp_algebraMap]

variable (K) in
/-- A infinite place of the base field is unramified in a field extension if every
infinite place over it is unramified. -/
def IsUnramifiedIn (w : InfinitePlace k) : Prop :=
  ∀ v, comap v (algebraMap k K) = w → IsUnramified k v

lemma isUnramifiedIn_comap [IsGalois k K] {w : InfinitePlace K} :
    (w.comap (algebraMap k K)).IsUnramifiedIn K ↔ w.IsUnramified k := by
  refine ⟨fun H ↦ H _ rfl, fun H v hv ↦ ?_⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_comap_eq hv
  rwa [isUnramified_smul_iff] at H

lemma even_card_aut_of_not_isUnramifiedIn [IsGalois k K] [FiniteDimensional k K]
    {w : InfinitePlace k} (hw : ¬ w.IsUnramifiedIn K) :
    Even (Fintype.card <| K ≃ₐ[k] K) := by
  obtain ⟨v, rfl⟩ := comap_surjective (K := K) w
  rw [isUnramifiedIn_comap] at hw
  exact even_card_aut_of_not_isUnramified hw

lemma even_finrank_of_not_isUnramifiedIn
    [IsGalois k K] {w : InfinitePlace k} (hw : ¬ w.IsUnramifiedIn K) :
    Even (finrank k K) := by
  obtain ⟨v, rfl⟩ := comap_surjective (K := K) w
  rw [isUnramifiedIn_comap] at hw
  exact even_finrank_of_not_isUnramified hw

variable (k K)
variable [NumberField K]

open Finset in
open scoped Classical in
lemma card_isUnramified [NumberField k] [IsGalois k K] :
    #{w : InfinitePlace K | w.IsUnramified k} =
      #{w : InfinitePlace k | w.IsUnramifiedIn K} * finrank k K := by
  letI := Module.Finite.of_restrictScalars_finite ℚ k K
  rw [← IsGalois.card_aut_eq_finrank,
    Finset.card_eq_sum_card_fiberwise (f := (comap · (algebraMap k K)))
    (t := {w : InfinitePlace k | w.IsUnramifiedIn K}), ← smul_eq_mul, ← sum_const]
  · refine sum_congr rfl (fun w hw ↦ ?_)
    obtain ⟨w, rfl⟩ := comap_surjective (K := K) w
    simp only [mem_univ, forall_true_left, mem_filter, true_and] at hw
    trans #(MulAction.orbit (K ≃ₐ[k] K) w).toFinset
    · congr; ext w'
      simp only [mem_univ, forall_true_left, filter_congr_decidable, mem_filter, true_and,
        Set.mem_toFinset, mem_orbit_iff, @eq_comm _ (comap w' _), and_iff_right_iff_imp]
      intro e; rwa [← isUnramifiedIn_comap, ← e]
    · rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ w,
        ← Nat.card_eq_fintype_card (α := Stab w), card_stabilizer, if_pos,
        mul_one, Set.toFinset_card]
      rwa [← isUnramifiedIn_comap]
  · simp [Set.MapsTo, isUnramifiedIn_comap]

open Finset in
open scoped Classical in
lemma card_isUnramified_compl [NumberField k] [IsGalois k K] :
    #({w : InfinitePlace K | w.IsUnramified k} : Finset _)ᶜ =
      #({w : InfinitePlace k | w.IsUnramifiedIn K} : Finset _)ᶜ * (finrank k K / 2) := by
  letI := Module.Finite.of_restrictScalars_finite ℚ k K
  rw [← IsGalois.card_aut_eq_finrank,
    Finset.card_eq_sum_card_fiberwise (f := (comap · (algebraMap k K)))
    (t := ({w : InfinitePlace k | w.IsUnramifiedIn K}: Finset _)ᶜ), ← smul_eq_mul, ← sum_const]
  · refine sum_congr rfl (fun w hw ↦ ?_)
    obtain ⟨w, rfl⟩ := comap_surjective (K := K) w
    simp only [mem_univ, forall_true_left, compl_filter, not_not, mem_filter, true_and] at hw
    trans Finset.card (MulAction.orbit (K ≃ₐ[k] K) w).toFinset
    · congr; ext w'
      simp only [compl_filter, filter_congr_decidable, mem_filter, mem_univ, true_and,
        @eq_comm _ (comap w' _), Set.mem_toFinset, mem_orbit_iff, and_iff_right_iff_imp]
      intro e; rwa [← isUnramifiedIn_comap, ← e]
    · rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group _ w,
        ← Nat.card_eq_fintype_card (α := Stab w), InfinitePlace.card_stabilizer, if_neg,
        Nat.mul_div_cancel _ zero_lt_two, Set.toFinset_card]
      rwa [← isUnramifiedIn_comap]
  · simp [Set.MapsTo, isUnramifiedIn_comap]

open scoped Classical in
lemma card_eq_card_isUnramifiedIn [NumberField k] [IsGalois k K] :
    Fintype.card (InfinitePlace K) =
      #{w : InfinitePlace k | w.IsUnramifiedIn K} * finrank k K +
      #({w : InfinitePlace k | w.IsUnramifiedIn K} : Finset _)ᶜ * (finrank k K / 2) := by
  rw [← card_isUnramified, ← card_isUnramified_compl, Finset.card_add_card_compl]

end NumberField.InfinitePlace

open NumberField

variable (k : Type*) [Field k] (K : Type*) [Field K] (F : Type*) [Field F]

variable [Algebra k K] [Algebra k F] [Algebra K F] [IsScalarTower k K F]

/-- A field extension is unramified at infinite places if every infinite place is unramified. -/
class IsUnramifiedAtInfinitePlaces : Prop where
  isUnramified : ∀ w : InfinitePlace K, w.IsUnramified k

instance IsUnramifiedAtInfinitePlaces.id : IsUnramifiedAtInfinitePlaces K K where
  isUnramified w := w.isUnramified_self

lemma IsUnramifiedAtInfinitePlaces.trans
    [h₁ : IsUnramifiedAtInfinitePlaces k K] [h₂ : IsUnramifiedAtInfinitePlaces K F] :
    IsUnramifiedAtInfinitePlaces k F where
  isUnramified w :=
    Eq.trans (IsScalarTower.algebraMap_eq k K F ▸ h₁.1 (w.comap (algebraMap _ _))) (h₂.1 w)

lemma IsUnramifiedAtInfinitePlaces.top [h : IsUnramifiedAtInfinitePlaces k F] :
    IsUnramifiedAtInfinitePlaces K F where
  isUnramified w := (h.1 w).of_restrictScalars K

lemma IsUnramifiedAtInfinitePlaces.bot [h₁ : IsUnramifiedAtInfinitePlaces k F]
    [Algebra.IsAlgebraic K F] :
    IsUnramifiedAtInfinitePlaces k K where
  isUnramified w := by
    obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (K := F) w
    exact (h₁.1 w).comap K

variable {K}

lemma NumberField.InfinitePlace.isUnramified [IsUnramifiedAtInfinitePlaces k K]
    (w : InfinitePlace K) : IsUnramified k w := IsUnramifiedAtInfinitePlaces.isUnramified w

variable {k} (K)

lemma NumberField.InfinitePlace.isUnramifiedIn [IsUnramifiedAtInfinitePlaces k K]
    (w : InfinitePlace k) : IsUnramifiedIn K w := fun v _ ↦ v.isUnramified k

variable {K}

lemma IsUnramifiedAtInfinitePlaces_of_odd_card_aut [IsGalois k K] [FiniteDimensional k K]
    (h : Odd (Fintype.card <| K ≃ₐ[k] K)) : IsUnramifiedAtInfinitePlaces k K :=
  ⟨fun _ ↦ not_not.mp (Nat.not_even_iff_odd.2 h ∘ InfinitePlace.even_card_aut_of_not_isUnramified)⟩

lemma IsUnramifiedAtInfinitePlaces_of_odd_finrank [IsGalois k K]
    (h : Odd (Module.finrank k K)) : IsUnramifiedAtInfinitePlaces k K :=
  ⟨fun _ ↦ not_not.mp (Nat.not_even_iff_odd.2 h ∘ InfinitePlace.even_finrank_of_not_isUnramified)⟩

variable (k K)

open Module in
lemma IsUnramifiedAtInfinitePlaces.card_infinitePlace [NumberField k] [NumberField K]
    [IsGalois k K] [IsUnramifiedAtInfinitePlaces k K] :
    Fintype.card (InfinitePlace K) = Fintype.card (InfinitePlace k) * finrank k K := by
  classical
  rw [InfinitePlace.card_eq_card_isUnramifiedIn (k := k) (K := K), Finset.filter_true_of_mem,
    Finset.card_univ, Finset.card_eq_zero.mpr, zero_mul, add_zero]
  · exact Finset.compl_univ
  simp only [Finset.mem_univ, forall_true_left, Finset.filter_eq_empty_iff]
  exact InfinitePlace.isUnramifiedIn K

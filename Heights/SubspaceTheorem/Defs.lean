module

public import Mathlib

/-!
# Schmidt's Subspace Theorem: definitions

We set up the language needed to state Schmidt's Subspace Theorem in its classical form
(W. M. Schmidt, *Norm form equations*, Ann. of Math. 96 (1972), 526–551):

> Let `L₁, …, Lₙ` be linearly independent linear forms in `n ≥ 2` variables with algebraic
> coefficients and let `ε > 0`. Then the set of solutions `x ∈ ℤⁿ` of
> `|L₁(x) ⋯ Lₙ(x)| ≤ ‖x‖ ^ (-ε)`
> is contained in the union of finitely many proper linear subspaces of `ℚⁿ`.

## References

* [J.-H. Evertse, *The Subspace Theorem of W. M. Schmidt*][evertse1993], Chapter IV of
  *Diophantine Approximation and Abelian Varieties* (B. Edixhoven, J.-H. Evertse eds.),
  Lecture Notes in Mathematics 1566, Springer, 1993. This is the reference we follow: the
  statement is Theorem 1.5 there and the proof is outlined in Section 3.
* [W. M. Schmidt, *Diophantine Approximation*][schmidt1980], Lecture Notes in Mathematics 785,
  Springer, 1980, Chapters IV–VI, for the complete details.

## Main definitions

The `n` variables are indexed by a finite type `ι`, and a system of linear forms in these variables
with real coefficients is a matrix `L : Matrix κ ι ℝ`: the `i`-th form is the one whose coefficients
are the `i`-th row of `L`.

* `Schmidt.eval L x`: the vector of the values `Lᵢ(x)` at the integer point `x`.
* `Schmidt.solutionSet L ε`: the set of `x ∈ ℤⁿ` with `|L₁(x) ⋯ Lₙ(x)| ≤ ‖x‖ ^ (-ε)`.
* `Schmidt.CoveredByProperSubspaces S`: the set `S` of integer points is contained in the union of
  finitely many proper linear subspaces of `ℚⁿ`.
* `Schmidt.box L a`: the set of integer points of the parallelepiped `|Lᵢ(x)| ≤ aᵢ`.
* `Schmidt.size a`: the quantity `Q(a) = max (a₁, …, aₙ, a₁⁻¹, …, aₙ⁻¹)`.

Here `‖x‖` is the sup norm `max |xᵢ|` of `x : ι → ℤ`.
-/

@[expose] public section

open Matrix

namespace Schmidt

variable {ι κ : Type*} [Fintype ι]

/-! ### Linear forms at integer points -/

/-- The vector `(L₁(x), …, Lₖ(x))` of the values at the integer point `x` of the linear forms
whose coefficients are the rows of `L`. -/
def eval (L : Matrix κ ι ℝ) (x : ι → ℤ) : κ → ℝ :=
  L *ᵥ fun j ↦ (x j : ℝ)

lemma eval_apply (L : Matrix κ ι ℝ) (x : ι → ℤ) (i : κ) : eval L x i = ∑ j, L i j * x j := rfl

@[simp]
lemma eval_zero (L : Matrix κ ι ℝ) : eval L 0 = 0 := by
  ext i; simp [eval_apply]

lemma eval_add (L : Matrix κ ι ℝ) (x y : ι → ℤ) : eval L (x + y) = eval L x + eval L y := by
  ext i; simp [eval_apply, mul_add, Finset.sum_add_distrib]

lemma eval_neg (L : Matrix κ ι ℝ) (x : ι → ℤ) : eval L (-x) = -eval L x := by
  ext i; simp [eval_apply]

lemma eval_smul (L : Matrix κ ι ℝ) (k : ℤ) (x : ι → ℤ) : eval L (k • x) = (k : ℝ) • eval L x := by
  ext i; simp [eval_apply, Finset.mul_sum, mul_left_comm]

/-- The set of solutions `x ∈ ℤⁿ` of the inequality `|L₁(x) ⋯ Lₙ(x)| ≤ ‖x‖ ^ (-ε)`. -/
def solutionSet (L : Matrix ι ι ℝ) (ε : ℝ) : Set (ι → ℤ) :=
  {x | |∏ i, eval L x i| ≤ ‖x‖ ^ (-ε)}

lemma mem_solutionSet {L : Matrix ι ι ℝ} {ε : ℝ} {x : ι → ℤ} :
    x ∈ solutionSet L ε ↔ |∏ i, eval L x i| ≤ ‖x‖ ^ (-ε) := Iff.rfl

/-! ### Sets covered by finitely many proper subspaces -/

/-- A set `S` of integer points is contained in the union of finitely many proper linear
subspaces of `ℚⁿ`. -/
def CoveredByProperSubspaces (S : Set (ι → ℤ)) : Prop :=
  ∃ T : Finset (Submodule ℚ (ι → ℚ)), (∀ V ∈ T, V ≠ ⊤) ∧
    ∀ x ∈ S, ∃ V ∈ T, (fun i ↦ (x i : ℚ)) ∈ V

namespace CoveredByProperSubspaces

variable {S S' : Set (ι → ℤ)}

omit [Fintype ι] in
lemma mono (h : CoveredByProperSubspaces S') (hS : S ⊆ S') : CoveredByProperSubspaces S := by
  obtain ⟨T, hT, h⟩ := h
  exact ⟨T, hT, fun x hx ↦ h x (hS hx)⟩

omit [Fintype ι] in
lemma empty : CoveredByProperSubspaces (∅ : Set (ι → ℤ)) :=
  ⟨∅, by simp, by simp⟩

omit [Fintype ι] in
lemma union (h : CoveredByProperSubspaces S) (h' : CoveredByProperSubspaces S') :
    CoveredByProperSubspaces (S ∪ S') := by
  classical
  obtain ⟨T, hT, h⟩ := h
  obtain ⟨T', hT', h'⟩ := h'
  refine ⟨T ∪ T', fun V hV ↦ ?_, fun x hx ↦ ?_⟩
  · rcases Finset.mem_union.mp hV with hV | hV
    exacts [hT V hV, hT' V hV]
  · rcases hx with hx | hx
    · obtain ⟨V, hV, hxV⟩ := h x hx
      exact ⟨V, Finset.mem_union_left _ hV, hxV⟩
    · obtain ⟨V, hV, hxV⟩ := h' x hx
      exact ⟨V, Finset.mem_union_right _ hV, hxV⟩

omit [Fintype ι] in
lemma biUnion {α : Type*} (s : Finset α) (S : α → Set (ι → ℤ))
    (h : ∀ i ∈ s, CoveredByProperSubspaces (S i)) :
    CoveredByProperSubspaces (⋃ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using empty
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    exact (h a (Finset.mem_insert_self a s)).union
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

omit [Fintype ι] in
lemma iUnion {α : Type*} [Finite α] (S : α → Set (ι → ℤ))
    (h : ∀ i, CoveredByProperSubspaces (S i)) : CoveredByProperSubspaces (⋃ i, S i) := by
  have := Fintype.ofFinite α
  simpa using biUnion Finset.univ S fun i _ ↦ h i

/-- The integer points at which a nonzero linear form with real coefficients vanishes lie in a
proper subspace of `ℚⁿ`. -/
lemma of_real_form (c : ι → ℝ) (hc : c ≠ 0) :
    CoveredByProperSubspaces {x : ι → ℤ | ∑ i, c i * x i = 0} := by
  classical
  let f : (ι → ℚ) →ₗ[ℚ] ℝ := ∑ i, (LinearMap.toSpanSingleton ℚ ℝ (c i)) ∘ₗ (LinearMap.proj i)
  have hf (v : ι → ℚ) : f v = ∑ i, c i * (v i : ℝ) := by
    simp [f, LinearMap.sum_apply, Rat.smul_def, mul_comm]
  refine ⟨{LinearMap.ker f}, fun V hV htop ↦ ?_, fun x hx ↦ ⟨_, Finset.mem_singleton_self _, ?_⟩⟩
  · rw [Finset.mem_singleton] at hV
    subst hV
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    have : Pi.single j (1 : ℚ) ∈ LinearMap.ker f := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hf, Finset.sum_eq_single j (fun b _ hb ↦ by simp [hb]) (by simp)] at this
    exact hj (by simpa using this)
  · rw [LinearMap.mem_ker, hf]
    simpa using hx

/-- The integer points orthogonal to a nonzero integer vector lie in a proper subspace of `ℚⁿ`. -/
lemma of_dotProduct (c : ι → ℤ) (hc : c ≠ 0) :
    CoveredByProperSubspaces {x : ι → ℤ | c ⬝ᵥ x = 0} := by
  have hc' : (fun i ↦ (c i : ℝ)) ≠ 0 := fun h ↦ hc <| by
    ext i
    simpa using congrFun h i
  refine (of_real_form _ hc').mono fun x hx ↦ ?_
  have : ((c ⬝ᵥ x : ℤ) : ℝ) = 0 := by rw [hx]; simp
  simpa [dotProduct] using this

/-- A finite union of hyperplanes orthogonal to nonzero integer vectors is covered by finitely
many proper subspaces of `ℚⁿ`. -/
lemma of_normals (T : Finset (ι → ℤ)) (hT : ∀ c ∈ T, c ≠ 0)
    (h : ∀ x ∈ S, ∃ c ∈ T, c ⬝ᵥ x = 0) : CoveredByProperSubspaces S := by
  refine (biUnion T (fun c ↦ {x : ι → ℤ | c ⬝ᵥ x = 0}) fun c hc ↦
    of_dotProduct c (hT c hc)).mono fun x hx ↦ ?_
  obtain ⟨c, hc, hcx⟩ := h x hx
  exact Set.mem_biUnion hc hcx

/-- If `n ≥ 2`, then every integer point lies in a proper subspace of `ℚⁿ`. -/
lemma singleton [Nontrivial ι] (x : ι → ℤ) : CoveredByProperSubspaces {x} := by
  classical
  refine ⟨{Submodule.span ℚ {fun i ↦ (x i : ℚ)}}, fun V hV htop ↦ ?_, fun y hy ↦
    ⟨_, Finset.mem_singleton_self _, ?_⟩⟩
  · rw [Finset.mem_singleton] at hV
    subst hV
    have h1 := finrank_span_finset_le_card (R := ℚ) ({fun i ↦ (x i : ℚ)} : Finset (ι → ℚ))
    rw [Set.finrank, Finset.coe_singleton, htop, finrank_top, Module.finrank_fintype_fun_eq_card,
      Finset.card_singleton] at h1
    exact absurd h1 (not_le.mpr Fintype.one_lt_card)
  · rw [Set.mem_singleton_iff.mp hy]
    exact Submodule.mem_span_singleton_self _

/-- If `n ≥ 2`, then every finite set of integer points is covered by finitely many proper
subspaces of `ℚⁿ`. -/
lemma of_finite [Nontrivial ι] (hS : S.Finite) : CoveredByProperSubspaces S := by
  have := (biUnion hS.toFinset (fun x ↦ {x}) fun x _ ↦ singleton x)
  refine this.mono fun x hx ↦ ?_
  simpa using hx

end CoveredByProperSubspaces

/-! ### Parallelepipeds -/

/-- The set of integer points of the parallelepiped `Π(a) = {x ∈ ℝⁿ : |Lᵢ(x)| ≤ aᵢ for all i}`. -/
def box (L : Matrix κ ι ℝ) (a : κ → ℝ) : Set (ι → ℤ) :=
  {x | ∀ i, |eval L x i| ≤ a i}

lemma mem_box {L : Matrix κ ι ℝ} {a : κ → ℝ} {x : ι → ℤ} :
    x ∈ box L a ↔ ∀ i, |eval L x i| ≤ a i := Iff.rfl

lemma zero_mem_box {L : Matrix κ ι ℝ} {a : κ → ℝ} (ha : ∀ i, 0 ≤ a i) : 0 ∈ box L a := by
  simpa [mem_box] using ha

lemma neg_mem_box {L : Matrix κ ι ℝ} {a : κ → ℝ} {x : ι → ℤ} (hx : x ∈ box L a) :
    -x ∈ box L a := by
  simpa [mem_box, eval_neg] using hx

/-- The quantity `Q(a) = max (a₁, …, aₙ, a₁⁻¹, …, aₙ⁻¹)` attached to a tuple `a` of positive real
numbers. -/
noncomputable def size [Fintype κ] (a : κ → ℝ) : ℝ :=
  ⨆ i, max (a i) (a i)⁻¹

section size

variable [Fintype κ] {a : κ → ℝ}

lemma le_size (a : κ → ℝ) (i : κ) : a i ≤ size a :=
  (le_max_left _ _).trans (le_ciSup (f := fun i ↦ max (a i) (a i)⁻¹) (Finite.bddAbove_range _) i)

lemma inv_le_size (a : κ → ℝ) (i : κ) : (a i)⁻¹ ≤ size a :=
  (le_max_right _ _).trans (le_ciSup (f := fun i ↦ max (a i) (a i)⁻¹) (Finite.bddAbove_range _) i)

lemma size_le [Nonempty κ] {B : ℝ} (h : ∀ i, a i ≤ B) (h' : ∀ i, (a i)⁻¹ ≤ B) : size a ≤ B :=
  ciSup_le fun i ↦ max_le (h i) (h' i)

lemma one_le_size [Nonempty κ] (ha : ∀ i, 0 < a i) : 1 ≤ size a := by
  obtain ⟨i⟩ := ‹Nonempty κ›
  rcases le_total 1 (a i) with h | h
  · exact h.trans (le_size a i)
  · exact ((one_le_inv₀ (ha i)).mpr h).trans (inv_le_size a i)

lemma inv_size_le (ha : ∀ i, 0 < a i) (i : κ) : (size a)⁻¹ ≤ a i := by
  have := inv_le_size a i
  exact inv_le_of_inv_le₀ (ha i) this

end size

end Schmidt

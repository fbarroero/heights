module

public import Heights.SubspaceTheorem.Compound
public import Heights.SubspaceTheorem.Minkowski
public import Heights.SubspaceTheorem.UnipotentReduction

/-!
# Step 1 of the proof: reduction to parallelepipeds of rank `n - 1`

This file contains the statement of [evertse1993], Proposition 3.3.2: if the parallelepiped
`Π(a)` has small volume, then there are `m` with `0 < m < n` and a parallelepiped `Π_m(b)` in
`ℝ^N`, `N = n.choose m`, defined by the compound linear forms `L_σ = l_{i₁} ∧ ⋯ ∧ l_{iₘ}`, which
also has small volume and whose integer points span a hyperplane. Moreover, this hyperplane
determines a `(n - m)`-dimensional subspace of `ℚⁿ` containing the integer points of `Π(a)`.

The proof combines Minkowski's second theorem (`Schmidt.exists_successive_minima`) with
[evertse1993], Lemma 3.3.5 (`Schmidt.exists_unipotent_mul_le`).
-/

@[expose] public section

open Matrix Set.powersetCard

namespace Schmidt

variable {ι : Type*} [Fintype ι]

/-! ### Auxiliary definitions -/

/-- The product `∏_{i ∈ s} a i` attached to an `m`-subset `s` of `ι`. -/
noncomputable def sprod {m : ℕ} (a : ι → ℝ) (s : Set.powersetCard ι m) : ℝ :=
  ∏ i ∈ (s : Finset ι), a i

/-- The constant `4 ^ N * m!`, `N = n.choose m`, appearing in the definition of the tuple `b`. -/
noncomputable def C0 (ι : Type*) [Fintype ι] (m : ℕ) : ℝ :=
  4 ^ Fintype.card (Set.powersetCard ι m) * m.factorial

/-- The alternating extension to arbitrary `m`-tuples of indices of a vector `c` indexed by
`m`-subsets: if `f = (increasing enumeration of s) ∘ π` then the value is `sign π * c s`,
and it is `0` if `f` is not injective. -/
noncomputable def altCoord [LinearOrder ι] {m : ℕ} (c : Set.powersetCard ι m → ℤ)
    (f : Fin m → ι) : ℤ :=
  open Classical in
  if h : ∃ (s : Set.powersetCard ι m) (π : Equiv.Perm (Fin m)), f = ofFinEmbEquiv.symm s ∘ π then
    Equiv.Perm.sign h.choose_spec.choose * c h.choose else 0

/-- The map sending a normal vector `c` of the hyperplane `f_k(V)` of `ℚ^N` to a normal vector of
a hyperplane of `ℚⁿ` containing `V` (see `Schmidt.exists_compound_box`). -/
noncomputable def Phi [LinearOrder ι] : (m : ℕ) → (Set.powersetCard ι m → ℤ) → ι → ℤ
  | 0, _ => fun _ ↦ 1
  | _ + 1, c =>
    open Classical in
    if h : ∃ s, c s ≠ 0 then
      fun j ↦ altCoord c (Fin.snoc (ofFinEmbEquiv.symm h.choose ∘ Fin.castSucc) j)
    else fun _ ↦ 1

/-- The data extracted from Minkowski's second theorem in the proof of
`Schmidt.exists_compound_box`: `lam` are the successive minima (reindexed by `ι`), the columns of
`G` are the corresponding integer points, `T` is the set of the indices of the last `m` minima,
and `ρ` is the ratio `λ_k / λ_{k+1}`, where `k = n - m`. -/
structure MinimaData [DecidableEq ι] (L : Matrix ι ι ℝ) (ε C : ℝ) (a lam : ι → ℝ) (G : Matrix ι ι ℤ)
    (T : Finset ι) (ρ : ℝ) : Prop where
  lam_pos : ∀ j, 0 < lam j
  det_ne : G.det ≠ 0
  eval_le : ∀ i j, |eval L (fun l ↦ G l j) i| ≤ a i * lam j
  prod_le : (∏ j, lam j) * ∏ i, a i ≤ C
  lam_ge : ∀ j, 1 ≤ C * lam j * size a
  card_pos : 0 < T.card
  card_lt : T.card < Fintype.card ι
  rho_pos : 0 < ρ
  rho_le_one : ρ ≤ 1
  rho_le : ρ ≤ C * size a ^ (-(ε / (Fintype.card ι * ((Fintype.card ι : ℝ) - 1))))
  le_rho_mul : ∀ i ∉ T, ∀ j ∈ T, lam i ≤ ρ * lam j
  rho_ge : ∃ j ∈ T, 1 ≤ C * (ρ * lam j) * size a
  ker : ∀ x ∈ box L a, ∀ j ∈ T, ((G.map (Int.cast : ℤ → ℚ))⁻¹ *ᵥ fun i ↦ (x i : ℚ)) j = 0

/-! ### Determinant bounds -/

/-- If `|M i j| ≤ r i * c j` then `|det M| ≤ k! * ∏ r * ∏ c`. -/
lemma abs_det_le {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℝ) (r c : κ → ℝ)
    (h : ∀ i j, |M i j| ≤ r i * c j) :
    |M.det| ≤ (Fintype.card κ).factorial * ((∏ i, r i) * ∏ j, c j) := by
  rw [Matrix.det_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have key : ∀ σ : Equiv.Perm κ, |Equiv.Perm.sign σ • ∏ i, M (σ i) i| ≤
      (∏ i, r i) * ∏ j, c j := by
    intro σ
    rw [Units.smul_def, zsmul_eq_mul, abs_mul, Finset.abs_prod]
    have h1 : |(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [h1, one_mul]
    calc ∏ i, |M (σ i) i| ≤ ∏ i, (r (σ i) * c i) :=
          Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) (fun i _ ↦ h _ _)
      _ = _ := by rw [Finset.prod_mul_distrib, Equiv.prod_comp σ r]
  refine (Finset.sum_le_sum fun σ _ ↦ key σ).trans ?_
  simp [Finset.card_univ, Fintype.card_perm]

/-- If the columns of the integer matrix `X` with non-zero determinant satisfy
`|Mᵢ(Xⱼ)| ≤ r i * c j`, then `|det M| ≤ k! * ∏ r * ∏ c`. -/
lemma abs_det_le_of_eval_le {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℝ)
    (X : Matrix κ κ ℤ) (hX : X.det ≠ 0) (r c : κ → ℝ)
    (h : ∀ i j, |eval M (fun l ↦ X l j) i| ≤ r i * c j) :
    |M.det| ≤ (Fintype.card κ).factorial * ((∏ i, r i) * ∏ j, c j) := by
  have h1 : ∀ i j, (M * X.map (Int.cast : ℤ → ℝ)) i j = eval M (fun l ↦ X l j) i := fun i j ↦ by
    simp [Matrix.mul_apply, eval_apply]
  have h2 := abs_det_le (M * X.map (Int.cast : ℤ → ℝ)) r c (fun i j ↦ by rw [h1]; exact h i j)
  rw [Matrix.det_mul, abs_mul] at h2
  have h3 : (1 : ℝ) ≤ |(X.map (Int.cast : ℤ → ℝ)).det| := by
    have : (X.map (Int.cast : ℤ → ℝ)).det = ((X.det : ℤ) : ℝ) := by
      simpa using (RingHom.map_det (Int.castRingHom ℝ) X).symm
    rw [this, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hX
  nlinarith [abs_nonneg M.det]

/-! ### The map `Φ` -/

omit [Fintype ι] in
/-- Taking compound matrices commutes with ring homomorphisms. -/
lemma compound_map {R S : Type*} [CommRing R] [CommRing S] [LinearOrder ι] (f : R →+* S)
    (A : Matrix ι ι R) (m : ℕ) : compound (A.map f) m = (compound A m).map f := by
  ext s t
  simp only [compound_apply, Matrix.map_apply]
  rw [RingHom.map_det]
  rfl

lemma altCoord_eq [LinearOrder ι] {m : ℕ} (c : Set.powersetCard ι m → ℤ) (f : Fin m → ι)
    (s : Set.powersetCard ι m) (π : Equiv.Perm (Fin m)) (hf : f = ofFinEmbEquiv.symm s ∘ π) :
    altCoord c f = Equiv.Perm.sign π * c s := by
  have h : ∃ (s' : Set.powersetCard ι m) (π' : Equiv.Perm (Fin m)),
      f = ofFinEmbEquiv.symm s' ∘ π' := ⟨s, π, hf⟩
  simp only [altCoord, h, ↓reduceDIte]
  have h2 := h.choose_spec.choose_spec
  generalize h.choose_spec.choose = π' at h2 ⊢
  generalize h.choose = s' at h2 ⊢
  have hr : Set.range (ofFinEmbEquiv.symm s') = Set.range (ofFinEmbEquiv.symm s) := by
    have h3 := congrArg Set.range (h2.symm.trans hf)
    rwa [EquivLike.range_comp, EquivLike.range_comp] at h3
  have hs : s' = s := by
    refine Subtype.ext (Finset.ext fun i ↦ ?_)
    have h4 := mem_range_ofFinEmbEquiv_symm_iff_mem s' i
    have h5 := mem_range_ofFinEmbEquiv_symm_iff_mem s i
    rw [hr] at h4
    exact (h4.symm.trans h5)
  subst hs
  have hπ : π' = π := by
    refine Equiv.ext fun j ↦ (ofFinEmbEquiv.symm s').injective ?_
    exact congrFun (h2.symm.trans hf) j
  rw [hπ]

/-- The alternating extension of a vector of `m × m` minors of a matrix `H` (up to a scalar) is
given by the determinants of arbitrary `m`-tuples of columns of `H`. -/
lemma cast_altCoord_eq [LinearOrder ι] {m : ℕ} (c : Set.powersetCard ι m → ℤ) (μ : ℚ)
    (H : Matrix (Fin m) ι ℚ)
    (hc : ∀ s, (c s : ℚ) = μ * (H.submatrix id (ofFinEmbEquiv.symm s)).det) (f : Fin m → ι) :
    (altCoord c f : ℚ) = μ * (H.submatrix id f).det := by
  by_cases h : ∃ (s : Set.powersetCard ι m) (π : Equiv.Perm (Fin m)),
      f = ofFinEmbEquiv.symm s ∘ π
  · obtain ⟨s, π, rfl⟩ := h
    rw [altCoord_eq c _ s π rfl]
    have h1 : H.submatrix id (ofFinEmbEquiv.symm s ∘ π) =
        (H.submatrix id (ofFinEmbEquiv.symm s)).submatrix id π := rfl
    rw [h1, Matrix.det_permute', Int.cast_mul, hc]
    ring
  · have hf : ¬ Function.Injective f := by
      intro hf
      apply h
      let s : Set.powersetCard ι m := ofFinEmb m ι ⟨f, hf⟩
      have hmem : ∀ j, ∃ k, ofFinEmbEquiv.symm s k = f j := fun j ↦ by
        have : f j ∈ s := (mem_ofFinEmb_iff_mem_range m ι ⟨f, hf⟩ (f j)).mpr ⟨j, rfl⟩
        exact (mem_range_ofFinEmbEquiv_symm_iff_mem s (f j)).mpr this
      choose g hg using hmem
      have ginj : Function.Injective g := fun i j hij ↦ hf (by rw [← hg i, ← hg j, hij])
      refine ⟨s, Equiv.ofBijective g (Finite.injective_iff_bijective.mp ginj), ?_⟩
      funext j
      exact (hg j).symm
    simp only [altCoord, h, ↓reduceDIte]
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
      simpa [Function.Injective] using hf
    rw [Matrix.det_zero_of_column_eq hne (fun k ↦ by simp [hij])]
    simp

/-- `Φ m c` is never zero. -/
lemma Phi_ne_zero [LinearOrder ι] [Nonempty ι] (m : ℕ) (c : Set.powersetCard ι m → ℤ) :
    Phi m c ≠ 0 := by
  have h1 : (fun _ : ι ↦ (1 : ℤ)) ≠ 0 := fun h ↦ by
    simpa using congrFun h (Classical.arbitrary ι)
  cases m with
  | zero => exact h1
  | succ m =>
    rw [Phi]
    split_ifs with h
    · intro h0
      have h2 := congrFun h0 (ofFinEmbEquiv.symm h.choose (Fin.last m))
      have key : (Fin.snoc (α := fun _ ↦ ι) (ofFinEmbEquiv.symm h.choose ∘ Fin.castSucc)
          (ofFinEmbEquiv.symm h.choose (Fin.last m)) : Fin (m + 1) → ι) =
          ofFinEmbEquiv.symm h.choose ∘ (1 : Equiv.Perm (Fin (m + 1))) := by
        funext i
        refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp
      simp only [Pi.zero_apply] at h2
      rw [altCoord_eq c _ _ 1 key] at h2
      simp only [Equiv.Perm.sign_one, Units.val_one, one_mul] at h2
      exact h.choose_spec h2
    · exact h1

/-- If `c ≠ 0` is orthogonal to all the columns of the `m`-th compound of the integer matrix `G`
except the column `T`, then `Φ m c` is orthogonal to the span of the columns of `G` outside `T`. -/
lemma Phi_dotProduct_eq_zero [LinearOrder ι] (m : ℕ) (hm : 0 < m)
    (c : Set.powersetCard ι m → ℤ) (hc : c ≠ 0)
    (G : Matrix ι ι ℤ) (hG : G.det ≠ 0) (T : Set.powersetCard ι m)
    (hcT : ∀ τ, τ ≠ T → c ⬝ᵥ (fun σ ↦ compound G m σ τ) = 0) (x : ι → ℤ)
    (hx : ∀ j ∈ (T : Finset ι), ((G.map (Int.cast : ℤ → ℚ))⁻¹ *ᵥ fun i ↦ (x i : ℚ)) j = 0) :
    Phi m c ⬝ᵥ x = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  set Gq : Matrix ι ι ℚ := G.map (Int.cast : ℤ → ℚ) with hGq
  have hGq' : Gq = G.map (Int.castRingHom ℚ) := rfl
  have hdet : Gq.det ≠ 0 := by
    have h1 := (RingHom.map_det (Int.castRingHom ℚ) G).symm
    rw [RingHom.mapMatrix_apply] at h1
    rw [hGq', h1]
    simpa using hG
  have hinv : compound Gq (m + 1) * compound Gq⁻¹ (m + 1) = 1 := by
    rw [← compound_mul, Matrix.mul_nonsing_inv Gq (Ne.isUnit hdet), compound_one]
  set μ : ℚ := ∑ σ, (c σ : ℚ) * compound Gq (m + 1) σ T with hμ
  have hrow : (fun σ ↦ (c σ : ℚ)) ᵥ* compound Gq (m + 1) = fun τ ↦ if τ = T then μ else 0 := by
    funext τ
    by_cases hτ : τ = T
    · subst hτ
      simp [Matrix.vecMul, dotProduct, hμ]
    · have h1 := congrArg (Int.cast : ℤ → ℚ) (hcT τ hτ)
      simp only [hτ, ↓reduceIte]
      rw [← Int.cast_zero, ← h1, hGq', compound_map]
      simp [Matrix.vecMul, dotProduct]
  have hcρ : ∀ ρ, (c ρ : ℚ) = μ * compound Gq⁻¹ (m + 1) T ρ := by
    intro ρ
    have h1 : (fun σ ↦ (c σ : ℚ)) = ((fun σ ↦ (c σ : ℚ)) ᵥ* compound Gq (m + 1)) ᵥ*
        compound Gq⁻¹ (m + 1) := by
      rw [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
    rw [hrow] at h1
    have h2 := congrFun h1 ρ
    simpa [Matrix.vecMul, dotProduct] using h2
  set H : Matrix (Fin (m + 1)) ι ℚ := Gq⁻¹.submatrix (ofFinEmbEquiv.symm T) id with hH
  have hHx : H *ᵥ (fun i ↦ (x i : ℚ)) = 0 := by
    funext k
    have h1 := hx (ofFinEmbEquiv.symm T k)
      ((mem_range_ofFinEmbEquiv_symm_iff_mem T _).mp ⟨k, rfl⟩)
    simpa [hH, Matrix.mulVec, dotProduct] using h1
  have halt := cast_altCoord_eq c μ H (fun s ↦ by rw [hcρ s]; rfl)
  have hex : ∃ s, c s ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  have hPhi : Phi (m + 1) c = fun j ↦ altCoord c
      (Fin.snoc (α := fun _ ↦ ι) (ofFinEmbEquiv.symm hex.choose ∘ Fin.castSucc) j) := by
    simp only [Phi, hex, ↓reduceDIte]
  set s₀ := hex.choose
  set B₀ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ := H.submatrix id (ofFinEmbEquiv.symm s₀)
  have hdetj : ∀ j, (H.submatrix id (Fin.snoc (α := fun _ ↦ ι)
      (ofFinEmbEquiv.symm s₀ ∘ Fin.castSucc) j)).det =
      Matrix.cramer B₀ (fun k ↦ H k j) (Fin.last m) := by
    intro j
    rw [Matrix.cramer_apply]
    congr 1
    ext k l
    refine Fin.lastCases ?_ (fun l ↦ ?_) l
    · simp [B₀]
    · simp [B₀, Fin.castSucc_ne_last]
  have hsum : ∑ j, Matrix.cramer B₀ (fun k ↦ H k j) (Fin.last m) * (x j : ℚ) = 0 := by
    have h1 : H *ᵥ (fun i ↦ (x i : ℚ)) = ∑ j, (x j : ℚ) • (fun k ↦ H k j) := by
      funext k
      simp [Matrix.mulVec, dotProduct, mul_comm]
    have h2 := congrArg (fun v ↦ Matrix.cramer B₀ v (Fin.last m)) h1
    simp only [hHx, map_zero, map_sum, map_smul, Pi.zero_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h2
    rw [h2]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hfinal : ((Phi (m + 1) c ⬝ᵥ x : ℤ) : ℚ) = 0 := by
    rw [hPhi]
    simp only [dotProduct, Int.cast_sum, Int.cast_mul]
    simp_rw [halt, hdetj, mul_assoc]
    rw [← Finset.mul_sum, hsum, mul_zero]
  exact_mod_cast hfinal

/-! ### Minkowski's theorem -/

/-- A linearly independent family of integer points of a set `S` has at most
`Set.finrank ℤ S` elements. -/
lemma card_le_setFinrank {κ κ' : Type*} [Fintype κ] [Fintype κ'] (v : κ' → κ → ℤ)
    (hv : LinearIndependent ℤ v) (S : Set (κ → ℤ)) (h : ∀ i, v i ∈ S) :
    Fintype.card κ' ≤ Set.finrank ℤ S := by
  let v' : κ' → Submodule.span ℤ S := fun i ↦ ⟨v i, Submodule.subset_span (h i)⟩
  have hv' : LinearIndependent ℤ v' := LinearIndependent.of_comp (Submodule.span ℤ S).subtype hv
  exact hv'.fintype_card_le_finrank

lemma exists_forall_lt_rpow (K : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∃ R : ℝ, ∀ Q : ℝ, R ≤ Q → K < Q ^ γ :=
  Filter.eventually_atTop.mp ((tendsto_rpow_atTop hγ).eventually_gt_atTop K)

/-- A non-zero integer point `x` satisfies `1 ≪ max |Lᵢ(x)|`. -/
lemma exists_norm_bound [DecidableEq ι] (L : Matrix ι ι ℝ) (hL : L.det ≠ 0) :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ (x : ι → ℤ) (B : ℝ), x ≠ 0 → (∀ i, |eval L x i| ≤ B) → 1 ≤ P * B := by
  have hS : 0 ≤ ∑ i, ∑ j, |L⁻¹ i j| :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _
  refine ⟨1 + ∑ i, ∑ j, |L⁻¹ i j|, by linarith, fun x B hx hB ↦ ?_⟩
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB i₀)
  have h1 : (x i₀ : ℝ) = ∑ j, L⁻¹ i₀ j * eval L x j := by
    have h2 : L⁻¹ *ᵥ eval L x = fun j ↦ (x j : ℝ) := by
      rw [eval, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L (Ne.isUnit hL), Matrix.one_mulVec]
    exact (congrFun h2 i₀).symm
  have h3 : (1 : ℝ) ≤ |(x i₀ : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hi₀
  have h4 : |(x i₀ : ℝ)| ≤ (∑ j, |L⁻¹ i₀ j|) * B := by
    rw [h1, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB j) (abs_nonneg _)
  have h5 : ∑ j, |L⁻¹ i₀ j| ≤ ∑ i, ∑ j, |L⁻¹ i j| :=
    Finset.single_le_sum (f := fun i ↦ ∑ j, |L⁻¹ i j|)
      (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _) (Finset.mem_univ i₀)
  linarith [mul_le_mul_of_nonneg_right h5 hB0]

/-- If `f s ≤ ρ ^ (d + 1) * f (s + d + 1)`, then `f j ≤ ρ * f (j + 1)` for some `s ≤ j ≤ s + d`. -/
lemma exists_ratio_le (f : ℕ → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (s d : ℕ)
    (h : f s ≤ ρ ^ (d + 1) * f (s + d + 1)) :
    ∃ j, s ≤ j ∧ j ≤ s + d ∧ f j ≤ ρ * f (j + 1) := by
  induction d with
  | zero => exact ⟨s, le_rfl, le_rfl, by simpa using h⟩
  | succ d ih =>
    by_cases hc : f (s + d + 1) ≤ ρ * f (s + d + 1 + 1)
    · exact ⟨s + d + 1, by omega, by omega, hc⟩
    · push Not at hc
      have h1 : f s ≤ ρ ^ (d + 1) * f (s + d + 1) := by
        change f s ≤ ρ ^ (d + 1 + 1) * f (s + d + 1 + 1) at h
        refine h.trans ?_
        have h2 : ρ ^ (d + 1 + 1) * f (s + d + 1 + 1) =
            ρ ^ (d + 1) * (ρ * f (s + d + 1 + 1)) := by
          rw [pow_succ ρ (d + 1)]
          ring
        rw [h2]
        exact mul_le_mul_of_nonneg_left hc.le (by positivity)
      obtain ⟨j, h1, h2, h3⟩ := ih h1
      exact ⟨j, h1, by omega, h3⟩

/-- If the columns of the integer matrix `G` with indices in `I` lie in the parallelepiped and
the integer points of the parallelepiped span a module of rank at most `#I`, then every integer
point of the parallelepiped lies in the `ℚ`-span of these columns. -/
lemma inv_mulVec_eq_zero_of_finrank_le [DecidableEq ι] (L : Matrix ι ι ℝ) (a : ι → ℝ)
    (G : Matrix ι ι ℤ) (hG : G.det ≠ 0) (I : Finset ι)
    (hI : ∀ j ∈ I, (fun i ↦ G i j) ∈ box L a) (hrank : Set.finrank ℤ (box L a) ≤ I.card)
    (x : ι → ℤ) (hx : x ∈ box L a) (j : ι) (hj : j ∉ I) :
    ((G.map (Int.cast : ℤ → ℚ))⁻¹ *ᵥ fun i ↦ (x i : ℚ)) j = 0 := by
  by_contra hne
  set Gq : Matrix ι ι ℚ := G.map (Int.cast : ℤ → ℚ) with hGq
  have hGq' : Gq = G.map (Int.castRingHom ℚ) := rfl
  have hGqdet : Gq.det ≠ 0 := by
    have h1 := (RingHom.map_det (Int.castRingHom ℚ) G).symm
    rw [RingHom.mapMatrix_apply] at h1
    rw [hGq', h1]
    simpa using hG
  have h1 : Matrix.cramer Gq (fun i ↦ (x i : ℚ)) j =
      Gq.det * (Gq⁻¹ *ᵥ fun i ↦ (x i : ℚ)) j := by
    rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.inv_def, Ring.inverse_eq_inv',
      Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hGqdet]
  have h2 : (G.updateCol j x).det ≠ 0 := by
    intro h0
    have h3 : (G.updateCol j x).map (Int.castRingHom ℚ) =
        Gq.updateCol j (fun i ↦ (x i : ℚ)) := by
      ext i k
      by_cases hk : k = j <;> simp [hk, hGq]
    have h4 := RingHom.map_det (Int.castRingHom ℚ) (G.updateCol j x)
    rw [RingHom.mapMatrix_apply, h3, h0] at h4
    rw [← Matrix.cramer_apply, h1] at h4
    simp only [map_zero, zero_eq_mul] at h4
    rcases h4 with h4 | h4
    · exact hGqdet h4
    · exact hne h4
  have hli := Matrix.linearIndependent_cols_of_det_ne_zero h2
  have hli' := hli.comp (Subtype.val : (↥(insert j I)) → ι) Subtype.val_injective
  have h5 := card_le_setFinrank _ hli' (box L a) (fun k ↦ by
    change (fun i ↦ (G.updateCol j x) i k) ∈ box L a
    by_cases hk : (k : ι) = j
    · have h6 : (fun i ↦ (G.updateCol j x) i k) = x := by
        funext i
        simp [hk]
      rw [h6]
      exact hx
    · have h6 : (fun i ↦ (G.updateCol j x) i k) = fun i ↦ G i k := by
        funext i
        simp [hk]
      rw [h6]
      exact hI k ((Finset.mem_insert.mp k.2).resolve_left hk))
  rw [Fintype.card_coe, Finset.card_insert_of_notMem hj] at h5
  omega

/-- Steps (1) and (2): the data given by Minkowski's second theorem when `Q(a)` is large. -/
lemma exists_minimaData [DecidableEq ι] [Nontrivial ι] (L : Matrix ι ι ℝ) (hL : L.det ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Q₀ : ℝ, ∀ a : ι → ℝ, (∀ i, 0 < a i) → ∏ i, a i < size a ^ (-ε) →
      Q₀ ≤ size a → (∃ x ∈ box L a, x ≠ 0) →
      ∃ (lam : ι → ℝ) (G : Matrix ι ι ℤ) (T : Finset ι) (ρ : ℝ), MinimaData L ε C a lam G T ρ := by
  have hn2 : 2 ≤ (Fintype.card ι) := Fintype.one_lt_card
  have hnR : (2 : ℝ) ≤ (Fintype.card ι) := by exact_mod_cast hn2
  have hn1 : (0 : ℝ) < ((Fintype.card ι) : ℝ) - 1 := by linarith
  obtain ⟨P, hP1, hP⟩ := exists_norm_bound L hL
  have hdet : 0 < |L.det| := abs_pos.mpr hL
  have hfac : (0 : ℝ) < ((Fintype.card ι)).factorial := by exact_mod_cast Nat.factorial_pos _
  set c₀ : ℝ := |L.det| / ((Fintype.card ι)).factorial with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  set β : ℝ := 1 / (((Fintype.card ι) : ℝ) * (((Fintype.card ι) : ℝ) - 1)) with hβ
  have hβpos : 0 < β := by positivity
  set C : ℝ := 1 + ((Fintype.card ι) : ℝ) ^ (Fintype.card ι) * |L.det| + P + c₀ ^ (-β) with hC
  have hcβ : 0 < c₀ ^ (-β) := Real.rpow_pos_of_pos hc₀pos _
  have hD0 : 0 ≤ ((Fintype.card ι) : ℝ) ^ (Fintype.card ι) * |L.det| := by positivity
  obtain ⟨R, hR⟩ := exists_forall_lt_rpow (1 / c₀) hε
  refine ⟨C, by linarith, R, fun a ha hprod hQ hx ↦ ?_⟩
  obtain ⟨lam, g, hmono, hpos, hli, hbox, hmin, hprodle⟩ := exists_successive_minima L hL a ha
  set Q := size a with hQdef
  have hQ1 : 1 ≤ Q := one_le_size ha
  have hQpos : 0 < Q := by linarith
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  set G : Matrix ι ι ℤ := Matrix.of fun l j ↦ g (e j) l with hGdef
  have hcol : ∀ j, (fun l ↦ G l j) = g (e j) := fun j ↦ rfl
  have hG : G.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hli' := hli.comp e e.injective
    rw [Fintype.linearIndependent_iff] at hli'
    apply hv0
    funext k
    refine hli' v ?_ k
    funext l
    have := congrFun hv l
    simpa [Matrix.mulVec, dotProduct, hGdef, mul_comm] using this
  have heval : ∀ i j, |eval L (fun l ↦ G l j) i| ≤ a i * lam (e j) := by
    intro i j
    rw [hcol, mul_comm]
    exact hbox (e j) i
  have hprod' : ∏ j, lam (e j) = ∏ j, lam j := Equiv.prod_comp e lam
  have hF1 := abs_det_le_of_eval_le L G hG a (fun j ↦ lam (e j)) heval
  rw [hprod'] at hF1
  have hapos : 0 < ∏ i, a i := Finset.prod_pos fun i _ ↦ ha i
  have hlampos : 0 < ∏ j, lam j := Finset.prod_pos fun i _ ↦ hpos i
  set last : Fin (Fintype.card ι) := ⟨(Fintype.card ι) - 1, by omega⟩ with hlast
  have hle_last : ∀ j, lam j ≤ lam last := fun j ↦
    hmono (Fin.mk_le_mk.mpr (by have := j.2; omega))
  have hprodlast : ∏ j, lam j ≤ lam last ^ (Fintype.card ι) := by
    have := Finset.prod_le_prod₀ (s := Finset.univ) (fun j _ ↦ (hpos j).le)
      (fun j _ ↦ hle_last j)
    simpa using this
  set A := Q ^ ε with hA
  have hApos : 0 < A := Real.rpow_pos_of_pos hQpos _
  have hprodA : (∏ i, a i) < A⁻¹ := by rwa [hA, ← Real.rpow_neg hQpos.le]
  have hlastn : c₀ * A < lam last ^ (Fintype.card ι) := by
    have h1 : |L.det| < ((Fintype.card ι)).factorial * (A⁻¹ * lam last ^ (Fintype.card ι)) := by
      calc |L.det| ≤ ((Fintype.card ι)).factorial * ((∏ i, a i) * ∏ j, lam j) := hF1
        _ < ((Fintype.card ι)).factorial * (A⁻¹ * lam last ^ (Fintype.card ι)) :=
          mul_lt_mul_of_pos_left
            (mul_lt_mul hprodA hprodlast hlampos (inv_pos.mpr hApos).le) hfac
    rw [hc₀, div_mul_eq_mul_div, div_lt_iff₀ hfac]
    calc |L.det| * A < ((Fintype.card ι)).factorial * (A⁻¹ * lam last ^ (Fintype.card ι)) * A :=
          mul_lt_mul_of_pos_right h1 hApos
      _ = lam last ^ (Fintype.card ι) * ((Fintype.card ι)).factorial := by field_simp
  have hRQ := hR Q hQ
  have hcA : 1 < c₀ * A := by
    rw [div_lt_iff₀ hc₀pos] at hRQ
    linarith
  have hlast1 : 1 < lam last := by
    by_contra h
    push Not at h
    have := pow_le_one₀ (hpos last).le h (n := (Fintype.card ι))
    linarith
  set lamN : ℕ → ℝ := fun i ↦ if h : i < (Fintype.card ι) then lam ⟨i, h⟩ else lam last with hlamN
  have hlamN_fin : ∀ j : Fin (Fintype.card ι), lamN j = lam j := fun j ↦ by simp [hlamN, j.2]
  have hlamN_lt : ∀ i (h : i < (Fintype.card ι)), lamN i = lam ⟨i, h⟩ := fun i h ↦ by simp [hlamN, h]
  have hlamN_pos : ∀ i, 0 < lamN i := fun i ↦ by
    simp only [hlamN]
    split_ifs <;> exact hpos _
  have hlamN_mono : Monotone lamN := by
    intro i k hik
    simp only [hlamN]
    split_ifs with h1 h2 h2
    · exact hmono (Fin.mk_le_mk.mpr hik)
    · exact hle_last _
    · omega
    · exact le_rfl
  have hex : ∃ j, 1 < lamN j :=
    ⟨(Fintype.card ι) - 1, by rw [hlamN_lt ((Fintype.card ι) - 1) (by omega)]; exact hlast1⟩
  set j₂ := Nat.find hex with hj₂def
  have hj₂ : 1 < lamN j₂ := Nat.find_spec hex
  have hj₂min : ∀ i, i < j₂ → lamN i ≤ 1 := fun i hi ↦ not_lt.mp (Nat.find_min hex hi)
  have hj₂n : j₂ ≤ (Fintype.card ι) - 1 :=
    Nat.find_min' hex (by rw [hlamN_lt ((Fintype.card ι) - 1) (by omega)]; exact hlast1)
  have hj₂lt : j₂ < (Fintype.card ι) := by omega
  have hrank : Set.finrank ℤ (box L a) ≤ j₂ := by
    have := hmin ⟨j₂, hj₂lt⟩ 1 (by rw [← hlamN_lt j₂ hj₂lt]; exact hj₂)
    simpa using this
  set I : Finset ι := Finset.univ.filter (fun k ↦ (e k : ℕ) < j₂) with hI
  have hIcard : j₂ ≤ I.card := by
    have := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin j₂))) (t := I)
      (fun p ↦ e.symm ⟨p, by omega⟩) (fun p _ ↦ by simp [hI]) (fun p _ q _ hpq ↦ by
        have := e.symm.injective hpq
        exact Fin.ext (by simpa using this))
    simpa using this
  have hIbox : ∀ k ∈ I, (fun i ↦ G i k) ∈ box L a := by
    intro k hk i
    have hk' : (e k : ℕ) < j₂ := (Finset.mem_filter.mp hk).2
    have h1 : lam (e k) ≤ 1 := by
      rw [← hlamN_fin]
      exact hj₂min _ hk'
    exact (heval i k).trans (mul_le_of_le_one_right (ha i).le h1)
  have hker : ∀ x ∈ box L a, ∀ k, j₂ ≤ (e k : ℕ) →
      ((G.map (Int.cast : ℤ → ℚ))⁻¹ *ᵥ fun i ↦ (x i : ℚ)) k = 0 := fun x hx k hk ↦
    inv_mulVec_eq_zero_of_finrank_le L a G hG I hIbox (hrank.trans hIcard) x hx k
      (by simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
  have hj₂pos : 0 < j₂ := by
    by_contra h0
    obtain ⟨x, hxbox, hxne⟩ := hx
    apply hxne
    have h1 : (G.map (Int.cast : ℤ → ℚ))⁻¹ *ᵥ (fun i ↦ (x i : ℚ)) = 0 :=
      funext fun k ↦ hker x hxbox k (by omega)
    have hGq : (G.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
      have h2 := (RingHom.map_det (Int.castRingHom ℚ) G).symm
      rw [RingHom.mapMatrix_apply] at h2
      change (G.map (Int.castRingHom ℚ)).det ≠ 0
      rw [h2]
      simpa using hG
    have h3 : (fun i ↦ (x i : ℚ)) = 0 := by
      have := congrArg (fun v ↦ (G.map (Int.cast : ℤ → ℚ)) *ᵥ v) h1
      simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hGq)] using this
    funext i
    have h4 := congrFun h3 i
    simp only [Pi.zero_apply] at h4 ⊢
    exact_mod_cast h4
  have hlastpos := hpos last
  set ρ₀ : ℝ := (lam last ^ (Fintype.card ι)) ^ (-β) with hρ₀
  have hρ₀pos : 0 < ρ₀ := Real.rpow_pos_of_pos (pow_pos hlastpos _) _
  have hρ₀le1 : ρ₀ ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ hlast1.le) (by linarith)
  have hρ₀pow : ρ₀ ^ ((Fintype.card ι) - 1) = (lam last)⁻¹ := by
    rw [hρ₀, ← Real.rpow_natCast (lam last) (Fintype.card ι), ← Real.rpow_mul hlastpos.le,
      ← Real.rpow_natCast _ ((Fintype.card ι) - 1), ← Real.rpow_mul hlastpos.le, ← Real.rpow_neg_one]
    congr 1
    rw [hβ, Nat.cast_sub (by omega)]
    push_cast
    field_simp
  have hρ₀le : ρ₀ ≤ C * Q ^ (-(ε / ((Fintype.card ι) * (((Fintype.card ι) : ℝ) - 1)))) := by
    have h1 : ρ₀ ≤ (c₀ * A) ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlastn.le (by linarith)
    have h2 : (c₀ * A) ^ (-β) = c₀ ^ (-β) * Q ^ (-(ε / ((Fintype.card ι) * (((Fintype.card ι) : ℝ) - 1)))) := by
      rw [Real.mul_rpow hc₀pos.le hApos.le, hA, ← Real.rpow_mul hQpos.le]
      congr 2
      rw [hβ]
      field_simp
    rw [h2] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos hQpos _).le)
    rw [hC]
    linarith
  obtain ⟨k0, hk0s, hk0d, hk0⟩ := exists_ratio_le lamN ρ₀ hρ₀pos (j₂ - 1) ((Fintype.card ι) - 1 - j₂) (by
    have e1 : j₂ - 1 + ((Fintype.card ι) - 1 - j₂) + 1 = (Fintype.card ι) - 1 := by omega
    rw [e1, hlamN_lt ((Fintype.card ι) - 1) (by omega)]
    have h1 : lamN (j₂ - 1) ≤ 1 := hj₂min _ (by omega)
    have h2 : ρ₀ ^ ((Fintype.card ι) - 1) ≤ ρ₀ ^ ((Fintype.card ι) - 1 - j₂ + 1) :=
      pow_le_pow_of_le_one hρ₀pos.le hρ₀le1 (by omega)
    have h3 : (1 : ℝ) = ρ₀ ^ ((Fintype.card ι) - 1) * lam last := by
      rw [hρ₀pow, inv_mul_cancel₀ hlastpos.ne']
    calc lamN (j₂ - 1) ≤ 1 := h1
      _ = ρ₀ ^ ((Fintype.card ι) - 1) * lam last := h3
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 hlastpos.le)
  have hk0n : k0 + 1 < (Fintype.card ι) := by omega
  set ρ := lamN k0 / lamN (k0 + 1) with hρ
  have hρpos : 0 < ρ := div_pos (hlamN_pos _) (hlamN_pos _)
  have hρle : ρ ≤ ρ₀ := by
    rw [hρ, div_le_iff₀ (hlamN_pos _)]
    exact hk0
  have hρmul : ρ * lamN (k0 + 1) = lamN k0 := div_mul_cancel₀ _ (hlamN_pos _).ne'
  set T : Finset ι := Finset.univ.filter (fun k ↦ k0 < (e k : ℕ)) with hT
  have hlam_ge : ∀ j, 1 ≤ C * lam (e j) * Q := by
    intro j
    have h1 := hP (g (e j)) (lam (e j) * Q) (hli.ne_zero (e j)) (fun i ↦ by
      refine (hbox (e j) i).trans ?_
      exact mul_le_mul_of_nonneg_left (le_size a i) (hpos _).le)
    have h2 : 0 ≤ lam (e j) * Q := mul_nonneg (hpos _).le hQpos.le
    have h3 : P ≤ C := by
      rw [hC]
      linarith
    nlinarith [mul_le_mul_of_nonneg_right h3 h2]
  refine ⟨fun j ↦ lam (e j), G, T, ρ, ?_⟩
  exact
  { lam_pos := fun j ↦ hpos _
    det_ne := hG
    eval_le := heval
    prod_le := by
      rw [hprod']
      refine hprodle.trans ?_
      rw [hC]
      linarith
    lam_ge := hlam_ge
    card_pos := Finset.card_pos.mpr ⟨e.symm ⟨k0 + 1, hk0n⟩, by simp [hT]⟩
    card_lt := Finset.card_lt_univ_of_notMem (x := e.symm ⟨0, by omega⟩) (by simp [hT])
    rho_pos := hρpos
    rho_le_one := hρle.trans hρ₀le1
    rho_le := hρle.trans hρ₀le
    le_rho_mul := by
      intro i hi j hj
      have hi' : (e i : ℕ) ≤ k0 := by simpa [hT] using hi
      have hj' : k0 < (e j : ℕ) := by simpa [hT] using hj
      rw [← hlamN_fin, ← hlamN_fin]
      calc lamN (e i) ≤ lamN k0 := hlamN_mono hi'
        _ = ρ * lamN (k0 + 1) := hρmul.symm
        _ ≤ ρ * lamN (e j) := mul_le_mul_of_nonneg_left (hlamN_mono hj') hρpos.le
    rho_ge := ⟨e.symm ⟨k0 + 1, hk0n⟩, by simp [hT], by
      have h1 := hlam_ge (e.symm ⟨k0, by omega⟩)
      simp only [Equiv.apply_symm_apply] at h1 ⊢
      rw [← hlamN_lt (k0 + 1) hk0n, hρmul, hlamN_lt k0 (by omega)]
      exact h1⟩
    ker := fun x hx j hj ↦ hker x hx j (by
      have : k0 < (e j : ℕ) := by simpa [hT] using hj
      omega) }

/-! ### The compound parallelepiped -/

/-- An enumeration of a finite type along which `w` is monotone and which ends with a given
element at which `w` is maximal. -/
lemma exists_sorted_equiv {S : Type*} [Fintype S] (w : S → ℝ) (t : S) (ht : ∀ s, w s ≤ w t) :
    ∃ f : Fin (Fintype.card S) ≃ S, Monotone (w ∘ f) ∧ ∀ p, p ≤ f.symm t := by
  classical
  let e₀ : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let w' : S → ℝ := fun s ↦ if s = t then w t + 1 else w s
  let σ := Tuple.sort (w' ∘ e₀)
  have hmono : Monotone ((w' ∘ e₀) ∘ σ) := Tuple.monotone_sort _
  let f : Fin (Fintype.card S) ≃ S := σ.trans e₀
  have hf : ∀ p, w' (f p) = ((w' ∘ e₀) ∘ σ) p := fun p ↦ rfl
  have htop : ∀ p, p ≤ f.symm t := by
    intro p
    by_contra h
    push Not at h
    have h1 := hmono h.le
    rw [← hf, ← hf, Equiv.apply_symm_apply] at h1
    have hp : f p ≠ t := fun hp ↦ by
      rw [← hp, Equiv.symm_apply_apply] at h
      exact lt_irrefl _ h
    simp only [w', hp, ↓reduceIte] at h1
    linarith [ht (f p)]
  refine ⟨f, fun p q hpq ↦ ?_, htop⟩
  change w (f p) ≤ w (f q)
  by_cases hq : f q = t
  · rw [hq]
    exact ht _
  · have hp : f p ≠ t := fun hp ↦ hq (by
      have h1 : q ≤ p := by
        rw [← Equiv.symm_apply_apply f p, hp]
        exact htop q
      rw [← le_antisymm hpq h1]
      exact hp)
    have h1 := hmono hpq
    rw [← hf, ← hf] at h1
    simpa [w', hp, hq] using h1

omit [Fintype ι] in
lemma prod_ofFinEmbEquiv_symm [LinearOrder ι] {m : ℕ} (x : ι → ℝ) (s : Set.powersetCard ι m) :
    ∏ i : Fin m, x (ofFinEmbEquiv.symm s i) = sprod x s := by
  have h : Finset.univ.map (ofFinEmbEquiv.symm s).toEmbedding = (s : Finset ι) := by
    rw [ofFinEmbEquiv_symm_apply]
    exact Finset.map_orderEmbOfFin_univ _ _
  rw [sprod, ← h, Finset.prod_map]
  rfl

omit [Fintype ι] in
/-- If `lam i ≤ ρ * lam j` for `i ∉ T` and `j ∈ T`, then `∏_τ lam ≤ ρ * ∏_T lam` for every `τ ≠ T`
with as many elements as `T`. -/
lemma sprod_le_rho_mul [DecidableEq ι] {m : ℕ} (lam : ι → ℝ) (hlam : ∀ j, 0 < lam j) (ρ : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (T τ : Set.powersetCard ι m)
    (hT : ∀ i ∉ (T : Finset ι), ∀ j ∈ (T : Finset ι), lam i ≤ ρ * lam j) (hτ : τ ≠ T) :
    sprod lam τ ≤ ρ * sprod lam T := by
  have hcard : ((τ : Finset ι) \ T).card = ((T : Finset ι) \ τ).card :=
    Finset.card_sdiff_comm ((Set.powersetCard.card_eq τ).trans (Set.powersetCard.card_eq T).symm)
  have h1 := Finset.prod_inter_mul_prod_sdiff (τ : Finset ι) T lam
  have h2 := Finset.prod_inter_mul_prod_sdiff (T : Finset ι) τ lam
  have hne : ((τ : Finset ι) \ T).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hτ (Set.powersetCard.eq_iff_subset.mpr hsub)
  have hne' : ((T : Finset ι) \ τ).Nonempty := by
    rw [← Finset.card_pos, ← hcard, Finset.card_pos]
    exact hne
  obtain ⟨i₁, hi₁, hmax⟩ := Finset.exists_max_image _ lam hne
  obtain ⟨j₂, hj₂, hmin⟩ := Finset.exists_min_image _ lam hne'
  have hij : lam i₁ ≤ ρ * lam j₂ :=
    hT i₁ (Finset.mem_sdiff.mp hi₁).2 j₂ (Finset.mem_sdiff.mp hj₂).1
  set d := ((τ : Finset ι) \ T).card with hd
  have hd1 : d ≠ 0 := (Finset.card_pos.mpr hne).ne'
  have h3 : ∏ i ∈ (τ : Finset ι) \ T, lam i ≤ lam i₁ ^ d := by
    have := Finset.prod_le_prod₀ (s := (τ : Finset ι) \ T) (fun i _ ↦ (hlam i).le)
      (fun i hi ↦ hmax i hi)
    simpa using this
  have h4 : lam j₂ ^ d ≤ ∏ j ∈ (T : Finset ι) \ τ, lam j := by
    have := Finset.prod_le_prod₀ (s := (T : Finset ι) \ τ) (fun i _ ↦ (hlam j₂).le)
      (fun i hi ↦ hmin i hi)
    simpa [← hcard] using this
  have h5 : lam i₁ ^ d ≤ ρ * lam j₂ ^ d := by
    calc lam i₁ ^ d ≤ (ρ * lam j₂) ^ d := pow_le_pow_left₀ (hlam i₁).le hij d
      _ = ρ ^ d * lam j₂ ^ d := mul_pow _ _ _
      _ ≤ ρ * lam j₂ ^ d :=
        mul_le_mul_of_nonneg_right (pow_le_of_le_one hρ.le hρ1 hd1) (pow_pos (hlam j₂) d).le
  have h6 : (τ : Finset ι) ∩ T = (T : Finset ι) ∩ τ := Finset.inter_comm _ _
  rw [sprod, sprod, ← h1, ← h2, h6]
  have hI : 0 < ∏ i ∈ (T : Finset ι) ∩ τ, lam i := Finset.prod_pos fun j _ ↦ hlam j
  have h7 : ∏ i ∈ (τ : Finset ι) \ T, lam i ≤ ρ * ∏ j ∈ (T : Finset ι) \ τ, lam j := by
    linarith [mul_le_mul_of_nonneg_left h4 hρ.le]
  calc _ ≤ (∏ i ∈ (T : Finset ι) ∩ τ, lam i) * (ρ * ∏ j ∈ (T : Finset ι) \ τ, lam j) :=
        mul_le_mul_of_nonneg_left h7 hI.le
    _ = _ := by ring

/-- Steps (3)–(5), algebraic part: construction of the tuple `b`. -/
lemma exists_box_of_minima [LinearOrder ι] (L : Matrix ι ι ℝ) (hL : L.det ≠ 0) (m : ℕ)
    (a lam : ι → ℝ) (G : Matrix ι ι ℤ) (T : Set.powersetCard ι m) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hlam : ∀ j, 0 < lam j) (hG : G.det ≠ 0)
    (hLG : ∀ i j, |eval L (fun l ↦ G l j) i| ≤ a i * lam j) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hT : ∀ i ∉ (T : Finset ι), ∀ j ∈ (T : Finset ι), lam i ≤ ρ * lam j) :
    ∃ b : Set.powersetCard ι m → ℝ,
      (∀ s, ∃ t, b s = C0 ι m * sprod a s * (sprod lam t * if t = T then ρ else 1)) ∧
      ∏ s, b s = C0 ι m ^ Fintype.card (Set.powersetCard ι m) * (∏ s : Set.powersetCard ι m,
        sprod a s) * (∏ s : Set.powersetCard ι m, sprod lam s) * ρ ∧
      Fintype.card (Set.powersetCard ι m) ≤ Set.finrank ℤ (box (compound L m) b) + 1 ∧
      ∀ c : Set.powersetCard ι m → ℤ, c ≠ 0 → (∀ y ∈ box (compound L m) b, c ⬝ᵥ y = 0) →
        ∀ τ, τ ≠ T → c ⬝ᵥ (fun σ ↦ compound G m σ τ) = 0 := by
  set N := Fintype.card (Set.powersetCard ι m) with hN
  have hΛ : ∀ τ, τ ≠ T → sprod lam τ ≤ ρ * sprod lam T := fun τ hτ ↦
    sprod_le_rho_mul lam hlam ρ hρ hρ1 T τ hT hτ
  have hΛpos : ∀ τ : Set.powersetCard ι m, 0 < sprod lam τ := fun τ ↦
    Finset.prod_pos fun j _ ↦ hlam j
  have hApos : ∀ σ : Set.powersetCard ι m, 0 < sprod a σ := fun σ ↦
    Finset.prod_pos fun j _ ↦ ha j
  have hΛT : ∀ τ : Set.powersetCard ι m, sprod lam τ ≤ sprod lam T := by
    intro τ
    by_cases hτ : τ = T
    · rw [hτ]
    · exact (hΛ τ hτ).trans (mul_le_of_le_one_left (hΛpos T).le hρ1)
  obtain ⟨f, hfmono, hftop⟩ := exists_sorted_equiv (sprod lam) T hΛT
  set GR : Matrix ι ι ℝ := G.map (Int.castRingHom ℝ) with hGR
  have hGRdet : GR.det ≠ 0 := by
    have h1 := (RingHom.map_det (Int.castRingHom ℝ) G).symm
    rw [RingHom.mapMatrix_apply] at h1
    rw [hGR, h1]
    simpa using hG
  set A : Matrix (Set.powersetCard ι m) (Set.powersetCard ι m) ℝ := compound (L * GR) m with hA
  have hLGR : ∀ i j, (L * GR) i j = eval L (fun l ↦ G l j) i := fun i j ↦ by
    simp [Matrix.mul_apply, eval_apply, hGR]
  have hAbound : ∀ σ τ, |A σ τ| ≤ m.factorial * (sprod a σ * sprod lam τ) := by
    intro σ τ
    have := abs_det_le ((L * GR).submatrix (ofFinEmbEquiv.symm σ) (ofFinEmbEquiv.symm τ))
      (fun i ↦ a (ofFinEmbEquiv.symm σ i)) (fun j ↦ lam (ofFinEmbEquiv.symm τ j))
      (fun i j ↦ by rw [Matrix.submatrix_apply, hLGR]; exact hLG _ _)
    rwa [prod_ofFinEmbEquiv_symm, prod_ofFinEmbEquiv_symm, Fintype.card_fin] at this
  have hAdet : A.det ≠ 0 := by
    rw [hA, compound_mul, Matrix.det_mul]
    exact mul_ne_zero (compound_det_ne_zero L hL m) (compound_det_ne_zero GR hGRdet m)
  set M : Matrix (Fin N) (Fin N) ℝ :=
    Matrix.of fun p q ↦ (sprod a (f p))⁻¹ * A (f p) (f q) with hM
  have hMdet : M.det ≠ 0 := by
    have h1 : M = (Matrix.of fun σ τ ↦ (sprod a σ)⁻¹ * A σ τ).submatrix f f := rfl
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_mul_column]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun σ _ ↦ inv_ne_zero (hApos σ).ne') hAdet
  set μ : Fin N → ℝ := fun q ↦ m.factorial * sprod lam (f q) with hμ
  have hμmono : Monotone μ := fun p q hpq ↦
    mul_le_mul_of_nonneg_left (hfmono hpq) (Nat.cast_nonneg _)
  have hMbound : ∀ p q, |M p q| ≤ μ q := by
    intro p q
    rw [hM, Matrix.of_apply, abs_mul, abs_inv, abs_of_pos (hApos _), inv_mul_le_iff₀ (hApos _)]
    calc |A (f p) (f q)| ≤ _ := hAbound _ _
      _ = _ := by ring
  obtain ⟨κ, U, hU1, hU0, hκ⟩ := exists_unipotent_mul_le M hMdet μ hμmono hMbound
  set U' : Matrix (Set.powersetCard ι m) (Set.powersetCard ι m) ℤ :=
    U.submatrix f.symm f.symm with hU'
  set V : Matrix (Set.powersetCard ι m) (Set.powersetCard ι m) ℤ := compound G m * U' with hV
  have hUdet : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (M := U) (fun i j hij ↦ hU0 i j hij)]
    simp [hU1]
  have hVdet : V.det ≠ 0 := by
    rw [hV, Matrix.det_mul, hU', Matrix.det_submatrix_equiv_self, hUdet, mul_one]
    intro h0
    apply compound_det_ne_zero GR hGRdet m
    rw [hGR, compound_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hkey : ∀ σ q, eval (compound L m) (fun σ' ↦ V σ' (f q)) σ =
      sprod a σ * (M * U.map (Int.cast : ℤ → ℝ)) (f.symm σ) q := by
    intro σ q
    have h1 : eval (compound L m) (fun σ' ↦ V σ' (f q)) σ =
        (compound L m * V.map (Int.castRingHom ℝ)) σ (f q) := by
      simp [eval_apply, Matrix.mul_apply]
    have h2 : V.map (Int.castRingHom ℝ) = compound GR m * U'.map (Int.castRingHom ℝ) := by
      rw [hV, Matrix.map_mul, hGR, compound_map]
    rw [h1, h2, ← Matrix.mul_assoc, ← compound_mul, ← hA, Matrix.mul_apply, Matrix.mul_apply,
      Finset.mul_sum, ← Equiv.sum_comp f]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp only [hU', hM, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.of_apply, Equiv.apply_symm_apply, Int.coe_castRingHom]
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (hApos σ).ne', one_mul]
  set B : Set.powersetCard ι m → ℝ := fun τ ↦ sprod lam τ * (if τ = T then ρ else 1) with hB
  set π : Set.powersetCard ι m ≃ Set.powersetCard ι m := f.symm.trans (κ.symm.trans f) with hπ
  set b : Set.powersetCard ι m → ℝ := fun σ ↦ C0 ι m * sprod a σ * B (π σ) with hb
  have hbox : ∀ τ, τ ≠ T → (fun σ' ↦ V σ' τ) ∈ box (compound L m) b := by
    intro τ hτ σ
    obtain ⟨q, rfl⟩ := f.surjective τ
    have hq : q < f.symm T :=
      lt_of_le_of_ne (hftop q) (fun h ↦ hτ (by rw [h, Equiv.apply_symm_apply]))
    set i := κ.symm (f.symm σ) with hi
    have hκi : f.symm σ = κ i := by rw [hi, Equiv.apply_symm_apply]
    have hπσ : π σ = f i := rfl
    have hAσ := hApos σ
    rw [hkey, abs_mul, abs_of_pos hAσ, hκi, hb]
    simp only [hπσ]
    have h1 := hκ i q
    have h2 : (2 : ℝ) ^ ((i : ℕ) + q + 2) ≤ 4 ^ N := by
      have h4 : (4 : ℝ) ^ N = 2 ^ (2 * N) := by
        rw [pow_mul]
        norm_num
      rw [h4]
      exact pow_le_pow_right₀ (by norm_num) (by have := i.2; have := q.2; omega)
    have h3 : sprod lam (f (min i q)) ≤ B (f i) := by
      simp only [hB]
      by_cases hfi : f i = T
      · have hiq : min i q = q :=
          min_eq_right (by rw [← hfi, Equiv.symm_apply_apply] at hq; exact hq.le)
        simp only [hiq, hfi, ↓reduceIte]
        rw [mul_comm]
        exact hΛ _ hτ
      · simp only [hfi, ↓reduceIte, mul_one]
        exact hfmono (min_le_left _ _)
    have hY : μ (min i q) = m.factorial * sprod lam (f (min i q)) := rfl
    have hW'pos := hΛpos (f (min i q))
    rw [hY] at h1
    generalize |(M * U.map (Int.cast : ℤ → ℝ)) (κ i) q| = X at h1 ⊢
    generalize (2 : ℝ) ^ ((i : ℕ) + (q : ℕ) + 2) = Z at h1 h2
    generalize B (f i) = W at h3 ⊢
    generalize sprod lam (f (min i q)) = W' at h3 h1 hW'pos
    generalize sprod a σ = Aσ at hAσ ⊢
    have hm0 : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    calc Aσ * X ≤ Aσ * (Z * (m.factorial * W')) := mul_le_mul_of_nonneg_left h1 hAσ.le
      _ ≤ Aσ * (4 ^ N * (m.factorial * W)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h2
            (mul_le_mul_of_nonneg_left h3 hm0.le) (by positivity) (by positivity)) hAσ.le
      _ = C0 ι m * Aσ * W := by
          rw [C0]
          ring
  refine ⟨b, fun σ ↦ ⟨π σ, rfl⟩, ?_, ?_, ?_⟩
  · have h1 : ∏ τ : Set.powersetCard ι m, B τ =
        (∏ τ : Set.powersetCard ι m, sprod lam τ) * ρ := by
      simp only [hB, Finset.prod_mul_distrib]
      rw [Finset.prod_ite_eq' Finset.univ T (fun _ ↦ ρ)]
      simp
    simp only [hb]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Equiv.prod_comp π B, h1]
    ring
  · have hli : LinearIndependent ℤ V.col := Matrix.linearIndependent_cols_of_det_ne_zero hVdet
    have hli' := hli.comp (Subtype.val : {τ // τ ≠ T} → _) Subtype.val_injective
    have h1 := card_le_setFinrank _ hli' _ (fun τ ↦ hbox τ.1 τ.2)
    have h2 : Fintype.card {τ : Set.powersetCard ι m // τ ≠ T} = N - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    omega
  · intro c _ hy τ hτ
    set w : Fin N → ℤ := fun q ↦ c ⬝ᵥ (fun σ ↦ compound G m σ (f q)) with hw
    have hsum : ∀ q, c ⬝ᵥ (fun σ' ↦ V σ' (f q)) = ∑ p, w p * U p q := by
      intro q
      simp only [hw, hV, hU', dotProduct, Matrix.mul_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm, ← Equiv.sum_comp f]
      refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun σ _ ↦ ?_
      simp [mul_assoc]
    have hw0 : ∀ k : ℕ, ∀ q : Fin N, (q : ℕ) = k → q < f.symm T → w q = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro q hqk hq
        have h1 := hy _ (hbox (f q) (fun h ↦ by
          rw [← h, Equiv.symm_apply_apply] at hq
          exact lt_irrefl _ hq))
        rw [hsum, Finset.sum_eq_single q] at h1
        · rwa [hU1, mul_one] at h1
        · intro p _ hpq
          rcases lt_or_gt_of_ne hpq with h | h
          · rw [ih p (by rw [← hqk]; exact h) p rfl (h.trans hq), zero_mul]
          · rw [hU0 p q h, mul_zero]
        · simp
    obtain ⟨q, rfl⟩ := f.surjective τ
    exact hw0 q q rfl (lt_of_le_of_ne (hftop q) (fun h ↦ hτ (by rw [h, Equiv.apply_symm_apply])))

/-- Every index lies in `(n - 1).choose (m - 1)` of the `m`-subsets. -/
lemma prod_sprod (x : ι → ℝ) (m : ℕ) (hm : 0 < m) :
    ∏ s : Set.powersetCard ι m, sprod x s =
      (∏ i, x i) ^ (Fintype.card ι - 1).choose (m - 1) := by
  classical
  have h1 : ∏ s : Set.powersetCard ι m, sprod x s =
      ∏ s ∈ Finset.powersetCard m (Finset.univ : Finset ι), ∏ i ∈ s, x i :=
    (Finset.prod_subtype (Finset.powersetCard m (Finset.univ : Finset ι))
      (p := (· ∈ Set.powersetCard ι m)) (by simp) (fun s ↦ ∏ i ∈ s, x i)).symm
  rw [h1]
  have h2 : ∀ s ∈ Finset.powersetCard m (Finset.univ : Finset ι),
      ∏ i ∈ s, x i = ∏ i, if i ∈ s then x i else 1 := fun s _ ↦ by
    simp [Finset.prod_ite_mem]
  rw [Finset.prod_congr rfl h2, Finset.prod_comm, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  have := Finset.card_filter_powersetCard_subset {i} (Finset.univ : Finset ι) m (by simp)
    (by rw [Finset.card_singleton]; exact hm)
  simpa [Finset.card_univ] using this

/-- If the integer points of `S` span a module of full rank, then `S` contains the columns of an
integer matrix with non-zero determinant. -/
lemma exists_det_ne_zero_of_finrank {κ : Type*} [Fintype κ] [DecidableEq κ] (S : Set (κ → ℤ))
    (h : Fintype.card κ ≤ Set.finrank ℤ S) :
    ∃ X : Matrix κ κ ℤ, X.det ≠ 0 ∧ ∀ j, (fun i ↦ X i j) ∈ S := by
  let castL : (κ → ℤ) →ₗ[ℤ] (κ → ℚ) := (Algebra.linearMap ℤ ℚ).compLeft κ
  have hcastL : ∀ x i, castL x i = (x i : ℚ) := fun x i ↦ by simp [castL]
  have hinj : Function.Injective castL := fun x y hxy ↦ by
    funext i
    have := congrFun hxy i
    rw [hcastL, hcastL] at this
    exact_mod_cast this
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank
    (R := ℤ) (M := Submodule.span ℤ S) h
  let F : Fin (Fintype.card κ) → κ → ℚ := fun i ↦ castL (f i).1
  have hF : LinearIndependent ℚ F := by
    have h1 : LinearIndependent ℤ (fun i ↦ (f i : κ → ℤ)) :=
      hf.map' (Submodule.subtype _) (Submodule.ker_subtype _)
    have h2 : LinearIndependent ℤ F := h1.map' castL (LinearMap.ker_eq_bot.mpr hinj)
    exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp h2
  have hFV : ∀ i, F i ∈ Submodule.span ℚ (castL '' S) := by
    intro i
    have h1 : Submodule.span ℤ S ≤
        ((Submodule.span ℚ (castL '' S)).restrictScalars ℤ).comap castL :=
      Submodule.span_le.mpr fun x hx ↦ Submodule.subset_span ⟨x, hx, rfl⟩
    exact h1 (f i).2
  have hVtop : Submodule.span ℚ (castL '' S) = ⊤ := by
    have h1 := hF.span_eq_top_of_card_eq_finrank' (by simp)
    refine top_le_iff.mp (h1 ▸ Submodule.span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    exact hFV i
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℚ (castL '' S)
  have hbtop : ⊤ ≤ Submodule.span ℚ (Set.range ((↑) : b → κ → ℚ)) := by
    rw [Subtype.range_coe, hbspan]
    exact hVtop.ge
  let bas := Module.Basis.mk hbli hbtop
  have : Finite b := Module.Finite.finite_basis bas
  have := Fintype.ofFinite b
  have hcard : Fintype.card κ = Fintype.card b := by
    rw [← Module.finrank_eq_card_basis bas, Module.finrank_fintype_fun_eq_card]
  let e : κ ≃ b := Fintype.equivOfCardEq hcard
  have hx : ∀ k, ∃ x ∈ S, castL x = (e k : κ → ℚ) := fun k ↦ hbS (e k).2
  choose x hxS hxe using hx
  refine ⟨Matrix.of fun i j ↦ x j i, ?_, fun j ↦ hxS j⟩
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hli2 : LinearIndependent ℚ (fun k ↦ castL (x k)) := by
    have h1 := hbli.comp e e.injective
    have h2 : (fun k ↦ castL (x k)) = ((↑) : b → κ → ℚ) ∘ e := funext fun k ↦ hxe k
    rw [h2]
    exact h1
  rw [Fintype.linearIndependent_iff] at hli2
  have h0 : ∑ k, (v k : ℚ) • castL (x k) = 0 := by
    funext i
    have h1 := congrArg (Int.cast : ℤ → ℚ) (congrFun hv i)
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, Int.cast_sum,
      Int.cast_mul, Int.cast_zero] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, hcastL, smul_eq_mul, Pi.zero_apply]
    rw [← h1]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  apply hv0
  funext k
  exact_mod_cast hli2 _ h0 k

/-- If `∏ b` is small with respect to `det M`, then the integer points of the parallelepiped
defined by `M` and `b` do not span a module of full rank. -/
lemma finrank_box_lt {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ ℝ) (b : κ → ℝ)
    (h : (Fintype.card κ).factorial * ∏ i, b i < |M.det|) :
    Set.finrank ℤ (box M b) < Fintype.card κ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨X, hX, hXS⟩ := exists_det_ne_zero_of_finrank (box M b) hlt
  have h1 := abs_det_le_of_eval_le M X hX b (fun _ ↦ 1)
    (fun i j ↦ by rw [mul_one]; exact hXS j i)
  simp only [Finset.prod_const_one, mul_one] at h1
  linarith

omit [Fintype ι] in
lemma sprod_le_pow {m : ℕ} (x : ι → ℝ) (B : ℝ) (hx : ∀ i, 0 ≤ x i) (h : ∀ i, x i ≤ B)
    (s : Set.powersetCard ι m) : sprod x s ≤ B ^ m := by
  have h1 : sprod x s ≤ ∏ _i ∈ (s : Finset ι), B :=
    Finset.prod_le_prod₀ (fun i _ ↦ hx i) (fun i _ ↦ h i)
  rwa [Finset.prod_const, Set.powersetCard.card_eq] at h1

omit [Fintype ι] in
lemma pow_le_sprod {m : ℕ} (x : ι → ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ i, B ≤ x i)
    (s : Set.powersetCard ι m) : B ^ m ≤ sprod x s := by
  have h1 : ∏ _i ∈ (s : Finset ι), B ≤ sprod x s :=
    Finset.prod_le_prod₀ (fun i _ ↦ hB) (fun i _ ↦ h i)
  rwa [Finset.prod_const, Set.powersetCard.card_eq] at h1

/-- Steps (3)–(5), for a fixed value of `m`. -/
lemma exists_compound_box_of_minimaData [LinearOrder ι] [Nontrivial ι] (L : Matrix ι ι ℝ)
    (hL : L.det ≠ 0) {ε : ℝ} (hε : 0 < ε) (C : ℝ) (hC : 1 ≤ C) (Q₁ : ℝ) (m : ℕ) :
    ∃ Q₀ : ℝ, ∀ (a lam : ι → ℝ) (G : Matrix ι ι ℤ) (T : Finset ι) (ρ : ℝ),
      MinimaData L ε C a lam G T ρ → T.card = m → (∀ i, 0 < a i) → Q₀ ≤ size a →
      ∃ b : Set.powersetCard ι m → ℝ,
        (∀ s, 0 < b s) ∧ ∏ s, b s < size b ^ (-(ε / (2 * (Fintype.card ι : ℝ) ^ 3))) ∧
        Q₁ ≤ size b ∧
        Set.finrank ℤ (box (compound L m) b) + 1 = (Fintype.card ι).choose m ∧
        ∀ c : Set.powersetCard ι m → ℤ, c ≠ 0 → (∀ y ∈ box (compound L m) b, c ⬝ᵥ y = 0) →
          ∀ x ∈ box L a, Phi m c ⬝ᵥ x = 0 := by
  set n := Fintype.card ι with hn
  have hn2 : 2 ≤ n := Fintype.one_lt_card
  set N := Fintype.card (Set.powersetCard ι m) with hN
  have hNchoose : N = n.choose m := by
    rw [hN, ← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card]
  set α : ℝ := ε / (n * ((n : ℝ) - 1)) with hα
  set d : ℝ := ε / (2 * (n : ℝ) ^ 3) with hd
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hαpos : 0 < α := by positivity
  have hdpos : 0 < d := by positivity
  have hγ : 0 < α - 2 * n * d := by
    have h1 : α - 2 * n * d = ε / ((n : ℝ) ^ 2 * ((n : ℝ) - 1)) := by
      rw [hα, hd]
      field_simp
      ring
    rw [h1]
    positivity
  set δ := |(compound L m).det| with hδdef
  have hδ : 0 < δ := abs_pos.mpr (compound_det_ne_zero L hL m)
  have hC0 : 1 ≤ C0 ι m := by
    have h1 : (1 : ℝ) ≤ 4 ^ Fintype.card (Set.powersetCard ι m) := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
    rw [C0]
    nlinarith
  have hC0pos : 0 < C0 ι m := by linarith
  have hCpos : 0 < C := by linarith
  set K₁ : ℝ := C0 ι m ^ N * C ^ ((n - 1).choose (m - 1)) * C with hK₁
  set K₂ : ℝ := C0 ι m * C ^ (n + 1) with hK₂
  have hK₁pos : 0 < K₁ := by positivity
  have hK₂pos : 0 < K₂ := by positivity
  obtain ⟨R1, hR1⟩ := exists_forall_lt_rpow (N.factorial * K₁ / δ) hαpos
  obtain ⟨R2, hR2⟩ := exists_forall_lt_rpow (K₁ * (max Q₁ 1) ^ N) hαpos
  obtain ⟨R3, hR3⟩ := exists_forall_lt_rpow (K₁ * K₂ ^ d) hγ
  refine ⟨max R1 (max R2 R3), ?_⟩
  intro a lam G T ρ hD hTm ha hQ0
  have hm : 0 < m := hTm ▸ hD.card_pos
  have hmn : m < n := hTm ▸ hD.card_lt
  have : Nonempty (Set.powersetCard ι m) := Set.powersetCard.nonempty_iff.mpr hmn.le
  set T' : Set.powersetCard ι m := ⟨T, hTm⟩ with hT'
  set Q := size a with hQdef
  have hQ1 : 1 ≤ Q := one_le_size ha
  have hQpos : 0 < Q := by linarith
  specialize hR1 Q ((le_max_left _ _).trans hQ0)
  specialize hR2 Q (((le_max_left _ _).trans (le_max_right _ _)).trans hQ0)
  specialize hR3 Q (((le_max_right _ _).trans (le_max_right _ _)).trans hQ0)
  obtain ⟨b, hbform, hbprod, hbrank, hbc⟩ := exists_box_of_minima L hL m a lam G T' ρ ha
    hD.lam_pos hD.det_ne hD.eval_le hD.rho_pos hD.rho_le_one hD.le_rho_mul
  have hρ := hD.rho_pos
  have hlam := hD.lam_pos
  set u := C * Q with hu
  have hupos : 0 < u := by positivity
  have hlam_ge : ∀ j, u⁻¹ ≤ lam j := fun j ↦ by
    rw [inv_le_iff_one_le_mul₀ hupos]
    linarith [hD.lam_ge j]
  have ha_le : ∀ i, a i ≤ Q := le_size a
  have ha_ge : ∀ i, Q⁻¹ ≤ a i := inv_size_le ha
  have hprodlam : ∏ j, lam j ≤ C * Q ^ n := by
    have h1 : (Q⁻¹) ^ n ≤ ∏ i, a i := by
      have := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ ↦ (inv_pos.mpr hQpos).le)
        (fun i _ ↦ ha_ge i)
      simpa [Finset.prod_const, Finset.card_univ] using this
    have h2 : 0 < ∏ j, lam j := Finset.prod_pos fun j _ ↦ hlam j
    have h3 : (∏ j, lam j) * (Q⁻¹) ^ n ≤ C :=
      (mul_le_mul_of_nonneg_left h1 h2.le).trans hD.prod_le
    calc ∏ j, lam j = (∏ j, lam j) * (Q⁻¹) ^ n * Q ^ n := by
          rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hQpos.ne', one_pow, mul_one]
      _ ≤ C * Q ^ n := mul_le_mul_of_nonneg_right h3 (by positivity)
  have h_sl_le : ∀ t : Set.powersetCard ι m, sprod lam t ≤ C * Q ^ n * u ^ (n - m) := by
    intro t
    have h1 := Finset.prod_mul_prod_compl (t : Finset ι) lam
    have h2 : (u⁻¹) ^ (n - m) ≤ ∏ j ∈ (t : Finset ι)ᶜ, lam j := by
      have := Finset.prod_le_prod₀ (s := (t : Finset ι)ᶜ) (fun i _ ↦ (inv_pos.mpr hupos).le)
        (fun i _ ↦ hlam_ge i)
      simpa [Finset.prod_const, Finset.card_compl, ← hn] using this
    have h3 : 0 < sprod lam t := Finset.prod_pos fun j _ ↦ hlam j
    have h4 : sprod lam t * (u⁻¹) ^ (n - m) ≤ C * Q ^ n :=
      ((mul_le_mul_of_nonneg_left h2 h3.le).trans_eq h1).trans hprodlam
    calc sprod lam t = sprod lam t * (u⁻¹) ^ (n - m) * u ^ (n - m) := by
          rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hupos.ne', one_pow, mul_one]
      _ ≤ C * Q ^ n * u ^ (n - m) := mul_le_mul_of_nonneg_right h4 (by positivity)
  have h_B_ge : ∀ t : Set.powersetCard ι m,
      (u⁻¹) ^ m ≤ sprod lam t * (if t = T' then ρ else 1) := by
    intro t
    split_ifs with ht
    · subst ht
      obtain ⟨j₁, hj₁, hj₁'⟩ := hD.rho_ge
      have h1 : sprod lam T' = lam j₁ * ∏ j ∈ T.erase j₁, lam j :=
        (Finset.mul_prod_erase T lam hj₁).symm
      have h2 : u⁻¹ ≤ ρ * lam j₁ := by
        rw [inv_le_iff_one_le_mul₀ hupos]
        linarith
      have h3 : (u⁻¹) ^ (m - 1) ≤ ∏ j ∈ T.erase j₁, lam j := by
        have := Finset.prod_le_prod₀ (s := T.erase j₁) (fun i _ ↦ (inv_pos.mpr hupos).le)
          (fun i _ ↦ hlam_ge i)
        simpa [Finset.prod_const, Finset.card_erase_of_mem hj₁, hTm] using this
      calc (u⁻¹) ^ m = u⁻¹ * (u⁻¹) ^ (m - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel hm]
        _ ≤ (ρ * lam j₁) * ∏ j ∈ T.erase j₁, lam j :=
            mul_le_mul h2 h3 (by positivity) (mul_pos hρ (hlam j₁)).le
        _ = _ := by rw [h1]; ring
    · rw [mul_one]
      exact pow_le_sprod lam _ (inv_pos.mpr hupos).le hlam_ge t
  have h_B_le : ∀ t : Set.powersetCard ι m,
      sprod lam t * (if t = T' then ρ else 1) ≤ C * Q ^ n * u ^ (n - m) := by
    intro t
    have h3 : 0 < sprod lam t := Finset.prod_pos fun j _ ↦ hlam j
    refine le_trans ?_ (h_sl_le t)
    split_ifs
    · exact mul_le_of_le_one_right h3.le hD.rho_le_one
    · rw [mul_one]
  have h_A_le : ∀ s : Set.powersetCard ι m, sprod a s ≤ Q ^ m :=
    sprod_le_pow a Q (fun i ↦ (ha i).le) ha_le
  have h_A_ge : ∀ s : Set.powersetCard ι m, (Q⁻¹) ^ m ≤ sprod a s :=
    pow_le_sprod a _ (inv_pos.mpr hQpos).le ha_ge
  have h_A_pos : ∀ s : Set.powersetCard ι m, 0 < sprod a s := fun s ↦
    Finset.prod_pos fun j _ ↦ ha j
  have hbpos : ∀ s, 0 < b s := by
    intro s
    obtain ⟨t, ht⟩ := hbform s
    rw [ht]
    have := (pow_pos (inv_pos.mpr hupos) m).trans_le (h_B_ge t)
    have := h_A_pos s
    positivity
  have hb_le : ∀ s, b s ≤ K₂ * Q ^ (2 * n) := by
    intro s
    obtain ⟨t, ht⟩ := hbform s
    rw [ht]
    have hB0 := (pow_pos (inv_pos.mpr hupos) m).le.trans (h_B_ge t)
    calc C0 ι m * sprod a s * (sprod lam t * if t = T' then ρ else 1)
        ≤ C0 ι m * Q ^ m * (C * Q ^ n * u ^ (n - m)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (h_A_le s) hC0pos.le) (h_B_le t) hB0
            (by positivity)
      _ = C0 ι m * C ^ (n - m + 1) * (Q ^ m * Q ^ n * Q ^ (n - m)) := by
          rw [hu, mul_pow, pow_succ]
          ring
      _ = C0 ι m * C ^ (n - m + 1) * Q ^ (2 * n) := by
          rw [← pow_add, ← pow_add]
          congr 2
          omega
      _ ≤ K₂ * Q ^ (2 * n) := by
          rw [hK₂]
          gcongr
          omega
  have hb_inv : ∀ s, (b s)⁻¹ ≤ K₂ * Q ^ (2 * n) := by
    intro s
    obtain ⟨t, ht⟩ := hbform s
    have h1 : (Q ^ m * u ^ m)⁻¹ ≤ b s := by
      rw [ht, mul_inv, ← inv_pow, ← inv_pow]
      calc (Q⁻¹) ^ m * (u⁻¹) ^ m = 1 * (Q⁻¹) ^ m * (u⁻¹) ^ m := by ring
        _ ≤ C0 ι m * sprod a s * (sprod lam t * if t = T' then ρ else 1) :=
          mul_le_mul (mul_le_mul hC0 (h_A_ge s) (by positivity) (by positivity)) (h_B_ge t)
            (by positivity) (by have := h_A_pos s; positivity)
    have h2 : (b s)⁻¹ ≤ Q ^ m * u ^ m := inv_le_of_inv_le₀ (by positivity) h1
    refine h2.trans ?_
    calc Q ^ m * u ^ m = 1 * C ^ m * Q ^ (2 * m) := by
          rw [hu, mul_pow, two_mul, pow_add]
          ring
      _ ≤ C0 ι m * C ^ (n + 1) * Q ^ (2 * n) := by
          gcongr
          omega
  have hsize_le : size b ≤ K₂ * Q ^ (2 * n) := size_le hb_le hb_inv
  have hsize1 : 1 ≤ size b := one_le_size hbpos
  have hsize_pos : 0 < size b := by linarith
  set A := Q ^ α with hA
  have hApos : 0 < A := Real.rpow_pos_of_pos hQpos α
  have hprod_pos : 0 < ∏ s, b s := Finset.prod_pos fun s _ ↦ hbpos s
  have hprod_le : ∏ s, b s ≤ K₁ * A⁻¹ := by
    rw [hbprod, prod_sprod a m hm, prod_sprod lam m hm, hK₁]
    have h1 : (∏ i, a i) ^ (n - 1).choose (m - 1) * (∏ i, lam i) ^ (n - 1).choose (m - 1) ≤
        C ^ (n - 1).choose (m - 1) := by
      rw [← mul_pow, mul_comm]
      refine pow_le_pow_left₀ ?_ hD.prod_le _
      have := Finset.prod_pos (s := Finset.univ) fun j _ ↦ hlam j
      have := Finset.prod_pos (s := Finset.univ) fun j _ ↦ ha j
      positivity
    have h2 : ρ ≤ C * A⁻¹ := by
      rw [hA, ← Real.rpow_neg hQpos.le]
      exact hD.rho_le
    calc C0 ι m ^ N * (∏ i, a i) ^ (n - 1).choose (m - 1) * (∏ i, lam i) ^ (n - 1).choose (m - 1) * ρ
        = C0 ι m ^ N * ((∏ i, a i) ^ (n - 1).choose (m - 1) *
            (∏ i, lam i) ^ (n - 1).choose (m - 1)) * ρ := by ring
      _ ≤ C0 ι m ^ N * C ^ (n - 1).choose (m - 1) * (C * A⁻¹) := by
          gcongr
      _ = _ := by ring
  have hprod_ge : 1 ≤ size b ^ N * ∏ s, b s := by
    have h1 : ∏ _s : Set.powersetCard ι m, (size b)⁻¹ ≤ ∏ s, b s :=
      Finset.prod_le_prod₀ (fun s _ ↦ (inv_pos.mpr hsize_pos).le) (fun s _ ↦ inv_size_le hbpos s)
    rw [Finset.prod_const, Finset.card_univ, ← hN] at h1
    calc (1 : ℝ) = size b ^ N * (size b)⁻¹ ^ N := by
          rw [← mul_pow, mul_inv_cancel₀ hsize_pos.ne', one_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  refine ⟨b, hbpos, ?_, ?_, ?_, ?_⟩
  · -- `∏ b < size b ^ (-d)`
    have hk : 0 < K₂ ^ d := Real.rpow_pos_of_pos hK₂pos d
    have hBq : 0 < Q ^ (-(2 * n * d)) := Real.rpow_pos_of_pos hQpos _
    have h1 : K₁ * K₂ ^ d < A * Q ^ (-(2 * n * d)) := by
      rw [hA, ← Real.rpow_add hQpos, ← sub_eq_add_neg]
      exact hR3
    have h2 : (K₂ * Q ^ (2 * n)) ^ (-d) = (K₂ ^ d)⁻¹ * Q ^ (-(2 * n * d)) := by
      rw [Real.mul_rpow hK₂pos.le (by positivity), Real.rpow_neg hK₂pos.le,
        ← Real.rpow_natCast, ← Real.rpow_mul hQpos.le]
      congr 2
      push_cast
      ring
    have h3 : (K₂ * Q ^ (2 * n)) ^ (-d) ≤ size b ^ (-d) :=
      Real.rpow_le_rpow_of_nonpos hsize_pos hsize_le (by linarith)
    calc ∏ s, b s ≤ K₁ * A⁻¹ := hprod_le
      _ = (K₁ * K₂ ^ d) * (A⁻¹ * (K₂ ^ d)⁻¹) := by field_simp
      _ < (A * Q ^ (-(2 * n * d))) * (A⁻¹ * (K₂ ^ d)⁻¹) :=
          mul_lt_mul_of_pos_right h1 (by positivity)
      _ = (K₂ ^ d)⁻¹ * Q ^ (-(2 * n * d)) := by field_simp
      _ = (K₂ * Q ^ (2 * n)) ^ (-d) := h2.symm
      _ ≤ size b ^ (-d) := h3
  · -- `Q₁ ≤ size b`
    refine (le_max_left Q₁ 1).trans ?_
    by_contra h
    push Not at h
    have h1 : size b ^ N ≤ max Q₁ 1 ^ N := pow_le_pow_left₀ hsize_pos.le h.le N
    have h2 : size b ^ N * ∏ s, b s ≤ max Q₁ 1 ^ N * (K₁ * A⁻¹) :=
      mul_le_mul h1 hprod_le hprod_pos.le (by positivity)
    have h3 : max Q₁ 1 ^ N * (K₁ * A⁻¹) < 1 := by
      have : max Q₁ 1 ^ N * (K₁ * A⁻¹) = (K₁ * max Q₁ 1 ^ N) / A := by
        field_simp
      rw [this, div_lt_one hApos]
      exact hR2
    linarith
  · -- the rank
    have h1 : (N.factorial : ℝ) * ∏ s, b s < δ := by
      have h2 : (N.factorial : ℝ) * K₁ < δ * A := by
        rwa [div_lt_iff₀' hδ] at hR1
      calc (N.factorial : ℝ) * ∏ s, b s ≤ N.factorial * (K₁ * A⁻¹) := by gcongr
        _ = (N.factorial * K₁) * A⁻¹ := by ring
        _ < (δ * A) * A⁻¹ := mul_lt_mul_of_pos_right h2 (inv_pos.mpr hApos)
        _ = δ := by field_simp
    have h2 := finrank_box_lt (compound L m) b h1
    omega
  · intro c hc hy x hx
    exact Phi_dotProduct_eq_zero m hm c hc G hD.det_ne T' (hbc c hc hy) x (hD.ker x hx)

/-- **Step 1** ([evertse1993], Proposition 3.3.2). Let `L₁, …, Lₙ` be linearly independent linear
forms with real coefficients and `ε > 0`. If `a₁ ⋯ aₙ < Q(a) ^ (-ε)`, `Q(a)` is large enough and
`Π(a)` contains a non-zero integer point, then there are `0 < m < n` and a tuple `b` of
`N = n.choose m` positive real numbers such that

* `∏ b < Q(b) ^ (-ε / (2 n³))` (and `Q(b)` is as large as we wish);
* the integer points of the parallelepiped `Π_m(b)` defined by the `m`-th compound of `L` span a
  module of rank `N - 1`;
* the hyperplane of `ℚ^N` spanned by the integer points of `Π_m(b)` determines a proper subspace
  of `ℚⁿ` containing the integer points of `Π(a)`: if `c` is a normal vector of this hyperplane,
  then all the integer points of `Π(a)` are orthogonal to `Φ m c`.

In [evertse1993] the integer points of `Π(a)` lie in a subspace `V` of dimension `k = n - m`
such that `f_k(V)` is the hyperplane spanned by the integer points of `Π_m(b)`, where `f_k` is
an injective map from the set of `k`-dimensional subspaces of `ℚⁿ` to the set of hyperplanes of
`ℚ^N`: the map `Φ m` sends a normal vector of the hyperplane `f_k(V)` to the normal vector of a
hyperplane of `ℚⁿ` containing `V`. -/
theorem exists_compound_box [LinearOrder ι] [Nontrivial ι] (L : Matrix ι ι ℝ) (hL : L.det ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Φ : (m : ℕ) → (Set.powersetCard ι m → ℤ) → (ι → ℤ), (∀ m c, Φ m c ≠ 0) ∧
      ∀ Q₁ : ℝ, ∃ Q₀ : ℝ, ∀ a : ι → ℝ, (∀ i, 0 < a i) → ∏ i, a i < size a ^ (-ε) → Q₀ ≤ size a →
        (∃ x ∈ box L a, x ≠ 0) →
        ∃ m : ℕ, 0 < m ∧ m < Fintype.card ι ∧ ∃ b : Set.powersetCard ι m → ℝ,
          (∀ s, 0 < b s) ∧ ∏ s, b s < size b ^ (-(ε / (2 * (Fintype.card ι : ℝ) ^ 3))) ∧
          Q₁ ≤ size b ∧
          Set.finrank ℤ (box (compound L m) b) + 1 = (Fintype.card ι).choose m ∧
          ∀ c : Set.powersetCard ι m → ℤ, c ≠ 0 → (∀ y ∈ box (compound L m) b, c ⬝ᵥ y = 0) →
            ∀ x ∈ box L a, Φ m c ⬝ᵥ x = 0 := by
  obtain ⟨C, hC, QA, hA⟩ := exists_minimaData L hL hε
  refine ⟨Phi, Phi_ne_zero, fun Q₁ ↦ ?_⟩
  choose QB hB using exists_compound_box_of_minimaData L hL hε C hC Q₁
  refine ⟨max QA (∑ m ∈ Finset.range (Fintype.card ι), |QB m|), fun a ha hprod hQ hx ↦ ?_⟩
  obtain ⟨lam, G, T, ρ, hD⟩ := hA a ha hprod ((le_max_left _ _).trans hQ) hx
  have hQB : QB T.card ≤ size a := by
    refine le_trans ((le_abs_self _).trans ?_) ((le_max_right _ _).trans hQ)
    exact Finset.single_le_sum (f := fun m ↦ |QB m|) (fun _ _ ↦ abs_nonneg _)
      (Finset.mem_range.mpr hD.card_lt)
  exact ⟨T.card, hD.card_pos, hD.card_lt, hB T.card a lam G T ρ hD rfl ha hQB⟩

end Schmidt

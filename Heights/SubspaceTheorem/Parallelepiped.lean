module

public import Heights.SubspaceTheorem.CompoundBox
public import Heights.SubspaceTheorem.PenultimateMinimum

/-!
# The Subspace Theorem for parallelepipeds

We deduce [evertse1993], Theorem 3.2.1 from Step 1 (`Schmidt.exists_compound_box`) and Step 2
(`Schmidt.parallelepiped_theorem_of_rank`) of its proof.
-/

@[expose] public section

open Matrix

namespace Schmidt

variable {ι : Type*} [Fintype ι]

/-- **The Subspace Theorem for parallelepipeds** ([evertse1993], Theorem 3.2.1). Let `L₁, …, Lₙ`
be linearly independent linear forms in `n ≥ 2` variables with real algebraic coefficients and let
`ε > 0`. There are finitely many hyperplanes `T₁, …, Tₜ` of `ℚⁿ` such that, for every tuple `a` of
positive real numbers with `a₁ ⋯ aₙ < Q(a) ^ (-ε)` and `Q(a)` large enough, the integer points of
the parallelepiped `Π(a) = {x : |Lᵢ(x)| ≤ aᵢ}` lie in one of `T₁, …, Tₜ`. -/
theorem parallelepiped_theorem [LinearOrder ι] [Nontrivial ι] (L : Matrix ι ι ℝ) (hL : L.det ≠ 0)
    (halg : ∀ i j, IsAlgebraic ℚ (L i j)) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (ι → ℤ), (∀ c ∈ T, c ≠ 0) ∧ ∃ Q₀ : ℝ, ∀ a : ι → ℝ, (∀ i, 0 < a i) →
      ∏ i, a i < size a ^ (-ε) → Q₀ ≤ size a → ∃ c ∈ T, ∀ x ∈ box L a, c ⬝ᵥ x = 0 := by
  classical
  have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hε' : 0 < ε / (2 * (Fintype.card ι : ℝ) ^ 3) := by positivity
  -- Step 1
  obtain ⟨Φ, hΦ, hS1⟩ := exists_compound_box L hL hε
  -- Step 2, applied to the compounds of `L`
  have hS2 (m : ℕ) := parallelepiped_theorem_of_rank (compound L m) (compound_det_ne_zero L hL m)
    (isAlgebraic_compound L halg m) hε'
  choose T hT Q hQ using hS2
  set Q₁ := ∑ m ∈ Finset.range (Fintype.card ι), |Q m| with hQ₁_def
  have hQ₁ : ∀ m < Fintype.card ι, Q m ≤ Q₁ := fun m hm ↦ (le_abs_self _).trans
    (Finset.single_le_sum (f := fun m ↦ |Q m|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.mpr hm))
  obtain ⟨Q₀, hQ₀⟩ := hS1 Q₁
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hc₀ : (Pi.single i₀ 1 : ι → ℤ) ≠ 0 := by simp
  refine ⟨insert (Pi.single i₀ 1) ((Finset.range (Fintype.card ι)).biUnion
    fun m ↦ (T m).image (Φ m)), ?_, Q₀, ?_⟩
  · intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hc₀
    · obtain ⟨m, -, hc⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨c', -, rfl⟩ := Finset.mem_image.mp hc
      exact hΦ m c'
  · intro a ha hprod hsize
    by_cases hbox : ∃ x ∈ box L a, x ≠ 0
    · obtain ⟨m, -, hmn, b, hb, hbprod, hbsize, hrank, hb'⟩ := hQ₀ a ha hprod hsize hbox
      have hcard : Fintype.card (Set.powersetCard ι m) = (Fintype.card ι).choose m := by
        simpa [Nat.card_eq_fintype_card] using Set.powersetCard.card ι m
      obtain ⟨c, hcT, hc⟩ := hQ m b hb hbprod ((hQ₁ m hmn).trans hbsize) (by rw [hrank, hcard])
      exact ⟨Φ m c, Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
        ⟨m, Finset.mem_range.mpr hmn, Finset.mem_image_of_mem _ hcT⟩), hb' c (hT m c hcT) hc⟩
    · push Not at hbox
      refine ⟨Pi.single i₀ 1, Finset.mem_insert_self _ _, fun x hx ↦ ?_⟩
      rw [hbox x hx, dotProduct_zero]

end Schmidt

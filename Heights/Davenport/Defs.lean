import Mathlib

/-!
# Davenport's lemma: definitions

We formalize the main theorem of

* H. Davenport, *On a principle of Lipschitz*, J. London Math. Soc. 26 (1951), 179–183.

Let `R` be a compact subset of `ℝⁿ` (here `ι → ℝ` for a finite type `ι`) such that

* (I) every line parallel to a coordinate axis meets `R` in at most `h` intervals;
* (II) the same holds for every projection of `R` onto a coordinate subspace.

Then `|N(R) - V(R)| ≤ ∑ m ∈ range n, h ^ (n - m) * V_m`, where `N(R)` is the number of points of
`R` with integer coordinates, `V(R)` is the volume of `R` and `V_m` is the sum of the
`m`-dimensional volumes of the projections of `R` onto the `m`-dimensional coordinate subspaces.

This file contains the definitions needed to state the theorem.

## Main definitions

* `Davenport.IsUnionOfIntervals h S`: the set `S : Set ℝ` is a union of at most `h` intervals.
* `Davenport.Conditions h R`: the conditions I and II of Davenport's paper.
* `Davenport.latticeCount R`: the number `N(R)` of points of `R` with integer coordinates.
* `Davenport.projVolume R m`: the sum `V_m` of the `m`-dimensional volumes of the projections of
  `R` onto the coordinate subspaces of dimension `m`.

## Implementation notes

The projection of `R : Set (ι → ℝ)` onto the coordinate subspace spanned by the coordinates in
`s : Finset ι` is modelled by `s.restrict '' R : Set (s → ℝ)`, so that its `#s`-dimensional
volume is simply its measure with respect to `volume` on `s → ℝ`.
-/

open MeasureTheory Set Function

namespace Davenport

/-- `IsUnionOfIntervals h S` means that the set `S` of real numbers is a union of at most `h`
intervals. Intervals are allowed to be of any kind (open, closed, degenerate, empty, ...) and are
not required to be disjoint. -/
def IsUnionOfIntervals (h : ℕ) (S : Set ℝ) : Prop :=
  ∃ I : Fin h → Set ℝ, (∀ k, (I k).OrdConnected) ∧ S = ⋃ k, I k

variable {ι : Type*} [Fintype ι]

/-- The conditions I and II of Davenport's paper for a subset `R` of `ι → ℝ` and a natural
number `h`. -/
structure Conditions [DecidableEq ι] (h : ℕ) (R : Set (ι → ℝ)) : Prop where
  /-- **Condition I**: any line parallel to one of the coordinate axes intersects `R` in a set
  which consists of at most `h` intervals. -/
  line : ∀ (i : ι) (x : ι → ℝ), IsUnionOfIntervals h {t : ℝ | update x i t ∈ R}
  /-- **Condition II**: the same is true for the projection of `R` on any of the coordinate
  subspaces obtained by equating a selection of the coordinates to zero. -/
  proj_line : ∀ s : Finset ι, s ≠ Finset.univ → ∀ (i : s) (x : s → ℝ),
    IsUnionOfIntervals h {t : ℝ | update x i t ∈ s.restrict '' R}

/-- The number `N(R)` of points with integer coordinates in `R` (it is `0` if there are
infinitely many such points). -/
noncomputable def latticeCount (R : Set (ι → ℝ)) : ℕ :=
  ((fun (z : ι → ℤ) (i : ι) ↦ (z i : ℝ)) ⁻¹' R).ncard

/-- The sum `V_m` of the `m`-dimensional volumes of the projections of `R` on the various
coordinate subspaces obtained by equating `n - m` coordinates to zero.

Note that for `m = 0` this is `1` if `R` is nonempty and `0` if `R` is empty. -/
noncomputable def projVolume (R : Set (ι → ℝ)) (m : ℕ) : ℝ :=
  ∑ s ∈ Finset.powersetCard m Finset.univ, volume.real (s.restrict '' R)

end Davenport

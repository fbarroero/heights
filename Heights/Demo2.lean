import Mathlib

--Demo: if x and y are integers such that y^2 = x^3 + 1 and x is odd, then (x,y) =(-1,0).

open Int



example (x y : ℤ) (h : y ^ 2 = x ^ 3 + 1) (hx : ¬ 2 ∣ x) : (x, y) = (-1, 0) := by
  -- first we have (y + 1) * (y - 1) = x ^ 3
  have h' : (y + 1) * (y - 1) = x ^ 3 := by grind
  have h_coprime : Int.gcd (y + 1) (y - 1) = 1 := by
    have : Int.gcd (y + 1) (y - 1) ∣ 2 := by
      zify
      calc
      (Int.gcd (y + 1) (y - 1) : ℤ) ∣ (y + 1) - (y - 1) := by
        apply dvd_sub <| Int.gcd_dvd_left (y + 1) (y - 1)
        exact Int.gcd_dvd_right (y + 1) (y - 1)
      _ = 2 := by simp
    apply Nat.le_of_dvd (by omega) at this
    by_contra h_gcd
    have : Int.gcd (y + 1) (y - 1) ≠ 0 := by
      simp
      grind
    have : Int.gcd (y + 1) (y - 1) = 2 := by omega
    have hh : 2 ∣ x ^ 3 := by
      rw [← h']
      refine Int.dvd_mul_of_dvd_right ?_
      zify at this
      rw [← this]
      exact Int.gcd_dvd_right (y + 1) (y - 1)
    apply hx
    have : Nat.Prime 2 := Nat.prime_two
    apply Int.Prime.dvd_pow' this hh
  have : IsCoprime (y + 1) (y - 1) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact h_coprime
  obtain ⟨w, hw⟩ := exists_associated_pow_of_mul_eq_pow' this h'
  rw [mul_comm] at h'
  obtain ⟨z, hz⟩ := exists_associated_pow_of_mul_eq_pow' this.symm h'
  have (a b : ℤ) (h : Associated (a ^ 3) b) : ∃ c, b = c ^ 3 := by
    rw [associated_iff] at h
    simp_all only [two_dvd_ne_zero]
    cases h with
    | inl h_2 =>
      subst h_2
      use a
    | inr h_3 =>
      use -a
      grind
  apply this at hw
  apply this at hz
  obtain ⟨w', hw'⟩ := hw
  obtain ⟨z', hz'⟩ := hz
  have h_2 : 2 = (w' ^ 3) - (z' ^ 3) := by
    rw [← hw', ← hz']
    grind
  have : w' ^ 3 - z' ^ 3 = (w' - z') * (w' ^ 2 + w' * z' + z' ^ 2) := by
    ring
  have h_ineq : z' < w' := by
    contrapose! h_2
    have : w' ^3 ≤ z' ^3 := by
      refine (Odd.pow_le_pow ?_).mpr h_2
      exact Nat.odd_iff.mpr rfl
    omega

  rw [this] at h_2





  /-
  have (a b : ℤ) : Associated (a ^ 3) b ↔ natAbs b = natAbs a ^ 3 := by
    rw [associated_iff_natAbs, natAbs_pow a 3]
    exact eq_comm
  rw [this] at hw hz   -/
  sorry

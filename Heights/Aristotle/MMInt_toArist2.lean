
import Mathlib

lemma aaa' {α : Type u_1} {β : Type u_2} [CommMonoid α] [CommMonoidWithZero β] [PartialOrder β] [PosMulMono β]
    (f : α → β) (h1 : ∀ (a : α), 1 ≤ f a) (s : Multiset α) (a : α) (ha : a ∈ s) :
    f a ≤ (Multiset.map f s).prod := by
  sorry

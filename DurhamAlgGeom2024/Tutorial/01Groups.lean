import Mathlib

-- let G be a group
variable {G : Type} [Group G]

-- If a^2=1 for all a ∈ G then G is abelian
example (h : ∀ a : G, a * a = 1) : ∀ x y : G, x * y = y * x := by
  sorry

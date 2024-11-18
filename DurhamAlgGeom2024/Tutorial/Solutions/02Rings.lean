import Mathlib

open Function

-- a finite integral domain is a field
theorem bar (R : Type) [CommRing R] [IsDomain R] [Finite R] : IsField R := by
  -- let's see what we actually have to prove here
  constructor
  -- First we've got to prove R has more than one element
  -- so let's prove 0 ≠ 1
  · use 0
    use 1
    -- This works because R is a domain and this is one of the axioms.
    exact zero_ne_one
  -- Next we've got to prove that R is commutative
  · intro x y
    -- This works because R is a commutative ring :-)
    rw [mul_comm]
  -- Finally we've got to prove that every nonzero elment has an inverse.
  -- This is where the work is.
    -- Let a be an arbitrary nonzero element of R
  · intro a ha
    -- Define φ to be the function sending x to a * x
    set φ : R → R := fun x ↦ a * x with hφ
    -- It's straightforward to show that this is injective
    have hi : Injective φ := by
      intro s t hst
      rw [hφ] at hst
      dsimp at hst
      apply sub_eq_zero_of_eq at hst
      rw [← mul_sub] at hst
      replace hst := eq_zero_of_ne_zero_of_mul_left_eq_zero ha hst
      exact eq_of_sub_eq_zero hst
    -- So it's also surjective
    have hs : Surjective φ := by exact Finite.surjective_of_injective hi
    -- and so a times something must be 1
    apply hs

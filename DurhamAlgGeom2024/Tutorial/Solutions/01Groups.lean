import Mathlib

-- let G be a group
variable {G : Type} [Group G]

-- first let's prove the lemma that if a*a = 1 then a = a⁻¹
lemma eq_inv {a : G} (ha : a * a = 1) : a⁻¹ = a := by
  -- multiply both sides of hypothesis by a⁻¹ on the left
  apply_fun (fun x ↦ a⁻¹ * x) at ha
  -- now use group axioms in a sensible way
  rw [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at ha
  -- and we're done
  exact ha.symm

-- If a*a=1 for all a ∈ G then G is abelian
example (h : ∀ a : G, a * a = 1) : ∀ x y : G, x * y = y * x := by
  -- let x and y be arbitrary
  intro x y
  -- use the fact that xy=(xy)⁻¹
  rw [← eq_inv (h (x * y))]
  -- use (xy)⁻²=y⁻¹x⁻¹
  rw [mul_inv_rev] -- found with `simp?`
  -- use x⁻¹ = x and y⁻¹ = y
  rw [eq_inv (h x), eq_inv (h y)]

-- Solution given in the lecture
example (h : ∀ a : G, a * a = 1) :
    ∀ x y : G, x * y = y * x := by
  -- let x and y be arbitrary
  intro x y
  -- xy=1xy1=yyxyxx=y(yx)(yx)x
  calc x * y = 1 * x * y * 1 := by group
       _     = (y * y) * (x * y) * (x * x) := by
               rw [h x, h y]
               repeat rw [mul_assoc]
       _     = y * ((y * x) * (y * x)) * x := by simp [mul_assoc]
       _     = y * 1 * x := by rw [h (y * x)]
       _     = y * x := by simp only [mul_one]

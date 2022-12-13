import data.set
import data.int.basic
open function int set

section
  def f (x : ℤ) : ℤ := x + 3
  def g (x : ℤ) : ℤ := -x
  def h (x : ℤ) : ℤ := 2 * x + 3

  -- 1
  example : injective h := 
  assume x1 x2, 
  assume h1, 
  have h2: 2 ≠ (0 : ℤ), from dec_trivial, 
  show x1 = x2, from mul_left_cancel₀ h2 (add_right_cancel h1)

  -- 2
  example : surjective g :=
  assume y,
  have h1 : g (-y) = y, from calc
     g (-y) = -(-y) : rfl
        ...  = y : by rw neg_neg,
  show ∃ x, g x = y, from exists.intro (-y) h1  

  -- 3
  example (A B : Type) (u : A → B) (v1 : B → A) (v2 : B → A)
    (h1 : left_inverse v1 u) (h2 : right_inverse v2 u) : v1 = v2 :=
  funext
   (assume x,
      calc
        v1 x = v1 (u (v2 x)) : by rw h2
         ... = v2 x          : by rw h1)
end

-- 4
section
  variables {X Y : Type}
  variable f : X → Y
  variables A B : set X

  example : f '' (A ∩ B) ⊆ f '' A ∩ f '' B :=
  assume y,
  assume h1 : y ∈ f '' (A ∩ B),
  exists.elim h1 $
  assume x h,
  have h2 : x ∈ (A ∩ B), from h.left,
  have h3 : f x = y, from h.right,
  have h4 : x ∈ A, from and.left h2,
  have h5 : x ∈ B, from and.right h2, 
  have h6 : y ∈ f '' A, from ⟨x, h4, h3⟩,
  have h7 : y ∈ f '' B, from ⟨x, h5, h3⟩,
  show y ∈ f '' A ∩ f '' B, from and.intro (h6)(h7)

end
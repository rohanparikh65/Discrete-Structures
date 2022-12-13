variables A B C D : Prop

example : A ∧ (A → B) → B :=
assume h : A ∧ (A → B),
(and.right h) (and.left h)


example : A → ¬(¬A ∧ B) :=
assume h : A,
assume h2 : ¬A ∧ B,
show false, from (and.left h2) h



example : ¬(A ∧ B) → (A → ¬B) :=
assume h : ¬(A ∧ B),
assume h1 : A,
assume h2 : B, h (and.intro h1 h2)


example (h₁ : A ∨ B) (h₂ : A → C) (h₃ : B → D) : C ∨ D :=
  or.elim h₁
    (assume h1 : A,
      show C ∨ D, from or.inl (h₂ h1))
    (assume h1 : B,
      show C ∨ D, from or.inr (h₃ h1))


example (h : ¬A ∧ ¬B) : ¬(A ∨ B) :=
(assume h1 : (A ∨ B), show false, from or.elim h1
                (assume h2 : A, false.elim (h.left h2) )
                (assume h3 : B, false.elim (h.right h3) ))


example : ¬(A ↔ ¬A) :=
assume h : A ↔ ¬A,
have h1 : ¬A, from
    (show A → false, from
        assume h2 : A,
        false.elim ( (h.mp h2) h2)), 
false.elim (h1 (h.mpr h1)) 




axioms
  (Person: Type)
  (Likes : Person → Person → Prop)
  
example : 
  ¬ (∀ p : Person, Likes p p) ↔ 
  ∃ p : Person, ¬ Likes p p :=
  begin
    apply iff.intro _ _,
    assume h,
    have f := classical.em (∃ p : Person, ¬ Likes p p),
    cases f,
    apply f,
    have contra : ∀ (p : Person), Likes p p := _,
    contradiction,
    assume p,
    have g := classical.em (Likes p p),
    cases g,
    assumption,
    have a : ∃ (p : Person), ¬ Likes p p := exists.intro p g,
    contradiction,

  end

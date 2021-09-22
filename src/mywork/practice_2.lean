/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := _    -- trick question? why?
/- Cannot prove false, instead prove not true-/

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P, 
  apply iff.intro _ _,
  -- forward
    assume porp,
    apply or.elim porp,
    -- left disjunct is true
      assume p,
      exact p,
    -- right disjunct is true
      assume p,
      exact p,
  -- backwards
    assume p,
    exact or.intro_left P p,
end

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume p,
  apply and.elim_left p,
  assume h,
  apply and.intro h h,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forwards
  assume porq,
  apply or.elim porq _ _,
  assume p,
  apply or.intro_right _ _,
  apply p,
  assume q,
  apply or.intro_left,
  apply q,
  --backwards
  assume qorp,
  apply or.elim qorp _ _,
  assume q,
  apply or.intro_right _ _,
  apply q,
  assume p,
  apply or.intro_left _ _,
  apply p,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forwards
  assume pandq,
  apply and.intro _ _,
  apply and.elim_right pandq,
  apply and.elim_left pandq,
  --backwards
  assume qandp,
  apply and.intro _ _,
  apply and.elim_right qandp,
  apply and.elim_left qandp,
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro,
  --forwards
  assume pandqorr,
  apply and.elim pandqorr,
  assume p,
  assume qorr,
  apply or.elim qorr _ _,
  assume q,
  apply or.intro_left _ _,
  apply and.intro p q,
  assume r,
  apply or.intro_right _ _,
  apply and.intro p r,
  --backwards
  assume pandqorpandr,
  apply or.elim pandqorpandr,
  --left
  assume pandq,
  apply and.intro _ _,
  apply and.elim_left pandq,
  apply or.intro_left _ _,
  apply and.elim_right pandq,
  --right
  assume pandr,
  apply and.intro _ _,
  apply and.elim_left pandr,
  apply or.intro_right _ _,
  apply and.elim_right pandr,
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  --forwards
  assume porqandr,
  apply or.elim porqandr,
  assume p,
  apply and.intro _ _,
  apply or.intro_left _ _,
  apply p,
  apply or.intro_left,
  apply p,
  assume qandr,
  apply and.intro _ _,
  apply or.intro_right _ _,
  apply and.elim_left qandr,
  apply or.intro_right _ _,
  apply and.elim_right qandr,
  --backwards
  assume porqandporr,
  apply and.elim porqandporr, 
  assume porq,
  assume porr,
  apply or.elim porq,
  assume p,
  apply or.intro_left _ _,
  apply p,
  assume q,
  apply or.elim porr,
  assume p,
  apply or.intro_left _ _,
  apply p,
  assume r,
  apply or.intro_right _ _,
  apply and.intro q r,
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forwards
  assume pandporq,
  apply and.elim_left pandporq, 
  --backwards
  assume p,
  apply and.intro _ _,
  apply p,
  apply or.intro_left _ _,
  apply p,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forwards
  assume porpandq,
  apply or.elim porpandq,
  assume p,
  apply p,
  assume pandq,
  apply and.elim_left pandq,
  --backwards
  assume p,
  apply or.intro_left _ _,
  apply p,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
  --forwards
  assume portrue,
  apply or.elim portrue,
  assume p,
  exact true.intro,
  assume t,
  apply t,
  --backwards
  assume t,
  apply or.intro_right _ _,
  apply t,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forwards
  assume porfalse,
  apply or.elim porfalse,
  assume p,
  apply p,
  assume f,
  cases f,
  --backwards
  assume p,
  apply or.intro_left _ _,
  apply p,
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forwards 
  assume pandtrue,
  apply and.elim_left pandtrue,
  --backwards,
  assume p,
  apply and.intro _ _,
  apply p,
  exact true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  --forwards
  assume pandfalse,
  apply and.elim_right pandfalse,
  --backwards
  assume f,
  apply and.intro _ _,
  cases f,
  apply f,
end



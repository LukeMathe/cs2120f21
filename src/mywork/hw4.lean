/-Luke Mathe, lkm6eka-/
-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro _ _,
  --forwards
  assume h,
  have pornp := classical.em P,
  have qornq := classical.em Q,
  cases pornp,
  cases qornq,
  apply or.intro_left,
  assume p,
  apply h,
  apply and.intro _ _,
  apply p,
  apply qornq,
  apply or.intro_right,
  apply qornq,
  apply or.intro_left,
  apply pornp,
  --backwards
  assume npornq,
  apply not.intro,
  assume pandq,
  apply or.elim npornq,
  assume np,
  apply np,
  cases pandq with p q,
  apply p,
  assume nq,
  apply nq,
  cases pandq with p q,
  apply q,
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume notporq,
  apply and.intro _ _,
  assume p,
  apply notporq,
  apply or.intro_left,
  apply p,
  assume q,
  apply notporq,
  apply or.intro_right,
  apply q,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forwards
  assume pornpandq,
  have pornp := classical.em P,
  cases pornp with p np,
  apply or.intro_left,
  apply p,
  apply or.intro_right,
  apply or.elim pornpandq,
  assume p,
  contradiction,
  assume notpandq,
  apply and.elim_right notpandq,
  --backwards
  assume porq,
  have pornp := classical.em P,
  cases pornp,
  cases porq,
  apply or.intro_left,
  apply pornp,
  apply or.intro_left,
  apply pornp,
  apply or.elim porq,
  assume p,
  contradiction,
  assume q,
  apply or.intro_right,
  apply and.intro pornp q,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
  --forwards
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
  -- backwards
  assume porqandr,
  apply and.intro _ _,
  apply or.elim porqandr,
  assume p,
  apply or.intro_left,
  apply p,
  assume qandr,
  apply or.intro_right,
  apply and.elim_left qandr,
  apply or.elim porqandr,
  assume p,
  apply or.intro_left,
  apply p,
  assume qandr,
  apply or.intro_right,
  apply and.elim_right qandr,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro _ _,
  --forwards
  assume porqandrors,
  have porq := and.left porqandrors,
  have rors := and.right porqandrors,
  cases porq,
  cases rors,
  apply or.intro_left,
  apply and.intro,
  apply porq,
  apply rors,
  apply or.intro_right,
  apply or.intro_left,
  apply and.intro _ _,
  apply porq,
  apply rors,
  apply or.elim rors,
  assume r,
  apply or.intro_right,
  apply or.intro_right,
  apply or.intro_left,
  apply and.intro _ _,
  apply porq,
  apply r,
  assume s,
  apply or.intro_right, 
  apply or.intro_right,
  apply or.intro_right,
  apply and.intro _ _,
  apply porq,
  apply s,
  --backwards
  assume h,
  cases h,
  apply and.intro _ _,
  apply or.intro_left,
  apply and.elim_left h,
  apply or.intro_left,
  apply and.elim_right h,
  apply and.intro _ _,
  cases h,
  apply or.intro_left,
  apply and.elim_left h,
  apply or.intro_right,
  apply or.elim h,
  assume qandr,
  apply and.elim_left qandr,
  assume qands,
  apply and.elim_left qands,
  cases h,
  apply or.intro_right,
  apply and.elim_right h,
  apply or.elim h,
  assume qandr,
  apply or.intro_left,
  apply and.elim_right qandr,
  assume qands,
  apply or.intro_right,
  apply and.elim_right qands,


end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ¬ ∀( n : ℕ ), n = 0 :=
begin
  assume h,
  have f := h 1,
  contradiction,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro _ _,
  --forwards
  have pornp := classical.em P,
  apply or.elim pornp,
  assume p,
  assume pimpq,
  apply or.intro_right,
  apply pimpq,
  apply p,
  assume np,
  assume pimpq,
  apply or.intro_left,
  apply np,
  --backwards
  assume nporq,
  assume p,
  cases nporq,
  contradiction,
  apply nporq,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume pimpq,
  have pimpqornpimpq := classical.em (P → Q),
  cases pimpqornpimpq,
  assume nq,
  apply not.intro,
  assume p,
  apply nq,
  apply pimpq,
  apply p,
  assume nq,
  apply not.intro,
  assume p,
  apply nq,
  apply pimpq,
  apply p,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume npimpnq,
  have pornp := classical.em P,
  have qornq := classical.em Q,
  cases pornp,
  cases qornq,
  assume q,
  apply pornp,
  assume q,
  apply pornp,
  assume q,
  have nq := npimpnq pornp,
  contradiction,
end

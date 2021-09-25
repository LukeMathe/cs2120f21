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
/-Suppose P is a proposition, and we have a proof 
that the hyposthesis P ∨ P is true. Using the 
elimination rule for or, we can conclude that P is true, 
and thus that P implies P. We do this again for the right side of the
or statement. Using the introduction rule for if 
and only if, we have proved the statement going forwards.
Now we need to prove the statement going backwards. Here we
assume the hypothesis of P is true, and thus, using the 
introduction rule for or from the left side, we apply this
hypothesis, and prove that P ∨ P is also true. -/

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume p,
  apply and.elim_left p,
  assume h,
  apply and.intro h h,
end
/-Suppose P is a proposition, and we have a proof 
of the hypothesis that P ∧ P is true. Using the left 
and elimination rule, applied to this proof, we find 
P is true. Using the introduction rule for if and only
if, we have proved that P ∧ P implies P. Now we need
to prove that P implies P ∧ P. Now we assume we have a 
proof that the hypothesis of P is true. Using the 
and introduction rule, we apply this proof twice, and
thus have proved that P implies P ∧ P.
-/
example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forwards
  assume porq,
  apply or.elim porq _ _,
  assume p,
  apply or.intro_right,
  apply p,
  assume q,
  apply or.intro_left,
  apply q,
  --backwards
  assume qorp,
  apply or.elim qorp _ _,
  assume q,
  apply or.intro_right,
  apply q,
  assume p,
  apply or.intro_left,
  apply p,
end
/- Suppose that P and Q are propositions, and that we
have a proof that P ∨ Q is true. We wand to prove that
P ∨ Q implies Q ∨ P, and that Q ∨ P implies P ∨ Q. To
prove this going forwards, we apply the or elimination rule
to the proof of P ∨ Q, and then assume this is a proof of P
we apply this proof of P using the right or introduction rule.
Then we assume we have a proof of Q, also from the or
elimination rule. We apply the proof of Q to the left
or introduction rule, and thus have proved P ∨ Q implies
Q ∨ P. To prove it backwards, we assume we have a proof that
Q ∨ P is true. We apply the or elimination rule to this 
proof, and assume this is a proof of Q. We apply the proof
of Q using the right or introduction rule. Then we assume we have
a proof of P, also from the or elimination rule, and apply
this proof using the left or introduction rule, and thus have
proved Q ∨ P implies P ∨ Q. We apply the if and only if
introduction rule to the two forwards and backwards proofs.
-/

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
/- Suppose we have propositions P and Q, and that we
want to prove P ∧ Q implies Q ∧ P, and vice versa. 
We assume we have a proof that P ∧ Q is true, and 
apply the right and elimination rule to this proof, 
and then the left and elimination rule to this proof.
We then apply the and introduction rule to these two
applied and elimination rules, and this proves Q ∧ P
from P ∧ Q. Now to prove P ∧ Q from Q ∧ P, we assume 
we have a proof of Q ∧ P, and then apply the right
and elimination rule to this proof, and then apply the
left and elimination rule to this proof. Then we apply the
and introduction rule to these two applied and elimination rules,
and this proves P ∧ Q from Q ∧ P. Then we apply the if 
and only if introduction rule to the forward and backwards proofs.
-/
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
/- Suppose we have propositions P Q and R.  We want
 to prove (P ∧ Q) ∨ (P ∧ R) from P ∧ (Q ∨ R) and 
 vice versa. Then we assume we have a proof of 
 P ∧ (Q ∨ R). Using the and elimination rule, we can break
 this down into two separate proofs, one of P, and one
 of Q ∨ R. We apply the or elimination rule to Q ∨ R,
 aand assume a proof of Q. Then we apply the and introduction
 rule to the proofs of P and Q, and apply the left
 or introduction rule to this. Then we assume a proof of
 R from the or elimination rule of Q ∨ R, and then 
 apply the and introduction rule to the proofs of P and Q. 
 Then we apply the right or introduction rule to this, and we
 have proved it forwards. To prove it backwards, we
 assume we have a proof of (P ∧ Q) ∨ (P ∧ R). We apply
 the or elimination rule to this proof, and get proofs
 of (P ∧ Q) and (P ∧ R). Using the proof of (P ∧ Q), 
 we apply the left and elimination rule, to get a proof of P.
 Then we apply the right and elimination rule to (P ∧ Q)
 to get a proof of Q. Then we apply the left or introduction rule to
to the proof of Q, and the and introduction rule to this,
and the proof of P to prove P ∧ ( Q ∨ R). We have to 
prove P ∧ ( Q ∨ R) from P ∧ R now. We apply the left and elim
rule, achieving a proof of P. The right and elim
rule yields a proof of R. We apply the right or intro rule
to the proof of R to prove Q ∨ R, and then apply the and
intro rule to P and this proof to prove P ∧ ( Q ∨ R). 
Then we apply the if and only if intro rule to the 
forwards and backwards proofs. 
 -/
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
/- Suppose we have propositions P and Q and R. We want to
prove (P ∨ Q) ∧ (P ∨ R) from P ∨ (Q ∧ R), and vice versa.
We assume a proof of P ∨ (Q ∧ R). We apply the or elim rule,
and assume a proof of P and a proof of (Q ∧ R) from this.
We apply the left or introduction rule to the proof of P,
to get a proof of (P ∨ Q). We apply the left or intro rule
to the proof of P again to get a proof of (P ∨ R), and then
apply the and introduction rule to these two proofs.Then,
we use the proof of ( Q ∧ R) to to get a proof of Q and a 
proof of R, using the left and elim rule, and the right and
elim rule respectively. We use the right or introduction rule
on each of these proofs to get a proof of (P ∨ Q), and a
proof of (P ∨ R), and then apply the and intro rule to these
proofs. This concludes the forwards proof. To prove it backwards
we assume a proof of (P ∨ Q) ∧ (P ∨ R) , apply the and elim
rule to get proofs of (P ∨ Q) and of (P ∨ R) respectively. 
We apply the or elim rule to (P ∨ Q) to get a proof of P
and a proof of Q. We apply the left or introduction to the
proof of P to prove P ∨ (Q ∧ R). We apply the or elim rule to 
the proof of (P ∨ R), to get proofs of P and R. We apply the
left or intro rule to the proof of P to prove P ∨ (Q ∧ R). 
Then we apply the and intro rule to the proofs of Q and R, and 
apply the right or intro rule to this. This completes the
backwards proof, and then we apply the if and only if intro
rule to these proofs. 
-/
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
/- Suppose we have propositions P and Q. We want to prove
P from P ∧ (P ∨ Q) and vice versa. We assume a proof of P ∧ (P ∨ Q), then apply the
left and elim rule to this proof to geta proof of P. 
This completes the forwards proof. To prove it backwards
we assume a proof of P, apply the left or introduction rule
to this proof to prove P ∨ Q, and then apply the and intro
rule to the proof of P and this proof to prove P ∧ (P ∨ Q). 
Then apply the if and only if intro rule to these proofs. 
-/
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
/-Suppose we have propositions P and Q. We want to prove
P ∨ (P ∧ Q) implies P and vice versa. We assume P ∨ (P ∧ Q),
then apply or elimination to this to get a proof of P,
and a proof of (P ∧ Q). We apply the proof of P to prove P,
then apply the left and elim rule to (P ∧ Q) to prove P
from both sides of the or. To prove this backwards, we 
assume a proof of P, then apply the left or intro rule, which
proves P ∨ (P ∧ Q). Then we apply the if and only if intro rule
to these proofs. 
-/
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
/- Suppose P is a propositon, and we want to prove P ∨ true
implies true, and vice versa. We asume a proof of P ∨ true,
apply or.elim to this proof, and get proofs of P and true
respectively. We exact the true introduction rule on P, which
proves true, and then apply the true proof, so true is proved by both sides of the or. 
To prove it backwards, we assume a proof of true, apply the right
or intro rule to this proof, and we have then proved true implies
P ∨ true. Then we apply the if and only if intro rule to these
two proofs. 
-/
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
/- Suppose we have a propositon P , and want to prove
P ∨ false implies P, and vice versa. We assume a proof
of P ∨ false, and apply the or elim rule to this proof to 
get a proof of P and a proof of false. We apply P, and then
do case analysis on the false proof to prove P from
a case of false. To prove it backwards, we assume a proof 
of P, and apply it using the left or introduction rule to
prove P ∨ false. Then we apply the if and only if
introduction rule to these two proofs. 
-/
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
/- Suppose we have a proposition P, for which we are trying
to prove P ∧ true implies P, and vice versa. First,
we assume a proof of P ∧ true, and then apply the left
and elim rule to this proof to prove P. To prove this 
backwards, we assume a proof of P, then apply the and 
intro rule to the proof of p and the applied true intro
ruel, proving P ∧ true. Then we apply the if and only if
intro rule to these two proofs. 
-/
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
/- Suppose we have aproposition P, for which we are trying
to prove P ∧ false implies false, and vice versa. We
assume a proof of P ∧ false, and apply the right and elim
rule to this proof to prove false. To prove this
backwards, we assume a proof of false, then do case analysis
on this proof to get a proof of P. We then apply this proof
and the proof of false to the and introduction rule to 
prove P ∧ false. Then we apply the if and only if intro 
rule to these two proofs. 
-/


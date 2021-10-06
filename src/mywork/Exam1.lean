/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

(P Q : Prop) (p2q : P → Q) (p : P)
----------------------------------
     q : Q
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q,
  assume p2q,
  assume p,
  apply p2q p,
end

-- Extra credit [2 points]. Who invented this principle?



-- -------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- answer here

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := 


-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- If we have a proof of P and a proof of Q, the and introduction
rule gives a proof of P ∧ Q.

ELIMINATION

Given the elimination rules for ∧ in both
inference rule and English language forms.
-/
/-(P Q : Prop) (pq : P ∧ Q) 
---------------------------- elim
        (p : P) (q : Q)
        
In english this states that given propositions P and Q, and a
proof of P ∧ Q, we can derive a proof of P, from the left and 
elimination rule, and a proof of Q, from the right and
elimination rule. -/
/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀ (P Q : Prop), Q ∧ P → P := 
begin
  assume P Q,
  assume qandp,
  apply and.elim_right qandp, 
end


-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- The introduction rule for for all is to assume an arbitrary,
yet specific case of type T, and then prove the proposition Q for
that case of T.

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                q : Q

-- Given a proof that Q is true for all t of type T, and a 
proof t of type T, we can apply the proof of Q being true
for all T to the proof of T, and from this get a proof of Q.

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- We know that Q is true for all t of type T, from the proof pf. 
We are then given a value t of type T. Using this value, we derive
a proof of Q, because we know Q is true for all T, and we also
have a value of this type T, so we know Q must be true. 
-/

/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalizee the following assumptions here
  -- (1) Lynn is a person
  -- (2) Lynn knows logic
  (Lynn : Person)
  (LynnKnowsLogic : KnowsLogic Lynn)

/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : ∀  (Person : Type ) (KnowsLogic BetterComputerScientist : Person → Prop)
 (Lynn : Person) (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p),
  KnowsLogic Lynn → BetterComputerScientist Lynn:= 
 begin
   assume Person,
   assume KnowsLogic BetterComputerScientist,
   assume Lynn,
   assume LogicMakesYouBetterAtCS,
   assume LKL,
   apply LogicMakesYouBetterAtCS,
   apply LKL,
 end  



-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := P → false -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

-- In proof by negation, one assumes the proposition P, 
-- and then shows that this leads to a contradiction,
-- and then conclude p → false. 
 

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume  ¬P and show that this yields a contradiction.
From this derivation you can conclude  ¬¬P.
Then you apply the rule of negation elimination
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is classicaly valid, and that accepting the axiom
of the excluded middle suffices to establish negation
 elimination (better called double negation elimination)
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

example : ∀ ( P Q : Prop), (P ↔ Q) → (Q ↔ P) :=
begin
assume P Q,
assume piffq,
apply iff.intro _ _,
assume q,
apply iff.elim_right piffq,
apply q,
assume p,
apply iff.elim_left piffq,
apply p,
end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/

def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 
    

example : ELJL :=
begin
  unfold ELJL,
  intros Person Nice Talented Likes,
  assume elantp,
  assume JohnLennon,
  assume JLNT,
  apply elantp JohnLennon,
  apply and.elim_left JLNT,
  apply and.elim_right JLNT,
end

/- Fluent English Rendition:
We have a proof that for all people, every person likes a person 
who is nice and talented. We have a proof that John Lennon is nice,
and John Lennon is talented. We apply the proof that for all
people, everyone likes a person who is nice and talented to the proof 
of John Lennon.  Then we just need a proof that John Lennon is
nice, and a proof that John Lennon is talented. We achieve these by
applying the left and elimination rule and the right and elimination
rule to the proof that John Lennon is Nice and John Lennon is talented. 

-/

/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? __
-- list the cases (informaly)
    -- heavy red
    -- heavy blue
    -- light red
    -- light blue

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), x = y → y = x

def eq_is_transitive : Prop :=
  ∀ (T : Type) ( x y z : T), x = y → y = z → x = z


/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/

def negelim_equiv_exmid : Prop := 
  ∀ (P : Prop), ¬¬P ↔ P ∨ ¬P
  
  example : negelim_equiv_exmid :=
  begin
    unfold negelim_equiv_exmid,
    assume P,
    apply iff.intro _ _,
    assume nnp,
    apply or.intro_left,
    have pornp := classical.em P,
    cases pornp with p pn,
    assumption,
    contradiction,
    assume pornp,
    apply or.elim pornp,
    assume p,
    contradiction,
    assume np,
    assume np,
    apply np,
    
  end  



/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop

example :  (∃ (p1 : Person), ∀ ( p2 : Person), Loves p2 p1) → (∀ ( p3 : Person), ∃ (p4 : Person), Loves p3 p4) := 
begin
  assume h,
  cases h with p pf,
  assume p3,
  apply exists.intro p,
  apply pf p3,
end


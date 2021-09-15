axioms (P Q : Prop)

def if_P_is_true_then_so_is_Q : Prop := P → Q

axiom p : P
-- assume P is true
-- assume we have a proof of P (p)

axiom pq : P → Q
-- assume that we have a proof pq of P implies Q 

--intro for assume premise show conclusion
-- elimination rule for implies: 
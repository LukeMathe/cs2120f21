/-
A simple predicate.
-/
def ev (n : ℕ) : Prop := n%2=0


/-
Introduction rule for exists
-/
example : exists (n : ℕ), ev n :=
begin
  apply exists.intro ,
  
end

example : exists n, ev n := _

def pythagorean_triple ( a b c : nat) : Prop :=   a*a + b*b = c*c


example : pythagorean_triple 3 4 5 := 
begin
unfold pythagorean_triple,
apply eq.refl,
end  


example : ∀ (n : ℕ), ∃ (m : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro _,
end

example : ∀ (m : ℕ), ∃ (n : ℕ), n = 2 * m :=
begin
  intros,
  apply exists.intro (2*m),
end

example : (∃ (n : nat), ev n) → true :=
begin
assume h,
cases h with v pf,
intros,
end
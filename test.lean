/-

This exam focuses on assessing your 
ability to write and prove propositions 
in predicate logic, with an emphasis on
predicates, disjunctions, and existentially 
quantified propositions. There are three 
parts: 

A: Predicates [20 points in 4 parts]
B: Disjuctions [40 points in 2 parts]
C. Existentials [40 point in 2 parts]
-/

/- Chuanhao Ma   cm9mb -/
/- ******************************** -/
/- *** A. PREDICATES [20 points] ***-/
/- ******************************** -/

/-
1a. Define a function called isOdd that
takes an argument, n : ℕ, and returns a 
proposition that asserts that n is odd.
The function will thus be a predicate on 
values of type ℕ. Hint: a number is odd
if it's one more than an even number.
-/
def isOdd(n : ℕ) : Prop := ∃ m, m*2+1 = n


/-
1b. To test your predicate, use "example"
to write and prove isOdd(15).
-/
example : isOdd(15) :=
begin
    unfold isOdd,
    apply exists.intro 7,
    apply eq.refl,
end


/-
1c. Define isSmall : ℕ → Prop, to be a
predicate that is true exactly when the
argument, n, is such that n = 0 ∨ n = 1
∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5. (Don't
try to rewrite this proposition as an 
inequality; just use it as is.) 
-/
def isSmall(n : ℕ) : Prop := 
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5


/-
1d. Define a predicate, isBoth(n:ℕ) that 
is true exacly when n satisfies both the
isOdd and isSmall predicates. Use isOdd 
and isSmall in your answer.
-/
def isBoth(n : ℕ) : Prop := (isOdd n) ∧ (isSmall n)



/- ******************* -/
/- *** DISJUNCTIONS ***-/
/- ******************* -/

/-
2. [20 Points]

Jane walks to school or she carries 
her lunch. In either case, she uses
a bag. If she walks, she uses a bag for
her books. If she carries her lunch, she
uses a bag to carry her food. So if she
walks, she uses a bag, and if she carries
her lunch, she uses a bag. From the fact
that she walks or carries her lunch, and
from the added facts that in either case 
she uses a bag, we can conclude that she 
uses a bag.

Using Walks, Carries, and Bag as names
of propositions, write a Lean example 
that asserts the following proposition; 
then prove it. 

If Walks, Carries, and Bag are 
propositions, then if (Walks ∨ Carries) 
is true, and then if (Walks implies Bag)
is true, and then if (Carries implies Bag)
is true, then Bag is true.

Here's a start.

example : ∀ (Walks Carries Bag : Prop), ...
-/
example : ∀ (Walks Carries Bag : Prop),
    (Walks ∨ Carries) →
    (Walks → Bag) →
    (Carries → Bag) →
    Bag :=
begin
    assume Walks Carries Bag,
    assume WalksOrCarries: (Walks ∨ Carries),
    assume WalksWithBag: (Walks → Bag),
    assume CarriesWithBag: (Carries → Bag),
    cases WalksOrCarries with walks carries,
    show Bag, from WalksWithBag walks,
    show Bag, from CarriesWithBag carries,
end


/-
3. [20 Points]

Prove the following proposition.
-/

example : 
    ∀ (P Q R : Prop), 
    (P ∧ Q) → (Q ∨ R) → (P ∨ R) :=
begin
    intros P Q R,
    intros PandQ QorR,
    apply or.inl PandQ.left,
end


/- *********************** -/
/- *** C. EXISTENTIALS  ***-/
/- *********************** -/

/-
4. [20 points]

Referring to the isBoth predicate you
defined in question #1, state and prove 
the proposition that there *exists* a 
number, n, that satisfies isBoth. Remember 
that you can use the unfold tactic to 
expand the name of a predicate in a goal.
Use "example" to state the proposition.
-/
example :
∃ n, isBoth n :=
begin
    unfold isBoth,
    apply exists.intro 3,
    apply and.intro,
    unfold isOdd,
    apply exists.intro 1,
    apply eq.refl,
    unfold isSmall,
    apply or.inr,
    apply or.inr,
    apply or.inr,
    apply or.inl,
    apply eq.refl,
end

/-
5. [20 points]

Suppose that Heavy and Round are
predicates on values of any type, T.
Prove the proposition that if every 
t : T is Heavy (satisfies the Heavy 
predicate) and if there exists some 
t : T that is Round (satisfies the
Round predicate) then there exists 
some t : T is both Heavy and Round
(satisfies the conjunction of the
two properties). 
-/

example : 
∀ T : Type, ∀ (Heavy Round : T → Prop),
(∀ t, Heavy t) → (∃ t, Round t) →
(∃ t, Heavy t ∧ Round t) :=
begin
intro T,
intros H R,
assume allTH,
assume someTR,
apply exists.elim someTR,
intro w,
assume wR,
have wH := allTH w,
apply exists.intro w,
exact ⟨ wH, wR ⟩,
end

/-

5. [20 points] New problem

Since we worked out that problem in class,
here's a replacement problem: Show that if
there exists an object of some type, T, that
has properties P and Q, then there exists an
object of that type that has the property
P or Q. Remember that a property is defined
by a predicate.
-/
example :
∀ T : Type, ∀ (P Q : T → Prop),
(∃ t, P t ∧ Q t) → (∃ o, P o ∨ Q o) :=
begin
    intros T P Q,
    intro ex,
    apply exists.elim ex,
    intros w pwandqw,
    apply exists.intro w,
    exact or.inl pwandqw.left,
end

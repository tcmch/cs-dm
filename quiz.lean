example :
    ∀ (x : Type),
    ∀ (p q : x → Prop),
    (∀ x, p x) ∨ (∀ x, q x) →
    ∀ x, p x ∨ q x :=
begin
    intros,
    cases a with ap aq,
    apply or.intro_left,
    exact ap x_1,
    apply or.intro_right,
    exact aq x_1, 
end

example :
    ∀ (X : Type),
    ∀ (p q : X → Prop),
    (exists x , p x) ∨ (exists x, q x) →
    exists x, p x ∨ q x :=
begin
    intros,
    cases a with ep eq,
    apply exists.elim ep,
    intros,
    exact exists.intro a (or.inl a_1),
    apply exists.elim eq,
    intros,
    exact exists.intro a (or.inr a_1),
end

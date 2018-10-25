example : ∀ P Q : Prop, P → Q → P ∧ Q :=
begin
    assume P Q : Prop,
    assume p,
    assume q,
    show P ∧ Q,
    apply and.intro,
    exact p,
    exact q,
end

example : ∀ P Q : Prop, P ∧ Q → P :=
begin
    assume P Q : Prop,
    assume pandq,
    show P,
    apply and.left pandq,
end

example : ∀ P : Prop, P → ¬ ¬ P :=
begin
    assume P : Prop,
    assume p,
    show ¬ ¬ P,
    from
        begin
            assume np,
            have f : false := np p,
            apply false.elim f,
        end
end

example : ∀ P Q : Prop, P ∧ ¬ P → Q :=
begin
    intros P Q pandq,
    show Q,
    from
    begin
        have f : false :=
            pandq.right pandq.left,
        apply false.elim f,
    end    
end

example : ∀ P Q : Prop, P ∧ Q → Q ∧ P :=
begin
    intros P Q pandq,
    have p : P := pandq.left,
    have q : Q := pandq.right,
    show Q ∧ P,
    apply and.intro q p,
end

example : ∀ R S W : Prop, R ∨ S → (R → W) → (S → W) → W :=
begin
    intros R S W rors rimw simw,
    cases rors with pfR pfS,
    exact rimw pfR,
    exact simw pfS,
end

example : ∀ P Q : Prop, P ∨ Q → Q ∨ P :=
begin
    intros P Q porq,
    cases porq with pfP pfQ,
    exact or.inr pfP,
    exact or.inl pfQ,
end

axiom em : ∀ P, P ∨ ¬ P

example : ∀ P : Prop, P → (true ∨ false) :=
begin
    intros,
    cases (em P) with p np,
    apply or.intro_left,
    exact true.intro,
    apply or.intro_right,
    exact np a,
end

example : ∀ P Q : Prop, ¬ (P ∧ Q) → (¬ P) ∨ (¬ Q) :=
begin
    intros P Q npandq,
    cases (em P) with p np,
    apply or.intro_right,
    assume q,
    apply npandq (and.intro p q),
    apply or.intro_left,
    exact np,
end

example : ∀ P Q : Prop, (¬ P) ∨ (¬ Q) → ¬ (P ∧ Q) :=
begin
    intros P Q npornq,
    assume porq,
    cases npornq with np nq,   
    exact np porq.left,
    exact nq porq.right,
end

example : ∀ P Q : Prop, (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) :=
begin
    intros P Q npandnq,
    have np := npandnq.left,
    have np := npandnq.right,
    assume porq,
    cases porq with p q,
    contradiction,
    contradiction,
end

example : ∀ P Q : Prop, ¬ (P ∨ Q) → (¬ P) ∧ (¬ Q) :=
begin
    intros P Q nporq,
    apply and.intro,
    assume p,
    apply nporq (or.inl p),
    assume q,
    apply nporq (or.inr q),
end


variables P Q : Prop
variable pfP : P
variable pfQ : Q
#check (and.intro pfP pfQ)

def and_comm1(P Q: Prop)(pq: P /\ Q) : (Q /\ P) :=
    and.intro (and.elim_right pq) (and.elim_left pq)
#check and_comm1 P Q (and.intro pfP pfQ)

def and_comm2 : ∀ P Q: Prop, P /\ Q → Q /\ P :=
    λ X Y pq,
    and.intro (and.elim_right pq) (and.elim_left pq)
#check and_comm2

def inc: ℕ → ℕ :=
λ n : ℕ, 0

def n: nat := 0

#check true

def t: true := true.intro

#check false

def no_contra: ∀ P: Prop, ¬(P /\ ¬ P) :=
    λ P pf, pf.right pf.left
#check no_contra


theorem foo : ∀ P Q R : Prop, (P → Q) → (Q → R) → (P → R) :=
    λ P Q R pq qr, 
        λ P, qr (pq P)
#check foo

section se

theorem zeqz : 0 = 0 := eq.refl 0
theorem zneqo : 0 ≠ 1 :=
begin
    assume zeqo : 0 = 1,
    show false,
    from nat.no_confusion zeqo
end

theorem zneqo' : 0 = 1 → false :=
    λ pf : 0 = 1, nat.no_confusion pf



end se
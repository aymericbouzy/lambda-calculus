Require Import Arith.
Require Import List.
Require Import Compare_dec.
Require Import Omega.

Inductive term: Set :=
| var: nat -> term
| lambda: term -> term
| application: term -> term -> term.

Fixpoint closed (n: nat) (t: term): Prop :=
match t with
| var x => x < n
| lambda t => closed (S n) t
| application t u => (closed n t) /\ (closed n u)
end.

Fixpoint closed_list (n:nat) (l: list term): Prop :=
match l with
| nil => True
| t :: r => (closed n t) /\ (closed_list n r)
end.

Proposition closed_implication : forall t:term, forall n:nat, (closed n t) -> (closed (S n) t).
Proof.
induction t.
simpl.
apply le_S.
intro.
simpl.
apply IHt.
intro.
simpl.
intro.
split.
apply IHt1.
case H.
intros.
exact H0.
apply IHt2.
case H.
intros.
exact H1.
Qed.

Fixpoint increase_var (s: term) (n: nat) (p: nat): term :=
match s with
| var x => (match nat_compare x p with
  | Gt => var (x + n) 
  | _ => var x
  end)
| lambda t => increase_var t (S n) (S p)
| application t u => application (increase_var t n p) (increase_var u n p)
end.

Fixpoint de_bruijn_substitution (t: term) (s: term) (n: nat): term :=
match t with
| var x => if (beq_nat x n) then increase_var s n 0 else var x
| lambda t => lambda (de_bruijn_substitution t s (S n))
| application t u => application (de_bruijn_substitution t s n) (de_bruijn_substitution u s n)
end.

Fixpoint de_bruijn_aux (x: nat) (l: list term) (n: nat): term :=
match l with
  | nil => var x
  | s :: r => if (beq_nat x n) then increase_var s n 0 else de_bruijn_aux x r (S n)
end.

Fixpoint de_bruijn_substitution_list (t: term) (l: list term) (n: nat): term :=
match t with
| var x => de_bruijn_aux x l n
| lambda t => lambda (de_bruijn_substitution_list t l (S n))
| application t u => application (de_bruijn_substitution_list t l n) (de_bruijn_substitution_list u l n)
end.


Fixpoint eq_term (t1:term) (t2:term): Prop :=
match t1, t2 with
| var x1, var x2 => x1 = x2
| lambda u1, lambda u2 => eq_term u1 u2
| application r1 u1, application r2 u2 => (eq_term r1 r2) /\ (eq_term u1 u2)
| _, _ => False
end.

Proposition eq_term_eq : forall t:term, eq_term t t.
Proof.
intro.
induction t.
simpl.
trivial.
simpl.
exact IHt.
simpl.
split.
exact IHt1.
exact IHt2.
Qed.

Proposition nil_substitution : forall t:term, forall i:nat, (de_bruijn_substitution_list t nil i) = t.
Proof.
intro.
induction t.
intros.
simpl.
trivial.
intros.
simpl.
rewrite IHt.
trivial.
intros.
simpl.
rewrite IHt1.
rewrite IHt2.
trivial.
Qed.

Proposition missing_variable_substitution : forall t:term, forall i:nat, closed i t -> match l with | nil => True | u :: r => (de_bruijn_substitution t u i) = t.
Proof.
intro. intro.
induction t.
intros.
simpl.
assert (n < i).
apply H.
assert (beq_nat n i = false).
apply beq_nat_false_iff.
omega.
rewrite H1.
trivial.
intros.
simpl.
rewrite IHt.
trivial.
apply H.
intros.
simpl.
rewrite IHt1.
rewrite IHt2.
trivial.
case H.
trivial.
case H.
trivial.
Qed.

Proposition successive_subsitutions : forall l:list term, forall t:term, forall u:term, forall i: nat, closed_list i (u :: l) -> (de_bruijn_substitution (de_bruijn_substitution_list t l (S i)) u i) = (de_bruijn_substitution_list t (u :: l) i).
Proof.
intro.
induction l.
simpl.
intro.
induction t.
intros.
simpl.
destruct (beq_nat n i);
trivial.
simpl.
intros.
rewrite nil_substitution.
rewrite <- IHt.
rewrite nil_substitution.
trivial.
split.
apply closed_implication.
case H.
trivial.
trivial.
intros.
rewrite nil_substitution.
simpl.
rewrite <- IHt1.
rewrite <- IHt2.
rewrite nil_substitution.
rewrite nil_substitution.
trivial.
exact H.
exact H.
intros.


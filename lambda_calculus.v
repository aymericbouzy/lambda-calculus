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

Fixpoint eq_nat_branch (n1 n2: nat) (t1 t2: term): term :=
match n1, n2 with
| 0, 0 => t1
| 0, _ => t2
| _, 0 => t2
| S(m1), S(m2) => eq_nat_branch m1 m2 t1 t2
end.

Proposition eq_branch_real_eq : forall n1 n2: nat, forall t1 t2: term, n1 = n2 -> eq_nat_branch n1 n2 t1 t2 = t1.
Proof.
intro.
induction n1.
intro.
induction n2.
intros.
simpl.
trivial.
intros.
contradict H.
trivial.
intro.
induction n2.
intros.
contradict H.
apply not_eq_sym.
trivial.
intros.
simpl.
apply IHn1.
omega.
Qed.

Proposition neq_branch_real_neq : forall n1 n2: nat, forall t1 t2: term, n1 <> n2 -> eq_nat_branch n1 n2 t1 t2 = t2.
Proof.
intro.
induction n1.
intro.
induction n2.
intros.
simpl.
contradict H.
trivial.
intros.
simpl.
trivial.
intro.
induction n2.
intros.
simpl.
trivial.
intros.
simpl.
apply IHn1.
omega.
Qed.

Fixpoint de_bruijn_substitution (t: term) (s: term) (n: nat): term :=
match t with
| var x => eq_nat_branch x n (increase_var s n 0) (var x)
| lambda t => lambda (de_bruijn_substitution t s (S n))
| application t u => application (de_bruijn_substitution t s n) (de_bruijn_substitution u s n)
end.

Fixpoint de_bruijn_aux (x: nat) (l: list term) (n: nat): term :=
match l with
  | nil => var x
  | s :: r => eq_nat_branch x n (increase_var s n 0) (de_bruijn_aux x r (S n))
end.

Proposition de_bruijn_aux_terminate : forall (l: list term), forall (x n: nat), x < n -> de_bruijn_aux x l n = var x.
Proof.
intro.
induction l.
intros.
simpl.
trivial.
intros.
simpl.
assert (de_bruijn_aux x l (S n) = var x).
apply IHl.
omega.
rewrite <- H0.
apply neq_branch_real_neq.
omega.
Qed.

Fixpoint de_bruijn_substitution_list (t: term) (l: list term) (n: nat): term :=
match t with
| var x => de_bruijn_aux x l n
| lambda t => lambda (de_bruijn_substitution_list t l (S n))
| application t u => application (de_bruijn_substitution_list t l n) (de_bruijn_substitution_list u l n)
end.

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

Proposition missing_variable_substitution : forall t:term, forall u:term, forall i:nat, closed i t -> (de_bruijn_substitution t u i) = t.
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
apply neq_branch_real_neq.
omega.
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
intro.
induction t.
intros.
simpl.
assert ((n = i) \/ (n = S i) \/ (n <> i /\ n <> S i)).
omega.
case H0.
intro.
assert (eq_nat_branch n i (increase_var u i 0)
  (eq_nat_branch n (S i) (increase_var a (S i) 0)
     (de_bruijn_aux n l (S (S i)))) = increase_var u i 0).
apply eq_branch_real_eq.
exact H1.
rewrite H2.
assert (eq_nat_branch n (S i) (increase_var a (S i) 0)
     (de_bruijn_aux n l (S (S i))) = (de_bruijn_aux n l (S (S i)))).
apply neq_branch_real_neq.
omega.
rewrite H3.
assert (de_bruijn_aux n l (S (S i)) = var n).
apply de_bruijn_aux_terminate.
omega.
rewrite H4.
simpl.
apply eq_branch_real_eq.
exact H1.
intros.
case H1.
intros.
assert (eq_nat_branch n (S i) (increase_var a (S i) 0)
     (de_bruijn_aux n l (S (S i))) = increase_var a (S i) 0).
apply eq_branch_real_eq.
exact H2.
rewrite H3.
assert (eq_nat_branch n i (increase_var u i 0) (increase_var a (S i) 0) = increase_var a (S i) 0).
apply neq_branch_real_neq.
omega.
rewrite H4.
apply missing_variable_substitution.
induction a.
simpl.





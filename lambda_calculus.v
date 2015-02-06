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

Proposition eq_unconditionnal_branch : forall (n1 n2: nat), forall (t: term), eq_nat_branch n1 n2 t t = t.
Proof.
intro.
induction n1.
intro.
induction n2.
intros.
simpl.
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
Qed.

Fixpoint gt_nat_branch (n1 n2: nat) (t1 t2: term): term :=
match n1, n2 with
| 0, 0 => t2
| 0, _ => t2
| _, 0 => t1
| S(m1), S(m2) => gt_nat_branch m1 m2 t1 t2
end.

Proposition gt_branch_real_gt : forall n1 n2: nat, forall t1 t2: term, n1 > n2 -> gt_nat_branch n1 n2 t1 t2 = t1.
Proof.
intro.
induction n1.
intro.
induction n2.
intros.
omega.
intros.
omega.
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

Proposition leq_branch_real_leq : forall n1 n2: nat, forall t1 t2: term, n1 <= n2 -> gt_nat_branch n1 n2 t1 t2 = t2.
Proof.
intro.
induction n1.
intro.
induction n2.
intros.
simpl.
trivial.
intros.
simpl.
trivial.
intro.
induction n2.
intros.
omega.
intros.
simpl.
apply IHn1.
omega.
Qed.

Proposition gt_unconditionnal_branch : forall (n1 n2: nat), forall (t: term), gt_nat_branch n1 n2 t t = t.
Proof.
intro.
induction n1.
intro.
induction n2.
intros.
simpl.
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
Qed.

Fixpoint increase_var (s: term) (n: nat) (p: nat): term :=
match s with
| var x => gt_nat_branch x p (var (x + n)) (var x)
| lambda t => lambda (increase_var t n (S p))
| application t u => application (increase_var t n p) (increase_var u n p)
end.

Proposition increase_var_keeps_close : forall (s: term), forall (i n p: nat), closed i s -> closed (i+n) (increase_var s n p).
Proof.
intro.
induction s.
intros.
simpl.
assert (n > p \/ n <= p).
omega.
case H0.
intro.
rewrite gt_branch_real_gt.
simpl.
simpl in H.
omega.
trivial.
intro.
rewrite leq_branch_real_leq.
simpl.
simpl in H.
omega.
trivial.
intros.
simpl.
assert (S (i + n) = (S i) + n).
omega.
rewrite H0.
apply IHs.
simpl in H.
trivial.
intros.
simpl.
simpl in H.
case H.
intros.
split.
apply IHs1.
trivial.
apply IHs2.
trivial.
Qed.

Proposition increase_is_id : forall (s: term), forall (n p:nat), closed p s -> increase_var s n p = s.
Proof.
intro.
induction s.
intros.
simpl.
apply leq_branch_real_leq.
simpl in H.
omega.
intros.
simpl.
rewrite IHs.
trivial.
simpl in H.
trivial.
intros.
simpl.
rewrite IHs1.
rewrite IHs2.
trivial.
case H.
intros.
trivial.
case H.
intros.
trivial.
Qed.

Fixpoint de_bruijn_substitution (t: term) (s: term) (n: nat) (p:nat): term :=
match t with
| var x => eq_nat_branch x (n + p) (increase_var s p 0) (var x)
| lambda t => lambda (de_bruijn_substitution t s n (S p))
| application t u => application (de_bruijn_substitution t s n p) (de_bruijn_substitution u s n p)
end.

Fixpoint de_bruijn_aux (x: nat) (l: list term) (n m p: nat): term :=
match l with
  | nil => var x
  | s :: r => eq_nat_branch x (n + m + p) (increase_var s m 0) (de_bruijn_aux x r n m (S p))
end.

Proposition de_bruijn_aux_terminate : forall (l: list term), forall (x n m p: nat), x < n + m + p -> de_bruijn_aux x l n m p = var x.
Proof.
intro.
induction l.
intros.
simpl.
trivial.
intros.
simpl.
rewrite IHl.
rewrite neq_branch_real_neq.
trivial.
omega.
omega.
Qed.

Fixpoint de_bruijn_substitution_list (t: term) (l: list term) (n p: nat): term :=
match t with
| var x => de_bruijn_aux x l n p 0
| lambda t => lambda (de_bruijn_substitution_list t l n (S p))
| application t u => application (de_bruijn_substitution_list t l n p) (de_bruijn_substitution_list u l n p)
end.

Proposition nil_substitution : forall t:term, forall i p:nat, (de_bruijn_substitution_list t nil i p) = t.
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

Proposition missing_variable_substitution : forall t:term, forall u:term, forall i p:nat, closed (i+p) t -> (de_bruijn_substitution t u i p) = t.
Proof.
intro. intro.
induction t.
intros.
simpl.
rewrite neq_branch_real_neq.
trivial.
simpl in H.
omega.
intros.
simpl.
rewrite IHt.
trivial.
simpl in H.
assert (i + S p = S (i + p)).
omega.
rewrite H0.
trivial.
intros.
simpl.
rewrite IHt1, IHt2.
trivial.
simpl in H.
case H.
intros.
trivial.
simpl in H.
case H.
intros.
trivial.
Qed.

Proposition successive_substitutions : forall l:list term, forall t:term, forall u:term, forall i p: nat, closed_list i l -> de_bruijn_substitution (de_bruijn_substitution_list t l (S i) p) u i p = de_bruijn_substitution_list t (u :: l) i p.
Proof.
intro.
induction l.
intro.
induction t.
intros.
simpl.
assert (i + p + 0 = i + p).
omega.
rewrite H0.
trivial.
intros.
rewrite nil_substitution.
assert (de_bruijn_substitution_list t (u :: nil) i (S p) = de_bruijn_substitution (de_bruijn_substitution_list t nil (S i) (S p)) u i
        (S p)).
rewrite IHt.
trivial.
simpl.
trivial.
simpl.
rewrite H0.
rewrite nil_substitution.
trivial.
intros.
simpl.
rewrite IHt1, IHt2.
trivial.
trivial.
trivial.
intro.
induction t.
intros.
simpl.
assert ((n = i + p) \/ (n = S i + p) \/ (n <> i  + p /\ n <> S i + p)).
omega.
case H0.
intros.
assert (eq_nat_branch n (i + p + 0) (increase_var u p 0)
  (eq_nat_branch n (i + p + 1) (increase_var a p 0) (de_bruijn_aux n l i p 2)) = increase_var u p 0).
apply eq_branch_real_eq.
omega.
rewrite H2.
rewrite neq_branch_real_neq.
rewrite de_bruijn_aux_terminate.
simpl.
apply eq_branch_real_eq.
trivial.
omega.
omega.
intros.
case H1.
intros.
assert (eq_nat_branch n (S (i + p + 0)) (increase_var a p 0)
     (de_bruijn_aux n l (S i) p 1) = increase_var a p 0).
rewrite eq_branch_real_eq.
trivial.
omega.
rewrite H3.
assert (eq_nat_branch n (i + p + 1) (increase_var a p 0) (de_bruijn_aux n l i p 2) = increase_var a p 0).
rewrite eq_branch_real_eq.
trivial.
omega.
rewrite H4.
rewrite neq_branch_real_neq.
rewrite missing_variable_substitution.
trivial.
simpl in H.





induction a.
simpl.
induction n0.
rewrite leq_branch_real_leq.
simpl.
simpl in H.
case H.
intros.
omega.
omega.
simpl.
simpl in H.
case H.
intros.
omega.
simpl.




simpl.
apply closed_implication.
rewrite nil_substitution in IHt.
simpl in IHt.
rewrite nil_subsititution
rewrite missing_variable_substitution.
simpl.
assert ((n = i) \/ (n = S i) \/ (n <> i /\ n <> S i)).
omega.
rewrite increase_is_id.



simpl in IHt. 

rewrite IHt.
assert (de_bruijn_substitution (de_bruijn_substitution_list t nil (S i)) u i = de_bruijn_substitution_list t nil (S i)).
apply missing_variable_substitution.


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
assert (increase_var a (S i) 0 = a).
apply increase_is_id.
simpl in H.
induction a.
simpl.
assert (closed i (var n0)).
case H.
intros.
case H6.
intros.
trivial.
simpl in H5.

induction n0.
assert (gt_nat_branch 0 0 (var (0 + S i)) (var 0) = var 0).
apply leq_branch_real_leq.
trivial.
omega.
rewrite H6.
trivial.
assert (gt_nat_branch (S n0) 0 (var (S n0 + S i)) (var (S n0)) = var (S n0 + S i)).
apply gt_branch_real_gt.
omega.
rewrite H6.
simpl.


case H5.
induction n0.
simpl.
apply closed_implication.
omega.
simpl.
omega.
intros.
induction n0.
simpl.
omega.
simpl.
omega.
case H.
intros.
case H6.
intros.
assert (closed (S i) a = closed i (lambda a)).
simpl.
trivial.
simpl.

rewrite H9.
trivial.
simpl.
case H.
intros.
case H6.
intros.
assert ((closed i a1 /\ closed i a2) = closed i (application a1 a2)).
simpl.
trivial.
rewrite H9.
trivial.
intros.
assert (eq_nat_branch n (S i) (increase_var a (S i) 0)
     (de_bruijn_aux n l (S (S i))) = de_bruijn_aux n l (S (S i))).
apply neq_branch_real_neq.
omega.
rewrite H3.
assert (eq_nat_branch n i (increase_var u i 0) (de_bruijn_aux n l (S (S i))) = de_bruijn_aux n l (S (S i))).
apply neq_branch_real_neq.
omega.
rewrite H4.
apply missing_variable_substitution.

assert (eq_nat_branch n i (increase_var u i 0)
  (eq_nat_branch n (S i) (increase_var a (S i) 0)
     (de_bruijn_aux n l (S (S i)))) = de_bruijn_aux n l (S (S i))).
apply neq_branch_real_neq.


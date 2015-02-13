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

Fixpoint de_bruijn_substitution (t: term) (s: term) (p:nat): term :=
match t with
| var x => eq_nat_branch x p (increase_var s p 0) (var x)
| lambda t => lambda (de_bruijn_substitution t s (S p))
| application t u => application (de_bruijn_substitution t s p) (de_bruijn_substitution u s p)
end.

Fixpoint de_bruijn_aux (x: nat) (l: list term) (m p: nat): term :=
match l with
  | nil => var x
  | s :: r => eq_nat_branch x (m + p) (increase_var s m 0) (de_bruijn_aux x r m (S p))
end.

Proposition de_bruijn_aux_terminate : forall (l: list term), forall (x m p: nat), x < m + p -> de_bruijn_aux x l m p = var x.
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

Proposition de_bruijn_aux_keeps_close : forall (l: list term), forall (x i n p: nat), closed_list i l -> x < i + n -> closed (i+n) (de_bruijn_aux x l n p).
Proof.
intro.
induction l.
intros.
simpl.
trivial.
intros.
simpl.
simpl in H.
case H.
intros.
assert (x = n + p \/ x <> n + p).
omega.
case H3.
intro.
rewrite eq_branch_real_eq.
apply increase_var_keeps_close.
trivial.
trivial.
intro.
rewrite neq_branch_real_neq.
apply IHl.
trivial.
trivial.
trivial.
Qed.

Fixpoint de_bruijn_substitution_list (t: term) (l: list term) (n p: nat): term :=
match t with
| var x => de_bruijn_aux x l p n
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

Proposition missing_variable_substitution : forall t:term, forall u:term, forall p:nat, closed p t -> (de_bruijn_substitution t u p) = t.
Proof.
intro.
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
(*
Proposition successive_substitutions : forall t: term, forall u:term, forall l:list term, forall i p: nat, closed_list i l -> de_bruijn_substitution (de_bruijn_substitution_list t l (S i) p) u i p = de_bruijn_substitution_list t (u :: l) i p.
Proof.
intro.
induction t.
intro.
induction u.
simpl.
intros.
assert (n = p + i \/ n <> p + i).
omega.
case H0.
intro.
rewrite de_bruijn_aux_terminate.
simpl.
assert (i + p = p + i).
omega.
rewrite H2.
trivial.
omega.
intro.
rewrite neq_branch_real_neq.
rewrite missing_variable_substitution.
trivial.
apply de_bruijn_aux_keeps_close.
trivial.



Qed.
*)

Proposition successive_substitutions : forall l:list term, forall t:term, forall u:term, forall i p: nat, closed_list i l -> de_bruijn_substitution (de_bruijn_substitution_list t l (S i) p) u (p + i) = de_bruijn_substitution_list t (u :: l) i p.
Proof.
(* intro.
induction l.
intro.
induction t.
intros.
simpl.
assert (p + i = i + p).
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
intros. *)
admit.
Qed.

Inductive reduce_one: term -> term -> Prop :=
  | red_app_left: forall t u v: term, reduce_one t u -> reduce_one (application t v) (application u v)
  | red_app_right: forall t u v: term, reduce_one u v -> reduce_one (application t u) (application t v)
  | red_lambda: forall t u: term, reduce_one t u -> reduce_one (lambda t) (lambda u)
  | red_beta: forall t u v: term, t = application (lambda u) v -> reduce_one t (de_bruijn_substitution u v 0)
.

Inductive reduce_any: term -> term -> Prop :=
  | red_identity: forall t u: term, t = u -> reduce_any t u
  | red_trans: forall t u v: term, reduce_one t u -> reduce_any u v -> reduce_any t v
.

Proposition reduce_one_is_any : forall t u: term, reduce_one t u -> reduce_any t u.
Proof.
intros.
apply (red_trans t u u).
exact H.
constructor.
trivial.
Qed.

Proposition reduce_any_app_left : forall t u v: term, reduce_any t u -> reduce_any (application t v) (application u v).
Proof.
intros.
induction H.
apply red_identity.
rewrite H.
trivial.
apply (red_trans (application t v) (application u v) (application v0 v)).
constructor.
trivial.
trivial.
Qed.

Proposition reduce_any_app_right : forall t u v: term, reduce_any u v -> reduce_any (application t u) (application t v).
Proof.
intros.
induction H.
apply red_identity.
rewrite H.
trivial.
apply (red_trans (application t t0) (application t u) (application t v)).
constructor.
trivial.
trivial.
Qed.

Proposition reduce_any_lambda : forall t u v: term, reduce_any t u -> reduce_any (lambda t) (lambda u).
Proof.
intros.
induction H.
apply red_identity.
rewrite H.
trivial.
apply (red_trans (lambda t) (lambda u) (lambda v0)).
constructor.
trivial.
trivial.
Qed.

Inductive instruction: Set := 
| Access: nat -> instruction
| Grab: instruction
| Push: list instruction -> instruction
.

Inductive environment: Set:=
| Nil_env: environment
| Env: list instruction -> environment -> environment -> environment
.

Inductive stack: Set:=
| Nil_stack: stack
| St: list instruction -> environment -> stack -> stack
.

Inductive krivine_state: Set :=
| Krivine_state: list instruction -> environment -> stack -> krivine_state.

Inductive one_step_krivine: krivine_state -> krivine_state -> Prop :=
| access_0: forall c c0 : list instruction, forall e e0: environment, forall s: stack, 
  one_step_krivine (Krivine_state ((Access 0) :: c) (Env c0 e0 e) s) (Krivine_state c0 e0 s)
| access_Sn : forall n: nat, forall c c0: list instruction, forall e e0: environment, forall s: stack,
  one_step_krivine (Krivine_state ((Access (S n)) :: c) (Env c0 e0 e) s) (Krivine_state ((Access n) :: c) e s)
| push : forall c' c: list instruction, forall e: environment, forall s: stack,
  one_step_krivine (Krivine_state ((Push c') :: c) e s) (Krivine_state c e (St c' e s))
| grab : forall c c0 : list instruction, forall e e0: environment, forall s: stack, 
  one_step_krivine (Krivine_state (Grab :: c) e (St c0 e0 s)) (Krivine_state c (Env c0 e0 e) s)
.

Fixpoint one_step_krivine_f (state: krivine_state) : option krivine_state :=
match state with
| Krivine_state ((Access 0) :: c) (Env c0 e0 e) s => Some (Krivine_state c0 e0 s)
| Krivine_state ((Access (S n)) :: c) (Env c0 e0 e) s => Some (Krivine_state ((Access n) :: c) e s)
| Krivine_state ((Push c') :: c) e s => Some (Krivine_state c e (St c' e s))
| Krivine_state (Grab :: c) e (St c0 e0 s) => Some (Krivine_state c (Env c0 e0 e) s)
| _, _, _ => None
end.


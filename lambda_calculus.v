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
| var x => var (x + n)
| lambda t => lambda (increase_var t n (S p))
| application t u => application (increase_var t n p) (increase_var u n p)
end.

Proposition increase_var_keeps_close : forall (s: term), forall (i n p: nat), closed i s -> closed (i+n) (increase_var s n p).
Proof.
intro.
induction s.
intros.
simpl.
simpl in H.
omega.
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
inversion H.
split.
apply IHs1.
trivial.
apply IHs2.
trivial.
Qed.
(*
Proposition increase_is_id : forall (s: term), forall (n p:nat), closed p s -> increase_var s n p = s.
Proof.
intro.
induction s.
intros.
simpl.
apply gt_branch_real_gt.
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
Qed.*)

Proposition null_increase : forall (s: term), forall (p: nat), increase_var s 0 p = s.
Proof.
intro. induction s.
intro.
simpl. assert (n + 0 = n). omega. rewrite H. trivial.
intro. simpl. rewrite IHs. trivial.
intro. simpl. rewrite IHs1. rewrite IHs2. trivial.
Qed.

Fixpoint de_bruijn_aux (x: nat) (l: list term) (p: nat): term :=
match l with
  | nil => var x
  | s :: r => eq_nat_branch x p (increase_var s p 0) (de_bruijn_aux x r (S p))
end.

Proposition de_bruijn_aux_terminate : forall (l: list term), forall (x p: nat), x < p -> de_bruijn_aux x l p = var x.
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

Proposition de_bruijn_aux_keeps_close : forall (l: list term), forall (x i p: nat), closed_list i l -> closed p (var x) -> closed (i+p) (de_bruijn_aux x l p).
Proof.
intros.
simpl.
simpl in H0.
rewrite de_bruijn_aux_terminate. simpl. omega. omega.
Qed.

Fixpoint de_bruijn_substitution_list (l: list term) (p: nat) (t: term) : term :=
match t with
| var x => de_bruijn_aux x l p
| lambda t => lambda (de_bruijn_substitution_list l (S p) t)
| application t u => application (de_bruijn_substitution_list l p t) (de_bruijn_substitution_list l p u)
end.

Proposition nil_substitution : forall t:term, forall p:nat, (de_bruijn_substitution_list nil p t) = t.
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

Proposition missing_variable_substitution : forall l: list term, forall t:term, forall p:nat, closed p t -> (de_bruijn_substitution_list l p t) = t.
Proof.
intro.
induction l. intros.
rewrite nil_substitution. trivial.
intro.
induction t.
intros.
simpl.
rewrite neq_branch_real_neq.
rewrite de_bruijn_aux_terminate.
trivial.
inversion H. omega. omega. inversion H. omega. omega.
intros.
simpl.
rewrite (IHt (S p)).
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

Proposition successive_substitutions : forall l:list term, forall t:term, forall u:term, forall p: nat, closed_list p (u :: l) -> de_bruijn_substitution_list (u :: nil) p (de_bruijn_substitution_list l (S p) t) = de_bruijn_substitution_list (u :: l) p t.
Proof.
intro.
induction l.
intros. rewrite nil_substitution. trivial.
intro. induction t.
simpl. intros. inversion H. inversion H1.
assert (n = p \/ n = S p \/ n > S p \/ n < p). omega. case H4.
intro. rewrite (eq_branch_real_eq n p).
rewrite neq_branch_real_neq. rewrite de_bruijn_aux_terminate.

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

Proposition successive_substitutions : forall l:list term, forall t:term, forall u:term, forall i p: nat, closed_list i l -> de_bruijn_substitution (de_bruijn_substitution_list l (S i) p t) u (p + i)= de_bruijn_substitution_list (u :: l) i p t.
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
| Push: list_instruction -> instruction
with list_instruction: Set :=
| Nil_block: list_instruction
| Block: instruction -> list_instruction -> list_instruction
.

Inductive environment: Set:=
| Nil_env: environment
| Env: list_instruction -> environment -> environment -> environment
.

Inductive stack: Set:=
| Nil_stack: stack
| St: list_instruction -> environment -> stack -> stack
.

Fixpoint one_step_krivine (state: list_instruction*environment*stack) : option (list_instruction*environment*stack) :=
match state with
| ((Block (Access 0) c), (Env c0 e0 e), s) => Some (c0, e0, s)
| ((Block (Access (S n)) c), (Env c0 e0 e), s) => Some ((Block (Access n) c), e, s)
| ((Block (Push c') c), e, s) => Some (c, e, (St c' e s))
| ((Block Grab c), e, (St c0 e0 s)) => Some (c, (Env c0 e0 e), s)
| _ => None
end.

Fixpoint compilation (t: term) : list_instruction :=
match t with
| var x => Block (Access x) Nil_block
| lambda t => Block Grab (compilation t)
| application t u => Block (Push (compilation u)) (compilation t)
end.

Fixpoint instruction_translation (c: list_instruction) {struct c} : term :=
match c with
| Nil_block => var 42
| Block (Access n) c => var n
| Block (Push c1) c0 => application (instruction_translation c0) (instruction_translation c1)
| Block Grab c => lambda (instruction_translation c)
end.

Fixpoint environment_translation (e: environment) {struct e} : list term :=
match e with
| Nil_env => nil
| Env c0 e0 e => (de_bruijn_substitution_list (environment_translation e0) 0 0 (instruction_translation c0)) :: (environment_translation e)
end
.

Fixpoint state_translation (c: list_instruction) (e: environment) (s: stack) : term :=
match s with
| Nil_stack => de_bruijn_substitution_list (environment_translation e) 0 0 (instruction_translation c)
| (St c0 e0 s) => application (de_bruijn_substitution_list (environment_translation e) 0 0 (instruction_translation c)) (state_translation c0 e0 s)
end.

Theorem translate_inverse_of_compile: forall (t: term), instruction_translation (compilation t) = t.
Proof.
intro.
induction t.
simpl.
trivial.
simpl.
rewrite IHt.
trivial.
simpl.
rewrite IHt1.
rewrite IHt2.
trivial.
Qed.

Fixpoint env_size (e: environment) : nat :=
match e with
| Nil_env => 0
| Env _ _ e => S (env_size e)
end.

Fixpoint correct_env (e: environment) : Prop :=
match e with
| Nil_env => True
| Env c0 e0 e1 => correct_env e0 /\ correct_env e1 /\ closed (S (env_size e0)) (instruction_translation c0)
end.

Fixpoint correct_state (c: list_instruction) (e: environment) (s: stack) : Prop :=
correct_env (Env c e Nil_env) /\ 
match s with
| Nil_stack => True
| St c0 e0 s => correct_state c0 e0 s
end.

Theorem krivine_keeps_correct: forall (s2: stack), forall (c1: list_instruction), forall (e1: environment), forall (s1: stack), forall (c2: list_instruction), forall (e2: environment), correct_state c1 e1 s1 -> one_step_krivine (c1, e1, s1) = Some (c2, e2, s2) -> correct_state c2 e2 s2.
Proof.
intro.
induction s2.
intro.
induction c1.
intros.
simpl in H0.
inversion H0.
induction i.
simpl.
intro.
induction e1.
intros.
induction n; inversion H0.
induction n.
intro.
induction s1.
intros.
split.
split.
inversion H0.
rewrite <- H3.
simpl in H.
elim H. intros. elim H1. intros. elim H5. intros.
trivial.
split.
trivial.
simpl in H.
inversion H0.
rewrite <- H3.
rewrite <- H2.
elim H. intros. elim H1. intros. elim H5. intros. elim H8. intros. trivial.
trivial.
intros.
split.
split.
inversion H0.
split.
trivial.
simpl in H.
elim H. intros. elim H1. intros. elim H3. intros. elim H6. intros.
inversion H0. trivial.
induction s1.
intros.
split.
split.
simpl in H.
inversion H0. rewrite <- H3.
elim H. intros. elim H1. intros. elim H5. intros. elim H8. intros. trivial.
split. trivial.
simpl in H.
inversion H0.
rewrite <- H3.
simpl.
elim H. intros. elim H1. intros. elim H6. intros. omega.
trivial. 
intros.
split.
split.
simpl in H.
inversion H0.
split.
trivial.
simpl in H.
inversion H0.
trivial.
intro. intro. induction s1.
intros.
inversion H0.
intros.
inversion H0.
rewrite H3.
simpl.
rewrite <- H3. simpl. simpl in H. elim H. intros. elim H1. intros. elim H7. intros. rewrite H4 in H5. simpl in H5. elim H5. intros. elim H10. intros. elim H13. intros. 
split. split. split. trivial. split. trivial. trivial. split. trivial. rewrite <- H2. trivial. trivial. 
intros. inversion H0.
intro.
induction c1.
intros. inversion H0.
induction i. induction n. intro. induction e1. intros. inversion H0.
intros. inversion H0.
rewrite H4 in H. simpl in H. inversion H. inversion H1. inversion H6. simpl.
split. split. rewrite <- H3. trivial. split. trivial. inversion H9. rewrite <- H2. rewrite <- H3. trivial.
trivial.
intro. induction e1.
intros. inversion H0.
intros. inversion H0.
rewrite H4 in H. simpl in H. inversion H. inversion H1. inversion H6. simpl.
split. split. rewrite <- H3. inversion H9. trivial. split. trivial. inversion H7. rewrite <- H3. omega. trivial.
assert (forall (s1 : stack) (e1 : environment) (c2 : list_instruction)
  (e2 : environment),
correct_state (Block Grab c1) e1 s1 ->
one_step_krivine (Block Grab c1, e1, s1) = Some (c2, e2, St l e s2) ->
correct_state c2 e2 (St l e s2)).
intro. induction s1.
intros. inversion H0.
intros. inversion H0.
simpl in H. simpl. inversion H. inversion H1. inversion H7. rewrite H4 in H5. simpl in H5. inversion H5. inversion H10. inversion H13.
split. split. split. trivial. split. trivial. trivial. split. trivial. rewrite <- H2. trivial. trivial.
intros.
apply (H s1 e1 c2 e2).
trivial. trivial.
assert (forall (s1 : stack) (e1 : environment) (c2 : list_instruction)
  (e2 : environment),
correct_state (Block (Push l0) c1) e1 s1 ->
one_step_krivine (Block (Push l0) c1, e1, s1) = Some (c2, e2, St l e s2) ->
correct_state c2 e2 (St l e s2)).
intro. induction s1.
intros. inversion H0.
rewrite <- H5. rewrite <- H3. rewrite <- H2.
simpl. simpl in H. inversion H. inversion H1. inversion H9. inversion H11.
split. split. trivial. split. trivial. trivial. split. split. trivial. split. trivial. rewrite <- H4. trivial. trivial.
intros. inversion H0.
rewrite <- H5. rewrite <- H3. rewrite <- H2. rewrite <- H4.
simpl. simpl in H. inversion H. inversion H1. inversion H9. inversion H11. 
split. split. trivial. split. trivial. trivial. split. split. trivial. split. trivial. trivial. trivial.
intros. apply (H s1 e1 c2 e2). trivial. trivial.
Qed.

Theorem krivine_step_is_reduction: forall (c1 c2: list_instruction) (e1 e2: environment) (s1 s2: stack), Some (c2, e2, s2) = one_step_krivine (c1, e1, s1) -> reduce_any (state_translation c1 e1 s1) (state_translation c2 e2 s2).
Proof.
intros.
induction c1. inversion H.
induction i. induction n. induction e1. inversion H.
inversion H. induction s1; simpl; rewrite null_increase; apply red_identity; trivial.
induction e1. inversion H.
inversion H. induction s1. simpl. induction e1_2. simpl.
inversion H in IHe1_2. 
simpl in IHe1_2. apply IHe1_2. 
Qed.

Inductive krivine_steps: list_instruction -> list_instruction -> environment ->
 environment -> stack -> stack -> Prop :=
| zero_step: forall (c1 c2: list_instruction) (e1 e2: environment) (s1 s2: stack), c1 = c2 -> e1 = e2 -> s1 = s2 -> krivine_steps c1 c2 e1 e2 s1 s2
| any_step: forall (c1 c2 c3: list_instruction) (e1 e2 e3: environment) (s1 s2 s3: stack), Some (c2, e2, s2) = one_step_krivine (c1, e1, s1) -> krivine_steps c2 c3 e2 e3 s2 s3 -> krivine_steps c1 c3 e1 e3 s1 s3
.

Lemma krivine_steps_are_reductions : forall (c1 c2: list_instruction) (e1 e2: environment) (s1 s2: stack), krivine_steps c1 c2 e1 e2 s1 s2 -> reduce_any (state_translation c1 e1 s1) (state_translation c2 e2 s2).
Proof.
intros. induction H.
rewrite H. rewrite H0. rewrite H1. apply red_identity. trivial.
apply (red_trans _ (state_translation c2 e2 s2)). apply krivine_step_is_reduction. trivial. trivial.
Qed.

Theorem krivine_steps_keep_correct : forall (c1 c2: list_instruction) (e1 e2: environment) (s1 s2: stack), krivine_steps c1 c2 e1 e2 s1 s2 -> correct_state c1 e1 s1 -> correct_state c2 e2 s2.
Proof.
intros. induction H. rewrite H in H0. rewrite H1 in H0. rewrite H2 in H0. trivial.
apply IHkrivine_steps.
apply (krivine_keeps_correct s2 c1 e1 s1 c2 e2). trivial. rewrite H. trivial.
Qed.

Theorem correct_after_compilation_and_krivine : forall (t: term) (c: list_instruction) (e: environment) (s: stack), closed 1 t -> krivine_steps (compilation t) c Nil_env e Nil_stack s -> correct_state c e s.
Proof.
intros.
apply (krivine_steps_keep_correct (compilation t) c Nil_env e Nil_stack s). trivial.
simpl. split. split. trivial. split. trivial. rewrite translate_inverse_of_compile. trivial. trivial.
Qed.
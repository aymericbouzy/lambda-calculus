Require Import Arith.
Require Import List.
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
simpl. intros. omega. 
intros. simpl. simpl in H. apply IHt. trivial.
intros. simpl. inversion H. split.
apply IHt1. trivial.
apply IHt2. trivial.
Qed.

Proposition closed_implication_generalized : forall (p n: nat) (t: term), closed n t -> n <= p -> closed p t.
Proof.
intro. induction p. intros.
assert (0 = n). omega. rewrite H1. trivial.
intros. assert (n = S p \/ n < S p). omega. case H1. intros. rewrite <- H2. trivial.
intros. apply closed_implication. apply (IHp n). trivial. omega.
Qed.

Proposition closed_list_implication : forall (l: list term) (n: nat), closed_list n l -> closed_list (S n) l.
Proof.
intro. induction l.
intros. simpl. trivial.
intros. simpl. inversion H. split.
apply closed_implication. trivial.
apply IHl. trivial.
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
| var x => gt_nat_branch p x (var x) (var (x + n))
| lambda t => lambda (increase_var t n (S p))
| application t u => application (increase_var t n p) (increase_var u n p)
end.

Proposition increase_var_keeps_close : forall (a: term) (p n m k: nat), closed m a -> k >= n + p -> k >= m + n -> closed k (increase_var a n p).
Proof.
intro. induction a.
intros. simpl. assert (p > n \/ p <= n). omega. case H2.
intro. rewrite gt_branch_real_gt. simpl. omega. omega.
intro. rewrite leq_branch_real_leq. simpl. simpl in H. omega. omega.
intros. simpl.  apply (IHa _ _ (S m)). simpl in H. trivial. omega. omega.
intros. simpl. inversion H. split. apply (IHa1 _ _ m). trivial. omega. omega. apply (IHa2 _ _ m). trivial. omega. omega.
Qed.

Proposition null_increase : forall (s: term), forall (p: nat), increase_var s 0 p = s.
Proof.
intro. induction s.
intro.
simpl. assert (n + 0 = n). omega. rewrite H. rewrite gt_unconditionnal_branch. trivial.
intro. simpl. rewrite IHs. trivial.
intro. simpl. rewrite IHs1. rewrite IHs2. trivial.
Qed.

Proposition no_change_increase : forall (s: term) (n p: nat), closed p s -> increase_var s n p = s.
Proof.
intro. induction s.
intros. simpl. simpl in H. rewrite gt_branch_real_gt. trivial. trivial.
intros. simpl. rewrite (IHs n (S p)). trivial. simpl in H. trivial.
intros. simpl. inversion H. rewrite IHs1, IHs2. trivial. trivial. trivial. 
Qed.

Fixpoint de_bruijn_aux (x: nat) (l: list term) (p: nat): term :=
match l with
  | nil => var x
  | s :: r => eq_nat_branch x p (increase_var s p 0) (de_bruijn_aux x r (S p))
end.

Proposition de_bruijn_aux_terminate : forall (l: list term), forall (x p: nat), x < p -> de_bruijn_aux x l p = var x.
Proof.
intro. induction l.
intros. simpl. trivial.
intros. simpl. rewrite IHl. rewrite neq_branch_real_neq. trivial. omega. omega.
Qed.

Proposition de_bruijn_aux_keeps_close : forall (l: list term), forall (x i p k: nat), closed_list i l -> k >= S i + x -> closed k (de_bruijn_aux x l p).
Proof.
intro. induction l.
intros. simpl. omega.
intros. simpl. assert (x = p \/ x <> p). omega. case H1.
intro. rewrite eq_branch_real_eq. simpl in IHl. apply (increase_var_keeps_close _ _ _ (S i)). apply closed_implication. inversion H. trivial. omega. omega. trivial.
intro. rewrite neq_branch_real_neq. simpl. apply (IHl _ i). inversion H. trivial. trivial. trivial.
Qed.

(*Proposition de_bruijn_aux_invariant : forall (l: list term) (n p: nat), de_bruijn_aux (S n) l (S p) = de_bruijn_aux n l p.
Proof.
intro. induction l. intros. simpl.

Qed.*)

Fixpoint de_bruijn_substitution_list (l: list term) (p: nat) (t: term) : term :=
match t with
| var x => de_bruijn_aux x l p
| lambda t => lambda (de_bruijn_substitution_list l (S p) t)
| application t u => application (de_bruijn_substitution_list l p t) (de_bruijn_substitution_list l p u)
end.

Proposition nil_substitution : forall t:term, forall p:nat, (de_bruijn_substitution_list nil p t) = t.
Proof.
intro. induction t.
intros. simpl. trivial. 
intros. simpl. rewrite IHt. trivial.
intros. simpl. rewrite IHt1, IHt2. trivial.
Qed.

Proposition missing_variable_substitution : forall l: list term, forall t:term, forall p:nat, closed p t -> (de_bruijn_substitution_list l p t) = t.
Proof.
intro. induction l. 
intros. rewrite nil_substitution. trivial.
intro. induction t.
intros. simpl. rewrite neq_branch_real_neq. rewrite de_bruijn_aux_terminate. trivial.
inversion H. omega. omega. inversion H. omega. omega.
intros. simpl. rewrite (IHt (S p)). trivial. simpl in H. trivial.
intros. simpl. rewrite IHt1, IHt2. trivial. simpl in H. case H.
intros. trivial. simpl in H. case H.
intros. trivial.
Qed.

Fixpoint absent_var (n: nat) (t: term) : Prop :=
match t with
| var m => n <> m
| lambda t => absent_var (S n) t
| application t u => absent_var n t /\ absent_var n u
end.

Lemma absent_vars_after_increase : forall (t: term) (n p i: nat), i >= n -> i < n + p -> absent_var i (increase_var t p n).
Proof.
intro. induction t.
intros. simpl. assert (n0 > n \/ n0 <= n). omega. elim H1.
intro. rewrite gt_branch_real_gt. simpl. omega. trivial.
intro. rewrite leq_branch_real_leq. simpl. omega. trivial.
simpl. intros. apply IHt. omega. omega.
intros. simpl. split. apply IHt1. trivial. trivial. apply IHt2. trivial. trivial.
Qed.

Lemma substitution_is_identity_when_absent_var : forall (t u: term) (n: nat), absent_var n t -> de_bruijn_substitution_list (u :: nil) n t = t.
Proof.
intro. induction t.
intros. simpl. simpl in H. rewrite neq_branch_real_neq. trivial. omega.
intros. simpl. rewrite IHt. trivial. simpl in H. trivial.
intros. simpl. inversion H. rewrite IHt1, IHt2. trivial. trivial. trivial.
Qed.

Lemma absent_var_after_aux : forall (l: list term) (n p k m: nat), k >= p -> n > k -> closed_list p l -> absent_var k (de_bruijn_aux n l m).
Proof.
intro. induction l.
intros. simpl. omega.
intros. simpl. assert (n = m \/ n <> m). omega. case H2.
intro. rewrite eq_branch_real_eq. apply absent_vars_after_increase. omega. omega. trivial.
intro. rewrite neq_branch_real_neq. apply (IHl _ p). trivial. trivial. inversion H1. trivial. trivial.
Qed.

Proposition successive_substitutions : forall l:list term, forall t:term, forall p: nat, forall u:term, closed_list p (u :: l) -> de_bruijn_substitution_list (u :: nil) p (de_bruijn_substitution_list l (S p) t) = de_bruijn_substitution_list (u :: l) p t.
Proof.
intro.
induction l.
intros. rewrite nil_substitution. trivial.
intro. induction t.
intros. simpl.
assert (n = p \/ n = S p \/ n > S p \/ n < p). omega. case H0.
intro. rewrite (eq_branch_real_eq n p). rewrite neq_branch_real_neq. rewrite de_bruijn_aux_terminate. simpl. rewrite eq_branch_real_eq. trivial. trivial. omega. omega. trivial.
intro. case H1. intro. rewrite (eq_branch_real_eq n (S p)). rewrite neq_branch_real_neq. rewrite substitution_is_identity_when_absent_var. trivial. apply absent_vars_after_increase. omega. omega. omega. trivial.
intro. rewrite neq_branch_real_neq. rewrite neq_branch_real_neq.
case H2. intro. inversion H. inversion H5. rewrite substitution_is_identity_when_absent_var. trivial.
apply (absent_var_after_aux l _ p). omega. omega. trivial.
intro. rewrite de_bruijn_aux_terminate. simpl. rewrite neq_branch_real_neq. trivial. omega. omega. omega. omega.
intros. simpl. rewrite IHt. trivial. apply closed_list_implication. trivial.
intros. simpl. rewrite IHt1, IHt2. trivial. trivial. trivial.
Qed.
(*
Proposition whatever : forall (l1 l2: list term) (t1 t2 t3: term) (n: nat), de_bruijn_substitution_list (de_bruijn_substitution_list l2 n t2 :: l1) n t1 = de_bruijn_substitution_list ((de_bruijn_substitution_list l2 n t2) :: nil) n (de_bruijn_substitution_list l1 (S n) t1).
Proof.
intros. induction l2.
rewrite nil_substitution.
Qed.
*)
Inductive reduce_one: term -> term -> Prop :=
  | red_app_left: forall t u v: term, reduce_one t u -> reduce_one (application t v) (application u v)
  | red_app_right: forall t u v: term, reduce_one u v -> reduce_one (application t u) (application t v)
  | red_lambda: forall t u: term, reduce_one t u -> reduce_one (lambda t) (lambda u)
  | red_beta: forall t u v: term, t = de_bruijn_substitution_list (v :: nil) 0 u -> reduce_one (application (lambda u) v) t
.

Inductive reduce_any: term -> term -> Prop :=
  | red_identity: forall t u: term, t = u -> reduce_any t u
  | red_trans: forall t u v: term, reduce_one t u -> reduce_any u v -> reduce_any t v
.

Proposition reduce_one_is_any : forall t u: term, reduce_one t u -> reduce_any t u.
Proof.
intros. apply (red_trans t u u). exact H. constructor. trivial.
Qed.

Proposition reduce_any_app_left : forall t u v: term, reduce_any t u -> reduce_any (application t v) (application u v).
Proof.
intros. induction H. apply red_identity. rewrite H. trivial. 
apply (red_trans (application t v) (application u v) (application v0 v)). constructor. trivial. trivial.
Qed.

Proposition reduce_any_app_right : forall t u v: term, reduce_any u v -> reduce_any (application t u) (application t v).
Proof.
intros. induction H.
apply red_identity. rewrite H. trivial.
apply (red_trans (application t t0) (application t u) (application t v)). constructor. trivial. trivial.
Qed.

Proposition reduce_any_lambda : forall t u v: term, reduce_any t u -> reduce_any (lambda t) (lambda u).
Proof.
intros. induction H.
apply red_identity. rewrite H. trivial.
apply (red_trans (lambda t) (lambda u) (lambda v0)). constructor. trivial. trivial.
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
| Env c0 e0 e => (de_bruijn_substitution_list (environment_translation e0) 0 (instruction_translation c0)) :: (environment_translation e)
end
.

Fixpoint state_translation (c: list_instruction) (e: environment) (s: stack) : term :=
match s with
| Nil_stack => de_bruijn_substitution_list (environment_translation e) 0 (instruction_translation c)
| (St c0 e0 s) => application (de_bruijn_substitution_list (environment_translation e) 0 (instruction_translation c)) (state_translation c0 e0 s)
end.

Theorem translate_inverse_of_compile: forall (t: term), instruction_translation (compilation t) = t.
Proof.
intro. induction t.
simpl. trivial.
simpl. rewrite IHt. trivial.
simpl. rewrite IHt1, IHt2. trivial.
Qed.

Fixpoint env_size (e: environment) : nat :=
match e with
| Nil_env => 0
| Env _ _ e => S (env_size e)
end.

Fixpoint correct_env (e: environment) : Prop :=
match e with
| Nil_env => True
| Env c0 e0 e1 => correct_env e0 /\ correct_env e1 /\ closed (env_size e0) (instruction_translation c0)
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

Proposition closed_after_substitutions : forall (l: list term) (t: term) (k j p m: nat), closed j t -> closed_list m l -> m + j <= k -> closed k (de_bruijn_substitution_list l p t).
Proof.
intro. induction l.
intros. rewrite nil_substitution. apply (closed_implication_generalized _ j). trivial. omega.
intro. induction t. intros.
assert (n = p \/ n < p \/ n > p). omega. induction H2. simpl. rewrite eq_branch_real_eq. inversion H0. simpl in H. apply (increase_var_keeps_close _ _ _ m). trivial. omega. omega. omega.
induction H2.
simpl. rewrite neq_branch_real_neq. apply (de_bruijn_aux_keeps_close _ _ m). inversion H0. trivial. simpl in H. omega. omega.
simpl. rewrite neq_branch_real_neq. inversion H. assert (de_bruijn_aux n l (S p) = de_bruijn_substitution_list l (S p) (var n)). simpl. trivial. rewrite H4. apply (IHl _ _ j _ m).
inversion H. simpl. omega. simpl. omega. inversion H0. trivial. trivial.
apply (de_bruijn_aux_keeps_close _ _ m). inversion H0. trivial. omega. omega. 
intros. simpl. apply (IHt _ (S j) _ m). simpl in H. trivial. trivial. omega.
intros. simpl. inversion H. split. 
apply (IHt1 _ j _ m). trivial. trivial. trivial.
apply (IHt2 _ j _ m). trivial. trivial. trivial.
Qed.
(*
Proposition correct_implies_closed : forall (s: stack) (c: list_instruction) (e: environment), correct_state c e s -> closed 0 (state_translation c e s).
Proof.
intro. induction s.
intros. inversion H. inversion H0. inversion H3. induction e.
induction c.
inversion H5.
simpl. rewrite nil_substitution.
induction i. inversion H5.
simpl in H5. simpl. trivial.
simpl in H5. simpl. trivial.
simpl. simpl in H5. apply (closed_after_substitutions _ _ _ 0 _ 0). admit.
split. apply (closed_after_substitutions _ _ _ 0 _ 0). inversion H2.
Qed.

Proposition krivine_grab_is_reduction: forall (s1: stack) (e1: environment) (c1 c2: list_instruction) (e2: environment) (s2: stack), 
reduce_one (state_translation c1 e1 s1) (state_translation c2 e2 s2) \/ (state_translation c2 e2 s2) = (state_translation c1 e1 s1) ->
Some (c2, e2, s2) = one_step_krivine (Block Grab c1, e1, s1) -> 
correct_state (Block Grab c1) e1 s1 -> 
reduce_one (state_translation (Block Grab c1) e1 s1) (state_translation c2 e2 s2) \/ (state_translation c2 e2 s2) = (state_translation (Block Grab c1) e1 s1).
Proof.
intro. induction s1.
intros. inversion H.
intros. inversion H. simpl. simpl in H. inversion H. left.
induction s2. inversion H0. simpl. inversion H1. inversion H5. inversion H8. simpl in H10.



Qed.

Proposition krivine_push_is_reduction: forall (e1: environment) (c0 c1 c2: list_instruction) (e2: environment) (s1 s2: stack), 
Some (c2, e2, s2) = one_step_krivine (Block (Push c0) c1, e1, s1) -> 
correct_state (Block (Push c0) c1) e1 s1 -> 
reduce_one (state_translation c2 e2 s2) (state_translation (Block (Push c0) c1) e1 s1) \/ (state_translation c2 e2 s2) = (state_translation (Block (Push c0) c1) e1 s1).
Proof.
intros. inversion H. simpl. induction e1.
simpl. rewrite nil_substitution.
induction s1. simpl. rewrite nil_substitution. rewrite nil_substitution. right. trivial.
simpl. rewrite nil_substitution. rewrite nil_substitution. 
inversion H0. inversion H1. inversion H7. inversion H9. left. apply  

intro. induction e1.
intros. inversion H. simpl. rewrite nil_substitution. induction s1.
simpl. rewrite nil_substitution. rewrite nil_substitution. inversion H0. inversion H1. inversion H7. simpl in H9.
induction c1. simpl. inversion H9. induction i. simpl in H9. inversion H9. simpl.
simpl. 
assert (instruction_translation c1 = de_bruijn_substitution_list ((instruction_translation c0) :: nil) 0 (instruction_translation c1)).
rewrite missing_variable_substitution. trivial. simpl in H9. simpl. trivial.
assert (reduce_one
  (application (lambda (instruction_translation c1))
     (instruction_translation c0)) (de_bruijn_substitution_list ((instruction_translation c0) :: nil) 0 (lambda (instruction_translation c1))) -> reduce_one
  (application (lambda (instruction_translation c1))
     (instruction_translation c0)) (lambda (instruction_translation c1))).
rewrite <- H10. trivial. apply H11.
apply red_beta.
Qed.

Proposition krivine_access_ 0_is_identity: forall , state_translation ((Block (Access 0) c), (Env c0 e0 e), s)
*)

Lemma nil_env_size : forall (e: environment), 0 = env_size e -> e = Nil_env.
Proof.
intros. induction e.
trivial. inversion H.
Qed.
(*
Lemma krivine_access_0_is_reduction : forall (e1: environment) (s1: stack) (e2 : environment) (s2 : stack) (c1 c2 : list_instruction), 
Some (c2, e2, s2) = one_step_krivine (Block (Access 0) c1, e1, s1) -> 
correct_state (Block (Access 0) c1) e1 s1->
(Some (c2, e2, s2) = one_step_krivine (c1, e1, s1) ->
       correct_state c1 e1 s1 ->
       reduce_one (state_translation c1 e1 s1) (state_translation c2 e2 s2) \/
       state_translation c1 e1 s1 = state_translation c2 e2 s2) ->
reduce_one (state_translation (Block (Access 0) c1) e1 s1)
  (state_translation c2 e2 s2) \/
state_translation (Block (Access 0) c1) e1 s1 = state_translation c2 e2 s2.
Proof.
intro. induction e1. intros. inversion H.
intro. induction s1.
intro. induction e2. intros. inversion H. inversion H0. inversion H2. inversion H8.  inversion H10.
assert (e1_2 = Nil_env). apply nil_env_size. trivial. inversion H11. simpl. rewrite nil_substitution. rewrite nil_increase.
Qed.

*)

Theorem krivine_step_is_reduction: forall (c1 c2: list_instruction) (e1 e2: environment) (s1 s2: stack), Some (c2, e2, s2) = one_step_krivine (c1, e1, s1) -> correct_state c1 e1 s1 -> reduce_one (state_translation c1 e1 s1) (state_translation c2 e2 s2) \/ state_translation c1 e1 s1 = state_translation c2 e2 s2.
Proof.
intros. induction c1.
inversion H.
inversion H. induction i.
induction n.
admit.
admit.
admit.
admit.
Qed.

(*
intro. induction c1. intros. inversion H.
assert (forall (e1: environment) (s1: stack) (e2 : environment) (s2 : stack) (c2 : list_instruction),
Some (c2, e2, s2) = one_step_krivine (Block i c1, e1, s1) ->
correct_state (Block i c1) e1 s1 ->
reduce_one (state_translation (Block i c1) e1 s1)
  (state_translation c2 e2 s2) \/
state_translation (Block i c1) e1 s1 = state_translation c2 e2 s2).
induction i. induction n. intro. induction e1. intros. inversion H.
intros. inversion H. simpl. induction s1; simpl; rewrite null_increase; right; trivial.
intro. induction e1. intros. inversion H.
intro. induction s1. intro. induction e2. intros. assert (correct_state c2 Nil_env s2).
apply (krivine_keeps_correct _ (Block (Access (S n)) c1) (Env l e1_1 e1_2) Nil_stack). trivial. rewrite H. trivial.
inversion H. simpl. inversion H in H1. simpl in H1. inversion H1. inversion H2. inversion H11. inversion H13.
intro. induction s2. intros. inversion H. simpl. induction n. rewrite eq_branch_real_eq. rewrite eq_branch_real_eq. rewrite null_increase. rewrite no_change_increase. right. trivial.
inversion H0. 


Qed.
*)

Inductive krivine_steps: list_instruction -> list_instruction -> environment ->
 environment -> stack -> stack -> Prop :=
| zero_step: forall (c1 c2: list_instruction) (e1 e2: environment) (s1 s2: stack), c1 = c2 -> e1 = e2 -> s1 = s2 -> krivine_steps c1 c2 e1 e2 s1 s2
| any_step: forall (c1 c2 c3: list_instruction) (e1 e2 e3: environment) (s1 s2 s3: stack), Some (c2, e2, s2) = one_step_krivine (c1, e1, s1) -> krivine_steps c2 c3 e2 e3 s2 s3 -> krivine_steps c1 c3 e1 e3 s1 s3
.

Lemma krivine_steps_are_reductions : forall (c1 c2: list_instruction) (e1 e2: environment) (s1 s2: stack), krivine_steps c1 c2 e1 e2 s1 s2 -> correct_state c1 e1 s1 -> reduce_any (state_translation c1 e1 s1) (state_translation c2 e2 s2).
Proof.
intros. induction H.
rewrite H, H1, H2. apply red_identity. trivial.
assert (reduce_one (state_translation c1 e1 s1) (state_translation c2 e2 s2) \/ state_translation c1 e1 s1 = state_translation c2 e2 s2).
apply krivine_step_is_reduction. trivial. trivial.
inversion H1. elim H2.
intro. apply (red_trans _ (state_translation c2 e2 s2)). trivial. apply IHkrivine_steps. apply (krivine_keeps_correct _ c1 e1 s1). trivial. rewrite H. trivial.
intro. rewrite H12. apply IHkrivine_steps. apply (krivine_keeps_correct _ c1 e1 s1). trivial. rewrite H. trivial. 
elim H2.
intro. apply (red_trans _ (state_translation c2 e2 s2)). trivial. apply IHkrivine_steps. apply (krivine_keeps_correct _ c1 e1 s1). trivial. rewrite H. trivial.
intro. rewrite H11. apply IHkrivine_steps. apply (krivine_keeps_correct _ c1 e1 s1). trivial. rewrite H. trivial. 
Qed.

Theorem krivine_steps_keep_correct : forall (c1 c2: list_instruction) (e1 e2: environment) (s1 s2: stack), krivine_steps c1 c2 e1 e2 s1 s2 -> correct_state c1 e1 s1 -> correct_state c2 e2 s2.
Proof.
intros. induction H. rewrite H in H0. rewrite H1 in H0. rewrite H2 in H0. trivial.
apply IHkrivine_steps.
apply (krivine_keeps_correct s2 c1 e1 s1 c2 e2). trivial. rewrite H. trivial.
Qed.

Theorem correct_after_compilation_and_krivine : forall (t: term) (c: list_instruction) (e: environment) (s: stack), closed 0 t -> krivine_steps (compilation t) c Nil_env e Nil_stack s -> correct_state c e s.
Proof.
intros.
apply (krivine_steps_keep_correct (compilation t) c Nil_env e Nil_stack s). trivial.
simpl. split. split. trivial. split. trivial. rewrite translate_inverse_of_compile. trivial. trivial.
Qed.
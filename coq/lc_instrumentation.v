From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
Import ListNotations.


(* based on STLCRef chapter of Software Foundations *)

(* terms *)
Inductive tm  : Type :=
  | var    : string -> tm
  | app    : tm -> tm -> tm
  | abs    : string -> tm -> tm
  | const  : nat -> tm
  | scc    : tm -> tm
  | prd    : tm -> tm
  | test0  : tm -> tm -> tm -> tm
  | unit   : tm
  | ref    : tm -> tm
  | deref  : tm -> tm
  | assign : tm -> tm -> tm
  | loc    : nat -> tm
  | error  : string -> tm.


(* values *)
Inductive value : tm -> Prop :=
  | v_abs  : forall x t,
      value (abs x t)
  | v_nat : forall n,
      value (const n)
  | v_unit :
      value unit
  | v_loc : forall l,
      value (loc l).
Hint Constructors value.

Fixpoint valueb (t : tm) : bool :=
  match t with
  | abs _ _ | const _ | unit | loc _ => true
  | _ => false
  end.

Theorem valueb_sound : forall t, value t -> (valueb t = true).
Proof.
  intros.
  inversion H; simpl; reflexivity.
Qed.

Theorem valueb_complete : forall t, (valueb t = true) -> value t.
Proof.
  intros.
  destruct t; simpl; try discriminate; auto.
Qed.

(* substitution. NB ignores free-variable issues. *)
Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  | var x'       =>
      if String.eqb x x' then s else t
  | app t1 t2    =>
      app (subst x s t1) (subst x s t2)
  | abs x' t1  =>
      if String.eqb x x' then t else abs x' (subst x s t1)
  | const n        =>
      t
  | scc t1      =>
      scc (subst x s t1)
  | prd t1      =>
      prd (subst x s t1)
  | test0 t1 t2 t3 =>
      test0 (subst x s t1) (subst x s t2) (subst x s t3)
  | unit         =>
      t
  | ref t1       =>
      ref (subst x s t1)
  | deref t1     =>
      deref (subst x s t1)
  | assign t1 t2 =>
      assign (subst x s t1) (subst x s t2)
  | loc _        =>
      t
  | error _      => t 
  end.
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).


(* equivalent to `t1; t2` *)
Definition tseq t1 t2 :=
  app (abs "x" t2) t1.


(* store-based substitution semantics *)

(* stores *)
Definition store := list tm.

Definition store_lookup (n:nat) (st:store) :=
  nth n st unit.

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil => nil
  | h :: t =>
    match n with
    | O => x :: t
    | S n' => h :: replace n' x t
    end
  end.


Reserved Notation "t1 '/' st1 '-->' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Import ListNotations.

Inductive step : tm * store -> tm * store -> Prop :=
  | ST_AppAbs : forall x t12 v2 st,
         value v2 ->
         app (abs x t12) v2 / st --> [x:=v2]t12 / st
  | ST_App1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         app t1 t2 / st --> app t1' t2 / st'
  | ST_App2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         app v1 t2 / st --> app v1 t2'/ st'
  | ST_SuccNat : forall n st,
         scc (const n) / st --> const (S n) / st
  | ST_Succ : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         scc t1 / st --> scc t1' / st'
  | ST_PredNat : forall n st,
         prd (const n) / st --> const (pred n) / st
  | ST_Pred : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         prd t1 / st --> prd t1' / st'
  | ST_If0 : forall t1 t1' t2 t3 st st',
         t1 / st --> t1' / st' ->
         test0 t1 t2 t3 / st --> test0 t1' t2 t3 / st'
  | ST_If0_Zero : forall t2 t3 st,
         test0 (const 0) t2 t3 / st --> t2 / st
  | ST_If0_Nonzero : forall n t2 t3 st,
         test0 (const (S n)) t2 t3 / st --> t3 / st
  | ST_RefValue : forall v1 st,
         value v1 ->
         ref v1 / st --> loc (length st) / (st ++ v1::nil)
  | ST_Ref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         ref t1 /  st --> ref t1' /  st'
  | ST_DerefLoc : forall st l,
         l < length st ->
         deref (loc l) / st --> store_lookup l st / st
  | ST_Deref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         deref t1 / st --> deref t1' / st'
  | ST_Assign : forall v2 l st,
         value v2 ->
         l < length st ->
         assign (loc l) v2 / st --> unit / replace l v2 st
  | ST_Assign1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         assign t1 t2 / st --> assign t1' t2 / st'
  | ST_Assign2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         assign v1 t2 / st --> assign v1 t2' / st'

where "t1 '/' st1 '-->' t2 '/' st2" := (step (t1,st1) (t2,st2)).

Definition relation (X : Type) := X -> X -> Prop.
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Hint Constructors step.
Definition multistep := (multi step).
Notation "t1 '/' st '-->*' t2 '/' st'" :=
               (multistep (t1,st) (t2,st'))
               (at level 40, st at level 39, t2 at level 39).


Fixpoint stepfn (t : tm) (s : store) : tm * store :=
  match t with
  | var _ | unit | const _ | abs _ _ | loc _ | error _ => (t,s)
  | app fn arg =>
    if (valueb fn) then
      if (valueb arg) then
        match fn with
        | abs x body => (subst x arg body, s)
        | _ => (error "attempt to apply non-fn", s)
        end
      else
        let (arg',s') := stepfn arg s in
        (app fn arg', s')
    else
      let (fn',s') := stepfn fn s in
      (app fn' arg, s')
  | scc t1 =>
    if (valueb t1) then
      match t1 with
      | const n => (const (S n), s)
      | _ => (error "scc of non nat", s)
      end
    else
      let (t1', s') := stepfn t1 s in
      (scc t1', s')
  | prd t1 =>
    if (valueb t1) then
      match t1 with
      | const n => (const (pred n), s)
      | _ => (error "prd of non nat", s)
      end
    else
      let (t1', s') := stepfn t1 s in
      (prd t1', s')
  | test0 cond yes no =>
    if (valueb cond) then
      match cond with
      | const 0 => (yes, s)
      | const (S n) => (no, s)
      | _ => (error "test0 of non nat", s)
      end
    else
      let (cond', s') := stepfn cond s in
      (test0 cond' yes no, s')
  | ref t1 =>
    if (valueb t1) then
      (loc (length s), (s ++ t1::nil))
    else
      let (t1', s') := stepfn t1 s in
      (ref t1', s')
  | deref t1 =>
    if (valueb t1) then
      match t1 with
      | loc l =>
        if Nat.ltb l (length s) then
          (store_lookup l s, s)
        else (error "attempt to deref invalid loc", s)
      | _ => (error "attempt to deref non-loc", s)
      end
    else
      let (t1', s') := stepfn t1 s in
      (deref t1', s')
  | assign t1 t2 =>
    if (valueb t1) then
      if (valueb t2) then
        match t1 with
        | loc l =>
          if  Nat.ltb l (length s) then
            (unit, replace l t2 s)
          else (error "attempt to assign invalid loc", s)
        | _ => (error "attempt to assign non-loc", s)
        end
      else
        let (t2', s') := stepfn t2 s in
        (assign t1 t2', s')
    else
      let (t1', s') := stepfn t1 s in
      (assign t1' t2, s')   
  end.


Lemma stepfn_deterministic : forall t1 s1 t2 s2 t2' s2',
    t1 / s1 --> t2 / s2 ->
    t1 / s1 --> t2' / s2' ->
    t2 = t2' /\ s2 = s2'.
Proof.
  intros t1.
  induction t1; intros.
  - inversion H.
  - inversion H; subst.
    + specialize H2.
Admitted.

Lemma step_not_value : forall t s t' s',
    t / s --> t' / s' -> ~(value t).
Proof.
  intros t1.
  destruct t1; intros; try inversion H.
  - 
Admitted.
  
 
Lemma not_valueb_sound : forall t, ~(value t) -> valueb t = false.
Proof.
  intros.
  destruct t; simpl; try reflexivity; try contradict H.
  - apply (v_abs s t).
  - apply (v_nat n).
  - apply (v_unit).
  - apply (v_loc n).
Qed.

Theorem stepfn_sound : forall t1 s1 t2 s2,
    t1 / s1 --> t2 / s2 -> stepfn t1 s1 = (t2, s2).
Proof.
  intros t1.
  induction t1; intros.
  - inversion H.
  - simpl.
    inversion H; subst.
    + apply valueb_sound in H1.
      rewrite H1.
      simpl.
      reflexivity.
    + specialize (not_valueb_sound t1_1).
      intro H2.
      specialize (step_not_value t1_1 s1 t1' s2 H1) as NV.
      specialize (H2 NV).
      rewrite H2.
      specialize (IHt1_1 s1 t1' s2).
      rewrite IHt1_1.
      reflexivity.
      assumption.
    + apply valueb_sound in H2.
      rewrite H2.
      specialize (step_not_value t1_2 s1 t2' s2 H6) as NV.
      specialize (not_valueb_sound t1_2).
      intro H3.
      specialize (H3 NV).
      rewrite H3.
      specialize (IHt1_2 s1 t2' s2).
      rewrite IHt1_2.
      reflexivity.
      assumption.
  - inversion H.
  - inversion H.
  - simpl.
    inversion H; subst.
    + cbn. reflexivity.
    + specialize (step_not_value t1 s1 t1' s2 H1) as NV.
      specialize (not_valueb_sound t1).
      intro H2.
      specialize (H2 NV).
      rewrite H2.
      specialize (IHt1 s1 t1' s2).
      rewrite IHt1.
      reflexivity.
      assumption.
  - simpl.
    inversion H; subst.
    + cbn. reflexivity.
    + specialize (step_not_value t1 s1 t1' s2 H1) as NV.
      specialize (not_valueb_sound t1).
      intro H2.
      specialize (H2 NV).
      rewrite H2.
      specialize (IHt1 s1 t1' s2).
      rewrite IHt1.
      reflexivity.
      assumption.
  - inversion H; subst; simpl.
    + specialize (step_not_value t1_1 s1 t1' s2 H1) as NV.
      specialize (not_valueb_sound t1_1).
      intro H2.
      specialize (H2 NV).
      rewrite H2.
      specialize (IHt1_1 s1 t1' s2 H1).
      rewrite IHt1_1.
      reflexivity.
    + reflexivity.
    + reflexivity.
  - inversion H.
  - inversion H; subst; simpl.
    + apply valueb_sound in H1.
      rewrite H1.
      reflexivity.
    + specialize (step_not_value t1 s1 t1' s2 H1) as NV.
      specialize (not_valueb_sound t1).
      intro H2.
      specialize (H2 NV).
      rewrite H2.
      specialize (IHt1 s1 t1' s2 H1).
      rewrite IHt1.
      reflexivity.
  - inversion H; subst; simpl.
    + apply Nat.ltb_lt in H1.
      rewrite H1.
      reflexivity.
    + specialize (step_not_value t1 s1 t1' s2 H1) as NV.
      specialize (not_valueb_sound t1).
      intro H2.
      specialize (H2 NV).
      rewrite H2.
      specialize (IHt1 s1 t1' s2 H1).
      rewrite IHt1.
      reflexivity.
  - inversion H; subst; simpl.
    + apply valueb_sound in H2.
      rewrite H2.
      apply Nat.ltb_lt in H6.
      rewrite H6.
      reflexivity.
    + specialize (step_not_value t1_1 s1 t1' s2 H1) as NV.
      specialize (not_valueb_sound t1_1).
      intro H2.
      specialize (H2 NV).
      rewrite H2.
      specialize (IHt1_1 s1 t1' s2 H1).
      rewrite IHt1_1.
      reflexivity.
    + apply valueb_sound in H2.
      rewrite H2.
      specialize (step_not_value t1_2 s1 t2' s2 H6) as NV.
      specialize (not_valueb_sound t1_2).
      intro H3.
      specialize (H3 NV).
      rewrite H3.
      specialize (IHt1_2 s1 t2' s2 H6).
      rewrite IHt1_2.
      reflexivity.
  - inversion H.
  - inversion H.
Qed.

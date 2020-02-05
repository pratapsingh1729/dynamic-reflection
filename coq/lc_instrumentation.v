From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Decidable.
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


Lemma step_not_value : forall t s t' s',
    t / s --> t' / s' -> ~(value t).
Proof.
  intros; inversion H; subst; intuition; inversion H0.
Qed.
 
Lemma not_valueb_sound : forall t, ~(value t) -> valueb t = false.
Proof.
  intros.
  destruct t; simpl; try reflexivity; try contradict H; constructor.
Qed.
  
Theorem stepfn_sound : forall t1 s1 t2 s2,
    t1 / s1 --> t2 / s2 -> stepfn t1 s1 = (t2, s2).
Proof.
  intros t1.
  induction t1; intros; inversion H; subst; simpl.
  - apply valueb_sound in H1.
    rewrite H1.
    simpl.
    reflexivity.
  - specialize (not_valueb_sound t1_1) as VBS;
    specialize (step_not_value t1_1 s1 t1' s2 H1) as NV;
    specialize (VBS NV);
    rewrite VBS.
    specialize (IHt1_1 s1 t1' s2).
    rewrite IHt1_1.
    reflexivity.
    assumption.
  - apply valueb_sound in H2.
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
  - cbn. reflexivity.
  - specialize (step_not_value t1 s1 t1' s2 H1) as NV.
    specialize (not_valueb_sound t1).
    intro H2.
    specialize (H2 NV).
    rewrite H2.
    specialize (IHt1 s1 t1' s2).
    rewrite IHt1.
    reflexivity.
    assumption.
  - cbn. reflexivity.
  - specialize (step_not_value t1 s1 t1' s2 H1) as NV.
    specialize (not_valueb_sound t1).
    intro H2.
    specialize (H2 NV).
    rewrite H2.
    specialize (IHt1 s1 t1' s2).
    rewrite IHt1.
    reflexivity.
    assumption.
  - specialize (step_not_value t1_1 s1 t1' s2 H1) as NV.
    specialize (not_valueb_sound t1_1).
    intro H2.
    specialize (H2 NV).
    rewrite H2.
    specialize (IHt1_1 s1 t1' s2 H1).
    rewrite IHt1_1.
    reflexivity.
  - reflexivity.
  - reflexivity.
  - apply valueb_sound in H1.
    rewrite H1.
    reflexivity.
  - specialize (step_not_value t1 s1 t1' s2 H1) as NV.
    specialize (not_valueb_sound t1).
    intro H2.
    specialize (H2 NV).
    rewrite H2.
    specialize (IHt1 s1 t1' s2 H1).
    rewrite IHt1.
    reflexivity.
  - apply Nat.ltb_lt in H1.
    rewrite H1.
    reflexivity.
  - specialize (step_not_value t1 s1 t1' s2 H1) as NV.
    specialize (not_valueb_sound t1).
    intro H2.
    specialize (H2 NV).
    rewrite H2.
    specialize (IHt1 s1 t1' s2 H1).
    rewrite IHt1.
    reflexivity.
  - apply valueb_sound in H2.
    rewrite H2.
    apply Nat.ltb_lt in H6.
    rewrite H6.
    reflexivity.
  - specialize (step_not_value t1_1 s1 t1' s2 H1) as NV.
    specialize (not_valueb_sound t1_1).
    intro H2.
    specialize (H2 NV).
    rewrite H2.
    specialize (IHt1_1 s1 t1' s2 H1).
    rewrite IHt1_1.
    reflexivity.
  - apply valueb_sound in H2.
    rewrite H2.
    specialize (step_not_value t1_2 s1 t2' s2 H6) as NV.
    specialize (not_valueb_sound t1_2).
    intro H3.
    specialize (H3 NV).
    rewrite H3.
    specialize (IHt1_2 s1 t2' s2 H6).
    rewrite IHt1_2.
    reflexivity.
Qed.


(* --------------------------------------------------- *)
(* META LANGUAGE - add counters to stores, incremented each time
   the loc is refed, derefed, or assigned *)


Inductive mtm : Type :=
  | mvar    : string -> mtm
  | mapp    : mtm -> mtm -> mtm
  | mabs    : string -> mtm -> mtm
  | mconst  : nat -> mtm
  | mscc    : mtm -> mtm
  | mprd    : mtm -> mtm
  | mtest0  : mtm -> mtm -> mtm -> mtm
  | munit   : mtm
  | mref    : mtm -> mtm
  | mderef  : mtm -> mtm
  | massign : mtm -> mtm -> mtm
  | mloc    : nat -> mtm
  | merror  : string -> mtm.

(* values *)
Inductive mvalue : mtm -> Prop :=
  | mv_abs  : forall x t,
      mvalue (mabs x t)
  | mv_nat : forall n,
      mvalue (mconst n)
  | mv_unit :
      mvalue munit
  | mv_loc : forall l,
      mvalue (mloc l).
Hint Constructors mvalue.

Fixpoint mvalueb (mt : mtm) : bool :=
  match mt with
  | mabs _ _ | mconst _ | munit | mloc _ => true
  | _ => false
  end.

Theorem mvalueb_sound : forall mt, mvalue mt -> (mvalueb mt = true).
Proof.
  intros.
  inversion H; simpl; reflexivity.
Qed.

Theorem mvalueb_complete : forall mt, (mvalueb mt = true) -> mvalue mt.
Proof.
  intros.
  destruct mt; simpl; try discriminate; auto.
Qed.

(* substitution. NB ignores free-variable issues. *)
Fixpoint msubst (x:string) (s:mtm) (t:mtm) : mtm :=
  match t with
  | mvar x'       =>
      if String.eqb x x' then s else t
  | mapp t1 t2    =>
      mapp (msubst x s t1) (msubst x s t2)
  | mabs x' t1  =>
      if String.eqb x x' then t else mabs x' (msubst x s t1)
  | mconst n        =>
      t
  | mscc t1      =>
      mscc (msubst x s t1)
  | mprd t1      =>
      mprd (msubst x s t1)
  | mtest0 t1 t2 t3 =>
      mtest0 (msubst x s t1) (msubst x s t2) (msubst x s t3)
  | munit         =>
      t
  | mref t1       =>
      mref (msubst x s t1)
  | mderef t1     =>
      mderef (msubst x s t1)
  | massign t1 t2 =>
      massign (msubst x s t1) (msubst x s t2)
  | mloc _        =>
      t
  | merror _      => t 
  end.


Definition mstore := list (mtm * nat).

Definition mstore_lookup (n:nat) (mst:mstore) :=
  match nth n mst (munit, O) with
  | (mt, _) => mt
  end.

Definition mstore_incr_loc (n:nat) (mst:mstore) :=
  match nth n mst (munit, O) with
  | (mt, ct) => replace n (mt, S ct) mst
  end. 

Definition replace_incr_loc (n:nat) (t:mtm) (mst:mstore) :=
  match nth n mst (munit, O) with
  | (_, ct) => replace n (t, S ct) mst
  end. 

Fixpoint mstepfn (t : mtm) (s : mstore) : mtm * mstore :=
  match t with
  | mvar _ | munit | mconst _ | mabs _ _ | mloc _ | merror _ => (t,s)
  | mapp fn arg =>
    if (mvalueb fn) then
      if (mvalueb arg) then
        match fn with
        | mabs x body => (msubst x arg body, s)
        | _ => (merror "attempt to apply non-fn", s)
        end
      else
        let (arg',s') := mstepfn arg s in
        (mapp fn arg', s')
    else
      let (fn',s') := mstepfn fn s in
      (mapp fn' arg, s')
  | mscc t1 =>
    if (mvalueb t1) then
      match t1 with
      | mconst n => (mconst (S n), s)
      | _ => (merror "scc of non nat", s)
      end
    else
      let (t1', s') := mstepfn t1 s in
      (mscc t1', s')
  | mprd t1 =>
    if (mvalueb t1) then
      match t1 with
      | mconst n => (mconst (pred n), s)
      | _ => (merror "prd of non nat", s)
      end
    else
      let (t1', s') := mstepfn t1 s in
      (mprd t1', s')
  | mtest0 cond yes no =>
    if (mvalueb cond) then
      match cond with
      | mconst 0 => (yes, s)
      | mconst (S n) => (no, s)
      | _ => (merror "test0 of non nat", s)
      end
    else
      let (cond', s') := mstepfn cond s in
      (mtest0 cond' yes no, s')
  (* Add instrumentation to the store *)
  | mref t1 =>
    if (mvalueb t1) then
      (mloc (length s), (s ++ (t1,0)::nil))
    else
      let (t1', s') := mstepfn t1 s in
      (mref t1', s')
  | mderef t1 =>
    if (mvalueb t1) then
      match t1 with
      | mloc l =>
        if Nat.ltb l (length s) then
          (mstore_lookup l s, mstore_incr_loc l s)
        else (merror "attempt to deref invalid loc", s)
      | _ => (merror "attempt to deref non-loc", s)
      end
    else
      let (t1', s') := mstepfn t1 s in
      (mderef t1', s')
  | massign t1 t2 =>
    if (mvalueb t1) then
      if (mvalueb t2) then
        match t1 with
        | mloc l =>
          if Nat.ltb l (length s) then
            (munit, replace_incr_loc l t2 s)
          else (merror "attempt to assign invalid loc", s)
        | _ => (merror "attempt to assign non-loc", s)
        end
      else
        let (t2', s') := mstepfn t2 s in
        (massign t1 t2', s')
    else
      let (t1', s') := mstepfn t1 s in
      (massign t1' t2, s')   
  end.

Fixpoint reify_tm (t : tm) : mtm :=
  match t with
  | var x' => mvar x'
  | app t1 t2 => mapp (reify_tm t1) (reify_tm t2)
  | abs x' t1 => mabs x' (reify_tm t1)
  | const n => mconst n
  | scc t1 => mscc (reify_tm t1)
  | prd t1 => mprd (reify_tm t1)
  | test0 t1 t2 t3 => mtest0 (reify_tm t1) (reify_tm t2) (reify_tm t3)
  | unit => munit
  | ref t1 => mref (reify_tm t1)
  | deref t1  => mderef (reify_tm t1)
  | assign t1 t2 => massign (reify_tm t1) (reify_tm t2)
  | loc l => mloc l
  | error s => merror s 
  end.

Definition reify_st (st : store) : mstore :=
  map (fun t => (reify_tm t, O)) st.
 
Definition reify (t : tm) (st : store) : (mtm * mstore) :=
  (reify_tm t, reify_st st).

Fixpoint reflect_mtm (mt : mtm) : tm :=
  match mt with
  | mvar x' => var x'
  | mapp t1 t2 => app (reflect_mtm t1) (reflect_mtm t2)
  | mabs x' t1 => abs x' (reflect_mtm t1)
  | mconst n => const n
  | mscc t1 => scc (reflect_mtm t1)
  | mprd t1 => prd (reflect_mtm t1)
  | mtest0 t1 t2 t3 => test0 (reflect_mtm t1) (reflect_mtm t2) (reflect_mtm t3)
  | munit => unit
  | mref t1 => ref (reflect_mtm t1)
  | mderef t1 => deref (reflect_mtm t1)
  | massign t1 t2 => assign (reflect_mtm t1) (reflect_mtm t2)
  | mloc l => loc l
  | merror s => error s 
  end.

Definition reflect_mst (mst : mstore) : store :=
  map (fun pair =>
         match pair with
         | (t, _) => reflect_mtm t
         end)
      mst.

Definition reflect (mt : mtm) (mst : mstore) : (tm * store) :=
  (reflect_mtm mt, reflect_mst mst).

Theorem reflection_sound :
  forall t s t' s' mt ms mt' ms',
    stepfn t s = (t', s') ->
    reify t s = (mt, ms) ->
    mstepfn mt ms = (mt', ms') ->
    reflect mt' ms' = (t', s').
Proof.
  intros.
Abort.


                   


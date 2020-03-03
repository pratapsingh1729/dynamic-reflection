From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Decidable.
Import ListNotations.

(* a continuation-based semantics for an IMP-like language, loosely based on
 * https://xavierleroy.org/courses/EUTypes-2019/html/EUTypes2019.CompilerVerification.IMP.html *)

Definition ident := string.
Definition store : Type := ident -> nat.

(* large-step for arithmetic expressions *)
Inductive aexp : Type :=
  | aconst (n: nat)                       
  | avar (x: ident)                     
  | aplus (a1: aexp) (a2: aexp)
  | amult (a1 : aexp) (a2: aexp).

Fixpoint aeval (s: store) (a: aexp) : nat :=
  match a with
  | aconst n => n
  | avar x => s x
  | aplus a1 a2 => aeval s a1 + aeval s a2
  | amult a1 a2 => aeval s a1 * aeval s a2
  end.
Hint Unfold aeval.

(* large-step for boolean expressions *)
Inductive bexp : Type :=
  | btrue | bfalse
  | beq (a1: aexp) (a2: aexp)       
  | bleq (a1: aexp) (a2: aexp)   
  | bnot (b1: bexp)                    
  | band (b1: bexp) (b2: bexp)
  | bor  (b1: bexp) (b2: bexp).

Fixpoint beval (s: store) (b: bexp) : bool :=
  match b with
  | btrue => true
  | bfalse => false
  | beq a1 a2 => aeval s a1 =? aeval s a2
  | bleq a1 a2 => aeval s a1 <=? aeval s a2
  | bnot b1 => negb (beval s b1)
  | band b1 b2 => beval s b1 && beval s b2
  | bor b1 b2 => beval s b1 || beval s b2
  end.
Hint Unfold beval.

(* statements in the language *)
Inductive stmt: Type :=
  | skip
  | assign (x: ident) (a: aexp)        
  | seq (s1: stmt) (s2: stmt)            
  | cond (b: bexp) (s1: stmt) (s2: stmt) 
  | while (b: bexp) (s1: stmt).

Definition store_update (x: ident) (v: nat) (s: store) : store :=
  fun y => if string_dec x y then v else s y.

(* continuation-based step semantics for language *)
Definition cont := list stmt.

Inductive step: stmt * cont * store -> stmt * cont * store -> Prop :=
  | Step_Assign: forall x a k s,              
      step (assign x a, k, s) (skip, k, store_update x (aeval s a) s)
  | step_seq: forall c1 c2 s k,               
      step (seq c1 c2, k, s) (c1, c2 :: k, s)
  | step_cond: forall b c1 c2 k s,
      step (cond b c1 c2, k, s) ((if beval s b then c1 else c2), k, s)
  | step_while_done: forall b c k s,
      beval s b = false ->
      step (while b c, k, s) (skip, k, s)
  | step_while_true: forall b c k s,
      beval s b = true ->
      step (while b c, k, s) (c, while b c :: k, s)
  | step_skip_seq: forall c k s,
      step (skip, c :: k, s) (c, k, s).




(* 
NEED CONTINUATIONS!!!!!!

reify - take current continuation as argument


reflect - replace current continuation with argument

*)

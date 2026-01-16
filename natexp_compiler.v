(* 

  Axel van Abkoude - s1021909
  Project 4

------------------------------------------------

This file has four sections:
   - Definitions
   - Expression Evaluator
   - Non dependent implementation of RPN   (1) 
   - Dependent types implementation of RPN (2) 

The functions relating to RPN will be annotated with the number to
differentiate if they are dependent or non dependent

 *)
Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.

(* 
-----------------------------
        Definitions 
 *)
Definition lit := nat. 
Definition binop := (lit -> lit -> lit). 

(*
Partial map: Includes option in env chosen not to do this
 as it adds extra complexity.
This could be solved by a dependent type or a Map type
 *)

(* Total map with as defaults element 0*)
Definition env := string -> lit.
Definition empty : env := (fun _ => 0).
Definition update (f : env) (x : string) (l : lit) : env :=
  (fun y => if String.eqb x y then l else f y).

(* 
-----------------------------
        Expressions 
 *)
(* Definition of Exp *)
Inductive Exp : Set :=
  | Elit : lit -> Exp
  | Evar : string -> Exp
  | Ebinop : binop -> Exp -> Exp -> Exp
.

(* Semantics for Exp *)
Fixpoint eval (e:Exp) (f:env) {struct e} : lit :=
match e with
| Elit l      => l
| Evar x      => f x
| Ebinop op e1 e2 => op (eval e1 f) (eval e2 f)
end.

(* 
  -----------------------------
  Non dependent type stackbased implementation (1)
 *)

(* Defintion of Non dependent RPN *)
Inductive RPN1 : Type :=
  | RPN1lit : lit -> RPN1
  | RPN1var : string -> RPN1
  | RPN1bin : binop -> RPN1
.

(* Non dependent RPN1 compiler *)
Fixpoint compiler1 (e:Exp) {struct e} : list RPN1 :=
match e with
| Elit l => RPN1lit l :: nil
| Evar s => RPN1var s :: nil
| Ebinop op e1 e2 => compiler1 e1 ++ compiler1 e2 ++ RPN1bin op :: nil
end.

(* Non dependent rpn evaluator *)
Fixpoint rpn_eval1 (inp: list RPN1) (stack: list lit) (f : env) {struct inp} : option lit :=
match inp with
| nil => 
  match stack with
  | x::xs => Some x
  | nil  => None
  end
| (RPN1lit   l ) :: rs => rpn_eval1 rs (l  ::stack) f
| (RPN1var   s ) :: rs => rpn_eval1 rs (f s::stack) f
| (RPN1bin op) :: rs =>
  match stack with
  | x::x'::xs => rpn_eval1 rs ((op x' x)::xs) f
  | _         => None
  end
end.

(* Some basic sanity checks *)
Definition rpn0:(list RPN1) := (RPN1lit 1) :: (RPN1lit 2) :: (RPN1bin plus)::nil.
Definition rpn1:(list RPN1) := (RPN1lit 3) :: (RPN1lit 1) :: (RPN1lit 2) :: (RPN1bin plus) :: (RPN1bin plus)::nil.
Definition rpn2:(list RPN1) := (RPN1lit 3) :: (RPN1lit 1) :: (RPN1lit 2) :: (RPN1bin plus) :: (RPN1bin mult)::nil.
Eval compute in (rpn_eval1 (rpn2) nil empty).
Definition rpn3:(list RPN1) := (RPN1var "x") :: (RPN1lit 2) :: (RPN1bin plus)::nil.

(* Helper lemma which signifies one step of the rpn_eval1 while keeping the expression intact *)
Lemma rpn_eval1_applied:
  forall (e : Exp) (f : env) (st : list lit) (rpn : list RPN1),
    rpn_eval1 (compiler1 e ++ rpn) st f =
    rpn_eval1 rpn (eval e f :: st) f.
Proof.
  (* We do not need to use a different environment in the induction step*)
  intros e f.
  (* Induction on the expressions *)
  induction e;
  (* Solve trivial cases (Lit and Var) *)
  simpl; try reflexivity.
  (* Solve Binop case*)
  - intros st rpn.
    (* Reshuffle list to get into a form of (compiler1 e1 ++ (compiler1 e2 ++ rpn)) *)
    rewrite <- app_assoc. 
    rewrite <- app_assoc. 
    rewrite <- app_comm_cons. 
    simpl. 
    (* Rewrite the IHs *)
    rewrite IHe1. 
    rewrite IHe2. 
    reflexivity.
Qed.

(*
Prove that
forall e:Exp, Some (eval e) = rpn_eval (rpn e)

Aka: prove equivalence with non dependent types
 *)
Lemma equivalent1 : forall (f:env) (e:Exp), 
  Some (eval e f) = rpn_eval1 (compiler1 e) nil f.
Proof.
  intros f e.
  (* Delay the inductive step to the helper Lemma rpn_eval1_applied *)
  destruct e; 
  (* Solve trivial cases (Lit and Var) *)
  simpl; try reflexivity.
  (* Solve Binop case by applying the rpn_eval twice *)
  - rewrite rpn_eval1_applied.
    rewrite rpn_eval1_applied.
    reflexivity.
Qed.

(*
QUESTION:
Discuss how you might avoid explicit consideration of None terms in the
definition of rpn_eval, and explain how you need to modify your formal-
ization in Rocq.

ANSWER:
   We could make the steps in the stack explicit. We would need a dependent type 
   for the RPN list which keeps track of the stack size after evaluation. 
   This would be +1 for the Lit and Var case and -1 for the Binop case as we 
   remove 2 stack elements and add one. We encode this as S (S n) -> (S n) 
   instead of (S n) -> n to ensure that the stack has enough Lits and/or 
   Vars to evaluate a Binop.

   Then we create a dependent structure that looks like a vector 

   When we return this dependent type with value 1 we know that when the program type checks it has a valid stack (where the evaluated length is 1).
   As we do not have negative numbers in 'nat' we model the difference each instruction takes with two nats as follows:
 *)


Require Import Coq.Vectors.Vector.
(*Makes working with vectors less verbose *)
Import VectorNotations.

(* The instructions with their stack difference *)
Inductive RPN2 : nat -> nat -> Type :=
| RPN2lit {n} : lit -> RPN2 n (S n)
| RPN2var {n} : string -> RPN2 n (S n)
| RPN2bin {n} : binop -> RPN2 (S (S n)) (S n).

(* 
   R_nil needs to be 1 here as we want the length of the evaluated RPNvec to be 1 
*)
Inductive RPNvec : nat -> Type :=
| R_nil  : RPNvec 1 
| R_cons {n m} : RPN2 n m -> RPNvec m -> RPNvec n.

Fixpoint compiler2 {n} (e : Exp) : RPNvec (S n) -> RPNvec n :=
match e with
| Elit l          => fun c => R_cons (RPN2lit l) c
| Evar s          => fun c => R_cons (RPN2var s) c
| Ebinop op e1 e2 => fun c => compiler2 e1 (compiler2 e2 
    (R_cons (RPN2bin op) c)) 
end.

Definition rpn := compiler2 (Ebinop plus (Elit 1) (Evar "a")) R_nil.
Eval compute in rpn.

Fixpoint eval_instr {n m} (ins: RPN2 n m) (f : env) : Vector.t lit n -> Vector.t lit m :=
match ins with
| RPN2lit l  => fun st => l::st
| RPN2var s  => fun st => f s::st
| RPN2bin op => fun st =>
  let x   := hd st in
  let st' := tl st in
  let y   := hd st' in
  let xs  := tl st' in
    op y x :: xs
end.


Fixpoint rpn_eval2 {n} (c : RPNvec n) (f : env)
  : Vector.t lit n -> Vector.t lit 1 :=
match c with
| R_nil       => fun st => st
| R_cons i c' => fun st =>
    rpn_eval2 c' f (eval_instr i f st) 
end.

(* 
Some experimentation that the implementation is correct 
 *)
Definition test := rpn_eval2 rpn empty.
Eval compute in test.
Definition test' := rpn_eval2 rpn (update empty "a" 1).
Eval compute in test'.
Definition rpn'' := R_nil.
(*Definition test'' := rpn_eval2 rpn'' empty.*)
Definition rpn''' := R_cons (RPN2bin plus) R_nil.
(*Definition test''' := rpn_eval2 rpn''' empty.*)
(*Definition rpn'''' := R_cons (RPN2lit 1) (R_cons (RPN2lit 2) R_nil).*)
(*Definition test'''' := rpn_eval2 rpn'''' empty.*)


(* 
The intermediate step (between IHe1 and IHe2) can not be rewritten as
the dependent types of the stacks do not match.
Thus for the dependent case we add n to the IH. 
Otherwise this helper lemma is the same as rpn_eval1_applied
*)
Lemma rpn_eval2_applied :
  forall (e : Exp) (f : env) (n:nat) (st : Vector.t lit n) (rpn : RPNvec (S n)),
    rpn_eval2 (compiler2 e rpn) f st =
    rpn_eval2 rpn f (eval e f :: st).
Proof.
  intros e f.
  induction e;intros n.
  (* Lit and Var case *)
  - destruct n;reflexivity.
  - destruct n;reflexivity.
  (*Binop case*)
  - intros st rpn. simpl.
    rewrite IHe1.
    rewrite IHe2. 
    reflexivity.
Qed.

(*
Prove that
forall e:Exp, eval e = rpn_eval (rpn e)

Aka: Prove equivalence with dependent types *)
Lemma equivalent2 : forall (f:env) (e:Exp), 
  eval e f = hd (rpn_eval2 (compiler2 e R_nil) f (nil lit)).
Proof.
  intros f e.
  destruct e;
  simpl;try reflexivity.
  - rewrite rpn_eval2_applied.
    rewrite rpn_eval2_applied.
    reflexivity.
Qed.


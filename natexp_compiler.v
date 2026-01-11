(* 

  Axel van Abkoude - s1021909
  Project 4

------------------------------------------------
4 Proving an expression compiler correct
Formalize both an interpreter and a compiler for a simple language of arith-
metical expressions, and show that both give the same results. Compile the
expressions to code for a simple stack machine. Use dependent types to make
Rocq aware of the fact that the compiled code will never lead to a run time error.

 *)


Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.


(*
Inductive definition:
 *)

Definition lit := nat. 
Definition binop := (lit -> lit -> lit). 

(*Partial map*)
(*
Definition env := string -> option lit.
Definition empty : env := (fun _ => None).
Definition update (f : env) (x : string) (l : lit) : env :=
  (fun y => if String.eqb x y then Some l else f y).
 *)

(*Total map: Defaults to 0*)
Definition env := string -> lit.
Definition empty : env := (fun _ => 0).
Definition update (f : env) (x : string) (l : lit) : env :=
  (fun y => if String.eqb x y then l else f y).

Inductive Exp : Set :=
  | Elit : lit -> Exp
  | Evar : string -> Exp
  | Ebinop : binop -> Exp -> Exp -> Exp
.
(*
Semantics for Exp
 *)
Fixpoint eval (e:Exp) (f:env) {struct e} : lit :=
match e with
| Elit l      => l
| Evar x      => f x
| Ebinop op e1 e2 => op (eval e1 f) (eval e2 f)
end.

(*
Stackbased Implementation 
 *)
 
Inductive RPN : Type :=
  | RPNlit : lit -> RPN
  | RPNvar : string -> RPN
  | RPNbinop : binop -> RPN
.

Fixpoint exp_to_rpnlist (e:Exp) {struct e} : list RPN :=
match e with
| Elit l => RPNlit l :: nil
| Evar s => RPNvar s :: nil
| Ebinop op e1 e2 => exp_to_rpnlist e1 ++ exp_to_rpnlist e2 ++ RPNbinop op :: nil
end.

Fixpoint rpn_eval (inp: list RPN) (stack: list lit) (f : env) {struct inp} : option lit :=
match inp with
| nil => 
  match stack with
  | x::xs => Some x
  | nil  => None
  end
| (RPNlit   l ) :: rs => rpn_eval rs (l  ::stack) f
| (RPNvar   s ) :: rs => rpn_eval rs (f s::stack) f
| (RPNbinop op) :: rs =>
  match stack with
  | x::x'::xs => rpn_eval rs ((op x' x)::xs) f
  | _         => None
  end
end.

Definition rpn0:(list RPN) := (RPNlit 1) :: (RPNlit 2) :: (RPNbinop plus)::nil.
Definition rpn1:(list RPN) := (RPNlit 3) :: (RPNlit 1) :: (RPNlit 2) :: (RPNbinop plus) :: (RPNbinop plus)::nil.
Definition rpn2:(list RPN) := (RPNlit 3) :: (RPNlit 1) :: (RPNlit 2) :: (RPNbinop plus) :: (RPNbinop mult)::nil.
Eval compute in (rpn_eval (rpn2) nil empty).
Definition rpn3:(list RPN) := (RPNvar "x") :: (RPNlit 2) :: (RPNbinop plus)::nil.
(*
Eval compute in (rpn_eval (rpn3) nil env0).
Eval compute in (rpn_eval (rpn3) nil empty).
 *)

Lemma rpn_applied :
  forall (e : Exp) (f : env) (st : list lit) (rpn : list RPN),
    rpn_eval (exp_to_rpnlist e ++ rpn) st f =
    rpn_eval rpn (eval e f :: st) f.
Proof.
  (* We do not need to use a different environment in the induction step*)
  intros e f.
  (* Induction on the expressions *)
  induction e;
  (* Solve trivial cases (Lit and Var) *)
  simpl; try reflexivity.
  (* Solve Binop case*)
  - intros st rpn.
    (* Reshuffle list to get into a form of (exp_to_rpnlist e1 ++ (exp_to_rpnlist e2 ++ rpn)) *)
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
 *)
Lemma equivalent_under_extensionality : forall (f:env) (e:Exp), 
  Some (eval e f) = rpn_eval (exp_to_rpnlist e) nil f.
Proof.
  intros f e.
  (* Delay the inductive step to the helper Lemma rpn_applied *)
  destruct e; 
  (* Solve trivial cases (Lit and Var) *)
  simpl; try reflexivity.
  (* Solve Binop case by applying the rpn_eval twice *)
  - rewrite rpn_applied.
    rewrite rpn_applied.
    reflexivity.
Qed.

(*
QUESTION:
Discuss how you might avoid explicit consideration of None terms in the
definition of rpn_eval, and explain how you need to modify your formal-
ization in Rocq.

ANSWER:
   We could make the steps in the stack explicit. We would need a dependent type for stack which keeps track of the stack size after evaluation. This would be +1 for the Lit and Var case and -1 for the Binop case as we remove 2 stack elements and add one.
   When we return this dependent type with value 1 we know that when the program type checks it has a valid stack (where the evaluated length is 1).
   As we do not have negative numbers in 'nat' we model the difference with two nats as follows:
 *)


(* Does not compile as the execution needs a negative stack length *)
(*
Definition test1 := LScons (RPNlit' 1) (LScons (RPNlit' 2) (LScons (RPNbin' plus) LSnil)).
 *)
(* Does not compile as the stack ends not equal to 1 *)
(*
Definition test2 : ListWithEvalSize 1 := LScons (RPNlit' 1) (LScons (RPNlit' 2) LSnil).
 *)

(* I do not know how to get this working: 
   - In each situation i tried we still need to match on a empty stack. This is not reachable because of the ListWithEvalSize 1 but i cannot connect the two.
*)


Require Import Coq.Vectors.Vector.
(*Makes working with vectors less verbose *)
Import VectorNotations.

Inductive Instr : nat -> nat -> Type :=
| I_lit {n} : lit -> Instr n (S n)
| I_var {n} : string -> Instr n (S n)
| I_bin {n} : binop -> Instr (S (S n)) (S n).

Inductive RPNdep : nat -> nat -> Type :=
| R_nil  {n} : RPNdep n n
| R_cons {n m k} : Instr n m -> RPNdep m k -> RPNdep n k.

Fixpoint eval_instr {n m} (ins: Instr n m) (f : env) : Vector.t lit n -> Vector.t lit m :=
match ins in Instr n' m' return Vector.t lit n' -> Vector.t lit m' with
| I_lit l  => fun st => l::st
| I_var s  => fun st => f s::st
| I_bin op => fun st =>
  let x   := hd st in
  let st' := tl st in
  let y   := hd st' in
  let xs  := tl st' in
    op y x :: xs
end.

Fixpoint exec {n m} (c : RPNdep n m) (f : env)
  : Vector.t lit n -> Vector.t lit m :=
match c in RPNdep n' m' return Vector.t lit n' -> Vector.t lit m' with
| R_nil       => fun st => st
| R_cons i c' => fun st =>
    exec c' f (eval_instr i f st)
end.

Fixpoint exp_to_rpndepvec {n k} (e : Exp) : RPNdep (S n) k -> RPNdep n k :=
match e with
| Elit l          => fun c => R_cons (I_lit l) c
| Evar s          => fun c => R_cons (I_var s) c
| Ebinop op e1 e2 => fun c => exp_to_rpndepvec e1 (exp_to_rpndepvec e2 (R_cons (I_bin op) c))
end.


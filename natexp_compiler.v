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

(*
Inductive definition:
 *)

Definition lit := nat. 
Definition env := string -> option lit.
Definition empty : env := (fun _ => None).
Definition update (f : env) (x : string) (l : lit) : env :=
  (fun y => if String.eqb x y then Some l else f y).
Inductive Exp : Set :=
  | Elit : lit -> Exp
  | Evar : string -> Exp
  | Eplus : Exp -> Exp -> Exp
  | Emin : Exp -> Exp -> Exp
  | Emult : Exp -> Exp -> Exp.


(*
Semantics for Exp
 *)
Fixpoint eval (e:Exp) (f:env) {struct e} : option lit :=
match e with
| Elit l      => Some l
| Evar x      => f x
| Eplus e1 e2 => 
    match eval e1 f, eval e2 f with
    | Some l1, Some l2 => Some (plus l1 l2)
    | _,_ => None
    end
| Emin  e1 e2 =>
    match eval e1 f, eval e2 f with
    | Some l1, Some l2 => Some (min l1 l2)
    | _,_ => None
    end
| Emult e1 e2 => 
    match eval e1 f, eval e2 f with
    | Some l1, Some l2 => Some (mult l1 l2)
    | _,_ => None
    end
end.

Definition exp0 := Elit 0.
Definition exp1 := Elit 1.
Definition exp2 := Evar "x".
Definition exp3 := Eplus (Evar "x") (Elit 2).
Definition exp4 := Eplus (Elit 1) (Elit 2).
Definition env0 := update empty "x" 4.
Definition env1 := update env0 "y" 6.
Definition env2 := update empty "y" 6.

Eval compute in (eval exp3 empty).
Eval compute in (eval exp3 env0).
Eval compute in (eval exp3 env1).
Eval compute in (eval exp3 env2).


(*
   Inductive definition RPN
 *)
Inductive RPN : Set :=
  | RPNlit : lit -> RPN
  | RPNvar : string -> RPN
  | RPNbinop : option RPN -> option RPN -> (lit -> lit -> lit) -> RPN
.

(*
   Compiler from Exp to RPN
 *)
Fixpoint rpn (e:Exp) {struct e} : RPN :=
match e with
| Elit l => RPNlit l
| Evar x => RPNvar x
| Eplus e1 e2 => RPNbinop (Some (rpn e1)) (Some (rpn e2)) plus
| Emin  e1 e2 => RPNbinop (Some (rpn e1)) (Some (rpn e2)) min
| Emult e1 e2 => RPNbinop (Some (rpn e1)) (Some (rpn e2)) mult
end.

(*
  Evaluator for RPN
 *)

Fixpoint rpn_eval (r:RPN) (f:env) {struct r} : option lit :=
match r with
| RPNlit l => Some l
| RPNvar x => f x
| RPNbinop (Some r1) (Some r2) op => 
    match (rpn_eval r1 f), (rpn_eval r2 f) with
    | Some r1', Some r2' => Some (op r1' r2')
    | _, _ => None
    end
| _ => None
end.

Definition rpn0 := RPNlit 0.
Definition rpn1 := RPNbinop (Some (RPNlit 5)) (Some (RPNlit 6)).
Definition rpn2 := RPNbinop (Some (RPNvar "x")) (Some (RPNlit 6)).
Definition rpn3 := RPNbinop None (Some (RPNlit 6)).
Eval compute in (rpn_eval (rpn1 plus) empty).
Eval compute in (rpn_eval (rpn1 mult) empty).
Eval compute in (rpn_eval (rpn2 plus) empty).
Eval compute in (rpn_eval (rpn2 plus) env0 ).
Eval compute in (rpn_eval (rpn2 plus) env1 ).
Eval compute in (rpn_eval (rpn2 plus) env2 ).

(*
Prove that
forall e:Exp, Some (eval e) = rpn_eval (rpn e)
 *)

Lemma Equivalence_Eval_RPNEval : forall e:Exp, eval e = rpn_eval (rpn e).
Proof.
  induction e; simpl; try rewrite <- IHe1, <- IHe2; reflexivity.
Qed.

(*
QUESTION:
Discuss how you might avoid explicit consideration of None terms in the
definition of rpn_eval, and explain how you need to modify your formal-
ization in Rocq.

ANSWER:
We can make it a relation which should hold for all Exp. This means that
we do not need to include None terms as we check for all possible expressions. 
Now if we prove this relation we prove the equivalence.
 *)

Inductive RPN' : Set :=
  | RPNlit' : lit -> RPN'
  | RPNvar' : string -> RPN'
  | RPNbinop' : RPN' -> RPN' -> (lit -> lit -> lit) -> RPN'
.

Fixpoint rpn' (e:Exp) {struct e} : RPN' :=
match e with
| Elit l => RPNlit' l
| Evar x => RPNvar' x
| Eplus e1 e2 => RPNbinop' (rpn' e1) (rpn' e2) plus
| Emin  e1 e2 => RPNbinop' (rpn' e1) (rpn' e2) min
| Emult e1 e2 => RPNbinop' (rpn' e1) (rpn' e2) mult
end.

Inductive exprpn_rel : Exp -> RPN' -> Prop :=
    RPNl : forall n:lit     , exprpn_rel (Elit n) (RPNlit' n)
  | RPNv : forall v:string  , exprpn_rel (Evar v) (RPNvar' v)
  | RPNb0 : forall e1 e2:Exp, exprpn_rel (Eplus e1 e2) (RPNbinop' (rpn' e1) (rpn' e2) plus)
  | RPNb1 : forall e1 e2:Exp, exprpn_rel (Emin  e1 e2) (RPNbinop' (rpn' e1) (rpn' e2) min)
  | RPNb2 : forall e1 e2:Exp, exprpn_rel (Emult e1 e2) (RPNbinop' (rpn' e1) (rpn' e2) mult)
.

Lemma AllExpRelateToTheSameRPN : forall e:Exp, exprpn_rel e (rpn' e).
Proof.
  induction e; simpl.
  - apply RPNl.
  - apply RPNv.
  - apply RPNb0.
  - apply RPNb1.
  - apply RPNb2.
Qed.


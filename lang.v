(*From stdpp Require binders.*)
(* Require Export stdpp.strings.*)
Require Import Zee.lattice.
Require Export String.
Global Open Scope string_scope.

Section Lang.
Context {A : Set} `{lattice A}.
Context {BinOpS : Set}.
  
Definition Lab := @Word A string.
Hint Unfold Lab.
Definition LabVar := @WordVar A string.

Inductive Ty :=
| IntTy: Ty
| PtrTy: Lab -> SecTy -> Ty
| SPtrTy: SecTy -> SecTy -> Ty
| ExTyTy: string -> Lab -> SecTy -> Ty
| ExLabTy: string -> Lab -> SecTy -> Ty
| RecTy: Lab -> string -> SecTy -> Ty
| SizeTy: SecTy -> Ty
with AtomSecTy :=
       STy: Ty -> Lab -> AtomSecTy
     | VarTy: string -> Lab -> AtomSecTy
with SecTy :=
     | ASecTy: AtomSecTy -> SecTy
     | ProdTy: AtomSecTy -> SecTy -> SecTy
     | NilTy: SecTy.
Hint Constructors Ty SecTy.

Coercion ASecTy : AtomSecTy >-> SecTy.

Inductive Expr :=
| Var: string -> Expr
| Num: nat -> Expr
| BinOp: BinOpS -> Expr -> Expr -> Expr
| Unroll: Expr -> Expr
| Roll: Expr -> Expr
| PackTy: SecTy -> Expr -> Lab -> string -> SecTy -> Expr
| PackLab: Lab -> Expr -> Lab -> string -> SecTy -> Expr
| SizeOf: SecTy -> Expr
| AddrOf: string -> Expr.
Hint Constructors Expr.

Inductive Pat :=
  PInt: Pat
| PSPtr: SecPat -> SecPat -> Pat
| PPtr: string -> SecPat -> Pat
with AtomPat :=
       SPat: Pat -> string -> AtomPat
     | PVar: string -> AtomPat
with SecPat :=
| PProd: AtomPat -> SecPat -> SecPat
| PNil: SecPat
| PAtom: AtomPat -> SecPat.
Hint Constructors Pat AtomPat SecPat.

Coercion PAtom : AtomPat >-> SecPat.

Class SPtrAble (A B : Type) := sptr: A -> A -> B.
Class PtrAble (A B C : Type) := ptr: A -> B -> C.
Class NilAble (A : Type) := ε : A.
Class ProdAble (A B : Type) := prod: A -> B -> B.

Global Instance SPtrAble_Ty : SPtrAble SecTy Ty := SPtrTy.
Global Instance SPtrAble_Pat : SPtrAble SecPat Pat := PSPtr.
Global Instance PtrAble_Ty : PtrAble Lab SecTy Ty := PtrTy.
Global Instance PtrAble_Pat : PtrAble string SecPat Pat := PPtr.
Global Instance Nilable_SecTy : NilAble SecTy := NilTy.
Global Instance Nilable_SecPat : NilAble SecPat := PNil.
Global Instance ProdAble_SecTy : ProdAble AtomSecTy SecTy := ProdTy.
Global Instance ProdAble_SecPat : ProdAble AtomPat SecPat := PProd.

Inductive Cmd :=
| CSkip (* Done Done *)
| CLet: string -> SecTy -> Expr -> Cmd -> Cmd (* Done Done *)
| CIf: Expr -> Cmd -> Cmd -> Cmd (* Done *)
| CWhile: Expr -> Cmd -> Cmd (* Done *)
| CSeq: Cmd -> Cmd -> Cmd (* Done *)
| CWrite: Expr -> Expr -> Cmd (* Done *)
| CRead: string -> Expr -> Cmd (* Done *)
| CAt: Lab -> Expr -> Cmd -> Cmd (* Done *)
| CLabIf: Lab -> Lab -> Cmd -> Cmd -> Cmd (* Done *)
| CMatch: string -> list (SecPat * Cmd) -> Cmd (* Done *)
| CFP: string -> Cmd (* Done *)
| CCall: string -> list Lab -> list SecTy -> list Expr -> Cmd
| CUnpTy: string -> Lab -> string -> SecTy -> Expr -> Cmd -> Cmd (* Done *)
| CUnpLab: string -> Lab -> string -> SecTy -> Expr -> Cmd -> Cmd (* Done *)
| CDelay: nat -> Cmd (* Done *)
| CUnsc: string -> Cmd (* Done *)
| CEpi: Cmd (* Done *)
| CStop.
Hint Constructors Cmd.

Class Raiseable (B A : Type) := raise : B -> A -> B.
Class Sizeable (A : Type) := size : SecTy -> A.

Global Instance Sizeable_Expr : Sizeable Expr := SizeOf.
Global Instance Sizeable_SecTy : Sizeable Ty := SizeTy.

End Lang.

Notation "'∃ₛ' '(' α ':::' k ')' s" := (ExTyTy α k s) (at level 61).
Notation "'∃ₖ' '(' κ ':::' k ')' s" := (ExLabTy κ k s) (at level 61).
Notation "'μ' '(' α ':::' k ')' s" := (RecTy k α s) (at level 61).
Notation "'|' s '|'" := (size s) (at level 40).
Infix "#" := ptr (at level 49, right associativity).
Infix "@" := sptr (at level 60, right associativity).

Infix "·" := prod (at level 51, right associativity).

Notation "'UNROLL' e" := (Unroll e) (at level 70).
Notation "'ROLL' e" := (Roll e) (at level 70) .
Notation "'TYPACK' '(' s1 ',' e ')' 'AS' '∃' '(' α ':::' k ')' s2" :=
  (PackTy s1 e k α s2) (at level 70) .
Notation "'LABPACK' '(' k1 ',' e ')' 'AS' '∃' '(' κ ':::' k2 ')' s" :=
  (PackLab k1 e k2 κ s) (at level 70) .

Notation "'&(' x ')'" := (AddrOf x) (at level 9).

Notation "c1 ';;' c2 " := (CSeq c1 c2) (at level 100, c2 at level 200, right associativity).
Notation "'SKIP'" := CSkip.
Notation "'LET' x 'AS' s '::=' e 'IN' c 'ENDLET'" := (CLet x s e c).
Notation "'IF' e 'THEN' c1 'ELSE' c2 'FI'" := (CIf e c1 c2).
Notation "'WHILE' e 'DO' c 'END'" := (CWhile e c).
Infix "*=" := CWrite (at level 60).
Infix "=*" := CRead (at level 60).
Notation "'AT' k 'WITH' 'BOUND' e 'DO' c 'TA'" := (CAt k e c).
Notation "'IF' k1 'FLOWS' k2 'THEN' c1 'ELSE' c2 'FI'" := (CLabIf k1 k2 c1 c2).
Notation "'MATCH' α 'WITH' p | .. | q 'ENDMATCH'" :=
  (CMatch α (cons p .. (cons q nil) ..)).
Notation "'MATCH' α 'WITH' 'ENDMATCH'" :=
  (CMatch α nil).
Notation "x '<-' 'FP'" := (CFP x) (at level 60).
Notation "'CALL' f" := (CCall f) (at level 5).

Notation "'UNPACKTY' α 'AS' 'TYPE' k ',' x 'AS' s '::=' e 'IN' c 'ENDUNPACKTY'" :=
  (CUnpTy α k x s e c).
Notation "'UNPACKLAB' α 'AS' 'LABEL' k ',' x 'AS' s '::=' e 'IN' c 'ENDUNPACKLAB'" :=
  (CUnpLab α k x s e c).

Infix "^^" := (raise) (at level 30).
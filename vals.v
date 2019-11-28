Require Import lattice.
Require Import Zee.lang.

Section Vals.
  Context {A : Set}.
  Definition Lab := @Lab A.
  Definition Ty := @Ty A.
  Definition LabVar := @LabVar A.
  Definition SecTy := @SecTy A.
  Definition AtomSecTy := @AtomSecTy A.
  Definition Version := nat.
  
  Inductive SecTyV :=
  | ASTyV: AtomSecTyV -> SecTyV
  | ProdSecTyV: AtomSecTyV -> SecTyV -> SecTyV
  | NilTyV: SecTyV
  with AtomSecTyV :=
       | STyV: TyV -> A -> AtomSecTyV
       | NonSecTyV: AtomSecTyV
  with TyV :=
       | IntTV : TyV
       | PtrTV : A -> SecTyV -> TyV
       | SPtrTV : SecTyV -> SecTyV -> TyV
       | ExTyTV : string -> SecTy -> TyV
       | ExLabTV : string -> SecTy -> TyV
       | RecTyV: string -> SecTy -> TyV.
  Hint Constructors TyV SecTyV.

  Inductive V :=
  | VNum: nat -> V
  | VAddr: nat -> Version -> V
  | ExLab: A -> V -> V
  | ExTy: SecTyV -> V -> V.
  Hint Constructors V.
End Vals.

Coercion VNum : nat >-> V.
Coercion ASTyV : AtomSecTyV >-> SecTyV.